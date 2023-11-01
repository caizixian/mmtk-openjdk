use crate::OpenJDKEdge;

use super::abi::*;
use super::UPCALLS;
use mmtk::util::constants::*;
use mmtk::util::opaque_pointer::*;
use mmtk::util::{Address, ObjectReference};
use mmtk::vm::EdgeVisitor;
use std::cell::UnsafeCell;
use std::{mem, slice};

type E<const COMPRESSED: bool> = OpenJDKEdge<COMPRESSED>;

trait OopIterate: Sized {
    fn oop_iterate<const COMPRESSED: bool>(
        &self,
        oop: Oop,
        closure: &mut impl EdgeVisitor<OpenJDKEdge<COMPRESSED>>,
    );
}

#[repr(u8)]
#[derive(Copy, Debug, Clone)]
enum AlignmentEncodingPattern {
    Fallback = 7,
    RefArray = 6,
    NoRef = 0,
    Ref0 = 1,
    Ref1_2_3 = 2,
    Ref4_5_6 = 3,
    Ref2 = 4,
    Ref0_1 = 5,
}

impl OopIterate for AlignmentEncodingPattern {
    fn oop_iterate<const COMPRESSED: bool>(&self, oop: Oop, closure: &mut impl EdgeVisitor<E<COMPRESSED>>) {
        match self {
            // Currently exclude mirrors, refs, and instances with references
            // patterns we cannot encode
            AlignmentEncodingPattern::Fallback => oop_iterate(oop, closure),
            AlignmentEncodingPattern::RefArray => {
                let array = unsafe { oop.as_array_oop() };
                assert!(!COMPRESSED, "Alignment encoding doesn't support compressed pointers");
                for oop in unsafe { array.data::<Oop, COMPRESSED>(BasicType::T_OBJECT) } {
                    closure.visit_edge(Address::from_ref(oop as &Oop).into());
                }
            }
            AlignmentEncodingPattern::NoRef => {}
            AlignmentEncodingPattern::Ref0 => {
                // if the first field (field 0) is a ref field, it has an offset of 16 from oop
                let start = oop.get_field_address(2 * BYTES_IN_WORD as i32);
                closure.visit_edge((start + (0usize << LOG_BYTES_IN_ADDRESS)).into());
            }
            AlignmentEncodingPattern::Ref1_2_3 => {
                let start = oop.get_field_address(2 * BYTES_IN_WORD as i32);
                closure.visit_edge((start + (1usize << LOG_BYTES_IN_ADDRESS)).into());
                closure.visit_edge((start + (2usize << LOG_BYTES_IN_ADDRESS)).into());
                closure.visit_edge((start + (3usize << LOG_BYTES_IN_ADDRESS)).into());
            }
            AlignmentEncodingPattern::Ref4_5_6 => {
                let start = oop.get_field_address(2 * BYTES_IN_WORD as i32);
                closure.visit_edge((start + (4usize << LOG_BYTES_IN_ADDRESS)).into());
                closure.visit_edge((start + (5usize << LOG_BYTES_IN_ADDRESS)).into());
                closure.visit_edge((start + (6usize << LOG_BYTES_IN_ADDRESS)).into());
            }
            AlignmentEncodingPattern::Ref2 => {
                let start = oop.get_field_address(2 * BYTES_IN_WORD as i32);
                closure.visit_edge((start + (2usize << LOG_BYTES_IN_ADDRESS)).into());
            }
            AlignmentEncodingPattern::Ref0_1 => {
                let start = oop.get_field_address(2 * BYTES_IN_WORD as i32);
                closure.visit_edge((start + (0usize << LOG_BYTES_IN_ADDRESS)).into());
                closure.visit_edge((start + (1usize << LOG_BYTES_IN_ADDRESS)).into());
            }
        }
        // oop_iterate(oop, closure)
    }
}

impl From<AlignmentEncodingPattern> for u8 {
    fn from(value: AlignmentEncodingPattern) -> Self {
        value as u8
    }
}

impl From<u8> for AlignmentEncodingPattern {
    fn from(value: u8) -> Self {
        match value {
            0 => Self::NoRef,
            1 => Self::Ref0,
            2 => Self::Ref1_2_3,
            3 => Self::Ref4_5_6,
            4 => Self::Ref2,
            5 => Self::Ref0_1,
            6 => Self::RefArray,
            7 => Self::Fallback,
            _ => unreachable!(),
        }
    }
}
impl OopIterate for OopMapBlock {
    fn oop_iterate<const COMPRESSED: bool>(
        &self,
        oop: Oop,
        closure: &mut impl EdgeVisitor<E<COMPRESSED>>,
    ) {
        let log_bytes_in_oop = if COMPRESSED { 2 } else { 3 };
        let start = oop.get_field_address(self.offset);
        for i in 0..self.count as usize {
            let edge = (start + (i << log_bytes_in_oop)).into();
            closure.visit_edge(edge);
        }
    }
}

impl OopIterate for InstanceKlass {
    fn oop_iterate<const COMPRESSED: bool>(
        &self,
        oop: Oop,
        closure: &mut impl EdgeVisitor<E<COMPRESSED>>,
    ) {
        let oop_maps = self.nonstatic_oop_maps();
        for map in oop_maps {
            map.oop_iterate::<COMPRESSED>(oop, closure)
        }
    }
}

impl OopIterate for InstanceMirrorKlass {
    fn oop_iterate<const COMPRESSED: bool>(
        &self,
        oop: Oop,
        closure: &mut impl EdgeVisitor<E<COMPRESSED>>,
    ) {
        self.instance_klass.oop_iterate::<COMPRESSED>(oop, closure);

        // static fields
        let start = Self::start_of_static_fields(oop);
        let len = Self::static_oop_field_count(oop);
        if COMPRESSED {
            let start: *const NarrowOop = start.to_ptr::<NarrowOop>();
            let slice = unsafe { slice::from_raw_parts(start, len as _) };
            for narrow_oop in slice {
                closure.visit_edge(narrow_oop.slot().into());
            }
        } else {
            let start: *const Oop = start.to_ptr::<Oop>();
            let slice = unsafe { slice::from_raw_parts(start, len as _) };
            for oop in slice {
                closure.visit_edge(Address::from_ref(oop as &Oop).into());
            }
        }
    }
}

impl OopIterate for InstanceClassLoaderKlass {
    fn oop_iterate<const COMPRESSED: bool>(
        &self,
        oop: Oop,
        closure: &mut impl EdgeVisitor<E<COMPRESSED>>,
    ) {
        self.instance_klass.oop_iterate::<COMPRESSED>(oop, closure);
    }
}

impl OopIterate for ObjArrayKlass {
    fn oop_iterate<const COMPRESSED: bool>(
        &self,
        oop: Oop,
        closure: &mut impl EdgeVisitor<E<COMPRESSED>>,
    ) {
        let array = unsafe { oop.as_array_oop() };
        if COMPRESSED {
            for narrow_oop in unsafe { array.data::<NarrowOop, COMPRESSED>(BasicType::T_OBJECT) } {
                closure.visit_edge(narrow_oop.slot().into());
            }
        } else {
            for oop in unsafe { array.data::<Oop, COMPRESSED>(BasicType::T_OBJECT) } {
                closure.visit_edge(Address::from_ref(oop as &Oop).into());
            }
        }
    }
}

impl OopIterate for TypeArrayKlass {
    fn oop_iterate<const COMPRESSED: bool>(
        &self,
        _oop: Oop,
        _closure: &mut impl EdgeVisitor<E<COMPRESSED>>,
    ) {
        // Performance tweak: We skip processing the klass pointer since all
        // TypeArrayKlasses are guaranteed processed via the null class loader.
    }
}

impl OopIterate for InstanceRefKlass {
    fn oop_iterate<const COMPRESSED: bool>(
        &self,
        oop: Oop,
        closure: &mut impl EdgeVisitor<E<COMPRESSED>>,
    ) {
        use crate::abi::*;
        use crate::api::{add_phantom_candidate, add_soft_candidate, add_weak_candidate};
        self.instance_klass.oop_iterate::<COMPRESSED>(oop, closure);

        if Self::should_scan_weak_refs::<COMPRESSED>() {
            let reference = ObjectReference::from(oop);
            match self.instance_klass.reference_type {
                ReferenceType::None => {
                    panic!("oop_iterate on InstanceRefKlass with reference_type as None")
                }
                ReferenceType::Weak => add_weak_candidate(reference),
                ReferenceType::Soft => add_soft_candidate(reference),
                ReferenceType::Phantom => add_phantom_candidate(reference),
                // Process these two types normally (as if they are strong refs)
                // We will handle final reference later
                ReferenceType::Final | ReferenceType::Other => {
                    Self::process_ref_as_strong(oop, closure)
                }
            }
        } else {
            Self::process_ref_as_strong(oop, closure);
        }
    }
}

impl InstanceRefKlass {
    fn should_scan_weak_refs<const COMPRESSED: bool>() -> bool {
        !*crate::singleton::<COMPRESSED>()
            .get_options()
            .no_reference_types
    }
    fn process_ref_as_strong<const COMPRESSED: bool>(
        oop: Oop,
        closure: &mut impl EdgeVisitor<E<COMPRESSED>>,
    ) {
        let referent_addr = Self::referent_address::<COMPRESSED>(oop);
        closure.visit_edge(referent_addr);
        let discovered_addr = Self::discovered_address::<COMPRESSED>(oop);
        closure.visit_edge(discovered_addr);
    }
}

#[allow(unused)]
fn oop_iterate_slow<const COMPRESSED: bool, V: EdgeVisitor<E<COMPRESSED>>>(
    oop: Oop,
    closure: &mut V,
    tls: OpaquePointer,
) {
    unsafe {
        CLOSURE.with(|x| *x.get() = closure as *mut V as *mut u8);
        ((*UPCALLS).scan_object)(
            mem::transmute(
                scan_object_fn::<COMPRESSED, V> as *const unsafe extern "C" fn(edge: Address),
            ),
            mem::transmute(oop),
            tls,
        );
    }
}

struct AlignmentEncoding {}

impl AlignmentEncoding {
    const FIELD_WIDTH: u32 = 3;
    const MAX_ALIGN_WORDS: u32 = 1 << Self::FIELD_WIDTH;
    const FIELD_SHIFT: u32 = LOG_BYTES_IN_WORD as u32;
    // const ALIGNMENT_INCREMENT: u32 = 1 << Self::FIELD_SHIFT;
    const KLASS_MASK: u32 = (Self::MAX_ALIGN_WORDS - 1) << Self::FIELD_SHIFT;
    // const ALIGN_CODE_NONE: i32 = -1;
    // const VERBOSE: bool = false;

    fn get_klass_code_for_region(klass: &Klass) -> AlignmentEncodingPattern {
        let klass = klass as *const Klass as usize;
        // println!("binding klass 0x{:x}", klass);
        let align_code = ((klass & Self::KLASS_MASK as usize) >> Self::FIELD_SHIFT) as u32;
        debug_assert!(
            align_code < Self::MAX_ALIGN_WORDS,
            "Invalid align code"
        );
        let ret: AlignmentEncodingPattern = (align_code as u8).into();
        let inverse: u8 = ret.into();
        debug_assert!(inverse == align_code as u8);
        ret
    }
}

#[allow(unused)]
fn oop_iterate_with_encoding<const COMPRESSED: bool>(oop: Oop, closure: &mut impl EdgeVisitor<E<COMPRESSED>>) {
    let pattern = AlignmentEncoding::get_klass_code_for_region(oop.klass::<COMPRESSED>());
    pattern.oop_iterate(oop, closure);
}

fn oop_iterate<const COMPRESSED: bool>(oop: Oop, closure: &mut impl EdgeVisitor<E<COMPRESSED>>) {
    let klass = oop.klass::<COMPRESSED>();
    let klass_id = klass.id;
    assert!(
        klass_id as i32 >= 0 && (klass_id as i32) < 6,
        "Invalid klass-id: {:x} for oop: {:x}",
        klass_id as i32,
        unsafe { mem::transmute::<Oop, ObjectReference>(oop) }
    );
    match klass_id {
        KlassID::Instance => {
            let instance_klass = unsafe { klass.cast::<InstanceKlass>() };
            instance_klass.oop_iterate::<COMPRESSED>(oop, closure);
        }
        KlassID::InstanceClassLoader => {
            let instance_klass = unsafe { klass.cast::<InstanceClassLoaderKlass>() };
            instance_klass.oop_iterate::<COMPRESSED>(oop, closure);
        }
        KlassID::InstanceMirror => {
            let instance_klass = unsafe { klass.cast::<InstanceMirrorKlass>() };
            instance_klass.oop_iterate::<COMPRESSED>(oop, closure);
        }
        KlassID::ObjArray => {
            let array_klass = unsafe { klass.cast::<ObjArrayKlass>() };
            array_klass.oop_iterate::<COMPRESSED>(oop, closure);
        }
        KlassID::TypeArray => {
            // Skip scanning primitive arrays as they contain no reference fields.
        }
        KlassID::InstanceRef => {
            let instance_klass = unsafe { klass.cast::<InstanceRefKlass>() };
            instance_klass.oop_iterate::<COMPRESSED>(oop, closure);
        }
    }
}

thread_local! {
    static CLOSURE: UnsafeCell<*mut u8> = UnsafeCell::new(std::ptr::null_mut());
}

pub unsafe extern "C" fn scan_object_fn<
    const COMPRESSED: bool,
    V: EdgeVisitor<OpenJDKEdge<COMPRESSED>>,
>(
    edge: Address,
) {
    let ptr: *mut u8 = CLOSURE.with(|x| *x.get());
    let closure = &mut *(ptr as *mut V);
    closure.visit_edge(edge.into());
}

pub fn scan_object<const COMPRESSED: bool>(
    object: ObjectReference,
    closure: &mut impl EdgeVisitor<E<COMPRESSED>>,
    _tls: VMWorkerThread,
) {
    // println!("*****scan_object(0x{:x}) -> \n 0x{:x}, 0x{:x} \n",
    //     object,
    //     unsafe { *(object.value() as *const usize) },
    //     unsafe { *((object.value() + 8) as *const usize) }
    // );
    #[cfg(feature = "alignment_encoding")]
    unsafe { oop_iterate_with_encoding::<COMPRESSED>(mem::transmute(object), closure) }
    #[cfg(not(feature = "alignment_encoding"))]
    unsafe { oop_iterate::<COMPRESSED>(mem::transmute(object), closure) }
}

pub fn is_obj_array(oop: Oop) -> bool {
    oop.klass::<false>().id == KlassID::ObjArray
}

pub fn is_val_array(oop: Oop) -> bool {
    oop.klass::<false>().id == KlassID::TypeArray
}
