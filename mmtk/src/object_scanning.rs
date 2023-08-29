use crate::SINGLETON;

use crate::abi::*;
use crate::{OpenJDKEdge, UPCALLS};
use mmtk::util::constants::*;
use mmtk::util::opaque_pointer::*;
use mmtk::util::{Address, ObjectReference};
use mmtk::vm::EdgeVisitor;
use std::{mem, slice};

trait OopIterate: Sized {
    fn oop_iterate(&self, oop: Oop, closure: &mut impl EdgeVisitor<OpenJDKEdge>);
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
    fn oop_iterate(&self, oop: Oop, closure: &mut impl EdgeVisitor<OpenJDKEdge>) {
        match self {
            // Currently exclude mirrors, refs, and instances with references
            // patterns we cannot encode
            AlignmentEncodingPattern::Fallback => oop_iterate(oop, closure),
            AlignmentEncodingPattern::RefArray => {
                let array = unsafe { oop.as_array_oop() };
                for oop in unsafe { array.data::<Oop>(BasicType::T_OBJECT) } {
                    closure.visit_edge(Address::from_ref(oop as &Oop));
                }
            }
            AlignmentEncodingPattern::NoRef => {}
            AlignmentEncodingPattern::Ref0 => {
                // if the first field (field 0) is a ref field, it has an offset of 16 from oop
                let start = oop.get_field_address(2 * BYTES_IN_WORD as i32);
                closure.visit_edge(start + (0usize << LOG_BYTES_IN_ADDRESS));
            }
            AlignmentEncodingPattern::Ref1_2_3 => {
                let start = oop.get_field_address(2 * BYTES_IN_WORD as i32);
                closure.visit_edge(start + (1usize << LOG_BYTES_IN_ADDRESS));
                closure.visit_edge(start + (2usize << LOG_BYTES_IN_ADDRESS));
                closure.visit_edge(start + (3usize << LOG_BYTES_IN_ADDRESS));
            }
            AlignmentEncodingPattern::Ref4_5_6 => {
                let start = oop.get_field_address(2 * BYTES_IN_WORD as i32);
                closure.visit_edge(start + (4usize << LOG_BYTES_IN_ADDRESS));
                closure.visit_edge(start + (5usize << LOG_BYTES_IN_ADDRESS));
                closure.visit_edge(start + (6usize << LOG_BYTES_IN_ADDRESS));
            }
            AlignmentEncodingPattern::Ref2 => {
                let start = oop.get_field_address(2 * BYTES_IN_WORD as i32);
                closure.visit_edge(start + (2usize << LOG_BYTES_IN_ADDRESS));
            }
            AlignmentEncodingPattern::Ref0_1 => {
                let start = oop.get_field_address(2 * BYTES_IN_WORD as i32);
                closure.visit_edge(start + (0usize << LOG_BYTES_IN_ADDRESS));
                closure.visit_edge(start + (1usize << LOG_BYTES_IN_ADDRESS));
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
    fn oop_iterate(&self, oop: Oop, closure: &mut impl EdgeVisitor<OpenJDKEdge>) {
        let start = oop.get_field_address(self.offset);
        for i in 0..self.count as usize {
            let edge = start + (i << LOG_BYTES_IN_ADDRESS);
            closure.visit_edge(edge);
        }
    }
}

impl OopIterate for InstanceKlass {
    fn oop_iterate(&self, oop: Oop, closure: &mut impl EdgeVisitor<OpenJDKEdge>) {
        let oop_maps = self.nonstatic_oop_maps();
        for map in oop_maps {
            map.oop_iterate(oop, closure)
        }
    }
}

impl OopIterate for InstanceMirrorKlass {
    fn oop_iterate(&self, oop: Oop, closure: &mut impl EdgeVisitor<OpenJDKEdge>) {
        self.instance_klass.oop_iterate(oop, closure);
        // if (Devirtualizer::do_metadata(closure)) {
        //     Klass* klass = java_lang_Class::as_Klass(obj);
        //     // We'll get NULL for primitive mirrors.
        //     if (klass != NULL) {
        //       if (klass->is_instance_klass() && InstanceKlass::cast(klass)->is_anonymous()) {
        //         // An anonymous class doesn't have its own class loader, so when handling
        //         // the java mirror for an anonymous class we need to make sure its class
        //         // loader data is claimed, this is done by calling do_cld explicitly.
        //         // For non-anonymous classes the call to do_cld is made when the class
        //         // loader itself is handled.
        //         Devirtualizer::do_cld(closure, klass->class_loader_data());
        //       } else {
        //         Devirtualizer::do_klass(closure, klass);
        //       }
        //     } else {
        //       // We would like to assert here (as below) that if klass has been NULL, then
        //       // this has been a mirror for a primitive type that we do not need to follow
        //       // as they are always strong roots.
        //       // However, we might get across a klass that just changed during CMS concurrent
        //       // marking if allocation occurred in the old generation.
        //       // This is benign here, as we keep alive all CLDs that were loaded during the
        //       // CMS concurrent phase in the class loading, i.e. they will be iterated over
        //       // and kept alive during remark.
        //       // assert(java_lang_Class::is_primitive(obj), "Sanity check");
        //     }
        // }

        // static fields
        let start: *const Oop = Self::start_of_static_fields(oop).to_ptr::<Oop>();
        let len = Self::static_oop_field_count(oop);
        let slice = unsafe { slice::from_raw_parts(start, len as _) };
        for oop in slice {
            closure.visit_edge(Address::from_ref(oop as &Oop));
        }
    }
}

impl OopIterate for InstanceClassLoaderKlass {
    fn oop_iterate(&self, oop: Oop, closure: &mut impl EdgeVisitor<OpenJDKEdge>) {
        self.instance_klass.oop_iterate(oop, closure);
        // if (Devirtualizer::do_metadata(closure)) {
        //     ClassLoaderData* cld = java_lang_ClassLoader::loader_data(obj);
        //     // cld can be null if we have a non-registered class loader.
        //     if (cld != NULL) {
        //         Devirtualizer::do_cld(closure, cld);
        //     }
        // }
    }
}

impl OopIterate for ObjArrayKlass {
    fn oop_iterate(&self, oop: Oop, closure: &mut impl EdgeVisitor<OpenJDKEdge>) {
        let array = unsafe { oop.as_array_oop() };
        for oop in unsafe { array.data::<Oop>(BasicType::T_OBJECT) } {
            closure.visit_edge(Address::from_ref(oop as &Oop));
        }
    }
}

impl OopIterate for TypeArrayKlass {
    fn oop_iterate(&self, _oop: Oop, _closure: &mut impl EdgeVisitor<OpenJDKEdge>) {
        // Performance tweak: We skip processing the klass pointer since all
        // TypeArrayKlasses are guaranteed processed via the null class loader.
    }
}

impl OopIterate for InstanceRefKlass {
    fn oop_iterate(&self, oop: Oop, closure: &mut impl EdgeVisitor<OpenJDKEdge>) {
        use crate::abi::*;
        use crate::api::{add_phantom_candidate, add_soft_candidate, add_weak_candidate};
        self.instance_klass.oop_iterate(oop, closure);

        if Self::should_scan_weak_refs() {
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
    fn should_scan_weak_refs() -> bool {
        !*SINGLETON.get_options().no_reference_types
    }
    fn process_ref_as_strong(oop: Oop, closure: &mut impl EdgeVisitor<OpenJDKEdge>) {
        let referent_addr = Self::referent_address(oop);
        closure.visit_edge(referent_addr);
        let discovered_addr = Self::discovered_address(oop);
        closure.visit_edge(discovered_addr);
    }
}

#[allow(unused)]
fn oop_iterate_slow(oop: Oop, closure: &mut impl EdgeVisitor<OpenJDKEdge>, tls: OpaquePointer) {
    unsafe {
        ((*UPCALLS).scan_object)(closure as *mut _ as _, mem::transmute(oop), tls);
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

fn oop_iterate_with_encoding(oop: Oop, closure: &mut impl EdgeVisitor<OpenJDKEdge>) {
    let pattern = AlignmentEncoding::get_klass_code_for_region(oop.klass);
    pattern.oop_iterate(oop, closure);
}

fn oop_iterate(oop: Oop, closure: &mut impl EdgeVisitor<OpenJDKEdge>) {
    let klass_id = oop.klass.id;
    debug_assert!(
        klass_id as i32 >= 0 && (klass_id as i32) < 6,
        "Invalid klass-id: {:x} for oop: {:x}",
        klass_id as i32,
        unsafe { mem::transmute::<Oop, ObjectReference>(oop) }
    );
    match klass_id {
        KlassID::Instance => {
            let instance_klass = unsafe { oop.klass.cast::<InstanceKlass>() };
            instance_klass.oop_iterate(oop, closure);
        }
        KlassID::InstanceClassLoader => {
            let instance_klass = unsafe { oop.klass.cast::<InstanceClassLoaderKlass>() };
            instance_klass.oop_iterate(oop, closure);
        }
        KlassID::InstanceMirror => {
            let instance_klass = unsafe { oop.klass.cast::<InstanceMirrorKlass>() };
            instance_klass.oop_iterate(oop, closure);
        }
        KlassID::ObjArray => {
            let array_klass = unsafe { oop.klass.cast::<ObjArrayKlass>() };
            array_klass.oop_iterate(oop, closure);
        }
        KlassID::TypeArray => {
            let array_klass = unsafe { oop.klass.cast::<TypeArrayKlass>() };
            array_klass.oop_iterate(oop, closure);
        }
        KlassID::InstanceRef => {
            let instance_klass = unsafe { oop.klass.cast::<InstanceRefKlass>() };
            instance_klass.oop_iterate(oop, closure);
        } // _ => oop_iterate_slow(oop, closure, tls),
    }
}

pub fn scan_object(
    object: ObjectReference,
    closure: &mut impl EdgeVisitor<OpenJDKEdge>,
    _tls: VMWorkerThread,
) {
    // println!("*****scan_object(0x{:x}) -> \n 0x{:x}, 0x{:x} \n",
    //     object,
    //     unsafe { *(object.value() as *const usize) },
    //     unsafe { *((object.value() + 8) as *const usize) }
    // );
    unsafe { oop_iterate_with_encoding(mem::transmute(object), closure) }
}

pub fn is_obj_array(oop: Oop) -> bool {
    oop.klass.id == KlassID::ObjArray
}

pub fn is_val_array(oop: Oop) -> bool {
    oop.klass.id == KlassID::TypeArray
}
