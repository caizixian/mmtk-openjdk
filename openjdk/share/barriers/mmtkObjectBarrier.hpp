#ifndef MMTK_OPENJDK_BARRIERS_MMTK_OBJECT_BARRIER_HPP
#define MMTK_OPENJDK_BARRIERS_MMTK_OBJECT_BARRIER_HPP

#include "../mmtk.h"
#include "../mmtkBarrierSet.hpp"
#include "utilities/macros.hpp"
#include CPU_HEADER(mmtkBarrierSetAssembler)
#include CPU_HEADER(mmtkObjectBarrierSetAssembler)
#ifdef COMPILER1
#include "../mmtkBarrierSetC1.hpp"
#include "c1/c1_LIRAssembler.hpp"
#include "c1/c1_MacroAssembler.hpp"
#endif
#ifdef COMPILER2
#include "../mmtkBarrierSetC2.hpp"
#include "opto/callnode.hpp"
#include "opto/idealKit.hpp"
#endif
#include "gc/shared/barrierSet.hpp"

#define SIDE_METADATA_WORST_CASE_RATIO_LOG 1
#define LOG_BYTES_IN_CHUNK 22
#define CHUNK_MASK ((1L << LOG_BYTES_IN_CHUNK) - 1)

const intptr_t SIDE_METADATA_BASE_ADDRESS = (intptr_t) GLOBAL_SIDE_METADATA_VM_BASE_ADDRESS;

class MMTkObjectBarrierSetRuntime: public MMTkBarrierSetRuntime {
public:
  // Interfaces called by `MMTkBarrierSet::AccessBarrier`
  virtual void object_reference_write_post(oop src, oop* slot, oop target) const override;
  virtual void object_reference_array_copy_post(oop* src, oop* dst, size_t count) const override {
    object_reference_array_copy_post_call((void*) src, (void*) dst, count);
  }
};

#ifdef COMPILER1
class MMTkObjectBarrierSetC1: public MMTkBarrierSetC1 {
protected:
  virtual void object_reference_write_post(LIRAccess& access, LIR_Opr src, LIR_Opr slot, LIR_Opr new_val) const override;

  virtual LIR_Opr resolve_address(LIRAccess& access, bool resolve_in_register) override {
    return MMTkBarrierSetC1::resolve_address_in_register(access, resolve_in_register);
  }
};
#else
class MMTkObjectBarrierSetC1;
#endif

#ifdef COMPILER2
class MMTkObjectBarrierSetC2: public MMTkBarrierSetC2 {
protected:
  virtual void object_reference_write_post(GraphKit* kit, Node* src, Node* slot, Node* val) const override;
};
#else
class MMTkObjectBarrierSetC2;
#endif

struct MMTkObjectBarrier: MMTkBarrierImpl<
  MMTkObjectBarrierSetRuntime,
  MMTkObjectBarrierSetAssembler,
  MMTkObjectBarrierSetC1,
  MMTkObjectBarrierSetC2
> {};

#endif // MMTK_OPENJDK_BARRIERS_MMTK_OBJECT_BARRIER_HPP
