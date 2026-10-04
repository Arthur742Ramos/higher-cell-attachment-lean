/-
Copyright (c) 2019 Sébastien Gouëzel. All rights reserved.
Copyright (c) 2026 Sebastian Kumar. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Sébastien Gouëzel, Sebastian Kumar
Narrow dependency closure vendored from mathlib PR #28246,
Sebi-Kumar/mathlib4 commit 037ad801e1e5a5b7aa1750957c07f7769812effc.
-/
module
public import Mathlib.Logic.Equiv.PartialEquiv
@[expose] public section
open Set
namespace PartialEquiv
variable {α β : Type*} (e : PartialEquiv α β)
theorem image_source_minus_singleton_eq {a : α} (h : a ∈ e.source) :
    e '' (e.source \ {a}) = e.target \ {e a} := by
  rw [image_sdiff_of_injOn, image_source_eq_target, image_singleton]
  · exact e.injOn
  · exact singleton_subset_iff.mpr h
theorem symm_image_target_minus_singleton_eq {b : β} (h : b ∈ e.target) :
    e.symm '' (e.target \ {b}) = e.source \ {e.symm b} := e.symm.image_source_minus_singleton_eq h
end PartialEquiv
