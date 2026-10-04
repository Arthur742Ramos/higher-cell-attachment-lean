module

public import HigherCellAttachment.OpenCover
public import HigherCellAttachment.Radial
public import Mathlib.Topology.Homeomorph.Lemmas

@[expose] public section


/-! # The punctured raw coproduct and its genuine quotient map -/

noncomputable section
namespace HigherCellAttachment
universe u v
open Topology

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {d : ι → ℕ}

abbrev PuncturedRaw (X : Type u) {ι : Type v} (d : ι → ℕ) := X ⊕ (Σ i : ι, PuncturedDisk (d i))

/-- Forget the nonzero condition while keeping the coproduct topology. -/
def puncturedRawInclusion : PuncturedRaw X d → Raw X d :=
  Sum.map id (Sigma.map id (fun _ => Subtype.val))

lemma puncturedDisk_isOpen {n : ℕ} : IsOpen {z : Disk n | (z : Euclid n) ≠ 0} :=
  isOpen_ne.preimage continuous_subtype_val

lemma puncturedSigmaInclusion_isOpenEmbedding :
    IsOpenEmbedding (Sigma.map id (fun _ : ι => Subtype.val) :
      (Σ i : ι, PuncturedDisk (d i)) → (Σ i : ι, Disk (d i))) :=
  (isOpenEmbedding_sigmaMap Function.injective_id).mpr
    (fun _ => puncturedDisk_isOpen.isOpenEmbedding_subtypeVal)

lemma puncturedRawInclusion_isOpenEmbedding :
    IsOpenEmbedding (puncturedRawInclusion : PuncturedRaw X d → Raw X d) := by
  apply IsOpenEmbedding.of_continuous_injective_isOpenMap
  · exact continuous_id.sumMap puncturedSigmaInclusion_isOpenEmbedding.continuous
  · exact Sum.map_injective.mpr ⟨Function.injective_id,
      puncturedSigmaInclusion_isOpenEmbedding.injective⟩
  · exact IsOpenMap.id.sumMap puncturedSigmaInclusion_isOpenEmbedding.isOpenMap

lemma puncturedRawInclusion_mem (f : ∀ i : ι, C(Sphere (d i), X)) (a : PuncturedRaw X d) :
    quotientMap f (puncturedRawInclusion a) ∈ puncturedNeighborhood f := by
  cases a with
  | inl x => exact inclusion_not_mem_centers f x
  | inr z =>
    rcases z with ⟨i, z⟩
    change quotientMap f (.inr ⟨i, z.1⟩) ∉ centers f
    rw [quotient_inr_mem_centers]
    exact z.property

/-- The punctured coproduct is exactly the open preimage of the punctured neighborhood. -/
def puncturedRawEquiv (f : ∀ i : ι, C(Sphere (d i), X)) :
    PuncturedRaw X d ≃ (quotientMap f ⁻¹' puncturedNeighborhood f) where
  toFun a := ⟨puncturedRawInclusion a, puncturedRawInclusion_mem f a⟩
  invFun
    | ⟨.inl x, _⟩ => .inl x
    | ⟨.inr ⟨i, z⟩, h⟩ => .inr ⟨i, ⟨z, by
        exact (quotient_inr_mem_centers f i z).not.mp h⟩⟩
  left_inv a := by cases a <;> rfl
  right_inv a := by rcases a with ⟨a,h⟩; cases a <;> rfl

/-- Its topology is the actual subspace topology of the raw coproduct. -/
def puncturedRawHomeomorph (f : ∀ i : ι, C(Sphere (d i), X)) :
    PuncturedRaw X d ≃ₜ (quotientMap f ⁻¹' puncturedNeighborhood f) :=
  (puncturedRawEquiv f).toHomeomorphOfIsInducing
    (puncturedRawInclusion_isOpenEmbedding.isEmbedding.codRestrict
      _ (puncturedRawInclusion_mem f)).isInducing

/-- The quotient onto the punctured neighborhood, with all disk punctures genuine. -/
def puncturedQuotient (f : ∀ i : ι, C(Sphere (d i), X)) : C(PuncturedRaw X d, puncturedNeighborhood f) where
  toFun a := ⟨quotientMap f (puncturedRawInclusion a), puncturedRawInclusion_mem f a⟩
  continuous_toFun := Continuous.subtype_mk
    ((quotientMap f).continuous.comp puncturedRawInclusion_isOpenEmbedding.continuous) _

lemma puncturedQuotient_isQuotientMap (f : ∀ i : ι, C(Sphere (d i), X)) :
    IsQuotientMap (puncturedQuotient f) := by
  have hq := (quotientMap_isQuotientMap f).restrictPreimage_isOpen
    (puncturedNeighborhood_isOpen f)
  exact hq.comp (puncturedRawHomeomorph f).isQuotientMap

end HigherCellAttachment
