module
public import CellAttachment.GroupoidQuotient
public import HigherCellAttachment.CoverModels
public import HigherCellAttachment.NeighborhoodPi1
@[expose] public section

/-! # Higher-cell vertex groups from the actual two-open-set van Kampen square -/
noncomputable section
set_option backward.isDefEq.respectTransparency false
open CategoryTheory CategoryTheory.Limits
namespace HigherCellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {d : ι → ℕ}
variable [∀ i, Fact (3 ≤ d i)]

theorem overlapLeft_groupoid_obj_injective (f : ∀ i : ι, C(Sphere (d i), X)) :
    Function.Injective (FundamentalGroupoid.map (overlapLeft f)).obj := by
  rintro ⟨a⟩ ⟨b⟩ h
  congr 1
  apply Subtype.ext
  exact congrArg (fun z => z.as.1) h

theorem neighborhood_base_outside_overlap (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X)
    (w : FundamentalGroupoid (overlap f)) :
    (FundamentalGroupoid.map (overlapLeft f)).obj w ≠
      FundamentalGroupoid.mk (neighborhoodInclusion f x₀) := by
  intro h
  have hw : (w.as : Space f) = inclusion f x₀ := congrArg (fun z => z.as.1) h
  exact inclusion_not_mem_interiors f x₀ (hw ▸ w.as.property.2)

theorem neighborhood_groupoid_connected (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X)
    [PathConnectedSpace X] (w : FundamentalGroupoid (puncturedNeighborhood f)) :
    Nonempty (FundamentalGroupoid.mk (neighborhoodInclusion f x₀) ⟶ w) := by
  letI := neighborhood_pathConnectedSpace f x₀
  exact ⟨Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath _ _)⟩

/-- The actual neighborhood inclusion induces a bijection on fundamental groups.
The categorical bridge is applied to the constructed open-cover pushout.
Its cyclic-generator input is instantiated by the identity because each
higher-cell overlap vertex group has been proved trivial. -/
theorem neighborhood_inclusion_bijective
    (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X) [PathConnectedSpace X] :
    Function.Bijective
      (FundamentalGroup.map (neighborhoodToSpace f) (neighborhoodInclusion f x₀)) := by
  letI := neighborhood_pathConnectedSpace f x₀
  let I := ULift.{u} ι
  let indexA : FundamentalGroupoid (overlap f) → I := fun w => ⟨overlapIndex f w.as⟩
  let indexC : FundamentalGroupoid (interiors f) → I := fun w => ⟨interiorIndex f w.as⟩
  let anchor : I → FundamentalGroupoid (overlap f) :=
    fun i => FundamentalGroupoid.mk (overlapAnchor f i.down)
  let q : ∀ w : FundamentalGroupoid (overlap f), anchor (indexA w) ⟶ w :=
    fun w => Path.Homotopic.Quotient.mk (overlapAnchorPaths f w.as)
  let s : ∀ w : FundamentalGroupoid (interiors f),
      (FundamentalGroupoid.map (overlapRight f)).obj (anchor (indexC w)) ⟶ w :=
    fun w => Path.Homotopic.Quotient.mk (interiorAnchorPaths f w.as)
  let p : ∀ i : I, FundamentalGroupoid.mk (neighborhoodInclusion f x₀) ⟶
      (FundamentalGroupoid.map (overlapLeft f)).obj (anchor i) :=
    fun i => Path.Homotopic.Quotient.mk (PathConnectedSpace.somePath _ _)
  let r : ∀ i : I, End (anchor i) := fun _ => 1
  have hindexC : ∀ (y z : FundamentalGroupoid (interiors f)) (_γ : y ⟶ z),
      indexC y = indexC z := by
    intro y z γ
    exact congrArg ULift.up (interiorIndex_arrow f γ)
  have hindex : ∀ w : FundamentalGroupoid (overlap f),
      indexC ((FundamentalGroupoid.map (overlapRight f)).obj w) = indexA w := by
    intro w
    exact congrArg ULift.up (interiorIndex_overlapToInteriors f w.as)
  have hcyc : ∀ (i : I) (g : End (anchor i)), ∃ n : ℤ, g = r i ^ n := by
    intro i g
    letI := overlapVertexGroup_subsingleton f (overlapAnchor f i.down)
    exact ⟨0, Subsingleton.elim _ _⟩
  obtain ⟨hs,hk,_⟩ := CellAttachment.pushout_vertex_quotient_of_component_data
    (FundamentalGroupoid.map (overlapLeft f)) (FundamentalGroupoid.map (overlapRight f))
    (FundamentalGroupoid.map (neighborhoodToSpace f)) (FundamentalGroupoid.map (interiorsToSpace f))
    (coverPushout f) (overlapLeft_groupoid_obj_injective f)
    (FundamentalGroupoid.mk (neighborhoodInclusion f x₀))
    (neighborhood_base_outside_overlap f x₀) (neighborhood_groupoid_connected f x₀)
    indexA indexC anchor q p s (fun w => interiorVertexGroup_subsingleton f w.as)
    hindexC hindex r hcyc
  have hn : Subgroup.normalClosure (Set.range (fun i : I =>
      CellAttachment.overlapLoop (FundamentalGroupoid.map (overlapLeft f))
        (FundamentalGroupoid.mk (neighborhoodInclusion f x₀)) (anchor i) (p i) (r i))) = ⊥ := by
    apply Subgroup.normalClosure_eq_bot_iff.mpr
    rintro g ⟨i,rfl⟩
    change CellAttachment.transportEnd (p i)
      ((FundamentalGroupoid.map (overlapLeft f)).mapEnd (anchor i) 1) = 1
    rw [map_one, map_one]
  have hk' : (FundamentalGroup.map (neighborhoodToSpace f)
      (neighborhoodInclusion f x₀)).ker = ⊥ := hk.trans hn
  exact ⟨(MonoidHom.ker_eq_bot_iff _).mp hk', hs⟩

end HigherCellAttachment
