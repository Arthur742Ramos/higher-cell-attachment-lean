module

public import HigherCellAttachment.OpenCover
public import ClassicalSVK.Pushout

@[expose] public section


/-! # Van Kampen on the actual disk-center/interior open cover -/

noncomputable section
open CategoryTheory CategoryTheory.Limits
namespace HigherCellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {d : ι → ℕ}

/-- The actual intersection of the two quotient open sets. -/
def overlap (f : ∀ i : ι, C(Sphere (d i), X)) : Set (Space f) :=
  puncturedNeighborhood f ∩ interiors f

/-- Actual overlap inclusion into the punctured neighborhood. -/
def overlapLeft (f : ∀ i : ι, C(Sphere (d i), X)) : C(overlap f, puncturedNeighborhood f) :=
  ⟨fun y => ⟨y.1,y.2.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- Actual overlap inclusion into the disk interiors. -/
def overlapRight (f : ∀ i : ι, C(Sphere (d i), X)) : C(overlap f, interiors f) :=
  ⟨fun y => ⟨y.1,y.2.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The actual inclusion of the punctured neighborhood into the quotient. -/
def neighborhoodToSpace (f : ∀ i : ι, C(Sphere (d i), X)) : C(puncturedNeighborhood f, Space f) :=
  ⟨Subtype.val,continuous_subtype_val⟩

/-- The actual inclusion of all disk interiors into the quotient. -/
def interiorsToSpace (f : ∀ i : ι, C(Sphere (d i), X)) : C(interiors f, Space f) :=
  ⟨Subtype.val,continuous_subtype_val⟩

/-- The established ordinary all-object fundamental-groupoid SVK theorem is
applied to proved open sets in the genuine adjunction quotient. -/
theorem coverPushout (f : ∀ i : ι, C(Sphere (d i), X)) :
    IsPushout (FundamentalGroupoid.map (overlapLeft f)).toCatHom
      (FundamentalGroupoid.map (overlapRight f)).toCatHom
      (FundamentalGroupoid.map (neighborhoodToSpace f)).toCatHom
      (FundamentalGroupoid.map (interiorsToSpace f)).toCatHom := by
  exact ClassicalSVK.classicalOpenCoverPushout (puncturedNeighborhood f) (interiors f)
    (puncturedNeighborhood_isOpen f) (interiors_isOpen f) (openCover_union f)

end HigherCellAttachment
