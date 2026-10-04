module
public import HigherCellAttachment.Adjunction
@[expose] public section
noncomputable section
namespace HigherCellAttachment
universe u v
/-- Attaching an arbitrary family of genuine closed cells of independently
varying dimensions at least three preserves the actual based fundamental
group. The displayed equivalence has exactly the inclusion-induced homomorphism. -/
def completeStatement : Prop :=
  ∀ (X : Type u) [TopologicalSpace X] [PathConnectedSpace X]
    (ι : Type v) (d : ι → ℕ) (_hd : ∀ i, 3 ≤ d i)
    (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X),
    Function.Bijective (inclusionPi1 f x₀) ∧
      ∃ E : FundamentalGroup X x₀ ≃* FundamentalGroup (Space f) (inclusion f x₀),
        E.toMonoidHom = inclusionPi1 f x₀
end HigherCellAttachment
