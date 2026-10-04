module
public import HigherCellAttachment.GeometricPushout
public import HigherCellAttachment.Statement
@[expose] public section
noncomputable section
namespace HigherCellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]
variable {ι : Type v} {d : ι → ℕ}

/-- The actual inclusion into the boundary-generated topological quotient
induces a bijective homomorphism, with no extra global or local assumptions. -/
theorem inclusionPi1_bijective (hd : ∀ i, 3 ≤ d i)
    (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X) :
    Function.Bijective (inclusionPi1 f x₀) := by
  letI (i : ι) : Fact (3 ≤ d i) := ⟨hd i⟩
  have h := (neighborhood_inclusion_bijective f x₀).comp
    (neighborhoodPi1Equiv f x₀).bijective
  have hf := inclusionPi1_factorization f x₀
  change Function.Bijective ((FundamentalGroup.map (neighborhoodToSpace f)
    (neighborhoodInclusion f x₀)).comp (neighborhoodPi1Equiv f x₀).toMonoidHom) at h
  rwa [hf] at h

/-- Full mixed-dimension, arbitrary-family higher-cell attachment invariance. -/
theorem higher_cell_attachment : completeStatement.{u,v} := by
  intro X _ _ ι d hd f x₀
  have h := inclusionPi1_bijective hd f x₀
  exact ⟨h, MulEquiv.ofBijective (inclusionPi1 f x₀) h, rfl⟩
end HigherCellAttachment
