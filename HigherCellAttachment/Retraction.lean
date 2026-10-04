module

public import HigherCellAttachment.RawNeighborhood

@[expose] public section


/-!
# Radial retraction onto the original space

The descent below uses the actual quotient map on the open punctured neighborhood.
No retraction is assumed as a hypothesis.
-/

noncomputable section
namespace HigherCellAttachment
universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {d : ι → ℕ}

@[simp] lemma polar_boundary {n : ℕ} (z : Sphere n) :
    polar ⟨boundaryInclusion z, Sphere.coe_ne_zero z⟩ = z := by
  apply Subtype.ext
  change (‖(z : Euclid n)‖⁻¹ : ℝ) • (z : Euclid n) = z
  simp [Sphere.norm_coe]

/-- An algebraic extension to disk centers, used only to define quotient descent.
Continuity is asserted only after restricting to the punctured neighborhood. -/
def rawRetraction (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X) : Raw X d → X
  | .inl x => x
  | .inr ⟨i,z⟩ => if h : (z : Euclid (d i)) ≠ 0 then f i (polar ⟨z,h⟩) else x₀

lemma rawRetraction_respects (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X)
    {a b : Raw X d} (h : AttachingRel f a b) : rawRetraction f x₀ a = rawRetraction f x₀ b := by
  cases h with
  | boundary i z =>
    change (if h : (z : Euclid (d i)) ≠ 0 then f i (polar ⟨boundaryInclusion z,h⟩) else x₀) = f i z
    rw [dite_eq_left (Sphere.coe_ne_zero z), polar_boundary]

/-- Algebraic quotient descent, prior to its restriction to the continuous domain. -/
def quotientRetraction (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X) : Space f → X :=
  Quot.lift (rawRetraction f x₀) (fun _ _ h => rawRetraction_respects f x₀ h)

@[simp] lemma quotientRetraction_inclusion (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ x : X) :
    quotientRetraction f x₀ (inclusion f x) = x := rfl

/-- On the punctured raw coproduct the retraction is continuous componentwise. -/
lemma quotientRetraction_puncturedQuotient (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X)
    (a : PuncturedRaw X d) :
    quotientRetraction f x₀ (puncturedQuotient f a) =
      Sum.elim id (fun z : Σ i : ι, PuncturedDisk (d i) => f z.1 (polar z.2)) a := by
  cases a with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i,z⟩
    exact dite_eq_left z.property

lemma quotientRetraction_continuousOnNeighborhood (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X) :
    Continuous (fun y : puncturedNeighborhood f => quotientRetraction f x₀ y) := by
  apply (puncturedQuotient_isQuotientMap f).continuous_iff.mpr
  have h : Continuous (Sum.elim id
      (fun z : Σ i : ι, PuncturedDisk (d i) => f z.1 (polar z.2))) := by
    apply Continuous.sumElim continuous_id
    apply continuous_sigma
    intro i
    exact (f i).continuous.comp polar.continuous
  simpa only [Function.comp_def, quotientRetraction_puncturedQuotient] using h

/-- The proved continuous retraction onto the actual original space. -/
def neighborhoodRetraction (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X) :
    C(puncturedNeighborhood f, X) :=
  ⟨fun y => quotientRetraction f x₀ y, quotientRetraction_continuousOnNeighborhood f x₀⟩

/-- The actual inclusion, codomain-restricted to the punctured neighborhood. -/
def neighborhoodInclusion (f : ∀ i : ι, C(Sphere (d i), X)) : C(X, puncturedNeighborhood f) :=
  ⟨fun x => ⟨inclusion f x, inclusion_not_mem_centers f x⟩,
    (inclusion f).continuous.subtype_mk _⟩

@[simp] theorem neighborhoodRetraction_inclusion (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ x : X) :
    neighborhoodRetraction f x₀ (neighborhoodInclusion f x) = x := rfl

end HigherCellAttachment
