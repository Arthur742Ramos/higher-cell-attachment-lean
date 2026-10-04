module

public import HigherCellAttachment.Adjunction

@[expose] public section


/-!
# Algebraic normal forms in the genuine attaching quotient

These normal forms classify quotient points. They do not replace the quotient
topology by a disjoint-union topology and are not asserted to be continuous.
-/

noncomputable section
namespace HigherCellAttachment
universe u v

abbrev OpenDisk (n : ℕ) := {z : Euclid n // ‖z‖ < 1}
abbrev NormalForm (X : Type u) {ι : Type v} (d : ι → ℕ) := X ⊕ (Σ i : ι, OpenDisk (d i))

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {d : ι → ℕ}

/-- The representative of an interior disk point in the raw disjoint union. -/
def interiorRepresentative (i : ι) (z : OpenDisk (d i)) : Raw X d :=
  .inr ⟨i, ⟨z, z.property.le⟩⟩

/-- Interior points remain points of their unique disk; boundary points go to X. -/
def normalize (f : ∀ i : ι, C(Sphere (d i), X)) : Raw X d → NormalForm X d
  | .inl x => .inl x
  | .inr ⟨i, z⟩ =>
      if h : ‖(z : Euclid (d i))‖ = 1 then .inl (f i (diskBoundaryPoint z h))
      else .inr ⟨i, ⟨z, lt_of_le_of_ne z.property h⟩⟩

theorem normalize_respects (f : ∀ i : ι, C(Sphere (d i), X)) {a b : Raw X d}
    (h : AttachingRel f a b) : normalize f a = normalize f b := by
  cases h with
  | boundary i z =>
    change (if h : ‖(z : Euclid (d i))‖ = 1 then (Sum.inl (f i (diskBoundaryPoint (boundaryInclusion z) h)) : NormalForm X d)
      else Sum.inr ⟨i, _⟩) = Sum.inl (f i z)
    rw [dite_eq_left (Sphere.norm_coe z)]
    rfl

/-- A well-defined algebraic normal form for every quotient point. -/
def normalForm (f : ∀ i : ι, C(Sphere (d i), X)) : Space f → NormalForm X d :=
  Quot.lift (normalize f) (fun _ _ h => normalize_respects f h)

/-- Pick the raw representative of a normal form. -/
def normalRepresentative : NormalForm X d → Raw X d
  | .inl x => .inl x
  | .inr ⟨i, z⟩ => interiorRepresentative i z

@[simp] theorem normalize_normalRepresentative (f : ∀ i : ι, C(Sphere (d i), X))
    (n : NormalForm X d) : normalize f (normalRepresentative n) = n := by
  cases n with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i, z⟩
    change (if h : ‖(z : Euclid (d i))‖ = 1 then _ else _) = _
    rw [dite_eq_right (ne_of_lt z.property)]

/-- Normalization changes a representative only by prescribed boundary gluings. -/
theorem quotient_normalRepresentative_normalize (f : ∀ i : ι, C(Sphere (d i), X)) (a : Raw X d) :
    quotientMap f (normalRepresentative (normalize f a)) = quotientMap f a := by
  cases a with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i, z⟩
    by_cases h : ‖(z : Euclid (d i))‖ = 1
    · simp only [normalize, h, dite_true, normalRepresentative]
      exact (Quot.sound (.boundary i (diskBoundaryPoint z h))).symm
    · simp only [normalize, h, dite_false, normalRepresentative, interiorRepresentative]

/-- Equality in the adjunction quotient is exactly equality of the algebraic normal forms. -/
theorem quotient_eq_iff_normalize_eq (f : ∀ i : ι, C(Sphere (d i), X)) (a b : Raw X d) :
    quotientMap f a = quotientMap f b ↔ normalize f a = normalize f b := by
  constructor
  · exact fun h => congrArg (normalForm f) h
  · intro h
    rw [← quotient_normalRepresentative_normalize f a,
      ← quotient_normalRepresentative_normalize f b, h]

/-- Every interior point has its own unchanged normal form. -/
@[simp] theorem normalForm_interiorRepresentative (f : ∀ i : ι, C(Sphere (d i), X)) (i : ι) (z : OpenDisk (d i)) :
    normalForm f (quotientMap f (interiorRepresentative i z)) = .inr ⟨i, z⟩ :=
  normalize_normalRepresentative f (.inr ⟨i, z⟩)

@[simp] theorem normalForm_inclusion (f : ∀ i : ι, C(Sphere (d i), X)) (x : X) :
    normalForm f (inclusion f x) = .inl x := rfl

/-- All disk interiors embed algebraically as a disjoint family. -/
theorem interiors_injective (f : ∀ i : ι, C(Sphere (d i), X)) :
    Function.Injective (fun z : Σ i : ι, OpenDisk (d i) =>
      quotientMap f (interiorRepresentative z.1 z.2)) := by
  intro a b h
  have h' := congrArg (normalForm f) h
  simpa using h'

/-- No interior point is identified with an original point. -/
theorem interior_ne_inclusion (f : ∀ i : ι, C(Sphere (d i), X)) (i : ι) (z : OpenDisk (d i)) (x : X) :
    quotientMap f (interiorRepresentative i z) ≠ inclusion f x := by
  intro h
  have h' := congrArg (normalForm f) h
  simpa using h'

end HigherCellAttachment
