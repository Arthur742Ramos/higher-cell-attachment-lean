module

public import HigherCellAttachment.Retraction
public import Mathlib.Topology.CompactOpen
public import Mathlib.Topology.Homeomorph.Lemmas
public import Mathlib.Topology.Homotopy.Equiv

@[expose] public section


/-!
# Jointly continuous radial deformation on the genuine adjunction quotient

Continuity is descended from the actual punctured quotient using local compactness
of the interval. No global openness of the quotient map is assumed.
-/

noncomputable section
set_option maxHeartbeats 800000
set_option backward.isDefEq.respectTransparency false
open scoped unitInterval
namespace HigherCellAttachment
universe u v

variable {X : Type u} [TopologicalSpace X] {ι : Type v} {d : ι → ℕ}

/-- Expand each punctured disk radially while fixing the original space and centers. -/
def rawRadial (t : unitInterval) : Raw X d → Raw X d
  | .inl x => .inl x
  | .inr ⟨i,z⟩ => if h : (z : Euclid (d i)) ≠ 0 then .inr ⟨i,(radialDeformation t ⟨z,h⟩).1⟩
      else .inr ⟨i,z⟩

lemma rawRadial_respects (f : ∀ i : ι, C(Sphere (d i), X)) (t : unitInterval)
    {a b : Raw X d} (h : AttachingRel f a b) :
    AttachingRel f (rawRadial t a) (rawRadial t b) := by
  cases h with
  | boundary i z =>
    change AttachingRel f
      (if h : (z : Euclid (d i)) ≠ 0 then .inr ⟨i,(radialDeformation t ⟨boundaryInclusion z,h⟩).1⟩
        else .inr ⟨i,boundaryInclusion z⟩) (.inl (f i z))
    rw [dite_eq_left (Sphere.coe_ne_zero z)]
    have hfix : (radialDeformation (n := d i) t
        ⟨boundaryInclusion z, Sphere.coe_ne_zero z⟩).1 = boundaryInclusion z :=
      congrArg Subtype.val (radialDeformation_boundary_fixed (n := d i) t
        ⟨boundaryInclusion z, Sphere.coe_ne_zero z⟩ (Sphere.norm_coe z))
    rw [hfix]
    exact .boundary i z

/-- Algebraic radial descent; joint continuity on the punctured neighborhood is proved below. -/
def quotientRadial (f : ∀ i : ι, C(Sphere (d i), X)) (t : unitInterval) : Space f → Space f :=
  Quot.map (rawRadial (X := X) (d := d) t) (fun _ _ h => rawRadial_respects f t h)

@[simp] lemma quotientRadial_inclusion (f : ∀ i : ι, C(Sphere (d i), X)) (t : unitInterval) (x : X) :
    quotientRadial f t (inclusion f x) = inclusion f x := rfl

lemma quotientRadial_puncturedQuotient (f : ∀ i : ι, C(Sphere (d i), X)) (t : unitInterval)
    (a : PuncturedRaw X d) :
    quotientRadial f t (puncturedQuotient f a) =
      puncturedQuotient f (Sum.map id (Sigma.map id (fun _ => radialDeformation t)) a) := by
  cases a with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i,z⟩
    change quotientMap f (if h : (z.1 : Euclid (d i)) ≠ 0 then _ else _) = _
    rw [dite_eq_left z.property]
    rfl

lemma quotientRadial_mem_neighborhood (f : ∀ i : ι, C(Sphere (d i), X)) (t : unitInterval)
    (y : puncturedNeighborhood f) : quotientRadial f t y ∈ puncturedNeighborhood f := by
  obtain ⟨a,ha⟩ := (puncturedQuotient_isQuotientMap f).surjective y
  rw [← ha, quotientRadial_puncturedQuotient]
  exact (puncturedQuotient f _).property

/-- The descended radial deformation, with codomain the genuine neighborhood. -/
def neighborhoodRadial (f : ∀ i : ι, C(Sphere (d i), X)) (t : unitInterval)
    (y : puncturedNeighborhood f) : puncturedNeighborhood f :=
  ⟨quotientRadial f t y, quotientRadial_mem_neighborhood f t y⟩

lemma neighborhoodRadial_puncturedQuotient (f : ∀ i : ι, C(Sphere (d i), X)) (t : unitInterval)
    (a : PuncturedRaw X d) :
    neighborhoodRadial f t (puncturedQuotient f a) =
      puncturedQuotient f (Sum.map id (Sigma.map id (fun _ => radialDeformation t)) a) := by
  apply Subtype.ext
  exact quotientRadial_puncturedQuotient f t a

/-- The raw deformation is jointly continuous, using the coproduct and sigma topologies. -/
lemma puncturedQuotient_radial_continuous (f : ∀ i : ι, C(Sphere (d i), X)) :
    Continuous (fun p : unitInterval × PuncturedRaw X d =>
      puncturedQuotient f (Sum.map id (Sigma.map id (fun _ => radialDeformation p.1)) p.2)) := by
  have hl : Continuous (fun p : unitInterval × X => puncturedQuotient f (.inl p.2)) :=
    (puncturedQuotient f).continuous.comp (continuous_inl.comp continuous_snd)
  have hs : Continuous (fun p : Σ i : ι, PuncturedDisk (d i) × unitInterval =>
      puncturedQuotient f (.inr ⟨p.1, radialDeformation p.2.2 p.2.1⟩)) := by
    apply continuous_sigma
    intro i
    exact (puncturedQuotient f).continuous.comp
      (continuous_inr.comp (continuous_sigmaMk.comp
        (radialDeformation_continuous.comp continuous_swap)))
  let e : unitInterval × (Σ i : ι, PuncturedDisk (d i)) ≃ₜ
      (Σ i : ι, PuncturedDisk (d i) × unitInterval) :=
    (Homeomorph.prodComm _ _).trans Homeomorph.sigmaProdDistrib
  have hr : Continuous (fun p : unitInterval × (Σ i : ι, PuncturedDisk (d i)) =>
      puncturedQuotient f (.inr ⟨p.2.1, radialDeformation p.1 p.2.2⟩)) :=
    hs.comp e.continuous
  convert (hl.sumElim hr).comp (Homeomorph.prodSumDistrib.continuous) using 1
  ext p
  rcases p with ⟨t,a⟩
  cases a <;> rfl

/-- Joint continuity of the quotient homotopy, rather than continuity at each time. -/
lemma neighborhoodRadial_continuous (f : ∀ i : ι, C(Sphere (d i), X)) :
    Continuous (fun p : unitInterval × puncturedNeighborhood f => neighborhoodRadial f p.1 p.2) := by
  apply (puncturedQuotient_isQuotientMap f).continuous_lift_prod_right
  simpa only [neighborhoodRadial_puncturedQuotient] using puncturedQuotient_radial_continuous f

@[simp] lemma neighborhoodRadial_zero (f : ∀ i : ι, C(Sphere (d i), X))
    (y : puncturedNeighborhood f) : neighborhoodRadial f 0 y = y := by
  obtain ⟨a,rfl⟩ := (puncturedQuotient_isQuotientMap f).surjective y
  rw [neighborhoodRadial_puncturedQuotient]
  congr 1
  cases a with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i,z⟩
    change (Sum.inr ⟨i, radialDeformation 0 z⟩ : PuncturedRaw X d) = Sum.inr ⟨i,z⟩
    rw [radialDeformation_zero]

lemma neighborhoodRadial_one (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X)
    (y : puncturedNeighborhood f) :
    neighborhoodRadial f 1 y = neighborhoodInclusion f (neighborhoodRetraction f x₀ y) := by
  obtain ⟨a,rfl⟩ := (puncturedQuotient_isQuotientMap f).surjective y
  apply Subtype.ext
  cases a with
  | inl x => rfl
  | inr z =>
    rcases z with ⟨i,z⟩
    change quotientRadial f 1 (puncturedQuotient f (.inr ⟨i,z⟩)) =
      inclusion f (quotientRetraction f x₀ (puncturedQuotient f (.inr ⟨i,z⟩)))
    rw [quotientRadial_puncturedQuotient]
    change characteristic f i (radialDeformation 1 z).1 =
      inclusion f (quotientRetraction f x₀ (puncturedQuotient f (.inr ⟨i,z⟩)))
    rw [quotientRetraction_puncturedQuotient]
    have h : (radialDeformation 1 z).1 = boundaryInclusion (polar z) :=
      Subtype.ext (radialDeformation_one_coordinate z)
    rw [h, characteristic_boundary]
    rfl

/-- A proved deformation homotopy from the neighborhood identity to inclusion∘retraction. -/
def neighborhoodDeformation (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X) :
    ContinuousMap.Homotopy (ContinuousMap.id (puncturedNeighborhood f))
      ((neighborhoodInclusion f).comp (neighborhoodRetraction f x₀)) where
  toFun p := neighborhoodRadial f p.1 p.2
  continuous_toFun := neighborhoodRadial_continuous f
  map_zero_left := neighborhoodRadial_zero f
  map_one_left := neighborhoodRadial_one f x₀

/-- The original space is genuinely homotopy equivalent to the punctured neighborhood. -/
def neighborhoodHomotopyEquiv (f : ∀ i : ι, C(Sphere (d i), X)) (x₀ : X) :
    ContinuousMap.HomotopyEquiv X (puncturedNeighborhood f) where
  toFun := neighborhoodInclusion f
  invFun := neighborhoodRetraction f x₀
  left_inv := by
    have h : (neighborhoodRetraction f x₀).comp (neighborhoodInclusion f) =
        ContinuousMap.id X := by ext x; rfl
    rw [h]
  right_inv := ⟨(neighborhoodDeformation f x₀).symm⟩

end HigherCellAttachment
