module

public import HigherCellAttachment.NormalForm
public import HigherCellAttachment.Sphere
public import Mathlib.Analysis.Convex.Contractible
public import Mathlib.AlgebraicTopology.FundamentalGroupoid.InducedMaps
public import Mathlib.Analysis.Normed.Module.Convex

@[expose] public section


/-! # Genuine open-disk and punctured-open-disk geometry

The punctured open disk retracts to the sphere at radius `1/2`, which lies inside
its domain. Normalizing to the radius-one boundary alone would not give a
self-map of the open disk.
-/

noncomputable section
open scoped unitInterval ContinuousMap
namespace HigherCellAttachment
variable {n : ℕ}

/-- The annular intersection model is the genuine punctured open unit disk. -/
abbrev Annulus (n : ℕ) := {z : (OpenDisk n) // (z : Euclid n) ≠ 0}

/-- The actual Euclidean coordinate on the punctured open disk. -/
def annulusCoordinate : C((Annulus n), Euclid n) :=
  ⟨fun z => z.1.1, continuous_subtype_val.comp continuous_subtype_val⟩

lemma annulus_norm_pos (z : (Annulus n)) : 0 < ‖annulusCoordinate z‖ :=
  norm_pos_iff.mpr z.property

lemma annulus_norm_lt_one (z : (Annulus n)) : ‖annulusCoordinate z‖ < 1 :=
  z.1.property

/-- Polar normalization into the actual Euclidean unit sphere. -/
def annulusPolar : C((Annulus n), (Sphere n)) where
  toFun z := ⟨(‖annulusCoordinate z‖⁻¹ : ℝ) • annulusCoordinate z, by
    apply mem_sphere_zero_iff_norm.mpr
    rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_norm, inv_mul_cancel₀]
    exact ne_of_gt (annulus_norm_pos z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    exact ((annulusCoordinate.continuous.norm.inv₀
      (fun z => ne_of_gt (annulus_norm_pos z))).smul annulusCoordinate.continuous)

/-- The radius-half sphere lies inside the punctured open disk. -/
def halfSphere : C((Sphere n), (Annulus n)) where
  toFun z := ⟨⟨(1 / 2 : ℝ) • (z : Euclid n), by
    rw [norm_smul, Real.norm_eq_abs, Sphere.norm_coe]
    norm_num⟩, smul_ne_zero (by norm_num) (Sphere.coe_ne_zero z)⟩
  continuous_toFun := by
    apply Continuous.subtype_mk
    apply Continuous.subtype_mk
    exact (continuous_const : Continuous fun _ : (Sphere n) => (1 / 2 : ℝ)).smul
      (continuous_subtype_val : Continuous fun z : (Sphere n) => (z : Euclid n))

@[simp] lemma annulusCoordinate_halfSphere (z : (Sphere n)) :
    annulusCoordinate (halfSphere z) = (1 / 2 : ℝ) • (z : Euclid n) := rfl

@[simp] lemma annulus_norm_halfSphere (z : (Sphere n)) :
    ‖annulusCoordinate (halfSphere z)‖ = (1 / 2 : ℝ) := by
  rw [annulusCoordinate_halfSphere, norm_smul, Real.norm_eq_abs, Sphere.norm_coe]
  norm_num

@[simp] lemma annulusPolar_halfSphere (z : (Sphere n)) : annulusPolar (halfSphere z) = z := by
  apply Subtype.ext
  change ‖annulusCoordinate (halfSphere z)‖⁻¹ • ((1 / 2 : ℝ) • (z : Euclid n)) = _
  rw [annulus_norm_halfSphere, smul_smul]
  norm_num

/-- The coefficient interpolating the original radius and radius one half. -/
def annulusRadialCoefficient (t : unitInterval) (z : (Annulus n)) : ℝ :=
  (1 - (t : ℝ)) + (t : ℝ) * (1 / 2) * ‖annulusCoordinate z‖⁻¹

lemma annulusRadialCoefficient_mul_norm (t : unitInterval) (z : (Annulus n)) :
    annulusRadialCoefficient t z * ‖annulusCoordinate z‖ =
      (1 - (t : ℝ)) * ‖annulusCoordinate z‖ + (t : ℝ) * (1 / 2) := by
  unfold annulusRadialCoefficient
  rw [add_mul, mul_assoc, inv_mul_cancel₀ (ne_of_gt (annulus_norm_pos z)), mul_one]

lemma annulusRadialCoefficient_pos (t : unitInterval) (z : (Annulus n)) :
    0 < annulusRadialCoefficient t z := by
  have hi : 0 < ‖annulusCoordinate z‖⁻¹ := inv_pos.mpr (annulus_norm_pos z)
  have ht0 := t.property.1
  have ht1 := t.property.2
  unfold annulusRadialCoefficient
  by_cases h : (t : ℝ) = 1
  · rw [h]
    positivity
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne ht1 h
    have hnonneg : 0 ≤ (t : ℝ) * (1 / 2) * ‖annulusCoordinate z‖⁻¹ := by positivity
    linarith

lemma annulusRadialCoefficient_mul_norm_lt_one (t : unitInterval) (z : (Annulus n)) :
    annulusRadialCoefficient t z * ‖annulusCoordinate z‖ < 1 := by
  rw [annulusRadialCoefficient_mul_norm]
  have ht0 := t.property.1
  have ht1 := t.property.2
  by_cases h : (t : ℝ) = 1
  · rw [h]
    norm_num
  · have hlt : (t : ℝ) < 1 := lt_of_le_of_ne ht1 h
    have hm := mul_lt_mul_of_pos_left (annulus_norm_lt_one z) (by linarith : 0 < 1 - (t : ℝ))
    nlinarith

/-- Explicit radial deformation within the actual punctured open disk. -/
def annulusRadialDeformation (t : unitInterval) (z : (Annulus n)) : Annulus n :=
  ⟨⟨annulusRadialCoefficient t z • annulusCoordinate z, by
      rw [norm_smul, Real.norm_eq_abs, abs_of_pos (annulusRadialCoefficient_pos t z)]
      exact annulusRadialCoefficient_mul_norm_lt_one t z⟩,
    smul_ne_zero (ne_of_gt (annulusRadialCoefficient_pos t z)) z.property⟩

lemma annulusRadialDeformation_continuous :
    Continuous (fun p : unitInterval × (Annulus n) => annulusRadialDeformation p.1 p.2) := by
  apply Continuous.subtype_mk
  apply Continuous.subtype_mk
  change Continuous ((fun p : unitInterval × (Annulus n) => annulusRadialCoefficient p.1 p.2) •
    (fun p : unitInterval × (Annulus n) => annulusCoordinate p.2))
  apply Continuous.smul
  · exact (continuous_const.sub (continuous_subtype_val.comp continuous_fst)).add
      (((continuous_subtype_val.comp continuous_fst).mul continuous_const).mul
        ((annulusCoordinate.continuous.comp continuous_snd).norm.inv₀
          (fun p => ne_of_gt (annulus_norm_pos p.2))))
  · exact annulusCoordinate.continuous.comp continuous_snd

@[simp] lemma annulusRadialDeformation_zero (z : (Annulus n)) :
    annulusRadialDeformation 0 z = z := by
  apply Subtype.ext
  apply Subtype.ext
  simp [annulusRadialDeformation, annulusRadialCoefficient, annulusCoordinate]

@[simp] lemma annulusRadialDeformation_one (z : (Annulus n)) :
    annulusRadialDeformation 1 z = halfSphere (annulusPolar z) := by
  apply Subtype.ext
  apply Subtype.ext
  change annulusRadialCoefficient 1 z • annulusCoordinate z =
    (1 / 2 : ℝ) • (‖annulusCoordinate z‖⁻¹ • annulusCoordinate z)
  simp [annulusRadialCoefficient, smul_smul]

/-- The radius-half sphere is fixed throughout the deformation. -/
lemma annulusRadialDeformation_halfSphere (t : unitInterval) (z : (Sphere n)) :
    annulusRadialDeformation t (halfSphere z) = halfSphere z := by
  apply Subtype.ext
  apply Subtype.ext
  change annulusRadialCoefficient t (halfSphere z) • annulusCoordinate (halfSphere z) =
    annulusCoordinate (halfSphere z)
  have hc : annulusRadialCoefficient t (halfSphere z) = 1 := by
    unfold annulusRadialCoefficient
    rw [annulus_norm_halfSphere]
    ring
  rw [hc, one_smul]

/-- The explicit homotopy from the identity to the half-radius polar projection. -/
def annulusRadialHomotopy :
    (ContinuousMap.id (Annulus n)).Homotopy (halfSphere.comp annulusPolar) where
  toFun p := annulusRadialDeformation p.1 p.2
  continuous_toFun := annulusRadialDeformation_continuous
  map_zero_left := annulusRadialDeformation_zero
  map_one_left := annulusRadialDeformation_one

/-- Polar projection and the half-radius embedding give a genuine homotopy equivalence. -/
def annulusHomotopyEquivSphere : (Annulus n) ≃ₕ (Sphere n) where
  toFun := annulusPolar
  invFun := halfSphere
  left_inv := ⟨annulusRadialHomotopy.symm⟩
  right_inv := by
    have h : annulusPolar.comp halfSphere = ContinuousMap.id (Sphere n) := by
      apply ContinuousMap.ext
      exact annulusPolar_halfSphere
    rw [h]

/-- Path-connectedness transfers along the explicit homotopy equivalence. -/
theorem homotopyEquivPathConnectedSpace {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] [PathConnectedSpace Y] (e : X ≃ₕ Y) :
    PathConnectedSpace X where
  nonempty := ⟨e.invFun (Classical.arbitrary Y)⟩
  joined x y := ⟨((e.left_inv.some.evalAt x).symm.trans
    ((PathConnectedSpace.somePath (e x) (e y)).map e.invFun.continuous)).trans
      (e.left_inv.some.evalAt y)⟩

/-- A homotopy equivalence induces the actual map on based fundamental groups
as a multiplicative equivalence. Its forward map is not an abstract choice. -/
def homotopyEquivFundamentalGroup {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]
    (e : X ≃ₕ Y) (x : X) : FundamentalGroup X x ≃* FundamentalGroup Y (e x) :=
  (FundamentalGroupoidFunctor.equivOfHomotopyEquiv e).fullyFaithfulFunctor.mulEquivEnd
    (FundamentalGroupoid.mk x)

@[simp] lemma homotopyEquivFundamentalGroup_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) (x : X)
    (γ : FundamentalGroup X x) :
    homotopyEquivFundamentalGroup e x γ = FundamentalGroup.map e.toFun x γ := rfl

/-- The based version with the target basepoint explicitly identified. -/
def homotopyEquivFundamentalGroupOfEq {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) {x : X} {y : Y} (h : e x = y) :
    FundamentalGroup X x ≃* FundamentalGroup Y y :=
  (homotopyEquivFundamentalGroup e x).trans
    (CategoryTheory.eqToIso (congrArg FundamentalGroupoid.mk h)).conj

@[simp] lemma homotopyEquivFundamentalGroupOfEq_apply {X Y : Type*}
    [TopologicalSpace X] [TopologicalSpace Y] (e : X ≃ₕ Y) {x : X} {y : Y} (h : e x = y)
    (γ : FundamentalGroup X x) :
    homotopyEquivFundamentalGroupOfEq e h γ = FundamentalGroup.mapOfEq e.toFun h γ := rfl

/-- The coordinate-defined open disk is exactly the ordinary convex metric ball. -/
lemma openDisk_eq_ball : {z : Euclid n | ‖z‖ < 1} = Metric.ball (0 : Euclid n) 1 := by
  ext z
  simp [Metric.mem_ball, dist_zero_right]

/-- Contractibility comes from actual convex ball geometry. -/
instance openDisk_contractibleSpace : ContractibleSpace (OpenDisk n) := by
  have hc : Convex ℝ {z : Euclid n | ‖z‖ < 1} := by
    rw [openDisk_eq_ball]
    exact convex_ball (0 : Euclid n) 1
  exact hc.contractibleSpace ⟨0, by simp⟩

/-- In particular the genuine open disk is simply connected. -/
instance openDisk_simplyConnectedSpace : SimplyConnectedSpace (OpenDisk n) := inferInstance

end HigherCellAttachment
