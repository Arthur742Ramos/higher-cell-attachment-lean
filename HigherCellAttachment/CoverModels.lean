module

public import HigherCellAttachment.Annulus
public import HigherCellAttachment.Embeddings
public import HigherCellAttachment.CoverPushout
public import HigherCellAttachment.Retraction
public import HigherCellAttachment.Sphere
public import Mathlib.Topology.LocallyConstant.Basic

@[expose] public section


/-! # Coordinate models of the genuine cover and its overlap

The interior open set is the actual coproduct of open disks; its intersection
with the punctured neighborhood is the actual coproduct of punctured open
disks. Component indices are locally constant and hence cannot change along
any path or fundamental-groupoid arrow.
-/

noncomputable section
set_option backward.isDefEq.respectTransparency false
open scoped ContinuousMap
namespace HigherCellAttachment
attribute [local instance] Classical.propDecidable
universe u v
variable {X : Type u} [TopologicalSpace X] {ι : Type v} {d : ι → ℕ}

theorem overlap_isOpen (f : ∀ i : ι, C(Sphere (d i), X)) : IsOpen (overlap f) :=
  (puncturedNeighborhood_isOpen f).inter (interiors_isOpen f)

/-- Forget puncturing while retaining the actual open-disk point. -/
def annulusInclusion {n : ℕ} : C(Annulus n, OpenDisk n) := ⟨Subtype.val, continuous_subtype_val⟩

/-- The coproduct of punctured-disk inclusions. -/
def sigmaAnnulusInclusion : C((Σ i : ι, Annulus (d i)), (Σ i : ι, OpenDisk (d i))) :=
  ⟨Sigma.map id (fun _ => annulusInclusion), Continuous.sigma_map
    (fun _ => annulusInclusion.continuous)⟩

lemma sigmaAnnulusInclusion_isEmbedding :
    Topology.IsEmbedding (sigmaAnnulusInclusion (d := d)) := by
  change Topology.IsEmbedding (Sigma.map (β₁ := fun i : ι => Annulus (d i)) (β₂ := fun i : ι => OpenDisk (d i))
    (id : ι → ι) (fun i => (Subtype.val : Annulus (d i) → OpenDisk (d i))))
  exact (Topology.isEmbedding_sigmaMap Function.injective_id).mpr
    (fun _ => Topology.IsEmbedding.subtypeVal)

/-- Coordinates of punctured interior points in the actual quotient space. -/
def annulusInteriorMap (f : ∀ i : ι, C(Sphere (d i), X)) : C((Σ i : ι, Annulus (d i)), Space f) :=
  (interiorMap f).comp sigmaAnnulusInclusion

@[simp] lemma annulusInteriorMap_apply (f : ∀ i : ι, C(Sphere (d i), X))
    (z : Σ i : ι, Annulus (d i)) : annulusInteriorMap f z = interiorMap f ⟨z.1, z.2.1⟩ := rfl

lemma annulusInteriorMap_isEmbedding (f : ∀ i : ι, C(Sphere (d i), X)) :
    Topology.IsEmbedding (annulusInteriorMap f) :=
  (interiorMap_isOpenEmbedding f).isEmbedding.comp sigmaAnnulusInclusion_isEmbedding

/-- An interior coordinate belongs to the punctured neighborhood exactly when it is nonzero. -/
@[simp] lemma interiorMap_mem_puncturedNeighborhood_iff (f : ∀ i : ι, C(Sphere (d i), X))
    (i : ι) (z : OpenDisk (d i)) :
    interiorMap f ⟨i, z⟩ ∈ puncturedNeighborhood f ↔ (z : Euclid (d i)) ≠ 0 := by
  change quotientMap f (.inr ⟨i, ⟨z, z.property.le⟩⟩) ∉ centers f ↔ _
  simp only [quotient_inr_mem_centers]

/-- No assumed topology: the image of the actual punctured-disk embedding is the overlap. -/
lemma annulusInteriorMap_range (f : ∀ i : ι, C(Sphere (d i), X)) :
    Set.range (annulusInteriorMap f) = overlap f := by
  ext y
  constructor
  · rintro ⟨⟨i, z⟩, rfl⟩
    exact ⟨(interiorMap_mem_puncturedNeighborhood_iff f i z.1).mpr z.property,
      interiorRepresentative_mem_interiors f i z.1⟩
  · intro hy
    have hy' : y ∈ Set.range (interiorMap f) := by
      rw [interiorMap_range]
      exact hy.2
    obtain ⟨⟨i, z⟩, rfl⟩ := hy'
    have hz : (z : Euclid (d i)) ≠ 0 :=
      (interiorMap_mem_puncturedNeighborhood_iff f i z).mp hy.1
    exact ⟨⟨i, ⟨z, hz⟩⟩, rfl⟩

/-- The overlap, with its genuine induced quotient topology, is the annulus coproduct. -/
def overlapHomeomorph (f : ∀ i : ι, C(Sphere (d i), X)) :
    (Σ i : ι, Annulus (d i)) ≃ₜ overlap f :=
  (annulusInteriorMap_isEmbedding f).toHomeomorph.trans
    (Homeomorph.setCongr (annulusInteriorMap_range f))

@[simp] lemma overlapHomeomorph_apply (f : ∀ i : ι, C(Sphere (d i), X))
    (z : Σ i : ι, Annulus (d i)) : (overlapHomeomorph f z : Space f) = annulusInteriorMap f z := rfl

/-- The actual continuous inclusion of the overlap into the interior open set. -/
def overlapToInteriors (f : ∀ i : ι, C(Sphere (d i), X)) : C(overlap f, interiors f) :=
  ⟨fun z => ⟨z.1, z.property.2⟩, continuous_subtype_val.subtype_mk _⟩

/-- The actual continuous inclusion of the overlap into the punctured neighborhood. -/
def overlapToNeighborhood (f : ∀ i : ι, C(Sphere (d i), X)) : C(overlap f, puncturedNeighborhood f) :=
  ⟨fun z => ⟨z.1, z.property.1⟩, continuous_subtype_val.subtype_mk _⟩

/-- The coordinate square of the overlap inclusion commutes on the nose. -/
lemma overlapToInteriors_coordinates (f : ∀ i : ι, C(Sphere (d i), X))
    (z : Σ i : ι, Annulus (d i)) :
    overlapToInteriors f (overlapHomeomorph f z) =
      interiorsHomeomorph f (sigmaAnnulusInclusion z) := rfl

/-- The index projection from any topological coproduct is locally constant,
without giving the index type any additional structure. -/
lemma sigmaIndex_isLocallyConstant {A : ι → Type*} [∀ i, TopologicalSpace (A i)] :
    IsLocallyConstant (Sigma.fst : (Σ i, A i) → ι) :=
  fun S => isOpen_sigma_fst_preimage S

/-- The cell index of an actual interior point. -/
def interiorIndex (f : ∀ i : ι, C(Sphere (d i), X)) (z : interiors f) : ι :=
  ((interiorsHomeomorph f).symm z).1

/-- The cell index of an actual overlap point. -/
def overlapIndex (f : ∀ i : ι, C(Sphere (d i), X)) (z : overlap f) : ι :=
  ((overlapHomeomorph f).symm z).1

lemma interiorIndex_isLocallyConstant (f : ∀ i : ι, C(Sphere (d i), X)) :
    IsLocallyConstant (interiorIndex f) :=
  sigmaIndex_isLocallyConstant.comp_continuous (interiorsHomeomorph f).symm.continuous

lemma overlapIndex_isLocallyConstant (f : ∀ i : ι, C(Sphere (d i), X)) :
    IsLocallyConstant (overlapIndex f) :=
  sigmaIndex_isLocallyConstant.comp_continuous (overlapHomeomorph f).symm.continuous

@[simp] lemma interiorIndex_coordinates (f : ∀ i : ι, C(Sphere (d i), X))
    (z : Σ i : ι, OpenDisk (d i)) : interiorIndex f (interiorsHomeomorph f z) = z.1 := by
  simp [interiorIndex]

@[simp] lemma overlapIndex_coordinates (f : ∀ i : ι, C(Sphere (d i), X))
    (z : Σ i : ι, Annulus (d i)) : overlapIndex f (overlapHomeomorph f z) = z.1 := by
  simp [overlapIndex]

lemma interiorIndex_overlapToInteriors (f : ∀ i : ι, C(Sphere (d i), X)) (z : overlap f) :
    interiorIndex f (overlapToInteriors f z) = overlapIndex f z := by
  obtain ⟨z, rfl⟩ := (overlapHomeomorph f).surjective z
  rw [overlapToInteriors_coordinates, interiorIndex_coordinates, overlapIndex_coordinates]
  rfl

/-- A locally constant index cannot change anywhere along a continuous path. -/
lemma index_constant_along_path {A : Type*} [TopologicalSpace A] {j : A → ι}
    (hj : IsLocallyConstant j) {a b : A} (p : Path a b) (t : unitInterval) : j (p t) = j a := by
  have h := (hj.comp_continuous p.continuous).apply_eq_of_preconnectedSpace t 0
  simpa only [Function.comp_apply, p.source] using h

lemma interiorIndex_path (f : ∀ i : ι, C(Sphere (d i), X)) {a b : interiors f}
    (p : Path a b) (t : unitInterval) : interiorIndex f (p t) = interiorIndex f a :=
  index_constant_along_path (interiorIndex_isLocallyConstant f) p t

lemma overlapIndex_path (f : ∀ i : ι, C(Sphere (d i), X)) {a b : overlap f}
    (p : Path a b) (t : unitInterval) : overlapIndex f (p t) = overlapIndex f a :=
  index_constant_along_path (overlapIndex_isLocallyConstant f) p t

/-- Every actual interior groupoid arrow lies within a single disk component. -/
lemma interiorIndex_arrow (f : ∀ i : ι, C(Sphere (d i), X)) {a b : interiors f}
    (γ : Path.Homotopic.Quotient a b) : interiorIndex f a = interiorIndex f b := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
  simpa only [p.target] using (interiorIndex_path f p 1).symm

/-- Every actual overlap groupoid arrow lies within a single annulus component. -/
lemma overlapIndex_arrow (f : ∀ i : ι, C(Sphere (d i), X)) {a b : overlap f}
    (γ : Path.Homotopic.Quotient a b) : overlapIndex f a = overlapIndex f b := by
  obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
  simpa only [p.target] using (overlapIndex_path f p 1).symm


/-- Retraction to one chosen coproduct component. Each other component is
sent constantly to the chosen anchor. Continuity uses the coproduct topology. -/
def coproductRetraction {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    (i : ι) (a : A i) : C((Σ j, A j), A i) where
  toFun z := if h : z.1 = i then h ▸ z.2 else a
  continuous_toFun := by
    apply continuous_sigma
    intro j
    by_cases h : j = i
    · subst j
      convert (continuous_id : Continuous (id : A i → A i)) using 1
      funext z
      simp
    · simpa [h] using (continuous_const : Continuous (fun _ : A j => a))

/-- The continuous inclusion of one dependent coproduct component. -/
def coproductComponent {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    (i : ι) : C(A i, (Σ j, A j)) :=
  ⟨Sigma.mk i, continuous_sigmaMk⟩

@[simp] lemma coproductRetraction_component {A : ι → Type*}
    [∀ i, TopologicalSpace (A i)] (i : ι) (a z : A i) :
    coproductRetraction i a (coproductComponent i z) = z := by
  simp [coproductRetraction, coproductComponent]

/-- Every loop stays in its initial coproduct component, including mixed
fiber dimensions. Projecting and reincluding therefore preserves the path. -/
lemma coproduct_path_reconstruction {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    (i : ι) (a : A i) (p : Path (⟨i, a⟩ : Σ j, A j) ⟨i, a⟩) :
    ((p.map (coproductRetraction i a).continuous).cast
      (coproductRetraction_component i a a).symm
      (coproductRetraction_component i a a).symm).map (coproductComponent i).continuous = p := by
  apply Path.ext
  funext t
  change coproductComponent i (coproductRetraction i a (p t)) = p t
  have hi : (p t).1 = i := index_constant_along_path sigmaIndex_isLocallyConstant p t
  rcases hpt : p t with ⟨j,z⟩
  have hji : j = i := by simpa [hpt] using hi
  subst j
  simp [coproductRetraction, coproductComponent, hpt]

/-- A component inclusion induces the actual isomorphism of its based
fundamental group, for an arbitrary dependent family of topological spaces. -/
def coproductFundamentalGroupEquiv {A : ι → Type*} [∀ i, TopologicalSpace (A i)]
    (i : ι) (a : A i) :
    FundamentalGroup (A i) a ≃* FundamentalGroup (Σ j, A j) ⟨i, a⟩ :=
  MulEquiv.ofBijective (FundamentalGroup.map (coproductComponent i) a) (by
    constructor
    · intro γ δ h
      have hr (ε : FundamentalGroup (A i) a) :
          FundamentalGroup.mapOfEq (coproductRetraction i a)
            (coproductRetraction_component i a a)
            (FundamentalGroup.map (coproductComponent i) a ε) = ε := by
        obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective ε
        rw [FundamentalGroup.mapOfEq_apply]
        change (Path.Homotopic.Quotient.mk
          ((p.map (coproductComponent i).continuous).map
            (coproductRetraction i a).continuous)).cast _ _ = _
        rw [← Path.Homotopic.Quotient.mk_cast]
        congr 1
        apply Path.ext
        funext t
        exact coproductRetraction_component i a (p t)
      have hh := congrArg (FundamentalGroup.mapOfEq (coproductRetraction i a)
        (coproductRetraction_component i a a)) h
      exact (hr γ).symm.trans (hh.trans (hr δ))
    · intro γ
      obtain ⟨p, rfl⟩ := Path.Homotopic.Quotient.mk_surjective γ
      refine ⟨FundamentalGroup.mapOfEq (coproductRetraction i a)
        (coproductRetraction_component i a a) (.mk p), ?_⟩
      rw [FundamentalGroup.mapOfEq_apply]
      change Path.Homotopic.Quotient.mk
        (((p.map (coproductRetraction i a).continuous).cast _ _).map
          (coproductComponent i).continuous) = _
      congr 1
      apply Path.ext
      funext t
      exact congrArg (fun q => q t) (coproduct_path_reconstruction i a p))

variable [∀ i, Fact (3 ≤ d i)]

instance annulus_simplyConnectedSpace {n : ℕ} [Fact (3 ≤ n)] :
    SimplyConnectedSpace (Annulus n) := annulusHomotopyEquivSphere.simplyConnectedSpace

/-- The radius-half anchor in the actual overlap of each higher cell. -/
def annulusBasepoint {n : ℕ} [Fact (3 ≤ n)] : Annulus n :=
  halfSphere (Classical.arbitrary (Sphere n))

def overlapAnchor (f : ∀ i : ι, C(Sphere (d i), X)) (i : ι) : overlap f :=
  overlapHomeomorph f ⟨i, annulusBasepoint⟩

/-- Componentwise connecting paths use proved sphere connectivity. -/
def overlapAnchorPaths (f : ∀ i : ι, C(Sphere (d i), X)) (w : overlap f) :
    Path (overlapAnchor f (overlapIndex f w)) w :=
  ((PathConnectedSpace.somePath annulusBasepoint ((overlapHomeomorph f).symm w).2).map
    ((overlapHomeomorph f).continuous.comp (continuous_sigmaMk (i := overlapIndex f w)))).cast
      rfl ((overlapHomeomorph f).apply_symm_apply w).symm

def interiorAnchorPaths (f : ∀ i : ι, C(Sphere (d i), X)) (v : interiors f) :
    Path (overlapRight f (overlapAnchor f (interiorIndex f v))) v :=
  ((PathConnectedSpace.somePath annulusBasepoint.1 ((interiorsHomeomorph f).symm v).2).map
    ((interiorsHomeomorph f).continuous.comp (continuous_sigmaMk (i := interiorIndex f v)))).cast
      rfl ((interiorsHomeomorph f).apply_symm_apply v).symm

/-- Thin vertex groups transfer to arbitrary dependent coproducts. -/
theorem coproductVertexGroup_subsingleton {A : ι → Type*}
    [∀ i, TopologicalSpace (A i)]
    (hA : ∀ i (a : A i), Subsingleton (FundamentalGroup (A i) a))
    (c : Σ j, A j) : Subsingleton (FundamentalGroup (Σ j, A j) c) := by
  rcases c with ⟨i,a⟩
  letI := hA i a
  exact (coproductFundamentalGroupEquiv (A := A) i a).symm.injective.subsingleton

/-- Interior vertex groups are trivial by convex-ball contractibility. -/
theorem interiorVertexGroup_subsingleton (f : ∀ i : ι, C(Sphere (d i), X)) (v : interiors f) :
    Subsingleton (FundamentalGroup (interiors f) v) := by
  let h := interiorsHomeomorph f
  letI := coproductVertexGroup_subsingleton (A := fun i : ι => OpenDisk (d i))
    (fun i a => inferInstance) (h.symm.toHomotopyEquiv.toFun v)
  exact (homotopyEquivFundamentalGroup h.symm.toHomotopyEquiv v).injective.subsingleton

/-- Overlap vertex groups are trivial by the explicit radial equivalence to
the simply connected unit sphere. No thinness assumption is supplied by callers. -/
theorem overlapVertexGroup_subsingleton (f : ∀ i : ι, C(Sphere (d i), X)) (v : overlap f) :
    Subsingleton (FundamentalGroup (overlap f) v) := by
  let h := overlapHomeomorph f
  letI := coproductVertexGroup_subsingleton (A := fun i : ι => Annulus (d i))
    (fun i a => inferInstance) (h.symm.toHomotopyEquiv.toFun v)
  exact (homotopyEquivFundamentalGroup h.symm.toHomotopyEquiv v).injective.subsingleton

end HigherCellAttachment
