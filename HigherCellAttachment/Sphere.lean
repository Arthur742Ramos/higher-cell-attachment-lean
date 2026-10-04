module

public import HigherCellAttachment.Adjunction
public import SphereInfrastructure.SimplyConnectedSphere

/-!
# Simply connected higher-cell boundaries

`Sphere n` is the unit sphere in an `n`-dimensional ambient Euclidean space.
For `3 ≤ n` it is simply connected. The sphere theorem used below is the
vendored theorem of Sebastian Kumar from mathlib PR #28246; this file only
adapts its dimension convention and exposes the consequences for attachment.
-/

@[expose] public section

noncomputable section

namespace HigherCellAttachment

namespace Sphere

/-- A cell of dimension at least three has a simply connected boundary. -/
theorem simplyConnectedSpace {n : ℕ} (h : 3 ≤ n) : SimplyConnectedSpace (Sphere n) := by
  have hn : n = (n - 3) + 2 + 1 := by omega
  rw [hn]
  exact EuclideanSphere.simplyConnectedSpace (n - 3)

/-- Higher-cell boundaries are path connected. -/
theorem pathConnectedSpace {n : ℕ} (h : 3 ≤ n) : PathConnectedSpace (Sphere n) := by
  letI : SimplyConnectedSpace (Sphere n) := simplyConnectedSpace h
  infer_instance

/-- Higher-cell boundaries are nonempty, with no extra nonemptiness hypothesis. -/
theorem nonempty {n : ℕ} (h : 3 ≤ n) : Nonempty (Sphere n) := by
  letI : PathConnectedSpace (Sphere n) := pathConnectedSpace h
  infer_instance

instance instSimplyConnectedSpace (n : ℕ) [Fact (3 ≤ n)] :
    SimplyConnectedSpace (Sphere n) := simplyConnectedSpace Fact.out

instance instPathConnectedSpace (n : ℕ) [Fact (3 ≤ n)] :
    PathConnectedSpace (Sphere n) := pathConnectedSpace Fact.out

instance instNonempty (n : ℕ) [Fact (3 ≤ n)] : Nonempty (Sphere n) := nonempty Fact.out

/-- A boundary basepoint whose existence follows from the dimension bound. -/
def basepoint (n : ℕ) [Fact (3 ≤ n)] : Sphere n := Classical.arbitrary _

/-- The fundamental group of a higher-cell boundary is trivial at every basepoint. -/
theorem fundamentalGroup_subsingleton {n : ℕ} (h : 3 ≤ n) (b : Sphere n) :
    Subsingleton (FundamentalGroup (Sphere n) b) := by
  letI : SimplyConnectedSpace (Sphere n) := simplyConnectedSpace h
  infer_instance

/-- Every boundary loop class equals the identity, regardless of basepoint. -/
theorem fundamentalGroup_eq_one {n : ℕ} (h : 3 ≤ n) (b : Sphere n)
    (g : FundamentalGroup (Sphere n) b) : g = 1 := by
  letI := fundamentalGroup_subsingleton h b
  exact Subsingleton.elim _ _

/-- Every higher-cell boundary loop is nullhomotopic. -/
theorem loops_nullhomotopic {n : ℕ} (h : 3 ≤ n) (b : Sphere n) (p : Path b b) :
    p.Homotopic (Path.refl b) := by
  letI : SimplyConnectedSpace (Sphere n) := simplyConnectedSpace h
  exact SimplyConnectedSpace.paths_homotopic _ _

end Sphere

end HigherCellAttachment
