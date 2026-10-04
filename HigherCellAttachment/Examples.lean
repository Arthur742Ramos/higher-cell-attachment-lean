module
public import HigherCellAttachment.Main
@[expose] public section
noncomputable section
namespace HigherCellAttachment
universe u v
variable {X : Type u} [TopologicalSpace X] [PathConnectedSpace X]

/-- Empty families are covered directly by the full quotient theorem. -/
theorem empty_family (x₀ : X) :
    Function.Bijective (inclusionPi1 (d := fun i : Empty => nomatch i)
      (fun i : Empty => nomatch i) x₀) :=
  inclusionPi1_bijective (fun i : Empty => nomatch i) _ x₀

/-- Uniform-dimension families recover the fixed-dimensional source statement. -/
theorem fixed_dimension {ι : Type v} (n : ℕ) (hn : 3 ≤ n)
    (f : ι → C(Sphere n, X)) (x₀ : X) :
    Function.Bijective (inclusionPi1 (d := fun _ : ι => n) f x₀) :=
  inclusionPi1_bijective (fun _ => hn) f x₀

/-- The theorem also allows dimensions three and five in one attachment. -/
theorem mixed_dimensions (f : ∀ b : Bool, C(Sphere (if b then 3 else 5), X)) (x₀ : X) :
    Function.Bijective (inclusionPi1 (d := fun b : Bool => if b then 3 else 5) f x₀) := by
  apply inclusionPi1_bijective
  intro b
  cases b <;> norm_num

#check higher_cell_attachment.{u,v}
#check higher_cell_attachment.{1,2}
#check higher_cell_attachment.{2,1}
end HigherCellAttachment
