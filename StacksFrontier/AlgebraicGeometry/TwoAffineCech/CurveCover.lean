module

public import StacksFrontier.AlgebraicGeometry.TwoAffineCech.Family
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ProjectiveCompletion
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.CommonAffineOpenOfDimensionOnePointsFiniteComponents
public import StacksFrontier.AlgebraicGeometry.CurveAffineOrHProjective.Basic

/-!
# A Noetherian separated scheme of dimension at most one is covered by two affine opens

Let `X` be a separated Noetherian scheme of dimension at most one. The generic points of its
finitely many irreducible components lie in a common affine open `U` ([Stacks, Tag 09NN]); the
complement of `U` is then a finite set of closed points, which lies in another affine open `V`,
again by [Stacks, Tag 09NN]. So `X = U ∪ V`.

## Main results

* `Stacks.TwoAffineCech.exists_cover_isAffineOpen`: a covering indexed by
  `Stacks.TwoAffineCech.Cover` by affine opens.
-/

@[expose] public section

open CategoryTheory TopologicalSpace AlgebraicGeometry

universe u

namespace Stacks.TwoAffineCech

variable (X : Scheme.{u}) [X.IsSeparated] [IsNoetherian X]

/-- **Two affine opens cover a separated Noetherian scheme of dimension at most one.** -/
theorem exists_isAffineOpen_sup_eq_top (hdim : topologicalKrullDim X ≤ 1) :
    ∃ U V : X.Opens, IsAffineOpen U ∧ IsAffineOpen V ∧ U ⊔ V = ⊤ := by
  have hcomp : ∀ W : X.Opens, IsCompact (W : Set X) → (irreducibleComponents W).Finite :=
    fun W _ =>
      have : NoetherianSpace W := NoetherianSpace.set (W : Set X)
      NoetherianSpace.finite_irreducibleComponents
  have hfinite : ∀ S : Set X, S.Finite → ∃ U : X.Opens, IsAffineOpen U ∧ S ⊆ U := fun S hS =>
    have := hS.to_subtype
    exists_isAffineOpen_containing_of_stalk_krullDimLE_one_of_finite_components X hcomp
      (fun x : S => (x : X)) (fun _ => inferInstance)
      (fun x => krullDimLE_one_stalk_of_topologicalKrullDim_le_one X hdim x) |>.imp
        fun _ h => ⟨h.1, fun x hx => h.2 ⟨x, hx⟩⟩
  obtain ⟨U, hU, hgU⟩ :=
    hfinite _ (genericPoints.finite NoetherianSpace.finite_irreducibleComponents)
  obtain ⟨hfin, -⟩ := Stacks.CurveProjectiveCompletion.finite_compl_of_genericPoints_subset
    U.isOpen hdim hgU
  obtain ⟨V, hV, hcV⟩ := hfinite _ hfin
  refine ⟨U, V, hU, hV, ?_⟩
  rw [eq_top_iff]
  intro x _
  by_cases hx : x ∈ U
  · exact Or.inl hx
  · exact Or.inr (hcV hx)

/-- **A covering indexed by `Stacks.TwoAffineCech.Cover` by two affine opens.** -/
theorem exists_cover_isAffineOpen (hdim : topologicalKrullDim X ≤ 1) :
    ∃ U : Cover.{u} → X.Opens, (⊤ : X.Opens) = ⨆ i, U i ∧ ∀ i, IsAffineOpen (U i) := by
  obtain ⟨U, V, hU, hV, hUV⟩ := exists_isAffineOpen_sup_eq_top X hdim
  refine ⟨fun i => if i.down = 0 then U else V, ?_, fun i => ?_⟩
  · rw [eq_comm, eq_top_iff, ← hUV]
    refine sup_le ?_ ?_
    · exact le_iSup_of_le ⟨0⟩ (by simp)
    · exact le_iSup_of_le ⟨1⟩ (by simp)
  · by_cases h : i.down = 0 <;> simp [h, hU, hV]

end Stacks.TwoAffineCech
