module

public import Mathlib.LinearAlgebra.DirectSum.TensorProduct
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksFrontier.RingTheory.GradedTowerLimit.Pieces

/-!
# Base change of a graded inverse limit

For an admissible tower of graded algebras, the graded inverse limit `B = ⨁_d lim (Aₙ)_d` over
`R = lim Rₙ` has finite projective homogeneous parts, its degree-zero part is `R`, and its base
change to every `Rₙ` is `Aₙ`: the map `Rₙ ⊗_R B → Aₙ`, `r ⊗ b ↦ r · prₙ(b)`, is an isomorphism of
graded `Rₙ`-algebras. These are the properties of the algebra `B` constructed in the proof of
Stacks Tag 0D4T.

## Main definitions

* `Stacks.GradedTowerLimit.GradedTower.baseChangeLim`: the comparison `Rₙ ⊗_R B → Aₙ`.

## Main results

* `Stacks.GradedTowerLimit.GradedTower.finite_limGrading`,
  `Stacks.GradedTowerLimit.GradedTower.projective_limGrading`: the homogeneous parts are finite
  projective.
* `Stacks.GradedTowerLimit.GradedTower.bijective_algebraMap_limGrading_zero`: the degree-zero
  part is the limit ring.
* `Stacks.GradedTowerLimit.GradedTower.bijective_baseChangeLim`: the base change of the limit to
  `Rₙ` is `Aₙ`.
* `Stacks.GradedTowerLimit.GradedTower.baseChangeLim_mem`: the comparison preserves degrees.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped TensorProduct DirectSum

universe u

namespace Stacks.GradedTowerLimit

namespace GradedTower

variable {Rg : ℕᵒᵖ ⥤ CommRingCat.{u}} (T : GradedTower Rg)

/-- **The base-change comparison** `Rₙ ⊗_{lim R} B → Aₙ` of the graded inverse limit `B`,
`r ⊗ b ↦ r · prₙ(b)`. -/
def baseChangeLim (n : ℕ) :
    Rg.obj (op n) ⊗[(limit Rg : CommRingCat.{u})] T.Lim →ₐ[Rg.obj (op n)] T.A n :=
  Algebra.TensorProduct.lift (Algebra.ofId _ _) (T.projAlgHom n) fun _ _ => Commute.all _ _

/-- The base-change comparison sends `r ⊗ b` to `r · prₙ(b)`. -/
@[simp]
theorem baseChangeLim_tmul (n : ℕ) (r : Rg.obj (op n)) (b : T.Lim) :
    T.baseChangeLim n (r ⊗ₜ b) = algebraMap (Rg.obj (op n)) (T.A n) r * T.proj n b :=
  Algebra.TensorProduct.lift_tmul _ _ _ _ _

/-- **The base-change comparison preserves degrees**: it carries the base change of the
degree-`d` part of the limit into `(Aₙ)_d`. -/
theorem baseChangeLim_mem (n d : ℕ)
    {x : Rg.obj (op n) ⊗[(limit Rg : CommRingCat.{u})] T.Lim}
    (hx : x ∈ (T.limGrading d).baseChange (Rg.obj (op n))) :
    T.baseChangeLim n x ∈ T.𝒜 n d := by
  rw [Submodule.baseChange_eq_span] at hx
  induction hx using Submodule.span_induction with
  | mem x h =>
    obtain ⟨y, hy, rfl⟩ := h
    rw [TensorProduct.mk_apply, baseChangeLim_tmul, map_one, one_mul]
    exact T.proj_mem n hy
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

variable {T}

/-- **The homogeneous parts of the graded inverse limit are finite** over the limit ring. -/
theorem finite_limGrading (hT : T.IsAdmissible) (d : ℕ) :
    Module.Finite (limit Rg : CommRingCat.{u}) (T.limGrading d) :=
  have := (finite_projective_baseChange_piece hT d).1
  Module.Finite.equiv (T.limGradingEquiv d)

/-- **The homogeneous parts of the graded inverse limit are projective** over the limit ring. -/
theorem projective_limGrading (hT : T.IsAdmissible) (d : ℕ) :
    Module.Projective (limit Rg : CommRingCat.{u}) (T.limGrading d) :=
  have := (finite_projective_baseChange_piece hT d).2.1
  Module.Projective.of_equiv (T.limGradingEquiv d)

/-- **The degree-zero part of the graded inverse limit is the limit ring.** -/
theorem bijective_algebraMap_limGrading_zero (hT : T.IsAdmissible) :
    Function.Bijective fun r : (limit Rg : CommRingCat.{u}) =>
      (⟨algebraMap (limit Rg : CommRingCat.{u}) T.Lim r,
        SetLike.algebraMap_mem_graded T.limGrading r⟩ : T.limGrading 0) := by
  refine ⟨fun r s h => ?_, fun z => ?_⟩
  · refine Concrete.limit_ext Rg r s fun i => ?_
    obtain ⟨n⟩ := i
    have h' := congrArg (fun z : T.limGrading 0 => T.proj n (z : T.Lim)) h
    simp only [proj_algebraMap] at h'
    exact (hT.zero_bijective n).1 (Subtype.ext h')
  · obtain ⟨y, hy⟩ := z.2
    have hs : ∀ n, ∃ s : Rg.obj (op n),
        algebraMap (Rg.obj (op n)) (T.A n) s = (y : ∀ n, T.A n) n := fun n => by
      obtain ⟨s, hs⟩ := (hT.zero_bijective n).2 ⟨(y : ∀ n, T.A n) n, (T.mem_piece.1 y.2 n).1⟩
      exact ⟨s, congrArg Subtype.val hs⟩
    choose s hs using hs
    have hcompat : ∀ n, (tr Rg n).hom (s (n + 1)) = s n := fun n => by
      refine (hT.zero_bijective n).1 (Subtype.ext ?_)
      change algebraMap _ (T.A n) ((tr Rg n).hom (s (n + 1))) = algebraMap _ (T.A n) (s n)
      rw [← T.ρ_algebraMap, hs, hs]
      exact (T.mem_piece.1 y.2 n).2
    obtain ⟨r, hr⟩ := exists_limit_eq Rg s hcompat
    refine ⟨r, Subtype.ext ?_⟩
    rw [← hy]
    change algebraMap (limit Rg : CommRingCat.{u}) T.Lim r = DirectSum.lof _ ℕ _ 0 y
    rw [DirectSum.algebraMap_apply, DirectSum.lof_eq_of]
    congr 1
    ext n
    change algebraMap (limit Rg : CommRingCat.{u}) (T.A n) r = _
    rw [limitAlgebraA_algebraMap, hr, hs]

/-- **The base change of the graded inverse limit to `Rₙ` is `Aₙ`.** -/
theorem bijective_baseChangeLim (hT : T.IsAdmissible) (n : ℕ) :
    Function.Bijective (T.baseChangeLim n) := by
  choose e he using fun d => (finite_projective_baseChange_piece hT d).2.2 n
  let Φ : Rg.obj (op n) ⊗[(limit Rg : CommRingCat.{u})] T.Lim ≃ₗ[Rg.obj (op n)] T.A n :=
    TensorProduct.directSumRight (limit Rg : CommRingCat.{u}) (Rg.obj (op n)) (Rg.obj (op n))
        (fun d => T.piece d) ≪≫ₗ
      DFinsupp.mapRange.linearEquiv e ≪≫ₗ (DirectSum.decomposeLinearEquiv (T.𝒜 n)).symm
  suffices h : ∀ x, T.baseChangeLim n x = Φ x by
    have : ⇑(T.baseChangeLim n) = ⇑Φ := funext h
    rw [this]
    exact Φ.bijective
  intro x
  induction x using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => rw [map_add, map_add, hx, hy]
  | tmul a b =>
    induction b using DirectSum.induction_on with
    | zero => simp
    | add b c hb hc => rw [TensorProduct.tmul_add, map_add, map_add, hb, hc]
    | of d y =>
      rw [baseChangeLim_tmul, proj_of]
      simp only [Φ, LinearEquiv.trans_apply]
      rw [← DirectSum.lof_eq_of (limit Rg : CommRingCat.{u}),
        TensorProduct.directSumRight_tmul_lof]
      symm
      change (DirectSum.decomposeLinearEquiv (T.𝒜 n)).symm (DirectSum.lmap
        (fun d => (e d).toLinearMap) (DirectSum.lof (Rg.obj (op n)) ℕ
          (fun d => Rg.obj (op n) ⊗[(limit Rg : CommRingCat.{u})] T.piece d) d (a ⊗ₜ y))) = _
      rw [DirectSum.lmap_lof, DirectSum.decomposeLinearEquiv_symm_apply, DirectSum.lof_eq_of,
        DirectSum.decompose_symm_of, LinearEquiv.coe_coe, he d a y, Submodule.coe_smul,
        coe_pieceProj, Algebra.smul_def]

end GradedTower

end Stacks.GradedTowerLimit
