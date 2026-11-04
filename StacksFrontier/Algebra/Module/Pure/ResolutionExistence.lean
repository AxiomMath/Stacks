module

public import Mathlib.Algebra.Exact.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.TensorProduct.RightExactness
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Pure.Projective
public import StacksFrontier.Algebra.Module.Pure.ProjectiveResolution

/-!
# Existence of pure projective resolutions

Every module is the target of a universally exact surjection from a pure projective module
(`Module.exists_pureProjective_universallyExact_presentation`).  Splicing such presentations
together along the resulting chain of iterated kernels produces a pure projective resolution
in the sense of `Module.PureProjectiveResolution.IsPureProjectiveResolution`.

## References

* [Stacks Project, Tag 0703](https://stacks.math.columbia.edu/tag/0703)
-/

@[expose] public section

namespace Module.PureProjectiveResolution

open CategoryTheory

universe u w

/-- One step of the construction of a pure projective resolution of `X`: a universally exact
short exact sequence `0 ⟶ kerObj ⟶ projObj ⟶ X ⟶ 0` whose middle term is pure projective. -/
private structure PureStep (A : Type u) [CommRing A] (X : Type w)
    [AddCommGroup X] [Module A X] where
  /-- The kernel of the presentation, to be presented at the next step. -/
  kerObj : ModuleCat.{max u w} A
  /-- The pure projective module presenting `X`. -/
  projObj : ModuleCat.{max u w} A
  /-- The inclusion of the kernel into the presenting module. -/
  incl : kerObj →ₗ[A] projObj
  /-- The presentation of `X`. -/
  proj : projObj →ₗ[A] X
  /-- The kernel is included injectively. -/
  injective_incl : Function.Injective incl
  /-- The presentation is surjective. -/
  surjective_proj : Function.Surjective proj
  /-- The presenting sequence is exact in the middle. -/
  exact_incl_proj : Function.Exact incl proj
  /-- The inclusion of the kernel stays injective after every base change. -/
  universallyInjective_incl : UniversallyInjective incl
  /-- The presenting module is pure projective. -/
  pureProjective_projObj : Module.PureProjective A projObj

/-- Every module admits one step of a pure projective resolution: a universally exact
presentation by a pure projective module ([Stacks, Tag 06ZZ]). -/
private theorem nonempty_pureStep (A : Type u) [CommRing A] (X : Type w)
    [AddCommGroup X] [Module A X] : Nonempty (PureStep.{u, w} A X) := by
  obtain ⟨N, P, iN, iNmod, iP, iPmod, f, g, hf, hg, hrange, hui, hpp⟩ :=
    Module.exists_pureProjective_universallyExact_presentation A X
  let := iN
  let := iNmod
  let := iP
  let := iPmod
  exact ⟨{ kerObj := ModuleCat.of A N
           projObj := ModuleCat.of A P
           incl := f
           proj := g
           injective_incl := hf
           surjective_proj := hg
           exact_incl_proj := LinearMap.exact_iff.mpr hrange.symm
           universallyInjective_incl := hui
           pureProjective_projObj := hpp }⟩

section Resolution

universe v

variable (A : Type u) [CommRing A] (M : Type v) [AddCommGroup M] [Module A M]

/-- A universally exact presentation of `M` itself by a pure projective module. -/
private noncomputable def base : PureStep.{u, v} A M := (nonempty_pureStep A M).some

/-- The tower of iterated kernels: the `n`-th entry is a universally exact presentation, by a
pure projective module, of the `n`-th syzygy of `M`. -/
@[reducible] private noncomputable def tower :
    ℕ → Σ X : ModuleCat.{max u v} A, PureStep.{u, max u v} A X :=
  Nat.rec ⟨(base A M).kerObj, (nonempty_pureStep A (base A M).kerObj).some⟩
    fun _ p => ⟨p.2.kerObj, (nonempty_pureStep A p.2.kerObj).some⟩

/-- The degree `n` term of the pure projective resolution of `M`. -/
@[reducible] private noncomputable def resObj : ℕ → ModuleCat.{max u v} A
  | 0 => (base A M).projObj
  | n + 1 => (tower A M n).2.projObj

/-- The differential of the pure projective resolution of `M`: the degree `n + 1` term surjects
onto the `n`-th syzygy, which is included in the degree `n` term. -/
private noncomputable def resDiff : (n : ℕ) → (resObj A M (n + 1) ⟶ resObj A M n)
  | 0 => ModuleCat.ofHom ((base A M).incl ∘ₗ (tower A M 0).2.proj)
  | n + 1 => ModuleCat.ofHom ((tower A M n).2.incl ∘ₗ (tower A M (n + 1)).2.proj)

private theorem resDiff_zero :
    resDiff A M 0 = ModuleCat.ofHom ((base A M).incl ∘ₗ (tower A M 0).2.proj) := rfl

private theorem resDiff_succ (n : ℕ) :
    resDiff A M (n + 1)
      = ModuleCat.ofHom ((tower A M n).2.incl ∘ₗ (tower A M (n + 1)).2.proj) := rfl

private theorem resDiff_comp_resDiff (n : ℕ) :
    resDiff A M (n + 1) ≫ resDiff A M n = 0 := by
  obtain _ | k := n
  · rw [resDiff_succ, resDiff_zero]
    apply ModuleCat.hom_ext
    ext x
    show (base A M).incl ((tower A M 0).2.proj
      ((tower A M 0).2.incl ((tower A M 1).2.proj x))) = 0
    rw [(tower A M 0).2.exact_incl_proj.apply_apply_eq_zero, map_zero]
  · rw [resDiff_succ, resDiff_succ]
    apply ModuleCat.hom_ext
    ext x
    simp [(tower A M (k + 1)).2.exact_incl_proj.apply_apply_eq_zero]

/-- The pure projective resolution of `M`. -/
@[reducible] private noncomputable def resComplex : ChainComplex (ModuleCat.{max u v} A) ℕ :=
  ChainComplex.of (resObj A M) (resDiff A M) (resDiff_comp_resDiff A M)

private theorem resComplex_d_one : (resComplex A M).d 1 0 = resDiff A M 0 :=
  ChainComplex.of_d (resObj A M) (resDiff A M) 0

private theorem resComplex_d_succ (n : ℕ) : (resComplex A M).d (n + 1) n = resDiff A M n :=
  ChainComplex.of_d (resObj A M) (resDiff A M) n

private theorem resComplex_d_succ_succ (n : ℕ) :
    (resComplex A M).d (n + 2) (n + 1) = resDiff A M (n + 1) :=
  ChainComplex.of_d (resObj A M) (resDiff A M) (n + 1)

private theorem exact_incl_proj_comp {A : Type u} [CommRing A] {X : Type w} [AddCommGroup X]
    [Module A X] (s : PureStep.{u, w} A X) (t : PureStep.{u, max u w} A s.kerObj)
    (u : PureStep.{u, max u w} A t.kerObj) :
    Function.Exact (t.incl ∘ₗ u.proj) (s.incl ∘ₗ t.proj) :=
  u.surjective_proj.comp_exact_iff_exact.mpr
    (s.injective_incl.comp_exact_iff_exact.mpr t.exact_incl_proj)

/-- The base change of `exact_incl_proj_comp` along any module `Q`. -/
private theorem rTensor_exact_incl_proj_comp {A : Type u} [CommRing A] {X : Type w}
    [AddCommGroup X] [Module A X] (s : PureStep.{u, w} A X)
    (t : PureStep.{u, max u w} A s.kerObj) (u : PureStep.{u, max u w} A t.kerObj)
    (Q : Type (max u w)) [AddCommGroup Q] [Module A Q] :
    Function.Exact ((t.incl ∘ₗ u.proj).rTensor Q) ((s.incl ∘ₗ t.proj).rTensor Q) := by
  rw [LinearMap.rTensor_comp, LinearMap.rTensor_comp]
  exact (LinearMap.rTensor_surjective Q u.surjective_proj).comp_exact_iff_exact.mpr
    ((s.universallyInjective_incl Q).comp_exact_iff_exact.mpr
      (rTensor_exact Q t.exact_incl_proj t.surjective_proj))

private theorem exact_resDiff (i : ℕ) :
    Function.Exact (resDiff A M (i + 1)) (resDiff A M i) := by
  obtain _ | k := i
  · exact exact_incl_proj_comp _ _ _
  · exact exact_incl_proj_comp _ _ _

private theorem baseChange_exact_resDiff (Q : Type (max u v)) [AddCommGroup Q] [Module A Q]
    (i : ℕ) :
    Function.Exact ((resDiff A M (i + 1)).hom.rTensor Q) ((resDiff A M i).hom.rTensor Q) := by
  obtain _ | k := i
  · exact rTensor_exact_incl_proj_comp _ _ _ Q
  · exact rTensor_exact_incl_proj_comp _ _ _ Q

/-- Every module admits a pure projective resolution. -/
@[stacks 0703 "existence"]
public theorem exists_isPureProjectiveResolution :
    ∃ (P : ChainComplex (ModuleCat.{max u v} A) ℕ) (augmentation : P.X 0 →ₗ[A] M),
      IsPureProjectiveResolution P augmentation := by
  refine ⟨resComplex A M, (base A M).proj, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact (base A M).surjective_proj
  · intro Q _ _
    exact LinearMap.rTensor_surjective Q (base A M).surjective_proj
  · rw [resComplex_d_one, resDiff_zero]
    exact ((tower A M 0).2.surjective_proj).comp_exact_iff_exact.mpr
      (base A M).exact_incl_proj
  · intro Q _ _
    rw [resComplex_d_one, resDiff_zero, ModuleCat.hom_ofHom, LinearMap.rTensor_comp]
    exact (LinearMap.rTensor_surjective Q
          (tower A M 0).2.surjective_proj).comp_exact_iff_exact.mpr
      (rTensor_exact Q (base A M).exact_incl_proj (base A M).surjective_proj)
  · intro i
    rw [resComplex_d_succ_succ, resComplex_d_succ]
    exact exact_resDiff A M i
  · intro Q _ _ i
    rw [resComplex_d_succ_succ, resComplex_d_succ]
    exact baseChange_exact_resDiff A M Q i
  · intro i
    obtain _ | k := i
    · exact (base A M).pureProjective_projObj
    · exact (tower A M k).2.pureProjective_projObj

end Resolution

end Module.PureProjectiveResolution

end
