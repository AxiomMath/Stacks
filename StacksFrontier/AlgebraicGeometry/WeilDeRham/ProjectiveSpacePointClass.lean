module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.ChowCohomologyOverFieldIso
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.Transport
public import StacksFrontier.AlgebraicGeometry.Chow.FieldSituation.NegativeDimensionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ProjectiveBundleFormula.Formula
public import StacksFrontier.AlgebraicGeometry.ProjCoherentCohomologyFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.TwistTransport
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.Basic
public import StacksFrontier.AlgebraicGeometry.ProjTwistRank.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.SmoothOfRelativeDimension
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.TopDegreeAffineBase
public import StacksFrontier.AlgebraicGeometry.TwistChartLocality.ChartGamma
public import StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalGysinPoint

/-!
# The class of a rational point of projective space is `c₁(𝒪(1))^d ∩ [ℙ^d]`

In the proof of Axiom (A6) for de Rham cohomology (Stacks, Proposition 0FWD) the source reduces
to `ℙ^d_k` and needs "a zero cycle on `ℙ^d_k` whose class is nonzero", which it gets from
Lemma 0FMJ: the cohomology class `c₁^H(𝒪(1))^d` is nonzero. The Chow-theoretic link is that the
class of a `k`-rational point of `ℙ^d_k` is a power of the first Chern class of `𝒪(1)`:

  `c₁(𝒪(1))^d ∩ [ℙ^d_k] = x_*[Spec k]`   in `CH_0(ℙ^d_k)`,

for every `k`-rational point `x : Spec k ⟶ ℙ^d_k`. This file proves it, for `ℙ^d_k` the
polynomial model `Proj k[T₀, …, T_d]` over `Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff`
(the model of `StacksFrontier.AlgebraicGeometry.DeRham.ProjectiveSpaceDeRhamEveryDimension` and of
`StacksFrontier.AlgebraicGeometry.WeilDeRham.FiniteProjectionToProjectiveSpace`), with `𝒪(1)` its
Serre twist `ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1` and `c₁(𝒪(1)) ∩ -` the
first Chern class cap of Stacks 02SO / 02TI (`Stacks.Chow.invCap`), its `d`-th power being
`Stacks.Chow.capPow`.

## The argument

The proof is the projective bundle formula (Stacks 02TX, 02TW) for `π : ℙ^d_k ⟶ Spec k`. The
polynomial model with `𝒪(1)` is a projective tower of fibre dimension `d`
(`Stacks.WeilDeRham.isProjectiveTower_projToSpecCoeff`): the base's integral model is one
(`Stacks.Chow.FreeTower.isProjectiveTower_projectiveSpaceOver`), and the comparison of the two
models (`Stacks.ProjectiveCohomology.projModelIso`) lies over `Spec k` and matches the two
twists
(`Stacks.ProjectiveCohomology.nonempty_projectiveTwistingSheaf_iso_pullback_projModelIso_inv`).
Then:

* by surjectivity in Stacks 02TX, `CH_0(ℙ^d_k)` is spanned by the classes `ξ^i ∩ π^* β_i` with
  `β_i ∈ CH_{i-d}(Spec k)`, and these groups vanish for `i < d`, so every `γ ∈ CH_0(ℙ^d_k)` is
  `ξ^d ∩ π^* β`; by the top case of Stacks 02TW, `β = π_* γ`
  (`Stacks.WeilDeRham.eq_capPow_bundlePullback_properChowPushforward`);
* for `γ = x_*[Spec k]`, `π_* γ = (x ≫ π)_*[Spec k] = [Spec k]`, and `π^*[Spec k] = [ℙ^d_k]`
  (flat pullback of a fundamental class).

No hyperplane is ever cut and no coordinate change is made: the identity holds for every rational
point at once, which is the form in which (A6) uses it.

## Main results

* `Stacks.WeilDeRham.capPow_twistingSheaf_fundamentalChowClass_eq_point` —
  `c₁(𝒪(1))^d ∩ [ℙ^d_k]_d = x_*[Spec k]_0` in `CH_0(ℙ^d_k)`.
* `Stacks.WeilDeRham.chowCodimPushforward_point_eq_chowCodimPart_capPow` — the same identity in
  `CH^d(ℙ^d_k)`, with the class of the point written as in
  `StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalGysinPoint`:
  `Stacks.WeilCohomology.chowCodimPushforward k (𝟙 _) π x hx 0 d (chowCodimFundamental k (𝟙 _))`.
* `Stacks.WeilDeRham.properChowPushforward_point_eq_point` — any two `k`-rational points of
  `ℙ^d_k` have the same class in `CH_0(ℙ^d_k)`.
* `Stacks.WeilDeRham.isProjectiveTower_projToSpecCoeff` — `Proj R[T₀, …, T_d] ⟶ Spec R` with
  `𝒪(1)` is a projective tower of fibre dimension `d`, for every commutative ring `R`.
* `Stacks.WeilDeRham.eq_capPow_bundlePullback_properChowPushforward` — for a locally projective
  tower `π` of fibre dimension `n` and a degree `m = k + n` below which the base has no Chow
  groups, every `γ ∈ CH_m(P)` is `ξ^n ∩ π^*(π_* γ)`.

## References

* [Stacks Project, Tag 0FWD](https://stacks.math.columbia.edu/tag/0FWD)
* [Stacks Project, Tag 0FMJ](https://stacks.math.columbia.edu/tag/0FMJ)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02TW](https://stacks.math.columbia.edu/tag/02TW)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02TI](https://stacks.math.columbia.edu/tag/02TI)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.WeilDeRham

open Stacks.Chow Stacks.AlgebraicGeometry.ProjPolyChart

attribute [local instance] MvPolynomial.gradedAlgebra
  Stacks.ProjCoherentCohomologyFinite.isProper_projToSpecCoeff

/-! ### The polynomial model of projective space is a projective tower -/

section Tower

variable (R : Type u) [CommRing R] (d : ℕ)

/-- **The polynomial model of projective space is a projective tower.** `Proj R[T₀, …, T_d] ⟶
Spec R` with `𝒪(1)` is a projective tower of fibre dimension `d`: the comparison
`Stacks.ProjectiveCohomology.projModelIso` with the base change of the integral model lies over
`Spec R` and carries `𝒪(1)` to `𝒪(1)`, and the integral model is a projective tower over every
base (`Stacks.Chow.FreeTower.isProjectiveTower_projectiveSpaceOver`). -/
theorem isProjectiveTower_projToSpecCoeff :
    IsProjectiveTower d (projToSpecCoeff R d)
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R d) 1) := by
  set e := Stacks.ProjectiveCohomology.projModelIso R d
  obtain ⟨i⟩ :=
    Stacks.ProjectiveCohomology.nonempty_projectiveTwistingSheaf_iso_pullback_projModelIso_inv
      R d 1 (Stacks.AlgebraicGeometry.TwistChartLocality.hasPolyTwistTransport R d 1)
  have he : e.hom ≫ pullback.fst (terminal.from (Spec (CommRingCat.of R)))
      (terminal.from (AlgebraicGeometry.projectiveSpaceAtUniverse.{u} d)) =
        projToSpecCoeff R d := by
    rw [Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism,
      Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.projToSpecCoeff_eq_projModelToSpec]
  refine IsProjectiveTower.of_iso_left e he ?_
    (Stacks.Chow.FreeTower.isProjectiveTower_projectiveSpaceOver d (Spec (CommRingCat.of R)))
  exact ((Scheme.Modules.pullbackId (AlgebraicGeometry.Proj (polyGrading R d))).app
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R d) 1)).symm ≪≫
    (Scheme.Modules.pullbackCongr e.hom_inv_id).symm.app _ ≪≫
    ((Scheme.Modules.pullbackComp e.hom e.inv).app _).symm ≪≫
    (Scheme.Modules.pullback e.hom).mapIso i.symm

/-- The Serre twists of the polynomial model of projective space are invertible, in the form the
first Chern class cap of Stacks 02SO consumes (Stacks 01MT). -/
instance isInvertible_twistingSheaf_polyGrading (m : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (polyGrading R d)).sheaf.obj
      (AlgebraicGeometry.Proj (polyGrading R d)).ringCatSheaf.property
      (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading R d) m) :=
  Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover.isInvertible_twistingSheaf
    (polyGrading R d) (Stacks.AlgebraicGeometry.ProjTwistRank.degreeOneCover_polyGrading R d) m

end Tower

/-- **A projective tower is flat, locally of finite type, of relative dimension its fibre
dimension.** In fibre dimension zero it is an isomorphism; in positive fibre dimension these are
part of the structure. -/
theorem locallyOfFiniteType_flat_relativeDimension_of_isProjectiveTower {n : ℕ}
    {P U : Scheme.{u}} {π : P ⟶ U} {L : P.Modules} (h : IsProjectiveTower n π L) :
    ∃ (_ : LocallyOfFiniteType π) (_ : Flat π), AlgebraicGeometry.RelativeDimension π n := by
  cases h with
  | zero _ _ hiso _ => exact ⟨inferInstance, inferInstance, relativeDimension_of_isIso π⟩
  | succ n π L hπ => exact ⟨inferInstance, inferInstance, hπ⟩

/-- `Proj R[T₀, …, T_d] ⟶ Spec R` has relative dimension `d`. -/
theorem relativeDimension_projToSpecCoeff (R : Type u) [CommRing R] (d : ℕ) :
    AlgebraicGeometry.RelativeDimension (projToSpecCoeff R d) d :=
  (locallyOfFiniteType_flat_relativeDimension_of_isProjectiveTower
    (isProjectiveTower_projToSpecCoeff R d)).snd.snd

/-! ### Classes of the top-codimensional degree along a projective tower -/

/-- **Along a projective tower, a class in the bottom degree is `ξ^n ∩ π^*(π_* γ)`.** Let
`π : P ⟶ U` be a locally projective tower of fibre dimension `n` with module `L`, `ξ = c₁(L) ∩ -`,
and let `m = k + n` be a degree such that `CH_{k+i}(U) = 0` for all `i < n`. Then every
`γ ∈ CH_m(P)` is `ξ^n ∩ π^*(π_* γ)`.

By surjectivity in Stacks 02TX, `γ = ∑_{i ≤ n} ξ^i ∩ π^* β_i` with `β_i ∈ CH_{k+i}(U)`; all but the
last summand vanish, and the top case of Stacks 02TW gives `π_* γ = β_n`. -/
theorem eq_capPow_bundlePullback_properChowPushforward (C : ChowSituation.{u})
    {n : ℕ} {P U : Scheme.{u}} {π : P ⟶ U} {L : P.Modules} (h : IsLocallyProjectiveTower n π L)
    (sU : U ⟶ C.S) [LocallyOfFiniteType sU] (sP : P ⟶ C.S) [LocallyOfFiniteType sP]
    (hsP : π ≫ sU = sP)
    [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property L]
    [Flat π] [IsProper π]
    (hπ : AlgebraicGeometry.RelativeDimension π n) (k m : ℤ) (hm : m = k + n)
    (hvan : ∀ i : ℕ, i < n → Subsingleton (chowGroup C sU (k + i)))
    (γ : chowGroup C sP m) :
    γ = capPow C sP (invCap C sP L) n (m + n) m rfl
      (bundlePullback C sU sP π hsP n hπ m
        (properChowPushforward C sP sU π hsP m
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP m) γ)) := by
  subst hm
  obtain ⟨β, hβ⟩ := h.bundleMap_surjective C (affineBundleSurjectivity C) sU sP hsP hπ k γ
  have hsum : bundleMap C sU sP π hsP n hπ (invCap C sP L) k β =
      bundleTerm C sU sP π hsP n hπ (invCap C sP L) k n (β (Fin.last n)) := by
    rw [bundleMap_apply, Finset.sum_eq_single (Fin.last n)]
    · rfl
    · intro i _ hi
      have := hvan i (Fin.val_lt_last hi)
      rw [Subsingleton.elim (β i) 0, map_zero]
    · intro h'
      exact absurd (Finset.mem_univ _) h'
  have hproj : properChowPushforward C sP sU π hsP (k + n)
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sP sU π hsP (k + n)) γ =
      β (Fin.last n) := by
    rw [← hβ, hsum]
    exact h.bundleProjection_self C sU sP hsP hπ (k + n) (β (Fin.last n))
  rw [hproj]
  exact hβ.symm.trans hsum

/-- **Over a field there are no Chow groups in negative degree**: there are no nonzero cycles of
negative dimension (`Stacks.Chow.cycleGroup_eq_zero_of_neg`). -/
theorem subsingleton_chowGroup_field_of_neg (k : Type u) [Field k] {Y : Scheme.{u}}
    (s : Y ⟶ Spec (.of k)) [LocallyOfFiniteType s] {m : ℤ} (hm : m < 0) :
    Subsingleton (chowGroup (fieldChowSituation k) s m) := by
  refine ⟨fun a b => ?_⟩
  obtain ⟨c, rfl⟩ := QuotientAddGroup.mk'_surjective _ a
  obtain ⟨c', rfl⟩ := QuotientAddGroup.mk'_surjective _ b
  rw [cycleGroup_eq_zero_of_neg k s hm c, cycleGroup_eq_zero_of_neg k s hm c']

/-! ### The class of a rational point of `ℙ^d_k` -/

variable (k : Type u) [Field k] (d : ℕ)

/-- **The class of a rational point of `ℙ^d_k` is `c₁(𝒪(1))^d ∩ [ℙ^d_k]`, for any structure
morphism equal to that of `ℙ^d_k` and any module isomorphic to `𝒪(1)`.** For `sP = π ≫ 𝟙` and
`L' ≅ 𝒪(1)`, the pushforward of `[Spec k]_n` along a section `x` of `sP` is
`c₁(L')^d ∩ [ℙ^d_k]_{n+d}`, in a degree `n = 0`. The case `sP = π`, `L' = 𝒪(1)` is
`Stacks.WeilDeRham.properChowPushforward_point_eq_capPow`. -/
theorem properChowPushforward_point_eq_capPow_of_iso
    (sP : AlgebraicGeometry.Proj (polyGrading k d) ⟶ Spec (.of k)) [LocallyOfFiniteType sP]
    (hsP : projToSpecCoeff k d ≫ 𝟙 _ = sP)
    (L : (AlgebraicGeometry.Proj (polyGrading k d)).Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible
      (AlgebraicGeometry.Proj (polyGrading k d)).sheaf.obj
      (AlgebraicGeometry.Proj (polyGrading k d)).ringCatSheaf.property L]
    (eL : L ≅ ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1)
    (x : Spec (.of k) ⟶ AlgebraicGeometry.Proj (polyGrading k d))
    (hx : x ≫ sP = 𝟙 _) (n : ℤ) (hn : n = 0) :
    haveI : IsSeparated sP := hsP ▸ inferInstance
    haveI : IsProper x := isProper_of_comp_eq_id hx
    properChowPushforward (fieldChowSituation k) (𝟙 _) sP x hx n
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ n)
        (fundamentalChowClass (fieldChowSituation k) (𝟙 _) n) =
      capPow (fieldChowSituation k) sP (invCap (fieldChowSituation k) sP L) d (n + d) n rfl
        (fundamentalChowClass (fieldChowSituation k) sP (n + d)) := by
  subst hsP hn
  have : IsProper x := isProper_of_comp_eq_id hx
  have hT := (isProjectiveTower_projToSpecCoeff k d).of_iso_module eL
  obtain ⟨_, _, hπ⟩ := locallyOfFiniteType_flat_relativeDimension_of_isProjectiveTower hT
  have key := eq_capPow_bundlePullback_properChowPushforward (fieldChowSituation k)
    hT.isLocallyProjectiveTower (𝟙 _) (projToSpecCoeff k d ≫ 𝟙 _) rfl hπ (-d) 0
    (by ring) (fun i hi => subsingleton_chowGroup_field_of_neg k _ (by omega))
    (properChowPushforward (fieldChowSituation k) (𝟙 _) (projToSpecCoeff k d ≫ 𝟙 _) x hx 0
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ 0)
        (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0))
  -- `π_* x_* [Spec k] = (x ≫ π)_* [Spec k] = [Spec k]`
  rw [← properChowPushforward_comp_apply (fieldChowSituation k) (𝟙 _)
      (projToSpecCoeff k d ≫ 𝟙 _) (𝟙 _) x (projToSpecCoeff k d) (𝟙 _)
      (by simpa using hx) hx rfl (Category.id_comp _) 0
      _ _ (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ 0),
    properChowPushforward_id, AddMonoidHom.id_apply] at key
  -- `π^*[Spec k] = [ℙ^d_k]`
  have hpull : bundlePullback (fieldChowSituation k) (𝟙 _) (projToSpecCoeff k d ≫ 𝟙 _)
      (projToSpecCoeff k d) rfl d hπ 0
      (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) =
      fundamentalChowClass (fieldChowSituation k) (projToSpecCoeff k d ≫ 𝟙 _) (0 + d) :=
    flatPullbackChow_fundamentalChowClass (fieldChowSituation k) _ _ _ _ d hπ 0 _
      (schemeDeltaDimension_id_fieldChowSituation_le k)
  rw [hpull] at key
  exact key

/-- **The class of a rational point of `ℙ^d_k` is `c₁(𝒪(1))^d ∩ [ℙ^d_k]`, in a degree `n = 0`.**
This is `Stacks.WeilDeRham.capPow_twistingSheaf_fundamentalChowClass_eq_point` with the degree of
the point an integer `n` equal to zero, the form in which the codimension-graded statement
consumes it. -/
theorem properChowPushforward_point_eq_capPow
    (x : Spec (.of k) ⟶ AlgebraicGeometry.Proj (polyGrading k d))
    (hx : x ≫ projToSpecCoeff k d = 𝟙 _) (n : ℤ) (hn : n = 0) :
    haveI : IsProper x := isProper_of_comp_eq_id hx
    properChowPushforward (fieldChowSituation k) (𝟙 _) (projToSpecCoeff k d) x hx n
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ n)
        (fundamentalChowClass (fieldChowSituation k) (𝟙 _) n) =
      capPow (fieldChowSituation k) (projToSpecCoeff k d)
        (invCap (fieldChowSituation k) (projToSpecCoeff k d)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1)) d (n + d) n rfl
        (fundamentalChowClass (fieldChowSituation k) (projToSpecCoeff k d) (n + d)) :=
  properChowPushforward_point_eq_capPow_of_iso k d (projToSpecCoeff k d) (Category.comp_id _)
    _ (Iso.refl _) x hx n hn

/-- **The class of a rational point of projective space is a power of the first Chern class of
`𝒪(1)`.** For every `k`-rational point `x : Spec k ⟶ ℙ^d_k` of the polynomial model of projective
space,

  `c₁(𝒪(1))^d ∩ [ℙ^d_k] = x_*[Spec k]`   in `CH_0(ℙ^d_k)`,

with `c₁(𝒪(1)) ∩ -` the first Chern class cap of Stacks 02SO / 02TI, `[ℙ^d_k]` the fundamental
class in dimension `d` and `x_*` proper pushforward. This is the identification the proof of
(A6), the trace axiom, in Stacks 0FWD needs to deduce, from Lemma 0FMJ, that the class of a zero
cycle of `ℙ^d_k` is nonzero. -/
theorem capPow_twistingSheaf_fundamentalChowClass_eq_point
    (x : Spec (.of k) ⟶ AlgebraicGeometry.Proj (polyGrading k d))
    (hx : x ≫ projToSpecCoeff k d = 𝟙 _) :
    haveI : IsProper x := isProper_of_comp_eq_id hx
    capPow (fieldChowSituation k) (projToSpecCoeff k d)
        (invCap (fieldChowSituation k) (projToSpecCoeff k d)
          (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1)) d d 0 (by simp)
        (fundamentalChowClass (fieldChowSituation k) (projToSpecCoeff k d) d) =
      properChowPushforward (fieldChowSituation k) (𝟙 _) (projToSpecCoeff k d) x hx 0
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ 0)
        (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) := by
  refine Eq.trans ?_ (properChowPushforward_point_eq_capPow k d x hx 0 rfl).symm
  have hcast : ∀ {a b : ℤ} (e : a = b),
      chowGroupCast (fieldChowSituation k) (projToSpecCoeff k d) e
        (fundamentalChowClass (fieldChowSituation k) (projToSpecCoeff k d) a) =
      fundamentalChowClass (fieldChowSituation k) (projToSpecCoeff k d) b := by
    intro a b e
    subst e
    rfl
  rw [← hcast (show (d : ℤ) = 0 + d by ring), capPow_cast]

/-- **All rational points of `ℙ^d_k` have the same class**: for two `k`-rational points `x`, `y`
of the polynomial model, `x_*[Spec k] = y_*[Spec k]` in `CH_0(ℙ^d_k)`, both being
`c₁(𝒪(1))^d ∩ [ℙ^d_k]`. -/
theorem properChowPushforward_point_eq_point
    (x y : Spec (.of k) ⟶ AlgebraicGeometry.Proj (polyGrading k d))
    (hx : x ≫ projToSpecCoeff k d = 𝟙 _) (hy : y ≫ projToSpecCoeff k d = 𝟙 _) :
    haveI : IsProper x := isProper_of_comp_eq_id hx
    haveI : IsProper y := isProper_of_comp_eq_id hy
    properChowPushforward (fieldChowSituation k) (𝟙 _) (projToSpecCoeff k d) x hx 0
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ 0)
        (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) =
      properChowPushforward (fieldChowSituation k) (𝟙 _) (projToSpecCoeff k d) y hy 0
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper _ _ _ _ _ 0)
        (fundamentalChowClass (fieldChowSituation k) (𝟙 _) 0) :=
  (capPow_twistingSheaf_fundamentalChowClass_eq_point k d x hx).symm.trans
    (capPow_twistingSheaf_fundamentalChowClass_eq_point k d y hy)

/-- **The class of a rational point of `ℙ^d_k` in `CH^d(ℙ^d_k)`.** In the codimension-graded
groups of the definition of a Weil cohomology theory, the class
`[x] = x_*[Spec k] ∈ CH^d(ℙ^d_k)` of a `k`-rational point, written as in
`StacksFrontier.AlgebraicGeometry.WeilDeRham.DiagonalGysinPoint`, is the codimension-`d` part of the
family `n ↦ c₁(𝒪(1))^d ∩ [ℙ^d_k]_{n+d}`, `[ℙ^d_k]_{n+d}` being the dimension-`(n+d)` class of
the fundamental class `[ℙ^d_k] ∈ CH^0(ℙ^d_k)`.

On the part of `ℙ^d_k` of dimension `d`, which is everything, this is
`Stacks.WeilDeRham.properChowPushforward_point_eq_capPow`; the other parts are empty. -/
theorem chowCodimPushforward_point_eq_chowCodimPart_capPow
    (x : Spec (.of k) ⟶ AlgebraicGeometry.Proj (polyGrading k d))
    (hx : x ≫ projToSpecCoeff k d = 𝟙 _) :
    haveI : IsProper x := isProper_of_comp_eq_id hx
    haveI : SmoothOfRelativeDimension d (projToSpecCoeff k d) :=
      smoothOfRelativeDimension_projToSpecCoeff k d
    haveI : Smooth (projToSpecCoeff k d) := SmoothOfRelativeDimension.smooth d _
    Stacks.WeilCohomology.chowCodimPushforward k (𝟙 _) (projToSpecCoeff k d) x hx 0 d
        (Stacks.WeilCohomology.chowCodimFundamental k (𝟙 _)) =
      Stacks.WeilCohomology.chowCodimPart k (projToSpecCoeff k d)
        (fun n ↦ capPow (fieldChowSituation k) (projToSpecCoeff k d)
          (invCap (fieldChowSituation k) (projToSpecCoeff k d)
            (ProjectiveSpectrum.Proj.twistingSheaf (polyGrading k d) 1)) d (n + d) n rfl
          (Stacks.WeilCohomology.chowCodimTotal k (projToSpecCoeff k d) 0 (n + d)
            (Stacks.WeilCohomology.chowCodimFundamental k (projToSpecCoeff k d)))) d := by
  have : IsProper x := isProper_of_comp_eq_id hx
  have : SmoothOfRelativeDimension d (projToSpecCoeff k d) :=
    smoothOfRelativeDimension_projToSpecCoeff k d
  have : Smooth (projToSpecCoeff k d) := SmoothOfRelativeDimension.smooth d _
  funext e
  simp only [Stacks.WeilCohomology.chowCodimPushforward, Stacks.WeilCohomology.chowCodimPart]
  by_cases he : e = d
  · subst he
    congr 1
    rw [chowCodimTotal_chowCodimFundamental (𝟙 _) (relativeDimension_of_isIso _),
      chowCodimTotal_chowCodimFundamental (projToSpecCoeff k e)
        (relativeDimension_projToSpecCoeff k e)]
    exact properChowPushforward_point_eq_capPow k e x hx _ (by ring)
  · have := Stacks.WeilCohomology.isEmpty_dimPart_of_ne (projToSpecCoeff k d)
      (relativeDimension_projToSpecCoeff k d) he
    exact (subsingleton_chowGroup_of_isEmpty (fieldChowSituation k) _ _).elim _ _

end Stacks.WeilDeRham

end
