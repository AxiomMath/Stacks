module

public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.WhitneyDeformation
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.AffineHomotopy
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.DefinedChernClasses
public import StacksFrontier.AlgebraicGeometry.Chow.LocalizedChern.LocalizedClosedCover
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.ShortExact
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.FiberRankIsomorphismInvariant
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.Triangles
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDerived.Triangle
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodOverEtaPerfect
public import Mathlib.Algebra.Homology.DerivedCategory.HomologySequence
public import StacksFrontier.Homology.Perfect.BoundedComplexCokernelRank

/-!
# The deformation to the direct sum in the proof of Stacks 0FBD

Let `(S, δ)` be the base situation of chapter 42, let `X` be locally of finite type over `S`, let
`i : Z ⟶ X` be a closed immersion and let `φ : P₃ ⟶ P₁` be a map of locally bounded complexes of
finite locally free `𝒪_X`-modules, so that `E₁ = P₁`, `E₂ = C(φ)` and `E₃ = P₃[1]` sit in a
distinguished triangle `E₁ ⟶ E₂ ⟶ E₃ ⟶ E₁[1]`. Suppose `E₁|_{X ∖ Z}` and `E₃|_{X ∖ Z}` are finite
locally free of rank `< p₁` and `< p₃` placed in degree `0`. The third paragraph of the proof of
Stacks 0FBD shows

  `c_p(Z ⟶ X, E₂) = c_p(Z ⟶ X, E₁ ⊕ E₃)`   for `p + 1 ≥ p₁ + p₃`,

and, when `E₁` and `E₃` vanish off `Z`, `P_p(Z ⟶ X, E₂) = P_p(Z ⟶ X, E₁ ⊕ E₃)` for all `p`. On
`X' = 𝐀¹_X` with coordinate `t` consider the mapping cone `C` of `t · π^*φ`. Off `Z' = 𝐀¹_Z` it is
finite locally free of rank `< p₁ + p₃ - 1` in degree `0` (resp. zero), so it has localized classes
on `𝐀¹_X`. Its fibre at `t = 1` is `C(φ)` and its fibre at `t = 0` is `C(0) = E₁ ⊕ E₃`, so by
Stacks 0FB3 the two classes on `X` are the restrictions of the class of `C` along the sections
`t = 1` and `t = 0`, and these restrictions agree ("`i_0^* = i_1^*`",
`Stacks.Chow.SectionDivisor.sectionRestriction_eq`).

The first sentence of that proof, "the statement makes sense", is
`Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_iso_obj₂`: the middle vertex of a distinguished
triangle whose outer vertices are finite locally free modules of rank `< a` and `< c` in degree
`0` is one of rank `< a + c - 1`.

## Main definitions

* `Stacks.Chow.SectionDivisor.ofSection` — a closed-immersion section cut out by a section of an
  invertible module, as a divisor; `Stacks.Chow.affineLineZeroDivisor` and
  `Stacks.Chow.affineLinePointDivisor` — the points `0` and `t` of `𝐀¹_Y`.
* `Stacks.Chow.SectionDivisor.sectionRestriction` — the restriction `i_σ^* c` of a bivariant class
  on `𝐀¹_X` along a section, read on `Z`.
* `Stacks.Chow.LocalizedChernData.deformationSituation` — the deformation cone as an instance of
  Situation 0GUJ on `𝐀¹_X`.

## Main results

* `Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_iso_obj₂`,
  `Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_obj₂` — the extension of finite
  locally free modules of rank `< a`, `< c` in degree `0` in a distinguished triangle, on `Y` and
  after restriction along any morphism.
* `Stacks.Chow.SectionDivisor.sectionRestriction_eq` — `i_σ^* = i_σ'^*` for two divisors of an
  affine-space bundle of rank one.
* `Stacks.Chow.LocalizedChernData.localizedChern_mappingCone_eq` — `c_p(Z ⟶ X, C(φ)) =
  c_p(Z ⟶ X, C(0))` for `p₁ + p₃ ≤ p + 1`, for the classes of Remark 0GUK.
* `Stacks.Chow.LocalizedChernData.localizedPowerSum_mappingCone_eq` — `P_q(Z ⟶ X, C(φ)) =
  P_q(Z ⟶ X, C(0))` for all `q` when `P₁` and `P₃[1]` vanish off `Z`.

## Implementation notes

The rank bound is `a + c - 1` rather than the `a + c` of the source: ranks `< a` and `< c` add up
to at most `(a - 1) + (c - 1)`. Accordingly the deformation is run in every degree `p` with
`p₁ + p₃ ≤ p + 1`.

The comparison is carried out in Situation 0GUJ, through alternative (c) of its condition (3)
(`C(φ)`, `C(0)` and the deformation cone are locally bounded complexes of finite locally free
modules), and transferred to the classes of Remark 0GUK by
`Stacks.Chow.LocalizedSituation.localizedChern_toLocalizedChernData`. The objects `E ≅ C(φ)`
and `E₀ ≅ C(0)` are arbitrary objects isomorphic to the two cones: Stacks 0FB3 is applied in the
form `Stacks.Chow.bivariantTransport_bivariantRestriction_graphChernClass_of_eq`, which accepts
any object isomorphic to the derived fibre of the deformation cone and any closed subscheme
identified with the base change of `𝐀¹_Z`.

## References

* [Stacks Project, Tag 0FBD](https://stacks.math.columbia.edu/tag/0FBD)
* [Stacks Project, Tag 0FB3](https://stacks.math.columbia.edu/tag/0FB3)
* [Stacks Project, Tag 0GUJ](https://stacks.math.columbia.edu/tag/0GUJ)
* [Stacks Project, Tag 0GUK](https://stacks.math.columbia.edu/tag/0GUK)
* [Stacks Project, Tag 0F96](https://stacks.math.columbia.edu/tag/0F96)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open StrictlyPerfect
open Stacks.SheafOfModules.FlatShortExact (abStalk stalkModule stalkShortExact)

universe u

namespace Stacks.Chow

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Finite locally free objects in a distinguished triangle -/

section Triangle

variable {Y : Scheme.{u}}

/-- The fibre rank at a point where the stalk is free of finite rank is the rank of the stalk. -/
theorem fiberRank_eq_finrank_stalk_of_free (F : Y.Modules) (x : Y)
    (hfree :
      letI : Module (Y.presheaf.stalk x) (F.presheaf.stalk x) :=
        PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
          (R := Y.presheaf) F.val x
      Module.Free (Y.presheaf.stalk x) (F.presheaf.stalk x) ∧
        Module.Finite (Y.presheaf.stalk x) (F.presheaf.stalk x)) :
    letI : Module (Y.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) F.val x
    Scheme.Modules.fiberRank F x = Module.finrank (Y.presheaf.stalk x) (F.presheaf.stalk x) := by
  let A := ToType (Y.presheaf.stalk x)
  let M := ToType (F.presheaf.stalk x)
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) F.val x
  let : Module.Free A M := hfree.1
  let : Module.Finite A M := hfree.2
  let : IsLocalRing A := Y.isLocalRing x
  let : Algebra A (Y.residueField x) := (Y.residue x).hom.toAlgebra
  exact Module.finrank_baseChange

/-- At every point the fibre rank of a module of rank `< p` is `< p`. -/
theorem IsFiniteLocallyFreeOfRankLT.fiberRank_lt {M : Y.Modules} {p : ℕ} (hM :
    IsFiniteLocallyFreeOfRankLT M p)
    (x : Y) : Scheme.Modules.fiberRank M x < p := by
  obtain ⟨V, hxV, r, hrp, hr⟩ := hM.2 x
  let V' : Y.Opens := V
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.restrictFunctor V'.ι).obj M) r :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso
      ((Stacks.AlgebraicGeometry.PerfectCohomology.restrictModulesIsoRestrict Y V').app M) hr
  have h : Scheme.Modules.fiberRank M x = r :=
    (Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict V'.ι M ⟨x, hxV⟩).symm.trans
      (Scheme.Modules.fiberRank_eq_rank_of_isFiniteLocallyFreeOfRank _ r _)
  exact h ▸ hrp

/-- A finite locally free module placed in degree `0` is perfect. -/
theorem isPerfect_of_iso_singleFunctor (M : Y.Modules)
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M]
    {K : DerivedCategory Y.Modules} (e : K ≅ (DerivedCategory.singleFunctor _ 0).obj M) :
    Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) K := by
  let e' : DerivedCategory.Q.obj ((CochainComplex.singleFunctor Y.Modules 0).obj M) ≅ K :=
    ((DerivedCategory.singleFunctorIsoCompQ Y.Modules 0).app M).symm ≪≫ e.symm
  exact ⟨_, Stacks.BlowUpComplexes.isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree _
      (isLocallyBoundedFiniteLocallyFree_single M), ⟨e'⟩⟩

/-- **The middle stalk of a short exact sequence of modules with free outer stalks.** If the
stalks at `x` of the outer terms of a short exact sequence of `𝒪_Y`-modules are free of finite
rank, so is the stalk of the middle term (the sequence of stalks splits), and the fibre ranks at
`x` add up. -/
theorem free_stalk_and_fiberRank_add_of_shortExact (S : ShortComplex Y.Modules) (hS :
    S.ShortExact) (x : Y)
    (h₁ : Module.Free (ToType (Y.presheaf.stalk x)) (ToType (TopCat.Presheaf.stalk
        S.X₁.val.presheaf x)) ∧
      Module.Finite (ToType (Y.presheaf.stalk x)) (ToType (TopCat.Presheaf.stalk S.X₁.val.presheaf
          x)))
    (h₃ : Module.Free (ToType (Y.presheaf.stalk x)) (ToType (TopCat.Presheaf.stalk
        S.X₃.val.presheaf x)) ∧
      Module.Finite (ToType (Y.presheaf.stalk x)) (ToType (TopCat.Presheaf.stalk S.X₃.val.presheaf
          x))) :
    (Module.Free (ToType (Y.presheaf.stalk x)) (ToType (TopCat.Presheaf.stalk S.X₂.val.presheaf
        x)) ∧
      Module.Finite (ToType (Y.presheaf.stalk x)) (ToType (TopCat.Presheaf.stalk S.X₂.val.presheaf
          x))) ∧
      Scheme.Modules.fiberRank S.X₂ x =
        Scheme.Modules.fiberRank S.X₁ x + Scheme.Modules.fiberRank S.X₃ x := by
  let R := ToType (Y.presheaf.stalk x)
  let := stalkModule (X := Y.toRingedSpace) S.X₁ x
  let := stalkModule (X := Y.toRingedSpace) S.X₂ x
  let := stalkModule (X := Y.toRingedSpace) S.X₃ x
  obtain ⟨f, g, hf, hfg, hg⟩ := stalkShortExact (X := Y.toRingedSpace) S hS x
  have : Module.Free R (abStalk (X := Y.toRingedSpace) S.X₁ x) := h₁.1
  have : Module.Finite R (abStalk (X := Y.toRingedSpace) S.X₁ x) := h₁.2
  have : Module.Free R (abStalk (X := Y.toRingedSpace) S.X₃ x) := h₃.1
  have : Module.Finite R (abStalk (X := Y.toRingedSpace) S.X₃ x) := h₃.2
  obtain ⟨e⟩ := Stacks.CokernelRank.nonempty_linearEquiv_prod_of_exact f g hf hg hfg
  have hfree : Module.Free R (abStalk (X := Y.toRingedSpace) S.X₂ x) := Module.Free.of_equiv e.symm
  have hfin : Module.Finite R (abStalk (X := Y.toRingedSpace) S.X₂ x) := Module.Finite.equiv e.symm
  refine ⟨⟨hfree, hfin⟩, ?_⟩
  rw [fiberRank_eq_finrank_stalk_of_free S.X₁ x h₁, fiberRank_eq_finrank_stalk_of_free S.X₃ x h₃,
    fiberRank_eq_finrank_stalk_of_free S.X₂ x ⟨hfree, hfin⟩]
  exact e.finrank_eq.trans Module.finrank_prod

/-- **An extension of finite locally free modules in degree `0`** (the first sentence of the proof
of Stacks 0FBD). Let `A ⟶ B ⟶ C ⟶ A[1]` be a distinguished triangle in `D(𝒪_Y)` with `A` and `C`
isomorphic to finite locally free modules of rank `< a` and `< c` placed in degree `0`. Then `B`
is isomorphic to a finite locally free module of rank `< a + c - 1` placed in degree `0`.

The cohomology sequence gives `H^n(B) = 0` for `n ≠ 0` and a short exact sequence
`0 ⟶ H^0(A) ⟶ H^0(B) ⟶ H^0(C) ⟶ 0`; at each point its stalks split, so the cohomology stalks of
the perfect object `B` are finite free with fibre ranks `r_A + r_C ≤ (a - 1) + (c - 1)`, and
`Stacks.Chow.exists_opens_iso_singleFunctor_isFiniteLocallyFreeOfRankLT` applies on all of `Y`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_iso_obj₂ (T : Triangle (DerivedCategory Y.Modules)) (hT
    : T ∈ distTriang _) {a c : ℕ}
    (h₁ : ∃ M : Y.Modules, IsFiniteLocallyFreeOfRankLT M a ∧
      Nonempty (T.obj₁ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (h₃ : ∃ M : Y.Modules, IsFiniteLocallyFreeOfRankLT M c ∧
      Nonempty (T.obj₃ ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ M : Y.Modules, IsFiniteLocallyFreeOfRankLT M (a + c - 1) ∧
      Nonempty (T.obj₂ ≅ (DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨M₁, hM₁, ⟨e₁⟩⟩ := h₁
  obtain ⟨M₃, hM₃, ⟨e₃⟩⟩ := h₃
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M₁ := hM₁.1
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} M₃ := hM₃.1
  have hz₁ : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor Y.Modules n).obj T.obj₁) :=
    fun n hn => (Scheme.Modules.isZero_homologyFunctor_singleFunctor_obj M₁ hn).of_iso
      ((DerivedCategory.homologyFunctor Y.Modules n).mapIso e₁)
  have hz₃ : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor Y.Modules n).obj T.obj₃) :=
    fun n hn => (Scheme.Modules.isZero_homologyFunctor_singleFunctor_obj M₃ hn).of_iso
      ((DerivedCategory.homologyFunctor Y.Modules n).mapIso e₃)
  have hz₂ : ∀ n : ℤ, n ≠ 0 → IsZero ((DerivedCategory.homologyFunctor Y.Modules n).obj T.obj₂) :=
    fun n hn => (DerivedCategory.HomologySequence.exact₂ T hT n).isZero_of_both_isZero
      (hz₁ n hn) (hz₃ n hn)
  let S := ShortComplex.mk ((DerivedCategory.homologyFunctor Y.Modules 0).map T.mor₁)
    ((DerivedCategory.homologyFunctor Y.Modules 0).map T.mor₂)
    (by simp only [← Functor.map_comp, comp_distTriang_mor_zero₁₂ _ hT, Functor.map_zero])
  have hS : S.ShortExact :=
    { exact := DerivedCategory.HomologySequence.exact₂ T hT 0
      mono_f := (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff T hT (-1) 0).2
        ((hz₃ (-1) (by omega)).eq_of_src _ _)
      epi_g := (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff T hT 0 1).2
        ((hz₁ 1 (by omega)).eq_of_tgt _ _) }
  have hP₂ : Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) T.obj₂ :=
    Stacks.Cohomology.PerfectComplexTriangles.isPerfect_obj₂_of_distinguished T hT
      (isPerfect_of_iso_singleFunctor M₁ e₁) (isPerfect_of_iso_singleFunctor M₃ e₃)
  let i₁ : S.X₁ ≅ M₁ := (DerivedCategory.homologyFunctor Y.Modules 0).mapIso e₁ ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M₁
  let i₃ : S.X₃ ≅ M₃ := (DerivedCategory.homologyFunctor Y.Modules 0).mapIso e₃ ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso _ 0).app M₃
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₁ :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso i₁.symm
  have : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} S.X₃ :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.of_iso i₃.symm
  have hsub : ∀ (n : ℤ), n ≠ 0 → ∀ x : Y, Subsingleton (ToType (TopCat.Presheaf.stalk
      ((DerivedCategory.homologyFunctor Y.Modules n).obj T.obj₂).val.presheaf x)) :=
    fun n hn x => ModuleCat.subsingleton_of_isZero
      (Functor.map_isZero (Stacks.ModuleSkyscraper.modulesStalkFunctor Y x) (hz₂ n hn))
  have hpt : ∀ x : Y, x ∈ RingedSpace.cohomologyFiniteFreeLocus T.obj₂ ∧
      (∀ n : ℤ, n ≠ 0 → Scheme.Modules.fiberRank
        ((DerivedCategory.homologyFunctor Y.Modules n).obj T.obj₂) x = 0) ∧
      Scheme.Modules.fiberRank ((DerivedCategory.homologyFunctor Y.Modules 0).obj T.obj₂) x <
        a + c - 1 := by
    intro x
    obtain ⟨⟨hfree, hfin⟩, hrank⟩ := free_stalk_and_fiberRank_add_of_shortExact S hS x
      (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree S.X₁ x)
      (Stacks.StalkFreeBridge.freeAndFinite_stalk_of_isFiniteLocallyFree S.X₃ x)
    refine ⟨fun n => ?_, fun n hn =>
      Scheme.Modules.fiberRank_eq_zero_of_subsingleton_stalk _ _ (hsub n hn x), ?_⟩
    · by_cases hn : n = 0
      · subst hn
        exact ⟨hfree, hfin⟩
      · have h' := hsub n hn x
        refine ⟨@Module.Free.of_subsingleton _ _ _ _ _ h', ⟨⟨∅, top_unique fun m _ => ?_⟩⟩⟩
        rw [@Subsingleton.elim _ h' m 0]
        exact Submodule.zero_mem _
    · have h₁ := hM₁.fiberRank_lt x
      have h₃ := hM₃.fiberRank_lt x
      rw [← Scheme.Modules.fiberRank_eq_of_iso i₁ x] at h₁
      rw [← Scheme.Modules.fiberRank_eq_of_iso i₃ x] at h₃
      change Scheme.Modules.fiberRank S.X₂ x < a + c - 1
      omega
  obtain ⟨U, hU, M, hM, ⟨e⟩⟩ :=
    exists_opens_iso_singleFunctor_isFiniteLocallyFreeOfRankLT T.obj₂ hP₂ (a + c - 1)
  have hUtop : Set.range (𝟙 Y : Y ⟶ Y) ⊆ Set.range U.ι := by
    rintro _ ⟨x, rfl⟩
    refine ⟨⟨x, hU x (hpt x).1 (hpt x).2.1 (hpt x).2.2⟩, rfl⟩
  obtain ⟨M', hM', ⟨e'⟩⟩ := exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_factors
    (IsOpenImmersion.lift_fac U.ι (𝟙 Y) hUtop) ⟨M, hM, ⟨e⟩⟩
  refine ⟨M', hM', ⟨?_ ≪≫ e'⟩⟩
  exact ((Cohomology.DerivedPullbackAlongIso.derivedPullbackIdIso Y.toRingedSpace).app
    T.obj₂).symm

/-- **The middle vertex of a distinguished triangle, after restriction.** Let
`A ⟶ B ⟶ C ⟶ A[1]` be distinguished in `D(𝒪_Y)` and let `j : W ⟶ Y` be a morphism of schemes
(for instance the inclusion of the complement of a closed subscheme). If `Lj^*A` and `Lj^*C` are
finite locally free modules of rank `< a` and `< c` placed in degree `0`, then so is `Lj^*B`,
of rank `< a + c - 1`: `Lj^*` is exact, and
`Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_iso_obj₂` applies on `W`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_derivedPullback_obj₂ {W : Scheme.{u}} (j : W ⟶ Y)
    (T : Triangle (DerivedCategory Y.Modules)) (hT : T ∈ distTriang _) {a c : ℕ}
    (h₁ : ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M a ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).obj T.obj₁ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (h₃ : ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M c ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).obj T.obj₃ ≅ (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M (a + c - 1) ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).obj T.obj₂ ≅ (DerivedCategory.singleFunctor _ 0).obj M) :=
  exists_isFiniteLocallyFreeOfRankLT_iso_obj₂ ((schemeDerivedPullback j).mapTriangle.obj T)
    ((schemeDerivedPullback j).map_distinguished T hT) h₁ h₃

/-- The zero case of `Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_obj₂`: if
`Lj^*A` and `Lj^*C` are zero, so is `Lj^*B`. -/
theorem isZero_derivedPullback_obj₂ {W : Scheme.{u}} (j : W ⟶ Y)
    (T : Triangle (DerivedCategory Y.Modules)) (hT : T ∈ distTriang _)
    (h₁ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      j.toLRSHom.toShHom).obj T.obj₁))
    (h₃ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      j.toLRSHom.toShHom).obj T.obj₃)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      j.toLRSHom.toShHom).obj T.obj₂) :=
  Triangle.isZero₂_of_isZero₁₃ _ ((schemeDerivedPullback j).map_distinguished T hT) h₁ h₃

/-- **The restriction of a mapping cone.** For a map of complexes `ψ : K ⟶ L` on `Y` and
`j : W ⟶ Y`, if `Lj^*L` and `Lj^*(K[1])` are finite locally free modules of rank `< a` and `< c`
placed in degree `0`, then so is the restriction of the mapping cone of `ψ`, of rank
`< a + c - 1`: it is the middle vertex of the rotated triangle `L ⟶ C(ψ) ⟶ K[1] ⟶ L[1]`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_derivedPullback_mappingCone {W : Scheme.{u}}
    (j : W ⟶ Y) {K L : CochainComplex Y.Modules ℤ} (ψ : K ⟶ L) {a c : ℕ}
    (hL : ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M a ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).obj (DerivedCategory.Q.obj L) ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (hK : ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M c ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).obj (DerivedCategory.Q.obj
          ((shiftFunctor (CochainComplex Y.Modules ℤ) (1 : ℤ)).obj K)) ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M (a + c - 1) ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).obj (DerivedCategory.Q.obj (CochainComplex.mappingCone (C :=
            Y.Modules) ψ)) ≅
          (DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨M, hM, ⟨e⟩⟩ := hK
  exact exists_isFiniteLocallyFreeOfRankLT_derivedPullback_obj₂ j _
    (rot_of_distTriang _ (DerivedCategory.mappingCone_triangle_distinguished ψ)) hL
    ⟨M, hM, ⟨(Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      j.toLRSHom.toShHom).mapIso ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app K).symm ≪≫ e⟩⟩

/-- The zero case of
`Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_mappingCone`. -/
theorem isZero_derivedPullback_mappingCone {W : Scheme.{u}} (j : W ⟶ Y)
    {K L : CochainComplex Y.Modules ℤ} (ψ : K ⟶ L)
    (hL : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      j.toLRSHom.toShHom).obj (DerivedCategory.Q.obj L)))
    (hK : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      j.toLRSHom.toShHom).obj (DerivedCategory.Q.obj
        ((shiftFunctor (CochainComplex Y.Modules ℤ) (1 : ℤ)).obj K)))) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      j.toLRSHom.toShHom).obj (DerivedCategory.Q.obj (CochainComplex.mappingCone (C := Y.Modules)
          ψ))) :=
  isZero_derivedPullback_obj₂ j _
    (rot_of_distTriang _ (DerivedCategory.mappingCone_triangle_distinguished ψ)) hL
    (hK.of_iso ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      j.toLRSHom.toShHom).mapIso ((DerivedCategory.Q.commShiftIso (1 : ℤ)).app K).symm))

end Triangle

/-! ### Sections presented as divisors -/

namespace SectionDivisor

variable {V X : Scheme.{u}} {π : V ⟶ X}

/-- If the ideal sheaf `J` is the kernel of a closed immersion `σ` that is a section of `π`, then
`J ⟶ V ⟶ X` is an isomorphism. -/
theorem isIso_subschemeι_comp_of_eq_ker (σ : X ⟶ V) [IsClosedImmersion σ] (hσ : σ ≫ π = 𝟙 X)
    {J : V.IdealSheafData} (hJ : J = σ.ker) : IsIso (J.subschemeι ≫ π) := by
  subst hJ
  have h : σ.toImage ≫ (σ.imageι ≫ π) = 𝟙 X := by
    rw [← Category.assoc, Scheme.Hom.toImage_imageι, hσ]
  rw [← IsIso.inv_eq_of_hom_inv_id h]
  infer_instance

/-- If the ideal sheaf `J` is the kernel of a closed immersion `σ` that is a section of `π`, then
the inverse of `J ⟶ V ⟶ X` followed by `J ⟶ V` is `σ`. -/
theorem inv_comp_subschemeι_of_eq_ker (σ : X ⟶ V) [IsClosedImmersion σ] (hσ : σ ≫ π = 𝟙 X)
    {J : V.IdealSheafData} (hJ : J = σ.ker) [IsIso (J.subschemeι ≫ π)] :
    inv (J.subschemeι ≫ π) ≫ J.subschemeι = σ := by
  subst hJ
  rw [IsIso.inv_comp_eq, ← cancel_epi σ.toImage, Scheme.Hom.toImage_imageι, ← Category.assoc,
    ← Category.assoc, Scheme.Hom.toImage_imageι, hσ, Category.id_comp]

/-- **The divisor of a section that is cut out by a section of an invertible module.** Let
`σ : X ⟶ V` be a closed immersion and a section of `π`, and let `s` be a global section of an
invertible module `L` on `V` whose zero scheme is the image of `σ` and is an effective Cartier
divisor. -/
def ofSection (L : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (σ : X ⟶ V) [IsClosedImmersion σ] (hσ : σ ≫ π = 𝟙 X)
    (hL : Stacks.Divisors.zeroScheme V L s = σ.ker)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme V L s)) :
    SectionDivisor π where
  L := L
  s := s
  isEffectiveCartierDivisor := hD
  isIso := isIso_subschemeι_comp_of_eq_ker σ hσ hL

/-- The section of `Stacks.Chow.SectionDivisor.ofSection` is the given section. -/
@[simp]
theorem ofSection_section (L : V.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible V.sheaf.obj V.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) (σ : X ⟶ V) [IsClosedImmersion σ] (hσ : σ ≫ π = 𝟙 X)
    (hL : Stacks.Divisors.zeroScheme V L s = σ.ker)
    (hD : Stacks.Divisors.IsEffectiveCartierDivisor (Stacks.Divisors.zeroScheme V L s)) :
    (ofSection L s σ hσ hL hD).section = σ :=
  have := isIso_subschemeι_comp_of_eq_ker σ hσ hL
  inv_comp_subschemeι_of_eq_ker σ hσ hL

end SectionDivisor

/-! ### The points `0` and `1` of the affine line -/

section AffineLinePoints

variable (Y : Scheme.{u})

/-- **The point `0` of `𝐀¹_Y` as a divisor**: the zero scheme of the canonical section of
`𝒪(D₀)` pulled back to the affine chart, whose section is the zero section of `𝐀¹_Y`. -/
def affineLineZeroDivisor : SectionDivisor (affineLineOverHom Y) :=
  SectionDivisor.ofSection (lineZeroModule (affineChart Y)) (lineZeroModuleSection (affineChart Y))
    (affineLineConstantSection Y integralAffineZeroSection)
    (affineLineConstantSection_comp_fst Y integralAffineZeroSection)
    ((zeroScheme_lineZeroModuleSection _).trans (comap_lineZeroDivisor_affineChart Y))
    (by
      rw [zeroScheme_lineZeroModuleSection]
      exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
        (lineZeroDivisor_isEffectiveCartierDivisor Y) _)

/-- The section of the point `0` of `𝐀¹_Y` is the zero section. -/
@[simp]
theorem affineLineZeroDivisor_section :
    (affineLineZeroDivisor Y).section = affineLineConstantSection Y integralAffineZeroSection :=
  SectionDivisor.ofSection_section _ _ _ _ _ _

/-- The section of `𝐀¹_Y` at a global function is a closed immersion: it is the zero section
followed by a translation. -/
instance isClosedImmersion_affineLineSection (t : Γ(Y, ⊤)) :
    IsClosedImmersion (affineLineSection Y t) := by
  rw [affineLineSection]
  infer_instance

/-- The section of `𝐀¹_Y` at `t` cuts out the inverse image of the zero section under the
translation by `t`. -/
theorem ker_affineLineSection (t : Γ(Y, ⊤)) :
    (affineLineSection Y t).ker =
      (affineLineConstantSection Y integralAffineZeroSection).ker.comap
        (inv (affineTranslation Y t)) := by
  refine AlgebraicGeometry.ker_eq_comap_ker_of_isPullback
    (b := 𝟙 Y) (i := affineLineConstantSection Y integralAffineZeroSection)
    (IsPullback.of_vert_isIso_mono ⟨?_⟩)
  rw [Category.id_comp, affineLineSection, Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The invertible module of the point `t` of `𝐀¹_Y`: the module of the point `0` pulled back
along the inverse of the translation by `t`. -/
abbrev affineLinePointModule (t : Γ(Y, ⊤)) : (affineLineOver Y).Modules :=
  (Scheme.Modules.pullback (inv (affineTranslation Y t))).obj (affineLineZeroDivisor Y).L

/-- The module of the point `t` of `𝐀¹_Y` is invertible. -/
instance (t : Γ(Y, ⊤)) :
    AlgebraicGeometry.SheafOfModules.IsInvertible (affineLineOver Y).sheaf.obj
      (affineLineOver Y).ringCatSheaf.property (affineLinePointModule Y t) :=
  Stacks.ChernCap42.isInvertible_sheafObj_modulePullback _ _

/-- **The point `t` of `𝐀¹_Y` as a divisor**: the translate by `t` of the point `0`, whose
section is the section of `𝐀¹_Y` at `t`. -/
def affineLinePointDivisor (t : Γ(Y, ⊤)) : SectionDivisor (affineLineOverHom Y) :=
  SectionDivisor.ofSection (affineLinePointModule Y t)
    (AlgebraicGeometry.pullbackGlobalSections (inv (affineTranslation Y t))
      (affineLineZeroDivisor Y).L (affineLineZeroDivisor Y).s)
    (affineLineSection Y t) (affineLineSection_comp Y t)
    ((Stacks.Divisors.zeroScheme_pullback _ _ _).trans
      ((congrArg (fun J => Scheme.IdealSheafData.comap J (inv (affineTranslation Y t)))
        ((zeroScheme_lineZeroModuleSection _).trans (comap_lineZeroDivisor_affineChart Y))).trans
        (ker_affineLineSection Y t).symm))
    (by
      rw [Stacks.Divisors.zeroScheme_pullback]
      exact Stacks.Blowup.isEffectiveCartierDivisor_comap_of_isOpenImmersion _
        (affineLineZeroDivisor Y).isEffectiveCartierDivisor _)

/-- The section of the point `t` of `𝐀¹_Y` is the section of `𝐀¹_Y` at `t`. -/
@[simp]
theorem affineLinePointDivisor_section (t : Γ(Y, ⊤)) :
    (affineLinePointDivisor Y t).section = affineLineSection Y t :=
  SectionDivisor.ofSection_section _ _ _ _ _ _

end AffineLinePoints

/-! ### The restriction of a class along the section of a divisor -/

section SectionRestriction

variable {X Z Z' V : Scheme.{u}} {π : V ⟶ X} {z : Z ⟶ X} {z' : Z' ⟶ V} {zf : Z' ⟶ Z}
  (sqZ : IsPullback zf z' z π) (C : ChowSituation.{u}) (f : X ⟶ C.S) [LocallyOfFiniteType f]
  [LocallyOfFiniteType π] [Flat π] [LocallyOfFiniteType z] [LocallyOfFiniteType z'] {p : ℤ}

/-- **The base change of `Z' ⟶ V` along the section of a divisor is `Z`.** -/
def SectionDivisor.sectionIso (D : SectionDivisor π) : pullback z' D.section ≅ Z :=
  testIso sqZ (IsPullback.id_horiz z) D.section D.section_comp

omit [LocallyOfFiniteType π] [Flat π] [LocallyOfFiniteType z] [LocallyOfFiniteType z'] in
/-- The identification `Stacks.Chow.SectionDivisor.sectionIso` lies over `X`. -/
@[reassoc (attr := simp)]
theorem SectionDivisor.sectionIso_hom_comp (D : SectionDivisor π) :
    (D.sectionIso sqZ).hom ≫ z = pullback.snd z' D.section :=
  testIso_hom_snd _ _ _ _

omit [LocallyOfFiniteType π] [Flat π] [LocallyOfFiniteType z] [LocallyOfFiniteType z'] in
/-- The identification `Stacks.Chow.SectionDivisor.sectionIso` is the first projection followed
by `Z' ⟶ Z`. -/
@[reassoc (attr := simp)]
theorem SectionDivisor.sectionIso_hom (D : SectionDivisor π) :
    (D.sectionIso sqZ).hom = pullback.fst z' D.section ≫ zf :=
  (Category.comp_id _).symm.trans (testIso_hom_fst _ _ _ _)

/-- **The restriction of a bivariant class on `V` along the section of a divisor**, read as a
class for `z : Z ⟶ X`: the restriction (Remark 0F9Z) along `σ : X ⟶ V`, transported along the
identification of `Z' ×_V X` with `Z`. This is `i_σ^* ∘ c` in the proof of Stacks 0FBD. -/
def SectionDivisor.sectionRestriction (D : SectionDivisor π)
    (c : BivariantClass C (gysinSystemOfInvertible C) (z' ≫ π ≫ f) (π ≫ f) z' rfl p) :
    BivariantClass C (gysinSystemOfInvertible C) (z ≫ f) f z rfl p :=
  bivariantClassCongrBase C (gysinSystemOfInvertible C) z rfl (by simp) (hv := by simp)
    (hv' := rfl) p
    (bivariantTransport C (gysinSystemOfInvertible C) (pullback.fst z' D.section ≫ (z' ≫ π ≫ f))
      (z ≫ f) (D.section ≫ π ≫ f) (pullback.snd z' D.section)
      (pullbackSnd_comp_structureMorphism_eq C (z' ≫ π ≫ f) (π ≫ f) z' rfl D.section) z
      (by simp) (D.sectionIso sqZ) (D.sectionIso_hom_comp sqZ) p
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (bivariantRestriction C (gysinSystemOfInvertible C) (z' ≫ π ≫ f) (π ≫ f) z' rfl D.section
        p (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C) c))

omit [LocallyOfFiniteType π] [Flat π] [LocallyOfFiniteType z] [LocallyOfFiniteType z'] in
include sqZ in
/-- The comparison of base changes behind the cap formula of
`Stacks.Chow.SectionDivisor.sectionRestriction`. -/
theorem SectionDivisor.sectionRestriction_iso_eq (D : SectionDivisor π) {T : Scheme.{u}}
    (g : T ⟶ X) :
    (pullbackLeftPullbackSndIso z' D.section g).inv ≫
        (transportPullbackIso (pullback.snd z' D.section) z (D.sectionIso sqZ)
          (D.sectionIso_hom_comp sqZ) g).hom =
      (testIso sqZ (IsPullback.of_hasPullback z g) (g ≫ D.section) (by simp)).hom := by
  refine pullback.hom_ext ?_ ?_
  · rw [Category.assoc, transportPullbackIso_hom_fst, testIso_hom_fst, sectionIso_hom,
      pullbackLeftPullbackSndIso_inv_fst_assoc]
  · rw [Category.assoc, transportPullbackIso_hom_snd, testIso_hom_snd,
      pullbackLeftPullbackSndIso_inv_snd_snd]

omit [Flat π] in
/-- **The cap formula for the restriction along a section**: on a test scheme `g : T ⟶ X` the
restriction of `c` along the section `σ` caps as `c` along `g ≫ σ`, read on `Z ×_X T`. -/
theorem SectionDivisor.sectionRestriction_cap (D : SectionDivisor π)
    (c : BivariantClass C (gysinSystemOfInvertible C) (z' ≫ π ≫ f) (π ≫ f) z' rfl p)
    {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ) (α : chowGroup C (g ≫ f) k) :
    (D.sectionRestriction sqZ C f c).cap g k α =
      chowPushforwardOfIso C (pullback.fst z' (g ≫ D.section) ≫ (z' ≫ (π ≫ f)))
        (pullback.fst z g ≫ z ≫ f)
        (testIso sqZ (IsPullback.of_hasPullback z g) (g ≫ D.section) (by simp)).hom
        (testIso_base sqZ (IsPullback.of_hasPullback z g) C f D) (k - p)
        (c.cap (g ≫ D.section) k (chowGroupCongr C (by simp) k α)) := by
  have hg : g ≫ f = g ≫ D.section ≫ π ≫ f := by simp
  apply eq_of_heq
  refine (bivariantClassCongrBase_cap C _ z _ _ p _ g k (chowGroupCongr C hg k α) α
    (chowGroupCongr_heq C hg k α)).trans (heq_of_eq ?_)
  rw [bivariantTransport_cap, bivariantTransportCap_apply, bivariantRestriction_cap,
    bivariantRestrictionCap_apply, chowPushforwardOfIso_comp_apply]
  rw [chowPushforwardOfIso_congr_apply C _ _ _ _ (D.sectionRestriction_iso_eq sqZ g)]
  refine congrArg (chowPushforwardOfIso C _ _ _ _ (k - p))
    (congrArg (c.cap (g ≫ D.section) k) ?_)
  exact eq_of_heq ((chowGroupCongr_heq C _ k _).trans ((chowGroupCongr_heq C hg k α).trans
    (chowGroupCongr_heq C _ k α).symm))

include sqZ in
/-- **`i_σ^* = i_σ'^*`** (the proof of Stacks 0FBD, "by definition of rational equivalence"): for
an affine-space bundle `π : V ⟶ X` of rank one and two divisors `D, D'` of `V` mapping
isomorphically to `X`, the restrictions of a bivariant class `c` for `Z' = Z ×_X V ⟶ V` along
their sections agree as classes for `Z ⟶ X`. This is
`Stacks.Chow.SectionDivisor.cap_section_eq` read through the cap formula of
`Stacks.Chow.SectionDivisor.sectionRestriction`. -/
theorem SectionDivisor.sectionRestriction_eq (hπ : AlgebraicGeometry.RelativeDimension π 1)
    (hb : IsAffineSpaceBundle π 1) (D D' : SectionDivisor π)
    (c : BivariantClass C (gysinSystemOfInvertible C) (z' ≫ π ≫ f) (π ≫ f) z' rfl p) :
    D.sectionRestriction sqZ C f c = D'.sectionRestriction sqZ C f c := by
  ext T g _ k α
  rw [D.sectionRestriction_cap sqZ C f c g k α, D'.sectionRestriction_cap sqZ C f c g k α]
  have sqA := IsPullback.of_hasPullback π g
  have sqT := IsPullback.of_hasPullback z g
  have sqM := isPullback_testMap sqZ sqA sqT
  have : LocallyOfFiniteType (testMap sqZ sqA sqT) :=
    MorphismProperty.of_isPullback sqM inferInstance
  have : Flat (testMap sqZ sqA sqT) := MorphismProperty.of_isPullback sqM inferInstance
  exact SectionDivisor.cap_section_eq sqZ sqA sqT C f c D D'
    (RelativeDimension.of_isPullback (IsPullback.of_hasPullback π g) hπ)
    (RelativeDimension.of_isPullback sqM hπ) (isAffineSpaceBundle_of_isPullback sqM hb) k α

end SectionRestriction

/-! ### The deformation cone -/

section DeformationCone

variable {Y : Scheme.{u}} {P₁ P₃ : CochainComplex Y.Modules ℤ}
  (hP₁ : IsLocallyBoundedFiniteLocallyFree P₁) (hP₃ : IsLocallyBoundedFiniteLocallyFree P₃)
  (φ : P₃ ⟶ P₁)

include hP₁ hP₃ in
/-- **The deformation cone is a locally bounded complex of finite locally free modules**: it is
the mapping cone of a map between pullbacks of such complexes. -/
theorem isLocallyBoundedFiniteLocallyFree_deformationCone :
    IsLocallyBoundedFiniteLocallyFree (deformationCone φ) :=
  isLocallyBoundedFiniteLocallyFree_mappingCone _
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ P₃ hP₃)
    (Stacks.BlowUpComplexes.isLocallyBoundedFiniteLocallyFree_pullback _ P₁ hP₁)

include hP₁ in
/-- The pullback of `P₁` to `𝐀¹_Y` computes the derived pullback of `P₁`. -/
def derivedPullbackAffineLineIso₁ :
    DerivedCategory.Q.obj (pullbackComplex (affineLineOverHom Y) P₁) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (affineLineOverHom Y).toLRSHom.toShHom).obj (DerivedCategory.Q.obj P₁) :=
  (Cohomology.derivedPullbackIsoPullbackOfKFlat (affineLineOverHom Y).toLRSHom.toShHom P₁
    (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree P₁ hP₁)).symm

include hP₃ in
/-- The shift of the pullback of `P₃` to `𝐀¹_Y` computes the derived pullback of `P₃[1]`. -/
def derivedPullbackAffineLineIso₃ :
    DerivedCategory.Q.obj ((shiftFunctor (CochainComplex (affineLineOver Y).Modules ℤ) (1 : ℤ)).obj
        (pullbackComplex (affineLineOverHom Y) P₃)) ≅
      (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (affineLineOverHom Y).toLRSHom.toShHom).obj (DerivedCategory.Q.obj
          ((shiftFunctor (CochainComplex Y.Modules ℤ) (1 : ℤ)).obj P₃)) :=
  DerivedCategory.Q.mapIso
      (((Scheme.Modules.pullback (affineLineOverHom Y)).mapCochainComplexShiftIso 1).app P₃).symm ≪≫
    (Cohomology.derivedPullbackIsoPullbackOfKFlat (affineLineOverHom Y).toLRSHom.toShHom _
      (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree _
        (isLocallyBoundedFiniteLocallyFree_shift hP₃ 1))).symm

include hP₁ hP₃ in
/-- **The deformation cone off `𝐀¹_Z`, rank form.** Let `j : W ⟶ Y`, `j' : W' ⟶ 𝐀¹_Y` and
`k : W' ⟶ W` with `k ≫ j = j' ≫ π` (for instance the complements of `Z` and `𝐀¹_Z`). If `Lj^*P₁`
and `Lj^*(P₃[1])` are finite locally free of rank `< a` and `< c` in degree `0`, then the
restriction of the deformation cone along `j'` is finite locally free of rank `< a + c - 1` in
degree `0`: the deformation cone is the mapping cone of `t · π^*φ : π^*P₃ ⟶ π^*P₁`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_derivedPullback_deformationCone {W W' : Scheme.{u}}
    {j : W ⟶ Y} {j' : W' ⟶ affineLineOver Y} {k : W' ⟶ W}
    (hk : k ≫ j = j' ≫ affineLineOverHom Y) {a c : ℕ}
    (h₁ : ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M a ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P₁) ≅
          (DerivedCategory.singleFunctor _ 0).obj M))
    (h₃ : ∃ M : W.Modules, IsFiniteLocallyFreeOfRankLT M c ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).obj (DerivedCategory.Q.obj
          ((shiftFunctor (CochainComplex Y.Modules ℤ) (1 : ℤ)).obj P₃)) ≅
          (DerivedCategory.singleFunctor _ 0).obj M)) :
    ∃ M : W'.Modules, IsFiniteLocallyFreeOfRankLT M (a + c - 1) ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j'.toLRSHom.toShHom).obj (DerivedCategory.Q.obj (deformationCone φ)) ≅
          (DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨M₁, hM₁, ⟨e₁⟩⟩ := exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_comp_eq hk h₁
  obtain ⟨M₃, hM₃, ⟨e₃⟩⟩ := exists_isFiniteLocallyFreeOfRankLT_derivedPullback_of_comp_eq hk h₃
  exact exists_isFiniteLocallyFreeOfRankLT_derivedPullback_mappingCone j' _
    ⟨M₁, hM₁, ⟨(Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      j'.toLRSHom.toShHom).mapIso (derivedPullbackAffineLineIso₁ hP₁) ≪≫ e₁⟩⟩
    ⟨M₃, hM₃, ⟨(Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      j'.toLRSHom.toShHom).mapIso (derivedPullbackAffineLineIso₃ hP₃) ≪≫ e₃⟩⟩

include hP₁ hP₃ in
/-- **The deformation cone off `𝐀¹_Z`, zero form**: as
`Stacks.Chow.exists_isFiniteLocallyFreeOfRankLT_derivedPullback_deformationCone`, if `Lj^*P₁` and
`Lj^*(P₃[1])` are zero, so is the restriction of the deformation cone along `j'`. -/
theorem isZero_derivedPullback_deformationCone {W W' : Scheme.{u}}
    {j : W ⟶ Y} {j' : W' ⟶ affineLineOver Y} {k : W' ⟶ W}
    (hk : k ≫ j = j' ≫ affineLineOverHom Y)
    (h₁ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).obj (DerivedCategory.Q.obj P₁)))
    (h₃ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j.toLRSHom.toShHom).obj (DerivedCategory.Q.obj
          ((shiftFunctor (CochainComplex Y.Modules ℤ) (1 : ℤ)).obj P₃)))) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j'.toLRSHom.toShHom).obj (DerivedCategory.Q.obj (deformationCone φ))) :=
  isZero_derivedPullback_mappingCone j' _
    ((isZero_derivedPullback_of_isZero_of_comp_eq hk h₁).of_iso
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j'.toLRSHom.toShHom).mapIso (derivedPullbackAffineLineIso₁ hP₁)))
    ((isZero_derivedPullback_of_isZero_of_comp_eq hk h₃).of_iso
      ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        j'.toLRSHom.toShHom).mapIso (derivedPullbackAffineLineIso₃ hP₃)))

include hP₁ hP₃ in
/-- **The derived fibre of the deformation cone at a section** `σ` of `𝐀¹_Y ⟶ Y`: it is the
mapping cone of `σ^♯ t · φ`. -/
def derivedPullbackDeformationConeIso (σ : Y ⟶ affineLineOver Y)
    (hσ : σ ≫ affineLineOverHom Y = 𝟙 Y) :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback σ.toLRSHom.toShHom).obj
        (DerivedCategory.Q.obj (deformationCone φ)) ≅
      DerivedCategory.Q.obj (CochainComplex.mappingCone (C := Y.Modules)
        (φ ≫ complexSmul (σ.appTop (affineCoordinate Y)) P₁)) :=
  Cohomology.derivedPullbackIsoPullbackOfKFlat σ.toLRSHom.toShHom _
      (Stacks.BlowUpComplexes.kFlatComplex_of_isLocallyBoundedFiniteLocallyFree _
        (isLocallyBoundedFiniteLocallyFree_deformationCone hP₁ hP₃ φ)) ≪≫
    DerivedCategory.Q.mapIso
      (pullbackComplexMappingConeSmulIso σ (affineLineOverHom Y) hσ φ (affineCoordinate Y))

end DeformationCone

/-! ### The situation on the affine line -/

/-- An object of `D(𝒪_X)` represented by a locally bounded complex of finite locally free
modules is perfect. -/
theorem isPerfect_of_iso_Q_obj {Y : Scheme.{u}} {P : CochainComplex Y.Modules ℤ}
    (hP : IsLocallyBoundedFiniteLocallyFree P) {E : DerivedCategory Y.Modules}
    (e : E ≅ DerivedCategory.Q.obj P) :
    Cohomology.PerfectComplexes.IsPerfect (X := Y.toRingedSpace) E :=
  ⟨P, Stacks.BlowUpComplexes.isPerfectComplex_of_isLocallyBoundedFiniteLocallyFree P hP,
    ⟨e.symm⟩⟩

namespace LocalizedChernData

variable (D : LocalizedChernData.{u})

/-- The second alternative of condition (2) for the data `D` with its object replaced by `E`,
in terms of `E`. -/
theorem isFiniteLocallyFreeOfRankLTOnComplement_update_iff
    (E : DerivedCategory (OXMod.{u, u, u} D.X.toRingedSpace))
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E)
        {hres : letI U : TopologicalSpace.Opens D.X :=
        ⟨(Set.range D.i.base)ᶜ, D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      letI F := Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (D.X.toRingedSpace.ofRestrict U.isOpenEmbedding)
      IsZero (F.obj E) ∨
        ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict U.isOpenEmbedding),
          IsFiniteLocallyFreeOfRankLT M D.p ∧
            Nonempty (F.obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M)} :
    ({ D with E := E, perfect := hE, restriction := hres } :
        LocalizedChernData).IsFiniteLocallyFreeOfRankLTOnComplement ↔
      (∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M D.p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
              D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
                  D.X.Opens).isOpenEmbedding)).obj E ≅
            (DerivedCategory.singleFunctor _ 0).obj M)) :=
  Iff.rfl

/-- The first alternative of condition (2) for the data `D` with its object replaced by `E`, in
terms of `E`. -/
theorem isZeroOnComplement_update_iff
    (E : DerivedCategory (OXMod.{u, u, u} D.X.toRingedSpace))
    (hE : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E)
        {hres : letI U : TopologicalSpace.Opens D.X :=
        ⟨(Set.range D.i.base)ᶜ, D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      letI F := Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (D.X.toRingedSpace.ofRestrict U.isOpenEmbedding)
      IsZero (F.obj E) ∨
        ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict U.isOpenEmbedding),
          IsFiniteLocallyFreeOfRankLT M D.p ∧
            Nonempty (F.obj E ≅ (DerivedCategory.singleFunctor _ 0).obj M)} :
    ({ D with E := E, perfect := hE, restriction := hres } :
        LocalizedChernData).IsZeroOnComplement ↔ IsZero
            ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E)
              :=
  Iff.rfl

/-- The complement of `𝐀¹_Z` in `𝐀¹_X`. -/
abbrev deformationComplement : (affineLineOver D.X).Opens :=
  ⟨(Set.range (Limits.pullback.snd D.i (affineLineOverHom D.X)).base)ᶜ,
    (Limits.pullback.snd D.i (affineLineOverHom D.X)).isClosedEmbedding.isClosed_range.isOpen_compl⟩

variable {P₁ P₃ : CochainComplex D.X.Modules ℤ}
  (hP₁ : IsLocallyBoundedFiniteLocallyFree P₁) (hP₃ : IsLocallyBoundedFiniteLocallyFree P₃)
  (φ : P₃ ⟶ P₁)

/-- **The situation of the deformation**: on `X' = 𝐀¹_X` with `Z' = 𝐀¹_Z`, the deformation cone
`C` of `φ` (the mapping cone of `t · π^*φ`), in the degree of `D`. It is an instance of
Situation 0GUJ through alternative (c) of its condition (3), `C` being a locally bounded complex
of finite locally free modules; condition (2) is the hypothesis `hres`. -/
abbrev deformationSituation
    (hres : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        D.deformationComplement.ι.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj (deformationCone φ))) ∨
      ∃ M : D.deformationComplement.toScheme.Modules, IsFiniteLocallyFreeOfRankLT M D.p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          D.deformationComplement.ι.toLRSHom.toShHom).obj
            (DerivedCategory.Q.obj (deformationCone φ)) ≅
              (DerivedCategory.singleFunctor _ 0).obj M)) :
    LocalizedSituation.{u} where
  base := D.base
  X := affineLineOver D.X
  a := affineLineOverHom D.X ≫ D.a
  Z := Limits.pullback D.i (affineLineOverHom D.X)
  i := Limits.pullback.snd D.i (affineLineOverHom D.X)
  E := DerivedCategory.Q.obj (deformationCone φ)
  p := D.p
  perfect := isPerfect_of_iso_Q_obj (isLocallyBoundedFiniteLocallyFree_deformationCone hP₁ hP₃ φ)
    (Iso.refl _)
  restriction := hres
  finiteness := Or.inr (Or.inr (Or.inl ⟨deformationCone φ,
    isLocallyBoundedFiniteLocallyFree_deformationCone hP₁ hP₃ φ, ⟨Iso.refl _⟩⟩))

/-- The second alternative of condition (2) for the situation of the deformation. -/
theorem deformationSituation_isFiniteLocallyFreeOfRankLTOnComplement_iff (hres : IsZero
    ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        D.deformationComplement.ι.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj (deformationCone φ))) ∨
      (∃ M : D.deformationComplement.toScheme.Modules, IsFiniteLocallyFreeOfRankLT M D.p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          D.deformationComplement.ι.toLRSHom.toShHom).obj
            (DerivedCategory.Q.obj (deformationCone φ)) ≅
              (DerivedCategory.singleFunctor _ 0).obj M))) :
    (D.deformationSituation hP₁ hP₃ φ hres).IsFiniteLocallyFreeOfRankLTOnComplement ↔
      (∃ M : D.deformationComplement.toScheme.Modules, IsFiniteLocallyFreeOfRankLT M D.p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          D.deformationComplement.ι.toLRSHom.toShHom).obj
            (DerivedCategory.Q.obj (deformationCone φ)) ≅
              (DerivedCategory.singleFunctor _ 0).obj M)) :=
  Iff.rfl

/-- The first alternative of condition (2) for the situation of the deformation. -/
theorem deformationSituation_isZeroOnComplement_iff (hres : IsZero
    ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        D.deformationComplement.ι.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj (deformationCone φ))) ∨
      (∃ M : D.deformationComplement.toScheme.Modules, IsFiniteLocallyFreeOfRankLT M D.p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          D.deformationComplement.ι.toLRSHom.toShHom).obj
            (DerivedCategory.Q.obj (deformationCone φ)) ≅
              (DerivedCategory.singleFunctor _ 0).obj M))) :
    (D.deformationSituation hP₁ hP₃ φ hres).IsZeroOnComplement ↔ IsZero
        ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        D.deformationComplement.ι.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj (deformationCone φ))) :=
  Iff.rfl

variable {D hP₁ hP₃ φ} in
/-- **Stacks 0FB3 along a section of the affine line, for `c_p`.** Let `D'` be a divisor of
`𝐀¹_X` mapping isomorphically to `X`, with section `σ`, and suppose the derived fibre `Lσ^*C` of
the deformation cone is `E`. Then the restriction along `σ` of the class `c_p(𝐀¹_Z ⟶ 𝐀¹_X, C)`,
read on `Z`, is `c_p(Z ⟶ X, E)`. -/
theorem sectionRestriction_localizedChern_deformationSituation
    {hres : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        D.deformationComplement.ι.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj (deformationCone φ))) ∨
      ∃ M : D.deformationComplement.toScheme.Modules, IsFiniteLocallyFreeOfRankLT M D.p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          D.deformationComplement.ι.toLRSHom.toShHom).obj
            (DerivedCategory.Q.obj (deformationCone φ)) ≅
              (DerivedCategory.singleFunctor _ 0).obj M)}
    (h' : (D.deformationSituation hP₁ hP₃ φ hres).IsFiniteLocallyFreeOfRankLTOnComplement)
    (D' : SectionDivisor (affineLineOverHom D.X))
    (hc : ∃ P : CochainComplex (OXMod.{u, u, u} D.X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ D.E))
    (e : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        D'.section.toLRSHom.toShHom).obj (DerivedCategory.Q.obj (deformationCone φ)) ≅ D.E)
    (h : (D.toSituation hc).IsFiniteLocallyFreeOfRankLTOnComplement) :
    D'.sectionRestriction (IsPullback.of_hasPullback D.i (affineLineOverHom D.X)) D.base D.a
        ((D.deformationSituation hP₁ hP₃ φ hres).localizedChern h') =
      (D.toSituation hc).localizedChern h := by
  let S' := D.deformationSituation hP₁ hP₃ φ hres
  let T := D.toSituation hc
  have key := bivariantTransport_bivariantRestriction_graphChernClass_of_eq (C := S'.base)
    (a := S'.a) (h := D'.section) (E := S'.E) (hE := S'.perfect) (E' := T.E) (hE' := T.perfect)
    (e := e) (z := S'.i) (z' := T.i)
    (θ := D'.sectionIso (IsPullback.of_hasPullback D.i (affineLineOverHom D.X)))
    (hθ := D'.sectionIso_hom_comp (IsPullback.of_hasPullback D.i (affineLineOverHom D.X)))
    (t := S'.graphSubschemeι) (hH := S'.isFiniteLocallyFree_graphObjectRestrictHomology)
    (hQ := S'.hasDefinedChernClasses_graphObject) (p := S'.p) (hT := S'.mem_range_graphSubschemeι)
    (hz := rfl) (a' := T.a) (ha' := by simp [S', T]) (hsB := rfl) (t'' := T.graphSubschemeι)
    (hH'' := T.isFiniteLocallyFree_graphObjectRestrictHomology)
    (hQ'' := T.hasDefinedChernClasses_graphObject) (hT'' := T.mem_range_graphSubschemeι)
    (hrk := S'.finiteLocallyFreeRank_graphSubscheme_lt h')
    (hrk'' := T.finiteLocallyFreeRank_graphSubscheme_lt h)
  exact eq_of_heq ((bivariantClassCongrBase_heq _ _ _ _ _).trans
    ((heq_of_eq key).trans (bivariantClassCongrBase_heq _ _ _ _ _)))

variable {D hP₁ hP₃ φ} in
/-- **Stacks 0FB3 along a section of the affine line, for `P_p`.** Let `D'` be a divisor of
`𝐀¹_X` mapping isomorphically to `X`, with section `σ`, and suppose the derived fibre `Lσ^*C` of
the deformation cone is `E`. Then the restriction along `σ` of the class `P_p(𝐀¹_Z ⟶ 𝐀¹_X, C)`,
read on `Z`, is `P_p(Z ⟶ X, E)`. -/
theorem sectionRestriction_localizedPowerSum_deformationSituation
    {hres : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        D.deformationComplement.ι.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj (deformationCone φ))) ∨
      ∃ M : D.deformationComplement.toScheme.Modules, IsFiniteLocallyFreeOfRankLT M D.p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          D.deformationComplement.ι.toLRSHom.toShHom).obj
            (DerivedCategory.Q.obj (deformationCone φ)) ≅
              (DerivedCategory.singleFunctor _ 0).obj M)}
    (h' : (D.deformationSituation hP₁ hP₃ φ hres).IsZeroOnComplement) (q : ℕ)
    (D' : SectionDivisor (affineLineOverHom D.X))
    (hc : ∃ P : CochainComplex (OXMod.{u, u, u} D.X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ D.E))
    (e : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        D'.section.toLRSHom.toShHom).obj (DerivedCategory.Q.obj (deformationCone φ)) ≅ D.E)
    (h : (D.toSituation hc).IsZeroOnComplement) :
    D'.sectionRestriction (IsPullback.of_hasPullback D.i (affineLineOverHom D.X)) D.base D.a
        ((D.deformationSituation hP₁ hP₃ φ hres).localizedPowerSum h' q) =
      (D.toSituation hc).localizedPowerSum h q := by
  let S' := D.deformationSituation hP₁ hP₃ φ hres
  let T := D.toSituation hc
  have key := bivariantTransport_bivariantRestriction_graphPowerSumClass_of_eq (C := S'.base)
    (a := S'.a) (h := D'.section) (E := S'.E) (hE := S'.perfect) (E' := T.E) (hE' := T.perfect)
    (e := e) (z := S'.i) (z' := T.i)
    (θ := D'.sectionIso (IsPullback.of_hasPullback D.i (affineLineOverHom D.X)))
    (hθ := D'.sectionIso_hom_comp (IsPullback.of_hasPullback D.i (affineLineOverHom D.X)))
    (t := S'.graphSubschemeι) (hH := S'.isFiniteLocallyFree_graphObjectRestrictHomology)
    (hQ := S'.hasDefinedChernClasses_graphObject) (p := q) (hT := S'.mem_range_graphSubschemeι)
    (hz := rfl) (a' := T.a) (ha' := by simp [S', T]) (hsB := rfl) (t'' := T.graphSubschemeι)
    (hH'' := T.isFiniteLocallyFree_graphObjectRestrictHomology)
    (hQ'' := T.hasDefinedChernClasses_graphObject) (hT'' := T.mem_range_graphSubschemeι)
    (hrk := S'.finiteLocallyFreeRank_graphSubscheme_eq_zero h')
    (hrk'' := T.finiteLocallyFreeRank_graphSubscheme_eq_zero h)
  exact eq_of_heq ((bivariantClassCongrBase_heq _ _ _ _ _).trans
    ((heq_of_eq key).trans (bivariantClassCongrBase_heq _ _ _ _ _)))

/-! ### The restrictions to the complements -/

section Restrictions

variable {D}

include hP₁ hP₃ in
/-- **The deformation cone off `𝐀¹_Z`, rank form**: if `P₁|_{X ∖ Z}` and `P₃[1]|_{X ∖ Z}` are
finite locally free of rank `< p₁` and `< p₃` in degree `0`, and `p₁ + p₃ ≤ p + 1`, then the
deformation cone is finite locally free of rank `< p` in degree `0` off `𝐀¹_Z`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_deformationCone {p₁ p₃ : ℕ}
    (h₁ : (∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₁ ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
              D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
                  D.X.Opens).isOpenEmbedding)).obj (DerivedCategory.Q.obj P₁) ≅
            (DerivedCategory.singleFunctor _ 0).obj M)))
    (h₃ : (∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₃ ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
              D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
                  D.X.Opens).isOpenEmbedding)).obj (DerivedCategory.Q.obj ((shiftFunctor
                      (CochainComplex D.X.Modules ℤ) (1 : ℤ)).obj P₃)) ≅
            (DerivedCategory.singleFunctor _ 0).obj M)))
    (hp : p₁ + p₃ ≤ D.p + 1) :
    ∃ M : D.deformationComplement.toScheme.Modules, IsFiniteLocallyFreeOfRankLT M D.p ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        D.deformationComplement.ι.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj (deformationCone φ)) ≅
            (DerivedCategory.singleFunctor _ 0).obj M) := by
  obtain ⟨M, hM, he⟩ := exists_isFiniteLocallyFreeOfRankLT_derivedPullback_deformationCone hP₁ hP₃
    φ (j := Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens))
    (IsOpenImmersion.lift_fac _ _ (D.range_compl_pullbackSnd_subset (affineLineOverHom D.X))) h₁ h₃
  exact ⟨M, hM.mono (by omega), he⟩

include hP₁ hP₃ in
/-- **The deformation cone off `𝐀¹_Z`, zero form**: if `P₁|_{X ∖ Z}` and `P₃[1]|_{X ∖ Z}` are
zero, so is the deformation cone off `𝐀¹_Z`. -/
theorem isZero_deformationCone
    (h₁ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj
              (DerivedCategory.Q.obj P₁)))
    (h₃ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj
              (DerivedCategory.Q.obj ((shiftFunctor (CochainComplex D.X.Modules ℤ) (1 : ℤ)).obj
                  P₃)))) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        D.deformationComplement.ι.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj (deformationCone φ))) :=
  isZero_derivedPullback_deformationCone hP₁ hP₃ φ (j := Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens))
    (IsOpenImmersion.lift_fac _ _ (D.range_compl_pullbackSnd_subset (affineLineOverHom D.X))) h₁ h₃

variable (D) in
/-- **The statement of Stacks 0FBD makes sense, for a mapping cone**: if `P₁|_{X ∖ Z}` and
`P₃[1]|_{X ∖ Z}` are finite locally free of rank `< p₁` and `< p₃` in degree `0` and
`p₁ + p₃ ≤ p + 1`, then every object isomorphic to the mapping cone of a map `ψ : P₃ ⟶ P₁` is,
off `Z`, finite locally free of rank `< p` in degree `0`. -/
theorem exists_isFiniteLocallyFreeOfRankLT_of_iso_mappingCone (ψ : P₃ ⟶ P₁) {p₁ p₃ : ℕ}
    (h₁ : (∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₁ ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
              D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
                  D.X.Opens).isOpenEmbedding)).obj (DerivedCategory.Q.obj P₁) ≅
            (DerivedCategory.singleFunctor _ 0).obj M)))
    (h₃ : (∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₃ ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
              D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
                  D.X.Opens).isOpenEmbedding)).obj (DerivedCategory.Q.obj ((shiftFunctor
                      (CochainComplex D.X.Modules ℤ) (1 : ℤ)).obj P₃)) ≅
            (DerivedCategory.singleFunctor _ 0).obj M)))
    (hp : p₁ + p₃ ≤ D.p + 1) {E : DerivedCategory (OXMod.{u, u, u} D.X.toRingedSpace)}
    (e : E ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules) ψ)) :
    (∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M D.p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
              D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
                  D.X.Opens).isOpenEmbedding)).obj E ≅
            (DerivedCategory.singleFunctor _ 0).obj M)) := by
  have h₁' : ∃ M : (Scheme.Opens.toScheme (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)).Modules,
          IsFiniteLocallyFreeOfRankLT M p₁ ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
            D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)).toLRSHom.toShHom).obj
                (DerivedCategory.Q.obj P₁) ≅
          (DerivedCategory.singleFunctor _ 0).obj M) := h₁
  have h₃' : ∃ M : (Scheme.Opens.toScheme (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)).Modules,
          IsFiniteLocallyFreeOfRankLT M p₃ ∧
      Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
            D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)).toLRSHom.toShHom).obj
                (DerivedCategory.Q.obj
          ((shiftFunctor (CochainComplex D.X.Modules ℤ) (1 : ℤ)).obj P₃)) ≅
          (DerivedCategory.singleFunctor _ 0).obj M) := h₃
  have key := exists_isFiniteLocallyFreeOfRankLT_derivedPullback_mappingCone (Y := D.X)
    (Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)) (K := P₃) (L := P₁) ψ (a
            := p₁) (c := p₃)
  have key2 := key h₁'
  have key3 := key2 h₃'
  obtain ⟨M, hM, ⟨e'⟩⟩ := key3
  have e'' : (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)).toLRSHom.toShHom).obj E ≅
        (DerivedCategory.singleFunctor _ 0).obj M :=
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
              D.X.Opens)).toLRSHom.toShHom).mapIso e ≪≫ e'
  exact ⟨M, hM.mono (by omega), ⟨e''⟩⟩

variable (D) in
/-- **The statement of Stacks 0FBD makes sense, for a mapping cone, zero form**: if
`P₁|_{X ∖ Z}` and `P₃[1]|_{X ∖ Z}` are zero, so is every object isomorphic to the mapping cone
of a map `ψ : P₃ ⟶ P₁`, off `Z`. -/
theorem isZero_of_iso_mappingCone (ψ : P₃ ⟶ P₁)
    (h₁ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj
              (DerivedCategory.Q.obj P₁)))
    (h₃ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj
              (DerivedCategory.Q.obj ((shiftFunctor (CochainComplex D.X.Modules ℤ) (1 : ℤ)).obj
                  P₃))))
    {E : DerivedCategory (OXMod.{u, u, u} D.X.toRingedSpace)}
    (e : E ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules) ψ)) :
    IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj E)
              :=
  (isZero_derivedPullback_mappingCone (Scheme.Opens.ι (⟨(Set.range D.i.base)ᶜ,
      D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens)) ψ h₁ h₃).of_iso
    ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).mapIso
              e)


end Restrictions

/-! ### The deformation to the direct sum -/

section Deformation

variable {D}

/-- An object isomorphic to a mapping cone of locally bounded finite locally free complexes is
isomorphic to such a complex. -/
private theorem exists_isLocallyBoundedFiniteLocallyFree_iso_of_iso_mappingCone
    (hP₁ : IsLocallyBoundedFiniteLocallyFree P₁) (hP₃ : IsLocallyBoundedFiniteLocallyFree P₃)
    (ψ : P₃ ⟶ P₁) {E : DerivedCategory (OXMod.{u, u, u} D.X.toRingedSpace)}
    (e : E ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules) ψ)) :
    ∃ P : CochainComplex (OXMod.{u, u, u} D.X.toRingedSpace) ℤ,
      IsLocallyBoundedFiniteLocallyFree P ∧ Nonempty (DerivedCategory.Q.obj P ≅ E) :=
  ⟨_, isLocallyBoundedFiniteLocallyFree_mappingCone ψ hP₃ hP₁, ⟨e.symm⟩⟩

/-- The derived fibre of the deformation cone along the section of a divisor `D'` of `𝐀¹_X` is
`E`, when `E` is the mapping cone of `ψ = φ · σ^♯ t`. -/
private def derivedPullbackDeformationConeIsoOfEq (D' : SectionDivisor (affineLineOverHom D.X))
    {E : DerivedCategory (OXMod.{u, u, u} D.X.toRingedSpace)} (ψ : P₃ ⟶ P₁)
    (hψ : φ ≫ complexSmul (D'.section.appTop (affineCoordinate D.X)) P₁ = ψ)
    (e : E ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules) ψ)) :
    (Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      D'.section.toLRSHom.toShHom).obj (DerivedCategory.Q.obj (deformationCone φ)) ≅ E :=
  derivedPullbackDeformationConeIso hP₁ hP₃ φ D'.section D'.section_comp ≪≫
    DerivedCategory.Q.mapIso (mappingConeCongr hψ) ≪≫ e.symm

include hP₁ hP₃ in
/-- **The deformation argument of Stacks 0FBD, for `c_p`.** Let `C` be the deformation cone of
`φ : P₃ ⟶ P₁` on `𝐀¹_X`, with `C|_{𝐀¹_X ∖ 𝐀¹_Z}` finite locally free of rank `< p` in degree `0`.
If `E ≅ C(φ)` and `E₀ ≅ C(0)`, then `c_p(Z ⟶ X, E) = c_p(Z ⟶ X, E₀)`: both are restrictions of
`c_p(𝐀¹_Z ⟶ 𝐀¹_X, C)`, along the sections `t = 1` and `t = 0` (Stacks 0FB3), and these two
restrictions agree (`Stacks.Chow.SectionDivisor.sectionRestriction_eq`). -/
theorem localizedChern_eq_of_deformation (hres : IsZero
    ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        D.deformationComplement.ι.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj (deformationCone φ))) ∨
      (∃ M : D.deformationComplement.toScheme.Modules, IsFiniteLocallyFreeOfRankLT M D.p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          D.deformationComplement.ι.toLRSHom.toShHom).obj
            (DerivedCategory.Q.obj (deformationCone φ)) ≅
              (DerivedCategory.singleFunctor _ 0).obj M)))
    (h' : (D.deformationSituation hP₁ hP₃ φ hres).IsFiniteLocallyFreeOfRankLTOnComplement)
    (e : D.E ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules) φ))
    (E₀ : DerivedCategory (OXMod.{u, u, u} D.X.toRingedSpace))
    (hE₀ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₀)
    (hres₀ : letI U : TopologicalSpace.Opens D.X :=
        ⟨(Set.range D.i.base)ᶜ, D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      letI F := Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (D.X.toRingedSpace.ofRestrict U.isOpenEmbedding)
      IsZero (F.obj E₀) ∨
        ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict U.isOpenEmbedding),
          IsFiniteLocallyFreeOfRankLT M D.p ∧
            Nonempty (F.obj E₀ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (e₀ : E₀ ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules)
      (0 : P₃ ⟶ P₁)))
    (hD : HasDefinedChernClasses D.E) (h : D.IsFiniteLocallyFreeOfRankLTOnComplement)
    (hD₀ : HasDefinedChernClasses E₀)
    (h₀ : ({ D with E := E₀, perfect := hE₀, restriction := hres₀ } :
        LocalizedChernData).IsFiniteLocallyFreeOfRankLTOnComplement) :
    D.localizedChern hD h = ({ D with E := E₀, perfect := hE₀, restriction := hres₀ } :
        LocalizedChernData).localizedChern hD₀ h₀ := by
  have hc := exists_isLocallyBoundedFiniteLocallyFree_iso_of_iso_mappingCone hP₁ hP₃ φ e
  have hc₀ := exists_isLocallyBoundedFiniteLocallyFree_iso_of_iso_mappingCone hP₁ hP₃ 0 e₀
  have e₁ := derivedPullbackDeformationConeIsoOfEq hP₁ hP₃ φ (affineLinePointDivisor D.X 1) φ
    (by rw [affineLinePointDivisor_section, affineLineSection_appTop_affineCoordinate,
      complexSmul_one, Category.comp_id]) e
  have e₀' := derivedPullbackDeformationConeIsoOfEq hP₁ hP₃ φ (affineLineZeroDivisor D.X) 0
    (by rw [affineLineZeroDivisor_section, affineLineConstantSection_appTop_affineCoordinate_zero,
      complexSmul_zero, Limits.comp_zero]) e₀
  have key₁ := sectionRestriction_localizedChern_deformationSituation h'
    (affineLinePointDivisor D.X 1) hc e₁ h
  have key₀ := sectionRestriction_localizedChern_deformationSituation
    (D := { D with E := E₀, perfect := hE₀, restriction := hres₀ }) (hP₁ := hP₁) (hP₃ := hP₃) (φ
        := φ) (hres := hres) h'
    (affineLineZeroDivisor D.X) hc₀ e₀' h₀
  have hom := SectionDivisor.sectionRestriction_eq
    (IsPullback.of_hasPullback D.i (affineLineOverHom D.X)) D.base D.a
    (relativeDimension_affineLineOver_fst _) (isAffineSpaceBundle_affineLineOver_fst D.X)
    (affineLinePointDivisor D.X 1) (affineLineZeroDivisor D.X)
    ((D.deformationSituation hP₁ hP₃ φ hres).localizedChern h')
  refine Eq.trans (LocalizedSituation.localizedChern_toLocalizedChernData
    (D.toSituation hc) h) ?_
  refine Eq.trans key₁.symm (Eq.trans hom (Eq.trans key₀ ?_))
  exact (LocalizedSituation.localizedChern_toLocalizedChernData
    (({ D with E := E₀, perfect := hE₀, restriction := hres₀ } : LocalizedChernData).toSituation
        hc₀) h₀).symm

include hP₁ hP₃ in
/-- **The deformation argument of Stacks 0FBD, for `P_p`.** Let `C` be the deformation cone of
`φ : P₃ ⟶ P₁` on `𝐀¹_X`, with `C|_{𝐀¹_X ∖ 𝐀¹_Z}` finite locally free of zero.
If `E ≅ C(φ)` and `E₀ ≅ C(0)`, then `P_q(Z ⟶ X, E) = P_q(Z ⟶ X, E₀)`: both are restrictions of
`P_q(𝐀¹_Z ⟶ 𝐀¹_X, C)`, along the sections `t = 1` and `t = 0` (Stacks 0FB3), and these two
restrictions agree (`Stacks.Chow.SectionDivisor.sectionRestriction_eq`). -/
theorem localizedPowerSum_eq_of_deformation (hres : IsZero
    ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        D.deformationComplement.ι.toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj (deformationCone φ))) ∨
      (∃ M : D.deformationComplement.toScheme.Modules, IsFiniteLocallyFreeOfRankLT M D.p ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          D.deformationComplement.ι.toLRSHom.toShHom).obj
            (DerivedCategory.Q.obj (deformationCone φ)) ≅
              (DerivedCategory.singleFunctor _ 0).obj M)))
    (h' : (D.deformationSituation hP₁ hP₃ φ hres).IsZeroOnComplement) (q : ℕ)
    (e : D.E ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules) φ))
    (E₀ : DerivedCategory (OXMod.{u, u, u} D.X.toRingedSpace))
    (hE₀ : Cohomology.PerfectComplexes.IsPerfect (X := D.X.toRingedSpace) E₀)
    (hres₀ : letI U : TopologicalSpace.Opens D.X :=
        ⟨(Set.range D.i.base)ᶜ, D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩
      letI F := Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        (D.X.toRingedSpace.ofRestrict U.isOpenEmbedding)
      IsZero (F.obj E₀) ∨
        ∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict U.isOpenEmbedding),
          IsFiniteLocallyFreeOfRankLT M D.p ∧
            Nonempty (F.obj E₀ ≅ (DerivedCategory.singleFunctor _ 0).obj M))
    (e₀ : E₀ ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules)
      (0 : P₃ ⟶ P₁)))
    (hD : HasDefinedChernClasses D.E) (h : D.IsZeroOnComplement)
    (hD₀ : HasDefinedChernClasses E₀)
    (h₀ : ({ D with E := E₀, perfect := hE₀, restriction := hres₀ } :
        LocalizedChernData).IsZeroOnComplement) :
    D.localizedPowerSum hD h q = ({ D with E := E₀, perfect := hE₀, restriction := hres₀ } :
        LocalizedChernData).localizedPowerSum hD₀ h₀ q := by
  have hc := exists_isLocallyBoundedFiniteLocallyFree_iso_of_iso_mappingCone hP₁ hP₃ φ e
  have hc₀ := exists_isLocallyBoundedFiniteLocallyFree_iso_of_iso_mappingCone hP₁ hP₃ 0 e₀
  have e₁ := derivedPullbackDeformationConeIsoOfEq hP₁ hP₃ φ (affineLinePointDivisor D.X 1) φ
    (by rw [affineLinePointDivisor_section, affineLineSection_appTop_affineCoordinate,
      complexSmul_one, Category.comp_id]) e
  have e₀' := derivedPullbackDeformationConeIsoOfEq hP₁ hP₃ φ (affineLineZeroDivisor D.X) 0
    (by rw [affineLineZeroDivisor_section, affineLineConstantSection_appTop_affineCoordinate_zero,
      complexSmul_zero, Limits.comp_zero]) e₀
  have key₁ := sectionRestriction_localizedPowerSum_deformationSituation h' q
    (affineLinePointDivisor D.X 1) hc e₁ h
  have key₀ := sectionRestriction_localizedPowerSum_deformationSituation
    (D := { D with E := E₀, perfect := hE₀, restriction := hres₀ }) (hP₁ := hP₁) (hP₃ := hP₃) (φ
        := φ) (hres := hres) h' q
    (affineLineZeroDivisor D.X) hc₀ e₀' h₀
  have hom := SectionDivisor.sectionRestriction_eq
    (IsPullback.of_hasPullback D.i (affineLineOverHom D.X)) D.base D.a
    (relativeDimension_affineLineOver_fst _) (isAffineSpaceBundle_affineLineOver_fst D.X)
    (affineLinePointDivisor D.X 1) (affineLineZeroDivisor D.X)
    ((D.deformationSituation hP₁ hP₃ φ hres).localizedPowerSum h' q)
  refine Eq.trans (LocalizedSituation.localizedPowerSum_toLocalizedChernData
    (D.toSituation hc) h q) ?_
  refine Eq.trans key₁.symm (Eq.trans hom (Eq.trans key₀ ?_))
  exact (LocalizedSituation.localizedPowerSum_toLocalizedChernData
    (({ D with E := E₀, perfect := hE₀, restriction := hres₀ } : LocalizedChernData).toSituation
        hc₀) h₀ q).symm

include hP₁ hP₃ in
/-- **The `A¹`-deformation step of Stacks 0FBD, for `c_p`.** Let `φ : P₃ ⟶ P₁` be a map of
locally bounded complexes of finite locally free `𝒪_X`-modules such that `P₁|_{X ∖ Z}` and
`P₃[1]|_{X ∖ Z}` are finite locally free of rank `< p₁` and `< p₃` placed in degree `0`, and let
`p₁ + p₃ ≤ p + 1`. For `E ≅ C(φ)` and `E₀ ≅ C(0) = P₁ ⊕ P₃[1]`, the localized Chern classes of
Remark 0GUK agree: `c_p(Z ⟶ X, E) = c_p(Z ⟶ X, E₀)`. The restriction hypotheses of the two
classes are those of
`Stacks.Chow.LocalizedChernData.exists_isFiniteLocallyFreeOfRankLT_of_iso_mappingCone`
("the statement makes sense"). -/
theorem localizedChern_mappingCone_eq {p₁ p₃ : ℕ}
    (h₁ : (∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₁ ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
              D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
                  D.X.Opens).isOpenEmbedding)).obj (DerivedCategory.Q.obj P₁) ≅
            (DerivedCategory.singleFunctor _ 0).obj M)))
    (h₃ : (∃ M : OXMod.{u, u, u} (D.X.toRingedSpace.restrict (⟨(Set.range D.i.base)ᶜ,
        D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding),
      IsFiniteLocallyFreeOfRankLT M p₃ ∧
        Nonempty ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
          (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
              D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ :
                  D.X.Opens).isOpenEmbedding)).obj (DerivedCategory.Q.obj ((shiftFunctor
                      (CochainComplex D.X.Modules ℤ) (1 : ℤ)).obj P₃)) ≅
            (DerivedCategory.singleFunctor _ 0).obj M)))
    (hp : p₁ + p₃ ≤ D.p + 1)
    (e : D.E ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules) φ))
    (E₀ : DerivedCategory (OXMod.{u, u, u} D.X.toRingedSpace))
    (e₀ : E₀ ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules)
      (0 : P₃ ⟶ P₁)))
    (hD : HasDefinedChernClasses D.E) (hD₀ : HasDefinedChernClasses E₀) :
    D.localizedChern hD (D.exists_isFiniteLocallyFreeOfRankLT_of_iso_mappingCone φ h₁ h₃ hp e) =
      ({ D with
          E := E₀
          perfect := isPerfect_of_iso_Q_obj
            (isLocallyBoundedFiniteLocallyFree_mappingCone 0 hP₃ hP₁) e₀
          restriction := Or.inr (D.exists_isFiniteLocallyFreeOfRankLT_of_iso_mappingCone 0 h₁ h₃
            hp e₀) } : LocalizedChernData).localizedChern hD₀
        ((D.isFiniteLocallyFreeOfRankLTOnComplement_update_iff E₀ _).2
          (D.exists_isFiniteLocallyFreeOfRankLT_of_iso_mappingCone 0 h₁ h₃ hp e₀)) :=
  localizedChern_eq_of_deformation hP₁ hP₃ φ
    (Or.inr (exists_isFiniteLocallyFreeOfRankLT_deformationCone hP₁ hP₃ φ h₁ h₃ hp))
    ((D.deformationSituation_isFiniteLocallyFreeOfRankLTOnComplement_iff hP₁ hP₃ φ
      (hres := Or.inr (exists_isFiniteLocallyFreeOfRankLT_deformationCone hP₁ hP₃ φ h₁ h₃ hp))).2
      (exists_isFiniteLocallyFreeOfRankLT_deformationCone hP₁ hP₃ φ h₁ h₃ hp))
    e E₀ _ _ e₀ hD _ hD₀ _

include hP₁ hP₃ in
/-- **The `A¹`-deformation step of Stacks 0FBD, for `P_p`.** Let `φ : P₃ ⟶ P₁` be a map of
locally bounded complexes of finite locally free `𝒪_X`-modules such that `P₁|_{X ∖ Z}` and
`P₃[1]|_{X ∖ Z}` are zero. For `E ≅ C(φ)` and `E₀ ≅ C(0) = P₁ ⊕ P₃[1]`, the localized classes of
Remark 0GUK agree in every degree: `P_q(Z ⟶ X, E) = P_q(Z ⟶ X, E₀)`. -/
theorem localizedPowerSum_mappingCone_eq
    (h₁ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj
              (DerivedCategory.Q.obj P₁)))
    (h₃ : IsZero ((Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
      (D.X.toRingedSpace.ofRestrict (⟨(Set.range D.i.base)ᶜ,
          D.i.isClosedEmbedding.isClosed_range.isOpen_compl⟩ : D.X.Opens).isOpenEmbedding)).obj
              (DerivedCategory.Q.obj ((shiftFunctor (CochainComplex D.X.Modules ℤ) (1 : ℤ)).obj
                  P₃))))
    (e : D.E ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules) φ))
    (E₀ : DerivedCategory (OXMod.{u, u, u} D.X.toRingedSpace))
    (e₀ : E₀ ≅ DerivedCategory.Q.obj (CochainComplex.mappingCone (C := D.X.Modules)
      (0 : P₃ ⟶ P₁)))
    (hD : HasDefinedChernClasses D.E) (hD₀ : HasDefinedChernClasses E₀) (q : ℕ) :
    D.localizedPowerSum hD (D.isZero_of_iso_mappingCone φ h₁ h₃ e) q =
      ({ D with
          E := E₀
          perfect := isPerfect_of_iso_Q_obj
            (isLocallyBoundedFiniteLocallyFree_mappingCone 0 hP₃ hP₁) e₀
          restriction := Or.inl (D.isZero_of_iso_mappingCone 0 h₁ h₃ e₀) } :
            LocalizedChernData).localizedPowerSum hD₀
        ((D.isZeroOnComplement_update_iff E₀ _).2
          (D.isZero_of_iso_mappingCone 0 h₁ h₃ e₀)) q :=
  localizedPowerSum_eq_of_deformation hP₁ hP₃ φ (Or.inl (isZero_deformationCone hP₁ hP₃ φ h₁ h₃))
    ((D.deformationSituation_isZeroOnComplement_iff hP₁ hP₃ φ
      (hres := Or.inl (isZero_deformationCone hP₁ hP₃ φ h₁ h₃))).2
      (isZero_deformationCone hP₁ hP₃ φ h₁ h₃)) q
    e E₀ _ _ e₀ hD _ hD₀ _

end Deformation

end LocalizedChernData

end Stacks.Chow

end
