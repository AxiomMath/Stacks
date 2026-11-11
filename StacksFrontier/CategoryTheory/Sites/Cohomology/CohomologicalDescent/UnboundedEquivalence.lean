module

public import Mathlib.CategoryTheory.Adjunction.FullyFaithful
public import Mathlib.CategoryTheory.Adjunction.Restrict
public import Mathlib.CategoryTheory.Functor.Derived.PointwiseLeftDerived
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CohomologicalDescent.BoundedBelowEquivalence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.PushforwardBoundedCohomologicalDimension

/-!
# Derived pullback as an equivalence of unbounded derived categories

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a flat morphism of ringed topoi induced by a morphism of
sites, let `𝒜 ⊂ Mod(𝒪)` and
`𝒜' ⊂ Mod(𝒪')` be weak Serre subcategories, and assume

1. `f^*` induces an equivalence `𝒜' ⟶ 𝒜`,
2. `ℱ' ⟶ Rf_*f^*ℱ'` is an isomorphism for every `ℱ'` of `𝒜'`,
3. `C, 𝒪, 𝒜` and `C', 𝒪', 𝒜'` both satisfy the standing Olsson--Laszlo hypothesis of Tag 0D6R.

Then

  `Lf^* : D_{𝒜'}(𝒪') ⟶ D_𝒜(𝒪)`

is an equivalence of categories, with quasi-inverse `Rf_* : D_𝒜(𝒪) ⟶ D_{𝒜'}(𝒪')`.

This is Stacks 0D7V for morphisms presented by sites. Stacks 0D7V itself, for an arbitrary
morphism of ringed topoi, is in `UnboundedEquivalenceOfToposHom`, and carries the tag.

## The argument

This is Tag 0D7U with the boundedness below dropped, and the two extra Olsson--Laszlo hypotheses
are what pays for dropping it.

Derived pullback restricts for the same reason as in the bounded below case: it is degreewise
pullback, which is exact, so `H^q(Lf^*K)` is `f^*H^q(K)`, and `f^*` carries `𝒜'` into `𝒜`. No
boundedness enters.

Derived pushforward restricts by Tag 0D6U, part (a), applied with `N = 0`. Its two inputs are
read off from the bounded below case: `Rᵖf_*ℱ` lies in `𝒜'` for `ℱ` of `𝒜` because `Rf_*ℱ` lies
in `D⁺_{𝒜'}(𝒪')`, and `Rᵖf_*ℱ` vanishes for `p > 0` because `Rf_*ℱ` is the object `ℱ'` of `𝒜'`
with `f^*ℱ' ≅ ℱ`, placed in degree zero — so it lives in degrees `≤ 0`.

The counit is invertible on all of `D_𝒜(𝒪)` degreewise. Fix `j` and truncate at `-n` with
`n` large enough that `-n ≤ j`. The truncation `K ⟶ τ_{≥ -n}K` is an isomorphism on `H^j`; the
counit at `τ_{≥ -n}K` is invertible because that object is bounded below with cohomology in `𝒜`;
and `Rf_*` of the truncation is an isomorphism on `H^j` by Tag 0D6U, part (b). Since
`H^j ∘ Lf^*` is `f^* ∘ H^j`, the left-hand vertical of the naturality square for the counit is
also an isomorphism on `H^j`, and the square identifies `H^j` of the counit at `K` with an
isomorphism. The unit then follows: `Lf^*` of the unit at `K` is invertible by the triangle
identity together with the counit at `Lf^*K`, and `f^*` reflects isomorphisms between objects of
`𝒜'` because it induces an equivalence `𝒜' ⟶ 𝒜`.

## Main definitions

* `Stacks.Cohomology.CohomologicalDescent.derivedPullbackNatIso`: the derived pullback of a
  morphism along which degreewise pullback is exact *is* the functor induced by degreewise
  pullback, naturally in the argument.
* `Stacks.Cohomology.CohomologicalDescent.derivedPullbackCompHomologyFunctorIso`:
  consequently `H^q(Lf^*-)` is `f^*H^q(-)`, naturally.
* `Stacks.Cohomology.CohomologicalDescent.derivedAdjunctionUnbounded`: the restriction of
  `Lf^* ⊣ Rf_*` to the subcategories `D_{𝒜'}(𝒪')` and `D_𝒜(𝒪)`.
* `Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnbounded`:
  **the equivalence.**

## Main results

* `Stacks.Cohomology.CohomologicalDescent.derivedCategoryB_derivedPullback_obj`: `Lf^*` carries
  `D_{𝒜'}(𝒪')` into `D_𝒜(𝒪)`.
* `Stacks.Cohomology.CohomologicalDescent.derivedCategoryB_derivedPushforward_obj`: `Rf_*`
  carries `D_𝒜(𝒪)` into `D_{𝒜'}(𝒪')`.
* `Stacks.Cohomology.CohomologicalDescent.isIso_derivedCounit_app_of_derivedCategoryB_of_exact`
  and `isIso_derivedUnit_app_of_derivedCategoryB_of_exact`: the counit is invertible on
  `D_𝒜(𝒪)` and the unit on `D_{𝒜'}(𝒪')`.
* `Stacks.Cohomology.CohomologicalDescent.derivedPullbackEquivalenceUnbounded_functor` and
  `derivedPullbackEquivalenceUnbounded_inverse`: the two functors of the equivalence are the
  restrictions of `Lf^*` and of `Rf_*`.

## Implementation notes

**The Olsson--Laszlo hypotheses are carried as loose data**, as they are for Tag 0D6U: a class of
objects of each site, an integer bound and a cofinal system of coverings of each member of the
class, rather than two `Stacks.Cohomology.OlssonLaszloSituation` arguments, because such a
situation bundles its own site and sheaf of rings, which here must be those of `X` and of `Y`.

**Flatness is the hypothesis of the source; the morphism-of-sites condition `hmos` is not.**
As in Tag 0D7U, the final statements open with `letI`, because the *type* of `Lf^*` mentions the
instance saying that degreewise pullback has a left derived functor, so nothing about `Lf^*` can
be written down before that instance is in scope. The section `Exact` takes exactness of degreewise
pullback as instances and the propagated counit hypothesis of Tag 0D7S as an argument; the
section `Descent` produces the instances from flatness and discharges that hypothesis.

**Only the counit half of the bounded below propagation is needed.** Tag 0D7S carries the
invertibility of the counit from `𝒜` to `D⁺_𝒜(𝒪)`, which is what the truncation argument consumes;
the invertibility of the unit on `D_{𝒜'}(𝒪')` then comes from the triangle identity, so the
corresponding statement for the unit — Tag 0D7T — is not used.

**`Rᵖf_*ℱ` is read as `Hᵖ(Rf_*(ℱ[0]))`**, the convention of Tag 0D6U, so that every statement is
about one and the same functor — the unbounded `Rf_*` of Tag 07A6 — and no comparison between the
bounded below and the unbounded derived functor is needed.

**The naturality of `H^q(Lf^*-) ≅ f^*H^q(-)` is what the unbounded case needs beyond the bounded
below one.** Tag 0D7U uses only the pointwise comparison
`derivedPullbackHomologyObjIso`; here the comparison is applied to a *morphism*, namely `Rf_*` of
a truncation map, so it is rebuilt as a natural isomorphism by the uniqueness of left derived
functors.

## References

* [Stacks Project, Tag 0D7V](https://stacks.math.columbia.edu/tag/0D7V)
* [Stacks Project, Tag 0D7U](https://stacks.math.columbia.edu/tag/0D7U)
* [Stacks Project, Tag 0D7S](https://stacks.math.columbia.edu/tag/0D7S)
* [Stacks Project, Tag 0D6R](https://stacks.math.columbia.edu/tag/0D6R)
* [Stacks Project, Tag 0D6U](https://stacks.math.columbia.edu/tag/0D6U)
* [Stacks Project, Tag 06YY](https://stacks.math.columbia.edu/tag/06YY)
* [Stacks Project, Tag 07A6](https://stacks.math.columbia.edu/tag/07A6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.CohomologicalDescent

universe w

attribute [local instance] HasDerivedCategory.standard

/- `isIso_homologyMap_truncGEπ_app` stood here: the same statement, with the same proof, as
`DerivedCategory.isIso_homologyMap_truncGEπ_app` in
`StacksFrontier/Algebra/Homology/DerivedCategory/TruncGELTSingle.lean:98`, which this module
imports. Uses here and in `UnboundedEquivalenceRelativeSituation` name that one. -/

variable {X Y : RingedTopos.{w, w, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasSheafify Y.J AddCommGrpCat.{w}]
  [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  (f : RingedToposSiteHom X Y)
  (A : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (A' : ObjectProperty (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
  [A.IsWeakSerreClass] [A'.IsWeakSerreClass]

section Exact

variable [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))]
  (hmos : f.u.IsMorphismOfSites Y.J X.J)

/-! ### Derived pullback is degreewise pullback, naturally -/

/-- **For a morphism along which degreewise pullback is exact, the derived pullback is the
functor induced on derived categories by degreewise pullback, naturally in the argument.** Both
are left derived functors of degreewise pullback followed by localization — the first by
construction, the second because an exact functor inverts the quasi-isomorphisms — so they agree
by the uniqueness of left derived functors. -/
def derivedPullbackNatIso : derivedPullback f ≅ f.pullbackTopos.mapDerivedCategory :=
  haveI : f.pullbackTopos.mapDerivedCategory.IsLeftDerivedFunctor
      f.pullbackTopos.mapDerivedCategoryFactorsh.hom
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ)) :=
    Functor.isLeftDerivedFunctor_of_inverts
      (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
          (ComplexShape.up ℤ)) _
      f.pullbackTopos.mapDerivedCategoryFactorsh
  Functor.leftDerivedNatIso (derivedPullback f) f.pullbackTopos.mapDerivedCategory
    (derivedPullbackComparison f) f.pullbackTopos.mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
        (ComplexShape.up ℤ))
    (Iso.refl _)

/-- **`H^q(Lf^*-)` is `f^*H^q(-)`, naturally in the argument.** The derived pullback is the
functor induced by the exact functor `f^*`, and such a functor commutes with the cohomology
functors of the derived category. -/
def derivedPullbackCompHomologyFunctorIso (q : ℤ) :
    derivedPullback f ⋙ DerivedCategory.homologyFunctor (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q ≅
      DerivedCategory.homologyFunctor (SheafOfModules.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) q ⋙ f.pullbackTopos :=
  Functor.isoWhiskerRight (derivedPullbackNatIso f)
      (DerivedCategory.homologyFunctor (SheafOfModules.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) q) ≪≫
    StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso f.pullbackTopos q

/-! ### The two derived functors restrict -/

variable (hA : ∀ M, A' M → A (f.pullbackTopos.obj M))

include hA in
omit [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [A'.IsWeakSerreClass] in
/-- `Lf^*` carries `D_{𝒜'}(𝒪')` into `D_𝒜(𝒪)`: its cohomology objects are `f^*` of those of the
source, and `f^*` carries `𝒜'` into `𝒜`. -/
theorem derivedCategoryB_derivedPullback_obj_of_exact
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : DerivedCategoryB.derivedCategoryB A' K) :
    DerivedCategoryB.derivedCategoryB A ((derivedPullback f).obj K) :=
  fun q ↦ A.prop_of_iso (derivedPullbackHomologyObjIso f K q).symm (hA _ (hK q))

variable (hEquiv : (A.lift (A'.ι ⋙ f.pullbackTopos) (fun N ↦ hA N.obj N.property)).IsEquivalence)
  (hUnit : ∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
    ((DerivedCategory.singleFunctor (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M)))

include hA hEquiv hUnit in
omit [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [A.IsWeakSerreClass] [A'.IsWeakSerreClass] in
/-- **For `ℱ` in `𝒜` the pushforward `Rf_*ℱ` lives in degrees `≤ 0`.** Write `ℱ = f^*ℱ'` using
hypothesis (1); the unit `ℱ' ⟶ Rf_*Lf^*ℱ'` is invertible by hypothesis (2) and `Lf^*ℱ'` is `ℱ`,
so `Rf_*ℱ` is `ℱ'` placed in degree zero. This is the vanishing of `Rᵖf_*` above `0`. -/
theorem isLE_derivedPushforward_singleFunctor_obj_of_exact
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (hM : A M) :
    ((derivedPushforward f).obj
      ((DerivedCategory.singleFunctor (SheafOfModules.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M)).IsLE 0 := by
  have := hEquiv
  obtain ⟨N, ⟨e⟩⟩ := Functor.EssSurj.mem_essImage
    (A.lift (A'.ι ⋙ f.pullbackTopos) (fun N ↦ hA N.obj N.property)) ⟨M, hM⟩
  have e₀ : f.pullbackTopos.obj N.obj ≅ M := A.ι.mapIso e
  have hN := hUnit N.obj N.property
  have eL := derivedPullbackSingleFunctorObjIso f N.obj ≪≫
    (DerivedCategory.singleFunctor (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).mapIso e₀
  have eR : (DerivedCategory.singleFunctor (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj N.obj ≅
      (derivedPushforward f).obj
        ((DerivedCategory.singleFunctor (SheafOfModules.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) 0).obj M) :=
    (@asIso _ _ _ _ _ hN).trans ((derivedPushforward f).mapIso eL)
  exact DerivedCategory.TStructure.t.isLE_of_iso eR 0

variable (B : Set X.C)
  (basisCover : ∀ U : X.C, ∃ 𝒰 : PreZeroHypercover.{w} U,
    𝒰.sieve₀ ∈ X.J U ∧ ∀ i, B (𝒰.X i))
  (degreeBound : ∀ V : X.C, B V → ℤ)
  (coverings : ∀ V : X.C, B V → Stacks.Cohomology.CofinalCoveringSystem X.J V)
  (vanishing : ∀ (V : X.C) (hV : B V) (𝒰 : PreZeroHypercover.{w} V),
    (coverings V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
        IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (𝒰.X i) p F))
  (B' : Set Y.C)
  (basisCover' : ∀ U : Y.C, ∃ 𝒰 : PreZeroHypercover.{w} U,
    𝒰.sieve₀ ∈ Y.J U ∧ ∀ i, B' (𝒰.X i))
  (degreeBound' : ∀ V : Y.C, B' V → ℤ)
  (coverings' : ∀ V : Y.C, B' V → Stacks.Cohomology.CofinalCoveringSystem Y.J V)
  (vanishing' : ∀ (V : Y.C) (hV : B' V) (𝒰 : PreZeroHypercover.{w} V),
    (coverings' V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound' V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O), A' F →
        IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            (𝒰.X i) p F))


/-! ### The unit and the counit are invertible -/

include hmos hA hEquiv hUnit basisCover vanishing basisCover' vanishing' in
/-- **The counit `Lf^*Rf_*K ⟶ K` is invertible for every `K` of `D_𝒜(𝒪)`.** Fix a degree `j` and
truncate at `-n ≤ j`. The truncation map is invertible on `H^j`, the counit at the truncation is
invertible because that object lies in `D⁺_𝒜(𝒪)`, and `Rf_*` of the truncation map is invertible
on `H^j` by Tag 0D6U, part (b); applying `f^* = H^j ∘ Lf^*` and reading the naturality square for
the counit gives the claim in degree `j`. -/
theorem isIso_derivedCounit_app_of_derivedCategoryB_of_exact
    (hCounitPlus : DerivedCategoryB.derivedCategoryBPlus A ≤
      (derivedPullbackPushforwardAdjunctionOfExact f).counitIsIso)
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (hK : DerivedCategoryB.derivedCategoryB A K) :
    IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app K) := by
  rw [DerivedCategory.isIso_iff]
  intro j
  obtain ⟨n, hn⟩ : ∃ n : ℕ, -(n : ℤ) ≤ j := ⟨(-j).toNat, by omega⟩
  have hπ := DerivedCategory.isIso_homologyMap_truncGEπ_app (-(n : ℤ)) j hn K
  have hε : IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app
      ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)) :=
    hCounitPlus _ (Stacks.Cohomology.OlssonLaszlo.truncGETower_obj_mem_plus A K hK n)
  have hRπ : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
      ((derivedPushforward f).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) :=
    Stacks.Cohomology.OlssonLaszlo.isIso_homology_derivedPushforward_truncGEπ f hmos A A'
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing' 0
      (fun p F hF ↦ (derivedCategoryBPlus_derivedPushforward_singleFunctor_obj_of_exact
        f A A' hA hEquiv hUnit F hF).2 p)
      (fun p hp F hF ↦
        have := isLE_derivedPushforward_singleFunctor_obj_of_exact f A A' hA hEquiv hUnit F hF
        DerivedCategory.isZero_of_isLE _ 0 (p : ℤ) hp)
      K hK n j (by omega)
  have hLRπ : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
      ((derivedPullback f).map ((derivedPushforward f).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)))) :=
    (NatIso.isIso_map_iff (derivedPullbackCompHomologyFunctorIso f j)
      ((derivedPushforward f).map
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))).2 (by
      show IsIso (f.pullbackTopos.map
        ((DerivedCategory.homologyFunctor (SheafOfModules.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
          ((derivedPushforward f).map
            ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))))
      exact inferInstance)
  have hnat : (DerivedCategory.homologyFunctor (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
        ((derivedPullback f).map ((derivedPushforward f).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))) ≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
          ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app
            ((DerivedCategory.TStructure.t.truncGE (-(n : ℤ))).obj K)) =
      (DerivedCategory.homologyFunctor (SheafOfModules.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
          ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app K) ≫
        (DerivedCategory.homologyFunctor (SheafOfModules.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
          ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K) := by
    rw [← Functor.map_comp, ← Functor.map_comp]
    exact congrArg (DerivedCategory.homologyFunctor (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
      ((derivedPullbackPushforwardAdjunctionOfExact f).counit.naturality
        ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))
  have hcomp : IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
      ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app K) ≫
    (DerivedCategory.homologyFunctor (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
      ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K)) := by
    rw [← hnat]
    exact IsIso.comp_isIso' hLRπ inferInstance
  exact IsIso.of_isIso_comp_right _
    ((DerivedCategory.homologyFunctor (SheafOfModules.{w}
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
      ((DerivedCategory.TStructure.t.truncGEπ (-(n : ℤ))).app K))

include hA hEquiv in
omit [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [A.IsWeakSerreClass]
  [PreservesFiniteLimits f.pullbackTopos] [PreservesFiniteColimits f.pullbackTopos]
  [(pullbackOnHomotopy f).HasLeftDerivedFunctor
    (HomotopyCategory.quasiIso (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ComplexShape.up ℤ))] in
/-- **`f^*` reflects isomorphisms between objects of `𝒜'`**, because it induces an equivalence
`𝒜' ⟶ 𝒜` and the inclusion of a full subcategory reflects isomorphisms. -/
theorem isIso_of_isIso_pullbackTopos_map
    {M N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (g : M ⟶ N) (hM : A' M)
    (hN : A' N)
    [IsIso (f.pullbackTopos.map g)] : IsIso g := by
  have := hEquiv
  let F := A.lift (A'.ι ⋙ f.pullbackTopos) (fun N ↦ hA N.obj N.property)
  let g' : (⟨M, hM⟩ : A'.FullSubcategory) ⟶ ⟨N, hN⟩ := ObjectProperty.homMk g
  have : IsIso (F.map g') := by
    refine (ObjectProperty.isIso_hom_iff (F.map g')).1 ?_
    show IsIso (f.pullbackTopos.map g)
    exact inferInstance
  have : IsIso g' := isIso_of_reflects_iso g' F
  show IsIso g'.hom
  exact inferInstance

include hmos hA hEquiv hUnit basisCover vanishing basisCover' vanishing' in
/-- **The unit `K ⟶ Rf_*Lf^*K` is invertible for every `K` of `D_{𝒜'}(𝒪')`.** By the triangle
identity, `Lf^*` of the unit at `K` composed with the counit at `Lf^*K` is the identity, and the
latter is invertible because `Lf^*K` lies in `D_𝒜(𝒪)`; so `Lf^*` of the unit is invertible.
Degreewise this says that `f^*H^j` of the unit is invertible, and `f^*` reflects isomorphisms
between objects of `𝒜'`, which both `H^j(K)` and `H^j(Rf_*Lf^*K)` are. -/
theorem isIso_derivedUnit_app_of_derivedCategoryB_of_exact
    (hCounitPlus : DerivedCategoryB.derivedCategoryBPlus A ≤
      (derivedPullbackPushforwardAdjunctionOfExact f).counitIsIso)
    (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))
    (hK : DerivedCategoryB.derivedCategoryB A' K) :
    IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app K) := by
  have hFK : DerivedCategoryB.derivedCategoryB A ((derivedPullback f).obj K) :=
    derivedCategoryB_derivedPullback_obj_of_exact f A A' hA K hK
  have hGFK : DerivedCategoryB.derivedCategoryB A'
      ((derivedPushforward f).obj ((derivedPullback f).obj K)) :=
    (Stacks.Cohomology.OlssonLaszlo.derivedCategoryB_derivedPushforward_obj f hmos A A'
    B basisCover degreeBound coverings vanishing
    B' basisCover' degreeBound' coverings' vanishing' 0
    (fun p F hF ↦ (derivedCategoryBPlus_derivedPushforward_singleFunctor_obj_of_exact
      f A A' hA hEquiv hUnit F hF).2 p)
    (fun p hp F hF ↦
      have := isLE_derivedPushforward_singleFunctor_obj_of_exact f A A' hA hEquiv hUnit F hF
      DerivedCategory.isZero_of_isLE _ 0 (p : ℤ) hp)) _ hFK
  have hε : IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app
      ((derivedPullback f).obj K)) :=
    isIso_derivedCounit_app_of_derivedCategoryB_of_exact f A A' hmos hA hEquiv hUnit
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing' hCounitPlus _ hFK
  have hLη : IsIso ((derivedPullback f).map
      ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app K)) := by
    have htri : IsIso ((derivedPullback f).map
        ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app K) ≫
          (derivedPullbackPushforwardAdjunctionOfExact f).counit.app
            ((derivedPullback f).obj K)) := by
      rw [(derivedPullbackPushforwardAdjunctionOfExact f).left_triangle_components K]
      exact (Iso.refl ((derivedPullback f).obj K)).isIso_hom
    exact IsIso.of_isIso_comp_right _
      ((derivedPullbackPushforwardAdjunctionOfExact f).counit.app ((derivedPullback f).obj K))
  rw [DerivedCategory.isIso_iff]
  intro j
  have hpb : IsIso (f.pullbackTopos.map
      ((DerivedCategory.homologyFunctor (SheafOfModules.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) j).map
        ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app K))) :=
    (NatIso.isIso_map_iff (derivedPullbackCompHomologyFunctorIso f j)
      ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app K)).1 (by
      show IsIso ((DerivedCategory.homologyFunctor (SheafOfModules.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) j).map
        ((derivedPullback f).map
          ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app K)))
      exact inferInstance)
  exact isIso_of_isIso_pullbackTopos_map f A A' hA hEquiv _ (hK j) (hGFK j)

/-! ### The equivalence -/

include hmos hA hEquiv hUnit basisCover vanishing basisCover' vanishing' in
/-- **The restriction of the derived adjunction `Lf^* ⊣ Rf_*` to the subcategories `D_{𝒜'}(𝒪')`
and `D_𝒜(𝒪)`.** -/
def derivedAdjunctionUnbounded :
    (DerivedCategoryB.derivedCategoryB A).lift
        ((DerivedCategoryB.derivedCategoryB A').ι ⋙ derivedPullback f)
        (fun K ↦ derivedCategoryB_derivedPullback_obj_of_exact f A A' hA K.obj K.property) ⊣
      (DerivedCategoryB.derivedCategoryB A').lift
        ((DerivedCategoryB.derivedCategoryB A).ι ⋙ derivedPushforward f)
        (fun K ↦ (Stacks.Cohomology.OlssonLaszlo.derivedCategoryB_derivedPushforward_obj f hmos A A'
    B basisCover degreeBound coverings vanishing
    B' basisCover' degreeBound' coverings' vanishing' 0
    (fun p F hF ↦ (derivedCategoryBPlus_derivedPushforward_singleFunctor_obj_of_exact
      f A A' hA hEquiv hUnit F hF).2 p)
    (fun p hp F hF ↦
      haveI := isLE_derivedPushforward_singleFunctor_obj_of_exact f A A' hA hEquiv hUnit F hF
      DerivedCategory.isZero_of_isLE _ 0 (p : ℤ) hp)) K.obj K.property) :=
  (derivedPullbackPushforwardAdjunctionOfExact f).restrictFullyFaithful
    (DerivedCategoryB.derivedCategoryB A').fullyFaithfulι
    (DerivedCategoryB.derivedCategoryB A).fullyFaithfulι (Iso.refl _) (Iso.refl _)

include hmos hA hEquiv hUnit basisCover vanishing basisCover' vanishing' in
/-- **The equivalence, for a morphism along which degreewise pullback is exact.** The restricted
left adjoint is fully faithful because `D_{𝒜'}(𝒪')` lies in the subcategory of Tag 0D7Q where the
unit is invertible, the restricted right adjoint because `D_𝒜(𝒪)` lies in the subcategory of Tag
0D7R where the counit is invertible; an adjunction whose two adjoints are fully faithful is an
equivalence. -/
def derivedPullbackEquivalenceUnboundedOfExact
    (hCounitPlus : DerivedCategoryB.derivedCategoryBPlus A ≤
      (derivedPullbackPushforwardAdjunctionOfExact f).counitIsIso) :
    (DerivedCategoryB.derivedCategoryB A').FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB A).FullSubcategory :=
  have hUnitB : DerivedCategoryB.derivedCategoryB A' ≤
      (derivedPullbackPushforwardAdjunctionOfExact f).unitIsIso := fun K hK ↦
    isIso_derivedUnit_app_of_derivedCategoryB_of_exact f A A' hmos hA hEquiv hUnit
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing' hCounitPlus K hK
  have hCounitB : DerivedCategoryB.derivedCategoryB A ≤
      (derivedPullbackPushforwardAdjunctionOfExact f).counitIsIso := fun K hK ↦
    isIso_derivedCounit_app_of_derivedCategoryB_of_exact f A A' hmos hA hEquiv hUnit
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing' hCounitPlus K hK
  letI hL := (derivedPullbackPushforwardAdjunctionOfExact f).fullyFaithfulιCompLeftAdjointOfLE
    hUnitB
  letI hR := (derivedPullbackPushforwardAdjunctionOfExact f).fullyFaithfulιCompRightAdjointOfLE
    hCounitB
  letI := hL.full
  letI := hL.faithful
  letI := hR.full
  letI := hR.faithful
  (derivedAdjunctionUnbounded f A A' hmos hA hEquiv hUnit
    B basisCover degreeBound coverings vanishing
    B' basisCover' degreeBound' coverings' vanishing').toEquivalence

end Exact

section Descent

variable (hmos : f.u.IsMorphismOfSites Y.J X.J)
  (hf : SheafOfModules.IsFlatMapULift.{w, w, w} (StacksPullbackFactorization.auxHomH f).fSharp)
  (hA : ∀ M, A' M → A (f.pullbackTopos.obj M))
  (hEquiv : (A.lift (A'.ι ⋙ f.pullbackTopos) (fun N ↦ hA N.obj N.property)).IsEquivalence)
  (B : Set X.C)
  (basisCover : ∀ U : X.C, ∃ 𝒰 : PreZeroHypercover.{w} U,
    𝒰.sieve₀ ∈ X.J U ∧ ∀ i, B (𝒰.X i))
  (degreeBound : ∀ V : X.C, B V → ℤ)
  (coverings : ∀ V : X.C, B V → Stacks.Cohomology.CofinalCoveringSystem X.J V)
  (vanishing : ∀ (V : X.C) (hV : B V) (𝒰 : PreZeroHypercover.{w} V),
    (coverings V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O), A F →
        IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
            (𝒰.X i) p F))
  (B' : Set Y.C)
  (basisCover' : ∀ U : Y.C, ∃ 𝒰 : PreZeroHypercover.{w} U,
    𝒰.sieve₀ ∈ Y.J U ∧ ∀ i, B' (𝒰.X i))
  (degreeBound' : ∀ V : Y.C, B' V → ℤ)
  (coverings' : ∀ V : Y.C, B' V → Stacks.Cohomology.CofinalCoveringSystem Y.J V)
  (vanishing' : ∀ (V : Y.C) (hV : B' V) (𝒰 : PreZeroHypercover.{w} V),
    (coverings' V hV).cov 𝒰 → ∀ (i : 𝒰.I₀) (p : ℕ), degreeBound' V hV < (p : ℤ) →
      ∀ F : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O), A' F →
        IsZero (Stacks.Cohomology.moduleCohomology (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
            (𝒰.X i) p F))

include hmos hf hA in
omit [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  [EnoughInjectives (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))]
  [A'.IsWeakSerreClass] in
/-- **Derived pullback restricts, for a morphism of ringed topoi induced by a morphism of sites**
(the hypothesis `hmos`). Let `f` be a flat such morphism and let `𝒜 ⊂ Mod(𝒪)`, `𝒜' ⊂ Mod(𝒪')` be
weak Serre subcategories with `f^*𝒜' ⊂ 𝒜`. Then `Lf^*` carries `D_{𝒜'}(𝒪')` into `D_𝒜(𝒪)`.
This is the special case of Stacks 0D7V for morphisms presented by sites; the statement for an
arbitrary morphism of ringed topoi is
`Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom.derivedCategoryB_derivedPullback_obj`. -/
theorem derivedCategoryB_derivedPullback_obj :
    letI := f.pullbackTopos_preservesFiniteLimits hmos hf
    letI := f.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
    ∀ (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))),
      DerivedCategoryB.derivedCategoryB A' K →
        DerivedCategoryB.derivedCategoryB A ((derivedPullback f).obj K) := by
  let := f.pullbackTopos_preservesFiniteLimits hmos hf
  let := f.pullbackTopos_preservesFiniteColimits
  let := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
  exact derivedCategoryB_derivedPullback_obj_of_exact f A A' hA

include hmos hf hA hEquiv basisCover vanishing basisCover' vanishing' in
/-- **Derived pushforward restricts, for a morphism of ringed topoi induced by a morphism of sites**
(the hypothesis `hmos`, which the source does not make). Under the other hypotheses of Stacks
0D7V — `f` flat, `f^*` inducing an equivalence `𝒜' ⟶ 𝒜`, the unit `ℱ' ⟶ Rf_*f^*ℱ'` invertible
on `𝒜'`, and both sites satisfying the Olsson--Laszlo hypothesis of Tag 0D6R — the pushforward
`Rf_*` carries `D_𝒜(𝒪)` into `D_{𝒜'}(𝒪')`. The statement for an arbitrary morphism of ringed
topoi is
`Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom.derivedCategoryB_derivedPushforward_obj`.
-/
theorem derivedCategoryB_derivedPushforward_obj :
    letI := f.pullbackTopos_preservesFiniteLimits hmos hf
    letI := f.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
    (∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
      ((DerivedCategory.singleFunctor (SheafOfModules.{w}
          (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M))) →
      ∀ (K : DerivedCategory (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))),
        DerivedCategoryB.derivedCategoryB A K →
          DerivedCategoryB.derivedCategoryB A' ((derivedPushforward f).obj K) := by
  let := f.pullbackTopos_preservesFiniteLimits hmos hf
  let := f.pullbackTopos_preservesFiniteColimits
  let := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
  exact fun hUnit ↦
      (Stacks.Cohomology.OlssonLaszlo.derivedCategoryB_derivedPushforward_obj f hmos A A'
    B basisCover degreeBound coverings vanishing
    B' basisCover' degreeBound' coverings' vanishing' 0
    (fun p F hF ↦ (derivedCategoryBPlus_derivedPushforward_singleFunctor_obj_of_exact
      f A A' hA hEquiv hUnit F hF).2 p)
    (fun p hp F hF ↦
      have := isLE_derivedPushforward_singleFunctor_obj_of_exact f A A' hA hEquiv hUnit F hF
      DerivedCategory.isZero_of_isLE _ 0 (p : ℤ) hp))

/-- **Stacks 0D7V for a morphism of ringed topoi induced by a morphism of sites** (the hypothesis
`hmos`, which the source does not make). Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a flat such
morphism and let `𝒜 ⊂ Mod(𝒪)`, `𝒜' ⊂ Mod(𝒪')` be weak Serre subcategories such that `f^*` induces an
equivalence `𝒜' ⟶ 𝒜` and the unit `ℱ' ⟶ Rf_*f^*ℱ'` is invertible for every `ℱ'` of `𝒜'`, and
assume that `C, 𝒪, 𝒜` and `C', 𝒪', 𝒜'` both satisfy the standing hypothesis of Tag 0D6R. Then
the derived pullback is an **equivalence** `D_{𝒜'}(𝒪') ≌ D_𝒜(𝒪)`.

The hypothesis on the unit propagates from `𝒜'` to all of `D⁺_{𝒜'}(𝒪')` by Tag 0D7T and the
corresponding statement for the counit from `𝒜` to all of `D⁺_𝒜(𝒪)` by Tag 0D7S; the
Olsson--Laszlo hypotheses then carry both from the bounded below subcategories to the whole
derived categories, through Tag 0D6U. The statement for an arbitrary morphism of ringed topoi is
`Stacks.Cohomology.CohomologicalDescent.OfRingedToposHom.derivedPullbackEquivalenceUnbounded`. -/
def derivedPullbackEquivalenceUnbounded
    (hUnit :
      letI := f.pullbackTopos_preservesFiniteLimits hmos hf
      letI := f.pullbackTopos_preservesFiniteColimits
      letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
      ∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
        ((DerivedCategory.singleFunctor (SheafOfModules.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M))) :
    (DerivedCategoryB.derivedCategoryB A').FullSubcategory ≌
      (DerivedCategoryB.derivedCategoryB A).FullSubcategory :=
  letI := f.pullbackTopos_preservesFiniteLimits hmos hf
  letI := f.pullbackTopos_preservesFiniteColimits
  letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
  derivedPullbackEquivalenceUnboundedOfExact f A A' hmos hA hEquiv hUnit
    B basisCover degreeBound coverings vanishing
    B' basisCover' degreeBound' coverings' vanishing'
    (fun K hK ↦ isIso_derivedCounit_app_of_isIso_homology f hmos hf K
      ((DerivedCategoryB.isBoundedBelow_iff_exists_isGE K).1 hK.1) fun q ↦
        isIso_derivedCounit_app_singleFunctor_obj_of_exact f A A' hA hEquiv hUnit _ (hK.2 q))

/-- The identification of the forward functor of `derivedPullbackEquivalenceUnbounded` (Stacks
0D7V for a morphism induced by a morphism of sites) with the restriction of the derived pullback.
-/
theorem derivedPullbackEquivalenceUnbounded_functor
    (hUnit :
      letI := f.pullbackTopos_preservesFiniteLimits hmos hf
      letI := f.pullbackTopos_preservesFiniteColimits
      letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
      ∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
        ((DerivedCategory.singleFunctor (SheafOfModules.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M))) :
    letI := f.pullbackTopos_preservesFiniteLimits hmos hf
    letI := f.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
    (derivedPullbackEquivalenceUnbounded f A A' hmos hf hA hEquiv
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing' hUnit).functor =
      (DerivedCategoryB.derivedCategoryB A).lift
        ((DerivedCategoryB.derivedCategoryB A').ι ⋙ derivedPullback f)
        (fun K ↦ derivedCategoryB_derivedPullback_obj f A A' hmos hf hA K.obj K.property) :=
  rfl

/-- The identification of the quasi-inverse of `derivedPullbackEquivalenceUnbounded` (Stacks 0D7V
for a morphism induced by a morphism of sites) with the restriction of the derived pushforward. -/
theorem derivedPullbackEquivalenceUnbounded_inverse
    (hUnit :
      letI := f.pullbackTopos_preservesFiniteLimits hmos hf
      letI := f.pullbackTopos_preservesFiniteColimits
      letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
      ∀ M, A' M → IsIso ((derivedPullbackPushforwardAdjunctionOfExact f).unit.app
        ((DerivedCategory.singleFunctor (SheafOfModules.{w}
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) 0).obj M))) :
    letI := f.pullbackTopos_preservesFiniteLimits hmos hf
    letI := f.pullbackTopos_preservesFiniteColimits
    letI := pullbackOnHomotopy_hasLeftDerivedFunctor_of_exact f
    (derivedPullbackEquivalenceUnbounded f A A' hmos hf hA hEquiv
      B basisCover degreeBound coverings vanishing
      B' basisCover' degreeBound' coverings' vanishing' hUnit).inverse =
      (DerivedCategoryB.derivedCategoryB A').lift
        ((DerivedCategoryB.derivedCategoryB A).ι ⋙ derivedPushforward f)
        (fun K ↦ derivedCategoryB_derivedPushforward_obj f A A' hmos hf hA hEquiv
          B basisCover degreeBound coverings vanishing
          B' basisCover' degreeBound' coverings' vanishing' hUnit K.obj K.property) :=
  rfl

end Descent

end Stacks.Cohomology.CohomologicalDescent

end
