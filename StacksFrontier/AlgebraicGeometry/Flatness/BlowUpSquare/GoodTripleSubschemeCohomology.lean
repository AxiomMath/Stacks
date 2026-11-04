module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassArbitraryRank.RankLoci
public import StacksFrontier.AlgebraicGeometry.ClosedImmersion.IdealSheafInclusion
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.FiberRankIsomorphismInvariant
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Sheaf
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartDecalageExistence
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartHomologyFreeness
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ChartPullback
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.DivisorRankStrata
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleBlowupGlue
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.GoodTripleSubschemeExistence
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ObstructionSubschemeCohomology
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowUpSquare.ProjectiveHomologyBaseChange
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
public import StacksFrontier.AlgebraicGeometry.Modules.ReducedFiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas

/-!
# The décalage restricted to the closed subscheme of a good triple

Let `(X, D, M)` be a triple as in Situation 0F8S and let `b : X' ⟶ X` be good for it: the
pullback `D' = b⁻¹D` of the divisor is defined and the pulled-back triple `(X', D', Lb^*M)` is
a good triple.  Let `Q = Lη_{ℐ'}Lb^*M` be the object of Stacks tag 0F8U, let `T ⊆ D'` be the
closed subscheme of Stacks tag 0GTZ for the pulled-back triple — on every affine chart
`(U, A, f, M^•)` with principal determinantal ideals it is cut out in `D' ∩ U = Spec(A ⧸ fA)`
by the total obstruction ideal `J(M^•, f)` of More on Algebra, Tag 0F81 — and let
`j : T ⟶ X'` be its inclusion.  This file proves that the cohomology sheaves of `Lj^*Q` are
finite locally free, with ranks bounded near every point, that their ranks agree with those of
the cohomology sheaves of `Lb^*M` at the points of `T` over the locally free locus of `Lb^*M`
(parts (2) and (3) of Stacks tag 0GTZ) and with those of the cohomology sheaves of `M` at the
points of `T` over the locally free locus `W` of `M`, and that `T` contains `D' ∩ b⁻¹(W)`
scheme-theoretically.  For the morphism `b` of Stacks tag 0GTY this is Stacks tag 0F8X, and the
rank strata of Stacks tag 0F8Y follow.

On a chart `(U, A, f, M^•)` with principal determinantal ideals, `T ∩ U` is `Spec C` with
`C = (A ⧸ fA) ⧸ J(M^•, f)`.  The restriction of `Lη_{ℐ'}Lb^*M` to `U` is the sheaf of the
décalage `η_f M^•` (Stacks tag 0GTV), a strictly perfect complex (Stacks tag 0F7W); so its
derived pullback to `Spec C` is computed termwise, and the cohomology sheaves of `Lj^*Q` restrict
on `Spec C` to the sheaves of the modules `H^n(η_f M^• ⊗_A C)`, which are finite projective by
Tag 0F81.  On a chart whose cohomology modules are finite projective — a chart inside the locally
free locus, or the pullback along `b` of such a chart of `(X, D, M)` compared with a chart with
principal determinantal ideals — the décalage has the same cohomology as `M^•` (More on
Algebra, Tag 0F7P), and the cohomology of a bounded above complex of projectives with projective
cohomology commutes with base change; this computes the ranks.

## Main results

All in the namespace `AlgebraicGeometry.ComplexAndDivisorSituation`.

* `isFiniteLocallyFree_etaDerivedPullbackRestrictHomology`: **Stacks tag 0GTZ, part (2)**.
* `finiteLocallyFreeRank_etaDerivedPullbackRestrictHomology_eq_fiberRank`: **Stacks tag 0GTZ,
  part (3)**.
* `exists_finset_finiteLocallyFreeRank_etaDerivedPullbackRestrictHomology_eq_zero`: the ranks of
  the cohomology sheaves of `Lj^*Q` vanish near every point outside a finite set of degrees.
* `isFiniteLocallyFree_locallyFreeLocusCohomologySheaf`: the cohomology sheaves of `M` are finite
  locally free on the locally free locus `W`.
* `comap_preimage_locallyFreeLocus_eq_bot` and
  `finiteLocallyFreeRank_etaDerivedPullbackRestrictHomology_eq_fiberRank_cohomologySheaf`: parts
  (1) and (3) of Stacks tag 0F8X for every morphism good for the triple.
* `exists_closedSubscheme_etaDerivedPullback_goodBlowupToBase`: **Stacks tag 0F8X**.
* `exists_isClopen_rankStratum_etaDerivedPullback_of_isGoodOver`: **Stacks tag 0F8Y**.

## Implementation notes

The rank of a cohomology sheaf at a point is read as its fibre rank, the dimension over the
residue field of the fibre of the stalk; where the stalk is finite free this is the rank of the
stalk, and for a finite locally free module it is the locally constant rank
`AlgebraicGeometry.Scheme.Modules.finiteLocallyFreeRank`.

The comparisons with the cohomology of `M` are proved for every morphism `b` good for the
triple, of which the morphism of Stacks tag 0GTY is one; the source deduces them for that
morphism from Stacks tag 0F8W, which the argument here does not need: the pullback along `b` of a
chart of `(X, D, M)` inside `W` already has finite projective cohomology.

## References

* [Stacks Project, Tag 0GTZ](https://stacks.math.columbia.edu/tag/0GTZ)
* [Stacks Project, Tag 0F8X](https://stacks.math.columbia.edu/tag/0F8X)
* [Stacks Project, Tag 0F8Y](https://stacks.math.columbia.edu/tag/0F8Y)
* [Stacks Project, Tag 0F81](https://stacks.math.columbia.edu/tag/0F81)
* [Stacks Project, Tag 0F7W](https://stacks.math.columbia.edu/tag/0F7W)
* [Stacks Project, Tag 0F7P](https://stacks.math.columbia.edu/tag/0F7P)
* [Stacks Project, Tag 0GTA](https://stacks.math.columbia.edu/tag/0GTA)
* [Stacks Project, Tag 0GTV](https://stacks.math.columbia.edu/tag/0GTV)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory StrictlyPerfect
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u d

namespace AlgebraicGeometry.ComplexAndDivisorSituation

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteLimits
attribute [local instance] AlgebraicGeometry.RingedSpace.restrictModules_preservesFiniteColimits
attribute [local instance] AlgebraicGeometry.RingedSpace.restrictModules_preservesHomology

variable {S : ComplexAndDivisorSituation.{u, d}}

namespace AffineChart

/-- Pulling back along `U ≅ Spec A` the direct image along `Spec A ≅ U` is the identity. -/
def pushforwardPullbackIsoSpec (C : AffineChart S) :
    (RingedSpace.PseudoCoherence.moduleEquivOfIso C.specIso).functor ⋙
      Scheme.Modules.pullback C.U.2.isoSpec.inv ≅ 𝟭 _ :=
  Functor.isoWhiskerRight (Stacks.Morphisms.pushforwardIsoRestrictInv C.U.2.isoSpec.symm) _ ≪≫
    Functor.isoWhiskerLeft _ (Scheme.Modules.restrictFunctorIsoPullback C.U.2.isoSpec.inv).symm ≪≫
    (Scheme.Modules.restrictFunctorComp C.U.2.isoSpec.inv C.U.2.isoSpec.hom).symm ≪≫
    Scheme.Modules.restrictFunctorCongr C.U.2.isoSpec.inv_hom_id ≪≫
    Scheme.Modules.restrictFunctorId

/-- **An object restricting on a chart to the décalage of the chart, pulled back to
`Spec Γ(X, U)`.**  If the restriction of `K` to the domain of a chart with principal
determinantal ideals is the complex of sheaves of `η_f M^•`, then the derived pullback of `K`
along `Spec Γ(X, U) ⟶ X` is the complex of sheaves `(η_f M^•)^~` on `Spec Γ(X, U)`. -/
def derivedPullbackFromSpecEtaIso (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) (K : DerivedCategory S.X.Modules)
    (e : (RingedSpace.PseudoCoherence.restrictModules S.X.toRingedSpace
        C.U.1).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj C.specEtaComplex) :
    (derivedPullback C.U.2.fromSpec.toLRSHom.toShHom).obj K ≅
      DerivedCategory.Q.obj (((tilde.functor Γ(S.X, C.U)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C.etaComplex) := by
  have hK := RingedSpace.KFlatDerivedPullback.kFlat_of_isStrictlyPerfect _
    (C.isStrictlyPerfect_specEtaComplex hI)
  let F := DerivedCategory.Q.objPreimage K
  let eF : DerivedCategory.Q.obj F ≅ K := DerivedCategory.Q.objObjPreimageIso K
  let R := RingedSpace.PseudoCoherence.restrictModules S.X.toRingedSpace C.U.1
  let ρ := RingedSpace.restrictModulesIsoRestrictFunctor S.X C.U.1
  let eC : ((Scheme.Modules.restrictFunctor (C.U.1 : S.X.Opens).ι).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj F ≅ (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj F :=
    HomologicalComplex.Hom.isoOfComponents
      (fun i => (ρ.app (F.X i)).symm) (fun i j _ => (ρ.inv.naturality (F.d i j)).symm)
  let eR : (Scheme.Modules.restrictFunctor (C.U.1 : S.X.Opens).ι).mapDerivedCategory.obj K ≅
      R.mapDerivedCategory.obj K :=
    (Scheme.Modules.restrictFunctor (C.U.1 : S.X.Opens).ι).mapDerivedCategory.mapIso eF.symm ≪≫
      (Scheme.Modules.restrictFunctor (C.U.1 : S.X.Opens).ι).mapDerivedCategoryFactors.app F ≪≫
      DerivedCategory.Q.mapIso eC ≪≫
      (R.mapDerivedCategoryFactors.app F).symm ≪≫ R.mapDerivedCategory.mapIso eF
  exact ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
      C.U.2.isoSpec.inv.toLRSHom.toShHom (C.U.1 : S.X.Opens).ι.toLRSHom.toShHom).app K).symm ≪≫
    (derivedPullback C.U.2.isoSpec.inv.toLRSHom.toShHom).mapIso
      ((Scheme.Modules.derivedRestrictIsoDerivedPullback (C.U.1 : S.X.Opens).ι).app K).symm ≪≫
    (derivedPullback C.U.2.isoSpec.inv.toLRSHom.toShHom).mapIso eR ≪≫
    (derivedPullback C.U.2.isoSpec.inv.toLRSHom.toShHom).mapIso e ≪≫
    Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat _ _ hK ≪≫
    DerivedCategory.Q.mapIso (HomologicalComplex.Hom.isoOfComponents
      (fun i => C.pushforwardPullbackIsoSpec.app ((tilde.functor Γ(S.X, C.U)).obj
        (C.etaComplex.X i)))
      (fun i j _ => (C.pushforwardPullbackIsoSpec.hom.naturality
        ((tilde.functor Γ(S.X, C.U)).map (C.etaComplex.d i j))).symm))

/-- **The cohomology of the derived pullback to an affine scheme mapping into a chart.**  In the
situation of `derivedPullbackFromSpecEtaIso`, let `g : Spec R ⟶ X` factor as `Spec ψ` followed
by `Spec Γ(X, U) ⟶ X`.  The cohomology sheaves of `Lg^*K` are the sheaves of the cohomology
modules of `η_f M^• ⊗_{Γ(X, U)} R`: derived pullback of a strictly perfect complex is computed
termwise, the sheaf of a base change is the pullback of the sheaf, and the sheaf functor is
exact. -/
def homologyDerivedPullbackSpecIso (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) (K : DerivedCategory S.X.Modules)
    (e : (RingedSpace.PseudoCoherence.restrictModules S.X.toRingedSpace
        C.U.1).mapDerivedCategory.obj K ≅ DerivedCategory.Q.obj C.specEtaComplex)
    {R : CommRingCat.{u}} (ψ : Γ(S.X, C.U) ⟶ R) (g : Spec R ⟶ S.X)
    (hg : g = Spec.map ψ ≫ C.U.2.fromSpec) (n : ℤ) :
    (DerivedCategory.homologyFunctor (Spec R).Modules n).obj
        ((derivedPullback g.toLRSHom.toShHom).obj K) ≅
      (tilde.functor R).obj ((((ModuleCat.extendScalars ψ.hom).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj C.etaComplex).homology n) := by
  subst hg
  let L := ((ModuleCat.extendScalars ψ.hom).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    C.etaComplex
  have hbdd : {i : ℤ | ¬ Limits.IsZero (C.etaComplex.X i)}.Finite :=
    C.complex.bounded.subset fun _ hi hr => hi (C.isZero_etaComplex_X hr)
  have hK := RingedSpace.KFlatDerivedPullback.kFlat_of_isStrictlyPerfect _
    (Stacks.AffineTilde.isStrictlyPerfect_tildeComplex_of_projective C.etaComplex hbdd
      (C.finite_projective_etaComplex_X hI))
  exact (DerivedCategory.homologyFunctor (Spec R).Modules n).mapIso
      (((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (Spec.map ψ).toLRSHom.toShHom C.U.2.fromSpec.toLRSHom.toShHom).app K).symm ≪≫
      (derivedPullback (Spec.map ψ).toLRSHom.toShHom).mapIso
        (C.derivedPullbackFromSpecEtaIso hI K e) ≪≫
      Stacks.Cohomology.derivedPullbackIsoPullbackOfKFlat _ _ hK ≪≫
      DerivedCategory.Q.mapIso ((tildePullbackComplexIso _ R ψ).app C.etaComplex) ≪≫
      ((tilde.functor R).mapDerivedCategoryFactors.app L).symm) ≪≫
    ((tilde.functor R).mapDerivedCategoryHomologyIso n).app (DerivedCategory.Q.obj L) ≪≫
    (tilde.functor R).mapIso ((DerivedCategory.homologyFunctorFactors _ n).app L)

end AffineChart

/-- The restriction along an open immersion `g` of the cohomology sheaves of a derived pullback
`Lj^*K` is the cohomology of the derived pullback along `g ≫ j`. -/
def restrictHomologyDerivedPullbackIso {Y Z W : Scheme.{u}} (j : Y ⟶ Z) (g : W ⟶ Y)
    [IsOpenImmersion g] (K : DerivedCategory Z.Modules) (n : ℤ) :
    (Scheme.Modules.restrictFunctor g).obj
        ((DerivedCategory.homologyFunctor Y.Modules n).obj
          ((derivedPullback j.toLRSHom.toShHom).obj K)) ≅
      (DerivedCategory.homologyFunctor W.Modules n).obj
        ((derivedPullback (g ≫ j).toLRSHom.toShHom).obj K) :=
  (((Scheme.Modules.restrictFunctor g).mapDerivedCategoryHomologyIso n).app _).symm ≪≫
    (DerivedCategory.homologyFunctor W.Modules n).mapIso
      ((Scheme.Modules.derivedRestrictIsoDerivedPullback g).app _ ≪≫
        (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
          g.toLRSHom.toShHom j.toLRSHom.toShHom).app K)

open Stacks.Decalage.DirectSumIdeal in
/-- The ring `C = (A ⧸ fA) ⧸ J(M^•, f)` of More on Algebra, Tag 0F81 for an affine chart. -/
abbrev AffineChart.obstructionQuotient (C : AffineChart S) : CommRingCat.{u} :=
  CommRingCat.of ((Γ(S.X, C.U) ⧸ Ideal.span {C.f}) ⧸ etaTotalDirectSumIdeal C.complex C.f)

open Stacks.Decalage.DirectSumIdeal in
/-- The quotient map `A ⟶ (A ⧸ fA) ⧸ J(M^•, f)`. -/
abbrev AffineChart.toObstructionQuotient (C : AffineChart S) :
    Γ(S.X, C.U) ⟶ C.obstructionQuotient :=
  CommRingCat.ofHom ((Ideal.Quotient.mk (etaTotalDirectSumIdeal C.complex C.f)).comp
    (Ideal.Quotient.mk (Ideal.span {C.f})))

section Subscheme

variable (T : S.D.subscheme.IdealSheafData)

namespace AffineChart

open Stacks.Decalage.DirectSumIdeal in
/-- **The coordinate ring of `T ∩ U` is `(A ⧸ fA) ⧸ J(M^•, f)`** when `T` is cut out over the
chart by the obstruction ideal. -/
def subschemeSectionsIso (C : AffineChart S)
    (hT : T.ideal C.divisorAffineOpen = C.obstructionIdeal) :
    Γ(T.subscheme, (C.subschemeAffineOpen T).1) ≅ C.obstructionQuotient :=
  T.subschemeObjIso C.divisorAffineOpen ≪≫
    (Ideal.quotientEquiv (T.ideal C.divisorAffineOpen) (etaTotalDirectSumIdeal C.complex C.f)
      C.divisorQuotEquiv (by
        rw [hT]
        exact (Ideal.map_of_equiv (I := etaTotalDirectSumIdeal C.complex C.f)
          C.divisorQuotEquiv.symm).symm)).toCommRingCatIso

/-- The identification of the coordinate ring of `T ∩ U` with `(A ⧸ fA) ⧸ J(M^•, f)` is
compatible with the restriction of sections along `T ⟶ X`. -/
theorem appLE_comp_subschemeSectionsIso (C : AffineChart S)
    (hT : T.ideal C.divisorAffineOpen = C.obstructionIdeal) :
    (T.subschemeι ≫ S.D.subschemeι).appLE C.U.1 (C.subschemeAffineOpen T).1
        (C.subschemeAffineOpen_le T) ≫ (C.subschemeSectionsIso T hT).hom =
      C.toObstructionQuotient := by
  have h1 : (T.subschemeι ≫ S.D.subschemeι).appLE C.U.1 (C.subschemeAffineOpen T).1
      (C.subschemeAffineOpen_le T) =
        S.D.subschemeι.app C.U.1 ≫ T.subschemeι.app C.divisorAffineOpen.1 := by
    rw [Scheme.Hom.comp_appLE]
    exact congrArg (S.D.subschemeι.app C.U.1 ≫ ·) (Scheme.Hom.appLE_eq_app _)
  rw [h1]
  ext a
  show (Ideal.quotientEquiv (T.ideal C.divisorAffineOpen)
      (Stacks.Decalage.DirectSumIdeal.etaTotalDirectSumIdeal C.complex C.f) C.divisorQuotEquiv
      (by
        rw [hT]
        exact (Ideal.map_of_equiv
          (I := Stacks.Decalage.DirectSumIdeal.etaTotalDirectSumIdeal C.complex C.f)
          C.divisorQuotEquiv.symm).symm)).toCommRingCatIso.hom.hom
        ((T.subschemeObjIso C.divisorAffineOpen).hom.hom
          ((T.subschemeι.app C.divisorAffineOpen.1).hom ((S.D.subschemeι.app C.U.1).hom a))) = _
  have h2 : (T.subschemeObjIso C.divisorAffineOpen).hom.hom
      ((T.subschemeι.app C.divisorAffineOpen.1).hom ((S.D.subschemeι.app C.U.1).hom a)) =
        Ideal.Quotient.mk (T.ideal C.divisorAffineOpen) ((S.D.subschemeι.app C.U.1).hom a) :=
    RingHom.congr_fun
      (Stacks.ClosedImmersion.subschemeObjIso_hom_comp_subschemeι_app T C.divisorAffineOpen) _
  rw [h2]
  exact congrArg (Ideal.Quotient.mk
    (Stacks.Decalage.DirectSumIdeal.etaTotalDirectSumIdeal C.complex C.f))
    (C.divisorQuotEquiv.symm_apply_eq.1 (C.divisorQuotEquiv_symm_mk a)).symm

/-- The open immersion `Spec((A ⧸ fA) ⧸ J(M^•, f)) ⟶ T` onto `T ∩ U`. -/
def subschemeChartι (C : AffineChart S)
    (hT : T.ideal C.divisorAffineOpen = C.obstructionIdeal) :
    Spec C.obstructionQuotient ⟶ T.subscheme :=
  Spec.map (C.subschemeSectionsIso T hT).hom ≫ (C.subschemeAffineOpen T).2.fromSpec

/-- The morphism `subschemeChartι` is an open immersion. -/
instance (C : AffineChart S)
    (hT : T.ideal C.divisorAffineOpen = C.obstructionIdeal) :
    IsOpenImmersion (C.subschemeChartι T hT) :=
  haveI := IsAffineOpen.isOpenImmersion_fromSpec (C.subschemeAffineOpen T).2
  inferInstanceAs (IsOpenImmersion (_ ≫ _))

/-- The open immersion onto `T ∩ U`, followed by `T ⟶ X`, is `Spec` of the quotient map
followed by `Spec A ⟶ X`. -/
theorem subschemeChartι_comp (C : AffineChart S)
    (hT : T.ideal C.divisorAffineOpen = C.obstructionIdeal) :
    C.subschemeChartι T hT ≫ T.subschemeι ≫ S.D.subschemeι =
      Spec.map C.toObstructionQuotient ≫ C.U.2.fromSpec := by
  rw [subschemeChartι, Category.assoc, ← IsAffineOpen.SpecMap_appLE_fromSpec
    (T.subschemeι ≫ S.D.subschemeι) C.U.2 (C.subschemeAffineOpen T).2
    (C.subschemeAffineOpen_le T), ← Category.assoc, ← Spec.map_comp,
    C.appLE_comp_subschemeSectionsIso T hT]

/-- Every point of `T` over `U` lies in `T ∩ U`. -/
theorem mem_range_subschemeChartι (C : AffineChart S)
    (hT : T.ideal C.divisorAffineOpen = C.obstructionIdeal) {t : T.subscheme}
    (ht : T.subschemeι t ∈ S.D.subschemeι ⁻¹ᵁ C.U.1) :
    t ∈ Set.range (C.subschemeChartι T hT) := by
  have hA : IsAffineOpen (T.subschemeι ⁻¹ᵁ C.divisorAffineOpen.1) :=
    T.isAffineOpen_preimage_subschemeι C.divisorAffineOpen
  obtain ⟨z, rfl⟩ : t ∈ Set.range hA.fromSpec := by
    rw [hA.range_fromSpec]
    exact ht
  refine ⟨Spec.map (C.subschemeSectionsIso T hT).inv z, ?_⟩
  show hA.fromSpec ((Spec.map (C.subschemeSectionsIso T hT).inv ≫
    Spec.map (C.subschemeSectionsIso T hT).hom) z) = _
  rw [← Spec.map_comp, Iso.hom_inv_id, Spec.map_id]
  rfl

end AffineChart

end Subscheme

private theorem isoSpec_hom_isoSpec_inv_apply {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : Spec Γ(X, U)) : hU.isoSpec.hom (hU.isoSpec.inv x) = x := by
  show (hU.isoSpec.inv ≫ hU.isoSpec.hom) x = x
  rw [Iso.inv_hom_id]
  rfl

/-! ### Charts with projective cohomology -/

namespace AffineChart

/-- The complex of a chart and its décalage are bounded above. -/
theorem exists_isStrictlyLE (C : AffineChart S) :
    ∃ bd : ℤ, C.complex.toCochainComplex.IsStrictlyLE bd ∧ C.etaComplex.IsStrictlyLE bd := by
  obtain ⟨bd, hbd⟩ := C.complex.bounded.bddAbove
  have hr : ∀ i, bd < i → C.complex.rank i = 0 := fun i hi =>
    not_not.mp fun h => (hbd h).not_gt hi
  refine ⟨bd, ?_, ?_⟩
  · rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    rw [BoundedComplex.toCochainComplex_X, hr i hi]
    exact ModuleCat.isZero_of_subsingleton _
  · rw [CochainComplex.isStrictlyLE_iff]
    exact fun i hi => C.isZero_etaComplex_X (hr i hi)

/-- The terms of the complex of a chart are projective. -/
instance projective_complex_X (C : AffineChart S) (i : ℤ) :
    Projective (C.complex.toCochainComplex.X i) := by
  rw [BoundedComplex.toCochainComplex_X]
  infer_instance

/-- The equation of the divisor is a nonzerodivisor on the terms of the complex of a chart. -/
theorem isSMulRegular_complex_X (C : AffineChart S) (i : ℤ) :
    IsSMulRegular (C.complex.toCochainComplex.X i) C.f := by
  rw [BoundedComplex.toCochainComplex_X]
  exact Module.Flat.isSMulRegular_of_isRegular C.regular

/-- The cohomology of the base change of a chart with projective cohomology is the base change of
its cohomology. -/
private theorem nonempty_homology_baseChange_iso (C : AffineChart S) {B : Type u} [CommRing B]
    (φ : Γ(S.X, C.U) →+* B)
    (hproj : ∀ k, Module.Projective Γ(S.X, C.U) (C.complex.toCochainComplex.homology k))
    (k : ℤ) :
    Nonempty ((C.complex.baseChange φ).toCochainComplex.homology k ≅
      (ModuleCat.extendScalars φ).obj (C.complex.toCochainComplex.homology k)) := by
  obtain ⟨bd, hbd, -⟩ := C.exists_isStrictlyLE
  have hH : ∀ i, Projective (C.complex.toCochainComplex.homology i) := fun i =>
    (IsProjective.iff_projective (R := Γ(S.X, C.U)) _).mp (hproj i)
  exact ⟨HomologicalComplex.homologyMapIso
      (Stacks.Eta.DeterminantalIdeal.baseChangeCochainIso φ C.complex).symm k ≪≫
    CochainComplex.mapHomologyIsoOfProjective C.complex.toCochainComplex bd
      (ModuleCat.extendScalars φ) k⟩

/-- **Comparing a chart with a chart with principal determinantal ideals.**  Let `(X, D, M)` be a
good triple and let `(U₂, A₂, f₂, M₂^•)` be an affine chart all of whose cohomology modules are
projective.  Every point of `D ∩ U₂` lies in a chart `(U, A, f, M^•)` with principal determinantal
ideals and `U ⊆ U₂`, whose cohomology is the base change of that of `M₂^•`. -/
theorem exists_principal_chart_homology_iso (hS : S.IsGoodTriple) (C₂ : AffineChart S)
    (hproj : ∀ k, Module.Projective Γ(S.X, C₂.U) (C₂.complex.toCochainComplex.homology k))
    {y : S.X} (hyD : y ∈ S.D.supportSet) (hy : y ∈ (C₂.U.1 : Set S.X)) :
    ∃ (C : AffineChart S) (_ : ∀ i, (C.determinantalIdeal i).IsPrincipal)
      (hle : (C.U.1 : S.X.Opens) ≤ C₂.U.1), y ∈ (C.U.1 : Set S.X) ∧
      ∀ k, Nonempty (C.complex.toCochainComplex.homology k ≅
        (ModuleCat.extendScalars (S.X.presheaf.map (homOfLE hle).op).hom).obj
          (C₂.complex.toCochainComplex.homology k)) := by
  obtain ⟨C', hyC', hI'⟩ := hS y hyD
  obtain ⟨g, hgle, hyg⟩ := C'.U.2.exists_basicOpen_le (V := C₂.U.1) ⟨y, hy⟩ hyC'
  refine ⟨C'.restrictBasicOpen g, fun i => C'.isPrincipal_restrict_determinantalIdeal _
    (S.X.basicOpen_le g) (hI' i), hgle, hyg, fun k => ?_⟩
  obtain ⟨e⟩ := Stacks.Duality.nonempty_iso_of_nonempty_iso_tilde (S.X.affineBasicOpen g).2
    (representsDerivedIso (C'.restrictBasicOpen g))
    (representsDerivedIso (C₂.restrict (S.X.affineBasicOpen g) hgle))
  exact ⟨((DerivedCategory.homologyFunctorFactors _ k).app _).symm ≪≫
    (DerivedCategory.homologyFunctor _ k).mapIso e ≪≫
    (DerivedCategory.homologyFunctorFactors _ k).app _ ≪≫
    (C₂.nonempty_homology_baseChange_iso _ hproj k).some⟩

/-- The fibre rank of a cohomology sheaf of `M` at a point of a chart is the fibre rank there of
the sheaf associated with the corresponding cohomology module of the chart's complex. -/
theorem fiberRank_cohomologySheaf (C : AffineChart S) (n : ℤ) (u : C.U.1.toScheme) :
    Scheme.Modules.fiberRank (S.cohomologySheaf n) (C.U.1.ι u) =
      Scheme.Modules.fiberRank (tilde (C.complex.toCochainComplex.homology n))
        (C.U.2.isoSpec.hom u) :=
  (Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict _ _ u).symm.trans
    ((Scheme.Modules.fiberRank_eq_of_iso (C.chartHomologyIso n) u).trans
      (Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict _ _ u))

/-- **On a chart contained in the locally free locus the cohomology modules of the chart's
complex are finite projective**: they are free at every prime, and a bounded complex of finite
projective modules whose cohomology is free at every maximal ideal has finite projective
cohomology. -/
theorem finite_projective_homology_of_le_locallyFreeLocus (C : AffineChart S)
    (hW : (C.U.1 : S.X.Opens) ≤ S.locallyFreeLocus) (k : ℤ) :
    Module.Finite Γ(S.X, C.U) (C.complex.toCochainComplex.homology k) ∧
      Module.Projective Γ(S.X, C.U) (C.complex.toCochainComplex.homology k) := by
  obtain ⟨bd, hbd, -⟩ := C.exists_isStrictlyLE
  refine CochainComplex.finite_projective_homology_of_free_localization _ bd (fun i => ?_)
    (fun i m hm => ?_) k
  · rw [BoundedComplex.toCochainComplex_X]
    exact ⟨inferInstance, inferInstance⟩
  · let x : C.U.1.toScheme := C.U.2.isoSpec.inv ⟨m, hm.isPrime⟩
    have hx : C.U.2.primeIdealOf x = ⟨m, hm.isPrime⟩ := isoSpec_hom_isoSpec_inv_apply C.U.2 _
    have := C.free_localizedModule_homology_of_subset_cohomologyFiniteFreeLocus
      (fun y hy ↦ hW hy) x i
    rwa [hx] at this

open Stacks.Decalage.DirectSumIdeal in
/-- **The total obstruction ideal of a chart with finite projective cohomology vanishes.**  At a
maximal ideal containing `f` the cohomology of the chart's complex is free, so the obstruction
ideal localizes to zero by More on Algebra, Tag 0F81; at a maximal ideal not containing `f` the
whole of `A ⧸ fA` localizes to zero. -/
theorem etaTotalDirectSumIdeal_eq_bot_of_finite_projective (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    (hproj : ∀ k, Module.Finite Γ(S.X, C.U) (C.complex.toCochainComplex.homology k) ∧
      Module.Projective Γ(S.X, C.U) (C.complex.toCochainComplex.homology k)) :
    etaTotalDirectSumIdeal C.complex C.f = ⊥ := by
  have hsub : ∀ (P : Ideal Γ(S.X, C.U)) [P.IsMaximal],
      Subsingleton (LocalizedModule P.primeCompl (etaTotalDirectSumIdeal C.complex C.f)) := by
    intro P hP
    by_cases hfP : C.f ∈ P
    · have hfree : ∀ i : ℤ, Module.Free (Localization.AtPrime P)
          (LocalizedModule P.primeCompl (C.complex.toCochainComplex.homology i)) := fun i => by
        obtain ⟨_, _⟩ := hproj i
        exact Module.free_of_flat_of_isLocalRing
      exact subsingleton_localizedModule_etaTotal_of_free_homology C.complex C.f C.regular hI
        P hfP fun i =>
          Stacks.DeterminantalIdeal.FreeHomology.free_homology_baseChange_of_free_localizedModule
            P.primeCompl C.complex hfree i
    · rw [subsingleton_iff_forall_eq 0]
      intro z
      induction z using LocalizedModule.induction_on with
      | _ y s =>
        rw [← LocalizedModule.zero_mk 1, LocalizedModule.mk_eq]
        refine ⟨⟨C.f, hfP⟩, ?_⟩
        have hy : C.f • y = 0 := by
          refine Submodule.coe_eq_zero.mp ?_
          rw [Submodule.coe_smul_of_tower, Algebra.smul_def, Ideal.Quotient.algebraMap_eq,
            Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self C.f), zero_mul]
        simpa [Submonoid.smul_def] using hy
  have : Subsingleton (etaTotalDirectSumIdeal C.complex C.f) :=
    Module.subsingleton_of_localization_maximal
      (fun P _ ↦ LocalizedModule P.primeCompl (etaTotalDirectSumIdeal C.complex C.f))
      (fun P _ ↦ LocalizedModule.mkLinearMap P.primeCompl _) fun P _ ↦ hsub P
  exact Submodule.eq_bot_of_subsingleton

/-- The obstruction ideal of a chart with principal determinantal ideals and finite projective
cohomology vanishes. -/
theorem obstructionIdeal_eq_bot_of_finite_projective (C : AffineChart S)
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    (hproj : ∀ k, Module.Finite Γ(S.X, C.U) (C.complex.toCochainComplex.homology k) ∧
      Module.Projective Γ(S.X, C.U) (C.complex.toCochainComplex.homology k)) :
    C.obstructionIdeal = ⊥ := by
  rw [obstructionIdeal, C.etaTotalDirectSumIdeal_eq_bot_of_finite_projective hI hproj,
    Ideal.map_bot]

end AffineChart

/-- Every point of the locally free locus lies in a chart contained in it. -/
theorem exists_chart_le_locallyFreeLocus (S : ComplexAndDivisorSituation.{u, d}) {x : S.X}
    (hx : x ∈ S.locallyFreeLocus) :
    ∃ C : AffineChart S, x ∈ (C.U.1 : Set S.X) ∧ (C.U.1 : S.X.Opens) ≤ S.locallyFreeLocus := by
  obtain ⟨C₀, hx₀⟩ := S.exists_chart_mem x
  exact C₀.exists_mem_le hx₀ hx

/-- A module isomorphic to the base change of a finite projective module is finite projective. -/
private theorem finite_projective_of_iso_extendScalars {A B : Type u} [CommRing A] [CommRing B]
    (ψ : A →+* B) {P : ModuleCat.{u} A} {N : ModuleCat.{u} B}
    (h : Module.Finite A P ∧ Module.Projective A P) (e : N ≅ (ModuleCat.extendScalars ψ).obj P) :
    Module.Finite B N ∧ Module.Projective B N := by
  obtain ⟨_, _⟩ := CochainComplex.finite_projective_extendScalars ψ P h
  exact ⟨Module.Finite.equiv e.toLinearEquiv.symm, Module.Projective.of_equiv e.toLinearEquiv.symm⟩

/-- If the cohomology modules of a chart are finite projective, those of its pullback along a
morphism `b` are their base changes. -/
theorem AffineChart.pullback_homology_iso (C₁ : AffineChart S) {X' : Scheme.{u}} (b : X' ⟶ S.X)
    (hb : Stacks.Divisors.IsPullbackDefined b S.D) (V : X'.affineOpens)
    (hV : (V : X'.Opens) ≤ b ⁻¹ᵁ (C₁.U : S.X.Opens))
    (hproj : ∀ k, Module.Finite Γ(S.X, C₁.U) (C₁.complex.toCochainComplex.homology k) ∧
      Module.Projective Γ(S.X, C₁.U) (C₁.complex.toCochainComplex.homology k)) (k : ℤ) :
    Nonempty ((C₁.pullback b hb V hV).complex.toCochainComplex.homology k ≅
      (ModuleCat.extendScalars (C₁.pullbackRingHom b V hV).hom).obj
        (C₁.complex.toCochainComplex.homology k)) := by
  exact C₁.nonempty_homology_baseChange_iso _ (fun k => (hproj k).2) k

/-- If the cohomology modules of a chart are finite projective, so are those of its pullback
along a morphism `b`. -/
theorem AffineChart.projective_pullback_homology (C₁ : AffineChart S) {X' : Scheme.{u}}
    (b : X' ⟶ S.X) (hb : Stacks.Divisors.IsPullbackDefined b S.D) (V : X'.affineOpens)
    (hV : (V : X'.Opens) ≤ b ⁻¹ᵁ (C₁.U : S.X.Opens))
    (hproj : ∀ k, Module.Finite Γ(S.X, C₁.U) (C₁.complex.toCochainComplex.homology k) ∧
      Module.Projective Γ(S.X, C₁.U) (C₁.complex.toCochainComplex.homology k)) (k : ℤ) :
    Module.Projective Γ((S.pullback b hb).X, (C₁.pullback b hb V hV).U)
      ((C₁.pullback b hb V hV).complex.toCochainComplex.homology k) :=
  (finite_projective_of_iso_extendScalars _ (hproj k)
    (C₁.pullback_homology_iso b hb V hV hproj k).some).2

/-- **The cohomology sheaves of `M` are finite locally free on the locally free locus.**  On a
chart contained in `W` the cohomology modules of the chart's complex are finite projective, so
the cohomology sheaves of `M` are finite locally free there. -/
theorem isFiniteLocallyFree_locallyFreeLocusCohomologySheaf
    (S : ComplexAndDivisorSituation.{u, d}) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (S.locallyFreeLocusCohomologySheaf n) := by
  choose C hxC hCW using fun w : S.locallyFreeLocus.toScheme =>
    S.exists_chart_le_locallyFreeLocus w.2
  refine (Scheme.Modules.isFiniteLocallyFree_iff _).mp
    (Stacks.Modules.isFiniteLocallyFree_of_openCover _
      (Scheme.Cover.mkOfCovers S.locallyFreeLocus.toScheme (fun w => (C w).U.1.toScheme)
        (fun w => S.X.homOfLE (hCW w))
        (fun w => ⟨w, ⟨w.1, hxC w⟩, by rw [Scheme.homOfLE_apply']; rfl⟩)
        fun w => inferInstance) fun w => ?_)
  obtain ⟨hfin, hproj⟩ := (C w).finite_projective_homology_of_le_locallyFreeLocus (hCW w) n
  have h₁ := (Stacks.Modules.tilde_isFiniteLocallyFree_iff_module _ _).mpr
    ((Module.isFiniteLocallyFree_iff_finite_projective _ _).mpr ⟨hfin, hproj⟩)
  have h₂ := ((Scheme.Modules.isFiniteLocallyFree_iff _).mpr h₁).restrict (C w).U.2.isoSpec.hom
  refine (Scheme.Modules.isFiniteLocallyFree_iff _).mpr
    (SheafOfModules.IsFiniteLocallyFree.of_iso ?_
      (h := (Scheme.Modules.isFiniteLocallyFree_iff _).mp h₂))
  exact ((C w).chartHomologyIso n).symm ≪≫
    (Scheme.Modules.restrictFunctorCongr (S.X.homOfLE_ι (hCW w))).symm.app _ ≪≫
    (Scheme.Modules.restrictFunctorComp _ _).app _

section EtaDerivedPullback

variable {X' : Scheme.{u}} (b : X' ⟶ S.X) (hb : Stacks.Divisors.IsPullbackDefined b S.D)
  (T : (S.pullback b hb).D.subscheme.IdealSheafData)

/-- **The cohomology sheaves of `Lj^*Q` on `T ∩ U`.**  On a chart of the pulled-back triple
with principal determinantal ideals, the cohomology sheaves of `Lj^*Q` restrict on
`T ∩ U = Spec C` to the sheaves of the cohomology modules of `η_f M^• ⊗_A C`: the restriction of
`Q` to the chart is the complex of the algebraic décalage
(`AlgebraicGeometry.ComplexAndDivisorSituation.ChartDecalage.nonempty_iso`). -/
theorem AffineChart.nonempty_restrictEtaDerivedPullbackHomologyIso
    (C : AffineChart (S.pullback b hb)) (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    (hT : T.ideal C.divisorAffineOpen = C.obstructionIdeal) (n : ℤ) :
    Nonempty ((Scheme.Modules.restrictFunctor (C.subschemeChartι T hT)).obj
        (S.etaDerivedPullbackRestrictHomology b hb
          (T.subschemeι ≫ (S.pullback b hb).D.subschemeι) n) ≅
      (tilde.functor C.obstructionQuotient).obj
        ((((ModuleCat.extendScalars C.toObstructionQuotient.hom).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj C.etaComplex).homology n)) := by
  obtain ⟨e⟩ := ((S.pullback b hb).chartDecalage_of_derivedEta
    (Stacks.Divisors.Eta.derivedEtaData (S.D.comap b))).nonempty_iso C hI
  exact ⟨restrictHomologyDerivedPullbackIso _ _ _ n ≪≫
    C.homologyDerivedPullbackSpecIso hI (S.etaDerivedPullbackObject b hb) e
      C.toObstructionQuotient _ (C.subschemeChartι_comp T hT) n⟩

variable {b hb T}

/-- **Stacks tag 0GTZ, part (2).**  Let `(X, D, M)` be a triple, let `b : X' ⟶ X` be a
morphism along which the pullback `D'` of the divisor is defined and the pulled-back triple
`(X', D', Lb^*M)` is good, and let `T ⊆ D'` be the closed subscheme cut out on every chart with
principal determinantal ideals by the obstruction ideal of More on Algebra, Tag 0F81.  Then the
cohomology sheaves of `Lj^*Lη_{ℐ'}Lb^*M` are finite locally free, `j : T ⟶ X'` being the
inclusion.

On a chart with principal determinantal ideals they are the sheaves of the cohomology modules of
`η_f M^• ⊗_A C`, `C = (A ⧸ fA) ⧸ J(M^•, f)`, which are finite projective by Tag 0F81; such charts
cover `T`, the pulled-back triple being good. -/
@[stacks 0GTZ "part (2)"]
theorem isFiniteLocallyFree_etaDerivedPullbackRestrictHomology
    (hS : (S.pullback b hb).IsGoodTriple)
    (hT : ∀ C : AffineChart (S.pullback b hb), (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
      T.ideal C.divisorAffineOpen = C.obstructionIdeal) (n : ℤ) :
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (S.etaDerivedPullbackRestrictHomology b hb
        (T.subschemeι ≫ (S.pullback b hb).D.subschemeι) n) := by
  choose C hI ht using fun t : T.subscheme =>
    (S.pullback b hb).exists_good_chart_mem_preimage hS (T.subschemeι t)
  refine (Scheme.Modules.isFiniteLocallyFree_iff _).mp
    (Stacks.Modules.isFiniteLocallyFree_of_openCover _
      (Scheme.Cover.mkOfCovers T.subscheme (fun t => Spec (C t).obstructionQuotient)
        (fun t => (C t).subschemeChartι T (hT _ (hI t)))
        (fun t => ⟨t, (C t).mem_range_subschemeChartι T (hT _ (hI t)) (ht t)⟩)
        fun t => inferInstance) fun t => ?_)
  refine (Scheme.Modules.isFiniteLocallyFree_iff _).mpr ?_
  obtain ⟨hfin, hproj⟩ :=
    Stacks.Decalage.DirectSumIdeal.finite_projective_etaHomology_quotient_etaTotalDirectSumIdeal
      (C t).complex (C t).f (C t).regular (hI t) n
  obtain ⟨e⟩ :=
    (C t).nonempty_restrictEtaDerivedPullbackHomologyIso b hb T (hI t) (hT _ (hI t)) n
  exact SheafOfModules.IsFiniteLocallyFree.of_iso e.symm
    (h := (Stacks.Modules.tilde_isFiniteLocallyFree_iff_module _ _).mpr
      ((Module.isFiniteLocallyFree_iff_finite_projective _ _).mpr ⟨hfin, hproj⟩))

/-- **The ranks of the cohomology sheaves of `Lj^*Q` are locally bounded**: near every point
of `T` all but finitely many of them vanish, namely on a chart with principal determinantal
ideals all those in the degrees in which the chart's complex vanishes. -/
theorem exists_finset_finiteLocallyFreeRank_etaDerivedPullbackRestrictHomology_eq_zero
    (hS : (S.pullback b hb).IsGoodTriple)
    (hT : ∀ C : AffineChart (S.pullback b hb), (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
      T.ideal C.divisorAffineOpen = C.obstructionIdeal) (t : T.subscheme) :
    ∃ V : T.subscheme.Opens, t ∈ V ∧ ∃ s : Finset ℤ, ∀ n ∉ s, ∀ v ∈ V,
      @Scheme.Modules.finiteLocallyFreeRank T.subscheme
        (S.etaDerivedPullbackRestrictHomology b hb
          (T.subschemeι ≫ (S.pullback b hb).D.subschemeι) n)
        (S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology hS hT n) v = 0 := by
  obtain ⟨C, hI, ht⟩ := (S.pullback b hb).exists_good_chart_mem_preimage hS (T.subschemeι t)
  refine ⟨(C.subschemeChartι T (hT C hI)).opensRange,
    C.mem_range_subschemeChartι T (hT C hI) ht, C.complex.bounded.toFinset,
    fun n hn v hv => ?_⟩
  obtain ⟨z, rfl⟩ := hv
  have hr : C.complex.rank n = 0 := by
    simpa only [Set.Finite.mem_toFinset, Set.mem_ofPred_eq, not_not] using hn
  let K := ((ModuleCat.extendScalars C.toObstructionQuotient.hom).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj C.etaComplex
  have hH : Limits.IsZero (K.homology n) := (K.sc n).isZero_homology_of_isZero_X₂
    ((ModuleCat.extendScalars C.toObstructionQuotient.hom).map_isZero (C.isZero_etaComplex_X hr))
  let F := S.etaDerivedPullbackRestrictHomology b hb
    (T.subschemeι ≫ (S.pullback b hb).D.subschemeι) n
  obtain ⟨e⟩ := C.nonempty_restrictEtaDerivedPullbackHomologyIso b hb T hI (hT C hI) n
  calc @Scheme.Modules.finiteLocallyFreeRank T.subscheme F
        (S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology hS hT n)
        (C.subschemeChartι T (hT C hI) z)
      = Scheme.Modules.fiberRank F (C.subschemeChartι T (hT C hI) z) :=
        (@Stacks.Chow.fiberRank_eq_moduleRank _ F
          (S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology hS hT n) _).symm
    _ = Scheme.Modules.fiberRank (F.restrict (C.subschemeChartι T (hT C hI))) z :=
        (Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict _ F z).symm
    _ = Scheme.Modules.fiberRank ((tilde.functor C.obstructionQuotient).obj (K.homology n)) z :=
        Scheme.Modules.fiberRank_eq_of_iso e z
    _ = 0 := Scheme.Modules.fiberRank_eq_zero_of_subsingleton_stalk _ _
        (subsingleton_moduleStalk_of_isZero
          ((tilde.functor C.obstructionQuotient).map_isZero hH) z)

/-- **The fibre rank of `H^n(Li^*Q)` on a chart with principal determinantal ideals and
projective cohomology**: it is the fibre rank of the sheaf associated with the base change of the
cohomology of the chart's complex to the coordinate ring of `T ∩ U`. -/
theorem fiberRank_etaDerivedPullbackRestrictHomology_eq (C : AffineChart (S.pullback b hb))
    (hI : ∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal)
    (hT : T.ideal C.divisorAffineOpen = C.obstructionIdeal)
    (hproj : ∀ k, Module.Projective Γ((S.pullback b hb).X, C.U)
      (C.complex.toCochainComplex.homology k)) (n : ℤ) (z : Spec C.obstructionQuotient) :
    Scheme.Modules.fiberRank (S.etaDerivedPullbackRestrictHomology b hb
        (T.subschemeι ≫ (S.pullback b hb).D.subschemeι) n) (C.subschemeChartι T hT z) =
      Scheme.Modules.fiberRank (tilde ((ModuleCat.extendScalars C.toObstructionQuotient.hom).obj
        (C.complex.toCochainComplex.homology n))) z := by
  obtain ⟨bd, -, hη⟩ := C.exists_isStrictlyLE
  have hX : ∀ i, Projective (C.etaComplex.X i) := fun i =>
    (IsProjective.iff_projective (R := Γ((S.pullback b hb).X, C.U)) _).mp
      (C.finite_projective_etaComplex_X hI i).2
  have e : ∀ k, C.etaComplex.homology k ≃ₗ[Γ((S.pullback b hb).X, C.U)]
      C.complex.toCochainComplex.homology k := fun k =>
    (Stacks.Decalage.Cohomology.nonempty_etaHomologyLinearEquiv_of_isSMulRegular C.f
      C.complex.toCochainComplex C.isSMulRegular_complex_X k
      (Module.Flat.isSMulRegular_of_isRegular (M := C.complex.toCochainComplex.homology k)
        C.regular)).some
  have hH : ∀ k, Projective (C.etaComplex.homology k) := fun k =>
    (IsProjective.iff_projective (R := Γ((S.pullback b hb).X, C.U)) _).mp
      (Module.Projective.of_equiv (e k).symm)
  let F := S.etaDerivedPullbackRestrictHomology b hb
    (T.subschemeι ≫ (S.pullback b hb).D.subschemeι) n
  obtain ⟨eH⟩ := C.nonempty_restrictEtaDerivedPullbackHomologyIso b hb T hI hT n
  calc Scheme.Modules.fiberRank F (C.subschemeChartι T hT z)
      = Scheme.Modules.fiberRank (F.restrict (C.subschemeChartι T hT)) z :=
        (Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict _ F z).symm
    _ = _ := Scheme.Modules.fiberRank_eq_of_iso
        (eH ≪≫ (tilde.functor C.obstructionQuotient).mapIso
          (CochainComplex.mapHomologyIsoOfProjective C.etaComplex bd
            (ModuleCat.extendScalars C.toObstructionQuotient.hom) n ≪≫
            (ModuleCat.extendScalars C.toObstructionQuotient.hom).mapIso
              (e n).toModuleIso)) z

/-- **Stacks tag 0GTZ, part (3).**  In the situation of
`isFiniteLocallyFree_etaDerivedPullbackRestrictHomology`, at a point `t ∈ T` whose image in `X'`
lies in the locally free locus of `Lb^*M`, the rank of `H^n(Lj^*Lη_{ℐ'}Lb^*M)` at `t` is the
rank of `H^n(Lb^*M)` at the image of `t`.

Around that image there is a chart with principal determinantal ideals inside the locally free
locus; its cohomology modules are finite projective, so the décalage has the same cohomology
(More on Algebra, Tag 0F7P) and its cohomology commutes with base change to `C`. -/
@[stacks 0GTZ "part (3)"]
theorem finiteLocallyFreeRank_etaDerivedPullbackRestrictHomology_eq_fiberRank
    (hS : (S.pullback b hb).IsGoodTriple)
    (hT : ∀ C : AffineChart (S.pullback b hb), (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
      T.ideal C.divisorAffineOpen = C.obstructionIdeal) (n : ℤ) (t : T.subscheme)
    (ht : (T.subschemeι ≫ (S.pullback b hb).D.subschemeι) t ∈
      (S.pullback b hb).locallyFreeLocus) :
    @Scheme.Modules.finiteLocallyFreeRank T.subscheme
        (S.etaDerivedPullbackRestrictHomology b hb
          (T.subschemeι ≫ (S.pullback b hb).D.subschemeι) n)
        (S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology hS hT n) t =
      Scheme.Modules.fiberRank ((S.pullback b hb).cohomologySheaf n)
        ((T.subschemeι ≫ (S.pullback b hb).D.subschemeι) t) := by
  obtain ⟨C, hI, hxC, hCW⟩ := (S.pullback b hb).exists_good_chart_le_locallyFreeLocus hS _
    ((S.pullback b hb).D.mem_supportSet_subschemeι (T.subschemeι t)) ht
  obtain ⟨z, rfl⟩ := C.mem_range_subschemeChartι T (hT C hI) (t := t) hxC
  obtain ⟨_, _⟩ := C.finite_projective_homology_of_le_locallyFreeLocus hCW n
  have hpt : (T.subschemeι ≫ (S.pullback b hb).D.subschemeι)
      (C.subschemeChartι T (hT C hI) z) =
        C.U.1.ι (C.U.2.isoSpec.inv (PrimeSpectrum.comap C.toObstructionQuotient.hom z)) := by
    rw [← Scheme.Hom.comp_apply, C.subschemeChartι_comp]
    rfl
  rw [hpt, C.fiberRank_cohomologySheaf n,
    isoSpec_hom_isoSpec_inv_apply C.U.2 (PrimeSpectrum.comap C.toObstructionQuotient.hom z)]
  refine (@Stacks.Chow.fiberRank_eq_moduleRank _ _
    (S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology hS hT n) _).symm.trans ?_
  rw [fiberRank_etaDerivedPullbackRestrictHomology_eq C hI (hT C hI)
    (fun k => (C.finite_projective_homology_of_le_locallyFreeLocus hCW k).2) n z]
  exact fiberRank_tilde_extendScalars C.toObstructionQuotient _ z

/-- Every point of the pulled-back divisor lying over the locally free locus lies in a chart of
the pulled-back triple with principal determinantal ideals whose cohomology is the base change of
the finite projective cohomology of a chart of `(X, D, M)` inside the locally free locus. -/
theorem exists_principal_chart_homology_iso_extendScalars (hS : (S.pullback b hb).IsGoodTriple)
    {y : (S.pullback b hb).X} (hyD : y ∈ (S.pullback b hb).D.supportSet)
    (hx : b y ∈ S.locallyFreeLocus) :
    ∃ (C₁ : AffineChart S) (V' : X'.affineOpens)
      (hVle' : (V' : X'.Opens) ≤ b ⁻¹ᵁ (C₁.U : S.X.Opens))
      (C : AffineChart (S.pullback b hb)) (_ : ∀ i, (C.determinantalIdeal i).IsPrincipal)
      (hle : (C.U.1 : X'.Opens) ≤ V'.1),
      (∀ k, Module.Finite Γ(S.X, C₁.U) (C₁.complex.toCochainComplex.homology k) ∧
        Module.Projective Γ(S.X, C₁.U) (C₁.complex.toCochainComplex.homology k)) ∧
      y ∈ (C.U.1 : Set (S.pullback b hb).X) ∧
      ∀ k, Nonempty (C.complex.toCochainComplex.homology k ≅
        (ModuleCat.extendScalars (C₁.pullbackRingHom b V' hVle' ≫
          (S.pullback b hb).X.presheaf.map (homOfLE hle).op).hom).obj
            (C₁.complex.toCochainComplex.homology k)) := by
  obtain ⟨C₁, hxC₁, hC₁W⟩ := S.exists_chart_le_locallyFreeLocus hx
  have hproj₁ := C₁.finite_projective_homology_of_le_locallyFreeLocus hC₁W
  obtain ⟨_, ⟨V, hV, rfl⟩, hyV, hVle⟩ := X'.isBasis_affineOpens.exists_subset_of_mem_open
    (show y ∈ (b ⁻¹ᵁ C₁.U.1 : Set X') from hxC₁) (b ⁻¹ᵁ C₁.U.1).isOpen
  let V' : X'.affineOpens := ⟨V, hV⟩
  have hVle' : (V' : X'.Opens) ≤ b ⁻¹ᵁ (C₁.U : S.X.Opens) := hVle
  obtain ⟨C, hI, hle, hyC, hiso⟩ := AffineChart.exists_principal_chart_homology_iso hS
    (C₁.pullback b hb V' hVle') (C₁.projective_pullback_homology b hb V' hVle' hproj₁) hyD hyV
  exact ⟨C₁, V', hVle', C, hI, hle, hproj₁, hyC, fun k => ⟨(hiso k).some ≪≫
    (ModuleCat.extendScalars _).mapIso (C₁.pullback_homology_iso b hb V' hVle' hproj₁ k).some ≪≫
      ((ModuleCat.extendScalarsComp _ _).app _).symm⟩⟩

/-- **Stacks tag 0F8X, part (3), for every morphism good for the triple.**  At a point `t ∈ T`
whose image in `X` lies in the locally free locus `W` of `M`, the rank of `H^n(Lj^*Q)` at `t` is
the rank of `H^n(M)` at the image of `t`.

The pullback along `b` of a chart of `(X, D, M)` inside `W` has cohomology the base change of
that of the chart, hence finite projective, and so does a chart with principal determinantal
ideals compared with it on a common open; the ranks are then computed there. -/
theorem finiteLocallyFreeRank_etaDerivedPullbackRestrictHomology_eq_fiberRank_cohomologySheaf
    (hS : (S.pullback b hb).IsGoodTriple)
    (hT : ∀ C : AffineChart (S.pullback b hb), (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
      T.ideal C.divisorAffineOpen = C.obstructionIdeal) (n : ℤ) (t : T.subscheme)
    (hx : ((T.subschemeι ≫ (S.pullback b hb).D.subschemeι) ≫ b) t ∈ S.locallyFreeLocus) :
    @Scheme.Modules.finiteLocallyFreeRank T.subscheme
        (S.etaDerivedPullbackRestrictHomology b hb
          (T.subschemeι ≫ (S.pullback b hb).D.subschemeι) n)
        (S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology hS hT n) t =
      Scheme.Modules.fiberRank (S.cohomologySheaf n)
        (((T.subschemeι ≫ (S.pullback b hb).D.subschemeι) ≫ b) t) := by
  obtain ⟨C₁, V', hVle', C, hI, hle, hproj₁, hyC, hiso⟩ :=
    exists_principal_chart_homology_iso_extendScalars hS
      ((S.pullback b hb).D.mem_supportSet_subschemeι (T.subschemeι t)) hx
  obtain ⟨z, rfl⟩ := C.mem_range_subschemeChartι T (hT C hI) (t := t) hyC
  let φ := C₁.pullbackRingHom b V' hVle'
  let ρ := (S.pullback b hb).X.presheaf.map (homOfLE hle).op
  let ψ := C.toObstructionQuotient
  obtain ⟨_, _⟩ := hproj₁ n
  have eC : ∀ k, C.complex.toCochainComplex.homology k ≅
      (ModuleCat.extendScalars (φ ≫ ρ).hom).obj (C₁.complex.toCochainComplex.homology k) :=
    fun k => (hiso k).some
  have hprojC : ∀ k, Module.Projective Γ((S.pullback b hb).X, C.U)
      (C.complex.toCochainComplex.homology k) := fun k =>
    (finite_projective_of_iso_extendScalars _ (hproj₁ k) (eC k)).2
  have h1 : (T.subschemeι ≫ (S.pullback b hb).D.subschemeι)
      (C.subschemeChartι T (hT C hI) z) = C.U.2.fromSpec (Spec.map ψ z) := by
    rw [← Scheme.Hom.comp_apply, C.subschemeChartι_comp, Scheme.Hom.comp_apply]
  have h2 : C.U.2.fromSpec (Spec.map ψ z) = V'.2.fromSpec (Spec.map ρ (Spec.map ψ z)) :=
    (congrArg (fun f => f (Spec.map ψ z))
      (IsAffineOpen.map_fromSpec V'.2 C.U.2 (homOfLE hle).op)).symm
  have h3 : b (V'.2.fromSpec (Spec.map ρ (Spec.map ψ z))) =
      C₁.U.2.fromSpec (Spec.map φ (Spec.map ρ (Spec.map ψ z))) :=
    (congrArg (fun f => f (Spec.map ρ (Spec.map ψ z)))
      (IsAffineOpen.SpecMap_appLE_fromSpec b C₁.U.2 V'.2 hVle')).symm
  have hpt : ((T.subschemeι ≫ (S.pullback b hb).D.subschemeι) ≫ b)
      (C.subschemeChartι T (hT C hI) z) =
      C₁.U.1.ι (C₁.U.2.isoSpec.inv (PrimeSpectrum.comap (φ ≫ ρ ≫ ψ).hom z)) :=
    (congrArg b (h1.trans h2)).trans h3
  rw [hpt, C₁.fiberRank_cohomologySheaf n,
    isoSpec_hom_isoSpec_inv_apply C₁.U.2 (PrimeSpectrum.comap (φ ≫ ρ ≫ ψ).hom z)]
  refine (@Stacks.Chow.fiberRank_eq_moduleRank _ _
    (S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology hS hT n) _).symm.trans ?_
  rw [fiberRank_etaDerivedPullbackRestrictHomology_eq C hI (hT C hI) hprojC n z]
  refine (Scheme.Modules.fiberRank_eq_of_iso ((tilde.functor _).mapIso
      ((ModuleCat.extendScalars ψ.hom).mapIso (eC n) ≪≫
        ((ModuleCat.extendScalarsComp (φ ≫ ρ).hom ψ.hom).app _).symm)) z).trans ?_
  exact fiberRank_tilde_extendScalars (φ ≫ ρ ≫ ψ) _ z

/-- Every point of the pulled-back divisor lying over the locally free locus lies in a chart of
the pulled-back triple with principal determinantal ideals and finite projective cohomology. -/
theorem exists_principal_chart_finite_projective (hS : (S.pullback b hb).IsGoodTriple)
    {y : (S.pullback b hb).X}
    (hyD : y ∈ (S.pullback b hb).D.supportSet) (hx : b y ∈ S.locallyFreeLocus) :
    ∃ (C : AffineChart (S.pullback b hb)) (_ : ∀ i, (C.determinantalIdeal i).IsPrincipal),
      y ∈ (C.U.1 : Set (S.pullback b hb).X) ∧ ∀ k,
        Module.Finite Γ((S.pullback b hb).X, C.U) (C.complex.toCochainComplex.homology k) ∧
        Module.Projective Γ((S.pullback b hb).X, C.U) (C.complex.toCochainComplex.homology k) := by
  obtain ⟨C₁, V', hVle', C, hI, hle, hproj₁, hyC, hiso⟩ :=
    exists_principal_chart_homology_iso_extendScalars hS hyD hx
  exact ⟨C, hI, hyC, fun k => finite_projective_of_iso_extendScalars _ (hproj₁ k) (hiso k).some⟩

/-- **Stacks tag 0F8X, part (1), for every morphism good for the triple.**  The closed subscheme
`T ⊆ D'` contains `D' ∩ b⁻¹(W)` scheme-theoretically: the ideal of `T` vanishes on it, the
obstruction ideal of a chart with finite projective cohomology being zero. -/
theorem comap_preimage_locallyFreeLocus_eq_bot (hS : (S.pullback b hb).IsGoodTriple)
    (hT : ∀ C : AffineChart (S.pullback b hb), (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
      T.ideal C.divisorAffineOpen = C.obstructionIdeal) :
    T.comap ((S.pullback b hb).D.subschemeι ⁻¹ᵁ (b ⁻¹ᵁ S.locallyFreeLocus)).ι = ⊥ := by
  have hV : ∀ V : (S.pullback b hb).D.subscheme.affineOpens,
      (V.1 : (S.pullback b hb).D.subscheme.Opens) ≤
        (S.pullback b hb).D.subschemeι ⁻¹ᵁ (b ⁻¹ᵁ S.locallyFreeLocus) → T.ideal V = ⊥ := by
    intro V hVW
    refine T.ideal_eq_bot_of_cover_eq_bot
      (fun C : {C : AffineChart (S.pullback b hb) //
          (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) ∧ ∀ k,
            Module.Finite Γ((S.pullback b hb).X, C.U) (C.complex.toCochainComplex.homology k) ∧
            Module.Projective Γ((S.pullback b hb).X, C.U)
              (C.complex.toCochainComplex.homology k)} ↦ C.1.divisorAffineOpen) V
      (fun z ↦ ?_) fun C ↦ ?_
    · obtain ⟨C, hI, hyC, hproj⟩ := exists_principal_chart_finite_projective hS
        ((S.pullback b hb).D.mem_supportSet_subschemeι z.1) (hVW z.2)
      exact ⟨⟨C, hI, hproj⟩, hyC⟩
    · exact (hT C.1 C.2.1).trans (C.1.obstructionIdeal_eq_bot_of_finite_projective C.2.1 C.2.2)
  refine Scheme.IdealSheafData.ext (funext fun V ↦ ?_)
  rw [Scheme.IdealSheafData.ideal_comap_of_isOpenImmersion,
    hV _ (Scheme.Opens.ι_image_le _ V.1), ← RingHom.ker_eq_comap_bot]
  exact RingHom.ker_coe_equiv
    ((((S.pullback b hb).D.subschemeι ⁻¹ᵁ (b ⁻¹ᵁ S.locallyFreeLocus)).ι.appIso
      V.1).symm).commRingCatIsoToRingEquiv

end EtaDerivedPullback

/-! ### Stacks tags 0F8X and 0F8Y -/

section GoodBlowup

variable (S : ComplexAndDivisorSituation.{u, d})

/-- The rank comparison of tag 0F8X, part (3), read against the cohomology sheaves of `M`
restricted to the locally free locus `W`. -/
theorem finiteLocallyFreeRank_etaDerivedPullbackRestrictHomology_eq_locallyFreeLocus
    {X' : Scheme.{u}} {b : X' ⟶ S.X} (hb : S.IsGoodOver b)
    {T : (S.pullback b hb.pullbackDefined).D.subscheme.IdealSheafData}
    (hT : ∀ C : AffineChart (S.pullback b hb.pullbackDefined),
      (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
        T.ideal C.divisorAffineOpen = C.obstructionIdeal) (n : ℤ) (t : T.subscheme)
    (hw : ((T.subschemeι ≫ (S.pullback b hb.pullbackDefined).D.subschemeι) ≫ b) t ∈
      S.locallyFreeLocus) :
    @Scheme.Modules.finiteLocallyFreeRank T.subscheme
        (S.etaDerivedPullbackRestrictHomology b hb.pullbackDefined
          (T.subschemeι ≫ (S.pullback b hb.pullbackDefined).D.subschemeι) n)
        (S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology hb.isGoodTriple hT n) t =
      @Scheme.Modules.finiteLocallyFreeRank S.locallyFreeLocus.toScheme
        (S.locallyFreeLocusCohomologySheaf n)
        (S.isFiniteLocallyFree_locallyFreeLocusCohomologySheaf n) ⟨_, hw⟩ := by
  rw [S.finiteLocallyFreeRank_etaDerivedPullbackRestrictHomology_eq_fiberRank_cohomologySheaf
    hb.isGoodTriple hT n t hw]
  exact (Stacks.FiniteLocallyFree.Reduced.fiberRank_restrict S.locallyFreeLocus.ι
    (S.cohomologySheaf n) ⟨_, hw⟩).symm.trans
    (@Stacks.Chow.fiberRank_eq_moduleRank _ _
      (S.isFiniteLocallyFree_locallyFreeLocusCohomologySheaf n) _)

/-- **Stacks tag 0F8Y.**  Let `b : X' ⟶ X` be good for the triple — for instance the morphism of
Stacks tag 0GTY — let `T ⊆ D'` be the closed subscheme of Stacks tag 0F8X and let
`ρ = (ρ_n)_{n ∈ ℤ}` be ranks.  There is an open and closed `T(ρ) ⊆ T` containing the inverse
image of `W(ρ)`, the rank-`ρ` stratum of the cohomology sheaves of `M` on the locally free locus,
on which `H^n(Lj^*Q)` is free of rank `ρ_n` near every point.

This is `exists_isClopen_rankStratum_etaDerivedPullback`, whose inputs — finite local freeness
and local boundedness of `H^n(Lj^*Q)`, finite local freeness of `H^n(M)` on `W`, and the rank
comparison of tag 0F8X, part (3) — are proved in this file. -/
@[stacks 0F8Y]
theorem exists_isClopen_rankStratum_etaDerivedPullback_of_isGoodOver {X' : Scheme.{u}}
    {b : X' ⟶ S.X} (hb : S.IsGoodOver b)
    {T : (S.pullback b hb.pullbackDefined).D.subscheme.IdealSheafData}
    (hT : ∀ C : AffineChart (S.pullback b hb.pullbackDefined),
      (∀ i : ℤ, (C.determinantalIdeal i).IsPrincipal) →
        T.ideal C.divisorAffineOpen = C.obstructionIdeal) (ρ : ℤ → ℕ) :
    ∃ Tρ : Set T.subscheme, IsClopen Tρ ∧
      (∀ (t : T.subscheme)
        (hw : ((T.subschemeι ≫ (S.pullback b hb.pullbackDefined).D.subschemeι) ≫ b) t ∈
          S.locallyFreeLocus),
        (⟨_, hw⟩ : S.locallyFreeLocus.toScheme) ∈
            Scheme.Modules.rankStratumSet S.locallyFreeLocusCohomologySheaf
              S.isFiniteLocallyFree_locallyFreeLocusCohomologySheaf ρ →
          t ∈ Tρ) ∧
      ∀ (n : ℤ) (t : T.subscheme), t ∈ Tρ →
        ∃ (V : T.subscheme.Opens) (_ : t ∈ V) (I : Type u), Nonempty (I ≃ Fin (ρ n)) ∧
          Nonempty (_root_.SheafOfModules.free.{u} I ≅
            (Scheme.Modules.toRingSheafModule
              (S.etaDerivedPullbackRestrictHomology b hb.pullbackDefined
                (T.subschemeι ≫ (S.pullback b hb.pullbackDefined).D.subschemeι) n)).over V) :=
  S.exists_isClopen_rankStratum_etaDerivedPullback b hb.pullbackDefined T.subschemeι ρ
    (S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology hb.isGoodTriple hT)
    (S.exists_finset_finiteLocallyFreeRank_etaDerivedPullbackRestrictHomology_eq_zero
      hb.isGoodTriple hT)
    S.isFiniteLocallyFree_locallyFreeLocusCohomologySheaf
    (S.finiteLocallyFreeRank_etaDerivedPullbackRestrictHomology_eq_locallyFreeLocus hb hT)

/-- **Stacks tag 0F8X.**  Let `b : X' ⟶ X` be the morphism of Stacks tag 0GTY, `D' = b⁻¹D` and
`Q = Lη_{ℐ'}Lb^*M`, and let `W ⊆ X` be the locally free locus of `M`.  There is a closed
immersion `i : T ⟶ D'` of finite presentation such that
1. `D' ∩ b⁻¹(W) ⊆ T` scheme-theoretically,
2. the cohomology sheaves of `L(i ≫ D' ⟶ X')^*Q` are finite locally free, and
3. at a point `t ∈ T` over `W` the rank of `H^n(L(i ≫ D' ⟶ X')^*Q)` at `t` is the rank of
   `H^n(M)` at the image of `t`.

`T` is the closed subscheme of Stacks tag 0GTZ for the pulled-back triple. -/
@[stacks 0F8X]
theorem exists_closedSubscheme_etaDerivedPullback_goodBlowupToBase :
    ∃ T : (S.pullback S.goodBlowupToBase
        S.isGoodBlowup_goodBlowupToBase.isGoodOver.pullbackDefined).D.subscheme.IdealSheafData,
      LocallyOfFinitePresentation T.subschemeι ∧
      T.comap ((S.pullback S.goodBlowupToBase
          S.isGoodBlowup_goodBlowupToBase.isGoodOver.pullbackDefined).D.subschemeι ⁻¹ᵁ
            (S.goodBlowupToBase ⁻¹ᵁ S.locallyFreeLocus)).ι = ⊥ ∧
      (∀ n : ℤ, AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (S.etaDerivedPullbackRestrictHomology S.goodBlowupToBase
          S.isGoodBlowup_goodBlowupToBase.isGoodOver.pullbackDefined
          (T.subschemeι ≫ (S.pullback S.goodBlowupToBase
            S.isGoodBlowup_goodBlowupToBase.isGoodOver.pullbackDefined).D.subschemeι) n)) ∧
      ∀ (n : ℤ) (t : T.subscheme),
        ((T.subschemeι ≫ (S.pullback S.goodBlowupToBase
          S.isGoodBlowup_goodBlowupToBase.isGoodOver.pullbackDefined).D.subschemeι) ≫
            S.goodBlowupToBase) t ∈ S.locallyFreeLocus →
        Scheme.Modules.fiberRank (S.etaDerivedPullbackRestrictHomology S.goodBlowupToBase
            S.isGoodBlowup_goodBlowupToBase.isGoodOver.pullbackDefined
            (T.subschemeι ≫ (S.pullback S.goodBlowupToBase
              S.isGoodBlowup_goodBlowupToBase.isGoodOver.pullbackDefined).D.subschemeι) n) t =
          Scheme.Modules.fiberRank (S.cohomologySheaf n)
            (((T.subschemeι ≫ (S.pullback S.goodBlowupToBase
              S.isGoodBlowup_goodBlowupToBase.isGoodOver.pullbackDefined).D.subschemeι) ≫
                S.goodBlowupToBase) t) := by
  have hb := S.isGoodBlowup_goodBlowupToBase.isGoodOver
  obtain ⟨T, hT, hfp, -⟩ :=
    (S.pullback _ hb.pullbackDefined).exists_isGoodChartOpen_ideal_eq_obstructionIdeal
      hb.isGoodTriple
  refine ⟨T, hfp, S.comap_preimage_locallyFreeLocus_eq_bot hb.isGoodTriple hT,
    S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology hb.isGoodTriple hT,
    fun n t hw => ?_⟩
  rw [← S.finiteLocallyFreeRank_etaDerivedPullbackRestrictHomology_eq_fiberRank_cohomologySheaf
    hb.isGoodTriple hT n t hw]
  exact @Stacks.Chow.fiberRank_eq_moduleRank _ _
    (S.isFiniteLocallyFree_etaDerivedPullbackRestrictHomology hb.isGoodTriple hT n) _

end GoodBlowup

end AlgebraicGeometry.ComplexAndDivisorSituation

end
