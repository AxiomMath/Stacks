module

public import StacksFrontier.Algebra.Category.Grp.CountableCohomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.PostcomposedTotalRightDerived
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartCohomologyVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartsHaveEnoughObjects
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraAffineTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModuleExtensionByZeroExact
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulesGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePushforwardGlobalSections
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.DerivedPushforwardEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.InductionPrinciple
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisSections
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.LerayForUnboundedSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.AcyclicObject
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsInitialForget
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.BoundedBelowRestriction
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.CategoryTheory.Sites.Simplicial.DerivedSystem
public import StacksFrontier.Homology.DerivedCategory.MapHomologyIso

/-!
# Countable cohomology over the quasi-compact quasi-separated étale objects of a space

Let `X` be a quasi-compact quasi-separated algebraic space and let `L` be an object of `D(𝒪_X)`
whose cohomology sheaves are quasi-coherent and have countable sets of sections over the affine
schemes étale over `X`. Then `H^i(U, L|_U)` is countable for every quasi-compact quasi-separated
`U` étale over `X` and every `i`. This is the argument of Stacks 0CRU: the affine case is Stacks
0BKZ, and the induction principle of Stacks 08GP, whose step is the Mayer–Vietoris triangle of
Stacks 0CRS, spreads it to every quasi-compact quasi-separated étale object.

All names are in the namespace `AlgebraicGeometry.Space`.

## Main definitions

* `derivedGlobalSectionsAb`: the unbounded derived global sections `RΓ(Y, -)` of `𝒪_Y`-modules,
  in abelian groups.
* `totalRightDerivedIsoMapDerivedCategoryOfExact`: the total right derived functor of an exact
  functor is the functor it induces on derived categories.
* `derivedRestrictPushGlobalSectionsIso`: `R(Γ(W, j_*((-)|_Y))) ≅ RΓ(Y, (-)|_Y)` for an étale
  `j : Y ⟶ W`.
* `HasCountableRestrictedCohomology`: countability of the cohomology of the restriction of `L`
  to every algebraic space structure on a presheaf étale over `X`.
* `derivedSectionsAbAt`: the unbounded derived sections `RΓ(v, -)` over an étale chart `v`.
* `derivedGlobalSectionsAbRestrictIsoOfIso`: for a representable `Y` étale over `X`,
  `RΓ(Y, (-)|_Y)` is `RΓ(v, -)` over the corresponding chart, up to the lift of universes.

## Main results

* `hasCountableCohomology_derivedGlobalSectionsAb_of_eds`: the Mayer–Vietoris step for an
  elementary distinguished square.
* `hasCountableRestrictedCohomology_of_affine`: countability on the affine objects of the
  spaces-étale site implies countability on the quasi-compact quasi-separated ones.
* `hasCountableRestrictedCohomology_of_isAffineSpace`: the affine case.
* `hasCountableCohomology_derivedGlobalSectionsAb_restrict`: the statement above.

## References

* [Stacks Project, Tag 0CRU](https://stacks.math.columbia.edu/tag/0CRU)
* [Stacks Project, Tag 0CRS](https://stacks.math.columbia.edu/tag/0CRS)
* [Stacks Project, Tag 08GP](https://stacks.math.columbia.edu/tag/08GP)
* [Stacks Project, Tag 0BKZ](https://stacks.math.columbia.edu/tag/0BKZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AddCommGrpCat (HasCountableCohomology)

universe u

namespace AlgebraicGeometry.Space

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The `𝒪_Y`-modules of an algebraic space are Grothendieck abelian at the universe of the
schemes; restated as an instance for the spelling `Y.1`, `Y.2`. -/
local instance isGrothendieckAbelian_modules' (Y : AlgebraicSpaces B S hS) :
    IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS Y.1 Y.2) :=
  isGrothendieckAbelian_modules B S hS Y.1 Y.2

/-- **`RΓ(Y, -)`**, the unbounded derived global sections of `𝒪_Y`-modules on an algebraic space
`Y`, read in abelian groups. -/
abbrev derivedGlobalSectionsAb (Y : AlgebraicSpaces B S hS) :
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2) ⥤ DerivedCategory AddCommGrpCat.{u + 1} :=
  Stacks.DerivedFunctor.totalRightDerived (globalSectionsAb B S hS Y)

/-- Having countable cohomology is invariant under isomorphism in `D(Ab)`. -/
theorem _root_.AddCommGrpCat.HasCountableCohomology.of_iso
    {E F : DerivedCategory AddCommGrpCat.{u + 1}} (e : E ≅ F) (hE : HasCountableCohomology E) :
    HasCountableCohomology F := fun i =>
  have := hE i
  Countable.of_equiv _ (((DerivedCategory.homologyFunctor AddCommGrpCat.{u + 1} i).mapIso
    e).addCommGroupIsoToAddEquiv).toEquiv

section Exact

variable {A : Type*} [Category* A] [Abelian A] [IsGrothendieckAbelian.{u} A] [EnoughInjectives A]
  [HasDerivedCategory A] {A' : Type*} [Category* A'] [Abelian A'] [HasDerivedCategory A']

/-- The total right derived functor of an exact functor is the functor it induces on derived
categories. -/
def totalRightDerivedIsoMapDerivedCategoryOfExact (F : A ⥤ A') [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] :
    Stacks.DerivedFunctor.totalRightDerived F ≅ F.mapDerivedCategory :=
  letI := Functor.isRightDerivedFunctor_of_inverts
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh
  Functor.rightDerivedUnique _ _
    (Stacks.Cohomology.LerayUnbounded.totalDerivedUnit F) F.mapDerivedCategoryFactorsh.inv
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))

end Exact

/-- **`R(Γ(W, j_*((-)|_Y))) = RΓ(Y, (-)|_Y)`** for an étale morphism `j : Y ⟶ W` of algebraic
spaces: the right derived functor of global sections of the direct image of the restriction is
derived global sections over `Y` after restriction.  Restriction is exact and carries
K-injective complexes to K-injective complexes (Stacks 08FI), and `Γ(W, j_*N) = Γ(Y, N)`. -/
def derivedRestrictPushGlobalSectionsIso {Y W : AlgebraicSpaces B S hS} (j : Y ⟶ W)
    (hj : IsEtale B S hS j.hom) :
    Stacks.DerivedFunctor.totalRightDerived
        ((etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j) ⋙
          globalSectionsAb B S hS W) ≅
      (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory ⋙
        derivedGlobalSectionsAb B S hS Y :=
  (Stacks.Cohomology.LerayUnbounded.derivedCompIso (etaleModulePullback.{u, u} B S hS j hj)
      (globalSectionsAb B S hS Y)
      ((etaleModulePullback.{u, u} B S hS j hj ⋙ modulePushforward B S hS j) ⋙
        globalSectionsAb B S hS W)
      (Functor.isoWhiskerLeft (etaleModulePullback.{u, u} B S hS j hj)
        (globalSectionsModulePushforwardIso B S hS j).symm)
      (fun I hI => isKInjective_etaleModulePullback B S hS j hj
        (etaleModuleLowerShriekAdjunction B S hS j hj) I hI)).symm ≪≫
    Functor.isoWhiskerRight (totalRightDerivedIsoMapDerivedCategoryOfExact _)
      (derivedGlobalSectionsAb B S hS Y)

section MayerVietoris

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

open CategoryTheory.PushforwardMayerVietoris in
/-- **The Mayer–Vietoris step for countability of cohomology.**  For an elementary
distinguished square `(U ⊆ W, V ⟶ W)` and an object `E` of `D(𝒪_W)`, if `H^i(U, E|_U)`,
`H^i(V, E|_V)` and `H^i(U ×_W V, E|_{U ×_W V})` are countable for every `i`, then so is
`H^i(W, E)`.  This is the distinguished triangle of Stacks 0CRS together with the two out of
three property of the countable abelian groups. -/
theorem hasCountableCohomology_derivedGlobalSectionsAb_of_eds
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hU : HasCountableCohomology ((derivedGlobalSectionsAb B S hS (edsOpen B S hS hsq)).obj
      ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E)))
    (hV : HasCountableCohomology ((derivedGlobalSectionsAb B S hS (edsEtale B S hS hsq)).obj
      ((etaleModulePullback.{u, u} B S hS (edsEtaleHom B S hS hsq)
        (isEtale_edsEtaleHom B S hS hsq)).mapDerivedCategory.obj E)))
    (hP : HasCountableCohomology ((derivedGlobalSectionsAb B S hS (edsInter B S hS hsq)).obj
      ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E))) :
    HasCountableCohomology ((derivedGlobalSectionsAb B S hS W).obj E) := by
  obtain ⟨aU, aV, bU, bV, δ, h⟩ := exists_natTrans_mem_distTriang_mapMayerVietoris_of_injective
    (edsAdjOpen B S hS hsq).unit (edsAdjEtale B S hS hsq).unit
    (conjugateEquiv ((edsAdjOpen B S hS hsq).comp (edsLowerShriekAdjOpen B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (conjugateEquiv ((edsAdjEtale B S hS hsq).comp (edsLowerShriekAdjEtale B S hS hsq))
      ((edsAdjInter B S hS hsq).comp (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq)))
    (zero_edsRestrictPushMayerVietoris B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
      (edsLowerShriekAdjEtale B S hS hsq) (edsLowerShriekAdjInter B S hS hsq)
      (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq))
      (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
        (edsLowerShriekAdjInter B S hS hsq))
      (zero_edsShriekMayerVietoris B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
        (edsLowerShriekAdjEtale B S hS hsq) (edsLowerShriekAdjInter B S hS hsq)))
    (globalSectionsAb B S hS W)
    (exists_quasiIso_isKInjective_injective_modules B S hS W.1 W.2)
    (fun M hM => shortExact_edsRestrictPushMayerVietoris_of_injective B S hS hsq
      (edsLowerShriekAdjOpen B S hS hsq) (edsLowerShriekAdjEtale B S hS hsq)
      (edsLowerShriekAdjInter B S hS hsq) M hM)
    (derivedGlobalSectionsAb B S hS W)
    (Stacks.DerivedFunctor.totalRightDerived (edsRestrictPushOpen B S hS hsq ⋙
      globalSectionsAb B S hS W))
    (Stacks.DerivedFunctor.totalRightDerived (edsRestrictPushEtale B S hS hsq ⋙
      globalSectionsAb B S hS W))
    (Stacks.DerivedFunctor.totalRightDerived (edsRestrictPushInter B S hS hsq ⋙
      globalSectionsAb B S hS W))
    (Stacks.Cohomology.LerayUnbounded.totalDerivedUnit _)
    (Stacks.Cohomology.LerayUnbounded.totalDerivedUnit _)
    (Stacks.Cohomology.LerayUnbounded.totalDerivedUnit _)
    (Stacks.Cohomology.LerayUnbounded.totalDerivedUnit _)
    inferInstance inferInstance inferInstance inferInstance
  exact HasCountableCohomology.obj₁ _ (h E)
    ((hU.of_iso ((derivedRestrictPushGlobalSectionsIso B S hS (edsOpenHom B S hS hsq)
      (isEtale_edsOpenHom B S hS hsq)).app E).symm).biprod
    (hV.of_iso ((derivedRestrictPushGlobalSectionsIso B S hS (edsEtaleHom B S hS hsq)
      (isEtale_edsEtaleHom B S hS hsq)).app E).symm))
    (hP.of_iso ((derivedRestrictPushGlobalSectionsIso B S hS (edsInterHom B S hS hsq)
      (isEtale_edsInterHom B S hS hsq)).app E).symm)

end MayerVietoris

section Induction

/-- Countability of the cohomology of the restriction of `L` to a presheaf `Y` over `X`, for
every way of reading `Y` as an algebraic space étale over `X`: the property the induction
principle of Stacks 08GP is run on. -/
def HasCountableRestrictedCohomology (X : AlgebraicSpaces B S hS)
    (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (g : Y ⟶ X.1) : Prop :=
  ∀ (hY : IsAlgebraicSpace B S hS Y) (hg : IsEtale B S hS g),
    letI := etaleModulePullback_additive.{u, u} B S hS
      (U := ⟨Y, hY⟩) (V := X) (ObjectProperty.homMk g) hg
    letI := preservesFiniteLimits_etaleModulePullback B S hS
      (U := ⟨Y, hY⟩) (V := X) (ObjectProperty.homMk g) hg
    letI := preservesFiniteColimits_etaleModulePullback B S hS
      (U := ⟨Y, hY⟩) (V := X) (ObjectProperty.homMk g) hg
    HasCountableCohomology ((derivedGlobalSectionsAb B S hS ⟨Y, hY⟩).obj
      ((etaleModulePullback.{u, u} B S hS
        (X := ⟨Y, hY⟩) (Y := X) (ObjectProperty.homMk g) hg).mapDerivedCategory.obj L))

/-- Restricting in two steps along étale morphisms is restricting along the composite, on
derived categories. -/
def etaleModulePullbackDerivedCompIso {Y W X : AlgebraicSpaces B S hS} (j : Y ⟶ W) (g : W ⟶ X)
    (hj : IsEtale B S hS j.hom) (hg : IsEtale B S hS g.hom)
    (hjg : IsEtale B S hS (j ≫ g).hom) :
    (etaleModulePullback.{u, u} B S hS (j ≫ g) hjg).mapDerivedCategory ≅
      (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory ⋙
        (etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory :=
  CategoryTheory.derivedCompIso _ _ _ (etaleModulePullbackCompIso B S hS j g hj hg hjg).symm

variable {X : AlgebraicSpaces B S hS} (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))

/-- Countability of the cohomology of a restriction, carried along a factorization of the
restricting morphism. -/
theorem hasCountableCohomology_restrict_comp {Y W : AlgebraicSpaces B S hS} (j : Y ⟶ W)
    (hj : IsEtale B S hS j.hom) (gW : W ⟶ X) (hgW : IsEtale B S hS gW.hom) (g : Y ⟶ X)
    (hg : IsEtale B S hS g.hom) (h : j ≫ gW = g)
    (hL : HasCountableCohomology ((derivedGlobalSectionsAb B S hS Y).obj
      ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj L))) :
    HasCountableCohomology ((derivedGlobalSectionsAb B S hS Y).obj
      ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj
        ((etaleModulePullback.{u, u} B S hS gW hgW).mapDerivedCategory.obj L))) := by
  subst h
  exact hL.of_iso ((derivedGlobalSectionsAb B S hS Y).mapIso
    ((etaleModulePullbackDerivedCompIso B S hS j gW hj hgW hg).app L))

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **The induction of Stacks 0CRU.**  Let `X` be a quasi-compact quasi-separated algebraic
space and `L` an object of `D(𝒪_X)`.  If the cohomology of `L|_V` is countable for every affine
object `V` of the spaces-étale site of `X`, then it is countable for every quasi-compact
quasi-separated object.  This is the induction principle of Stacks 08GP, whose step is the
Mayer–Vietoris triangle of Stacks 0CRS
(`AlgebraicGeometry.Space.hasCountableCohomology_derivedGlobalSectionsAb_of_eds`). -/
theorem hasCountableRestrictedCohomology_of_affine (hZ : B.Contains (⊤_ Scheme.{u}))
    (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (haff : ∀ V : SpacesEtale B S hS X, IsAffineSpace B S hS V.1.left.1 →
      HasCountableRestrictedCohomology B S hS X L V.1.left.1 V.1.hom.hom) :
    ∀ Y : SpacesEtale B S hS X, IsQuasiCompactSpace B S hS Y.1.left.1 →
      IsAbsolutelyQuasiSeparated B S hS hZ Y.1.left.1 →
      HasCountableRestrictedCohomology B S hS X L Y.1.left.1 Y.1.hom.hom := by
  refine qcqs_induction_on B S hS hZ X hXqc hXqs (HasCountableRestrictedCohomology B S hS X L)
    haff ?_
  intro W V U f hcomm hsq _ _ _ _ hU hV hP hY hg
  let W' : AlgebraicSpaces B S hS := ⟨W.1.left.1, hY⟩
  let gW : W' ⟶ X := ObjectProperty.homMk W.1.hom.hom
  have hsq' : IsElementaryDistinguishedSquare B S hS W'.2 U f := hsq
  have key : ∀ {Z : AlgebraicSpaces B S hS} (j : Z ⟶ W') (hj : IsEtale B S hS j.hom)
      (g : Z ⟶ X) (h : j ≫ gW = g),
      HasCountableRestrictedCohomology B S hS X L Z.1 g.hom →
      HasCountableCohomology ((derivedGlobalSectionsAb B S hS Z).obj
        ((etaleModulePullback.{u, u} B S hS j hj).mapDerivedCategory.obj
          ((etaleModulePullback.{u, u} B S hS gW hg).mapDerivedCategory.obj L))) := by
    rintro Z j hj - rfl H
    have hjg := isEtale_comp B S hS hj hg
    exact hasCountableCohomology_restrict_comp B S hS L j hj gW hg _ hjg rfl (H Z.2 hjg)
  exact hasCountableCohomology_derivedGlobalSectionsAb_of_eds B S hS hsq'
    ((etaleModulePullback.{u, u} B S hS gW hg).mapDerivedCategory.obj L)
    (key _ (isEtale_edsOpenHom B S hS hsq') _ rfl hU)
    (key _ (isEtale_edsEtaleHom B S hS hsq') _ (ObjectProperty.hom_ext _ hcomm) hV)
    (key _ (isEtale_edsInterHom B S hS hsq') _ rfl hP)

end Induction

section Affine

variable {X : AlgebraicSpaces B S hS}

/-- **Global sections over a representable algebraic space étale over `X` are sections of `X`
over a chart.**  If `e : yoneda T ≅ Y` and `g : Y ⟶ X` is étale, the chart `e⁻¹ : yoneda T ⟶ Y`
is a final object of the small étale site of `Y`, so the global sections of `g^*M` are its
sections there, which are the sections of `M` over the chart `T ⟶ X` obtained by composing
with `g`. -/
def etaleModulePullbackGlobalSectionsAbIsoOfIso {Y : AlgebraicSpaces B S hS}
    {T : BigFppfOver B S hS} (e : yoneda.obj T ≅ Y.1) (g : Y ⟶ X) (hg : IsEtale B S hS g.hom) :
    etaleModulePullback.{u, u} B S hS g hg ⋙ globalSectionsAb B S hS Y ≅
      SheafOfModules.evaluation _
          (Opposite.op ((smallEtalePostcomp B S hS g hg).obj (isoChart B S hS e))) ⋙
        forget₂ _ AddCommGrpCat.{u} ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  Functor.isoWhiskerLeft (etaleModulePullback.{u, u} B S hS g hg)
    (Stacks.Cohomology.SiteModules.globalSectionsFunctorForgetIsoEvaluation
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)
      (Opposite.op (isoChart B S hS e)) (isTerminal_isoChart B S hS e).op)

attribute [local instance] enoughInjectives_modules'
  Stacks.Cohomology.HypercohomologyEdge.evaluation_additive

/-- The universe lift of abelian groups is exact. -/
local instance preservesFiniteColimits_uliftFunctor :
    PreservesFiniteColimits AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  PreservesColimitsOfSize.preservesFiniteColimits.{0, 0} _

/-- The universe lift of abelian groups is exact. -/
local instance preservesFiniteLimits_uliftFunctor :
    PreservesFiniteLimits AddCommGrpCat.uliftFunctor.{u + 1, u} :=
  PreservesLimitsOfSize.preservesFiniteLimits.{0, 0} _

/-- Unbounded derived sections over an étale chart `v` of `X`, read in abelian groups:
`RΓ(v, -) : D(𝒪_X) ⥤ D(Ab)`. -/
abbrev derivedSectionsAbAt (v : SmallEtale B S hS X.1) :
    DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤ DerivedCategory AddCommGrpCat.{u} :=
  Stacks.DerivedFunctor.totalRightDerived
    (SheafOfModules.evaluation
        (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)
        (Opposite.op v) ⋙
      forget₂ _ AddCommGrpCat.{u})

/-- **The cohomology of a representable algebraic space étale over `X` is the cohomology of `X`
over the corresponding chart**: if `e : yoneda T ≅ Y` and `g : Y ⟶ X` is étale, then
`RΓ(Y, (-)|_Y)` is `RΓ(v, -)` for the chart `v = (T ⟶ Y ⟶ X)`, up to the lift of universes. -/
def derivedGlobalSectionsAbRestrictIsoOfIso {Y : AlgebraicSpaces B S hS}
    {T : BigFppfOver B S hS} (e : yoneda.obj T ≅ Y.1) (g : Y ⟶ X) (hg : IsEtale B S hS g.hom) :
    (etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory ⋙
        derivedGlobalSectionsAb B S hS Y ≅
      derivedSectionsAbAt B S hS ((smallEtalePostcomp B S hS g hg).obj (isoChart B S hS e)) ⋙
        AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory :=
  let v := (smallEtalePostcomp B S hS g hg).obj (isoChart B S hS e)
  let ev := SheafOfModules.evaluation
    (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O) (Opposite.op v)
  let G := ev ⋙ forget₂ _ AddCommGrpCat.{u}
  letI : G.Additive := inferInstance
  letI : (G ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u}).Additive := inferInstance
  Functor.isoWhiskerRight (totalRightDerivedIsoMapDerivedCategoryOfExact _).symm _ ≪≫
    Stacks.Cohomology.LerayUnbounded.derivedCompIso (etaleModulePullback.{u, u} B S hS g hg)
      (globalSectionsAb B S hS Y) _ (Iso.refl _)
      (fun I hI => isKInjective_etaleModulePullback B S hS g hg
        (etaleModuleLowerShriekAdjunction B S hS g hg) I hI) ≪≫
    Stacks.DerivedFunctor.totalRightDerivedIsoOfIso _
      (G := G ⋙ AddCommGrpCat.uliftFunctor.{u + 1, u})
      (etaleModulePullbackGlobalSectionsAbIsoOfIso B S hS e g hg) ≪≫
    (Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso G
      AddCommGrpCat.uliftFunctor.{u + 1, u}).symm

/-- **The cohomology over an affine chart of a complex with quasi-coherent cohomology sheaves
is countable as soon as the sections of its cohomology sheaves there are.**  Over an affine
étale chart `v` of `X` the hypercohomology `H^q(v, L)` is the module of sections over `v` of
`H^q(L)`, by Stacks 0BKZ: the cohomology sheaves are quasi-coherent, hence have no higher
cohomology on the affine charts, and the affine charts cover the small étale site. -/
theorem hasCountableCohomology_derivedSectionsAbAt (v : SmallEtale B S hS X.1)
    (hv : IsAffineChart B S hS X.1 v) (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj L).IsQuasicoherentOnSite)
    (hcount : ∀ q : ℤ, Countable (((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj L).val.obj (Opposite.op v))) :
    HasCountableCohomology ((derivedSectionsAbAt B S hS v).obj L) := by
  intro q
  let O := Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O
  have hedge := Stacks.Cohomology.HypercohomologyEdge.isIso_hypercohomologyEdge_app_of_acyclic_cover
    O v L (IsAffineChart B S hS X.1) (hasEnoughObjects_isAffineChart B S hS X.1)
    (fun V hV p hp m => isZero_rightDerived_evaluation_of_isAffineChart B S hS X.1 X.2 _
      (hqc m) V hV p hp) hv q
  let e₁ := (Stacks.Cohomology.SiteCohomologyPresheaf.totalRightDerivedMapDerivedCategoryIso
    (SheafOfModules.evaluation O (Opposite.op v)) (forget₂ _ AddCommGrpCat.{u})).app L
  let e₂ := (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
    (forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op v))) AddCommGrpCat.{u}) q).app
      ((Stacks.Cohomology.HypercohomologyEdge.derivedSections O v).obj L)
  let e₃ := (forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op v))) AddCommGrpCat.{u}).mapIso
    (@asIso _ _ _ _ _ hedge)
  let e := (DerivedCategory.homologyFunctor AddCommGrpCat.{u} q).mapIso e₁.symm ≪≫ e₂ ≪≫ e₃
  have : Countable ((forget₂ (ModuleCat.{u} (O.obj.obj (Opposite.op v))) AddCommGrpCat.{u}).obj
      ((DerivedCategory.homologyFunctor (SheafOfModules O) q ⋙
        SheafOfModules.evaluation O (Opposite.op v)).obj L)) := hcount q
  exact Countable.of_equiv _ e.addCommGroupIsoToAddEquiv.toEquiv.symm

/-- Countable cohomology survives the universe lift of abelian groups. -/
theorem hasCountableCohomology_uliftFunctor_mapDerivedCategory
    {N : DerivedCategory AddCommGrpCat.{u}} (hN : HasCountableCohomology N) :
    HasCountableCohomology (AddCommGrpCat.uliftFunctor.{u + 1, u}.mapDerivedCategory.obj N) :=
  fun q =>
    have := hN q
    let e := (StacksDraft.DerivedCategoryHomology.mapDerivedCategoryHomologyIso
      AddCommGrpCat.uliftFunctor.{u + 1, u} q).app N
    Countable.of_equiv _ (Equiv.ulift.symm.trans e.addCommGroupIsoToAddEquiv.toEquiv.symm)

/-- **The affine case of Stacks 0CRU.**  If `L ∈ D(𝒪_X)` has quasi-coherent cohomology sheaves
whose sections over the affine étale charts of `X` are countable, then the cohomology of `L|_V`
is countable for every affine object `V` of the spaces-étale site of `X`. -/
theorem hasCountableRestrictedCohomology_of_isAffineSpace
    (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj L).IsQuasicoherentOnSite)
    (hcount : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS X.1 X.2) q).obj L).val.obj (Opposite.op v)))
    (V : SpacesEtale B S hS X) (hV : IsAffineSpace B S hS V.1.left.1) :
    HasCountableRestrictedCohomology B S hS X L V.1.left.1 V.1.hom.hom := by
  intro hY hg
  obtain ⟨T, hT, ⟨e⟩⟩ := hV
  let Y : AlgebraicSpaces B S hS := ⟨V.1.left.1, hY⟩
  let g : Y ⟶ X := ObjectProperty.homMk V.1.hom.hom
  let v := (smallEtalePostcomp B S hS g hg).obj (isoChart B S hS e.symm)
  have hv : IsAffineChart B S hS X.1 v := hT
  exact (hasCountableCohomology_uliftFunctor_mapDerivedCategory
    (hasCountableCohomology_derivedSectionsAbAt B S hS v hv L hqc
      fun q => hcount v hv q)).of_iso
    ((derivedGlobalSectionsAbRestrictIsoOfIso B S hS e.symm g hg).app L).symm

end Affine

attribute [-instance] CategoryTheory.Limits.Types.instHasPushoutsType in
/-- **Countable cohomology over the quasi-compact quasi-separated étale objects of a space.**
Let `X` be a quasi-compact quasi-separated algebraic space and let `L` be an object of `D(𝒪_X)`
whose cohomology sheaves are quasi-coherent and have countable sets of sections over the affine
schemes étale over `X`.  Then `H^i(U, L|_U)` is countable for every quasi-compact
quasi-separated `U` étale over `X` and every `i`.

This is the argument of Stacks 0CRU for the groups `H^i(U, -)`: the affine case is Stacks 0BKZ
(`AlgebraicGeometry.Space.hasCountableRestrictedCohomology_of_isAffineSpace`) and the induction
principle of Stacks 08GP, with the Mayer–Vietoris triangle of Stacks 0CRS as its step, spreads
it to every quasi-compact quasi-separated étale object
(`AlgebraicGeometry.Space.hasCountableRestrictedCohomology_of_affine`). -/
theorem hasCountableCohomology_derivedGlobalSectionsAb_restrict (hZ : B.Contains (⊤_ Scheme.{u}))
    (X : AlgebraicSpaces B S hS) (hXqc : IsQuasiCompactSpace B S hS X.1)
    (hXqs : IsAbsolutelyQuasiSeparated B S hS hZ X.1)
    (L : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor
      (Modules.{u, u} B S hS X.1 X.2) q).obj L).IsQuasicoherentOnSite)
    (hcount : ∀ v : SmallEtale B S hS X.1, IsAffineChart B S hS X.1 v → ∀ q : ℤ,
      Countable (((DerivedCategory.homologyFunctor
        (Modules.{u, u} B S hS X.1 X.2) q).obj L).val.obj (Opposite.op v)))
    (U : SpacesEtale B S hS X) (hUqc : IsQuasiCompactSpace B S hS U.1.left.1)
    (hUqs : IsAbsolutelyQuasiSeparated B S hS hZ U.1.left.1) :
    HasCountableCohomology ((derivedGlobalSectionsAb B S hS U.1.left).obj
      ((etaleModulePullback.{u, u} B S hS U.1.hom U.2).mapDerivedCategory.obj L)) :=
  hasCountableRestrictedCohomology_of_affine B S hS L hZ hXqc hXqs
    (hasCountableRestrictedCohomology_of_isAffineSpace B S hS L hqc hcount) U hUqc hUqs
    U.1.left.2 U.2

end AlgebraicGeometry.Space

end
