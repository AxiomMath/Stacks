module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSupportInvariance
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisPushforwardTag
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.PerfectLocalOnSquare
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedVanishingConverse
public import StacksFrontier.Homology.DerivedCategory.IsZero
import StacksCore.Tactic.StacksAttribute

/-!
# Restricting a supported derived object away from its support

Let `X` be an algebraic space over a scheme `S`, let `T ⊆ |X|` and let `E` be an object of
`D(𝒪_X)` supported on `T` in the sense of Stacks 08GF.  If `g : Y ⟶ X` is étale and the image of
`|Y|` in `|X|` misses `T`, then `E|_Y = 0`: restriction is exact, so `Hⁱ(E|_Y) = Hⁱ(E)|_Y`
(`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`), the support of a restriction along an
étale morphism is the inverse image of the support (Stacks 04KB,
`AlgebraicGeometry.Space.supportOfSheaf_toSheaf_etaleModulePullback`), and a module with empty
support vanishes (Stacks 04K5, `AlgebraicGeometry.Space.supportOfSheaf_eq_empty_iff_isZero`).

For an elementary distinguished square `(U ⊆ X, j : V ⟶ X)` with `T = |X| \ |U|` this vanishing is
the step from which the source deduces part (1) of Stacks 08GG; together with part (1) of Stacks
08GV for the extension by zero of `AlgebraicGeometry.Space.edsLowerShriekAdjOpen` and its
companions (`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`) it gives clause (1)(b).

## Main results

* `AlgebraicGeometry.Space.isZero_etaleModulePullback_mapDerivedCategory_of_cohomologySupportedOn`:
  the vanishing of the restriction, for an arbitrary subset `T` of `|X|`.
* `AlgebraicGeometry.Space.isIso_derivedCounit_etaleModuleLowerShriek_of_cohomologySupportedOn`:
  **Stacks 08GG, clause (1)(b)**.
* `AlgebraicGeometry.Space.exists_isIso_derivedRestrictPushEtale_of_cohomologySupportedOn`:
  **Stacks 08GG, clause (1)(a)**, in the existentially quantified form, assuming the Mayer–Vietoris
  short exact sequence (part (1) of Stacks 08GW) and the two vanishing direct images.
* `AlgebraicGeometry.Space.isPerfect_derivedPushforwardOfSupported`: Stacks 08HK from clause
  (2)(b) of Stacks 08GG and the vanishing of `(Rj_*E)|_U`, both taken as hypotheses (Stacks 08HK
  itself is
  `AlgebraicGeometry.Space.isPerfect_rightAdjoint_edsDerivedRestrictEtale_of_cohomologySupportedOn`).

## References

* [Stacks Project, Tag 08GG](https://stacks.math.columbia.edu/tag/08GG)
* [Stacks Project, Tag 08HK](https://stacks.math.columbia.edu/tag/08HK)
* [Stacks Project, Tag 08GF](https://stacks.math.columbia.edu/tag/08GF)
* [Stacks Project, Tag 08GV](https://stacks.math.columbia.edu/tag/08GV)
* [Stacks Project, Tag 08GW](https://stacks.math.columbia.edu/tag/08GW)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 04KB](https://stacks.math.columbia.edu/tag/04KB)
* [Stacks Project, Tag 08GE](https://stacks.math.columbia.edu/tag/08GE)
* [Stacks Project, Tag 08FR](https://stacks.math.columbia.edu/tag/08FR)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] HasDerivedCategory.standard etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback
  smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

/-! ### The vanishing of a restriction away from the support -/

/-- The restriction of an object of `D(𝒪_X)` supported on `T ⊆ |X|` along an étale morphism
`g : Y ⟶ X` whose image on points misses `T` vanishes.

This is Stacks 04K5 together with `Hⁱ(E|_Y) = Hⁱ(E)|_Y`. -/
theorem isZero_etaleModulePullback_mapDerivedCategory_of_cohomologySupportedOn
    {X Y : AlgebraicSpaces B S hS} (T : Set (points B S hS X.1))
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : CohomologySupportedOn B S hS X.1 X.2 T E)
    (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)
    (hgT : Set.range (pointsMap B S hS Y.1 g.hom) ⊆ Tᶜ) :
    IsZero ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E) := by
  rw [DerivedCategory.isZero_iff_forall_isZero_homology]
  intro n
  refine (((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategoryHomologyIso n).app
    E).isZero_iff.mpr ?_
  refine (supportOfSheaf_eq_empty_iff_isZero B S hS Y _).mp ?_
  rw [Functor.comp_obj, supportOfSheaf_toSheaf_etaleModulePullback]
  refine Set.eq_empty_of_forall_notMem fun y hy => ?_
  exact hgT ⟨y, rfl⟩ (hE n hy)

section Square

variable {W : AlgebraicSpaces B S hS} {V : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
  {Uo : Subfunctor W.1} {fV : V ⟶ W.1}
  (hsq : IsElementaryDistinguishedSquare B S hS W.2 Uo fV)

/-- An étale morphism to the ambient space of an elementary distinguished square whose image on
points lies in the open subspace has image missing `T = |X| \ |U|`. -/
theorem range_pointsMap_subset_compl_edsComplementPoints {Y : AlgebraicSpaces B S hS}
    (g : Y ⟶ W) (hgU : Set.range (pointsMap B S hS Y.1 g.hom) ⊆
      Set.range (pointsMap B S hS Uo.toFunctor Uo.ι)) :
    Set.range (pointsMap B S hS Y.1 g.hom) ⊆ (edsComplementPoints B S hS Uo)ᶜ :=
  fun _ hp => Set.notMem_compl_iff.mpr (hgU hp)

/-- The vanishing hypothesis of Stacks 08GG for an object supported on `|X| \ |U|`. -/
private theorem isZero_etaleModulePullback_of_range_subset_eds
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2)) :
    CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E →
      ∀ {Y : AlgebraicSpaces B S hS} (g : Y ⟶ W) (hg : IsEtale B S hS g.hom),
        Set.range (pointsMap B S hS Y.1 g.hom) ⊆
          Set.range (pointsMap B S hS Uo.toFunctor Uo.ι) →
        IsZero ((etaleModulePullback.{u, u} B S hS g hg).mapDerivedCategory.obj E) :=
  fun hE _ g hg hgU =>
    isZero_etaleModulePullback_mapDerivedCategory_of_cohomologySupportedOn B S hS _ E hE g hg
      (range_pointsMap_subset_compl_edsComplementPoints B S hS g hgU)

/-! ### Stacks 08GG, clause (1)(b) -/

/-- **Stacks 08GG, clause (1)(b).**  Let `(U ⊆ X, j : V ⟶ X)` be an elementary distinguished
square of algebraic spaces over a scheme `S` and set `T = |X| \ |U|`.  Let `E` be an object of
`D(𝒪_X)` supported on `T`.  Then the derived counit `j_!(E|_V) ⟶ E` of the adjunction
`j_! ⊣ (-)|_V` is an isomorphism.

The extension by zero is the one the library constructs, part (1) of Stacks 08GV for it is
`AlgebraicGeometry.Space.shortExact_edsShriekMayerVietoris`, and the vanishing of the
restrictions to `U` and to `P = U ×_X V` is
`AlgebraicGeometry.Space.isZero_etaleModulePullback_mapDerivedCategory_of_cohomologySupportedOn`.
The deduction itself is
`AlgebraicGeometry.Space.isIso_counit_mapDerivedCategory_of_cohomologySupportedOn`. -/
@[stacks 08GG "clause (1)(b): the derived counit j_!(E|_V) ⟶ E is an isomorphism for E \
    supported on |X| \\ |U|"]
theorem isIso_derivedCounit_etaleModuleLowerShriek_of_cohomologySupportedOn
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E) :
    IsIso ((NatTrans.mapDerivedCategory
      (edsLowerShriekAdjEtale B S hS hsq).counit).app E) :=
  isIso_counit_mapDerivedCategory_of_cohomologySupportedOn B S hS hsq
    (edsLowerShriekAdjOpen B S hS hsq) (edsLowerShriekAdjEtale B S hS hsq)
    (edsShriekOpenComparison B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
      (edsLowerShriekAdjInter B S hS hsq))
    (edsShriekEtaleComparison B S hS hsq (edsLowerShriekAdjEtale B S hS hsq)
      (edsLowerShriekAdjInter B S hS hsq))
    (zero_edsShriekMayerVietoris B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
      (edsLowerShriekAdjEtale B S hS hsq) (edsLowerShriekAdjInter B S hS hsq))
    (shortExact_edsShriekMayerVietoris B S hS hsq (edsLowerShriekAdjOpen B S hS hsq)
      (edsLowerShriekAdjEtale B S hS hsq) (edsLowerShriekAdjInter B S hS hsq))
    E hE
    (isZero_etaleModulePullback_of_range_subset_eds B S hS E)

/-! ### Stacks 08GG, clause (1)(a) -/

/-- For an elementary distinguished square `(U ⊆ X, j : V ⟶ X)` of algebraic spaces over a
scheme `S` with `T = |X| \ |U|`, and right derived functors `R_U`, `R_V`, `R_P` of the three
composites `j_{Y,*}((-)|_Y)` for which the Mayer–Vietoris sequence holds, an object `E` of
`D(𝒪_X)` supported on `T` with `R_U E` and `R_P E` zero admits an isomorphism `E ⟶ R_V E`. -/
theorem exists_isIso_derivedRestrictPushEtale_of_cohomologySupportedOn
    (RU RV RP : DerivedCategory (Modules.{u, u} B S hS W.1 W.2) ⥤
      DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (αU : (edsRestrictPushOpen B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RU)
    (αV : (edsRestrictPushEtale B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RV)
    (αP : (edsRestrictPushInter B S hS hsq).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ RP)
    (hRU : RU.IsRightDerivedFunctor αU
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRV : RV.IsRightDerivedFunctor αV
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (hRP : RP.IsRightDerivedFunctor αP
      (HomotopyCategory.quasiIso (Modules.{u, u} B S hS W.1 W.2) (ComplexShape.up ℤ)))
    (ηU : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushOpen B S hS hsq)
    (ηV : 𝟭 (Modules.{u, u} B S hS W.1 W.2) ⟶ edsRestrictPushEtale B S hS hsq)
    (dU : edsRestrictPushOpen B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (dV : edsRestrictPushEtale B S hS hsq ⟶ edsRestrictPushInter B S hS hsq)
    (hzero : ∀ M, biprod.lift (ηU.app M) (ηV.app M) ≫
      biprod.desc (dU.app M) (-(dV.app M)) = 0)
    (hMV : ∀ M, (ShortComplex.mk (biprod.lift (ηU.app M) (ηV.app M))
      (biprod.desc (dU.app M) (-(dV.app M))) (hzero M)).ShortExact)
    (E : DerivedCategory (Modules.{u, u} B S hS W.1 W.2))
    (hE : CohomologySupportedOn B S hS W.1 W.2 (edsComplementPoints B S hS Uo) E)
    (hRUzero : IsZero ((etaleModulePullback.{u, u} B S hS (edsOpenHom B S hS hsq)
        (isEtale_edsOpenHom B S hS hsq)).mapDerivedCategory.obj E) → IsZero (RU.obj E))
    (hRPzero : IsZero ((etaleModulePullback.{u, u} B S hS (edsInterHom B S hS hsq)
        (isEtale_edsInterHom B S hS hsq)).mapDerivedCategory.obj E) → IsZero (RP.obj E)) :
    ∃ f : E ⟶ RV.obj E, IsIso f :=
  exists_isIso_derivedRestrictPush_of_cohomologySupportedOn B S hS hsq RU RV RP αU αV αP
    hRU hRV hRP ηU ηV dU dV hzero hMV E hE
    (isZero_etaleModulePullback_of_range_subset_eds B S hS E)
    hRUzero hRPzero

/-! ### Stacks 08HK -/

variable {RpushD : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
    (edsEtale B S hS hsq).2) ⥤ DerivedCategory (Modules.{u, u} B S hS W.1 W.2)}
  (adjPush : edsDerivedRestrictEtale B S hS hsq ⊣ RpushD)

/-- For an elementary distinguished square `(U ⊆ X, j : V ⟶ X)` of algebraic spaces over a
scheme `S` with `T = |X| \ |U|`, a perfect object `E` of `D(𝒪_V)` supported on `j^{-1}T` whose
derived direct image restricts to zero on `U`, and for which the counit `(Rj_*E)|_V ⟶ E` is an
isomorphism, has perfect derived direct image `Rj_*E` in `D(𝒪_X)`. -/
theorem isPerfect_derivedPushforwardOfSupported
    (E : DerivedCategory (Modules.{u, u} B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2))
    (hperf : (smallEtaleRingedSite B S hS (edsEtale B S hS hsq).1
      (edsEtale B S hS hsq).2).IsPerfect E)
    (hE : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
      (edsEtalePreimageComplementPoints B S hS hsq) E)
    (h2b : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
        (edsEtalePreimageComplementPoints B S hS hsq) E →
      IsIso (adjPush.counit.app E))
    (hUzero : CohomologySupportedOn B S hS (edsEtale B S hS hsq).1 (edsEtale B S hS hsq).2
        (edsEtalePreimageComplementPoints B S hS hsq) E →
      IsZero ((edsDerivedRestrictOpen B S hS hsq).obj (RpushD.obj E))) :
    (smallEtaleRingedSite B S hS W.1 W.2).IsPerfect (RpushD.obj E) :=
  isPerfect_derivedPushforward_of_cohomologySupportedOn B S hS hsq adjPush E hperf hE h2b hUzero
    (isPerfect_of_isPerfect_edsDerivedRestrict B S hS hsq (RpushD.obj E))

end Square

end AlgebraicGeometry.Space

end
