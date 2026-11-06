module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsion.TorsionCohomologySingle
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesPushforwardCompAnyCoefficients
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ComparingBigSmall.DerivedProperDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.GeometricPointStalkCohomology
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableBaseChangeComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedBaseChangeMate
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDerivedProperBaseChange
public import StacksFrontier.RingTheory.Dualizing.DerivedHomBaseChange.Conservative

/-!
# Derived base change for squares of represented algebraic spaces

Let `T` be a big étale site of algebraic spaces over a scheme `S` and let
```
Y' --g'--> Y
|f'        |f
v          v
X' --g---> X
```
be a cartesian square of its objects. The abelian base change map
`AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleAbelianBaseChange` is the mate, across the
abelian adjunctions `(g')⁻¹ ⊣ g'_*` and `g⁻¹ ⊣ g_*`, of a comparison of the two composite direct
images of abelian sheaves, and that comparison is
`AlgebraicGeometry.Space.spacesPushforwardCompSquare_anyCoefficients` at abelian coefficients.

For a cartesian square
```
W' --n'--> W
|m'        |m
v          v
V' --n---> V
```
of the big fppf site of `S` whose right arrow has proper underlying morphism of schemes, the
derived base change map of the square of represented algebraic spaces is invertible at every
torsion abelian sheaf placed in degree zero, granted the proper base change theorem for schemes
(Stacks 095T).

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleAbelianPushforwardCompSquare`: the comparison
  `g'_* ⋙ f_* ⟶ f'_* ⋙ g_*` of abelian sheaves whose mate is the abelian base change map.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleAbelianBaseChange_eq_mateEquiv_symm`: the abelian
  base change map is that mate.
* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleAbelianPushforwardCompSquare_app_forget`: on
  underlying sheaves of sets the comparison is
  `AlgebraicGeometry.Space.spacesPushforwardCompSquare`.
* `AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleAbelianPushforwardCompSquare_eq`: it is
  `AlgebraicGeometry.Space.spacesPushforwardCompSquare_anyCoefficients` at abelian coefficients.
* `representableProperBaseChange_of_cohomologyCommutesWithBaseChange`:
  `AlgebraicGeometry.BigEtaleSpaceSite.RepresentableProperBaseChange` holds, granted
  Stacks 095T.

## References

* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
* [Stacks Project, Tag 095T](https://stacks.math.columbia.edu/tag/095T)
* [Stacks Project, Tag 0DDE](https://stacks.math.columbia.edu/tag/0DDE)
* [Stacks Project, Tag 0DG3](https://stacks.math.columbia.edu/tag/0DG3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TwoSquare

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard smallEtaleAbelianInverseImage_additive

/-! ### The abelian comparison of composite direct images -/

section Square

variable {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')

/-- **The comparison of the two composite direct images of abelian sheaves around a cartesian
square** `g'_* ⋙ f_* ⟶ f'_* ⋙ g_*` on the spaces-étale sites: the mate, across the abelian
adjunctions `(g')⁻¹ ⊣ g'_*` and `g⁻¹ ⊣ g_*`, of the abelian base change map. -/
def spacesEtaleAbelianPushforwardCompSquare (sq : IsPullback g' f' f g) :
    TwoSquare (smallEtalePushforward T g') (smallEtalePushforward T f')
      (smallEtalePushforward T f) (smallEtalePushforward T g) :=
  mateEquiv (smallEtaleAbelianAdjunction T g') (smallEtaleAbelianAdjunction T g)
    (TwoSquare.mk _ _ _ _ (spacesEtaleAbelianBaseChange T f g g' f' sq))

/-- The abelian base change map is the mate of the abelian comparison of composite direct
images. -/
theorem spacesEtaleAbelianBaseChange_eq_mateEquiv_symm (sq : IsPullback g' f' f g) :
    spacesEtaleAbelianBaseChange T f g g' f' sq =
      ((mateEquiv (smallEtaleAbelianAdjunction T g') (smallEtaleAbelianAdjunction T g)).symm
        (spacesEtaleAbelianPushforwardCompSquare T f g g' f' sq)).natTrans :=
  congrArg TwoSquare.natTrans ((mateEquiv (smallEtaleAbelianAdjunction T g')
    (smallEtaleAbelianAdjunction T g)).symm_apply_apply _).symm

/-- **On underlying sheaves of sets, the abelian comparison of composite direct images is the
comparison of composite direct images of sheaves of sets.** -/
theorem spacesEtaleAbelianPushforwardCompSquare_app_forget (sq : IsPullback g' f' f g)
    (M : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y') Ab.{u + 1}) :
    (sheafCompose _ (forget Ab.{u + 1})).map
        ((spacesEtaleAbelianPushforwardCompSquare T f g g' f' sq).natTrans.app M) =
      (TwoSquare.mk _ _ _ _ (Space.spacesPushforwardCompSquare_anyCoefficients T.fppfSite S
        T.fppf_mem g' f' f g sq.w (Type (u + 1)))).natTrans.app
          ((sheafCompose _ (forget Ab.{u + 1})).obj M) := by
  have hL : ∀ {N₁ N₂ : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) Ab.{u + 1}}
      (x : N₁ ⟶ N₂), (sheafCompose _ (forget Ab.{u + 1})).map
        ((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g)).map x) =
      (smallEtaleMorphism T g).inverseImage.map ((sheafCompose _ (forget Ab.{u + 1})).map x) :=
    fun _ => rfl
  have hR : ∀ {N₁ N₂ : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y') Ab.{u + 1}}
      (x : N₁ ⟶ N₂), (sheafCompose _ (forget Ab.{u + 1})).map ((smallEtalePushforward T f').map x) =
      ((Space.spacesBaseChange T.fppfSite S T.fppf_mem f').functor.sheafPushforwardContinuous
        (Type (u + 1)) (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')
        (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y')).map
        ((sheafCompose _ (forget Ab.{u + 1})).map x) :=
    fun _ => rfl
  have hab := congrArg (sheafCompose _ (forget Ab.{u + 1})).map
    (mateEquiv_counit (smallEtaleAbelianAdjunction T g') (smallEtaleAbelianAdjunction T g)
      (TwoSquare.mk _ _ _ _ (spacesEtaleAbelianBaseChange T f g g' f' sq)) M)
  dsimp only [TwoSquare.mk] at hab
  rw [Functor.map_comp, Functor.map_comp, hL, smallEtaleAbelianAdjunction_counit_forget, hR,
    smallEtaleAbelianAdjunction_counit_forget] at hab
  have hm : mateEquiv (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g')
      (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g)
      (Space.spacesToposBaseChangeSquare T.fppfSite S T.fppf_mem g' f' f g sq) =
      Space.spacesPushforwardCompSquare_anyCoefficients T.fppfSite S T.fppf_mem g' f' f g sq.w
        (Type (u + 1)) :=
    Equiv.apply_symm_apply _ _
  have hset := mateEquiv_counit (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g')
    (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g)
    (Space.spacesToposBaseChangeSquare T.fppfSite S T.fppf_mem g' f' f g sq)
    ((sheafCompose _ (forget Ab.{u + 1})).obj M)
  rw [hm] at hset
  have hθ : (sheafCompose _ (forget Ab.{u + 1})).map
      ((spacesEtaleAbelianBaseChange T f g g' f' sq).app ((smallEtalePushforward T g').obj M)) =
      (Space.spacesToposBaseChangeSquare T.fppfSite S T.fppf_mem g' f' f g sq).app
        ((sheafCompose _ (forget Ab.{u + 1})).obj ((smallEtalePushforward T g').obj M)) := rfl
  rw [hθ] at hab
  have key : ∀ {A₀ : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) (Type (u + 1))}
      {B₀ : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X') (Type (u + 1))}
      {a b : A₀ ⟶ ((Space.spacesBaseChange T.fppfSite S T.fppf_mem
        g).functor.sheafPushforwardContinuous (Type (u + 1))
          (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X)
          (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X')).obj B₀},
      (smallEtaleMorphism T g).inverseImage.map a ≫
          (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g).counit.app B₀ =
        (smallEtaleMorphism T g).inverseImage.map b ≫
          (Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g).counit.app B₀ → a = b :=
    fun h ↦ ((Space.spacesToposAdjunction T.fppfSite S T.fppf_mem g).homEquiv _ _).symm.injective
      (by rwa [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit])
  exact key (hab.trans hset.symm)

/-- **On underlying sheaves of sets, the comparison of composite direct images of abelian sheaves
is the one of sheaves of sets.** -/
theorem sheafCompose_forget_map_spacesPushforwardCompSquare_app (w : g' ≫ f = f' ≫ g)
    (M : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y') Ab.{u + 1}) :
    (sheafCompose _ (forget Ab.{u + 1})).map
        ((Space.spacesPushforwardCompSquare_anyCoefficients T.fppfSite S T.fppf_mem g' f' f g w
          Ab.{u + 1}).app M) =
      (Space.spacesPushforwardCompSquare_anyCoefficients T.fppfSite S T.fppf_mem g' f' f g w
        (Type (u + 1))).app ((sheafCompose _ (forget Ab.{u + 1})).obj M) := by
  rw [Space.spacesPushforwardCompSquare_anyCoefficients_eq T.fppfSite S T.fppf_mem g' f' f g w
      Ab.{u + 1},
    Space.spacesPushforwardCompSquare_anyCoefficients_eq T.fppfSite S T.fppf_mem g' f' f g w
      (Type (u + 1))]
  rfl

/-- **The abelian comparison of composite direct images is the comparison of composite direct
images of abelian sheaves**, `AlgebraicGeometry.Space.spacesPushforwardCompSquare_anyCoefficients`
at abelian coefficients. -/
theorem spacesEtaleAbelianPushforwardCompSquare_eq (sq : IsPullback g' f' f g) :
    spacesEtaleAbelianPushforwardCompSquare T f g g' f' sq =
      TwoSquare.mk _ _ _ _
        (Space.spacesPushforwardCompSquare_anyCoefficients T.fppfSite S T.fppf_mem g' f' f g sq.w
          Ab.{u + 1}) := by
  refine TwoSquare.ext _ _ fun M => (sheafCompose _ (forget Ab.{u + 1})).map_injective ?_
  rewrite [spacesEtaleAbelianPushforwardCompSquare_app_forget, TwoSquare.mk_natTrans_app,
    TwoSquare.mk_natTrans_app, sheafCompose_forget_map_spacesPushforwardCompSquare_app]
  rfl

end Square

/-! ### Squares of represented algebraic spaces -/

section Represented

open Space Stacks.Homology.DerivedSquare

variable {V W V' W' : BigFppfOver T.fppfSite S T.fppf_mem} (m : W ⟶ V) (n : V' ⟶ V)
  (n' : W' ⟶ W) (m' : W' ⟶ V')

/- Lean v4.35.0: instance search for these limits on presheaves of the big fppf site and on the
Kan extensions along the comparison functors times out; supply them directly. -/
set_option synthInstance.maxHeartbeats 400000 in
local instance hasLimitsOfSize_presheaf_RepresentableDerivedBaseChange :
    HasLimitsOfSize.{0, 0} ((BigFppfOver T.fppfSite S T.fppf_mem)ᵒᵖ ⥤ Type u) := inferInstance

local instance hasLimitsOfShape_presheaf_RepresentableDerivedBaseChange (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver T.fppfSite S T.fppf_mem)ᵒᵖ ⥤ Type u) :=
  HasLimitsOfSize.has_limits_of_shape _

set_option synthInstance.maxHeartbeats 400000 in
local instance hasLimitsOfShape_structuredArrow_RepresentableDerivedBaseChange
    (V₀ : BigFppfOver T.fppfSite S T.fppf_mem)
    (Y : (SpacesEtale T.fppfSite S T.fppf_mem (yonedaSpace T.fppfSite S T.fppf_mem V₀))ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow Y (comparisonFunctor T.fppfSite S T.fppf_mem
      (yonedaSpace T.fppfSite S T.fppf_mem V₀)).op) Ab.{u + 1} := inferInstance

/-- **The cube identity at abelian coefficients.** The comparison of the two composite direct
images of abelian sheaves around the square of represented algebraic spaces corresponds, under the
chart restrictions, to the bounded comparison through a diagonal `Q` of the square. -/
theorem representedPushforwardCube_abelian (Q : W' ⟶ V) (e₁ : n' ≫ m = Q) (e₂ : m' ≫ n = Q)
    (hQ₁ : n'.left ≫ m.left = Q.left) (hQ₂ : m'.left ≫ n.left = Q.left)
    (sq : IsPullback (yonedaSpaceHom n') (yonedaSpaceHom m') (yonedaSpaceHom m)
      (yonedaSpaceHom n)) :
    ((TwoSquare.mk _ _ _ _ (representedPushforwardIso n' Ab.{u + 1}).hom ≫ᵥ
        SmallEtale.boundedBaseChangeMate (associatedBigEtaleSite T.fppfSite) Ab.{u + 1} m.left
          n.left n'.left m'.left Q.left hQ₁ hQ₂).whiskerRight
        (representedPushforwardIso m Ab.{u + 1}).hom).whiskerLeft
        (representedPushforwardIso m' Ab.{u + 1}).inv =
      spacesEtaleAbelianPushforwardCompSquare T (yonedaSpaceHom m) (yonedaSpaceHom n)
          (yonedaSpaceHom n') (yonedaSpaceHom m') sq ≫ᵥ
        TwoSquare.mk _ _ _ _ (representedPushforwardIso n Ab.{u + 1}).hom := by
  rewrite [spacesEtaleAbelianPushforwardCompSquare_eq]
  exact representedPushforwardCube Ab.{u + 1} m n n' m' Q e₁ e₂ hQ₁ hQ₂ sq.w

/-- **Restriction along the chart functor carries torsion sheaves to torsion sheaves.** -/
theorem torsionSheafProperty_representedRestriction (V₀ : BigFppfOver T.fppfSite S T.fppf_mem)
    (F : Sheaf (SpacesEtale.topology T.fppfSite S T.fppf_mem
      (yonedaSpace T.fppfSite S T.fppf_mem V₀)) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) :
    Stacks.Torsion.torsionSheafProperty (representedSchemeTopology T.fppfSite S T.fppf_mem V₀)
      ((representedRestriction V₀ Ab.{u + 1}).obj F) := by
  have : (comparisonFunctor T.fppfSite S T.fppf_mem
      (yonedaSpace T.fppfSite S T.fppf_mem V₀)).IsCocontinuous
      (Space.SmallEtale.topology T.fppfSite S T.fppf_mem (yoneda.obj V₀))
      (SpacesEtale.topology T.fppfSite S T.fppf_mem (yonedaSpace T.fppfSite S T.fppf_mem V₀)) :=
    @Functor.IsDenseSubsite.instIsCocontinuous _ _ _ _ _ _ _
      (comparisonFunctor_isDenseSubsite T.fppfSite S T.fppf_mem
        (yonedaSpace T.fppfSite S T.fppf_mem V₀))
  have : (representedChartFunctor T.fppfSite S T.fppf_mem V₀).IsCocontinuous
      (representedSchemeTopology T.fppfSite S T.fppf_mem V₀)
      (SpacesEtale.topology T.fppfSite S T.fppf_mem (yonedaSpace T.fppfSite S T.fppf_mem V₀)) :=
    isCocontinuous_comp _ _ _ (Space.SmallEtale.topology T.fppfSite S T.fppf_mem (yoneda.obj V₀))
  have : (representedSchemeChartFunctor V₀).IsCocontinuous
      (representedSchemeTopology T.fppfSite S T.fppf_mem V₀)
      (SpacesEtale.topology T.fppfSite S T.fppf_mem (yonedaSpace T.fppfSite S T.fppf_mem V₀)) :=
    Functor.IsCocontinuous.of_iso (representedSchemeChartFunctorIso V₀).symm
  exact Stacks.Torsion.isLocallyTorsion_comp_op _ _ (representedSchemeChartFunctor V₀) F.obj hF

/-- Restriction of abelian sheaves along the chart functor is additive. -/
instance representedRestriction_additive (V₀ : BigFppfOver T.fppfSite S T.fppf_mem) :
    (representedRestriction V₀ Ab.{u + 1}).Additive :=
  ⟨rfl⟩

/-- **The cube identity at abelian coefficients, objectwise**: the front base change mate of the
square of represented algebraic spaces and the back base change mate of the square of schemes
agree at every abelian sheaf, up to the chart comparisons. -/
theorem representedPushforwardCube_abelian_app (hQ₁ : n'.left ≫ m.left = (n' ≫ m).left)
    (hQ₂ : m'.left ≫ n.left = (n' ≫ m).left) (hw : n' ≫ m = m' ≫ n)
    (sq : IsPullback (yonedaSpaceHom n') (yonedaSpaceHom m') (yonedaSpaceHom m)
      (yonedaSpaceHom n))
    (c : Sheaf (SpacesEtale.topology T.fppfSite S T.fppf_mem
      (yonedaSpace T.fppfSite S T.fppf_mem W)) Ab.{u + 1}) :
    ((mateEquiv (smallEtaleAbelianAdjunction T (yonedaSpaceHom n))
        ((associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction n.left Ab.{u + 1})).symm
        (TwoSquare.mk _ _ _ _ (representedPushforwardIso n Ab.{u + 1}).hom)).natTrans.app
        ((smallEtalePushforward T (yonedaSpaceHom m)).obj c) ≫
      (representedRestriction V' Ab.{u + 1}).map
        (((mateEquiv (smallEtaleAbelianAdjunction T (yonedaSpaceHom n'))
          (smallEtaleAbelianAdjunction T (yonedaSpaceHom n))).symm
          (spacesEtaleAbelianPushforwardCompSquare T (yonedaSpaceHom m) (yonedaSpaceHom n)
            (yonedaSpaceHom n') (yonedaSpaceHom m') sq)).natTrans.app c) =
    ((associatedBigEtaleSite T.fppfSite).smallInverseImage n.left Ab.{u + 1}).map
        ((representedPushforwardIso m Ab.{u + 1}).hom.app c) ≫
      ((mateEquiv ((associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction n'.left Ab.{u + 1})
        ((associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction n.left Ab.{u + 1})).symm
        (SmallEtale.boundedBaseChangeMate (associatedBigEtaleSite T.fppfSite) Ab.{u + 1} m.left
          n.left n'.left m'.left (n' ≫ m).left hQ₁ hQ₂)).natTrans.app
          ((representedRestriction W Ab.{u + 1}).obj c) ≫
      ((associatedBigEtaleSite T.fppfSite).smallPushforward m'.left Ab.{u + 1}).map
        (((mateEquiv (smallEtaleAbelianAdjunction T (yonedaSpaceHom n'))
          ((associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction n'.left Ab.{u + 1})).symm
          (TwoSquare.mk _ _ _ _ (representedPushforwardIso n' Ab.{u + 1}).hom)).natTrans.app c) ≫
      (representedPushforwardIso m' Ab.{u + 1}).inv.app
        ((CategoryTheory.Sites.abelianInverseImage
          (smallEtaleMorphism T (yonedaSpaceHom n'))).obj c) := by
  let adj₁ := smallEtaleAbelianAdjunction T (yonedaSpaceHom n')
  let adj₂ := smallEtaleAbelianAdjunction T (yonedaSpaceHom n)
  let adj₁' := (associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction n'.left Ab.{u + 1}
  let adj₂' := (associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction n.left Ab.{u + 1}
  exact Stacks.CategoryTheory.mateEquiv_symm_hComp_eq_app adj₁ adj₂ adj₁' adj₂'
    ((mateEquiv adj₁ adj₁').symm
      (TwoSquare.mk _ _ _ _ (representedPushforwardIso n' Ab.{u + 1}).hom))
    ((mateEquiv adj₂ adj₂').symm
      (TwoSquare.mk _ _ _ _ (representedPushforwardIso n Ab.{u + 1}).hom))
    (representedPushforwardIso m Ab.{u + 1}).hom (representedPushforwardIso m' Ab.{u + 1}).inv
    (spacesEtaleAbelianPushforwardCompSquare T (yonedaSpaceHom m) (yonedaSpaceHom n)
      (yonedaSpaceHom n') (yonedaSpaceHom m') sq)
    (SmallEtale.boundedBaseChangeMate (associatedBigEtaleSite T.fppfSite) Ab.{u + 1} m.left
      n.left n'.left m'.left (n' ≫ m).left hQ₁ hQ₂)
    (by
      rewrite [Equiv.apply_symm_apply, Equiv.apply_symm_apply]
      exact representedPushforwardCube_abelian T m n n' m' (n' ≫ m) rfl hw.symm hQ₁ hQ₂ sq) c

/-- **The derived base change maps of a square of represented algebraic spaces and of its
square of schemes are invertible together**: at a K-injective complex `I`, the derived base
change map of the schemes is invertible at the restriction of `I` to the chart exactly when the
restriction of the derived base change map of the represented algebraic spaces at `I` is. -/
theorem isIso_derivedBaseChangeMap_representedRestriction_iff
    (hQ₁ : n'.left ≫ m.left = (n' ≫ m).left) (hQ₂ : m'.left ≫ n.left = (n' ≫ m).left)
    (hw : n' ≫ m = m' ≫ n)
    (sq : IsPullback (yonedaSpaceHom n') (yonedaSpaceHom m') (yonedaSpaceHom m)
      (yonedaSpaceHom n))
    (I : CochainComplex (Sheaf (SpacesEtale.topology T.fppfSite S T.fppf_mem
      (yonedaSpace T.fppfSite S T.fppf_mem W)) Ab.{u + 1}) ℤ) (hI : I.IsKInjective) :
    IsIso ((Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap
        ((associatedBigEtaleSite T.fppfSite).smallInverseImage n'.left Ab.{u + 1})
        ((associatedBigEtaleSite T.fppfSite).smallInverseImage n.left Ab.{u + 1})
        ((associatedBigEtaleSite T.fppfSite).smallPushforward m.left Ab.{u + 1})
        ((associatedBigEtaleSite T.fppfSite).smallPushforward m'.left Ab.{u + 1})
        (totalRightDerived ((associatedBigEtaleSite T.fppfSite).smallPushforward m.left Ab.{u + 1}))
        (totalRightDerived
          ((associatedBigEtaleSite T.fppfSite).smallPushforward m'.left Ab.{u + 1}))
        (totalRightDerivedUnit
          ((associatedBigEtaleSite T.fppfSite).smallPushforward m.left Ab.{u + 1}))
        (totalRightDerivedUnit
          ((associatedBigEtaleSite T.fppfSite).smallPushforward m'.left Ab.{u + 1}))
        ((mateEquiv
          ((associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction n'.left Ab.{u + 1})
          ((associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction n.left Ab.{u + 1})).symm
          (SmallEtale.boundedBaseChangeMate (associatedBigEtaleSite T.fppfSite) Ab.{u + 1} m.left
            n.left n'.left m'.left (n' ≫ m).left hQ₁ hQ₂)).natTrans).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((representedRestriction W Ab.{u + 1}).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)))) ↔
      IsIso ((representedRestriction V' Ab.{u + 1}).mapDerivedCategory.map
        ((Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap
          (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T (yonedaSpaceHom n')))
          (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T (yonedaSpaceHom n)))
          (smallEtalePushforward T (yonedaSpaceHom m))
          (smallEtalePushforward T (yonedaSpaceHom m'))
          (totalRightDerived (smallEtalePushforward T (yonedaSpaceHom m)))
          (totalRightDerived (smallEtalePushforward T (yonedaSpaceHom m')))
          (totalRightDerivedUnit (smallEtalePushforward T (yonedaSpaceHom m)))
          (totalRightDerivedUnit (smallEtalePushforward T (yonedaSpaceHom m')))
          ((mateEquiv (smallEtaleAbelianAdjunction T (yonedaSpaceHom n'))
            (smallEtaleAbelianAdjunction T (yonedaSpaceHom n))).symm
            (spacesEtaleAbelianPushforwardCompSquare T (yonedaSpaceHom m) (yonedaSpaceHom n)
              (yonedaSpaceHom n') (yonedaSpaceHom m') sq)).natTrans).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))) := by
  have := smallEtaleSheaf_isGrothendieckAbelian (associatedBigEtaleSite T.fppfSite) W.left
  have := smallEtaleSheaf_isGrothendieckAbelian (associatedBigEtaleSite T.fppfSite) W'.left
  have := representedRestriction_isEquivalence W Ab.{u + 1}
  have := representedRestriction_isEquivalence W' Ab.{u + 1}
  have := representedRestriction_isEquivalence V' Ab.{u + 1}
  have hmate : ∀ {A B : BigFppfOver T.fppfSite S T.fppf_mem} (k : A ⟶ B),
      IsIso ((mateEquiv (smallEtaleAbelianAdjunction T (yonedaSpaceHom k))
        ((associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction k.left Ab.{u + 1})).symm
          (TwoSquare.mk _ _ _ _ (representedPushforwardIso k Ab.{u + 1}).hom)).natTrans :=
    fun k => @CategoryTheory.isIso_mateEquiv_symm_of_isEquivalence _ _ _ _ _ _ _ _ _ _ _ _ _ _
      (smallEtaleAbelianAdjunction T (yonedaSpaceHom k))
      ((associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction k.left Ab.{u + 1})
      (representedRestriction_isEquivalence _ Ab.{u + 1})
      (representedRestriction_isEquivalence _ Ab.{u + 1}) _
      (representedPushforwardIso k Ab.{u + 1}).isIso_hom
  have := hmate n'
  have := hmate n
  have hKinj' : ∀ (V₀ : BigFppfOver T.fppfSite S T.fppf_mem)
      [(representedRestriction V₀ Ab.{u + 1}).IsEquivalence]
      (J : CochainComplex (Sheaf (SpacesEtale.topology T.fppfSite S T.fppf_mem
        (yonedaSpace T.fppfSite S T.fppf_mem V₀)) Ab.{u + 1}) ℤ), J.IsKInjective →
      CochainComplex.IsKInjective (((representedRestriction V₀ Ab.{u + 1}).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj J) := fun V₀ _ J _ => by
    have : (representedRestriction V₀ Ab.{u + 1}).asEquivalence.functor.Additive :=
      inferInstanceAs (representedRestriction V₀ Ab.{u + 1}).Additive
    have := (representedRestriction V₀ Ab.{u + 1}).asEquivalence.isEquivalence_inverse
    exact CochainComplex.isKInjective_mapHomologicalComplex_of_exact
      (representedRestriction V₀ Ab.{u + 1})
      (representedRestriction V₀ Ab.{u + 1}).asEquivalence.inverse
      (representedRestriction V₀ Ab.{u + 1}).asEquivalence.symm.toAdjunction J
  exact Stacks.Cohomology.UnboundedComplexes.isIso_derivedBaseChangeMap_app_iff_of_cube
    (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T (yonedaSpaceHom n')))
    (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T (yonedaSpaceHom n)))
    (smallEtalePushforward T (yonedaSpaceHom m)) (smallEtalePushforward T (yonedaSpaceHom m'))
    (totalRightDerived (smallEtalePushforward T (yonedaSpaceHom m)))
    (totalRightDerived (smallEtalePushforward T (yonedaSpaceHom m')))
    (totalRightDerivedUnit (smallEtalePushforward T (yonedaSpaceHom m)))
    (totalRightDerivedUnit (smallEtalePushforward T (yonedaSpaceHom m')))
    ((mateEquiv (smallEtaleAbelianAdjunction T (yonedaSpaceHom n'))
      (smallEtaleAbelianAdjunction T (yonedaSpaceHom n))).symm
      (spacesEtaleAbelianPushforwardCompSquare T (yonedaSpaceHom m) (yonedaSpaceHom n)
        (yonedaSpaceHom n') (yonedaSpaceHom m') sq)).natTrans
    ((associatedBigEtaleSite T.fppfSite).smallInverseImage n'.left Ab.{u + 1})
    ((associatedBigEtaleSite T.fppfSite).smallInverseImage n.left Ab.{u + 1})
    ((associatedBigEtaleSite T.fppfSite).smallPushforward m.left Ab.{u + 1})
    ((associatedBigEtaleSite T.fppfSite).smallPushforward m'.left Ab.{u + 1})
    (totalRightDerived ((associatedBigEtaleSite T.fppfSite).smallPushforward m.left Ab.{u + 1}))
    (totalRightDerived ((associatedBigEtaleSite T.fppfSite).smallPushforward m'.left Ab.{u + 1}))
    (totalRightDerivedUnit
      ((associatedBigEtaleSite T.fppfSite).smallPushforward m.left Ab.{u + 1}))
    (totalRightDerivedUnit
      ((associatedBigEtaleSite T.fppfSite).smallPushforward m'.left Ab.{u + 1}))
    ((mateEquiv ((associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction n'.left Ab.{u + 1})
      ((associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction n.left Ab.{u + 1})).symm
      (SmallEtale.boundedBaseChangeMate (associatedBigEtaleSite T.fppfSite) Ab.{u + 1} m.left
        n.left n'.left m'.left (n' ≫ m).left hQ₁ hQ₂)).natTrans
    _ _ _ _ _ _ _ _ (representedPushforwardCube_abelian_app T m n n' m' hQ₁ hQ₂ hw sq)
    (hKinj' W') I hI (hKinj' W I hI)

/-- **Proper base change on the chart of a represented square**, granted that cohomology commutes
with base change for `m`: the derived base change map of the square of schemes is invertible at
the restriction to the chart of a K-injective model `I` of a torsion abelian sheaf. -/
theorem isIso_derivedBaseChangeMap_representedRestriction_app
    (hQ₁ : n'.left ≫ m.left = (n' ≫ m).left) (hQ₂ : m'.left ≫ n.left = (n' ≫ m).left)
    (hsite : IsPullback n' m' m n)
    (h095T : Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0}
      ((associatedBigEtaleSite T.fppfSite).inclusion.map m.left))
    (F : Sheaf (SpacesEtale.topology T.fppfSite S T.fppf_mem
      (yonedaSpace T.fppfSite S T.fppf_mem W)) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F)
    (I : CochainComplex (Sheaf (SpacesEtale.topology T.fppfSite S T.fppf_mem
      (yonedaSpace T.fppfSite S T.fppf_mem W)) Ab.{u + 1}) ℤ)
    (e : DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) ≅
      (DerivedCategory.singleFunctor _ 0).obj F) :
    IsIso ((Stacks.Cohomology.UnboundedComplexes.derivedBaseChangeMap
        ((associatedBigEtaleSite T.fppfSite).smallInverseImage n'.left Ab.{u + 1})
        ((associatedBigEtaleSite T.fppfSite).smallInverseImage n.left Ab.{u + 1})
        ((associatedBigEtaleSite T.fppfSite).smallPushforward m.left Ab.{u + 1})
        ((associatedBigEtaleSite T.fppfSite).smallPushforward m'.left Ab.{u + 1})
        (totalRightDerived ((associatedBigEtaleSite T.fppfSite).smallPushforward m.left Ab.{u + 1}))
        (totalRightDerived
          ((associatedBigEtaleSite T.fppfSite).smallPushforward m'.left Ab.{u + 1}))
        (totalRightDerivedUnit
          ((associatedBigEtaleSite T.fppfSite).smallPushforward m.left Ab.{u + 1}))
        (totalRightDerivedUnit
          ((associatedBigEtaleSite T.fppfSite).smallPushforward m'.left Ab.{u + 1}))
        ((mateEquiv
          ((associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction n'.left Ab.{u + 1})
          ((associatedBigEtaleSite T.fppfSite).smallPullbackAdjunction n.left Ab.{u + 1})).symm
          (SmallEtale.boundedBaseChangeMate (associatedBigEtaleSite T.fppfSite) Ab.{u + 1} m.left
            n.left n'.left m'.left (n' ≫ m).left hQ₁ hQ₂)).natTrans).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
          (((representedRestriction W Ab.{u + 1}).mapHomologicalComplex
            (ComplexShape.up ℤ)).obj I)))) := by
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme T.fppfSite S T.fppf_mem) :=
    comp_preservesLimitsOfShape _ _
  let ΦW := representedRestriction W Ab.{u + 1}
  let eK : ΦW.mapDerivedCategory.obj ((DerivedCategory.singleFunctor _ 0).obj F) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((ΦW.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    ΦW.mapDerivedCategory.mapIso e.symm ≪≫ ΦW.mapDerivedCategoryFactorsh.app _
  have hK : (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
      ((ΦW.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))).IsGE 0 := by
    have := Functor.isGE_obj_mapDerivedCategory ΦW ((DerivedCategory.singleFunctor _ 0).obj F) 0
      inferInstance
    exact DerivedCategory.TStructure.t.isGE_of_iso eK 0
  have hT : Stacks.Torsion.torsionCohomologyProperty.{u + 1}
      (representedSchemeTopology T.fppfSite S T.fppf_mem W)
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((ΦW.mapHomologicalComplex (ComplexShape.up ℤ)).obj I))) := fun i =>
    (Stacks.Torsion.torsionSheafProperty _).prop_of_iso
      (((ΦW.mapDerivedCategoryHomologyIso i).app _).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso eK)
      (torsionSheafProperty_representedRestriction T W _
        (Stacks.Torsion.torsionCohomologyProperty_singleFunctor _ F hF i))
  exact isIso_derivedBaseChangeMap_bounded_app_of_cohomologyCommutesWithBaseChange
    (associatedBigEtaleSite T.fppfSite) m.left n.left n'.left m'.left (hQ₁.trans hQ₂.symm)
    (hsite.map (BigFppfOver.toScheme T.fppfSite S T.fppf_mem))
    (totalRightDerived ((associatedBigEtaleSite T.fppfSite).smallPushforward m.left Ab.{u + 1}))
    (totalRightDerived ((associatedBigEtaleSite T.fppfSite).smallPushforward m'.left Ab.{u + 1}))
    (totalRightDerivedUnit
      ((associatedBigEtaleSite T.fppfSite).smallPushforward m.left Ab.{u + 1}))
    (totalRightDerivedUnit
      ((associatedBigEtaleSite T.fppfSite).smallPushforward m'.left Ab.{u + 1}))
    h095T _ 0 hK hT

/-- **Proper base change for squares of schemes, read on the spaces-étale sites**, granted the
proper base change theorem for schemes in the form of Stacks 095T: cohomology commutes with base
change for every proper morphism of schemes (`h095T`). -/
theorem representableProperBaseChange_of_cohomologyCommutesWithBaseChange
    (h095T : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y) [_root_.AlgebraicGeometry.IsProper f],
      Stacks.EtaleCohomology.CohomologyCommutesWithBaseChange.{u, 0} f) :
    RepresentableProperBaseChange T := by
  intro V W V' W' m n n' m' hsite hm sq F hF
  have hQ₁ : n'.left ≫ m.left = (n' ≫ m).left := (Over.comp_left _ _ _ n' m).symm
  have hQ₂ : m'.left ≫ n.left = (n' ≫ m).left :=
    (Over.comp_left _ _ _ m' n).symm.trans (congrArg (fun k : W' ⟶ V => k.left) hsite.w.symm)
  have : _root_.AlgebraicGeometry.IsProper
      ((associatedBigEtaleSite T.fppfSite).inclusion.map m.left) := hm
  obtain ⟨I, hI, ⟨e⟩⟩ := Stacks.Cohomology.UnboundedComplexes.exists_isKInjective_iso
    DerivedCategory.Qh ((DerivedCategory.singleFunctor _ 0).obj F)
  rw [← NatTrans.isIso_app_iff_of_iso _ e]
  rewrite [spacesEtaleDerivedBaseChange, derivedSquare_eq_derivedBaseChangeMap,
    spacesEtaleAbelianBaseChange_eq_mateEquiv_symm]
  have hfront := (isIso_derivedBaseChangeMap_representedRestriction_iff T m n n' m' hQ₁ hQ₂
    hsite.w sq I hI).1 (isIso_derivedBaseChangeMap_representedRestriction_app T m n n' m' hQ₁ hQ₂
      hsite (h095T _) F hF I e)
  have := representedRestriction_isEquivalence V' Ab.{u + 1}
  exact (isIso_iff_of_reflects_iso _ (representedRestriction V' Ab.{u + 1}).mapDerivedCategory).1
    hfront

end Represented

end AlgebraicGeometry.BigEtaleSpaceSite

end
