module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigSmallEtaleDerivedProperPushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.ProperBaseChangeRepresentable
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedSquareCommShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowCoreflection
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowNaturalTransformations
public import StacksFrontier.CategoryTheory.Sites.Cohomology.UnboundedDerivedFunctor.LeftTExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.RepresentableBridgeBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleAffineChartDensity
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleInverseImageKInjective
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedUnitComposition
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRestriction
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.BaseChangeZariskiLocality

/-!
# Derived proper base change for algebraic spaces

Let `S` be a scheme and
```
Y' --g'--> Y
|f'        |f
v          v
X' --g---> X
```
a cartesian square of algebraic spaces over `S` with `f` proper. The base change map
`g⁻¹ R f_* E ⟶ R f'_* (g')⁻¹ E`
(`AlgebraicGeometry.BigEtaleSpaceSite.spacesEtaleDerivedBaseChange`) is an isomorphism for every
`E ∈ D⁺(Y_étale)` with torsion cohomology sheaves, provided proper base change holds for étale
sheaves of sets along proper morphisms of schemes and the derived base change map is invertible
over an affine base along an affine base change.

## Main definitions

* `AlgebraicGeometry.BigEtaleSpaceSite.AffineBaseProperBaseChange`: derived proper base change
  over an affine base, along an affine base change.
* `AlgebraicGeometry.BigEtaleSpaceSite.RepresentableProperBaseChange`: proper base change for
  squares of schemes, on torsion sheaves, read on the spaces-étale sites.

## Main results

* `AlgebraicGeometry.BigEtaleSpaceSite.natTransCommShift_spacesEtaleDerivedBaseChange`: the base
  change map commutes with the shift.
* `AlgebraicGeometry.BigEtaleSpaceSite.isIso_spacesEtaleDerivedBaseChange_app_of_isGE`:
  invertibility at torsion sheaves implies invertibility at bounded below objects with torsion
  cohomology sheaves.
* `isIso_spacesEtaleDerivedBaseChange_app_of_affineThroughEtaleChart`: the base change map is
  local on the base change.
* `isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_affineBase`: the base change map of a
  cartesian square with `f` proper is invertible at bounded below objects with torsion cohomology
  sheaves, under the two hypotheses above.

## References

* [Stacks Project, Tag 0DG3](https://stacks.math.columbia.edu/tag/0DG3)
* [Stacks Project, Tag 0DG2](https://stacks.math.columbia.edu/tag/0DG2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Homology.DerivedSquare (derivedSquare totalRightDerived totalRightDerivedUnit)

universe u

namespace AlgebraicGeometry.BigEtaleSpaceSite

variable {S : Scheme.{u}} (T : BigEtaleSpaceSite S)

attribute [local instance] HasDerivedCategory.standard smallEtaleAbelianInverseImage_additive
  bigToSmallAbelianInverseImage_additive

/- Lean v4.35.0: instance search for these limits on presheaves of the big fppf site and on the
Kan extensions defining the big direct image times out; supply them directly. -/
set_option synthInstance.maxHeartbeats 400000 in
local instance hasLimitsOfSize_presheaf_SpacesEtaleDerivedProperBaseChange :
    HasLimitsOfSize.{0, 0} ((BigFppfOver T.fppfSite S T.fppf_mem)ᵒᵖ ⥤ Type u) := inferInstance

local instance hasLimitsOfShape_presheaf_SpacesEtaleDerivedProperBaseChange (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver T.fppfSite S T.fppf_mem)ᵒᵖ ⥤ Type u) :=
  HasLimitsOfSize.has_limits_of_shape _

set_option synthInstance.maxHeartbeats 400000 in
local instance hasLimitsOfShape_structuredArrow_SpacesEtaleDerivedProperBaseChange
    {X Y : T.Spaces} (f : Y ⟶ X) (V : (Over X)ᵒᵖ) :
    HasLimitsOfShape (StructuredArrow V (Over.map f).op) Ab.{u + 1} := inferInstance

/-- The base change map of a square of algebraic spaces commutes with the shift. -/
instance natTransCommShift_spacesEtaleDerivedBaseChange {X Y X' Y' : T.Spaces} (f : Y ⟶ X)
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g) :
    NatTrans.CommShift (spacesEtaleDerivedBaseChange T f g g' f' sq) ℤ := by
  unfold spacesEtaleDerivedBaseChange
  infer_instance

/-- **From torsion sheaves to bounded below complexes.** If the base change map of a square of
algebraic spaces is invertible at every torsion abelian sheaf placed in degree zero, it is
invertible at every bounded below object with torsion cohomology sheaves. -/
theorem isIso_spacesEtaleDerivedBaseChange_app_of_isGE {X Y X' Y' : T.Spaces} (f : Y ⟶ X)
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    (h : ∀ F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y) Ab.{u + 1},
      Stacks.Torsion.torsionSheafProperty (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
        F →
      IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app
        ((DerivedCategory.singleFunctor _ 0).obj F)))
    (E : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})) (n : ℤ) (hE : E.IsGE n) (hT : HasTorsionCohomology T E) :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app E) :=
  NatTrans.isIso_app_of_isGE (spacesEtaleDerivedBaseChange T f g g' f' sq)
    (fun L m hL ↦ by
      have := hL
      exact Functor.isGE_obj_mapDerivedCategory _ _ m
        (Stacks.DerivedFunctor.isGE_totalRightDerived_obj _ L m))
    (fun L m hL ↦ by
      have := Functor.isGE_obj_mapDerivedCategory
        (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T g')) L m hL
      exact Stacks.DerivedFunctor.isGE_totalRightDerived_obj _ _ m)
    E n hE (fun q ↦ h _ (hT q))

/-! ### Localization of the base change map -/

/-- The inverse image of abelian sheaves along a composite of morphisms of algebraic spaces is the
composite of the inverse images. -/
def smallEtaleAbelianInverseImageCompIso {X Y Z : T.Spaces} (a : X ⟶ Y) (b : Y ⟶ Z) :
    CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T (a ≫ b)) ≅
      CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T b) ⋙
        CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T a) :=
  haveI : HasBinaryBiproducts
      (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z) Ab.{u + 1}) :=
    HasBinaryBiproducts.of_hasBinaryProducts
  ProEtale.liftSheafNatIso (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem X) _ _
    (Functor.isoWhiskerLeft
      (sheafCompose (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Z) (forget Ab.{u + 1}))
      (Space.spacesEtaleInverseImage_comp T.fppfSite S T.fppf_mem a b))

/-- **The base change map at a K-injective complex, read on the big étale site.** If the abelian
base-change map is invertible, the derived base change map `g⁻¹ R f_* ⟶ R f'_* (g')⁻¹` is
invertible at a K-injective complex `I` exactly when the restriction to the spaces-étale site of
`X'` of the unit of `R f_{big,*}` at `π_Y⁻¹ I` is invertible. -/
theorem isIso_spacesEtaleDerivedBaseChange_app_iff_restriction {X Y X' Y' : T.Spaces}
    (f : Y ⟶ X) (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    [IsIso (spacesEtaleAbelianBaseChange T f g g' f' sq)]
    (I : CochainComplex (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1}) ℤ) [I.IsKInjective] :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) ↔
      IsIso ((smallEtaleRestriction T g).mapDerivedCategory.map
        ((totalRightDerivedUnit (bigEtalePushforward T f)).app
          (((CategoryTheory.Sites.abelianInverseImage
            (bigToSmallEtaleMorphism T Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
              ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)))) :=
  (isIso_spacesEtaleDerivedBaseChange_app_iff T f g g' f' sq I).trans
    ((NatTrans.isIso_app_iff_of_iso _
      (pulledAbelianInverseImageHomotopyIso T g' _)).symm.trans
      (isIso_map_totalRightDerivedUnit_bigEtalePushforward_iff T f g g' f' sq _).symm)

/-- **The base change map is local on the base change.** Let `f : Y ⟶ X` be a morphism of
algebraic spaces whose abelian base-change maps are all invertible. If the derived base change map
along some cartesian square over every affine chart through an étale chart `w : W ⟶ X` is
invertible at a K-injective complex `I`, then so is the derived base change map along every
`g : X' ⟶ X`. -/
theorem isIso_spacesEtaleDerivedBaseChange_app_of_affineThroughEtaleChart {X Y : T.Spaces}
    (f : Y ⟶ X)
    (hc : ∀ ⦃X' Y' : T.Spaces⦄ (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
      (sq : IsPullback g' f' f g), IsIso (spacesEtaleAbelianBaseChange T f g g' f' sq))
    (I : CochainComplex (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1}) ℤ) [I.IsKInjective]
    (h : ∀ V : Over X, IsAffineThroughEtaleChart T X V →
      ∃ (Y' : T.Spaces) (g' : Y' ⟶ Y) (f' : Y' ⟶ V.left) (sq : IsPullback g' f' f V.hom),
        IsIso ((spacesEtaleDerivedBaseChange T f V.hom g' f' sq).app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))))
    ⦃X' Y' : T.Spaces⦄ (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
    (sq : IsPullback g' f' f g) :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  have hU : IsIso ((totalRightDerivedUnit (bigEtalePushforward T f)).app
      (((CategoryTheory.Sites.abelianInverseImage
        (bigToSmallEtaleMorphism T Y)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
    refine isIso_of_isIso_mapDerivedCategory_affineThroughEtaleChart T _ fun V hV ↦ ?_
    obtain ⟨Y', g', f', sqV, hV'⟩ := h V hV
    have := hc V.hom g' f' sqV
    exact (isIso_spacesEtaleDerivedBaseChange_app_iff_restriction T f V.hom g' f' sqV I).mp hV'
  have := hc g g' f' sq
  exact (isIso_spacesEtaleDerivedBaseChange_app_iff_restriction T f g g' f' sq I).mpr
    inferInstance

/-- The inverse image of abelian sheaves along an étale morphism of algebraic spaces carries
torsion sheaves to torsion sheaves. -/
theorem torsionSheafProperty_smallEtaleAbelianInverseImage_of_isEtale {U V : T.Spaces}
    (h : U ⟶ V) (hh : Space.IsEtale T.fppfSite S T.fppf_mem h.hom)
    (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem V) Ab.{u + 1})
    (hF : Stacks.Torsion.torsionSheafProperty _ F) :
    Stacks.Torsion.torsionSheafProperty (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem U)
      ((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T h)).obj F) :=
  Stacks.Torsion.torsionSheafProperty_of_iso _
    ((smallEtaleAbelianInverseImageIsoPostcomp T h hh).app F).symm
    (Stacks.Torsion.isLocallyTorsion_comp_op _ _
      (Space.spacesEtalePostcomp T.fppfSite S T.fppf_mem h hh) F.obj hF)

/-- **The base change map along `a ≫ v`, with `v` étale, is the base change map of the base
change along `v`.** For cartesian squares
```
Y'' --a'--> Y_V --v'--> Y
|f''        |f_V        |f
v           v           v
W   --a---> V   --v---> X
```
with `v` étale and invertible abelian base-change maps for `f` along `a ≫ v` and for `f_V` along
`a`, the derived base change map of `f` along `a ≫ v` is invertible at a K-injective complex `I`
as soon as that of `f_V` along `a` is invertible at the K-injective complex `v'⁻¹ I`. -/
theorem isIso_spacesEtaleDerivedBaseChange_app_of_comp_isEtale {X Y V W YV Y'' : T.Spaces}
    (f : Y ⟶ X) (v : V ⟶ X) (hv : Space.IsEtale T.fppfSite S T.fppf_mem v.hom)
    (v' : YV ⟶ Y) (fV : YV ⟶ V) (sqV : IsPullback v' fV f v)
    (a : W ⟶ V) (a' : Y'' ⟶ YV) (f'' : Y'' ⟶ W) (sqa : IsPullback a' f'' fV a)
    (g' : Y'' ⟶ Y) (hg : a' ≫ v' = g') (sq : IsPullback g' f'' f (a ≫ v))
    [IsIso (spacesEtaleAbelianBaseChange T f (a ≫ v) g' f'' sq)]
    [IsIso (spacesEtaleAbelianBaseChange T fV a a' f'' sqa)]
    (I : CochainComplex (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1}) ℤ) [I.IsKInjective]
    (h : IsIso ((spacesEtaleDerivedBaseChange T fV a a' f'' sqa).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        (((CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T v')).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I))))) :
    IsIso ((spacesEtaleDerivedBaseChange T f (a ≫ v) g' f'' sq).app
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I))) := by
  subst hg
  have hv' : Space.IsEtale T.fppfSite S T.fppf_mem v'.hom :=
    Space.isEtale_of_isPullback T.fppfSite S T.fppf_mem _ _ _ _ sqV.flip hv
  have := isKInjective_smallEtaleAbelianInverseImage_of_isEtale T v' hv' I
  rw [isIso_spacesEtaleDerivedBaseChange_app_iff T fV a a' f'' sqa] at h
  rw [isIso_spacesEtaleDerivedBaseChange_app_iff T f (a ≫ v) (a' ≫ v') f'' sq]
  refine (NatTrans.isIso_app_iff_of_iso _ ?_).mpr h
  exact (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
    ((NatIso.mapHomologicalComplex (smallEtaleAbelianInverseImageCompIso T a' v')
      (ComplexShape.up ℤ)).app I ≪≫
      (Functor.mapHomologicalComplexCompIso
        (Iso.refl (CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T v') ⋙
          CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T a')))
        (ComplexShape.up ℤ)).symm.app I)

/-- **Derived proper base change over an affine base, along an affine base change.** For every
proper morphism `f_V : Y ⟶ h_V` of algebraic spaces to the space represented by an affine scheme
`V`, every morphism `a : h_W ⟶ h_V` from the space represented by an affine scheme `W` and every
cartesian square over `a`, the base change map is invertible at every bounded below object with
torsion cohomology sheaves. -/
def AffineBaseProperBaseChange : Prop :=
  ∀ ⦃V₀ W₀ : BigFppfOver T.fppfSite S T.fppf_mem⦄,
    IsAffine ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj V₀) →
    IsAffine ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj W₀) →
    ∀ ⦃Y Y'' : T.Spaces⦄ (fV : Y ⟶ Space.yonedaSpace T.fppfSite S T.fppf_mem V₀),
      Space.IsProper T.fppfSite S T.fppf_mem fV.hom →
      ∀ (a : Space.yonedaSpace T.fppfSite S T.fppf_mem W₀ ⟶
          Space.yonedaSpace T.fppfSite S T.fppf_mem V₀) (a' : Y'' ⟶ Y)
        (f'' : Y'' ⟶ Space.yonedaSpace T.fppfSite S T.fppf_mem W₀) (sq : IsPullback a' f'' fV a)
        (E : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
          Ab.{u + 1})) (n : ℤ), E.IsGE n → HasTorsionCohomology T E →
        IsIso ((spacesEtaleDerivedBaseChange T fV a a' f'' sq).app E)

/-- **Proper base change for squares of schemes, read on the spaces-étale sites.** For every
cartesian square
```
W' --n'--> W
|m'        |m
v          v
V' --n---> V
```
of the big fppf site of `S` whose right arrow has proper underlying morphism of schemes, the base
change map `spacesEtaleDerivedBaseChange` of the square of represented algebraic spaces is
invertible at every torsion abelian sheaf on the spaces-étale site of `h_W`, placed in degree
zero. -/
def RepresentableProperBaseChange : Prop :=
  ∀ ⦃V W V' W' : BigFppfOver T.fppfSite S T.fppf_mem⦄ (m : W ⟶ V) (n : V' ⟶ V) (n' : W' ⟶ W)
    (m' : W' ⟶ V'), IsPullback n' m' m n →
    _root_.AlgebraicGeometry.IsProper ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).map m) →
    ∀ (sq : IsPullback (Space.yonedaSpaceHom n') (Space.yonedaSpaceHom m')
        (Space.yonedaSpaceHom m) (Space.yonedaSpaceHom n))
      (F : Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem
        (Space.yonedaSpace T.fppfSite S T.fppf_mem W)) Ab.{u + 1}),
      Stacks.Torsion.torsionSheafProperty _ F →
      IsIso ((spacesEtaleDerivedBaseChange T (Space.yonedaSpaceHom m) (Space.yonedaSpaceHom n)
        (Space.yonedaSpaceHom n') (Space.yonedaSpaceHom m') sq).app
          ((DerivedCategory.singleFunctor _ 0).obj F))

/-- Having torsion cohomology sheaves is invariant under isomorphism. -/
private theorem hasTorsionCohomology_of_iso {Y : T.Spaces}
    {E E' : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})} (e : E ≅ E') (hT : HasTorsionCohomology T E) : HasTorsionCohomology T E' :=
  fun p ↦ Stacks.Torsion.torsionSheafProperty_of_iso _
    ((DerivedCategory.homologyFunctor _ p).mapIso e) (hT p)

/-- The abelian base-change map of a cartesian square of algebraic spaces with `f` proper is
invertible, given proper base change for étale sheaves of sets. -/
private theorem isIso_spacesEtaleAbelianBaseChange_of_isProper
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g) :
    IsIso (spacesEtaleAbelianBaseChange T f g g' f' sq) :=
  isIso_spacesEtaleAbelianBaseChange T f g g' f' sq
    (Space.isIso_spacesToposBaseChangeSquare_of_isProper_of_properBaseChange T.fppfSite S
      T.fppf_mem h0A3U f hf g g' f' sq)

/-- **Derived proper base change for one proper morphism, from its affine charts.** Assume proper
base change for étale sheaves of sets along proper morphisms of schemes (the hypothesis `h0A3U`),
and let `f : Y ⟶ X` be proper. Suppose that for every étale `v : h_{V₀} ⟶ X` and every
`a : h_{W₀} ⟶ h_{V₀}` with `V₀`, `W₀` affine there are cartesian squares
```
Y'' --a'--> Y_V --v'--> Y
|f''        |f_V        |f
v           v           v
h_{W₀} -a-> h_{V₀} -v-> X
```
along which the base change map of `f_V` along `a` is invertible on bounded below objects with
torsion cohomology sheaves. Then the base change map `g⁻¹ R f_* E ⟶ R f'_* (g')⁻¹ E` of every
cartesian square over `f` is invertible at every bounded below `E` with torsion cohomology
sheaves. -/
theorem isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_affineCharts
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    {X Y : T.Spaces} (f : Y ⟶ X) (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (H : ∀ ⦃V₀ W₀ : BigFppfOver T.fppfSite S T.fppf_mem⦄,
      IsAffine ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj V₀) →
      IsAffine ((BigFppfOver.toScheme T.fppfSite S T.fppf_mem).obj W₀) →
      ∀ (v : Space.yonedaSpace T.fppfSite S T.fppf_mem V₀ ⟶ X),
        Space.IsEtale T.fppfSite S T.fppf_mem v.hom →
      ∀ (a : Space.yonedaSpace T.fppfSite S T.fppf_mem W₀ ⟶
          Space.yonedaSpace T.fppfSite S T.fppf_mem V₀),
      ∃ (YV : T.Spaces) (v' : YV ⟶ Y) (fV : YV ⟶ Space.yonedaSpace T.fppfSite S T.fppf_mem V₀)
        (_ : IsPullback v' fV f v) (Y'' : T.Spaces) (a' : Y'' ⟶ YV)
        (f'' : Y'' ⟶ Space.yonedaSpace T.fppfSite S T.fppf_mem W₀)
        (sqa : IsPullback a' f'' fV a),
        ∀ (E : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem YV)
          Ab.{u + 1})) (n : ℤ), E.IsGE n → HasTorsionCohomology T E →
          IsIso ((spacesEtaleDerivedBaseChange T fV a a' f'' sqa).app E))
    {X' Y' : T.Spaces} (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    (E : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})) (n : ℤ) (hE : E.IsGE n) (hT : HasTorsionCohomology T E) :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app E) := by
  have hc : ∀ ⦃X' Y' : T.Spaces⦄ (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X')
      (sq : IsPullback g' f' f g), IsIso (spacesEtaleAbelianBaseChange T f g g' f' sq) :=
    fun _ _ g g' f' sq ↦ isIso_spacesEtaleAbelianBaseChange_of_isProper T h0A3U f hf g g' f' sq
  obtain ⟨L', hL'⟩ := HomotopyCategory.quotient_obj_surjective (DerivedCategory.Qh.objPreimage E)
  obtain ⟨I, q, hI, hq⟩ := Stacks.Cohomology.Localization.enoughKInjectives L'
  have hqi : IsIso (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q)) := by
    apply Localization.inverts DerivedCategory.Qh (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ))
    rwa [HomotopyCategory.quotient_map_mem_quasiIso_iff]
  let e : E ≅ DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I) :=
    (DerivedCategory.Qh.objObjPreimageIso E).symm ≪≫ eqToIso (by rw [← hL']) ≪≫
      asIso (DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map q))
  have hIE : (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)).IsGE n := by
    have := hE
    exact DerivedCategory.TStructure.t.isGE_of_iso e n
  have hIT : HasTorsionCohomology T
      (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) :=
    hasTorsionCohomology_of_iso T e hT
  rw [NatTrans.isIso_app_iff_of_iso _ e]
  refine isIso_spacesEtaleDerivedBaseChange_app_of_affineThroughEtaleChart T f hc I ?_ g g' f' sq
  rintro V ⟨W₀, V₀, hW, hV0, v, a, hv, rfl⟩
  obtain ⟨YV, v', fV, sqV, Y'', a', f'', sqa, hYV⟩ := H hV0 hW v hv a
  have sqO : IsPullback (a' ≫ v') f'' f (a ≫ v) := sqa.paste_horiz sqV
  have hfV : Space.IsProper T.fppfSite S T.fppf_mem fV.hom :=
    (Space.isProper_isStableUnderBaseChange T.fppfSite S T.fppf_mem).of_isPullback sqV hf
  have := hc (a ≫ v) (a' ≫ v') f'' sqO
  have := isIso_spacesEtaleAbelianBaseChange_of_isProper T h0A3U fV hfV a a' f'' sqa
  refine ⟨_, _, _, sqO, isIso_spacesEtaleDerivedBaseChange_app_of_comp_isEtale T f v hv v' fV sqV
    a a' f'' sqa (a' ≫ v') rfl sqO I ?_⟩
  have hv' : Space.IsEtale T.fppfSite S T.fppf_mem v'.hom :=
    Space.isEtale_of_isPullback T.fppfSite S T.fppf_mem _ _ _ _ sqV.flip hv
  let F := CategoryTheory.Sites.abelianInverseImage (smallEtaleMorphism T v')
  let eF : F.mapDerivedCategory.obj (DerivedCategory.Qh.obj
      ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj I)) ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) :=
    F.mapDerivedCategoryFactorsh.app _
  refine hYV _ n ?_ ?_
  · have := Functor.isGE_obj_mapDerivedCategory F _ n hIE
    exact DerivedCategory.TStructure.t.isGE_of_iso eF n
  · exact hasTorsionCohomology_of_iso T eF fun p ↦
      Stacks.Torsion.torsionSheafProperty_of_iso _ ((F.mapDerivedCategoryHomologyIso p).app _).symm
        (torsionSheafProperty_smallEtaleAbelianInverseImage_of_isEtale T _ hv' _ (hIT p))

/-- **Derived proper base change, from an affine base and an affine base change.** Assume proper
base change for étale sheaves of sets along proper morphisms of schemes (the hypothesis `h0A3U`)
and derived proper base change over an affine base along an affine base change
(`AffineBaseProperBaseChange`, the hypothesis `haff`). Then the base change map
`g⁻¹ R f_* E ⟶ R f'_* (g')⁻¹ E` of a cartesian square with `f` proper is invertible at every
bounded below `E` with torsion cohomology sheaves. -/
theorem isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_affineBase
    (h0A3U : ∀ {X X' Y Y' : Scheme.{u}} (f : X ⟶ Y) (g : Y' ⟶ Y) (g' : X' ⟶ X) (f' : X' ⟶ Y')
      (sq : IsPullback g' f' f g), _root_.AlgebraicGeometry.IsProper f →
        IsIso (Stacks.EtaleCohomology.smallEtaleSetBaseChange.{u, 0} g' f' f g sq.w))
    (haff : AffineBaseProperBaseChange T)
    {X Y X' Y' : T.Spaces} (f : Y ⟶ X) (hf : Space.IsProper T.fppfSite S T.fppf_mem f.hom)
    (g : X' ⟶ X) (g' : Y' ⟶ Y) (f' : Y' ⟶ X') (sq : IsPullback g' f' f g)
    (E : DerivedCategory (Sheaf (Space.SpacesEtale.topology T.fppfSite S T.fppf_mem Y)
      Ab.{u + 1})) (n : ℤ) (hE : E.IsGE n) (hT : HasTorsionCohomology T E) :
    IsIso ((spacesEtaleDerivedBaseChange T f g g' f' sq).app E) := by
  refine isIso_spacesEtaleDerivedBaseChange_app_of_isProper_of_affineCharts T h0A3U f hf
    (fun V₀ W₀ hV0 hW v _ a ↦ ?_) g g' f' sq E n hE hT
  have sqV := IsPullback.of_hasPullback f v
  refine ⟨_, _, _, sqV, _, _, _, IsPullback.of_hasPullback (pullback.snd f v) a,
    fun E n hE hT ↦ haff hV0 hW _ ?_ a _ _ _ E n hE hT⟩
  exact (Space.isProper_isStableUnderBaseChange T.fppfSite S T.fppf_mem).of_isPullback sqV hf

end AlgebraicGeometry.BigEtaleSpaceSite

end
