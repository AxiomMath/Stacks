module

public import StacksFrontier.AlgebraicGeometry.Descent.Germ.OfSchemeHom
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase
public import StacksFrontier.AlgebraicGeometry.Quot.CartesianFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamiliesOverSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation
public import StacksFrontier.AlgebraicGeometry.Spaces.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopology
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsTopologyUnique
public import StacksFrontier.AlgebraicGeometry.Spaces.SchemeAsSpace
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBase
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallerBaseProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothLocalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.Deformation.Artin.Predeformation
public import StacksFrontier.Deformation.Artin.Versality
public import StacksFrontier.Deformation.Artin.Versality.Openness
import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FibreDimension
import StacksFrontier.AlgebraicGeometry.Spaces.Points
import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDimensionChart
import StacksFrontier.AlgebraicGeometry.Spaces.StronglyCartesian
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf
import all StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.SmoothnessOverNoetherianBase

/-!
# Openness of versality for families of curves

Openness of versality for the stack of curves (Stacks 0D59), deduced from openness of versality
for the stack of finitely presented, flat and proper algebraic spaces (Stacks 0D3X), which is
taken as the hypothesis `hPF`. The families of curves are the finitely presented, flat and proper
families of relative dimension at most one, a full subcategory of the families of Stacks 0D1E.
Over `Spec ℤ` the comparison is an isomorphism of categories. Over a Noetherian scheme `S` it is
the fully faithful functor from the costructured arrow category of Stacks 0D54 given by the
base-change equivalence of Stacks 04SG, and versality is transported along it in both
directions.

## Main definitions

* `Deformation.Artin.OpenVersalityOf`: openness of versality (Stacks 07XQ (1)) as a predicate on
  a functor `q : 𝒳 ⥤ Over S` alone.

## Main results

* `Deformation.Artin.isOpenVersality_iff_openVersalityOf`: `Deformation.Artin.OpenVersalityOf q`
  is `Deformation.Artin.IsOpenVersality q hq`.
* `AlgebraicGeometry.curves_openVersality_specZ_of_properFlatSpaces`: openness of versality for
  curves over `Spec ℤ`, with Stacks 0D3X over `Spec ℤ` as a hypothesis.
* `AlgebraicGeometry.curves_openVersality_of_properFlatSpaces`: openness of versality for curves
  over a Noetherian scheme `S`, with Stacks 0D3X over `S` as a hypothesis.

## References

* [Stacks Project, Tag 0D59](https://stacks.math.columbia.edu/tag/0D59)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
* [Stacks Project, Tag 0D54](https://stacks.math.columbia.edu/tag/0D54)
* [Stacks Project, Tag 0D1E](https://stacks.math.columbia.edu/tag/0D1E)
* [Stacks Project, Tag 04SG](https://stacks.math.columbia.edu/tag/04SG)
* [Stacks Project, Tag 0CXU](https://stacks.math.columbia.edu/tag/0CXU)
* [Stacks Project, Tag 0G2K](https://stacks.math.columbia.edu/tag/0G2K)
* [Stacks Project, Tag 0CXM](https://stacks.math.columbia.edu/tag/0CXM)
-/


@[expose] public section

attribute [local implicit_reducible] AlgebraicGeometry.curvesProjectionOver

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin

universe u vX wX

/-- Openness of versality, **Stacks 07XQ part (1)**, as a predicate on a functor `q : 𝒳 ⥤ Over S`
alone: versality of an object at a finite-type point of a base locally of finite type over `S`
persists at every finite-type point of an open neighbourhood. This is
`Deformation.Artin.IsOpenVersality` without its fibredness argument, which that predicate
ignores. -/
public abbrev OpenVersalityOf {S : Scheme.{u}} {X : Type vX} [Category.{wX} X]
    (q : X ⥤ Over S) : Prop :=
  ∀ (U : Over S), LocallyOfFiniteType U.hom →
    ∀ (x : X) (hx : q.obj x = U) (u₀ : U.left),
      IsFiniteTypePoint u₀ →
      IsVersalAt U q u₀ x hx →
      ∃ V : U.left.Opens, u₀ ∈ V.1 ∧
        ∀ (u : U.left), u ∈ V.1 →
          IsFiniteTypePoint u →
          IsVersalAt U q u x hx

/-- `Deformation.Artin.OpenVersalityOf` is `Deformation.Artin.IsOpenVersality`: the fibredness
datum the latter carries does not enter the proposition. -/
public theorem isOpenVersality_iff_openVersalityOf {S : Scheme.{u}} {X : Type vX}
    [Category.{wX} X] (q : X ⥤ Over S) (hq : q.IsFiberedInGroupoids) :
    IsOpenVersality q hq ↔ OpenVersalityOf q := Iff.rfl

end Deformation.Artin

namespace AlgebraicGeometry

open Deformation.Artin

universe u

/-! ### Comparison of families of curves with proper flat families -/

namespace CurvesVersality

/-! ### Names for the two categories of Stacks 0D1E -/

/-- Algebraic spaces over varying base schemes of the big fppf site of `S`: the comma category
whose objects are an algebraic space over `S`, a scheme of the site, and a morphism from the
first to the presheaf of the second: the ambient category of Stacks 0D1E. -/
private abbrev spaceFamilies (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :=
  Comma
    (ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
      IsAlgebraicSpace B S hS F))
    (yoneda : BigFppfOver B S hS ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- The objects of Stacks 0D1E: the finitely presented, flat and proper families, before the
morphisms are cut down to the cartesian ones. -/
private abbrev properFlatSpaceObjects (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) := (isProperFlatSpace B S hS).FullSubcategory

/-- `AlgebraicGeometry.schemeSpace`, as a reducible alias: the algebraic space whose underlying
presheaf is `yoneda.obj U`. -/
private abbrev schemeSpace_ {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    (U : BigFppfOver B S hS) : AlgebraicSpaces B S hS :=
  Space.representedAlgebraicSpace B S hS U

/-- `AlgebraicGeometry.schemeSpaceMap`, as a reducible alias. -/
private abbrev schemeSpaceMap_ {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {U V : BigFppfOver B S hS} (g : U ⟶ V) : schemeSpace_ U ⟶ schemeSpace_ V :=
  ObjectProperty.homMk (yoneda.map g)

/-- The structural morphism of a family of curves, with its codomain written as the representable
presheaf of the base rather than as the algebraic space of the base. -/
private abbrev curveToBase {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}
    (X : CurveFamily B hZ) : X.total.obj ⟶ yoneda.obj X.base := CurveFamily.toBase X |>.hom

/-! ### Forms of the morphism properties carrying the algebraicity hypotheses -/

/-- `AlgebraicGeometry.Space.pointTopology` taking the algebraicity of its argument, as the
members of `AlgebraicGeometry.Space.PointTopologyFamily` do. -/
private abbrev spacePointTopology (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (_hF : IsAlgebraicSpace B S hS F) :
    TopologicalSpace (Space.points B S hS F) :=
  Space.pointTopology B S hS F

/-- `AlgebraicGeometry.Space.IsClosedMorphism` taking the algebraicity of source and target. -/
private abbrev spaceIsClosedMorphism (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_hF : IsAlgebraicSpace B S hS F)
    (_hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) : Prop :=
  Space.IsClosedMorphism B S hS f

/-- `AlgebraicGeometry.Space.UniversallyClosed` taking the algebraicity of source and target. -/
private abbrev spaceUniversallyClosed (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_hF : IsAlgebraicSpace B S hS F)
    (_hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) : Prop :=
  Space.UniversallyClosed B S hS f

/-- `AlgebraicGeometry.Space.IsProper` taking the algebraicity of source and target. -/
private abbrev spaceIsProper (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (_hF : IsAlgebraicSpace B S hS F)
    (_hG : IsAlgebraicSpace B S hS G) (f : F ⟶ G) : Prop :=
  Space.IsProper B S hS f

/-- The base-change equivalence of Stacks 04SG together with the identification of its forward
functor with the lower-shriek extension. -/
private noncomputable def smallerBaseEquivalenceData (B : BigFppfSite.{u}) (S S' : Scheme.{u})
    (hS : B.Contains S) (hS' : B.Contains S') (g : B.obj hS ⟶ B.obj hS') :
    Σ e : AlgebraicSpaces B S hS ≌ SpacesOverSmallerBase B S S' hS hS' g,
      (e.functor ⋙
          (ObjectProperty.ι (fun X : Over (yoneda.obj (Over.mk g) :
            (BigFppfOver B S' hS')ᵒᵖ ⥤ Type u) =>
              IsAlgebraicSpace B S' hS' X.left)) ⋙
          Over.forget (yoneda.obj (Over.mk g))) ≅
        ((ObjectProperty.ι (fun F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u =>
            IsAlgebraicSpace B S hS F)) ⋙
          OverShriek.relocalizePresheafFunctor g) :=
  ⟨spacesOverSmallerBaseEquivalence B S S' hS hS' g,
    spacesOverSmallerBaseFunctorForgetIso B S S' hS hS' g⟩


/-- Schemes of size below the cutoff of `B` form a property closed under isomorphisms. -/
local instance schemeCutoff_isClosedUnderIsomorphisms
    (B : AlgebraicGeometry.BigFppfSite.{u}) :
    ObjectProperty.IsClosedUnderIsomorphisms
      (fun X : Scheme.{u} ↦ X.size < B.cutoff) where
  of_iso {X Y} e h := by rwa [← Scheme.size_congr e]

/-- Schemes of size below the cutoff of `B` form a property closed under pullbacks. -/
local instance schemeCutoff_isClosedUnderPullbacks
    (B : AlgebraicGeometry.BigFppfSite.{u}) :
    ObjectProperty.IsClosedUnderLimitsOfShape
      (fun X : Scheme.{u} ↦ X.size < B.cutoff) WalkingCospan :=
  .mk' (by
    rintro _ ⟨F, hF⟩
    rw [Scheme.size_congr (HasLimit.isoOfNatIso (diagramIsoCospan F))]
    exact Scheme.size_pullback_lt _ _ (hF .left) (hF .right))

attribute [local instance] AlgebraicGeometry.BigFppfSite.hasPullbacks_schemes

/-- Pullbacks in presheaf categories on the big fppf site (instance search times out
without this shortcut). -/
local instance (priority := high) hasPullback_presheaf_ProperFlatFamilies
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

set_option synthInstance.maxHeartbeats 400000 in
/-- Limits of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasLimits_presheaf_ProperFlatFamilies
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasFiniteLimits ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Pullbacks of presheaves on the big fppf site (instance search times out without this
shortcut). -/
local instance hasPullbacks_presheaf_ProperFlatFamilies
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

set_option synthInstance.maxHeartbeats 400000 in
/-- Small discrete limits of presheaves on the big fppf site (instance search times out
without this shortcut). -/
local instance hasLimitsOfShape_discrete_presheaf_ProperFlatFamilies
    {B : AlgebraicGeometry.BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {J : Type} : HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

private theorem surjective_specMap_of_artinianLocal
    (R T : CommRingCat.{u}) [IsLocalRing R] [IsArtinianRing R]
    [IsLocalRing T] [IsArtinianRing T] (f : R ⟶ T) :
    Function.Surjective (Spec.map f) := by
  let : Subsingleton (Spec R) := subsingleton_spec_of_isArtinianRing R
  let : Subsingleton (Spec T) := subsingleton_spec_of_isArtinianRing T
  intro p
  refine ⟨IsLocalRing.closedPoint T, ?_⟩
  have hp : p = IsLocalRing.closedPoint R :=
    Subsingleton.elim _ _
  have hmap : Spec.map f (IsLocalRing.closedPoint T) =
      IsLocalRing.closedPoint R := Subsingleton.elim _ _
  rw [hmap, hp]

private theorem relativeDimensionLE_of_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y' Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : IsPullback g' f' f g)
    (_hX' : AlgebraicGeometry.IsAlgebraicSpace B S hS X')
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY' : AlgebraicGeometry.IsAlgebraicSpace B S hS Y')
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (hrel : Space.HasRelativeDimensionLE 1 B S hS f) :
    Space.HasRelativeDimensionLE 1 B S hS f' := by
  intro x'
  obtain ⟨d, hd, hdim⟩ := hrel (Space.pointsMap B S hS X' g' x')
  refine ⟨d, hd, ?_⟩
  exact (AlgebraicGeometry.Space.hasRelativeDimensionAt_iff_of_isPullback
    B S hS h hX hY' hY hf x' d).mp hdim

private theorem relativeDimensionLE_of_pullback_of_surjective_points
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y' Y : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g' : X' ⟶ X) (f' : X' ⟶ Y') (f : X ⟶ Y) (g : Y' ⟶ Y)
    (h : IsPullback g' f' f g)
    (_hX' : AlgebraicGeometry.IsAlgebraicSpace B S hS X')
    (hX : AlgebraicGeometry.IsAlgebraicSpace B S hS X)
    (hY' : AlgebraicGeometry.IsAlgebraicSpace B S hS Y')
    (hY : AlgebraicGeometry.IsAlgebraicSpace B S hS Y)
    (hf : Space.IsLocallyOfFiniteType B S hS f)
    (hsurj : Function.Surjective (Space.pointsMap B S hS X' g'))
    (hrel : Space.HasRelativeDimensionLE 1 B S hS f') :
    Space.HasRelativeDimensionLE 1 B S hS f := by
  intro x
  obtain ⟨x', hx'⟩ := hsurj x
  obtain ⟨d, hd, hdim⟩ := hrel x'
  refine ⟨d, hd, ?_⟩
  have hdim' := (AlgebraicGeometry.Space.hasRelativeDimensionAt_iff_of_isPullback
    B S hS h hX hY' hY hf x' d).mpr hdim
  rw [hx'] at hdim'
  exact hdim'

private noncomputable def properFlatCommaHomAsSpaceMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (C : spaceFamilies B S hS) :
    C.left ⟶ schemeSpace C.right :=
  ObjectProperty.homMk (show C.left.obj ⟶ (schemeSpace C.right).obj from by
    change (ObjectProperty.ι _).obj C.left ⟶ yoneda.obj C.right
    exact C.hom)

private noncomputable def properFlatCommaHomAsSpaceMap_over
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (C : spaceFamilies B S hS) :
    C.left ⟶ schemeSpace C.right :=
  ObjectProperty.homMk (show C.left.obj ⟶ (schemeSpace C.right).obj from by
    change (ObjectProperty.ι _).obj C.left ⟶ yoneda.obj C.right
    exact C.hom)


private noncomputable def properFlatAsCurve
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (hZ : B.Contains integerBase)
    (X : CartesianProperFlatSpaces B integerBase hZ)
    (hDim : Space.HasRelativeDimensionLE 1 B integerBase hZ
      X.obj.obj.hom) : AlgebraicGeometry.CurveFamily B hZ := by
  let C := X.obj.obj
  refine {
    base := C.right
    total := C.left
    toBase := properFlatCommaHomAsSpaceMap B integerBase hZ C
    flat := ?_
    proper := ?_
    finitePresentation := ?_
    relativeDimensionLE := by
      change Space.HasRelativeDimensionLE 1 B integerBase hZ C.hom
      exact hDim
  }
  · change Space.IsFlat B integerBase hZ C.hom
    exact X.obj.property.2.1
  · change spaceIsProper B integerBase hZ C.left.property
      (schemeSpace C.right).property C.hom
    exact X.obj.property.2.2
  · change AlgebraicGeometry.Space.IsFinitePresentation B integerBase hZ C.hom
    exact X.obj.property.1

private theorem spaceFamily_morphism_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {A C : spaceFamilies B S hS} (m : A ⟶ C)
    (hsc : (spacesProjection B S hS).IsStronglyCartesian
      ((spacesProjection B S hS).map m) m) :
    IsPullback m.left.hom A.hom C.hom (yoneda.map m.right) := by
  have hpull' : IsPullback A.hom m.left.hom
      (schemeSpaceMap m.right).hom
      (ObjectProperty.homMk C.hom).hom := by
    let t : A.left ⟶ AlgebraicSpaces.fiberProduct B S hS
        (schemeSpaceMap m.right) (ObjectProperty.homMk C.hom) :=
      ObjectProperty.homMk (pullback.lift A.hom m.left.hom m.w.symm)
    have hiso : IsIso t :=
      (AlgebraicGeometry.spacesProjection_isStronglyCartesian_iff
        (B := B) (S := S) (hS := hS) (m := m)).mp hsc
    let e₀ := asIso t
    let e := (ObjectProperty.ι _).mapIso e₀
    apply IsPullback.of_iso_pullback (CommSq.mk (by
      simpa [schemeSpaceMap, schemeSpace] using
        (show A.hom ≫ yoneda.map m.right = m.left.hom ≫ C.hom from m.w.symm))) e
    · show e.hom ≫ pullback.fst (yoneda.map m.right) C.hom = A.hom
      show (ObjectProperty.ι _).map t ≫
        pullback.fst (yoneda.map m.right) C.hom = A.hom
      show pullback.lift A.hom m.left.hom m.w.symm ≫
        pullback.fst (yoneda.map m.right) C.hom = A.hom
      exact pullback.lift_fst _ _ _
    · show e.hom ≫ pullback.snd (yoneda.map m.right) C.hom = m.left.hom
      show (ObjectProperty.ι _).map t ≫
        pullback.snd (yoneda.map m.right) C.hom = m.left.hom
      show pullback.lift A.hom m.left.hom m.w.symm ≫
        pullback.snd (yoneda.map m.right) C.hom = m.left.hom
      exact pullback.lift_snd _ _ _
  simpa [schemeSpaceMap, schemeSpace,
    ObjectProperty.ι_obj, ObjectProperty.homMk_hom] using hpull'.flip

private theorem properFlatHom_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CartesianProperFlatSpaces B S hS} (f : X ⟶ Y) :
    IsPullback f.hom.hom.left.hom X.obj.obj.hom Y.obj.obj.hom
      (yoneda.map f.hom.hom.right) := by
  have hsc : (spacesProjection B S hS).IsStronglyCartesian
      ((spacesProjection B S hS).map f.hom.hom) f.hom.hom := f.property
  exact spaceFamily_morphism_isPullback B S hS f.hom.hom hsc

private theorem properFlatHom_isPullback_over
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CartesianProperFlatSpaces B S hS} (f : X ⟶ Y) :
    IsPullback f.hom.hom.left.hom X.obj.obj.hom Y.obj.obj.hom
      (yoneda.map f.hom.hom.right) := by
  have hsc : (spacesProjection B S hS).IsStronglyCartesian
      ((spacesProjection B S hS).map f.hom.hom) f.hom.hom := f.property
  exact spaceFamily_morphism_isPullback B S hS f.hom.hom hsc


private theorem properFlatHom_isPullback_spaces
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CartesianProperFlatSpaces B S hS} (f : X ⟶ Y) :
    IsPullback f.hom.hom.left
      (properFlatCommaHomAsSpaceMap B S hS X.obj.obj)
      (properFlatCommaHomAsSpaceMap B S hS Y.obj.obj)
      (schemeSpaceMap f.hom.hom.right) := by
  let m := f.hom.hom
  have hsc : (spacesProjection B S hS).IsStronglyCartesian
      m.right m := f.property
  let Cx := X.obj.obj
  let Cy := Y.obj.obj
  let fbase := schemeSpaceMap m.right
  let cbase := properFlatCommaHomAsSpaceMap B S hS Cy
  let P := AlgebraicSpaces.fiberProduct B S hS fbase cbase
  let pFst : P ⟶ schemeSpace Cx.right := by
    simpa [P, AlgebraicSpaces.fiberProduct] using
      (ObjectProperty.homMk
        (CategoryTheory.Limits.pullback.fst fbase.hom cbase.hom) :
          AlgebraicSpaces.fiberProduct B S hS fbase cbase ⟶
            schemeSpace Cx.right)
  let pSnd : P ⟶ Cy.left := by
    simpa [P, AlgebraicSpaces.fiberProduct] using
      (ObjectProperty.homMk
        (CategoryTheory.Limits.pullback.snd fbase.hom cbase.hom) :
          AlgebraicSpaces.fiberProduct B S hS fbase cbase ⟶ Cy.left)
  let hp := AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS fbase cbase
  let lift : Cx.left ⟶ P := ObjectProperty.homMk
    (CategoryTheory.Limits.pullback.lift Cx.hom m.left.hom m.w.symm)
  have hlift : IsIso lift :=
    (AlgebraicGeometry.spacesProjection_isStronglyCartesian_iff m).mp hsc
  let e : Cx.left ≅ P := asIso lift
  have hfst : e.hom ≫ pFst = properFlatCommaHomAsSpaceMap B S hS Cx := by
    apply ObjectProperty.hom_ext
    show CategoryTheory.Limits.pullback.lift Cx.hom m.left.hom m.w.symm ≫
      CategoryTheory.Limits.pullback.fst fbase.hom cbase.hom = Cx.hom
    exact CategoryTheory.Limits.pullback.lift_fst _ _ _
  have hsnd : e.hom ≫ pSnd = m.left := by
    apply ObjectProperty.hom_ext
    show CategoryTheory.Limits.pullback.lift Cx.hom m.left.hom m.w.symm ≫
      CategoryTheory.Limits.pullback.snd fbase.hom cbase.hom = m.left.hom
    exact CategoryTheory.Limits.pullback.lift_snd _ _ _
  show IsPullback m.left
    (properFlatCommaHomAsSpaceMap B S hS Cx)
    (properFlatCommaHomAsSpaceMap B S hS Cy) (schemeSpaceMap m.right)
  apply hp.flip.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · calc
      pSnd = e.symm.hom ≫ e.hom ≫ pSnd := by simp
      _ = e.symm.hom ≫ m.left := by rw [hsnd]
  · calc
      pFst = e.symm.hom ≫ e.hom ≫ pFst := by simp
      _ = e.symm.hom ≫ properFlatCommaHomAsSpaceMap B S hS Cx := by rw [hfst]
  · rfl
  · rfl

private theorem properFlatHom_isPullback_spaces_over
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CartesianProperFlatSpaces B S hS} (f : X ⟶ Y) :
    IsPullback f.hom.hom.left
      (properFlatCommaHomAsSpaceMap_over B S hS X.obj.obj)
      (properFlatCommaHomAsSpaceMap_over B S hS Y.obj.obj)
      (schemeSpaceMap f.hom.hom.right) := by
  let m := f.hom.hom
  have hsc : (spacesProjection B S hS).IsStronglyCartesian
      m.right m := f.property
  let Cx := X.obj.obj
  let Cy := Y.obj.obj
  let fbase := schemeSpaceMap m.right
  let cbase := properFlatCommaHomAsSpaceMap_over B S hS Cy
  let P := AlgebraicSpaces.fiberProduct B S hS fbase cbase
  let pFst : P ⟶ schemeSpace Cx.right := by
    simpa [P, AlgebraicSpaces.fiberProduct] using
      (ObjectProperty.homMk
        (CategoryTheory.Limits.pullback.fst fbase.hom cbase.hom) :
          AlgebraicSpaces.fiberProduct B S hS fbase cbase ⟶
            schemeSpace Cx.right)
  let pSnd : P ⟶ Cy.left := by
    simpa [P, AlgebraicSpaces.fiberProduct] using
      (ObjectProperty.homMk
        (CategoryTheory.Limits.pullback.snd fbase.hom cbase.hom) :
          AlgebraicSpaces.fiberProduct B S hS fbase cbase ⟶ Cy.left)
  let hp := AlgebraicGeometry.AlgebraicSpaces.isPullback_fiberProduct B S hS fbase cbase
  let lift : Cx.left ⟶ P := ObjectProperty.homMk
    (CategoryTheory.Limits.pullback.lift Cx.hom m.left.hom m.w.symm)
  have hlift : IsIso lift :=
    (AlgebraicGeometry.spacesProjection_isStronglyCartesian_iff m).mp hsc
  let e : Cx.left ≅ P := asIso lift
  have hfst : e.hom ≫ pFst = properFlatCommaHomAsSpaceMap_over B S hS Cx := by
    apply ObjectProperty.hom_ext
    show CategoryTheory.Limits.pullback.lift Cx.hom m.left.hom m.w.symm ≫
      CategoryTheory.Limits.pullback.fst fbase.hom cbase.hom = Cx.hom
    exact CategoryTheory.Limits.pullback.lift_fst _ _ _
  have hsnd : e.hom ≫ pSnd = m.left := by
    apply ObjectProperty.hom_ext
    show CategoryTheory.Limits.pullback.lift Cx.hom m.left.hom m.w.symm ≫
      CategoryTheory.Limits.pullback.snd fbase.hom cbase.hom = m.left.hom
    exact CategoryTheory.Limits.pullback.lift_snd _ _ _
  show IsPullback m.left
    (properFlatCommaHomAsSpaceMap_over B S hS Cx)
    (properFlatCommaHomAsSpaceMap_over B S hS Cy) (schemeSpaceMap m.right)
  apply hp.flip.of_iso e.symm (Iso.refl _) (Iso.refl _) (Iso.refl _)
  · calc
      pSnd = e.symm.hom ≫ e.hom ≫ pSnd := by simp
      _ = e.symm.hom ≫ m.left := by rw [hsnd]
  · calc
      pFst = e.symm.hom ≫ e.hom ≫ pFst := by simp
      _ = e.symm.hom ≫ properFlatCommaHomAsSpaceMap_over B S hS Cx := by rw [hfst]
  · rfl
  · rfl


private theorem pointsMap_surjective_of_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S)
    {W Z X Y : AlgebraicSpaces B S hS}
    {p : W ⟶ Z} {q : W ⟶ X} {f : Z ⟶ Y} {g : X ⟶ Y}
    (h : IsPullback p q f g)
    (hbase : Function.Surjective (Space.pointsMap B S hS X.1 g.hom)) :
    Function.Surjective (Space.pointsMap B S hS W.1 p.hom) := by
  intro z
  obtain ⟨x, hx⟩ := hbase (Space.pointsMap B S hS Z.1 f.hom z)
  obtain ⟨w, hp, hq⟩ := AlgebraicGeometry.Space.exists_point_of_isPullback B S hS h z x hx.symm
  exact ⟨w, hp⟩

private theorem pointsMap_surjective_of_properFlatHom_of_surjective_base
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CartesianProperFlatSpaces B S hS} (f : X ⟶ Y)
    (hbase : Function.Surjective (Space.pointsMap B S hS
      (yoneda.obj X.obj.obj.right) (yoneda.map f.hom.hom.right))) :
    Function.Surjective (Space.pointsMap B S hS
      X.obj.obj.left.obj f.hom.hom.left.hom) :=
  pointsMap_surjective_of_isPullback B S hS
    (properFlatHom_isPullback_spaces B S hS f) hbase

private theorem pointsMap_surjective_of_properFlatHom_of_surjective_base_over
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CartesianProperFlatSpaces B S hS} (f : X ⟶ Y)
    (hbase : Function.Surjective (Space.pointsMap B S hS
      (yoneda.obj X.obj.obj.right) (yoneda.map f.hom.hom.right))) :
    Function.Surjective (Space.pointsMap B S hS
      X.obj.obj.left.obj f.hom.hom.left.hom) :=
  pointsMap_surjective_of_isPullback B S hS
    (properFlatHom_isPullback_spaces_over B S hS f) hbase


private theorem properFlatHom_pointsMap_surjective_of_base_nonempty_subsingleton
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CartesianProperFlatSpaces B S hS} (f : X ⟶ Y)
    (hXbase : Nonempty ((cartesianProperFlatProjection B S hS ⋙
      Over.post B.inclusion).obj X).left)
    (hYbase : Subsingleton ((cartesianProperFlatProjection B S hS ⋙
      Over.post B.inclusion).obj Y).left) :
    Function.Surjective (Space.pointsMap B S hS
      X.obj.obj.left.obj f.hom.hom.left.hom) := by
  let q := cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion
  let : Nonempty (q.obj X).left := hXbase
  let : Subsingleton (q.obj Y).left := hYbase
  have hbaseScheme : Function.Surjective (q.map f).left := by
    intro y
    obtain ⟨x⟩ := hXbase
    exact ⟨x, Subsingleton.elim _ _⟩
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) T
  let : HasPullbacks B.Schemes := inferInstance
  let : PreservesLimitsOfShape WalkingCospan T := by
    apply comp_preservesLimitsOfShape
  let : P.IsStableUnderBaseChange := ⟨by
    intro A C C' W g p p' g' hsq hp
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Surjective) (hsq.map T) hp⟩
  let : HasPullbacks (AlgebraicGeometry.BigFppfOver B S hS) := inferInstance
  have hscheme : P f.hom.hom.right := by
    show Surjective (T.map f.hom.hom.right)
    exact ⟨hbaseScheme⟩
  have hpresheaf : P.presheaf (yoneda.map f.hom.hom.right) :=
    MorphismProperty.relative_map hscheme
  have hbase := (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda B S hS
    (yoneda.obj Y.obj.obj.right)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Y.obj.obj.right)
    X.obj.obj.right (yoneda.map f.hom.hom.right)).mp hpresheaf
  exact pointsMap_surjective_of_properFlatHom_of_surjective_base B S hS f hbase

private theorem properFlatHom_pointsMap_surjective_of_base_nonempty_subsingleton_over
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : CartesianProperFlatSpaces B S hS} (f : X ⟶ Y)
    (hXbase : Nonempty ((cartesianProperFlatProjection B S hS ⋙
      Over.post B.inclusion).obj X).left)
    (hYbase : Subsingleton ((cartesianProperFlatProjection B S hS ⋙
      Over.post B.inclusion).obj Y).left) :
    Function.Surjective (Space.pointsMap B S hS
      X.obj.obj.left.obj f.hom.hom.left.hom) := by
  let q := cartesianProperFlatProjection B S hS ⋙ Over.post B.inclusion
  let : Nonempty (q.obj X).left := hXbase
  let : Subsingleton (q.obj Y).left := hYbase
  have hbaseScheme : Function.Surjective (q.map f).left := by
    intro y
    obtain ⟨x⟩ := hXbase
    exact ⟨x, Subsingleton.elim _ _⟩
  let T := AlgebraicGeometry.BigFppfOver.toScheme B S hS
  let P := MorphismProperty.inverseImage
    (@Surjective.{u} : MorphismProperty Scheme.{u}) T
  let : HasPullbacks B.Schemes := inferInstance
  let : PreservesLimitsOfShape WalkingCospan T := by
    apply comp_preservesLimitsOfShape
  let : P.IsStableUnderBaseChange := ⟨by
    intro A C C' W g p p' g' hsq hp
    exact MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @Surjective) (hsq.map T) hp⟩
  let : HasPullbacks (AlgebraicGeometry.BigFppfOver B S hS) := inferInstance
  have hscheme : P f.hom.hom.right := by
    show Surjective (T.map f.hom.hom.right)
    exact ⟨hbaseScheme⟩
  have hpresheaf : P.presheaf (yoneda.map f.hom.hom.right) :=
    MorphismProperty.relative_map hscheme
  have hbase := (AlgebraicGeometry.Space.presheafSurjective_iff_isSurjective_yoneda B S hS
    (yoneda.obj Y.obj.obj.right)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Y.obj.obj.right)
    X.obj.obj.right (yoneda.map f.hom.hom.right)).mp hpresheaf
  exact pointsMap_surjective_of_properFlatHom_of_surjective_base_over B S hS f hbase


private theorem properFlat_relativeDimensionLE_of_artinianArrow
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y Z : CartesianProperFlatSpaces B S hS} (f : Y ⟶ Z)
    (hYdim : Space.HasRelativeDimensionLE 1 B S hS Y.obj.obj.hom)
    (hYbase : Nonempty ((cartesianProperFlatProjection B S hS ⋙
      Over.post B.inclusion).obj Y).left)
    (hZbase : Subsingleton ((cartesianProperFlatProjection B S hS ⋙
      Over.post B.inclusion).obj Z).left) :
    Space.HasRelativeDimensionLE 1 B S hS Z.obj.obj.hom := by
  have hsurj := properFlatHom_pointsMap_surjective_of_base_nonempty_subsingleton
    B S hS f hYbase hZbase
  have hft : Space.IsLocallyOfFiniteType B S hS Z.obj.obj.hom :=
    AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      Z.obj.property.1.1
  exact relativeDimensionLE_of_pullback_of_surjective_points B S hS
    (g' := f.hom.hom.left.hom) (f' := Y.obj.obj.hom) (f := Z.obj.obj.hom)
    (g := yoneda.map f.hom.hom.right)
    (properFlatHom_isPullback B S hS f)
    Y.obj.obj.left.property Z.obj.obj.left.property
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Y.obj.obj.right)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Z.obj.obj.right)
    hft hsurj hYdim

private theorem properFlat_relativeDimensionLE_of_artinianArrow_over
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y Z : CartesianProperFlatSpaces B S hS} (f : Y ⟶ Z)
    (hYdim : Space.HasRelativeDimensionLE 1 B S hS Y.obj.obj.hom)
    (hYbase : Nonempty ((cartesianProperFlatProjection B S hS ⋙
      Over.post B.inclusion).obj Y).left)
    (hZbase : Subsingleton ((cartesianProperFlatProjection B S hS ⋙
      Over.post B.inclusion).obj Z).left) :
    Space.HasRelativeDimensionLE 1 B S hS Z.obj.obj.hom := by
  have hsurj := properFlatHom_pointsMap_surjective_of_base_nonempty_subsingleton_over
    B S hS f hYbase hZbase
  have hft : Space.IsLocallyOfFiniteType B S hS Z.obj.obj.hom :=
    AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isLocallyOfFinitePresentation B S hS
      Z.obj.property.1.1
  exact relativeDimensionLE_of_pullback_of_surjective_points B S hS
    (g' := f.hom.hom.left.hom) (f' := Y.obj.obj.hom) (f := Z.obj.obj.hom)
    (g := yoneda.map f.hom.hom.right)
    (properFlatHom_isPullback_over B S hS f)
    Y.obj.obj.left.property Z.obj.obj.left.property
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Y.obj.obj.right)
    (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS Z.obj.obj.right)
    hft hsurj hYdim


end CurvesVersality

end AlgebraicGeometry

end
