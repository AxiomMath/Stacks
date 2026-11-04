module

public import StacksFrontier.AlgebraicGeometry.Topologies.InverseImageArrow
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeDescentAffineSituation
public import StacksFrontier.AlgebraicGeometry.ModulePullbackPseudofunctor.Basic
public import StacksFrontier.AlgebraicGeometry.Conormal.IsoSquare
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.ExactAlongAnIsomorphism
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons

/-!
# Relative perfectness across an isomorphism of arrows of schemes

Let `f : X ⟶ S` and `f' : X' ⟶ S'` be morphisms of schemes and `φ` an isomorphism between them in
the arrow category of ringed spaces. Derived restriction of scalars along `f` and along `f'`
are the derived pushforwards along the units `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` of
`AlgebraicGeometry.RingedSpace.inverseImageArrowUnit`, and the naturality of that unit is a
commutative square of ringed spaces whose horizontal edges are isomorphisms. Its derived square
matches derived restriction of scalars with derived pullback, and relative perfectness in the
sense of Stacks 0DI0 transports across `φ`.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.derivedSquareOfNatIso`: the isomorphism of derived functors
  induced by an isomorphism of two composites of exact functors.
* `AlgebraicGeometry.Scheme.Hom.derivedMatchingIso`: derived restriction of scalars along `f`
  after derived pullback along the source leg of `φ` is derived pullback along the induced
  isomorphism of inverse-image ringed spaces after derived restriction of scalars along `f'`.
* `AlgebraicGeometry.Scheme.Hom.ringedArrowIsoSpec`: the arrow isomorphism between an affine
  morphism of affine schemes and the spectrum of its map on global sections.

## Main results

* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_arrowIso_iff`: relative perfectness
  transports across an isomorphism of arrows.
* `AlgebraicGeometry.Scheme.Hom.isPerfectRelativeTo_isoSpec_iff_unconditional`: relative
  perfectness of an affine morphism of affine schemes transports along
  `AlgebraicGeometry.Scheme.isoSpec` to the spectrum of its map on global sections.

## References

* [Stacks Project, Definition 36.35.1 (Tag 0DI0)](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Lemma 36.35.9 (Tag 0DI8)](https://stacks.math.columbia.edu/tag/0DI8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits StrictlyPerfect
open RingedSpaceModuleAdjunction
open AlgebraicGeometry AlgebraicGeometry.RingedSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry.Scheme.Hom

/-! ### The generic derived square -/

/-- An isomorphism `F ⋙ G ≅ F' ⋙ G'` of composites of exact functors between abelian categories
induces an isomorphism of the composites of their derived functors at every object `E`. -/
def derivedSquareOfNatIso {C₁ C₂ C₃ C₄ : Type*}
    [Category* C₁] [Abelian C₁] [HasDerivedCategory C₁]
    [Category* C₂] [Abelian C₂] [HasDerivedCategory C₂]
    [Category* C₃] [Abelian C₃] [HasDerivedCategory C₃]
    [Category* C₄] [Abelian C₄] [HasDerivedCategory C₄]
    (E : DerivedCategory C₁) (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₄) (F' : C₁ ⥤ C₃) (G' : C₃ ⥤ C₄)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    [F'.Additive] [PreservesFiniteLimits F'] [PreservesFiniteColimits F']
    [G'.Additive] [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (e : F ⋙ G ≅ F' ⋙ G') :
    G.mapDerivedCategory.obj (F.mapDerivedCategory.obj E) ≅
      G'.mapDerivedCategory.obj (F'.mapDerivedCategory.obj E) :=
  (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F G).symm.app E ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso _ _ e).app E ≪≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryCompIso F' G').app E

/-! ### The arrow of ringed spaces attached to a morphism of schemes -/

variable {X X' S S' : Scheme.{u}}

/-- The morphism of schemes read as an arrow of ringed spaces. -/
abbrev ringedArrow (f : X ⟶ S) : Arrow RingedSpace.{u, u} :=
  Arrow.mk (Scheme.forgetToRingedSpace.map f)

/-- The identity-on-spaces morphism `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)`. -/
abbrev arrowUnit (f : X ⟶ S) :
    X.toRingedSpace ⟶ RingedSpace.inverseImage S.toRingedSpace f.base :=
  inverseImageArrowUnit.app (ringedArrow f)

variable (f : X ⟶ S) (f' : X' ⟶ S') (φ : ringedArrow f ≅ ringedArrow f')

/-- The isomorphism of the sources of the two morphisms. -/
abbrev arrowLeftIso : X.toRingedSpace ≅ X'.toRingedSpace := Arrow.leftFunc.mapIso φ

/-- The isomorphism of the two inverse-image ringed spaces. -/
abbrev arrowInverseImageIso :
    RingedSpace.inverseImage S.toRingedSpace f.base ≅
      RingedSpace.inverseImage S'.toRingedSpace f'.base :=
  inverseImageArrow.mapIso φ

/-- The naturality square of the unit `AlgebraicGeometry.Scheme.Hom.arrowUnit` at `φ`. -/
theorem arrowLeftIso_inv_comp_arrowUnit :
    (arrowLeftIso f f' φ).inv ≫ arrowUnit f =
      arrowUnit f' ≫ (arrowInverseImageIso f f' φ).inv :=
  inverseImageArrowUnit.naturality φ.inv

/-- Restriction of scalars is the pushforward along the unit of the arrow. -/
theorem scalarRestriction_eq_modulePushforward :
    scalarRestriction f = modulePushforward (arrowUnit f) := rfl

/-- Pushforward along the unit of the arrow preserves finite limits. -/
instance preservesFiniteLimits_modulePushforward_arrowUnit :
    PreservesFiniteLimits (modulePushforward (arrowUnit f)) :=
  Scheme.Hom.preservesFiniteLimits_scalarRestriction f

/-- Pushforward along the unit of the arrow preserves finite colimits. -/
instance preservesFiniteColimits_modulePushforward_arrowUnit :
    PreservesFiniteColimits (modulePushforward (arrowUnit f)) :=
  Scheme.Hom.preservesFiniteColimits_scalarRestriction f

/-- Derived restriction of scalars is the derived pushforward along the unit. -/
theorem derivedScalarRestriction_eq_mapDerivedCategory :
    derivedScalarRestriction f = (modulePushforward (arrowUnit f)).mapDerivedCategory := rfl

/-- Pullback along the source leg of `φ` followed by pushforward along the unit of `f` is
pushforward along the unit of `f'` followed by pullback along the induced isomorphism of
inverse-image ringed spaces. -/
def scalarRestrictionPullbackIso :
    modulePullback (arrowLeftIso f f' φ).hom ⋙ modulePushforward (arrowUnit f) ≅
      modulePushforward (arrowUnit f') ⋙ modulePullback (arrowInverseImageIso f f' φ).hom := by
  exact Functor.isoWhiskerRight (modulePullbackIsoPushforwardInv (arrowLeftIso f f' φ)) _ ≪≫
    Stacks.RingedSpace.modulePushforwardComp (arrowLeftIso f f' φ).inv (arrowUnit f) ≪≫
    eqToIso (congrArg modulePushforward (arrowLeftIso_inv_comp_arrowUnit f f' φ)) ≪≫
    (Stacks.RingedSpace.modulePushforwardComp (arrowUnit f')
      (arrowInverseImageIso f f' φ).inv).symm ≪≫
    Functor.isoWhiskerLeft _ (modulePullbackIsoPushforwardInv (arrowInverseImageIso f f' φ)).symm

/-- Derived pushforward along the unit of `f` after derived pullback along the source leg of `φ`
is derived pullback along the induced isomorphism of inverse-image ringed spaces after derived
pushforward along the unit of `f'`. -/
def derivedMatchingIso'
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'.toRingedSpace))) :
    (modulePushforward (arrowUnit f)).mapDerivedCategory.obj
        ((derivedPullback (arrowLeftIso f f' φ).hom).obj E) ≅
      (derivedPullback (arrowInverseImageIso f f' φ).hom).obj
        ((modulePushforward (arrowUnit f')).mapDerivedCategory.obj E) := by
  exact (modulePushforward (arrowUnit f)).mapDerivedCategory.mapIso
      ((Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIsoMapDerivedCategory
        (arrowLeftIso f f' φ)).app E) ≪≫
    derivedSquareOfNatIso E (modulePullback (arrowLeftIso f f' φ).hom)
      (modulePushforward (arrowUnit f)) (modulePushforward (arrowUnit f'))
      (modulePullback (arrowInverseImageIso f f' φ).hom)
      (scalarRestrictionPullbackIso f f' φ) ≪≫
    (Stacks.Cohomology.DerivedPullbackAlongIso.derivedPullbackIsoMapDerivedCategory
      (arrowInverseImageIso f f' φ)).symm.app
      ((modulePushforward (arrowUnit f')).mapDerivedCategory.obj E)

/-- Derived restriction of scalars along `f` after derived pullback along the source leg of `φ`
is derived pullback along the induced isomorphism of inverse-image ringed spaces after derived
restriction of scalars along `f'`. -/
def derivedMatchingIso (E : DerivedCategory (OXMod.{u, u} X'.toRingedSpace)) :
    (derivedScalarRestriction f).obj ((derivedPullback (arrowLeftIso f f' φ).hom).obj E) ≅
      (derivedPullback (arrowInverseImageIso f f' φ).hom).obj
        ((derivedScalarRestriction f').obj E) := by
  rw [derivedScalarRestriction_eq_mapDerivedCategory f,
    derivedScalarRestriction_eq_mapDerivedCategory f']
  exact derivedMatchingIso' f f' φ E


/-! ### Relative perfectness across the square, with no hypothesis -/

/-- Relative perfectness in the sense of Stacks 0DI0 transports across an isomorphism of arrows of
ringed spaces. -/
theorem isPerfectRelativeTo_arrowIso_iff [Flat f] [LocallyOfFinitePresentation f] [Flat f']
    [LocallyOfFinitePresentation f'] [CompactSpace X.carrier]
    (E : DerivedCategory (OXMod.{u, u} X'.toRingedSpace)) :
    f.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
        ((derivedPullback (arrowLeftIso f f' φ).hom).obj E) ↔
      f'.IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E :=
  isPerfectRelativeTo_derivedPullback_iso_iff f f' (arrowLeftIso f f' φ)
    (arrowInverseImageIso f f' φ) E (derivedMatchingIso f f' φ E)


/-! ### The affine case, read on spectra -/

/-- The isomorphism of arrows of ringed spaces between a morphism of affine schemes and the
spectrum of its map on global sections, given by `AlgebraicGeometry.Scheme.isoSpec`. -/
def ringedArrowIsoSpec (g : X ⟶ S) [IsAffine X] [IsAffine S] :
    ringedArrow g ≅ ringedArrow (Spec.map g.appTop) :=
  Arrow.isoMk (Scheme.forgetToRingedSpace.mapIso X.isoSpec)
    (Scheme.forgetToRingedSpace.mapIso S.isoSpec) (by
      change Scheme.forgetToRingedSpace.map X.isoSpec.hom ≫
          Scheme.forgetToRingedSpace.map (Spec.map g.appTop) =
        Scheme.forgetToRingedSpace.map g ≫ Scheme.forgetToRingedSpace.map S.isoSpec.hom
      rw [← Scheme.forgetToRingedSpace.map_comp, ← Scheme.forgetToRingedSpace.map_comp]
      exact congrArg Scheme.forgetToRingedSpace.map (Scheme.toSpecΓ_naturality g).symm)

/-- The left leg of that square is `AlgebraicGeometry.Scheme.isoSpec` on the source. -/
theorem arrowLeftIso_ringedArrowIsoSpec (g : X ⟶ S) [IsAffine X] [IsAffine S] :
    arrowLeftIso g (Spec.map g.appTop) (ringedArrowIsoSpec g) =
      Scheme.forgetToRingedSpace.mapIso X.isoSpec :=
  Iso.ext rfl

/-- A morphism of affine schemes is relatively perfect at the pullback of `E` along
`AlgebraicGeometry.Scheme.isoSpec` exactly when the spectrum of its map on global sections is
relatively perfect at `E`. -/
theorem isPerfectRelativeTo_isoSpec_iff_unconditional (g : X ⟶ S) [IsAffine X] [IsAffine S]
    [Flat g] [LocallyOfFinitePresentation g] [Flat (Spec.map g.appTop)]
    [LocallyOfFinitePresentation (Spec.map g.appTop)] [CompactSpace X.carrier]
    (E : DerivedCategory (OXMod.{u, u} (Spec Γ(X, ⊤)).toRingedSpace)) :
    g.IsPerfectRelativeTo (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _)
        ((derivedPullback (Scheme.forgetToRingedSpace.mapIso X.isoSpec).hom).obj E) ↔
      (Spec.map g.appTop).IsPerfectRelativeTo
        (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily _) E := by
  rw [← arrowLeftIso_ringedArrowIsoSpec g]
  exact isPerfectRelativeTo_arrowIso_iff g (Spec.map g.appTop) (ringedArrowIsoSpec g) E

end AlgebraicGeometry.Scheme.Hom

end
