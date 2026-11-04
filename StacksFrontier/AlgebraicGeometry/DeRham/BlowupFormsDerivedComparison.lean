module

public import StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDerivedRetraction
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.ExceptionalCurve
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.AdjunctionAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ExactPushforwardHomology

/-!
# The derived comparison of [Stacks, Tag 0FUU] clause (3)

Let `i : Z ⟶ X` be a closed immersion, let `b : X' ⟶ X` be the blowing up of `X` along `Z`, let
`j : E ⟶ X'` be the exceptional divisor and let `p : E ⟶ Z` be its structure morphism over the
centre, so that `j ≫ b = p ≫ i`.  For a morphism `f : X ⟶ S` and an integer `a`, clause (3) of
[Stacks, Tag 0FUU] is about the canonical map

`Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}`

in `D(𝒪_X)`.  This file constructs that map, so that the clause has a carrier.

## Main definitions

* `Stacks.DeRham.pushforwardSingleToDerived`: the comparison `g_*N ⟶ Rg_*N`, for a module `N`
  placed in degree zero.  It is the map belonging to the right-derived-functor structure of
  `AlgebraicGeometry.schemeDerivedPushforward`.
* `Stacks.DeRham.formsDerivedSquareComparison`: for any commutative square `j ≫ b = p ≫ i` of
  schemes over `S`, the map `Rb_*Ω^a_{X'/S} ⟶ Ri_*Rp_*Ω^a_{E/S}`.  It is built in three steps:
  1. `Rb_*` of the restriction `Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S} ⟶ Rj_*Ω^a_{E/S}`;
  2. the composition isomorphism `Rb_*Rj_* ≅ R(j ≫ b)_*` of [Stacks, Tag 0D5T];
  3. the equality `j ≫ b = p ≫ i`, then the composition isomorphism `R(p ≫ i)_* ≅ Ri_*Rp_*`.
* `Stacks.DeRham.blowupFormsDerivedComparison`: **the map of [Stacks, Tag 0FUU] clause (3)**.  It
  is that construction for the exceptional square of the blowup
  `AlgebraicGeometry.blowUpToBase i.ker`, with
  `p = AlgebraicGeometry.exceptionalDivisorToCentre i`.
* `Stacks.DeRham.derivedPushforwardHomologyIsoOfIsClosedImmersion`: for a closed immersion `i`,
  `H^q(Ri_*L) ≅ i_*H^q(L)`.  This is how the target of clause (3) reads as `i_*` of an
  `𝒪_Z`-module in each degree.

## Implementation notes

The target is written `Ri_*Rp_*` rather than `i_*Rp_*`.  For a closed immersion the two agree,
since `i_*` is exact (`Stacks.ClosedImmersion.derivedPushforwardIsoMapDerivedCategoryOfSchemes`),
and `derivedPushforwardHomologyIsoOfIsClosedImmersion` makes that agreement explicit on
cohomology sheaves.  The forms on `E` are those of the structure morphism `p ≫ i ≫ f`.  These
are the forms that clause (2) is about, in
`Stacks.DeRham.exceptionalFormsDirectImage`.

As in `StacksFrontier.AlgebraicGeometry.DeRham.BlowupFormsDerivedRetraction`, which this file
extends, `HasDerivedCategory.standard` is installed with raised priority, so the derived
categories here are the ones [Stacks, Tag 0G5J] is stated in.

## References

* [Stacks Project, Tag 0FUU](https://stacks.math.columbia.edu/tag/0FUU)
* [Stacks Project, Tag 0D5T](https://stacks.math.columbia.edu/tag/0D5T)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory
open Stacks.SchemeCohomology (hom)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
  (derivedPushforward derivedPushforwardCompIso)

universe u

attribute [local instance 10000] HasDerivedCategory.standard

namespace Stacks.DeRham

/-- **The comparison `g_*N ⟶ Rg_*N`** for a module `N` placed in degree zero: the map belonging
to the right-derived-functor structure of `AlgebraicGeometry.schemeDerivedPushforward`, read
through the two identifications of `K ↦ K[0]` with its homotopy-category spellings. -/
def pushforwardSingleToDerived {X Y : Scheme.{u}} (g : X ⟶ Y) (N : X.Modules) :
    (DerivedCategory.singleFunctor Y.Modules 0).obj ((Scheme.Modules.pushforward g).obj N) ⟶
      (schemeDerivedPushforward g).obj ((DerivedCategory.singleFunctor X.Modules 0).obj N) :=
  (DerivedCategory.singleFunctorIsoCompQh Y.Modules 0).hom.app _ ≫
    DerivedCategory.Qh.map
      (((Scheme.Modules.pushforward g).mapHomotopyCategorySingleFunctor 0).inv.app N) ≫
    (schemeDerivedPushforwardUnit g).app ((HomotopyCategory.singleFunctor X.Modules 0).obj N) ≫
    (schemeDerivedPushforward g).map
      ((DerivedCategory.singleFunctorIsoCompQh X.Modules 0).inv.app N)

/-- The canonical map `Ω^a_{X/S} ⟶ Rb_*Ω^a_{X'/S}` of
`Stacks.DeRham.formsDerivedDirectImage` is the underived comparison followed by
`Stacks.DeRham.pushforwardSingleToDerived`. -/
theorem formsDerivedDirectImage_eq {S X X' : Scheme.{u}} (f : X ⟶ S) (b : X' ⟶ X) (a : ℤ) :
    formsDerivedDirectImage f b a =
      (DerivedCategory.singleFunctor X.Modules 0).map
          (Scheme.Hom.formsDirectImageComparison b f a) ≫
        pushforwardSingleToDerived b _ := by
  simp only [formsDerivedDirectImage, pushforwardSingleToDerived]

/-- The object `Rφ_*Ω^a_{E/S}` depends only on `φ` and on the structure morphism of `E`, up to
equality. -/
theorem derivedPushforward_formsSingle_congr {S X E : Scheme.{u}}
    {φ₁ φ₂ : Stacks.SchemeCohomology.ringedSpace E ⟶ Stacks.SchemeCohomology.ringedSpace X}
    (hφ : φ₁ = φ₂) {f₁ f₂ : E ⟶ S} (hf : f₁ = f₂) (a : ℤ) :
    (derivedPushforward φ₁).obj (formsSingle f₁ a) =
      (derivedPushforward φ₂).obj (formsSingle f₂ a) := by
  subst hφ hf; rfl

/-- The underlying morphism of ringed spaces of a composite is the composite. -/
theorem schemeCohomologyHom_comp {X Y Z : Scheme.{u}} (g : X ⟶ Y) (h : Y ⟶ Z) :
    hom g ≫ hom h = hom (g ≫ h) := rfl

section Square

variable {S X X' Z E : Scheme.{u}} (f : X ⟶ S) {j : E ⟶ X'} {b : X' ⟶ X} {p : E ⟶ Z}
  {i : Z ⟶ X} (w : j ≫ b = p ≫ i)

/-- The identification `Rb_*Rj_*Ω^a_{E/S} ≅ Ri_*Rp_*Ω^a_{E/S}` attached to a commutative square
`j ≫ b = p ≫ i`: the two composition isomorphisms of [Stacks, Tag 0D5T] and the equality
`j ≫ b = p ≫ i` between them. -/
def formsDerivedSquareIso (a : ℤ) :
    (schemeDerivedPushforward b).obj
        ((schemeDerivedPushforward j).obj (formsSingle (j ≫ b ≫ f) a)) ≅
      (schemeDerivedPushforward i).obj
        ((schemeDerivedPushforward p).obj (formsSingle (p ≫ i ≫ f) a)) :=
  (derivedPushforwardCompIso (hom j) (hom b)).app _ ≪≫
    eqToIso (derivedPushforward_formsSingle_congr
      ((schemeCohomologyHom_comp j b).trans (congrArg hom w))
      (by rw [← Category.assoc, w, Category.assoc]) a) ≪≫
    ((derivedPushforwardCompIso (hom p) (hom i)).app _).symm

/-- **The comparison `Rb_*Ω^a_{X'/S} ⟶ Ri_*Rp_*Ω^a_{E/S}` of a commutative square**
`j ≫ b = p ≫ i` of schemes, with `X` over `S` by `f`.  It is `Rb_*` of the restriction
`Ω^a_{X'/S} ⟶ j_*Ω^a_{E/S} ⟶ Rj_*Ω^a_{E/S}`, followed by the composition isomorphism
`Rb_*Rj_* ≅ R(j ≫ b)_*`, then the equality `j ≫ b = p ≫ i`, then `R(p ≫ i)_* ≅ Ri_*Rp_*`. -/
def formsDerivedSquareComparison (a : ℤ) :
    (schemeDerivedPushforward b).obj (formsSingle (b ≫ f) a) ⟶
      (schemeDerivedPushforward i).obj
        ((schemeDerivedPushforward p).obj (formsSingle (p ≫ i ≫ f) a)) :=
  (schemeDerivedPushforward b).map
      ((DerivedCategory.singleFunctor _ 0).map
          (Scheme.Hom.formsDirectImageComparison j (b ≫ f) a) ≫
        pushforwardSingleToDerived j _) ≫
    (formsDerivedSquareIso f w a).hom

end Square

variable {S X Z : Scheme.{u}} (f : X ⟶ S) (i : Z ⟶ X) [IsClosedImmersion i]

/-- **The comparison map of [Stacks, Tag 0FUU] clause (3)**,
`Rb_*Ω^a_{X'/S} ⟶ i_*Rp_*Ω^a_{E/S}` in `D(𝒪_X)`.  Here `b : X' ⟶ X` is the blowing up of `X`
along the closed subscheme cut out by `i`, `E` is its exceptional divisor and
`p : E ⟶ Z` is the structure morphism of `E` over the centre.  The target is written as
`Ri_*Rp_*`, which is `i_*Rp_*` because `i_*` is exact; see
`Stacks.DeRham.derivedPushforwardHomologyIsoOfIsClosedImmersion`. -/
def blowupFormsDerivedComparison (a : ℤ) :
    (schemeDerivedPushforward (blowUpToBase i.ker)).obj
        (formsSingle (blowUpToBase i.ker ≫ f) a) ⟶
      (schemeDerivedPushforward i).obj
        ((schemeDerivedPushforward (exceptionalDivisorToCentre i)).obj
          (formsSingle (exceptionalDivisorToCentre i ≫ i ≫ f) a)) :=
  formsDerivedSquareComparison f (exceptionalDivisorToCentre_comp i).symm a

/-- **The cohomology sheaves of `Ri_*L` are `i_*` of those of `L`**, for a closed immersion `i`:
`H^q(Ri_*L) ≅ i_*H^q(L)`, because `i_*` is exact. -/
def derivedPushforwardHomologyIsoOfIsClosedImmersion (q : ℤ)
    (L : DerivedCategory Z.Modules) :
    (DerivedCategory.homologyFunctor X.Modules q).obj ((schemeDerivedPushforward i).obj L) ≅
      (Scheme.Modules.pushforward i).obj ((DerivedCategory.homologyFunctor Z.Modules q).obj L) :=
  Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardHomologyFunctorObjIso
    (hom i) q L

end Stacks.DeRham
