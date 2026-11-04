module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.DerivedStalkCharacterization
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedStalk.DerivedStalkPushforwardLocalRing
public import StacksFrontier.CategoryTheory.Adjunction.MateOfUnitSquare
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunctionUnit

/-!
# The derived stalk of `Ri_*` on the image is the mate of the derived stalk formula

Let `i : Z ⟶ X` be a closed immersion of schemes and `z : Z`. There are two derived
comparisons at the germ map `i^♯_z : 𝒪_{X, i z} ⟶ 𝒪_{Z, z}`:

* `AlgebraicGeometry.derivedPullbackStalkIso` for `i` at `z`, which computes the derived stalk of
  the derived pullback as derived extension of scalars of the derived stalk, a square over the
  two left adjoints `Li^*` and `𝒪_{Z,z} ⊗ᴸ -`;
* `AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing`, which computes the
  derived stalk at `i z` of `Ri_*` as the derived stalk at `z` with scalars restricted, a square
  over the two right adjoints `Ri_*` and `restrictScalars (i^♯_z)`.

This file states that the second is the mate of the first, in the two forms
`CategoryTheory.mateEquiv` relates — the unit square and the counit square — and reduces it to
the unit square at `DerivedCategory.Q` of a K-flat complex.

## Main definitions

* `AlgebraicGeometry.derivedStalkGermAdjunction`: derived extension of scalars along the germ
  map, at the model `derivedPullbackStalkIso` produces, left adjoint to derived restriction of
  scalars.
* `AlgebraicGeometry.DerivedStalkPushforwardUnitSquareAt`: the unit square of the two
  comparisons, at one object of `D(𝒪_X)`.

## Main results

* `AlgebraicGeometry.derivedStalkPushforwardUnitSquareAt_iff`: the unit square is equivalent to
  the equality of the adjoint transposes of its two sides across `derivedStalkGermAdjunction`.
* `AlgebraicGeometry.derivedStalkPushforwardUnitSquare_of_kFlat`: the unit square at
  `DerivedCategory.Q` of every K-flat complex implies it at every object.
* `AlgebraicGeometry.derivedStalkDerivedPushforwardIso_eq_mateEquiv`: assuming the unit square,
  `derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` is the mate of `derivedPullbackStalkIso`
  read backwards.
* `AlgebraicGeometry.extendScalars_map_derivedStalkPushforward_comp_counit`: assuming the unit
  square, the counit square of the mate correspondence.

## Implementation notes

The structure field of `CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars`
states the comparison at `CochainComplex.DerivedExtensionScalars.extensionOfScalarsComplexGeneral`,
which is the same functor as `(ModuleCat.extendScalars _).mapHomologicalComplex _ ⋙
DerivedCategory.Q` but not the same term; `AlgebraicGeometry.germAlpha` restates it at the latter
spelling.

## References

* [Stacks Project, Tag 0098](https://stacks.math.columbia.edu/tag/0098)
* [Stacks Project, Tag 06YS](https://stacks.math.columbia.edu/tag/06YS)
* [Stacks Project, Tag 0E23](https://stacks.math.columbia.edu/tag/0E23)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces

noncomputable section

universe u

namespace AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

section

variable {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i] (z : Z)

/-- The comparison of the model of total derived extension of scalars along the germ map with
termwise extension of scalars. -/
abbrev germAlpha :
    DerivedCategory.Q ⋙ (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap z).hom).functor ⟶
      (ModuleCat.extendScalars.{u, u, u} (i.stalkMap z).hom).mapHomologicalComplex
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Q :=
  (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap z).hom).comparison

/-- The model of total derived extension of scalars along the germ map is left derived with
respect to `germAlpha`. -/
local instance isLeftDerived_germAlpha :
    (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap z).hom).functor.IsLeftDerivedFunctor
      (germAlpha i z)
      (HomologicalComplex.quasiIso (ModuleCat.{u} (ToType (X.presheaf.stalk (i z))))
        (ComplexShape.up ℤ)) :=
  (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap z).hom).isLeftDerived

/-- Derived extension of scalars along the germ map of `i` at `z`, at the model
`AlgebraicGeometry.derivedPullbackStalkIso` produces, is left adjoint to derived restriction of
scalars. -/
def derivedStalkGermAdjunction :
    (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap z).hom).functor ⊣
      (ModuleCat.restrictScalars.{u, u, u} (i.stalkMap z).hom).mapDerivedCategory :=
  derivedExtensionScalarsAdjunction.{u, u, u} (i.stalkMap z).hom
    (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap z).hom).functor (germAlpha i z)

/-- The unit square of the two derived comparisons at the germ map, at one object: the unit
of `derivedStalkGermAdjunction` at the derived stalk at `i z` of `K`, followed by derived
restriction of scalars of `AlgebraicGeometry.derivedPullbackStalkIso` read backwards, is the
derived stalk at `i z` of the unit of `Li^* ⊣ Ri_*`, followed by
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` at the derived pullback
of `K`. -/
abbrev DerivedStalkPushforwardUnitSquareAt (K : DerivedCategory X.Modules) : Prop :=
  (derivedStalkGermAdjunction i z).unit.app
        ((AlgebraicGeometry.derivedStalkFunctor (i.toLRSHom.toShHom.hom.base z)).obj K) ≫
      (ModuleCat.restrictScalars.{u, u, u}
          (i.toLRSHom.toShHom.hom.stalkMap z).hom).mapDerivedCategory.map
        ((AlgebraicGeometry.derivedPullbackStalkIso i z).inv.app K) =
    (AlgebraicGeometry.derivedStalkFunctor (i.toLRSHom.toShHom.hom.base z)).map
        ((derivedAdjunction i.toLRSHom.toShHom).unit.app K) ≫
      (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app
        ((derivedPullback i.toLRSHom.toShHom).obj K)

/-- The square of `AlgebraicGeometry.derivedPullbackStalkIso` read backwards. -/
private abbrev derivedPullbackStalkSquare :=
  TwoSquare.mk _ _ _ _ (AlgebraicGeometry.derivedPullbackStalkIso i z).inv

/-- The square of `AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing`. -/
private abbrev derivedStalkPushforwardSquare :=
  TwoSquare.mk _ _ _ _
    (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom

/-- The unit square at `K` holds if and only if `AlgebraicGeometry.derivedPullbackStalkIso` read
backwards at `K` is derived extension of scalars of the right-hand side of the square followed by
the counit of `derivedStalkGermAdjunction`. -/
theorem derivedStalkPushforwardUnitSquareAt_iff (K : DerivedCategory X.Modules) :
    DerivedStalkPushforwardUnitSquareAt i z K ↔
      (AlgebraicGeometry.derivedPullbackStalkIso i z).inv.app K =
        (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap z).hom).functor.map
            ((AlgebraicGeometry.derivedStalkFunctor (i.toLRSHom.toShHom.hom.base z)).map
                ((derivedAdjunction i.toLRSHom.toShHom).unit.app K) ≫
              (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app
                ((derivedPullback i.toLRSHom.toShHom).obj K)) ≫
          (derivedStalkGermAdjunction i z).counit.app
            ((AlgebraicGeometry.derivedStalkFunctor z).obj
              ((derivedPullback i.toLRSHom.toShHom).obj K)) :=
  CategoryTheory.unit_square_iff_transpose (derivedAdjunction i.toLRSHom.toShHom)
    (derivedStalkGermAdjunction i z)
    (derivedPullbackStalkSquare i z) (derivedStalkPushforwardSquare i z) K

/-- If the unit square holds at `DerivedCategory.Q` of every K-flat complex, it holds at every
object of `D(𝒪_X)`. -/
theorem derivedStalkPushforwardUnitSquare_of_kFlat
    (h : ∀ P : CochainComplex X.Modules ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toSheafedSpace P →
        DerivedStalkPushforwardUnitSquareAt i z (DerivedCategory.Q.obj P))
    (K : DerivedCategory X.Modules) : DerivedStalkPushforwardUnitSquareAt i z K :=
  CategoryTheory.unit_square_of_representatives (derivedAdjunction i.toLRSHom.toShHom)
    (derivedStalkGermAdjunction i z)
    (derivedPullbackStalkSquare i z) (derivedStalkPushforwardSquare i z)
    (fun L => ∃ P : CochainComplex X.Modules ℤ,
      Stacks.Cohomology.KFlatDerivedPullback.KFlatComplex X.toSheafedSpace P ∧
        L = DerivedCategory.Q.obj P)
    (fun L => by
      obtain ⟨P, s, hP, -, hs, -⟩ :=
        Stacks.Cohomology.KFlatDerivedPullback.exists_kFlatResolution X.toSheafedSpace
          (DerivedCategory.Q.objPreimage L)
      have : IsIso (DerivedCategory.Q.map s) := by
        rw [DerivedCategory.isIso_Q_map_iff_quasiIso]; exact hs
      exact ⟨DerivedCategory.Q.obj P, ⟨P, hP, rfl⟩,
        ⟨asIso (DerivedCategory.Q.map s) ≪≫ DerivedCategory.Q.objObjPreimageIso L⟩⟩)
    (fun L hL => by obtain ⟨P, hP, rfl⟩ := hL; exact h P hP) K

/-- If the unit square holds at every object,
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing` is the mate of
`AlgebraicGeometry.derivedPullbackStalkIso` read backwards, under `Li^* ⊣ Ri_*` and
`derivedStalkGermAdjunction`. -/
theorem derivedStalkDerivedPushforwardIso_eq_mateEquiv
    (h : ∀ K : DerivedCategory X.Modules, DerivedStalkPushforwardUnitSquareAt i z K) :
    mateEquiv (derivedAdjunction i.toLRSHom.toShHom) (derivedStalkGermAdjunction i z)
        (TwoSquare.mk _ _ _ _ (AlgebraicGeometry.derivedPullbackStalkIso i z).inv) =
      TwoSquare.mk _ _ _ _
        (AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom :=
  CategoryTheory.mateEquiv_eq_of_unit (derivedAdjunction i.toLRSHom.toShHom)
    (derivedStalkGermAdjunction i z) _ _ h

/-- If the unit square holds at every object, then derived extension of scalars along the germ
map of the component at `K` of
`AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing`, followed by the counit of
`derivedStalkGermAdjunction`, is `AlgebraicGeometry.derivedPullbackStalkIso` read backwards at
`Ri_* K`, followed by the derived stalk at `z` of the counit of `Li^* ⊣ Ri_*`. -/
theorem extendScalars_map_derivedStalkPushforward_comp_counit
    (h : ∀ K : DerivedCategory X.Modules, DerivedStalkPushforwardUnitSquareAt i z K)
    (K : DerivedCategory Z.Modules) :
    (totalDerivedExtensionScalars.{u, u, u} (i.stalkMap z).hom).functor.map
          ((AlgebraicGeometry.derivedStalkDerivedPushforwardIsoOfSchemesLocalRing i z).hom.app
            K) ≫
        (derivedStalkGermAdjunction i z).counit.app
          ((AlgebraicGeometry.derivedStalkFunctor z).obj K) =
      (AlgebraicGeometry.derivedPullbackStalkIso i z).inv.app
          ((derivedPushforward i.toLRSHom.toShHom).obj K) ≫
        (AlgebraicGeometry.derivedStalkFunctor z).map
          ((derivedAdjunction i.toLRSHom.toShHom).counit.app K) :=
  CategoryTheory.map_counit_comp_of_unit (derivedAdjunction i.toLRSHom.toShHom)
    (derivedStalkGermAdjunction i z)
    (derivedPullbackStalkSquare i z) (derivedStalkPushforwardSquare i z) h K

end

end AlgebraicGeometry

end

end
