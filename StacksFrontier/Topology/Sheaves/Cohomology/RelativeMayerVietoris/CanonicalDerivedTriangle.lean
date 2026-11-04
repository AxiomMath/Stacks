module

public import StacksFrontier.Topology.Sheaves.Cohomology.RelativeMayerVietoris.UnboundedDerivedPushforward
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.PullbackPushforwardAdjunction

/-!
# The canonical relative Mayer--Vietoris triangle

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `iU : U ⟶ X`, `iV : V ⟶ X` be open
immersions whose images cover `X`, with `iW : W ⟶ X` cutting out their intersection.  Stacks
08HZ puts the four derived direct images attached to the cover into a distinguished triangle

`Rf_*E ⟶ Ra_*(E|_U) ⊞ Rb_*(E|_V) ⟶ Rc_*(E|_{U ∩ V}) ⟶ (Rf_*E)⟦1⟧`.

Every additive functor between the module categories of two ringed spaces has a canonical right
derived functor on the unbounded derived category. Built from these and the canonical relative
Mayer--Vietoris sequence of Stacks 01EC, the triangle depends only on `f` and the cover.

## Main definitions

* `Stacks.Cohomology.RelativeMayerVietoris.canonicalRightDerived`: the right derived functor
  `D(𝒪_X) ⥤ D(𝒪_Y)` of an additive functor on modules, with canonical comparison
  `canonicalRightDerivedUnit`.
* `Stacks.Cohomology.RelativeMayerVietoris.canonicalPushforwardTriangle`: the relative
  Mayer--Vietoris triangle of a cover by two open immersions, depending on no choices.

## Main results

* `Stacks.Cohomology.RelativeMayerVietoris.canonicalRightDerived_isRightDerivedFunctor`: the
  canonical right derived functor, with `canonicalRightDerivedUnit`, is a right derived functor.
* `Stacks.Cohomology.RelativeMayerVietoris.canonicalPushforwardTriangle_distinguished`: the
  canonical triangle is distinguished.
* `Stacks.Cohomology.RelativeMayerVietoris.canonicalPushforwardTriangleMap`: functoriality of the
  canonical triangle in the derived object.
* `Stacks.Cohomology.RelativeMayerVietoris.isIso_hom₁_of_canonicalTriangleHom`: for a morphism
  from the image of a canonical triangle under an exact functor to another canonical triangle,
  the first component is invertible when the second and third components are.

## References

* [Stacks Project, Tag 08HZ](https://stacks.math.columbia.edu/tag/08HZ)
* [Stacks Project, Tag 01EC](https://stacks.math.columbia.edu/tag/01EC)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 014A](https://stacks.math.columbia.edu/tag/014A)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open CategoryTheory.Pretriangulated
open RingedSpaceModuleAdjunction

universe u

namespace Stacks.Cohomology.RelativeMayerVietoris

attribute [local instance] HasDerivedCategory.standard

section Canonical

variable {X Y : RingedSpace.{u, u}}
  (F : SheafOfModules.{u} (structureSheafRing X) ⥤ SheafOfModules.{u} (structureSheafRing Y))
  [F.Additive]

/-- Every additive functor on modules has a right derived functor on the unbounded derived
category. -/
public instance homotopyToDerived_hasRightDerivedFunctor :
    (homotopyToDerived F).HasRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :=
  have : (homotopyToDerived F).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :=
    (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      u, u + 1, u, u + 1, u + 1, u + 1} (homotopyToDerived F)
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.exists_quasiIso_isKInjective X)).1
  Functor.hasRightDerivedFunctor_of_hasPointwiseRightDerivedFunctor _ _

/-- The canonical right derived functor `RF : D(𝒪_X) ⥤ D(𝒪_Y)` of an additive functor `F` on
modules: the total right derived functor of `F` applied degreewise. -/
public def canonicalRightDerived :
    DerivedCategory (SheafOfModules.{u} (structureSheafRing X)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) :=
  (homotopyToDerived F).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- The canonical comparison from the degreewise image of a complex to the canonical right
derived functor. -/
public def canonicalRightDerivedUnit :
    homotopyToDerived F ⟶ DerivedCategory.Qh ⋙ canonicalRightDerived F :=
  (homotopyToDerived F).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ))

/-- The canonical right derived functor, with its canonical comparison, is a right derived
functor. -/
public instance canonicalRightDerived_isRightDerivedFunctor :
    (canonicalRightDerived F).IsRightDerivedFunctor (canonicalRightDerivedUnit F)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) :=
  inferInstanceAs
    (((homotopyToDerived F).totalRightDerived DerivedCategory.Qh
        _).IsRightDerivedFunctor
      ((homotopyToDerived F).totalRightDerivedUnit DerivedCategory.Qh _) _)

end Canonical

section Triangle

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

variable {X Y U V W : RingedSpace.{u, u}} (f : X ⟶ Y)
  (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X)
  [SheafedSpace.IsOpenImmersion iU] [SheafedSpace.IsOpenImmersion iV]
  [SheafedSpace.IsOpenImmersion iW]
  (cover : Set.range iU.hom.base ∪ Set.range iV.hom.base = Set.univ)
  (intersection : Set.range iW.hom.base = Set.range iU.hom.base ∩ Set.range iV.hom.base)

/-- The relative Mayer--Vietoris triangle of a cover by two open immersions at an object `E` of
`D(𝒪_X)`: the triangle `Rf_*E ⟶ Ra_*(E|_U) ⊞ Rb_*(E|_V) ⟶ Rc_*(E|_{U ∩ V}) ⟶ (Rf_*E)⟦1⟧`
built from the canonical right derived functors and the canonical relative Mayer--Vietoris
sequence. -/
public def canonicalPushforwardTriangle
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    Triangle (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :=
  pushforwardTriangle f iU iV iW
    (relativeMayerVietorisSequence f iU iV iW cover intersection)
    (canonicalRightDerived (modulePushforward f))
    (canonicalRightDerived (restrictedPushforwardAlong f iU))
    (canonicalRightDerived (restrictedPushforwardAlong f iV))
    (canonicalRightDerived (restrictedPushforwardAlong f iW))
    (canonicalRightDerivedUnit (modulePushforward f))
    (canonicalRightDerivedUnit (restrictedPushforwardAlong f iU))
    (canonicalRightDerivedUnit (restrictedPushforwardAlong f iV))
    (canonicalRightDerivedUnit (restrictedPushforwardAlong f iW)) E

/-- The relative Mayer--Vietoris triangle built from the canonical derived functors and the
canonical relative Mayer--Vietoris sequence is distinguished at every object of the unbounded
derived category. -/
@[stacks 08HZ "the triangle with no choices: the canonical derived functors of \
`canonicalRightDerived` and the canonical sequence of Tag 01EC, which is the form in which two \
such triangles can be compared"]
public theorem canonicalPushforwardTriangle_distinguished
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    canonicalPushforwardTriangle f iU iV iW cover intersection E ∈
      distTriang (DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :=
  pushforwardTriangle_distinguished f iU iV iW _ _ _ _ _ _ _ _ _ E

/-- The first vertex of the canonical relative Mayer--Vietoris triangle is `Rf_*E`. -/
public theorem canonicalPushforwardTriangle_obj₁
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (canonicalPushforwardTriangle f iU iV iW cover intersection E).obj₁ =
      (canonicalRightDerived (modulePushforward f)).obj E :=
  pushforwardTriangle_obj₁ f iU iV iW _ _ _ _ _ _ _ _ _ E

/-- The second vertex of the canonical relative Mayer--Vietoris triangle is the biproduct of the
two restricted direct images. -/
public theorem canonicalPushforwardTriangle_obj₂
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (canonicalPushforwardTriangle f iU iV iW cover intersection E).obj₂ =
      ((canonicalRightDerived (restrictedPushforwardAlong f iU)).obj E ⊞
        (canonicalRightDerived (restrictedPushforwardAlong f iV)).obj E) :=
  pushforwardTriangle_obj₂ f iU iV iW _ _ _ _ _ _ _ _ _ E

/-- The third vertex of the canonical relative Mayer--Vietoris triangle is the direct image
restricted to the intersection of the two members of the cover. -/
public theorem canonicalPushforwardTriangle_obj₃
    (E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) :
    (canonicalPushforwardTriangle f iU iV iW cover intersection E).obj₃ =
      (canonicalRightDerived (restrictedPushforwardAlong f iW)).obj E :=
  pushforwardTriangle_obj₃ f iU iV iW _ _ _ _ _ _ _ _ _ E

/-- The canonical triangle is functorial in the derived object: a morphism `e : E ⟶ E'` induces a
morphism of canonical triangles whose components are the four canonical derived functors applied
to `e`. -/
public def canonicalPushforwardTriangleMap
    {E E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (e : E ⟶ E') :
    canonicalPushforwardTriangle f iU iV iW cover intersection E ⟶
      canonicalPushforwardTriangle f iU iV iW cover intersection E' :=
  pushforwardTriangleMap f iU iV iW _ _ _ _ _ _ _ _ _ e

end Triangle

section FiveLemma

attribute [local instance 2000] CategoryTheory.Abelian.hasBinaryBiproducts

variable {X Y U V W X' Y' U' V' W' : RingedSpace.{u, u}} (f : X ⟶ Y) (f' : X' ⟶ Y')
  (iU : U ⟶ X) (iV : V ⟶ X) (iW : W ⟶ X)
  [SheafedSpace.IsOpenImmersion iU] [SheafedSpace.IsOpenImmersion iV]
  [SheafedSpace.IsOpenImmersion iW]
  (cover : Set.range iU.hom.base ∪ Set.range iV.hom.base = Set.univ)
  (intersection : Set.range iW.hom.base = Set.range iU.hom.base ∩ Set.range iV.hom.base)
  (iU' : U' ⟶ X') (iV' : V' ⟶ X') (iW' : W' ⟶ X')
  [SheafedSpace.IsOpenImmersion iU'] [SheafedSpace.IsOpenImmersion iV']
  [SheafedSpace.IsOpenImmersion iW']
  (cover' : Set.range iU'.hom.base ∪ Set.range iV'.hom.base = Set.univ)
  (intersection' : Set.range iW'.hom.base = Set.range iU'.hom.base ∩ Set.range iV'.hom.base)

/-- Let `L : D(𝒪_Y) ⥤ D(𝒪_{Y'})` be an exact functor and let `φ` be a morphism from `L` of the
canonical triangle of a cover of `X` to the canonical triangle of a cover of `X'`. If the
comparisons at the two members of the cover and at the intersection are invertible, so is the
comparison of the two direct images. -/
public theorem isIso_hom₁_of_canonicalTriangleHom
    (L : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y)) ⥤
      DerivedCategory (SheafOfModules.{u} (structureSheafRing Y')))
    [L.CommShift ℤ] [L.IsTriangulated]
    {E : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))}
    {E' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X'))}
    (φ : L.mapTriangle.obj (canonicalPushforwardTriangle f iU iV iW cover intersection E) ⟶
      canonicalPushforwardTriangle f' iU' iV' iW' cover' intersection' E')
    (h₂ : IsIso φ.hom₂) (h₃ : IsIso φ.hom₃) : IsIso φ.hom₁ :=
  isIso₁_of_isIso₂₃ φ
    (L.map_distinguished _ (canonicalPushforwardTriangle_distinguished f iU iV iW cover
      intersection E))
    (canonicalPushforwardTriangle_distinguished f' iU' iV' iW' cover' intersection' E') h₂ h₃

end FiveLemma

end Stacks.Cohomology.RelativeMayerVietoris

end
