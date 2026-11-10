module

public import StacksFrontier.CategoryTheory.Adjunction.TensorHomDiagonal
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.BraidingNatIso
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.MiddleSwap
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryTargetNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.InterfaceDerivedTensorComparison

/-!
# [Stacks, Tag 08J8] tensoring on the other side, and the diagonal of [Stacks, Tag 0BYS] it gives

Let `(C, O)` be a ringed site. [Stacks, Tag 08J8] fixes the *second* tensor slot, so the
adjunction `AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction` is

`- ⊗^𝐋_O B ⊣ RSheafHom(B, -)`,

whereas the derived tensor–Hom diagonal of [Stacks, Tag 0BYS] and the tensor–Hom adjunction at
`Ri_* 𝒪_Z` of
`Stacks.Duality.TensorHomTorAmplitude.tensorSheafHomAdjunctionAtPushforwardStructureSheaf` tensor
on the *first*. This file moves the slot and reads off the consequences.

Three things are needed and all three are now available. The commutativity constraint of
[Stacks, Tag 0FPT] is an isomorphism of bifunctors,
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso`; a ringed site's two
independently chosen derived tensor products are isomorphic,
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso`; and flipping a bifunctor is
functorial, `CategoryTheory.flipFunctor`. Composing the three gives an isomorphism of bifunctors
`- ⊗^𝐋_O - ≅ (- ⊗^𝐋_O -)ᶠˡⁱᵖ` for the tensor product [Stacks, Tag 08J8] is stated over, and
`CategoryTheory.Adjunction.ofNatIsoLeft` at its value at `B` moves the slot.

With the slot moved, `CategoryTheory.Adjunction.tensorHomDiagonal` applies, and the
interchange it asks for is
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.middleSwapIso`. The result is a morphism

`K ⊗^𝐋_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^𝐋_O L)`

of the type of the diagonal of [Stacks, Tag 0BYS], **at an arbitrary ringed site and an
arbitrary `M`**, built from [Stacks, Tag 08J8] and from nothing else, with the adjunction
equation that pins it down.

## Main definitions

* `AlgebraicGeometry.RingedSite.derivedTensorFlipNatIso`: the derived tensor product of
  [Stacks, Tag 06YU] is isomorphic to its flip, for the inhabitant [Stacks, Tag 08J8] is stated
  over.
* `AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunctionFlip`: [Stacks, Tag 08J8]
  tensoring on the first slot, `B ⊗^𝐋_O - ⊣ RSheafHom(B, -)`.
* `AlgebraicGeometry.RingedSite.interfaceDerivedTensorSheafHomAdjunction`: the same adjunction
  read over `Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, the tensor product
  the symmetric monoidal structure and the projection formula of this development use.
* `AlgebraicGeometry.RingedSite.curryTensorHomDiagonal`: the diagonal of [Stacks, Tag 0BYS]
  obtained by adjointness from that adjunction.

## Main results

* `AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction_counit_app`: **the counit of
  [Stacks, Tag 08J8] is the derived evaluation morphism** `RSheafHom(B, Z) ⊗^𝐋_O B ⟶ Z`, the
  transpose of the identity under the tensor–internal-Hom bijection.
* `AlgebraicGeometry.RingedSite.curryTensorHomDiagonal_mate` and
  `AlgebraicGeometry.RingedSite.eq_curryTensorHomDiagonal`: the adjunction equation
  characterizing the diagonal, and that it determines it.
* `AlgebraicGeometry.RingedSite.curryTensorHomDiagonal_natural_right`: functoriality in `L`.

## What this is for, and what it is not

`AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal` is the class of the complex-level
morphism of [Stacks, Tag 0BYR] between a chosen K-flat and a chosen K-injective representative,
conjugated by two model comparisons. It is **not** identified with `curryTensorHomDiagonal`
here, and no tag is placed below: [Stacks, Tag 0BYS] sits on the complex-model morphism, and a
second registration on a morphism not compared with it would assert the identification that is
missing.

The comparison the route through `Ri_*` of [Stacks, Tag 0E2N] needs is an equation between the
complex-model diagonal and a morphism built by adjointness under the *composite* of
[Stacks, Tag 079W] and [Stacks, Tag 0A76], whose counit is assembled from the units and counits of
those two. It factors through `curryTensorHomDiagonal` into two equations, each stated between
morphisms already in the library:

* that `derivedTensorHomDiagonal` is `curryTensorHomDiagonal`, which lives entirely inside the
  derived-internal-Hom development: by `eq_curryTensorHomDiagonal` it is the adjunction equation
  for the complex-model morphism, and by
  `derivedTensorSheafHomAdjunction_counit_app` the counit occurring in it is the transpose of the
  identity under `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`, with no pushforward and no
  projection formula in sight;
* that the two adjunctions `B ⊗^𝐋_O - ⊣ RSheafHom(B, -)` at `B = Ri_* 𝒪_Z` — this one and the
  composite one — agree. By `CategoryTheory.Adjunction.tensorHomDiagonal_eq_of_counit_eq` the
  diagonal depends on an adjunction only through its **counit**, so what has to be compared is
  the evaluation morphism of [Stacks, Tag 08J8] with the evaluation morphism assembled from
  [Stacks, Tag 079W] and [Stacks, Tag 0A76]; the units need not be compared separately, and a
  note of
`StacksFrontier/AlgebraicGeometry/Duality/RightAdjointLemmas/ExactSupportSiteTensorHomDiagonal.lean`
  that put the comparison at the units is corrected there.

## Implementation notes

The hom-set equivalence of [Stacks, Tag 08J8] is an explicit `Equiv` whose inverse function is
`derivedCurryHomEquiv` itself, so the counit — the value of that inverse at an identity — is
reached by rewriting with `CategoryTheory.Adjunction.mkOfHomEquiv_counit_app` and then
`Equiv.symm_mk` and `Equiv.coe_fn_mk`. Closing the same goal by `rfl` exhausts the recursion
depth at these arguments, and raising that limit by a compiler option is a workaround this
development does not accept; this is the discipline recorded in
`StacksFrontier/CategoryTheory/Sites/Cohomology/InternalHom/DerivedCurryTargetNaturality.lean`.

Everything else below is a term or a single `exact`, with the rewriting done one level up over an
abstract bifunctor in `StacksFrontier/CategoryTheory/Adjunction/TensorHomDiagonal.lean`.

## References

* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 0BYR](https://stacks.math.columbia.edu/tag/0BYR)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0E2N](https://stacks.math.columbia.edu/tag/0E2N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open Stacks.DerivedTensor.RingedSite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] _root_.SheafOfModules.monoidalCategorySheafTensor
  _root_.SheafOfModules.symmetricCategorySheafTensor
  _root_.SheafOfModules.monoidalPreadditiveSheafTensor
  _root_.SheafOfModules.monoidalClosedSheafTensor
  _root_.SheafOfModules.preservesColimit_tensorRight_sheafTensor

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj A).Additive]
  [∀ (K₁ K₂ : HomologicalComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u,
    u} X.O))
      (ComplexShape.up ℤ)),
    HomologicalComplex.HasMapBifunctor K₁ K₂ (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-! ### The counit of [Stacks, Tag 08J8] -/

/-- **The counit of [Stacks, Tag 08J8] is the derived evaluation morphism**

`RSheafHom(B, Z) ⊗^𝐋_O B ⟶ Z`,

the transpose of the identity of `RSheafHom(B, Z)` under the tensor–internal-Hom bijection
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv`. The adjunction is built from that bijection
by `CategoryTheory.Adjunction.mkOfHomEquiv`, whose counit is the value of the inverse of the
hom-set equivalence at an identity, and that inverse is `derivedCurryHomEquiv` itself. -/
theorem derivedTensorSheafHomAdjunction_counit_app
    (B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedTensorSheafHomAdjunction X B).counit.app Z =
      derivedCurryHomEquiv X (((derivedSheafHomBifunctor X).obj (op B)).obj Z) B Z (𝟙 _) := by
  rw [derivedTensorSheafHomAdjunction, Adjunction.mkOfHomEquiv_counit_app, Equiv.symm_mk,
    Equiv.coe_fn_mk]

/-! ### Moving the tensor slot -/

/-- **The derived tensor product of [Stacks, Tag 06YU] is isomorphic to its flip**, for the
inhabitant of it that [Stacks, Tag 08J8] is stated over. This is the commutativity constraint of
[Stacks, Tag 0FPT] read as an isomorphism of bifunctors,
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingNatIso`, conjugated by the
comparison `Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso` of the two
independently chosen derived tensor products of the site, flipped on one side by
`CategoryTheory.flipFunctor`. -/
def derivedTensorFlipNatIso :
    Stacks.SheafOfModules.derivedTensorProductFunctor X ≅
      (Stacks.SheafOfModules.derivedTensorProductFunctor X).flip :=
  Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso X ≪≫
    DerivedTensorProduct.braidingNatIso X (canonicalDerivedTensorProduct X.O) ≪≫
      (flipFunctor _ _ _).mapIso
        (Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso X).symm

/-- **[Stacks, Tag 08J8] tensoring on the first slot**: `B ⊗^𝐋_O - ⊣ RSheafHom(B, -)`. This is
`AlgebraicGeometry.RingedSite.derivedTensorSheafHomAdjunction`, whose left adjoint is
`- ⊗^𝐋_O B`, transported along `derivedTensorFlipNatIso` at `B`. -/
def derivedTensorSheafHomAdjunctionFlip
    (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (Stacks.SheafOfModules.derivedTensorProductFunctor X).obj B ⊣
      (derivedSheafHomBifunctor X).obj (op B) :=
  Adjunction.ofNatIsoLeft (derivedTensorSheafHomAdjunction X B)
    ((derivedTensorFlipNatIso X).app B).symm

/-- **[Stacks, Tag 08J8] tensoring on the first slot, over the other derived tensor product of
the site**: `B ⊗^𝐋_O - ⊣ RSheafHom(B, -)` with the tensor product
`Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor`, which is the one the symmetric
monoidal structure, the relative Künneth morphism and the projection formula of this development
are stated over. This is `derivedTensorSheafHomAdjunctionFlip` carried along
`Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso`. -/
def interfaceDerivedTensorSheafHomAdjunction
    (B : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedTensorProductFunctor X.O).obj B ⊣ (derivedSheafHomBifunctor X).obj (op B) :=
  Adjunction.ofNatIsoLeft (derivedTensorSheafHomAdjunctionFlip X B)
    ((Stacks.SheafOfModules.DerivedMonoidal.interfaceTensorCanonicalIso X).app B)

/-! ### The diagonal of [Stacks, Tag 0BYS] that the adjunction gives -/

/-- **The diagonal of [Stacks, Tag 0BYS] built from [Stacks, Tag 08J8].** For objects `M`, `K`,
`L` of `D(O)`, the morphism

`K ⊗^𝐋_O RSheafHom(M, L) ⟶ RSheafHom(M, K ⊗^𝐋_O L)`

obtained by adjointness under `interfaceDerivedTensorSheafHomAdjunction` from the interchange
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.middleSwapIso` followed by `K ⊗^𝐋_O -` of
the counit of that adjunction, the counit being the derived evaluation morphism of
`derivedTensorSheafHomAdjunction_counit_app`.

It is `CategoryTheory.Adjunction.tensorHomDiagonal` at that adjunction and that interchange, so
it is not an arbitrary morphism between the two objects. It is **not** identified with
`AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal`, the class of the complex-level morphism
of [Stacks, Tag 0BYR]; the module documentation says what such an identification would take. -/
def curryTensorHomDiagonal
    (M K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedTensorProductFunctor X.O).obj K).obj
        (((derivedSheafHomBifunctor X).obj (op M)).obj L) ⟶
      ((derivedSheafHomBifunctor X).obj (op M)).obj
        (((derivedTensorProductFunctor X.O).obj K).obj L) :=
  Adjunction.tensorHomDiagonal (interfaceDerivedTensorSheafHomAdjunction X M)
    (DerivedTensorProduct.middleSwapIso X (canonicalDerivedTensorProduct X.O) M K
      (((derivedSheafHomBifunctor X).obj (op M)).obj L)).hom

/-- **The adjunction equation characterizing the diagonal built from [Stacks, Tag 08J8].**
Tensoring it with `M` and composing with the counit — the derived evaluation morphism — gives
the interchange followed by `K ⊗^𝐋_O -` of that counit. -/
theorem curryTensorHomDiagonal_mate
    (M K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    ((derivedTensorProductFunctor X.O).obj M).map (curryTensorHomDiagonal X M K L) ≫
        (interfaceDerivedTensorSheafHomAdjunction X M).counit.app
          (((derivedTensorProductFunctor X.O).obj K).obj L) =
      (DerivedTensorProduct.middleSwapIso X (canonicalDerivedTensorProduct X.O) M K
            (((derivedSheafHomBifunctor X).obj (op M)).obj L)).hom ≫
        ((derivedTensorProductFunctor X.O).obj K).map
          ((interfaceDerivedTensorSheafHomAdjunction X M).counit.app L) :=
  Adjunction.tensorHomDiagonal_mate (interfaceDerivedTensorSheafHomAdjunction X M) _

/-- **The adjunction equation determines the diagonal built from [Stacks, Tag 08J8].** No other
morphism of its type satisfies `curryTensorHomDiagonal_mate`.

This is the form in which the identification of the complex-model diagonal of
[Stacks, Tag 0BYS] with an adjunct is to be discharged: it is enough to check the displayed
equation for `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal`. -/
theorem eq_curryTensorHomDiagonal
    (M K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {φ : ((derivedTensorProductFunctor X.O).obj K).obj
        (((derivedSheafHomBifunctor X).obj (op M)).obj L) ⟶
      ((derivedSheafHomBifunctor X).obj (op M)).obj
        (((derivedTensorProductFunctor X.O).obj K).obj L)}
    (hφ : ((derivedTensorProductFunctor X.O).obj M).map φ ≫
          (interfaceDerivedTensorSheafHomAdjunction X M).counit.app
            (((derivedTensorProductFunctor X.O).obj K).obj L) =
        (DerivedTensorProduct.middleSwapIso X (canonicalDerivedTensorProduct X.O) M K
              (((derivedSheafHomBifunctor X).obj (op M)).obj L)).hom ≫
          ((derivedTensorProductFunctor X.O).obj K).map
            ((interfaceDerivedTensorSheafHomAdjunction X M).counit.app L)) :
    φ = curryTensorHomDiagonal X M K L :=
  Adjunction.eq_tensorHomDiagonal (interfaceDerivedTensorSheafHomAdjunction X M) _ hφ

/-- **The diagonal built from [Stacks, Tag 08J8] is functorial in the target of the internal
Hom.** It comes from the naturality of the interchange,
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.middleSwapIso_hom_naturality_right`, and
the naturality of the hom-bijection of the adjunction. -/
theorem curryTensorHomDiagonal_natural_right
    (M K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : L ⟶ L') :
    ((derivedTensorProductFunctor X.O).obj K).map
          (((derivedSheafHomBifunctor X).obj (op M)).map g) ≫
        curryTensorHomDiagonal X M K L' =
      curryTensorHomDiagonal X M K L ≫
        ((derivedSheafHomBifunctor X).obj (op M)).map
          (((derivedTensorProductFunctor X.O).obj K).map g) :=
  Adjunction.tensorHomDiagonal_natural_right
    (interfaceDerivedTensorSheafHomAdjunction X M) g _ _
    (DerivedTensorProduct.middleSwapIso_hom_naturality_right X
      (canonicalDerivedTensorProduct X.O) M K
      (((derivedSheafHomBifunctor X).obj (op M)).map g))

end AlgebraicGeometry.RingedSite

end
