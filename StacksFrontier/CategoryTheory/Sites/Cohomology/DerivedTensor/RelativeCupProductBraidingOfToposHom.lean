module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.DerivedPullbackTensorBraidingOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductOfToposHom
import StacksCore.Tactic.StacksAttribute

/-!
# Commutativity of the relative cup product, for a morphism of ringed topoi

Let `f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi in the sense of
[Stacks, Tag 01D3], part (2): a morphism of the underlying topoi together with the structure map
(`AlgebraicGeometry.RingedToposHom`). **[Stacks, Tag 0FPM]** asserts that the relative cup
product of [Stacks, Tag 0B6C] is commutative. For all `K, L` in `D(𝒪)` the square

```
Rf_*K ⊗^L_{𝒪'} Rf_*L --cup--→ Rf_*(K ⊗^L_𝒪 L)
        | ψ                          | Rf_*ψ
        ↓                            ↓
Rf_*L ⊗^L_{𝒪'} Rf_*K --cup--→ Rf_*(L ⊗^L_𝒪 K)
```

commutes in `D(𝒪')`, where `ψ` is the commutativity constraint of [Stacks, Tag 0FPT].

## Main results

* `Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct_braiding`:
  **[Stacks, Tag 0FPM]**, for every morphism of ringed topoi and all `K, L` in `D(𝒪)`.

## Implementation notes

*Which morphisms of ringed topoi.* The registration in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedTensor/RelativeCupProductBraiding.lean`
covers a morphism presented by a continuous functor of the underlying sites that is a morphism
of sites (`AlgebraicGeometry.RingedToposSiteHom` with `hmos`). Not every morphism of topoi
`Sh(C) ⟶ Sh(C')` is induced by a functor `C' ⥤ C`; the source only gets one after replacing the
sites. So that statement is narrower than the source. The statement here is about the
two-field `AlgebraicGeometry.RingedToposHom` of Tag 01D3, part (2). Its geometric datum is a
morphism of the underlying topoi, and nothing is asked of the sites.

*No hypothesis, and no instance is a binder.* The theorem is stated with no class argument
of its own. Every instance its statement mentions comes from instance search, at
`RingedTopos.{u, u, u}`:

* the sheaf conditions for the forgetful functors and the sheafification on both sites;
* the additivity of `Stacks.SheafOfModules.Tensor.sheafTensor` (`sheafTensor_additive`,
  `sheafTensor_obj_additive` of `Stacks.SheafOfModules.Tensor`);
* the existence of total tensor complexes, `hasMapBifunctor_sheafTensor_ringedTopos`. This is
  `Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor` at a ringed topos, installed as a
  file-local instance because instance search does not find it unaided;
* the existence of `Lf^*`
  (`Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy`,
  installed locally exactly as in the file that defines the cup product).

So the statement holds for every morphism of ringed topoi at those universes. The universe
narrowing is the one the derived tensor product of [Stacks, Tag 06YU] carries, and it is
documented at `Stacks.DerivedTensor.RingedSite.exists_derivedTensorProduct`.

*The proof.* The square reduces, by the diagram chase
`Stacks.Cohomology.RelativeCupProductOnRingedTopoi.adjunctionCupProduct_braiding` (which assumes
nothing about ringed topoi), to two inputs:

* the naturality of `ψ`, which is `CategoryTheory.BraidedCategory.braiding_naturality` for
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalDerivedSymmetric`;
* the braidedness of the comparison of [Stacks, Tag 07A4], which is
  `Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_braiding`.

`ψ` on both edges is `Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom`, the braiding of
the symmetric monoidal structure of Tag 0FPT. Its tensor product is the derived tensor product of
Tag 06YU on the nose. The relative cup product is the one canonical definition,
`Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct`.

## References

* [Stacks Project, Tag 0FPM](https://stacks.math.columbia.edu/tag/0FPM)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.DerivedPullbackOfToposHom
open Stacks.Cohomology.RelativeCupProductOnRingedTopoi
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.DerivedMonoidal (canonicalBraidingHom canonicalDerivedMonoidal
  canonicalDerivedSymmetric)
open scoped CategoryTheory.Prod

namespace Stacks.Cohomology.RelativeCupProductOfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

section Instances

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget RingCat.{u})] [Y.J.HasSheafCompose (forget RingCat.{u})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify X.J (Type u)] [HasSheafify Y.J (Type u)]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).obj M).Additive]
  [(Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O) (ComplexShape.up ℤ)]
  [∀ (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} Y.O) (ComplexShape.up ℤ)]
  (f : RingedToposHom X Y)

/-- **[Stacks, Tag 0FPM], at the variable block of the cup product.** This is
`relativeCupProduct_braiding` with the eighteen `Prop`-valued class arguments that
`relativeCupProduct` is defined under kept as binders. `relativeCupProduct_braiding` drops them,
because instance search supplies every one of them. -/
theorem relativeCupProduct_braiding_of_instances
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    relativeCupProduct f K L ≫ (derivedPushforward f).map (canonicalBraidingHom X.O K L) =
      canonicalBraidingHom Y.O ((derivedPushforward f).obj K) ((derivedPushforward f).obj L) ≫
        relativeCupProduct f L K :=
  adjunctionCupProduct_braiding (derivedAdjunction f)
    (uncurriedDerivedTensor Y) (uncurriedDerivedTensor X)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso f).hom
    (canonicalBraidingHom Y.O) (canonicalBraidingHom X.O)
    (fun u v =>
      let := canonicalDerivedMonoidal X.O
      let := canonicalDerivedSymmetric X.O
      BraidedCategory.braiding_naturality u v)
    (Stacks.Sheaves.DerivedPullback.OfToposHom.derivedPullbackTensorIso_braiding f) K L

end Instances

/-- **Total tensor complexes exist on a ringed topos.** This is
`Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor` at the structure sheaf of `W`, with
its three class arguments found by instance search one at a time. They are the weak
sheafification of abelian groups, `WEqualsLocallyBijective`, and binary biproducts of sheaves of
modules. Instance search does not find the composite goal by itself: it tries a path through
`∀ j, WEqualsLocallyBijective` and runs out of budget. So the composite is installed as a
file-local instance here, the way neighbouring files pin `hasMapBifunctor_sheafTensor`. -/
theorem hasMapBifunctor_sheafTensor_ringedTopos (W : RingedTopos.{u, u, u})
    (A B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf W.O)) ℤ) :
    HomologicalComplex.HasMapBifunctor A B
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} W.O) (ComplexShape.up ℤ) :=
  Stacks.SheafOfModules.Tensor.hasMapBifunctor_sheafTensor W.O A B

attribute [local instance high] hasMapBifunctor_sheafTensor_ringedTopos

/-- **[Stacks, Tag 0FPM].** The relative cup product of [Stacks, Tag 0B6C] is commutative. Let
`f : (Sh(C), 𝒪) ⟶ (Sh(C'), 𝒪')` be a morphism of ringed topoi: a morphism of the underlying
topoi together with the structure map. Then for **all** `K, L` in `D(𝒪)` the square

```
Rf_*K ⊗^L_{𝒪'} Rf_*L --cup--→ Rf_*(K ⊗^L_𝒪 L)
        | ψ                          | Rf_*ψ
        ↓                            ↓
Rf_*L ⊗^L_{𝒪'} Rf_*K --cup--→ Rf_*(L ⊗^L_𝒪 K)
```

commutes in `D(𝒪')`. The horizontal arrows are the relative cup product. The left edge is `ψ` at
`(Rf_*K, Rf_*L)` and the right edge is `Rf_*` applied to `ψ` at `(K, L)`, as the source draws
them. `ψ` is the commutativity constraint of [Stacks, Tag 0FPT] on each of the two derived
categories.

The statement has no hypothesis and no class argument of its own. -/
@[stacks 0FPM "the whole tag, for an arbitrary morphism of ringed topoi in the two-field sense \
  of Tag 01D3, part (2) (a morphism of the underlying topoi with its structure map, no functor \
  between the underlying sites and no morphism-of-sites hypothesis), at RingedTopos.{u, u, u}, \
  for all K, L in D(𝒪); ψ on both edges is the commutativity constraint of Tag 0FPT and the \
  statement carries no hypothesis or class argument"]
theorem relativeCupProduct_braiding {X Y : RingedTopos.{u, u, u}} (f : RingedToposHom X Y)
    (K L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    relativeCupProduct f K L ≫ (derivedPushforward f).map (canonicalBraidingHom X.O K L) =
      canonicalBraidingHom Y.O ((derivedPushforward f).obj K) ((derivedPushforward f).obj L) ≫
        relativeCupProduct f L K :=
  @relativeCupProduct_braiding_of_instances X Y _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ f K L

end Stacks.Cohomology.RelativeCupProductOfToposHom

end
