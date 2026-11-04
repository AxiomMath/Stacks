module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MixedTensorChangeOfRings
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPullback.MixedDerivedTensor.DerivedMixedTensor

/-!
# Stacks 08I6, `O`-linearly

Let `f : (Sh(C), O) ⟶ (Sh(C'), O')` be a morphism of ringed topoi.  Both sides of Stacks 08I6
are `O`-modules: on the right `F ⊗_{f⁻¹O'} f⁻¹G` carries the `O`-action of its first factor, the
tensor product being taken over the smaller sheaf of rings `f⁻¹O' ⟶ O`.  This file states the
tag with that action, both underived and in the derived category.

The mixed tensor product `F ⊗_{f⁻¹O'} N` of a sheaf of `O`-modules and a sheaf of
`f⁻¹O'`-modules is `Stacks.MixedTensor.sheafMixedTensorRight`, a sheaf of `O`-modules whose
sections are `F(U) ⊗_{f⁻¹O'(U)} N(U)`.  The underived identity

`F ⊗_O f^*G ≅ F ⊗_{f⁻¹O'} f⁻¹G`

then holds as sheaves of `O`-modules: `f^*G` is the extension of scalars of `f⁻¹G` along
`f⁻¹O' ⟶ O` (`pullbackIsoExtendInverseImage`) and the base change cancels `O`-linearly
(`Stacks.MixedTensor.sheafMixedBaseChangeIso`).  This is where the present statement departs
from `underivedTensorInverseImageLinearIso`, which is the same identity read in `f⁻¹O'`-modules.

In the derived category the identity is read off the factorization `X --h--> (C, f⁻¹O') --g--> Y`
of `f`: the derived mixed tensor product `F ⊗^L_{f⁻¹O'} N` is `F ⊗^L_O Lh^*N`, which is the
derived functor of the mixed tensor product because `- ⊗_O h^*N` and `- ⊗_{f⁻¹O'} N` are
isomorphic as underived functors, and `Lf^* ≅ Lg^* ⋙ Lh^*` is Stacks 0G6R.

## Main definitions

* `Stacks.Cohomology.MixedDerivedTensor.linearMixedTensorRight`: the endofunctor
  `F ↦ F ⊗_{f⁻¹O'} N` of sheaves of `O`-modules.
* `Stacks.Cohomology.MixedDerivedTensor.linearDerivedTensorPullback` and
  `linearDerivedMixedTensor`: the two bifunctors `D(O) × D(O') ⥤ D(O)` of the tag.

## Main results

* `Stacks.Cohomology.MixedDerivedTensor.underivedLinearTensorInverseImageIso`: **the underived
  identity of Stacks 08I6 as sheaves of `O`-modules.**
* `Stacks.Cohomology.MixedDerivedTensor.linearMixedTensorRight_iso_extendScalars`: tensoring
  over `f⁻¹O'` with `N` is tensoring over `O` with the extension of scalars `h^*N`.  This is
  what makes the second bifunctor below the derived mixed tensor product.
* `Stacks.Cohomology.MixedDerivedTensor.derivedLinearMixedTensorIso`: **Stacks 08I6,
  `O`-linearly.**

## Implementation notes

*What the derived statement rests on.*  `linearDerivedMixedTensor` is written with `Lh^*`, and
the content that makes it the derived mixed tensor product is
`linearMixedTensorRight_iso_extendScalars`: an isomorphism of the two *underived* endofunctors
of sheaves of `O`-modules, so their derived functors agree.  The statement of the tag is then
the whiskering of Stacks 0G6R into the second variable.  Nothing here is a restatement of the
`f⁻¹O'`-linear form: that form is an isomorphism in `D(f⁻¹O')`, and restriction of scalars on
derived categories is not faithful, so neither of the two statements follows from the other.

*The morphism-of-sites hypothesis and the derived-functor instances.*  These are exactly the
ones carried by `derivedPullbackFactorIso`, and for the same reasons; see the notes of
`DerivedMixedTensor`.

## References

* [The Stacks Project, Tag 08I6](https://stacks.math.columbia.edu/tag/08I6)
* [The Stacks Project, Tag 0G6R](https://stacks.math.columbia.edu/tag/0G6R)
* [The Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

namespace Stacks.Cohomology.MixedDerivedTensor

open StacksPullbackFactorization

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance]
  AlgebraicGeometry.SheafOfModules.isRightAdjoint_sheafPushforwardContinuous_commRingCat

/-! ### Transporting an isomorphism into the second variable of a product -/

/-- An isomorphism of functors induces one of their products with an identity functor. -/
def prodIdIso (E : Type*) [Category E] {C' D' : Type*} [Category C'] [Category D']
    {A B : C' ⥤ D'} (e : A ≅ B) : (𝟭 E).prod A ≅ (𝟭 E).prod B :=
  NatIso.ofComponents (fun P ↦ (Iso.refl P.1).prod (e.app P.2)) fun φ ↦
    Prod.ext ((Category.comp_id _).trans (Category.id_comp _).symm) (e.hom.naturality φ.2)

/-! ### The underived identity, `O`-linearly -/

section Underived

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedToposSiteHom X Y)

/-- **The mixed tensor product over `f⁻¹O'`, as an endofunctor of sheaves of `O`-modules**:
`F ↦ F ⊗_{f⁻¹O'} N`, with the `O`-action coming from `F`. -/
noncomputable def linearMixedTensorRight
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (auxTopos f).O)) :
    SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O) ⥤
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.O) :=
  Stacks.MixedTensor.sheafMixedTensorRight ((auxHomH f).fSharp) N

/-- **Tensoring over `f⁻¹O'` is tensoring over `O` with the extension of scalars.**  This is the
cancellation of a base change, `O`-linearly, and it is what identifies the derived functor of
the mixed tensor product below. -/
noncomputable def linearMixedTensorRight_iso_extendScalars
    (N : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (auxTopos f).O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.obj
      ((auxHomH f).pullbackTopos.obj N)) ≅
      linearMixedTensorRight f N :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.mapIso
      ((extendScalarsIsoPullbackAuxHomH f).app N)).symm ≪≫
    Stacks.MixedTensor.sheafMixedBaseChangeIso ((auxHomH f).fSharp) N

/-- **The underived identity of Stacks 08I6, as sheaves of `O`-modules.**  For a sheaf `G` of
`O'`-modules, the functor carrying a sheaf `F` of `O`-modules to `F ⊗_O f^*G` and the functor
carrying it to `F ⊗_{f⁻¹O'} f⁻¹G` are isomorphic, naturally in `F`, as functors into sheaves of
`O`-modules. -/
noncomputable def underivedLinearTensorInverseImageIso
    (G : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) :
    ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.obj
      (f.pullbackTopos.obj G)) ≅
      linearMixedTensorRight f ((auxHomG f).pullbackTopos.obj G) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.O).flip.mapIso
      (pullbackIsoExtendInverseImage f G)).symm ≪≫
    Stacks.MixedTensor.sheafMixedBaseChangeIso ((auxHomH f).fSharp)
      ((auxHomG f).pullbackTopos.obj G)

end Underived

/-! ### Stacks 08I6, `O`-linearly -/

section Derived

variable {X Y : RingedTopos.{u, u, u}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
  [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasSheafify Y.J AddCommGrpCat.{u}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [(Stacks.SheafOfModules.Tensor.sheafTensor X.O).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj M).Additive]
  [∀ (A B : CochainComplex (SheafOfModules.{u}
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ),
    HomologicalComplex.HasMapBifunctor A B (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]
  (f : RingedToposSiteHom X Y)

/-- **The left-hand bifunctor of Stacks 08I6, `O`-linearly**: `(F, G) ↦ F ⊗^L_O Lf^*G`, read in
`D(O)`. -/
abbrev linearDerivedTensorPullback
    [(pullbackOnHomotopy f).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O))
        (ComplexShape.up ℤ))] :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
        DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (𝟭 _).prod (derivedPullback f) ⋙
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)

/-- **The right-hand bifunctor of Stacks 08I6, `O`-linearly**:
`(F, G) ↦ F ⊗^L_{f⁻¹O'} f⁻¹G`, read in `D(O)`.  The mixed derived tensor product is written as
`F ⊗^L_O Lh^*(f⁻¹G)`, which is the derived functor of the mixed tensor product by
`linearMixedTensorRight_iso_extendScalars`. -/
abbrev linearDerivedMixedTensor
    [(pullbackOnHomotopy (auxHomH f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} (auxTopos f).O))
        (ComplexShape.up ℤ))]
    [(pullbackOnHomotopy (auxHomG f)).HasLeftDerivedFunctor
      (HomotopyCategory.quasiIso
        (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O))
        (ComplexShape.up ℤ))] :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ×
        DerivedCategory
          (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :=
  (𝟭 _).prod (derivedPullback (auxHomG f) ⋙ derivedPullback (auxHomH f)) ⋙
    Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O)

/-- **Stacks 08I6, `O`-linearly.**  The canonical bifunctorial isomorphism

`F ⊗^L_O Lf^*G ≅ F ⊗^L_{f⁻¹O'} f⁻¹G`

in `D(O)`, for `F` in `D(O)` and `G` in `D(O')`.  Both sides are objects of `D(O)`: the mixed
tensor product on the right inherits the `O`-action from `F`, and
`linearMixedTensorRight_iso_extendScalars` is the identification of the underived mixed tensor
product with the `Lh^*` form in which the right-hand side is written. -/
def derivedLinearMixedTensorIso (hmos : f.u.IsMorphismOfSites Y.J X.J) :
    haveI := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
      (auxHomH f) (isMorphismOfSites_auxHomH f)
    haveI := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
      (auxHomG f) hmos
    haveI := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
      f hmos
    linearDerivedTensorPullback f ≅ linearDerivedMixedTensor f :=
  haveI := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (auxHomH f) (isMorphismOfSites_auxHomH f)
  haveI := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (auxHomG f) hmos
  haveI := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    f hmos
  Functor.isoWhiskerRight (prodIdIso _ (derivedPullbackFactorIso f hmos).symm)
    (Functor.uncurry.obj (Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor X.O))

end Derived

end Stacks.Cohomology.MixedDerivedTensor

end
