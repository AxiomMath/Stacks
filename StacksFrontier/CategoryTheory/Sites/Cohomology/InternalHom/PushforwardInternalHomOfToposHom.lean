module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.RelativeCupProductOfToposHom
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.ProjectionFormulaInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom and derived direct image, for a morphism of ringed topoi

Let `f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` be a morphism of ringed topoi — a morphism of the
underlying topoi together with the structure map, `AlgebraicGeometry.RingedToposHom`, with no
functor between the underlying sites — and let `L`, `M` be objects of `D(O_C)`.  There is a
canonical map

`Rf_*RHom_{O_C}(L, M) ⟶ RHom_{O_D}(Rf_*L, Rf_*M)`

of [Stacks, Tag 0B6D]: under the tensor–internal-Hom bijection of [Stacks, Tag 08J8] on `D(O_D)`
it corresponds to the composition

`Rf_*RHom_{O_C}(L, M) ⊗^L_{O_D} Rf_*L ⟶ Rf_*(RHom_{O_C}(L, M) ⊗^L_{O_C} L) ⟶ Rf_*M`

of the relative cup product of [Stacks, Tag 0B6C] and `Rf_*` of the evaluation morphism
`RHom_{O_C}(L, M) ⊗^L_{O_C} L ⟶ M`.

## Main definitions

All in the namespace `Stacks.Cohomology.PushforwardInternalHomOfToposHom`.

* `pushforwardInternalHomMap` — the construction at an abstract tensor–internal-Hom bijection on
  each of `D(O_C)` and `D(O_D)`.
* `derivedPushforwardSheafHomMap` — **the canonical map of [Stacks, Tag 0B6D]**, the
  construction at the development's own derived internal Hom
  `AlgebraicGeometry.RingedSite.derivedSheafHomBifunctor` and its bijection of
  [Stacks, Tag 08J8].

## Main results

* `derivedPushforwardSheafHomMap_homEquiv` — the defining property of the canonical map: its
  adjunct under the bijection of [Stacks, Tag 08J8] on `D(O_D)` is the relative cup product
  followed by `Rf_*` of evaluation.
* `pushforwardInternalHomMap_naturality_source`, `pushforwardInternalHomMap_naturality_target`
  — contravariance in `L` and covariance in `M`, at an abstract tensor–internal-Hom adjunction.

## Implementation notes

The relative cup product used is
`Stacks.Cohomology.RelativeCupProductOfToposHom.relativeCupProduct`, the one for an arbitrary
morphism of ringed topoi, built from the derived adjunction `Lf^* ⊣ Rf_*` of
[Stacks, Tag 07A6] and the comparison of [Stacks, Tag 07A4] for a morphism of topoi; so nothing
here asks `f` to come from a morphism of sites.  The tensor–internal-Hom bijection and the
evaluation morphism are those of
`Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi.derivedTensorHomBijection`; the
evaluation `RHom(L, M) ⊗^L L ⟶ M` is the image of the identity of `RHom(L, M)` under the
bijection of [Stacks, Tag 08J8], that is the counit
`AlgebraicGeometry.RingedSite.derivedSheafHomCounit` (`derivedTensorHomBijection_evaluation` in
the namespace `Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi`).

## References

* [Stacks Project, Tag 0B6D](https://stacks.math.columbia.edu/tag/0B6D)
* [Stacks Project, Tag 0B6C](https://stacks.math.columbia.edu/tag/0B6C)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0A98](https://stacks.math.columbia.edu/tag/0A98)
* [Stacks Project, Tag 01D3](https://stacks.math.columbia.edu/tag/01D3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.DerivedPushforward
open Stacks.Cohomology.RelativeCupProductOfToposHom
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi
open Stacks.DerivedTensor.RingedSite

namespace Stacks.Cohomology.PushforwardInternalHomOfToposHom

universe u

attribute [local instance 10000] HasDerivedCategory.standard

attribute [local instance]
  Stacks.Cohomology.DerivedPullbackOfToposHom.hasLeftDerivedFunctor_pullbackOnHomotopy

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

/-! ### The construction at an abstract tensor–internal-Hom bijection -/

section Abstract

variable
  (HX : (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))ᵒᵖ ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
  (HY : (DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))ᵒᵖ ⥤
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)))

section Bijection

variable (DX : TensorHomBijection (derivedTensorProductFunctor X.O) HX)
  (DY : TensorHomBijection (derivedTensorProductFunctor Y.O) HY)

/-- The canonical map of [Stacks, Tag 0B6D] for a morphism of ringed topoi, at an abstract
tensor–internal-Hom bijection on each of `D(O_C)` and `D(O_D)`: the morphism
`Rf_*H(L, M) ⟶ H(Rf_*L, Rf_*M)` which the bijection on `D(O_D)` sends to the relative cup
product of [Stacks, Tag 0B6C] followed by `Rf_*` of the evaluation morphism. -/
def pushforwardInternalHomMap
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPushforward f).obj ((HX.obj (op L)).obj M) ⟶
      (HY.obj (op ((derivedPushforward f).obj L))).obj ((derivedPushforward f).obj M) :=
  (DY.homEquiv ((derivedPushforward f).obj ((HX.obj (op L)).obj M))
      ((derivedPushforward f).obj L) ((derivedPushforward f).obj M)).symm
    (relativeCupProduct f ((HX.obj (op L)).obj M) L ≫
      (derivedPushforward f).map (DX.evaluation L M))

/-- **The defining property of the canonical map**, at an abstract bijection: its adjunct under
the tensor–internal-Hom bijection on `D(O_D)` is the relative cup product followed by `Rf_*` of
the evaluation morphism. -/
theorem pushforwardInternalHomMap_homEquiv
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    DY.homEquiv ((derivedPushforward f).obj ((HX.obj (op L)).obj M))
        ((derivedPushforward f).obj L) ((derivedPushforward f).obj M)
        (pushforwardInternalHomMap f HX HY DX DY L M) =
      relativeCupProduct f ((HX.obj (op L)).obj M) L ≫
        (derivedPushforward f).map (DX.evaluation L M) := by
  dsimp only [pushforwardInternalHomMap]
  exact (DY.homEquiv _ _ _).apply_symm_apply _

end Bijection

section Adjunction

variable (DX : TensorHomAdjunction (derivedTensorProductFunctor X.O) HX)
  (DY : TensorHomAdjunction (derivedTensorProductFunctor Y.O) HY)

/-- **The canonical map at an abstract adjunction is covariant in the target `M`.** -/
theorem pushforwardInternalHomMap_naturality_target
    (L : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    {M M' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (m : M ⟶ M') :
    (derivedPushforward f).map ((HX.obj (op L)).map m) ≫
        pushforwardInternalHomMap f HX HY DX.toTensorHomBijection DY.toTensorHomBijection L M' =
      pushforwardInternalHomMap f HX HY DX.toTensorHomBijection DY.toTensorHomBijection L M ≫
        (HY.obj (op ((derivedPushforward f).obj L))).map ((derivedPushforward f).map m) := by
  apply (DY.homEquiv ((derivedPushforward f).obj ((HX.obj (op L)).obj M))
    ((derivedPushforward f).obj L) ((derivedPushforward f).obj M')).injective
  have hev := DX.evaluation_naturality_target L m
  have hcup := relativeCupProduct_naturality_left f ((HX.obj (op L)).map m) L
  dsimp only [pushforwardInternalHomMap]
  rw [DY.homEquiv_naturality_source, DY.homEquiv_naturality_target,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, reassoc_of% hcup, ← Functor.map_comp, hev,
    Functor.map_comp, Category.assoc]

/-- **The canonical map at an abstract adjunction is contravariant in the source `L`.** -/
theorem pushforwardInternalHomMap_naturality_source
    {L L' : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (g : L' ⟶ L)
    (M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPushforward f).map ((HX.map g.op).app M) ≫
        pushforwardInternalHomMap f HX HY DX.toTensorHomBijection DY.toTensorHomBijection L' M =
      pushforwardInternalHomMap f HX HY DX.toTensorHomBijection DY.toTensorHomBijection L M ≫
        (HY.map ((derivedPushforward f).map g).op).app ((derivedPushforward f).obj M) := by
  apply (DY.homEquiv ((derivedPushforward f).obj ((HX.obj (op L)).obj M))
    ((derivedPushforward f).obj L') ((derivedPushforward f).obj M)).injective
  have hev := DX.evaluation_naturality_source g M
  have hcupL := relativeCupProduct_naturality_left f ((HX.map g.op).app M) L'
  have hcupR := relativeCupProduct_naturality_right f ((HX.obj (op L)).obj M) g
  dsimp only [pushforwardInternalHomMap]
  rw [DY.homEquiv_naturality_source, DY.homEquiv_naturality_middle,
    Equiv.apply_symm_apply, Equiv.apply_symm_apply, reassoc_of% hcupL, ← Functor.map_comp, hev,
    Functor.map_comp, ← reassoc_of% hcupR]

end Adjunction

end Abstract

/-! ### The canonical map of Tag 0B6D -/

/-- **[Stacks, Tag 0B6D].**  For a morphism of ringed topoi
`f : (Sh(C), O_C) ⟶ (Sh(D), O_D)` and objects `L`, `M` of `D(O_C)`, the canonical map

`Rf_*RHom_{O_C}(L, M) ⟶ RHom_{O_D}(Rf_*L, Rf_*M)`.

It is the morphism which the tensor–internal-Hom bijection of [Stacks, Tag 08J8] on `D(O_D)`
sends to the relative cup product
`Rf_*RHom(L, M) ⊗^L_{O_D} Rf_*L ⟶ Rf_*(RHom(L, M) ⊗^L_{O_C} L)` of [Stacks, Tag 0B6C] followed
by `Rf_*` of the evaluation morphism `RHom_{O_C}(L, M) ⊗^L_{O_C} L ⟶ M`. -/
@[stacks 0B6D "the canonical map, for an arbitrary morphism of ringed topoi (no \
  morphism-of-sites hypothesis); its defining property is \
  `derivedPushforwardSheafHomMap_homEquiv`"]
def derivedPushforwardSheafHomMap
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedPushforward f).obj
        (((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X)).obj (op L)).obj M) ⟶
      ((RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y)).obj
        (op ((derivedPushforward f).obj L))).obj ((derivedPushforward f).obj M) :=
  pushforwardInternalHomMap f
    (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X))
    (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y))
    (derivedTensorHomBijection (RingedTopos.toRingedSite X))
    (derivedTensorHomBijection (RingedTopos.toRingedSite Y)) L M

/-- The canonical map of [Stacks, Tag 0B6D] is the construction `pushforwardInternalHomMap` at
the development's own derived internal Hom and its bijection of [Stacks, Tag 08J8]. -/
theorem derivedPushforwardSheafHomMap_eq
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedPushforwardSheafHomMap f L M =
      pushforwardInternalHomMap f
        (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite X))
        (RingedSite.derivedSheafHomBifunctor (RingedTopos.toRingedSite Y))
        (derivedTensorHomBijection (RingedTopos.toRingedSite X))
        (derivedTensorHomBijection (RingedTopos.toRingedSite Y)) L M :=
  rfl

/-- **The defining property of the canonical map of [Stacks, Tag 0B6D]**: its adjunct under the
tensor–internal-Hom bijection of [Stacks, Tag 08J8] on `D(O_D)` is the relative cup product of
[Stacks, Tag 0B6C] followed by `Rf_*` of the evaluation morphism
`RHom_{O_C}(L, M) ⊗^L_{O_C} L ⟶ M`. -/
@[stacks 0B6D "the defining property: the 08J8 adjunct of the canonical map is the relative \
  cup product of 0B6C followed by Rf_* of evaluation, for an arbitrary morphism of ringed topoi"]
theorem derivedPushforwardSheafHomMap_homEquiv
    (L M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    (derivedTensorHomBijection (RingedTopos.toRingedSite Y)).homEquiv
        ((derivedPushforward f).obj
          (((RingedSite.derivedSheafHomBifunctor
            (RingedTopos.toRingedSite X)).obj (op L)).obj M))
        ((derivedPushforward f).obj L) ((derivedPushforward f).obj M)
        (derivedPushforwardSheafHomMap f L M) =
      relativeCupProduct f
          (((RingedSite.derivedSheafHomBifunctor
            (RingedTopos.toRingedSite X)).obj (op L)).obj M) L ≫
        (derivedPushforward f).map
          ((derivedTensorHomBijection (RingedTopos.toRingedSite X)).evaluation L M) := by
  rw [derivedPushforwardSheafHomMap_eq, pushforwardInternalHomMap_homEquiv]

end Stacks.Cohomology.PushforwardInternalHomOfToposHom

end
