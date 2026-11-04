module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.CompletionProper.AdicPictureBridges
public import StacksFrontier.AlgebraicGeometry.TwistMultCompat.Generic

/-!
# The multiplication of a system, as a morphism out of the completion of a tensor square

`AlgebraicGeometry.existsUnique_hom_of_adicThickeningCompletion` descends a family of morphisms
on the adic thickenings to a morphism on `X` once that family commutes with the canonical
transitions `AlgebraicGeometry.adicThickeningCompletionTransition` of the two completions. For
the multiplication of a system of algebra sheaves, the source of the family is the completion of
a tensor square and the family is built out of the multiplications of the system. This file
constructs the components of that family and proves that they commute with the transitions,
over arbitrary schemes.

## Main definitions

* `AlgebraicGeometry.tensorDescentApp`: for `w : W ⟶ W''`, a module `N` on `W''`, a module `M`
  on `W` and maps `ε : w^*N ⟶ M`, `δ : M ⟶ w^*N` and `mul : M ⊗ M ⟶ M`, the composite
  `w^*(N ⊗ N) ⟶ w^*N ⊗ w^*N ⟶ M ⊗ M ⟶ M ⟶ w^*N`, the first factor being the comparison of
  [Stacks, Tag 01CD].

## Main results

* `Stacks.Tag01VSPullbackTensor.schemePullbackTensorIso_tensorSheafMap_hom`: naturality of the
  comparison of [Stacks, Tag 01CD] in its two module arguments.
* `AlgebraicGeometry.tensorDescentApp_comm`: for `i ≫ v = w`, the components at `v` and at `w`
  commute with the two transitions, as soon as `mul` is carried by the transition `φ` of the
  algebra system through the comparison of Tag 01CD, and `ε`, `δ` commute with `φ` and the
  transition of the completion.

## Implementation notes

The tensor product is `Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheaf`, the one at
which `AlgebraicGeometry.multiplication_comp_adicAlgebraModuleSystem_transitionIso` and
`AlgebraicGeometry.tensorSquareProperOver` are stated.

Every scheme is a variable. The transitions enter `tensorDescentApp_comm` as binders
`{t} (ht : … = t)` and are substituted before anything is proved, and the component is a `def`,
so a statement of the square mentions no
`Stacks.SheafOfModules.TensorStalkRingedSpace.tensorSheafMap`. Stating the square directly at
the fibre product `AlgebraicGeometry.adicBaseChange A I f n` does not elaborate within the
default heartbeat budget.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 088F](https://stacks.math.columbia.edu/tag/088F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry
open Stacks.AlgebraicGeometry.TwistMultTransport (tensorSheafMap_comp)

universe u

namespace Stacks.Tag01VSPullbackTensor

/-- The comparison of [Stacks, Tag 01CD] is natural in its two module arguments: pulling back a
tensor product of two morphisms and then splitting the target is splitting the source and then
tensoring the two pullbacks. -/
public theorem schemePullbackTensorIso_tensorSheafMap_hom {W W' : Scheme.{u}} (g : W ⟶ W')
    {P P' Q Q' : W'.Modules} (a : P ⟶ P') (b : Q ⟶ Q') :
    (Scheme.Modules.pullback g).map
          ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨W'.toRingedSpace.presheaf, W'.toRingedSpace.IsSheaf⟩)).map
              (X := (P, Q)) (Y := (P', Q'))
              ((a, b) : (_, _) ⟶ (_, _))) ≫
        (schemePullbackTensorIso g P' Q').hom =
      (schemePullbackTensorIso g P Q).hom ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback g).obj P, (Scheme.Modules.pullback g).obj Q))
            (Y := ((Scheme.Modules.pullback g).obj P', (Scheme.Modules.pullback g).obj Q'))
            ((((Scheme.Modules.pullback g).map a), ((Scheme.Modules.pullback g).map b)) :
              (_, _) ⟶ (_, _))) :=
  Stacks.AlgebraicGeometry.TwistMultCompat.comparison_tensorSheafMap_nat g a b

end Stacks.Tag01VSPullbackTensor

namespace AlgebraicGeometry

open Stacks.Tag01VSPullbackTensor (schemePullbackTensorIso schemePullbackTensorIso_pullbackCompCongr
  schemePullbackTensorIso_tensorSheafMap_hom)

/-! ### The component of the multiplication on a thickening -/

/-- The multiplication of a module on `W`, read as a morphism out of the inverse image of a
tensor square on `W''`. For `w : W ⟶ W''`, `N` on `W''`, `M` on `W` with
`ε : w^*N ⟶ M`, `δ : M ⟶ w^*N` and a multiplication `mul : M ⊗ M ⟶ M`, this is

  `w^*(N ⊗ N) ⟶ w^*N ⊗ w^*N ⟶ M ⊗ M ⟶ M ⟶ w^*N`,

the first factor being the comparison of [Stacks, Tag 01CD]. -/
public def tensorDescentApp {W W'' : Scheme.{u}} (w : W ⟶ W'') (N : W''.Modules) (M : W.Modules)
    (ε : (Scheme.Modules.pullback w).obj N ⟶ M) (δ : M ⟶ (Scheme.Modules.pullback w).obj N)
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj M).obj M) ⟶ M) :
    (Scheme.Modules.pullback w).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W''.toRingedSpace.presheaf, W''.toRingedSpace.IsSheaf⟩).obj N).obj N) ⟶
      (Scheme.Modules.pullback w).obj N :=
  (schemePullbackTensorIso w N N).hom ≫
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
        (X := ((Scheme.Modules.pullback w).obj N, (Scheme.Modules.pullback w).obj N))
        (Y := (M, M))
        ((ε, ε) : (_, _) ⟶ (_, _))) ≫ mul ≫ δ

/-- `AlgebraicGeometry.tensorDescentApp` is the composite
`w^*(N ⊗ N) ⟶ w^*N ⊗ w^*N ⟶ M ⊗ M ⟶ M ⟶ w^*N`. -/
public theorem tensorDescentApp_eq {W W'' : Scheme.{u}} (w : W ⟶ W'') (N : W''.Modules)
    (M : W.Modules) (ε : (Scheme.Modules.pullback w).obj N ⟶ M)
    (δ : M ⟶ (Scheme.Modules.pullback w).obj N)
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj M).obj M) ⟶ M) :
    tensorDescentApp w N M ε δ mul =
      (schemePullbackTensorIso w N N).hom ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback w).obj N, (Scheme.Modules.pullback w).obj N))
            (Y := (M, M))
            ((ε, ε) : (_, _) ⟶ (_, _))) ≫ mul ≫ δ :=
  rfl

/-! ### The commuting square, as pure category algebra -/

/-- A functor carries a four-fold composite to the composite of the four images. -/
private theorem map_comp_four {C D : Type*} [Category C] [Category D] (F : C ⥤ D)
    {O₀ O₁ O₂ O₃ O₄ : C} (a : O₀ ⟶ O₁) (b : O₁ ⟶ O₂) (c : O₂ ⟶ O₃) (d : O₃ ⟶ O₄) :
    F.map (a ≫ b ≫ c ≫ d) = F.map a ≫ F.map b ≫ F.map c ≫ F.map d := by
  simp only [Functor.map_comp]

/-- Pasting five commuting squares: the square of `AlgebraicGeometry.tensorDescentApp_comm` in
an abstract category. -/
private theorem descentChain {C : Type*} [Category C]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ Oa Ob : C}
    {pc : O₀ ⟶ O₁} {pt : O₁ ⟶ O₂} {pm : O₂ ⟶ O₃} {pd : O₃ ⟶ O₄} {tN : O₄ ⟶ O₅}
    {φ : O₃ ⟶ O₆} {δ : O₆ ⟶ O₅} {cB : O₂ ⟶ O₇} {mφ : O₇ ⟶ O₈} {mul : O₈ ⟶ O₆}
    {ci : O₁ ⟶ O₉} {tε : O₉ ⟶ O₇} {ttN : O₉ ⟶ Oa} {tfin : Oa ⟶ O₈}
    {tT : O₀ ⟶ Ob} {c : Ob ⟶ Oa}
    (h₁ : pd ≫ tN = φ ≫ δ) (h₂ : pm ≫ φ = cB ≫ mφ ≫ mul)
    (h₃ : pt ≫ cB = ci ≫ tε) (h₄ : tε ≫ mφ = ttN ≫ tfin)
    (h₅ : (pc ≫ ci) ≫ ttN = tT ≫ c) :
    (pc ≫ pt ≫ pm ≫ pd) ≫ tN = tT ≫ c ≫ tfin ≫ mul ≫ δ :=
  calc (pc ≫ pt ≫ pm ≫ pd) ≫ tN
      = pc ≫ pt ≫ pm ≫ pd ≫ tN := by simp only [Category.assoc]
    _ = pc ≫ pt ≫ (pm ≫ φ) ≫ δ := by rw [h₁, Category.assoc]
    _ = pc ≫ (pt ≫ cB) ≫ mφ ≫ mul ≫ δ := by rw [h₂]; simp only [Category.assoc]
    _ = (pc ≫ ci) ≫ (tε ≫ mφ) ≫ mul ≫ δ := by rw [h₃]; simp only [Category.assoc]
    _ = ((pc ≫ ci) ≫ ttN) ≫ tfin ≫ mul ≫ δ := by rw [h₄]; simp only [Category.assoc]
    _ = tT ≫ c ≫ tfin ≫ mul ≫ δ := by rw [h₅]; simp only [Category.assoc]

/-! ### The three inputs of the square -/

section Inputs

variable {W W' W'' : Scheme.{u}} (i : W ⟶ W') (v : W' ⟶ W'') (N : W''.Modules)
  {M' : W'.Modules} {M : W.Modules}

/-- The inverse image of `AlgebraicGeometry.tensorDescentApp`, with the four factors separated. -/
private theorem map_tensorDescentApp (ε' : (Scheme.Modules.pullback v).obj N ⟶ M')
    (δ' : M' ⟶ (Scheme.Modules.pullback v).obj N)
    (mul' : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W'.toRingedSpace.presheaf, W'.toRingedSpace.IsSheaf⟩).obj M').obj M') ⟶ M') :
    (Scheme.Modules.pullback i).map (tensorDescentApp v N M' ε' δ' mul') =
      (Scheme.Modules.pullback i).map (schemePullbackTensorIso v N N).hom ≫
        (Scheme.Modules.pullback i).map
            ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
              ⟨W'.toRingedSpace.presheaf, W'.toRingedSpace.IsSheaf⟩)).map
                (X := ((Scheme.Modules.pullback v).obj N, (Scheme.Modules.pullback v).obj N))
                (Y := (M', M'))
                ((ε', ε') : (_, _) ⟶ (_, _))) ≫
          (Scheme.Modules.pullback i).map mul' ≫ (Scheme.Modules.pullback i).map δ' := by
  rw [tensorDescentApp_eq]
  exact map_comp_four _ _ _ _ _

/-- The hypothesis `hmul` of `AlgebraicGeometry.tensorDescentApp_comm` with the comparison of
[Stacks, Tag 01CD] moved to the other side. -/
private theorem map_mul_comp_of_tensorSheafMap_comp {φ : (Scheme.Modules.pullback i).obj M' ⟶ M}
    {mul' : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W'.toRingedSpace.presheaf, W'.toRingedSpace.IsSheaf⟩).obj M').obj M') ⟶ M'}
    {mul : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj M).obj M) ⟶ M}
    (hmul : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback i).obj M', (Scheme.Modules.pullback i).obj M'))
            (Y := (M, M))
            ((φ, φ) : (_, _) ⟶ (_, _))) ≫ mul =
      (schemePullbackTensorIso i M' M').inv ≫ (Scheme.Modules.pullback i).map mul' ≫ φ) :
    (Scheme.Modules.pullback i).map mul' ≫ φ =
      (schemePullbackTensorIso i M' M').hom ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback i).obj M', (Scheme.Modules.pullback i).obj M'))
            (Y := (M, M))
            ((φ, φ) : (_, _) ⟶ (_, _))) ≫ mul :=
  ((congrArg (fun z => (schemePullbackTensorIso i M' M').hom ≫ z) hmul).trans
    ((schemePullbackTensorIso i M' M').hom_inv_id_assoc _)).symm

/-- The two tensor factors of the square compose, and by the hypothesis `hε` the composite is the
transition tensored with itself followed by `ε`. -/
private theorem tensorSheafMap_comp_of_comm {Z : W.Modules}
    {φ : (Scheme.Modules.pullback i).obj M' ⟶ M}
    (ε' : (Scheme.Modules.pullback v).obj N ⟶ M') {ε : Z ⟶ M}
    {t : (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback v).obj N) ⟶ Z}
    (hε : (Scheme.Modules.pullback i).map ε' ≫ φ = t ≫ ε) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
          (X := ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback v).obj N),
            (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback v).obj N)))
          (Y := ((Scheme.Modules.pullback i).obj M', (Scheme.Modules.pullback i).obj M'))
          ((((Scheme.Modules.pullback i).map ε'), ((Scheme.Modules.pullback i).map ε')) :
            (_, _) ⟶ (_, _))) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback i).obj M', (Scheme.Modules.pullback i).obj M'))
            (Y := (M, M))
            ((φ, φ) : (_, _) ⟶ (_, _))) =
      ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback v).obj N),
              (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback v).obj N)))
            (Y := (Z, Z))
            ((t, t) : (_, _) ⟶ (_, _))) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (X := (Z, Z))
            (Y := (M, M))
            ((ε, ε) : (_, _) ⟶ (_, _))) :=
  (tensorSheafMap_comp W.toRingedSpace _ _ _ _).symm.trans
    (hε ▸ tensorSheafMap_comp W.toRingedSpace t ε t ε)

end Inputs

/-! ### The compatibility of the component with the transitions -/

/-- The component of the multiplication commutes with the transitions. Let `i ≫ v = w`, let
`N` be a module on `W''`, let `M'` on `W'` and `M` on `W` carry multiplications `mul'` and `mul`,
and let

* `φ : i^*M' ⟶ M` carry `mul'` to `mul` through the comparison of [Stacks, Tag 01CD] (the
  hypothesis `hmul`);
* `ε' : v^*N ⟶ M'`, `ε : w^*N ⟶ M` commute with `φ` and the transition `tN` of the pullbacks
  of `N` (the hypothesis `hε`);
* `δ' : M' ⟶ v^*N`, `δ : M ⟶ w^*N` likewise (the hypothesis `hδ`).

Then the square formed by `AlgebraicGeometry.tensorDescentApp` at `v` and at `w` and the two
transitions commutes.

The two transitions `tN` and `tT` are the composites of the two pseudofunctoriality
isomorphisms; at the adic morphisms they are the canonical transitions, by
`AlgebraicGeometry.pullbackComp_pullbackCongr_app_eq_adicThickeningCompletionTransition`. -/
public theorem tensorDescentApp_comm {W W' W'' : Scheme.{u}} (i : W ⟶ W') (v : W' ⟶ W'')
    {w : W ⟶ W''} (hw : i ≫ v = w) (N : W''.Modules) {M' : W'.Modules} {M : W.Modules}
    (mul' : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W'.toRingedSpace.presheaf, W'.toRingedSpace.IsSheaf⟩).obj M').obj M') ⟶ M')
    (mul : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩).obj M).obj M) ⟶ M)
    (φ : (Scheme.Modules.pullback i).obj M' ⟶ M)
    (ε' : (Scheme.Modules.pullback v).obj N ⟶ M') (ε : (Scheme.Modules.pullback w).obj N ⟶ M)
    (δ' : M' ⟶ (Scheme.Modules.pullback v).obj N) (δ : M ⟶ (Scheme.Modules.pullback w).obj N)
    {tN : (Scheme.Modules.pullback i).obj ((Scheme.Modules.pullback v).obj N) ⟶
      (Scheme.Modules.pullback w).obj N}
    (htN : (Scheme.Modules.pullbackComp i v).hom.app N ≫
      (Scheme.Modules.pullbackCongr hw).hom.app N = tN)
    {tT : (Scheme.Modules.pullback i).obj
        ((Scheme.Modules.pullback v).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W''.toRingedSpace.presheaf, W''.toRingedSpace.IsSheaf⟩).obj N).obj N)) ⟶
      (Scheme.Modules.pullback w).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨W''.toRingedSpace.presheaf, W''.toRingedSpace.IsSheaf⟩).obj N).obj N)}
    (htT : (Scheme.Modules.pullbackComp i v).hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨W''.toRingedSpace.presheaf, W''.toRingedSpace.IsSheaf⟩).obj N).obj N) ≫
        (Scheme.Modules.pullbackCongr hw).hom.app
          (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨W''.toRingedSpace.presheaf, W''.toRingedSpace.IsSheaf⟩).obj N).obj N) = tT)
    (hmul : ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W.toRingedSpace.presheaf, W.toRingedSpace.IsSheaf⟩)).map
            (X := ((Scheme.Modules.pullback i).obj M', (Scheme.Modules.pullback i).obj M'))
            (Y := (M, M))
            ((φ, φ) : (_, _) ⟶ (_, _))) ≫ mul =
      (schemePullbackTensorIso i M' M').inv ≫
        (Scheme.Modules.pullback i).map mul' ≫ φ)
    (hε : (Scheme.Modules.pullback i).map ε' ≫ φ = tN ≫ ε)
    (hδ : (Scheme.Modules.pullback i).map δ' ≫ tN = φ ≫ δ) :
    (Scheme.Modules.pullback i).map (tensorDescentApp v N M' ε' δ' mul') ≫ tN =
      tT ≫ tensorDescentApp w N M ε δ mul := by
  subst htN htT
  refine Eq.trans (congrArg (fun z => z ≫ ((Scheme.Modules.pullbackComp i v).hom.app N ≫
    (Scheme.Modules.pullbackCongr hw).hom.app N)) (map_tensorDescentApp i v N ε' δ' mul')) ?_
  refine Eq.trans ?_ (congrArg
    (fun z => ((Scheme.Modules.pullbackComp i v).hom.app
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W''.toRingedSpace.presheaf, W''.toRingedSpace.IsSheaf⟩).obj N).obj N) ≫
      (Scheme.Modules.pullbackCongr hw).hom.app
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨W''.toRingedSpace.presheaf, W''.toRingedSpace.IsSheaf⟩).obj N).obj N)) ≫ z)
    (tensorDescentApp_eq w N M ε δ mul).symm)
  exact descentChain hδ (map_mul_comp_of_tensorSheafMap_comp i hmul)
    (schemePullbackTensorIso_tensorSheafMap_hom i ε' ε')
    (tensorSheafMap_comp_of_comm i v N ε' hε)
    (schemePullbackTensorIso_pullbackCompCongr i v hw N N)

end AlgebraicGeometry

end
