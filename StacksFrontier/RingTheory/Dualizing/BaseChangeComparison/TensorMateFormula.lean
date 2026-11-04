module

public import StacksFrontier.RingTheory.Dualizing.BaseChangeComparison.TensorMate

/-!
# A closed formula for the lax monoidal structure map of derived base change

`Dualizing.derivedTensorBaseChange` is the lax monoidal structure map
`μ_{X,Y} : F X ⊗ᴸ_A F Y ⟶ F (X ⊗ᴸ_R Y)` of a model `F` of derived extension of scalars along
`f : R → A`, defined as `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate`, a double
adjoint transpose of coevaluation followed by the change-of-rings comparison
`Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChangeMate`.

For every morphism `ψ : X ⊗ᴸ_R Y ⟶ W` out of a derived tensor product,

`μ_{X,Y} ≫ F ψ` is the adjoint transpose of `F (ψ̃) ≫ RHom-base-change at (Y, W)`,

where `ψ̃ : X ⟶ RHom_R(Y, W)` is the transpose of `ψ` and the last factor is the derived-Hom
base-change morphism `Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange` of Stacks 0E1X.
Taking `ψ` to be the identity gives a closed formula for `μ` itself, with coevaluation in place
of `ψ̃`.

The equation is first proved for an arbitrary pair of derived tensor–Hom adjunctions, an
arbitrary adjunction `F ⊣ G` between their derived categories, and an arbitrary comparison of the
two internal-Hom bifunctors, and then specialized to derived base change.

## Main results

* `StacksDraft.DerivedHom.DerivedHomAdjunction.tensorHomUnit_comp_hom_map`: coevaluation followed
  by the internal Hom of a morphism out of the tensor product is the transpose of that morphism.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate_comp_map`: the lax tensor
  comparison followed by the functor applied to a morphism out of the tensor product is the
  transpose of the transposed morphism followed by the mate of the internal-Hom comparison.
* `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate_eq`: the closed formula for the
  lax tensor comparison itself.
* `Dualizing.derivedTensorBaseChange_comp_map`: the same equation for derived base change, with
  the mate transpose written as the morphism of Stacks 0E1X.
* `Dualizing.derivedTensorBaseChange_eq`: the closed formula for the lax monoidal structure map of
  derived base change in terms of coevaluation and the morphism of Stacks 0E1X.

## References

* [Stacks Project, Tag 0E1X](https://stacks.math.columbia.edu/tag/0E1X)
* [Stacks Project, Tag 0A63](https://stacks.math.columbia.edu/tag/0A63)
* [Stacks Project, Tag 0E2A](https://stacks.math.columbia.edu/tag/0E2A)
* [Stacks Project, Tag 0GMT](https://stacks.math.columbia.edu/tag/0GMT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor StacksDraft.DerivedHom
open scoped ChangeOfRings

universe uR uA uM v v' w w'

namespace StacksDraft.DerivedHom.DerivedHomAdjunction

section Mate

variable {R : Type uR} [CommRing R] [HasDerivedCategory.{w} (ModuleCat.{v} R)]
  {A : Type uA} [CommRing A] [HasDerivedCategory.{w'} (ModuleCat.{v'} A)]
  (d : DerivedHomAdjunction R) (d' : DerivedHomAdjunction A)
  {F : DerivedCategory (ModuleCat.{v} R) ⥤ DerivedCategory (ModuleCat.{v'} A)}
  {G : DerivedCategory (ModuleCat.{v'} A) ⥤ DerivedCategory (ModuleCat.{v} R)}
  (a : F ⊣ G)
  (m : d.hom ⟶ F.op.prod F ⋙ d'.hom ⋙ G)

/-- The coevaluation `X ⟶ RHom(Y, X ⊗ᴸ Y)` of Stacks 0A63, followed by the internal Hom out of
`Y` applied to a morphism `ψ : X ⊗ᴸ Y ⟶ W`, is the adjoint transpose of `ψ`. -/
theorem tensorHomUnit_comp_hom_map (X Y W : DerivedCategory (ModuleCat.{v} R))
    (ψ : d.tensor.obj (X, Y) ⟶ W) :
    d.tensorHomUnit X Y ≫ d.hom.map ((𝟙 (Opposite.op Y), ψ) :
        (Opposite.op Y, d.tensor.obj (X, Y)) ⟶ (Opposite.op Y, W)) =
      (d.homEquiv X Y W).symm ψ := by
  have hunit : d.homEquiv X Y (d.tensor.obj (X, Y)) (d.tensorHomUnit X Y) =
      𝟙 (d.tensor.obj (X, Y)) :=
    (d.homEquiv X Y (d.tensor.obj (X, Y))).apply_symm_apply (𝟙 _)
  apply (d.homEquiv X Y W).injective
  rw [d.homEquiv_naturality_right, AddEquiv.apply_symm_apply, hunit, Category.id_comp]

/-- For an adjunction `F ⊣ G` and a comparison `m` of the two internal-Hom bifunctors, the lax
tensor comparison `F X ⊗ᴸ F Y ⟶ F (X ⊗ᴸ Y)` of
`StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate`, followed by `F` applied to a
morphism `ψ : X ⊗ᴸ Y ⟶ W`, is the transpose over the target ring of `F` applied to the transpose
of `ψ` followed by the transpose along `a` of the component of `m` at `(Y, W)`. -/
theorem laxTensorOfHomMate_comp_map (X Y W : DerivedCategory (ModuleCat.{v} R))
    (ψ : d.tensor.obj (X, Y) ⟶ W) :
    laxTensorOfHomMate d d' a m X Y ≫ F.map ψ =
      d'.homEquiv (F.obj X) (F.obj Y) (F.obj W)
        (F.map ((d.homEquiv X Y W).symm ψ) ≫
          (a.homEquiv (d.hom.obj (Opposite.op Y, W))
            (d'.hom.obj (Opposite.op (F.obj Y), F.obj W))).symm
              (m.app (Opposite.op Y, W))) := by
  have hm := m.naturality ((𝟙 (Opposite.op Y), ψ) :
    (Opposite.op Y, d.tensor.obj (X, Y)) ⟶ (Opposite.op Y, W))
  dsimp only [Functor.comp_map, Functor.comp_obj, Functor.prod_map] at hm
  rw [CategoryTheory.Functor.map_id] at hm
  have hm' : d.hom.map ((𝟙 (Opposite.op Y), ψ) :
        (Opposite.op Y, d.tensor.obj (X, Y)) ⟶ (Opposite.op Y, W)) ≫
        m.app (Opposite.op Y, W) =
      m.app (Opposite.op Y, d.tensor.obj (X, Y)) ≫
        G.map (d'.hom.map ((𝟙 (Opposite.op (F.obj Y)), F.map ψ) :
          (Opposite.op (F.obj Y), F.obj (d.tensor.obj (X, Y))) ⟶
            (Opposite.op (F.obj Y), F.obj W))) := hm
  have hdef : laxTensorOfHomMate d d' a m X Y =
      d'.homEquiv (F.obj X) (F.obj Y) (F.obj (d.tensor.obj (X, Y)))
        ((a.homEquiv X (d'.hom.obj (Opposite.op (F.obj Y),
            F.obj (d.tensor.obj (X, Y))))).symm
          (d.tensorHomUnit X Y ≫ m.app (Opposite.op Y, d.tensor.obj (X, Y)))) := rfl
  rw [hdef, ← d'.homEquiv_naturality_right]
  refine congrArg (d'.homEquiv (F.obj X) (F.obj Y) (F.obj W)) ?_
  rw [← a.homEquiv_naturality_left_symm, ← tensorHomUnit_comp_hom_map d X Y W ψ,
    Category.assoc, hm', ← Category.assoc, ← a.homEquiv_naturality_right_symm]

/-- The lax tensor comparison `StacksDraft.DerivedHom.DerivedHomAdjunction.laxTensorOfHomMate` is
the transpose over the target ring of `F` applied to coevaluation, followed by the transpose along
`a` of the component of the internal-Hom comparison at `(Y, X ⊗ᴸ Y)`. -/
theorem laxTensorOfHomMate_eq (X Y : DerivedCategory (ModuleCat.{v} R)) :
    laxTensorOfHomMate d d' a m X Y =
      d'.homEquiv (F.obj X) (F.obj Y) (F.obj (d.tensor.obj (X, Y)))
        (F.map (d.tensorHomUnit X Y) ≫
          (a.homEquiv (d.hom.obj (Opposite.op Y, d.tensor.obj (X, Y)))
            (d'.hom.obj (Opposite.op (F.obj Y),
              F.obj (d.tensor.obj (X, Y))))).symm
              (m.app (Opposite.op Y, d.tensor.obj (X, Y)))) := by
  refine Eq.trans ?_ (laxTensorOfHomMate_comp_map d d' a m X Y
    (d.tensor.obj (X, Y)) (𝟙 _))
  rw [CategoryTheory.Functor.map_id, Category.comp_id]

end Mate

end StacksDraft.DerivedHom.DerivedHomAdjunction

namespace Dualizing

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] extendScalarsAdditiveOfRingHom

variable {R : Type uR} {A : Type uA} [CommRing R] [CommRing A] (f : R →+* A)
  (F : DerivedCategory (ModuleCat.{max uR uA uM} R) ⥤
    DerivedCategory (ModuleCat.{max uR uA uM} A))
  (comparison : DerivedCategory.Q ⋙ F ⟶
    (ModuleCat.extendScalars.{uR, uA, max uR uA uM} f).mapHomologicalComplex
      (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
  [F.IsLeftDerivedFunctor comparison
    (HomologicalComplex.quasiIso (ModuleCat.{max uR uA uM} R) (ComplexShape.up ℤ))]

/-- For every morphism `ψ : X ⊗ᴸ_R Y ⟶ W` of `D(R)`, the structure map
`Dualizing.derivedTensorBaseChange` followed by `F` applied to `ψ` is the adjoint transpose, under
the tensor–Hom adjunction of Stacks 0A63 over `A`, of `F` applied to the transpose of `ψ` followed
by the derived-Hom base-change morphism of Stacks 0E1X at `(Y, W)`. -/
theorem derivedTensorBaseChange_comp_map
    (X Y W : DerivedCategory (ModuleCat.{max uR uA uM} R))
    (ψ : (derivedHomAdjunctionOverRing.{uR, max uR uA uM, max uR uA uM + 1} R).tensor.obj
      (X, Y) ⟶ W) :
    derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y ≫ F.map ψ =
      (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
        (F.obj X) (F.obj Y) (F.obj W)
        (F.map (((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).homEquiv X Y W).symm ψ) ≫
          Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison Y W)
            :=
  DerivedHomAdjunction.laxTensorOfHomMate_comp_map _ _ _ _ X Y W ψ

/-- The lax monoidal structure map `Dualizing.derivedTensorBaseChange` of derived base change is
the adjoint transpose over `A` of `F` applied to the coevaluation `X ⟶ RHom_R(Y, X ⊗ᴸ_R Y)` of
Stacks 0A63, followed by the derived-Hom base-change morphism of Stacks 0E1X at
`(Y, X ⊗ᴸ_R Y)`. -/
theorem derivedTensorBaseChange_eq
    (X Y : DerivedCategory (ModuleCat.{max uR uA uM} R)) :
    derivedTensorBaseChange.{uR, uA, uM} f F comparison X Y =
      (derivedHomAdjunctionOverRing.{uA, max uR uA uM, max uR uA uM + 1} A).homEquiv
        (F.obj X) (F.obj Y)
        (F.obj ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
          max uR uA uM + 1} R).tensor.obj (X, Y)))
        (F.map ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).tensorHomUnit X Y) ≫
          Stacks.DerivedHom.ExtensionOfScalars.derivedHomBaseChange.{uR, uA, uM} f F comparison Y
            ((derivedHomAdjunctionOverRing.{uR, max uR uA uM,
              max uR uA uM + 1} R).tensor.obj (X, Y))) :=
  DerivedHomAdjunction.laxTensorOfHomMate_eq _ _ _ _ X Y

end Dualizing

end
