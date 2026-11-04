module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorAssocInverse

/-! # The relative tensor product with a bimodule is associative

Let `(A, d)`, `(B, d)` and `(C, d)` be differential graded algebras over a commutative ring `R`,
let `N` be a differential graded `(A, B)`-bimodule, let `N'` be a differential graded
`(B, C)`-bimodule and write `N'' = N ⊗_B N'` for the composite differential graded
`(A, C)`-bimodule of Tag 0BZ3. The two comparisons
`DifferentialGraded.Bimodule.assocForward` and `DifferentialGraded.Bimodule.assocInverse` between
`M ⊗_A N''` and `(M ⊗_A N) ⊗_B N'` are mutually inverse and natural in `M`, so tensoring with
`N''` is isomorphic to tensoring with `N` followed by tensoring with `N'`.

Both composites are the identity because they fix every pure tensor, and the pure tensors
*generate* the relative tensor product by
`DifferentialGraded.Bimodule.tensorObj_linearMap_ext`; the uniqueness half of the universal
property of Tag 09LM is not enough on its own, since the second variable of a pure tensor of
`M ⊗_A N''` has to be reduced to a pure tensor of `N ⊗_B N'` and that reduction is not a
statement about homomorphisms.

## Main definitions

* `DifferentialGraded.Bimodule.assocIso`: the isomorphism `M ⊗_A N'' ≅ (M ⊗_A N) ⊗_B N'` of
  right differential graded `C`-modules.
* `DifferentialGraded.Bimodule.tensorCompFunctorAssocIso`: **the associativity isomorphism**
  `- ⊗_A N'' ≅ (- ⊗_A N) ⊗_B N'` of functors
  `Mod^{dg}_{(A, d)} ⥤ Mod^{dg}_{(C, d)}`.

## Main results

* `DifferentialGraded.Bimodule.assocForward_assocInverse` and
  `DifferentialGraded.Bimodule.assocInverse_assocForward`: the two comparisons are mutually
  inverse.
* `DifferentialGraded.Bimodule.assocForward_naturality`: the comparison is natural in `M`.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) is the relative tensor
  product and its universal property;
  [Tag 0BZ3](https://stacks.math.columbia.edu/tag/0BZ3) is the composite bimodule.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}

/-! ### The two comparisons are mutually inverse -/

/-- Two morphisms out of `M ⊗_A (N ⊗_B N')` agreeing on every pure tensor `x ⊗ (y ⊗ y')` are
equal. -/
private theorem compTensor_hom_ext (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) {P : DifferentialGradedModule.{u, u, u} C}
    (f g : tensorObj (compTensor N N') M ⟶ P)
    (h : ∀ (x : M.M) (y : N.rightModule.M) (y' : N'.rightModule.M),
      f.toFun ((tensorPure (compTensor N N') M).toLinearMap x
          ((tensorPure N' N.rightModule).toLinearMap y y')) =
        g.toFun ((tensorPure (compTensor N N') M).toLinearMap x
          ((tensorPure N' N.rightModule).toLinearMap y y'))) :
    f = g := by
  refine tensorObj_hom_ext (compTensor N N') M _ _ fun x z => ?_
  exact LinearMap.congr_fun (tensorObj_linearMap_ext N' N.rightModule
    (f.toFun.comp (assocPure N N' M x)) (g.toFun.comp (assocPure N N' M x)) (h x)) z

/-- The comparison `M ⊗_A N'' ⟶ (M ⊗_A N) ⊗_B N'` followed by the comparison back is the
identity: both fix every pure tensor `x ⊗ (y ⊗ y')`, and those generate `M ⊗_A N''`. -/
theorem assocForward_assocInverse (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    assocForward N N' M ≫ assocInverse N N' M = 𝟙 (tensorObj (compTensor N N') M) := by
  refine compTensor_hom_ext N N' M _ _ fun x y y' => ?_
  show (assocInverse N N' M).toFun ((assocForward N N' M).toFun
      ((tensorPure (compTensor N N') M).toLinearMap x
        ((tensorPure N' N.rightModule).toLinearMap y y'))) =
    (tensorPure (compTensor N N') M).toLinearMap x
      ((tensorPure N' N.rightModule).toLinearMap y y')
  rw [assocForward_pure, assocInverse_pure]
  rfl

/-- The comparison `(M ⊗_A N) ⊗_B N' ⟶ M ⊗_A N''` followed by the comparison back is the
identity: both fix every pure tensor `(x ⊗ y) ⊗ y'`, and those generate `(M ⊗_A N) ⊗_B N'`. -/
theorem assocInverse_assocForward (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    assocInverse N N' M ≫ assocForward N N' M = 𝟙 (tensorObj N' (tensorObj N M)) := by
  refine tensorObj_hom_ext N' (tensorObj N M) _ _ fun w y' => ?_
  have key : ((assocInverse N N' M ≫ assocForward N N' M).toFun.comp
        ((tensorPure N' (tensorObj N M)).toLinearMap.flip y')) =
      (tensorPure N' (tensorObj N M)).toLinearMap.flip y' := by
    refine tensorObj_linearMap_ext N M _ _ fun x y => ?_
    show (assocForward N N' M).toFun ((assocInverse N N' M).toFun
        ((tensorPure N' (tensorObj N M)).toLinearMap
          ((tensorPure N M).toLinearMap x y) y')) =
      (tensorPure N' (tensorObj N M)).toLinearMap ((tensorPure N M).toLinearMap x y) y'
    rw [assocInverse_pure]
    exact assocForward_pure N N' M x y y'
  exact LinearMap.congr_fun key w

/-- **The relative tensor product with a bimodule is associative**: `M ⊗_A (N ⊗_B N')` and
`(M ⊗_A N) ⊗_B N'` are isomorphic as right differential graded `C`-modules, by the comparison
carrying `x ⊗ (y ⊗ y')` to `(x ⊗ y) ⊗ y'`. -/
def assocIso (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    tensorObj (compTensor N N') M ≅ tensorObj N' (tensorObj N M) where
  hom := assocForward N N' M
  inv := assocInverse N N' M
  hom_inv_id := assocForward_assocInverse N N' M
  inv_hom_id := assocInverse_assocForward N N' M

/-! ### Naturality -/

/-- **The associativity comparison is natural in the module.** Both sides carry
`x ⊗ (y ⊗ y')` to `(f x ⊗ y) ⊗ y'`. -/
theorem assocForward_naturality (N : Bimodule A B) (N' : Bimodule B C)
    {M M₂ : DifferentialGradedModule.{u, u, u} A} (f : M ⟶ M₂) :
    (tensorCompFunctor (compTensor N N')).map f ≫ assocForward N N' M₂ =
      assocForward N N' M ≫ (tensorCompFunctor N').map ((tensorCompFunctor N).map f) := by
  refine compTensor_hom_ext N N' M _ _ fun x y y' => ?_
  show (assocForward N N' M₂).toFun
      (((tensorCompFunctor (compTensor N N')).map f).toFun
        ((tensorPure (compTensor N N') M).toLinearMap x
          ((tensorPure N' N.rightModule).toLinearMap y y'))) =
    ((tensorCompFunctor N').map ((tensorCompFunctor N).map f)).toFun
      ((assocForward N N' M).toFun
        ((tensorPure (compTensor N N') M).toLinearMap x
          ((tensorPure N' N.rightModule).toLinearMap y y')))
  rw [tensorCompFunctor_map_pure (compTensor N N') f x
      ((tensorPure N' N.rightModule).toLinearMap y y'),
    assocForward_pure N N' M₂ (f.toFun x) y y', assocForward_pure N N' M x y y']
  refine Eq.symm ((tensorCompFunctor_map_pure N' ((tensorCompFunctor N).map f)
    ((tensorPure N M).toLinearMap x y) y').trans ?_)
  exact congrArg (fun w => (tensorPure N' (tensorObj N M₂)).toLinearMap w y')
    (tensorCompFunctor_map_pure N f x y)

/-- **The associativity isomorphism of the tensor functors of Tag 09LM**: tensoring with the
composite bimodule `N'' = N ⊗_B N'` is tensoring with `N` followed by tensoring with `N'`. -/
def tensorCompFunctorAssocIso (N : Bimodule A B) (N' : Bimodule B C) :
    tensorCompFunctor (compTensor N N') ≅ tensorCompFunctor N ⋙ tensorCompFunctor N' :=
  NatIso.ofComponents (fun M => assocIso N N' M) fun f => assocForward_naturality N N' f

end DifferentialGraded.Bimodule

end
