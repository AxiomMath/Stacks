module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorAssocIso
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorNatTransCommShift

/-! # Associativity of the relative tensor product on the homotopy categories

Let `(A, d)`, `(B, d)` and `(C, d)` be differential graded algebras over a commutative ring `R`,
let `N` be a differential graded `(A, B)`-bimodule, let `N'` be a differential graded
`(B, C)`-bimodule and write `N'' = N ⊗_B N'`. The associativity isomorphism
`DifferentialGraded.Bimodule.tensorCompFunctorAssocIso` of the tensor functors on differential
graded modules commutes with the translation — both sides are the identity on pure tensors once
the sign-free shift comparison of Tag 0FQN is unwound — and therefore descends to an isomorphism
`- ⊗_A N'' ≅ (- ⊗_A N) ⊗_B N'` of the functors `K(A, d) ⥤ K(C, d)` of Tag 09LM which again
commutes with the translation.

## Main definitions

* `DifferentialGraded.Bimodule.tensorHomotopyFunctorAssocIso`: the associativity isomorphism on
  the homotopy categories.

## Main results

* `DifferentialGraded.Bimodule.assocForward_commShift`: the associativity isomorphism of the
  functors on differential graded modules commutes with the translation.
* `DifferentialGraded.Bimodule.tensorHomotopyFunctorAssocIso_commShift`: so does its descent to
  the homotopy categories.

## References

* [Stacks Project, Tag 09LM](https://stacks.math.columbia.edu/tag/09LM) is the tensor functor on
  differential graded modules and on homotopy categories;
  [Tag 0FQN](https://stacks.math.columbia.edu/tag/0FQN) is the shift comparison, and
  [Tag 0BZ3](https://stacks.math.columbia.edu/tag/0BZ3) is the composite bimodule.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}

/-! ### The associativity isomorphism commutes with the shift -/

/-- Both sides of the compatibility of the associativity isomorphism with the shift send the pure
tensor `x ⊗ (y ⊗ y')` of `M[n] ⊗_A N''` to `(x ⊗ y) ⊗ y'`. -/
private theorem assocForward_commShift_pure (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) (x : M.M) (y : N.rightModule.M)
    (y' : N'.rightModule.M) :
    ((CategoryTheory.shiftFunctor (DifferentialGradedModule C) n).map
          (assocForward N N' M)).toFun
        ((((tensorCompFunctor (compTensor N N')).commShiftIso n).hom.app M).toFun
          (assocPure N N' (DifferentialGradedModule.shift M n) x (compPure N N' y y'))) =
      (((tensorCompFunctor N ⋙ tensorCompFunctor N').commShiftIso n).hom.app M).toFun
        ((assocForward N N' (DifferentialGradedModule.shift M n)).toFun
          (assocPure N N' (DifferentialGradedModule.shift M n) x (compPure N N' y y'))) := by
  have hL : (((tensorCompFunctor (compTensor N N')).commShiftIso n).hom.app M).toFun
        (assocPure N N' (DifferentialGradedModule.shift M n) x (compPure N N' y y')) =
      assocPure N N' M x (compPure N N' y y') :=
    tensorShiftIso_inv_pure (compTensor N N') M n x (compPure N N' y y')
  have hR1 : (assocForward N N' (DifferentialGradedModule.shift M n)).toFun
        (assocPure N N' (DifferentialGradedModule.shift M n) x (compPure N N' y y')) =
      (tensorPure N' (tensorObj N (DifferentialGradedModule.shift M n))).toLinearMap
        ((tensorPure N (DifferentialGradedModule.shift M n)).toLinearMap x y) y' :=
    assocForward_pure N N' (DifferentialGradedModule.shift M n) x y y'
  have s1 : ((tensorCompFunctor N').map
          (((tensorCompFunctor N).commShiftIso n).hom.app M)).toFun
        ((tensorPure N' (tensorObj N (DifferentialGradedModule.shift M n))).toLinearMap
          ((tensorPure N (DifferentialGradedModule.shift M n)).toLinearMap x y) y') =
      (tensorPure N' (DifferentialGradedModule.shift (tensorObj N M) n)).toLinearMap
        ((tensorPure N M).toLinearMap x y) y' := by
    refine (tensorCompFunctor_map_pure N' (((tensorCompFunctor N).commShiftIso n).hom.app M)
      ((tensorPure N (DifferentialGradedModule.shift M n)).toLinearMap x y) y').trans ?_
    exact congrArg
      (fun w => (tensorPure N' (DifferentialGradedModule.shift (tensorObj N M) n)).toLinearMap
        w y') (tensorShiftIso_inv_pure N M n x y)
  have hR2 : (((tensorCompFunctor N ⋙ tensorCompFunctor N').commShiftIso n).hom.app M).toFun
        ((tensorPure N' (tensorObj N (DifferentialGradedModule.shift M n))).toLinearMap
          ((tensorPure N (DifferentialGradedModule.shift M n)).toLinearMap x y) y') =
      (tensorPure N' (tensorObj N M)).toLinearMap ((tensorPure N M).toLinearMap x y) y' := by
    rw [Functor.commShiftIso_comp_hom_app]
    change (((tensorCompFunctor N').commShiftIso n).hom.app
        ((tensorCompFunctor N).obj M)).toFun
      (((tensorCompFunctor N').map (((tensorCompFunctor N).commShiftIso n).hom.app M)).toFun
        ((tensorPure N' (tensorObj N (DifferentialGradedModule.shift M n))).toLinearMap
          ((tensorPure N (DifferentialGradedModule.shift M n)).toLinearMap x y) y')) = _
    rw [s1]
    exact tensorShiftIso_inv_pure N' (tensorObj N M) n ((tensorPure N M).toLinearMap x y) y'
  rw [hL, hR1, hR2]
  change (assocForward N N' M).toFun (assocPure N N' M x (compPure N N' y y')) = _
  exact assocForward_pure N N' M x y y'

/-- The compatibility of the associativity isomorphism with the shift, at an object. -/
private theorem assocForward_commShift_app (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) (n : ℤ) :
    ((tensorCompFunctor (compTensor N N')).commShiftIso n).hom.app M ≫
        (CategoryTheory.shiftFunctor (DifferentialGradedModule C) n).map
          (assocForward N N' M) =
      assocForward N N' (DifferentialGradedModule.shift M n) ≫
        ((tensorCompFunctor N ⋙ tensorCompFunctor N').commShiftIso n).hom.app M := by
  refine tensorObj_hom_ext (compTensor N N') (DifferentialGradedModule.shift M n) _ _
    fun x z => ?_
  have key : ((((tensorCompFunctor (compTensor N N')).commShiftIso n).hom.app M ≫
          (CategoryTheory.shiftFunctor (DifferentialGradedModule C) n).map
            (assocForward N N' M)).toFun.comp
        (assocPure N N' (DifferentialGradedModule.shift M n) x)) =
      ((assocForward N N' (DifferentialGradedModule.shift M n) ≫
          ((tensorCompFunctor N ⋙ tensorCompFunctor N').commShiftIso n).hom.app M).toFun.comp
        (assocPure N N' (DifferentialGradedModule.shift M n) x)) := by
    refine tensorObj_linearMap_ext N' N.rightModule _ _ fun y y' => ?_
    exact assocForward_commShift_pure N N' M n x y y'
  exact LinearMap.congr_fun key z

/-- **The associativity isomorphism of the tensor functors of Tag 09LM commutes with the
translation.** Both sides are homomorphisms out of `M[n] ⊗_A N''` sending the pure tensor
`x ⊗ (y ⊗ y')` to `(x ⊗ y) ⊗ y'`, the shift comparison of Tag 0FQN being the identity on pure
tensors. -/
instance assocForward_commShift (N : Bimodule A B) (N' : Bimodule B C) :
    NatTrans.CommShift (tensorCompFunctorAssocIso N N').hom ℤ := by
  constructor
  intro n
  ext M
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  exact assocForward_commShift_app N N' M n

/-! ### The associativity isomorphism on the homotopy categories

The restriction of the isomorphism along the quotient by homotopy is a composite of seven
isomorphisms of functors `Mod^{dg}_{(A, d)} ⥤ K(C, d)`, and the seven are named one at a time.
The reason is the compatibility with the translation: `CategoryTheory.NatTrans.CommShift` is
stated against a *chosen* compatibility of each of the two functors with the shift, and the ones
chosen for `(F ⋙ G) ⋙ H` and for `F ⋙ (G ⋙ H)` are different terms, so a composite whose
grouping shifts silently from one to the other cannot be assembled from the compatibilities of
its factors. The associators are therefore written out, which is what makes every composition
below one of two transformations between functors with the same chosen compatibility. -/

/-- The comparison of Tag 09LM with the quotient, for the composite bimodule, reversed. -/
def assocHomotopyStep₁ (N : Bimodule A B) (N' : Bimodule B C) :
    toHomotopyCategory A ⋙ tensorHomotopyFunctor (compTensor N N') ≅
      tensorCompFunctor (compTensor N N') ⋙ toHomotopyCategory C :=
  (tensorCompFunctor_quotient (compTensor N N')).symm

/-- The plain associativity isomorphism, with the target localized. -/
def assocHomotopyStep₂ (N : Bimodule A B) (N' : Bimodule B C) :
    tensorCompFunctor (compTensor N N') ⋙ toHomotopyCategory C ≅
      (tensorCompFunctor N ⋙ tensorCompFunctor N') ⋙ toHomotopyCategory C :=
  Functor.isoWhiskerRight (tensorCompFunctorAssocIso N N') (toHomotopyCategory C)

/-- The comparison of Tag 09LM with the quotient, for `N'`, inside tensoring with `N`. -/
def assocHomotopyStep₄ (N : Bimodule A B) (N' : Bimodule B C) :
    tensorCompFunctor N ⋙ tensorCompFunctor N' ⋙ toHomotopyCategory C ≅
      tensorCompFunctor N ⋙ toHomotopyCategory B ⋙ tensorHomotopyFunctor N' :=
  Functor.isoWhiskerLeft (tensorCompFunctor N) (tensorCompFunctor_quotient N')

/-- The comparison of Tag 09LM with the quotient, for `N`, followed by tensoring with `N'`. -/
def assocHomotopyStep₆ (N : Bimodule A B) (N' : Bimodule B C) :
    (tensorCompFunctor N ⋙ toHomotopyCategory B) ⋙ tensorHomotopyFunctor N' ≅
      (toHomotopyCategory A ⋙ tensorHomotopyFunctor N) ⋙ tensorHomotopyFunctor N' :=
  Functor.isoWhiskerRight (tensorCompFunctor_quotient N) (tensorHomotopyFunctor N')

/-- The associativity isomorphism, restricted along the quotient by homotopy: the plain
associativity isomorphism read through the compatibility of Tag 09LM with the passage to homotopy
classes. -/
def assocHomotopyAux (N : Bimodule A B) (N' : Bimodule B C) :
    toHomotopyCategory A ⋙ tensorHomotopyFunctor (compTensor N N') ≅
      toHomotopyCategory A ⋙ (tensorHomotopyFunctor N ⋙ tensorHomotopyFunctor N') :=
  assocHomotopyStep₁ N N' ≪≫ assocHomotopyStep₂ N N' ≪≫
    Functor.associator (tensorCompFunctor N) (tensorCompFunctor N') (toHomotopyCategory C) ≪≫
      assocHomotopyStep₄ N N' ≪≫
        (Functor.associator (tensorCompFunctor N) (toHomotopyCategory B)
          (tensorHomotopyFunctor N')).symm ≪≫
          assocHomotopyStep₆ N N' ≪≫
            Functor.associator (toHomotopyCategory A) (tensorHomotopyFunctor N)
              (tensorHomotopyFunctor N')

/-- The compatibility of Tag 09LM with the quotient by homotopy commutes with the translation, at
raised priority.

This is `DifferentialGraded.Bimodule.tensorCompFunctor_quotient_commShift` again. The two
`CategoryTheory.NatTrans.CommShift` instances for the inverse and for the symmetry of an
isomorphism refer to each other, so a search for the compatibility of an isomorphism with the
translation cycles between them unless an instance matching the isomorphism at hand is reached
first; raising the priority is what makes that happen here. -/
instance (priority := 2000) tensorCompFunctor_quotient_commShift' (N : Bimodule A B) :
    NatTrans.CommShift (tensorCompFunctor_quotient N).hom ℤ :=
  tensorCompFunctor_quotient_commShift N

/-- The first step `assocHomotopyStep₁ N N'` commutes with the translation. -/
instance assocHomotopyStep₁_commShift (N : Bimodule A B) (N' : Bimodule B C) :
    NatTrans.CommShift (assocHomotopyStep₁ N N').hom ℤ :=
  inferInstanceAs (NatTrans.CommShift
    (tensorCompFunctor_quotient (compTensor N N')).inv ℤ)

/-- The second step `assocHomotopyStep₂ N N'` commutes with the translation. -/
instance assocHomotopyStep₂_commShift (N : Bimodule A B) (N' : Bimodule B C) :
    NatTrans.CommShift (assocHomotopyStep₂ N N').hom ℤ :=
  inferInstanceAs (NatTrans.CommShift
    (Functor.whiskerRight (tensorCompFunctorAssocIso N N').hom (toHomotopyCategory C)) ℤ)

/-- The fourth step `assocHomotopyStep₄ N N'` commutes with the translation. -/
instance assocHomotopyStep₄_commShift (N : Bimodule A B) (N' : Bimodule B C) :
    NatTrans.CommShift (assocHomotopyStep₄ N N').hom ℤ :=
  inferInstanceAs (NatTrans.CommShift
    (Functor.whiskerLeft (tensorCompFunctor N) (tensorCompFunctor_quotient N').hom) ℤ)

/-- The sixth step `assocHomotopyStep₆ N N'` commutes with the translation. -/
instance assocHomotopyStep₆_commShift (N : Bimodule A B) (N' : Bimodule B C) :
    NatTrans.CommShift (assocHomotopyStep₆ N N').hom ℤ :=
  inferInstanceAs (NatTrans.CommShift
    (Functor.whiskerRight (tensorCompFunctor_quotient N).hom (tensorHomotopyFunctor N')) ℤ)

/-- The restriction of the associativity isomorphism along the quotient by homotopy commutes with
the translation: it is a composite of seven isomorphisms that do.

The composition instance is applied with its two arguments supplied rather than searched for: the
search explores the compatibility of each intermediate composite functor with the shift afresh at
every branch, and on a seven-fold composite that exhausts the heartbeat budget. -/
instance assocHomotopyAux_commShift (N : Bimodule A B) (N' : Bimodule B C) :
    NatTrans.CommShift (assocHomotopyAux N N').hom ℤ := by
  have h1 : NatTrans.CommShift (assocHomotopyStep₁ N N').hom ℤ := inferInstance
  have h2 : NatTrans.CommShift (assocHomotopyStep₂ N N').hom ℤ := inferInstance
  have h3 : NatTrans.CommShift (Functor.associator (tensorCompFunctor N)
      (tensorCompFunctor N') (toHomotopyCategory C)).hom ℤ := inferInstance
  have h4 : NatTrans.CommShift (assocHomotopyStep₄ N N').hom ℤ := inferInstance
  have h5 : NatTrans.CommShift (Functor.associator (tensorCompFunctor N)
      (toHomotopyCategory B) (tensorHomotopyFunctor N')).inv ℤ := inferInstance
  have h6 : NatTrans.CommShift (assocHomotopyStep₆ N N').hom ℤ := inferInstance
  have h7 : NatTrans.CommShift (Functor.associator (toHomotopyCategory A)
      (tensorHomotopyFunctor N) (tensorHomotopyFunctor N')).hom ℤ := inferInstance
  have h67 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h6 h7
  have h567 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h5 h67
  have h4567 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h4 h567
  have h34567 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h3 h4567
  have h234567 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h2 h34567
  have he : (assocHomotopyAux N N').hom =
      (assocHomotopyStep₁ N N').hom ≫ (assocHomotopyStep₂ N N').hom ≫
        (Functor.associator (tensorCompFunctor N) (tensorCompFunctor N')
          (toHomotopyCategory C)).hom ≫ (assocHomotopyStep₄ N N').hom ≫
          (Functor.associator (tensorCompFunctor N) (toHomotopyCategory B)
            (tensorHomotopyFunctor N')).inv ≫ (assocHomotopyStep₆ N N').hom ≫
            (Functor.associator (toHomotopyCategory A) (tensorHomotopyFunctor N)
              (tensorHomotopyFunctor N')).hom := rfl
  rw [he]
  exact @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h1 h234567

/-- **The associativity isomorphism on the homotopy categories**: tensoring with the composite
bimodule `N'' = N ⊗_B N'` is tensoring with `N` followed by tensoring with `N'`, as functors
`K(A, d) ⥤ K(C, d)`. It is the descent of the plain associativity isomorphism along the quotient
by homotopy, which is available because `K(A, d)` is that quotient. -/
def tensorHomotopyFunctorAssocIso (N : Bimodule A B) (N' : Bimodule B C) :
    tensorHomotopyFunctor (compTensor N N') ≅
      tensorHomotopyFunctor N ⋙ tensorHomotopyFunctor N' where
  hom := CategoryTheory.Quotient.natTransLift (homotopyRel A) (assocHomotopyAux N N').hom
  inv := CategoryTheory.Quotient.natTransLift (homotopyRel A) (assocHomotopyAux N N').inv
  hom_inv_id := by
    rw [CategoryTheory.Quotient.comp_natTransLift, Iso.hom_inv_id,
      CategoryTheory.Quotient.natTransLift_id]
  inv_hom_id := by
    rw [CategoryTheory.Quotient.comp_natTransLift, Iso.inv_hom_id,
      CategoryTheory.Quotient.natTransLift_id]

/-- The associativity isomorphism on the homotopy categories, at the class of a module `M`, is
the restricted isomorphism `assocHomotopyAux N N'` at `M`. -/
theorem tensorHomotopyFunctorAssocIso_hom_app (N : Bimodule A B) (N' : Bimodule B C)
    (M : DifferentialGradedModule.{u, u, u} A) :
    (tensorHomotopyFunctorAssocIso N N').hom.app ((toHomotopyCategory A).obj M) =
      (assocHomotopyAux N N').hom.app M := rfl

/-- **The associativity isomorphism on the homotopy categories commutes with the translation.**
Its restriction along the quotient by homotopy is the plain one, read through the comparison of
Tag 09LM, and every factor of that composite commutes with the translation. -/
instance tensorHomotopyFunctorAssocIso_commShift (N : Bimodule A B) (N' : Bimodule B C) :
    NatTrans.CommShift (tensorHomotopyFunctorAssocIso N N').hom ℤ := by
  have hw : Functor.whiskerLeft (toHomotopyCategory A)
        (tensorHomotopyFunctorAssocIso N N').hom =
      (assocHomotopyAux N N').hom :=
    NatTrans.ext (funext fun M => tensorHomotopyFunctorAssocIso_hom_app N N' M)
  have h : NatTrans.CommShift
      (Functor.whiskerLeft (toHomotopyCategory A)
        (tensorHomotopyFunctorAssocIso N N').hom) ℤ := by
    rw [hw]
    infer_instance
  exact NatTrans.commShift_of_whiskerLeft_quotientFunctor ℤ
    (tensorHomotopyFunctorAssocIso N N').hom

end DifferentialGraded.Bimodule

end
