module

public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorAssocHomotopy
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorUnit
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleHom
public import StacksFrontier.Homology.Devissage.CompactGeneratedNatTrans
public import StacksCore.Tactic.StacksAttribute

/-! # The composition of two derived tensor products

Let `(A, d)`, `(B, d)` and `(C, d)` be differential graded algebras over a commutative ring `R`,
let `N` be a differential graded `(A, B)`-bimodule, let `N'` be a differential graded
`(B, C)`-bimodule and let `N'' = N ⊗_B N'` be the composite differential graded `(A, C)`-bimodule
of Stacks Tag 0BZ3. If the comparison of Tag 0BZ2 from the derived to the plain tensor product
with `N'` is an isomorphism at the right differential graded `B`-module underlying `N`, then the
composition `D(A, d) → D(B, d) → D(C, d)` of `- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'` is isomorphic to
`- ⊗_A^𝐋 N''`. This is the assertion of Tag 0BZ3.

The comparison is the transformation the universal property of `- ⊗_A^𝐋 N''` as a total left
derived functor (Tag 09LS) produces from the associativity isomorphism
`(- ⊗_A N) ⊗_B N' ≅ - ⊗_A N''` of the plain tensor functors on the homotopy categories, and the
dévissage of Tag 0FQE reduces its invertibility to the shifts `A[k]` of the regular module. There
it is invertible because `A[k]` is orthogonal on the left to the acyclic modules by Tag 09K1, so
both derived tensor products are computed by the plain ones, and because the remaining comparison
is the one assumed invertible at `N`, transported along `A[k] ⊗_A N ≅ N[k]`.

## Main definitions

* `DifferentialGraded.Bimodule.derivedAssocCounit`: the comparison of the composite of the two
  derived tensor functors with the composite of the two plain ones.
* `DifferentialGraded.Bimodule.ordinaryAssocNatTrans`: the associativity isomorphism on the
  homotopy categories, with the target localized.
* `DifferentialGraded.Bimodule.derivedTensorCompNatTrans`: the comparison
  `- ⊗_A^𝐋 N ⋙ - ⊗_B^𝐋 N' ⟶ - ⊗_A^𝐋 N''`.
* `DifferentialGraded.Bimodule.derivedTensorFunctorCompTensorIso`: **Stacks Tag 0BZ3**, the
  isomorphism of functors.

## Main results

* `DifferentialGraded.Bimodule.derivedTensorCompNatTrans_app_comp_counit`: the defining identity
  of the comparison.
* `DifferentialGraded.Bimodule.isIso_derivedTensorCompNatTrans_app_shift_regularModule`: it is
  invertible at every shift of the regular module. This is where the hypothesis is spent.
* `DifferentialGraded.Bimodule.isIso_derivedTensorCompNatTrans_app_sigma` and
  `DifferentialGraded.Bimodule.derivedTensorCompNatTrans_twoOutOfThree`: the other two clauses of
  the dévissage of Tag 0FQE.

## References

* [Stacks Project, Tag 0BZ3](https://stacks.math.columbia.edu/tag/0BZ3); the derived tensor
  product and its comparison with the plain one are
  [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) and
  [Tag 0BZ2](https://stacks.math.columbia.edu/tag/0BZ2), the plain tensor functors are
  [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM), the dévissage is
  [Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE), the left orthogonality of the shifted
  regular module is [Tag 09K1](https://stacks.math.columbia.edu/tag/09K1), the unit isomorphism
  is [Tag 0FQN](https://stacks.math.columbia.edu/tag/0FQN) and the adjunction making the derived
  tensor functors preserve direct sums is
  [Tag 09LT](https://stacks.math.columbia.edu/tag/09LT).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

variable {R : Type u} [CommRing R] {A B C : DifferentialGradedAlgebra.{u, u} R}

/-! ### The two comparisons the universal property consumes -/

/-- The comparison of the composite `- ⊗_A^𝐋 N ⋙ - ⊗_B^𝐋 N'` of the derived tensor functors,
restricted along the localization, with the composite of the plain tensor functors on the
homotopy categories: the comparison of Tag 0BZ2 for `N`, tensored with `N'`, followed by the
comparison of Tag 0BZ2 for `N'`. -/
def derivedAssocCounit (N : Bimodule A B) (N' : Bimodule B C) :
    (quasiIsomorphisms' A).Q ⋙ (derivedTensorFunctor N ⋙ derivedTensorFunctor N') ⟶
      (tensorHomotopyFunctor N ⋙ tensorHomotopyFunctor N') ⋙ (quasiIsomorphisms' C).Q :=
  (Functor.associator (quasiIsomorphisms' A).Q (derivedTensorFunctor N)
      (derivedTensorFunctor N')).inv ≫
    Functor.whiskerRight (derivedTensorFunctorCounit N) (derivedTensorFunctor N') ≫
      (Functor.associator (tensorHomotopyFunctor N) (quasiIsomorphisms' B).Q
          (derivedTensorFunctor N')).hom ≫
        Functor.whiskerLeft (tensorHomotopyFunctor N) (derivedTensorFunctorCounit N') ≫
          (Functor.associator (tensorHomotopyFunctor N) (tensorHomotopyFunctor N')
            (quasiIsomorphisms' C).Q).inv

/-- The component of the comparison: the associators contribute identities. -/
theorem derivedAssocCounit_app (N : Bimodule A B) (N' : Bimodule B C)
    (X : HomotopyCategory A) :
    (derivedAssocCounit N N').app X =
      (derivedTensorFunctor N').map ((derivedTensorFunctorCounit N).app X) ≫
        (derivedTensorFunctorCounit N').app ((tensorHomotopyFunctor N).obj X) := by
  simp [derivedAssocCounit]

/-- The associativity isomorphism of the plain tensor functors on the homotopy categories, with
the target localized: a transformation from the composite of the two functors that Tag 09LS
derives to the one for `N''`. -/
def ordinaryAssocNatTrans (N : Bimodule A B) (N' : Bimodule B C) :
    (tensorHomotopyFunctor N ⋙ tensorHomotopyFunctor N') ⋙ (quasiIsomorphisms' C).Q ⟶
      tensorFunctorToDerivedCategory (compTensor N N') :=
  Functor.whiskerRight (tensorHomotopyFunctorAssocIso N N').inv (quasiIsomorphisms' C).Q

/-- The transformation `ordinaryAssocNatTrans N N'` commutes with the shifts by `ℤ`. -/
instance ordinaryAssocNatTrans_commShift (N : Bimodule A B) (N' : Bimodule B C) :
    NatTrans.CommShift (ordinaryAssocNatTrans N N') ℤ :=
  inferInstanceAs (NatTrans.CommShift (Functor.whiskerRight
    (tensorHomotopyFunctorAssocIso N N').inv (quasiIsomorphisms' C).Q) ℤ)

/-- The transformation `derivedAssocCounit N N'` commutes with the shifts by `ℤ`. -/
instance derivedAssocCounit_commShift (N : Bimodule A B) (N' : Bimodule B C) :
    NatTrans.CommShift (derivedAssocCounit N N') ℤ := by
  have h1 : NatTrans.CommShift (Functor.associator (quasiIsomorphisms' A).Q
      (derivedTensorFunctor N) (derivedTensorFunctor N')).inv ℤ := inferInstance
  have h2 : NatTrans.CommShift (Functor.whiskerRight (derivedTensorFunctorCounit N)
      (derivedTensorFunctor N')) ℤ := inferInstance
  have h3 : NatTrans.CommShift (Functor.associator (tensorHomotopyFunctor N)
      (quasiIsomorphisms' B).Q (derivedTensorFunctor N')).hom ℤ := inferInstance
  have h4 : NatTrans.CommShift (Functor.whiskerLeft (tensorHomotopyFunctor N)
      (derivedTensorFunctorCounit N')) ℤ := inferInstance
  have h5 : NatTrans.CommShift (Functor.associator (tensorHomotopyFunctor N)
      (tensorHomotopyFunctor N') (quasiIsomorphisms' C).Q).inv ℤ := inferInstance
  have h45 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h4 h5
  have h345 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h3 h45
  have h2345 := @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h2 h345
  exact @NatTrans.CommShift.comp _ _ _ _ _ _ _ _ _ ℤ _ _ _ _ _ _ h1 h2345

/-! ### The comparison of the derived tensor functors -/

/-- **The comparison `- ⊗_A^𝐋 N ⋙ - ⊗_B^𝐋 N' ⟶ - ⊗_A^𝐋 N''`.** It is the transformation that the
universal property of `- ⊗_A^𝐋 N''` as a total left derived functor attaches to the associativity
isomorphism of the plain tensor functors. -/
def derivedTensorCompNatTrans (N : Bimodule A B) (N' : Bimodule B C) :
    derivedTensorFunctor N ⋙ derivedTensorFunctor N' ⟶
      derivedTensorFunctor (compTensor N N') :=
  Functor.leftDerivedNatTrans (derivedTensorFunctor N ⋙ derivedTensorFunctor N')
    (derivedTensorFunctor (compTensor N N')) (derivedAssocCounit N N')
    (derivedTensorFunctorCounit (compTensor N N')) (quasiIsomorphisms' A)
    (ordinaryAssocNatTrans N N')

/-- **The defining identity of the comparison.** Followed by the comparison of Tag 0BZ2 for
`N''`, it is the comparison of Tag 0BZ2 for `N` and for `N'` followed by the associativity
isomorphism. -/
theorem derivedTensorCompNatTrans_app_comp_counit (N : Bimodule A B) (N' : Bimodule B C)
    (X : HomotopyCategory A) :
    (derivedTensorCompNatTrans N N').app ((quasiIsomorphisms' A).Q.obj X) ≫
        (derivedTensorFunctorCounit (compTensor N N')).app X =
      (derivedAssocCounit N N').app X ≫ (ordinaryAssocNatTrans N N').app X :=
  Functor.leftDerivedNatTrans_app (derivedTensorFunctor N ⋙ derivedTensorFunctor N')
    (derivedTensorFunctor (compTensor N N')) (derivedAssocCounit N N')
    (derivedTensorFunctorCounit (compTensor N N')) (quasiIsomorphisms' A)
    (ordinaryAssocNatTrans N N') X

/-- The comparison `derivedTensorCompNatTrans N N'` commutes with the shifts by `ℤ`. -/
instance derivedTensorCompNatTrans_commShift (N : Bimodule A B) (N' : Bimodule B C) :
    NatTrans.CommShift (derivedTensorCompNatTrans N N') ℤ :=
  Functor.leftDerivedNatTrans_commShift
    (derivedTensorFunctor N ⋙ derivedTensorFunctor N')
    (derivedTensorFunctor (compTensor N N')) (derivedAssocCounit N N')
    (derivedTensorFunctorCounit (compTensor N N')) (quasiIsomorphisms' A) ℤ
    (ordinaryAssocNatTrans N N')

/-! ### Clause (3) of the dévissage: the shifts of the algebra -/

/-- **Clause (3) of the dévissage of Stacks 0FQE for the comparison**: if the comparison of
Tag 0BZ2 for `N'` is invertible at the right differential graded `B`-module underlying `N`, then
the comparison `- ⊗_A^𝐋 N ⋙ - ⊗_B^𝐋 N' ⟶ - ⊗_A^𝐋 N''` is invertible at the class of every shift
`A[k]` of the regular module.

The shift `A[k]` is orthogonal on the left to the acyclic modules by Tag 09K1, so the comparisons
of Tag 0BZ2 for `N` and for `N''` are invertible there; the remaining one is the comparison for
`N'` at `A[k] ⊗_A N`, which the unit isomorphism of Tag 0FQN identifies with `N[k]`, where the
hypothesis applies. -/
theorem isIso_derivedTensorCompNatTrans_app_shift_regularModule (N : Bimodule A B)
    (N' : Bimodule B C)
    (hiso : IsIso ((derivedTensorFunctorCounit N').app
      ((toHomotopyCategory B).obj N.rightModule))) (k : ℤ) :
    IsIso ((derivedTensorCompNatTrans N N').app
      (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦k⟧)) := by
  set M := DifferentialGradedModule.shift (regularModule A) k with hM
  set X := (toHomotopyCategory A).obj M with hX
  have horth :=
    DifferentialGradedModule.leftOrthogonal_acyclic_toHomotopyCategory_shift_regularModule A k
  have hcN : IsIso ((derivedTensorFunctorCounit N).app X) :=
    isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal N X horth
  have hcN'' : IsIso ((derivedTensorFunctorCounit (compTensor N N')).app X) :=
    isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal (compTensor N N') X horth
  have e : ((toHomotopyCategory B).obj N.rightModule)⟦k⟧ ≅
      (tensorHomotopyFunctor N).obj X :=
    (((toHomotopyCategory B).commShiftIso k).app N.rightModule).symm ≪≫
      (toHomotopyCategory B).mapIso (tensorShiftRegularIso N k).symm ≪≫
        Iso.app (tensorCompFunctor_quotient N) M
  have hcN' : IsIso ((derivedTensorFunctorCounit N').app ((tensorHomotopyFunctor N).obj X)) :=
    StacksDraft.NatTransDevissage.isIso_app_of_iso (derivedTensorFunctorCounit N') e
      (StacksDraft.NatTransDevissage.isIso_app_shift (derivedTensorFunctorCounit N') hiso k)
  have hα : IsIso ((derivedAssocCounit N N').app X) := by
    rw [derivedAssocCounit_app]
    infer_instance
  have hord : IsIso ((ordinaryAssocNatTrans N N').app X) := by
    have h : (ordinaryAssocNatTrans N N').app X =
        (quasiIsomorphisms' C).Q.map ((tensorHomotopyFunctorAssocIso N N').inv.app X) := rfl
    rw [h]
    exact (inferInstance : IsIso ((quasiIsomorphisms' C).Q.map
      ((Iso.app (tensorHomotopyFunctorAssocIso N N') X).inv)))
  have hcomp : IsIso ((derivedTensorCompNatTrans N N').app ((quasiIsomorphisms' A).Q.obj X) ≫
      (derivedTensorFunctorCounit (compTensor N N')).app X) := by
    rw [derivedTensorCompNatTrans_app_comp_counit]
    infer_instance
  have hQX : IsIso ((derivedTensorCompNatTrans N N').app ((quasiIsomorphisms' A).Q.obj X)) :=
    IsIso.of_isIso_comp_right _ ((derivedTensorFunctorCounit (compTensor N N')).app X)
  exact StacksDraft.NatTransDevissage.isIso_app_of_iso (derivedTensorCompNatTrans N N')
    (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).commShiftIso k).app
      (regularModule A)) hQX

/-! ### Clauses (1) and (2) of the dévissage -/

/-- **Clause (1) of the dévissage of Stacks 0FQE for the comparison**: it is invertible at a
direct sum of objects at which it is invertible. All three derived tensor functors are left
adjoints by Tag 09LT, hence preserve direct sums. -/
theorem isIso_derivedTensorCompNatTrans_app_sigma (N : Bimodule A B) (N' : Bimodule B C)
    {ι : Type u} (K : ι → derivedCategory' A)
    (h : ∀ i, IsIso ((derivedTensorCompNatTrans N N').app (K i))) :
    IsIso ((derivedTensorCompNatTrans N N').app (∐ K)) := by
  have hN := (derivedTensorFunctor_adj_derivedHomFunctor N).leftAdjoint_preservesColimits
  have hN' := (derivedTensorFunctor_adj_derivedHomFunctor N').leftAdjoint_preservesColimits
  have hN'' :=
    (derivedTensorFunctor_adj_derivedHomFunctor (compTensor N N')).leftAdjoint_preservesColimits
  exact StacksDraft.NatTransDevissage.isIso_app_of_isColimit (derivedTensorCompNatTrans N N')
    (Discrete.functor K) (Limits.colimit.isColimit _) fun j => h j.as

/-- **Clause (2) of the dévissage of Stacks 0FQE for the comparison**: invertibility propagates
along the distinguished triangles of `D(A, d)`. All three derived tensor functors are exact and
the comparison commutes with the translation, so its components form a morphism of distinguished
triangles, to which the five lemma of Tag 014A applies. -/
theorem derivedTensorCompNatTrans_twoOutOfThree (N : Bimodule A B) (N' : Bimodule B C)
    (Δ : Pretriangulated.Triangle (derivedCategory' A))
    (hΔ : Δ ∈ Pretriangulated.distinguishedTriangles) :
    (IsIso ((derivedTensorCompNatTrans N N').app Δ.obj₁) →
        IsIso ((derivedTensorCompNatTrans N N').app Δ.obj₂) →
        IsIso ((derivedTensorCompNatTrans N N').app Δ.obj₃)) ∧
      (IsIso ((derivedTensorCompNatTrans N N').app Δ.obj₁) →
        IsIso ((derivedTensorCompNatTrans N N').app Δ.obj₃) →
        IsIso ((derivedTensorCompNatTrans N N').app Δ.obj₂)) ∧
      (IsIso ((derivedTensorCompNatTrans N N').app Δ.obj₂) →
        IsIso ((derivedTensorCompNatTrans N N').app Δ.obj₃) →
        IsIso ((derivedTensorCompNatTrans N N').app Δ.obj₁)) := by
  have hF := (derivedTensorFunctor N ⋙ derivedTensorFunctor N').map_distinguished Δ hΔ
  have hG := (derivedTensorFunctor (compTensor N N')).map_distinguished Δ hΔ
  let f := StacksDraft.NatTransDevissage.mapTriangleHom (derivedTensorCompNatTrans N N') Δ
  exact ⟨Pretriangulated.isIso₃_of_isIso₁₂ f hF hG, Pretriangulated.isIso₂_of_isIso₁₃ f hF hG,
    Pretriangulated.isIso₁_of_isIso₂₃ f hF hG⟩

/-! ### Stacks Tag 0BZ3 -/

/-- **The comparison is an isomorphism.** The three clauses of the dévissage of Tag 0FQE are the
invertibility at a direct sum, along a distinguished triangle, and at the shifts `A[k]` of the
regular module. -/
theorem isIso_derivedTensorCompNatTrans (N : Bimodule A B) (N' : Bimodule B C)
    (hiso : IsIso ((derivedTensorFunctorCounit N').app
      ((toHomotopyCategory B).obj N.rightModule))) :
    IsIso (derivedTensorCompNatTrans N N') := by
  have happ : ∀ Y, IsIso ((derivedTensorCompNatTrans N N').app Y) :=
    DifferentialGradedModule.property_of_coproducts_of_two_out_of_three_of_shifts A
      (fun Y => IsIso ((derivedTensorCompNatTrans N N').app Y))
      (fun K hK => isIso_derivedTensorCompNatTrans_app_sigma N N' K hK)
      (fun Δ hΔ => derivedTensorCompNatTrans_twoOutOfThree N N' Δ hΔ)
      (fun k => isIso_derivedTensorCompNatTrans_app_shift_regularModule N N' hiso k)
  have := happ
  exact NatIso.isIso_of_isIso_app _

/-- **Stacks Tag 0BZ3.** *"Let `R` be a ring. Let `(A, d)`, `(B, d)`, and `(C, d)` be differential
graded `R`-algebras. Let `N` be a differential graded `(A, B)`-bimodule. Let `N'` be a differential
graded `(B, C)`-bimodule. Assume that (0BZ2) `N_B ⊗_B^𝐋 N' ⟶ (N ⊗_B N')_C` is an isomorphism.
Then the composition `D(A, d) → D(B, d) → D(C, d)` of `- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'` is isomorphic
to `- ⊗_A^𝐋 N''` where `N'' = N ⊗_B N'`."*

The bimodule `N''` is `DifferentialGraded.Bimodule.compTensor N N'`, the relative tensor product
with the left `A`-action inherited from `N`, exactly as in the source; the isomorphism is
`DifferentialGraded.Bimodule.derivedTensorCompNatTrans`, the transformation attached to the
associativity isomorphism of the plain tensor functors by the universal property of Tag 09LS. -/
@[stacks 0BZ3 "composition of the derived tensor functors"]
def derivedTensorFunctorCompTensorIso (N : Bimodule A B) (N' : Bimodule B C)
    (hiso : IsIso ((derivedTensorFunctorCounit N').app
      ((toHomotopyCategory B).obj N.rightModule))) :
    derivedTensorFunctor N ⋙ derivedTensorFunctor N' ≅
      derivedTensorFunctor (compTensor N N') :=
  have := isIso_derivedTensorCompNatTrans N N' hiso
  asIso (derivedTensorCompNatTrans N N')

end DifferentialGraded.Bimodule

end
