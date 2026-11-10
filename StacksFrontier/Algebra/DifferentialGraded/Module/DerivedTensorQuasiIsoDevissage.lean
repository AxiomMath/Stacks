module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTensorEquivalence
public import StacksFrontier.Algebra.DifferentialGraded.Module.BaseChangeTensorKFlat
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleComposition
public import StacksFrontier.Algebra.DifferentialGraded.Module.BimoduleTensorUnit
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorBimoduleMap
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorHomAdjunction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorTriangulated
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorNatTransCommShift
public import StacksFrontier.Algebra.DifferentialGraded.Module.RegularModuleHom
public import StacksFrontier.Homology.Devissage.CompactGeneratedNatTrans

/-! # The second assertion of Stacks 09S3 along the dévissage from the shifts of the algebra

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R` and let
`f : N ⟶ N'` be a homomorphism of differential graded `(A, B)`-bimodules whose underlying map of
right differential graded `B`-modules is a quasi-isomorphism. The second assertion of Stacks Tag
09S3 is that the induced morphism `1 ⊗ f : - ⊗_A^𝐋 N ⟶ - ⊗_A^𝐋 N'` of functors `D(A, d) ⥤ D(B, d)`
is then an isomorphism.

The dévissage of Tag 0FQE reduces the invertibility of `1 ⊗ f` at an arbitrary object of `D(A, d)`
to three clauses: invertibility at a direct sum from invertibility at the summands, invertibility
at the third vertex of a distinguished triangle from invertibility at two of them, and
invertibility at every shift `A[k]` of the regular module. All three are proved here, so `1 ⊗ f`
is an isomorphism.

At `A[k]` the comparison of Tag 09LS is invertible, because `A[k]` is orthogonal on the left to the
acyclic modules by Tag 09K1, so `1 ⊗ f` is there the ordinary map
`A[k] ⊗_A N ⟶ A[k] ⊗_A N'`; the unit isomorphism `A[k] ⊗_A N ≅ N[k]` of Tag 0FQN identifies that
map with `f[k]`, which is a quasi-isomorphism. This is the step where the hypothesis on `f` is
spent. At a direct sum the clause is formal: `- ⊗_A^𝐋 N` is a left adjoint by Tag 09LT, hence
preserves direct sums.

## Main definitions

* `DifferentialGraded.Bimodule.tensorShiftRegularIsoComp`: the unit isomorphism
  `A[k] ⊗_A N ≅ N[k]`, read on the functor of Tag 09LM.
* `DifferentialGraded.Bimodule.DerivedTensorTwoOutOfThree`: the two-out-of-three clause of the
  dévissage of Tag 0FQE for the transformations `1 ⊗ f`.
* `DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoOfKFlat'`: the second conclusion of
  Tag 09S4 with the two appeals to the second assertion of Tag 09S3 discharged.

## Main results

* `DifferentialGraded.Bimodule.tensorShiftRegularIsoComp_naturality`: the unit isomorphism
  `A[k] ⊗_A N ≅ N[k]` is natural in the bimodule, carrying `1 ⊗ f` to `f[k]`.
* `DifferentialGraded.Bimodule.isIso_derivedTensorNatTrans_app_shift_regularModule`: clause (3)
  of the dévissage — `1 ⊗ f` is invertible at every shift of the regular module.
* `DifferentialGraded.Bimodule.isIso_derivedTensorNatTrans_app_sigma`: clause (1) of the
  dévissage — `1 ⊗ f` is invertible at a direct sum of objects at which it is invertible.
* `DifferentialGraded.Bimodule.derivedTensorTwoOutOfThree`: clause (2) of the dévissage — `1 ⊗ f`
  is invertible at the third vertex of a distinguished triangle as soon as it is invertible at two
  of them.
* `DifferentialGraded.Bimodule.quasiIsoInvertsDerivedTensor`: the second assertion of Tag 09S3.
* `DifferentialGraded.Bimodule.quasiIsoInvertsDerivedTensor_of_twoOutOfThree`: the second
  assertion of Tag 09S3 from the two-out-of-three clause.
* `DifferentialGraded.Bimodule.derivedTensorFunctorCompIsoOfKFlatOfTwoOutOfThree`: the second
  conclusion of Tag 09S4 with the two appeals to the second assertion of Tag 09S3 replaced by the
  two-out-of-three clause.

## References

* [Stacks Project, Tag 09S3](https://stacks.math.columbia.edu/tag/09S3); the dévissage is
  [Tag 0FQE](https://stacks.math.columbia.edu/tag/0FQE), the derived tensor product is
  [Tag 09LS](https://stacks.math.columbia.edu/tag/09LS) built on
  [Tag 09LM](https://stacks.math.columbia.edu/tag/09LM), the left orthogonality of the shifted
  regular module is [Tag 09K1](https://stacks.math.columbia.edu/tag/09K1), the shift comparison is
  [Tag 0FQN](https://stacks.math.columbia.edu/tag/0FQN), the adjunction is
  [Tag 09LT](https://stacks.math.columbia.edu/tag/09LT), and the composition of derived tensor
  products is [Tag 0BZ5](https://stacks.math.columbia.edu/tag/0BZ5) with
  [Tag 09S4](https://stacks.math.columbia.edu/tag/09S4).
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra.{u, u} R}

/-- The shift of a quasi-isomorphism of differential graded modules is a quasi-isomorphism: the
complex underlying `M[k]` is the `k`-th shift of the complex underlying `M`. -/
theorem quasiIso_forget_shiftFunctor_map {M M' : DifferentialGradedModule.{u, u, u} A}
    (g : M ⟶ M') (k : ℤ) (hg : QuasiIso ((forgetToCochainComplex A).map g)) :
    QuasiIso ((forgetToCochainComplex A).map ((shiftFunctor A k).map g)) := by
  let e := dgShiftToCochainShiftNatIso A k
  have h1 : QuasiIso ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) k).map
      ((forgetToCochainComplex A).map g)) := by
    rwa [CochainComplex.quasiIso_shift_iff]
  have h2 : QuasiIso (e.hom.app M ≫ (forgetToCochainComplex A ⋙
      CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} R) ℤ) k).map g) :=
    (quasiIso_iff_comp_left _ _).2 h1
  rw [← e.hom.naturality g] at h2
  exact (quasiIso_iff_comp_right
    ((shiftFunctor A k ⋙ forgetToCochainComplex A).map g) (e.hom.app M')).1 h2

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

attribute [local instance 10000] DifferentialGradedModule.instPretriangulatedHomotopyCategory'

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra.{u, u} R}

/-! ### The unit isomorphism at the shifts of the algebra, natural in the bimodule -/

/-- A homomorphism of differential graded bimodules commutes with the totalized left action of the
algebra, for an arbitrary element of the algebra and not only a homogeneous one. -/
theorem Hom.map_leftActionTotal' {N N' : Bimodule A B} (f : N ⟶ N') (a : A.A)
    (y : N.rightModule.M) :
    f.rightHom.toFun (leftActionTotal A B N.rightModule N.leftAction.1 a y) =
      leftActionTotal A B N'.rightModule N'.leftAction.1 a (f.rightHom.toFun y) := by
  induction a using DirectSum.Decomposition.inductionOn A.grading with
  | zero => simp
  | add a b ha hb => simp [ha, hb]
  | @homogeneous m a => exact Hom.map_leftActionTotal A B f m a a.2 y

/-- The unit isomorphism `A[k] ⊗_A N ≅ N[k]` of Stacks 0FQN, read on the functor of Tag 09LM. -/
def tensorShiftRegularIsoComp (N : Bimodule A B) (k : ℤ) :
    (tensorCompFunctor N).obj (DifferentialGradedModule.shift (regularModule A) k) ≅
      DifferentialGradedModule.shift N.rightModule k :=
  tensorShiftRegularIso N k

/-- The unit isomorphism `A[k] ⊗_A N ≅ N[k]` sends the pure tensor `a ⊗ y` to `a y`. -/
theorem tensorShiftRegularIsoComp_hom_pure (N : Bimodule A B) (k : ℤ)
    (a : (DifferentialGradedModule.shift (regularModule A) k).M) (y : N.rightModule.M) :
    (tensorShiftRegularIsoComp N k).hom.toFun
        (((tensorDGFunctor N).pure
          (DifferentialGradedModule.shift (regularModule A) k)).toLinearMap a y) =
      leftActionTotal A B N.rightModule N.leftAction.1 a y :=
  tensorShiftRegularIso_hom_pure N k a y

/-- **The unit isomorphism `A[k] ⊗_A N ≅ N[k]` is natural in the bimodule**: it carries the
ordinary map `1 ⊗ f : A[k] ⊗_A N ⟶ A[k] ⊗_A N'` to the shift `f[k]` of `f`.

Both sides are homomorphisms out of a relative tensor product, so they agree as soon as they agree
on pure tensors, where both send `a ⊗ y` to `a f(y)`. -/
theorem tensorShiftRegularIsoComp_naturality {N N' : Bimodule A B} (f : N ⟶ N') (k : ℤ) :
    (tensorModuleNatTrans f).app (DifferentialGradedModule.shift (regularModule A) k) ≫
        (tensorShiftRegularIsoComp N' k).hom =
      (tensorShiftRegularIsoComp N k).hom ≫
        (DifferentialGradedModule.shiftFunctor B k).map f.rightHom := by
  refine tensorObj_hom_ext' N (DifferentialGradedModule.shift (regularModule A) k) _ _
    fun x y => ?_
  have hL : ((tensorModuleNatTrans f).app (DifferentialGradedModule.shift (regularModule A) k) ≫
      (tensorShiftRegularIsoComp N' k).hom).toFun
        (((tensorDGFunctor N).pure
          (DifferentialGradedModule.shift (regularModule A) k)).toLinearMap x y) =
      leftActionTotal A B N'.rightModule N'.leftAction.1 x (f.rightHom.toFun y) := by
    change (tensorShiftRegularIsoComp N' k).hom.toFun
      ((tensorHomOfBimoduleHom f (DifferentialGradedModule.shift (regularModule A) k)).toFun _) = _
    rw [tensorHomOfBimoduleHom_pure, tensorShiftRegularIsoComp_hom_pure]
  have hR : ((tensorShiftRegularIsoComp N k).hom ≫
      (DifferentialGradedModule.shiftFunctor B k).map f.rightHom).toFun
        (((tensorDGFunctor N).pure
          (DifferentialGradedModule.shift (regularModule A) k)).toLinearMap x y) =
      f.rightHom.toFun (leftActionTotal A B N.rightModule N.leftAction.1 x y) := by
    change ((DifferentialGradedModule.shiftFunctor B k).map f.rightHom).toFun
      ((tensorShiftRegularIsoComp N k).hom.toFun _) = _
    rw [tensorShiftRegularIsoComp_hom_pure, DifferentialGradedModule.shiftFunctor_map_toFun]
  exact hL.trans ((Hom.map_leftActionTotal' f x y).symm.trans hR.symm)

/-! ### Clause (3) of the dévissage: the shifts of the algebra -/

/-- **Tensoring the shift `A[k]` with a quasi-isomorphism of bimodules is a quasi-isomorphism.**
Under the unit isomorphism `A[k] ⊗_A N ≅ N[k]` the map `1 ⊗ f` is the shift `f[k]`. -/
theorem quasiIso_tensorModuleNatTrans_app_shift_regularModule {N N' : Bimodule A B} (f : N ⟶ N')
    (hf : QuasiIso ((forgetToCochainComplex B).map f.rightHom)) (k : ℤ) :
    QuasiIso ((forgetToCochainComplex B).map
      ((tensorModuleNatTrans f).app (DifferentialGradedModule.shift (regularModule A) k))) := by
  have h2 : QuasiIso ((forgetToCochainComplex B).map
        ((tensorModuleNatTrans f).app (DifferentialGradedModule.shift (regularModule A) k)) ≫
      (forgetToCochainComplex B).map (tensorShiftRegularIsoComp N' k).hom) := by
    rw [← Functor.map_comp (forgetToCochainComplex B), tensorShiftRegularIsoComp_naturality f k,
      Functor.map_comp (forgetToCochainComplex B), quasiIso_iff_comp_left]
    exact quasiIso_forget_shiftFunctor_map f.rightHom k hf
  exact (quasiIso_iff_comp_right _
    ((forgetToCochainComplex B).map (tensorShiftRegularIsoComp N' k).hom)).1 h2

/-- **Clause (3) of the dévissage of Stacks 0FQE for `1 ⊗ f`**: for a homomorphism `f : N ⟶ N'` of
differential graded `(A, B)`-bimodules which is a quasi-isomorphism of right differential graded
`B`-modules, the transformation `1 ⊗ f : - ⊗_A^𝐋 N ⟶ - ⊗_A^𝐋 N'` is invertible at the class of
every shift `A[k]` of the regular module.

The shift `A[k]` is orthogonal on the left to the acyclic modules by Tag 09K1, so both comparisons
of Tag 09LS are invertible there and `1 ⊗ f` becomes the ordinary map `A[k] ⊗_A N ⟶ A[k] ⊗_A N'`,
which is the quasi-isomorphism `f[k]`. -/
@[stacks 09S3 "the second assertion at the shifts A[k] of the algebra, where the \
quasi-isomorphism hypothesis enters"]
theorem isIso_derivedTensorNatTrans_app_shift_regularModule {N N' : Bimodule A B} (f : N ⟶ N')
    (hf : QuasiIso ((forgetToCochainComplex B).map f.rightHom)) (k : ℤ) :
    IsIso ((derivedTensorNatTrans f).app
      (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).obj (regularModule A))⟦k⟧)) := by
  set M := DifferentialGradedModule.shift (regularModule A) k
  set X := (toHomotopyCategory A).obj M
  have hq : IsIso ((quasiIsomorphisms' B).Q.map ((toHomotopyCategory B).map
      ((tensorModuleNatTrans f).app M))) :=
    DifferentialGradedModule.isIso_q_map_toHomotopyCategory_map _
      (quasiIso_tensorModuleNatTrans_app_shift_regularModule f hf k)
  have hord : IsIso ((ordinaryTensorNatTrans f).app X) := by
    rw [ordinaryTensorNatTrans_app, tensorHomotopyNatTrans_app, Functor.map_comp,
      Functor.map_comp]
    infer_instance
  have hc : ∀ N : Bimodule A B, IsIso ((derivedTensorFunctorCounit N).app X) := fun N =>
    isIso_derivedTensorFunctorCounit_app_of_leftOrthogonal N X
      (DifferentialGradedModule.leftOrthogonal_acyclic_toHomotopyCategory_shift_regularModule A k)
  have hcN := hc N
  have hcN' := hc N'
  have hcomp : IsIso ((derivedTensorNatTrans f).app ((quasiIsomorphisms' A).Q.obj X) ≫
      (derivedTensorFunctorCounit N').app X) := by
    rw [derivedTensorNatTrans_app_comp_counit]
    infer_instance
  have hQX : IsIso ((derivedTensorNatTrans f).app ((quasiIsomorphisms' A).Q.obj X)) :=
    IsIso.of_isIso_comp_right _ ((derivedTensorFunctorCounit N').app X)
  exact StacksDraft.NatTransDevissage.isIso_app_of_iso (derivedTensorNatTrans f)
    (((toHomotopyCategory A ⋙ (quasiIsomorphisms' A).Q).commShiftIso k).app
      (regularModule A)) hQX

/-! ### Clause (1) of the dévissage: direct sums -/

/-- **Clause (1) of the dévissage of Stacks 0FQE for `1 ⊗ f`**: the transformation
`1 ⊗ f : - ⊗_A^𝐋 N ⟶ - ⊗_A^𝐋 N'` is invertible at a direct sum of objects of `D(A, d)` at which it
is invertible.

Both functors are left adjoints by Tag 09LT, hence preserve direct sums, so the component of
`1 ⊗ f` at `⨁ᵢ Kᵢ` is the comparison of the two colimit cocones induced by its components at the
`Kᵢ`. -/
@[stacks 09S3 "the second assertion at a direct sum, from the summands"]
theorem isIso_derivedTensorNatTrans_app_sigma {N N' : Bimodule A B} (f : N ⟶ N')
    {ι : Type u} (K : ι → derivedCategory' A)
    (h : ∀ i, IsIso ((derivedTensorNatTrans f).app (K i))) :
    IsIso ((derivedTensorNatTrans f).app (∐ K)) := by
  have hN := (derivedTensorFunctor_adj_derivedHomFunctor N).leftAdjoint_preservesColimits
  have hN' := (derivedTensorFunctor_adj_derivedHomFunctor N').leftAdjoint_preservesColimits
  exact StacksDraft.NatTransDevissage.isIso_app_of_isColimit (derivedTensorNatTrans f)
    (Discrete.functor K) (Limits.colimit.isColimit _) fun j => h j.as

/-! ### Clause (2) of the dévissage, and the second assertion of Tag 09S3 -/

/-- **Clause (2) of the dévissage of Stacks 0FQE for the transformations `1 ⊗ f`**: invertibility
of `1 ⊗ f : - ⊗_A^𝐋 N ⟶ - ⊗_A^𝐋 N'` propagates along the distinguished triangles of `D(A, d)` —
if it holds at two of the three vertices then it holds at the third. -/
def DerivedTensorTwoOutOfThree (A B : DifferentialGradedAlgebra.{u, u} R) : Prop :=
  ∀ {N N' : Bimodule A B} (f : N ⟶ N') (Δ : Pretriangulated.Triangle (derivedCategory' A)),
    Δ ∈ Pretriangulated.distinguishedTriangles →
      (IsIso ((derivedTensorNatTrans f).app Δ.obj₁) →
          IsIso ((derivedTensorNatTrans f).app Δ.obj₂) →
          IsIso ((derivedTensorNatTrans f).app Δ.obj₃)) ∧
        (IsIso ((derivedTensorNatTrans f).app Δ.obj₁) →
          IsIso ((derivedTensorNatTrans f).app Δ.obj₃) →
          IsIso ((derivedTensorNatTrans f).app Δ.obj₂)) ∧
        (IsIso ((derivedTensorNatTrans f).app Δ.obj₂) →
          IsIso ((derivedTensorNatTrans f).app Δ.obj₃) →
          IsIso ((derivedTensorNatTrans f).app Δ.obj₁))

/-- **Clause (2) of the dévissage of Stacks 0FQE for the transformations `1 ⊗ f`.** The derived
tensor functors are exact and `1 ⊗ f` commutes with the translation, so its components form a
morphism of distinguished triangles, to which the five lemma of Tag 014A applies. -/
@[stacks 09S3 "the second assertion along a distinguished triangle, two out of three"]
theorem derivedTensorTwoOutOfThree (A B : DifferentialGradedAlgebra.{u, u} R) :
    DerivedTensorTwoOutOfThree A B := by
  intro N N' f Δ hΔ
  have hF := (derivedTensorFunctor N).map_distinguished Δ hΔ
  have hG := (derivedTensorFunctor N').map_distinguished Δ hΔ
  let φ := StacksDraft.NatTransDevissage.mapTriangleHom (derivedTensorNatTrans f) Δ
  exact ⟨Pretriangulated.isIso₃_of_isIso₁₂ φ hF hG, Pretriangulated.isIso₂_of_isIso₁₃ φ hF hG,
    Pretriangulated.isIso₁_of_isIso₂₃ φ hF hG⟩

/-- **The second assertion of Stacks 09S3 from the two-out-of-three clause.** A homomorphism
`f : N ⟶ N'` of differential graded `(A, B)`-bimodules which is a quasi-isomorphism of right
differential graded `B`-modules induces an isomorphism `1 ⊗ f : - ⊗_A^𝐋 N ⟶ - ⊗_A^𝐋 N'` of
functors `D(A, d) ⥤ D(B, d)`.

The three clauses of the dévissage of Tag 0FQE are the hypothesis, the invertibility at a direct
sum, and the invertibility at the shifts `A[k]`. -/
theorem quasiIsoInvertsDerivedTensor_of_twoOutOfThree
    (htri : DerivedTensorTwoOutOfThree A B) : QuasiIsoInvertsDerivedTensor A B := by
  intro N N' f hf
  have happ : ∀ Y, IsIso ((derivedTensorNatTrans f).app Y) :=
    DifferentialGradedModule.property_of_coproducts_of_two_out_of_three_of_shifts A
      (fun Y => IsIso ((derivedTensorNatTrans f).app Y))
      (isIso_derivedTensorNatTrans_app_sigma f)
      (htri f)
      (isIso_derivedTensorNatTrans_app_shift_regularModule f hf)
  exact NatIso.isIso_of_isIso_app _

/-- **The second assertion of Stacks 09S3.** A homomorphism `f : N ⟶ N'` of differential graded
`(A, B)`-bimodules that is a quasi-isomorphism of right differential graded `B`-modules induces
an isomorphism `1 ⊗ f : - ⊗_A^𝐋 N ⟶ - ⊗_A^𝐋 N'` of functors `D(A, d) ⥤ D(B, d)`. -/
@[stacks 09S3 "the second assertion"]
theorem quasiIsoInvertsDerivedTensor (A B : DifferentialGradedAlgebra.{u, u} R) :
    QuasiIsoInvertsDerivedTensor A B :=
  quasiIsoInvertsDerivedTensor_of_twoOutOfThree (derivedTensorTwoOutOfThree A B)

/-! ### The second conclusion of Tag 09S4 -/

/-- The second conclusion of Stacks 09S4 with the two appeals to the second assertion of Tag 09S3
replaced by the two-out-of-three clause of the dévissage of Tag 0FQE for the two pairs of
algebras: the composite of `- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'` is isomorphic to `- ⊗_A^𝐋 N''` for the
bimodule `N'' = Ñ ⊗_B Ñ'`. -/
def derivedTensorFunctorCompIsoOfKFlatOfTwoOutOfThree {A B C : DifferentialGradedAlgebra.{u, u} R}
    (hABtri : DerivedTensorTwoOutOfThree A B) (hBCtri : DerivedTensorTwoOutOfThree B C)
    (hcomp : DerivedTensorCompositionData A B C) (hdev : BaseChangeDevissage A B C)
    (hC : CochainComplex.KFlat.{u, u} (regularModule C).toCochainComplex)
    (N : Bimodule A B) (N' : Bimodule B C) :
    derivedTensorFunctor N ⋙ derivedTensorFunctor N' ≅
      derivedTensorFunctor (compTensorResolution N N') :=
  derivedTensorFunctorCompIsoOfKFlat
    (quasiIsoInvertsDerivedTensor_of_twoOutOfThree hABtri)
    (quasiIsoInvertsDerivedTensor_of_twoOutOfThree hBCtri) hcomp hdev hC N N'

/-- The second conclusion of Stacks 09S4 from Tag 0BZ3 for the triple and the dévissage performed
in the proof of Tag 0BZ5: the composite of `- ⊗_A^𝐋 N` and `- ⊗_B^𝐋 N'` is isomorphic to
`- ⊗_A^𝐋 N''` for the bimodule `N'' = Ñ ⊗_B Ñ'`. -/
def derivedTensorFunctorCompIsoOfKFlat' {A B C : DifferentialGradedAlgebra.{u, u} R}
    (hcomp : DerivedTensorCompositionData A B C) (hdev : BaseChangeDevissage A B C)
    (hC : CochainComplex.KFlat.{u, u} (regularModule C).toCochainComplex)
    (N : Bimodule A B) (N' : Bimodule B C) :
    derivedTensorFunctor N ⋙ derivedTensorFunctor N' ≅
      derivedTensorFunctor (compTensorResolution N N') :=
  derivedTensorFunctorCompIsoOfKFlat (quasiIsoInvertsDerivedTensor A B)
    (quasiIsoInvertsDerivedTensor B C) hcomp hdev hC N N'

end DifferentialGraded.Bimodule

end
