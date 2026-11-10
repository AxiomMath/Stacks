module

public import StacksFrontier.Cotangent.BaseChangeComplexCounit
public import StacksFrontier.Cotangent.LichtenbaumSchlessingerComparisonNatural
public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.RingTheory.TensorProduct.Free
public import Mathlib.RingTheory.Kaehler.Polynomial

/-!
# The Lichtenbaum–Schlessinger complex of a tensor product, from a presentation of a factor

Let `R` be a ring, `A` and `B` two `R`-algebras and `P → B` a polynomial presentation of `B`
over `R` with chosen generators `f_t` of its defining ideal. Base change along `R → A` gives the
polynomial presentation `P_A = A ⊗_R P → A ⊗_R B` of `A ⊗_R B` over `A`, with generators
`1 ⊗ f_t`. The map `P → P_A` lies over the square `R → A`, `B → A ⊗_R B` and carries `f_t` to
`1 ⊗ f_t`, so it induces the map of Lichtenbaum–Schlessinger complexes of [Stacks, Tag 09D7].

## Main definitions

* `Algebra.Presentation.tensorBaseChange`: the presentation of `A ⊗_R B` over `A`.
* `Algebra.Presentation.tensorBaseChangeHom`: the map of presentations over the square.
* `Algebra.Presentation.tensorBaseChangeComplexMap`: the induced map
  `(A ⊗_R B) ⊗_B L ⟶ L_A` of complexes of `A ⊗_R B`-modules, adjoint to the map of
  Tag 09D7.

## References

* [Stacks Project, Tag 09DB](https://stacks.math.columbia.edu/tag/09DB)
* [Stacks Project, Tag 09D7](https://stacks.math.columbia.edu/tag/09D7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TensorProduct

universe u

namespace Algebra.Presentation

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {X T : Type u}
  (P : Presentation R B X T) (A : Type u) [CommRing A] [Algebra R A]

/-- The presentation of `A ⊗_R B` over `A` obtained from `P` by base change along `R → A`, with
the relations indexed by `T ⊕ ∅`: the generator of index `t` is `1 ⊗ f_t`. -/
def tensorBaseChange : Presentation A (A ⊗[R] B) X (T ⊕ PEmpty.{u + 1}) :=
  (P.baseChange A).reindex (Equiv.refl X) (Equiv.sumEmpty T PEmpty)

/-- The generator `x` of `P.tensorBaseChange A` is `1 ⊗ x`. -/
theorem tensorBaseChange_val (x : X) :
    (P.tensorBaseChange A).val x = (1 : A) ⊗ₜ[R] P.val x :=
  rfl

/-- The relation of index `t` of `P.tensorBaseChange A` is the image of the relation `f_t` of `P`
under `R[X] → A[X]`. -/
theorem tensorBaseChange_relation (t : T) :
    (P.tensorBaseChange A).relation (Sum.inl t) =
      MvPolynomial.map (algebraMap R A) (P.relation t) := by
  change MvPolynomial.rename (Equiv.refl X).symm
    (MvPolynomial.map (algebraMap R A) (P.relation t)) = _
  rw [Equiv.refl_symm, Equiv.coe_refl, MvPolynomial.rename_id_apply]

/-- The map `P = R[X] → P_A = A[X]` sending each variable to itself, as a map of generators over
the square `R → A`, `B → A ⊗_R B`. -/
def tensorBaseChangeGeneratorsHom :
    Generators.Hom P.toGenerators (P.tensorBaseChange A).toGenerators where
  val x := MvPolynomial.X x
  aeval_val x := by
    rw [MvPolynomial.aeval_X]
    rfl

/-- The algebra map underlying `tensorBaseChangeGeneratorsHom` is `R[X] → A[X]`, applying
`algebraMap R A` to the coefficients. -/
theorem tensorBaseChangeGeneratorsHom_toAlgHom (p : P.Ring) :
    (P.tensorBaseChangeGeneratorsHom A).toAlgHom p = MvPolynomial.map (algebraMap R A) p := by
  have h : (P.tensorBaseChangeGeneratorsHom A).toAlgHom =
      MvPolynomial.mapAlgHom (Algebra.ofId R A) := by
    apply MvPolynomial.algHom_ext
    intro x
    rw [Generators.Hom.toAlgHom_X, MvPolynomial.mapAlgHom_apply, MvPolynomial.map_X]
    rfl
  rw [h, MvPolynomial.mapAlgHom_apply]
  rfl

/-- The map of presentations `P → P_A` over the square `R → A`, `B → A ⊗_R B`: the generator
`1 ⊗ f_t` of `P_A` is the image of `f_t`. -/
def tensorBaseChangeHom : LichtenbaumSchlessingerHom P (P.tensorBaseChange A) where
  toHom := P.tensorBaseChangeGeneratorsHom A
  relation_inl t := by
    rw [tensorBaseChange_relation, tensorBaseChangeGeneratorsHom_toAlgHom]

/-- The ring map underlying `tensorBaseChangeHom` is `R[X] → A[X]`, applying `algebraMap R A` to
the coefficients. -/
theorem tensorBaseChangeHom_ringHom (p : P.Ring) :
    (P.tensorBaseChangeHom A).ringHom p = MvPolynomial.map (algebraMap R A) p :=
  P.tensorBaseChangeGeneratorsHom_toAlgHom A p

/-- The map `(A ⊗_R B) ⊗_B L ⟶ L_A` of complexes of `A ⊗_R B`-modules: extension of scalars
along `B → A ⊗_R B` of the map `L → L_A` of Tag 09D7, followed by the counit of the
extension–restriction adjunction. -/
def tensorBaseChangeComplexMap :
    ((ModuleCat.extendScalars (algebraMap B (A ⊗[R] B))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj (lichtenbaumSchlessingerComplex P).complex ⟶
      (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).complex :=
  ((ModuleCat.extendScalars (algebraMap B (A ⊗[R] B))).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (P.tensorBaseChangeHom A).complexMap ≫
    ModuleCat.extendRestrictScalarsAdjCounitComplex (algebraMap B (A ⊗[R] B))
      (ComplexShape.up ℤ) (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).complex

end Algebra.Presentation

namespace ModuleCat

/-! ### The adjoint of a map carrying a basis to a basis -/

/-- Let `θ : X ⟶ Y` be a map from a module over `R` to a module over `S`, linear along
`f : R →+* S`, which carries a basis of `X` bijectively to a basis of `Y`. Then its adjoint
`S ⊗_R X ⟶ Y` is an isomorphism. -/
theorem isIso_extendRestrictScalarsAdj_homEquiv_symm_of_basis {R S : Type u} [CommRing R]
    [CommRing S] (f : R →+* S) {X : ModuleCat.{u} R} {Y : ModuleCat.{u} S}
    (θ : X ⟶ (ModuleCat.restrictScalars f).obj Y) {ι ι' : Type*} (bX : Module.Basis ι R X)
    (bY : Module.Basis ι' S Y) (e : ι ≃ ι') (h : ∀ i, θ (bX i) = bY (e i)) :
    IsIso (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm θ) := by
  let adj := ModuleCat.extendRestrictScalarsAdj.{u, u, u} f
  let v : ι' → (ModuleCat.extendScalars f).obj X := fun j => adj.unit.app X (bX (e.symm j))
  let Ψ : Y ⟶ (ModuleCat.extendScalars f).obj X :=
    ConcreteCategory.ofHom (C := ModuleCat S) (X := Y) (Y := (ModuleCat.extendScalars f).obj X)
      (bY.constr (M' := (ModuleCat.extendScalars f).obj X) S v)
  have hΨ : ∀ j, Ψ (bY j) = adj.unit.app X (bX (e.symm j)) := fun j =>
    bY.constr_basis (M' := (ModuleCat.extendScalars f).obj X) S v j
  have hunit : θ ≫ (ModuleCat.restrictScalars f).map Ψ = adj.unit.app X := by
    ext1
    refine bX.ext fun i => ?_
    change Ψ (θ (bX i)) = _
    rw [h, hΨ, Equiv.symm_apply_apply]
  have hθ : ∀ x, (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm θ)
      (adj.unit.app X x) = θ x := fun x =>
    congrArg (fun φ => φ x)
      (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).apply_symm_apply θ)
  refine ⟨Ψ, ?_, ?_⟩
  · rw [← Adjunction.homEquiv_naturality_right_symm, hunit, ← Adjunction.homEquiv_id,
      Equiv.symm_apply_apply]
  · ext1
    refine bY.ext fun j => ?_
    change (((ModuleCat.extendRestrictScalarsAdj f).homEquiv _ _).symm θ) (Ψ (bY j)) = bY j
    rw [hΨ, hθ, h, Equiv.apply_symm_apply]

end ModuleCat

namespace Algebra.Presentation

/-! ### The terms of the Lichtenbaum–Schlessinger complex in degrees `-1` and `0` are free -/

variable {R' S' : Type u} [CommRing R'] [CommRing S'] [Algebra R' S'] {X' T' : Type u}
  (Q : Presentation R' S' X' T')

/-- The basis `1 ⊗ e_t` of the term `S ⊗_P F` of the Lichtenbaum–Schlessinger complex in degree
`-1`. -/
def lsFreeBasis : Module.Basis T' S' ((lichtenbaumSchlessingerComplex Q).complex.X (-1)) :=
  (Algebra.TensorProduct.basis S' (Finsupp.basisSingleOne (R := Q.Ring) (ι := T'))).map
    (lichtenbaumSchlessingerComplex Q).freeIso.toLinearEquiv.symm

/-- Under `freeIso`, the basis vector `lsFreeBasis Q t` is `1 ⊗ e_t`. -/
theorem lsFreeBasis_apply (t : T') :
    (lichtenbaumSchlessingerComplex Q).freeIso.hom (lsFreeBasis Q t) =
      (1 : S') ⊗ₜ[Q.Ring] Finsupp.single t (1 : Q.Ring) := by
  rw [lsFreeBasis, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    Finsupp.coe_basisSingleOne]
  exact (lichtenbaumSchlessingerComplex Q).freeIso.inv_hom_id_apply _

/-- The basis vector of `Ω_{R[X]/R}` of index `x` is `d x`. -/
theorem mvPolynomialBasis_apply (x : X') :
    KaehlerDifferential.mvPolynomialBasis R' X' x =
      KaehlerDifferential.D R' (MvPolynomial X' R') (MvPolynomial.X x) :=
  (KaehlerDifferential.mvPolynomialBasis R' X').repr.injective (by
    rw [Module.Basis.repr_self, KaehlerDifferential.mvPolynomialBasis_repr_D_X])

/-- The basis `1 ⊗ d x` of the term `S ⊗_P Ω_{P/R}` of the Lichtenbaum–Schlessinger complex in
degree `0`. -/
def lsDifferentialBasis :
    Module.Basis X' S' ((lichtenbaumSchlessingerComplex Q).complex.X 0) :=
  (Algebra.TensorProduct.basis (R := Q.Ring) (M := Ω[Q.Ring⁄R']) S'
    (KaehlerDifferential.mvPolynomialBasis R' X')).map
    (lichtenbaumSchlessingerComplex Q).differentialIso.toLinearEquiv.symm

/-- Under `differentialIso`, the basis vector `lsDifferentialBasis Q x` is `1 ⊗ d x`. -/
theorem lsDifferentialBasis_apply (x : X') :
    (lichtenbaumSchlessingerComplex Q).differentialIso.hom (lsDifferentialBasis Q x) =
      (1 : S') ⊗ₜ[Q.Ring] KaehlerDifferential.D R' Q.Ring (MvPolynomial.X x) := by
  rw [lsDifferentialBasis, Module.Basis.map_apply, Algebra.TensorProduct.basis_apply,
    mvPolynomialBasis_apply]
  exact (lichtenbaumSchlessingerComplex Q).differentialIso.inv_hom_id_apply _

/-- The terms of the Lichtenbaum–Schlessinger complex in degrees `> -2` are projective. -/
theorem projective_lichtenbaumSchlessingerComplex_X (n : ℤ) (hn : -2 < n) :
    Projective ((lichtenbaumSchlessingerComplex Q).complex.X n) := by
  rcases eq_or_ne n (-1) with rfl | h1
  · exact ModuleCat.projective_of_free (lsFreeBasis Q)
  rcases eq_or_ne n 0 with rfl | h0
  · exact ModuleCat.projective_of_free (lsDifferentialBasis Q)
  exact ((lichtenbaumSchlessingerComplex Q).isZero_X n (by omega) h1 h0).projective

/-! ### The map `(A ⊗_R B) ⊗_B L ⟶ L_A` in the degrees `≠ -2` -/

section TensorBaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

variable {R B : Type u} [CommRing R] [CommRing B] [Algebra R B] {X T : Type u}
  (P : Presentation R B X T) (A : Type u) [CommRing A] [Algebra R A]

/-- In each degree the map `(A ⊗_R B) ⊗_B L ⟶ L_A` is the adjoint of the component of the map of
Tag 09D7. -/
theorem tensorBaseChangeComplexMap_f (n : ℤ) :
    (P.tensorBaseChangeComplexMap A).f n =
      ((ModuleCat.extendRestrictScalarsAdj (algebraMap B (A ⊗[R] B))).homEquiv _ _).symm
        ((P.tensorBaseChangeHom A).complexMap.f n) :=
  (Adjunction.homEquiv_counit (ModuleCat.extendRestrictScalarsAdj (algebraMap B (A ⊗[R] B)))
    _ _ _).symm

/-- In degree `-1` the map `(A ⊗_R B) ⊗_B L ⟶ L_A` is an isomorphism. -/
theorem isIso_tensorBaseChangeComplexMap_f_negOne :
    IsIso ((P.tensorBaseChangeComplexMap A).f (-1)) := by
  rw [tensorBaseChangeComplexMap_f]
  refine ModuleCat.isIso_extendRestrictScalarsAdj_homEquiv_symm_of_basis _ _ (lsFreeBasis P)
    (lsFreeBasis (P.tensorBaseChange A)) (Equiv.sumEmpty T PEmpty).symm fun t => ?_
  apply (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).freeIso.toLinearEquiv.injective
  change (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).freeIso.hom
      ((P.tensorBaseChangeHom A).complexMap.f (-1) (lsFreeBasis P t)) =
    (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).freeIso.hom
      (lsFreeBasis (P.tensorBaseChange A) (Sum.inl t))
  rw [LichtenbaumSchlessingerHom.complexMap_f,
    LichtenbaumSchlessingerHom.complexMapComponent_negOne,
    LichtenbaumSchlessingerHom.complexMapOne_apply, lsFreeBasis_apply, lsFreeBasis_apply,
    LichtenbaumSchlessingerHom.freeTensorMap_tmul, LichtenbaumSchlessingerHom.freeMap_single,
    map_one, map_one]

/-- In degree `0` the map `(A ⊗_R B) ⊗_B L ⟶ L_A` is an isomorphism. -/
theorem isIso_tensorBaseChangeComplexMap_f_zero :
    IsIso ((P.tensorBaseChangeComplexMap A).f 0) := by
  rw [tensorBaseChangeComplexMap_f]
  refine ModuleCat.isIso_extendRestrictScalarsAdj_homEquiv_symm_of_basis _ _
    (lsDifferentialBasis P) (lsDifferentialBasis (P.tensorBaseChange A)) (Equiv.refl X)
    fun x => ?_
  apply (lichtenbaumSchlessingerComplex
    (P.tensorBaseChange A)).differentialIso.toLinearEquiv.injective
  change (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).differentialIso.hom
      ((P.tensorBaseChangeHom A).complexMap.f 0 (lsDifferentialBasis P x)) =
    (lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).differentialIso.hom
      (lsDifferentialBasis (P.tensorBaseChange A) x)
  rw [LichtenbaumSchlessingerHom.complexMap_f, LichtenbaumSchlessingerHom.complexMapComponent_zero,
    LichtenbaumSchlessingerHom.complexMapZero_apply, lsDifferentialBasis_apply,
    lsDifferentialBasis_apply, LichtenbaumSchlessingerHom.differentialTensorMap_tmul_D, map_one,
    tensorBaseChangeHom_ringHom, MvPolynomial.map_X]

/-- In every degree `≠ -2` the map `(A ⊗_R B) ⊗_B L ⟶ L_A` is an isomorphism. -/
private theorem isIso_tensorBaseChangeComplexMap_f (n : ℤ) (hn : n ≠ -2) :
    IsIso ((P.tensorBaseChangeComplexMap A).f n) := by
  rcases eq_or_ne n (-1) with rfl | h1
  · exact isIso_tensorBaseChangeComplexMap_f_negOne P A
  rcases eq_or_ne n 0 with rfl | h0
  · exact isIso_tensorBaseChangeComplexMap_f_zero P A
  have h0' := Functor.map_isZero (ModuleCat.extendScalars (algebraMap B (A ⊗[R] B)))
    ((lichtenbaumSchlessingerComplex P).isZero_X n hn h1 h0)
  have hf := h0'.iso ((lichtenbaumSchlessingerComplex (P.tensorBaseChange A)).isZero_X n hn h1 h0)
  rw [h0'.eq_of_src ((P.tensorBaseChangeComplexMap A).f n) hf.hom]
  infer_instance

/-- The map `(A ⊗_R B) ⊗_B L ⟶ L_A` is onto in every degree `≠ -2`. -/
theorem epi_tensorBaseChangeComplexMap_f (n : ℤ) (hn : n ≠ -2) :
    Epi ((P.tensorBaseChangeComplexMap A).f n) :=
  have := isIso_tensorBaseChangeComplexMap_f P A n hn
  inferInstance

/-- The map `(A ⊗_R B) ⊗_B L ⟶ L_A` is injective in every degree `> -2`. -/
theorem mono_tensorBaseChangeComplexMap_f (n : ℤ) (hn : -2 < n) :
    Mono ((P.tensorBaseChangeComplexMap A).f n) :=
  have := isIso_tensorBaseChangeComplexMap_f P A n (by omega)
  inferInstance

end TensorBaseChange

end Algebra.Presentation
