module

public import StacksFrontier.Algebra.DifferentialGraded.Endomorphism.BimoduleTensorEquivalence
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedCategoryDevissage
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedRestriction
public import StacksFrontier.Algebra.DifferentialGraded.Module.DerivedTensorAlgebraComparison

/-! # Restriction of scalars, direct sums, shifts, and the graded pieces over the base

Let `(A, d)` and `(B, d)` be differential graded algebras over a commutative ring `R`. A
differential graded `(A, B)`-bimodule is the same thing as a right differential graded module
over `Aᵒᵖ ⊗_R B` (Tag 0FQJ), and the right differential graded `B`-module underlying it is the
restriction of scalars of that module along `b ↦ 1 ⊗ b`. This file records what that restriction
does to the three constructions a property-(P) filtration is built from:

* it commutes with direct sums and with the translation, both being untouched on underlying
  modules;
* it carries an admissible short exact sequence to an admissible short exact sequence, the graded
  splittings being `R`-linear maps that stay right linear;
* **it carries the regular module of `Aᵒᵖ ⊗_R B` to `(A ⊗_R B)_B`**, the base-change module of
  Tag 0BZ4. Consequently it carries a direct sum of shifts of `Aᵒᵖ ⊗_R B` — the graded pieces of a
  property-(P) filtration — to a direct sum of shifts of `(A ⊗_R B)_B`.

## Main definitions

* `DifferentialGradedModule.restrictScalarsDirectSumObjIso`,
  `DifferentialGradedModule.restrictScalarsShiftIso`: the first two compatibilities.
* `DifferentialGraded.Bimodule.oppTensorEquiv`: the identification of the carrier of `Aᵒᵖ ⊗_R B`
  with that of `A ⊗_R B`, induced by the identification of the graded opposite of `A` with `A`.
* `DifferentialGradedModule.directSumObjMapIso`: a family of isomorphisms induces an isomorphism
  of the direct sums.
* `DifferentialGraded.Bimodule.baseChangeRegularIso`: the regular module of `Aᵒᵖ ⊗_R B`, read over
  `B`, is `(A ⊗_R B)_B`.
* `DifferentialGraded.Bimodule.baseChangeDirectSumShiftsIso`: a direct sum of shifts of
  `Aᵒᵖ ⊗_R B`, read over `B`, is the direct sum of the corresponding shifts of `(A ⊗_R B)_B`.
* `DifferentialGraded.Bimodule.ofTensorRightModuleToTensorIso`: the right `B`-module underlying
  the module over `Aᵒᵖ ⊗_R B` attached to a bimodule is the right `B`-module of that bimodule.

## Implementation notes

*Why the first two compatibilities are the identity.* `DifferentialGradedModule.restrictScalars`,
`DifferentialGradedModule.directSumObj` and `DifferentialGradedModule.shift` all leave the
underlying `R`-module, the grading and the differential alone — a shift only reindexes the grading
and rescales the differential — so each comparison is the identity map, and only its compatibility
with the right action has content.

*Why the regular module needs a map.* The graded opposite of `A` is not `A`: it is a differential
graded algebra given together with an `R`-linear identification
`DifferentialGraded.Opposite.equiv` of its carrier with that of `A` which preserves the grading,
the differential and the unit but reverses multiplication up to the Koszul sign. Tensoring that
identification with the identity of `B` gives an identification of the carriers of `Aᵒᵖ ⊗_R B` and
`A ⊗_R B`. It is not an algebra map; but the right `B`-action on either is multiplication by
`1 ⊗ b`, which involves only the unit of the first factor, and the differential is the signed
differential, which involves only the degree of the first factor, so the identification is an
isomorphism of right differential graded `B`-modules. That is all Tag 0BZ4 asks of it.

## References

* [Stacks Project, Tag 0FQJ](https://stacks.math.columbia.edu/tag/0FQJ), bimodules as modules over
  the graded tensor product.
* [Stacks Project, Tag 0BYX](https://stacks.math.columbia.edu/tag/0BYX), restriction of scalars.
* [Stacks Project, Tag 0BZ4](https://stacks.math.columbia.edu/tag/0BZ4), the base-change module.
-/

@[expose] public noncomputable section

open CategoryTheory
open scoped DirectSum TensorProduct

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A B : DifferentialGradedAlgebra R}

/-! ### Restriction of scalars of a graded homomorphism, and of admissible sequences -/

/-- A homomorphism of *graded* right `B`-modules is a homomorphism of graded right `A`-modules
between the restrictions along `φ : A → B`. -/
def restrictScalarsGradedHom (φ : A.Hom B) {N N' : DifferentialGradedModule B}
    (f : GradedHom N N') : GradedHom (restrictScalars φ N) (restrictScalars φ N') where
  toFun := f.toFun
  map_smul x a := f.map_smul x (φ.toAlgebraHom a)
  map_grading := f.map_grading

/-- **Restriction of scalars carries an admissible short exact sequence to an admissible short
exact sequence.** The three underlying maps and the two graded splittings are unchanged. -/
theorem restrictScalarsHom_isAdmissibleShortExact (φ : A.Hom B)
    {K L M : DifferentialGradedModule B} (i : K ⟶ L) (p : L ⟶ M)
    (h : IsAdmissibleShortExact i p) :
    IsAdmissibleShortExact (restrictScalarsHom φ i) (restrictScalarsHom φ p) where
  injective := h.injective
  surjective := h.surjective
  exact := h.exact
  admissibleMono :=
    ⟨restrictScalarsGradedHom φ h.admissibleMono.choose, h.admissibleMono.choose_spec⟩
  admissibleEpi :=
    ⟨restrictScalarsGradedHom φ h.admissibleEpi.choose, h.admissibleEpi.choose_spec⟩

/-! ### Restriction of scalars, direct sums and shifts -/

/-- **Restriction of scalars commutes with direct sums.** Both sides have the bare direct sum of
the carriers as underlying module, with the componentwise grading and differential. -/
def restrictScalarsDirectSumObjIso (φ : A.Hom B) {ι : Type u} [DecidableEq ι]
    (N : ι → DifferentialGradedModule B) :
    restrictScalars φ (directSumObj N) ≅ directSumObj (fun i => restrictScalars φ (N i)) :=
  Hom.isoOfBijective
    { toFun := LinearMap.id
      map_smul := fun _ _ => rfl
      map_grading := fun _ _ hx => hx
      map_d := rfl }
    Function.bijective_id

/-- **A family of isomorphisms induces an isomorphism of the direct sums.** -/
def directSumObjMapIso {ι : Type u} [DecidableEq ι] {N N' : ι → DifferentialGradedModule B}
    (e : ∀ i, N i ≅ N' i) : directSumObj N ≅ directSumObj N' where
  hom := directSumMap N (fun i => (e i).hom)
  inv := directSumMap N' (fun i => (e i).inv)
  hom_inv_id := by
    refine directSum_hom_ext _ fun j => ?_
    rw [Category.comp_id, ← Category.assoc, directSumInj_comp_directSumMap, Category.assoc,
      directSumInj_comp_directSumMap, ← Category.assoc, (e j).hom_inv_id, Category.id_comp]
  inv_hom_id := by
    refine directSum_hom_ext _ fun j => ?_
    rw [Category.comp_id, ← Category.assoc, directSumInj_comp_directSumMap, Category.assoc,
      directSumInj_comp_directSumMap, ← Category.assoc, (e j).inv_hom_id, Category.id_comp]

/-- **Restriction of scalars commutes with the translation.** Both sides have the same underlying
module, the same reindexed grading and the same rescaled differential. -/
def restrictScalarsShiftIso (φ : A.Hom B) (N : DifferentialGradedModule B) (k : ℤ) :
    restrictScalars φ (shift N k) ≅ shift (restrictScalars φ N) k :=
  Hom.isoOfBijective
    { toFun := LinearMap.id
      map_smul := fun _ _ => rfl
      map_grading := fun _ _ hx => hx
      map_d := rfl }
    Function.bijective_id

end DifferentialGradedModule

namespace DifferentialGraded.Bimodule

open DifferentialGradedModule DifferentialGradedAlgebra

variable {R : Type u} [CommRing R]

/-! ### The carrier of `Aᵒᵖ ⊗_R B` is the carrier of `A ⊗_R B` -/

variable (A B : DifferentialGradedAlgebra.{u, u} R)

/-- The identification of the carrier of `Aᵒᵖ ⊗_R B` with that of `A ⊗_R B`: the identification
`DifferentialGraded.Opposite.equiv` of the graded opposite of `A` with `A`, tensored with the
identity of `B`. -/
def oppTensorEquiv : (tensorAlgebra A B).A ≃ₗ[R] (tensorProduct A B).A :=
  ((GradedTensorProduct.of R (oppAlgebra A).grading B.grading).symm.trans
    (TensorProduct.congr (DifferentialGradedAlgebra.opposite R A).equiv
      (LinearEquiv.refl R B.A))).trans (GradedTensorProduct.of R A.grading B.grading)

/-- The identification of carriers on a pure tensor. -/
theorem oppTensorEquiv_tmul (a : (oppAlgebra A).A) (b : B.A) :
    oppTensorEquiv A B ((a ᵍ⊗ₜ[R] b : (oppAlgebra A).grading ᵍ⊗[R] B.grading)) =
      (((DifferentialGradedAlgebra.opposite R A).equiv a) ᵍ⊗ₜ[R] b :
        A.grading ᵍ⊗[R] B.grading) :=
  rfl

/-- The identification of carriers preserves the grading. -/
theorem oppTensorEquiv_mem_grading (n : ℤ) (x : (tensorAlgebra A B).A)
    (hx : x ∈ (tensorAlgebra A B).grading n) :
    oppTensorEquiv A B x ∈ (tensorProduct A B).grading n := by
  refine tensorProductGrading_induction (oppAlgebra A) B n
    (motive := fun x => oppTensorEquiv A B x ∈ (tensorProduct A B).grading n) ?_ ?_ ?_ ?_ x hx
  · simpa only [map_zero] using ((tensorProduct A B).grading n).zero_mem
  · intro y z hy hz
    simpa only [map_add] using ((tensorProduct A B).grading n).add_mem hy hz
  · intro r y hy
    simpa only [map_smul] using ((tensorProduct A B).grading n).smul_mem r hy
  · intro p q a b ha hb hpq
    rw [oppTensorEquiv_tmul]
    rw [← hpq]
    exact tmul_mem_grading A B p q _ b
      (((DifferentialGradedAlgebra.opposite R A).mem_grading_iff p a).mp ha) hb

/-- The identification of carriers commutes with the signed differentials. -/
theorem oppTensorEquiv_d (x : (tensorAlgebra A B).A) :
    oppTensorEquiv A B ((tensorAlgebra A B).d x) =
      (tensorProduct A B).d (oppTensorEquiv A B x) := by
  refine tensorProduct_induction (oppAlgebra A) B
    (P := fun x => oppTensorEquiv A B ((tensorAlgebra A B).d x) =
      (tensorProduct A B).d (oppTensorEquiv A B x)) ?_ ?_ ?_ x
  · simp only [map_zero]
  · intro y z hy hz
    simp only [map_add, hy, hz]
  · intro m n a b
    have hma : ((DifferentialGradedAlgebra.opposite R A).equiv (a : (oppAlgebra A).A)) ∈
        A.grading m :=
      ((DifferentialGradedAlgebra.opposite R A).mem_grading_iff m _).mp a.property
    rw [tensorProductDifferential_tmul (oppAlgebra A) B m a (b : B.A), map_add,
      oppTensorEquiv_tmul, map_zsmul, oppTensorEquiv_tmul, oppTensorEquiv_tmul,
      tensorProductDifferential_tmul A B m
        (⟨_, hma⟩ : A.grading m) (b : B.A),
      (DifferentialGradedAlgebra.opposite R A).map_d]

/-- The identification of carriers is right linear for multiplication by `1 ⊗ b`, which is the
right `B`-action on either tensor product algebra. -/
theorem oppTensorEquiv_mul_includeRight (x : (tensorAlgebra A B).A) (b : B.A) :
    oppTensorEquiv A B
        (x * (tensorIncludeRightHom (oppAlgebra A) B).toAlgebraHom b) =
      oppTensorEquiv A B x * (tensorIncludeRightHom A B).toAlgebraHom b := by
  have hopp : ((tensorIncludeRightHom (oppAlgebra A) B).toAlgebraHom b :
      (tensorAlgebra A B).A) =
      ((1 : (oppAlgebra A).A) ᵍ⊗ₜ[R] b : (oppAlgebra A).grading ᵍ⊗[R] B.grading) := rfl
  have hplain : ((tensorIncludeRightHom A B).toAlgebraHom b : (tensorProduct A B).A) =
      ((1 : A.A) ᵍ⊗ₜ[R] b : A.grading ᵍ⊗[R] B.grading) := rfl
  refine tensorProduct_induction (oppAlgebra A) B
    (P := fun x => oppTensorEquiv A B
        (x * (tensorIncludeRightHom (oppAlgebra A) B).toAlgebraHom b) =
      oppTensorEquiv A B x * (tensorIncludeRightHom A B).toAlgebraHom b) ?_ ?_ ?_ x
  · simp only [zero_mul, map_zero]
  · intro y z hy hz
    simp only [add_mul, map_add, hy, hz]
  · intro m n a b'
    rw [hopp, hplain, tmul_mul_one_tmul (oppAlgebra A) B (a : (oppAlgebra A).A) (b' : B.A) b,
      oppTensorEquiv_tmul, oppTensorEquiv_tmul, tmul_mul_one_tmul A B _ (b' : B.A) b]

/-! ### The graded pieces over the base -/

/-- **The regular module of `Aᵒᵖ ⊗_R B`, read as a right differential graded `B`-module, is
`(A ⊗_R B)_B`.** The comparison is `DifferentialGraded.Bimodule.oppTensorEquiv`; its right
`B`-linearity is multiplication by `1 ⊗ b` on either side. -/
def baseChangeRegularIso :
    ofTensorRightModule A B (regularModule (tensorAlgebra A B)) ≅ baseChangeModule A B :=
  Hom.isoOfBijective
    { toFun := (oppTensorEquiv A B).toLinearMap
      map_smul := fun x b => oppTensorEquiv_mul_includeRight A B x b
      map_grading := oppTensorEquiv_mem_grading A B
      map_d := LinearMap.ext (oppTensorEquiv_d A B) }
    (oppTensorEquiv A B).bijective

/-- **A direct sum of shifts of `Aᵒᵖ ⊗_R B`, read over `B`, is the direct sum of the corresponding
shifts of `(A ⊗_R B)_B`.** These are the graded pieces of a property-(P) filtration of a
differential graded `(A, B)`-bimodule, read as a right differential graded `B`-module. -/
def baseChangeDirectSumShiftsIso {ι : Type u} [DecidableEq ι] (k : ι → ℤ) :
    ofTensorRightModule A B (directSumShifts (tensorAlgebra A B) k) ≅
      directSumObj (fun i => shift (baseChangeModule A B) (k i)) :=
  (restrictScalarsFunctor (tensorIncludeRightHom (oppAlgebra A) B)).mapIso
      (directSumObjIsoDirectSumShifts (tensorAlgebra A B) k).symm ≪≫
    restrictScalarsDirectSumObjIso (tensorIncludeRightHom (oppAlgebra A) B)
      (fun i => shift (regularModule (tensorAlgebra A B)) (k i)) ≪≫
    directSumObjMapIso (fun i =>
      restrictScalarsShiftIso (tensorIncludeRightHom (oppAlgebra A) B)
          (regularModule (tensorAlgebra A B)) (k i) ≪≫
        (shiftFunctor B (k i)).mapIso (baseChangeRegularIso A B))

/-- **The right differential graded `B`-module underlying the module over `Aᵒᵖ ⊗_R B` attached to
a differential graded `(A, B)`-bimodule is the right `B`-module of that bimodule.** The two have
the same carrier, grading and differential, and the combined action restricted along `b ↦ 1 ⊗ b`
is the right `B`-action by
`DifferentialGraded.Bimodule.tensorActionApply_includeRight`. -/
def ofTensorRightModuleToTensorIso (M : Bimodule A B) :
    ofTensorRightModule A B (toTensorModule A B M) ≅ M.rightModule :=
  Hom.isoOfBijective
    { toFun := LinearMap.id
      map_smul := fun x b => tensorActionApply_includeRight A B M b x
      map_grading := fun _ _ hx => hx
      map_d := rfl }
    Function.bijective_id

end DifferentialGraded.Bimodule

end
