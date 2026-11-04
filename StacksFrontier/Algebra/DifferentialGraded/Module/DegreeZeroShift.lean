module

public import StacksFrontier.Algebra.DifferentialGraded.Module.DegreeZeroAlgebra
public import StacksFrontier.Algebra.DifferentialGraded.Module.HasShift

/-!
# The degree-zero comparison commutes with the shift

Let `R` be a commutative ring, `S` an `R`-algebra, not necessarily commutative, and `A` an
`R`-algebra identified with the opposite algebra of `S`. The homogeneous-components functor
`DifferentialGradedModule.degreeZeroComponentFunctor` carries a differential graded module over
`S` in degree zero to a cochain complex of `A`-modules. Both sides are shifted by `ℤ`: on the
left by `DifferentialGradedModule.shift`, whose degree `n` part is the old degree `n + k` and
whose differential is multiplied by `(-1)^k`, and on the right by
`CochainComplex.shiftFunctor`, which does the same thing. The comparison is therefore the
identity on every homogeneous component, and this file assembles it into a
`CategoryTheory.Functor.CommShift ℤ`.

## Main definitions

* `DifferentialGradedModule.degreeZeroComplexShiftIso`: the comparison between the complex of
  homogeneous components of `M[k]` and the `k`-th shift of the complex of homogeneous components
  of `M`.
* `DifferentialGradedModule.degreeZeroComponentShiftNatIso`: that comparison, natural in `M`.
* `DifferentialGradedModule.degreeZeroComponentFunctor_commShift`: the resulting
  `(degreeZeroComponentFunctor R A).CommShift ℤ`.

## Main results

* `DifferentialGradedModule.degreeZeroComplex_d_val`: the differential of the complex of
  homogeneous components is the differential of the module.
* `DifferentialGradedModule.degreeZeroComplex_eqToHom_val`: a transport along an equality of
  degrees does not change the underlying element.

## Implementation notes

The two shift conventions agree on the nose: `(M[k])^n = M^{n+k}` and `d_{M[k]} = (-1)^k d_M`
hold by definition on both sides, so every component of the comparison is the identity and the
only content of the compatibility conditions is the bookkeeping of the degree arithmetic.

The degree of a term of the shifted complex is spelled `i + k` when it is reached through the
shifted complex and `i` when it is reached through the shifted module; the two spellings are equal
only after unfolding `DifferentialGradedModule.degreeZeroComplex`, which no rewrite can do. The
comparison of the differentials is therefore split into two lemmas, each written entirely in one
of the two spellings, which meet at the closing `exact` of
`DifferentialGradedModule.degreeZeroComplexShiftIso`; this is the same device as in the
comparison of the shift with the underlying cochain complex of `R`-modules in
`StacksFrontier/Algebra/DGA/QuasiIsomorphisms.lean`.

The remaining `eqToHom`s come from the comparison isomorphisms of the two shifts with the
identity functor and with the sum: `n + 0` and `n`, and `n + b + a` and `n + (a + b)`, are equal
but not definitionally equal integers, so on the cochain side those comparisons are transports
along the equalities, while on the differential graded side they are the identity on the
underlying module. `DifferentialGradedModule.degreeZeroComplex_eqToHom_val` reduces such a
transport to the identity on elements.

## References

* [Stacks Project, Tag 09JL](https://stacks.math.columbia.edu/tag/09JL) for the shift of a
  differential graded module, and [Tag 09JI](https://stacks.math.columbia.edu/tag/09JI) for the
  modules themselves.
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace DifferentialGradedModule

open DifferentialGradedAlgebra

variable {R : Type u} [CommRing R] {A : Type u} [Ring A] [Algebra R A]
  {S : Type u} [Ring S] [Algebra R S] [IsOppositeAlgebra R S A]

attribute [local instance] degreeZeroOppositeModule degreeZeroComponentModule

/-- The differential of the complex of homogeneous components is the differential of the
differential graded module. -/
theorem degreeZeroComplex_d_val (M : DifferentialGradedModule (degreeZero R S)) {p q : ℤ}
    (hpq : p + 1 = q) (x : (degreeZeroComplex (A := A) M).X p) :
    (((degreeZeroComplex (A := A) M).d p q).hom x : M.grading q).val =
      M.d (x : M.grading p).val := by
  subst hpq
  rw [degreeZeroComplex_d_self]
  rfl

/-- Transporting a homogeneous component along an equality of degrees does not change the
underlying element. -/
theorem degreeZeroComplex_eqToHom_val (M : DifferentialGradedModule (degreeZero R S)) {i j : ℤ}
    (hij : i = j) (x : M.grading i) :
    ((eqToHom (congrArg (fun m : ℤ => ModuleCat.of A (M.grading m)) hij)) x).val = x.val := by
  subst hij
  rfl

/-- Scalars pulled out of a homogeneous component of the complex of homogeneous components. -/
theorem degreeZeroComplex_zsmul_val (M : DifferentialGradedModule (degreeZero R S)) (p c : ℤ)
    (y : (degreeZeroComplex (A := A) M).X p) :
    (c • y : M.grading p).val = c • (y : M.grading p).val := rfl

/-- A unit of `ℤ` acting on a morphism of modules acts on its values. -/
theorem units_smul_hom_apply {X Y : ModuleCat.{u} A} (u : ℤˣ) (f : X ⟶ Y) (x : X) :
    (u • f).hom x = (u : ℤ) • f.hom x := rfl

/-- The degree-`i` term of the complex of homogeneous components of `M[k]` is the degree-`i` term
of the `k`-th shift of the complex of homogeneous components of `M`. -/
theorem degreeZeroComplex_shift_X_eq (M : DifferentialGradedModule (degreeZero R S)) (k i : ℤ) :
    (degreeZeroComplex (A := A) (shift M k)).X i =
      ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) k).obj
        (degreeZeroComplex (A := A) M)).X i := rfl

/-- The differential of the shifted complex of homogeneous components, read through the unshifted
differential graded module. -/
theorem degreeZeroComplex_shiftCochain_d_val (M : DifferentialGradedModule (degreeZero R S))
    (k i : ℤ) (x : (degreeZeroComplex (A := A) M).X (i + k)) :
    ((k.negOnePow • (degreeZeroComplex (A := A) M).d (i + k) (i + 1 + k)).hom x :
        M.grading (i + 1 + k)).val =
      (k.negOnePow : ℤ) • M.d (x : M.grading (i + k)).val := by
  rw [units_smul_hom_apply, degreeZeroComplex_zsmul_val,
    degreeZeroComplex_d_val (A := A) M (show i + k + 1 = i + 1 + k by omega)]

/-- The differential of the complex of homogeneous components of the shifted differential graded
module, read through the unshifted module. -/
theorem degreeZeroComplex_shiftModule_d_val (M : DifferentialGradedModule (degreeZero R S))
    (k i : ℤ) (y : (degreeZeroComplex (A := A) (shift M k)).X i) :
    (((degreeZeroComplex (A := A) (shift M k)).d i (i + 1)).hom y :
        (shift M k).grading (i + 1)).val =
      (k.negOnePow : ℤ) • M.d (y : (shift M k).grading i).val := by
  rw [degreeZeroComplex_d_val (A := A) (shift M k) rfl]
  rfl

/-- **The complex of homogeneous components of a shifted differential graded module is the shift
of the complex of homogeneous components.** Both shifts reindex the degrees by `n ↦ n + k` and
multiply the differential by `(-1)^k`, so the comparison is the identity on every component. -/
def degreeZeroComplexShiftIso (M : DifferentialGradedModule (degreeZero R S)) (k : ℤ) :
    degreeZeroComplex (A := A) (shift M k) ≅
      (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) k).obj
        (degreeZeroComplex (A := A) M) := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => eqToIso (degreeZeroComplex_shift_X_eq (A := A) M k i)) ?_
  rintro i _ rfl
  exact ModuleCat.hom_ext <| LinearMap.ext fun x => Subtype.ext <|
    (degreeZeroComplex_shiftCochain_d_val (A := A) M k i x).trans
      (degreeZeroComplex_shiftModule_d_val (A := A) M k i x).symm

/-- The comparison of the shift with the homogeneous-components functor, natural in the
differential graded module. -/
def degreeZeroComponentShiftNatIso (k : ℤ) :
    CategoryTheory.shiftFunctor (DifferentialGradedModule (degreeZero R S)) k ⋙
        degreeZeroComponentFunctor R A ≅
      degreeZeroComponentFunctor R A ⋙
        CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{u} A) ℤ) k :=
  NatIso.ofComponents (fun M => degreeZeroComplexShiftIso (A := A) M k) (by
    intro M N f
    ext i x
    rfl)

/-- **The homogeneous-components functor commutes with the shift.** -/
instance degreeZeroComponentFunctor_commShift :
    (degreeZeroComponentFunctor R A).CommShift ℤ where
  commShiftIso := degreeZeroComponentShiftNatIso
  commShiftIso_zero := by
    ext M n x
    rw [Functor.CommShift.isoZero_hom_app]
    exact Subtype.ext (degreeZeroComplex_eqToHom_val (A := A) M (add_zero n).symm
      ((shiftZeroHom (degreeZero R S) M).gradedMap n x)).symm
  commShiftIso_add a b := by
    ext M n x
    rw [Functor.CommShift.isoAdd_hom_app]
    exact Subtype.ext (degreeZeroComplex_eqToHom_val (A := A) M
      (show n + b + a = n + (a + b) by omega)
      ((shiftAddHom (degreeZero R S) M a b).gradedMap n x)).symm

end DifferentialGradedModule

end
