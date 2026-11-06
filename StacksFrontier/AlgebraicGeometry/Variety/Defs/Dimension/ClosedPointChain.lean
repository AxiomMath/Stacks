module

public import Mathlib.AlgebraicGeometry.Morphisms.Finite
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ImmediateSpecialization
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ResidueField
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.SpecializationTrdeg
public import StacksFrontier.Topology.Dimension.DimensionFunctionDifference

/-!
# A chain of immediate specializations down to a closed point

Let `X` be a scheme locally of finite type over a field `k` and let `x` be a point of `X`. The
transcendence degree `trdeg_k κ(x)` of the residue field at `x` is finite, and as a function of
`x` it is a dimension function on the underlying topological space of `X`: it drops strictly
along every nontrivial specialization and by exactly one along every immediate specialization.
Consequently, starting at `x` one can walk down a chain of immediate specializations

`x = c 0 ⤳ c 1 ⤳ ⋯ ⤳ c d`

of length exactly `d = trdeg_k κ(x)`, whose final term is a closed point of `X`.

Both ends of the walk are controlled by the transcendence degree. At a closed point the residue
field is a finite extension of `k`, so the degree is zero; conversely a point of degree zero
admits no nontrivial specialization, since the degree would have to drop below zero, and so is
closed. In between, a point of positive degree is not closed, hence admits a nontrivial
specialization, which by the dimension-function property begins with an immediate one.

## Main definitions

* `AlgebraicGeometry.natTrdegResidueField` is `trdeg_k κ(x)` as a natural number.
* `AlgebraicGeometry.residueFieldTrdegDimensionFunction` packages it as a
  `TopologicalSpace.DimensionFunction`.

## Main results

* `AlgebraicGeometry.natTrdegResidueField_eq_zero_of_isClosed` and
  `AlgebraicGeometry.isClosed_singleton_of_natTrdegResidueField_eq_zero`: degree zero and
  closedness are equivalent.
* `AlgebraicGeometry.exists_chain_isImmediateSpecialization_isClosed`: the chain of immediate
  specializations from `x` to a closed point, of length `trdeg_k κ(x)`.

## Implementation notes

A locally algebraic `k`-scheme is represented by its structure morphism to `Spec k` together
with a `LocallyOfFiniteType` instance, and the `k`-algebra structure on a residue field is the
canonical composite through global sections and evaluation, as elsewhere in this development.
Transcendence degree is cardinal-valued, so `Cardinal.toNat` is used throughout; this is
harmless because the degrees occurring here are finite, by
`AlgebraicGeometry.residueField_finTrdeg`.

A chain of length `d` is a function `Fin (d + 1) → X`, and the `d` steps are indexed by
`Fin d` through `Fin.castSucc` and `Fin.succ`, as for `RelSeries`.

The identification of the degree at a closed point with zero isolates a step of the proof of
`AlgebraicGeometry.topologicalKrullDimAt_eq_krullDimOfRing_stalk`, where it appears only inside
the proof.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
  [LocallyOfFiniteType f]

/-- The transcendence degree over `k` of the residue field at a point of a scheme locally of
finite type over `k`, as a natural number. -/
noncomputable def natTrdegResidueField (x : X) : ℕ :=
  letI : Algebra k (X.residueField x) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
  Cardinal.toNat (Algebra.trdeg k (X.residueField x))

/-- The `k`-algebra structure on the residue field at `x`, through global sections. -/
private noncomputable abbrev residueFieldAlgebra (x : X) : Algebra k (X.residueField x) :=
  ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra

/-- The residue-field transcendence degree drops strictly along a nontrivial specialization. -/
theorem natTrdegResidueField_lt_of_specializes {x x' : X} (hxx' : x ⤳ x') (hne : x ≠ x') :
    natTrdegResidueField k X f x' < natTrdegResidueField k X f x := by
  let := residueFieldAlgebra k X f x
  let := residueFieldAlgebra k X f x'
  let : FinTrdeg k (X.residueField x) := residueField_finTrdeg k f x
  exact Cardinal.toNat_lt_toNat
    (trdeg_residueField_lt_of_specialization k X f hxx' hne) (trdeg_lt_aleph0 k _)

/-- The residue-field transcendence degree drops by exactly one along an immediate
specialization. -/
theorem natTrdegResidueField_eq_add_one_of_isImmediateSpecialization {x x' : X}
    (h : IsImmediateSpecialization x x') :
    natTrdegResidueField k X f x = natTrdegResidueField k X f x' + 1 := by
  let := residueFieldAlgebra k X f x
  let := residueFieldAlgebra k X f x'
  let : FinTrdeg k (X.residueField x') := residueField_finTrdeg k f x'
  have h1 := trdeg_residueField_eq_add_one_of_isImmediateSpecialization k X f h
  change Cardinal.toNat (Algebra.trdeg k (X.residueField x)) =
    Cardinal.toNat (Algebra.trdeg k (X.residueField x')) + 1
  rw [h1, Cardinal.toNat_add (trdeg_lt_aleph0 k _) Cardinal.one_lt_aleph0]
  simp

/-- The residue-field transcendence degree is a dimension function on a scheme locally of finite
type over a field. -/
noncomputable def residueFieldTrdegDimensionFunction : DimensionFunction X where
  toFun x := (natTrdegResidueField k X f x : ℤ)
  strictAnti_specializes := by
    intro x x' hxy hne
    exact_mod_cast natTrdegResidueField_lt_of_specializes k X f hxy hne
  step_immediate := by
    intro x x' h
    have := natTrdegResidueField_eq_add_one_of_isImmediateSpecialization k X f h
    omega

/-- At a closed point of a scheme locally of finite type over a field the residue field is a
finite extension of the base field, so its transcendence degree vanishes. -/
theorem natTrdegResidueField_eq_zero_of_isClosed (x : X) (hx : IsClosed ({x} : Set X)) :
    natTrdegResidueField k X f x = 0 := by
  let := residueFieldAlgebra k X f x
  let : LocallyOfFiniteType (X.fromSpecResidueField x) := by
    have := isClosed_singleton_iff_isClosedImmersion.mp hx; infer_instance
  have hcomp : LocallyOfFiniteType (X.fromSpecResidueField x ≫ f) := inferInstance
  rw [← f.SpecMap_residueFieldMap_fromSpecResidueField x] at hcomp
  simp only [Scheme.fromSpecResidueField, Spec.fromSpecStalk_eq, Spec.map_comp] at hcomp
  simp only [← Spec.map_comp] at hcomp
  change LocallyOfFiniteType (Spec.map _) at hcomp
  rw [AlgebraicGeometry.HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)] at hcomp
  let : Algebra.FiniteType k (X.residueField x) := by
    change RingHom.FiniteType (algebraMap k (X.residueField x))
    convert hcomp using 1
    simp only [RingHom.algebraMap_toAlgebra]
    rw [← Scheme.Γevaluation_naturality]
    simp only [Scheme.Γevaluation, Scheme.evaluation, Category.assoc]
  let : Module.Finite k (X.residueField x) := finite_of_finite_type_of_isJacobsonRing _ _
  let : Algebra.IsAlgebraic k (X.residueField x) := Algebra.IsAlgebraic.of_finite _ _
  change Cardinal.toNat (Algebra.trdeg k (X.residueField x)) = 0
  exact Cardinal.toNat_eq_zero.mpr (Or.inl trdeg_eq_zero)

/-- A point admitting no nontrivial specialization is closed. -/
private theorem isClosed_singleton_of_forall_specializes {Y : Type*} [TopologicalSpace Y]
    (y : Y) (h : ∀ z : Y, y ⤳ z → y = z) : IsClosed ({y} : Set Y) := by
  rw [← closure_eq_iff_isClosed]
  refine subset_antisymm (fun z hz ↦ ?_) subset_closure
  exact Set.mem_singleton_iff.mpr (h z (specializes_iff_mem_closure.mpr hz)).symm

/-- A point of a scheme locally of finite type over a field whose residue-field transcendence
degree vanishes is closed: a nontrivial specialization would make the degree drop below zero. -/
theorem isClosed_singleton_of_natTrdegResidueField_eq_zero (x : X)
    (hx : natTrdegResidueField k X f x = 0) : IsClosed ({x} : Set X) := by
  refine isClosed_singleton_of_forall_specializes x fun z hz ↦ ?_
  by_contra hne
  have := natTrdegResidueField_lt_of_specializes k X f hz hne
  omega

/-- From a point of positive residue-field transcendence degree there is an immediate
specialization, and it drops the degree by one. -/
private theorem exists_isImmediateSpecialization_of_pos (x : X)
    (hx : 0 < natTrdegResidueField k X f x) :
    ∃ z : X, IsImmediateSpecialization x z ∧
      natTrdegResidueField k X f z + 1 = natTrdegResidueField k X f x := by
  have hnot : ¬ IsClosed ({x} : Set X) := fun hcl ↦ by
    have := natTrdegResidueField_eq_zero_of_isClosed k X f x hcl
    omega
  obtain ⟨w, hw, hwne⟩ : ∃ w : X, x ⤳ w ∧ x ≠ w := by
    by_contra hcon
    refine hnot (isClosed_singleton_of_forall_specializes x fun z hz ↦ ?_)
    by_contra hne
    exact hcon ⟨z, hz, hne⟩
  obtain ⟨z, hz, -⟩ :=
    (residueFieldTrdegDimensionFunction k X f).exists_isImmediateSpecialization hw hwne
  exact ⟨z, hz, by
    have := natTrdegResidueField_eq_add_one_of_isImmediateSpecialization k X f hz
    omega⟩

/-- The chain of immediate specializations of prescribed length, by induction on that length. -/
private theorem exists_chain_aux (n : ℕ) :
    ∀ x : X, natTrdegResidueField k X f x = n →
      ∃ c : Fin (n + 1) → X, c 0 = x ∧
        (∀ i : Fin n, IsImmediateSpecialization (c i.castSucc) (c i.succ)) ∧
        natTrdegResidueField k X f (c (Fin.last n)) = 0 := by
  induction n with
  | zero => exact fun x hx ↦ ⟨fun _ ↦ x, rfl, fun i ↦ i.elim0, hx⟩
  | succ n ih =>
    intro x hx
    obtain ⟨z, hz, hzn⟩ := exists_isImmediateSpecialization_of_pos k X f x (by omega)
    obtain ⟨c, hc0, hcstep, hclast⟩ := ih z (by omega)
    refine ⟨Fin.cons x c, rfl, ?_, ?_⟩
    · refine Fin.cases ?_ ?_
      · simpa only [Fin.castSucc_zero, Fin.cons_zero, Fin.cons_succ, hc0] using hz
      · intro j
        simpa only [← Fin.succ_castSucc, Fin.cons_succ] using hcstep j
    · simpa only [← Fin.succ_last, Fin.cons_succ] using hclast

/-- **The chain of immediate specializations down to a closed point.** On a scheme locally of
finite type over a field, every point `x` is the head of a chain of `trdeg_k κ(x)` immediate
specializations whose final term is a closed point. -/
theorem exists_chain_isImmediateSpecialization_isClosed (x : X) :
    ∃ c : Fin (natTrdegResidueField k X f x + 1) → X, c 0 = x ∧
      (∀ i : Fin (natTrdegResidueField k X f x),
        IsImmediateSpecialization (c i.castSucc) (c i.succ)) ∧
      IsClosed ({c (Fin.last (natTrdegResidueField k X f x))} : Set X) := by
  obtain ⟨c, hc0, hcstep, hclast⟩ := exists_chain_aux k X f _ x rfl
  exact ⟨c, hc0, hcstep, isClosed_singleton_of_natTrdegResidueField_eq_zero k X f _ hclast⟩

end AlgebraicGeometry

end
