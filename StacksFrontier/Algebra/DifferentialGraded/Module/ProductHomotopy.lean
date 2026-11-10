module

public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyLifting

/-! # Maps into a product of differential graded modules

The product of a family `(Q i)` of right differential graded `A`-modules is not the product of
the underlying modules: the category is one of *graded* modules, so the product is formed
degreewise, `(∏ Q)ⁿ = ∏ᵢ (Q i)ⁿ`, and the product object is the direct sum of these. This file
works with a product presented as *data* — the projections, assumed jointly injective and
degreewise jointly surjective — and proves the two things the property-(I) material needs: that
a family of maps into the factors lifts to a map into the product, and that a product of modules
orthogonal on the right to the acyclic modules is orthogonal on the right to them.

The second is the form in which the graded pieces of a property-(I) filtration — products of
shifts of `A^∨` — are recognised as orthogonal, and it is the dual of
`StacksFrontier/Algebra/DifferentialGraded/Module/DirectSumHomotopy.lean`.

## Main results

* `DifferentialGradedModule.exists_productLift`: a family of maps into the factors, all shifting
  the degree by the same amount, lifts to a map into the product. This is the single
  construction from which all three liftings below are obtained.
* `DifferentialGradedModule.exists_homLift` and `exists_gradedHomLift`: the cases of a family of
  homomorphisms and of a family of graded homomorphisms.
* `DifferentialGradedModule.rightOrthogonal_acyclic_of_product`: a differential graded module
  presented as a product of modules orthogonal on the right to the acyclic modules is itself
  orthogonal on the right to them.

## Implementation notes

The presentation is taken as data rather than as a universal property, as on the direct-sum
side. It is *not* an `A`-linear equivalence of `P.M` with `∀ i, (Q i).M`, because the product
here is formed degreewise, so `P.M` is in general a proper submodule of the cartesian product of
the `(Q i).M`, namely the part of it with finite graded support. What survives of the
equivalence is exactly the two hypotheses used below:

* `hsep`, that the projections are jointly injective, which is the injectivity of the comparison
  map into the cartesian product;
* `hlift`, that a family of homogeneous elements of a common degree `n` is the family of
  components of a homogeneous element of degree `n`, which is its surjectivity in each degree.

Compared with the direct-sum side the homogeneity hypothesis runs the other way. There one needs
the presentation to *reflect* componentwise homogeneity, in order to bound each component
homotopy; here one needs it to *establish* homogeneity of the assembled element, since that
element is what is being constructed. Both directions hold for the graded product, so this is a
matter of asking for the right one.

`exists_productLift` produces a bare function together with its laws rather than a bundled
linear map, because its clients bundle it differently: as a `Hom` — which needs in addition
compatibility with the differentials, proved by the client from joint injectivity — as a
`GradedHom`, and as the underlying map of a `Homotopy`. The finiteness that makes the assembly
work is the grading of the *source*: an element of it is a finite sum of homogeneous ones, and
the lift is performed on each homogeneous piece, where `hlift` applies.

As everywhere in this chapter's differential graded interface, the base ring, the algebra and
the modules all live in a single universe `u`, following Stacks Tag 09JJ.
The index type of a product is in a universe of its own, since the two products that occur in
the property-(I) material are indexed differently: the graded pieces of a filtration are
products over an index type in `Type u`, while the telescope of Tag 09KR is a product over `ℕ`.

## References

* [Stacks Project, Tag 09KS](https://stacks.math.columbia.edu/tag/09KS), in whose proof the
  graded pieces of a property-(I) filtration are products of shifts of `A^∨`, and
  [Tag 09KR](https://stacks.math.columbia.edu/tag/09KR), whose telescope is built out of such a
  product.
-/

@[expose] public section

open CategoryTheory MulOpposite

universe u v

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] {A : DifferentialGradedAlgebra R}
  {ι : Type v} {Q : ι → DifferentialGradedModule A} {P : DifferentialGradedModule A}

section Lift

variable (π : ∀ i, P ⟶ Q i)
  (hsep : ∀ y : P.M, (∀ i, (π i).toFun y = 0) → y = 0)
  (hlift : ∀ (n : ℤ) (q : ∀ i, (Q i).M), (∀ i, q i ∈ (Q i).grading n) →
    ∃ y ∈ P.grading n, ∀ i, (π i).toFun y = q i)

include hsep in
/-- An element of a product is determined by its components. -/
theorem eq_of_proj_eq {y y' : P.M} (h : ∀ i, (π i).toFun y = (π i).toFun y') : y = y' := by
  have := hsep (y - y') fun i => by rw [map_sub, h i, sub_self]
  rwa [sub_eq_zero] at this

include hsep hlift in
/-- **Lifting a family of maps into a product.** Given maps into the factors that are additive,
compatible with the two actions, and all raising the degree by the same amount `c`, there is a
map into the product with the same four properties whose components they are. -/
theorem exists_productLift {T : DifferentialGradedModule A} (c : ℤ) (φ : ∀ i, T.M → (Q i).M)
    (hadd : ∀ (i : ι) (x y : T.M), φ i (x + y) = φ i x + φ i y)
    (hsmulR : ∀ (i : ι) (r : R) (x : T.M), φ i (r • x) = r • φ i x)
    (hsmulA : ∀ (i : ι) (a : A.A) (x : T.M), φ i (op a • x) = op a • φ i x)
    (hgr : ∀ (i : ι) (n : ℤ) (x : T.M), x ∈ T.grading n → φ i x ∈ (Q i).grading (n + c)) :
    ∃ ψ : T.M → P.M,
      (∀ x y : T.M, ψ (x + y) = ψ x + ψ y) ∧
      (∀ (r : R) (x : T.M), ψ (r • x) = r • ψ x) ∧
      (∀ (a : A.A) (x : T.M), ψ (op a • x) = op a • ψ x) ∧
      (∀ (n : ℤ) (x : T.M), x ∈ T.grading n → ψ x ∈ P.grading (n + c)) ∧
      (∀ (i : ι) (x : T.M), (π i).toFun (ψ x) = φ i x) := by
  classical
  have hzero : ∀ i : ι, φ i 0 = 0 := by
    intro i
    have h := hadd i 0 0
    rw [add_zero] at h
    have h' : φ i 0 + 0 = φ i 0 + φ i 0 := by rw [add_zero]; exact h
    exact (add_left_cancel h').symm
  have hex : ∀ x : T.M, ∃ y : P.M, ∀ i, (π i).toFun y = φ i x := by
    intro x
    induction x using DirectSum.Decomposition.inductionOn T.grading with
    | zero => exact ⟨0, fun i => by rw [map_zero, hzero i]⟩
    | @homogeneous n x =>
        obtain ⟨y, _, hy⟩ := hlift (n + c) (fun i => φ i (x : T.M))
          (fun i => hgr i n (x : T.M) x.2)
        exact ⟨y, hy⟩
    | add x x' hx hx' =>
        obtain ⟨y, hy⟩ := hx
        obtain ⟨y', hy'⟩ := hx'
        exact ⟨y + y', fun i => by rw [map_add, hy i, hy' i, hadd i x x']⟩
  refine ⟨fun x => (hex x).choose, ?_, ?_, ?_, ?_, fun i x => (hex x).choose_spec i⟩
  · intro x y
    refine eq_of_proj_eq π hsep fun i => ?_
    rw [(hex (x + y)).choose_spec i, map_add, (hex x).choose_spec i, (hex y).choose_spec i,
      hadd i x y]
  · intro r x
    refine eq_of_proj_eq π hsep fun i => ?_
    rw [(hex (r • x)).choose_spec i, map_smul, (hex x).choose_spec i, hsmulR i r x]
  · intro a x
    refine eq_of_proj_eq π hsep fun i => ?_
    rw [(hex (op a • x)).choose_spec i, (π i).map_smul, (hex x).choose_spec i, hsmulA i a x]
  · intro n x hx
    change (hex x).choose ∈ P.grading (n + c)
    obtain ⟨y, hymem, hy⟩ := hlift (n + c) (fun i => φ i x) (fun i => hgr i n x hx)
    rw [show (hex x).choose = y from
      eq_of_proj_eq π hsep fun i => by rw [(hex x).choose_spec i, hy i]]
    exact hymem

/-- A family of graded homomorphisms into the factors lifts to a graded homomorphism. -/
private theorem exists_gradedHomLift_aux
    (hsep : ∀ y : P.M, (∀ i, (π i).toFun y = 0) → y = 0)
    (hlift : ∀ (n : ℤ) (q : ∀ i, (Q i).M), (∀ i, q i ∈ (Q i).grading n) →
      ∃ y ∈ P.grading n, ∀ i, (π i).toFun y = q i)
    {T : DifferentialGradedModule A} (φ : ∀ i, GradedHom T (Q i)) :
    ∃ ψ : GradedHom T P, ∀ (i : ι) (x : T.M), (π i).toFun (ψ.toFun x) = (φ i).toFun x := by
  obtain ⟨ψ, hadd, hsmulR, hsmulA, hgr, hπ⟩ :=
    exists_productLift π hsep hlift 0 (fun i => (φ i).toFun)
      (fun i x y => map_add _ x y) (fun i r x => map_smul _ r x)
      (fun i a x => (φ i).map_smul x a)
      (fun i n x hx => by rw [add_zero]; exact (φ i).map_grading n x hx)
  exact ⟨{
    toFun := { toFun := ψ, map_add' := hadd, map_smul' := hsmulR }
    map_smul := fun x a => hsmulA a x
    map_grading := fun n x hx => by simpa using hgr n x hx }, hπ⟩

include hsep hlift in
/-- **Lifting a family of homomorphisms into a product.** The lift commutes with the
differentials because its components do and an element of the product is determined by its
components. -/
theorem exists_homLift {T : DifferentialGradedModule A} (φ : ∀ i, T ⟶ Q i) :
    ∃ ψ : T ⟶ P, ∀ (i : ι) (x : T.M), (π i).toFun (ψ.toFun x) = (φ i).toFun x := by
  obtain ⟨ψ, hπ⟩ : ∃ ψ : GradedHom T P, ∀ (i : ι) (x : T.M),
      (π i).toFun (ψ.toFun x) = (φ i).toFun x :=
    exists_gradedHomLift_aux π hsep hlift fun i => (φ i).toGradedHom
  refine ⟨{ ψ with map_d := ?_ }, hπ⟩
  refine LinearMap.ext fun x => eq_of_proj_eq π hsep fun i => ?_
  change (π i).toFun (ψ.toFun (T.d x)) = (π i).toFun (P.d (ψ.toFun x))
  rw [hπ i (T.d x), ← LinearMap.comp_apply, (φ i).map_d, LinearMap.comp_apply,
    ← hπ i x, ← LinearMap.comp_apply, ← (π i).map_d, LinearMap.comp_apply]

include hsep hlift in
/-- **Lifting a family of graded homomorphisms into a product.** -/
theorem exists_gradedHomLift {T : DifferentialGradedModule A} (φ : ∀ i, GradedHom T (Q i)) :
    ∃ ψ : GradedHom T P, ∀ (i : ι) (x : T.M), (π i).toFun (ψ.toFun x) = (φ i).toFun x :=
  exists_gradedHomLift_aux π hsep hlift φ

end Lift

/-- A differential graded module presented as a product of modules orthogonal on the right to
the acyclic differential graded modules is itself orthogonal on the right to them.

The presentation is the family of projections `π i : P ⟶ Q i`, assumed jointly injective
(`hsep`) and degreewise jointly surjective (`hlift`). -/
theorem rightOrthogonal_acyclic_of_product (π : ∀ i, P ⟶ Q i)
    (hsep : ∀ y : P.M, (∀ i, (π i).toFun y = 0) → y = 0)
    (hlift : ∀ (n : ℤ) (q : ∀ i, (Q i).M), (∀ i, q i ∈ (Q i).grading n) →
      ∃ y ∈ P.grading n, ∀ i, (π i).toFun y = q i)
    (hQ : ∀ i, (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj (Q i))) :
    (acyclic' A).rightOrthogonal ((toHomotopyCategory A).obj P) := by
  classical
  rw [rightOrthogonal_acyclic_iff]
  intro N hN f
  -- a null-homotopy of each component
  have h : ∀ i, Homotopy (f ≫ π i) 0 :=
    fun i => ((rightOrthogonal_acyclic_iff (Q i)).1 (hQ i) N hN (f ≫ π i)).some
  -- their assembly over the product, a degree `-1` map into `P`
  obtain ⟨H, Hadd, _, HsmulA, Hgr, Hπ⟩ :=
    exists_productLift π hsep hlift (-1) (fun i => (h i).toLinearMap)
      (fun i x y => map_add _ x y)
      (fun i r x => by
        rw [show (r : R) • x = (algebraMap R (MulOpposite A.A) r) • x from
          (IsScalarTower.algebraMap_smul _ r x).symm, map_smul,
          IsScalarTower.algebraMap_smul])
      (fun i a x => map_smul _ (op a) x)
      (fun i n x hx => by
        rw [show n + (-1 : ℤ) = n - 1 from by ring]
        exact (h i).map_grading n x hx)
  refine ⟨{
    toLinearMap :=
      { toFun := H
        map_add' := Hadd
        map_smul' := fun c x => by
          rw [← MulOpposite.op_unop c]
          exact HsmulA c.unop x }
    map_grading := fun n x hx => by
      have hh := Hgr n x hx
      rwa [show n + (-1 : ℤ) = n - 1 from by ring] at hh
    homotopy_eq := ?_ }⟩
  intro x
  refine eq_of_proj_eq π hsep fun i => ?_
  have hi := (h i).homotopy_eq x
  simp only [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero, Hom.comp_toFun_apply] at hi
  change (π i).toFun (f.toFun x - (0 : N ⟶ P).toFun x)
    = (π i).toFun (P.d (H x) + H (N.d x))
  simp only [Hom.hom_zero_toFun, LinearMap.zero_apply, sub_zero, map_add]
  rw [show (π i).toFun (P.d (H x)) = (Q i).d ((π i).toFun (H x)) from
    LinearMap.congr_fun (π i).map_d _, Hπ, Hπ]
  exact hi

end DifferentialGradedModule

end
