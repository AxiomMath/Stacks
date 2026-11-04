module

public import Mathlib.Algebra.Colimit.DirectLimit
public import StacksFrontier.AlgebraicGeometry.IntegralDirectedColimit.Basic

/-!
# An integral algebra is a directed colimit of finite, finitely presented algebras

Let `R → S` be an integral ring map. The file
`StacksFrontier/AlgebraicGeometry/IntegralDirectedColimit/Basic.lean` built a directed family
`obj i` of `R`-algebras, indexed by `Index R S`, each of which is a finite `R`-module and of
finite presentation over `R`. This file turns that family into a directed system and
identifies its direct limit with `S`:

* `Stacks.RingTheory.IntegralColimit.equivS : colim R S ≃ₐ[R] S`.

This is the commutative-algebra content of [Stacks, Tag 0817], i.e. the statement that tag 0817
asserts for a quasi-coherent algebra on a scheme, read on a single affine open. Tag 0817
itself is a statement about sheaves of algebras and is not proved here; passing to it also needs
[Stacks, Tag 05JT], for the directedness of the finite type quasi-coherent subalgebras.

## The two halves of the colimit statement

A filtered cocone of rings is colimiting exactly when it is jointly surjective and when
everything that dies in the colimit already dies at a finite stage. Both are immediate from
the shape of the index:

* joint surjectivity holds because `y : S` is the image of the variable `X y` in the algebra at
  the index `Index.singleton R S y`, which has `y` as its only variable;
* an element of `obj i` dying in `S` is the class of some `a` in the subalgebra with
  `eval R S a = 0`, and adjoining `a` to the prescribed relations of `i` produces a larger index
  at which the class of `a` is zero.

## Main definitions

* `Stacks.RingTheory.IntegralColimit.system`: the transition maps of the approximating system.
* `Stacks.RingTheory.IntegralColimit.colim`: the direct limit of the system.
* `Stacks.RingTheory.IntegralColimit.toS` and
  `Stacks.RingTheory.IntegralColimit.liftToS`: the maps from the approximating algebras to `S`,
  and the induced map out of the direct limit.

## Main results

* `Stacks.RingTheory.IntegralColimit.instDirectedSystem`: the family is a directed system.
* `Stacks.RingTheory.IntegralColimit.liftToS_surjective` and
  `Stacks.RingTheory.IntegralColimit.liftToS_injective`: the two halves above.
* `Stacks.RingTheory.IntegralColimit.equivS`: the direct limit is `S`.

## Implementation notes

`Mathlib.Algebra.Colimit.DirectLimit` is the colimit of a directed system in the category of
`R`-algebras, with an explicit description of when two elements of components become equal, so
`equivS` is exactly the assertion that `S` is the directed colimit of the system.

`system` is a plain `def` rather than an `abbrev`: declaring it reducibly makes the
`DirectedSystem` instance unfindable at its use sites, because the instance is keyed on the
unfolded transition map instead of on `system`. For the same reason the arguments of
`DirectLimit.Algebra.lift` are supplied explicitly in `liftToS`; left as underscores, the
`DirectedSystem` instance is searched for before the expected type has pinned the system down.

`liftToS_injective` is proved on a difference `a - b` rather than through
`injective_iff_map_eq_zero`: synthesising `AddGroup (colim R S)` exceeds the default
instance-search budget, although `CommRing (colim R S)` is found.

## References

* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
* [Stacks Project, Tag 086N](https://stacks.math.columbia.edu/tag/086N)
-/

@[expose] public section

noncomputable section

open MvPolynomial

universe u v

namespace Stacks.RingTheory.IntegralColimit

variable (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
  [Algebra.IsIntegral R S]

/-- The transition map of the approximating system: for `i ≤ j`, the map induced on quotients
by the inclusion of the subalgebra at `i` into the subalgebra at `j`. -/
def system (i j : Index R S) (h : i ≤ j) : obj i →ₐ[R] obj j :=
  Ideal.Quotient.liftₐ _
    ((Ideal.Quotient.mkₐ R (relIdeal j)).comp (Subalgebra.inclusion (subalg_mono h)))
    (fun a ha => by
      have key : relIdeal i ≤ RingHom.ker (((Ideal.Quotient.mkₐ R (relIdeal j)).comp
          (Subalgebra.inclusion (subalg_mono h))) : subalg i →+* obj j) := by
        rw [relIdeal, Ideal.span_le]
        intro b hb
        simp only [SetLike.mem_coe, RingHom.mem_ker]
        change Ideal.Quotient.mk (relIdeal j) (Subalgebra.inclusion (subalg_mono h) b) = 0
        exact mk_eq_zero_of_mem_gens _ (gens_mono h hb)
      exact key ha)

/-- The transition map sends the class of `a` to the class of `a`. -/
@[simp] theorem system_mk {i j : Index R S} (h : i ≤ j) (a : subalg i) :
    system R S i j h (Ideal.Quotient.mk (relIdeal i) a) =
      Ideal.Quotient.mk (relIdeal j) (Subalgebra.inclusion (subalg_mono h) a) := rfl

/-- The approximating algebras with the transition maps `system` form a directed system. -/
instance : DirectedSystem (fun i : Index R S => obj i) (system R S · · · ·) where
  map_self i x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl
  map_map k j i hij hjk x := by
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rfl

/-- The direct limit of the approximating system. -/
abbrev colim : Type (max u v) := DirectLimit (fun i : Index R S => obj i) (system R S)

variable {R S}

/-- Two classes in `obj i` already agree at an index `j ≥ i` whose relations contain the
difference of their representatives. -/
theorem system_mk_eq_system_mk {i j : Index R S} (h : i ≤ j) (a b : subalg i)
    (hsub : (a : MvPolynomial S R) - (b : MvPolynomial S R) ∈ gens j) :
    system R S i j h (Ideal.Quotient.mk (relIdeal i) a)
      = system R S i j h (Ideal.Quotient.mk (relIdeal i) b) := by
  rw [system_mk, system_mk, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  exact Ideal.subset_span hsub

/-- The map to `S` out of the approximating algebra at the index `i`: evaluation of
polynomials, which kills the relations because they hold in `S`. -/
def toS (i : Index R S) : obj i →ₐ[R] S :=
  Ideal.Quotient.liftₐ _ ((eval R S).comp (subalg i).val) (fun a ha => by
    have key : relIdeal i ≤ RingHom.ker (((eval R S).comp (subalg i).val) : subalg i →+* S) := by
      rw [relIdeal, Ideal.span_le]
      intro b hb
      simp only [SetLike.mem_coe, RingHom.mem_ker]
      exact eval_eq_zero_of_mem_gens hb
    exact key ha)

/-- `toS i` sends the class of `a` to the evaluation of `a`. -/
@[simp] theorem toS_mk (i : Index R S) (a : subalg i) :
    toS i (Ideal.Quotient.mk (relIdeal i) a) = eval R S a := rfl

/-- The maps `toS` are compatible with the transition maps. -/
theorem toS_system {i j : Index R S} (h : i ≤ j) (x : obj i) :
    toS j (system R S i j h x) = toS i x := by
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  rw [system_mk, toS_mk, toS_mk, Subalgebra.coe_inclusion]

variable (R S)

/-- The map from the direct limit of the approximating system to `S`. -/
def liftToS : colim R S →ₐ[R] S :=
  DirectLimit.Algebra.lift (fun i : Index R S => obj i) (system R S) S toS
    fun _ _ h x => toS_system h x

/-- The approximating system covers `S`: every element of `S` is already in the image of the
algebra indexed by the single variable naming it. -/
theorem liftToS_surjective : Function.Surjective (liftToS R S) := fun y =>
  ⟨DirectLimit.Algebra.of (fun i : Index R S => obj i) (system R S) (Index.singleton R S y)
    (Ideal.Quotient.mk _ ⟨X y, X_mem_varSubalg R S rfl⟩), eval_X R S y⟩

/-- Nothing extra is identified in `S`: two classes with the same image already agree at a
larger index, obtained by adjoining the difference of their representatives to the prescribed
relations. -/
theorem liftToS_injective : Function.Injective (liftToS R S) := by
  intro z w
  induction z, w using DirectLimit.induction₂ with
  | _ i x y =>
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective y
    intro hzw
    have hab : eval R S ((a : MvPolynomial S R) - (b : MvPolynomial S R)) = 0 := by
      rw [map_sub, sub_eq_zero]
      exact hzw
    have hmem : ∀ g ∈ i.1.2 ∪ {(a : MvPolynomial S R) - (b : MvPolynomial S R)},
        g ∈ varSubalg R S i.1.1 ∧ eval R S g = 0 := by
      rintro g (hg | rfl)
      · exact i.2.2.2 g hg
      · exact ⟨sub_mem a.2 b.2, hab⟩
    refine Quotient.sound ⟨⟨(i.1.1, i.1.2 ∪ {(a : MvPolynomial S R) - (b : MvPolynomial S R)}),
      i.2.1, i.2.2.1.union (Set.finite_singleton _), hmem⟩,
      ⟨subset_rfl, Set.subset_union_left⟩, ⟨subset_rfl, Set.subset_union_left⟩,
      system_mk_eq_system_mk _ a b (Or.inl (Set.mem_union_right _ rfl))⟩

/-- **An integral algebra is the directed colimit of its finite, finitely presented
approximations.** The direct limit of the system of `Basic.lean` -- every member of which is a
finite `R`-module by `moduleFinite_obj` and of finite presentation over `R` by
`finitePresentation_obj` -- is `S` itself.

This is the commutative-algebra content of [Stacks, Tag 0817], read on an affine open. -/
def equivS : colim R S ≃ₐ[R] S :=
  AlgEquiv.ofBijective (liftToS R S) ⟨liftToS_injective R S, liftToS_surjective R S⟩

/-- `equivS` is `liftToS`. -/
@[simp] theorem equivS_apply (z : colim R S) : equivS R S z = liftToS R S z := rfl

end Stacks.RingTheory.IntegralColimit

end
