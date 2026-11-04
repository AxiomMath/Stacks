module

public import Mathlib.Order.RelSeries
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.ImmediateSpecialization

/-!
# Length of a maximal specialization chain

For a scheme locally of finite type over a field, the length of a maximal chain of nontrivial
specializations between two distinct specializing points is the difference of the transcendence
degrees of the residue fields at its endpoints: each step of a maximal chain is an immediate
specialization, so it drops the transcendence degree by exactly one.

## Main definitions

* `AlgebraicGeometry.IsMaximalSpecializationChain` expresses that a finite chain of nontrivial
  specializations cannot be refined between two consecutive terms.

## Main results

* `AlgebraicGeometry.length_eq_trdeg_sub_of_maximalSpecializationChain` computes the length of
  such a chain.

## Implementation notes

A finite chain is represented by `RelSeries`, for the relation of nontrivial specialization.
Maximality is expressed in its relative sense between the prescribed endpoints: no point can be
inserted between consecutive terms. Since the transcendence degrees here are finite cardinals,
the formula is stated for their natural-number values.

## References

* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The natural-number transcendence degree over `k` of the residue field at a point of a scheme
over `k`. -/
private noncomputable def natTrdeg (k : Type u) [Field k] (X : Scheme.{u})
    (f : X ⟶ Spec (.of k)) (a : X) : ℕ :=
  letI : Algebra k (X.residueField a) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation a).hom.toAlgebra
  Cardinal.toNat (Algebra.trdeg k (X.residueField a))

/-- A function which drops by one along every step of a chain of nontrivial specializations
takes, at the head of the chain, the value it takes at the last term plus the length. -/
private theorem nat_value_at_last_eq_length_add_nat_value_at_head
    {X : Type*} [TopologicalSpace X]
    (d : X → ℕ)
    (c : RelSeries {p : X × X | p.1 ⤳ p.2 ∧ p.1 ≠ p.2})
    (hd : ∀ i : Fin c.length, d (c i.castSucc) = d (c i.succ) + 1) :
    d c.head = c.length + d c.last := by
  induction c using RelSeries.inductionOn' with
  | singleton a => simp [RelSeries.singleton, RelSeries.head, RelSeries.last]
  | snoc c a ha ih =>
      have ih' := ih (fun i => by
        convert hd ⟨i, by simp⟩ using 1 <;>
          simp [RelSeries.snoc, RelSeries.append, Fin.append, Fin.addCases, Fin.cast] <;>
          congr)
      rw [RelSeries.head_snoc, RelSeries.last_snoc, RelSeries.snoc_length]
      rw [ih']
      have hlast := hd ⟨c.length, by simp⟩
      have hlast' : d c.last = d a + 1 := by
        convert hlast using 1 <;>
          simp [RelSeries.snoc, RelSeries.append, RelSeries.singleton, Fin.append, Fin.addCases,
            Fin.cast]
        congr
      rw [hlast']
      omega

/-- A maximal finite chain of nontrivial specializations is one for which no point can be
inserted between two consecutive terms. -/
def IsMaximalSpecializationChain {X : Type*} [TopologicalSpace X]
    (c : RelSeries {p : X × X | p.1 ⤳ p.2 ∧ p.1 ≠ p.2}) : Prop :=
  ∀ (i : Fin c.length) (z : X),
    (c i.castSucc) ⤳ z → z ⤳ (c i.succ) →
      z = c i.castSucc ∨ z = c i.succ

/-- Every step of a maximal chain of nontrivial specializations is an immediate
specialization. -/
private theorem isImmediateSpecialization_of_chain_step
    {X : Type*} [TopologicalSpace X]
    (c : RelSeries {p : X × X | p.1 ⤳ p.2 ∧ p.1 ≠ p.2})
    (hc : IsMaximalSpecializationChain c) (i : Fin c.length) :
    IsImmediateSpecialization (c i.castSucc) (c i.succ) := by
  rw [TopologicalSpace.isImmediateSpecialization_iff]
  exact ⟨(c.step i).1, (c.step i).2, fun z hz1 hz2 => hc i z hz1 hz2⟩

/-- The length of a maximal chain of nontrivial specializations on a scheme locally of finite
type over a field is the drop in transcendence degree of the residue fields at its endpoints. -/
@[stacks 0A21 "specialization_chain_length"]
theorem length_eq_trdeg_sub_of_maximalSpecializationChain
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [LocallyOfFiniteType f] (x x' : X) (_hxx' : x ⤳ x') (_hne : x ≠ x')
    (c : RelSeries {p : X × X | p.1 ⤳ p.2 ∧ p.1 ≠ p.2})
    (hc : IsMaximalSpecializationChain c) (hhead : c.head = x) (hlast : c.last = x') :
    letI : Algebra k (X.residueField x) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x).hom.toAlgebra
    letI : Algebra k (X.residueField x') :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation x').hom.toAlgebra
    c.length = Cardinal.toNat (Algebra.trdeg k (X.residueField x)) -
      Cardinal.toNat (Algebra.trdeg k (X.residueField x')) := by
  have hstep : ∀ i : Fin c.length,
      natTrdeg k X f (c i.castSucc) = natTrdeg k X f (c i.succ) + 1 := by
    intro i
    let : Algebra k (X.residueField (c i.castSucc)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫
        X.Γevaluation (c i.castSucc)).hom.toAlgebra
    let : Algebra k (X.residueField (c i.succ)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop ≫ X.Γevaluation (c i.succ)).hom.toAlgebra
    have h := trdeg_residueField_eq_add_one_of_isImmediateSpecialization k X f
      (x := c i.castSucc) (x' := c i.succ)
      (isImmediateSpecialization_of_chain_step c hc i)
    dsimp [natTrdeg]
    let : Algebra.EssFiniteType k (X.residueField (c i.castSucc)) :=
      residueField_essFiniteType k f (c i.castSucc)
    let : Algebra.EssFiniteType k (X.residueField (c i.succ)) :=
      residueField_essFiniteType k f (c i.succ)
    rw [h, Cardinal.toNat_add]
    · simp
    · exact trdeg_lt_aleph0 k _
    · simp
  have htel := nat_value_at_last_eq_length_add_nat_value_at_head
    (natTrdeg k X f) c hstep
  rw [hhead, hlast] at htel
  show c.length = natTrdeg k X f x - natTrdeg k X f x'
  omega

end AlgebraicGeometry

end
