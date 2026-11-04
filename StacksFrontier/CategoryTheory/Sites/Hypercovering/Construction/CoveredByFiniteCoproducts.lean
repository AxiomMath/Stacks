module

public import Mathlib.CategoryTheory.Limits.Comma
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Construction.WeaklyContractibleHypercovering

/-!
# Hypercoverings on a site covered by finite disjoint unions

A Grothendieck topology is *covered by finite disjoint unions* when the summands of every finite
disjoint union form a covering family of it. On such a site the remaining hypothesis of
Stacks 0DB2 for finitely indexed families — that taking disjoint unions degreewise preserves
coverings — holds, so any hypercovering whose families are finite can be replaced by one whose
term in every degree is a single object.

## Main definitions

* `CoveredByFiniteCoproducts`: the summands of every finite disjoint union cover it.

## Main results

* `takeUnionsFinPreservesCoverings_of_coveredByFiniteCoproducts`: on such a site, taking finite
  disjoint unions degreewise preserves coverings.
* `exists_singleton_hypercovering_of_finite`: a hypercovering whose families are finite and
  consist of objects of a class `B` closed under finite disjoint unions gives a hypercovering
  whose term in every degree is one object of `B` covering the base.

## References

* [Stacks Project, Tag 0DB2](https://stacks.math.columbia.edu/tag/0DB2)
* [Stacks Project, Tag 09A1](https://stacks.math.columbia.edu/tag/09A1)
-/

@[expose] public section

universe w v u

open CategoryTheory CategoryTheory.Limits Opposite Simplicial

namespace Stacks.CategoryTheory.Hypercovering

variable {C : Type u} [Category.{v} C] (T : GrothendieckTopology C)

/-- The topology `T` is *covered by finite disjoint unions*: the summands of every disjoint union
of a family indexed by a finite type of universe `w` form a covering family of it. -/
def CoveredByFiniteCoproducts : Prop :=
  ∀ ⦃ι : Type w⦄ [Finite ι] {Y : ι → C} (c : Cofan Y), IsColimit c →
    Sieve.ofArrows Y c.inj ∈ T c.pt

variable {T} [HasPullbacks C]

/-- On a site with finite coproducts covered by finite disjoint unions, taking finite disjoint
unions of semi-representable objects over `X` degreewise preserves coverings: a finite coproduct
in `Over X` is computed in the underlying category. -/
theorem takeUnionsFinPreservesCoverings_of_coveredByFiniteCoproducts [HasFiniteCoproducts C]
    (hT : CoveredByFiniteCoproducts.{w} T) (X : C) [FinitaryExtensive (Over X)] :
    TakeUnionsFinPreservesCoverings.{w} T X :=
  takeUnionsFinPreservesCoverings_of_ofArrows_sigmaι T X fun A ↦
    hT _ (isColimitOfHasCoproductOfPreservesColimit (Over.forget X) A)

variable (T)

/-- **Disjoint unions in a hypercovering.** Let `K` be a hypercovering of `X` whose family in
every degree is finite and consists of objects of a class `B` closed under finite disjoint unions
over `X`, and suppose that taking finite disjoint unions degreewise preserves coverings. Then `X`
has a hypercovering whose term in every degree is a single object of `B` covering `X`: the
degreewise disjoint union of `K` (Stacks 0DB2). -/
theorem exists_singleton_hypercovering_of_finite (B : Set C) {X : C} [FinitaryExtensive (Over X)]
    (hunions : TakeUnionsFinPreservesCoverings.{w} T X) (sum_mem : SumMemFin.{w} B X)
    (K : SimplicialObject (FormalCoproduct.{w} (Over X)))
    (hK : IsHypercovering T.toPretopology K)
    (hfin : ∀ n : ℕ, Finite (K.obj (op ⦋n⦌)).I ∧ ∀ i, ((K.obj (op ⦋n⦌)).obj i).left ∈ B) :
    ∃ K : SimplicialObject (FormalCoproduct.{w} (Over X)),
      IsHypercovering T.toPretopology K ∧
        ∀ n : ℕ, ∃ i : (K.obj (op ⦋n⦌)).I,
          (∀ j : (K.obj (op ⦋n⦌)).I, j = i) ∧
            ((K.obj (op ⦋n⦌)).obj i).left ∈ B ∧
            Presieve.singleton ((K.obj (op ⦋n⦌)).obj i).hom ∈ T.toPretopology X := by
  classical
  have hsum : ∀ n, Finite (K.obj n).I := fun n ↦ (hfin n.unop.len).1
  refine ⟨((SimplicialObject.whiskering _ _).obj (takeUnionsFin (C := Over X))).obj
      (ObjectProperty.lift (fun A : FormalCoproduct.{w} (Over X) ↦ Finite A.I) K hsum),
    isHypercovering_whiskerLift T.toPretopology _ (takeUnionsFin (C := Over X)) hunions K hsum hK,
    fun n ↦ ?_⟩
  have hfinI : Finite (K.obj (op ⦋n⦌)).I := (hfin n).1
  refine ⟨PUnit.unit, fun j ↦ Subsingleton.elim (α := PUnit.{w + 1}) j PUnit.unit, ?_, ?_⟩
  · show ((∐ (K.obj (op ⦋n⦌)).obj : Over X)).left ∈ B
    exact sum_mem (K.obj (op ⦋n⦌)) (hfin n).2
  · refine singleton_mem_toPretopology_of_factorsThrough T (K.obj (op ⦋0⦌)) hK.1 _ (fun i ↦ ?_)
    let F := K.map (SimplexCategory.const ⦋n⦌ ⦋0⦌ 0).op
    exact F.φ i ≫ Sigma.ι (K.obj (op ⦋n⦌)).obj (F.f i)

end Stacks.CategoryTheory.Hypercovering

end
