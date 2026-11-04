module

public import StacksFrontier.AlgebraicGeometry.Etale.FiniteEtaleLocal
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.Finrank
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.FieldTarget

/-!
# The fold map of a finite disjoint union of copies of an affine scheme

A finite disjoint union of copies of an affine scheme is, over that scheme, finite locally free
of rank the number of copies: on the spectrum of a ring `T` the disjoint union of `ι` copies is
the spectrum of `ι → T`, which is free of rank `#ι` as a `T`-module. The same holds for the map
out of the disjoint union given by an arbitrary family of *automorphisms* of the base, since
such a map differs from the fold map by an automorphism of the disjoint union.

The second form is what the covering of Stacks 05ZI needs: the pair of charts of the affine line
with doubled origin maps to the affine line by the identity on one copy and by negation of the
coordinate on the other.

## Main definitions

* `AlgebraicGeometry.sigmaTwist`: the automorphism of a disjoint union of copies of a scheme
  given by a family of automorphisms of that scheme, acting summandwise.
* `AlgebraicGeometry.sigmaShrinkIso`: the comparison of a disjoint union indexed by a `u`-small
  type with the one indexed by a copy of that type in the universe `u`.

## Main results

* `Module.isFiniteLocallyFreeOfRank_pi`: a finite product of copies of a commutative ring is
  finite locally free of rank the cardinality of the index type.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_sigmaDesc_id`: the fold map of a finite disjoint
  union of copies of an affine scheme is finite locally free of rank the number of copies.
* `AlgebraicGeometry.isFiniteLocallyFreeOfRank_sigmaDesc_of_isIso`: the same for the map given by
  a family of automorphisms of the base.

## Implementation notes

The module-level statement is proved through the rank function `Module.rankAtStalk`, to which
`Stacks.Morphisms.isFiniteLocallyFreeOfRank_iff_rankAtStalk_eq` reduces finite local freeness of
a fixed rank for a finite flat module. Over the zero ring the rank function is not constantly
`#ι`, but there the prime spectrum is empty and the condition is vacuous, which is why the proof
splits on `Subsingleton`/`Nontrivial`.

The index type is only assumed `u`-small, while the ring `ι → T` has to live in the universe of
the scheme; the passage is `AlgebraicGeometry.sigmaShrinkIso`, which reindexes the disjoint union
along `Shrink`.

Affineness of the base is not a limitation of the method but of the statement that is needed:
being finite locally free of rank `r` is Zariski local on the target, so the general case follows
by covering the base — but the base change of a disjoint union along an open immersion has to be
identified with the disjoint union of the base changes first, and nothing downstream needs that.

## References

* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe v u

/-- **A finite product of copies of a commutative ring is finite locally free of rank the
cardinality of the index type.** The rank at a prime of a finite product is the sum of the ranks
of the factors, each of which is `1`; over the zero ring there are no primes and the condition is
vacuous. -/
theorem Module.isFiniteLocallyFreeOfRank_pi (T : Type u) [CommRing T] (ι : Type u) [Finite ι] :
    Module.IsFiniteLocallyFreeOfRank T (ι → T) (Nat.card ι) := by
  rw [Module.isFiniteLocallyFreeOfRank_iff_rankAtStalk_eq]
  intro p
  rcases subsingleton_or_nontrivial T with _ | _
  · exact (IsEmpty.false p).elim
  · have : Fintype ι := Fintype.ofFinite ι
    rw [Module.rankAtStalk_pi, finsum_eq_sum_of_fintype]
    simp [Nat.card_eq_fintype_card]

namespace AlgebraicGeometry

section Twist

variable {X : Scheme.{u}} {ι : Type v} [Small.{u} ι]

/-- The endomorphism of a disjoint union of copies of a scheme given by a family of
endomorphisms of that scheme, acting summandwise. -/
noncomputable def sigmaTwist (e : ι → (X ⟶ X)) :
    (∐ fun _ : ι => X) ⟶ (∐ fun _ : ι => X) :=
  Sigma.desc fun i => e i ≫ Sigma.ι (fun _ : ι => X) i

/-- On the `i`-th summand, `sigmaTwist e` is `e i` followed by the inclusion of the `i`-th
summand. -/
@[simp]
theorem sigmaι_comp_sigmaTwist (e : ι → (X ⟶ X)) (i : ι) :
    Sigma.ι (fun _ : ι => X) i ≫ sigmaTwist e = e i ≫ Sigma.ι (fun _ : ι => X) i :=
  Sigma.ι_desc _ i

/-- Twisting by a family of endomorphisms and then folding is the map given by the family. -/
theorem sigmaTwist_comp_sigmaDesc_id (e : ι → (X ⟶ X)) :
    sigmaTwist e ≫ (Sigma.desc fun _ : ι => 𝟙 X) = Sigma.desc e := by
  refine Sigma.hom_ext _ _ fun i => ?_
  rw [← Category.assoc, sigmaι_comp_sigmaTwist, Category.assoc, Sigma.ι_desc, Category.comp_id,
    Sigma.ι_desc]

/-- Twisting by a family of isomorphisms is an isomorphism of the disjoint union. -/
instance isIso_sigmaTwist (e : ι → (X ⟶ X)) [∀ i, IsIso (e i)] : IsIso (sigmaTwist e) := by
  refine ⟨sigmaTwist fun i => inv (e i), ?_, ?_⟩ <;>
    refine Sigma.hom_ext _ _ fun i => ?_ <;>
    rw [← Category.assoc, sigmaι_comp_sigmaTwist, Category.assoc, sigmaι_comp_sigmaTwist,
      ← Category.assoc]
  · rw [IsIso.hom_inv_id, Category.id_comp, Category.comp_id]
  · rw [IsIso.inv_hom_id, Category.id_comp, Category.comp_id]

/-- The comparison of a disjoint union of copies of a scheme indexed by a `u`-small type with
the one indexed by a copy of that type in the universe `u`. -/
noncomputable def sigmaShrinkIso (X : Scheme.{u}) (ι : Type v) [Small.{u} ι] :
    (∐ fun _ : ι => X) ≅ (∐ fun _ : Shrink.{u} ι => X) where
  hom := Sigma.desc fun i => Sigma.ι (fun _ : Shrink.{u} ι => X) (equivShrink ι i)
  inv := Sigma.desc fun j => Sigma.ι (fun _ : ι => X) ((equivShrink ι).symm j)
  hom_inv_id := by
    refine Sigma.hom_ext _ _ fun i => ?_
    rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc, Category.comp_id, Equiv.symm_apply_apply]
  inv_hom_id := by
    refine Sigma.hom_ext _ _ fun j => ?_
    rw [← Category.assoc, Sigma.ι_desc, Sigma.ι_desc, Category.comp_id, Equiv.apply_symm_apply]

/-- The reindexing comparison is compatible with the fold maps. -/
theorem sigmaShrinkIso_hom_comp_sigmaDesc_id (X : Scheme.{u}) (ι : Type v) [Small.{u} ι] :
    (sigmaShrinkIso X ι).hom ≫ (Sigma.desc fun _ : Shrink.{u} ι => 𝟙 X) =
      Sigma.desc fun _ : ι => 𝟙 X := by
  refine Sigma.hom_ext _ _ fun i => ?_
  rw [← Category.assoc]
  show (Sigma.ι (fun _ : ι => X) i ≫ Sigma.desc fun i =>
    Sigma.ι (fun _ : Shrink.{u} ι => X) (equivShrink ι i)) ≫ _ = _
  rw [Sigma.ι_desc, Sigma.ι_desc, Sigma.ι_desc]

end Twist

/-- **The fold map of a finite disjoint union of copies of the spectrum of a ring is finite
locally free of rank the number of copies.** The disjoint union is the spectrum of the product
of the copies, by `AlgebraicGeometry.sigmaSpec`, and that product is finite locally free of rank
`#ι` over the ring. -/
theorem isFiniteLocallyFreeOfRank_sigmaDesc_id_spec (T : Type u) [CommRing T] (ι : Type u)
    [Finite ι] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (Sigma.desc fun _ : ι => 𝟙 (Spec (CommRingCat.of T))) (Nat.card ι) := by
  have h : Stacks.Morphisms.IsFiniteLocallyFreeOfRank
      (Spec.map (CommRingCat.ofHom (algebraMap T (ι → T)))) (Nat.card ι) :=
    (Stacks.Morphisms.isFiniteLocallyFreeOfRank_specMap_iff_module T (ι → T) _).2
      (Module.isFiniteLocallyFreeOfRank_pi T ι)
  rw [← Stacks.Etale.sigmaSpec_comp_specMap_algebraMap ι T]
  exact Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp
    (asIso (sigmaSpec fun _ : ι => CommRingCat.of T)) _ h

/-- The fold map of a finite disjoint union of copies of an affine scheme, for an index type in
the universe of the scheme. -/
private theorem isFiniteLocallyFreeOfRank_sigmaDesc_id_aux {X : Scheme.{u}} [IsAffine X]
    (ι : Type u) [Finite ι] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (Sigma.desc fun _ : ι => 𝟙 X) (Nat.card ι) := by
  set e : X ≅ Spec (CommRingCat.of Γ(X, ⊤)) := X.isoSpec with he
  set m : (∐ fun _ : ι => X) ≅ ∐ fun _ : ι => Spec (CommRingCat.of Γ(X, ⊤)) :=
    Sigma.mapIso fun _ => e with hm
  have hfac : (Sigma.desc fun _ : ι => 𝟙 X) =
      m.hom ≫ (Sigma.desc fun _ : ι => 𝟙 (Spec (CommRingCat.of Γ(X, ⊤)))) ≫ e.inv := by
    refine Sigma.hom_ext _ _ fun i => ?_
    simp [hm]
  have h := Stacks.Morphisms.isFiniteLocallyFreeOfRank_postcomp e.symm _
    (isFiniteLocallyFreeOfRank_sigmaDesc_id_spec Γ(X, ⊤) ι)
  rw [hfac]
  exact Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp m _ h

/-- **The fold map of a finite disjoint union of copies of an affine scheme is finite locally
free of rank the number of copies.** The affine scheme is the spectrum of its global sections,
and the index type is reindexed into the universe of the scheme by
`AlgebraicGeometry.sigmaShrinkIso`. -/
theorem isFiniteLocallyFreeOfRank_sigmaDesc_id {X : Scheme.{u}} [IsAffine X] (ι : Type v)
    [Small.{u} ι] [Finite ι] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (Sigma.desc fun _ : ι => 𝟙 X) (Nat.card ι) := by
  have _hfin : Finite (Shrink.{u} ι) := Finite.of_equiv ι (equivShrink ι)
  have hcard : Nat.card (Shrink.{u} ι) = Nat.card ι :=
    Nat.card_congr (equivShrink ι).symm
  rw [← sigmaShrinkIso_hom_comp_sigmaDesc_id X ι, ← hcard]
  exact Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp (sigmaShrinkIso X ι) _
    (isFiniteLocallyFreeOfRank_sigmaDesc_id_aux (X := X) (Shrink.{u} ι))

/-- **A disjoint union of finitely many copies of an affine scheme is, by any family of
automorphisms of that scheme, finite locally free of rank the number of copies.** Such a map
differs from the fold map by the summandwise automorphism `AlgebraicGeometry.sigmaTwist`. -/
theorem isFiniteLocallyFreeOfRank_sigmaDesc_of_isIso {X : Scheme.{u}} [IsAffine X] {ι : Type v}
    [Small.{u} ι] [Finite ι] (e : ι → (X ⟶ X)) [∀ i, IsIso (e i)] :
    Stacks.Morphisms.IsFiniteLocallyFreeOfRank (Sigma.desc e) (Nat.card ι) := by
  rw [← sigmaTwist_comp_sigmaDesc_id e]
  exact Stacks.Morphisms.isFiniteLocallyFreeOfRank_precomp (asIso (sigmaTwist e)) _
    (isFiniteLocallyFreeOfRank_sigmaDesc_id ι)

end AlgebraicGeometry

end
