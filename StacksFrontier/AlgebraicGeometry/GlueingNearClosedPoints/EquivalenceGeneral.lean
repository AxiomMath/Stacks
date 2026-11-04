module

public import Mathlib.Data.Fintype.Option
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.AmbientOpen
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.Induction
public import StacksFrontier.AlgebraicGeometry.GlueingNearClosedPoints.PeelTransport

/-!
# Glueing schemes near finitely many closed points

This file proves [Stacks, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q) in general: for a
finite family `s : I → S` of pairwise distinct closed points of a scheme `S` whose open
complement `U` has quasi-compact inclusion, the canonical restriction functor from schemes of
finite presentation over `S` to glueing data near the family is an equivalence of categories.

The proof is the induction of the source, run over the index type by
`Finite.induction_empty_option`.  The empty case is
`AlgebraicGeometry.canonicalRestrictionFunctor_isEquivalence_of_isEmpty`, and reindexing along an
equivalence of index types is
`AlgebraicGeometry.restrictionFunctorOf_isEquivalence_of_reindex`.  For the inductive step one
peels the point `s none` off an `Option J`-indexed family: writing `W` for the open complement of
the subfamily at `some`, the open `U` is the complement of `s none` inside `W`, so
[Stacks, Tag 0BPA] applies to `s none` relative to `W`
(`AlgebraicGeometry.restrictionFunctorOfSquare_isEquivalence_of_ambientOpen`), while the
inductive hypothesis handles the subfamily over `W`.  Those two equivalences are combined by
`AlgebraicGeometry.restrictionFunctorOf_isEquivalence_of_peel`, whose hypothesis that the
overlaps of the two families agree is
`AlgebraicGeometry.preimage_fromSpecStalk_complementOfClosedPoints`: this is the only place where
the points are used to be pairwise distinct, apart from the fact that `s none` has not already
been removed from `W`.

## Main results

* `AlgebraicGeometry.canonicalRestrictionFunctor_isEquivalence_of_opens`: the inductive step, for
  a family indexed by `Option J` and a pair of opens `U ⊆ W` presenting it.
* `AlgebraicGeometry.canonicalRestrictionFunctor_isEquivalence`: **Stacks Project, Tag 0E8Q**.

## Implementation notes

The statement carried through the induction is about
`AlgebraicGeometry.restrictionFunctorOf` for an open `U` which is only *assumed* to be the
complement of the family, rather than about
`AlgebraicGeometry.canonicalRestrictionFunctor` directly.  That is what makes the reindexing step
free: the complement of `s` and the complement of `s ∘ e` are equal but not definitionally so,
and carrying the open as a parameter lets both families be treated with the same term for `U`, so
that the two canonical functors are literally the same up to reindexing the glueing data.

## References

* [Stacks Project, Tag 0E8Q](https://stacks.math.columbia.edu/tag/0E8Q)
* [Stacks Project, Lemma 32.14.1 (0BPA)](https://stacks.math.columbia.edu/tag/0BPA)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Topology

universe u

namespace AlgebraicGeometry

/-! ### The inductive step -/

/-- The inductive step of **Stacks Project, Tag 0E8Q**, for a family of closed points indexed by
`Option J`.

Let `W` be an open of `S` containing the point `s none`, which is closed in `S`, and let `U` be
the complement of `s none` in `W`, with quasi-compact inclusion.  Assume that the overlaps of the
remaining points of the family do not change when the open is enlarged from `U` to `W`.  Then the
canonical functor of the whole family over `U` is an equivalence as soon as the canonical functor
of the subfamily over `W` is one. -/
theorem canonicalRestrictionFunctor_isEquivalence_of_opens {S : Scheme.{u}} {J : Type u}
    (s : Option J → S) (U W : S.Opens) (ht : IsClosed ({s none} : Set S)) (htW : s none ∈ W)
    (hUW : (U : Set S) = (W : Set S) ∩ ({s none}ᶜ : Set S)) (hqc : QuasiCompact U.ι)
    (hpre : ∀ j, S.fromSpecStalk (s (some j)) ⁻¹ᵁ U = S.fromSpecStalk (s (some j)) ⁻¹ᵁ W)
    (hG : (restrictionFunctorOf W.ι (fun j ↦ S.fromSpecStalk (s (some j)))
      (fun j ↦ S.fromSpecStalk (s (some j)) ∣_ W)
      (fun j ↦ (S.fromSpecStalk (s (some j)) ⁻¹ᵁ W).ι)
      (fun j ↦ morphismRestrict_ι (S.fromSpecStalk (s (some j))) W)).IsEquivalence) :
    (restrictionFunctorOf U.ι (fun i ↦ S.fromSpecStalk (s i))
      (fun i ↦ S.fromSpecStalk (s i) ∣_ U) (fun i ↦ (S.fromSpecStalk (s i) ⁻¹ᵁ U).ι)
      (fun i ↦ morphismRestrict_ι (S.fromSpecStalk (s i)) U)).IsEquivalence := by
  have hUle : U ≤ W := le_of_eq_inter_compl W U hUW
  have hτb : ∀ j, ((Spec (S.presheaf.stalk (s (some j)))).isoOfEq (hpre j)).hom ≫
      (S.fromSpecStalk (s (some j)) ⁻¹ᵁ W).ι = (S.fromSpecStalk (s (some j)) ⁻¹ᵁ U).ι :=
    fun j ↦ Scheme.isoOfEq_hom_ι _ (hpre j)
  have hτa : ∀ j, ((Spec (S.presheaf.stalk (s (some j)))).isoOfEq (hpre j)).hom ≫
      (S.fromSpecStalk (s (some j)) ∣_ W) =
        (S.fromSpecStalk (s (some j)) ∣_ U) ≫ S.homOfLE hUle := by
    intro j
    rw [← cancel_mono W.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      Scheme.homOfLE_ι, morphismRestrict_ι, ← Category.assoc, hτb j]
  have h₀ : (S.fromSpecStalk (s none) ∣_ U) ≫ S.homOfLE hUle =
      (S.fromSpecStalk (s none) ⁻¹ᵁ U).ι ≫ W.fromSpecStalkOfMem (s none) htW := by
    rw [← cancel_mono W.ι, Category.assoc, Category.assoc, Scheme.homOfLE_ι,
      Scheme.Opens.fromSpecStalkOfMem_ι, morphismRestrict_ι]
  have hH := restrictionFunctorOfSquare_isEquivalence_of_ambientOpen W ht htW U hUW hqc
    (S.homOfLE_ι hUle) (Scheme.Opens.fromSpecStalkOfMem_ι W (s none) htW) h₀
  exact restrictionFunctorOf_isEquivalence_of_peel
    (fun j ↦ (Spec (S.presheaf.stalk (s (some j)))).isoOfEq (hpre j)) hτa hτb
    (S.homOfLE_ι hUle) (Scheme.Opens.fromSpecStalkOfMem_ι W (s none) htW) h₀
    (fun j ↦ morphismRestrict_ι (S.fromSpecStalk (s (some j))) W)
    (fun i ↦ morphismRestrict_ι (S.fromSpecStalk (s i)) U) hH hG

/-! ### The induction -/

/-- **Stacks Project, Tag 0E8Q** in the form carried through the induction on the index type: the
open complement is a parameter, assumed only to have the complement of the family as its
underlying set. -/
theorem restrictionFunctorOf_isEquivalence_of_closedPoints (I : Type u) [Finite I] :
    ∀ (S : Scheme.{u}) (V : S.Opens) (s : I → S), (∀ i, s i ∈ closedPoints S) →
      Function.Injective s → (V : Set S) = ⋂ i, ({s i}ᶜ : Set S) → QuasiCompact V.ι →
      (restrictionFunctorOf V.ι (fun i ↦ S.fromSpecStalk (s i))
        (fun i ↦ S.fromSpecStalk (s i) ∣_ V) (fun i ↦ (S.fromSpecStalk (s i) ⁻¹ᵁ V).ι)
        (fun i ↦ morphismRestrict_ι (S.fromSpecStalk (s i)) V)).IsEquivalence := by
  induction I using Finite.induction_empty_option
  · next α β e hα =>
    intro S V s hs hinj hV hqc
    refine restrictionFunctorOf_isEquivalence_of_reindex _ _ e _ _ _ ?_
    refine hα S V (fun i' ↦ s (e i')) (fun i' ↦ hs (e i'))
      (fun _ _ hxy ↦ e.injective (hinj hxy)) ?_ hqc
    rw [hV]
    exact (e.surjective.iInter_comp fun i ↦ ({s i}ᶜ : Set S)).symm
  · intro S V s hs hinj hV hqc
    obtain rfl : V = complementOfClosedPoints s hs := TopologicalSpace.Opens.ext hV
    exact canonicalRestrictionFunctor_isEquivalence_of_isEmpty s hs
  · next α _ hα =>
    intro S V s hs hinj hV hqc
    obtain rfl : V = complementOfClosedPoints s hs := TopologicalSpace.Opens.ext hV
    refine canonicalRestrictionFunctor_isEquivalence_of_opens s (complementOfClosedPoints s hs)
      (complementOfClosedPoints (s ∘ Option.some) (fun j ↦ hs (some j)))
      (mem_closedPoints_iff.mp (hs none))
      (mem_complementOfClosedPoints_some_of_injective s hs hinj) ?_ hqc
      (fun j ↦ preimage_fromSpecStalk_complementOfClosedPoints s hs Option.some ?_) ?_
    · rw [complementOfClosedPoints_option s hs]
      rfl
    · rintro (_ | i) hi
      · exact fun heq ↦ Option.some_ne_none _ (hinj heq).symm
      · exact absurd ⟨i, rfl⟩ hi
    · exact hα S (complementOfClosedPoints (s ∘ Option.some) (fun j ↦ hs (some j)))
        (s ∘ Option.some) (fun j ↦ hs (some j))
        (fun _ _ hxy ↦ Option.some_injective α (hinj hxy)) rfl
        (quasiCompact_ι_complementOfClosedPoints_comp s hs Option.some hqc)

/-- **Stacks Project, Tag 0E8Q.** Let `s : I → S` be a finite family of pairwise distinct closed
points of a scheme `S` whose open complement has quasi-compact inclusion.  Then the canonical
restriction functor from schemes of finite presentation over `S` to glueing data near the family
— a scheme of finite presentation over the open complement, a family of schemes of finite
presentation over the local schemes at the points, and an isomorphism of the two restrictions to
each punctured local scheme — is an equivalence of categories. -/
@[stacks 0E8Q "equivalence, general finite family of points"]
theorem canonicalRestrictionFunctor_isEquivalence {S : Scheme.{u}} {I : Type u} [Finite I]
    (s : I → S) (hs : ∀ i, s i ∈ closedPoints S) (hinj : Function.Injective s)
    (hqc : QuasiCompact (complementOfClosedPoints s hs).ι) :
    (canonicalRestrictionFunctor s hs).IsEquivalence :=
  restrictionFunctorOf_isEquivalence_of_closedPoints I S (complementOfClosedPoints s hs) s hs
    hinj rfl hqc

end AlgebraicGeometry

end
