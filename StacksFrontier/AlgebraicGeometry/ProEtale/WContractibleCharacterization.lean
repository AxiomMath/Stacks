module

public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtaleConstruction.StrictlyHenselianFromRetractions
public import StacksFrontier.AlgebraicGeometry.ProEtale.WContractibleIndEtaleRetraction

/-!
# Towards the characterization of w-contractible rings

Lemma 0982 states that for a ring `A` the following are equivalent:

1. `A` is w-contractible (Definition 0981: every faithfully flat weakly étale `A → B` has a
   retraction);
2. every faithfully flat *ind-étale* `A → B` has a retraction;
3. `Spec A` is w-local, `π₀(Spec A)` is extremally disconnected, and `A_𝔪` is strictly henselian
   for every maximal ideal `𝔪`.

This file proves the implication (1) ⇒ (2) and the part of (2) ⇒ (3) that concerns condition
(3)(c), strict henselianity of the local rings at the maximal ideals.

## Main results

* `AlgebraicGeometry.ProEtale.nonempty_algHom_of_ind_etale_of_isWContractible`: implication
  (1) ⇒ (2) of Lemma 0982.
* `AlgebraicGeometry.ProEtale.strictlyHenselian_atPrime_of_ind_etale_retraction`: the component
  (2) ⇒ (3)(c) of Lemma 0982.

## Implementation notes

Condition (2) is stated with ind-étaleness in the single-universe categorical form
`(CommAlgCat.etale A).ind (CommAlgCat.of A B)`, which `StacksDraft.indEtale_iff` identifies with
the universe-independent `StacksDraft.IndEtale`; the latter is the form in which
`ProetaleWContractible.IsWContractible.nonempty_algHom_of_indEtale` proves (1) ⇒ (2).

For (2) ⇒ (3)(c), an étale algebra is ind-étale by `CategoryTheory.ObjectProperty.le_ind`, so
condition (2) specializes to the hypothesis of Lemma 097V
(`localizationAtPrime_strictlyHenselian_of_etale_faithfullyFlat`).

## References

* [Stacks Project, Tag 0982](https://stacks.math.columbia.edu/tag/0982)
* [Stacks Project, Tag 0981](https://stacks.math.columbia.edu/tag/0981)
* [Stacks Project, Tag 097V](https://stacks.math.columbia.edu/tag/097V)
-/

open CategoryTheory

@[expose] public section

universe u

namespace AlgebraicGeometry.ProEtale

/-- **Lemma 0982, (1) ⇒ (2).** A w-contractible ring retracts every faithfully flat ind-étale
algebra over it, ind-étaleness being taken in the categorical form
`(CommAlgCat.etale A).ind (CommAlgCat.of A B)`. -/
@[stacks 0982 "(1) ⇒ (2)"]
theorem nonempty_algHom_of_ind_etale_of_isWContractible (A : Type u) [CommRing A]
    (h : ProetaleWContractible.IsWContractible.{u, u} A) (B : Type u) [CommRing B]
    [Algebra A B] (hff : Module.FaithfullyFlat A B)
    (hind : ObjectProperty.ind.{u} (fun C : CommAlgCat A ↦ Algebra.Etale A C)
      (CommAlgCat.of A B)) :
    Nonempty (B →ₐ[A] A) :=
  h.nonempty_algHom_of_indEtale B hff (StacksDraft.indEtale_iff.mpr hind)

/-- **Lemma 0982, the (3)(c) component of (2) ⇒ (3).** If every faithfully flat ind-étale
algebra over `A` has a retraction, then `A` localized at any maximal ideal is strictly
henselian. An étale algebra is ind-étale, so this is Lemma 097V. -/
@[stacks 0982 "(2) ⇒ (3)(c)"]
theorem strictlyHenselian_atPrime_of_ind_etale_retraction (A : Type u) [CommRing A]
    (h : ∀ (B : Type u) [CommRing B] [Algebra A B], Module.FaithfullyFlat A B →
      ObjectProperty.ind.{u} (fun C : CommAlgCat A ↦ Algebra.Etale A C) (CommAlgCat.of A B) →
      Nonempty (B →ₐ[A] A))
    (m : Ideal A) [m.IsMaximal] :
    StrictlyHenselianLocalRing (Localization.AtPrime m) :=
  localizationAtPrime_strictlyHenselian_of_etale_faithfullyFlat_retracts A
    (fun B _ _ _ _ ↦ h B inferInstance
      (ObjectProperty.le_ind _ (CommAlgCat.of A B) inferInstance)) m

end AlgebraicGeometry.ProEtale

end
