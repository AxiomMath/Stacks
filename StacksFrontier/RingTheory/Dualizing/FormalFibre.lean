module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Dualizing.Gorenstein
public import StacksFrontier.RingTheory.LocalCompleteIntersection.Basic

/-!
# Ground-field and prime-local independence of two conditions (Stacks chapter Dualizing Complexes)

Two of the conditions used in the study of formal fibres — being a local complete intersection
and being Gorenstein — are properties of the underlying Noetherian ring alone, and each is
local at prime ideals. Tags 0BJN and 0BJP ask for five properties of such a condition, (A) to
(E) of [Stacks, Tag 0BIR]; this file records the two of them which hold for the definitions
themselves, namely that the condition is the condition at every prime and that it does not
mention the ground field, so that enlarging the ground field along a separable algebraic
extension leaves it unchanged.

Concretely: `LocalCompleteIntersection.IsLocalCompleteIntersectionRing` is defined as the
assertion that every localization at a prime is a complete intersection local ring, and
`Dualizing.IsGorensteinRing` is defined as the assertion that every localization at a prime is
a Gorenstein local ring. Both predicates take only a Noetherian commutative ring as input, so
they are visibly independent of any algebra structure over a field, and the defining
equivalences are the prime-local characterizations the source asks for.

The other three properties — (A), base change along a finitely generated extension of the
ground field, (C), ascent through a composition of flat maps whose second map is regular, and
(D), descent through a faithfully flat second map — are not definitional unfoldings and are
proved elsewhere. For the local complete intersection condition all five, including the two
recorded here, are conjoined in
`localCompleteIntersectionProperty_satisfies_formalFiberAxioms` in
`StacksFrontier/RingTheory/LocalCompleteIntersection/FormalFibreAxioms.lean`.

For Gorensteinness the same two definitional clauses of [Stacks, Tag 0BJN] are also available as
theorems, in `StacksFrontier/RingTheory/Dualizing/GorensteinFormalFibreAxioms.lean`: the prime-local
characterization, clause (B), is `Dualizing.gorensteinProperty_localization`, and the ground-field
independence, clause (E), is `Dualizing.gorensteinProperty_groundFieldExtension`.

## References

* [Stacks Project, Tag 0BJN](https://stacks.math.columbia.edu/tag/0BJN)
* [Stacks Project, Tag 0BJP](https://stacks.math.columbia.edu/tag/0BJP)
* [Stacks Project, Tag 0BIR](https://stacks.math.columbia.edu/tag/0BIR)
-/

-- Tag 0BJP, the two properties of 0BIR which are definitional here: being a local complete
-- intersection is characterized by, and defined as, the condition at every prime, which gives
-- property (B); and the predicate takes no ground field as input, so it is unchanged by
-- enlarging one, which gives property (E). Properties (A), (C) and (D) are proved in
-- `StacksFrontier/RingTheory/LocalCompleteIntersection/FormalFibreAxioms.lean`, where all five are
-- also conjoined.
add_to_stacks 0BJP "localization"
  LocalCompleteIntersection.isLocalCompleteIntersectionRing_iff
add_to_stacks 0BJP "ground_field_change"
  LocalCompleteIntersection.IsLocalCompleteIntersectionRing

-- Tag 0BJN: likewise for Gorensteinness — the predicate is defined by the condition at every
-- prime localization and has no ground-field parameter, which gives both the local
-- characterization and the ground-field independence. The same two clauses are proved as
-- theorems in `StacksFrontier/RingTheory/Dualizing/GorensteinFormalFibreAxioms.lean`, namely
-- `Dualizing.gorensteinProperty_localization` (B) and
-- `Dualizing.gorensteinProperty_groundFieldExtension` (E).
add_to_stacks 0BJN "gorenstein_local and gorenstein_ground_field: this predicate is defined by \
  the condition at every prime localization and takes no ground field as input"
  Dualizing.IsGorensteinRing
