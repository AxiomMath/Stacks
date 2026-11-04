module

public import Mathlib.Algebra.Algebra.Subalgebra.Lattice
public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import StacksFrontier.Algebra.Category.ModuleCat.Center
public import StacksFrontier.CategoryTheory.Center.Shift

import StacksCore.Tactic.StacksAttribute

/-!
# Derived equivalent algebras have isomorphic centres

Let `R` be a commutative ring and let `A` and `B` be `R`-algebras. If the derived categories
`D(A)` and `D(B)` are equivalent as `R`-linear categories, then the centres of `A` and `B` are
isomorphic as `R`-algebras; and if `A` and `B` are commutative then `A ≅ B`.

The invariant that mediates the comparison is *not* the full categorical centre
`CatCenter (DerivedCategory (ModuleCat A))` but its shift-compatible part
`CategoryTheory.CatCenter.shiftSubalgebra R (DerivedCategory (ModuleCat A)) ℤ`. The full centre
is too large to be comparable with the centre of `A`: over a field `k` every object of `D(k)`
is a direct sum of shifts of vector spaces and a natural endomorphism of the identity may use an
unrelated scalar in each degree, so `CatCenter (D(k))` is the product of a copy of `k` for every
`n : ℤ` rather than `k` itself. This is explained at the top of
`StacksFrontier/CategoryTheory/Center/Shift.lean`, which constructs the shift-compatible centre and
the machinery used below.

The comparison therefore runs

`Z(A) ≃ Z_shift(D(A)) ≃ Z_shift(D(B)) ≃ Z(B)`,

in three steps, of which the outer two are the same map read in opposite directions:

1. the canonical map `ModuleCat.centerToShiftCenterDerived R A : Z(A) →ₐ[R] Z_shift(D(A))`,
   which is defined unconditionally — a central element of `A` acts on each module, hence
   degreewise on each complex, and the degreewise action commutes with the shift — and is
   unconditionally injective, by `ModuleCat.centerToShiftCenterDerived_injective`;
2. transport along the equivalence, `CategoryTheory.CatCenter.transportShiftAlgEquiv`, which is
   unconditional and uses only that the functor of the equivalence is additive, `R`-linear and
   shift-commuting, not that it is triangulated;
3. step 1 for `B`, inverted.

## Tag 09SD is registered here only CONDITIONALLY

[Stacks, Tag 09SD](https://stacks.math.columbia.edu/tag/09SD) is **not** proved by this file. The
two declarations below carry `@[stacks 09SD]` — the attribute the base already placed on them —
but each still assumes one input, so neither is a delivery of the tag. Exactly one input is
missing: the
*surjectivity* of `ModuleCat.centerToShiftCenterDerived R A`, that is, that every
shift-compatible central element of `D(A)` is the degreewise action of a central element of `A`.
It enters `DerivedEquivalence.centerAlgEquiv` and `DerivedEquivalence.algEquiv` as the
hypotheses `hA` and `hB`, where it is assumed and not proved. Injectivity of the same map is
proved here, so this surjectivity is the whole of what is still owed, and it is a theorem of the
literature rather than an impossible demand — the references below assert exactly it — so the
hypothesis is satisfiable and the statements below are not vacuous.

That surjectivity is J. Rickard, *Derived equivalences as derived functors*, Proposition 9.2
(equivalently S. König and A. Zimmermann, *Derived equivalences for group rings*, Proposition
6.3.2) — the result the Stacks project itself defers to rather than proving. Obtaining it
requires the representability of coproduct-preserving exact endofunctors of `D(A)` in the form
`- ⊗ᴸ N` for a complex of bimodules `N`, which rests on the endomorphism-algebra machinery that
`StacksFrontier/Algebra/DifferentialGraded/Module/DerivedEquivalenceCompactGenerator.lean` records
as absent from this development. The tag stays unclaimed until that input lands.

## Main definitions

* `DerivedEquivalence.centerShiftCenterDerivedAlgEquiv`: granted the surjectivity above, the
  canonical map `Z(A) →ₐ[R] Z_shift(D(A))` is an isomorphism of `R`-algebras.
* `DerivedEquivalence.centerAlgEquiv`: the isomorphism `Z(A) ≅ Z(B)` of `R`-algebras.
* `DerivedEquivalence.algEquiv`: the isomorphism `A ≅ B` of `R`-algebras when `A` and `B` are
  commutative.

## Implementation notes

The hypotheses are surjectivity statements about the map that is actually constructed here,
rather than abstract isomorphisms produced out of nothing; this keeps the missing input visible
as one Prop-valued assumption about a named declaration, and makes the conclusions genuine
isomorphisms rather than non-emptiness statements.

Modules over `A` are taken in the universe of `A`, as `ModuleCat.centerAlgEquiv` requires, and
the two algebras are allowed to live in different universes. The hypothesis on the equivalence
is weaker than the source's: an `R`-linear equivalence of triangulated categories is in
particular an additive, `R`-linear, shift-commuting equivalence, which is all that is used.

## References

* [Stacks Project, Tag 09SD](https://stacks.math.columbia.edu/tag/09SD)
* J. Rickard, *Derived equivalences as derived functors*, Proposition 9.2.
* S. König and A. Zimmermann, *Derived equivalences for group rings*, Proposition 6.3.2.
-/

@[expose] public section

open CategoryTheory

namespace DerivedEquivalence

open scoped ModuleCat.Algebra

universe w₁ w₂ u v

section

variable (R : Type*) [CommRing R]
variable (A : Type u) [Ring A] [Algebra R A] [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
variable (B : Type v) [Ring B] [Algebra R B] [HasDerivedCategory.{w₂} (ModuleCat.{v} B)]

/-- **The centre of an algebra and the shift-compatible centre of its derived category.** The
canonical map `ModuleCat.centerToShiftCenterDerived` is always injective, so if it is also
surjective it is an isomorphism of `R`-algebras. Surjectivity is the one input this file assumes
rather than proves; see the note on Tag 09SD above. -/
noncomputable def centerShiftCenterDerivedAlgEquiv
    (h : Function.Surjective (ModuleCat.centerToShiftCenterDerived R A)) :
    Subalgebra.center R A ≃ₐ[R]
      CatCenter.shiftSubalgebra R (DerivedCategory (ModuleCat.{u} A)) ℤ :=
  AlgEquiv.ofBijective (ModuleCat.centerToShiftCenterDerived R A)
    ⟨ModuleCat.centerToShiftCenterDerived_injective R A, h⟩

/-- **Derived equivalent algebras have isomorphic centres.** Let `A` and `B` be algebras over a
commutative ring `R` whose derived categories are equivalent through an additive, `R`-linear,
shift-commuting equivalence `E`. If the canonical maps from `Z(A)` and from `Z(B)` to the
shift-compatible centres of `D(A)` and of `D(B)` are surjective — the step the Stacks project
defers to Rickard, assumed here and not proved — then `Z(A)` and `Z(B)` are isomorphic as
`R`-algebras, by transporting the shift-compatible centre along `E`.

The `@[stacks 09SD]` part string below says "the centre of `DerivedCategory (ModuleCat A)`". Read
that as the SHIFT-COMPATIBLE centre `CatCenter.shiftSubalgebra`, which is the correct object: the
full `CatCenter` of the derived category is too big, being `∏_{n : ℤ} k` over a field `k`, so the
hypothesis as originally stated here was unsatisfiable and has been replaced by surjectivity of
`ModuleCat.centerToShiftCenterDerived`. See the note on Tag 09SD at the top of this file. -/
@[stacks 09SD "Z(A) to Z(B) by transporting the shift-compatible centre along the equivalence"]
noncomputable def centerAlgEquiv
    (hA : Function.Surjective (ModuleCat.centerToShiftCenterDerived R A))
    (hB : Function.Surjective (ModuleCat.centerToShiftCenterDerived R B))
    (E : DerivedCategory (ModuleCat.{u} A) ≌ DerivedCategory (ModuleCat.{v} B))
    [E.functor.Additive] [E.functor.Linear R] [E.functor.CommShift ℤ] :
    (Subalgebra.center R A) ≃ₐ[R] (Subalgebra.center R B) :=
  (centerShiftCenterDerivedAlgEquiv R A hA).trans <|
    (CatCenter.transportShiftAlgEquiv (A := ℤ) E R).trans
      (centerShiftCenterDerivedAlgEquiv R B hB).symm

end

section

variable (R : Type*) [CommRing R]
variable (A : Type u) [CommRing A] [Algebra R A] [HasDerivedCategory.{w₁} (ModuleCat.{u} A)]
variable (B : Type v) [CommRing B] [Algebra R B] [HasDerivedCategory.{w₂} (ModuleCat.{v} B)]

/-- **Derived equivalent commutative algebras are isomorphic.** A commutative algebra is its own
centre, so the isomorphism of centres of `DerivedEquivalence.centerAlgEquiv` is an isomorphism
`A ≃ₐ[R] B` when `A` and `B` are commutative. The same surjectivity of
`ModuleCat.centerToShiftCenterDerived` is assumed and not proved.

As for `centerAlgEquiv`, read "the centre of `DerivedCategory (ModuleCat A)`" in the part string
below as the SHIFT-COMPATIBLE centre; the full `CatCenter` there is too big and the hypothesis as
originally stated was unsatisfiable. -/
@[stacks 09SD "the commutative case: A to B, a commutative algebra being its own centre"]
noncomputable def algEquiv
    (hA : Function.Surjective (ModuleCat.centerToShiftCenterDerived R A))
    (hB : Function.Surjective (ModuleCat.centerToShiftCenterDerived R B))
    (E : DerivedCategory (ModuleCat.{u} A) ≌ DerivedCategory (ModuleCat.{v} B))
    [E.functor.Additive] [E.functor.Linear R] [E.functor.CommShift ℤ] :
    A ≃ₐ[R] B :=
  (Subalgebra.topEquiv.symm.trans
      (Subalgebra.equivOfEq _ _ (Subalgebra.center_eq_top R A).symm)).trans <|
    (centerAlgEquiv R A B hA hB E).trans <|
      (Subalgebra.equivOfEq _ _ (Subalgebra.center_eq_top R B)).trans Subalgebra.topEquiv

end

end DerivedEquivalence

end
