module

public import Mathlib.AlgebraicGeometry.Morphisms.Etale
public import Mathlib.AlgebraicGeometry.Morphisms.FlatMono
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Diagonal

/-!
# Open immersions among étale morphisms

A morphism of schemes is an open immersion exactly when it is universally injective and étale,
and exactly when it is a flat monomorphism which is locally of finite presentation.

## Main results

* `AlgebraicGeometry.tfae_isOpenImmersion` is the three-way equivalence of Tag 025G.

## Implementation notes

Two of the three implications are available: an open immersion is a monomorphism, hence
universally injective, and it is étale; and a flat monomorphism locally of finite presentation
is an open immersion by `AlgebraicGeometry.IsOpenImmersion.of_flat_of_mono`, which is Mathlib's
fpqc-descent proof of Tag 06NC together with the openness of a flat morphism locally of finite
presentation.

What is proved here is the passage from "universally injective and étale" to "flat
monomorphism". Flatness and local finite presentation are part of étaleness. For the
monomorphism condition the source argument cites Tag 05VH; the route taken instead is through
the diagonal, which is where both hypotheses meet: the diagonal of an étale — indeed of any
unramified — morphism is an open immersion (Tag 02GE,
`AlgebraicGeometry.Unramified.isOpenImmersion_diagonal`), universal injectivity says exactly
that the diagonal is surjective (`AlgebraicGeometry.UniversallyInjective.iff_diagonal`), a
surjective open immersion is an isomorphism, and a morphism whose diagonal is an isomorphism is
a monomorphism.

The converse direction, that every open immersion is étale, is Mathlib's
`AlgebraicGeometry.Etale.instOfIsOpenImmersion`, which is what supplies the étaleness in the
first implication; the tag for it is recorded on that declaration below.

## References

* [Stacks Project, Tag 025G](https://stacks.math.columbia.edu/tag/025G)
* [Stacks Project, Tag 02GE](https://stacks.math.columbia.edu/tag/02GE)
* [Stacks Project, Tag 02GP](https://stacks.math.columbia.edu/tag/02GP)
* [Stacks Project, Tag 06NC](https://stacks.math.columbia.edu/tag/06NC)
-/

add_to_stacks 02GP AlgebraicGeometry.Etale.instOfIsOpenImmersion

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- **Stacks 025G.** For a morphism of schemes, being an open immersion, being universally
injective and étale, and being a flat monomorphism locally of finite presentation are
equivalent. -/
@[ega "IV 17.9.1",
  sga "1 I 5.1" "more general",
  sga "3 X 3.7" "partial",
  sga "3 XXII 5.4.10" "more general",
  sga "7 IX 3.1.3" "more general"]
theorem tfae_isOpenImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) :
    List.TFAE [IsOpenImmersion f,
      UniversallyInjective f ∧ Etale f,
      Flat f ∧ Mono f ∧ LocallyOfFinitePresentation f] := by
  tfae_have 1 → 2 := fun _ ↦ ⟨inferInstance, inferInstance⟩
  tfae_have 2 → 3 := by
    rintro ⟨hui, het⟩
    have hunr : Unramified f := inferInstance
    have hoi : IsOpenImmersion (pullback.diagonal f) := inferInstance
    have hepi : Epi (pullback.diagonal f).base :=
      (TopCat.epi_iff_surjective _).mpr ((UniversallyInjective.iff_diagonal f).mp hui).1
    have : IsIso (pullback.diagonal f) :=
      (isIso_iff_isOpenImmersion_and_epi_base _).mpr ⟨hoi, hepi⟩
    exact ⟨inferInstance, (pullback.isIso_diagonal_iff f).mp inferInstance, inferInstance⟩
  tfae_have 3 → 1 := by
    rintro ⟨hflat, hmono, hfp⟩
    exact IsOpenImmersion.of_flat_of_mono f
  tfae_finish

end AlgebraicGeometry

end
