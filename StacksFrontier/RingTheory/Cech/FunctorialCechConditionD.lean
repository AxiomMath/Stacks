module

public import StacksFrontier.RingTheory.Cech.IdealCechComplexRestriction

/-!
# Condition (d) of tag 099D, for a Čech complex

Condition (d) of tag 099D asks, of a complex `K(A, I)` attached to a pair of a ring and a finitely
generated ideal, that for *every* finite family `f₁, …, f_r` generating `I` there be an
isomorphism in `D(A)` from the extended alternating Čech complex on `f₁, …, f_r` to `K(A, I)`,
compatible with the augmentations onto `A`. It is a condition in the derived category, not between
complexes.

This file records that for `K(A, I)` the extended Čech complex of *one* chosen generating family
`g₁, …, g_s` the condition holds, and holds with no work: it is exactly the independence of the
Čech object of the chosen finite generating set,
`Stacks.IdealCechComplex.canonicalHom_comp_augmentationHom`, whose morphism is moreover the unique
one over `A` and therefore canonical
(`Stacks.IdealCechComplex.eq_canonicalHom`, `Stacks.IdealCechComplex.canonicalHom_comp`).

The point of stating it is to separate the two halves of tag 099D. Conditions (c) and (d) of
`Stacks.LocalCohomology.FunctorialCechData` are conditions in a derived category, and for them a
`D(A)`-level comparison such as `canonicalIso` is enough — this file is the proof for (d). The
data (1)–(3) and the conditions (a), (b) are statements about complexes and about equalities of
maps of complexes on the nose, and no `D(A)`-level comparison can supply them; nor can any choice
of generating family, by `Stacks.FunctorialCechFamily.not_transportedFamily`.

## Main results

* `Stacks.FunctorialCechFamily.exists_extendedCechObject_iso_over_augmentation` — condition (d) of
  tag 099D for the extended Čech complex of a chosen generating family.

## Implementation notes

The statement is the body of the field
`Stacks.LocalCohomology.FunctorialCechData.exists_cech_iso` with `complex A I hI` replaced by
`Stacks.LocalCohomology.extendedCechComplex g (ModuleCat.of A A)` and `augmentation A I hI` by
`Stacks.LocalCohomology.extendedCechAugmentation g (ModuleCat.of A A)`, so that it can be read off
against that field. It is deliberately *not* stated as a lemma about `FunctorialCechData`, of
which the library has no term.

No `@[stacks 099D]` attribute is attached. Condition (d) is a condition on a datum, and this file
provides no datum: the complex here is attached to a generating family, not to the pair.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.LocalCohomology

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.FunctorialCechFamily

/-- **Condition (d) of tag 099D, for the extended Čech complex of a chosen generating family.**
If `g₁, …, g_s` and `f₁, …, f_r` both generate the finitely generated ideal `I ⊆ A`, there is an
isomorphism in `D(A)` from the extended alternating Čech complex on `f₁, …, f_r` to the one on
`g₁, …, g_s`, carrying the augmentation of the former onto the augmentation of the latter.

This is the field `Stacks.LocalCohomology.FunctorialCechData.exists_cech_iso`, read at
`complex A I hI = extendedCechComplex g (ModuleCat.of A A)`. The isomorphism is
`Stacks.IdealCechComplex.canonicalIso`, which lives in `D(A)`; condition (d), being itself a
condition in `D(A)`, asks for nothing more. -/
@[stacks 099D "condition (d) for a pair with a chosen finite generating family"]
theorem exists_extendedCechObject_iso_over_augmentation {A : Type u} [CommRing A] {r s : ℕ}
    (f : Fin r → A) (g : Fin s → A) (I : Ideal A)
    (hf : Ideal.span (Set.range f) = I) (hg : Ideal.span (Set.range g) = I) :
    ∃ e : extendedCechObject f (ModuleCat.of A A) ≅
        DerivedCategory.Q.obj (extendedCechComplex g (ModuleCat.of A A)),
      e.hom ≫ DerivedCategory.Q.map (extendedCechAugmentation g (ModuleCat.of A A)) ≫
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app
            (ModuleCat.of A A)).inv =
        extendedCechAugmentationHom f (ModuleCat.of A A) :=
  ⟨IdealCechComplex.canonicalIso f g (ModuleCat.of A A) (hf.trans hg.symm),
    IdealCechComplex.canonicalHom_comp_augmentationHom f g (ModuleCat.of A A)
      (hf.trans hg.symm)⟩

end Stacks.FunctorialCechFamily

end
