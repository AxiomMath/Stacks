module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.FpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.FpqcLocal

/-!
# Universally open morphisms and universal homeomorphisms are fpqc local on the base

A morphism of schemes is universally open, or a universal homeomorphism, precisely when its base
changes along the members of an fpqc covering of the target are.

## Main results

* `AlgebraicGeometry.universallyOpen_isLocalAtTarget_fpqc`: universal openness is fpqc local on
  the base.
* `AlgebraicGeometry.universalHomeomorphism_eq_inf`: a universal homeomorphism is exactly a
  surjective, universally injective, universally open morphism.
* `AlgebraicGeometry.universalHomeomorphism_isLocalAtTarget_fpqc`: being a universal
  homeomorphism is fpqc local on the base.

## Implementation notes

Universal openness is Zariski local on the target, stable under base change, and descends along
surjective flat quasi-compact morphisms, so the criterion
`Stacks.Descent.isLocalAtTarget_fpqcPrecoverage` applies directly.

A homeomorphism is a continuous open bijection, and the three conditions are universal
separately, so a universal homeomorphism is the same thing as a morphism which is surjective,
universally injective and universally open. Surjectivity and universal injectivity are already
known to be fpqc local on the base, so the second statement follows from the first by an infimum.

## References

* [Stacks Project, Tag 02KT](https://stacks.math.columbia.edu/tag/02KT)
* [Stacks Project, Tag 0CEX](https://stacks.math.columbia.edu/tag/0CEX)
-/

@[expose] public section

open CategoryTheory MorphismProperty

namespace AlgebraicGeometry

universe u

/-- **Stacks Project, Tag 02KT.** Universal openness of morphisms of schemes is fpqc local on
the base. -/
@[stacks 02KT,
  ega "IV 2.4.3" "more general",
  ega "IV 2.6.4" "more general",
  sga "1 VIII 4.7" "more general",
  sga "3 VIB 2.1.2" "partial",
  sga "4 IV 8.5.5"]
instance universallyOpen_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget (@UniversallyOpen : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage :=
  have := Stacks.Descent.isStableUnderFlatBaseChange_of_isStableUnderBaseChange
    (@UniversallyOpen : MorphismProperty Scheme.{u})
  Stacks.Descent.isLocalAtTarget_fpqcPrecoverage _

/-- A morphism of schemes is a universal homeomorphism exactly when it is surjective,
universally injective and universally open. -/
@[ega "IV 2.4.5" "(ii)"]
theorem universalHomeomorphism_iff_surjective_and_universallyInjective_and_universallyOpen
    {X Y : Scheme.{u}} (f : X ⟶ Y) :
    UniversalHomeomorphism f ↔
      Surjective f ∧ UniversallyInjective f ∧ UniversallyOpen f := by
  constructor
  · intro hf
    have h := hf.universally_isHomeomorph
    refine ⟨⟨(h _ _ _ IsPullback.of_id_snd).surjective⟩, ?_, ?_⟩
    · rw [universallyInjective_iff]
      intro X' Y' i₁ i₂ f' hp
      exact (h i₁ i₂ f' hp).injective
    · rw [universallyOpen_iff]
      intro X' Y' i₁ i₂ f' hp
      exact (h i₁ i₂ f' hp).isOpenMap
  · rintro ⟨hsurj, hinj, hopen⟩
    refine ⟨?_⟩
    intro X' Y' i₁ i₂ f' hp
    have _ : Surjective f' := MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip hsurj
    have _ : UniversallyInjective f' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip hinj
    have _ : UniversallyOpen f' :=
      MorphismProperty.IsStableUnderBaseChange.of_isPullback hp.flip hopen
    exact ⟨f'.continuous, f'.isOpenMap,
      ⟨f'.injective, (show Surjective f' from inferInstance).surj⟩⟩

/-- Being a universal homeomorphism is the conjunction of surjectivity, universal injectivity
and universal openness. -/
theorem universalHomeomorphism_eq_inf :
    (show MorphismProperty Scheme.{u} from @UniversalHomeomorphism) =
      (show MorphismProperty Scheme.{u} from
        @Surjective ⊓ @UniversallyInjective ⊓ @UniversallyOpen) := by
  ext X Y f
  change UniversalHomeomorphism f ↔
    (Surjective f ∧ UniversallyInjective f) ∧ UniversallyOpen f
  simpa only [and_assoc] using
    universalHomeomorphism_iff_surjective_and_universallyInjective_and_universallyOpen f

/-- **Stacks Project, Tag 0CEX.** Being a universal homeomorphism of schemes is fpqc local on
the base. -/
@[stacks 0CEX,
  ega "IV 2.6.2" "(iv), special case",
  ega "IV 2.6.4" "more general",
  sga "1 VIII 4.7" "more general",
  sga "4 IV 8.5.5"]
instance universalHomeomorphism_isLocalAtTarget_fpqc :
    MorphismProperty.IsLocalAtTarget
      (@UniversalHomeomorphism : MorphismProperty Scheme.{u}) Scheme.fpqcPrecoverage := by
  have : MorphismProperty.IsLocalAtTarget
      (@Surjective ⊓ @UniversallyInjective : MorphismProperty Scheme.{u})
      Scheme.fpqcPrecoverage := .inf _ _
  rw [universalHomeomorphism_eq_inf]
  exact .inf _ _

end AlgebraicGeometry

end
