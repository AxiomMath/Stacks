module

public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.BaseChangeComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Relative

/-!
# Base change of a relative cycle is a relative cycle

Let `f : X ⟶ S` be locally of finite type with `S` locally Noetherian, let `g : S' ⟶ S` be an
arbitrary morphism with `S'` locally Noetherian and let `α` be a relative `r`-cycle on `X/S`.
This file proves that the base change `g^*α` is a relative `r`-cycle on `X'/S'`, where
`X' = X ×_S S'`. This is the base change clause of
[Stacks, Tag 0H51](https://stacks.math.columbia.edu/tag/0H51).

## Main results

* `Stacks.Chow.compBaseChangeFiberIso_hom_eq_fiberRestrict` — the canonical isomorphism of
  fibres `Stacks.Chow.compBaseChangeFiberIso` is the fibre morphism induced by the pasting
  isomorphism of the total spaces.
* `Stacks.Chow.baseChangeFamily_baseChangeFamily_of_locallyOfFiniteType` — base change along `g`
  followed by base change along `h' : T ⟶ S'` is base change along `h' ≫ g`, read through the
  pasting isomorphism `(X ×_S S') ×_{S'} T ≅ X ×_S T`, with no hypothesis on either morphism of
  the composite.
* `Stacks.Chow.isRelativeCycle_baseChangeFamily` — **Stacks 0H51**, the base change clause: the
  base change of a relative `r`-cycle along an arbitrary morphism of locally Noetherian bases is
  a relative `r`-cycle.

## Implementation notes

The two-step compatibility needs no hypothesis on either morphism: the multiplicativity of the
base-change multiplicities, Tag 0FVP, is `Stacks.Chow.baseChangeFamily_apply_comp` for an
arbitrary pair of residue field extensions, hence so is the coefficient identity
`Stacks.Chow.baseChangeFamily_apply_compBaseChangeFiberIso`, and the isomorphism of fibres
appearing there is definitionally the transport `Stacks.Chow.fiberCycleRestrict` along the
pasting isomorphism. The specialization map commutes with that transport by the open-immersion
case of Tag 0H4L, `Stacks.Chow.specializationCycle_fiberCycleRestrict`.

## References

* [Stacks Project, Lemma 0H51](https://stacks.math.columbia.edu/tag/0H51)
* [Stacks Project, Section 0H4N](https://stacks.math.columbia.edu/tag/0H4N)
* [Stacks Project, Lemma 0H4X](https://stacks.math.columbia.edu/tag/0H4X)
* [Stacks Project, Lemma 0H4L](https://stacks.math.columbia.edu/tag/0H4L)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

section Comparison

variable {X S S' T : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (g : S' ⟶ S) (h' : T ⟶ S')

omit [LocallyOfFiniteType f] in
/-- The canonical isomorphism `Stacks.Chow.compBaseChangeFiberIso` between the fibre over `t` of
the twofold base change `(X ×_S S') ×_{S'} T` and the fibre over `t` of `X ×_S T` is the fibre
morphism induced by the pasting isomorphism `(X ×_S S') ×_{S'} T ≅ X ×_S T` of the total
spaces. -/
theorem compBaseChangeFiberIso_hom_eq_fiberRestrict (t : T) :
    (compBaseChangeFiberIso f g h' t).hom =
      fiberRestrict (pullback.snd f (h' ≫ g)) (pullback.snd (pullback.snd f g) h')
        (pullbackLeftPullbackSndIso f g h').hom
        (pullbackLeftPullbackSndIso_hom_snd f g h') t :=
  rfl

/-- **Stacks Project, Tag 0H4X (2), the composition of two base changes.** Base change of a
family of cycles on fibres along `g : S' ⟶ S` followed by base change along `h' : T ⟶ S'` is
base change along `h' ≫ g`, read through the pasting isomorphism
`(X ×_S S') ×_{S'} T ≅ X ×_S T`. No hypothesis is placed on `g` or on `h'`. -/
theorem baseChangeFamily_baseChangeFamily_of_locallyOfFiniteType (r : ℕ)
    (α : FamilyOfCycles f r) (t : T) :
    baseChangeFamily (pullback.snd f g) h' r (baseChangeFamily f g r α) t =
      fiberCycleRestrict (pullback.snd f (h' ≫ g)) (pullback.snd (pullback.snd f g) h')
        (pullbackLeftPullbackSndIso f g h').hom
        (pullbackLeftPullbackSndIso_hom_snd f g h') t r
        (baseChangeFamily f (h' ≫ g) r α t) := by
  refine Subtype.ext (Function.locallyFinsuppWithin.ext fun y => ?_)
  rw [fiberCycleRestrict_apply, ← compBaseChangeFiberIso_hom_eq_fiberRestrict f g h' t]
  exact baseChangeFamily_apply_compBaseChangeFiberIso f g h' r t α y

end Comparison

/-- **Stacks Project, Lemma 0H51, the base change clause.** The base change of a relative
`r`-cycle along an arbitrary morphism `g : S' ⟶ S` of locally Noetherian schemes is a relative
`r`-cycle on `X ×_S S'` over `S'`. -/
@[stacks 0H51 "base change along an arbitrary morphism of locally Noetherian bases"]
theorem isRelativeCycle_baseChangeFamily {X S S' : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [IsLocallyNoetherian S] [IsLocallyNoetherian S'] (g : S' ⟶ S)
    (r : ℕ) {α : FamilyOfCycles f r} (hα : IsRelativeCycle f r α) :
    IsRelativeCycle (pullback.snd f g) r (baseChangeFamily f g r α) := by
  intro R _ _ _ c
  rw [baseChangeFamily_baseChangeFamily_of_locallyOfFiniteType f g c r α
      (genericPoint (Spec (.of R))),
    baseChangeFamily_baseChangeFamily_of_locallyOfFiniteType f g c r α
      (IsLocalRing.closedPoint R),
    specializationCycle_fiberCycleRestrict (pullback.snd f (c ≫ g))
      (pullback.snd (pullback.snd f g) c) (pullbackLeftPullbackSndIso f g c).hom
      (pullbackLeftPullbackSndIso_hom_snd f g c) r
      (baseChangeFamily f (c ≫ g) r α (genericPoint (Spec (.of R)))),
    hα R (c ≫ g)]

end Stacks.Chow

end
