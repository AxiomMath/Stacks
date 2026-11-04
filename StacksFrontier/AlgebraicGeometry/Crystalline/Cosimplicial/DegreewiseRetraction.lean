module

public import Mathlib.Algebra.Group.Hom.Defs
public import Mathlib.Algebra.Group.Basic
public import Mathlib.Tactic.Abel

/-!
# Degreewise deformation retractions of complexes of abelian groups

A map of complexes `ι : C ⟶ C'` of abelian groups indexed by `ℕ` is a *deformation retract* when
it has a retraction `π` which is a map of complexes, `π ∘ ι = id`, and `ι ∘ π` is homotopic to
the identity of `C'`.  This is the shape in which the completed clause of
[Stacks, Lemma 60.21.2, Tag 07LD] produces its conclusion, written degree by degree with
additive maps, as `Crystalline.CompletedDeRham.exists_twistedHomotopyEquiv` does.

This module packages that data as `Crystalline.DegreewiseRetraction` and proves the one formal
property of it that its consumers need: it **transports along isomorphisms** of the two
complexes compatible with `ι` (`Crystalline.DegreewiseRetraction.transport`).  The proof of
[Stacks, Proposition 60.21.3, Tag 07LG] obtains the retraction for the base change
`M ⊗^∧_D Ω^*_D ⟶ M ⊗^∧_D Ω^*_{D⟨ξ⟩^∧}` and needs it for the row comparison
`M(0) ⊗^∧_{D(0)} Ω^*_{D(0)} ⟶ M(b) ⊗^∧_{D(b)} Ω^*_{D(b)}` of the double complex, which is the
same map read through isomorphisms.

## References

* [Stacks Project, Lemma 60.21.2, Tag 07LD](https://stacks.math.columbia.edu/tag/07LD)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

universe u v u' v'

namespace Crystalline

/-- **A degreewise deformation retraction of a map of complexes.**  `C` and `C'` are graded
abelian groups with differentials `d`, `d'`, and `ι` is a family of additive maps, which in the
applications is a map of complexes.  The data is a retraction `π` commuting with the
differentials, and a homotopy `h` from `ι ∘ π` to the identity of `C'`. -/
structure DegreewiseRetraction {C : ℕ → Type u} {C' : ℕ → Type v} [∀ i, AddCommGroup (C i)]
    [∀ i, AddCommGroup (C' i)] (d : ∀ i, C i →+ C (i + 1)) (d' : ∀ i, C' i →+ C' (i + 1))
    (ι : ∀ i, C i →+ C' i) where
  /-- The retraction. -/
  π : ∀ i, C' i →+ C i
  /-- The homotopy. -/
  h : ∀ i, C' (i + 1) →+ C' i
  /-- The retraction commutes with the differentials. -/
  d_π : ∀ (i : ℕ) (y : C' i), d i (π i y) = π (i + 1) (d' i y)
  /-- The retraction retracts `ι`. -/
  π_ι : ∀ (i : ℕ) (x : C i), π i (ι i x) = x
  /-- The homotopy identity in degree zero: `h ∘ d' + ι ∘ π = id`. -/
  h_zero : ∀ x : C' 0, h 0 (d' 0 x) + ι 0 (π 0 x) = x
  /-- The homotopy identity in positive degree: `d' ∘ h + h ∘ d' + ι ∘ π = id`. -/
  h_succ : ∀ (i : ℕ) (x : C' (i + 1)),
    d' i (h i x) + h (i + 1) (d' (i + 1) x) + ι (i + 1) (π (i + 1) x) = x

namespace DegreewiseRetraction

variable {C : ℕ → Type u} {C' : ℕ → Type v} [∀ i, AddCommGroup (C i)] [∀ i, AddCommGroup (C' i)]
  {d : ∀ i, C i →+ C (i + 1)} {d' : ∀ i, C' i →+ C' (i + 1)} {ι : ∀ i, C i →+ C' i}
  {E : ℕ → Type u'} {E' : ℕ → Type v'} [∀ i, AddCommGroup (E i)] [∀ i, AddCommGroup (E' i)]
  {e : ∀ i, E i →+ E (i + 1)} {e' : ∀ i, E' i →+ E' (i + 1)} {κ : ∀ i, E i →+ E' i}

/-- **A deformation retraction transports along isomorphisms of complexes compatible with the
maps.**  Let `u : C ≅ E` and `u' : C' ≅ E'` be degreewise additive isomorphisms (`u` with inverse
`uInv`, `u'` with inverse `u'Inv`) commuting with the differentials, with `u' ∘ ι = κ ∘ u`.  A
deformation retraction of `κ` gives one of `ι`: the retraction `uInv ∘ π ∘ u'` and the homotopy
`u'Inv ∘ h ∘ u'`. -/
def transport (R : DegreewiseRetraction e e' κ)
    (u : ∀ i, C i →+ E i) (uInv : ∀ i, E i →+ C i)
    (u' : ∀ i, C' i →+ E' i) (u'Inv : ∀ i, E' i →+ C' i)
    (huInv : ∀ (i : ℕ) (x : C i), uInv i (u i x) = x)
    (huInv' : ∀ (i : ℕ) (y : E i), u i (uInv i y) = y)
    (hu'Inv : ∀ (i : ℕ) (x : C' i), u'Inv i (u' i x) = x)
    (hu'Inv' : ∀ (i : ℕ) (y : E' i), u' i (u'Inv i y) = y)
    (hud : ∀ (i : ℕ) (y : E i), d i (uInv i y) = uInv (i + 1) (e i y))
    (hu'd : ∀ (i : ℕ) (x : C' i), u' (i + 1) (d' i x) = e' i (u' i x))
    (hι : ∀ (i : ℕ) (x : C i), u' i (ι i x) = κ i (u i x)) :
    DegreewiseRetraction d d' ι where
  π i := (uInv i).comp ((R.π i).comp (u' i))
  h i := (u'Inv i).comp ((R.h i).comp (u' (i + 1)))
  d_π i y := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [hud, R.d_π, hu'd]
  π_ι i x := by
    simp only [AddMonoidHom.coe_comp, Function.comp_apply]
    rw [hι, R.π_ι, huInv]
  h_zero x := by
    have hinj : Function.Injective (u' 0) := fun a b hab => by
      have := congrArg (u'Inv 0) hab
      rwa [hu'Inv, hu'Inv] at this
    apply hinj
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, map_add]
    rw [hu'Inv', hι, huInv', hu'd]
    exact R.h_zero (u' 0 x)
  h_succ i x := by
    have hinj : Function.Injective (u' (i + 1)) := fun a b hab => by
      have := congrArg (u'Inv (i + 1)) hab
      rwa [hu'Inv, hu'Inv] at this
    apply hinj
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, map_add]
    rw [hu'd, hu'Inv', hu'Inv', hι, huInv', hu'd]
    exact R.h_succ i (u' (i + 1) x)

end DegreewiseRetraction

end Crystalline

end
