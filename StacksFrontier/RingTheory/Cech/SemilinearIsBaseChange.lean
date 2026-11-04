module

public import StacksFrontier.RingTheory.Cech.GeneralReindexBaseChange
public import StacksFrontier.RingTheory.Cech.SemilinearBaseChange

/-!
# The two spellings of the change-of-rings map of a Čech complex agree

The library carries the change of rings on the terms of an extended alternating Čech complex
twice. `Stacks.CechSemilinear.termMap` takes a ring map `φ : A → B` together with two families
`f` in `A` and `g` in `B` and a proof that `φ ∘ f = g` *pointwise*, and produces a `φ`-semilinear
map `C^p(f; A) → C^p(g; B)`; it is the form a presheaf of Čech complexes needs, because there
the target family is the one attached to the target object and is given, not constructed.
`Stacks.CechRingBaseChange.termMap` takes only `φ` and `f` and lands in the Čech term of the
image family `φ ∘ f`; it is the form the comparison maps `Cech.genRingTerm` of
`GeneralReindexBaseChange.lean` are built from.

Nothing connected them. This file does: at `g = φ ∘ f` the two are the same map
(`Stacks.CechSemilinear.termMap_eq_termMap`), and consequently the comparison map of
`Cech.genRingTerm` factors through the semilinear spelling
(`Stacks.CechSemilinear.genTerm_comp_termMap`). That is what lets a map out of a presheaf of
Čech complexes — whose restriction maps are the semilinear spelling — be computed by the
`genRingTerm` calculus, which is how one compares such a presheaf with a presheaf assembled out
of `Cech.cechGenRingMap`.

Both maps are `φ`-semilinear out of a localization and agree on the fractions with denominator
one, so they agree: that is `Stacks.CechSemilinear.locHom_ext`, whose injectivity hypothesis is
`Stacks.CechRingBaseChange.isUnit_algebraMap_restrictedMod`.

## Main results

* `Stacks.CechSemilinear.locMap_eq_modMap`: the two spellings agree on a single localization.
* `Stacks.CechSemilinear.termMap_eq_termMap`: the two spellings agree on the degree-`p` term.
* `Stacks.CechSemilinear.genTerm_comp_termMap`: the comparison map `Cech.genRingTerm` is the
  semilinear change of rings followed by the same-ring comparison.

## References

* [Stacks Project, Tag 099D](https://stacks.math.columbia.edu/tag/099D)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace Stacks.CechSemilinear

variable {A B : Type u} [CommRing A] [CommRing B] {r s : ℕ}

/-- The change of rings on a single localization, in the base-change spelling, read as a
`φ`-semilinear map. The `A`-action on the restriction of scalars along `φ` is the `B`-action
along `φ`, so the two laws are the same law. -/
def modMapₛₗ (φ : A →+* B) (f : Fin r → A) (t : Finset (Fin r)) :
    Cech.cechMod f A t →ₛₗ[φ] Cech.cechMod (CechRingBaseChange.mapFamily φ f) B t where
  toFun := CechRingBaseChange.modMap φ f t
  map_add' := map_add _
  map_smul' a x := (CechRingBaseChange.modMap φ f t).map_smul a x

/-- **The two spellings agree on a single localization.** Both are `φ`-semilinear maps out of
`A_{f_t}` sending a fraction with denominator one to the image of its numerator, and such a map
is unique. -/
theorem locMap_eq_modMap (φ : A →+* B) (f : Fin r → A) (t : Finset (Fin r))
    (h : Cech.cechSub f t ≤ (Cech.cechSub (CechRingBaseChange.mapFamily φ f) t).comap φ)
    (x : Cech.cechMod f A t) :
    locMap φ (Cech.cechSub f t) (Cech.cechSub (CechRingBaseChange.mapFamily φ f) t) h x =
      CechRingBaseChange.modMap φ f t x := by
  have hinj : ∀ y : Cech.cechSub f t,
      Function.Injective (fun z : Cech.cechMod (CechRingBaseChange.mapFamily φ f) B t =>
        φ (y : A) • z) := by
    intro y z₁ z₂ hz
    refine ((Module.End.isUnit_iff _).1
      (CechRingBaseChange.isUnit_algebraMap_restrictedMod φ f (le_refl t) y)).injective ?_
    exact hz
  exact congrFun (congrArg (fun m : Cech.cechMod f A t →ₛₗ[φ]
      Cech.cechMod (CechRingBaseChange.mapFamily φ f) B t => (m : _ → _))
    (locHom_ext φ (Cech.cechSub f t)
      (locMap φ (Cech.cechSub f t) (Cech.cechSub (CechRingBaseChange.mapFamily φ f) t) h)
      (modMapₛₗ φ f t) hinj fun m =>
        (locMap_mkLinearMap φ _ _ h m).trans
          (CechRingBaseChange.modMap_mkLinearMap φ f t m).symm)) x

/-- **The two spellings agree on the degree-`p` term.** -/
theorem termMap_eq_termMap (φ : A →+* B) (f : Fin r → A)
    (hfg : ∀ i, φ (f i) = CechRingBaseChange.mapFamily φ f i) (p : ℕ)
    (x : Cech.cechTerm f A p) :
    termMap φ f (CechRingBaseChange.mapFamily φ f) hfg p x =
      CechRingBaseChange.termMap φ f p x := by
  ext t
  refine Eq.trans ?_ (CechRingBaseChange.termMap_component φ f p x t).symm
  exact locMap_eq_modMap φ f t.1
    (cechSub_le_comap φ f (CechRingBaseChange.mapFamily φ f) hfg t.1) (x t)

/-- **The comparison map of `Cech.genRingTerm` is the semilinear change of rings followed by the
same-ring comparison.** This is the form a map out of a presheaf of Čech complexes is computed
in: the restriction maps of such a presheaf are `Stacks.CechSemilinear.termMap`, while the
comparison maps assembled out of `Cech.cechGenRingMap` are `Cech.genRingTerm`. -/
theorem genTerm_comp_termMap (φ : A →+* B) (f : Fin r → A) (g : Fin r → B)
    (hfg : ∀ i, φ (f i) = g i) (hg : CechRingBaseChange.mapFamily φ f = g) {t : ℕ}
    (u : Fin t → B) (α : Fin t → Fin r) (hα : ∀ j, ∃ n : ℕ, g (α j) ∣ u j ^ n)
    (hα' : ∀ j, ∃ n : ℕ, φ (f (α j)) ∣ u j ^ n) (p : ℕ) (x : Cech.cechTerm f A p) :
    Cech.genTerm g u α hα B p (termMap φ f g hfg p x) = Cech.genRingTerm φ f u α hα' p x := by
  subst hg
  exact congrArg (Cech.genTerm (CechRingBaseChange.mapFamily φ f) u α hα B p)
    (termMap_eq_termMap φ f hfg p x)

end Stacks.CechSemilinear

end
