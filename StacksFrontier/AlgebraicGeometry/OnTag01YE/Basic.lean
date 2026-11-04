module

public import StacksFrontier.AlgebraicGeometry.ConfinedDevissage.KilledSupport

/-!
# Tag 01YG on the conclusion of [Stacks, Tag 01YE] and nothing else

`Stacks.AlgebraicGeometry.IrreducibleDevissage.property_of_hasKilledIdealCoproductSub`
(`../IrreducibleDevissage/Coproduct.lean`) is the statement of Tag 01YG verbatim on the single
hypothesis
`Stacks.AlgebraicGeometry.IrreducibleDevissage.HasKilledIdealCoproductSub`, and the
implementation notes there record that hypothesis as **strictly stronger** than the conclusion of
[Stacks, Tag 01YE] in two respects: it asks for the support of a cokernel rather than an open on
which a monomorphism is invertible, and it asks for coherence of `i_* I` rather than of
`i_*(I ^ {⊕ r})`.

Both of those gaps are closed by `ConfinedDevissage.supp_cokernel_ssubset_of_killed` and
`ConfinedDevissage.isCoherent_pushforward_of_isCoherent_pushforward_coproduct`, but only for the
**confined** predicate `ConfinedDevissage.HasKilledIdealGenericIsoSubIn`, which carries
`Set.range i.base ⊆ Z` because that is the form [Stacks, Tag 01YH] consumes. Tag 01YG's `hideal`
hypothesis quantifies over *every* integral closed subscheme with no containment condition, so the
hypothesis Tag 01YG wants is the unconfined one.

`HasKilledIdealGenericIsoSub` is the conclusion of [Stacks, Tag 01YE] with no containment
condition, and Tag 01YG follows from it with nothing added. The confined predicate implies the
unconfined one by forgetting the containment, so Tag 01YG also follows from
`ConfinedDevissage.HasKilledIdealGenericIsoSubIn`.

## Main definitions

* `Stacks.AlgebraicGeometry.Tag01YGOnTag01YE.HasKilledIdealGenericIsoSub`: **the conclusion of
  [Stacks, Tag 01YE], unconfined** — a coherent quasi-coherent module annihilated affine-locally
  by the ideal sheaf of an irreducible closed set `Z` receives a monomorphism from the direct
  image, along a closed immersion from an integral scheme, of a finite coproduct of copies of a
  quasi-coherent ideal sheaf, and the monomorphism becomes invertible on an open neighbourhood
  of some point of `Z`.

## Main results

* `hasKilledIdealGenericIsoSub_of_hasKilledIdealGenericIsoSubIn`: the confined predicate implies
  the unconfined one.
* `hasKilledIdealDevissage_of_hasKilledIdealDevissageIn`: the confined dévissage implies the
  unconfined one, the confined quotient class being contained in the unconfined one.
* `hasKilledIdealDevissage_of_hasKilledIdealGenericIsoSub`: **step 4 of the proof of
  [Stacks, Tag 01YF], unconfined, from the conclusion of [Stacks, Tag 01YE] alone.**
* `property_of_hasKilledIdealGenericIsoSub`: **the statement of Tag 01YG verbatim with the
  conclusion of [Stacks, Tag 01YE] as its one added hypothesis**, nothing strengthened.
* `property_of_hasKilledIdealGenericIsoSubIn`: the same on the confined form of that conclusion.

## Implementation notes

**The proof is the unconfined mirror of
`ConfinedDevissage.hasKilledIdealDevissageIn_of_hasKilledIdealGenericIsoSubIn`**,
with `Stacks.AlgebraicGeometry.IrreducibleDevissage.isIdealPushforward_or_supp_ssubset_of_iso'`
in place of the confined class and
`Stacks.AlgebraicGeometry.IrreducibleDevissage.isIdealPushforward_pushforward` in place of its
confined counterpart. The multiplicity `r = 0` is separated exactly as it is there: the sub is
then a zero module, the quotient map is an isomorphism, and `Q` itself is supported strictly
inside `Z`, which is a one-step filtration on the right disjunct of the class with no ideal
sheaf used at all.

**The hypothesis of Tag 01YE is on the stalk, this one is affine-local.** Tag 01YE asks only
that the stalk of `Q` at the generic point be annihilated by the maximal ideal, which is
*weaker* than affine-local annihilation by the ideal sheaf of `Z`. So the predicate below asks
for 01YE's conclusion at fewer modules than Tag 01YE delivers it, and Tag 01YE supplies it as
soon as affine-local annihilation is known to imply that stalk condition. That implication is
not proved in this file.

## References

* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 01YF](https://stacks.math.columbia.edu/tag/01YF)
* [Stacks Project, Tag 01YG](https://stacks.math.columbia.edu/tag/01YG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits SheafOfModules TopologicalSpace
open Stacks.AlgebraicGeometry.HigherDirectImageCoherent
open Stacks.AlgebraicGeometry.DevissageBounded
open Stacks.AlgebraicGeometry.IrreducibleDevissage

universe u

namespace Stacks.AlgebraicGeometry.Tag01YGOnTag01YE

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-! ### The conclusion of [Stacks, Tag 01YE], unconfined -/

/-- **The conclusion of [Stacks, Tag 01YE], with no containment condition on the subscheme.** A
coherent quasi-coherent module `Q` annihilated affine-locally by the ideal sheaf of an
irreducible closed set `Z` receives a monomorphism from the direct image, along a closed
immersion from an integral scheme, of a finite coproduct of copies of a quasi-coherent ideal
sheaf, and that monomorphism becomes invertible on an open neighbourhood of some point of `Z`.

This is `ConfinedDevissage.HasKilledIdealGenericIsoSubIn` with
`Set.range i.base ⊆ Z` dropped. The confined form is what [Stacks, Tag 01YH] consumes; the
`hideal` hypothesis of Tag 01YG has no containment condition, so the unconfined form is what
Tag 01YG wants. -/
def HasKilledIdealGenericIsoSub (X : Scheme.{u}) : Prop :=
  ∀ Z : Closeds X, IsIrreducible (Z : Set X) →
    ∀ Q : X.Modules, Q.IsQuasicoherent → Q.IsCoherent →
      (∀ U : X.affineOpens, (IdealPowerSmul.closedIdeal Z).ideal U •
          (⊤ : Submodule Γ(X, U.1) Γ(Q, U.1)) = ⊥) →
      ∃ (W : Scheme.{u}) (i : W ⟶ X) (_ : IsClosedImmersion i) (_ : IsIntegral W) (r : ℕ)
        (I : (SheafOfModules.unit W.ringCatSheaf).Submodule),
        I.toSheafOfModules.IsQuasicoherent ∧
          ((Scheme.Modules.pushforward i).obj
            (∐ fun _ : Fin r => I.toSheafOfModules)).IsCoherent ∧
          ∃ φ : (Scheme.Modules.pushforward i).obj (∐ fun _ : Fin r => I.toSheafOfModules) ⟶ Q,
            Mono φ ∧ ∃ (V : X.Opens) (ξ : X), ξ ∈ V ∧ ξ ∈ (Z : Set X) ∧
              IsIso ((Scheme.Modules.restrictFunctor V.ι).map φ)

/-- **Forgetting the containment** takes the confined conclusion of [Stacks, Tag 01YE] to the
unconfined one. -/
theorem hasKilledIdealGenericIsoSub_of_hasKilledIdealGenericIsoSubIn
    (h : ConfinedDevissage.HasKilledIdealGenericIsoSubIn X) : HasKilledIdealGenericIsoSub X := by
  intro Z hZirr Q hQq hQc hkill
  obtain ⟨W, i, hi, hW, r, I, hIq, -, hAc, φ, hmono, hrest⟩ := h Z hZirr Q hQq hQc hkill
  exact ⟨W, i, hi, hW, r, I, hIq, hAc, φ, hmono, hrest⟩

/-! ### The confined dévissage implies the unconfined one -/

/-- **The confined dévissage of step 4 implies the unconfined one.** The confined quotient class
of [Stacks, Tag 01YH] is contained in the unconfined class of [Stacks, Tag 01YF], by
`ConfinedDevissage.isIdealPushforward_of_isIdealPushforwardIn`, and
`ConfinedDevissage.hasDevissageWith_mono` transports a filtration along a
containment of classes. -/
theorem hasKilledIdealDevissage_of_hasKilledIdealDevissageIn
    (h : HasKilledIdealDevissageIn X) : HasKilledIdealDevissage X := by
  intro Z hZirr Q hQq hQc hkill
  refine ConfinedDevissage.hasDevissageWith_mono (fun M hM => ?_) (h Z hZirr Q hQq hQc hkill)
  exact hM.imp ConfinedDevissage.isIdealPushforward_of_isIdealPushforwardIn id

/-! ### Step 4 of [Stacks, Tag 01YF], unconfined, from [Stacks, Tag 01YE] -/

/-- **Step 4 of the proof of [Stacks, Tag 01YF], unconfined, from the conclusion of
[Stacks, Tag 01YE] alone.** Nothing is added to what Tag 01YE produces: the support of the
cokernel comes from
`ConfinedDevissage.supp_cokernel_ssubset_of_killed`, the filtration of the sub by
its `r` factors from
`Stacks.AlgebraicGeometry.IrreducibleDevissage.hasDevissageWith_pushforward_coproduct_const`, and
the coherence that filtration needs from
`ConfinedDevissage.isCoherent_pushforward_of_isCoherent_pushforward_coproduct`.

At multiplicity `r = 0` the sub is a zero module, so the quotient map is an isomorphism and `Q`
itself is supported strictly inside `Z`; that is a one-step filtration on the right disjunct, and
no ideal sheaf is used at all. -/
theorem hasKilledIdealDevissage_of_hasKilledIdealGenericIsoSub
    (h : HasKilledIdealGenericIsoSub X) : HasKilledIdealDevissage X := by
  intro Z hZirr Q hQq hQc hkill
  obtain ⟨W, i, hi, hW, r, I, hIq, hAc, φ, hmono, V, ξ, hξV, hξZ, hiso⟩ :=
    h Z hZirr Q hQq hQc hkill
  have hsupp : SheafOfModules.supp (cokernel φ) ⊂ (Z : Set X) :=
    ConfinedDevissage.supp_cokernel_ssubset_of_killed Z Q hQq hkill φ V hiso ξ hξV hξZ
  have hCc : (cokernel φ).IsCoherent := isCoherent_cokernel' φ hAc hQc
  rcases Nat.eq_zero_or_pos r with hr | hr
  · subst hr
    have hcz : IsZero (∐ fun _ : Fin 0 => I.toSheafOfModules) :=
      (IsZero.iff_id_eq_zero _).2 (Sigma.hom_ext _ _ fun j => isEmptyElim j)
    have hAz : IsZero ((Scheme.Modules.pushforward i).obj
        (∐ fun _ : Fin 0 => I.toSheafOfModules)) :=
      Functor.map_isZero _ hcz
    have hφ0 : φ = 0 := hAz.eq_of_src φ 0
    have hπ : IsIso (cokernel.π φ) := by
      rw [hφ0, ← cokernelZeroIsoTarget_inv]
      infer_instance
    have hQsupp : SheafOfModules.supp Q ⊂ (Z : Set X) := by
      rw [supp_eq_of_iso (asIso (cokernel.π φ))]
      exact hsupp
    exact hasDevissageWith_single isIdealPushforward_or_supp_ssubset_of_iso' hQc (Or.inr hQsupp)
  · have hIc : ((Scheme.Modules.pushforward i).obj I.toSheafOfModules).IsCoherent :=
      ConfinedDevissage.isCoherent_pushforward_of_isCoherent_pushforward_coproduct i
        I.toSheafOfModules r hr hAc
    refine hasDevissageWith_trans' isIdealPushforward_or_supp_ssubset_of_iso' φ hQc ?_ ?_
    · exact hasDevissageWith_pushforward_coproduct_const
        isIdealPushforward_or_supp_ssubset_of_iso' i I.toSheafOfModules hIc
        (Or.inl (isIdealPushforward_pushforward i hi hW I hIq)) r
    · exact hasDevissageWith_single isIdealPushforward_or_supp_ssubset_of_iso' hCc (Or.inr hsupp)

/-! ### Tag 01YG on the conclusion of [Stacks, Tag 01YE] -/

/-- **The statement of Tag 01YG verbatim, with the conclusion of [Stacks, Tag 01YE] as its one added
hypothesis.** A property of modules on a Noetherian scheme that holds on the zero module, is
stable under extensions of coherent modules, and holds on the direct image of every
quasi-coherent ideal sheaf on every integral closed subscheme, holds on every coherent module.

This replaces the hypothesis
`Stacks.AlgebraicGeometry.IrreducibleDevissage.HasKilledIdealCoproductSub` of
`Stacks.AlgebraicGeometry.IrreducibleDevissage.property_of_hasKilledIdealCoproductSub` — which
is stronger than the conclusion of Tag 01YE in the two respects recorded there — by that
conclusion itself, strengthened in no respect. -/
theorem property_of_hasKilledIdealGenericIsoSub (X : Scheme.{u}) [IsNoetherian X]
    (h : HasKilledIdealGenericIsoSub X)
    (P : X.Modules → Prop)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    ∀ F : X.Modules, F.IsCoherent → P F :=
  property_of_hasKilledIdealDevissage X
    (hasKilledIdealDevissage_of_hasKilledIdealGenericIsoSub h) P hzero hext hideal

/-- **The statement of Tag 01YG verbatim on the confined conclusion of [Stacks, Tag 01YE]** — the
predicate `ConfinedDevissage.HasKilledIdealGenericIsoSubIn` that
[Stacks, Tag 01YH] consumes, so that Tags 01YG and 01YH rest on one statement. -/
theorem property_of_hasKilledIdealGenericIsoSubIn (X : Scheme.{u}) [IsNoetherian X]
    (h : ConfinedDevissage.HasKilledIdealGenericIsoSubIn X)
    (P : X.Modules → Prop)
    (hzero : P (⊤_ X.Modules))
    (hext : ∀ S : ShortComplex X.Modules, S.ShortExact →
      S.X₁.IsCoherent → S.X₂.IsCoherent → S.X₃.IsCoherent → P S.X₁ → P S.X₃ → P S.X₂)
    (hideal : ∀ {Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z]
      (I : (SheafOfModules.unit Z.ringCatSheaf).Submodule),
      I.toSheafOfModules.IsQuasicoherent →
      P ((Scheme.Modules.pushforward i).obj I.toSheafOfModules)) :
    ∀ F : X.Modules, F.IsCoherent → P F :=
  property_of_hasKilledIdealGenericIsoSub X
    (hasKilledIdealGenericIsoSub_of_hasKilledIdealGenericIsoSubIn h) P hzero hext hideal

end Stacks.AlgebraicGeometry.Tag01YGOnTag01YE

end
