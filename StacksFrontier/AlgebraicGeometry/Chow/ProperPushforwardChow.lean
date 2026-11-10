module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs

/-!
# Proper pushforward on Chow groups

Let `S` be the base scheme of chapter 42 of the Stacks Project and let `X`, `Y` be schemes
locally of finite type over `S`. Proper pushforward of cycles along a proper `p : X ⟶ Y` over
`S` is `Stacks.Chow.properPushforward`. Stacks 02S2 says that it carries cycles rationally
equivalent to zero to cycles rationally equivalent to zero, and Stacks 0GU8 therefore defines
proper pushforward on Chow groups

  `p_* : A_k(X) ⟶ A_k(Y)`.

The vanishing itself is not proved here, because its proof runs through material that imports
this file: see the implementation notes. What this file does is the descent, once the vanishing is
granted, together with the functoriality of the descended map. Granting it loses no information:
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_iff` says that the vanishing is
*equivalent* to the existence of a descended map, and `Stacks.Chow.properChowPushforward` is the
unique such map (`Stacks.Chow.eq_properChowPushforward`).

## Main definitions

* `Stacks.Chow.ProperPushforwardFactorsThroughRationalEquivalence` — the assertion that proper
  pushforward of `k`-cycles kills rational equivalences, i.e. the statement of Stacks 02S2.
* `Stacks.Chow.properChowPushforward` — proper pushforward on Chow groups, the definition of
  Stacks 0GU8.

## Main results

* `Stacks.Chow.properPushforward_rationallyEquivalent` — Stacks 02S2 in its two-cycle form:
  pushforwards of rationally equivalent cycles are rationally equivalent.
* `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_iff` — factoring through
  rational equivalence is equivalent to the existence of a descended map on Chow groups.
* `Stacks.Chow.properChowPushforward_mk` — the descended map agrees with pushforward of cycles
  on cycle representatives; `Stacks.Chow.eq_properChowPushforward` — it is the only such map.
* `Stacks.Chow.properChowPushforward_comp` — proper pushforward on Chow groups is functorial,
  which is Stacks 02R5 read on Chow groups.

## Implementation notes

### Why the vanishing is a hypothesis

The proof of Stacks 02S2 reduces, by the local finiteness of the family of integral closed
subschemes presenting a rational equivalence, to a single integral closed subscheme `V ⊆ X` of
delta-dimension `k + 1` and a single nonzero rational function `g` on `V`, and then splits on
the delta-dimension of the scheme-theoretic image of `V` in `Y`:

* if the image has delta-dimension `k + 1`, the pushforward of `div(g)` is the principal divisor
  of the norm of `g` along the finite extension of function fields — this is Stacks 02RT, and it
  **is** in this repository, as `Stacks.Chow.properPushforward_principalDivisorCycle` in
  `StacksFrontier.AlgebraicGeometry.Chow.PrincipalDivisorPushforward`;
* if the image has delta-dimension `k`, the generic fibre is a proper curve over the function
  field of the image and the pushforward of `div(g)` vanishes because the degree of a principal
  divisor on a proper curve over a field is zero — this is Stacks 02RU, which is not in this
  repository. Available are its projective-line case,
  `Stacks.Chow.finsum_ordAt_mul_natDegree_add_ordAtInfty_eq_zero` in
  `StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardDivisor`, and the reduction of the general
  case to a single model curve,
  `Stacks.Chow.properPushforward_principalDivisorCycle_eq_zero_of_properDominant` in
  `StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.Basic`, which descends Stacks
  02RU along a proper dominant morphism of curves by way of Stacks 02RT.

Both branches are now proved. The first is Stacks 02RT, and the second is reduced in
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.DimensionDrop` to
`Stacks.Chow.GenericFibreDegreeVanishes` — that for a proper dominant `π : V ⟶ T` of integral
schemes with `dim_δ(V) = dim_δ(T) + 1` the sum `∑_{x ↦ η} ord_x(f) · [κ(x) : κ(η)]` over the
fibre of `π` at the generic point `η` of `T` vanishes — which is a relative form of Stacks 02RU
and is proved as `Stacks.Chow.genericFibreDegreeVanishes` in
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre`.

So the hypothesis `Stacks.Chow.ProperPushforwardFactorsThroughRationalEquivalence` below is a
theorem:
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper` proves it for every
proper morphism over the base. It is nevertheless still carried as a hypothesis in this file,
because this file is upstream of Stacks 02RU: the proof of Stacks 02RU runs through the degree
theory of `StacksFrontier.AlgebraicGeometry.Chow.Degrees.ZeroCycleDegree`, which imports this one.
Each consumer that wants the unconditional statement supplies
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`, as
`Stacks.Chow.chowDegree` does.

### No `@[stacks 02S2]` and no `@[stacks 0GU8]` here

The covering set of Stacks 02S2 is the vanishing statement itself, which is a hypothesis in this
file rather than a theorem, so no declaration here is literally the tagged statement; the tag
sits on
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper` and
`Stacks.Chow.properPushforward_rationallyEquivalent_of_isProper` in
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre`. The covering set of
Stacks 0GU8 additionally contains the exactness and surjectivity statements for an envelope,
which are not in the repository at all, so that attribute is not placed anywhere.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 02R5](https://stacks.math.columbia.edu/tag/02R5)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

variable (C : ChowSituation.{u}) {X Y Z : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]

/-! ### Stacks 02S2 as a hypothesis -/

/-- **Stacks 02S2.** The assertion that proper pushforward of `k`-cycles along `p : X ⟶ Y`
carries cycles rationally equivalent to zero to cycles rationally equivalent to zero, hence
factors through rational equivalence.

This is the statement of Stacks 02S2. It is carried as a hypothesis in this file, whose material
Stacks 02RU is proved from; it is discharged for every proper morphism by
`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`. See the
implementation notes of `StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow`. -/
def ProperPushforwardFactorsThroughRationalEquivalence (p : X ⟶ Y) [IsProper p]
    (hp : p ≫ sY = sX) (k : ℤ) : Prop :=
  ∀ α ∈ rationalEquivalences C sX k,
    properPushforward C sX sY p hp k α ∈ rationalEquivalences C sY k

/-- **Stacks 02S2.** Proper pushforward preserves rational equivalence of cycles, granted that
it factors through rational equivalence. -/
theorem properPushforward_rationallyEquivalent (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX)
    (k : ℤ) (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k)
    {α β : CycleGroup C sX k} (h : RationallyEquivalent C sX k α β) :
    RationallyEquivalent C sY k (properPushforward C sX sY p hp k α)
      (properPushforward C sX sY p hp k β) := by
  change properPushforward C sX sY p hp k α - properPushforward C sX sY p hp k β ∈
    rationalEquivalences C sY k
  rw [← properPushforward_sub]
  exact hfac (α - β) h

/-- Factoring through rational equivalence is exactly the preservation of rational equivalence
of pairs of cycles: the two forms of Stacks 02S2 agree. -/
theorem properPushforwardFactorsThroughRationalEquivalence_iff_rationallyEquivalent
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ) :
    ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k ↔
      ∀ α β : CycleGroup C sX k, RationallyEquivalent C sX k α β →
        RationallyEquivalent C sY k (properPushforward C sX sY p hp k α)
          (properPushforward C sX sY p hp k β) := by
  refine ⟨fun hfac α β h ↦ properPushforward_rationallyEquivalent C sX sY p hp k hfac h,
    fun h α hα ↦ ?_⟩
  have hα0 : RationallyEquivalent C sX k α 0 := by
    change α - 0 ∈ rationalEquivalences C sX k
    simpa only [sub_zero] using hα
  have h0 : properPushforward C sX sY p hp k α - properPushforward C sX sY p hp k 0 ∈
    rationalEquivalences C sY k := h α 0 hα0
  simpa only [properPushforward_zero, sub_zero] using h0

/-! ### Proper pushforward on Chow groups -/

/-- **Stacks 0GU8.** Proper pushforward on Chow groups, `p_* : A_k(X) ⟶ A_k(Y)`, induced by
proper pushforward of cycles and granted that it factors through rational equivalence. -/
def properChowPushforward (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k) :
    chowGroup C sX k →+ chowGroup C sY k :=
  QuotientAddGroup.map (rationalEquivalences C sX k) (rationalEquivalences C sY k)
    (properPushforwardHom C sX sY p hp k) fun α hα ↦ hfac α hα

/-- **Stacks 0GU8.** On the class of a cycle, proper pushforward on Chow groups is the class of
the proper pushforward of that cycle. -/
@[simp]
theorem properChowPushforward_mk (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k)
    (α : CycleGroup C sX k) :
    properChowPushforward C sX sY p hp k hfac
        (QuotientAddGroup.mk' (rationalEquivalences C sX k) α) =
      QuotientAddGroup.mk' (rationalEquivalences C sY k) (properPushforward C sX sY p hp k α) :=
  rfl

/-- Proper pushforward on Chow groups, composed with the projection from the cycle group, is
the projection of the proper pushforward of cycles. -/
theorem properChowPushforward_comp_mk' (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k) :
    (properChowPushforward C sX sY p hp k hfac).comp
        (QuotientAddGroup.mk' (rationalEquivalences C sX k)) =
      (QuotientAddGroup.mk' (rationalEquivalences C sY k)).comp
        (properPushforwardHom C sX sY p hp k) :=
  rfl

/-- **Stacks 0GU8.** Proper pushforward on Chow groups is the only homomorphism agreeing with
proper pushforward of cycles on cycle representatives. -/
theorem eq_properChowPushforward (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) (k : ℤ)
    (hfac : ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k)
    (F : chowGroup C sX k →+ chowGroup C sY k)
    (hF : F.comp (QuotientAddGroup.mk' (rationalEquivalences C sX k)) =
      (QuotientAddGroup.mk' (rationalEquivalences C sY k)).comp
        (properPushforwardHom C sX sY p hp k)) :
    F = properChowPushforward C sX sY p hp k hfac :=
  QuotientAddGroup.addMonoidHom_ext _
    (hF.trans (properChowPushforward_comp_mk' C sX sY p hp k hfac).symm)

/-- **The hypothesis is exactly the descent.** Proper pushforward of cycles factors through
rational equivalence precisely when it descends to a homomorphism of Chow groups. So carrying
Stacks 02S2 as a hypothesis, as this repository must, loses nothing: the hypothesis *is* the
existence of the map of Stacks 0GU8. -/
theorem properPushforwardFactorsThroughRationalEquivalence_iff (p : X ⟶ Y) [IsProper p]
    (hp : p ≫ sY = sX) (k : ℤ) :
    ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k ↔
      ∃ F : chowGroup C sX k →+ chowGroup C sY k,
        F.comp (QuotientAddGroup.mk' (rationalEquivalences C sX k)) =
          (QuotientAddGroup.mk' (rationalEquivalences C sY k)).comp
            (properPushforwardHom C sX sY p hp k) := by
  refine ⟨fun hfac ↦ ⟨properChowPushforward C sX sY p hp k hfac,
    properChowPushforward_comp_mk' C sX sY p hp k hfac⟩, fun ⟨F, hF⟩ α hα ↦ ?_⟩
  have h : F (QuotientAddGroup.mk' (rationalEquivalences C sX k) α) =
      QuotientAddGroup.mk' (rationalEquivalences C sY k)
        (properPushforward C sX sY p hp k α) :=
    congrFun (congrArg DFunLike.coe hF) α
  rw [QuotientAddGroup.mk'_apply, (QuotientAddGroup.eq_zero_iff α).2 hα, map_zero] at h
  exact (QuotientAddGroup.eq_zero_iff _).1 h.symm

/-! ### Functoriality on Chow groups -/

/-- The composite of two proper morphisms over the base factors through rational equivalence as
soon as each factor does. This is Stacks 02R5 at the level of the hypothesis of Stacks 02S2. -/
theorem properPushforwardFactorsThroughRationalEquivalence_comp (f : X ⟶ Y) [IsProper f]
    (g : Y ⟶ Z) [IsProper g] (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (k : ℤ)
    (hfacf : ProperPushforwardFactorsThroughRationalEquivalence C sX sY f hf k)
    (hfacg : ProperPushforwardFactorsThroughRationalEquivalence C sY sZ g hg k) :
    ProperPushforwardFactorsThroughRationalEquivalence C sX sZ (f ≫ g)
      (by rw [Category.assoc, hg, hf]) k := by
  intro α hα
  rw [← properPushforward_properPushforward C sX sY sZ f g hf hg k α]
  exact hfacg _ (hfacf α hα)

/-- **Stacks 02R5, 0GU8.** Proper pushforward on Chow groups is functorial. -/
theorem properChowPushforward_comp (f : X ⟶ Y) [IsProper f] (g : Y ⟶ Z) [IsProper g]
    (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (k : ℤ)
    (hfacf : ProperPushforwardFactorsThroughRationalEquivalence C sX sY f hf k)
    (hfacg : ProperPushforwardFactorsThroughRationalEquivalence C sY sZ g hg k) :
    (properChowPushforward C sY sZ g hg k hfacg).comp
        (properChowPushforward C sX sY f hf k hfacf) =
      properChowPushforward C sX sZ (f ≫ g) (by rw [Category.assoc, hg, hf]) k
        (properPushforwardFactorsThroughRationalEquivalence_comp C sX sY sZ f g hf hg k
          hfacf hfacg) := by
  refine eq_properChowPushforward C sX sZ (f ≫ g) (by rw [Category.assoc, hg, hf]) k _ _ ?_
  ext α
  change QuotientAddGroup.mk' (rationalEquivalences C sZ k)
      (properPushforward C sY sZ g hg k (properPushforward C sX sY f hf k α)) = _
  rw [properPushforward_properPushforward C sX sY sZ f g hf hg k α]
  rfl

end Stacks.Chow

end
