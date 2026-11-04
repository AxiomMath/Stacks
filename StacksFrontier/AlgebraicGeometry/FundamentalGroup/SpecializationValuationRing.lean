module

public import Mathlib.AlgebraicGeometry.Stalk
public import StacksFrontier.RingTheory.Valuation.StrictlyHenselian

import StacksCore.Tactic.StacksAttribute

/-!
# Realizing a specialization by a strictly henselian valuation ring

Let `S` be a scheme, let `φ : Spec K ⟶ S` be a geometric point of `S` with image `s'`, and let
`s' ⤳ s` be a specialization. Then there is a valuation subring `A ⊆ K` and a morphism
`r : Spec A ⟶ S` whose generic point is `φ` and whose closed point is `s`, and `A` is strictly
henselian with algebraically closed residue field.

## Main results

* `AlgebraicGeometry.exists_valuationSubring_strictlyHenselian_of_specializes` — the morphism
  `Spec A ⟶ S` above, for a strictly henselian valuation subring `A` of `K` with algebraically
  closed residue field.

## Implementation notes

The construction is the one in the proof of Stacks 0C0M: the specialization `s' ⤳ s` and the
geometric point give a ring homomorphism `𝒪_{S, s} ⟶ K`, namely
`S.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo φ`, which is *not* local — this is
exactly why a valuation ring is needed. Dominating the image of `𝒪_{S, s}` by a valuation
subring of `K` makes it local (`IsLocalRing.exists_factor_valuationRing`, Stacks 00IA), and a
local homomorphism `𝒪_{S, s} → A` is the same thing as a morphism `Spec A ⟶ S` carrying the
closed point to `s` (`AlgebraicGeometry.SpecToEquivOfLocalRing`).

That `A` is strictly henselian with algebraically closed residue field is
`IsLocalRing.exists_factor_valuationRing_strictlyHenselian`; its fraction field is `K` by
`ValuationSubring.instIsFractionRingSubtypeMem`, so `A` is a strictly henselian valuation ring
over `S` with algebraically closed fraction field, as Stacks 0C0M asks for.

The conclusion is stated as an equality of morphisms `Spec.map (algebraMap A K) ≫ r = φ` rather
than as a statement about the generic point of `Spec A`: it implies the statement about points,
and it is the form in which the identification of the generic geometric fibre of `X ×_S Spec A`
with the geometric fibre `X ×_S Spec K` of a morphism `X ⟶ S` is available, namely as
`CategoryTheory.Limits.pullbackLeftPullbackSndIso f r _ ≪≫ pullback.congrHom rfl hr`.

Stacks 0C0M dominates the image not of `𝒪_{S, s}` but of its strict henselization `A`, which is
what makes the residue field of the valuation ring contain `κ(s)^{sep}`. That variant is the
ring-theoretic statement applied to the chosen homomorphism `𝒪^{sh}_{S, s} → κ(s̄')` directly —
it needs no scheme theory, so it is not restated here: use
`IsLocalRing.exists_factor_valuationRing_strictlyHenselian` and compose
`Spec A ⟶ Spec 𝒪^{sh}_{S, s} ⟶ Spec 𝒪_{S, s} ⟶ S`.

## What Stacks 0C0M asserts beyond this, and why it is not here

Stacks 0C0M says that a specialization map `sp : π₁(X_{s̄'}) → π₁(X_{s̄})` of a proper morphism
with geometrically connected fibres is isomorphic to the specialization map `sp_R` of the base
change to such a valuation ring `R`. Neither `sp` nor `sp_R` can be written down in this
library: by the construction of Stacks 0BUP, `sp` is the composite
`π₁(X_{s̄'}) → π₁(X_A) = π₁(X_{κ(s)^{sep}}) = π₁(X_{s̄})`, whose first map is
`AlgebraicGeometry.etaleFundamentalGroupMap` but whose two equalities are Stacks 0A48, 0BTW and
0A49 — none of which is formalized here. The second of them, proper base change over a
henselian local ring, is Stacks 0GS2, and its essential-surjectivity half is explicitly left
open by `StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence`, which
reduces 0GS2 to it. In particular `sp` is not merely hard to construct: it is defined by
inverting a map which this library cannot yet prove to be invertible.

What the lemma adds on top of the result below is therefore exactly the formal part of its
proof, and the result below is exactly the part that is argued.

## References

* [Stacks Project, Tag 0C0M](https://stacks.math.columbia.edu/tag/0C0M)
* [Stacks Project, Tag 0BUP](https://stacks.math.columbia.edu/tag/0BUP)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

/-- **Stacks Project, Tag 0C0M**, the existence of the valuation ring. Let `φ : Spec K ⟶ S` be a
geometric point of a scheme `S`, with `K` algebraically closed, and let the image of `φ`
specialize to `s`. Then there is a strictly henselian valuation subring `A` of `K` — so a
valuation ring with algebraically closed fraction field `K` and, as it happens, algebraically
closed residue field — together with a morphism `r : Spec A ⟶ S` over which `φ` is the generic
point and which carries the closed point of `Spec A` to `s`. -/
@[stacks 0C0M "the existence of the strictly henselian valuation ring `R` over `S` with \
algebraically closed fraction field realizing the specialization, which is the only step the \
Stacks proof argues; the comparison `sp ≅ sp_R` of specialization maps of fundamental groups \
is not \
formalized, because the specialization map `sp` cannot be constructed in this library: its \
construction (Stacks 0BUP) is the composite of the functoriality map with the identifications \
of Stacks 0A48, 0BTW and 0A49, and none of those three is available here — 0BTW is \
proper base change over a henselian local ring, i.e. Stacks 0GS2, whose \
essential-surjectivity half is open \
(see `StacksFrontier.AlgebraicGeometry.FundamentalGroup.FiniteEtaleProperEquivalence`)"]
theorem exists_valuationSubring_strictlyHenselian_of_specializes
    {S : Scheme.{u}} {K : Type u} [Field K] [IsAlgClosed K] (φ : Spec (.of K) ⟶ S) {s : S}
    (h : φ (closedPoint K) ⤳ s) :
    ∃ A : ValuationSubring K, StrictlyHenselianLocalRing A ∧
      IsAlgClosed (IsLocalRing.ResidueField A) ∧
      ∃ r : Spec (.of A) ⟶ S,
        Spec.map (CommRingCat.ofHom (algebraMap A K)) ≫ r = φ ∧ r (closedPoint A) = s := by
  let ψ : S.presheaf.stalk s ⟶ CommRingCat.of K :=
    S.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo φ
  obtain ⟨A, hmem, hlocal, hsh, halg⟩ :=
    IsLocalRing.exists_factor_valuationRing_strictlyHenselian ψ.hom
  have := hlocal
  refine ⟨A, hsh, halg, Spec.map (CommRingCat.ofHom (ψ.hom.codRestrict A.toSubring hmem)) ≫
    S.fromSpecStalk s, ?_, ?_⟩
  · rw [← Spec.map_comp_assoc]
    have he : CommRingCat.ofHom (ψ.hom.codRestrict A.toSubring hmem) ≫
        CommRingCat.ofHom (algebraMap A K) =
          S.presheaf.stalkSpecializes h ≫ Scheme.stalkClosedPointTo φ := by
      ext x
      rfl
    rw [he, Spec.map_comp_assoc, Scheme.SpecMap_stalkSpecializes_fromSpecStalk,
      Scheme.Spec_stalkClosedPointTo_fromSpecStalk]
  · have hc : Spec.map (CommRingCat.ofHom (ψ.hom.codRestrict A.toSubring hmem))
        (closedPoint A) = closedPoint (S.presheaf.stalk s) :=
      comap_closedPoint (ψ.hom.codRestrict A.toSubring hmem)
    exact (Scheme.Hom.comp_apply _ _ _).trans
      ((congrArg (fun x ↦ (S.fromSpecStalk s) x) hc).trans Scheme.fromSpecStalk_closedPoint)

end AlgebraicGeometry

end
