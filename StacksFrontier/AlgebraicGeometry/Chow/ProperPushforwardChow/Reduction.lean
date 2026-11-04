module

public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.LocallyFiniteImage

/-!
# Reducing Stacks 02S2 to one integral closed subscheme

Stacks 02S2 — that proper pushforward of `k`-cycles kills rational equivalences — is proved in
two stages. The first is bookkeeping with locally finite families: a `k`-cycle rationally
equivalent to zero is presented by a locally finite family `W_j` of integral closed subschemes
of delta-dimension `k + 1` together with nonzero rational functions `g_j` on them, and one has
to see that the proper pushforwards of the `div(g_j)` again make up such a presentation on `Y`.
The second is the content: what the pushforward of a *single* `div(g_j)` is.

This file does the first stage, with the second stage as a hypothesis. The hypothesis
`Stacks.Chow.ProperPushforwardKillsPrincipalDivisor` is exactly the dichotomy that Stacks
proves, and nothing more: for an integral closed subscheme `V ⊆ X` of delta-dimension `k + 1`
and a nonzero rational function `g` on `V`, the pushforward of `div(g)` is either zero, or the
principal divisor of a rational function on the scheme-theoretic image `V.map p` of `V`, which
then also has delta-dimension `k + 1`. The first alternative is Stacks 02RU (the image drops
dimension, the generic fibre is a proper curve over the function field of the image and the
degree of a principal divisor there vanishes), the second is Stacks 02RT (the image keeps the
dimension, the function-field extension is finite and the pushforward is the principal divisor
of the norm). Neither is in this repository.

Reassembling is possible because the new family is indexed by the subset of the old index set on
which the second alternative holds, and the support of `V.map p` is the closure of the image of
the support of `V`, so Stacks 02R2 turns the local finiteness of the old family into the local
finiteness of the new one.

## Main definitions

* `Stacks.Chow.ProperPushforwardKillsPrincipalDivisor` — the one-subscheme input to Stacks 02S2.

## Main results

* `Stacks.Chow.algebraicCycle_map_finsum_apply` — the weighted pushforward of a cycle presented
  as a locally finite sum is the locally finite sum of the pushforwards, coefficientwise.
* `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_killsPrincipalDivisor` —
  Stacks 02S2 follows from its one-subscheme case.

## Implementation notes

The weighted pushforward of a cycle is `AlgebraicGeometry.AlgebraicCycle.map`, whose coefficient
at `y` is a sum over the fibre `p⁻¹(y)`, which is compact because `p` is proper. So only the
finitely many members of the locally finite family whose support meets that fibre contribute,
and the interchange of the two sums is a finite Fubini (`finsum_sum_comm`).

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02RT](https://stacks.math.columbia.edu/tag/02RT)
* [Stacks Project, Tag 02RU](https://stacks.math.columbia.edu/tag/02RU)
* [Stacks Project, Tag 02R2](https://stacks.math.columbia.edu/tag/02R2)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Pushing forward a locally finite sum of cycles -/

/-- The weighted pushforward along a proper morphism of a cycle presented as a locally finite
sum of cycles is, coefficientwise, the locally finite sum of the pushforwards. -/
theorem algebraicCycle_map_finsum_apply {X Y : Scheme.{u}} (f : X ⟶ Y) [IsProper f]
    (wx : X → ℤ) (wy : Y → ℤ) {J : Type*} (E : J → Set X) (hE : LocallyFinite E)
    (a : J → AlgebraicCycle X ℤ) (ha : ∀ j, Function.support (a j) ⊆ E j)
    (c : AlgebraicCycle X ℤ) (hc : ∀ x, c x = ∑ᶠ j, a j x) (y : Y) :
    AlgebraicCycle.map f wx wy c y = ∑ᶠ j, AlgebraicCycle.map f wx wy (a j) y := by
  classical
  set K : Set X := f.base ⁻¹' {y} with hKdef
  have hK : IsCompact K := f.isProperMap.isCompact_preimage isCompact_singleton
  have hJ : {j | (E j ∩ K).Nonempty}.Finite := hE.finite_nonempty_inter_compact hK
  set w : X → ℤ := fun x ↦ (AlgebraicCycle.mapCoeff f wx wy x : ℤ) with hw
  have ht : ∀ j ∉ hJ.toFinset, ∀ x : K, a j x = 0 := by
    intro j hj x
    by_contra hx
    exact hj (hJ.mem_toFinset.mpr ⟨x, ha j hx, x.2⟩)
  have hsupp : ∀ j, Function.HasFiniteSupport fun x : K ↦ a j x * w x := by
    intro j
    refine (((a j).locallyFiniteSupport.finite_inter_support_of_isCompact
      hK).preimage Subtype.coe_injective.injOn).subset fun x hx ↦ ?_
    exact ⟨x.2, (mul_ne_zero_iff.mp hx).1⟩
  have hct : ∀ x : K, c x = ∑ j ∈ hJ.toFinset, a j x := by
    intro x
    rw [hc]
    refine finsum_eq_sum_of_support_subset _ fun j hj ↦ ?_
    by_contra hjt
    exact hj (ht j hjt x)
  have hpush : ∀ d : AlgebraicCycle X ℤ,
      AlgebraicCycle.map f wx wy d y = ∑ᶠ x : K, d x * w x := by
    intro d
    rw [AlgebraicCycle.map, Function.locallyFinsupp.map_apply, ← finsum_set_coe_eq_finsum_mem]
  rw [hpush]
  simp_rw [hpush]
  calc (∑ᶠ x : K, c x * w x)
      = ∑ᶠ x : K, ∑ j ∈ hJ.toFinset, a j x * w x :=
        finsum_congr fun x ↦ by rw [hct x, Finset.sum_mul]
    _ = ∑ j ∈ hJ.toFinset, ∑ᶠ x : K, a j x * w x :=
        finsum_sum_comm hJ.toFinset _ fun j _ ↦ hsupp j
    _ = ∑ᶠ j, ∑ᶠ x : K, a j x * w x := by
        refine (finsum_eq_sum_of_support_subset _ fun j hj ↦ ?_).symm
        by_contra hjt
        exact hj (finsum_eq_zero_of_forall_eq_zero fun x ↦ by rw [ht j hjt x, zero_mul])

/-! ### The one-subscheme hypothesis -/

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX)

/-- The proper pushforward along `p` of the principal divisor of a rational function on an
integral closed subscheme of `X`, as a cycle on `Y`. -/
def properPushforwardPrincipalDivisor (V : X.IdealSheafData) (hV : IsIntegral V.subscheme)
    (g : (rationalFunctions V.subscheme)ˣ) : AlgebraicCycle Y ℤ :=
  AlgebraicCycle.map p (relativeDimension C.dimensionFunction sX)
    (relativeDimension C.dimensionFunction sY) (principalDivisorPushforward C sX V hV g)

/-- **The content of Stacks 02S2, isolated.** For every integral closed subscheme `V ⊆ X` of
delta-dimension `k + 1` and every nonzero rational function `g` on `V`, the proper pushforward of
`div(g)` along `p` is either zero or again the principal divisor of a rational function on an
integral closed subscheme of `Y` of delta-dimension `k + 1`, namely on the scheme-theoretic image
`V.map p` of `V`.

The first alternative is Stacks 02RU and the second is Stacks 02RT; neither is formalized in
this repository, so this is carried as a hypothesis. See the module documentation of
`StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Reduction`. -/
def ProperPushforwardKillsPrincipalDivisor (k : ℤ) : Prop :=
  ∀ (V : X.IdealSheafData) (hV : IsIntegral V.subscheme),
    schemeDeltaDimension C (V.subschemeι ≫ sX) = ((k + 1 : ℤ) : EInt) →
      ∀ g : (rationalFunctions V.subscheme)ˣ,
        properPushforwardPrincipalDivisor C sX sY p V hV g = 0 ∨
          ∃ hT : IsIntegral (V.map p).subscheme,
            schemeDeltaDimension C ((V.map p).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt) ∧
              ∃ h : (rationalFunctions (V.map p).subscheme)ˣ,
                properPushforwardPrincipalDivisor C sX sY p V hV g =
                  principalDivisorPushforward C sY (V.map p) hT h

/-! ### The reduction -/

/-- **Stacks 02S2, granted its one-subscheme case.** Proper pushforward of `k`-cycles factors
through rational equivalence as soon as it does so on the principal divisor of a single
rational function on a single integral closed subscheme. -/
theorem properPushforwardFactorsThroughRationalEquivalence_of_killsPrincipalDivisor (k : ℤ)
    (hrule : ProperPushforwardKillsPrincipalDivisor C sX sY p k) :
    ProperPushforwardFactorsThroughRationalEquivalence C sX sY p hp k := by
  classical
  intro α hα
  obtain ⟨J, W, hW, hDim, hLocal, g, hg⟩ := hα
  -- the index set of the new family: those `j` for which the pushforward is a principal divisor
  set P : J → Prop := fun j ↦ ∃ hT : IsIntegral ((W j).map p).subscheme,
    schemeDeltaDimension C (((W j).map p).subschemeι ≫ sY) = ((k + 1 : ℤ) : EInt) ∧
      ∃ h : (rationalFunctions ((W j).map p).subscheme)ˣ,
        properPushforwardPrincipalDivisor C sX sY p (W j) (hW j) (g j) =
          principalDivisorPushforward C sY ((W j).map p) hT h with hP
  have hzero : ∀ j, ¬ P j → properPushforwardPrincipalDivisor C sX sY p (W j) (hW j) (g j) = 0 :=
    fun j hj ↦ (hrule (W j) (hW j) (hDim j) (g j)).resolve_right hj
  choose hT hTDim h heq using fun j : {j // P j} ↦ j.2
  refine ⟨{j // P j}, fun j ↦ (W j.1).map p, hT, hTDim, ?_, h, fun y ↦ ?_⟩
  · -- local finiteness: Stacks 02R2 applied to the proper, hence quasi-compact, `p`
    have himg : LocallyFinite fun j : J ↦ closure (p.base '' ((W j).support : Set X)) :=
      locallyFinite_closure_image_of_isSpectralMap p.base p.isSpectralMap _ hLocal
    have hsupp : (fun j : J ↦ (((W j).map p).support : Set Y)) =
        fun j : J ↦ closure (p.base '' ((W j).support : Set X)) := by
      funext j
      rw [Scheme.IdealSheafData.support_map]
      rfl
    exact (hsupp ▸ himg).comp_injective Subtype.val_injective
  · -- the coefficient identity
    have hpush : (properPushforward C sX sY p hp k α).1 y =
        ∑ᶠ j : J, properPushforwardPrincipalDivisor C sX sY p (W j) (hW j) (g j) y := by
      refine algebraicCycle_map_finsum_apply p _ _ (fun j ↦ ((W j).support : Set X)) hLocal
        (fun j ↦ principalDivisorPushforward C sX (W j) (hW j) (g j))
        (fun j ↦ support_principalDivisorPushforward_subset C sX (W j) (hW j) (g j)) α.1 ?_ y
      exact fun x ↦ hg x
    rw [hpush]
    unfold principalDivisorFamilyCoefficient
    simp only [← heq]
    rw [finsum_subtype_eq_finsum_cond
      (f := fun j : J ↦ properPushforwardPrincipalDivisor C sX sY p (W j) (hW j) (g j) y) P]
    refine finsum_congr fun j ↦ ?_
    by_cases hj : P j
    · have _ : Unique (P j) := ⟨⟨hj⟩, fun _ ↦ rfl⟩
      rw [finsum_unique]
    · have _ : IsEmpty (P j) := ⟨hj⟩
      rw [finsum_of_isEmpty, hzero j hj]
      rfl

end Stacks.Chow

end
