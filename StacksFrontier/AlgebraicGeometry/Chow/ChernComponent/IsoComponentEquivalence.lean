module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernCapPushforward.ComponentDegree
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.ModuleIso
public import StacksFrontier.AlgebraicGeometry.Chow.ChernComponent.Trivialization
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.MeromorphicDivisorPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardChow.Functoriality

/-!
# The component cycle of an invertible module across an isomorphism of schemes

Let `C = (S, δ)` be the base situation of chapter 42 of the Stacks Project, let `ε : A ≅ B` be an
isomorphism over `S` of integral schemes locally of finite type over `S` of delta-dimension
`j + 1`, let `M₁` be an invertible `𝒪_B`-module and let `M₂` be an invertible `𝒪_A`-module with
`ε^*M₁ ≅ M₂`. If a `j`-cycle `c` on `B` has the class of `div_{M₁}(t)` for every nonzero
meromorphic section `t` of `M₁`, then

  `ε_*c - div_{M₂}(σ)` is rationally equivalent to zero on `A`

for every nonzero meromorphic section `σ` of `M₂`. This is the comparison that identifies the two
spellings of the component cycle of the first Chern class on a scheme presented in two ways.

## The argument

Pick a nonzero meromorphic section `t₁` of `M₁`; by hypothesis `c - div_{M₁}(t₁)` is rationally
equivalent to zero, and proper pushforward along the closed immersion `ε.inv` preserves that
(`Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion`). The
pushforward of `div_{M₁}(t₁)` is the divisor cycle of the pullback `ε^*t₁`: that is the first
displayed equation of [Stacks, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST), read
coefficientwise through `Stacks.Chow.properPushforward_apply_of_isIso` and with the degree of the
extension of function fields equal to one because `ε` is an isomorphism. Finally `ε^*t₁` and `σ`
are nonzero meromorphic sections of the isomorphic modules `ε^*M₁` and `M₂`, so their divisor
cycles have the same class by `Stacks.Chow.mk_chernComponentCycle_eq_of_moduleIso`.

## Main results

* `Stacks.Divisors.genericStalkPullback_ne_zero` — the pullback of a nonzero meromorphic section
  along a dominant morphism is nonzero.
* `Stacks.Chow.rationallyEquivalentToZero_properPushforward_sub_chernComponentCycle` — the
  comparison above.

## References

* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02SJ](https://stacks.math.columbia.edu/tag/02SJ)
* [Stacks Project, Tag 02ST](https://stacks.math.columbia.edu/tag/02ST)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Divisors

/-- **The pullback of a nonzero meromorphic section along a dominant morphism is nonzero.** A
coordinate of the section at the image of the generic point pulls back to a coordinate of the
pullback, and the extension of function fields is injective. -/
theorem genericStalkPullback_ne_zero {A B : Scheme.{u}} (h : A ⟶ B) [IsIntegral A] [IsIntegral B]
    [IsLocallyNoetherian A] [IsLocallyNoetherian B] [IsDominant h] {N : B.Modules}
    (hN : ∀ y : B, IsTrivializedNear N y) {t : N.presheaf.stalk (genericPoint B)} (ht : t ≠ 0) :
    genericStalkPullback h N t ≠ 0 := by
  obtain ⟨a, ha⟩ := exists_isCoordinateAt (hN (h.base (genericPoint A))) t
  obtain ⟨m, hm, hτ⟩ := ha.pullback (x := genericPoint A)
  have hbasis := hm.toGenericStalk (hN (h.base (genericPoint A))).pullback
  intro h0
  have hzero : dominantFunctionFieldMap h a = 0 := by
    refine hbasis.injective ?_
    change dominantFunctionFieldMap h a • _ = (0 : A.functionField) • _
    rw [zero_smul, ← hτ, h0]
  exact ha.ne_zero ht ((map_eq_zero_iff _ (dominantFunctionFieldMap h).injective).1 hzero)

end Stacks.Divisors

namespace Stacks.Chow

open Stacks.Divisors

/-- **The component cycle of an invertible module is carried across an isomorphism.** If the
class of a `j`-cycle `c` on `B` is that of `div_{M₁}(t)` for every nonzero meromorphic section
`t` of the invertible module `M₁`, and `σ` is a nonzero meromorphic section of an invertible
`M₂ ≅ ε^*M₁` on `A`, then `ε_*c - div_{M₂}(σ)` is rationally equivalent to zero. -/
theorem rationallyEquivalentToZero_properPushforward_sub_chernComponentCycle
    (C : ChowSituation.{u}) {A B : Scheme.{u}} (qA : A ⟶ C.S) [LocallyOfFiniteType qA]
    (qB : B ⟶ C.S) [LocallyOfFiniteType qB] [IsIntegral A] [IsIntegral B]
    (ε : A ≅ B) (hε : ε.hom ≫ qB = qA) (j : ℤ)
    (hA : schemeDeltaDimension C qA = ((j + 1 : ℤ) : EInt))
    (hB : schemeDeltaDimension C qB = ((j + 1 : ℤ) : EInt))
    (M₁ : B.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible B.presheaf B.ringCatSheaf.2 M₁]
    (M₂ : A.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible A.presheaf A.ringCatSheaf.2 M₂]
    (ψ : (Scheme.Modules.pullback ε.hom).obj M₁ ≅ M₂)
    {σ : M₂.presheaf.stalk (genericPoint A)} (hσ : σ ≠ 0)
    (c : CycleGroup C qB j)
    (hc : ∀ t : M₁.presheaf.stalk (genericPoint B), t ≠ 0 →
      letI : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian qB
      (QuotientAddGroup.mk c : chowGroup C qB j) =
        QuotientAddGroup.mk (Stacks.Chow.chernComponentCycle C qB hB
          (Stacks.Divisors.isTrivializedNear_of_isInvertible M₁) t)) :
    letI : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian qA
    IsRationallyEquivalentToZero C qA j
      (properPushforward C qB qA ε.inv (by rw [← hε, Iso.inv_hom_id_assoc]) j c -
        Stacks.Chow.chernComponentCycle C qA hA
          (Stacks.Divisors.isTrivializedNear_of_isInvertible M₂) σ) := by
  classical
  let : IsLocallyNoetherian A := LocallyOfFiniteType.isLocallyNoetherian qA
  let : IsLocallyNoetherian B := LocallyOfFiniteType.isLocallyNoetherian qB
  let _ : Algebra B.functionField A.functionField := (dominantFunctionFieldMap ε.hom).toAlgebra
  have hinv : ε.inv ≫ qA = qB := by rw [← hε, Iso.inv_hom_id_assoc]
  set hL₁ : ∀ y : B, IsTrivializedNear M₁ y := isTrivializedNear_of_isInvertible M₁
  set hL₂ : ∀ x : A, IsTrivializedNear M₂ x := isTrivializedNear_of_isInvertible M₂
  set hLp : ∀ x : A, IsTrivializedNear ((Scheme.Modules.pullback ε.hom).obj M₁) x :=
    fun x => (hL₁ (ε.hom.base x)).pullback
  change IsRationallyEquivalentToZero C qA j
    (properPushforward C qB qA ε.inv hinv j c - chernComponentCycle C qA hA hL₂ σ)
  -- Step 1: a nonzero meromorphic section of `M₁`, and the class of `c` it computes
  obtain ⟨t₁, ht₁⟩ := exists_ne_zero_genericStalk_of_isInvertible M₁
  have hmem1 : c - chernComponentCycle C qB hB hL₁ t₁ ∈ rationalEquivalences C qB j :=
    QuotientAddGroup.eq_iff_sub_mem.1 (hc t₁ ht₁)
  -- Step 2: push that relation forward along the isomorphism `ε.inv`
  have hmem2 := properPushforwardFactorsThroughRationalEquivalence_of_isClosedImmersion
    ε.inv C qB qA hinv j _ hmem1
  rw [properPushforward_sub] at hmem2
  -- Step 3: the pushed-forward component cycle is the component cycle of the pulled-back section
  set τ := genericStalkPullback ε.hom M₁ t₁
  have hfr := (finrank_functionField_eq_residueDegree ε.hom).trans
    (residueDegree_eq_one_of_iso ε (genericPoint A))
  have hpf := properPushforward_meromorphicDivisorCycle C qA qB hA hB ε.hom hε hL₁ t₁ ht₁
  have hcoef : ∀ a : A,
      ((meromorphicDivisorCycle C qA hA hLp τ).val.1 : AlgebraicCycle A ℤ) a =
        ((meromorphicDivisorCycle C qB hB hL₁ t₁).val.1 : AlgebraicCycle B ℤ) (ε.hom.base a) := by
    intro a
    have h1 := properPushforward_apply_of_isIso C qA qB ε.hom hε (j + 1 - 1)
      (meromorphicDivisorCycle C qA hA hLp τ).val a
    rw [hpf, hfr, Nat.cast_one, one_smul] at h1
    exact h1.symm
  have hstep3 : properPushforward C qB qA ε.inv hinv j (chernComponentCycle C qB hB hL₁ t₁) =
      chernComponentCycle C qA hA hLp τ := by
    apply Subtype.ext
    ext a
    have h2 := properPushforward_apply_of_isIso C qB qA ε.inv hinv j
      (chernComponentCycle C qB hB hL₁ t₁) (ε.hom.base a)
    rw [show ε.inv.base (ε.hom.base a) = a from Scheme.hom_inv_apply ε a] at h2
    rw [h2]
    exact (hcoef a).symm
  -- Step 4: the two component cycles on `A` have the same class
  have hτ : τ ≠ 0 := genericStalkPullback_ne_zero ε.hom hL₁ ht₁
  have hmem4 : chernComponentCycle C qA hA hLp τ - chernComponentCycle C qA hA hL₂ σ ∈
      rationalEquivalences C qA j :=
    QuotientAddGroup.eq_iff_sub_mem.1
      (mk_chernComponentCycle_eq_of_moduleIso C qA hA ψ hLp hL₂ hτ hσ)
  -- Step 6: add the two relations
  rw [hstep3] at hmem2
  have hsum := AddSubgroup.add_mem (rationalEquivalences C qA j) hmem2 hmem4
  rwa [sub_add_sub_cancel] at hsum

end Stacks.Chow

end
