module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.CurveUpperBound
public import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.Order
public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.BigOperators.Group.Finset.Basic

/-!
# The twisted Bombieri–Stepanov bound, and the counting identities of the lower bound

The lower bound of Bombieri's proof of the Riemann hypothesis for curves runs through a Galois
cover `W → ℙ¹` with group `G` dominating the curve `X`: for each `σ ∈ G` the *twisted* count
`N_σ = #{w ∈ W(k̄) : Frob_Q(w) = σ(w)}` is bounded above by Stepanov's method, the twisted counts
add up to `|G| · #ℙ¹(𝔽_Q) + O(1)`, and `#X(𝔽_Q)` is at least the average of the `N_σ` over the
group of `W → X`. This file proves the two pieces that do not involve the construction of `W`.

* **The twisted bound on a curve**,
  `Stacks.BombieriStepanov.exists_sum_curveDeg_add_one_le_twisted`:
  `Stacks.BombieriStepanov.exists_sum_curveDeg_add_one_le` with the identity replaced by any map
  `σ` of the function field carrying `L(n P₀)` into `L(n P₁)` for a second place `P₁` of degree
  one, the places counted being those at which `σ y ≡ y ^ Q` for every regular `y`. This is the
  general form `Stacks.BombieriStepanov.sum_deg_add_one_le` already proves, read on a curve.
* **The hypothesis `hσ` from an automorphism**,
  `Stacks.BombieriStepanov.mapsTo_poleSpace_placeMap`:
  an automorphism `s` of the curve carries `L(n P₀)` into `L(n s(P₀))` on function fields.
* **The two counting identities**, at the level of sets with a group action and a "Frobenius":
  `Stacks.BombieriStepanov.card_mul_card_le_sum_ncard_twisted` (the twisted counts over a family
  of torsor fibres add up to `|G|` times the number of fibres) and
  `Stacks.BombieriStepanov.sum_ncard_twisted_le_card_mul` (for a subgroup `H` acting freely and
  transitively on the fibres of a map to a set with a Frobenius, the twisted counts for `σ ∈ H`
  add up to at most `|H|` times the number of fixed points downstairs).
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.BombieriStepanov

section Twisted

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))
  [IsIntegral X] [IsLocallyNoetherian X]
  (hdvr : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
  [IsProper p] [IsCurve k p]

include hdvr in
/-- **The twisted Bombieri–Stepanov bound on a proper curve over a finite field.** Let `P₀`, `P₁`
be closed points of `X` with residue field `k`, and let `σ` be a map of the function field
carrying `L(n P₀)` into `L(n P₁)` for every `n`. There is a constant `γ` such that, whenever
`q ^ ν = r²` with `r = p ^ e` and `r > γ² + 3γ + 1`, every finite set `S` of closed points other
than `P₀` at which `σ y ≡ y ^ (r²)` for every regular `y` has
`∑_{x ∈ S} deg x + 1 ≤ r² + (2γ + 1) r`. -/
theorem exists_sum_curveDeg_add_one_le_twisted [Fintype k] (pr : ℕ) [Fact pr.Prime] [CharP k pr]
    (P₀ P₁ : CurvePlace X) (hcl : IsClosed ({P₀.1} : Set X)) (hP₀ : curveDeg k p P₀ = 1)
    (hP₁ : curveDeg k p P₁ = 1)
    (hsurj : Function.Surjective fun c : k =>
      IsLocalRing.residue (X.presheaf.stalk P₀.1) ((fieldToStalk p P₀.1).hom c))
    (σ : X.functionField → X.functionField)
    (hσ : ∀ n, ∀ y ∈ poleSpace (curveVal hdvr) P₀ n, σ y ∈ poleSpace (curveVal hdvr) P₁ n) :
    ∃ γ : ℕ, ∀ e : ℕ, γ ^ 2 + 3 * γ + 1 < pr ^ e →
      ∀ S : Finset (CurvePlace X), P₀ ∉ S →
        (∀ P ∈ S, ∀ y : X.functionField, 0 ≤ curveVal hdvr P y →
          ((1 : ℤ) : WithTop ℤ) ≤ curveVal hdvr P (σ y - y ^ (pr ^ e * pr ^ e))) →
        ∑ P ∈ S, curveDeg k p P + 1 ≤ pr ^ e * pr ^ e + (2 * γ + 1) * pr ^ e := by
  let := functionFieldAlgebra p
  have : CharP X.functionField pr :=
    charP_of_injective_algebraMap (algebraMap k X.functionField).injective pr
  have hD := hasDegreeFormula_curveVal hdvr k p
  have hres : IsResidueRational (k := k) (curveVal hdvr P₀) := by
    have := hdvr P₀.1 P₀.2
    exact isResidueRational_schemeVal p P₀.2 hsurj
  obtain ⟨e₀, a, b, ha, ha0, hae, hb, hb0, hbe⟩ :=
    exists_consecutive_poleOrders hdvr k p P₀ hP₀ hcl
  have hRR := pow_le_natCard_poleSpace hD hP₀ hres e₀ ha ha0 hae hb hb0 hbe
  refine ⟨e₀ * e₀, fun e hr S hS₀ hS => ?_⟩
  refine sum_deg_add_one_le pr e hD hP₀ hP₁ hres (e₀ * e₀) hRR hr σ hσ S hS₀
    fun P hP n y hy => hS P hP y (hy.2 P fun h => hS₀ (h ▸ hP))

/-- The place `s(P)` of a curve, for an automorphism `s`: an isomorphism preserves coheights. -/
def placeMap (s : X ≅ X) (P : CurvePlace X) : CurvePlace X :=
  ⟨s.hom.base P.1, (coheight_eq_of_isOpenImmersion s.hom).trans P.2⟩

/-- **An automorphism moves valuations.** For an automorphism `s` of `X` and the induced
automorphism `σ` of the function field, `ord_{s(P)}(σ f) = ord_P(f)`. -/
theorem curveVal_placeMap (s : X ≅ X) (P : CurvePlace X) (f : X.functionField) :
    curveVal hdvr (placeMap s P) (Stacks.Chow.functionFieldRingEquivOfIso s f) =
      curveVal hdvr P f := by
  rcases eq_or_ne f 0 with rfl | hf
  · simp
  have hσf : Stacks.Chow.functionFieldRingEquivOfIso s f ≠ 0 :=
    (map_ne_zero_iff _ (Stacks.Chow.functionFieldRingEquivOfIso s).injective).2 hf
  rw [← coe_ordZ hσf, ← coe_ordZ hf, ordZ_curveVal, ordZ_curveVal]
  exact congrArg _ (Stacks.Chow.ord_functionFieldRingEquivOfIso s f P.1)

/-- **An automorphism moves Riemann–Roch spaces.** The automorphism `σ` of the function field
induced by an automorphism `s` of `X` carries `L(n P₀)` into `L(n s(P₀))`. This is the hypothesis
`hσ` of `Stacks.BombieriStepanov.exists_sum_curveDeg_add_one_le_twisted`. -/
theorem mapsTo_poleSpace_placeMap (s : X ≅ X) (P₀ : CurvePlace X) (n : ℕ) (y : X.functionField)
    (hy : y ∈ poleSpace (curveVal hdvr) P₀ n) :
    Stacks.Chow.functionFieldRingEquivOfIso s y ∈
      poleSpace (curveVal hdvr) (placeMap s P₀) n := by
  refine ⟨(curveVal_placeMap hdvr s P₀ y).symm ▸ hy.1, fun P hP => ?_⟩
  have hPeq : P = placeMap s (placeMap s.symm P) := by
    refine Subtype.ext ?_
    have h := congrArg (fun g : X ⟶ X => g.base P.1) s.inv_hom_id
    simpa [placeMap] using h.symm
  have hne : placeMap s.symm P ≠ P₀ := by
    intro h
    exact hP (hPeq.trans (congrArg (placeMap s) h))
  rw [hPeq, curveVal_placeMap hdvr s]
  exact hy.2 _ hne

end Twisted

section Counting

variable {G W B : Type*} [Group G] [Fintype G] [MulAction G W]

/-- A set described by membership in a finset and a predicate has the `ncard` of that filter. -/
private theorem ncard_eq_card_filter {α : Type*} (S : Finset α) (p : α → Prop) [DecidablePred p]
    (t : Set α) (h : ∀ w, w ∈ t ↔ w ∈ S ∧ p w) : t.ncard = (S.filter p).card := by
  rw [← Set.ncard_coe_finset]
  congr 1
  ext w
  simpa using h w

/-- **The twisted counts over torsor fibres.** Let `G` act on `W`, let `π : W → B` be
`G`-invariant, and let `F : W → W` lie over the identity of the fibres in a finite set `T ⊆ B`,
each of which is finite with exactly `|G|` elements on which `G` acts transitively. Then the
twisted counts `#{w over T : F w = σ • w}`, summed over `σ ∈ G`, are at least `|G| · #T`. -/
theorem card_mul_card_le_sum_ncard_twisted (π : W → B) (F : W → W) (T : Finset B)
    (hF : ∀ w, π w ∈ T → π (F w) = π w)
    (htrans : ∀ w w', π w ∈ T → π w' = π w → ∃ g : G, g • w = w')
    (hfin : ∀ b ∈ T, (π ⁻¹' {b}).Finite)
    (hcard : ∀ b ∈ T, (π ⁻¹' {b}).ncard = Fintype.card G) :
    Fintype.card G * T.card ≤ ∑ σ : G, {w | π w ∈ T ∧ F w = σ • w}.ncard := by
  classical
  have hTfin : (π ⁻¹' (T : Set B)).Finite := T.finite_toSet.preimage' hfin
  set S := hTfin.toFinset with hSdef
  have hS : ∀ w, w ∈ S ↔ π w ∈ T := fun w => by simp [S]
  have hcardS : S.card = Fintype.card G * T.card := by
    rw [Finset.card_eq_sum_card_fiberwise (f := π) (t := T) fun w hw => (hS w).1 hw,
      Finset.sum_congr rfl (g := fun _ => Fintype.card G), Finset.sum_const, smul_eq_mul,
      mul_comm]
    intro b hb
    rw [← hcard b hb]
    refine (ncard_eq_card_filter S _ _ fun w => ?_).symm
    exact ⟨fun h => ⟨(hS w).2 (h ▸ hb), h⟩, fun h => h.2⟩
  have hsub : S ⊆ Finset.univ.biUnion fun σ : G => S.filter fun w => F w = σ • w := by
    intro w hw
    obtain ⟨g, hg⟩ := htrans w (F w) ((hS w).1 hw) (hF w ((hS w).1 hw))
    simp only [Finset.mem_biUnion, Finset.mem_univ, Finset.mem_filter, true_and]
    exact ⟨g, hw, hg.symm⟩
  calc Fintype.card G * T.card = S.card := hcardS.symm
    _ ≤ (Finset.univ.biUnion fun σ : G => S.filter fun w => F w = σ • w).card :=
        Finset.card_le_card hsub
    _ ≤ ∑ σ : G, (S.filter fun w => F w = σ • w).card := Finset.card_biUnion_le
    _ = ∑ σ : G, {w | π w ∈ T ∧ F w = σ • w}.ncard := by
        refine Finset.sum_congr rfl fun σ _ => (ncard_eq_card_filter S _ _ fun w => ?_).symm
        simp [hS]

/-- **The fibres of a fibrewise transitive action are small.** If a finite group `H` acts on `V`
and acts transitively on each fibre of a map `ρ : V → Y`, then every fibre of `ρ` is finite with
at most `|H|` elements. -/
private theorem finite_and_ncard_fiber_le_card {V Y H : Type*} [Group H] [Fintype H]
    [MulAction H V] (ρ : V → Y)
    (htrans : ∀ w w' : V, ρ w = ρ w' → ∃ h : H, h • w = w') :
    ∀ x, (ρ ⁻¹' {x}).Finite ∧ (ρ ⁻¹' {x}).ncard ≤ Fintype.card H := by
  classical
  intro x
  by_cases hx : (ρ ⁻¹' {x}).Nonempty
  · obtain ⟨w₀, hw₀⟩ := hx
    have hrange : ρ ⁻¹' {x} ⊆ Set.range fun h : H => h • w₀ := by
      intro w hw
      obtain ⟨h, hh⟩ := htrans w₀ w (hw₀.trans hw.symm)
      exact ⟨h, hh⟩
    refine ⟨(Set.finite_range _).subset hrange, ?_⟩
    calc (ρ ⁻¹' {x}).ncard ≤ (Set.range fun h : H => h • w₀).ncard :=
          Set.ncard_le_ncard hrange (Set.finite_range _)
      _ ≤ Nat.card H := by
          rw [← Nat.card_coe_set_eq]
          exact Nat.card_le_card_of_surjective _ Set.rangeFactorization_surjective
      _ = Fintype.card H := Nat.card_eq_fintype_card
  · rw [Set.not_nonempty_iff_eq_empty] at hx
    rw [hx]
    simp

/-- **The twisted counts for a group acting freely and transitively on fibres.** Let a finite
group `H` act on `W`, let `ρ : W → X'` be `H`-invariant with `H` acting freely and transitively on
its fibres, and let `F : W → W` and `F' : X' → X'` be compatible with `ρ`. If `F'` has finitely
many fixed points, then the twisted counts `#{w : F w = σ • w}`, summed over `σ ∈ H`, are at most
`|H|` times the number of fixed points of `F'`. -/
theorem sum_ncard_twisted_le_card_mul {H X' : Type*} [Group H] [Fintype H] [MulAction H W]
    (ρ : W → X') (F : W → W) (F' : X' → X') (hρF : ∀ w, ρ (F w) = F' (ρ w))
    (hρH : ∀ (h : H) (w : W), ρ (h • w) = ρ w) (hfree : ∀ (h : H) (w : W), h • w = w → h = 1)
    (htrans : ∀ w w' : W, ρ w = ρ w' → ∃ h : H, h • w = w')
    (hD : {x | F' x = x}.Finite) :
    ∑ σ : H, {w | F w = σ • w}.ncard ≤ Fintype.card H * {x | F' x = x}.ncard := by
  classical
  -- the fibres of `ρ` have at most `|H|` points
  have hfib := finite_and_ncard_fiber_le_card ρ htrans
  -- every twisted point lies over a fixed point downstairs
  have hmaps : ∀ σ : H, ∀ w, F w = σ • w → ρ w ∈ {x | F' x = x} := by
    intro σ w hw
    show F' (ρ w) = ρ w
    rw [← hρF, hw, hρH]
  have hPfin : (ρ ⁻¹' {x | F' x = x}).Finite := hD.preimage' fun x _ => (hfib x).1
  set P := hPfin.toFinset
  set A : H → Finset W := fun σ => P.filter fun w => F w = σ • w
  have hA : ∀ σ, {w | F w = σ • w}.ncard = (A σ).card := by
    intro σ
    refine ncard_eq_card_filter P _ _ fun w => ?_
    simpa [P] using fun h => hmaps σ w h
  rw [Finset.sum_congr rfl fun σ _ => hA σ, ← Finset.card_sigma]
  set s := Finset.univ.sigma A
  have himage : s.image (fun a => ρ a.2) ⊆ hD.toFinset := by
    intro x hx
    obtain ⟨⟨σ, w⟩, hmem, rfl⟩ := Finset.mem_image.1 hx
    simp only [s, Finset.mem_sigma, Finset.mem_univ, true_and, A, Finset.mem_filter] at hmem
    exact hD.mem_toFinset.2 (hmaps σ w hmem.2)
  calc s.card ≤ Fintype.card H * (s.image fun a => ρ a.2).card := by
        refine Finset.card_le_mul_card_image (f := fun a => ρ a.2) s _ fun x _ => ?_
        -- a point `w` determines `σ`
        have hinj : Set.InjOn (fun a : Σ _ : H, W => a.2)
            ↑(s.filter fun a => ρ a.2 = x) := by
          rintro ⟨σ, w⟩ ha ⟨σ', w'⟩ ha' (hww' : w = w')
          subst hww'
          simp only [Finset.coe_filter, Set.mem_setOf_eq, Finset.mem_sigma, Finset.mem_univ,
            true_and, A, Finset.mem_filter, s] at ha ha'
          have h1 : σ⁻¹ * σ' = 1 := by
            refine hfree _ w ?_
            rw [mul_smul, ← ha'.1.2, ha.1.2, inv_smul_smul]
          rw [inv_mul_eq_one] at h1
          subst h1
          rfl
        calc (s.filter fun a => ρ a.2 = x).card
            = ((s.filter fun a => ρ a.2 = x).image fun a => a.2).card :=
              (Finset.card_image_of_injOn hinj).symm
          _ ≤ (ρ ⁻¹' {x}).ncard := by
              rw [← Set.ncard_coe_finset]
              refine Set.ncard_le_ncard ?_ (hfib x).1
              intro w hw
              obtain ⟨a, ha, rfl⟩ := Finset.mem_image.1 hw
              exact (Finset.mem_filter.1 ha).2
          _ ≤ Fintype.card H := (hfib x).2
    _ ≤ Fintype.card H * hD.toFinset.card := Nat.mul_le_mul_left _ (Finset.card_le_card himage)
    _ = Fintype.card H * {x | F' x = x}.ncard := by rw [Set.ncard_eq_toFinset_card _ hD]

end Counting

end Stacks.BombieriStepanov

end
