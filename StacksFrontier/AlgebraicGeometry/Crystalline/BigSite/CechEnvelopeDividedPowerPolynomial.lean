module

public import Mathlib.RingTheory.Etale.Basic
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.CechEnvelopeProducts
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialBaseSituation
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.TrivialDividedPowers
public import StacksFrontier.AlgebraicGeometry.Crystalline.StrongLiftingEnvelope
public import StacksFrontier.AlgebraicGeometry.Crystalline.Differentials.DeRhamPairPolynomial
public import StacksFrontier.AlgebraicGeometry.Crystalline.DividedPowerEnvelope.FlatAlgebraBaseChange

/-!
# The envelope of a chart with étale coordinates is a divided power polynomial algebra

Let `(A, I, γ)` be a divided power ring with `p` nilpotent in `A`, let `B_0, …, B_n` be
`A`-algebras with étale coordinates (`A[t^{(k)}_1, …, t^{(k)}_{d_k}] → B_k` étale), let
`(C₀, I C₀, γ₀)` be a divided power `A`-algebra étale over `A[t^{(0)}]` through `r_0`, and let
`r_k : B_k → C₀` be `A`-algebra maps such that `B_0 ⊗_A ⋯ ⊗_A B_n → C₀ → C₀ ⧸ I C₀` is surjective,
with kernel `J`. Let `D` be the divided power envelope of `J`, and `σ : C₀ → D` an `A`-algebra
map lifting `C₀ → C₀ ⧸ I C₀ = D ⧸ J̄` and compatible with `pr_0` on the coordinates. Then `D` is
the divided power polynomial algebra over `C₀` on the variables
`τ^{(k)}_i = pr_k(t^{(k)}_i) - σ(r_k(t^{(k)}_i))`, `1 ≤ k ≤ n`
(`Crystalline.exists_dpPolynomial_equiv_chartEnvelope`).

The two maps are produced by universal properties. The map `C₀⟨τ⟩ → D` is that of the divided
power polynomial algebra. For the inverse, each `B_k` (`k ≥ 1`) maps to `C₀⟨τ⟩` by the unique lift
of `r_k` along the augmentation `C₀⟨τ⟩ → C₀` sending `t^{(k)}_i` to `r_k(t^{(k)}_i) + τ^{(k)}_i`,
which exists because `B_k` is étale over `A[t^{(k)}]` and the augmentation ideal is locally
nilpotent (`p` being nilpotent); the universal property of the envelope then gives `D → C₀⟨τ⟩`.
The two composites are identities by the uniqueness of lifts along locally nilpotent ideals for
algebras with étale coordinates (`Crystalline.algHom_ext_of_etaleCoordinates`).

The case of one smooth lift `B` of an affine open `U` repeated `n + 1` times is
`Crystalline.GlobalCrystallineSituation.CechEnvelope.exists_dpPolynomial_equiv_envelope_const`:
the envelope of `U` in `Y^{n+1}`, `Y = Spec B`, is `B⟨τ^{(j)}_i⟩` via the first projection, with
`τ^{(j)}_i = pr_j(t_i) - pr_0(t_i)`. Over a base whose divided power ideal is zero (for instance
`Crystalline.GlobalCrystallineSituation.trivialBaseSituation`,
`CechEnvelope.baseSectionsRing_trivialBaseSituation_ideal`), for smooth lifts `B_k` of affine
opens `U_k` with étale coordinates, the envelope of `U_0 ∩ ⋯ ∩ U_n` is `Γ(U_0 ∩ ⋯ ∩ U_n)⟨τ⟩` over a
section of its retraction onto `Γ(U_0 ∩ ⋯ ∩ U_n)`
(`CechEnvelope.exists_dpPolynomial_equiv_envelope_of_ideal_eq_bot`).

## References

* [Stacks Project, Tag 07HC](https://stacks.math.columbia.edu/tag/07HC)
* [Stacks Project, Tag 07KE](https://stacks.math.columbia.edu/tag/07KE)
* [Stacks Project, Tag 07K4](https://stacks.math.columbia.edu/tag/07K4)
-/

@[expose] public section

open scoped TensorProduct

universe u

namespace Crystalline

open DividedPowers

section Unramified

/-- **Lifts are unique along a locally nilpotent ideal** for a formally unramified algebra of
finite type: two algebra maps which agree modulo a locally nilpotent ideal are equal. -/
theorem algHom_ext_of_isLocallyNilpotent {R S T : Type*} [CommRing R] [CommRing S] [CommRing T]
    [Algebra R S] [Algebra R T] [Algebra.FormallyUnramified R S] [Algebra.FiniteType R S]
    (L : Ideal T) (hL : L.IsLocallyNilpotent) (g₁ g₂ : S →ₐ[R] T)
    (h : ∀ x, g₁ x - g₂ x ∈ L) : g₁ = g₂ := by
  classical
  obtain ⟨s, hs⟩ := Algebra.FiniteType.out (R := R) (A := S)
  let L' : Ideal T := Ideal.span ((fun x => g₁ x - g₂ x) '' (s : Set S))
  have hL'fg : L'.FG := ⟨s.image (fun x => g₁ x - g₂ x), by simp [L']⟩
  have hL'le : L' ≤ L := Ideal.span_le.mpr (by rintro _ ⟨x, -, rfl⟩; exact h x)
  have hnil : IsNilpotent L' :=
    hL'fg.isNilpotent_iff_le_nilradical.mpr fun x hx => hL x (hL'le hx)
  refine Algebra.FormallyUnramified.ext L' hnil fun x => ?_
  rw [Ideal.Quotient.eq]
  have hsub : (⊤ : Subalgebra R S) ≤
      { carrier := {x | g₁ x - g₂ x ∈ L'}
        mul_mem' := fun {a b} ha hb => by
          change g₁ (a * b) - g₂ (a * b) ∈ L'
          have : g₁ (a * b) - g₂ (a * b) = g₁ a * (g₁ b - g₂ b) + (g₁ a - g₂ a) * g₂ b := by
            rw [map_mul, map_mul]; ring
          rw [this]
          exact L'.add_mem (L'.mul_mem_left _ hb) (L'.mul_mem_right _ ha)
        add_mem' := fun {a b} ha hb => by
          change g₁ (a + b) - g₂ (a + b) ∈ L'
          rw [map_add, map_add, add_sub_add_comm]
          exact L'.add_mem ha hb
        algebraMap_mem' := fun r => by
          change g₁ (algebraMap R S r) - g₂ (algebraMap R S r) ∈ L'
          rw [AlgHom.commutes, AlgHom.commutes, sub_self]
          exact L'.zero_mem } := by
    rw [← hs, Algebra.adjoin_le_iff]
    intro x hx
    exact Ideal.subset_span ⟨x, hx, rfl⟩
  exact hsub Algebra.mem_top

variable {R B' : Type u} [CommRing R] [CommRing B'] [Algebra R B'] {m : ℕ} (t' : Fin m → B')
  (ht' : (MvPolynomial.aeval (R := R) t').toRingHom.Etale)

private theorem map_aeval_eq {X Y : Type*} [CommRing X] [CommRing Y] [Algebra R X] [Algebra R Y]
    (g : X →ₐ[R] Y) (v : Fin m → X) (q : MvPolynomial (Fin m) R) :
    g (MvPolynomial.aeval v q) = MvPolynomial.aeval (g ∘ v) q := by
  rw [← AlgHom.comp_apply, MvPolynomial.comp_aeval]
  rfl

/-- The polynomial ring is a scalar tower over `R` when its algebra structure is `aeval v`. -/
private theorem isScalarTower_of_algebraMap_eq_aeval {X : Type*} [CommRing X] [Algebra R X]
    (v : Fin m → X) [Algebra (MvPolynomial (Fin m) R) X]
    (h : algebraMap (MvPolynomial (Fin m) R) X = (MvPolynomial.aeval v).toRingHom) :
    IsScalarTower R (MvPolynomial (Fin m) R) X :=
  .of_algebraMap_eq' (by
    rw [h]
    ext a
    exact ((MvPolynomial.aeval v).commutes a).symm)

include ht' in
/-- **Uniqueness of lifts for an algebra with étale coordinates**: two algebra maps out of `B'`
which agree on the coordinates and agree modulo a locally nilpotent ideal are equal. -/
theorem algHom_ext_of_etaleCoordinates {Q : Type*} [CommRing Q] [Algebra R Q] (L : Ideal Q)
    (hL : L.IsLocallyNilpotent) (g₁ g₂ : B' →ₐ[R] Q) (hg : ∀ i, g₁ (t' i) = g₂ (t' i))
    (h : ∀ x, g₁ x - g₂ x ∈ L) : g₁ = g₂ := by
  let : Algebra (MvPolynomial (Fin m) R) B' := (MvPolynomial.aeval t').toRingHom.toAlgebra
  have : Algebra.Etale (MvPolynomial (Fin m) R) B' := ht'
  let : Algebra (MvPolynomial (Fin m) R) Q := (MvPolynomial.aeval (g₁ ∘ t')).toRingHom.toAlgebra
  have hcomm (g : B' →ₐ[R] Q) (hgt : ∀ i, g (t' i) = g₁ (t' i)) (q : MvPolynomial (Fin m) R) :
      g (algebraMap (MvPolynomial (Fin m) R) B' q) = algebraMap (MvPolynomial (Fin m) R) Q q := by
    change g (MvPolynomial.aeval t' q) = MvPolynomial.aeval (g₁ ∘ t') q
    rw [map_aeval_eq]
    exact congrArg (fun w => MvPolynomial.aeval w q) (funext hgt)
  let g₁' : B' →ₐ[MvPolynomial (Fin m) R] Q :=
    { g₁.toRingHom with commutes' := hcomm g₁ (fun _ => rfl) }
  let g₂' : B' →ₐ[MvPolynomial (Fin m) R] Q :=
    { g₂.toRingHom with commutes' := hcomm g₂ (fun i => (hg i).symm) }
  have := algHom_ext_of_isLocallyNilpotent L hL g₁' g₂' h
  ext x
  exact congrArg (fun f => f x) this

include ht' in
/-- **Existence of lifts for an algebra with étale coordinates** along a surjection with locally
nilpotent kernel, with prescribed values on the coordinates. -/
theorem exists_algHom_lift_of_etaleCoordinates {Q Q' : Type u} [CommRing Q] [CommRing Q']
    [Algebra R Q] [Algebra R Q'] (f : Q →ₐ[R] Q') (hf : Function.Surjective f)
    (hker : (RingHom.ker (f : Q →+* Q')).IsLocallyNilpotent) (g : B' →ₐ[R] Q') (v : Fin m → Q)
    (hv : ∀ i, f (v i) = g (t' i)) :
    ∃ ρ : B' →ₐ[R] Q, f.comp ρ = g ∧ ∀ i, ρ (t' i) = v i := by
  let : Algebra (MvPolynomial (Fin m) R) B' := (MvPolynomial.aeval t').toRingHom.toAlgebra
  have := isScalarTower_of_algebraMap_eq_aeval (R := R) t' rfl
  have : Algebra.Etale (MvPolynomial (Fin m) R) B' := ht'
  let : Algebra (MvPolynomial (Fin m) R) Q := (MvPolynomial.aeval v).toRingHom.toAlgebra
  have := isScalarTower_of_algebraMap_eq_aeval (R := R) v rfl
  let : Algebra (MvPolynomial (Fin m) R) Q' := (MvPolynomial.aeval (g ∘ t')).toRingHom.toAlgebra
  have := isScalarTower_of_algebraMap_eq_aeval (R := R) (g ∘ t') rfl
  let f' : Q →ₐ[MvPolynomial (Fin m) R] Q' :=
    { f.toRingHom with
      commutes' := fun q => by
        change f (MvPolynomial.aeval v q) = MvPolynomial.aeval (g ∘ t') q
        rw [map_aeval_eq]
        exact congrArg (fun w => MvPolynomial.aeval w q) (funext hv) }
  let g' : B' →ₐ[MvPolynomial (Fin m) R] Q' :=
    { g.toRingHom with
      commutes' := fun q => by
        exact map_aeval_eq g t' q }
  have hsl := Algebra.HasStrongLiftingProperty.of_smooth (MvPolynomial (Fin m) R) B'
  obtain ⟨ρ', hρ'⟩ := hsl.exists_lift_of_surjective f' hf hker g'
  refine ⟨ρ'.restrictScalars R, ?_, fun i => ?_⟩
  · ext x
    exact congrArg (fun φ => φ x) hρ'
  · have h1 : t' i = algebraMap (MvPolynomial (Fin m) R) B' (MvPolynomial.X i) :=
      (MvPolynomial.aeval_X t' i).symm
    rw [AlgHom.restrictScalars_apply, h1, ρ'.commutes]
    exact MvPolynomial.aeval_X v i

end Unramified

section Augmentation

variable (C : DividedPowerRing.{u}) (W : Type u)

/-- An element of the divided power polynomial algebra lies in its divided power ideal exactly
when its augmentation lies in the divided power ideal of the coefficients. -/
theorem mem_dividedPowerPolynomialIdeal_iff (x : DividedPowerAlgebra C (W →₀ C)) :
    x ∈ dividedPowerPolynomialIdeal C.ideal W ↔
      dividedPowerPolynomialAugmentation C W x ∈ C.ideal := by
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · have hle : dividedPowerPolynomialIdeal C.ideal W ≤
        C.ideal.comap (dividedPowerPolynomialAugmentation C W).toRingHom := by
      apply sup_le
      · rw [Ideal.map_le_iff_le_comap]
        intro a ha
        change dividedPowerPolynomialAugmentation C W (algebraMap C _ a) ∈ C.ideal
        rw [AlgHom.commutes]
        exact ha
      · intro z hz
        change dividedPowerPolynomialAugmentation C W z ∈ C.ideal
        rw [show dividedPowerPolynomialAugmentation C W z = 0 from hz]
        exact C.ideal.zero_mem
    exact hle hx
  · rw [show x = algebraMap C _ (dividedPowerPolynomialAugmentation C W x) +
        (x - algebraMap C _ (dividedPowerPolynomialAugmentation C W x)) by ring]
    refine Submodule.add_mem_sup (Ideal.mem_map_of_mem _ hx) ?_
    change dividedPowerPolynomialAugmentation C W _ = 0
    rw [map_sub, AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply, sub_self]

/-- The augmentation is a retraction of the coefficients. -/
theorem dividedPowerPolynomialAugmentation_algebraMap (c : C) :
    dividedPowerPolynomialAugmentation C W (algebraMap C _ c) = c := by
  rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply]

/-- The augmentation kills the variables. -/
theorem dividedPowerPolynomialAugmentation_variable (w : W) :
    dividedPowerPolynomialAugmentation C W (dividedPowerPolynomialVariable C w) = 0 :=
  variable_mem_positiveIdeal C w

end Augmentation

section Chart

open GlobalCrystallineSituation.CechEnvelope DeRhamPair

variable {A : DividedPowerRing.{u}} (C₀ : DividedPowerRing.{u}) [Algebra A C₀]
  {n : ℕ} {B : Fin (n + 1) → Type u} [∀ k, CommRing (B k)] [∀ k, Algebra A (B k)]
  (r : ∀ k, B k →ₐ[A] C₀)

/-- The kernel of `B_0 ⊗_A ⋯ ⊗_A B_n → C₀ → C₀ ⧸ I C₀`, `b_0 ⊗ ⋯ ⊗ b_n ↦ ∏ r_k(b_k)`. -/
def etaleChartIdeal : Ideal (⨂[A] k, B k) :=
  RingHom.ker ((Ideal.Quotient.mk C₀.ideal).comp
    ((piLift r : (⨂[A] k, B k) →ₐ[A] C₀) : (⨂[A] k, B k) →+* C₀))

/-- The ideal `J` contains the extension of the divided power ideal of `A`. -/
theorem map_le_etaleChartIdeal (hC₀ : C₀.ideal = A.ideal.map (algebraMap A C₀)) :
    A.ideal.map (algebraMap A (⨂[A] k, B k)) ≤ etaleChartIdeal C₀ r := by
  rw [Ideal.map_le_iff_le_comap]
  intro a ha
  change Ideal.Quotient.mk C₀.ideal (piLift r (algebraMap A _ a)) = 0
  rw [AlgHom.commutes, Ideal.Quotient.eq_zero_iff_mem, hC₀]
  exact Ideal.mem_map_of_mem _ ha

variable {d : Fin (n + 1) → ℕ} (t : ∀ k, Fin (d k) → B k)

/-- The index set of the divided power variables: one variable `τ^{(k)}_i` for each `k = 1, …, n`
and each coordinate `t^{(k)}_i` of `B_k`. -/
abbrev chartVariables (d : Fin (n + 1) → ℕ) : Type u := ULift.{u} (Σ k : Fin n, Fin (d k.succ))

variable {r} {hJ : A.ideal.map (algebraMap A (⨂[A] k, B k)) ≤ etaleChartIdeal C₀ r}
  (D : DividedPowerEnvelope A (algebraMap A (⨂[A] k, B k)) (etaleChartIdeal C₀ r) hJ)
  (σ : C₀ →+* D.object)

/-- The element `τ^{(k)}_i = t^{(k)}_i ⊗ 1 - σ(r_k(t^{(k)}_i))` of the envelope. -/
noncomputable def chartTau (w : chartVariables d) : D.object :=
  D.algebraMap.toRingHom (PiTensorProduct.singleAlgHom w.down.1.succ (t _ w.down.2)) -
    σ (r _ (t _ w.down.2))

/-- **The envelope of a chart with étale coordinates is a divided power polynomial algebra**:
there are mutually inverse divided power morphisms `e : C₀⟨τ⟩ ⇄ D : e'` with `e = σ` on the
coefficients and `e(τ^{(k)}_i) = pr_k(t^{(k)}_i) - σ(r_k(t^{(k)}_i))`. -/
theorem exists_dpPolynomial_equiv_chartEnvelope {p : ℕ} (hp : p.Prime)
    (hpA : IsNilpotent (p : A))
    (hC₀ : C₀.ideal = A.ideal.map (algebraMap A C₀))
    (hC₀dp : IsDPMorphism A.dividedPowers C₀.dividedPowers (algebraMap A C₀))
    (ht : ∀ k, (MvPolynomial.aeval (R := A) (t k)).toRingHom.Etale)
    (hr0 : (MvPolynomial.aeval (R := A) (r 0 ∘ t 0)).toRingHom.Etale)
    (hsurj : ∀ c : C₀, ∃ x, c - piLift r x ∈ C₀.ideal)
    (hσA : σ.comp (algebraMap A C₀) = D.structureMap.toRingHom)
    (hσ0 : ∀ i, σ (r 0 (t 0 i)) = D.algebraMap.toRingHom (PiTensorProduct.singleAlgHom 0 (t 0 i)))
    (hσ : ∀ x, σ (piLift r x) - D.algebraMap.toRingHom x ∈ D.object.ideal) :
    ∃ (e : DPMorphism (polyRing C₀ (chartVariables d)).dividedPowers D.object.dividedPowers)
      (e' : DPMorphism D.object.dividedPowers (polyRing C₀ (chartVariables d)).dividedPowers),
      (∀ c, e.toRingHom (algebraMap C₀ _ c) = σ c) ∧
      (∀ w, e.toRingHom (dividedPowerPolynomialVariable C₀ w) = chartTau C₀ t D σ w) ∧
      (∀ x, e.toRingHom (e'.toRingHom x) = x) ∧ (∀ y, e'.toRingHom (e.toRingHom y) = y) := by
  classical
  set W := chartVariables d
  set P := polyRing C₀ W
  set aug := dividedPowerPolynomialAugmentation C₀ W
  -- nilpotence
  have hpC₀ : IsNilpotent (p : C₀) := by simpa using hpA.map (algebraMap A C₀)
  have hnilC₀ := locallyNilpotent_dpIdeal hp C₀ hpC₀
  have hnilD := locallyNilpotent_dpIdeal hp D.object
    (by simpa using hpA.map D.structureMap.toRingHom)
  have hnilP := locallyNilpotent_dpIdeal hp P (by simpa using hpC₀.map (algebraMap C₀ P))
  have hkeraug : ∀ x : P, aug x = 0 → x ∈ P.ideal := fun x hx =>
    (mem_dividedPowerPolynomialIdeal_iff C₀ W x).mpr (by rw [hx]; exact C₀.ideal.zero_mem)
  have hnilaug : (RingHom.ker aug.toRingHom).IsLocallyNilpotent :=
    fun x hx => hnilP x (hkeraug x hx)
  -- `σ` and the variables `τ`
  have hσdp : IsDPMorphism C₀.dividedPowers D.object.dividedPowers σ :=
    IsDPMorphism.of_comp A.dividedPowers C₀.dividedPowers D.object.dividedPowers
      (algebraMap A C₀) σ hC₀ hC₀dp (by rw [hσA]; exact D.structureMap.isDPMorphism)
  let σDP : DPMorphism C₀.dividedPowers D.object.dividedPowers := DPMorphism.mk' hσdp
  have hσ_single : ∀ (k : Fin (n + 1)) (b : B k),
      σ (r k b) - D.algebraMap.toRingHom (PiTensorProduct.singleAlgHom k b) ∈ D.object.ideal :=
    fun k b => by simpa only [piLift_single] using hσ (PiTensorProduct.singleAlgHom k b)
  have hτ : ∀ w, chartTau C₀ t D σ w ∈ D.object.ideal := by
    intro w
    have h2 := D.object.ideal.neg_mem (hσ_single w.down.1.succ (t _ w.down.2))
    rwa [neg_sub] at h2
  obtain ⟨φ, hφ, -⟩ := existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial C₀ W
    D.object σDP (fun w => ⟨_, hτ w⟩)
  have hφcoeff : ∀ c, φ.toRingHom (algebraMap C₀ P c) = σ c := fun c =>
    congrArg (fun q => q.toRingHom c) hφ.1
  have hφvar : ∀ w, φ.toRingHom (dividedPowerPolynomialVariable C₀ w) = chartTau C₀ t D σ w :=
    hφ.2
  -- the lifts `ρ_k : B_k → C₀⟨τ⟩`
  let augA : P →ₐ[A] C₀ := aug.restrictScalars A
  have haug_surj : Function.Surjective augA := fun c =>
    ⟨algebraMap C₀ P c, dividedPowerPolynomialAugmentation_algebraMap C₀ W c⟩
  have hρ : ∀ k : Fin n, ∃ ρ : B k.succ →ₐ[A] P, augA.comp ρ = r k.succ ∧
      ∀ i, ρ (t k.succ i) = algebraMap C₀ P (r k.succ (t k.succ i)) +
        dividedPowerPolynomialVariable C₀ (⟨⟨k, i⟩⟩ : W) := by
    intro k
    refine exists_algHom_lift_of_etaleCoordinates (t k.succ) (ht k.succ) augA haug_surj
      hnilaug (r k.succ) _ (fun i => ?_)
    change aug (algebraMap C₀ P _ + dividedPowerPolynomialVariable C₀ _) = _
    rw [map_add, dividedPowerPolynomialAugmentation_algebraMap,
      dividedPowerPolynomialAugmentation_variable, add_zero]
  choose ρs hρaug hρt using hρ
  let ρ : ∀ k, B k →ₐ[A] P :=
    Fin.cases ((IsScalarTower.toAlgHom A C₀ P).comp (r 0)) ρs
  have hρ0 : ∀ b, ρ 0 b = algebraMap C₀ P (r 0 b) := fun b => rfl
  have hρsucc : ∀ (k : Fin n) b, ρ k.succ b = ρs k b := fun k b => rfl
  let Φ : (⨂[A] k, B k) →ₐ[A] P := piLift ρ
  have hΦaug : augA.comp Φ = piLift r := by
    apply PiTensorProduct.algHom_ext
    intro k
    ext b
    simp only [AlgHom.comp_apply, Φ, piLift_single]
    induction k using Fin.cases with
    | zero => exact dividedPowerPolynomialAugmentation_algebraMap C₀ W _
    | succ k => exact congrArg (fun f => f b) (hρaug k)
  have hΦaug' : ∀ x, aug (Φ x) = piLift r x := fun x => congrArg (fun f => f x) hΦaug
  -- the inverse `ψ : D → C₀⟨τ⟩`
  have hΦJ : (etaleChartIdeal C₀ r).map (Φ : (⨂[A] k, B k) →+* P) ≤ P.ideal := by
    rw [Ideal.map_le_iff_le_comap]
    intro x hx
    change Φ x ∈ dividedPowerPolynomialIdeal C₀.ideal W
    rw [mem_dividedPowerPolynomialIdeal_iff, hΦaug']
    exact Ideal.Quotient.eq_zero_iff_mem.mp hx
  let a : DPMorphism A.dividedPowers P.dividedPowers :=
    (setIndexedDividedPowerPolynomialCoefficientDPMorphism C₀ W).comp (DPMorphism.mk' hC₀dp)
  have hΦa : (Φ : (⨂[A] k, B k) →+* P).comp (algebraMap A (⨂[A] k, B k)) = a.toRingHom := by
    ext z
    change Φ (algebraMap A _ z) = algebraMap C₀ P (algebraMap A C₀ z)
    rw [AlgHom.commutes, ← IsScalarTower.algebraMap_apply]
  let ψ := envLift D P a (Φ : (⨂[A] k, B k) →+* P) hΦJ hΦa
  have hψalg : ∀ x, ψ.toRingHom (D.algebraMap.toRingHom x) = Φ x := fun x =>
    congrArg (fun f => f x) (envLift_comp_algebraMap D P a _ hΦJ hΦa)
  have hψstruct : ∀ z, ψ.toRingHom (D.structureMap.toRingHom z) =
      algebraMap C₀ P (algebraMap A C₀ z) := fun z =>
    congrArg (fun f => f.toRingHom z) (envLift_comp_structureMap D P a _ hΦJ hΦa)
  have hψI : ∀ y ∈ D.object.ideal, aug (ψ.toRingHom y) ∈ C₀.ideal := fun y hy =>
    (mem_dividedPowerPolynomialIdeal_iff C₀ W _).mp (ψ.ideal_comp (Ideal.mem_map_of_mem _ hy))
  have hσI : ∀ c ∈ C₀.ideal, σ c ∈ D.object.ideal := fun c hc =>
    σDP.ideal_comp (Ideal.mem_map_of_mem _ hc)
  have hψσA : ∀ z, ψ.toRingHom (σ (algebraMap A C₀ z)) = algebraMap C₀ P (algebraMap A C₀ z) := by
    intro z
    rw [← RingHom.comp_apply σ, hσA, hψstruct]
  have hψσt : ∀ i, ψ.toRingHom (σ (r 0 (t 0 i))) = algebraMap C₀ P (r 0 (t 0 i)) := by
    intro i
    rw [hσ0, hψalg]
    exact piLift_single ρ 0 (t 0 i)
  -- `aug ∘ ψ ∘ σ` is the identity of `C₀`
  let θ : C₀ →ₐ[A] C₀ :=
    { aug.toRingHom.comp (ψ.toRingHom.comp σ) with
      commutes' := fun z => by
        change aug (ψ.toRingHom (σ (algebraMap A C₀ z))) = algebraMap A C₀ z
        rw [hψσA, dividedPowerPolynomialAugmentation_algebraMap] }
  have hθ : θ = AlgHom.id A C₀ := by
    refine algHom_ext_of_etaleCoordinates (r 0 ∘ t 0) hr0 C₀.ideal hnilC₀ θ _ (fun i => ?_)
      (fun c => ?_)
    · change aug (ψ.toRingHom (σ (r 0 (t 0 i)))) = r 0 (t 0 i)
      rw [hψσt, dividedPowerPolynomialAugmentation_algebraMap]
    · obtain ⟨x, hx⟩ := hsurj c
      have hj := hψI _ (hσ x)
      have hi := hψI _ (hσI _ hx)
      change aug (ψ.toRingHom (σ c)) - c ∈ C₀.ideal
      have hsplit : aug (ψ.toRingHom (σ c)) - c =
          aug (ψ.toRingHom (σ (piLift r x) - D.algebraMap.toRingHom x)) +
            aug (ψ.toRingHom (σ (c - piLift r x))) - (c - piLift r x) := by
        rw [map_sub, map_sub, map_sub, map_sub, map_sub, hψalg, hΦaug']
        ring
      rw [hsplit]
      exact C₀.ideal.sub_mem (C₀.ideal.add_mem hj hi) hx
  have hθ' : ∀ c, aug (ψ.toRingHom (σ c)) = c := fun c => congrArg (fun f => f c) hθ
  -- `ψ ∘ σ` is the coefficient map
  have hψσ : ∀ c, ψ.toRingHom (σ c) = algebraMap C₀ P c := by
    let g₁ : C₀ →ₐ[A] P :=
      { ψ.toRingHom.comp σ with
        commutes' := fun z => by
          change ψ.toRingHom (σ (algebraMap A C₀ z)) = algebraMap A P z
          rw [hψσA, ← IsScalarTower.algebraMap_apply] }
    have := algHom_ext_of_etaleCoordinates (r 0 ∘ t 0) hr0 (RingHom.ker aug.toRingHom) hnilaug
      g₁ (IsScalarTower.toAlgHom A C₀ P) (fun i => hψσt i) (fun c => by
        change aug (ψ.toRingHom (σ c) - algebraMap C₀ P c) = 0
        rw [map_sub, hθ', dividedPowerPolynomialAugmentation_algebraMap, sub_self])
    exact fun c => congrArg (fun f => f c) this
  -- `ψ ∘ φ` is the identity of `C₀⟨τ⟩`
  have hψφ : ψ.comp φ = DPMorphism.id P.dividedPowers := by
    have hu := existsUnique_dPMorphism_from_setIndexedDividedPowerPolynomial C₀ W P
      (setIndexedDividedPowerPolynomialCoefficientDPMorphism C₀ W)
      (fun w => ⟨_, variable_mem_polynomialIdeal C₀ w⟩)
    refine hu.unique ⟨?_, fun w => ?_⟩ ⟨?_, fun w => rfl⟩
    · apply DPMorphism.ext
      funext c
      change ψ.toRingHom (φ.toRingHom (algebraMap C₀ P c)) = algebraMap C₀ P c
      rw [hφcoeff, hψσ]
    · change ψ.toRingHom (φ.toRingHom (dividedPowerPolynomialVariable C₀ w)) = _
      rw [hφvar, chartTau, map_sub, hψalg, hψσ]
      change piLift ρ _ - _ = _
      rw [piLift_single, hρsucc, hρt, add_sub_cancel_left]
    · apply DPMorphism.ext
      rfl
  -- `φ ∘ ψ` is the identity of the envelope
  have hφψ : φ.comp ψ = DPMorphism.id D.object.dividedPowers := by
    refine envelopeHom_ext D D.object _ _ ?_ ?_
    · apply DPMorphism.ext
      funext z
      change φ.toRingHom (ψ.toRingHom (D.structureMap.toRingHom z)) = D.structureMap.toRingHom z
      rw [hψstruct, hφcoeff, ← RingHom.comp_apply σ, hσA]
    · let : Algebra A D.object := D.structureMap.toRingHom.toAlgebra
      have hDalg : ∀ z, D.algebraMap.toRingHom (algebraMap A (⨂[A] k, B k) z) =
          D.structureMap.toRingHom z := fun z => by
        rw [← D.algebraMap_comp]
        rfl
      let f₁ : (⨂[A] k, B k) →ₐ[A] D.object :=
        { φ.toRingHom.comp (Φ : (⨂[A] k, B k) →+* P) with
          commutes' := fun z => by
            change φ.toRingHom (Φ (algebraMap A _ z)) = D.structureMap.toRingHom z
            rw [AlgHom.commutes, IsScalarTower.algebraMap_apply A C₀ P, hφcoeff,
              ← RingHom.comp_apply σ, hσA] }
      let f₂ : (⨂[A] k, B k) →ₐ[A] D.object :=
        { D.algebraMap.toRingHom with commutes' := hDalg }
      have hf : f₁ = f₂ := by
        apply PiTensorProduct.algHom_ext
        intro k
        induction k using Fin.cases with
        | zero =>
          refine algHom_ext_of_etaleCoordinates (t 0) (ht 0) D.object.ideal hnilD _ _
            (fun i => ?_) (fun b => ?_)
          · change φ.toRingHom (Φ (PiTensorProduct.singleAlgHom 0 (t 0 i))) =
              D.algebraMap.toRingHom (PiTensorProduct.singleAlgHom 0 (t 0 i))
            rw [piLift_single, hρ0, hφcoeff, hσ0]
          · change φ.toRingHom (Φ (PiTensorProduct.singleAlgHom 0 b)) -
              D.algebraMap.toRingHom (PiTensorProduct.singleAlgHom 0 b) ∈ D.object.ideal
            rw [piLift_single, hρ0, hφcoeff]
            exact hσ_single 0 b
        | succ j =>
          refine algHom_ext_of_etaleCoordinates (t j.succ) (ht j.succ) D.object.ideal hnilD _ _
            (fun i => ?_) (fun b => ?_)
          · change φ.toRingHom (Φ (PiTensorProduct.singleAlgHom j.succ (t j.succ i))) =
              D.algebraMap.toRingHom (PiTensorProduct.singleAlgHom j.succ (t j.succ i))
            rw [piLift_single, hρsucc, hρt, map_add, hφcoeff, hφvar, chartTau]
            simp
          · change φ.toRingHom (Φ (PiTensorProduct.singleAlgHom j.succ b)) -
              D.algebraMap.toRingHom (PiTensorProduct.singleAlgHom j.succ b) ∈ D.object.ideal
            rw [piLift_single, hρsucc]
            have hker : ρs j b - algebraMap C₀ P (r j.succ b) ∈ P.ideal := hkeraug _ (by
              rw [map_sub, dividedPowerPolynomialAugmentation_algebraMap]
              exact sub_eq_zero.mpr (congrArg (fun f => f b) (hρaug j)))
            have h1 := φ.ideal_comp (Ideal.mem_map_of_mem φ.toRingHom hker)
            rw [map_sub, hφcoeff] at h1
            simpa only [sub_add_sub_cancel] using D.object.ideal.add_mem h1 (hσ_single j.succ b)
      ext x
      change φ.toRingHom (ψ.toRingHom (D.algebraMap.toRingHom x)) = D.algebraMap.toRingHom x
      rw [hψalg]
      exact congrArg (fun f => f x) hf
  exact ⟨φ, ψ, hφcoeff, hφvar, fun x => congrArg (fun f => f.toRingHom x) hφψ,
    fun y => congrArg (fun f => f.toRingHom y) hψφ⟩

end Chart

end Crystalline

namespace Crystalline.GlobalCrystallineSituation.CechEnvelope

open CategoryTheory AlgebraicGeometry DividedPowers DeRhamPair

section SingleLift

variable {S : GlobalCrystallineSituation.{u}} {U₀ : S.X.Opens} {n : ℕ}

/-- For a constant family of opens the restriction to the intersection is injective. -/
theorem restr_const_injective :
    Function.Injective (restr (fun _ : Fin (n + 1) => U₀) 0) := by
  have h' : U₀ ≤ inter (fun _ : Fin (n + 1) => U₀) := le_iInf fun _ => le_rfl
  have key : ∀ z, (S.X.homOfLE h').appTop.hom (restr (fun _ : Fin (n + 1) => U₀) 0 z) = z := by
    intro z
    have h1 : S.X.homOfLE h' ≫ S.X.homOfLE (inter_le (fun _ : Fin (n + 1) => U₀) 0) = 𝟙 _ := by
      rw [Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl]
    simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp, RingHom.coe_comp,
      Function.comp_apply, Scheme.Hom.id_appTop, CommRingCat.hom_id, RingHom.id_apply] using
      congrArg (fun f => f.appTop.hom z) h1
  intro x y hxy
  rw [← key x, ← key y, hxy]

variable [IsAffine S.S.scheme] (L₀ : SmoothLift S U₀.ι)

attribute [local instance] interAlgebra

/-- The `A`-algebra structure of the divided power ring `(B, IB, γ_B)` of a smooth lift. -/
instance SmoothLift.algebraDividedPowerRing :
    Algebra (baseSectionsRing S) L₀.dividedPowerRing := L₀.algebra

omit [IsAffine S.S.scheme] in
/-- For a single smooth lift repeated `n + 1` times, the ideal of the closed immersion
`U ⟶ Y ×_S ⋯ ×_S Y` is the kernel of the multiplication `B ⊗ ⋯ ⊗ B → B → B ⧸ I B`. -/
theorem tensorIdeal_const :
    tensorIdeal (U := fun _ : Fin (n + 1) => U₀) (fun _ => L₀) =
      etaleChartIdeal L₀.dividedPowerRing (fun _ => AlgHom.id (baseSectionsRing S) L₀.ring) := by
  have htm : (tensorMap (U := fun _ : Fin (n + 1) => U₀) (fun _ => L₀)) =
      (component (U := fun _ : Fin (n + 1) => U₀) (fun _ => L₀) 0).comp
        (piLift (fun _ => AlgHom.id (baseSectionsRing S) L₀.ring)) := by
    refine PiTensorProduct.algHom_ext fun k => ?_
    ext b
    simp only [AlgHom.comp_apply]
    rw [tensorMap_single, piLift_single]
    rfl
  ext x
  change tensorMap _ x = 0 ↔ Ideal.Quotient.mk _ (piLift _ x) = 0
  rw [htm, AlgHom.comp_apply, component_apply]
  refine ⟨fun h => L₀.equiv.symm.injective
    ((restr_const_injective (h.trans (map_zero _).symm)).trans (map_zero _).symm), fun h => ?_⟩
  have h' : Ideal.Quotient.mk ((baseSectionsRing S).ideal.map
      (algebraMap (baseSectionsRing S) L₀.ring))
      (piLift (fun _ => AlgHom.id (baseSectionsRing S) L₀.ring) x) = 0 := h
  rw [h', map_zero, map_zero]

omit [IsAffine S.S.scheme] in
/-- **The envelope of a single lift with étale coordinates is a divided power polynomial
algebra.** Let `B` be a smooth lift of `U` with global étale coordinates `t_1, …, t_d`
(`A[t] → B` étale), and let `D` be the divided power envelope of `U` in `Y^{n+1}`, `Y = Spec B`
(`CechEnvelope.envelope` for the constant family `B, …, B`). Then, via the first projection
`pr_0 : B → D`, `D` is the divided power polynomial algebra `B⟨τ^{(j)}_i⟩` on the variables
`τ^{(j)}_i = pr_j(t_i) - pr_0(t_i)`, `1 ≤ j ≤ n`, `1 ≤ i ≤ d`: there are mutually inverse divided
power morphisms `e : B⟨τ⟩ ⇄ D : e'` with `e ∘ (B → B⟨τ⟩) = pr_0` and `e(τ^{(j)}_i) =
pr_j(t_i) - pr_0(t_i)`. -/
theorem exists_dpPolynomial_equiv_envelope_const {p : ℕ} (hp : p.Prime)
    (hpA : IsNilpotent (p : baseSectionsRing S)) {d : ℕ} (t : Fin d → L₀.ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) :
    ∃ (e : DPMorphism (polyRing L₀.dividedPowerRing
          (chartVariables (fun _ : Fin (n + 1) => d))).dividedPowers
        (envelope (U := fun _ : Fin (n + 1) => U₀) (fun _ => L₀)).object.dividedPowers)
      (e' : DPMorphism
        (envelope (U := fun _ : Fin (n + 1) => U₀) (fun _ => L₀)).object.dividedPowers
        (polyRing L₀.dividedPowerRing (chartVariables (fun _ : Fin (n + 1) => d))).dividedPowers),
      (∀ b : L₀.ring, e.toRingHom (algebraMap L₀.dividedPowerRing _ b) =
        (envelope (U := fun _ : Fin (n + 1) => U₀) (fun _ => L₀)).algebraMap.toRingHom
          (PiTensorProduct.singleAlgHom 0 b)) ∧
      (∀ w : chartVariables (fun _ : Fin (n + 1) => d),
        e.toRingHom (dividedPowerPolynomialVariable L₀.dividedPowerRing w) =
          (envelope (U := fun _ : Fin (n + 1) => U₀) (fun _ => L₀)).algebraMap.toRingHom
            (PiTensorProduct.singleAlgHom w.down.1.succ (t w.down.2)) -
          (envelope (U := fun _ : Fin (n + 1) => U₀) (fun _ => L₀)).algebraMap.toRingHom
            (PiTensorProduct.singleAlgHom 0 (t w.down.2))) ∧
      (∀ x, e.toRingHom (e'.toRingHom x) = x) ∧ (∀ y, e'.toRingHom (e.toRingHom y) = y) := by
  set E := envelope (U := fun _ : Fin (n + 1) => U₀) (fun _ => L₀)
  set r : ∀ _ : Fin (n + 1), L₀.ring →ₐ[baseSectionsRing S] L₀.dividedPowerRing :=
    fun _ => AlgHom.id (baseSectionsRing S) L₀.ring
  have hideal := tensorIdeal_const (n := n) L₀
  let D := E.copy (f' := algebraMap (baseSectionsRing S) _)
    (J' := etaleChartIdeal L₀.dividedPowerRing r)
    rfl hideal.symm (map_le_etaleChartIdeal L₀.dividedPowerRing r rfl)
  let σ : L₀.dividedPowerRing →+* D.object :=
    E.algebraMap.toRingHom.comp (PiTensorProduct.singleAlgHom (R := baseSectionsRing S)
      (A := fun _ : Fin (n + 1) => L₀.ring) 0).toRingHom
  have hσA : σ.comp (algebraMap (baseSectionsRing S) L₀.dividedPowerRing) =
      D.structureMap.toRingHom := by
    ext a
    change E.algebraMap.toRingHom (PiTensorProduct.singleAlgHom 0 (algebraMap _ L₀.ring a)) =
      E.structureMap.toRingHom a
    rw [AlgHom.commutes, ← E.algebraMap_comp]
    rfl
  have hσ : ∀ x, σ (piLift r x) - D.algebraMap.toRingHom x ∈ D.object.ideal := by
    intro x
    change E.algebraMap.toRingHom (PiTensorProduct.singleAlgHom 0 (piLift r x)) -
      E.algebraMap.toRingHom x ∈ E.object.ideal
    rw [← map_sub]
    refine D.algebraMap.ideal_comp (Ideal.mem_map_of_mem _ ?_)
    change Ideal.Quotient.mk _ (piLift r (PiTensorProduct.singleAlgHom 0 (piLift r x) - x)) = 0
    have hs : piLift r (PiTensorProduct.singleAlgHom 0 (piLift r x) - x) = 0 := by
      rw [map_sub]
      exact sub_eq_zero.mpr (piLift_single r 0 (piLift r x : L₀.ring))
    rw [hs, map_zero]
  obtain ⟨e, e', h1, h2, h3, h4⟩ := exists_dpPolynomial_equiv_chartEnvelope L₀.dividedPowerRing
    (fun _ => t) D σ hp hpA rfl L₀.isDPMorphism_algebraMap (fun _ => ht) ht
    (fun c => ⟨PiTensorProduct.singleAlgHom 0 (c : L₀.ring), by
      have hs : c - piLift r (PiTensorProduct.singleAlgHom 0 (c : L₀.ring)) = 0 :=
        sub_eq_zero.mpr (piLift_single r 0 (c : L₀.ring)).symm
      rw [hs]
      exact Ideal.zero_mem _⟩)
    hσA (fun i => rfl) hσ
  exact ⟨e, e', h1, h2, h3, h4⟩

end SingleLift

section TrivialBase

variable {S : GlobalCrystallineSituation.{u}} [IsAffine S.S.scheme] [S.X.IsSeparated]
  (hI : (baseSectionsRing S).ideal = ⊥)
  {n : ℕ} {U : Fin (n + 1) → S.X.Opens} [∀ k, IsAffine (U k)]
  (L : ∀ k, SmoothLift S (U k).ι)

attribute [local instance] interAlgebra

omit [IsAffine S.S.scheme] [S.X.IsSeparated] [∀ k, IsAffine (U k)] in
include hI in
/-- The extension of the zero divided power ideal of the base to `Γ(U_0 ∩ ⋯ ∩ U_n)` is zero. -/
theorem map_baseIdeal_inter_eq_bot :
    (baseSectionsRing S).ideal.map (algebraMap (baseSectionsRing S) Γ((inter U).toScheme, ⊤)) =
      ⊥ := by
  rw [hI, Ideal.map_bot]

/-- **`Γ(U_0 ∩ ⋯ ∩ U_n)` as a divided power ring** when the divided power ideal of the base is
zero: its divided power ideal is the (zero) extension of that of the base. -/
noncomputable abbrev interDividedPowerRing : DividedPowerRing.{u} :=
  .of Γ((inter U).toScheme, ⊤)
    ((baseSectionsRing S).ideal.map (algebraMap (baseSectionsRing S) Γ((inter U).toScheme, ⊤)))
    (DividedPowers.ofEqBot (map_baseIdeal_inter_eq_bot (U := U) hI))

omit [IsAffine S.S.scheme] [S.X.IsSeparated] [∀ k, IsAffine (U k)] in
include hI in
/-- Over a base with zero divided power ideal the ideal of `U_0 ∩ ⋯ ∩ U_n` in
`B_0 ⊗ ⋯ ⊗ B_n` is the kernel of the chart map. -/
theorem tensorIdeal_eq_etaleChartIdeal :
    tensorIdeal L = etaleChartIdeal (interDividedPowerRing (U := U) hI) (component L) := by
  ext x
  change tensorMap L x = 0 ↔ Ideal.Quotient.mk _ (piLift (component L) x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem]
  change _ ↔ _ ∈ (baseSectionsRing S).ideal.map
    (algebraMap (baseSectionsRing S) Γ((inter U).toScheme, ⊤))
  rw [map_baseIdeal_inter_eq_bot hI, Ideal.mem_bot]
  rfl

omit [IsAffine S.S.scheme] in
/-- Restriction to `U_0 ∩ ⋯ ∩ U_n` is étale, being the restriction along an open immersion of
affine schemes. -/
theorem etale_restr (k : Fin (n + 1)) : (restr U k).Etale := by
  have : Etale (S.X.homOfLE (inter_le U k)) := inferInstance
  exact (HasRingHomProperty.iff_of_isAffine (P := @Etale)).mp this

omit [IsAffine S.S.scheme] in
include hI in
/-- Over a base with zero divided power ideal, `Γ(U_0 ∩ ⋯ ∩ U_n)` is étale over `A[t^{(0)}]`
through the étale coordinates of `B_0 = Γ(U_0)`. -/
theorem etale_aeval_component_zero {d : ℕ} (t : Fin d → (L 0).ring)
    (ht : (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom.Etale) :
    (MvPolynomial.aeval (R := baseSectionsRing S) (component L 0 ∘ t)).toRingHom.Etale := by
  have heq : (MvPolynomial.aeval (R := baseSectionsRing S) (component L 0 ∘ t)) =
      (component L 0).comp (MvPolynomial.aeval t) := (MvPolynomial.comp_aeval t _).symm
  rw [heq]
  have hmk : Function.Bijective (Ideal.Quotient.mk
      ((baseSectionsRing S).ideal.map (algebraMap (baseSectionsRing S) (L 0).ring))) := by
    refine ⟨fun x y hxy => ?_, Ideal.Quotient.mk_surjective⟩
    rw [Ideal.Quotient.eq, hI, Ideal.map_bot, Ideal.mem_bot, sub_eq_zero] at hxy
    exact hxy
  have hc : (component L 0).toRingHom = (restr U 0).comp ((L 0).equiv.symm.toRingHom.comp
      (Ideal.Quotient.mk _)) := rfl
  change ((component L 0).toRingHom.comp
    (MvPolynomial.aeval (R := baseSectionsRing S) t).toRingHom).Etale
  rw [hc]
  refine RingHom.Etale.stableUnderComposition _ _ ht ?_
  refine RingHom.Etale.stableUnderComposition _ _ ?_ (etale_restr 0)
  exact RingHom.Etale.stableUnderComposition _ _ (RingHom.Etale.of_bijective hmk)
    (RingHom.Etale.of_bijective (L 0).equiv.symm.bijective)

omit [IsAffine S.S.scheme] in
include hI in
/-- **Over a base with zero divided power ideal, the envelope of `U_0 ∩ ⋯ ∩ U_n` in
`Y_0 ×_S ⋯ ×_S Y_n` is a divided power polynomial algebra over `Γ(U_0 ∩ ⋯ ∩ U_n)`.** Let the smooth
lifts `B_k` of `U_k` carry étale coordinates `t^{(k)}`. Then there is an `A`-algebra section
`σ : Γ(U_0 ∩ ⋯ ∩ U_n) → D` of the retraction `D → D ⧸ J̄ ≅ Γ(U_0 ∩ ⋯ ∩ U_n)`, compatible with
`pr_0` on the coordinates of `B_0`, and mutually inverse divided power morphisms
`e : Γ(U_0 ∩ ⋯ ∩ U_n)⟨τ^{(k)}_i⟩ ⇄ D : e'` with `e = σ` on the coefficients and
`e(τ^{(k)}_i) = pr_k(t^{(k)}_i) - σ(t^{(k)}_i|_{U_0 ∩ ⋯ ∩ U_n})` for `1 ≤ k ≤ n`. -/
theorem exists_dpPolynomial_equiv_envelope_of_ideal_eq_bot {p : ℕ} (hp : p.Prime)
    (hpA : IsNilpotent (p : baseSectionsRing S)) {d : Fin (n + 1) → ℕ}
    (t : ∀ k, Fin (d k) → (L k).ring)
    (ht : ∀ k, (MvPolynomial.aeval (R := baseSectionsRing S) (t k)).toRingHom.Etale) :
    letI : Algebra (baseSectionsRing S) (envelope L).object :=
      (envelope L).structureMap.toRingHom.toAlgebra
    ∃ σ : Γ((inter U).toScheme, ⊤) →ₐ[baseSectionsRing S] (envelope L).object,
      (∀ y, Ideal.Quotient.mk _ (σ y) = (envelopeEquiv L).symm y) ∧
      (∀ i, σ (component L 0 (t 0 i)) =
        (envelope L).algebraMap.toRingHom (PiTensorProduct.singleAlgHom 0 (t 0 i))) ∧
      ∃ (e : DPMorphism (polyRing (interDividedPowerRing (U := U) hI)
            (chartVariables d)).dividedPowers (envelope L).object.dividedPowers)
        (e' : DPMorphism (envelope L).object.dividedPowers
          (polyRing (interDividedPowerRing (U := U) hI) (chartVariables d)).dividedPowers),
        (∀ c, e.toRingHom (algebraMap (interDividedPowerRing (U := U) hI) _ c) = σ c) ∧
        (∀ w : chartVariables d,
          e.toRingHom (dividedPowerPolynomialVariable (interDividedPowerRing (U := U) hI) w) =
            (envelope L).algebraMap.toRingHom
              (PiTensorProduct.singleAlgHom w.down.1.succ (t _ w.down.2)) -
            σ (component L w.down.1.succ (t _ w.down.2))) ∧
        (∀ x, e.toRingHom (e'.toRingHom x) = x) ∧ (∀ y, e'.toRingHom (e.toRingHom y) = y) := by
  let : Algebra (baseSectionsRing S) (envelope L).object :=
    (envelope L).structureMap.toRingHom.toAlgebra
  set C₀ := interDividedPowerRing (U := U) hI
  have hpE : IsNilpotent (p : (envelope L).object) := by
    simpa using hpA.map (envelope L).structureMap.toRingHom
  have hnilE := locallyNilpotent_dpIdeal hp (envelope L).object hpE
  -- the section `σ`
  have hEalg' : ∀ x, algebraMap (baseSectionsRing S) (envelope L).object x =
      (envelope L).algebraMap.toRingHom (algebraMap _ (tensorRing L) x) := fun x => by
    rw [← RingHom.comp_apply, (envelope L).algebraMap_comp]
    rfl
  let g : Γ((inter U).toScheme, ⊤) →ₐ[baseSectionsRing S]
      (envelope L).object ⧸ (envelope L).object.ideal :=
    { (envelopeEquiv L).symm.toRingHom with
      commutes' := fun a => by
        change (envelopeEquiv L).symm (algebraMap _ Γ((inter U).toScheme, ⊤) a) = _
        rw [RingEquiv.symm_apply_eq, IsScalarTower.algebraMap_apply (baseSectionsRing S)
          (envelope L).object ((envelope L).object ⧸ (envelope L).object.ideal) a,
          Ideal.Quotient.algebraMap_eq, hEalg', envelopeEquiv_mk_algebraMap, AlgHom.commutes] }
  obtain ⟨σ, hσg, hσt⟩ := Crystalline.exists_algHom_lift_of_etaleCoordinates
    (component L 0 ∘ t 0) (etale_aeval_component_zero hI L (t 0) (ht 0))
    (Ideal.Quotient.mkₐ (baseSectionsRing S) (envelope L).object.ideal)
    Ideal.Quotient.mk_surjective (by rwa [Ideal.Quotient.mkₐ_ker]) g
    (fun i => (envelope L).algebraMap.toRingHom (PiTensorProduct.singleAlgHom 0 (t 0 i)))
    (fun i => by
      change Ideal.Quotient.mk _ _ = (envelopeEquiv L).symm _
      rw [RingEquiv.eq_symm_apply, envelopeEquiv_mk_algebraMap, tensorMap_single]
      rfl)
  have hσmk : ∀ y, Ideal.Quotient.mk _ (σ y) = (envelopeEquiv L).symm y := fun y =>
    congrArg (fun f => f y) hσg
  refine ⟨σ, hσmk, hσt, ?_⟩
  -- the envelope as an envelope of the chart ideal
  have hideal := tensorIdeal_eq_etaleChartIdeal hI L
  let D := (envelope L).copy (f' := algebraMap (baseSectionsRing S) _)
    (J' := etaleChartIdeal C₀ (component L)) rfl hideal.symm
    (map_le_etaleChartIdeal C₀ (component L) rfl)
  let σ' : C₀ →+* D.object := σ.toRingHom
  have hσA : σ'.comp (algebraMap (baseSectionsRing S) C₀) = D.structureMap.toRingHom := by
    ext a
    change σ (algebraMap _ Γ((inter U).toScheme, ⊤) a) = _
    exact σ.commutes a
  have hσ : ∀ x, σ' (piLift (component L) x) - D.algebraMap.toRingHom x ∈ D.object.ideal := by
    intro x
    change σ (piLift (component L) x) - (envelope L).algebraMap.toRingHom x ∈
      (envelope L).object.ideal
    rw [← Ideal.Quotient.eq, hσmk, RingEquiv.symm_apply_eq, envelopeEquiv_mk_algebraMap]
    rfl
  obtain ⟨e, e', h1, h2, h3, h4⟩ := exists_dpPolynomial_equiv_chartEnvelope C₀ t D σ'
    hp hpA rfl (DividedPowers.IsDPMorphism.of_eq_bot _ _ _ (map_baseIdeal_inter_eq_bot hI) le_rfl)
    ht (etale_aeval_component_zero hI L (t 0) (ht 0))
    (fun c => by
      obtain ⟨x, hx⟩ := surjective_tensorMap L c
      refine ⟨x, ?_⟩
      have : c - piLift (component L) x = 0 := sub_eq_zero.mpr hx.symm
      rw [this]
      exact Ideal.zero_mem _)
    hσA hσt hσ
  exact ⟨e, e', h1, h2, h3, h4⟩

omit [IsAffine S.S.scheme] [S.X.IsSeparated] in
/-- The divided power ideal of the global sections of the trivial base `(S₀, 0, 0)` is zero. -/
theorem baseSectionsRing_trivialBaseSituation_ideal :
    (baseSectionsRing (trivialBaseSituation S)).ideal = ⊥ :=
  SheafOfModules.Submodule.bot_obj _ _

end TrivialBase

end Crystalline.GlobalCrystallineSituation.CechEnvelope
