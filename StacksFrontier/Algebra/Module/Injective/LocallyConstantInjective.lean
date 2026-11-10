module

public import Mathlib.Algebra.Module.Injective
public import Mathlib.Topology.LocallyConstant.Algebra
public import Mathlib.RingTheory.Noetherian.Defs

/-!
# Locally constant maps into an injective module

Let `R` be a left Noetherian ring and `M` an injective `R`-module. For every topological space
`T`, the module `LocallyConstant T M` of locally constant maps `T → M` is injective. By Baer's
criterion it suffices to extend a linear map `φ : 𝔞 → LocallyConstant T M` on a left ideal `𝔞`;
the ideal is finitely generated, the finitely many locally constant maps `φ(aᵢ)` on its
generators define a locally constant map `π : T → Mⁱ`, and `φ` factors through the module of all
maps `π(T) → M`, a product of copies of `M`, which is injective.

For a finite self-injective ring `R`, such as `(ℤ/ℓⁿ)[H]`, this is the injectivity of the sections
of the constant sheaf `R` over an étale scheme, which makes `Hom_R(-, D(A[H]))` exact on the
Galois covering trivializing `D(A[H])` in Step 7 of the proof of [Stacks, Tag 03UG].

## Main results

* `Module.injective_locallyConstant`

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public section

universe u v w

namespace Module

variable {R : Type u} [Ring R] [IsNoetherianRing R] {M : Type v} [AddCommGroup M] [Module R M]

omit [IsNoetherianRing R] in
/-- Two points at which a linear map into locally constant maps agrees on a spanning set of the
ideal `𝔞` are points at which it agrees on all of `𝔞`. -/
private theorem apply_eq_apply_of_span_eq {T : Type w} [TopologicalSpace T] {𝔞 : Ideal R}
    (φ : 𝔞 →ₗ[R] LocallyConstant T M) {s : Set R} (hs : Submodule.span R s = 𝔞) {t t' : T}
    (h : ∀ (y : R) (hy : y ∈ 𝔞), y ∈ s → φ ⟨y, hy⟩ t = φ ⟨y, hy⟩ t') (x : R) (hx : x ∈ 𝔞) :
    φ ⟨x, hx⟩ t = φ ⟨x, hx⟩ t' := by
  have hx' : x ∈ Submodule.span R s := hs.symm ▸ hx
  induction hx' using Submodule.span_induction with
  | mem y hy => exact h y hx hy
  | zero =>
    have : (⟨0, hx⟩ : 𝔞) = 0 := rfl
    rw [this, map_zero]
    rfl
  | add y z hy hz ihy ihz =>
    have : (⟨y + z, hx⟩ : 𝔞) = ⟨y, hs ▸ hy⟩ + ⟨z, hs ▸ hz⟩ := rfl
    rw [this, map_add]
    change φ ⟨y, _⟩ t + φ ⟨z, _⟩ t = φ ⟨y, _⟩ t' + φ ⟨z, _⟩ t'
    rw [ihy, ihz]
  | smul r y hy ihy =>
    have : (⟨r • y, hx⟩ : 𝔞) = r • ⟨y, hs ▸ hy⟩ := rfl
    rw [this, map_smul]
    change r • φ ⟨y, _⟩ t = r • φ ⟨y, _⟩ t'
    rw [ihy]

/-- **Baer's criterion for locally constant maps into an injective module.** -/
theorem baer_locallyConstant [Small.{v} R] [Module.Injective R M] (T : Type w)
    [TopologicalSpace T] : Module.Baer R (LocallyConstant T M) := by
  classical
  intro 𝔞 φ
  obtain ⟨s, hs⟩ := (IsNoetherian.noetherian 𝔞 : 𝔞.FG)
  -- the locally constant map `π : T → M^s` of the values on the generators
  let π : LocallyConstant T (s → M) :=
    LocallyConstant.unflip fun i : s => φ ⟨i.1, hs ▸ Submodule.subset_span i.2⟩
  have hπ : ∀ t t' : T, π t = π t' → ∀ (x : R) (hx : x ∈ 𝔞), φ ⟨x, hx⟩ t = φ ⟨x, hx⟩ t' :=
    fun t t' htt' => apply_eq_apply_of_span_eq φ hs fun i _ hi => congrFun htt' ⟨i, hi⟩
  -- the factorization through maps on the image of `π`
  let V := Set.range π
  let pt : V → T := fun v => v.2.choose
  have hpt : ∀ v : V, π (pt v) = v.1 := fun v => v.2.choose_spec
  let φ' : 𝔞 →ₗ[R] (V → M) :=
    { toFun := fun x v => φ x (pt v)
      map_add' := fun x y => by
        funext v
        simp
      map_smul' := fun r x => by
        funext v
        simp }
  let ext : (V → M) → (s → M) → M := fun g w => if hw : w ∈ V then g ⟨w, hw⟩ else 0
  have hext : ∀ (g : V → M) (t : T), ext g (π t) = g ⟨π t, t, rfl⟩ := fun g t =>
    dite_eq_left ⟨t, rfl⟩
  let ι : (V → M) →ₗ[R] LocallyConstant T M :=
    { toFun := fun g => π.map (ext g)
      map_add' := fun g₁ g₂ => by
        ext t
        change ext (g₁ + g₂) (π t) = ext g₁ (π t) + ext g₂ (π t)
        rw [hext, hext, hext]
        rfl
      map_smul' := fun r g => by
        ext t
        change ext (r • g) (π t) = r • ext g (π t)
        rw [hext, hext]
        rfl }
  have : Small.{max u v} R := small_lift R
  obtain ⟨ψ', hψ'⟩ := Module.Baer.of_injective (R := R) (Q := V → M) inferInstance 𝔞 φ'
  refine ⟨ι ∘ₗ ψ', fun x hx => ?_⟩
  ext t
  change ext (ψ' x) (π t) = φ ⟨x, hx⟩ t
  rw [hext, hψ' x hx]
  exact hπ _ _ (hpt _) x hx

/-- **Locally constant maps into an injective module form an injective module**, over a left
Noetherian ring. -/
theorem injective_locallyConstant [Small.{v} R] [Module.Injective R M]
    (T : Type w) [TopologicalSpace T] : Module.Injective R (LocallyConstant T M) :=
  (baer_locallyConstant T).injective

end Module
