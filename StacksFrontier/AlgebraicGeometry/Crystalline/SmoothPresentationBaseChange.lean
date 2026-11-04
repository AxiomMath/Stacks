module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CompletedDeRhamFormsDataCompletion
public import StacksFrontier.AlgebraicGeometry.Crystalline.TensorPowerEnvelopeLifts

/-!
# The base change of a de Rham complex from a polynomial presentation to a smooth one

Let `P = A[x_i : i ∈ ι] → C` be a surjective polynomial presentation `f₀` of an affine
crystalline situation (the canonical one `A[x_c : c ∈ C] → C` being the default),
`D(n)` the completed divided power envelopes of its tensor powers, and `(M, ∇)` a module with an
integrable completed connection over `D = D(0)`.  Suppose

* `(M, ∇)` is a crystal on the cosimplicial system in the weak sense the proof of
  [Stacks, Lemma 60.21.4, Tag 07LH] uses: its base changes along the two coprojections
  `σ, δ : D(0) → D(1)` are identified by a horizontal isomorphism (the stratification);
* the base change along every coprojection `σ_n : D(0) → D(n)` onto the vertex `0` is a
  quasi-isomorphism of completed de Rham complexes ([Stacks, Lemma 60.20.2, Tag 07LD] through
  [Stacks, Lemma 60.17.5, Tag 07L2]).

Then for every smooth presentation `A → P' → C`, with `D'` the `p`-adic completion of
`D_{P',γ}(J')`, and every divided power `A`-algebra map `a : D → D'` induced by a lift
`g : P → P'` of the variables, the base change map
`M ⊗^∧_D Ω^*_D → (M ⊗̂_{D,a} D') ⊗^∧_{D'} Ω^*_{D'}` is a quasi-isomorphism
(`Crystalline.quasiIso_baseChangeHom_smoothPresentation`).

This is the argument of the source's proof of [Stacks, Tag 07LH]: a retract `a ∘ b = id` between
a tensor power `D(n)` surjecting onto `D'` and `D'` (Lemma [Stacks, Tag 07L5]), reducing the claim
to the base change along the round trip `ρ = b ∘ a`, and the homotopy invariance of the de Rham
complex under divided power morphisms congruent to the identity modulo the divided power ideal,
proved with the universal property of `D(1)` and the stratification.

## References

* [Stacks Project, Lemma 60.21.4, Tag 07LH](https://stacks.math.columbia.edu/tag/07LH)
* [Stacks Project, Lemma 60.17.5, Tag 07L5](https://stacks.math.columbia.edu/tag/07L5)
-/

@[expose] public noncomputable section

open CategoryTheory DividedPowers Simplicial

universe u

namespace Crystalline

section Tower

variable (s : AffineCrystallineSituation.{u, u}) {ι₀ : Type u}
  (f₀ : MvPolynomial ι₀ s.A →ₐ[s.A] s.C) (hf₀ : Function.Surjective f₀)

attribute [local instance] tensorPowerEnvelopeAlgebraInstance presentationEnvelopeAlgebraInst

include hf₀ in
/-- `p` is nilpotent modulo the divided power ideal of each degree of the cosimplicial envelope
of the presentation `f₀`. -/
theorem presTowerPrime_nilpotent (n : ℕ) :
    IsNilpotent (Ideal.Quotient.mk ((envelopeDPAlgebra s (f₀)).ideal n)
      (s.p : (envelopeDPAlgebra s (f₀)).carrier n)) :=
  tensorPowerEnvelope_prime_nilpotent s _ hf₀ n

/-- The divided powers of the degree `n` of the cosimplicial envelope of the canonical
presentation. -/
abbrev presTowerDP (n : ℕ) :
    DividedPowers ((envelopeDPAlgebra s (f₀)).ideal n) :=
  (envelopeDPAlgebra s (f₀)).dividedPowers n

/-- The ring `D(n)` with its completed forms: the degree `n` of the completed cosimplicial
envelope of the presentation `f₀`. -/
abbrev presTowerFormsData (n : ℕ) : FormsData.{u} s.p :=
  FormsData.ofDividedPowers s.p s.A (presTowerDP s f₀ n)

/-- The completed reindexing map of a map of finite ordinals, as a morphism of rings with forms. -/
abbrev presTowerReindexHom {m n : SimplexCategory} (φ : m ⟶ n) :
    FormsData.Hom (presTowerFormsData s f₀ m.len) (presTowerFormsData s f₀ n.len) :=
  FormsData.Hom.ofCompletion s.p s.A (presTowerDP s f₀ m.len) (presTowerPrime_nilpotent s f₀ hf₀
      m.len)
    (presTowerDP s f₀ n.len) (presTowerPrime_nilpotent s f₀ hf₀ n.len)
    (completedReindex s _ φ)
    (isDPMorphism_completedReindex s _ (hf₀) φ)

/-- The completed reindexing morphisms compose. -/
theorem presTowerReindexHom_comp {m n k : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ k) :
    (presTowerReindexHom s f₀ hf₀ ψ).comp (presTowerReindexHom s f₀ hf₀ φ) = presTowerReindexHom s
        f₀ hf₀ (φ ≫ ψ) :=
  (FormsData.Hom.ofCompletion_comp s.p s.A _ (presTowerPrime_nilpotent s f₀ hf₀ m.len) _
    (presTowerPrime_nilpotent s f₀ hf₀ n.len) _ (presTowerPrime_nilpotent s f₀ hf₀ k.len) _
    (isDPMorphism_completedReindex s _ hf₀ φ) _
    (isDPMorphism_completedReindex s _ hf₀ ψ)
    ((isDPMorphism_completedReindex s _ hf₀ ψ).comp _
      (isDPMorphism_completedReindex s _ hf₀ φ))).trans
    (FormsData.Hom.ofCompletion_congr (h := completedReindex_comp s _ φ ψ) ..)

/-- The completed reindexing morphism of an identity is the identity. -/
theorem presTowerReindexHom_id (n : SimplexCategory) :
    presTowerReindexHom s f₀ hf₀ (𝟙 n) = FormsData.Hom.id _ :=
  (FormsData.Hom.ofCompletion_congr (h := completedReindex_id s _ n) ..).trans
    (FormsData.Hom.ofCompletion_id s.p s.A _ (presTowerPrime_nilpotent s f₀ hf₀ n.len)
      (completedReindex_id s _ n ▸
        isDPMorphism_completedReindex s _ hf₀ (𝟙 n)))

/-- The completed reindexing maps are compatible with the augmentations to `C`. -/
theorem completedEnvelopeAugmentation_comp_presTowerReindex {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (completedEnvelopeAugmentation s (tensorPowerPresentation s (f₀) n.len)
        (tensorPowerPresentation_surjective s _ (hf₀) n.len)).comp
      (completedReindex s _ φ).toRingHom =
      completedEnvelopeAugmentation s (tensorPowerPresentation s (f₀) m.len)
        (tensorPowerPresentation_surjective s _ (hf₀) m.len) :=
  completedEnvelopeAugmentation_comp_of_algebraMap s _ _ _ _
    (MvPolynomial.rename (simplexVariableMap φ)) (by
      ext x
      simp [tensorPowerPresentation, simplexVariableMap])
    _ (isDPMorphism_completedReindex s _ hf₀ φ) fun y ↦
      (completedReindex_of s _ φ _).trans
        (congrArg _ (envelopeReindex_polynomial s _ φ y))

end Tower

section TowerMain

variable (s : AffineCrystallineSituation.{u, u}) {ι₀ : Type u}
  (f₀ : MvPolynomial ι₀ s.A →ₐ[s.A] s.C) (hf₀ : Function.Surjective f₀)

attribute [local instance] tensorPowerEnvelopeAlgebraInstance presentationEnvelopeAlgebraInst

/-- The completed envelope `D'` of a presentation, with its completed forms. -/
abbrev presentationFormsData {P' : Type u} [CommRing P'] [Algebra s.A P']
    (f' : P' →ₐ[s.A] s.C) : FormsData.{u} s.p :=
  FormsData.ofDividedPowers s.p s.A (presentationEnvelope s f').object.dividedPowers

include hf₀ in
/-- **A tensor power of a presentation with at least one variable surjects onto a smooth
presentation**: for `f₀ : A[x_i] ↠ C` and a smooth presentation `f' : P' ↠ C` there is a
surjection `q : A[x_i(k) : k ≤ n] ↠ P'` with `f' ∘ q` the presentation of the tensor power.  The
factor `0` maps by a lift of `f₀`; the factor `t + 1` sends one chosen variable to the `t`-th
generator of `P'` corrected by an element of the kernel of `f'`. -/
theorem exists_tensorPowerSurjectionOfTower [Nonempty ι₀] (P' : Type u) [CommRing P']
    [Algebra s.A P'] [Algebra.Smooth (s.A : Type u) P'] (f' : P' →ₐ[s.A] s.C)
    (hf' : Function.Surjective f') :
    ∃ (n : ℕ) (q : MvPolynomial (Fin (n + 1) × ι₀) s.A →ₐ[s.A] P'),
      Function.Surjective q ∧ f'.comp q = tensorPowerPresentation s f₀ n := by
  classical
  obtain ⟨m, q₀, hq₀⟩ := exists_mvPolynomial_surjection_of_smooth (s.A : Type u) P'
  let i₀ : ι₀ := Classical.arbitrary ι₀
  let g : MvPolynomial ι₀ s.A →ₐ[s.A] P' :=
    MvPolynomial.aeval fun i ↦ Function.surjInv hf' (f₀ (MvPolynomial.X i))
  have hg : ∀ x, f' (g x) = f₀ x := DFunLike.congr_fun
    (MvPolynomial.algHom_ext fun i ↦ by simp [g, Function.surjInv_eq hf'] : f'.comp g = f₀)
  let r : Fin m → MvPolynomial ι₀ s.A := fun t ↦ Function.surjInv hf₀ (f' (q₀ (MvPolynomial.X t)))
  have hr : ∀ t, f₀ (r t) = f' (q₀ (MvPolynomial.X t)) := fun t ↦ Function.surjInv_eq hf₀ _
  let vals : Fin (m + 1) × ι₀ → P' := fun x ↦
    Fin.cases (g (MvPolynomial.X x.2))
      (fun t : Fin m ↦ if x.2 = i₀ then g (MvPolynomial.X i₀) + (q₀ (MvPolynomial.X t) - g (r t))
        else g (MvPolynomial.X x.2)) x.1
  have hzero : (MvPolynomial.aeval vals).comp (MvPolynomial.rename (Prod.mk (0 : Fin (m + 1)))) =
      g := MvPolynomial.algHom_ext fun i ↦ by simp [vals]
  refine ⟨m, MvPolynomial.aeval vals, fun y ↦ ?_, ?_⟩
  · obtain ⟨z, rfl⟩ := hq₀ y
    let φ : MvPolynomial (Fin m) s.A →ₐ[s.A] MvPolynomial (Fin (m + 1) × ι₀) s.A :=
      MvPolynomial.aeval fun t ↦ MvPolynomial.X (t.succ, i₀) - MvPolynomial.X (0, i₀) +
        MvPolynomial.rename (Prod.mk (0 : Fin (m + 1))) (r t)
    have : (MvPolynomial.aeval vals).comp φ = q₀ := by
      refine MvPolynomial.algHom_ext fun t ↦ ?_
      have h0 := DFunLike.congr_fun hzero (r t)
      simp only [AlgHom.comp_apply] at h0
      simp [φ, vals, h0]
    exact ⟨φ z, DFunLike.congr_fun this z⟩
  · refine MvPolynomial.algHom_ext fun x ↦ ?_
    obtain ⟨k, i⟩ := x
    simp only [AlgHom.comp_apply, MvPolynomial.aeval_X, tensorPowerPresentation,
      MvPolynomial.rename_X]
    refine Fin.cases ?_ (fun t ↦ ?_) k
    · simpa [vals] using hg (MvPolynomial.X i)
    · simp only [vals, Fin.cases_succ]
      split_ifs with h
      · subst h
        rw [map_add, map_sub, hg, hg, hr]
        abel
      · simpa using hg (MvPolynomial.X i)

/-- **The base change from a presentation `f₀` to a smooth presentation is a
quasi-isomorphism**, for a module with an integrable connection whose base changes along the two
coprojections `D(0) → D(1)` are identified by a horizontal isomorphism and whose base change along
every coprojection `D(0) → D(n)` is a quasi-isomorphism: the core of the proof of
[Stacks, Lemma 60.21.4, Tag 07LH].  The map `a : D → D'` is any divided power `A`-algebra map
compatible with the augmentations to `C`. -/
theorem quasiIso_baseChangeHom_smoothPresentationOfTower
    (M : FormsData.ConnModule (presTowerFormsData s f₀ 0))
    (hσ : ∀ n : ℕ,
      QuasiIso (M.baseChangeHom (presTowerReindexHom s f₀ hf₀ (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0))))
    (Θ : FormsData.ConnModule.Hom
      (M.baseChange (presTowerReindexHom s f₀ hf₀ (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)))
      (M.baseChange (presTowerReindexHom s f₀ hf₀ (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1))))
    (hΘ : Function.Bijective Θ.toLinearMap)
    {P' : Type u} [CommRing P'] [Algebra s.A P'] [Algebra.Smooth (s.A : Type u) P']
    (f' : P' →ₐ[s.A] s.C) (hf' : Function.Surjective f')
    (htower : ∃ (n : ℕ) (q : MvPolynomial (Fin (n + 1) × ι₀) s.A →ₐ[s.A] P'),
      Function.Surjective q ∧ f'.comp q = tensorPowerPresentation s f₀ n)
    (a : AdicCompletion
        (pAdicIdeal (A := (tensorPowerEnvelope s (f₀) 0).object) s.p)
        (tensorPowerEnvelope s (f₀) 0).object →ₐ[(s.A : Type u)]
      AdicCompletion (pAdicIdeal (A := (presentationEnvelope s f').object) s.p)
        (presentationEnvelope s f').object)
    (ha : IsDPMorphism (completionDividedPowers s.p
        (tensorPowerEnvelope s (f₀) 0).object.dividedPowers
        (tensorPowerEnvelope_prime_nilpotent s _ (hf₀) 0))
      (completionDividedPowers s.p (presentationEnvelope s f').object.dividedPowers
        (presentationEnvelope_prime_nilpotent s f' hf')) a.toRingHom)
    (haug : (completedEnvelopeAugmentation s f' hf').comp a.toRingHom =
      completedEnvelopeAugmentation s (tensorPowerPresentation s (f₀) 0)
        (tensorPowerPresentation_surjective s _ (hf₀) 0)) :
    QuasiIso (M.baseChangeHom (FormsData.Hom.ofCompletion s.p s.A _
      (presTowerPrime_nilpotent s f₀ hf₀ 0) _
      (presentationEnvelope_prime_nilpotent s f' hf') a ha)) := by
  have hp := presTowerPrime_nilpotent s f₀ hf₀
  have hp' := presentationEnvelope_prime_nilpotent s f' hf'
  -- a lift of the variables and a tensor power surjecting onto `P'`
  obtain ⟨n, q, hq, hfq⟩ := htower
  -- the retract of [Stacks, Tag 07L5]
  obtain ⟨A₀, B₀, hA₀, hB₀, hAB, -, haugA, haugB⟩ := exists_completedEnvelopeRetractAlgHom s q f'
    hq hf' (tensorPowerPresentation s f₀ n) hfq (tensorPowerPresentation_surjective s _ hf₀ n)
    (hp n)
  let aH : FormsData.Hom (presTowerFormsData s f₀ n) (presentationFormsData s f') :=
    FormsData.Hom.ofCompletion s.p s.A (presTowerDP s f₀ n) (hp n) _ hp' A₀ hA₀
  let bH : FormsData.Hom (presentationFormsData s f') (presTowerFormsData s f₀ n) :=
    FormsData.Hom.ofCompletion s.p s.A _ hp' (presTowerDP s f₀ n) (hp n) B₀ hB₀
  have hid : IsDPMorphism
      (completionDividedPowers s.p (presentationEnvelope s f').object.dividedPowers hp')
      (completionDividedPowers s.p (presentationEnvelope s f').object.dividedPowers hp')
      (AlgHom.id (s.A : Type u) (AdicCompletion
        (pAdicIdeal (A := (presentationEnvelope s f').object) s.p)
        (presentationEnvelope s f').object)).toRingHom := by
    rw [← hAB]
    exact hA₀.comp _ hB₀
  have hab : aH.comp bH = FormsData.Hom.id _ :=
    (FormsData.Hom.ofCompletion_comp s.p s.A _ hp' (presTowerDP s f₀ n) (hp n) _ hp' B₀ hB₀ A₀ hA₀
      (hA₀.comp _ hB₀)).trans
      ((FormsData.Hom.ofCompletion_congr (h := hAB) (hφ' := hid) ..).trans
        (FormsData.Hom.ofCompletion_id s.p s.A _ hp' hid))
  -- the coprojections and the codegeneracy
  let σ := presTowerReindexHom s f₀ hf₀ (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)
  let δ := presTowerReindexHom s f₀ hf₀ (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1)
  let sH := presTowerReindexHom s f₀ hf₀ (SimplexCategory.const ⦋1⦌ ⦋0⦌ 0)
  let σn := presTowerReindexHom s f₀ hf₀ (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)
  have hsσ : sH.comp σ = FormsData.Hom.id _ := by
    rw [presTowerReindexHom_comp, Subsingleton.elim (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0 ≫
      SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) (𝟙 ⦋0⦌), presTowerReindexHom_id]
  have hsδ : sH.comp δ = FormsData.Hom.id _ := by
    rw [presTowerReindexHom_comp, Subsingleton.elim (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1 ≫
      SimplexCategory.const ⦋1⦌ ⦋0⦌ 0) (𝟙 ⦋0⦌), presTowerReindexHom_id]
  have := hσ 1
  have := hσ n
  -- the lift `w : D(1) → D(n)` of `σₙ` and `b ∘ a ∘ σₙ`
  have hr := isDPMorphism_completedReindex s _ hf₀ (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)
  obtain ⟨w, hw, hwσ, hwδ⟩ := exists_completedTensorPowerOneLift s _ hf₀
    (tensorPowerEnvelope s f₀ n).object.dividedPowers (hp n)
    (B₀.comp (A₀.comp (completedReindex s _ (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0))))
    (completedReindex s _ (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0))
    (hB₀.comp _ (hA₀.comp _ hr)) hr fun x ↦
      sub_mem_completionIdeal_of_augmentation_eq s _
        (tensorPowerPresentation_surjective s _ hf₀ n)
        ((DFunLike.congr_fun haugB
          (A₀ (completedReindex s _ (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) x))).trans
          (DFunLike.congr_fun haugA (completedReindex s _ (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0) x)))
  let wH : FormsData.Hom (presTowerFormsData s f₀ 1) (presTowerFormsData s f₀ n) :=
    FormsData.Hom.ofCompletion s.p s.A (presTowerDP s f₀ 1) (hp 1) (presTowerDP s f₀ n) (hp n) w hw
  have hwσH : wH.comp σ = σn :=
    FormsData.Hom.ofCompletion_comp_eq s.p s.A (presTowerDP s f₀ 0) (hp 0) (presTowerDP s f₀ 1)
      (hp 1) (presTowerDP s f₀ n) (hp n) _ hw hr hwσ
  have e1 : bH.comp aH = FormsData.Hom.ofCompletion s.p s.A (presTowerDP s f₀ n) (hp n)
      (presTowerDP s f₀ n) (hp n) (B₀.comp A₀) (hB₀.comp _ hA₀) :=
    FormsData.Hom.ofCompletion_comp_eq s.p s.A (presTowerDP s f₀ n) (hp n) _ hp'
      (presTowerDP s f₀ n) (hp n) hA₀ hB₀ _ rfl
  have e2 : (FormsData.Hom.ofCompletion s.p s.A (presTowerDP s f₀ n) (hp n) (presTowerDP s f₀ n)
      (hp n) (B₀.comp A₀) (hB₀.comp _ hA₀)).comp σn =
      FormsData.Hom.ofCompletion s.p s.A (presTowerDP s f₀ 0) (hp 0) (presTowerDP s f₀ n) (hp n)
        ((B₀.comp A₀).comp (completedReindex s _ (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)))
        (hB₀.comp _ (hA₀.comp _ hr)) :=
    FormsData.Hom.ofCompletion_comp_eq s.p s.A (presTowerDP s f₀ 0) (hp 0) (presTowerDP s f₀ n)
      (hp n) (presTowerDP s f₀ n) (hp n) hr _ _ rfl
  have hwδH : wH.comp δ = (bH.comp aH).comp σn := by
    rw [e1]
    exact (FormsData.Hom.ofCompletion_comp_eq s.p s.A (presTowerDP s f₀ 0) (hp 0)
      (presTowerDP s f₀ 1) (hp 1) (presTowerDP s f₀ n) (hp n) _ hw _
      (hwδ.trans (AlgHom.comp_assoc _ _ _).symm)).trans e2.symm
  have h₁ : QuasiIso (M.baseChangeHom (aH.comp σn)) :=
    FormsData.ConnModule.quasiIso_baseChangeHom_of_retract_of_stratification σ δ sH hsσ hsδ M Θ
      hΘ σn aH bH hab wH hwσH hwδH
  -- the lift `w' : D(1) → D'` of `a ∘ σₙ` and the given map
  obtain ⟨w', hw', hw'σ, hw'δ⟩ := exists_completedTensorPowerOneLift s _ hf₀
    (presentationEnvelope s f').object.dividedPowers hp' a
    (A₀.comp (completedReindex s _ (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0))) ha
    (hA₀.comp _ hr) fun x ↦ sub_mem_completionIdeal_of_augmentation_eq s f' hf'
      ((DFunLike.congr_fun haug x).trans ((DFunLike.congr_fun haugA _).trans
        (DFunLike.congr_fun (completedEnvelopeAugmentation_comp_presTowerReindex s f₀ hf₀
          (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)) x)).symm)
  let w'H : FormsData.Hom (presTowerFormsData s f₀ 1) (presentationFormsData s f') :=
    FormsData.Hom.ofCompletion s.p s.A (presTowerDP s f₀ 1) (hp 1) _ hp' w' hw'
  have e3 : aH.comp σn = FormsData.Hom.ofCompletion s.p s.A (presTowerDP s f₀ 0) (hp 0) _ hp'
      (A₀.comp (completedReindex s _ (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0))) (hA₀.comp _ hr) :=
    FormsData.Hom.ofCompletion_comp_eq s.p s.A (presTowerDP s f₀ 0) (hp 0) (presTowerDP s f₀ n)
      (hp n) _ hp' hr hA₀ _ rfl
  have hw'σH : w'H.comp σ = aH.comp σn := by
    rw [e3]
    exact FormsData.Hom.ofCompletion_comp_eq s.p s.A (presTowerDP s f₀ 0) (hp 0)
      (presTowerDP s f₀ 1) (hp 1) _ hp' _ hw' _ hw'σ
  have hw'δH : w'H.comp δ =
      FormsData.Hom.ofCompletion s.p s.A (presTowerDP s f₀ 0) (hp 0) _ hp' a ha :=
    FormsData.Hom.ofCompletion_comp_eq s.p s.A (presTowerDP s f₀ 0) (hp 0) (presTowerDP s f₀ 1)
      (hp 1) _ hp' _ hw' _ hw'δ
  have : QuasiIso (M.baseChangeHom (w'H.comp σ)) := by
    rwa [hw'σH]
  have h₂ := FormsData.ConnModule.quasiIso_baseChangeHom_comp_of_stratification σ δ sH hsσ hsδ M
    Θ hΘ w'H
  rwa [hw'δH] at h₂
/-- **There is a divided power `A`-algebra map `D → D'` compatible with the augmentations**, for
every smooth presentation `A → P' → C`: the completion of the map of envelopes induced by a lift
of the variables of the presentation `f₀` to `P'`; the tower hypothesis `htower` holds as soon as
`f₀` has a variable (`Crystalline.exists_tensorPowerSurjectionOfTower`). -/
theorem exists_smoothPresentationMapOfTower {P' : Type u} [CommRing P'] [Algebra s.A P']
    [Algebra.Smooth (s.A : Type u) P'] (f' : P' →ₐ[s.A] s.C) (hf' : Function.Surjective f')
    (htower : ∃ (n : ℕ) (q : MvPolynomial (Fin (n + 1) × ι₀) s.A →ₐ[s.A] P'),
      Function.Surjective q ∧ f'.comp q = tensorPowerPresentation s f₀ n) :
    ∃ (a : AdicCompletion
        (pAdicIdeal (A := (tensorPowerEnvelope s (f₀) 0).object) s.p)
        (tensorPowerEnvelope s (f₀) 0).object →ₐ[(s.A : Type u)]
      AdicCompletion (pAdicIdeal (A := (presentationEnvelope s f').object) s.p)
        (presentationEnvelope s f').object),
      IsDPMorphism (completionDividedPowers s.p
          (tensorPowerEnvelope s (f₀) 0).object.dividedPowers
          (tensorPowerEnvelope_prime_nilpotent s _ (hf₀) 0))
        (completionDividedPowers s.p (presentationEnvelope s f').object.dividedPowers
          (presentationEnvelope_prime_nilpotent s f' hf')) a.toRingHom ∧
      (completedEnvelopeAugmentation s f' hf').comp a.toRingHom =
        completedEnvelopeAugmentation s (tensorPowerPresentation s (f₀) 0)
          (tensorPowerPresentation_surjective s _ (hf₀) 0) := by
  obtain ⟨n, q, hq, hfq⟩ := htower
  obtain ⟨A₀, -, hA₀, -, -, -, haugA, -⟩ := exists_completedEnvelopeRetractAlgHom s q f' hq hf'
    (tensorPowerPresentation s f₀ n) hfq (tensorPowerPresentation_surjective s _ hf₀ n)
    (tensorPowerEnvelope_prime_nilpotent s _ hf₀ n)
  exact ⟨A₀.comp (completedReindex s _ (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)),
    hA₀.comp _ (isDPMorphism_completedReindex s _ hf₀ _),
    RingHom.ext fun x ↦ (DFunLike.congr_fun haugA _).trans (DFunLike.congr_fun
      (completedEnvelopeAugmentation_comp_presTowerReindex s f₀ hf₀
        (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0)) x)⟩

end TowerMain

section Canonical

variable (s : AffineCrystallineSituation.{u, u})

attribute [local instance] tensorPowerEnvelopeAlgebraInstance presentationEnvelopeAlgebraInst

/-- `p` is nilpotent modulo the divided power ideal of each degree of the cosimplicial envelope
of the canonical presentation. -/
theorem canonicalPrime_nilpotent (n : ℕ) :
    IsNilpotent (Ideal.Quotient.mk ((envelopeDPAlgebra s (canonicalPresentation s)).ideal n)
      (s.p : (envelopeDPAlgebra s (canonicalPresentation s)).carrier n)) :=
  presTowerPrime_nilpotent s _ (canonicalPresentation_surjective s) n

/-- The divided powers of the degree `n` of the cosimplicial envelope of the canonical
presentation. -/
abbrev canonicalDP (n : ℕ) :
    DividedPowers ((envelopeDPAlgebra s (canonicalPresentation s)).ideal n) :=
  presTowerDP s (canonicalPresentation s) n

/-- The ring `D(n)` with its completed forms: the degree `n` of the completed cosimplicial
envelope of the canonical presentation. -/
abbrev canonicalFormsData (n : ℕ) : FormsData.{u} s.p :=
  presTowerFormsData s (canonicalPresentation s) n

/-- The completed reindexing map of a map of finite ordinals, as a morphism of rings with forms,
for the canonical presentation. -/
abbrev canonicalReindexHom {m n : SimplexCategory} (φ : m ⟶ n) :
    FormsData.Hom (canonicalFormsData s m.len) (canonicalFormsData s n.len) :=
  presTowerReindexHom s (canonicalPresentation s) (canonicalPresentation_surjective s) φ

/-- The completed reindexing morphisms compose. -/
theorem canonicalReindexHom_comp {m n k : SimplexCategory} (φ : m ⟶ n) (ψ : n ⟶ k) :
    (canonicalReindexHom s ψ).comp (canonicalReindexHom s φ) = canonicalReindexHom s (φ ≫ ψ) :=
  presTowerReindexHom_comp s _ (canonicalPresentation_surjective s) φ ψ

/-- The completed reindexing morphism of an identity is the identity. -/
theorem canonicalReindexHom_id (n : SimplexCategory) :
    canonicalReindexHom s (𝟙 n) = FormsData.Hom.id _ :=
  presTowerReindexHom_id s _ (canonicalPresentation_surjective s) n

/-- The completed reindexing maps are compatible with the augmentations to `C`. -/
theorem completedEnvelopeAugmentation_comp_completedReindex {m n : SimplexCategory}
    (φ : m ⟶ n) :
    (completedEnvelopeAugmentation s (tensorPowerPresentation s (canonicalPresentation s) n.len)
        (tensorPowerPresentation_surjective s _ (canonicalPresentation_surjective s) n.len)).comp
      (completedReindex s _ φ).toRingHom =
      completedEnvelopeAugmentation s (tensorPowerPresentation s (canonicalPresentation s) m.len)
        (tensorPowerPresentation_surjective s _ (canonicalPresentation_surjective s) m.len) :=
  completedEnvelopeAugmentation_comp_presTowerReindex s _ (canonicalPresentation_surjective s) φ

/-- A smooth presentation of `C` receives a surjection from a tensor power of the canonical
presentation. -/
private theorem exists_canonical_tensorPowerSurjection {P' : Type u} [CommRing P']
    [Algebra s.A P'] [Algebra.Smooth (s.A : Type u) P'] (f' : P' →ₐ[s.A] s.C)
    (hf' : Function.Surjective f') :
    ∃ (n : ℕ) (q : MvPolynomial (Fin (n + 1) × s.C) s.A →ₐ[s.A] P'),
      Function.Surjective q ∧
        f'.comp q = tensorPowerPresentation s (canonicalPresentation s) n := by
  classical
  obtain ⟨n, q, hq, hfq, -⟩ := exists_tensorPowerSurjection s P' f'
    (MvPolynomial.aeval fun c ↦ Function.surjInv hf' c)
    (MvPolynomial.algHom_ext fun c ↦ by simp [canonicalPresentation, Function.surjInv_eq hf'])
  exact ⟨n, q, hq, hfq⟩

/-- **The base change from the canonical presentation to a smooth presentation is a
quasi-isomorphism**, for a module with an integrable connection whose base changes along the two
coprojections `D(0) → D(1)` are identified by a horizontal isomorphism and whose base change along
every coprojection `D(0) → D(n)` is a quasi-isomorphism: the core of the proof of
[Stacks, Lemma 60.21.4, Tag 07LH].  The map `a : D → D'` is any divided power `A`-algebra map
compatible with the augmentations to `C`. -/
theorem quasiIso_baseChangeHom_smoothPresentation
    (M : FormsData.ConnModule (canonicalFormsData s 0))
    (hσ : ∀ n : ℕ,
      QuasiIso (M.baseChangeHom (canonicalReindexHom s (SimplexCategory.const ⦋0⦌ ⦋n⦌ 0))))
    (Θ : FormsData.ConnModule.Hom
      (M.baseChange (canonicalReindexHom s (SimplexCategory.const ⦋0⦌ ⦋1⦌ 0)))
      (M.baseChange (canonicalReindexHom s (SimplexCategory.const ⦋0⦌ ⦋1⦌ 1))))
    (hΘ : Function.Bijective Θ.toLinearMap)
    {P' : Type u} [CommRing P'] [Algebra s.A P'] [Algebra.Smooth (s.A : Type u) P']
    (f' : P' →ₐ[s.A] s.C) (hf' : Function.Surjective f')
    (a : AdicCompletion
        (pAdicIdeal (A := (tensorPowerEnvelope s (canonicalPresentation s) 0).object) s.p)
        (tensorPowerEnvelope s (canonicalPresentation s) 0).object →ₐ[(s.A : Type u)]
      AdicCompletion (pAdicIdeal (A := (presentationEnvelope s f').object) s.p)
        (presentationEnvelope s f').object)
    (ha : IsDPMorphism (completionDividedPowers s.p
        (tensorPowerEnvelope s (canonicalPresentation s) 0).object.dividedPowers
        (tensorPowerEnvelope_prime_nilpotent s _ (canonicalPresentation_surjective s) 0))
      (completionDividedPowers s.p (presentationEnvelope s f').object.dividedPowers
        (presentationEnvelope_prime_nilpotent s f' hf')) a.toRingHom)
    (haug : (completedEnvelopeAugmentation s f' hf').comp a.toRingHom =
      completedEnvelopeAugmentation s (tensorPowerPresentation s (canonicalPresentation s) 0)
        (tensorPowerPresentation_surjective s _ (canonicalPresentation_surjective s) 0)) :
    QuasiIso (M.baseChangeHom (FormsData.Hom.ofCompletion s.p s.A _
      (canonicalPrime_nilpotent s 0) _
      (presentationEnvelope_prime_nilpotent s f' hf') a ha)) :=
  quasiIso_baseChangeHom_smoothPresentationOfTower s _ (canonicalPresentation_surjective s) M hσ Θ
    hΘ f' hf'
    (exists_canonical_tensorPowerSurjection s f' hf') a ha haug

/-- **There is a divided power `A`-algebra map `D → D'` compatible with the augmentations**, for
every smooth presentation `A → P' → C`: the completion of the map of envelopes induced by a lift
of the variables of the canonical presentation to `P'`. -/
theorem exists_smoothPresentationMap {P' : Type u} [CommRing P'] [Algebra s.A P']
    [Algebra.Smooth (s.A : Type u) P'] (f' : P' →ₐ[s.A] s.C) (hf' : Function.Surjective f') :
    ∃ (a : AdicCompletion
        (pAdicIdeal (A := (tensorPowerEnvelope s (canonicalPresentation s) 0).object) s.p)
        (tensorPowerEnvelope s (canonicalPresentation s) 0).object →ₐ[(s.A : Type u)]
      AdicCompletion (pAdicIdeal (A := (presentationEnvelope s f').object) s.p)
        (presentationEnvelope s f').object),
      IsDPMorphism (completionDividedPowers s.p
          (tensorPowerEnvelope s (canonicalPresentation s) 0).object.dividedPowers
          (tensorPowerEnvelope_prime_nilpotent s _ (canonicalPresentation_surjective s) 0))
        (completionDividedPowers s.p (presentationEnvelope s f').object.dividedPowers
          (presentationEnvelope_prime_nilpotent s f' hf')) a.toRingHom ∧
      (completedEnvelopeAugmentation s f' hf').comp a.toRingHom =
        completedEnvelopeAugmentation s (tensorPowerPresentation s (canonicalPresentation s) 0)
          (tensorPowerPresentation_surjective s _ (canonicalPresentation_surjective s) 0) :=
  exists_smoothPresentationMapOfTower s _ (canonicalPresentation_surjective s) f' hf'
    (exists_canonical_tensorPowerSurjection s f' hf')

end Canonical

end Crystalline

end
