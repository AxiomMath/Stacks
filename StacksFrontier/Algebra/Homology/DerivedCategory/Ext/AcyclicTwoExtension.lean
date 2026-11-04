module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.ExactSequences
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex

/-!
# Yoneda products with a two-extension through `Ext`-acyclic middle terms

Let `P` be an object of an abelian category and let

`0 ⟶ A ⟶ B ⟶ M ⟶ N ⟶ 0`

be exact, with `Ext^•(P, B) = 0` and `Ext^•(P, M) = 0`. Splitting the sequence at the image `I` of
`B ⟶ M` gives two short exact sequences `0 → A → B → I → 0` and `0 → I → M → N → 0`, with
classes `e₁ ∈ Ext¹(I, A)` and `e₂ ∈ Ext¹(N, I)`; their Yoneda product is a class
`γ = e₂ ∘ e₁ ∈ Ext²(N, A)`. The two covariant long exact sequences of `Ext(P, -)` show that the
Yoneda product with `γ`

`Ext^n(P, N) ⟶ Ext^{n+2}(P, A)`,  `y ↦ y ∘ γ`

is bijective for every `n`, and that `Ext^n(P, A) = 0` for `n < 2`.

The main source of such sequences is a complex `K` of `Ext(P, -)`-acyclic objects concentrated in
nonnegative degrees whose cohomology vanishes in degrees `≥ 2`: then
`0 → Z⁰(K) → K⁰ → Z¹(K) → H¹(K) → 0` is exact, and the cycles `Z¹(K)` are `Ext(P, -)`-acyclic,
being resolved by the acyclic objects `K¹ → K² → ⋯`. With `K = j_* I^•` for an injective
resolution `I^•` of a sheaf on an open `U` and `P` a sheaf supported off `U`, this is how the
higher direct images of `j` compute `Ext^•(P, -)` (cohomological purity in codimension one).

## Main definitions

* `CategoryTheory.Abelian.Ext.twoExtensionClass`: the class `γ ∈ Ext²(N, A)` of a four-term exact
  sequence `0 → A → B → M → N → 0`.

## Main results

* `CategoryTheory.Abelian.Ext.bijective_comp_extClass_of_subsingleton`: Yoneda product with the
  class of a short exact sequence whose middle term is `Ext(P, -)`-acyclic is bijective.
* `CategoryTheory.Abelian.Ext.subsingleton_of_shortExact_family`: the first terms of a family of
  short exact sequences `0 → Zₙ → Mₙ → Zₙ₊₁ → 0` with acyclic middle terms are acyclic.
* `CategoryTheory.Abelian.Ext.bijective_comp_twoExtensionClass`: Yoneda product with the class of a
  four-term exact sequence with acyclic middle terms is bijective.
* `CategoryTheory.Abelian.Ext.subsingleton_of_twoExtension`: `Ext^n(P, A) = 0` for `n < 2`.
* `CategoryTheory.Abelian.Ext.subsingleton_ext_cycles_one`: the cycles in degree one of a complex
  of acyclic objects with cohomology vanishing in degrees `≥ 2` are acyclic.
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory Category Limits

namespace CategoryTheory.Abelian.Ext

variable {C : Type u} [Category.{v} C] [Abelian C] [HasExt.{w} C]

section ShortExact

variable {S : ShortComplex C} (hS : S.ShortExact) (P : C)

/-- **Yoneda product with the class of a short exact sequence `0 → X₁ → X₂ → X₃ → 0` is
bijective** `Ext^{n₀}(P, X₃) → Ext^{n₀+1}(P, X₁)` when `Ext^•(P, X₂) = 0`. -/
theorem bijective_comp_extClass_of_subsingleton (h : ∀ n, Subsingleton (Ext P S.X₂ n))
    {n₀ n₁ : ℕ} (hn : n₀ + 1 = n₁) :
    Function.Bijective (fun x : Ext P S.X₃ n₀ => x.comp hS.extClass hn) := by
  refine ⟨fun a b hab => ?_, fun y => covariant_sequence_exact₁ P hS y (Subsingleton.elim _ _) hn⟩
  have hab' : (a - b).comp hS.extClass hn = 0 := by
    rw [sub_eq_add_neg, add_comp, neg_comp]
    exact add_neg_eq_zero.mpr hab
  obtain ⟨x₂, hx₂⟩ := covariant_sequence_exact₃ P hS (a - b) hn hab'
  rw [Subsingleton.elim x₂ 0, zero_comp] at hx₂
  exact sub_eq_zero.mp hx₂.symm

include hS in
/-- `Ext⁰(P, X₁) = 0` for a short exact sequence `0 → X₁ → X₂ → X₃ → 0` with
`Ext⁰(P, X₂) = 0`. -/
theorem subsingleton_ext_zero_of_shortExact (h : Subsingleton (Ext P S.X₂ 0)) :
    Subsingleton (Ext P S.X₁ 0) := by
  have := hS.mono_f
  exact (postcomp_mk₀_injective_of_mono P S.f).subsingleton

end ShortExact

/-- `Ext^{m+1}(P, X₁) = 0` for a short exact sequence `0 → X₁ → X₂ → X₃ → 0` with
`Ext^•(P, X₂) = 0` and `Ext^m(P, X₃) = 0`. -/
private theorem subsingleton_ext_succ_of_shortExact {S : ShortComplex C} (hS : S.ShortExact)
    (P : C) (h : ∀ n, Subsingleton (Ext P S.X₂ n))
    {m : ℕ} (h₃ : Subsingleton (Ext P S.X₃ m)) : Subsingleton (Ext P S.X₁ (m + 1)) :=
  (bijective_comp_extClass_of_subsingleton hS P h rfl).2.subsingleton

/-- **Acyclicity propagates along a family of short exact sequences with acyclic middle
terms.** If `0 → Zₙ → Mₙ → Zₙ₊₁ → 0` is short exact for every `n` and `Ext^•(P, Mₙ) = 0`, then
`Ext^•(P, Zₙ) = 0` for every `n`: in degree `m + 1` the connecting map identifies
`Ext^{m+1}(P, Zₙ)` with `Ext^m(P, Zₙ₊₁)`. -/
theorem subsingleton_of_shortExact_family (P : C) (S : ℕ → ShortComplex C)
    (hS : ∀ n, (S n).ShortExact) (hX : ∀ n, (S n).X₃ = (S (n + 1)).X₁)
    (hM : ∀ n m, Subsingleton (Ext P (S n).X₂ m)) (m n : ℕ) :
    Subsingleton (Ext P (S n).X₁ m) := by
  induction m generalizing n with
  | zero => exact subsingleton_ext_zero_of_shortExact (hS n) P (hM n 0)
  | succ m ih =>
    exact subsingleton_ext_succ_of_shortExact (hS n) P (hM n) (by rw [hX n]; exact ih (n + 1))

section TwoExtension

variable {A B M N : C}

/-- The first half `0 → A → B → im(g) → 0` of a four-term exact sequence. -/
abbrev twoExtensionLeft (f : A ⟶ B) (g : B ⟶ M) (hfg : f ≫ g = 0) : ShortComplex C :=
  ShortComplex.mk f (Limits.factorThruImage g) (by simp [← cancel_mono (Limits.image.ι g), hfg])

/-- The second half `0 → im(g) → M → N → 0` of a four-term exact sequence. -/
abbrev twoExtensionRight (g : B ⟶ M) (h : M ⟶ N) (hgh : g ≫ h = 0) : ShortComplex C :=
  ShortComplex.mk (Limits.image.ι g) h (by simp [← cancel_epi (Limits.factorThruImage g), hgh])

omit [HasExt C] in
/-- If `f` is mono and `A → B → M` is exact, then `0 → A → B → im(g) → 0` is short exact. -/
theorem twoExtensionLeft_shortExact (f : A ⟶ B) (g : B ⟶ M) (hfg : f ≫ g = 0) [Mono f]
    (ex₁ : (ShortComplex.mk f g hfg).Exact) : (twoExtensionLeft f g hfg).ShortExact where
  exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := twoExtensionLeft f g hfg) (S₂ := ShortComplex.mk f g hfg)
      { τ₁ := 𝟙 A, τ₂ := 𝟙 B, τ₃ := Limits.image.ι g, comm₂₃ := by simp }).mpr ex₁

omit [HasExt C] in
/-- If `h` is epi and `B → M → N` is exact, then `0 → im(g) → M → N → 0` is short exact. -/
theorem twoExtensionRight_shortExact (g : B ⟶ M) (h : M ⟶ N) (hgh : g ≫ h = 0) [Epi h]
    (ex₂ : (ShortComplex.mk g h hgh).Exact) : (twoExtensionRight g h hgh).ShortExact where
  exact := (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
      (S₁ := ShortComplex.mk g h hgh) (S₂ := twoExtensionRight g h hgh)
      { τ₁ := Limits.factorThruImage g, τ₂ := 𝟙 M, τ₃ := 𝟙 N, comm₁₂ := by simp }).mp ex₂

/-- **The class `γ ∈ Ext²(N, A)` of a four-term exact sequence** `0 → A → B → M → N → 0`: the
Yoneda product of the classes of its two halves `0 → im(g) → M → N → 0` and
`0 → A → B → im(g) → 0`. -/
def twoExtensionClass (f : A ⟶ B) (g : B ⟶ M) (h : M ⟶ N) (hfg : f ≫ g = 0)
    (hgh : g ≫ h = 0) [Mono f] [Epi h] (ex₁ : (ShortComplex.mk f g hfg).Exact)
    (ex₂ : (ShortComplex.mk g h hgh).Exact) : Ext N A 2 :=
  (twoExtensionRight_shortExact g h hgh ex₂).extClass.comp
    (twoExtensionLeft_shortExact f g hfg ex₁).extClass (by rfl)

/-- **Yoneda product with the class of a four-term exact sequence `0 → A → B → M → N → 0` is
bijective** `Ext^n(P, N) → Ext^{n+2}(P, A)` when `Ext^•(P, B) = 0` and `Ext^•(P, M) = 0`. -/
theorem bijective_comp_twoExtensionClass (f : A ⟶ B) (g : B ⟶ M) (h : M ⟶ N)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) [Mono f] [Epi h] (ex₁ : (ShortComplex.mk f g hfg).Exact)
    (ex₂ : (ShortComplex.mk g h hgh).Exact) (P : C) (hB : ∀ n, Subsingleton (Ext P B n))
    (hM : ∀ n, Subsingleton (Ext P M n)) (n : ℕ) :
    Function.Bijective (fun y : Ext P N n =>
      y.comp (twoExtensionClass f g h hfg hgh ex₁ ex₂) (rfl : n + 2 = n + 2)) := by
  have e : (fun y : Ext P N n =>
      y.comp (twoExtensionClass f g h hfg hgh ex₁ ex₂) (rfl : n + 2 = n + 2)) =
      (fun z : Ext P (Limits.image g) (n + 1) =>
        z.comp (twoExtensionLeft_shortExact f g hfg ex₁).extClass (rfl : n + 1 + 1 = n + 2)) ∘
      (fun y : Ext P N n => y.comp (twoExtensionRight_shortExact g h hgh ex₂).extClass
        (rfl : n + 1 = n + 1)) := by
    funext y
    exact (comp_assoc _ _ _ rfl rfl rfl).symm
  rw [e]
  exact Function.Bijective.comp
    (bijective_comp_extClass_of_subsingleton (twoExtensionLeft_shortExact f g hfg ex₁) P hB
      (rfl : n + 1 + 1 = n + 2))
    (bijective_comp_extClass_of_subsingleton (twoExtensionRight_shortExact g h hgh ex₂) P hM
      (rfl : n + 1 = n + 1))

/-- `Ext^n(P, A) = 0` for `n < 2` for a four-term exact sequence `0 → A → B → M → N → 0` with
`Ext^•(P, B) = 0` and `Ext^•(P, M) = 0`. -/
theorem subsingleton_of_twoExtension (f : A ⟶ B) (g : B ⟶ M) (h : M ⟶ N)
    (hfg : f ≫ g = 0) (hgh : g ≫ h = 0) [Mono f] [Epi h] (ex₁ : (ShortComplex.mk f g hfg).Exact)
    (ex₂ : (ShortComplex.mk g h hgh).Exact) (P : C) (hB : ∀ n, Subsingleton (Ext P B n))
    (hM : ∀ n, Subsingleton (Ext P M n)) (n : ℕ) (hn : n < 2) :
    Subsingleton (Ext P A n) := by
  have hI : Subsingleton (Ext P (Limits.image g) 0) :=
    subsingleton_ext_zero_of_shortExact (twoExtensionRight_shortExact g h hgh ex₂) P (hM 0)
  rcases n with _ | _ | n
  · exact subsingleton_ext_zero_of_shortExact (twoExtensionLeft_shortExact f g hfg ex₁) P (hB 0)
  · exact subsingleton_ext_succ_of_shortExact (twoExtensionLeft_shortExact f g hfg ex₁) P hB hI
  · omega

end TwoExtension

section Complex

variable (K : CochainComplex C ℕ)

/-- The short exact sequence `0 → Zⁿ(K) → Kⁿ → Zⁿ⁺¹(K)`, exact on the right when `K` is exact in
degree `n + 1`. -/
abbrev cyclesShortComplex (n : ℕ) : ShortComplex C :=
  ShortComplex.mk (K.iCycles n) (K.toCycles n (n + 1)) (by
    simp [← cancel_mono (K.iCycles (n + 1))])

omit [HasExt C] in
/-- The sequence `Zⁿ(K) → Kⁿ → Zⁿ⁺¹(K)` is exact. -/
theorem cyclesShortComplex_exact (n : ℕ) : (cyclesShortComplex K n).Exact :=
  ShortComplex.exact_of_f_is_kernel _
    (isKernelOfComp (K.iCycles (n + 1)) (K.d n (n + 1))
      (K.cyclesIsKernel n (n + 1) (CochainComplex.next ℕ n)) _ (K.toCycles_i n (n + 1)))

omit [HasExt C] in
/-- If `Hⁿ⁺¹(K) = 0`, then the map `Kⁿ → Zⁿ⁺¹(K)` is an epimorphism. -/
theorem epi_toCycles_of_isZero_homology (n : ℕ) (hn : IsZero (K.homology (n + 1))) :
    Epi (K.toCycles n (n + 1)) :=
  Preadditive.epi_of_isZero_cokernel' _ (K.homologyIsCokernel n (n + 1)
    (CochainComplex.prev_nat_succ n)) hn

omit [HasExt C] in
/-- If `Hⁿ⁺¹(K) = 0`, then `0 → Zⁿ(K) → Kⁿ → Zⁿ⁺¹(K) → 0` is short exact. -/
theorem cyclesShortComplex_shortExact (n : ℕ) (hn : IsZero (K.homology (n + 1))) :
    (cyclesShortComplex K n).ShortExact :=
  have := epi_toCycles_of_isZero_homology K n hn
  { exact := cyclesShortComplex_exact K n }

/-- **The cycles `Z¹(K)` of a complex of `Ext(P, -)`-acyclic objects with vanishing cohomology in
degrees `≥ 2` are `Ext(P, -)`-acyclic**: they are resolved by `K¹ → K² → ⋯`. -/
theorem subsingleton_ext_cycles_one (P : C) (hK : ∀ q m, Subsingleton (Ext P (K.X q) m))
    (hH : ∀ q, 2 ≤ q → IsZero (K.homology q)) (m : ℕ) :
    Subsingleton (Ext P (K.cycles 1) m) :=
  subsingleton_of_shortExact_family P (fun n => cyclesShortComplex K (n + 1))
    (fun n => cyclesShortComplex_shortExact K (n + 1) (hH _ (by omega))) (fun _ => rfl)
    (fun n m => hK (n + 1) m) m 0

omit [HasExt C] in
/-- The exact sequence `Z⁰(K) → K⁰ → Z¹(K)`. -/
theorem exact_iCycles_zero_toCycles : (ShortComplex.mk (K.iCycles 0) (K.toCycles 0 1)
    (cyclesShortComplex K 0).zero).Exact :=
  cyclesShortComplex_exact K 0

omit [HasExt C] in
/-- The exact sequence `K⁰ → Z¹(K) → H¹(K) → 0`. -/
theorem exact_toCycles_homologyπ : (ShortComplex.mk (K.toCycles 0 1) (K.homologyπ 1)
    (K.toCycles_comp_homologyπ 0 1)).Exact :=
  ShortComplex.exact_of_g_is_cokernel _ (K.homologyIsCokernel 0 1 (CochainComplex.prev_nat_succ 0))

/-- **The class in `Ext²(H¹(K), Z⁰(K))` of a complex `K` concentrated in nonnegative degrees**:
the class of the four-term exact sequence `0 → Z⁰(K) → K⁰ → Z¹(K) → H¹(K) → 0`. -/
def complexTwoExtensionClass : Ext (K.homology 1) (K.cycles 0) 2 :=
  twoExtensionClass (K.iCycles 0) (K.toCycles 0 1) (K.homologyπ 1) _ _
    (exact_iCycles_zero_toCycles K) (exact_toCycles_homologyπ K)

/-- **Yoneda product with the class of a complex `K` of `Ext(P, -)`-acyclic objects with
cohomology vanishing in degrees `≥ 2` is bijective**, `Ext^n(P, H¹(K)) → Ext^{n+2}(P, Z⁰(K))`. -/
theorem bijective_comp_complexTwoExtensionClass (P : C)
    (hK : ∀ q m, Subsingleton (Ext P (K.X q) m)) (hH : ∀ q, 2 ≤ q → IsZero (K.homology q))
    (n : ℕ) :
    Function.Bijective (fun y : Ext P (K.homology 1) n =>
      y.comp (complexTwoExtensionClass K) (rfl : n + 2 = n + 2)) :=
  bijective_comp_twoExtensionClass _ _ _ _ _ (exact_iCycles_zero_toCycles K)
    (exact_toCycles_homologyπ K) P (hK 0) (subsingleton_ext_cycles_one K P hK hH) n

/-- `Ext^n(P, Z⁰(K)) = 0` for `n < 2`, for a complex `K` of `Ext(P, -)`-acyclic objects with
cohomology vanishing in degrees `≥ 2`. -/
theorem subsingleton_ext_cycles_zero (P : C) (hK : ∀ q m, Subsingleton (Ext P (K.X q) m))
    (hH : ∀ q, 2 ≤ q → IsZero (K.homology q)) (n : ℕ) (hn : n < 2) :
    Subsingleton (Ext P (K.cycles 0) n) :=
  subsingleton_of_twoExtension _ _ _ _ _ (exact_iCycles_zero_toCycles K)
    (exact_toCycles_homologyπ K) P (hK 0) (subsingleton_ext_cycles_one K P hK hH) n hn

end Complex

end CategoryTheory.Abelian.Ext

end
