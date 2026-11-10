module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Order.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Interval
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeHom
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.CategoryTheory.Triangulated.Elementary
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.YonedaClassMap

/-!
# `Ext^1` and extensions, and vanishing of `Ext`

## Main results

* `CategoryTheory.Abelian.Ext.extClass_surjective_and_eq_iff_iso_and_baerSum`: the class map of
  short exact sequences is surjective onto `Ext^1_𝒜(B, A)`, separates exactly the isomorphism
  classes of extensions of `B` by `A`, and takes Baer sums to sums; so `Ext^1_𝒜(B, A)` is the
  Ext-group of extensions of `B` by `A`.
* `CategoryTheory.hasProjectiveDimensionLT_of_forall_ext_eq_zero`: vanishing of `Ext^p_𝒜(X, -)`
  implies `HasProjectiveDimensionLT X p`, in an arbitrary abelian category.
* `CategoryTheory.ShortComplex.ShortExact.extClass_comp_extClass_eq_zero_iff`: the Yoneda
  product of the classes of two composable short exact sequences vanishes exactly when the first
  is the restriction of an extension of the middle term of the second.
* `DerivedCategory.bijective_homologyFunctor_shiftMap_of_isLE_of_isGE`: taking homology in
  degree `a` is a bijection `Ext^n_𝒜(X, Y) → Hom_𝒜(H^a(X), H^{a'}(Y))` when `X` lives in
  degrees `≤ a`, `Y` in degrees `≥ b`, and `n + a = a' ≤ b`.

## References

* [Stacks Project 06XS](https://stacks.math.columbia.edu/tag/06XS)
* [Stacks Project 06XV](https://stacks.math.columbia.edu/tag/06XV)
* [Stacks Project 0EWW](https://stacks.math.columbia.edu/tag/0EWW)
* [Stacks Project 0GSM](https://stacks.math.columbia.edu/tag/0GSM)
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

namespace Abelian

open Limits ComposableArrows

/-! ### `Ext^1` and extensions -/

section

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt.{w} 𝒜] {A B : 𝒜}

/-- Naturality of the class map of a short exact sequence, for a comparison given by its three
components: if `(u, v, w)` is a morphism of short exact sequences `S₁ ⟶ S₂`, then the
corestriction of `[S₁]` along `u` is the restriction of `[S₂]` along `w`. -/
private lemma extClass_comp_mk₀_eq_mk₀_comp_extClass {S₁ S₂ : ShortComplex 𝒜}
    (h₁ : S₁.ShortExact) (h₂ : S₂.ShortExact) (u : S₁.X₁ ⟶ S₂.X₁) (v : S₁.X₂ ⟶ S₂.X₂)
    (w : S₁.X₃ ⟶ S₂.X₃) (hu : S₁.f ≫ v = u ≫ S₂.f) (hw : v ≫ S₂.g = S₁.g ≫ w) :
    h₁.extClass.comp (Ext.mk₀ u) (add_zero 1) = (Ext.mk₀ w).comp h₂.extClass (zero_add 1) :=
  h₁.extClass_naturality h₂ { τ₁ := u, τ₂ := v, τ₃ := w, comm₁₂ := hu.symm, comm₂₃ := hw }

/-- **A short exact sequence is the restriction of an extension exactly when its class is.**
A short exact sequence `0 → A → Z → B → 0` is the restriction along `φ : B ⟶ Z'` of a short
exact sequence `0 → A → W → Z' → 0`, i.e. admits a comparison map `i : Z ⟶ W` which is the
identity on `A` and `φ` on the quotients, if and only if its class is the restriction along
`φ` of the class of the latter.

For `⇒`, the map `g ≫ φ : Z ⟶ Z'` is killed by the class of the second sequence
(`CategoryTheory.ShortComplex.ShortExact.comp_extClass`), so the covariant long exact sequence
of the second sequence lifts it to a map `i₀ : Z ⟶ W`
(`CategoryTheory.Abelian.Ext.covariant_sequence_exact₃`). The map `u : A ⟶ A` induced by `i₀` on
the sub-objects satisfies `(𝟙 A - u)_* [Z] = 0` by naturality of the class, hence
`𝟙 A - u = f ≫ t` for some `t : Z ⟶ A` by the contravariant long exact sequence of the first
sequence (`CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁`), and `i₀ + t ≫ a` is the
required morphism. -/
private lemma extClass_eq_mk₀_comp_extClass_iff {Z W Z' : 𝒜} {f : A ⟶ Z} {g : Z ⟶ B}
    {hfg : f ≫ g = 0} {a : A ⟶ W} {q : W ⟶ Z'} {haq : a ≫ q = 0}
    (hS : (ShortComplex.mk f g hfg).ShortExact) (hW : (ShortComplex.mk a q haq).ShortExact)
    (φ : B ⟶ Z') :
    hS.extClass = (Ext.mk₀ φ).comp hW.extClass (zero_add 1) ↔
      ∃ i : Z ⟶ W, f ≫ i = a ∧ i ≫ q = g ≫ φ := by
  have := hS.mono_f
  have := hW.mono_f
  refine ⟨fun hcl ↦ ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ Z hW (Ext.mk₀ (g ≫ φ)) (zero_add 1)
      (by rw [← Ext.mk₀_comp_mk₀_assoc, ← hcl, hS.comp_extClass])
    obtain ⟨i₀, rfl⟩ := (Ext.mk₀_bijective _ _).2 x
    have hi₀ : i₀ ≫ q = g ≫ φ := (Ext.mk₀_bijective _ _).1 (by rwa [Ext.mk₀_comp_mk₀] at hx)
    obtain ⟨u, hu⟩ := hW.exact.lift' (f ≫ i₀)
      (by rw [Category.assoc, hi₀, ← Category.assoc, hfg, zero_comp])
    obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS A (Ext.mk₀ (𝟙 A - u)) (add_zero 1)
      (by rw [sub_eq_add_neg, Ext.mk₀_add, Ext.mk₀_neg, Ext.comp_add, Ext.comp_neg,
        extClass_comp_mk₀_eq_mk₀_comp_extClass hS hW u i₀ φ hu.symm hi₀, ← hcl,
        Ext.comp_mk₀_id, add_neg_cancel])
    obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
    have ht : f ≫ t = 𝟙 A - u := (Ext.mk₀_bijective _ _).1 (by rwa [Ext.mk₀_comp_mk₀] at hy)
    refine ⟨i₀ + t ≫ a, ?_, ?_⟩
    · rw [Preadditive.comp_add, ← Category.assoc, ht, Preadditive.sub_comp, Category.id_comp, hu]
      abel
    · rw [Preadditive.add_comp, hi₀, Category.assoc, haq, comp_zero, add_zero]
  · rintro ⟨i, hfi, hiq⟩
    rw [← extClass_comp_mk₀_eq_mk₀_comp_extClass hS hW (𝟙 A) i φ (by simpa using hfi) hiq,
      Ext.comp_mk₀_id]

/-- **Naturality of the class of a short exact sequence.** If the extension `0 → A → E → C → 0`
maps to the extension `0 → A → T → D → 0` by the identity on `A` and by `β : C ⟶ D` on the
right, then the class of the first is the composite of `β` with the class of the second. -/
private lemma extClass_eq_mk₀_comp_extClass {C D E T : 𝒜} {i : A ⟶ E} {p : E ⟶ C}
    {hw : i ≫ p = 0} {j : A ⟶ T} {q : T ⟶ D} {hwT : j ≫ q = 0}
    (h : (ShortComplex.mk i p hw).ShortExact) (hT : (ShortComplex.mk j q hwT).ShortExact)
    (β : C ⟶ D) (v : E ⟶ T) (hv : i ≫ v = j) (hv' : v ≫ q = p ≫ β) :
    h.extClass = (Ext.mk₀ β).comp hT.extClass (zero_add 1) :=
  (extClass_eq_mk₀_comp_extClass_iff h hT β).2 ⟨v, hv, hv'⟩

/-- **Isomorphic extensions have the same class.** -/
private lemma extClass_eq_of_iso {E E' : 𝒜} {i : A ⟶ E} {p : E ⟶ B} {hw : i ≫ p = 0}
    {i' : A ⟶ E'} {p' : E' ⟶ B} {hw' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p hw).ShortExact) (h' : (ShortComplex.mk i' p' hw').ShortExact)
    (φ : E ≅ E') (h₁ : i ≫ φ.hom = i') (h₂ : φ.hom ≫ p' = p) : h.extClass = h'.extClass := by
  rw [extClass_eq_mk₀_comp_extClass h h' (𝟙 B) φ.hom h₁ (by rw [h₂, Category.comp_id]),
    Ext.mk₀_id_comp]

/-- **The class map is surjective**: every element of `Ext^1_𝒜(B, A)` is the class of a short
exact sequence `0 → A → E → B → 0`.

The element `ξ` is killed by a monomorphism `A ⟶ Z`
(`exists_shortExact_comp_mk₀_eq_zero`), hence, by the covariant long exact sequence
of the short exact sequence `S : 0 → A → Z → C → 0`, of the form `ξ = u ∘ δ(S)` for a map
`u : B ⟶ C`; and the pullback of `S` along `u` is a short exact sequence `0 → A → Z ×_C B → B → 0`
of class `ξ`, by naturality of `CategoryTheory.ShortComplex.ShortExact.extClass`. -/
private lemma exists_shortExact_extClass_eq (B A : 𝒜) (ξ : Ext.{w} B A 1) :
    ∃ (E : 𝒜) (i : A ⟶ E) (p : E ⟶ B) (hw : i ≫ p = 0)
      (h : (ShortComplex.mk i p hw).ShortExact), h.extClass = ξ := by
  obtain ⟨Z, C, f, p, hz, hS, hξ⟩ := exists_shortExact_comp_mk₀_eq_zero B A 0 ξ
  obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ B hS ξ hξ (zero_add 1)
  obtain ⟨u, hu⟩ := (Ext.mk₀_bijective _ _).2 x₃
  obtain ⟨W, f', q, hz', hS', v, hv₁, hv₂⟩ := exists_shortExact_pullback hS u
  refine ⟨W, f', q, hz', hS', ?_⟩
  rw [extClass_eq_mk₀_comp_extClass hS' hS u v hv₁ hv₂.symm, hu]
  exact hx₃

/-- **Two extensions with the same class admit a morphism.** Two short exact sequences
`0 → A → E → B → 0` and `0 → A → E' → B → 0` with the same class in `Ext^1_𝒜(B, A)` admit a
morphism `E ⟶ E'` over the identity of `A` and of `B`.

The map `p : E ⟶ B` is killed by the class of the second sequence
(`CategoryTheory.ShortComplex.ShortExact.comp_extClass`), so the covariant long exact sequence
of the second sequence lifts it to a map `q : E ⟶ E'` with `q ≫ p' = p`
(`CategoryTheory.Abelian.Ext.covariant_sequence_exact₃`). The map `u : A ⟶ A` induced by `q` on
the sub-objects satisfies `δ ∘ (u - 𝟙) = 0` by naturality of the class, hence `u - 𝟙 = i ≫ k`
for some `k : E ⟶ A` by the contravariant long exact sequence of the first sequence
(`CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁`), and `q - k ≫ i'` is the required
morphism. -/
@[ega "0 12.3.2" "partial"]
private lemma exists_hom_of_extClass_eq {E E' : 𝒜} {i : A ⟶ E} {p : E ⟶ B} {hw : i ≫ p = 0}
    {i' : A ⟶ E'} {p' : E' ⟶ B} {hw' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p hw).ShortExact) (h' : (ShortComplex.mk i' p' hw').ShortExact)
    (hcl : h.extClass = h'.extClass) : ∃ q : E ⟶ E', i ≫ q = i' ∧ q ≫ p' = p := by
  obtain ⟨q, hq₁, hq₂⟩ := (extClass_eq_mk₀_comp_extClass_iff h h' (𝟙 B)).1
    (by rw [hcl, Ext.mk₀_id_comp])
  exact ⟨q, hq₁, by simpa using hq₂⟩

/-- **Two extensions have the same class if and only if they are isomorphic.** -/
private lemma extClass_eq_iff_exists_iso {E E' : 𝒜} {i : A ⟶ E} {p : E ⟶ B} {hw : i ≫ p = 0}
    {i' : A ⟶ E'} {p' : E' ⟶ B} {hw' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p hw).ShortExact) (h' : (ShortComplex.mk i' p' hw').ShortExact) :
    h.extClass = h'.extClass ↔ ∃ φ : E ≅ E', i ≫ φ.hom = i' ∧ φ.hom ≫ p' = p := by
  refine ⟨fun hcl => ?_, fun ⟨φ, h₁, h₂⟩ => extClass_eq_of_iso h h' φ h₁ h₂⟩
  obtain ⟨q, hq₁, hq₂⟩ := exists_hom_of_extClass_eq h h' hcl
  have := isIso₂_of_shortExact_of_id₁₃ h h' q hq₁ hq₂
  exact ⟨asIso q, hq₁, hq₂⟩

/-- **A summand of a direct sum of extensions.** Let `0 → A → T → B ⊞ B → 0` receive the direct
sum of the extensions `0 → A → E₁ → B → 0` and `0 → A → E₂ → B → 0` over the sum map
`Σ : A ⊞ A → A`, by `u : E₁ ⊞ E₂ ⟶ T`. An extension `0 → A → F → B → 0` mapping into that direct
sum by `ε : F ⟶ E₁ ⊞ E₂` over a section `α` of `Σ` and over `β : B ⟶ B ⊞ B` on the right then
has class `β ∘ δ(T)`: composing with `u` cancels `α` against `Σ`, and
`extClass_eq_mk₀_comp_extClass` applies to `ε ≫ u`. -/
private lemma extClass_eq_mk₀_comp_extClass_of_biprod {E₁ E₂ F T : 𝒜} {i₁ : A ⟶ E₁} {p₁ : E₁ ⟶ B}
    {i₂ : A ⟶ E₂} {p₂ : E₂ ⟶ B} {iF : A ⟶ F} {pF : F ⟶ B} {hwF : iF ≫ pF = 0}
    {j : A ⟶ T} {q : T ⟶ B ⊞ B} {hwT : j ≫ q = 0}
    (hF : (ShortComplex.mk iF pF hwF).ShortExact) (hT : (ShortComplex.mk j q hwT).ShortExact)
    (u : E₁ ⊞ E₂ ⟶ T) (hu : biprod.map i₁ i₂ ≫ u = biprod.desc (𝟙 A) (𝟙 A) ≫ j)
    (hu' : u ≫ q = biprod.map p₁ p₂)
    (α : A ⟶ A ⊞ A) (ε : F ⟶ E₁ ⊞ E₂) (β : B ⟶ B ⊞ B)
    (hα : α ≫ biprod.desc (𝟙 A) (𝟙 A) = 𝟙 A) (hε : iF ≫ ε = α ≫ biprod.map i₁ i₂)
    (hε' : ε ≫ biprod.map p₁ p₂ = pF ≫ β) :
    hF.extClass = (Ext.mk₀ β).comp hT.extClass (zero_add 1) :=
  extClass_eq_mk₀_comp_extClass hF hT β (ε ≫ u)
    (by rw [← Category.assoc, hε, Category.assoc, hu, ← Category.assoc, hα, Category.id_comp])
    (by rw [Category.assoc, hu', hε'])

/-- **The class of a Baer sum is the sum of the classes.** If the extension
`0 → A → T → B ⊞ B → 0` receives the direct sum extension of `0 → A → E₁ → B → 0` and
`0 → A → E₂ → B → 0` over the sum map `A ⊞ A → A`, and if `0 → A → E → B → 0` maps to it over
the diagonal `B ⟶ B ⊞ B`, then `δ(E) = δ(E₁) + δ(E₂)`. -/
@[ega "0 12.3.2" "additivity"]
private lemma extClass_eq_add_of_baerSum {E₁ E₂ E T : 𝒜} {i₁ : A ⟶ E₁} {p₁ : E₁ ⟶ B}
    {hw₁ : i₁ ≫ p₁ = 0} {i₂ : A ⟶ E₂} {p₂ : E₂ ⟶ B} {hw₂ : i₂ ≫ p₂ = 0}
    {i : A ⟶ E} {p : E ⟶ B} {hw : i ≫ p = 0}
    {j : A ⟶ T} {q : T ⟶ B ⊞ B} {hwT : j ≫ q = 0}
    (h₁ : (ShortComplex.mk i₁ p₁ hw₁).ShortExact) (h₂ : (ShortComplex.mk i₂ p₂ hw₂).ShortExact)
    (h : (ShortComplex.mk i p hw).ShortExact) (hT : (ShortComplex.mk j q hwT).ShortExact)
    (u : E₁ ⊞ E₂ ⟶ T) (v : E ⟶ T)
    (hu : biprod.map i₁ i₂ ≫ u = biprod.desc (𝟙 A) (𝟙 A) ≫ j)
    (hu' : u ≫ q = biprod.map p₁ p₂)
    (hv : i ≫ v = j) (hv' : v ≫ q = p ≫ biprod.lift (𝟙 B) (𝟙 B)) :
    h.extClass = h₁.extClass + h₂.extClass := by
  rw [extClass_eq_mk₀_comp_extClass h hT _ v hv hv',
    extClass_eq_mk₀_comp_extClass_of_biprod h₁ hT u hu hu' biprod.inl biprod.inl biprod.inl
      (by simp) (by simp) (by simp),
    extClass_eq_mk₀_comp_extClass_of_biprod h₂ hT u hu hu' biprod.inr biprod.inr biprod.inr
      (by simp) (by simp) (by simp),
    ← Ext.add_comp, ← Ext.mk₀_add, biprod.lift_eq, Category.id_comp, Category.id_comp]

end

section

variable (𝒜 : Type*) [Category 𝒜] [Abelian 𝒜] [HasExt.{w} 𝒜]

/-- **`Ext^1` is the Ext-group of extensions.** Let `𝒜` be an abelian category and let `A`, `B`
be objects of `𝒜`. The class `δ(E) ∈ Ext^1_𝒜(B, A)` of an extension
`E : 0 → A → E → B → 0` of `B` by `A`, i.e. Mathlib's
`CategoryTheory.ShortComplex.ShortExact.extClass`, has the following three properties:

* every element of `Ext^1_𝒜(B, A)` is the class of an extension of `B` by `A`;
* two extensions of `B` by `A` have the same class if and only if they are isomorphic, i.e.
  there is an isomorphism of their middle terms compatible with the maps from `A` and to `B`;
* the class of a Baer sum is the sum of the classes: if `0 → A → T → B ⊕ B → 0` is an
  extension receiving a morphism from the direct sum extension
  `0 → A ⊕ A → E₁ ⊕ E₂ → B ⊕ B → 0` over the sum map `Σ : A ⊕ A → A`, and if
  `0 → A → E → B → 0` maps to it over the diagonal `Δ : B → B ⊕ B`, then
  `δ(E) = δ(E₁) + δ(E₂)`.

Hence `δ` induces an isomorphism from the Ext-group `Ext_𝒜(B, A)` of isomorphism classes of
extensions of `B` by `A` under Baer sum onto the group `Ext^1_𝒜(B, A)`. -/
@[stacks 06XV, ega "0 12.3.2", sga "7 VII 3.2.5" "partial"]
public theorem Ext.extClass_surjective_and_eq_iff_iso_and_baerSum (B A : 𝒜) :
    (∀ x : Ext.{w} B A 1, ∃ (E : 𝒜) (i : A ⟶ E) (p : E ⟶ B) (w : i ≫ p = 0)
        (h : (ShortComplex.mk i p w).ShortExact), h.extClass = x) ∧
    (∀ (E E' : 𝒜) (i : A ⟶ E) (p : E ⟶ B) (w : i ≫ p = 0) (i' : A ⟶ E') (p' : E' ⟶ B)
        (w' : i' ≫ p' = 0) (h : (ShortComplex.mk i p w).ShortExact)
        (h' : (ShortComplex.mk i' p' w').ShortExact),
        h.extClass = h'.extClass ↔ ∃ φ : E ≅ E', i ≫ φ.hom = i' ∧ φ.hom ≫ p' = p) ∧
    (∀ (E₁ E₂ E T : 𝒜) (i₁ : A ⟶ E₁) (p₁ : E₁ ⟶ B) (w₁ : i₁ ≫ p₁ = 0)
        (i₂ : A ⟶ E₂) (p₂ : E₂ ⟶ B) (w₂ : i₂ ≫ p₂ = 0)
        (i : A ⟶ E) (p : E ⟶ B) (w : i ≫ p = 0)
        (j : A ⟶ T) (q : T ⟶ B ⊞ B) (wT : j ≫ q = 0)
        (h₁ : (ShortComplex.mk i₁ p₁ w₁).ShortExact)
        (h₂ : (ShortComplex.mk i₂ p₂ w₂).ShortExact)
        (h : (ShortComplex.mk i p w).ShortExact)
        (_hT : (ShortComplex.mk j q wT).ShortExact)
        (u : E₁ ⊞ E₂ ⟶ T) (v : E ⟶ T),
        biprod.map i₁ i₂ ≫ u = biprod.desc (𝟙 A) (𝟙 A) ≫ j →
        u ≫ q = biprod.map p₁ p₂ →
        i ≫ v = j → v ≫ q = p ≫ biprod.lift (𝟙 B) (𝟙 B) →
          h.extClass = h₁.extClass + h₂.extClass) :=
  ⟨exists_shortExact_extClass_eq B A,
    fun _ _ _ _ _ _ _ _ h h' => extClass_eq_iff_exists_iso h h',
    fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ h₁ h₂ h hT u v hu hu' hv hv' =>
      extClass_eq_add_of_baerSum h₁ h₂ h hT u v hu hu' hv hv'⟩

end

end Abelian

/-! ### Vanishing of `Ext` and projective dimension -/

section

open Limits Abelian

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜] [HasExt.{w} 𝒜]

/-- An object all of whose degree `0` `Ext` groups out of it vanish is a zero object: its
identity is the zero morphism. -/
private lemma isZero_of_forall_ext_eq_zero (X : 𝒜)
    (h : ∀ (Y : 𝒜) (e : Ext.{w} X Y 0), e = 0) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  refine (Ext.mk₀_bijective X X).injective ?_
  rw [Ext.mk₀_zero]
  exact h X _

/-- **Dimension shifting along Yoneda extensions.** If `p ≥ 1` and `Ext^p_𝒜(X, Y) = 0` for every
`Y`, then `Ext^i_𝒜(X, Y) = 0` for every `i ≥ p` and every `Y`: a class in `Ext^{j + 1}_𝒜(X, Y)`
with `p ≤ j` is the class `δ(E)` of a Yoneda extension `E` of `X` by `Y` of degree `j + 1`
([Stacks, Tag 06XU]); as `j ≥ 1`, cutting `E` at its left end (`Abelian.exists_cut`)
factors `δ(E)` through a class of degree `j`, which vanishes by induction. -/
private lemma ext_eq_zero_of_le (X : 𝒜) (p : ℕ) (hp : 1 ≤ p)
    (h : ∀ (Y : 𝒜) (e : Ext.{w} X Y p), e = 0) :
    ∀ (i : ℕ), p ≤ i → ∀ (Y : 𝒜) (e : Ext.{w} X Y i), e = 0 := by
  intro i
  induction i with
  | zero => exact fun h0 => absurd (hp.trans h0) (by omega)
  | succ j ih =>
    intro hi Y e
    rcases eq_or_lt_of_le hi with heq | hlt
    · subst heq
      exact h Y e
    · have hpj : p ≤ j := by omega
      obtain ⟨n, rfl⟩ : ∃ n, j = n + 1 := ⟨j - 1, by omega⟩
      obtain ⟨E, rfl⟩ := Abelian.surjective_extClassMap X Y (n + 1) e
      obtain ⟨C, E', q, hq, hS, φ, hc₁, hc₂⟩ := Abelian.exists_cut E
      dsimp only
      rw [Abelian.extClassMap_succ_of_cut E E' q hq hS φ hc₁ hc₂,
        ih hpj C (Abelian.extClassMap n E'), Ext.zero_comp]

/-- **Vanishing of `Ext^p_𝒜(X, -)` forces projective dimension `< p`.**
If `𝒜` is an abelian category and `Ext^p_𝒜(X, Y) = 0` for every object `Y` of `𝒜`, then `X` has
projective dimension `< p`, i.e. `Ext^i_𝒜(X, Y) = 0` for every `i ≥ p` and every `Y`. This
generalizes `CategoryTheory.hasProjectiveDimensionLT_of_enoughInjectives` by dropping the
assumption `[EnoughInjectives 𝒜]`. [Stacks, Tag 0EWW] states the reading for all pairs of
objects at once, which follows by applying this to every object of `𝒜`. -/
@[stacks 0EWW]
public theorem hasProjectiveDimensionLT_of_forall_ext_eq_zero (X : 𝒜) (p : ℕ)
    (h : ∀ (Y : 𝒜) (e : Abelian.Ext.{w} X Y p), e = 0) : HasProjectiveDimensionLT X p := by
  obtain _ | q := p
  · exact (isZero_of_forall_ext_eq_zero X h).hasProjectiveDimensionLT_zero
  · exact HasProjectiveDimensionLT.mk
      (fun i hi Y e => ext_eq_zero_of_le X (q + 1) (by omega) h i hi Y e)

end

/-! ### Vanishing of a Yoneda product of two extension classes -/

namespace ShortComplex.ShortExact

open Limits Abelian

section

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt.{w} 𝒜] {X Y : 𝒜} {S : ShortComplex 𝒜}

/-- **Lifting criterion.** A morphism `ψ : X ⟶ S.X₃` into the quotient term of a short exact
sequence `S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` factors through `S.X₂` if and only if the
restriction `ψ^* [S] ∈ Ext^1_𝒜(X, S.X₁)` of the class of `S` along it vanishes. This is
exactness of the covariant long exact sequence of `S` at `Ext^0_𝒜(X, S.X₃)`. -/
@[sga "7 VII 3.3.6" "Exactness at Ext⁰(L•"]
private lemma mk₀_comp_extClass_eq_zero_iff (hS : S.ShortExact) (ψ : X ⟶ S.X₃) :
    (Ext.mk₀ ψ).comp hS.extClass (zero_add 1) = 0 ↔ ∃ l : X ⟶ S.X₂, l ≫ S.g = ψ := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨x, hx⟩ := Ext.covariant_sequence_exact₃ X hS (Ext.mk₀ ψ) (zero_add 1) h
    obtain ⟨l, rfl⟩ := (Ext.mk₀_bijective X S.X₂).surjective x
    exact ⟨l, (Ext.mk₀_bijective X S.X₃).injective (by rwa [Ext.mk₀_comp_mk₀] at hx)⟩
  · rintro ⟨l, rfl⟩
    rw [← Ext.mk₀_comp_mk₀_assoc, hS.comp_extClass, Ext.comp_zero]

/-- **Extension criterion.** A morphism `v : S.X₁ ⟶ Y` out of the sub-object of a short exact
sequence `S : 0 → S.X₁ → S.X₂ → S.X₃ → 0` extends to `S.X₂` if and only if the corestriction
`v_* [S] ∈ Ext^1_𝒜(S.X₃, Y)` of the class of `S` along it vanishes. This is exactness of the
contravariant long exact sequence of `S` at `Ext^0_𝒜(S.X₁, Y)`. -/
@[sga "7 VII 3.4.9" "partial"]
private lemma extClass_comp_mk₀_eq_zero_iff (hS : S.ShortExact) (v : S.X₁ ⟶ Y) :
    hS.extClass.comp (Ext.mk₀ v) (add_zero 1) = 0 ↔ ∃ t : S.X₂ ⟶ Y, S.f ≫ t = v := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨y, hy⟩ := Ext.contravariant_sequence_exact₁ hS Y (Ext.mk₀ v) (add_zero 1) h
    obtain ⟨t, rfl⟩ := (Ext.mk₀_bijective S.X₂ Y).surjective y
    exact ⟨t, (Ext.mk₀_bijective S.X₁ Y).injective (by rwa [Ext.mk₀_comp_mk₀] at hy)⟩
  · rintro ⟨t, rfl⟩
    rw [← Ext.mk₀_comp_mk₀]
    exact hS.extClass_comp_assoc _

variable {A Z B W Z' C : 𝒜} {f : A ⟶ Z} {g : Z ⟶ B} {hfg : f ≫ g = 0}
  {a : A ⟶ W} {q : W ⟶ Z'} {haq : a ≫ q = 0}

omit [HasExt.{w} 𝒜] in
/-- The third column of the diagram of [Stacks, Tag 0GSM] is a consequence of the rest: if
`0 → A → Z → B → 0`, `0 → B → Z' → C → 0` and `0 → A → W → Z' → 0` are short exact and
`i : Z ⟶ W` is the identity on `A` and `f'` on the quotients, then `0 → Z → W → C → 0` is short
exact. -/
private lemma shortExact_column {f' : B ⟶ Z'} {g' : Z' ⟶ C} {hf'g' : f' ≫ g' = 0}
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    (hS' : (ShortComplex.mk f' g' hf'g').ShortExact)
    (hW : (ShortComplex.mk a q haq).ShortExact) (i : Z ⟶ W)
    (hfi : f ≫ i = a) (hiq : i ≫ q = g ≫ f') (hip : i ≫ (q ≫ g') = 0) :
    (ShortComplex.mk i (q ≫ g') hip).ShortExact := by
  have := hS.mono_f; have := hS.epi_g; have := hS'.mono_f
  have := hS'.epi_g; have := hW.mono_f; have := hW.epi_g
  have hmono : Mono i :=
    ShortComplex.mono_τ₂_of_exact_of_mono
      (S₁ := ShortComplex.mk f g hfg) (S₂ := ShortComplex.mk a q haq)
      { τ₁ := 𝟙 A, τ₂ := i, τ₃ := f'
        comm₁₂ := by simpa using hfi.symm
        comm₂₃ := hiq } hS.exact
  refine { exact := ?_, mono_f := hmono, epi_g := epi_comp q g' }
  refine ShortComplex.exact_of_g_is_cokernel _ (CokernelCofork.IsColimit.ofπ' _ hip ?_)
  intro T k hk
  -- `k` kills `a = f ≫ i`, hence descends along `q` to some `m : Z' ⟶ T`.
  have hak : a ≫ k = 0 := by rw [← hfi, Category.assoc, hk, comp_zero]
  obtain ⟨m, hm⟩ : { m : Z' ⟶ T // q ≫ m = k } := ⟨_, hW.exact.g_desc k hak⟩
  -- `m` kills `f'` because `g` is epi, hence descends along `g'` to the required map.
  have hf'm : f' ≫ m = 0 := by
    rw [← cancel_epi g, comp_zero, ← Category.assoc, ← hiq, Category.assoc, hm, hk]
  exact ⟨hS'.exact.desc m hf'm, by rw [Category.assoc, hS'.exact.g_desc m hf'm, hm]⟩

end

section

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt.{w} 𝒜]

/-- **Vanishing of a Yoneda product of two extension classes.** Let `0 → A → Z → B → 0` and
`0 → B → Z' → C → 0` be short exact sequences in an abelian category `𝒜`, with classes
`[Z] ∈ Ext^1_𝒜(B, A)` and `[Z'] ∈ Ext^1_𝒜(C, B)`. Then the Yoneda product
`[Z] ∘ [Z'] ∈ Ext^2_𝒜(C, A)` is zero if and only if there is a commutative diagram with exact
rows and columns

```
                 0             0
                 ↓             ↓
  0 →   A   →    Z     →       B      →  0
      ‖ 1 ‖      ↓             ↓
  0 →   A   →    W     →       Z'     →  0
                 ↓             ↓
                 C   → ‖ 1 ‖ → C
                 ↓             ↓
                 0             0
```

in `𝒜`, i.e. if and only if `0 → A → Z → B → 0` is the restriction along `B → Z'` of an
extension `0 → A → W → Z' → 0` of `Z'` by `A`. -/
@[stacks 0GSM]
public theorem extClass_comp_extClass_eq_zero_iff {A Z B Z' C : 𝒜}
    {f : A ⟶ Z} {g : Z ⟶ B} {hfg : f ≫ g = 0}
    (hS : (ShortComplex.mk f g hfg).ShortExact)
    {f' : B ⟶ Z'} {g' : Z' ⟶ C} {hf'g' : f' ≫ g' = 0}
    (hS' : (ShortComplex.mk f' g' hf'g').ShortExact) :
    hS'.extClass.comp hS.extClass rfl = 0 ↔
      ∃ (W : 𝒜) (a : A ⟶ W) (q : W ⟶ Z') (i : Z ⟶ W) (p : W ⟶ C)
        (haq : a ≫ q = 0) (hip : i ≫ p = 0),
        (ShortComplex.mk a q haq).ShortExact ∧ (ShortComplex.mk i p hip).ShortExact ∧
          f ≫ i = a ∧ i ≫ q = g ≫ f' ∧ q ≫ g' = p := by
  refine ⟨fun h ↦ ?_, ?_⟩
  · obtain ⟨ξ, hξ⟩ := Ext.contravariant_sequence_exact₁ hS' A hS.extClass rfl h
    obtain ⟨W, a, q, haq, hW, hWξ⟩ := Abelian.exists_shortExact_extClass_eq Z' A ξ
    obtain ⟨i, hfi, hiq⟩ := (extClass_eq_mk₀_comp_extClass_iff hS hW f').1 (by rw [hWξ, ← hξ])
    have hip : i ≫ (q ≫ g') = 0 := by
      rw [← Category.assoc, hiq, Category.assoc, hf'g', comp_zero]
    exact ⟨W, a, q, i, q ≫ g', haq, hip, hW, shortExact_column hS hS' hW i hfi hiq hip,
      hfi, hiq, rfl⟩
  · rintro ⟨W, a, q, i, p, haq, hip, hW, -, hfi, hiq, -⟩
    rw [(extClass_eq_mk₀_comp_extClass_iff hS hW f').2 ⟨i, hfi, hiq⟩]
    exact hS'.extClass_comp_assoc hW.extClass

end

end ShortComplex.ShortExact

end CategoryTheory

/-! ### Ext between objects of the derived category with disjoint homology ranges -/

namespace DerivedCategory

section

open CategoryTheory Category Limits Pretriangulated Triangulated

variable {D : Type*} [Category D]

/-- Postcomposition with an isomorphism is bijective on morphisms: this is
`CategoryTheory.Iso.homToEquiv`. -/
private lemma bijective_comp_right {X Y Y' : D} (β : Y ⟶ Y') [IsIso β] :
    Function.Bijective (fun f : X ⟶ Y ↦ f ≫ β) :=
  (Iso.homToEquiv (asIso β)).bijective

/-- Pre- and postcomposition with isomorphisms is bijective on morphisms: this is
`CategoryTheory.Iso.homCongr`. -/
private lemma bijective_comp_comp {X X' Y Y' : D} (α : X ⟶ X') [IsIso α] (β : Y ⟶ Y')
    [IsIso β] : Function.Bijective (fun f : X' ⟶ Y ↦ α ≫ f ≫ β) :=
  ((asIso α).symm.homCongr (asIso β)).bijective

end

section

open CategoryTheory Category Limits Pretriangulated Triangulated TStructure

variable {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]

/-- If the first vertex of a distinguished triangle has vanishing homology in degrees `a`
and `a + 1`, then the second morphism of the triangle induces an isomorphism on `H^a`. -/
private lemma isIso_homologyFunctor_map_mor₂ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (a : ℤ) (h₀ : IsZero ((homologyFunctor C a).obj T.obj₁))
    (h₁ : IsZero ((homologyFunctor C (a + 1)).obj T.obj₁)) :
    IsIso ((homologyFunctor C a).map T.mor₂) := by
  have : Mono ((homologyFunctor C a).map T.mor₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff T hT a).2 (h₀.eq_of_src _ _)
  have : Epi ((homologyFunctor C a).map T.mor₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff T hT a (a + 1) rfl).2 (h₁.eq_of_tgt _ _)
  apply isIso_of_mono_of_epi

/-- If the third vertex of a distinguished triangle has vanishing homology in degrees `a - 1`
and `a`, then the first morphism of the triangle induces an isomorphism on `H^a`. -/
private lemma isIso_homologyFunctor_map_mor₁ (T : Triangle (DerivedCategory C))
    (hT : T ∈ distTriang _) (a : ℤ) (h₀ : IsZero ((homologyFunctor C a).obj T.obj₃))
    (h₁ : IsZero ((homologyFunctor C (a - 1)).obj T.obj₃)) :
    IsIso ((homologyFunctor C a).map T.mor₁) := by
  have : Epi ((homologyFunctor C a).map T.mor₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff T hT a).2 (h₀.eq_of_tgt _ _)
  have : Mono ((homologyFunctor C a).map T.mor₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff T hT (a - 1) a (by omega)).2 (h₁.eq_of_src _ _)
  apply isIso_of_mono_of_epi

/-- Let `X`, `Z` be objects of `D(𝒜)` with `X` in degrees `≤ a` and `Z` in degrees `≥ a`.
Then taking homology in degree `a` is a bijection
`Hom_{D(𝒜)}(X, Z) → Hom_𝒜(H^a(X), H^a(Z))`. -/
public theorem bijective_homologyFunctor_map_of_isLE_of_isGE (X Z : DerivedCategory C) (a : ℤ)
    [X.IsLE a] [Z.IsGE a] :
    Function.Bijective (fun f : X ⟶ Z ↦ (homologyFunctor C a).map f) := by
  have hUle : t.IsLE ((t.truncGE a).obj X) a :=
    t.isLE_of_iso ((t.truncGTIsoTruncGE (a - 1) a (by omega)).app X) a
  have hUle' : t.IsLE ((t.truncGE a).obj X) (a + 1 - 1) :=
    t.isLE_of_le _ a _ (by omega)
  have hVge : t.IsGE ((t.truncLT (a + 1)).obj Z) a :=
    t.isGE_of_iso ((t.truncLEIsoTruncLT a (a + 1) rfl).app Z) a
  -- the two comparison maps induce isomorphisms on `H^a`
  have hp : IsIso ((homologyFunctor C a).map ((t.truncGEπ a).app X)) := by
    refine isIso_homologyFunctor_map_mor₂ ((t.triangleLTGE a).obj X)
      (t.triangleLTGE_distinguished a X) a ?_ ?_
    · exact isZero_of_isLE _ (a - 1) a (by omega)
    · exact isZero_of_isLE _ (a - 1) (a + 1) (by omega)
  have hi : IsIso ((homologyFunctor C a).map ((t.truncLTι (a + 1)).app Z)) := by
    refine isIso_homologyFunctor_map_mor₁ ((t.triangleLTGE (a + 1)).obj Z)
      (t.triangleLTGE_distinguished (a + 1) Z) a ?_ ?_
    · exact isZero_of_isGE _ (a + 1) a (by omega)
    · exact isZero_of_isGE _ (a + 1) (a - 1) (by omega)
  -- `Hom(τ_{≥a}X, τ_{<a+1}Z) ≅ Hom(X, Z)`
  have hα : Function.Bijective
      (fun h : (t.truncGE a).obj X ⟶ (t.truncLT (a + 1)).obj Z ↦
        h ≫ (t.truncLTι (a + 1)).app Z) :=
    ⟨fun _ _ hh ↦ t.to_truncLT_obj_ext hh,
      fun f ↦ ⟨t.liftTruncLT f a (a + 1) rfl, t.liftTruncLT_ι f a (a + 1) rfl⟩⟩
  have hβ : Function.Bijective
      (fun k : (t.truncGE a).obj X ⟶ Z ↦ (t.truncGEπ a).app X ≫ k) :=
    ⟨fun _ _ hk ↦ t.from_truncGE_obj_ext hk, fun f ↦ ⟨t.descTruncGE f a, t.π_descTruncGE f a⟩⟩
  refine (Function.Bijective.of_comp_iff _ (hβ.comp hα)).mp ?_
  have key : ((fun f : X ⟶ Z ↦ (homologyFunctor C a).map f) ∘
      ((fun k : (t.truncGE a).obj X ⟶ Z ↦ (t.truncGEπ a).app X ≫ k) ∘
        (fun h : (t.truncGE a).obj X ⟶ (t.truncLT (a + 1)).obj Z ↦
          h ≫ (t.truncLTι (a + 1)).app Z))) =
      (fun k : (homologyFunctor C a).obj ((t.truncGE a).obj X) ⟶
          (homologyFunctor C a).obj ((t.truncLT (a + 1)).obj Z) ↦
        (homologyFunctor C a).map ((t.truncGEπ a).app X) ≫ k ≫
          (homologyFunctor C a).map ((t.truncLTι (a + 1)).app Z)) ∘
        (fun g : (t.truncGE a).obj X ⟶ (t.truncLT (a + 1)).obj Z ↦
          (homologyFunctor C a).map g) := by
    funext g
    simp
  rw [key]
  exact (bijective_comp_comp _ _).comp
    (bijective_homologyFunctor_map a _ _ inferInstance inferInstance inferInstance inferInstance)

/-- Let `𝒜` be an abelian category and let `X`, `Y` be objects of `D(𝒜)` such that
`H^i(X) = 0` for `i > a` and `H^j(Y) = 0` for `j < b`. If `n + a = a'` and `a' ≤ b`, then taking
homology in degree `a`,
`Ext^n_𝒜(X, Y) = Hom_{D(𝒜)}(X, Y⟦n⟧) → Hom_𝒜(H^a(X), H^{a'}(Y))`,
is bijective. For `a' < b` the target is the zero group, so this says that
`Ext^n_𝒜(X, Y) = 0` for `n < b - a`; for `a' = b` it is the identification
`Ext^{b - a}_𝒜(X, Y) = Hom_𝒜(H^a(X), H^b(Y))`. -/
@[stacks 06XS]
public theorem bijective_homologyFunctor_shiftMap_of_isLE_of_isGE
    (X Y : DerivedCategory C) (a b n a' : ℤ) [X.IsLE a] [Y.IsGE b]
    (ha' : n + a = a') (hab : a' ≤ b) :
    Function.Bijective (fun f : DerivedCategory.Ext X Y n ↦
      ((homologyFunctor C 0).shiftMap f a a' ha' :
        (homologyFunctor C a).obj X ⟶ (homologyFunctor C a').obj Y)) := by
  have : (Y⟦n⟧).IsGE (b - n) := t.isGE_shift Y b n (b - n) (by omega)
  have : (Y⟦n⟧).IsGE a := t.isGE_of_ge _ a (b - n) (by omega)
  change Function.Bijective (fun f : X ⟶ Y⟦n⟧ ↦
    ((homologyFunctor C 0).shiftMap f a a' ha' :
      (homologyFunctor C a).obj X ⟶ (homologyFunctor C a').obj Y))
  have key : (fun f : X ⟶ Y⟦n⟧ ↦
      ((homologyFunctor C 0).shiftMap f a a' ha' :
        (homologyFunctor C a).obj X ⟶ (homologyFunctor C a').obj Y)) =
      (fun k : (homologyFunctor C a).obj X ⟶ (homologyFunctor C a).obj (Y⟦n⟧) ↦
        k ≫ ((homologyFunctor C 0).shiftIso n a a' ha').hom.app Y) ∘
        (fun f : X ⟶ Y⟦n⟧ ↦ (homologyFunctor C a).map f) := rfl
  rw [key]
  exact (bijective_comp_right (((homologyFunctor C 0).shiftIso n a a' ha').hom.app Y)).comp
    (bijective_homologyFunctor_map_of_isLE_of_isGE X (Y⟦n⟧) a)

end

end DerivedCategory

end
