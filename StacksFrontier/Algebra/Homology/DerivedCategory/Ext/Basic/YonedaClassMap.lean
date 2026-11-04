module

public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Abelian.Projective.Dimension
import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import Mathlib.Combinatorics.Quiver.ReflQuiver
public import Mathlib.Data.Int.ConditionallyCompleteOrder
public import Mathlib.Data.Int.Interval
public import StacksFrontier.Algebra.Homology.DerivedCategory.SingleDegreeHom
import Mathlib.RingTheory.WittVector.IsPoly
import Mathlib.Tactic.ENatToNat
import Mathlib.Tactic.ReduceModChar
import StacksFrontier.CategoryTheory.Triangulated.Elementary
import StacksCore.Tactic.EgaSgaAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.ExtAndYonedaExtensions

/-!
# The class map of Yoneda extensions

This file cuts and splices Yoneda extensions in an abelian category `𝒜`, and constructs the
class map from Yoneda extensions to `Ext` groups.

## Main results

* `CategoryTheory.Abelian.extClassMap`: the class map `δ`, sending a degree `n + 1` Yoneda
  extension of `B` by `A` to an element of `Ext^{n + 1}_𝒜(B, A)`. It is the unique map which in
  degree `1` is `CategoryTheory.ShortComplex.ShortExact.extClass` and is multiplicative for
  splicing (`CategoryTheory.Abelian.isExtClassMap_extClassMap`,
  `CategoryTheory.Abelian.eq_of_isExtClassMap`), it is surjective
  (`CategoryTheory.Abelian.surjective_extClassMap`), and two Yoneda extensions are equivalent
  exactly when they have the same class (`CategoryTheory.Abelian.extClassMap_eq_of_equivalent`,
  `CategoryTheory.Abelian.equivalent_of_extClassMap_eq`).

## Implementation notes

The class map of Yoneda extensions is not constructed by the recipe `δ(E) = f s⁻¹` of the
source, which needs the complex of `E` together with its quasi-isomorphism to `B[0]` and its map
to `A[i]`. It is characterised instead inside the theory of `Ext` groups: in degree `1` it is
`CategoryTheory.ShortComplex.ShortExact.extClass`, and it is multiplicative for splicing at the
left end. These two properties determine it, because every extension of degree at least `2` can
be cut at its left end, so the theorem can assert uniqueness; the map they characterise is built
here by recursion on the degree along those very cuts.

## References

* [Stacks Project 06XU](https://stacks.math.columbia.edu/tag/06XU)
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory

namespace Abelian

open Limits ComposableArrows

/-! ### Cutting and splicing Yoneda extensions -/

section

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜]

/-- The differential `d^m` of a cochain complex which vanishes in degree `m - 1` and is exact
in degree `m` is a monomorphism. -/
private lemma mono_d_of_exactAt {L : CochainComplex 𝒜 ℤ} {m : ℤ}
    (hm : IsZero (L.X (m - 1))) (hL : L.ExactAt m) : Mono (L.d m (m + 1)) :=
  (ShortComplex.exact_iff_mono _ (hm.eq_of_src _ 0)).1
    ((HomologicalComplex.exactAt_iff' L (m - 1) m (m + 1) (by simp) (by simp)).1 hL)

/-- A null-homotopic morphism of cochain complexes is zero in the derived category. -/
private lemma Q_map_eq_zero_of_homotopy [HasDerivedCategory.{w} 𝒜] {K L : CochainComplex 𝒜 ℤ}
    {f : K ⟶ L} (H : Homotopy f 0) : DerivedCategory.Q.map f = 0 := by
  rw [← cancel_epi ((DerivedCategory.quotientCompQhIso 𝒜).hom.app K),
    ← DerivedCategory.quotientCompQhIso_hom_naturality,
    (HomotopyCategory.quotient_map_eq_zero_iff f).2 ⟨H⟩, Functor.map_zero, zero_comp, comp_zero]

/-- **Killing a morphism to a complex concentrated in one degree.** Let `L` be a cochain
complex whose differential `d^m` is a monomorphism and let `g : L ⟶ A[-m]` be a morphism to the
complex with `A` in degree `m`. Then `A` embeds into the pushout `Z = (L^{m + 1} ⊕ A)/L^m` of
`d^m` along `g^m`, and the composite `L ⟶ A[-m] ⟶ Z[-m]` is null-homotopic, the homotopy being
the other map `L^{m + 1} ⟶ Z` of the pushout. -/
private lemma exists_mono_nonempty_homotopy {L : CochainComplex 𝒜 ℤ} {m : ℤ} {A : 𝒜}
    [Mono (L.d m (m + 1))]
    (g : L ⟶ (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) m).obj A) :
    ∃ (Z : 𝒜) (ι : A ⟶ Z) (_ : Mono ι),
      Nonempty (Homotopy (g ≫ (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) m).map ι) 0) := by
  set γ : L.X m ⟶ A :=
    g.f m ≫ (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m A).hom with hγ
  refine ⟨pushout (L.d m (m + 1)) γ, pushout.inr _ _, inferInstance, ?_⟩
  set h : ∀ (i j : ℤ), (ComplexShape.up ℤ).Rel j i →
      (L.X i ⟶ ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) m).obj
        (pushout (L.d m (m + 1)) γ)).X j) := fun i j hij =>
    if hj : j = m then
      (L.XIsoOfEq (show i = m + 1 by simp only [ComplexShape.up_Rel] at hij; omega)).hom ≫
        pushout.inl _ _ ≫
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) m
            (pushout (L.d m (m + 1)) γ)).inv ≫
          (((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) m).obj
            (pushout (L.d m (m + 1)) γ)).XIsoOfEq hj.symm).hom
    else 0 with hh
  have key : g ≫ (HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) m).map
      (pushout.inr (L.d m (m + 1)) γ) = Homotopy.nullHomotopicMap' h := by
    refine HomologicalComplex.hom_ext _ _ fun i => ?_
    rw [Homotopy.nullHomotopicMap'_f (k₂ := i - 1) (k₀ := i + 1) (by simp) (by simp)]
    by_cases hi : i = m
    · subst hi
      rw [hh]
      simp only [dite_eq_right (show ¬ (i - 1 = i) by omega), HomologicalComplex.single_obj_d,
        comp_zero, add_zero, HomologicalComplex.single_map_f_self, HomologicalComplex.comp_f,
        dite_true, HomologicalComplex.XIsoOfEq, eqToIso_refl, Iso.refl_hom, Category.id_comp,
        ← Category.assoc]
      rw [← hγ, pushout.condition, Category.comp_id]
    · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) m _ i hi).eq_of_tgt _ _
  exact ⟨key ▸ Homotopy.nullHomotopy' h⟩

/-- Exactness of a sequence of composable arrows is inherited by a quotient sequence: if
`ψ : F ⟶ T` is epimorphic in every degree and an isomorphism in every degree but the first,
then `T` is exact as soon as `F` is. -/
private lemma exact_of_epi_of_isIso {n : ℕ} {F T : ComposableArrows 𝒜 n} (ψ : F ⟶ T)
    (hF : F.Exact) (hepi : ∀ (i : ℕ) (hi : i ≤ n), Epi (app' ψ i hi))
    (hiso : ∀ (i : ℕ) (_ : 1 ≤ i) (hi : i ≤ n), IsIso (app' ψ i hi)) : T.Exact := by
  have hc : T.IsComplex := by
    refine IsComplex.mk fun i hi => ?_
    have hi' : i ≤ n := by omega
    have he := hepi i hi'
    rw [← cancel_epi (app' ψ i hi'), comp_zero, ← Category.assoc,
      ← naturality' ψ i (i + 1) (by omega) (by omega), Category.assoc,
      ← naturality' ψ (i + 1) (i + 2) (by omega) (by omega), ← Category.assoc,
      hF.toIsComplex.zero i hi, zero_comp]
  refine Exact.mk hc fun i hi => ?_
  have h1 : Epi (scMap ψ hF.toIsComplex hc i hi).τ₁ := hepi i (by omega)
  have h2 : IsIso (scMap ψ hF.toIsComplex hc i hi).τ₂ := hiso (i + 1) (by omega) (by omega)
  have h3 : IsIso (scMap ψ hF.toIsComplex hc i hi).τ₃ := hiso (i + 2) (by omega) (by omega)
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (scMap ψ hF.toIsComplex hc i hi)).1 (hF.exact i hi)

/-- Exactness of a two-term sequence is unchanged by factoring its first map through an
epimorphism: if `u ≫ v = t` with `u` an epimorphism, then `X → Z → W` is exact if and only if
`Y → Z → W` is. The two complex conditions `t ≫ w = 0` and `v ≫ w = 0` are themselves
equivalent, again because `u` is an epimorphism, so neither is a hypothesis. -/
private lemma exact₂_iff_of_epi_fac {X Y Z W : 𝒜} {u : X ⟶ Y} [Epi u] {v : Y ⟶ Z} {t : X ⟶ Z}
    (ht : u ≫ v = t) (w : Z ⟶ W) : (mk₂ t w).Exact ↔ (mk₂ v w).Exact := by
  have key : ∀ (h₁ : t ≫ w = 0) (h₂ : v ≫ w = 0),
      (ShortComplex.mk t w h₁).Exact ↔ (ShortComplex.mk v w h₂).Exact := fun h₁ h₂ =>
    ShortComplex.exact_iff_of_epi_of_isIso_of_mono ⟨u, 𝟙 _, 𝟙 _, by simpa using ht, by simp⟩
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h₁ : t ≫ w = 0 := h.toIsComplex.zero 0
    have h₂ : v ≫ w = 0 := (cancel_epi u).1 (by rw [← Category.assoc, ht, h₁, comp_zero])
    exact exact₂_mk _ h₂
      ((key h₁ h₂).1 ((ShortComplex.exact_iff_exact_toComposableArrows _).2 h))
  · have h₂ : v ≫ w = 0 := h.toIsComplex.zero 0
    have h₁ : t ≫ w = 0 := by rw [← ht, Category.assoc, h₂, comp_zero]
    exact exact₂_mk _ h₁
      ((key h₁ h₂).2 ((ShortComplex.exact_iff_exact_toComposableArrows _).2 h))

variable {B A : 𝒜}

/-- The two maps of a degree `1` Yoneda extension compose to zero. -/
public lemma comp_g_eq_zero (E : YonedaExtension B A 0) : E.f ≫ E.g = 0 :=
  E.exact_g.toIsComplex.zero 0

/-- A degree `1` Yoneda extension is a short exact sequence `0 → A → Z₀ → B → 0`. -/
private lemma shortExact_zero (E : YonedaExtension B A 0) :
    (ShortComplex.mk E.f E.g (comp_g_eq_zero E)).ShortExact where
  exact := (ShortComplex.exact_iff_exact_toComposableArrows _).2 E.exact_g

/-- The map `coker(A ⟶ Z_n) ⟶ Z_{n - 1}` through which the map `Z_n ⟶ Z_{n - 1}` of a Yoneda
extension of degree at least `2` factors. -/
private noncomputable def cutMap {n : ℕ} (E : YonedaExtension B A (n + 1)) :
    cokernel E.f ⟶ E.Z.δ₀.left :=
  cokernel.desc E.f (E.Z.map' 0 1) (E.exact.toIsComplex.zero 0)

private lemma π_comp_cutMap {n : ℕ} (E : YonedaExtension B A (n + 1)) :
    cokernel.π E.f ≫ cutMap E = E.Z.map' 0 1 :=
  cokernel.π_desc _ _ _

private lemma mono_cutMap {n : ℕ} (E : YonedaExtension B A (n + 1)) : Mono (cutMap E) :=
  (E.exact.exact' 0 1 2).mono_cokernelDesc

set_option backward.isDefEq.respectTransparency false in
/-- The comparison map from the middle terms `Z_{n + 1} → ⋯ → Z_0` of a Yoneda extension `E` of
degree `n + 2` to the sequence `coker(A ⟶ Z_{n + 1}) → Z_n → ⋯ → Z_0` obtained by cutting `E`
at its left end: it is `Z_{n + 1} ↠ coker(A ⟶ Z_{n + 1})` in the first degree and the identity
in the others. -/
private noncomputable def cutHom {n : ℕ} (E : YonedaExtension B A (n + 1)) :
    E.Z ⟶ E.Z.δ₀.precomp (cutMap E) :=
  homMkSucc (cokernel.π E.f) (𝟙 E.Z.δ₀) ((Category.comp_id _).trans (π_comp_cutMap E).symm)

private lemma cutHom_app_zero {n : ℕ} (E : YonedaExtension B A (n + 1)) (h : 0 ≤ n + 1) :
    app' (cutHom E) 0 h = cokernel.π E.f := rfl

private lemma cutHom_app_succ {n : ℕ} (E : YonedaExtension B A (n + 1)) (i : ℕ)
    (hi : i + 1 ≤ n + 1) : app' (cutHom E) (i + 1) hi = 𝟙 _ := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma epi_cutHom_app {n : ℕ} (E : YonedaExtension B A (n + 1)) (i : ℕ) (hi : i ≤ n + 1) :
    Epi (app' (cutHom E) i hi) := by
  obtain _ | j := i
  · rw [cutHom_app_zero]; infer_instance
  · rw [cutHom_app_succ]; exact IsIso.epi_of_iso _

set_option backward.isDefEq.respectTransparency false in
private lemma isIso_cutHom_app {n : ℕ} (E : YonedaExtension B A (n + 1)) (i : ℕ) (_ : 1 ≤ i)
    (hi : i ≤ n + 1) : IsIso (app' (cutHom E) i hi) := by
  obtain _ | j := i
  · omega
  · rw [cutHom_app_succ]; exact IsIso.id _

private lemma cut_exact {n : ℕ} (E : YonedaExtension B A (n + 1)) :
    (E.Z.δ₀.precomp (cutMap E)).Exact :=
  exact_of_epi_of_isIso (cutHom E) E.exact.δ₀ (epi_cutHom_app E) (isIso_cutHom_app E)

set_option backward.isDefEq.respectTransparency false in
private lemma cut_exact_g {n : ℕ} (E : YonedaExtension B A (n + 1)) :
    (mk₂ ((E.Z.δ₀.precomp (cutMap E)).map' n (n + 1)) E.g).Exact := by
  have hnn : n ≤ n + 1 := by omega
  have hn := epi_cutHom_app E n hnn
  have hnat : app' (cutHom E) n hnn ≫ (E.Z.δ₀.precomp (cutMap E)).map' n (n + 1) =
      E.Z.map' n (n + 1) := by
    rw [← naturality' (cutHom E) n (n + 1) (by omega) (by omega), cutHom_app_succ E n (by omega),
      Category.comp_id]
  exact (exact₂_iff_of_epi_fac hnat E.g).1 E.exact_g

set_option backward.isDefEq.respectTransparency false in
/-- **Cutting a Yoneda extension at its left end.** A Yoneda extension
`E : 0 → A → Z_{n + 1} → Z_n → ⋯ → Z_0 → B → 0` of degree `n + 2` gives a Yoneda extension
`0 → coker(A ⟶ Z_{n + 1}) → Z_n → ⋯ → Z_0 → B → 0` of `B` by `coker(A ⟶ Z_{n + 1})` of degree
`n + 1`: the map from the cokernel is a monomorphism because `E` is exact at `Z_{n + 1}`, and
exactness of the shorter sequence follows from that of `E` because `Z_{n + 1}` maps onto the
cokernel. Together with the short exact sequence `shortExact_cut`, it recovers `E`. -/
private noncomputable def cut {n : ℕ} (E : YonedaExtension B A (n + 1)) :
    YonedaExtension B (cokernel E.f) n where
  Z := E.Z.δ₀
  f := cutMap E
  g := E.g
  mono_f := mono_cutMap E
  exact := cut_exact E
  exact_g := cut_exact_g E

private lemma cut_f {n : ℕ} (E : YonedaExtension B A (n + 1)) : (cut E).f = cutMap E := rfl

private lemma cut_g {n : ℕ} (E : YonedaExtension B A (n + 1)) : (cut E).g = E.g := rfl

set_option backward.isDefEq.respectTransparency false in
private lemma π_comp_cut_f {n : ℕ} (E : YonedaExtension B A (n + 1)) :
    cokernel.π E.f ≫ (cut E).f = E.Z.map' 0 1 :=
  π_comp_cutMap E

/-- The short exact sequence `0 → A → Z_{n + 1} → coker(A ⟶ Z_{n + 1}) → 0` at the left end of
a Yoneda extension of degree at least `2`. -/
private lemma shortExact_cut {n : ℕ} (E : YonedaExtension B A (n + 1)) :
    (ShortComplex.mk E.f (cokernel.π E.f) (cokernel.condition E.f)).ShortExact where
  exact := ShortComplex.exact_cokernel E.f

set_option backward.isDefEq.respectTransparency false in
/-- Every degree `n + 2` Yoneda extension `E` of `B` by `A` can be cut at its left end: the
cokernel `C` of `E.f` gives a short exact sequence `0 → A → Z_{n + 1} → C → 0`, and the
remaining terms of `E`, with the induced map from `C`, form a degree `n + 1` Yoneda extension
of `B` by `C`. -/
lemma exists_cut {n : ℕ} (E : YonedaExtension B A (n + 1)) :
    ∃ (C : 𝒜) (E' : YonedaExtension B C n) (p : E.Z.left ⟶ C) (h : E.f ≫ p = 0)
      (_hS : (ShortComplex.mk E.f p h).ShortExact) (φ : E.Z.δ₀ ≅ E'.Z),
      E.Z.map' 0 1 ≫ app' φ.hom 0 = p ≫ E'.f ∧ app' φ.hom n ≫ E'.g = E.g :=
  ⟨cokernel E.f, cut E, cokernel.π E.f, cokernel.condition E.f, shortExact_cut E, Iso.refl _,
    (Category.comp_id _).trans (π_comp_cutMap E).symm, Category.id_comp _⟩

/-- The map on cokernels induced by a morphism of Yoneda extensions of degree at least `2`. -/
private noncomputable def cokernelMap {n : ℕ} {A₁ A₂ : 𝒜} (E₁ : YonedaExtension B A₁ (n + 1))
    (E₂ : YonedaExtension B A₂ (n + 1)) (u : A₁ ⟶ A₂) (φ : E₁.Z ⟶ E₂.Z)
    (w : E₁.f ≫ app' φ 0 = u ≫ E₂.f) : cokernel E₁.f ⟶ cokernel E₂.f :=
  cokernel.map E₁.f E₂.f u (app' φ 0) w

private lemma π_comp_cokernelMap {n : ℕ} {A₁ A₂ : 𝒜} (E₁ : YonedaExtension B A₁ (n + 1))
    (E₂ : YonedaExtension B A₂ (n + 1)) (u : A₁ ⟶ A₂) (φ : E₁.Z ⟶ E₂.Z)
    (w : E₁.f ≫ app' φ 0 = u ≫ E₂.f) :
    cokernel.π E₁.f ≫ cokernelMap E₁ E₂ u φ w = app' φ 0 ≫ cokernel.π E₂.f :=
  cokernel.π_desc _ _ _

omit [Abelian 𝒜] in
private lemma app'_δ₀Functor_map {m : ℕ} {F G : ComposableArrows 𝒜 (m + 1)} (φ : F ⟶ G) (i : ℕ)
    (hi : i ≤ m) : app' (δ₀Functor.map φ) i hi = app' φ (i + 1) (by omega) := rfl

set_option backward.isDefEq.respectTransparency false in
/-- Cutting is functorial: a morphism of Yoneda extensions of degree `n + 2` over the identity
of `B`, inducing `u` on the extended object, induces a morphism of the cut extensions over the
identity of `B`, inducing `cokernelMap` on the extended object. -/
private lemma cut_f_comp {n : ℕ} {A₁ A₂ : 𝒜} (E₁ : YonedaExtension B A₁ (n + 1))
    (E₂ : YonedaExtension B A₂ (n + 1)) (u : A₁ ⟶ A₂) (φ : E₁.Z ⟶ E₂.Z)
    (w : E₁.f ≫ app' φ 0 = u ≫ E₂.f) :
    (cut E₁).f ≫ app' (δ₀Functor.map φ) 0 = cokernelMap E₁ E₂ u φ w ≫ (cut E₂).f := by
  rw [← cancel_epi (cokernel.π E₁.f), cut_f, cut_f, ← Category.assoc, ← Category.assoc,
    π_comp_cutMap, π_comp_cokernelMap, app'_δ₀Functor_map, Category.assoc, π_comp_cutMap,
    naturality' φ 0 1]

/-- Exactness of a two-term sequence at its middle object is unchanged by composing its second
map with a monomorphism. -/
private lemma exact₂_comp_mono {X Y Z W : 𝒜} {u : X ⟶ Y} {v : Y ⟶ Z} {w : Z ⟶ W} [Mono w]
    {h₁ : u ≫ v = 0} (h : (ShortComplex.mk u v h₁).Exact) : (mk₂ u (v ≫ w)).Exact := by
  have h₂ : u ≫ v ≫ w = 0 := by rw [← Category.assoc, h₁, zero_comp]
  exact exact₂_mk _ h₂ ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (S₁ := ShortComplex.mk u v h₁) (S₂ := ShortComplex.mk u (v ≫ w) h₂)
    ⟨𝟙 _, 𝟙 _, w, by simp, by simp⟩).1 h)

set_option backward.isDefEq.respectTransparency false in
/-- The degree `1` Yoneda extension that a short exact sequence `0 → X₁ → X₂ → X₃ → 0` is. -/
private def ofShortExact {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    YonedaExtension S.X₃ S.X₁ 0 where
  Z := mk₀ S.X₂
  f := S.f
  g := S.g
  mono_f := hS.mono_f
  exact := exact₁ _
  exact_g := hS.exact.exact_toComposableArrows
  epi_g := hS.epi_g

/-- **Pulling back a short exact sequence.** Given a short exact sequence
`0 → A → Z → C → 0` and a map `u : B ⟶ C`, the pullback `Z ×_C B` sits in a short exact
sequence `0 → A → Z ×_C B → B → 0` which maps to the given one by the identity on `A` and by
`u` on the right. -/
lemma exists_shortExact_pullback {Z C : 𝒜} {f : A ⟶ Z} {p : Z ⟶ C} {hz : f ≫ p = 0}
    (hS : (ShortComplex.mk f p hz).ShortExact) (u : B ⟶ C) :
    ∃ (W : 𝒜) (f' : A ⟶ W) (q : W ⟶ B) (hz' : f' ≫ q = 0)
      (_ : (ShortComplex.mk f' q hz').ShortExact) (v : W ⟶ Z),
      f' ≫ v = f ∧ q ≫ u = v ≫ p := by
  have := hS.mono_f
  have := hS.epi_g
  refine ⟨pullback p u, pullback.lift f 0 (by rw [hz, zero_comp]), pullback.snd p u,
    pullback.lift_snd _ _ _, { exact := ?_, mono_f := ?_, epi_g := ?_ }, pullback.fst p u,
    pullback.lift_fst _ _ _, pullback.condition.symm⟩
  · exact ShortComplex.exact_iff_exact_up_to_refinements _ |>.2 (fun T z hz' => by
      have hz₀ : z ≫ pullback.snd p u = 0 := hz'
      obtain ⟨T', π, hπ, a, ha⟩ := hS.exact.exact_up_to_refinements (z ≫ pullback.fst p u) (by
        dsimp
        rw [Category.assoc, pullback.condition, ← Category.assoc, hz₀, zero_comp])
      refine ⟨T', π, hπ, a, pullback.hom_ext ?_ ?_⟩
      · dsimp
        rw [Category.assoc, Category.assoc, pullback.lift_fst]
        exact ha
      · simp only [Category.assoc, pullback.lift_snd, comp_zero, hz₀])
  · exact mono_of_mono_fac (pullback.lift_fst (f := p) (g := u) f 0 (by rw [hz, zero_comp]))
  · dsimp
    infer_instance

/-- Splicing a short exact sequence `0 → A → Z → C → 0` onto a degree `n + 1` Yoneda extension
of `B` by `C` produces an exact sequence `Z → Z_n → ⋯ → Z_0`: exactness at `Z_n, …, Z_1` is
inherited from the extension, since `Z → C` is an epimorphism. -/
private lemma exact_precomp_comp_epi {n : ℕ} {C Z : 𝒜} (p : Z ⟶ C) [Epi p]
    (E' : YonedaExtension B C n) : (E'.Z.precomp (p ≫ E'.f)).Exact := by
  obtain _ | m := n
  · exact exact₁ _
  · exact exact_of_δ₀ ((exact₂_iff_of_epi_fac (u := p) (v := E'.f) rfl
      ((E'.Z.precomp E'.f).map' 1 2)).2
      ((ShortComplex.exact_iff_exact_toComposableArrows _).1 (E'.exact.exact' 0 1 2)))
      E'.exact.δ₀

set_option backward.isDefEq.respectTransparency false in
/-- **Splicing a short exact sequence onto a Yoneda extension**, the construction inverse to
`cut`: a short exact sequence `0 → A → Z → C → 0` and a degree `n + 1` Yoneda
extension `E' : 0 → C → Z_n → ⋯ → Z_0 → B → 0` of `B` by `C` splice to the degree `n + 2`
Yoneda extension `0 → A → Z → Z_n → ⋯ → Z_0 → B → 0` of `B` by `A`, whose map `Z ⟶ Z_n` is
`Z ↠ C ↪ Z_n`. It is exact at `Z` because `C ↪ Z_n` is a monomorphism, and at `Z_n, …, Z_1`
because `Z ↠ C` is an epimorphism. -/
private def splice {n : ℕ} {C Z : 𝒜} {f : A ⟶ Z} {p : Z ⟶ C} {hz : f ≫ p = 0}
    (hS : (ShortComplex.mk f p hz).ShortExact) (E' : YonedaExtension B C n) :
    YonedaExtension B A (n + 1) where
  Z := E'.Z.precomp (p ≫ E'.f)
  f := f
  g := E'.g
  mono_f := hS.mono_f
  exact := by
    have hepi : Epi p := hS.epi_g
    exact exact_of_δ₀ (exact₂_comp_mono (w := E'.f) hS.exact) (exact_precomp_comp_epi p E')
  exact_g := by
    have hepi : Epi p := hS.epi_g
    obtain _ | m := n
    · exact (exact₂_iff_of_epi_fac (u := p) (v := E'.f) rfl E'.g).2 E'.exact_g
    · exact E'.exact_g
  epi_g := E'.epi_g

/-- **The short five lemma for extensions.** A morphism of extensions of `B` by `A` which is
the identity on `A` and on `B` is an isomorphism; the unbundled form of
`CategoryTheory.ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'` for the two identities. -/
lemma isIso₂_of_shortExact_of_id₁₃ {E E' : 𝒜} {i : A ⟶ E} {p : E ⟶ B} {hw : i ≫ p = 0}
    {i' : A ⟶ E'} {p' : E' ⟶ B} {hw' : i' ≫ p' = 0}
    (h : (ShortComplex.mk i p hw).ShortExact) (h' : (ShortComplex.mk i' p' hw').ShortExact)
    (φ : E ⟶ E') (h₁ : i ≫ φ = i') (h₂ : φ ≫ p' = p) : IsIso φ :=
  ShortComplex.isIso₂_of_shortExact_of_isIso₁₃'
    (S₁ := ShortComplex.mk i p hw) (S₂ := ShortComplex.mk i' p' hw')
    { τ₁ := 𝟙 A, τ₂ := φ, τ₃ := 𝟙 B
      comm₁₂ := by simpa using h₁.symm
      comm₂₃ := by simpa using h₂ } h h' (IsIso.id _) (IsIso.id _)

end

/-! ### The class map of Yoneda extensions -/

section

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt.{w} 𝒜]

/-- The two properties which pin down the class map of Yoneda extensions: in degree `1` it is
the class `CategoryTheory.ShortComplex.ShortExact.extClass` of the short exact sequence the
extension is, and it is multiplicative for splicing at the left end. -/
def IsExtClassMap
    (δ : ∀ (B A : 𝒜) (n : ℕ), YonedaExtension B A n → Ext.{w} B A (n + 1)) : Prop :=
  (∀ (B A : 𝒜) (E : YonedaExtension B A 0) (h : E.f ≫ E.g = 0)
      (hS : (ShortComplex.mk E.f E.g h).ShortExact), δ B A 0 E = hS.extClass) ∧
    (∀ (B A C : 𝒜) (n : ℕ) (E : YonedaExtension B A (n + 1)) (E' : YonedaExtension B C n)
      (p : E.Z.left ⟶ C) (h : E.f ≫ p = 0)
      (hS : (ShortComplex.mk E.f p h).ShortExact) (φ : E.Z.δ₀ ≅ E'.Z),
      E.Z.map' 0 1 ≫ app' φ.hom 0 = p ≫ E'.f → app' φ.hom n ≫ E'.g = E.g →
        δ B A (n + 1) E = (δ B C n E').comp hS.extClass rfl)

/-- There is at most one class map: the degree `1` values are prescribed, and cutting an
extension at its left end computes the value in degree `n + 2` from a value in degree `n + 1`. -/
@[stacks 06XU "uniqueness of the class map"]
lemma eq_of_isExtClassMap
    (δ₁ δ₂ : ∀ (B A : 𝒜) (n : ℕ), YonedaExtension B A n → Ext.{w} B A (n + 1))
    (h₁ : IsExtClassMap δ₁) (h₂ : IsExtClassMap δ₂) : δ₁ = δ₂ := by
  funext B A n E
  induction n generalizing A with
  | zero =>
    rw [h₁.1 B A E (comp_g_eq_zero E) (shortExact_zero E),
      h₂.1 B A E (comp_g_eq_zero E) (shortExact_zero E)]
  | succ n ih =>
    obtain ⟨C, E', p, h, hS, φ, w₁, w₂⟩ := exists_cut E
    rw [h₁.2 B A C n E E' p h hS φ w₁ w₂, h₂.2 B A C n E E' p h hS φ w₁ w₂, ih C E']

/-- **The class of a Yoneda extension.** It is defined by recursion on the degree: in degree `1`
it is the class `CategoryTheory.ShortComplex.ShortExact.extClass` of the short exact sequence
the extension is, and in degree `n + 2` it is the class of the extension cut at its left end
(`cut`) composed with the class of the cutting short exact sequence
(`shortExact_cut`). It is the unique such map: `isExtClassMap_extClassMap` is the pair of
properties and `eq_of_isExtClassMap` their uniqueness. -/
@[stacks 06XU "the class map δ itself; `isExtClassMap_extClassMap` is its two defining \
properties and `eq_of_isExtClassMap` their uniqueness", no_expose, ega "0 12.3.2" "canonical map δ"]
noncomputable def extClassMap {B : 𝒜} :
    ∀ (n : ℕ) {A : 𝒜}, YonedaExtension B A n → Ext.{w} B A (n + 1)
  | 0, _, E => (shortExact_zero E).extClass
  | n + 1, _, E => (extClassMap n (cut E)).comp (shortExact_cut E).extClass rfl

private lemma extClassMap_zero {B A : 𝒜} (E : YonedaExtension B A 0) :
    extClassMap 0 E = (shortExact_zero E).extClass := rfl

private lemma extClassMap_succ {B A : 𝒜} {n : ℕ} (E : YonedaExtension B A (n + 1)) :
    extClassMap (n + 1) E = (extClassMap n (cut E)).comp (shortExact_cut E).extClass rfl := rfl

private lemma extClassMap_ofShortExact {S : ShortComplex 𝒜} (hS : S.ShortExact) :
    extClassMap.{w} 0 (ofShortExact hS) = hS.extClass := rfl

/-- **The class map is natural.** A morphism of Yoneda extensions of the same degree over the
identity of `B`, inducing `u : A₁ ⟶ A₂` on the extended object, carries the class of its source
to the class of its target: `δ(E₁) ∘ u = δ(E₂)`. In particular equivalent Yoneda extensions have
the same class. -/
lemma extClassMap_comp_mk₀ {B : 𝒜} : ∀ (n : ℕ) {A₁ A₂ : 𝒜} (E₁ : YonedaExtension B A₁ n)
    (E₂ : YonedaExtension B A₂ n) (u : A₁ ⟶ A₂) (φ : E₁.Z ⟶ E₂.Z),
      E₁.f ≫ app' φ 0 = u ≫ E₂.f → app' φ n ≫ E₂.g = E₁.g →
        (extClassMap n E₁).comp (Ext.mk₀ u) (add_zero _) = extClassMap n E₂ := by
  intro n
  induction n with
  | zero =>
    intro A₁ A₂ E₁ E₂ u φ w₁ w₂
    have h := ShortComplex.ShortExact.extClass_naturality (shortExact_zero E₁)
      (shortExact_zero E₂)
      { τ₁ := u, τ₂ := app' φ 0, τ₃ := 𝟙 B, comm₁₂ := w₁.symm,
        comm₂₃ := by rw [Category.comp_id]; exact w₂ }
    rw [extClassMap_zero, extClassMap_zero]
    exact h.trans (Ext.mk₀_id_comp _)
  | succ n ih =>
    intro A₁ A₂ E₁ E₂ u φ w₁ w₂
    have hnat := ShortComplex.ShortExact.extClass_naturality (shortExact_cut E₁)
      (shortExact_cut E₂)
      { τ₁ := u, τ₂ := app' φ 0, τ₃ := cokernelMap E₁ E₂ u φ w₁, comm₁₂ := w₁.symm,
        comm₂₃ := (π_comp_cokernelMap E₁ E₂ u φ w₁).symm }
    rw [extClassMap_succ, extClassMap_succ, Ext.comp_assoc_of_third_deg_zero, hnat,
      ← Ext.comp_assoc_of_second_deg_zero,
      ih (cut E₁) (cut E₂) (cokernelMap E₁ E₂ u φ w₁) (δ₀Functor.map φ)
        (cut_f_comp E₁ E₂ u φ w₁) (by rw [cut_g, cut_g, app'_δ₀Functor_map]; exact w₂)]

/-- Equivalent Yoneda extensions have the same class. -/
@[stacks 06XU "equivalent Yoneda extensions have the same class",
  ega "0 12.3.2" "E~E' ⇒ δE=δE'",
  sga "7 VII 3.2" "c(X, special case"]
lemma extClassMap_eq_of_equivalent {B A : 𝒜} {n : ℕ} {E E' : YonedaExtension B A n}
    (h : E.Equivalent E') : extClassMap n E = extClassMap n E' := by
  obtain ⟨E'', φ, ψ, hφ₁, hφ₂, hψ₁, hψ₂⟩ := h
  have h₁ := extClassMap_comp_mk₀ n E'' E (𝟙 A) φ (by rw [Category.id_comp]; exact hφ₁) hφ₂
  have h₂ := extClassMap_comp_mk₀ n E'' E' (𝟙 A) ψ (by rw [Category.id_comp]; exact hψ₁) hψ₂
  rw [Ext.comp_mk₀_id] at h₁ h₂
  rw [← h₁, ← h₂]

/-- **The class map is multiplicative for splicing at the left end**, for an arbitrary cut, not
only for the canonical one by the cokernel: any short exact sequence `0 → A → Z_{n + 1} → C → 0`
at the left end of `E`, followed by a degree `n + 1` extension `E'` of `B` by `C`, computes the
class of `E` as `δ(E') ∘ [0 → A → Z_{n + 1} → C → 0]`. -/
lemma extClassMap_succ_of_cut {B A C : 𝒜} {n : ℕ} (E : YonedaExtension B A (n + 1))
    (E' : YonedaExtension B C n) (p : E.Z.left ⟶ C) (h : E.f ≫ p = 0)
    (hS : (ShortComplex.mk E.f p h).ShortExact) (φ : E.Z.δ₀ ≅ E'.Z)
    (w₁ : E.Z.map' 0 1 ≫ app' φ.hom 0 = p ≫ E'.f) (w₂ : app' φ.hom n ≫ E'.g = E.g) :
    extClassMap (n + 1) E = (extClassMap n E').comp hS.extClass rfl := by
  have hπu : cokernel.π E.f ≫ cokernel.desc E.f p h = p := cokernel.π_desc _ _ _
  have hIH : (extClassMap n (cut E)).comp (Ext.mk₀ (cokernel.desc E.f p h)) (add_zero _) =
      extClassMap n E' := by
    refine extClassMap_comp_mk₀ n (cut E) E' (cokernel.desc E.f p h) φ.hom ?_ ?_
    · rw [← cancel_epi (cokernel.π E.f), ← Category.assoc, ← Category.assoc, π_comp_cut_f, hπu]
      exact w₁
    · rw [cut_g]; exact w₂
  have he : (shortExact_cut E).extClass =
      (Ext.mk₀ (cokernel.desc E.f p h)).comp hS.extClass (zero_add 1) := by
    rw [← ShortComplex.ShortExact.extClass_naturality (shortExact_cut E) hS
      { τ₁ := 𝟙 A, τ₂ := 𝟙 E.Z.left, τ₃ := cokernel.desc E.f p h,
        comm₁₂ := by rw [Category.id_comp, Category.comp_id],
        comm₂₃ := by rw [Category.id_comp]; exact hπu.symm }, Ext.comp_mk₀_id]
  rw [extClassMap_succ, he, ← Ext.comp_assoc_of_second_deg_zero, hIH]

/-- The class map has the two properties which pin it down. -/
@[stacks 06XU "the two defining properties of the class map"]
lemma isExtClassMap_extClassMap :
    IsExtClassMap (fun (_ _ : 𝒜) (n : ℕ) (E : YonedaExtension _ _ n) => extClassMap.{w} n E) :=
  ⟨fun _ _ _ _ _ => rfl,
    fun _ _ _ _n E E' p h hS φ w₁ w₂ => extClassMap_succ_of_cut E E' p h hS φ w₁ w₂⟩

/-- Any map with the two characterising properties is the class map. -/
lemma eq_extClassMap_of_isExtClassMap
    (δ : ∀ (B A : 𝒜) (n : ℕ), YonedaExtension B A n → Ext.{w} B A (n + 1))
    (hδ : IsExtClassMap δ) :
    δ = fun (_ _ : 𝒜) (n : ℕ) (E : YonedaExtension _ _ n) => extClassMap.{w} n E :=
  eq_of_isExtClassMap δ _ hδ isExtClassMap_extClassMap

set_option backward.isDefEq.respectTransparency false in
/-- **The class of a spliced extension.** Splicing a short exact sequence
`0 → A → Z → C → 0` onto a degree `n + 1` Yoneda extension `E'` of `B` by `C`
(`splice`) multiplies the classes: the canonical cut of the spliced extension is
the given short exact sequence followed by `E'`. -/
private lemma extClassMap_splice {B A C Z : 𝒜} {n : ℕ} {f : A ⟶ Z} {p : Z ⟶ C}
    {hz : f ≫ p = 0} (hS : (ShortComplex.mk f p hz).ShortExact)
    (E' : YonedaExtension B C n) :
    extClassMap.{w} (n + 1) (splice hS E') = (extClassMap.{w} n E').comp hS.extClass rfl :=
  extClassMap_succ_of_cut (splice hS E') E' p hz hS (Iso.refl _) (Category.comp_id _)
    (Category.id_comp _)

/-- **Every class of positive degree is killed by pushing it forward along a monomorphism**:
for `ξ ∈ Ext^{n + 1}_𝒜(B, A)` there is a short exact sequence `0 → A → Z → C → 0` with
`ξ ∘ (A ⟶ Z) = 0` in `Ext^{n + 1}_𝒜(B, Z)`.

This is the source's construction, in the derived category: writing `ξ = f s⁻¹` for a
quasi-isomorphism `s : L^• → B[0]` and a map `f : L^• → A[n + 1]` with `L^j = 0` for `j > 0`, the
map
`f^{- n - 1} : L^{- n - 1} → A` kills the cycles of `L^•` in degree `- n - 1` (they are
boundaries, since `H^{- n - 1}(L^•) = 0` for `n + 1 ≥ 1`), so that `A` maps monomorphically to
the pushout `Z = (L^{-n} ⊕ A)/L^{- n - 1}` of `L^{- n - 1} → L^{-n}` along `f^{- n - 1}`; and
the composite `L^• → A[n + 1] → Z[n + 1]` is null-homotopic, the homotopy being the map
`L^{-n} → Z`, so `ξ ∘ (A ⟶ Z)` vanishes already in the homotopy category.

From this, surjectivity of the class map (`surjective_extClassMap`) follows from
the covariant long exact sequence of `Ext` groups, the splicing construction
`splice` and, in degree `1`, pulling the short exact sequence back
(`exists_shortExact_pullback`). -/
lemma exists_shortExact_comp_mk₀_eq_zero (B A : 𝒜) (n : ℕ) (ξ : Ext.{w} B A (n + 1)) :
    ∃ (Z C : 𝒜) (f : A ⟶ Z) (p : Z ⟶ C) (hz : f ≫ p = 0)
      (_ : (ShortComplex.mk f p hz).ShortExact),
      ξ.comp (Ext.mk₀ f) (add_zero (n + 1)) = 0 := by
  let := HasDerivedCategory.standard 𝒜
  set m : ℤ := -((n + 1 : ℕ) : ℤ)
  have hB : ((CochainComplex.singleFunctor 𝒜 0).obj B).IsStrictlyGE m :=
    CochainComplex.isStrictlyGE_of_ge _ m 0 (by omega)
  let e := (DerivedCategory.singleFunctors 𝒜).shiftIso ((n + 1 : ℕ) : ℤ) m 0 (by omega)
  obtain ⟨L, hL₁, hL₂, s, hs, g, hfac⟩ :=
    DerivedCategory.right_fac_of_isStrictlyLE_of_isStrictlyGE
      (X := (CochainComplex.singleFunctor 𝒜 0).obj B)
      (Y := (CochainComplex.singleFunctor 𝒜 m).obj A) m 0 (ξ.hom ≫ e.hom.app A)
  have hq : QuasiIso s := (DerivedCategory.isIso_Q_map_iff_quasiIso 𝒜 s).1 hs
  have hmono : Mono (L.d m (m + 1)) :=
    mono_d_of_exactAt (L.isZero_of_isStrictlyGE m (m - 1) (by omega))
      ((exactAt_iff_of_quasiIsoAt s m).2 (HomologicalComplex.ExactAt.of_isZero
        (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 B m (by omega))))
  obtain ⟨Z, ι, hι, ⟨H⟩⟩ := exists_mono_nonempty_homotopy g
  refine ⟨Z, cokernel ι, ι, cokernel.π ι, cokernel.condition ι,
    { exact := ShortComplex.exact_cokernel ι }, ?_⟩
  have hnat : (shiftFunctor (DerivedCategory 𝒜) ((n + 1 : ℕ) : ℤ)).map
        ((DerivedCategory.singleFunctor 𝒜 0).map ι) ≫ e.hom.app Z =
      e.hom.app A ≫ (DerivedCategory.singleFunctor 𝒜 m).map ι := e.hom.naturality ι
  apply Ext.ext
  rw [Ext.comp_hom, Ext.mk₀_hom, Ext.zero_hom, ShiftedHom.comp_mk₀,
    ← cancel_mono (e.hom.app Z), zero_comp, Category.assoc, hnat, ← Category.assoc, hfac,
    show (DerivedCategory.singleFunctor 𝒜 m).map ι =
      DerivedCategory.Q.map ((HomologicalComplex.single 𝒜 (ComplexShape.up ℤ) m).map ι) from rfl,
    Category.assoc, ← Functor.map_comp, Q_map_eq_zero_of_homotopy H, comp_zero]

/-- **The class map is surjective**: every element of `Ext^{n + 1}_𝒜(B, A)` is the class of a
degree `n + 1` Yoneda extension of `B` by `A`. The induction is on the degree: an element `ξ`
of `Ext^{n + 1}_𝒜(B, A)` is killed by a monomorphism `A ⟶ Z`
(`exists_shortExact_comp_mk₀_eq_zero`), hence, by the covariant long exact
sequence of the short exact sequence `S : 0 → A → Z → C → 0`, of the form
`ξ = η ∘ δ(S)` with `η ∈ Ext^n_𝒜(B, C)`. For `n ≥ 1` the inductive hypothesis writes
`η = δ(E')` for a degree `n` extension `E'` of `B` by `C`, and `E'` spliced with `S` is an
extension of class `ξ` (`extClassMap_splice`). For `n = 0`, `η` is a map
`u : B ⟶ C` and the pullback of `S` along `u` is a short exact sequence
`0 → A → Z ×_C B → B → 0` of class `ξ`, by naturality of
`CategoryTheory.ShortComplex.ShortExact.extClass`. -/
@[stacks 06XU "every element of `Ext^{n + 1}` is the class of a degree `n + 1` Yoneda \
extension", ega "0 12.3.2" "surjectivity of δ", sga "7 VII 3.2.5" "partial"]
lemma surjective_extClassMap (B A : 𝒜) (n : ℕ) :
    Function.Surjective (fun E : YonedaExtension B A n => extClassMap.{w} n E) := by
  induction n generalizing A with
  | zero =>
    intro ξ
    obtain ⟨Z, C, f, p, hz, hS, hξ⟩ := exists_shortExact_comp_mk₀_eq_zero B A 0 ξ
    obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ B hS ξ hξ (zero_add 1)
    obtain ⟨u, hu⟩ := (Ext.mk₀_bijective _ _).2 x₃
    obtain ⟨W, f', q, hz', hS', v, hv₁, hv₂⟩ := exists_shortExact_pullback hS u
    refine ⟨ofShortExact hS', ?_⟩
    have hnat := ShortComplex.ShortExact.extClass_naturality hS' hS
      { τ₁ := 𝟙 A, τ₂ := v, τ₃ := u, comm₁₂ := by simpa using hv₁.symm, comm₂₃ := hv₂.symm }
    dsimp only
    rw [extClassMap_ofShortExact, ← Ext.comp_mk₀_id hS'.extClass, hnat, hu]
    exact hx₃
  | succ n ih =>
    intro ξ
    obtain ⟨Z, C, f, p, hz, hS, hξ⟩ := exists_shortExact_comp_mk₀_eq_zero B A (n + 1) ξ
    obtain ⟨x₃, hx₃⟩ := Ext.covariant_sequence_exact₁ B hS ξ hξ rfl
    obtain ⟨E', hE'⟩ := ih C x₃
    refine ⟨splice hS E', ?_⟩
    dsimp only at hE' ⊢
    rw [extClassMap_splice, hE']
    exact hx₃

/-- Yoneda composition is compatible with subtraction in its second variable: the missing
sibling of `CategoryTheory.Abelian.Ext.comp_add`, which is precomposition being additive. -/
private lemma comp_sub {X Y Z : 𝒜} {a b c : ℕ} (α : Ext.{w} X Y a) (β γ : Ext.{w} Y Z b)
    (h : a + b = c) : α.comp (β - γ) h = α.comp β h - α.comp γ h :=
  map_sub (α.precomp Z h) β γ

/-- Yoneda composition with two morphisms is composition with their composite. -/
private lemma comp_mk₀_comp_mk₀ {X Y Z T : 𝒜} {k : ℕ} (α : Ext.{w} X Y k) (f : Y ⟶ Z)
    (g : Z ⟶ T) :
    (α.comp (Ext.mk₀ f) (add_zero k)).comp (Ext.mk₀ g) (add_zero k) =
      α.comp (Ext.mk₀ (f ≫ g)) (add_zero k) := by
  rw [Ext.comp_assoc_of_second_deg_zero, Ext.mk₀_comp_mk₀]

/-- Yoneda composition is compatible with subtraction in its first variable: the missing
sibling of `CategoryTheory.Abelian.Ext.add_comp`, which is postcomposition being additive. -/
private lemma sub_comp {X Y Z : 𝒜} {a b c : ℕ} (α β : Ext.{w} X Y a) (γ : Ext.{w} Y Z b)
    (h : a + b = c) : (α - β).comp γ h = α.comp γ h - β.comp γ h :=
  map_sub (γ.postcomp X h) α β

/-- A class with values in a binary biproduct vanishes as soon as both of its components do. -/
private lemma eq_zero_of_comp_mk₀_biprod {X Y₁ Y₂ : 𝒜} {k : ℕ} (α : Ext.{w} X (Y₁ ⊞ Y₂) k)
    (h₁ : α.comp (Ext.mk₀ (biprod.fst : Y₁ ⊞ Y₂ ⟶ Y₁)) (add_zero k) = 0)
    (h₂ : α.comp (Ext.mk₀ (biprod.snd : Y₁ ⊞ Y₂ ⟶ Y₂)) (add_zero k) = 0) : α = 0 := by
  have h := Ext.comp_mk₀_id α
  rw [← biprod.total, Ext.mk₀_add, Ext.comp_add, ← Ext.mk₀_comp_mk₀, ← Ext.mk₀_comp_mk₀,
    ← Ext.comp_assoc_of_second_deg_zero, ← Ext.comp_assoc_of_second_deg_zero, h₁, h₂,
    Ext.zero_comp, Ext.zero_comp, add_zero] at h
  exact h.symm

/-- **A short exact sequence through which two maps out of `A` factor and which kills a class of
positive degree.** Given `a₁ : A ⟶ Z₁`, `a₂ : A ⟶ Z₂` and `ξ ∈ Ext^{n + 1}_𝒜(B, A)` with
`ξ ∘ a₁ = 0` and `ξ ∘ a₂ = 0`, there is a short exact sequence `0 → A → W → D → 0` with maps
`p₁ : W ⟶ Z₁`, `p₂ : W ⟶ Z₂` restricting to `a₁` and `a₂` on `A`, such that `ξ ∘ (A ⟶ W) = 0`
and such that every pair of classes in `Ext^{n + 1}_𝒜(B, Z₁)` and `Ext^{n + 1}_𝒜(B, Z₂)` is the
pair of images of a class in `Ext^{n + 1}_𝒜(B, W)`. Take `W = Z₁ ⊞ Z₂ ⊞ M` with `A ⟶ M` a
monomorphism killing `ξ` (`exists_shortExact_comp_mk₀_eq_zero`): the third
component makes `A ⟶ W` a monomorphism, and the first two make it factor as required. -/
private lemma exists_shortExact_fac {B A : 𝒜} (n : ℕ) (ξ : Ext.{w} B A (n + 1))
    {Z₁ Z₂ : 𝒜} (a₁ : A ⟶ Z₁) (a₂ : A ⟶ Z₂)
    (h₁ : ξ.comp (Ext.mk₀ a₁) (add_zero (n + 1)) = 0)
    (h₂ : ξ.comp (Ext.mk₀ a₂) (add_zero (n + 1)) = 0) :
    ∃ (W D : 𝒜) (ι : A ⟶ W) (π : W ⟶ D) (hz : ι ≫ π = 0)
      (_ : (ShortComplex.mk ι π hz).ShortExact) (p₁ : W ⟶ Z₁) (p₂ : W ⟶ Z₂),
      ι ≫ p₁ = a₁ ∧ ι ≫ p₂ = a₂ ∧ ξ.comp (Ext.mk₀ ι) (add_zero (n + 1)) = 0 ∧
        ∀ (k : ℕ) (w₁ : Ext.{w} B Z₁ k) (w₂ : Ext.{w} B Z₂ k),
          ∃ η : Ext.{w} B W k, η.comp (Ext.mk₀ p₁) (add_zero k) = w₁ ∧
            η.comp (Ext.mk₀ p₂) (add_zero k) = w₂ := by
  obtain ⟨M, N, m, pm, hzm, hSm, hξm⟩ := exists_shortExact_comp_mk₀_eq_zero B A n ξ
  have hmono : Mono m := hSm.mono_f
  have hfac : biprod.lift a₁ (biprod.lift a₂ m) ≫ (biprod.snd ≫ biprod.snd) = m := by simp
  have : Mono (biprod.lift a₁ (biprod.lift a₂ m)) := mono_of_mono_fac hfac
  refine ⟨Z₁ ⊞ (Z₂ ⊞ M), cokernel (biprod.lift a₁ (biprod.lift a₂ m)),
    biprod.lift a₁ (biprod.lift a₂ m), cokernel.π _, cokernel.condition _,
    { exact := ShortComplex.exact_cokernel _ }, biprod.fst, biprod.snd ≫ biprod.fst,
    by simp, by simp, ?_, fun k w₁ w₂ => ⟨w₁.comp (Ext.mk₀ biprod.inl) (add_zero k) +
      w₂.comp (Ext.mk₀ (biprod.inl ≫ biprod.inr)) (add_zero k), ?_, ?_⟩⟩
  · refine eq_zero_of_comp_mk₀_biprod _ ?_ (eq_zero_of_comp_mk₀_biprod _ ?_ ?_)
    exacts [by simpa [comp_mk₀_comp_mk₀] using h₁, by simpa [comp_mk₀_comp_mk₀] using h₂,
      by simpa [comp_mk₀_comp_mk₀] using hξm]
  all_goals simp [Ext.add_comp]

set_option backward.isDefEq.respectTransparency false in
omit [HasExt.{w} 𝒜] in
/-- **A morphism out of a spliced extension.** Let `0 → A → W → D → 0` be a short exact
sequence, let `G` be a degree `n + 1` Yoneda extension of `B` by `D` and let `E` be a degree
`n + 2` Yoneda extension of `B` by `A'`. A map `p : W ⟶ Z_{n + 1}` restricting to `u : A ⟶ A'`
on `A`, compatible with a map `v : D ⟶ coker(A' ⟶ Z_{n + 1})`, and a morphism from `G` to the
cut of `E` over `v`, assemble into a morphism from the splice of `0 → A → W → D → 0` with `G`
to `E` over `u`. -/
private lemma exists_hom_splice {B A A' D W : 𝒜} {n : ℕ} {ι : A ⟶ W} {π : W ⟶ D}
    {hz : ι ≫ π = 0} (hT : (ShortComplex.mk ι π hz).ShortExact) (G : YonedaExtension B D n)
    (E : YonedaExtension B A' (n + 1)) (u : A ⟶ A') (p : W ⟶ E.Z.left) (v : D ⟶ cokernel E.f)
    (hup : ι ≫ p = u ≫ E.f) (hπv : π ≫ v = p ≫ cokernel.π E.f)
    (φ : G.Z ⟶ (cut E).Z) (hφ₁ : G.f ≫ app' φ 0 = v ≫ (cut E).f)
    (hφ₂ : app' φ n ≫ (cut E).g = G.g) :
    ∃ Φ : (splice hT G).Z ⟶ E.Z, (splice hT G).f ≫ app' Φ 0 = u ≫ E.f ∧
      app' Φ (n + 1) ≫ E.g = (splice hT G).g := by
  refine ⟨homMkSucc p φ ?_, ?_, ?_⟩
  · change (π ≫ G.f) ≫ app' φ 0 = p ≫ E.Z.map' 0 1
    rw [Category.assoc, hφ₁, cut_f, ← Category.assoc, hπv, Category.assoc, π_comp_cutMap]
  · change ι ≫ p = u ≫ E.f
    exact hup
  · change app' φ n ≫ E.g = G.g
    exact hφ₂

/-- **A morphism of degree `1` Yoneda extensions out of a relation between their classes.** If
`E` is a short exact sequence `0 → A → Z₀ → B → 0`, `E'` one `0 → A' → Z'₀ → B → 0` and
`u : A ⟶ A'` satisfies `δ(E) ∘ u = δ(E')`, then there is a morphism `Z₀ ⟶ Z'₀` from `E` to `E'`
over `u` and over the identity of `B`.

The map `E.g : Z₀ ⟶ B` is killed by the class of the second sequence
(`CategoryTheory.ShortComplex.ShortExact.comp_extClass`), so the covariant long exact sequence
of the second sequence lifts it to a map `q : Z₀ ⟶ Z'₀` with `q ≫ E'.g = E.g`
(`CategoryTheory.Abelian.Ext.covariant_sequence_exact₃`). The map `u' : A ⟶ A'` induced by `q`
on the extended object satisfies `δ(E) ∘ (u' - u) = 0` by naturality of the class, hence
`u' - u = E.f ≫ k` for some `k : Z₀ ⟶ A'` by the contravariant long exact sequence of the first
sequence (`CategoryTheory.Abelian.Ext.contravariant_sequence_exact₁`), and `q - k ≫ E'.f` is
the required morphism. -/
@[ega "0 12.3.2" "partial"]
private lemma exists_hom_of_extClassMap_comp_mk₀_eq {B A A' : 𝒜} (E : YonedaExtension B A 0)
    (E' : YonedaExtension B A' 0) (u : A ⟶ A')
    (h : (extClassMap.{w} 0 E).comp (Ext.mk₀ u) (add_zero 1) = extClassMap.{w} 0 E') :
    ∃ q : E.Z.left ⟶ E'.Z.left, E.f ≫ q = u ≫ E'.f ∧ q ≫ E'.g = E.g := by
  rw [extClassMap_zero, extClassMap_zero] at h
  have h1 : (Ext.mk₀ E.g).comp (shortExact_zero E').extClass (zero_add 1) = 0 := by
    rw [← h, ← Ext.comp_assoc_of_third_deg_zero, (shortExact_zero E).comp_extClass,
      Ext.zero_comp]
  obtain ⟨x₂, hx₂⟩ :=
    Ext.covariant_sequence_exact₃ _ (shortExact_zero E') _ (zero_add 1) h1
  obtain ⟨q, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
  rw [Ext.mk₀_comp_mk₀] at hx₂
  have hqg : q ≫ E'.g = E.g := (Ext.mk₀_bijective _ _).1 hx₂
  have hz : (E.f ≫ q) ≫ E'.g = 0 := by rw [Category.assoc, hqg]; exact comp_g_eq_zero E
  obtain ⟨u', hu'⟩ : ∃ u' : A ⟶ A', u' ≫ E'.f = E.f ≫ q :=
    ⟨(shortExact_zero E').exact.lift (E.f ≫ q) hz,
      (shortExact_zero E').exact.lift_f (E.f ≫ q) hz⟩
  have hnat := ShortComplex.ShortExact.extClass_naturality (shortExact_zero E)
    (shortExact_zero E')
    { τ₁ := u', τ₂ := q, τ₃ := 𝟙 B, comm₁₂ := hu', comm₂₃ := by simpa using hqg }
  have key : (shortExact_zero E).extClass.comp (Ext.mk₀ u' - Ext.mk₀ u) (add_zero 1) = 0 := by
    rw [comp_sub, hnat, Ext.mk₀_id_comp, h, sub_self]
  obtain ⟨y, hy⟩ :=
    Ext.contravariant_sequence_exact₁ (shortExact_zero E) A' _ (add_zero 1) key
  obtain ⟨k, rfl⟩ := (Ext.mk₀_bijective _ _).2 y
  rw [Ext.mk₀_comp_mk₀, sub_eq_add_neg, ← Ext.mk₀_neg, ← Ext.mk₀_add, ← sub_eq_add_neg] at hy
  have hfk : E.f ≫ k = u' - u := (Ext.mk₀_bijective _ _).1 hy
  refine ⟨q - k ≫ E'.f, ?_, ?_⟩
  · rw [Preadditive.comp_sub, ← Category.assoc, hfk, Preadditive.sub_comp, hu', sub_sub_cancel]
  · rw [Preadditive.sub_comp, Category.assoc, comp_g_eq_zero E', comp_zero, sub_zero, hqg]

/-- **A class whose pushforward is the class of an extension kills that extension's own
monomorphism.** If `ξ ∘ u = δ(E)` for a degree `n + 2` extension `E` of `B` by `A'` and
`u : A ⟶ A'`, then `ξ ∘ (u ≫ E.f) = 0`, because `δ(E)` ends with the class of the short exact
sequence `0 → A' → Z_{n + 1} → coker(A' ⟶ Z_{n + 1}) → 0`, which kills its own monomorphism
`E.f`. -/
private lemma comp_mk₀_comp_f_eq_zero {B A A' : 𝒜} {n : ℕ} (E : YonedaExtension B A' (n + 1))
    (u : A ⟶ A') (ξ : Ext.{w} B A (n + 1 + 1))
    (h : ξ.comp (Ext.mk₀ u) (add_zero (n + 1 + 1)) = extClassMap.{w} (n + 1) E) :
    ξ.comp (Ext.mk₀ (u ≫ E.f)) (add_zero (n + 1 + 1)) = 0 := by
  rw [← Ext.mk₀_comp_mk₀, ← Ext.comp_assoc_of_second_deg_zero, h, extClassMap_succ,
    Ext.comp_assoc_of_third_deg_zero, (shortExact_cut E).extClass_comp, Ext.comp_zero]

/-- **Correcting a class by one that absorbs an error term.** Given a commuting square
`π ≫ v = p ≫ κ`, a class `wv` whose image along `κ` is the error term `ξ₀ ∘ v - δ`, and a class
`η` whose image along `p` is `wv`, the corrected class `ξ₀ - η ∘ π` has image exactly `δ`
along `v`. -/
private lemma sub_comp_mk₀_eq_of_comp_mk₀_eq_sub {B D W X Y : 𝒜} {k : ℕ} {π : W ⟶ D} {p : W ⟶ X}
    {v : D ⟶ Y} {κ : X ⟶ Y} (hsq : π ≫ v = p ≫ κ) {ξ₀ : Ext.{w} B D k} {δ : Ext.{w} B Y k}
    {wv : Ext.{w} B X k} {η : Ext.{w} B W k}
    (hwv : wv.comp (Ext.mk₀ κ) (add_zero k) = ξ₀.comp (Ext.mk₀ v) (add_zero k) - δ)
    (hη : η.comp (Ext.mk₀ p) (add_zero k) = wv) :
    (ξ₀ - η.comp (Ext.mk₀ π) (add_zero k)).comp (Ext.mk₀ v) (add_zero k) = δ := by
  rw [sub_comp, comp_mk₀_comp_mk₀, hsq, ← comp_mk₀_comp_mk₀, hη, hwv, sub_sub_cancel]

/-- **The comparison map on cokernels, and the error term of a factorisation through a short
exact sequence.** Let
`T : 0 → A → W → D → 0` be a short exact sequence, let `E` be a degree `n + 2` extension of `B`
by `A'`, and let `p : W ⟶ Z_{n + 1}` restrict to `u : A ⟶ A'` on `A`. Then `p` induces a map
`v : D ⟶ coker(A' ⟶ Z_{n + 1})` making `T` map to the short exact sequence
`shortExact_cut` of `E`, and if `ξ = ξ₀ ∘ [T]` pushes forward along `u` to `δ(E)`,
then `ξ₀ ∘ v` and the class of the cut of `E` differ by a class coming from `Z_{n + 1}`: their
difference is killed by `[shortExact_cut E]`, by the naturality of the class of a short exact
sequence, hence lifts along `Z_{n + 1} ↠ coker(A' ⟶ Z_{n + 1})` by the covariant long exact
sequence. -/
private lemma exists_comp_mk₀_π_eq_sub {B A A' D W : 𝒜} {n : ℕ} {ι : A ⟶ W} {π : W ⟶ D}
    {hzι : ι ≫ π = 0} (hT : (ShortComplex.mk ι π hzι).ShortExact)
    (E : YonedaExtension B A' (n + 1)) {u : A ⟶ A'} {p : W ⟶ E.Z.left}
    (hup : ι ≫ p = u ≫ E.f) {ξ : Ext.{w} B A (n + 1 + 1)} {ξ₀ : Ext.{w} B D (n + 1)}
    (hξ₀ : ξ₀.comp hT.extClass rfl = ξ)
    (h : ξ.comp (Ext.mk₀ u) (add_zero (n + 1 + 1)) = extClassMap.{w} (n + 1) E) :
    ∃ (v : D ⟶ cokernel E.f) (_ : π ≫ v = p ≫ cokernel.π E.f)
      (wv : Ext.{w} B E.Z.left (n + 1)),
      wv.comp (Ext.mk₀ (cokernel.π E.f)) (add_zero (n + 1)) =
        ξ₀.comp (Ext.mk₀ v) (add_zero (n + 1)) - extClassMap.{w} n (cut E) := by
  have hepi : Epi π := hT.epi_g
  have hzv : ι ≫ (p ≫ cokernel.π E.f) = 0 := by
    rw [← Category.assoc, hup, Category.assoc, cokernel.condition, comp_zero]
  refine ⟨hT.exact.desc _ hzv, hT.exact.g_desc _ _, ?_⟩
  have hnat := ShortComplex.ShortExact.extClass_naturality hT (shortExact_cut E)
    { τ₁ := u, τ₂ := p, τ₃ := hT.exact.desc _ hzv, comm₁₂ := hup.symm,
      comm₂₃ := (hT.exact.g_desc _ _).symm }
  exact Ext.covariant_sequence_exact₃ B (shortExact_cut E) _ rfl (by
    rw [sub_comp, Ext.comp_assoc_of_second_deg_zero, ← hnat,
      ← Ext.comp_assoc_of_third_deg_zero, hξ₀, h, extClassMap_succ, sub_self])

set_option backward.isDefEq.respectTransparency false in
/-- **Two Yoneda extensions whose classes come from a common class are refined by a common
extension.** Let `E₁`, `E₂` be degree `n + 1` Yoneda extensions of `B` by `A₁`, `A₂`, let
`u_i : A ⟶ A_i` and let `ξ ∈ Ext^{n + 1}_𝒜(B, A)` satisfy `ξ ∘ u_i = δ(E_i)`. Then there is a
degree `n + 1` Yoneda extension `G` of `B` by `A` together with morphisms `G → E₁` over `u₁`
and `G → E₂` over `u₂`, both over the identity of `B`.

For `n = 0` the extension `G` is any one of class `ξ` (`surjective_extClassMap`)
and the two morphisms come from `exists_hom_of_extClassMap_comp_mk₀_eq`. For
`n + 1` the two extensions are cut at their left ends into short exact sequences
`S_i : 0 → A_i → Z_i → C_i → 0` and degree `n + 1` extensions `F_i = cut E_i` of `B` by `C_i`.
The classes `ξ ∘ (u_i ≫ E_i.f)` vanish, because `[S_i] ∘ E_i.f = 0`, so
`exists_shortExact_fac` produces a short exact sequence
`T : 0 → A → W → D → 0` with `ξ ∘ (A ⟶ W) = 0` whose monomorphism factors the two maps
`u_i ≫ E_i.f`, and `T` maps to `S_i` by `(u_i, p_i, v_i)` for the map `v_i : D ⟶ C_i` induced
by `p_i`. The covariant long exact sequence of `T` writes `ξ = ξ₀ ∘ [T]`, whence
`(ξ₀ ∘ v_i) ∘ [S_i] = δ(E_i) = δ(F_i) ∘ [S_i]` by naturality of the class of a short exact
sequence, so `ξ₀ ∘ v_i - δ(F_i)` lifts to `w_i ∈ Ext^{n + 1}_𝒜(B, Z_i)` by the covariant long
exact sequence of `S_i`. Correcting `ξ₀` by the class of `Ext^{n + 1}_𝒜(B, W)` whose components
are `w₁` and `w₂` gives a class `ξ'` with `ξ' ∘ v_i = δ(F_i)`, to which the inductive hypothesis
applies: a common refinement `G'` of `F₁` and `F₂` over `v₁`, `v₂` splices with `T` to a common
refinement of `E₁` and `E₂` over `u₁`, `u₂` (`exists_hom_splice`). -/
private lemma exists_hom₂_of_comp_mk₀_eq {B : 𝒜} : ∀ (n : ℕ) {A A₁ A₂ : 𝒜}
    (E₁ : YonedaExtension B A₁ n) (E₂ : YonedaExtension B A₂ n) (u₁ : A ⟶ A₁) (u₂ : A ⟶ A₂)
    (ξ : Ext.{w} B A (n + 1)),
    ξ.comp (Ext.mk₀ u₁) (add_zero (n + 1)) = extClassMap.{w} n E₁ →
    ξ.comp (Ext.mk₀ u₂) (add_zero (n + 1)) = extClassMap.{w} n E₂ →
    ∃ (G : YonedaExtension B A n) (φ : G.Z ⟶ E₁.Z) (ψ : G.Z ⟶ E₂.Z),
      G.f ≫ app' φ 0 = u₁ ≫ E₁.f ∧ app' φ n ≫ E₁.g = G.g ∧
        G.f ≫ app' ψ 0 = u₂ ≫ E₂.f ∧ app' ψ n ≫ E₂.g = G.g := by
  intro n
  induction n with
  | zero =>
    intro A A₁ A₂ E₁ E₂ u₁ u₂ ξ h₁ h₂
    obtain ⟨G, hG⟩ := surjective_extClassMap B A 0 ξ
    dsimp only at hG
    obtain ⟨q₁, hq₁, hq₁'⟩ :=
      exists_hom_of_extClassMap_comp_mk₀_eq G E₁ u₁ (by rw [hG]; exact h₁)
    obtain ⟨q₂, hq₂, hq₂'⟩ :=
      exists_hom_of_extClassMap_comp_mk₀_eq G E₂ u₂ (by rw [hG]; exact h₂)
    exact ⟨G, homMk₀ q₁, homMk₀ q₂, by simpa using hq₁, by simpa using hq₁',
      by simpa using hq₂, by simpa using hq₂'⟩
  | succ n ih =>
    intro A A₁ A₂ E₁ E₂ u₁ u₂ ξ h₁ h₂
    obtain ⟨W, D, ι, π, hzι, hT, p₁, p₂, hιp₁, hιp₂, hξι, hη⟩ :=
      exists_shortExact_fac (n + 1) ξ (u₁ ≫ E₁.f) (u₂ ≫ E₂.f)
        (comp_mk₀_comp_f_eq_zero E₁ u₁ ξ h₁) (comp_mk₀_comp_f_eq_zero E₂ u₂ ξ h₂)
    obtain ⟨ξ₀, hξ₀⟩ := Ext.covariant_sequence_exact₁ B hT ξ hξι rfl
    obtain ⟨v₁, hπv₁, w₁, hw₁⟩ := exists_comp_mk₀_π_eq_sub hT E₁ hιp₁ hξ₀ h₁
    obtain ⟨v₂, hπv₂, w₂, hw₂⟩ := exists_comp_mk₀_π_eq_sub hT E₂ hιp₂ hξ₀ h₂
    obtain ⟨η, hη₁, hη₂⟩ := hη (n + 1) w₁ w₂
    obtain ⟨G, φ', ψ', hφ'₁, hφ'₂, hψ'₁, hψ'₂⟩ :=
      ih (cut E₁) (cut E₂) v₁ v₂ (ξ₀ - η.comp (Ext.mk₀ π) (add_zero (n + 1)))
        (sub_comp_mk₀_eq_of_comp_mk₀_eq_sub hπv₁ hw₁ hη₁)
        (sub_comp_mk₀_eq_of_comp_mk₀_eq_sub hπv₂ hw₂ hη₂)
    obtain ⟨Φ, hΦ₁, hΦ₂⟩ := exists_hom_splice hT G E₁ u₁ p₁ v₁ hιp₁ hπv₁ φ' hφ'₁ hφ'₂
    obtain ⟨Ψ, hΨ₁, hΨ₂⟩ := exists_hom_splice hT G E₂ u₂ p₂ v₂ hιp₂ hπv₂ ψ' hψ'₁ hψ'₂
    exact ⟨splice hT G, Φ, Ψ, hΦ₁, hΦ₂, hΨ₁, hΨ₂⟩

/-- Two Yoneda extensions of the same degree with the same class are equivalent. -/
@[stacks 06XU "Yoneda extensions of the same degree with the same class are equivalent",
  ega "0 12.3.2" "δE=δE' ⇒ E~E'"]
lemma equivalent_of_extClassMap_eq {B A : 𝒜} {n : ℕ} (E E' : YonedaExtension B A n)
    (h : extClassMap.{w} n E = extClassMap.{w} n E') : E.Equivalent E' := by
  obtain ⟨G, φ, ψ, hφ₁, hφ₂, hψ₁, hψ₂⟩ :=
    exists_hom₂_of_comp_mk₀_eq n E E' (𝟙 A) (𝟙 A) (extClassMap.{w} n E)
      (by rw [Ext.comp_mk₀_id]) (by rw [Ext.comp_mk₀_id]; exact h)
  exact ⟨G, φ, ψ, by simpa using hφ₁, hφ₂, by simpa using hψ₁, hψ₂⟩

/-- The class map is surjective, for any map with the two characterising properties. -/
lemma surjective_of_isExtClassMap
    (δ : ∀ (B A : 𝒜) (n : ℕ), YonedaExtension B A n → Ext.{w} B A (n + 1))
    (hδ : IsExtClassMap δ) (B A : 𝒜) (n : ℕ) : Function.Surjective (δ B A n) := by
  rw [eq_extClassMap_of_isExtClassMap δ hδ]
  exact surjective_extClassMap B A n

/-- Two Yoneda extensions of the same degree are equivalent if and only if they have the same
class, for any map with the two characterising properties. -/
lemma equivalent_iff_of_isExtClassMap
    (δ : ∀ (B A : 𝒜) (n : ℕ), YonedaExtension B A n → Ext.{w} B A (n + 1))
    (hδ : IsExtClassMap δ) (B A : 𝒜) (n : ℕ) (E E' : YonedaExtension B A n) :
    E.Equivalent E' ↔ δ B A n E = δ B A n E' := by
  rw [eq_extClassMap_of_isExtClassMap δ hδ]
  exact ⟨extClassMap_eq_of_equivalent, equivalent_of_extClassMap_eq E E'⟩

end

end Abelian

end CategoryTheory

end
