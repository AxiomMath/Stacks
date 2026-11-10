module

public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.GlueingPicardSequence
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PushforwardCokernelVanishing
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PushforwardMono
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingPicard
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SquishingUnitsSequence

/-!
# Global sections across one elementary step

Let `f : X' ⟶ X` be a finite morphism of algebraic `k`-schemes which is an isomorphism over the
complement of a single point `x`, as every elementary step of [Stacks, Tag 0C1L] is. This file
proves that `Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})` is **bijective** for each of the two kinds of step:

* a glueing of two rational points lying on the **same** connected component of a proper `X'`;
* a squishing of a tangent vector of a proper reduced `X'`.

The two arguments look very different, because the two predicates package the exactness of
`0 ⟶ 𝒪_X ⟶ f_*𝒪_{X'} ⟶ k_x ⟶ 0` differently.

`AlgebraicGeometry.IsGlueingTwoPoints` states it germ-locally, so the glueing needs a two-open
gluing argument over the cover `{V, {x}ᶜ}` of `X`, where `V` is a neighbourhood of the glued
point supplied by the glueing's own clauses:

* *injectivity.* A section killed by `f` is killed near `x`, by the injectivity clause; away from
  `x` the morphism is an isomorphism; so the section vanishes on a cover and hence vanishes.
* *surjectivity.* A global section `s` of `𝒪_{X'}` takes the same value at the two glued points,
  by `Stacks.GluePicard.sectionAt_eq_of_connectedComponents_eq'`, so the descent clause of the
  glueing produces a `t` over some `V ∋ x` with `f^♯ t = s|_{f⁻¹V}`, while over `{x}ᶜ` the
  section descends because `f` is an isomorphism there. The two descents agree on the overlap
  because `f` is injective on sections, so they glue.

`AlgebraicGeometry.IsSquishingTangentVector` instead carries an honest `ShortExact` short complex
of sheaves of abelian groups, and for that no gluing is needed at all: injectivity is its
monomorphism read on sections over `⊤`, and surjectivity is left exactness of evaluation at an
open, `TopCat.Sheaf.sections_exact_of_left_exact`, applied to a global function whose
`ε`-coefficient vanishes by
`Stacks.SquishPicard.epsilonCoefficientAt_eq_zero_of_isProper_of_isReduced`.

The two general lemmas doing the work on the glueing side,
`Stacks.GlueSquishFactor.eq_zero_of_isIso_of_locally` and
`Stacks.GlueSquishFactor.exists_app_eq_of_le_sup`, are stated for an arbitrary morphism with a
cofinite isomorphism locus and mention no step at all.

Read together with
`Stacks.GlueSquishFactor.genus_eq_add_finrank_of_finrank_globalSections_eq`, the resulting
equality of `h⁰` is what turns the Euler-characteristic bookkeeping of one step into a statement
about the genus alone, which is what the induction of [Stacks, Tag 0C20] tracks.

## Main results

* `Stacks.GlueSquishFactor.eq_zero_of_isIso_of_locally` — a section of `𝒪_X` killed by `f` and
  vanishing near the one bad point vanishes.
* `Stacks.GlueSquishFactor.exists_app_eq_of_le_sup` — a section of `𝒪_{X'}` that descends near
  the bad point descends everywhere.
* `Stacks.GlueSquishFactor.bijective_appTop_of_isGlueingTwoPoints` and
  `Stacks.GlueSquishFactor.bijective_appTop_of_isSquishingTangentVector` — bijectivity of
  `Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})` for the two kinds of step.
* `Stacks.GlueSquishFactor.finrank_globalSections_eq_of_bijective_appTop`,
  `Stacks.GlueSquishFactor.finrank_globalSections_eq_of_isGlueingTwoPoints` and
  `Stacks.GlueSquishFactor.finrank_globalSections_eq_of_isSquishingTangentVector` — the resulting
  equality `h⁰(X') = h⁰(X)` of `k`-dimensions.

## References

* [Stacks Project, Tag 0C20](https://stacks.math.columbia.edu/tag/0C20)
* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
* [Stacks Project, Tag 0C1M](https://stacks.math.columbia.edu/tag/0C1M)
* [Stacks Project, Tag 0C1N](https://stacks.math.columbia.edu/tag/0C1N)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.GlueSquishFactor

/-! ### Vanishing and descent over a two-open cover -/

/-- Restricting along `B ≤ A` and applying `f^♯` commutes with applying `f^♯` and restricting. -/
private theorem app_map_eq {X' X : Scheme.{u}} (f : X' ⟶ X) {A B : X.Opens} (h : B ≤ A)
    (a : Γ(X, A)) : (f.app B).hom ((X.presheaf.map (homOfLE h).op).hom a)
      = (X'.presheaf.map (homOfLE (f.preimage_mono h)).op).hom ((f.app A).hom a) := by
  have h1 := congrArg (fun φ : Γ(X, A) ⟶ Γ(X', f ⁻¹ᵁ B) => φ.hom a) (map_comp_app f h)
  simpa only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply] using h1

/-- A point other than `x` lies in an open whose underlying set is `{x}ᶜ`. -/
private theorem mem_of_ne_of_eq_compl {X : Scheme.{u}} {x y : X} {U : X.Opens}
    (hU : (U : Set X) = {x}ᶜ) (hyx : y ≠ x) : y ∈ U := by
  rw [← SetLike.mem_coe, hU]
  exact hyx

/-- **A section of `𝒪_X` killed by `f^♯` vanishes**, for a morphism which is an isomorphism over
`{x}ᶜ` and whose kernel is concentrated near `x` in the sense of `hker`. Over `{x}ᶜ` the section
vanishes because `f^♯` is there an isomorphism, near `x` by `hker`, and the two opens cover
whichever open the section lives on. -/
theorem eq_zero_of_isIso_of_locally {X' X : Scheme.{u}} (f : X' ⟶ X)
    {x : X} {U : X.Opens} (hU : (U : Set X) = {x}ᶜ) [IsIso (f ∣_ U)]
    (hker : ∀ (Ω : X.Opens), x ∈ Ω → ∀ s : Γ(X, Ω), (f.app Ω).hom s = 0 →
      ∃ (V : X.Opens) (hVΩ : V ≤ Ω), x ∈ V ∧ (X.presheaf.map (homOfLE hVΩ).op).hom s = 0)
    (Ω : X.Opens) (s : Γ(X, Ω)) (hs : (f.app Ω).hom s = 0) : s = 0 := by
  by_cases hx : x ∈ Ω
  · obtain ⟨V, hVΩ, hxV, hV0⟩ := hker Ω hx s hs
    have hUΩ : Ω ⊓ U ≤ Ω := inf_le_left
    have : IsIso (f.app (Ω ⊓ U)) := isIso_app_of_isIso_morphismRestrict f U _ inf_le_right
    have hU0 : (X.presheaf.map (homOfLE hUΩ).op).hom s = 0 := by
      refine (ConcreteCategory.bijective_of_isIso (f.app (Ω ⊓ U))).1 ?_
      rw [app_map_eq, hs, map_zero, map_zero]
    have hcov : Ω ≤ V ⊔ (Ω ⊓ U) := by
      intro y hy
      by_cases hyx : y = x
      · exact Or.inl (hyx ▸ hxV)
      · exact Or.inr ⟨hy, mem_of_ne_of_eq_compl hU hyx⟩
    refine TopCat.Sheaf.eq_of_locally_eq₂ X.sheaf (homOfLE hVΩ) (homOfLE hUΩ) hcov s 0 ?_ ?_
    · change (X.presheaf.map (homOfLE hVΩ).op).hom s = (X.presheaf.map (homOfLE hVΩ).op).hom 0
      rw [hV0, map_zero]
    · change (X.presheaf.map (homOfLE hUΩ).op).hom s = (X.presheaf.map (homOfLE hUΩ).op).hom 0
      rw [hU0, map_zero]
  · have : IsIso (f.app Ω) := by
      refine isIso_app_of_isIso_morphismRestrict f U _ ?_
      intro y hy
      exact mem_of_ne_of_eq_compl hU fun hyx => hx (hyx ▸ hy)
    have := (ConcreteCategory.bijective_of_isIso (f.app Ω)).1 (a₁ := s) (a₂ := 0)
    simpa using this (by simpa using hs)

/-- **`f^♯` is injective on sections over every open**, under the hypotheses of
`Stacks.GlueSquishFactor.eq_zero_of_isIso_of_locally`: a ring homomorphism with trivial kernel is
injective. -/
theorem injective_app_of_isIso_of_locally {X' X : Scheme.{u}} (f : X' ⟶ X)
    {x : X} {U : X.Opens} (hU : (U : Set X) = {x}ᶜ) [IsIso (f ∣_ U)]
    (hker : ∀ (Ω : X.Opens), x ∈ Ω → ∀ s : Γ(X, Ω), (f.app Ω).hom s = 0 →
      ∃ (V : X.Opens) (hVΩ : V ≤ Ω), x ∈ V ∧ (X.presheaf.map (homOfLE hVΩ).op).hom s = 0)
    (Ω : X.Opens) : Function.Injective (f.app Ω).hom := by
  intro s₁ s₂ he
  have : s₁ - s₂ = 0 := by
    refine eq_zero_of_isIso_of_locally f hU hker Ω _ ?_
    rw [map_sub, he, sub_self]
  rwa [sub_eq_zero] at this

/-- **A section of `𝒪_{X'}` which descends over a neighbourhood of the bad point descends over
the whole of `Ω`**, for a morphism injective on sections and an isomorphism over `U`, when `Ω` is
covered by that neighbourhood and `U`. Over `U` the section descends because `f^♯` is an
isomorphism there; the two descents agree on `V ⊓ U` because `f^♯` is injective; and the sheaf
condition glues them. -/
theorem exists_app_eq_of_le_sup {X' X : Scheme.{u}} (f : X' ⟶ X)
    (hinj : ∀ W : X.Opens, Function.Injective (f.app W).hom)
    {V U Ω : X.Opens} (hVle : V ≤ Ω) (hUle : U ≤ Ω) (hΩ : Ω ≤ V ⊔ U) [IsIso (f ∣_ U)]
    (s : Γ(X', f ⁻¹ᵁ Ω)) (t : Γ(X, V))
    (hst : (X'.presheaf.map (homOfLE (f.preimage_mono hVle)).op).hom s = (f.app V).hom t) :
    ∃ r : Γ(X, Ω), (f.app Ω).hom r = s := by
  classical
  have : IsIso (f.app U) := isIso_app_of_isIso_morphismRestrict f U U le_rfl
  obtain ⟨tU, hfU⟩ := (ConcreteCategory.bijective_of_isIso (f.app U)).2
    ((X'.presheaf.map (homOfLE (f.preimage_mono hUle)).op).hom s)
  have hres : ∀ (A : X.Opens) (hAle : A ≤ Ω) (a : Γ(X, A)),
      (X'.presheaf.map (homOfLE (f.preimage_mono hAle)).op).hom s = (f.app A).hom a →
      ∀ (W : X.Opens) (hWA : W ≤ A),
      (f.app W).hom ((X.presheaf.map (homOfLE hWA).op).hom a)
        = (X'.presheaf.map (homOfLE (f.preimage_mono (hWA.trans hAle))).op).hom s := by
    intro A hAle a ha W hWA
    rw [app_map_eq, ← ha, ← CommRingCat.comp_apply, ← Functor.map_comp]
    rfl
  set W : Bool → X.Opens := fun c => cond c V U with hWdef
  have hWle : ∀ c, W c ≤ Ω := by intro c; cases c <;> assumption
  set sf : (c : Bool) → Γ(X, W c) := fun c => match c with | true => t | false => tU with hsfdef
  have hsec : ∀ c, (X'.presheaf.map (homOfLE (f.preimage_mono (hWle c))).op).hom s
      = (f.app (W c)).hom (sf c) := by
    intro c
    cases c
    · exact hfU.symm
    · exact hst
  have hcompat : TopCat.Presheaf.IsCompatible X.presheaf W sf := by
    intro c d
    refine hinj _ ?_
    exact (hres (W c) (hWle c) (sf c) (hsec c) (W c ⊓ W d) inf_le_left).trans
      (hres (W d) (hWle d) (sf d) (hsec d) (W c ⊓ W d) inf_le_right).symm
  have hcover : Ω ≤ ⨆ c, W c := by
    refine hΩ.trans ?_
    rw [iSup_bool_eq]
    exact le_rfl
  obtain ⟨r, hr, -⟩ :=
    X.sheaf.existsUnique_gluing' W Ω (fun c => homOfLE (hWle c)) hcover sf hcompat
  have hrV : (X.presheaf.map (homOfLE hVle).op).hom r = t := hr true
  have hrU : (X.presheaf.map (homOfLE hUle).op).hom r = tU := hr false
  refine ⟨r, ?_⟩
  refine TopCat.Sheaf.eq_of_locally_eq₂ X'.sheaf
    (homOfLE (f.preimage_mono hVle) : f ⁻¹ᵁ V ⟶ f ⁻¹ᵁ Ω)
    (homOfLE (f.preimage_mono hUle) : f ⁻¹ᵁ U ⟶ f ⁻¹ᵁ Ω) ?_ _ _ ?_ ?_
  · rw [← Scheme.Hom.preimage_sup]
    exact f.preimage_mono hΩ
  · have e1 : (X'.presheaf.map (homOfLE (f.preimage_mono hVle)).op).hom ((f.app Ω).hom r)
        = (f.app V).hom t := by rw [← app_map_eq f hVle r, hrV]
    exact e1.trans hst.symm
  · have e2 : (X'.presheaf.map (homOfLE (f.preimage_mono hUle)).op).hom ((f.app Ω).hom r)
        = (f.app U).hom tU := by rw [← app_map_eq f hUle r, hrU]
    exact e2.trans hfU

/-! ### Glueing two points on the same connected component -/

/-- **Glueing two rational points on the same connected component of a proper `X'` does not
change the global functions**: `Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})` is bijective.

Injectivity is `Stacks.GlueSquishFactor.injective_app_of_isIso_of_locally` fed by the
injectivity clause of `AlgebraicGeometry.IsGlueingTwoPoints`. For surjectivity, a global
function on `X'` takes the same value at the two glued points by
`Stacks.GluePicard.sectionAt_eq_of_connectedComponents_eq'`, so the descent clause of the glueing
produces a preimage near the glued point, and
`Stacks.GlueSquishFactor.exists_app_eq_of_le_sup` spreads it over all of `X`. -/
theorem bijective_appTop_of_isGlueingTwoPoints {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) [IsProper (X' ↘ Spec (.of k))]
    (hab : ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) =
      ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k))) :
    Function.Bijective (f.appTop).hom := by
  obtain ⟨ha, hb, -, -, -, -, -, -, hab', hfin, ⟨U, hUset, hUiso⟩, hker, hdesc, -⟩ := h
  have := hUiso
  have hkerloc : ∀ (Ω : X.Opens),
      (a ≫ f).base (IsLocalRing.closedPoint k) ∈ Ω → ∀ s : Γ(X, Ω), (f.app Ω).hom s = 0 →
      ∃ (V : X.Opens) (hVΩ : V ≤ Ω),
        (a ≫ f).base (IsLocalRing.closedPoint k) ∈ V ∧
          (X.presheaf.map (homOfLE hVΩ).op).hom s = 0 := by
    intro Ω hx s hs
    obtain ⟨V, hVΩ, hxV, hV0⟩ := hker Ω hx s ⟨Ω, le_rfl, hx, by rw [hs, map_zero]⟩
    exact ⟨V, hVΩ, hxV, hV0⟩
  have hinj := injective_app_of_isIso_of_locally f hUset hkerloc
  refine ⟨hinj ⊤, fun s => ?_⟩
  obtain ⟨V, hVtop, hxV, t, hst⟩ := hdesc ⊤ (Opens.mem_top _) s (by
    rw [sub_eq_zero]
    exact Stacks.GluePicard.sectionAt_eq_of_connectedComponents_eq' a b ha hb hab s)
  refine exists_app_eq_of_le_sup f hinj hVtop (le_top (a := U)) ?_ s t hst
  intro y _
  by_cases hyx : y = (a ≫ f).base (IsLocalRing.closedPoint k)
  · exact Or.inl (hyx ▸ hxV)
  · exact Or.inr (mem_of_ne_of_eq_compl hUset hyx)

/-! ### Squishing a tangent vector -/

/-- **Squishing a tangent vector of a proper reduced `X'` does not change the global
functions**: `Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})` is bijective.

No gluing is needed here, because `AlgebraicGeometry.IsSquishingTangentVector` states its
exactness as a short exact sequence of sheaves of abelian groups rather than germ-locally:
injectivity is the monomorphism of that sequence, read on sections over `⊤`, and surjectivity is
left exactness of evaluation at an open, `TopCat.Sheaf.sections_exact_of_left_exact`, applied to
a global function whose `ε`-coefficient vanishes by
`Stacks.SquishPicard.epsilonCoefficientAt_eq_zero_of_isProper_of_isReduced`. -/
theorem bijective_appTop_of_isSquishingTangentVector {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ)
    [IsProper (X' ↘ Spec (.of k))] [AlgebraicGeometry.IsReduced X'] :
    Function.Bijective (f.appTop).hom := by
  obtain ⟨ψ, hzero, hshort, hψ⟩ :=
    Stacks.SquishSheafSequence.shortExact_of_isSquishingTangentVector f θ h
  have := hshort.mono_f
  have : Mono (Stacks.SquishSheafSequence.structureToPushforwardAddSheaf f).hom :=
    Functor.map_mono (TopCat.Sheaf.forget AddCommGrpCat.{u} X)
      (Stacks.SquishSheafSequence.structureToPushforwardAddSheaf f)
  refine ⟨(AddCommGrpCat.mono_iff_injective
      ((Stacks.SquishSheafSequence.structureToPushforwardAddSheaf f).hom.app
        (op (⊤ : X.Opens)))).mp inferInstance, fun s => ?_⟩
  have hcoef : AlgebraicGeometry.epsilonCoefficientAt θ (f ⁻¹ᵁ (⊤ : X.Opens))
      (Opens.mem_top _) s = 0 :=
    Stacks.SquishPicard.epsilonCoefficientAt_eq_zero_of_isProper_of_isReduced f θ h s
  refine TopCat.Sheaf.sections_exact_of_left_exact (U := (⊤ : X.Opens))
    hshort.exact hshort.mono_f s ?_
  rw [hψ ⊤ (Opens.mem_top _) s, hcoef,
    Stacks.SquishSheafSequence.skyscraperAddSheafMk_zero]

/-! ### The resulting equality of dimensions -/

/-- **`h⁰(X') = h⁰(X)` whenever `Γ(X, 𝒪_X) ⟶ Γ(X', 𝒪_{X'})` is bijective.** The map is a
homomorphism of `k`-algebras for the structures pulled back along `p` and along `f ≫ p`, because
`(f ≫ p)^♯ = f^♯ ∘ p^♯` on global sections; a bijective algebra homomorphism is a `k`-linear
equivalence, and `k`-linearly equivalent modules have the same dimension. -/
theorem finrank_globalSections_eq_of_bijective_appTop (k : Type u) [Field k]
    {X' X : Scheme.{u}} (f : X' ⟶ X) (p : X ⟶ Spec (.of k))
    (hbij : Function.Bijective (f.appTop).hom) :
    letI : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
    letI : Algebra k Γ(X', ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ p).appTop).hom.toAlgebra
    Module.finrank k Γ(X', ⊤) = Module.finrank k Γ(X, ⊤) := by
  let : Algebra k Γ(X, ⊤) := ((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom.toAlgebra
  let : Algebra k Γ(X', ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ p).appTop).hom.toAlgebra
  have e : Γ(X, ⊤) ≃ₐ[k] Γ(X', ⊤) :=
    AlgEquiv.ofRingEquiv (f := RingEquiv.ofBijective (f.appTop).hom hbij) (by
      intro c
      change (f.appTop).hom (((Scheme.ΓSpecIso (.of k)).inv ≫ p.appTop).hom c)
        = ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ p).appTop).hom c
      have hc : (f ≫ p).appTop = p.appTop ≫ f.appTop := by simp
      rw [hc]
      simp)
  exact e.toLinearEquiv.finrank_eq.symm

/-- **Glueing two rational points on the same connected component of a proper `X'` does not
change `h⁰`.** This is the hypothesis of
`Stacks.GlueSquishFactor.genus_eq_add_finrank_of_finrank_globalSections_eq`, so together with the
Euler-characteristic bookkeeping of one step it says that the genus of `X` exceeds that of `X'`
by exactly `dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X)` across such a glueing. -/
theorem finrank_globalSections_eq_of_isGlueingTwoPoints {k : Type u} [Field k] [IsAlgClosed k]
    {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (a b : Spec (.of k) ⟶ X')
    (h : AlgebraicGeometry.IsGlueingTwoPoints f a b) [IsProper (X' ↘ Spec (.of k))]
    (hab : ConnectedComponents.mk (a.base (IsLocalRing.closedPoint k)) =
      ConnectedComponents.mk (b.base (IsLocalRing.closedPoint k))) :
    letI : Algebra k Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom.toAlgebra
    letI : Algebra k Γ(X', ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ X ↘ Spec (.of k)).appTop).hom.toAlgebra
    Module.finrank k Γ(X', ⊤) = Module.finrank k Γ(X, ⊤) :=
  finrank_globalSections_eq_of_bijective_appTop k f (X ↘ Spec (.of k))
    (bijective_appTop_of_isGlueingTwoPoints f a b h hab)

/-- **Squishing a tangent vector of a proper reduced `X'` does not change `h⁰`.** Together with
`Stacks.GlueSquishFactor.genus_eq_add_finrank_of_finrank_globalSections_eq` this says that the
genus of `X` exceeds that of `X'` by exactly `dim_k H⁰(X, f_*𝒪_{X'}/𝒪_X)` across a squishing as
well. -/
theorem finrank_globalSections_eq_of_isSquishingTangentVector {k : Type u} [Field k]
    [IsAlgClosed k] {X' X : Scheme.{u}} [X'.Over (Spec (.of k))] [X.Over (Spec (.of k))]
    (f : X' ⟶ X) (θ : Spec (.of (DualNumber k)) ⟶ X')
    (h : AlgebraicGeometry.IsSquishingTangentVector f θ)
    [IsProper (X' ↘ Spec (.of k))] [AlgebraicGeometry.IsReduced X'] :
    letI : Algebra k Γ(X, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (X ↘ Spec (.of k)).appTop).hom.toAlgebra
    letI : Algebra k Γ(X', ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (f ≫ X ↘ Spec (.of k)).appTop).hom.toAlgebra
    Module.finrank k Γ(X', ⊤) = Module.finrank k Γ(X, ⊤) :=
  finrank_globalSections_eq_of_bijective_appTop k f (X ↘ Spec (.of k))
    (bijective_appTop_of_isSquishingTangentVector f θ h)

end Stacks.GlueSquishFactor

end
