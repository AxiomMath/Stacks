module

public import StacksFrontier.AlgebraicGeometry.Coherent.HomColimit.IdealPowerBridge

/-!
# Surjectivity of the canonical map `colim_n Hom(Iⁿ, F) ⟶ Γ(U, F)`

Let `X` be a quasi-compact scheme, let `I` be a quasi-coherent sheaf of ideals of finite type, let
`Z` be the closed subscheme it defines and let `U = X \ Z`. Let `F` be a quasi-coherent
`𝒪_X`-module which has **no `I`-power torsion**, that is, for which the subsheaf `F_N` of sections
annihilated by `Iᴺ` is zero for every `N`. This file proves that the canonical map

`colim_n Hom_{𝒪_X}(Iⁿ, F) ⟶ Γ(U, F)`

of `StacksFrontier/AlgebraicGeometry/Coherent/HomColimit/Injectivity.lean` is **surjective**, hence,
with the injectivity proved there, bijective.

This is the second assertion of Tag 01PQ in the case `F_N = 0`, where `F/F_N = F`: it is the case
of that assertion which [Stacks, Tag 01YB] invokes, after replacing `F` by `F' = Iᵐ F` for a large
`m` supplied by Artin-Rees.

## Main definitions

* `Stacks.AlgebraicGeometry.IdealPowerColimit.IsValue`: for `s : Γ(U, F)`, a section `a` of
  `𝒪_X` over `V` and a section `y` of `F` over `W`, the predicate that `y` agrees with `a • s`
  on every open contained in `W`, in `V` and in `U`. Such a `y` is *the value of* `a • s`.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.NoIdealTorsion`: the hypothesis `F_N = 0` for all
  `N`, spelled affine-locally as "a section annihilated by `I(V)ᴺ` is zero".
* `Stacks.AlgebraicGeometry.IdealPowerColimit.valueIdeal`: the ideal of sections of `𝒪_X` over
  `V` admitting a value.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.homOfSections`: a morphism of `𝒪_X`-modules built
  from a natural family of linear maps on sections.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.valueHom`: the morphism `Iᴺ ⟶ F` assembled from
  the values, the preimage of `s` under the canonical map.

## Main results

* `Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToSections_surjective`: the canonical
  map is surjective. **This is the second assertion of Tag 01PQ in the case `F_N = 0` only**;
  the general assertion, about `colim_n Hom(Iⁿ, F/F_N) ⟶ Γ(U, F)`, needs the quotient sheaves
  `F/F_N` and is not proved here.  Those quotients are built in
  `StacksFrontier/AlgebraicGeometry/Coherent/HomColimit/AnnihilatorQuotient.lean`, and the
  canonical map out of `colim_n Hom(Iⁿ, F/F_n)` is constructed and proved *injective* in
  `StacksFrontier/AlgebraicGeometry/Coherent/HomColimit/QuotientColimit.lean`; its surjectivity,
  which is the only part of Tag 01PQ that uses quasi-separatedness of `X`, is
  `Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToSectionsQuotient_surjective` of
  `StacksFrontier/AlgebraicGeometry/Coherent/HomColimit/QuotientSurjectivity.lean`, whence the
  general assertion `…_bijective` there, with no torsion hypothesis.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_hom_idealPow_app_oneSection_eq`: the same
  statement in existence form, which is the shape the global-sections clause of
  [Stacks, Tag 01YB] consumes.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToSections_bijective`: combining this
  with the injectivity proved before.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.IsValue.unique`,
  `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_isValue_pow` and
  `Stacks.AlgebraicGeometry.IdealPowerColimit.exists_isValue_of_iSup`: the three steps of the
  argument, uniqueness, the affine case and gluing.
* `Stacks.AlgebraicGeometry.IdealPowerColimit.noIdealTorsion_of_idealPowerAnnihilator_obj_eq_bot`:
  the hypothesis in the form the ideal-power annihilator supplies it.

## Implementation notes

**Why values, and why no quotient appears.** The proof of Tag 01PM in the source builds the
inverse map out of a vector `xᵢ/fᵢⁿ` in `⨁ᵢ M_{fᵢ}`, introduces
`Kₙ = {x ∈ M | f₁ⁿx = … = fₜⁿx = 0}`, and defines a monomial map
`I^(t(n-1)+1) → M/Kₙ` on a free module on multi-indices. Under the hypothesis `F_N = 0` all of
this collapses: `Kₙ ⊆ M_{t(n-1)+1} = 0`, so no quotient is needed, and more importantly the
section `y` of `F` over `V` representing `a • s` is **unique**, because a section of `F` over `V`
restricting to zero on `V ∩ U` is annihilated by a power of `I(V)` and hence is zero
(`eq_zero_of_res_compl_eq_zero`). Uniqueness makes linearity in `a`, naturality in `V` and
gluing over a covering automatic, so the construction is organised around the predicate `IsValue`
rather than around an explicit formula: the monomials, the free module on multi-indices and the
relations `fⱼⁿxᵢ = fᵢⁿxⱼ` all disappear.

**Where the exponent comes from.** `valueIdeal s V` is an ideal, so it suffices to show that
`I(V)` lies in its radical: for `f ∈ I(V)` the section `s` restricted to `D(f)` is `y₀/fᵏ` for
some `y₀ : Γ(V, F)` (the affine case of the Qcqs lemma for modules), and a further power of `f`
corrects `y₀` so that it agrees with `f^(k+m) • s` on all of `V ∩ U` and not merely on `D(f)`.
That correction is the only place where `V ∩ U` must be quasi-compact, which it is: it is the
finite union of the `D(fᵢ)` for a set of generators `fᵢ` of `I(V)`
(`inf_compl_eq_iSup_basicOpen`). `Ideal.exists_pow_le_of_le_radical_of_fg` then gives a single
exponent on each affine open, and a finite affine cover of `X` gives a single exponent globally,
the descent to smaller affine opens being `pow_le_valueIdeal_of_le`.

**Quasi-separatedness is not needed.** Tag 01PQ assumes `X` quasi-separated for its second
assertion, because the source glues morphisms `φⱼ` defined on the members `Wⱼ` of a finite affine
cover and must compare them on a finite affine cover of each `Wⱼ ∩ Wⱼ'`. Here the local sections
being glued are unique, so there is nothing to compare and only quasi-compactness of `X` is used.

## References

* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ)
* [Stacks Project, Tag 01PM](https://stacks.math.columbia.edu/tag/01PM) (the affine case)
* [Stacks Project, Tag 01YB](https://stacks.math.columbia.edu/tag/01YB) (the consumer)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry TopologicalSpace
open Stacks.AlgebraicGeometry.IdealPower
open Stacks.AlgebraicGeometry.GabberColimit (res_res res_self)
open Stacks.AlgebraicGeometry.QcqsLocalization

universe u

namespace Stacks.AlgebraicGeometry.IdealPowerColimit

variable {X : Scheme.{u}} {I : X.IdealSheafData} {F : X.Modules}

/-! ### Values of `a • s` -/

/-- For a section `s` of `F` over `U = X \ V(I)`, a section `a` of `𝒪_X` over `V` and a section
`y` of `F` over `W`, the predicate that `y` restricts to `a • s` on every open contained in
`W`, in `V` and in `U`. -/
def IsValue (s : Γ(F, (I.support.compl : X.Opens))) {V : X.Opens} (a : Γ(X, V)) {W : X.Opens}
    (y : Γ(F, W)) : Prop :=
  ∀ (W' : X.Opens) (h1 : W' ≤ W) (h2 : W' ≤ (I.support.compl : X.Opens)) (h3 : W' ≤ V),
    F.presheaf.map (homOfLE h1).op y
      = X.presheaf.map (homOfLE h3).op a • F.presheaf.map (homOfLE h2).op s

variable {s : Γ(F, (I.support.compl : X.Opens))}

/-- The unit section of `Iⁿ` over the complement of the support has value `1`. -/
theorem val_oneSection (I : X.IdealSheafData) (n : ℕ) :
    ((oneSection I n).1 : Γ(X, (I.support.compl : X.Opens)))
      = (1 : Γ(X, (I.support.compl : X.Opens))) := rfl

/-- A value over `W` is a value over any smaller open. -/
theorem IsValue.res {V : X.Opens} {a : Γ(X, V)} {W : X.Opens} {y : Γ(F, W)}
    (h : IsValue s a y) {W₀ : X.Opens} (hW₀ : W₀ ≤ W) :
    IsValue s a (F.presheaf.map (homOfLE hW₀).op y) := by
  intro W' h1 h2 h3
  rw [res_res F hW₀ h1, h W' (h1.trans hW₀) h2 h3]

/-- The scalar of a value may be restricted to a smaller open. -/
theorem IsValue.restrictScalar {V V₀ : X.Opens} {a : Γ(X, V)} {W : X.Opens} {y : Γ(F, W)}
    (h : IsValue s a y) (hV : V₀ ≤ V) :
    IsValue s (X.presheaf.map (homOfLE hV).op a) y := by
  intro W' h1 h2 h3
  rw [h W' h1 h2 (h3.trans hV), presheaf_map_map h3 hV (h3.trans hV) a]

/-- Conversely, a value for the restriction of `a` to the domain of the section is a value
for `a` itself. -/
theorem IsValue.ofRestrictScalar {V W : X.Opens} {a : Γ(X, V)} (hWV : W ≤ V) {y : Γ(F, W)}
    (h : IsValue s (X.presheaf.map (homOfLE hWV).op a) y) : IsValue s a y := by
  intro W' h1 h2 h3
  rw [h W' h1 h2 h1, presheaf_map_map h1 hWV h3 a]

/-- Zero is a value of `0 • s`. -/
theorem isValue_zero (s : Γ(F, (I.support.compl : X.Opens))) (V W : X.Opens) :
    IsValue s (0 : Γ(X, V)) (0 : Γ(F, W)) := by
  intro W' h1 h2 h3
  rw [map_zero, map_zero, zero_smul]

/-- Values add. -/
theorem IsValue.add {V W : X.Opens} {a₁ a₂ : Γ(X, V)} {y₁ y₂ : Γ(F, W)}
    (h₁ : IsValue s a₁ y₁) (h₂ : IsValue s a₂ y₂) : IsValue s (a₁ + a₂) (y₁ + y₂) := by
  intro W' h1 h2 h3
  rw [map_add, h₁ W' h1 h2 h3, h₂ W' h1 h2 h3, map_add, add_smul]

/-- Values scale. -/
theorem IsValue.smul {V : X.Opens} {a : Γ(X, V)} {y : Γ(F, V)} (h : IsValue s a y)
    (r : Γ(X, V)) : IsValue s (r * a) (r • y) := by
  intro W' h1 h2 h3
  rw [F.map_smul (homOfLE h1), h W' h1 h2 h3, smul_smul, map_mul]

/-! ### Torsion-freeness and uniqueness of values -/

/-- `F` has no `Iⁿ`-torsion: on every affine open, a section annihilated by `I(V)ⁿ` is zero.
This is the hypothesis `F_N = 0` for all `N` of [Stacks, Tag 01YB]. -/
def NoIdealTorsion (I : X.IdealSheafData) (F : X.Modules) : Prop :=
  ∀ (N : ℕ) (V : X.affineOpens) (y : Γ(F, V.1)),
    (∀ a ∈ (I.ideal V ^ N : Ideal Γ(X, V.1)), a • y = 0) → y = 0

/-- A section of `F` vanishing on every open contained both in its domain and in `X \ V(I)`
vanishes, provided `F` has no `I`-power torsion. -/
theorem eq_zero_of_res_compl_eq_zero [F.IsQuasicoherent]
    (hFT : ∀ V : X.affineOpens, (I.ideal V).FG) (hTF : NoIdealTorsion I F)
    {V : X.Opens} (y : Γ(F, V))
    (h : ∀ (W : X.Opens) (hWV : W ≤ V), W ≤ (I.support.compl : X.Opens) →
      F.presheaf.map (homOfLE hWV).op y = 0) :
    y = 0 := by
  refine eq_zero_of_restrict_affineOpens_eq_zero y fun V' hV' ↦ ?_
  set y' := F.presheaf.map (homOfLE hV').op y with hy'
  have key : ∀ f ∈ I.ideal V', ∃ k : ℕ, f ^ k • y' = 0 := by
    intro f hf
    have hDU : X.basicOpen f ≤ (I.support.compl : X.Opens) :=
      basicOpen_le_compl_support I V' hf
    have hres : F.presheaf.map (homOfLE (X.basicOpen_le f)).op y' = 0 := by
      rw [hy', res_res F hV' (X.basicOpen_le f)]
      exact h _ _ hDU
    exact exists_pow_smul_eq_zero_of_res_eq_zero_of_isCompact F V'.2.isCompact f rfl
      (X.basicOpen_le f) y' hres
  obtain ⟨N, hN⟩ := Ideal.exists_pow_le_of_le_radical_of_fg
    (J := (Submodule.span Γ(X, V'.1) {y'}).annihilator)
    (fun f hf ↦ by
      obtain ⟨k, hk⟩ := key f hf
      exact ⟨k, (Submodule.mem_annihilator_span_singleton _ _).mpr hk⟩) (hFT V')
  exact hTF N V' y' fun a ha ↦ (Submodule.mem_annihilator_span_singleton _ _).mp (hN ha)

/-- **Values are unique.** Two sections of `F` over `W ≤ V` that are both values of `a • s` are
equal. -/
theorem IsValue.unique [F.IsQuasicoherent] (hFT : ∀ V : X.affineOpens, (I.ideal V).FG)
    (hTF : NoIdealTorsion I F) {V W : X.Opens} {a : Γ(X, V)} (hWV : W ≤ V) {y₁ y₂ : Γ(F, W)}
    (h₁ : IsValue s a y₁) (h₂ : IsValue s a y₂) : y₁ = y₂ := by
  refine sub_eq_zero.mp (eq_zero_of_res_compl_eq_zero hFT hTF (y₁ - y₂) fun W' hW' hW'U ↦ ?_)
  rw [map_sub, h₁ W' hW' hW'U (hW'.trans hWV), h₂ W' hW' hW'U (hW'.trans hWV), sub_self]

/-- Restricting `a • s`, with `a` and `s` already restricted to `P`, to a smaller open `W`. -/
private theorem map_smul_map_map {V U P W : X.Opens} (hWP : W ≤ P) (hPV : P ≤ V) (hPU : P ≤ U)
    (hWV : W ≤ V) (hWU : W ≤ U) (a : Γ(X, V)) (s : Γ(F, U)) :
    F.presheaf.map (homOfLE hWP).op
        (X.presheaf.map (homOfLE hPV).op a • F.presheaf.map (homOfLE hPU).op s)
      = X.presheaf.map (homOfLE hWV).op a • F.presheaf.map (homOfLE hWU).op s := by
  rw [F.map_smul, presheaf_map_map hWP hPV hWV, res_res F hPU hWP s]

/-- A value may be recognised by its restriction to `V ⊓ (X \ V(I))`. -/
theorem isValue_of_res_inf {V : X.Opens} {a : Γ(X, V)} {y : Γ(F, V)}
    (h : F.presheaf.map
          (homOfLE (inf_le_left : V ⊓ (I.support.compl : X.Opens) ≤ V)).op y
        = X.presheaf.map
            (homOfLE (inf_le_left : V ⊓ (I.support.compl : X.Opens) ≤ V)).op a •
          F.presheaf.map (homOfLE (inf_le_right : V ⊓ (I.support.compl : X.Opens)
            ≤ (I.support.compl : X.Opens))).op s) :
    IsValue s a y := by
  intro W' h1 h2 h3
  have hWP : W' ≤ V ⊓ (I.support.compl : X.Opens) := le_inf h1 h2
  rw [← res_res F inf_le_left hWP y, h]
  exact map_smul_map_map hWP inf_le_left inf_le_right h3 h2 a s

/-! ### The complement of `V(I)` inside an affine open -/

/-- Inside an affine open `V`, the complement of the support of `I` is the union of the basic
opens attached to a finite set of generators of `I(V)`. -/
theorem inf_compl_eq_iSup_basicOpen (I : X.IdealSheafData) (V : X.affineOpens)
    (G : Finset Γ(X, V.1)) (hG : Ideal.span (G : Set Γ(X, V.1)) = I.ideal V) :
    (V.1 ⊓ (I.support.compl : X.Opens) : X.Opens)
      = ⨆ f : G, X.basicOpen (f : Γ(X, V.1)) := by
  refine le_antisymm (fun x hx ↦ ?_) (iSup_le fun f ↦ le_inf (X.basicOpen_le _)
    (basicOpen_le_compl_support I V (hG ▸ Ideal.subset_span f.2)))
  obtain ⟨hxV, hxU⟩ := hx
  have hz : x ∉ X.zeroLocus (U := V.1) (I.ideal V : Set Γ(X, V.1)) := fun h ↦
    hxU ((Scheme.IdealSheafData.mem_support_iff_of_mem hxV).mpr h)
  rw [← hG, Scheme.zeroLocus_span, Scheme.mem_zeroLocus_iff] at hz
  push Not at hz
  obtain ⟨f, hfG, hxf⟩ := hz
  exact Opens.mem_iSup.mpr ⟨⟨f, hfG⟩, hxf⟩

/-- Inside an affine open `V` on which `I` is of finite type, the complement of the support of
`I` is quasi-compact, being a finite union of basic opens. -/
theorem isCompact_inf_compl (I : X.IdealSheafData) (V : X.affineOpens)
    (hFG : (I.ideal V).FG) :
    IsCompact ((V.1 ⊓ (I.support.compl : X.Opens) : X.Opens) : Set X) := by
  obtain ⟨G, hG⟩ := hFG
  rw [inf_compl_eq_iSup_basicOpen I V G hG, Opens.coe_iSup]
  exact isCompact_iUnion fun f ↦ (V.2.basicOpen (f : Γ(X, V.1))).isCompact

/-! ### The affine case: a power of each element of `I(V)` has a value -/

/-- **The affine case of surjectivity.** On an affine open `V` with `I(V)` finitely generated,
every `f ∈ I(V)` has a power `f ^ n` admitting a value: a section of `F` over `V` restricting
to `f ^ n • s` on `V ∩ (X \ V(I))`.

The section is produced on the basic open `D(f)`, where `F` is the localization of `Γ(F, V)`,
and then corrected by a further power of `f` so that it agrees with `f ^ n • s` on the whole of
`V ∩ (X \ V(I))` and not merely on `D(f)`. -/
theorem exists_isValue_pow [F.IsQuasicoherent] (s : Γ(F, (I.support.compl : X.Opens)))
    (V : X.affineOpens) (hFG : (I.ideal V).FG) {f : Γ(X, V.1)} (hf : f ∈ I.ideal V) :
    ∃ (n : ℕ) (y : Γ(F, V.1)), IsValue s (f ^ n) y := by
  have hPV : (V.1 ⊓ (I.support.compl : X.Opens) : X.Opens) ≤ V.1 := inf_le_left
  have hPU : (V.1 ⊓ (I.support.compl : X.Opens) : X.Opens)
      ≤ (I.support.compl : X.Opens) := inf_le_right
  have hDfV : X.basicOpen f ≤ V.1 := X.basicOpen_le f
  have hDfU : X.basicOpen f ≤ (I.support.compl : X.Opens) :=
    basicOpen_le_compl_support I V hf
  have hDfP : X.basicOpen f ≤ (V.1 ⊓ (I.support.compl : X.Opens) : X.Opens) :=
    le_inf hDfV hDfU
  obtain ⟨k, y₀, hy₀⟩ := exists_eq_pow_smul_of_isAffineOpen F V.2 f rfl hDfV
    (F.presheaf.map (homOfLE hDfU).op s)
  set fP := X.presheaf.map (homOfLE hPV).op f with hfP
  set sP := F.presheaf.map (homOfLE hPU).op s with hsP
  set d := F.presheaf.map (homOfLE hPV).op y₀ - fP ^ k • sP with hdef
  have hd : F.presheaf.map (homOfLE hDfP).op d = 0 := by
    rw [hdef, map_sub, res_res F hPV hDfP y₀, hfP, ← map_pow,
      map_smul_map_map hDfP hPV hPU hDfV hDfU, hy₀, map_pow, sub_self]
  have hbo : X.basicOpen f = X.basicOpen fP := by
    rw [hfP, Scheme.basicOpen_res]
    exact (inf_eq_right.mpr hDfP).symm
  obtain ⟨m, hm⟩ := exists_pow_smul_eq_zero_of_res_eq_zero_of_isCompact F
    (isCompact_inf_compl I V hFG) fP hbo hDfP d hd
  refine ⟨m + k, f ^ m • y₀, isValue_of_res_inf ?_⟩
  rw [hdef, smul_sub, sub_eq_zero] at hm
  rw [F.map_smul (homOfLE hPV), map_pow, ← hfP, hm, smul_smul, ← pow_add, map_pow, ← hfP]


/-! ### The ideal of scalars admitting a value -/

/-- The sections of `𝒪_X` over `V` that admit a value for `s`.  This is an ideal because values
add and scale, and it is the set over which a morphism `Iᴺ ⟶ F` recovering `s` can be
defined. -/
noncomputable def valueIdeal (s : Γ(F, (I.support.compl : X.Opens))) (V : X.Opens) :
    Ideal Γ(X, V) where
  carrier := {a | ∃ y : Γ(F, V), IsValue s a y}
  add_mem' := fun ⟨y₁, h₁⟩ ⟨y₂, h₂⟩ ↦ ⟨y₁ + y₂, h₁.add h₂⟩
  zero_mem' := ⟨0, isValue_zero s V V⟩
  smul_mem' := fun r _ h ↦ by
    obtain ⟨y, hy⟩ := h
    exact ⟨r • y, by rw [smul_eq_mul]; exact hy.smul r⟩

/-- Membership in `valueIdeal` is the existence of a value, by definition. -/
theorem mem_valueIdeal {s : Γ(F, (I.support.compl : X.Opens))} {V : X.Opens} {a : Γ(X, V)} :
    a ∈ valueIdeal s V ↔ ∃ y : Γ(F, V), IsValue s a y := Iff.rfl

/-- **A power of `I(V)` admits values on an affine open.** Every element of `I(V)` has a power
admitting a value, so `I(V)` lies in the radical of the ideal of scalars admitting a value;
finite generation then produces a single exponent. -/
theorem exists_pow_le_valueIdeal [F.IsQuasicoherent] (s : Γ(F, (I.support.compl : X.Opens)))
    (V : X.affineOpens) (hFG : (I.ideal V).FG) :
    ∃ N : ℕ, (I.ideal V ^ N : Ideal Γ(X, V.1)) ≤ valueIdeal s V.1 :=
  Ideal.exists_pow_le_of_le_radical_of_fg
    (fun f hf ↦ by
      obtain ⟨n, y, hy⟩ := exists_isValue_pow s V hFG hf
      exact ⟨n, y, hy⟩) hFG

/-- Values descend to smaller affine opens: `I(V)ᴺ` is generated by the restrictions of
`I(W)ᴺ`, each of which has a value over `W`, and restriction of a value is a value. -/
theorem pow_le_valueIdeal_of_le (s : Γ(F, (I.support.compl : X.Opens))) {V W : X.affineOpens}
    (hVW : V.1 ≤ W.1) {N : ℕ} (h : (I.ideal W ^ N : Ideal Γ(X, W.1)) ≤ valueIdeal s W.1) :
    (I.ideal V ^ N : Ideal Γ(X, V.1)) ≤ valueIdeal s V.1 := by
  rw [← map_idealPow I N hVW, Ideal.map_le_iff_le_comap]
  intro b hb
  rw [Ideal.mem_comap]
  obtain ⟨y, hy⟩ := h hb
  exact ⟨F.presheaf.map (homOfLE hVW).op y, (hy.res hVW).restrictScalar hVW⟩

/-- **A single exponent works on a finite affine cover.** -/
theorem exists_forall_pow_le_valueIdeal [CompactSpace X] [F.IsQuasicoherent]
    (hFT : ∀ V : X.affineOpens, (I.ideal V).FG)
    (s : Γ(F, (I.support.compl : X.Opens))) :
    ∃ (N : ℕ) (c : Set X.affineOpens),
      (Set.univ : Set X) = ⋃ i ∈ c, ((i : X.affineOpens) : Set X) ∧
        ∀ W ∈ c, (I.ideal W ^ N : Ideal Γ(X, W.1)) ≤ valueIdeal s W.1 := by
  classical
  obtain ⟨c, hcfin, hcov⟩ :=
    isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens.mp
      (⟨isCompact_univ, isOpen_univ⟩ :
        IsCompact (Set.univ : Set X) ∧ IsOpen (Set.univ : Set X))
  have key : ∀ V : X.affineOpens,
      ∃ N : ℕ, (I.ideal V ^ N : Ideal Γ(X, V.1)) ≤ valueIdeal s V.1 :=
    fun V ↦ exists_pow_le_valueIdeal s V (hFT V)
  choose Nf hNf using key
  refine ⟨hcfin.toFinset.sup Nf, c, hcov, fun W hW ↦ ?_⟩
  exact le_trans (Ideal.pow_le_pow_right (Finset.le_sup (hcfin.mem_toFinset.mpr hW))) (hNf W)

/-! ### Gluing values -/

/-- **Values glue.** If `a` has a value on every member of an open covering of `V`, it has a
value on `V`: the local values agree on overlaps by uniqueness, so they glue, and the glued
section is a value because the defining identity is local. -/
theorem exists_isValue_of_iSup [F.IsQuasicoherent] (hFT : ∀ V : X.affineOpens, (I.ideal V).FG)
    (hTF : NoIdealTorsion I F) (s : Γ(F, (I.support.compl : X.Opens))) {V : X.Opens}
    (a : Γ(X, V)) {ι : Type u} (W : ι → X.Opens) (hWV : ∀ i, W i ≤ V) (hcov : V ≤ ⨆ i, W i)
    (hy : ∀ i, ∃ y : Γ(F, W i), IsValue s a y) :
    ∃ y : Γ(F, V), IsValue s a y := by
  classical
  choose y hy using hy
  have hcompat : TopCat.Presheaf.IsCompatible F.presheaf W y := by
    intro i j
    change F.presheaf.map (homOfLE (inf_le_left : W i ⊓ W j ≤ W i)).op (y i) =
      F.presheaf.map (homOfLE (inf_le_right : W i ⊓ W j ≤ W j)).op (y j)
    exact IsValue.unique hFT hTF (le_trans (inf_le_left : W i ⊓ W j ≤ W i) (hWV i))
      ((hy i).res inf_le_left) ((hy j).res inf_le_right)
  obtain ⟨g, hg, -⟩ := TopCat.Sheaf.existsUnique_gluing' (F := abSheaf F) W V
    (fun i ↦ homOfLE (hWV i)) hcov y hcompat
  refine ⟨g, fun W' h1 h2 h3 ↦ sub_eq_zero.mp (eq_zero_of_locally_zero _ fun x hx ↦ ?_)⟩
  obtain ⟨i, hxi⟩ := Opens.mem_iSup.mp (hcov (h1 hx))
  refine ⟨W' ⊓ W i, inf_le_left, ⟨hx, hxi⟩, ?_⟩
  have eg : F.presheaf.map (homOfLE (inf_le_left : W' ⊓ W i ≤ W')).op
        (F.presheaf.map (homOfLE h1).op g)
      = F.presheaf.map (homOfLE (inf_le_right : W' ⊓ W i ≤ W i)).op (y i) := by
    rw [res_res F h1 inf_le_left g, ← hg i]
    exact (res_res F (hWV i) inf_le_right g).symm
  have ea := map_smul_map_map (F := F) (inf_le_left : W' ⊓ W i ≤ W') h3 h2
    (inf_le_left.trans h3) (inf_le_left.trans h2) a s
  rw [map_sub, sub_eq_zero, eg, ea]
  exact hy i (W' ⊓ W i) inf_le_right (le_trans inf_le_left h2) (le_trans inf_le_left h3)

/-- **Every section of `Iᴺ` has a value**, once the exponent `N` works on a finite affine cover:
the affine opens contained in a member of the cover form a basis, on each of them the
restriction of the section lies in a power of the ideal admitting values, and the local values
glue. -/
theorem exists_isValue_of_mem_idealPow [F.IsQuasicoherent]
    (hFT : ∀ V : X.affineOpens, (I.ideal V).FG) (hTF : NoIdealTorsion I F)
    (s : Γ(F, (I.support.compl : X.Opens))) {N : ℕ} {c : Set X.affineOpens}
    (hcov : (Set.univ : Set X) = ⋃ i ∈ c, ((i : X.affineOpens) : Set X))
    (hmem : ∀ W ∈ c, (I.ideal W ^ N : Ideal Γ(X, W.1)) ≤ valueIdeal s W.1)
    (V : X.Opens) (t : Γ(idealPow I N, V)) :
    ∃ y : Γ(F, V), IsValue s (t.1 : Γ(X, V)) y := by
  classical
  have hWV : ∀ i : {W : X.Opens // W ≤ V ∧ IsAffineOpen W ∧
      ∃ W' ∈ c, W ≤ (W' : X.affineOpens).1}, (i : X.Opens) ≤ V := fun i ↦ i.2.1
  have hcovι : V ≤ ⨆ i : {W : X.Opens // W ≤ V ∧ IsAffineOpen W ∧
      ∃ W' ∈ c, W ≤ (W' : X.affineOpens).1}, (i : X.Opens) := by
    intro x hx
    obtain ⟨W, hWc, hxW⟩ : ∃ W ∈ c, x ∈ (W : X.affineOpens).1 := by
      have hmem' : x ∈ ⋃ i ∈ c, ((i : X.affineOpens) : Set X) := hcov ▸ Set.mem_univ x
      simpa using hmem'
    obtain ⟨-, ⟨V', hV'aff, rfl⟩, hxV', hV'sub⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open
        (show x ∈ ((V ⊓ (W : X.affineOpens).1 : X.Opens) : Set X) from ⟨hx, hxW⟩)
        (V ⊓ (W : X.affineOpens).1).isOpen
    exact Opens.mem_iSup.mpr
      ⟨⟨V', fun z hz ↦ (hV'sub hz).1, hV'aff, W, hWc, fun z hz ↦ (hV'sub hz).2⟩, hxV'⟩
  refine exists_isValue_of_iSup hFT hTF s _ _ hWV hcovι fun i ↦ ?_
  obtain ⟨hiV, hiaff, W, hWc, hiW⟩ := i.2
  have hmemi : ((((idealPow I N).presheaf.map (homOfLE hiV).op t) : _).1 : Γ(X, (i : X.Opens)))
      ∈ (I.ideal ⟨(i : X.Opens), hiaff⟩ ^ N : Ideal Γ(X, (i : X.Opens))) :=
    le_of_eq (obj_idealPow_affineOpen I N ⟨(i : X.Opens), hiaff⟩)
      ((idealPow I N).presheaf.map (homOfLE hiV).op t).2
  obtain ⟨y, hy⟩ := pow_le_valueIdeal_of_le s (V := ⟨(i : X.Opens), hiaff⟩) (W := W) hiW
    (hmem W hWc) hmemi
  exact ⟨y, hy.ofRestrictScalar hiV⟩

/-! ### The morphism `Iᴺ ⟶ F` and surjectivity -/

/-- A morphism of `𝒪_X`-modules built from a natural family of linear maps on sections.  The
`PresheafOfModules.homMk` of Mathlib asks instead for a morphism of the underlying abelian
presheaves, which is not the shape produced here. -/
noncomputable def homOfSections (M N : X.Modules)
    (f : ∀ V : X.Opens, Γ(M, V) →ₗ[Γ(X, V)] Γ(N, V))
    (hnat : ∀ (V W : X.Opens) (h : W ≤ V) (x : Γ(M, V)),
      N.presheaf.map (homOfLE h).op (f V x) = f W (M.presheaf.map (homOfLE h).op x)) :
    M ⟶ N :=
  ⟨{  app := fun V ↦ ModuleCat.ofHom (f V.unop)
      naturality := fun {V W} g ↦ by
        ext x
        exact (hnat V.unop W.unop g.unop.le x).symm }⟩

/-- On sections over `V`, `homOfSections M N f hnat` is the linear map `f V`. -/
@[simp] theorem homOfSections_app (M N : X.Modules)
    (f : ∀ V : X.Opens, Γ(M, V) →ₗ[Γ(X, V)] Γ(N, V))
    (hnat : ∀ (V W : X.Opens) (h : W ≤ V) (x : Γ(M, V)),
      N.presheaf.map (homOfLE h).op (f V x) = f W (M.presheaf.map (homOfLE h).op x))
    (V : X.Opens) (x : Γ(M, V)) :
    (homOfSections M N f hnat).app V x = f V x := rfl

/-- **The morphism recovering `s`.** Given an exponent `N` for which every section of `Iᴺ` has a
value, the values assemble into a morphism `Iᴺ ⟶ F`; linearity and naturality are forced by the
uniqueness of values. -/
noncomputable def valueHom [F.IsQuasicoherent] (hFT : ∀ V : X.affineOpens, (I.ideal V).FG)
    (hTF : NoIdealTorsion I F) (s : Γ(F, (I.support.compl : X.Opens))) (N : ℕ)
    (hex : ∀ (V : X.Opens) (t : Γ(idealPow I N, V)),
      ∃ y : Γ(F, V), IsValue s (t.1 : Γ(X, V)) y) :
    idealPow I N ⟶ F :=
  homOfSections _ _
    (fun V ↦
      { toFun := fun t ↦ (hex V t).choose
        map_add' := fun t₁ t₂ ↦ IsValue.unique hFT hTF le_rfl (hex V (t₁ + t₂)).choose_spec
          ((hex V t₁).choose_spec.add (hex V t₂).choose_spec)
        map_smul' := fun r t ↦ by
          refine IsValue.unique hFT hTF le_rfl (hex V (r • t)).choose_spec ?_
          exact (hex V t).choose_spec.smul r })
    (fun V W h t ↦ IsValue.unique hFT hTF (le_refl W)
      (((hex V t).choose_spec.res h).restrictScalar h)
      ((hex W ((idealPow I N).presheaf.map (homOfLE h).op t)).choose_spec))

/-- The image under `valueHom` of a section `t` of `Iᴺ` over `V` is a value of `s` at `t`: it is
the value chosen in the definition. -/
theorem isValue_valueHom_app [F.IsQuasicoherent] (hFT : ∀ V : X.affineOpens, (I.ideal V).FG)
    (hTF : NoIdealTorsion I F) (s : Γ(F, (I.support.compl : X.Opens))) (N : ℕ)
    (hex : ∀ (V : X.Opens) (t : Γ(idealPow I N, V)),
      ∃ y : Γ(F, V), IsValue s (t.1 : Γ(X, V)) y)
    (V : X.Opens) (t : Γ(idealPow I N, V)) :
    IsValue s (t.1 : Γ(X, V)) ((valueHom hFT hTF s N hex).app V t) :=
  (hex V t).choose_spec

/-- The morphism `valueHom` sends the unit section of `Iᴺ` over `X \ V(I)` back to `s`. -/
theorem valueHom_app_oneSection [F.IsQuasicoherent]
    (hFT : ∀ V : X.affineOpens, (I.ideal V).FG) (hTF : NoIdealTorsion I F)
    (s : Γ(F, (I.support.compl : X.Opens))) (N : ℕ)
    (hex : ∀ (V : X.Opens) (t : Γ(idealPow I N, V)),
      ∃ y : Γ(F, V), IsValue s (t.1 : Γ(X, V)) y) :
    (valueHom hFT hTF s N hex).app (I.support.compl : X.Opens) (oneSection I N) = s := by
  have h := isValue_valueHom_app hFT hTF s N hex (I.support.compl : X.Opens) (oneSection I N)
    (I.support.compl : X.Opens) (le_refl _) (le_refl _) (le_refl _)
  rw [res_self, res_self, val_oneSection, map_one, one_smul] at h
  exact h

/-- **Surjectivity in existence form.** For `X` quasi-compact, `I` of finite type and `F`
quasi-coherent with no `I`-power torsion, every section of `F` over `X \ V(I)` is `φ(1)` for
some `φ : Iⁿ ⟶ F`.

This is the shape that the global-sections clause of [Stacks, Tag 01YB] consumes. -/
theorem exists_hom_idealPow_app_oneSection_eq [CompactSpace X] (I : X.IdealSheafData)
    (hFT : ∀ V : X.affineOpens, (I.ideal V).FG) (F : X.Modules) [F.IsQuasicoherent]
    (hTF : NoIdealTorsion I F) (s : Γ(F, (I.support.compl : X.Opens))) :
    ∃ (n : ℕ) (φ : idealPow I n ⟶ F),
      φ.app (I.support.compl : X.Opens) (oneSection I n) = s := by
  obtain ⟨N, c, hcov, hmem⟩ := exists_forall_pow_le_valueIdeal hFT s
  exact ⟨N, valueHom hFT hTF s N (exists_isValue_of_mem_idealPow hFT hTF s hcov hmem),
    valueHom_app_oneSection hFT hTF s N _⟩

/-- **Stacks Project, Tag 01PQ (`surjective`), the case `F_N = 0`.** Let `X` be a quasi-compact
scheme, let `I` be a quasi-coherent sheaf of ideals of finite type and let `F` be a
quasi-coherent `𝒪_X`-module with **no `I`-power torsion**, that is, with
`F_N = 0` for every `N`.  Then the canonical map
`colim_n Hom_{𝒪_X}(Iⁿ, F) → Γ(X \ V(I), F)` is surjective.

Together with `canonicalMapToSections_injective` this is the second assertion of Tag 01PQ in the
case `F_N = 0`, where `F/F_N = F`; the general assertion, which needs the quotient sheaves
`F/F_N`, is
`Stacks.AlgebraicGeometry.IdealPowerColimit.canonicalMapToSectionsQuotient_bijective` of
`StacksFrontier/AlgebraicGeometry/Coherent/HomColimit/QuotientSurjectivity.lean`.  Note that
quasi-separatedness of `X` is not needed for the torsion-free case proved here: the source
glues the local morphisms over a finite cover of the pairwise intersections, whereas here the
local sections to be glued are *unique*, by the absence of torsion, so no comparison over the
intersections is required. -/
@[stacks 01PQ "surjective (F_n = 0)"]
theorem canonicalMapToSections_surjective [CompactSpace X] (I : X.IdealSheafData)
    (hFT : ∀ V : X.affineOpens, (I.ideal V).FG) (F : X.Modules) [F.IsQuasicoherent]
    (hTF : NoIdealTorsion I F) :
    Function.Surjective (canonicalMapToSections I F) := fun s ↦ by
  obtain ⟨n, φ, hφ⟩ := exists_hom_idealPow_app_oneSection_eq I hFT F hTF s
  exact ⟨Limits.colimit.ι (idealPowHomSystem I F) n φ,
    (canonicalMapToSections_ι I F n φ).trans hφ⟩

/-- **Stacks Project, Tag 01PQ, second assertion in the case `F_N = 0`.** The canonical map
`colim_n Hom_{𝒪_X}(Iⁿ, F) → Γ(X \ V(I), F)` is bijective for a quasi-coherent `F` without
`I`-power torsion on a quasi-compact scheme. -/
theorem canonicalMapToSections_bijective [CompactSpace X] (I : X.IdealSheafData)
    (hFT : ∀ V : X.affineOpens, (I.ideal V).FG) (F : X.Modules) [F.IsQuasicoherent]
    (hTF : NoIdealTorsion I F) :
    Function.Bijective (canonicalMapToSections I F) :=
  ⟨canonicalMapToSections_injective I hFT F, canonicalMapToSections_surjective I hFT F hTF⟩

/-! ### The hypothesis in the form of the ideal-power annihilator -/

/-- **`F_N = 0` implies no `I`-power torsion.**  If the subsheaf
`AlgebraicGeometry.idealPowerAnnihilator` of sections annihilated by `Iᴺ` has zero sections over
every affine open, for every `N`, then `F` satisfies `NoIdealTorsion I F`.  This is the
hypothesis as [Stacks, Tag 01YB] produces it for `F' = Iᵐ F`, through
`exists_idealPow_smul_inf_idealPowerAnnihilator_eq_bot`. -/
theorem noIdealTorsion_of_idealPowerAnnihilator_obj_eq_bot (I : X.IdealSheafData)
    (F : X.Modules)
    (h : ∀ (N : ℕ) (V : X.affineOpens),
      (idealPowerAnnihilator I.unitSubmodule F N).toSubmodule.obj (op V.1)
        = (⊥ : Submodule Γ(X, V.1) Γ(F, V.1))) :
    NoIdealTorsion I F := by
  intro N V y hy
  have hmem : y ∈ (idealPowerAnnihilator I.unitSubmodule F N).toSubmodule.obj (op V.1) :=
    (mem_idealPowerAnnihilator_affineOpen I F N V y).mpr hy
  rw [h N V] at hmem
  exact Submodule.mem_bot _ |>.mp hmem

end Stacks.AlgebraicGeometry.IdealPowerColimit

end
