module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.ExteriorProductDedekind.BaseFundamentalClass

/-!
# Stacks 0FC5: bivariant classes towards a Dedekind base are Chow classes

Let `(S, δ)` be as in Stacks section 42.63 — locally the spectrum of a Dedekind domain, with
`δ = 0` at the closed points and `δ = 1` elsewhere — and let `X` be locally of finite type over
`S`. **Stacks 0FC5** asserts the canonical identification

  `A^p(X ⟶ S) = CH_{1-p}(X)`,   `c ↦ c ∩ [S]₁`,

for every `p ∈ ℤ`, whose inverse is `α ↦ c_α` with `c_α ∩ α' = α × α'`.

## The hypothesis that the components of `S` are curves

The section assumes, through its reference to Example 02QN, that `S` has dimension one: an affine
open `Spec A` with `A` a Noetherian domain *of dimension one*. Read literally, "an open covering by
spectra of Dedekind domains" also allows fields (Algebra, Lemma 034X), and then the statement is
false: for `S = Spec k` the unique point is closed, so `δ = 0` and `[S]₁ = 0`, whereas
`A^0(S ⟶ S)` contains the identity class, which is nonzero because it acts as the identity on
`CH_0(S) = ℤ`; indeed over a field `A^p(X ⟶ S) = CH_{-p}(X)` by Stacks 0FBW (this is
`Stacks.Chow.not_bijective_bivariantChowClassCapBaseFundamentalClass_field`). The hypothesis
`hdim` below — every irreducible component of `S` has dimension one — is the one-dimensionality
the section intends, and it is used exactly where the source uses `δ(η) = 1` at the generic point
of a component.

## Main definitions

* `Stacks.Chow.bivariantChowClassCapBaseFundamentalClass` — the canonical map
  `A^p(X ⟶ S) ⟶ CH_{1-p}(X)`, `c ↦ c ∩ [S]₁`, for the group `A^p(X ⟶ S)` of Stacks 0B76.
* `Stacks.Chow.chowCohomologyDedekindEquiv` — **Stacks 0FC5**, the identification as an
  isomorphism of groups.

## Main results

* `Stacks.Chow.bivariantChowClassCapBaseFundamentalClass_dedekindExteriorClass` — `c_α ∩ [S]₁ = α`.
* `Stacks.Chow.bivariantChowClassCapBaseFundamentalClass_bijective` — **Stacks 0FC5**: the
  canonical map `A^p(X ⟶ S) ⟶ CH_{1-p}(X)`, `c ↦ c ∩ [S]₁`, is bijective.
* `Stacks.Chow.chowCohomologyDedekindEquiv_symm` — the inverse identification is `α ↦ c_α`.

## References

* [Stacks Project, Tag 0FC5](https://stacks.math.columbia.edu/tag/0FC5)
* [Stacks Project, Example 02QN](https://stacks.math.columbia.edu/tag/02QN)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

variable {C : ChowSituation.{u}} {X : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (p : ℤ)

/-- The canonical map `A^p(X ⟶ S) ⟶ CH_{1-p}(X)` of Stacks 0FC5, `c ↦ c ∩ [S]₁`, for the group
`A^p(X ⟶ S)` of Stacks 0B76: the cap product with the fundamental class of the base in degree
one, read on `X` through `X ×_S S ≅ X`. -/
def bivariantChowClassCapBaseFundamentalClass :
    BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p →+ chowGroup C sX (1 - p) :=
  (bivariantCapBaseFundamentalClass C (gysinSystemOfInvertible C) sX p).comp
    BivariantChowClass.addEquivBivariantClass.toAddMonoidHom

/-- The canonical map `c ↦ c ∩ [S]₁` on a bivariant class: the cap product with the fundamental
class of the base in degree one, followed by the identification `X ×_S S ≅ X`. -/
theorem bivariantChowClassCapBaseFundamentalClass_apply
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    bivariantChowClassCapBaseFundamentalClass sX p c =
      basePullbackPushforward C sX (1 - p) (c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C)) :=
  rfl

variable {sX p}

/-- The fundamental classes of two equal structure morphisms are heterogeneously equal. -/
theorem fundamentalChowClass_heq_of_structureMorphism_eq {T : Scheme.{u}} {q q' : T ⟶ C.S}
    [LocallyOfFiniteType q] [LocallyOfFiniteType q'] (h : q = q') (k : ℤ) :
    fundamentalChowClass C q k ≍ fundamentalChowClass C q' k := by
  subst h
  rfl

variable (hC : IsDedekindChowBase C)
  (hdim : ∀ Z : irreducibleComponents C.S, topologicalKrullDim (Z : Set C.S) = 1)

include hdim in
/-- **`c_α ∩ [S]₁ = α`.** The bivariant class `c_α = dedekindExteriorClass hC sX p α` caps the
fundamental class of the base to `α`. -/
theorem bivariantChowClassCapBaseFundamentalClass_dedekindExteriorClass
    (α : chowGroup C sX (1 - p)) :
    bivariantChowClassCapBaseFundamentalClass sX p (dedekindExteriorClass hC sX p α) = α := by
  obtain ⟨a₀, rfl⟩ := QuotientAddGroup.mk'_surjective (rationalEquivalences C sX (1 - p)) α
  rw [bivariantChowClassCapBaseFundamentalClass_apply, dedekindExteriorClass_cap,
    dedekindExteriorCap_apply]
  have hS : chowGroupCongr C (Category.comp_id (𝟙 C.S)) 1 (baseFundamentalChowClass C) =
      QuotientAddGroup.mk' (rationalEquivalences C (𝟙 C.S) 1) (fundamentalCycle C (𝟙 C.S) 1) :=
    eq_of_heq ((chowGroupCongr_heq C _ _ _).trans
      (fundamentalChowClass_heq_of_structureMorphism_eq (Category.comp_id (𝟙 C.S)) 1))
  rw [hS, exteriorProductDedekindChowTensor_tmul_mk, basePullbackPushforward,
    ← chowGroupDegreeEquiv_properChowPushforward_comp C _ _ _ _ (by ring : 1 - p + 1 - 1 = 1 - p)
      (properPushforwardDescends C _ _ _ _ _), properChowPushforward_mk,
    mk_properPushforward_exteriorProductDedekindCycles_fundamentalCycle hC hdim sX (1 - p) a₀]
  exact chowGroupDegreeEquiv_mk_eq_mk_of_val C sX _ _ _ rfl

include hC hdim in
/-- **Bivariant classes towards a Dedekind base are Chow classes.** Let `(S, δ)` be as in Stacks
section 42.63 — locally the spectrum of a Dedekind domain, with `δ = 0` at the closed points and
`δ = 1` elsewhere — every irreducible component of `S` being of dimension one, and let `X` be a
scheme locally of finite type over `S`. For every `p ∈ ℤ` the canonical map
`A^p(X ⟶ S) ⟶ CH_{1-p}(X)`, `c ↦ c ∩ [S]₁`, is bijective. Here `A^p(X ⟶ S)` is the group of
bivariant classes of Stacks 0B76 for the structure morphism of `X`, and `c ∩ [S]₁` is read on `X`
through `X ×_S S ≅ X`. -/
@[stacks 0FC5 "the canonical map A^p(X → S) → CH_{1-p}(X), c ↦ c ∩ [S]₁, is bijective; the \
components of S are curves, as in Example 02QN (for S the spectrum of a field the statement \
fails)"]
theorem bivariantChowClassCapBaseFundamentalClass_bijective :
    Function.Bijective (bivariantChowClassCapBaseFundamentalClass sX p) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun c hc ↦ ?_, fun α ↦
    ⟨dedekindExteriorClass hC sX p α,
      bivariantChowClassCapBaseFundamentalClass_dedekindExteriorClass hC hdim α⟩⟩
  rw [bivariantChowClassCapBaseFundamentalClass_apply, basePullbackPushforward] at hc
  exact c.eq_zero_of_cap_baseFundamentalChowClass_dedekind hC hdim
    (eq_zero_of_properChowPushforward_eq_zero_of_isIso _ _ _ _ _ _ _ hc)

/-- The canonical identification `A^p(X ⟶ S) = CH_{1-p}(X)` over a Dedekind base whose
irreducible components are curves, as an isomorphism of groups: `c ↦ c ∩ [S]₁`. Its inverse
sends `α` to the class `c_α` with `c_α ∩ α' = α × α'` (`chowCohomologyDedekindEquiv_symm`). -/
@[stacks 0FC5 "the canonical identification A^p(X → S) = CH_{1-p}(X) as an isomorphism of \
groups, c ↦ c ∩ [S]₁, with inverse α ↦ c_α; the components of S are curves, as in Example 02QN"]
def chowCohomologyDedekindEquiv (p : ℤ) (hC : IsDedekindChowBase C)
    (hdim : ∀ Z : irreducibleComponents C.S, topologicalKrullDim (Z : Set C.S) = 1) :
    BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p ≃+ chowGroup C sX (1 - p) :=
  AddEquiv.ofBijective _ (bivariantChowClassCapBaseFundamentalClass_bijective hC hdim)

/-- The identification `chowCohomologyDedekindEquiv` sends `c` to `c ∩ [S]₁`, read on `X`
through `X ×_S S ≅ X`. -/
theorem chowCohomologyDedekindEquiv_apply (hC : IsDedekindChowBase C)
    (hdim : ∀ Z : irreducibleComponents C.S, topologicalKrullDim (Z : Set C.S) = 1)
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    chowCohomologyDedekindEquiv p hC hdim c =
      basePullbackPushforward C sX (1 - p) (c.cap (𝟙 C.S) 1 (baseFundamentalChowClass C)) :=
  rfl

/-- The inverse of the identification of Stacks 0FC5 sends `α` to `c_α`. -/
theorem chowCohomologyDedekindEquiv_symm (hC : IsDedekindChowBase C)
    (hdim : ∀ Z : irreducibleComponents C.S, topologicalKrullDim (Z : Set C.S) = 1)
    (α : chowGroup C sX (1 - p)) :
    (chowCohomologyDedekindEquiv p hC hdim).symm α = dedekindExteriorClass hC sX p α :=
  (AddEquiv.symm_apply_eq _).2
    (bivariantChowClassCapBaseFundamentalClass_dedekindExteriorClass hC hdim α).symm

/-- The class corresponding to `α` under Stacks 0FC5 caps by exterior product with `α`:
`c_α ∩ α' = α × α'`. -/
theorem chowCohomologyDedekindEquiv_symm_cap (hC : IsDedekindChowBase C)
    (hdim : ∀ Z : irreducibleComponents C.S, topologicalKrullDim (Z : Set C.S) = 1)
    (α : chowGroup C sX (1 - p)) {T : Scheme.{u}} (g : T ⟶ C.S) [LocallyOfFiniteType g] (k : ℤ)
    (β : chowGroup C (g ≫ 𝟙 C.S) k) :
    ((chowCohomologyDedekindEquiv p hC hdim).symm α).cap g k β =
      chowGroupDegreeEquiv C (pullback.fst sX g ≫ sX) (by ring : 1 - p + k - 1 = k - p)
        (exteriorProductDedekindChowTensor C sX g (1 - p) k hC
          (α ⊗ₜ[ℤ] chowGroupCongr C (Category.comp_id g) k β)) := by
  rw [chowCohomologyDedekindEquiv_symm]
  rfl

/-- Every bivariant class towards the base is the class `c_α` of its cap product
`α = c ∩ [S]₁`. -/
theorem eq_dedekindExteriorClass (hC : IsDedekindChowBase C)
    (hdim : ∀ Z : irreducibleComponents C.S, topologicalKrullDim (Z : Set C.S) = 1)
    (c : BivariantChowClass C sX (𝟙 C.S) sX (Category.comp_id sX) p) :
    c = dedekindExteriorClass hC sX p (bivariantChowClassCapBaseFundamentalClass sX p c) := by
  rw [← chowCohomologyDedekindEquiv_symm hC hdim]
  exact ((chowCohomologyDedekindEquiv p hC hdim).symm_apply_apply c).symm

end Stacks.Chow

end
