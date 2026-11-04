module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.Algebra.Homology.StrictlyPerfectRestriction
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjects
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedTensorRestrictScalars
public import StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedTwoFactorWitness
public import StacksFrontier.RingTheory.LocalRing.IdempotentElem

/-!
# At a point with local stalk, one factor of a product decomposition survives

Let `(X, 𝒪_X)` be a ringed space carrying a locally finite direct product decomposition
`𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` of its structure sheaf — the datum
`Stacks.Cohomology.InvertibleDerived.ProductDecomposition` of Stacks 0FPG — and let `x` be a
point of `X` whose stalk `𝒪_{X, x}` is a local ring. Then `x` has a neighbourhood on which
**exactly one** factor of the decomposition is nonzero.

This is the input the source of Stacks 0FPG uses for the equivalence of clauses (2) and (3) of
that tag, clause (3) being stated only under the hypothesis that every stalk is a local ring.
It is a step of the proof of an implication, not a clause of the tag, so nothing here carries a
`@[stacks]` attribute.

## Main definitions

* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.compHom`: the `n`-th component of a
  section of `𝒪_X`, as a homomorphism of the rings of sections. It is the `n`-th projection of
  `ProductDecomposition.productPresentation`, the decomposition read as a
  `Stacks.SheafOfModules.RingSheafProductFactor.ProductPresentation`, evaluated over an open set.
* `Stacks.Cohomology.InvertibleDerived.ProductDecomposition.idemSection`: the section `e_n` of
  `𝒪_X` over an open set whose `n`-th component is `1` and whose other components vanish.

## Main results

* `...ProductDecomposition.isIdempotentElem_idemSection`,
  `...ProductDecomposition.idemSection_mul_of_ne`,
  `...ProductDecomposition.sum_idemSection`: the `e_n` are idempotent, pairwise orthogonal, and
  sum to `1` over any open set outside of which only finitely many factors have sections.
* `...ProductDecomposition.subsingleton_factor_of_idemSection_eq_zero`: conversely, a vanishing
  `e_n` forces the `n`-th factor to have no sections.
* `...ProductDecomposition.exists_nhd_unique_factor`: **the conclusion.** If `𝒪_{X, x}` is a
  local ring then some neighbourhood `V` of `x` and some degree `n₀` have
  `Subsingleton (𝒪_n(V))` for every `n ≠ n₀`.
* `...ProductDecomposition.bijective_compHom_of_subsingleton` and
  `...ProductDecomposition.isIso_compHom_of_subsingleton`: on such a `V`, and on every open set
  below it, the structure sheaf **is** the surviving factor — the component map
  `𝒪_X(W) ⟶ 𝒪_{n₀}(W)` is bijective. This is the input any transport of invertibility from the
  factor to `𝒪_X|_V` runs through.
* `...ProductDecomposition.isIso_over_factorProjection`: the module-level form — on the slice
  site over such a `V` the morphism `RingSheafProductFactor.factorProjection` is an isomorphism,
  so the `n₀`-th factor module is the structure sheaf there.
* `exists_cover_restrict_iso_single`: with every stalk a local ring, the complex of clause (2)
  restricts, on a covering of `X`, to one module placed in one degree. This is clause (3) of the
  tag minus its invertibility assertion.
* `not_exists_nhd_unique_factor_witness`: the local-ring hypothesis is **not** droppable —
  `TwoFactorWitness.witnessDecomposition`, a decomposition with two nonzero factors over a
  one-point space, refutes the conclusion without it.

## Implementation notes

The argument does **not** need the stalk of a locally finite product of sheaves of rings to be
the product of the stalks, which is what the module docstring of
`StacksFrontier.Topology.Sheaves.Cohomology.InvertibleDerivedObjects` records as the obligation of
the equivalence `(2) ⟺ (3)`. Only the idempotents are transported to the stalk: the finitely
many `e_n` surviving near `x` are orthogonal idempotents summing to `1`, so in a local ring one
of them is `1` and the rest are `0` — and an idempotent whose germ vanishes already vanishes on
a neighbourhood, where its own factor then has no sections. The product-of-stalks statement is
false without local finiteness (Stacks 007D) and is not needed with it.

A section of the structure sheaf of a ringed space has two spellings, `X.presheaf.obj U` and
`(SheafedSpace.sheaf X).obj.obj U`, which are definitionally equal but do not unify at the
`implicit` transparency that `rw` works at. `compHom` and `idemSection` fix the first spelling
once, as `TwoFactorWitness.skyscraperRingSheaf` does for its own crossing, and every statement
below stays inside it; the crossings to the product-presentation API are all discharged in term
mode.

The idempotents of a local stalk ring are `0` and `1` by
`IsLocalRing.isIdempotentElem_eq_zero_or_one` (`StacksFrontier.RingTheory.LocalRing.IdempotentElem`).

## References

* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG)
* [Stacks Project, Tag 007D](https://stacks.math.columbia.edu/tag/007D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace
open Stacks.SheafOfModules.RingSheafProductFactor StrictlyPerfect

universe u

namespace Stacks.Cohomology.InvertibleDerived

namespace ProductDecomposition

variable {X : RingedSpace.{u, u}}

/-- **The `n`-th component of a section of the structure sheaf**, as a homomorphism of rings of
sections: the `n`-th projection of the decomposition, evaluated over an open set. -/
public def compHom (D : ProductDecomposition X) (n : ℤ) (U : (Opens X.carrier)ᵒᵖ) :
    X.presheaf.obj U ⟶ (D.factor n).obj.obj U :=
  (D.productPresentation.π n).hom.app U

/-- A section of `𝒪_X` is determined by its components. -/
public theorem comp_injective (D : ProductDecomposition X) {U : (Opens X.carrier)ᵒᵖ}
    {s s' : X.presheaf.obj U} (h : ∀ n : ℤ, D.compHom n U s = D.compHom n U s') : s = s' :=
  D.productPresentation.injective h

/-- Taking components commutes with restriction. -/
public theorem comp_map (D : ProductDecomposition X) (n : ℤ) {U V : (Opens X.carrier)ᵒᵖ}
    (f : U ⟶ V) (s : X.presheaf.obj U) :
    D.compHom n V (X.presheaf.map f s) = (D.factor n).obj.map f (D.compHom n U s) :=
  D.productPresentation.app_map n f s

/-- Triviality of the sections of a factor propagates to smaller open sets. -/
private theorem subsingleton_factor_of_le (D : ProductDecomposition X) (n : ℤ)
    {U V : Opens X.carrier} (hVU : V ≤ U)
    (h : Subsingleton ((D.factor n).obj.obj (op U))) :
    Subsingleton ((D.factor n).obj.obj (op V)) := by
  have h1 : Subsingleton
      ((Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)).obj.obj (op U)) := h
  exact Stacks.SheafOfModules.subsingleton_of_subsingleton_of_le (homOfLE hVU) h1

/-- **The idempotent cutting out the `n`-th factor.** The section of `𝒪_X` over `U` whose `n`-th
component is `1` and whose every other component is `0`. -/
public def idemSection (D : ProductDecomposition X) (n : ℤ) (U : (Opens X.carrier)ᵒᵖ) :
    X.presheaf.obj U :=
  D.productPresentation.inclSection n U 1

/-- The `n`-th component of `e_n` is `1`. -/
public theorem comp_idemSection_self (D : ProductDecomposition X) (n : ℤ)
    (U : (Opens X.carrier)ᵒᵖ) :
    D.compHom n U (D.idemSection n U) = 1 :=
  D.productPresentation.app_inclSection_self n U 1

/-- The `m`-th component of `e_n` vanishes for `m ≠ n`. -/
public theorem comp_idemSection_of_ne (D : ProductDecomposition X) {n m : ℤ} (hmn : m ≠ n)
    (U : (Opens X.carrier)ᵒᵖ) :
    D.compHom m U (D.idemSection n U) = 0 :=
  D.productPresentation.app_inclSection_of_ne hmn U 1

/-- `e_n` is idempotent: in every component it is `1` or `0`. -/
public theorem isIdempotentElem_idemSection (D : ProductDecomposition X) (n : ℤ)
    (U : (Opens X.carrier)ᵒᵖ) : IsIdempotentElem (D.idemSection n U) := by
  refine D.comp_injective fun m => ?_
  rw [map_mul]
  by_cases h : m = n
  · subst h
    rw [D.comp_idemSection_self, one_mul]
  · rw [D.comp_idemSection_of_ne h, mul_zero]

/-- The idempotents of two distinct degrees are orthogonal: in every component one of the two
factors is `0`. -/
public theorem idemSection_mul_of_ne (D : ProductDecomposition X) {n m : ℤ} (hnm : n ≠ m)
    (U : (Opens X.carrier)ᵒᵖ) :
    D.idemSection n U * D.idemSection m U = 0 := by
  refine D.comp_injective fun k => ?_
  rw [map_mul, map_zero]
  by_cases h : k = n
  · subst h
    rw [D.comp_idemSection_of_ne hnm, mul_zero]
  · rw [D.comp_idemSection_of_ne h, zero_mul]

/-- **The idempotents of the surviving factors sum to `1`.** If every factor outside a finite set
`S` has no sections over `U`, then `∑_{n ∈ S} e_n = 1` in `𝒪_X(U)`: for `m ∈ S` the `m`-th
component of the sum is `1`, and for `m ∉ S` the `m`-th factor is trivial. -/
public theorem sum_idemSection (D : ProductDecomposition X) (U : (Opens X.carrier)ᵒᵖ)
    (S : Finset ℤ) (hS : ∀ n ∉ S, Subsingleton ((D.factor n).obj.obj U)) :
    ∑ n ∈ S, D.idemSection n U = 1 := by
  refine D.comp_injective fun m => ?_
  rw [map_sum, map_one]
  by_cases hm : m ∈ S
  · rw [Finset.sum_eq_single_of_mem m hm
      fun b _ hbm => D.comp_idemSection_of_ne (Ne.symm hbm) U]
    exact D.comp_idemSection_self m U
  · exact (hS m hm).elim _ _

/-- A degree whose idempotent vanishes over `U` has no sections over `U`: the `n`-th component of
`e_n` is `1`, so `1 = 0` in the factor. -/
public theorem subsingleton_factor_of_idemSection_eq_zero (D : ProductDecomposition X) (n : ℤ)
    (U : (Opens X.carrier)ᵒᵖ) (h : D.idemSection n U = 0) :
    Subsingleton ((D.factor n).obj.obj U) := by
  have h1 : (1 : (D.factor n).obj.obj U) = 0 := by
    rw [← D.comp_idemSection_self n U, h, map_zero]
  exact subsingleton_of_forall_eq 0 fun a => by rw [← mul_one a, h1, mul_zero]

/-- The idempotents are compatible with restriction: `e_n` over `U` restricts to `e_n` over any
smaller open set. -/
public theorem map_idemSection (D : ProductDecomposition X) (n : ℤ)
    {U V : (Opens X.carrier)ᵒᵖ} (f : U ⟶ V) :
    X.presheaf.map f (D.idemSection n U) = D.idemSection n V := by
  have h := D.productPresentation.map_inclSection n f (1 : (D.factor n).obj.obj U)
  rwa [map_one] at h

/-- A degree whose idempotent has vanishing germ at `x` has no sections on some neighbourhood
of `x`. -/
private theorem exists_nhd_subsingleton_factor_of_germ_eq_zero (D : ProductDecomposition X)
    {U : Opens X.carrier} {x : X.carrier} (hxU : x ∈ U) (n : ℤ)
    (h : X.presheaf.germ U x hxU (D.idemSection n (op U)) = 0) :
    ∃ W : Opens X.carrier, x ∈ W ∧ W ≤ U ∧ Subsingleton ((D.factor n).obj.obj (op W)) := by
  obtain ⟨W, hxW, iU, _, hW⟩ := X.presheaf.germ_eq x hxU hxU (D.idemSection n (op U))
    (0 : X.presheaf.obj (op U)) (by rwa [map_zero])
  exact ⟨W, hxW, leOfHom iU, D.subsingleton_factor_of_idemSection_eq_zero n (op W)
    (by rw [← D.map_idemSection n iU.op, hW, map_zero])⟩

/-- **At a point with local stalk, one factor survives.** Let `D` be a locally finite direct
product decomposition `𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` of the structure sheaf of a ringed space and let `x`
be a point of `X` whose stalk is a local ring. Then there are a neighbourhood `V` of `x` and a
degree `n₀` such that every factor other than the `n₀`-th has no sections over `V`.

Near `x` only finitely many factors have sections, and their idempotents `e_n` are orthogonal and
sum to `1`; in the local ring `𝒪_{X, x}` each germ is `0` or `1`, not all of them are `0`, and
two of them cannot both be `1`, so exactly one germ is `1`. The germs that vanish do so already
on a neighbourhood, and there the corresponding factor has no sections. -/
public theorem exists_nhd_unique_factor (D : ProductDecomposition X) (x : X.carrier)
    (hx : IsLocalRing (X.presheaf.stalk x)) :
    ∃ (V : Opens X.carrier) (n₀ : ℤ), x ∈ V ∧
      ∀ n, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op V)) := by
  classical
  obtain ⟨U, hxU, hfin⟩ := D.locallyFinite x
  set S : Finset ℤ := hfin.toFinset
  have hout : ∀ n ∉ S, Subsingleton ((D.factor n).obj.obj (op U)) := fun n hn =>
    by_contra fun hcon => hn (hfin.mem_toFinset.mpr hcon)
  -- the germs of the idempotents are idempotent and sum to one
  have hidem : ∀ n : ℤ,
      IsIdempotentElem (X.presheaf.germ U x hxU (D.idemSection n (op U))) := by
    intro n
    have h := D.isIdempotentElem_idemSection n (op U)
    unfold IsIdempotentElem at h ⊢
    rw [← map_mul, h]
  have hsum : ∑ n ∈ S, X.presheaf.germ U x hxU (D.idemSection n (op U)) = 1 := by
    rw [← map_sum, D.sum_idemSection (op U) S hout, map_one]
  -- in a local ring each germ is zero or one, and they are not all zero
  have hexists : ∃ n₀ ∈ S, X.presheaf.germ U x hxU (D.idemSection n₀ (op U)) = 1 := by
    by_contra hcon
    simp only [not_exists, not_and] at hcon
    rw [Finset.sum_congr rfl fun n hn =>
      (IsLocalRing.isIdempotentElem_eq_zero_or_one (hidem n)).resolve_right (hcon n hn),
      Finset.sum_const_zero] at hsum
    exact one_ne_zero hsum.symm
  obtain ⟨n₀, hn₀S, hn₀⟩ := hexists
  -- every other germ is zero, by orthogonality with the one that is one, so the factor loses
  -- its sections on a neighbourhood
  have hshrink : ∀ n ∈ S, n ≠ n₀ → ∃ W : Opens X.carrier, x ∈ W ∧ W ≤ U ∧
      Subsingleton ((D.factor n).obj.obj (op W)) := by
    intro n _ hne
    refine D.exists_nhd_subsingleton_factor_of_germ_eq_zero hxU n ?_
    have h0 : X.presheaf.germ U x hxU (D.idemSection n (op U)) *
        X.presheaf.germ U x hxU (D.idemSection n₀ (op U)) = 0 := by
      rw [← map_mul, D.idemSection_mul_of_ne hne (op U), map_zero]
    rwa [hn₀, mul_one] at h0
  choose! W hxW hWU hWsub using hshrink
  -- intersecting the finitely many neighbourhoods leaves only the `n₀`-th factor
  have hxV : x ∈ (S.erase n₀).inf W ⊓ U :=
    ⟨mem_finsetInf fun n hn =>
      hxW n (Finset.mem_of_mem_erase hn) (Finset.ne_of_mem_erase hn), hxU⟩
  refine ⟨(S.erase n₀).inf W ⊓ U, n₀, hxV, fun n hn => ?_⟩
  by_cases hnS : n ∈ S
  · exact D.subsingleton_factor_of_le n
      (le_trans inf_le_left (Finset.inf_le (Finset.mem_erase.mpr ⟨hn, hnS⟩)))
      (hWsub n hnS hn)
  · exact D.subsingleton_factor_of_le n inf_le_right (hout n hnS)

/-- **Where only one factor survives, the structure sheaf *is* that factor.** If every factor
other than the `n₀`-th has no sections over `V`, then over every open set `W ≤ V` the `n₀`-th
component map `𝒪_X(W) ⟶ 𝒪_{n₀}(W)` is bijective: it is injective because the other components
of a section of `𝒪_X(W)` live in trivial rings, and surjective because
`ProductPresentation.inclSection` names a preimage. -/
public theorem bijective_compHom_of_subsingleton (D : ProductDecomposition X) {n₀ : ℤ}
    {V : Opens X.carrier} (hsub : ∀ n, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op V)))
    {W : Opens X.carrier} (hWV : W ≤ V) :
    Function.Bijective fun s : X.presheaf.obj (op W) => D.compHom n₀ (op W) s := by
  refine ⟨fun s s' h => D.comp_injective fun m => ?_, fun a =>
    ⟨D.productPresentation.inclSection n₀ (op W) a,
      D.productPresentation.app_inclSection_self n₀ (op W) a⟩⟩
  rcases eq_or_ne m n₀ with rfl | hm
  · exact h
  · exact (D.subsingleton_factor_of_le m hWV (hsub m hm)).elim _ _

/-- The `n₀`-th component map is an isomorphism of the rings of sections over every open set on
which the other factors have no sections. -/
public theorem isIso_compHom_of_subsingleton (D : ProductDecomposition X) {n₀ : ℤ}
    {V : Opens X.carrier} (hsub : ∀ n, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op V)))
    {W : Opens X.carrier} (hWV : W ≤ V) :
    IsIso (D.compHom n₀ (op W)) :=
  (ConcreteCategory.isIso_iff_bijective _).mpr (D.bijective_compHom_of_subsingleton hsub hWV)

/-- **On an open set where only the `n₀`-th factor survives, that factor *is* the structure
sheaf as a module.** The morphism of sheaves of `𝒪_X`-modules
`Stacks.SheafOfModules.RingSheafProductFactor.factorProjection`, whose sections map is the
`n₀`-th component map, becomes an isomorphism after restriction to the slice site over `V`: over
every object `W ⟶ V` of that site it is bijective, by
`bijective_compHom_of_subsingleton`.

This is the geometric input of the invertibility half of clause (3) of Stacks 0FPG: it is what
carries a local trivialization of `ℋ^{n₀}` over `𝒪_{n₀}` to one over `𝒪_X|_V`, after which
`Stacks.SheafOfModules.isInvertible_of_isLocallyTrivial` applies. A step of a proof, not a
clause. -/
public theorem isIso_over_factorProjection (D : ProductDecomposition X) {n₀ : ℤ}
    {V : Opens X.carrier}
    (hsub : ∀ n, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op V))) :
    IsIso ((Stacks.SheafOfModules.RingSheafProductFactor.factorProjection
      D.productPresentation n₀).over V) :=
  Stacks.SheafOfModules.isIso_of_bijective_app _ fun U =>
    D.bijective_compHom_of_subsingleton hsub (leOfHom U.unop.hom)

end ProductDecomposition

/-! ### The complex of clause (2) is locally a module in a single degree -/

/-- **Clause (2) puts the complex `⨁ ℋ^n[-n]` in a single degree, locally, when the stalks are
local rings.** Let `𝒪_X = ∏_{n ∈ ℤ} 𝒪_n` be a locally finite direct product decomposition of the
structure sheaf of a ringed space whose stalks are local rings, and let `ℋ^n` be an `𝒪_n`-module
for each `n`. Then `X` is covered by open sets `V` on which the complex with `ℋ^n` in degree `n`
and zero differentials — the complex representing `⨁ ℋ^n[-n]` — restricts to the single complex
`ℋ^{n₀}` in one degree `n₀`.

On `V` every factor other than the `n₀`-th has no sections
(`ProductDecomposition.exists_nhd_unique_factor`), so every term of the restricted complex
other than the `n₀`-th is a zero module (`isZero_restrict_toOXMod`), and a cochain complex
concentrated in one degree is the single complex there.

This is the part of clause (3) of Stacks 0FPG which does not mention invertibility: it supplies
the covering, the degree, and the identification of the restricted complex with a module placed
in that degree. What clause (3) asks beyond it is that the module be an invertible
`𝒪_{V}`-module. A step of the proof of an implication of the tag, not a clause, so no
`@[stacks]` attribute. -/
public theorem nonempty_iso_single_restrict_of_subsingleton {X : RingedSpace.{u, u}}
    (D : ProductDecomposition X)
    (H : ∀ n : ℤ, SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    {n₀ : ℤ} {V : Opens X.carrier}
    (hsub : ∀ n, n ≠ n₀ → Subsingleton ((D.factor n).obj.obj (op V))) :
    Nonempty (((restrictModules X V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (CochainComplex.zeroDifferentialComplex fun m => (D.toOXMod m).obj (H m)) ≅
      (CochainComplex.singleFunctor _ n₀).obj
        ((restrictModules X V).obj ((D.toOXMod n₀).obj (H n₀)))) := by
  set K := ((restrictModules X V).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (CochainComplex.zeroDifferentialComplex fun m => (D.toOXMod m).obj (H m))
  have hzero : ∀ i : ℤ, i ≠ n₀ → IsZero (K.X i) := fun i hi =>
    isZero_restrict_toOXMod D i (H i) (hsub i hi) (le_refl V)
  have : CochainComplex.IsStrictlyGE K n₀ :=
    (CochainComplex.isStrictlyGE_iff K n₀).mpr fun i hi => hzero i (by omega)
  have : CochainComplex.IsStrictlyLE K n₀ :=
    (CochainComplex.isStrictlyLE_iff K n₀).mpr fun i hi => hzero i (by omega)
  obtain ⟨L, ⟨e⟩⟩ := CochainComplex.exists_iso_single K n₀
  refine ⟨e ≪≫ (CochainComplex.singleFunctor _ n₀).mapIso ?_⟩
  exact (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) n₀ L).symm ≪≫
    (HomologicalComplex.eval _ _ n₀).mapIso e.symm

/-- **Clause (2) puts the complex `⨁ ℋ^n[-n]` in a single degree on a covering of `X`.** This is
`nonempty_iso_single_restrict_of_subsingleton` at the neighbourhoods
`ProductDecomposition.exists_nhd_unique_factor` produces. -/
public theorem exists_cover_restrict_iso_single {X : RingedSpace.{u, u}}
    (D : ProductDecomposition X)
    (H : ∀ n : ℤ, SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (hloc : ∀ x : X.carrier, IsLocalRing (X.presheaf.stalk x)) :
    ∃ V : X.carrier → Opens X.carrier, iSup V = ⊤ ∧ ∀ x : X.carrier, ∃ n : ℤ,
      Nonempty (((restrictModules X (V x)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (CochainComplex.zeroDifferentialComplex fun m => (D.toOXMod m).obj (H m)) ≅
        (CochainComplex.singleFunctor _ n).obj
          ((restrictModules X (V x)).obj ((D.toOXMod n).obj (H n)))) := by
  choose V n₀ hxV hsub using fun x : X.carrier => D.exists_nhd_unique_factor x (hloc x)
  exact ⟨V, le_antisymm le_top fun x _ => Opens.mem_iSup.mpr ⟨x, hxV x⟩,
    fun x => ⟨n₀ x, nonempty_iso_single_restrict_of_subsingleton D H (hsub x)⟩⟩

/-! ### The local-ring hypothesis cannot be dropped -/

/-- **Without the local-ring hypothesis `exists_nhd_unique_factor` is false**, not merely
unproved. Over the one-point space with `𝒪_X = ℤ × ℤ` decomposed as `ℤ` in degree `0` and `ℤ`
in degree `1` — `TwoFactorWitness.witnessDecomposition`, which assumes nothing — every open set
containing the point has nonzero sections of *both* factors, so no neighbourhood of the point
leaves only one factor alive. The stalk of that structure sheaf is `ℤ × ℤ`, which is not a local
ring, and this is what the hypothesis excludes. -/
public theorem not_exists_nhd_unique_factor_witness :
    ¬ ∃ (V : Opens (TwoFactorWitness.witnessSpace.{u}).carrier) (n₀ : ℤ),
      PUnit.unit ∈ V ∧ ∀ n, n ≠ n₀ →
        Subsingleton ((TwoFactorWitness.witnessDecomposition.{u}.factor n).obj.obj (op V)) := by
  rintro ⟨V, n₀, hxV, h⟩
  by_cases h0 : n₀ = 0
  · subst h0
    exact TwoFactorWitness.not_subsingleton_factor_one _ _ _ _ hxV (h 1 one_ne_zero)
  · exact TwoFactorWitness.not_subsingleton_factor_zero _ _ _ _ hxV (h 0 (Ne.symm h0))

end Stacks.Cohomology.InvertibleDerived

end
