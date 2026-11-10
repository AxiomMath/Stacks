module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.LocallyFiniteCoproductIso
public import StacksFrontier.AlgebraicGeometry.Cohomology.CoherentExtension.LocallyNoetherian
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeFiniteFree
public import StacksFrontier.AlgebraicGeometry.HigherRank.Basic
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericFreeNeighbourhood
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.Coproduct
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericIdealPushforward

/-!
# A coherent module is a sum of structure sheaves near a generic point

Let `X` be a locally Noetherian scheme, let `i : Z ⟶ X` be an integral closed subscheme with
generic point `ξ`, and let `𝒢` be a coherent `𝒪_X`-module whose stalk at `i ξ` is annihilated by
the maximal ideal of the local ring there. This file produces a coherent `𝒪_X`-module `M`
together with

`M ⟶ ⨁_{j < r} i_* 𝒪_Z`  and  `M ⟶ 𝒢`,

both isomorphisms over one open neighbourhood of `i ξ`, where `r` is the dimension of the stalk
`𝒢_{i ξ}` over the residue field there.

This is [Stacks, Tag 01YE] **with its Noetherian hypothesis removed**. The source, and
`Stacks.ClosedImmersion.exists_idealCoproduct_pushforward_mono_isIso_near_genericPoint`
following it, takes `M` to be `i_*(ℐ^{⊕ r})` for `ℐ` a power of the ideal sheaf of the closed
complement of the neighbourhood on which `𝒢` is free; that choice needs one exponent valid over
the whole of `Z`, and so needs `Z` quasi-compact. Replacing it by [Stacks, Tag 0FD0] — which
holds over a locally Noetherian scheme, and which hands back an unnamed coherent submodule
rather than a power of an ideal — removes the hypothesis. Nothing is lost: what the dévissage of
a dimension layer reads off `M` is only its two comparison maps and the fact that its support
lies in `Z`, never that it is a coproduct of ideal sheaves.

The monomorphy of `M ⟶ 𝒢` which the source also delivers is *not* claimed here, and is not
needed: a morphism of coherent modules is inverted by the localization at a Serre class of
lower-dimensional modules as soon as it is invertible near every point of the top dimension, and
invertibility near `i ξ` is what the construction gives.

## Main results

* `Stacks.Chow.exists_free_comparison_near_genericPoint` — **[Stacks, Tag 01YE] over a locally
  Noetherian scheme**, in the comparison form described above.

## Implementation notes

The chain is: the annihilator submodule `𝒜 ⊆ 𝒢` of the ideal sheaf of `Z`, which agrees with `𝒢`
near `i ξ` by
`Stacks.ClosedImmersion.exists_coherent_annihilator_submodule_isIso_near_of_isLocallyNoetherian`;
its description as a direct image `i_* 𝒢₀` by [Stacks, Tag 087T]; the freeness of `𝒢₀`, given by
`Stacks.AlgebraicGeometry.IrreducibleDevissage.exists_isIso_restrictFunctor_free_near_genericPoint`
on a neighbourhood `V` of `ξ`; and [Stacks, Tag 0FD0] applied on `Z` to the resulting isomorphism
`(⨁_{j < r} 𝒪_Z)|_V ≅ 𝒢₀|_V`, which extends it to a coherent submodule of `⨁_{j < r} 𝒪_Z`
mapping to `𝒢₀`.

The direct image of the finite coproduct is identified with the coproduct of the direct images
through `Stacks.AlgebraicGeometry.IrreducibleDevissage.pushforwardCoproductConstIso`, which goes
by way of the biproduct: direct image is additive, so it preserves finite biproducts, while it
preserves no infinite colimit.

An isomorphism over an open `V` of `Z` becomes one over `Stacks.ClosedImmersion.pushforwardOpen
i V`, the largest open of `X` with preimage inside `V`, after direct image.

## References

* [Stacks Project, Tag 087T](https://stacks.math.columbia.edu/tag/087T)
* [Stacks Project, Tag 01YE](https://stacks.math.columbia.edu/tag/01YE)
* [Stacks Project, Tag 0FD0](https://stacks.math.columbia.edu/tag/0FD0)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.IrreducibleDevissage (freeCoproductIso isCoherent_free_ulift
  isCoherent_of_iso' exists_isIso_restrictFunctor_free_near_genericPoint
  pushforwardCoproductConstIso)
open Stacks.ClosedImmersion (StalkKilledByMaximalIdeal pushforwardOpen mem_pushforwardOpen
  preimage_pushforwardOpen_le isIso_restrictFunctor_map_of_le
  isIso_restrictFunctor_map_pushforward exists_coherent_pushforward_iso
  exists_coherent_annihilator_submodule_isIso_near_of_isLocallyNoetherian)

universe u

namespace Stacks.Chow

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable {X : Scheme.{u}}

/-- The support of a direct image along a closed immersion lies in the range of that
immersion. -/
private theorem supp_pushforward_subset_range {Z : Scheme.{u}} (i : Z ⟶ X)
    [IsClosedImmersion i] (H : Z.Modules) :
    SheafOfModules.supp ((Scheme.Modules.pushforward i).obj H) ⊆ Set.range i.base := fun x hx ↦
  Stacks.AlgebraicGeometry.Tag01YMHigherRank.supp_pushforward_subset_range i H x
    ((SheafOfModules.mem_supp_iff_nontrivial_stalk _ x).mp hx)

/-- **[Stacks, Tag 01YE] over a locally Noetherian scheme.** Let `i : Z ⟶ X` be an integral
closed subscheme of a locally Noetherian scheme, with generic point `ξ`, and let `𝒢` be a
coherent `𝒪_X`-module whose stalk at `i ξ` is annihilated by the maximal ideal of
`𝒪_{X, i ξ}`. Then there are an `r ≥ 0`, a coherent `𝒪_X`-module `M` supported inside `Z`, and
morphisms

`M ⟶ ⨁_{j < r} i_* 𝒪_Z`  and  `M ⟶ 𝒢`

which are both isomorphisms after restriction to one open neighbourhood of `i ξ`.

The annihilator of the ideal sheaf of `Z` inside `𝒢` agrees with `𝒢` near `i ξ` and is a direct
image `i_* 𝒢₀` by [Stacks, Tag 087T]; `𝒢₀` is free of some rank `r` on a neighbourhood of `ξ`,
the local ring of `Z` there being its function field; and [Stacks, Tag 0FD0] extends the
resulting isomorphism `(⨁_{j < r} 𝒪_Z)|_V ≅ 𝒢₀|_V` to a coherent submodule of `⨁_{j < r} 𝒪_Z`
equipped with a morphism to `𝒢₀`, still invertible over `V`. -/
theorem exists_free_comparison_near_genericPoint [IsLocallyNoetherian X] {Z : Scheme.{u}}
    (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (ξ : Z)
    (hξ : IsGenericPoint ξ (Set.univ : Set Z)) (G : X.Modules)
    [_root_.SheafOfModules.IsCoherent G]
    (hG : StalkKilledByMaximalIdeal G (i.base ξ)) :
    ∃ (r : ℕ) (M : X.Modules) (_ : _root_.SheafOfModules.IsCoherent M)
      (jm : M ⟶ ∐ fun _ : Fin r ↦
        (Scheme.Modules.pushforward i).obj (SheafOfModules.unit Z.ringCatSheaf))
      (β : M ⟶ G) (U : X.Opens), i.base ξ ∈ U ∧
      SheafOfModules.supp M ⊆ Set.range i.base ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map jm) ∧
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map β) := by
  have hZln : IsLocallyNoetherian Z := isLocallyNoetherian_of_isClosedImmersion i
  -- the annihilator submodule of the ideal sheaf of `Z`, which agrees with `G` near `i ξ`
  obtain ⟨A, hAcoh, hAkill, U₁, hU₁, hAiso⟩ :=
    exists_coherent_annihilator_submodule_isIso_near_of_isLocallyNoetherian i ξ hξ G hG
  have hA := hAcoh
  -- it is a direct image from `Z`
  obtain ⟨G₀, hG₀coh, ⟨eA⟩⟩ := exists_coherent_pushforward_iso i A.toSheafOfModules hAkill
  have hG₀ := hG₀coh
  -- `G₀` is free on a neighbourhood of `ξ`
  obtain ⟨r, V, hV, ⟨eF⟩⟩ := exists_isIso_restrictFunctor_free_near_genericPoint G₀ ξ hξ
  have hNcoh : _root_.SheafOfModules.IsCoherent
      (∐ fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf) :=
    isCoherent_of_iso' (freeCoproductIso Z r) (isCoherent_free_ulift r)
  -- the isomorphism `(⨁_{j < r} 𝒪_Z)|_V ≅ (G₀)|_V`
  let φiso : (Scheme.Modules.restrictFunctor V.ι).obj
        (∐ fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf) ≅
      (Scheme.Modules.restrictFunctor V.ι).obj G₀ :=
    (Scheme.Modules.restrictFunctor V.ι).mapIso (freeCoproductIso Z r) ≪≫ eF
  -- [Stacks, Tag 0FD0] on `Z`
  obtain ⟨M₀, hM₀coh, jj, hjjmono, φ', e₀, hje, hφe⟩ :=
    @AlgebraicGeometry.exists_coherent_submodule_extension_of_isLocallyNoetherian Z hZln
      (∐ fun _ : Fin r ↦ SheafOfModules.unit Z.ringCatSheaf) G₀ hNcoh hG₀coh V φiso.hom
  have hM₀ := hM₀coh
  -- push everything forward
  set U : X.Opens := U₁ ⊓ pushforwardOpen i V with hUdef
  have hUmem : i.base ξ ∈ U := ⟨hU₁, mem_pushforwardOpen i V hV⟩
  have hpre : i ⁻¹ᵁ U ≤ V := (i.preimage_mono inf_le_right).trans (preimage_pushforwardOpen_le i V)
  have push : ∀ {P : Z.Modules} (f : M₀ ⟶ P), IsIso ((Scheme.Modules.restrictFunctor V.ι).map f) →
      IsIso ((Scheme.Modules.restrictFunctor U.ι).map ((Scheme.Modules.pushforward i).map f)) :=
    fun f hf ↦ isIso_restrictFunctor_map_pushforward i f V hf U hpre
  have h1 := push jj (by rw [hje]; infer_instance)
  have h2 := push φ' (by rw [← hφe]; infer_instance)
  have h3 : IsIso ((Scheme.Modules.restrictFunctor U.ι).map A.ι) :=
    isIso_restrictFunctor_map_of_le A.ι inf_le_left hAiso
  refine ⟨r, (Scheme.Modules.pushforward i).obj M₀,
    AlgebraicGeometry.isCoherent_pushforward_of_isClosedImmersion i M₀,
    (Scheme.Modules.pushforward i).map jj ≫
      (pushforwardCoproductConstIso i (SheafOfModules.unit Z.ringCatSheaf) r).hom ≫
        (biproduct.isoCoproduct _).hom,
    (Scheme.Modules.pushforward i).map φ' ≫ eA.hom ≫ A.ι, U, hUmem,
    supp_pushforward_subset_range i M₀, ?_, ?_⟩
  · exact isIso_map_comp _ _ _ h1 (isIso_map_comp _ _ _ inferInstance inferInstance)
  · exact isIso_map_comp _ _ _ h2 (isIso_map_comp _ _ _ inferInstance h3)

/-! ### Morphisms out of a locally finite direct sum, near one point -/

/-- **A morphism out of a locally finite direct sum is invertible near a point at which the
corresponding summand's morphism is.** Near such a point only the one summand survives. -/
theorem exists_isIso_restrict_desc {J : Type u} (F : J → X.Modules) (Zc : J → Set X)
    (hsupp : ∀ j, SheafOfModules.supp (F j) ⊆ Zc j) (hclosed : ∀ j, IsClosed (Zc j))
    (hLF : LocallyFinite Zc) {N : X.Modules} (g : ∀ j, F j ⟶ N) (j₀ : J) (x : X)
    (hx : ∀ j, j ≠ j₀ → x ∉ Zc j) (W : X.Opens) (hxW : x ∈ W)
    (hW : IsIso ((Scheme.Modules.restrictFunctor W.ι).map (g j₀))) :
    ∃ W' : X.Opens, x ∈ W' ∧
      IsIso ((Scheme.Modules.restrictFunctor W'.ι).map (Sigma.desc g)) := by
  obtain ⟨V, hxV, hι⟩ := exists_isIso_restrict_sigmaι F Zc hsupp hclosed hLF x j₀ hx
  refine ⟨V ⊓ W, ⟨hxV, hxW⟩, ?_⟩
  refine isIso_map_of_comp _ (Sigma.ι F j₀) (Sigma.desc g) (g j₀) (Sigma.ι_comp_desc _ _) ?_ ?_
  · exact isIso_restrictFunctor_map_of_le _ inf_le_left hι
  · exact isIso_restrictFunctor_map_of_le _ inf_le_right hW

/-- **A morphism of locally finite direct sums is invertible near a point at which the
corresponding summand's morphism is.** Near such a point only the one summand survives, on both
sides. -/
theorem exists_isIso_restrict_sigmaMap {J : Type u} (F G : J → X.Modules) (Zc : J → Set X)
    (hsuppF : ∀ j, SheafOfModules.supp (F j) ⊆ Zc j)
    (hsuppG : ∀ j, SheafOfModules.supp (G j) ⊆ Zc j) (hclosed : ∀ j, IsClosed (Zc j))
    (hLF : LocallyFinite Zc) (g : ∀ j, F j ⟶ G j) (j₀ : J) (x : X)
    (hx : ∀ j, j ≠ j₀ → x ∉ Zc j) (W : X.Opens) (hxW : x ∈ W)
    (hW : IsIso ((Scheme.Modules.restrictFunctor W.ι).map (g j₀))) :
    ∃ W' : X.Opens, x ∈ W' ∧
      IsIso ((Scheme.Modules.restrictFunctor W'.ι).map
        (CategoryTheory.Limits.Sigma.map g)) := by
  obtain ⟨V₁, hxV₁, hι₁⟩ := exists_isIso_restrict_sigmaι F Zc hsuppF hclosed hLF x j₀ hx
  obtain ⟨V₂, hxV₂, hι₂⟩ := exists_isIso_restrict_sigmaι G Zc hsuppG hclosed hLF x j₀ hx
  refine ⟨V₁ ⊓ V₂ ⊓ W, ⟨⟨hxV₁, hxV₂⟩, hxW⟩, ?_⟩
  refine isIso_map_of_comp _ (Sigma.ι F j₀) (CategoryTheory.Limits.Sigma.map g)
    (g j₀ ≫ Sigma.ι G j₀) (CategoryTheory.Limits.Sigma.ι_map _ j₀) ?_ ?_
  · exact isIso_restrictFunctor_map_of_le _ (le_trans inf_le_left inf_le_left) hι₁
  · exact isIso_map_comp _ _ _ (isIso_restrictFunctor_map_of_le _ inf_le_right hW)
      (isIso_restrictFunctor_map_of_le _ (le_trans inf_le_left inf_le_right) hι₂)


end Stacks.Chow

end
