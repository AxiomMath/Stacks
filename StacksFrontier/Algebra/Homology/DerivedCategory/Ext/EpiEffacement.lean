module

public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
import all StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic.YonedaClassMap

/-!
# Effacing a positive-degree `Ext`-class by an epimorphism of the source

Let `𝒜` be an abelian category. Every class `ξ ∈ Ext^{n + 1}_𝒜(B, A)` of positive degree is
killed by precomposition with some epimorphism `p : Z ⟶ B`:

`(mk₀ p) ∘ ξ = 0  in  Ext^{n + 1}_𝒜(Z, A)`.

The epimorphism is the one a Yoneda extension representing `ξ` ends with. Indeed
`CategoryTheory.Abelian.surjective_extClassMap` writes `ξ` as the class of an exact sequence
`0 → A → Z_n → ⋯ → Z_0 → B → 0`, and the class of such a sequence is killed by its own
surjection `Z_0 ↠ B`: in degree one that is
`CategoryTheory.ShortComplex.ShortExact.comp_extClass`, and in higher degree it follows by
induction, because cutting the sequence at its left end leaves a shorter extension *with the
same surjection onto `B`* and multiplies the classes.

## Why this is not `Stacks.ExtEffacement.exists_epi_precomp_eq_zero`

`Stacks.ExtEffacement.exists_epi_precomp_eq_zero` effaces a positive-degree class too, but it
builds the epimorphism out of an injective resolution, so it needs `𝒜` to have enough
injectives and it gives no control whatever over the source `Z`. Here there is no hypothesis
beyond `𝒜` being abelian, and `Z` is a term of an exact sequence in `𝒜` itself. That is what
makes the statement usable in an abelian category of finiteness-constrained objects — the
category `Coh(𝒪_X)` of coherent modules on a Noetherian scheme, which has no injectives at all,
is the case the dévissage of [Stacks, Tag 0G2H] needs, where the effacing epimorphism is fed to
Artin--Rees and so must have a coherent source and a coherent kernel.

## Main results

* `CategoryTheory.Abelian.mk₀_comp_extClassMap_eq_zero`: the surjection a Yoneda extension ends
  with kills the class of that extension.
* `CategoryTheory.Abelian.exists_epi_mk₀_comp_eq_zero`: **every class of positive degree is
  effaced by an epimorphism of its source.**

## References

* [Stacks Project, Tag 06XU](https://stacks.math.columbia.edu/tag/06XU)
* [Stacks Project, Tag 0G2H](https://stacks.math.columbia.edu/tag/0G2H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w

namespace CategoryTheory.Abelian

variable {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] [HasExt.{w} 𝒜]

/-- **The surjection a Yoneda extension ends with kills the class of that extension.** For
`E : 0 → A → Z_n → ⋯ → Z_0 → B → 0` the composite of `δ(E) ∈ Ext^{n + 1}_𝒜(B, A)` with
`Z_0 ↠ B` vanishes.

In degree one this is `CategoryTheory.ShortComplex.ShortExact.comp_extClass`. In degree `n + 2`
the class is that of the extension cut at its left end, composed with the class of the cutting
short exact sequence; the cut extension has the *same* surjection `Z_0 ↠ B`, so the inductive
hypothesis applies to the left factor. -/
public lemma mk₀_comp_extClassMap_eq_zero {B : 𝒜} :
    ∀ (n : ℕ) {A : 𝒜} (E : YonedaExtension B A n),
      (Ext.mk₀ E.g).comp (extClassMap.{w} n E) (zero_add (n + 1)) = 0 := by
  intro n
  induction n with
  | zero =>
    intro A E
    exact (shortExact_zero E).comp_extClass
  | succ n ih =>
    intro A E
    have key : (Ext.mk₀ E.g).comp (extClassMap.{w} (n + 1) E) (zero_add (n + 1 + 1)) =
        ((Ext.mk₀ (cut E).g).comp (extClassMap.{w} n (cut E)) (zero_add (n + 1))).comp
          (shortExact_cut E).extClass rfl := by
      rw [extClassMap_succ]
      exact (Ext.comp_assoc _ _ _ (zero_add (n + 1)) rfl (by lia)).symm
    rw [key, ih (cut E), Ext.zero_comp]
    rfl

/-- **Every `Ext`-class of positive degree is effaced by an epimorphism of its source.** For
`ξ ∈ Ext^{n + 1}_𝒜(B, A)` in an abelian category there is an epimorphism `p : Z ⟶ B` with
`ξ ∘ p = 0`; moreover `Z` is the right-hand term of an exact sequence
`0 → A → Z_n → ⋯ → Z_1 → Z → B → 0` in `𝒜` representing `ξ`.

Nothing is assumed about `𝒜` beyond abelianness: the epimorphism comes from the Yoneda
extension representing `ξ` (`CategoryTheory.Abelian.surjective_extClassMap`), which exists in
any abelian category, and `CategoryTheory.Abelian.mk₀_comp_extClassMap_eq_zero` says it kills
the class. -/
public lemma exists_epi_mk₀_comp_eq_zero {B A : 𝒜} (n : ℕ) (ξ : Ext.{w} B A (n + 1)) :
    ∃ (Z : 𝒜) (p : Z ⟶ B), Epi p ∧ (Ext.mk₀ p).comp ξ (zero_add (n + 1)) = 0 := by
  obtain ⟨E, hE⟩ := surjective_extClassMap.{w} B A n ξ
  exact ⟨E.Z.right, E.g, E.epi_g, hE ▸ mk₀_comp_extClassMap_eq_zero.{w} n E⟩

end CategoryTheory.Abelian

end
