module

public import StacksFrontier.AlgebraicGeometry.Chow.SplittingPrinciple.DualTotalChern
public import StacksFrontier.CategoryTheory.Sites.Modules.AdicQuotientModuleTower

/-!
# A filtration with invertible quotients starts with an invertible submodule

Let `X` be a scheme and let `ℰ` be an `𝒪_X`-module with a filtration
`0 = ℱ₀ ⊆ ℱ₁ ⊆ ⋯ ⊆ ℱ_{r+1} = ℰ` whose successive quotients are invertible
(`Stacks.WeilCohomology.HasInvertibleFiltration`). The filtration is recorded from the top: `ℰ`
is an extension `0 ⟶ ℱ_r ⟶ ℰ ⟶ ℒ ⟶ 0` of an invertible module `ℒ` by a filtered module.
Reading it from the bottom, the first step `ℱ₁` is a submodule of rank one of `ℰ` and the
quotient `ℰ/ℱ₁` inherits the filtration `ℱᵢ/ℱ₁`, whose successive quotients are the same
invertible modules. This file proves that reading.

## Main results

* `Stacks.WeilCohomology.HasInvertibleFiltration.exists_shortExact_rankOne_sub`: a module with
  a filtration of length `r + 1` with invertible quotients is an extension
  `0 ⟶ ℒ' ⟶ ℰ ⟶ 𝒬 ⟶ 0` of a module `𝒬` with such a filtration of length `r` by a module `ℒ'`
  finite locally free of rank one.

## Implementation notes

The induction runs along the filtration. For the step `0 ⟶ ℱ ⟶ ℰ ⟶ ℒ ⟶ 0`, the induction
hypothesis writes `ℱ` as an extension of `𝒬_ℱ` by `ℒ'`, and the third isomorphism theorem
(`Stacks.Abelian.cokernelCompShortComplex_shortExact`) gives the short exact sequence
`0 ⟶ ℱ/ℒ' ⟶ ℰ/ℒ' ⟶ ℰ/ℱ ⟶ 0`, with `ℱ/ℒ' ≅ 𝒬_ℱ` and `ℰ/ℱ ≅ ℒ`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open scoped ZeroObject

universe u

namespace Stacks.WeilCohomology.HasInvertibleFiltration

variable {X : Scheme.{u}}

/-- The cokernel of the first arrow of a short exact sequence is its third term. -/
private def cokernelIsoX₃ (S : ShortComplex X.Modules) (hS : S.ShortExact) :
    cokernel S.f ≅ S.X₃ :=
  (cokernelIsCokernel S.f).coconePointUniqueUpToIso hS.gIsCokernel

/-- The cokernel of a monomorphism sits in a short exact sequence. -/
private theorem shortExact_cokernel {A B : X.Modules} (i : A ⟶ B) [Mono i] :
    (ShortComplex.mk i (cokernel.π i) (cokernel.condition i)).ShortExact :=
  ShortComplex.ShortExact.mk' (ShortComplex.exact_cokernel i) inferInstance inferInstance

/-- The induction behind
`Stacks.WeilCohomology.HasInvertibleFiltration.exists_shortExact_rankOne_sub`, with the length
of the filtration as an index. -/
private theorem exists_shortExact_rankOne_sub_aux {E : X.Modules} {n : ℕ}
    (h : HasInvertibleFiltration X E n) :
    ∀ r, n = r + 1 → ∃ (L Q : X.Modules) (i : L ⟶ E) (p : E ⟶ Q) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 ∧
        HasInvertibleFiltration X Q r := by
  induction h with
  | nil E hE => intro r hr; omega
  | @step E F L r₀ f g w hS hL hE hF ih =>
    intro r hr
    obtain rfl : r = r₀ := by omega
    have := hS.mono_f
    have := hS.epi_g
    have hL1 := @Stacks.Chow.isFiniteLocallyFreeOfRank_one_of_isInvertible _ L hL
    rcases r with _ | r₁
    · -- `ℱ = 0`, so `ℰ ≅ ℒ` is itself of rank one
      have hF0 : IsZero F := by
        cases hF with
        | nil _ h0 => exact h0
      have : Mono g := (ShortComplex.exact_iff_mono _ (hF0.eq_of_src f 0)).1 hS.exact
      have : IsIso g := isIso_of_mono_of_epi g
      refine ⟨E, 0, 𝟙 E, 0, by simp, ?_,
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.of_iso.{u, u, u}
          (asIso g).symm hL1, HasInvertibleFiltration.nil 0 (isZero_zero _)⟩
      exact ShortComplex.ShortExact.mk' ((ShortComplex.exact_iff_epi _ rfl).2 inferInstance)
        inferInstance ((isZero_zero _).epi _)
    · -- `ℱ` is an extension of `𝒬_ℱ` by `ℒ'`; pass to the quotients by `ℒ'`
      obtain ⟨L', QF, i', p', w', hS', hL', hQF⟩ := ih r₁ rfl
      have := hS'.mono_f
      let K := Stacks.Abelian.cokernelCompShortComplex i' f
      have hK : K.ShortExact := Stacks.Abelian.cokernelCompShortComplex_shortExact i' f
      let e₁ : cokernel i' ≅ QF := cokernelIsoX₃ _ hS'
      let e₃ : cokernel f ≅ L := cokernelIsoX₃ _ hS
      have hK' : (ShortComplex.mk (Stacks.Abelian.cokernelCompι i' f)
          (Stacks.Abelian.cokernelCompπ i' f ≫ e₃.hom)
          (by rw [← Category.assoc, Stacks.Abelian.cokernelCompι_comp_cokernelCompπ,
            zero_comp])).ShortExact :=
        ShortComplex.shortExact_of_iso
          (ShortComplex.isoMk (S₁ := K) (Iso.refl _) (Iso.refl _) e₃
          ((Category.id_comp _).trans (Category.comp_id _).symm) (Category.id_comp _)) hK
      have hQfl : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
          (cokernel i') :=
        ((hQF.of_iso e₁.symm).isFiniteLocallyFreeOfRank).isFiniteLocallyFree
      refine ⟨L', cokernel (i' ≫ f), i' ≫ f, cokernel.π (i' ≫ f), cokernel.condition _,
        shortExact_cokernel (i' ≫ f), hL', ?_⟩
      exact HasInvertibleFiltration.step _ _ _ hK' hL
        (Stacks.Chow.GenuineChern.isFiniteLocallyFree_of_shortExact _ hK' hQfl
          hL1.isFiniteLocallyFree)
        (hQF.of_iso e₁.symm)

/-- **A filtration with invertible quotients starts with a submodule of rank one.** A module
`ℰ` with a filtration of length `r + 1` with invertible successive quotients is an extension
`0 ⟶ ℒ' ⟶ ℰ ⟶ 𝒬 ⟶ 0` in which `ℒ'` is finite locally free of rank one and `𝒬` has a
filtration of length `r` with invertible successive quotients. -/
theorem exists_shortExact_rankOne_sub {E : X.Modules} {r : ℕ}
    (h : HasInvertibleFiltration X E (r + 1)) :
    ∃ (L Q : X.Modules) (i : L ⟶ E) (p : E ⟶ Q) (w : i ≫ p = 0),
      (ShortComplex.mk i p w).ShortExact ∧
        AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 ∧
        HasInvertibleFiltration X Q r :=
  exists_shortExact_rankOne_sub_aux h r rfl

end Stacks.WeilCohomology.HasInvertibleFiltration

end
