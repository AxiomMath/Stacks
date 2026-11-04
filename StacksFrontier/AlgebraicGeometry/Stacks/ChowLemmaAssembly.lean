module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaCompactifiableCover
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaNoetherianClaim
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaQuasiSeparated

/-!
# Chow's lemma for algebraic stacks (Stacks 0CQ8), assembled from the statement of 0CQ7

The proof of Stacks 0CQ8 first reduces from separated 1-morphisms of finite type to separated
1-morphisms of finite presentation (Stacks 0CQ2), then by absolute Noetherian approximation of the
base (Stacks 07SU) and the descent of the stack and of separatedness to a finite stage (Stacks
0CN4, Stacks 0CPZ) to a Noetherian base. This file chains those reductions, which are proved in
`AlgebraicGeometry.Stack.AlgebraicStacks.HasChowCover.of_hasNoetherianApproximation`, into the
statement of Stacks 0CQ8 from its Noetherian case, and proves the Noetherian case from the
statement of Stacks 0CQ7, following the source's last three paragraphs.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_of_forall_isNoetherian`: the conclusion of
  Stacks 0CQ8 for every separated 1-morphism of finite type to a quasi-compact quasi-separated
  algebraic space, from its Noetherian case and the statements of Stacks 0CQ2 (in the form of the
  reduction `HasChowCover.of_forall_isFinitePresentation`), 0CN4, 0CPZ and 07SU.
* `AlgebraicStacks.hasChowCover_of_isNoetherian_of_isReducedStack_of_chowInputs`:
  the Noetherian reduced case, from the statement of Stacks 0CQ7.
* `AlgebraicStacks.exists_isProper_isSurjective_cover_of_isSeparated_isFiniteType_of`: the
  statement of Stacks 0CQ8 from the statements of Stacks 0CQ7, 0CQ2 (as the reduction step), 0CN4,
  0CPZ and 07SU, which are the results of other chapters the source's proof uses.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The reduction of Stacks 0CQ8 to its Noetherian case.** Let `Y` be a quasi-compact and
quasi-separated algebraic space and `f : 𝒳 ⟶ Y` a separated 1-morphism of finite type. The
conclusion of Chow's lemma holds for `f` given:
* `h0CQ2step` — the first reduction of the source's proof, finite presentation suffices; it is
  `HasChowCover.of_forall_isFinitePresentation` applied to the statement of Stacks 0CQ2;
* `h07SU` — the statement of Stacks 07SU, absolute Noetherian approximation;
* `h0CN4`, `h0CPZ` — the statements of Stacks 0CN4 and Stacks 0CPZ as consumed by
  `HasChowCover.of_hasNoetherianApproximation`;
* `hN` — the Noetherian case;
* `hqs` — a quasi-separated algebraic space is a quasi-separated algebraic stack.
The proof is the source's second paragraph:
`HasChowCover.of_hasNoetherianApproximation` handles finite presentation over a base with a
Noetherian approximation. -/
theorem hasChowCover_of_forall_isNoetherian
    (h0CQ2step : (∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y),
      Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
        IsSeparated B S hS f → IsFinitePresentation B S hS f →
          HasChowCover.{u, w} B S hS hY f) →
      ∀ {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y),
        Space.IsQuasiCompactSpace B S hS Y →
        Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
        ∀ {𝒳 : AlgebraicStacks.{u, w} B S hS}
          (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
          IsSeparated B S hS f → IsFiniteType B S hS f → HasChowCover.{u, w} B S hS hY f)
    (h07SU : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Y →
      Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
        Space.HasNoetherianApproximation B S hS B.contains_terminal Y)
    (h0CN4 : ∀ {I : Type u} [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (_ : IsLimit c)
      (hX : IsAlgebraicSpace B S hS c.pt) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
      (_ : ∀ {i j : I} (f : i ⟶ j), Space.IsAffineHom B S hS (D.map f))
      (_ : ∀ i, Space.IsQuasiCompactSpace B S hS (D.obj i))
      (_ : ∀ i, Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B)
        (D.obj i))
      (𝒳 : AlgebraicStacks.{u, w} B S hS)
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS c.pt hX),
      IsFinitePresentation B S hS f →
      ∃ (i : I) (𝒳ᵢ : AlgebraicStacks.{u, w} B S hS)
        (fᵢ : 𝒳ᵢ ⟶ algebraicSpaceStack.{u, w} B S hS (D.obj i) (hD i)),
        IsFinitePresentation B S hS fᵢ ∧
        ∃ e : Bicategory.Equivalence 𝒳 (twoFibreProductSquareAlgebraicStacks B S hS fᵢ
            (algebraicSpaceStackMap.{u, w} B S hS hX (hD i) (c.π.app i))).pt,
          Nonempty (e.hom ≫ (twoFibreProductSquareAlgebraicStacks B S hS fᵢ
            (algebraicSpaceStackMap.{u, w} B S hS hX (hD i) (c.π.app i))).snd ≅ f))
    (h0CPZ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : Space.DescentSituation B S hS (BigFppfSite.contains_terminal B) I)
      (𝒳₀ : AlgebraicStacks.{u, w} B S hS)
      (f₀ : 𝒳₀ ⟶ algebraicSpaceStack.{u, w} B S hS (D.system.obj (op D.base))
        (D.algebraicSpace D.base)),
      IsQuasiCompactStack.{u, w} B S hS 𝒳₀.val 𝒳₀.property →
      AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS
        (BigFppfSite.contains_terminal B) 𝒳₀ →
      IsSeparated B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f₀
          (algebraicSpaceStackMap.{u, w} B S hS D.limitAlgebraicSpace (D.algebraicSpace D.base)
            (D.limitCone.π.app (op D.base)))).snd →
      ∃ (i₀ : I) (h₀ : D.base ≤ i₀), ∀ (i : I) (hi : i₀ ≤ i),
        IsSeparated B S hS
          (twoFibreProductSquareAlgebraicStacks B S hS f₀
            (algebraicSpaceStackMap.{u, w} B S hS (D.algebraicSpace i) (D.algebraicSpace D.base)
              (D.system.map (homOfLE (h₀.trans hi)).op))).snd)
    (hN : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y),
      Space.IsNoetherian B S hS (BigFppfSite.contains_terminal B) Y →
      ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
        IsSeparated B S hS f → IsFiniteType B S hS f → HasChowCover.{u, w} B S hS hY f)
    (hqs : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y),
      Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B) Y →
      AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS
        (BigFppfSite.contains_terminal B) (algebraicSpaceStack.{u, w} B S hS Y hY))
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) :
    HasChowCover.{u, w} B S hS hY f :=
  h0CQ2step (fun Y' hY' hY'qc hY'qs _ f' hsep' hfp' =>
      HasChowCover.of_hasNoetherianApproximation B S hS h0CN4 h0CPZ hN hqs hY'
        (h07SU Y' hY' hY'qc hY'qs) f' hsep' hfp')
    hY hYqc hYqs f hsep hft

/-- **The Noetherian reduced case of Stacks 0CQ8, from the statement of Stacks 0CQ7.** Let `Y` be
a Noetherian algebraic space and `f : 𝒳 ⟶ Y` a separated 1-morphism of finite type from a reduced
algebraic stack. Granted the statement of Stacks 0CQ7 (`h0CQ7`, in the form
`HasProperCompactifiableCover`), the conclusion of Chow's lemma holds for `f`.

The inertia of `𝒳` is quasi-compact, `𝒳` being quasi-separated over the quasi-separated `Y`
(`isQuasiCompactMorphism_inertiaProjectionAlgebraicStacks_of_isQuasiSeparated`). The claim of the
source's proof (`exists_gerbe_claim_of_isNoetherian_of_isReducedStack`) produces `𝒳' ⟶ Y'` over
`𝒳 ⟶ Y` through a proper surjective `𝒳' ⟶ 𝒳` and a proper `Y' ⟶ Y`, with a quasi-compact open
`V ⊆ Y'` over which `𝒳'` is a gerbe and whose points are dense in `|𝒳'|`. Stacks 0CQ7 for
`(𝒳' ⟶ Y', V)` gives a Chow cover of `𝒳' ⟶ Y'`
(`HasChowCover.of_hasProperCompactifiableCover`), which descends to `f`
(`HasChowCover.of_proper`). -/
theorem hasChowCover_of_isNoetherian_of_isReducedStack_of_chowInputs
    (h0CQ7 : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
      (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
      (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V),
      IsSeparated B S hS f → IsFiniteType B S hS f → Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      Space.IsQuasiCompactSpace B S hS V.toFunctor →
      IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst →
        HasProperCompactifiableCover.{u, w} B S hS hY f V)
    {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    (hYN : Space.IsNoetherian B S hS B.contains_terminal Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hred : IsReducedStack B S hS 𝒳) (hsep : IsSeparated B S hS f)
    (hft : IsFiniteType B S hS f) :
    HasChowCover.{u, w} B S hS hY f := by
  obtain ⟨Y', hY', q', V, hV, 𝒳', f', b, hq', hb, hbs, hsep', hft', hY'qc, hY'qs, hVqc, hG,
      hdense, ⟨e⟩⟩ :=
    exists_gerbe_claim_of_isNoetherian_of_isReducedStack B S hS hY hYN f hsep hft hred
      (isQuasiCompactMorphism_inertiaProjectionAlgebraicStacks_of_isQuasiSeparated B S hS hY
        hYN.2.1 f (isQuasiSeparated_of_isSeparated B S hS hsep))
  exact HasChowCover.of_proper B S hS hY hY' f f' q' hq' b hb hbs e
    (HasChowCover.of_hasProperCompactifiableCover B S hS hY' f' V hV hG hdense
      (h0CQ7 Y' hY' 𝒳' f' V hV hsep' hft' hY'qc hY'qs hVqc hG))

/-- **Stacks 0CQ8 from the statements of the results of other chapters its proof uses.** Let
`f : 𝒳 ⟶ Y` be a 1-morphism from an algebraic stack to a quasi-compact and quasi-separated
algebraic space which is separated and of finite type. Then there are algebraic spaces `X` and
`X̄`, a proper surjective `X ⟶ 𝒳`, an open immersion `X ⟶ X̄` and a proper `X̄ ⟶ Y` with
`X ⟶ 𝒳 ⟶ Y` 2-isomorphic to `X ⟶ X̄ ⟶ Y`.

The inputs are the statements of Stacks 0CQ7 (`h0CQ7`), 07SU (`h07SU`), 0CN4 (`h0CN4`) and
0CPZ (`h0CPZ`), and the 0CQ2 step of the source's first paragraph (`h0CQ2step`, which is
`HasChowCover.of_forall_isFinitePresentation` applied to the statement of Stacks 0CQ2). The other
steps of the source's proof are the reduction to the reduced case (Stacks 050C,
`HasChowCover.of_forall_isReducedStack`), the Noetherian reduced case
(`hasChowCover_of_isNoetherian_of_isReducedStack_of_chowInputs`), and the finite presentation step
(`hasChowCover_of_forall_isNoetherian`), with the quasi-separatedness of the stack of a
quasi-separated algebraic space (`isAbsolutelyQuasiSeparated_algebraicSpaceStack`). -/
theorem exists_isProper_isSurjective_cover_of_isSeparated_isFiniteType_of
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h0CQ7 : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
      (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
      (V : Subfunctor Y) (hV : Space.IsOpenSubspace B S hS V),
      IsSeparated B S hS f → IsFiniteType B S hS f → Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      Space.IsQuasiCompactSpace B S hS V.toFunctor →
      IsGerbeOver B S hS (twoFibreProductSquareAlgebraicStacks B S hS
        (algebraicSpaceStackMap.{u, w} B S hS hV.1 hY V.ι) f).fst →
        HasProperCompactifiableCover.{u, w} B S hS hY f V)
    (h0CQ2step : (∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y),
      Space.IsQuasiCompactSpace B S hS Y →
      Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      ∀ (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
        IsSeparated B S hS f → IsFinitePresentation B S hS f →
          HasChowCover.{u, w} B S hS hY f) →
      ∀ ⦃Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u⦄ (hY : IsAlgebraicSpace B S hS Y),
        Space.IsQuasiCompactSpace B S hS Y →
        Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
        ∀ ⦃𝒳 : AlgebraicStacks.{u, w} B S hS⦄
          (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
          IsSeparated B S hS f → IsFiniteType B S hS f → HasChowCover.{u, w} B S hS hY f)
    (h07SU : ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u), IsAlgebraicSpace B S hS Y →
      Space.IsQuasiCompactSpace B S hS Y → Space.IsAbsolutelyQuasiSeparated B S hS hZ Y →
        Space.HasNoetherianApproximation B S hS hZ Y)
    (h0CN4 : ∀ {I : Type u} [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (c : Cone D) (_ : IsLimit c)
      (hX : IsAlgebraicSpace B S hS c.pt) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
      (_ : ∀ {i j : I} (f : i ⟶ j), Space.IsAffineHom B S hS (D.map f))
      (_ : ∀ i, Space.IsQuasiCompactSpace B S hS (D.obj i))
      (_ : ∀ i, Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B)
        (D.obj i))
      (𝒳 : AlgebraicStacks.{u, w} B S hS)
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS c.pt hX),
      IsFinitePresentation B S hS f →
      ∃ (i : I) (𝒳ᵢ : AlgebraicStacks.{u, w} B S hS)
        (fᵢ : 𝒳ᵢ ⟶ algebraicSpaceStack.{u, w} B S hS (D.obj i) (hD i)),
        IsFinitePresentation B S hS fᵢ ∧
        ∃ e : Bicategory.Equivalence 𝒳 (twoFibreProductSquareAlgebraicStacks B S hS fᵢ
            (algebraicSpaceStackMap.{u, w} B S hS hX (hD i) (c.π.app i))).pt,
          Nonempty (e.hom ≫ (twoFibreProductSquareAlgebraicStacks B S hS fᵢ
            (algebraicSpaceStackMap.{u, w} B S hS hX (hD i) (c.π.app i))).snd ≅ f))
    (h0CPZ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : Space.DescentSituation B S hS (BigFppfSite.contains_terminal B) I)
      (𝒳₀ : AlgebraicStacks.{u, w} B S hS)
      (f₀ : 𝒳₀ ⟶ algebraicSpaceStack.{u, w} B S hS (D.system.obj (op D.base))
        (D.algebraicSpace D.base)),
      IsQuasiCompactStack.{u, w} B S hS 𝒳₀.val 𝒳₀.property →
      AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B S hS
        (BigFppfSite.contains_terminal B) 𝒳₀ →
      IsSeparated B S hS
        (twoFibreProductSquareAlgebraicStacks B S hS f₀
          (algebraicSpaceStackMap.{u, w} B S hS D.limitAlgebraicSpace (D.algebraicSpace D.base)
            (D.limitCone.π.app (op D.base)))).snd →
      ∃ (i₀ : I) (h₀ : D.base ≤ i₀), ∀ (i : I) (hi : i₀ ≤ i),
        IsSeparated B S hS
          (twoFibreProductSquareAlgebraicStacks B S hS f₀
            (algebraicSpaceStackMap.{u, w} B S hS (D.algebraicSpace i) (D.algebraicSpace D.base)
              (D.system.map (homOfLE (h₀.trans hi)).op))).snd)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) (hYqc : Space.IsQuasiCompactSpace B S hS Y)
    (hYqs : Space.IsAbsolutelyQuasiSeparated B S hS hZ Y)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hsep : IsSeparated B S hS f) (hft : IsFiniteType B S hS f) :
    ∃ (X Xbar : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
      (_ : IsAlgebraicSpace B S hS Xbar)
      (a : algebraicSpaceStack.{u, w} B S hS X hX ⟶ 𝒳) (i : X ⟶ Xbar) (g : Xbar ⟶ Y),
      IsProper B S hS a ∧ Stack.IsSurjective B S hS a ∧ Space.IsOpenImmersion B S hS i ∧
        Space.IsProper B S hS g ∧
        Nonempty (a ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS hX hY (i ≫ g)) :=
  hasChowCover_of_forall_isNoetherian B S hS h0CQ2step (fun Y hY hqc hqs => h07SU Y hY hqc hqs)
    h0CN4 h0CPZ
    (fun _ hY hYN _ f hsep hft => HasChowCover.of_forall_isReducedStack B S hS
      (fun _ hY hYN _ f hred hsep hft =>
        hasChowCover_of_isNoetherian_of_isReducedStack_of_chowInputs B S hS h0CQ7 hY hYN f hred hsep
          hft)
      hY hYN f hsep hft)
    (fun _ hY h => isAbsolutelyQuasiSeparated_algebraicSpaceStack B S hS B.contains_terminal hY h)
    hY hYqc hYqs f hsep hft

end AlgebraicGeometry.Stack.AlgebraicStacks

end
