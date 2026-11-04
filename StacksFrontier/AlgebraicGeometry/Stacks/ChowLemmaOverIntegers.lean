module

public import StacksFrontier.AlgebraicGeometry.Spaces.AbsoluteNoetherianApproximation.Main
public import StacksFrontier.AlgebraicGeometry.Spaces.DescendingProperties.SeparatedDescent
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemma.ChangeOfBase
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemma.ChangeOfBaseHypotheses
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemma.ChangeOfBaseSpaces
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaAssembly

/-!
# Chow's lemma for algebraic stacks (Stacks 0CQ8) with the approximation taken over `Spec(ℤ)`

The proof of Stacks 0CQ8 approximates the base by algebraic spaces of finite type over `Spec(ℤ)`
(Stacks 07SU). That approximation is an absolute statement: it is about algebraic spaces over
`Spec(ℤ)`, and `AlgebraicGeometry.Space.hasNoetherianApproximation_of_isQuasiCompactSpace` proves
it for the big fppf site of the terminal scheme. For a base scheme `S` other than `Spec(ℤ)` the
analogous statement about algebraic spaces over `S` is of no use: a stage of such an approximation
would be an algebraic space over `S` of finite type over `Spec(ℤ)`, so for `S = Spec(k)` with `k`
uncountable no nonempty stage can exist, while the stages of an approximation of a nonempty space
are nonempty.

This file therefore takes the approximation where it is available. Following
`AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_of_changeBase`, a 1-morphism
`f : 𝒳 ⟶ Y` over `S` is viewed over the terminal scheme through the lower-shriek extension, the
conclusion of Chow's lemma is proved there — where absolute Noetherian approximation applies and
is discharged by Stacks 07SU — and the conclusion descends back to `S`.

## Main results

* `exists_isProper_isSurjective_cover_of_isSeparated_isFiniteType_of_overIntegers`:
  the statement of Stacks 0CQ8 over an arbitrary base scheme `S` of the big fppf site, from the
  statements over the terminal scheme of Stacks 0CN4, 0CPZ and of the 0CQ2 reduction step.
  Absolute Noetherian approximation is no longer an input: it is Stacks 07SU.

## References

* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
* [Stacks Project, Tag 07SU](https://stacks.math.columbia.edu/tag/07SU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0CQ8 with absolute Noetherian approximation discharged.** Let `f : 𝒳 ⟶ Y` be a
1-morphism from an algebraic stack to a quasi-compact and quasi-separated algebraic space over a
base scheme `S` of the big fppf site, separated and of finite type. Then there are algebraic
spaces `X` and `X̄`, a proper surjective `X ⟶ 𝒳`, an open immersion `X ⟶ X̄` and a proper
`X̄ ⟶ Y` with `X ⟶ 𝒳 ⟶ Y` 2-isomorphic to `X ⟶ X̄ ⟶ Y`.

The conclusion is that of `exists_isProper_isSurjective_cover_of_isSeparated_isFiniteType_of`,
and the difference is in the inputs. Here they are the statements of Stacks 0CN4 (`h0CN4`) and
0CPZ (`h0CPZ`), and the 0CQ2 step of the source's first paragraph
(`h0CQ2step`, which is `HasChowCover.of_forall_isFinitePresentation` applied to the statement of
Stacks 0CQ2) — all three for algebraic spaces over the **terminal** scheme. Absolute Noetherian
approximation is not an input: `f` is viewed over the terminal scheme
(`AlgebraicGeometry.Stack.changeBaseToAlgebraicSpace`), where Stacks 07SU
(`AlgebraicGeometry.Space.hasNoetherianApproximation_of_isQuasiCompactSpace`) applies, and the
conclusion of Chow's lemma descends back to `S` by
`AlgebraicGeometry.Stack.AlgebraicStacks.hasChowCover_of_changeBase`. The hypotheses on `f` are
carried across by `AlgebraicGeometry.Stack.AlgebraicStacks.isSeparated_changeBaseToAlgebraicSpace`
and `AlgebraicGeometry.Stack.AlgebraicStacks.isFiniteType_changeBaseToAlgebraicSpace`, and those
on `Y` by `AlgebraicGeometry.Space.isQuasiCompactSpace_relocalize` and
`AlgebraicGeometry.Space.isAbsolutelyQuasiSeparated_relocalize`. -/
theorem exists_isProper_isSurjective_cover_of_isSeparated_isFiniteType_of_overIntegers
    (hZ : B.Contains (⊤_ Scheme.{u}))
    (h0CQ2step : (∀ (Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u)
      (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y),
      Space.IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Y →
      Space.IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ B.contains_terminal Y →
      ∀ (𝒳 : AlgebraicStacks.{u, w} B (⊤_ Scheme.{u}) hZ)
        (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B (⊤_ Scheme.{u}) hZ Y hY),
        IsSeparated B (⊤_ Scheme.{u}) hZ f → IsFinitePresentation B (⊤_ Scheme.{u}) hZ f →
          HasChowCover.{u, w} B (⊤_ Scheme.{u}) hZ hY f) →
      ∀ {Y : (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u}
        (hY : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ Y),
        Space.IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ Y →
        Space.IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ B.contains_terminal Y →
        ∀ {𝒳 : AlgebraicStacks.{u, w} B (⊤_ Scheme.{u}) hZ}
          (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B (⊤_ Scheme.{u}) hZ Y hY),
          IsSeparated B (⊤_ Scheme.{u}) hZ f → IsFiniteType B (⊤_ Scheme.{u}) hZ f →
            HasChowCover.{u, w} B (⊤_ Scheme.{u}) hZ hY f)
    (h0CN4 : ∀ {I : Type u} [Category.{u} I] [IsCofiltered I]
      (D : I ⥤ (BigFppfOver B (⊤_ Scheme.{u}) hZ)ᵒᵖ ⥤ Type u) (c : Cone D) (_ : IsLimit c)
      (hX : IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ c.pt)
      (hD : ∀ i, IsAlgebraicSpace B (⊤_ Scheme.{u}) hZ (D.obj i))
      (_ : ∀ {i j : I} (f : i ⟶ j), Space.IsAffineHom B (⊤_ Scheme.{u}) hZ (D.map f))
      (_ : ∀ i, Space.IsQuasiCompactSpace B (⊤_ Scheme.{u}) hZ (D.obj i))
      (_ : ∀ i, Space.IsAbsolutelyQuasiSeparated B (⊤_ Scheme.{u}) hZ
        (BigFppfSite.contains_terminal B) (D.obj i))
      (𝒳 : AlgebraicStacks.{u, w} B (⊤_ Scheme.{u}) hZ)
      (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B (⊤_ Scheme.{u}) hZ c.pt hX),
      IsFinitePresentation B (⊤_ Scheme.{u}) hZ f →
      ∃ (i : I) (𝒳ᵢ : AlgebraicStacks.{u, w} B (⊤_ Scheme.{u}) hZ)
        (fᵢ : 𝒳ᵢ ⟶ algebraicSpaceStack.{u, w} B (⊤_ Scheme.{u}) hZ (D.obj i) (hD i)),
        IsFinitePresentation B (⊤_ Scheme.{u}) hZ fᵢ ∧
        ∃ e : Bicategory.Equivalence 𝒳 (twoFibreProductSquareAlgebraicStacks B
            (⊤_ Scheme.{u}) hZ fᵢ (algebraicSpaceStackMap.{u, w} B (⊤_ Scheme.{u}) hZ hX (hD i)
              (c.π.app i))).pt,
          Nonempty (e.hom ≫ (twoFibreProductSquareAlgebraicStacks B (⊤_ Scheme.{u}) hZ fᵢ
            (algebraicSpaceStackMap.{u, w} B (⊤_ Scheme.{u}) hZ hX (hD i) (c.π.app i))).snd ≅ f))
    (h0CPZ : ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
      (D : Space.DescentSituation B (⊤_ Scheme.{u}) hZ (BigFppfSite.contains_terminal B) I)
      (𝒳₀ : AlgebraicStacks.{u, w} B (⊤_ Scheme.{u}) hZ)
      (f₀ : 𝒳₀ ⟶ algebraicSpaceStack.{u, w} B (⊤_ Scheme.{u}) hZ (D.system.obj (op D.base))
        (D.algebraicSpace D.base)),
      IsQuasiCompactStack.{u, w} B (⊤_ Scheme.{u}) hZ 𝒳₀.val 𝒳₀.property →
      AlgebraicStacks.IsAbsolutelyQuasiSeparated.{u, w} B (⊤_ Scheme.{u}) hZ
        (BigFppfSite.contains_terminal B) 𝒳₀ →
      IsSeparated B (⊤_ Scheme.{u}) hZ
        (twoFibreProductSquareAlgebraicStacks B (⊤_ Scheme.{u}) hZ f₀
          (algebraicSpaceStackMap.{u, w} B (⊤_ Scheme.{u}) hZ D.limitAlgebraicSpace
            (D.algebraicSpace D.base) (D.limitCone.π.app (op D.base)))).snd →
      ∃ (i₀ : I) (h₀ : D.base ≤ i₀), ∀ (i : I) (hi : i₀ ≤ i),
        IsSeparated B (⊤_ Scheme.{u}) hZ
          (twoFibreProductSquareAlgebraicStacks B (⊤_ Scheme.{u}) hZ f₀
            (algebraicSpaceStackMap.{u, w} B (⊤_ Scheme.{u}) hZ (D.algebraicSpace i)
              (D.algebraicSpace D.base) (D.system.map (homOfLE (h₀.trans hi)).op))).snd)
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
  hasChowCover_of_changeBase.{u, w} B S (⊤_ Scheme.{u}) hS hZ ⟨terminal.from S⟩ hY f
    (hasChowCover_of_forall_isNoetherian B (⊤_ Scheme.{u}) hZ h0CQ2step
      (fun _ hY' hY'qc hY'qs =>
        Space.hasNoetherianApproximation_of_isQuasiCompactSpace hY' hY'qc hY'qs)
      h0CN4 h0CPZ
      (fun _ hY' hY'N _ f' hsep' hft' => HasChowCover.of_forall_isReducedStack
        B (⊤_ Scheme.{u}) hZ
        (fun _ hY'' hY''N _ f'' hred'' hsep'' hft'' =>
          hasChowCover_of_isNoetherian_of_isReducedStack hY'' hY''N f'' hsep'' hft'' hred'')
        hY' hY'N f' hsep' hft')
      (fun _ hY' h => isAbsolutelyQuasiSeparated_algebraicSpaceStack.{u, w}
        B (⊤_ Scheme.{u}) hZ B.contains_terminal hY' h)
      (isAlgebraicSpace_viewOver B S (⊤_ Scheme.{u}) hS hZ ⟨terminal.from S⟩ Y hY)
      (Space.isQuasiCompactSpace_relocalize B S hS hZ ⟨terminal.from S⟩ hYqc)
      (Space.isAbsolutelyQuasiSeparated_relocalize B S (⊤_ Scheme.{u}) hS hZ
        ⟨terminal.from S⟩ hZ Y hYqs)
      (changeBaseToAlgebraicSpace.{u, w} B S (⊤_ Scheme.{u}) hS hZ ⟨terminal.from S⟩ hY f)
      (isSeparated_changeBaseToAlgebraicSpace.{u, w} B S (⊤_ Scheme.{u}) hS hZ
        ⟨terminal.from S⟩ hY f hsep)
      (isFiniteType_changeBaseToAlgebraicSpace.{u, w} B S (⊤_ Scheme.{u}) hS hZ
        ⟨terminal.from S⟩ hY f hft))

end AlgebraicGeometry.Stack.AlgebraicStacks

end
