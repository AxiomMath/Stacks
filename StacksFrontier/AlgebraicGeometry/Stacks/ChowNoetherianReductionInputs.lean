module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.ChowLemmaFinitePresentation

/-!
# The inputs of the reduction to the Noetherian case in Chow's lemma for algebraic stacks

The proof of Chow's lemma for algebraic stacks (Stacks 0CQ8) reduces to the Noetherian case by
three results of Limits of Stacks: Stacks 0CQ2 (a separated 1-morphism of finite type to a qcqs
algebraic space is a closed immersion into one of finite presentation), Stacks 0CN4 (an algebraic
stack of finite presentation over a limit of qcqs algebraic spaces with affine transition
morphisms comes from a finite stage) and Stacks 0CPZ (separatedness of the base change to the limit
descends to a finite stage). Each is stated here, as the source states it, as a proposition, one
per declaration; the reduction takes them as inputs.

The two limit statements are read for systems satisfying the chapter's standing convention of
Section 70.2 (tag 07SD), `AlgebraicGeometry.Space.SiteContainsBaseChangeLimits`, under which the
chapter's descent results hold, and with no bound on the size of the index: the Noetherian
approximations of Stacks 07SU satisfy the convention
(`AlgebraicGeometry.Space.hasConventionalNoetherianApproximation_of_etaleAtlas`) but no such bound.
Without the convention the statement of Stacks 0CPZ fails: for the system of spectra of the
finitely generated subrings of a field of size at least the cutoff of the site, indexed by its
finite subsets, the limit in the site is empty
(`Space.SiteConventionCounterexample.not_siteContainsBaseChangeLimits` records that the convention
fails there), so every base change to the limit is separated while the line with doubled origin is
separated at no stage.

They correspond to the following statements:

* `ClosedImmersionIntoFinitePresentationStatement` is the conclusion of
  `AlgebraicGeometry.Stack.exists_separated_finitePresentation_closedImmersion`;
* `FinitePresentationStackDescendsStatement` is
  `StackDescentSystem.exists_stage_model_of_isFinitePresentation_unconditional`, for a system
  satisfying the convention in place of the bound `#I < cof` on the index;
* `SeparatedAtFiniteStageStatement` is
  `Space.DescentSituation.exists_isSeparated_stage_of_siteContainsBaseChangeLimits`.

## References

* [Stacks Project, Tag 0CQ2](https://stacks.math.columbia.edu/tag/0CQ2)
* [Stacks Project, Tag 0CN4](https://stacks.math.columbia.edu/tag/0CN4)
* [Stacks Project, Tag 0CPZ](https://stacks.math.columbia.edu/tag/0CPZ)
* [Stacks Project, Tag 0CQ8](https://stacks.math.columbia.edu/tag/0CQ8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The statement of Stacks 0CQ2.** A separated 1-morphism of finite type `f : 𝒳 ⟶ Y` from an
algebraic stack to a quasi-compact quasi-separated algebraic space factors as a closed immersion
`i : 𝒳 ⟶ 𝒳'` followed by a separated 1-morphism of finite presentation `f' : 𝒳' ⟶ Y`. -/
def ClosedImmersionIntoFinitePresentationStatement : Prop :=
  ∀ (Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY : IsAlgebraicSpace B S hS Y)
    (𝒳 : AlgebraicStacks.{u, w} B S hS) (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY),
    IsFiniteType B S hS f → IsSeparated B S hS f → Space.IsQuasiCompactSpace B S hS Y →
    Space.IsAbsolutelyQuasiSeparated B S hS B.contains_terminal Y →
      ∃ (𝒳' : AlgebraicStacks.{u, w} B S hS)
        (f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (i : 𝒳 ⟶ 𝒳'),
        IsSeparated B S hS f' ∧ IsFinitePresentation B S hS f' ∧
          IsClosedImmersion B S hS i ∧ Nonempty (i ≫ f' ≅ f)

/-- **The statement of Stacks 0CN4.** Let `X = lim X_i` be the limit of a directed system of
quasi-compact quasi-separated algebraic spaces with affine transition morphisms satisfying the
chapter's convention of Section 70.2. Every 1-morphism of finite presentation `f : 𝒳 ⟶ X` from
an algebraic stack is, for some `i`, the base change `X ×_{X_i} 𝒳ᵢ ⟶ X` of a 1-morphism of finite
presentation `fᵢ : 𝒳ᵢ ⟶ X_i`. -/
def FinitePresentationStackDescendsStatement : Prop :=
  ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
    (D : Iᵒᵖ ⥤ (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hX : IsAlgebraicSpace B S hS (limit D)) (hD : ∀ i, IsAlgebraicSpace B S hS (D.obj i))
    (_ : ∀ {i j : Iᵒᵖ} (f : i ⟶ j), Space.IsAffineHom B S hS (D.map f))
    (_ : ∀ i, Space.IsQuasiCompactSpace B S hS (D.obj i))
    (_ : ∀ i, Space.IsAbsolutelyQuasiSeparated B S hS (BigFppfSite.contains_terminal B)
      (D.obj i))
    (_ : Space.SiteContainsBaseChangeLimits B S hS D)
    (𝒳 : AlgebraicStacks.{u, w} B S hS)
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS (limit D) hX),
    IsFinitePresentation B S hS f →
    ∃ (i : Iᵒᵖ) (𝒳ᵢ : AlgebraicStacks.{u, w} B S hS)
      (fᵢ : 𝒳ᵢ ⟶ algebraicSpaceStack.{u, w} B S hS (D.obj i) (hD i)),
      IsFinitePresentation B S hS fᵢ ∧
      ∃ e : Bicategory.Equivalence 𝒳 (twoFibreProductSquareAlgebraicStacks B S hS fᵢ
          (algebraicSpaceStackMap.{u, w} B S hS hX (hD i) (limit.π D i))).pt,
        Nonempty (e.hom ≫ (twoFibreProductSquareAlgebraicStacks B S hS fᵢ
          (algebraicSpaceStackMap.{u, w} B S hS hX (hD i) (limit.π D i))).snd ≅ f)

/-- **The statement of Stacks 0CPZ.** In the situation of a directed limit `Y = lim Y_i` of
quasi-compact quasi-separated algebraic spaces with affine transition morphisms and a distinguished
index `0`, satisfying the chapter's convention of Section 70.2, let `f₀ : 𝒳₀ ⟶ Y₀` be a
1-morphism from a quasi-compact quasi-separated algebraic stack. If the base change
`Y ×_{Y₀} 𝒳₀ ⟶ Y` is separated, then so is `Y_i ×_{Y₀} 𝒳₀ ⟶ Y_i` for all large `i`. -/
def SeparatedAtFiniteStageStatement : Prop :=
  ∀ {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)]
    (D : Space.DescentSituation B S hS (BigFppfSite.contains_terminal B) I),
    (haveI : Nonempty I := ⟨D.base⟩; Space.SiteContainsBaseChangeLimits B S hS D.system) →
    ∀ (𝒳₀ : AlgebraicStacks.{u, w} B S hS)
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
            (D.system.map (homOfLE (h₀.trans hi)).op))).snd

end AlgebraicGeometry.Stack.AlgebraicStacks

end
