module

public import StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.InvertibleSubSplitting
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.StandingSituation

/-!
# Splitting off an invertible submodule over the projective bundle of the dual (weak setting)

Splitting an invertible submodule off by passing to the projective bundle of the dual, in the
weak standing situation. The results of
`StacksFrontier.AlgebraicGeometry.WeilCohomology.ChernClasses.InvertibleSubSplitting`, stated for
`Stacks.WeilCohomology.Weak.ChernSetup`: the standing situation of Stacks Section 45.12 in which
the projective bundle formula, condition (4), is only asked to be injective and to resolve the
top power `c₁^A(𝒪_P(1))^{r+1}` of the twist class (see
`StacksFrontier.AlgebraicGeometry.WeilCohomology.WeakChernClasses.Situation`, which explains why Tag
0FIE needs this generality). The arguments use condition (4) only through these two properties.

## References

* [Stacks Project, Tag 0FI5](https://stacks.math.columbia.edu/tag/0FI5)
* [Stacks Project, Tag 0FI4](https://stacks.math.columbia.edu/tag/0FI4)
* [Stacks Project, Tag 0FV8](https://stacks.math.columbia.edu/tag/0FV8)
* [Stacks Project, Tag 02N4](https://stacks.math.columbia.edu/tag/02N4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u v v₁ w

namespace Stacks.WeilCohomology.Weak

/-! ### The constant rank of the middle term of a short exact sequence -/

namespace ChernSituation

variable {C : Type w} [Category.{v₁} C] {S : C ⥤ Scheme.{u}}
  (𝔗 : ChernSituation.{u, v, v₁, w} C S)

/-- **"It suffices to check this after pulling back by the morphism `𝐏(ℰ^∨) → X`; thus we may
assume we have an invertible submodule `ℒ ⊂ ℰ` such that both `ℰ/ℒ` and `ℱ/ℒ` are finite locally
free"** — the sentence of Tag 0FI5's proof of the Whitney formula in arbitrary rank, proved.

The object `P` is the projective bundle of `ℰ^∨`, an object of `𝒞` by clause (3)(a), and
injectivity of `p^*` on `A` is `Stacks.WeilCohomology.Weak.ChernSetup.injective_pull_proj`, a
consequence of the projective bundle formula and not a further assumption. The three sequences
are `Stacks.WeilCohomology.exists_splitInvertibleSub_of_bundleDatum`, which is pure sheaf
theory. -/
theorem exists_splitInvertibleSub (X : C) (T : ShortComplex (S.obj X).Modules) (hT : T.ShortExact)
    (r b c : ℕ)
    (hE : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₁ (r + 1 + 1))
    (hF : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₂ b)
    (hG : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} T.X₃ c) :
    ∃ (P : C) (p : P ⟶ X), Function.Injective (𝔗.pull p) ∧
      ∃ (L E' F' : (S.obj P).Modules)
        (_ : AlgebraicGeometry.SheafOfModules.IsInvertible (S.obj P).presheaf
          (S.obj P).ringCatSheaf.2 L)
        (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E' (r + 1))
        (s : ℕ)
        (_ : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} F' s)
        (iE : L ⟶ (Scheme.Modules.pullback (S.map p)).obj T.X₁)
        (qE : (Scheme.Modules.pullback (S.map p)).obj T.X₁ ⟶ E') (wE : iE ≫ qE = 0)
        (iF : L ⟶ (Scheme.Modules.pullback (S.map p)).obj T.X₂)
        (qF : (Scheme.Modules.pullback (S.map p)).obj T.X₂ ⟶ F') (wF : iF ≫ qF = 0)
        (fQ : E' ⟶ F') (gQ : F' ⟶ (Scheme.Modules.pullback (S.map p)).obj T.X₃)
        (wQ : fQ ≫ gQ = 0),
        (ShortComplex.mk iE qE wE).ShortExact ∧ (ShortComplex.mk iF qF wF).ShortExact ∧
          (ShortComplex.mk fQ gQ wQ).ShortExact :=
  have hEd := isFiniteLocallyFreeOfRank_dualSheaf T.X₁ (r + 1 + 1) hE
  ⟨(𝔗.bundleDatum X (dualSheaf T.X₁) (r + 1) hEd).bundle,
    (𝔗.bundleDatum X (dualSheaf T.X₁) (r + 1) hEd).proj,
    𝔗.injective_pull_proj X (dualSheaf T.X₁) (r + 1) hEd,
    exists_splitInvertibleSub_of_bundleDatum X T hT r b c hE hF hG
      (𝔗.bundleDatum X (dualSheaf T.X₁) (r + 1) hEd)⟩

end ChernSituation

end Stacks.WeilCohomology.Weak

end
