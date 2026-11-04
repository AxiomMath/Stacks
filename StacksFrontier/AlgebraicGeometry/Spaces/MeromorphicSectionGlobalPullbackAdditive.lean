module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SectionsAddCommGroup
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramCofinal
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineChartDiagramSieveRefinement
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionCanonicalValue
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackLinear
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionGlobalPullbackValue
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionTrivialChart
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionValueDescent
import StacksCore.Tactic.StacksAttribute

/-!
# The global pullback map on meromorphic sections is additive

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` for which pullbacks of
meromorphic functions are defined (Stacks 0EN8) and let `M` be a sheaf of `𝒪_Y`-modules on the
small étale site of `Y`.  The global map

`Γ(Y, 𝒦_Y(M)) ⟶ Γ(X, 𝒦_X(f^*M))`

of Stacks 0ENC, part (1) — `AlgebraicGeometry.Space.pullbackMeromorphicSection` — is built out
of a chartwise rule carried along three identifications, one of which is a *non-canonical*
isomorphism presenting the sheaf on `X` as the restriction of a spaces-étale sheaf of **sets**.
Nothing in that construction is a map of abelian groups, and the map was produced on the
underlying sets for exactly that reason.  This file reads it as a map of abelian groups all the
same.

The chartwise additivity is
`AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_add`, of
`StacksFrontier/AlgebraicGeometry/Spaces/MeromorphicSectionGlobalPullbackLinear.lean`, which states
it of three sections one of whose values is the sum of the other two rather than of a sum of
sections: it predates the group structure, which is what makes `s₁ + s₂` a term at all.  What is
added here is that group structure's consequence — the map is additive on the nose, and so is a
morphism of abelian groups.

## Main results

* `AlgebraicGeometry.Space.eval_add_of_sieve`: an additivity relation between three meromorphic
  sections over a chart follows from the relation over the members of a covering sieve of that
  chart.
* `AlgebraicGeometry.Space.pullbackMeromorphicSection_add`: **the global map of Stacks 0ENC,
  part (1) is additive**, and `AlgebraicGeometry.Space.pullbackMeromorphicSectionAddHom` is it
  bundled as a morphism of abelian groups.

## Implementation notes

The abelian group structure on the meromorphic sections is
`PresheafOfModules.sectionsAddCommGroup`: Mathlib defines the global sections of a presheaf of
modules as the sections of the underlying presheaf of sets, so before that instance `s + t` was
not a term and additivity of the pullback was not a statement.  The relation the chartwise
lemma asks for is then supplied by `PresheafOfModules.sections_eval_add`.

## References

* [Stacks Project, Tag 0ENC](https://stacks.math.columbia.edu/tag/0ENC)
* [Stacks Project, Tag 0EN5](https://stacks.math.columbia.edu/tag/0EN5)
* [Stacks Project, Tag 0EN8](https://stacks.math.columbia.edu/tag/0EN8)
* [Stacks Project, Tag 03G2](https://stacks.math.columbia.edu/tag/03G2)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Additivity of meromorphic sections is local -/

/-- **An additivity relation between three meromorphic sections holds over a chart as soon as it
holds over the members of a covering sieve of that chart.**  This is separatedness of the sheaf
`𝒦_F(N)` of meromorphic sections of Stacks 0EN5
(`AlgebraicGeometry.Space.isSheaf_forget_meromorphicSectionSheaf`) applied to the two sides of
the relation, the restriction maps carrying it from the source of an arrow of the sieve by
`PresheafOfModules.sections_restrictₛₗ_eval_add`. -/
theorem eval_add_of_sieve (X : AlgebraicSpaces B S hS) (N : Modules.{u, u} B S hS X.1 X.2)
    (t t₁ t₂ : MeromorphicSection.{u, u} B S hS X.1 X.2 N)
    (U : SmallEtale B S hS X.1) (T : Sieve U)
    (hT : T ∈ SmallEtale.topology B S hS X.1 U)
    (h : ∀ ⦃W : SmallEtale B S hS X.1⦄ (k : W ⟶ U), T k →
      t.eval (op W) = t₁.eval (op W) + t₂.eval (op W)) :
    t.eval (op U) = t₁.eval (op U) + t₂.eval (op U) :=
  (isSheaf_forget_meromorphicSectionSheaf B S hS X N T hT).isSeparatedFor.ext
    fun {_} k hk ↦ PresheafOfModules.sections_restrictₛₗ_eval_add k.op (h k hk)

/-! ### Additivity of the global pullback -/

section Additive

variable {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (M : Modules.{u, u} B S hS Y.1 Y.2)
  (hf : PullbacksMeromorphicSections B S hS f.hom)
  (s₁ s₂ : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M)

/-- **Stacks 0ENC, part (1) is additive.**  The canonical map on global meromorphic sections

`Γ(Y, 𝒦_Y(M)) ⟶ Γ(X, 𝒦_X(f^*M))`

of `AlgebraicGeometry.Space.pullbackMeromorphicSection` is a map of abelian groups.

The construction of that map passes through presheaves of sets, and through a non-canonical
isomorphism presenting the sheaf on `X` as the restriction of a spaces-étale sheaf of sets, so
nothing in it is additive; additivity is proved instead from the values of the map, which over
the chart of `X` of a square of étale charts are the chartwise rule
`m ⊗ a ↦ (f^*m) ⊗ (f^♯a)` applied to a presentation of the section, and that rule *is* additive.
That chartwise statement is `AlgebraicGeometry.Space.pullbackMeromorphicSection_eval_add`, which
asks for the summand relation on values rather than for a sum of sections, since it predates the
group structure; `PresheafOfModules.sections_eval_add` supplies the relation for `s₁ + s₂`. -/
theorem pullbackMeromorphicSection_add :
    pullbackMeromorphicSection B S hS f M hf (s₁ + s₂) =
      pullbackMeromorphicSection B S hS f M hf s₁ +
        pullbackMeromorphicSection B S hS f M hf s₂ :=
  PresheafOfModules.sections_ext _ _ fun U ↦
    pullbackMeromorphicSection_eval_add B S hS f M hf s₁ s₂ (s₁ + s₂)
      (fun V ↦ PresheafOfModules.sections_eval_add s₁ s₂ (op V)) U.unop

/-- **Stacks 0ENC, part (1) as a morphism of abelian groups.**  The canonical map on global
meromorphic sections `Γ(Y, 𝒦_Y(M)) ⟶ Γ(X, 𝒦_X(f^*M))` of
`AlgebraicGeometry.Space.pullbackMeromorphicSection`, bundled with its additivity
(`AlgebraicGeometry.Space.pullbackMeromorphicSection_add`). -/
noncomputable def pullbackMeromorphicSectionAddHom :
    MeromorphicSection.{u, u} B S hS Y.1 Y.2 M →+
      MeromorphicSection.{u, u} B S hS X.1 X.2 ((modulePullback B S hS f).obj M) :=
  AddMonoidHom.mk' (pullbackMeromorphicSection B S hS f M hf)
    (pullbackMeromorphicSection_add B S hS f M hf)

/-- The bundled map `AlgebraicGeometry.Space.pullbackMeromorphicSectionAddHom` sends a
meromorphic section `s` to `AlgebraicGeometry.Space.pullbackMeromorphicSection` of `s`. -/
@[simp]
theorem pullbackMeromorphicSectionAddHom_apply
    (s : MeromorphicSection.{u, u} B S hS Y.1 Y.2 M) :
    pullbackMeromorphicSectionAddHom B S hS f M hf s =
      pullbackMeromorphicSection B S hS f M hf s := rfl

end Additive

end AlgebraicGeometry.Space

end
