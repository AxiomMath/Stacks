module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompactificationMap
public import
  StacksFrontier.AlgebraicGeometry.Duality.UpperShriekAffineComparison.OpenImmersionRestriction
import StacksCore.Tactic.StacksAttribute

/-!
# The upper shriek functor commutes with restriction to opens

In Situation [Stacks, Tag 0F42] let `j : U ⟶ X` and `j' : V ⟶ Y` be open immersions in `FTS S`
and `f : X ⟶ Y`, `g : U ⟶ V` morphisms with `j ≫ f = g ≫ j'`. Then
`j^* ∘ f^! ≅ g^! ∘ (j')^*` on `D⁺_QCoh(𝒪_Y)` ([Stacks, Tag 0G4J]). Following the source, both
sides are `h^!` for `h = j ≫ f = g ≫ j'`: `(j ≫ f)^! ≅ j^* ∘ f^!` at the compactification of
`j ≫ f` restricted from one of `f`, `(g ≫ j')^! ≅ g^! ∘ (j')^!` by the composition isomorphism,
and `(j')^! ≅ (j')^*` by [Stacks, Tag 0AU0].

## References

* [Stacks Project, Tag 0G4J](https://stacks.math.columbia.edu/tag/0G4J)
* [Stacks Project, Tag 0AU0](https://stacks.math.columbia.edu/tag/0AU0)
* [Stacks Project, Tag 0BV2](https://stacks.math.columbia.edu/tag/0BV2)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Duality

variable {S : Scheme.{u}} [IsNoetherian S] {U X V Y : FTS S} (j : U ⟶ X) (f : X ⟶ Y)
  (g : U ⟶ V) (j' : V ⟶ Y) [IsOpenImmersion j.left] [IsOpenImmersion j'.left]
  (w : j ≫ f = g ≫ j') (cf : CompactificationOf (Over.mk f.left))
  (cg : CompactificationOf (Over.mk g.left))

/-- **Stacks Project, Tag 0G4J (Lemma 48.17.2).** In Situation 48.16.1 let
`j : U ⟶ X`, `j' : V ⟶ Y` be open immersions and `f : X ⟶ Y`, `g : U ⟶ V` morphisms of
`FTS S` with `j ≫ f = g ≫ j'`. Then `j^* ∘ f^! ≅ g^! ∘ (j')^*` as functors on
`D⁺_QCoh(𝒪_Y)`, for arbitrary compactifications `cf` of `f` and `cg` of `g` computing `f^!` and
`g^!`; here `j^*`, `(j')^*` are the restrictions to the opens.

This is also the first assertion of [Stacks, Tag 0BV2] (Remark 48.17.5): for open
`U ⊆ X`, `V ⊆ Y` with `f(U) ⊆ V` and `g` the restriction of `f`, `(f^!E)|_U = g^!(E|_V)` for
`E ∈ D⁺_QCoh(𝒪_Y)`, stated here for arbitrary open immersions and compactifications. -/
@[stacks 0G4J, stacks 0BV2 "part (a): (f^!E)|_U ≅ g^!(E|_V) for E in D^+_QCoh, every open square \
  and every pair of compactifications"]
def upperShriekRestrictIso :
    (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙ upperShriek f cf ⋙
        OpenImmersion.restrictedDerivedRestrict j.left ≅
      (ObjectProperty.ι _ : quasiCoherentDerivedCategoryPlusOfModel Y.left ⥤ _) ⋙
        OpenImmersion.restrictedDerivedRestrict j'.left ⋙ upperShriek g cg :=
  Functor.isoWhiskerLeft _ (Functor.isoWhiskerLeft _
      (restrictedDerivedRestrictIsoQuasiCoherentDerivedPullback j.left) ≪≫
      (upperShriekPrecompOpenIso j f cf).symm) ≪≫
    (upperShriekPlusCompιIso (j ≫ f) (cf.precompOpen j.left)).symm ≪≫
    Functor.isoWhiskerRight (upperShriekPlusCongr w (cf.precompOpen j.left)
      (w ▸ cf.precompOpen j.left) ≪≫
      upperShriekCompIso g j' cg (openCompactification j') _) (ObjectProperty.ι _) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (upperShriekPlusCompιIso g cg) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (upperShriekPlusCompιIso j' (openCompactification j') ≪≫
      Functor.isoWhiskerLeft _ (upperShriekIsoRestrictOfOpenImmersion j')) _ ≪≫
    Functor.associator _ _ _

end Stacks.Duality

end
