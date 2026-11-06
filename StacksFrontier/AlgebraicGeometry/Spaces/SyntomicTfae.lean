module

public import Mathlib.Data.List.TFAE
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Syntomic

/-!
# Characterizations of a syntomic morphism of algebraic spaces

Nine conditions on a morphism `f : X ⟶ Y` of algebraic spaces over a scheme `S` are
equivalent: syntomicity in the sense of Tag 03Z7, syntomicity at every point of the source,
syntomicity of every scheme-valued base change, syntomicity of every *affine* scheme-valued
base change, syntomicity of one surjective étale base change, syntomicity of the composite
with one surjective étale chart of the source, the chart conditions (1) and (2) of Tag 03MJ
for syntomic morphisms of schemes, and syntomicity over a pair of Zariski coverings of the
target and of the preimages.

## Main results

* `AlgebraicGeometry.Space.isSyntomic_tfae`: **Stacks 03ZA**.

## Implementation notes

The equivalences are not reproved here. `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae`
is Tag 03MM for an arbitrary property `P` of morphisms of schemes that is étale local on the
source and target, stable under composition and under base change, and implied by étaleness,
and Tag 03ZA is its instance at `AlgebraicGeometry.Syntomic`: those four hypotheses are the
syntomic case of Tag 04R3, Tag 01UH, Tag 01UI and Tag 01VD. Condition (2) of Tag 03ZA is
`AlgebraicGeometry.Space.IsSyntomicAt`, which unfolds to condition (2) of Tag 03MM.

The statement is in its own module rather than beside the other permanence properties of
syntomic morphisms of algebraic spaces, in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Syntomic.lean`: the general criterion lives in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Flat.lean`, which already imports that file.
`StacksFrontier/AlgebraicGeometry/Spaces/SmoothTfae.lean` holds the smooth analogue, Tag 03ZF,
for the same reason.

Inside the namespace `AlgebraicGeometry.Space` the scheme-morphism class `Syntomic` and the
scheme-level lemmas about it are written with an explicit `_root_.`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Syntomic.lean`, because the unqualified names
would be read in the `Space` namespace.

## References

* [Stacks Project, Tag 01UH](https://stacks.math.columbia.edu/tag/01UH)
* [Stacks Project, Tag 01UI](https://stacks.math.columbia.edu/tag/01UI)
* [Stacks Project, Tag 01VD](https://stacks.math.columbia.edu/tag/01VD)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
* [Stacks Project, Tag 03MM](https://stacks.math.columbia.edu/tag/03MM)
* [Stacks Project, Tag 03Z7](https://stacks.math.columbia.edu/tag/03Z7)
* [Stacks Project, Tag 03ZA](https://stacks.math.columbia.edu/tag/03ZA)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_syntomicTfae :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_syntomicTfae
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_syntomicTfae B S hS).has_limit _

/-- **Stacks 03ZA.** Nine criteria for a morphism of algebraic spaces over `S` to be syntomic:
pointwise syntomicity, syntomicity of every base change to a scheme or to an affine scheme or
to one surjective étale chart of the target, syntomicity of the composite with one surjective
étale chart of the source, syntomicity of the morphism of schemes in every — or in one
surjective — commuting square of étale charts, or over a pair of Zariski coverings.

Syntomicity of morphisms of schemes is étale local on the source and target (Tag 04R3), stable
under composition ([Stacks Project, Tag 01UH]) and under base change
([Stacks Project, Tag 01UI]), and implied by étaleness ([Stacks Project, Tag 01VD]), so this
is the instance of `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_tfae` — Tag 03MM for an
arbitrary such property — at that property. Condition (2) is
`AlgebraicGeometry.Space.IsSyntomicAt`, which is by definition condition (2) of that
theorem. -/
@[stacks 03ZA]
theorem isSyntomic_tfae (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE [
      IsSyntomic B S hS f,
      ∀ x : points B S hS X, IsSyntomicAt B S hS f x,
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsSyntomic B S hS (pullback.fst g f),
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) → IsSyntomic B S hS (pullback.fst g f),
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧ IsSyntomic B S hS (pullback.fst g f),
      ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsSurjective B S hS p ∧ IsEtale B S hS p ∧ IsSyntomic B S hS (p ≫ f),
      ∀ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p → IsEtale B S hS q → p ≫ f = yoneda.map a ≫ q →
          IsSyntomic B S hS (yoneda.map a),
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧ IsSyntomic B S hS (yoneda.map a),
      ∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, IsSyntomic B S hS ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι)
    ] :=
  holdsOnEveryEtaleChart_tfae B S hS
    (@_root_.AlgebraicGeometry.Syntomic.{u} : MorphismProperty Scheme.{u})
    _root_.AlgebraicGeometry.syntomic_isEtaleLocalOnSourceAndTarget inferInstance inferInstance
    (fun g hg => have := hg; _root_.AlgebraicGeometry.syntomic_of_etale g) hX hY f

end AlgebraicGeometry.Space

end
