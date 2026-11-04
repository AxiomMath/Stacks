module

public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.AugmentationCartesianModule
import StacksCore.Tactic.StacksAttribute

/-!
# `a_m ∘ f_φ = a_n` for a ringed augmentation

Let `S` be a simplicial-site situation, `a` an augmentation of `S` towards a site `(D, K)` and
`A` a ringed augmentation of Stacks 0D9D. For a simplex map `φ : [m] ⟶ [n]` the source asserts
the identity `a_m ∘ f_φ = a_n` of morphisms of *ringed* topoi, and uses it as the whole reason
for Stacks 0D7H. This module supplies that identity in the form an equality of morphisms of
ringed topoi takes in this development: a 2-isomorphism of Stacks 04IC.

## Main definitions

* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.componentRingedTwoIsoAux`: the
  2-morphism `g_n ⟶ g_m ∘ f_φ` with the augmentation appended, as a 2-isomorphism.
* `CategoryTheory.SimplicialSiteSituation.RingedAugmentation.componentRingedTwoIso`:
  **`a_m ∘ f_φ = a_n`**, as a 2-isomorphism of morphisms of ringed topoi.

## The argument

The 2-morphism `g_n ⟶ g_m ∘ f_φ` of morphisms of ringed topoi attached to a simplex map is
`CategoryTheory.SimplicialSiteSituation.componentRingedTwoMorphism`, and it is *not* invertible:
the component inclusions do not agree after a simplicial transition. What the source's identity
says is that it becomes invertible once the augmentation is appended, and that is exactly
`CategoryTheory.SimplicialSiteSituation.Augmentation`
`.isIso_whiskerRight_componentPushforwardTransition`, which rests on Stacks 0D7H (1).

So the construction is: whisker the 2-morphism on the right by `a`
(`AlgebraicGeometry.RingedToposHom.TwoMorphism.whiskerRight`), promote the result to a
2-isomorphism by that invertibility
(`AlgebraicGeometry.RingedToposHom.TwoMorphism.toTwoIso`), and reassociate `a ∘ (g_m ∘ f_φ)`
into `(a ∘ g_m) ∘ f_φ = a_m ∘ f_φ` (`AlgebraicGeometry.RingedToposHom.TwoIso.associator`). The
source `a ∘ g_n` of the whiskering is `a_n` on the nose, the component augmentation being
defined as that composite.

Nothing is assumed beyond what Stacks 0D7H (1) already gives, and in particular the structure
maps need no separate coherence: the compatibility clause of the whiskered 2-morphism is the
compatibility clause of `componentRingedTwoMorphism` with `a^♯` prepended, and the associator's
is an associativity of three structure maps.

## References

* [Stacks Project, Section 85.10 (Tag 0D9D)](https://stacks.math.columbia.edu/tag/0D9D)
* [Stacks Project, Tag 0D7H](https://stacks.math.columbia.edu/tag/0D7H)
* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
* [Stacks Project, Tag 04IC](https://stacks.math.columbia.edu/tag/04IC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace CategoryTheory.SimplicialSiteSituation.RingedAugmentation

variable {S : SimplicialSiteSituation.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  {a : Augmentation S D K} (A : RingedAugmentation S D K a)

/-- **`a ∘ g_n ⟶ a ∘ (g_m ∘ f_φ)` is invertible.** The 2-morphism `g_n ⟶ g_m ∘ f_φ` of
Stacks 04IC with the ringed augmentation appended on the right: a 2-*isomorphism*, because
appending the augmentation is exactly what makes it invertible.

Its underlying transformation of direct images is the 2-morphism of sheaves of sets with `a_*`
appended, which Stacks 0D7H (1) makes invertible through
`CategoryTheory.SimplicialSiteSituation.Augmentation`
`.isIso_whiskerRight_componentPushforwardTransition`. -/
def componentRingedTwoIsoAux {m n : SimplexCategory} (φ : m ⟶ n) :
    AlgebraicGeometry.RingedToposHom.TwoIso.{u, u, u, u, u, u}
      (A.componentRingedHom n)
      (AlgebraicGeometry.RingedToposHom.comp (X := S.componentRingedTopos A.O n)
        (Y := S.totalRingedTopos A.O) (Z := A.augmentationRingedTopos) A.totalRingedHom
        (AlgebraicGeometry.RingedToposHom.comp (X := S.componentRingedTopos A.O n)
          (Y := S.componentRingedTopos A.O m) (Z := S.totalRingedTopos A.O)
          (componentRingedToposHom S A.O m) (S.transitionRingedToposHom A.O φ))) :=
  ((S.componentRingedTwoMorphism A.O φ).whiskerRight A.totalRingedHom).toTwoIso
    (Augmentation.isIso_whiskerRight_componentPushforwardTransition S D K a φ)

/-- **`a_m ∘ f_φ = a_n`, as a 2-isomorphism of morphisms of ringed topoi.** For every simplex map
`φ : [m] ⟶ [n]` the canonical 2-morphism `a_n ⟶ a_m ∘ f_φ` is invertible. This is the identity
the source's proof of Stacks 0D7H appeals to, read for morphisms of ringed topoi.

It is `componentRingedTwoIsoAux` followed by the reassociation of `a ∘ (g_m ∘ f_φ)` into
`(a ∘ g_m) ∘ f_φ = a_m ∘ f_φ`; the source `a ∘ g_n` is `a_n` on the nose. -/
@[stacks 0D9D "`a_m ∘ f_φ = a_n`, as a 2-isomorphism of the morphisms of ringed topoi"]
def componentRingedTwoIso {m n : SimplexCategory} (φ : m ⟶ n) :
    AlgebraicGeometry.RingedToposHom.TwoIso.{u, u, u, u, u, u}
      (A.componentRingedHom n)
      (AlgebraicGeometry.RingedToposHom.comp (X := S.componentRingedTopos A.O n)
        (Y := S.componentRingedTopos A.O m) (Z := A.augmentationRingedTopos)
        (A.componentRingedHom m) (S.transitionRingedToposHom A.O φ)) :=
  (A.componentRingedTwoIsoAux φ).trans
    (AlgebraicGeometry.RingedToposHom.TwoIso.associator (S.transitionRingedToposHom A.O φ)
      (componentRingedToposHom S A.O m) A.totalRingedHom)

end CategoryTheory.SimplicialSiteSituation.RingedAugmentation

end
