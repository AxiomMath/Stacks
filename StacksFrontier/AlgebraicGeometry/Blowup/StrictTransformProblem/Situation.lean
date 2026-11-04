module

public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformModule
public import StacksFrontier.AlgebraicGeometry.Blowup.StrictTransformRetrocompact

/-!
# The strict-transform problem

Fix a quasi-compact and quasi-separated base scheme `S`, a quasi-coherent module `F` on a
scheme `X` over `S`, and a quasi-compact open `U ⊆ S`. Let `P` be a property of pairs
(morphism, module) which is invariant under isomorphism of such pairs and which persists after
a blowup admissible over the inverse image of `U` and the passage to strict transforms. The
*strict-transform problem* asks for a `U`-admissible blowup of `S` after which the transformed
triple has the property `P`.

This is the shape in which the three reductions of [Stacks, Tag 080Y] are stated: each of them
replaces one strict-transform problem by another, and the stability of `P` is what lets the
replacement be undone.

## Main definitions

* `AlgebraicGeometry.StrictTransformProblem` bundles the standing data and the stability of the
  property.
* `AlgebraicGeometry.StrictTransformProblem.IsSolvable` is the existence of a `U`-admissible
  centre whose strict transform has the property.

## Implementation notes

The strict transform of the triple is `Stacks.Blowup.strictTransformMap` and
`Stacks.Blowup.strictTransformModule`: the module lives on the strict transform `X'` itself,
not on the ambient base change `X ×_S S'`. Blowups are indexed by their centres, so the
transformed scheme and module are canonical; an admissible *morphism* alone does not determine
a strict transform.

For a scheme over the original base the distinguished open is always the inverse image of `U`.
This makes the stability hypothesis apply after restriction to an open and after successive
admissible blowups.

## References

* [Stacks Project, Tag 080Y](https://stacks.math.columbia.edu/tag/080Y)
* [Stacks Project, Tag 080D](https://stacks.math.columbia.edu/tag/080D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- The standing situation for the strict-transform problem: a quasi-coherent module on a
scheme over a quasi-compact and quasi-separated base, a quasi-compact open of the base, and a
property of pairs (morphism, module) that is invariant under isomorphism and stable under
admissible strict transform. -/
structure StrictTransformProblem where
  /-- The base scheme. -/
  S : Scheme.{u}
  [compactSpace : CompactSpace S]
  [quasiSeparatedSpace : QuasiSeparatedSpace S]
  /-- The scheme carrying the module. -/
  X : Scheme.{u}
  /-- The structure morphism of the triple. -/
  f : X ⟶ S
  /-- The module to be transformed. -/
  F : X.Modules
  [quasicoherent : F.IsQuasicoherent]
  /-- The open over which the blowups are required to be isomorphisms. -/
  U : S.Opens
  /-- The distinguished open is quasi-compact. -/
  compact_U : IsCompact (U : Set S)
  /-- The property sought for the transformed triple. -/
  P : {Y T : Scheme.{u}} → (Y ⟶ T) → Y.Modules → Prop
  /-- The property depends only on the isomorphism class of the pair. -/
  invariant_under_iso : ∀ {Y T Y₂ T₂ : Scheme.{u}}
    (g : Y ⟶ T) (g₂ : Y₂ ⟶ T₂) (G : Y.Modules) (G₂ : Y₂.Modules)
    (eY : Y ≅ Y₂) (eT : T ≅ T₂), g ≫ eT.hom = eY.hom ≫ g₂ →
      (G ≅ (Scheme.Modules.pullback eY.hom).obj G₂) → (P g G ↔ P g₂ G₂)
  /-- The property persists under the strict transform along a blowup whose centre is
  admissible relative to the inverse image of the distinguished open. -/
  stable : ∀ {Y T : Scheme.{u}} [CompactSpace T] [QuasiSeparatedSpace T]
    (g : Y ⟶ T) (G : Y.Modules) [G.IsQuasicoherent] (p : T ⟶ S)
    (_hV : IsCompact ((p ⁻¹ᵁ U : T.Opens) : Set T)) (I : T.IdealSheafData),
    FinitePresentation I.subschemeι →
      Disjoint ((p ⁻¹ᵁ U : T.Opens) : Set T) (I.support : Set T) →
        P g G → P (Stacks.Blowup.strictTransformMap g I)
          (Stacks.Blowup.strictTransformModule g I G)

attribute [instance] StrictTransformProblem.compactSpace
  StrictTransformProblem.quasiSeparatedSpace StrictTransformProblem.quasicoherent

/-- The strict-transform problem is **solvable** if some `U`-admissible centre makes the
strict-transformed triple satisfy the required property. -/
def StrictTransformProblem.IsSolvable (D : StrictTransformProblem.{u}) : Prop :=
  ∃ I : D.S.IdealSheafData, FinitePresentation I.subschemeι ∧
    Disjoint (D.U : Set D.S) (I.support : Set D.S) ∧
      D.P (Stacks.Blowup.strictTransformMap D.f I)
        (Stacks.Blowup.strictTransformModule D.f I D.F)

/-- If the original triple already has the property, the strict-transform problem is solvable. -/
theorem StrictTransformProblem.isSolvable_of_property (D : StrictTransformProblem.{u})
    (hP : D.P D.f D.F) : D.IsSolvable := by
  refine ⟨⊤, Stacks.Blowup.finitePresentation_subschemeι_top, by simp, ?_⟩
  refine D.stable D.f D.F (𝟙 D.S) ?_ ⊤ Stacks.Blowup.finitePresentation_subschemeι_top
    (by simp) hP
  simpa using D.compact_U

end AlgebraicGeometry

end
