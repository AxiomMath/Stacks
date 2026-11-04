module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ShortExactDerivedTrace

/-!
# A twisted endomorphism followed by an endomorphism of the complex

Let `P`, `F₁`, `F₂` be additive functors with `θ : P ⋙ F₁ ≅ F₁`, and let
`CategoryTheory.Functor.derivedTwistEndo` attach to a twist `τ : K ⟶ P(K)` of a bounded below
complex an endomorphism of `RF₂(RF₁(K))`.  For an endomorphism `ψ` of `K`, the twist
`τ ≫ P(ψ)` induces the composite of the endomorphism induced by `τ` with `RF₂(RF₁(ψ))`.

In [Tag 03UG], Step 8, this writes the endomorphism `(g, π^*)` of the compactly supported
cohomology of a sheaf with a deck action as the twisted endomorphism of a single twist, to which
the invariance of twisted traces under finite direct images applies.

## Main results

* `CategoryTheory.Functor.derivedTwistEndo_comp_mapCochainComplexPlus_map`.

## References

* [Stacks Project, Tag 03UG](https://stacks.math.columbia.edu/tag/03UG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CategoryTheory.Functor

attribute [local instance] HasDerivedCategory.standard

universe v₁ u₁

variable {C D : Type u₁} {E : Type*} [Category.{v₁} C] [Category.{v₁} D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E] [EnoughInjectives C] [EnoughInjectives D]
  (P : C ⥤ C) (F₁ : C ⥤ D) (F₂ : D ⥤ E) [P.Additive] [F₁.Additive] [F₂.Additive]
  [P.PreservesInjectiveObjects] (θ : P ⋙ F₁ ≅ F₁)

/-- **The twist `τ ≫ P(ψ)` induces the endomorphism induced by `τ` followed by `RF₂(RF₁(ψ))`.** -/
theorem derivedTwistEndo_comp_mapCochainComplexPlus_map (K : CochainComplex.Plus C)
    (τ : K ⟶ P.mapCochainComplexPlus.obj K) (ψ : K ⟶ K) :
    derivedTwistEndo P F₁ F₂ θ K (τ ≫ P.mapCochainComplexPlus.map ψ) =
      derivedTwistEndo P F₁ F₂ θ K τ ≫
        F₂.rightDerivedFunctorPlus.map
          (F₁.rightDerivedFunctorPlus.map (DerivedCategory.Plus.Q.map ψ)) := by
  have hc := (Stacks.EtaleCohomology.rightDerivedFunctorPlusCompIsoOfIso P F₁ F₁ θ).inv.naturality
    (DerivedCategory.Plus.Q.map ψ)
  have hu := (mapCochainComplexPlusDerivedUnit P).naturality ψ
  dsimp only [Functor.comp_map, Functor.comp_obj] at hc hu
  simp only [derivedTwistEndo, ← Functor.map_comp, Category.assoc]
  congr 1
  conv_rhs => rw [← hc, ← Category.assoc, ← Functor.map_comp, Category.assoc, ← hu,
    ← Category.assoc, ← Functor.map_comp]

end CategoryTheory.Functor

end
