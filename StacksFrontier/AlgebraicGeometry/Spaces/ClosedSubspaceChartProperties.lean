module

public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantClosedSubschemeGlueing

/-!
# Properties of a subspace over a scheme read on a subscheme of a chart

Let `π : P ⟶ T` be a morphism from an algebraic space to (the functor of points of) a scheme `T`
of a big fppf site, let `φ : U ⟶ P` be an étale chart with structure morphism `ψ : U ⟶ T`, and
let `W ⊆ P` be a subfunctor whose inverse image along `φ` is the functor of points of an immersed
subscheme `C ⊆ U`. Then `C` is an étale chart of `W`, so a property `Q` of morphisms of schemes
which is étale local on source and target holds for `W ⟶ T` in the sense of Stacks 03MJ as soon as
it holds for `C ⟶ T` and `φ` is surjective, and conversely `C ⟶ T` has `Q` whenever `W ⟶ T` does.

## Main results

* `AlgebraicGeometry.Space.prop_arrow_comp_of_holdsOnEveryEtaleChart`: from the subspace to the
  subscheme of the chart.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_prop_arrow_comp`: from the subscheme of a
  surjective chart to the subspace.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {P₀ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {T U : BigFppfOver B S hS}
    (π : P₀ ⟶ yoneda.obj T) {φ : yoneda.obj U ⟶ P₀} (ψ : U ⟶ T)
    (hψ : yoneda.map ψ = φ ≫ π) {W : Subfunctor P₀}
    {C : Subobject ((BigFppfOver.toScheme B S hS).obj U)}
    (hC : AlgebraicGeometry.IsImmersion C.arrow)
    (hWC : W.preimage φ = subschemePoints B S hS C)

include hψ hC hWC in
/-- **The subscheme of the chart inherits the properties of the subspace.** -/
theorem prop_arrow_comp_of_holdsOnEveryEtaleChart (Q : MorphismProperty Scheme.{u})
    [Q.RespectsIso]
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (h : HoldsOnEveryEtaleChart B S hS Q (W.ι ≫ π)) :
    Q (C.arrow ≫ (BigFppfOver.toScheme B S hS).map ψ) := by
  obtain ⟨V, i, e, hei⟩ := exists_presentation B S hS C hC
  obtain ⟨k, hk⟩ := exists_isPullback_yoneda_of_preimage_eq B S hS hWC i e hei
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _
  have hke := MorphismProperty.of_isPullback hk.flip he
  have := isMultiplicative_presheaf_etale B S hS
  have hQ := h V T k (𝟙 _) (i ≫ ψ) hke (MorphismProperty.id_mem _ _) (by
    rw [Category.comp_id, ← Category.assoc, hk.w, Category.assoc, ← hψ, Functor.map_comp])
  rw [Functor.map_comp, ← hei, Category.assoc] at hQ
  exact (MorphismProperty.cancel_left_of_respectsIso Q e.hom _).1 hQ

include hψ hC hWC in
/-- **The subspace inherits the properties of the subscheme of a surjective chart.** -/
theorem holdsOnEveryEtaleChart_of_prop_arrow_comp (Q : MorphismProperty Scheme.{u})
    [Q.RespectsIso] (hQ : IsEtaleLocalOnSourceAndTarget Q)
    (hW : IsAlgebraicSpace B S hS W.toFunctor)
    (hs : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (he : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) φ)
    (h : Q (C.arrow ≫ (BigFppfOver.toScheme B S hS).map ψ)) :
    HoldsOnEveryEtaleChart B S hS Q (W.ι ≫ π) := by
  obtain ⟨V, i, e, hei⟩ := exists_presentation B S hS C hC
  obtain ⟨k, hk⟩ := exists_isPullback_yoneda_of_preimage_eq B S hS hWC i e hei
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _
  have : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).IsStableUnderBaseChange :=
    MorphismProperty.relative_isStableUnderBaseChange (F := yoneda) _
  have := isMultiplicative_presheaf_etale B S hS
  refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS Q hQ hW
    (isAlgebraicSpace_yoneda B S hS T) _).2
    ⟨V, T, k, 𝟙 _, i ≫ ψ, MorphismProperty.of_isPullback hk.flip he,
      MorphismProperty.id_mem _ _, MorphismProperty.of_isPullback hk.flip hs, ?_, ?_⟩
  · rw [Category.comp_id, ← Category.assoc, hk.w, Category.assoc, ← hψ, Functor.map_comp]
  · rw [Functor.map_comp, ← hei, Category.assoc]
    exact (MorphismProperty.cancel_left_of_respectsIso Q e.hom _).2 h

end AlgebraicGeometry.Space

end
