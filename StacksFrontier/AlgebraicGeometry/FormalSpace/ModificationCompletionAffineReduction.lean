module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.CompletionMorphismAffineChartFactorization
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ModificationCompletionAffineCharts

/-!
# The existence half of Stacks 0GI3 reduces to affine Noetherian charts

Let `X` be a locally Noetherian algebraic space over `S`, `T ⊆ |X|` closed with open complement
`U`, `f : X' ⟶ X` proper with `f⁻¹(U) ⟶ U` an isomorphism, and `(w', ŵ)` a compatible pair of
morphisms `X' ⟶ W`, `X_{/T} ⟶ W` to an algebraic space `W`. This file shows that a morphism
`w : X ⟶ W` restricting to `(w', ŵ)` exists as soon as the affine form of the existence
statement holds: over a Noetherian affine `V` mapping into an affine open `O` of `S`, with the
formal morphism factoring through an affine `W₀` over `O`.

## Main results

* `AlgebraicGeometry.Space.exists_morToModificationCompletion_eq_of_forall_affine`: the
  reduction.

## Implementation notes

A locally Noetherian atlas `p : Va ⟶ X` exists by hypothesis. Every point of `Va` over `T` has
an affine Noetherian étale chart on which the base change of `ŵ` factors through an affine
étale chart of `W`
(`AlgebraicGeometry.Space.exists_affine_chart_completion_factorization`), which is the input of
`AlgebraicGeometry.Space.exists_morToModificationCompletion_eq_of_affine_charts`.

## References

* [Stacks Project, Tag 0GI3](https://stacks.math.columbia.edu/tag/0GI3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_modificationCompletionAffineReduction :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_modificationCompletionAffineReduction
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The existence half of Stacks 0GI3 reduces to affine Noetherian charts.** Let `X`, `T`,
`f`, `W` be as in Stacks 0GI3, with `X` locally Noetherian, `f` proper and an isomorphism over
the open complement of `T`, and let `(w', ŵ)` be a compatible pair. Suppose that the affine
existence statement `hlocal` holds: over every Noetherian affine site object `V` mapping into
an affine open `O` of `S`, for every proper `f₁ : X'₁ ⟶ V` which is an isomorphism over the
complement of a closed `T₁`, every compatible pair whose formal component factors as `ŵ₀ ≫ π`
through an affine site object `W₀` over `O` comes from a morphism `V ⟶ W`. Then there is
`w : X ⟶ W` restricting to `w'` on `X'` and to `ŵ` on `X_{/T}`. -/
theorem exists_morToModificationCompletion_eq_of_forall_affine
    {X' X W : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hX' : IsAlgebraicSpace B S hS X')
    (hW : IsAlgebraicSpace B S hS W)
    (hXnoeth : HasEtaleLocalProperty B S hS X (fun V : Scheme.{u} => IsLocallyNoetherian V))
    {T : Set (points B S hS X)} (hT : IsClosed T)
    (f : X' ⟶ X) (hfproper : IsProper B S hS f)
    (hfU : IsIso (pullback.snd f (openSubspaceOfPoints B S hS X Tᶜ).ι))
    (hlocal : ∀ (V W₀ : BigFppfOver B S hS) (O : S.Opens), IsAffineOpen O →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
      IsNoetherian ((BigFppfOver.toScheme B S hS).obj V) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj W₀) →
      Set.range (B.inclusion.map V.hom).base ⊆ (O : Set S) →
      Set.range (B.inclusion.map W₀.hom).base ⊆ (O : Set S) →
      ∀ {X'₁ : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS X'₁ →
      ∀ {T₁ : Set (points B S hS (yoneda.obj V))}, IsClosed T₁ →
      ∀ (f₁ : X'₁ ⟶ yoneda.obj V), IsProper B S hS f₁ →
      IsIso (pullback.snd f₁ (openSubspaceOfPoints B S hS (yoneda.obj V) T₁ᶜ).ι) →
      ∀ (π : yoneda.obj W₀ ⟶ W) (w'₁ : X'₁ ⟶ W)
        (ŵ₀ : (completionSubfunctor B S hS (yoneda.obj V) T₁).toFunctor ⟶
          yoneda.obj W₀ ⋙ uliftFunctor.{u + 1}),
      completionMap B S hS f₁ T₁ ≫ ŵ₀ ≫ Functor.whiskerRight π uliftFunctor.{u + 1} =
        (completionSubfunctor B S hS X'₁ (pointsMap B S hS X'₁ f₁ ⁻¹' T₁)).ι ≫
          Functor.whiskerRight w'₁ uliftFunctor.{u + 1} →
      ∃ w₁ : yoneda.obj V ⟶ W, morToModificationCompletion B S hS f₁ T₁ W w₁ =
        (w'₁, ŵ₀ ≫ Functor.whiskerRight π uliftFunctor.{u + 1}))
    (w' : X' ⟶ W)
    (ŵ : (completionSubfunctor B S hS X T).toFunctor ⟶ W ⋙ uliftFunctor.{u + 1})
    (hcompat : completionMap B S hS f T ≫ ŵ =
      (completionSubfunctor B S hS X' (pointsMap B S hS X' f ⁻¹' T)).ι ≫
        Functor.whiskerRight w' uliftFunctor.{u + 1}) :
    ∃ w : X ⟶ W, morToModificationCompletion B S hS f T W w = (w', ŵ) := by
  obtain ⟨Va, p, hpsurj, hpet, hVnoeth⟩ := id hXnoeth
  have : IsLocallyNoetherian ((BigFppfOver.toScheme B S hS).obj Va) := hVnoeth
  exact exists_morToModificationCompletion_eq_of_affine_charts B S hS hX hX' hW hXnoeth hT f
    hfproper hfU hlocal w' ŵ hcompat p hpsurj hpet
    fun v hv => exists_affine_chart_completion_factorization B S hS hW hT ŵ p v hv

end Space

end AlgebraicGeometry

end
