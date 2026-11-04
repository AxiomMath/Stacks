module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteSchemeCoverGraphBasicOpens
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactImageEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompactSchemeTheoreticImageDense
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.DescendingFiniteTypeLimitImage

/-!
# Étale charts over the scheme-theoretic image of a cover

Let `f : Y ⟶ P` be a morphism of algebraic spaces and `g : Γ ⟶ P` an étale morphism whose base
change `Γ ×_P Y ⟶ Y` is a monomorphism. Then `g` is a monomorphism over every closed subspace of
`P` whose points come from `Y`, in the sense of the first property of
`AlgebraicGeometry.Space.IsEtaleSectionClosed`: a pair of points of `Γ` with the same image in
`|f(Y)|` lifts to a pair of points of `Γ ×_P Y` over one point of `Y`, which is on the diagonal.

This is how, in the proof of Stacks 0GUN, the scheme-theoretic image of the integral cover in a
space of finite presentation over `X` inherits the charts on which the cover is a monomorphism.

## Main results

* `AlgebraicGeometry.Space.preimage_le_range_diagonal_of_mono_pullback_snd`.
* `AlgebraicGeometry.Space.schemeTheoreticImageSubfunctor_eq_range_of_isClosedImmersion`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] pointTopology

/-- **An étale morphism which becomes a monomorphism over `Y` is a monomorphism over the points
coming from `Y`.** -/
theorem preimage_le_range_diagonal_of_mono_pullback_snd
    {P Y F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hP : IsAlgebraicSpace B S hS P)
    (hF : IsAlgebraicSpace B S hS F) (g : F ⟶ P) (hg : IsEtale B S hS g) (f : Y ⟶ P)
    (hmono : Mono (pullback.snd g f)) (C : Subfunctor P)
    (hCf : Set.range (pointsMap B S hS C.toFunctor C.ι) ⊆ Set.range (pointsMap B S hS Y f)) :
    C.preimage (pullback.fst g g ≫ g) ≤ Subfunctor.range (pullback.diagonal g) := by
  have hD : IsOpenImmersion B S hS (pullback.diagonal g) :=
    isOpenImmersion_diagonal_of_isUnramified B S hS hF hP g (isUnramified_of_isEtale B S hS hg)
  have _ : Mono (pullback.diagonal g) := inferInstance
  refine le_of_range_pointsMap_ι_subset B S hS
    (isOpenSubspace_range_of_isAlgebraicSpace B S hS hF _ hD) ?_
  rw [range_pointsMap_preimage_ι, range_pointsMap_ι_range]
  intro β hβ
  obtain ⟨y, hy⟩ := hCf hβ
  let ρ : pullback g g ⟶ P := pullback.fst g g ≫ g
  obtain ⟨β', hβ', -⟩ := exists_points_of_isPullback B S hS (IsPullback.of_hasPullback ρ f) β y
    hy.symm
  let m₁ : pullback ρ f ⟶ pullback g f :=
    pullback.lift (pullback.fst ρ f ≫ pullback.fst g g) (pullback.snd ρ f)
      (by rw [Category.assoc, ← pullback.condition])
  let m₂ : pullback ρ f ⟶ pullback g f :=
    pullback.lift (pullback.fst ρ f ≫ pullback.snd g g) (pullback.snd ρ f)
      (by rw [Category.assoc, ← pullback.condition, ← pullback.condition])
  have hm : m₁ = m₂ := by
    rw [← cancel_mono (pullback.snd g f)]
    simp only [m₁, m₂, pullback.lift_snd]
  have hk : pullback.fst ρ f ≫ pullback.fst g g = pullback.fst ρ f ≫ pullback.snd g g := by
    have h₁ : m₁ ≫ pullback.fst g f = pullback.fst ρ f ≫ pullback.fst g g := pullback.lift_fst _ _ _
    have h₂ : m₂ ≫ pullback.fst g f = pullback.fst ρ f ≫ pullback.snd g g := pullback.lift_fst _ _ _
    rw [← h₁, ← h₂, hm]
  have hdiag : pullback.fst ρ f = (pullback.fst ρ f ≫ pullback.fst g g) ≫ pullback.diagonal g := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.diagonal_fst, Category.comp_id]
    · rw [Category.assoc, pullback.diagonal_snd, Category.comp_id, hk]
  refine ⟨pointsMap B S hS _ (pullback.fst ρ f ≫ pullback.fst g g) β', ?_⟩
  rw [← pointsMap_comp_apply, ← hdiag, hβ']

/-- The scheme-theoretic image of a closed immersion is its range. -/
theorem schemeTheoreticImageSubfunctor_eq_range_of_isClosedImmersion
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (i : F ⟶ G) (hF : IsAlgebraicSpace B S hS F)
    (hi : IsClosedImmersion B S hS i) :
    schemeTheoreticImageSubfunctor B S hS i = Subfunctor.range i :=
  le_antisymm (schemeTheoreticImageSubfunctor_le B S hS i
      (isClosedSubspace_range_of_isClosedImmersion B S hS i hF hi) le_rfl)
    (range_le_schemeTheoreticImageSubfunctor B S hS i)

end AlgebraicGeometry.Space

end
