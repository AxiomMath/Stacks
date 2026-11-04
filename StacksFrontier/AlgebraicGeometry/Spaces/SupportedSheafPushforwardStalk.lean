module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStalkComparison
import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveSmallEtale
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianCounitComp
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The stalk of a direct image of an abelian sheaf supported on a closed subspace

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let `i : Z ⟶ X` and
`i' : W ⟶ Y` be closed immersions and let `f' : W ⟶ Z` be an integral universally injective
morphism making the square commute. For an abelian sheaf `K` on the small étale site of `Y`
whose support is contained in `|W|` and a geometric point `w` of `W`, the canonical comparison
`(f_*K)_{f(i'(w))} ⟶ K_{i'(w)}` is an isomorphism.

This is the degree-zero case of the identification the source of Stacks 0AEQ makes on derived
categories, proved here directly for abelian sheaves.

The route is the source's chain, run on counits rather than on the stalk comparisons: the
comparison is the stalk of the counit `f^{-1}f_* ⟶ 𝟭` of
`AlgebraicGeometry.Space.smallEtaleAbelianInverseImageAdjunction`, by
`AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkMap_app`; the sheaf is the direct
image `i'_*K'` of `K' = (i')^{-1}K` by Étale Cohomology 04CA; and
`AlgebraicGeometry.Space.counit_app_smallEtaleAbelianInverseImageAdjunction_comp`, applied along
the two factorizations `i' ≫ f` and `f' ≫ i` of the diagonal, reduces the invertibility of that
counit to the invertibility of the counits of the two closed immersions, Stacks 04E5 part (2),
and of the integral universally injective `f'`, the trailing clause of Stacks 0AEH.

## Main results

* `AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkMap_app` evaluates the stalk
  comparison at a sheaf: it is the stalk of the counit.
* `isIso_counit_smallEtaleAbelianInverseImageAdjunction_of_isClosedImmersion`, in the namespace
  `AlgebraicGeometry.Space`: the counit of the adjunction of a closed immersion is invertible.
* `AlgebraicGeometry.Space.isIso_app_smallEtaleAbelianPushforwardStalkMap_of_support`: the
  comparison on stalks is an isomorphism at a sheaf supported on `|W|`.

## References

* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 0AEH](https://stacks.math.columbia.edu/tag/0AEH)
* [Stacks Project, Tag 0AEQ](https://stacks.math.columbia.edu/tag/0AEQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-- Invertibility of a natural transformation at an object only depends on the isomorphism class
of that object. -/
private theorem isIso_app_of_isIso_hom {C : Type*} [Category* C] {D : Type*} [Category* D]
    {F G : C ⥤ D} (θ : F ⟶ G) {A A' : C} (η : A ⟶ A') [IsIso η] [IsIso (θ.app A')] :
    IsIso (θ.app A) := by
  have h : θ.app A = F.map η ≫ θ.app A' ≫ inv (G.map η) := by
    rw [← Category.assoc, θ.naturality, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [h]
  infer_instance

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y Z W : AlgebraicSpaces B S hS}

/-- **The stalk comparison at a sheaf is the stalk of the counit.** The canonical map
`(f_*F)_{f(ȳ)} ⟶ F_ȳ` of
`AlgebraicGeometry.Space.smallEtaleAbelianPushforwardStalkMap` is the identification of
Stacks 04K2 part (4) followed by the geometric stalk of the counit `f^{-1}f_*F ⟶ F`. -/
theorem smallEtaleAbelianPushforwardStalkMap_app (f : Y ⟶ X)
    (hf : yoneda.relativelyRepresentable f.hom) (y : GeometricPoint B S hS Y.1)
    (F : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1}) :
    (smallEtaleAbelianPushforwardStalkMap B S hS f hf y).app F =
      (smallEtaleAbelianInverseImageStalkIso B S hS f hf y).inv.app
          ((smallEtaleAbelianPushforward.{u + 1} B S hS f hf).obj F) ≫
        (smallEtaleAbelianStalk B S hS y).map
          ((smallEtaleAbelianInverseImageAdjunction B S hS f hf).counit.app F) := by
  simp [smallEtaleAbelianPushforwardStalkMap]

/-- **The counit of the adjunction of a closed immersion is invertible.** The direct image of
abelian sheaves along a closed immersion is fully faithful, Stacks 04E5 part (2), so the counit
`i^{-1}i_* ⟶ 𝟭` is a natural isomorphism. -/
@[sga "4 VIII 5.7" "partial"]
theorem isIso_counit_smallEtaleAbelianInverseImageAdjunction_of_isClosedImmersion (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) :
    IsIso (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep).counit := by
  have hff := fullyFaithfulSmallEtaleAbelianPushforwardOfIsClosedImmersion.{u + 1} B S hS i hi
  have := hff.full
  have := hff.faithful
  exact Adjunction.counit_isIso_of_R_fully_faithful
    (h := smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep)

/-- **The stalk of a direct image of a sheaf supported on a closed subspace.** For a commutative
square with closed immersions `i : Z ⟶ X` and `i' : W ⟶ Y` and `f' : W ⟶ Z` integral and
universally injective, an abelian sheaf `K` on `Y_étale` supported on `|W|` and a geometric
point `w` of `W`, the canonical comparison `(f_*K)_{f(i'(w))} ⟶ K_{i'(w)}` is an isomorphism.

This is the degree-zero case of Stacks 0AEQ for abelian sheaves. -/
theorem isIso_app_smallEtaleAbelianPushforwardStalkMap_of_support (f : Y ⟶ X)
    (hfr : yoneda.relativelyRepresentable f.hom) (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (i' : W ⟶ Y)
    (hi' : IsClosedImmersion B S hS i'.hom) (f' : W ⟶ Z)
    (hf'int : IsIntegralHom B S hS f'.hom) (hf'inj : UniversallyInjective B S hS f'.hom)
    (hsq : i' ≫ f = f' ≫ i) (w : GeometricPoint B S hS W.1)
    (K : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1})
    (hK : supportOfSheaf B S hS Y.1 K ⊆ Set.range (pointsMap B S hS W.1 i'.hom)) :
    IsIso ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr
      (geometricPointMap i'.hom w)).app K) := by
  have hf'r := relativelyRepresentable_of_isIntegralHom B S hS f' hf'int
  have hc : yoneda.relativelyRepresentable (i' ≫ f).hom :=
    MorphismProperty.comp_mem _ i'.hom f.hom hi'.rep hfr
  have hεi := isIso_counit_smallEtaleAbelianInverseImageAdjunction_of_isClosedImmersion
    B S hS i hi
  have hεi' := isIso_counit_smallEtaleAbelianInverseImageAdjunction_of_isClosedImmersion
    B S hS i' hi'
  have hη : IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS i' hi'.rep).unit.app K) :=
    isIso_unit_app_of_supportOfSheaf_subset B S hS i' hi' K hK
  set K' := (smallEtaleAbelianInverseImage B S hS i' hi'.rep).obj K with hK'def
  have hεc : IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS (i' ≫ f) hc).counit.app
      K') := by
    refine isIso_counit_app_smallEtaleAbelianInverseImageAdjunction_comp B S hS f' i (i' ≫ f)
      hf'r hi.rep hc hsq.symm K' ?_ ?_
    · exact inferInstance
    · exact smallEtaleAdjunctionCounitIsIsoAbelianOfIntegralUniversallyInjective.{u + 1}
        B S hS f' hf'int hf'inj K'
  have h₁ : IsIso ((smallEtaleAbelianInverseImage B S hS i' hi'.rep).map
      ((smallEtaleAbelianInverseImageAdjunction B S hS f hfr).counit.app
        ((smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).obj K'))) :=
    isIso_map_counit_app_smallEtaleAbelianInverseImageAdjunction_comp B S hS i' f (i' ≫ f)
      hi'.rep hfr hc rfl K' hεc inferInstance
  have h₂ : IsIso ((smallEtaleAbelianStalk B S hS (geometricPointMap i'.hom w)).map
      ((smallEtaleAbelianInverseImageAdjunction B S hS f hfr).counit.app
        ((smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).obj K'))) := by
    have h₃ : IsIso ((smallEtaleAbelianInverseImage B S hS i' hi'.rep ⋙
        smallEtaleAbelianStalk B S hS w).map
          ((smallEtaleAbelianInverseImageAdjunction B S hS f hfr).counit.app
            ((smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).obj K'))) := by
      rw [Functor.comp_map]
      have := h₁
      infer_instance
    have := h₃
    exact isIso_map_of_natIso (smallEtaleAbelianInverseImageStalkIso B S hS i' hi'.rep w) _
  have h₄ : IsIso ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr
      (geometricPointMap i'.hom w)).app
        ((smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).obj K')) := by
    rw [smallEtaleAbelianPushforwardStalkMap_app]
    have := h₂
    infer_instance
  have h₅ : IsIso ((smallEtaleAbelianPushforwardStalkMap B S hS f hfr
      (geometricPointMap i'.hom w)).app
        ((smallEtaleAbelianInverseImage B S hS i' hi'.rep ⋙
          smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).obj K)) := h₄
  have := h₅
  exact isIso_app_of_isIso_hom _
    ((smallEtaleAbelianInverseImageAdjunction B S hS i' hi'.rep).unit.app K)

end AlgebraicGeometry.Space

end
