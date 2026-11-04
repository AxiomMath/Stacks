module

public import StacksFrontier.AlgebraicGeometry.Spaces.PushforwardStalkComparisonGeneral
public import StacksFrontier.AlgebraicGeometry.Spaces.SupportedSheafPushforwardStalk
import all StacksFrontier.AlgebraicGeometry.Spaces.SupportedSheafPushforwardStalk
import StacksFrontier.AlgebraicGeometry.Spaces.IntegralUniversallyInjectiveSmallEtale
import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianCounitComp

/-!
# The stalk of a direct image of a supported sheaf, along an arbitrary morphism

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S`, let `i : Z ⟶ X` be a
closed immersion and let `i' : W ⟶ Y` sit in a commutative square `i' ≫ f = f' ≫ i` with `i'`
a closed immersion and `f' : W ⟶ Z` integral and universally injective.  For an abelian sheaf
`K` on the small étale site of `Y` supported on `|W|` and a geometric point of `Y` coming from
`W`, the canonical comparison `(f_*K)_{f(ȳ)} ⟶ K_ȳ` is an isomorphism.

This is the degree-zero case of Stacks 0AEQ for an arbitrary `f`; for representable `f` it is
`AlgebraicGeometry.Space.isIso_app_smallEtaleAbelianPushforwardStalkMap_of_support`.

## The argument, and why `f` need not be representable

The chain is the source's, run on the adjunction counits rather than on the stalk comparisons,
exactly as in the representable case.  What makes it go through for an arbitrary `f` is that
`CategoryTheory.Adjunction.isIso_counit_app_of_comp` and
`CategoryTheory.Adjunction.isIso_map_counit_app_of_comp` are stated for *arbitrary*
adjunctions: the only thing they need about a factorisation `a ≫ b = c` is an isomorphism
`a_* ⋙ b_* ≅ c_*`.  So the three legs of the square other than `f` — the two closed immersions
`i` and `i'`, and the integral `f'` — may keep the representable direct image, whose counit is
where all the input lies (Stacks 04E5 part (2) for the immersions, Stacks 0AEH for `f'`), while
`f` and the diagonal `i' ≫ f` use the direct image of
`StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleAbelianDirectImageGeneral`.  The two mixed
composition isomorphisms below are what joins the two flavours, and they are the bridge
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImageIso` followed by the unconditional
composition isomorphism of the general direct image.

## Main definitions

* `AlgebraicGeometry.Space.smallEtaleAbelianMixedCompIsoRight` and
  `AlgebraicGeometry.Space.smallEtaleAbelianMixedCompIsoBoth`: the composition isomorphism
  `a_* ⋙ b_* ≅ c_*` with the representable direct image on the representable legs and the
  general one on the composite.

## Main results

* `AlgebraicGeometry.Space.isIso_app_smallEtaleAbelianDirectImageStalkMap_of_support`.

## References

* [Stacks Project, Tag 0AEQ](https://stacks.math.columbia.edu/tag/0AEQ)
* [Stacks Project, Tag 0AEH](https://stacks.math.columbia.edu/tag/0AEH)
* [Stacks Project, Tag 04E5](https://stacks.math.columbia.edu/tag/04E5)
* [Stacks Project, Tag 04CA](https://stacks.math.columbia.edu/tag/04CA)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

variable {X Y Z W : AlgebraicSpaces B S hS}

/-- **The composition isomorphism `a_* ⋙ b_* ≅ c_*` with the representable direct image on `a`
only.**  For `a ≫ b = c` with `a` representable and `b` arbitrary: the bridge
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImageIso` on the `a` factor followed by the
unconditional composition isomorphism of the general direct image. -/
def smallEtaleAbelianMixedCompIsoRight (a : W ⟶ Y) (b : Y ⟶ X) (c : W ⟶ X)
    (ha : yoneda.relativelyRepresentable a.hom) (h : a ≫ b = c) :
    smallEtaleAbelianPushforward.{u + 1} B S hS a ha ⋙
        smallEtaleAbelianDirectImage B S hS b ≅
      smallEtaleAbelianDirectImage B S hS c :=
  Functor.isoWhiskerRight (smallEtaleAbelianDirectImageIso B S hS a ha)
      (smallEtaleAbelianDirectImage B S hS b) ≪≫
    smallEtaleAbelianDirectImageCompIsoOfEq B S hS a b c h

/-- **The composition isomorphism `a_* ⋙ b_* ≅ c_*` with the representable direct image on both
factors.**  For `a ≫ b = c` with `a` and `b` representable and `c` arbitrary: the bridge
`AlgebraicGeometry.Space.smallEtaleAbelianDirectImageIso` on each factor followed by the
unconditional composition isomorphism of the general direct image. -/
def smallEtaleAbelianMixedCompIsoBoth (a : W ⟶ Z) (b : Z ⟶ X) (c : W ⟶ X)
    (ha : yoneda.relativelyRepresentable a.hom) (hb : yoneda.relativelyRepresentable b.hom)
    (h : a ≫ b = c) :
    smallEtaleAbelianPushforward.{u + 1} B S hS a ha ⋙
        smallEtaleAbelianPushforward.{u + 1} B S hS b hb ≅
      smallEtaleAbelianDirectImage B S hS c :=
  Functor.isoWhiskerRight (smallEtaleAbelianDirectImageIso B S hS a ha)
      (smallEtaleAbelianPushforward.{u + 1} B S hS b hb) ≪≫
    Functor.isoWhiskerLeft (smallEtaleAbelianDirectImage B S hS a)
      (smallEtaleAbelianDirectImageIso B S hS b hb) ≪≫
    smallEtaleAbelianDirectImageCompIsoOfEq B S hS a b c h

/-- **The stalk of a direct image of a sheaf supported on a closed subspace, along an arbitrary
morphism.** For a commutative square with closed immersions `i : Z ⟶ X` and `i' : W ⟶ Y` and
`f' : W ⟶ Z` integral and universally injective, an abelian sheaf `K` on `Y_étale` supported on
`|W|` and a geometric point `w` of `W`, the canonical comparison
`(f_*K)_{f(i'(w))} ⟶ K_{i'(w)}` is an isomorphism.

This is the degree-zero case of Stacks 0AEQ for abelian sheaves, with no hypothesis on `f`. -/
theorem isIso_app_smallEtaleAbelianDirectImageStalkMap_of_support (f : Y ⟶ X) (i : Z ⟶ X)
    (hi : IsClosedImmersion B S hS i.hom) (i' : W ⟶ Y)
    (hi' : IsClosedImmersion B S hS i'.hom) (f' : W ⟶ Z)
    (hf'int : IsIntegralHom B S hS f'.hom) (hf'inj : UniversallyInjective B S hS f'.hom)
    (hsq : i' ≫ f = f' ≫ i) (w : GeometricPoint B S hS W.1)
    (K : Sheaf (SmallEtale.topology B S hS Y.1) AddCommGrpCat.{u + 1})
    (hK : supportOfSheaf B S hS Y.1 K ⊆ Set.range (pointsMap B S hS W.1 i'.hom)) :
    IsIso ((smallEtaleAbelianDirectImageStalkMap B S hS f
      (geometricPointMap i'.hom w)).app K) := by
  have hf'r := relativelyRepresentable_of_isIntegralHom B S hS f' hf'int
  -- The counits of the two closed immersions are invertible.
  have hεi := isIso_counit_smallEtaleAbelianInverseImageAdjunction_of_isClosedImmersion
    B S hS i hi
  have hεi' := isIso_counit_smallEtaleAbelianInverseImageAdjunction_of_isClosedImmersion
    B S hS i' hi'
  -- `K` is the direct image of `K' = (i')^{-1}K`, by Étale Cohomology 04CA.
  have hη : IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS i' hi'.rep).unit.app K) :=
    isIso_unit_app_of_supportOfSheaf_subset B S hS i' hi' K hK
  set K' := (smallEtaleAbelianInverseImage B S hS i' hi'.rep).obj K with hK'def
  -- The counit of the diagonal is invertible, read along the factorization `f' ≫ i`.
  have hεc : IsIso ((smallEtaleAbelianGeneralAdjunction B S hS (i' ≫ f)).counit.app K') := by
    have : IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep).counit.app
        ((smallEtaleAbelianPushforward.{u + 1} B S hS f' hf'r).obj K')) := by
      have := hεi
      infer_instance
    have : IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS f' hf'r).counit.app K') :=
      smallEtaleAdjunctionCounitIsIsoAbelianOfIntegralUniversallyInjective.{u + 1}
        B S hS f' hf'int hf'inj K'
    exact Adjunction.isIso_counit_app_of_comp
      (smallEtaleAbelianInverseImageAdjunction B S hS i hi.rep)
      (smallEtaleAbelianInverseImageAdjunction B S hS f' hf'r)
      (smallEtaleAbelianGeneralAdjunction B S hS (i' ≫ f))
      (smallEtaleAbelianMixedCompIsoBoth B S hS f' i (i' ≫ f) hf'r hi.rep hsq.symm) K'
  -- Hence the counit of `f` at `i'_*K'` is invertible after applying `(i')^{-1}`.
  have h₁ : IsIso ((smallEtaleAbelianInverseImage B S hS i' hi'.rep).map
      ((smallEtaleAbelianGeneralAdjunction B S hS f).counit.app
        ((smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).obj K'))) := by
    have := hεc
    have : IsIso ((smallEtaleAbelianInverseImageAdjunction B S hS i' hi'.rep).counit.app K') := by
      have := hεi'
      infer_instance
    exact Adjunction.isIso_map_counit_app_of_comp
      (smallEtaleAbelianGeneralAdjunction B S hS f)
      (smallEtaleAbelianInverseImageAdjunction B S hS i' hi'.rep)
      (smallEtaleAbelianGeneralAdjunction B S hS (i' ≫ f))
      (smallEtaleAbelianMixedCompIsoRight B S hS i' f (i' ≫ f) hi'.rep rfl) K'
  -- The geometric stalk at `i'(w)` of that counit is therefore invertible.
  have h₂ : IsIso ((smallEtaleAbelianStalk B S hS (geometricPointMap i'.hom w)).map
      ((smallEtaleAbelianGeneralAdjunction B S hS f).counit.app
        ((smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).obj K'))) := by
    have h₃ : IsIso ((smallEtaleAbelianInverseImage B S hS i' hi'.rep ⋙
        smallEtaleAbelianStalk B S hS w).map
          ((smallEtaleAbelianGeneralAdjunction B S hS f).counit.app
            ((smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).obj K'))) := by
      rw [Functor.comp_map]
      have := h₁
      infer_instance
    have := h₃
    exact isIso_map_of_natIso (smallEtaleAbelianInverseImageStalkIso B S hS i' hi'.rep w) _
  -- Read back through Stacks 04K2 part (4) and transport along the unit.
  have h₄ : IsIso ((smallEtaleAbelianDirectImageStalkMap B S hS f
      (geometricPointMap i'.hom w)).app
        ((smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).obj K')) := by
    rw [smallEtaleAbelianDirectImageStalkMap_app]
    have := h₂
    infer_instance
  have h₅ : IsIso ((smallEtaleAbelianDirectImageStalkMap B S hS f
      (geometricPointMap i'.hom w)).app
        ((smallEtaleAbelianInverseImage B S hS i' hi'.rep ⋙
          smallEtaleAbelianPushforward.{u + 1} B S hS i' hi'.rep).obj K)) := h₄
  have := h₅
  exact isIso_app_of_isIso_hom _
    ((smallEtaleAbelianInverseImageAdjunction B S hS i' hi'.rep).unit.app K)

end AlgebraicGeometry.Space

end
