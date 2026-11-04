module

public import StacksFrontier.AlgebraicGeometry.Chow.GysinLocalCompleteIntersection.FactorizationRegularImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# The factorizations of a composite of local complete intersection morphisms

Let `f : X ⟶ Y` and `g : Y ⟶ Z` be morphisms of schemes, let `X ⟶ P ⟶ Z` be a factorization of
`g ∘ f` and `Y ⟶ P' ⟶ Z` a factorization of `g`, each an immersion followed by a smooth morphism.
This file constructs the diagram

  `X ⟶ P ×_Z Y ⟶ P ×_Z P'`,   `P ×_Z Y ⟶ Y`,   `P ×_Z P' ⟶ P'`,   `Y ⟶ P' ⟶ Z`,

in which the horizontal arrows are immersions, the other arrows are smooth and the square
`P ×_Z Y ⟶ P ×_Z P'` over `Y ⟶ P'` is cartesian; the immersion `P ×_Z Y ⟶ P ×_Z P'` is
Koszul-regular when `Y ⟶ P'` is.

## Main definitions

* `Stacks.Chow.SmoothFactorization.ofComp` — a factorization of `g ∘ f` induces the
  factorization `X ⟶ P ×_Z Y ⟶ Y` of `f`.
* `Stacks.Chow.SmoothFactorization.compositeImm` — the immersion `a : P ×_Z Y ⟶ P ×_Z P'`, the
  base change of the immersion `b : Y ⟶ P'` along the projection `q : P ×_Z P' ⟶ P'`.
* `Stacks.Chow.SmoothFactorization.composite` — the factorization `X ⟶ P ×_Z P' ⟶ Z` of `g ∘ f`.

## Main results

* `Stacks.Chow.SmoothFactorization.isPullback_compositeImm` — the square `a` over `b` is
  cartesian.
* `Stacks.Chow.SmoothFactorization.isKoszulRegularImmersion_compositeImm` — `a` is a
  Koszul-regular immersion when `b` is.

## References

* [Stacks Project, Tag 0FF5](https://stacks.math.columbia.edu/tag/0FF5)
* [Stacks Project, Tag 0FF3](https://stacks.math.columbia.edu/tag/0FF3)
* [Stacks Project, Tag 067P](https://stacks.math.columbia.edu/tag/067P)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace Stacks.Chow

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z}

/-- A factorization `X ⟶ P ⟶ Z` of `g ∘ f` induces the factorization `X ⟶ P ×_Z Y ⟶ Y` of `f`,
by the morphism into the fibre product induced by the immersion and by `f`, followed by the
projection to `Y`. -/
def SmoothFactorization.ofComp (F : SmoothFactorization (f ≫ g)) : SmoothFactorization f where
  ambient := pullback F.proj g
  imm := pullback.lift F.imm f F.imm_proj
  proj := pullback.snd F.proj g
  isImmersion := by
    have : IsImmersion (pullback.lift F.imm f F.imm_proj ≫ pullback.fst F.proj g) := by
      rw [pullback.lift_fst]
      infer_instance
    exact IsImmersion.of_comp _ (pullback.fst F.proj g)
  isSmooth := inferInstance
  imm_proj := pullback.lift_snd _ _ _

section Composite

variable (F : SmoothFactorization (f ≫ g)) (G : SmoothFactorization g)

/-- The morphism `a : P ×_Z Y ⟶ P ×_Z P'` induced by the identity of `P` and the immersion
`b : Y ⟶ P'` of the factorization of `g`. -/
def SmoothFactorization.compositeImm : F.ofComp.ambient ⟶ pullback F.proj G.proj :=
  pullback.map F.proj g F.proj G.proj (𝟙 _) G.imm (𝟙 _) (by simp) (by simp [G.imm_proj])

/-- The composite of `a : P ×_Z Y ⟶ P ×_Z P'` with the projection to `P` is the projection
`P ×_Z Y ⟶ P`. -/
@[reassoc (attr := simp)]
theorem SmoothFactorization.compositeImm_fst :
    F.compositeImm G ≫ pullback.fst F.proj G.proj = pullback.fst F.proj g :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/-- The composite of `a : P ×_Z Y ⟶ P ×_Z P'` with the projection to `P'` is the projection
`P ×_Z Y ⟶ Y` followed by the immersion `b : Y ⟶ P'`. -/
@[reassoc (attr := simp)]
theorem SmoothFactorization.compositeImm_snd :
    F.compositeImm G ≫ pullback.snd F.proj G.proj = F.ofComp.proj ≫ G.imm :=
  pullback.lift_snd _ _ _

/-- The morphism `a : P ×_Z Y ⟶ P ×_Z P'` is the base change of the immersion `b : Y ⟶ P'` along
the projection `q : P ×_Z P' ⟶ P'`, and the projection `p : P ×_Z Y ⟶ Y` is the base change of
`q` along `b`. -/
theorem SmoothFactorization.isPullback_compositeImm :
    IsPullback (F.compositeImm G) F.ofComp.proj (pullback.snd F.proj G.proj) G.imm := by
  have hbig : IsPullback (F.compositeImm G ≫ pullback.fst F.proj G.proj) F.ofComp.proj F.proj
      (G.imm ≫ G.proj) := by
    rw [compositeImm_fst, G.imm_proj]
    exact IsPullback.of_hasPullback F.proj g
  exact IsPullback.of_right hbig (F.compositeImm_snd G)
    (IsPullback.of_hasPullback F.proj G.proj)

/-- The morphism `a : P ×_Z Y ⟶ P ×_Z P'` is an immersion. -/
instance SmoothFactorization.isImmersion_compositeImm : IsImmersion (F.compositeImm G) :=
  MorphismProperty.of_isPullback (P := @IsImmersion) (F.isPullback_compositeImm G).flip
    inferInstance

/-- The base change `a : P ×_Z Y ⟶ P ×_Z P'` of the immersion `b : Y ⟶ P'` along the projection
`q : P ×_Z P' ⟶ P'` is a Koszul-regular immersion when `b` is. -/
theorem SmoothFactorization.isKoszulRegularImmersion_compositeImm
    (hb : IsKoszulRegularImmersion G.imm) : IsKoszulRegularImmersion (F.compositeImm G) :=
  Stacks.AlgebraicGeometry.isKoszulRegularImmersion_of_isPullback_of_flat
    (F.isPullback_compositeImm G) hb

/-- The factorization `X ⟶ P ×_Z P' ⟶ Z` of `g ∘ f`: the composite of the immersion
`X ⟶ P ×_Z Y` of `Stacks.Chow.SmoothFactorization.ofComp` with `a`, followed by the smooth
morphism `P ×_Z P' ⟶ P' ⟶ Z`. -/
def SmoothFactorization.composite : SmoothFactorization (f ≫ g) where
  ambient := pullback F.proj G.proj
  imm := F.ofComp.imm ≫ F.compositeImm G
  proj := pullback.snd F.proj G.proj ≫ G.proj
  isImmersion := inferInstance
  isSmooth := inferInstance
  imm_proj := by
    rw [Category.assoc, F.compositeImm_snd_assoc, G.imm_proj, ← Category.assoc,
      F.ofComp.imm_proj]

end Composite

end Stacks.Chow

end
