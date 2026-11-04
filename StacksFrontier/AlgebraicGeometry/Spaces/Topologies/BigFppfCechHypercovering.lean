module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigFppfPretopology
public import StacksFrontier.CategoryTheory.Sites.Simplicial.CechAugmentationHypercovering

/-!
# Čech hypercoverings in the big fppf site of algebraic spaces

A flat, locally finitely presented morphism `g : Z ⟶ X` of algebraic spaces which is surjective
on points is by itself a covering of the big fppf site of algebraic spaces. For such a morphism
`b₀ : V₀ ⟶ Y` the Čech nerve `V_n = V₀ ×_Y ⋯ ×_Y V₀` of `b₀` is a hypercovering of `Y`, and for
any `f : X ⟶ Y` its base change `U_n = V_n ×_Y X` is a hypercovering of `X` (Stacks 09X8); the
squares formed by `U_n ⟶ V_n` and the simplicial structure maps are cartesian.

## Main definitions

* `AlgebraicGeometry.BigFppfSpaceSite.cechOver`: the Čech nerve of `b₀`, over `Y`.
* `AlgebraicGeometry.BigFppfSpaceSite.cechOverPullback`: its base change along `f`, over `X`.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.isHypercoveringAugmentation_cechOver`,
  `AlgebraicGeometry.BigFppfSpaceSite.isHypercoveringAugmentation_cechOverPullback`.
* `AlgebraicGeometry.BigFppfSpaceSite.isPullback_cechOverPullback_map`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial Stacks.CategoryTheory.Hypercovering
open AlgebraicGeometry.Space

universe u

/-- A one-member covering family stays covering after precomposing with an isomorphism. -/
theorem CategoryTheory.Pretopology.singleton_comp_mem_of_isIso {C : Type*} [Category C]
    [HasPullbacks C]
    (J : Pretopology C) {Z' Z X : C} (e : Z' ⟶ Z) [IsIso e] (g : Z ⟶ X)
    (hg : Presieve.singleton g ∈ J X) : Presieve.singleton (e ≫ g) ∈ J X := by
  let Ti : ∀ ⦃W : C⦄ (q : W ⟶ X), Presieve.singleton g q → Presieve W := fun _ _ ⟨⟩ =>
    Presieve.singleton e
  have hbind : (Presieve.singleton g).bind Ti = Presieve.singleton (e ≫ g) := by
    funext W q
    refine propext ⟨?_, ?_⟩
    · rintro ⟨V, a, b, ⟨⟩, ⟨⟩, rfl⟩
      exact Presieve.singleton.mk
    · rintro ⟨⟩
      exact ⟨Z, e, g, ⟨⟩, ⟨⟩, rfl⟩
  rw [← hbind]
  exact J.transitive _ Ti hg fun _ _ ⟨⟩ => J.has_isos e

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} {T : BigFppfSpaceSite S}

/-- Finite products in the slices of the algebraic spaces over `S`: fibre products. -/
local instance (Y : T.Spaces) : HasFiniteProducts (Over Y) :=
  haveI := Over.ConstructProducts.over_binaryProduct_of_pullback (B := Y)
  haveI := Over.over_hasTerminal Y
  hasFiniteProducts_of_has_binary_and_terminal

/-- The Čech nerve `n ↦ V₀ ×_Y ⋯ ×_Y V₀` of a morphism `b₀ : V₀ ⟶ Y`, as a simplicial object
of the slice over `Y`. -/
def cechOver {V₀ Y : T.Spaces} (b₀ : V₀ ⟶ Y) : SimplicialObject (Over Y) :=
  cechNerveTerminalFrom (Over.mk b₀)

/-- The base change `n ↦ V_n ×_Y X` along `f : X ⟶ Y` of the Čech nerve of `b₀`, as a
simplicial object of the slice over `X`. -/
def cechOverPullback {V₀ Y X : T.Spaces} (b₀ : V₀ ⟶ Y) (f : X ⟶ Y) :
    SimplicialObject (Over X) :=
  cechOver b₀ ⋙ Over.pullback f

/-- The degree-zero term of the Čech nerve of `b₀ : V₀ ⟶ Y` is `V₀`. -/
def cechOverObjZeroIso {V₀ Y : T.Spaces} (b₀ : V₀ ⟶ Y) :
    ((cechOver b₀).obj (op ⦋0⦌)).left ≅ V₀ :=
  (Over.forget Y).mapIso (Limits.productUniqueIso (fun _ : Fin 1 => Over.mk b₀))

/-- The structure morphism `V₀ ×_Y ⋯ ×_Y V₀ ⟶ Y` in degree zero is a covering, for any
pretopology `J` on the algebraic spaces, as soon as `b₀` is one. -/
theorem singleton_cechOver_obj_zero_mem (J : Pretopology T.Spaces) {V₀ Y : T.Spaces}
    (b₀ : V₀ ⟶ Y) (hb₀ : Presieve.singleton b₀ ∈ J Y) :
    Presieve.singleton ((cechOver b₀).obj (op ⦋0⦌)).hom ∈ J Y := by
  let e : (cechOver b₀).obj (op ⦋0⦌) ≅ Over.mk b₀ :=
    Limits.productUniqueIso (fun _ : Fin 1 => Over.mk b₀)
  rw [← Over.w e.hom]
  have : IsIso e.hom.left := inferInstanceAs (IsIso ((Over.forget Y).map e.hom))
  exact J.singleton_comp_mem_of_isIso e.hom.left b₀ hb₀

/-- **The Čech nerve of a covering morphism is a hypercovering** (Stacks 09X8): for a
pretopology `J` on the algebraic spaces (e.g. that of the big fppf site) and `b₀ : V₀ ⟶ Y`
forming a `J`-covering by itself, the augmentation of its Čech nerve to `Y` is a
`J`-hypercovering of `Y`. -/
theorem isHypercoveringAugmentation_cechOver (J : Pretopology T.Spaces) {V₀ Y : T.Spaces}
    (b₀ : V₀ ⟶ Y) (hb₀ : Presieve.singleton b₀ ∈ J Y) :
    IsHypercoveringAugmentation J (cechOver b₀ ⋙ Over.forget Y)
      (overAugmentation (cechOver b₀)) :=
  isHypercoveringAugmentation_of_iso_cechNerveTerminalFrom J (cechOver b₀)
    (Over.mk b₀) (Iso.refl _) (singleton_cechOver_obj_zero_mem J b₀ hb₀)

/-- **The base change of a Čech hypercovering is a hypercovering** (Stacks 09X8): for a
pretopology `J` on the algebraic spaces, `b₀ : V₀ ⟶ Y` forming a `J`-covering by itself and any
`f : X ⟶ Y`, the augmentation of `n ↦ V_n ×_Y X` to `X` is a `J`-hypercovering of `X`; it is the
Čech nerve of `V₀ ×_Y X ⟶ X`. -/
theorem isHypercoveringAugmentation_cechOverPullback (J : Pretopology T.Spaces)
    {V₀ Y X : T.Spaces} (b₀ : V₀ ⟶ Y) (f : X ⟶ Y) (hb₀ : Presieve.singleton b₀ ∈ J Y) :
    IsHypercoveringAugmentation J (cechOverPullback b₀ f ⋙ Over.forget X)
      (overAugmentation (cechOverPullback b₀ f)) := by
  refine isHypercoveringAugmentation_of_iso_cechNerveTerminalFrom J
    (cechOverPullback b₀ f) ((Over.pullback f).obj (Over.mk b₀))
    (cechNerveTerminalFromCompIso (Over.pullback f) (Over.mk b₀)) ?_
  change Presieve.singleton (pullback.snd ((cechOver b₀).obj (op ⦋0⦌)).hom f) ∈ _
  rw [← Presieve.pullback_singleton]
  exact J.pullbacks f _ (singleton_cechOver_obj_zero_mem J b₀ hb₀)

/-- The projection `U_n = V_n ×_Y X ⟶ V_n` in each degree. -/
abbrev cechOverPullbackFst {V₀ Y X : T.Spaces} (b₀ : V₀ ⟶ Y) (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) :
    ((cechOverPullback b₀ f).obj n).left ⟶ ((cechOver b₀).obj n).left :=
  pullback.fst ((cechOver b₀).obj n).hom f

/-- The simplicial structure maps of `n ↦ V_n ×_Y X` are the base changes of those of the Čech
nerve `V`: the square formed with the projections `U_n ⟶ V_n` is cartesian. -/
theorem isPullback_cechOverPullback_map {V₀ Y X : T.Spaces} (b₀ : V₀ ⟶ Y) (f : X ⟶ Y)
    {n m : SimplexCategoryᵒᵖ} (φ : n ⟶ m) :
    IsPullback ((cechOverPullback b₀ f).map φ).left (cechOverPullbackFst b₀ f n)
      (cechOverPullbackFst b₀ f m) ((cechOver b₀).map φ).left :=
  isPullback_overPullback_map_left f ((cechOver b₀).map φ)

/-- The square formed by the projection `U_n = V_n ×_Y X ⟶ V_n` and `f` is cartesian. -/
theorem isPullback_cechOverPullbackFst {V₀ Y X : T.Spaces} (b₀ : V₀ ⟶ Y) (f : X ⟶ Y)
    (n : SimplexCategoryᵒᵖ) :
    IsPullback ((cechOverPullback b₀ f).obj n).hom (cechOverPullbackFst b₀ f n) f
      ((cechOver b₀).obj n).hom :=
  (IsPullback.of_hasPullback ((cechOver b₀).obj n).hom f).flip

end AlgebraicGeometry.BigFppfSpaceSite

end
