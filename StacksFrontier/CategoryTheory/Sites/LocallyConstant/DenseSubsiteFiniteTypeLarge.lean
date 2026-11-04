module

public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.DenseSubsiteFiniteType

/-!
# Local constancy of finite type along a dense subsite with a larger morphism universe

`Stacks.ConstantSheaf.isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_iff`
transports local constancy of finite type (Tag 093U) along a fully faithful dense subsite
inclusion `G : (C, J) ⥤ (D, K)` between two sites in the *same* pair of universes. The inclusion
`AsSmall.down : AsSmall D ⥤ D` of the small model of a site is such an inclusion, but its source
has its morphisms one universe up: the small étale site `X.Etale` of `X : Scheme.{u}` has
objects in `Type (u + 1)` and morphisms in `Type u`, its small model `AsSmall X.Etale` has both
in `Type (u + 1)`. The sheaves of `Λ`-modules on the two sites still take values in one module
category, `ModuleCat.{max u v w} Λ` for a site `D` with objects in `Type (max u v)` and
morphisms in `Type v`, and this file proves the direction of the transport needed to read a
locally constant sheaf of finite type on `D` on a dense subsite `C` with morphisms in
`Type (max u v)`. The proof is the one of the equal-universe statement.

## Main results

* `isConstantFGOver_sheafPushforwardContinuous_of_large`: a constant trivialization of `F` over
  `G(W)` restricts to one of `F ∘ G` over `W`.
* `isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_of_large`: the restriction
  along `G` of a locally constant sheaf of finite type is locally constant of finite type.

## References

* [Stacks Project, Tag 093U](https://stacks.math.columbia.edu/tag/093U)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v u w r

namespace Stacks.ConstantSheaf

attribute [local instance] ModuleCat.hasLimitsOfSize

variable {C : Type (max u v)} [Category.{max u v} C] {D : Type (max u v)} [Category.{v} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K] [G.Full] [G.Faithful] (Λ : Type w) [Ring Λ]

/-- **A constant trivialization over `G(W)` restricts to one over `W`**, along a fully faithful
dense subsite inclusion whose source has the larger morphism universe. -/
theorem isConstantFGOver_sheafPushforwardContinuous_of_large
    (F : Sheaf K (ModuleCat.{max u v w} Λ)) (W : C) (h : IsConstantFGOver K Λ (G.obj W) F) :
    IsConstantFGOver J Λ W
      ((G.sheafPushforwardContinuous (ModuleCat.{max u v w} Λ) J K).obj F) := by
  have := Functor.isDenseSubsite_overPost_of_fullyFaithful J K G W
  let Φ := (Over.post (X := W) G).sheafPushforwardContinuous (ModuleCat.{max u v w} Λ)
    (J.over W) (K.over (G.obj W))
  have hres : Φ.obj ((K.overPullback (ModuleCat.{max u v w} Λ) (G.obj W)).obj F) ≅
      (J.overPullback (ModuleCat.{max u v w} Λ) W).obj
        ((G.sheafPushforwardContinuous (ModuleCat.{max u v w} Λ) J K).obj F) :=
    Iso.refl _
  have hconst : ∀ E : ModuleCat.{max u v w} Λ,
      Φ.obj ((constantSheaf (K.over (G.obj W)) (ModuleCat.{max u v w} Λ)).obj E) ≅
        (constantSheaf (J.over W) (ModuleCat.{max u v w} Λ)).obj E := fun E ↦
    ((Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility (J.over W) (K.over (G.obj W))
      (Over.post (X := W) G) (ModuleCat.{max u v w} Λ)).app
        ((Functor.const (Over (G.obj W))ᵒᵖ).obj E)).symm
  obtain ⟨E, hE, ⟨ε⟩⟩ := h
  exact ⟨E, hE, ⟨(hconst E).symm ≪≫ Φ.mapIso ε ≪≫ hres⟩⟩

/-- **Local constancy of finite type restricts along a dense subsite** whose source has the
larger morphism universe (Tag 093U): the restriction along a fully faithful dense subsite
inclusion `G` of a locally constant sheaf of `Λ`-modules of finite type is locally constant of
finite type. -/
theorem isFiniteTypeLocallyConstantModuleSheaf_sheafPushforwardContinuous_of_large
    (F : Sheaf K (ModuleCat.{max u v w} Λ)) (h : IsFiniteTypeLocallyConstantModuleSheaf K Λ F) :
    IsFiniteTypeLocallyConstantModuleSheaf J Λ
      ((G.sheafPushforwardContinuous (ModuleCat.{max u v w} Λ) J K).obj F) := by
  have := Functor.IsDenseSubsite.isCoverDense J K G
  have := Functor.IsDenseSubsite.isLocallyFull J K G
  rw [isFiniteTypeLocallyConstantModuleSheaf_iff_trivSieve_mem] at h ⊢
  intro U
  refine J.superset_covering ?_ ((G.functorPushforward_mem_iff J K).1
    (Functor.IsCoverDense.functorPullback_pushforward_covering ⟨_, h (G.obj U)⟩))
  intro V v hv
  exact isConstantFGOver_sheafPushforwardContinuous_of_large J K G Λ F V hv

end Stacks.ConstantSheaf

end
