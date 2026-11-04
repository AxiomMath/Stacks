module

public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.EssentiallySmallTensorHomAdjunction

/-!
# The pullback map of small internal Homs along a pushforward of modules

Let `u : X.C ⥤ Y.C` be a continuous functor of essentially small ringed sites and `F = u_*` the
pushforward of modules along a map of structure sheaves, with a comparison
`μ : F(A ⊗ B) ≅ F A ⊗ F B`. This file computes the map `F H(M, K) ⟶ H(F M, F K)` of Stacks 08JF
for the small internal Hom `AlgebraicGeometry.RingedSite.internalHomSheafSmall` on sections, and
shows that it is invertible when morphisms of restricted modules over each slice `X/U` come from
unique morphisms over the slice `Y/uU`.

## Main results

* `AlgebraicGeometry.RingedSite.pullbackHomMap_internalHomSheafSmall_section`.
* `AlgebraicGeometry.RingedSite.isIso_pullbackHomMap_internalHomSheafSmall`.

## References

* [Stacks Project, Tag 08JF](https://stacks.math.columbia.edu/tag/08JF)
* [Stacks Project, Tag 03EO](https://stacks.math.columbia.edu/tag/03EO)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite MonoidalCategory
open Stacks.PresheafOfModules.InternalHom

universe u v w

namespace AlgebraicGeometry.RingedSite

attribute [local instance 5000] SheafOfModules.instAbelian


variable {X Y : RingedSite.{u, v, w}} [EssentiallySmall.{w} X.C] [EssentiallySmall.{w} Y.C]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  [HasWeakSheafify Y.J AddCommGrpCat.{w}] [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {u : X.C ⥤ Y.C} [u.IsContinuous X.J Y.J]
  (φ : (Stacks.SheafOfModules.Tensor.ringSheaf X.O) ⟶
    (u.sheafPushforwardContinuous RingCat.{w} X.J Y.J).obj
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
  (μ : Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor Y.O) ⋙
      SheafOfModules.pushforward.{w} φ ≅
    (SheafOfModules.pushforward.{w} φ).prod (SheafOfModules.pushforward.{w} φ) ⋙
      Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor X.O))

/-- The comparison `μ` of Stacks 03EL for the pushforward along `u` is the identity on sheafified
local pure tensors. -/
structure PushforwardTensorCompat : Prop where
  tmul : ∀ (A M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (U : X.C)
      (s : (valOf X ((SheafOfModules.pushforward.{w} φ).obj A)).obj (op U))
      (t : (valOf X ((SheafOfModules.pushforward.{w} φ).obj M)).obj (op U)),
      ((μ.inv.app (A, M)).val.app (op U)).hom
          ((((PresheafOfModules.sheafificationAdjunction
              (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj)).unit.app
            ((valOf X ((SheafOfModules.pushforward.{w} φ).obj A) ⊗
              valOf X ((SheafOfModules.pushforward.{w} φ).obj M) :
                PresheafOfModules (Oforget X.O.obj)))).app (op U)).hom (s ⊗ₜ t)) =
        (((PresheafOfModules.sheafificationAdjunction
            (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)).unit.app
            ((valOf Y A ⊗ valOf Y M : PresheafOfModules (Oforget Y.O.obj)))).app
              (op (u.obj U))).hom (s ⊗ₜ t)

/-- Morphisms of restricted modules over a slice of `X` come from unique morphisms over the
corresponding slice of `Y`, compatibly with sections. -/
structure PushforwardSliceUnique : Prop where
  existsUnique : ∀ (U : X.C) (M K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (ψ : (restrFun X.O.obj U).obj (valOf X ((SheafOfModules.pushforward.{w} φ).obj M)) ⟶
        (restrFun X.O.obj U).obj (valOf X ((SheafOfModules.pushforward.{w} φ).obj K))),
      ∃! α : (restrFun Y.O.obj (u.obj U)).obj (valOf Y M) ⟶
          (restrFun Y.O.obj (u.obj U)).obj (valOf Y K),
        ∀ {T : X.C} (q : T ⟶ U)
          (y : (valOf X ((SheafOfModules.pushforward.{w} φ).obj M)).obj (op T)),
          AnyUniverse.sectionOfRestr X.O.obj (valOf X ((SheafOfModules.pushforward.{w} φ).obj K))
              U q
              ((ψ.app (op (Over.mk q))).hom
                (AnyUniverse.restrSection X.O.obj
                  (valOf X ((SheafOfModules.pushforward.{w} φ).obj M)) U q y)) =
            AnyUniverse.sectionOfRestr Y.O.obj (valOf Y K) (u.obj U) (u.map q)
              ((α.app (op (Over.mk (u.map q)))).hom
                (AnyUniverse.restrSection Y.O.obj (valOf Y M) (u.obj U) (u.map q) y))

/-- **The pullback map of small internal Homs along a pushforward, on sections.** If the
comparison `μ` of Stacks 03EL for `F = u_*` is the identity on sheafified local pure tensors, then
the map `F H(M, K) ⟶ H(F M, F K)` of Stacks 08JF sends a section `z` over `U`, a morphism
`M|_{uU} ⟶ K|_{uU}`, to the morphism whose component at `q : T ⟶ U` is the component of `z` at
`u q`. -/
theorem pullbackHomMap_internalHomSheafSmall_section
    (hμ : PushforwardTensorCompat φ μ)
    (M K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) (U : X.C)
    (z : (valOf X ((SheafOfModules.pushforward.{w} φ).obj
      (internalHomSheafSmall Y M K))).obj (op U))
    {T : X.C} (q : T ⟶ U) (y : (valOf X ((SheafOfModules.pushforward.{w} φ).obj M)).obj (op T)) :
    AnyUniverse.sectionOfRestr X.O.obj (valOf X ((SheafOfModules.pushforward.{w} φ).obj K)) U q
        (((internalHomSheafSmallSectionEquiv X ((SheafOfModules.pushforward.{w} φ).obj M)
          ((SheafOfModules.pushforward.{w} φ).obj K) U
          (internalHomSheafSmallApplyLinear X
            ((SheafOfModules.pushforward.{w} φ).obj (internalHomSheafSmall Y M K))
            ((SheafOfModules.pushforward.{w} φ).obj M) ((SheafOfModules.pushforward.{w} φ).obj K)
            (PullbackInternalHom.pullbackHomMap
              (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} Y.O)
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O) μ
              (internalHomSheafSmallBifunctor Y) (internalHomSheafSmallBifunctor X)
              (fun P ↦ internalHomSheafSmallAdjunction Y P)
              (fun P ↦ internalHomSheafSmallAdjunction X P) M K) U z)).app
            (op (Over.mk q))).hom
          (AnyUniverse.restrSection X.O.obj (valOf X ((SheafOfModules.pushforward.{w} φ).obj M))
            U q y)) =
      AnyUniverse.sectionOfRestr Y.O.obj (valOf Y K) (u.obj U) (u.map q)
        (((internalHomSheafSmallSectionEquiv Y M K (u.obj U) z).app
            (op (Over.mk (u.map q)))).hom
          (AnyUniverse.restrSection Y.O.obj (valOf Y M) (u.obj U) (u.map q) y)) := by
  refine (internalHomSheafSmallAdjunction_homEquiv_app X
    ((SheafOfModules.pushforward.{w} φ).obj (internalHomSheafSmall Y M K))
    ((SheafOfModules.pushforward.{w} φ).obj M) ((SheafOfModules.pushforward.{w} φ).obj K)
    (μ.inv.app (internalHomSheafSmall Y M K, M) ≫
      (SheafOfModules.pushforward.{w} φ).map ((internalHomSheafSmallAdjunction Y M).counit.app K))
    U z q y).trans ?_
  refine (congrArg (fun x ↦ ((((internalHomSheafSmallAdjunction Y M).counit.app K).val.app
      (op (u.obj T))).hom x)) (hμ.tmul (internalHomSheafSmall Y M K) M T _ y)).trans ?_
  refine (internalHomSheafSmallAdjunction_counit_app_val_app Y M K (u.obj T) _ y).trans ?_
  refine (congrArg (fun α ↦ AnyUniverse.sectionOfRestr Y.O.obj (valOf Y K) (u.obj T) (𝟙 (u.obj T))
      ((α.app (op (Over.mk (𝟙 (u.obj T))))).hom
        (AnyUniverse.restrSection Y.O.obj (valOf Y M) (u.obj T) (𝟙 (u.obj T)) y)))
    (internalHomSheafSmallSectionEquiv_restrict Y M K (u.map q) z)).trans ?_
  refine (AnyUniverse.homRestr_section Y.O.obj (valOf Y M) (valOf Y K) (u.map q) _ (𝟙 _) y).trans ?_
  have key : ∀ (h : u.obj T ⟶ u.obj U) (_ : 𝟙 (u.obj T) ≫ u.map q = h),
      AnyUniverse.sectionOfRestr Y.O.obj (valOf Y K) (u.obj U) (𝟙 (u.obj T) ≫ u.map q)
        (((internalHomSheafSmallSectionEquiv Y M K (u.obj U) z).app
            (op (Over.mk (𝟙 (u.obj T) ≫ u.map q)))).hom
          (AnyUniverse.restrSection Y.O.obj (valOf Y M) (u.obj U) (𝟙 (u.obj T) ≫ u.map q) y)) =
      AnyUniverse.sectionOfRestr Y.O.obj (valOf Y K) (u.obj U) h
        (((internalHomSheafSmallSectionEquiv Y M K (u.obj U) z).app
            (op (Over.mk h))).hom
          (AnyUniverse.restrSection Y.O.obj (valOf Y M) (u.obj U) h y)) := by
    intro h e
    subst e
    rfl
  exact key _ (Category.id_comp _)

/-- **The pullback map of small internal Homs along a pushforward is invertible** when, slice by
slice, morphisms of restricted modules over `X/U` come from unique morphisms over `Y/uU` (as for an
étale morphism, Stacks 04M0) and `μ` is the identity on sheafified local pure tensors. -/
theorem isIso_pullbackHomMap_internalHomSheafSmall
    (hμ : PushforwardTensorCompat φ μ)
    (hslice : PushforwardSliceUnique φ)
    (M K : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :
    IsIso (PullbackInternalHom.pullbackHomMap (Stacks.SheafOfModules.Tensor.sheafTensor Y.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) μ
      (internalHomSheafSmallBifunctor Y) (internalHomSheafSmallBifunctor X)
      (fun P ↦ internalHomSheafSmallAdjunction Y P)
      (fun P ↦ internalHomSheafSmallAdjunction X P) M K) := by
  set g := PullbackInternalHom.pullbackHomMap
      (Stacks.SheafOfModules.Tensor.sheafTensor.{_, _, _, w, w} Y.O)
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O) μ
      (internalHomSheafSmallBifunctor Y) (internalHomSheafSmallBifunctor X)
      (fun P ↦ internalHomSheafSmallAdjunction Y P)
      (fun P ↦ internalHomSheafSmallAdjunction X P) M K with hg
  have hGH := pullbackHomMap_internalHomSheafSmall_section φ μ hμ M K
  have hbij : ∀ V : X.Cᵒᵖ, Function.Bijective (g.val.app V) := by
    intro V
    obtain ⟨U⟩ := V
    let ε' := internalHomSheafSmallSectionEquiv X ((SheafOfModules.pushforward.{w} φ).obj M)
      ((SheafOfModules.pushforward.{w} φ).obj K) U
    let ε := internalHomSheafSmallSectionEquiv Y M K (u.obj U)
    have hext : ∀ (ψ₁ ψ₂ : (restrFun X.O.obj U).obj
          (valOf X ((SheafOfModules.pushforward.{w} φ).obj M)) ⟶
        (restrFun X.O.obj U).obj (valOf X ((SheafOfModules.pushforward.{w} φ).obj K))),
        (∀ {T : X.C} (q : T ⟶ U)
          (y : (valOf X ((SheafOfModules.pushforward.{w} φ).obj M)).obj (op T)),
          AnyUniverse.sectionOfRestr X.O.obj (valOf X ((SheafOfModules.pushforward.{w} φ).obj K))
              U q
              ((ψ₁.app (op (Over.mk q))).hom
                (AnyUniverse.restrSection X.O.obj
                  (valOf X ((SheafOfModules.pushforward.{w} φ).obj M)) U q y)) =
            AnyUniverse.sectionOfRestr X.O.obj
              (valOf X ((SheafOfModules.pushforward.{w} φ).obj K)) U q
              ((ψ₂.app (op (Over.mk q))).hom
                (AnyUniverse.restrSection X.O.obj
                  (valOf X ((SheafOfModules.pushforward.{w} φ).obj M)) U q y)))
          → ψ₁ = ψ₂ := fun _ _ h ↦
      _root_.PresheafOfModules.hom_ext fun ⟨W⟩ ↦ ModuleCat.hom_ext (LinearMap.ext (h W.hom))
    refine ⟨fun z z' hzz ↦ ?_, fun w' ↦ ?_⟩
    · have h1 : ε' ((g.val.app (op U)).hom z) = ε' ((g.val.app (op U)).hom z') :=
        congrArg ε' hzz
      obtain ⟨α, -, huniq⟩ := hslice.existsUnique U M K (ε' ((g.val.app (op U)).hom z))
      have ha : ε z = α := huniq _ (fun q y ↦ hGH U z q y)
      have ha' : ε z' = α := huniq _ (fun q y ↦ by rw [h1]; exact hGH U z' q y)
      exact ε.injective (ha.trans ha'.symm)
    · obtain ⟨α, hα, -⟩ := hslice.existsUnique U M K (ε' w')
      refine ⟨ε.symm α, ε'.injective (hext _ _ (fun q y ↦ ?_))⟩
      refine (hGH U (ε.symm α) q y).trans ?_
      erw [ε.apply_symm_apply]
      exact (hα q y).symm
  have happ : ∀ V : X.Cᵒᵖ, IsIso (g.val.app V) := fun V ↦
    (ConcreteCategory.isIso_iff_bijective _).mpr (hbij V)
  have hval : IsIso g.val :=
    (PresheafOfModules.isoMk (fun V ↦ asIso (g.val.app V))
      (fun _ _ f ↦ g.val.naturality f)).isIso_hom
  have : IsIso ((SheafOfModules.forget _).map g) := hval
  exact isIso_of_reflects_iso g (SheafOfModules.forget _)

end AlgebraicGeometry.RingedSite

end
