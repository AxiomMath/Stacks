module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.AugmentationPushforwardCocycle
public import StacksFrontier.CategoryTheory.Sites.Simplicial.RestrictTransitionCoherence
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationMorphism
public import StacksFrontier.CategoryTheory.Sites.Simplicial.ContinuousAugmentationSiteFunctors

/-!
# Sections of the component direct images of a continuous augmentation

Let `C` be a simplicial site in case (A) of Stacks 09WE and `a` a continuous augmentation of `C`
towards a site `D`. In simplicial degree `n` the direct image along the augmentation of that
degree of the restriction of a sheaf `F` on the total site has, over `W` in `D`, the sections of
`F` over the object `a_n(W)` of degree `n`. The cosimplicial structure of these direct images
(Stacks 0D70, compatibility (3)) acts on sections as restriction along the cartesian arrow from
`a_n(W)` to `a_m(W)` lying over a simplex map `[m] → [n]`.

## Main results

* `componentPushforwardTransition_app_hom_app`, in the namespace
  `CategoryTheory.SimplicialSite.ContinuousAugmentation`: the transitions of the component direct
  images on sections.
* `CategoryTheory.Functor.sheafPushforwardContinuous_eqToHom_app_hom_app`: the transport of a
  direct image along an equality of continuous site functors on sections.

## References

* [Stacks Project, Tag 0D70](https://stacks.math.columbia.edu/tag/0D70)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace CategoryTheory.SimplicialSite.ContinuousAugmentation

open SimplicialSiteSituation SimplicialSiteSituation.Augmentation

/-- The transport of the direct image along an equality of continuous site functors acts on
sections as restriction along the transport of the equality. -/
theorem _root_.CategoryTheory.Functor.sheafPushforwardContinuous_eqToHom_app_hom_app
    {X Y : Type u} [SmallCategory X] [SmallCategory Y] (J : GrothendieckTopology X)
    (M : GrothendieckTopology Y) {F F' : X ⥤ Y} [F.IsContinuous J M] [F'.IsContinuous J M]
    (e : F = F')
    (e' : F.sheafPushforwardContinuous (Type u) J M = F'.sheafPushforwardContinuous (Type u) J M)
    (P : Sheaf M (Type u)) (V : X) :
    ((eqToHom e').app P).hom.app (op V) = P.obj.map (eqToHom (Functor.congr_obj e V).symm).op := by
  cases e
  simp only [eqToHom_refl, NatTrans.id_app, op_id, CategoryTheory.Functor.map_id]
  rfl

variable {C : SimplicialSite.{u}} {D : Cat.{u, u}} {K : GrothendieckTopology D}
  (a : C.ContinuousAugmentation D K)

/-- **Stacks 0D70, compatibility (3), case (A), on sections.** The transition along `φ : [m] → [n]`
of the direct images along the augmentations of the degrees restricts a section over
`a_m(W)` along the cartesian arrow `(φ, 𝟙)` from the degree-`n` object `a_n(W)`. -/
theorem componentPushforwardTransition_app_hom_app {m n : SimplexCategory} (φ : m ⟶ n)
    (F : Sheaf C.totalTopology (Type u)) (W : D) :
    ((componentPushforwardTransition C.situation D K a φ).app F).hom.app (op W) =
      F.obj.map ((Pseudofunctor.CoGrothendieck.ι C.totalPseudofunctor (op n)).map
          (eqToHom (Functor.congr_obj (a.componentSiteFunctor_comp_eq φ) W).symm) ≫
        (continuousInclusionTransition C φ).app ((a.componentSiteFunctor m).obj W)).op := by
  let v₀ : SimplexCategory.mk 0 ⟶ m := SimplexCategory.const (SimplexCategory.mk 0) m 0
  let v₁ : SimplexCategory.mk 0 ⟶ n := SimplexCategory.const (SimplexCategory.mk 0) n 0
  have := (C.isMorphismOfSites (v₀ ≫ φ)).isContinuous
  have := (C.isMorphismOfSites v₁).isContinuous
  have := Functor.isContinuous_comp a.functor (C.underlying.map (v₀ ≫ φ)).toFunctor K
    (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck
  have := Functor.isContinuous_comp a.functor (C.underlying.map v₁).toFunctor K
    (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck
  let ι := Pseudofunctor.CoGrothendieck.ι C.totalPseudofunctor (op n)
  let g₁ := (continuousInclusionTransition C φ).app ((a.componentSiteFunctor m).obj W)
  let g₂ := (eqToIso (congrArg Cat.Hom.toFunctor (C.underlying.map_comp v₀ φ)).symm).inv.app
    (a.functor.obj W)
  let g₃ := eqToHom (Functor.congr_obj (a.compatibility n (v₀ ≫ φ) v₁) W).symm
  have e₁ : ((componentAugmentation C.situation D K a m).pushforward.map
      ((C.situation.restrictTransition φ).app F)).hom.app (op W) = F.obj.map g₁.op :=
    restrictTransition_inl_app C φ F _
  have e₂ : ((Functor.isoWhiskerRight (C.situation.pushforwardCompSymm v₀ φ)
      (morphismOfTopoi C.situation D K a).pushforward).hom.app
        ((C.situation.restrict n).obj F)).hom.app (op W) = F.obj.map (ι.map g₂).op :=
    pushforwardCompSymm_inl_hom_app_hom_app C v₀ φ _ (op (a.functor.obj W))
  have h₃ := Functor.sheafPushforwardContinuousCompIsoOfEq_eqToIso K
    (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck a.functor
    (C.underlying.map (v₀ ≫ φ)).toFunctor (C.underlying.map v₁).toFunctor
    (a.compatibility n (v₀ ≫ φ) v₁)
    (Functor.sheafPushforwardContinuousCompLeft_congr K
      (C.coverage (SimplexCategory.mk 0)).toGrothendieck (C.coverage n).toGrothendieck a.functor
      (C.underlying.map (v₀ ≫ φ)).toFunctor (C.underlying.map v₁).toFunctor
      (a.compatibility n (v₀ ≫ φ) v₁))
  have e₃ : ((vertexPushforwardIso C.situation D K a (v₀ ≫ φ) v₁).hom.app
      ((C.situation.restrict n).obj F)).hom.app (op W) = F.obj.map (ι.map g₃).op :=
    (congrArg (fun e => (e.hom.app ((C.situation.restrict n).obj F)).hom.app (op W)) h₃).trans
      (Functor.sheafPushforwardContinuous_eqToHom_app_hom_app K (C.coverage n).toGrothendieck
        (a.compatibility n (v₀ ≫ φ) v₁)
        (Functor.sheafPushforwardContinuous_congr K (C.coverage n).toGrothendieck
          (a.compatibility n (v₀ ≫ φ) v₁)) _ W)
  have h' : (a.functor ⋙ (C.underlying.map v₁).toFunctor).obj W =
      (C.underlying.map v₀ ≫ C.underlying.map φ).toFunctor.obj (a.functor.obj W) :=
    (Functor.congr_obj (a.compatibility n (v₀ ≫ φ) v₁) W).symm.trans
      (Functor.congr_obj (congrArg Cat.Hom.toFunctor (C.underlying.map_comp v₀ φ)) _)
  have hg : g₃ ≫ g₂ = eqToHom h' := by
    simp only [g₂, g₃, eqToIso.inv, eqToHom_app, eqToHom_trans]
  have hι : ι.map g₃ ≫ ι.map g₂ = ι.map (eqToHom h') :=
    (ι.map_comp g₃ g₂).symm.trans (congrArg ι.map hg)
  refine (congrArg₂ (fun x y => x ≫ y) e₁ (congrArg₂ (fun x y => x ≫ y) e₂ e₃)).trans ?_
  refine ((F.obj.map_comp g₁.op ((ι.map g₂).op ≫ (ι.map g₃).op)).trans
    (congrArg (F.obj.map g₁.op ≫ ·) (F.obj.map_comp _ _))).symm.trans ?_
  exact congrArg (fun k => F.obj.map (Quiver.Hom.op k)) (congrArg (· ≫ g₁) hι)

end CategoryTheory.SimplicialSite.ContinuousAugmentation
