module

public import StacksFrontier.AlgebraicGeometry.Spaces.StructureSheafPullbackUnitSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsAndPushforward

/-!
# The ring map on global sections of a morphism of ringed topoi, on sections

Let `f : (Sh(C), 𝒪_C) ⟶ (Sh(D), 𝒪_D)` be a morphism of ringed topoi. The ring map
`Stacks.Cohomology.SiteModules.globalSectionsRingHom f : Γ(𝒪_D) ⟶ Γ(𝒪_C)` is built abstractly,
by transporting the multiplication by a global section of `𝒪_D` across the adjunction of
Stacks 03D7 and the identification `f^*𝒪_D ≅ 𝒪_C` of Stacks 03LU, so it comes with no formula.
This file supplies one. Whenever the sections of the direct image `f_*` over an object `W` of `D`
map, naturally in the sheaf, to the sections over an object `Z` of `C` — for the structure
morphism of a crystalline topos these are the projections of the limit computing the direct
image — the value of `globalSectionsRingHom f b` at `Z` is the image of `f♯(b)` over `W`.

## Main results

* `pushforwardUnitHomEquiv_eq`: the bijection `pushforwardUnitHomEquiv` is the preservation of
  global sections by the direct image of the underlying topoi.
* `globalSectionsRingHom_val_eq`: **the formula** for `globalSectionsRingHom`.

## References

* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf Opposite
open AlgebraicGeometry
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules

noncomputable section

namespace Stacks.Cohomology.SiteModules

universe w v u v' u'

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : Stacks.Sheaves.RingedToposModules.RingedToposHom X Y)

/-- **`pushforwardUnitHomEquiv` is the preservation of global sections by a direct image**: a
morphism `1_{𝒪_D} ⟶ f_*N` is read as a global section of `f_*N`, carried to a global section of
`N` by `Stacks.Sheaves.RingedToposModules.pushforwardModulesUnitHomEquiv`, and read back as a
morphism `1_{𝒪_C} ⟶ N`. -/
theorem pushforwardUnitHomEquiv_eq (N : SheafOfModules.{w}
    (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (b : SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) ⟶
        (pushforwardModules f).obj N) :
    pushforwardUnitHomEquiv f N b =
      (unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N).symm
        (pushforwardModulesUnitHomEquiv f N b) :=
  (pullbackModulesObjUnitIso_hom_comp f N _).trans
    (congrArg (fun q ↦ (unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O) N).symm
      (pushforwardModulesUnitHomEquiv f N q))
      (((pullbackAdjPushforwardModules f).homEquiv _ N).apply_symm_apply b))

/-- **The ring map on global sections of a morphism of ringed topoi, on sections.** Let `W` be
an object of `D` and `Z` an object of `C`, and let `θ` carry the sections of a direct image over
`W` to sections over `Z`, naturally in the sheaf of sets on `C`. Then for a global section `b`
of `𝒪_D`, the section over `Z` of `globalSectionsRingHom f b` is `θ` of `f♯(b)` over `W`.

The ring map is built by transporting the multiplication by `b` across the adjunction of
Stacks 03D7; reading it through the preservation of global sections by a direct image
(`pushforwardUnitHomEquiv_eq`), the transported multiplication is the action of `f♯(b)` on the
direct image of `𝒪_C`, and `θ`, being natural, is compatible with that action and carries the
image of the unit section to the unit section. -/
theorem globalSectionsRingHom_val_eq {W : Y.Cᵒᵖ} {Z : X.Cᵒᵖ}
    (θ : f.toToposHom.pushforward ⋙ sectionsFunctor Y.J W ⟶ sectionsFunctor X.J Z)
    (b : RingCat.sectionsSubring (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj) :
    (globalSectionsRingHom f b).1 Z =
      θ.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        ((sectionsFunctor Y.J W).map ((sheafCompose Y.J (forget RingCat.{w})).map f.fSharp)
          (b.1 W)) := by
  set U := SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)
  set e := unitTerminalHomEquiv (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
  set x := (MorphismOfTopoi.pushforwardTerminalSection f.toToposHom).hom.app W
    (terminalSheafSection Y.J W)
  set one : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj W := 1
  have hθ : ∀ (E : Sheaf X.J (Type w)) (c : ⊤_ (Sheaf X.J (Type w)) ⟶ E),
      θ.app E ((f.toToposHom.pushforward.map c).hom.app W x) =
        c.hom.app Z (terminalSheafSection X.J Z) := fun E c ↦
    (Functor.natTrans_app_map_apply θ c x).trans
      (congrArg (c.hom.app Z) (eq_terminalSheafSection _))
  -- the canonical morphism `1_{𝒪_D} ⟶ f_*𝒪_C` and its value at the unit section
  have h₀ : pushforwardModulesUnitHomEquiv f U (pushforwardUnitSection f) = e (𝟙 U) := by
    exact (Equiv.symm_apply_eq e).mp
      ((pushforwardUnitHomEquiv_eq f U _).symm.trans (Equiv.apply_symm_apply _ _))
  have key : ∀ g, (f.toToposHom.pushforward.map (pushforwardModulesUnitHomEquiv f U g)).hom.app W
      x = g.val.app W one := fun g ↦ by
    rw [← pushforwardModulesUnitHomEquiv_symm_val_app_one, Equiv.symm_apply_apply]
  have hs₀ : (pushforwardUnitSection f).val.app W one =
      (f.toToposHom.pushforward.map (e (𝟙 U))).hom.app W x := by
    rw [← h₀, key]
  -- the transported multiplication by `b`
  set c := pushforwardModulesUnitHomEquiv f U
    (unitEnd (Stacks.SheafOfModules.Tensor.ringSheaf Y.O) b ≫ pushforwardUnitSection f)
  have h₁ : (globalSectionsRingHom f b).1 Z = c.hom.app Z (terminalSheafSection X.J Z) := by
    change (pushforwardUnitEndMap f b).val.app Z (1 :
        (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj Z) = _
    rw [pushforwardUnitEndMap_eq, pushforwardUnitHomEquiv_eq]
    exact unitTerminalHomEquiv_symm_val_app_one _ _ c Z
  have h₂ : (f.toToposHom.pushforward.map c).hom.app W x =
      (pushforwardUnitSection f).val.app W (b.1 W) :=
    (key _).trans (congrArg ((pushforwardUnitSection f).val.app W) (one_mul (b.1 W)))
  have h₃ : (pushforwardUnitSection f).val.app W (b.1 W) =
      moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
        (f.toToposHom.pushforward ⋙ sectionsFunctor Y.J W)
        ((sectionsFunctor Y.J W).map ((sheafCompose Y.J (forget RingCat.{w})).map f.fSharp)
          (b.1 W))
        ((pushforwardUnitSection f).val.app W one) := by
    refine Eq.trans ?_ (pushforwardModules_smul f U W (b.1 W) _)
    refine Eq.trans (congrArg ((pushforwardUnitSection f).val.app W) (mul_one (b.1 W)).symm) ?_
    exact ((pushforwardUnitSection f).val.app W).hom.map_smul (b.1 W) one
  refine h₁.trans ((hθ _ c).symm.trans ((congrArg (θ.app _) (h₂.trans h₃)).trans
    ((moduleSMulObj_naturality (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U θ _ _).trans ?_)))
  refine Eq.trans (congrArg (moduleSMulObj (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U
      (sectionsFunctor X.J Z) _)
    ((congrArg (θ.app _) hs₀).trans (hθ _ (e (𝟙 U))))) ?_
  exact (sectionsFunctor_map_moduleSMulHom
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O) U Z _ _).trans
    (mul_one (M := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj Z) _)

end Stacks.Cohomology.SiteModules

end

end
