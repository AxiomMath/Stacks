module

public import StacksFrontier.Deformation.ToposThickening.Helpers.ObstructionDescentNaturality
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPushforwardComp
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModuleCompIsoComparison

/-!
# The direct images of modules of two thickenings related by a morphism of their targets

Let `i₁ : X ⟶ Y₁` and `i₂ : X ⟶ Y₂` be thickenings of one ringed topos and `j : Y₂ ⟶ Y₁` a
morphism of their targets (`Deformation.ToposThickening.ThickeningTargetMorphism`), with
`Ψ₀ = ρ^*j_*` on modules over the bases. Given an isomorphism `θ : j_*i₂_* ≅ i₁_*` of direct
images of sheaves of sets which carries `ρ` to the identity of `i₁_*O_X`, this file builds the
isomorphism `Ψ₀ ∘ i₂_* ≅ i₁_*` of direct images of modules
(`Deformation.ToposThickening.ThickeningTargetMorphism.thickenedModulesCompIso`) and records that
it is `θ` on underlying sheaves of sets.

This module is a helper and carries no `@[stacks]` attribute.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 0CYF](https://stacks.math.columbia.edu/tag/0CYF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPullback (pullbackRingSheaf)

universe v u v₁ u₁ v₂ u₂ w

namespace Deformation.ToposThickening.ThickeningTargetMorphism

variable {X : RingedTopos.{v, u, w}} {Y₁ : RingedTopos.{v₁, u₁, w}} {Y₂ : RingedTopos.{v₂, u₂, w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y₁.J.HasSheafCompose (forget RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₁.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y₂.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {i₁ : RingedToposHom X Y₁} {i₂ : RingedToposHom X Y₂} (D : ThickeningTargetMorphism i₁ i₂)

/-- **`Ψ₀ ∘ i₂_* ≅ i₁_*` on modules**, from an isomorphism `θ : j_*i₂_* ≅ i₁_*` of direct images
of sheaves of sets, a map `β` of the direct images of `O_X` lying over `θ`, and the identity
saying that `β` carries the structure map of `j ∘ i₂` to that of `i₁`. -/
noncomputable def thickenedModulesCompIso
    (θ : (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).toToposHom.pushforward ≅
      (pushforwardRingToposHom i₁ X.O).toToposHom.pushforward)
    (β : pullbackRingSheaf Y₁.J
        (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).toToposHom.pushforward
        (Stacks.SheafOfModules.Tensor.ringSheaf (reshape X X.O).O) ⟶
      pullbackRingSheaf Y₁.J (pushforwardRingToposHom i₁ X.O).toToposHom.pushforward
        (Stacks.SheafOfModules.Tensor.ringSheaf (reshape X X.O).O))
    (hβ : (sheafCompose Y₁.J (forget RingCat.{w})).map β =
      θ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (reshape X X.O).O)))
    (hstruct : (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).structureRingMap ≫ β =
      (pushforwardRingToposHom i₁ X.O).structureRingMap) :
    thickenedModulesFunctor i₂ ⋙ D.basePushforward ≅ thickenedModulesFunctor i₁ :=
  (RingedToposHom.pushforwardModulesCompIso (pushforwardRingToposHom i₂ X.O) D.baseHom).symm ≪≫
    RingedToposHom.pushforwardModulesIsoOfPushforwardIso
      (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)) (pushforwardRingToposHom i₁ X.O) θ β hβ
      hstruct

/-- **`Ψ₀ ∘ i₂_* ≅ i₁_*` is `θ` on underlying sheaves of sets.** -/
theorem moduleSheafFunctor_map_thickenedModulesCompIso_hom_app
    (θ : (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).toToposHom.pushforward ≅
      (pushforwardRingToposHom i₁ X.O).toToposHom.pushforward)
    (β : pullbackRingSheaf Y₁.J
        (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).toToposHom.pushforward
        (Stacks.SheafOfModules.Tensor.ringSheaf (reshape X X.O).O) ⟶
      pullbackRingSheaf Y₁.J (pushforwardRingToposHom i₁ X.O).toToposHom.pushforward
        (Stacks.SheafOfModules.Tensor.ringSheaf (reshape X X.O).O))
    (hβ : (sheafCompose Y₁.J (forget RingCat.{w})).map β =
      θ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (reshape X X.O).O)))
    (hstruct : (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).structureRingMap ≫ β =
      (pushforwardRingToposHom i₁ X.O).structureRingMap)
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) :
    (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))).map
        ((D.thickenedModulesCompIso θ β hβ hstruct).hom.app M) =
      θ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) := by
  have h1 : (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))).map
      ((RingedToposHom.pushforwardModulesCompIso (pushforwardRingToposHom i₂ X.O)
        D.baseHom).inv.app M) =
      𝟙 ((D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).toToposHom.pushforward.obj
        (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M)) :=
    Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_ofSheafHom _ _ _
  have h2 := RingedToposHom.moduleSheafFunctor_map_pushforwardModulesIsoOfPushforwardIso_hom_app
    (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)) (pushforwardRingToposHom i₁ X.O) θ β hβ
    hstruct M
  exact ((Sheaf.moduleSheafFunctor _).map_comp _ _).trans
    ((congrArg₂ (· ≫ ·) h1 h2).trans (Category.id_comp _))

/-- **`Ψ₀ ∘ i₂_* ≅ i₁_*` together with its value `θ` on underlying sheaves of sets**, elaborated
once: a consumer that only needs an isomorphism which is `θ` on sheaves of sets takes the two
components, and never compares the type of `hβ` again. -/
noncomputable def thickenedModulesCompIsoWithSheafMap
    (θ : (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).toToposHom.pushforward ≅
      (pushforwardRingToposHom i₁ X.O).toToposHom.pushforward)
    (β : pullbackRingSheaf Y₁.J
        (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).toToposHom.pushforward
        (Stacks.SheafOfModules.Tensor.ringSheaf (reshape X X.O).O) ⟶
      pullbackRingSheaf Y₁.J (pushforwardRingToposHom i₁ X.O).toToposHom.pushforward
        (Stacks.SheafOfModules.Tensor.ringSheaf (reshape X X.O).O))
    (hβ : (sheafCompose Y₁.J (forget RingCat.{w})).map β =
      θ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (reshape X X.O).O)))
    (hstruct : (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).structureRingMap ≫ β =
      (pushforwardRingToposHom i₁ X.O).structureRingMap) :
    { E : thickenedModulesFunctor i₂ ⋙ D.basePushforward ≅ thickenedModulesFunctor i₁ //
      ∀ M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O),
        (Sheaf.moduleSheafFunctor (Stacks.SheafOfModules.Tensor.ringSheaf (baseRing i₁))).map
            (E.hom.app M) =
          θ.hom.app (Sheaf.moduleSheaf (Stacks.SheafOfModules.Tensor.ringSheaf X.O) M) } :=
  ⟨D.thickenedModulesCompIso θ β hβ hstruct,
    D.moduleSheafFunctor_map_thickenedModulesCompIso_hom_app θ β hβ hstruct⟩

omit [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₁.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y₂.J.HasSheafCompose (forget AddCommGrpCat.{w})] in
/-- **The structure maps are compatible with the map of direct images of `O_X` induced by `θ`**,
as soon as `ρ` followed by `j_*i₂_* = (j ∘ i₂)_*` is inverse to `θ` on `O_X`, on underlying
sheaves of sets. -/
theorem structureRingMap_comp_pullbackRingSheafMapOfNatTrans
    (θ : (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).toToposHom.pushforward ≅
      (pushforwardRingToposHom i₁ X.O).toToposHom.pushforward)
    (h : (sheafCompose Y₁.J (forget CommRingCat.{w})).map
        (D.ρ ≫ (Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso i₂.toToposHom
          D.j.toToposHom X.O).hom) ≫
        θ.hom.app (Sheaf.ringSheaf (Stacks.SheafOfModules.Tensor.ringSheaf (reshape X X.O).O)) =
      𝟙 _) :
    (D.baseHom.comp (pushforwardRingToposHom i₂ X.O)).structureRingMap ≫
        Stacks.Sheaves.ToposPullback.pullbackRingSheafMapOfNatTrans Y₁.J
          (Stacks.SheafOfModules.Tensor.ringSheaf (reshape X X.O).O) θ.hom =
      (pushforwardRingToposHom i₁ X.O).structureRingMap := by
  refine (sheafCompose Y₁.J (forget RingCat.{w})).map_injective ?_
  refine ((sheafCompose Y₁.J (forget RingCat.{w})).map_comp _ _).trans ?_
  refine (congrArg (_ ≫ ·) (Stacks.Sheaves.ToposPullback.ringSheafMap_pullbackRingSheafMapOfNatTrans
    Y₁.J (Stacks.SheafOfModules.Tensor.ringSheaf (reshape X X.O).O) θ.hom)).trans ?_
  change (sheafCompose Y₁.J (forget CommRingCat.{w})).map
      (D.ρ ≫ (Stacks.Sheaves.ToposPushforward.pushforwardCommRingFunctor D.j.toToposHom).map
          (𝟙 _) ≫
        (Stacks.Sheaves.ToposPushforward.pushforwardCommRingCompIso i₂.toToposHom
          D.j.toToposHom X.O).hom) ≫ _ =
    (sheafCompose Y₁.J (forget CommRingCat.{w})).map (𝟙 _)
  rw [CategoryTheory.Functor.map_id, Category.id_comp]
  exact h.trans (CategoryTheory.Functor.map_id _ _).symm

end Deformation.ToposThickening.ThickeningTargetMorphism

end
