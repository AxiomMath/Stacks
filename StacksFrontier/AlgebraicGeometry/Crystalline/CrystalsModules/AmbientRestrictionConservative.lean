module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionColimits
public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystalsModules.QuasicoherentImpliesLocal
public import StacksFrontier.AlgebraicGeometry.QcohRestrictEquiv.IsoLocality
public import StacksFrontier.CategoryTheory.Limits.CokernelOfConservativeFamily

/-!
# The ambient restrictions on a localised crystalline site are jointly conservative

Let `(U', T', δ')` be an object of the big crystalline site of a global crystalline situation and
let `𝒞/(U', T', δ')` be the localisation of the site at it.  Every object `(U, T, δ)` of that
localised site carries its own family of restrictions to the opens of its ambient scheme `T`, and
those restrictions are again objects of the localised site: the restriction of `(U, T, δ)` to an
open `W` of `T` maps to `(U, T, δ)` and hence to `(U', T', δ')`.

This file turns that observation into a family of functors of sites indexed by the objects of the
*fixed* localised site, and proves that restriction of sheaves of modules along that family is
jointly conservative.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.Thickening.ambientOverFunctor` — for an object `X` of
  the localised site `CRIS(X/S)/B`, the functor from the Zariski site of the ambient scheme of
  `X` localised at its greatest open to `CRIS(X/S)/B`, sending an open to the restriction of `X`
  to it.
* `Crystalline.GlobalCrystallineSituation.Thickening.ambientOverStructureHom` — the comparison of
  structure sheaves along that functor, which is the identity.

## Main results

* `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_iso` — invertibility of a component
  of a morphism of sheaves of modules only depends on the isomorphism class of the object.
* `Crystalline.GlobalCrystallineSituation.Thickening.isIso_of_forall_isIso_pushforward_ambientOver`
  — **the ambient restrictions on a fixed localised crystalline site are jointly conservative**: a
  morphism of sheaves of modules on `CRIS(X/S)/B` all of whose restrictions along the functors
  above are invertible is itself invertible.
* `Crystalline.GlobalCrystallineSituation.Thickening.isColimitCokernelCoforkOfForallAmbientOver`
  — consequently **a cokernel of sheaves of modules on a localised crystalline site is detected by
  the ambient restrictions**: a cofork is a cokernel as soon as each of those restrictions carries
  it to one.

## Implementation notes

The functor is built as `CategoryTheory.Over.post` of
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenFunctor` followed by
`CategoryTheory.Over.map`, so that both halves of continuity and both halves of cocontinuity are
already available: `Over.post` of the restriction functor is
`Crystalline.GlobalCrystallineSituation.Thickening.restrictOpenOverFunctor`, which is continuous
and cocontinuous because the opens of a scheme have pullbacks and the restriction functor
preserves them, and `Over.map` along any arrow is continuous and cocontinuous for the localised
topologies.  That is why the source of the functor is the slice `Over ⊤` of the opens of the
ambient scheme at its greatest element rather than the opens themselves: the opens are not of the
form `Over V` and the composite would have to have its continuity proved from scratch.

Joint conservativity is `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app`
together with `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward`: the
latter gives invertibility of the component of the morphism at every object in the image of one of
the functors, and for the functor attached to `X` itself the image of the identity arrow of the
greatest open is the restriction of `X` to the whole of its ambient scheme, which is isomorphic to
`X`.  Isomorphic objects have the same components up to conjugation by the transition maps, which
is `Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_iso`.

## References

* [Stacks Project, Tag 07IT](https://stacks.math.columbia.edu/tag/07IT)
* [Stacks Project, Tag 07IQ](https://stacks.math.columbia.edu/tag/07IQ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe w v v' u u' u₁ v₁

namespace Stacks.AlgebraicGeometry.QcohRestrictEquiv

/-- **A component of a natural transformation at an object is invertible as soon as it is
invertible at an isomorphic object.** -/
theorem isIso_natTrans_app_of_iso {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
    {F G : C ⥤ D} (α : F ⟶ G) {a b : C} (e : a ≅ b) (h : IsIso (α.app a)) :
    IsIso (α.app b) := by
  have key : α.app b = inv (F.map e.hom) ≫ α.app a ≫ G.map e.hom := by
    rw [← α.naturality e.hom, IsIso.inv_hom_id_assoc]
  rw [key]
  have := h
  infer_instance

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}

/-- A component of a morphism of sheaves of modules is invertible as soon as its image under the
forgetful functor to sheaves of abelian groups is. -/
theorem isIso_val_app_of_isIso_toSheaf_app {M N : SheafOfModules.{v} R} (φ : M ⟶ N) (W : Cᵒᵖ)
    (h : IsIso (((SheafOfModules.toSheaf R).map φ).hom.app W)) : IsIso (φ.val.app W) := by
  have h3 : IsIso ((forget₂ (ModuleCat.{v} (R.obj.obj W)) AddCommGrpCat.{v}).map
      (φ.val.app W)) := h
  exact @isIso_of_reflects_iso _ _ _ _ _ _ (φ.val.app W)
    (forget₂ (ModuleCat.{v} (R.obj.obj W)) AddCommGrpCat.{v}) h3 inferInstance

/-- **Invertibility of a component of a morphism of sheaves of modules depends only on the
isomorphism class of the object.** -/
theorem isIso_val_app_of_iso {M N : SheafOfModules.{v} R} (φ : M ⟶ N) {Z Y : C} (e : Z ≅ Y)
    (h : IsIso (φ.val.app (op Z))) : IsIso (φ.val.app (op Y)) :=
  isIso_val_app_of_isIso_toSheaf_app φ (op Y)
    (isIso_natTrans_app_of_iso ((SheafOfModules.toSheaf R).map φ).hom
      e.symm.op (isIso_toSheaf_map_hom_app φ (op Z) h))

end Stacks.AlgebraicGeometry.QcohRestrictEquiv

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace Thickening

variable (B : Thickening S)

/-- **The restrictions of an object of a localised crystalline site to the opens of its ambient
scheme, as a functor of sites into that localised site.**  For `X` an object of
`CRIS(X/S)/B` — that is, an object `A` of `CRIS(X/S)` with a morphism `A ⟶ B` — this sends an
open `W` of the ambient scheme of `A`, presented as an object of the slice of the opens at the
greatest open, to the restriction of `A` to `W`, equipped with its composite morphism to `B`. -/
noncomputable def ambientOverFunctor (X : Over B) :
    Over (⊤ : X.left.thickening.target.scheme.Opens) ⥤ Over B :=
  Over.post (X := (⊤ : X.left.thickening.target.scheme.Opens)) X.left.restrictOpenFunctor ⋙
    Over.map (X.left.restrictOpenHom ⊤ ≫ X.hom)

/-- The ambient restriction functor is continuous for the localised topologies. -/
instance isContinuous_ambientOverFunctor (X : Over B) :
    (ambientOverFunctor B X).IsContinuous
      ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over ⊤)
      ((topology S).over B) :=
  haveI := isContinuous_restrictOpenOverFunctor X.left
    (⊤ : X.left.thickening.target.scheme.Opens)
  Functor.isContinuous_comp (restrictOpenOverFunctor X.left ⊤)
    (Over.map (X.left.restrictOpenHom ⊤ ≫ X.hom))
    ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over ⊤)
    ((topology S).over (X.left.restrictOpen ⊤)) ((topology S).over B)

/-- The ambient restriction functor is cocontinuous for the localised topologies. -/
instance isCocontinuous_ambientOverFunctor (X : Over B) :
    (ambientOverFunctor B X).IsCocontinuous
      ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over ⊤)
      ((topology S).over B) :=
  haveI := isCocontinuous_restrictOpenOverFunctor X.left
    (⊤ : X.left.thickening.target.scheme.Opens)
  CategoryTheory.isCocontinuous_comp (restrictOpenOverFunctor X.left ⊤)
    (Over.map (X.left.restrictOpenHom ⊤ ≫ X.hom))
    ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over ⊤)
    ((topology S).over (X.left.restrictOpen ⊤))

/-- **The comparison of structure sheaves along the ambient restrictions**, the identity morphism
from the restriction of `𝒪_{X/S}` to the opens of the ambient scheme of `X` to the pushforward of
the restriction of `𝒪_{X/S}` to `CRIS(X/S)/B` along `ambientOverFunctor`. -/
noncomputable def ambientOverStructureHom (X : Over B) :
    (X.left.ringRestrictionSheaf).over ⊤ ⟶
      ((ambientOverFunctor B X).sheafPushforwardContinuous RingCat.{u}
        ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over ⊤)
        ((topology S).over B)).obj ((crystallineStructureSheaf S).over B) :=
  𝟙 _

/-- The comparison of structure sheaves along the ambient restrictions is an isomorphism. -/
instance isIso_ambientOverStructureHom (B : Thickening S) (X : Over B) :
    IsIso (ambientOverStructureHom B X) :=
  inferInstanceAs (IsIso (𝟙 ((X.left.ringRestrictionSheaf).over ⊤)))

/-- The structure morphism of the image under `ambientOverFunctor` of the identity arrow of the
greatest open of the ambient scheme of `X` is the composite of the image of that identity arrow,
the restriction morphism of the greatest open, and the structure morphism of `X`. -/
theorem ambientOverFunctor_obj_mk_id_hom (X : Over B) :
    ((ambientOverFunctor B X).obj
        (Over.mk (𝟙 (⊤ : X.left.thickening.target.scheme.Opens)))).hom =
      X.left.restrictOpenFunctor.map (𝟙 (⊤ : X.left.thickening.target.scheme.Opens)) ≫
        X.left.restrictOpenHom (⊤ : X.left.thickening.target.scheme.Opens) ≫ X.hom :=
  rfl

/-- **The restriction of an object of a localised crystalline site to the whole of its ambient
scheme is that object**: the image under `ambientOverFunctor` of the identity arrow of the
greatest open of the ambient scheme of `X` is isomorphic to `X`. -/
noncomputable def ambientOverFunctorObjTopIso (X : Over B) :
    (ambientOverFunctor B X).obj (Over.mk (𝟙 (⊤ : X.left.thickening.target.scheme.Opens))) ≅ X :=
  Over.isoMk
    (@asIso _ _ _ _ (X.left.restrictOpenHom (⊤ : X.left.thickening.target.scheme.Opens))
      X.left.isIso_restrictOpenHom_top)
    (by
      rw [ambientOverFunctor_obj_mk_id_hom, CategoryTheory.Functor.map_id, Category.id_comp]
      rfl)

/-- **The ambient restrictions on a fixed localised crystalline site are jointly conservative.**
A morphism of sheaves of `𝒪_{X/S}`-modules on `CRIS(X/S)/B` whose restriction along the ambient
restrictions of *every* object of that site is invertible is itself invertible. -/
theorem isIso_of_forall_isIso_pushforward_ambientOver
    {M N : SheafOfModules.{v} ((crystallineStructureSheaf S).over B)} (φ : M ⟶ N)
    (h : ∀ X : Over B,
      IsIso ((SheafOfModules.pushforward.{v} (ambientOverStructureHom B X)).map φ)) :
    IsIso φ := by
  refine Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_of_isIso_val_app φ fun W ↦ ?_
  obtain ⟨Y⟩ := W
  exact Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_iso φ
    (ambientOverFunctorObjTopIso B Y)
    (Stacks.AlgebraicGeometry.QcohRestrictEquiv.isIso_val_app_of_isIso_pushforward
      (ambientOverStructureHom B Y) φ (h Y)
      (op (Over.mk (𝟙 (⊤ : Y.left.thickening.target.scheme.Opens)))))

/-- Restriction of sheaves of modules along the ambient restrictions preserves colimits of size
`u + 1`. -/
theorem preservesColimitsOfSize_pushforward_ambientOverStructureHom (X : Over B) :
    PreservesColimitsOfSize.{u + 1, u + 1}
      (show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) ⥤
          SheafOfModules.{u + 1} ((X.left.ringRestrictionSheaf).over ⊤) from
        SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)) := by
  have _ : HasSheafify ((topology S).over B) AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u + 1} _
  have _ : ((topology S).over B).WEqualsLocallyBijective AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u + 1, u} _
  have _ : HasSheafify
      ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over ⊤)
      AddCommGrpCat.{u + 1} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{u + 1, u, u} _
  have _ : GrothendieckTopology.WEqualsLocallyBijective
      ((Opens.grothendieckTopology ↥X.left.thickening.target.scheme).over ⊤)
      AddCommGrpCat.{u + 1} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{u + 1, u, u} _
  exact Stacks.SheafOfModules.pushforward_preservesColimits.{u, u, u + 1, u + 1, u, u}
    (ambientOverFunctor B X) (ambientOverStructureHom B X)

/-- Restriction of sheaves of modules along the ambient restrictions preserves zero morphisms. -/
instance preservesZeroMorphisms_pushforward_ambientOverStructureHom (X : Over B) :
    (show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) ⥤
        SheafOfModules.{u + 1} ((X.left.ringRestrictionSheaf).over ⊤) from
      SheafOfModules.pushforward.{u + 1}
        (ambientOverStructureHom B X)).PreservesZeroMorphisms where
  map_zero _ _ := rfl

/-- **A cokernel of sheaves of `𝒪_{X/S}`-modules on a localised crystalline site is detected by
the ambient restrictions.**  A cofork is a cokernel as soon as its restriction along the ambient
restrictions of every object of the localised site is one. -/
noncomputable def isColimitCokernelCoforkOfForallAmbientOver
    {Q P N : SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B)}
    {a : Q ⟶ P} {b : P ⟶ N} (hab : a ≫ b = 0) [HasCokernel a]
    (hb : ∀ X : Over B, IsColimit (CokernelCofork.ofπ
      ((SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map b)
      (show (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map a ≫
            (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map b = 0 by
        rw [← Functor.map_comp, hab]
        exact (SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)).map_zero _ _))) :
    IsColimit (CokernelCofork.ofπ b hab) :=
  haveI : ∀ X : Over B, PreservesColimit (parallelPair a 0)
      (show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) ⥤
          SheafOfModules.{u + 1} ((X.left.ringRestrictionSheaf).over ⊤) from
        SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)) := fun X ↦ by
    have := preservesColimitsOfSize_pushforward_ambientOverStructureHom B X
    have : PreservesColimitsOfSize.{0, 0}
        (show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) ⥤
            SheafOfModules.{u + 1} ((X.left.ringRestrictionSheaf).over ⊤) from
          SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X)) :=
      preservesColimitsOfSize_shrink _
    infer_instance
  isColimitCokernelCoforkOfConservativeFamily hab
    (fun X : Over B ↦
      show SheafOfModules.{u + 1} ((crystallineStructureSheaf S).over B) ⥤
          SheafOfModules.{u + 1} ((X.left.ringRestrictionSheaf).over ⊤) from
        SheafOfModules.pushforward.{u + 1} (ambientOverStructureHom B X))
    (fun _ _ f hf ↦ isIso_of_forall_isIso_pushforward_ambientOver B f hf) hb

end Thickening

end Crystalline.GlobalCrystallineSituation

end
