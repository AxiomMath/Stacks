module

public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.RelativeCechComplex
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.Composition
public import StacksCore.Tactic.StacksAttribute

/-!
# Pullback maps for direct images of presheaves and sheaves

Let `h : V ⥤ U` and `f : U ⥤ X` be composable functors. A presheaf `G` on `U` has a canonical
map from its direct image along `f` to the direct image along `h ⋙ f` of its restriction along
`h`; it is the direct image of the unit of the restriction/direct-image adjunction for `h`,
followed by the canonical comparison of iterated direct image with direct image along the
composite. When `V`, `U`, `X` carry topologies and the functors are (co)continuous, the same
recipe in sheaves produces a map of sheaf direct images, and the two agree: the sheaf map is
the presheaf map after forgetting the sheaf conditions.

The coface maps of the relative Čech complex of `Stacks.RelativeCech.complex` are exactly these
pullback maps, for `h` a reindexing functor of the relative Čech nerve.

## Main definitions

* `Stacks.presheafPullbackMap`: the canonical pullback map on direct images of presheaves.
* `Stacks.sheafPullbackMap`: its counterpart for sheaves.

## Main results

* `Stacks.presheafPullbackMap_natural`, `Stacks.sheafPullbackMap_natural`: naturality in the
  coefficient presheaf, resp. sheaf.
* `Stacks.RelativeCech.reindexMap_eq_presheafPullbackMap`: the reindexing maps of the relative
  Čech complex are these pullback maps.
* `Stacks.sheafPullbackMap_hom`: the underlying presheaf morphism of the sheaf pullback map is
  the presheaf pullback map.

## Implementation notes

Restriction of presheaves is precomposition with the opposite functor and direct image is right
Kan extension along it, so the construction only needs the relevant right Kan extensions to
exist; categories fibred in groupoids over the big fppf site are the case of interest but play
no role in the proofs. The comparison of iterated direct image with direct image along a
composite is `AlgebraicGeometry.ranCompIso`.

For sheaves the hypotheses are that `f` be cocontinuous and `h` be both continuous and
cocontinuous, which is what Stacks 06TS provides for a `1`-morphism of categories fibred in
groupoids with any of the five inherited topologies. Direct image of sheaves along a
cocontinuous functor is the restriction of the presheaf right Kan extension, and the
compositor is `AlgebraicGeometry.sheafPushforwardCocontinuousCompIso`, so
`Stacks.sheafPullbackMap_hom` identifies the two constructions themselves rather than merely
the objects they connect.

Because reindexing of relative Čech tuples commutes strictly with the projection to `X`
(`Stacks.RelativeCech.projection_reindex`), the identification of the Čech reindexing maps with
pullback maps carries no transport along an isomorphism of functors.

## References

* [Stacks Project, Tag 06X8](https://stacks.math.columbia.edu/tag/06X8)
-/

@[expose] public section

open CategoryTheory
open scoped Simplicial

namespace Stacks

universe vV vU vX vA uV uU uX uA

section Presheaf

variable {V : Type uV} {U : Type uU} {X : Type uX} {A : Type uA}
    [Category.{vV} V] [Category.{vU} U] [Category.{vX} X] [Category.{vA} A]
    (f : U ⥤ X) (h : V ⥤ U)
    [∀ P : Vᵒᵖ ⥤ A, h.op.HasRightKanExtension P]
    [∀ P : Uᵒᵖ ⥤ A, f.op.HasRightKanExtension P]
    [∀ P : Vᵒᵖ ⥤ A, (h.op ⋙ f.op).HasRightKanExtension P]

/-- **Stacks 06X8.** The canonical map from the direct image of a presheaf along `f` to the
direct image along `h ⋙ f` of its restriction along `h`: the direct image of the adjunction
unit for `h`, followed by the comparison from iterated direct image to direct image along the
composite. -/
@[stacks 06X8 "the pullback map on presheaf direct images"]
public noncomputable def presheafPullbackMap (G : Uᵒᵖ ⥤ A) :
    f.op.ran.obj G ⟶ (h.op ⋙ f.op).ran.obj (h.op ⋙ G) :=
  f.op.ran.map ((h.op.ranAdjunction A).unit.app G) ≫
    (AlgebraicGeometry.ranCompIso A h.op f.op).symm.hom.app (h.op ⋙ G)

/-- **Stacks 06X8.** The presheaf pullback map is natural in the presheaf. -/
@[stacks 06X8 "naturality of the pullback map on presheaf direct images"]
public theorem presheafPullbackMap_natural {G H : Uᵒᵖ ⥤ A} (α : G ⟶ H) :
    f.op.ran.map α ≫ presheafPullbackMap f h H =
      presheafPullbackMap f h G ≫
        (h.op ⋙ f.op).ran.map (Functor.whiskerLeft h.op α) := by
  simp only [presheafPullbackMap]
  let η := (h.op.ranAdjunction A).unit
  let κ := (AlgebraicGeometry.ranCompIso A h.op f.op).symm
  have hη : α ≫ η.app H = η.app G ≫
      h.op.ran.map (((Functor.whiskeringLeft Vᵒᵖ Uᵒᵖ A).obj h.op).map α) := by
    simpa [η] using (h.op.ranAdjunction A).unit.naturality α
  calc
    f.op.ran.map α ≫ f.op.ran.map (η.app H) ≫ κ.hom.app (h.op ⋙ H) =
        f.op.ran.map (α ≫ η.app H) ≫ κ.hom.app (h.op ⋙ H) := by simp [Category.assoc]
    _ = f.op.ran.map (η.app G ≫
          h.op.ran.map (((Functor.whiskeringLeft Vᵒᵖ Uᵒᵖ A).obj h.op).map α)) ≫
          κ.hom.app (h.op ⋙ H) := by rw [hη]
    _ = f.op.ran.map (η.app G) ≫
          f.op.ran.map (h.op.ran.map (((Functor.whiskeringLeft Vᵒᵖ Uᵒᵖ A).obj h.op).map α)) ≫
          κ.hom.app (h.op ⋙ H) := by simp [Category.assoc]
    _ = f.op.ran.map (η.app G) ≫ κ.hom.app (h.op ⋙ G) ≫
          (h.op ⋙ f.op).ran.map (Functor.whiskerLeft h.op α) := by
      have hmap : f.op.ran.map (h.op.ran.map
          (((Functor.whiskeringLeft Vᵒᵖ Uᵒᵖ A).obj h.op).map α)) =
          (h.op.ran ⋙ f.op.ran).map (Functor.whiskerLeft h.op α) := rfl
      rw [hmap, κ.hom.naturality (Functor.whiskerLeft h.op α)]
  simp [η, κ, Category.assoc]

/-- Restricting the counit of `f` along `h` factors through the iterated-to-composite
direct-image comparison and the counit of `h ⋙ f`. -/
private theorem whiskerLeft_ranCompIso_symm_hom_app_comp_ranCounit (Y : Vᵒᵖ ⥤ A) :
    Functor.whiskerLeft (h.op ⋙ f.op)
        ((AlgebraicGeometry.ranCompIso A h.op f.op).symm.hom.app Y) ≫
      (h.op ⋙ f.op).ranCounit.app Y =
    Functor.whiskerLeft h.op (f.op.ranCounit.app (h.op.ran.obj Y)) ≫
      h.op.ranCounit.app Y := by
  let adjComp := (h.op ⋙ f.op).ranAdjunction A
  let adjIter := ((f.op.ranAdjunction A).comp (h.op.ranAdjunction A)).ofNatIsoLeft
    (eqToIso (rfl :
      (Functor.whiskeringLeft Uᵒᵖ Xᵒᵖ A).obj f.op ⋙
          (Functor.whiskeringLeft Vᵒᵖ Uᵒᵖ A).obj h.op =
        (Functor.whiskeringLeft Vᵒᵖ Xᵒᵖ A).obj (h.op ⋙ f.op)))
  have hκ :
      (h.op.associator f.op (f.op.ran.obj (h.op.ran.obj Y))).inv ≫
        Functor.whiskerLeft (h.op ⋙ f.op)
          ((AlgebraicGeometry.ranCompIso A h.op f.op).symm.hom.app Y) ≫
        (h.op.associator f.op ((h.op ⋙ f.op).ran.obj Y)).hom ≫
        (h.op ⋙ f.op).ranCounit.app Y =
      Functor.whiskerLeft h.op (f.op.ranCounit.app (h.op.ran.obj Y)) ≫
        h.op.ranCounit.app Y := by
    simpa [adjIter, adjComp, AlgebraicGeometry.ranCompIso, Functor.whiskerRight_app,
      Functor.whiskerLeft_app, Adjunction.comp_counit_app,
      Adjunction.rightAdjointUniq_inv_app] using
        congr_app (Adjunction.rightAdjointUniq_hom_counit adjIter adjComp) Y
  ext x
  simpa [Functor.associator, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.assoc, Functor.whiskerLeft_app, NatTrans.comp_app, NatTrans.id_app,
    Category.id_comp, Category.comp_id] using congr_app hκ x

/-- **Stacks 06X8.** The defining property of the presheaf pullback map against the
Kan-extension counits: restricting the counit of `f` along `h` factors through it. -/
@[stacks 06X8 "the counit factorisation of the presheaf pullback map"]
public theorem presheafPullbackMap_whiskerLeft_ranCounit (G : Xᵒᵖ ⥤ A) :
    Functor.whiskerLeft h.op (f.op.ranCounit.app (f.op ⋙ G)) =
      Functor.whiskerLeft (h.op ⋙ f.op) (presheafPullbackMap f h (f.op ⋙ G)) ≫
        (h.op ⋙ f.op).ranCounit.app (h.op ⋙ f.op ⋙ G) := by
  simp only [presheafPullbackMap, Functor.whiskerLeft_comp, Category.assoc]
  rw [whiskerLeft_ranCompIso_symm_hom_app_comp_ranCounit f h (h.op ⋙ f.op ⋙ G)]
  let Y := h.op ⋙ (f.op ⋙ G)
  let η := (h.op.ranAdjunction A).unit.app (f.op ⋙ G)
  ext x
  simp only [Functor.whiskerLeft_app, NatTrans.comp_app]
  have hnat :
      (f.op.ran.map η).app (f.op.obj (h.op.obj x)) ≫
          (f.op.ranCounit.app (h.op.ran.obj Y)).app (h.op.obj x) =
        (f.op.ranCounit.app (f.op ⋙ G)).app (h.op.obj x) ≫ η.app (h.op.obj x) := by
    simpa [η, Functor.comp_map, Functor.whiskerLeft_app] using
      congr_app (f.op.ranCounit.naturality η) (h.op.obj x)
  calc
    (f.op.ranCounit.app (f.op ⋙ G)).app (h.op.obj x) =
        (f.op.ranCounit.app (f.op ⋙ G)).app (h.op.obj x) ≫
          (η.app (h.op.obj x) ≫ (h.op.ranCounit.app Y).app x) := by
            rw [h.op.ranCounit_app_app_ranAdjunction_unit_app_app (f.op ⋙ G) x]
            simp
    _ = ((f.op.ranCounit.app (f.op ⋙ G)).app (h.op.obj x) ≫ η.app (h.op.obj x)) ≫
          (h.op.ranCounit.app Y).app x := by simp [Category.assoc]
    _ = ((f.op.ran.map η).app (f.op.obj (h.op.obj x)) ≫
          (f.op.ranCounit.app (h.op.ran.obj Y)).app (h.op.obj x)) ≫
          (h.op.ranCounit.app Y).app x := by rw [hnat.symm]
    _ = _ := by simp [η, Y, Functor.comp_obj]

end Presheaf

namespace RelativeCech

universe vC uC w

/-- **Stacks 06X8.** Each reindexing map of the relative Čech complex of an abelian presheaf is
the canonical pullback map along the corresponding reindexing functor of relative Čech
tuples. -/
@[stacks 06X8 "the Čech reindexing maps are pullback maps"]
public theorem reindexMap_eq_presheafPullbackMap {U : Type uU} {X : Type uX} {C : Type uC}
    [Category.{vU} U] [Category.{vX} X] [Category.{vC} C] (p : X ⥤ C) (f : U ⥤ X)
    (F : Xᵒᵖ ⥤ AddCommGrpCat.{max uU uX vX vU vC w}) {m n : ℕ} (φ : ⦋m⦌ ⟶ ⦋n⦌) :
    reindexMap.{vU, vX, vC, uU, uX, uC, max vU vC w} p f F φ =
      presheafPullbackMap (Tuple.projection p f m)
        (Tuple.reindex p f φ.toOrderHom) ((Tuple.projection p f m).op ⋙ F) := by
  let Pm := Tuple.projection p f m
  let Pn := Tuple.projection p f n
  let r := Tuple.reindex p f φ.toOrderHom
  let A := AddCommGrpCat.{max uU uX vX vU vC w}
  have hr : r ⋙ Pm = Pn := projection_reindex p f φ.toOrderHom
  apply ((Pn.op.ranAdjunction A).homEquiv _ _).symm.injective
  show Functor.whiskerLeft Pn.op (reindexMap p f F φ) ≫ Pn.op.ranCounit.app (Pn.op ⋙ F) =
    Functor.whiskerLeft Pn.op (presheafPullbackMap Pm r (Pm.op ⋙ F)) ≫
      Pn.op.ranCounit.app (Pn.op ⋙ F)
  rw [reindexMap_fac (p := p) (f := f) (F := F) (m := m) (n := n) φ]
  cases hr
  exact presheafPullbackMap_whiskerLeft_ranCounit (f := Pm) (h := r) F

end RelativeCech

section Sheaf

variable {V : Type uV} {U : Type uU} {X : Type uX} {A : Type uA}
    [Category.{vV} V] [Category.{vU} U] [Category.{vX} X] [Category.{vA} A]
    (J : GrothendieckTopology V) (K : GrothendieckTopology U) (L : GrothendieckTopology X)
    (f : U ⥤ X) (h : V ⥤ U)
    [f.IsCocontinuous K L] [h.IsContinuous J K] [h.IsCocontinuous J K]
    [∀ P : Vᵒᵖ ⥤ A, h.op.HasPointwiseRightKanExtension P]
    [∀ P : Uᵒᵖ ⥤ A, f.op.HasPointwiseRightKanExtension P]
    [∀ P : Vᵒᵖ ⥤ A, (h ⋙ f).op.HasPointwiseRightKanExtension P]

/-- **Stacks 06X8.** The canonical map from the direct image of a sheaf along `f` to the direct
image along `h ⋙ f` of its restriction along `h`, formed from the unit of the
restriction/direct-image adjunction for `h` and the direct-image compositor. -/
@[stacks 06X8 "the pullback map on sheaf direct images"]
public noncomputable def sheafPullbackMap (G : Sheaf K A) :
    letI := isCocontinuous_comp h f J K (L := L)
    (f.sheafPushforwardCocontinuous A K L).obj G ⟶
      ((h ⋙ f).sheafPushforwardCocontinuous A J L).obj
        ((h.sheafPushforwardContinuous A J K).obj G) := by
  letI := isCocontinuous_comp h f J K (L := L)
  exact (f.sheafPushforwardCocontinuous A K L).map
      ((h.sheafAdjunctionCocontinuous A J K).unit.app G) ≫
    (AlgebraicGeometry.sheafPushforwardCocontinuousCompIso A J K L h f).symm.hom.app
      ((h.sheafPushforwardContinuous A J K).obj G)

/-- **Stacks 06X8.** The underlying presheaf morphism of the sheaf pullback map is the presheaf
pullback map. -/
@[stacks 06X8 "agreement of the sheaf and presheaf pullback maps"]
public theorem sheafPullbackMap_hom (G : Sheaf K A) :
    letI : ∀ P : Vᵒᵖ ⥤ A, (h.op ⋙ f.op).HasRightKanExtension P :=
      fun P => inferInstanceAs ((h ⋙ f).op.HasRightKanExtension P)
    (sheafPullbackMap J K L f h G).hom = presheafPullbackMap f h G.obj := by
  dsimp [sheafPullbackMap, Functor.sheafPushforwardCocontinuous,
    Functor.sheafPushforwardContinuous, AlgebraicGeometry.sheafPushforwardCocontinuousCompIso,
    AlgebraicGeometry.ranCompIso]
  simp only [presheafPullbackMap, Functor.comp_obj, Functor.whiskeringLeft_obj_obj,
    AlgebraicGeometry.ranCompIso, eqToIso_refl, Iso.symm_hom]
  rw [Functor.sheafAdjunctionCocontinuous_unit_app_hom]
  congr 1
  exact Functor.map_preimage (sheafToPresheaf L A) _

/-- **Stacks 06X8.** The sheaf pullback map is natural in the sheaf. -/
@[stacks 06X8 "naturality of the pullback map on sheaf direct images"]
public theorem sheafPullbackMap_natural {G H : Sheaf K A} (α : G ⟶ H) :
    letI := isCocontinuous_comp h f J K (L := L)
    (f.sheafPushforwardCocontinuous A K L).map α ≫ sheafPullbackMap J K L f h H =
      sheafPullbackMap J K L f h G ≫
        ((h ⋙ f).sheafPushforwardCocontinuous A J L).map
          ((h.sheafPushforwardContinuous A J K).map α) := by
  let _ : ∀ P : Vᵒᵖ ⥤ A, (h.op ⋙ f.op).HasRightKanExtension P :=
    fun P => inferInstanceAs ((h ⋙ f).op.HasRightKanExtension P)
  apply (sheafToPresheaf L A).map_injective
  show _ ≫ (sheafPullbackMap J K L f h H).hom = _ ≫ _
  rw [sheafPullbackMap_hom J K L f h G, sheafPullbackMap_hom J K L f h H]
  exact presheafPullbackMap_natural f h α.hom

end Sheaf

end Stacks

end
