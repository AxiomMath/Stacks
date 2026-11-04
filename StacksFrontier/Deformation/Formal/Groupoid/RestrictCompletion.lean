module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Formal.Groupoid.Completion
public import StacksFrontier.Deformation.Formal.Groupoid.LimitPreserving

/-!
# Completion of the restriction of a groupoid in functors

A groupoid in functors on complete local `Λ`-algebras whose object and arrow functors
preserve limits is canonically isomorphic to the completion of its restriction to Artinian
local algebras. On objects and on arrows the inverse of this isomorphism is the unit of the
restriction--completion adjunction for set-valued functors.

## Main results

* `Deformation.GroupoidInFunctors.completionRestrictionIso`: the canonical groupoid
  isomorphism, with its object and arrow components identified.

## Implementation notes

The isomorphism is packaged with the equations identifying the components of its inverse,
so the statement pins down the canonical comparison rather than merely asserting that some
isomorphism exists.

A morphism of groupoids in functors carries the data of its object and arrow maps together
with compatibility with source, target, identity and composition; the identity clause is
redundant, and `Deformation.groupoidMap_id_of_comp` derives it from the other three.

## References

* [Stacks Project, Tag 06KF](https://stacks.math.columbia.edu/tag/06KF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace Deformation

universe u v w z

/-- The comparisons attached to limit-preserving functors are natural in the
functor. -/
private theorem cofiberedCompletionRestrictionIso_naturality
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (F H : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
    [PreservesLimits F] [PreservesLimits H] (f : F ⟶ H) :
    (cofiberedCompletion (Λ := Λ) (k := k)).map
        (((Functor.whiskeringLeft
          (ArtinianLocalAlgCat.{u, v, w} Λ k)
          (CompleteLocalAlgCat.{u, v, w} Λ k)
          (Type (max v z))).obj
            (artinianToComplete (Λ := Λ) (k := k))).map f) ≫
        (cofiberedCompletionRestrictionIso H).hom =
      (cofiberedCompletionRestrictionIso F).hom ≫ f := by
  let adj := cofiberedCompletionAdjunction.{u, v, w, z} (Λ := Λ) (k := k)
  have hn := adj.unit.naturality f
  let := cofiberedCompletionUnit_isIso H
  let isoF := cofiberedCompletionRestrictionIso F
  let isoH := cofiberedCompletionRestrictionIso H
  have hF : isoF.hom ≫ adj.unit.app F =
      𝟙 (cofiberedCompletion.obj
        (artinianToComplete (Λ := Λ) (k := k) ⋙ F)) := by
    simpa only [isoF, Functor.comp_obj,
      cofiberedCompletionRestrictionIso_inv]
      using isoF.hom_inv_id
  have hH : isoH.hom ≫ adj.unit.app H =
      𝟙 (cofiberedCompletion.obj
        (artinianToComplete (Λ := Λ) (k := k) ⋙ H)) := by
    simpa only [isoH, Functor.comp_obj,
      cofiberedCompletionRestrictionIso_inv]
      using isoH.hom_inv_id
  apply (cancel_mono (adj.unit.app H)).1
  let cf := (cofiberedCompletion (Λ := Λ) (k := k)).map
    (((Functor.whiskeringLeft
      (ArtinianLocalAlgCat.{u, v, w} Λ k)
      (CompleteLocalAlgCat.{u, v, w} Λ k)
      (Type (max v z))).obj
        (artinianToComplete (Λ := Λ) (k := k))).map f)
  calc
    cf ≫ isoH.hom ≫ adj.unit.app H = cf := by
      simp [hH]
    _ = isoF.hom ≫ f ≫ adj.unit.app H := by
      calc
        cf = isoF.hom ≫ adj.unit.app F ≫ cf := by
          rw [← Category.assoc, hF, Category.id_comp]
        _ = isoF.hom ≫ f ≫ adj.unit.app H := by
          simpa [cf, Functor.comp_obj, Functor.comp_map, Category.assoc] using
            congrArg (fun α => isoF.hom ≫ α) hn.symm

/-- The identity clause in a morphism of groupoids in functors is a consequence of
compatibility with source, target and composition. -/
public theorem groupoidMap_id_of_comp
    {C : Type u} [Category.{v} C] {G H : GroupoidInFunctors C}
    (mapObjects : G.objects ⟶ H.objects) (mapArrows : G.arrows ⟶ H.arrows)
    (map_source : ∀ (T : C) (a : G.arrows.obj T),
      H.source.app T (mapArrows.app T a) = mapObjects.app T (G.source.app T a))
    (map_target : ∀ (T : C) (a : G.arrows.obj T),
      H.target.app T (mapArrows.app T a) = mapObjects.app T (G.target.app T a))
    (map_comp : ∀ (T : C) (a b : G.arrows.obj T)
      (h : G.source.app T a = G.target.app T b),
      H.compose T (mapArrows.app T a) (mapArrows.app T b)
          ((map_source T a).trans ((congrArg (mapObjects.app T) h).trans
            (map_target T b).symm)) = mapArrows.app T (G.compose T a b h)) :
    ∀ (T : C) (x : G.Evaluation T),
      mapArrows.app T (G.identity T x) = H.identity T (mapObjects.app T x) := by
  intro T x
  let : Groupoid (G.Evaluation T) := G.evaluationGroupoid T
  let : Groupoid (H.Evaluation T) := H.evaluationGroupoid T
  let y : H.Evaluation T := mapObjects.app T x
  let a := mapArrows.app T (G.identity T x)
  have hGsource : G.source.app T (G.identity T x) = x :=
    (G.evaluationArrowEquiv T x x (𝟙 x)).2.1
  have hGtarget : G.target.app T (G.identity T x) = x :=
    (G.evaluationArrowEquiv T x x (𝟙 x)).2.2
  have hasource : H.source.app T a = y := by
    dsimp [a, y]
    rw [map_source, hGsource]
  have hatarget : H.target.app T a = y := by
    dsimp [a, y]
    rw [map_target, hGtarget]
  let f : y ⟶ y := (H.evaluationArrowEquiv T y y).symm ⟨a, hasource, hatarget⟩
  have hsourceTarget : G.source.app T (G.identity T x) =
      G.target.app T (G.identity T x) := hGsource.trans hGtarget.symm
  have hcompMap := map_comp T (G.identity T x) (G.identity T x) hsourceTarget
  have hsourceComp : G.compose T (G.identity T x) (G.identity T x) hsourceTarget =
      G.identity T x := by
    simpa only [Category.id_comp, GroupoidInFunctors.identity] using
      (G.evaluationArrowEquiv_comp T (𝟙 x) (𝟙 x)).symm
  have hcompVal : H.compose T a a
      ((map_source T (G.identity T x)).trans
        ((congrArg (mapObjects.app T) hsourceTarget).trans
          (map_target T (G.identity T x)).symm)) = a := by
    rw [hsourceComp] at hcompMap
    simpa [a, y] using hcompMap
  have hff : f ≫ f = f := by
    apply (H.evaluationArrowEquiv T y y).injective
    apply Subtype.ext
    show (H.evaluationArrowEquiv T y y (f ≫ f)).1 =
      (H.evaluationArrowEquiv T y y f).1
    rw [H.evaluationArrowEquiv_comp]
    simpa [f] using hcompVal
  have hf_id : f = 𝟙 y := by
    apply (cancel_mono f).1
    simp [hff]
  have hval := congrArg (fun g => (H.evaluationArrowEquiv T y y g).1) hf_id
  simpa [a, y, f, H.evaluationArrowEquiv_id] using hval

namespace GroupoidInFunctors

/-- The canonical groupoid isomorphism from the completion of a restricted
limit-preserving groupoid to the original groupoid. -/
@[stacks 06KF "restrict_completion"]
public noncomputable def completionRestrictionIso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors.{_, v, max v z}
      (CompleteLocalAlgCat.{u, v, w} Λ k))
    [PreservesLimits G.objects] [PreservesLimits G.arrows] :
    { i : GroupoidInFunctors.completion
        (GroupoidInFunctors.restrict G
          (artinianToComplete (Λ := Λ) (k := k))) ≅ G //
      i.inv.mapObjects =
        (cofiberedCompletionAdjunction (Λ := Λ) (k := k)).unit.app
          G.objects ∧
      i.inv.mapArrows =
        (cofiberedCompletionAdjunction (Λ := Λ) (k := k)).unit.app
          G.arrows } := by
  let G₀ := GroupoidInFunctors.restrict G
    (artinianToComplete (Λ := Λ) (k := k))
  let Gc := GroupoidInFunctors.completion G₀
  let uIso := cofiberedCompletionRestrictionIso G.objects
  let rIso := cofiberedCompletionRestrictionIso G.arrows
  let C := composableArrows G.objects G.arrows G.source G.target
  let inc := artinianToComplete (Λ := Λ) (k := k)
  have hRestrSource : G₀.source = inc.whiskerLeft G.source := by
    ext T a
    rfl
  have hRestrTarget : G₀.target = inc.whiskerLeft G.target := by
    ext T a
    rfl
  have hRestrComp : G₀.comp = inc.whiskerLeft G.comp := by
    ext T a
    rfl
  have hRestrFirst : composableFirst G₀.objects G₀.arrows G₀.source G₀.target =
      inc.whiskerLeft (composableFirst G.objects G.arrows G.source G.target) := by
    ext T a
    rfl
  have hRestrSecond : composableSecond G₀.objects G₀.arrows G₀.source G₀.target =
      inc.whiskerLeft (composableSecond G.objects G.arrows G.source G.target) := by
    ext T a
    rfl
  have hGcSource : Gc.source = (cofiberedCompletion (Λ := Λ) (k := k)).map
      (inc.whiskerLeft G.source) := by
    ext T a
    rfl
  have hGcTarget : Gc.target = (cofiberedCompletion (Λ := Λ) (k := k)).map
      (inc.whiskerLeft G.target) := by
    ext T a
    rfl
  have huinj := natIso_app_injective uIso
  have hrinj := natIso_app_injective rIso
  let hMapSource : ∀ (T : CompleteLocalAlgCat.{u, v, w} Λ k) (a : Gc.arrows.obj T),
      G.source.app T (rIso.hom.app T a) = uIso.hom.app T (Gc.source.app T a) := by
    intro T a
    have hn := cofiberedCompletionRestrictionIso_naturality G.arrows G.objects G.source
    have hnapp := congrArg (fun f => f.app T a) hn
    rw [congrArg (fun f => f.app T a) hGcSource]
    simpa [Gc, GroupoidInFunctors.completion, G₀, GroupoidInFunctors.restrict,
      Category.assoc, Functor.comp_obj, Functor.comp_map] using hnapp.symm
  let hMapTarget : ∀ (T : CompleteLocalAlgCat.{u, v, w} Λ k) (a : Gc.arrows.obj T),
      G.target.app T (rIso.hom.app T a) = uIso.hom.app T (Gc.target.app T a) := by
    intro T a
    have hn := cofiberedCompletionRestrictionIso_naturality G.arrows G.objects G.target
    have hnapp := congrArg (fun f => f.app T a) hn
    rw [congrArg (fun f => f.app T a) hGcTarget]
    simpa [Gc, GroupoidInFunctors.completion, G₀, GroupoidInFunctors.restrict,
      Category.assoc, Functor.comp_obj, Functor.comp_map] using hnapp.symm
  let hMapComp : ∀ (T : CompleteLocalAlgCat.{u, v, w} Λ k)
      (a b : Gc.arrows.obj T) (hab : Gc.source.app T a = Gc.target.app T b),
      G.compose T (rIso.hom.app T a) (rIso.hom.app T b)
          ((hMapSource T a).trans ((congrArg (uIso.hom.app T) hab).trans
            (hMapTarget T b).symm)) = rIso.hom.app T (Gc.compose T a b hab) := by
    intro T a b hab
    let D := GroupoidInFunctors.completionData G₀
    let p : (composableArrows Gc.objects Gc.arrows Gc.source Gc.target).obj T :=
      ⟨(a, b), hab⟩
    have hab₀ : G.source.app T (rIso.hom.app T a) =
        G.target.app T (rIso.hom.app T b) := by
      simpa only [hMapSource, hMapTarget] using congrArg (uIso.hom.app T) hab
    let p₀ : C.obj T := ⟨(rIso.hom.app T a, rIso.hom.app T b), hab₀⟩
    let adj := cofiberedCompletionAdjunction.{u, v, w, z}
      (Λ := Λ) (k := k)
    let q₀ := (adj.unit.app C).app T p₀
    have hRunit : (adj.unit.app G.arrows).app T (rIso.hom.app T a) = a := by
      have hh := congrArg (fun f => f.app T a) rIso.hom_inv_id
      simpa [adj, rIso,
        cofiberedCompletionRestrictionIso_inv] using hh
    have hRunitB : (adj.unit.app G.arrows).app T (rIso.hom.app T b) = b := by
      have hh := congrArg (fun f => f.app T b) rIso.hom_inv_id
      simpa [adj, rIso,
        cofiberedCompletionRestrictionIso_inv] using hh
    have hfirstD : (D.comparison.hom.app T q₀).1.1 = a := by
      have hh := congrArg (fun f => f.app T q₀) D.first_comm
      have hu := congrArg (fun f => f.app T p₀) (adj.unit.naturality
        (composableFirst G.objects G.arrows G.source G.target))
      have hu' : ((cofiberedCompletion (Λ := Λ) (k := k)).map
          (inc.whiskerLeft
            (composableFirst G.objects G.arrows G.source G.target))).app
            T q₀ = (adj.unit.app G.arrows).app T (rIso.hom.app T a) := by
        simpa [q₀, p₀, C, G₀, GroupoidInFunctors.restrict, adj,
          composableFirst, Category.assoc, Functor.comp_obj,
          Functor.comp_map] using hu.symm
      have hnat : ((cofiberedCompletion (Λ := Λ) (k := k)).map
          (composableFirst G₀.objects G₀.arrows G₀.source G₀.target)).app
            T q₀ = (adj.unit.app G.arrows).app T (rIso.hom.app T a) := by
        simpa only [hRestrFirst] using hu'
      exact hh.trans (hnat.trans hRunit)
    have hsecondD : (D.comparison.hom.app T q₀).1.2 = b := by
      have hh := congrArg (fun f => f.app T q₀) D.second_comm
      have hu := congrArg (fun f => f.app T p₀) (adj.unit.naturality
        (composableSecond G.objects G.arrows G.source G.target))
      have hu' : ((cofiberedCompletion (Λ := Λ) (k := k)).map
          (inc.whiskerLeft
            (composableSecond G.objects G.arrows G.source G.target))).app
            T q₀ = (adj.unit.app G.arrows).app T (rIso.hom.app T b) := by
        simpa [q₀, p₀, C, G₀, GroupoidInFunctors.restrict, adj,
          composableSecond, Category.assoc, Functor.comp_obj,
          Functor.comp_map] using hu.symm
      have hnat : ((cofiberedCompletion (Λ := Λ) (k := k)).map
          (composableSecond G₀.objects G₀.arrows G₀.source G₀.target)).app
            T q₀ = (adj.unit.app G.arrows).app T (rIso.hom.app T b) := by
        simpa only [hRestrSecond] using hu'
      exact hh.trans (hnat.trans hRunitB)
    have hD : D.comparison.hom.app T q₀ = p := Subtype.ext (Prod.ext hfirstD hsecondD)
    have hq : D.comparison.inv.app T p = q₀ := by
      rw [← hD]
      simp
    have huComp := congrArg (fun f => f.app T p₀) (adj.unit.naturality G.comp)
    have huComp' : ((cofiberedCompletion (Λ := Λ) (k := k)).map
        (inc.whiskerLeft G.comp)).app T q₀ =
        (adj.unit.app G.arrows).app T (G.comp.app T p₀) := by
      simpa [q₀, p₀, G₀, GroupoidInFunctors.restrict, adj,
        Category.assoc, Functor.comp_obj, Functor.comp_map] using huComp.symm
    have hnatComp : ((cofiberedCompletion (Λ := Λ) (k := k)).map G₀.comp).app T q₀ =
        (adj.unit.app G.arrows).app T (G.comp.app T p₀) := by
      simpa only [hRestrComp] using huComp'
    have hRunitComp : rIso.hom.app T ((adj.unit.app G.arrows).app T
        (G.comp.app T p₀)) = G.comp.app T p₀ := by
      have hh := congrArg (fun f => f.app T (G.comp.app T p₀)) rIso.inv_hom_id
      simpa [adj, rIso,
        cofiberedCompletionRestrictionIso_inv] using hh
    change G.comp.app T p₀ = rIso.hom.app T (Gc.comp.app T p)
    calc
      G.comp.app T p₀ = rIso.hom.app T
          ((adj.unit.app G.arrows).app T (G.comp.app T p₀)) := hRunitComp.symm
      _ = rIso.hom.app T
          (((cofiberedCompletion (Λ := Λ) (k := k)).map G₀.comp).app T q₀) := by
        rw [← hnatComp]
      _ = rIso.hom.app T (Gc.comp.app T p) := by
        congr 1
        change ((cofiberedCompletion (Λ := Λ) (k := k)).map G₀.comp).app T q₀ =
          ((cofiberedCompletion (Λ := Λ) (k := k)).map G₀.comp).app T
            (D.comparison.inv.app T p)
        rw [hq]
  let h : Gc ⟶ G := {
    mapObjects := uIso.hom
    mapArrows := rIso.hom
    map_source := hMapSource
    map_target := hMapTarget
    map_id := groupoidMap_id_of_comp (C := CompleteLocalAlgCat.{u, v, w} Λ k)
      (G := Gc) (H := G) uIso.hom rIso.hom hMapSource hMapTarget hMapComp
    map_comp := hMapComp
  }
  let hInvSource : ∀ (T : CompleteLocalAlgCat.{u, v, w} Λ k) (a : G.arrows.obj T),
      Gc.source.app T (rIso.inv.app T a) = uIso.inv.app T (G.source.app T a) := by
    intro T a
    apply huinj T
    calc
      uIso.hom.app T (Gc.source.app T (rIso.inv.app T a)) =
          G.source.app T (rIso.hom.app T (rIso.inv.app T a)) :=
        (hMapSource T (rIso.inv.app T a)).symm
      _ = G.source.app T a := by simp
      _ = uIso.hom.app T (uIso.inv.app T (G.source.app T a)) := by simp
  let hInvTarget : ∀ (T : CompleteLocalAlgCat.{u, v, w} Λ k) (a : G.arrows.obj T),
      Gc.target.app T (rIso.inv.app T a) = uIso.inv.app T (G.target.app T a) := by
    intro T a
    apply huinj T
    calc
      uIso.hom.app T (Gc.target.app T (rIso.inv.app T a)) =
          G.target.app T (rIso.hom.app T (rIso.inv.app T a)) :=
        (hMapTarget T (rIso.inv.app T a)).symm
      _ = G.target.app T a := by simp
      _ = uIso.hom.app T (uIso.inv.app T (G.target.app T a)) := by simp
  let hInvComp : ∀ (T : CompleteLocalAlgCat.{u, v, w} Λ k)
      (a b : G.arrows.obj T) (hab : G.source.app T a = G.target.app T b),
      Gc.compose T (rIso.inv.app T a) (rIso.inv.app T b)
          ((hInvSource T a).trans ((congrArg (uIso.inv.app T) hab).trans
            (hInvTarget T b).symm)) = rIso.inv.app T (G.compose T a b hab) := by
    intro T a b hab
    have hab' : Gc.source.app T (rIso.inv.app T a) =
        Gc.target.app T (rIso.inv.app T b) := by
      apply huinj T
      calc
        uIso.hom.app T (Gc.source.app T (rIso.inv.app T a)) = G.source.app T a := by
          rw [← hMapSource]
          simp
        _ = G.target.app T b := hab
        _ = uIso.hom.app T (Gc.target.app T (rIso.inv.app T b)) := by
          rw [← hMapTarget]
          simp
    apply hrinj T
    calc
      rIso.hom.app T
          (Gc.compose T (rIso.inv.app T a) (rIso.inv.app T b) hab') =
          G.compose T (rIso.hom.app T (rIso.inv.app T a))
            (rIso.hom.app T (rIso.inv.app T b)) _ :=
        (h.map_comp T (rIso.inv.app T a) (rIso.inv.app T b) hab').symm
      _ = G.compose T a b hab := by simp
      _ = rIso.hom.app T (rIso.inv.app T (G.compose T a b hab)) := by simp
  let hInv : G ⟶ Gc := {
    mapObjects := uIso.inv
    mapArrows := rIso.inv
    map_source := hInvSource
    map_target := hInvTarget
    map_id := groupoidMap_id_of_comp (C := CompleteLocalAlgCat.{u, v, w} Λ k)
      (G := G) (H := Gc) uIso.inv rIso.inv hInvSource hInvTarget hInvComp
    map_comp := hInvComp
  }
  let i : Gc ≅ G := {
    hom := h
    inv := hInv
    hom_inv_id := by
      change GroupoidInFunctors.Hom.comp h hInv = GroupoidInFunctors.Hom.id Gc
      ext <;> simp [h, hInv]
    inv_hom_id := by
      change GroupoidInFunctors.Hom.comp hInv h = GroupoidInFunctors.Hom.id G
      ext <;> simp [h, hInv]
  }
  exact ⟨i, rfl, rfl⟩

end GroupoidInFunctors

end Deformation
