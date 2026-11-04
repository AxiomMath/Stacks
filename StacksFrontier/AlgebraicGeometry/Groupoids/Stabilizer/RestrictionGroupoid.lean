module

public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Restriction
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Pullback
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Evaluation
public import StacksCore.Tactic.StacksAttribute

/-!
# Restricting a groupoid scheme

A groupoid scheme `G` can be restricted along an arbitrary morphism `g` to its scheme of
objects.  The restriction is again a groupoid scheme, with the arrow scheme of
`AlgebraicGeometry.restrictionArrows`, and it comes with a canonical morphism to `G` which on
generalized points is the full subgroupoid induced along `g`.

## Main definitions

* `AlgebraicGeometry.GroupoidScheme.Restriction` records the restricted groupoid, its
  structure maps, its canonical morphism to `G`, and the universal property.
* `AlgebraicGeometry.GroupoidScheme.restrict` constructs it.

## References

* [Stacks Project, Tag 02VB](https://stacks.math.columbia.edu/tag/02VB)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.Groupoids

universe u

namespace AlgebraicGeometry.GroupoidScheme

attribute [local simp] pullback.lift_fst pullback.lift_snd
  pullback.lift_fst_assoc pullback.lift_snd_assoc

/-- The data and universal property of the restriction of a groupoid scheme along a map to its
scheme of objects. -/
structure Restriction {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S) {U' : Over S}
    (g : U' ⟶ G.objects) where
  /-- The restricted groupoid scheme. -/
  groupoid : Stacks.Groupoids.GroupoidScheme S
  /-- Its scheme of objects is the domain of the restricting map. -/
  objects_eq : groupoid.objects = U'
  /-- Its scheme of arrows is the iterated fibre product of the source and target maps. -/
  arrows_eq : groupoid.arrows = restrictionArrows G g
  /-- Its source map is the projection to the lift of the source. -/
  source_eq : groupoid.source =
    eqToHom arrows_eq ≫ restrictionSource G g ≫ eqToHom objects_eq.symm
  /-- Its target map is the projection to the lift of the target. -/
  target_eq : groupoid.target =
    eqToHom arrows_eq ≫ restrictionTarget G g ≫ eqToHom objects_eq.symm
  /-- The canonical morphism from the restricted groupoid to the original one. -/
  hom : Stacks.Groupoids.GroupoidScheme.Hom groupoid G
  /-- The map on objects is the restricting map. -/
  mapObjects_eq : hom.mapObjects = eqToHom objects_eq ≫ g
  /-- The map on arrows is the canonical projection from the iterated fibre product. -/
  mapArrows_eq : hom.mapArrows = eqToHom arrows_eq ≫ restrictionArrowsToArrows G g
  /-- On every test scheme, the canonical functor identifies the restriction with the full
  groupoid induced on the objects mapping to the original groupoid. -/
  evaluation_fullyFaithful : ∀ T : Over S, Nonempty (hom.evaluation T).FullyFaithful

/-- Restriction of a groupoid scheme along a morphism to its scheme of objects. -/
@[stacks 02VB,
  stacks 02VC "the restriction R|_{U'} of a groupoid scheme to U', with its morphism to the",
  stacks 04MN "R' is the iterated fibre product of the displayed diagram and s', t' are its"]
noncomputable def restrict {S : Scheme.{u}} (G : Stacks.Groupoids.GroupoidScheme S)
    {U' : Over S} (g : U' ⟶ G.objects) : Restriction G g := Classical.choice (by
  constructor
  classical
  let P : Over S := restrictionArrows G g
  let src : P ⟶ U' := restrictionSource G g
  let tgt : P ⟶ U' := restrictionTarget G g
  let arr : P ⟶ G.arrows := restrictionArrowsToArrows G g
  let identTarget : U' ⟶ pullback g G.target :=
    pullback.lift (𝟙 U') (g ≫ G.identity) (by simp [G.target_identity])
  let identSource : U' ⟶ pullback G.source g :=
    pullback.lift (g ≫ G.identity) (𝟙 U') (by simp [G.source_identity])
  let ident : U' ⟶ P :=
    pullback.lift identTarget identSource (by simp [identTarget, identSource])
  have ident_fst : ident ≫ pullback.fst (pullback.snd g G.target) (pullback.fst G.source g) =
      identTarget := pullback.lift_fst _ _ _
  have ident_snd : ident ≫ pullback.snd (pullback.snd g G.target) (pullback.fst G.source g) =
      identSource := pullback.lift_snd _ _ _
  have ident_source : ident ≫ src = 𝟙 U' :=
    (Category.assoc ident _ _).symm.trans
      ((congrArg (· ≫ pullback.snd G.source g) ident_snd).trans (pullback.lift_snd _ _ _))
  have ident_target : ident ≫ tgt = 𝟙 U' :=
    (Category.assoc ident _ _).symm.trans
      ((congrArg (· ≫ pullback.fst g G.target) ident_fst).trans (pullback.lift_fst _ _ _))
  have ident_arr : ident ≫ arr = g ≫ G.identity :=
    (Category.assoc ident _ _).symm.trans
      ((congrArg (· ≫ pullback.snd g G.target) ident_fst).trans (pullback.lift_snd _ _ _))
  let invTarget : P ⟶ pullback g G.target :=
    pullback.lift src (arr ≫ G.inverse) (by simp [src, arr, G.target_inverse])
  let invSource : P ⟶ pullback G.source g :=
    pullback.lift (arr ≫ G.inverse) tgt (by simp [tgt, arr, G.source_inverse])
  let inv : P ⟶ P := pullback.lift invTarget invSource (by simp [invTarget, invSource])
  have inv_fst : inv ≫ pullback.fst (pullback.snd g G.target) (pullback.fst G.source g) =
      invTarget := pullback.lift_fst _ _ _
  have inv_snd : inv ≫ pullback.snd (pullback.snd g G.target) (pullback.fst G.source g) =
      invSource := pullback.lift_snd _ _ _
  have inv_source : inv ≫ src = tgt :=
    (Category.assoc inv _ _).symm.trans
      ((congrArg (· ≫ pullback.snd G.source g) inv_snd).trans (pullback.lift_snd _ _ _))
  have inv_target : inv ≫ tgt = src :=
    (Category.assoc inv _ _).symm.trans
      ((congrArg (· ≫ pullback.fst g G.target) inv_fst).trans (pullback.lift_fst _ _ _))
  have inv_arr : inv ≫ arr = arr ≫ G.inverse :=
    (Category.assoc inv _ _).symm.trans
      ((congrArg (· ≫ pullback.snd g G.target) inv_fst).trans (pullback.lift_snd _ _ _))
  let c : pullback src tgt ⟶ G.arrows :=
    pullback.lift (pullback.fst src tgt ≫ arr) (pullback.snd src tgt ≫ arr)
      (by
          calc
            (pullback.fst src tgt ≫ arr) ≫ G.source =
                pullback.fst src tgt ≫ src ≫ g := by
              simpa only [Category.assoc] using congrArg (pullback.fst src tgt ≫ ·)
                (restriction_condition G g).symm
            _ = pullback.snd src tgt ≫ tgt ≫ g := by
              simpa only [Category.assoc] using
                congrArg (· ≫ g)
                  (pullback.condition : pullback.fst src tgt ≫ src =
                    pullback.snd src tgt ≫ tgt)
            _ = (pullback.snd src tgt ≫ arr) ≫ G.target := by
              simpa only [Category.assoc] using congrArg (pullback.snd src tgt ≫ ·)
                (restriction_condition' G g).symm) ≫ G.comp
  let compTarget : pullback src tgt ⟶ pullback g G.target :=
    pullback.lift (pullback.fst src tgt ≫ tgt) c (by simp [c, src, tgt, arr, G.target_comp])
  let compSource : pullback src tgt ⟶ pullback G.source g :=
    pullback.lift c (pullback.snd src tgt ≫ src) (by simp [c, src, tgt, arr, G.source_comp])
  let comp : pullback src tgt ⟶ P :=
    pullback.lift compTarget compSource (by simp [compTarget, compSource])
  have comp_fst : comp ≫ pullback.fst (pullback.snd g G.target) (pullback.fst G.source g) =
      compTarget := pullback.lift_fst _ _ _
  have comp_snd : comp ≫ pullback.snd (pullback.snd g G.target) (pullback.fst G.source g) =
      compSource := pullback.lift_snd _ _ _
  have comp_source : comp ≫ src = pullback.snd src tgt ≫ src :=
    (Category.assoc comp _ _).symm.trans
      ((congrArg (· ≫ pullback.snd G.source g) comp_snd).trans (pullback.lift_snd _ _ _))
  have comp_target : comp ≫ tgt = pullback.fst src tgt ≫ tgt :=
    (Category.assoc comp _ _).symm.trans
      ((congrArg (· ≫ pullback.fst g G.target) comp_fst).trans (pullback.lift_fst _ _ _))
  have comp_arr : comp ≫ arr = c :=
    (Category.assoc comp _ _).symm.trans
      ((congrArg (· ≫ pullback.snd g G.target) comp_fst).trans (pullback.lift_snd _ _ _))
  have comp_arrow {T : Over S} (f h : T ⟶ P)
      (w : f ≫ src = h ≫ tgt) :
      (pullback.lift f h w ≫ comp) ≫ arr =
        G.compose (f ≫ arr) (h ≫ arr) (by
          calc
            (f ≫ arr) ≫ G.source = f ≫ src ≫ g := by
              simpa only [Category.assoc] using congrArg (f ≫ ·)
                (restriction_condition G g).symm
            _ = h ≫ tgt ≫ g := by
              simpa only [Category.assoc] using congrArg (· ≫ g) w
            _ = (h ≫ arr) ≫ G.target := by
              simpa only [Category.assoc] using congrArg (h ≫ ·)
                (restriction_condition' G g).symm) := by
    rw [Category.assoc, comp_arr]
    change (pullback.lift f h w ≫
        (pullback.lift (pullback.fst src tgt ≫ arr)
          (pullback.snd src tgt ≫ arr) _)) ≫ G.comp =
      (pullback.lift (f ≫ arr) (h ≫ arr) _) ≫ G.comp
    apply congrArg (· ≫ G.comp)
    apply pullback.hom_ext <;> simp
  let H : Stacks.Groupoids.GroupoidScheme S :=
    { objects := U'
      arrows := P
      source := src
      target := tgt
      comp := comp
      identity := ident
      inverse := inv
      source_identity := ident_source
      target_identity := ident_target
      source_inverse := inv_source
      target_inverse := inv_target
      source_comp := comp_source
      target_comp := comp_target
      left_identity := by
        intro T f w
        apply restriction_hom_ext G g
        · change _ ≫ src = _ ≫ src
          simp [comp_source]
        · change _ ≫ tgt = _ ≫ tgt
          simp [comp_target, ident_target]
        · change _ ≫ arr = _ ≫ arr
          have hid : (f ≫ tgt ≫ ident) ≫ arr = (f ≫ arr) ≫ G.target ≫ G.identity := by
            simpa only [Category.assoc, ident_arr] using
              congrArg (fun z ↦ f ≫ z ≫ G.identity) (restriction_condition' G g).symm
          have wG : ((f ≫ arr) ≫ G.target ≫ G.identity) ≫ G.source =
              f ≫ arr ≫ G.target := by
            simp [G.source_identity]
          calc
            (pullback.lift (f ≫ tgt ≫ ident) f w ≫ comp) ≫ arr =
                G.compose ((f ≫ tgt ≫ ident) ≫ arr) (f ≫ arr) _ :=
                  comp_arrow (f ≫ tgt ≫ ident) f w
            _ = f ≫ arr := by
              simpa only [Stacks.Groupoids.GroupoidScheme.compose, hid] using
                G.left_identity T (f ≫ arr) wG
      right_identity := by
        intro T f w
        apply restriction_hom_ext G g
        · change _ ≫ src = _ ≫ src
          simp [comp_source, ident_source]
        · change _ ≫ tgt = _ ≫ tgt
          simp [comp_target]
        · change _ ≫ arr = _ ≫ arr
          have hid : (f ≫ src ≫ ident) ≫ arr = (f ≫ arr) ≫ G.source ≫ G.identity := by
            simpa only [Category.assoc, ident_arr] using
              congrArg (fun z ↦ f ≫ z ≫ G.identity) (restriction_condition G g)
          have wG : f ≫ arr ≫ G.source =
              (f ≫ arr ≫ G.source ≫ G.identity) ≫ G.target := by
            simp [G.target_identity]
          calc
            (pullback.lift f (f ≫ src ≫ ident) w ≫ comp) ≫ arr =
                G.compose (f ≫ arr) ((f ≫ src ≫ ident) ≫ arr) _ :=
                  comp_arrow f (f ≫ src ≫ ident) w
            _ = f ≫ arr := by
              simpa only [Stacks.Groupoids.GroupoidScheme.compose, hid] using
                G.right_identity T (f ≫ arr) wG
      left_inverse := by
        intro T f w
        apply restriction_hom_ext G g
        · change _ ≫ src = _ ≫ src
          simp [comp_source, ident_source]
        · change _ ≫ tgt = _ ≫ tgt
          simp [comp_target, inv_target, ident_target]
        · change _ ≫ arr = _ ≫ arr
          have hid : (f ≫ src ≫ ident) ≫ arr = (f ≫ arr) ≫ G.source ≫ G.identity := by
            simpa only [Category.assoc, ident_arr] using
              congrArg (fun z ↦ f ≫ z ≫ G.identity) (restriction_condition G g)
          have wG : ((f ≫ arr) ≫ G.inverse) ≫ G.source = (f ≫ arr) ≫ G.target := by
            simp only [Category.assoc, G.source_inverse]
          have hinv : (f ≫ inv) ≫ arr = (f ≫ arr) ≫ G.inverse := by
            simp [inv_arr]
          have wInv : ((f ≫ inv) ≫ arr) ≫ G.source = (f ≫ arr) ≫ G.target := by rwa [hinv]
          have hcomp : G.compose ((f ≫ inv) ≫ arr) (f ≫ arr) wInv =
              G.compose ((f ≫ arr) ≫ G.inverse) (f ≫ arr) wG := by
            unfold Stacks.Groupoids.GroupoidScheme.compose
            apply congrArg (· ≫ G.comp)
            apply pullback.hom_ext
            · simpa only [pullback.lift_fst] using hinv
            · simp only [pullback.lift_snd]
          calc
            (pullback.lift (f ≫ inv) f w ≫ comp) ≫ arr =
                G.compose ((f ≫ inv) ≫ arr) (f ≫ arr) wInv :=
                  comp_arrow (f ≫ inv) f w
            _ = G.compose ((f ≫ arr) ≫ G.inverse) (f ≫ arr) wG := hcomp
            _ = f ≫ arr ≫ G.source ≫ G.identity := by
              simpa [Stacks.Groupoids.GroupoidScheme.compose] using
                G.left_inverse T (f ≫ arr) wG
            _ = (f ≫ src ≫ ident) ≫ arr := hid.symm
      right_inverse := by
        intro T f w
        apply restriction_hom_ext G g
        · change _ ≫ src = _ ≫ src
          simp [comp_source, inv_source, ident_source]
        · change _ ≫ tgt = _ ≫ tgt
          simp [comp_target, ident_target]
        · change _ ≫ arr = _ ≫ arr
          have hid : (f ≫ tgt ≫ ident) ≫ arr = (f ≫ arr) ≫ G.target ≫ G.identity := by
            simpa only [Category.assoc, ident_arr] using
              congrArg (fun z ↦ f ≫ z ≫ G.identity) (restriction_condition' G g).symm
          have wG : (f ≫ arr) ≫ G.source = ((f ≫ arr) ≫ G.inverse) ≫ G.target := by
            simp only [Category.assoc, G.target_inverse]
          have hinv : (f ≫ inv) ≫ arr = (f ≫ arr) ≫ G.inverse := by
            simp [inv_arr]
          have wInv : (f ≫ arr) ≫ G.source = ((f ≫ inv) ≫ arr) ≫ G.target := by rwa [hinv]
          have hcomp : G.compose (f ≫ arr) ((f ≫ inv) ≫ arr) wInv =
              G.compose (f ≫ arr) ((f ≫ arr) ≫ G.inverse) wG := by
            unfold Stacks.Groupoids.GroupoidScheme.compose
            apply congrArg (· ≫ G.comp)
            apply pullback.hom_ext
            · simp only [pullback.lift_fst]
            · simpa only [pullback.lift_snd] using hinv
          calc
            (pullback.lift f (f ≫ inv) w ≫ comp) ≫ arr =
                G.compose (f ≫ arr) ((f ≫ inv) ≫ arr) wInv :=
                  comp_arrow f (f ≫ inv) w
            _ = G.compose (f ≫ arr) ((f ≫ arr) ≫ G.inverse) wG := hcomp
            _ = f ≫ arr ≫ G.target ≫ G.identity := by
              simpa [Stacks.Groupoids.GroupoidScheme.compose] using
                G.right_inverse T (f ≫ arr) wG
            _ = (f ≫ tgt ≫ ident) ≫ arr := hid.symm
      assoc := by
        intro T f h k w₁ w₂ w₃ w₄
        apply restriction_hom_ext G g
        · change _ ≫ src = _ ≫ src
          simp [comp_source]
        · change _ ≫ tgt = _ ≫ tgt
          simp [comp_target]
        · change _ ≫ arr = _ ≫ arr
          have wfg : (f ≫ arr) ≫ G.source = (h ≫ arr) ≫ G.target := by
            calc
              (f ≫ arr) ≫ G.source = f ≫ src ≫ g := by
                simpa only [Category.assoc] using congrArg (f ≫ ·)
                  (restriction_condition G g).symm
              _ = h ≫ tgt ≫ g := by
                simpa only [Category.assoc] using congrArg (· ≫ g) w₁
              _ = (h ≫ arr) ≫ G.target := by
                simpa only [Category.assoc] using congrArg (h ≫ ·)
                  (restriction_condition' G g).symm
          have wgh : (h ≫ arr) ≫ G.source = (k ≫ arr) ≫ G.target := by
            calc
              (h ≫ arr) ≫ G.source = h ≫ src ≫ g := by
                simpa only [Category.assoc] using congrArg (h ≫ ·)
                  (restriction_condition G g).symm
              _ = k ≫ tgt ≫ g := by
                simpa only [Category.assoc] using congrArg (· ≫ g) w₂
              _ = (k ≫ arr) ≫ G.target := by
                simpa only [Category.assoc] using congrArg (k ≫ ·)
                  (restriction_condition' G g).symm
          have w₁G :
              (G.compose (f ≫ arr) (h ≫ arr) wfg) ≫ G.source =
                (k ≫ arr) ≫ G.target := by
            simpa [Stacks.Groupoids.GroupoidScheme.compose, G.source_comp] using wgh
          have w₂G : (f ≫ arr) ≫ G.source =
              (G.compose (h ≫ arr) (k ≫ arr) wgh) ≫ G.target := by
            simpa [Stacks.Groupoids.GroupoidScheme.compose, G.target_comp] using wfg
          simpa only [comp_arrow, Stacks.Groupoids.GroupoidScheme.compose] using
            G.assoc T (f ≫ arr) (h ≫ arr) (k ≫ arr) wfg wgh w₁G w₂G }
  let F : Stacks.Groupoids.GroupoidScheme.Hom H G :=
    { mapObjects := g
      mapArrows := arr
      map_source := by simp [H, src, arr]
      map_target := by simp [H, tgt, arr]
      map_identity := by simpa [H] using ident_arr.symm
      map_comp := by
        intro T f h w w'
        simpa [H, Stacks.Groupoids.GroupoidScheme.compose] using comp_arrow f h w }
  refine Restriction.mk H rfl rfl rfl rfl F rfl rfl fun T ↦ ?_
  let _ : Groupoid (H.Evaluation T) := H.evaluationGroupoid T
  let _ : Groupoid (G.Evaluation T) := G.evaluationGroupoid T
  let _ : Functor.Full (F.evaluation T) := ⟨by
    intro x y f
    have hsrc : f.arrow ≫ G.source = x ≫ g := f.source_eq
    have htgt : f.arrow ≫ G.target = y ≫ g := f.target_eq
    let q := pullback.lift y f.arrow htgt.symm
    let r := pullback.lift f.arrow x hsrc
    let p := pullback.lift q r (by
      calc
        q ≫ pullback.snd g G.target = f.arrow := by simp [q]
        _ = r ≫ pullback.fst G.source g := by simp [r])
    let h : H.EvaluationHom x y :=
      { arrow := p
        source_eq := by
          change p ≫ src = x
          dsimp [src, restrictionSource, restrictionArrows]
          simp [p, r]
        target_eq := by
          change p ≫ tgt = y
          dsimp [tgt, restrictionTarget, restrictionArrows]
          simp [p, q] }
    refine ⟨h, ?_⟩
    apply Stacks.Groupoids.GroupoidScheme.EvaluationHom.ext
    change p ≫ arr = f.arrow
    simp [p, q, arr, restrictionArrowsToArrows, restrictionArrows]⟩
  let _ : Functor.Faithful (F.evaluation T) := ⟨by
    intro x y f h hEq
    apply Stacks.Groupoids.GroupoidScheme.EvaluationHom.ext
    apply restriction_hom_ext G g
    · exact f.source_eq.trans h.source_eq.symm
    · exact f.target_eq.trans h.target_eq.symm
    · exact congrArg Stacks.Groupoids.GroupoidScheme.EvaluationHom.arrow hEq⟩
  exact ⟨Functor.FullyFaithful.ofFullyFaithful (F.evaluation T)⟩)

end AlgebraicGeometry.GroupoidScheme

end
