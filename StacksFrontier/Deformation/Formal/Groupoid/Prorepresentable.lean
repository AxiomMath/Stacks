module

public import Mathlib.CategoryTheory.Limits.Preserves.Basic
public import Mathlib.CategoryTheory.Limits.Yoneda
public import Mathlib.CategoryTheory.Yoneda
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Completed.Pushout
public import StacksFrontier.Deformation.Formal.Groupoid.CompletionRestrict
public import StacksFrontier.Deformation.Formal.Groupoid.RestrictCompletion
public import StacksFrontier.Deformation.Predeformation.Basic

/-!
# Prorepresentability criteria for groupoids in functors

A groupoid in functors on Artinian local `Λ`-algebras is prorepresentable exactly when its
completion is a representable groupoid in functors on complete local `Λ`-algebras.
Equivalently, both its functor of objects and its functor of arrows are prorepresentable.

## Main results

* `Deformation.GroupoidInFunctors.isProrepresentable_iff_isRepresentable_completion`:
  prorepresentability is representability of the completion.
* `Deformation.GroupoidInFunctors.isProrepresentable_iff_objects_arrows`:
  prorepresentability is prorepresentability of the object and arrow functors.
* `Deformation.GroupoidInFunctors.exists_representablePresentation_completion_of_isos`: the
  completion is presented by the algebras prorepresenting the object and arrow functors.
* `Deformation.GroupoidInFunctors.isProrepresentable_iff_objectsULift_arrowsULift`:
  the same criterion with the two functors' prorepresentability in universe-raised form.

## Implementation notes

The completion criterion keeps the value universe of the groupoid functors independent of
the hom-set universe of the algebras. The object-and-arrow criterion is stated in the
hom-set universe, where prorepresentability of a single functor is defined.

Both directions are assembled from a presentation by corepresentable functors: given
isomorphisms of the object and arrow functors with corepresentable ones, the source and
target maps are induced by morphisms of representing algebras, and the groupoid law
transports along the isomorphisms.

## References

* [Stacks Project, Tag 06KG](https://stacks.math.columbia.edu/tag/06KG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Deformation.GroupoidInFunctors

universe u v w z

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Transport of a groupoid structure along a bijection of its objects. -/
@[instance_reducible]
private noncomputable def transferGroupoid (α : Type u)
    [CategoryTheory.Groupoid.{v} α]
    {β : Type u} (e : α ≃ β) : CategoryTheory.Groupoid.{v} β where
  Hom x y := (e.symm x ⟶ e.symm y)
  id x := 𝟙 (e.symm x)
  comp f g := f ≫ g
  id_comp := by intros; simp
  comp_id := by intros; simp
  assoc := by intros; simp
  inv f := inv f
  inv_comp := by intros; simp
  comp_inv := by intros; simp
/-- Transport of a pointwise groupoid structure along bijections of objects and of
arrows that respect source, target and composition. -/
private noncomputable def transferPointwise {α ρ β σ : Type u}
    (s t : ρ → α) (c : {p : ρ × ρ // s p.1 = t p.2} → ρ)
    (s' t' : σ → β) (c' : {p : σ × σ // s' p.1 = t' p.2} → σ)
    (eA : α ≃ β) (eR : ρ ≃ σ)
    (hs : ∀ a, s' (eR a) = eA (s a))
    (ht : ∀ a, t' (eR a) = eA (t a))
    (hc : ∀ a b (hab : s a = t b),
      c' ⟨(eR a, eR b), by rw [hs, ht, hab]⟩ = eR (c ⟨(a, b), hab⟩))
    (p : PointwiseGroupoid s t c) : PointwiseGroupoid s' t' c' where
  groupoid := by letI := p.groupoid; exact transferGroupoid α eA
  arrowEquiv x y := by
    letI := p.groupoid
    letI := transferGroupoid α eA
    let eSub : {a : ρ // s a = eA.symm x ∧ t a = eA.symm y} ≃
        {b : σ // s' b = x ∧ t' b = y} :=
      eR.subtypeEquiv fun a => by
        constructor
        · rintro ⟨ha, hb⟩
          constructor
          · calc
              s' (eR a) = eA (s a) := hs a
              _ = eA (eA.symm x) := congrArg eA ha
              _ = x := eA.apply_symm_apply x
          · calc
              t' (eR a) = eA (t a) := ht a
              _ = eA (eA.symm y) := congrArg eA hb
              _ = y := eA.apply_symm_apply y
        · rintro ⟨ha, hb⟩
          constructor
          · apply eA.injective
            rw [eA.apply_symm_apply]
            calc
              eA (s a) = s' (eR a) := (hs a).symm
              _ = x := ha
          · apply eA.injective
            rw [eA.apply_symm_apply]
            calc
              eA (t a) = t' (eR a) := (ht a).symm
              _ = y := hb
    exact (p.arrowEquiv (eA.symm x) (eA.symm y)).trans eSub
  comp_eq := by
    let := p.groupoid
    intro x y z g f
    let qf := p.arrowEquiv (eA.symm y) (eA.symm z) f
    let qg := p.arrowEquiv (eA.symm x) (eA.symm y) g
    have hab : s qf.1 = t qg.1 := qf.2.1.trans qg.2.2.symm
    have hqf : qf = p.arrowEquiv (eA.symm y) (eA.symm z) f := rfl
    have hqg : qg = p.arrowEquiv (eA.symm x) (eA.symm y) g := rfl
    change eR (p.arrowEquiv (eA.symm x) (eA.symm z) (g ≫ f)).1 = _
    rw [p.comp_eq]
    simpa [hqf, hqg, Equiv.subtypeEquiv, Equiv.trans_apply] using (hc qf.1 qg.1 hab).symm

/-- A groupoid in functors whose object and arrow functors are corepresented by `A` and `B` is
isomorphic to the groupoid in functors of a representable presentation whose objects and arrows are
`A` and `B` themselves. -/
public theorem exists_representablePresentation_of_componentIsos
    {C : Type u} [Category.{v} C] [HasPushouts C]
    {G : GroupoidInFunctors.{u, v, max v w} C} (A B : C)
    (iU : G.objects ≅ uliftCoyoneda.{w}.obj (op A))
    (iR : G.arrows ≅ uliftCoyoneda.{w}.obj (op B)) :
    ∃ P : RepresentablePresentation.{u, v, w} C,
      P.objects = A ∧ P.arrows = B ∧ Nonempty (G ≅ P.groupoidInFunctors) := by
  classical
  let YA := uliftCoyoneda.{w}.obj (op A)
  let YB := uliftCoyoneda.{w}.obj (op B)
  let sN := iR.inv ≫ G.source ≫ iU.hom
  let tN := iR.inv ≫ G.target ≫ iU.hom
  let s := (uliftCoyonedaEquiv (X := op B) (F := YA) sN).down
  let t := (uliftCoyonedaEquiv (X := op B) (F := YA) tN).down
  let sP := uliftCoyoneda.map s.op
  let tP := uliftCoyoneda.{w}.map t.op
  have hlift (n : YB ⟶ YA) :
      n = uliftCoyoneda.map (uliftCoyonedaEquiv (X := op B) (F := YA) n).down.op := by
    apply (uliftCoyonedaEquiv (X := op B) (F := YA)).injective
    rw [uliftCoyonedaEquiv_uliftCoyoneda_map]
    apply ULift.ext
    rfl
  have hcomp (n : YB ⟶ YA) (N : G.arrows ⟶ G.objects) (h : n = iR.inv ≫ N ≫ iU.hom)
      (T : C) (a : G.arrows.obj T) : n.app T (iR.hom.app T a) = iU.hom.app T (N.app T a) := by
    have h := congrFun (congrArg (fun η => η.app T) h) (iR.hom.app T a)
    simpa [NatTrans.comp_app] using h
  have hs (T : C) (a : G.arrows.obj T) :
      sP.app T (iR.hom.app T a) = iU.hom.app T (G.source.app T a) :=
    hcomp sP G.source (hlift sN).symm T a
  have ht (T : C) (a : G.arrows.obj T) :
      tP.app T (iR.hom.app T a) = iU.hom.app T (G.target.app T a) :=
    hcomp tP G.target (hlift tN).symm T a
  have hinv (Gm : G.arrows ⟶ G.objects) (Hm : YB ⟶ YA)
      (hm : ∀ (T : C) (a : G.arrows.obj T),
        Hm.app T (iR.hom.app T a) = iU.hom.app T (Gm.app T a))
      (T : C) (a : YB.obj T) : Gm.app T (iR.inv.app T a) = iU.inv.app T (Hm.app T a) := by
    simpa using congrArg (iU.inv.app T) (hm T (iR.inv.app T a)).symm
  let Dp := composableArrows YA YB sP tP
  let Dg := composableArrows G.objects G.arrows G.source G.target
  let dIso : Dp ≅ Dg := NatIso.ofComponents (fun T => Equiv.toIso {
    toFun := fun p => ⟨(iR.inv.app T p.1.1, iR.inv.app T p.1.2), by
      rw [hinv _ _ hs, hinv _ _ ht, p.2]⟩
    invFun := fun p => ⟨(iR.hom.app T p.1.1, iR.hom.app T p.1.2), by
      calc
        sP.app T (iR.hom.app T p.1.1) = iU.hom.app T (G.source.app T p.1.1) := by
          simpa using hs T p.1.1
        _ = iU.hom.app T (G.target.app T p.1.2) := congrArg (iU.hom.app T) p.2
        _ = tP.app T (iR.hom.app T p.1.2) := by simpa using (ht T p.1.2).symm⟩
    left_inv := by intro p; apply Subtype.ext; apply Prod.ext <;> simp
    right_inv := by intro p; apply Subtype.ext; apply Prod.ext <;> simp
  }) (by
    intro X Y f
    ext p
    apply Subtype.ext
    apply Prod.ext
    · simpa [Dg, Dp, composableArrows, YB, uliftCoyoneda] using (iR.inv.naturality_apply f p.1.1)
    · simpa [Dg, Dp, composableArrows, YB, uliftCoyoneda] using (iR.inv.naturality_apply f p.1.2))
  let cP := dIso.hom ≫ G.comp ≫ iR.hom
  have hcP (T : C) (a b : G.arrows.obj T) (hab : G.source.app T a = G.target.app T b)
      (h : sP.app T (iR.hom.app T a) = tP.app T (iR.hom.app T b)) :
      cP.app T ⟨(iR.hom.app T a, iR.hom.app T b), h⟩ = iR.hom.app T (G.compose T a b hab) := by
    have hdom : dIso.hom.app T ⟨(iR.hom.app T a, iR.hom.app T b), h⟩ = ⟨(a, b), hab⟩ := by
      apply Subtype.ext
      apply Prod.ext <;> simp [dIso]
    change iR.hom.app T (G.comp.app T (dIso.hom.app T _)) = _
    rw [hdom]
    rfl
  let P : RepresentablePresentation.{u, v, w} C := {
    objects := A
    arrows := B
    source := s
    target := t
    comp := cP
    pointwiseGroupoid := fun T => by
      let eA : G.objects.obj T ≃ YA.obj T := (iU.app T).toEquiv
      let eR : G.arrows.obj T ≃ YB.obj T := (iR.app T).toEquiv
      let hsource : ∀ a, sP.app T (eR a) = eA (G.source.app T a) := hs T
      let htarget : ∀ a, tP.app T (eR a) = eA (G.target.app T a) := ht T
      exact ⟨transferPointwise (G.source.app T) (G.target.app T)
        (fun p => G.comp.app T p) (sP.app T) (tP.app T)
        (fun p => cP.app T p) eA eR hsource htarget (fun a b hab => hcP T a b hab _)
        (G.pointwiseData T)⟩
    hasPushout := inferInstance
  }
  let H := P.groupoidInFunctors
  let F : GroupoidInFunctors.Hom G H := {
    mapObjects := iU.hom
    mapArrows := iR.hom
    map_source := by intro T a; exact hs T a
    map_target := by intro T a; exact ht T a
    map_id := by
      intro T x
      let pG := G.pointwiseData T
      let := pG.groupoid
      let pH := H.pointwiseData T
      let : Groupoid (YA.obj T) := pH.groupoid
      let y := iU.hom.app T x
      let r := G.identity T x
      let z := iR.hom.app T r
      have hrs : G.source.app T r = x := by
        have h := (G.evaluationArrowEquiv T x x (𝟙 x)).2.1
        simpa [r, GroupoidInFunctors.evaluationArrowEquiv_id] using h
      have hrt : G.target.app T r = x := by
        have h := (G.evaluationArrowEquiv T x x (𝟙 x)).2.2
        simpa [r, GroupoidInFunctors.evaluationArrowEquiv_id] using h
      have hys : H.source.app T z = y := by
        show sP.app T z = y
        calc
          sP.app T z = iU.hom.app T (G.source.app T r) := hs T r
          _ = y := by rw [hrs]
      have hyt : H.target.app T z = y := by
        show tP.app T z = y
        calc
          tP.app T z = iU.hom.app T (G.target.app T r) := ht T r
          _ = y := by rw [hrt]
      have hrr : G.source.app T r = G.target.app T r := hrs.trans hrt.symm
      have hid : G.compose T r r hrr = r := by
        have h := G.evaluationArrowEquiv_comp T (𝟙 x) (𝟙 x)
        have h' : r = G.compose T r r hrr := by
          simpa [r, GroupoidInFunctors.evaluationArrowEquiv_id,
            GroupoidInFunctors.compose] using h
        exact h'.symm
      have hlooprel : H.source.app T z = H.target.app T z := hys.trans hyt.symm
      have hloop : H.compose T z z hlooprel = z := by
        change cP.app T ⟨(z, z), hlooprel⟩ = z
        rw [hcP T r r hrr hlooprel, hid]
      let α := (H.evaluationArrowEquiv T y y).symm ⟨z, hys, hyt⟩
      have hα : α ≫ α = α := by
        apply (H.evaluationArrowEquiv T y y).injective
        apply Subtype.ext
        simpa [α, GroupoidInFunctors.evaluationArrowEquiv_comp,
          GroupoidInFunctors.compose] using hloop
      have hαid : α = 𝟙 y := by simpa using congrArg (· ≫ inv α) hα
      calc
        iR.hom.app T (G.identity T x) = z := rfl
        _ = (H.evaluationArrowEquiv T y y α).1 := by simp [α]
        _ = (H.evaluationArrowEquiv T y y (𝟙 y)).1 :=
          congrArg (fun q => (H.evaluationArrowEquiv T y y q).1) hαid
        _ = H.identity T y := rfl
    map_comp := by
      intro T a b hab
      exact hcP T a b hab ((hs T a).trans
        ((congrArg (iU.hom.app T) hab).trans (ht T b).symm))
  }
  let J : GroupoidInFunctors.Hom H G := {
    mapObjects := iU.inv
    mapArrows := iR.inv
    map_source := fun T a => hinv _ _ hs T a
    map_target := fun T a => hinv _ _ ht T a
    map_id := by
      intro T x
      have h := F.map_id T (iU.inv.app T x)
      have h' := congrArg (iR.inv.app T) h
      simpa [F, Iso.inv_hom_id_app, Iso.hom_inv_id_app] using h'.symm
    map_comp := by
      intro T a b hab
      have ha := F.map_source T (iR.inv.app T a)
      have hb := F.map_target T (iR.inv.app T b)
      have hinvU : Function.LeftInverse (iU.inv.app T) (iU.hom.app T) := by
        intro x
        simp
      have hrel : G.source.app T (iR.inv.app T a) = G.target.app T (iR.inv.app T b) := by
        apply (Function.LeftInverse.injective hinvU)
        calc
          iU.hom.app T (G.source.app T (iR.inv.app T a)) = H.source.app T a := by
            simpa [F, Iso.inv_hom_id_app, Iso.hom_inv_id_app] using ha.symm
          _ = H.target.app T b := hab
          _ = iU.hom.app T (G.target.app T (iR.inv.app T b)) := by
            simpa [F, Iso.inv_hom_id_app, Iso.hom_inv_id_app] using hb
      have hm := F.map_comp T (iR.inv.app T a) (iR.inv.app T b) hrel
      have hinj : Function.LeftInverse (iR.inv.app T) (iR.hom.app T) := by
        intro x
        simp
      apply hinj.injective
      simpa [F, Iso.inv_hom_id_app, Iso.hom_inv_id_app,
        GroupoidInFunctors.compose] using hm.symm
  }
  let e : G ≅ H := {
    hom := F
    inv := J
    hom_inv_id := by
      apply GroupoidInFunctors.Hom.ext
      · ext T x
        show iU.inv.app T (iU.hom.app T x) = x
        simp
      · ext T x
        show iR.inv.app T (iR.hom.app T x) = x
        simp
    inv_hom_id := by
      apply GroupoidInFunctors.Hom.ext
      · ext T x
        show iU.hom.app T (iU.inv.app T x) = x
        simp
      · ext T x
        show iR.hom.app T (iR.inv.app T x) = x
        simp
  }
  exact ⟨P, rfl, rfl, ⟨e⟩⟩

/-- A groupoid in functors whose object and arrow functors are corepresentable is
representable. -/
private theorem groupoidPresentationOfComponentIsos
    {C : Type u} [Category.{v} C] [HasPushouts C]
    {G : GroupoidInFunctors.{u, v, max v w} C} (A B : C)
    (iU : G.objects ≅ uliftCoyoneda.{w}.obj (op A))
    (iR : G.arrows ≅ uliftCoyoneda.{w}.obj (op B)) :
    IsRepresentable G := by
  obtain ⟨P, -, -, e⟩ := exists_representablePresentation_of_componentIsos A B iU iR
  exact ⟨P, e⟩

/-- The discrete groupoid on a type, whose only arrows are the equalities. -/
@[instance_reducible] private def discreteGroupoid (α : Type u) : Groupoid.{u} α where
  Hom x y := ULift.{u, 0} (PLift.{0} (x = y))
  id x := ULift.up (PLift.up rfl)
  comp f g := ULift.up (PLift.up (f.down.down.trans g.down.down))
  id_comp := by intros; apply Subsingleton.elim
  comp_id := by intros; apply Subsingleton.elim
  assoc := by intros; apply Subsingleton.elim
  inv f := ULift.up (PLift.up f.down.down.symm)
  inv_comp := by intros; apply Subsingleton.elim
  comp_inv := by intros; apply Subsingleton.elim

/-- The presentation whose object and arrow functors are both corepresented by one
object, with identity source and target. -/
private noncomputable def identityPresentation
    {C : Type u} [Category.{v} C] [HasPushouts C] (R : C) :
    RepresentablePresentation.{u, v, v} C := by
  classical
  let Y := uliftCoyoneda.{v}.obj (op R)
  let s := uliftCoyoneda.map (𝟙 R).op
  let compMap : composableArrows Y Y
      s s ⟶ Y := {
    app T := ↾ fun p : {q : Y.obj T × Y.obj T // s.app T q.1 = s.app T q.2} => p.1.2
    naturality := by intro X Z f; rfl
  }
  refine {
    objects := R
    arrows := R
    source := 𝟙 R
    target := 𝟙 R
    comp := compMap
    pointwiseGroupoid := ?_
    hasPushout := inferInstance
  }
  intro T
  let : Groupoid.{v} (Y.obj T) := discreteGroupoid (Y.obj T)
  refine ⟨{
    groupoid := discreteGroupoid (Y.obj T)
    arrowEquiv := ?_
    comp_eq := ?_
  }⟩
  · intro x y
    haveI : Subsingleton (ULift.{v, 0} (PLift.{0} (x = y))) := by infer_instance
    refine {
      toFun := fun f => ⟨x, by simp, by cases f.down.down; simp⟩
      invFun := fun a => by
        have hx : a.1 = x := by simpa using a.2.1
        have hy : a.1 = y := by simpa using a.2.2
        exact ULift.up (PLift.up (hx.symm.trans hy))
      left_inv := by intro f; exact Subsingleton.elim _ _
      right_inv := by intro a; apply Subtype.ext; exact (by simpa using a.2.1.symm)
    }
  · intro x y z g f
    simp [compMap, composableArrows]


/-- The isomorphism of object functors induced by an isomorphism of groupoids in
functors. -/
private def objectsIso {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (i : G ≅ H) :
    G.objects ≅ H.objects where
  hom := i.hom.mapObjects
  inv := i.inv.mapObjects
  hom_inv_id := congrArg GroupoidInFunctors.Hom.mapObjects i.hom_inv_id
  inv_hom_id := congrArg GroupoidInFunctors.Hom.mapObjects i.inv_hom_id

/-- The isomorphism of arrow functors induced by an isomorphism of groupoids in
functors. -/
private def arrowsIso {C : Type u} [Category.{v} C]
    {G H : GroupoidInFunctors.{u, v, w} C} (i : G ≅ H) :
    G.arrows ≅ H.arrows where
  hom := i.hom.mapArrows
  inv := i.inv.mapArrows
  hom_inv_id := congrArg GroupoidInFunctors.Hom.mapArrows i.hom_inv_id
  inv_hom_id := congrArg GroupoidInFunctors.Hom.mapArrows i.inv_hom_id

/-- Whiskering a natural isomorphism of set-valued functors by a functor on the
source. -/
private def whiskerNatIso {C : Type u} {D : Type v} [Category.{w} C]
    [Category.{z} D] (F : C ⥤ D) {G H : D ⥤ Type z} (i : G ≅ H) :
    F ⋙ G ≅ F ⋙ H :=
  NatIso.ofComponents (fun X => i.app (F.obj X))

/-- The comparison between the universe-lifted and the plain covariant representable
functor of an object. -/
private def uliftCoyonedaIso {C : Type u} [Category.{v} C] (X : C) :
    uliftCoyoneda.{v}.obj (Opposite.op X) ≅ coyoneda.obj (Opposite.op X) :=
  (CategoryTheory.uliftCoyonedaIsoCoyoneda.{v}).app (Opposite.op X)

/-- The completion of a restricted covariant representable functor is the lifted
covariant representable functor it restricts. -/
private noncomputable def completedRestrictedCoyonedaIso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    (cofiberedCompletion.{u, v, w, v} (Λ := Λ) (k := k)).obj
      (restrictedCoyoneda R) ≅ uliftCoyoneda.{v}.obj (op R) := by
  let P := identityPresentation R
  let H := P.groupoidInFunctors
  haveI : PreservesLimits H.objects := by
    change PreservesLimits (uliftCoyoneda.{v}.obj (op R))
    infer_instance
  haveI : PreservesLimits H.arrows := by
    change PreservesLimits (uliftCoyoneda.{v}.obj (op R))
    infer_instance
  let e := (GroupoidInFunctors.completionRestrictionIso H).1
  let iRestr := whiskerNatIso artinianToComplete
    ((CategoryTheory.uliftCoyonedaIsoCoyoneda.{v}).app (op R))
  exact (cofiberedCompletion.{u, v, w, v} (Λ := Λ) (k := k)).mapIso iRestr.symm |>.trans
    (objectsIso e)

/-- The completion of a functor prorepresented by `R` is the lifted covariant representable
functor of `R`. -/
private noncomputable def completionIsoUliftCoyoneda
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    {F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v}
    {R : CompleteLocalAlgCat.{u, v, w} Λ k} (i : F ≅ restrictedCoyoneda R) :
    (cofiberedCompletion.{u, v, w, v} (Λ := Λ) (k := k)).obj F ≅
      uliftCoyoneda.{v}.obj (op R) :=
  (cofiberedCompletion.{u, v, w, v} (Λ := Λ) (k := k)).mapIso i |>.trans
    (completedRestrictedCoyonedaIso R)

/-- A groupoid in functors on Artinian local algebras is prorepresentable if
and only if its completion is representable on complete local algebras. -/
@[stacks 06KG "part (1)"]
public theorem isProrepresentable_iff_isRepresentable_completion
    (G : GroupoidInFunctors.{_, v, max v z}
      (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    GroupoidInFunctors.IsProrepresentable G ↔
      IsRepresentable (GroupoidInFunctors.completion G) := by
  constructor
  · rintro ⟨H, hH, ⟨e⟩⟩
    have hH' : IsRepresentable.{_, v, z} H := hH
    rcases hH' with ⟨P, ⟨f⟩⟩
    have : PreservesLimits (uliftCoyoneda.{z}.obj (Opposite.op P.objects)) :=
      by infer_instance
    have : PreservesLimits (uliftCoyoneda.{z}.obj (Opposite.op P.arrows)) :=
      by infer_instance
    let : PreservesLimits P.groupoidInFunctors.objects := by
      show PreservesLimits (uliftCoyoneda.{z}.obj (Opposite.op P.objects))
      infer_instance
    let : PreservesLimits P.groupoidInFunctors.arrows := by
      show PreservesLimits (uliftCoyoneda.{z}.obj (Opposite.op P.arrows))
      infer_instance
    let : PreservesLimits H.objects :=
      preservesLimits_of_natIso (objectsIso f).symm
    let : PreservesLimits H.arrows :=
      preservesLimits_of_natIso (arrowsIso f).symm
    let eH := (GroupoidInFunctors.completionRestrictionIso H).1
    let iU := (cofiberedCompletion (Λ := Λ) (k := k)).mapIso (objectsIso e)
    let iR := (cofiberedCompletion (Λ := Λ) (k := k)).mapIso (arrowsIso e)
    have iU' : (GroupoidInFunctors.completion G).objects ≅ H.objects :=
      iU.trans (objectsIso eH)
    have iR' : (GroupoidInFunctors.completion G).arrows ≅ H.arrows :=
      iR.trans (arrowsIso eH)
    exact groupoidPresentationOfComponentIsos P.objects P.arrows
      (iU'.trans (objectsIso f)) (iR'.trans (arrowsIso f))
  · intro h
    exact ⟨GroupoidInFunctors.completion G, h,
      ⟨(GroupoidInFunctors.completionRestrictIso G).1.symm⟩⟩

/-- A groupoid in functors is prorepresentable if and only if both its object
and arrow functors are prorepresentable. -/
@[stacks 06KG "part (2)"]
public theorem isProrepresentable_iff_objects_arrows
    (G : GroupoidInFunctors.{_, v, v}
      (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    GroupoidInFunctors.IsProrepresentable G ↔
      (_root_.Deformation.IsProrepresentable G.objects ∧
        _root_.Deformation.IsProrepresentable G.arrows) := by
  constructor
  · rintro ⟨H, hH, ⟨e⟩⟩
    rcases hH with ⟨P, ⟨f⟩⟩
    have key {X : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type v}
        {Y : CompleteLocalAlgCat.{u, v, w} Λ k ⥤ Type v}
        {R : CompleteLocalAlgCat.{u, v, w} Λ k} (i : X ≅ artinianToComplete ⋙ Y)
        (j : Y ≅ uliftCoyoneda.{v}.obj (op R)) : _root_.Deformation.IsProrepresentable X :=
      ⟨R, ⟨i.trans ((whiskerNatIso artinianToComplete j).trans
        (whiskerNatIso artinianToComplete (uliftCoyonedaIso R)))⟩⟩
    exact ⟨key (objectsIso e) (objectsIso f), key (arrowsIso e) (arrowsIso f)⟩
  · intro h
    rcases h.1 with ⟨R₀, ⟨iU⟩⟩
    rcases h.2 with ⟨R₁, ⟨iR⟩⟩
    exact (isProrepresentable_iff_isRepresentable_completion G).mpr
      (groupoidPresentationOfComponentIsos R₀ R₁ (completionIsoUliftCoyoneda iU)
        (completionIsoUliftCoyoneda iR))

/-- A groupoid in functors on Artinian local algebras whose object and arrow functors are
prorepresented by `A` and `B` has a completion isomorphic to the groupoid in functors of a
representable presentation whose objects and arrows are `A` and `B` themselves. This is the
converse direction of `isProrepresentable_iff_objects_arrows` with the representing algebras
kept. -/
public theorem exists_representablePresentation_completion_of_isos
    (G : GroupoidInFunctors.{_, v, v}
      (ArtinianLocalAlgCat.{u, v, w} Λ k))
    (A B : CompleteLocalAlgCat.{u, v, w} Λ k)
    (iU : G.objects ≅ restrictedCoyoneda A) (iR : G.arrows ≅ restrictedCoyoneda B) :
    ∃ P : RepresentablePresentation.{_, v, v} (CompleteLocalAlgCat.{u, v, w} Λ k),
      P.objects = A ∧ P.arrows = B ∧
        Nonempty (GroupoidInFunctors.completion G ≅ P.groupoidInFunctors) :=
  exists_representablePresentation_of_componentIsos A B
    (completionIsoUliftCoyoneda iU) (completionIsoUliftCoyoneda iR)

/-- The object-and-arrow criterion with the two functors' prorepresentability written in the
universe-raised form `Deformation.IsProrepresentableULift`, which is what a statement whose
value universe is independent of the hom-set universe has to use. At the hom-set value
universe, where the criterion lives, the two notions agree by
`Deformation.isProrepresentableULift_iff`, so this is the same statement; it is recorded
separately for consumers written over that form, and is deliberately untagged, the tagged
covering set of part (2) being `isProrepresentable_iff_objects_arrows` above. -/
public theorem isProrepresentable_iff_objectsULift_arrowsULift
    (G : GroupoidInFunctors.{_, v, v}
      (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    GroupoidInFunctors.IsProrepresentable G ↔
      (_root_.Deformation.IsProrepresentableULift G.objects ∧
        _root_.Deformation.IsProrepresentableULift G.arrows) := by
  rw [_root_.Deformation.isProrepresentableULift_iff,
    _root_.Deformation.isProrepresentableULift_iff]
  exact isProrepresentable_iff_objects_arrows G

end Deformation.GroupoidInFunctors
