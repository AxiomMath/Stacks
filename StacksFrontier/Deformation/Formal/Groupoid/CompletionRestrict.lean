module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Formal.Groupoid.Completion

/-!
# Restricting the completion of a groupoid in functors

The completion of a groupoid in functors on Artinian local `Λ`-algebras, restricted back
along the inclusion of Artinian local algebras into complete local algebras, is canonically
isomorphic to the original groupoid. On objects and on arrows this isomorphism is the counit
of the completion–restriction adjunction for set-valued functors.

## Main results

* `Deformation.GroupoidInFunctors.completionRestrictIso`: the canonical isomorphism from the
  restricted completion to the original groupoid, with its object and arrow components
  identified.

## Implementation notes

The isomorphism is packaged together with the equations identifying its two components,
so the statement pins down the canonical comparison rather than merely asserting that some
isomorphism exists.

## References

* [Stacks Project, Tag 06KF](https://stacks.math.columbia.edu/tag/06KF)
-/

@[expose] public section

open CategoryTheory

namespace Deformation.GroupoidInFunctors

universe u v w z

/-- The canonical isomorphism from a completed groupoid, restricted back to
Artinian local algebras, to the original groupoid. Its two components are the
completion--restriction counits. -/
@[stacks 06KF "completion_restrict"]
public noncomputable def completionRestrictIso
    {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors.{_, v, max v z}
      (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    { e : GroupoidInFunctors.restrict
          (GroupoidInFunctors.completion G)
          (artinianToComplete (Λ := Λ) (k := k)) ≅ G //
      e.hom.mapObjects =
        (cofiberedCompletionAdjunction
          (Λ := Λ) (k := k)).counit.app G.objects ∧
      e.hom.mapArrows =
        (cofiberedCompletionAdjunction
          (Λ := Λ) (k := k)).counit.app G.arrows } := by
    classical
    let incl := artinianToComplete (Λ := Λ) (k := k)
    let adj := cofiberedCompletionAdjunction (Λ := Λ) (k := k)
    let B := GroupoidInFunctors.restrict
      (GroupoidInFunctors.completion G) incl
    let ηU := adj.counit.app G.objects
    let ηR := adj.counit.app G.arrows
    have hU : IsIso ηU := cofiberedCompletion_restriction_isIso G.objects
    have hR : IsIso ηR := cofiberedCompletion_restriction_isIso G.arrows
    let iU := asIso ηU
    let iR := asIso ηR
    have hRinv (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (a : G.arrows.obj A) :
        ηR.app A (iR.inv.app A a) = a := by
      rw [← ConcreteCategory.comp_apply]
      simp [ηR, iR]
    have hUinv (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (x : B.objects.obj A) :
        iU.inv.app A (ηU.app A x) = x := by
      rw [← ConcreteCategory.comp_apply]
      simp [ηU, iU]
    have hRinv' (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (a : B.arrows.obj A) :
        iR.inv.app A (ηR.app A a) = a := by
      rw [← ConcreteCategory.comp_apply]
      simp [ηR, iR]
    have hUinv' (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (x : G.objects.obj A) :
        ηU.app A (iU.inv.app A x) = x := by
      rw [← ConcreteCategory.comp_apply]
      simp [ηU, iU]
    have hsrc (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (a : B.arrows.obj A) :
        G.source.app A (ηR.app A a) = ηU.app A (B.source.app A a) := by
      have h := adj.counit_naturality G.source
      have hA := congrFun (congrArg (fun α => α.app A) h) a
      simpa [adj, ηU, ηR, incl, B, GroupoidInFunctors.completion,
        GroupoidInFunctors.restrict] using hA.symm
    have htgt (A : ArtinianLocalAlgCat.{u, v, w} Λ k) (a : B.arrows.obj A) :
        G.target.app A (ηR.app A a) = ηU.app A (B.target.app A a) := by
      have h := adj.counit_naturality G.target
      have hA := congrFun (congrArg (fun α => α.app A) h) a
      simpa [adj, ηU, ηR, incl, B, GroupoidInFunctors.completion,
        GroupoidInFunctors.restrict] using hA.symm
    have hcomp (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (a b : B.arrows.obj A) (hab : B.source.app A a = B.target.app A b) :
        G.compose A (ηR.app A a) (ηR.app A b)
          ((hsrc A a).trans ((congrArg (ηU.app A) hab).trans (htgt A b).symm)) =
        ηR.app A (B.compose A a b hab) := by
      let C := GroupoidInFunctors.completion G
      let cd := GroupoidInFunctors.completionData G
      let qA := composableArrows G.objects G.arrows G.source G.target
      let qC := composableArrows C.objects C.arrows C.source C.target
      let firstA := composableFirst G.objects G.arrows G.source G.target
      let secondA := composableSecond G.objects G.arrows G.source G.target
      let firstC := composableFirst
        (cofiberedCompletion.obj G.objects) (cofiberedCompletion.obj G.arrows)
        (cofiberedCompletion.map G.source) (cofiberedCompletion.map G.target)
      let secondC := composableSecond
        (cofiberedCompletion.obj G.objects) (cofiberedCompletion.obj G.arrows)
        (cofiberedCompletion.map G.source) (cofiberedCompletion.map G.target)
      let ηQ := adj.counit.app qA
      let p : qC.obj (incl.obj A) := ⟨(a, b), hab⟩
      let x := cd.comparison.inv.app (incl.obj A) p
      have hfirst : firstC.app (incl.obj A) p =
          (cofiberedCompletion.map firstA).app (incl.obj A) x := by
        have h := congrFun (congrArg (fun θ => θ.app (incl.obj A)) cd.first_comm) x
        simpa [x, NatTrans.comp_app, Iso.hom_inv_id_app] using h
      have hsecond : secondC.app (incl.obj A) p =
          (cofiberedCompletion.map secondA).app (incl.obj A) x := by
        have h := congrFun (congrArg (fun θ => θ.app (incl.obj A)) cd.second_comm) x
        simpa [x, NatTrans.comp_app, Iso.hom_inv_id_app] using h
      have hηfirst : (ηQ.app A x).val.1 = ηR.app A a := by
        have h := adj.counit_naturality firstA
        have hA := congrFun (congrArg (fun θ => θ.app A) h) x
        have hcomp := congrArg (fun y => (ηR.app A) y) hfirst.symm
        simpa [ηQ, ηR, firstA, firstC, p, qA, composableFirst,
          NatTrans.comp_app] using hA.symm.trans hcomp
      have hηsecond : (ηQ.app A x).val.2 = ηR.app A b := by
        have h := adj.counit_naturality secondA
        have hA := congrFun (congrArg (fun θ => θ.app A) h) x
        have hcomp := congrArg (fun y => (ηR.app A) y) hsecond.symm
        simpa [ηQ, ηR, secondA, secondC, p, qA, composableSecond,
          NatTrans.comp_app] using hA.symm.trans hcomp
      have hq : ηQ.app A x =
          ⟨(ηR.app A a, ηR.app A b),
            (hsrc A a).trans ((congrArg (ηU.app A) hab).trans (htgt A b).symm)⟩ :=
        Subtype.ext (Prod.ext hηfirst hηsecond)
      have hBcomp : B.comp.app A ⟨(a, b), hab⟩ =
          (cofiberedCompletion.map G.comp).app (incl.obj A) x :=
        rfl
      have h := adj.counit_naturality G.comp
      have hA := congrFun (congrArg (fun θ => θ.app A) h) x
      change G.comp.app A _ = ηR.app A (B.comp.app A ⟨(a, b), hab⟩)
      rw [hBcomp]
      exact (congrArg (G.comp.app A) hq).symm.trans hA.symm
    let f : GroupoidInFunctors.Hom B G := {
      mapObjects := ηU
      mapArrows := ηR
      map_source := hsrc
      map_target := htgt
      map_id := by
        intro A x
        let := B.evaluationGroupoid A
        let := G.evaluationGroupoid A
        let r := B.identity A x
        let y : G.Evaluation A := ηU.app A x
        have hrs : B.source.app A r = x := by
          have h := (B.evaluationArrowEquiv A x x (𝟙 x)).2.1
          simpa [r, GroupoidInFunctors.evaluationArrowEquiv_id] using h
        have hrt : B.target.app A r = x := by
          have h := (B.evaluationArrowEquiv A x x (𝟙 x)).2.2
          simpa [r, GroupoidInFunctors.evaluationArrowEquiv_id] using h
        have hrr : B.source.app A r = B.target.app A r := hrs.trans hrt.symm
        have hys : G.source.app A (ηR.app A r) = y := by
          simpa [y] using (hsrc A r).trans (congrArg (ηU.app A) hrs)
        have hyt : G.target.app A (ηR.app A r) = y := by
          simpa [y] using (htgt A r).trans (congrArg (ηU.app A) hrt)
        let eG := G.evaluationArrowEquiv A y y
        let α := eG.symm ⟨ηR.app A r, ⟨hys, hyt⟩⟩
        have hbc : B.compose A r r hrr = r :=
          (by simpa [r, GroupoidInFunctors.evaluationArrowEquiv_id] using
            B.evaluationArrowEquiv_comp A (𝟙 x) (𝟙 x) : r = B.compose A r r hrr).symm
        have hm := hcomp A r r hrr
        rw [hbc] at hm
        have hα : α ≫ α = α := by
          apply eG.injective
          apply Subtype.ext
          simpa [eG, α, GroupoidInFunctors.evaluationArrowEquiv_comp, hbc,
            GroupoidInFunctors.compose] using hm
        have hαid : α = 𝟙 y := by
          apply (cancel_mono α).mp
          simpa [Category.id_comp] using hα
        calc
          ηR.app A (B.identity A x) = ηR.app A r := rfl
          _ = (G.evaluationArrowEquiv A y y α).1 := by simp [α, eG]
          _ = (G.evaluationArrowEquiv A y y (𝟙 y)).1 :=
            congrArg (fun q => (G.evaluationArrowEquiv A y y q).1) hαid
          _ = G.identity A y := by
            simp [GroupoidInFunctors.evaluationArrowEquiv_id]
      map_comp := hcomp
    }
    let g : GroupoidInFunctors.Hom G B := {
      mapObjects := iU.inv
      mapArrows := iR.inv
      map_source := by
        intro A a
        have h := f.map_source A (iR.inv.app A a)
        have h' := congrArg (iU.inv.app A) h
        rw [hRinv A a] at h'
        have hu := hUinv A (B.source.app A (iR.inv.app A a))
        rw [hu] at h'
        exact h'.symm
      map_target := by
        intro A a
        have h := f.map_target A (iR.inv.app A a)
        have h' := congrArg (iU.inv.app A) h
        rw [hRinv A a] at h'
        have hu := hUinv A (B.target.app A (iR.inv.app A a))
        rw [hu] at h'
        exact h'.symm
      map_id := by
        intro A x
        have h := f.map_id A (iU.inv.app A x)
        rw [hUinv' A x] at h
        have h' := congrArg (iR.inv.app A) h
        rw [hRinv' A (B.identity A (iU.inv.app A x))] at h'
        exact h'.symm
      map_comp := by
        intro A a b hab
        have ha := f.map_source A (iR.inv.app A a)
        have hb := f.map_target A (iR.inv.app A b)
        have hrel : B.source.app A (iR.inv.app A a) =
            B.target.app A (iR.inv.app A b) := by
          apply Function.LeftInverse.injective (hUinv A)
          calc
            _ = G.source.app A (ηR.app A (iR.inv.app A a)) := ha.symm
            _ = G.source.app A a := by rw [hRinv A a]
            _ = G.target.app A b := hab
            _ = G.target.app A (ηR.app A (iR.inv.app A b)) := by rw [hRinv A b]
            _ = _ := hb
        apply Function.LeftInverse.injective (hRinv' A)
        calc
          ηR.app A (B.compose A (iR.inv.app A a) (iR.inv.app A b) hrel) =
              G.compose A a b hab := by
                simpa only [hRinv A a, hRinv A b,
                  GroupoidInFunctors.compose] using
                  (hcomp A (iR.inv.app A a) (iR.inv.app A b) hrel).symm
          _ = ηR.app A (iR.inv.app A (G.compose A a b hab)) :=
            (hRinv A (G.compose A a b hab)).symm
    }
    let e : B ≅ G := {
      hom := f
      inv := g
      hom_inv_id := GroupoidInFunctors.Hom.ext (by ext A x; exact hUinv A x)
        (by ext A x; exact hRinv' A x)
      inv_hom_id := GroupoidInFunctors.Hom.ext (by ext A x; exact hUinv' A x)
        (by ext A x; exact hRinv A x)
    }
    exact ⟨e, rfl, rfl⟩

end Deformation.GroupoidInFunctors
