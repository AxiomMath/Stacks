module

public import Mathlib.CategoryTheory.Limits.Preserves.Limits
public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.HasPullback
public import Mathlib.CategoryTheory.Yoneda
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Formal.Groupoid.CofiberedCompletion
public import StacksFrontier.Deformation.Groupoid.Basic
public import StacksFrontier.Deformation.Groupoid.BaseCategory

/-!
# Completion of a groupoid in functors

Completing the object and arrow functors of a groupoid in functors on Artinian local
`Λ`-algebras produces a groupoid in functors on complete local `Λ`-algebras. Completion
is a right adjoint, so it preserves the pullback that defines the functor of composable
arrows; transporting the composition law along the resulting comparison supplies the
composition of the completed groupoid.

## Main definitions

* `Deformation.composableFirst`, `Deformation.composableSecond`: the two projections
  from the functor of composable arrows.
* `Deformation.GroupoidInFunctors.CompletionData`: the pullback comparison together with
  its compatibility with both projections and the pointwise groupoid law it induces.
* `Deformation.GroupoidInFunctors.completion`: the completed groupoid in functors.

## Implementation notes

`CompletionData` is data rather than an existence statement, so the composition of the
completed groupoid is a definite natural transformation. Its `pointwiseGroupoid` field
records that identities and inverses of the completion are the completions of the
original ones; this is proved by testing a section of a completion against all maps from
its base to an Artinian algebra, which determines it because the completion is a right
Kan extension.

The completed groupoid has, definitionally, the completions of the object and arrow
functors and of the source and target maps; only its composition is transported.

## References

* [Stacks Project, Tag 06KE](https://stacks.math.columbia.edu/tag/06KE)
-/

@[expose] public section

open CategoryTheory

namespace Deformation

universe u v w z c d e

/-- The first projection from the functor of composable arrows. -/
public def composableFirst {C : Type c} [Category.{d} C]
    (U R : Functor.{d, e} C (Type e)) (source target : R ⟶ U) :
    composableArrows U R source target ⟶ R where
  app T := ↾ (fun p : (composableArrows U R source target).obj T ↦ p.1.1)
  naturality _ _ _ := rfl

/-- The second projection from the functor of composable arrows. -/
public def composableSecond {C : Type c} [Category.{d} C]
    (U R : Functor.{d, e} C (Type e)) (source target : R ⟶ U) :
    composableArrows U R source target ⟶ R where
  app T := ↾ (fun p : (composableArrows U R source target).obj T ↦ p.1.2)
  naturality _ _ _ := rfl

namespace GroupoidInFunctors

/-- An isomorphism from the completion of the functor of composable arrows of `G` to the functor
of composable arrows of the completions, compatible with both projections, together with a
pointwise groupoid structure for the transported composition law. This is data, not a mere
existence proposition. -/
public structure CompletionData {Λ : Type u} {k : Type w} [CommRing Λ] [Field k]
    [Algebra Λ k]
    (G : GroupoidInFunctors.{_, v, max v z}
      (ArtinianLocalAlgCat.{u, v, w} Λ k)) where
  /-- The isomorphism from the completion of the composable arrows of `G` to the composable
  arrows of the completed object and arrow functors. -/
  comparison :
    (cofiberedCompletion (Λ := Λ) (k := k)).obj
        (composableArrows G.objects G.arrows G.source G.target) ≅
      composableArrows
        ((cofiberedCompletion (Λ := Λ) (k := k)).obj G.objects)
        ((cofiberedCompletion (Λ := Λ) (k := k)).obj G.arrows)
        ((cofiberedCompletion (Λ := Λ) (k := k)).map G.source)
        ((cofiberedCompletion (Λ := Λ) (k := k)).map G.target)
  /-- `comparison` is compatible with the first projections. -/
  first_comm :
    comparison.hom ≫ composableFirst _ _ _ _ =
      (cofiberedCompletion (Λ := Λ) (k := k)).map
        (composableFirst G.objects G.arrows G.source G.target)
  /-- `comparison` is compatible with the second projections. -/
  second_comm :
    comparison.hom ≫ composableSecond _ _ _ _ =
      (cofiberedCompletion (Λ := Λ) (k := k)).map
        (composableSecond G.objects G.arrows G.source G.target)
  /-- At each complete local algebra `T`, the completed source and target maps and the
  composition transported along `comparison` form a groupoid. -/
  pointwiseGroupoid : ∀ T,
    Nonempty (PointwiseGroupoid
      (((cofiberedCompletion (Λ := Λ) (k := k)).map G.source).app T)
      (((cofiberedCompletion (Λ := Λ) (k := k)).map G.target).app T)
      (fun p ↦ (comparison.inv ≫
        (cofiberedCompletion (Λ := Λ) (k := k)).map G.comp).app T p))

/-- The canonical pullback comparison and its induced pointwise groupoid law. -/
public noncomputable def completionData {Λ : Type u} {k : Type w} [CommRing Λ]
    [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors.{_, v, max v z}
      (ArtinianLocalAlgCat.{u, v, w} Λ k)) : CompletionData G := by
  classical
  let K := cofiberedCompletion (Λ := Λ) (k := k)
  let coord := fun (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
      (S : CompleteLocalAlgCat.{u, v, w} Λ k)
      (x : (K.obj F).obj S) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
      (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A) =>
    ((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.app F).app A
      ((K.obj F).map f x)
  have coordExt (F : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z))
      (S : CompleteLocalAlgCat.{u, v, w} Λ k) {x y : (K.obj F).obj S}
      (h : ∀ A (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A),
        coord F S x A f = coord F S y A f) : x = y := by
    let Y := uliftCoyoneda.{max v z}.obj (Opposite.op S)
    let α : Y ⟶ K.obj F := uliftCoyonedaEquiv.symm x
    let β : Y ⟶ K.obj F := uliftCoyonedaEquiv.symm y
    have hαβ : Functor.whiskerLeft (artinianToComplete (Λ := Λ) (k := k)) α ≫
        (cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.app F =
      Functor.whiskerLeft (artinianToComplete (Λ := Λ) (k := k)) β ≫
        (cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.app F := by
      apply NatTrans.ext
      funext A
      apply ConcreteCategory.hom_ext
      intro f
      simpa [α, β, Y, coord, uliftCoyonedaEquiv] using h A f.down
    let : (K.obj F).IsRightKanExtension
        ((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.app F) :=
      cofiberedCompletion_isRightKanExtension (Λ := Λ) (k := k) F
    have hab := Functor.hom_ext_of_isRightKanExtension (K.obj F)
      ((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.app F)
      α β hαβ
    have hxy := congrArg (fun η : Y ⟶ K.obj F => uliftCoyonedaEquiv η) hab
    simpa [α, β, Y] using hxy
  have coordMap {F F' : ArtinianLocalAlgCat.{u, v, w} Λ k ⥤ Type (max v z)}
      (φ : F ⟶ F') (S : CompleteLocalAlgCat.{u, v, w} Λ k)
      (x : (K.obj F).obj S) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
      (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A) :
      coord F' S ((K.map φ).app S x) A f = φ.app A (coord F S x A f) := by
    dsimp [coord]
    have hnat := NatTrans.naturality_apply (K.map φ) f x
    have hnat' := congrArg (fun y =>
      ((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.app F').app A y) hnat
    have hc := NatTrans.congr_app
      ((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.naturality φ) A
    have hc' := congrArg (fun m : (K.obj F).obj
        ((artinianToComplete (Λ := Λ) (k := k)).obj A) ⟶ F'.obj A =>
      m ((K.obj F).map f x)) hc
    change ((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.app F').app A
        (((K.map φ).app ((artinianToComplete (Λ := Λ) (k := k)).obj A))
          ((K.obj F).map f x)) =
      φ.app A (((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.app F).app A
        ((K.obj F).map f x)) at hc'
    calc
      ((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.app F').app A
          (((K.obj F').map f) ((K.map φ).app S x)) =
        ((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.app F').app A
          (((K.map φ).app ((artinianToComplete (Λ := Λ) (k := k)).obj A))
            ((K.obj F).map f x)) := hnat'.symm
      _ = φ.app A (((cofiberedCompletionAdjunction (Λ := Λ) (k := k)).counit.app F).app A
          ((K.obj F).map f x)) := hc'
  let q := composableArrows G.objects G.arrows G.source G.target
  let q' := composableArrows (K.obj G.objects) (K.obj G.arrows)
    (K.map G.source) (K.map G.target)
  let cone : Limits.PullbackCone G.source G.target := Limits.PullbackCone.mk
    (composableFirst G.objects G.arrows G.source G.target)
    (composableSecond G.objects G.arrows G.source G.target) (by
      ext T p
      exact p.2)
  let hq : Limits.IsLimit cone := by
    refine Limits.PullbackCone.isLimitAux' _ fun s => ?_
    let lift : s.pt ⟶ q := {
      app := fun T => ↾fun x => ⟨(s.fst.app T x, s.snd.app T x), by
        exact congrArg (fun f => f x) (NatTrans.congr_app s.condition T)⟩
      naturality := by
        intro X Y f
        ext x
        apply Subtype.ext
        apply Prod.ext <;> simp [q, composableArrows] }
    refine ⟨lift, ?_, ?_, ?_⟩
    · ext T x
      rfl
    · ext T x
      rfl
    · intro m hm₁ hm₂
      ext T x
      exact Subtype.ext (Prod.ext (congrArg (fun f => f x) (NatTrans.congr_app hm₁ T))
        (congrArg (fun f => f x) (NatTrans.congr_app hm₂ T)))
  letI : Limits.PreservesLimits K :=
    (cofiberedCompletionAdjunction (Λ := Λ) (k := k)).rightAdjoint_preservesLimits
  let hqMap : Limits.IsLimit
      (K.mapCone cone) :=
    Limits.isLimitOfPreserves K hq
  let hDiagram := Limits.cospanCompIso K G.source G.target
  let hConeEquiv := Limits.Cone.postcomposeEquivalence hDiagram
  let hqMapCone := hConeEquiv.functor.obj
      (K.mapCone cone)
  let hqMapPreCone := hConeEquiv.symm.functor.obj hqMapCone
  have hqMapPre : Limits.IsLimit hqMapPreCone :=
    hqMap.ofIsoLimit (hConeEquiv.unitIso.app
      (K.mapCone cone))
  let hqMap' : Limits.IsLimit
      hqMapCone :=
    (Limits.IsLimit.ofConeEquiv hConeEquiv.symm (c := hqMapCone)) hqMapPre
  let cone' : Limits.PullbackCone (K.map G.source) (K.map G.target) :=
    Limits.PullbackCone.mk
    (composableFirst (K.obj G.objects) (K.obj G.arrows) (K.map G.source) (K.map G.target))
    (composableSecond (K.obj G.objects) (K.obj G.arrows) (K.map G.source) (K.map G.target))
    (by ext T p; exact p.2)
  let hq' : Limits.IsLimit cone' := by
    refine Limits.PullbackCone.isLimitAux' _ fun s => ?_
    let lift : s.pt ⟶ q' := {
      app := fun T => ↾fun x => ⟨(s.fst.app T x, s.snd.app T x), by
        exact congrArg (fun f => f x) (NatTrans.congr_app s.condition T)⟩
      naturality := by
        intro X Y f
        ext x
        apply Subtype.ext
        apply Prod.ext <;> simp [q', composableArrows] }
    refine ⟨lift, ?_, ?_, ?_⟩
    · ext T x
      rfl
    · ext T x
      rfl
    · intro m hm₁ hm₂
      ext T x
      exact Subtype.ext (Prod.ext (congrArg (fun f => f x) (NatTrans.congr_app hm₁ T))
        (congrArg (fun f => f x) (NatTrans.congr_app hm₂ T)))
  let cmp := hqMap'.conePointUniqueUpToIso hq'
  have hfirst : hqMapCone.π.app Limits.WalkingCospan.left =
      K.map (composableFirst G.objects G.arrows G.source G.target) := by
    simp [hqMapCone, hConeEquiv, hDiagram, Limits.Cone.postcomposeEquivalence,
      Limits.Cone.postcompose, cone]
  have hsecond : hqMapCone.π.app Limits.WalkingCospan.right =
      K.map (composableSecond G.objects G.arrows G.source G.target) := by
    simp [hqMapCone, hConeEquiv, hDiagram, Limits.Cone.postcomposeEquivalence,
      Limits.Cone.postcompose, cone]
  refine ⟨cmp, ?_, ?_, ?_⟩
  · change cmp.hom ≫ composableFirst (K.obj G.objects) (K.obj G.arrows)
      (K.map G.source) (K.map G.target) =
        K.map (composableFirst G.objects G.arrows G.source G.target)
    exact (Limits.IsLimit.conePointUniqueUpToIso_hom_comp hqMap' hq'
      Limits.WalkingCospan.left).trans hfirst
  · change cmp.hom ≫ composableSecond (K.obj G.objects) (K.obj G.arrows)
      (K.map G.source) (K.map G.target) =
        K.map (composableSecond G.objects G.arrows G.source G.target)
    exact (Limits.IsLimit.conePointUniqueUpToIso_hom_comp hqMap' hq'
      Limits.WalkingCospan.right).trans hsecond
  · intro T
    classical
    let S : CompleteLocalAlgCat.{u, v, w} Λ k := T
    let s := (K.map G.source).app T
    let t := (K.map G.target).app T
    let c := fun p : q'.obj T => (cmp.inv ≫ K.map G.comp).app T p
    rcases existsUnique_identity G with ⟨e, he, -⟩
    rcases existsUnique_inverse G with ⟨i, hi, -⟩
    have hcmpFirst : cmp.hom ≫
        composableFirst (K.obj G.objects) (K.obj G.arrows) (K.map G.source) (K.map G.target) =
        K.map (composableFirst G.objects G.arrows G.source G.target) :=
      (Limits.IsLimit.conePointUniqueUpToIso_hom_comp hqMap' hq'
        Limits.WalkingCospan.left).trans hfirst
    have hcmpSecond : cmp.hom ≫
        composableSecond (K.obj G.objects) (K.obj G.arrows) (K.map G.source) (K.map G.target) =
        K.map (composableSecond G.objects G.arrows G.source G.target) :=
      (Limits.IsLimit.conePointUniqueUpToIso_hom_comp hqMap' hq'
        Limits.WalkingCospan.right).trans hsecond
    have coordPair (p : q'.obj T) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A) :
        coord q S (cmp.inv.app T p) A f =
          ⟨(coord G.arrows S p.1.1 A f,
              coord G.arrows S p.1.2 A f), by
            calc
              G.source.app A (coord G.arrows S p.1.1 A f) =
                  coord G.objects S (s p.1.1) A f :=
                (coordMap G.source S p.1.1 A f).symm
              _ = coord G.objects S (t p.1.2) A f := congrArg (fun x => coord G.objects S x A f) p.2
              _ = G.target.app A (coord G.arrows S p.1.2 A f) :=
                coordMap G.target S p.1.2 A f⟩ := by
      let r := cmp.inv.app T p
      have hr : cmp.hom.app T r = p :=
        congrArg (fun η : q' ⟶ q' => η.app T p) cmp.inv_hom_id
      have hfirst' : (K.map (composableFirst G.objects G.arrows G.source G.target)).app T r =
          (composableFirst (K.obj G.objects) (K.obj G.arrows)
            (K.map G.source) (K.map G.target)).app T p := by
        have hh' : (composableFirst (K.obj G.objects) (K.obj G.arrows)
            (K.map G.source) (K.map G.target)).app T (cmp.hom.app T r) =
              (K.map (composableFirst G.objects G.arrows G.source G.target)).app T r :=
          congrArg (fun η : (K.obj q) ⟶ (K.obj G.arrows) => η.app T r) hcmpFirst
        exact hh'.symm.trans (congrArg
          (fun x => (composableFirst (K.obj G.objects) (K.obj G.arrows)
            (K.map G.source) (K.map G.target)).app T x) hr)
      have hsecond' : (K.map (composableSecond G.objects G.arrows G.source G.target)).app T r =
          (composableSecond (K.obj G.objects) (K.obj G.arrows)
            (K.map G.source) (K.map G.target)).app T p := by
        have hh' : (composableSecond (K.obj G.objects) (K.obj G.arrows)
            (K.map G.source) (K.map G.target)).app T (cmp.hom.app T r) =
              (K.map (composableSecond G.objects G.arrows G.source G.target)).app T r :=
          congrArg (fun η : (K.obj q) ⟶ (K.obj G.arrows) => η.app T r) hcmpSecond
        exact hh'.symm.trans (congrArg
          (fun x => (composableSecond (K.obj G.objects) (K.obj G.arrows)
            (K.map G.source) (K.map G.target)).app T x) hr)
      apply Subtype.ext
      apply Prod.ext
      · calc
          (coord q S r A f).1.1 =
              coord G.arrows S
                ((K.map (composableFirst G.objects G.arrows G.source G.target)).app T r) A f := by
            symm
            simpa [composableFirst] using coordMap
              (composableFirst G.objects G.arrows G.source G.target) S r A f
          _ = coord G.arrows S
              ((composableFirst (K.obj G.objects) (K.obj G.arrows)
                (K.map G.source) (K.map G.target)).app T p) A f := by rw [hfirst']
          _ = coord G.arrows S p.1.1 A f := rfl
      · calc
          (coord q S r A f).1.2 =
              coord G.arrows S
                ((K.map (composableSecond G.objects G.arrows G.source G.target)).app T r) A f := by
            symm
            simpa [composableSecond] using coordMap
              (composableSecond G.objects G.arrows G.source G.target) S r A f
          _ = coord G.arrows S
              ((composableSecond (K.obj G.objects) (K.obj G.arrows)
                (K.map G.source) (K.map G.target)).app T p) A f := by rw [hsecond']
          _ = coord G.arrows S p.1.2 A f := rfl
    have coordComp (p : q'.obj T) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A) :
        coord G.arrows S (c p) A f =
          G.comp.app A ⟨(coord G.arrows S p.1.1 A f,
            coord G.arrows S p.1.2 A f), by
              calc
                G.source.app A (coord G.arrows S p.1.1 A f) =
                    coord G.objects S (s p.1.1) A f :=
                  (coordMap G.source S p.1.1 A f).symm
                _ = coord G.objects S (t p.1.2) A f :=
                  congrArg (fun x => coord G.objects S x A f) p.2
                _ = G.target.app A (coord G.arrows S p.1.2 A f) :=
                  coordMap G.target S p.1.2 A f⟩ := by
      dsimp [c]
      calc
        coord G.arrows S ((K.map G.comp).app T (cmp.inv.app T p)) A f =
            G.comp.app A (coord q S (cmp.inv.app T p) A f) :=
          coordMap G.comp S (cmp.inv.app T p) A f
        _ = G.comp.app A ⟨(coord G.arrows S p.1.1 A f,
              coord G.arrows S p.1.2 A f), by
                calc
                  G.source.app A (coord G.arrows S p.1.1 A f) =
                      coord G.objects S (s p.1.1) A f :=
                    (coordMap G.source S p.1.1 A f).symm
                  _ = coord G.objects S (t p.1.2) A f :=
                    congrArg (fun x => coord G.objects S x A f) p.2
                  _ = G.target.app A (coord G.arrows S p.1.2 A f) :=
                    coordMap G.target S p.1.2 A f⟩ := by
            rw [coordPair]
    have hcoordS (a : (K.obj G.arrows).obj T) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A) :
        coord G.objects S (s a) A f =
          G.source.app A (coord G.arrows S a A f) :=
      coordMap G.source S a A f
    have hcoordT (a : (K.obj G.arrows).obj T) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A) :
        coord G.objects S (t a) A f =
          G.target.app A (coord G.arrows S a A f) :=
      coordMap G.target S a A f
    have hcoordId (x : (K.obj G.objects).obj T) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A) :
        coord G.arrows S ((K.map e).app T x) A f =
          G.identity A (coord G.objects S x A f) := by
      rw [coordMap, he]
    have hcoordInv (a : (K.obj G.arrows).obj T) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A) :
        coord G.arrows S ((K.map i).app T a) A f =
          inverseArrow G A (coord G.arrows S a A f) := by
      rw [coordMap, hi]
    have origIdSource (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (x : G.objects.obj A) : G.source.app A (G.identity A x) = x := by
      let P := G.pointwiseData A
      let := P.groupoid
      exact (G.evaluationArrowEquiv A x x (𝟙 x)).2.1
    have origIdTarget (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (x : G.objects.obj A) : G.target.app A (G.identity A x) = x := by
      let P := G.pointwiseData A
      let := P.groupoid
      exact (G.evaluationArrowEquiv A x x (𝟙 x)).2.2
    have origInvSource (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (a : G.arrows.obj A) :
        G.source.app A (inverseArrow G A a) = G.target.app A a := by
      let P := G.pointwiseData A
      let := P.groupoid
      let x := G.source.app A a
      let y := G.target.app A a
      exact (G.evaluationArrowEquiv A y x
        (Groupoid.inv ((G.evaluationArrowEquiv A x y).symm ⟨a, rfl, rfl⟩))).2.1
    have origInvTarget (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (a : G.arrows.obj A) :
        G.target.app A (inverseArrow G A a) = G.source.app A a := by
      let P := G.pointwiseData A
      let := P.groupoid
      let x := G.source.app A a
      let y := G.target.app A a
      exact (G.evaluationArrowEquiv A y x
        (Groupoid.inv ((G.evaluationArrowEquiv A x y).symm ⟨a, rfl, rfl⟩))).2.2
    have origCompSource (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (a b : G.arrows.obj A) (h : G.source.app A a = G.target.app A b) :
        G.source.app A (G.compose A a b h) = G.source.app A b := by
      let P := G.pointwiseData A
      let := P.groupoid
      let x := G.source.app A b
      let y := G.target.app A b
      let z := G.target.app A a
      let g := (P.arrowEquiv x y).symm ⟨b, rfl, rfl⟩
      let f := (P.arrowEquiv y z).symm ⟨a, h, rfl⟩
      have hc' : (P.arrowEquiv x z (g ≫ f)).1 = G.compose A a b h := by
        simpa [g, f, GroupoidInFunctors.compose] using P.comp_eq g f
      rw [← hc']
      exact (P.arrowEquiv x z (g ≫ f)).2.1
    have origCompTarget (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (a b : G.arrows.obj A) (h : G.source.app A a = G.target.app A b) :
        G.target.app A (G.compose A a b h) = G.target.app A a := by
      let P := G.pointwiseData A
      let := P.groupoid
      let x := G.source.app A b
      let y := G.target.app A b
      let z := G.target.app A a
      let g := (P.arrowEquiv x y).symm ⟨b, rfl, rfl⟩
      let f := (P.arrowEquiv y z).symm ⟨a, h, rfl⟩
      have hc' : (P.arrowEquiv x z (g ≫ f)).1 = G.compose A a b h := by
        simpa [g, f, GroupoidInFunctors.compose] using P.comp_eq g f
      rw [← hc']
      exact (P.arrowEquiv x z (g ≫ f)).2.2
    have origUnitLeft (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (a : G.arrows.obj A) :
        G.compose A a (G.identity A (G.source.app A a)) (by
          rw [origIdTarget]) = a := by
      let P := G.pointwiseData A
      let := P.groupoid
      let x := G.source.app A a
      let y := G.target.app A a
      let f := (P.arrowEquiv x y).symm ⟨a, rfl, rfl⟩
      have hid : (P.arrowEquiv x x (𝟙 x)).1 = G.identity A x := rfl
      have hc := P.comp_eq (𝟙 x) f
      have hc' : G.compose A a (G.identity A x) (by rw [origIdTarget]) =
          (P.arrowEquiv x y (𝟙 x ≫ f)).1 := by
        simpa only [f, GroupoidInFunctors.compose, Equiv.apply_symm_apply, hid] using hc.symm
      calc
        G.compose A a (G.identity A x) (by rw [origIdTarget]) =
            (P.arrowEquiv x y (𝟙 x ≫ f)).1 := hc'
        _ = (P.arrowEquiv x y f).1 := congrArg (fun g => (P.arrowEquiv x y g).1)
          (Category.id_comp f)
        _ = a := by
          change (P.arrowEquiv x y ((P.arrowEquiv x y).symm ⟨a, rfl, rfl⟩)).1 = a
          simp
    have origUnitRight (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (a : G.arrows.obj A) :
        G.compose A (G.identity A (G.target.app A a)) a (by
          rw [origIdSource]) = a := by
      let P := G.pointwiseData A
      let := P.groupoid
      let x := G.source.app A a
      let y := G.target.app A a
      let f := (P.arrowEquiv x y).symm ⟨a, rfl, rfl⟩
      have hid : (P.arrowEquiv y y (𝟙 y)).1 = G.identity A y := rfl
      have hc := P.comp_eq f (𝟙 y)
      have hc' : G.compose A (G.identity A y) a (by rw [origIdSource]) =
          (P.arrowEquiv x y (f ≫ 𝟙 y)).1 := by
        simpa only [f, GroupoidInFunctors.compose, Equiv.apply_symm_apply, hid] using hc.symm
      calc
        G.compose A (G.identity A y) a (by rw [origIdSource]) =
            (P.arrowEquiv x y (f ≫ 𝟙 y)).1 := hc'
        _ = (P.arrowEquiv x y f).1 := congrArg (fun g => (P.arrowEquiv x y g).1)
          (Category.comp_id f)
        _ = a := by
          change (P.arrowEquiv x y ((P.arrowEquiv x y).symm ⟨a, rfl, rfl⟩)).1 = a
          simp
    have origInvLeft (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (a : G.arrows.obj A) :
        G.compose A a (inverseArrow G A a) (by rw [origInvTarget]) =
          G.identity A (G.target.app A a) := by
      let P := G.pointwiseData A
      let := P.groupoid
      let x := G.source.app A a
      let y := G.target.app A a
      let f := (P.arrowEquiv x y).symm ⟨a, rfl, rfl⟩
      let g := (P.arrowEquiv y x).symm
        ⟨inverseArrow G A a, origInvSource A a, origInvTarget A a⟩
      have hInvDef : inverseArrow G A a = (P.arrowEquiv y x (Groupoid.inv f)).1 := by
        rfl
      have hg : g = Groupoid.inv f := by
        apply (P.arrowEquiv y x).injective
        apply Subtype.ext
        simpa [g] using hInvDef
      have hc' : G.compose A a (inverseArrow G A a) (by rw [origInvTarget]) =
          (P.arrowEquiv y y (g ≫ f)).1 := by
        simpa [f, g, GroupoidInFunctors.compose] using (P.comp_eq g f).symm
      calc
        G.compose A a (inverseArrow G A a) (by rw [origInvTarget]) =
            (P.arrowEquiv y y (g ≫ f)).1 := hc'
        _ = (P.arrowEquiv y y (𝟙 y)).1 := by
          rw [hg, Groupoid.inv_comp]
        _ = G.identity A y := rfl
    have origInvRight (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (a : G.arrows.obj A) :
        G.compose A (inverseArrow G A a) a (by rw [origInvSource]) =
          G.identity A (G.source.app A a) := by
      let P := G.pointwiseData A
      let := P.groupoid
      let x := G.source.app A a
      let y := G.target.app A a
      let f := (P.arrowEquiv x y).symm ⟨a, rfl, rfl⟩
      let g := (P.arrowEquiv y x).symm
        ⟨inverseArrow G A a, origInvSource A a, origInvTarget A a⟩
      have hInvDef : inverseArrow G A a = (P.arrowEquiv y x (Groupoid.inv f)).1 := by
        rfl
      have hg : g = Groupoid.inv f := by
        apply (P.arrowEquiv y x).injective
        apply Subtype.ext
        simpa [g] using hInvDef
      have hc' : G.compose A (inverseArrow G A a) a (by rw [origInvSource]) =
          (P.arrowEquiv x x (f ≫ g)).1 := by
        simpa [f, g, GroupoidInFunctors.compose] using (P.comp_eq f g).symm
      calc
        G.compose A (inverseArrow G A a) a (by rw [origInvSource]) =
            (P.arrowEquiv x x (f ≫ g)).1 := hc'
        _ = (P.arrowEquiv x x (𝟙 x)).1 := by
          rw [hg, Groupoid.comp_inv]
        _ = G.identity A x := rfl
    have origAssoc (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (a b d : G.arrows.obj A)
        (hab : G.source.app A a = G.target.app A b)
        (hbd : G.source.app A b = G.target.app A d) :
        G.compose A (G.compose A a b hab) d (by rw [origCompSource]; exact hbd) =
          G.compose A a (G.compose A b d hbd) (by rw [origCompTarget]; exact hab) := by
      let P := G.pointwiseData A
      let := P.groupoid
      let x := G.source.app A d
      let y := G.target.app A d
      let z := G.target.app A b
      let w := G.target.app A a
      let fd := (P.arrowEquiv x y).symm ⟨d, rfl, rfl⟩
      let fb := (P.arrowEquiv y z).symm ⟨b, hbd, rfl⟩
      let fa := (P.arrowEquiv z w).symm ⟨a, hab, rfl⟩
      have hfdVal : (P.arrowEquiv x y fd).1 = d := by simp [fd]
      have hfdTarget : G.target.app A d = y := by
        simpa [fd] using (P.arrowEquiv x y fd).2.2
      have hfaVal : (P.arrowEquiv z w fa).1 = a := by simp [fa]
      have hbf : (P.arrowEquiv y w (fb ≫ fa)).1 = G.compose A a b hab := by
        simpa only [fb, fa, Equiv.apply_symm_apply, GroupoidInFunctors.compose] using
          P.comp_eq fb fa
      have hdb : (P.arrowEquiv x z (fd ≫ fb)).1 = G.compose A b d hbd := by
        simpa only [fd, fb, Equiv.apply_symm_apply, GroupoidInFunctors.compose] using
          P.comp_eq fd fb
      have compose_congr (r r' q q' : G.arrows.obj A) (hr : r = r') (hq : q = q')
          (h : G.source.app A r = G.target.app A q)
          (h' : G.source.app A r' = G.target.app A q') :
          G.compose A r q h = G.compose A r' q' h' := by
        unfold GroupoidInFunctors.compose
        congr 1
        exact Subtype.ext (Prod.ext hr hq)
      have hleft : G.compose A (G.compose A a b hab) d
          (by rw [origCompSource]; exact hbd) =
          (P.arrowEquiv x w (fd ≫ (fb ≫ fa))).1 := by
        calc
          G.compose A (G.compose A a b hab) d (by rw [origCompSource]; exact hbd) =
              G.compose A (P.arrowEquiv y w (fb ≫ fa)).1 d (by
                exact (P.arrowEquiv y w (fb ≫ fa)).2.1.trans
                  hfdTarget.symm) :=
            compose_congr (G.compose A a b hab) (P.arrowEquiv y w (fb ≫ fa)).1 d d
              hbf.symm rfl _ _
          _ = G.compose A (P.arrowEquiv y w (fb ≫ fa)).1 (P.arrowEquiv x y fd).1 _ :=
            compose_congr (P.arrowEquiv y w (fb ≫ fa)).1
              (P.arrowEquiv y w (fb ≫ fa)).1 d (P.arrowEquiv x y fd).1
              rfl hfdVal.symm _ _
          _ = (P.arrowEquiv x w (fd ≫ (fb ≫ fa))).1 := (P.comp_eq fd (fb ≫ fa)).symm
      have hright : (P.arrowEquiv x w ((fd ≫ fb) ≫ fa)).1 =
          G.compose A a (G.compose A b d hbd) (by rw [origCompTarget]; exact hab) := by
        have hfaSource : G.source.app A a = z := by
          simpa [fa] using (P.arrowEquiv z w fa).2.1
        have hdbTarget : G.target.app A (P.arrowEquiv x z (fd ≫ fb)).1 = z :=
          (P.arrowEquiv x z (fd ≫ fb)).2.2
        have hbdTarget : G.target.app A (G.compose A b d hbd) = z := by
          rw [origCompTarget]
        calc
          (P.arrowEquiv x w ((fd ≫ fb) ≫ fa)).1 =
              G.compose A (P.arrowEquiv z w fa).1 (P.arrowEquiv x z (fd ≫ fb)).1
                ((P.arrowEquiv z w fa).2.1.trans
                  (P.arrowEquiv x z (fd ≫ fb)).2.2.symm) := P.comp_eq (fd ≫ fb) fa
          _ = G.compose A a (P.arrowEquiv x z (fd ≫ fb)).1 _ :=
            compose_congr (P.arrowEquiv z w fa).1 a (P.arrowEquiv x z (fd ≫ fb)).1
              (P.arrowEquiv x z (fd ≫ fb)).1 hfaVal rfl _
              (hfaSource.trans hdbTarget.symm)
          _ = G.compose A a (G.compose A b d hbd) (by rw [origCompTarget]; exact hab) :=
            compose_congr a a (P.arrowEquiv x z (fd ≫ fb)).1 (G.compose A b d hbd)
              rfl hdb (hfaSource.trans hdbTarget.symm) (hfaSource.trans hbdTarget.symm)
      calc
        G.compose A (G.compose A a b hab) d (by rw [origCompSource]; exact hbd) =
            (P.arrowEquiv x w (fd ≫ (fb ≫ fa))).1 := hleft
        _ = (P.arrowEquiv x w ((fd ≫ fb) ≫ fa)).1 :=
          congrArg (fun g => (P.arrowEquiv x w g).1) (Category.assoc fd fb fa).symm
        _ = G.compose A a (G.compose A b d hbd) (by rw [origCompTarget]; exact hab) := hright
    have origComposeCongr (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (a a' b b' : G.arrows.obj A) (ha : a = a') (hb : b = b')
        (h : G.source.app A a = G.target.app A b)
        (h' : G.source.app A a' = G.target.app A b') :
        G.compose A a b h = G.compose A a' b' h' := by
      unfold GroupoidInFunctors.compose
      congr 1
      exact Subtype.ext (Prod.ext ha hb)
    have origUnitLeftAt (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (a : G.arrows.obj A) (x : G.objects.obj A)
        (hx : G.source.app A a = x) :
        G.compose A a (G.identity A x) (by rw [origIdTarget]; exact hx) = a := by
      cases hx
      exact origUnitLeft A a
    have origUnitRightAt (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (a : G.arrows.obj A) (y : G.objects.obj A)
        (hy : G.target.app A a = y) :
        G.compose A (G.identity A y) a (by rw [origIdSource]; exact hy.symm) = a := by
      cases hy
      exact origUnitRight A a
    let U := (K.obj G.objects).obj T
    let R := (K.obj G.arrows).obj T
    have coordSource (a : R) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A) :
        coord G.objects S (s a) A f = G.source.app A (coord G.arrows S a A f) :=
      hcoordS a A f
    have coordTarget (a : R) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A) :
        coord G.objects S (t a) A f = G.target.app A (coord G.arrows S a A f) :=
      hcoordT a A f
    have coordIdentity (x : U) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A) :
        coord G.arrows S ((K.map e).app T x) A f =
          G.identity A (coord G.objects S x A f) := hcoordId x A f
    have coordInverse (a : R) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A) :
        coord G.arrows S ((K.map i).app T a) A f =
          inverseArrow G A (coord G.arrows S a A f) := hcoordInv a A f
    have coordComposeAt (p : q'.obj T) (A : ArtinianLocalAlgCat.{u, v, w} Λ k)
        (f : S ⟶ (artinianToComplete (Λ := Λ) (k := k)).obj A) :
        coord G.arrows S (c p) A f = G.compose A
          (coord G.arrows S p.1.1 A f) (coord G.arrows S p.1.2 A f) (by
            calc
              G.source.app A (coord G.arrows S p.1.1 A f) = coord G.objects S (s p.1.1) A f :=
                (coordSource p.1.1 A f).symm
              _ = coord G.objects S (t p.1.2) A f := congrArg (fun x => coord G.objects S x A f) p.2
              _ = G.target.app A (coord G.arrows S p.1.2 A f) := coordTarget p.1.2 A f) := by
      simpa [GroupoidInFunctors.compose] using coordComp p A f
    have idSource (x : U) : s ((K.map e).app T x) = x :=
      coordExt G.objects S fun A f => by rw [coordSource, coordIdentity, origIdSource]
    have idTarget (x : U) : t ((K.map e).app T x) = x :=
      coordExt G.objects S fun A f => by rw [coordTarget, coordIdentity, origIdTarget]
    have invSource (a : R) : s ((K.map i).app T a) = t a :=
      coordExt G.objects S fun A f => by rw [coordSource, coordInverse, coordTarget, origInvSource]
    have invTarget (a : R) : t ((K.map i).app T a) = s a :=
      coordExt G.objects S fun A f => by rw [coordTarget, coordInverse, coordSource, origInvTarget]
    have compSource (a b : R) (hab : s a = t b) :
        s (c ⟨(a, b), hab⟩) = s b := by
      let p : q'.obj T := ⟨(a, b), hab⟩
      refine coordExt G.objects S fun A f => ?_
      have hab' : G.source.app A (coord G.arrows S a A f) =
          G.target.app A (coord G.arrows S b A f) := by
        calc
          G.source.app A (coord G.arrows S a A f) = coord G.objects S (s a) A f :=
            (coordSource a A f).symm
          _ = coord G.objects S (t b) A f := congrArg (fun x => coord G.objects S x A f) hab
          _ = G.target.app A (coord G.arrows S b A f) := coordTarget b A f
      calc
        coord G.objects S (s (c p)) A f = G.source.app A (coord G.arrows S (c p) A f) :=
          coordSource (c p) A f
        _ = G.source.app A (G.compose A (coord G.arrows S a A f)
            (coord G.arrows S b A f) hab') := congrArg (G.source.app A)
          (coordComposeAt p A f)
        _ = G.source.app A (coord G.arrows S b A f) := origCompSource A _ _ hab'
        _ = coord G.objects S (s b) A f := (coordSource b A f).symm
    have compTarget (a b : R) (hab : s a = t b) :
        t (c ⟨(a, b), hab⟩) = t a := by
      let p : q'.obj T := ⟨(a, b), hab⟩
      refine coordExt G.objects S fun A f => ?_
      have hab' : G.source.app A (coord G.arrows S a A f) =
          G.target.app A (coord G.arrows S b A f) := by
        calc
          G.source.app A (coord G.arrows S a A f) = coord G.objects S (s a) A f :=
            (coordSource a A f).symm
          _ = coord G.objects S (t b) A f := congrArg (fun x => coord G.objects S x A f) hab
          _ = G.target.app A (coord G.arrows S b A f) := coordTarget b A f
      calc
        coord G.objects S (t (c p)) A f = G.target.app A (coord G.arrows S (c p) A f) :=
          coordTarget (c p) A f
        _ = G.target.app A (G.compose A (coord G.arrows S a A f)
            (coord G.arrows S b A f) hab') := congrArg (G.target.app A)
          (coordComposeAt p A f)
        _ = G.target.app A (coord G.arrows S a A f) := origCompTarget A _ _ hab'
        _ = coord G.objects S (t a) A f := (coordTarget a A f).symm
    let : Groupoid U := {
      Hom x y := {a : R // s a = x ∧ t a = y}
      id x := ⟨(K.map e).app T x, ⟨idSource x, idTarget x⟩⟩
      comp {x y z} f g :=
        ⟨c ⟨(g.1, f.1), g.2.1.trans f.2.2.symm⟩,
          ⟨(compSource g.1 f.1 (g.2.1.trans f.2.2.symm)).trans f.2.1,
           (compTarget g.1 f.1 (g.2.1.trans f.2.2.symm)).trans g.2.2⟩⟩
      id_comp := by
        intro x y f
        apply Subtype.ext
        apply coordExt G.arrows S
        intro A f'
        let ex := (K.map e).app T x
        let p : q'.obj T := ⟨(f.1, ex), f.2.1.trans (idTarget x).symm⟩
        have hc := coordComposeAt p A f'
        have hid := coordIdentity x A f'
        have hs : G.source.app A (coord G.arrows S f.1 A f') = coord G.objects S x A f' := by
          calc
            G.source.app A (coord G.arrows S f.1 A f') = coord G.objects S (s f.1) A f' :=
              (coordSource f.1 A f').symm
            _ = coord G.objects S x A f' := congrArg (fun z => coord G.objects S z A f') f.2.1
        calc
          coord G.arrows S (c p) A f' =
              G.compose A (coord G.arrows S f.1 A f')
                (coord G.arrows S ex A f') _ := hc
          _ = G.compose A (coord G.arrows S f.1 A f')
                (G.identity A (coord G.objects S x A f')) _ :=
            origComposeCongr A _ _ _ _ rfl hid _ _
          _ = coord G.arrows S f.1 A f' :=
            origUnitLeftAt A (coord G.arrows S f.1 A f')
              (coord G.objects S x A f') hs
      comp_id := by
        intro x y f
        apply Subtype.ext
        apply coordExt G.arrows S
        intro A f'
        let ey := (K.map e).app T y
        let p : q'.obj T := ⟨(ey, f.1), (idSource y).trans f.2.2.symm⟩
        have hc := coordComposeAt p A f'
        have hid := coordIdentity y A f'
        have ht : G.target.app A (coord G.arrows S f.1 A f') = coord G.objects S y A f' := by
          calc
            G.target.app A (coord G.arrows S f.1 A f') = coord G.objects S (t f.1) A f' :=
              (coordTarget f.1 A f').symm
            _ = coord G.objects S y A f' := congrArg (fun z => coord G.objects S z A f') f.2.2
        calc
          coord G.arrows S (c p) A f' =
              G.compose A (coord G.arrows S ey A f')
                (coord G.arrows S f.1 A f') _ := hc
          _ = G.compose A (G.identity A (coord G.objects S y A f'))
                (coord G.arrows S f.1 A f') _ :=
            origComposeCongr A _ _ _ _ hid rfl _ _
          _ = coord G.arrows S f.1 A f' :=
            origUnitRightAt A (coord G.arrows S f.1 A f')
              (coord G.objects S y A f') ht
      assoc := by
        intro x y z w f g h
        apply Subtype.ext
        apply coordExt G.arrows S
        intro A f'
        let pfg : q'.obj T := ⟨(g.1, f.1), g.2.1.trans f.2.2.symm⟩
        let pleft : q'.obj T := ⟨(h.1, c pfg),
          h.2.1.trans ((compTarget g.1 f.1 pfg.2).trans g.2.2).symm⟩
        let pgh : q'.obj T := ⟨(h.1, g.1), h.2.1.trans g.2.2.symm⟩
        let pright : q'.obj T := ⟨(c pgh, f.1),
          (compSource h.1 g.1 pgh.2).trans (g.2.1.trans f.2.2.symm)⟩
        have hfgCoord : G.source.app A (coord G.arrows S g.1 A f') =
            G.target.app A (coord G.arrows S f.1 A f') := by
          calc
            G.source.app A (coord G.arrows S g.1 A f') = coord G.objects S (s g.1) A f' :=
              (coordSource g.1 A f').symm
            _ = coord G.objects S y A f' := congrArg (fun z => coord G.objects S z A f') g.2.1
            _ = coord G.objects S (t f.1) A f' :=
              (congrArg (fun z => coord G.objects S z A f') f.2.2).symm
            _ = G.target.app A (coord G.arrows S f.1 A f') := coordTarget f.1 A f'
        have hghCoord : G.source.app A (coord G.arrows S h.1 A f') =
            G.target.app A (coord G.arrows S g.1 A f') := by
          calc
            G.source.app A (coord G.arrows S h.1 A f') = coord G.objects S (s h.1) A f' :=
              (coordSource h.1 A f').symm
            _ = coord G.objects S z A f' := congrArg (fun z => coord G.objects S z A f') h.2.1
            _ = coord G.objects S (t g.1) A f' :=
              (congrArg (fun z => coord G.objects S z A f') g.2.2).symm
            _ = G.target.app A (coord G.arrows S g.1 A f') := coordTarget g.1 A f'
        have hleft := coordComposeAt pleft A f'
        have hleftInner := coordComposeAt pfg A f'
        have hright := coordComposeAt pright A f'
        have hrightInner := coordComposeAt pgh A f'
        have houterCoordBase : G.source.app A (coord G.arrows S h.1 A f') =
            G.target.app A (G.compose A (coord G.arrows S g.1 A f')
              (coord G.arrows S f.1 A f') hfgCoord) := by
          rw [origCompTarget]
          exact hghCoord
        have houterCoord : G.source.app A (coord G.arrows S h.1 A f') =
            G.target.app A (coord G.arrows S (c pfg) A f') :=
          houterCoordBase.trans (congrArg (G.target.app A) hleftInner).symm
        have hrightCoordBase : G.source.app A (G.compose A (coord G.arrows S h.1 A f')
              (coord G.arrows S g.1 A f') hghCoord) =
            G.target.app A (coord G.arrows S f.1 A f') := by
          rw [origCompSource]
          exact hfgCoord
        have hrightCoord : G.source.app A (coord G.arrows S (c pgh) A f') =
            G.target.app A (coord G.arrows S f.1 A f') :=
          (congrArg (G.source.app A) hrightInner).trans hrightCoordBase
        calc
          coord G.arrows S (c pleft) A f' =
              G.compose A (coord G.arrows S h.1 A f')
                (coord G.arrows S (c pfg) A f') _ := hleft
          _ = G.compose A (coord G.arrows S h.1 A f')
                (G.compose A (coord G.arrows S g.1 A f')
                  (coord G.arrows S f.1 A f') hfgCoord) houterCoordBase :=
            origComposeCongr A (coord G.arrows S h.1 A f') (coord G.arrows S h.1 A f')
              (coord G.arrows S (c pfg) A f')
              (G.compose A (coord G.arrows S g.1 A f') (coord G.arrows S f.1 A f') hfgCoord)
              rfl hleftInner houterCoord houterCoordBase
          _ = G.compose A (G.compose A (coord G.arrows S h.1 A f')
                (coord G.arrows S g.1 A f') hghCoord)
                (coord G.arrows S f.1 A f') hrightCoordBase :=
            (origAssoc A (coord G.arrows S h.1 A f') (coord G.arrows S g.1 A f')
              (coord G.arrows S f.1 A f') hghCoord hfgCoord).symm
          _ = G.compose A (coord G.arrows S (c pgh) A f')
                (coord G.arrows S f.1 A f') _ :=
            origComposeCongr A
              (G.compose A (coord G.arrows S h.1 A f') (coord G.arrows S g.1 A f') hghCoord)
              (coord G.arrows S (c pgh) A f')
              (coord G.arrows S f.1 A f') (coord G.arrows S f.1 A f')
              hrightInner.symm rfl hrightCoordBase hrightCoord
          _ = coord G.arrows S (c pright) A f' := hright.symm
      inv {x y} f := ⟨(K.map i).app T f.1,
        ⟨(invSource f.1).trans f.2.2, (invTarget f.1).trans f.2.1⟩⟩
      inv_comp := by
        intro x y f
        apply Subtype.ext
        apply coordExt G.arrows S
        intro A f'
        let iy := (K.map i).app T f.1
        let p : q'.obj T := ⟨(f.1, iy), (invTarget f.1).symm⟩
        have hc := coordComposeAt p A f'
        have hi := coordInverse f.1 A f'
        have hy := coordIdentity y A f'
        have ht : G.target.app A (coord G.arrows S f.1 A f') = coord G.objects S y A f' := by
          calc
            G.target.app A (coord G.arrows S f.1 A f') = coord G.objects S (t f.1) A f' :=
              (coordTarget f.1 A f').symm
            _ = coord G.objects S y A f' := congrArg (fun z => coord G.objects S z A f') f.2.2
        calc
          coord G.arrows S (c p) A f' = G.compose A (coord G.arrows S f.1 A f')
              (coord G.arrows S iy A f') _ := hc
          _ = G.compose A (coord G.arrows S f.1 A f')
              (inverseArrow G A (coord G.arrows S f.1 A f')) _ :=
            origComposeCongr A _ _ _ _ rfl hi _ _
          _ = G.identity A (coord G.objects S y A f') :=
            (origInvLeft A _).trans (congrArg (G.identity A) ht)
          _ = coord G.arrows S ((K.map e).app T y) A f' := hy.symm
      comp_inv := by
        intro x y f
        apply Subtype.ext
        apply coordExt G.arrows S
        intro A f'
        let ix := (K.map i).app T f.1
        let p : q'.obj T := ⟨(ix, f.1), invSource f.1⟩
        have hc := coordComposeAt p A f'
        have hi := coordInverse f.1 A f'
        have hx := coordIdentity x A f'
        have hs : G.source.app A (coord G.arrows S f.1 A f') = coord G.objects S x A f' := by
          calc
            G.source.app A (coord G.arrows S f.1 A f') = coord G.objects S (s f.1) A f' :=
              (coordSource f.1 A f').symm
            _ = coord G.objects S x A f' := congrArg (fun z => coord G.objects S z A f') f.2.1
        calc
          coord G.arrows S (c p) A f' = G.compose A (coord G.arrows S ix A f')
              (coord G.arrows S f.1 A f') _ := hc
          _ = G.compose A (inverseArrow G A (coord G.arrows S f.1 A f'))
              (coord G.arrows S f.1 A f') _ :=
            origComposeCongr A _ _ _ _ hi rfl _ _
          _ = G.identity A (coord G.objects S x A f') :=
            (origInvRight A _).trans (congrArg (G.identity A) hs)
          _ = coord G.arrows S ((K.map e).app T x) A f' := hx.symm
    }
    refine ⟨⟨inferInstance, fun x y => Equiv.refl _, ?_⟩⟩
    intro x y z g f
    rfl

/-- Completion of a groupoid in functors on Artinian local algebras. -/
@[implicit_reducible, stacks 06KE]
public noncomputable def completion {Λ : Type u} {k : Type w} [CommRing Λ]
    [Field k] [Algebra Λ k]
    (G : GroupoidInFunctors.{_, v, max v z}
      (ArtinianLocalAlgCat.{u, v, w} Λ k)) :
    GroupoidInFunctors.{_, v, max v z}
      (CompleteLocalAlgCat.{u, v, w} Λ k) :=
  let d := completionData G
  { objects := (cofiberedCompletion (Λ := Λ) (k := k)).obj G.objects
    arrows := (cofiberedCompletion (Λ := Λ) (k := k)).obj G.arrows
    source := (cofiberedCompletion (Λ := Λ) (k := k)).map G.source
    target := (cofiberedCompletion (Λ := Λ) (k := k)).map G.target
    comp := d.comparison.inv ≫ (cofiberedCompletion (Λ := Λ) (k := k)).map G.comp
    pointwiseGroupoid := d.pointwiseGroupoid }

end GroupoidInFunctors

end Deformation
