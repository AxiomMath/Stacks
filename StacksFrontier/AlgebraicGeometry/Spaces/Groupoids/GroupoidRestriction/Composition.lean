module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestriction.Arrows

/-!
# Restriction of a groupoid in algebraic spaces: sections of arrows and composition

Part of the restriction of a groupoid in algebraic spaces along a morphism `g : U' ⟶ G.objects`
(Stacks 044B). This file describes the sections over `T` of the restricted arrow space
(`RestrictionArrowData`, `restrictionArrowDataEquiv`), identifies the arrows between two sections
of `U'` with arrows of the evaluated groupoid of `G` (`restrictionHomEquiv`), and constructs the
composition law of the restriction (`restrictionComp`, `restrictionCompForGroupoid`) together with
the computation of the source, target and underlying arrow of a composite.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace AlgebraicGeometry

namespace GroupoidInAlgebraicSpaces

/-- A section over `T` of the arrow space of a restriction, unpacked: an arrow of `G` together
with a lift along `g` of each of its two endpoints. -/
public structure RestrictionArrowData
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (T : (BigFppfOver C S hS)ᵒᵖ) where
  /-- The lift along `g` of the source of `arrow`. -/
  sourceLift : U'.obj.obj T
  /-- The underlying arrow of `G`. -/
  arrow : G.arrows.obj.obj T
  /-- The lift along `g` of the target of `arrow`. -/
  targetLift : U'.obj.obj T
  target_eq : g.hom.app T targetLift = G.target.hom.app T arrow
  source_eq : G.source.hom.app T arrow = g.hom.app T sourceLift

/-- Such a datum is determined by its arrow and its two lifts; the two compatibilities it
carries are propositions. -/
public theorem RestrictionArrowData.ext
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    {G : GroupoidInAlgebraicSpaces C S hS B}
    {U' : AlgebraicSpaces C S hS} {g : U' ⟶ G.objects}
    {T : (BigFppfOver C S hS)ᵒᵖ}
    {d d' : RestrictionArrowData G g T}
    (hs : d.sourceLift = d'.sourceLift) (ha : d.arrow = d'.arrow)
    (ht : d.targetLift = d'.targetLift) : d = d' := by
  cases d with
  | mk s a t hta hsa =>
    cases d' with
    | mk s' a' t' hta' hsa' =>
      dsimp at hs ha ht
      subst s'
      subst a'
      subst t'
      rfl

/-- Sections over `T` of the arrow space of the restriction are precisely the data of an arrow
of `G` with a lift of each endpoint. -/
public noncomputable def restrictionArrowDataEquiv
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    (restrictionArrows G g).obj.obj T ≃ RestrictionArrowData G g T := by
  let p := pullback.snd g.hom G.target.hom
  let q := pullback.fst G.source.hom g.hom
  let e₁ := pullbackAppEquiv g.hom G.target.hom T
  let e₂ := pullbackAppEquiv G.source.hom g.hom T
  let e₀ := pullbackAppEquiv p q T
  refine
    { toFun := fun z =>
        let v := e₀ z
        let a := e₁ v.1.1
        let b := e₂ v.1.2
        have hmid : a.1.2 = b.1.1 := by
          calc
            a.1.2 = p.app T v.1.1 := pullbackAppEquiv_snd g.hom G.target.hom T v.1.1
            _ = q.app T v.1.2 := v.2
            _ = b.1.1 := (pullbackAppEquiv_fst G.source.hom g.hom T v.1.2).symm
        ⟨b.1.2, a.1.2, a.1.1, a.2,
          (congrArg (G.source.hom.app T) hmid).trans b.2⟩
      invFun := fun d => by
        let a := e₁.symm ⟨(d.targetLift, d.arrow), d.target_eq⟩
        let b := e₂.symm ⟨(d.arrow, d.sourceLift), d.source_eq⟩
        have h₁ : p.app T a = d.arrow := by
          have hh := pullbackAppEquiv_snd g.hom G.target.hom T a
          simpa [a, e₁] using hh.symm
        have h₂ : q.app T b = d.arrow := by
          have hh := pullbackAppEquiv_fst G.source.hom g.hom T b
          simpa [b, e₂] using hh.symm
        exact e₀.symm ⟨(a, b), h₁.trans h₂.symm⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro z
    let v := e₀ z
    let a := e₁ v.1.1
    let b := e₂ v.1.2
    have hmid : a.1.2 = b.1.1 := by
      calc
        a.1.2 = p.app T v.1.1 := pullbackAppEquiv_snd g.hom G.target.hom T v.1.1
        _ = q.app T v.1.2 := v.2
        _ = b.1.1 := (pullbackAppEquiv_fst G.source.hom g.hom T v.1.2).symm
    apply e₀.injective
    simp only [Equiv.apply_symm_apply]
    apply Subtype.ext
    apply Prod.ext
    · apply e₁.injective
      simp only [Equiv.apply_symm_apply]
    · apply e₂.injective
      simp only [Equiv.apply_symm_apply]
      apply Subtype.ext
      exact Prod.ext hmid rfl
  · intro d
    cases d
    simp [e₀, e₁, e₂]

/-- The source lift of `restrictionArrowDataEquiv` is the source map of the restriction. -/
public theorem restrictionArrowDataEquiv_source
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (T : (BigFppfOver C S hS)ᵒᵖ) (z : (restrictionArrows G g).obj.obj T) :
    (restrictionArrowDataEquiv G g T z).sourceLift =
      (restrictionSource G g).hom.app T z := by
  let p := pullback.snd g.hom G.target.hom
  let q := pullback.fst G.source.hom g.hom
  let e₀ := pullbackAppEquiv p q T
  let e₂ := pullbackAppEquiv G.source.hom g.hom T
  have h₀ := pullbackAppEquiv_snd p q T z
  have h₂ := pullbackAppEquiv_snd G.source.hom g.hom T ((pullback.snd p q).app T z)
  rw [← h₀] at h₂
  unfold restrictionArrowDataEquiv
  calc
    (e₂ ((e₀ z).1.2)).1.2 =
        (pullback.snd G.source.hom g.hom).app T ((e₀ z).1.2) := h₂
    _ = (pullback.snd G.source.hom g.hom).app T ((pullback.snd p q).app T z) :=
      congrArg (fun r => (pullback.snd G.source.hom g.hom).app T r) h₀
    _ = (restrictionSource G g).hom.app T z := rfl

/-- The target lift of `restrictionArrowDataEquiv` is the target map of the restriction. -/
public theorem restrictionArrowDataEquiv_target
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (T : (BigFppfOver C S hS)ᵒᵖ) (z : (restrictionArrows G g).obj.obj T) :
    (restrictionArrowDataEquiv G g T z).targetLift =
      (restrictionTarget G g).hom.app T z := by
  let p := pullback.snd g.hom G.target.hom
  let q := pullback.fst G.source.hom g.hom
  let e₀ := pullbackAppEquiv p q T
  let e₁ := pullbackAppEquiv g.hom G.target.hom T
  have h₀ := pullbackAppEquiv_fst p q T z
  have h₁ := pullbackAppEquiv_fst g.hom G.target.hom T ((pullback.fst p q).app T z)
  rw [← h₀] at h₁
  unfold restrictionArrowDataEquiv
  calc
    (e₁ ((e₀ z).1.1)).1.1 =
        (pullback.fst g.hom G.target.hom).app T ((e₀ z).1.1) := h₁
    _ = (pullback.fst g.hom G.target.hom).app T ((pullback.fst p q).app T z) :=
      congrArg (fun r => (pullback.fst g.hom G.target.hom).app T r) h₀
    _ = (restrictionTarget G g).hom.app T z := rfl

/-- The arrow of `restrictionArrowDataEquiv` is the canonical map to the original arrows. -/
public theorem restrictionArrowDataEquiv_arrow
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (T : (BigFppfOver C S hS)ᵒᵖ) (z : (restrictionArrows G g).obj.obj T) :
    (restrictionArrowDataEquiv G g T z).arrow =
      (restrictionArrowsToArrows G g).hom.app T z := by
  let p := pullback.snd g.hom G.target.hom
  let q := pullback.fst G.source.hom g.hom
  let e₀ := pullbackAppEquiv p q T
  let e₁ := pullbackAppEquiv g.hom G.target.hom T
  have h₀ := pullbackAppEquiv_fst p q T z
  have h₁ := pullbackAppEquiv_snd g.hom G.target.hom T
    ((pullback.fst p q).app T z)
  unfold restrictionArrowDataEquiv
  show (e₁ ((e₀ z).1.1)).1.2 = _
  calc
    _ = (pullback.snd g.hom G.target.hom).app T
        ((pullback.fst p q).app T z) := by
      conv_lhs => rw [h₀]
      exact h₁
    _ = (restrictionArrowsToArrows G g).hom.app T z := rfl

/-- The arrows of the evaluated groupoid of `G` between the images of two sections of `U'` are
precisely the sections of the restricted arrow space having those two sections as source and
target.  This is pointwise full faithfulness of the canonical morphism, in equivalence form. -/
public noncomputable def restrictionHomEquiv
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (T : (BigFppfOver C S hS)ᵒᵖ) (x y : U'.obj.obj T) :
    @Quiver.Hom (G.objects.obj.obj T)
      (G.toGroupoidInFunctors.evaluationGroupoid T).toCategory.toQuiver
      (g.hom.app T x) (g.hom.app T y) ≃
      {z : (restrictionArrows G g).obj.obj T //
        (restrictionSource G g).hom.app T z = x ∧
        (restrictionTarget G g).hom.app T z = y} := by
  letI : Groupoid (G.objects.obj.obj T) :=
    G.toGroupoidInFunctors.evaluationGroupoid T
  let q := (G.toGroupoidInFunctors.evaluationArrowEquiv T
    (g.hom.app T x) (g.hom.app T y))
  let e := restrictionArrowDataEquiv G g T
  refine {
    toFun := fun f => by
      let a := q f
      let d : RestrictionArrowData G g T :=
        ⟨x, a.1, y, a.2.2.symm, a.2.1⟩
      refine ⟨e.symm d, ?_⟩
      constructor
      · rw [← restrictionArrowDataEquiv_source]
        simp [d, e, GroupoidInAlgebraicSpaces.toGroupoidInFunctors]
      · rw [← restrictionArrowDataEquiv_target]
        simp [d, e, GroupoidInAlgebraicSpaces.toGroupoidInFunctors]
    invFun := fun z => by
      let d := e z.1
      have hx : d.sourceLift = x :=
        (restrictionArrowDataEquiv_source G g T z.1).trans z.2.1
      have hy : d.targetLift = y :=
        (restrictionArrowDataEquiv_target G g T z.1).trans z.2.2
      exact q.symm ⟨d.arrow,
        d.source_eq.trans (congrArg (g.hom.app T) hx),
        d.target_eq.symm.trans (congrArg (g.hom.app T) hy)⟩
    left_inv := by
      intro f
      apply q.injective
      dsimp only
      simp only [Equiv.apply_symm_apply]
    right_inv := by
      intro z
      apply Subtype.ext
      apply e.injective
      let d := e z.1
      have hx : d.sourceLift = x :=
        (restrictionArrowDataEquiv_source G g T z.1).trans z.2.1
      have hy : d.targetLift = y :=
        (restrictionArrowDataEquiv_target G g T z.1).trans z.2.2
      let hs' := d.source_eq.trans (congrArg (g.hom.app T) hx)
      let ht' := d.target_eq.symm.trans (congrArg (g.hom.app T) hy)
      have ha : (q (q.symm ⟨d.arrow, hs', ht'⟩)).1 = d.arrow :=
        congrArg Subtype.val (q.apply_symm_apply ⟨d.arrow, hs', ht'⟩)
      let d' : RestrictionArrowData G g T :=
        ⟨x, (q (q.symm ⟨d.arrow, hs', ht'⟩)).1, y,
          (q (q.symm ⟨d.arrow, hs', ht'⟩)).2.2.symm,
          (q (q.symm ⟨d.arrow, hs', ht'⟩)).2.1⟩
      have hd : d' = d := RestrictionArrowData.ext hx.symm ha hy.symm
      calc
        e (e.symm d') = d' := e.apply_symm_apply d'
        _ = e z.1 := by simpa [d] using hd }


/-- The composition law of a restriction, together with the composite arrow of `G` underlying
it and the three identities pinning both down. -/
public structure RestrictionCompositionData
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) where
  /-- The composition law on the arrow space of the restriction. -/
  hom : AlgebraicSpaces.fiberProduct C S hS (restrictionSource G g)
      (restrictionTarget G g) ⟶ restrictionArrows G g
  /-- The composite arrow of `G` underlying `hom`. -/
  underlying : AlgebraicSpaces.fiberProduct C S hS (restrictionSource G g)
      (restrictionTarget G g) ⟶ G.arrows
  hom_comp : hom ≫ restrictionArrowsToArrows G g = underlying
  hom_source : hom ≫ restrictionSource G g =
    fiberProductSnd (restrictionSource G g) (restrictionTarget G g) ≫
      restrictionSource G g
  hom_target : hom ≫ restrictionTarget G g =
    fiberProductFst (restrictionSource G g) (restrictionTarget G g) ≫
      restrictionTarget G g

/-- The composition law of a restriction exists: compose the two underlying arrows in `G` and
lift the result along the two fibre-product squares defining the restricted arrow space. -/
public noncomputable def restrictionCompositionData
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    RestrictionCompositionData G g := by
  let p := fiberProductSnd g G.target
  let q := fiberProductFst G.source g
  let af := fiberProductFst (restrictionSource G g) (restrictionTarget G g)
  let as := fiberProductSnd (restrictionSource G g) (restrictionTarget G g)
  let ar := restrictionArrowsToArrows G g
  let c₀ : (AlgebraicSpaces.fiberProduct C S hS (restrictionSource G g)
      (restrictionTarget G g)).obj ⟶ G.arrows.obj := {
    app := fun T => ↾ fun z => G.toGroupoidInFunctors.comp.app T
      ⟨(ar.hom.app T (af.hom.app T z), ar.hom.app T (as.hom.app T z)), (by
        calc
          G.source.hom.app T (ar.hom.app T (af.hom.app T z)) =
              g.hom.app T ((restrictionSource G g).hom.app T (af.hom.app T z)) := by
            exact congrArg (fun f => f.hom.app T (af.hom.app T z))
              (restriction_condition G g).symm
          _ = g.hom.app T ((restrictionTarget G g).hom.app T (as.hom.app T z)) := by
            have h := pullback_condition_app (restrictionSource G g).hom
              (restrictionTarget G g).hom T z
            exact congrArg (g.hom.app T) h
          _ = G.target.hom.app T (ar.hom.app T (as.hom.app T z)) := by
            exact (congrArg (fun f => f.hom.app T (as.hom.app T z))
              (restriction_condition' G g)).symm)⟩,
    naturality := by
      intro X Y f
      ext z
      let aX := ar.hom.app X (af.hom.app X z)
      let bX := ar.hom.app X (as.hom.app X z)
      let hX : G.source.hom.app X aX = G.target.hom.app X bX := by
        calc
          G.source.hom.app X aX =
              g.hom.app X ((restrictionSource G g).hom.app X (af.hom.app X z)) := by
            exact congrArg (fun f => f.hom.app X (af.hom.app X z))
              (restriction_condition G g).symm
          _ = g.hom.app X ((restrictionTarget G g).hom.app X (as.hom.app X z)) := by
            have hh := pullback_condition_app (restrictionSource G g).hom
              (restrictionTarget G g).hom X z
            exact congrArg (g.hom.app X) hh
          _ = G.target.hom.app X bX := by
            exact (congrArg (fun f => f.hom.app X (as.hom.app X z))
              (restriction_condition' G g)).symm
      let pX : (Deformation.composableArrows G.objects.obj G.arrows.obj
          G.source.hom G.target.hom).obj X := ⟨(aX, bX), hX⟩
      let aY := ar.hom.app Y (af.hom.app Y
        ((AlgebraicSpaces.fiberProduct C S hS (restrictionSource G g)
          (restrictionTarget G g)).obj.map f z))
      let bY := ar.hom.app Y (as.hom.app Y
        ((AlgebraicSpaces.fiberProduct C S hS (restrictionSource G g)
          (restrictionTarget G g)).obj.map f z))
      let hY : G.source.hom.app Y aY = G.target.hom.app Y bY := by
        calc
          G.source.hom.app Y aY = G.source.hom.app Y (G.arrows.obj.map f aX) := by
            dsimp [aY, aX]
            simp [NatTrans.naturality_apply]
          _ = G.target.hom.app Y (G.arrows.obj.map f bX) := by
            rw [NatTrans.naturality_apply G.source.hom f aX,
              NatTrans.naturality_apply G.target.hom f bX, hX]
          _ = G.target.hom.app Y bY := by
            dsimp [bY, bX]
            simp [NatTrans.naturality_apply]
      let pY : (Deformation.composableArrows G.objects.obj G.arrows.obj
          G.source.hom G.target.hom).obj Y := ⟨(aY, bY), hY⟩
      have hp : pY = (Deformation.composableArrows G.objects.obj G.arrows.obj
          G.source.hom G.target.hom).map f pX := by
        apply Subtype.ext
        change (aY, bY) = (G.arrows.obj.map f aX, G.arrows.obj.map f bX)
        apply Prod.ext
        · dsimp [aY, aX]
          simp [NatTrans.naturality_apply]
        · dsimp [bY, bX]
          simp [NatTrans.naturality_apply]
      have hn := NatTrans.naturality_apply G.toGroupoidInFunctors.comp f pX
      change G.toGroupoidInFunctors.comp.app Y pY =
        G.arrows.obj.map f (G.toGroupoidInFunctors.comp.app X pX)
      rw [hp]
      exact hn }
  let c : AlgebraicSpaces.fiberProduct C S hS (restrictionSource G g)
      (restrictionTarget G g) ⟶ G.arrows := ObjectProperty.homMk c₀
  have hc_target : c ≫ G.target = af ≫ ar ≫ G.target := by
    apply ObjectProperty.hom_ext
    ext T z
    exact functorGroupoid_comp_target G.toGroupoidInFunctors T
      (ar.hom.app T (af.hom.app T z)) (ar.hom.app T (as.hom.app T z)) (by
        calc
          G.source.hom.app T (ar.hom.app T (af.hom.app T z)) =
              g.hom.app T ((restrictionSource G g).hom.app T (af.hom.app T z)) := by
            exact congrArg (fun f => f.hom.app T (af.hom.app T z))
              (restriction_condition G g).symm
          _ = g.hom.app T ((restrictionTarget G g).hom.app T (as.hom.app T z)) := by
            have h := pullback_condition_app (restrictionSource G g).hom
              (restrictionTarget G g).hom T z
            exact congrArg (g.hom.app T) h
          _ = G.target.hom.app T (ar.hom.app T (as.hom.app T z)) := by
            exact (congrArg (fun f => f.hom.app T (as.hom.app T z))
              (restriction_condition' G g)).symm)
  have hc_source : c ≫ G.source = as ≫ ar ≫ G.source := by
    apply ObjectProperty.hom_ext
    ext T z
    exact functorGroupoid_comp_source G.toGroupoidInFunctors T
      (ar.hom.app T (af.hom.app T z)) (ar.hom.app T (as.hom.app T z)) (by
        calc
          G.source.hom.app T (ar.hom.app T (af.hom.app T z)) =
              g.hom.app T ((restrictionSource G g).hom.app T (af.hom.app T z)) := by
            exact congrArg (fun f => f.hom.app T (af.hom.app T z))
              (restriction_condition G g).symm
          _ = g.hom.app T ((restrictionTarget G g).hom.app T (as.hom.app T z)) := by
            have h := pullback_condition_app (restrictionSource G g).hom
              (restrictionTarget G g).hom T z
            exact congrArg (g.hom.app T) h
          _ = G.target.hom.app T (ar.hom.app T (as.hom.app T z)) := by
            exact (congrArg (fun f => f.hom.app T (as.hom.app T z))
              (restriction_condition' G g)).symm)
  let hp := (AlgebraicSpaces.isPullback_fiberProduct C S hS g G.target).lift
    (af ≫ restrictionTarget G g) c (by
      calc
        (af ≫ restrictionTarget G g) ≫ g = af ≫ ar ≫ G.target := by
          simp only [Category.assoc]
          exact congrArg (af ≫ ·) (restriction_condition' G g).symm
        _ = c ≫ G.target := hc_target.symm)
  let hq := (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source g).lift
    c (as ≫ restrictionSource G g) (by
      calc
        c ≫ G.source = as ≫ ar ≫ G.source := hc_source
        _ = (as ≫ restrictionSource G g) ≫ g := by
          simp only [Category.assoc]
          exact congrArg (as ≫ ·) (restriction_condition G g).symm)
  let m := (AlgebraicSpaces.isPullback_fiberProduct C S hS p q).lift hp hq (by
    calc
      hp ≫ p = c := by
        dsimp [hp, p]
        exact (AlgebraicSpaces.isPullback_fiberProduct C S hS g G.target).lift_snd _ _ _
      _ = hq ≫ q := by
        dsimp [hq, q]
        exact ((AlgebraicSpaces.isPullback_fiberProduct C S hS G.source g).lift_fst _ _ _).symm)
  refine ⟨m, c, ?_, ?_, ?_⟩
  · calc
      m ≫ restrictionArrowsToArrows G g = m ≫ fiberProductFst p q ≫ p := rfl
      _ = hp ≫ p :=
        congrArg (fun k => k ≫ p)
          ((AlgebraicSpaces.isPullback_fiberProduct C S hS p q).lift_fst _ _ _)
      _ = c := by
        dsimp [hp, p]
        exact (AlgebraicSpaces.isPullback_fiberProduct C S hS g G.target).lift_snd _ _ _
  · calc
      m ≫ restrictionSource G g =
          m ≫ fiberProductSnd p q ≫ fiberProductSnd G.source g := rfl
      _ = hq ≫ fiberProductSnd G.source g :=
        congrArg (fun k => k ≫ fiberProductSnd G.source g)
          ((AlgebraicSpaces.isPullback_fiberProduct C S hS p q).lift_snd _ _ _)
      _ = fiberProductSnd (restrictionSource G g) (restrictionTarget G g) ≫
          restrictionSource G g := by
        dsimp [hq, q, restrictionSource, restrictionArrows]
        exact (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source g).lift_snd _ _ _
  · calc
      m ≫ restrictionTarget G g =
          m ≫ fiberProductFst p q ≫ fiberProductFst g G.target := rfl
      _ = hp ≫ fiberProductFst g G.target :=
        congrArg (fun k => k ≫ fiberProductFst g G.target)
          ((AlgebraicSpaces.isPullback_fiberProduct C S hS p q).lift_fst _ _ _)
      _ = fiberProductFst (restrictionSource G g) (restrictionTarget G g) ≫
          restrictionTarget G g := by
        dsimp [hp, p, restrictionTarget, restrictionArrows]
        exact (AlgebraicSpaces.isPullback_fiberProduct C S hS g G.target).lift_fst _ _ _

/-- The composition law of a restriction. -/
public noncomputable def restrictionComp
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    AlgebraicSpaces.fiberProduct C S hS (restrictionSource G g) (restrictionTarget G g) ⟶
      restrictionArrows G g := (restrictionCompositionData G g).hom

/-- Evaluating an equality of composites of morphisms of algebraic spaces at a section. -/
private theorem hom_app_app_of_comp_eq
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {X Y Z : AlgebraicSpaces C S hS} {f : X ⟶ Y} {g : Y ⟶ Z} {h : X ⟶ Z}
    (e : f ≫ g = h) (T : (BigFppfOver C S hS)ᵒᵖ) (z : X.obj.obj T) :
    g.hom.app T (f.hom.app T z) = h.hom.app T z := by
  simpa [CategoryTheory.hom_comp, NatTrans.comp_app] using congrArg (fun f => f.hom.app T z) e

/-- The source of a composite section of the restricted arrow space is the source of the
section composed first. -/
public theorem restrictionCompositionData_hom_source_app
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (z : (AlgebraicSpaces.fiberProduct C S hS (restrictionSource G g)
      (restrictionTarget G g)).obj.obj T) :
    (restrictionSource G g).hom.app T
        ((restrictionCompositionData G g).hom.hom.app T z) =
      (restrictionSource G g).hom.app T
        ((fiberProductSnd (restrictionSource G g) (restrictionTarget G g)).hom.app T z) := by
  exact hom_app_app_of_comp_eq (restrictionCompositionData G g).hom_source T z

/-- The target of a composite section of the restricted arrow space is the target of the
section composed last. -/
public theorem restrictionCompositionData_hom_target_app
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (z : (AlgebraicSpaces.fiberProduct C S hS (restrictionSource G g)
      (restrictionTarget G g)).obj.obj T) :
    (restrictionTarget G g).hom.app T
        ((restrictionCompositionData G g).hom.hom.app T z) =
      (restrictionTarget G g).hom.app T
        ((fiberProductFst (restrictionSource G g) (restrictionTarget G g)).hom.app T z) := by
  exact hom_app_app_of_comp_eq (restrictionCompositionData G g).hom_target T z

/-- The arrow of `G` underlying a composite section of the restricted arrow space. -/
public theorem restrictionCompositionData_hom_arrow_app
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (z : (AlgebraicSpaces.fiberProduct C S hS (restrictionSource G g)
      (restrictionTarget G g)).obj.obj T) :
    (restrictionArrowsToArrows G g).hom.app T
        ((restrictionCompositionData G g).hom.hom.app T z) =
      (restrictionCompositionData G g).underlying.hom.app T z := by
  exact hom_app_app_of_comp_eq (restrictionCompositionData G g).hom_comp T z

/-- That underlying arrow is the composite in `G` of the two underlying arrows. -/
public theorem restrictionCompositionData_underlying_comp_app
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (z : (AlgebraicSpaces.fiberProduct C S hS (restrictionSource G g)
      (restrictionTarget G g)).obj.obj T) :
    (restrictionCompositionData G g).underlying.hom.app T z =
      G.toGroupoidInFunctors.comp.app T
        ⟨((restrictionArrowsToArrows G g).hom.app T
            ((fiberProductFst (restrictionSource G g) (restrictionTarget G g)).hom.app T z),
          (restrictionArrowsToArrows G g).hom.app T
            ((fiberProductSnd (restrictionSource G g) (restrictionTarget G g)).hom.app T z)), by
          calc
            G.source.hom.app T ((restrictionArrowsToArrows G g).hom.app T
                ((fiberProductFst (restrictionSource G g) (restrictionTarget G g)).hom.app T z)) =
                g.hom.app T ((restrictionSource G g).hom.app T
                  ((fiberProductFst (restrictionSource G g)
                    (restrictionTarget G g)).hom.app T z)) := by
              exact congrArg (fun f => f.hom.app T
                ((fiberProductFst (restrictionSource G g) (restrictionTarget G g)).hom.app T z))
                (restriction_condition G g).symm
            _ = g.hom.app T ((restrictionTarget G g).hom.app T
                ((fiberProductSnd (restrictionSource G g)
                  (restrictionTarget G g)).hom.app T z)) := by
              congr 1
              exact pullback_condition_app (restrictionSource G g).hom
                (restrictionTarget G g).hom T z
            _ = G.target.hom.app T ((restrictionArrowsToArrows G g).hom.app T
                ((fiberProductSnd (restrictionSource G g)
                  (restrictionTarget G g)).hom.app T z)) := by
              exact (congrArg (fun f => f.hom.app T
                ((fiberProductSnd (restrictionSource G g) (restrictionTarget G g)).hom.app T z))
                (restriction_condition' G g)).symm⟩ := by
  rfl

/-- The composition law of a restriction, at the shape the `comp` field of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces` expects. -/
public noncomputable abbrev restrictionCompForGroupoid
    {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
    {B : AlgebraicSpaces C S hS}
    (G : GroupoidInAlgebraicSpaces C S hS B)
    {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects) :
    AlgebraicSpaces.fiberProduct C S hS (restrictionSource G g) (restrictionTarget G g) ⟶
      restrictionArrows G g := restrictionComp G g

end GroupoidInAlgebraicSpaces

end AlgebraicGeometry

end
