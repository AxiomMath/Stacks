module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.MorphismProperty.Limits
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.LimitFPObjectDescent.Approximation
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.ClosedImmersionDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian

/-!
# Relative approximation of a scheme over a base

A quasi-compact and quasi-separated scheme over a quasi-separated base is a directed inverse limit
of quasi-compact and quasi-separated schemes of finite presentation over that base, with affine
transition morphisms over the base.

## Main results

* `AlgebraicGeometry.exists_isLimit_finitePresentation` gives the relative approximation by
  schemes of finite presentation.

## Implementation notes

The approximating schemes form a functor indexed by the opposite of a directed preorder; their
structure morphisms to the base form a natural transformation to the constant diagram, so every
transition morphism lies over the base, and the displayed equation identifies the structure
morphism induced on the limit with the given morphism. The approximating schemes are quasi-compact
and quasi-separated because the construction first restricts the base to a quasi-compact open
containing the image of the given morphism.

The index preorder lies in the universe of the schemes, so finite-stage descent applies to this
approximation.

## References

* [Stacks Project, Tag 09MV](https://stacks.math.columbia.edu/tag/09MV)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

section RelativeApproximationHelpers

universe v

private def relativeBaseMap {I : Type v} [Category I] {X B : Scheme.{u}}
    {D : I ⥤ Arrow Scheme.{u}} (f : X ⟶ B) (c : Cone D)
    (e : c.pt ≅ Arrow.mk f) (i : I) : B ⟶ (D.obj i).right :=
  (e.inv ≫ c.π.app i).right

private theorem relativeBaseMap_apply {I : Type v} [Category I] {X B : Scheme.{u}}
    {D : I ⥤ Arrow Scheme.{u}} (f : X ⟶ B) (c : Cone D)
    (e : c.pt ≅ Arrow.mk f) (i : I) :
    relativeBaseMap f c e i = e.inv.right ≫ (c.π.app i).right := by
  simp [relativeBaseMap]

private theorem relativeBaseMap_natural {I : Type v} [Category I] {X B : Scheme.{u}}
    {D : I ⥤ Arrow Scheme.{u}} (f : X ⟶ B) (c : Cone D)
    (e : c.pt ≅ Arrow.mk f) {i j : I} (a : i ⟶ j) :
    relativeBaseMap f c e i ≫ (D.map a).right = relativeBaseMap f c e j := by
  change (e.inv ≫ c.π.app i).right ≫ (D.map a).right =
    (e.inv ≫ c.π.app j).right
  rw [← Arrow.comp_right, Category.assoc, c.w a]

private noncomputable def relativePullbackTransition {I : Type v} [Category I]
    {D : I ⥤ Arrow Scheme.{u}} {B : Scheme.{u}}
    (q : ∀ i, B ⟶ (D.obj i).right)
    (hq : ∀ {i j} (a : i ⟶ j), q i ≫ (D.map a).right = q j)
    {i j : I} (a : i ⟶ j) :
    pullback (D.obj i).hom (q i) ⟶ pullback (D.obj j).hom (q j) :=
  pullback.map (D.obj i).hom (q i) (D.obj j).hom (q j)
    (D.map a).left (𝟙 _) (D.map a).right (by
      simp) (by simpa using hq a)

private theorem relativePullbackTransition_fst {I : Type v} [Category I]
    {D : I ⥤ Arrow Scheme.{u}} {B : Scheme.{u}}
    (q : ∀ i, B ⟶ (D.obj i).right)
    (hq : ∀ {i j} (a : i ⟶ j), q i ≫ (D.map a).right = q j)
    {i j : I} (a : i ⟶ j) :
    relativePullbackTransition q hq a ≫ pullback.fst (D.obj j).hom (q j) =
      pullback.fst (D.obj i).hom (q i) ≫ (D.map a).left := by
  simp only [relativePullbackTransition, pullback.map, pullback.lift_fst]

private theorem relativePullbackTransition_snd {I : Type v} [Category I]
    {D : I ⥤ Arrow Scheme.{u}} {B : Scheme.{u}}
    (q : ∀ i, B ⟶ (D.obj i).right)
    (hq : ∀ {i j} (a : i ⟶ j), q i ≫ (D.map a).right = q j)
    {i j : I} (a : i ⟶ j) :
    relativePullbackTransition q hq a ≫ pullback.snd (D.obj j).hom (q j) =
      pullback.snd (D.obj i).hom (q i) := by
  simp only [relativePullbackTransition, pullback.map, pullback.lift_snd,
    Category.comp_id]

private theorem relativePullbackTransition_isAffineHom {I : Type v} [Category I]
    {D : I ⥤ Arrow Scheme.{u}} {B : Scheme.{u}}
    (q : ∀ i, B ⟶ (D.obj i).right)
    (hq : ∀ {i j} (a : i ⟶ j), q i ≫ (D.map a).right = q j)
    {i j : I} (a : i ⟶ j)
    (hleft : IsAffineHom (D.map a).left)
    (hright : IsAffineHom (D.map a).right) :
    IsAffineHom (relativePullbackTransition q hq a) := by
  classical
  let fi := (D.obj i).hom
  let fj := (D.obj j).hom
  let r := (D.map a).right
  let l := (D.map a).left
  let qi := q i
  let qj := q j
  have hsq : fi ≫ r = l ≫ fj := (D.map a).w.symm
  have hqij : qi ≫ r = qj := hq a
  let m₁ : pullback fi qi ⟶ pullback (fi ≫ r) (qi ≫ r) :=
    pullback.mapDesc fi qi r
  let iso₁ : pullback (fi ≫ r) (qi ≫ r) ≅ pullback (l ≫ fj) qj :=
    pullback.congrHom hsq hqij
  let iso₂ : pullback (l ≫ fj) qj ≅ pullback qj (l ≫ fj) :=
    pullbackSymmetry (l ≫ fj) qj
  let iso₃ : pullback qj (l ≫ fj) ≅ pullback (pullback.snd qj fj) l :=
    (pullbackLeftPullbackSndIso qj fj l).symm
  let iso : pullback (fi ≫ r) (qi ≫ r) ≅ pullback (pullback.snd qj fj) l :=
    iso₁ ≪≫ iso₂ ≪≫ iso₃
  let m₂base : pullback (pullback.snd qj fj) l ⟶ pullback fj qj :=
    pullback.fst (pullback.snd qj fj) l ≫ (pullbackSymmetry fj qj).inv
  let m₂map : pullback (fi ≫ r) (qi ≫ r) ⟶ pullback fj qj :=
    pullback.map (fi ≫ r) (qi ≫ r) fj qj l (𝟙 B) (𝟙 (D.obj j).right)
      (by simpa using hsq) (by simpa using hqij)
  have hm₁ : IsAffineHom m₁ := by
    have : IsAffineHom r := hright
    have : IsSeparated r := IsSeparated.of_isAffineHom r
    have : IsClosedImmersion m₁ := inferInstance
    infer_instance
  have hm₂base : IsAffineHom m₂base := by
    have : MorphismProperty.IsStableUnderBaseChangeAlong
        (P := @IsAffineHom) (pullback.snd qj fj) := {
      of_isPullback := fun pb hp =>
        (show MorphismProperty.IsStableUnderBaseChange @IsAffineHom
          from inferInstance).of_isPullback pb hp }
    have : IsAffineHom (pullback.fst (pullback.snd qj fj) l) :=
      MorphismProperty.pullback_fst (pullback.snd qj fj) l hleft
    infer_instance
  have h₂eq : m₂map = iso.hom ≫ m₂base := by
    apply pullback.hom_ext <;>
      simp [m₂map, m₂base, iso, iso₁, iso₂, iso₃, pullback.map, pullback.congrHom,
        Category.assoc]
  have hfactor : m₁ ≫ m₂map = relativePullbackTransition q hq a := by
    apply pullback.hom_ext
    · simp only [pullback.mapDesc, pullback.map, Category.comp_id, Category.assoc,
        pullback.lift_fst, pullback.lift_fst_assoc, relativePullbackTransition, m₁, m₂map]
      rw [pullback.lift_fst]
    · simp only [pullback.mapDesc, pullback.map, Category.comp_id, Category.assoc,
        pullback.lift_snd, relativePullbackTransition, m₁, m₂map]
      rw [pullback.lift_snd]
  rw [← hfactor, h₂eq]
  infer_instance

private noncomputable def relativePullbackSystem {I : Type v} [Category I]
    {X B : Scheme.{u}} {D : I ⥤ Arrow Scheme.{u}}
    (f : X ⟶ B) (c : Cone D) (e : c.pt ≅ Arrow.mk f) : I ⥤ Scheme.{u} :=
  { obj i := pullback (D.obj i).hom (relativeBaseMap f c e i)
    map := fun {i j} a => relativePullbackTransition
      (relativeBaseMap f c e) (relativeBaseMap_natural f c e) a
    map_id := by
      intro i
      simp [relativePullbackTransition]
    map_comp := by
      intro i j k a b
      change relativePullbackTransition (relativeBaseMap f c e)
        (relativeBaseMap_natural f c e) (a ≫ b) =
          relativePullbackTransition (relativeBaseMap f c e)
            (relativeBaseMap_natural f c e) a ≫
          relativePullbackTransition (relativeBaseMap f c e)
            (relativeBaseMap_natural f c e) b
      dsimp only [relativePullbackTransition]
      rw [pullback.map_comp]
      congr 1 <;> simp [Functor.map_comp] }

private noncomputable def relativePullbackLimitMap {I : Type v} [Category I]
    {X B : Scheme.{u}} {D : I ⥤ Arrow Scheme.{u}}
    (f : X ⟶ B) (c : Cone D) (e : c.pt ≅ Arrow.mk f) (i : I) :
    X ⟶ pullback (D.obj i).hom (relativeBaseMap f c e i) :=
  pullback.lift (e.inv.left ≫ (c.π.app i).left) f (by
      calc
        (e.inv.left ≫ (c.π.app i).left) ≫ (D.obj i).hom =
            e.inv.left ≫ c.pt.hom ≫ (c.π.app i).right := by
              rw [Category.assoc, (c.π.app i).w]
              simp only [Functor.const_obj_obj]
        _ = f ≫ e.inv.right ≫ (c.π.app i).right := by
              rw [← Category.assoc, e.inv.w, Category.assoc]
              simp
        _ = f ≫ relativeBaseMap f c e i := by
              rw [relativeBaseMap_apply])

private theorem relativePullbackLimitMap_fst {I : Type v} [Category I]
    {X B : Scheme.{u}} {D : I ⥤ Arrow Scheme.{u}}
    (f : X ⟶ B) (c : Cone D) (e : c.pt ≅ Arrow.mk f) (i : I) :
    relativePullbackLimitMap f c e i ≫
      pullback.fst (D.obj i).hom (relativeBaseMap f c e i) =
      e.inv.left ≫ (c.π.app i).left :=
  pullback.lift_fst _ _ _

private theorem relativePullbackLimitMap_snd {I : Type v} [Category I]
    {X B : Scheme.{u}} {D : I ⥤ Arrow Scheme.{u}}
    (f : X ⟶ B) (c : Cone D) (e : c.pt ≅ Arrow.mk f) (i : I) :
    relativePullbackLimitMap f c e i ≫
      pullback.snd (D.obj i).hom (relativeBaseMap f c e i) = f :=
  pullback.lift_snd _ _ _

private noncomputable def relativePullbackLimitCone {I : Type v} [Category I]
    {X B : Scheme.{u}} {D : I ⥤ Arrow Scheme.{u}}
    (f : X ⟶ B) (c : Cone D) (e : c.pt ≅ Arrow.mk f) :
    Cone (relativePullbackSystem f c e) := by
  refine Cone.mk X {
    app := fun i => relativePullbackLimitMap f c e i
    naturality := by
      intro i j a
      apply pullback.hom_ext
      · change relativePullbackLimitMap f c e j ≫
            pullback.fst (D.obj j).hom (relativeBaseMap f c e j) =
          relativePullbackLimitMap f c e i ≫
            relativePullbackTransition (relativeBaseMap f c e)
              (relativeBaseMap_natural f c e) a ≫
            pullback.fst (D.obj j).hom (relativeBaseMap f c e j)
        have hleft : (c.π.app i).left ≫ (D.map a).left = (c.π.app j).left := by
          simpa only [Arrow.comp_left] using congrArg Arrow.Hom.left (c.w a)
        rw [relativePullbackTransition_fst (relativeBaseMap f c e)
            (relativeBaseMap_natural f c e) a, ← Category.assoc, relativePullbackLimitMap_fst,
          relativePullbackLimitMap_fst, ← hleft, Category.assoc]
      · change relativePullbackLimitMap f c e j ≫
            pullback.snd (D.obj j).hom (relativeBaseMap f c e j) =
          relativePullbackLimitMap f c e i ≫
            relativePullbackTransition (relativeBaseMap f c e)
              (relativeBaseMap_natural f c e) a ≫
            pullback.snd (D.obj j).hom (relativeBaseMap f c e j)
        rw [relativePullbackTransition_snd (relativeBaseMap f c e)
            (relativeBaseMap_natural f c e) a, relativePullbackLimitMap_snd,
          relativePullbackLimitMap_snd] }

private theorem relativePullbackCone_snd_eq {J : Type v} [Preorder J]
    [IsDirectedOrder J] [Nonempty J] {X B : Scheme.{u}}
    {D : Jᵒᵖ ⥤ Arrow Scheme.{u}} (f : X ⟶ B) (c : Cone D)
    (e : c.pt ≅ Arrow.mk f) (s : Cone (relativePullbackSystem f c e))
    (i : Jᵒᵖ) :
    s.π.app i ≫ pullback.snd (D.obj i).hom (relativeBaseMap f c e i) =
      s.π.app (Opposite.op (Classical.choice ‹Nonempty J›)) ≫
        pullback.snd (D.obj (Opposite.op (Classical.choice ‹Nonempty J›))).hom
          (relativeBaseMap f c e (Opposite.op (Classical.choice ‹Nonempty J›))) := by
  classical
  let i₀ : J := Classical.choice ‹Nonempty J›
  obtain ⟨k, hk₀, hki⟩ := exists_ge_ge i₀ i.unop
  let a₀ : (Opposite.op k) ⟶ (Opposite.op i₀) := (homOfLE hk₀).op
  let aᵢ : (Opposite.op k) ⟶ i := (homOfLE hki).op
  have h {a b : Jᵒᵖ} (g : a ⟶ b) :
      s.π.app a ≫ pullback.snd (D.obj a).hom (relativeBaseMap f c e a) =
      s.π.app b ≫ pullback.snd (D.obj b).hom (relativeBaseMap f c e b) := by
    calc
      _ = s.π.app a ≫ ((relativePullbackSystem f c e).map g ≫
            pullback.snd (D.obj b).hom (relativeBaseMap f c e b)) := by
              congr 1
              exact (relativePullbackTransition_snd (relativeBaseMap f c e)
                (relativeBaseMap_natural f c e) g).symm
      _ = (s.π.app a ≫ (relativePullbackSystem f c e).map g) ≫
            pullback.snd (D.obj b).hom (relativeBaseMap f c e b) :=
              (Category.assoc _ _ _).symm
      _ = _ := by rw [s.w g]
  exact (h aᵢ).symm.trans (h a₀)

private noncomputable def relativePullbackConeBase {J : Type v} [Preorder J]
    [Nonempty J] {X B : Scheme.{u}} {D : Jᵒᵖ ⥤ Arrow Scheme.{u}}
    (f : X ⟶ B) (c : Cone D) (e : c.pt ≅ Arrow.mk f)
    (s : Cone (relativePullbackSystem f c e)) : s.pt ⟶ B :=
  s.π.app (Opposite.op (Classical.choice ‹Nonempty J›)) ≫
    pullback.snd (D.obj (Opposite.op (Classical.choice ‹Nonempty J›))).hom
      (relativeBaseMap f c e (Opposite.op (Classical.choice ‹Nonempty J›)))

private noncomputable def relativePullbackArrowCone {J : Type v} [Preorder J]
    [IsDirectedOrder J] [Nonempty J] {X B : Scheme.{u}}
    {D : Jᵒᵖ ⥤ Arrow Scheme.{u}} (f : X ⟶ B) (c : Cone D)
    (e : c.pt ≅ Arrow.mk f) (s : Cone (relativePullbackSystem f c e)) : Cone D := by
  classical
  let i₀ : J := Classical.choice ‹Nonempty J›
  let b : s.pt ⟶ B := s.π.app (Opposite.op i₀) ≫
    pullback.snd (D.obj (Opposite.op i₀)).hom
      (relativeBaseMap f c e (Opposite.op i₀))
  have hb (i : Jᵒᵖ) : s.π.app i ≫
      pullback.snd (D.obj i).hom (relativeBaseMap f c e i) = b :=
    relativePullbackCone_snd_eq f c e s i
  refine Cone.mk (Arrow.mk b) {
    app := fun i => Arrow.homMk
      (s.π.app i ≫ pullback.fst (D.obj i).hom (relativeBaseMap f c e i))
      (relativeBaseMap f c e i) (by
        calc
          (s.π.app i ≫ pullback.fst (D.obj i).hom
            (relativeBaseMap f c e i)) ≫ (D.obj i).hom =
              s.π.app i ≫ (pullback.fst (D.obj i).hom
                (relativeBaseMap f c e i) ≫ (D.obj i).hom) :=
                  Category.assoc _ _ _
          _ = s.π.app i ≫ (pullback.snd (D.obj i).hom
                (relativeBaseMap f c e i) ≫ relativeBaseMap f c e i) :=
                  congrArg (fun z => s.π.app i ≫ z) pullback.condition
          _ = (s.π.app i ≫ pullback.snd (D.obj i).hom
                (relativeBaseMap f c e i)) ≫ relativeBaseMap f c e i :=
                  (Category.assoc _ _ _).symm
          _ = b ≫ relativeBaseMap f c e i := by rw [hb i])
    naturality := by
      intro i j a
      apply Arrow.hom_ext
      · change s.π.app j ≫ pullback.fst (D.obj j).hom
          (relativeBaseMap f c e j) =
          (s.π.app i ≫ pullback.fst (D.obj i).hom
            (relativeBaseMap f c e i)) ≫ (D.map a).left
        have hnat : s.π.app i ≫ (relativePullbackSystem f c e).map a =
            s.π.app j := s.w a
        have hfst : (relativePullbackSystem f c e).map a ≫
            pullback.fst (D.obj j).hom (relativeBaseMap f c e j) =
            pullback.fst (D.obj i).hom (relativeBaseMap f c e i) ≫ (D.map a).left := by
          change relativePullbackTransition (relativeBaseMap f c e)
            (relativeBaseMap_natural f c e) a ≫ _ = _
          exact relativePullbackTransition_fst (relativeBaseMap f c e)
            (relativeBaseMap_natural f c e) a
        calc
          s.π.app j ≫ pullback.fst (D.obj j).hom
              (relativeBaseMap f c e j) =
              (s.π.app i ≫ (relativePullbackSystem f c e).map a) ≫
                pullback.fst (D.obj j).hom (relativeBaseMap f c e j) := by
                  rw [hnat]
          _ = s.π.app i ≫ ((relativePullbackSystem f c e).map a ≫
                pullback.fst (D.obj j).hom (relativeBaseMap f c e j)) :=
                  Category.assoc _ _ _
          _ = s.π.app i ≫ (pullback.fst (D.obj i).hom
                (relativeBaseMap f c e i) ≫ (D.map a).left) :=
                  congrArg (fun z => s.π.app i ≫ z) hfst
          _ = (s.π.app i ≫ pullback.fst (D.obj i).hom
                (relativeBaseMap f c e i)) ≫ (D.map a).left :=
                  (Category.assoc _ _ _).symm
      · change relativeBaseMap f c e j =
          relativeBaseMap f c e i ≫ (D.map a).right
        exact (relativeBaseMap_natural f c e a).symm
  }

/-- The source component of the factorization of `s` through the limit cone `c`. -/
private theorem relativePullbackArrowCone_fac_left {J : Type v} [Preorder J]
    [IsDirectedOrder J] [Nonempty J] {X B : Scheme.{u}}
    {D : Jᵒᵖ ⥤ Arrow Scheme.{u}} (f : X ⟶ B) (c : Cone D)
    (e : c.pt ≅ Arrow.mk f) (hc : IsLimit c) (s : Cone (relativePullbackSystem f c e))
    (i : Jᵒᵖ) :
    (hc.lift (relativePullbackArrowCone f c e s)).left ≫ (c.π.app i).left =
      s.π.app i ≫ pullback.fst (D.obj i).hom (relativeBaseMap f c e i) :=
  congrArg Arrow.Hom.left (hc.fac (relativePullbackArrowCone f c e s) i)

/-- The base component of the factorization of `s` through the limit cone `c`. -/
private theorem relativePullbackArrowCone_fac_right {J : Type v} [Preorder J]
    [IsDirectedOrder J] [Nonempty J] {X B : Scheme.{u}}
    {D : Jᵒᵖ ⥤ Arrow Scheme.{u}} (f : X ⟶ B) (c : Cone D)
    (e : c.pt ≅ Arrow.mk f) (hc : IsLimit c) (s : Cone (relativePullbackSystem f c e))
    (i : Jᵒᵖ) :
    (hc.lift (relativePullbackArrowCone f c e s)).right ≫ (c.π.app i).right =
      relativeBaseMap f c e i :=
  congrArg Arrow.Hom.right (hc.fac (relativePullbackArrowCone f c e s) i)

private noncomputable def relativePullbackLimitCone_isLimit {J : Type v} [Preorder J]
    [IsDirectedOrder J] [Nonempty J] {X B : Scheme.{u}}
    {D : Jᵒᵖ ⥤ Arrow Scheme.{u}} (f : X ⟶ B) (c : Cone D)
    (e : c.pt ≅ Arrow.mk f) (hc : IsLimit c) :
    IsLimit (relativePullbackLimitCone f c e) := by
  classical
  refine {
    lift := fun s => (hc.lift (relativePullbackArrowCone f c e s) ≫ e.hom).left
    fac := ?_
    uniq := ?_ }
  · intro s i
    let d := relativePullbackArrowCone f c e s
    let l := hc.lift d
    let m := l ≫ e.hom
    have hleft : l.left ≫ (c.π.app i).left =
        s.π.app i ≫ pullback.fst (D.obj i).hom (relativeBaseMap f c e i) :=
      relativePullbackArrowCone_fac_left f c e hc s i
    have hright : l.right = e.inv.right := by
      let z₁ : Arrow.mk (Scheme.emptyTo B) ⟶ c.pt :=
        Arrow.homMk (Scheme.emptyTo _) l.right (by apply Scheme.empty_ext)
      let z₂ : Arrow.mk (Scheme.emptyTo B) ⟶ c.pt :=
        Arrow.homMk (Scheme.emptyTo _) e.inv.right (by apply Scheme.empty_ext)
      have hz : z₁ = z₂ := by
        apply hc.hom_ext
        intro j
        apply Arrow.hom_ext
        · apply Scheme.empty_ext
        · exact (relativePullbackArrowCone_fac_right f c e hc s j).trans
            (relativeBaseMap_apply f c e j).symm
      have h := congrArg Arrow.Hom.right hz
      simpa [d, relativePullbackArrowCone, z₁, z₂] using h
    have hmright : m.right = 𝟙 B := by
      change l.right ≫ e.hom.right = 𝟙 B
      rw [hright]
      change Arrow.Hom.right (e.inv ≫ e.hom) =
        Arrow.Hom.right (𝟙 (Arrow.mk f))
      rw [e.inv_hom_id]
    have hcancel : e.hom.left ≫ e.inv.left = 𝟙 c.pt.left := by
      simp
    apply pullback.hom_ext
    · have hfst := relativePullbackLimitMap_fst f c e i
      change m.left ≫ (relativePullbackLimitMap f c e i ≫
          pullback.fst (D.obj i).hom (relativeBaseMap f c e i)) =
        s.π.app i ≫ pullback.fst (D.obj i).hom (relativeBaseMap f c e i)
      rw [hfst]
      change (l.left ≫ e.hom.left) ≫
        (e.inv.left ≫ (c.π.app i).left) =
        s.π.app i ≫ pullback.fst (D.obj i).hom (relativeBaseMap f c e i)
      simpa [Category.assoc, hcancel] using hleft
    · have hsnd := relativePullbackLimitMap_snd f c e i
      change m.left ≫ (relativePullbackLimitMap f c e i ≫
          pullback.snd (D.obj i).hom (relativeBaseMap f c e i)) =
        s.π.app i ≫ pullback.snd (D.obj i).hom (relativeBaseMap f c e i)
      have hm : m.left ≫ f = relativePullbackConeBase f c e s := by
        have hw := Arrow.w m
        change m.left ≫ f = relativePullbackConeBase f c e s ≫ m.right at hw
        rw [hmright] at hw
        simpa only [Category.comp_id] using hw
      have hbase : relativePullbackConeBase f c e s =
          s.π.app i ≫ pullback.snd (D.obj i).hom (relativeBaseMap f c e i) := by
        simpa [relativePullbackConeBase] using
          (relativePullbackCone_snd_eq f c e s i).symm
      have hproj : m.left ≫ (relativePullbackLimitMap f c e i ≫
          pullback.snd (D.obj i).hom (relativeBaseMap f c e i)) = m.left ≫ f :=
        congrArg (fun z => m.left ≫ z) hsnd
      exact hproj.trans (hm.trans hbase)
  · intro s (g : _ ⟶ X) hg
    let l := hc.lift (relativePullbackArrowCone f c e s)
    have hg' (i : Jᵒᵖ) : g ≫ relativePullbackLimitMap f c e i = s.π.app i := hg i
    let n : Arrow.mk (relativePullbackConeBase f c e s) ⟶ c.pt := by
      let b : s.pt ⟶ B := relativePullbackConeBase f c e s
      have hb : g ≫ f = b := by
        obtain ⟨i⟩ := ‹Nonempty J›
        have h := relativePullbackLimitMap_snd f c e (Opposite.op i)
        calc g ≫ f = (g ≫ relativePullbackLimitMap f c e (Opposite.op i)) ≫
              pullback.snd (D.obj (Opposite.op i)).hom
                (relativeBaseMap f c e (Opposite.op i)) :=
            (congrArg (g ≫ ·) h.symm).trans (Category.assoc _ _ _).symm
          _ = b := by
            rw [hg' (Opposite.op i)]
            exact relativePullbackCone_snd_eq f c e s (Opposite.op i)
      refine Arrow.homMk (g ≫ e.inv.left) e.inv.right ?_
      change (g ≫ e.inv.left) ≫ c.pt.hom = b ≫ e.inv.right
      rw [Category.assoc, e.inv.w, ← Category.assoc]
      exact congrArg (· ≫ e.inv.right) hb
    have hnfac : n = l := by
      apply hc.hom_ext
      intro i
      apply Arrow.hom_ext
      · refine Eq.trans ?_ (relativePullbackArrowCone_fac_left f c e hc s i).symm
        change (g ≫ e.inv.left) ≫ (c.π.app i).left = _
        rw [Category.assoc, ← relativePullbackLimitMap_fst f c e i, ← Category.assoc, hg' i]
        rfl
      · exact (relativeBaseMap_apply f c e i).symm.trans
          (relativePullbackArrowCone_fac_right f c e hc s i).symm
    have hleft := congrArg Arrow.Hom.left hnfac
    have hcomp : g = (g ≫ e.inv.left) ≫ e.hom.left := by
      simp
    have hnleft : n.left = g ≫ e.inv.left := by
      simp [n, Arrow.homMk_left]
    rw [hcomp, ← hnleft, hleft]
    rfl

end RelativeApproximationHelpers

/-- **Stacks Project, Tag 09MV.** A quasi-compact and quasi-separated scheme over a
quasi-separated base is a directed inverse limit of quasi-compact and quasi-separated schemes of
finite presentation over that base, with affine transition morphisms over the base. -/
@[stacks 09MV]
theorem exists_isLimit_finitePresentation
    {X S : Scheme.{u}} (f : X ⟶ S)
    [CompactSpace X] [QuasiSeparatedSpace X] [QuasiSeparatedSpace S] :
    ∃ (I : Type u) (_ : Preorder I) (_ : Nonempty I)
      (_ : IsDirectedOrder I) (D : Iᵒᵖ ⥤ Scheme.{u})
      (t : D ⟶ (Functor.const Iᵒᵖ).obj S)
      (p : (Functor.const Iᵒᵖ).obj X ⟶ D) (_ : IsLimit (Cone.mk X p)),
      p ≫ t = (Functor.const Iᵒᵖ).map f ∧
        (∀ i, FinitePresentation (t.app i)) ∧
        (∀ i, CompactSpace (D.obj i) ∧ QuasiSeparatedSpace (D.obj i)) ∧
        ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (D.map g) := by
  classical
  obtain ⟨U, hUcompact, -, himageU⟩ :=
    exists_compactOpen_covering_range f (W := ⊤) (by simp)
  have hpre : (⊤ : X.Opens) ≤ f ⁻¹ᵁ U := fun x _ => himageU ⟨x, rfl⟩
  let fU : X ⟶ U.toScheme := X.topIso.inv ≫ f.resLE U ⊤ hpre
  have hfU : fU ≫ U.ι = f := by simp [fU]
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hUcompact
  have hUqs : QuasiSeparatedSpace U.toScheme := by
    apply (quasiSeparatedSpace_iff_quasiSeparated U.toScheme).2
    let : QuasiSeparated U.ι := inferInstance
    have hSqs : QuasiSeparated (terminal.from S) :=
      (quasiSeparatedSpace_iff_quasiSeparated S).mp inferInstance
    have : QuasiSeparated (U.ι ≫ terminal.from S) := inferInstance
    simpa using this
  let : QuasiSeparatedSpace U.toScheme := hUqs
  obtain ⟨I, hIpre, hInonempty, hIdir, D, c, hD, hS, htrans, hc0, he0⟩ :=
    LimitFPObjectDescent.exists_isLimit_finiteType_arrow fU
  let : Preorder I := hIpre
  let : Nonempty I := hInonempty
  let : IsDirectedOrder I := hIdir
  let hc : IsLimit c := Classical.choice hc0
  let e : c.pt ≅ Arrow.mk fU := Classical.choice he0
  let E : Iᵒᵖ ⥤ Scheme.{u} := relativePullbackSystem fU c e
  let s : Cone E := relativePullbackLimitCone fU c e
  let t : E ⟶ (Functor.const Iᵒᵖ).obj S := {
    app := fun i => pullback.snd (D.obj i).hom (relativeBaseMap fU c e i) ≫ U.ι
    naturality := by
      intro i j a
      change (relativePullbackTransition (relativeBaseMap fU c e)
          (relativeBaseMap_natural fU c e) a ≫
            pullback.snd (D.obj j).hom (relativeBaseMap fU c e j)) ≫ U.ι =
        pullback.snd (D.obj i).hom (relativeBaseMap fU c e i) ≫ U.ι
      exact congrArg (fun z => z ≫ U.ι)
        (relativePullbackTransition_snd (relativeBaseMap fU c e)
          (relativeBaseMap_natural fU c e) a)
  }
  let p : (Functor.const Iᵒᵖ).obj X ⟶ E := s.π
  have happrox (i : Iᵒᵖ) : FinitePresentation (t.app i) ∧
      CompactSpace (E.obj i) ∧ QuasiSeparatedSpace (E.obj i) := by
    change FinitePresentation
        (pullback.snd (D.obj i).hom (relativeBaseMap fU c e i) ≫ U.ι) ∧
      CompactSpace (pullback (D.obj i).hom (relativeBaseMap fU c e i) : Scheme.{u}) ∧
      QuasiSeparatedSpace (pullback (D.obj i).hom (relativeBaseMap fU c e i) : Scheme.{u})
    have : LocallyOfFiniteType (terminal.from (D.obj i).right) := (hS i).1
    have hcompLft : LocallyOfFiniteType
        ((D.obj i).hom ≫ terminal.from (D.obj i).right) := by
      simpa using (hD i).1
    have : LocallyOfFiniteType (D.obj i).hom :=
      locallyOfFiniteType_of_comp (D.obj i).hom (terminal.from (D.obj i).right)
    have : IsLocallyNoetherian (⊤_ Scheme.{u}) := by
      have : IsNoetherianRing (ULift.{u} ℤ) :=
        isNoetherianRing_of_ringEquiv ℤ ULift.ringEquiv.symm
      have : IsLocallyNoetherian (Spec (.of (ULift.{u} ℤ))) := inferInstance
      let eT := AlgebraicGeometry.specULiftZIsTerminal.uniqueUpToIso
        terminalIsTerminal
      have : IsOpenImmersion eT.inv := inferInstance
      exact isLocallyNoetherian_of_isOpenImmersion eT.inv
    have : IsLocallyNoetherian (D.obj i).right :=
      LocallyOfFiniteType.isLocallyNoetherian (terminal.from (D.obj i).right)
    have : QuasiSeparatedSpace (D.obj i).right := inferInstance
    have hcompQC : QuasiCompact
        ((D.obj i).hom ≫ terminal.from (D.obj i).right) := by
      simpa using (hD i).2
    have : QuasiCompact (D.obj i).hom :=
      QuasiCompact.of_comp (D.obj i).hom (terminal.from (D.obj i).right)
    have hfp : FinitePresentation (D.obj i).hom :=
      finitePresentation_of_finiteType (D.obj i).hom
    have : LocallyOfFinitePresentation (D.obj i).hom := hfp.locallyOfFinitePresentation
    have : QuasiSeparated (D.obj i).hom := hfp.quasiSeparated
    refine ⟨FinitePresentation.mk inferInstance inferInstance inferInstance, ?_, ?_⟩
    · exact QuasiCompact.compactSpace_of_compactSpace
        (pullback.snd (D.obj i).hom (relativeBaseMap fU c e i))
    · exact quasiSeparatedSpace_of_quasiSeparated
        (pullback.snd (D.obj i).hom (relativeBaseMap fU c e i))
  refine ⟨I, hIpre, hInonempty, hIdir, E, t, p, relativePullbackLimitCone_isLimit fU c e hc, ?_,
    fun i => (happrox i).1, fun i => (happrox i).2, fun a =>
      relativePullbackTransition_isAffineHom (relativeBaseMap fU c e)
        (relativeBaseMap_natural fU c e) a (htrans a).1 (htrans a).2⟩
  ext i
  change (relativePullbackLimitMap fU c e i ≫
      pullback.snd (D.obj i).hom (relativeBaseMap fU c e i)) ≫ U.ι = f
  rw [relativePullbackLimitMap_snd, hfU]

end AlgebraicGeometry

end
