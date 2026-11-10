module

public import Mathlib.AlgebraicGeometry.ResidueField
public import StacksCore.Tactic.StacksAttribute
public import StacksCore.Topology.Maps.SubmersiveOpen
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.PointsOverField
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.RestrictionOverField
public import StacksFrontier.AlgebraicGeometry.Groupoids.More.Translation
public import StacksFrontier.AlgebraicGeometry.Groupoids.Slicing.ArrowImageOverField
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.OverPullbackLeft
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.Restriction
public import StacksFrontier.AlgebraicGeometry.Groupoids.Stabilizer.RestrictionGroupoid

/-!
# Open images of morphisms of groupoids on a field

The image on arrows of a morphism between groupoid schemes with common object scheme the
spectrum of a field is closed as soon as it is open.

## Main results

* `AlgebraicGeometry.isClosed_range_mapArrows_of_isOpen` proves that an open image on arrows
  is closed.

## Implementation notes

That the two groupoids share their object scheme is expressed by an equality of objects in the
over category, and that the map on objects is the identity by the corresponding equality
morphism; the hypothesis that the common object scheme is the spectrum of a field is likewise
an equality of schemes.

The argument lifts a point of the closure of the image to a point of the arrow scheme valued in
an algebraically closed field, restricts the target groupoid along the resulting extension, and
uses translation by that point. Translation is an automorphism of the restricted arrow scheme
carrying the identity section to the chosen point, so it carries an open neighbourhood of the
identity inside the image to an open neighbourhood of the point; composing the resulting pair
of arrows inside the image then exhibits the point itself in the image.

## References

* [Stacks Project, Tag 04Q6](https://stacks.math.columbia.edu/tag/04Q6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry

/-- A morphism in the over category has an invertible underlying morphism of schemes if it is
invertible. -/
private lemma isIso_left_of_isIso {S : Scheme.{u}} {X Y : Over S} (f : X ⟶ Y) [IsIso f] :
    IsIso f.left :=
  inferInstanceAs (IsIso ((Over.forget S).map f))

/-- An equation between composites of morphisms over `S` holds pointwise on underlying spaces. -/
private lemma left_base_apply_eq {S : Scheme.{u}} {W X Y Z : Over S} {f : W ⟶ X} {g : X ⟶ Z}
    {f' : W ⟶ Y} {g' : Y ⟶ Z} (h : f ≫ g = f' ≫ g') (w : W.left) :
    g.left.base (f.left.base w) = g'.left.base (f'.left.base w) := by
  simpa [Scheme.Hom.comp_apply] using congrArg (fun q => q.left.base w) h

/-- If a morphism of schemes factors through isomorphisms on both sides, and the middle factor is
an isomorphism on residue fields at the image point, then so is the composite. -/
private lemma isIso_residueFieldMap_of_eq_comp {X Y Z W : Scheme.{u}} (eA : X ⟶ Y) [IsIso eA]
    (φ : Y ⟶ Z) (eO : Z ⟶ W) [IsIso eO] (ψ : X ⟶ W) (h : ψ = eA ≫ φ ≫ eO) (x : X)
    (hφ : IsIso (φ.residueFieldMap (eA.base x))) : IsIso (ψ.residueFieldMap x) := by
  have hO : IsIso (eO.residueFieldMap (φ.base (eA.base x))) := inferInstance
  have hA : IsIso (eA.residueFieldMap x) := inferInstance
  rw [h, Scheme.residueFieldMap_comp, Scheme.residueFieldMap_comp]
  exact IsIso.comp_isIso' (IsIso.comp_isIso' hO hφ) hA

/-- A morphism of groupoid schemes commutes with composition of arrows, read on points of the
scheme of composable arrows. -/
private lemma map_comp_point {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}
    (F : GroupoidScheme.Hom G₁ G₂)
    (hs : G₁.source ≫ F.mapObjects = F.mapArrows ≫ G₂.source)
    (ht : G₁.target ≫ F.mapObjects = F.mapArrows ≫ G₂.target)
    (z : (pullback G₁.source G₁.target).left) :
    F.mapArrows.left.base (G₁.comp.left.base z) =
      G₂.comp.left.base ((pullback.map G₁.source G₁.target G₂.source G₂.target
        F.mapArrows F.mapArrows F.mapObjects hs ht).left.base z) := by
  have w' : (pullback.fst G₁.source G₁.target ≫ F.mapArrows) ≫ G₂.source =
      (pullback.snd G₁.source G₁.target ≫ F.mapArrows) ≫ G₂.target := by
    simp only [Category.assoc, F.map_source, F.map_target]
    rw [← Category.assoc, pullback.condition, Category.assoc]
  have h := congrArg (fun f : pullback G₁.source G₁.target ⟶ G₂.arrows => f.left.base z)
    (F.map_comp (pullback G₁.source G₁.target) (pullback.fst G₁.source G₁.target)
      (pullback.snd G₁.source G₁.target) pullback.condition w')
  simpa [GroupoidScheme.compose] using h

/-- If both arrows of a composable pair lie in the image of a morphism of groupoid schemes which
is an isomorphism on objects, then so does their composite. -/
private lemma range_comp_of_isIso_mapObjects
    {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}
    (F : GroupoidScheme.Hom G₁ G₂) [IsIso F.mapObjects]
    {t : ↑(pullback G₂.source.left G₂.target.left)}
    (ht₁ : pullback.fst G₂.source.left G₂.target.left t ∈
      Set.range F.mapArrows.left.base)
    (ht₂ : pullback.snd G₂.source.left G₂.target.left t ∈
      Set.range F.mapArrows.left.base) :
    G₂.comp.left.base ((overPullbackLeftIso G₂.source G₂.target).inv.base t) ∈
      Set.range F.mapArrows.left.base := by
  have := isIso_left_of_isIso F.mapObjects
  have hs : G₁.source ≫ F.mapObjects = F.mapArrows ≫ G₂.source := F.map_source.symm
  have ht : G₁.target ≫ F.mapObjects = F.mapArrows ≫ G₂.target := F.map_target.symm
  let m₁ := pullback.map G₁.source.left G₁.target.left G₂.source.left G₂.target.left
    F.mapArrows.left F.mapArrows.left F.mapObjects.left
    (by simpa using congrArg (fun f => f.left) hs)
    (by simpa using congrArg (fun f => f.left) ht)
  obtain ⟨z₁, hz₁⟩ : t ∈ Set.range m₁.base := by
    rw [Scheme.Pullback.range_map]
    exact ⟨ht₁, ht₂⟩
  let e₁ := overPullbackLeftIso G₁.source G₁.target
  let e₂ := overPullbackLeftIso G₂.source G₂.target
  let z : (pullback G₁.source G₁.target).left := e₁.inv z₁
  let m₂ := pullback.map G₁.source G₁.target G₂.source G₂.target
    F.mapArrows F.mapArrows F.mapObjects hs ht
  have hm₂fst : m₂ ≫ pullback.fst G₂.source G₂.target =
      pullback.fst G₁.source G₁.target ≫ F.mapArrows := pullback.lift_fst _ _ _
  have hm₂snd : m₂ ≫ pullback.snd G₂.source G₂.target =
      pullback.snd G₁.source G₁.target ≫ F.mapArrows := pullback.lift_snd _ _ _
  have hm₁fst : m₁ ≫ pullback.fst G₂.source.left G₂.target.left =
      pullback.fst G₁.source.left G₁.target.left ≫ F.mapArrows.left := pullback.lift_fst _ _ _
  have hm₁snd : m₁ ≫ pullback.snd G₂.source.left G₂.target.left =
      pullback.snd G₁.source.left G₁.target.left ≫ F.mapArrows.left := pullback.lift_snd _ _ _
  have hm₂fst' : m₂.left ≫ (pullback.fst G₂.source G₂.target).left =
      (pullback.fst G₁.source G₁.target).left ≫ F.mapArrows.left := by
    simpa [Over.comp_left] using congrArg (fun f => f.left) hm₂fst
  have hm₂snd' : m₂.left ≫ (pullback.snd G₂.source G₂.target).left =
      (pullback.snd G₁.source G₁.target).left ≫ F.mapArrows.left := by
    simpa [Over.comp_left] using congrArg (fun f => f.left) hm₂snd
  have hcompare : m₂.left ≫ e₂.hom = e₁.hom ≫ m₁ := by
    apply pullback.hom_ext
    · rw [Category.assoc, overPullbackLeftIso_hom_fst, hm₂fst', Category.assoc, hm₁fst,
        ← Category.assoc, overPullbackLeftIso_hom_fst]
    · rw [Category.assoc, overPullbackLeftIso_hom_snd, hm₂snd', Category.assoc, hm₁snd,
        ← Category.assoc, overPullbackLeftIso_hom_snd]
  have hz : e₁.hom.base z = z₁ := by simp [z]
  have hmap : e₂.hom.base (m₂.left.base z) = t := by
    simpa [Scheme.Hom.comp_apply, hz, hz₁] using congrArg (fun x => x.base z) hcompare
  have hmap' : m₂.left.base z = e₂.inv.base t := by
    simpa [e₂] using congrArg e₂.inv.base hmap
  exact ⟨G₁.comp.left.base z,
    (map_comp_point F hs ht z).trans (congrArg (G₂.comp.left.base ·) hmap')⟩

/-- The image on arrows of a morphism of groupoid schemes is stable under the inverse morphism. -/
private lemma range_inverse {S : Scheme.{u}} {G₁ G₂ : GroupoidScheme S}
    (F : GroupoidScheme.Hom G₁ G₂) {x : G₂.arrows.left}
    (hx : x ∈ Set.range F.mapArrows.left.base) :
    G₂.inverse.left.base x ∈ Set.range F.mapArrows.left.base := by
  obtain ⟨y, rfl⟩ := hx
  exact ⟨G₁.inverse.left.base y, (left_base_apply_eq (groupoidHom_map_inverse F) y).symm⟩

/-- Left translation acts on a generalized arrow by composing with the chosen section at its
target. -/
private lemma leftTranslation_apply {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : G.objects ⟶ G.arrows) (ha : a ≫ G.source = 𝟙 G.objects)
    {T : Over S} (f : T ⟶ G.arrows) :
    f ≫ GroupoidScheme.leftTranslation G a ha =
      G.compose (f ≫ G.target ≫ a) f (by simp [Category.assoc, ha]) := by
  have w : (f ≫ G.target ≫ a) ≫ G.source = f ≫ G.target := by
    simp [Category.assoc, ha]
  have hpull : f ≫ pullback.lift (G.target ≫ a) (𝟙 G.arrows)
      (by simp [Category.assoc, ha]) = pullback.lift (f ≫ G.target ≫ a) f w := by
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
    · simp only [Category.assoc, pullback.lift_snd]
      simp
  dsimp [GroupoidScheme.leftTranslation, GroupoidScheme.compose]
  rw [← Category.assoc, hpull]

/-- Left translation does not change the source of an arrow. -/
private lemma leftTranslation_source {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : G.objects ⟶ G.arrows) (ha : a ≫ G.source = 𝟙 G.objects) :
    GroupoidScheme.leftTranslation G a ha ≫ G.source = G.source := by
  simp [GroupoidScheme.leftTranslation, Category.assoc,
    G.source_comp]

/-- Composing a left translate of an arrow with the inverse of that arrow recovers the value of
the chosen section at its target. -/
private lemma leftTranslation_comp_inverse {S : Scheme.{u}} (G : GroupoidScheme S)
    (a : G.objects ⟶ G.arrows) (ha : a ≫ G.source = 𝟙 G.objects)
    {T : Over S} (f : T ⟶ G.arrows) :
    G.compose (f ≫ GroupoidScheme.leftTranslation G a ha)
      (f ≫ G.inverse) (by
        rw [Category.assoc, leftTranslation_source G a ha,
          Category.assoc, G.target_inverse]) = f ≫ G.target ≫ a := by
  let A := f ≫ G.target ≫ a
  have wAf : A ≫ G.source = f ≫ G.target := by
    simp [A, Category.assoc, ha]
  have wfi : f ≫ G.source = (f ≫ G.inverse) ≫ G.target := by
    simp [Category.assoc, G.target_inverse]
  have wcomposed : (f ≫ GroupoidScheme.leftTranslation G a ha) ≫ G.source =
      (f ≫ G.inverse) ≫ G.target := by
    rw [Category.assoc, leftTranslation_source G a ha,
      Category.assoc, G.target_inverse]
  have w1 : (G.compose A f wAf) ≫ G.source = (f ≫ G.inverse) ≫ G.target := by
    calc
      (G.compose A f wAf) ≫ G.source = f ≫ G.source := by
        simp [GroupoidScheme.compose, Category.assoc, G.source_comp]
      _ = (f ≫ G.inverse) ≫ G.target := wfi
  have hrightInv : G.compose f (f ≫ G.inverse) wfi = f ≫ G.target ≫ G.identity :=
    G.right_inverse T f wfi
  have w2 : A ≫ G.source = (G.compose f (f ≫ G.inverse) wfi) ≫ G.target := by
    rw [hrightInv]
    simp [A, Category.assoc, G.target_identity, wAf]
  have w2' : A ≫ G.source = (f ≫ G.target ≫ G.identity) ≫ G.target := by
    rw [wAf]
    simp [Category.assoc, G.target_identity]
  calc
    G.compose (f ≫ GroupoidScheme.leftTranslation G a ha)
        (f ≫ G.inverse) wcomposed = G.compose (G.compose A f wAf) (f ≫ G.inverse) w1 :=
          GroupoidScheme.groupoidCompose_congr_left G (leftTranslation_apply G a ha f) _ _
    _ = G.compose A (G.compose f (f ≫ G.inverse) wfi) w2 :=
          G.assoc T A f (f ≫ G.inverse) wAf wfi w1 w2
    _ = G.compose A (f ≫ G.target ≫ G.identity) w2' :=
          GroupoidScheme.groupoidCompose_congr_right G hrightInv w2 w2'
    _ = G.compose A (A ≫ G.source ≫ G.identity) _ :=
          GroupoidScheme.groupoidCompose_congr_right G
            (congrArg (fun q => q ≫ G.identity) wAf.symm) _ _
    _ = A := G.right_identity T A (by simp [Category.assoc, G.target_identity])

/-- **Stacks Project, Tag 04Q6.** If a morphism of groupoid schemes whose common object
scheme is the spectrum of a field has open image on arrows, then that image is closed. -/
@[stacks 04Q6] public lemma isClosed_range_mapArrows_of_isOpen
    {S : Scheme.{u}} {k : Type u} [Field k]
    {G₁ G₂ : GroupoidScheme S} (F : GroupoidScheme.Hom G₁ G₂)
    (hobjects : G₁.objects = G₂.objects)
    (hfield : G₁.objects.left = Spec (.of k))
    (hmapObjects : F.mapObjects = eqToHom hobjects)
    (hopen : IsOpen (Set.range F.mapArrows.left.base)) :
    IsClosed (Set.range F.mapArrows.left.base) := by
  classical
  apply closure_subset_iff_isClosed.mp
  intro r hr
  have : IsIso F.mapObjects := by
    rw [hmapObjects]
    infer_instance
  let A : Set G₂.arrows.left := Set.range F.mapArrows.left.base
  have hAopen : IsOpen A := hopen
  have hfield₂ : G₂.objects.left = Spec (.of k) := by
    rw [← congrArg Over.left hobjects]
    exact hfield
  have objects_eq : G₂.objects =
      Over.mk (eqToHom hfield₂.symm ≫ G₂.objects.hom) := by
    revert hfield₂
    cases G₂.objects with
    | mk X p =>
      intro hX
      change X = Spec (.of k) at hX
      cases hX
      rfl
  let structureMap : Spec (.of k) ⟶ S := eqToHom hfield₂.symm ≫ G₂.objects.hom
  obtain ⟨k', hk', halg', i, rPoint, hrLift, hsourceLift, htargetLift⟩ :=
    GroupoidScheme.exists_isIso_source_target_over_isAlgClosed
      structureMap G₂ objects_eq r
  let g : Over.mk (Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap) ⟶ G₂.objects :=
    GroupoidScheme.extensionMap structureMap i ≫ eqToHom objects_eq.symm
  have hfield' : (Over.mk (Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap)).left =
      Spec (.of k') := rfl
  have hGfield : G₂.objects.left ≅ Spec (.of k) := asIso (eqToHom hfield₂)
  have hUfield : (Over.mk (Scheme.Spec.map (CommRingCat.ofHom i).op ≫ structureMap)).left ≅
      Spec (.of k') := Iso.refl _
  let q := restrictionArrowsToArrows G₂ g
  have hqSurj' : Surjective q.left :=
    surjective_restrictionDiagramMorphisms G₂ g k k'
      hGfield hUfield 11
  have hqOpen' : UniversallyOpen q.left :=
    universallyOpen_restrictionDiagramMorphisms G₂ g k k'
      hGfield hUfield 11
  let : UniversallyOpen q.left := hqOpen'
  have hqOpen : IsOpenMap q.left.base := by
    exact Scheme.Hom.isOpenMap q.left
  have hqCont : Continuous q.left.base := q.left.continuous
  let R := GroupoidScheme.restrict G₂ g
  have hRfield : R.groupoid.objects.left = Spec (.of k') := by
    simpa [R] using congrArg Over.left R.objects_eq
  let rR : R.groupoid.arrows.left :=
    (eqToHom R.arrows_eq.symm).left (rPoint (IsLocalRing.closedPoint k'))
  have := isIso_left_of_isIso (eqToHom R.arrows_eq)
  let qR : Scheme.Hom R.groupoid.arrows.left G₂.arrows.left := R.hom.mapArrows.left
  have hqReq : qR = (eqToHom R.arrows_eq).left ≫ q.left := by
    simpa [qR, R] using congrArg (fun f => f.left) R.mapArrows_eq
  have hqRopen : IsOpenMap qR.base := by
    intro U hU
    rw [hqReq]
    have hEopen : IsOpen ((eqToHom R.arrows_eq).left.base '' U) :=
      (eqToHom R.arrows_eq).left.homeomorph.isOpenMap U hU
    have h := hqOpen ((eqToHom R.arrows_eq).left.base '' U) hEopen
    simpa [Scheme.Hom.comp_apply, Set.image_image, Function.comp_def] using h
  have hqRcont : Continuous qR.base := qR.continuous
  let A' : Set R.groupoid.arrows.left := qR.base ⁻¹' A
  have hA'open : IsOpen A' := hAopen.preimage hqRcont
  have htransport : (eqToHom R.arrows_eq).left.base rR =
      rPoint (IsLocalRing.closedPoint k') := by
    let p := rPoint (IsLocalRing.closedPoint k')
    have hcomp : (eqToHom R.arrows_eq.symm).left ≫ (eqToHom R.arrows_eq).left =
        𝟙 (restrictionArrows G₂ g).left := by simp
    have h := congrArg (fun f : (restrictionArrows G₂ g).left ⟶
        (restrictionArrows G₂ g).left => f.base p) hcomp
    change (eqToHom R.arrows_eq).left.base
      ((eqToHom R.arrows_eq.symm).left.base p) = p
    change ((eqToHom R.arrows_eq.symm).left ≫ (eqToHom R.arrows_eq).left).base p = p
    exact h
  have hqr : qR.base rR = r := by
    rw [hqReq]
    change q.left.base ((eqToHom R.arrows_eq).left.base rR) = r
    rw [htransport]
    exact hrLift
  have hr' : rR ∈ closure A' := by
    have hclosure := hqRopen.preimage_closure_eq_closure_preimage hqRcont A
    have hp : rR ∈ qR.base ⁻¹' closure A := by
      change qR.base rR ∈ closure A
      rw [hqr]
      exact hr
    rw [hclosure] at hp
    exact hp
  let eA := (eqToHom R.arrows_eq).left
  let eO := (eqToHom R.objects_eq.symm).left
  have : IsIso eO := isIso_left_of_isIso (eqToHom R.objects_eq.symm)
  have heApoint : eA.base rR = rPoint (IsLocalRing.closedPoint k') := by
    exact htransport
  have hsourceR : IsIso (R.groupoid.source.left.residueFieldMap rR) :=
    isIso_residueFieldMap_of_eq_comp eA (restrictionSource G₂ g).left eO _
      (by simpa [Over.comp_left, eA, eO] using congrArg (fun f => f.left) R.source_eq) rR
      (by rw [heApoint]; simpa [g] using hsourceLift)
  have htargetR : IsIso (R.groupoid.target.left.residueFieldMap rR) :=
    isIso_residueFieldMap_of_eq_comp eA (restrictionTarget G₂ g).left eO _
      (by simpa [Over.comp_left, eA, eO] using congrArg (fun f => f.left) R.target_eq) rR
      (by rw [heApoint]; simpa [g] using htargetLift)
  have hIdA : ∀ x : G₂.objects.left, G₂.identity.left.base x ∈ A := by
    intro x
    have := isIso_left_of_isIso F.mapObjects
    obtain ⟨y, hy⟩ := F.mapObjects.left.surjective x
    exact ⟨G₁.identity.left.base y, by simpa [hy] using (left_base_apply_eq F.map_identity y).symm⟩
  have hIdA' : ∀ x : R.groupoid.objects.left, R.groupoid.identity.left.base x ∈ A' := by
    intro x
    change qR.base (R.groupoid.identity.left.base x) ∈ A
    rw [(left_base_apply_eq R.hom.map_identity x).symm]
    exact hIdA (R.hom.mapObjects.left.base x)
  let : IsIso (R.groupoid.source.left.residueFieldMap rR) := hsourceR
  let : IsIso (R.groupoid.target.left.residueFieldMap rR) := htargetR
  let τ := GroupoidScheme.translationByPoint R.groupoid k' hRfield rR
  have hτiso : IsIso τ :=
    GroupoidScheme.translationByPoint_isIso R.groupoid k' hRfield rR
  let : IsIso τ := hτiso
  have := isIso_left_of_isIso τ
  let eR := R.groupoid.identity.left.base (R.groupoid.source.left.base rR)
  have hτe : τ.left.base eR = rR := by
    simpa [τ, eR, Scheme.Hom.comp_apply] using
      GroupoidScheme.identity_image_translationByPoint R.groupoid k' hRfield rR
  have hτAopen : IsOpen (τ.left.base '' A') := τ.left.homeomorph.isOpenMap A' hA'open
  have hrW : rR ∈ τ.left.base '' A' := ⟨eR, hIdA' _, hτe⟩
  obtain ⟨x, hxW, hxA'⟩ := mem_closure_iff.mp hr' _ hτAopen hrW
  obtain ⟨y, hyA', hyx⟩ := hxW
  have hτyA' : τ.left.base y ∈ A' := by
    rw [hyx]
    exact hxA'
  have hinvPoint : qR.base (R.groupoid.inverse.left.base y) =
      G₂.inverse.left.base (qR.base y) := by
    exact (left_base_apply_eq (groupoidHom_map_inverse R.hom) y).symm
  have hinvA : qR.base (R.groupoid.inverse.left.base y) ∈ A :=
    hinvPoint ▸ range_inverse F (by simpa [A, A'] using hyA')
  have hτyA : qR.base (τ.left.base y) ∈ A := hτyA'
  let a := GroupoidScheme.sourceNormalizedArrow R.groupoid k' hRfield rR
  have ha : a ≫ R.groupoid.source = 𝟙 R.groupoid.objects :=
    GroupoidScheme.sourceNormalizedArrow_source R.groupoid k' hRfield rR
  have hτsource : τ ≫ R.groupoid.source = R.groupoid.source := by
    dsimp [τ, GroupoidScheme.translationByPoint,
      GroupoidScheme.leftTranslation]
    simp [Category.assoc, R.groupoid.source_comp]
  let L := R.groupoid.arrows.left.residueField y
  let pL := IsLocalRing.closedPoint L
  let pt := R.groupoid.arrows.left.fromSpecResidueField y
  let Tspec : Over S := Over.mk (pt ≫ R.groupoid.arrows.hom)
  let f : Tspec ⟶ R.groupoid.arrows := Over.homMk pt (by rfl)
  have hfpoint : f.left pL = y := by
    exact Scheme.fromSpecResidueField_apply y pL
  have w : (f ≫ τ) ≫ R.groupoid.source =
      (f ≫ R.groupoid.inverse) ≫ R.groupoid.target := by
    rw [Category.assoc, hτsource, Category.assoc, R.groupoid.target_inverse]
  let P : Tspec ⟶ pullback R.groupoid.source R.groupoid.target :=
    pullback.lift (f ≫ τ) (f ≫ R.groupoid.inverse) w
  have hPfst : P ≫ pullback.fst R.groupoid.source R.groupoid.target = f ≫ τ := by
    dsimp [P]
    rw [pullback.lift_fst]
  have hPsnd : P ≫ pullback.snd R.groupoid.source R.groupoid.target =
      f ≫ R.groupoid.inverse := by
    dsimp [P]
    rw [pullback.lift_snd]
  have hPfstPoint : (pullback.fst R.groupoid.source R.groupoid.target).left.base
      ((P.left.base) pL) = (f ≫ τ).left.base pL := by
    have h := congrArg
      (fun q : Scheme.Hom Tspec.left R.groupoid.arrows.left => q.base pL)
      (congrArg (fun q => q.left) hPfst)
    change ((pullback.fst R.groupoid.source R.groupoid.target).left.base ∘ P.left.base) pL = _
    simpa [Scheme.Hom.comp_apply] using h
  have hPsndPoint : (pullback.snd R.groupoid.source R.groupoid.target).left.base
      ((P.left.base) pL) = (f ≫ R.groupoid.inverse).left.base pL := by
    have h := congrArg
      (fun q : Scheme.Hom Tspec.left R.groupoid.arrows.left => q.base pL)
      (congrArg (fun q => q.left) hPsnd)
    change ((pullback.snd R.groupoid.source R.groupoid.target).left.base ∘ P.left.base) pL = _
    simpa [Scheme.Hom.comp_apply] using h
  let z : (pullback R.groupoid.source R.groupoid.target).left := P.left.base pL
  let m := pullback.map R.groupoid.source R.groupoid.target G₂.source G₂.target
    R.hom.mapArrows R.hom.mapArrows R.hom.mapObjects
    R.hom.map_source.symm R.hom.map_target.symm
  let tG := (overPullbackLeftIso G₂.source G₂.target).hom.base (m.left.base z)
  have hmFst : m ≫ pullback.fst G₂.source G₂.target =
      pullback.fst R.groupoid.source R.groupoid.target ≫ R.hom.mapArrows := by
    dsimp [m, pullback.map]
    rw [pullback.lift_fst]
  have hmSnd : m ≫ pullback.snd G₂.source G₂.target =
      pullback.snd R.groupoid.source R.groupoid.target ≫ R.hom.mapArrows := by
    dsimp [m, pullback.map]
    rw [pullback.lift_snd]
  have hfst : pullback.fst G₂.source.left G₂.target.left tG ∈ A := by
    have heval : pullback.fst G₂.source.left G₂.target.left tG =
        qR.base (τ.left.base y) := by
      calc
        pullback.fst G₂.source.left G₂.target.left tG =
            (pullback.fst G₂.source G₂.target).left.base (m.left.base z) :=
              overPullbackLeftIso_hom_fst_apply G₂.source G₂.target (m.left.base z)
        _ = qR.base ((pullback.fst R.groupoid.source R.groupoid.target).left.base z) := by
              have h := congrArg (fun f : Scheme.Hom
                  (pullback R.groupoid.source R.groupoid.target).left G₂.arrows.left => f.base z)
                (congrArg (fun f => f.left) hmFst)
              simpa [Scheme.Hom.comp_apply, qR] using h
        _ = qR.base (τ.left.base y) := by
              rw [show z = P.left.base pL from rfl, hPfstPoint]
              have hpoint : (f ≫ τ).left.base pL = τ.left.base y := by
                change τ.left.base (f.left.base pL) = τ.left.base y
                exact congrArg τ.left.base hfpoint
              exact congrArg qR.base hpoint
    rw [heval]
    exact hτyA
  have hsnd : pullback.snd G₂.source.left G₂.target.left tG ∈ A := by
    have heval : pullback.snd G₂.source.left G₂.target.left tG =
        qR.base (R.groupoid.inverse.left.base y) := by
      calc
        pullback.snd G₂.source.left G₂.target.left tG =
            (pullback.snd G₂.source G₂.target).left.base (m.left.base z) :=
              overPullbackLeftIso_hom_snd_apply G₂.source G₂.target (m.left.base z)
        _ = qR.base ((pullback.snd R.groupoid.source R.groupoid.target).left.base z) := by
              have h := congrArg (fun f : Scheme.Hom
                  (pullback R.groupoid.source R.groupoid.target).left G₂.arrows.left => f.base z)
                (congrArg (fun f => f.left) hmSnd)
              simpa [Scheme.Hom.comp_apply, qR] using h
        _ = qR.base (R.groupoid.inverse.left.base y) := by
              rw [show z = P.left.base pL from rfl, hPsndPoint]
              have hpoint : (f ≫ R.groupoid.inverse).left.base pL =
                  R.groupoid.inverse.left.base y := by
                change R.groupoid.inverse.left.base (f.left.base pL) =
                  R.groupoid.inverse.left.base y
                exact congrArg R.groupoid.inverse.left.base hfpoint
              exact congrArg qR.base hpoint
    rw [heval]
    exact hinvA
  have hcompA : G₂.comp.left.base ((overPullbackLeftIso G₂.source G₂.target).inv.base tG) ∈ A :=
    range_comp_of_isIso_mapObjects F hfst hsnd
  have hcompMap : qR.base (R.groupoid.comp.left.base z) =
      G₂.comp.left.base ((overPullbackLeftIso G₂.source G₂.target).inv.base tG) := by
    simpa [tG] using map_comp_point R.hom R.hom.map_source.symm R.hom.map_target.symm z
  have hcompPoint : R.groupoid.comp.left.base z = rR := by
    have hEq := congrArg
      (fun f : Scheme.Hom Tspec.left R.groupoid.arrows.left => f.base pL)
      (congrArg (fun f => f.left)
        (leftTranslation_comp_inverse R.groupoid a ha f))
    have : Subsingleton R.groupoid.objects.left := by
      rw [hRfield]
      infer_instance
    have htargetPoint : (f ≫ R.groupoid.target).left.base pL =
        R.groupoid.source.left.base rR := Subsingleton.elim _ _
    have hEq' : R.groupoid.comp.left.base (P.left.base pL) =
        (f.left ≫ R.groupoid.target.left ≫ a.left).base pL := by
      change ((R.groupoid.comp.left).base ∘ P.left.base) pL =
        ((f.left ≫ R.groupoid.target.left ≫ a.left).base) pL
      exact hEq
    change R.groupoid.comp.left.base (P.left.base pL) = rR
    calc
      R.groupoid.comp.left.base (P.left.base pL) =
          (f.left ≫ R.groupoid.target.left ≫ a.left).base pL := hEq'
      _ = a.left ((f.left ≫ R.groupoid.target.left).base pL) := by
        rfl
      _ = a.left (R.groupoid.source.left.base rR) := congrArg a.left htargetPoint
      _ = rR :=
        GroupoidScheme.sourceNormalizedArrow_apply R.groupoid k' hRfield rR
  have hrA : r ∈ A := by
    have hqrA : qR.base rR ∈ A := by
      rw [← hcompPoint, hcompMap]
      exact hcompA
    rw [hqr] at hqrA
    exact hqrA
  exact hrA

end AlgebraicGeometry
