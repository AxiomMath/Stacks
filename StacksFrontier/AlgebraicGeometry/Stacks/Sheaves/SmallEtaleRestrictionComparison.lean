module

public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.SmallEtaleRestriction
public import StacksFrontier.CategoryTheory.Sites.InheritedTopology.Functoriality
public import StacksFrontier.CategoryTheory.Sites.Localization.PushforwardAdjunction

/-!
# Inverse image and the small étale comparison maps

Let `F` be an étale sheaf on a category fibred in groupoids `p : 𝒳 ⥤ (Sch/S)_{fppf}`, let
`G : 𝒴 ⥤ 𝒳` be a 1-morphism of categories fibred in groupoids and let `y` be an object of `𝒴`.
The restriction of `G^{-1}F` to the small étale site at `y` is canonically the restriction of `F`
at `G y`, and the comparison maps of Stacks 06W2 and 06W3 match under that identification.

## Main definitions

* `CategoryTheory.Functor.liftIsoAlongEquivalence`: the isomorphism `d ≅ H.obj c` whose image
  under an equivalence `P` is a given isomorphism `P.obj d ≅ Q.obj c`, where `H ⋙ P = Q`.
* `CategoryTheory.Functor.invIsoInvCompOfPost` and `CategoryTheory.Functor.invIsoInvCompOfEq`:
  the quasi-inverse of `P` is the quasi-inverse of `H ⋙ P = Q` followed by `H`.
* `AlgebraicGeometry.Stack.restrictToSmallEtaleInverseImageIso` and
  `AlgebraicGeometry.Stack.restrictToSmallEtaleSheafInverseImageIso`: the restriction of `G^{-1}F`
  at `y` is the restriction of `F` at `G y`, as presheaves and as sheaves.

## Main results

* `AlgebraicGeometry.Stack.existsUnique_inverseImageComparisonLift`: the comparison arrow of `𝒳`
  between the cartesian lift at `G y` and the image of the cartesian lift at `y` exists and is
  unique.
* `AlgebraicGeometry.Stack.restrictToSmallEtaleInverseImageIso_app`: the components of the
  identification are restriction along that arrow.
* `AlgebraicGeometry.Stack.restrictionPushforwardComparison_comp_inverseImageIso`: the comparison
  maps of Stacks 06W2 for `ψ` and for `G ψ` agree under the identification.
* `AlgebraicGeometry.Stack.restrictionInverseImageComparison_comp_inverseImageIso`: the comparison
  maps of Stacks 06W3 for `ψ` and for `G ψ` agree under the identification.

## References

* [Stacks Project, Tag 075D](https://stacks.math.columbia.edu/tag/075D)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w v' w' t

namespace CategoryTheory.Functor

/-- Given an equivalence `P : D ⥤ E`, a functor `H : C ⥤ D` with `H ⋙ P = Q`, and an
isomorphism `P.obj d ≅ Q.obj c`, the arrow `d ≅ H.obj c` it is the image of under `P`. -/
noncomputable def liftIsoAlongEquivalence {C D E : Type*} [Category C] [Category D] [Category E]
    (P : D ⥤ E) [P.IsEquivalence] (H : C ⥤ D) (Q : C ⥤ E) (h : H ⋙ P = Q) (d : D) (c : C)
    (e : P.obj d ≅ Q.obj c) : d ≅ H.obj c :=
  let η : P.obj d ≅ P.obj (H.obj c) := e ≪≫ (eqToIso (Functor.congr_obj h c)).symm
  { hom := P.preimage η.hom
    inv := P.preimage η.inv
    hom_inv_id := by
      apply P.map_injective
      simp [η]
    inv_hom_id := by
      apply P.map_injective
      simp [η] }

/-- The image under `P` of the lifted isomorphism is the given one, transported along the
equality of functors. -/
lemma map_liftIsoAlongEquivalence_hom {C D E : Type*} [Category C] [Category D] [Category E]
    (P : D ⥤ E) [P.IsEquivalence] (H : C ⥤ D) (Q : C ⥤ E) (h : H ⋙ P = Q) (d : D) (c : C)
    (e : P.obj d ≅ Q.obj c) :
    P.map (liftIsoAlongEquivalence P H Q h d c e).hom =
      e.hom ≫ (eqToIso (Functor.congr_obj h c)).symm.hom := by
  simp [liftIsoAlongEquivalence]

/-- If `P` and `H ⋙ P` are both equivalences, then the quasi-inverse of `P` is the
quasi-inverse of `H ⋙ P` followed by `H`. -/
noncomputable def invIsoInvCompOfPost {C D E : Type*} [Category C] [Category D] [Category E]
    (P : D ⥤ E) [P.IsEquivalence] (H : C ⥤ D) [(H ⋙ P).IsEquivalence] :
    P.inv ≅ (H ⋙ P).inv ⋙ H := by
  classical
  refine NatIso.ofComponents (fun X =>
    liftIsoAlongEquivalence P H (H ⋙ P) rfl (P.inv.obj X) ((H ⋙ P).inv.obj X)
      (P.objObjPreimageIso X ≪≫ ((H ⋙ P).objObjPreimageIso X).symm)) ?_
  intro X Y f
  apply P.map_injective
  have hX : P.map (liftIsoAlongEquivalence P H (H ⋙ P) rfl
      (P.inv.obj X) ((H ⋙ P).inv.obj X)
      (P.objObjPreimageIso X ≪≫ ((H ⋙ P).objObjPreimageIso X).symm)).hom =
      (P.objObjPreimageIso X ≪≫ ((H ⋙ P).objObjPreimageIso X).symm).hom := by
    simp [liftIsoAlongEquivalence]
  have hY : P.map (liftIsoAlongEquivalence P H (H ⋙ P) rfl
      (P.inv.obj Y) ((H ⋙ P).inv.obj Y)
      (P.objObjPreimageIso Y ≪≫ ((H ⋙ P).objObjPreimageIso Y).symm)).hom =
      (P.objObjPreimageIso Y ≪≫ ((H ⋙ P).objObjPreimageIso Y).symm).hom := by
    simp [liftIsoAlongEquivalence]
  simp only [Functor.map_comp]
  rw [hY, hX]
  have hP : P.map (P.inv.map f) ≫ (P.objObjPreimageIso Y).hom =
      (P.objObjPreimageIso X).hom ≫ f := by
    change P.map (P.inv.map f) ≫ P.asEquivalence.counit.app Y =
      P.asEquivalence.counit.app X ≫ f
    exact P.asEquivalence.counit.naturality f
  have hQ : (H ⋙ P).map ((H ⋙ P).inv.map f) ≫ ((H ⋙ P).objObjPreimageIso Y).hom =
      ((H ⋙ P).objObjPreimageIso X).hom ≫ f := by
    change (H ⋙ P).map ((H ⋙ P).inv.map f) ≫ (H ⋙ P).asEquivalence.counit.app Y =
      (H ⋙ P).asEquivalence.counit.app X ≫ f
    exact (H ⋙ P).asEquivalence.counit.naturality f
  have hQinv : f ≫ ((H ⋙ P).objObjPreimageIso Y).inv =
      ((H ⋙ P).objObjPreimageIso X).inv ≫ (H ⋙ P).map ((H ⋙ P).inv.map f) := by
    apply (cancel_mono ((H ⋙ P).objObjPreimageIso Y).hom).1
    calc
      (f ≫ ((H ⋙ P).objObjPreimageIso Y).inv) ≫ ((H ⋙ P).objObjPreimageIso Y).hom = f := by
        simp
      _ = ((H ⋙ P).objObjPreimageIso X).inv ≫
          (((H ⋙ P).objObjPreimageIso X).hom ≫ f) := by simp
      _ = ((H ⋙ P).objObjPreimageIso X).inv ≫
          ((H ⋙ P).map ((H ⋙ P).inv.map f) ≫
            ((H ⋙ P).objObjPreimageIso Y).hom) := by rw [← hQ]
      _ = (((H ⋙ P).objObjPreimageIso X).inv ≫
          (H ⋙ P).map ((H ⋙ P).inv.map f)) ≫
            ((H ⋙ P).objObjPreimageIso Y).hom := (Category.assoc _ _ _).symm
  change (P.map (P.inv.map f) ≫
      (P.objObjPreimageIso Y).hom ≫ ((H ⋙ P).objObjPreimageIso Y).inv) =
    ((P.objObjPreimageIso X).hom ≫ ((H ⋙ P).objObjPreimageIso X).inv) ≫
      (H ⋙ P).map ((H ⋙ P).inv.map f)
  calc
    P.map (P.inv.map f) ≫
        ((P.objObjPreimageIso Y).hom ≫ ((H ⋙ P).objObjPreimageIso Y).inv) =
      (P.map (P.inv.map f) ≫ (P.objObjPreimageIso Y).hom) ≫
        ((H ⋙ P).objObjPreimageIso Y).inv := (Category.assoc _ _ _).symm
    _ = ((P.objObjPreimageIso X).hom ≫ f) ≫
        ((H ⋙ P).objObjPreimageIso Y).inv := by rw [hP]
    _ = (P.objObjPreimageIso X).hom ≫
        (f ≫ ((H ⋙ P).objObjPreimageIso Y).inv) := Category.assoc _ _ _
    _ = (P.objObjPreimageIso X).hom ≫
        (((H ⋙ P).objObjPreimageIso X).inv ≫
          (H ⋙ P).map ((H ⋙ P).inv.map f)) := by rw [hQinv]
    _ = ((P.objObjPreimageIso X).hom ≫ ((H ⋙ P).objObjPreimageIso X).inv) ≫
        (H ⋙ P).map ((H ⋙ P).inv.map f) := (Category.assoc _ _ _).symm

/-- The quasi-inverse of `P` is the quasi-inverse of `Q` followed by `H`, whenever
`H ⋙ P = Q` and both `P` and `Q` are equivalences. -/
noncomputable def invIsoInvCompOfEq {C D E : Type*} [Category C] [Category D] [Category E]
    (P : D ⥤ E) [P.IsEquivalence] (H : C ⥤ D) (Q : C ⥤ E) [Q.IsEquivalence] (h : H ⋙ P = Q) :
    P.inv ≅ Q.inv ⋙ H := by
  cases h
  exact invIsoInvCompOfPost P H

end CategoryTheory.Functor

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

/-- Restriction to a small étale site commutes canonically with inverse image along a 1-morphism
of categories fibred in groupoids: the restriction at `y` of the inverse image of `F` is the
restriction of `F` at `G y`. -/
@[stacks 075D "part (3), the identification"]
noncomputable def restrictToSmallEtaleInverseImageIso {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    {𝒴 : Type v'} [Category.{w'} 𝒴] (G : 𝒴 ⥤ 𝒳) (hGp : (G ⋙ p).IsFiberedInGroupoids)
    (hG : (G ⋙ p).IsFibredOneMorphism p G) (y : 𝒴)
    (F : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type t)) :
    letI : (G ⋙ p).IsFibered := hGp.isFibered
    letI : p.IsFibered := hp.isFibered
    letI := (hG.isContinuous_and_isCocontinuous_inheritedTopology
      ((etaleTopology B).over (B.obj hS))).1
    restrictToSmallEtale B E h S hS (G ⋙ p) hGp y
        ((G.sheafPushforwardContinuous (Type t)
          (associatedTopology B S hS (G ⋙ p) (etaleTopology B))
          (associatedTopology B S hS p (etaleTopology B))).obj F).obj ≅
      restrictToSmallEtale B E h S hS p hp (G.obj y) F.obj := by
  classical
  let J := (etaleTopology B).over (B.obj hS)
  letI : (G ⋙ p).IsFibered := hGp.isFibered
  letI : p.IsFibered := hp.isFibered
  letI := (hG.isContinuous_and_isCocontinuous_inheritedTopology J).1
  let P := Over.post (X := G.obj y) (p ⋙ Over.forget (B.obj hS))
  let H : Over y ⥤ Over (G.obj y) := Over.post (X := y) G
  let Q := Over.post (X := y) ((G ⋙ p) ⋙ Over.forget (B.obj hS))
  letI : P.IsEquivalence := isEquivalence_overPost B S hS p hp (G.obj y)
  letI : Q.IsEquivalence := isEquivalence_overPost B S hS (G ⋙ p) hGp y
  let α : P.inv ≅ Q.inv ⋙ H := Functor.invIsoInvCompOfEq P H Q rfl
  let β := (hG.inverseImageCompSheafToPresheafIso J (Type t)).app F
  let ι := smallEtaleInclusion B E h (p.obj (G.obj y)).left.1
    (contains_base B E h S hS p (G.obj y))
  refine NatIso.ofComponents (fun Wop ↦ ?_) ?_
  · let W := Wop.unop
    let V := ι.obj W
    let a := P.inv.obj V
    let b := Q.inv.obj V
    let e : a.left ≅ G.obj b.left := (Over.forget (G.obj y)).mapIso (α.app V)
    simpa [P, Q, H, ι, restrictToSmallEtale, presheafPullback] using
      (β.app (Opposite.op b.left) ≪≫ Functor.mapIso F.obj e.op)
  · intro W W' f
    let V := ι.obj W.unop
    let V' := ι.obj W'.unop
    let fV := ι.map f.unop
    let q := Q.inv.map fV
    let e : (P.inv.obj V).left ≅ ((Q.inv ⋙ H).obj V).left :=
      { hom := (α.app V).hom.left
        inv := (α.app V).inv.left
        hom_inv_id := congrArg Over.Hom.left (α.app V).hom_inv_id
        inv_hom_id := congrArg Over.Hom.left (α.app V).inv_hom_id }
    let e' : (P.inv.obj V').left ≅ ((Q.inv ⋙ H).obj V').left :=
      { hom := (α.app V').hom.left
        inv := (α.app V').inv.left
        hom_inv_id := congrArg Over.Hom.left (α.app V').hom_inv_id
        inv_hom_id := congrArg Over.Hom.left (α.app V').inv_hom_id }
    have hβ := β.hom.naturality q.left.op
    have hα := α.hom.naturality fV
    have hα' : (P.inv.map fV).left ≫ e.hom = e'.hom ≫ (H.map q).left := by
      have hh := congrArg Over.Hom.left hα
      simp only [Over.comp_left] at hh
      exact hh
    have hsections := congrArg (fun k ↦ F.obj.map k.op) hα'
    have hsections' :
        F.obj.map (H.map q).left.op ≫ F.obj.map e'.hom.op =
          F.obj.map e.hom.op ≫ F.obj.map ((P.inv.map fV).left).op := by
      calc
        F.obj.map (H.map q).left.op ≫ F.obj.map e'.hom.op =
            F.obj.map (e'.hom ≫ (H.map q).left).op := by
          rw [← Functor.map_comp, ← op_comp]
        _ = F.obj.map ((P.inv.map fV).left ≫ e.hom).op := hsections.symm
        _ = F.obj.map e.hom.op ≫ F.obj.map ((P.inv.map fV).left).op := by
          rw [← Functor.map_comp, ← op_comp]
    have hsectionsG :
        F.obj.map (G.map q.left).op ≫ F.obj.map e'.hom.op =
          F.obj.map e.hom.op ≫ F.obj.map ((P.inv.map fV).left).op := by
      dsimp [H] at hsections'
      exact hsections'
    let A := (G.sheafPushforwardContinuous (Type t)
      (associatedTopology B S hS (G ⋙ p) (etaleTopology B))
      (associatedTopology B S hS p (etaleTopology B)) ⋙
        sheafToPresheaf (associatedTopology B S hS (G ⋙ p) (etaleTopology B)) (Type t)).obj F
    let B' := (sheafToPresheaf (associatedTopology B S hS p (etaleTopology B)) (Type t) ⋙
      (Functor.whiskeringLeft 𝒴ᵒᵖ 𝒳ᵒᵖ (Type t)).obj G.op).obj F
    have hcomp : A.map q.left.op ≫
        β.hom.app (Opposite.op (Q.inv.obj V').left) ≫ F.obj.map e'.hom.op =
      β.hom.app (Opposite.op (Q.inv.obj V).left) ≫ F.obj.map e.hom.op ≫
        F.obj.map ((P.inv.map fV).left).op := by
      calc
        A.map q.left.op ≫ β.hom.app (Opposite.op (Q.inv.obj V').left) ≫
            F.obj.map e'.hom.op =
            (A.map q.left.op ≫ β.hom.app (Opposite.op (Q.inv.obj V').left)) ≫
              F.obj.map e'.hom.op := (Category.assoc _ _ _).symm
        _ = (β.hom.app (Opposite.op (Q.inv.obj V).left) ≫ B'.map q.left.op) ≫
              F.obj.map e'.hom.op := by rw [hβ]
        _ = β.hom.app (Opposite.op (Q.inv.obj V).left) ≫
              (B'.map q.left.op ≫ F.obj.map e'.hom.op) := Category.assoc _ _ _
        _ = β.hom.app (Opposite.op (Q.inv.obj V).left) ≫
              (F.obj.map e.hom.op ≫ F.obj.map ((P.inv.map fV).left).op) := by
            have hB : B'.map q.left.op = F.obj.map (G.map q.left).op := by
              simp [B', Functor.comp_map]
            calc
              β.hom.app (Opposite.op (Q.inv.obj V).left) ≫
                  (B'.map q.left.op ≫ F.obj.map e'.hom.op) =
                β.hom.app (Opposite.op (Q.inv.obj V).left) ≫
                  (F.obj.map (G.map q.left).op ≫ F.obj.map e'.hom.op) := by
                    simp only [hB]
              _ = β.hom.app (Opposite.op (Q.inv.obj V).left) ≫
                  (F.obj.map e.hom.op ≫ F.obj.map ((P.inv.map fV).left).op) :=
                congrArg (fun k ↦ β.hom.app (Opposite.op (Q.inv.obj V).left) ≫ k) hsectionsG
        _ = β.hom.app (Opposite.op (Q.inv.obj V).left) ≫ F.obj.map e.hom.op ≫
              F.obj.map ((P.inv.map fV).left).op := rfl
    change A.map q.left.op ≫ β.hom.app (Opposite.op (Q.inv.obj V').left) ≫
        F.obj.map e'.hom.op =
      β.hom.app (Opposite.op (Q.inv.obj V).left) ≫ F.obj.map e.hom.op ≫
        F.obj.map ((P.inv.map fV).left).op
    exact hcomp

/-- Over a small étale object there is exactly one arrow of `𝒳` from the cartesian lift at `G y` to
the image of the cartesian lift at `y` compatible with the structure morphisms and lying over the
canonical comparison of their bases. -/
@[stacks 075D "part (3), the unique comparison arrow"]
theorem existsUnique_inverseImageComparisonLift {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    {𝒴 : Type v'} [Category.{w'} 𝒴] (G : 𝒴 ⥤ 𝒳) (hGp : (G ⋙ p).IsFiberedInGroupoids) (y : 𝒴)
    (W : SmallEtale E (p.obj (G.obj y)).left.1 (contains_base B E h S hS p (G.obj y))) :
    let P := Over.post (X := G.obj y) (p ⋙ Over.forget (B.obj hS))
    let Q := Over.post (X := y) ((G ⋙ p) ⋙ Over.forget (B.obj hS))
    letI : P.IsEquivalence := isEquivalence_overPost B S hS p hp (G.obj y)
    letI : Q.IsEquivalence := isEquivalence_overPost B S hS (G ⋙ p) hGp y
    let V := (smallEtaleInclusion B E h (p.obj (G.obj y)).left.1
      (contains_base B E h S hS p (G.obj y))).obj W
    let a := P.inv.obj V
    let b := Q.inv.obj V
    ∃! φ : a.left ⟶ G.obj b.left,
      (φ ≫ G.map b.hom = a.hom) ∧
      ((p.map φ).left ≫ (Q.objObjPreimageIso V).hom.left =
        (P.objObjPreimageIso V).hom.left) := by
  classical
  dsimp only
  let P := Over.post (X := G.obj y) (p ⋙ Over.forget (B.obj hS))
  let Q := Over.post (X := y) ((G ⋙ p) ⋙ Over.forget (B.obj hS))
  let H : Over y ⥤ Over (G.obj y) := Over.post (X := y) G
  have hHPQ : H ⋙ P = Q := by rfl
  cases hHPQ
  let V := (smallEtaleInclusion B E h (p.obj (G.obj y)).left.1
    (contains_base B E h S hS p (G.obj y))).obj W
  let : P.IsEquivalence := isEquivalence_overPost B S hS p hp (G.obj y)
  let : Q.IsEquivalence := isEquivalence_overPost B S hS (G ⋙ p) hGp y
  let a := P.inv.obj V
  let b := Q.inv.obj V
  let e : P.obj a ≅ P.obj (H.obj b) :=
    P.objObjPreimageIso V ≪≫ (Q.objObjPreimageIso V).symm
  let u : a ≅ H.obj b :=
    { hom := P.preimage e.hom
      inv := P.preimage e.inv
      hom_inv_id := by apply P.map_injective; simp [e]
      inv_hom_id := by apply P.map_injective; simp [e] }
  have hcancel : e.hom ≫ (Q.objObjPreimageIso V).hom = (P.objObjPreimageIso V).hom := by
    show ((P.objObjPreimageIso V).hom ≫ (Q.objObjPreimageIso V).inv) ≫ _ = _
    simp [Category.assoc]
  have hcancelLeft : e.hom.left ≫ (Q.objObjPreimageIso V).hom.left =
      (P.objObjPreimageIso V).hom.left :=
    (Over.comp_left _ _ _ _ _).symm.trans (congrArg Over.Hom.left hcancel)
  have hm : (p.map u.hom.left).left = e.hom.left :=
    congrArg Over.Hom.left (show P.map u.hom = e.hom by simp [u])
  have hU : (p.map u.hom.left).left ≫ (Q.objObjPreimageIso V).hom.left =
      (P.objObjPreimageIso V).hom.left := hm.symm ▸ hcancelLeft
  refine ⟨u.hom.left, ⟨Over.w u.hom, hU⟩, fun φ hφ ↦ ?_⟩
  have hbase : p.map φ = p.map u.hom.left :=
    Over.OverMorphism.ext ((cancel_mono (Q.objObjPreimageIso V).hom.left).1 (hφ.2.trans hU.symm))
  have hLiftU : p.IsHomLift (p.map φ) u.hom.left := by
    rw [hbase]
    exact Functor.IsHomLift.map (p := p) u.hom.left
  have hcomp : φ ≫ G.map b.hom = u.hom.left ≫ G.map b.hom := hφ.1.trans (Over.w u.hom).symm
  exact @Functor.IsStronglyCartesian.ext _ _ _ _ p _ _ _ _
      (p.map (G.map b.hom)) (G.map b.hom) (hp.isStronglyCartesian (G.map b.hom))
      _ _ (p.map φ) φ u.hom.left (Functor.IsHomLift.map (p := p) φ) hLiftU hcomp

/-- On sections over a small étale object, the identification
`AlgebraicGeometry.Stack.restrictToSmallEtaleInverseImageIso` is restriction of `F` along the
unique comparison arrow of `AlgebraicGeometry.Stack.existsUnique_inverseImageComparisonLift`. -/
@[stacks 075D "part (3), the component formula"]
theorem restrictToSmallEtaleInverseImageIso_app {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    {𝒴 : Type v'} [Category.{w'} 𝒴] (G : 𝒴 ⥤ 𝒳) (hGp : (G ⋙ p).IsFiberedInGroupoids)
    (hG : (G ⋙ p).IsFibredOneMorphism p G) (y : 𝒴)
    (F : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type t))
    (W : SmallEtale E (p.obj (G.obj y)).left.1 (contains_base B E h S hS p (G.obj y))) :
    letI : (G ⋙ p).IsFibered := hGp.isFibered
    letI : p.IsFibered := hp.isFibered
    letI := (hG.isContinuous_and_isCocontinuous_inheritedTopology
      ((etaleTopology B).over (B.obj hS))).1
    let P := Over.post (X := G.obj y) (p ⋙ Over.forget (B.obj hS))
    let Q := Over.post (X := y) ((G ⋙ p) ⋙ Over.forget (B.obj hS))
    letI : P.IsEquivalence := isEquivalence_overPost B S hS p hp (G.obj y)
    letI : Q.IsEquivalence := isEquivalence_overPost B S hS (G ⋙ p) hGp y
    let V := (smallEtaleInclusion B E h (p.obj (G.obj y)).left.1
      (contains_base B E h S hS p (G.obj y))).obj W
    let a := P.inv.obj V
    let b := Q.inv.obj V
    ∀ φ : a.left ⟶ G.obj b.left, φ ≫ G.map b.hom = a.hom →
      (p.map φ).left ≫ (Q.objObjPreimageIso V).hom.left =
        (P.objObjPreimageIso V).hom.left →
      (restrictToSmallEtaleInverseImageIso B E h S hS p hp G hGp hG y F).hom.app
          (Opposite.op W) = F.obj.map φ.op := by
  classical
  dsimp only
  intro φ hcart hbase
  let P := Over.post (X := G.obj y) (p ⋙ Over.forget (B.obj hS))
  let Q := Over.post (X := y) ((G ⋙ p) ⋙ Over.forget (B.obj hS))
  let H : Over y ⥤ Over (G.obj y) := Over.post (X := y) G
  have hHPQ : H ⋙ P = Q := by rfl
  let : P.IsEquivalence := isEquivalence_overPost B S hS p hp (G.obj y)
  let : Q.IsEquivalence := isEquivalence_overPost B S hS (G ⋙ p) hGp y
  let V := (smallEtaleInclusion B E h (p.obj (G.obj y)).left.1
    (contains_base B E h S hS p (G.obj y))).obj W
  let a := P.inv.obj V
  let b := Q.inv.obj V
  let α := Functor.invIsoInvCompOfEq P H Q hHPQ
  let e := α.app V
  let : (H ⋙ P).IsEquivalence := by
    rw [hHPQ]
    infer_instance
  have hmap : P.map e.hom = (P.objObjPreimageIso V ≪≫ (Q.objObjPreimageIso V).symm).hom := by
    dsimp [e, α, Functor.invIsoInvCompOfEq]
    cases hHPQ
    exact Functor.map_liftIsoAlongEquivalence_hom P H (H ⋙ P) rfl
      (P.inv.obj V) ((H ⋙ P).inv.obj V)
      (P.objObjPreimageIso V ≪≫ ((H ⋙ P).objObjPreimageIso V).symm)
  have hEbase : (p.map e.hom.left).left ≫ (Q.objObjPreimageIso V).hom.left =
      (P.objObjPreimageIso V).hom.left := by
    have hm : P.map e.hom ≫ (Q.objObjPreimageIso V).hom = (P.objObjPreimageIso V).hom := by
      calc
        P.map e.hom ≫ (Q.objObjPreimageIso V).hom =
            (P.objObjPreimageIso V ≪≫ (Q.objObjPreimageIso V).symm).hom ≫
              (Q.objObjPreimageIso V).hom := by rw [hmap]; rfl
        _ = (P.objObjPreimageIso V).hom := by simp
    exact congrArg Over.Hom.left hm
  have hφ : φ = e.hom.left :=
    (existsUnique_inverseImageComparisonLift B E h S hS p hp G hGp y W).unique ⟨hcart, hbase⟩
      ⟨Over.w e.hom, hEbase⟩
  rw [hφ]
  simp only [restrictToSmallEtaleInverseImageIso, P, Q, H, α, e, V,
    restrictToSmallEtale, presheafPullback,
    Functor.IsFibredOneMorphism.inverseImageCompSheafToPresheafIso,
    Functor.sheafPushforwardContinuousCompSheafToPresheafIso]
  show F.obj.map ((Over.forget (G.obj y)).mapIso e).hom.op =
    F.obj.map (Over.Hom.left e.hom).op
  rfl

/-- The identification `AlgebraicGeometry.Stack.restrictToSmallEtaleInverseImageIso`, as an
isomorphism of sheaves. -/
@[stacks 075D "part (3), on sheaves"]
noncomputable def restrictToSmallEtaleSheafInverseImageIso {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    {𝒴 : Type v'} [Category.{w'} 𝒴] (G : 𝒴 ⥤ 𝒳) (hGp : (G ⋙ p).IsFiberedInGroupoids)
    (hG : (G ⋙ p).IsFibredOneMorphism p G) (y : 𝒴)
    (F : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type (max (u + 1) t))) :
    letI : (G ⋙ p).IsFibered := hGp.isFibered
    letI : p.IsFibered := hp.isFibered
    letI := (hG.isContinuous_and_isCocontinuous_inheritedTopology
      ((etaleTopology B).over (B.obj hS))).1
    restrictToSmallEtaleSheaf B E h S hS (G ⋙ p) hGp y
        ((G.sheafPushforwardContinuous (Type (max (u + 1) t))
          (associatedTopology B S hS (G ⋙ p) (etaleTopology B))
          (associatedTopology B S hS p (etaleTopology B))).obj F) ≅
      restrictToSmallEtaleSheaf B E h S hS p hp (G.obj y) F :=
  letI : (G ⋙ p).IsFibered := hGp.isFibered
  letI : p.IsFibered := hp.isFibered
  letI := (hG.isContinuous_and_isCocontinuous_inheritedTopology
    ((etaleTopology B).over (B.obj hS))).1
  (fullyFaithfulSheafToPresheaf
    (SmallEtale.topology E (p.obj (G.obj y)).left.1
      (contains_base B E h S hS p (G.obj y))) (Type (max (u + 1) t))).preimageIso
    (restrictToSmallEtaleInverseImageIso B E h S hS p hp G hGp hG y F)

/-- Transporting an isomorphism of presheaves to an isomorphism of sheaves along the fully
faithful inclusion does not change the underlying morphism of presheaves. -/
private lemma preimageIso_sheafToPresheaf_hom_hom {C : Type*} [Category C]
    (J : GrothendieckTopology C) {A : Type*} [Category A] {X Y : Sheaf J A}
    (e : X.obj ≅ Y.obj) :
    (((fullyFaithfulSheafToPresheaf J A).preimageIso e).hom).hom = e.hom :=
  (fullyFaithfulSheafToPresheaf J A).map_preimage e.hom

/-- If `fInv` is a left inverse of `f` and `g` factors `h` through `f`, then `g` is `h`
precomposed with `fInv`. -/
private theorem comp_eq_of_comp_left_inverse {C : Type*} [Category C] {X Y Z : C}
    (f : X ⟶ Y) (fInv : Y ⟶ X) (g : Y ⟶ Z) (k : X ⟶ Z)
    (hInv : fInv ≫ f = 𝟙 Y) (hfg : f ≫ g = k) : fInv ≫ k = g := by
  calc
    fInv ≫ k = fInv ≫ (f ≫ g) := congrArg (fun m ↦ fInv ≫ m) hfg.symm
    _ = (fInv ≫ f) ≫ g := (Category.assoc _ _ _).symm
    _ = g := by rw [hInv]; simp

/-- A four-fold composite `((f ≫ g) ≫ k) ≫ l` is `o ≫ q` when `k ≫ l = m`, `g ≫ m = n ≫ q` and
`f ≫ n = o`. -/
private theorem comp_rewrite_of_squares {C : Type*} [Category C] {A B C₁ D E : C}
    (f : A ⟶ B) (g : B ⟶ C₁) (k : C₁ ⟶ D) (l : D ⟶ E)
    {F : C} {m : C₁ ⟶ E} {n : B ⟶ F} {o : A ⟶ F} (q : F ⟶ E)
    (hk : k ≫ l = m) (gx : g ≫ m = n ≫ q) (fy : f ≫ n = o) :
    ((f ≫ g) ≫ k) ≫ l = o ≫ q := by
  calc
    ((f ≫ g) ≫ k) ≫ l = f ≫ (g ≫ (k ≫ l)) := by cat_disch
    _ = f ≫ (g ≫ m) := congrArg (fun r ↦ f ≫ (g ≫ r)) hk
    _ = f ≫ (n ≫ q) := congrArg (fun r ↦ f ≫ r) gx
    _ = (f ≫ n) ≫ q := by cat_disch
    _ = o ≫ q := congrArg (fun r ↦ r ≫ q) fy

/-- An arrow of a category fibred in groupoids is invertible once its base map, composed with an
isomorphism, is an isomorphism. -/
private theorem isIso_of_map_left_comp_eq {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) {X Y : 𝒳} (α : X ⟶ Y)
    {Z} (g : (p.obj Y).left ⟶ Z) (k : (p.obj X).left ⟶ Z) (hg : IsIso g) (hk : IsIso k)
    (h : (p.map α).left ≫ g = k) : IsIso α := by
  have : IsIso (p.map α) := by
    apply (isIso_iff_of_reflects_iso (p.map α) (Over.forget (B.obj hS))).mp
    have : IsIso ((p.map α).left ≫ g) := h ▸ hk
    have := hg
    simpa only [Over.forget_map] using IsIso.of_isIso_comp_right (p.map α).left g
  let : p.IsStronglyCartesian (p.map α) α := hp.isStronglyCartesian_homLift _ _
  exact Functor.IsStronglyCartesian.isIso_of_base_isIso p (p.map α) α

/-- The comparison maps of Stacks 06W2 for `ψ : y' ⟶ y` in `𝒴` and for its image `G ψ` in `𝒳`
agree under the identifications `AlgebraicGeometry.Stack.restrictToSmallEtaleInverseImageIso`. -/
@[stacks 075D "part (4), for the direct-image comparison of a presheaf of sets"]
theorem restrictionPushforwardComparison_comp_inverseImageIso {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    {𝒴 : Type v'} [Category.{w'} 𝒴] (G : 𝒴 ⥤ 𝒳) (hGp : (G ⋙ p).IsFiberedInGroupoids)
    (hG : (G ⋙ p).IsFibredOneMorphism p G) {y' y : 𝒴} (ψ : y' ⟶ y)
    (F : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type t)) :
    letI : (G ⋙ p).IsFibered := hGp.isFibered
    letI : p.IsFibered := hp.isFibered
    letI := (hG.isContinuous_and_isCocontinuous_inheritedTopology
      ((etaleTopology B).over (B.obj hS))).1
    let F' := (G.sheafPushforwardContinuous (Type t)
      (associatedTopology B S hS (G ⋙ p) (etaleTopology B))
      (associatedTopology B S hS p (etaleTopology B))).obj F
    let b := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p (G.map ψ))
    (restrictToSmallEtaleInverseImageIso B E h S hS p hp G hGp hG y F).hom ≫
        restrictionPushforwardComparison B E h S hS p hp (G.map ψ) F.obj =
      restrictionPushforwardComparison B E h S hS (G ⋙ p) hGp ψ F'.obj ≫
        Functor.whiskerLeft b.op
          (restrictToSmallEtaleInverseImageIso B E h S hS p hp G hGp hG y' F).hom := by
  let : (G ⋙ p).IsFibered := hGp.isFibered
  let : p.IsFibered := hp.isFibered
  let := (hG.isContinuous_and_isCocontinuous_inheritedTopology
    ((etaleTopology B).over (B.obj hS))).1
  let F' := (G.sheafPushforwardContinuous (Type t)
    (associatedTopology B S hS (G ⋙ p) (etaleTopology B))
    (associatedTopology B S hS p (etaleTopology B))).obj F
  let Uy := (p.obj (G.obj y)).left.1
  let Uy' := (p.obj (G.obj y')).left.1
  let hy : E.Contains Uy := contains_base B E h S hS p (G.obj y)
  let hy' : E.Contains Uy' := contains_base B E h S hS p (G.obj y')
  let b := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p (G.map ψ))
  let iy := restrictToSmallEtaleInverseImageIso B E h S hS p hp G hGp hG y F
  let iy' := restrictToSmallEtaleInverseImageIso B E h S hS p hp G hGp hG y' F
  ext W x
  show ((iy.hom.app W) ≫
      (restrictionPushforwardComparison B E h S hS p hp (G.map ψ) F.obj).app W) x =
    ((restrictionPushforwardComparison B E h S hS (G ⋙ p) hGp ψ F'.obj).app W ≫
      iy'.hom.app (Opposite.op (b.obj W.unop))) x
  let W₀ := W.unop
  let V := (smallEtaleInclusion B E h Uy hy).obj W₀
  let U := (smallEtaleInclusion B E h Uy' hy').obj (b.obj W₀)
  let P := Over.post (X := G.obj y) (p ⋙ Over.forget (B.obj hS))
  let P' := Over.post (X := G.obj y') (p ⋙ Over.forget (B.obj hS))
  let Q := Over.post (X := y) ((G ⋙ p) ⋙ Over.forget (B.obj hS))
  let Q' := Over.post (X := y') ((G ⋙ p) ⋙ Over.forget (B.obj hS))
  let : P.IsEquivalence := isEquivalence_overPost B S hS p hp (G.obj y)
  let : P'.IsEquivalence := isEquivalence_overPost B S hS p hp (G.obj y')
  let : Q.IsEquivalence := isEquivalence_overPost B S hS (G ⋙ p) hGp y
  let : Q'.IsEquivalence := isEquivalence_overPost B S hS (G ⋙ p) hGp y'
  let A := P.objPreimage V
  let A' := P'.objPreimage U
  let C := Q.objPreimage V
  let C' := Q'.objPreimage U
  let eP := P.objObjPreimageIso V
  let eP' := P'.objObjPreimageIso U
  let eQ := Q.objObjPreimageIso V
  let eQ' := Q'.objObjPreimageIso U
  have hQobjC : (Q.obj C).left = (p.obj (G.obj C.left)).left := by rfl
  have hQ'objC' : (Q'.obj C').left = (p.obj (G.obj C'.left)).left := by rfl
  have hPobjA : (P.obj A).left = (p.obj A.left).left := by rfl
  have hP'objA' : (P'.obj A').left = (p.obj A'.left).left := by rfl
  have hα : ∃! α : A.left ⟶ G.obj C.left,
      (α ≫ G.map C.hom = A.hom) ∧
        ((p.map α).left ≫ eQ.hom.left = eP.hom.left) := by
    simpa [A, C, P, Q, eP, eQ, U, V, Functor.inv] using
      existsUnique_inverseImageComparisonLift B E h S hS p hp G hGp y W₀
  have hα' : ∃! α : A'.left ⟶ G.obj C'.left,
      (α ≫ G.map C'.hom = A'.hom) ∧
        ((p.map α).left ≫ eQ'.hom.left = eP'.hom.left) := by
    simpa [A', C', P', Q', eP', eQ', U, V, Functor.inv] using
      existsUnique_inverseImageComparisonLift B E h S hS p hp G hGp y' (b.obj W₀)
  rcases hα with ⟨α, hα, -⟩
  rcases hα' with ⟨α', hα', -⟩
  have : IsIso eP.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eP.hom))
  have : IsIso eQ.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eQ.hom))
  have : IsIso eP'.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eP'.hom))
  have : IsIso eQ'.hom.left := inferInstanceAs (IsIso ((Over.forget _).map eQ'.hom))
  have : IsIso α := isIso_of_map_left_comp_eq B S hS p hp α eQ.hom.left eP.hom.left ‹_› ‹_› hα.2
  have : IsIso α' :=
    isIso_of_map_left_comp_eq B S hS p hp α' eQ'.hom.left eP'.hom.left ‹_› ‹_› hα'.2
  let fSite := pullback.fst W₀.obj.hom (smallEtaleBaseMorphism B E h S hS (G ⋙ p) ψ)
  let fScheme : U.left ⟶ V.left := ObjectProperty.homMk (E.inclusion.map fSite)
  let fBaseQ : (Q'.obj C').left ⟶ (Q.obj C).left := eQ'.hom.left ≫ fScheme ≫ eQ.inv.left
  let fBase : (p.obj (G.obj C'.left)).left ⟶ (p.obj (G.obj C.left)).left :=
    (eqToHom hQ'objC'.symm ≫ fBaseQ) ≫ eqToHom hQobjC
  let gBase : (p.obj (G.obj y')).left ⟶ (p.obj (G.obj y)).left :=
    ObjectProperty.homMk (E.inclusion.map (smallEtaleBaseMorphism B E h S hS p (G.map ψ)))
  have hfscheme : fScheme ≫ V.hom = U.hom ≫ gBase := by
    apply B.inclusion.map_injective
    show E.inclusion.map fSite ≫ E.inclusion.map W₀.obj.hom =
      E.inclusion.map (pullback.snd W₀.obj.hom
        (smallEtaleBaseMorphism B E h S hS (G ⋙ p) ψ)) ≫
      E.inclusion.map (smallEtaleBaseMorphism B E h S hS (G ⋙ p) ψ)
    rw [← Functor.map_comp, ← Functor.map_comp, pullback.condition]
  have hQinvObj : eQ.inv.left ≫ (p.map (G.map C.hom)).left = V.hom := by
    show eQ.inv.left ≫ (Q.obj C).hom = V.hom
    exact eQ.inv.w
  have hQ'homObj : eQ'.hom.left ≫ U.hom = (p.map (G.map C'.hom)).left := by
    show eQ'.hom.left ≫ U.hom = (Q'.obj C').hom
    exact eQ'.hom.w
  have hQC : (p.map (G.map C.hom)).left ≫ (p.obj (G.obj y)).hom =
      (p.obj (G.obj C.left)).hom := (p.map (G.map C.hom)).w
  have hQC' : (p.map (G.map C'.hom)).left ≫ (p.obj (G.obj y')).hom =
      (p.obj (G.obj C'.left)).hom := (p.map (G.map C'.hom)).w
  have hQcastmap : eqToHom hQobjC ≫ (p.map (G.map C.hom)).left = (Q.obj C).hom := by
    cases hQobjC
    rfl
  have hQ'castmap' : eqToHom hQ'objC'.symm ≫ (Q'.obj C').hom =
      (p.map (G.map C'.hom)).left := by
    cases hQ'objC'
    rfl
  have hQbasehom : eqToHom hQobjC ≫ (p.obj (G.obj C.left)).hom =
      (Q.obj C).hom ≫ (p.obj (G.obj y)).hom := by
    cases hQobjC
    show (p.obj (G.obj C.left)).hom =
      (p.map (G.map C.hom)).left ≫ (p.obj (G.obj y)).hom
    exact hQC.symm
  have hQ'basehom : eqToHom hQ'objC'.symm ≫
      ((Q'.obj C').hom ≫ (p.obj (G.obj y')).hom) = (p.obj (G.obj C'.left)).hom := by
    cases hQ'objC'
    show (p.map (G.map C'.hom)).left ≫ (p.obj (G.obj y')).hom =
      (p.obj (G.obj C'.left)).hom
    exact hQC'
  have hQ'homObjQ : eQ'.hom.left ≫ U.hom = (Q'.obj C').hom := eQ'.hom.w
  have hmidMap : fBaseQ ≫ (Q.obj C).hom = (Q'.obj C').hom ≫ gBase := by
    dsimp [fBaseQ]
    calc
      (eQ'.hom.left ≫ fScheme ≫ eQ.inv.left) ≫ (Q.obj C).hom =
          (eQ'.hom.left ≫ fScheme) ≫ (eQ.inv.left ≫ (Q.obj C).hom) := Category.assoc _ _ _
      _ = (eQ'.hom.left ≫ fScheme) ≫ V.hom :=
            congrArg (fun k ↦ (eQ'.hom.left ≫ fScheme) ≫ k) eQ.inv.w
      _ = (eQ'.hom.left ≫ U.hom) ≫ gBase := by
            simpa only [Category.assoc] using
              congrArg (fun k ↦ eQ'.hom.left ≫ k) hfscheme
      _ = (Q'.obj C').hom ≫ gBase := congrArg (fun k ↦ k ≫ gBase) hQ'homObjQ
  have hψbase : gBase ≫ (p.obj (G.obj y)).hom = (p.obj (G.obj y')).hom :=
    B.inclusion.map_injective (congrArg B.inclusion.map (Over.w (p.map (G.map ψ))))
  have hmidHom : fBaseQ ≫ (Q.obj C).hom ≫ (p.obj (G.obj y)).hom =
      (Q'.obj C').hom ≫ (p.obj (G.obj y')).hom := by
    calc
      fBaseQ ≫ (Q.obj C).hom ≫ (p.obj (G.obj y)).hom =
          (Q'.obj C').hom ≫ gBase ≫ (p.obj (G.obj y)).hom :=
            congrArg (fun k ↦ k ≫ (p.obj (G.obj y)).hom) hmidMap
      _ = (Q'.obj C').hom ≫ (p.obj (G.obj y')).hom := by
            calc
              ((Q'.obj C').hom ≫ gBase) ≫ (p.obj (G.obj y)).hom =
                  (Q'.obj C').hom ≫ (gBase ≫ (p.obj (G.obj y)).hom) := Category.assoc _ _ _
              _ = (Q'.obj C').hom ≫ (p.obj (G.obj y')).hom :=
                    congrArg (fun k ↦ (Q'.obj C').hom ≫ k) hψbase
  have hbasecompat : fBase ≫ (p.obj (G.obj C.left)).hom = (p.obj (G.obj C'.left)).hom := by
    dsimp [fBase]
    simp only [Category.assoc]
    calc
      (eqToHom hQ'objC'.symm ≫ fBaseQ ≫ eqToHom hQobjC) ≫ (p.obj (G.obj C.left)).hom =
        eqToHom hQ'objC'.symm ≫ (fBaseQ ≫
          ((eqToHom hQobjC ≫ (p.obj (G.obj C.left)).hom))) := by simp only [Category.assoc]
      _ = eqToHom hQ'objC'.symm ≫
          (fBaseQ ≫ ((Q.obj C).hom ≫ (p.obj (G.obj y)).hom)) := by rw [hQbasehom]
      _ = (p.obj (G.obj C'.left)).hom := by
            rw [hmidHom]
            exact hQ'basehom
  let fBig : p.obj (G.obj C'.left) ⟶ p.obj (G.obj C.left) :=
    Over.homMk fBase (by
      dsimp [fBase]
      exact hbasecompat)
  have hbaseTriangle : fBase ≫ (p.map (G.map C.hom)).left =
      (p.map (G.map C'.hom)).left ≫ gBase := by
    dsimp [fBase]
    simp only [Category.assoc]
    calc
      (eqToHom hQ'objC'.symm ≫ fBaseQ ≫ eqToHom hQobjC) ≫ (p.map (G.map C.hom)).left =
        eqToHom hQ'objC'.symm ≫ (fBaseQ ≫
          (eqToHom hQobjC ≫ (p.map (G.map C.hom)).left)) := by simp only [Category.assoc]
      _ = eqToHom hQ'objC'.symm ≫ (fBaseQ ≫ (Q.obj C).hom) := by rw [hQcastmap]
      _ = eqToHom hQ'objC'.symm ≫ ((Q'.obj C').hom ≫ gBase) := by rw [hmidMap]
      _ = (p.map (G.map C'.hom)).left ≫ gBase := by
            calc
              eqToHom hQ'objC'.symm ≫ ((Q'.obj C').hom ≫ gBase) =
                  (eqToHom hQ'objC'.symm ≫ (Q'.obj C').hom) ≫ gBase :=
                    (Category.assoc _ _ _).symm
              _ = (p.map (G.map C'.hom)).left ≫ gBase :=
                    congrArg (fun k ↦ k ≫ gBase) hQ'castmap'
  have hgBase : gBase = (p.map (G.map ψ)).left := by
    dsimp [gBase, smallEtaleBaseMorphism]
    rfl
  have htri : fBig ≫ (G ⋙ p).map C.hom = (G ⋙ p).map (C'.hom ≫ ψ) := by
    apply Over.OverMorphism.ext
    simpa only [fBig, Over.homMk_left, Functor.comp_obj, Functor.comp_map,
      Over.comp_left, Functor.map_comp, hgBase] using hbaseTriangle
  obtain ⟨β, hβ, -⟩ := hGp.unique_lift C.hom (C'.hom ≫ ψ) fBig htri
  let χ := α' ≫ G.map β ≫ inv α
  have hχ : χ ≫ A.hom = A'.hom ≫ G.map ψ := by
    have hinv : inv α ≫ A.hom = G.map C.hom := by
      calc
        inv α ≫ A.hom = inv α ≫ (α ≫ G.map C.hom) := by rw [hα.1]
        _ = G.map C.hom := by simp
    calc
      χ ≫ A.hom = α' ≫ (G.map β ≫ (inv α ≫ A.hom)) := by simp [χ, Category.assoc]
      _ = α' ≫ (G.map β ≫ G.map C.hom) := by rw [hinv]
      _ = α' ≫ G.map (β ≫ C.hom) := by rw [Functor.map_comp]
      _ = α' ≫ G.map (C'.hom ≫ ψ) := by rw [hβ.2]
      _ = (α' ≫ G.map C'.hom) ≫ G.map ψ := by rw [Functor.map_comp, Category.assoc]
      _ = A'.hom ≫ G.map ψ := by rw [hα'.1]
  have hχfac : χ ≫ α = α' ≫ G.map β := by
    dsimp [χ]
    simp [Category.assoc]
  have hβbaseRaw : fBig.left ≫ eQ.hom.left = eQ'.hom.left ≫ fScheme := by
    show fBase ≫ eQ.hom.left = eQ'.hom.left ≫ fScheme
    have hQinvhom : eQ.inv.left ≫ eQ.hom.left = 𝟙 _ := congrArg Over.Hom.left eQ.inv_hom_id
    dsimp [fBase]
    calc
      (eQ'.hom.left ≫ fScheme ≫ eQ.inv.left) ≫ eQ.hom.left =
          (eQ'.hom.left ≫ fScheme) ≫ (eQ.inv.left ≫ eQ.hom.left) := Category.assoc _ _ _
      _ = (eQ'.hom.left ≫ fScheme) ≫ 𝟙 _ :=
        congrArg (fun k ↦ (eQ'.hom.left ≫ fScheme) ≫ k) hQinvhom
      _ = eQ'.hom.left ≫ fScheme := by simp
  have hβmap : (p.map (G.map β)).left = fBig.left := by
    simpa only [Functor.comp_map] using congrArg Over.Hom.left hβ.1
  have hβbaseRaw' : (p.map (G.map β)).left ≫ eQ.hom.left = eQ'.hom.left ≫ fScheme := by
    simpa only [hβmap] using hβbaseRaw
  have hincl : ∀ {X Y} (x : X ⟶ Y) (y : Y ⟶ V.left) (z : X ⟶ U.left),
      x ≫ y = z ≫ fScheme →
        B.inclusion.map x ≫ B.inclusion.map y = B.inclusion.map z ≫ E.inclusion.map fSite :=
    fun x y z hxy ↦ by rw [← Functor.map_comp, hxy, Functor.map_comp]; rfl
  have hβbase :
      B.inclusion.map ((G ⋙ p).map β).left ≫ B.inclusion.map eQ.hom.left =
        B.inclusion.map eQ'.hom.left ≫ E.inclusion.map fSite :=
    hincl _ _ _ (by rw [hβ.1]; exact hβbaseRaw)
  have hχbase :
      B.inclusion.map (p.map χ).left ≫ B.inclusion.map eP.hom.left =
        B.inclusion.map eP'.hom.left ≫ E.inclusion.map fSite := by
    cases hQobjC
    cases hQ'objC'
    cases hPobjA
    cases hP'objA'
    have hcancel : (p.map (inv α)).left ≫ (p.map α).left = 𝟙 _ :=
      congrArg Over.Hom.left (show p.map (inv α) ≫ p.map α = 𝟙 _ by simp)
    have hinvαRaw : (p.map (inv α)).left ≫ eP.hom.left = eQ.hom.left :=
      comp_eq_of_comp_left_inverse (p.map α).left (p.map (inv α)).left eQ.hom.left
        eP.hom.left hcancel hα.2
    have hχRaw : (p.map χ).left =
        ((p.map α').left ≫ (p.map (G.map β)).left) ≫ (p.map (inv α)).left := by
      simp [χ, Functor.map_comp, Over.comp_left, Category.assoc]
    refine hincl _ _ _ ((congrArg (· ≫ eP.hom.left) hχRaw).trans ?_)
    exact (by cat_disch : _ = _).trans
        (comp_rewrite_of_squares (p.map α').left (p.map (G.map β)).left
          (p.map (inv α)).left eP.hom.left (q := fScheme)
          hinvαRaw hβbaseRaw' hα'.2)
  have hcmpX := restrictionPushforwardComparison_app B E h S hS p hp
    (G.map ψ) F.obj W₀ χ hχ hχbase
  have hcmpY := restrictionPushforwardComparison_app B E h S hS (G ⋙ p) hGp
    ψ F'.obj W₀ β hβ.2 hβbase
  have hcmpXW : (restrictionPushforwardComparison B E h S hS p hp
      (G.map ψ) F.obj).app W = F.obj.map χ.op := by
    simpa [W₀] using hcmpX
  have hcmpYW : (restrictionPushforwardComparison B E h S hS (G ⋙ p) hGp
      ψ F'.obj).app W = F'.obj.map β.op := hcmpY
  have hiy := restrictToSmallEtaleInverseImageIso_app
    B E h S hS p hp G hGp hG y F W₀ α hα.1 hα.2
  have hiy' := restrictToSmallEtaleInverseImageIso_app
    B E h S hS p hp G hGp hG y' F (b.obj W₀) α' hα'.1 hα'.2
  have hiyMap : iy.hom.app (Opposite.op W₀) = F.obj.map α.op := hiy
  have hiy'Map : iy'.hom.app (Opposite.op (b.obj W₀)) = F.obj.map α'.op := hiy'
  have hiyMapW : iy.hom.app W = F.obj.map α.op := by simpa [W₀] using hiyMap
  have hFMap : F'.obj.map β.op = F.obj.map (G.map β).op := by rfl
  have hχfacOp : α.op ≫ χ.op = (G.map β).op ≫ α'.op := by
    rw [← op_comp, ← op_comp, hχfac]
  rw [hcmpXW, hcmpYW, hiyMapW, hiy'Map, hFMap]
  calc
    F.obj.map χ.op (F.obj.map α.op x) = (F.obj.map α.op ≫ F.obj.map χ.op) x := rfl
    _ = F.obj.map (α.op ≫ χ.op) x := by rw [Functor.map_comp]
    _ = F.obj.map ((G.map β).op ≫ α'.op) x := by rw [hχfacOp]
    _ = (F.obj.map (G.map β).op ≫ F.obj.map α'.op) x := by rw [Functor.map_comp]
    _ = F.obj.map α'.op (F.obj.map (G.map β).op x) := rfl

/-- The comparison maps of Stacks 06W3 for `ψ : y' ⟶ y` in `𝒴` and for its image `G ψ` in `𝒳`
agree under the identifications
`AlgebraicGeometry.Stack.restrictToSmallEtaleSheafInverseImageIso`. -/
@[stacks 075D "part (4)"]
theorem restrictionInverseImageComparison_comp_inverseImageIso {𝒳 : Type v} [Category.{w} 𝒳]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
    {𝒴 : Type v'} [Category.{w'} 𝒴] (G : 𝒴 ⥤ 𝒳) (hGp : (G ⋙ p).IsFiberedInGroupoids)
    (hG : (G ⋙ p).IsFibredOneMorphism p G) {y' y : 𝒴} (ψ : y' ⟶ y)
    (F : Sheaf (associatedTopology B S hS p (etaleTopology B)) (Type (max (u + 1) t))) :
    letI : (G ⋙ p).IsFibered := hGp.isFibered
    letI : p.IsFibered := hp.isFibered
    letI := (hG.isContinuous_and_isCocontinuous_inheritedTopology
      ((etaleTopology B).over (B.obj hS))).1
    let F' := (G.sheafPushforwardContinuous (Type (max (u + 1) t))
      (associatedTopology B S hS (G ⋙ p) (etaleTopology B))
      (associatedTopology B S hS p (etaleTopology B))).obj F
    let a := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS (G ⋙ p) ψ)
    letI : a.IsContinuous
        (SmallEtale.topology E (p.obj (G.obj y)).left.1
          (contains_base B E h S hS p (G.obj y)))
        (SmallEtale.topology E (p.obj (G.obj y')).left.1
          (contains_base B E h S hS p (G.obj y'))) :=
      smallEtaleBaseChange_isContinuous E (smallEtaleBaseMorphism B E h S hS (G ⋙ p) ψ)
    let iy := restrictToSmallEtaleSheafInverseImageIso B E h S hS p hp G hGp hG y F
    let iy' := restrictToSmallEtaleSheafInverseImageIso B E h S hS p hp G hGp hG y' F
    (a.sheafPullback (Type (max (u + 1) t))
          (SmallEtale.topology E (p.obj (G.obj y)).left.1
            (contains_base B E h S hS p (G.obj y)))
          (SmallEtale.topology E (p.obj (G.obj y')).left.1
            (contains_base B E h S hS p (G.obj y')))).map iy.hom ≫
        restrictionInverseImageComparison B E h S hS p hp (G.map ψ) F =
      restrictionInverseImageComparison B E h S hS (G ⋙ p) hGp ψ F' ≫ iy'.hom := by
  let : (G ⋙ p).IsFibered := hGp.isFibered
  let : p.IsFibered := hp.isFibered
  let := (hG.isContinuous_and_isCocontinuous_inheritedTopology
    ((etaleTopology B).over (B.obj hS))).1
  let F' := (G.sheafPushforwardContinuous (Type (max (u + 1) t))
    (associatedTopology B S hS (G ⋙ p) (etaleTopology B))
    (associatedTopology B S hS p (etaleTopology B))).obj F
  let Uy := (p.obj (G.obj y)).left.1
  let Uy' := (p.obj (G.obj y')).left.1
  let hy : E.Contains Uy := contains_base B E h S hS p (G.obj y)
  let hy' : E.Contains Uy' := contains_base B E h S hS p (G.obj y')
  let Jy := SmallEtale.topology E Uy hy
  let Jy' := SmallEtale.topology E Uy' hy'
  let Iy := restrictToSmallEtaleSheaf B E h S hS (G ⋙ p) hGp y F'
  let Iy' := restrictToSmallEtaleSheaf B E h S hS (G ⋙ p) hGp y' F'
  let Fy := restrictToSmallEtaleSheaf B E h S hS p hp (G.obj y) F
  let Fy' := restrictToSmallEtaleSheaf B E h S hS p hp (G.obj y') F
  let iy : Iy ≅ Fy := restrictToSmallEtaleSheafInverseImageIso B E h S hS p hp G hGp hG y F
  let iy' : Iy' ≅ Fy' := restrictToSmallEtaleSheafInverseImageIso B E h S hS p hp G hGp hG y' F
  let b := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p (G.map ψ))
  let adj := b.sheafAdjunctionContinuous (Type (max (u + 1) t)) Jy Jy'
  let cX : Fy ⟶ (b.sheafPushforwardContinuous (Type (max (u + 1) t)) Jy Jy').obj Fy' :=
    Sheaf.homEquiv.symm (restrictionPushforwardComparison B E h S hS p hp (G.map ψ) F.obj)
  let cI : Iy ⟶ (b.sheafPushforwardContinuous (Type (max (u + 1) t)) Jy Jy').obj Iy' :=
    Sheaf.homEquiv.symm (restrictionPushforwardComparison B E h S hS (G ⋙ p) hGp ψ F'.obj)
  have hpull :
      (adj.homEquiv Fy Fy') (restrictionInverseImageComparison B E h S hS p hp (G.map ψ) F) =
        cX := by
    show (adj.homEquiv Fy Fy') ((adj.homEquiv Fy Fy').symm cX) = _
    exact (adj.homEquiv Fy Fy').apply_symm_apply _
  have hcomp : restrictionInverseImageComparison B E h S hS (G ⋙ p) hGp ψ F' =
      (adj.homEquiv Iy Iy').symm cI := by
    rfl
  have hcompAdj :
      (adj.homEquiv Iy Iy') (restrictionInverseImageComparison B E h S hS (G ⋙ p) hGp ψ F') =
        cI := by
    rw [hcomp]
    simp
  have hnat := adj.homEquiv_naturality_right
    (restrictionInverseImageComparison B E h S hS (G ⋙ p) hGp ψ F') iy'.hom
  have hpush : iy.hom ≫ cX =
        cI ≫ (b.sheafPushforwardContinuous (Type (max (u + 1) t)) Jy Jy').map iy'.hom := by
    apply Sheaf.hom_ext
    have hiyhom : iy.hom.hom =
        (restrictToSmallEtaleInverseImageIso B E h S hS p hp G hGp hG y F).hom :=
      preimageIso_sheafToPresheaf_hom_hom _ _
    have hiy'hom : iy'.hom.hom =
        (restrictToSmallEtaleInverseImageIso B E h S hS p hp G hGp hG y' F).hom :=
      preimageIso_sheafToPresheaf_hom_hom _ _
    show iy.hom.hom ≫ restrictionPushforwardComparison B E h S hS p hp (G.map ψ) F.obj =
      restrictionPushforwardComparison B E h S hS (G ⋙ p) hGp ψ F'.obj ≫
        Functor.whiskerLeft b.op iy'.hom.hom
    rw [hiyhom, hiy'hom]
    exact restrictionPushforwardComparison_comp_inverseImageIso
      B E h S hS p hp G hGp hG ψ F
  show (b.sheafPullback (Type (max (u + 1) t)) Jy Jy').map iy.hom ≫
      restrictionInverseImageComparison B E h S hS p hp (G.map ψ) F =
    restrictionInverseImageComparison B E h S hS (G ⋙ p) hGp ψ F' ≫ iy'.hom
  apply (adj.homEquiv Iy Fy').injective
  rw [adj.homEquiv_naturality_left iy.hom, hpull, hpush, ← hcompAdj]
  exact hnat.symm

end AlgebraicGeometry.Stack

end
