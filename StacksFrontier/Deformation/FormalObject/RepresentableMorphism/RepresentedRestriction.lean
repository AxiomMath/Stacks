module

public import Mathlib.CategoryTheory.Elements
public import Mathlib.CategoryTheory.FiberedCategory.BasedCategory
public import Mathlib.CategoryTheory.FiberedCategory.Fiber
public import Mathlib.CategoryTheory.FiberedCategory.Fibered
public import StacksCore.CategoryTheory.FiberedInGroupoidsEquiv
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedCategory.EquivalenceInvariance
public import StacksFrontier.Deformation.FormalObject.HomEquivalenceMain
public import StacksFrontier.Deformation.Groupoid.BaseCategory
public import StacksFrontier.Deformation.Predeformation.Basic
public import StacksFrontier.Deformation.FormalObject.RepresentableMorphism.Evaluation

/-!
# Restriction of the functor represented by a complete local algebra (Stacks 06SK)

The restriction of the represented functor is the unit of the completion adjunction of Stacks
06HA, so morphisms out of it into `p` correspond to morphisms out of `R` into the completion
of `p`. This file identifies the restricted represented functor with the strict restriction
of its category of elements, and compares the two presentations of morphisms out of it.

## Implementation notes

The restricted represented functor is `Deformation.restrictedCoyoneda`. Its associated
cofibered set is the category of elements.

## References

* [Stacks Project, Tag 06SK](https://stacks.math.columbia.edu/tag/06SK)
-/

@[expose] public section

open CategoryTheory

universe u v w uF vF

namespace Deformation

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The functor from the strict restriction of the functor represented by `R` to the elements
of the restricted represented functor of `R`, inverse to `restrictedRepresentableInclusion R`. -/
public def representedRestrictionInverse
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    Restriction (p := representedProjection R) ⥤
      (restrictedCoyoneda R).Elements := by
  refine
    { obj := fun X => (restrictedCoyoneda R).elementsMk X.base (X.obj.val ≫ eqToHom X.obj_eq)
      map := fun {X Y} f => Functor.Elements.homMk f.base (by
        have hobj : X.obj.2 ≫ f.obj.hom = Y.obj.2 := by
          simpa using f.obj.map_val
        change (X.obj.2 ≫ eqToHom X.obj_eq) ≫
          artinianToComplete.map f.base = Y.obj.2 ≫ eqToHom Y.obj_eq
        calc
          _ = X.obj.2 ≫ (eqToHom X.obj_eq ≫
              artinianToComplete.map f.base) := by simp [Category.assoc]
          _ = X.obj.2 ≫ (f.obj.hom ≫ eqToHom Y.obj_eq) := by
            rw [f.comm]
            rfl
          _ = (X.obj.2 ≫ f.obj.hom) ≫ eqToHom Y.obj_eq := by simp [Category.assoc]
          _ = Y.obj.2 ≫ eqToHom Y.obj_eq := by rw [hobj])
      map_id := ?_
      map_comp := ?_ }
  · intro X
    exact Functor.Elements.hom_ext rfl
  · intro X Y Z f g
    exact Functor.Elements.hom_ext rfl

/-- The isomorphism between an object of the strict restriction and its image under the inverse
followed by the inclusion. -/
public noncomputable def representedRestrictionCounitIso
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (X : Restriction (p := representedProjection R)) :
    (restrictedRepresentableInclusion R).obj
        ((representedRestrictionInverse R).obj X) ≅ X := by
  cases X with
  | mk obj base obj_eq =>
    cases obj with
    | @mk A α =>
      cases obj_eq
      rfl

/-- The equivalence between the elements of the restricted represented functor of `R` and the
strict restriction of the functor represented by `R` to Artinian algebras. -/
public noncomputable def representedRestrictionEquivalence
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    (restrictedCoyoneda R).Elements ≌
      Restriction (p := representedProjection R) where
  functor := (restrictedRepresentableInclusion R).toFunctor
  inverse := representedRestrictionInverse R
  unitIso := NatIso.ofComponents (fun X => Iso.refl X)
  counitIso := NatIso.ofComponents (representedRestrictionCounitIso R) (by
    intro X Y f
    cases X with
    | mk Xobj Xbase Xeq =>
      cases Y with
      | mk Yobj Ybase Yeq =>
        cases Xobj with
        | @mk XA Xα =>
          cases Yobj with
          | @mk YA Yα =>
            cases Xeq
            cases Yeq
            apply Restriction.Hom.ext
            · apply Functor.Elements.hom_ext
              change artinianToComplete.map f.base = f.obj.hom
              simpa [representedProjection, Functor.Elements.π] using f.comm
            · change f.base = f.base
              rfl)
  functor_unitIso_comp := by
    intro X
    rfl

/-- The functor `representedRestrictionInverse R` as a based functor. -/
public def representedRestrictionInverseBased
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    BasedFunctor
      (BasedCategory.ofFunctor
        (Restriction.projection (p := representedProjection R)))
      (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R))) where
  toFunctor := representedRestrictionInverse R
  w := rfl

/-- The unit isomorphism of `representedRestrictionBasedEquivalence R`, as an isomorphism of
based functors. -/
public noncomputable def representedRestrictionUnitBasedIso
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    (BasedFunctor.id (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R)))) ≅
      (restrictedRepresentableInclusion R).comp
        (representedRestrictionInverseBased R) := by
  apply BasedNatIso.mkNatIso (representedRestrictionEquivalence R).unitIso
  intro X
  change (Functor.Elements.π (restrictedCoyoneda R)).IsHomLift
    (𝟙 ((Functor.Elements.π (restrictedCoyoneda R)).obj X)) (𝟙 X)
  exact IsHomLift.map (p := Functor.Elements.π (restrictedCoyoneda R)) (𝟙 X)

/-- The counit isomorphism of `representedRestrictionBasedEquivalence R`, as an isomorphism of
based functors. -/
public noncomputable def representedRestrictionCounitBasedIso
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    (representedRestrictionInverseBased R).comp (restrictedRepresentableInclusion R) ≅
      (BasedFunctor.id (BasedCategory.ofFunctor
        (Restriction.projection (p := representedProjection R)))) := by
  apply BasedNatIso.mkNatIso (representedRestrictionEquivalence R).counitIso
  intro X
  change (Restriction.projection (p := representedProjection R)).IsHomLift
    (𝟙 X.base) ((representedRestrictionCounitIso R X).hom)
  have hmap : (Restriction.projection (p := representedProjection R)).map
      ((representedRestrictionCounitIso R X).hom) = 𝟙 X.base := by
    cases X with
    | mk obj base obj_eq =>
      cases obj with
      | @mk A α =>
        cases obj_eq
        rfl
  exact hmap ▸ IsHomLift.map
    (p := Restriction.projection (p := representedProjection R))
    ((representedRestrictionCounitIso R X).hom)

/-- Right whiskering of an isomorphism of based functors by a based functor. -/
public def basedIsoWhiskerRight
    {S : Type*} [Category S] {A B C : BasedCategory S}
    {F G : A ⥤ᵇ B} (e : F ≅ G)
    (H : B ⥤ᵇ C) : (F.comp H) ≅ (G.comp H) where
  hom := BasedCategory.whiskerRight e.hom H
  inv := BasedCategory.whiskerRight e.inv H
  hom_inv_id := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext X
    have he : e.hom.app X ≫ e.inv.app X = 𝟙 (F.obj X) := by
      have hh := congrArg (fun η : F ⟶ F => η.app X) e.hom_inv_id
      exact hh
    change H.toFunctor.map (e.hom.app X) ≫ H.toFunctor.map (e.inv.app X) = _
    rw [← H.toFunctor.map_comp, he]
    simp [BasedFunctor.comp]
  inv_hom_id := by
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext X
    have he : e.inv.app X ≫ e.hom.app X = 𝟙 (G.obj X) := by
      have hh := congrArg (fun η : G ⟶ G => η.app X) e.inv_hom_id
      exact hh
    change H.toFunctor.map (e.inv.app X) ≫ H.toFunctor.map (e.hom.app X) = _
    rw [← H.toFunctor.map_comp, he]
    simp [BasedFunctor.comp]

/-- The equivalence `representedRestrictionEquivalence R` as an equivalence of based categories. -/
public noncomputable def representedRestrictionBasedEquivalence
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    BasedCategory.Equivalence
      (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor
        (Restriction.projection (p := representedProjection R))) where
  functor := restrictedRepresentableInclusion R
  inverse := representedRestrictionInverseBased R
  unitIso := (representedRestrictionUnitBasedIso R).symm
  counitIso := representedRestrictionCounitBasedIso R

/-- Precomposition with an equivalence of based categories satisfying the triangle identity
`htriangle` is an equivalence of the categories of based functors. -/
public noncomputable def basedPrecompositionEquivalence
    {S : Type*} [Category S] {A B C : BasedCategory S}
    (e : BasedCategory.Equivalence A B)
    (htriangle : ∀ X : A.obj,
      e.counitIso.inv.toNatTrans.app (e.functor.obj X) ≫
        e.functor.map (e.unitIso.hom.toNatTrans.app X) =
          𝟙 (e.functor.obj X)) : (B ⥤ᵇ C) ≌ (A ⥤ᵇ C) where
  functor := {
    obj := fun F => e.functor.comp F
    map := fun α => BasedCategory.whiskerLeft e.functor α
    map_id := by intro F; rfl
    map_comp := by intro F G H α β; rfl }
  inverse := {
    obj := fun F => e.inverse.comp F
    map := fun α => BasedCategory.whiskerLeft e.inverse α
    map_id := by intro F; rfl
    map_comp := by intro F G H α β; rfl }
  unitIso := NatIso.ofComponents
    (fun F => basedIsoWhiskerRight e.counitIso.symm F) (by
      intro F G α
      apply BasedNatTrans.ext
      apply NatTrans.ext
      funext X
      exact (α.toNatTrans.naturality (e.counitIso.inv.toNatTrans.app X)).symm)
  counitIso := NatIso.ofComponents
    (fun F => basedIsoWhiskerRight e.unitIso F) (by
      intro F G α
      apply BasedNatTrans.ext
      apply NatTrans.ext
      funext X
      exact (α.toNatTrans.naturality (e.unitIso.hom.toNatTrans.app X)).symm)
  functor_unitIso_comp := by
    intro F
    apply BasedNatTrans.ext
    apply NatTrans.ext
    funext X
    change F.toFunctor.map (e.counitIso.inv.toNatTrans.app (e.functor.obj X)) ≫
        F.toFunctor.map (e.functor.map (e.unitIso.hom.toNatTrans.app X)) =
          𝟙 (F.toFunctor.obj (e.functor.obj X))
    exact (F.toFunctor.map_comp _ _).symm |>.trans
      (congrArg F.toFunctor.map (htriangle X)) |>.trans
      (F.toFunctor.map_id _)

/-- The equivalence between based functors out of the strict restriction of the functor
represented by `R` and based functors out of the elements of the restricted represented
functor of `R`, given by precomposition. -/
public noncomputable def representedHomPrecompositionEquivalence
    {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    BasedFunctor (BasedCategory.ofFunctor
      (Restriction.projection (p := representedProjection R)))
      (BasedCategory.ofFunctor p) ≌
    BasedFunctor (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor p) := by
  let e := representedRestrictionBasedEquivalence R
  have htriangle : ∀ X : (restrictedCoyoneda R).Elements,
      e.counitIso.inv.toNatTrans.app (e.functor.obj X) ≫
        e.functor.map (e.unitIso.hom.toNatTrans.app X) = 𝟙 (e.functor.obj X) :=
    (representedRestrictionEquivalence R).counitInv_functor_comp
  exact basedPrecompositionEquivalence e htriangle

/-- Precomposition with the canonical identification of the restricted represented set. -/
public def extendRepresentedHom {F : Type uF} [Category.{vF} F]
    (p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k)
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    BasedFunctor
      (BasedCategory.ofFunctor (Functor.Elements.π (restrictedCoyoneda R)))
      (BasedCategory.ofFunctor p) ⥤
    BasedFunctor
      (BasedCategory.ofFunctor
        (Restriction.projection (p := representedProjection R)))
      (BasedCategory.ofFunctor p) where
  obj φ := (representedRestrictionInverseBased R).comp φ
  map t := BasedCategory.whiskerLeft (representedRestrictionInverseBased R) t
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The functor represented by a complete local algebra is cofibered in groupoids. -/
public theorem representedProjection_cofibered
    (R : CompleteLocalAlgCat.{u, v, w} Λ k) :
    IsCofiberedInGroupoids (representedProjection R) := by
  constructor
  · intro V U f x hx
    subst U
    let y : (coyoneda.obj (Opposite.op R)).Elements :=
      (coyoneda.obj (Opposite.op R)).elementsMk V.unop (x.unop.2 ≫ f.unop)
    let a : x.unop ⟶ y := ⟨f.unop, rfl⟩
    exact ⟨Opposite.op y, a.op, by
      show (representedProjection R).op.IsHomLift
        ((representedProjection R).op.map a.op) a.op
      infer_instance⟩
  · intro x y z φ ψ f hf
    have he : φ.unop.hom ≫ f.unop = ψ.unop.hom := congrArg Quiver.Hom.unop hf
    let a : y.unop ⟶ z.unop := ⟨f.unop, by
      show y.unop.2 ≫ f.unop = z.unop.2
      have hφ : x.unop.2 ≫ φ.unop.hom = y.unop.2 := φ.unop.map_val
      rw [← hφ, Category.assoc, he]
      exact ψ.unop.map_val⟩
    refine ⟨a.op, ⟨rfl, ?_⟩, ?_⟩
    · exact Quiver.Hom.unop_inj (Functor.Elements.hom_ext he)
    · exact fun b hb =>
        Quiver.Hom.unop_inj (Functor.Elements.hom_ext (congrArg Quiver.Hom.unop hb.1))

/-- The inclusion of Artinian local algebras into complete local algebras is injective on
objects. -/
public theorem artinianToComplete_obj_injective
    {A B : ArtinianLocalAlgCat.{u, v, w} Λ k}
    (h : artinianToComplete.obj A = artinianToComplete.obj B) :
    A = B := by
  cases A
  cases B
  cases h
  rfl

/-- Reassociation of a composite of five morphisms. -/
public theorem compReassocFive {C : Type*} [Category C]
    {A B D E G H : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E)
    (i : E ⟶ G) (j : G ⟶ H) :
    f ≫ ((g ≫ h ≫ i) ≫ j) = ((f ≫ g) ≫ h) ≫ (i ≫ j) := by
  simp only [Category.assoc]

/-- Reassociation of a composite of four morphisms. -/
public theorem compReassocFour {C : Type*} [Category C]
    {A B D E G : C} (f : A ⟶ B) (g : B ⟶ D) (h : D ⟶ E)
    (i : E ⟶ G) : f ≫ (g ≫ h ≫ i) = (f ≫ g) ≫ (h ≫ i) := by
  simp only [Category.assoc]

end Deformation
end

universe u v w uF vF

namespace Deformation

open CategoryTheory

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

@[expose] public section

/-- The inverse of the restriction equivalence sends the `n`-th level of the adic pushforward of
the identity element of `R` to the canonical quotient point at the `n`-th truncation. -/
public theorem representedRestrictionInverse_adicLevel_eq
    (R : CompleteLocalAlgCat.{u, v, w} Λ k)
    (hq : IsCofiberedInGroupoids (representedProjection R))
    (n : ℕ) :
    (representedRestrictionInverse R).obj
      ((adicPushforwardChoice (representedProjection R) hq).level
        (representedIdentityElement R) n) =
      (restrictedCoyoneda R).elementsMk (AdicTruncation.obj R n) (canonicalQuotientPoint R n) := by
  let P := adicPushforwardChoice (representedProjection R) hq
  let X : (coyoneda.obj (Opposite.op R)).Elements := representedIdentityElement R
  let L := P.level X n
  have : (representedProjection R).IsHomLift (P.baseMap X n) (P.inclusion X n) :=
    P.inclusion_lift X n
  have hc := IsHomLift.codomain_eq (representedProjection R) (P.baseMap X n)
    (P.inclusion X n)
  have hfunctor : (AdicTruncation.functor n).obj R = AdicTruncation.obj R n := rfl
  have hcomplete : artinianToComplete.obj L.base =
      artinianToComplete.obj
        ((AdicTruncation.functor n).obj ((representedProjection R).obj X)) :=
    L.obj_eq.symm.trans hc
  have hbaseX : L.base =
      (AdicTruncation.functor n).obj ((representedProjection R).obj X) :=
    artinianToComplete_obj_injective hcomplete
  have hbaseFunctor : L.base = (AdicTruncation.functor n).obj R := by
    simpa [X, representedIdentityElement, representedProjection,
      Functor.Elements.π] using hbaseX
  have hbase : L.base = AdicTruncation.obj R n := hbaseFunctor.trans hfunctor
  have hbaseXEq : hbaseX = hbase := by
    apply Subsingleton.elim
  have heq : (representedRestrictionInverse R).obj L =
      ((restrictedCoyoneda R).elementsMk (AdicTruncation.obj R n) (canonicalQuotientPoint R n) :
        (restrictedCoyoneda R).Elements) := by
    refine Functor.Elements.ext ((representedRestrictionInverse R).obj L)
      ((restrictedCoyoneda R).elementsMk (AdicTruncation.obj R n) (canonicalQuotientPoint R n) :
        (restrictedCoyoneda R).Elements) hbase ?_
    have hincl : (P.inclusion X n).hom = L.obj.2 := by
      have h := (P.inclusion X n).map_val
      change X.2 ≫ (P.inclusion X n).hom = L.obj.2 at h
      simpa [X, representedIdentityElement] using h
    have hfac := IsHomLift.fac' (representedProjection R) (P.baseMap X n)
      (P.inclusion X n)
    have hfac' : (P.inclusion X n).hom = P.baseMap X n ≫ eqToHom hc.symm := by
      simpa [representedProjection, Functor.Elements.π] using hfac
    have hpoint : L.obj.2 ≫ eqToHom L.obj_eq ≫
        artinianToComplete.map (eqToHom hbaseX) = P.baseMap X n := by
      have hcast : eqToHom hc.symm ≫ eqToHom L.obj_eq ≫
          artinianToComplete.map (eqToHom hbaseX) = 𝟙 _ := by
        simp [eqToHom_map]
      rw [← hincl, hfac']
      erw [Category.assoc, hcast, Category.comp_id]
    rw [hbaseXEq] at hpoint
    have hquot : P.baseMap X n = canonicalQuotientPoint R n := by
      apply CompleteLocalAlgCat.Hom.ext
      apply AlgHom.ext
      intro r
      rw [P.baseMap_hom, canonicalQuotientPoint_hom]
      rfl
    show (L.obj.2 ≫ eqToHom L.obj_eq) ≫
        artinianToComplete.map (eqToHom hbase) =
      canonicalQuotientPoint R n
    exact hpoint.trans hquot
  simpa [P, L, X, representedIdentityElement] using heq

open CategoryTheory

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- Transporting the transition maps of a formal object along an equality of formal objects. -/
public theorem formalObject_transition_transport
    {F : Type uF} [Category.{vF} F]
    {p : F ⥤ ArtinianLocalAlgCat.{u, v, w} Λ k}
    {X Y : FormalObject p} (h : X = Y) (n : ℕ) :
    eqToHom (congrArg (fun Z => Z.level (n + 1)) h).symm ≫ X.transition n ≫
      eqToHom (congrArg (fun Z => Z.level n) h) = Y.transition n := by
  cases h
  simp

end
end Deformation
