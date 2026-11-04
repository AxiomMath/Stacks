module

public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.InducedFunctor
public import StacksFrontier.Deformation.Artin.FormalObject

/-!
# Effectivity is stable under 2-fibre products (Stacks 07X9)

Let `S` be a scheme and let `f : 𝒳 → 𝒴` and `g : 𝒵 → 𝒴` be morphisms of categories fibred
in groupoids over the big fppf site of `S`. The approximation functor of Stacks 07X6 sends a
complete local object to the system of its restrictions to the infinitesimal thickenings of
the closed point of its base. If that functor is an equivalence for `𝒳`, for `𝒴` and for
`𝒵`, then it is an equivalence for `𝒳 ×_𝒴 𝒵`.

The proof compares both sides of the square with a categorical pullback. Complete local
objects of the 2-fibre product are exactly the categorical pullback of the complete local
objects of `𝒳` and of `𝒵` over those of `𝒴`, and the same comparison functor for formal
objects is fully faithful — it need not be essentially surjective, since a compatible pair
of formal objects carries no reason for its two complete local bases to be *equal* rather
than isomorphic. That is enough: the comparison functor for complete local objects is an
equivalence, the induced functor between the two categorical pullbacks is an equivalence by
the three hypotheses, and the approximation functor of the 2-fibre product followed by the
fully faithful comparison is isomorphic to that composite, so it is an equivalence; a
functor which becomes an equivalence after a fully faithful functor is an equivalence.

## Main results

* `Deformation.Artin.isEquivalence_approximationFunctor_twoFibreProduct`: **Stacks 07X9**,
  the approximation functor of a 2-fibre product is an equivalence when it is one for each
  of the three constituent categories.

## Implementation notes

The 2-fibre product is taken over the common site, so its comparison isomorphisms are
vertical and the two projections are strictly over the site; that is what lets a formal
object of the 2-fibre product be split into a formal object of `𝒳`, one of `𝒵` and an
isomorphism of their images, all over one and the same complete local base.

`Deformation.Artin.CompleteLocalObjects` keeps only the morphisms inducing a local map of
complete local bases, so the comparison functor for complete local objects has to be checked
to land there; `Deformation.Artin.mapCompleteLocalObjects_local_iff` reduces that to locality
downstairs, where it holds because the base map of a morphism of 2-fibre-product objects is
the base map of its first component.

Essential surjectivity of the comparison for complete local objects produces the missing
object as a 2-fibre-product object over the base of the `𝒳`-component; the `𝒵`-component is
transported along the isomorphism of `𝒴`-images, which is where the chosen complete local
base of `Deformation.Artin.chosenBase` has to be identified with the actual one.

## References

* [Stacks Project, Tag 07X9](https://stacks.math.columbia.edu/tag/07X9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

namespace Deformation.Artin


universe u vX vY vZ wX wY wZ

@[implicit_reducible]
private noncomputable def mapFormalObjects
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G : Type*} [Category F] [Category G]
    {pF : F ⥤ BigFppfOver B S hS}
    {pG : G ⥤ BigFppfOver B S hS}
    (K : F ⥤ G) (hK : K ⋙ pG = pF) :
    FormalObject B S hS pF ⥤ FormalObject B S hS pG where
  obj X := {
    base := X.base
    contains := X.contains
    level := fun n => K.obj (X.level n)
    level_eq := fun n =>
      (congrArg (fun H : F ⥤ BigFppfOver B S hS => H.obj (X.level n)) hK).trans (X.level_eq n)
    transition := fun n => K.map (X.transition n)
    transition_lift := fun n => by
      have := X.transition_lift n
      exact Functor.isHomLift_map_of_comp_eq hK _ _
  }
  map f := {
    app := fun n => K.map (f.app n)
    naturality := fun n => by
      simpa only [Functor.map_comp] using congrArg K.map (f.naturality n)
  }
  map_id X := FormalObject.Hom.ext fun n => K.map_id (X.level n)
  map_comp f g := FormalObject.Hom.ext fun n => K.map_comp (f.app n) (g.app n)

@[implicit_reducible]
private noncomputable def mapCompleteLocalObjects
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G : Type*} [Category F] [Category G]
    {pF : F ⥤ BigFppfOver B S hS}
    {pG : G ⥤ BigFppfOver B S hS}
    (K : F ⥤ G) (hK : K ⋙ pG = pF) :
    CompleteLocalObjects B S hS pF ⥤
      CompleteLocalObjects B S hS pG where
  obj x := ⟨⟨K.obj x.obj.1, by
    obtain ⟨A, hA, hx⟩ := x.obj.2
    exact ⟨A, hA, (congrArg (fun H => H.obj x.obj.1) hK).trans hx⟩⟩⟩
  map {x y} f := ⟨ObjectProperty.homMk (K.map f.1.hom), by
    cases hK
    exact f.2⟩
  map_id x := WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _ (K.map_id x.obj.1))
  map_comp f g :=
    WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _ (K.map_comp f.1.hom g.1.hom))

private theorem mapCompleteLocalObjects_obj_val
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F G : Type*} [Category F] [Category G]
    {pF : F ⥤ BigFppfOver B S hS}
    {pG : G ⥤ BigFppfOver B S hS}
    (K : F ⥤ G) (hK : K ⋙ pG = pF)
    (x : CompleteLocalObjects B S hS pF) :
    ((mapCompleteLocalObjects K hK).obj x).obj.obj = K.obj x.obj.obj := by
  cases hK
  rfl

@[implicit_reducible]
private noncomputable def formalObjectsToCategoricalPullback
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type vX} [Category.{wX} X]
    {Y : Type vY} [Category.{wY} Y]
    {Z : Type vZ} [Category.{wZ} Z]
    (pX : X ⥤ BigFppfOver B S hS)
    (pY : Y ⥤ BigFppfOver B S hS)
    (pZ : Z ⥤ BigFppfOver B S hS)
    (f : X ⥤ Y) (g : Z ⥤ Y)
    (hf : f ⋙ pY = pX) (hg : g ⋙ pY = pZ) :
      FormalObject B S hS
        (TwoFibreProductOver.structureFunctor pX pZ pY f g) ⥤
      CategoryTheory.Limits.CategoricalPullback
        (mapFormalObjects f hf) (mapFormalObjects g hg) := by
  refine {
    obj := fun P => by
      let FX : FormalObject B S hS pX := {
        base := P.base
        contains := P.contains
        level := fun n => (P.level n).x
        level_eq := fun n => by
          have h := P.level_eq n
          change (P.level n).base = _ at h
          exact (P.level n).hx.trans h
        transition := fun n => (P.transition n).a
        transition_lift := fun n => by
          have h : ((TwoFibreProductOver.fst pX pZ pY f g) ⋙ pX).IsHomLift
              (truncationOverSucc B S hS P.base P.contains n) (P.transition n) := by
            rw [TwoFibreProductOver.fst_comp_eq]
            exact P.transition_lift n
          exact (Functor.isHomLift_comp_iff (TwoFibreProductOver.fst pX pZ pY f g)
            pX (truncationOverSucc B S hS P.base P.contains n)
            (P.transition n)).1 h }
      let FZ : FormalObject B S hS pZ := {
        base := P.base
        contains := P.contains
        level := fun n => (P.level n).y
        level_eq := fun n => by
          have h := P.level_eq n
          change (P.level n).base = _ at h
          exact (P.level n).hy.trans h
        transition := fun n => (P.transition n).b
        transition_lift := fun n => by
          have h : ((TwoFibreProductOver.snd pX pZ pY f g) ⋙ pZ).IsHomLift
              (truncationOverSucc B S hS P.base P.contains n) (P.transition n) := by
            rw [TwoFibreProductOver.snd_comp_eq]
            exact P.transition_lift n
          exact (Functor.isHomLift_comp_iff (TwoFibreProductOver.snd pX pZ pY f g)
            pZ (truncationOverSucc B S hS P.base P.contains n)
            (P.transition n)).1 h }
      exact {
        fst := FX
        snd := FZ
        iso := {
          hom := {
            app := fun n => (P.level n).iso.hom
            naturality := fun n => (P.transition n).w }
          inv := {
            app := fun n => (P.level n).iso.inv
            naturality := fun n => by
              change g.map (P.transition n).b ≫ (P.level (n + 1)).iso.inv =
                (P.level n).iso.inv ≫ f.map (P.transition n).a
              apply (cancel_mono (P.level (n + 1)).iso.hom).1
              calc
                (g.map (P.transition n).b ≫ (P.level (n + 1)).iso.inv) ≫
                    (P.level (n + 1)).iso.hom = g.map (P.transition n).b := by simp
                _ = ((P.level n).iso.inv ≫ (P.level n).iso.hom) ≫
                    g.map (P.transition n).b := by simp
                _ = ((P.level n).iso.inv ≫ f.map (P.transition n).a) ≫
                    (P.level (n + 1)).iso.hom := by
                      rw [Category.assoc, ← (P.transition n).w]
                      exact (Category.assoc _ _ _).symm }
          hom_inv_id := FormalObject.Hom.ext fun n => (P.level n).iso.hom_inv_id
          inv_hom_id := FormalObject.Hom.ext fun n => (P.level n).iso.inv_hom_id } }
    map := fun {P Q} a =>
      { fst := {
          app := fun n => (a.app n).a
          naturality := fun n => by
            change (P.transition n).a ≫ (a.app (n + 1)).a =
              (a.app n).a ≫ (Q.transition n).a
            exact congrArg (fun z => z.a) (a.naturality n) }
        snd := {
          app := fun n => (a.app n).b
          naturality := fun n => by
            change (P.transition n).b ≫ (a.app (n + 1)).b =
              (a.app n).b ≫ (Q.transition n).b
            exact congrArg (fun z => z.b) (a.naturality n) }
        w := by
          apply FormalObject.Hom.ext
          intro n
          exact (a.app n).w }
    map_id := by
      intro P
      apply CategoryTheory.Limits.CategoricalPullback.Hom.ext <;> rfl
    map_comp := by
      intro P Q R a b
      apply CategoryTheory.Limits.CategoricalPullback.Hom.ext <;> rfl }

private theorem formalObjectsToCategoricalPullback_faithful
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type vX} [Category.{wX} X]
    {Y : Type vY} [Category.{wY} Y]
    {Z : Type vZ} [Category.{wZ} Z]
    (pX : X ⥤ BigFppfOver B S hS)
    (pY : Y ⥤ BigFppfOver B S hS)
    (pZ : Z ⥤ BigFppfOver B S hS)
    (f : X ⥤ Y) (g : Z ⥤ Y)
    (hf : f ⋙ pY = pX) (hg : g ⋙ pY = pZ) :
    (formalObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg).Faithful := by
  constructor
  intro P Q a b h
  exact FormalObject.Hom.ext fun n => TwoFibreProductOver.Hom.ext'
    (congrArg (fun k => k.fst.app n) h :) (congrArg (fun k => k.snd.app n) h :)

/-- The two components of a comparison square of the 2-fibre product induce the same base
morphism. -/
private theorem eqToHom_map_comp_eq_of_square
    {C : Type*} [Category C] {X : Type*} [Category X] {Y : Type*} [Category Y]
    {Z : Type*} [Category Z] (pY : Y ⥤ C) (f : X ⥤ Y) (g : Z ⥤ Y)
    {P Q : TwoFibreProductOver (f ⋙ pY) (g ⋙ pY) pY f g} (a : P.x ⟶ Q.x) (b : P.y ⟶ Q.y)
    (w : f.map a ≫ Q.iso.hom = P.iso.hom ≫ g.map b) :
    eqToHom P.hy.symm ≫ pY.map (g.map b) ≫ eqToHom Q.hy =
      eqToHom P.hx.symm ≫ pY.map (f.map a) ≫ eqToHom Q.hx := by
  have hv (R : TwoFibreProductOver (f ⋙ pY) (g ⋙ pY) pY f g) :
      pY.map R.iso.hom = eqToHom R.hx ≫ eqToHom R.hy.symm := by
    have := R.vertical
    simpa using IsHomLift.fac' pY (𝟙 R.base) R.iso.hom
  have hw := congrArg pY.map w
  rw [Functor.map_comp, Functor.map_comp, hv Q, hv P] at hw
  apply (cancel_mono (eqToHom Q.hy.symm)).1
  apply (cancel_epi (eqToHom P.hx)).1
  simpa [Functor.comp_map, Category.assoc] using hw.symm

private theorem formalObjectsToCategoricalPullback_full
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type vX} [Category.{wX} X]
    {Y : Type vY} [Category.{wY} Y]
    {Z : Type vZ} [Category.{wZ} Z]
    (pX : X ⥤ BigFppfOver B S hS)
    (pY : Y ⥤ BigFppfOver B S hS)
    (pZ : Z ⥤ BigFppfOver B S hS)
    (f : X ⥤ Y) (g : Z ⥤ Y)
    (hf : f ⋙ pY = pX) (hg : g ⋙ pY = pZ) :
    (formalObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg).Full := by
  refine ⟨fun {P Q} φ => ?_⟩
  cases hf
  cases hg
  let a := φ.fst
  let b := φ.snd
  let aa (n : ℕ) : (P.level n).x ⟶ (Q.level n).x := a.app n
  let bb (n : ℕ) : (P.level n).y ⟶ (Q.level n).y := b.app n
  have hwRaw (n : ℕ) :
      f.map (aa n) ≫ (Q.level n).iso.hom = (P.level n).iso.hom ≫ g.map (bb n) :=
    congrArg (fun z => z.app n) φ.w
  have hbase (n : ℕ) := eqToHom_map_comp_eq_of_square pY f g (aa n) (bb n) (hwRaw n)
  let k : P ⟶ Q := {
    app := fun n => TwoFibreProductOver.Hom.mk'
      (aa n) (bb n) (hbase n) (hwRaw n)
    naturality := fun n => by
      apply TwoFibreProductOver.Hom.ext'
      · simpa [formalObjectsToCategoricalPullback] using a.naturality n
      · simpa [formalObjectsToCategoricalPullback] using b.naturality n }
  refine ⟨k, ?_⟩
  apply CategoryTheory.Limits.CategoricalPullback.Hom.ext <;>
    apply FormalObject.Hom.ext <;>
    intro n <;> rfl

private noncomputable def relativeProductToCategoricalPullback
    {C : Type*} [Category C]
    {X : Type*} [Category X] {Y : Type*} [Category Y] {Z : Type*} [Category Z]
    (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C)
    (f : X ⥤ Y) (g : Z ⥤ Y) :
    TwoFibreProductOver pX pZ pY f g ⥤ CategoryTheory.Limits.CategoricalPullback f g where
  obj P := { fst := P.x, snd := P.y, iso := P.iso }
  map φ := { fst := φ.a, snd := φ.b, w := φ.w }
  map_id P := by
    apply CategoryTheory.Limits.CategoricalPullback.Hom.ext <;> rfl
  map_comp := by
    intro P Q R φ ψ
    apply CategoryTheory.Limits.CategoricalPullback.Hom.ext <;> rfl

private theorem relativeProductToCategoricalPullback_fullyFaithful
    {C : Type*} [Category C]
    {X : Type*} [Category X] {Y : Type*} [Category Y] {Z : Type*} [Category Z]
    (pX : X ⥤ C) (pY : Y ⥤ C) (pZ : Z ⥤ C)
    (f : X ⥤ Y) (g : Z ⥤ Y)
    (hf : f ⋙ pY = pX) (hg : g ⋙ pY = pZ) :
    (relativeProductToCategoricalPullback pX pY pZ f g).Faithful ∧
      (relativeProductToCategoricalPullback pX pY pZ f g).Full := by
  constructor
  · constructor
    intro P Q φ ψ h
    exact TwoFibreProductOver.Hom.ext' (congrArg CategoricalPullback.Hom.fst h :)
      (congrArg CategoricalPullback.Hom.snd h :)
  · refine ⟨fun {P Q} φ => ?_⟩
    cases hf
    cases hg
    let a : P.x ⟶ Q.x := φ.fst
    let b : P.y ⟶ Q.y := φ.snd
    have hw : f.map a ≫ Q.iso.hom = P.iso.hom ≫ g.map b := φ.w
    refine ⟨TwoFibreProductOver.Hom.mk' a b (eqToHom_map_comp_eq_of_square pY f g a b hw) hw, ?_⟩
    apply CategoryTheory.Limits.CategoricalPullback.Hom.ext <;> rfl

section CompleteLocal

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type*} [Category F] {p : F ⥤ BigFppfOver B S hS}

@[implicit_reducible]
private def forgetComplete (p : F ⥤ BigFppfOver B S hS) :
    CompleteLocalObjects B S hS p ⥤ F where
  obj x := x.obj.obj
  map a := a.1.1

private theorem local_of_isIso
    {x y : CompleteLocalObjectsFull B S hS p}
    (a : x ⟶ y) [IsIso a] : IsLocalBaseMap B S hS p a := by
  have : IsIso a.hom :=
    Functor.map_isIso (IsCompleteLocalObject B S hS p).ι a
  let t := baseMap B S hS p a
  have : IsIso t := by
    unfold t baseMap
    exact Functor.map_isIso _ _
  let e := Scheme.Hom.homeomorph t
  apply Inseparable.eq
  apply (IsLocalRing.specializes_closedPoint (t (IsLocalRing.closedPoint _))).antisymm
  have h := (IsLocalRing.specializes_closedPoint
    (e.symm (IsLocalRing.closedPoint
      (CommRingCat.of (chosenBase B S hS p y).R)))).map e.continuous
  have heq : e (e.symm (IsLocalRing.closedPoint
      (CommRingCat.of (chosenBase B S hS p y).R))) =
      IsLocalRing.closedPoint (CommRingCat.of (chosenBase B S hS p y).R) :=
    e.apply_symm_apply _
  exact heq ▸ h

@[implicit_reducible]
private def completeLocalIso
    {x y : CompleteLocalObjects B S hS p} (e : x.obj.obj ≅ y.obj.obj) :
    x ≅ y :=
  WideSubcategory.isoMk (ObjectProperty.isoMk _ e)
    (local_of_isIso _) (local_of_isIso _)

private theorem mapCompleteLocalObjects_local_iff
    {G : Type*} [Category G] {q : G ⥤ BigFppfOver B S hS}
    (K : F ⥤ G) (hK : K ⋙ q = p)
    {x y : CompleteLocalObjects B S hS p} (a : x.obj ⟶ y.obj) :
    IsLocalBaseMap B S hS q
      (ObjectProperty.homMk (X := ((mapCompleteLocalObjects K hK).obj x).obj)
        (Y := ((mapCompleteLocalObjects K hK).obj y).obj) (K.map a.hom)) ↔
      IsLocalBaseMap B S hS p a := by
  cases hK
  rfl

end CompleteLocal

section CompleteProduct

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type vX} [Category.{wX} X]
    {Y : Type vY} [Category.{wY} Y]
    {Z : Type vZ} [Category.{wZ} Z]
    (pX : X ⥤ BigFppfOver B S hS)
    (pY : Y ⥤ BigFppfOver B S hS)
    (pZ : Z ⥤ BigFppfOver B S hS)
    (f : X ⥤ Y) (g : Z ⥤ Y)
    (hf : f ⋙ pY = pX) (hg : g ⋙ pY = pZ)

@[implicit_reducible]
private def completeObjectsToCategoricalPullback :
    CompleteLocalObjects B S hS
      (TwoFibreProductOver.structureFunctor pX pZ pY f g) ⥤
    CategoricalPullback (mapCompleteLocalObjects f hf) (mapCompleteLocalObjects g hg) where
  obj P := {
    fst := (mapCompleteLocalObjects (TwoFibreProductOver.fst pX pZ pY f g)
      TwoFibreProductOver.fst_comp_eq).obj P
    snd := (mapCompleteLocalObjects (TwoFibreProductOver.snd pX pZ pY f g)
      TwoFibreProductOver.snd_comp_eq).obj P
    iso := completeLocalIso P.obj.obj.iso }
  map a := {
    fst := (mapCompleteLocalObjects (TwoFibreProductOver.fst pX pZ pY f g)
      TwoFibreProductOver.fst_comp_eq).map a
    snd := (mapCompleteLocalObjects (TwoFibreProductOver.snd pX pZ pY f g)
      TwoFibreProductOver.snd_comp_eq).map a
    w := WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _ a.1.1.w) }
  map_id P := by
    apply CategoricalPullback.Hom.ext <;>
      apply WideSubcategory.hom_ext <;> apply ObjectProperty.hom_ext <;> rfl
  map_comp a b := by
    apply CategoricalPullback.Hom.ext <;>
      apply WideSubcategory.hom_ext <;> apply ObjectProperty.hom_ext <;> rfl

private theorem completeObjectsToCategoricalPullback_faithful :
    (completeObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg).Faithful where
  map_injective h := WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _
    (TwoFibreProductOver.Hom.ext' (congrArg (fun k => k.fst.1.1) h :)
      (congrArg (fun k => k.snd.1.1) h :)))

private theorem completeObjectsToCategoricalPullback_full :
    (completeObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg).Full := by
  let R := relativeProductToCategoricalPullback pX pY pZ f g
  have := (relativeProductToCategoricalPullback_fullyFaithful pX pY pZ f g hf hg).2
  refine ⟨fun {P Q} φ => ?_⟩
  let k : R.obj P.obj.obj ⟶ R.obj Q.obj.obj := {
    fst := φ.fst.1.1
    snd := φ.snd.1.1
    w := congrArg (fun a => a.1.1) φ.w }
  let a := R.preimage k
  have ha : a.a = φ.fst.1.1 := congrArg CategoricalPullback.Hom.fst (R.map_preimage k)
  have hb : a.b = φ.snd.1.1 := congrArg CategoricalPullback.Hom.snd (R.map_preimage k)
  have hl : IsLocalBaseMap B S hS
      (TwoFibreProductOver.structureFunctor pX pZ pY f g)
      (ObjectProperty.homMk (X := P.obj) (Y := Q.obj) a) := by
    apply (mapCompleteLocalObjects_local_iff (TwoFibreProductOver.fst pX pZ pY f g)
      TwoFibreProductOver.fst_comp_eq (x := P) (y := Q) _).mp
    change IsLocalBaseMap B S hS pX
      (ObjectProperty.homMk
        (X := ((completeObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg).obj P).fst.obj)
        (Y := ((completeObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg).obj Q).fst.obj)
        a.a)
    rw [ha]
    exact φ.fst.2
  exact ⟨⟨ObjectProperty.homMk a, hl⟩, CategoricalPullback.Hom.ext
    (WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _ ha))
    (WideSubcategory.hom_ext _ (ObjectProperty.hom_ext _ hb))⟩

private theorem completeObjectsToCategoricalPullback_essSurj
    (hpX : pX.IsFiberedInGroupoids) :
    (completeObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg).EssSurj := by
  cases hf
  cases hg
  let C := completeObjectsToCategoricalPullback B S hS (f ⋙ pY) pY (g ⋙ pY) f g rfl rfl
  refine ⟨fun P => ?_⟩
  let ψ := (forgetComplete pY).mapIso P.iso
  let α : (f ⋙ pY).obj P.fst.obj.obj ≅ (g ⋙ pY).obj P.snd.obj.obj := pY.mapIso ψ
  have : (f ⋙ pY).IsFibered := hpX.isFibered
  let x := Functor.IsPreFibered.pullbackObj rfl α.inv
  let u : x ⟶ P.fst.obj.obj := Functor.IsPreFibered.pullbackMap rfl α.inv
  have huBase : (f ⋙ pY).obj x = (g ⋙ pY).obj P.snd.obj.obj :=
    Functor.IsPreFibered.pullbackObj_proj rfl α.inv
  have huLift : (f ⋙ pY).IsHomLift α.inv u := by
    change (f ⋙ pY).IsHomLift _ (Functor.IsPreFibered.pullbackMap rfl α.inv)
    infer_instance
  have huCart : (f ⋙ pY).IsStronglyCartesian α.inv u :=
    hpX.isStronglyCartesian_homLift α.inv u
  have huIso : IsIso u :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso (p := f ⋙ pY) (f := α.inv) u
  have hfLift : pY.IsHomLift α.inv (f.map u) :=
    Functor.isHomLift_map_of_comp_eq rfl α.inv u
  have hpsiLift : pY.IsHomLift α.hom ψ.hom := by
    change pY.IsHomLift (pY.map ψ.hom) ψ.hom
    infer_instance
  let θ : f.obj x ≅ g.obj P.snd.obj.obj := asIso (f.map u ≫ ψ.hom)
  have hθ : θ.hom = f.map u ≫ ψ.hom := rfl
  have hv : pY.IsHomLift (𝟙 ((g ⋙ pY).obj P.snd.obj.obj)) θ.hom := by
    rw [hθ]
    simpa only [Iso.inv_hom_id] using
      IsHomLift.comp pY α.inv α.hom (f.map u) ψ.hom
  let Q : TwoFibreProductOver (f ⋙ pY) (g ⋙ pY) pY f g := {
    base := (g ⋙ pY).obj P.snd.obj.obj
    x := x
    y := P.snd.obj.obj
    hx := huBase
    hy := rfl
    iso := θ
    vertical := hv }
  let q : CompleteLocalObjects B S hS
      (TwoFibreProductOver.structureFunctor (f ⋙ pY) (g ⋙ pY) pY f g) :=
    ⟨⟨Q, P.snd.obj.property⟩⟩
  let a : (C.obj q).fst ≅ P.fst := completeLocalIso (@asIso _ _ _ _ u huIso)
  let b : (C.obj q).snd ≅ P.snd := completeLocalIso (Iso.refl _)
  refine ⟨q, ⟨{
    hom := { fst := a.hom, snd := b.hom, w := ?_ }
    inv := { fst := a.inv, snd := b.inv, w := ?_ }
    hom_inv_id := ?_
    inv_hom_id := ?_ }⟩⟩
  · apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    change f.map u ≫ ψ.hom = θ.hom ≫ g.map (𝟙 _)
    simp [θ]
  · apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    change f.map (inv u) ≫ θ.hom = ψ.hom ≫ g.map (𝟙 _)
    suffices h : f.map (inv u) ≫ θ.hom = ψ.hom from
      h.trans ((Category.comp_id ψ.hom).symm.trans
        (congrArg (ψ.hom ≫ ·) (g.map_id P.snd.obj.obj).symm))
    simp [θ]
  · exact CategoricalPullback.Hom.ext a.hom_inv_id b.hom_inv_id
  · exact CategoricalPullback.Hom.ext a.inv_hom_id b.inv_hom_id

private theorem completeObjectsToCategoricalPullback_isEquivalence
    (hpX : pX.IsFiberedInGroupoids) :
    (completeObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg).IsEquivalence where
  faithful := completeObjectsToCategoricalPullback_faithful B S hS pX pY pZ f g hf hg
  full := completeObjectsToCategoricalPullback_full B S hS pX pY pZ f g hf hg
  essSurj := completeObjectsToCategoricalPullback_essSurj B S hS pX pY pZ f g hf hg hpX

end CompleteProduct

private theorem mono_of_mono_base
    {C D : Type*} [Category C] [Category D] (p : C ⥤ D)
    (hp : p.IsFiberedInGroupoids) {x y : C} (r : x ⟶ y) [Mono (p.map r)] :
    Mono r := by
  constructor
  intro z a b h
  have hab : p.map a = p.map b := by
    apply (cancel_mono (p.map r)).1
    simpa only [← p.map_comp] using congrArg p.map h
  obtain ⟨c, hc, hu⟩ := hp.unique_lift r (a ≫ r) (p.map a) (p.map_comp a r).symm
  exact (hu a ⟨rfl, rfl⟩).trans (hu b ⟨hab.symm, h.symm⟩).symm

section Approximation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : Type*} [Category F] {p : F ⥤ BigFppfOver B S hS}

@[implicit_reducible]
private def restriction (hp : p.IsFiberedInGroupoids)
    (x : CompleteLocalObjects B S hS p) (n : ℕ) :
    ((approximationFunctor B S hS p hp).obj x).level n ⟶ x.obj.obj :=
  (approximationFunctorData B S hS p hp).2.choose x n

private theorem restriction_base (hp : p.IsFiberedInGroupoids)
    (x : CompleteLocalObjects B S hS p) :
    ((approximationFunctor B S hS p hp).obj x).base =
      chosenBase B S hS p x.obj :=
  (approximationFunctorData B S hS p hp).2.choose_spec.choose x

private theorem restriction_transition (hp : p.IsFiberedInGroupoids)
    (x : CompleteLocalObjects B S hS p) (n : ℕ) :
    ((approximationFunctor B S hS p hp).obj x).transition n ≫
      restriction hp x (n + 1) = restriction hp x n :=
  (approximationFunctorData B S hS p hp).2.choose_spec.choose_spec.2.1 x n

private theorem restriction_naturality (hp : p.IsFiberedInGroupoids)
    {x y : CompleteLocalObjects B S hS p} (a : x ⟶ y) (n : ℕ) :
    ((approximationFunctor B S hS p hp).map a).app n ≫
      restriction hp y n = restriction hp x n ≫ a.1.1 :=
  (approximationFunctorData B S hS p hp).2.choose_spec.choose_spec.2.2.1 x y a n

private theorem restriction_spec (hp : p.IsFiberedInGroupoids)
    (x : CompleteLocalObjects B S hS p) (n : ℕ) :
    (BigFppfOver.toScheme B S hS).map
      (eqToHom (((approximationFunctor B S hS p hp).obj x).level_eq n).symm ≫
        p.map (restriction hp x n) ≫ eqToHom (chosenBase_eq B S hS p x.obj)) =
      adicThickeningι
        ((approximationFunctor B S hS p hp).obj x).base.R
        (IsLocalRing.maximalIdeal _) n ≫
        eqToHom (congrArg (fun A : FormalBase S => Spec (.of A.R))
          (restriction_base hp x)) :=
  (approximationFunctorData B S hS p hp).2.choose_spec.choose_spec.2.2.2 x n

private theorem restriction_mono (hp : p.IsFiberedInGroupoids)
    (x : CompleteLocalObjects B S hS p) (n : ℕ) :
    Mono (restriction hp x n) := by
  suffices Mono (p.map (restriction hp x n)) from mono_of_mono_base p hp _
  let T := BigFppfOver.toScheme B S hS
  apply T.mono_of_mono_map
  have hhmono : Mono (T.map (eqToHom
      (((approximationFunctor B S hS p hp).obj x).level_eq n).symm) ≫
      T.map (p.map (restriction hp x n)) ≫
      T.map (eqToHom (chosenBase_eq B S hS p x.obj))) := by
    simp only [← Functor.map_comp]
    rw [restriction_spec hp x n]
    have hmono : Mono (adicThickeningι
        ((approximationFunctor B S hS p hp).obj x).base.R
        (IsLocalRing.maximalIdeal
          ((approximationFunctor B S hS p hp).obj x).base.R) n) := by
      have : IsClosedImmersion (adicThickeningι
          ((approximationFunctor B S hS p hp).obj x).base.R
          (IsLocalRing.maximalIdeal
            ((approximationFunctor B S hS p hp).obj x).base.R) n) :=
        IsClosedImmersion.spec_of_quotient_mk (R := CommRingCat.of _) _
      infer_instance
    have hiso : Mono (eqToHom (congrArg (fun A : FormalBase S => Spec (.of A.R))
        (restriction_base hp x))) := IsIso.mono_of_iso _
    exact @mono_comp _ _ _ _ _ _ hmono _ hiso
  rwa [mono_comp_iff_of_isIso, mono_comp_iff_of_mono] at hhmono


private theorem truncationOver_eq (A D : FormalBase S)
    (hA : ∀ n, B.Contains (A.truncation n))
    (hD : ∀ n, B.Contains (D.truncation n)) (h : A = D) (n : ℕ) :
    truncationOver B S hS A hA n =
      truncationOver B S hS D hD n := by
  cases h
  rfl

private theorem truncationOver_ι_congr (A D C : FormalBase S)
    (hA : ∀ n, B.Contains (A.truncation n))
    (hD : ∀ n, B.Contains (D.truncation n)) (ha : A = C) (hd : D = C) (n : ℕ) :
    (BigFppfOver.toScheme B S hS).map
        (eqToHom (truncationOver_eq A D hA hD (ha.trans hd.symm) n)) ≫
      (adicThickeningι D.R (IsLocalRing.maximalIdeal D.R) n ≫
        eqToHom (congrArg (fun E : FormalBase S => Spec (.of E.R)) hd)) =
      adicThickeningι A.R (IsLocalRing.maximalIdeal A.R) n ≫
        eqToHom (congrArg (fun E : FormalBase S => Spec (.of E.R)) ha) := by
  cases ha
  cases hd
  exact Category.comp_id (adicThickeningι A.R (IsLocalRing.maximalIdeal A.R) n)

private theorem restriction_map_eq
    {G : Type*} [Category G]
    {q : G ⥤ BigFppfOver B S hS}
    (K : F ⥤ G) (hK : K ⋙ q = p)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (x : CompleteLocalObjects B S hS p) (n : ℕ) :
    ∃ h : q.obj (K.obj (((approximationFunctor B S hS p hp).obj x).level n)) =
        q.obj (((approximationFunctor B S hS q hq).obj
          ((mapCompleteLocalObjects K hK).obj x)).level n),
      q.map (K.map (restriction hp x n) ≫
        eqToHom (mapCompleteLocalObjects_obj_val K hK x).symm) =
        eqToHom h ≫ q.map (restriction hq ((mapCompleteLocalObjects K hK).obj x) n) := by
  cases hK
  let A := (approximationFunctor B S hS (K ⋙ q) hp).obj x
  let y := (mapCompleteLocalObjects K rfl).obj x
  let D := (approximationFunctor B S hS q hq).obj y
  have hAD : A.base = D.base :=
    (restriction_base hp x).trans (restriction_base hq y).symm
  have ht : truncationOver B S hS A.base A.contains n =
      truncationOver B S hS D.base D.contains n :=
    truncationOver_eq _ _ _ _ hAD n
  let h := (A.level_eq n).trans (ht.trans (D.level_eq n).symm)
  refine ⟨h, ?_⟩
  change q.map (K.map (restriction hp x n) ≫ 𝟙 _) =
    eqToHom h ≫ q.map (restriction hq y n)
  rw [Category.comp_id]
  apply (BigFppfOver.toScheme B S hS).map_injective
  have ha := restriction_spec hp x n
  have hd := restriction_spec hq y n
  have he : (BigFppfOver.toScheme B S hS).map (eqToHom ht) ≫
      (adicThickeningι D.base.R (IsLocalRing.maximalIdeal _) n ≫
        eqToHom (congrArg (fun A : FormalBase S => Spec (.of A.R))
          (restriction_base hq y))) =
      adicThickeningι A.base.R (IsLocalRing.maximalIdeal _) n ≫
        eqToHom (congrArg (fun A : FormalBase S => Spec (.of A.R))
          (restriction_base hp x)) :=
    truncationOver_ι_congr _ _ _ _ _ (restriction_base hp x) (restriction_base hq y) n
  apply (cancel_epi ((BigFppfOver.toScheme B S hS).map
    (eqToHom (A.level_eq n).symm))).1
  apply (cancel_mono ((BigFppfOver.toScheme B S hS).map
    (eqToHom (chosenBase_eq B S hS q y.obj)))).1
  have key := ha.trans (he.symm.trans (congrArg
    ((BigFppfOver.toScheme B S hS).map (eqToHom ht) ≫ ·) hd.symm))
  simp only [← Functor.map_comp, Category.assoc]
  have hassoc : eqToHom ht ≫ eqToHom (D.level_eq n).symm ≫
        q.map (restriction hq y n) ≫ eqToHom (chosenBase_eq B S hS q y.obj) =
      eqToHom (A.level_eq n).symm ≫ eqToHom h ≫
        q.map (restriction hq y n) ≫ eqToHom (chosenBase_eq B S hS q y.obj) := by
    simp only [eqToHom_trans_assoc]
  exact key.trans ((((BigFppfOver.toScheme B S hS).map_comp _ _).symm).trans
    (congrArg (BigFppfOver.toScheme B S hS).map hassoc))

private theorem exists_approximationMapIso
    {G : Type*} [Category G]
    {q : G ⥤ BigFppfOver B S hS}
    (K : F ⥤ G) (hK : K ⋙ q = p)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) :
    ∃ e : approximationFunctor B S hS p hp ⋙ mapFormalObjects K hK ≅
        mapCompleteLocalObjects K hK ⋙ approximationFunctor B S hS q hq,
      ∀ x n, (e.hom.app x).app n ≫
          restriction hq ((mapCompleteLocalObjects K hK).obj x) n =
        K.map (restriction hp x n) ≫
          eqToHom (mapCompleteLocalObjects_obj_val K hK x).symm := by
  cases hK
  let A := approximationFunctor B S hS (K ⋙ q) hp
  let D := approximationFunctor B S hS q hq
  let L := mapCompleteLocalObjects K (pG := q) rfl
  have hh (x : CompleteLocalObjects B S hS (K ⋙ q)) (n : ℕ) :
      ∃ e : K.obj ((A.obj x).level n) ≅ (D.obj (L.obj x)).level n,
        e.hom ≫ restriction hq (L.obj x) n = K.map (restriction hp x n) := by
    obtain ⟨h, hh⟩ := restriction_map_eq K rfl hp hq x n
    change q.map (K.map (restriction hp x n) ≫ 𝟙 _) =
      eqToHom h ≫ q.map (restriction hq (L.obj x) n) at hh
    rw [Category.comp_id] at hh
    have hr := hq.isStronglyCartesian_homLift (q.map (restriction hq (L.obj x) n))
      (restriction hq (L.obj x) n)
    have hs := hq.isStronglyCartesian_homLift (q.map (K.map (restriction hp x n)))
      (K.map (restriction hp x n))
    refine ⟨Functor.IsStronglyCartesian.domainIsoOfBaseIso q (g := eqToIso h) hh
      (restriction hq (L.obj x) n) (K.map (restriction hp x n)), ?_⟩
    exact Functor.IsStronglyCartesian.fac q (q.map (restriction hq (L.obj x) n))
      (restriction hq (L.obj x) n) hh (K.map (restriction hp x n))
  choose e he using hh
  have ht (x : CompleteLocalObjects B S hS (K ⋙ q)) (n : ℕ) :
      K.map ((A.obj x).transition n) ≫ (e x (n + 1)).hom =
        (e x n).hom ≫ (D.obj (L.obj x)).transition n := by
    have := restriction_mono hq (L.obj x) (n + 1)
    apply (cancel_mono (restriction hq (L.obj x) (n + 1))).1
    rw [Category.assoc, he, Category.assoc, restriction_transition hq (L.obj x) n, he]
    exact (K.map_comp _ _).symm.trans (congrArg K.map (restriction_transition hp x n))
  let E (x : CompleteLocalObjects B S hS (K ⋙ q)) :
      (mapFormalObjects K (pG := q) rfl).obj (A.obj x) ≅ D.obj (L.obj x) := {
    hom := { app := fun n => (e x n).hom, naturality := ht x }
    inv := {
      app := fun n => (e x n).inv
      naturality := fun n => by
        change (D.obj (L.obj x)).transition n ≫ (e x (n + 1)).inv =
          (e x n).inv ≫ K.map ((A.obj x).transition n)
        apply (cancel_epi (e x n).hom).1
        apply (cancel_mono (e x (n + 1)).hom).1
        simpa [Category.assoc] using (ht x n).symm }
    hom_inv_id := FormalObject.Hom.ext fun n => (e x n).hom_inv_id
    inv_hom_id := FormalObject.Hom.ext fun n => (e x n).inv_hom_id }
  refine ⟨NatIso.ofComponents E (fun {x y} a => ?_), fun x n => ?_⟩
  · refine FormalObject.Hom.ext fun n => ?_
    have := restriction_mono hq (L.obj y) n
    apply (cancel_mono (restriction hq (L.obj y) n)).1
    change (K.map ((A.map a).app n) ≫ (e y n).hom) ≫ _ =
      ((e x n).hom ≫ (D.map (L.map a)).app n) ≫ _
    rw [Category.assoc, he, Category.assoc, restriction_naturality hq (L.map a) n,
      ← Category.assoc, he]
    exact (K.map_comp _ _).symm.trans
      ((congrArg K.map (restriction_naturality hp a n)).trans (K.map_comp _ _))
  · change (e x n).hom ≫ restriction hq (L.obj x) n =
      K.map (restriction hp x n) ≫ 𝟙 _
    exact (he x n).trans (Category.comp_id _).symm

private def approximationMapIso
    {G : Type*} [Category G]
    {q : G ⥤ BigFppfOver B S hS}
    (K : F ⥤ G) (hK : K ⋙ q = p)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) :
    approximationFunctor B S hS p hp ⋙ mapFormalObjects K hK ≅
      mapCompleteLocalObjects K hK ⋙ approximationFunctor B S hS q hq :=
  (exists_approximationMapIso K hK hp hq).choose

private theorem approximationMapIso_fac
    {G : Type*} [Category G]
    {q : G ⥤ BigFppfOver B S hS}
    (K : F ⥤ G) (hK : K ⋙ q = p)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (x : CompleteLocalObjects B S hS p) (n : ℕ) :
    ((approximationMapIso K hK hp hq).hom.app x).app n ≫
        restriction hq ((mapCompleteLocalObjects K hK).obj x) n =
      K.map (restriction hp x n) := by
  cases hK
  simp only [approximationMapIso]
  exact ((exists_approximationMapIso K rfl hp hq).choose_spec x n).trans (Category.comp_id _)

end Approximation

/-- A commuting square, read off from factorisations of its two legs through a common
monomorphism. Both legs of the square `u ≫ v ≫ t = i ≫ b ≫ e` are tested after
composition with the monomorphism `r`; the hypotheses say that `t ≫ r` factors as `s ≫ w`,
that `v ≫ s` and `u ≫ c` collapse to `c` and `d`, that `d ≫ w = i ≫ l` is the square one
already knows, and that `l` and `e ≫ r` both describe `k`.

This is stated for abstract morphisms so that the associativity bookkeeping happens once,
in a category where it is free of the unfolding that the fibred structures carry. -/
private theorem eq_of_mono_comp_fac {C : Type*} [Category C]
    {o₁ o₂ o₃ o₄ o₅ o₆ o₇ o₈ : C}
    {u : o₁ ⟶ o₂} {v : o₂ ⟶ o₃} {t : o₃ ⟶ o₄} {r : o₄ ⟶ o₇}
    {s : o₃ ⟶ o₅} {w : o₅ ⟶ o₇} {c : o₂ ⟶ o₅} {d : o₁ ⟶ o₅}
    {i : o₁ ⟶ o₆} {b : o₆ ⟶ o₈} {e : o₈ ⟶ o₄} {k : o₈ ⟶ o₇} {l : o₆ ⟶ o₇}
    (hr : Mono r) (hlong : t ≫ r = s ≫ w) (hv : v ≫ s = c) (hu : u ≫ c = d)
    (hsq : d ≫ w = i ≫ l) (hl : l = b ≫ k) (he : e ≫ r = k) :
    u ≫ v ≫ t = i ≫ b ≫ e := by
  apply (cancel_mono r).1
  simp only [Category.assoc]
  rw [hlong, reassoc_of% hv, reassoc_of% hu, hsq, hl, he]

private def categoricalPullbackIso
    {A D E : Type*} [Category A] [Category D] [Category E]
    {H : A ⥤ E} {I : D ⥤ E} {P Q : CategoricalPullback H I}
    (a : P.fst ≅ Q.fst) (b : P.snd ≅ Q.snd)
    (h : H.map a.hom ≫ Q.iso.hom = P.iso.hom ≫ I.map b.hom) : P ≅ Q where
  hom := ⟨a.hom, b.hom, h⟩
  inv := ⟨a.inv, b.inv, by
    apply (cancel_epi (H.map a.hom)).1
    apply (cancel_mono (I.map b.hom)).1
    simpa [Category.assoc, ← H.map_comp_assoc, ← I.map_comp] using h.symm⟩
  hom_inv_id := CategoricalPullback.Hom.ext a.hom_inv_id b.hom_inv_id
  inv_hom_id := CategoricalPullback.Hom.ext a.inv_hom_id b.inv_hom_id

section Comparison

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type vX} [Category.{wX} X]
    {Y : Type vY} [Category.{wY} Y]
    {Z : Type vZ} [Category.{wZ} Z]
    (pX : X ⥤ BigFppfOver B S hS)
    (pY : Y ⥤ BigFppfOver B S hS)
    (pZ : Z ⥤ BigFppfOver B S hS)
    (f : X ⥤ Y) (g : Z ⥤ Y)
    (hpX : pX.IsFiberedInGroupoids) (hpY : pY.IsFiberedInGroupoids)
    (hpZ : pZ.IsFiberedInGroupoids)
    (hf : f ⋙ pY = pX) (hg : g ⋙ pY = pZ)

private def inducedApproximation :
    CategoricalPullback (mapCompleteLocalObjects f hf) (mapCompleteLocalObjects g hg) ⥤
      CategoricalPullback (mapFormalObjects f hf) (mapFormalObjects g hg) :=
  CategoricalPullback.map _ _
    (approximationFunctor B S hS pX hpX)
    (approximationFunctor B S hS pZ hpZ)
    (approximationFunctor B S hS pY hpY) _ _
    (approximationMapIso g hg hpZ hpY) (approximationMapIso f hf hpX hpY).symm

private def approximationComparisonIso :
    approximationFunctor B S hS
      (TwoFibreProductOver.structureFunctor pX pZ pY f g)
      (TwoFibreProductOver.isFiberedInGroupoids pX pZ pY f g hpX hpZ hpY hf hg) ⋙
      formalObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg ≅
    completeObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg ⋙
      inducedApproximation B S hS pX pY pZ f g hpX hpY hpZ hf hg := by
  let p := TwoFibreProductOver.structureFunctor pX pZ pY f g
  let hp := TwoFibreProductOver.isFiberedInGroupoids pX pZ pY f g hpX hpZ hpY hf hg
  let A := approximationFunctor B S hS p hp
  let C := completeObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg
  let D := formalObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg
  let V := inducedApproximation B S hS pX pY pZ f g hpX hpY hpZ hf hg
  let K := TwoFibreProductOver.fst pX pZ pY f g
  let L := TwoFibreProductOver.snd pX pZ pY f g
  let eX := approximationMapIso K TwoFibreProductOver.fst_comp_eq hp hpX
  let eZ := approximationMapIso L TwoFibreProductOver.snd_comp_eq hp hpZ
  let ef := approximationMapIso f hf hpX hpY
  let eg := approximationMapIso g hg hpZ hpY
  have hcompat (P : CompleteLocalObjects B S hS p) :
      (mapFormalObjects f hf).map (eX.hom.app P) ≫ ((V.obj (C.obj P)).iso.hom) =
        ((D.obj (A.obj P)).iso.hom) ≫ (mapFormalObjects g hg).map (eZ.hom.app P) := by
    apply FormalObject.Hom.ext
    intro n
    let x := (C.obj P).fst
    have hmono := restriction_mono hpY
      ((mapCompleteLocalObjects g hg).obj (C.obj P).snd) n
    have hw :
        f.map ((eX.hom.app P).app n) ≫ (ef.hom.app x).app n ≫
            ((approximationFunctor B S hS pY hpY).map (C.obj P).iso.hom).app n =
          ((A.obj P).level n).iso.hom ≫
            g.map ((eZ.hom.app P).app n) ≫ (eg.hom.app (C.obj P).snd).app n := by
      have hfFac := approximationMapIso_fac f hf hpX hpY x n
      have hgFac := approximationMapIso_fac g hg hpZ hpY (C.obj P).snd n
      have hXFac : (eX.hom.app P).app n ≫ restriction hpX x n =
          (restriction hp P n).a :=
        approximationMapIso_fac K TwoFibreProductOver.fst_comp_eq hp hpX P n
      have hZFac : (eZ.hom.app P).app n ≫ restriction hpZ (C.obj P).snd n =
          (restriction hp P n).b :=
        approximationMapIso_fac L TwoFibreProductOver.snd_comp_eq hp hpZ P n
      have hnat : ((approximationFunctor B S hS pY hpY).map (C.obj P).iso.hom).app n ≫
            restriction hpY ((mapCompleteLocalObjects g hg).obj (C.obj P).snd) n =
          restriction hpY ((mapCompleteLocalObjects f hf).obj x) n ≫ P.obj.obj.iso.hom :=
        restriction_naturality hpY (C.obj P).iso.hom n
      exact eq_of_mono_comp_fac hmono hnat hfFac
        ((f.map_comp _ _).symm.trans (congrArg f.map hXFac))
        (restriction hp P n).w
        ((congrArg g.map hZFac.symm).trans (g.map_comp _ _))
        hgFac
    have : IsIso ((eg.hom.app (C.obj P).snd).app n) :=
      Functor.map_isIso (FormalObject.evaluation n) (eg.hom.app (C.obj P).snd)
    apply (cancel_mono ((eg.hom.app (C.obj P).snd).app n)).1
    change
      (f.map ((eX.hom.app P).app n) ≫
        ((ef.hom.app x).app n ≫
          ((approximationFunctor B S hS pY hpY).map (C.obj P).iso.hom).app n ≫
          (eg.inv.app (C.obj P).snd).app n)) ≫ (eg.hom.app (C.obj P).snd).app n =
        (((A.obj P).level n).iso.hom ≫ g.map ((eZ.hom.app P).app n)) ≫
          (eg.hom.app (C.obj P).snd).app n
    have he : (eg.inv.app (C.obj P).snd).app n ≫ (eg.hom.app (C.obj P).snd).app n = 𝟙 _ :=
      congrArg (fun a => a.app n) (eg.app (C.obj P).snd).inv_hom_id
    simp only [Category.assoc, he]
    exact (congrArg (fun t => f.map ((eX.hom.app P).app n) ≫ (ef.hom.app x).app n ≫ t)
      (Category.comp_id
        (((approximationFunctor B S hS pY hpY).map (C.obj P).iso.hom).app n))).trans hw
  exact NatIso.ofComponents (fun P => categoricalPullbackIso (eX.app P) (eZ.app P) (hcompat P))
    fun a => CategoricalPullback.Hom.ext (eX.hom.naturality a) (eZ.hom.naturality a)

end Comparison

private theorem isEquivalence_of_comp_fullyFaithful
    {C D E : Type*} [Category C] [Category D] [Category E]
    (F : C ⥤ D) (G : D ⥤ E) [G.Full] [G.Faithful] [(F ⋙ G).IsEquivalence] :
    F.IsEquivalence where
  faithful := Functor.Faithful.of_comp F G
  full := Functor.Full.of_comp_faithful F G
  essSurj := ⟨fun d => ⟨(F ⋙ G).objPreimage (G.obj d),
    ⟨G.preimageIso ((F ⋙ G).objObjPreimageIso (G.obj d))⟩⟩⟩

/-- **Stacks 07X9.** The approximation equivalence is stable under 2-fibre products of
categories fibred in groupoids over the big fppf site: if the approximation functor is an
equivalence for `pX`, `pY` and `pZ`, then it is an equivalence for `pX ×_pY pZ`. -/
@[stacks 07X9]
public theorem isEquivalence_approximationFunctor_twoFibreProduct
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : Type vX} [Category.{wX} X]
    {Y : Type vY} [Category.{wY} Y]
    {Z : Type vZ} [Category.{wZ} Z]
    (pX : X ⥤ BigFppfOver B S hS)
    (pY : Y ⥤ BigFppfOver B S hS)
    (pZ : Z ⥤ BigFppfOver B S hS)
    (f : X ⥤ Y) (g : Z ⥤ Y)
    (hpX : pX.IsFiberedInGroupoids) (hpY : pY.IsFiberedInGroupoids)
    (hpZ : pZ.IsFiberedInGroupoids)
    (hf : f ⋙ pY = pX) (hg : g ⋙ pY = pZ)
    (hX : (approximationFunctor B S hS pX hpX).IsEquivalence)
    (hY : (approximationFunctor B S hS pY hpY).IsEquivalence)
    (hZ : (approximationFunctor B S hS pZ hpZ).IsEquivalence) :
    (approximationFunctor B S hS
      (TwoFibreProductOver.structureFunctor pX pZ pY f g)
      (TwoFibreProductOver.isFiberedInGroupoids pX pZ pY f g
        hpX hpZ hpY hf hg)).IsEquivalence := by
  let A := approximationFunctor B S hS
    (TwoFibreProductOver.structureFunctor pX pZ pY f g)
    (TwoFibreProductOver.isFiberedInGroupoids pX pZ pY f g hpX hpZ hpY hf hg)
  let C := completeObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg
  let D := formalObjectsToCategoricalPullback B S hS pX pY pZ f g hf hg
  let V := inducedApproximation B S hS pX pY pZ f g hpX hpY hpZ hf hg
  have : C.IsEquivalence :=
    completeObjectsToCategoricalPullback_isEquivalence B S hS pX pY pZ f g hf hg hpX
  have : V.IsEquivalence := induced_isEquivalence_of_isEquivalence _ _ _ _ _
  have : D.Faithful := formalObjectsToCategoricalPullback_faithful B S hS pX pY pZ f g hf hg
  have : D.Full := formalObjectsToCategoricalPullback_full B S hS pX pY pZ f g hf hg
  have : (A ⋙ D).IsEquivalence := Functor.isEquivalence_of_iso
    (approximationComparisonIso B S hS pX pY pZ f g hpX hpY hpZ hf hg).symm
  exact isEquivalence_of_comp_fullyFaithful A D


end Deformation.Artin

end
