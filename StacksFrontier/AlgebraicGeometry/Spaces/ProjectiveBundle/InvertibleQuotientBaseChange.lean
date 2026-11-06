module

public import StacksFrontier.AlgebraicGeometry.Spaces.SectionsInvertibleQuotients

/-!
# Base change of invertible quotients on algebraic spaces

Let `f : Y ⟶ X` be a morphism of algebraic spaces and `ℰ` an `𝒪_X`-module.  An invertible
quotient `q : ℰ ⟶ ℒ` pulls back to the invertible quotient `f^*q : f^*ℰ ⟶ f^*ℒ` of `f^*ℰ`: the
inverse image of an invertible module is invertible (Stacks 0B8P) and the inverse image is a
left adjoint (Stacks 03LU), hence preserves epimorphisms.  This file records that operation, its
transport along an identification `ℰ' ≅ f^*ℰ`, and its compatibility with identities and
composites on isomorphism classes.

## Main definitions

* `AlgebraicGeometry.Space.InvertibleQuotient.transport`: an invertible quotient of `ℰ` read as
  one of `ℰ'` along `ℰ' ≅ ℰ`.
* `AlgebraicGeometry.Space.InvertibleQuotient.pullback`: the pullback of an invertible quotient.
* `AlgebraicGeometry.Space.InvertibleQuotient.baseChange`: the pullback read along
  `ℰ' ≅ f^*ℰ`.
* `AlgebraicGeometry.Space.invertibleQuotientBaseChangeClass`: the same on isomorphism classes.

## Main results

* `AlgebraicGeometry.Space.invertibleQuotientBaseChangeClass_comp`: base change along a composite
  is the composite of the base changes.
* `AlgebraicGeometry.Space.invertibleQuotientBaseChangeClass_id`: base change along an identity is
  transport along the identification.

## References

* [Stacks Project, Tag 0B4I](https://stacks.math.columbia.edu/tag/0B4I)
* [Stacks Project, Tag 0B8P](https://stacks.math.columbia.edu/tag/0B8P)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace InvertibleQuotient

variable {X : AlgebraicSpaces B S hS} {E E' : Modules.{u, u} B S hS X.1 X.2}

set_option synthInstance.maxHeartbeats 400000 in
/-- An invertible quotient of `ℰ`, read as an invertible quotient of `ℰ'` along `ℰ' ≅ ℰ`. -/
def transport (e : E' ≅ E) (Q : InvertibleQuotient X E) : InvertibleQuotient X E' where
  L := Q.L
  invertible := Q.invertible
  q := e.hom ≫ Q.q
  epi := by have := Q.epi; infer_instance

/-- Transport along `e : ℰ' ≅ ℰ` preserves equivalence of invertible quotients. -/
theorem IsEquivalent.transport (e : E' ≅ E) {Q R : InvertibleQuotient X E}
    (h : Q.IsEquivalent R) : (Q.transport e).IsEquivalent (R.transport e) := by
  obtain ⟨α, hα⟩ := h
  exact ⟨α, by simp [InvertibleQuotient.transport, ← hα]⟩

variable {Y : AlgebraicSpaces B S hS}

/-- **The pullback of an invertible quotient** `q : ℰ ⟶ ℒ` along `f : Y ⟶ X`:
`f^*q : f^*ℰ ⟶ f^*ℒ`. -/
def pullback (f : Y ⟶ X) (Q : InvertibleQuotient X E) :
    InvertibleQuotient Y ((modulePullback B S hS f).obj E) where
  L := (modulePullback B S hS f).obj Q.L
  invertible := modulePullbackInvertible f Q.L Q.invertible
  q := (modulePullback B S hS f).map Q.q
  epi := by
    have := Q.epi
    have : (modulePullback B S hS f).PreservesEpimorphisms :=
      Functor.preservesEpimorphisms_of_adjunction (modulePullbackAdjunction B S hS f)
    infer_instance

/-- The pullback along `f : Y ⟶ X` preserves equivalence of invertible quotients. -/
theorem IsEquivalent.pullback (f : Y ⟶ X) {Q R : InvertibleQuotient X E}
    (h : Q.IsEquivalent R) : (Q.pullback f).IsEquivalent (R.pullback f) := by
  obtain ⟨α, hα⟩ := h
  exact ⟨(modulePullback B S hS f).mapIso α, by
    simp only [InvertibleQuotient.pullback, Functor.mapIso_hom, ← Functor.map_comp, hα]⟩

/-- **The base change of an invertible quotient** along `f : Y ⟶ X`, read along an
identification `ℰ' ≅ f^*ℰ` of the module on `Y`. -/
def baseChange (f : Y ⟶ X) {EY : Modules.{u, u} B S hS Y.1 Y.2}
    (e : EY ≅ (modulePullback B S hS f).obj E) (Q : InvertibleQuotient X E) :
    InvertibleQuotient Y EY :=
  (Q.pullback f).transport e

/-- The base change along `f : Y ⟶ X` preserves equivalence of invertible quotients. -/
theorem IsEquivalent.baseChange (f : Y ⟶ X) {EY : Modules.{u, u} B S hS Y.1 Y.2}
    (e : EY ≅ (modulePullback B S hS f).obj E) {Q R : InvertibleQuotient X E}
    (h : Q.IsEquivalent R) : (Q.baseChange f e).IsEquivalent (R.baseChange f e) :=
  (h.pullback f).transport e

end InvertibleQuotient

variable {X Y Z : AlgebraicSpaces B S hS} {E : Modules.{u, u} B S hS X.1 X.2}

/-- **The base change of isomorphism classes of invertible quotients** along `f : Y ⟶ X`, read
along an identification `ℰ' ≅ f^*ℰ`. -/
def invertibleQuotientBaseChangeClass (f : Y ⟶ X) {EY : Modules.{u, u} B S hS Y.1 Y.2}
    (e : EY ≅ (modulePullback B S hS f).obj E) :
    InvertibleQuotientClass X E → InvertibleQuotientClass Y EY :=
  Quotient.map (InvertibleQuotient.baseChange f e)
    fun _ _ h => InvertibleQuotient.IsEquivalent.baseChange f e h

/-- The base change of the isomorphism class of `Q` is the class of the base change of `Q`. -/
@[simp]
theorem invertibleQuotientBaseChangeClass_mk (f : Y ⟶ X) {EY : Modules.{u, u} B S hS Y.1 Y.2}
    (e : EY ≅ (modulePullback B S hS f).obj E) (Q : InvertibleQuotient X E) :
    invertibleQuotientBaseChangeClass f e (Quotient.mk _ Q) =
      Quotient.mk (invertibleQuotientSetoid Y EY) (Q.baseChange f e) :=
  rfl

/-- **Base change along a composite is the composite of the base changes**, the two
identifications of the module on `Z` being related by the comparison `g^* f^* ≅ (g ≫ f)^*` of
Stacks 03LU. -/
theorem invertibleQuotientBaseChangeClass_comp (f : Y ⟶ X) (g : Z ⟶ Y)
    {EY : Modules.{u, u} B S hS Y.1 Y.2} {EZ : Modules.{u, u} B S hS Z.1 Z.2}
    (eY : EY ≅ (modulePullback B S hS f).obj E) (eZ : EZ ≅ (modulePullback B S hS g).obj EY)
    (c : InvertibleQuotientClass X E) :
    invertibleQuotientBaseChangeClass g eZ (invertibleQuotientBaseChangeClass f eY c) =
      invertibleQuotientBaseChangeClass (g ≫ f)
        (eZ ≪≫ (modulePullback B S hS g).mapIso eY ≪≫
          (modulePullbackCompIso B S hS g f).app E) c := by
  induction c using Quotient.ind with
  | _ Q =>
  refine Quotient.sound ⟨(modulePullbackCompIso B S hS g f).app Q.L, ?_⟩
  simp only [InvertibleQuotient.baseChange, InvertibleQuotient.transport,
    InvertibleQuotient.pullback, Iso.trans_hom, Functor.mapIso_hom, Iso.app_hom, Functor.map_comp,
    Category.assoc]
  rw [← (modulePullbackCompIso B S hS g f).hom.naturality Q.q]
  rfl

/-- **Base change along an identity is transport along the identification**, through the unit
law `(𝟙 X)^* ≅ 𝟭` of Stacks 03LU. -/
theorem invertibleQuotientBaseChangeClass_id {E' : Modules.{u, u} B S hS X.1 X.2}
    (e : E' ≅ (modulePullback B S hS (𝟙 X)).obj E) (Q : InvertibleQuotient X E) :
    invertibleQuotientBaseChangeClass (𝟙 X) e (Quotient.mk _ Q) =
      Quotient.mk (invertibleQuotientSetoid X E')
        (Q.transport (e ≪≫ (modulePullbackIdIso B S hS X).app E)) := by
  refine Quotient.sound ⟨(modulePullbackIdIso B S hS X).app Q.L, ?_⟩
  simp only [InvertibleQuotient.baseChange, InvertibleQuotient.transport,
    InvertibleQuotient.pullback, Iso.trans_hom, Iso.app_hom, Category.assoc]
  exact congrArg (e.hom ≫ ·) ((modulePullbackIdIso B S hS X).hom.naturality Q.q)

/-- **The transport of isomorphism classes of invertible quotients** along an identification
`ℰ' ≅ ℰ`. -/
def invertibleQuotientTransportClass {E' : Modules.{u, u} B S hS X.1 X.2} (e : E' ≅ E) :
    InvertibleQuotientClass X E → InvertibleQuotientClass X E' :=
  Quotient.map (InvertibleQuotient.transport e)
    fun _ _ h => InvertibleQuotient.IsEquivalent.transport e h

/-- The transport of the isomorphism class of `Q` is the class of the transport of `Q`. -/
@[simp]
theorem invertibleQuotientTransportClass_mk {E' : Modules.{u, u} B S hS X.1 X.2} (e : E' ≅ E)
    (Q : InvertibleQuotient X E) :
    invertibleQuotientTransportClass e (Quotient.mk _ Q) =
      Quotient.mk (invertibleQuotientSetoid X E') (Q.transport e) :=
  rfl

/-- Transport after base change is base change along the composite identification. -/
theorem invertibleQuotientTransportClass_baseChangeClass (f : Y ⟶ X)
    {EY EY' : Modules.{u, u} B S hS Y.1 Y.2} (a : EY' ≅ EY)
    (b : EY ≅ (modulePullback B S hS f).obj E) (c : InvertibleQuotientClass X E) :
    invertibleQuotientTransportClass a (invertibleQuotientBaseChangeClass f b c) =
      invertibleQuotientBaseChangeClass f (a ≪≫ b) c := by
  induction c using Quotient.ind with
  | _ Q =>
  refine Quotient.sound ⟨Iso.refl _, ?_⟩
  simp [InvertibleQuotient.baseChange, InvertibleQuotient.transport]

/-- Base change after transport is base change along the composite identification. -/
theorem invertibleQuotientBaseChangeClass_transportClass (f : Y ⟶ X)
    {E' : Modules.{u, u} B S hS X.1 X.2} (a : E' ≅ E) {EY : Modules.{u, u} B S hS Y.1 Y.2}
    (b : EY ≅ (modulePullback B S hS f).obj E') (c : InvertibleQuotientClass X E) :
    invertibleQuotientBaseChangeClass f b (invertibleQuotientTransportClass a c) =
      invertibleQuotientBaseChangeClass f (b ≪≫ (modulePullback B S hS f).mapIso a) c := by
  induction c using Quotient.ind with
  | _ Q =>
  refine Quotient.sound ⟨Iso.refl _, ?_⟩
  simp [InvertibleQuotient.baseChange, InvertibleQuotient.transport, InvertibleQuotient.pullback]

/-- Transport of isomorphism classes along `b` and then along `a` is transport along
`a ≪≫ b`. -/
theorem invertibleQuotientTransportClass_trans {E' E'' : Modules.{u, u} B S hS X.1 X.2}
    (a : E'' ≅ E') (b : E' ≅ E) (c : InvertibleQuotientClass X E) :
    invertibleQuotientTransportClass a (invertibleQuotientTransportClass b c) =
      invertibleQuotientTransportClass (a ≪≫ b) c := by
  induction c using Quotient.ind with
  | _ Q =>
  refine Quotient.sound ⟨Iso.refl _, ?_⟩
  simp [InvertibleQuotient.transport]

/-- Transport along the identity of `ℰ` is the identity of isomorphism classes. -/
theorem invertibleQuotientTransportClass_refl (c : InvertibleQuotientClass X E) :
    invertibleQuotientTransportClass (Iso.refl E) c = c := by
  induction c using Quotient.ind with
  | _ Q =>
  refine Quotient.sound ⟨Iso.refl _, ?_⟩
  simp [InvertibleQuotient.transport]

/-- Transport of isomorphism classes of invertible quotients along `ℰ' ≅ ℰ` is injective. -/
theorem invertibleQuotientTransportClass_injective {E' : Modules.{u, u} B S hS X.1 X.2}
    (a : E' ≅ E) : Function.Injective (invertibleQuotientTransportClass a) := fun c c' h => by
  have := congrArg (invertibleQuotientTransportClass a.symm) h
  rwa [invertibleQuotientTransportClass_trans, invertibleQuotientTransportClass_trans,
    Iso.symm_self_id, invertibleQuotientTransportClass_refl,
    invertibleQuotientTransportClass_refl] at this

end AlgebraicGeometry.Space

end
