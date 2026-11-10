module

public import StacksFrontier.Deformation.PredeformationTangent.DerivationMap
public import StacksFrontier.Deformation.Smooth.IsomorphismClasses
public import StacksFrontier.Deformation.TangentSpace.Functor
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The action of residue-field derivations on the tangent space

For a predeformation category, a derivation of its residue field acts on isomorphism classes
of first-order deformations by pushforward along the automorphism `a + εb ↦ a + ε(b + D a)`
of the dual numbers. The action is additive in the derivation and natural in the
predeformation category.

## Main definitions

* `Deformation.predeformationTangentSpace`: the tangent-space construction specialized to the
  associated functor of a predeformation category.
* `Deformation.uliftDerivation`: a derivation `k → k` read as a derivation into the rank-one
  module used by the dual numbers.
* `Deformation.residueFieldCoordinates`: the chosen coordinate on the residue-field object.
* `Deformation.dualNumbersTwistHom`: the twisting automorphism of the dual numbers.
* `Deformation.DerivationActionData`: the action together with the square-zero maps that
  specify it.
* `Deformation.derivationAction`: the construction of the action on the tangent space.

## Main results

* `Deformation.dualNumbersTwistHom_apply`, `Deformation.dualNumbersTwistHom_zero` and
  `Deformation.dualNumbersTwistHom_add`: the coordinate formula for the twisting
  automorphism, and the fact that it turns addition of derivations into composition.
* `Deformation.derivationAction_natural`: naturality under morphisms of predeformation
  categories.

## Implementation notes

The tangent space is the value on the dual numbers of the associated functor of fibrewise
isomorphism classes. The universe lift only places the dual numbers in the carrier universe of
the Artinian algebra category. The data includes the coordinate formula for the twisting
automorphism and its pushforward characterization, rather than an arbitrary function on
classes; this makes the action independent of the choices made in its construction, which is
what `Deformation.dualNumbersTwistHom_eq_of_formula` and hence naturality rest on.

## References

* [Stacks Project, Tag 06SW](https://stacks.math.columbia.edu/tag/06SW)
-/

@[expose] public section

namespace Deformation

section
open CategoryTheory

universe u v w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-! ### Coordinates on the residue field and the dual numbers -/

/-- The rank-one module whose square-zero extension is the dual-number object of `𝒞_Λ`. -/
noncomputable abbrev dualNumbersModule (Λ : Type u) (k : Type w) [CommRing Λ] [Field k]
    [Algebra Λ k] : FGModuleCat.{max v w} k :=
  FGModuleCat.of k (ULift.{v} k)

/-- A derivation `k → k`, read as a derivation into the rank-one module of the dual
numbers. -/
noncomputable def uliftDerivation (D : Derivation Λ k k) :=
  derivationOfLinearMap (dualNumbersModule.{u, v, w} Λ k)
    ULift.moduleEquiv.symm.toLinearMap D

/-- The chosen coordinate on the residue-field object of `𝒞_Λ`. -/
noncomputable abbrev residueFieldCoordinates :
    residueFieldObject.{u, v, w} Λ k ≃ₐ[Λ] k :=
  ULift.algEquiv (R := Λ) (A := k)

/-- The residue-field coordinate induces the prescribed residue-field identification. -/
theorem residueFieldCoordinates_residue (a : residueFieldObject.{u, v, w} Λ k) :
    (residueFieldObject.{u, v, w} Λ k).residueEquiv
        (IsLocalRing.residue (residueFieldObject.{u, v, w} Λ k) a) =
      residueFieldCoordinates.{u, v, w} (Λ := Λ) (k := k) a := by
  change ((Ideal.quotientEquivAlgOfEq Λ
      (IsLocalRing.maximalIdeal_eq_bot (R := ULift.{v, w} k))).trans
      ((AlgEquiv.quotientBot Λ (ULift.{v, w} k)).trans
        (ULift.algEquiv (R := Λ) (A := k))))
      (Ideal.Quotient.mk (IsLocalRing.maximalIdeal (ULift.{v, w} k)) a) = a.down
  simp

/-! ### The twisting automorphism of the dual numbers -/

variable {F : Type u₁} [Category.{v₁} F]

/-- The derivation map and the action on classes over the dual numbers, in the chosen
coordinates. -/
noncomputable def dualNumbersDerivationData
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) :
    DerivationMapAndAction p
      (residueFieldObject.{u, v, w} Λ k)
      (artinianDualNumbers.{u, w, v} Λ k)
      (residueFieldCoordinates.{u, v, w} (Λ := Λ) (k := k))
      (squareZeroCoordinates.{u, v, w} (dualNumbersModule.{u, v, w} Λ k))
      (residueFieldCoordinates_residue.{u, v, w} (Λ := Λ) (k := k))
      (squareZeroCoordinates_residue.{u, v, w} (dualNumbersModule.{u, v, w} Λ k))
      (specialFiberObject p hp).1
      (specialFiberObject p hp).2 :=
  squareZeroDerivationMapAndAction p hp
    (residueFieldObject.{u, v, w} Λ k)
    (residueFieldCoordinates.{u, v, w} (Λ := Λ) (k := k))
    (residueFieldCoordinates_residue.{u, v, w} (Λ := Λ) (k := k))
    (dualNumbersModule.{u, v, w} Λ k)
    (specialFiberObject p hp).1
    (specialFiberObject p hp).2

/-- The automorphism `a + εb ↦ a + ε(b + D a)` of the dual numbers. -/
noncomputable def dualNumbersTwistHom
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (D : Derivation Λ k k) :
    artinianDualNumbers.{u, w, v} Λ k ⟶ artinianDualNumbers.{u, w, v} Λ k :=
  (dualNumbersDerivationData p hp).twistMap (uliftDerivation.{u, v, w} D)

/-- The coordinate formula for the twisting automorphism, on a lifted second coordinate. -/
theorem dualNumbersTwistHom_apply_ulift
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (D : Derivation Λ k k) (a : k)
    (b : ULift.{v, w} k) :
    (dualNumbersTwistHom p hp D).hom
        ((TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) :
          artinianDualNumbers.{u, w, v} Λ k) =
      TrivSqZeroExt.inl a + TrivSqZeroExt.inr (b + ULift.up (D a)) :=
  (dualNumbersDerivationData p hp).twistMap_apply (uliftDerivation.{u, v, w} D) a b

/-- The coordinate formula for the twisting automorphism. -/
theorem dualNumbersTwistHom_apply
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (D : Derivation Λ k k) (a b : k) :
    (dualNumbersTwistHom p hp D).hom
        ((TrivSqZeroExt.inl a + TrivSqZeroExt.inr (ULift.up b)) :
          artinianDualNumbers.{u, w, v} Λ k) =
      TrivSqZeroExt.inl a + TrivSqZeroExt.inr (ULift.up (b + D a)) :=
  dualNumbersTwistHom_apply_ulift p hp D a (ULift.up b)

/-- Endomorphisms of the dual numbers are equal if they agree on all `a + εb`. -/
private theorem dualNumbers_hom_ext
    {f g : artinianDualNumbers.{u, w, v} Λ k ⟶ artinianDualNumbers.{u, w, v} Λ k}
    (h : ∀ (a : k) (b : ULift.{v, w} k),
      f.hom ((TrivSqZeroExt.inl a + TrivSqZeroExt.inr b) :
          artinianDualNumbers.{u, w, v} Λ k) =
        g.hom (TrivSqZeroExt.inl a + TrivSqZeroExt.inr b :
          artinianDualNumbers.{u, w, v} Λ k)) :
    f = g := by
  apply ArtinianLocalAlgCat.hom_ext
  ext x
  induction x using TrivSqZeroExt.ind with
  | inl_add_inr a b => exact h a b

/-- The zero derivation twists by the identity. -/
theorem dualNumbersTwistHom_zero
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) :
    dualNumbersTwistHom p hp 0 = 𝟙 (artinianDualNumbers.{u, w, v} Λ k) := by
  refine dualNumbers_hom_ext fun a b => ?_
  rw [dualNumbersTwistHom_apply_ulift, Derivation.zero_apply]
  apply TrivSqZeroExt.ext
  · rfl
  · change (0 : ULift.{v, w} k) + (b + ULift.up.{v, w} (0 : k)) = 0 + b
    rw [show ULift.up.{v, w} (0 : k) = 0 from rfl, add_zero]

/-- Addition of derivations becomes composition of twisting automorphisms. -/
theorem dualNumbersTwistHom_add
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (D E : Derivation Λ k k) :
    dualNumbersTwistHom p hp (D + E) =
      dualNumbersTwistHom p hp E ≫ dualNumbersTwistHom p hp D := by
  refine dualNumbers_hom_ext fun a b => ?_
  rw [ArtinianLocalAlgCat.comp_hom]
  simp only [AlgHom.comp_apply]
  rw [dualNumbersTwistHom_apply_ulift, dualNumbersTwistHom_apply_ulift,
    dualNumbersTwistHom_apply_ulift, Derivation.add_apply]
  apply TrivSqZeroExt.ext
  · rfl
  · change (0 : ULift.{v, w} k) + (b + ULift.up.{v, w} (D a + E a)) =
      0 + ((b + ULift.up.{v, w} (E a)) + ULift.up.{v, w} (D a))
    rw [show ULift.up.{v, w} (D a + E a) =
      ULift.up.{v, w} (D a) + ULift.up.{v, w} (E a) from rfl]
    abel

/-- The twisting automorphism depends only on the derivation, not on the predeformation
category it was constructed from. -/
theorem dualNumbersTwistHom_eq_of_formula
    {G : Type u₁} [Category.{v₁} G]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p)
    (q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hq : IsPredeformationCategory q) (D : Derivation Λ k k) :
    dualNumbersTwistHom p hp D = dualNumbersTwistHom q hq D :=
  dualNumbers_hom_ext fun a b => by
    rw [dualNumbersTwistHom_apply_ulift, dualNumbersTwistHom_apply_ulift]

/-! ### The action on the tangent space -/

/-- The tangent space of a predeformation category, formed from its associated functor of
isomorphism classes. -/
@[stacks 06IG, sga "7 VI 1.18"]
noncomputable abbrev predeformationTangentSpace
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) : Type u₁ :=
  tangentSpaceArtinian Λ k
    (isomorphismClasses (BasedCategory.ofFunctor p) hp.cofibered)

/-- The action on first-order deformations, specified by the pushforward along the
automorphism `a + εb ↦ a + ε(b + D a)` of the dual numbers. -/
structure DerivationActionData
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) where
  /-- The twisting automorphism attached to a derivation. -/
  twistMap : Derivation Λ k k →
    (artinianDualNumbers.{u, w, v} Λ k ⟶ artinianDualNumbers.{u, w, v} Λ k)
  /-- Its coordinate formula. -/
  twistMap_eq : ∀ (D : Derivation Λ k k) (a b : k),
    (twistMap D).hom (TrivSqZeroExt.inl a +
      TrivSqZeroExt.inr (ULift.up b)) =
        TrivSqZeroExt.inl a + TrivSqZeroExt.inr (ULift.up (b + D a))
  /-- The action of a derivation on a tangent vector. -/
  action : Derivation Λ k k ×
    predeformationTangentSpace.{u, v, w} p hp → predeformationTangentSpace.{u, v, w} p hp
  /-- The action is pushforward along the twisting automorphism. -/
  action_pushforward : ∀ (D : Derivation Λ k k)
      (x : predeformationTangentSpace.{u, v, w} p hp),
    ∃ (x' y : p.Fiber (artinianDualNumbers.{u, w, v} Λ k))
      (φ : x'.1 ⟶ y.1),
      (classOf (BasedCategory.ofFunctor p) hp.cofibered x' = x) ∧
        (p.map φ = eqToHom x'.2 ≫ twistMap D ≫ eqToHom y.2.symm) ∧
          (classOf (BasedCategory.ofFunctor p) hp.cofibered y = action (D, x))
  /-- The zero derivation acts trivially. -/
  zero_action : ∀ x, action (0, x) = x
  /-- The action is additive in the derivation. -/
  add_action : ∀ D E x, action (D + E, x) = action (D, action (E, x))

/-- **Stacks Project, Tag 06SW.** Residue-field derivations act on the tangent space of any
predeformation category by the twisting automorphisms of the dual numbers. -/
@[stacks 06SW, sga "7 VI 1.18" "partial"]
noncomputable def derivationAction
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) : DerivationActionData.{u, v, w} p hp := by
  let 𝓑 : BasedCategory.{v₁, u₁} (ArtinianLocalAlgCat.{u, max v w, w} Λ k) :=
    BasedCategory.ofFunctor p
  let h𝓑 : IsCofiberedInGroupoids 𝓑.p := hp.cofibered
  let 𝓕 := isomorphismClasses 𝓑 h𝓑
  refine {
    twistMap := dualNumbersTwistHom p hp
    twistMap_eq := dualNumbersTwistHom_apply p hp
    action := fun ⟨D, x⟩ => 𝓕.map (dualNumbersTwistHom p hp D) x
    action_pushforward := ?_
    zero_action := ?_
    add_action := ?_ }
  · intro D x
    obtain ⟨x₀, hx₀⟩ := classOf_surjective 𝓑 h𝓑
      (artinianDualNumbers.{u, w, v} Λ k) x
    obtain ⟨x', y, φ, hx, hfac, _⟩ :=
      (dualNumbersDerivationData p hp).action_pushforward
        (uliftDerivation.{u, v, w} D) (toSkeleton x₀)
    let x'B : 𝓑.p.Fiber (artinianDualNumbers.{u, w, v} Λ k) := ⟨x'.1, x'.2⟩
    let yB : 𝓑.p.Fiber (artinianDualNumbers.{u, w, v} Λ k) := ⟨y.1, y.2⟩
    have hxB : toSkeleton x'B = toSkeleton x₀ := hx
    have hclass : classOf 𝓑 h𝓑 x'B = x :=
      (classOf_eq_of_isIsomorphic 𝓑 h𝓑 x'B x₀
        (CategoryTheory.toSkeleton_eq_toSkeleton_iff.mp hxB)).trans hx₀
    have hfac' : p.map φ =
        eqToHom x'.2 ≫ dualNumbersTwistHom p hp D ≫ eqToHom y.2.symm := by
      simpa [dualNumbersTwistHom] using hfac
    have hfacB : 𝓑.p.map φ =
        eqToHom x'B.2 ≫ dualNumbersTwistHom p hp D ≫ eqToHom yB.2.symm := hfac'
    have hLift : 𝓑.p.IsHomLift (dualNumbersTwistHom p hp D) φ :=
      IsHomLift.of_fac' (p := 𝓑.p) (f := dualNumbersTwistHom p hp D) (φ := φ)
        x'B.2 yB.2 hfacB
    let := hLift
    refine ⟨x'B, yB, φ, hclass, hfac', ?_⟩
    calc
      classOf 𝓑 h𝓑 y = 𝓕.map (dualNumbersTwistHom p hp D) (classOf 𝓑 h𝓑 x'B) :=
        (map_classOf 𝓑 h𝓑 (dualNumbersTwistHom p hp D) x'B yB φ).symm
      _ = 𝓕.map (dualNumbersTwistHom p hp D) x := congrArg _ hclass
  · intro x
    change 𝓕.map (dualNumbersTwistHom p hp 0) x = x
    rw [dualNumbersTwistHom_zero]
    simp
  · intro D E x
    change 𝓕.map (dualNumbersTwistHom p hp (D + E)) x =
      𝓕.map (dualNumbersTwistHom p hp D) (𝓕.map (dualNumbersTwistHom p hp E) x)
    rw [dualNumbersTwistHom_add]
    simp

/-- **Stacks Project, Tag 06SW.** The tangent map induced by a morphism of predeformation
categories commutes with the action of residue-field derivations. -/
@[stacks 06SW "naturality"]
theorem derivationAction_natural
    {G : Type u₁} [Category.{v₁} G]
    (p : F ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (q : G ⥤ ArtinianLocalAlgCat.{u, max v w, w} Λ k)
    (hp : IsPredeformationCategory p) (hq : IsPredeformationCategory q)
    (φ : BasedFunctor (BasedCategory.ofFunctor p) (BasedCategory.ofFunctor q))
    (D : Derivation Λ k k)
    (x : predeformationTangentSpace.{u, v, w} p hp) :
    mapIsomorphismClasses hp.cofibered hq.cofibered φ
        (artinianDualNumbers.{u, w, v} Λ k)
        ((derivationAction.{u, v, w} p hp).action (D, x)) =
      (derivationAction.{u, v, w} q hq).action
        (D, mapIsomorphismClasses hp.cofibered hq.cofibered φ
          (artinianDualNumbers.{u, w, v} Λ k) x) := by
  change mapIsomorphismClasses hp.cofibered hq.cofibered φ
      (artinianDualNumbers.{u, w, v} Λ k)
      ((isomorphismClasses (BasedCategory.ofFunctor p) hp.cofibered).map
        (dualNumbersTwistHom p hp D) x) =
    (isomorphismClasses (BasedCategory.ofFunctor q) hq.cofibered).map
      (dualNumbersTwistHom q hq D)
      (mapIsomorphismClasses hp.cofibered hq.cofibered φ
        (artinianDualNumbers.{u, w, v} Λ k) x)
  rw [← dualNumbersTwistHom_eq_of_formula p hp q hq D]
  exact mapIsomorphismClasses_naturality hp.cofibered hq.cofibered φ
    (dualNumbersTwistHom p hp D) x

end

end Deformation
