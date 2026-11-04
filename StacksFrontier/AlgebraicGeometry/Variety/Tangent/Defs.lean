module

public import Mathlib.Algebra.DualNumber
public import Mathlib.Algebra.Module.TransferInstance
public import Mathlib.AlgebraicGeometry.ResidueField
public import Mathlib.RingTheory.Derivation.Basic
public import Mathlib.RingTheory.DualNumber
public import StacksCore.Tactic.StacksAttribute

/-!
# The vector space of tangent arrows

Let `f : X ⟶ S` be a morphism of schemes and let `x` be a point of `X`. The morphisms from the
spectrum of the dual numbers over `κ(x)` to `X` which extend the residue-field point `x` and lie
over the residue-field point `f(x)` form a canonical vector space over `κ(x)`.

The two equations defining `DottedTangentArrow` are the two triangles containing the dotted
arrow in the tangent-space diagram; the remaining parts of that diagram commute by the canonical
residue-field constructions. Such an arrow is the same data as a derivation of the local ring
into its residue field which kills the image of the base, and the vector space structure is
transported along that equivalence.

## Main definitions

* `AlgebraicGeometry.dualNumberClosedPoint`: the closed-point inclusion from `Spec(κ(x))` to the
  spectrum of the dual numbers.
* `AlgebraicGeometry.dualNumberBasePoint`: the canonical morphism from the spectrum of the dual
  numbers to `S` through `Spec(κ(f(x)))`.
* `AlgebraicGeometry.DottedTangentArrow`: the dotted arrows in the tangent-space diagram; with
  the vector space structure below this is the tangent space `T_{X/S, x}`, whose elements are
  the tangent vectors of `X/S` at `x`.
* `AlgebraicGeometry.TangentSpaceStructure`: a vector space structure together with its
  canonical geometric operations.
* `AlgebraicGeometry.dottedTangentArrowModule`: the canonical such structure, whose zero,
  addition and scalar multiplication are characterized geometrically.
* `AlgebraicGeometry.dottedDerivationEquiv`: the dotted arrows are equivalent to the derivations
  of the local ring at `x` into `κ(x)` which kill the image of the local ring of `S`.

## Main results

* `AlgebraicGeometry.dottedTangentArrowAddCommGroup`: the addition of tangent vectors of `X/S`
  at `x`.
* `AlgebraicGeometry.dottedTangentArrowModuleInstance`: the canonical `κ(x)`-vector space
  structure on `AlgebraicGeometry.DottedTangentArrow`, making the dotted arrows the tangent space
  `T_{X/S, x}`.

## Implementation notes

The algebra `DoubleDualNumber κ = κ ⊕ (κ × κ)` has square-zero second summand. Its two
projections to `DualNumber κ` exhibit the corresponding spectrum as the pushout used to add
tangent arrows; the map induced by addition on `κ × κ` sends both infinitesimal generators to
`ε`. Scalar multiplication is precomposition by the endomorphism sending `ε` to `rε`. These
formulas are part of `TangentSpaceStructure`.

## References

* [Stacks Project, Tag 0B2B](https://stacks.math.columbia.edu/tag/0B2B)
* [Stacks Project, Tag 0B2C](https://stacks.math.columbia.edu/tag/0B2C)
-/

@[expose] public section

open CategoryTheory
open IsLocalRing

universe u

namespace AlgebraicGeometry

/-- The closed-point inclusion `Spec(κ(x)) ⟶ Spec(κ(x)[ε])`. -/
noncomputable def dualNumberClosedPoint (X : Scheme.{u}) (x : X) :
    Spec (.of (X.residueField x)) ⟶ Spec (.of (DualNumber (X.residueField x))) :=
  Spec.map (CommRingCat.ofHom
    (TrivSqZeroExt.fstHom (X.residueField x) (X.residueField x) (X.residueField x)))

/-- The canonical morphism `Spec(κ(x)[ε]) ⟶ S` induced by
`κ(f(x)) ⟶ κ(x) ⟶ κ(x)[ε]`. -/
noncomputable def dualNumberBasePoint {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Spec (.of (DualNumber (X.residueField x))) ⟶ S :=
  Spec.map (CommRingCat.ofHom
      (algebraMap (X.residueField x) (DualNumber (X.residueField x)))) ≫
    Spec.map (f.residueFieldMap x) ≫
      S.fromSpecResidueField (f.base x)

/-- A dotted arrow in the tangent-space diagram: a morphism from the spectrum of the dual
numbers which restricts to the point `x` and is a morphism over `S`. Carrying the canonical
`κ(x)`-vector space structure below, this is the tangent space `T_{X/S, x}` of `X` over `S` at
`x`, and its elements are the tangent vectors of `X/S` at `x`. -/
@[stacks 0B2A "the dotted arrows", stacks 0B2C "the tangent space as a set"]
def DottedTangentArrow {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :=
  { θ : Spec (.of (DualNumber (X.residueField x))) ⟶ X //
    dualNumberClosedPoint X x ≫ θ = X.fromSpecResidueField x ∧
      θ ≫ f = dualNumberBasePoint f x }

/-- The `κ`-algebra with square-zero ideal `κ × κ`, whose two generators are denoted informally
by `ε₁` and `ε₂`. -/
abbrev DoubleDualNumber (κ : Type*) := TrivSqZeroExt κ (κ × κ)

/-- The homomorphism `κ[ε₁, ε₂] ⟶ κ[ε]` sending `ε₁` to `ε` and `ε₂` to zero. -/
def firstDualNumberProjection (κ : Type*) [CommRing κ] :
    DoubleDualNumber κ →ₐ[κ] DualNumber κ :=
  TrivSqZeroExt.map (LinearMap.fst κ κ κ)

/-- The homomorphism `κ[ε₁, ε₂] ⟶ κ[ε]` sending `ε₁` to zero and `ε₂` to `ε`. -/
def secondDualNumberProjection (κ : Type*) [CommRing κ] :
    DoubleDualNumber κ →ₐ[κ] DualNumber κ :=
  TrivSqZeroExt.map (LinearMap.snd κ κ κ)

/-- The homomorphism `κ[ε₁, ε₂] ⟶ κ[ε]` sending both `ε₁` and `ε₂` to `ε`. -/
def sumDualNumberProjection (κ : Type*) [CommRing κ] :
    DoubleDualNumber κ →ₐ[κ] DualNumber κ :=
  TrivSqZeroExt.map (LinearMap.fst κ κ κ + LinearMap.snd κ κ κ)

/-- The endomorphism of the dual numbers sending `ε` to `rε`. -/
def scaleDualNumber (κ : Type*) [CommRing κ] (r : κ) :
    DualNumber κ →ₐ[κ] DualNumber κ :=
  TrivSqZeroExt.map (r • LinearMap.id)

/-- The first canonical map from the spectrum of the dual numbers into the square-zero
pushout. -/
noncomputable def firstDualNumberInclusion (κ : Type*) [CommRing κ] :
    Spec (.of (DualNumber κ)) ⟶ Spec (.of (DoubleDualNumber κ)) :=
  Spec.map (CommRingCat.ofHom (firstDualNumberProjection κ))

/-- The second canonical map from the spectrum of the dual numbers into the square-zero
pushout. -/
noncomputable def secondDualNumberInclusion (κ : Type*) [CommRing κ] :
    Spec (.of (DualNumber κ)) ⟶ Spec (.of (DoubleDualNumber κ)) :=
  Spec.map (CommRingCat.ofHom (secondDualNumberProjection κ))

/-- The map from the spectrum of the dual numbers to the square-zero pushout which sends both
infinitesimal generators to `ε`. -/
noncomputable def sumDualNumberMap (κ : Type*) [CommRing κ] :
    Spec (.of (DualNumber κ)) ⟶ Spec (.of (DoubleDualNumber κ)) :=
  Spec.map (CommRingCat.ofHom (sumDualNumberProjection κ))

/-- The self-map of the spectrum of the dual numbers induced by `ε ↦ rε`. -/
noncomputable def scaleDualNumberMap (κ : Type*) [CommRing κ] (r : κ) :
    Spec (.of (DualNumber κ)) ⟶ Spec (.of (DualNumber κ)) :=
  Spec.map (CommRingCat.ofHom (scaleDualNumber κ r))

/-- The structure morphism from the spectrum of the dual numbers to `Spec(κ)`. -/
noncomputable def dualNumberToBase (κ : Type*) [CommRing κ] :
    Spec (.of (DualNumber κ)) ⟶ Spec (.of κ) :=
  Spec.map (CommRingCat.ofHom (algebraMap κ (DualNumber κ)))

/-- A vector space structure on the dotted tangent arrows, together with the geometric formulas
which characterize its zero, addition, and scalar multiplication. -/
structure TangentSpaceStructure {X S : Scheme.{u}} (f : X ⟶ S) (x : X) where
  /-- The additive commutative group structure on tangent arrows. -/
  addCommGroup : AddCommGroup (DottedTangentArrow f x)
  /-- The scalar action of the residue field. -/
  module : letI := addCommGroup
    Module (X.residueField x) (DottedTangentArrow f x)
  /-- The zero tangent arrow factors through the residue-field point. -/
  zero_apply : letI := addCommGroup
    (0 : DottedTangentArrow f x).val =
      dualNumberToBase (X.residueField x) ≫ X.fromSpecResidueField x
  /-- Addition is induced by the square-zero pushout: the two given arrows glue to an arrow out
  of `Spec(κ[ε₁, ε₂])`, and the sum is its pullback along `εᵢ ↦ ε`. -/
  add_apply : letI := addCommGroup
    ∀ θ η : DottedTangentArrow f x,
      ∃ μ : Spec (.of (DoubleDualNumber (X.residueField x))) ⟶ X,
        firstDualNumberInclusion (X.residueField x) ≫ μ = θ.1 ∧
        secondDualNumberInclusion (X.residueField x) ≫ μ = η.1 ∧
        (θ + η).val = sumDualNumberMap (X.residueField x) ≫ μ
  /-- Scalar multiplication is precomposition by the map induced by `ε ↦ rε`. -/
  smul_apply : letI := addCommGroup; letI := module
    ∀ (r : X.residueField x) (θ : DottedTangentArrow f x),
      (r • θ).val = scaleDualNumberMap (X.residueField x) r ≫ θ.1

/-- A dotted tangent arrow sends the closed point of the spectrum of the dual numbers to `x`. -/
lemma dotted_closedPoint {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (θ : DottedTangentArrow f x) :
    θ.1 (closedPoint (CommRingCat.of (DualNumber (X.residueField x)))) = x := by
  let _ : IsLocalHom (CommRingCat.ofHom
      (↑(TrivSqZeroExt.fstHom (X.residueField x) (X.residueField x)
        (X.residueField x)) : DualNumber (X.residueField x) →+* X.residueField x)).hom :=
    IsLocalHom.of_surjective _ (fun r ↦ ⟨TrivSqZeroExt.inl r, rfl⟩)
  have h := congrArg (fun g : Spec (.of (X.residueField x)) ⟶ X ↦
    g (closedPoint (CommRingCat.of (X.residueField x)))) θ.property.1
  change θ.1 (dualNumberClosedPoint X x (closedPoint (CommRingCat.of (X.residueField x)))) =
    (X.fromSpecResidueField x) (closedPoint (CommRingCat.of (X.residueField x))) at h
  unfold dualNumberClosedPoint at h
  rw [Spec_closedPoint] at h
  exact h.trans (Scheme.fromSpecResidueField_apply x _)

/-- The derivations of the local ring at `x` into its residue field which annihilate the image
of the local ring of `S` at `f x`. -/
noncomputable def tangentDerivations {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    letI : Module (X.presheaf.stalk x) (X.residueField x) :=
      Module.compHom _ (X.residue x).hom
    letI : SMulCommClass (X.residueField x) (X.presheaf.stalk x)
        (X.residueField x) := ⟨by
          intro r a v
          change r * ((X.residue x a) * v) = (X.residue x a) * (r * v)
          ring⟩
    Submodule (X.residueField x)
      (Derivation ℤ (X.presheaf.stalk x) (X.residueField x)) := by
  letI : Module (X.presheaf.stalk x) (X.residueField x) :=
    Module.compHom _ (X.residue x).hom
  letI : SMulCommClass (X.residueField x) (X.presheaf.stalk x)
      (X.residueField x) := ⟨by
        intro r a v
        change r * ((X.residue x a) * v) = (X.residue x a) * (r * v)
        ring⟩
  exact { carrier := { D | ∀ s : S.presheaf.stalk (f x), D (f.stalkMap x s) = 0 }
          zero_mem' := fun _ ↦ Derivation.zero_apply _
          add_mem' := fun hD hE s ↦ by simp [hD s, hE s]
          smul_mem' := fun r D hD s ↦ by simp [hD s] }

/-- The map on local rings determined by a dotted tangent arrow. -/
noncomputable def dottedStalkHom {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (θ : DottedTangentArrow f x) :
    X.presheaf.stalk x ⟶ .of (DualNumber (X.residueField x)) :=
  (X.presheaf.stalkCongr (Inseparable.of_eq (dotted_closedPoint f x θ).symm)).hom ≫
    Scheme.stalkClosedPointTo θ.1

/-- The arrow `θ` factors as `Spec` of its map on local rings followed by
`X.fromSpecStalk x`. -/
lemma dottedStalkHom_spec {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (θ : DottedTangentArrow f x) :
    Spec.map (dottedStalkHom f x θ) ≫ X.fromSpecStalk x = θ.1 := by
  have hs := Scheme.SpecMap_stalkSpecializes_fromSpecStalk
    (X := X) ((Inseparable.of_eq (dotted_closedPoint f x θ)).specializes)
  simp only [dottedStalkHom, Spec.map_comp, Category.assoc,
    TopCat.Presheaf.stalkCongr_hom]
  rw [hs]
  exact Scheme.Spec_stalkClosedPointTo_fromSpecStalk θ.1

/-- The map on local rings of a dotted tangent arrow, followed by the projection of the dual
numbers onto `κ(x)`, is the residue map. -/
lemma dottedStalkHom_fst {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (θ : DottedTangentArrow f x) :
    dottedStalkHom f x θ ≫ CommRingCat.ofHom
      (TrivSqZeroExt.fstHom (X.residueField x) (X.residueField x)
        (X.residueField x)).toRingHom = X.residue x := by
  have h : Spec.map (dottedStalkHom f x θ ≫ CommRingCat.ofHom
      (TrivSqZeroExt.fstHom (X.residueField x) (X.residueField x)
        (X.residueField x)).toRingHom) ≫ X.fromSpecStalk x =
      Spec.map (X.residue x) ≫ X.fromSpecStalk x := by
    simpa only [AlgHom.toRingHom_eq_coe, Spec.map_comp, Category.assoc, dottedStalkHom_spec,
      dualNumberClosedPoint, Scheme.fromSpecResidueField] using θ.property.1
  exact Spec.map_inj.mp ((cancel_mono (X.fromSpecStalk x)).mp h)

/-- `Spec.map` of the residue map followed by the inclusion of `κ(x)` into the dual numbers is
the composite of the two `Spec.map`s. -/
private lemma Spec_map_residue_comp_dualNumber {X : Scheme.{u}} (x : X) :
    Spec.map (X.residue x ≫ CommRingCat.ofHom
        (algebraMap (X.residueField x) (DualNumber (X.residueField x)))) =
      Spec.map (CommRingCat.ofHom
          (algebraMap (X.residueField x) (DualNumber (X.residueField x)))) ≫
        Spec.map (X.residue x) :=
  Spec.map_comp _ _

/-- The base point `dualNumberBasePoint f x` factors through `S.fromSpecStalk (f x)`, via the
stalk map of `f`, the residue map and the inclusion of `κ(x)` into the dual numbers. -/
lemma basePoint_asStalk {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    Spec.map (f.stalkMap x ≫ X.residue x ≫
      CommRingCat.ofHom (algebraMap (X.residueField x)
        (DualNumber (X.residueField x)))) ≫ S.fromSpecStalk (f x) =
      dualNumberBasePoint f x := by
  rw [Spec.map_comp, Spec_map_residue_comp_dualNumber, Category.assoc,
    Scheme.SpecMap_stalkMap_fromSpecStalk]
  change Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x)
    (DualNumber (X.residueField x)))) ≫ (X.fromSpecResidueField x ≫ f) = _
  rw [← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField]
  rfl

/-- On the local ring of `S` at `f x`, the map on local rings of a dotted tangent arrow agrees
with the residue map followed by the inclusion of `κ(x)` into the dual numbers. -/
lemma dottedStalkHom_base {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (θ : DottedTangentArrow f x) :
    f.stalkMap x ≫ dottedStalkHom f x θ =
      f.stalkMap x ≫ X.residue x ≫
        CommRingCat.ofHom (algebraMap (X.residueField x)
          (DualNumber (X.residueField x))) := by
  have hl : Spec.map (f.stalkMap x ≫ dottedStalkHom f x θ) ≫
      S.fromSpecStalk (f x) = θ.1 ≫ f := by
    rw [Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkMap_fromSpecStalk, ← Category.assoc,
      dottedStalkHom_spec]
  exact Spec.map_inj.mp <| (cancel_mono (S.fromSpecStalk (f x))).mp
    (hl.trans (θ.property.2.trans (basePoint_asStalk f x).symm))

/-- The derivation determined by a dotted tangent arrow. -/
noncomputable def dottedToDerivation {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (θ : DottedTangentArrow f x) :
    (tangentDerivations f x) := by
  letI : Module (X.presheaf.stalk x) (X.residueField x) :=
    Module.compHom _ (X.residue x).hom
  letI : SMulCommClass (X.residueField x) (X.presheaf.stalk x)
      (X.residueField x) := ⟨by
        intro r a v
        change r * ((X.residue x a) * v) = (X.residue x a) * (r * v)
        ring⟩
  let h := dottedStalkHom f x θ
  let D : Derivation ℤ (X.presheaf.stalk x) (X.residueField x) :=
    { toLinearMap := ((TrivSqZeroExt.sndHom (X.residueField x)
        (X.residueField x)).restrictScalars ℤ).comp h.hom.toAddMonoidHom.toIntLinearMap
      map_one_eq_zero' := by simp [h]
      leibniz' := by
        intro a b
        have ha : (h a).fst = X.residue x a :=
          congrArg (fun g : X.presheaf.stalk x ⟶ X.residueField x ↦ g a)
            (dottedStalkHom_fst f x θ)
        have hb : (h b).fst = X.residue x b :=
          congrArg (fun g : X.presheaf.stalk x ⟶ X.residueField x ↦ g b)
            (dottedStalkHom_fst f x θ)
        change (h (a * b)).snd =
          (X.residue x a) * (h b).snd + (X.residue x b) * (h a).snd
        rw [map_mul, TrivSqZeroExt.snd_mul, ha, hb]
        simp only [MulOpposite.smul_eq_mul_unop, MulOpposite.unop_op]
        ring }
  refine ⟨D, fun s ↦ ?_⟩
  have hs := congrArg (fun g : S.presheaf.stalk (f x) ⟶
      CommRingCat.of (DualNumber (X.residueField x)) ↦ (g s).snd)
    (dottedStalkHom_base f x θ)
  have hs0 : ((f.stalkMap x ≫ X.residue x ≫
      CommRingCat.ofHom (algebraMap (X.residueField x)
        (DualNumber (X.residueField x)))) s).snd = 0 := by
    change (algebraMap (X.residueField x) (DualNumber (X.residueField x))
      (X.residue x (f.stalkMap x s))).snd = 0
    simp [TrivSqZeroExt.algebraMap_eq_inl]
  exact hs.trans hs0

/-- The map on local rings determined by a derivation. -/
noncomputable def derivationStalkHom {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (D : tangentDerivations f x) :
    X.presheaf.stalk x ⟶ .of (DualNumber (X.residueField x)) := by
  letI : Module (X.presheaf.stalk x) (X.residueField x) :=
    Module.compHom _ (X.residue x).hom
  letI : SMulCommClass (X.residueField x) (X.presheaf.stalk x)
      (X.residueField x) := ⟨by
        intro r a v
        change r * ((X.residue x a) * v) = (X.residue x a) * (r * v)
        ring⟩
  exact CommRingCat.ofHom {
    toFun := fun a ↦ (X.residue x a, D.1 a)
    map_one' := TrivSqZeroExt.ext (map_one (X.residue x).hom) D.1.map_one_eq_zero
    map_mul' := by
      intro a b
      apply TrivSqZeroExt.ext
      · exact map_mul (X.residue x).hom a b
      · have hleib := D.1.leibniz a b
        change D.1 (a * b) =
          (X.residue x a) * D.1 b + (X.residue x b) * D.1 a at hleib
        change D.1 (a * b) =
          (X.residue x a) * D.1 b + D.1 a * (X.residue x b)
        rw [hleib, mul_comm (X.residue x b)]
    map_zero' := TrivSqZeroExt.ext (map_zero (X.residue x).hom) (map_zero D.1)
    map_add' := fun a b ↦ TrivSqZeroExt.ext (map_add (X.residue x).hom a b) (map_add D.1 a b) }

/-- The map on local rings of a derivation, followed by the projection of the dual numbers onto
`κ(x)`, is the residue map. -/
lemma derivationStalkHom_fst {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (D : tangentDerivations f x) :
    derivationStalkHom f x D ≫ CommRingCat.ofHom
      (TrivSqZeroExt.fstHom (X.residueField x) (X.residueField x)
        (X.residueField x)).toRingHom = X.residue x := by
  ext a; rfl

/-- On the local ring of `S` at `f x`, the map on local rings of a derivation in
`tangentDerivations f x` agrees with the residue map followed by the inclusion of `κ(x)` into the
dual numbers. -/
lemma derivationStalkHom_base {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (D : tangentDerivations f x) :
    f.stalkMap x ≫ derivationStalkHom f x D =
      f.stalkMap x ≫ X.residue x ≫
        CommRingCat.ofHom (algebraMap (X.residueField x)
          (DualNumber (X.residueField x))) := by
  ext s
  · rfl
  · exact D.property s

/-- The dotted tangent arrow determined by a derivation. -/
noncomputable def derivationToDotted {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (D : tangentDerivations f x) : DottedTangentArrow f x := by
  let h := derivationStalkHom f x D
  refine ⟨Spec.map h ≫ X.fromSpecStalk x, ?_, ?_⟩
  · change dualNumberClosedPoint X x ≫ (Spec.map h ≫ X.fromSpecStalk x) =
      X.fromSpecResidueField x
    simp only [dualNumberClosedPoint,
      ← Category.assoc, ← Spec.map_comp,
      Scheme.fromSpecResidueField]
    simpa only [h, AlgHom.toRingHom_eq_coe] using
      congrArg (fun g ↦ Spec.map g ≫ X.fromSpecStalk x)
        (derivationStalkHom_fst f x D)
  · change (Spec.map h ≫ X.fromSpecStalk x) ≫ f = dualNumberBasePoint f x
    rw [Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
      ← Category.assoc, ← Spec.map_comp, derivationStalkHom_base]
    exact basePoint_asStalk f x

/-- The map on local rings of the dotted tangent arrow of a derivation is the map on local rings of
that derivation. -/
lemma dottedStalkHom_derivationToDotted {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (D : tangentDerivations f x) :
    dottedStalkHom f x (derivationToDotted f x D) = derivationStalkHom f x D := by
  apply Spec.map_inj.mp
  apply (cancel_mono (X.fromSpecStalk x)).mp
  rw [dottedStalkHom_spec]
  rfl

/-- Passing from a derivation to its dotted tangent arrow and back returns the derivation. -/
lemma dottedToDerivation_derivationToDotted {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) (D : tangentDerivations f x) :
    dottedToDerivation f x (derivationToDotted f x D) = D := by
  let _ : Module (X.presheaf.stalk x) (X.residueField x) :=
    Module.compHom _ (X.residue x).hom
  refine Subtype.ext (Derivation.ext fun a ↦ ?_)
  change (dottedStalkHom f x (derivationToDotted f x D) a).snd = D.1 a
  rw [dottedStalkHom_derivationToDotted]
  rfl

/-- Passing from a dotted tangent arrow to its derivation and back returns the arrow. -/
lemma derivationToDotted_dottedToDerivation {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) (θ : DottedTangentArrow f x) :
    derivationToDotted f x (dottedToDerivation f x θ) = θ := by
  have hh : derivationStalkHom f x (dottedToDerivation f x θ) =
      dottedStalkHom f x θ := by
    ext a
    · exact (congrArg (fun g : X.presheaf.stalk x ⟶ X.residueField x ↦ g a)
        (dottedStalkHom_fst f x θ)).symm
    · rfl
  apply Subtype.ext
  change Spec.map (derivationStalkHom f x (dottedToDerivation f x θ)) ≫
    X.fromSpecStalk x = θ.1
  rw [hh, dottedStalkHom_spec]

/-- Dotted tangent arrows are the same data as derivations annihilating the base. -/
noncomputable def dottedDerivationEquiv {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) : DottedTangentArrow f x ≃ tangentDerivations f x where
  toFun := dottedToDerivation f x
  invFun := derivationToDotted f x
  left_inv := derivationToDotted_dottedToDerivation f x
  right_inv := dottedToDerivation_derivationToDotted f x

/-- The map on local rings of `r • D` is that of `D` followed by `ε ↦ rε`. -/
lemma derivationStalkHom_smul {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (r : X.residueField x) (D : tangentDerivations f x) :
    derivationStalkHom f x (r • D) = derivationStalkHom f x D ≫
      CommRingCat.ofHom (scaleDualNumber (X.residueField x) r) := by
  ext a
  · change X.residue x a =
        (scaleDualNumber (X.residueField x) r (derivationStalkHom f x D a)).fst
    simp only [scaleDualNumber, TrivSqZeroExt.fst_map]
    rfl
  · change (r • D).val a =
        (scaleDualNumber (X.residueField x) r (derivationStalkHom f x D a)).snd
    simp only [scaleDualNumber, TrivSqZeroExt.snd_map]
    rfl

/-- The map to the square-zero pushout determined by a pair of derivations. -/
noncomputable def derivationPairStalkHom {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (D E : tangentDerivations f x) :
    X.presheaf.stalk x ⟶ .of (DoubleDualNumber (X.residueField x)) := by
  letI : Module (X.presheaf.stalk x) (X.residueField x) :=
    Module.compHom _ (X.residue x).hom
  letI : SMulCommClass (X.residueField x) (X.presheaf.stalk x)
      (X.residueField x) := ⟨by
        intro r a v
        change r * ((X.residue x a) * v) = (X.residue x a) * (r * v)
        ring⟩
  exact CommRingCat.ofHom {
    toFun := fun a ↦ (X.residue x a, (D.1 a, E.1 a))
    map_one' := TrivSqZeroExt.ext (map_one (X.residue x).hom)
      (Prod.ext (Derivation.map_one_eq_zero _) (Derivation.map_one_eq_zero _))
    map_mul' := by
      intro a b
      apply TrivSqZeroExt.ext
      · exact map_mul (X.residue x).hom a b
      · apply Prod.ext
        · have hleib := D.1.leibniz a b
          change D.1 (a * b) =
            (X.residue x a) * D.1 b + (X.residue x b) * D.1 a at hleib
          change D.1 (a * b) =
            (X.residue x a) * D.1 b + D.1 a * (X.residue x b)
          rw [hleib, mul_comm (X.residue x b)]
        · have hleib := E.1.leibniz a b
          change E.1 (a * b) =
            (X.residue x a) * E.1 b + (X.residue x b) * E.1 a at hleib
          change E.1 (a * b) =
            (X.residue x a) * E.1 b + E.1 a * (X.residue x b)
          rw [hleib, mul_comm (X.residue x b)]
    map_zero' := TrivSqZeroExt.ext (map_zero (X.residue x).hom)
      (Prod.ext (map_zero _) (map_zero _))
    map_add' := fun a b ↦ TrivSqZeroExt.ext (map_add (X.residue x).hom a b)
      (Prod.ext (map_add _ a b) (map_add _ a b)) }

/-- Composing the map of a pair `(D, E)` to `κ(x)[ε₁, ε₂]` with the map induced by a linear map
`φ : κ × κ → κ` gives the map on local rings of any `D'` with `D' a = φ (D a, E a)`. -/
private lemma derivationPairStalkHom_comp {X S : Scheme.{u}} (f : X ⟶ S) (x : X)
    (D E D' : tangentDerivations f x)
    (φ : X.residueField x × X.residueField x →ₗ[X.residueField x] X.residueField x)
    (hφ : ∀ a, φ (D.1 a, E.1 a) = D'.1 a) :
    derivationPairStalkHom f x D E ≫ CommRingCat.ofHom (TrivSqZeroExt.map φ) =
      derivationStalkHom f x D' := by
  ext a
  · change (TrivSqZeroExt.map φ (derivationPairStalkHom f x D E a)).fst = X.residue x a
    rw [TrivSqZeroExt.fst_map]
    rfl
  · change (TrivSqZeroExt.map φ (derivationPairStalkHom f x D E a)).snd = D'.1 a
    rw [TrivSqZeroExt.snd_map]
    exact hφ a

/-- The map to `κ(x)[ε₁, ε₂]` of a pair `(D, E)`, followed by the first projection, is the map on
local rings of `D`. -/
lemma derivationPairStalkHom_first {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (D E : tangentDerivations f x) :
    derivationPairStalkHom f x D E ≫
      CommRingCat.ofHom (firstDualNumberProjection (X.residueField x)) =
        derivationStalkHom f x D :=
  derivationPairStalkHom_comp f x D E D _ fun _ ↦ rfl

/-- The map to `κ(x)[ε₁, ε₂]` of a pair `(D, E)`, followed by the second projection, is the map on
local rings of `E`. -/
lemma derivationPairStalkHom_second {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (D E : tangentDerivations f x) :
    derivationPairStalkHom f x D E ≫
      CommRingCat.ofHom (secondDualNumberProjection (X.residueField x)) =
        derivationStalkHom f x E :=
  derivationPairStalkHom_comp f x D E E _ fun _ ↦ rfl

/-- The map to `κ(x)[ε₁, ε₂]` of a pair `(D, E)`, followed by `ε₁, ε₂ ↦ ε`, is the map on local
rings of `D + E`. -/
lemma derivationPairStalkHom_sum {X S : Scheme.{u}} (f : X ⟶ S)
    (x : X) (D E : tangentDerivations f x) :
    derivationPairStalkHom f x D E ≫
      CommRingCat.ofHom (sumDualNumberProjection (X.residueField x)) =
        derivationStalkHom f x (D + E) :=
  derivationPairStalkHom_comp f x D E (D + E) _ fun _ ↦ rfl

/-- The dotted arrows in the tangent-space diagram carry a canonical vector space structure over
the residue field `κ(x)`. Its operations are characterized by the square-zero pushout and by
scaling the infinitesimal generator. -/
@[stacks 0B2B]
noncomputable def dottedTangentArrowModule {X S : Scheme.{u}} (f : X ⟶ S) (x : X) :
    TangentSpaceStructure f x :=
  let e := dottedDerivationEquiv f x
  letI : AddCommGroup (DottedTangentArrow f x) := e.addCommGroup
  letI : Module (X.residueField x) (DottedTangentArrow f x) :=
    (e.addEquiv).module (X.residueField x)
  { addCommGroup := inferInstance
    module := inferInstance
    zero_apply := by
      change (derivationToDotted f x (0 : tangentDerivations f x)).val =
        dualNumberToBase (X.residueField x) ≫ X.fromSpecResidueField x
      have hh : derivationStalkHom f x (0 : tangentDerivations f x) =
          X.residue x ≫ CommRingCat.ofHom
            (algebraMap (X.residueField x) (DualNumber (X.residueField x))) := by
        ext a
        · rfl
        · change (0 : tangentDerivations f x).val a = 0
          simp
      change Spec.map (derivationStalkHom f x 0) ≫ X.fromSpecStalk x =
        Spec.map (CommRingCat.ofHom (algebraMap (X.residueField x)
          (DualNumber (X.residueField x)))) ≫
          (Spec.map (X.residue x) ≫ X.fromSpecStalk x)
      rw [hh, ← Spec.map_comp_assoc]
      rfl
    add_apply := by
      intro θ η
      let D := dottedToDerivation f x θ
      let E := dottedToDerivation f x η
      let h := derivationPairStalkHom f x D E
      refine ⟨Spec.map h ≫ X.fromSpecStalk x, ?_, ?_, ?_⟩
      · change Spec.map (CommRingCat.ofHom
            (firstDualNumberProjection (X.residueField x))) ≫
            (Spec.map h ≫ X.fromSpecStalk x) = θ.val
        conv_rhs => rw [← derivationToDotted_dottedToDerivation f x θ]
        change Spec.map (CommRingCat.ofHom
            (firstDualNumberProjection (X.residueField x))) ≫
            (Spec.map h ≫ X.fromSpecStalk x) =
          Spec.map (derivationStalkHom f x D) ≫ X.fromSpecStalk x
        rw [← Spec.map_comp_assoc, derivationPairStalkHom_first]
      · change Spec.map (CommRingCat.ofHom
            (secondDualNumberProjection (X.residueField x))) ≫
            (Spec.map h ≫ X.fromSpecStalk x) = η.val
        conv_rhs => rw [← derivationToDotted_dottedToDerivation f x η]
        change Spec.map (CommRingCat.ofHom
            (secondDualNumberProjection (X.residueField x))) ≫
            (Spec.map h ≫ X.fromSpecStalk x) =
          Spec.map (derivationStalkHom f x E) ≫ X.fromSpecStalk x
        rw [← Spec.map_comp_assoc, derivationPairStalkHom_second]
      · change (derivationToDotted f x (D + E)).val =
          Spec.map (CommRingCat.ofHom
            (sumDualNumberProjection (X.residueField x))) ≫
              (Spec.map h ≫ X.fromSpecStalk x)
        change Spec.map (derivationStalkHom f x (D + E)) ≫ X.fromSpecStalk x =
          Spec.map (CommRingCat.ofHom
            (sumDualNumberProjection (X.residueField x))) ≫
              (Spec.map h ≫ X.fromSpecStalk x)
        rw [← Spec.map_comp_assoc, derivationPairStalkHom_sum]
    smul_apply := by
      intro r θ
      change (derivationToDotted f x
        (r • dottedToDerivation f x θ)).val =
          scaleDualNumberMap (X.residueField x) r ≫ θ.val
      conv_rhs => rw [← derivationToDotted_dottedToDerivation f x θ]
      change Spec.map (derivationStalkHom f x
          (r • dottedToDerivation f x θ)) ≫ X.fromSpecStalk x =
        Spec.map (CommRingCat.ofHom (scaleDualNumber (X.residueField x) r)) ≫
          (Spec.map (derivationStalkHom f x (dottedToDerivation f x θ)) ≫
            X.fromSpecStalk x)
      rw [derivationStalkHom_smul, ← Spec.map_comp_assoc] }

/-- The canonical additive commutative group structure on dotted tangent arrows, i.e. the
addition of tangent vectors of `X/S` at `x`. -/
@[stacks 0B2C "the additive group of tangent vectors"]
noncomputable instance dottedTangentArrowAddCommGroup {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) : AddCommGroup (DottedTangentArrow f x) :=
  (dottedTangentArrowModule f x).addCommGroup

/-- The canonical `κ(x)`-vector space structure on dotted tangent arrows; with it the dotted
arrows are the tangent space `T_{X/S, x}`. -/
@[stacks 0B2C "the canonical κ(x)-vector space structure on the tangent space"]
noncomputable instance dottedTangentArrowModuleInstance {X S : Scheme.{u}}
    (f : X ⟶ S) (x : X) : Module (X.residueField x) (DottedTangentArrow f x) :=
  (dottedTangentArrowModule f x).module

end AlgebraicGeometry

end
