module

public import StacksFrontier.AlgebraicGeometry.Curves.BombieriStepanov.Local
public import StacksFrontier.AlgebraicGeometry.FieldToResidue
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.ClosedPointCodimension
public import Mathlib.AlgebraicGeometry.ValuativeCriterion

/-!
# The places of a proper curve are the valuation rings of its function field

Let `X` be an integral scheme, universally closed over a field `k`. Every valuation subring `V` of
the function field `R(X)` containing `k` dominates the local ring of `X` at some point: this is
the existence half of the valuative criterion, applied to the square formed by the generic point
`Spec R(X) ⟶ X` and `Spec V ⟶ Spec k`. If moreover `X` is a curve whose local rings at closed
points are discrete valuation rings and `V ≠ R(X)`, the dominated local ring is a discrete
valuation ring, and a valuation ring dominating a valuation ring with the same fraction field is
equal to it. So `V` is the local ring of `X` at a place `P`, and `V = {f | ord_P f ≥ 0}`.

## Main results

* `Stacks.BombieriStepanov.fromSpecStalk_comp_eq_specMap_fieldToStalk`: the composite
  `Spec 𝒪_{X,x} ⟶ X ⟶ Spec k` is induced by `k → 𝒪_{X,x}`.
* `Stacks.BombieriStepanov.exists_isLocalHom_stalk_valuationSubring`: the valuative criterion
  read on the function field, a point whose local ring `V` dominates.
* `Stacks.BombieriStepanov.exists_curvePlace_mem_iff`: on a curve with discrete valuation rings
  at its places, every proper valuation subring containing `k` is `{f | ord_P f ≥ 0}`.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Order

universe u

namespace Stacks.BombieriStepanov

variable {k : Type u} [Field k] {X : Scheme.{u}} (p : X ⟶ Spec (.of k))

/-- The composite `Spec 𝒪_{X,x} ⟶ X ⟶ Spec k` is induced by the ring map `k → 𝒪_{X,x}`. -/
theorem fromSpecStalk_comp_eq_specMap_fieldToStalk (x : X) :
    X.fromSpecStalk x ≫ p = Spec.map (fieldToStalk p x) := by
  have h : p = X.toSpecΓ ≫ Spec.map p.appTop ≫ Spec.map (Scheme.ΓSpecIso (.of k)).inv := by
    rw [← Scheme.toSpecΓ_naturality_assoc, toSpecΓ_SpecMap_ΓSpecIso_inv, Category.comp_id]
  conv_lhs => rw [h]
  rw [← Category.assoc, Scheme.fromSpecStalk_toSpecΓ, ← Spec.map_comp, ← Spec.map_comp,
    fieldToStalk, Category.assoc]

variable [IsIntegral X]

/-- **The valuative criterion on the function field.** Let `X` be integral and universally closed
over `k`, and let `V` be a valuation subring of `R(X)` containing (the image of) `k`. Then there
is a point `x` of `X` and a local homomorphism `𝒪_{X,x} → V` through which the inclusion
`𝒪_{X,x} → R(X)` factors. -/
theorem exists_isLocalHom_stalk_valuationSubring [UniversallyClosed p]
    (V : ValuationSubring X.functionField)
    (hk : ∀ c : k, (fieldToStalk p (genericPoint X)).hom c ∈ V) :
    ∃ (x : X) (φ : X.presheaf.stalk x →+* V), IsLocalHom φ ∧
      ∀ a, (φ a : X.functionField) = algebraMap (X.presheaf.stalk x) X.functionField a := by
  let : Algebra k V :=
    ((fieldToStalk p (genericPoint X)).hom.codRestrict V.toSubring hk).toAlgebra
  have hex : ValuativeCriterion.Existence p := by
    have h : (ValuativeCriterion.Existence ⊓ @QuasiCompact) p := by
      rw [← UniversallyClosed.eq_valuativeCriterion]
      infer_instance
    exact h.1
  let S : ValuativeCommSq p :=
    { R := V
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := Spec.map (CommRingCat.ofHom (algebraMap k V))
      commSq := ⟨by
        rw [fromSpecStalk_comp_eq_specMap_fieldToStalk, ← Spec.map_comp]
        congr 1⟩ }
  obtain ⟨l, hl₁, -⟩ := (hex S).exists_lift
  refine ⟨l (IsLocalRing.closedPoint V), (Scheme.stalkClosedPointTo l).hom, inferInstance,
    fun a => ?_⟩
  -- `l = Spec φ ≫ (Spec 𝒪_{X,x} ⟶ X)`, and the generic point factors through `Spec 𝒪_{X,x}`
  have hl : Spec.map (Scheme.stalkClosedPointTo l) ≫ X.fromSpecStalk _ = l :=
    Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
  have hgen : genericPoint X ⤳ l (IsLocalRing.closedPoint V) := genericPoint_specializes _
  have key : Spec.map (Scheme.stalkClosedPointTo l ≫ CommRingCat.ofHom (algebraMap V
      X.functionField)) ≫ X.fromSpecStalk (l (IsLocalRing.closedPoint V)) =
      Spec.map (X.presheaf.stalkSpecializes hgen) ≫
        X.fromSpecStalk (l (IsLocalRing.closedPoint V)) := by
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Spec.map_comp, Category.assoc, hl]
    exact hl₁
  exact congrArg (fun g => g.hom a) (Spec.map_injective ((cancel_mono _).1 key))

/-- On the generic point the inclusion of the local ring into the function field is the
identity. -/
theorem algebraMap_stalk_genericPoint (a : X.presheaf.stalk (genericPoint X)) :
    @algebraMap (X.presheaf.stalk (genericPoint X)) X.functionField _ _
      (stalkFunctionFieldAlgebra X (genericPoint X)) a = a := by
  have h : X.presheaf.stalkSpecializes ((genericPoint_spec X).specializes trivial) = 𝟙 _ :=
    TopCat.Presheaf.stalkSpecializes_refl _ _
  simp only [RingHom.algebraMap_toAlgebra, h]
  rfl

/-- **A proper valuation subring of the function field of a curve is the local ring at a place.**
Let `X` be an integral curve, universally closed over `k`, whose local rings at the points of
codimension one are discrete valuation rings. A valuation subring `V ≠ R(X)` containing `k` is
the image of `𝒪_{X,P}` for a place `P`. -/
theorem exists_curvePlace_mem_iff [UniversallyClosed p] [IsCurve k p]
    (hdvr : ∀ x : X, coheight x = 1 → IsDiscreteValuationRing (X.presheaf.stalk x))
    (V : ValuationSubring X.functionField)
    (hk : ∀ c : k, (fieldToStalk p (genericPoint X)).hom c ∈ V) (hV : V ≠ ⊤) :
    ∃ P : CurvePlace X, ∀ f : X.functionField,
      f ∈ V ↔ ∃ a : X.presheaf.stalk P.1, algebraMap _ X.functionField a = f := by
  obtain ⟨x, φ, hloc, hφ⟩ := exists_isLocalHom_stalk_valuationSubring p V hk
  -- an element of `V` whose inverse is an element of `V` is a unit of `V`
  have hunit : ∀ (f : X.functionField) (hf : f ∈ V), f⁻¹ ∈ V → f ≠ 0 → IsUnit (⟨f, hf⟩ : V) := by
    intro f hf hf' hf0
    refine IsUnit.of_mul_eq_one (⟨f⁻¹, hf'⟩ : V) (Subtype.ext ?_)
    simp [mul_inv_cancel₀ hf0]
  -- an element of `V` which is a unit of `V` has its inverse in `V`
  have hinv : ∀ (f : X.functionField) (hf : f ∈ V), IsUnit (⟨f, hf⟩ : V) → f⁻¹ ∈ V := by
    rintro f hf ⟨w, hw⟩
    have h3 := congrArg (fun z : V => (z : X.functionField)) (Units.mul_inv w)
    simp only [hw, MulMemClass.coe_mul, OneMemClass.coe_one] at h3
    have h4 : (((w⁻¹ : Vˣ) : V) : X.functionField) = f⁻¹ :=
      eq_inv_of_mul_eq_one_right h3
    exact h4 ▸ ((w⁻¹ : Vˣ) : V).2
  obtain ⟨g, hgV⟩ : ∃ g : X.functionField, g ∉ V := by
    by_contra! h
    exact hV (eq_top_iff.2 fun g _ => h g)
  have hg0 : g ≠ 0 := fun h => hgV (h ▸ V.zero_mem)
  have hgV' : g⁻¹ ∈ V := (V.mem_or_inv_mem g).resolve_left hgV
  -- the point is not the generic point: there `g⁻¹` would be a unit of `V`
  have hx : x ≠ genericPoint X := by
    rintro rfl
    have ha : ((φ g⁻¹ : V) : X.functionField) = g⁻¹ :=
      (hφ g⁻¹).trans (algebraMap_stalk_genericPoint (X := X) g⁻¹)
    have hu : IsUnit (g⁻¹ : X.presheaf.stalk (genericPoint X)) :=
      isUnit_iff_ne_zero.2 (inv_ne_zero hg0)
    have hu' : IsUnit (φ g⁻¹) := hu.map φ
    have h' : (φ g⁻¹) = ⟨g⁻¹, hgV'⟩ := Subtype.ext ha
    rw [h'] at hu'
    exact hgV (by simpa using hinv g⁻¹ hgV' hu')
  have hcoh : coheight x = 1 := IsCurve.coheight_eq_one p hx
  have := hdvr x hcoh
  refine ⟨⟨x, hcoh⟩, fun f => ⟨fun hf => ?_, ?_⟩⟩
  · rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk x) f with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact ⟨a, ha⟩
    rcases eq_or_ne f 0 with rfl | hf0
    · exact ⟨0, map_zero _⟩
    by_cases hau : IsUnit a
    · refine ⟨↑hau.unit⁻¹, ?_⟩
      have h1 : algebraMap (X.presheaf.stalk x) X.functionField ↑hau.unit⁻¹ * f⁻¹ = 1 := by
        rw [← ha, ← map_mul, IsUnit.val_inv_mul, map_one]
      exact (mul_inv_eq_one₀ hf0).1 h1
    · exfalso
      have hfV' : f⁻¹ ∈ V := by
        rw [← ha, ← hφ a]
        exact (φ a).2
      have h' : φ a = ⟨f⁻¹, hfV'⟩ := Subtype.ext ((hφ a).trans ha)
      have hu := hunit f⁻¹ hfV' (by simpa using hf) (inv_ne_zero hf0)
      rw [← h'] at hu
      exact hau (isUnit_of_map_unit φ a hu)
  · rintro ⟨a, rfl⟩
    rw [← hφ a]
    exact (φ a).2

/-- The local ring at a point with valuation ring stalk, as a valuation subring of the function
field. -/
def stalkValuationSubring (x : X) [ValuationRing (X.presheaf.stalk x)] :
    ValuationSubring X.functionField :=
  .ofSubring (algebraMap (X.presheaf.stalk x) X.functionField).range fun f => by
    rcases ValuationRing.isInteger_or_isInteger (X.presheaf.stalk x) f with ⟨a, ha⟩ | ⟨a, ha⟩
    · exact Or.inl ⟨a, ha⟩
    · exact Or.inr ⟨a, ha⟩

/-- Membership in the valuation subring of a local ring. -/
theorem mem_stalkValuationSubring_iff (x : X) [ValuationRing (X.presheaf.stalk x)]
    (f : X.functionField) : f ∈ stalkValuationSubring x ↔
      ∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = f := Iff.rfl

/-- The local ring is isomorphic to its image in the function field. -/
def stalkEquivValuationSubring (x : X) [ValuationRing (X.presheaf.stalk x)] :
    X.presheaf.stalk x ≃+* stalkValuationSubring x :=
  RingEquiv.ofBijective
    ((algebraMap (X.presheaf.stalk x) X.functionField).codRestrict
      (stalkValuationSubring x).toSubring fun a => ⟨a, rfl⟩)
    ⟨Function.Injective.of_comp (f := Subtype.val)
      (IsFractionRing.injective (X.presheaf.stalk x) X.functionField),
      fun y => let ⟨a, ha⟩ := y.2; ⟨a, Subtype.ext ha⟩⟩

/-- The isomorphism of the local ring with its image is the inclusion. -/
theorem coe_stalkEquivValuationSubring (x : X) [ValuationRing (X.presheaf.stalk x)]
    (a : X.presheaf.stalk x) : (stalkEquivValuationSubring x a : X.functionField) =
      algebraMap _ X.functionField a := rfl

/-- If the local ring of `X` at a point `z` is identified with a valuation subring `V` of `R(X)`
compatibly with the inclusions into `R(X)`, then the induced map `Spec V ⟶ X` restricts on the
generic point of `Spec V` to the generic point `Spec R(X) ⟶ X` of `X`. -/
private theorem specMap_algebraMap_comp_fromSpecStalk (V : ValuationSubring X.functionField) :
    ∀ (z : X) (e : X.presheaf.stalk z ≃+* V),
      (∀ a, (e a : X.functionField) = algebraMap _ X.functionField a) →
      Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫
        Spec.map (CommRingCat.ofHom (e : X.presheaf.stalk z →+* V)) ≫ X.fromSpecStalk z =
        X.fromSpecStalk (genericPoint X) := by
  intro z e he
  rw [← Category.assoc, ← Spec.map_comp, ← Scheme.SpecMap_stalkSpecializes_fromSpecStalk
    (genericPoint_specializes z)]
  congr 2
  ext a
  exact he a

/-- Two morphisms `Spec V ⟶ Spec k` out of the spectrum of a valuation subring `V` of `R(X)`
agreeing after composition with `Spec R(X) ⟶ Spec V` are equal: on rings this is the injectivity
of `V → R(X)`. -/
private theorem hom_ext_of_specMap_algebraMap_comp_eq (V : ValuationSubring X.functionField) :
    ∀ a b : Spec (.of V) ⟶ Spec (.of k),
      Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ a =
        Spec.map (CommRingCat.ofHom (algebraMap V X.functionField)) ≫ b → a = b := by
  intro a b hab
  obtain ⟨a, rfl⟩ := Spec.map_surjective a
  obtain ⟨b, rfl⟩ := Spec.map_surjective b
  rw [← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at hab
  congr 1
  ext c
  exact congrArg (fun g => g.hom c) hab

/-- **A point of a separated scheme is determined by its local ring.** Two points with valuation
ring local rings having the same image in the function field are equal: both local rings give
lifts in the same valuative square, which are equal by separatedness. -/
theorem eq_of_forall_algebraMap_iff [IsSeparated p] {x y : X} [ValuationRing (X.presheaf.stalk x)]
    [ValuationRing (X.presheaf.stalk y)]
    (h : ∀ f : X.functionField, (∃ a : X.presheaf.stalk x, algebraMap _ X.functionField a = f) ↔
      ∃ b : X.presheaf.stalk y, algebraMap _ X.functionField b = f) : x = y := by
  have hV : stalkValuationSubring x = stalkValuationSubring y := by
    ext f
    exact h f
  set V := stalkValuationSubring x
  let ex : X.presheaf.stalk x ≃+* V := stalkEquivValuationSubring x
  let ey : X.presheaf.stalk y ≃+* V := (stalkEquivValuationSubring y).trans
    (RingEquiv.subringCongr (congrArg ValuationSubring.toSubring hV.symm))
  have hey : ∀ b, (ey b : X.functionField) = algebraMap _ X.functionField b := fun b => rfl
  let lx : Spec (.of V) ⟶ X := Spec.map (CommRingCat.ofHom (ex : X.presheaf.stalk x →+* V)) ≫
    X.fromSpecStalk x
  let ly : Spec (.of V) ⟶ X := Spec.map (CommRingCat.ofHom (ey : X.presheaf.stalk y →+* V)) ≫
    X.fromSpecStalk y
  have hgen := specMap_algebraMap_comp_fromSpecStalk V
  -- maps `Spec V ⟶ Spec k` are determined after composing with `Spec R(X) ⟶ Spec V`
  have hepi := hom_ext_of_specMap_algebraMap_comp_eq (k := k) V
  have hx' : ∀ a, (ex a : X.functionField) = algebraMap _ X.functionField a := fun a => rfl
  let S : ValuativeCommSq p :=
    { R := V
      K := X.functionField
      i₁ := X.fromSpecStalk (genericPoint X)
      i₂ := lx ≫ p
      commSq := ⟨by rw [← hgen x ex hx', Category.assoc, Category.assoc]⟩ }
  have hU : ValuativeCriterion.Uniqueness p := IsSeparated.valuativeCriterion p
  have := hU S
  let hlx : S.commSq.LiftStruct := ⟨lx, hgen x ex hx', rfl⟩
  let hly : S.commSq.LiftStruct := ⟨ly, hgen y ey hey, hepi _ _ (by
    change Spec.map _ ≫ (Spec.map _ ≫ X.fromSpecStalk y) ≫ p =
      Spec.map _ ≫ (Spec.map _ ≫ X.fromSpecStalk x) ≫ p
    simp only [Category.assoc]
    rw [reassoc_of% (hgen y ey hey), reassoc_of% (hgen x ex hx')])⟩
  have hl : lx = ly := congrArg CommSq.LiftStruct.l (Subsingleton.elim hlx hly)
  -- the closed point of `Spec V` maps to `z` under the map induced by `X.stalk z ≃+* V`
  have hclosed : ∀ (z : X) (e : X.presheaf.stalk z ≃+* V),
      (X.fromSpecStalk z) ((Spec.map (CommRingCat.ofHom (e : X.presheaf.stalk z →+* V)))
        (IsLocalRing.closedPoint V)) = z := by
    intro z e
    have : IsLocalHom (CommRingCat.ofHom (e : X.presheaf.stalk z →+* V)).hom :=
      inferInstanceAs (IsLocalHom (e : X.presheaf.stalk z →+* V))
    rw [Spec_closedPoint, Scheme.fromSpecStalk_closedPoint]
  exact (hclosed x ex).symm.trans
    ((congrArg (fun g : Spec (.of V) ⟶ X => g (IsLocalRing.closedPoint V)) hl).trans
      (hclosed y ey))

end Stacks.BombieriStepanov

end
