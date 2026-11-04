module

public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import Mathlib.RingTheory.Valuation.LocalSubring
public import Mathlib.Algebra.Polynomial.Lifts

/-!
# Residue functions regular along the closure of a point of a proper scheme

Let `f : X ⟶ Spec R` be universally closed, let `y ∈ X` and let `γ ∈ κ(y)`. Suppose that `γ`
is regular along the closure of `y`: for every specialization `y ⤳ x` the element `γ` is the
image of an element of `𝒪_{X, x}` under `𝒪_{X, x} ⟶ 𝒪_{X, y} ⟶ κ(y)`. Then `γ` is integral
over `R`.

This is the integrality of the global functions on the reduced closed subscheme `\overline{{y}}`
of a proper scheme over an affine base, read off at its generic point; it is proved here by the
valuative criterion, without constructing that subscheme.

## Main results

* `AlgebraicGeometry.isIntegralElem_residue_of_forall_specializes`: the integrality statement.

## Implementation notes

The map `R ⟶ κ(y)` is `R ⟶ 𝒪_{Spec R, f y} ⟶ 𝒪_{X, y} ⟶ κ(y)`. An element of `κ(y)` lies in the
integral closure of the image of `R` as soon as it lies in every valuation subring containing that
image (`iInf_valuationSubring_superset`). For such a valuation subring `V` the valuative criterion
lifts `Spec V ⟶ Spec R` to `X` compatibly with `Spec κ(y) ⟶ X`; the closed point of `Spec V`
goes to a specialization `x` of `y`, and the local homomorphism `𝒪_{X, x} ⟶ V` agrees with
`𝒪_{X, x} ⟶ κ(y)` because `Spec 𝒪_{X, x} ⟶ X` is a monomorphism.

## References

* [Stacks Project, Tag 01KF](https://stacks.math.columbia.edu/tag/01KF)
* [Stacks Project, Tag 0AXJ](https://stacks.math.columbia.edu/tag/0AXJ)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec R)

/-- The canonical map from the base ring to the residue field of a point of a scheme over
`Spec R`. -/
def residueAlgebraMap (y : X) : R ⟶ X.residueField y :=
  StructureSheaf.toStalk R (f y) ≫ f.stalkMap y ≫ X.residue y

/-- The two maps `Spec κ(y) ⟶ Spec R` agree: through `X`, and through `residueAlgebraMap`. -/
lemma fromSpecResidueField_comp_eq_SpecMap_residueAlgebraMap (y : X) :
    X.fromSpecResidueField y ≫ f = Spec.map (residueAlgebraMap f y) := by
  rw [Scheme.fromSpecResidueField, Category.assoc, ← Scheme.SpecMap_stalkMap_fromSpecStalk,
    Spec.fromSpecStalk_eq', residueAlgebraMap, Spec.map_comp (StructureSheaf.toStalk R (f y))]
  exact (Category.assoc _ _ _).symm.trans
    (congrArg (· ≫ Spec.map (StructureSheaf.toStalk R (f y))) (Spec.map_comp _ _).symm)

/-- Two ring maps out of a stalk which induce the same morphism to `X` after composing with
`Spec 𝒪_{X, x} ⟶ X` are equal, the latter being a monomorphism. -/
lemma eq_of_SpecMap_comp_fromSpecStalk_eq {x : X} {S : CommRingCat.{u}}
    {α β : X.presheaf.stalk x ⟶ S}
    (h : Spec.map α ≫ X.fromSpecStalk x = Spec.map β ≫ X.fromSpecStalk x) : α = β :=
  Spec.map_injective ((cancel_mono _).mp h)

/-- An element of a field lying in every valuation subring containing the range of a ring map
is integral over the source of that map. -/
lemma isIntegralElem_of_forall_valuationSubring {A K : Type u} [CommRing A] [Field K]
    (φ : A →+* K) {γ : K}
    (hγ : ∀ V : ValuationSubring K, Set.range φ ⊆ V → γ ∈ V) : φ.IsIntegralElem γ := by
  classical
  have hmem : γ ∈ (integralClosure (Subring.closure (Set.range φ)) K).toSubring := by
    rw [← iInf_valuationSubring_superset]
    exact Subring.mem_iInf.mpr fun V => hγ V.1 V.2
  have hcl : Subring.closure (Set.range φ) = φ.range := by
    rw [← RingHom.coe_range, Subring.closure_eq]
  obtain ⟨p, hpm, hp⟩ := (hmem : _root_.IsIntegral (Subring.closure (Set.range φ)) γ)
  let ψ : A →+* Subring.closure (Set.range φ) :=
    φ.codRestrict _ fun a => Subring.subset_closure ⟨a, rfl⟩
  have hψ : Function.Surjective ψ := by
    rintro ⟨z, hz⟩
    rw [hcl] at hz
    obtain ⟨a, rfl⟩ := hz
    exact ⟨a, rfl⟩
  have hlift : p ∈ Polynomial.lifts ψ := Polynomial.lifts_iff_coeff_lifts p |>.mpr
    fun n => hψ _
  obtain ⟨q, hq, -, hqm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hlift hpm
  refine ⟨q, hqm, ?_⟩
  have hcomp : φ = (Subring.closure (Set.range φ)).subtype.comp ψ := by ext; rfl
  rw [hcomp, ← Polynomial.eval₂_map, hq]
  exact hp

variable [UniversallyClosed f]

/-- **A residue function regular along the closure of a point of a scheme universally closed over
`Spec R` is integral over `R`.** If `γ ∈ κ(y)` is, for every specialization `x` of `y`, the image
of an element of `𝒪_{X, x}`, then `γ` is integral over `R`. -/
theorem isIntegralElem_residue_of_forall_specializes (y : X) (γ : X.residueField y)
    (hγ : ∀ (x : X) (h : y ⤳ x), ∃ t : X.presheaf.stalk x,
      X.residue y (X.presheaf.stalkSpecializes h t) = γ) :
    (residueAlgebraMap f y).hom.IsIntegralElem γ := by
  refine isIntegralElem_of_forall_valuationSubring _ fun V hV => ?_
  let K := X.residueField y
  have hVmem : ∀ a, (residueAlgebraMap f y).hom a ∈ V.toSubring := fun a => hV ⟨a, rfl⟩
  let φV : R ⟶ CommRingCat.of V :=
    CommRingCat.ofHom ((residueAlgebraMap f y).hom.codRestrict V.toSubring hVmem)
  have hφ : φV ≫ CommRingCat.ofHom (algebraMap V K) = residueAlgebraMap f y := by
    ext; rfl
  have w : X.fromSpecResidueField y ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap V K)) ≫ Spec.map φV := by
    rw [fromSpecResidueField_comp_eq_SpecMap_residueAlgebraMap, ← Spec.map_comp, hφ]
  have H : ValuativeCriterion.Existence f :=
    (UniversallyClosed.eq_valuativeCriterion ▸ (inferInstance : UniversallyClosed f) :
      (ValuativeCriterion.Existence ⊓ @QuasiCompact) f).1
  obtain ⟨l, hl₁, hl₂⟩ :=
    (H (ValuativeCommSq.mk (R := V) (K := K) (X.fromSpecResidueField y) (Spec.map φV)
      ⟨w⟩)).exists_lift
  dsimp only at hl₁ hl₂
  let x := l (closedPoint V)
  have hyx : y ⤳ x := by
    simp_rw [x, ← Scheme.fromSpecResidueField_apply y (closedPoint K), ← hl₁]
    exact (specializes_closedPoint _).map l.continuous
  obtain ⟨t, ht⟩ := hγ x hyx
  let ψ : X.presheaf.stalk x ⟶ CommRingCat.of V := Scheme.stalkClosedPointTo l
  have hl : Spec.map ψ ≫ X.fromSpecStalk x = l := Scheme.Spec_stalkClosedPointTo_fromSpecStalk l
  have heq : ψ ≫ CommRingCat.ofHom (algebraMap V K) =
      X.presheaf.stalkSpecializes hyx ≫ X.residue y := by
    apply eq_of_SpecMap_comp_fromSpecStalk_eq
    rw [Spec.map_comp, Category.assoc, hl, hl₁, Spec.map_comp, Category.assoc,
      Scheme.SpecMap_stalkSpecializes_fromSpecStalk]
    rfl
  have hval : algebraMap V K (ψ t) = γ := by
    rw [← ht]
    exact congrArg (fun g => g.hom t) heq
  rw [← hval]
  exact (ψ t).2

omit [UniversallyClosed f] in
/-- The map from the base ring to a residue field factors through every stalk at a specialization
of the point. -/
lemma residueAlgebraMap_apply {y x : X} (h : y ⤳ x) (a : R) :
    residueAlgebraMap f y a = X.residue y (X.presheaf.stalkSpecializes h
      ((StructureSheaf.toStalk R (f x) ≫ f.stalkMap x) a)) := by
  have h1 := Scheme.Hom.stalkSpecializes_stalkMap_apply f y x h
    (StructureSheaf.toStalk R (f x) a)
  have h2 : (Spec R).presheaf.stalkSpecializes (f.base.hom.map_specializes h)
      (StructureSheaf.toStalk R (f x) a) = StructureSheaf.toStalk R (f y) a :=
    StructureSheaf.toStalk_stalkSpecializes_apply (f.base.hom.map_specializes h) a
  rw [h2] at h1
  show X.residue y (f.stalkMap y (StructureSheaf.toStalk R (f y) a)) = _
  rw [h1]
  rfl

/-- The canonical map to the stalk at a prime sends the elements of the prime to nonunits. -/
lemma not_isUnit_toStalk (p : PrimeSpectrum R) (a : R) (ha : a ∈ p.asIdeal) :
    ¬ IsUnit (algebraMap R ((Spec.structureSheaf R).presheaf.stalk p) a) :=
  (IsLocalization.AtPrime.isUnit_to_map_iff _ p.asIdeal a).not.mpr (not_not.mpr ha)

/-- **A nonzero residue function regular along the closure of a point lying over the closed point
of a local base is a unit wherever it is regular.** Let `R` be local, `y` a point over the closed
point of `Spec R`, and `γ ∈ κ(y)` nonzero and regular along the closure of `y`. Then every
`t ∈ 𝒪_{X, x}`, for `y ⤳ x`, whose image in `κ(y)` is `γ`, is a unit.

The element `γ` is integral over `R`, whose image in `κ(y)` is the residue field of `R`; so `γ`
is algebraic over a field and its inverse is a polynomial in it, hence again the image of an
element of `𝒪_{X, x}`. If `t` were not a unit, `1 = γ γ⁻¹` would be the image of an element of
the maximal ideal of `𝒪_{X, x}`. -/
theorem isUnit_of_residue_eq [IsLocalRing R] (y : X) (hy : f y = closedPoint R)
    (γ : X.residueField y) (hγ0 : γ ≠ 0)
    (hγ : ∀ (x : X) (h : y ⤳ x), ∃ t : X.presheaf.stalk x,
      X.residue y (X.presheaf.stalkSpecializes h t) = γ)
    {x : X} (h : y ⤳ x) {t : X.presheaf.stalk x}
    (ht : X.residue y (X.presheaf.stalkSpecializes h t) = γ) : IsUnit t := by
  classical
  let ρ := (residueAlgebraMap f y).hom
  -- the image of `R` is a field
  have hker : ∀ a : R, a ∈ maximalIdeal R → ρ a = 0 := by
    intro a ha
    have h1 : StructureSheaf.toStalk R (f y) a ∈
        maximalIdeal ((Spec R).presheaf.stalk (f y)) :=
      not_isUnit_toStalk (f y) a (by rw [hy]; exact ha)
    have h2 : f.stalkMap y (StructureSheaf.toStalk R (f y) a) ∈ maximalIdeal _ :=
      map_nonunit (f.stalkMap y).hom _ h1
    exact (IsLocalRing.residue_eq_zero_iff _).mpr h2
  have hfield : IsField ρ.range := by
    refine ⟨⟨0, 1, fun h0 => ?_⟩, mul_comm, ?_⟩
    · exact zero_ne_one (congrArg Subtype.val h0)
    · rintro ⟨_, a, rfl⟩ ha
      have ha' : a ∉ maximalIdeal R := fun hm => ha (Subtype.ext (hker a hm))
      obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.mp ha'
      refine ⟨⟨ρ ↑u⁻¹, ↑u⁻¹, rfl⟩, Subtype.ext ?_⟩
      show ρ ↑u * ρ ↑u⁻¹ = 1
      rw [← map_mul, Units.mul_inv, map_one]
  let := hfield.toField
  -- the subring of `κ(y)` of images of `𝒪_{X, x}`, as an algebra over the image of `R`
  let φ : X.presheaf.stalk x →+* X.residueField y :=
    (X.presheaf.stalkSpecializes h ≫ X.residue y).hom
  let S : Subring (X.residueField y) := φ.range
  have hRS : ρ.range ≤ S := by
    rintro _ ⟨a, rfl⟩
    exact ⟨_, (residueAlgebraMap_apply f h a).symm⟩
  let SA : Subalgebra ρ.range (X.residueField y) :=
    { S with algebraMap_mem' := fun r => hRS r.2 }
  have hint : _root_.IsIntegral ρ.range γ := by
    obtain ⟨p, hpm, hp⟩ := isIntegralElem_residue_of_forall_specializes f y γ hγ
    refine ⟨p.map ρ.rangeRestrict, hpm.map _, ?_⟩
    rw [Polynomial.eval₂_map]
    exact hp
  have hγS : γ ∈ SA := ⟨t, ht⟩
  obtain ⟨t', ht'⟩ : γ⁻¹ ∈ SA := hint.inv_mem hγS
  by_contra hnu
  have htm : t ∈ maximalIdeal _ := hnu
  have hsub : 1 - t * t' ∉ maximalIdeal (X.presheaf.stalk x) := by
    intro hm
    have h1 := Ideal.add_mem _ hm (Ideal.mul_mem_right t' _ htm)
    rw [sub_add_cancel] at h1
    exact (maximalIdeal.isMaximal (X.presheaf.stalk x)).ne_top
      ((Ideal.eq_top_iff_one _).mpr h1)
  have hunit : IsUnit (1 - t * t') := IsLocalRing.notMem_maximalIdeal.mp hsub
  have himg : φ (1 - t * t') = 0 := by
    rw [map_sub, map_one, map_mul, show φ t = γ from ht, show φ t' = γ⁻¹ from ht',
      mul_inv_cancel₀ hγ0, sub_self]
  exact (hunit.map φ).ne_zero himg

end AlgebraicGeometry

end
