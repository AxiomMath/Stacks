module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ConormalAlgebra.Immersion
public import StacksFrontier.RingTheory.Filtration.AssociatedGraded

/-!
# Sections of the conormal algebra of an immersion

Let `i : Z ⟶ X` be an immersion of schemes and `𝒞_{Z/X,*}` its conormal algebra, the graded
quasi-coherent `𝒪_Z`-algebra of Stacks tag 0630.  On an affine open `Spec R = U ⊆ X` over which
`i` restricts to a closed immersion, with `I ⊆ R` the kernel of `R ⟶ Γ(Z, i⁻¹U)`, the
degree-`n` sections of the conormal algebra over `i⁻¹U` are canonically `Iⁿ/Iⁿ⁺¹`;
equivalently, they are the pullback `Iⁿ ⊗_R Γ(Z, i⁻¹U)`.  This file supplies both
identifications and their compatibility with multiplication, with the unit, with the scalar
action of `𝒪_X` and with restriction between charts.

## Main definitions

* `AlgebraicGeometry.AffineSectionsEquiv`: the first identification on a single chart, with the
  four laws it satisfies.
* `AlgebraicGeometry.ClosedOpenIdentifications`: both identifications, on every affine chart
  inside an open in which the image of `i` is closed.

## Main results

* `AlgebraicGeometry.affineSectionsEquiv`: the associated-graded description on one chart.
* `AlgebraicGeometry.conormalAlgebra_on_closed_open`: both descriptions on an open where the
  immersion is closed.

## Implementation notes

The associated-graded pieces are `AssociatedGraded.piece I n`, the quotient of
`AssociatedGraded.power I n = Iⁿ` by `Iⁿ⁺¹`;  the identification is the one induced by the
canonical local map `Stacks.Conormal.ConormalAlgebraData.localMap` of tag 0630, which is
surjective with kernel exactly `Iⁿ⁺¹`, so the equivalence is read off
`QuotientAddGroup.quotientKerEquivOfSurjective`.

The pullback description is obtained from the associated-graded one by the standard
identification `Iⁿ ⊗_R R/I ≅ Iⁿ/Iⁿ⁺¹`, transported along `R/I ≅ Γ(Z, i⁻¹U)`, which is an
isomorphism because `i` restricts to a closed immersion over the chart.

## References

* [Stacks Project, Tag 0633](https://stacks.math.columbia.edu/tag/0633)
* [Stacks Project, Tag 0630](https://stacks.math.columbia.edu/tag/0630)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry

/-- The canonical graded-algebra identification on an affine closed-immersion
chart, specified by its values on representatives. -/
structure AffineSectionsEquiv {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) where
  /-- The equivalence in each nonnegative degree. -/
  equiv (n : ℕ) :
    AssociatedGraded.piece (M := Γ(X, U)) (Stacks.Conormal.chartIdeal i U) n ≃+
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.obj
        (op (i ⁻¹ᵁ U.1))
  /-- The map is the quotient of the canonical local map of Tag 0630. -/
  map_mk (n : ℕ) (a : AssociatedGraded.power (M := Γ(X, U))
      (Stacks.Conormal.chartIdeal i U) n) :
    equiv n (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i U) n a) =
      (Stacks.Conormal.conormalAlgebra i).localMap U hU n
        ⟨(a : Γ(X, U)), by simpa using a.property⟩
  /-- Products of homogeneous classes correspond to products of sections. -/
  map_mul (n m : ℕ)
      (a : AssociatedGraded.piece (M := Γ(X, U)) (Stacks.Conormal.chartIdeal i U) n)
      (b : AssociatedGraded.piece (M := Γ(X, U)) (Stacks.Conormal.chartIdeal i U) m) :
    equiv (n + m) (AssociatedGraded.homogeneousSMul (Stacks.Conormal.chartIdeal i U) a b) =
      ((Stacks.Conormal.conormalAlgebra i).algebra.mul (n : ℤ) (m : ℤ)).app
        (op (i ⁻¹ᵁ U.1)) (equiv n a) (equiv m b)
  /-- The degree-zero unit is respected. -/
  map_one :
    equiv 0 (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i U) 0
      (⟨1, by simp [AssociatedGraded.power]⟩ :
        AssociatedGraded.power (M := Γ(X, U)) (Stacks.Conormal.chartIdeal i U) 0)) =
      (Stacks.Conormal.conormalAlgebra i).algebra.one.eval (op (i ⁻¹ᵁ U.1))
  /-- The equivalence is linear over the quotient map on chart sections. -/
  map_smul (n : ℕ) (r : Γ(X, U))
      (a : AssociatedGraded.piece (M := Γ(X, U)) (Stacks.Conormal.chartIdeal i U) n) :
    equiv n (r • a) =
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from (i.app U).hom r) • equiv n a

/-- The degree-`n` identification `Iⁿ/Iⁿ⁺¹ ≃ 𝒞_{Z/X,n}(i⁻¹U)` on an affine closed-immersion
chart, induced by the canonical local map of Tag 0630. -/
noncomputable def degreeEquiv {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) (n : ℕ) :
    AssociatedGraded.piece (M := Γ(X, U)) (Stacks.Conormal.chartIdeal i U) n ≃+
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.obj
        (op (i ⁻¹ᵁ U.1)) := by
  let R := Γ(X, U)
  let TObj := ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.obj
        (op (i ⁻¹ᵁ U.1))
  let T := TObj.carrier
  letI : AddCommGroup T := TObj.isAddCommGroup
  let f := (Stacks.Conormal.conormalAlgebra i).localMap U hU n
  let M := AssociatedGraded.power (M := R) (Stacks.Conormal.chartIdeal i U) n
  let ePow : M ≃ₗ[R] ↥(Stacks.Conormal.chartIdeal i U ^ n) := {
    toFun x := ⟨x.1, by simpa only [M, AssociatedGraded.ring_power_eq] using x.property⟩
    invFun x := ⟨x.1, by simpa only [M, AssociatedGraded.ring_power_eq] using x.property⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }
  let e : M →+ T := f.comp ePow.toAddEquiv.toAddMonoidHom
  let P : Submodule R M :=
    (AssociatedGraded.power (M := R) (Stacks.Conormal.chartIdeal i U) (n + 1)).comap
      (Submodule.subtype M)
  let K : Submodule R M := {
    carrier := {x | e x = 0}
    zero_mem' := by simp [e]
    add_mem' := by
      intro x y hx hy
      change e (x + y) = 0
      rw [map_add, hx, hy, add_zero]
    smul_mem' := by
      intro r x hx
      have hl := (Stacks.Conormal.conormalAlgebra i).localMap_smul U hU n r
        (ePow x) (r • ePow x) (by simp)
      have he : e (r • x) =
          (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from (i.app U).hom r) • e x := by
        change f (ePow (r • x)) = _
        rw [ePow.map_smul]
        exact hl
      change e (r • x) = 0
      rw [he, hx, smul_zero]
  }
  have hker : K = P := by
    ext x
    change e x = 0 ↔ x ∈ P
    change f (ePow x) = 0 ↔ _
    rw [(Stacks.Conormal.conormalAlgebra i).localMap_eq_zero_iff U hU n (ePow x)]
    change (x : R) ∈ _ ↔
      (x : R) ∈ AssociatedGraded.power (M := R) (Stacks.Conormal.chartIdeal i U) (n + 1)
    simp only [AssociatedGraded.ring_power_eq]
  have hsurj : Function.Surjective e := by
    intro y
    obtain ⟨a, ha⟩ := (Stacks.Conormal.conormalAlgebra i).localMap_surjective U hU n y
    refine ⟨ePow.symm a, ?_⟩
    change f (ePow (ePow.symm a)) = y
    rw [LinearEquiv.apply_symm_apply]
    exact ha
  let eqKer : (AssociatedGraded.piece (M := R) (Stacks.Conormal.chartIdeal i U) n) ≃ₗ[R]
      (M ⧸ K) := by
    have hid : Submodule.map (LinearEquiv.refl R M).toLinearMap P = K := by
      rw [← hker]
      change Submodule.map LinearMap.id K = K
      exact Submodule.map_id K
    exact Submodule.Quotient.equiv P K (LinearEquiv.refl R M) hid
  have hkerAdd : K.toAddSubgroup = e.ker := by
    ext x
    rfl
  have hmapK : AddSubgroup.map (AddEquiv.refl M) K.toAddSubgroup = e.ker := by
    simpa using hkerAdd
  have eqK : (M ⧸ K) ≃+ (M ⧸ e.ker) :=
    QuotientAddGroup.congr K.toAddSubgroup e.ker (AddEquiv.refl M) hmapK
  have eqG : (M ⧸ K) ≃+ T :=
    eqK.trans (QuotientAddGroup.quotientKerEquivOfSurjective e hsurj)
  exact eqKer.toAddEquiv.trans eqG

/-- `degreeEquiv` sends the class of a representative to its canonical local section. -/
theorem degreeEquiv_mk {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.affineOpens) (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl))
    (n : ℕ) (a : AssociatedGraded.power (M := Γ(X, U)) (Stacks.Conormal.chartIdeal i U) n) :
    degreeEquiv i U hU n (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i U) n a) =
      (Stacks.Conormal.conormalAlgebra i).localMap U hU n
        ⟨(a : Γ(X, U)), by simpa using a.property⟩ := by
  rfl

/-- The homogeneous sections of the conormal algebra on an affine closed-immersion chart are
canonically the quotients `I^n/I^(n+1)`, compatibly with multiplication, unit, and scalars. -/
@[stacks 0633 "conormal_algebra_affine_sections"]
noncomputable def affineSectionsEquiv {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.affineOpens)
    (hU : IsClosedImmersion (i.resLE U.1 (i ⁻¹ᵁ U.1) le_rfl)) :
    AffineSectionsEquiv i U hU := {
      equiv := degreeEquiv i U hU
      map_mk := by
        intro n a
        exact degreeEquiv_mk i U hU n a
      map_mul := by
        intro n m a b
        induction a using Submodule.Quotient.induction_on with
        | _ a =>
          induction b using Submodule.Quotient.induction_on with
          | _ b =>
            change degreeEquiv i U hU (n + m)
                (AssociatedGraded.homogeneousSMul (Stacks.Conormal.chartIdeal i U)
                  (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i U) n a)
                  (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i U) m b)) = _
            rw [AssociatedGraded.homogeneousSMul_mk, degreeEquiv_mk]
            change _ = ((Stacks.Conormal.conormalAlgebra i).algebra.mul (n : ℤ) (m : ℤ)).app
              (op (i ⁻¹ᵁ U.1))
              (degreeEquiv i U hU n (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i U) n a))
              (degreeEquiv i U hU m (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i U) m b))
            rw [degreeEquiv_mk, degreeEquiv_mk]
            let a' : ↥(Stacks.Conormal.chartIdeal i U ^ n) :=
              ⟨(a : Γ(X, U)), by simpa using a.property⟩
            let b' : ↥(Stacks.Conormal.chartIdeal i U ^ m) :=
              ⟨(b : Γ(X, U)), by simpa using b.property⟩
            let c' : ↥(Stacks.Conormal.chartIdeal i U ^ (n + m)) :=
              ⟨(a : Γ(X, U)) * (b : Γ(X, U)), by
                rw [pow_add]
                exact Ideal.mul_mem_mul (by simpa using a.property) (by simpa using b.property)⟩
            have hc : (c' : Γ(X, U)) = (a' : Γ(X, U)) * (b' : Γ(X, U)) := rfl
            exact (Stacks.Conormal.conormalAlgebra i).localMap_mul U hU n m a' b' c' hc
      map_one := by
        rw [degreeEquiv_mk]
        exact (Stacks.Conormal.conormalAlgebra i).localMap_one U hU ⟨1, by simp⟩ rfl
      map_smul := by
        intro n r a
        induction a using Submodule.Quotient.induction_on with
        | _ a =>
          change degreeEquiv i U hU n (r • Submodule.Quotient.mk a) = _
          rw [← Submodule.Quotient.mk_smul]
          change degreeEquiv i U hU n
              (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i U) n (r • a)) =
            (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ U.1)) from (i.app U).hom r) •
              degreeEquiv i U hU n (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i U) n a)
          rw [degreeEquiv_mk, degreeEquiv_mk]
          let a' : ↥(Stacks.Conormal.chartIdeal i U ^ n) :=
            ⟨(a : Γ(X, U)), by simpa using a.property⟩
          let b' : ↥(Stacks.Conormal.chartIdeal i U ^ n) :=
            ⟨r * (a : Γ(X, U)), by
              change r • (a : Γ(X, U)) ∈ Stacks.Conormal.chartIdeal i U ^ n
              exact (Stacks.Conormal.chartIdeal i U ^ n).smul_mem r (by simpa using a.property)⟩
          have hb : (b' : Γ(X, U)) = r * (a' : Γ(X, U)) := rfl
          simpa [a', b'] using
            (Stacks.Conormal.conormalAlgebra i).localMap_smul U hU n r a' b' hb
    }


/-- An immersion restricts to a closed immersion over every open contained in one in which its
image is closed. -/
lemma closedImmersion_resLE_of_range_closed {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] (U V : X.Opens) (hVU : V ≤ U)
    (hU : IsClosed (Set.range (i.resLE U (i ⁻¹ᵁ U) le_rfl))) :
    IsClosedImmersion (i.resLE V (i ⁻¹ᵁ V) le_rfl) := by
  let W : U.toScheme.Opens := U.ι ⁻¹ᵁ V
  have himage : U.ι ''ᵁ W = V := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hVU hx⟩, hx, rfl⟩
  have hclosed : IsClosedImmersion (i.resLE U (i ⁻¹ᵁ U) le_rfl) :=
    IsClosedImmersion.of_isPreimmersion _ hU
  have hclosed' : IsClosedImmersion (i ∣_ U) := by
    simpa only [Scheme.Hom.resLE_eq_morphismRestrict] using hclosed
  have hrestrict : IsClosedImmersion ((i ∣_ U) ∣_ W) :=
    IsZariskiLocalAtTarget.restrict hclosed' W
  rw [Scheme.Hom.resLE_eq_morphismRestrict]
  exact (MorphismProperty.arrow_mk_iso_iff (P := @IsClosedImmersion)
    (morphismRestrictRestrict i U W ≪≫ morphismRestrictEq i himage)).mp hrestrict

/-- The standard identification `Iⁿ ⊗_R R/I ≅ Iⁿ/Iⁿ⁺¹`. -/
noncomputable def tensorPowerQuotientEquiv {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) :
    TensorProduct (R := R) ↥(I ^ n) (R ⧸ I) ≃ₗ[R]
      AssociatedGraded.piece (M := R) I n := by
  let e : ↥(I ^ n) ≃ₗ[R] ↥(AssociatedGraded.power (M := R) I n) := {
    toFun x := ⟨x.1, by simpa only [AssociatedGraded.ring_power_eq] using x.2⟩
    invFun x := ⟨x.1, by simpa only [AssociatedGraded.ring_power_eq] using x.2⟩
    left_inv _ := rfl
    right_inv _ := rfl
    map_add' _ _ := rfl
    map_smul' _ _ := rfl
  }
  let P : Submodule R ↥(I ^ n) := I • ⊤
  let Q : Submodule R ↥(AssociatedGraded.power (M := R) I n) :=
    (AssociatedGraded.power (M := R) I (n + 1)).comap
      (Submodule.subtype (AssociatedGraded.power (M := R) I n))
  have hmap : Submodule.map e.toLinearMap P = Q := by
    ext y
    constructor
    · intro hy
      rcases (Submodule.mem_map).1 hy with ⟨x, hx, hxy⟩
      have hval : (x : R) = (y : R) := congrArg Subtype.val hxy
      rw [Submodule.mem_smul_top_iff] at hx
      dsimp [Q]
      change (y : R) ∈ AssociatedGraded.power (M := R) I (n + 1)
      rw [AssociatedGraded.ring_power_eq, ← hval]
      change (x : R) ∈ I ^ (n + 1)
      simpa [Ideal.smul_eq_mul, pow_succ, Ideal.mul_comm, Ideal.mul_assoc] using hx
    · intro hy
      apply Submodule.mem_map.mpr
      refine ⟨⟨y.1, by simpa only [AssociatedGraded.ring_power_eq] using y.2⟩, ?_, ?_⟩
      · rw [Submodule.mem_smul_top_iff]
        change (y : R) ∈ I • (I ^ n : Ideal R)
        dsimp [Q] at hy
        change (y : R) ∈ AssociatedGraded.power (M := R) I (n + 1) at hy
        rw [AssociatedGraded.ring_power_eq] at hy
        simpa [Ideal.smul_eq_mul, pow_succ, Ideal.mul_comm, Ideal.mul_assoc] using hy
      · ext
        rfl
  exact (TensorProduct.tensorQuotEquivQuotSMul (↥(I ^ n)) I).trans
    (Submodule.Quotient.equiv P Q e hmap)

/-- A surjective ring map presents its target as the quotient of its source by its kernel,
as a linear equivalence of `R`-modules. -/
noncomputable def quotientKerLinearEquiv {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    letI : Algebra R S := f.toAlgebra
    (R ⧸ RingHom.ker f) ≃ₗ[R] S := by
  letI : Algebra R S := f.toAlgebra
  let q : R ⧸ RingHom.ker f ≃+* S := RingHom.quotientKerEquivOfSurjective hf
  refine {
    toFun := q
    invFun := q.symm
    left_inv := q.left_inv
    right_inv := q.right_inv
    map_add' := q.map_add
    map_smul' := ?_
  }
  intro r x
  obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
  change q (algebraMap R (R ⧸ RingHom.ker f) r * Ideal.Quotient.mk (RingHom.ker f) a) = _
  rw [q.map_mul]
  rfl

/-- The inverse of `quotientKerLinearEquiv` sends an element to the class of any preimage. -/
theorem quotientKerLinearEquiv_symm_apply {R S : Type*} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (r : R) :
    (quotientKerLinearEquiv f hf).symm (f r) = Ideal.Quotient.mk (RingHom.ker f) r := by
  show (RingHom.quotientKerEquivOfSurjective hf).symm (f r) = _
  exact RingHom.quotientKerEquivOfSurjective_symm_apply hf r

/-- Tensoring with a fixed module on the left turns a linear equivalence into one. -/
noncomputable def tensorRightLinearEquiv {R M A B : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) :
    TensorProduct R M A ≃ₗ[R] TensorProduct R M B := by
  let e' := TensorProduct.congr (LinearEquiv.refl R M) e
  exact e'.toAddEquiv.toLinearEquiv (by
    intro r x
    simp [e'.map_smulₛₗ r x])

/-- Over an affine open on which an immersion restricts to a closed immersion, the map on
sections is surjective. -/
lemma app_surjective_of_closedRestriction {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] (V : X.affineOpens)
    (hclosed : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl)) :
    Function.Surjective ((i.app V).hom) := by
  let _ : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl) := hclosed
  let _ : IsAffine V.1.toScheme := V.2
  have hs : Function.Surjective ⇑(CommRingCat.Hom.hom
      ((i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl).appTop)) := by
    exact (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl).app_surjective ⊤
      (isAffineOpen_top V.1.toScheme)
  simpa only [Scheme.Hom.app_eq_appLE] using
    (RingHom.surjective_respectsIso.arrow_mk_iso_iff
      (arrowResLEAppIso i V.1 (i ⁻¹ᵁ V.1) le_rfl)).mp hs

/-- The pullback identification `Iⁿ ⊗_{Γ(X,U)} Γ(Z, i⁻¹U) ≃ 𝒞_{Z/X,n}(i⁻¹U)` on an affine
closed-immersion chart. -/
noncomputable def pullbackEquiv {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] (V : X.affineOpens)
    (hclosed : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl)) (n : ℕ) :
    letI : Algebra Γ(X, V) Γ(Z, i ⁻¹ᵁ V.1) := (i.app V).hom.toAlgebra
    TensorProduct Γ(X, V) ↥(Stacks.Conormal.chartIdeal i V ^ n)
      Γ(Z, i ⁻¹ᵁ V.1) ≃+
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.obj
        (op (i ⁻¹ᵁ V.1)) := by
  let R := Γ(X, V)
  let S := Γ(Z, i ⁻¹ᵁ V.1)
  let φ : R →+* S := (i.app V).hom
  letI : Algebra R S := φ.toAlgebra
  have hsurj : Function.Surjective φ := app_surjective_of_closedRestriction i V hclosed
  let e := quotientKerLinearEquiv φ hsurj
  let eTensor := tensorRightLinearEquiv (M := ↥(Stacks.Conormal.chartIdeal i V ^ n)) e.symm
  exact (eTensor.trans
      (tensorPowerQuotientEquiv (Stacks.Conormal.chartIdeal i V) n)).toAddEquiv.trans
    ((affineSectionsEquiv i V hclosed).equiv n)

/-- `tensorPowerQuotientEquiv` on a pure tensor. -/
theorem tensorPowerQuotientEquiv_tmul {R : Type*} [CommRing R]
    (I : Ideal R) (n : ℕ) (a : ↥(I ^ n)) (r : R) :
    tensorPowerQuotientEquiv I n (a ⊗ₜ[R] Ideal.Quotient.mk I r) =
      r • AssociatedGraded.mk I n
        ⟨a.1, by simpa only [AssociatedGraded.ring_power_eq] using a.2⟩ := by
  simp [tensorPowerQuotientEquiv, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply, TensorProduct.tensorQuotEquivQuotSMul_tmul_mk]
  congr 1

/-- `tensorRightLinearEquiv` on a pure tensor. -/
theorem tensorRightLinearEquiv_tmul {R M A B : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup A] [Module R A]
    [AddCommGroup B] [Module R B] (e : A ≃ₗ[R] B) (x : M) (a : A) :
    tensorRightLinearEquiv (M := M) e (x ⊗ₜ[R] a) = x ⊗ₜ[R] e a := by
  simp [tensorRightLinearEquiv]

/-- `pullbackEquiv` on a pure tensor: it is the scalar action of the section on the canonical
local section of the representative. -/
theorem pullbackEquiv_tmul {Z X : Scheme.{u}}
    (i : Z ⟶ X) [IsImmersion i] (V : X.affineOpens)
    (hclosed : IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl)) (n : ℕ)
    (a : ↥(Stacks.Conormal.chartIdeal i V ^ n)) (s : Γ(Z, i ⁻¹ᵁ V.1)) :
    letI : Algebra Γ(X, V) Γ(Z, i ⁻¹ᵁ V.1) := (i.app V).hom.toAlgebra
    pullbackEquiv i V hclosed n (a ⊗ₜ[Γ(X, V)] s) =
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from s) •
        (Stacks.Conormal.conormalAlgebra i).localMap V hclosed n a := by
  let R := Γ(X, V)
  let S := Γ(Z, i ⁻¹ᵁ V.1)
  let φ : R →+* S := (i.app V).hom
  let _ : Algebra R S := φ.toAlgebra
  have hsurj : Function.Surjective φ := app_surjective_of_closedRestriction i V hclosed
  obtain ⟨r, rfl⟩ := hsurj s
  show (affineSectionsEquiv i V hclosed).equiv n
      (tensorPowerQuotientEquiv (Stacks.Conormal.chartIdeal i V) n
        (tensorRightLinearEquiv (M := ↥(Stacks.Conormal.chartIdeal i V ^ n))
          (quotientKerLinearEquiv φ hsurj).symm (a ⊗ₜ[R] φ r))) = _
  rw [tensorRightLinearEquiv_tmul, quotientKerLinearEquiv_symm_apply,
    tensorPowerQuotientEquiv_tmul]
  rw [(affineSectionsEquiv i V hclosed).map_smul,
    (affineSectionsEquiv i V hclosed).map_mk]

/-- Both canonical identifications of the sections of the conormal algebra, on every affine
open contained in an open in which the image of the immersion is closed. -/
structure ClosedOpenIdentifications {Z X : Scheme.{u}} (i : Z ⟶ X)
    [IsImmersion i] (U : X.Opens) where
  /-- Over each such affine open the immersion restricts to a closed immersion. -/
  closed (V : X.affineOpens) (hVU : V.1 ≤ U) :
    IsClosedImmersion (i.resLE V.1 (i ⁻¹ᵁ V.1) le_rfl)
  /-- The associated-graded identification on each chart. -/
  quotient (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ) :
    AssociatedGraded.piece (M := Γ(X, V)) (Stacks.Conormal.chartIdeal i V) n ≃+
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.obj
        (op (i ⁻¹ᵁ V.1))
  /-- It sends the class of a representative to its canonical local section. -/
  quotient_mk (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ)
      (a : AssociatedGraded.power (M := Γ(X, V)) (Stacks.Conormal.chartIdeal i V) n) :
    quotient V hVU n (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i V) n a) =
      (Stacks.Conormal.conormalAlgebra i).localMap V (closed V hVU) n
        ⟨(a : Γ(X, V)), by simpa using a.property⟩
  /-- It is multiplicative. -/
  quotient_mul (V : X.affineOpens) (hVU : V.1 ≤ U) (n m : ℕ)
      (a : AssociatedGraded.piece (M := Γ(X, V)) (Stacks.Conormal.chartIdeal i V) n)
      (b : AssociatedGraded.piece (M := Γ(X, V)) (Stacks.Conormal.chartIdeal i V) m) :
    quotient V hVU (n + m)
        (AssociatedGraded.homogeneousSMul (Stacks.Conormal.chartIdeal i V) a b) =
      ((Stacks.Conormal.conormalAlgebra i).algebra.mul (n : ℤ) (m : ℤ)).app
        (op (i ⁻¹ᵁ V.1)) (quotient V hVU n a) (quotient V hVU m b)
  /-- It sends the class of `1` to the graded unit. -/
  quotient_one (V : X.affineOpens) (hVU : V.1 ≤ U) :
    quotient V hVU 0 (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i V) 0
      (⟨1, by simp [AssociatedGraded.power]⟩ :
        AssociatedGraded.power (M := Γ(X, V)) (Stacks.Conormal.chartIdeal i V) 0)) =
      (Stacks.Conormal.conormalAlgebra i).algebra.one.eval (op (i ⁻¹ᵁ V.1))
  /-- It is linear over the map on sections of the immersion. -/
  quotient_smul (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ)
      (r : Γ(X, V))
      (a : AssociatedGraded.piece (M := Γ(X, V)) (Stacks.Conormal.chartIdeal i V) n) :
    quotient V hVU n (r • a) =
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from (i.app V).hom r) •
        quotient V hVU n a
  /-- It commutes with restriction between charts. -/
  quotient_restrict (V W : X.affineOpens) (hVU : V.1 ≤ U) (hWU : W.1 ≤ U)
      (hWV : W.1 ≤ V.1) (n : ℕ)
      (a : AssociatedGraded.power (M := Γ(X, V)) (Stacks.Conormal.chartIdeal i V) n)
      (b : AssociatedGraded.power (M := Γ(X, W)) (Stacks.Conormal.chartIdeal i W) n)
      (hab : (b : Γ(X, W)) =
        X.presheaf.map (homOfLE hWV).op (a : Γ(X, V))) :
    ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.map
        (homOfLE (show i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1 from by
          intro x hx; exact hWV hx)).op
        (quotient V hVU n (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i V) n a)) =
      quotient W hWU n (AssociatedGraded.mk (Stacks.Conormal.chartIdeal i W) n b)
  /-- The pullback identification on each chart. -/
  pullback (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ) :
    letI : Algebra Γ(X, V) Γ(Z, i ⁻¹ᵁ V.1) := (i.app V).hom.toAlgebra;
    TensorProduct Γ(X, V) ↥(Stacks.Conormal.chartIdeal i V ^ n)
      Γ(Z, i ⁻¹ᵁ V.1) ≃+
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.obj
        (op (i ⁻¹ᵁ V.1))
  /-- Its value on a pure tensor. -/
  pullback_tmul (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ) :
    letI : Algebra Γ(X, V) Γ(Z, i ⁻¹ᵁ V.1) := (i.app V).hom.toAlgebra;
    ∀ (a : ↥(Stacks.Conormal.chartIdeal i V ^ n))
      (s : Γ(Z, i ⁻¹ᵁ V.1)),
      pullback V hVU n (a ⊗ₜ[Γ(X, V)] s) =
        (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from s) •
          (Stacks.Conormal.conormalAlgebra i).localMap V (closed V hVU) n a
  /-- It is multiplicative. -/
  pullback_mul (V : X.affineOpens) (hVU : V.1 ≤ U) (n m : ℕ) :
    letI : Algebra Γ(X, V) Γ(Z, i ⁻¹ᵁ V.1) := (i.app V).hom.toAlgebra;
    ∀ (a : ↥(Stacks.Conormal.chartIdeal i V ^ n))
      (b : ↥(Stacks.Conormal.chartIdeal i V ^ m))
      (c : ↥(Stacks.Conormal.chartIdeal i V ^ (n + m)))
      (_hc : (c : Γ(X, V)) = (a : Γ(X, V)) * (b : Γ(X, V)))
      (s t : Γ(Z, i ⁻¹ᵁ V.1)),
      pullback V hVU (n + m) (c ⊗ₜ[Γ(X, V)] (s * t)) =
        ((Stacks.Conormal.conormalAlgebra i).algebra.mul (n : ℤ) (m : ℤ)).app
          (op (i ⁻¹ᵁ V.1))
          (pullback V hVU n (a ⊗ₜ[Γ(X, V)] s))
          (pullback V hVU m (b ⊗ₜ[Γ(X, V)] t))
  /-- It sends `1 ⊗ 1` to the graded unit. -/
  pullback_one (V : X.affineOpens) (hVU : V.1 ≤ U) :
    letI : Algebra Γ(X, V) Γ(Z, i ⁻¹ᵁ V.1) := (i.app V).hom.toAlgebra;
    pullback V hVU 0
      ((⟨1, by simp⟩ : ↥(Stacks.Conormal.chartIdeal i V ^ 0)) ⊗ₜ[Γ(X, V)]
        (1 : Γ(Z, i ⁻¹ᵁ V.1))) =
      (Stacks.Conormal.conormalAlgebra i).algebra.one.eval (op (i ⁻¹ᵁ V.1))
  /-- It is linear over the sections of the source. -/
  pullback_smul (V : X.affineOpens) (hVU : V.1 ≤ U) (n : ℕ) :
    letI : Algebra Γ(X, V) Γ(Z, i ⁻¹ᵁ V.1) := (i.app V).hom.toAlgebra;
    ∀ (a : ↥(Stacks.Conormal.chartIdeal i V ^ n))
      (r s : Γ(Z, i ⁻¹ᵁ V.1)),
      pullback V hVU n (a ⊗ₜ[Γ(X, V)] (r * s)) =
        (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from r) •
          pullback V hVU n (a ⊗ₜ[Γ(X, V)] s)
  /-- It commutes with restriction between charts. -/
  pullback_restrict (V W : X.affineOpens) (hVU : V.1 ≤ U) (hWU : W.1 ≤ U)
      (hWV : W.1 ≤ V.1) (n : ℕ) :
    letI : Algebra Γ(X, V) Γ(Z, i ⁻¹ᵁ V.1) := (i.app V).hom.toAlgebra;
    letI : Algebra Γ(X, W) Γ(Z, i ⁻¹ᵁ W.1) := (i.app W).hom.toAlgebra;
    ∀ (a : ↥(Stacks.Conormal.chartIdeal i V ^ n))
      (b : ↥(Stacks.Conormal.chartIdeal i W ^ n))
      (_hab : (b : Γ(X, W)) = X.presheaf.map (homOfLE hWV).op (a : Γ(X, V)))
      (s : Γ(Z, i ⁻¹ᵁ V.1)) (t : Γ(Z, i ⁻¹ᵁ W.1))
      (_hst : t = Z.presheaf.map
        (homOfLE (show i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1 from by
          intro x hx; exact hWV hx)).op s),
      ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.map
          (homOfLE (show i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1 from by
            intro x hx; exact hWV hx)).op
          (pullback V hVU n (a ⊗ₜ[Γ(X, V)] s)) =
        pullback W hWU n (b ⊗ₜ[Γ(X, W)] t)

/-- Both canonical identifications of the conormal algebra on an open where the immersion is
closed. -/
@[stacks 0633 "conormal_algebra_on_closed_open"]
noncomputable def conormalAlgebra_on_closed_open
    {Z X : Scheme.{u}} (i : Z ⟶ X) [IsImmersion i]
    (U : X.Opens)
    (hU : IsClosed (Set.range (i.resLE U (i ⁻¹ᵁ U) le_rfl))) :
    ClosedOpenIdentifications i U := by
  let closedFn := fun (V : X.affineOpens) (hVU : V.1 ≤ U) =>
    closedImmersion_resLE_of_range_closed i U V.1 hVU hU
  let affineFn := fun (V : X.affineOpens) (hVU : V.1 ≤ U) =>
    affineSectionsEquiv i V
      (closedFn V hVU)
  refine {
    closed := closedFn
    quotient := fun V hVU n => (affineFn V hVU).equiv n
    quotient_mk := ?_
    quotient_mul := ?_
    quotient_one := ?_
    quotient_smul := ?_
    quotient_restrict := ?_
    pullback := fun V hVU n => pullbackEquiv i V (closedFn V hVU) n
    pullback_tmul := ?_
    pullback_mul := ?_
    pullback_one := ?_
    pullback_smul := ?_
    pullback_restrict := ?_
  }
  · intro V hVU n a
    exact (affineFn V hVU).map_mk n a
  · intro V hVU n m a b
    exact (affineFn V hVU).map_mul n m a b
  · intro V hVU
    exact (affineFn V hVU).map_one
  · intro V hVU n r a
    exact (affineFn V hVU).map_smul n r a
  · intro V W hVU hWU hWV n a b hab
    let a' : ↥(Stacks.Conormal.chartIdeal i V ^ n) :=
      ⟨a.1, by simpa only [AssociatedGraded.ring_power_eq] using a.2⟩
    let b' : ↥(Stacks.Conormal.chartIdeal i W ^ n) :=
      ⟨b.1, by simpa only [AssociatedGraded.ring_power_eq] using b.2⟩
    have hab' : (b' : Γ(X, W)) =
        X.presheaf.map (homOfLE hWV).op (a' : Γ(X, V)) := by
      simpa only [a', b'] using hab
    rw [(affineFn V hVU).map_mk, (affineFn W hWU).map_mk]
    exact (Stacks.Conormal.conormalAlgebra i).localMap_naturality V W hWV
      (by intro x hx; exact hWV hx) (closedFn V hVU) (closedFn W hWU) n a' b' hab'
  · intro V hVU n a s
    exact pullbackEquiv_tmul i V (closedFn V hVU) n a s
  · intro V hVU n m a b c hc s t
    rw [pullbackEquiv_tmul, pullbackEquiv_tmul, pullbackEquiv_tmul]
    rw [(Stacks.Conormal.conormalAlgebra i).localMap_mul V (closedFn V hVU)
      n m a b c hc]
    rw [(Stacks.Conormal.conormalAlgebra i).algebra.mul n m |>.map_smul_left,
      (Stacks.Conormal.conormalAlgebra i).algebra.mul n m |>.map_smul_right]
    change (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from s * t) • _ =
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from s) •
        ((show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from t) • _)
    exact (smul_smul (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from s)
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from t) _).symm
  · intro V hVU
    rw [pullbackEquiv_tmul]
    change (1 : Z.ringCatSheaf.obj.obj
      (op (i ⁻¹ᵁ V.1))) • _ = _
    simpa only [one_smul] using
      (Stacks.Conormal.conormalAlgebra i).localMap_one V (closedFn V hVU)
        ⟨1, by simp⟩ (by simp)
  · intro V hVU n r s a
    rw [pullbackEquiv_tmul, pullbackEquiv_tmul]
    exact (smul_smul (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from s)
      (show Z.ringCatSheaf.obj.obj (op (i ⁻¹ᵁ V.1)) from a) _).symm
  · intro V W hVU hWU hWV n a b hab s t hst
    rw [pullbackEquiv_tmul, pullbackEquiv_tmul]
    let r : Z.ringCatSheaf.obj.obj
        (op (i ⁻¹ᵁ V.1)) := s
    change ((Stacks.Conormal.conormalAlgebra i).algebra.piece (n : ℤ)).val.map
        (homOfLE (show i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1 from by
          intro x hx; exact hWV hx)).op
        (r • (Stacks.Conormal.conormalAlgebra i).localMap V (closedFn V hVU) n a) = _
    rw [PresheafOfModules.map_smul]
    have hr : (Z.ringCatSheaf.obj).map
        (homOfLE (show i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1 from by
          intro x hx; exact hWV hx)).op r =
        (show Z.ringCatSheaf.obj.obj
          (op (i ⁻¹ᵁ W.1)) from t) := by
      change Z.presheaf.map
        (homOfLE (show i ⁻¹ᵁ W.1 ≤ i ⁻¹ᵁ V.1 from by
          intro x hx; exact hWV hx)).op s = t
      exact hst.symm
    rw [hr]
    rw [(Stacks.Conormal.conormalAlgebra i).localMap_naturality V W hWV
      (by intro x hx; exact hWV hx) (closedFn V hVU) (closedFn W hWU)
      n a b hab, hst]
    rfl


end AlgebraicGeometry

end
