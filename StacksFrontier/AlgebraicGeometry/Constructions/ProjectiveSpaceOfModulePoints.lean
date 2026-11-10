module

public import Mathlib.LinearAlgebra.Dimension.FreeAndStrongRankCondition
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Variety.Projective.RationalPointHyperplane

/-!
# The `k`-valued points of the projective space of a vector space

Let `k` be a field and `V` a `k`-vector space. A `k`-valued point of `P(V) = Proj (Sym_k V)` is a
section of its structure morphism to `Spec k`. Such a section is the same thing as a point of
`P(V)` whose residue field is `k`, and the degree-one forms vanishing at that point are the
kernel of a surjection of `V` onto a one-dimensional space. This file assembles that dictionary
and concludes that the `k`-valued points of `P(V)` are exactly the one-dimensional quotients
of `V`.

## Main definitions

* `AlgebraicGeometry.sectionEquivIsRationalPoint`: the sections of a scheme over `Spec k` are its
  `k`-rational points.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.oneDimQuotientEquivProjectivizationDual`: the
  one-dimensional quotients of `V`, recorded by their kernels, are the classes in the
  projectivization of the dual of `V`.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.awayEval` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.pointOfDual`: the `k`-valued point of `P(V)` that a
  functional taking the value one somewhere determines, read on an affine chart.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.kValuedPointEquivOneDimQuotient`: the `k`-valued
  points of `P(V)` as the one-dimensional quotients of `V`.

## Main results

* `AlgebraicGeometry.ProjectiveSpaceOfModule.finrank_quotient_ker_eq_one` and
  `AlgebraicGeometry.ProjectiveSpaceOfModule.finrank_quotient_eq_one_iff`: a subspace of `V` is
  the kernel of a surjection onto a one-dimensional space exactly when the quotient by it is
  one-dimensional. Neither needs `V` finite-dimensional or `k` algebraically closed.
* `AlgebraicGeometry.ProjectiveSpaceOfModule.isRationalPoint_linearFunctionalPoint`: the point of
  `P(V)` cut out by a nonzero functional on `V` has residue field `k`.

## Implementation notes

A section `p` of the structure morphism is recovered from its image point `x` because the
canonical map `k -> κ(x)` and the map `κ(x) -> k` that `p` induces are mutually inverse: the
second is a homomorphism of fields, hence injective, and the composite in one order is the
identity by the section identity, so the composite in the other order is too.

The `k`-valued point attached to a functional `φ` with `φ v₀ = 1` is built on the chart
`D₊(ι v₀)`, which is the spectrum of the degree-zero homogeneous localization
`A = (Sym_k V)_{(ι v₀)}`. The functional lifts to a `k`-algebra map `Sym_k V -> k`, which sends
`ι v₀` to a unit and so descends to `A -> k` sending `ι v / ι v₀` to `φ v`. That the resulting
morphism is a morphism over `Spec k` is the statement that the descended map is the identity on
the degree-zero scalars, and its image point is read off through
`AlgebraicGeometry.Proj.awayι_preimage_basicOpen`: the degree-one forms vanishing there are
exactly the kernel of `φ`.

Nothing here needs `V` finite-dimensional or `k` algebraically closed. The version for *closed*
points over an algebraically closed field, with `V` finite-dimensional, is
`AlgebraicGeometry.ProjectiveSpaceOfModule.closedPointsEquivDual`; over a field that is not
algebraically closed a closed point of `P(V)` need not be `k`-valued, so that statement is not
the one below and does not imply it.

## References

* [Stacks Project, Tag 0FCY](https://stacks.math.columbia.edu/tag/0FCY)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace AlgebraicGeometry

universe u

/-! ### Sections over the base field are the rational points -/

section RationalPoint

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-- The map on residue fields that a section of a scheme over `Spec k` induces at its image
point, together with the two identities making it inverse to the canonical map from `k`. -/
private theorem exists_residueField_inverse_of_section {p : Spec (.of k) ⟶ X}
    (hp : p ≫ f = 𝟙 _) (a : Spec (.of k)) :
    ∃ g : X.residueField (p.base a) ⟶ .of k,
      Spec.preimage (X.fromSpecResidueField (p.base a) ≫ f) ≫ g = 𝟙 (CommRingCat.of k) ∧
        g ≫ Spec.preimage (X.fromSpecResidueField (p.base a) ≫ f) =
          𝟙 (X.residueField (p.base a)) ∧
          Spec.map g ≫ X.fromSpecResidueField (p.base a) = p := by
  obtain rfl : a = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  set g := X.descResidueField (Scheme.stalkClosedPointTo p) with hg
  have h3 : Spec.map g ≫ X.fromSpecResidueField (p.base (IsLocalRing.closedPoint k)) = p :=
    Scheme.descResidueField_stalkClosedPointTo_fromSpecResidueField k X p
  have h1 : Spec.preimage (X.fromSpecResidueField
      (p.base (IsLocalRing.closedPoint k)) ≫ f) ≫ g = 𝟙 (CommRingCat.of k) := by
    apply Spec.map_injective
    rw [Spec.map_comp, Spec.map_preimage, Spec.map_id, ← Category.assoc, h3, hp]
  have hmono : Mono g := ConcreteCategory.mono_of_injective _ (RingHom.injective _)
  refine ⟨g, h1, ?_, h3⟩
  rw [← cancel_mono g, Category.assoc, Category.id_comp, h1, Category.comp_id]

/-- The image of a section of a scheme over `Spec k` is a `k`-rational point. -/
theorem isRationalPoint_base_of_comp_eq_id {p : Spec (.of k) ⟶ X} (hp : p ≫ f = 𝟙 _)
    (a : Spec (.of k)) : IsRationalPoint f (p.base a) := by
  obtain ⟨g, h1, h2, -⟩ := exists_residueField_inverse_of_section f hp a
  exact ⟨g, h1, h2⟩

/-- A section of a scheme over `Spec k` is the `k`-point attached to its image: a section is
determined by the point it hits. -/
theorem ptOfIsRationalPoint_base_of_comp_eq_id {p : Spec (.of k) ⟶ X} (hp : p ≫ f = 𝟙 _)
    (a : Spec (.of k)) :
    ptOfIsRationalPoint f (p.base a) (isRationalPoint_base_of_comp_eq_id f hp a) = p := by
  obtain ⟨g, h1, -, h3⟩ := exists_residueField_inverse_of_section f hp a
  have hiso : IsIso (Spec.preimage (X.fromSpecResidueField (p.base a) ≫ f)) :=
    isRationalPoint_base_of_comp_eq_id f hp a
  rw [ptOfIsRationalPoint, residueFieldIsoOfIsRationalPoint,
    show (asIso (Spec.preimage (X.fromSpecResidueField (p.base a) ≫ f))).symm.hom = g from
      IsIso.inv_eq_of_hom_inv_id h1]
  exact h3

/-- **The sections of a scheme over `Spec k` are its `k`-rational points.** A morphism
`Spec k ⟶ X` splitting the structure morphism is the same thing as a point of `X` whose residue
field is `k`. -/
@[ega "I 3.4.5", ega "II 7.3.2" "more general"]
def sectionEquivIsRationalPoint :
    { p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 (Spec (.of k)) } ≃ { x : X // IsRationalPoint f x } where
  toFun p := ⟨p.1.base default, isRationalPoint_base_of_comp_eq_id f p.2 default⟩
  invFun x := ⟨ptOfIsRationalPoint f x.1 x.2, ptOfIsRationalPoint_comp f x.1 x.2⟩
  left_inv p := Subtype.ext (ptOfIsRationalPoint_base_of_comp_eq_id f p.2 default)
  right_inv x := Subtype.ext (ptOfIsRationalPoint_apply f x.1 x.2 default)

/-- The rational point attached to a section of a scheme over `Spec k` is the image of the
closed point of `Spec k`. -/
@[simp]
lemma sectionEquivIsRationalPoint_apply_coe (p : { p : Spec (.of k) ⟶ X // p ≫ f = 𝟙 _ }) :
    (sectionEquivIsRationalPoint f p).val = p.val.base default := rfl

end RationalPoint

namespace ProjectiveSpaceOfModule

open HomogeneousLocalization

/-! ### One-dimensional quotients of a vector space -/

section LinearAlgebra

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- A functional taking a nonzero value somewhere takes the value one somewhere. -/
private theorem exists_apply_eq_one {φ : Module.Dual k V} (hφ : φ ≠ 0) : ∃ v : V, φ v = 1 := by
  obtain ⟨v, hv⟩ : ∃ v, φ v ≠ 0 := by
    contrapose! hφ
    ext v
    exact hφ v
  exact ⟨(φ v)⁻¹ • v, by rw [map_smul, smul_eq_mul, inv_mul_cancel₀ hv]⟩

/-- **The quotient by the kernel of a surjection onto a line is one-dimensional.** -/
theorem finrank_quotient_ker_eq_one_of_surjective {L : Type*} [AddCommGroup L] [Module k L]
    {g : V →ₗ[k] L} (hg : Function.Surjective g) (hL : Module.finrank k L = 1) :
    Module.finrank k (V ⧸ LinearMap.ker g) = 1 := by
  rw [(LinearMap.quotKerEquivOfSurjective g hg).finrank_eq, hL]

/-- **The quotient by the kernel of a nonzero functional is one-dimensional.** No
finite-dimensionality and no algebraic closedness is needed. -/
theorem finrank_quotient_ker_eq_one {φ : Module.Dual k V} (hφ : φ ≠ 0) :
    Module.finrank k (V ⧸ LinearMap.ker φ) = 1 :=
  finrank_quotient_ker_eq_one_of_surjective k V (surjective_of_dual_ne_zero k V hφ)
    (Module.finrank_self k)

/-- **A one-dimensional quotient is the quotient by the kernel of a surjective functional.** This
is the converse of `finrank_quotient_ker_eq_one`; it too needs no finite-dimensionality and no
algebraic closedness. -/
theorem exists_surjective_ker_eq_of_finrank_quotient_eq_one (K : Submodule k V)
    (hK : Module.finrank k (V ⧸ K) = 1) :
    ∃ φ : Module.Dual k V, Function.Surjective φ ∧ LinearMap.ker φ = K := by
  obtain ⟨w, hw, hspan⟩ := finrank_eq_one_iff'.mp hK
  have hinj : Function.Injective (LinearMap.toSpanSingleton k (V ⧸ K) w) := by
    intro a b hab
    simp only [LinearMap.toSpanSingleton_apply] at hab
    have h0 : (a - b) • w = 0 := by rw [sub_smul, hab, sub_self]
    rcases smul_eq_zero.mp h0 with h' | h'
    · exact sub_eq_zero.mp h'
    · exact absurd h' hw
  have hsurj : Function.Surjective (LinearMap.toSpanSingleton k (V ⧸ K) w) := fun y =>
    (hspan y).imp fun _ hc => hc
  let e : k ≃ₗ[k] (V ⧸ K) := LinearEquiv.ofBijective _ ⟨hinj, hsurj⟩
  refine ⟨e.symm.toLinearMap ∘ₗ K.mkQ, fun c => ?_, ?_⟩
  · obtain ⟨v, hv⟩ := K.mkQ_surjective (e c)
    exact ⟨v, by simp only [LinearMap.comp_apply, hv, LinearEquiv.coe_coe, e.symm_apply_apply]⟩
  · rw [LinearMap.ker_comp, LinearEquiv.ker, Submodule.comap_bot, Submodule.ker_mkQ]

/-- **A subspace of `V` has one-dimensional quotient exactly when it is the kernel of a
surjection of `V` onto a line.** -/
theorem finrank_quotient_eq_one_iff (K : Submodule k V) :
    Module.finrank k (V ⧸ K) = 1 ↔
      ∃ φ : Module.Dual k V, Function.Surjective φ ∧ LinearMap.ker φ = K := by
  refine ⟨exists_surjective_ker_eq_of_finrank_quotient_eq_one k V K, ?_⟩
  rintro ⟨φ, hφ, rfl⟩
  exact finrank_quotient_ker_eq_one_of_surjective k V hφ (Module.finrank_self k)

/-- The kernel of a class in the projectivization of the dual of `V`, as a subspace with
one-dimensional quotient. -/
@[sga "7 XVII 2.1" "partial"]
def kerOfProjectivizationDual :
    Projectivization k (Module.Dual k V) →
      { K : Submodule k V // Module.finrank k (V ⧸ K) = 1 } :=
  Quotient.lift
    (fun φ => ⟨LinearMap.ker φ.val, finrank_quotient_ker_eq_one k V φ.property⟩)
    (by
      rintro ⟨φ, hφ⟩ ⟨χ, hχ⟩ ⟨c, hc⟩
      apply Subtype.ext
      change c • χ = φ at hc
      subst φ
      ext v
      simp [LinearMap.mem_ker, Units.smul_def, c.ne_zero])

/-- On a representative, the subspace attached to a class is the kernel of that representative. -/
theorem kerOfProjectivizationDual_mk (φ : Module.Dual k V) (hφ : φ ≠ 0) :
    (kerOfProjectivizationDual k V (Projectivization.mk k φ hφ)).val = LinearMap.ker φ := rfl

/-- Distinct classes in the projectivized dual have distinct kernels. -/
@[sga "7 XVII 2.1" "partial"]
theorem kerOfProjectivizationDual_injective :
    Function.Injective (kerOfProjectivizationDual k V) := by
  intro p q hpq
  induction p using Projectivization.ind with | h φ hφ =>
  induction q using Projectivization.ind with | h χ hχ =>
  have h : ∀ v, φ v = 0 ↔ χ v = 0 := by
    intro v
    have hker := congrArg Subtype.val hpq
    rw [kerOfProjectivizationDual_mk, kerOfProjectivizationDual_mk] at hker
    rw [← LinearMap.mem_ker, ← LinearMap.mem_ker, hker]
  obtain ⟨c, hc⟩ := Module.Dual.exists_units_smul_eq_of_forall_eq_zero_iff hχ h
  exact (Projectivization.mk_eq_mk_iff k φ χ hφ hχ).2 ⟨c, hc.symm⟩

/-- Every subspace with one-dimensional quotient is the kernel of a class in the projectivized
dual. -/
@[sga "7 XVII 2.1" "partial"]
theorem kerOfProjectivizationDual_surjective :
    Function.Surjective (kerOfProjectivizationDual k V) := by
  rintro ⟨K, hK⟩
  obtain ⟨φ, hφ, hker⟩ := exists_surjective_ker_eq_of_finrank_quotient_eq_one k V K hK
  have hφ0 : φ ≠ 0 := LinearMap.ne_zero_of_surjective hφ
  exact ⟨Projectivization.mk k φ hφ0,
    Subtype.ext ((kerOfProjectivizationDual_mk k V φ hφ0).trans hker)⟩

/-- **The one-dimensional quotients of `V` are the classes in the projectivization of its
dual.** A quotient is recorded by its kernel, and a class by any functional representing it. -/
@[sga "7 XVII 2.1" "partial"]
def oneDimQuotientEquivProjectivizationDual :
    { K : Submodule k V // Module.finrank k (V ⧸ K) = 1 } ≃
      Projectivization k (Module.Dual k V) :=
  (Equiv.ofBijective _
    ⟨kerOfProjectivizationDual_injective k V, kerOfProjectivizationDual_surjective k V⟩).symm

end LinearAlgebra

/-! ### The `k`-valued point cut out by a functional -/

section PointOfDual

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- The degree-zero fraction attached to a vector, read in the localization. -/
private theorem awayFraction_val {v₀ : V}
    (hv₀ : SymmetricAlgebra.ι k V v₀ ∈ SymPow.symmetricPower 1 k V) (v : V) :
    (awayFraction k hv₀ v).val = Localization.mk (SymmetricAlgebra.ι k V v)
      (⟨SymmetricAlgebra.ι k V v₀ ^ 1, 1, rfl⟩ :
        ↥(Submonoid.powers (SymmetricAlgebra.ι k V v₀))) := rfl

/-- The algebra map `Sym_k V → k` extending a functional taking the value one at `v₀` sends
`ι v₀` to a unit, so it inverts it. -/
theorem isUnit_lift_ι {v₀ : V} (φ : Module.Dual k V) (hφv₀ : φ v₀ = 1) :
    IsUnit ((SymmetricAlgebra.lift φ).toRingHom (SymmetricAlgebra.ι k V v₀)) :=
  isUnit_iff_exists_inv.mpr ⟨1, by simp [SymmetricAlgebra.lift_ι_apply, hφv₀]⟩

/-- Evaluation at a functional `φ` with `φ v₀ = 1`: the `k`-algebra map from the degree-zero
homogeneous localization of `Sym_k V` away from `ι v₀` to `k` that sends the fraction
`ι v / ι v₀` to `φ v`.

It exists because the algebra map `Sym_k V → k` extending `φ` sends `ι v₀` to the unit `1`, so
it inverts `ι v₀` and descends to the localization, whose degree-zero part this is. -/
def awayEval {v₀ : V} (φ : Module.Dual k V) (hφv₀ : φ v₀ = 1) :
    Away (fun n => SymPow.symmetricPower n k V) (SymmetricAlgebra.ι k V v₀) →+* k :=
  (Localization.awayLift (SymmetricAlgebra.lift φ).toRingHom (SymmetricAlgebra.ι k V v₀)
      (isUnit_lift_ι k V φ hφv₀)).comp
    (algebraMap (Away (fun n => SymPow.symmetricPower n k V) (SymmetricAlgebra.ι k V v₀))
      (Localization (Submonoid.powers (SymmetricAlgebra.ι k V v₀))))

/-- Evaluation sends the fraction `ι v / ι v₀` to `φ v`. -/
theorem awayEval_awayFraction {v₀ : V} (φ : Module.Dual k V) (hφv₀ : φ v₀ = 1)
    (hdeg : SymmetricAlgebra.ι k V v₀ ∈ SymPow.symmetricPower 1 k V) (v : V) :
    awayEval k V φ hφv₀ (awayFraction k hdeg v) = φ v := by
  rw [awayEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply, awayFraction_val,
    Localization.awayLift_mk (f := (SymmetricAlgebra.lift φ).toRingHom)
      (r := SymmetricAlgebra.ι k V v₀) (a := SymmetricAlgebra.ι k V v) (v := 1)
      (hv := by simp [SymmetricAlgebra.lift_ι_apply, hφv₀]) (j := 1)]
  simp [SymmetricAlgebra.lift_ι_apply]

/-- Evaluation is the identity on the degree-zero scalars: the `k`-valued point it defines is a
point over `Spec k`. -/
theorem awayEval_fromZeroRingHom {v₀ : V} (φ : Module.Dual k V) (hφv₀ : φ v₀ = 1) (c : k) :
    awayEval k V φ hφv₀ (fromZeroRingHom (fun n => SymPow.symmetricPower n k V)
      (Submonoid.powers (SymmetricAlgebra.ι k V v₀))
      (algebraMap k (SymPow.symmetricPower 0 k V) c)) = c := by
  rw [awayEval, RingHom.comp_apply, HomogeneousLocalization.algebraMap_apply,
    show (fromZeroRingHom (fun n => SymPow.symmetricPower n k V)
      (Submonoid.powers (SymmetricAlgebra.ι k V v₀))
      (algebraMap k (SymPow.symmetricPower 0 k V) c)).val =
      Localization.mk (algebraMap k (SymmetricAlgebra k V) c)
        (1 : ↥(Submonoid.powers (SymmetricAlgebra.ι k V v₀))) from rfl,
    Localization.mk_one_eq_algebraMap, IsLocalization.Away.lift_eq]
  simp

/-- The `k`-valued point of `P(V)` that a functional `φ` with `φ v₀ = 1` determines: the point of
the chart `D₊(ι v₀)` at which evaluation along `φ` vanishes. -/
def pointOfDual {v₀ : V} (φ : Module.Dual k V) (hφv₀ : φ v₀ = 1) :
    Spec (.of k) ⟶ projectiveSpaceOfModule k V :=
  Spec.map (CommRingCat.ofHom (awayEval k V φ hφv₀)) ≫
    Proj.awayι (fun n => SymPow.symmetricPower n k V) (SymmetricAlgebra.ι k V v₀)
      (ι_mem_symmetricPower_one k V v₀) Nat.one_pos

/-- The point attached to a functional is a point over `Spec k`. -/
@[simp]
theorem pointOfDual_comp {v₀ : V} (φ : Module.Dual k V) (hφv₀ : φ v₀ = 1) :
    pointOfDual k V φ hφv₀ ≫ projectiveSpaceOfModuleToSpec k V = 𝟙 _ := by
  rw [pointOfDual, projectiveSpaceOfModuleToSpec, Category.assoc, Proj.awayι_toSpecZero_assoc,
    ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_id]
  exact congrArg Spec.map
    (CommRingCat.hom_ext (RingHom.ext (awayEval_fromZeroRingHom k V φ hφv₀)))

/-- The degree-one forms vanishing at the point attached to `φ` are exactly the vectors `φ`
kills. -/
theorem ι_mem_pointOfDual_iff {v₀ : V} (φ : Module.Dual k V) (hφv₀ : φ v₀ = 1)
    (a : Spec (.of k)) (v : V) :
    SymmetricAlgebra.ι k V v ∈ ((pointOfDual k V φ hφv₀).base a).asHomogeneousIdeal ↔
      φ v = 0 := by
  have hdeg : SymmetricAlgebra.ι k V v₀ ∈ SymPow.symmetricPower 1 k V :=
    ι_mem_symmetricPower_one k V v₀
  have hdv : SymmetricAlgebra.ι k V v ∈ SymPow.symmetricPower 1 k V :=
    ι_mem_symmetricPower_one k V v
  have hiso : Away.isLocalizationElem (𝒜 := fun n => SymPow.symmetricPower n k V)
      (d := 1) (e := 1) hdeg hdv = awayFraction k hdeg v := by
    apply val_injective
    rw [awayFraction_val]
    change Localization.mk _ _ = Localization.mk _ _
    simp only [pow_one]
  have hpre : Proj.awayι (fun n => SymPow.symmetricPower n k V) (SymmetricAlgebra.ι k V v₀)
        hdeg Nat.one_pos ⁻¹ᵁ
        Proj.basicOpen (fun n => SymPow.symmetricPower n k V) (SymmetricAlgebra.ι k V v) =
      PrimeSpectrum.basicOpen (awayFraction k hdeg v) := by
    rw [← hiso]
    exact Proj.awayι_preimage_basicOpen (𝒜 := fun n => SymPow.symmetricPower n k V)
      (f := SymmetricAlgebra.ι k V v₀) (g := SymmetricAlgebra.ι k V v)
      (f_deg := hdeg) (hm := Nat.one_pos) (g_deg := hdv) (hm' := Nat.one_pos)
  have hcomp : (pointOfDual k V φ hφv₀).base a =
      (Proj.awayι (fun n => SymPow.symmetricPower n k V) (SymmetricAlgebra.ι k V v₀) hdeg
        Nat.one_pos).base
        ((Spec.map (CommRingCat.ofHom (awayEval k V φ hφv₀))).base a) := rfl
  have hprime : awayFraction k hdeg v ∈ ((Spec.map (CommRingCat.ofHom
      (awayEval k V φ hφv₀))).base a).asIdeal ↔ φ v = 0 := by
    change awayFraction k hdeg v ∈
      Ideal.comap (CommRingCat.ofHom (awayEval k V φ hφv₀)).hom a.asIdeal ↔ _
    rw [Ideal.mem_comap, show (CommRingCat.ofHom (awayEval k V φ hφv₀)).hom
      (awayFraction k hdeg v) = φ v from awayEval_awayFraction k V φ hφv₀ hdeg v,
      (Ideal.eq_bot_or_top a.asIdeal).resolve_right a.isPrime.ne_top, Ideal.mem_bot]
  have hnot : SymmetricAlgebra.ι k V v ∉
      ((pointOfDual k V φ hφv₀).base a).asHomogeneousIdeal ↔ φ v ≠ 0 := by
    rw [← Proj.mem_basicOpen, hcomp]
    change (Spec.map (CommRingCat.ofHom (awayEval k V φ hφv₀))).base a ∈
      Proj.awayι (fun n => SymPow.symmetricPower n k V) (SymmetricAlgebra.ι k V v₀) hdeg
        Nat.one_pos ⁻¹ᵁ
        Proj.basicOpen (fun n => SymPow.symmetricPower n k V) (SymmetricAlgebra.ι k V v) ↔ _
    rw [hpre]
    exact (PrimeSpectrum.mem_basicOpen _ _).trans (not_congr hprime)
  exact not_iff_not.mp hnot

/-- The degree-one forms vanishing at the point attached to `φ` are the kernel of `φ`. -/
theorem pointSubmodule_pointOfDual {v₀ : V} (φ : Module.Dual k V) (hφv₀ : φ v₀ = 1)
    (a : Spec (.of k)) :
    pointSubmodule k V ((pointOfDual k V φ hφv₀).base a) = LinearMap.ker φ := by
  ext v
  rw [mem_pointSubmodule_iff, LinearMap.mem_ker]
  exact ι_mem_pointOfDual_iff k V φ hφv₀ a v

/-- The point attached to `φ` is the point `φ` cuts out. -/
theorem pointOfDual_base {v₀ : V} (φ : Module.Dual k V) (hφ : φ ≠ 0) (hφv₀ : φ v₀ = 1)
    (a : Spec (.of k)) :
    (pointOfDual k V φ hφv₀).base a = linearFunctionalPoint k V φ hφ := by
  have hmem : (pointOfDual k V φ hφv₀).base a ∈ linearSubspace k V (LinearMap.ker φ) :=
    (mem_linearSubspace_iff k V _ _).mpr (pointSubmodule_pointOfDual k V φ hφv₀ a).ge
  rwa [linearSubspace_ker k V φ hφ, Set.mem_singleton_iff] at hmem

/-- **The point cut out by a nonzero functional is `k`-rational**: the residue field of `P(V)`
there is `k`. No finite-dimensionality and no algebraic closedness is needed. -/
theorem isRationalPoint_linearFunctionalPoint (φ : Module.Dual k V) (hφ : φ ≠ 0) :
    IsRationalPoint (projectiveSpaceOfModuleToSpec k V) (linearFunctionalPoint k V φ hφ) := by
  obtain ⟨v₀, hφv₀⟩ := exists_apply_eq_one k V hφ
  rw [← pointOfDual_base k V φ hφ hφv₀ default]
  exact isRationalPoint_base_of_comp_eq_id _ (pointOfDual_comp k V φ hφv₀) default

end PointOfDual

/-! ### The `k`-valued points as one-dimensional quotients -/

section Clause

variable (k V : Type u) [Field k] [AddCommGroup V] [Module k V]

/-- The one-dimensional quotient of `V` attached to a `k`-rational point of `P(V)`: the degree-one
forms vanishing at the point are the kernel of a surjection of `V` onto a line. -/
def pointSubmoduleOfIsRationalPoint
    (x : { x : projectiveSpaceOfModule k V //
        IsRationalPoint (projectiveSpaceOfModuleToSpec k V) x }) :
    { K : Submodule k V // Module.finrank k (V ⧸ K) = 1 } :=
  ⟨pointSubmodule k V x.val, by
    obtain ⟨φ, hφ, hker⟩ := exists_dual_pointSubmodule_eq_ker k V x.val x.property
    rw [hker]
    exact finrank_quotient_ker_eq_one k V hφ⟩

/-- Distinct `k`-rational points of `P(V)` have distinct hyperplanes of degree-one forms. -/
theorem pointSubmoduleOfIsRationalPoint_injective :
    Function.Injective (pointSubmoduleOfIsRationalPoint k V) := by
  rintro ⟨x, hx⟩ ⟨y, hy⟩ hxy
  exact Subtype.ext (eq_of_pointSubmodule_le k V hy (congrArg Subtype.val hxy).ge)

/-- Every one-dimensional quotient of `V` is the hyperplane of a `k`-rational point of `P(V)`. -/
theorem pointSubmoduleOfIsRationalPoint_surjective :
    Function.Surjective (pointSubmoduleOfIsRationalPoint k V) := by
  rintro ⟨K, hK⟩
  obtain ⟨φ, hφ, hker⟩ := exists_surjective_ker_eq_of_finrank_quotient_eq_one k V K hK
  have hφ0 : φ ≠ 0 := LinearMap.ne_zero_of_surjective hφ
  obtain ⟨v₀, hφv₀⟩ := exists_apply_eq_one k V hφ0
  exact ⟨⟨(pointOfDual k V φ hφv₀).base default,
      isRationalPoint_base_of_comp_eq_id _ (pointOfDual_comp k V φ hφv₀) default⟩,
    Subtype.ext ((pointSubmodule_pointOfDual k V φ hφv₀ default).trans hker)⟩

/-- The `k`-rational points of `P(V)` are the one-dimensional quotients of `V`. -/
def isRationalPointEquivOneDimQuotient :
    { x : projectiveSpaceOfModule k V //
        IsRationalPoint (projectiveSpaceOfModuleToSpec k V) x } ≃
      { K : Submodule k V // Module.finrank k (V ⧸ K) = 1 } :=
  Equiv.ofBijective _
    ⟨pointSubmoduleOfIsRationalPoint_injective k V,
      pointSubmoduleOfIsRationalPoint_surjective k V⟩

/-- **Stacks Project, Tag 0FCY.** A `k`-valued point `p` of `P(V)`, that is a section of the
structure morphism `P(V) ⟶ Spec k`, corresponds to a surjection of `k`-vector spaces `V → L_p`
with `dim L_p = 1`.

The quotient is recorded by its kernel, which is the space of degree-one forms vanishing at `p`;
`finrank_quotient_eq_one_iff` turns such a subspace back into a surjection onto a line, and
`mem_kValuedPointEquivOneDimQuotient` identifies the correspondence. -/
def kValuedPointEquivOneDimQuotient :
    { p : Spec (.of k) ⟶ projectiveSpaceOfModule k V //
        p ≫ projectiveSpaceOfModuleToSpec k V = 𝟙 (Spec (.of k)) } ≃
      { K : Submodule k V // Module.finrank k (V ⧸ K) = 1 } :=
  (sectionEquivIsRationalPoint (projectiveSpaceOfModuleToSpec k V)).trans
    (isRationalPointEquivOneDimQuotient k V)

/-- **Stacks Project, Tag 0FCY.** The correspondence between the `k`-valued points of `P(V)` and
the one-dimensional quotients of `V` sends a point to the space of vectors whose degree-one forms
vanish at it. -/
theorem mem_kValuedPointEquivOneDimQuotient
    (p : { p : Spec (.of k) ⟶ projectiveSpaceOfModule k V //
        p ≫ projectiveSpaceOfModuleToSpec k V = 𝟙 (Spec (.of k)) }) (v : V) :
    v ∈ (kValuedPointEquivOneDimQuotient k V p).val ↔
      SymmetricAlgebra.ι k V v ∈ (p.val.base default).asHomogeneousIdeal :=
  mem_pointSubmodule_iff k V _ v

end Clause

end ProjectiveSpaceOfModule

end AlgebraicGeometry

end
