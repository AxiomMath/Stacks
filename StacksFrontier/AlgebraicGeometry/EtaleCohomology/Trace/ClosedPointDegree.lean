module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import Mathlib.FieldTheory.Finite.Basic
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Jacobson.Ring
public import Mathlib.RingTheory.RingHom.FiniteType
public import StacksFrontier.AlgebraicGeometry.FieldToResidue
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degrees of the closed points of a scheme over a field

Let `X` be a scheme over a field `k`. If `X` is locally of finite type over `k`, the residue field
`κ(x)` at a closed point `x` of `X` is a finite extension of `k`, so the degree
`deg x = [κ(x) : k]` is positive.

Over a *finite* field `k`, a quasi-compact `X` locally of finite type over `k` has only finitely
many closed points of degree at most `n`.

## Main definitions

* `Stacks.EtaleCohomology.residueDegree`: the degree `deg x = [κ(x) : k]` over `k` of a point of
  a scheme.

## Main results

* `Stacks.EtaleCohomology.fieldToResidue_eq_appLE_comp_evaluation`: the structural map `k → κ(x)`
  factors through the sections on an affine open containing `x`.
* `Stacks.EtaleCohomology.residueDegree_pos`: a closed point of a scheme locally of finite type
  over a field has positive residue degree.
* `Stacks.EtaleCohomology.finite_setOf_maximal_finrank_le`: a finite-type algebra over a finite
  field has finitely many maximal ideals of bounded residue degree.
* `Stacks.EtaleCohomology.finite_of_forall_affineOpens`: a property of points of a quasi-compact
  scheme holding at finitely many points of every affine open holds at finitely many points.
* `Stacks.EtaleCohomology.finrank_quotient_primeIdealOf`: the degree of a closed point of an
  affine open is the degree of the quotient of the sections by the corresponding maximal ideal.
* `Stacks.EtaleCohomology.finite_setOf_residueDegree_le` and
  `Stacks.EtaleCohomology.finite_setOf_closedPoints_residueDegree_le`: a quasi-compact scheme
  locally of finite type over a finite field has finitely many closed points of bounded degree.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Stacks.EtaleCohomology

/-! ### The residue field at a closed point -/

/-- The degree `deg x = [κ(x) : k]` of a point of a scheme over a field `k`. -/
public def residueDegree {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) : ℕ :=
  letI : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  Module.finrank k (X.residueField x)

/-- If `S` is a localization of `R` at a maximal ideal, the composite `R → S → κ(S)` onto the
residue field of `S` is surjective. -/
public theorem residue_comp_algebraMap_surjective {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [IsLocalRing S] (p : Ideal R) [hp : p.IsMaximal]
    [IsLocalization.AtPrime S p] :
    Function.Surjective ((IsLocalRing.residue S).comp (algebraMap R S)) := by
  intro y
  obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective y
  obtain ⟨⟨a, b⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl s
  obtain ⟨c, i, hi, hci⟩ := hp.exists_inv (b.2 : (b : R) ∉ p)
  have hbc : (b : R) * c - 1 ∈ p :=
    (show (b : R) * c - 1 = -i by linear_combination hci) ▸ p.neg_mem hi
  have h1 : IsLocalRing.residue S (algebraMap R S ((b : R) * c)) = 1 := by
    have h := (IsLocalRing.residue_eq_zero_iff (R := S) _).mpr <| by
      simpa using (IsLocalization.AtPrime.to_map_mem_maximal_iff S p _).mpr hbc
    simpa [sub_eq_zero] using h
  have h2 : algebraMap R S (a * c)
      = IsLocalization.mk' S a b * algebraMap R S ((b : R) * c) := by
    rw [map_mul, map_mul, ← mul_assoc, IsLocalization.mk'_spec]
  refine ⟨a * c, ?_⟩
  change IsLocalRing.residue S (algebraMap R S (a * c))
      = IsLocalRing.residue S (IsLocalization.mk' S a b)
  rw [h2, map_mul, h1, mul_one]

/-- Evaluating sections on an affine open at a closed point is surjective onto the residue
field. -/
public theorem evaluation_surjective {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hxU : x ∈ U) (hx : IsClosed ({x} : Set X)) :
    Function.Surjective (X.evaluation U x hxU).hom := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (U := U) ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have : (hU.primeIdealOf ⟨x, hxU⟩).asIdeal.IsMaximal :=
    hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hxU⟩ hx
  exact residue_comp_algebraMap_surjective (R := Γ(X, U)) (S := X.presheaf.stalk x)
    (hU.primeIdealOf ⟨x, hxU⟩).asIdeal

/-- The structural map `k → κ(x)` factors through the sections on any affine open containing `x`,
as the restriction of the structure morphism followed by evaluation at `x`. -/
public theorem fieldToResidue_eq_appLE_comp_evaluation {k : Type u} [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) {U : X.Opens}
    (hle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens)) (x : X) (hxU : x ∈ U) :
    fieldToResidue f x
      = ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U hle)
        ≫ X.evaluation U x hxU := by
  rw [fieldToResidue, fieldToStalk, Scheme.Hom.appLE, ← Scheme.germ_residue]
  simp only [Category.assoc, X.presheaf.germ_res_assoc]
  rfl

/-- The map `k → Γ(X, U)` induced by the structure morphism over an affine open `U` is of finite
type when `X` is locally of finite type over `k`. -/
private theorem finiteType_inv_comp_appLE {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] {U : X.Opens} (hU : IsAffineOpen U)
    (hle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens)) :
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U hle).hom.FiniteType := by
  rw [CommRingCat.hom_comp]
  exact (LocallyOfFiniteType.finiteType_appLE f (isAffineOpen_top _) hU hle).comp
    (.of_surjective _ (ConcreteCategory.bijective_of_isIso _).surjective)

/-- The residue field at a closed point of a scheme locally of finite type over a field `k` is a
finite-type `k`-algebra. -/
public theorem finiteType_fieldToResidue {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    (fieldToResidue f x).hom.FiniteType := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (x := x) (U := ⊤) trivial
  have hle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens) := by simp
  rw [fieldToResidue_eq_appLE_comp_evaluation f hle x hxU, CommRingCat.hom_comp]
  exact (finiteType_inv_comp_appLE f hU hle).comp_surjective (evaluation_surjective hU x hxU hx)

/-- A closed point of a scheme locally of finite type over a field has positive residue
degree. -/
public theorem residueDegree_pos {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] (x : X) (hx : IsClosed ({x} : Set X)) :
    0 < residueDegree f x := by
  let _ : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  have : Algebra.FiniteType k (X.residueField x) := finiteType_fieldToResidue f x hx
  have : Module.Finite k (X.residueField x) :=
    finite_of_finite_type_of_isJacobsonRing k (X.residueField x)
  exact Module.finrank_pos

/-! ### Counting maximal ideals of bounded residue degree -/

/-- A maximal ideal of bounded residue degree in a finite-type algebra over a finite field is the
kernel of a `k`-algebra map to an algebraic closure of `k` whose values are fixed by the
`#k ^ n !`-power map. -/
private theorem exists_algHom_ker_eq (k A : Type*) [Field k] [Finite k] [CommRing A] [Algebra k A]
    [Algebra.FiniteType k A] (n : ℕ) (m : Ideal A) (hm : m.IsMaximal)
    (hn : Module.finrank k (A ⧸ m) ≤ n) :
    ∃ φ : A →ₐ[k] AlgebraicClosure k, RingHom.ker φ = m ∧
      ∀ x : A, (φ x) ^ (Nat.card k ^ Nat.factorial n) = φ x := by
  let _ : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Algebra.FiniteType k (A ⧸ m) :=
    Algebra.FiniteType.of_surjective (Ideal.Quotient.mkₐ k m) Ideal.Quotient.mk_surjective
  have : Module.Finite k (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing k (A ⧸ m)
  have : Algebra.IsAlgebraic k (A ⧸ m) := Algebra.IsAlgebraic.of_finite k (A ⧸ m)
  have : Finite (A ⧸ m) := Module.finite_of_finite k
  let _ : Fintype (A ⧸ m) := Fintype.ofFinite _
  let _ : Fintype k := Fintype.ofFinite _
  let ψ : (A ⧸ m) →ₐ[k] AlgebraicClosure k := IsAlgClosed.lift
  obtain ⟨e, he⟩ : Module.finrank k (A ⧸ m) ∣ Nat.factorial n :=
    Nat.dvd_factorial Module.finrank_pos hn
  have hpow : ∀ z : A ⧸ m, z ^ (Nat.card k ^ Nat.factorial n) = z := fun z => by
    have h2 : Nat.card k ^ Nat.factorial n = Fintype.card (A ⧸ m) ^ e := by
      rw [Module.card_eq_pow_finrank (K := k), Nat.card_eq_fintype_card, ← pow_mul, ← he]
    rw [h2, FiniteField.pow_card_pow]
  refine ⟨ψ.comp (Ideal.Quotient.mkₐ k m), ?_, fun x => ?_⟩
  · ext x
    simp [Ideal.Quotient.eq_zero_iff_mem]
  · simp only [AlgHom.coe_comp, Function.comp_apply, Ideal.Quotient.mkₐ_eq_mk]
    rw [← map_pow, hpow]

/-- There are finitely many `k`-algebra maps from a finite-type algebra over a finite field `k` to
`AlgebraicClosure k` whose values are fixed by the `#k ^ N`-power map. -/
private theorem finite_setOf_algHom_pow_eq (k A : Type*) [Field k] [Finite k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (N : ℕ) (hN : 0 < N) :
    {φ : A →ₐ[k] AlgebraicClosure k | ∀ x : A, (φ x) ^ (Nat.card k ^ N) = φ x}.Finite := by
  obtain ⟨r, g, hg⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType k A)
  set K := AlgebraicClosure k
  set Ψ : (A →ₐ[k] K) → (Fin r → K) := fun φ i => φ (g (MvPolynomial.X i))
  have hinj : Function.Injective Ψ := by
    intro φ₁ φ₂ h
    have hc : φ₁.comp g = φ₂.comp g := MvPolynomial.algHom_ext fun i => congrFun h i
    refine AlgHom.ext fun a => ?_
    obtain ⟨b, rfl⟩ := hg a
    exact congrFun (congrArg (fun q : MvPolynomial (Fin r) k →ₐ[k] K => (q : _ → K)) hc) b
  have hq : 1 < Nat.card k ^ N := Nat.one_lt_pow (by omega) Finite.one_lt_card
  have hT : {y : K | y ^ (Nat.card k ^ N) = y}.Finite := by
    refine (Polynomial.finite_setOfPred_isRoot
      (FiniteField.X_pow_card_sub_X_ne_zero K hq)).subset fun y hy => ?_
    simp only [Set.mem_ofPred_eq, Polynomial.IsRoot.def, Polynomial.eval_sub,
      Polynomial.eval_pow, Polynomial.eval_X] at hy ⊢
    rw [hy, sub_self]
  exact (Set.Finite.preimage (f := Ψ)
    (s := Set.univ.pi fun _ : Fin r => {y : K | y ^ (Nat.card k ^ N) = y})
    hinj.injOn (Set.Finite.pi fun _ => hT)).subset fun φ hφ i _ => hφ _

/-- A finite-type algebra over a finite field has finitely many maximal ideals whose residue field
has degree at most `n`. -/
public theorem finite_setOf_maximal_finrank_le (k A : Type*) [Field k] [Finite k] [CommRing A]
    [Algebra k A] [Algebra.FiniteType k A] (n : ℕ) :
    {m : Ideal A | m.IsMaximal ∧ Module.finrank k (A ⧸ m) ≤ n}.Finite := by
  refine ((finite_setOf_algHom_pow_eq k A (Nat.factorial n) (Nat.factorial_pos n)).image
    fun φ => RingHom.ker φ).subset ?_
  rintro m ⟨hm, hn⟩
  obtain ⟨φ, hker, hpow⟩ := exists_algHom_ker_eq k A n m hm hn
  exact ⟨φ, hpow, hker⟩

/-! ### From affine opens to the whole scheme -/

/-- A property of the points of a quasi-compact scheme that holds at finitely many points of
every affine open holds at finitely many points of the scheme. -/
public theorem finite_of_forall_affineOpens {X : Scheme.{u}} [CompactSpace X] (P : X → Prop)
    (h : ∀ U : X.affineOpens, {x : X | P x ∧ x ∈ (U : X.Opens)}.Finite) :
    {x : X | P x}.Finite := by
  obtain ⟨s, hs, hcover⟩ :=
    (AlgebraicGeometry.isCompact_and_isOpen_iff_finite_and_eq_biUnion_affineOpens
      (X := X) (U := Set.univ)).mp ⟨CompactSpace.isCompact_univ, isOpen_univ⟩
  refine (hs.biUnion fun U _ => h U).subset fun x hx => ?_
  obtain ⟨U, hU, hxU⟩ := Set.mem_iUnion₂.1 (hcover ▸ Set.mem_univ x)
  exact Set.mem_iUnion₂.2 ⟨U, hU, hx, hxU⟩

/-! ### Closed points of bounded degree -/

/-- On an affine open `U`, the kernel of evaluation at a point `x` of `U` is the prime ideal of
`Γ(X, U)` corresponding to `x`. -/
public theorem ker_evaluation {X : Scheme.{u}} {U : X.Opens} (hU : IsAffineOpen U) (x : X)
    (hxU : x ∈ U) :
    RingHom.ker (X.evaluation U x hxU).hom = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := by
  let _ : Algebra Γ(X, U) (X.presheaf.stalk x) :=
    X.presheaf.algebra_section_stalk (U := U) ⟨x, hxU⟩
  have : IsLocalization.AtPrime (X.presheaf.stalk x) (hU.primeIdealOf ⟨x, hxU⟩).asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  ext r
  exact (IsLocalRing.residue_eq_zero_iff (R := X.presheaf.stalk x) _).trans
    (IsLocalization.AtPrime.to_map_mem_maximal_iff _ _ r)

/-- The degree of a closed point `x` of an affine open `U` is the degree over `k` of the quotient
of `Γ(X, U)` by the maximal ideal corresponding to `x`. -/
public theorem finrank_quotient_primeIdealOf {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hxU : x ∈ U)
    (hx : IsClosed ({x} : Set X)) [Algebra k Γ(X, U)]
    (hcomp : (X.evaluation U x hxU).hom.comp (algebraMap k Γ(X, U))
      = (fieldToResidue f x).hom) :
    Module.finrank k (Γ(X, U) ⧸ (hU.primeIdealOf ⟨x, hxU⟩).asIdeal) = residueDegree f x := by
  let _ : Algebra k (X.residueField x) := (fieldToResidue f x).hom.toAlgebra
  let ψ : Γ(X, U) →ₐ[k] X.residueField x :=
    { (X.evaluation U x hxU).hom with commutes' := fun c => congr($hcomp c) }
  have hker : RingHom.ker ψ = (hU.primeIdealOf ⟨x, hxU⟩).asIdeal := ker_evaluation hU x hxU
  have hsurj : Function.Surjective ψ := evaluation_surjective hU x hxU hx
  exact ((Ideal.quotientEquivAlgOfEq k hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hsurj)).toLinearEquiv.finrank_eq

/-- A quasi-compact scheme locally of finite type over a finite field has only finitely many
closed points of residue degree at most `n`. -/
@[ega "IV 10.4.11.1" "(ii), special case"]
public theorem finite_setOf_residueDegree_le {k : Type u} [Field k] [Finite k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ) :
    {x : X | IsClosed ({x} : Set X) ∧ residueDegree f x ≤ n}.Finite := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  refine finite_of_forall_affineOpens _ fun V => ?_
  obtain ⟨U, hU⟩ := V
  have hle : U ≤ f ⁻¹ᵁ (⊤ : (Spec (CommRingCat.of k)).Opens) := by simp
  let _ : Algebra k Γ(X, U) :=
    ((Scheme.ΓSpecIso (CommRingCat.of k)).inv ≫ f.appLE ⊤ U hle).hom.toAlgebra
  have hft : Algebra.FiniteType k Γ(X, U) := by
    exact finiteType_inv_comp_appLE f hU hle
  have hcomp : ∀ (x : X) (hxU : x ∈ U), (X.evaluation U x hxU).hom.comp (algebraMap k Γ(X, U))
      = (fieldToResidue f x).hom := by
    intro x hxU
    rw [fieldToResidue_eq_appLE_comp_evaluation f hle x hxU, CommRingCat.hom_comp]
    rfl
  have hinj : Function.Injective (fun y : U => (hU.primeIdealOf y).asIdeal) := fun y₁ y₂ h =>
    (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso hU.isoSpec)).injective (PrimeSpectrum.ext h)
  have himg : {x : X | (IsClosed ({x} : Set X) ∧ residueDegree f x ≤ n) ∧ x ∈ U}
      = Subtype.val '' {y : U | IsClosed ({y.1} : Set X) ∧ residueDegree f y.1 ≤ n} := by
    ext z
    exact ⟨fun ⟨hP, hz⟩ => ⟨⟨z, hz⟩, hP, rfl⟩, fun ⟨⟨z, hz⟩, hP, h⟩ => h ▸ ⟨hP, hz⟩⟩
  rw [himg]
  refine Set.Finite.image _ (Set.Finite.subset (Set.Finite.preimage (f := fun y : U =>
    (hU.primeIdealOf y).asIdeal) hinj.injOn
    (finite_setOf_maximal_finrank_le k Γ(X, U) n)) ?_)
  rintro ⟨x, hxU⟩ ⟨hclosed, hdeg⟩
  refine ⟨hU.primeIdealOf_isMaximal_of_isClosed ⟨x, hxU⟩ hclosed, ?_⟩
  rwa [finrank_quotient_primeIdealOf f hU x hxU hclosed (hcomp x hxU)]

/-- A quasi-compact scheme locally of finite type over a finite field has only finitely many
closed points of residue degree at most `n`, as a subset of the closed points. -/
@[ega "IV 10.4.11.1" "(ii), special case"]
public theorem finite_setOf_closedPoints_residueDegree_le {k : Type u} [Field k] [Finite k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] (n : ℕ) :
    {x : closedPoints X | residueDegree f x.1 ≤ n}.Finite := by
  refine Set.Finite.of_finite_image (f := (Subtype.val : closedPoints X → X)) ?_
    Subtype.val_injective.injOn
  refine (finite_setOf_residueDegree_le f n).subset ?_
  rintro x ⟨y, hy, rfl⟩
  exact ⟨y.2, hy⟩

end Stacks.EtaleCohomology

end
