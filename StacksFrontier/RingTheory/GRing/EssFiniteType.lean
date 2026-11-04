module

public import Mathlib
public import Mathlib.RingTheory.DedekindDomain.Basic
public import Mathlib.RingTheory.EssentialFiniteness
public import StacksFrontier.RingTheory.AdicCompletion.PermanenceOfProperties
public import StacksFrontier.RingTheory.Derivation.Extension
public import StacksFrontier.RingTheory.Derivation.Regularity
public import StacksFrontier.RingTheory.EssentialFiniteness.ColimitFinitePresentation
public import StacksFrontier.RingTheory.FormalFibres.RingMapProperty
public import StacksFrontier.RingTheory.FormallySmooth.Regularity
public import StacksFrontier.RingTheory.FormallySmooth.TopologicalRings
public import StacksFrontier.RingTheory.GRing.Criteria
public import StacksFrontier.RingTheory.GRing.Defs
public import StacksFrontier.RingTheory.GRing.Henselization
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import StacksFrontier.RingTheory.Henselian.Colimit
public import StacksFrontier.RingTheory.Henselian.Henselization.Existence
public import StacksFrontier.RingTheory.Henselian.HenselizationUniversalProperty
public import StacksFrontier.RingTheory.RegularLocalRing.Basic
public import StacksFrontier.RingTheory.RegularRing.Defs
public import StacksFrontier.RingTheory.RegularRing.GlobalDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# G-rings and algebras essentially of finite type

This file shows that the formal fibres of the completion of a localized polynomial ring over a
Noetherian complete local domain of prime characteristic are geometrically regular, that an
algebra essentially of finite type over a G-ring is a G-ring, that the basic examples of rings
are G-rings, and that every henselian local ring is a filtered colimit of henselian local G-rings.

## Main results

* `isGeometricallyRegular_formalFiber_polynomial`: let `A` be a Noetherian complete local domain
  whose fraction field has prime characteristic, `q` a maximal ideal of `A[X]` over the maximal
  ideal of `A` and `r ⊆ q` a nonzero prime over zero; then the formal fibre at `r` of the
  completion of `A[X]` localized at `q` is geometrically regular over `κ(r)`.
* `isGRing_of_essFiniteType`: an algebra essentially of finite type over a G-ring is a G-ring.
* `isGRing_basic_examples`: fields, Noetherian complete local rings, the integers and Dedekind
  domains of characteristic zero are G-rings, and a finite-type algebra over a G-ring is a
  G-ring.
* `exists_filteredColimit_henselianLocalGRing`: a henselian local ring is a filtered colimit of
  henselian local G-rings whose transition maps are local homomorphisms.

## References

* [Stacks Project, Tag 07PU](https://stacks.math.columbia.edu/tag/07PU)
* [Stacks Project, Tag 07PV](https://stacks.math.columbia.edu/tag/07PV)
* [Stacks Project, Tag 07PX](https://stacks.math.columbia.edu/tag/07PX)
* [Stacks Project, Tag 0A41](https://stacks.math.columbia.edu/tag/0A41)
-/

@[expose] public section

open Stacks.DerivationExtension
open Stacks.EssentialFiniteness.LocalRingColimit

/-! ### Formal fibres of a polynomial ring over a complete local domain -/

section

section

open scoped TensorProduct
open IsLocalRing

/-- Every element of the `I`-adic completion of `R` agrees with the image of an element of `R`
modulo any prescribed power of the extended ideal. -/
public theorem exists_sub_algebraMap_mem_pow_map
    {R : Type*} [CommRing R] (I : Ideal R) (hI : I.FG)
    (n : ℕ) (x : AdicCompletion I R) :
    ∃ r : R, x - algebraMap R (AdicCompletion I R) r ∈
      (I.map (algebraMap R (AdicCompletion I R))) ^ n := by
  obtain ⟨r, hr⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval I R n x)
  refine ⟨r, ?_⟩
  rw [← Ideal.map_pow, ← Submodule.restrictScalars_mem R, ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval hI]
  show AdicCompletion.eval I R n (x - algebraMap R (AdicCompletion I R) r) = 0
  rw [map_sub, sub_eq_zero]
  exact hr.symm

/-- Two ring homomorphisms out of an adic completion that agree on the image of the base ring
agree everywhere, provided each kills some power of the extended ideal. -/
public theorem adicCompletion_ringHom_ext_of_pow_le_ker
    {R S : Type*} [CommRing R] [CommRing S] (I : Ideal R) (hI : I.FG)
    (f g : AdicCompletion I R →+* S) (m n : ℕ)
    (hf : (I.map (algebraMap R (AdicCompletion I R))) ^ m ≤ RingHom.ker f)
    (hg : (I.map (algebraMap R (AdicCompletion I R))) ^ n ≤ RingHom.ker g)
    (hfg : f.comp (algebraMap R (AdicCompletion I R)) =
      g.comp (algebraMap R (AdicCompletion I R))) : f = g := by
  ext x
  obtain ⟨r, hr⟩ := exists_sub_algebraMap_mem_pow_map I hI (max m n) x
  have hfx : f x = f (algebraMap R (AdicCompletion I R) r) := by
    simpa only [RingHom.mem_ker, map_sub, sub_eq_zero] using
      hf (Ideal.pow_le_pow_right (le_max_left m n) hr)
  have hgx : g x = g (algebraMap R (AdicCompletion I R) r) := by
    simpa only [RingHom.mem_ker, map_sub, sub_eq_zero] using
      hg (Ideal.pow_le_pow_right (le_max_right m n) hr)
  exact hfx.trans ((DFunLike.congr_fun hfg r).trans hgx.symm)

/-- The adic completion of a formally smooth algebra is formally smooth for the topology
defined by the extended ideal. -/
public theorem formallySmoothNAdic_adicCompletion
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [Algebra.FormallySmooth A B] (I : Ideal B) (hI : I.FG) :
    RingHom.FormallySmoothNAdic (algebraMap A (AdicCompletion I B))
      (I.map (algebraMap B (AdicCompletion I B))) := by
  intro D _ J hJ f ψ hcomm hk
  let C := AdicCompletion I B
  let : Algebra A D := f.toAlgebra
  let ψB : B →ₐ[A] D ⧸ J :=
    { toRingHom := ψ.comp (algebraMap B C)
      commutes' := fun a => by
        show ψ (algebraMap B C (algebraMap A B a)) = Ideal.Quotient.mk J (f a)
        rw [← IsScalarTower.algebraMap_apply]
        exact DFunLike.congr_fun hcomm a }
  obtain ⟨g, hg⟩ := Algebra.FormallySmooth.exists_lift J ⟨2, hJ⟩ ψB
  obtain ⟨k, hkpos, hk⟩ := hk
  have hgJ : I ^ k ≤ J.comap g.toRingHom := by
    intro b hb
    show g b ∈ J
    apply Ideal.Quotient.eq_zero_iff_mem.mp
    have heq := DFunLike.congr_fun hg b
    change Ideal.Quotient.mk J (g b) = ψ (algebraMap B C b) at heq
    rw [heq]
    exact hk (by rw [← Ideal.map_pow]; exact Ideal.mem_map_of_mem _ hb)
  have hgker : I ^ (k * 2) ≤ RingHom.ker g.toRingHom := by
    rw [← Ideal.map_le_iff_le_comap] at hgJ
    intro b hb
    have hx : g b ∈ J ^ 2 := by
      apply Ideal.pow_right_mono hgJ 2
      rw [← Ideal.map_pow, ← pow_mul]
      exact Ideal.mem_map_of_mem _ hb
    simpa [hJ] using hx
  let ghat : C →+* D := (Ideal.Quotient.lift (I ^ (k * 2)) g.toRingHom hgker).comp
    (AdicCompletion.evalₐ I (k * 2)).toRingHom
  have hghat : ∀ b : B, ghat (algebraMap B C b) = g b := by
    intro b
    simp [ghat, C, AdicCompletion.algebraMap_apply]
  have hghatpow : (I.map (algebraMap B C)) ^ (k * 2) ≤ RingHom.ker ghat := by
    rw [← Ideal.map_pow, Ideal.map_le_iff_le_comap]
    intro b hb
    show ghat (algebraMap B C b) = 0
    rw [hghat]
    exact hgker hb
  refine ⟨ghat, ?_, ?_⟩
  · apply adicCompletion_ringHom_ext_of_pow_le_ker I hI
      ((Ideal.Quotient.mk J).comp ghat) ψ (k * 2) k
    · intro x hx
      show Ideal.Quotient.mk J (ghat x) = 0
      rw [show ghat x = 0 from hghatpow hx, map_zero]
    · exact hk
    · ext b
      show Ideal.Quotient.mk J (ghat (algebraMap B C b)) = ψ (algebraMap B C b)
      rw [hghat]
      exact DFunLike.congr_fun hg b
  · ext a
    show ghat (algebraMap A C a) = f a
    rw [IsScalarTower.algebraMap_apply A B C, hghat]
    exact g.commutes a

attribute [local instance 10000] Ring.toIntAlgebra

private theorem exists_derivation_adicCompletion_polynomial_localization
    (A : Type*) [CommRing A] (q : Ideal (Polynomial A)) [q.IsPrime] :
    ∃ D : Derivation ℤ
        (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q))
        (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)),
      ∀ f : Polynomial A,
        D (algebraMap (Polynomial A) _ f) =
          algebraMap (Polynomial A) _ (Polynomial.derivative f) := by
  let D := (Polynomial.derivative' (R := A)).restrictScalars ℤ
  let Dloc : Derivation ℤ (Localization.AtPrime q) (Localization.AtPrime q) :=
    Stacks.DerivationExtension.locDeriv D q.primeCompl (Localization.AtPrime q)
  have hDloc : Stacks.DerivationExtension.ExtendsAlong
      (algebraMap (Polynomial A) (Localization.AtPrime q)) D Dloc :=
    Stacks.DerivationExtension.locDeriv_extendsAlong D q.primeCompl (Localization.AtPrime q)
  obtain ⟨Dhat, hDhat⟩ := Stacks.DerivationExtension.exists_derivation_adicCompletion
    (Localization.AtPrime q) Dloc (maximalIdeal (Localization.AtPrime q))
  refine ⟨Dhat, fun f ↦ ?_⟩
  rw [IsScalarTower.algebraMap_apply (Polynomial A) (Localization.AtPrime q),
    hDhat, hDloc]
  rfl

private theorem isRegularRingHom_adicCompletion_of_formallySmooth
    {A B : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [IsNoetherianRing A] [IsLocalRing A] [IsPrecomplete (maximalIdeal A) A]
    [IsNoetherianRing B] [IsLocalRing B] [IsLocalHom (algebraMap A B)]
    [Algebra.FormallySmooth A B] :
    IsRegularRingHom
      (algebraMap A (AdicCompletion (maximalIdeal B) B)) := by
  let C := AdicCompletion (maximalIdeal B) B
  have : IsAdicComplete (maximalIdeal A) A := ⟨⟩
  have : IsLocalHom (algebraMap A C) := by
    rw [IsScalarTower.algebraMap_eq A B C]
    infer_instance
  apply ((isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae
    (algebraMap A C)).out 4 1).mp
  rw [AdicCompletion.maximalIdeal_eq_map]
  exact formallySmoothNAdic_adicCompletion (maximalIdeal B)
    (IsNoetherian.noetherian _)

universe u

private theorem exists_derivation_adicCompletion_polynomial_eq_one
    (A : Type*) [CommRing A] (q : Ideal (Polynomial A)) [q.IsPrime] :
    ∃ D : Derivation A
        (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q))
        (AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)),
      D (algebraMap (Polynomial A) _ Polynomial.X) = 1 := by
  let C := AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
  obtain ⟨Dhat, hDhat⟩ := exists_derivation_adicCompletion_polynomial_localization A q
  have h0 (a : A) : Dhat (algebraMap A C a) = 0 := by
    rw [IsScalarTower.algebraMap_apply A (Polynomial A) C]
    simpa only [Polynomial.algebraMap_eq, Polynomial.derivative_C, map_zero] using
      hDhat (Polynomial.C a)
  refine ⟨{ toFun := Dhat
            map_add' := Dhat.map_add
            map_smul' := fun a c => ?_
            map_one_eq_zero' := Dhat.map_one_eq_zero
            leibniz' := fun a b => Dhat.leibniz a b }, ?_⟩
  · show Dhat (a • c) = a • Dhat c
    rw [Algebra.smul_def, Dhat.leibniz, h0, smul_zero, add_zero, smul_eq_mul,
      Algebra.smul_def]
  · show Dhat _ = 1
    rw [hDhat, Polynomial.derivative_X, map_one]

private noncomputable def tensorDerivation
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (L : Type*) [CommRing L] [Algebra R L] (D : Derivation R B B) :
    Derivation R (L ⊗[R] B) (L ⊗[R] B) := by
  let d := D.toLinearMap.lTensor L
  refine Derivation.mk' d fun a b => ?_
  change d (a * b) = a * d b + b * d a
  induction a using TensorProduct.induction_on with
  | zero => simp
  | add a a' ha ha' => simp only [add_mul, map_add, ha, ha', mul_add]; ring
  | tmul l b' =>
    induction b using TensorProduct.induction_on with
    | zero => simp
    | add c c' hc hc' => simp only [mul_add, map_add, hc, hc', add_mul]; ring
    | tmul l' c =>
      simp [d, Algebra.TensorProduct.tmul_mul_tmul, Derivation.leibniz,
        smul_eq_mul, TensorProduct.tmul_add, mul_comm]

private lemma tensorDerivation_tmul
    {R B : Type*} [CommRing R] [CommRing B] [Algebra R B]
    (L : Type*) [CommRing L] [Algebra R L] (D : Derivation R B B) (l : L) (b : B) :
    tensorDerivation L D (l ⊗ₜ[R] b) = l ⊗ₜ[R] D b := rfl

private lemma isRegularRing_quotient_tensorProduct_of_derivation
    {R B L : Type*} [CommRing R] [CommRing B] [CommRing L]
    [Algebra R B] [Algebra R L] [IsRegularRing (L ⊗[R] B)]
    (D : Derivation R B B) (x : B) (hx : D x = 1) (a : L) :
    IsRegularRing ((L ⊗[R] B) ⧸ Ideal.span {1 ⊗ₜ[R] x - a ⊗ₜ[R] 1}) := by
  let : Algebra ℤ (L ⊗[R] B) := Ring.toIntAlgebra _
  apply isRegularRing_quotient_span_singleton_of_isUnit_derivation
    _ ((tensorDerivation L D).restrictScalars ℤ)
  simp [Derivation.restrictScalars_apply, map_sub, tensorDerivation_tmul, hx,
    ← Algebra.TensorProduct.one_def]

private noncomputable def tensorProductPolynomialQuotientEquiv
    (R L B : Type*) [CommRing R] [CommRing L] [CommRing B]
    [Algebra R L] [Algebra R B]
    [Algebra (Polynomial R) L] [Algebra (Polynomial R) B]
    [IsScalarTower R (Polynomial R) L] [IsScalarTower R (Polynomial R) B] :
    ((L ⊗[R] B) ⧸ Ideal.span
      {1 ⊗ₜ[R] algebraMap (Polynomial R) B Polynomial.X -
        algebraMap (Polynomial R) L Polynomial.X ⊗ₜ[R] 1}) ≃+*
      L ⊗[Polynomial R] B := by
  let P := Polynomial R
  let E := L ⊗[R] B
  let y : E := 1 ⊗ₜ[R] algebraMap P B Polynomial.X -
    algebraMap P L Polynomial.X ⊗ₜ[R] 1
  let I : Ideal E := Ideal.span {y}
  let Q := E ⧸ I
  let π : E →+* Q := Ideal.Quotient.mk I
  let F := Algebra.TensorProduct.mapOfCompatibleSMul P R L L B
  have hFy : F y = 0 := by
    simp only [y, map_sub, F, Algebra.TensorProduct.mapOfCompatibleSMul_tmul]
    apply sub_eq_zero.mpr
    simpa only [Algebra.algebraMap_eq_smul_one] using
      (TensorProduct.smul_tmul (Polynomial.X : P) (1 : L) (1 : B)).symm
  have hker : I ≤ RingHom.ker F.toRingHom :=
    Ideal.span_le.mpr (Set.singleton_subset_iff.mpr hFy)
  let Fbar : Q →+* L ⊗[P] B := Ideal.Quotient.lift I F.toRingHom
    (fun a ha => hker ha)
  have hpoly : (π.comp
      (Algebra.TensorProduct.includeRight (R := R) (A := L) (B := B)).toRingHom).comp
      (algebraMap P B) = algebraMap P Q := by
    apply Polynomial.ringHom_ext'
    · apply RingHom.ext
      intro r
      change π (1 ⊗ₜ[R] algebraMap P B (algebraMap R P r)) =
        π (algebraMap P L (algebraMap R P r) ⊗ₜ[R] 1)
      rw [← IsScalarTower.algebraMap_apply R P, ← IsScalarTower.algebraMap_apply R P]
      apply congrArg π
      simpa only [Algebra.algebraMap_eq_smul_one] using
        (TensorProduct.smul_tmul r (1 : L) (1 : B)).symm
    · change π (1 ⊗ₜ[R] algebraMap P B Polynomial.X) =
        π (algebraMap P L Polynomial.X ⊗ₜ[R] 1)
      apply sub_eq_zero.mp
      rw [← map_sub]
      exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.mem_span_singleton_self y)
  let f : B →ₐ[P] Q :=
    { π.comp (Algebra.TensorProduct.includeRight (R := R) (A := L) (B := B)).toRingHom with
      commutes' := RingHom.congr_fun hpoly }
  let g : L ⊗[P] B →ₐ[P] Q := Algebra.TensorProduct.lift
    (IsScalarTower.toAlgHom P L Q) f (fun _ _ => Commute.all _ _)
  refine RingEquiv.ofRingHom Fbar g.toRingHom ?_ ?_
  · apply RingHom.ext
    intro z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp_all
    | tmul l b =>
      change Fbar (algebraMap L Q l * π (1 ⊗ₜ[R] b)) = l ⊗ₜ[P] b
      change Fbar (π (l ⊗ₜ[R] 1) * π (1 ⊗ₜ[R] b)) = _
      rw [← map_mul]
      change F ((l ⊗ₜ[R] 1) * (1 ⊗ₜ[R] b)) = _
      simp [F, Algebra.TensorProduct.tmul_mul_tmul]
  · apply RingHom.ext
    intro z
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective z
    change g (F z) = π z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | add z z' hz hz' => simp_all
    | tmul l b =>
      change algebraMap L Q l * π (1 ⊗ₜ[R] b) = π (l ⊗ₜ[R] b)
      change π (l ⊗ₜ[R] 1) * π (1 ⊗ₜ[R] b) = _
      rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
private lemma tensorProductPolynomialQuotientEquiv_mk_tmul
    (R L B : Type*) [CommRing R] [CommRing L] [CommRing B]
    [Algebra R L] [Algebra R B]
    [Algebra (Polynomial R) L] [Algebra (Polynomial R) B]
    [IsScalarTower R (Polynomial R) L] [IsScalarTower R (Polynomial R) B]
    (l : L) (b : B) :
    tensorProductPolynomialQuotientEquiv R L B (Ideal.Quotient.mk _ (l ⊗ₜ[R] b)) =
      l ⊗ₜ[Polynomial R] b := rfl

private lemma isRegularRing_tensorProduct_polynomial_of_derivation
    (R L B : Type*) [CommRing R] [CommRing L] [CommRing B]
    [Algebra R L] [Algebra R B]
    [Algebra (Polynomial R) L] [Algebra (Polynomial R) B]
    [IsScalarTower R (Polynomial R) L] [IsScalarTower R (Polynomial R) B]
    [IsRegularRing (L ⊗[R] B)] (D : Derivation R B B)
    (hD : D (algebraMap (Polynomial R) B Polynomial.X) = 1) :
    IsRegularRing (L ⊗[Polynomial R] B) := by
  have := isRegularRing_quotient_tensorProduct_of_derivation D _ hD
    (algebraMap (Polynomial R) L Polynomial.X)
  exact IsRegularRing.of_ringEquiv (tensorProductPolynomialQuotientEquiv R L B)

private theorem isRegularRing_tensorProduct_adicCompletion_polynomial_of_injective
    (A L : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsPrecomplete (maximalIdeal A) A] [Field L] [Algebra A L] [Algebra (Polynomial A) L]
    [IsScalarTower A (Polynomial A) L] [Algebra.EssFiniteType A L]
    (hinj : Function.Injective (algebraMap A L))
    (q : Ideal (Polynomial A)) [q.IsMaximal]
    (hq : q.comap Polynomial.C = maximalIdeal A) :
    IsRegularRing (L ⊗[Polynomial A]
      AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)) := by
  let C := AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
  let F := (⊥ : Ideal A).ResidueField
  let B := Localization.AtPrime q
  have : IsLocalHom (algebraMap A B) := by
    apply ((IsLocalRing.local_hom_TFAE (algebraMap A B)).out 5 1).mp
    rw [IsScalarTower.algebraMap_eq A (Polynomial A) B, ← Ideal.comap_comap]
    show ((maximalIdeal B).under (Polynomial A)).comap Polynomial.C = maximalIdeal A
    rwa [IsLocalization.AtPrime.under_maximalIdeal B q]
  have hreg := isRegularRingHom_adicCompletion_of_formallySmooth (A := A) (B := B)
  have : Algebra.IsGeometricallyRegular F (F ⊗[A] C) :=
    ((isRegularRingHom_algebraMap_iff.mp hreg).2 ⊥).2
  let : Algebra F L := (IsFractionRing.lift hinj).toAlgebra
  have : IsScalarTower A F L :=
    IsScalarTower.of_algebraMap_eq fun a => (IsFractionRing.lift_algebraMap hinj a).symm
  have : Algebra.EssFiniteType F L := Algebra.EssFiniteType.of_comp A F L
  have : IsRegularRing (L ⊗[A] C) :=
    IsRegularRing.of_ringEquiv (R := L ⊗[F] (F ⊗[A] C))
      (Algebra.TensorProduct.cancelBaseChange A F L L C).toRingEquiv
  obtain ⟨D, hD⟩ := exists_derivation_adicCompletion_polynomial_eq_one A q
  exact isRegularRing_tensorProduct_polynomial_of_derivation A L C D hD

/-- The formal fibre at a nonzero prime `r` contained in a maximal ideal `q` of
`A[X]`, where `q` lies over the maximal ideal of the Noetherian complete local
domain `A` and `r` lies over zero, is geometrically regular over `κ(r)` when
the fraction field of `A` has prime characteristic. -/
@[stacks 07PU]
public theorem isGeometricallyRegular_formalFiber_polynomial
    (p : ℕ) (_hp : p.Prime)
    (A : Type u) [CommRing A] [IsDomain A] [IsNoetherianRing A] [IsLocalRing A]
    [IsPrecomplete (maximalIdeal A) A] [CharP (FractionRing A) p]
    (q r : Ideal (Polynomial A)) [q.IsMaximal] [r.IsPrime]
    (hq : q.comap Polynomial.C = maximalIdeal A)
    (_hr0 : r ≠ ⊥) (_hrq : r ≤ q) (hrA : r.comap Polynomial.C = ⊥) :
    Algebra.IsGeometricallyRegular r.ResidueField
      (r.ResidueField ⊗[Polynomial A]
        AdicCompletion (maximalIdeal (Localization.AtPrime q))
          (Localization.AtPrime q)) := by
  let κ := r.ResidueField
  let C := AdicCompletion (maximalIdeal (Localization.AtPrime q)) (Localization.AtPrime q)
  constructor
  intro L _ _ _
  let : Algebra (Polynomial A) L :=
    ((algebraMap κ L).comp (algebraMap (Polynomial A) κ)).toAlgebra
  have : IsScalarTower (Polynomial A) κ L := .of_algebraMap_eq' rfl
  let : Algebra A L := ((algebraMap (Polynomial A) L).comp (algebraMap A (Polynomial A))).toAlgebra
  have : IsScalarTower A (Polynomial A) L := .of_algebraMap_eq' rfl
  have : IsScalarTower A κ L := .of_algebraMap_eq fun a => by
    rw [IsScalarTower.algebraMap_apply A (Polynomial A) κ]
    rfl
  have : Algebra.EssFiniteType A κ := Algebra.EssFiniteType.comp A (Polynomial A) κ
  have : Algebra.EssFiniteType A L := Algebra.EssFiniteType.comp A κ L
  have hκ : Function.Injective (algebraMap A κ) := by
    rwa [RingHom.injective_iff_ker_eq_bot, IsScalarTower.algebraMap_eq A (Polynomial A) κ,
      ← RingHom.comap_ker, Ideal.ker_algebraMap_residueField, Polynomial.algebraMap_eq]
  have hinj : Function.Injective (algebraMap A L) := by
    rw [IsScalarTower.algebraMap_eq A κ L]
    exact (algebraMap κ L).injective.comp hκ
  have := isRegularRing_tensorProduct_adicCompletion_polynomial_of_injective A L hinj q hq
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange (Polynomial A) κ L L C).symm.toRingEquiv

end

end

/-! ### Algebras essentially of finite type over G-rings -/

section

section

open IsLocalRing
open scoped TensorProduct

universe u v w x

private abbrev P : RingMapProperty.{w, w} :=
  RingMapProperty.geometricallyRegular

private lemma isGRing_iff_isPRingAt (R : Type u) [CommRing R] :
    IsGRing R ↔
      IsPRingAt.{u, v, v}
        (RingMapProperty.geometricallyRegular :
          RingMapProperty.{max u v, max u v}) R := by
  constructor
  · rintro ⟨hN, h⟩
    let := hN
    exact ⟨hN, fun p =>
      (Stacks.GRing.formalFibersHaveAt_iff_isRegularRingHom _).mpr (h p.asIdeal)⟩
  · rintro ⟨hN, h⟩
    let := hN
    exact ⟨hN, fun p _ =>
      (Stacks.GRing.formalFibersHaveAt_iff_isRegularRingHom _).mp (h ⟨p, inferInstance⟩)⟩

private lemma isGRing_of_ringEquiv {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (e : A ≃+* B) (hA : IsGRing A) :
    IsGRing B := by
  have : IsNoetherianRing A := hA.1
  have : IsNoetherianRing B := isNoetherianRing_of_ringEquiv A e
  refine (isGRing_iff_isPRingAt.{v, u} B).mpr ⟨inferInstance, fun q => ?_⟩
  let p : PrimeSpectrum A := ⟨q.asIdeal.comap e.toRingHom, inferInstance⟩
  exact Stacks.FormalFibres.formalFibersHaveAt_of_ringEquiv.{u, v, 0, 0} _
    (Localization.localRingEquiv p.asIdeal q.asIdeal e rfl)
    (((isGRing_iff_isPRingAt.{u, v} A).mp hA).2 p)

private lemma isGRing_of_isLocalization {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] [Algebra A B]
    (M : Submonoid A) [IsLocalization M B] (hA : IsGRing A) :
    IsGRing B := by
  have : IsNoetherianRing A := hA.1
  have : IsNoetherianRing B := IsLocalization.isNoetherianRing M B inferInstance
  refine ⟨inferInstance, fun q _ => ?_⟩
  let p : Ideal A := q.comap (algebraMap A B)
  have : p.IsPrime := inferInstance
  have : IsLocalization.AtPrime (Localization.AtPrime q) p :=
    IsLocalization.isLocalization_isLocalization_atPrime_isLocalization M
      (T := Localization.AtPrime q) q
  let e := (IsLocalization.algEquiv p.primeCompl
    (Localization.AtPrime p) (Localization.AtPrime q)).toRingEquiv
  exact (Stacks.GRing.formalFibersHaveAt_iff_isRegularRingHom.{v, u} _).mp
    (Stacks.FormalFibres.formalFibersHaveAt_of_ringEquiv.{u, v, 0, 0} _ e
      ((Stacks.GRing.formalFibersHaveAt_iff_isRegularRingHom.{u, v} _).mpr (hA.2 p)))

private lemma isGRing_of_surjective {A : Type u} {B : Type v}
    [CommRing A] [CommRing B] (f : A →+* B) (hf : Function.Surjective f)
    (hA : IsGRing A) : IsGRing B := by
  let : Algebra A B := f.toAlgebra
  have : IsNoetherianRing A := hA.1
  have : IsNoetherianRing B := isNoetherianRing_of_surjective A B f hf
  have : Module.Finite A B := Module.Finite.of_surjective
    (Algebra.linearMap A B) hf
  have : Algebra.FiniteType A B := inferInstance
  have : Algebra.QuasiFinite A B := inferInstance
  exact ⟨inferInstance, fun q _ =>
    ((quasiFinite_preserves_geometricallyRegular_formalFibers_and_isGRing
      (R := A) q q le_rfl).2.2 inferInstance hA).2 q⟩

private lemma isGRing_mvPolynomial_of_polynomial
    (hpoly : ∀ (A : Type u) [CommRing A],
      IsGRing A → IsGRing (Polynomial A))
    {R : Type u} [CommRing R] (hR : IsGRing R) (n : ℕ) :
    IsGRing (MvPolynomial (Fin n) R) := by
  induction n with
  | zero => exact isGRing_of_ringEquiv (MvPolynomial.isEmptyRingEquiv R (Fin 0)).symm hR
  | succ n ih =>
    exact isGRing_of_ringEquiv (MvPolynomial.finSuccEquiv R n).symm.toRingEquiv
      (hpoly _ ih)

private lemma isGRing_of_finiteType_of_polynomial
    (hpoly : ∀ (A : Type u) [CommRing A],
      IsGRing A → IsGRing (Polynomial A))
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (hR : IsGRing R) :
    IsGRing S := by
  obtain ⟨n, f, hf⟩ := Algebra.FiniteType.iff_quotient_mvPolynomial''.mp
    (inferInstance : Algebra.FiniteType R S)
  exact isGRing_of_surjective f.toRingHom hf
    (isGRing_mvPolynomial_of_polynomial hpoly hR n)

private lemma isGRing_of_essFiniteType_of_polynomial
    (hpoly : ∀ (A : Type u) [CommRing A],
      IsGRing A → IsGRing (Polynomial A))
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (hR : IsGRing R) :
    IsGRing S :=
  isGRing_of_isLocalization (Algebra.EssFiniteType.submonoid R S)
    (isGRing_of_finiteType_of_polynomial hpoly hR)



private lemma isRegularRingHom_of_algEquiv
    {R B C : Type*} [CommRing R] [CommRing B] [CommRing C]
    [Algebra R B] [Algebra R C] (e : B ≃ₐ[R] C)
    (h : IsRegularRingHom (algebraMap R B)) :
    IsRegularRingHom (algebraMap R C) := by
  rw [isRegularRingHom_algebraMap_iff] at h
  have : Module.Flat R B := RingHom.flat_algebraMap_iff.mp h.1
  have : Module.Flat R C := Module.Flat.of_linearEquiv e.symm.toLinearEquiv
  exact isRegularRingHom_algebraMap_of_geometricallyRegular_fibers fun p =>
    @Algebra.IsGeometricallyRegular.of_algEquiv _ _ _ _ _ _ _ _
    (h.2 p.asIdeal).2
    ({ (Algebra.TensorProduct.congr
        (AlgEquiv.refl : p.asIdeal.ResidueField ≃ₐ[R] _) e).toRingEquiv with
      commutes' := fun a => by simp })

private lemma isRegularRing_tensorProduct_field_of_isRegularRingHom
    {R K : Type u} {B : Type v} [CommRing R] [CommRing B] [Field K]
    [Algebra R B] [Algebra R K] [Algebra.EssFiniteType R K]
    (h : IsRegularRingHom (algebraMap R B)) : IsRegularRing (K ⊗[R] B) := by
  let p : Ideal R := RingHom.ker (algebraMap R K)
  have : p.IsPrime := RingHom.ker_isPrime (algebraMap R K)
  let f : p.ResidueField →+* K := Ideal.ResidueField.lift p (algebraMap R K) le_rfl
    (fun a ha => isUnit_iff_ne_zero.mpr ha)
  let : Algebra p.ResidueField K := f.toAlgebra
  have : IsScalarTower R p.ResidueField K := IsScalarTower.of_algebraMap_eq fun r =>
    (Ideal.ResidueField.lift_algebraMap p (algebraMap R K) le_rfl _ r).symm
  have : Algebra.EssFiniteType p.ResidueField K := .of_comp R p.ResidueField K
  have hgeom := ((isRegularRingHom_algebraMap_iff.mp h).2 p).2
  have : IsRegularRing (K ⊗[p.ResidueField] p.Fiber B) := hgeom.isRegularRing_tensorProduct K
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange R p.ResidueField K K B).toRingEquiv

set_option backward.isDefEq.respectTransparency false in
private lemma isRegularRingHom_uniformCompletion
    {A : Type*} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (h : IsRegularRingHom (algebraMap A (AdicCompletion (maximalIdeal A) A))) :
    letI : WithIdeal A := ⟨maximalIdeal A⟩
    IsRegularRingHom (UniformSpace.Completion.coeRingHom : A →+* _) := by
  let : WithIdeal A := ⟨maximalIdeal A⟩
  let : Algebra A (UniformSpace.Completion A) := UniformSpace.Completion.coeRingHom.toAlgebra
  let e : UniformSpace.Completion A ≃ₐ[A] AdicCompletion (maximalIdeal A) A :=
    { uniformCompletionRingEquiv (maximalIdeal A) with
      commutes' := uniformCompletionRingEquiv_coe (maximalIdeal A) }
  exact isRegularRingHom_of_algEquiv e.symm h

private lemma isRegularRingHom_completion_of_formallySmooth
    {R A : Type*} [CommRing R] [CommRing A] [Algebra R A]
    [IsNoetherianRing R] [IsLocalRing R] [IsNoetherianRing A] [IsLocalRing A]
    [IsLocalHom (algebraMap R A)] [Algebra.FormallySmooth R A]
    (hR : IsRegularRingHom (algebraMap R (AdicCompletion (maximalIdeal R) R))) :
    IsRegularRingHom
      (algebraMap R (AdicCompletion (maximalIdeal A) A)) := by
  let C := AdicCompletion (maximalIdeal A) A
  have : IsLocalHom (algebraMap R C) := by
    rw [IsScalarTower.algebraMap_eq R A C]
    infer_instance
  have hs : RingHom.FormallySmoothNAdic (algebraMap R C) (maximalIdeal C) := by
    rw [AdicCompletion.maximalIdeal_eq_map]
    exact formallySmoothNAdic_adicCompletion (maximalIdeal A)
      (IsNoetherian.noetherian _)
  exact ((isRegularRingHom_flat_geometricallyRegular_specialFiber_formallySmooth_tfae_0h7u
    (algebraMap R C) (isRegularRingHom_uniformCompletion hR)).out 4 1).mp hs

private lemma isGRing_polynomial
    (R : Type u) [CommRing R] (hR : IsGRing R) :
    IsGRing (Polynomial R) := by
  have : IsNoetherianRing R := hR.1
  refine ⟨inferInstance, fun q _ => ?_⟩
  let A := Localization.AtPrime q
  let p := q.under R
  let Rp := Localization.AtPrime p
  let : Algebra Rp A := Localization.AtPrime.algebraOfLiesOver p q
  have : IsScalarTower R Rp A := inferInstance
  have : IsLocalHom (algebraMap Rp A) := inferInstance
  have : Algebra.FormallySmooth R A := .comp R (Polynomial R) A
  have : Algebra.FormallySmooth Rp A := .of_restrictScalars R Rp A
  let C := AdicCompletion (maximalIdeal A) A
  let : Algebra A C := inferInstance
  have hreg : IsRegularRingHom (algebraMap Rp C) :=
    isRegularRingHom_completion_of_formallySmooth (hR.2 p)
  obtain ⟨D, hD⟩ := exists_derivation_adicCompletion_polynomial_eq_one R q
  apply isRegularRingHom_algebraMap_of_geometricallyRegular_fibers
  intro r
  constructor
  intro K _ _ _
  let L := r.asIdeal.ResidueField
  let : Algebra A K := ((algebraMap L K).comp (algebraMap A L)).toAlgebra
  have : IsScalarTower A L K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra (Polynomial R) K :=
    ((algebraMap A K).comp (algebraMap (Polynomial R) A)).toAlgebra
  have : IsScalarTower (Polynomial R) A K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra R K := ((algebraMap A K).comp (algebraMap R A)).toAlgebra
  have : IsScalarTower R A K := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra Rp K := ((algebraMap A K).comp (algebraMap Rp A)).toAlgebra
  have : IsScalarTower Rp A K := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R Rp K := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap A K (algebraMap R A a) =
      algebraMap A K (algebraMap Rp A (algebraMap R Rp a))
    exact congrArg (algebraMap A K) (IsScalarTower.algebraMap_apply R Rp A a)
  have : IsScalarTower R (Polynomial R) K := IsScalarTower.of_algebraMap_eq fun a => by
    show algebraMap A K (algebraMap R A a) =
      algebraMap A K (algebraMap (Polynomial R) A (algebraMap R (Polynomial R) a))
    exact congrArg (algebraMap A K) (IsScalarTower.algebraMap_apply R (Polynomial R) A a)
  have : Algebra.EssFiniteType A K := .comp A L K
  have : Algebra.EssFiniteType R K := .comp R A K
  have : Algebra.EssFiniteType Rp K := .of_comp R Rp K
  have : IsRegularRing (K ⊗[Rp] C) :=
    isRegularRing_tensorProduct_field_of_isRegularRingHom hreg
  have : TensorProduct.CompatibleSMul R Rp K C :=
    IsLocalization.tensorProduct_compatibleSMul p.primeCompl Rp K C
  have : IsRegularRing (K ⊗[R] C) := IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.equivOfCompatibleSMul R Rp K K C).toRingEquiv
  have : IsRegularRing (K ⊗[Polynomial R] C) :=
    isRegularRing_tensorProduct_polynomial_of_derivation R K C D hD
  have : TensorProduct.CompatibleSMul (Polynomial R) A K C :=
    IsLocalization.tensorProduct_compatibleSMul q.primeCompl A K C
  have : IsRegularRing (K ⊗[A] C) := IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.equivOfCompatibleSMul (Polynomial R) A K K C).symm.toRingEquiv
  exact IsRegularRing.of_ringEquiv
    (Algebra.TensorProduct.cancelBaseChange A L K K C).symm.toRingEquiv

/-- An algebra essentially of finite type over a G-ring is a G-ring. -/
@[stacks 07PV]
public theorem isGRing_of_essFiniteType
    {R : Type u} {S : Type v} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.EssFiniteType R S] (hR : IsGRing R) :
    IsGRing S :=
  isGRing_of_essFiniteType_of_polynomial isGRing_polynomial hR

end

end

/-! ### Basic examples of G-rings -/

section

section

universe u v w

open scoped TensorProduct

private theorem isGeometricallyRegular_of_bijective_algebraMap
    (k : Type u) (A : Type v) [Field k] [CommRing A] [Algebra k A]
    (h : Function.Bijective (algebraMap k A)) : Algebra.IsGeometricallyRegular k A := by
  let e : k ≃ₐ[k] A := AlgEquiv.ofBijective (Algebra.ofId k A) h
  exact ⟨fun K _ _ _ => IsRegularRing.of_ringEquiv
    ((Algebra.TensorProduct.rid k k K).symm.trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : K ≃ₐ[k] K) e)).toRingEquiv⟩

private theorem bijective_algebraMap_closedFiber_adicCompletion
    (R : Type u) [CommRing R] (m : Ideal R) [m.IsMaximal] (hm : m.FG) :
    Function.Bijective (algebraMap m.ResidueField (m.Fiber (AdicCompletion m R))) := by
  let B := AdicCompletion m R
  let e₀ : (R ⧸ m) ≃ₐ[R] m.ResidueField :=
    AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ m) m.ResidueField)
      m.bijective_algebraMap_quotient_residueField
  let e₁ : m.Fiber B ≃ₐ[R] B ⧸ m.map (algebraMap R B) :=
    (Algebra.TensorProduct.congr e₀.symm (AlgEquiv.refl : B ≃ₐ[R] B)).trans
      ((Algebra.TensorProduct.comm R (R ⧸ m) B).trans
        ((Algebra.TensorProduct.quotIdealMapEquivTensorQuot B m).symm.restrictScalars R))
  let e₂ : (B ⧸ m.map (algebraMap R B)) ≃ₐ[R] R ⧸ m :=
    (Ideal.quotientEquivAlgOfEq R (AdicCompletion.ker_evalOneₐ_eq_map m hm).symm).trans
      (Ideal.quotientKerAlgEquivOfSurjective (AdicCompletion.evalOneₐ_surjective m))
  let e : m.Fiber B ≃ₐ[R] m.ResidueField := e₁.trans (e₂.trans e₀)
  have he (x : m.ResidueField) : e (algebraMap m.ResidueField (m.Fiber B) x) = x := by
    obtain ⟨r, rfl⟩ := m.algebraMap_residueField_surjective x
    rw [← IsScalarTower.algebraMap_apply R m.ResidueField (m.Fiber B), e.commutes]
  exact ⟨fun x y hxy => (he x).symm.trans ((congrArg e hxy).trans (he y)),
    fun x => ⟨e x, e.injective (he (e x))⟩⟩

private theorem isRegularRingHom_adicCompletion_of_isDedekindDomain
    (R : Type u) [CommRing R] [IsDedekindDomain R] [IsLocalRing R] [CharZero R] :
    IsRegularRingHom
      (algebraMap R (AdicCompletion (IsLocalRing.maximalIdeal R) R)) := by
  let m := IsLocalRing.maximalIdeal R
  let B := AdicCompletion m R
  rw [isRegularRingHom_algebraMap_iff]
  refine ⟨RingHom.flat_algebraMap_iff.mpr inferInstance, fun p hp => ?_⟩
  by_cases hpm : p.IsMaximal
  · have hp_eq : p = m := IsLocalRing.eq_maximalIdeal hpm
    subst p
    have hb := bijective_algebraMap_closedFiber_adicCompletion R m
      (Ideal.fg_of_isNoetherianRing m)
    let e := AlgEquiv.ofBijective (Algebra.ofId m.ResidueField (m.Fiber B)) hb
    exact ⟨isNoetherianRing_of_ringEquiv _ e.toRingEquiv,
      isGeometricallyRegular_of_bijective_algebraMap _ _ hb⟩
  · have hp_eq : p = ⊥ := by_contra fun h => hpm (hp.isMaximal h)
    subst p
    have hnf : ¬ IsField R := by
      intro h
      let := h.toField
      exact hpm Ideal.bot_isMaximal
    have : IsDiscreteValuationRing R :=
      ((IsDiscreteValuationRing.TFAE R hnf).out 1 3).mpr
        (show IsDedekindDomain R from inferInstance)
    obtain ⟨hB, hDVR⟩ :=
      (isDiscreteValuationRing_iff_adicCompletion_maximalIdeal (A := R)).mp
        ⟨inferInstance, inferInstance⟩
    have : IsDomain B := hB
    have : IsDiscreteValuationRing B := hDVR
    let : Algebra B ((⊥ : Ideal R).Fiber B) := Algebra.TensorProduct.rightAlgebra
    have : IsRegularRing ((⊥ : Ideal R).Fiber B) :=
      IsRegularRing.of_isLocalization
        (Algebra.algebraMapSubmonoid B (nonZeroDivisors R)) ((⊥ : Ideal R).Fiber B)
    have : CharZero (⊥ : Ideal R).ResidueField := IsFractionRing.charZero_of_isFractionRing R
    exact ⟨inferInstance, Stacks.GRing.isGeometricallyRegular_of_perfectField _ _⟩

private theorem isGRing_of_field (K : Type u) [Field K] : IsGRing K := by
  have : IsPrecomplete (IsLocalRing.maximalIdeal K) K := by
    rw [IsLocalRing.maximalIdeal_eq_bot]
    infer_instance
  exact isGRing_of_isPrecomplete_maximalIdeal K

@[ega "IV 7.8.4" "partial"]
private theorem isGRing_of_isDedekindDomain_of_charZero
    (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)] :
    IsGRing R := by
  have : CharZero R := (algebraMap R (FractionRing R)).charZero
  refine ⟨inferInstance, fun p _ => ?_⟩
  have : CharZero (Localization.AtPrime p) :=
    charZero_of_injective_algebraMap (IsLocalization.injective _ p.primeCompl_le_nonZeroDivisors)
  exact isRegularRingHom_adicCompletion_of_isDedekindDomain (Localization.AtPrime p)

/-- Fields, Noetherian complete local rings, the integers, and Dedekind domains
whose fraction fields have characteristic zero are G-rings. Moreover, a finite-type algebra over
any G-ring is a G-ring. -/
@[stacks 07PX, sga "3 VIB 10.10" "more general"]
public theorem isGRing_basic_examples :
    (∀ (K : Type u) [Field K], IsGRing K) ∧
      (∀ (R : Type u) [CommRing R] [IsNoetherianRing R] [IsLocalRing R]
        [IsPrecomplete (IsLocalRing.maximalIdeal R) R], IsGRing R) ∧
      IsGRing ℤ ∧
      (∀ (R : Type u) [CommRing R] [IsDedekindDomain R] [CharZero (FractionRing R)],
        IsGRing R) ∧
      (∀ (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]
        [Algebra.FiniteType R S], IsGRing R → IsGRing S) :=
  ⟨isGRing_of_field, isGRing_of_isPrecomplete_maximalIdeal,
    isGRing_of_isDedekindDomain_of_charZero ℤ, isGRing_of_isDedekindDomain_of_charZero,
    fun _ _ _ _ _ _ hR => isGRing_of_essFiniteType hR⟩

end

end

/-! ### Henselian local rings as filtered colimits of G-rings -/

section

section

public section

open CategoryTheory CategoryTheory.Limits

universe u

private structure HenselizationData (R : Type u) [CommRing R] [IsLocalRing R] where
  carrier : Type u
  commRing : CommRing carrier
  algebra : Algebra R carrier
  localRing : IsLocalRing carrier
  localHom : IsLocalHom (letI := commRing; letI := algebra; algebraMap R carrier)
  henselian : HenselianLocalRing carrier
  indEtale : letI := commRing; letI := algebra
    (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R carrier)
  residueBijective : letI := commRing; letI := algebra; letI := localRing
    Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R carrier))

private noncomputable def chosenHenselization
    (R : Type u) [CommRing R] [IsLocalRing R] : HenselizationData R := by
  let h := IsLocalRing.exists_henselization R
  let Rh := Classical.choose h
  let h₁ := Classical.choose_spec h
  let iR := Classical.choose h₁
  let h₂ := Classical.choose_spec h₁
  let iA := Classical.choose h₂
  let h₃ := Classical.choose_spec h₂
  let iL := Classical.choose h₃
  let h₄ := Classical.choose_spec h₃
  let iLH := Classical.choose h₄
  let h₅ := Classical.choose_spec h₄
  exact ⟨Rh, iR, iA, iL, iLH, h₅.1, h₅.2.1, h₅.2.2.2⟩

private noncomputable abbrev Henselization (R : Type u) [CommRing R] [IsLocalRing R] :=
  (chosenHenselization R).carrier

private noncomputable local instance henselizationCommRing
    (R : Type u) [CommRing R] [IsLocalRing R] :
    CommRing (Henselization R) := (chosenHenselization R).commRing
private noncomputable local instance henselizationAlgebra
    (R : Type u) [CommRing R] [IsLocalRing R] :
    Algebra R (Henselization R) := (chosenHenselization R).algebra
@[local instance] private lemma henselizationLocalRing (R : Type u) [CommRing R] [IsLocalRing R] :
    IsLocalRing (Henselization R) := (chosenHenselization R).localRing
@[local instance] private lemma henselizationLocalHom (R : Type u) [CommRing R] [IsLocalRing R] :
    IsLocalHom (algebraMap R (Henselization R)) := (chosenHenselization R).localHom
@[local instance] private lemma henselizationHenselian (R : Type u) [CommRing R] [IsLocalRing R] :
    HenselianLocalRing (Henselization R) := (chosenHenselization R).henselian

private lemma henselization_indEtale (R : Type u) [CommRing R] [IsLocalRing R] :
    (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R (Henselization R)) :=
  (chosenHenselization R).indEtale

private lemma henselization_indEtale_lift (R : Type u) [CommRing R] [IsLocalRing R] :
    (CommAlgCat.etale.{u} R).ind.{u} (CommAlgCat.of R (ULift.{u} (Henselization R))) :=
  (CommAlgCat.etale R).ind.prop_of_iso
    (CommAlgCat.isoMk (ULift.algEquiv (R := R) (A := Henselization R)).symm)
    (henselization_indEtale R)

private lemma henselization_residue_surjective (R : Type u) [CommRing R] [IsLocalRing R] :
    Function.Surjective
      (IsLocalRing.ResidueField.map (algebraMap R (Henselization R))) :=
  (chosenHenselization R).residueBijective.2

@[local instance] private lemma henselizationIsHenselization
    (R : Type u) [CommRing R] [IsLocalRing R] :
    IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) (Henselization R) := by
  apply IsLocalRing.IsHenselization.of_ind_etale.{u, _, 0} inferInstance
    (henselization_indEtale R)
  let e := RingEquiv.ofBijective
    (IsLocalRing.ResidueField.map (algebraMap R (Henselization R)))
    (chosenHenselization R).residueBijective
  exact ⟨e, fun _ => rfl⟩

private noncomputable def henselizationMap
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] : Henselization R →+* Henselization S := by
  let a : R →+* Henselization S := (algebraMap S (Henselization S)).comp f
  letI : Algebra R (Henselization S) := a.toAlgebra
  letI : IsLocalHom (algebraMap R (Henselization S)) := RingHom.isLocalHom_comp _ _
  exact (HenselianLocalRing.indEtaleAlgHom
    (Sh := Henselization S) (henselization_indEtale_lift R)
    (henselization_residue_surjective R)).toRingHom

private lemma henselizationMap_comp_algebraMap
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] :
    (henselizationMap f).comp (algebraMap R (Henselization R)) =
      (algebraMap S (Henselization S)).comp f := by
  let a : R →+* Henselization S := (algebraMap S (Henselization S)).comp f
  let : Algebra R (Henselization S) := a.toAlgebra
  let : IsLocalHom (algebraMap R (Henselization S)) := RingHom.isLocalHom_comp _ _
  exact (HenselianLocalRing.indEtaleAlgHom
    (Sh := Henselization S) (henselization_indEtale_lift R)
    (henselization_residue_surjective R)).comp_algebraMap

private lemma henselizationMap_isLocal
    {R S : Type u} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]
    (f : R →+* S) [IsLocalHom f] : IsLocalHom (henselizationMap f) := by
  let a : R →+* Henselization S := (algebraMap S (Henselization S)).comp f
  let : Algebra R (Henselization S) := a.toAlgebra
  let : IsLocalHom (algebraMap R (Henselization S)) :=
    RingHom.isLocalHom_comp _ _
  let g : Henselization R →ₐ[R] Henselization S := HenselianLocalRing.indEtaleAlgHom
    (Sh := Henselization S) (henselization_indEtale_lift R)
    (henselization_residue_surjective R)
  let : IsLocalHom g := HenselianLocalRing.isLocalHom_indEtaleAlgHom
    (Sh := Henselization S) (henselization_indEtale_lift R)
    (henselization_residue_surjective R)
  exact isLocalHom_toRingHom g

/-- A local map into a henselian ring extends uniquely to the henselization. -/
private lemma existsUnique_henselization_lift
    {R B : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [HenselianLocalRing B]
    (f : R →+* B) [IsLocalHom f] :
    ∃! g : Henselization R →+* B,
      IsLocalHom g ∧ g.comp (algebraMap R (Henselization R)) = f := by
  let := f.toAlgebra
  let : IsLocalHom (algebraMap R B) := ‹IsLocalHom f›
  let g : Henselization R →ₐ[R] B := HenselianLocalRing.indEtaleAlgHom
    (Sh := B) (henselization_indEtale_lift R) (henselization_residue_surjective R)
  have hg : IsLocalHom g := HenselianLocalRing.isLocalHom_indEtaleAlgHom
    (Sh := B) (henselization_indEtale_lift R) (henselization_residue_surjective R)
  have hu : ∀ f : Henselization R →ₐ[R] B, IsLocalHom f → f = g :=
    HenselianLocalRing.indEtaleAlgHom_unique
      (Sh := B) (henselization_indEtale_lift R) (henselization_residue_surjective R)
  refine ⟨g.toRingHom, ⟨?_, g.comp_algebraMap⟩, ?_⟩
  · let := hg
    exact isLocalHom_toRingHom g
  · intro g' hg'
    let g'' : Henselization R →ₐ[R] B :=
      { toRingHom := g'
        commutes' := fun r => DFunLike.congr_fun hg'.2 r }
    exact congrArg AlgHom.toRingHom (hu g'' ⟨fun x hx => hg'.1.map_nonunit x hx⟩)

/-- Local maps out of a henselization are determined by their restriction to the base. -/
private lemma henselization_hom_ext
    {R B : Type u} [CommRing R] [IsLocalRing R] [CommRing B] [HenselianLocalRing B]
    (g h : Henselization R →+* B) [IsLocalHom g] [IsLocalHom h]
    (he : g.comp (algebraMap R (Henselization R)) =
      h.comp (algebraMap R (Henselization R))) : g = h := by
  have : IsLocalHom (g.comp (algebraMap R (Henselization R))) :=
    RingHom.isLocalHom_comp _ _
  exact (existsUnique_henselization_lift (g.comp (algebraMap R (Henselization R)))).unique
    ⟨inferInstance, rfl⟩ ⟨inferInstance, he.symm⟩

private lemma henselizationMap_id (R : Type u) [CommRing R] [IsLocalRing R] :
    henselizationMap (RingHom.id R) = RingHom.id (Henselization R) := by
  let := henselizationMap_isLocal (RingHom.id R)
  apply henselization_hom_ext
  rw [henselizationMap_comp_algebraMap]
  rfl

private lemma henselizationMap_comp
    {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    [IsLocalRing R] [IsLocalRing S] [IsLocalRing T]
    (f : R →+* S) (g : S →+* T) [IsLocalHom f] [IsLocalHom g] :
    (henselizationMap g).comp (henselizationMap f) = henselizationMap (g.comp f) := by
  let := henselizationMap_isLocal f
  let := henselizationMap_isLocal g
  let := henselizationMap_isLocal (g.comp f)
  have : IsLocalHom ((henselizationMap g).comp (henselizationMap f)) :=
    RingHom.isLocalHom_comp _ _
  apply henselization_hom_ext
  rw [RingHom.comp_assoc, henselizationMap_comp_algebraMap,
    ← RingHom.comp_assoc, henselizationMap_comp_algebraMap,
    henselizationMap_comp_algebraMap, RingHom.comp_assoc]

/-- Henselization preserves the G-ring property. -/
private lemma henselization_isGRing (R : Type u) [CommRing R] [IsLocalRing R]
    (hR : IsGRing R) : IsGRing (Henselization R) := by
  let κsep := SeparableClosure (IsLocalRing.ResidueField R)
  obtain ⟨Rsh, iR, iL, iA, iAh, iT, iH, hh, _, hi, _, he⟩ :=
    IsLocalRing.exists_strictHenselization R (Henselization R)
      (henselization_indEtale R) (henselization_residue_surjective R) κsep
  let : IsLocalRing.IsHenselization R κsep Rsh :=
    IsLocalRing.IsHenselization.of_ind_etale.{u, _, 0} hh hi he
  exact (isGRing_henselization_and_strictHenselization
    R (Henselization R) Rsh κsep hR).1

@[local instance] private lemma henselization_directedSystem
    {J : Type u} [Preorder J]
    (G : J → Type u) [∀ j, CommRing (G j)] [∀ j, IsLocalRing (G j)]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    [∀ i j h, IsLocalHom (f i j h)] :
    DirectedSystem (fun j => Henselization (G j))
      (fun i j h => (henselizationMap (f i j h) : Henselization (G i) → Henselization (G j))) :=
    { map_self := fun {i} x => by
        have hi : f i i le_rfl = RingHom.id (G i) := by
          ext y
          exact DirectedSystem.map_self (f := fun i j h => (f i j h : G i → G j)) y
        show henselizationMap (f i i le_rfl) x = x
        simp only [hi, henselizationMap_id, RingHom.id_apply]
      map_map := fun {k j i} hij hjk x => by
        have ht : (f j k hjk).comp (f i j hij) = f i k (hij.trans hjk) := by
          ext y
          exact DirectedSystem.map_map (f := fun i j h => (f i j h : G i → G j)) hij hjk y
        show ((henselizationMap (f j k hjk)).comp
          (henselizationMap (f i j hij))) x = _
        rw [henselizationMap_comp]
        simp only [ht] }

/-- Henselizing the stages of a directed presentation of a henselian local ring preserves
its colimit. -/
private lemma henselization_directLimit_equiv
    {J : Type u} [Preorder J] [IsDirected J (· ≤ ·)] [Nonempty J]
    (G : J → Type u) [∀ j, CommRing (G j)] [∀ j, IsLocalRing (G j)]
    (f : ∀ i j, i ≤ j → G i →+* G j)
    [DirectedSystem G (fun i j h => (f i j h : G i → G j))]
    (hf : ∀ i j h, IsLocalHom (f i j h))
    (A : Type u) [CommRing A] [HenselianLocalRing A]
    (g : ∀ j, G j →+* A) (hg : ∀ j, IsLocalHom (g j))
    (e : Ring.DirectLimit G (fun i j h => (f i j h : G i → G j)) ≃+* A)
    (he : ∀ j x, e (Ring.DirectLimit.of G
      (fun i j h => (f i j h : G i → G j)) j x) = g j x) :
    letI : ∀ i j h, IsLocalHom (f i j h) := hf
    let H := fun j => Henselization (G j)
    let fh := fun i j h => henselizationMap (f i j h)
    Nonempty (Ring.DirectLimit H (fun i j h => (fh i j h : H i → H j)) ≃+* A) := by
  let : ∀ i j h, IsLocalHom (f i j h) := hf
  let : ∀ j, IsLocalHom (g j) := hg
  let H := fun j => Henselization (G j)
  let fh := fun i j h => henselizationMap (f i j h)
  let B := Ring.DirectLimit H (fun i j h => (fh i j h : H i → H j))
  let ofh (j : J) : H j →+* B := Ring.DirectLimit.of H
    (fun i j h => (fh i j h : H i → H j)) j
  have hfh : ∀ i j h, IsLocalHom (fh i j h) :=
    fun i j h => henselizationMap_isLocal (f i j h)
  let : HenselianLocalRing B := part2_henselian H fh hfh (fun j => inferInstance)
  let : ∀ j, IsLocalHom (ofh j) := part1_of_isLocalHom H fh hfh
  choose gh hgh _ using fun j => existsUnique_henselization_lift (g j)
  let : ∀ j, IsLocalHom (gh j) := fun j => (hgh j).1
  have hgcompat (i j : J) (h : i ≤ j) : (g j).comp (f i j h) = g i := by
    ext x
    show g j (f i j h x) = g i x
    rw [← he, ← he, Ring.DirectLimit.of_f]
  have hghcompat (i j : J) (h : i ≤ j) : (gh j).comp (fh i j h) = gh i := by
    let := hfh i j h
    have : IsLocalHom ((gh j).comp (fh i j h)) := RingHom.isLocalHom_comp _ _
    apply henselization_hom_ext
    rw [RingHom.comp_assoc, henselizationMap_comp_algebraMap,
      ← RingHom.comp_assoc, (hgh j).2, (hgh i).2, hgcompat]
  let β : B →+* A := Ring.DirectLimit.lift H
    (fun i j h => (fh i j h : H i → H j)) A gh
    (fun i j h x => DFunLike.congr_fun (hghcompat i j h) x)
  have hβ (j : J) (x : H j) : β (ofh j x) = gh j x := Ring.DirectLimit.lift_of _ _ _ _ _
  let η (j : J) := algebraMap (G j) (H j)
  have hηcompat (i j : J) (h : i ≤ j) :
      ((ofh j).comp (η j)).comp (f i j h) = (ofh i).comp (η i) := by
    rw [RingHom.comp_assoc, ← henselizationMap_comp_algebraMap, ← RingHom.comp_assoc]
    have ho : (ofh j).comp (fh i j h) = ofh i := by
      ext x
      exact Ring.DirectLimit.of_f
        (G := H) (f := fun i j h => (fh i j h : H i → H j)) h x
    rw [ho]
  let α₀ := Ring.DirectLimit.lift G (fun i j h => (f i j h : G i → G j)) B
    (fun j => (ofh j).comp (η j))
    (fun i j h x => DFunLike.congr_fun (hηcompat i j h) x)
  let α : A →+* B := α₀.comp e.symm.toRingHom
  have hα (j : J) (x : G j) : α (g j x) = ofh j (η j x) := by
    rw [← he]
    show α₀ (e.symm (e _)) = _
    rw [e.symm_apply_apply]
    exact Ring.DirectLimit.lift_of _ _ _ _ _
  have hgrep (a : A) : ∃ j x, g j x = a := by
    obtain ⟨j, x, hx⟩ := Ring.DirectLimit.exists_of (e.symm a)
    exact ⟨j, x, (he j x).symm.trans ((congrArg e hx).trans (e.apply_symm_apply a))⟩
  let : IsLocalHom α := ⟨fun a ha => by
    obtain ⟨j, x, rfl⟩ := hgrep a
    rw [hα] at ha
    exact (IsUnit.of_map (η j) x (IsUnit.of_map (ofh j) (η j x) ha)).map (g j)⟩
  have hβα (a : A) : β (α a) = a := by
    obtain ⟨j, x, rfl⟩ := hgrep a
    rw [hα, hβ]
    exact DFunLike.congr_fun (hgh j).2 x
  have hαgh (j : J) : α.comp (gh j) = ofh j := by
    have : IsLocalHom (α.comp (gh j)) := RingHom.isLocalHom_comp _ _
    apply henselization_hom_ext
    rw [RingHom.comp_assoc, (hgh j).2]
    ext x
    exact hα j x
  have hαβ (b : B) : α (β b) = b := by
    obtain ⟨j, x, rfl⟩ := Ring.DirectLimit.exists_of b
    rw [hβ]
    exact DFunLike.congr_fun (hαgh j) x
  exact ⟨{ β with invFun := α, left_inv := hαβ, right_inv := hβα }⟩

/-- A henselian local ring is a filtered colimit of henselian local G-rings
with local transition maps. -/
@[stacks 0A41, ega "IV 18.6.14" "(iii)"]
public theorem exists_filteredColimit_henselianLocalGRing
    (A : Type u) [CommRing A] [HenselianLocalRing A] :
    ∃ (J : Type u) (_ : SmallCategory J) (_ : IsFiltered J)
      (F : J ⥤ CommRingCat.{u}) (c : Cocone F) (_ : IsColimit c),
      (∀ j, HenselianLocalRing (F.obj j) ∧ IsGRing (F.obj j)) ∧
        (∀ ⦃i j⦄ (f : i ⟶ j), IsLocalHom (F.map f).hom) ∧
        Nonempty (c.pt ≅ CommRingCat.of A) := by
  let G := Stacks.EssentialFiniteness.LocalRingColimit.Robj A
  let f := fun i j h => Stacks.EssentialFiniteness.LocalRingColimit.fR A (s := i) (t := j) h
  let : DirectedSystem G (fun i j h => (f i j h : G i → G j)) :=
    Stacks.EssentialFiniteness.LocalRingColimit.fR_directedSystem A
  let : ∀ i j h, IsLocalHom (f i j h) := fun i j h =>
    Stacks.EssentialFiniteness.LocalRingColimit.fR_isLocalHom A h
  let H := fun j => Henselization (G j)
  let fh := fun i j h => henselizationMap (f i j h)
  let F : Finset A ⥤ CommRingCat.{u} :=
    { obj := fun s => CommRingCat.of (H s)
      map := fun h => CommRingCat.ofHom (fh _ _ h.le)
      map_id := fun i => by
        ext x
        exact DirectedSystem.map_self (f := fun i j h => (fh i j h : H i → H j)) x
      map_comp := fun a b => by
        ext x
        exact (DirectedSystem.map_map (f := fun i j h => (fh i j h : H i → H j))
          a.le b.le x).symm }
  let c : Cocone F :=
    { pt := CommRingCat.of (Ring.DirectLimit H (fun i j h => (fh i j h : H i → H j)))
      ι :=
        { app := fun s => CommRingCat.ofHom
            (Ring.DirectLimit.of H (fun i j h => (fh i j h : H i → H j)) s)
          naturality := fun _ _ a => by
            ext x
            exact Ring.DirectLimit.of_f
              (f := fun i j h => (fh i j h : H i → H j)) a.le x } }
  have hc : IsColimit c :=
    { desc := fun t => CommRingCat.ofHom <|
        Ring.DirectLimit.lift H (fun i j h => (fh i j h : H i → H j))
          t.pt (fun s => (t.ι.app s).hom)
          (fun _ _ h x => congr($(t.w (homOfLE h)).hom x))
      fac := fun t s => by
        ext x
        exact Ring.DirectLimit.lift_of t.pt (fun s => (t.ι.app s).hom)
          (fun _ _ h x => congr($(t.w (homOfLE h)).hom x)) s x
      uniq := fun t m hm => by
        refine CommRingCat.hom_ext (RingHom.ext fun x => ?_)
        obtain ⟨s, z, hz⟩ := Ring.DirectLimit.exists_of
          (G := H) (f := fun i j h => (fh i j h : H i → H j)) x
        rw [← hz]
        exact (congr($(hm s).hom z)).trans
          (Ring.DirectLimit.lift_of t.pt (fun s => (t.ι.app s).hom)
            (fun _ _ h x => congr($(t.w (homOfLE h)).hom x)) s z).symm }
  refine ⟨Finset A, inferInstance, inferInstance, F, c, hc, ?_,
    fun i j a => henselizationMap_isLocal (f i j a.le), ?_⟩
  · intro s
    refine ⟨inferInstance, henselization_isGRing (G s) ?_⟩
    let : Algebra ℤ (G s) := Ring.toIntAlgebra _
    have : Algebra.EssFiniteType ℤ (G s) :=
      Stacks.EssentialFiniteness.LocalRingColimit.Robj_essFiniteType A s
    exact isGRing_of_essFiniteType
      (R := ℤ) (S := G s) (isGRing_basic_examples.{u, u}).2.2.1
  · obtain ⟨e⟩ := henselization_directLimit_equiv G f
      (fun i j h => Stacks.EssentialFiniteness.LocalRingColimit.fR_isLocalHom A h) A
        (Stacks.EssentialFiniteness.LocalRingColimit.gR A)
      (Stacks.EssentialFiniteness.LocalRingColimit.gR_isLocalHom A)
        (Stacks.EssentialFiniteness.LocalRingColimit.colimEquiv A)
          (Stacks.EssentialFiniteness.LocalRingColimit.Phi_of A)
    exact ⟨e.toCommRingCatIso⟩

end

end

end

end
