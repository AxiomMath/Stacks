module

public import Mathlib.CategoryTheory.Presentable.Directed
public import Mathlib.FieldTheory.CardinalEmb
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import Mathlib.FieldTheory.SeparableDegree
public import Mathlib.RingTheory.Adjoin.Field
public import Mathlib.RingTheory.Etale.QuasiFinite
public import Mathlib.RingTheory.Ideal.Quotient.Basic
public import Mathlib.RingTheory.Localization.FractionRing
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.Spectrum.Maximal.Basic
public import Mathlib.RingTheory.Spectrum.Prime.Homeomorph
public import Mathlib.RingTheory.TensorProduct.Basic
public import Mathlib.RingTheory.TensorProduct.Maps
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Branches.Defs
public import StacksFrontier.RingTheory.Branches.MinimalPrimes
public import StacksFrontier.RingTheory.GeometricallyNormal.TFAE
public import StacksFrontier.RingTheory.Henselian.Henselization.Basic
public import StacksFrontier.RingTheory.Henselian.Henselization.Defs
public import StacksFrontier.RingTheory.Henselian.IntegralDomain
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Smooth.Normal
public import StacksFrontier.RingTheory.WeaklyEtale.Descent

/-!
# Branch correspondences via henselization and strict henselization

Let `A` be a local ring, let `A'` be the integral closure of `A` in the total ring of fractions
of its reduction, and let `Aʰ`, respectively `Aˢʰ`, be a henselization, respectively a strict
henselization, of `A`.

When `A` has finitely many minimal primes, contraction from `A' ⊗[A] Aʰ` is bijective on maximal
ideals toward `A'` and on minimal primes toward `Aʰ`, and minimal and maximal primes of the
tensor product determine one another by containment. After strict henselization the fibre of
`Spec (A' ⊗[A] Aˢʰ) → Spec A'` over a maximal ideal `m'` is canonically identified with the
embeddings of the residue field of `m'` into a chosen algebraic closure of the residue field of
`A`.

## Main results

* `flat_of_ind_etale`, `flat_of_isHenselization`: ind-étale algebras, and hence henselizations,
  are flat.
* `geometric_branches_of_strictHenselization` (Stacks 0C25): the residue-field description of
  the fibres, the bijection on minimal primes, and the incidence correspondence between minimal
  and maximal primes after strict henselization.
* `bijective_maximalIdeals_and_minimalPrimes_of_henselization` (Stacks 0C24): the two
  contraction bijections and the incidence correspondence between minimal and maximal primes of
  `(A')ʰ`.

## Implementation notes

The reduction of `A` is represented by `A ⧸ nilradical A`, its total ring of fractions by
`FractionRing (A ⧸ nilradical A)`, and `A'` by the corresponding `integralClosure`. A
henselization is represented abstractly by an `A`-algebra satisfying
`IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) Aʰ`, and a strict henselization by
the same predicate with a separable closure `ksep` of the residue field in place of the residue
field. Bijections on prime ideals are expressed by `Set.BijOn` for contraction, which includes
the assertion that contraction lands in the indicated class of ideals.

Maximal ideals are compared through the closed fibre, and minimal primes through a common
injective localization after flat base change. Normality gives a unique minimal prime below each
maximal ideal, and it is obtained by expressing the normalization as a finite product of normal
domains and the henselization as a filtered colimit of étale algebras.

The fibre over a maximal ideal is the inverse image of a point under contraction on prime
spectra. The canonical parametrization sends an embedding `σ` to the kernel of the unique map on
the tensor product whose value on `a ⊗ b` is `σ(a mod m')` times the image in `kbar` of the
residue of `b`.

Flatness of a henselization over its base is not part of
`StacksFrontier.RingTheory.Henselian.Henselization.Basic`; it is recovered here from the ind-étale
condition through Stacks 092N, which makes a filtered colimit of étale algebras weakly étale and
hence flat.

## References

* [The Stacks Project, Tag 0C24](https://stacks.math.columbia.edu/tag/0C24)
* [The Stacks Project, Tag 0C25](https://stacks.math.columbia.edu/tag/0C25)
-/

@[expose] public section

universe u u' v w

section GeometricBranches

open Topology
open scoped TensorProduct

/-- The structure map of a henselization is local. -/
private theorem isLocalHom_of_isHenselization
    {R : Type u} {Rh : Type v} [CommRing R] [IsLocalRing R] [CommRing Rh] [IsLocalRing Rh]
    [Algebra R Rh]
    [IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) Rh] :
    IsLocalHom (algebraMap R Rh) :=
  IsLocalRing.IsHenselization.isLocalHom (L := IsLocalRing.ResidueField R)

/-- A henselization has the same residue field as the original local ring. -/
private theorem residueFieldMap_bijective_of_isHenselization
    {R : Type u} {Rh : Type v} [CommRing R] [IsLocalRing R] [CommRing Rh] [IsLocalRing Rh]
    [Algebra R Rh]
    [IsLocalRing.IsHenselization R (IsLocalRing.ResidueField R) Rh] :
    letI : IsLocalHom (algebraMap R Rh) := isLocalHom_of_isHenselization
    Function.Bijective (IsLocalRing.ResidueField.map (algebraMap R Rh)) := by
  let : IsLocalHom (algebraMap R Rh) := isLocalHom_of_isHenselization
  obtain ⟨e, he⟩ :=
    IsLocalRing.IsHenselization.exists_residueFieldEquiv
      (R := R) (L := IsLocalRing.ResidueField R) (Rh := Rh)
  have hmap : IsLocalRing.ResidueField.map (algebraMap R Rh) = e.toRingHom := by
    apply RingHom.ext
    intro x
    obtain ⟨r, rfl⟩ := IsLocalRing.residue_surjective x
    simpa using (he r).symm
  rw [hmap]
  exact e.bijective

set_option backward.isDefEq.respectTransparency false

/-- Every prime in the base change of an integral algebra to a henselian local ring lies in
exactly one maximal ideal. -/
private theorem existsUnique_maximal_of_integral_tensorProduct
    (R : Type u) (Rh : Type v) (B : Type w) [CommRing R] [CommRing Rh]
    [HenselianLocalRing Rh] [CommRing B] [Algebra R Rh] [Algebra R B]
    [Algebra.IsIntegral R B]
    (q : Ideal (B ⊗[R] Rh)) (hq : q.IsPrime) :
    ∃! m : Ideal (B ⊗[R] Rh), m.IsMaximal ∧ q ≤ m := by
  let : Algebra Rh (B ⊗[R] Rh) := Algebra.TensorProduct.rightAlgebra
  let : Algebra.IsIntegral Rh (B ⊗[R] Rh) := integral_tensorProduct_right R B Rh
  exact existsUnique_maximal_of_integral_henselian Rh (B ⊗[R] Rh) q hq

/-- Contraction from the base change of the integral closure to the integral closure is
bijective on maximal ideals. -/
private theorem bijOn_maximalIdeals_integralClosure_henselization
    (A : Type u) (Ah : Type v) [CommRing A] [IsLocalRing A] [CommRing Ah] [IsLocalRing Ah]
    [Algebra A Ah]
    [IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) Ah] :
    let A' := integralClosure A (FractionRing (A ⧸ nilradical A))
    Set.BijOn
      (Ideal.comap (Algebra.TensorProduct.includeLeftRingHom : A' →+* A' ⊗[A] Ah))
      {P : Ideal (A' ⊗[A] Ah) | P.IsMaximal} {p : Ideal A' | p.IsMaximal} := by
  let : IsLocalHom (algebraMap A Ah) := isLocalHom_of_isHenselization
  exact bijOn_maximalIdeals_tensorProduct A Ah
    (integralClosure A (FractionRing (A ⧸ nilradical A)))
    residueFieldMap_bijective_of_isHenselization

/-- Every minimal prime of the base changed normalization is contained in a unique maximal
ideal. This is the first incidence assertion of the branch correspondence. -/
private theorem existsUnique_maximal_integralClosure_henselization
    (A : Type u) (Ah : Type v) (L : Type w) [CommRing A] [IsLocalRing A] [CommRing Ah]
    [IsLocalRing Ah] [Algebra A Ah] [Field L] [Algebra (IsLocalRing.ResidueField A) L]
    [IsLocalRing.IsHenselization A L Ah]
    (q : Ideal (integralClosure A (FractionRing (A ⧸ nilradical A)) ⊗[A] Ah))
    (hq : q ∈ minimalPrimes
      (integralClosure A (FractionRing (A ⧸ nilradical A)) ⊗[A] Ah)) :
    ∃! m : Ideal (integralClosure A (FractionRing (A ⧸ nilradical A)) ⊗[A] Ah),
      m.IsMaximal ∧ q ≤ m := by
  let : HenselianLocalRing Ah := IsLocalRing.IsHenselization.henselian A L
  exact existsUnique_maximal_of_integral_tensorProduct A Ah
    (integralClosure A (FractionRing (A ⧸ nilradical A))) q hq.isPrime

open CategoryTheory CategoryTheory.Limits

/-- An ind-étale algebra is flat: it is a filtered colimit of étale algebras, and by
Stacks 092N such a colimit is weakly étale, hence flat. -/
theorem flat_of_ind_etale (R : Type u) (S : Type v) [CommRing R] [CommRing S]
    [Algebra R S] (hind : (CommAlgCat.etale.{v} R).ind.{v} (CommAlgCat.of R S)) :
    Module.Flat R S := by
  obtain ⟨J, _, _, pres, hpres⟩ := hind
  have hwe := (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, v, v} R).2.2
    J pres.diag pres.cocone pres.isColimit (fun j => by
      have : Algebra.Etale R (pres.diag.obj j) := hpres j
      exact (weaklyEtale_of_isLocalization_etale_filteredColimit.{u, v, v} R).2.1
        (pres.diag.obj j))
  exact hwe.flat

/-- A henselization is flat over its base, being ind-étale. The ind-étale condition is recorded
for `ULift.{u} Rh`, whose flatness transports to `Rh`. -/
theorem flat_of_isHenselization {R : Type u} (L : Type v) {Rh : Type w}
    [CommRing R] [IsLocalRing R] [Field L] [Algebra (IsLocalRing.ResidueField R) L]
    [CommRing Rh] [IsLocalRing Rh] [Algebra R Rh] [IsLocalRing.IsHenselization R L Rh] :
    Module.Flat R Rh :=
  have : Module.Flat R (ULift.{u} Rh) :=
    flat_of_ind_etale R (ULift.{u} Rh) (IsLocalRing.IsHenselization.ind_etale (L := L))
  Module.Flat.of_linearEquiv (ULift.algEquiv : ULift.{u} Rh ≃ₐ[R] Rh).symm.toLinearEquiv

private theorem isNormalRing_integralClosure_tensorProduct_henselization
    (A : Type u) (Ah : Type v) (L : Type w) [CommRing A] [IsLocalRing A] [CommRing Ah]
    [IsLocalRing Ah] [Algebra A Ah] [Field L] [Algebra (IsLocalRing.ResidueField A) L]
    [IsLocalRing.IsHenselization A L Ah] (hmin : (minimalPrimes A).Finite) :
    IsNormalRing (integralClosure A (FractionRing (A ⧸ nilradical A)) ⊗[A] Ah) := by
  let N := integralClosure A (FractionRing (A ⧸ nilradical A))
  have hN := isNormalRing_integralClosure_fractionRing_reduction A hmin
  have h := isNormalRing_tensorProduct_of_ind_etale N hN
    (IsLocalRing.IsHenselization.ind_etale (R := A) (L := L) (Rh := Ah))
  exact IsNormalRing.congr
    (Algebra.TensorProduct.congr (AlgEquiv.refl : N ≃ₐ[N] N)
      (ULift.algEquiv : ULift.{u} Ah ≃ₐ[A] Ah)).toRingEquiv h

/-- The points of an algebraic algebra over an algebraically closed field are its
algebra-valued points. -/
private noncomputable def algHomEquivPrimeSpectrum_of_isAlgClosed
    (K : Type u) (R : Type v) [Field K] [CommRing R] [Algebra K R]
    [Algebra.IsIntegral K R] [IsAlgClosed K] :
    (R →ₐ[K] K) ≃ PrimeSpectrum R where
  toFun f := ⟨RingHom.ker f, RingHom.ker_isPrime f⟩
  invFun p :=
    (AlgEquiv.ofBijective (Algebra.ofId K (R ⧸ p.asIdeal))
      (IsAlgClosed.ringHom_bijective_of_isIntegral _
        (fun x => Algebra.IsIntegral.isIntegral x))).symm.toAlgHom.comp
      (Ideal.Quotient.mkₐ K p.asIdeal)
  left_inv f := by
    ext
    dsimp
    have : (RingHom.ker f).IsPrime := RingHom.ker_isPrime f
    apply (AlgEquiv.ofBijective (Algebra.ofId K (R ⧸ RingHom.ker f))
      (IsAlgClosed.ringHom_bijective_of_isIntegral _
        (fun x => Algebra.IsIntegral.isIntegral x))).injective
    rw [AlgEquiv.apply_symm_apply, AlgEquiv.coe_ofBijective, Algebra.ofId_apply,
      IsScalarTower.algebraMap_apply K R]
    simp [-Ideal.Quotient.mk_algebraMap, Ideal.Quotient.mk_eq_mk_iff_sub_mem]
  right_inv p := by
    ext : 1
    dsimp
    rw [← AlgHom.comap_ker, ← RingHom.ker_coe_toRingHom, AlgEquiv.toAlgHom_toRingHom,
      AlgHom.ker_coe_equiv, ← RingHom.ker_eq_comap_bot, ← RingHom.ker_coe_toRingHom,
      Ideal.Quotient.mkₐ_ker]

/-- Embeddings of an algebraic field extension in an algebraic closure parametrize
the points after extension to a separable closure. -/
private noncomputable def algHomEquivPrimeSpectrum_tensorProduct_sepClosure
    (F : Type u) (K : Type v) (L : Type w) (Omega : Type*)
    [Field F] [Field K] [Field L] [Field Omega]
    [Algebra F K] [Algebra F L] [Algebra F Omega] [Algebra L Omega]
    [IsScalarTower F L Omega] [Algebra.IsIntegral F K]
    [IsSepClosed L] [IsAlgClosed Omega] [Algebra.IsAlgebraic F Omega] :
    (K →ₐ[F] Omega) ≃ PrimeSpectrum (K ⊗[F] L) := by
  letI : Algebra.IsIntegral L Omega :=
    @Algebra.IsIntegral.tower_top F L Omega _ _ _ _ _ _ _ inferInstance
  letI : IsPurelyInseparable L Omega := inferInstance
  letI : Algebra.IsIntegral Omega (Omega ⊗[F] K) :=
    Algebra.IsIntegral.tensorProduct F Omega K
  exact (Algebra.TensorProduct.liftEquivRight F Omega K Omega).trans
    ((algHomEquivPrimeSpectrum_of_isAlgClosed Omega (Omega ⊗[F] K)).trans
      ((Equiv.ofBijective _
        (PrimeSpectrum.isHomeomorph_comap_tensorProductMap_of_isPurelyInseparable
          L F K Omega).bijective).trans
        (PrimeSpectrum.homeomorphOfRingEquiv
          (Algebra.TensorProduct.comm F L K).toRingEquiv).toEquiv))

/-- The point attached to an embedding `σ` is the kernel of `σ ⊗ 1`. -/
private theorem algHomEquivPrimeSpectrum_tensorProduct_sepClosure_asIdeal
    (F : Type u) (K : Type v) (L : Type w) (Omega : Type*)
    [Field F] [Field K] [Field L] [Field Omega]
    [Algebra F K] [Algebra F L] [Algebra F Omega] [Algebra L Omega]
    [IsScalarTower F L Omega] [Algebra.IsIntegral F K]
    [IsSepClosed L] [IsAlgClosed Omega] [Algebra.IsAlgebraic F Omega] (σ : K →ₐ[F] Omega) :
    (algHomEquivPrimeSpectrum_tensorProduct_sepClosure F K L Omega σ).asIdeal =
      RingHom.ker (Algebra.TensorProduct.lift σ (IsScalarTower.toAlgHom F L Omega)
        (fun _ _ => .all _ _)) := by
  have key : ((Algebra.TensorProduct.lift (Algebra.ofId Omega Omega) σ (fun _ _ ↦ .all _
    _)).toRingHom.comp
      ((Algebra.TensorProduct.map (Algebra.ofId L Omega) (AlgHom.id F K)).toRingHom.comp
        (Algebra.TensorProduct.comm F L K).symm.toRingEquiv.toRingHom)) =
      (Algebra.TensorProduct.lift σ (IsScalarTower.toAlgHom F L Omega)
        (fun _ _ => .all _ _)).toRingHom := by
    apply Algebra.TensorProduct.ringHom_ext <;> ext <;> simp
  ext x
  have hx := DFunLike.congr_fun key x
  show _ = 0 ↔ _ = 0
  exact Iff.of_eq (congrArg (· = 0) hx)

private theorem quotientMap_isIntegral_of_eq_comap
    {R : Type u} {S : Type v} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : f.IsIntegral) (I : Ideal R) (J : Ideal S)
    (h : I = J.comap f) :
    (Ideal.quotientMap J f (le_of_eq h)).IsIntegral := by
  let e : R ⧸ I ≃+* R ⧸ J.comap f := Ideal.quotEquivOfEq h
  let q : (R ⧸ J.comap f) →+* (S ⧸ J) := Ideal.quotientMap J f le_rfl
  have hq : q.IsIntegral := RingHom.IsIntegral.quotient f hf
  have he : e.toRingHom.IsIntegral := e.toRingHom.isIntegral_of_surjective e.surjective
  have hc : Ideal.quotientMap J f (le_of_eq h) = q.comp e.toRingHom := by
    ext x
    simp [q, e, Ideal.quotEquivOfEq_mk]
  rw [hc]
  exact RingHom.IsIntegral.trans _ _ he hq

open IsLocalRing in
/-- For an integral `A`-algebra `B` and a local `A`-algebra `C` whose maximal ideal is extended
from `A` and whose residue field is a separably closed extension of that of `A`, the fibre of
`Spec (B ⊗[A] C) → Spec B` over a maximal ideal `m'` is parametrized by the embeddings of the
residue field of `m'` into an algebraic closure, via kernels of the induced maps. -/
private theorem fibre_tensorProduct_integral
    (A : Type u) (B : Type*) (C : Type u') (ksep : Type v) (kbar : Type w)
    [CommRing A] [IsLocalRing A] [CommRing B] [Algebra A B] [Algebra.IsIntegral A B]
    [CommRing C] [IsLocalRing C] [Algebra A C]
    [Field ksep] [Algebra (ResidueField A) ksep] [IsSepClosed ksep]
    [Field kbar] [Algebra (ResidueField A) kbar] [IsAlgClosure (ResidueField A) kbar]
    [Algebra ksep kbar] [IsScalarTower (ResidueField A) ksep kbar]
    (hC : (maximalIdeal A).map (algebraMap A C) = maximalIdeal C)
    (e : ksep ≃+* ResidueField C)
    (he : ∀ x : A,
      e (algebraMap (ResidueField A) ksep (residue A x)) = residue C (algebraMap A C x))
    (m' : MaximalSpectrum B) :
      ∃ h : maximalIdeal A = m'.asIdeal.comap (algebraMap A B),
        let f := Ideal.quotientMap m'.asIdeal (algebraMap A B) (le_of_eq h)
        f.IsIntegral ∧
          ∃ E : ({σ : (B ⧸ m'.asIdeal) →+* kbar //
                    σ.comp f = algebraMap (ResidueField A) kbar} ≃
                  {q : PrimeSpectrum (B ⊗[A] C) //
                    PrimeSpectrum.comap
                      (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C) q =
                        m'.toPrimeSpectrum}),
            ∀ σ, ∃ φ : B ⊗[A] C →+* kbar,
              (∀ (a : B) (b : C),
                  φ (a ⊗ₜ[A] b) =
                    σ.1 (Ideal.Quotient.mk m'.asIdeal a) *
                      algebraMap ksep kbar (e.symm (residue C b))) ∧
                (E σ).1.asIdeal = RingHom.ker φ ∧
                ∀ ψ : B ⊗[A] C →+* kbar,
                  (∀ (a : B) (b : C),
                    ψ (a ⊗ₜ[A] b) =
                      σ.1 (Ideal.Quotient.mk m'.asIdeal a) *
                        algebraMap ksep kbar (e.symm (residue C b))) →
                  ψ = φ := by
  have : m'.asIdeal.IsMaximal := m'.isMaximal
  have hm : maximalIdeal A = m'.asIdeal.comap (algebraMap A B) :=
    (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := A) m'.asIdeal)).symm
  have hf_integral :
      (Ideal.quotientMap m'.asIdeal (algebraMap A B) (le_of_eq hm)).IsIntegral :=
    quotientMap_isIntegral_of_eq_comap (algebraMap A B)
      (algebraMap_isIntegral_iff.mpr inferInstance) _ _ hm
  refine ⟨hm, hf_integral, ?_⟩
  let F := ResidueField A
  let K := B ⧸ m'.asIdeal
  let : Field K := Ideal.Quotient.field m'.asIdeal
  let f : F →+* K := Ideal.quotientMap m'.asIdeal (algebraMap A B) (le_of_eq hm)
  let : Algebra F K := f.toAlgebra
  have : IsScalarTower A F K := IsScalarTower.of_algebraMap_eq fun a ↦
    (Ideal.quotientMap_algebraMap (f := algebraMap A B) (H := le_of_eq hm) (x := a)).symm
  have : Algebra.IsIntegral F K := ⟨hf_integral⟩
  let : Algebra A ksep := ((algebraMap F ksep).comp (residue A)).toAlgebra
  have : IsScalarTower A F ksep := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : TensorProduct.CompatibleSMul A F K ksep :=
    .of_algebraMap_surjective _ _ (by exact residue_surjective)
  let β : C →ₐ[A] ksep :=
    { e.symm.toRingHom.comp (residue C) with
      commutes' := fun a ↦ by
        show e.symm (residue C (algebraMap A C a)) = algebraMap F ksep (residue A a)
        rw [← he a, RingEquiv.symm_apply_apply] }
  have hβsurj : Function.Surjective β := fun y ↦ by
    obtain ⟨b, hb⟩ := residue_surjective (e y)
    exact ⟨b, by simp [β, hb]⟩
  have hβker : RingHom.ker β = maximalIdeal C := by
    ext b
    simp [β, RingHom.mem_ker]
  let qa : B →ₐ[A] K := Ideal.Quotient.mkₐ A m'.asIdeal
  let g : B ⊗[A] C →ₐ[A] K ⊗[F] ksep :=
    (Algebra.TensorProduct.equivOfCompatibleSMul F A A K ksep).toAlgHom.comp
      (Algebra.TensorProduct.map qa β)
  have hg_tmul (a : B) (b : C) :
      g (a ⊗ₜ[A] b) = Ideal.Quotient.mk m'.asIdeal a ⊗ₜ[F] e.symm (residue C b) := rfl
  have hgsurj : Function.Surjective g :=
    (Algebra.TensorProduct.equivOfCompatibleSMul F A A K ksep).surjective.comp
      (Algebra.TensorProduct.map_surjective qa β Ideal.Quotient.mk_surjective hβsurj)
  have hgker : RingHom.ker g = RingHom.ker (Algebra.TensorProduct.map qa β) :=
    RingHom.ker_comp_of_injective (Algebra.TensorProduct.map qa β).toRingHom
      (Algebra.TensorProduct.equivOfCompatibleSMul F A A K ksep).injective
  have hqaker : RingHom.ker qa = m'.asIdeal := Ideal.Quotient.mkₐ_ker A m'.asIdeal
  rw [Algebra.TensorProduct.map_ker qa β Ideal.Quotient.mk_surjective hβsurj, hβker,
    hqaker] at hgker
  have hker (q : PrimeSpectrum (B ⊗[A] C))
      (hq : PrimeSpectrum.comap
        (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C) q = m'.toPrimeSpectrum) :
      RingHom.ker g ≤ q.asIdeal := by
    have hq' : q.asIdeal.comap Algebra.TensorProduct.includeLeftRingHom = m'.asIdeal :=
      congrArg PrimeSpectrum.asIdeal hq
    rw [hgker, sup_le_iff, Ideal.map_le_iff_le_comap, Ideal.map_le_iff_le_comap]
    refine ⟨hq'.ge, ?_⟩
    rw [← hC, Ideal.map_le_iff_le_comap, hm, ← hq']
    intro a ha
    show (1 : B) ⊗ₜ[A] algebraMap A C a ∈ q.asIdeal
    change algebraMap A B a ⊗ₜ[A] (1 : C) ∈ q.asIdeal at ha
    rwa [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul,
      ← Algebra.algebraMap_eq_smul_one] at ha
  let primeEquiv : PrimeSpectrum (K ⊗[F] ksep) ≃
      {q : PrimeSpectrum (B ⊗[A] C) //
        PrimeSpectrum.comap
          (Algebra.TensorProduct.includeLeftRingHom : B →+* B ⊗[A] C) q = m'.toPrimeSpectrum} :=
    { toFun := fun q ↦ ⟨PrimeSpectrum.comap g.toRingHom q, by
        ext a
        show g (a ⊗ₜ[A] (1 : C)) ∈ q.asIdeal ↔ a ∈ m'.asIdeal
        rw [hg_tmul, map_one, map_one]
        have hbot : q.asIdeal.comap
            (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[F] ksep) = ⊥ :=
          Ideal.eq_bot_of_prime (q.asIdeal.comap (Algebra.TensorProduct.includeLeftRingHom : K →+* K
            ⊗[F] ksep))
        show Ideal.Quotient.mk m'.asIdeal a ∈ q.asIdeal.comap
            (Algebra.TensorProduct.includeLeftRingHom : K →+* K ⊗[F] ksep) ↔ _
        rw [hbot, Ideal.mem_bot, Ideal.Quotient.eq_zero_iff_mem]⟩
      invFun := fun q ↦
        ⟨q.1.asIdeal.map g, Ideal.map_isPrime_of_surjective hgsurj (hker q.1 q.2)⟩
      left_inv := fun q ↦ PrimeSpectrum.ext (Ideal.map_comap_of_surjective g hgsurj q.asIdeal)
      right_inv := fun q ↦ Subtype.ext (PrimeSpectrum.ext
        (Ideal.comap_map_of_surjective' g hgsurj _ |>.trans (sup_eq_left.mpr (hker q.1 q.2)))) }
  let : Algebra A kbar := ((algebraMap F kbar).comp (residue A)).toAlgebra
  have : IsScalarTower A F kbar := IsScalarTower.of_algebraMap_eq fun _ ↦ rfl
  have : Algebra.IsAlgebraic F kbar := IsAlgClosure.isAlgebraic
  have : IsAlgClosed kbar := IsAlgClosure.isAlgClosed F
  let ringHomEquiv :
      { σ : K →+* kbar // σ.comp f = algebraMap F kbar } ≃ (K →ₐ[F] kbar) :=
    { toFun := fun σ ↦ { σ.1 with commutes' := DFunLike.congr_fun σ.2 }
      invFun := fun σ ↦ ⟨σ.toRingHom, RingHom.ext σ.commutes⟩
      left_inv := fun _ ↦ rfl
      right_inv := fun _ ↦ rfl }
  let pointEquiv := algHomEquivPrimeSpectrum_tensorProduct_sepClosure F K ksep kbar
  refine ⟨ringHomEquiv.trans (pointEquiv.trans primeEquiv), fun σ ↦ ?_⟩
  let φ₀ : K ⊗[F] ksep →ₐ[F] kbar := Algebra.TensorProduct.lift (ringHomEquiv σ)
    (IsScalarTower.toAlgHom F ksep kbar) (fun _ _ => .all _ _)
  have hφ₀ (a : B) (b : C) :
      φ₀.toRingHom.comp g.toRingHom (a ⊗ₜ[A] b) =
        σ.1 (Ideal.Quotient.mk m'.asIdeal a) * algebraMap ksep kbar (e.symm (residue C b)) := by
    show φ₀ (g (a ⊗ₜ[A] b)) = _
    rw [hg_tmul]
    rfl
  refine ⟨φ₀.toRingHom.comp g.toRingHom, hφ₀, ?_, ?_⟩
  · show (pointEquiv (ringHomEquiv σ)).asIdeal.comap g.toRingHom = _
    rw [algHomEquivPrimeSpectrum_tensorProduct_sepClosure_asIdeal]
    rfl
  · intro ψ hψ
    apply Algebra.TensorProduct.ringHom_ext <;> ext x
    · simpa using (hψ x 1).trans (hφ₀ x 1).symm
    · simpa using (hψ 1 x).trans (hφ₀ 1 x).symm

private lemma geometric_fibres_of_strictHenselization
    (A : Type u) (Ash : Type u') (ksep : Type v) (kbar : Type w)
    [CommRing A] [IsLocalRing A] [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    [Field ksep] [Algebra (IsLocalRing.ResidueField A) ksep]
    [IsSepClosure (IsLocalRing.ResidueField A) ksep]
    [IsLocalRing.IsHenselization A ksep Ash]
    [Field kbar] [Algebra (IsLocalRing.ResidueField A) kbar]
    [IsAlgClosure (IsLocalRing.ResidueField A) kbar]
    [Algebra ksep kbar] [IsScalarTower (IsLocalRing.ResidueField A) ksep kbar]
    (e : ksep ≃+* IsLocalRing.ResidueField Ash)
    (he : ∀ x : A,
      e (algebraMap (IsLocalRing.ResidueField A) ksep (IsLocalRing.residue A x)) =
        IsLocalRing.residue Ash (algebraMap A Ash x)) :
    let A' := integralClosure A (FractionRing (A ⧸ nilradical A))
    let T := TensorProduct A A' Ash
    ∀ m' : MaximalSpectrum A',
      ∃ h : IsLocalRing.maximalIdeal A = m'.asIdeal.comap (algebraMap A A'),
        let f := Ideal.quotientMap m'.asIdeal (algebraMap A A') (le_of_eq h)
        f.IsIntegral ∧
          ∃ E : ({σ : (A' ⧸ m'.asIdeal) →+* kbar //
                    σ.comp f = algebraMap (IsLocalRing.ResidueField A) kbar} ≃
                  {q : PrimeSpectrum T //
                    PrimeSpectrum.comap
                      (Algebra.TensorProduct.includeLeftRingHom : A' →+* T) q =
                        m'.toPrimeSpectrum}),
            ∀ σ, ∃ φ : T →+* kbar,
              (∀ (a : A') (b : Ash),
                  φ (a ⊗ₜ[A] b) =
                    σ.1 (Ideal.Quotient.mk m'.asIdeal a) *
                      algebraMap ksep kbar (e.symm (IsLocalRing.residue Ash b))) ∧
                (E σ).1.asIdeal = RingHom.ker φ ∧
                ∀ ψ : T →+* kbar,
                  (∀ (a : A') (b : Ash),
                    ψ (a ⊗ₜ[A] b) =
                      σ.1 (Ideal.Quotient.mk m'.asIdeal a) *
                        algebraMap ksep kbar (e.symm (IsLocalRing.residue Ash b))) →
                  ψ = φ := by
  intro A' T m'
  have : IsSepClosed ksep := IsSepClosure.sep_closed (IsLocalRing.ResidueField A)
  exact fibre_tensorProduct_integral A A' Ash ksep kbar
    (IsLocalRing.IsHenselization.map_maximalIdeal (L := ksep)) e he m'

private lemma geometric_branches_core
    (A : Type u) (Ash : Type u') (ksep : Type v) (kbar : Type w)
    [CommRing A] [IsLocalRing A] [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    [Field ksep] [Algebra (IsLocalRing.ResidueField A) ksep]
    [IsSepClosure (IsLocalRing.ResidueField A) ksep]
    [IsLocalRing.IsHenselization A ksep Ash]
    [Field kbar] [Algebra (IsLocalRing.ResidueField A) kbar]
    [IsAlgClosure (IsLocalRing.ResidueField A) kbar]
    [Algebra ksep kbar] [IsScalarTower (IsLocalRing.ResidueField A) ksep kbar]
    (e : ksep ≃+* IsLocalRing.ResidueField Ash)
    (he : ∀ x : A,
      e (algebraMap (IsLocalRing.ResidueField A) ksep (IsLocalRing.residue A x)) =
        IsLocalRing.residue Ash (algebraMap A Ash x))
    (hmin : (minimalPrimes A).Finite) :
    let A' := integralClosure A (FractionRing (A ⧸ nilradical A))
    let T := TensorProduct A A' Ash
    (∀ m' : MaximalSpectrum A',
      ∃ h : IsLocalRing.maximalIdeal A = m'.asIdeal.comap (algebraMap A A'),
        let f := Ideal.quotientMap m'.asIdeal (algebraMap A A') (le_of_eq h)
        f.IsIntegral ∧
          ∃ E : ({σ : (A' ⧸ m'.asIdeal) →+* kbar //
                    σ.comp f = algebraMap (IsLocalRing.ResidueField A) kbar} ≃
                  {q : PrimeSpectrum T //
                    PrimeSpectrum.comap
                      (Algebra.TensorProduct.includeLeftRingHom : A' →+* T) q =
                        m'.toPrimeSpectrum}),
            ∀ σ, ∃ φ : T →+* kbar,
              (∀ (a : A') (b : Ash),
                  φ (a ⊗ₜ[A] b) =
                    σ.1 (Ideal.Quotient.mk m'.asIdeal a) *
                      algebraMap ksep kbar (e.symm (IsLocalRing.residue Ash b))) ∧
                (E σ).1.asIdeal = RingHom.ker φ ∧
                ∀ ψ : T →+* kbar,
                  (∀ (a : A') (b : Ash),
                    ψ (a ⊗ₜ[A] b) =
                      σ.1 (Ideal.Quotient.mk m'.asIdeal a) *
                        algebraMap ksep kbar (e.symm (IsLocalRing.residue Ash b))) →
                  ψ = φ) ∧
      Set.BijOn
        (Ideal.comap
          (Algebra.TensorProduct.includeRight : Ash →ₐ[A] T).toRingHom)
        (minimalPrimes T) (minimalPrimes Ash) ∧
      (∀ q ∈ minimalPrimes T, ∃! m : Ideal T, m.IsMaximal ∧ q ≤ m) ∧
      (∀ m : Ideal T, m.IsMaximal → ∃! q : Ideal T, q ∈ minimalPrimes T ∧ q ≤ m) := by
  let : Module.Flat A Ash := flat_of_isHenselization (L := ksep)
  let : HenselianLocalRing Ash := IsLocalRing.IsHenselization.henselian A ksep
  refine ⟨?_, bijOn_minimalPrimes_integralClosure_tensorProduct A Ash, ?_, ?_⟩
  · exact geometric_fibres_of_strictHenselization A Ash ksep kbar e he
  · exact existsUnique_maximal_integralClosure_henselization A Ash ksep
  · exact existsUnique_minimalPrime_le_of_isNormalRing _
      (isNormalRing_integralClosure_tensorProduct_henselization A Ash ksep hmin)

/-- Let `A'` be the integral closure of a local ring `A` in the total ring of fractions of its
reduction, and let `Aˢʰ` be a strict henselization with separably closed residue field `ksep`
inside an algebraic closure `kbar`. The residue extension at every maximal ideal of `A'` is
algebraic, and its embeddings into `kbar` canonically parametrize the fibre in
`Spec (A' ⊗[A] Aˢʰ)`. Contraction to `Aˢʰ` is bijective on minimal primes, and containment gives
mutually unique correspondences between minimal and maximal primes of the tensor product. -/
@[stacks 0C25]
theorem geometric_branches_of_strictHenselization
    (A : Type u) (Ash : Type u') (ksep : Type v) (kbar : Type w)
    [CommRing A] [IsLocalRing A] [CommRing Ash] [IsLocalRing Ash] [Algebra A Ash]
    [Field ksep] [Algebra (IsLocalRing.ResidueField A) ksep]
    [IsSepClosure (IsLocalRing.ResidueField A) ksep]
    [IsLocalRing.IsHenselization A ksep Ash]
    [Field kbar] [Algebra (IsLocalRing.ResidueField A) kbar]
    [IsAlgClosure (IsLocalRing.ResidueField A) kbar]
    [Algebra ksep kbar] [IsScalarTower (IsLocalRing.ResidueField A) ksep kbar]
    (e : ksep ≃+* IsLocalRing.ResidueField Ash)
    (he : ∀ x : A,
      e (algebraMap (IsLocalRing.ResidueField A) ksep (IsLocalRing.residue A x)) =
        IsLocalRing.residue Ash (algebraMap A Ash x))
    (hmin : (minimalPrimes A).Finite) :
    let A' := integralClosure A (FractionRing (A ⧸ nilradical A))
    let T := TensorProduct A A' Ash
    (∀ m' : MaximalSpectrum A',
      ∃ h : IsLocalRing.maximalIdeal A = m'.asIdeal.comap (algebraMap A A'),
        let f := Ideal.quotientMap m'.asIdeal (algebraMap A A') (le_of_eq h)
        f.IsIntegral ∧
          ∃ E : ({σ : (A' ⧸ m'.asIdeal) →+* kbar //
                    σ.comp f = algebraMap (IsLocalRing.ResidueField A) kbar} ≃
                  {q : PrimeSpectrum T //
                    PrimeSpectrum.comap
                      (Algebra.TensorProduct.includeLeftRingHom : A' →+* T) q =
                        m'.toPrimeSpectrum}),
            ∀ σ, ∃ φ : T →+* kbar,
              (∀ (a : A') (b : Ash),
                  φ (a ⊗ₜ[A] b) =
                    σ.1 (Ideal.Quotient.mk m'.asIdeal a) *
                      algebraMap ksep kbar (e.symm (IsLocalRing.residue Ash b))) ∧
                (E σ).1.asIdeal = RingHom.ker φ ∧
                ∀ ψ : T →+* kbar,
                  (∀ (a : A') (b : Ash),
                    ψ (a ⊗ₜ[A] b) =
                      σ.1 (Ideal.Quotient.mk m'.asIdeal a) *
                        algebraMap ksep kbar (e.symm (IsLocalRing.residue Ash b))) →
                  ψ = φ) ∧
      Set.BijOn
        (Ideal.comap
          (Algebra.TensorProduct.includeRight : Ash →ₐ[A] T).toRingHom)
        (minimalPrimes T) (minimalPrimes Ash) ∧
      (∀ q ∈ minimalPrimes T, ∃! m : Ideal T, m.IsMaximal ∧ q ≤ m) ∧
      (∀ m : Ideal T, m.IsMaximal → ∃! q : Ideal T, q ∈ minimalPrimes T ∧ q ≤ m) :=
  geometric_branches_core A Ash ksep kbar e he hmin

end GeometricBranches


section HenselizationBijection

open scoped TensorProduct

set_option backward.isDefEq.respectTransparency false

/-- Let `A'` be the integral closure of a local ring `A` in the total ring of fractions of its
reduction, and let `Aʰ` be a henselization of `A`. Contraction from `A' ⊗[A] Aʰ` is bijective
on maximal ideals toward `A'` and on minimal primes toward `Aʰ`. Each minimal prime of the tensor
product lies in a unique maximal ideal, and each maximal ideal contains a unique minimal prime. -/
@[stacks 0C24]
theorem bijective_maximalIdeals_and_minimalPrimes_of_henselization
    (A : Type u) (Ah : Type v) [CommRing A] [IsLocalRing A] [CommRing Ah] [IsLocalRing Ah]
    [Algebra A Ah]
    [IsLocalRing.IsHenselization A (IsLocalRing.ResidueField A) Ah]
    (hmin : (minimalPrimes A).Finite) :
    let A' := integralClosure A (FractionRing (A ⧸ nilradical A))
    let T := TensorProduct A A' Ah
    Set.BijOn
        (Ideal.comap (Algebra.TensorProduct.includeLeftRingHom : A' →+* T))
        {I : Ideal T | I.IsMaximal} {I : Ideal A' | I.IsMaximal} ∧
      Set.BijOn
        (Ideal.comap
          (Algebra.TensorProduct.includeRight : Ah →ₐ[A] T).toRingHom)
        (minimalPrimes T) (minimalPrimes Ah) ∧
      (∀ q ∈ minimalPrimes T, ∃! m : Ideal T, m.IsMaximal ∧ q ≤ m) ∧
      (∀ m : Ideal T, m.IsMaximal → ∃! q : Ideal T, q ∈ minimalPrimes T ∧ q ≤ m) := by
  let : Module.Flat A Ah :=
    flat_of_isHenselization (L := IsLocalRing.ResidueField A)
  refine ⟨bijOn_maximalIdeals_integralClosure_henselization A Ah,
    bijOn_minimalPrimes_integralClosure_tensorProduct A Ah,
    existsUnique_maximal_integralClosure_henselization A Ah (IsLocalRing.ResidueField A), ?_⟩
  exact existsUnique_minimalPrime_le_of_isNormalRing _
    (isNormalRing_integralClosure_tensorProduct_henselization A Ah
      (IsLocalRing.ResidueField A) hmin)

end HenselizationBijection

end
