module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Crystalline.AffineSite
public import StacksFrontier.AlgebraicGeometry.Crystalline.Crystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Completion
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Universal

/-!
# The universal differential on a completed divided power envelope

Fix an affine crystalline situation with base `A`, target `C` and prime `p`, and present `C` as a
quotient of a polynomial algebra `A[x_i]`.  Let `E` be the divided power envelope of the kernel
of that presentation and let `E^` be its `p`-adic completion, which is the object representing
the crystalline site in this presentation.

The universal divided power differential of `E` extends to `E^`: there is a divided power
derivation of `E^` into the `p`-adic completion of `Ω_{E/A, δ}` whose value on the image of an
element of `E` is the image of that element's universal divided power differential.  This is the
derivation appearing in the crystalline de Rham complex of a quasi-coherent crystal.

That `p`-adic completion of `Ω_{E/A, δ}` is the module written `Ω_D` in the source.  It is at
once the inverse limit of the divided power differentials of the finite levels `D_e` and the
`p`-adic completion of the divided power differentials of `E^` itself, and both identifications
are recorded here.

## Main definitions

* `Crystalline.polynomialDividedPowerEnvelopeRing` — the divided power envelope `E` of a polynomial
  presentation, with its algebra structure over the base.
* `Crystalline.pAdicCompletedDividedPowerDifferentials` — the module `Ω_D`.

## Main results

* `Crystalline.completedDividedPowerDifferential` — the divided power derivation on the completed
  envelope, together with its value on the image of the uncompleted envelope.
* `Crystalline.pAdicCompletedDividedPowerDifferentialsEquivLimit` and
  `Crystalline.pAdicCompletedDividedPowerDifferentialsEquivCompletion` — the two identifications
  of `Ω_D` displayed in the source.

## Implementation notes

The target of the derivation is stated as the `p`-adic completion of `Ω_{E/A, δ}`, which is the
second of the two inverse limits of equation 60.17.1; the comparison of
`Crystalline.dividedPowerDifferentialsCompletionComparison` identifies it with the first, the
completion of the differentials of `E^` itself.

The nilpotence of `p` modulo the divided power ideal of `E` is part of the conclusion rather than
a hypothesis, since it follows from the situation and is needed to name the completed divided
powers; this lets the polynomial variables lie in an arbitrary universe.

## References

* [Stacks Project, Equation 60.17.1, Tag 07JA](https://stacks.math.columbia.edu/tag/07JA)
* [Stacks Project, Equation 60.17.0.2, Tag 07J9](https://stacks.math.columbia.edu/tag/07J9)
-/

@[expose] public section

universe u v w

namespace Crystalline

open CategoryTheory CategoryTheory.Limits

/-- The composite of the two limit comparisons of
`Crystalline.dividedPowerDifferentialsCompletionComparison`, from the `p`-adic completion of the
differentials of the completed ring to the `p`-adic completion of the differentials of the
original ring, is semilinear over the completed ring. -/
public lemma completionComparison_composite_smul
    {A : Type u} {B : Type v} [CommRing A] [CommRing B] [Algebra A B]
    (J : Ideal B) (delta : DividedPowers J) (p : ℕ)
    (hp : IsNilpotent (Ideal.Quotient.mk J (p : B)))
    (hcmp : DifferentialsCompletionComparison J delta p hp) :
    let D := DividedPowerRing.of
      (AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) B)
      (DividedPowers.completionIdeal J p hp)
      (DividedPowers.completedDividedPowers J delta p hp).1
    let Mc := dividedPowerDifferentials (A := A) D.dividedPowers
    let Fadd := hcmp.fromCompletionLimit.trans hcmp.fromOriginalLimit.symm
    ∀ (r : D) (x : AdicCompletion (DividedPowers.pAdicIdeal (A := D) p) Mc),
      Fadd (r • x) = r • Fadd x := by
  classical
  intro D Mc Fadd r x
  let Q := QuotientDifferentialsSystem.functor (A := A) J delta p hcmp.quotientSystem
  have hlim (z : AdicCompletion (DividedPowers.pAdicIdeal (A := D) p) Mc) :
      hcmp.fromCompletionLimit z = hcmp.fromOriginalLimit (Fadd z) := by
    change hcmp.fromCompletionLimit z =
      hcmp.fromOriginalLimit
        (hcmp.fromOriginalLimit.symm (hcmp.fromCompletionLimit z))
    exact (hcmp.fromOriginalLimit.apply_symm_apply _).symm
  apply hcmp.fromOriginalLimit.injective
  apply Concrete.limit_ext Q
  intro i
  let e := i.unop
  let n := hcmp.quotientSystem.cutoff + e
  have hC (z : AdicCompletion (DividedPowers.pAdicIdeal (A := D) p) Mc) :
      limit.π Q i (hcmp.fromCompletionLimit z) = hcmp.fromCompletionAt e (z.val n) := by
    change ConcreteCategory.hom (limit.π Q (Opposite.op e)) (hcmp.fromCompletionLimit z) = _
    rw [← AdicCompletion.eval_apply]
    exact hcmp.fromCompletionLimit_projection e z
  have hO (z : AdicCompletion (DividedPowers.pAdicIdeal (A := B) p) _) :
      limit.π Q i (hcmp.fromOriginalLimit z) = hcmp.fromOriginalAt e (z.val n) := by
    change ConcreteCategory.hom (limit.π Q (Opposite.op e)) (hcmp.fromOriginalLimit z) = _
    rw [← AdicCompletion.eval_apply]
    exact hcmp.fromOriginalLimit_projection e z
  have hbase : hcmp.fromCompletionAt e (x.val n) =
      hcmp.fromOriginalAt e ((Fadd x).val n) := by
    rw [← hC x, hlim x, hO]
  rw [← hlim (r • x), hC, hO]
  have hcompSmul := hcmp.fromCompletionAt_smul e r (x.val n)
  obtain ⟨a, ha⟩ := Ideal.Quotient.mk_surjective
    (AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p) n r)
  have hsource : (r • Fadd x).val n = a • (Fadd x).val n := by
    rw [AdicCompletion.smul_eval,
      AdicCompletion.val_smul_eq_evalₐ_smul, ← ha]
    induction (Fadd x).val n using Quotient.inductionOn' with
    | _ y => rfl
  calc
    hcmp.fromCompletionAt e ((r • x).val n) =
        AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p) n r •
          hcmp.fromCompletionAt e (x.val n) := by
            have hcoord : (r • x).val n =
                r • x.val n := by
              change ((algebraMap D
                (AdicCompletion (DividedPowers.pAdicIdeal (A := D) p) D) r) • x).val n = _
              rw [AdicCompletion.smul_eval,
                AdicCompletion.val_smul_eq_evalₐ_smul]
              simp
            rw [hcoord]
            exact hcompSmul
    _ = AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := B) p) n r •
          hcmp.fromOriginalAt e ((Fadd x).val n) := by rw [hbase]
    _ = hcmp.fromOriginalAt e ((r • Fadd x).val n) := by
          rw [hsource, (hcmp.fromOriginalAt e).map_smul, ← ha]
          rfl

/-- In an affine crystalline situation the prime is nilpotent modulo the divided power ideal of
the divided power envelope of a polynomial presentation. -/
public lemma polynomialDividedPowerEnvelope_prime_nilpotent
    (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
    (f : MvPolynomial ι s.A →ₐ[s.A] s.C) :
    let E := (polynomialDividedPowerEnvelope s f).object
    IsNilpotent (Ideal.Quotient.mk E.ideal (s.p : E)) := by
  classical
  intro E
  let env := polynomialDividedPowerEnvelope s f
  let : Algebra s.A E := env.structureMap.toRingHom.toAlgebra
  obtain ⟨N, hN⟩ := s.prime_nilpotent
  refine ⟨N, ?_⟩
  rw [← map_pow]
  apply Ideal.Quotient.eq_zero_iff_mem.mpr
  have hker : algebraMap s.A (MvPolynomial ι s.A) ((s.p : s.A) ^ N) ∈
      RingHom.ker f.toRingHom := by
    change f (algebraMap s.A (MvPolynomial ι s.A) ((s.p : s.A) ^ N)) = 0
    rw [f.commutes]
    simpa using hN
  have hmem : env.algebraMap.toRingHom
      (algebraMap s.A (MvPolynomial ι s.A) ((s.p : s.A) ^ N)) ∈ E.ideal :=
    env.algebraMap.ideal_comp (Ideal.mem_map_of_mem _ hker)
  have hmap : env.algebraMap.toRingHom
      (algebraMap s.A (MvPolynomial ι s.A) ((s.p : s.A) ^ N)) =
      env.structureMap.toRingHom ((s.p : s.A) ^ N) := by
    have h := congrArg (fun g : s.A →+* E => g ((s.p : s.A) ^ N))
      env.algebraMap_comp
    simpa using h
  rw [hmap] at hmem
  have hpcast : (s.p : E) = algebraMap s.A E (s.p : s.A) := by simp
  rw [hpcast, ← map_pow]
  exact hmem

/-- The universal divided power derivation of the completed envelope, characterized
on the dense image of the original envelope. -/
@[stacks 07JA, stacks 07L1 "the same derivation for the (n+1)-fold tensor-product presentation"]
public noncomputable def completedDividedPowerDifferential
    (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
    (f : MvPolynomial ι s.A →ₐ[s.A] s.C) (hf : Function.Surjective f) :
    let env := polynomialDividedPowerEnvelope s f
    let E := env.object
    letI : Algebra s.A E := env.structureMap.toRingHom.toAlgebra
    let P := DividedPowers.pAdicIdeal (A := E) s.p
    let Ω := AdicCompletion P (dividedPowerDifferentials (A := s.A) E.dividedPowers)
    Σ' hp : IsNilpotent (Ideal.Quotient.mk E.ideal (s.p : E)),
      let D := DividedPowerRing.of
        (pAdicCompletedDividedPowerEnvelope s f hf)
        (DividedPowers.completionIdeal E.ideal s.p hp)
        (DividedPowers.completedDividedPowers E.ideal E.dividedPowers s.p hp).1
      letI : Algebra s.A D :=
        ((algebraMap E D).comp env.structureMap.toRingHom).toAlgebra
      { d : DividedPowerDerivation s.A D (algebraMap s.A D) Ω //
        ∀ b : E, d (algebraMap E D b) =
          AdicCompletion.of P (dividedPowerDifferentials (A := s.A) E.dividedPowers)
            (dividedPowerDifferential (A := s.A) E.dividedPowers b) } :=
  by
    classical
    let env := polynomialDividedPowerEnvelope s f
    let E := env.object
    letI : Algebra s.A E := env.structureMap.toRingHom.toAlgebra
    let P := DividedPowers.pAdicIdeal (A := E) s.p
    have hp := polynomialDividedPowerEnvelope_prime_nilpotent s f
    refine ⟨hp, ?_⟩
    let D := DividedPowerRing.of
      (pAdicCompletedDividedPowerEnvelope s f hf)
      (DividedPowers.completionIdeal E.ideal s.p hp)
      (DividedPowers.completedDividedPowers E.ideal E.dividedPowers s.p hp).1
    letI : Algebra s.A D :=
      @AdicCompletion.instAlgebra (↑E) (↑s.A) inferInstance inferInstance
        (DividedPowers.pAdicIdeal (A := E) s.p)
        (inferInstance : Algebra s.A E)
    let Mc := dividedPowerDifferentials (A := s.A) D.dividedPowers
    have hcmp := dividedPowerDifferentialsCompletionComparison
      (A := s.A) (B := E) (J := E.ideal) (delta := E.dividedPowers) (p := s.p) hp
    let Fadd := hcmp.fromCompletionLimit.trans hcmp.fromOriginalLimit.symm
    let Q := QuotientDifferentialsSystem.functor
      (A := s.A) (J := E.ideal) (delta := E.dividedPowers) (p := s.p)
      hcmp.quotientSystem
    have hlim (z : AdicCompletion
        (DividedPowers.pAdicIdeal
          (A := pAdicCompletedDividedPowerEnvelope s f hf) s.p) Mc) :
        hcmp.fromCompletionLimit z = hcmp.fromOriginalLimit (Fadd z) := by
      change hcmp.fromCompletionLimit z =
        hcmp.fromOriginalLimit
          (hcmp.fromOriginalLimit.symm (hcmp.fromCompletionLimit z))
      exact (hcmp.fromOriginalLimit.apply_symm_apply _).symm
    have hFsmul := completionComparison_composite_smul E.ideal E.dividedPowers s.p hp hcmp
    let F : Mc →ₗ[D]
        (AdicCompletion P (dividedPowerDifferentials (A := s.A) E.dividedPowers)) :=
      (Fadd.toLinearEquiv hFsmul).toLinearMap.comp
        (AdicCompletion.of (DividedPowers.pAdicIdeal (A := D) s.p) Mc)
    let du := universalDividedPowerDerivation (A := s.A) (B := D)
    let d : DividedPowerDerivation s.A D (algebraMap s.A D)
        (AdicCompletion P (dividedPowerDifferentials (A := s.A) E.dividedPowers)) := {
      toDerivation := Derivation.llcomp F du.toDerivation
      map_ringHom' := by
        intro a
        simp [du.map_ringHom]
      map_dpow' := by
        intro n hn x hx
        change F (du (D.dividedPowers.dpow n x)) = _
        rw [du.map_dpow n hn x hx]
        exact F.map_smul _ _ }
    refine ⟨d, ?_⟩
    intro b
    change F (du (algebraMap E D b)) =
      AdicCompletion.of P (dividedPowerDifferentials (A := s.A) E.dividedPowers)
        (dividedPowerDifferential (A := s.A) E.dividedPowers b)
    apply hcmp.fromOriginalLimit.injective
    apply Concrete.limit_ext Q
    intro i
    let e := i.unop
    let n := hcmp.quotientSystem.cutoff + e
    have hc := hcmp.fromCompletionLimit_projection e
      (AdicCompletion.of
        (DividedPowers.pAdicIdeal (A := D) s.p) Mc
        (du (algebraMap E D b)))
    have ho := hcmp.fromOriginalLimit_projection e
      (AdicCompletion.of P (dividedPowerDifferentials (A := s.A) E.dividedPowers)
        (dividedPowerDifferential (A := s.A) E.dividedPowers b))
    have hFcomp : hcmp.fromOriginalLimit (F (du (algebraMap E D b))) =
        hcmp.fromCompletionLimit
          (AdicCompletion.of
            (DividedPowers.pAdicIdeal (A := D) s.p) Mc
            (du (algebraMap E D b))) :=
      (hlim (AdicCompletion.of
        (DividedPowers.pAdicIdeal (A := D) s.p) Mc
        (du (algebraMap E D b)))).symm
    rw [hFcomp, hc, ho]
    dsimp only [du, universalDividedPowerDerivation]
    unfold D
    dsimp only [pAdicCompletedDividedPowerEnvelope]
    rw [AdicCompletion.eval_of]
    change hcmp.fromCompletionAt e
        (Submodule.Quotient.mk
          (dividedPowerDifferential (A := s.A)
            (DividedPowers.completedDividedPowers E.ideal E.dividedPowers s.p hp).1
            (algebraMap E
              (AdicCompletion (DividedPowers.pAdicIdeal (A := E) s.p) E) b))) =
      hcmp.fromOriginalAt e
        (Submodule.Quotient.mk (dividedPowerDifferential (A := s.A) E.dividedPowers b))
    rw [hcmp.fromCompletionAt_d, hcmp.fromOriginalAt_d]
    have heval : AdicCompletion.evalₐ (DividedPowers.pAdicIdeal (A := E) s.p) n
        (algebraMap E (AdicCompletion (DividedPowers.pAdicIdeal (A := E) s.p) E) b) =
      Ideal.Quotient.mk
          (DividedPowers.pAdicIdeal (A := E) s.p ^ n) b := by
      simp [AdicCompletion.algebraMap_apply]
    rw [heval]

/-! ### The completed module of differentials `Ω_D` -/

/-- The divided power envelope `D_{P, γ}(J)` of a polynomial presentation, as a divided power
ring. -/
public noncomputable abbrev polynomialDividedPowerEnvelopeRing
    (s : AffineCrystallineSituation.{u, v})
    {ι : Type w} (f : MvPolynomial ι s.A →ₐ[s.A] s.C) : DividedPowerRing.{max u w} :=
  (polynomialDividedPowerEnvelope s f).object

/-- The divided power envelope of a polynomial presentation is an algebra over the base, via
the structural divided power morphism. -/
public noncomputable instance presentationEnvelopeAlgebra
    (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
    (f : MvPolynomial ι s.A →ₐ[s.A] s.C) : Algebra s.A (polynomialDividedPowerEnvelopeRing s f) :=
  (polynomialDividedPowerEnvelope s f).structureMap.toRingHom.toAlgebra

/-- The module `Ω_D`: the `p`-adic completion of the module of divided power differentials of
the divided power envelope of a polynomial presentation of `C` over `A`. -/
@[stacks 07J9]
public noncomputable abbrev pAdicCompletedDividedPowerDifferentials
    (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
    (f : MvPolynomial ι s.A →ₐ[s.A] s.C) : Type (max u w) :=
  AdicCompletion (DividedPowers.pAdicIdeal (A := polynomialDividedPowerEnvelopeRing s f) s.p)
    (dividedPowerDifferentials (A := s.A) (polynomialDividedPowerEnvelopeRing s f).dividedPowers)

/-- The comparison of the three inverse limits of divided power differentials, read at the
divided power envelope of a polynomial presentation. -/
public noncomputable def presentationDifferentialsCompletionComparison
    (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
    (f : MvPolynomial ι s.A →ₐ[s.A] s.C) :
    DifferentialsCompletionComparison (A := s.A) (polynomialDividedPowerEnvelopeRing s f).ideal
      (polynomialDividedPowerEnvelopeRing s f).dividedPowers s.p
      (polynomialDividedPowerEnvelope_prime_nilpotent s f) :=
  dividedPowerDifferentialsCompletionComparison _ _ _
    (polynomialDividedPowerEnvelope_prime_nilpotent s f)

/-- **Stacks 07J9, the first identification.** `Ω_D = lim_e Ω_{D_e/A, γ̄}`: the completed module
of divided power differentials is the inverse limit of the modules of divided power
differentials of the finite levels `D_e`. -/
@[stacks 07J9 "the inverse limit over the finite levels"]
public noncomputable def pAdicCompletedDividedPowerDifferentialsEquivLimit
    (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
    (f : MvPolynomial ι s.A →ₐ[s.A] s.C) :
    pAdicCompletedDividedPowerDifferentials s f ≃+
      ((limit (QuotientDifferentialsSystem.functor (A := s.A)
          (polynomialDividedPowerEnvelopeRing s f).ideal
          (polynomialDividedPowerEnvelopeRing s f).dividedPowers s.p
          (presentationDifferentialsCompletionComparison s f).quotientSystem) :
        AddCommGrpCat) : Type (max u w)) :=
  (presentationDifferentialsCompletionComparison s f).fromOriginalLimit

/-- **Stacks 07J9, the second identification.** `Ω_D = lim_e Ω_{D/A, γ̄}/p^eΩ_{D/A, γ̄}`: the
completed module of divided power differentials is also the `p`-adic completion of the module
of divided power differentials of the completed envelope `D` itself. -/
@[stacks 07J9 "the p-adic completion of the differentials of the completed envelope"]
public noncomputable def pAdicCompletedDividedPowerDifferentialsEquivCompletion
    (s : AffineCrystallineSituation.{u, v}) {ι : Type w}
    (f : MvPolynomial ι s.A →ₐ[s.A] s.C) :
    pAdicCompletedDividedPowerDifferentials s f ≃+
      AdicCompletion
        (DividedPowers.pAdicIdeal
          (A := AdicCompletion
            (DividedPowers.pAdicIdeal (A := polynomialDividedPowerEnvelopeRing s f) s.p)
            (polynomialDividedPowerEnvelopeRing s f)) s.p)
        (dividedPowerDifferentials (A := s.A)
          (DividedPowers.completedDividedPowers (polynomialDividedPowerEnvelopeRing s f).ideal
            (polynomialDividedPowerEnvelopeRing s f).dividedPowers s.p
            (polynomialDividedPowerEnvelope_prime_nilpotent s f)).1) :=
  ((presentationDifferentialsCompletionComparison s f).fromOriginalLimit).trans
    ((presentationDifferentialsCompletionComparison s f).fromCompletionLimit).symm

end Crystalline

end
