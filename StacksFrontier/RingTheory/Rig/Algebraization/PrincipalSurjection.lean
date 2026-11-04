module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.RingTheory.Rig.Algebraization.JacobianCriterion
public import StacksFrontier.RingTheory.Rig.PrincipalLiftUniform
public import StacksFrontier.RingTheory.Rig.RigEtaleLifting

/-!
# Algebraizing a Jacobian chart over a principal ideal: the surjection

Let `A` be a Noetherian ring, `I = (a)` a *principal* ideal and `B` an object of the category
of Stacks 0AL4 presented as `B = A⟨x₁, …, x_r⟩/J`, carrying a Jacobian chart: an element `b`,
an integer `m ≤ r` and `f₁, …, f_m ∈ J` with `V(b) ⊆ V(IB)`, with the Jacobian determinant
`Δ = det(∂fⱼ/∂xᵢ)_{i, j ≤ m}` dividing the image of `b`, and with `bJ ⊆ (f₁, …, f_m) + J²`.
This file produces, **with no carried hypothesis**, a finite type `A`-algebra `C` which is
smooth over `Spec(A) ∖ V(I)` together with a *surjection* `φ : C^∧ ↠ B` of `A`-algebras.

That is the whole of Stacks 0GAW except for its last step. The source of Stacks 0ALS remarks
that in the principal case the use of Stacks 0GAQ can be replaced by the much easier
Stacks 0AK7, and that is what happens here: the lift of the comparison map
`ψₙ : C^∧ → B/IⁿB` to `φ : C^∧ → B` is produced by `Rig.exists_algHom_lift_of_torsion_disjoint`
(Stacks 0AK7) rather than by `Rig.exists_algHom_lift_of_dualSituation` (Stacks 0GAQ). Stacks
0AK7 asks only that the `a`-power torsion of the target meet a power of `I` in `0`, which is
automatic over a Noetherian ring (`Rig.exists_disjoint_torsionIdeal_pow_map`). So every one of
the `DualSituation` hypotheses that the library's Stacks 0GAQ carries — the family `S`, the
invariants `d`, `q₀`, `k` of Local Cohomology Section 0GA6, and the open duality input of
Stacks 0GAC — disappears, and with them the restriction that the target live in the universe
of `A`: `B` is an arbitrary `AdicFiniteTypeAlgebra.{u, v}` here.

## Main results

* `Rig.exists_finiteType_surjection_of_jacobianChart_principal`: for a Jacobian chart over a
  principal ideal there is a finite type `A`-algebra `C`, smooth away from `V(I)`, and a
  surjection `C^∧ ↠ B`; both `B` and `C^∧` are rig-smooth over `(A, I)`.
* `Rig.exists_finiteType_surjection_of_isRigEtale_principal`: the same for a rig-étale `B`,
  whose Jacobian chart is supplied by
  `Rig.exists_jacobianCriterion_of_isRigEtale_principal`.

## What remains for Stacks 0ALS

Exactly the conormal annihilation: that a power of `I` annihilates `Ker(φ)/Ker(φ)²`. Granted
that, `exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated` (Stacks 0ALR)
turns the surjection produced here into the isomorphism `B ≅ C^∧` of Stacks 0ALS. The source
obtains it from the six-term exact sequence of Stacks 0ALM
(`Rig.CompletedPolynomialPresentation.exists_sixTerm_exact_combined`) together with a
localized comparison `H⁰(NL^∧_{C^∧/A}) ⊗ B[1/b] = H⁰(NL^∧_{B/A}) ⊗ B[1/b]` of free modules of
rank `r - m`, which the library does not have. No hypothesis standing for it is introduced
here, and no `stacks` attribute for 0ALS or 0GAW is placed in this file.

## References

* [Stacks Project, Tag 0ALS](https://stacks.math.columbia.edu/tag/0ALS)
* [Stacks Project, Tag 0GAW](https://stacks.math.columbia.edu/tag/0GAW)
* [Stacks Project, Tag 0AK7](https://stacks.math.columbia.edu/tag/0AK7)
* [Stacks Project, Tag 0GAV](https://stacks.math.columbia.edu/tag/0GAV)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial RestrictedPowerSeries

namespace Rig

universe u v

attribute [local instance] HasDerivedCategory.standard

section Main

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- **The surjection of Stacks 0GAW over a principal ideal, with no carried hypothesis.**

Let `A` be a Noetherian ring, `I = (a)` principal, and let `B` be an object of the category of
Stacks 0AL4 carrying a Jacobian chart: a completed polynomial presentation
`B = A⟨x₁, …, x_r⟩/J`, an element `b` with `V(b) ⊆ V(IB)`, an integer `m ≤ r` and
`f₁, …, f_m ∈ J` whose Jacobian determinant divides the image of `b`, with
`bJ ⊆ (f₁, …, f_m) + J²`. Then there is a finite type `A`-algebra `C`, smooth over
`Spec(A) ∖ V(I)`, and a surjection `φ : C^∧ → B` of `A`-algebras; moreover both `B` and `C^∧`
are rig-smooth over `(A, I)`.

`C` is the algebra `A[z, x₁, …, x_r]/(zΔ' - a^{c₁}, f'₁, …, f'_m)` of Stacks 0GAV for the
one-element generating family `{a}` of `I`, where the `f'ⱼ` are polynomial approximations to
the `fⱼ` and `I^{c₁}B ⊆ bB`. It maps onto `B/IⁿB`, and that map lifts to `φ` by Stacks 0AK7:
the exponent `c = 1 + ((1+1)c₁ - 1)` of Stacks 0GAV annihilates `Ext¹` out of the completed
naive cotangent complex of `C^∧`, the `a`-power torsion of `B` meets `I^d B` in `0` for some
`d` because `B` is Noetherian, and `n` is taken past `max (2c) (c + d)`.

Lifting through Stacks 0AK7 rather than Stacks 0GAQ is the replacement the source of
Stacks 0ALS points to. It is what removes the `DualSituation` data, the invariants of Local
Cohomology Section 0GA6, the open duality input of Stacks 0GAC, and the restriction that `B`
live in the universe of `A`.

This is Stacks 0GAW up to, but not including, its final step; no `stacks` attribute is placed,
because the tag's statement is the isomorphism `B ≅ C^∧` and the conormal annihilation that
produces it from this surjection is not available.

This is the form of the statement which **names** `C`: it returns the polynomial
approximations `f'ⱼ` and the exponent `c₁` out of which `C` is built, so that the caller has
`C = Rig.MultiJacobianAlgebra hm f' (fun _ ↦ a) c₁` on the nose together with its completed
presentation `Rig.multiJacobianCompletedPresentation`.  That is needed because the comparison
of degree-`0` cohomologies in the last step of Stacks 0GAW is a statement about *that*
presentation of `C^∧`, not about an anonymous finite type algebra; see
`Rig.pow_smul_mem_range_innerBaseChangeDifferential_multiJacobian`.
`Rig.exists_finiteType_surjection_of_jacobianChart_principal` below is the anonymous form, a
bare application of this one. -/
public theorem exists_multiJacobian_surjection_of_jacobianChart_principal
    (a : A) (hI : I = Ideal.span {a})
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    (m : ℕ) (hm : m ≤ P.variableCount) (b : P.completedPolynomialRing)
    (f : Fin m → P.ker)
    (hvanish : B.adicIdeal ≤ (Ideal.span {P.toAlgHom b}).radical)
    (hjacobian :
      P.toAlgHom (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
          (f j : P.completedPolynomialRing)) ∣ P.toAlgHom b)
    (hrelations : ∀ x : P.completedPolynomialRing, x ∈ P.ker →
      b * x ∈ Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
        P.ker ^ 2) :
    ∃ (f' : Fin m → MvPolynomial (Fin P.variableCount) A) (c₁ : ℕ)
      (φ : AdicCompletion
          (I.map (algebraMap A (MultiJacobianAlgebra hm f' (fun _ : Fin 1 ↦ a) c₁)))
          (MultiJacobianAlgebra hm f' (fun _ : Fin 1 ↦ a) c₁) →ₐ[A] B.carrier),
      Function.Surjective φ ∧
        SmoothAwayFrom A I (MultiJacobianAlgebra hm f' (fun _ : Fin 1 ↦ a) c₁) ∧
        IsRigSmooth B ∧
        IsRigSmooth
          (adicCompletionObj I (B := MultiJacobianAlgebra hm f' (fun _ : Fin 1 ↦ a) c₁)) := by
  classical
  have hIfg : I.FG := Ideal.fg_of_isNoetherianRing I
  have hBcomplete : IsAdicComplete (I.map (algebraMap A B.carrier)) B.carrier :=
    B.isAdicallyComplete
  -- `I = (a)` is generated by the one-element family `agen`
  set agen : Fin 1 → A := fun _ ↦ a with hagendef
  have hagen : Ideal.span (Set.range agen) = I := by
    rw [hI, hagendef, Set.range_const]
  have hai : ∀ i, agen i ∈ I := fun i ↦ hagen ▸ Ideal.subset_span ⟨i, rfl⟩
  -- the Jacobian chart makes `B` rig-smooth over `(A, I)`
  have hBsmooth : IsRigSmooth B :=
    isRigSmooth_of_jacobianChart B P m hm b f hvanish hjacobian hrelations
  -- `V(b) ⊆ V(IB)` gives `c₁` with `I^{c₁}B ⊆ bB`
  obtain ⟨c₁, hc₁⟩ := exists_pow_adicIdeal_le_span_of_le_radical B (P.toAlgHom b) hvanish
  -- the `a`-power torsion of `B` meets `I^d B` in `0`: `B` is Noetherian
  obtain ⟨d, hd⟩ := exists_disjoint_torsionIdeal_pow_map hI B.carrier
  -- the relations read as restricted power series
  set g : Fin m → RestrictedPowerSeries I (Fin P.variableCount) := fun j ↦
    (adicCompletionAlgEquiv I (Fin P.variableCount)).symm (f j : P.completedPolynomialRing)
    with hgdef
  have hge : ∀ j, adicCompletionAlgEquiv I (Fin P.variableCount) (g j) =
      (f j : P.completedPolynomialRing) := fun j ↦ by
    rw [hgdef]
    exact AlgEquiv.apply_symm_apply _ _
  have hgker : ∀ j, g j ∈ P.restrictedKer := by
    intro j
    rw [P.mem_restrictedKer_iff, hge j]
    exact (f j).2
  -- the Jacobian determinant and its cofactor
  set Δ := P.toAlgHom (Matrix.det fun i j : Fin m ↦
    (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
      (f j : P.completedPolynomialRing)) with hΔdef
  obtain ⟨b', hb'⟩ := hjacobian
  -- the Ext exponent of Stacks 0GAV for the one-element generating family, and the accuracy
  set c : ℕ := 1 + 1 * ((1 + 1) * c₁ - 1) with hcdef
  obtain ⟨n, hn, hnc⟩ : ∃ n : ℕ, max (2 * c) (c + d) < n ∧ n - c ≠ 0 :=
    ⟨max (2 * c) (c + d) + 1, Nat.lt_succ_self _, by
      have : c ≤ max (2 * c) (c + d) := le_trans (by omega) (le_max_right _ _)
      omega⟩
  -- the polynomial approximations `f'ⱼ`
  obtain ⟨f', hf'proj, hf'mem⟩ :=
    P.exists_mvPolynomial_approx_mem_restrictedKer hIfg n g hgker
  -- the cofactors `b_k` of `b`
  have hbsex : ∀ i : Fin 1, ∃ w : B.carrier,
      P.toAlgHom b * w = algebraMap A B.carrier (agen i ^ c₁) := by
    intro i
    have hmem : algebraMap A B.carrier (agen i ^ c₁) ∈ B.adicIdeal ^ c₁ := by
      rw [show B.adicIdeal = I.map (algebraMap A B.carrier) from rfl, ← Ideal.map_pow]
      exact Ideal.mem_map_of_mem _ (Ideal.pow_mem_pow (hai i) c₁)
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.mp (hc₁ hmem)
    exact ⟨w, by rw [mul_comm]; exact hw⟩
  choose bs hbs using hbsex
  -- the determinant of the approximations is close to `Δ`
  have hbapprox : b' * P.restrictedToAlgHom
        (polynomialAlgHom I (Fin P.variableCount) (jacobian hm f').det) - P.toAlgHom b ∈
      (I ^ n).map (algebraMap A B.carrier) := by
    have hdet := det_partialDeriv_sub_restrictedToAlgHom_det_mem P hIfg n hm g f' hf'proj
    rw [show (Matrix.det fun i j : Fin m ↦
          (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
            (adicCompletionAlgEquiv I (Fin P.variableCount) (g j))) =
        (Matrix.det fun i j : Fin m ↦
          (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
            (f j : P.completedPolynomialRing)) from by
      congr 1
      funext i j
      rw [hge j]] at hdet
    rw [hb', show b' * P.restrictedToAlgHom
          (polynomialAlgHom I (Fin P.variableCount) (jacobian hm f').det) - Δ * b' =
        -(b' * (Δ - P.restrictedToAlgHom
          (polynomialAlgHom I (Fin P.variableCount) (jacobian hm f').det))) from by ring]
    exact neg_mem (Ideal.mul_mem_left _ b' hdet)
  -- the surjection `ψ : C ⟶ B/IⁿB`
  obtain ⟨ψ, hψsurj, -, -⟩ := exists_algHom_multiJacobianAlgebra_quotient P hIfg n hm f'
    agen c₁ (P.toAlgHom b) b' bs hf'mem hbapprox hbs
  set C := MultiJacobianAlgebra hm f' agen c₁ with hCdef
  have hLn : (I ^ n).map (algebraMap A B.carrier) =
      (I.map (algebraMap A B.carrier)) ^ n := Ideal.map_pow _ _ _
  set ψ' : C →ₐ[A] B.carrier ⧸ (I.map (algebraMap A B.carrier)) ^ n :=
    (Ideal.quotientEquivAlgOfEq A hLn).toAlgHom.comp ψ with hψ'def
  have hψ'surj : Function.Surjective ψ' :=
    (Ideal.quotientEquivAlgOfEq A hLn).surjective.comp hψsurj
  have hkillK : ∀ x : C, x ∈ (I.map (algebraMap A C)) ^ n → ψ' x = 0 := by
    intro x hx
    refine eq_zero_of_mem_map_pow n ψ' x ?_
    rwa [Ideal.map_pow]
  set ψq : C ⧸ (I.map (algebraMap A C)) ^ n →ₐ[A]
      B.carrier ⧸ (I.map (algebraMap A B.carrier)) ^ n :=
    Ideal.Quotient.liftₐ ((I.map (algebraMap A C)) ^ n) ψ' hkillK with hψqdef
  have hψqsurj : Function.Surjective ψq := by
    intro y
    obtain ⟨x, rfl⟩ := hψ'surj y
    exact ⟨Ideal.Quotient.mk _ x, rfl⟩
  set ψn : (adicCompletionObj I (B := C)).carrier →ₐ[A]
      B.carrier ⧸ (I.map (algebraMap A B.carrier)) ^ n :=
    ψq.comp ((AdicCompletion.evalₐ (I.map (algebraMap A C)) n).restrictScalars A) with hψndef
  have hψnsurj : Function.Surjective ψn :=
    hψqsurj.comp (AdicCompletion.surjective_evalₐ (I.map (algebraMap A C)) n)
  -- Stacks 0AK7 lifts `ψn` to an `A`-algebra map `φ : C^∧ → B`
  obtain ⟨φ, hφ⟩ := exists_algHom_lift_of_torsion_disjoint a I hI
    (adicCompletionObj I (B := C)) (multiJacobianCompletedPresentation I hm f' agen c₁) c
    (fun N ξ ↦ by
      rw [← map_pow]
      exact smul_ext_one_multiJacobianCompletedPresentation_eq_zero hm f' agen c₁ hagen.symm
        (a ^ c) (Ideal.pow_mem_pow (hI ▸ Ideal.mem_span_singleton_self a) c) N ξ)
    (C := B.carrier) d hd n hn ψn
  -- `φ` is surjective, because it is surjective modulo `I`
  have hmkφ : ∀ z : B.carrier, ∃ w,
      Ideal.Quotient.mk ((I.map (algebraMap A B.carrier)) ^ (n - c)) (φ w) =
        Ideal.Quotient.mk ((I.map (algebraMap A B.carrier)) ^ (n - c)) z := by
    intro z
    obtain ⟨w, hw⟩ := hψnsurj (Ideal.Quotient.mk ((I.map (algebraMap A B.carrier)) ^ n) z)
    refine ⟨w, ?_⟩
    have hcong := DFunLike.congr_fun hφ w
    rw [AlgHom.comp_apply, AlgHom.comp_apply, hw] at hcong
    exact hcong.symm
  have hmkφL : Function.Surjective
      ((Ideal.Quotient.mk (I.map (algebraMap A B.carrier))).comp φ.toRingHom) := by
    intro y
    obtain ⟨z, rfl⟩ := Ideal.Quotient.mk_surjective (I := I.map (algebraMap A B.carrier)) y
    obtain ⟨w, hw⟩ := hmkφ z
    exact ⟨w, Ideal.Quotient.eq.mpr (Ideal.pow_le_self hnc (Ideal.Quotient.eq.mp hw))⟩
  have hTcomplete : IsAdicComplete
      (I.map (algebraMap A (adicCompletionObj I (B := C)).carrier))
      (adicCompletionObj I (B := C)).carrier := (adicCompletionObj I (B := C)).isAdicallyComplete
  have hMmap : (I.map (algebraMap A (adicCompletionObj I (B := C)).carrier)).map φ.toRingHom =
      I.map (algebraMap A B.carrier) := by
    rw [Ideal.map_map]
    congr 1
    ext y
    exact φ.commutes y
  have hhaus : IsHausdorff ((I.map (algebraMap A (adicCompletionObj I (B := C)).carrier)).map
      φ.toRingHom) B.carrier := by
    rw [hMmap]
    infer_instance
  have hφsurj : Function.Surjective φ :=
    surjective_of_mk_map_comp_surjective
      (I := I.map (algebraMap A (adicCompletionObj I (B := C)).carrier)) φ.toRingHom
      (by rw [hMmap]; exact hmkφL)
  have hsmooth : SmoothAwayFrom A I C :=
    smoothAwayFrom_multiJacobianAlgebra hm f' agen c₁ hagen.symm
  exact ⟨f', c₁, φ, hφsurj, hsmooth, hBsmooth,
    isRigSmooth_adicCompletionObj_of_smoothAwayFrom I hsmooth⟩

/-- **The surjection of Stacks 0GAW over a principal ideal, with no carried hypothesis.**

Let `A` be a Noetherian ring, `I = (a)` principal, and let `B` be an object of the category of
Stacks 0AL4 carrying a Jacobian chart: a completed polynomial presentation
`B = A⟨x₁, …, x_r⟩/J`, an element `b` with `V(b) ⊆ V(IB)`, an integer `m ≤ r` and
`f₁, …, f_m ∈ J` whose Jacobian determinant divides the image of `b`, with
`bJ ⊆ (f₁, …, f_m) + J²`. Then there is a finite type `A`-algebra `C`, smooth over
`Spec(A) ∖ V(I)`, and a surjection `φ : C^∧ → B` of `A`-algebras; moreover both `B` and `C^∧`
are rig-smooth over `(A, I)`.

`C` is the algebra `A[z, x₁, …, x_r]/(zΔ' - a^{c₁}, f'₁, …, f'_m)` of Stacks 0GAV for the
one-element generating family `{a}` of `I`, where the `f'ⱼ` are polynomial approximations to
the `fⱼ` and `I^{c₁}B ⊆ bB`. It maps onto `B/IⁿB`, and that map lifts to `φ` by Stacks 0AK7:
the exponent `c = 1 + ((1+1)c₁ - 1)` of Stacks 0GAV annihilates `Ext¹` out of the completed
naive cotangent complex of `C^∧`, the `a`-power torsion of `B` meets `I^d B` in `0` for some
`d` because `B` is Noetherian, and `n` is taken past `max (2c) (c + d)`.

Lifting through Stacks 0AK7 rather than Stacks 0GAQ is the replacement the source of
Stacks 0ALS points to. It is what removes the `DualSituation` data, the invariants of Local
Cohomology Section 0GA6, the open duality input of Stacks 0GAC, and the restriction that `B`
live in the universe of `A`.

This is Stacks 0GAW up to, but not including, its final step; no `stacks` attribute is placed,
because the tag's statement is the isomorphism `B ≅ C^∧` and the conormal annihilation that
produces it from this surjection is not available. -/
public theorem exists_finiteType_surjection_of_jacobianChart_principal
    (a : A) (hI : I = Ideal.span {a})
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    (m : ℕ) (hm : m ≤ P.variableCount) (b : P.completedPolynomialRing)
    (f : Fin m → P.ker)
    (hvanish : B.adicIdeal ≤ (Ideal.span {P.toAlgHom b}).radical)
    (hjacobian :
      P.toAlgHom (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
          (f j : P.completedPolynomialRing)) ∣ P.toAlgHom b)
    (hrelations : ∀ x : P.completedPolynomialRing, x ∈ P.ker →
      b * x ∈ Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
        P.ker ^ 2) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.FiniteType A C)
      (φ : AdicCompletion (I.map (algebraMap A C)) C →ₐ[A] B.carrier),
      Function.Surjective φ ∧ SmoothAwayFrom A I C ∧
        IsRigSmooth B ∧ IsRigSmooth (adicCompletionObj I (B := C)) := by
  obtain ⟨f', c₁, φ, hφsurj, hsmooth, hBsmooth, hCsmooth⟩ :=
    exists_multiJacobian_surjection_of_jacobianChart_principal a hI B P m hm b f hvanish
      hjacobian hrelations
  exact ⟨MultiJacobianAlgebra hm f' (fun _ : Fin 1 ↦ a) c₁, inferInstance, inferInstance,
    inferInstance, φ, hφsurj, hsmooth, hBsmooth, hCsmooth⟩

/-- **The surjection of Stacks 0ALS, with no carried hypothesis.**

Let `A` be a Noetherian ring, `I = (a)` a principal ideal and `B` an object of the category of
Stacks 0AL4 which is rig-étale over `(A, I)`. Then there is a finite type `A`-algebra `C`,
smooth over `Spec(A) ∖ V(I)`, and a surjection `C^∧ → B` of `A`-algebras, with both `B` and
`C^∧` rig-smooth over `(A, I)`.

The Jacobian chart is supplied by `Rig.exists_jacobianCriterion_of_isRigEtale_principal`, in
the square case `m = r` of Stacks 0AJU part (6), and the surjection by
`Rig.exists_finiteType_surjection_of_jacobianChart_principal`.

Stacks 0ALS asserts more: that `φ` is an *isomorphism*. What is missing is exactly the
annihilation of `Ker(φ)/Ker(φ)²` by a power of `I`, after which Stacks 0ALR
(`exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated`) concludes. No
hypothesis standing in for that annihilation is introduced, and no `stacks` attribute for
0ALS is placed. -/
public theorem exists_finiteType_surjection_of_isRigEtale_principal
    (hI : I.IsPrincipal) (B : AdicFiniteTypeAlgebra.{u, v} A I) (hB : IsRigEtale B) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C) (_ : Algebra.FiniteType A C)
      (φ : AdicCompletion (I.map (algebraMap A C)) C →ₐ[A] B.carrier),
      Function.Surjective φ ∧ SmoothAwayFrom A I C ∧
        IsRigSmooth B ∧ IsRigSmooth (adicCompletionObj I (B := C)) := by
  obtain ⟨a, ha⟩ := hI.principal
  obtain ⟨P⟩ := nonempty_completedPolynomialPresentation hI.fg B
  obtain ⟨b, f, hvanish, hjacobian, hrelations⟩ :=
    exists_jacobianCriterion_of_isRigEtale_principal hI B P hB
  refine exists_finiteType_surjection_of_jacobianChart_principal a ha B P P.variableCount
    le_rfl b f hvanish ?_ (fun x hx ↦ hrelations ⟨x, hx⟩)
  -- the chart of `exists_jacobianCriterion_of_isRigEtale_principal` takes the determinant of
  -- the images; the chart of Stacks 0GAW takes the image of the determinant
  have hbridge : P.toAlgHom (Matrix.det fun i j : Fin P.variableCount ↦
        (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE le_rfl i)
          (f j : P.completedPolynomialRing)) =
      Matrix.det fun i j : Fin P.variableCount ↦ P.toAlgHom
        ((completedNaiveCotangentComplex B P).partialDeriv i
          (f j : P.completedPolynomialRing)) := by
    simp only [Fin.castLE_rfl, id_eq]
    exact RingHom.map_det (P.toAlgHom : P.completedPolynomialRing →+* B.carrier) _
  rw [hbridge]
  exact hjacobian

end Main

end Rig

end
