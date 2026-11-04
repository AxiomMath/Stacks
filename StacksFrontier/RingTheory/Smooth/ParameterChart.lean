module

public import Mathlib.LinearAlgebra.Basis.Exact
public import Mathlib.RingTheory.Etale.Kaehler
public import Mathlib.RingTheory.Smooth.Basic
public import StacksFrontier.RingTheory.Kaehler.Basic
public import StacksFrontier.RingTheory.NaiveCotangent.Defs

/-!
# The parameter chart `B[y]/(π y - g)`

For a ring `B`, an element `π` of `B` and a finite family `g₁, …, g_c` in `B`, the *parameter
chart* is the `B`-algebra

`Q = B[y₁, …, y_c]/(π y₁ - g₁, …, π y_c - g_c)`,

the universal `B`-algebra in which each `gᵢ` becomes divisible by `π`. Its differentials and its
formal smoothness are computed here under the single hypothesis that the differentials
`d g₁, …, d g_c` are part of a basis of `Ω_{B/R}`: in that case the relations are transverse, the
conormal sequence of the presentation splits, and `Ω_{Q/R}` has the basis obtained from the one
upstairs by replacing each `d gᵢ` with `d yᵢ`.

Everything is stated for a basis of `Ω_{B/R}` indexed by `Fin c ⊕ ι`, with the first summand
carrying the `d gᵢ`; the complementary index type `ι` is arbitrary.

## Main definitions

* `parameterChartAlgebra`: the algebra `B[y₁, …, y_c]/(π y₁ - g₁, …, π y_c - g_c)`.

## Main results

* `formallySmooth_and_exists_differentialBasis_parameterChartAlgebra`: the conormal sequence of
  the presentation splits, so the chart is formally smooth over `R` as soon as the polynomial ring
  is, and `Ω_{Q/R}` has the displayed basis.
* `subsingleton_h1Cotangent_parameterChartAlgebra_localization`: the first cotangent homology of
  a localization of the chart vanishes.
* `exists_differentialBasis_parameterChartAlgebra_localization`: the displayed basis of
  differentials on a localization of the chart.
* `mapBaseChange_D_parameterChartAlgebra_localization`: on the chart, `d gᵢ` becomes `π d yᵢ`.
-/

@[expose] public section

universe u v w

open scoped TensorProduct

/-- The parameter chart `B[y₁, …, y_c]/(π y₁ - g₁, …, π y_c - g_c)`: the universal `B`-algebra in
which each `gᵢ` becomes `π` times a chosen element `yᵢ`. -/
abbrev parameterChartAlgebra (B : Type v) [CommRing B] (π : B) (c : ℕ) (g : Fin c → B) : Type v :=
  MvPolynomial (Fin c) B ⧸ Ideal.span (Set.range fun i : Fin c ↦
    MvPolynomial.C π * MvPolynomial.X i - MvPolynomial.C (g i))

/-- A basis of `Ω_{B/R}` extends by the differentials of the variables to a basis of
`Ω_{B[y₁, …, y_c]/R}`. -/
private theorem exists_differentialBasis_mvPolynomial
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (c : ℕ) (κ : Type w) (b : Module.Basis κ B (KaehlerDifferential R B)) :
    ∃ e : Module.Basis (κ ⊕ Fin c) (MvPolynomial (Fin c) B)
        (KaehlerDifferential R (MvPolynomial (Fin c) B)),
      (∀ k, e (Sum.inl k) = KaehlerDifferential.mapBaseChange R B
        (MvPolynomial (Fin c) B) (1 ⊗ₜ[B] b k)) ∧
      (∀ i, e (Sum.inr i) = KaehlerDifferential.D R (MvPolynomial (Fin c) B)
        (MvPolynomial.X i)) := by
  let P := MvPolynomial (Fin c) B
  let f : P ⊗[B] (KaehlerDifferential R B) →ₗ[P] KaehlerDifferential R P :=
    KaehlerDifferential.mapBaseChange R B P
  let g : KaehlerDifferential R P →ₗ[P] KaehlerDifferential B P :=
    KaehlerDifferential.map R B P P
  have hExact : Function.Exact f g := KaehlerDifferential.exact_mapBaseChange_map R B P
  let bP := KaehlerDifferential.mvPolynomialBasis B (Fin c)
  let s : KaehlerDifferential B P →ₗ[P] KaehlerDifferential R P :=
    bP.constr P fun i ↦ KaehlerDifferential.D R P (MvPolynomial.X i)
  have hs : g ∘ₗ s = LinearMap.id := bP.ext fun i ↦ by
    show g (s (bP i)) = bP i
    dsimp [s]
    rw [bP.constr_basis, KaehlerDifferential.map_D R B P P,
      KaehlerDifferential.mvPolynomialBasis_apply]
    simp [P]
  have hInj : Function.Injective f := by
    have hzero : Subsingleton (Algebra.H1Cotangent B P) :=
      Algebra.FormallySmooth.subsingleton_h1Cotangent
    refine (injective_iff_map_eq_zero _).2 fun x hx ↦ ?_
    obtain ⟨z, rfl⟩ := (Algebra.H1Cotangent.exact_δ_mapBaseChange R B P x).mp hx
    simp [Subsingleton.elim z 0]
  let e := (hExact.splitSurjectiveEquiv hInj ⟨s, hs⟩).1.symm
  have he (x : (P ⊗[B] KaehlerDifferential R B) × KaehlerDifferential B P) :
      e x = f x.1 + s x.2 := rfl
  refine ⟨((b.baseChange P).prod bP).map e, fun k ↦ ?_, fun i ↦ ?_⟩
  · rw [Module.Basis.map_apply, Module.Basis.prod_apply, he]
    simp [P, f, Module.Basis.baseChange_apply]
  · rw [Module.Basis.map_apply, Module.Basis.prod_apply, he]
    simp [P, s]

/-- **The parameter chart is transverse.** Suppose the differentials `d g₁, …, d g_c` are the
first members of a basis of `Ω_{B/R}`, indexed by `Fin c ⊕ ι`. Then the conormal sequence of the
presentation `B[y₁, …, y_c] → Q` splits, so `Q` is formally smooth over `R` as soon as
`B[y₁, …, y_c]` is, and `Ω_{Q/R}` has a basis indexed by the same type whose first members are
the `d yᵢ` and whose remaining members are the images of the complementary basis vectors. -/
theorem formallySmooth_and_exists_differentialBasis_parameterChartAlgebra
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (π : R) (c : ℕ) (g : Fin c → B) (ι : Type w)
    (b : Module.Basis (Fin c ⊕ ι) B (KaehlerDifferential R B))
    (hb : ∀ i, b (Sum.inl i) = KaehlerDifferential.D R B (g i)) :
    (Algebra.FormallySmooth R (MvPolynomial (Fin c) B) →
      Algebra.FormallySmooth R (parameterChartAlgebra B (algebraMap R B π) c g)) ∧
      ∃ bQ : Module.Basis (Fin c ⊕ ι)
          (parameterChartAlgebra B (algebraMap R B π) c g)
          (KaehlerDifferential R (parameterChartAlgebra B (algebraMap R B π) c g)),
        (∀ i, bQ (Sum.inl i) = KaehlerDifferential.D R
          (parameterChartAlgebra B (algebraMap R B π) c g)
          (Ideal.Quotient.mk _ (MvPolynomial.X i))) ∧
        (∀ j, bQ (Sum.inr j) = KaehlerDifferential.mapBaseChange R B
          (parameterChartAlgebra B (algebraMap R B π) c g) (1 ⊗ₜ[B] b (Sum.inr j))) := by
  classical
  let P := MvPolynomial (Fin c) B
  let Q := parameterChartAlgebra B (algebraMap R B π) c g
  let rel (i : Fin c) : P :=
    MvPolynomial.C (algebraMap R B π) * MvPolynomial.X i - MvPolynomial.C (g i)
  let I : Ideal P := Ideal.span (Set.range rel)
  have hsurj : Function.Surjective (algebraMap P Q) := Ideal.Quotient.mk_surjective
  obtain ⟨eP, heB, heX⟩ := exists_differentialBasis_mvPolynomial R B c (Fin c ⊕ ι) b
  let v : Module.Basis ((Fin c ⊕ ι) ⊕ Fin c) Q (Q ⊗[P] KaehlerDifferential R P) :=
    eP.baseChange Q
  let φ : Q ⊗[P] KaehlerDifferential R P →ₗ[Q] Q ⊗[P] KaehlerDifferential R P :=
    v.constr Q fun k ↦ match k with
      | Sum.inl (Sum.inl i) => -v (Sum.inl (Sum.inl i)) + algebraMap R Q π • v (Sum.inr i)
      | Sum.inl (Sum.inr j) => v (Sum.inl (Sum.inr j))
      | Sum.inr i => v (Sum.inr i)
  have hφinl (i : Fin c) : φ (v (Sum.inl (Sum.inl i))) =
      -v (Sum.inl (Sum.inl i)) + algebraMap R Q π • v (Sum.inr i) := by
    simp [φ, Module.Basis.constr_basis]
  have hφinr (j : ι) : φ (v (Sum.inl (Sum.inr j))) = v (Sum.inl (Sum.inr j)) := by
    simp [φ, Module.Basis.constr_basis]
  have hφinrc (i : Fin c) : φ (v (Sum.inr i)) = v (Sum.inr i) := by
    simp [φ, Module.Basis.constr_basis]
  have hφ : φ ∘ₗ φ = LinearMap.id := by
    apply LinearMap.ext_on_range v.span_eq
    intro k
    show φ (φ (v k)) = v k
    match k with
    | Sum.inl (Sum.inl i) =>
        rw [hφinl i, map_add, map_neg, map_smul, hφinl i, hφinrc i]
        abel
    | Sum.inl (Sum.inr j) => rw [hφinr j, hφinr j]
    | Sum.inr i => rw [hφinrc i, hφinrc i]
  let φe : (Q ⊗[P] KaehlerDifferential R P) ≃ₗ[Q] (Q ⊗[P] KaehlerDifferential R P) :=
    LinearEquiv.ofInvolutive φ fun x ↦ by
      simpa [LinearMap.comp_apply] using congrArg (fun f : _ →ₗ[Q] _ ↦ f x) hφ
  let v' := v.map φe
  let E : Algebra.Extension R Q :=
    { Ring := P
      commRing := inferInstance
      algebra₁ := inferInstance
      algebra₂ := inferInstance
      isScalarTower := inferInstance
      σ := Function.surjInv hsurj
      algebraMap_σ := Function.surjInv_eq hsurj }
  have hEker : E.ker = I := Ideal.mk_ker (I := I)
  have hrelmem (i : Fin c) : rel i ∈ E.ker := hEker ▸ Ideal.subset_span ⟨i, rfl⟩
  let relClass (i : Fin c) : E.Cotangent := Algebra.Extension.Cotangent.mk ⟨rel i, hrelmem i⟩
  let f : E.Cotangent →ₗ[Q] Q ⊗[P] KaehlerDifferential R P := E.cotangentComplex
  let s : (Q ⊗[P] KaehlerDifferential R P) →ₗ[Q] E.Cotangent :=
    v'.constr Q fun k ↦ match k with
      | Sum.inl (Sum.inl i) => relClass i
      | _ => 0
  have hrelvec (i : Fin c) : f (relClass i) = v' (Sum.inl (Sum.inl i)) := by
    rw [show f (relClass i) = (1 : Q) ⊗ₜ[P] KaehlerDifferential.D R P (rel i) from
      Algebra.Extension.cotangentComplex_mk E ⟨rel i, hrelmem i⟩]
    show (1 : Q) ⊗ₜ[P] KaehlerDifferential.D R P (rel i) = φ (v (Sum.inl (Sum.inl i)))
    simp only [φ, Module.Basis.constr_basis]
    rw [show KaehlerDifferential.D R P (rel i) =
        algebraMap R P π • KaehlerDifferential.D R P (MvPolynomial.X i) -
          KaehlerDifferential.D R P (MvPolynomial.C (g i)) from by
      have hπ : MvPolynomial.C (algebraMap R B π) = algebraMap R P π :=
        IsScalarTower.algebraMap_apply R B P π
      show KaehlerDifferential.D R P
        (MvPolynomial.C (algebraMap R B π) * MvPolynomial.X i - MvPolynomial.C (g i)) = _
      rw [map_sub, (KaehlerDifferential.D R P).leibniz, hπ, Derivation.map_algebraMap]
      simp]
    have hgv : eP (Sum.inl (Sum.inl i)) = KaehlerDifferential.D R P (MvPolynomial.C (g i)) := by
      rw [heB (Sum.inl i), hb i, KaehlerDifferential.mapBaseChange_tmul, one_smul]
      exact KaehlerDifferential.map_D R R B P (g i)
    simp only [v, Module.Basis.baseChange_apply]
    rw [heX i, hgv]
    have hsmul : (1 : Q) ⊗ₜ[P]
          (algebraMap R P π • KaehlerDifferential.D R P (MvPolynomial.X i)) =
        algebraMap R Q π • ((1 : Q) ⊗ₜ[P] KaehlerDifferential.D R P (MvPolynomial.X i)) := by
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul',
        IsScalarTower.algebraMap_apply R P Q π]
      rfl
    rw [TensorProduct.tmul_sub, hsmul]
    abel
  have hspan : Submodule.span Q (Set.range relClass) = ⊤ :=
    Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker (P := E) rel hEker.symm
  have hs : s ∘ₗ f = LinearMap.id := by
    apply LinearMap.ext_on_range hspan
    intro i
    show s (f (relClass i)) = relClass i
    rw [hrelvec]
    simp [s, Module.Basis.constr_basis]
  have hformal (hP : Algebra.FormallySmooth R P) : Algebra.FormallySmooth R Q := by
    have : Algebra.FormallySmooth R E.Ring := hP
    exact (Algebra.Extension.formallySmooth_iff_split_injection E).2 ⟨s, hs⟩
  let gQ : Q ⊗[P] KaehlerDifferential R P →ₗ[Q] KaehlerDifferential R Q :=
    KaehlerDifferential.mapBaseChange R P Q
  have hfg : Function.Exact f gQ := E.exact_cotangentComplex_toKaehler
  let a : Fin c ⊕ ι → (Fin c ⊕ ι) ⊕ Fin c :=
    Sum.elim (fun i ↦ Sum.inr i) fun j ↦ Sum.inl (Sum.inr j)
  let d : Fin c → (Fin c ⊕ ι) ⊕ Fin c := fun i ↦ Sum.inl (Sum.inl i)
  have ha : Function.Injective a := Sum.elim_injective.2
    ⟨Sum.inr_injective, fun j k h ↦ Sum.inr.inj (Sum.inl.inj h), fun i j h ↦ by cases h⟩
  have hsa : ∀ k, s (v' (a k)) = 0 := by
    rintro (i | j) <;> simp [a, s, Module.Basis.constr_basis]
  have hsd (i : Fin c) : s (v' (d i)) = relClass i := by
    rw [← hrelvec i]
    simpa [f] using DFunLike.congr_fun hs (relClass i)
  have hd : Function.Injective d := fun x y h ↦ Sum.inl.inj (Sum.inl.inj h)
  have hliRel : LinearIndependent Q relClass := by
    apply LinearIndependent.of_comp f
    simpa [Function.comp_def, hrelvec] using v'.linearIndependent.comp d hd
  have hlib : LinearIndependent Q (s ∘ v' ∘ d) := by
    convert hliRel using 1
    exact funext hsd
  have hab : Codisjoint (Set.range a) (Set.range d) := by
    simp only [codisjoint_iff, Set.sup_eq_union, Set.top_eq_univ]
    ext k
    rcases k with (i | j) | i <;> simp [a, d]
  have hgQ (k) (hk : φ (v k) = v k) :
      gQ (v' k) = KaehlerDifferential.mapBaseChange R P Q (1 ⊗ₜ[P] eP k) := by
    have : v' k = v k := hk
    rw [this, Module.Basis.baseChange_apply]
  have hgoalInr (i : Fin c) : gQ (v' (Sum.inr i)) =
      KaehlerDifferential.D R Q (Ideal.Quotient.mk _ (MvPolynomial.X i)) := by
    rw [hgQ _ (hφinrc i), KaehlerDifferential.mapBaseChange_tmul, one_smul, heX,
      KaehlerDifferential.map_D]
    rfl
  have hgoalInlInr (j : ι) : gQ (v' (Sum.inl (Sum.inr j))) =
      KaehlerDifferential.mapBaseChange R B Q (1 ⊗ₜ[B] b (Sum.inr j)) := by
    rw [hgQ _ (hφinr j), heB (Sum.inr j)]
    simp only [KaehlerDifferential.mapBaseChange_tmul, one_smul]
    rw [← KaehlerDifferential.map_comp_map R B P Q]
    rfl
  clear_value s v'
  refine ⟨hformal, Module.Basis.ofSplitExact hs hfg
      E.toKaehler_surjective v' ha hsa hlib hab, fun i ↦ ?_, fun j ↦ ?_⟩
  · rw [Module.Basis.ofSplitExact_apply]
    simpa only [a, Sum.elim_inl] using hgoalInr i
  · rw [Module.Basis.ofSplitExact_apply]
    simpa only [a, Sum.elim_inr] using hgoalInlInr j

/-- On a parameter chart whose `d gᵢ` are part of a basis of `Ω_{B/R}`, with `B` smooth over `R`,
the first cotangent homology of any localization at a prime vanishes. -/
theorem subsingleton_h1Cotangent_parameterChartAlgebra_localization
    (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
    (hsm : Algebra.Smooth R B) (π : R) (c : ℕ) (g : Fin c → B) (ι : Type w)
    (b : Module.Basis (Fin c ⊕ ι) B (KaehlerDifferential R B))
    (hb : ∀ i, b (Sum.inl i) = KaehlerDifferential.D R B (g i))
    (q : Ideal (parameterChartAlgebra B (algebraMap R B π) c g)) (hq : q.IsPrime) :
    Subsingleton (Algebra.H1Cotangent R (Localization.AtPrime q)) := by
  let Q := parameterChartAlgebra B (algebraMap R B π) c g
  let C := Localization.AtPrime q
  have _ : q.IsPrime := hq
  have _ : Algebra.FormallySmooth R B := hsm.formallySmooth
  have _ : Algebra.FormallySmooth R Q :=
    (formallySmooth_and_exists_differentialBasis_parameterChartAlgebra R B π c g ι b hb).1
      (Algebra.FormallySmooth.comp R B (MvPolynomial (Fin c) B))
  have _ : Algebra.FormallySmooth Q C := Algebra.FormallySmooth.of_isLocalization q.primeCompl
  have _ : Algebra.FormallySmooth R C := Algebra.FormallySmooth.comp R Q C
  exact Algebra.FormallySmooth.subsingleton_h1Cotangent

section Localized

variable (R : Type u) (B : Type v) [CommRing R] [CommRing B] [Algebra R B]
  (π : R) (c : ℕ) (g : Fin c → B)
  (q : Ideal (parameterChartAlgebra B (algebraMap R B π) c g)) [q.IsPrime]
  (D : Type*) [CommRing D] [Algebra R D] [Algebra B D]
  [Algebra (parameterChartAlgebra B (algebraMap R B π) c g) D] [IsLocalization.AtPrime D q]
  [IsScalarTower R B D] [IsScalarTower R (parameterChartAlgebra B (algebraMap R B π) c g) D]
  [IsScalarTower B (parameterChartAlgebra B (algebraMap R B π) c g) D]

include q in
/-- On a localization of a parameter chart at a prime, the differentials `d yᵢ` followed by the
images of the complementary basis vectors of `Ω_{B/R}` form a basis of the relative
differentials. -/
theorem exists_differentialBasis_parameterChartAlgebra_localization
    (ι : Type w) (b : Module.Basis (Fin c ⊕ ι) B (KaehlerDifferential R B))
    (hb : ∀ i, b (Sum.inl i) = KaehlerDifferential.D R B (g i)) :
    ∃ b' : Module.Basis (Fin c ⊕ ι) D (KaehlerDifferential R D),
      (∀ i, b' (Sum.inl i) =
        KaehlerDifferential.D R D
          (algebraMap (parameterChartAlgebra B (algebraMap R B π) c g) D
            (Ideal.Quotient.mk _ (MvPolynomial.X i)))) ∧
      (∀ j, b' (Sum.inr j) =
        KaehlerDifferential.mapBaseChange R B D (1 ⊗ₜ[B] b (Sum.inr j))) := by
  let Q := parameterChartAlgebra B (algebraMap R B π) c g
  have _ : Algebra.FormallyEtale Q D := Algebra.FormallyEtale.of_isLocalization q.primeCompl
  obtain ⟨bQ, hbQ₁, hbQ₂⟩ :=
    (formallySmooth_and_exists_differentialBasis_parameterChartAlgebra R B π c g ι b hb).2
  let e := KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale R Q D
  refine ⟨(bQ.baseChange D).map e, fun i ↦ ?_, fun j ↦ ?_⟩
  · rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hbQ₁]
    show e (1 ⊗ₜ[Q] KaehlerDifferential.D R Q (Ideal.Quotient.mk _ (MvPolynomial.X i))) = _
    simp [e, KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale_apply,
      KaehlerDifferential.mapBaseChange_tmul, KaehlerDifferential.map_D, Q]
  · rw [Module.Basis.map_apply, Module.Basis.baseChange_apply, hbQ₂]
    show KaehlerDifferential.mapBaseChange R Q D
      (1 ⊗ₜ[Q] KaehlerDifferential.mapBaseChange R B Q (1 ⊗ₜ[B] b (Sum.inr j))) = _
    simp only [KaehlerDifferential.mapBaseChange_tmul, one_smul]
    rw [← KaehlerDifferential.map_comp_map R B Q D]
    simp only [LinearMap.comp_apply]
    rfl

/-- Under the base-change map to a localization of a parameter chart, `d gᵢ` becomes
`π · d yᵢ`. -/
theorem mapBaseChange_D_parameterChartAlgebra_localization (i : Fin c) :
    KaehlerDifferential.mapBaseChange R B D (1 ⊗ₜ[B] KaehlerDifferential.D R B (g i)) =
      algebraMap R D π •
        KaehlerDifferential.D R D
          (algebraMap (parameterChartAlgebra B (algebraMap R B π) c g) D
            (Ideal.Quotient.mk _ (MvPolynomial.X i))) := by
  have hqrel : algebraMap B (parameterChartAlgebra B (algebraMap R B π) c g) (g i) =
      algebraMap R (parameterChartAlgebra B (algebraMap R B π) c g) π *
        Ideal.Quotient.mk _ (MvPolynomial.X i) := by
    refine (sub_eq_zero.mp ?_).symm
    show Ideal.Quotient.mk
      (Ideal.span (Set.range fun j : Fin c ↦
        MvPolynomial.C (algebraMap R B π) * MvPolynomial.X j - MvPolynomial.C (g j)))
      (MvPolynomial.C (algebraMap R B π) * MvPolynomial.X i - MvPolynomial.C (g i)) = 0
    exact Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨i, rfl⟩)
  have hrel : algebraMap B D (g i) = algebraMap R D π *
      algebraMap (parameterChartAlgebra B (algebraMap R B π) c g) D
        (Ideal.Quotient.mk _ (MvPolynomial.X i)) := by
    rw [IsScalarTower.algebraMap_apply B (parameterChartAlgebra B (algebraMap R B π) c g) D,
      hqrel, map_mul, ← IsScalarTower.algebraMap_apply R _ D π]
  rw [KaehlerDifferential.mapBaseChange_tmul, one_smul, KaehlerDifferential.map_D R R B D, hrel,
    Derivation.leibniz, Derivation.map_algebraMap, smul_zero, add_zero]

end Localized

end
