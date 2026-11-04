module

public import StacksFrontier.RingTheory.AdicCompletion.Algebraization
public import StacksFrontier.RingTheory.Rig.JacobianAlgebraization
public import StacksFrontier.RingTheory.Rig.JacobianAlgebraizationApprox
public import StacksFrontier.RingTheory.Rig.LiftingUniformity
public import StacksFrontier.RingTheory.Rig.NaiveCotangent.ExtAnnihilation

/-!
# The Jacobian criterion for algebraization

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `B` an `I`-adically complete `A`-algebra of
finite type modulo `I`, presented as `B = A⟨x₁, …, x_r⟩/J`.  Suppose given `b`, an integer
`m ≤ r` and `f₁, …, f_m ∈ J` with `V(b) ⊆ V(IB)`, with the Jacobian determinant
`Δ = det(∂fⱼ/∂xᵢ)_{i, j ≤ m}` dividing `b`, and with `bJ ⊆ (f₁, …, f_m) + J²`.  Then `B` is the
`I`-adic completion of a finite type `A`-algebra.

## Main results

* `Rig.retractionIdeal_comp_le` — composing a linear map with any map out of its target can
  only shrink the retraction ideal.
* `Rig.det_pderiv_mem_retractionIdeal_of_le` — for a presentation with fewer relations than
  variables, the image of the Jacobian determinant formed from an initial segment of the
  variables lies in the retraction ideal of the differential.
* `Rig.smoothAwayFrom_multiJacobianAlgebra` — the multi-generator Jacobian algebra is smooth
  over `Spec(A) ∖ V(I)`.
* `Rig.smul_ext_one_multiJacobianCompletedPresentation_eq_zero` — a power of `I` with an
  exponent depending only on the number of generators of `I` and on the divisibility exponent
  annihilates `Ext¹` out of the completed naive cotangent complex of the completion of the
  multi-generator Jacobian algebra.
* `Rig.coefficientProjection_det_partialDerivative_sub_eq_zero` and
  `Rig.det_partialDeriv_sub_restrictedToAlgHom_det_mem` — polynomial approximations have
  approximately the same Jacobian determinant, in the coefficients and in `B`.
* `Rig.exists_finiteType_algEquiv_adicCompletion_of_jacobianChart` — **Stacks 0GAW**, with the
  hypotheses the library's Stacks 0GAQ carries made explicit.

## References

* [Stacks Project, Tag 0GAW](https://stacks.math.columbia.edu/tag/0GAW)
* [Stacks Project, Tag 0GAQ](https://stacks.math.columbia.edu/tag/0GAQ)
* [Stacks Project, Tag 0GAV](https://stacks.math.columbia.edu/tag/0GAV)
* [Stacks Project, Tag 0ALR](https://stacks.math.columbia.edu/tag/0ALR)
-/

@[expose] public noncomputable section

open CategoryTheory MvPolynomial

namespace Rig

universe u v

attribute [local instance] HasDerivedCategory.standard

section Retraction

variable {R : Type*} [CommRing R] {D E F : Type*} [AddCommGroup D] [Module R D]
  [AddCommGroup E] [Module R E] [AddCommGroup F] [Module R F]

/-- Postcomposing a linear map with a further map out of its target can only shrink the
retraction ideal: a retraction of `p ∘ d` composed with `p` is a retraction of `d`. -/
public theorem retractionIdeal_comp_le (d : D →ₗ[R] E) (p : E →ₗ[R] F) :
    retractionIdeal (p ∘ₗ d) ≤ retractionIdeal d := by
  rintro a ⟨h, hh⟩
  exact ⟨h ∘ₗ p, by rw [← hh]; rfl⟩

end Retraction

section NonSquarePresentation

variable {A : Type u} [CommRing A] {B : Type v} [CommRing B] [Algebra A B] {M N : ℕ}

/-- For a presentation of `B` by `N` variables with `M ≤ N` relations `f₁, …, f_M` generating
the kernel, the image in `B` of the Jacobian determinant `det(∂fⱼ/∂xᵢ)_{i, j ≤ M}` formed from
the first `M` variables lies in the retraction ideal of the differential of the naive cotangent
complex.

Cramer's rule gives a retraction of the composite of the differential with the projection onto
the first `M` coordinates, and a retraction of that composite yields one of the differential
itself. -/
public theorem det_pderiv_mem_retractionIdeal_of_le (hMN : M ≤ N)
    (G : Algebra.Generators A B (Fin N)) (rel : Fin M → G.Ring)
    (hrel : Ideal.span (Set.range rel) = G.toExtension.ker) :
    algebraMap G.Ring B (jacobian hMN rel).det ∈
      retractionIdeal (presentationDifferential G) := by
  classical
  have hspan := Algebra.Extension.Cotangent.span_eq_top_of_span_eq_ker
    (P := G.toExtension) rel hrel
  set p : (Fin N → B) →ₗ[B] (Fin M → B) := LinearMap.funLeft B B (Fin.castLE hMN) with hp
  have hd : ∀ (j i : Fin M),
      (p ∘ₗ presentationDifferential G) (Algebra.Extension.Cotangent.mk
          ⟨rel j, hrel.le (Ideal.subset_span ⟨j, rfl⟩)⟩) i =
        algebraMap G.Ring B (MvPolynomial.pderiv (Fin.castLE hMN i) (rel j)) := by
    intro j i
    change presentationDifferential G _ (Fin.castLE hMN i) = _
    rw [presentationDifferential_mk]
  have hmain := det_mem_retractionIdeal_of_span (p ∘ₗ presentationDifferential G)
    (fun j ↦ Algebra.Extension.Cotangent.mk ⟨rel j, hrel.le (Ideal.subset_span ⟨j, rfl⟩)⟩)
    hspan
    (Matrix.of fun i j ↦ algebraMap G.Ring B (MvPolynomial.pderiv (Fin.castLE hMN i) (rel j)))
    (fun j i ↦ hd j i)
  refine retractionIdeal_comp_le (presentationDifferential G) p ?_
  rwa [show (Matrix.of fun i j : Fin M ↦
        algebraMap G.Ring B (MvPolynomial.pderiv (Fin.castLE hMN i) (rel j))).det =
      algebraMap G.Ring B (jacobian hMN rel).det from
    (RingHom.map_det (algebraMap G.Ring B) (jacobian hMN rel)).symm] at hmain

/-- Each generator `a_k` of `I` has the power `a_k ^ ((t+1)c)` in the retraction ideal of the
differential of the naive presentation of the multi-generator Jacobian algebra, since
`a_k ^ c = z_kΔ` there and `Δ^{t+1}` lies in the retraction ideal. -/
private theorem pow_mem_retractionIdeal_multiJacobian {r m t : ℕ} (hm : m ≤ r)
    (f : Fin m → MvPolynomial (Fin r) A) (a : Fin t → A) (c : ℕ) (k : Fin t) :
    algebraMap A (MultiJacobianAlgebra hm f a c) (a k) ^ ((t + 1) * c) ∈
      retractionIdeal (presentationDifferential
        (Algebra.Generators.naive (R := A)
          (I := Ideal.span (Set.range (multiJacobianRelations hm f a c))))) := by
  classical
  set C := MultiJacobianAlgebra hm f a c with hC
  set rel := multiJacobianRelations hm f a c with hreldef
  set Isp : Ideal (MvPolynomial (Fin (t + r)) A) := Ideal.span (Set.range rel) with hIsp
  set h' : t + m ≤ t + r := Nat.add_le_add_left hm t with hh'
  set G := Algebra.Generators.naive (R := A) (I := Isp) with hG
  -- the determinant `Δ^{t+1}` of the full system lies in the retraction ideal
  have hdet : algebraMap G.Ring C (jacobian h' rel).det ∈
      retractionIdeal (presentationDifferential G) :=
    det_pderiv_mem_retractionIdeal_of_le h' G rel (Algebra.Generators.ker_naive _ _).symm
  rw [show (jacobian h' rel).det =
      rename (Fin.natAdd t) (jacobian hm f).det ^ (t + 1) from
    det_pderiv_multiJacobianRelations hm h' f a c, map_pow] at hdet
  have hrelk : Ideal.Quotient.mk Isp (rel (Fin.castAdd m k)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.subset_span ⟨Fin.castAdd m k, rfl⟩)
  rw [hreldef, multiJacobianRelations_castAdd, map_sub, sub_eq_zero, map_mul] at hrelk
  rw [← map_pow,
    show a k ^ ((t + 1) * c) = (a k ^ c) ^ (t + 1) by rw [mul_comm, pow_mul], map_pow,
    show algebraMap A C (a k ^ c) =
      Ideal.Quotient.mk Isp (X (Fin.castAdd r k)) *
        Ideal.Quotient.mk Isp (rename (Fin.natAdd t) (jacobian hm f).det) from hrelk.symm,
    mul_pow]
  exact Ideal.mul_mem_left _ _ hdet

end NonSquarePresentation

section MultiSmooth

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {r m t : ℕ}

/-- **The multi-generator Jacobian algebra is smooth away from `V(I)`.** For `I = (a₁, …, a_t)`
the algebra `C = A[z₁, …, z_t, x₁, …, x_r]/(z₁Δ - a₁^c, …, z_tΔ - a_t^c, f₁, …, f_m)` is smooth
over `Spec(A) ∖ V(I)`: the Jacobian determinant of its presentation is `Δ^{t+1}`, and
`a_k^c = z_kΔ` in `C`, so each generator `a_k` of `I` has a power in the retraction ideal of the
differential. -/
public theorem smoothAwayFrom_multiJacobianAlgebra (hm : m ≤ r)
    (f : Fin m → MvPolynomial (Fin r) A) (a : Fin t → A) (c : ℕ) {I : Ideal A}
    (hI : I = Ideal.span (Set.range a)) :
    SmoothAwayFrom A I (MultiJacobianAlgebra hm f a c) := by
  classical
  rw [smoothAwayFrom_iff_le_radical_retractionIdeal (I := I)
      (Algebra.Generators.naive (R := A)
        (I := Ideal.span (Set.range (multiJacobianRelations hm f a c)))), hI, Ideal.map_span,
    ← Set.range_comp]
  refine Ideal.span_le.mpr ?_
  rintro y ⟨k, rfl⟩
  exact Ideal.mem_radical_iff.mpr ⟨(t + 1) * c, by
    rw [Function.comp_apply]; exact pow_mem_retractionIdeal_multiJacobian hm f a c k⟩

end MultiSmooth

section FactorizationTransfer

open scoped TensorProduct

/-- A chain map of two-term complexes which is bijective in both degrees carries a
factorization of multiplication by a scalar through the differential of its source to one
through the differential of its target. -/
private theorem exists_retraction_of_bijective_chainMap {R : Type*} [CommRing R]
    {X Y : NaiveCotangent.TwoTerm R} (φ : NaiveCotangent.ChainMap X Y)
    (h1 : Function.Bijective φ.f₁) (h0 : Function.Bijective φ.f₀) (y : R)
    (l : X.X₀ →ₗ[R] X.X₁) (hl : l ∘ₗ X.d = y • LinearMap.id) :
    ∃ L : Y.X₀ →ₗ[R] Y.X₁, L ∘ₗ Y.d = y • LinearMap.id := by
  let e1 := LinearEquiv.ofBijective φ.f₁ h1
  let e0 := LinearEquiv.ofBijective φ.f₀ h0
  refine ⟨e1.toLinearMap ∘ₗ l ∘ₗ e0.symm.toLinearMap, ?_⟩
  ext z
  obtain ⟨w, rfl⟩ := h1.surjective z
  have hstep : Y.d (φ.f₁ w) = φ.f₀ (X.d w) := LinearMap.congr_fun φ.comm w
  have hlw : l (X.d w) = y • w := LinearMap.congr_fun hl w
  change e1 (l (e0.symm (Y.d (φ.f₁ w)))) = y • φ.f₁ w
  rw [hstep, show e0.symm (φ.f₀ (X.d w)) = X.d w from e0.symm_apply_apply (X.d w), hlw,
    map_smul]
  rfl

/-- The base change of multiplication by a scalar is multiplication by its image. -/
private theorem baseChange_smul_id_eq {R : Type*} [CommRing R] {M : Type*} [AddCommGroup M]
    [Module R M] (T : Type*) [CommRing T] [Algebra R T] (y : R) :
    LinearMap.baseChange T (y • (LinearMap.id : M →ₗ[R] M)) =
      (algebraMap R T y) • (LinearMap.id : T ⊗[R] M →ₗ[T] T ⊗[R] M) := by
  ext x
  change ((1 : T) ⊗ₜ[R] (y • x) : T ⊗[R] M) = (algebraMap R T y) • ((1 : T) ⊗ₜ[R] x)
  rw [TensorProduct.tmul_smul, algebraMap_smul]

variable {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {Bc : Type v} [CommRing Bc]
  [Algebra A Bc] [Algebra.FiniteType A Bc] {nv : ℕ} (G : Algebra.Generators A Bc (Fin nv))

/-- The base change to `Bc^` of a factorization of multiplication by `y` through the
differential of a presentation of `Bc`. -/
private theorem baseChange_comp_presentationDifferential_eq (y : A)
    (h : (Fin nv → Bc) →ₗ[Bc] G.toExtension.Cotangent)
    (hh : h ∘ₗ presentationDifferential G = (algebraMap A Bc y) • LinearMap.id) :
    LinearMap.baseChange (adicCompletionObj I (B := Bc)).carrier h ∘ₗ
        LinearMap.baseChange (adicCompletionObj I (B := Bc)).carrier
          (presentationDifferential G) =
      (algebraMap A (adicCompletionObj I (B := Bc)).carrier y) •
        (LinearMap.id : (adicCompletionObj I (B := Bc)).carrier ⊗[Bc] G.toExtension.Cotangent
          →ₗ[(adicCompletionObj I (B := Bc)).carrier] _) := by
  rw [← LinearMap.baseChange_comp, hh, baseChange_smul_id_eq,
    ← IsScalarTower.algebraMap_apply A Bc (adicCompletionObj I (B := Bc)).carrier y]

/-- **Stacks 0GAF transfer.** A factorization of multiplication by `y : A` through the
differential of a presentation of `Bc` gives one through the differential of the completed naive
cotangent complex of the completed presentation, because the comparison of complexes of
Stacks 0GAF is bijective in both degrees. -/
private theorem exists_factorization_completed (y : A)
    (h : (Fin nv → Bc) →ₗ[Bc] G.toExtension.Cotangent)
    (hh : h ∘ₗ presentationDifferential G = (algebraMap A Bc y) • LinearMap.id) :
    ∃ H : (Fin nv → (adicCompletionObj I (B := Bc)).carrier)
        →ₗ[(adicCompletionObj I (B := Bc)).carrier]
        (presentationCompletion I G).extension.Cotangent,
      H ∘ₗ (completedComplex I G).differential =
        (algebraMap A (adicCompletionObj I (B := Bc)).carrier y) • LinearMap.id :=
  exists_retraction_of_bijective_chainMap (completionComparison I G)
    (bijective_completionComparison_f₁ I G) (bijective_completionComparison_f₀ I G) _
    (LinearMap.baseChange (adicCompletionObj I (B := Bc)).carrier h)
    (baseChange_comp_presentationDifferential_eq I G y h hh)

end FactorizationTransfer

section ExtFromFactorization

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- A factorization of multiplication by `y ∈ B` through the differential `J/J² → ⨁ i, B dxᵢ`
of a completed polynomial presentation makes `y` annihilate `Ext¹_B(NL^∧_{B/A}, N)` for every
`B`-module `N`.  This is `Rig.smul_ext_one_derived_iff_exists_factorization` read on the
differential itself rather than on the universe-lifted cochain complex. -/
private theorem smul_ext_one_of_factorization_differential
    (B : AdicFiniteTypeAlgebra.{u, v} A I) (P : CompletedPolynomialPresentation I B)
    (y : B.carrier)
    (h : (Fin P.variableCount → B.carrier) →ₗ[B.carrier] P.extension.Cotangent)
    (hh : h ∘ₗ (completedNaiveCotangentComplex B P).differential = y • LinearMap.id) :
    ∀ (N : ModuleCat.{max u v} B.carrier)
      (ξ : DerivedCategory.Ext
        (DerivedCategory.Q.obj (completedNaiveCotangentComplex B P).cochainComplex)
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} B.carrier) 0).obj N) 1),
      y • ξ = 0 := by
  classical
  set K := completedNaiveCotangentComplex B P with hK
  set g : CompletedNaiveCotangentComplex.LiftedDifferentials (P := P) →ₗ[B.carrier]
      CompletedNaiveCotangentComplex.LiftedCotangent (P := P) :=
    ULift.moduleEquiv.symm.toLinearMap ∘ₗ h ∘ₗ ULift.moduleEquiv.toLinearMap with hg
  have hglift : g ∘ₗ K.liftedDifferential = y • LinearMap.id := by
    refine LinearMap.ext fun x ↦ ?_
    obtain ⟨x⟩ := x
    change ULift.up (h (K.differential x)) = y • ULift.up x
    rw [show h (K.differential x) = y • x from LinearMap.congr_fun hh x]
    rfl
  refine (smul_ext_one_derived_iff_exists_factorization B P y).mpr
    ⟨K.degreeZeroIso.hom ≫ ModuleCat.ofHom g ≫ K.degreeNegOneIso.inv, ?_⟩
  calc K.cochainComplex.d (-1) 0 ≫
        (K.degreeZeroIso.hom ≫ ModuleCat.ofHom g ≫ K.degreeNegOneIso.inv)
      = K.degreeNegOneIso.hom ≫ ModuleCat.ofHom (g.comp K.liftedDifferential) ≫
          K.degreeNegOneIso.inv := by
        rw [K.cochainComplex_d]
        simp [Category.assoc, ModuleCat.ofHom_comp]
    _ = K.degreeNegOneIso.hom ≫ ModuleCat.ofHom (y • LinearMap.id) ≫
          K.degreeNegOneIso.inv := by rw [hglift]
    _ = K.degreeNegOneIso.hom ≫
          (y • 𝟙 (ModuleCat.of B.carrier (CompletedNaiveCotangentComplex.LiftedCotangent
            (P := P)))) ≫ K.degreeNegOneIso.inv := by congr 1
    _ = y • 𝟙 (K.cochainComplex.X (-1)) := by
        calc K.degreeNegOneIso.hom ≫
              (y • 𝟙 (ModuleCat.of B.carrier (CompletedNaiveCotangentComplex.LiftedCotangent
                (P := P)))) ≫ K.degreeNegOneIso.inv
            = y • (K.degreeNegOneIso.hom ≫ 𝟙 _ ≫ K.degreeNegOneIso.inv) := by
              simp [Linear.smul_comp, Linear.comp_smul]
          _ = _ := by
              congr 1
              change K.degreeNegOneIso.hom ≫ K.degreeNegOneIso.inv = _
              rw [Iso.hom_inv_id]

end ExtFromFactorization

section MultiExt

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {r m t : ℕ}

/-- The naive presentation of the multi-generator Jacobian algebra by the `t + r` variables
`z₁, …, z_t, x₁, …, x_r`. -/
public abbrev multiJacobianGenerators (hm : m ≤ r) (f : Fin m → MvPolynomial (Fin r) A)
    (a : Fin t → A) (c : ℕ) :
    Algebra.Generators A (MultiJacobianAlgebra hm f a c) (Fin (t + r)) :=
  Algebra.Generators.naive (R := A)
    (I := Ideal.span (Set.range (multiJacobianRelations hm f a c)))

/-- The completed presentation of `C^∧` determined by the naive presentation of the
multi-generator Jacobian algebra `C`. -/
public abbrev multiJacobianCompletedPresentation (I : Ideal A) (hm : m ≤ r)
    (f : Fin m → MvPolynomial (Fin r) A) (a : Fin t → A) (c : ℕ) :
    CompletedPolynomialPresentation I
      (adicCompletionObj I (B := MultiJacobianAlgebra hm f a c)) :=
  presentationCompletion I (multiJacobianGenerators hm f a c)

/-- **A power of `I` with an explicit exponent annihilates `Ext¹` of the completed naive
cotangent complex of `C^∧`.** For `I = (a₁, …, a_t)` and
`C = A[z₁, …, z_t, x₁, …, x_r]/(z₁Δ - a₁^c, …, z_tΔ - a_t^c, f₁, …, f_m)`, every element of
`I^{1 + t((t+1)c - 1)}` annihilates `Ext¹_{C^∧}(NL^∧_{C^∧/A}, N)` for every `C^∧`-module `N`.

The exponent depends only on `t` and `c`; in particular it does not depend on `r`, on the
polynomials `fⱼ`, nor on any accuracy to which those polynomials approximate a given system.
That independence is what makes the exponent usable as the `c` of Stacks 0GAQ when the `fⱼ`
are themselves obtained by approximating to an accuracy chosen in terms of it. -/
public theorem smul_ext_one_multiJacobianCompletedPresentation_eq_zero (hm : m ≤ r)
    (f : Fin m → MvPolynomial (Fin r) A) (a : Fin t → A) (c : ℕ) {I : Ideal A}
    (hI : I = Ideal.span (Set.range a)) (y : A)
    (hy : y ∈ I ^ (1 + t * ((t + 1) * c - 1)))
    (N : ModuleCat.{u} (adicCompletionObj I (B := MultiJacobianAlgebra hm f a c)).carrier)
    (ξ : DerivedCategory.Ext
      (DerivedCategory.Q.obj (completedNaiveCotangentComplex
        (adicCompletionObj I (B := MultiJacobianAlgebra hm f a c))
        (multiJacobianCompletedPresentation I hm f a c)).cochainComplex)
      ((DerivedCategory.singleFunctor
        (ModuleCat.{u} (adicCompletionObj I (B := MultiJacobianAlgebra hm f a c)).carrier)
        0).obj N) 1) :
    algebraMap A (adicCompletionObj I (B := MultiJacobianAlgebra hm f a c)).carrier y • ξ = 0 := by
  classical
  set C := MultiJacobianAlgebra hm f a c with hC
  set G := multiJacobianGenerators hm f a c with hG
  -- the pigeonhole bound on the exponent
  have hle : (I.map (algebraMap A C)) ^ (1 + t * ((t + 1) * c - 1)) ≤
      retractionIdeal (presentationDifferential G) := by
    rw [hI, Ideal.map_span, ← Set.range_comp]
    exact span_range_pow_le_of_forall_pow_mem (fun k ↦ algebraMap A C (a k)) ((t + 1) * c) _
      (pow_mem_retractionIdeal_multiJacobian hm f a c)
  have hmem : algebraMap A C y ∈ retractionIdeal (presentationDifferential G) := by
    refine hle ?_
    rw [← Ideal.map_pow]
    exact Ideal.mem_map_of_mem _ hy
  obtain ⟨hret, hhret⟩ := hmem
  obtain ⟨H, hH⟩ := exists_factorization_completed I G y hret hhret
  exact smul_ext_one_of_factorization_differential _ (multiJacobianCompletedPresentation I hm f a c)
    _ H hH N ξ

end MultiExt

section DeterminantApproximation

open RestrictedPowerSeries

variable {A : Type u} [CommRing A]

/-- The level `n` coefficient reduction commutes with formal partial differentiation: both are
computed coefficient quotient by coefficient quotient, where the identity is
`MvPolynomial.pderiv_map`. -/
public theorem coefficientProjection_partialDerivative (I : Ideal A) (σ : Type v) (i : σ) (n : ℕ)
    (g : RestrictedPowerSeries I σ) :
    coefficientProjection I σ n (partialDerivative I i g) =
      MvPolynomial.pderiv i (coefficientProjection I σ n g) := rfl

/-- **Polynomial approximations have approximately the same Jacobian determinant.** If each
polynomial `fⱼ` agrees with the restricted power series `gⱼ` modulo `I^n` in every coefficient,
then the Jacobian determinant `det(∂fⱼ/∂xᵢ)` of the approximations agrees modulo `I^n` in every
coefficient with the Jacobian determinant of the `gⱼ`. -/
public theorem coefficientProjection_det_partialDerivative_sub_eq_zero (I : Ideal A) {r m : ℕ}
    (hm : m ≤ r) (n : ℕ) (g : Fin m → RestrictedPowerSeries I (Fin r))
    (f : Fin m → MvPolynomial (Fin r) A)
    (hgf : ∀ j, coefficientProjection I (Fin r) n
      (g j - polynomialRingHom I (Fin r) (f j)) = 0) :
    coefficientProjection I (Fin r) n
        ((Matrix.det fun i j : Fin m ↦ partialDerivative I (Fin.castLE hm i) (g j)) -
          polynomialRingHom I (Fin r) (jacobian hm f).det) = 0 := by
  classical
  have hcoef : ∀ j, coefficientProjection I (Fin r) n (g j) =
      MvPolynomial.map (Ideal.Quotient.mk (I ^ n)) (f j) := by
    intro j
    have h := hgf j
    rwa [map_sub, sub_eq_zero, coefficientProjection_polynomialRingHom] at h
  have hM : (coefficientProjection I (Fin r) n).mapMatrix
        (Matrix.of fun i j : Fin m ↦ partialDerivative I (Fin.castLE hm i) (g j)) =
      (MvPolynomial.map (Ideal.Quotient.mk (I ^ n))).mapMatrix (jacobian hm f) := by
    refine Matrix.ext fun i j ↦ ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply, jacobian]
    rw [coefficientProjection_partialDerivative, hcoef j, MvPolynomial.pderiv_map]
  have hgoal : (Matrix.det fun i j : Fin m ↦ partialDerivative I (Fin.castLE hm i) (g j)) =
      (Matrix.of fun i j : Fin m ↦ partialDerivative I (Fin.castLE hm i) (g j)).det := rfl
  rw [map_sub, sub_eq_zero, coefficientProjection_polynomialRingHom, hgoal,
    RingHom.map_det (coefficientProjection I (Fin r) n), hM]
  exact (RingHom.map_det (MvPolynomial.map (Ideal.Quotient.mk (I ^ n))) (jacobian hm f)).symm

end DeterminantApproximation

section PresentationDeterminant

open RestrictedPowerSeries

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}
  {B : AdicFiniteTypeAlgebra.{u, v} A I}

/-- The formal partial derivatives of the completed polynomial algebra are the formal partial
derivatives of restricted power series, read through the identification of the two models of the
completed polynomial algebra. -/
public theorem partialDeriv_adicCompletionAlgEquiv
    (P : CompletedPolynomialPresentation I B) (i : Fin P.variableCount)
    (x : RestrictedPowerSeries I (Fin P.variableCount)) :
    (completedNaiveCotangentComplex B P).partialDeriv i
        (adicCompletionAlgEquiv I (Fin P.variableCount) x) =
      adicCompletionAlgEquiv I (Fin P.variableCount) (partialDerivative I i x) := by
  have key : restrictedPartialDeriv I i
      ((adicCompletionAlgEquiv I (Fin P.variableCount)).symm
        (adicCompletionAlgEquiv I (Fin P.variableCount) x)) = partialDerivative I i x := by
    rw [AlgEquiv.symm_apply_apply]
    rfl
  rw [(completedNaiveCotangentComplex B P).partialDeriv_eq i]
  unfold completedPartialDeriv
  dsimp only [Derivation.coe_mk', LinearMap.coe_comp, Function.comp_apply]
  exact congrArg (adicCompletionAlgEquiv I (Fin P.variableCount)) key

/-- The Jacobian determinant of a family of elements of the kernel, read through a completed
polynomial presentation, is the image of the Jacobian determinant of the same family seen as
restricted power series. -/
public theorem toAlgHom_det_partialDeriv (P : CompletedPolynomialPresentation I B) {m : ℕ}
    (hm : m ≤ P.variableCount) (g : Fin m → RestrictedPowerSeries I (Fin P.variableCount)) :
    P.toAlgHom (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
          (adicCompletionAlgEquiv I (Fin P.variableCount) (g j))) =
      P.restrictedToAlgHom
        (Matrix.det fun i j : Fin m ↦ partialDerivative I (Fin.castLE hm i) (g j)) := by
  classical
  have hM : (Matrix.of fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
          (adicCompletionAlgEquiv I (Fin P.variableCount) (g j))) =
      (adicCompletionAlgEquiv I (Fin P.variableCount)).toAlgHom.toRingHom.mapMatrix
        (Matrix.of fun i j : Fin m ↦ partialDerivative I (Fin.castLE hm i) (g j)) := by
    refine Matrix.ext fun i j ↦ ?_
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.of_apply]
    exact partialDeriv_adicCompletionAlgEquiv P (Fin.castLE hm i) (g j)
  have hgoal : (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
          (adicCompletionAlgEquiv I (Fin P.variableCount) (g j))) =
      (Matrix.of fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
          (adicCompletionAlgEquiv I (Fin P.variableCount) (g j))).det := rfl
  rw [hgoal, hM, ← RingHom.map_det]
  rfl

/-- **The approximate Jacobian determinant.** Let `g₁, …, g_m` lie in the kernel of a completed
polynomial presentation of `B` and let `f₁, …, f_m` be polynomial approximations of them to
accuracy `n`.  Then the images in `B` of the two Jacobian determinants, formed from the first
`m` variables, differ by an element of `I^n·B`. -/
public theorem det_partialDeriv_sub_restrictedToAlgHom_det_mem
    (P : CompletedPolynomialPresentation I B) (hI : I.FG) (n : ℕ) {m : ℕ}
    (hm : m ≤ P.variableCount) (g : Fin m → RestrictedPowerSeries I (Fin P.variableCount))
    (f : Fin m → MvPolynomial (Fin P.variableCount) A)
    (hgf : ∀ j, coefficientProjection I (Fin P.variableCount) n
      (g j - polynomialRingHom I (Fin P.variableCount) (f j)) = 0) :
    P.toAlgHom (Matrix.det fun i j : Fin m ↦
          (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
            (adicCompletionAlgEquiv I (Fin P.variableCount) (g j))) -
        P.restrictedToAlgHom
          (polynomialAlgHom I (Fin P.variableCount) (jacobian hm f).det) ∈
      (I ^ n).map (algebraMap A B.carrier) := by
  have h := mem_map_pow_of_coefficientProjection_eq_zero I hI P.toAlgHom n _
    (coefficientProjection_det_partialDerivative_sub_eq_zero I hm n g f hgf)
  rw [map_sub, map_sub] at h
  rwa [toAlgHom_det_partialDeriv P hm g]

end PresentationDeterminant

section Main

open RestrictedPowerSeries Stacks.LocalCohomology.UniformityIII

variable {A : Type u} [CommRing A] [IsNoetherianRing A] {I : Ideal A}

/-- **Stacks 0GAW, carrying the hypotheses that the library's Stacks 0GAQ carries.**

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, `B` an `I`-adically complete `A`-algebra of
finite type modulo `I`, presented as `B = A⟨x₁, …, x_r⟩/J`, and suppose given `b`, an integer
`m ≤ r` and `f₁, …, f_m ∈ J` with `V(b) ⊆ V(IB)`, with the Jacobian determinant
`Δ = det(∂fⱼ/∂xᵢ)_{i, j ≤ m}` dividing the image of `b`, and with `bJ ⊆ (f₁, …, f_m) + J²`.
Then `B` is the `I`-adic completion of a finite type `A`-algebra.

**The route.** The hypotheses make `B` rig-smooth over `(A, I)`, so a power `I^{c}` annihilates
`Ext¹_B(NL^∧_{B/A}, N)`, and `V(b) ⊆ V(IB)` gives `c₁` with `I^{c₁}B ⊆ bB`.  Writing
`I = (a₁, …, a_t)` and approximating the `fⱼ` by polynomials `f'ⱼ` to accuracy `n`, the algebra

`C = A[z₁, …, z_t, x₁, …, x_r]/(z₁Δ' - a₁^{c₁}, …, z_tΔ' - a_t^{c₁}, f'₁, …, f'_m)`

of Stacks 0GAV has `I^{1 + t((t+1)c₁ - 1)}` annihilating `Ext¹` of its completed naive cotangent
complex — an exponent independent of `n`, which is what lets `n` be chosen in terms of it — and
maps onto `B/IⁿB` by `x_i ↦ x_i`, `z_k ↦ b_k b'`.  Stacks 0GAQ lifts that surjection to
`φ : C^∧ → B`, which is surjective because it is surjective modulo `I`, and Stacks 0ALR
algebraizes `B` from `φ`.

**The carried hypotheses, one line each.**

* `S` — a family of Stacks 0GA6 `DualSituation`s for `B`, one for each thickness and each
  Ext-exponent, exactly as the library's Stacks 0GAQ carries one for each thickness.
* `d`, `q₀`, `k`, `hd`, `hq₀`, `hk` — the invariants of Stacks 0GA6 of `B`, independent of the
  thickness and of the exponent, with `k + 1 = D = max(d, 1)`.
* `hdual` — the open duality input of Stacks 0GAC, which Stacks 0GAQ carries for every level
  `m ≥ n`, here carried for every level and every exponent since `n` is chosen inside the proof.
* `hconormal` — that for every finite type `A`-algebra `C` and every surjection
  `φ : C^∧ → B` of `A`-algebras with both `B` and `C^∧` rig-smooth over `(A, I)` a power of `I`
  annihilates `Ker(φ)/Ker(φ)²`; this is the step the source makes with the six-term sequence of
  Stacks 0ALM and the comparison `H⁰(NL^∧_{C^∧/A}) ⊗ B[1/b] = H⁰(NL^∧_{B/A}) ⊗ B[1/b]` of free
  modules of rank `r - m`, which the library does not have.  Both rig-smoothness inputs are
  discharged here: `B`'s from the Jacobian chart of the statement, `C^∧`'s from the smoothness
  of `C` away from `V(I)`.

Two further deviations, both inherited rather than assumed: the Stacks 0GAQ used here lifts only
to precision `I^{n-(2+D)c}` under `n > 2(2+D)c`, in place of the source's `I^{n-(1+d)c}` under
`n > 2(1+d)c`; and `B` is taken in the universe of `A`, which is the only case Stacks 0GAQ's
target admits. -/
@[stacks 0GAW "carrying, beyond the source's hypotheses: `S`, a family of Stacks 0GA6 \
DualSituations for B, one per thickness and per Ext-exponent, as the library's Stacks 0GAQ \
carries one per thickness; `d`, `q₀`, `k`, `hd`, `hq₀`, `hk`, the Stacks 0GA6 invariants of B, \
independent of thickness and exponent, with k+1 = D = max(d,1); `hdual`, the open duality input \
of Stacks 0GAC that Stacks 0GAQ carries, here for every level and exponent because n is chosen \
in the proof; and `hconormal`, that a power of I kills Ker(φ)/Ker(φ)² for every surjection φ \
from the completion of a finite type A-algebra onto B with both sides rig-smooth (both \
rig-smoothness inputs are discharged here), which is the source's last step by the Stacks 0ALM \
six-term sequence and the localized comparison H⁰(NL^∧_{C^∧/A}) ⊗ B[1/b] = \
H⁰(NL^∧_{B/A}) ⊗ B[1/b], absent from the library. Inherited, not assumed: the Stacks 0GAQ used \
lifts to precision I^{n-(2+D)c} under n > 2(2+D)c for the source's I^{n-(1+d)c}; and B is taken \
in A's own universe, the only case that Stacks 0GAQ's target admits"]
public theorem exists_finiteType_algEquiv_adicCompletion_of_jacobianChart
    (B : AdicFiniteTypeAlgebra.{u, u} A I) (P : CompletedPolynomialPresentation I B)
    (m : ℕ) (hm : m ≤ P.variableCount) (b : P.completedPolynomialRing)
    (f : Fin m → P.ker)
    (hvanish : B.adicIdeal ≤ (Ideal.span {P.toAlgHom b}).radical)
    (hjacobian :
      P.toAlgHom (Matrix.det fun i j : Fin m ↦
        (completedNaiveCotangentComplex B P).partialDeriv (Fin.castLE hm i)
          (f j : P.completedPolynomialRing)) ∣ P.toAlgHom b)
    (hrelations : ∀ x : P.completedPolynomialRing, x ∈ P.ker →
      b * x ∈ Ideal.span (Set.range fun j : Fin m ↦ (f j : P.completedPolynomialRing)) +
        P.ker ^ 2)
    (S : ∀ c l : ℕ, DualSituation B.carrier (I.map (algebraMap A B.carrier)) l c)
    (d q₀ k : ℕ) (hd : ∀ c l, (S c l).d = d) (hq₀ : ∀ c l, (S c l).q₀ = q₀)
    (hk : max d 1 = k + 1)
    (hdual : ∀ (c l e : ℕ) (hel : e + 2 * c = l) (hq : (S c l).q₀ ≤ e)
      (M : ANCModule (I.map (algebraMap A B.carrier)) l c)
      (ϕ : resModule (I.map (algebraMap A B.carrier)) l M.1 →ₗ[B.carrier]
        powQuot (I.map (algebraMap A B.carrier)) l l),
      ∃ s : (S c l).H M.dual 0 (e : ℤ),
        (S c l).ev M e hq s =
          (powQuotLe (I.map (algebraMap A B.carrier)) (Nat.le.intro hel)).comp ϕ)
    (hconormal : ∀ (C : Type u) [CommRing C] [Algebra A C] [Algebra.FiniteType A C]
      (ϕ : AdicCompletion (I.map (algebraMap A C)) C →ₐ[A] B.carrier),
      Function.Surjective ϕ → IsRigSmooth B → IsRigSmooth (adicCompletionObj I (B := C)) →
        ∃ c : ℕ, I ^ c • (⊤ : Submodule A (RingHom.ker ϕ.toRingHom).Cotangent) = ⊥) :
    ∃ (C : Type u) (_ : CommRing C) (_ : Algebra A C),
      Algebra.FiniteType A C ∧
        Nonempty (B.carrier ≃ₐ[A] AdicCompletion (I.map (algebraMap A C)) C) := by
  classical
  have hIfg : I.FG := Ideal.fg_of_isNoetherianRing I
  have hBcomplete : IsAdicComplete (I.map (algebraMap A B.carrier)) B.carrier :=
    B.isAdicallyComplete
  obtain ⟨t, agen, hagen⟩ := Submodule.fg_iff_exists_fin_generating_family.mp hIfg
  have hai : ∀ i, agen i ∈ I := fun i ↦ hagen ▸ Ideal.subset_span ⟨i, rfl⟩
  -- the Jacobian chart makes `B` rig-smooth over `(A, I)`
  have hBsmooth : IsRigSmooth B :=
    isRigSmooth_of_jacobianChart B P m hm b f hvanish hjacobian hrelations
  -- `V(b) ⊆ V(IB)` gives `c₁` with `I^{c₁}B ⊆ bB`
  obtain ⟨c₁, hc₁⟩ := exists_pow_adicIdeal_le_span_of_le_radical B (P.toAlgHom b) hvanish
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
  -- the exponent of Stacks 0GAQ and the accuracy of the approximation
  obtain ⟨n, hn₁, hn₂⟩ : ∃ n : ℕ, q₀ + (k + 2) * (1 + t * ((t + 1) * c₁ - 1)) ≤ n ∧
      2 * ((k + 3) * (1 + t * ((t + 1) * c₁ - 1))) < n :=
    ⟨max (q₀ + (k + 2) * (1 + t * ((t + 1) * c₁ - 1)))
        (2 * ((k + 3) * (1 + t * ((t + 1) * c₁ - 1))) + 1),
      le_max_left _ _, lt_of_lt_of_le (Nat.lt_succ_self _) (le_max_right _ _)⟩
  -- the polynomial approximations `f'ⱼ`
  obtain ⟨f', hf'proj, hf'mem⟩ :=
    P.exists_mvPolynomial_approx_mem_restrictedKer hIfg n g hgker
  -- the cofactors `b_k` of `b`
  have hbsex : ∀ i : Fin t, ∃ w : B.carrier,
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
  -- Stacks 0GAQ lifts `ψn` to an `A`-algebra map `φ : C^∧ → B`
  obtain ⟨φ, hφ⟩ := exists_algHom_lift_of_dualSituation'
    (adicCompletionObj I (B := C)) (multiJacobianCompletedPresentation I hm f' agen c₁)
    (1 + t * ((t + 1) * c₁ - 1))
    (fun y hy N ξ ↦ smul_ext_one_multiJacobianCompletedPresentation_eq_zero hm f' agen c₁
      hagen.symm y hy N ξ)
    (C := B.carrier) (fun l _ ↦ S (1 + t * ((t + 1) * c₁ - 1)) l) d q₀ k
    (fun l _ ↦ hd _ l) (fun l _ ↦ hq₀ _ l) hk n hn₁ hn₂
    (fun l e _ _ hel hq M ϕ ↦ hdual _ l e hel hq M ϕ) ψn
  -- `φ` is surjective, because it is surjective modulo `I`
  have hne : n - (k + 3) * (1 + t * ((t + 1) * c₁ - 1)) ≠ 0 := by omega
  have hmkφ : ∀ z : B.carrier, ∃ w,
      Ideal.Quotient.mk ((I.map (algebraMap A B.carrier)) ^
            (n - (k + 3) * (1 + t * ((t + 1) * c₁ - 1)))) (φ w) =
        Ideal.Quotient.mk ((I.map (algebraMap A B.carrier)) ^
          (n - (k + 3) * (1 + t * ((t + 1) * c₁ - 1)))) z := by
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
    exact ⟨w, Ideal.Quotient.eq.mpr (Ideal.pow_le_self hne (Ideal.Quotient.eq.mp hw))⟩
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
  -- Stacks 0ALR algebraizes `B`
  obtain ⟨c₂, hc₂⟩ := hconormal C φ hφsurj hBsmooth
    (isRigSmooth_adicCompletionObj_of_smoothAwayFrom I
      (smoothAwayFrom_multiJacobianAlgebra hm f' agen c₁ hagen.symm))
  exact _root_.exists_finiteType_algEquiv_adicCompletion_of_cotangent_annihilated A C B.carrier I
    φ hφsurj c₂ hc₂

end Main

end Rig

end
