module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.Algebra.Homology.ConcreteCategory
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksFrontier.RingTheory.DividedPowers.TateResolution.Existence
public import StacksFrontier.RingTheory.Tor.Balancing
public import StacksCore.Tactic.StacksAttribute

/-! # A Tate resolution computes Tor

A `Resolution R S σ φ` is a divided-power differential graded algebra resolving `S`, free over
`R` in every degree. Forgetting the multiplication and the divided powers leaves a chain complex
of free — hence projective — `R`-modules, and the exactness conditions of the resolution say
exactly that its augmentation to `S` is a quasi-isomorphism. So it *is* a projective resolution
of `S`, and therefore computes `Tor_*(S, M)`.

This is what makes a Tate resolution useful homologically, and is the step by which Gulliksen's
argument for Stacks Tag 09PU converts a non-vanishing homology class of `A/IA` into a
non-vanishing `Tor^R_{2n}(S, R/I)`.

The chain is: `differentialAt` and `complex` build the complex, `range_differentialAt_succ` and
`range_differentialAt_zero` are its exactness (from `exact_positive` and `exact_zero`),
`projectiveResolution` assembles the `ProjectiveResolution`, and `torIsoHomology` is the
resulting identification of `Tor` with the homology of the tensored complex — obtained from
`Tor'` via the Tag 00M1 balancing isomorphism, since `Tor'` is the functor derived in the
variable `S` occupies. Finally `tensorQuotEquiv` rewrites each tensored term `𝒜 i ⊗ R/I` as the
quotient `𝒜 i / I·𝒜 i`, which is the form in which the derivation of Tag 09PS acts.

## Main definitions

* `Resolution.complex` — the underlying chain complex of free `R`-modules.
* `Resolution.projectiveResolution` — it is a projective resolution of `S`.
* `Resolution.torIsoHomology` — hence it computes `Tor`.

## References

* [Stacks Project, Tag 09PQ](https://stacks.math.columbia.edu/tag/09PQ)
-/

@[expose] public noncomputable section

namespace DividedPowers.TateResolution

open CategoryTheory Limits CategoryTheory.MonoidalCategory

universe u

namespace Resolution

variable {R S σ : Type u} [CommRing R] [CommRing S] [Algebra R S]
  {φ : MvPolynomial σ R →ₐ[R] S} (T : Resolution R S σ φ)

/-- The differential of the resolution, restricted to a map between two homogeneous pieces. -/
public def differentialAt (i : ℕ) : T.grade (i + 1) →ₗ[R] T.grade i := by
  letI : Ring T.A := T.ring
  letI : Algebra R T.A := T.algebra
  letI : GradedAlgebra T.grade := T.graded
  letI : IsStrictlyGradedComm T.grade := T.strict
  letI : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
  exact (T.differential.comp (T.grade (i + 1)).subtype).codRestrict
    (T.grade i) (fun x => IsDifferentialGradedAlgebra.d_mem
      (𝒜 := T.grade) (d := T.differential) x.2)

/-- The underlying chain complex of `R`-modules, with `𝒜 i` in degree `i` and the restricted
differential; it is a complex because the differential squares to zero. -/
public def complex : ChainComplex (ModuleCat.{u} R) ℕ := by
  letI : Ring T.A := T.ring
  letI : Algebra R T.A := T.algebra
  letI : GradedAlgebra T.grade := T.graded
  letI : IsStrictlyGradedComm T.grade := T.strict
  letI : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
  let term : ℕ → ModuleCat.{u} R := fun i => ModuleCat.of R (T.grade i)
  let diff : ∀ i, term (i + 1) ⟶ term i := fun i =>
    ModuleCat.ofHom (T.differentialAt i)
  refine ChainComplex.of term diff ?_
  intro i
  ext x
  simp only [diff, ModuleCat.hom_comp, ModuleCat.hom_ofHom, LinearMap.comp_apply]
  exact IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := T.grade) (d := T.differential) x

/-- Exactness of the complex in positive degrees, which is `exact_positive`. -/
public theorem range_differentialAt_succ (i : ℕ) :
    LinearMap.range (T.differentialAt (i + 1)) = LinearMap.ker (T.differentialAt i) := by
  let : Ring T.A := T.ring
  let : Algebra R T.A := T.algebra
  let : GradedAlgebra T.grade := T.graded
  let : IsStrictlyGradedComm T.grade := T.strict
  let : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
  apply le_antisymm
  · rw [LinearMap.range_le_ker_iff]
    ext y
    show T.differential (T.differential y.1) = 0
    exact IsDifferentialGradedAlgebra.d_sq_zero (𝒜 := T.grade) (d := T.differential) y.1
  · intro x hx
    obtain ⟨y, hy, hdy⟩ := T.exact_positive (i + 1) x.1 (by omega) x.2
      (congrArg Subtype.val (LinearMap.mem_ker.mp hx))
    exact ⟨⟨y, hy⟩, Subtype.ext hdy⟩

/-- The augmentation on the degree-zero piece, as an `R`-linear map to `S`. -/
public def augmentationAtZero : T.grade 0 →ₗ[R] S := by
  letI : Ring T.A := T.ring
  letI : Algebra R T.A := T.algebra
  exact (T.augmentation.toLinearMap).comp (T.grade 0).subtype

/-- Exactness at the augmentation, which is `exact_zero` together with
`augmentation_differential`. -/
public theorem range_differentialAt_zero :
    LinearMap.range (T.differentialAt 0) = LinearMap.ker (T.augmentationAtZero) := by
  let : Ring T.A := T.ring
  let : Algebra R T.A := T.algebra
  let : GradedAlgebra T.grade := T.graded
  let : IsStrictlyGradedComm T.grade := T.strict
  let : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
  apply le_antisymm
  · rintro x ⟨y, rfl⟩
    show T.augmentation (T.differential y.1) = 0
    exact T.augmentation_differential y.1
  · intro x hx
    obtain ⟨y, hy, hdy⟩ := T.exact_zero x.1 x.2 hx
    exact ⟨⟨y, hy⟩, Subtype.ext hdy⟩

/-- The augmentation is onto in degree zero, since `𝒜 0` is the image of the coefficient map and
the augmentation restricted to it is `φ`, which is onto. -/
public theorem surjective_augmentation_gradeZero (hφ : Function.Surjective φ) :
    Function.Surjective fun x : T.grade 0 => T.augmentation x.1 := by
  intro s
  obtain ⟨p, rfl⟩ := hφ s
  exact ⟨⟨T.coefficient p, (T.degree_zero _).2 ⟨p, rfl⟩⟩,
    DFunLike.congr_fun T.augmentation_coefficient p⟩

/-- The complex is exact in every positive degree. -/
public theorem complex_exactAt_succ (n : ℕ) : (T.complex).ExactAt (n + 1) := by
  rw [HomologicalComplex.exactAt_iff' (T.complex) (n + 2) (n + 1) n
    (by simp only [ChainComplex.prev]; rfl) (by simp),
    ShortComplex.moduleCat_exact_iff_range_eq_ker]
  simp only [HomologicalComplex.sc', HomologicalComplex.shortComplexFunctor', complex]
  rw [show n + 2 = (n + 1) + 1 by omega, ChainComplex.of_d, ChainComplex.of_d]
  exact T.range_differentialAt_succ n

/-- Hence its homology vanishes in every positive degree. -/
public theorem isZero_complex_homology_succ (n : ℕ) :
    IsZero ((T.complex).homology (n + 1)) :=
  (T.complex_exactAt_succ n).isZero_homology

/-- The augmentation, as a chain map to `S` concentrated in degree zero. -/
public def augmentationHom :
    T.complex ⟶ (ChainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R S) := by
  letI : Ring T.A := T.ring
  letI : Algebra R T.A := T.algebra
  letI : GradedAlgebra T.grade := T.graded
  letI : IsStrictlyGradedComm T.grade := T.strict
  letI : IsDifferentialGradedAlgebra T.grade T.differential := T.dga
  let C := T.complex
  let Dc := (ChainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R S)
  let f0 : C.X 0 ⟶ Dc.X 0 := ModuleCat.ofHom
    ((T.augmentation.toLinearMap).comp (T.grade 0).subtype)
  let f1 : C.X 1 ⟶ Dc.X 1 := 0
  refine ChainComplex.mkHom C Dc f0 f1 ?_ ?_
  · ext x
    simp only [ModuleCat.hom_comp, LinearMap.comp_apply, f1, zero_comp]
    change 0 = T.augmentation (T.differential x.1)
    exact (T.augmentation_differential x.1).symm
  · intro n _
    exact ⟨0, (HomologicalComplex.isZero_single_obj_X (ComplexShape.down ℕ) 0
      (ModuleCat.of R S) (n + 1) (by omega)).eq_of_tgt _ _⟩

/-- The augmentation is a quasi-isomorphism in degree zero. -/
private theorem quasiIsoAt_zero_augmentationHom (hφ : Function.Surjective φ) :
    QuasiIsoAt T.augmentationHom 0 := by
  rw [ChainComplex.quasiIsoAt₀_iff]
  let S₁ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R)
    (ComplexShape.down ℕ) 1 0 0).obj (T.complex)
  let S₂ := (HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R)
    (ComplexShape.down ℕ) 1 0 0).obj
      ((ChainComplex.single₀ (ModuleCat.{u} R)).obj (ModuleCat.of R S))
  let c := ((HomologicalComplex.shortComplexFunctor' (ModuleCat.{u} R)
    (ComplexShape.down ℕ) 1 0 0).map (T.augmentationHom))
  have htgt : ∀ i j, ((ChainComplex.single₀ (ModuleCat.{u} R)).obj
      (ModuleCat.of R S)).d i j = 0 := fun _ _ => by rw [HomologicalComplex.single_obj_d]
  have htgtf : S₂.f = 0 := htgt 1 0
  have htgtg : S₂.g = 0 := htgt 0 0
  have hexact : (ShortComplex.mk S₁.f c.τ₂ (by
      rw [← c.comm₁₂, htgtf, comp_zero])).Exact := by
    rw [ShortComplex.moduleCat_exact_iff_range_eq_ker]
    exact T.range_differentialAt_zero
  exact (ShortComplex.quasiIso_iff_of_zeros' c rfl htgtf htgtg).2
    ⟨hexact, (ModuleCat.epi_iff_surjective _).2 (T.surjective_augmentation_gradeZero hφ)⟩

/-- The augmentation is a quasi-isomorphism in every positive degree, where both homologies
vanish. -/
private theorem quasiIsoAt_succ_augmentationHom (i : ℕ) :
    QuasiIsoAt T.augmentationHom (i + 1) := by
  rw [quasiIsoAt_iff_isIso_homologyMap]
  have h₁ := T.isZero_complex_homology_succ i
  have h₂ : IsZero (((ChainComplex.single₀ (ModuleCat.{u} R)).obj
      (ModuleCat.of R S)).homology (i + 1)) := by
    rw [← HomologicalComplex.exactAt_iff_isZero_homology]
    exact ChainComplex.exactAt_succ_single_obj _ _
  rw [h₁.eq_of_src (HomologicalComplex.homologyMap T.augmentationHom (i + 1)) 0]
  exact (isIsoZero_iff_source_target_isZero _ _).2 ⟨h₁, h₂⟩

/-- **A Tate resolution is a projective resolution of `S`.** Each term is free by `free`, hence
projective; the augmentation is a quasi-isomorphism because the complex is exact in positive
degrees and `range_differentialAt_zero` plus surjectivity give exactness at the end. -/
public def projectiveResolution (hφ : Function.Surjective φ) :
    ProjectiveResolution (ModuleCat.of R S) where
  complex := T.complex
  projective i :=
    letI : Ring T.A := T.ring
    letI : Algebra R T.A := T.algebra
    letI : Module.Free R (T.grade i) := T.free i
    ModuleCat.projective_of_free (Module.Free.chooseBasis R (T.grade i))
  π := T.augmentationHom
  quasiIso := by
    rw [quasiIso_iff]
    rintro (_ | i)
    · exact T.quasiIsoAt_zero_augmentationHom hφ
    · exact T.quasiIsoAt_succ_augmentationHom i

/-- **A Tate resolution computes Tor**: `Tor_i(S, M)` is the `i`-th homology of the complex
tensored with `M`. The identification is made for `Tor'`, which is derived in the variable `S`
occupies, and transported to `Tor` along the balancing isomorphism of Tag 00M1. -/
public def torIsoHomology (hφ : Function.Surjective φ) (M : ModuleCat.{u} R) (i : ℕ) :
    (((Tor (ModuleCat.{u} R) i).obj (ModuleCat.of R S)).obj M) ≅
    (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) i).obj
        ((((tensoringRight (ModuleCat.{u} R)).obj M).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (T.complex)) := by
  let α := ((Tor_iso_Tor' R i).app (ModuleCat.of R S)).app M
  let β : ((Tor' (ModuleCat.{u} R) i).obj (ModuleCat.of R S)).obj M ≅
      (HomologicalComplex.homologyFunctor (ModuleCat.{u} R) (ComplexShape.down ℕ) i).obj
        (((((tensoringRight (ModuleCat.{u} R)).obj M).mapHomologicalComplex
          (ComplexShape.down ℕ)).obj (T.complex))) := by
    dsimp [CategoryTheory.Tor']
    change (Functor.leftDerived ((tensoringRight (ModuleCat.{u} R)).obj M) i).obj
      (ModuleCat.of R S) ≅ _
    simpa [projectiveResolution] using
      (T.projectiveResolution hφ).isoLeftDerivedObj ((tensoringRight (ModuleCat.{u} R)).obj M) i
  exact α ≪≫ β

/-- Tensoring a homogeneous piece with `R/I` is dividing it by `I·𝒜 i`, which is the form in
which the derivation of Tag 09PS acts on the tensored complex. -/
public def tensorQuotEquiv (I : Ideal R) (i : ℕ) :=
  letI : Ring T.A := T.ring
  letI : Algebra R T.A := T.algebra
  letI : GradedAlgebra T.grade := T.graded
  TensorProduct.tensorQuotEquivQuotSMul (T.grade i) I

end Resolution

end DividedPowers.TateResolution

end
