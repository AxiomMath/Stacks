module

public import StacksFrontier.AlgebraicGeometry.Blowup.AlmostExactness
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.BitUniformityIII.BlowupTwistedPullbackModuleSituation

/-!
# `I^c` annihilates the sheaf `ℱ` of [Stacks, Tag 0GAA], on `Proj` of the Rees algebra

Let `A` be a Noetherian ring, `I ⊆ A` an ideal and `X = Proj(⨁ₙ Iⁿ)` the blowup of `Spec(A)`
in `I`. Fix an `(A, n, c)`-module `M` and a finite free presentation
`0 → K → (A/Iⁿ)^{⊕r} → M → 0` of it, and let `ℱ(q) = ker(p^*K(q) ⟶ 𝒢(q))` be the sheaf
`Stacks.LocalCohomology.UniformityIII.twistedPullbackSupported`. This file proves that `I^c`
annihilates `ℱ(q)`, for every twist `q : ℤ`.

## Main results

* `Stacks.LocalCohomology.UniformityIII.smul_eq_zero_of_mono_comp_map_eq_zero`: for an
  `R`-linear functor `G`, a subobject of `G K` killed by `G f` is killed by every scalar whose
  multiplication on `K` factors through `f`.
* `Stacks.LocalCohomology.UniformityIII.linear_twistedPullbackFunctor`: the functor
  `N ↦ 𝒪_X(q) ⊗ p^*Ñ` is `A`-linear.
* `Stacks.LocalCohomology.UniformityIII.exists_resScalarRetraction`: multiplication by `a ∈ I^c`
  on the kernel of a chosen presentation factors through the inclusion into the free module,
  over `A`.
* `Stacks.LocalCohomology.UniformityIII.smul_twistedPullbackSupported_eq_zero`: **`I^c`
  annihilates `ℱ(q)`**, for every `q : ℤ`.

## References

* [Stacks Project, Tag 0GA8](https://stacks.math.columbia.edu/tag/0GA8)
* [Stacks Project, Tag 0GAA](https://stacks.math.columbia.edu/tag/0GAA)
* [Stacks Project, Tag 0G93](https://stacks.math.columbia.edu/tag/0G93)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.LocalCohomology.UniformityIII

/-- **A subobject of `G K` killed by `G f` is killed by every scalar whose multiplication on `K`
factors through `f`.**

Let `G` be an `R`-linear functor out of `R`-modules, let `f : K ⟶ L`, and suppose
multiplication by `a : R` on `K` is `f ≫ h` for some `h : L ⟶ K`. If `ι : Z ⟶ G K` is a
monomorphism with `ι ≫ G f = 0`, then `a • 𝟙 Z = 0`. -/
theorem smul_eq_zero_of_mono_comp_map_eq_zero {R : Type u} [CommRing R]
    {C : Type*} [Category C] [Preadditive C] [Linear R C]
    (G : ModuleCat.{u} R ⥤ C) [G.Linear R] {K L : ModuleCat.{u} R} (f : K ⟶ L) (h : L ⟶ K)
    (a : R) (hfac : a • 𝟙 K = f ≫ h) {Z : C} (ι : Z ⟶ G.obj K) [Mono ι]
    (hι : ι ≫ G.map f = 0) : a • 𝟙 Z = 0 := by
  have key : ι ≫ (a • 𝟙 (G.obj K)) = 0 := by
    rw [← G.map_id, ← G.map_smul, hfac, G.map_comp, ← Category.assoc, hι, zero_comp]
  refine (cancel_mono ι).1 ?_
  rw [Linear.smul_comp, Category.id_comp, zero_comp, ← key, Linear.comp_smul, Category.comp_id]

variable {A : Type u} [CommRing A] (I : Ideal A)

/-- `N ↦ 𝒪_X(q) ⊗ p^*Ñ` is `A`-linear, as a functor to the category
`CategoryTheory.SheafOfModules` of sheaves of modules on the blowup. -/
theorem linear_twistedPullbackFunctor (q : ℤ) :
    letI : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
      Stacks.Blowup.blowUpModulesLinear I
    (twistedPullbackFunctor I q).Linear A :=
  let : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
    Stacks.Blowup.blowUpModulesLinear I
  Stacks.Blowup.linear_twistedGeometricFactor I q

variable {I} {n c : ℕ} {M : ANCModule I n c}

/-- **Multiplication by `a ∈ I^c` on the kernel of a chosen presentation of an
`(A, n, c)`-module factors through the inclusion into the free module**, over `A`: the
presentation is read as the short complex
`Stacks.LocalCohomology.UniformityIII.ANCPresentation.resShortComplex` of `A`-modules. -/
theorem exists_resScalarRetraction (P : ANCPresentation I n c M) {a : A} (ha : a ∈ I ^ c) :
    ∃ h : P.resShortComplex.X₂ ⟶ P.resShortComplex.X₁,
      a • 𝟙 P.resShortComplex.X₁ = P.resShortComplex.f ≫ h := by
  have hzero : P.proj.comp P.incl = 0 := by
    ext x
    exact (P.range_incl_eq_ker_proj.le ⟨x, rfl⟩ : _)
  obtain ⟨h, hh⟩ := AlgebraicGeometry.exists_scalar_retraction_of_projective_factorization
    P.incl P.proj hzero P.range_incl_eq_ker_proj P.proj_surjective P.incl_injective
    (Ideal.Quotient.mk (I ^ n) a) (M.2.2 _ (Ideal.mem_map_of_mem _ ha))
  refine ⟨(ModuleCat.restrictScalars (Ideal.Quotient.mk (I ^ n))).map (ModuleCat.ofHom h), ?_⟩
  ext x
  exact congrArg (fun φ => φ x) hh

/-- **`I^c` annihilates the sheaf `ℱ(q)` of the proof of [Stacks, Tag 0GAA], on
`Proj(⨁ₙ Iⁿ)`**, for every twist `q : ℤ`: multiplication by `a ∈ I^c` on
`ℱ(q) = ker(p^*K(q) ⟶ 𝒢(q))` is the zero morphism. The scalar action is the `A`-linear structure
`Stacks.Blowup.blowUpModulesLinear I` on sheaves of modules on the blowup, i.e. multiplication by
the pullback of the function `a`. -/
theorem smul_twistedPullbackSupported_eq_zero (P : ANCPresentation I n c M) (q : ℤ)
    {a : A} (ha : a ∈ I ^ c) :
    letI : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
      Stacks.Blowup.blowUpModulesLinear I
    a • 𝟙 (twistedPullbackSupported I q (S := P.resShortComplex)) = 0 := by
  let : Linear A (_root_.SheafOfModules.{u} (blowupScheme I).ringCatSheaf) :=
    Stacks.Blowup.blowUpModulesLinear I
  let : (twistedPullbackFunctor I q).Linear A := linear_twistedPullbackFunctor I q
  obtain ⟨h, hfac⟩ := exists_resScalarRetraction P ha
  refine smul_eq_zero_of_mono_comp_map_eq_zero (twistedPullbackFunctor I q)
    P.resShortComplex.f h a hfac (kernel.ι _) ?_
  show kernel.ι (P.resShortComplex.map (twistedPullbackFunctor I q)).toCycles ≫
      (P.resShortComplex.map (twistedPullbackFunctor I q)).f = 0
  rw [← ShortComplex.toCycles_i, ← Category.assoc, kernel.condition, zero_comp]

end Stacks.LocalCohomology.UniformityIII

end
