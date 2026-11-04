module

public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import Mathlib.Algebra.Category.ModuleCat.ChangeOfRings
public import StacksFrontier.Algebra.Homology.EulerCharacteristicHomology
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The fibre Euler characteristic of a bounded complex of finite projective modules

Let `R` be a commutative ring, `M^•` a bounded cochain complex of finite projective `R`-modules
and `φ : R ⟶ K` a ring map to a field.  The Euler characteristic of the cohomology of
`M^• ⊗_R K` is the alternating sum of the ranks of the terms `M^i` at the prime `ker φ`:

`∑ᵢ (-1)ⁱ dim_K Hⁱ(M^• ⊗_R K) = ∑ᵢ (-1)ⁱ rank_{ker φ} M^i`.

The right hand side, as a function of the prime, is locally constant on `Spec R`, finite
projective modules having locally constant rank.  This is the mechanism by which a bounded complex
of finite projective modules computing the cohomology of the fibres of a family makes the fibrewise
Euler characteristic locally constant (Stacks 0A1Q, 0D1Z).

## Main results

* `Module.finrank_tensorProduct_eq_rankAtStalk_ker`: `dim_K (K ⊗_R P) = rank_{ker φ} P` for a
  finite projective `P`.
* `CochainComplex.homologyEulerChar_extendScalars_eq_finsum_rankAtStalk`: the identity above.
* `CochainComplex.isLocallyConstant_finsum_rankAtStalk`: the alternating sum of the ranks of the
  terms of a bounded complex of finite projective modules is locally constant on `Spec R`.
* `DerivedExtensionScalars.TotalDerivedExtensionScalars.finsum_finrank_homology_functor_obj_Q_eq`:
  the same identity for the derived extension of scalars `M^• ⊗^L_R K`, which a bounded above
  complex of projectives computes termwise.

## References

* [Stacks Project, Tag 0A1Q](https://stacks.math.columbia.edu/tag/0A1Q)
* [Stacks Project, Tag 0D1Z](https://stacks.math.columbia.edu/tag/0D1Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

/-- **The dimension of a base change of a finite projective module to a field is its rank at the
kernel.**  For a finite projective `R`-module `P` and an `R`-algebra `K` which is a field,
`dim_K (K ⊗_R P)` is the rank of `P` at the prime `ker (R ⟶ K)`. -/
@[ega "I 6.4.12" "more general", ega "IV 2.5.8.9" "partial"]
theorem Module.finrank_tensorProduct_eq_rankAtStalk_ker {R K : Type*} [CommRing R] [Field K]
    [Algebra R K] (P : Type*) [AddCommGroup P] [Module R P] [Module.Finite R P]
    [Module.Projective R P] :
    Module.finrank K (TensorProduct R K P) =
      Module.rankAtStalk P ((⊥ : PrimeSpectrum K).comap (algebraMap R K)) := by
  rw [← Module.rankAtStalk_baseChange, Module.rankAtStalk_eq_finrank_of_free]
  rfl

namespace CochainComplex

variable {R : Type u} [CommRing R]

/-- **The fibre Euler characteristic of a bounded complex of finite projective modules.**  For a
cochain complex `M^•` of finite projective `R`-modules with finitely many nonzero terms and a
ring map `φ : R ⟶ K` to a field, the Euler characteristic of the cohomology of `M^• ⊗_R K` is
the alternating sum of the ranks of the `M^i` at `ker φ`. -/
@[ega "III 7.9.2" "more general"]
theorem homologyEulerChar_extendScalars_eq_finsum_rankAtStalk {K : Type u} [Field K]
    (φ : R →+* K) (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfin : ∀ i, Module.Finite R (M.X i)) (hproj : ∀ i, Module.Projective R (M.X i))
    (hsupp : {i | ¬ IsZero (M.X i)}.Finite) :
    (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        M).homologyEulerChar =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) *
        (Module.rankAtStalk (M.X i) ((⊥ : PrimeSpectrum K).comap φ) : ℤ) := by
  let := φ.toAlgebra
  let MK := ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  have hfinK : ∀ i, Module.Finite K (MK.X i) := fun i =>
    have := hfin i
    inferInstanceAs (Module.Finite K (TensorProduct R K (M.X i)))
  have hsuppK : {i | ¬ IsZero (MK.X i)}.Finite :=
    hsupp.subset fun i hi hz => hi ((ModuleCat.extendScalars φ).map_isZero hz)
  rw [HomologicalComplex.homologyEulerChar_eq_eulerChar_of_rel (Equiv.addRight 1)
    (fun i => rfl) MK hfinK hsuppK]
  refine finsum_congr fun i => ?_
  congr 2
  have := hfin i
  have := hproj i
  exact Module.finrank_tensorProduct_eq_rankAtStalk_ker (K := K) (M.X i)

/-- **The alternating sum of the ranks of a bounded complex of finite projective modules is
locally constant on the spectrum.** -/
theorem isLocallyConstant_finsum_rankAtStalk (M : CochainComplex (ModuleCat.{u} R) ℤ)
    (hfin : ∀ i, Module.Finite R (M.X i)) (hproj : ∀ i, Module.Projective R (M.X i))
    (hsupp : {i | ¬ IsZero (M.X i)}.Finite) :
    IsLocallyConstant fun p : PrimeSpectrum R =>
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (Module.rankAtStalk (M.X i) p : ℤ) := by
  have h : (fun p : PrimeSpectrum R =>
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (Module.rankAtStalk (M.X i) p : ℤ)) =
      fun p => ∑ i ∈ hsupp.toFinset, (i.negOnePow : ℤ) * (Module.rankAtStalk (M.X i) p : ℤ) := by
    funext p
    refine finsum_eq_sum_of_support_subset _ fun i hi => ?_
    rw [Set.Finite.coe_toFinset]
    intro hz
    apply hi
    have : Subsingleton (M.X i) := ModuleCat.isZero_iff_subsingleton.mp hz
    simp [Module.rankAtStalk_eq_zero_of_subsingleton]
  rw [h]
  have hf : ∀ i : ℤ, IsLocallyConstant fun p : PrimeSpectrum R =>
      (i.negOnePow : ℤ) * (Module.rankAtStalk (M.X i) p : ℤ) := fun i => by
    have := hfin i
    have := hproj i
    have : Module.FinitePresentation R (M.X i) := Module.finitePresentation_of_projective R _
    exact (Module.isLocallyConstant_rankAtStalk (M := M.X i)).comp
      (fun n : ℕ => (i.negOnePow : ℤ) * (n : ℤ))
  induction hsupp.toFinset using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact IsLocallyConstant.const (0 : ℤ)
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha]
    exact (hf a).add ih

namespace DerivedExtensionScalars.TotalDerivedExtensionScalars

/-- The cohomology of `D(M^•)` is isomorphic to that of the termwise base change `M^• ⊗_R K`, for
a bounded above complex `M^•` of projective `R`-modules. -/
private theorem nonempty_iso_homology_extendScalars {K : Type u} [Field K] (φ : R →+* K)
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} K)]
    (D : TotalDerivedExtensionScalars.{u, u, u} φ) (M : CochainComplex (ModuleCat.{u} R) ℤ)
    {b : ℤ} [M.IsStrictlyLE b] (hproj : ∀ i, Module.Projective R (M.X i)) (i : ℤ) :
    Nonempty ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) i).obj
      (D.functor.obj (DerivedCategory.Q.obj M)) ≅
      (((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M).homology i) :=
  have : ∀ i, Projective (M.X i) := fun i =>
    (IsProjective.iff_projective (R := R) (M.X i)).1 (hproj i)
  have := D.comparison_isIso_of_projective M b
  ⟨(DerivedCategory.homologyFunctor (ModuleCat.{u} K) i).mapIso (asIso (D.comparison.app M)) ≪≫
    (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} K) i).app _⟩

/-- **The fibre Euler characteristic of a bounded complex of finite projective modules, derived
form.**  For a total derived extension of scalars `D = - ⊗^L_R K` along a ring map `φ : R ⟶ K`
to a field and a bounded cochain complex `M^•` of finite projective `R`-modules,
`∑ᵢ (-1)ⁱ dim_K Hⁱ(M^• ⊗^L_R K) = ∑ᵢ (-1)ⁱ rank_{ker φ} M^i`: the derived extension is computed
termwise on a bounded above complex of projectives. -/
theorem finsum_finrank_homology_functor_obj_Q_eq {K : Type u} [Field K] (φ : R →+* K)
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} K)]
    (D : TotalDerivedExtensionScalars.{u, u, u} φ) (M : CochainComplex (ModuleCat.{u} R) ℤ)
    {a b : ℤ} [M.IsStrictlyGE a] [M.IsStrictlyLE b]
    (hfin : ∀ i, Module.Finite R (M.X i)) (hproj : ∀ i, Module.Projective R (M.X i)) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * (Module.finrank K
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) i).obj
          (D.functor.obj (DerivedCategory.Q.obj M))) : ℤ) =
      ∑ᶠ i : ℤ, (i.negOnePow : ℤ) *
        (Module.rankAtStalk (M.X i) ((⊥ : PrimeSpectrum K).comap φ) : ℤ) := by
  have hsupp : {i | ¬ IsZero (M.X i)}.Finite := by
    refine (Set.finite_Icc a b).subset fun i hi => ⟨?_, ?_⟩
    · by_contra h
      exact hi (M.isZero_of_isStrictlyGE a i (by omega))
    · by_contra h
      exact hi (M.isZero_of_isStrictlyLE b i (by omega))
  rw [← homologyEulerChar_extendScalars_eq_finsum_rankAtStalk φ M hfin hproj hsupp]
  refine finsum_congr fun i => ?_
  congr 2
  exact (nonempty_iso_homology_extendScalars (b := b) φ D M hproj i).some.toLinearEquiv.finrank_eq

/-- The cohomology of `M^• ⊗^L_R K` is finite dimensional, for a bounded above complex `M^•` of
finite projective `R`-modules and a ring map `R ⟶ K` to a field. -/
theorem moduleFinite_homology_functor_obj_Q {K : Type u} [Field K] (φ : R →+* K)
    [HasDerivedCategory (ModuleCat.{u} R)] [HasDerivedCategory (ModuleCat.{u} K)]
    (D : TotalDerivedExtensionScalars.{u, u, u} φ) (M : CochainComplex (ModuleCat.{u} R) ℤ)
    {b : ℤ} [M.IsStrictlyLE b]
    (hfin : ∀ i, Module.Finite R (M.X i)) (hproj : ∀ i, Module.Projective R (M.X i)) (i : ℤ) :
    Module.Finite K ((DerivedCategory.homologyFunctor (ModuleCat.{u} K) i).obj
      (D.functor.obj (DerivedCategory.Q.obj M))) := by
  let := φ.toAlgebra
  let MK := ((ModuleCat.extendScalars φ).mapHomologicalComplex (ComplexShape.up ℤ)).obj M
  have : Module.Finite K (MK.sc i).X₂ :=
    have := hfin i
    inferInstanceAs (Module.Finite K (TensorProduct R K (M.X i)))
  have : Module.Finite K (MK.sc i).moduleCatLeftHomologyData.H :=
    inferInstanceAs (Module.Finite K
      (LinearMap.ker (MK.sc i).g.hom ⧸ LinearMap.range (MK.sc i).moduleCatToCycles))
  exact Module.Finite.equiv ((nonempty_iso_homology_extendScalars (b := b) φ D M hproj i).some ≪≫
    (MK.sc i).moduleCatHomologyIso).toLinearEquiv.symm

end DerivedExtensionScalars.TotalDerivedExtensionScalars

end CochainComplex
