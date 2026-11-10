module

public import StacksFrontier.Homology.Perfect.BettiConstructible
public import StacksFrontier.Homology.Perfect.BettiSemicontinuity
public import StacksFrontier.RingTheory.Fitting.Rank
public import Mathlib.Topology.Constructible
public import Mathlib.RingTheory.Spectrum.Prime.Topology
public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffinePullbackSections

/-!
# Constructibility of the level sets of the derived-fibre Betti numbers

Let `R` be a ring and `K ∈ D(R)` pseudo-coherent, represented by a bounded above complex `F` of
finite free modules. At a prime `q`, with `V^• = F^• ⊗_R κ(q)`,

`dim Hⁱ(V^•) + dim V^{i+1} = dim coker(V^{i-1} → V^i) + dim coker(V^i → V^{i+1})`,

and `coker(V^{j-1} → V^j) = coker(F^{j-1} → F^j) ⊗_R κ(q)`. For a finitely presented module `C`,
`dim_{κ(q)} C ⊗_R κ(q) ≤ a` exactly off the closed set `V(Fitt_a(C))` cut out by a finitely
generated ideal, so its level sets are constructible; hence so are those of
`q ↦ dim_{κ(q)} Hⁱ(K ⊗^L_R κ(q))`.

## Main results

* `ShortComplex.finrank_homology_add_finrank_X₃`.
* `StacksDraft.Perfect.isConstructible_setOf_finrank_tensor_eq`.
* the affine case of Stacks 0BDI (3) itself is
  `StacksDraft.Perfect.isConstructible_fibreBetti_preimage`
  (`StacksFrontier/Homology/Perfect/BettiConstructible.lean`).

## References

* [Stacks Project, Tag 0BDI](https://stacks.math.columbia.edu/tag/0BDI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Topology CochainComplex.DerivedExtensionScalars
open scoped TensorProduct

universe u v

attribute [local instance] HasDerivedCategory.standard

namespace CategoryTheory.ShortComplex

/-- **The dimension of the homology of a short complex of vector spaces**:
`dim H + dim X₃ = dim coker f + dim coker g`. -/
theorem finrank_homology_add_finrank_X₃ {k : Type u} [Field k]
    (S : ShortComplex (ModuleCat.{v} k)) [FiniteDimensional k S.X₁]
    [FiniteDimensional k S.X₂] [FiniteDimensional k S.X₃] :
    Module.finrank k S.homology + Module.finrank k S.X₃ =
      Module.finrank k (S.X₂ ⧸ LinearMap.range S.f.hom) +
        Module.finrank k (S.X₃ ⧸ LinearMap.range S.g.hom) := by
  rw [S.moduleCatHomologyIso.toLinearEquiv.finrank_eq]
  change Module.finrank k (LinearMap.ker S.g.hom ⧸ LinearMap.range S.moduleCatToCycles) + _ = _
  have h1 := Submodule.finrank_quotient_add_finrank (LinearMap.range S.moduleCatToCycles)
  have h2 := LinearMap.finrank_range_add_finrank_ker S.moduleCatToCycles
  have h2' := LinearMap.finrank_range_add_finrank_ker S.f.hom
  have hker : LinearMap.ker S.moduleCatToCycles = LinearMap.ker S.f.hom :=
    LinearMap.ker_codRestrict _ _ _
  rw [hker] at h2
  have h3 := LinearMap.finrank_range_add_finrank_ker S.g.hom
  have h4 := Submodule.finrank_quotient_add_finrank (LinearMap.range S.f.hom)
  have h5 := Submodule.finrank_quotient_add_finrank (LinearMap.range S.g.hom)
  omega

end CategoryTheory.ShortComplex

namespace StacksDraft.Perfect

variable {R : Type u} [CommRing R]

/-- The locus of primes where a finite module has fibre dimension at most `a` is the complement
of the zero locus of its `a`-th Fitting ideal. -/
theorem setOf_finrank_tensor_le_eq (C : Type v) [AddCommGroup C] [Module R C] [Module.Finite R C]
    (a : ℕ) :
    {q : PrimeSpectrum R | Module.finrank q.asIdeal.ResidueField
        (q.asIdeal.ResidueField ⊗[R] C) ≤ a} =
      (PrimeSpectrum.zeroLocus (fittingIdeal (R := R) (M := C) (a : ℤ) : Set R))ᶜ := by
  ext q
  simp only [Set.mem_ofPred_eq, Set.mem_compl_iff, PrimeSpectrum.mem_zeroLocus,
    SetLike.coe_subset_coe]
  exact (fittingIdeal_local_generation_tfae (R := R) (M := C) a q.asIdeal).out 2 1

/-- The complement of the zero locus of a finitely generated ideal is constructible. -/
theorem isConstructible_compl_zeroLocus_of_fg {I : Ideal R} (hI : I.FG) :
    IsConstructible (PrimeSpectrum.zeroLocus (I : Set R))ᶜ := by
  obtain ⟨s, rfl⟩ := hI
  rw [PrimeSpectrum.zeroLocus_span]
  exact IsRetrocompact.isConstructible (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl
    (PrimeSpectrum.isRetrocompact_zeroLocus_compl s.finite_toSet)

/-- **The level sets of the fibre dimension of a finitely presented module are
constructible.** -/
theorem isConstructible_setOf_finrank_tensor_eq (C : Type v) [AddCommGroup C] [Module R C]
    [Module.FinitePresentation R C] (a : ℕ) :
    IsConstructible {q : PrimeSpectrum R | Module.finrank q.asIdeal.ResidueField
        (q.asIdeal.ResidueField ⊗[R] C) = a} := by
  have hle : ∀ b : ℕ, IsConstructible {q : PrimeSpectrum R | Module.finrank
      q.asIdeal.ResidueField (q.asIdeal.ResidueField ⊗[R] C) ≤ b} := fun b ↦ by
    rw [setOf_finrank_tensor_le_eq]
    exact isConstructible_compl_zeroLocus_of_fg
      ((fittingIdeal_basic_properties.{u, v, v, u} (R := R) (M := C)).2.2.2.1 inferInstance b)
  rcases a with _ | a
  · simpa only [Nat.le_zero] using hle 0
  · convert (hle (a + 1)).sdiff (hle a) using 1
    ext q
    simp only [Set.mem_ofPred_eq, Set.mem_sdiff]
    omega

/-- The cokernel of the base change of `d : M ⟶ N` to a residue field is the base change of the
cokernel of `d`. -/
theorem finrank_quotient_range_extendScalars_map (q : PrimeSpectrum R) {M N : ModuleCat.{u} R}
    (d : M ⟶ N) :
    Module.finrank q.asIdeal.ResidueField
        ((ModuleCat.extendScalars.{u, u, u} (algebraMap R q.asIdeal.ResidueField)).obj N ⧸
          LinearMap.range ((ModuleCat.extendScalars.{u, u, u}
            (algebraMap R q.asIdeal.ResidueField)).map d).hom) =
      Module.finrank q.asIdeal.ResidueField
        (q.asIdeal.ResidueField ⊗[R] (N ⧸ LinearMap.range d.hom)) := by
  let κ := q.asIdeal.ResidueField
  let eM := AlgebraicGeometry.extendScalarsTensorEquiv (S := κ) (R := R) M
  let eN := AlgebraicGeometry.extendScalarsTensorEquiv (S := κ) (R := R) N
  let g : κ ⊗[R] M →ₗ[κ] κ ⊗[R] N := TensorProduct.AlgebraTensorModule.lTensor κ κ d.hom
  have hcomm : ∀ x, eN (((ModuleCat.extendScalars.{u, u, u} (algebraMap R κ)).map d).hom x) =
      g (eM x) := by
    intro x
    refine TensorProduct.inductionOn
      (motive := fun x ↦ eN (((ModuleCat.extendScalars.{u, u, u} (algebraMap R κ)).map d).hom x) =
        g (eM x)) x (fun a m ↦ rfl) fun x y hx hy ↦ ?_
    exact (congrArg eN (map_add _ x y)).trans ((map_add eN _ _).trans
      ((congrArg₂ (· + ·) hx hy).trans ((map_add g _ _).symm.trans
        (congrArg g (map_add eM x y).symm))))
  have hrange : (LinearMap.range ((ModuleCat.extendScalars.{u, u, u}
      (algebraMap R κ)).map d).hom).map eN.toLinearMap = LinearMap.range g := by
    ext y
    simp only [Submodule.mem_map, LinearMap.mem_range, LinearEquiv.coe_coe]
    constructor
    · rintro ⟨_, ⟨x, rfl⟩, rfl⟩
      exact ⟨eM x, (hcomm x).symm⟩
    · rintro ⟨x, rfl⟩
      exact ⟨_, ⟨eM.symm x, rfl⟩, by rw [hcomm, LinearEquiv.apply_symm_apply]⟩
  have hsurj : Function.Surjective (TensorProduct.AlgebraTensorModule.lTensor κ κ
      d.hom.rangeRestrict) :=
    LinearMap.lTensor_surjective _ d.hom.surjective_rangeRestrict
  have hg : LinearMap.range g = LinearMap.range (TensorProduct.AlgebraTensorModule.lTensor κ κ
      ((LinearMap.range d.hom).subtype.restrictScalars R)) := by
    have hfac : g = (TensorProduct.AlgebraTensorModule.lTensor κ κ
        ((LinearMap.range d.hom).subtype.restrictScalars R)).comp
        (TensorProduct.AlgebraTensorModule.lTensor κ κ d.hom.rangeRestrict) := by
      apply TensorProduct.AlgebraTensorModule.curry_injective
      ext a
      rfl
    rw [hfac, LinearMap.range_comp_of_range_eq_top _ (LinearMap.range_eq_top.mpr hsurj)]
  exact (Submodule.Quotient.equiv _ _ eN hrange ≪≫ₗ
    Submodule.quotEquivOfEq _ _ hg ≪≫ₗ
    (TensorProduct.AlgebraTensorModule.tensorQuotientEquiv κ R κ
      (LinearMap.range d.hom)).symm).finrank_eq

end StacksDraft.Perfect
