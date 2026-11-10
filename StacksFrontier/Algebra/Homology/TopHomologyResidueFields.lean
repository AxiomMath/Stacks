module

public import Mathlib.RingTheory.LocalRing.Module
public import StacksFrontier.Algebra.Homology.PseudoCoherentNakayama
public import StacksFrontier.Algebra.Homology.KFlat
public import StacksFrontier.Algebra.Homology.DerivedCategory.StandardModelScoped

/-!
# Top cohomology of a complex of finite modules, read at the residue fields

Let `A` be a commutative ring and `P` a complex of `A`-modules with `P^i = 0` for `i > n` and
`P^n` finite. Then `H^n(P) = P^n / d(P^{n-1})` is a finite `A`-module, and `H^n` commutes with
the degreewise base change `κ(𝔭) ⊗_A -` (right exactness of the tensor product). So `H^n(P) = 0`
as soon as `H^n(κ(𝔭) ⊗_A P) = 0` for every prime `𝔭` of `A`: a finite module whose fibres at all
primes vanish has empty support, hence is zero (Nakayama's lemma at every localization). This is
the pointwise form of the derived Nakayama lemma (Stacks 068V).

## Main results

* `epi_of_forall_epi_extendScalars_residueField`: a map `N ⟶ M` with `M` finite is surjective
  when it is so after `κ(𝔭) ⊗_A -` for every prime `𝔭`.
* `isZero_homology_of_forall_isZero_homology_extendScalars_residueField`: the top cohomology of a
  complex of finite modules vanishes when it does after `κ(𝔭) ⊗_A -` for every prime `𝔭`.
* `isZero_homology_of_forall_isZero_homology_extendScalars_residueField_of_lt`: the cohomology of
  a bounded above complex of finite free modules vanishes above degree `n` when it does after
  `κ(𝔭) ⊗_A -` for every prime `𝔭`.

## References

* [Stacks Project, Tag 00DV](https://stacks.math.columbia.edu/tag/00DV)
* [Stacks Project, Tag 068V](https://stacks.math.columbia.edu/tag/068V)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u

namespace StacksDraft.PseudoCoherence

open scoped Stacks.StandardDerivedModel

variable {A : Type u} [CommRing A]

/-- **Surjectivity onto a finite module is detected at the residue fields.** A map `g : N ⟶ M` of
`A`-modules with `M` finite is surjective when `κ(𝔭) ⊗_A g` is surjective for every prime `𝔭` of
`A`. -/
theorem epi_of_forall_epi_extendScalars_residueField {N M : ModuleCat.{u} A} [Module.Finite A M]
    (g : N ⟶ M)
    (hg : ∀ p : PrimeSpectrum A,
      Epi ((ModuleCat.extendScalars.{u, u, u} (algebraMap A p.asIdeal.ResidueField)).map g)) :
    Epi g := by
  let Q : ModuleCat.{u} A := ModuleCat.of A (M ⧸ LinearMap.range g.hom)
  let π : M ⟶ Q := ModuleCat.ofHom (LinearMap.range g.hom).mkQ
  have hgπ : g ≫ π = 0 := by
    ext x
    exact (Submodule.Quotient.mk_eq_zero _).2 ⟨x, rfl⟩
  have hsupp : Module.support A Q = ∅ := by
    refine Set.eq_empty_iff_forall_notMem.2 fun p hp => ?_
    let : (ModuleCat.extendScalars.{u, u, u}
        (algebraMap A p.asIdeal.ResidueField)).IsLeftAdjoint :=
      (ModuleCat.extendRestrictScalarsAdj.{u, u, u}
        (algebraMap A p.asIdeal.ResidueField)).isLeftAdjoint
    let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A p.asIdeal.ResidueField)
    have := hg p
    have hFπ : F.map π = 0 := by
      rw [← cancel_epi (F.map g), ← F.map_comp, hgπ, F.map_zero, comp_zero]
    have hπepi : Epi π :=
      (ModuleCat.epi_iff_surjective π).2 (Submodule.mkQ_surjective _)
    have hFπepi : Epi (F.map π) := inferInstance
    rw [hFπ] at hFπepi
    have hQ : IsZero (F.obj Q) := IsZero.of_epi_zero (F.obj M) (F.obj Q)
    have hsub : Subsingleton (p.asIdeal.ResidueField ⊗[A] Q) := by
      let k := p.asIdeal.ResidueField
      let e : (ModuleCat.restrictScalars (algebraMap A k)).obj (ModuleCat.of k k) ≃ₗ[A] k :=
        { toFun := id
          invFun := id
          left_inv := fun _ => rfl
          right_inv := fun _ => rfl
          map_add' := fun _ _ => rfl
          map_smul' := by
            intro r c
            change algebraMap A k r * (show k from c) = r • (show k from c)
            exact (Algebra.smul_def r (show k from c)).symm }
      have : Subsingleton ((ModuleCat.restrictScalars (algebraMap A k)).obj (ModuleCat.of k k) ⊗[A]
          Q) := ModuleCat.subsingleton_of_isZero hQ
      exact (TensorProduct.congr e (LinearEquiv.refl A Q)).toEquiv.symm.subsingleton
    exact not_nontrivial_iff_subsingleton.2 hsub
      ((Module.mem_support_iff_nontrivial_residueField_tensorProduct p).1 hp)
  have hQsub : Subsingleton Q := Module.support_eq_empty_iff.1 hsupp
  refine (ModuleCat.epi_iff_surjective g).2 fun x => ?_
  exact LinearMap.mem_range.1 ((Submodule.Quotient.mk_eq_zero _).1 (Subsingleton.elim (α := Q) _ _))

/-- **The top cohomology of a complex of finite modules vanishes when it does at every residue
field.** Let `P` be a complex of `A`-modules with `P^{n+1} = 0` and `P^n` finite. If
`H^n(κ(𝔭) ⊗_A P) = 0` for every prime `𝔭` of `A` (degreewise base change), then `H^n(P) = 0`. -/
theorem isZero_homology_of_forall_isZero_homology_extendScalars_residueField
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (n : ℤ) (hP : IsZero (P.X (n + 1)))
    [Module.Finite A (P.X n)]
    (h : ∀ p : PrimeSpectrum A, IsZero
      (((CochainComplex.extendScalars (algebraMap A p.asIdeal.ResidueField)).obj P).homology n)) :
    IsZero (P.homology n) := by
  refine (isZero_homology_iff_epi_d_of_isZero P n hP).2
    (epi_of_forall_epi_extendScalars_residueField _ fun p => ?_)
  let F := ModuleCat.extendScalars.{u, u, u} (algebraMap A p.asIdeal.ResidueField)
  exact (isZero_homology_iff_epi_d_of_isZero ((F.mapHomologicalComplex _).obj P) n
    (F.map_isZero hP)).1 (h p)

/-- A complex of finite free modules consists of projective modules. -/
private theorem projective_X_of_finite_free {P : CochainComplex (ModuleCat.{u} A) ℤ}
    (h : ∀ j, Module.Finite A (P.X j) ∧ Module.Free A (P.X j)) (j : ℤ) : Projective (P.X j) :=
  have := (h j).2
  ModuleCat.projective_of_free (Module.Free.chooseBasis A (P.X j))

/-- **The cohomological amplitude of a pseudo-coherent complex is detected at the residue
fields.** Let `P` be a bounded above complex of finite free `A`-modules and `n ∈ ℤ`. If
`H^i(κ(𝔭) ⊗_A P) = 0` for every prime `𝔭` of `A` and every `i > n` (degreewise base change, which
computes the derived base change of `P`), then `H^i(P) = 0` for every `i > n`. -/
theorem isZero_homology_of_forall_isZero_homology_extendScalars_residueField_of_lt
    (P : CochainComplex (ModuleCat.{u} A) ℤ) (hP : IsBoundedAboveFiniteFree P) (n : ℤ)
    (h : ∀ p : PrimeSpectrum A, ∀ i : ℤ, n < i → IsZero
      (((CochainComplex.extendScalars (algebraMap A p.asIdeal.ResidueField)).obj P).homology i))
    (i : ℤ) (hi : n < i) :
    IsZero (P.homology i) := by
  obtain ⟨b, hb⟩ := hP.upperBound
  have : ∀ j, Projective (P.X j) := projective_X_of_finite_free fun j => hP.finiteFree j
  suffices key : ∀ k : ℕ, ∀ i : ℤ, n < i → b < i + k → IsZero (P.homology i) from
    key (b - i + 1).toNat i hi (by omega)
  intro k
  induction k with
  | zero =>
    intro i _ hbi
    exact ShortComplex.isZero_homology_of_isZero_X₂ (P.sc i)
      (P.isZero_of_isStrictlyLE b i (by omega))
  | succ k ih =>
    intro i hni hbi
    let K := DerivedCategory.Q.obj P
    have hK : IsPseudoCoherent K := ⟨P, hP, ⟨Iso.refl _⟩⟩
    have hvanK : ∀ j, i < j → IsZero ((DerivedCategory.homologyFunctor _ j).obj K) :=
      fun j hj => (ih j (by omega) (by omega)).of_iso
        ((DerivedCategory.homologyFunctorFactors _ j).app P)
    obtain ⟨P', α, hP', hle, hα⟩ := exists_finiteFree_representative_le K i hK hvanK
    have : ∀ j, Projective (P'.X j) := projective_X_of_finite_free hP'
    have : Module.Finite A (P'.X i) := (hP' i).1
    have h' : IsZero (P'.homology i) := by
      refine isZero_homology_of_forall_isZero_homology_extendScalars_residueField P' i
        (P'.isZero_of_isStrictlyLE i (i + 1) (by omega)) fun p => ?_
      let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, u}
        (algebraMap A p.asIdeal.ResidueField)
      have := D.comparison_isIso_of_projective P' i
      have := D.comparison_isIso_of_projective P b
      exact (h p i hni).of_iso (((DerivedCategory.homologyFunctorFactors _ i).app _).symm ≪≫
        (DerivedCategory.homologyFunctor _ i).mapIso ((asIso (D.comparison.app P')).symm ≪≫
          D.functor.mapIso (asIso α) ≪≫ asIso (D.comparison.app P)) ≪≫
        (DerivedCategory.homologyFunctorFactors _ i).app _)
    exact h'.of_iso (((DerivedCategory.homologyFunctorFactors _ i).app P).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso (asIso α).symm ≪≫
      (DerivedCategory.homologyFunctorFactors _ i).app P')

end StacksDraft.PseudoCoherence

end
