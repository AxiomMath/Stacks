module

public import StacksFrontier.Homology.Tor.DerivedFibreBoundedBelow

/-!
# Vanishing of the cohomology of derived base changes, degree by degree

Degreewise forms of the statements of `StacksFrontier.Homology.Tor.DerivedFibreBoundedBelow`: the
`i`-th cohomology of an object of `D(R)` is unchanged by restriction of scalars; the `i`-th
cohomology of the derived fibre `K ⊗^L_R L` along a ring map `R → L` to a field vanishes exactly
when that of `K ⊗^L_R κ(p)` does, `p` the kernel; and for a flat `R`-algebra `A`, a pushout
`A' = A ⊗_R R'` and `K ∈ D(A)`, the `i`-th cohomology of `K ⊗^L_A A'` vanishes exactly when that
of `K ⊗^L_R R'` does (Stacks 065Z for Tor independent squares).

## Main results

In the namespace `CochainComplex.DerivedExtensionScalars`:

* `isZero_homology_totalDerivedExtensionScalars_iff_residueField`
* `isZero_homology_totalDerivedExtensionScalars_iff_of_isPushout`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace CochainComplex.DerivedExtensionScalars

variable {R S : Type u} [CommRing R] [CommRing S]

/-- Restriction of scalars neither creates nor destroys cohomology in a given degree. -/
theorem isZero_homology_restrictScalars_mapDerivedCategory_obj_iff (f : R →+* S)
    (K : DerivedCategory (ModuleCat.{u} S)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj
        ((ModuleCat.restrictScalars.{u} f).mapDerivedCategory.obj K)) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj K) := by
  refine (Iso.isZero_iff ((StacksDraft.PseudoCoherence.mapDerivedCategoryHomologyIso
    (ModuleCat.restrictScalars.{u} f) i).app K)).trans ?_
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  exact Iff.rfl

/-- Derived extension of scalars along a faithfully flat ring map detects vanishing of the
cohomology in a given degree. -/
theorem isZero_homology_totalDerivedExtensionScalars_obj_iff_of_faithfullyFlat (f : R →+* S)
    (hf : f.FaithfullyFlat) (K : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} S) i).obj
        ((totalDerivedExtensionScalars.{u, u, u} f).functor.obj K)) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K) := by
  let := f.toAlgebra
  have : Module.FaithfullyFlat R S := hf
  refine (Iso.isZero_iff (derivedExtensionScalarsHomologyIso.{u, u, u} f hf.flat K i)).trans ?_
  change IsZero (ModuleCat.of S (TensorProduct R S
    ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj K))) ↔ _
  rw [ModuleCat.isZero_iff_subsingleton, ModuleCat.isZero_iff_subsingleton]
  exact Module.FaithfullyFlat.subsingleton_tensorProduct_iff_right R S

/-- **The derived fibre along a map to a field is read at the kernel, degree by degree.** For a
ring map `φ : R → L` to a field and `M ∈ D(R)`, the `i`-th cohomology of `M ⊗^L_R L` vanishes
exactly when that of `M ⊗^L_R κ(p)` does, for `p = ker φ`. -/
theorem isZero_homology_totalDerivedExtensionScalars_iff_residueField {L : Type u} [CommRing L]
    (hL : IsField L) (φ : R →+* L) (M : DerivedCategory (ModuleCat.{u} R)) (i : ℤ) :
    haveI := hL.isDomain
    haveI := RingHom.ker_isPrime φ
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} L) i).obj
        ((totalDerivedExtensionScalars.{u, u, u} φ).functor.obj M)) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} (RingHom.ker φ).ResidueField) i).obj
        ((totalDerivedExtensionScalars.{u, u, u}
          (algebraMap R (RingHom.ker φ).ResidueField)).functor.obj M)) := by
  have := hL.isDomain
  have := RingHom.ker_isPrime φ
  have : Nontrivial L := ⟨hL.exists_pair_ne⟩
  have hunit : (RingHom.ker φ).primeCompl ≤ Submonoid.comap φ (IsUnit.submonoid L) := by
    intro r hr
    obtain ⟨b, hb⟩ := hL.mul_inv_cancel fun h => hr (RingHom.mem_ker.2 h)
    exact IsUnit.of_mul_eq_one b hb
  let g := Ideal.ResidueField.lift (RingHom.ker φ) φ le_rfl hunit
  have hφ : φ = g.comp (algebraMap R (RingHom.ker φ).ResidueField) :=
    RingHom.ext fun r => (Ideal.ResidueField.lift_algebraMap _ φ le_rfl hunit r).symm
  let := g.toAlgebra
  have hff : g.FaithfullyFlat := (inferInstance : Module.FaithfullyFlat _ L)
  conv_lhs => rw [hφ]
  exact (Iso.isZero_iff ((DerivedCategory.homologyFunctor _ i).mapIso
      ((totalDerivedExtensionScalarsComp.{u, u} (algebraMap R (RingHom.ker φ).ResidueField)
        g).app M))).symm.trans
    (isZero_homology_totalDerivedExtensionScalars_obj_iff_of_faithfullyFlat g hff _ i)

/-- **Vanishing of the cohomology across a Tor independent base change, degree by degree.** For a
flat `R`-algebra `A`, a pushout `A' = A ⊗_R R'` and `K ∈ D(A)`, the `i`-th cohomology of
`K ⊗^L_A A'` vanishes exactly when that of `K ⊗^L_R R'` does, `K` being read over `R`. -/
theorem isZero_homology_totalDerivedExtensionScalars_iff_of_isPushout {A R' A' : Type u}
    [CommRing A] [CommRing R'] [CommRing A'] [Algebra R A] [Algebra R R'] [Algebra R A']
    [Algebra A A'] [Algebra R' A'] [IsScalarTower R A A'] [IsScalarTower R R' A']
    [Algebra.IsPushout R A R' A'] [Module.Flat R A] (K : DerivedCategory (ModuleCat.{u} A))
    (i : ℤ) :
    IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A') i).obj
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')).functor.obj K)) ↔
      IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R') i).obj
        ((totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')).functor.obj
          ((ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory.obj K))) := by
  let Tg := totalDerivedExtensionScalars.{u, u, u} (algebraMap R R')
  let Th := totalDerivedExtensionScalars.{u, u, u} (algebraMap A A')
  obtain ⟨cmp, hiso⟩ : ∃ cmp : (ModuleCat.restrictScalars.{u} (algebraMap R A)).mapDerivedCategory ⋙
      Tg.functor ⟶
        Th.functor ⋙ (ModuleCat.restrictScalars.{u} (algebraMap R' A')).mapDerivedCategory,
      IsIso cmp :=
    ⟨_, @RingTheory.TorIndependence.derivedBaseChangeComparison_isIso_of_torIndependent.{u,
      u, u, u, u, u + 1, u + 1, u + 1, u + 1} R A R' A' _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
      PseudoCoherence.torIndependent_of_flat Tg.functor Th.functor Tg.comparison Th.comparison
      Tg.isLeftDerived Th.isLeftDerived⟩
  refine (isZero_homology_restrictScalars_mapDerivedCategory_obj_iff (algebraMap R' A') _
    i).symm.trans ?_
  exact Iso.isZero_iff ((DerivedCategory.homologyFunctor _ i).mapIso (asIso (cmp.app K)).symm)

end CochainComplex.DerivedExtensionScalars

end
