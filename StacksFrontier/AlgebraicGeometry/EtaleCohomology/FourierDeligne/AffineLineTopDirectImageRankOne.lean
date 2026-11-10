module

public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.AffineLineTopCompactSupportRankOne
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RelativeAffineLineTopLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SeparablyClosedFieldCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.GaloisTrivializationInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierGenericCoinvariantFibreSplit
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocallyFreeRankOneDual

/-!
# `H²(R f_! Λ)` on `Spec k` is étale-locally free of rank one, and invertible

Let `k` be a finite field, `Λ` a finite commutative ring in which `#k` is invertible and
`f : 𝔸¹_k ⟶ Spec k` with any compactification. The sheaf `T = H²(R f_! Λ)` on `(Spec k)_étale`
is étale-locally constant with value a module isomorphic to `Λ`, and `T` is invertible.

All names below are in the namespace `Stacks.EtaleCohomology`.

## Main results

* `nonempty_linearEquiv_globalSections_inverseImage_homology_two_derivedLowerShriek_tensorUnit`:
  at a geometric point `Spec Ω ⟶ Spec k`, the global sections of the inverse image of `T` are
  isomorphic to `Λ`.
* `isLocallyConstantWith_homology_two_derivedLowerShriek_tensorUnit`: `T` is étale-locally
  constant with value isomorphic to `Λ`.
* `isLocallyFreeEtaleModule_homology_two_derivedLowerShriek_tensorUnit`: `T` is étale-locally free
  of finite rank.
* `exists_invertible_homology_two_derivedLowerShriek_tensorUnit`: `T` is invertible, with an
  étale-locally free inverse.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ]

local notation "𝔸f" => affineLineStructureMap k

/-- **The global sections of `H²(R f_! Λ)` at a geometric point are `Λ`**: for an algebraically
closed extension `Ω` of `k`, `Γ(Spec Ω, H²(R f_! Λ)|_Ω) ≅ H²_c(𝔸¹_Ω, Λ) ≅ Λ`. -/
theorem nonempty_linearEquiv_globalSections_inverseImage_homology_two_derivedLowerShriek_tensorUnit
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f)) (Ω : Type u) [Field Ω]
    [IsAlgClosed Ω] [Algebra k Ω] :
    Nonempty ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
      ((etaleModuleInverseImage.{u, 0} Λ (Stacks.Frobenius.specAlgebraMap k Ω)).obj
        ((DerivedCategory.Plus.homologyFunctor _ 2).obj ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))))))) ≃ₗ[Λ] Λ) := by
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  let g := Stacks.Frobenius.specAlgebraMap k Ω
  let K := (derivedLowerShriek.{u, 0} 𝔸f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
    (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))))
  let Γ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))
  let e₁ : Γ.obj ((etaleModuleInverseImage.{u, 0} Λ g).obj
      ((DerivedCategory.Plus.homologyFunctor _ 2).obj K)) ≅
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 2).obj
        ((etaleModuleDerivedGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
          ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ g).obj K)) :=
    Γ.mapIso (etaleModuleInverseImageHomologyIso Λ g K 2) ≪≫
      (etaleModuleDerivedGlobalSectionsHomologyIsoOfIsSepClosed Ω Λ _ 2).symm
  let e₂ := derivedLowerShriekSingleStalkIso Λ 𝔸f j Ω
    (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))) 2
  let e₃ := (compactSupportSheafCohomology Λ 𝔸f j Ω 2).mapIso
    (Stacks.Cohomology.GlobalSections.tensorUnitIsoConstantModuleSheaf Λ
      (Spec (.of (Polynomial k))).smallEtaleTopology)
  obtain ⟨l⟩ := nonempty_linearEquiv_compactSupportSheafCohomology_two_constantSheaf_affineLine k Λ
    Ω hq j
  exact ⟨(e₁ ≪≫ e₂ ≪≫ e₃).toLinearEquiv.trans l⟩

/-- **`H²(R f_! Λ)` on `Spec k` is étale-locally constant with value `Λ`**, `#k` invertible in
`Λ`. -/
theorem isLocallyConstantWith_homology_two_derivedLowerShriek_tensorUnit
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f)) :
    Stacks.ConstantSheaf.IsLocallyConstantWith Λ (Spec (.of k)).smallEtaleTopology
      (fun E => Nonempty (E ≃ₗ[Λ] Λ))
      ((DerivedCategory.Plus.homologyFunctor _ 2).obj ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))))))) := by
  let T := (DerivedCategory.Plus.homologyFunctor _ 2).obj ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))))))
  intro U
  obtain ⟨I, V, f, hcov, htriv⟩ :=
    isFiniteTypeLocallyConstant_homology_derivedLowerShriek_tensorUnit_affineLine Λ k j 2 U
  refine ⟨{ i : I // Nonempty (V i).left }, fun i ↦ V i.1, fun i ↦ f i.1, ?_, fun i ↦ ?_⟩
  · rw [Scheme.ofArrows_mem_smallEtaleTopology_iff] at hcov ⊢
    refine Set.eq_univ_of_forall fun u ↦ ?_
    obtain ⟨i, w, hw⟩ := Set.mem_iUnion.1 (hcov ▸ Set.mem_univ u)
    exact Set.mem_iUnion.2 ⟨⟨i, ⟨w⟩⟩, w, hw⟩
  · obtain ⟨E, -, ⟨e⟩⟩ := htriv i.1
    obtain ⟨w⟩ := i.2
    let s := GeometricPoint.ofPoint (V i.1).left w
    let g : Spec (.of s.residueField) ⟶ Spec (.of k) := s.hom ≫ (V i.1).hom
    let : Algebra k s.residueField := (Spec.preimage g).hom.toAlgebra
    have hg : Stacks.Frobenius.specAlgebraMap k s.residueField = g := Spec.map_preimage g
    obtain ⟨l⟩ :=
      nonempty_linearEquiv_globalSections_inverseImage_homology_two_derivedLowerShriek_tensorUnit
        k Λ hq j s.residueField
    rw [hg] at l
    let e' := etaleModuleInverseImageIsoConstantOfOverPullback (V i.1) Λ T E e
    let e'' : (etaleModuleInverseImage.{u, 0} Λ g).obj T ≅
        (constantSheaf (Spec (.of s.residueField)).smallEtaleTopology
          (ModuleCat.{u + 1} Λ)).obj E :=
      (etaleModuleInverseImageCompIso Λ s.hom (V i.1).hom).app T ≪≫
        (etaleModuleInverseImage.{u, 0} Λ s.hom).mapIso e' ≪≫
        (etaleModuleInverseImageConstantIso Λ s.hom).app E
    have : HasLimitsOfSize.{0, u} (ModuleCat.{u + 1} Λ) := ModuleCat.hasLimitsOfSize.{0, u, u + 1}
    have : HasSheafify (Spec (.of s.residueField)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
      hasSheafifyEtale.{u, 0} (Spec (.of s.residueField)) Λ
    have := isEquivalence_globalSections_of_isSepClosed s.residueField (ModuleCat.{u + 1} Λ)
    let adj := constantSheafΓAdj (Spec (.of s.residueField)).smallEtaleTopology
      (ModuleCat.{u + 1} Λ)
    have := adj.isEquivalence_left_of_isEquivalence_right
    exact ⟨E, ⟨(asIso (adj.unit.app E) ≪≫ (etaleModuleGlobalSections.{u, 0} Λ
      (Spec (.of s.residueField))).mapIso e''.symm).toLinearEquiv.trans l⟩, ⟨e⟩⟩

/-- **`H²(R f_! Λ)` on `Spec k` is étale-locally free of finite rank**, `#k` invertible in `Λ`. -/
theorem isLocallyFreeEtaleModule_homology_two_derivedLowerShriek_tensorUnit
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f)) :
    IsLocallyFreeEtaleModule Λ
      ((DerivedCategory.Plus.homologyFunctor _ 2).obj ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))))))) :=
  isLocallyConstantWith_of_imp Λ (fun _ ⟨l⟩ ↦ ⟨Module.Free.of_equiv l.symm,
    Module.Finite.equiv l.symm⟩)
    (isLocallyConstantWith_homology_two_derivedLowerShriek_tensorUnit k Λ hq j)

/-- **`H²(R f_! Λ)` on `Spec k` is invertible**, `#k` invertible in `Λ`: it is étale-locally free,
and so is its dual `T'`, with `H²(R f_! Λ) ⊗ T' ≅ Λ` and `T' ⊗ H²(R f_! Λ) ≅ Λ`. -/
theorem exists_invertible_homology_two_derivedLowerShriek_tensorUnit
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f)) :
    IsLocallyFreeEtaleModule Λ
        ((DerivedCategory.Plus.homologyFunctor _ 2).obj ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))))))) ∧
      ∃ T' : EtaleModules.{u, 0} Λ (Spec (.of k)), IsLocallyFreeEtaleModule Λ T' ∧
        Nonempty ((DerivedCategory.Plus.homologyFunctor _ 2).obj
          ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))))) ⊗ T' ≅
          𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of k)))) ∧
        Nonempty (T' ⊗ (DerivedCategory.Plus.homologyFunctor _ 2).obj
          ((derivedLowerShriek.{u, 0} 𝔸f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
            (𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))))) ≅
          𝟙_ (EtaleModules.{u, 0} Λ (Spec (.of k)))) :=
  exists_invertible_of_rankOne _
    (isLocallyConstantWith_homology_two_derivedLowerShriek_tensorUnit k Λ hq j)

end Stacks.EtaleCohomology

end
