module

public import StacksFrontier.AlgebraicGeometry.Perfect.CohomologyAndBaseChangeVanishing

/-!
# Cohomology and base change for a flat module without higher cohomology

Let `f : X ⟶ Spec A` be proper and `ℱ` a quasi-coherent `𝒪_X`-module flat over `A` with
`Hⁱ(X, ℱ) = 0` for all `i > 0`. Then for every ring map `A ⟶ B` and every base change `X'` of `X`
to `Spec B`, the pullback `ℱ'` of `ℱ` has no higher cohomology either, and the canonical map
`Γ(X, ℱ) ⊗_A B ⟶ Γ(X', ℱ')` is an isomorphism. No Noetherian hypothesis is made.

## Main results

* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.baseChange_exact_of_exactAt`: a bounded
  complex of flat modules, exact in positive degrees, stays exact in positive degrees after every
  base change, and so does the inclusion of the kernel of its first differential.
* `Stacks.AlgebraicGeometry.ProperFlatGlobalSections.cohomologyBaseChange_of_vanishing`: the
  statement above.

## References

* [Stacks Project, Tag 0B9X](https://stacks.math.columbia.edu/tag/0B9X)
* [Stacks Project, Tag 07VK](https://stacks.math.columbia.edu/tag/07VK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

universe u

namespace Stacks.AlgebraicGeometry.ProperFlatGlobalSections

attribute [local instance 10000] HasDerivedCategory.standard

section Acyclic

open Stacks.Cech

variable {A : Type u} [CommRing A]

/-- A bounded complex of flat modules, exact in positive degrees, stays exact in positive degrees
after every base change, and so does the inclusion of the kernel of its first differential. -/
theorem baseChange_exact_of_exactAt (L : CochainComplex (ModuleCat.{u} A) ℕ)
    [∀ n, Module.Flat A (L.X n)] (N : ℕ) (hN : ∀ m, N < m → Subsingleton (L.X m))
    (hex : ∀ n, L.ExactAt (n + 1)) {B : Type u} [CommRing B] (φ : A →+* B) :
    (∀ n, (((ModuleCat.extendScalars.{u, u, u} φ).mapHomologicalComplex
        (ComplexShape.up ℕ)).obj L).ExactAt (n + 1)) ∧
    ∀ {T : ModuleCat.{u} A} (ι : T ⟶ L.X 0), Function.Injective ι.hom →
      LinearMap.range ι.hom = LinearMap.ker (L.d 0 1).hom →
      letI : Algebra A B := φ.toAlgebra
      Function.Injective (ι.hom.baseChange B) ∧
        Function.Exact (ι.hom.baseChange B) ((L.d 0 1).hom.baseChange B) := by
  let d : ∀ n, L.X n →ₗ[A] L.X (n + 1) := fun n ↦ (L.d n (n + 1)).hom
  have hexA : ∀ m, Function.Exact (d m) (d (m + 1)) := fun m ↦ by
    have h := hex m
    rw [HomologicalComplex.exactAt_iff' _ m (m + 1) (m + 2) (by simp) (by simp),
      ShortComplex.moduleCat_exact_iff_range_eq_ker] at h
    exact LinearMap.exact_iff.2 h.symm
  let : Algebra A B := φ.toAlgebra
  obtain ⟨hPex, -, -⟩ :=
    (StacksDraft.FlatComplex.universallyExact.{u, u, u} d N hN 0 (fun m _ ↦ hexA m)).2 B
  refine ⟨fun n ↦ (exactAt_extendScalars_iff φ L n).2 ?_, fun ι hι hrange ↦ ?_⟩
  · simpa only [LinearMap.baseChange_eq_ltensor] using hPex n (Nat.zero_le _)
  · simpa only [LinearMap.baseChange_eq_ltensor] using
      StacksDraft.FlatComplex.lTensor_injective_and_exact_of_range_eq_ker d N hN hexA ι.hom hι
        hrange B

/-- The alternating Čech complex is exact in degree `n + 1` iff the `A`-linear model has zero
homology there. -/
private theorem exactAt_alternatingCechModuleComplex_iff {R : Type u} [CommRing R] {Y : Scheme.{u}}
    {g : Y ⟶ Spec (.of R)} {I : Type u} {V : I → Y.Opens} (hV : (⊤ : Y.Opens) = ⨆ i, V i)
    (G : Y.Modules) (n : ℕ) :
    (alternatingCechModuleComplex g V G).ExactAt (n + 1) ↔
      IsZero ((baseAlternatingCechComplex g V hV G).homology ((n + 1 : ℕ) : ℤ)) := by
  rw [HomologicalComplex.exactAt_iff_isZero_homology]
  exact Iso.isZero_iff ((HomologicalComplex.homologyFunctor _ _ ((n + 1 : ℕ) : ℤ)).mapIso
      (baseAlternatingCechComplexIsoExtend g V hV G) ≪≫
    HomologicalComplex.extendHomologyIso _ ComplexShape.embeddingUpNat
      (j := n + 1) (j' := ((n + 1 : ℕ) : ℤ)) rfl).symm

end Acyclic

section Main

open Stacks.Cech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (F : X.Modules)

/-- Let `f : X ⟶ Spec A` be proper and `F` a quasi-coherent `𝒪_X`-module flat over `A` with
`Hⁱ(X, F) = 0` for `i > 0`. Then for every ring map `φ : A ⟶ B` and every base change `X'` of `X`
to `B`, the pullback of `F` to `X'` has no cohomology in positive degrees, and its global sections
are the base change of `Γ(X, F)` along `φ`, through the canonical pullback of sections. -/
theorem cohomologyBaseChange_of_vanishing [IsProper f] [F.IsQuasicoherent]
    (hflat : IsFlatOver f.toLRSHom.toShHom F)
    (hvan : ∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections X).rightDerived i).obj F))
    {B : Type u} [CommRing B] (φ : A →+* B)
    {X' : Scheme.{u}} {f' : X' ⟶ Spec (.of B)} {g' : X' ⟶ X}
    (hsq' : IsPullback g' f' f (Spec.map (CommRingCat.ofHom φ))) :
    (∀ i : ℕ, 0 < i → Subsingleton
      (((moduleGlobalSections X').rightDerived i).obj ((Scheme.Modules.pullback g').obj F))) ∧
    letI : Algebra A B := φ.toAlgebra
    letI := sectionsModule f F ⊤
    letI := sectionsModule f' ((Scheme.Modules.pullback g').obj F) (g' ⁻¹ᵁ ⊤)
    letI := baseSectionsModule g' F φ f' (g' ⁻¹ᵁ ⊤)
    letI := isScalarTowerBaseSections g' F φ f' (g' ⁻¹ᵁ ⊤)
    IsBaseChange B (pullbackSectionsBaseₗ g' F φ f f'
      (fun W ↦ baseRingHom_comp_app _ f f' g' hsq' W) ⊤) := by
  classical
  obtain ⟨I, hI, hlo, U, hU, hUaff, haff⟩ := exists_finiteAffineCover_of_isProper f
  let L := alternatingCechModuleComplex f U F
  have : ∀ n, Module.Flat A (L.X n) := alternatingCechModuleComplex_flat f U F hUaff hflat
  have hN : ∀ m, Fintype.card I < m → Subsingleton (L.X m) := fun m hm ↦
    subsingleton_alternatingSubmodule f U F hm.le
  have hex : ∀ n, L.ExactAt (n + 1) := fun n ↦ by
    refine (exactAt_alternatingCechModuleComplex_iff hU F n).2 ?_
    refine IsZero.of_iso ?_ (homologyBaseAlternatingCechComplexIso f U hU F haff (n + 1))
    exact @ModuleCat.isZero_of_subsingleton _ _ _ (hvan (n + 1) (Nat.succ_pos n))
  obtain ⟨hBex, hBrow⟩ := baseChange_exact_of_exactAt L (Fintype.card I) hN hex φ
  let U' : I → X'.Opens := fun i ↦ g' ⁻¹ᵁ U i
  have hU'eq : ∀ i, U' i = g' ⁻¹ᵁ U ((Equiv.refl I) i) := fun _ ↦ rfl
  have : ((Scheme.Modules.pullback g').obj F).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineBaseChange.isQuasicoherent_pullback g' F
  let D := cechBaseChangeData φ f f' g' hsq' F U hUaff U' (Equiv.refl I) hU'eq
  have hU' : (⊤ : X'.Opens) = ⨆ i, U' i := top_eq_iSup_preimage g' U hU
  have haff' := iInf_preimage_isAffineOpen φ hsq' U hUaff
  constructor
  · intro i hi
    obtain ⟨n, rfl⟩ : ∃ n, i = n + 1 := ⟨i - 1, by omega⟩
    have hz : IsZero ((alternatingCechModuleComplex f' U'
        ((Scheme.Modules.pullback g').obj F)).homology (n + 1)) :=
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).1 (hBex n)).of_iso
        ((HomologicalComplex.homologyFunctor _ _ (n + 1)).mapIso D.alternatingIso).symm
    have hz' := (exactAt_alternatingCechModuleComplex_iff hU' _ n).1
      ((HomologicalComplex.exactAt_iff_isZero_homology _ _).2 hz)
    have hz'' := hz'.of_iso (homologyBaseAlternatingCechComplexIso f' U' hU' _ haff' (n + 1)).symm
    have hs := ModuleCat.subsingleton_of_isZero hz''
    exact hs
  · let : Algebra A B := φ.toAlgebra
    have hbase : ∀ W : X.Opens,
        baseRingHom f W ≫ g'.app W = CommRingCat.ofHom φ ≫ baseRingHom f' (g' ⁻¹ᵁ W) :=
      fun W ↦ baseRingHom_comp_app φ f f' g' hsq' W
    have hUW : ∀ i, U i ≤ (⊤ : X.Opens) := fun _ ↦ le_top
    have hcov : (⊤ : X.Opens) ≤ ⨆ i, U i := hU.le
    have hUW' := preimage_le_of_le U hUW g' U' (Equiv.refl I) hU'eq
    have hcov' : g' ⁻¹ᵁ (⊤ : X.Opens) ≤ ⨆ i, U' i := le_top.trans hU'.le
    let := sectionsModule f F ⊤
    let := sectionsModule f' ((Scheme.Modules.pullback g').obj F) (g' ⁻¹ᵁ ⊤)
    let := baseSectionsModule g' F φ f' (g' ⁻¹ᵁ ⊤)
    let := isScalarTowerBaseSections g' F φ f' (g' ⁻¹ᵁ ⊤)
    let := cochainModule f U F 0
    let := cochainModule f U F 1
    let := cochainModule f' U' ((Scheme.Modules.pullback g').obj F) 0
    let := cochainModule f' U' ((Scheme.Modules.pullback g').obj F) 1
    let := baseAlternatingModule g' U' F φ f' 0
    let := baseAlternatingModule g' U' F φ f' 1
    let := isScalarTowerBaseAlternating g' U' F φ f' 0
    let := isScalarTowerBaseAlternating g' U' F φ f' 1
    have hd0 : (L.d 0 1).hom = alternatingCechModuleD f U F 0 := by
      rw [show L.d 0 1 = alternatingCechModuleDiff f U F 0 from
        alternatingCechModuleComplex_d f U F 0]
      rfl
    have hrange := range_sectionsToAlternatingₗ f U F hUW hcov
    obtain ⟨inj₁, exact₁⟩ := hBrow (T := ModuleCat.of A Γ(F, ⊤))
      (ModuleCat.ofHom (sectionsToAlternatingₗ f U F hUW))
      (sectionsToAlternatingₗ_injective f U F hUW hcov) (by rwa [hd0])
    rw [hd0] at exact₁
    refine StacksDraft.FlatComplex.isBaseChange_of_left_exact_of_baseChange B
      (pullbackSectionsBaseₗ g' F φ f f' hbase ⊤)
      (alternatingCochainBaseChangeₗ g' U U' (Equiv.refl I) F hU'eq φ f f' hbase 0)
      (alternatingCochainBaseChangeₗ g' U U' (Equiv.refl I) F hU'eq φ f f' hbase 1)
      (f := sectionsToAlternatingₗ f U F hUW) (g := alternatingCechModuleD f U F 0)
      (f' := sectionsToAlternatingₗ f' U' ((Scheme.Modules.pullback g').obj F) hUW')
      (g' := alternatingCechModuleD f' U' ((Scheme.Modules.pullback g').obj F) 0)
      ?_ ?_ (isBaseChange_alternatingCochainBaseChangeₗ g' U U' (Equiv.refl I) F hU'eq φ f f'
        hbase hsq' hUaff 0)
      (isBaseChange_alternatingCochainBaseChangeₗ g' U U' (Equiv.refl I) F hU'eq φ f f'
        hbase hsq' hUaff 1) exact₁ inj₁
      (LinearMap.exact_iff.2 (range_sectionsToAlternatingₗ f' U'
        ((Scheme.Modules.pullback g').obj F) hUW' hcov').symm)
      (sectionsToAlternatingₗ_injective f' U' ((Scheme.Modules.pullback g').obj F) hUW' hcov')
    · ext s
      exact congrArg Subtype.val (alternatingCochainBaseChangeₗ_sectionsToAlternatingₗ f U F hUW
        g' U' (Equiv.refl I) hU'eq φ f' hbase s)
    · ext s
      exact (cochainBaseChange_cechD g' U U' (Equiv.refl I) F hU'eq 0 s.1).symm

end Main

end Stacks.AlgebraicGeometry.ProperFlatGlobalSections

end
