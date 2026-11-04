module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyExt
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleRestrictScalarsCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.GeometricLAdicVanishingSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.Boundedness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.CoverTriangleModules
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ProperBaseChange.ProperBaseChangeTheoremUnconditional

/-!
# The amplitude of the Fourier transform of a sheaf

Let `k` be a finite field, `Λ` a finite commutative ring, `ψ` an additive character of `k` with
values in `Λ` and `Φ(K) = R pr₂!(pr₁⁻¹ K ⊗ μ⁻¹ L_ψ)` the Fourier transform on `D⁺(𝔸¹_k, Λ)`. For
every sheaf `H` of `Λ`-modules on `𝔸¹_k`,

`Hⁱ(Φ(H[0])) = 0` for `i < 0` and for `i > 2`.

Over a separably closed field `Ω`, `Hⁱ_c(X, G) = Hⁱ(Rf_!(G[0]))` vanishes for `i > 2 dim X`.

## Main results

* `Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_two_mul_lt`: `Hⁱ_c(X, G) = 0` for
  `i > 2 dim X` over a separably closed field, as a vanishing of `Hⁱ(Rf_!(G[0]))`.
* `Stacks.EtaleCohomology.isZero_homology_fourierTransform_of_two_lt`,
  `Stacks.EtaleCohomology.isZero_homology_fourierTransform_of_neg`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so do the
statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry Opposite
  Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

section Fibre

variable (Λ : Type) [CommRing Λ] [Finite Λ]

/-- **`Hⁱ(Rf_!(G[0])) = 0` for `i > 2 dim X` over a separably closed field**, for every sheaf `G`
of modules over a finite ring. -/
theorem isZero_homology_derivedLowerShriek_of_two_mul_lt (Ω : Type u) [Field Ω] [IsSepClosed Ω]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of Ω)) [LocallyOfFiniteType f] [QuasiCompact f]
    [IsSeparated f] (j : CompactificationOf (Over.mk f)) (n : ℕ)
    (hX : topologicalKrullDim X ≤ n) (G : EtaleModules.{u, 0} Λ X) (i : ℤ)
    (hi : 2 * (n : ℤ) < i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((derivedLowerShriek.{u, 0} f j Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) := by
  obtain ⟨q, rfl⟩ : ∃ q : ℕ, i = q := ⟨i.toNat, by lia⟩
  have : HasLimitsOfSize.{0, u} (ModuleCat.{u + 1} Λ) := ModuleCat.hasLimitsOfSize.{0, u, u + 1}
  have : HasSheafify (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    hasSheafifyEtale.{u, 0} (Spec (.of Ω)) Λ
  have := isEquivalence_globalSections_of_isSepClosed Ω (ModuleCat.{u + 1} Λ)
  let Γ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))
  let K := (derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  have hw : j.immersion ≫ j.toBase = f := Over.w j.obj.hom
  have : QuasiCompact (j.immersion ≫ j.toBase) := by rw [hw]; infer_instance
  have : QuasiCompact j.immersion := QuasiCompact.of_comp _ j.toBase
  have hV : ∀ {V : Scheme.{u}} (v : V ⟶ j.space) [IsOpenImmersion v],
      Disjoint (Set.range v) (Set.range j.immersion) →
      IsZero ((etaleRestriction.{u, 0} v).obj ((etaleModuleUnderlyingAbelian j.space Λ).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj G))) := by
    intro V v _ hv
    have h0 : IsZero ((etaleModuleRestriction.{u, 0} Λ v).obj
        ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj G)) :=
      (isZero_etaleModuleInverseImage_extensionByZero_of_disjoint Λ v j.immersion hv G).of_iso
        ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ v).app _).symm
    refine isZero_of_forall_isZero_sections.{u, 0} _ fun W ↦ ?_
    have hW := ((sheafToPresheaf _ _ ⋙ (CategoryTheory.evaluation _ _).obj (op W)).map_isZero h0)
    change IsZero ((forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).obj
      (_ : ModuleCat.{u + 1} Λ))
    exact (forget₂ (ModuleCat.{u + 1} Λ) AddCommGrpCat.{u + 1}).map_isZero hW
  have htors := torsionSheafProperty_etaleModuleForget_obj_of_nsmul_eq_zero Λ (Nat.card Λ)
    Nat.card_pos (by rw [← nsmul_one]; exact card_nsmul_eq_zero')
    ((etaleModuleExtensionByZero.{u, 0} Λ j.immersion).obj G)
  have hH := subsingleton_sheafH_of_isZero_etaleRestriction_of_disjoint
    (properSeparablyClosedSheafHVanishingStatement_of_properDirectImageVanishingStatement
      properDirectImageVanishingStatement) Ω j.toBase j.immersion n hX _ htors hV q
    (by exact_mod_cast hi)
  have e :=
    (compactlySupportedCohomologyGroupSingleIsoExt Λ Ω f j G q).addCommGroupIsoToAddEquiv.trans
      (extConstantAddEquivSheafH j.space _ q)
  have hc : IsZero ((compactlySupportedCohomologyGroup.{u, 0} Ω f j Λ q).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) :=
    @ModuleCat.isZero_of_subsingleton _ _ _ e.toEquiv.subsingleton
  have h1 : IsZero (Γ.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) :=
    hc.of_iso ((Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso Γ q).app K).symm
  rw [IsZero.iff_id_eq_zero]
  exact Γ.map_injective (by rw [Γ.map_id, Functor.map_zero]; exact h1.eq_of_src _ _)

end Fibre

variable (k : Type u) [Field k]

local notation "𝔸f" => affineLineStructureMap k

/-- **The fibres of `pr₂ : 𝔸¹ ×_k 𝔸¹ ⟶ 𝔸¹` over the spectra of fields have dimension at most
one.** -/
theorem topologicalKrullDim_affineLineFibre_le_one (Ω : Type u) [Field Ω]
    (s : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))) :
    topologicalKrullDim ↥(pullback (pullback.snd 𝔸f 𝔸f) s) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨e, -⟩ := nonempty_affineLineFibre_iso k s
  rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph]
  calc topologicalKrullDim (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)))
      = topologicalKrullDim (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin 1)) Ω)) :=
        IsHomeomorph.topologicalKrullDim_eq _
          (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
            (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of Ω)))).isHomeomorph
    _ = ringKrullDim (MvPolynomial (ULift.{u} (Fin 1)) Ω) :=
        PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
    _ = ringKrullDim Ω + Nat.card (ULift.{u} (Fin 1)) :=
        MvPolynomial.ringKrullDim_of_isNoetherianRing
    _ ≤ ((1 : ℕ) : WithBot ℕ∞) := by simp

section Transform

variable [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

/-- The homology of `Φ(H[0])` is that of `Rpr₂_!` of the single sheaf `pr₁⁻¹ H ⊗ μ⁻¹ L_ψ`. -/
private theorem isZero_homology_fourierTransform_of_isZero_homology_lowerShriek
    (j : CompactificationOf (Over.mk 𝔸f))
    (H : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (i : ℤ)
    (h : IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((derivedLowerShriek.{u, 0} (pullback.snd 𝔸f 𝔸f)
        (j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)) Λ).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst 𝔸f 𝔸f)).obj H ⊗
            (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
              (affineLineArtinSchreierSheaf k Λ ψ B p₀)))))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj H))) := by
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let 𝓛 := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
    (affineLineArtinSchreierSheaf k Λ ψ B p₀)
  have h𝓛e := isExactTensorRight_fourierKernel k Λ ψ B p₀
  let G := (etaleModuleInverseImage.{u, 0} Λ pr₁).obj H ⊗ 𝓛
  let jP := j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)
  have := h𝓛e.1
  have := h𝓛e.2.1
  have := h𝓛e.2.2
  let eT : (fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj H) ≅
      (derivedLowerShriek.{u, 0} pr₂ jP Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G) :=
    (derivedLowerShriek.{u, 0} pr₂ jP Λ).mapIso
      ((etaleModuleDerivedTensorRight Λ 𝓛 h𝓛e).mapIso
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
            (etaleModuleInverseImage.{u, 0} Λ pr₁) 0).app H) ≪≫
        (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (MonoidalCategory.tensorRight 𝓛) 0).app _)
  exact IsZero.of_iso h ((DerivedCategory.Plus.homologyFunctor _ i).mapIso eT)

/-- **`Hⁱ(Φ(H[0])) = 0` for `i > 2`**, for every sheaf `H` of `Λ`-modules on `𝔸¹_k`. -/
theorem isZero_homology_fourierTransform_of_two_lt (j : CompactificationOf (Over.mk 𝔸f))
    (H : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (i : ℤ) (hi : 2 < i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj H))) := by
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let 𝓛 := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
    (affineLineArtinSchreierSheaf k Λ ψ B p₀)
  let G := (etaleModuleInverseImage.{u, 0} Λ pr₁).obj H ⊗ 𝓛
  let jP := j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)
  refine isZero_homology_fourierTransform_of_isZero_homology_lowerShriek k Λ ψ B p₀ j H i ?_
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : CompactSpace ↥(pullback 𝔸f 𝔸f) := QuasiCompact.compactSpace_of_compactSpace pr₂
  have : LocallyOfFiniteType pr₂ := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (IsPullback.of_hasPullback 𝔸f 𝔸f) inferInstance
  have : IsSeparated pr₂ := MorphismProperty.of_isPullback (P := @IsSeparated)
    (IsPullback.of_hasPullback 𝔸f 𝔸f) inferInstance
  have : QuasiCompact pr₂ := MorphismProperty.of_isPullback (P := @QuasiCompact)
    (IsPullback.of_hasPullback 𝔸f 𝔸f) inferInstance
  refine isZero_homology_derivedLowerShriek_of_geometricFibres Λ pr₂ jP _ (Nat.card Λ)
    Nat.card_pos ?_ i
    fun y => ?_
  · rw [← CategoryTheory.Functor.map_id (DerivedCategory.Plus.singleFunctor _ 0),
      ← Functor.map_nsmul, natCard_nsmul_id_etaleModules Λ G, Functor.map_zero]
  let s := (GeometricPoint.ofPoint (Spec (.of (Polynomial k))) y).hom
  let Ω := (GeometricPoint.ofPoint (Spec (.of (Polynomial k))) y).residueField
  let f' := pullback.snd pr₂ s
  let u' := pullback.fst pr₂ s
  have : LocallyOfFiniteType f' := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (IsPullback.of_hasPullback pr₂ s) inferInstance
  have : IsSeparated f' := MorphismProperty.of_isPullback (P := @IsSeparated)
    (IsPullback.of_hasPullback pr₂ s) inferInstance
  have : QuasiCompact f' := MorphismProperty.of_isPullback (P := @QuasiCompact)
    (IsPullback.of_hasPullback pr₂ s) inferInstance
  let j' := jP.baseChange (IsPullback.of_hasPullback pr₂ s)
  refine IsZero.of_iso
    (isZero_homology_derivedLowerShriek_of_two_mul_lt Λ Ω f' j' 1
      (topologicalKrullDim_affineLineFibre_le_one k Ω s) _ i (by lia))
    ((DerivedCategory.Plus.homologyFunctor _ i).mapIso ((derivedLowerShriek.{u, 0} f' j' Λ).mapIso
      ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (etaleModuleInverseImage.{u, 0} Λ u') 0).app G)))

/-- **`Hⁱ(Φ(H[0])) = 0` for `i < 0`**, for every sheaf `H` of `Λ`-modules on `𝔸¹_k`. -/
theorem isZero_homology_fourierTransform_of_neg (j : CompactificationOf (Over.mk 𝔸f))
    (H : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (i : ℤ) (hi : i < 0) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj H))) := by
  refine isZero_homology_fourierTransform_of_isZero_homology_lowerShriek k Λ ψ B p₀ j H i ?_
  have := isGE_derivedLowerShriek_obj Λ (pullback.snd 𝔸f 𝔸f)
    (j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f))
    ((DerivedCategory.Plus.singleFunctor _ 0).obj
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst 𝔸f 𝔸f)).obj H ⊗
        (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
          (affineLineArtinSchreierSheaf k Λ ψ B p₀))) 0
  exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 i hi

end Transform

end Stacks.EtaleCohomology

end
