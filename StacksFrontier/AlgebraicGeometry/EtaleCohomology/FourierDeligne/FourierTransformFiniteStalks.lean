module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformAmplitude
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyFreeTensor
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.LowerShriekHomologyBaseChange
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionModules.CompactSupportCurveFiniteness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactSupportCurves.ConstructibleBigSiteIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesAPI
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantIsConstructible
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.ProperFrobeniusLeray

/-!
# The Fourier transform has finite geometric stalks

Let `k` be a finite field, `Λ` a finite commutative ring, `ψ` an additive character of `k` with
values in `Λ` and `Φ(K) = R pr₂!(pr₁⁻¹ K ⊗ μ⁻¹ L_ψ)` the Fourier transform on `D⁺(𝔸¹_k, Λ)`. For a
sheaf `A` of `Λ`-modules on `𝔸¹_k` whose integrand `pr₁⁻¹ A ⊗ μ⁻¹ L_ψ` is constructible (for
instance `A` étale-locally free of finite rank), every cohomology sheaf `Hⁱ(Φ(A[0]))` has finite
geometric stalks: for an algebraically closed field `Ω` and `w : Spec Ω ⟶ 𝔸¹_k`,

`Γ(Spec Ω, w⁻¹ Hⁱ(Φ(A[0]))) ≅ Hⁱ_c(𝔸¹_Ω, (pr₁⁻¹ A ⊗ μ⁻¹ L_ψ)|_{𝔸¹_Ω})`

by proper base change for `Rf_!` ([Stacks, Tag 0F7L]), and the right hand side is finite by
[Stacks, Tag 0GKR] on the curve `𝔸¹_Ω`, the restriction of a constructible sheaf being
constructible ([Stacks, Tag 095G]).

This removes the finiteness hypotheses of the single-level argument for the irreducibility of the
Fourier transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

All names are in the namespace `Stacks.EtaleCohomology`.

* `isConstructibleEtaleModule_of_isFiniteTypeLocallyConstant`,
  `isConstructibleEtaleModule_of_isLocallyFreeEtaleModule`.
* `finite_globalSections_homology_derivedLowerShriek_of_isConstructible`: Tag 0GKR over an
  algebraically closed field, as a finiteness of `Γ(Hⁱ(Rf_!(G[0])))`.
* `finite_globalSections_inverseImage_lowerShriekHomology`: the geometric stalks of `Rⁱf_! Q`.
* `finite_globalSections_inverseImage_homology_fourierTransform`,
  `finite_globalSections_inverseImage_homology_fourierTransform_of_isLocallyFreeEtaleModule`.

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

section Constructible

variable (Λ : Type) [CommRing Λ]

/-- **A locally constant sheaf of finite type is constructible** ([Stacks, Tag 03RW]): its
transport to the small étale site of Tag 021B is locally constant of finite type
([Stacks, Tag 093U]), and such a sheaf is constructible. -/
theorem isConstructibleEtaleModule_of_isFiniteTypeLocallyConstant [IsNoetherianRing Λ]
    {X : Scheme.{u}} {F : EtaleModules.{u, 0} Λ X}
    (hF : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ X.smallEtaleTopology F) :
    IsConstructibleEtaleModule Λ F := by
  let B := BigEtaleSite.containing X
  have hX : B.Contains X := BigEtaleSite.contains_containing X
  have := fun (S T : B.Scheme) (f : T ⟶ S) =>
    SmallEtale.isRightAdjointPushforward_moduleCat.{u, 0, 0} B Λ f
  have := SmallEtale.hasWeakSheafifyOver_moduleCat.{u, 0, 0} B Λ
  refine (isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hX F).2 ?_
  refine isConstructibleModuleSheaf_of_isFiniteTypeLocallyConstant B (B.obj X hX) Λ _ ?_
  exact (isFiniteTypeLocallyConstantModuleSheaf_etaleModuleToBoundedSite_iff Λ B hX F).2 hF

/-- **An étale-locally free sheaf of finite rank is constructible**: it is locally constant of
finite type. -/
theorem isConstructibleEtaleModule_of_isLocallyFreeEtaleModule [IsNoetherianRing Λ]
    {X : Scheme.{u}} {F : EtaleModules.{u, 0} Λ X} (hF : IsLocallyFreeEtaleModule Λ F) :
    IsConstructibleEtaleModule Λ F :=
  isConstructibleEtaleModule_of_isFiniteTypeLocallyConstant Λ fun U => by
    obtain ⟨I, V, f, hcov, h⟩ := hF U
    exact ⟨I, V, f, hcov, fun i => (h i).elim fun E ⟨hE, e⟩ =>
      ⟨E, (ModuleCat.isFG_iff E).2 hE.2, e⟩⟩

end Constructible

section Fibre

variable (Λ : Type) [CommRing Λ] [Finite Λ]

/-- **[Stacks, Tag 0GKR] over an algebraically closed field, on global sections of `Rf_!`**: for
`X` separated of finite type over an algebraically closed field `Ω`, of dimension at most one, and
`G` a constructible sheaf of modules over a finite ring, `Γ(Spec Ω, Hⁱ(Rf_!(G[0])))` is finite:
it is `Hⁱ_c(X, G)`, global sections being exact over `Ω`. -/
theorem finite_globalSections_homology_derivedLowerShriek_of_isConstructible (Ω : Type u)
    [Field Ω] [IsAlgClosed Ω] {X : Scheme.{u}} (f : X ⟶ Spec (.of Ω)) [LocallyOfFiniteType f]
    [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (hX : topologicalKrullDim X ≤ 1) (G : EtaleModules.{u, 0} Λ X)
    (hG : IsConstructibleEtaleModule Λ G) (q : ℤ) :
    Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
      ((DerivedCategory.Plus.homologyFunctor _ q).obj
        ((derivedLowerShriek.{u, 0} f j Λ).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj G)))) := by
  have : HasLimitsOfSize.{0, u} (ModuleCat.{u + 1} Λ) := ModuleCat.hasLimitsOfSize.{0, u, u + 1}
  have : HasSheafify (Spec (.of Ω)).smallEtaleTopology (ModuleCat.{u + 1} Λ) :=
    hasSheafifyEtale.{u, 0} (Spec (.of Ω)) Λ
  have := isEquivalence_globalSections_of_isSepClosed Ω (ModuleCat.{u + 1} Λ)
  let Γ := etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))
  let K := (derivedLowerShriek.{u, 0} f j Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G)
  let B := BigEtaleSite.containing X
  have hXB : B.Contains X := BigEtaleSite.contains_containing X
  have := TorsionModules.module_finite_compactlySupportedCohomologyGroup B (B.obj X hXB) f hX j
    Λ G ((isConstructibleEtaleModule_iff_isConstructibleModuleSheaf Λ B hXB G).1 hG)
    (isTorsionEtaleModule_of_finite Λ X G) q
  let e := (Stacks.DerivedFunctor.exactRightDerivedPlusHomologyIso Γ q).app K
  have : Module.Finite Λ (Γ.obj ((DerivedCategory.Plus.homologyFunctor _ q).obj K)) :=
    Module.Finite.equiv (M := (compactlySupportedCohomologyGroup.{u, 0} Ω f j Λ q).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj G)) e.toLinearEquiv
  exact Module.finite_of_finite Λ

/-- **The geometric stalks of `Rⁱf_! Q` are finite**, for `Q` a sheaf of modules over a finite ring
whose restriction to the geometric fibre `X_w` at `w : Spec Ω ⟶ Y` (`Ω` algebraically closed) is
constructible, of dimension at most one: by proper base change for `Rf_!` ([Stacks, Tag 0F7L])
`w⁻¹ Rⁱf_! Q ≅ Rⁱ(f_w)_!(Q|_{X_w})`, whose global sections are finite by Tag 0GKR. -/
theorem finite_globalSections_inverseImage_lowerShriekHomology {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] (j : CompactificationOf (Over.mk f))
    (Q : EtaleModules.{u, 0} Λ X) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Y)
    (hdim : topologicalKrullDim ↥(pullback f w) ≤ 1)
    (hQ : IsConstructibleEtaleModule Λ
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst f w)).obj Q))
    (q : ℤ) :
    Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
      ((etaleModuleInverseImage.{u, 0} Λ w).obj ((lowerShriekHomology Λ f j q).obj Q))) := by
  let sq := IsPullback.of_hasPullback f w
  let f' := pullback.snd f w
  let j' := j.baseChange sq
  obtain ⟨e⟩ := nonempty_lowerShriekHomology_inverseImage_iso Λ sq j j' Q (Nat.card Λ)
    Nat.card_pos (natCard_nsmul_id_etaleModules Λ Q) q
  exact @Finite.of_equiv _ _
    (finite_globalSections_homology_derivedLowerShriek_of_isConstructible Λ Ω f' j' hdim _ hQ q)
    ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).mapIso e).toLinearEquiv.toEquiv

end Fibre

section Transform

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- **The cohomology sheaves of `Φ(A[0])` have finite geometric stalks** for a sheaf `A` on `𝔸¹_k`
whose integrand `pr₁⁻¹ A ⊗ μ⁻¹ L_ψ` is constructible: the stalk at `w : Spec Ω ⟶ 𝔸¹_k` is
`Hⁱ_c` of the restriction of the integrand to the affine line `𝔸¹_Ω`. -/
theorem finite_globalSections_inverseImage_homology_fourierTransform
    (j : CompactificationOf (Over.mk 𝔸f)) (A : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    (hA : IsConstructibleEtaleModule Λ
      ((etaleModuleInverseImage.{u, 0} Λ (pullback.fst 𝔸f 𝔸f)).obj A ⊗
      (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
        (affineLineArtinSchreierSheaf k Λ ψ B p₀)))
    (i : ℤ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω] (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))) :
    Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
      ((etaleModuleInverseImage.{u, 0} Λ w).obj ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((fourierTransform k Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj A))))) := by
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let 𝓛 := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
    (affineLineArtinSchreierSheaf k Λ ψ B p₀)
  have h𝓛e := isExactTensorRight_fourierKernel k Λ ψ B p₀
  let G := (etaleModuleInverseImage.{u, 0} Λ pr₁).obj A ⊗ 𝓛
  let sq := IsPullback.of_hasPullback 𝔸f 𝔸f
  let jP := j.baseChange sq
  have := h𝓛e.1
  have := h𝓛e.2.1
  have := h𝓛e.2.2
  let eT : (fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj A) ≅
      (derivedLowerShriek.{u, 0} pr₂ jP Λ).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj G) :=
    (derivedLowerShriek.{u, 0} pr₂ jP Λ).mapIso
      ((etaleModuleDerivedTensorRight Λ 𝓛 h𝓛e).mapIso
          ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
            (etaleModuleInverseImage.{u, 0} Λ pr₁) 0).app A) ≪≫
        (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
          (MonoidalCategory.tensorRight 𝓛) 0).app _)
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  exact @Finite.of_equiv _ _ (finite_globalSections_inverseImage_lowerShriekHomology Λ pr₂ jP G Ω w
    (by exact_mod_cast topologicalKrullDim_affineLineFibre_le_one k Ω w)
    (isConstructibleEtaleModule_etaleModuleInverseImage Λ _ G hA) i)
    ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).mapIso
      ((etaleModuleInverseImage.{u, 0} Λ w).mapIso
        ((DerivedCategory.Plus.homologyFunctor _ i).mapIso eT.symm))).toLinearEquiv.toEquiv

/-- **For `F` étale-locally free of finite rank, the cohomology sheaves of `Φ(F[0])` have finite
geometric stalks**: the integrand `pr₁⁻¹ F ⊗ μ⁻¹ L_ψ` is étale-locally free of finite rank, hence
constructible. -/
theorem finite_globalSections_inverseImage_homology_fourierTransform_of_isLocallyFreeEtaleModule
    (j : CompactificationOf (Over.mk 𝔸f)) (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    (hF : IsLocallyFreeEtaleModule Λ F) (i : ℤ) (Ω : Type u) [Field Ω] [IsAlgClosed Ω]
    (w : Spec (.of Ω) ⟶ Spec (.of (Polynomial k))) :
    Finite ((etaleModuleGlobalSections.{u, 0} Λ (Spec (.of Ω))).obj
      ((etaleModuleInverseImage.{u, 0} Λ w).obj ((DerivedCategory.Plus.homologyFunctor _ i).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F))))) :=
  finite_globalSections_inverseImage_homology_fourierTransform k Λ ψ B p₀ j F
    (isConstructibleEtaleModule_of_isLocallyFreeEtaleModule Λ
      (isLocallyFreeEtaleModule_tensor Λ (isLocallyFreeEtaleModule_inverseImage Λ _ hF)
        (isLocallyFreeEtaleModule_fourierKernel k Λ ψ B p₀))) i Ω w

end Transform

end Stacks.EtaleCohomology

end
