module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierClosedTransform
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyConstantEtaleCover
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierSubsheafAnnihilatorLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.RelativeAffineLineTopLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AffineLineOpenCurve
public import StacksFrontier.AlgebraicGeometry.ProperSectionsGeom.FiniteReducedEtale
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleOpenClosedTriangle
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.EtaleModulesAPI
public import StacksFrontier.AlgebraicGeometry.CurveAffineOrHProjective.Witness

/-!
# The Fourier transform of a punctual constructible sheaf is lisse in degree zero

Let `k` be a finite field, `Λ` a finite commutative ring, `ψ` an additive character of `k` with
values in `Λ` and `Φ` the Fourier transform on `D⁺(𝔸¹_k, Λ)`. For a constructible sheaf `P` on
`𝔸¹_k` vanishing on a nonempty open `U`, `H⁰(Φ(P[0]))` is locally constant of finite type:

* the reduced closed complement `i : Z ⟶ 𝔸¹_k` of `U` is finite over `k`, and étale over `k`, `Z`
  being reduced and `k` perfect;
* `P ≅ i_* i⁻¹ P` (Tag 095L, `j_! j⁻¹ P = 0`);
* `i⁻¹ P` is constructible on the finite discrete `Z`, hence locally constant of finite type;
* `H⁰(Φ(i_* N))` is locally constant of finite type for such `N` (Tag 095B).

Applied to `C = H²(Φ(F[0]))` for `F` étale-locally free of finite rank (punctual by the generic
vanishing of geometric coinvariants, constructible by Tag 0GL0), this discharges the last
hypothesis `hC` of the mechanism (b) of the single-level argument for the irreducibility of the
Fourier transform in Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH);
the only named input left is `Stacks.EtaleCohomology.FourierTwistNoConstantQuotientInput`.

## Main results

* `isFiniteTypeLocallyConstant_homology_zero_fourierTransform_of_isPunctual`: `H⁰(Φ(P[0]))` is
  locally constant of finite type for a punctual constructible sheaf `P`.
* `isFiniteTypeLocallyConstant_homology_zero_fourierTransform_homology_two`: `H⁰(Φ(C[0]))` is
  locally constant of finite type for `C = H²(Φ(F[0]))`, `F` étale-locally free of finite rank.
* `nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_map_of_twist`: for a monomorphism
  `α : A ⟶ H¹(Φ(F[0]))` with `A` locally constant with finite values on a nonempty open,
  `n • H¹(Φ(α)) = 0` implies `n • 𝟙 A = 0`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so do the
statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

/-- **`H⁰(Φ(P[0]))` is locally constant of finite type for a punctual constructible `P`**: `P` is
the direct image of its restriction to the reduced closed complement `Z` of an open where it
vanishes, `Z` is finite étale over `k` and the restriction is locally constant on `Z`. -/
theorem isFiniteTypeLocallyConstant_homology_zero_fourierTransform_of_isPunctual
    (j : CompactificationOf (Over.mk 𝔸f)) (P : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k))))
    (hP : IsPunctualEtaleModule Λ P) (hPc : IsConstructibleEtaleModule Λ P) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (Spec (.of (Polynomial k))).smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((fourierTransform k Λ ψ B p₀ j).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj P))) := by
  obtain ⟨U, jU, hjU, hU, hz⟩ := hP
  have := hjU
  have := hU
  let i := closedComplementι jU
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : IsFinite (i ≫ 𝔸f) := isFinite_closedComplementι_comp_of_irreducibleSpace 𝔸f jU
    (topologicalKrullDim_specPolynomial k).le
  have : Etale (i ≫ 𝔸f) :=
    Stacks.AlgebraicGeometry.ProperSectionsGeom.etale_of_isFinite_of_isReduced (i ≫ 𝔸f)
  have hN := isFiniteTypeLocallyConstant_of_isConstructibleEtaleModule_of_isFinite Λ (i ≫ 𝔸f)
    (isConstructibleEtaleModule_etaleModuleInverseImage Λ i P hPc)
  obtain ⟨h₀, hS⟩ := shortExact_etaleModuleExtensionByZero_directImage Λ i jU
    (range_eq_compl_range_closedComplementι jU) P
  have h₁ : IsZero ((etaleModuleExtensionByZero.{u, 0} Λ jU).obj
      ((etaleModuleRestriction.{u, 0} Λ jU).obj P)) :=
    (etaleModuleExtensionByZero.{u, 0} Λ jU).map_isZero
      (hz.of_iso ((etaleModuleInverseImageRestrictionIso.{u, 0} Λ jU).app P).symm)
  have : IsIso ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app P) :=
    (ShortComplex.ShortExact.isIso_g_iff hS).2 h₁
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
    ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso ((fourierTransform k Λ ψ B p₀ j).mapIso
      ((DerivedCategory.Plus.singleFunctor _ 0).mapIso
        (asIso ((etaleModuleInverseImageAdj.{u, 0} Λ i).unit.app P))))).symm
    (isFiniteTypeLocallyConstant_homology_zero_fourierTransform_directImage k Λ ψ B p₀ j i _ hN)

/-- **`H⁰(Φ(C[0]))` is locally constant of finite type for `C = H²(Φ(F[0]))`**, `F` étale-locally
free of finite rank on `𝔸¹_k`: `C` is punctual (generic vanishing of geometric coinvariants, from
the twist input `FourierTwistNoConstantQuotientInput`) and constructible (Tag 0GL0). -/
theorem isFiniteTypeLocallyConstant_homology_zero_fourierTransform_homology_two
    (hT : FourierTwistNoConstantQuotientInput.{u}) (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (Spec (.of (Polynomial k))).smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((DerivedCategory.Plus.homologyFunctor _ 2).obj
            ((fourierTransform k Λ ψ B p₀ j).obj
              ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))))) := by
  have : IsNoetherianRing Λ := inferInstance
  have hFc := isConstructibleEtaleModule_of_isLocallyFreeEtaleModule Λ hF
  have hH : Stacks.ConstantSheaf.IsLocallyConstantWith Λ
      (Spec (.of (Polynomial k))).smallEtaleTopology (fun E => Module.Finite Λ E)
      ((etaleModuleInverseImage.{u, 0} Λ (𝟙 (Spec (.of (Polynomial k))))).obj F) :=
    isLocallyConstantWith_inverseImage Λ _ (𝟙 _)
      (isLocallyConstantWith_of_imp Λ (fun _ hE => hE.2) hF)
  exact isFiniteTypeLocallyConstant_homology_zero_fourierTransform_of_isPunctual k Λ ψ B p₀ j _
    (isPunctualEtaleModule_homology_two_fourierTransform_of_twist k Λ ψ B p₀ hT hψ hq j F
      (𝟙 _) hH)
    (isConstructibleEtaleModule_homology_fourierTransform k Λ ψ B p₀ j F hFc 2)

/-- **Mechanism (b) for a subsheaf of `G = H¹(Φ(F[0]))`, with the twist input as its only named
input**: for `F` étale-locally free of finite rank on `𝔸¹_k`, `α : A ⟶ G` a monomorphism with `A`
locally constant with finite values on a nonempty open, `n • H¹(Φ(α)) = 0` implies
`n • 𝟙 A = 0`. -/
theorem nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_map_of_twist
    (hT : FourierTwistNoConstantQuotientInput.{u}) (hψ : ∑ a : k, ψ a = 0)
    (hq : IsUnit (Fintype.card k : Λ)) (j : CompactificationOf (Over.mk 𝔸f))
    (jQ : CompactificationOf (Over.mk (tripleProduct₂₃ 𝔸f 𝔸f 𝔸f ≫ pullback.snd 𝔸f 𝔸f)))
    (F : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))) (hF : IsLocallyFreeEtaleModule Λ F)
    {A : EtaleModules.{u, 0} Λ (Spec (.of (Polynomial k)))}
    (α : A ⟶ (DerivedCategory.Plus.homologyFunctor _ 1).obj
      ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
    [Mono α] (n : ℕ)
    (hu : n • (DerivedCategory.Plus.homologyFunctor _ 1).map
      ((fourierTransform k Λ ψ B p₀ j).map ((DerivedCategory.Plus.singleFunctor _ 0).map α)) = 0)
    {V : Scheme.{u}} (jV : V ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion jV] [Nonempty V]
    (hA : Stacks.ConstantSheaf.IsLocallyConstantWith Λ V.smallEtaleTopology
      (fun E => Module.Finite Λ E) ((etaleModuleInverseImage.{u, 0} Λ jV).obj A)) :
    n • 𝟙 A = 0 :=
  nsmul_id_eq_zero_of_nsmul_homology_one_fourierTransform_homology_one_map k Λ ψ B p₀ hT hψ hq j
    jQ F hF (isFiniteTypeLocallyConstant_homology_two_fourierTransform_comp Λ k ψ B p₀ hψ hq j jQ F
      hF 2)
    (isFiniteTypeLocallyConstant_homology_zero_fourierTransform_homology_two k Λ ψ B p₀ hT hψ hq j
      F hF) α n hu jV hA

end Stacks.EtaleCohomology

end
