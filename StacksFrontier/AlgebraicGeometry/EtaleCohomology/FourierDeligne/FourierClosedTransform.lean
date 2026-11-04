module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierPointTransform
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyConstantTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FiniteLocallyConstant.FiniteEtalePushforward
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomologyUnboundedExactness
public import StacksFrontier.Algebra.Homology.DerivedCategory.PlusTwoDegreeTriangle

/-!
# The Fourier transform of a sheaf supported on a finite étale closed subscheme

Let `k` be a finite field, `Λ` a finite commutative ring, `ψ` an additive character of `k` with
values in `Λ` and `Φ(K) = R pr₂!(pr₁⁻¹ K ⊗ μ⁻¹ L_ψ)` the Fourier transform on `D⁺(𝔸¹_k, Λ)`. Let
`i : Z ⟶ 𝔸¹_k` be a closed immersion with `Z` finite over `k`, `N` a sheaf of `Λ`-modules on `Z`,
`Z' = Z ×_{𝔸¹} 𝔸² = Z ×_k 𝔸¹_t` with `s : Z' ⟶ 𝔸²`, `q : Z' ⟶ Z`, and `π = pr₂ ∘ s : Z' ⟶ 𝔸¹_t`,
the base change of `Z ⟶ Spec k`. Then

`Φ(i_* N) ≅ (π_*(q⁻¹ N ⊗ s⁻¹ μ⁻¹ L_ψ))[0]`:

`i_* N = R i_! N` (`i` proper), base change along `pr₁` (Tag 0F7L), the projection formula for
`s`, the composition `R pr₂! ∘ R s_! = R π_!` (Tag 0F7J) and `R π_! = π_*` for the finite `π`.
When `Z ⟶ Spec k` is moreover étale and `N` is locally constant of finite type, `π` is finite
étale and `H⁰(Φ(i_* N))` is locally constant of finite type (Tag 095B).

This generalizes `Stacks.EtaleCohomology.nonempty_fourierTransform_affineLinePoint_iso` (a
rational point) to the closed subschemes carrying a punctual sheaf: it is the lisse half of the
step (L5) of the single-level argument for the irreducibility of the Fourier transform in
Laumon's proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.nonempty_fourierTransform_directImage_iso`.
* `Stacks.EtaleCohomology.isFiniteTypeLocallyConstant_homology_zero_fourierTransform_directImage`.

## Implementation notes

The Fourier transform lives in the standard model `HasDerivedCategory.standard`, and so do the
statements.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry
  Stacks.ArtinSchreier

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] Sheaf.monoidalCategory isMonoidal_W_etaleModules
  HasDerivedCategory.standard etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (k : Type u) [Field k] [Fintype k] (Λ : Type) [CommRing Λ] [Finite Λ] (ψ : AddChar k Λ)
  (B : BigEtaleSite.{u})
  (p₀ : (finiteEtaleFiberFunctor (affineLineOrigin k)).obj (cover k (Polynomial k) Polynomial.X))

local notation "𝔸f" => affineLineStructureMap k

omit [Fintype k] in
/-- **`Z ×_{𝔸¹} 𝔸² ⟶ 𝔸¹_t` is the base change of `Z ⟶ Spec k`**, for `i : Z ⟶ 𝔸¹_k`. -/
theorem isPullback_pullback_fst_affineLine {Z : Scheme.{u}}
    (i : Z ⟶ Spec (.of (Polynomial k))) :
    IsPullback (pullback.snd (pullback.fst 𝔸f 𝔸f) i)
      (pullback.fst (pullback.fst 𝔸f 𝔸f) i ≫ pullback.snd 𝔸f 𝔸f) (i ≫ 𝔸f) 𝔸f :=
  (IsPullback.of_hasPullback (pullback.fst 𝔸f 𝔸f) i).flip.paste_vert
    (IsPullback.of_hasPullback 𝔸f 𝔸f)

/-- **The Fourier transform of `i_* N`** for a closed immersion `i : Z ⟶ 𝔸¹_k` with `Z` finite
over `k`: `Φ(i_* N) ≅ (π_*(q⁻¹ N ⊗ s⁻¹ μ⁻¹ L_ψ))[0]`, `Z' = Z ×_{𝔸¹} 𝔸²`, `s : Z' ⟶ 𝔸²`,
`q : Z' ⟶ Z`, `π = pr₂ ∘ s`. -/
theorem nonempty_fourierTransform_directImage_iso (j : CompactificationOf (Over.mk 𝔸f))
    {Z : Scheme.{u}} (i : Z ⟶ Spec (.of (Polynomial k))) [IsClosedImmersion i]
    [IsFinite (i ≫ 𝔸f)] (N : EtaleModules.{u, 0} Λ Z) :
    Nonempty ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} Λ i).obj N)) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} Λ
            (pullback.fst (pullback.fst 𝔸f 𝔸f) i ≫ pullback.snd 𝔸f 𝔸f)).obj
          ((etaleModuleInverseImage.{u, 0} Λ (pullback.snd (pullback.fst 𝔸f 𝔸f) i)).obj N ⊗
            (etaleModuleInverseImage.{u, 0} Λ (pullback.fst (pullback.fst 𝔸f 𝔸f) i)).obj
              ((etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj
                (affineLineArtinSchreierSheaf k Λ ψ B p₀))))) := by
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let s := pullback.fst pr₁ i
  let q := pullback.snd pr₁ i
  let L := affineLineArtinSchreierSheaf k Λ ψ B p₀
  let 𝓛 := (etaleModuleInverseImage.{u, 0} Λ (affineLineMul k)).obj L
  have h𝓛 := isLocallyFreeEtaleModule_fourierKernel k Λ ψ B p₀
  have h𝓛e := isExactTensorRight_fourierKernel k Λ ψ B p₀
  have hs𝓛 : IsExactTensorRight Λ ((etaleModuleInverseImage.{u, 0} Λ s).obj 𝓛) :=
    isExactTensorRight_of_isLocallyFreeEtaleModule (isLocallyFreeEtaleModule_inverseImage Λ _ h𝓛)
  have : LocallyOfFiniteType 𝔸f := locallyOfFiniteType_specPolynomial k
  have : CompactSpace ↥(pullback 𝔸f 𝔸f) := QuasiCompact.compactSpace_of_compactSpace pr₂
  have : QuasiSeparatedSpace ↥(pullback 𝔸f 𝔸f) := quasiSeparatedSpace_of_quasiSeparated pr₂
  have : LocallyOfFiniteType pr₂ := MorphismProperty.of_isPullback (P := @LocallyOfFiniteType)
    (IsPullback.of_hasPullback 𝔸f 𝔸f) inferInstance
  have : IsSeparated pr₂ := MorphismProperty.of_isPullback (P := @IsSeparated)
    (IsPullback.of_hasPullback 𝔸f 𝔸f) inferInstance
  let sq := (IsPullback.of_hasPullback pr₁ i).flip
  have : IsClosedImmersion s := MorphismProperty.of_isPullback (P := @IsClosedImmersion) sq
    inferInstance
  have : IsFinite (s ≫ pr₂) := MorphismProperty.of_isPullback (P := @IsFinite)
    (isPullback_pullback_fst_affineLine k i) inferInstance
  have : IsProper (s ≫ pr₂) := inferInstance
  have : IsIntegralHom (s ≫ pr₂) := inferInstance
  let ji := CompactificationOf.ofProper i
  let js := ji.baseChange sq
  let jP := j.baseChange (IsPullback.of_hasPullback 𝔸f 𝔸f)
  let N0 := (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} Λ Z) 0).obj N
  let T𝓛 := etaleModuleDerivedTensorRight Λ 𝓛 h𝓛e
  let Ts := etaleModuleDerivedTensorRight Λ _ hs𝓛
  let A := (etaleModuleInverseImage.{u, 0} Λ q).obj N ⊗ (etaleModuleInverseImage.{u, 0} Λ s).obj 𝓛
  -- `i_* N = R i_! N`
  let ea : (DerivedCategory.Plus.singleFunctor _ 0).obj
      ((etaleModuleDirectImage.{u, 0} Λ i).obj N) ≅ (derivedLowerShriek.{u, 0} i ji Λ).obj N0 :=
    (Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (etaleModuleDirectImage.{u, 0} Λ i) 0).app N ≪≫
      ((derivedLowerShriekOfProperIso Λ i).app N0).symm
  -- base change along `pr₁` (Tag 0F7L)
  let eb := (isoOfIsTorsionPlusι (derivedLowerShriekBaseChangeIso Λ sq ji)).app N0
  -- the projection formula for `s`
  let ec := (isoOfIsTorsionPlusι ((derivedLowerShriekProjectionFormula Λ) s js 𝓛 h𝓛 h𝓛e
    hs𝓛).some).app ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ q).obj N0)
  -- the composition of lower shriek functors (Tag 0F7J)
  let ed := (isoOfIsTorsionPlusι (derivedLowerShriekCompIso Λ s pr₂ js jP
    (CompactificationOf.ofProper (s ≫ pr₂)))).app (Ts.obj
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ q).obj N0))
  have := hs𝓛.1
  have := hs𝓛.2.1
  have := hs𝓛.2.2
  let eT : Ts.obj ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ q).obj N0) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj A :=
    Ts.mapIso ((Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (etaleModuleInverseImage.{u, 0} Λ q) 0).app N) ≪≫
      (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
        (MonoidalCategory.tensorRight ((etaleModuleInverseImage.{u, 0} Λ s).obj 𝓛)) 0).app _
  -- `R π_! = R π_* = π_*`, `π` being finite
  let ee : (derivedLowerShriek.{u, 0} (s ≫ pr₂) (CompactificationOf.ofProper (s ≫ pr₂)) Λ).obj
      ((DerivedCategory.Plus.singleFunctor _ 0).obj A) ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((etaleModuleDirectImage.{u, 0} Λ (s ≫ pr₂)).obj A) :=
    (derivedLowerShriekOfProperIso Λ (s ≫ pr₂)).app _ ≪≫
      ((Stacks.DerivedFunctor.exactSingleFunctorRightDerivedPlusIso
        (etaleModuleDirectImage.{u, 0} Λ (s ≫ pr₂)) 0).app A).symm
  exact ⟨(derivedLowerShriek.{u, 0} pr₂ jP Λ).mapIso (T𝓛.mapIso
      ((etaleModuleDerivedInverseImagePlus.{u, 0} Λ pr₁).mapIso ea ≪≫ eb) ≪≫
      ec.symm) ≪≫ ed.symm ≪≫
    (derivedLowerShriek.{u, 0} (s ≫ pr₂) (CompactificationOf.ofProper (s ≫ pr₂)) Λ).mapIso eT ≪≫
    ee⟩

/-- **`H⁰(Φ(i_* N))` is locally constant of finite type** for a closed immersion
`i : Z ⟶ 𝔸¹_k` with `Z` finite étale over `k` and `N` locally constant of finite type on `Z`:
it is `π_*(q⁻¹ N ⊗ s⁻¹ μ⁻¹ L_ψ)` for the finite étale `π : Z ×_k 𝔸¹ ⟶ 𝔸¹` (Tag 095B). -/
theorem isFiniteTypeLocallyConstant_homology_zero_fourierTransform_directImage
    (j : CompactificationOf (Over.mk 𝔸f))
    {Z : Scheme.{u}} (i : Z ⟶ Spec (.of (Polynomial k))) [IsClosedImmersion i]
    [IsFinite (i ≫ 𝔸f)] [Etale (i ≫ 𝔸f)] (N : EtaleModules.{u, 0} Λ Z)
    (hN : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ Z.smallEtaleTopology N) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ
      (Spec (.of (Polynomial k))).smallEtaleTopology
      ((DerivedCategory.Plus.homologyFunctor _ 0).obj
        ((fourierTransform k Λ ψ B p₀ j).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((etaleModuleDirectImage.{u, 0} Λ i).obj N)))) := by
  let pr₁ := pullback.fst 𝔸f 𝔸f
  let pr₂ := pullback.snd 𝔸f 𝔸f
  let s := pullback.fst pr₁ i
  let q := pullback.snd pr₁ i
  have : IsFinite (s ≫ pr₂) := MorphismProperty.of_isPullback (P := @IsFinite)
    (isPullback_pullback_fst_affineLine k i) inferInstance
  have : Etale (s ≫ pr₂) := MorphismProperty.of_isPullback (P := @Etale)
    (isPullback_pullback_fst_affineLine k i) inferInstance
  obtain ⟨e⟩ := nonempty_fourierTransform_directImage_iso k Λ ψ B p₀ j i N
  have h𝓛 := isLocallyFreeEtaleModule_inverseImage Λ s
    (isLocallyFreeEtaleModule_fourierKernel k Λ ψ B p₀)
  have hA : Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant Λ _
      ((etaleModuleInverseImage.{u, 0} Λ q).obj N ⊗
        (etaleModuleInverseImage.{u, 0} Λ s).obj ((etaleModuleInverseImage.{u, 0} Λ
          (affineLineMul k)).obj (affineLineArtinSchreierSheaf k Λ ψ B p₀))) := fun U' => by
    obtain ⟨I', V, f, hcov, ht⟩ := isLocallyConstantWith_tensor Λ (fun E => ModuleCat.isFG Λ E)
      (fun E => Module.Free Λ E ∧ Module.Finite Λ E)
      (isLocallyConstantWith_inverseImage Λ (ModuleCat.isFG Λ) q hN) h𝓛 U'
    refine ⟨I', V, f, hcov, fun i' => ?_⟩
    obtain ⟨E, ⟨E₁, E₂, hE₁, hE₂, rfl⟩, e'⟩ := ht i'
    refine ⟨E₁ ⊗ E₂, (ModuleCat.isFG_iff _).2 ?_, e'⟩
    have := (ModuleCat.isFG_iff E₁).1 hE₁
    have := hE₂.2
    exact inferInstanceAs (Module.Finite Λ (TensorProduct Λ E₁ E₂))
  have hπ :=
    Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_finiteEtalePushforward_modules.{u, 0, 0}
      (s ≫ pr₂) Λ _ hA
  exact Stacks.ConstantSheaf.isFiniteTypeLocallyConstant_congr _ Λ
    ((DerivedCategory.Plus.homologyFunctor _ 0).mapIso e ≪≫
      Stacks.DerivedCategoryPlus.homologySingleFunctorIso 0 _).symm hπ

end Stacks.EtaleCohomology

end
