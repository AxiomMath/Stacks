module

public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.PartAInputs
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativeExt.OpenRestrictionSupported
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.QuasiCompactQuasiSeparated
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.ProjectionFormulaQCoh
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectPushforwardDerivedTensor
public import StacksFrontier.AlgebraicGeometry.Morphisms.Proper.ProperClosedSubsetCompact

/-!
# [Stacks, Tag 08IF] (A): relative `Ext` is approximated by a perfect complex on the base

Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism locally of finite type, `E` an object of
`D^-_{Coh}(𝒪_X)` and `𝒢` a bounded complex of coherent `𝒪_X`-modules, flat over `S`, with
support proper over `S`. For every `m` there is a perfect `K` in `D(𝒪_S)` and maps

`α^i_ℱ : Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ) ⟶ H^i(S, K ⊗^L_{𝒪_S} ℱ)`

for quasi-coherent `𝒪_S`-modules `ℱ`, functorial in `ℱ`, compatible with the boundary maps of
short exact sequences of quasi-coherent modules, and bijective for `i ≤ m`.

## Main results

* `Stacks.Cohomology.RelativeExt.exists_perfect_relativeExt_comparison`: [Stacks, Tag 08IF] (A),
  the existence of a perfect `K` and of the maps `α^i_ℱ`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.Cohomology.RelativeExt

variable {X S : Scheme.{u}} (f : X ⟶ S) [IsNoetherian S] [LocallyOfFiniteType f]

/-- Let `S` be a Noetherian scheme, `f : X ⟶ S` a morphism locally of finite type,
`E ∈ D^-_{Coh}(𝒪_X)` and `𝒢` a bounded complex of coherent `𝒪_X`-modules, flat over `S`, with
support proper over `S`. For every `m` there are a perfect object `K` of `D(𝒪_S)` and maps

`α^i_ℱ : Ext^i_{𝒪_X}(E, 𝒢 ⊗_{𝒪_X} f^*ℱ) ⟶ H^i(S, K ⊗^L_{𝒪_S} ℱ)`

for quasi-coherent `ℱ` (with `H^i(S, -) = Ext^i_{𝒪_S}(𝒪_S, -)`), which are additive, functorial in
`ℱ`, compatible with the boundary maps of short exact sequences `0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` of
quasi-coherent modules (on the left, the connecting morphism of
`0 ⟶ 𝒢 ⊗ f^*ℱ₁ ⟶ 𝒢 ⊗ f^*ℱ₂ ⟶ 𝒢 ⊗ f^*ℱ₃ ⟶ 0`, exact because `𝒢` is flat over `S`; on the right,
that of the distinguished triangle `K ⊗^L ℱ₁ ⟶ K ⊗^L ℱ₂ ⟶ K ⊗^L ℱ₃ ⟶`), and bijective for
`i ≤ m`. -/
@[stacks 08IF "(A)"]
theorem exists_perfect_relativeExt_comparison (E : DStd X) (hE : IsBoundedAboveCoherent E)
    (G : CochainComplex (TModules X.toRingedSpace) ℤ)
    (hG : Stacks.Cohomology.PerfectPushforward.FlatProperSupportComplex f G) (m : ℤ) :
    ∃ K : DStd S, IsPerfectObject K ∧
      ∃ α : ∀ (i : ℤ) (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)),
          F.IsQuasicoherent → (relativeExtGroup f G E F i →+ baseTensorGroup K F i),
        (∀ (i : ℤ) (F F' : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
            (hF : F.IsQuasicoherent) (hF' : F'.IsQuasicoherent) (v : F ⟶ F')
            (y : relativeExtGroup f G E F i),
          α i F' hF' (relativeExtMap f G E i v y) = baseTensorMap i K v (α i F hF y)) ∧
        (∀ (A : ShortComplex (SheafOfModules.{u} (structureSheafRing S.toRingedSpace)))
            (hA : A.ShortExact) (h₁ : A.X₁.IsQuasicoherent) (h₃ : A.X₃.IsQuasicoherent)
            (n m' : ℤ) (h : 1 + n = m') (y : relativeExtGroup f G E A.X₃ n),
          α m' A.X₁ h₁ (relativeExtBoundaryMap E
              (isBoundedFlatOver_of_flatProperSupportComplex hG) hA n m' h y) =
            baseTensorBoundaryMap K hA n m' h (α n A.X₃ h₃ y)) ∧
        (∀ (i : ℤ), i ≤ m → ∀ (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace))
            (hF : F.IsQuasicoherent), Function.Bijective (α i F hF)) := by
  obtain ⟨b, -, hb, -⟩ := hG.bounded
  obtain ⟨Z, hZp, hZs⟩ := hG.properSupport
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  obtain ⟨V, hZV, hVc⟩ := exists_isCompact_open_superset X Z (isCompact_of_isProperOver f Z hZp)
  have : CompactSpace V := isCompact_iff_compactSpace.mp hVc
  have : IsNoetherian (V : Scheme.{u}) := {}
  have hGU := flatProperSupportComplex_restrictComplex f V G hG Z hZp hZs hZV
  have hGZ : ∀ (q : ℤ) (x : X), x ∉ (Z : Set X) →
      IsZero (TopCat.Presheaf.stalk (X := X.carrier) (G.X q).val.presheaf x) := fun q =>
    isZero_stalk_of_supp_subset (G.X q) Z (hZs q)
  have hZj : (Z : Set X) ⊆ Set.range V.ι.base := by
    rwa [Scheme.Opens.range_ι]
  have hres : ∀ (F : SheafOfModules.{u} (structureSheafRing S.toRingedSpace)) (i : ℤ),
      Function.Bijective (restrictRelativeExt f V.ι G E F i) := fun F i =>
    restrictRelativeExt_bijective_of f V.ι E F i
      (bijective_derivedPullback_map_of_supportedOn V.ι Z Z.isClosed hZj E _
        (cohomologySupportedOn_relativeExtTarget_shift (f := f) (G := G) (Z : Set X) hGZ F i))
  obtain ⟨r, hr⟩ := AlgebraicGeometry.PerfectApproximation.hasApproximationByPerfectComplexes
    (V : Scheme.{u}) Set.univ isClosed_univ (by simp)
  obtain ⟨P₀, hP, -, p, hp, he⟩ := hr ((restrictDerived V.ι).obj E) (b - m - 1)
    (isPseudoCoherent_restrictDerived V E hE).2
    (isPseudoCoherentFrom_restrictDerived V E hE _)
    (fun _ x _ hx => absurd (Set.mem_univ x) hx)
  let P : DStd (V : Scheme.{u}) := P₀
  have hPF : ∀ N, qcohDerived S N →
      IsIso (Stacks.Cohomology.DerivedProjectionFormula.projectionFormulaMap
        (V.ι ≫ f).toLRSHom.toShHom
          (stageSource (X := (V : Scheme.{u}).toRingedSpace) (G := restrictComplex V.ι G) P) N) :=
    fun N hN => Stacks.Cohomology.ProjectionFormulaQCoh.isIso_projectionFormulaMap_of_isDQCoh
      (V.ι ≫ f) _ N (isDQCoh_stageSource (V.ι ≫ f) P hP _ hGU) hN
  refine ⟨stageK (V.ι ≫ f).toLRSHom.toShHom (G := restrictComplex V.ι G) P, ?_,
    exists_comparison_of_open f V.ι (isBoundedFlatOver_of_flatProperSupportComplex hG) E P
      (isPerfect_ringedSite_of_isPerfectObject P hP) hPF p b m hb hp he hres⟩
  rw [stageK_eq]
  exact Stacks.Cohomology.PerfectPushforward.isPerfect_derivedPushforward_derivedTensor_of_isPerfect
    (V.ι ≫ f) _ _ _ (isPerfectObject_derivedDual P hP) hGU

end Stacks.Cohomology.RelativeExt

end
