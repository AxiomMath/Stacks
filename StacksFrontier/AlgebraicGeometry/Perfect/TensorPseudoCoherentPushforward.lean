module

public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfect
import StacksFrontier.AlgebraicGeometry.BaseChange.FlatOverBase.TensorFlat
import StacksFrontier.AlgebraicGeometry.ConfinedDevissage.Basic
import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.BoundedBelowComparison
import StacksFrontier.AlgebraicGeometry.DerivedAcyclic.Pushforward
import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.AlgebraicFlatness
import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FlatLocus
import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
import StacksFrontier.AlgebraicGeometry.Morphisms.FlatMorphisms.BaseChange
import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.Affine
import StacksFrontier.AlgebraicGeometry.Perfect.PerfectApproximation.QuasiCompactQuasiSeparated
import StacksFrontier.AlgebraicGeometry.Perfect.PseudoCoherentFrom.Affine
import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectOpenLocality
import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfectPushforward
import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedPushforwardRelative
import StacksFrontier.AlgebraicGeometry.PseudoCoherent.DerivedTensorProjection
import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TransportAlongIso
import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.QcqsPushforwardBounds
import StacksFrontier.Homology.DerivedCategory.PerfectApproximation
import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.BoundedVanishing
import StacksCore.Tactic.StacksAttribute

/-!
# Stacks 0CSC

Let `f : X ⟶ S` be a morphism of finite presentation, `E ∈ D(𝒪_X)` pseudo-coherent and `𝒢^•` a
bounded above complex of finitely presented `𝒪_X`-modules, flat over `S`, with support proper
over `S`. Then `K = Rf_*(E ⊗^L_{𝒪_X} 𝒢^•)` is a pseudo-coherent object of `D(𝒪_S)` and its
formation commutes with arbitrary base change.

## Main results

* `AlgebraicGeometry.isPseudoCoherent_of_forall_isAffineOpen`: pseudo-coherence is local on the
  base.
* `AlgebraicGeometry.isPseudoCoherent_derivedPushforward_tensor`: the pseudo-coherence half of
  [Stacks, Tag 0CSC].
* `AlgebraicGeometry.isPseudoCoherent_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap`:
  [Stacks, Tag 0CSC].

## References

* [Stacks Project, Tag 0CSC](https://stacks.math.columbia.edu/tag/0CSC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback derivedPushforward)
open Stacks.Cohomology.DerivedPullbackTensor (pullbackComplex)
open Stacks.DerivedTensor.RingedSite (derivedTensorProductFunctor canonicalDerivedTensorProduct)

universe u

namespace AlgebraicGeometry

attribute [local instance 10000] HasDerivedCategory.standard

/-! ### Locality on the base -/

/-- **Pseudo-coherence is local on the base.** An object of `D(𝒪_S)` whose derived pullback to
every affine open of `S` is pseudo-coherent is pseudo-coherent. -/
theorem isPseudoCoherent_of_forall_isAffineOpen {S : Scheme.{u}} (K : DerivedCategory S.Modules)
    (h : ∀ W : S.Opens, IsAffineOpen W →
      RingedSpace.IsPseudoCoherent (X := W.toScheme.toRingedSpace)
        ((derivedPullback W.ι.toLRSHom.toShHom).obj K)) :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace) K :=
  have : ∀ W : S.affineOpens, SheafedSpace.IsOpenImmersion W.1.ι.toLRSHom.toShHom := fun W =>
    (inferInstance : IsOpenImmersion W.1.ι)
  RingedSpace.isPseudoCoherent_of_openImmersion_cover
    (fun W : S.affineOpens => W.1.toScheme.toRingedSpace) (fun W => W.1.ι.toLRSHom.toShHom)
    (fun y => by
      obtain ⟨W₀, hW, hyW, -⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.mp S.isBasis_affineOpens)
        (show y ∈ (⊤ : S.Opens) from trivial)
      let W : S.Opens := W₀
      exact ⟨⟨W, hW⟩, by
        change y ∈ Set.range (W.ι : W.toScheme → S)
        rwa [Scheme.Opens.range_ι]⟩)
    K fun W => h W.1 W.2

/-! ### The affine case -/

section Affine

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **[Stacks, Tag 08D5] for a derived tensor product.** For `f` quasi-compact and
quasi-separated with `S` quasi-compact there is an `N` such that `Rf_*(K ⊗^L L)` lies in degrees
`≤ a + b + N` whenever `K` and `L` have quasi-coherent cohomology and lie in degrees `≤ a`,
resp. `≤ b`. -/
private theorem exists_isLE_derivedPushforward_tensor [QuasiCompact f] [QuasiSeparated f]
    [CompactSpace S] :
    ∃ N : ℤ, ∀ (K L : DerivedCategory X.Modules) (a b : ℤ),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj K).IsQuasicoherent) →
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj L).IsQuasicoherent) →
      K.IsLE a → L.IsLE b →
      ((derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj K).obj L)).IsLE (a + b + N) := by
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_obj f
  exact ⟨N, fun K L a b hK hL ha hb => hN _
    (TorFormula.isQuasicoherent_homology_derivedTensor X K L hK hL) (a + b)
    (Scheme.Modules.isLE_derivedTensorProduct X K L a b ha hb)⟩

/-- The terms of a complex of finitely presented modules are quasi-coherent. -/
private theorem isQuasicoherent_X_of_isFinitePresentation {X : Scheme.{u}}
    {G : CochainComplex X.Modules ℤ} (hfp : ∀ i : ℤ, (G.X i).IsFinitePresentation) (i : ℤ) :
    (G.X i).IsQuasicoherent :=
  have := hfp i
  isQuasicoherent_of_isFinitePresentation (G.X i)

/-- **The terms of a brutal truncation `σ^{≥k}𝒢^•`**: the term in degree `i ≥ k` is that of
`𝒢^•`, the others vanish. -/
private theorem stupidTruncGE_X {X : Scheme.{u}} (G : CochainComplex X.Modules ℤ) (k i : ℤ) :
    (k ≤ i ∧ Nonempty ((G.stupidTrunc (ComplexShape.embeddingUpIntGE k)).X i ≅ G.X i)) ∨
      (i < k ∧ IsZero ((G.stupidTrunc (ComplexShape.embeddingUpIntGE k)).X i)) := by
  by_cases h : k ≤ i
  · exact Or.inl ⟨h, ⟨G.stupidTruncXIso (ComplexShape.embeddingUpIntGE k) (i := (i - k).toNat)
      (by change k + ((i - k).toNat : ℤ) = i; omega)⟩⟩
  · exact Or.inr ⟨by omega, G.isZero_stupidTrunc_X (ComplexShape.embeddingUpIntGE k) i
      (by rw [ComplexShape.notMem_range_embeddingUpIntGE_iff]; omega)⟩

/-- **A brutal truncation `σ^{≥k}𝒢^•` of a bounded above complex as in [Stacks, Tag 0CSC]
satisfies the hypothesis of [Stacks, Tag 0A1H].** -/
private theorem flatProperSupportFinitelyPresented_stupidTruncGE [LocallyOfFinitePresentation f]
    (G : CochainComplex X.Modules ℤ) (b : ℤ) (hb : G.IsStrictlyLE b)
    (hfp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hflat : ∀ i : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X i))
    (Z : Closeds X) (hZ : IsProperOver f Z)
    (hsupp : ∀ i : ℤ, SheafOfModules.supp (G.X i) ⊆ (Z : Set X)) (k : ℤ) :
    FlatProperSupportFinitelyPresented f (G.stupidTrunc (ComplexShape.embeddingUpIntGE k)) where
  bounded := ⟨k, b, (CochainComplex.isStrictlyGE_iff _ _).2 fun i hi => by
      rcases stupidTruncGE_X G k i with ⟨h, -⟩ | ⟨-, hz⟩
      · omega
      · exact hz,
    (CochainComplex.isStrictlyLE_iff _ _).2 fun i hi => by
      rcases stupidTruncGE_X G k i with ⟨-, ⟨e⟩⟩ | ⟨-, hz⟩
      · exact (G.isZero_of_isStrictlyLE b i hi).of_iso e
      · exact hz⟩
  isFinitePresentation i := by
    rcases stupidTruncGE_X G k i with ⟨-, ⟨e⟩⟩ | ⟨-, hz⟩
    · exact (SheafOfModules.isFinitePresentation X.ringCatSheaf).prop_of_iso e.symm (hfp i)
    · exact isFinitePresentation_of_isZero _ hz
  isFlatOver i := by
    rcases stupidTruncGE_X G k i with ⟨-, ⟨e⟩⟩ | ⟨-, hz⟩
    · exact (isFlatOver_iff_of_moduleIso f.toLRSHom.toShHom e).2 (hflat i)
    · exact isFlatOver_of_isZero f _ hz
  properSupport := ⟨Z, hZ, fun i => by
    rcases stupidTruncGE_X G k i with ⟨-, ⟨e⟩⟩ | ⟨-, hz⟩
    · rw [SheafOfModules.supp_eq_of_iso e]
      exact hsupp i
    · rw [Stacks.AlgebraicGeometry.ConfinedDevissage.supp_eq_empty_of_isZero _ hz]
      exact Set.empty_subset _⟩

section Triangulated

attribute [local implicit_reducible] CategoryTheory.sheafCompose structureSheafRing
  Stacks.SheafOfModules.Tensor.ringSheaf TopCat.Presheaf.IsSheaf TopCat.Sheaf
attribute [local instance_reducible] AlgebraicGeometry.SheafedSpace.sheaf

/-- **The perfect case of the affine case of [Stacks, Tag 0CSC].** If `S` is affine and `P` is
perfect, `Rf_*(P ⊗^L 𝒢^•)` is `m`-pseudo-coherent for every `m`: for `n` small enough the map
`Rf_*(P ⊗^L σ^{≥n+1}𝒢^•) ⟶ Rf_*(P ⊗^L 𝒢^•)` has a cone `Rf_*(P ⊗^L σ^{≤n}𝒢^•)` in degrees
`< m` by [Stacks, Tag 08D5], and its source is perfect by [Stacks, Tag 0A1H]. -/
private theorem isPseudoCoherentFrom_derivedPushforward_tensor_of_isPerfect [IsAffine S]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (P : DerivedCategory X.Modules) (hP : RingedSpace.IsPerfect (X := X.toRingedSpace) P)
    (G : CochainComplex X.Modules ℤ) (b : ℤ) (hb : G.IsStrictlyLE b)
    (hfp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hflat : ∀ i : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X i))
    (Z : Closeds X) (hZ : IsProperOver f Z)
    (hsupp : ∀ i : ℤ, SheafOfModules.supp (G.X i) ⊆ (Z : Set X)) (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj P).obj (DerivedCategory.Q.obj G))) m := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_tensor f
  obtain ⟨a, ha⟩ := RingedSpace.exists_isZero_homology_of_isPseudoCoherentFrom
    (X := X.toRingedSpace) P 0
    ((RingedSpace.isPseudoCoherent_iff_forall (X := X.toRingedSpace) P).1
      (RingedSpace.IsPerfect.isPseudoCoherent (X := X.toRingedSpace) hP) 0)
  have hPa : P.IsLE (a - 1) := by
    rw [DerivedCategory.isLE_iff]
    exact fun i hi => ha i (by omega)
  let F := (derivedTensorProductFunctor X.sheaf).obj P ⋙ derivedPushforward f.toLRSHom.toShHom
  let _ := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    f.toLRSHom.toShHom
  have _ := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated
    f.toLRSHom.toShHom
  let _ : ((derivedTensorProductFunctor X.sheaf).obj P).CommShift ℤ :=
    (canonicalDerivedTensorProduct X.sheaf).commShift_right _
  have _ : ((derivedTensorProductFunctor X.sheaf).obj P).IsTriangulated :=
    (canonicalDerivedTensorProduct X.sheaf).exact_right _
  let _ : F.CommShift ℤ := Functor.CommShift.comp _ _
  let n := m - a - N
  let T := (DerivedCategory.Qh ⋙ F).mapTriangle.obj (Stacks.DerivedAcyclic.stupidTruncTriangleh G n)
  have h₁ : RingedSpace.IsPseudoCoherentFrom (X := S.toRingedSpace) T.obj₁ m :=
    RingedSpace.IsPseudoCoherentFrom.ofIso (X := S.toRingedSpace)
      ((RingedSpace.isPseudoCoherent_iff_forall (X := S.toRingedSpace) _).1
        (RingedSpace.IsPerfect.isPseudoCoherent (X := S.toRingedSpace)
        (isPerfect_derivedPushforward_tensor_of_isAffine f P hP _
          (flatProperSupportFinitelyPresented_stupidTruncGE f G b hb hfp hflat Z hZ hsupp
            (n + 1)))) m)
      (F.mapIso ((DerivedCategory.quotientCompQhIso X.Modules).symm.app _))
  have h₃ : RingedSpace.IsPseudoCoherentFrom (X := S.toRingedSpace) T.obj₃ m := by
    have h := hN P (DerivedCategory.Q.obj (G.stupidTrunc (ComplexShape.embeddingUpIntLE n)))
      (a - 1) n (PerfectApproximation.isQuasicoherent_homology_of_isPerfect X P hP)
      (isQuasicoherent_derived_homology _
        (isQuasicoherent_stupidTruncLE G (isQuasicoherent_X_of_isFinitePresentation hfp) n)) hPa
      (Stacks.DerivedAcyclic.isLE_stupidTruncLE G n)
    rw [show a - 1 + n + N = m - 1 by omega] at h
    have hz : ∀ i : ℤ, m - 1 < i → IsZero ((DerivedCategory.homologyFunctor _ i).obj T.obj₃) :=
      fun i hi => (((DerivedCategory.isLE_iff _ _).1 h) i hi).of_iso
        ((DerivedCategory.homologyFunctor _ i).mapIso
          (F.mapIso ((DerivedCategory.quotientCompQhIso X.Modules).app _)))
    exact @RingedSpace.isPseudoCoherentFrom_of_isLE S.toRingedSpace _ T.obj₃ m
      ((DerivedCategory.isLE_iff _ _).2 hz)
  exact RingedSpace.IsPseudoCoherentFrom.ofIso (X := S.toRingedSpace)
    (RingedSpace.isPseudoCoherentFrom_obj₂_of_distinguished (X := S.toRingedSpace) m T
      ((DerivedCategory.Qh ⋙ F).map_distinguished _
        (Stacks.DerivedAcyclic.stupidTruncTriangleh_distinguished G n)) h₁ h₃)
    (F.mapIso ((DerivedCategory.quotientCompQhIso X.Modules).app G))

/-- **The affine case of the pseudo-coherence half of [Stacks, Tag 0CSC].** If `S` is affine,
`Rf_*(E ⊗^L 𝒢^•)` is `m`-pseudo-coherent for every `m`: by [Stacks, Tag 08ES] there is a perfect
`P ⟶ E` whose cone lies in degrees `< m - b - N`, with `𝒢^i = 0` for `i > b` and `N` the bound of
[Stacks, Tag 08D5], so `Rf_*(P ⊗^L 𝒢^•) ⟶ Rf_*(E ⊗^L 𝒢^•)` has a cone in degrees `< m`; and
`Rf_*(P ⊗^L 𝒢^•)` is `m`-pseudo-coherent by the perfect case. -/
private theorem isPseudoCoherentFrom_derivedPushforward_tensor_of_isAffine [IsAffine S]
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (E : DerivedCategory X.Modules) (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (G : CochainComplex X.Modules ℤ) (b : ℤ) (hb : G.IsStrictlyLE b)
    (hfp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hflat : ∀ i : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X i))
    (Z : Closeds X) (hZ : IsProperOver f Z)
    (hsupp : ∀ i : ℤ, SheafOfModules.supp (G.X i) ⊆ (Z : Set X)) (m : ℤ) :
    RingedSpace.IsPseudoCoherentFrom (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) m := by
  have : CompactSpace X := QuasiCompact.compactSpace_of_compactSpace f
  have : QuasiSeparatedSpace X := quasiSeparatedSpace_of_quasiSeparated f
  obtain ⟨N, hN⟩ := exists_isLE_derivedPushforward_tensor f
  have hEq : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj E).IsQuasicoherent :=
    isQuasicoherentDerived_of_isPseudoCoherent X E hE
  obtain ⟨r, hr⟩ := PerfectApproximation.hasApproximationByPerfectComplexes X Set.univ
    isClosed_univ (by simp)
  obtain ⟨P, hP, -, α, hα⟩ := hr E (m - b - N) hEq
    ((RingedSpace.isPseudoCoherent_iff_forall (X := X.toRingedSpace) E).1 hE _)
    (fun i x _ hx => (hx (Set.mem_univ x)).elim)
  obtain ⟨C, β, γ, hT⟩ := distinguished_cocone_triangle α
  have hC := (DerivedCategory.approximatesFrom_iff_isZero_homology_obj₃ (Triangle.mk α β γ) hT
    (m - b - N)).1 hα
  have hCq : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj C).IsQuasicoherent := by
    have : (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsClosedUnderIsomorphisms :=
      (DerivedCategoryB.derivedCategoryB_isTriangulated_saturated _
        (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)).1
    have : (DerivedCategoryB.derivedCategoryB (A := X.Modules)
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).IsTriangulated :=
      DerivedCategoryB.derivedCategoryB_isTriangulated _
        (Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.isQuasicoherent_isWeakSerre X)
    exact (DerivedCategoryB.derivedCategoryB (A := X.Modules)
      (SheafOfModules.isQuasicoherent X.ringCatSheaf)).ext_of_isTriangulatedClosed₃ _ hT
      (PerfectApproximation.isQuasicoherent_homology_of_isPerfect X P hP) hEq
  have hCle : C.IsLE (m - b - N - 1) :=
    (DerivedCategory.isLE_iff _ _).2 fun i hi => hC i (by omega)
  let F := (derivedTensorProductFunctor X.sheaf).flip.obj (DerivedCategory.Q.obj G) ⋙
    derivedPushforward f.toLRSHom.toShHom
  let _ := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforwardCommShift
    f.toLRSHom.toShHom
  have _ := Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPushforward_isTriangulated
    f.toLRSHom.toShHom
  let _ : ((derivedTensorProductFunctor X.sheaf).flip.obj (DerivedCategory.Q.obj G)).CommShift ℤ :=
    (canonicalDerivedTensorProduct X.sheaf).commShift_left _
  have _ : ((derivedTensorProductFunctor X.sheaf).flip.obj
      (DerivedCategory.Q.obj G)).IsTriangulated :=
    (canonicalDerivedTensorProduct X.sheaf).exact_left _
  let _ : F.CommShift ℤ := Functor.CommShift.comp _ _
  let T := F.mapTriangle.obj (Triangle.mk α β γ)
  have h₁ : RingedSpace.IsPseudoCoherentFrom (X := S.toRingedSpace) T.obj₁ m :=
    isPseudoCoherentFrom_derivedPushforward_tensor_of_isPerfect f P hP G b hb hfp hflat Z hZ
      hsupp m
  have h₃ : RingedSpace.IsPseudoCoherentFrom (X := S.toRingedSpace) T.obj₃ m := by
    have h := hN C (DerivedCategory.Q.obj G) (m - b - N - 1) b hCq
      (isQuasicoherent_derived_homology G (isQuasicoherent_X_of_isFinitePresentation hfp)) hCle
      inferInstance
    rw [show m - b - N - 1 + b + N = m - 1 by omega] at h
    exact @RingedSpace.isPseudoCoherentFrom_of_isLE S.toRingedSpace _ T.obj₃ m h
  exact RingedSpace.isPseudoCoherentFrom_obj₂_of_distinguished (X := S.toRingedSpace) m T
    (F.map_distinguished _ hT) h₁ h₃

end Triangulated

end Affine

/-! ### Stacks 0CSC -/

section BaseChange

attribute [local implicit_reducible] StacksDraft.KFlat.modulePullback
attribute [local instance_reducible] CategoryTheory.sheafCompose
  AlgebraicGeometry.SheafedSpace.sheaf

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- **The pseudo-coherence half of [Stacks, Tag 0CSC].** Let `f : X ⟶ S` be a morphism of
schemes of finite presentation, let `E` be a pseudo-coherent object of `D(𝒪_X)` and let `𝒢^•` be a
bounded above complex of finitely presented `𝒪_X`-modules, flat over `S`, with support proper over
`S`. Then `Rf_*(E ⊗^L_{𝒪_X} 𝒢^•)` is a pseudo-coherent object of `D(𝒪_S)`.

The question is local on `S` (`AlgebraicGeometry.isPseudoCoherent_of_forall_isAffineOpen`), and
over an affine open `W` of `S` the restriction is computed on `f⁻¹W` by [Stacks, Tag 0A1D]. -/
theorem isPseudoCoherent_derivedPushforward_tensor (hf : FinitePresentation f)
    (E : DerivedCategory X.Modules) (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (G : CochainComplex X.Modules ℤ) (hGminus : CochainComplex.minus X.Modules G)
    (hfp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hflat : ∀ i : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X i))
    (hsupp : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      ∃ Z : Closeds X, IsProperOver f Z ∧ ∀ i : ℤ, SheafOfModules.supp (G.X i) ⊆ (Z : Set X)) :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
      ((derivedPushforward f.toLRSHom.toShHom).obj
        (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) := by
  have : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
  obtain ⟨b, hb⟩ := hGminus
  obtain ⟨Z, hZ, hsub⟩ := hsupp
  have hGq := isQuasicoherent_X_of_isFinitePresentation hfp
  refine isPseudoCoherent_of_forall_isAffineOpen _ fun W hW => ?_
  have : IsAffine W.toScheme := hW
  have sq := (isPullback_morphismRestrict f W).flip
  have : LocallyOfFinitePresentation (f ∣_ W) := MorphismProperty.of_isPullback sq inferInstance
  have : QuasiCompact (f ∣_ W) := MorphismProperty.of_isPullback sq hf.quasiCompact
  have : QuasiSeparated (f ∣_ W) := MorphismProperty.of_isPullback sq hf.quasiSeparated
  have := isIso_tensorFlatBaseChangeMap_of_isPullback f W.ι (f ∣_ W) (f ⁻¹ᵁ W).ι sq
    hf.quasiCompact hf.quasiSeparated (comp_toShHom_of_comm sq.w) E
    (isQuasicoherentDerived_of_isPseudoCoherent X E hE) G ⟨b, hb⟩ hGq hflat
  refine RingedSpace.IsPseudoCoherent.of_iso (X := W.toScheme.toRingedSpace) ?_
    (asIso (tensorFlatBaseChangeMap f W.ι (f ∣_ W) (f ⁻¹ᵁ W).ι (comp_toShHom_of_comm sq.w) E
      G)).symm
  refine (RingedSpace.isPseudoCoherent_iff_forall (X := W.toScheme.toRingedSpace) _).2
    fun m => ?_
  refine isPseudoCoherentFrom_derivedPushforward_tensor_of_isAffine (f ∣_ W) _
    (Scheme.Hom.isPseudoCoherent_derivedPullback (f ⁻¹ᵁ W).ι E hE) _ b
    ((CochainComplex.isStrictlyLE_iff _ b).2 fun i hi =>
      Functor.map_isZero (Scheme.Modules.pullback (f ⁻¹ᵁ W).ι) (G.isZero_of_isStrictlyLE b i hi))
    (fun i => @Stacks.SheafOfModules.modulePullback_isFinitePresentation _ _
      (f ⁻¹ᵁ W).ι.toLRSHom.toShHom (G.X i) (hfp i))
    (fun i => @modulePullback_isFlatOver _ _ _ _ _ _ _ _ sq (G.X i) (hGq i) (hflat i))
    (Z.preimage (f ⁻¹ᵁ W).ι.continuous)
    (isProperOver_preimage_baseChange (f ⁻¹ᵁ W).ι (f ∣_ W) f W.ι sq Z hZ) (fun i => ?_) m
  change SheafOfModules.supp ((Scheme.Modules.pullback (f ⁻¹ᵁ W).ι).obj (G.X i)) ⊆ _
  rw [@supp_pullback_of_isFinitePresentation _ _ (f ⁻¹ᵁ W).ι (G.X i) (hfp i)]
  exact fun x hx => hsub i hx

/-- **[Stacks, Tag 0CSC].** Let `f : X ⟶ S` be a morphism of schemes of finite presentation, let
`E` be a pseudo-coherent object of `D(𝒪_X)` and let `𝒢^•` be a bounded above complex of finitely
presented `𝒪_X`-modules, flat over `S`, with support proper over `S`. Then
`K = Rf_*(E ⊗^L_{𝒪_X} 𝒢^•)` is a pseudo-coherent object of `D(𝒪_S)`, and its formation commutes
with arbitrary base change: for every cartesian square the canonical map
`Lg^*Rf_*(E ⊗^L 𝒢^•) ⟶ Rf'_*(L(g')^*E ⊗^L (g')^*𝒢^•)` of
`AlgebraicGeometry.tensorFlatBaseChangeMap` is an isomorphism.

Support proper over `S` means that a single closed subset of `X` proper over `S` contains the
support of every term of `𝒢^•`. -/
@[stacks 0CSC]
theorem isPseudoCoherent_derivedPushforward_tensor_and_isIso_tensorFlatBaseChangeMap
    (hf : FinitePresentation f)
    (E : DerivedCategory X.Modules) (hE : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) E)
    (G : CochainComplex X.Modules ℤ) (hGminus : CochainComplex.minus X.Modules G)
    (hfp : ∀ i : ℤ, (G.X i).IsFinitePresentation)
    (hflat : ∀ i : ℤ, IsFlatOver f.toLRSHom.toShHom (G.X i))
    (hsupp : letI : LocallyOfFinitePresentation f := hf.locallyOfFinitePresentation
      ∃ Z : Closeds X, IsProperOver f Z ∧ ∀ i : ℤ, SheafOfModules.supp (G.X i) ⊆ (Z : Set X)) :
    RingedSpace.IsPseudoCoherent (X := S.toRingedSpace)
        ((derivedPushforward f.toLRSHom.toShHom).obj
          (((derivedTensorProductFunctor X.sheaf).obj E).obj (DerivedCategory.Q.obj G))) ∧
      ∀ {X' S' : Scheme.{u}} (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
        (hsq : IsPullback g' f' f g),
        IsIso (tensorFlatBaseChangeMap f g f' g' (comp_toShHom_of_comm hsq.w) E G) :=
  ⟨isPseudoCoherent_derivedPushforward_tensor f hf E hE G hGminus hfp hflat hsupp,
    fun g f' g' hsq => isIso_tensorFlatBaseChangeMap_of_isPullback f g f' g' hsq hf.quasiCompact
      hf.quasiSeparated _ E (isQuasicoherentDerived_of_isPseudoCoherent X E hE) G hGminus
      (isQuasicoherent_X_of_isFinitePresentation hfp) hflat⟩

end BaseChange

end AlgebraicGeometry

end
