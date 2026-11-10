module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.NormalizedDualizingDegree
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.CompletionVanishingDescends
public import StacksFrontier.AlgebraicGeometry.Duality.CohenMacaulayDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleStalk
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexModelIndependence
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulayCharacterization
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.ModificationCurve
public import StacksFrontier.RingTheory.Dualizing.ConcentratedDualizingModule

/-!
# The dualizing module `ω_X` normalized relative to `ω_A`, from `f^!(ω_A)` being dualizing

In Situation [Stacks, Tag 0B4W] let `ω_A` be a dualizing module of `A` and let
`K = f^!(ω_A)` be the twisted inverse image of [Stacks, Tag 0A9E] applied to `ω_A` in degree
zero. [Stacks, Remark 0B4R] says that once `K` is a dualizing complex on `X`, it is a coherent
module `ω_X` placed in degree zero; that module is the dualizing module of `X` normalized
relative to `ω_A`. This file proves that implication and constructs `ω_X` together with its
normalization datum `AlgebraicGeometry.RationalSingularitySituation.DualizingNormalization`.

## Main definitions

* `AlgebraicGeometry.RationalSingularitySituation.normalizedDualizingSheaf` — `H⁰(f^!(ω_A))`.
* `AlgebraicGeometry.RationalSingularitySituation.dualizingNormalizationOfIsDualizingComplex` —
  the normalization datum for `H⁰(f^!(ω_A))`, given that `f^!(ω_A)` is a dualizing complex.

## Main results

* `Stacks.Duality.nontrivial_of_isDualizingComplex_single` — a module over a Noetherian local
  ring which, placed in some degree, is a dualizing complex, is nonzero.
* `AlgebraicGeometry.RationalSingularitySituation.isCohenMacaulay_X` — `X` is Cohen–Macaulay
  ([Stacks, Tag 0B3D]: `X` is normal of dimension `2`).
* `AlgebraicGeometry.RationalSingularitySituation.zero_le_of_iso_singleFunctor` — if the
  dualizing complex `f^!(ω_A)` is a module placed in degree `n`, then `n ≥ 0`.
* `AlgebraicGeometry.RationalSingularitySituation.isZero_homology_relativeDualizingComplex` —
  a dualizing `f^!(ω_A)` has no cohomology outside degree zero.

## The proof of `n ≥ 0`

Suppose `f^!(ω_A) ≅ M[-n]` with `n < 0`. Duality gives
`Hom(𝒪_X[-n], f^!(ω_A)) = Hom(Rf_*(𝒪_X)[-n], ω_A[0])`, and `Rf_*𝒪_X = A` sits in degree zero
because `A` defines a rational singularity, so the right side vanishes by the t-structure. The
left side is `Hom(𝒪_X, M) = Γ(X, M)`, so `Γ(X, M) = 0`. As `f_*M` is quasi-coherent on the affine
`Spec(A)`, it vanishes, and since `f` is an isomorphism over the punctured spectrum `U`
(the special fibre being the only place where `f` is not an isomorphism), every section of `M`
over an open of `f⁻¹(U)` vanishes. The generic point of `X` lies over `U`, so the stalk of `M`
there is zero. But it is a dualizing module over the local ring of `X` at its generic point,
hence nonzero.

The degree bound `n ≤ 0` is `le_zero_of_iso_singleFunctor`; that `K` is a module in a single
degree at all is [Stacks, Tag 0AWT], `X` being connected and Cohen–Macaulay.

## References

* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0B4W](https://stacks.math.columbia.edu/tag/0B4W)
* [Stacks Project, Tag 0AWT](https://stacks.math.columbia.edu/tag/0AWT)
* [Stacks Project, Tag 0B3D](https://stacks.math.columbia.edu/tag/0B3D)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open Stacks.Duality (isQuasicoherent_homology_derivedPushforward_of_qcqs)
open CategoryTheory CategoryTheory.Limits
open Stacks.Duality (singleQuasiCoherent)
open Stacks.Cohomology.AffineBase (moduleGlobalSections)

universe u

namespace Stacks.Duality

/-- **A dualizing module over a Noetherian local ring is nonzero.** If `M[-n]` is a dualizing
complex then its only possibly nonzero cohomology module is `M`, and a dualizing complex over a
local ring has a nonzero cohomology module. -/
theorem nontrivial_of_isDualizingComplex_single {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] (M : ModuleCat.{u} A) (n : ℤ)
    (h : letI := HasDerivedCategory.standard (ModuleCat.{u} A)
      Dualizing.IsDualizingComplex ((DerivedCategory.singleFunctor (ModuleCat.{u} A) n).obj M)) :
    Nontrivial M := by
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  obtain ⟨i, hi⟩ := Dualizing.exists_not_isZero_homology _ h
  obtain rfl | hin := eq_or_ne i n
  · rw [← not_subsingleton_iff_nontrivial]
    intro hs
    exact hi (IsZero.of_iso (ModuleCat.isZero_of_subsingleton M)
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A) i).app M))
  · exact absurd (Dualizing.isZero_homology_of_iso_single.{u, u} _ n M ⟨Iso.refl _⟩ i hin) hi

/-- A dualizing module over a Noetherian local ring is nonzero. -/
theorem IsDualizingRingModule.nontrivial {A : Type u} [CommRing A] [IsNoetherianRing A]
    [IsLocalRing A] {M : ModuleCat.{u} A} (h : IsDualizingRingModule A M) : Nontrivial M := by
  obtain ⟨-, n, hn⟩ := h
  exact nontrivial_of_isDualizingComplex_single (ModuleCat.of A M) n hn

end Stacks.Duality

namespace AlgebraicGeometry.RationalSingularitySituation

variable (S : RationalSingularitySituation.{u})

/-- The source of the modification is integral. -/
instance isIntegral_X : IsIntegral S.X :=
  S.modification.source_isIntegral

/-- The source of the modification is locally Noetherian: it is of finite type over the
Noetherian ring `A`. -/
instance isLocallyNoetherian_X : IsLocallyNoetherian S.X := by
  have : IsProper S.f := S.modification.isProper
  exact LocallyOfFiniteType.isLocallyNoetherian S.f

/-- `X` has dimension two: a modification preserves dimension. -/
theorem topologicalKrullDim_X : topologicalKrullDim S.X = 2 := by
  have : IsProper S.f := S.modification.isProper
  rw [S.modification.isBirational.topologicalKrullDim_eq_of_isClosedMap S.f.isClosedMap]
  exact (PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim (R := S.A)).trans S.dimension_two

/-- **`X` is Cohen–Macaulay**: it is normal of dimension two, [Stacks, Tag 0B3D]. -/
theorem isCohenMacaulay_X : IsCohenMacaulay S.X :=
  isCohenMacaulay_of_isNormal_of_topologicalKrullDim_le_two S.X S.topologicalKrullDim_X.le

/-- The generic point of `X` lies over the punctured spectrum: it maps to the generic point of
`Spec(A)`, which is not the closed point, `A` not being a field. -/
theorem genericPoint_mem_preimage_puncturedSpectrumOpen :
    genericPoint S.X ∈ S.f ⁻¹ᵁ S.puncturedSpectrumOpen := by
  have hmem := S.modification.isBirational.bijOn.mapsTo
    (show genericPoint S.X ∈ genericPoints S.X by simp [genericPoints_eq_singleton])
  rw [genericPoints_eq_singleton, Set.mem_singleton_iff] at hmem
  change S.f (genericPoint S.X) ∈ ({S.closedPoint}ᶜ : Set S.base)
  rw [hmem, Set.mem_compl_singleton_iff]
  intro h
  have hbot := genericPoint_eq_bot_of_affine (CommRingCat.of S.A)
  rw [h] at hbot
  have h0 : ringKrullDim S.A = 0 := ringKrullDim_eq_zero_of_isField
    (IsLocalRing.isField_iff_maximalIdeal_eq.2 (congrArg PrimeSpectrum.asIdeal hbot))
  rw [S.dimension_two] at h0
  exact absurd h0 (by decide)

/-- **An open of `X` over the punctured spectrum is a preimage.** `f` is an isomorphism over
the punctured spectrum `U` (`isIso_morphismRestrict_puncturedSpectrum_of_isModification`), so an
open `W ⊆ f⁻¹(U)` is `f⁻¹(f(W))`. -/
theorem exists_preimage_eq_of_le_preimage_puncturedSpectrumOpen (W : S.X.Opens)
    (hW : W ≤ S.f ⁻¹ᵁ S.puncturedSpectrumOpen) :
    ∃ V : S.base.Opens, S.f ⁻¹ᵁ V = W := by
  have hiso : IsIso (S.f ∣_ S.puncturedSpectrumOpen) :=
    isIso_morphismRestrict_puncturedSpectrum_of_isModification S.A S.dimension_two S.f
      S.modification
  let h : (S.f ⁻¹ᵁ S.puncturedSpectrumOpen).toScheme ⟶ S.base :=
    (S.f ⁻¹ᵁ S.puncturedSpectrumOpen).ι ≫ S.f
  have hh : h = (S.f ∣_ S.puncturedSpectrumOpen) ≫ S.puncturedSpectrumOpen.ι :=
    (morphismRestrict_ι S.f S.puncturedSpectrumOpen).symm
  have : IsOpenImmersion h := by
    rw [hh]
    infer_instance
  refine ⟨h ''ᵁ ((S.f ⁻¹ᵁ S.puncturedSpectrumOpen).ι ⁻¹ᵁ W), ?_⟩
  ext x
  constructor
  · rintro ⟨y, hy, hxy⟩
    have hxU : x ∈ S.f ⁻¹ᵁ S.puncturedSpectrumOpen := by
      change S.f x ∈ S.puncturedSpectrumOpen
      rw [← hxy]
      exact y.2
    obtain rfl : y = ⟨x, hxU⟩ := h.isOpenEmbedding.injective hxy
    exact hy
  · exact fun hx => ⟨⟨x, hW hx⟩, hx, rfl⟩

/-- **The relative dualizing complex is not a module in a negative degree, when it is a dualizing
complex.** If `f^!(ω_A)` is a dualizing complex isomorphic to `M[-n]`, then `n ≥ 0`. See the
module documentation for the argument. -/
theorem zero_le_of_iso_singleFunctor (ωA : ModuleCat.{u} S.A)
    (hK : Stacks.Duality.IsDualizingComplex (S.relativeDualizingComplex ωA).obj)
    (M : S.X.Modules) (n : ℤ)
    (e : (S.relativeDualizingComplex ωA).obj ≅
      (DerivedCategory.singleFunctor S.X.Modules n).obj M) :
    0 ≤ n := by
  by_contra hn
  push Not at hn
  let O : S.X.Modules := SheafOfModules.unit S.X.ringCatSheaf
  have hO : O.IsQuasicoherent := _root_.isQuasicoherent_of_isCoherent _
  have hH1 : IsZero (((moduleGlobalSections S.X).rightDerived 1).obj O) := by
    let := HasDerivedCategory.standard S.X.Modules
    let := HasDerivedCategory.standard (ModuleCat.{u} Γ(S.X, ⊤))
    exact (Stacks.DerivedIndexing.isZero_rightDerived_obj_iff _ 1 _).2
      S.isZero_firstCohomologyStructureSheaf
  -- `Rf_*(𝒪_X[-n])` lies in `D^{≤ n}`.
  let P := singleQuasiCoherent O hO n
  have hLE : ((ObjectProperty.ι _).obj
      ((Stacks.Duality.quasiCoherentDerivedPushforward S.f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f)).obj P)).IsLE
        n := by
    change ((Stacks.Duality.derivedPushforward S.f).obj
      ((DerivedCategory.singleFunctor S.X.Modules n).obj O)).IsLE n
    rw [DerivedCategory.isLE_iff]
    intro i hi
    have e2 := (Stacks.Duality.derivedPushforward S.f).mapIso
      (((DerivedCategory.singleFunctors S.X.Modules).shiftIso (-n) n 0 (by omega)).app O).symm ≪≫
      ((Stacks.Duality.derivedPushforward S.f).commShiftIso (-n)).app _
    exact IsZero.of_iso
      ((S.isZero_homology_derivedPushforward_single O hO hH1 (-n + i) (by omega)).of_iso
        (((DerivedCategory.homologyFunctor S.base.Modules 0).shiftIso (-n) i (-n + i) rfl).app _))
      ((DerivedCategory.homologyFunctor _ i).mapIso e2)
  have hGE : ((ObjectProperty.ι _).obj (S.baseDualizingComplex ωA)).IsGE 0 := by
    change ((DerivedCategory.singleFunctor S.base.Modules 0).obj
      ((tilde.functor (CommRingCat.of S.A)).obj ωA)).IsGE 0
    infer_instance
  -- Hence every morphism `𝒪_X[-n] ⟶ f^!(ω_A)` vanishes.
  have hzero : ∀ u : (DerivedCategory.singleFunctor S.X.Modules n).obj O ⟶
      (S.relativeDualizingComplex ωA).obj, u = 0 := by
    intro u
    let u' : P ⟶ S.relativeDualizingComplex ωA := ObjectProperty.homMk u
    let E := Stacks.Duality.relativeDualizingComplexHomEquiv S.f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs S.f) (S.baseDualizingComplex ωA) P
    have hv : E u' = 0 :=
      (ObjectProperty.ι _).map_injective
        ((DerivedCategory.TStructure.t.zero _ n 0 hn).trans (Functor.map_zero _ _ _).symm)
    have h0 : E 0 = 0 := by
      rw [Stacks.Duality.relativeDualizingComplexHomEquiv_apply, Functor.map_zero, zero_comp]
    have hu' : u' = 0 := E.injective (hv.trans h0.symm)
    exact congrArg (ObjectProperty.ι _).map hu'
  -- So `Hom(𝒪_X, M) = 0`.
  have hOM : ∀ φ : O ⟶ M, φ = 0 := by
    intro φ
    apply (DerivedCategory.singleFunctor S.X.Modules n).map_injective
    rw [Functor.map_zero, ← cancel_mono e.inv, zero_comp]
    exact hzero _
  -- So `Γ(X, M) = 0`.
  have hΓ : Subsingleton (S.globalSectionsModule M) := by
    refine ⟨fun s t => ?_⟩
    obtain ⟨φ, rfl⟩ := (S.bijective_unitSectionHom M).2 s
    obtain ⟨ψ, rfl⟩ := (S.bijective_unitSectionHom M).2 t
    rw [hOM φ, hOM ψ]
  -- `M` is quasi-coherent, and so is `f_*M`.
  have hM : M.IsQuasicoherent :=
    isQuasicoherent_of_iso S.X _ _
      ((DerivedCategory.homologyFunctor S.X.Modules n).mapIso e ≪≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso S.X.Modules n).app M)
      ((S.relativeDualizingComplex ωA).property n)
  let G := (Scheme.Modules.pushforward S.f).obj M
  have : G.IsQuasicoherent :=
    isQuasicoherent_of_iso S.base _ _ (S.derivedPushforwardSingleIso.app M)
      ((isQuasicoherent_homology_derivedPushforward_of_qcqs S.f) (singleQuasiCoherent M hM 0) 0)
  -- `f_*M = 0`.
  have hG : IsZero G :=
    (Functor.map_isZero (tilde.functor (CommRingCat.of S.A))
      (@ModuleCat.isZero_of_subsingleton _ _ _ hΓ)).of_iso (asIso G.fromTildeΓ).symm
  -- Every section of `M` over an open of `f⁻¹(U)` vanishes.
  have hsec : ∀ W : S.X.Opens, W ≤ S.f ⁻¹ᵁ S.puncturedSpectrumOpen → ∀ s : Γ(M, W), s = 0 := by
    intro W hW s
    obtain ⟨V, rfl⟩ := S.exists_preimage_eq_of_le_preimage_puncturedSpectrumOpen W hW
    have h := congrArg (fun φ : G ⟶ G => (φ.app V).hom s) (hG.eq_of_src (𝟙 G) 0)
    simp only [Scheme.Modules.Hom.id_app, AddCommGrpCat.hom_id, AddMonoidHom.coe_id,
      Scheme.Modules.Hom.zero_app, AddCommGrpCat.hom_zero] at h
    exact h
  -- So the stalk of `M` at the generic point vanishes.
  have hstalk : Subsingleton (M.presheaf.stalk (genericPoint S.X)) := by
    refine ⟨fun a b => ?_⟩
    suffices hz : ∀ t : M.presheaf.stalk (genericPoint S.X), t = 0 by rw [hz a, hz b]
    intro t
    obtain ⟨V, hV, s, rfl⟩ := TopCat.Presheaf.exists_germ_eq M.presheaf t
    let W := V ⊓ S.f ⁻¹ᵁ S.puncturedSpectrumOpen
    have hηW : genericPoint S.X ∈ W := ⟨hV, S.genericPoint_mem_preimage_puncturedSpectrumOpen⟩
    rw [← TopCat.Presheaf.germ_res_apply M.presheaf (homOfLE inf_le_left : W ⟶ V) _ hηW s,
      hsec W inf_le_right (M.presheaf.map (homOfLE inf_le_left : W ⟶ V).op s), map_zero]
  -- But that stalk is a dualizing module over a local ring, hence nonzero.
  have := hM
  let := Stacks.ModuleStalkSpecialization.stalkModule M (genericPoint S.X)
  have hKM := Stacks.Duality.isDualizingComplex_of_iso e hK
  have hnt := Stacks.Duality.nontrivial_of_isDualizingComplex_single
    (ModuleCat.of (S.X.presheaf.stalk (genericPoint S.X))
      (M.presheaf.stalk (genericPoint S.X))) 0
    (Stacks.Duality.isDualizingComplex_single_stalk M n hKM (genericPoint S.X))
  exact (not_subsingleton_iff_nontrivial.2 hnt) hstalk

variable (ωA : ModuleCat.{u} S.A)

/-- **`H⁰(f^!(ω_A))`**, which is the dualizing module of `X` normalized relative to `ω_A` once
`f^!(ω_A)` is a dualizing complex. -/
def normalizedDualizingSheaf : S.X.Modules :=
  (DerivedCategory.homologyFunctor S.X.Modules 0).obj (S.relativeDualizingComplex ωA).obj

variable {ωA} (hωA : Stacks.Duality.IsDualizingRingModule S.A ωA)
  (hK : Stacks.Duality.IsDualizingComplex (S.relativeDualizingComplex ωA).obj)

include hωA hK in
/-- **A dualizing `f^!(ω_A)` is concentrated in degree zero**, with coherent cohomology there.
It is a coherent module placed in a single degree `n` by [Stacks, Tag 0AWT] (`X` is connected and
Cohen–Macaulay), and `n ≤ 0` (`le_zero_of_iso_singleFunctor`) and `n ≥ 0`
(`zero_le_of_iso_singleFunctor`). -/
theorem isZero_homology_relativeDualizingComplex_and_isCoherent :
    (∀ j : ℤ, j ≠ 0 → IsZero ((DerivedCategory.homologyFunctor S.X.Modules j).obj
      (S.relativeDualizingComplex ωA).obj)) ∧ (S.normalizedDualizingSheaf ωA).IsCoherent := by
  obtain ⟨n, hcoh, -, ⟨e⟩⟩ :=
    Stacks.Duality.exists_coherent_cohenMacaulay_iso_single_of_connected _ hK S.isCohenMacaulay_X
  have := hωA.nontrivial
  obtain rfl : n = 0 :=
    le_antisymm (S.le_zero_of_iso_singleFunctor ωA _ n e)
      (S.zero_le_of_iso_singleFunctor ωA hK _ n e)
  refine ⟨fun j hj => ?_, hcoh⟩
  exact IsZero.of_iso
    ((HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 _ j hj).of_iso
      ((DerivedCategory.homologyFunctorFactors S.X.Modules j).app
        ((CochainComplex.singleFunctor S.X.Modules 0).obj _)))
    ((DerivedCategory.homologyFunctor S.X.Modules j).mapIso e)

include hωA hK in
/-- **The normalization isomorphism `f^!(ω_A) ≅ H⁰(f^!(ω_A))[0]`**, when `f^!(ω_A)` is a
dualizing complex. -/
def normalizedDualizingSheafIso :
    (S.relativeDualizingComplex ωA).obj ≅
      (DerivedCategory.singleFunctor S.X.Modules 0).obj (S.normalizedDualizingSheaf ωA) :=
  (DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero _ 0
    (S.isZero_homology_relativeDualizingComplex_and_isCoherent hωA hK).1).some

/-- **[Stacks, Remark 0B4R], given that `f^!(ω_A)` is a dualizing complex.** `H⁰(f^!(ω_A))` is
a dualizing module on `X` normalized relative to `ω_A`. -/
def dualizingNormalizationOfIsDualizingComplex :
    S.DualizingNormalization ωA (S.normalizedDualizingSheaf ωA) where
  isDualizing := ⟨(S.isZero_homology_relativeDualizingComplex_and_isCoherent hωA hK).2, 0,
    (Stacks.Duality.isDualizingComplex_singleFunctor_model_iff inferInstance
      (HasDerivedCategory.standard _) 0 _).2
      (Stacks.Duality.isDualizingComplex_of_iso (S.normalizedDualizingSheafIso hωA hK) hK)⟩
  normalizedIso := S.normalizedDualizingSheafIso hωA hK

end AlgebraicGeometry.RationalSingularitySituation

end
