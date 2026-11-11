module

public import StacksFrontier.AlgebraicGeometry.BlowupTwistUnit.NormalizedDualizingSurfaceChain
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Local
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleExistence
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModuleInvertibleTwist
public import StacksFrontier.AlgebraicGeometry.Duality.NormalizedModelOnAffineLocalBase
public import StacksFrontier.AlgebraicGeometry.Duality.SurfaceDualizingDegree.NormalizedUpperShriek
public import StacksFrontier.AlgebraicGeometry.Duality.UpperShriekBounded
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal
public import
  StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.GorensteinBlowupSequence
public import StacksFrontier.RingTheory.Dualizing.QuotientExtConcentration
public import StacksFrontier.RingTheory.LocalCohomology.TopLocalCohomology
public import StacksCore.Tactic.StacksAttribute

/-!
# Dualizing modules of normal surfaces and of their normal modifications

This file completes [Stacks, Remark 0B4R] beyond the equivalence of its conditions (1) and (2),
which is `Stacks.Duality.exists_isDualizingComplex_iff_exists_isDualizingModule`.

* **"where `n` can be any integer".** If a coherent module `ω` placed in one degree is a
  dualizing complex, then it is one placed in every degree, because a shift of a dualizing complex
  is a dualizing complex. So the existential degree in `Stacks.Duality.IsDualizingModule` and
  `Stacks.Duality.IsDualizingRingModule` may be read universally.
* **The local ring `A`.** For a Noetherian normal local domain `A` of dimension two, `A` has a
  dualizing complex if and only if it has a dualizing module: `A` is Cohen–Macaulay, so
  [Stacks, Tag 0AWS] concentrates its dualizing complex in one degree.
* **Normal modifications.** If `A` is a Noetherian normal local domain of dimension two having a
  dualizing module and `f : X ⟶ Spec(A)` is a modification with `X` normal, then `X` has a
  dualizing module ([Stacks, Tag 0AWI]: `f^!ω_A^•` is a dualizing complex on `X`).
* **The normalization relative to `ω_A`.** In that situation, for *every* dualizing module `ω_A`
  of `Spec(A)`, the complex `ω_A[2]` is the normalized dualizing complex of `Spec(A)` (it is
  modelled by a normalized dualizing complex over `Γ(Spec(A), ⊤)`), and `X` carries a dualizing
  module `ω_X` with `f^!(ω_A) ≅ ω_X`, both in degree zero; since `f^!` commutes with shifts this
  says that `ω_X[2]` is the dualizing complex of `X` normalized relative to `ω_A[2]`.

## Main results

* `Stacks.Duality.isDualizingModule_iff_forall_isDualizingComplex`
* `Stacks.Duality.isDualizingRingModule_iff_forall_isDualizingComplex`
* `Stacks.Duality.exists_isDualizingComplex_iff_exists_isDualizingRingModule`
* `Stacks.Duality.isDualizingModule_relativeDualizingModule_of_isNormalSurface`
* `Stacks.Duality.exists_isDualizingModule_of_isModification`
* `Stacks.Duality.isNormalizedDualizingComplex_of_isZero_homology_ne_neg_two`
* `Stacks.Duality.exists_isNormalizedDualizingComplex_single_neg_two`
* `Stacks.Duality.exists_normalized_isDualizingModule_of_isModification`

## Implementation notes

`Stacks.Duality.IsDualizingModule` is read at `HasDerivedCategory.standard`, while the twisted
inverse image `f^!` lives at the locally small model
`AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`. A module placed in one degree is a
dualizing complex at one model if and only if at the other
(`Stacks.Duality.isDualizingComplex_singleFunctor_model_iff`), which is how the two are joined.

The base's normalized dualizing complex is produced from its dualizing module by
`Stacks.Duality.exists_isNormalizedDualizingComplex_isTildeModelOnAnyModel_top`, and `f^!` of it
is identified with `ω_X[2]` by
`Stacks.Duality.relativeDualizingComplexIsoShiftTwoOfIsNormalSurface`; the normalization in
degree zero is `Stacks.BlowupTwistUnit.normalizedIsoOfIsNormalSurface`.

## References

* [Stacks Project, Tag 0B4R](https://stacks.math.columbia.edu/tag/0B4R)
* [Stacks Project, Tag 0AWI](https://stacks.math.columbia.edu/tag/0AWI)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
* [Stacks Project, Tag 0AU5](https://stacks.math.columbia.edu/tag/0AU5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace Stacks.Duality

/-! ### The degree of a dualizing module is arbitrary -/

section AnyDegree

attribute [local instance] HasDerivedCategory.standard

/-- **Stacks Project, Remark 0B4R, "where `n` can be any integer".** A sheaf of modules is a
dualizing module if and only if it is coherent and is a dualizing complex placed in *every*
cohomological degree: placing it in degree `n` is a shift of placing it in degree `m`. -/
@[stacks 0B4R "in (2), the integer n can be any integer"]
theorem isDualizingModule_iff_forall_isDualizingComplex {X : Scheme.{u}} [IsLocallyNoetherian X]
    (ω : X.Modules) :
    IsDualizingModule ω ↔ ω.IsCoherent ∧
      ∀ n : ℤ, IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules n).obj ω) := by
  refine ⟨fun ⟨hc, m, hm⟩ => ⟨hc, fun n => ?_⟩, fun ⟨hc, h⟩ => ⟨hc, 0, h 0⟩⟩
  exact isDualizingComplex_of_iso
    (((DerivedCategory.singleFunctors X.Modules).shiftIso (m - n) n m (by omega)).app ω)
    (IsDualizingComplex.shift hm (m - n))

/-- Being a dualizing complex over `A` depends on the object only through its isomorphism class,
for modules in any universe. -/
private theorem isDualizingComplex_of_iso_anyUniverse {A : Type u} [CommRing A]
    [IsNoetherianRing A] [HasDerivedCategory (ModuleCat.{v} A)]
    {K L : DerivedCategory (ModuleCat.{v} A)} (e : K ≅ L)
    (hK : Dualizing.IsDualizingComplex (A := A) K) : Dualizing.IsDualizingComplex (A := A) L := by
  constructor
  · obtain ⟨a, b, I, hge, hle, hinj, ⟨eI⟩⟩ := hK.finiteInjectiveDimension
    exact ⟨a, b, I, hge, hle, hinj, ⟨e.symm ≪≫ eI⟩⟩
  · intro i
    have : Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).obj K) :=
      hK.finiteCohomology i
    exact Module.Finite.equiv
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).mapIso e).toLinearEquiv
  · rintro I ⟨eI⟩ hinj hbound
    exact hK.homothetyQuasiIso I ⟨eI ≪≫ e.symm⟩ hinj hbound

/-- **Stacks Project, Remark 0B4R, "where `n` can be any integer", over a ring.** A module over a
Noetherian ring is a dualizing module if and only if it is finite and is a dualizing complex
placed in every cohomological degree. -/
@[stacks 0B4R "in (2) over a Noetherian ring, the integer n can be any integer"]
theorem isDualizingRingModule_iff_forall_isDualizingComplex (A : Type u) [CommRing A]
    [IsNoetherianRing A] (M : Type v) [AddCommGroup M] [Module A M] :
    IsDualizingRingModule A M ↔ Module.Finite A M ∧
      ∀ n : ℤ, Dualizing.IsDualizingComplex (A := A)
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) n).obj (ModuleCat.of A M)) := by
  refine ⟨fun ⟨hc, m, hm⟩ => ⟨hc, fun n => ?_⟩, fun ⟨hc, h⟩ => ⟨hc, 0, h 0⟩⟩
  exact @isDualizingComplex_of_iso_anyUniverse _ _ _ (HasDerivedCategory.standard _) _ _
    (((DerivedCategory.singleFunctors (ModuleCat.{v} A)).shiftIso (m - n) n m
      (by omega)).app _) (Dualizing.isDualizingComplex_shift _ hm (m - n))

/-- **Stacks Project, Remark 0B4R, for a Noetherian normal local domain of dimension two.** Such
a ring `A` has a dualizing complex if and only if it has a dualizing module, with complexes and
modules in any universe `max u v` containing `A`. It is Cohen–Macaulay, being normal of dimension
two, so by [Stacks, Tag 0AWS] a dualizing complex has its cohomology in a single degree and is
that cohomology module placed there. -/
@[stacks 0B4R "the equivalence of (1) and (2) for a Noetherian normal local domain of dimension 2"]
theorem exists_isDualizingComplex_iff_exists_isDualizingRingModule (A : Type u) [CommRing A]
    [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A] (hA : ringKrullDim A = 2) :
    (∃ K : DerivedCategory (ModuleCat.{max u v} A), Dualizing.IsDualizingComplex K) ↔
      ∃ (M : Type (max u v)) (_ : AddCommGroup M) (_ : Module A M),
        IsDualizingRingModule A M := by
  constructor
  · rintro ⟨K, hK⟩
    obtain ⟨d, hd⟩ := Dualizing.exists_homology_concentrated_of_isMaximalCohenMacaulay_self.{u, v}
      K hK ((isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay A).mp
        (isCohenMacaulayLocalRing_of_isNormalRing_of_ringKrullDim_eq_two
          (IsNormalRing.of_isIntegrallyClosed A) hA))
    let e := (DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero K d hd).some
    exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) d).obj K, inferInstance,
      inferInstance, hK.finiteCohomology d, d,
      @isDualizingComplex_of_iso_anyUniverse _ _ _ (HasDerivedCategory.standard _) _ _ e hK⟩
  · rintro ⟨M, _, _, -, n, hn⟩
    exact ⟨_, hn⟩

/-- **A dualizing complex over a Cohen–Macaulay local ring of dimension two with cohomology only
in degree `-2` is normalized.** It is its cohomology module placed in degree `-2`, and over a
Cohen–Macaulay local ring a module which is dualizing in some degree is normalized in degree
minus the dimension ([Stacks, Tag 0AWS]). -/
theorem isNormalizedDualizingComplex_of_isZero_homology_ne_neg_two {R : Type u} [CommRing R]
    [IsNoetherianRing R] [IsLocalRing R] (hR : IsCohenMacaulayLocalRing R)
    (hdim : ringKrullDim R = 2) (ω : DerivedCategory (ModuleCat.{u} R))
    (hω : Dualizing.IsDualizingComplex ω)
    (hz : ∀ i : ℤ, i ≠ -2 → IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} R) i).obj ω)) :
    Dualizing.IsNormalizedDualizingComplex.{u, u} ω := by
  obtain ⟨e⟩ := DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero ω (-2) hz
  have hn := (Dualizing.isDualizingComplex_iff_of_iso e).1 hω
  have h := Dualizing.isNormalizedDualizingComplex_single_neg_localRingDimension hR _ (-2) hn
  have hh : (IsLocalRing.maximalIdeal R).height = 2 := by
    have := (IsLocalRing.maximalIdeal_height_eq_ringKrullDim (R := R)).trans hdim
    exact WithBot.coe_injective this
  have hd : (-(Dualizing.localRingDimension R : ℤ)) = -2 := by
    rw [Dualizing.localRingDimension, hh]
    rfl
  rw [hd] at h
  exact Stacks.LocalCohomology.isNormalizedDualizingComplex_of_ulift_zero
    ((Dualizing.isNormalizedDualizingComplex_congr e).mpr h)

end AnyDegree

/-! ### Normal modifications -/

section Modification

-- The twisted inverse image lives at the locally small models
-- (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules, and `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

variable {S : Scheme.{u}} [IsAffine S] [AlgebraicGeometry.IsNoetherian S]
  [IsNoetherianRing Γ(S, ⊤)] [IsLocalRing Γ(S, ⊤)]

/-- **`ω_X = H^{-2}(f^!ω_S^•)` is a dualizing module.** Let `S` be affine with `Γ(S, ⊤)` a
Noetherian local ring, `ω_S^•` modelled on `S` by a normalized dualizing complex over `Γ(S, ⊤)`,
and `g : W ⟶ S` proper with `W` a connected normal scheme of dimension two. Then the relative
dualizing module `H^{-2}(g^!ω_S^•)` of [Stacks, Tag 0AWI] is coherent and, placed in degree `-2`,
is the dualizing complex `g^!ω_S^•`. -/
theorem isDualizingModule_relativeDualizingModule_of_isNormalSurface {W : Scheme.{u}}
    (g : W ⟶ S) [IsProper g] [ConnectedSpace W] (hnormal : IsNormal W)
    (hW : topologicalKrullDim W = 2) (ωS : quasiCoherentDerivedCategory S)
    (ω : DerivedCategory (ModuleCat.{u} Γ(S, ⊤)))
    (hω : Dualizing.IsNormalizedDualizingComplex.{u, u} ω)
    (hmodel : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top S) ω) :
    letI : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian g
    IsDualizingModule
      (relativeDualizingModule g (isQuasicoherent_homology_derivedPushforward_of_qcqs g) ωS) := by
  let : IsLocallyNoetherian W := LocallyOfFiniteType.isLocallyNoetherian g
  refine ⟨(coherent_cohenMacaulay_relativeDualizingModule_of_isNormalSurface g hnormal hW ωS ω
    hω hmodel).1, -2, ?_⟩
  refine (isDualizingComplex_singleFunctor_model_iff inferInstance
    (HasDerivedCategory.standard _) (-2) _).2 ?_
  exact isDualizingComplex_of_iso
    (relativeDualizingComplexIsoShiftTwoOfIsNormalSurface g hnormal hW ωS ω hω hmodel ≪≫
      ((DerivedCategory.singleFunctors W.Modules).shiftIso 2 (-2) 0 (by norm_num)).app _)
    (isDualizingComplex_relativeDualizingComplex g ωS ω hω.1 hmodel)

variable (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]

omit [IsLocalRing A] [IsNormalDomain A] in
/-- The global sections of `Spec(A)` form a Noetherian ring. -/
theorem isNoetherianRing_globalSections_spec : IsNoetherianRing Γ(Spec (.of A), ⊤) :=
  IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top _⟩

omit [IsNoetherianRing A] [IsNormalDomain A] in
/-- The global sections of `Spec(A)` form a local ring. -/
theorem isLocalRing_globalSections_spec : IsLocalRing Γ(Spec (.of A), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv.isLocalRing

omit [IsNormalDomain A] in
/-- **The input pair on `Spec(A)` from a dualizing module.** If `Spec(A)` has a dualizing module,
then there are a normalized dualizing complex over `Γ(Spec(A), ⊤)` and an object of
`D_QCoh(𝒪_{Spec A})` modelled on `Spec(A)` by it. -/
theorem exists_isNormalizedDualizingComplex_of_isDualizingModule
    (hA : ∃ ωA : (Spec (.of A)).Modules, IsDualizingModule ωA) :
    letI := isNoetherianRing_globalSections_spec A
    letI := isLocalRing_globalSections_spec A
    ∃ (ωS : quasiCoherentDerivedCategory (Spec (.of A)))
      (ω : DerivedCategory (ModuleCat.{u} Γ(Spec (.of A), ⊤))),
      Dualizing.IsNormalizedDualizingComplex.{u, u} ω ∧
        IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top _) ω := by
  let := isNoetherianRing_globalSections_spec A
  let := isLocalRing_globalSections_spec A
  obtain ⟨ωA, -, n, hn⟩ := hA
  obtain ⟨ω₀, hω₀, -⟩ := hn ⊤ (isAffineOpen_top _)
  exact exists_isNormalizedDualizingComplex_isTildeModelOnAnyModel_top ω₀ hω₀

variable {A}

omit [IsLocalRing A] in
/-- A modification of `Spec(A)`, for `A` of dimension two, is two-dimensional: a proper
birational morphism of integral schemes preserves dimension. -/
theorem topologicalKrullDim_eq_two_of_isModification (hA2 : ringKrullDim A = 2)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsModification f) :
    topologicalKrullDim X = 2 := by
  have : IsProper f := hf.isProper
  have : IsIntegral X := hf.source_isIntegral
  have h : topologicalKrullDim X = ringKrullDim A := by
    rw [← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    exact hf.isBirational.topologicalKrullDim_eq_of_isClosedMap f.isClosedMap
  rw [h, hA2]

/-- **Stacks Project, Remark 0B4R: a normal modification inherits a dualizing module.** Let `A`
be a Noetherian normal local domain of dimension two which has a dualizing module, that is,
`Spec(A)` has one, and let `f : X ⟶ Spec(A)` be a modification with `X` normal. Then `X` has a
dualizing module: by [Stacks, Tag 0AWI] the twisted inverse image of the normalized dualizing
complex of `Spec(A)` is a dualizing complex on `X`, and its cohomology in degree `-2` is a
dualizing module. -/
@[stacks 0B4R "if A has a dualizing module, so does every normal modification X of Spec(A)"]
theorem exists_isDualizingModule_of_isModification (hA2 : ringKrullDim A = 2)
    (hA : ∃ ωA : (Spec (.of A)).Modules, IsDualizingModule ωA)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsModification f) [IsNormal X] :
    haveI : IsProper f := hf.isProper
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    ∃ ωX : X.Modules, IsDualizingModule ωX := by
  have : IsProper f := hf.isProper
  have : IsIntegral X := hf.source_isIntegral
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : ConnectedSpace X := (irreducibleSpace_of_isIntegral X).connectedSpace
  let := isNoetherianRing_globalSections_spec A
  let := isLocalRing_globalSections_spec A
  obtain ⟨ωS, ω, hω, hmodel⟩ := exists_isNormalizedDualizingComplex_of_isDualizingModule A hA
  exact ⟨_, isDualizingModule_relativeDualizingModule_of_isNormalSurface f ‹IsNormal X›
    (topologicalKrullDim_eq_two_of_isModification hA2 f hf) ωS ω hω hmodel⟩

/-- **`ω_A[2]` is the normalized dualizing complex of `Spec(A)`, for every dualizing module
`ω_A`.** Let `A` be a Noetherian normal local domain of dimension two and `ω_A` a dualizing
module of `Spec(A)`. Then `ω_A` placed in degree `-2` is modelled on `Spec(A)` by a normalized
dualizing complex over `Γ(Spec(A), ⊤)`.

Over `⊤` the complex `ω_A[2]` is the associated sheaf of a dualizing complex `ω` over
`Γ(Spec(A), ⊤)`; the cohomology of `ω` is read off that of `ω_A[2]` through the associated sheaf,
so it vanishes outside degree `-2`, and `Γ(Spec(A), ⊤) ≅ A` is Cohen–Macaulay of dimension two,
so `ω` is normalized (`isNormalizedDualizingComplex_of_isZero_homology_ne_neg_two`). -/
theorem exists_isNormalizedDualizingComplex_single_neg_two (hA2 : ringKrullDim A = 2)
    (ωA : (Spec (.of A)).Modules) (hωA : IsDualizingModule ωA) :
    letI := isNoetherianRing_globalSections_spec A
    letI := isLocalRing_globalSections_spec A
    ∃ ω : DerivedCategory (ModuleCat.{u} Γ(Spec (.of A), ⊤)),
      Dualizing.IsNormalizedDualizingComplex.{u, u} ω ∧
        IsTildeModelOnAnyModel ((DerivedCategory.singleFunctor _ (-2)).obj ωA) ⊤
          (isAffineOpen_top _) ω := by
  let := isNoetherianRing_globalSections_spec A
  let := isLocalRing_globalSections_spec A
  have hn := ((isDualizingModule_iff_forall_isDualizingComplex ωA).1 hωA).2 (-2)
  have hloc : IsDualizingComplex ((DerivedCategory.singleFunctor _ (-2)).obj ωA) :=
    (isDualizingComplex_singleFunctor_model_iff (HasDerivedCategory.standard _) inferInstance
      (-2) ωA).2 hn
  obtain ⟨ω, hω, hmodel⟩ :=
    exists_isTildeModelOnAnyModel_of_hasDualizingModelOn (hloc ⊤ (isAffineOpen_top _))
  refine ⟨ω, ?_, hmodel⟩
  let e : A ≃+* Γ(Spec (.of A), ⊤) :=
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
  have hCM : IsCohenMacaulayLocalRing Γ(Spec (.of A), ⊤) :=
    (isCohenMacaulayLocalRing_iff_of_ringEquiv e).mp
      (isCohenMacaulayLocalRing_of_isNormalRing_of_ringKrullDim_eq_two
        (IsNormalRing.of_isIntegrallyClosed A) hA2)
  have hdim : ringKrullDim Γ(Spec (.of A), ⊤) = 2 :=
    (ringKrullDim_eq_of_ringEquiv e).symm.trans hA2
  refine isNormalizedDualizingComplex_of_isZero_homology_ne_neg_two hCM hdim ω hω fun i hi => ?_
  have hU := isAffineOpen_top (Spec (.of A))
  have h1 : IsZero ((Scheme.Modules.restrictFunctor (⊤ : (Spec (.of A)).Opens).ι).obj
      ((DerivedCategory.homologyFunctor _ i).obj
        ((DerivedCategory.singleFunctor _ (-2)).obj ωA))) :=
    Functor.map_isZero _ ((HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ)
      (-2) _ i hi).of_iso ((DerivedCategory.homologyFunctorFactors _ i).app
        ((CochainComplex.singleFunctor _ (-2)).obj ωA)))
  let := HasDerivedCategory.standard (⊤ : (Spec (.of A)).Opens).toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(Spec (.of A), ⊤))
  let e' : ((DerivedCategory.homologyFunctor _ i).obj
      ((DerivedCategory.singleFunctor _ (-2)).obj ωA)).restrict (⊤ : (Spec (.of A)).Opens).ι ≅
      (Scheme.Modules.pullback hU.isoSpec.hom).obj
        (tilde ((DerivedCategory.homologyFunctor _ i).obj ω)) :=
    ((Dualizing.mapDerivedCategoryHomologyIso
        (Scheme.Modules.restrictFunctor (⊤ : (Spec (.of A)).Opens).ι) i).app _).symm ≪≫
      (DerivedCategory.homologyFunctor _ i).mapIso hmodel.some ≪≫
      (Dualizing.mapDerivedCategoryHomologyIso
        (tilde.functor Γ(Spec (.of A), ⊤) ⋙
          Scheme.Modules.restrictFunctor hU.isoSpec.hom) i).app ω ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app _
  have h2 : IsZero ((Scheme.Modules.restrictFunctor hU.isoSpec.inv).obj
      ((Scheme.Modules.pullback hU.isoSpec.hom).obj
        (tilde ((DerivedCategory.homologyFunctor _ i).obj ω)))) :=
    Functor.map_isZero _ (h1.of_iso e'.symm)
  have hT : IsZero (tilde ((DerivedCategory.homologyFunctor _ i).obj ω)) :=
    h2.of_iso (((Scheme.Modules.restrictFunctor hU.isoSpec.inv).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback hU.isoSpec.hom).app _).symm ≪≫
        Stacks.AlgebraicGeometry.CoherentTFAE.restrictIsoSelf hU.isoSpec.symm _).symm)
  exact (moduleSpecΓFunctor.map_isZero hT).of_iso (tilde.toTildeΓNatIso.app _)

/-- **Stacks Project, Remark 0B4R: the dualizing module of `X` normalized relative to `ω_A`.**
Let `A` be a Noetherian normal local domain of dimension two, `ω_A` a dualizing module of
`Spec(A)`, and `f : X ⟶ Spec(A)` a modification with `X` normal. Then

* `ω_A[2]` is the normalized dualizing complex of `Spec(A)`: it is modelled on `Spec(A)` by a
  normalized dualizing complex over `Γ(Spec(A), ⊤)`, and
* there is a dualizing module `ω_X` of `X` with `f^!(ω_A[0]) ≅ ω_X[0]`.

As `f^!` commutes with shifts, the last isomorphism says that `ω_X[2]` is the dualizing complex
of `X` normalized relative to `ω_A[2]`, which is the convention fixed by the remark
([Stacks, Section 0AU5]). The statement is for every dualizing module `ω_A` of `Spec(A)`. -/
@[stacks 0B4R "for every dualizing module omega_A of Spec(A), omega_A[2] is normalized and the \
  dualizing module omega_X of X normalized relative to omega_A exists: f^!(omega_A) = omega_X \
  in degree zero"]
theorem exists_normalized_isDualizingModule_of_isModification (hA2 : ringKrullDim A = 2)
    (ωA : (Spec (.of A)).Modules) (hωA : IsDualizingModule ωA)
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (hf : IsModification f) [IsNormal X] :
    haveI : IsProper f := hf.isProper
    letI : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
    letI := isNoetherianRing_globalSections_spec A
    letI := isLocalRing_globalSections_spec A
    haveI : ωA.IsCoherent := hωA.1
    (∃ ω : DerivedCategory (ModuleCat.{u} Γ(Spec (.of A), ⊤)),
      Dualizing.IsNormalizedDualizingComplex.{u, u} ω ∧
        IsTildeModelOnAnyModel ((DerivedCategory.singleFunctor _ (-2)).obj ωA) ⊤
          (isAffineOpen_top _) ω) ∧
    ∃ ωX : X.Modules, IsDualizingModule ωX ∧
      Nonempty (((twistedInverseImage f
          (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).obj
        (singleQuasiCoherent ωA (isQuasicoherent_of_isCoherent ωA) 0)).obj ≅
          (DerivedCategory.singleFunctor X.Modules 0).obj ωX) := by
  have : IsProper f := hf.isProper
  have : IsIntegral X := hf.source_isIntegral
  let : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : ConnectedSpace X := (irreducibleSpace_of_isIntegral X).connectedSpace
  let := isNoetherianRing_globalSections_spec A
  let := isLocalRing_globalSections_spec A
  have : ωA.IsCoherent := hωA.1
  have : ConnectedSpace (Spec (.of A)) := (irreducibleSpace_of_isIntegral _).connectedSpace
  have hSnormal : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  have hSdim : topologicalKrullDim (Spec (.of A)) = 2 := by
    rw [← hA2, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
    rfl
  have hXdim := topologicalKrullDim_eq_two_of_isModification hA2 f hf
  have hqc : ωA.IsQuasicoherent := isQuasicoherent_of_isCoherent ωA
  obtain ⟨ω, hω, hmodel⟩ := exists_isNormalizedDualizingComplex_single_neg_two hA2 ωA hωA
  let ωS : quasiCoherentDerivedCategory (Spec (.of A)) := singleQuasiCoherent ωA hqc (-2)
  have hmodel' : IsTildeModelOnAnyModel ωS.obj ⊤ (isAffineOpen_top _) ω := hmodel
  let iA : relativeDualizingModule (𝟙 _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 _)) ωS ≅ ωA :=
    Stacks.BlowupTwistUnit.relativeDualizingModuleIdIso hSdim ωS ≪≫
      (DerivedCategory.singleFunctorCompHomologyFunctorIso _ (-2)).app ωA
  let jA : singleQuasiCoherent ωA hqc 0 ≅ singleQuasiCoherent (relativeDualizingModule (𝟙 _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs (𝟙 _)) ωS)
      (isQuasicoherent_relativeDualizingModule _ _ ωS) 0 :=
    ObjectProperty.isoMk _ ((DerivedCategory.singleFunctor _ 0).mapIso iA.symm)
  refine ⟨⟨ω, hω, hmodel⟩, _,
    isDualizingModule_relativeDualizingModule_of_isNormalSurface f ‹IsNormal X› hXdim ωS ω hω
      hmodel', ⟨?_⟩⟩
  exact (ObjectProperty.ι _).mapIso ((twistedInverseImage f
      (isQuasicoherent_homology_derivedPushforward_of_qcqs f)).mapIso jA) ≪≫
    Stacks.BlowupTwistUnit.normalizedIsoOfIsNormalSurface hSnormal hSdim f ‹IsNormal X› hXdim
      ωS ω hω hmodel'

end Modification

end Stacks.Duality

end
