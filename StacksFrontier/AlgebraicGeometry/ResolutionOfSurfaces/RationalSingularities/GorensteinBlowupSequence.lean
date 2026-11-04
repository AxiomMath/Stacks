module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.DualizingQuotientBlowUp
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.DualizingQuotientBlowupChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.SingularBlowupPrincipalization
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.SituationCohenMacaulay
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.SingularPointBlowupChainResolution
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Birational.Dominant
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayLocus
public import StacksFrontier.AlgebraicGeometry.Duality.GorensteinSchemes.StructureSheafDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.DualizingModule
public import StacksFrontier.AlgebraicGeometry.ClosedLift.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType
public import StacksFrontier.RingTheory.Dualizing.DualizingComplexes.EssentiallyFiniteType
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Resolution.RationalSingularPointsResolution
import all StacksFrontier.RingTheory.Dualizing.DualizingComplexes.PolynomialBaseChange

/-!
# The assembly of [Stacks, Tag 0BBV]

Let `A` be a local normal Nagata domain of dimension two defining a rational singularity and having
a dualizing complex. [Stacks, Tag 0BBV] produces a sequence of blowups in singular closed points
with normal stages whose final scheme `X` has invertible dualizing sheaf. The proof is pointwise:

* `A` is Cohen–Macaulay, so it has a dualizing module `ω_A`, and `ω_A` is isomorphic to a nonzero
  ideal `J` (it is torsion free of rank one);
* a sequence of blowups along which `J` becomes principal at every singular point
  (`AlgebraicGeometry.exists_singularPointBlowupChain_principal`; the source takes it from
  [Stacks, Tags 0ESN and 0BBT]);
* at every point `x` of `X` a dualizing module of `𝒪_{X,x}` is a quotient of `𝒪_{X,x} ⊗_A ω_A`
  (`AlgebraicGeometry.dualizingQuotientAt_of_singularPointBlowupChain_of_local` over the local
  step `AlgebraicGeometry.dualizingQuotientAt_blowUp_maximalIdealSheaf_of_isDualizingComplex`);
* so at a singular point `𝒪_{X,x}` is Gorenstein
  (`AlgebraicGeometry.isGorenstein_of_dualizingQuotientAt`), and regular points are Gorenstein;
* on a Gorenstein scheme of finite type over `A` the structure sheaf is a dualizing module, and
  it is invertible.

## Main results

* `Dualizing.exists_isDualizingRingModule_of_isMaximalCohenMacaulay`: a Cohen–Macaulay Noetherian
  local ring with a dualizing complex has a dualizing module.
* `AlgebraicGeometry.stalkAlgebraOfSpec_injective`: `A ⟶ 𝒪_{X,x}` is injective for `X` integral
  dominating `Spec(A)`.
* `Stacks.Duality.isDualizingComplex_unit_of_forall_affine`: the structure sheaf of a Gorenstein
  scheme whose affine rings of sections have dualizing complexes is a dualizing complex.
* `AlgebraicGeometry.exists_isDualizingModule_isInvertible_of_isGorenstein`: a Gorenstein scheme
  locally of finite type over a ring with a dualizing complex has an invertible dualizing module.
* `AlgebraicGeometry.exists_singularPointBlowupChain_isGorenstein_of_isDualizingComplex`: the
  assembly, given that `f^!(ω_R)` is dualizing on the blowup of each local ring `R` of the kind
  above.

## References

* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
* [Stacks Project, Tag 0BFQ](https://stacks.math.columbia.edu/tag/0BFQ)
* [Stacks Project, Tag 0AWS](https://stacks.math.columbia.edu/tag/0AWS)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry

universe u

namespace Dualizing

section

attribute [local instance 10000] HasDerivedCategory.standard

/-- **A Cohen–Macaulay Noetherian local ring with a dualizing complex has a dualizing module**
([Stacks, Tag 0AWS]): the dualizing complex has cohomology in a single degree `d`, so it is that
cohomology module placed in degree `d`. -/
theorem exists_isDualizingRingModule_of_isMaximalCohenMacaulay {A : Type u} [CommRing A]
    [IsNoetherianRing A] [IsLocalRing A] (hCM : Module.IsMaximalCohenMacaulay A A)
    (K : DerivedCategory (ModuleCat.{u} A)) (hK : IsDualizingComplex K) :
    ∃ (ω : Type u) (_ : AddCommGroup ω) (_ : Module A ω),
      Stacks.Duality.IsDualizingRingModule A ω := by
  obtain ⟨d, hd⟩ := exists_homology_concentrated_of_isMaximalCohenMacaulay_self.{u, 0} K hK hCM
  let M := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) d).obj K
  let e := (DerivedCategory.nonempty_iso_singleFunctor_homologyFunctor_of_isZero K d hd).some
  exact ⟨M, inferInstance, inferInstance, hK.finiteCohomology d, d, isDualizingComplex_of_iso e hK⟩

end

end Dualizing

namespace Stacks.Duality

variable {X : Scheme.{u}}

/-- **On a Gorenstein scheme whose rings of sections over affine opens have dualizing complexes,
the structure sheaf is a dualizing complex.** At an affine open `U` the model is `Γ(X, U)` in
degree zero, which is dualizing by [Stacks, Tag 0DW9 (2)] applied to the Gorenstein ring `Γ(X, U)`
(`Stacks.Duality.isGorensteinRing_sections`). This is the argument of [Stacks, Tag 0BFQ] (2),
`Stacks.Duality.exists_isDualizingComplex_iff_unit`, with the dualizing complexes over the affine
opens supplied directly rather than by a dualizing complex on `X`. -/
theorem isDualizingComplex_unit_of_forall_affine [AlgebraicGeometry.IsGorenstein X]
    (h : ∀ (U : X.Opens) (hU : IsAffineOpen U),
      letI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
      letI := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
      ∃ K : DerivedCategory (ModuleCat.{u} Γ(X, U)), Dualizing.IsDualizingComplex K) :
    letI := HasDerivedCategory.standard X.Modules
    IsDualizingComplex ((DerivedCategory.singleFunctor X.Modules 0).obj
      (SheafOfModules.unit X.ringCatSheaf)) := by
  let := HasDerivedCategory.standard X.Modules
  intro U hU
  let : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let := HasDerivedCategory.standard U.toScheme.Modules
  let := HasDerivedCategory.standard (ModuleCat.{u} Γ(X, U))
  refine ⟨(DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U)) 0).obj
    (ModuleCat.of Γ(X, U) Γ(X, U)),
    (Dualizing.exists_isDualizingComplex_iff_regularModule.{u, u} Γ(X, U)
      (isGorensteinRing_sections U hU)).mp (h U hU), ⟨?_⟩⟩
  refine ((Scheme.Modules.restrictFunctor U.ι).mapDerivedCategorySingleFunctor 0).app _ ≪≫
    (DerivedCategory.singleFunctor U.toScheme.Modules 0).mapIso
      (Scheme.Modules.restrictUnitIso U.ι ≪≫
        (Scheme.Modules.restrictUnitIso hU.isoSpec.hom).symm ≪≫
        (Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapIso
          (tildeSelf (R := Γ(X, U))).symm) ≪≫
    (((tilde.functor Γ(X, U) ⋙
      Scheme.Modules.restrictFunctor hU.isoSpec.hom).mapDerivedCategorySingleFunctor 0).app _).symm

end Stacks.Duality

namespace AlgebraicGeometry

/-- **The structure sheaf of a Gorenstein scheme locally of finite type over a Noetherian ring
with a dualizing complex is an invertible dualizing module.** The rings of sections over affine
opens are of finite type over the base, so they have dualizing complexes ([Stacks, Tag 0A7K]), and
`Stacks.Duality.isDualizingComplex_unit_of_forall_affine` applies. -/
theorem exists_isDualizingModule_isInvertible_of_isGorenstein (B : Type u) [CommRing B]
    [IsNoetherianRing B]
    (hB : letI := HasDerivedCategory.standard (ModuleCat.{u} B)
      ∃ K : DerivedCategory (ModuleCat.{u} B), Dualizing.IsDualizingComplex K)
    {X : Scheme.{u}} [IsGorenstein X] (f : X ⟶ Spec (.of B)) [LocallyOfFiniteType f] :
    ∃ ω : X.Modules, Stacks.Duality.IsDualizingModule ω ∧
      AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ω := by
  let := HasDerivedCategory.standard (ModuleCat.{u} B)
  obtain ⟨K, hK⟩ := hB
  refine ⟨SheafOfModules.unit X.ringCatSheaf,
    ⟨Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit, 0,
      Stacks.Duality.isDualizingComplex_unit_of_forall_affine fun V hV => ?_⟩,
    isInvertible_unit X⟩
  let φ : B →+* Γ(X, V) := ((Scheme.ΓSpecIso (.of B)).inv ≫ f.appLE ⊤ V le_top).hom
  have hφ : φ.FiniteType := by
    have h₁ : (f.appLE ⊤ V le_top).hom.FiniteType :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f inferInstance
        ⟨⊤, isAffineOpen_top _⟩ ⟨V, hV⟩ le_top
    exact h₁.comp (RingHom.FiniteType.of_surjective _
      (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of B)).inv).2)
  let : Algebra B Γ(X, V) := φ.toAlgebra
  have hft : Algebra.FiniteType B Γ(X, V) := hφ
  obtain ⟨_, L, hL⟩ := Dualizing.exists_isDualizingComplex_of_isEssentiallyOfFiniteType
    (Dualizing.isEssentiallyOfFiniteType_of_finiteType hft) K hK
  exact ⟨L, hL⟩

/-- Over a domain `A`, the map `A ⟶ 𝒪_{X,x}` of an integral scheme dominating `Spec(A)` by a
quasi-compact morphism is injective: it is the injective map `A ⟶ Γ(X, 𝒪_X)` followed by a germ
map of an integral scheme. -/
theorem stalkAlgebraOfSpec_injective (A : Type u) [CommRing A] [IsDomain A] {X : Scheme.{u}}
    [IsIntegral X] (f : X ⟶ Spec (.of A)) [IsDominant f] [QuasiCompact f] (x : X) :
    Function.Injective (stalkAlgebraOfSpec A f x) := by
  have : IsSchemeTheoreticallyDominant f := .of_isDominant f
  exact (germ_injective_of_isIntegral X (U := ⊤) x trivial).comp ((f.app_injective ⊤).comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of A)).inv).1)

/-- A sequence of blowups in singular closed points with normal stages, starting from `Spec(A)` for
a normal Nagata domain `A` of dimension two, is a modification. -/
private theorem isModification_of_singularPointBlowupChain_spec (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsNormalDomain A] (hN : IsNagataRing A) (hdim : ringKrullDim A = 2)
    {Y : Scheme.{u}} {f : Y ⟶ Spec (.of A)}
    (hchain : SingularPointBlowupChain IsNormal (Spec (.of A)) Y f) : IsModification f := by
  have : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  refine isModification_of_singularPointBlowupChain (fun _ h => h)
    (isNagataScheme_spec_of_isNagataRing _ hN) ?_ hchain
  change topologicalKrullDim (PrimeSpectrum A) = 2
  rw [PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim, hdim]

/-- **[Stacks, Tag 0BBV], given `f^!(ω_R)` dualizing on the blowups of local rings.** Let `A` be a
local normal Nagata domain of dimension two defining a rational singularity and having a dualizing
complex. Given (`hE1`) that `f^!(ω_R)` is a dualizing complex on the blowup of every ring `R` of
Situation [Stacks, Tag 0B4W] in its maximal ideal, there is a sequence of blowups in singular
closed points with normal stages ending in a Gorenstein scheme. -/
theorem exists_singularPointBlowupChain_isGorenstein_of_isDualizingComplex
    (hE1 : ∀ (S : RationalSingularitySituation.{u}) (ωA : ModuleCat.{u} S.A),
      Stacks.Duality.IsDualizingRingModule S.A ωA →
        Stacks.Duality.IsDualizingComplex
          ((rationalSingularitySituationBlowUp S).relativeDualizingComplex ωA).obj)
    (A : Type u) [CommRing A] [IsNoetherianRing A] [IsLocalRing A] [IsNormalDomain A]
    (hN : IsNagataRing A) (hdim : ringKrullDim A = 2) (hrat : DefinesRationalSingularity A)
    (hdual : letI := HasDerivedCategory.standard (ModuleCat.{u} A)
      ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) :
    ∃ (Y : Scheme.{u}) (f : Y ⟶ Spec (.of A)),
      SingularPointBlowupChain IsNormal (Spec (.of A)) Y f ∧ IsGorenstein Y := by
  -- a dualizing module `ω_A`, isomorphic to a nonzero ideal `J`
  have hCM : Module.IsMaximalCohenMacaulay A A :=
    (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay A).mp
      (isCohenMacaulayLocalRing_of_isNormalRing_of_ringKrullDim_eq_two
        (IsNormalRing.of_isIntegrallyClosed A) hdim)
  let := HasDerivedCategory.standard (ModuleCat.{u} A)
  obtain ⟨K, hK⟩ := hdual
  obtain ⟨ω, _, _, hω⟩ := Dualizing.exists_isDualizingRingModule_of_isMaximalCohenMacaulay hCM K hK
  obtain ⟨J, hJ, ⟨eJ⟩⟩ := Dualizing.exists_linearEquiv_ideal_of_isDualizingRingModule hω
  -- the sequence of blowups along which `J` becomes principal at the singular points
  obtain ⟨Y, f, hchain, hprinc⟩ := exists_singularPointBlowupChain_principal A hN hdim hrat J hJ
  have : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  have hf := isModification_of_singularPointBlowupChain_spec A hN hdim hchain
  have : IsIntegral Y := hf.source_isIntegral
  have : IsProper f := hf.isProper
  have : IsDominant f := hf.isBirational.isDominant
  have : IsLocallyNoetherian (Spec (.of A)) := isLocallyNoetherian_Spec.mpr inferInstance
  have : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  exact ⟨Y, f, hchain, isGorenstein_of_dualizingQuotientAt A ω f
    (stalkAlgebraOfSpec_injective A f) J hJ eJ hprinc fun y _ =>
      dualizingQuotientAt_of_singularPointBlowupChain_of_local A hN hdim hrat ω hω
        (fun R _ _ _ _ hNR hdimR hratR hnotR N _ _ hN' hln z =>
          dualizingQuotientAt_blowUp_maximalIdealSheaf_of_isDualizingComplex hE1 R hNR hdimR
            hratR hnotR N hN' hln z) hchain y⟩

/-- **[Stacks, Tag 0BBV] in the form of the source, given `f^!(ω_R)` dualizing on the blowups of
local rings.** For `A` a local normal Nagata domain of dimension two defining a rational
singularity and having a dualizing complex, there is a finite sequence of blowups in singular
closed points `X = Xₙ ⟶ … ⟶ X₀ = Spec(A)` with every `Xᵢ` normal, such that `X` has an invertible
dualizing module. -/
theorem exists_singularPointBlowupChain_isDualizingModule_isInvertible_of_isDualizingComplex
    (hE1 : ∀ (S : RationalSingularitySituation.{u}) (ωA : ModuleCat.{u} S.A),
      Stacks.Duality.IsDualizingRingModule S.A ωA →
        Stacks.Duality.IsDualizingComplex
          ((rationalSingularitySituationBlowUp S).relativeDualizingComplex ωA).obj)
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNormalDomain A]
    (hN : IsNagataRing A) (hdim : ringKrullDim A = 2) (hrat : DefinesRationalSingularity A)
    (hdual : letI : IsNoetherianRing A := hN.1
      letI := HasDerivedCategory.standard (ModuleCat.{u} A)
      ∃ K : DerivedCategory (ModuleCat.{u} A), Dualizing.IsDualizingComplex K) :
    ∃ (X : Scheme.{u}) (f : X ⟶ Spec (.of A)),
      SingularPointBlowupChain IsNormal (Spec (.of A)) X f ∧
        ∃ _ : IsLocallyNoetherian X, ∃ ω : X.Modules, Stacks.Duality.IsDualizingModule ω ∧
          AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 ω := by
  let : IsNoetherianRing A := hN.1
  obtain ⟨X, f, hchain, hgor⟩ :=
    exists_singularPointBlowupChain_isGorenstein_of_isDualizingComplex hE1 A hN hdim hrat hdual
  have : IsProper f := (isModification_of_singularPointBlowupChain_spec A hN hdim hchain).isProper
  exact ⟨X, f, hchain, inferInstance,
    exists_isDualizingModule_isInvertible_of_isGorenstein A hdual f⟩

end AlgebraicGeometry

end
