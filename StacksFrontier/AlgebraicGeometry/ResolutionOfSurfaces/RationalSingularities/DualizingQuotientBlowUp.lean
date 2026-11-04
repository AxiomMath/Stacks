module

public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.GorensteinOfDualizingQuotient
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.BlowUpNormalizedDualizingGeneration
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.SectionTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkEpiMono
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalDoublePoints.BlowUpCompletedLocalRings
public import StacksFrontier.AlgebraicGeometry.NormalizationBaseChange.Normal

/-!
# The local step of [Stacks, Tag 0BBV]

The proof of [Stacks, Tag 0BBV] follows a sequence of blowups in singular closed points and shows,
at every point `x` of the final scheme lying over singular points only, that the canonical map
`f^*ω_A ⟶ ω_X` is surjective on stalks. The local input at one blowup is [Stacks, Tag 0B64] (3):
for the blowup `X ⟶ Spec(A)` of a non-regular rational surface singularity in its maximal ideal,
`f^*ω_A ⟶ ω_X` is an epimorphism. This file reads that epimorphism on stalks, in the ring-level
form `AlgebraicGeometry.DualizingQuotientAt`: some dualizing module of `𝒪_{X,x}` is a quotient of
`𝒪_{X,x} ⊗_A ω_A`.

## Main results

* `AlgebraicGeometry.exists_surjective_tensor_stalk_of_epi`: an epimorphism `f^*M̃ ⟶ F` gives
  surjections `𝒪_{X,x} ⊗_R M ⟶ F_x`.
* `Stacks.Duality.IsDualizingModule.isDualizingRingModule_stalk`: the stalks of a dualizing
  module are dualizing modules of the local rings.
* `AlgebraicGeometry.dualizingQuotientAt_rationalSingularitySituationBlowUp`: the local step at
  the blowup of Situation [Stacks, Tag 0B4W], given that `f^!(ω_A)` is dualizing.
* `AlgebraicGeometry.dualizingQuotientAt_blowUp_maximalIdealSheaf_of_isDualizingComplex`: the
  same for the blowup of `Spec(A)` in `maximalIdealSheaf A`, in the form consumed by the
  propagation along a chain of blowups,
  `AlgebraicGeometry.dualizingQuotientAt_of_singularPointBlowupChain_of_local`.

## Implementation notes

The existence of the dualizing module `ω_X` normalized relative to `ω_A` is
`RationalSingularitySituation.dualizingNormalizationOfIsDualizingComplex`, which needs that
`f^!(ω_A)` is a dualizing complex ([Stacks, Tag 0AA3] for the blowup). That input is the binder
`hE1` of the last result, quantified over all of Situation [Stacks, Tag 0B4W], so that it can
be discharged once, by the theorem establishing it.

## References

* [Stacks Project, Tag 0BBV](https://stacks.math.columbia.edu/tag/0BBV)
* [Stacks Project, Tag 0B64](https://stacks.math.columbia.edu/tag/0B64)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-- **An epimorphism out of the pullback of `M̃` gives surjections on stalks out of
`𝒪_{X,x} ⊗_R M`.** For `f : X ⟶ Spec(R)` and an epimorphism `φ : f^*M̃ ⟶ F`, the stalk of `f^*M̃`
at `x` is `𝒪_{X,x} ⊗_{𝒪_{Spec R, f x}} M_{f x} = 𝒪_{X,x} ⊗_R M`, and the stalk map of `φ` is
surjective. The ring is a bundled `CommRingCat` so that the `R`-module structure on the stalks of
`M̃` is found by instance search. -/
theorem exists_surjective_tensor_stalk_of_epi {R : CommRingCat.{u}} {X : Scheme.{u}}
    (f : X ⟶ Spec R) (M : ModuleCat.{u} R) (F : X.Modules)
    (φ : (Scheme.Modules.pullback f).obj (tilde M) ⟶ F) (hφ : Epi φ) (x : X) :
    letI := ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra
    letI := Stacks.ModuleStalkSpecialization.stalkModule F x
    ∃ π : X.presheaf.stalk x ⊗[R] M →ₗ[X.presheaf.stalk x] F.presheaf.stalk x,
      Function.Surjective π := by
  let : Algebra R (X.presheaf.stalk x) :=
    ((Scheme.ΓSpecIso R).inv ≫ f.appTop ≫ X.presheaf.germ ⊤ x trivial).hom.toAlgebra
  let := Stacks.ModuleStalkSpecialization.stalkModule F x
  let y : PrimeSpectrum.Top R := f.base x
  let : Algebra R ((Spec R).presheaf.stalk y) := StructureSheaf.stalkAlgebra R y
  have : IsLocalization.AtPrime ((Spec R).presheaf.stalk y) y.asIdeal :=
    StructureSheaf.IsLocalization.to_stalk R y
  let : Algebra ((Spec R).presheaf.stalk y) (X.presheaf.stalk x) :=
    (f.stalkMap x).hom.toAlgebra
  have : IsScalarTower R ((Spec R).presheaf.stalk y) (X.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_eq fun a =>
      (Scheme.Hom.germ_stalkMap_apply f ⊤ x trivial ((Scheme.ΓSpecIso R).inv a)).symm
  have : IsScalarTower R ((Spec R).presheaf.stalk y)
      ((tilde M).presheaf.stalk y) :=
    ⟨fun a r m => by
      rw [Algebra.smul_def, mul_smul]
      rfl⟩
  have hbc : IsBaseChange ((Spec R).presheaf.stalk y) (tilde.toStalk M y).hom :=
    (isLocalizedModule_iff_isBaseChange y.asIdeal.primeCompl _ _).mp inferInstance
  let g₁ : X.presheaf.stalk x ⊗[R] M ≃ₗ[X.presheaf.stalk x]
      X.presheaf.stalk x ⊗[(Spec R).presheaf.stalk y]
        (tilde M).presheaf.stalk y :=
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R ((Spec R).presheaf.stalk y)
        (X.presheaf.stalk x) (X.presheaf.stalk x) M).symm ≪≫ₗ
      LinearEquiv.baseChange _ (X.presheaf.stalk x) _ _ hbc.equiv
  let g₃ := stalkLinearMap ((Scheme.Modules.pullback f).obj (tilde M)) F φ x
  refine ⟨g₃ ∘ₗ (Scheme.Modules.pullbackStalkEquiv f (tilde M) x).symm.toLinearMap ∘ₗ
    g₁.toLinearMap, ?_⟩
  have : @Epi (SheafOfModules X.ringCatSheaf) _ _ _ φ :=
    ⟨fun g₁ g₂ h => hφ.left_cancellation g₁ g₂ h⟩
  have h₃ : Function.Surjective g₃ :=
    Stacks.SheafOfModules.StalkEpiMono.stalk_surjective_of_epi (O := X.ringCatSheaf) φ x
  exact h₃.comp ((Scheme.Modules.pullbackStalkEquiv f (tilde M) x).symm.surjective.comp
    g₁.surjective)

/-- **The stalk of a dualizing module is a dualizing module of the local ring.** It is finite,
the module being coherent, and in degree zero a dualizing complex
(`Stacks.Duality.isDualizingComplex_single_stalk`). -/
theorem _root_.Stacks.Duality.IsDualizingModule.isDualizingRingModule_stalk {X : Scheme.{u}}
    [IsLocallyNoetherian X] {ω : X.Modules} (hω : Stacks.Duality.IsDualizingModule ω) (x : X) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule ω x
    Stacks.Duality.IsDualizingRingModule (X.presheaf.stalk x) (ω.presheaf.stalk x) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule ω x
  let := HasDerivedCategory.standard (ModuleCat.{u} (X.presheaf.stalk x))
  let := HasDerivedCategory.standard X.Modules
  have : ω.IsCoherent := hω.1
  have : ω.IsQuasicoherent := isQuasicoherent_of_isCoherent ω
  obtain ⟨n, hn⟩ := hω.2
  have h := Stacks.Duality.isDualizingComplex_single_stalk ω n hn x
  refine ⟨?_, 0, h⟩
  have := h.finiteCohomology 0
  let e : ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} (X.presheaf.stalk x)) 0).obj
        (ModuleCat.of (X.presheaf.stalk x) (ω.presheaf.stalk x)))) ≃ₗ[X.presheaf.stalk x]
      ω.presheaf.stalk x :=
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{u} (X.presheaf.stalk x)) 0).app
      (ModuleCat.of (X.presheaf.stalk x) (ω.presheaf.stalk x))).toLinearEquiv
  exact Module.Finite.equiv e

/-- **The local step of [Stacks, Tag 0BBV] at the blowup of Situation [Stacks, Tag 0B4W].** With
`A` not regular, let `ω_A` be a dualizing module of `A` such that `f^!(ω_A)` is a dualizing complex
on the blowup `f : X ⟶ Spec(A)` in the maximal ideal. Then at every point `z` of `X` some dualizing
module of `𝒪_{X,z}` is a quotient of `𝒪_{X,z} ⊗_A ω_A`: the stalk at `z` of the dualizing module
`ω_X` normalized relative to `ω_A` ([Stacks, Remark 0B4R]), onto which the canonical map
`f^*ω_A ⟶ ω_X` of [Stacks, Tag 0BBU] is surjective by [Stacks, Tag 0B64] (3). -/
theorem dualizingQuotientAt_rationalSingularitySituationBlowUp
    (S : RationalSingularitySituation.{u}) (hnot : ¬ IsRegularLocalRing S.A)
    (ω : Type u) [AddCommGroup ω] [Module S.A ω] (hω : Stacks.Duality.IsDualizingRingModule S.A ω)
    (hK : Stacks.Duality.IsDualizingComplex
      ((rationalSingularitySituationBlowUp S).relativeDualizingComplex (ModuleCat.of S.A ω)).obj)
    (z : (rationalSingularitySituationBlowUp S).X) :
    @DualizingQuotientAt S.A _ ω _ ‹_› _ _ (rationalSingularitySituationBlowUp S).f z := by
  have hω' : Stacks.Duality.IsDualizingRingModule S.A (ModuleCat.of S.A ω) := hω
  let N := (rationalSingularitySituationBlowUp S).dualizingNormalizationOfIsDualizingComplex hω' hK
  obtain ⟨π, hπ⟩ := exists_surjective_tensor_stalk_of_epi (R := CommRingCat.of S.A)
    (rationalSingularitySituationBlowUp S).f (ModuleCat.of S.A ω) _
    ((rationalSingularitySituationBlowUp S).normalizedPullbackMap hω' N.normalizedIso)
    (BlowUpDualizing.epi_normalizedPullbackMap S hnot (ModuleCat.of S.A ω) hω' _ N) z
  let := Stacks.ModuleStalkSpecialization.stalkModule
    ((rationalSingularitySituationBlowUp S).normalizedDualizingSheaf (ModuleCat.of S.A ω)) z
  exact ⟨_, inferInstance, _, N.isDualizing.isDualizingRingModule_stalk z, π, hπ⟩

/-- **The local step of [Stacks, Tag 0BBV]**, at the blowup of `Spec(A)` in `maximalIdealSheaf A`,
for `A` a local normal Nagata domain of dimension two defining a rational singularity which is not
regular, and `ω` a dualizing module of `A`: at every point `z` of the blowup some dualizing module
of `𝒪_z` is a quotient of `𝒪_z ⊗_A ω`. `hE1` is the input that `f^!(ω_A)` is a dualizing complex
on the blowup ([Stacks, Tag 0AA3] for it), which makes the normalized dualizing module `ω_X` of
[Stacks, Remark 0B4R] exist. The statement is the `hlocal` of
`AlgebraicGeometry.dualizingQuotientAt_of_singularPointBlowupChain_of_local`. -/
theorem dualizingQuotientAt_blowUp_maximalIdealSheaf_of_isDualizingComplex
    (hE1 : ∀ (S : RationalSingularitySituation.{u}) (ωA : ModuleCat.{u} S.A),
      Stacks.Duality.IsDualizingRingModule S.A ωA →
        Stacks.Duality.IsDualizingComplex
          ((rationalSingularitySituationBlowUp S).relativeDualizingComplex ωA).obj)
    (A : Type u) [CommRing A] [IsLocalRing A] [IsNoetherianRing A] [IsNormalDomain A]
    (hN : IsNagataRing A) (hdim : ringKrullDim A = 2) (hrat : DefinesRationalSingularity A)
    (hnot : ¬ IsRegularLocalRing A)
    (ω : Type u) [AddCommGroup ω] [Module A ω] (hω : Stacks.Duality.IsDualizingRingModule A ω)
    (_ : IsLocallyNoetherian (blowUp (maximalIdealSheaf A))) (z : blowUp (maximalIdealSheaf A)) :
    DualizingQuotientAt A ω (blowUpToBase (maximalIdealSheaf A)) z := by
  have : IsNormal (Spec (.of A)) :=
    isNormal_spec_of_isNormalRing (IsNormalRing.of_isIntegrallyClosed A)
  let S := rationalSingularitySituationOfModification A hN hdim hrat (𝟙 (Spec (.of A)))
    (isModification_id _)
  let : Module S.A ω := ‹Module A ω›
  suffices key : ∀ (I : (Spec (.of A)).IdealSheafData) (_ : IsLocallyNoetherian (blowUp I))
      (_ : (Stacks.Blowup.residuePoint A).ker = I) (z : blowUp I),
      DualizingQuotientAt A ω (blowUpToBase I) z from
    key _ ‹_› (ker_residuePoint_eq_ofIdealTop_map A) z
  rintro I _ rfl z
  exact dualizingQuotientAt_rationalSingularitySituationBlowUp S hnot ω hω
    (hE1 S (ModuleCat.of A ω) hω) z

end AlgebraicGeometry

end
