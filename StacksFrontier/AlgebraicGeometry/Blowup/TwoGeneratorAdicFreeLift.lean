module

public import StacksFrontier.AlgebraicGeometry.FormalFunctions.AdicGradedPieceVanishing
public import StacksFrontier.AlgebraicGeometry.Blowup.TwoGeneratorNoetherianModification
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.FullOnFree
public import StacksFrontier.AlgebraicGeometry.Flatness.Devissage.Complete.Transport
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.RankFromBasis
public import StacksFrontier.AlgebraicGeometry.FormalFunctions.IdealPowerQuotientSections
public import StacksFrontier.AlgebraicGeometry.AmpleSectionConnected.SectionsVanishing

/-!
# The free presentation produced by the `ℐ`-adic induction

Let `A` be a **Noetherian** ring and `f₁, f₂ ∈ A`, the data of [Stacks, Example 0EVH] after the
Noetherian reduction of [Stacks, Tag 0B8W], and let
`b : X' = Proj (A[T₀,T₁]/(f₂T₀-f₁T₁)) ⟶ Spec A` be the modification of the two-generator almost
blowup square, with exceptional line `i : E ⟶ X'` and `𝓘 = (f₁,f₂) 𝒪_{X'}` its ideal sheaf.

This file assembles the step of the essential surjectivity half of [Stacks, Tag 0EXD] which the
source states as: *given a finite locally free `𝒢` on `X'` whose restriction `i^*𝒢` is free of
rank `r`, there is a map `α : 𝒪_{X'}^{⊕r} ⟶ 𝒢` which is an isomorphism in a neighbourhood of
`E`.*  The sections of `α` are the lifts, supplied by the `ℐ`-adic induction
`Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_twoGenerator`, of a free basis
of `i^*𝒢`.

## Main results

* `AlgebraicGeometry.surjective_moduleGlobalSections_map_of_surjective_rightDerivedZero`: the
  degree-zero derived global sections functor and global sections send the same morphisms to
  surjections.
* `AlgebraicGeometry.surjective_sectionsMap_of_surjective_moduleGlobalSections_map`: a morphism
  surjective on the sections over `⊤` is surjective on compatible families of sections.
* `Stacks.Algebraization.pullback_map_eq_of_comp_cokernel_π_eq`: **the [Stacks, Tag 0EL1]
  comparison identifies lifts with their restrictions** — a morphism lifting, through that
  comparison, a morphism on the closed subscheme restricts to that morphism.
* `Stacks.AlmostBlowUp.ker_exceptionalToModification_eq_baseIdealSheaf_pow_one`: the ideal sheaf
  of the exceptional line is the first power of `𝓘`, the shape [Stacks, Tag 0EL1] consumes.
* `Stacks.AlmostBlowUp.exists_epi_free_idealPowerQuotient_of_pullback_iso_free`: **the quotient
  `𝒢 / 𝓘 𝒢` is the target of an epimorphism from `𝒪_{X'}^{⊕r}` which stays invertible after
  `i^*`** when `i^*𝒢` is free of rank `r` — the global generation the `ℐ`-adic induction needs,
  obtained with no cohomological input at all.  The epimorphism is returned together with the
  formula building it out of the given trivialisation.
* `Stacks.AlmostBlowUp.exists_hom_free_isIso_near_exceptional`: **the map `α` exists**, restricts
  along `i^*` to the given trivialisation of `i^*𝒢` (hence is an isomorphism after `i^*`), and is
  an isomorphism over an open neighbourhood of `E`.

## Implementation notes

The quotient by the exceptional ideal sheaf is the direct image of the restriction,
`Stacks.Algebraization.idealQuotientPushforwardIso` — [Stacks, Tag 0EL1] for an arbitrary closed
immersion whose ideal sheaf is `𝓘 ^ n` — at `n = 1`.  Applying it at `𝒢` *and* at the free module
`𝒪_{X'}^{⊕r}` produces an isomorphism `θ : 𝒪_{X'}^{⊕r} / 𝓘 𝒪_{X'}^{⊕r} ≅ 𝒢 / 𝓘 𝒢` out of the
given `i^*𝒢 ≅ 𝒪_E^{⊕r}`, because the pullback of a free module is free
(`AlgebraicGeometry.Scheme.Modules.pullbackFreeIso`).  The composite
`β = (𝒪_{X'}^{⊕r} ⟶ 𝒪_{X'}^{⊕r} / 𝓘 𝒪_{X'}^{⊕r}) ≫ θ` is therefore an epimorphism, which is
already the global generation of `𝒢 / 𝓘 𝒢`, and it is `β` that gets lifted.

**No separate passage through `H⁰(E, i^*𝒢)` is needed.**  Reading the quotient's global sections
as sections on the exceptional line and choosing a basis there would need the identification
`H⁰(X', i_* N) ≅ H⁰(E, N)`; instead `β` is written down at sheaf level on `X'` and the only
cohomological input is the surjectivity of `H⁰(X', 𝒢) ⟶ H⁰(X', 𝒢 / 𝓘 𝒢)`.  Equally, the
invertibility of `i^*α` needs no counit: `i^*` inverts *both* quotient projections, by
`Stacks.Algebraization.isIso_pullback_map_cokernel_π_of_ker`, so `i^*β` is invertible outright
and `i^*α` is obtained from it by cancelling `i^*` of the projection at `𝒢`.

The lift itself is Mathlib's universal property of a free sheaf of modules,
`SheafOfModules.freeHomEquiv`, in the packaged form
`SheafOfModules.exists_comp_eq_of_surjective_sectionsMap`.  That consumes surjectivity on
`SheafOfModules.sections`, i.e. on compatible families, whereas the `ℐ`-adic induction delivers
surjectivity of `R⁰Γ(X', -)` applied to the projection; the two bridges above cross that gap,
through `CategoryTheory.Functor.rightDerivedZeroIsoSelf` and through
`Stacks.SheafOfModules.FiniteTypeKernel.sectionsEquivOfTerminal` at the terminal open.

Coherence of `𝒢` and of the free module — which both the `ℐ`-adic induction and
`Stacks.AlmostBlowUp.exists_isIso_restrictFunctor_map_near_exceptional` need — is instance search
from `Stacks.AlmostBlowUp.isLocallyNoetherian_proj_modificationGrading` together with finite local
freeness, by [Stacks, Tag 01XZ]; this is the reason the Noetherian reduction has to be performed
before this step and not after.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry

/-- **Global sections and their degree-zero derived functor detect the same surjections.**  The
canonical identification `R⁰Γ(X, -) ≅ Γ(X, -)` is natural, so a morphism which `R⁰Γ(X, -)` sends
to a surjection is sent to a surjection by `Γ(X, -)`. -/
theorem surjective_moduleGlobalSections_map_of_surjective_rightDerivedZero {X : Scheme.{u}}
    {M N : X.Modules} (φ : M ⟶ N)
    (h : Function.Surjective (((moduleGlobalSections X).rightDerived 0).map φ).hom) :
    Function.Surjective ((moduleGlobalSections X).map φ).hom := by
  intro y
  obtain ⟨z, hz⟩ := (ConcreteCategory.bijective_of_isIso
    ((Stacks.Cohomology.FormalFunctions.moduleGlobalSectionsRightDerivedZeroIso X).hom.app
      N)).surjective y
  obtain ⟨x, hx⟩ := h z
  refine ⟨((Stacks.Cohomology.FormalFunctions.moduleGlobalSectionsRightDerivedZeroIso
    X).hom.app M).hom x, ?_⟩
  have hval := LinearMap.congr_fun (ModuleCat.hom_ext_iff.1
    ((Stacks.Cohomology.FormalFunctions.moduleGlobalSectionsRightDerivedZeroIso X).hom.naturality
      φ)) x
  simp only [ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply] at hval
  rw [hx] at hval
  exact hval.symm.trans hz

/-- **A morphism surjective on the sections over `⊤` is surjective on global sections.**  A
compatible family of sections of a sheaf of modules on a scheme is determined by its value over
`⊤`, the terminal open. -/
theorem surjective_sectionsMap_of_surjective_moduleGlobalSections_map {X : Scheme.{u}}
    {M N : X.Modules} (φ : M ⟶ N)
    (h : Function.Surjective ((moduleGlobalSections X).map φ).hom) :
    Function.Surjective (SheafOfModules.sectionsMap φ) := by
  intro t
  obtain ⟨x, hx⟩ := h (Stacks.AmpleSectionConnected.sectionsEquivEvalTop X N t)
  obtain ⟨s, hs⟩ := (Stacks.AmpleSectionConnected.sectionsEquivEvalTop X M).surjective x
  exact ⟨s, (Stacks.AmpleSectionConnected.sectionsEquivEvalTop X N).injective
    ((congrArg ((moduleGlobalSections X).map φ).hom hs).trans hx)⟩

end AlgebraicGeometry

namespace Stacks.Algebraization

/-- **The [Stacks, Tag 0EL1] comparison identifies lifts with their restrictions.**  Let
`v : V ⟶ X` be a closed immersion whose ideal sheaf is `I ^ n` and let `L` and `F` be
quasi-coherent modules on `X`.  [Stacks, Tag 0EL1]
(`Stacks.Algebraization.idealQuotientPushforwardIso`) presents the quotients `L / I ^ n L` and
`F / I ^ n F` as the direct images `v_* v^* L` and `v_* v^* F`, so a morphism `ψ : v^* L ⟶ v^* F`
on the closed subscheme becomes a morphism of those quotients.  If `α : L ⟶ F` is a lift of that
morphism — meaning that `α` followed by the quotient projection of `F` is the quotient projection
of `L` followed by it — then the restriction of `α` is `ψ`, that is `v^* α = ψ`.  In other words
the comparison of [Stacks, Tag 0EL1] identifies lifts with their restrictions.

The hypothesis is exactly the naturality square `α ≫ η_F = η_L ≫ v_* ψ` of the unit `η` of
`v^* ⊣ v_*`, because the comparison is normalized by `η`
(`Stacks.Algebraization.idealQuotientPushforwardMap_π`); applying `v^*` to that square and
composing with the counit turns it into `v^* α = ψ`, by the triangle identity at `L` and at `F`.

See [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1). -/
theorem pullback_map_eq_of_comp_cokernel_π_eq {X : Scheme.{u}} (I : X.IdealSheafData) (n : ℕ)
    {L F : X.Modules} [L.IsQuasicoherent] [F.IsQuasicoherent] {V : Scheme.{u}} (v : V ⟶ X)
    [IsClosedImmersion v] (hv : v.ker = I ^ n)
    (ψ : (Scheme.Modules.pullback v).obj L ⟶ (Scheme.Modules.pullback v).obj F) (α : L ⟶ F)
    (hα : α ≫ cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι =
      cokernel.π (C := X.Modules) (idealPowerMultiple I n L).ι ≫
        (idealQuotientPushforwardIso I n L v hv).hom ≫
          (Scheme.Modules.pushforward v).map ψ ≫
            (idealQuotientPushforwardIso I n F v hv).inv) :
    (Scheme.Modules.pullback v).map α = ψ := by
  have hπF : cokernel.π (C := X.Modules) (idealPowerMultiple I n F).ι ≫
      (idealQuotientPushforwardIso I n F v hv).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction v).unit.app F :=
    idealQuotientPushforwardMap_π I n F v hv
  have hπL : cokernel.π (C := X.Modules) (idealPowerMultiple I n L).ι ≫
      (idealQuotientPushforwardIso I n L v hv).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction v).unit.app L :=
    idealQuotientPushforwardMap_π I n L v hv
  have hunit : α ≫ (Scheme.Modules.pullbackPushforwardAdjunction v).unit.app F =
      (Scheme.Modules.pullbackPushforwardAdjunction v).unit.app L ≫
        (Scheme.Modules.pushforward v).map ψ := by
    rw [← hπF, ← hπL, ← Category.assoc, hα]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  apply ((Scheme.Modules.pullbackPushforwardAdjunction v).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Adjunction.unit_naturality, hunit]

end Stacks.Algebraization

namespace Stacks.AlmostBlowUp

open Stacks.Algebraization Stacks.Cohomology.FormalFunctions

attribute [local instance] MvPolynomial.gradedAlgebra modificationSubmoduleGraded

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

variable (A : Type u) [CommRing A] (f₁ f₂ : A)

/-- **The ideal sheaf of the exceptional line is the first power of the extension of the
centre's ideal to the modification.**  This is the shape in which [Stacks, Tag 0EL1], stated for
a closed immersion whose ideal sheaf is an `n`-th power, consumes
`Stacks.AlmostBlowUp.ker_exceptionalToModification`. -/
theorem ker_exceptionalToModification_eq_baseIdealSheaf_pow_one :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    (exceptionalToModification A f₁ f₂).ker =
      baseIdealSheaf A (centerIdeal A f₁ f₂) (modificationToBase A f₁ f₂) ^ 1 := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  rw [pow_one]
  exact (ker_exceptionalToModification A f₁ f₂).trans
    (comap_centerIdealSheaf_eq_baseIdealSheaf A f₁ f₂)

variable [IsNoetherianRing A]

/-- The free module of rank `r` and a finite locally free `G` on the modification are
finite locally free and quasi-coherent, via local Noetherianity. -/
private theorem free_isFiniteLocallyFree_and_isQuasicoherent (r : ℕ)
    {G : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Modules}
    (hG : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
        (_root_.SheafOfModules.free
          (R := (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf)
          (ULift.{u} (Fin r))) ∧
      G.IsQuasicoherent ∧
        (_root_.SheafOfModules.free
          (R := (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf)
          (ULift.{u} (Fin r))).IsQuasicoherent := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have hNoeth := isLocallyNoetherian_proj_modificationGrading A f₁ f₂
  have hGfl := hG
  have hLfl : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u}
      (_root_.SheafOfModules.free
        (R := (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf)
        (ULift.{u} (Fin r))) :=
    AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
      (_root_.SheafOfModules.free
        (R := (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf)
        (ULift.{u} (Fin r))) r
      (hM := AlgebraicGeometry.SheafOfModules.isFiniteLocallyFreeOfRank_free.{u, u, u} r)
  exact ⟨hLfl,
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent G).1,
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent _).1⟩

/-- **The quotient of `𝒢` by the exceptional ideal sheaf is generated by `r` global sections, and
stays invertible after restriction to the exceptional line**, as soon as `i^*𝒢` is free of rank
`r`.

Both `𝒢 / 𝓘 𝒢` and `𝒪_{X'}^{⊕r} / 𝓘 𝒪_{X'}^{⊕r}` are the direct image along `i` of the
restriction to the exceptional line, by [Stacks, Tag 0EL1]
(`Stacks.Algebraization.idealQuotientPushforwardIso` at `n = 1`), and the restriction of
`𝒪_{X'}^{⊕r}` is `𝒪_E^{⊕r}`; so the hypothesis makes the two quotients isomorphic, and `β` is
the quotient projection of the free module followed by that isomorphism.  It is therefore an
epimorphism — which is the global generation the `ℐ`-adic induction asks for — and `i^*β` is
invertible because `i^*` inverts the quotient projection
(`Stacks.Algebraization.isIso_pullback_map_cokernel_π_of_ker`). -/
theorem exists_epi_free_idealPowerQuotient_of_pullback_iso_free (r : ℕ)
    {G : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Modules}
    (hG : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G)
    (e : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).obj G ≅
        _root_.SheafOfModules.free (ULift.{u} (Fin r))) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∃ β : (_root_.SheafOfModules.free
          (R := (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf)
          (ULift.{u} (Fin r))) ⟶
        idealPowerQuotient
          (baseIdealSheaf A (centerIdeal A f₁ f₂) (modificationToBase A f₁ f₂)) 1 G,
      Epi β ∧
        IsIso ((Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).map β) ∧
          β = cokernel.π (C := _) (idealPowerMultiple
                (baseIdealSheaf A (centerIdeal A f₁ f₂) (modificationToBase A f₁ f₂)) 1
                (_root_.SheafOfModules.free (ULift.{u} (Fin r)))).ι ≫
              (idealQuotientPushforwardIso _ 1 _ (exceptionalToModification A f₁ f₂)
                  (ker_exceptionalToModification_eq_baseIdealSheaf_pow_one A f₁ f₂)).hom ≫
                (Scheme.Modules.pushforward (exceptionalToModification A f₁ f₂)).map
                    ((Scheme.Modules.pullbackFreeIso (exceptionalToModification A f₁ f₂)
                      (ULift.{u} (Fin r)) ≪≫ e.symm).hom) ≫
                  (idealQuotientPushforwardIso _ 1 G (exceptionalToModification A f₁ f₂)
                    (ker_exceptionalToModification_eq_baseIdealSheaf_pow_one A f₁ f₂)).inv := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have hNoeth := isLocallyNoetherian_proj_modificationGrading A f₁ f₂
  have hGfl := hG
  obtain ⟨hLfl, hGq, hLq⟩ := free_isFiniteLocallyFree_and_isQuasicoherent A f₁ f₂ r hG
  have hker := ker_exceptionalToModification_eq_baseIdealSheaf_pow_one A f₁ f₂
  let θ : idealPowerQuotient
      (baseIdealSheaf A (centerIdeal A f₁ f₂) (modificationToBase A f₁ f₂)) 1
        (_root_.SheafOfModules.free
          (R := (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf)
          (ULift.{u} (Fin r))) ≅
      idealPowerQuotient
        (baseIdealSheaf A (centerIdeal A f₁ f₂) (modificationToBase A f₁ f₂)) 1 G :=
    idealQuotientPushforwardIso _ 1 _ (exceptionalToModification A f₁ f₂) hker ≪≫
      (Scheme.Modules.pushforward (exceptionalToModification A f₁ f₂)).mapIso
        (Scheme.Modules.pullbackFreeIso (exceptionalToModification A f₁ f₂)
          (ULift.{u} (Fin r)) ≪≫ e.symm) ≪≫
      (idealQuotientPushforwardIso _ 1 G (exceptionalToModification A f₁ f₂) hker).symm
  refine ⟨cokernel.π (C := _)
      (idealPowerMultiple (baseIdealSheaf A (centerIdeal A f₁ f₂)
        (modificationToBase A f₁ f₂)) 1 (_root_.SheafOfModules.free (ULift.{u} (Fin r)))).ι ≫
    θ.hom, epi_comp' inferInstance (⟨θ.inv, θ.inv_hom_id⟩ : SplitEpi θ.hom).epi, ?_, ?_⟩
  · exact (Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).isIso_map_comp _ _
      (isIso_pullback_map_cokernel_π_of_ker _ 1 _ (exceptionalToModification A f₁ f₂) hker)
      ((Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).mapIso θ).isIso_hom
  · simp only [θ, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom]
    rfl

/-- **The morphism `α : 𝒪_{X'}^{⊕r} ⟶ 𝒢` of the essential surjectivity half of
[Stacks, Tag 0EXD], and its invertibility near the exceptional line.**

Let `A` be a Noetherian ring, `f₁, f₂ ∈ A`, and let `𝒢` be a finite locally free module on the
modification `X'` of the two-generator almost blowup square whose restriction `i^*𝒢` to the
exceptional line `E` is free of rank `r`.  Then there is a morphism `α : 𝒪_{X'}^{⊕r} ⟶ 𝒢` whose
restriction `i^*α` is an isomorphism and which is an isomorphism over an open neighbourhood
of `E`.

This is the sentence of the source's proof reading "*after shrinking we may assume `ℱ` is free,
and then the sections of `𝒢` lifting a basis of `𝒢|_E` define `α : 𝒪_{X'}^{⊕r} ⟶ 𝒢` which is an
isomorphism in a neighbourhood of `E`*".  The sections are produced by the `ℐ`-adic induction
`Stacks.Cohomology.FormalFunctions.surjective_adicCohomologyProj_twoGenerator` at `n = 1`, whose
two hypotheses are discharged here: coherence of `𝒢` from local Noetherianity of the modification
and finite local freeness, and global generation of `𝒢 / 𝓘 𝒢` from
`Stacks.AlmostBlowUp.exists_epi_free_idealPowerQuotient_of_pullback_iso_free`.  The neighbourhood
comes from `Stacks.AlmostBlowUp.exists_isIso_restrictFunctor_map_near_exceptional`.

The restriction `i^*α` is not merely invertible but is the given trivialisation: it is the
identification `i^*𝒪_{X'}^{⊕r} ≅ 𝒪_E^{⊕r}` followed by `e⁻¹`.  Indeed `α` lifts the morphism of
quotients that `e` defines through the [Stacks, Tag 0EL1] comparison, and
`Stacks.Algebraization.pullback_map_eq_of_comp_cokernel_π_eq` says that such a lift restricts to
the morphism it lifts. -/
theorem exists_hom_free_isIso_near_exceptional (r : ℕ)
    {G : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Modules}
    (hG : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} G)
    (e : letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
      (Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).obj G ≅
        _root_.SheafOfModules.free (ULift.{u} (Fin r))) :
    letI := (twoGeneratorSquare A f₁ f₂).modificationGraded
    ∃ α : (_root_.SheafOfModules.free
          (R := (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).ringCatSheaf)
          (ULift.{u} (Fin r))) ⟶ G,
      IsIso ((Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).map α) ∧
        (Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).map α =
            (Scheme.Modules.pullbackFreeIso (exceptionalToModification A f₁ f₂)
              (ULift.{u} (Fin r))).hom ≫ e.inv ∧
          ∃ U : (AlgebraicGeometry.Proj (modificationGrading A f₁ f₂)).Opens,
            Set.range (exceptionalToModification A f₁ f₂).base ⊆ (U : Set _) ∧
              IsIso ((Scheme.Modules.restrictFunctor U.ι).map α) := by
  let := (twoGeneratorSquare A f₁ f₂).modificationGraded
  have hNoeth := isLocallyNoetherian_proj_modificationGrading A f₁ f₂
  have hGfl := hG
  obtain ⟨hLfl, hGq, hLq⟩ := free_isFiniteLocallyFree_and_isQuasicoherent A f₁ f₂ r hG
  obtain ⟨β, hβepi, -, hβeq⟩ :=
    exists_epi_free_idealPowerQuotient_of_pullback_iso_free A f₁ f₂ r hG e
  have hQ : (idealPowerQuotient
      (baseIdealSheaf A (centerIdeal A f₁ f₂) (modificationToBase A f₁ f₂)) 1
        G).GeneratingSections :=
    { I := ULift.{u} (Fin r)
      s := (idealPowerQuotient
        (baseIdealSheaf A (centerIdeal A f₁ f₂) (modificationToBase A f₁ f₂)) 1 G).freeHomEquiv β
      epi := by rwa [Equiv.symm_apply_apply] }
  have hGroot : _root_.SheafOfModules.IsCoherent G := inferInstance
  have hGc : Stacks.SheafOfModules.IsCoherent G :=
    ⟨hGroot.isFiniteType, hGroot.kernel_isFiniteType⟩
  have hsec : Function.Surjective (_root_.SheafOfModules.sectionsMap
      (cokernel.π (C := _) (idealPowerMultiple
        (baseIdealSheaf A (centerIdeal A f₁ f₂) (modificationToBase A f₁ f₂)) 1 G).ι)) :=
    AlgebraicGeometry.surjective_sectionsMap_of_surjective_moduleGlobalSections_map _
      (AlgebraicGeometry.surjective_moduleGlobalSections_map_of_surjective_rightDerivedZero
        _ (surjective_adicCohomologyProj_twoGenerator A f₁ f₂ G hGc hQ 1))
  obtain ⟨α, hα⟩ := _root_.SheafOfModules.exists_comp_eq_of_surjective_sectionsMap _ hsec β
  have hαe : (Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).map α =
      (Scheme.Modules.pullbackFreeIso (exceptionalToModification A f₁ f₂)
        (ULift.{u} (Fin r))).hom ≫ e.inv :=
    Stacks.Algebraization.pullback_map_eq_of_comp_cokernel_π_eq
      (baseIdealSheaf A (centerIdeal A f₁ f₂) (modificationToBase A f₁ f₂)) 1
      (exceptionalToModification A f₁ f₂)
      (ker_exceptionalToModification_eq_baseIdealSheaf_pow_one A f₁ f₂)
      ((Scheme.Modules.pullbackFreeIso (exceptionalToModification A f₁ f₂)
        (ULift.{u} (Fin r)) ≪≫ e.symm).hom) α (hα.trans hβeq)
  have hαiso : IsIso ((Scheme.Modules.pullback (exceptionalToModification A f₁ f₂)).map α) := by
    rw [hαe]
    infer_instance
  exact ⟨α, hαiso, hαe,
    exists_isIso_restrictFunctor_map_near_exceptional A f₁ f₂ hLfl hG α hαiso⟩

end Stacks.AlmostBlowUp

end
