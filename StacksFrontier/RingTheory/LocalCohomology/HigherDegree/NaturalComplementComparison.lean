module

public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.RingTheory.LocalCohomology.BoundedComparison
public import StacksFrontier.RingTheory.LocalCohomology.HigherDegree.CohomologyWithSupportComparison
public import StacksFrontier.RingTheory.LocalCohomology.MinimalPrimeFiltration.ProZero
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The comparison of Stacks 0DWR, natural in the module

Let `A` be a Noetherian ring, let `I ⊆ A` be an ideal, let `X = Spec A`, let `T = V(I)` and let
`U = X ∖ T`. For an `A`-module `M` the long exact cohomology sequence of `T` collapses, by Serre
vanishing on `X`, to isomorphisms `H^p(U, M̃) ≅ H^{p+1}_T(M)` for `p ≥ 1` and to a four-term exact
sequence

`0 ⟶ H⁰_T(M) ⟶ M ⟶ Γ(U, M̃) ⟶ H¹_T(M) ⟶ 0`

in low degrees ([Stacks, Tag 0DWR], [Stacks, Tag 0BK0]). The library records the isomorphisms
one module at a time, as `Nonempty` statements. This file makes both comparisons **natural in
`M`**: the isomorphisms are natural isomorphisms of functors `ModuleCat A ⥤ ModuleCat A`, and the
four maps of the low-degree sequence are natural transformations.

## Main definitions

* `Stacks.Cohomology.LerayDegreewise.rightDerivedCompIsoOfRightAcyclic`: for `F` carrying
  injectives to `G`-acyclic objects and with every object `F`-acyclic,
  `R^n(G ∘ F) ≅ F ∘ R^nG` as functors.
* `Stacks.LocalCohomology.rightDerivedSectionsWithSupportInIso`: Mathlib's right derived functor
  of the `T`-supported sections is local cohomology with support in `T`, as functors.
* `Stacks.LocalCohomologySequence.complementCohomologyBaseFunctor`,
  `Stacks.LocalCohomologySequence.cohomologyWithSupportBaseFunctor`: `M ↦ H^p(U, M̃)` and
  `M ↦ H^p_T(X, M̃)`, as functors to `A`-modules.
* `Stacks.LocalCohomologySequence.complementDelta`: a connecting transformation of the long exact
  sequence of `T`, fixed once and for all.
* `Stacks.LocalCohomologySequence.cohomologyWithSupportBaseFunctorIso`: Stacks 0A6T in every
  degree, as a natural isomorphism.
* `Stacks.LocalCohomologySequence.complementCohomologyBaseFunctorIso`: **Stacks 0DWR above degree
  zero, natural in the module**: `H^p(U, M̃) ≅ H^{p+1}_T(M)` for `p ≥ 1`.
* `Stacks.LocalCohomologySequence.localCohomologyZeroToSelf`,
  `Stacks.LocalCohomologySequence.selfToComplementSections`,
  `Stacks.LocalCohomologySequence.complementSectionsToLocalCohomologyOne`: the three natural maps
  of the four-term sequence in degree zero.

## Main results

* `Stacks.LocalCohomologySequence.mono_localCohomologyZeroToSelf_app`,
  `Stacks.LocalCohomologySequence.exact_lowDegree_natural`,
  `Stacks.LocalCohomologySequence.epi_complementSectionsToLocalCohomologyOne_app`: **Stacks 0DWR in
  degree zero, natural in the module**: the sequence
  `0 ⟶ H⁰_T(M) ⟶ M ⟶ Γ(U, M̃) ⟶ H¹_T(M) ⟶ 0` is exact.
* `Stacks.LocalCohomologySequence.selfToComplementSections_app`: the middle map is the canonical
  map `Stacks.LocalCohomologySequence.toComplementSections`.

## Implementation notes

The objectwise isomorphisms of the library go through the comparison
`Stacks.Cohomology.LerayDegreewise.rightDerivedCompObjIso`, whose only non-natural ingredient is
the identification `RF(M[0]) ≅ F(M)[0]` at an `F`-acyclic object. Here every module is acyclic
for `M ↦ M̃`, so the unit `Stacks.DerivedIndexing.rightDerivedPlusUnitSingle` is a natural
isomorphism and the comparison becomes natural. On the algebraic side the identification of the
bounded-below derived functor with the unbounded one is the natural isomorphism of Stacks 0EF4,
taken by choice from
`Stacks.LocalCohomology.nonempty_derivedSectionsWithSupportInPlus_comp_inclusion_iso`.

The maps of the degree-zero sequence are the maps of the sheaf-theoretic sequence transported
along these natural isomorphisms, so exactness is transported along an isomorphism of composable
arrows.

## References

* [Stacks Project, Tag 0DWR](https://stacks.math.columbia.edu/tag/0DWR)
* [Stacks Project, Tag 0BK0](https://stacks.math.columbia.edu/tag/0BK0)
* [Stacks Project, Tag 0A6T](https://stacks.math.columbia.edu/tag/0A6T)
* [Stacks Project, Tag 0EF4](https://stacks.math.columbia.edu/tag/0EF4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open RingedSpaceModuleAdjunction

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

universe u

namespace Stacks.Cohomology.LerayDegreewise

section Natural

variable {C D E : Type*} [Category* C] [Category* D] [Category* E]
  [Abelian C] [Abelian D] [Abelian E]
  [HasDerivedCategory C] [HasDerivedCategory D] [HasDerivedCategory E]
  [EnoughInjectives C] [EnoughInjectives D]
  (F : C ⥤ D) (G : D ⥤ E) [F.Additive] [G.Additive]

omit [HasDerivedCategory E] [EnoughInjectives D] in
/-- If every object is right acyclic for `F`, the canonical map `(Fℱ)[0] ⟶ RF(ℱ[0])` is a natural
isomorphism. -/
theorem isIso_rightDerivedPlusUnitSingle (hF : ∀ M : C, F.rightAcyclic M) :
    IsIso (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle F) := by
  have : ∀ M : C, IsIso ((Stacks.DerivedIndexing.rightDerivedPlusUnitSingle F).app M) := by
    intro M
    have : IsIso (F.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) := by
      have hdesc := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
        F.rightDerivedFunctorPlus F.rightDerivedFunctorPlusUnith
        (HomotopyCategory.Plus.quasiIso C) _
        ((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
          DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C))).1 inferInstance
      have h : IsIso (((F.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
          DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso C)).app
          ((HomotopyCategory.Plus.singleFunctor C 0).obj M)) := hF M
      rw [← Functor.rightDerived_fac_app F.rightDerivedFunctorPlus
        F.rightDerivedFunctorPlusUnith (HomotopyCategory.Plus.quasiIso C) _ _
        ((HomotopyCategory.Plus.singleFunctor C 0).obj M)] at h
      exact (isIso_comp_right_iff _ _).1 h
    dsimp only [Stacks.DerivedIndexing.rightDerivedPlusUnitSingle, NatTrans.comp_app,
      Functor.whiskerLeft_app, Functor.whiskerRight_app]
    infer_instance
  exact NatIso.isIso_of_isIso_app _

/-- **The degreewise right derived functors of a composite, as functors.** Let `F : 𝒜 ⥤ ℬ` and
`G : ℬ ⥤ 𝒞` be additive functors between abelian categories with `𝒜` and `ℬ` having enough
injectives. If `F` carries every injective object to an object right acyclic for `G`, and every
object of `𝒜` is right acyclic for `F`, then `R^n(G ∘ F) ≅ F ∘ R^nG` naturally, in every degree
`n`. -/
@[sga "4½ Etat_0 4.3.1" "Degreewise consequence"]
def rightDerivedCompIsoOfRightAcyclic (hFG : ∀ I : C, Injective I → G.rightAcyclic (F.obj I))
    (hF : ∀ M : C, F.rightAcyclic M) (n : ℕ) :
    (F ⋙ G).rightDerived n ≅ F ⋙ G.rightDerived n :=
  haveI := isIso_rightDerivedPlusUnitSingle F hF
  Stacks.DerivedIndexing.rightDerivedIso (F ⋙ G) n ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor C 0)
      (Functor.isoWhiskerRight (Stacks.Cohomology.DerivedPushforwardSections.compIso F G hFG)
        (DerivedCategory.Plus.homologyFunctor E (n : ℤ))) ≪≫
    Functor.isoWhiskerRight (asIso (Stacks.DerivedIndexing.rightDerivedPlusUnitSingle F)).symm
      (G.rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.homologyFunctor E (n : ℤ)) ≪≫
    Functor.isoWhiskerLeft F (Stacks.DerivedIndexing.rightDerivedIso G n).symm

end Natural

end Stacks.Cohomology.LerayDegreewise

namespace Stacks.LocalCohomology

/-- **Local cohomology is the classical right derived functor of supported sections, as
functors.** Mathlib's `n`-th right derived functor of the sections with support in `T` is
naturally isomorphic to `M ↦ H^n_T(M)`, the degree-`n` cohomology of the total right derived
functor of sections with support applied to `M` placed in degree zero. The comparison of the two
indexings of right derived functors is followed by the natural identification of Stacks 0EF4
between the bounded-below and the unbounded derived functors. -/
def rightDerivedSectionsWithSupportInIso (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (n : ℕ) :
    (sectionsWithSupportInFunctor.{u, u} A T).rightDerived n ≅
      localCohomologyWithSupportInModuleFunctor.{u, u} A T (n : ℤ) :=
  Stacks.DerivedIndexing.rightDerivedIso (sectionsWithSupportInFunctor.{u, u} A T) n ≪≫
    Functor.isoWhiskerLeft (DerivedCategory.Plus.singleFunctor (ModuleCat.{u} A) 0)
      (Functor.isoWhiskerRight
        (Classical.choice (nonempty_derivedSectionsWithSupportInPlus_comp_inclusion_iso.{u, u} A T))
        (DerivedCategory.homologyFunctor (ModuleCat.{u} A) (n : ℤ)))

end Stacks.LocalCohomology

namespace Stacks.LocalCohomologySequence

open Stacks.Cohomology.SectionsWithSupport
open Stacks.LocalCohomologyTilde

variable {A : CommRingCat.{u}}

/-! ### The terms of the sequence, as functors -/

/-- `M ↦ H^p(Spec A ∖ V(I), M̃)`, as a functor from `A`-modules to `A`-modules. -/
abbrev complementCohomologyBaseFunctor (I : Ideal A) (p : ℕ) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  tildeSheafFunctor A ⋙ complementCohomology I p ⋙ globalToBase A

/-- `M ↦ H^p_{V(I)}(Spec A, M̃)`, as a functor from `A`-modules to `A`-modules. -/
abbrev cohomologyWithSupportBaseFunctor (I : Ideal A) (p : ℕ) :
    ModuleCat.{u} A ⥤ ModuleCat.{u} A :=
  tildeSheafFunctor A ⋙ cohomologyWithSupport I p ⋙ globalToBase A

/-- The value of `complementCohomologyBaseFunctor` at `M` is `complementCohomologyBase`. -/
theorem complementCohomologyBaseFunctor_obj (I : Ideal A) (p : ℕ) (M : ModuleCat.{u} A) :
    (complementCohomologyBaseFunctor I p).obj M = complementCohomologyBase I M p :=
  rfl

/-- The value of `cohomologyWithSupportBaseFunctor` at `M` is `cohomologyWithSupportBase`. -/
theorem cohomologyWithSupportBaseFunctor_obj (I : Ideal A) (p : ℕ) (M : ModuleCat.{u} A) :
    (cohomologyWithSupportBaseFunctor I p).obj M = cohomologyWithSupportBase I M p :=
  rfl

/-- `M ↦ Γ(Spec A, M̃)`, read over `A`, is the identity functor. -/
def ambientCohomologyZeroBaseFunctorIso :
    tildeSheafFunctor A ⋙ ambientCohomology A 0 ⋙ globalToBase A ≅ 𝟭 (ModuleCat.{u} A) :=
  Functor.isoWhiskerLeft (tildeSheafFunctor A)
      (Functor.isoWhiskerRight (ambientCohomologyZeroIso (A := A)) (globalToBase A)) ≪≫
    (globalSectionsTildeIso A).symm

/-! ### The connecting transformation -/

/-- A connecting transformation `H^n(U, -) ⟶ H^{n+1}_{V(I)}(X, -)` of the long exact cohomology
sequence of the closed subset `V(I)` of `X = Spec A`, fixed once and for all. -/
def complementDelta (I : Ideal A) (n : ℕ) :
    complementCohomology I n ⟶ cohomologyWithSupport I (n + 1) :=
  Classical.choose (longExact_rightDerived_sectionsWithSupport (Spec A).toRingedSpace
    (zeroLocusSubset I) (isClosed_zeroLocusSubset I)) n

/-- The long exact cohomology sequence of `V(I)`, with the connecting transformation
`complementDelta`. -/
theorem complementDelta_spec (I : Ideal A) :
    (∀ M : ModuleSheaves (Spec A).toRingedSpace, Mono ((supportInclusion I 0).app M)) ∧
      ∀ (n : ℕ) (M : ModuleSheaves (Spec A).toRingedSpace), (ComposableArrows.mk₅
        ((supportInclusion I n).app M) ((complementRestriction I n).app M)
        ((complementDelta I n).app M) ((supportInclusion I (n + 1)).app M)
        ((complementRestriction I (n + 1)).app M)).Exact :=
  Classical.choose_spec (longExact_rightDerived_sectionsWithSupport (Spec A).toRingedSpace
    (zeroLocusSubset I) (isClosed_zeroLocusSubset I))

/-- The connecting map `H^p(U, M̃) ⟶ H^{p+1}_{V(I)}(X, M̃)` is an isomorphism for `p ≥ 1`: the
terms `H^p(X, M̃)` and `H^{p+1}(X, M̃)` around it vanish by Serre vanishing. -/
theorem isIso_complementDelta_app_tilde (I : Ideal A) (M : ModuleCat.{u} A) (p : ℕ)
    (hp : 1 ≤ p) : IsIso ((complementDelta I p).app (tildeSheaf M)) := by
  have hexact := (complementDelta_spec I).2
  have hmono : Mono ((complementDelta I p).app (tildeSheaf M)) :=
    ((hexact p (tildeSheaf M)).exact' 1 2 3).mono_g
      ((isZero_ambientCohomology_tilde M p hp).eq_zero_of_src _)
  have hepi : Epi ((complementDelta I p).app (tildeSheaf M)) :=
    ((hexact p (tildeSheaf M)).exact' 2 3 4).epi_f
      ((isZero_ambientCohomology_tilde M (p + 1) p.succ_pos).eq_zero_of_tgt _)
  exact isIso_of_mono_of_epi _

/-- The connecting map `H^0(U, M̃) ⟶ H^1_{V(I)}(X, M̃)` is an epimorphism: the next term
`H^1(X, M̃)` vanishes by Serre vanishing. -/
theorem epi_complementDelta_zero_app_tilde (I : Ideal A) (M : ModuleCat.{u} A) :
    Epi ((complementDelta I 0).app (tildeSheaf M)) :=
  (((complementDelta_spec I).2 0 (tildeSheaf M)).exact' 2 3 4).epi_f
    ((isZero_ambientCohomology_tilde M 1 one_pos).eq_zero_of_tgt _)

/-- A three-term sequence `X ⟶ Y ⟶ Z ⟶ W` is exact if both of its short complexes are. -/
private theorem exact_mk₃_of_exact {C : Type*} [Category* C] [Abelian C] {X Y Z W : C}
    (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W) (hfg : f ≫ g = 0) (hgh : g ≫ h = 0)
    (h₁ : (ShortComplex.mk f g hfg).Exact) (h₂ : (ShortComplex.mk g h hgh).Exact) :
    (ComposableArrows.mk₃ f g h).Exact := by
  refine ComposableArrows.Exact.mk (ComposableArrows.IsComplex.mk fun i hi => ?_) fun i hi => ?_
  · match i, hi with
    | 0, _ => exact hfg
    | 1, _ => exact hgh
  · match i, hi with
    | 0, _ => exact h₁
    | 1, _ => exact h₂

/-- The four-term sequence `0 ⟶ H⁰_{V(I)}(X, M̃) ⟶ Γ(X, M̃) ⟶ Γ(U, M̃) ⟶ H¹_{V(I)}(X, M̃)`
with the connecting map `complementDelta` is exact in its middle terms. -/
theorem exact_complementDelta_zero_tilde (I : Ideal A) (M : ModuleCat.{u} A) :
    (ComposableArrows.mk₃ ((supportInclusion I 0).app (tildeSheaf M))
      ((complementRestriction I 0).app (tildeSheaf M))
      ((complementDelta I 0).app (tildeSheaf M))).Exact := by
  have hexact := (complementDelta_spec I).2 0 (tildeSheaf M)
  exact exact_mk₃_of_exact _ _ _ (hexact.toIsComplex.zero 0) (hexact.toIsComplex.zero 1)
    (hexact.exact 0) (hexact.exact 1)

/-- For `p ≥ 1` the connecting transformation is an isomorphism
`H^p(U, M̃) ≅ H^{p+1}_{V(I)}(X, M̃)` of functors of the `A`-module `M`. -/
def complementDeltaTildeIso (I : Ideal A) (p : ℕ) (hp : 1 ≤ p) :
    tildeSheafFunctor A ⋙ complementCohomology I p ≅
      tildeSheafFunctor A ⋙ cohomologyWithSupport I (p + 1) :=
  haveI : ∀ M : ModuleCat.{u} A,
      IsIso ((Functor.whiskerLeft (tildeSheafFunctor A) (complementDelta I p)).app M) :=
    fun M => isIso_complementDelta_app_tilde I M p hp
  haveI := NatIso.isIso_of_isIso_app
    (Functor.whiskerLeft (tildeSheafFunctor A) (complementDelta I p))
  asIso (Functor.whiskerLeft (tildeSheafFunctor A) (complementDelta I p))

/-! ### Cohomology with support of `M̃` is local cohomology of `M`, naturally -/

/-- **Stacks 0A6T in every degree, as a natural isomorphism.** For a Noetherian ring `A` and an
ideal `I`, the cohomology of `Spec A` with support in `V(I)` of `M̃`, read as an `A`-module, is the
local cohomology `H^n_{V(I)}(M)`, naturally in `M`. -/
def cohomologyWithSupportBaseFunctorIso [IsNoetherianRing A] (I : Ideal A) (n : ℕ) :
    cohomologyWithSupportBaseFunctor I n ≅
      Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctor.{u, u} A
        (PrimeSpectrum.zeroLocus (I : Set A)) (n : ℤ) :=
  Functor.isoWhiskerRight
      (Stacks.Cohomology.LerayDegreewise.rightDerivedCompIsoOfRightAcyclic (tildeSheafFunctor A)
        (sectionsWithSupport (Spec A).toRingedSpace (zeroLocusSubset I)
          (isClosed_zeroLocusSubset I))
        (fun E _ =>
          rightAcyclic_sectionsWithSupport_tilde_of_injective I (Ideal.fg_of_isNoetherianRing I) E)
        (fun M => rightAcyclic_tildeSheafFunctor M) n).symm (globalToBase A) ≪≫
    rightDerivedSectionsWithSupportTildeIso (PrimeSpectrum.zeroLocus (I : Set A))
      (isClosed_zeroLocusSubset I) n ≪≫
    Stacks.LocalCohomology.rightDerivedSectionsWithSupportInIso A
      (PrimeSpectrum.zeroLocus (I : Set A)) n

/-! ### Stacks 0DWR above degree zero, natural in the module -/

/-- **Stacks 0DWR above degree zero, natural in the module.** Let `A` be a Noetherian ring, let
`I ⊆ A` be an ideal and let `U = Spec A ∖ V(I)`. For every `p ≥ 1` there is an isomorphism
`H^p(U, M̃) ≅ H^{p+1}_{V(I)}(M)` of `A`-modules, natural in the `A`-module `M`. -/
def complementCohomologyBaseFunctorIso [IsNoetherianRing A] (I : Ideal A) (p : ℕ) (hp : 1 ≤ p) :
    complementCohomologyBaseFunctor I p ≅
      Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctor.{u, u} A
        (PrimeSpectrum.zeroLocus (I : Set A)) ((p + 1 : ℕ) : ℤ) :=
  Functor.isoWhiskerRight (complementDeltaTildeIso I p hp) (globalToBase A) ≪≫
    cohomologyWithSupportBaseFunctorIso I (p + 1)

/-! ### Stacks 0DWR in degree zero, natural in the module -/

/-- The natural map `H⁰_{V(I)}(M) ⟶ M`: the inclusion of the sections with support, read
through the identification of local cohomology with the cohomology with support of `M̃`. -/
def localCohomologyZeroToSelf [IsNoetherianRing A] (I : Ideal A) :
    Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctor.{u, u} A
        (PrimeSpectrum.zeroLocus (I : Set A)) 0 ⟶ 𝟭 (ModuleCat.{u} A) :=
  (cohomologyWithSupportBaseFunctorIso I 0).inv ≫
    Functor.whiskerLeft (tildeSheafFunctor A)
      (Functor.whiskerRight (supportInclusion I 0) (globalToBase A)) ≫
    ambientCohomologyZeroBaseFunctorIso.hom

/-- The natural map `M ⟶ Γ(U, M̃)`: the identification of `M` with the global sections of `M̃`
followed by restriction to `U = Spec A ∖ V(I)`. -/
def selfToComplementSections (I : Ideal A) :
    𝟭 (ModuleCat.{u} A) ⟶ complementCohomologyBaseFunctor I 0 :=
  ambientCohomologyZeroBaseFunctorIso.inv ≫
    Functor.whiskerLeft (tildeSheafFunctor A)
      (Functor.whiskerRight (complementRestriction I 0) (globalToBase A))

/-- The natural map `Γ(U, M̃) ⟶ H¹_{V(I)}(M)`: the connecting map of the cohomology sequence of
`V(I)`, read through the identification of the cohomology with support of `M̃` with local
cohomology. -/
def complementSectionsToLocalCohomologyOne [IsNoetherianRing A] (I : Ideal A) :
    complementCohomologyBaseFunctor I 0 ⟶
      Stacks.LocalCohomology.localCohomologyWithSupportInModuleFunctor.{u, u} A
        (PrimeSpectrum.zeroLocus (I : Set A)) 1 :=
  Functor.whiskerLeft (tildeSheafFunctor A)
      (Functor.whiskerRight (complementDelta I 0) (globalToBase A)) ≫
    (cohomologyWithSupportBaseFunctorIso I 1).hom

/-- The middle map of the natural four-term sequence is the canonical map `M ⟶ Γ(U, M̃)`. -/
theorem selfToComplementSections_app (I : Ideal A) (M : ModuleCat.{u} A) :
    (selfToComplementSections I).app M = toComplementSections I M :=
  rfl

/-- The map `H⁰_{V(I)}(M) ⟶ M` is a monomorphism. -/
theorem mono_localCohomologyZeroToSelf_app [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) : Mono ((localCohomologyZeroToSelf I).app M) := by
  have := (complementDelta_spec I).1 (tildeSheaf M)
  have hG : Mono ((globalToBase A).map ((supportInclusion I 0).app (tildeSheaf M))) :=
    Functor.map_mono _ _
  simp only [localCohomologyZeroToSelf, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  exact mono_comp' (IsIso.mono_of_iso _) (mono_comp' hG (IsIso.mono_of_iso _))

/-- The map `Γ(U, M̃) ⟶ H¹_{V(I)}(M)` is an epimorphism. -/
theorem epi_complementSectionsToLocalCohomologyOne_app [IsNoetherianRing A] (I : Ideal A)
    (M : ModuleCat.{u} A) : Epi ((complementSectionsToLocalCohomologyOne I).app M) := by
  have := epi_complementDelta_zero_app_tilde I M
  have hG : Epi ((globalToBase A).map ((complementDelta I 0).app (tildeSheaf M))) :=
    Functor.map_epi _ _
  simp only [complementSectionsToLocalCohomologyOne, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app]
  exact epi_comp' hG (IsIso.epi_of_iso _)

/-- **Stacks 0DWR in degree zero, natural in the module.** Let `A` be a Noetherian ring, let
`I ⊆ A` be an ideal and let `U = Spec A ∖ V(I)`. The natural sequence

`0 ⟶ H⁰_{V(I)}(M) ⟶ M ⟶ Γ(U, M̃) ⟶ H¹_{V(I)}(M) ⟶ 0`

is exact at `M` and at `Γ(U, M̃)`; together with `mono_localCohomologyZeroToSelf_app` and
`epi_complementSectionsToLocalCohomologyOne_app` it is exact. -/
@[ega "III 1.4.3" "(1.4.3.2)", sga "4 V 6.5" "(6.5.3) in degree q = 0"]
theorem exact_lowDegree_natural [IsNoetherianRing A] (I : Ideal A) (M : ModuleCat.{u} A) :
    (ComposableArrows.mk₃ ((localCohomologyZeroToSelf I).app M)
      ((selfToComplementSections I).app M)
      ((complementSectionsToLocalCohomologyOne I).app M)).Exact := by
  have hex := exact_complementDelta_zero_tilde I M
  have h01 : (supportInclusion I 0).app (tildeSheaf M) ≫
      (complementRestriction I 0).app (tildeSheaf M) = 0 := hex.toIsComplex.zero 0
  have h12 : (complementRestriction I 0).app (tildeSheaf M) ≫
      (complementDelta I 0).app (tildeSheaf M) = 0 := hex.toIsComplex.zero 1
  have hG : (ComposableArrows.mk₃
      ((globalToBase A).map ((supportInclusion I 0).app (tildeSheaf M)))
      ((globalToBase A).map ((complementRestriction I 0).app (tildeSheaf M)))
      ((globalToBase A).map ((complementDelta I 0).app (tildeSheaf M)))).Exact := by
    refine exact_mk₃_of_exact _ _ _ (by rw [← Functor.map_comp, h01, Functor.map_zero])
      (by rw [← Functor.map_comp, h12, Functor.map_zero]) ?_ ?_
    · exact (hex.exact 0).map (globalToBase A)
    · exact (hex.exact 1).map (globalToBase A)
  have w₀ : (globalToBase A).map ((supportInclusion I 0).app (tildeSheaf M)) ≫
      (ambientCohomologyZeroBaseFunctorIso.app M).hom =
        ((cohomologyWithSupportBaseFunctorIso I 0).app M).hom ≫
          (localCohomologyZeroToSelf I).app M := by
    simp [localCohomologyZeroToSelf]
    rfl
  have w₁ : (globalToBase A).map ((complementRestriction I 0).app (tildeSheaf M)) ≫
      𝟙 (complementCohomologyBase I M 0) =
        (ambientCohomologyZeroBaseFunctorIso.app M).hom ≫ (selfToComplementSections I).app M := by
    simp [selfToComplementSections]
    rfl
  have w₂ : (globalToBase A).map ((complementDelta I 0).app (tildeSheaf M)) ≫
      ((cohomologyWithSupportBaseFunctorIso I 1).app M).hom =
        𝟙 (complementCohomologyBase I M 0) ≫ (complementSectionsToLocalCohomologyOne I).app M :=
    (Category.id_comp _).symm
  exact ComposableArrows.exact_of_iso (S₁ := ComposableArrows.mk₃
      ((globalToBase A).map ((supportInclusion I 0).app (tildeSheaf M)))
      ((globalToBase A).map ((complementRestriction I 0).app (tildeSheaf M)))
      ((globalToBase A).map ((complementDelta I 0).app (tildeSheaf M))))
    (ComposableArrows.isoMk₃
      ((cohomologyWithSupportBaseFunctorIso I 0).app M)
      (ambientCohomologyZeroBaseFunctorIso.app M) (Iso.refl (complementCohomologyBase I M 0))
      ((cohomologyWithSupportBaseFunctorIso I 1).app M) w₀ w₁ w₂) hG

end Stacks.LocalCohomologySequence

end
