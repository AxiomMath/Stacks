module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AffineCohomologyVanishing.Basic
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.Noetherian.CoherentHomology
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.QuasicoherentCohomology
public import StacksFrontier.Homology.DerivedComplete.NoetherianCohomologyAdicCompletion
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.AffineCovering
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.HypercohomologyOverAcyclicOpens

/-!
# Affine sections of the derived completion of a pseudo-coherent complex

Let `X` be a locally Noetherian scheme, `𝓘 ⊂ 𝒪_X` a quasi-coherent sheaf of ideals and `K` a
pseudo-coherent object of `D(𝒪_X)` with derived completion `K^∧`. For an affine open `U ⊂ X`,
with `A = Γ(X, U)` and `I = 𝓘(U)`,
`H^p(U, K^∧) = lim H^p(U, K)/IⁿH^p(U, K) = H^p(U, K)^∧`,
the completion on the right being the derived completion of the `A`-module `H^p(U, K)` along `I`.

## Main results

* `Stacks.Algebraization.finite_homology_derivedSections_of_isPseudoCoherent`: the cohomology
  modules `H^p(U, K)` of a pseudo-coherent object over an affine open of a locally Noetherian
  scheme are finite over `Γ(X, U)`.
* `Stacks.Algebraization.adicCompletion_homology_derivedSections_iso_derivedCompletion`: the
  second equality, `lim H^p(U, K)/IⁿH^p(U, K) = H^p(U, K)^∧`.

## Implementation notes

The middle term `lim H^p(U, K)/IⁿH^p(U, K)` is Mathlib's `AdicCompletion I M`, which is by
definition the module of compatible families in `∏ₙ M/IⁿM`, that is the inverse limit of the
quotient tower; this is the same spelling the neighbouring tags 0A06 and 0A0M use for it.

`H^p(U, -)` is the degree-`p` cohomology of the unbounded derived sections
`Stacks.Cohomology.HypercohomologyEdge.derivedSections` over `U`, which is `RΓ(U, -)` on the
whole of `D(𝒪_X)`; the unbounded functor is the one needed, since `K^∧` is not known to be
bounded below. Derived completion of `A`-modules is represented by an arbitrary left adjoint `C`
to the inclusion of the derived-complete objects of `D(A)`, as in [Stacks, Tag 0A06], so no
choice of reflector enters.

Finiteness of `H^p(U, K)` is where pseudo-coherence and the Noetherian hypothesis are used. The
cohomology sheaves of `K` are quasi-coherent ([Stacks, Tag 08E5]) and coherent ([Stacks,
Tag 08E8]); quasi-coherence gives Serre vanishing on the affine opens ([Stacks, Tag 01XB]),
hence the hypercohomology edge isomorphism `H^p(U, K) = Γ(U, H^p(K))` of [Stacks, Tag 0BKT];
and the sections of a coherent module over an affine open are a finite module ([Stacks,
Tag 01PB]).

The first equality passes through the identification `RΓ(U, K^∧) = RΓ(U, K)^∧` in `D(A)` of
[Stacks, Tag 0CQI]. It is stated, together with the second, at `K^∧` itself by
`Stacks.Algebraization.exists_iso_homology_derivedSections_derivedCompletion_whole` of
`Completion/FormalFunctionsPseudoCoherentWhole.lean`, where that identification is proved.

## References

* [Stacks Project, Tag 0A0L](https://stacks.math.columbia.edu/tag/0A0L)
* [Stacks Project, Tag 0A06](https://stacks.math.columbia.edu/tag/0A06)
* [Stacks Project, Tag 0CQI](https://stacks.math.columbia.edu/tag/0CQI)
* [Stacks Project, Tag 0BKT](https://stacks.math.columbia.edu/tag/0BKT)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
* [Stacks Project, Tag 01PB](https://stacks.math.columbia.edu/tag/01PB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction Stacks.Cohomology.HypercohomologyEdge

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.Algebraization

/-! ### Finiteness of the affine cohomology modules -/

/-- **The cohomology of a pseudo-coherent complex over an affine open of a locally Noetherian
scheme is a finite module.**

The cohomology sheaves of `K` are quasi-coherent, so they are acyclic over the affine opens and
the hypercohomology edge morphism identifies `H^p(U, K)` with `Γ(U, H^p(K))`; and `H^p(K)` is
coherent, so its sections over an affine open form a finite module. -/
public theorem finite_homology_derivedSections_of_isPseudoCoherent (X : Scheme.{u})
    [IsLocallyNoetherian X] (K : DerivedCategory X.Modules)
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K)
    (U : X.affineOpens) (p : ℤ) :
    Module.Finite Γ(X, U.1)
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
        ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K)) := by
  obtain ⟨P, hP, e⟩ := hK
  have hqc : ∀ q : ℤ, ((DerivedCategory.homologyFunctor X.Modules q).obj K).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherentDerived_of_isPseudoCoherent X K ⟨P, hP, e⟩
  have hac : ∀ V ∈ X.affineOpens, ∀ r : ℕ, 0 < r → ∀ q : ℤ,
      IsZero (((SheafOfModules.evaluation (structureSheafRing X.toRingedSpace)
          (op V)).rightDerived r).obj
        ((DerivedCategory.homologyFunctor
          (SheafOfModules.{u} (structureSheafRing X.toRingedSpace)) q).obj K)) := by
    intro V hV r hr q
    have := hqc q
    exact (Stacks.Cohomology.CechAcyclic.isZero_rightDerived_evaluation_iff_isZero_Hgroup
      X.ringCatSheaf V r ((DerivedCategory.homologyFunctor X.Modules q).obj K)).2
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X _ V hV r hr)
  have hedge : (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
        ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K) ≅
      ModuleCat.of Γ(X, U.1) Γ((DerivedCategory.homologyFunctor X.Modules p).obj K, U.1) :=
    Stacks.Cohomology.AcyclicOpen.hypercohomologyIso X.toRingedSpace K
      X.affineOpens X.isBasis_affineOpens hac U.1 U.2 p
  have hcoh := AlgebraicGeometry.isCoherent_homology_of_isPseudoCoherentFrom X K p hqc
    ⟨P, hP p, e⟩ p le_rfl
  have := hqc p
  have := hcoh.isFiniteType
  have hfin : Module.Finite Γ(X, U.1)
      Γ((DerivedCategory.homologyFunctor X.Modules p).obj K, U.1) :=
    Stacks.AlgebraicGeometry.CoherentFinite.finite_sections
      ((DerivedCategory.homologyFunctor X.Modules p).obj K) U.2
  exact Module.Finite.equiv hedge.toLinearEquiv.symm

/-! ### The second equality of the theorem on formal functions -/

/-- The cohomology of a finite module placed in degree zero is finite in every degree. -/
private theorem finite_homology_single_of_finite {A : Type u} [CommRing A] (M : ModuleCat.{u} A)
    [Module.Finite A M] (n : ℤ) :
    Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
      ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) := by
  by_cases hn : n = 0
  · subst hn
    have : Module.Finite A ((𝟭 (ModuleCat.{u} A)).obj M) := inferInstanceAs (Module.Finite A M)
    exact Module.Finite.equiv
      ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} A)
        0).app M).toLinearEquiv.symm
  · have hz : IsZero ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) := by
      let e := (DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).mapIso
          ((DerivedCategory.singleFunctorIsoCompQ (ModuleCat.{u} A) 0).app M) ≪≫
        (DerivedCategory.homologyFunctorFactors (ModuleCat.{u} A) n).app _
      exact (HomologicalComplex.isZero_single_obj_homology (ComplexShape.up ℤ) 0 M n hn).of_iso e
    have : Subsingleton ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
        ((DerivedCategory.singleFunctor (ModuleCat.{u} A) 0).obj M)) :=
      ModuleCat.isZero_iff_subsingleton.mp hz
    infer_instance

/-- **Stacks Project, Tag 0A0L, the second equality.** Let `X` be a locally Noetherian scheme,
`𝓘 ⊂ 𝒪_X` a quasi-coherent sheaf of ideals and `K` a pseudo-coherent object of `D(𝒪_X)`. For an
affine open `U`, with `A = Γ(X, U)` and `I = 𝓘(U)`, and any left adjoint `C` to the inclusion of
the derived-complete objects of `D(A)`, the `I`-adic completion `lim H^p(U, K)/IⁿH^p(U, K)` of
`H^p(U, K)` is the derived `I`-adic completion of the `A`-module `H^p(U, K)`, read in degree zero.

This is [Stacks, Tag 0A06] for the complex `H^p(U, K)[0]`, which is legitimate because
`H^p(U, K)` is a finite module. -/
@[stacks 0A0L "the second equality `lim H^p(U, K)/IⁿH^p(U, K) = H^p(U, K)^∧`, the right hand \
completion being the derived completion of the module `H^p(U, K)` along `I = 𝓘(U)`; the first \
equality is `homology_derivedSections_derivedCompletion_iso_adicCompletion`"]
public theorem adicCompletion_homology_derivedSections_iso_derivedCompletion
    (X : Scheme.{u}) [IsLocallyNoetherian X] (𝓘 : X.IdealSheafData)
    (K : DerivedCategory X.Modules)
    (hK : RingedSpace.IsPseudoCoherent (X := X.toRingedSpace) K)
    (U : X.affineOpens)
    (C : DerivedCategory (ModuleCat.{u} Γ(X, U.1)) ⥤
      (show ObjectProperty (DerivedCategory (ModuleCat.{u} Γ(X, U.1))) from
        fun L ↦ IsDerivedComplete (𝓘.ideal U) L).FullSubcategory)
    (adj : C ⊣ (show ObjectProperty (DerivedCategory (ModuleCat.{u} Γ(X, U.1))) from
      fun L ↦ IsDerivedComplete (𝓘.ideal U) L).ι)
    (p : ℤ) :
    Nonempty
      (ModuleCat.of Γ(X, U.1) (AdicCompletion (𝓘.ideal U)
          ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
            ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K))) ≅
        (DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) 0).obj
          ((C ⋙ (show ObjectProperty (DerivedCategory (ModuleCat.{u} Γ(X, U.1))) from
              fun L ↦ IsDerivedComplete (𝓘.ideal U) L).ι).obj
            ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U.1)) 0).obj
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
                ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K))))) := by
  have : IsNoetherianRing Γ(X, U.1) := IsLocallyNoetherian.component_noetherian U
  have hfin := finite_homology_derivedSections_of_isPseudoCoherent X K hK U p
  obtain ⟨e⟩ := AdicCompletionCohomology.derivedCompletion_homology_iso_adicCompletion
    Γ(X, U.1) (𝓘.ideal U)
    ((DerivedCategory.singleFunctor (ModuleCat.{u} Γ(X, U.1)) 0).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{u} Γ(X, U.1)) p).obj
        ((derivedSections (structureSheafRing X.toRingedSpace) U.1).obj K)))
    (fun n ↦ finite_homology_single_of_finite _ n) C adj 0
  exact ⟨(e ≪≫ ((AdicCompletion.congr (𝓘.ideal U)
    ((DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{u} Γ(X, U.1))
      0).app _).toLinearEquiv).restrictScalars Γ(X, U.1)).toModuleIso).symm⟩

end Stacks.Algebraization

end
