module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalTypesUnderEquivalence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposEquivalenceModules
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposPullbackModulesComp
public import StacksFrontier.AlgebraicGeometry.Quot.ComplexesStackCechDescentSpacesEtaleVertex
public import StacksFrontier.AlgebraicGeometry.Simplicial.ComponentRingedTopos.CartesianDerivedModuleCohomologyOfExact
public import StacksFrontier.AlgebraicGeometry.Simplicial.QuasicoherentCartesian.Equivalence

/-!
# Quasi-coherence of a cartesian object of the strict total site

This file proves `strictCartesianQuasicoherent`, the statement `StrictCartesianQuasicoherent` about
the strict components: for an fppf hypercovering `U`, a cartesian object `K` of the derived
category of the total site of the strict components of `U` whose components realize to complexes
with quasi-coherent cohomology has quasi-coherent cohomology on `U_{spaces,étale}` after the
comparison `e`.

1. The faces of `U` are flat (Stacks 0DER), so the pullbacks of modules along the face
   transitions of the strict components are exact: through the realizations, which are
   equivalences of ringed topoi, they are the pullbacks along the faces on the spaces-étale
   sites (`strictComponentPullbackModulesTransitionIso`).
2. Hence each `H^q(K)` is a cartesian module (Stacks 0D7L (2), in the form with exact face
   pullbacks).
3. The components of `H^q(K)` are `H^q(K_n)`, quasi-coherent because their realizations
   `H^q(R_n K_n)` are and quasi-coherence is intrinsic (Stacks 03DM).
4. So `H^q(K)` is quasi-coherent (Stacks 0D7M), and so is its pullback along the comparison `e`
   (Stacks 03DO), which is `H^q(Le^*K)` because `e^*` is exact.

## Main results

* `isQuasicoherentOnSite_homology_derivedPullback_strictRingedToposHom` and
  `isQuasicoherentOnSite_homology_of_strictComponentDerivedRealize`: quasi-coherent cohomology
  across the comparison `e` and the realizations `R_n`.
* `preservesFiniteLimits_strictTransitionPullbackModules_of_isFlat`: the pullback of modules along
  the transition of a strict component is exact when the transition of the simplicial algebraic
  space is flat.
* `strictCartesianQuasicoherent`: a cartesian object of the strict total site with
  quasi-coherent component cohomology has quasi-coherent cohomology after the comparison `e`.

## References

* [Stacks Project, Tag 0DER](https://stacks.math.columbia.edu/tag/0DER)
* [Stacks Project, Tag 0D7L](https://stacks.math.columbia.edu/tag/0D7L)
* [Stacks Project, Tag 0D7M](https://stacks.math.columbia.edu/tag/0D7M)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DO](https://stacks.math.columbia.edu/tag/03DO)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space.SimplicialSpacesEtaleSite

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

open Stacks.Cohomology.DerivedPullbackOfToposHom Stacks.CategoryTheory.Hypercovering

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-! ### Quasi-coherent cohomology across the comparisons -/

/-- **The comparison `e` carries quasi-coherent cohomology to quasi-coherent cohomology.** The
comparison of the strict total site with `X_{spaces,étale}` is an equivalence of ringed topoi, so
its pullback of modules is exact, `H^q(Le^*K) ≅ e^*H^q(K)`, and `e^*` preserves quasi-coherence
(Stacks 03DO). -/
theorem isQuasicoherentOnSite_homology_derivedPullback_strictRingedToposHom
    (X : SimplicialObject (AlgebraicSpaces B S hS))
    (K : DerivedCategory (strictRingedTopos X).Modules) (q : ℤ)
    (hK : ((DerivedCategory.homologyFunctor (strictRingedTopos X).Modules q).obj
      K).IsQuasicoherentOnSite) :
    ((DerivedCategory.homologyFunctor (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos X).O)) q).obj
      ((derivedPullback (X := ringedTopos X) (Y := strictRingedTopos X)
        (strictRingedToposHom X)).obj K)).IsQuasicoherentOnSite := by
  open RingedToposHom in
  have := isEquivalence_pullbackModules_of_isEquivalence_ringedToposEquivalenceModules
    (strictRingedToposHom X)
  have := RingedToposHom.pullbackModules_preservesFiniteColimits (strictRingedToposHom X)
  have := RingedToposHom.pullbackModules_additive (strictRingedToposHom X)
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((DerivedCategory.homologyFunctor _ q).mapIso
      ((Stacks.Homology.leftDerivedIsoMapDerivedCategory
        (strictRingedToposHom X).toModulesHom.pullbackModules
        (derivedPullback (X := ringedTopos X) (Y := strictRingedTopos X) (strictRingedToposHom X))
        (derivedPullbackComparison (X := ringedTopos X) (Y := strictRingedTopos X)
          (strictRingedToposHom X))).app K).symm) ?_
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (strictRingedToposHom X).toModulesHom.pullbackModules q).app K).symm ?_
  exact RingedToposHom.isQuasicoherentOnSite_pullbackModules (strictRingedToposHom X) _ hK

/-- **A complex on a strict component has quasi-coherent cohomology when its realization does.**
The realization `R_n` is an equivalence of ringed topoi, so `H^q(R_n E) ≅ r_n^*H^q(E)`, and
quasi-coherence is intrinsic (Stacks 03DM). -/
theorem isQuasicoherentOnSite_homology_of_strictComponentDerivedRealize
    (X : SimplicialObject (AlgebraicSpaces B S hS)) (n : SimplexCategory)
    (E : DerivedCategory
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) n).Modules)
    (q : ℤ)
    (hE : ((DerivedCategory.homologyFunctor (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (spacesEtaleRingedTopos B S hS (X.obj (op n))).O))
          q).obj ((strictComponentDerivedRealize X n).obj E)).IsQuasicoherentOnSite) :
    ((DerivedCategory.homologyFunctor
      ((strictSituation X).componentRingedTopos (strictStructureSheaf X) n).Modules q).obj
        E).IsQuasicoherentOnSite := by
  open RingedToposHom in
  have := isEquivalence_pullbackModules_of_isEquivalence_ringedToposEquivalenceModules
    (strictComponentRingedToposHom X n)
  have :=
    RingedToposHom.pullbackModules_preservesFiniteColimits (strictComponentRingedToposHom X n)
  have := RingedToposHom.pullbackModules_additive (strictComponentRingedToposHom X n)
  refine (RingedToposHom.isQuasicoherentOnSite_iff_pullbackModules
    (strictComponentRingedToposHom X n) _).2 ?_
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
      (strictComponentRingedToposHom X n).toModulesHom.pullbackModules q).app E) ?_
  refine SheafOfModules.IsQuasicoherentOnSite.of_iso
    ((DerivedCategory.homologyFunctor _ q).mapIso
      ((Stacks.Homology.leftDerivedIsoMapDerivedCategory
        (strictComponentRingedToposHom X n).toModulesHom.pullbackModules
        (strictComponentDerivedRealize X n)
        (derivedPullbackComparison (X := spacesEtaleRingedTopos B S hS (X.obj (op n)))
          (Y := (strictSituation X).componentRingedTopos (strictStructureSheaf X) n)
          (strictComponentRingedToposHom X n))).app E)) hE

/-! ### Exactness of the face pullbacks of the strict components -/

/-- **The pullback of modules along a transition of the strict components is exact when the
transition of the simplicial algebraic space is flat.** Through the realizations, which are
equivalences, it is the pullback along `X(φ)` on the spaces-étale sites
(`strictComponentPullbackModulesTransitionIso`), which is exact for flat `X(φ)`. -/
theorem preservesFiniteLimits_strictTransitionPullbackModules_of_isFlat
    (X : SimplicialObject (AlgebraicSpaces B S hS)) {m n : SimplexCategory} (φ : m ⟶ n)
    (hφ : IsFlat B S hS (X.map φ.op).hom) :
    PreservesFiniteLimits ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X)
      φ).toModulesHom.pullbackModules := by
  have := preservesFiniteLimits_spacesEtaleRingedToposHom_pullbackModules_spacesEtaleModulePullbackFlatExact
    (X.map φ.op) hφ
  let e := (RingedToposHom.pullbackModulesCompIso (strictComponentRingedToposHom X n)
      ((strictSituation X).transitionRingedToposHom (strictStructureSheaf X) φ)).symm ≪≫
    strictComponentPullbackModulesTransitionIso X φ ≪≫
    RingedToposHom.pullbackModulesCompIso (spacesEtaleRingedToposHom (X.map φ.op))
      (strictComponentRingedToposHom X m)
  open RingedToposHom in
  have := isEquivalence_pullbackModules_of_isEquivalence_ringedToposEquivalenceModules
    (strictComponentRingedToposHom X m)
  open RingedToposHom in
  have := isEquivalence_pullbackModules_of_isEquivalence_ringedToposEquivalenceModules
    (strictComponentRingedToposHom X n)
  have : PreservesFiniteLimits
      ((strictComponentRingedToposHom X m).toModulesHom.pullbackModules ⋙
        (spacesEtaleRingedToposHom (X.map φ.op)).toModulesHom.pullbackModules) :=
    comp_preservesFiniteLimits _ _
  have := preservesFiniteLimits_of_natIso e.symm
  exact preservesFiniteLimits_of_reflects_of_preserves _
    (strictComponentRingedToposHom X n).toModulesHom.pullbackModules

/-! ### The statement -/

variable (B S hS) in
/-- **Quasi-coherence of a cartesian object of the strict total site**, the statement
`StrictCartesianQuasicoherent`. For an fppf hypercovering `U`, the cohomology modules of a
cartesian object `K` of `D(𝒪)` on the strict total site are cartesian (Stacks 0D7L (2), the face
pullbacks being exact) with quasi-coherent components, hence quasi-coherent (Stacks 0D7M), and
their pullbacks along the comparison `e` are the cohomology modules of `Le^*K`. -/
theorem strictCartesianQuasicoherent : StrictCartesianQuasicoherent B S hS := by
  intro U hU K hK hQ q
  have hexact : ∀ (k : ℕ) (i : Fin (k + 2)),
      PreservesFiniteLimits ((strictSituation U.left).transitionRingedToposHom
        (strictStructureSheaf U.left) (SimplexCategory.δ i)).toModulesHom.pullbackModules :=
    fun k i => preservesFiniteLimits_strictTransitionPullbackModules_of_isFlat U.left _
      (isFlat_δ_of_isHypercoveringAugmentation U hU k i)
  open CategoryTheory.SimplicialSiteSituation in
  have hcart :=
    (isCartesianDerivedModule_iff_forall_isCartesianModule_homology_of_preservesFiniteLimits
      (strictSituation U.left) (strictStructureSheaf U.left) hexact K).1 hK q
  have hcomp : ∀ n : SimplexCategory,
      ((strictSituation U.left).componentModule (strictStructureSheaf U.left)
        ((DerivedCategory.homologyFunctor (strictRingedTopos U.left).Modules q).obj K)
        n).IsQuasicoherentOnSite := fun n =>
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((StacksDraft.PseudoCoherence.mapDerivedCategoryCompHomologyFunctorIso
        ((strictSituation U.left).componentModulesRestriction (strictStructureSheaf U.left) n)
        q).app K)
      (isQuasicoherentOnSite_homology_of_strictComponentDerivedRealize U.left n _ q (hQ n q))
  open CategoryTheory.SimplicialSiteSituation in
  exact isQuasicoherentOnSite_homology_derivedPullback_strictRingedToposHom U.left K q
    ((isQuasicoherentOnSite_iff_isCartesianModule_and_isQuasicoherentOnSite_componentModule
      (strictSituation U.left) (strictStructureSheaf U.left) _).2 ⟨hcart, hcomp⟩)

end AlgebraicGeometry.Space.SimplicialSpacesEtaleSite
