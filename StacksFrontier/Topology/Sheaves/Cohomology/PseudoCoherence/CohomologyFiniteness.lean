module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.LocallyFree
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.FiniteFreeRepresentation
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.Defs
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.LocalApproximation

/-!
# Local tools for the finiteness of the top cohomology sheaves of a pseudo-coherent complex

Let `K` be an `m`-pseudo-coherent object of the derived category of `𝒪_X`-modules on a ringed
space `X`. Stacks 08DN says that `H^m(K)` is of finite type when the cohomology of `K` vanishes
above degree `m`, and that `H^{m+1}(K)` is finitely presented when it vanishes above degree
`m + 1`; those two statements are
`AlgebraicGeometry.RingedSpace.isFiniteType_homology_of_isPseudoCoherentFrom` (in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/ImmersionIndependence.lean`) and
`AlgebraicGeometry.RingedSpace.isFinitePresentation_homology_of_isPseudoCoherentFrom` (in
`StacksFrontier/AlgebraicGeometry/PseudoCoherent/FinitePresentationNextCohomology.lean`).

This file collects the tools for the cokernel presentation of a top cohomology sheaf. Given a
local strictly perfect approximation `α : P ⟶ C|_U` of a complex `C` representing `K`, with `P`
concentrated in degrees `≤ r` where `r` is the top possibly nonzero degree
(`AlgebraicGeometry.RingedSpace.exists_strictlyPerfect_approximation_boundedAbove`), `P` has no
term in degree `r + 1`, so its degree-`r` cohomology is the cokernel of `P^{r-1} ⟶ P^r` and `α`
identifies it with `H^r(K)|_U`. For finite type one only needs that `P^r`, a direct summand of a
finite free module, surjects onto it; for finite presentation one uses that `P^{r-1}` is a direct
summand of a finite free module too, so that `H^r(K)|_U` is the cokernel of a map of finite free
modules.

## Main results

* `AlgebraicGeometry.RingedSpace.nonempty_isColimit_cokernelCofork_homologyπ`: the top
  cohomology of a complex with no term above degree `r` is the cokernel of the last
  differential.
* `AlgebraicGeometry.RingedSpace.exists_retract_free`: a direct summand of a finite free module
  is a retract of a free module on a finite index type.

## Implementation notes

`StrictlyPerfect.finiteFree` is a biproduct indexed by `Fin n`, while Mathlib's free sheaf of
modules is a coproduct indexed by a type in the ring universe;
`AlgebraicGeometry.RingedSpace.finiteFreeIsoFree` is the comparison, and it is what turns a
retract of a finite free module into generating sections.

Finite type and finite presentation of a sheaf of modules are expressed by data indexed by a
covering of the terminal object. The covering provided here, `coversTop_of_mem`, is indexed by
the points of `X`, each point contributing the neighbourhood the local approximation produces;
this is also how the source phrases the local condition. The local data lives on the slice site
over that neighbourhood, so it is produced on the restricted ringed space and transported along
the equivalence `PseudoCoherence.sheafOfModulesEquivRestrict` between modules over the slice
sheaf of rings on an open subspace and modules on the restricted ringed space.

## References

* [Stacks Project, Lemma 20.46.12 (08DN)](https://stacks.math.columbia.edu/tag/08DN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect

attribute [local instance] AlgebraicGeometry.RingedSpace.overToRestricted_additive
  AlgebraicGeometry.RingedSpace.overToRestricted_isEquivalence

namespace AlgebraicGeometry.RingedSpace

universe u d

variable {X : RingedSpace.{u, u}}

/-- A direct summand of a finite free `𝒪_X`-module is a retract of a free sheaf of modules on a
finite index type. -/
theorem exists_retract_free {M : OXMod.{u, u} X} (hM : IsDirectSummandOfFiniteFree M) :
    ∃ n : ℕ, Nonempty (Retract M
      (SheafOfModules.free (R := structureSheafOfRings X) (ULift.{u} (Fin n)))) := by
  obtain ⟨n, ⟨ρ⟩⟩ := (isDirectSummandOfFiniteFree_iff_retract M).mp hM
  exact ⟨n, ⟨ρ.trans (finiteFreeIsoFree X n).retract⟩⟩

/-- The top cohomology of a complex of `𝒪_X`-modules with no term in degree `r + 1` is the
cokernel of the differential into degree `r`: the degree-`r` cycles are everything. -/
theorem nonempty_isColimit_cokernelCofork_homologyπ
    (P : CochainComplex (OXMod.{u, u} X) ℤ) (r : ℤ) (hr : IsZero (P.X (r + 1))) :
    ∃ (p : P.X r ⟶ P.homology r) (h : P.d (r - 1) r ≫ p = 0),
      Nonempty (IsColimit (CokernelCofork.ofπ p h)) := by
  have hiso : IsIso (P.iCycles r) :=
    KernelFork.IsLimit.isIso_ι (KernelFork.ofι (P.iCycles r) (P.iCycles_d r (r + 1)))
      (P.cyclesIsKernel r (r + 1) (by simp)) (hr.eq_of_tgt _ _)
  have hcomp : P.d (r - 1) r ≫ (asIso (P.iCycles r)).symm.hom = P.toCycles (r - 1) r := by
    rw [← P.toCycles_i (r - 1) r, Category.assoc]
    simp
  have hiff : ∀ ⦃W : OXMod.{u, u} X⦄ (φ : P.cycles r ⟶ W),
      P.toCycles (r - 1) r ≫ φ = 0 ↔
        P.d (r - 1) r ≫ (asIso (P.iCycles r)).symm.hom ≫ φ = 0 := by
    intro W φ
    rw [← Category.assoc, hcomp]
  exact ⟨_, _, ⟨CokernelCofork.isColimitOfIsColimitOfIff
    (P.homologyIsCokernel (r - 1) r (CochainComplex.prev ℤ r)) (P.d (r - 1) r)
    (asIso (P.iCycles r)).symm hiff⟩⟩

/-- Restricting a module to `X|_U` and identifying the result back with a module on the slice
site over `U` gives the restriction of the module to that slice site. -/
def overEquivRestrictedUnitIso (X : RingedSpace.{u, u}) (U : Opens X.carrier)
    (M : OXMod.{u, u} X) :
    (PseudoCoherence.sheafOfModulesEquivRestrict X U).inverse.obj
        ((restrictModules X U).obj M) ≅ M.over U :=
  ((PseudoCoherence.sheafOfModulesEquivRestrict X U).unitIso.app (M.over U)).symm

/-- The identification of modules on the slice site with modules on the restricted space sends
the structure sheaf to the structure sheaf. -/
def overEquivRestrictedUnitModuleIso (X : RingedSpace.{u, u}) (U : Opens X.carrier) :
    SheafOfModules.unit ((structureSheafOfRings X).over U) ≅
      (PseudoCoherence.sheafOfModulesEquivRestrict X U).inverse.obj
        (structureModule (X.restrict U.isOpenEmbedding)) :=
  (PseudoCoherence.sheafOfModulesEquivRestrict X U).unitIso.app _

/-- The cohomology of the restriction of a complex to an open subspace, in a degree where the
complex computes the cohomology of a derived object it represents. -/
def restrictHomologyIso [HasDerivedCategory.{d} (OXMod.{u, u} X)]
    {K : DerivedCategory (OXMod.{u, u} X)} (C : CochainComplex (OXMod.{u, u} X) ℤ)
    (e : DerivedCategory.Q.obj C ≅ K) (U : Opens X.carrier) (r : ℤ)
    [PreservesFiniteLimits (restrictModules X U)]
    [PreservesFiniteColimits (restrictModules X U)] :
    (restrictComplex C U).homology r ≅
      (restrictModules X U).obj ((DerivedCategory.homologyFunctor (OXMod.{u, u} X) r).obj K) :=
  (C.sc r).mapHomologyIso (restrictModules X U) ≪≫
    (restrictModules X U).mapIso
      (((DerivedCategory.homologyFunctorFactors (OXMod.{u, u} X) r).app C).symm ≪≫
        (DerivedCategory.homologyFunctor (OXMod.{u, u} X) r).mapIso e)

/-- A family of open sets, one containing each point, covers `X`. -/
theorem coversTop_of_mem (V : X.carrier → Opens X.carrier) (hV : ∀ x, x ∈ V x) :
    (Opens.grothendieckTopology X.carrier).CoversTop V :=
  (Opens.coversTop_iff _ V).mpr <|
    Opens.ext <| Set.eq_univ_of_forall fun x => le_iSup V x (hV x)

end AlgebraicGeometry.RingedSpace

end
