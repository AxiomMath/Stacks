module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CoefficientChangeTrace
public import StacksFrontier.CategoryTheory.Trace.Sorites.TwistedRestrictionTrace

/-!
# Conjugacy traces of the Frobenius trace over a group ring

Let `A` be a finite commutative ring, `G` a finite group with `A[G]` injective as a module over
itself, `Y` a scheme over a finite field and `L` a bounded below complex of sheaves of
`A[G]`-modules on `Y_étale` whose restriction to `Y_k̄` has injective stalks, with
`T = Tr_{A[G]}(π_Y^* | RΓ(Y_k̄, L|))` defined. For `g ∈ G` the conjugacy trace
`κ_g(T) = ∑_{h} T(h⁻¹ g h)` (`Stacks.Trace.conjugacyTrace`) is the trace over `A` of the Frobenius
of `RΓ(Y_k̄, L|)`, viewed as a complex of `A`-modules, composed with the action of `g⁻¹`:

`κ_g(Tr_{A[G]}(π_Y^* | RΓ(Y_k̄, L|))) = Tr_A(g⁻¹ π_Y^* | RΓ(Y_k̄, L|))`.

This is `Stacks.EtaleCohomology.perfectDerivedTrace_derivedTwistEndo_coefficient` for restriction
of scalars along `A → A[G]` twisted by the action of `g⁻¹`. In Step 7 of the proof of
[Stacks, Tag 03UG] it turns the vanishing of Steps 8 and 9 for every deck transformation into the
vanishing of every conjugacy trace of the trace over the group ring.

## Main results

* `Stacks.EtaleCohomology.perfectDerivedTrace_groupElementAction_eq_conjugacyTrace`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.FilteredDerived
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius
open scoped MonoidAlgebra

attribute [local instance] HasDerivedCategory.standard

universe u

/-- The group ring of a finite group over a finite ring is finite. -/
instance MonoidAlgebra.finite_of_finite {A : Type*} [Semiring A] [Finite A] {G : Type*} [Finite G] :
    Finite (MonoidAlgebra A G) :=
  Finite.of_equiv _ (MonoidAlgebra.coeffEquiv.trans Finsupp.equivFunOnFinite).symm

namespace Stacks.EtaleCohomology

variable {A : Type} [CommRing A] [Finite A] {G : Type} [Group G] [Finite G]
  {k : Type u} [Field k] [Fintype k] (Y : Over (Spec (.of k)))
  (kbar : Type u) [Field kbar] [IsSepClosed kbar] [Algebra k kbar] (p q : ℕ) [Fact p.Prime]
  [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **The conjugacy traces of the Frobenius trace over a group ring.** -/
theorem perfectDerivedTrace_groupElementAction_eq_conjugacyTrace (g : G)
    (hR : Module.Baer A[G] A[G])
    (L : CochainComplex.Plus (EtaleModules.{u, 0} A[G] Y.left))
    (hL : ∀ (x : fieldBaseChange Y kbar) (n : ℤ), Module.Injective A[G]
      (((residueEtalePoint.{u, 0} (fieldBaseChange Y kbar) x).sheafFiber
        (A := ModuleCat.{u + 1} A[G])).obj
          (((etaleModuleInverseImage.{u, 0} A[G]
            (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            L).obj.X n)))
    (hperf : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} A[G] (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} A[G]
          (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} A[G] Y kbar L))))) :
    ∃ hperf' : StacksDraft.Perfect.IsPerfect (DerivedCategory.Plus.ι.obj
      ((etaleModuleDerivedGlobalSections.{u, 0} A (Spec (.of kbar))).obj
        ((etaleModuleDerivedDirectImage.{u, 0} A (pullback.snd Y.hom (specAlgebraMap k kbar))).obj
          (fieldBaseChangeRestriction.{u, 0} A Y kbar
            ((etaleModuleCoefficient (Stacks.Trace.groupAlgebraRestriction.{0, 0, u + 1} A G)
              Y.left).mapCochainComplexPlus.obj L))))),
      perfectDerivedTrace A ⟨_, hperf'⟩ (DerivedCategory.Plus.ι.map (Functor.derivedTwistEndo
        (etaleModuleDirectImage.{u, 0} A (geometricFrobeniusBaseChange Y kbar p q hcard))
        (etaleModuleDirectImage.{u, 0} A (pullback.snd Y.hom (specAlgebraMap k kbar)))
        (etaleModuleGlobalSections.{u, 0} A (Spec (.of kbar)))
        (etaleModuleDirectImageComp.{u, 0} A (geometricFrobeniusBaseChange Y kbar p q hcard)
          (pullback.snd Y.hom (specAlgebraMap k kbar)) (pullback.snd Y.hom (specAlgebraMap k kbar))
          (geometricFrobeniusBaseChange_comp_toBase Y kbar p q hcard).symm)
        ((etaleModuleInverseImage.{u, 0} A (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
          ((etaleModuleCoefficient (Stacks.Trace.groupAlgebraRestriction.{0, 0, u + 1} A G)
            Y.left).mapCochainComplexPlus.obj L))
        (ObjectProperty.homMk
          (X := (etaleModuleInverseImage.{u, 0} A
            (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
            ((etaleModuleCoefficient (Stacks.Trace.groupAlgebraRestriction.{0, 0, u + 1} A G)
              Y.left).mapCochainComplexPlus.obj L))
          (Y := (etaleModuleDirectImage.{u, 0} A
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.obj
            ((etaleModuleInverseImage.{u, 0} A
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.obj
              ((etaleModuleCoefficient (Stacks.Trace.groupAlgebraRestriction.{0, 0, u + 1} A G)
                Y.left).mapCochainComplexPlus.obj L)))
          ((NatTrans.mapHomologicalComplex
          (frobeniusBaseChangeTwist.{u, 0} A Y kbar p q hcard) (ComplexShape.up ℤ)).app
            ((etaleModuleCoefficient (Stacks.Trace.groupAlgebraRestriction.{0, 0, u + 1} A G)
              Y.left).mapCochainComplexPlus.obj L).obj) ≫
          (etaleModuleDirectImage.{u, 0} A
            (geometricFrobeniusBaseChange Y kbar p q hcard)).mapCochainComplexPlus.map
            ((etaleModuleInverseImage.{u, 0} A
              (fieldBaseChangeProj Y kbar)).mapCochainComplexPlus.map
              (ObjectProperty.homMk
                (X := (etaleModuleCoefficient
                  (Stacks.Trace.groupAlgebraRestriction.{0, 0, u + 1} A G)
                  Y.left).mapCochainComplexPlus.obj L)
                (Y := (etaleModuleCoefficient
                  (Stacks.Trace.groupAlgebraRestriction.{0, 0, u + 1} A G)
                  Y.left).mapCochainComplexPlus.obj L)
                ((NatTrans.mapHomologicalComplex
                (sheafCompose_map Y.left.smallEtaleTopology
                  (Stacks.Trace.groupElementAction.{0, 0, u + 1} A G g))
                  (ComplexShape.up ℤ)).app L.obj)))))) =
        Stacks.Trace.conjugacyTrace.{0, 0, u + 1} A G g
          (perfectDerivedTrace A[G] ⟨_, hperf⟩ (DerivedCategory.Plus.ι.map
            (frobeniusRestrictionCohomologyEndo.{u, 0} A[G] Y kbar p q hcard L))) :=
  perfectDerivedTrace_derivedTwistEndo_coefficient
    (Stacks.Trace.groupAlgebraRestriction.{0, 0, u + 1} A G) Y kbar p q hcard
    (fun _ I _ => isAcyclicEverywhere_restrictScalars' _ I)
    (Stacks.Trace.groupElementAction.{0, 0, u + 1} A G g) hR
    (Stacks.Trace.preservesFiniteProjective_groupAlgebraRestriction A G) L hL hperf

end Stacks.EtaleCohomology

end
