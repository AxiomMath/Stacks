module

public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleQuasicoherentHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.CoarseningDerivedUnitDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.CompositeAdjunctionUnit
public import StacksFrontier.Homology.PseudoCoherent.Locality

/-!
# The derived unit of the fppf-to-big-étale comparison of an algebraic space

Let `T` be a big fppf site of algebraic spaces over a scheme `S`, `E` a big étale site over the
same big fppf site of schemes and `X` an object of `T`. The change-of-topology morphism
`ε_X : ((Spaces/X)_fppf, 𝒪) ⟶ ((Spaces/X)_étale, 𝒪)` is, once the two sites are identified, the
comparison morphism of a topology with a coarser one on one ringed category. So its inverse image
`ε_X^*` on sheaves of modules is exact.

## Main results

* `AlgebraicGeometry.BigFppfSpaceSite.fppfToBigEtale_pullbackTopos_preservesFiniteLimits` and
  `..._preservesFiniteColimits`: `ε_X^*` is exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.BigFppfSpaceSite

variable {S : Scheme.{u}} (T : BigFppfSpaceSite S) (E : BigEtaleSpaceSite S)
  (h : T.schemeSite = E.fppfSite)

/-- **`ε_X^*` is left exact.** After identifying the two sites, `ε_X` is the comparison morphism
of the big étale topology with the finer big fppf topology on the slice category of `X`, whose
inverse image is sheafification for the finer topology. -/
instance fppfToBigEtale_pullbackTopos_preservesFiniteLimits (X : T.Spaces) :
    PreservesFiniteLimits (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pullbackTopos := by
  cases T with
  | mk tScheme tSchemeMem tInitial tInitialSmall tInitialFppf tBound tOrdinal tOrdinalLim
      tInitialBounded tIsSite tRepresentative =>
    cases E with
    | mk eSchemeSite eSchemeMem eFppfSite eFppfMem eInitial eInitialSmall eInitialEtale eBound
        eOrdinal eOrdinalLim eInitialBounded eIsSite eRepresentative =>
      cases h
      let T' : BigFppfSpaceSite S :=
        ⟨tScheme, tSchemeMem, tInitial, tInitialSmall, tInitialFppf, tBound, tOrdinal,
          tOrdinalLim, tInitialBounded, tIsSite, tRepresentative⟩
      let E' : BigEtaleSpaceSite S :=
        ⟨eSchemeSite, eSchemeMem, tScheme, eFppfMem, eInitial, eInitialSmall, eInitialEtale,
          eBound, eOrdinal, eOrdinalLim, eInitialBounded, eIsSite, eRepresentative⟩
      have htop : E'.topology ≤ T'.topology := by
        change E'.precoverage.toGrothendieck ≤ T'.precoverage.toGrothendieck
        intro U R hR
        rw [Precoverage.mem_toGrothendieck_iff] at hR ⊢
        induction hR with
        | of U R hR =>
            rw [BigEtaleSpaceSite.mem_precoverage_iff] at hR
            rcases hR with ⟨E₀, rfl, hE₀⟩
            have hEt : Space.IsEtaleCoveringFamily tScheme S eFppfMem ⟨U, E₀⟩ :=
              BigEtaleSpaceSite.IsCovering.etale hE₀
            have hFppf : Space.IsFppfCoveringFamily tScheme S eFppfMem ⟨U, E₀⟩ :=
              Space.isFppfCovering_of_isEtaleCovering tScheme S eFppfMem hEt
            obtain ⟨E₁, hE₁, hCE⟩ := tRepresentative ⟨U, E₀⟩ hFppf
            rcases hCE with ⟨hU, hCE'⟩
            change U = E₁.1 at hU
            subst hU
            have hpres := PreZeroHypercover.presieve₀_eq_of_combinatoriallyEquivalent hCE'
            have hpre : E₁.2.presieve₀ ∈ T'.precoverage E₁.1 := by
              rw [BigFppfSpaceSite.mem_precoverage_iff]
              exact ⟨E₁.2, rfl, hE₁⟩
            rw [hpres]
            exact Precoverage.generate_mem_toGrothendieck hpre
        | top => exact T'.topology.top_mem _
        | pullback U R _ V f ih => exact T'.topology.pullback_stable _ ih
        | transitive U R R' _ _ ihR ihT =>
            refine T'.topology.transitive ihR _ ?_
            intro V g hg
            exact ihT hg
      exact (bigFppfRingedSite T' X).preservesFiniteLimits_pullbackTopos_coarseningHom
        (J' := E'.topology.over X) (fun Z R hR => by
          rw [GrothendieckTopology.mem_over_iff] at hR ⊢
          exact htop Z.left hR)

/-- `ε_X^*` is right exact, being a left adjoint. -/
instance fppfToBigEtale_pullbackTopos_preservesFiniteColimits (X : T.Spaces) :
    PreservesFiniteColimits
      (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pullbackTopos :=
  have := (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom
    |>.pullbackPushforwardAdjunctionTopos.isLeftAdjoint
  inferInstance

/-! ### The derived pullback `Lε_X^*` -/

section Derived

attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackOnRingedTopoi

/-- `Lε_X^*` exists. -/
instance fppfToBigEtale_hasLeftDerivedFunctor (X : T.Spaces) :
    (pullbackOnHomotopy
      (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom).HasLeftDerivedFunctor
        (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
  hasLeftDerivedFunctor_pullbackOnHomotopy.{u + 1} _
    (fppfToBigEtaleRingedHom T E h X).isMorphismOfSites

/-- `ε_X^*` on sheaves of modules is additive, being a left adjoint. -/
instance fppfToBigEtale_pullbackTopos_additive (X : T.Spaces) :
    (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom.pullbackTopos.Additive :=
  (fppfToBigEtaleRingedHom T E h X).toRingedToposSiteHom
    |>.pullbackPushforwardAdjunctionTopos.left_adjoint_additive

end Derived

end AlgebraicGeometry.BigFppfSpaceSite

end
