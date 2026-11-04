module

public import Mathlib.Topology.Sets.Opens
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.CohomologyOfInverseLimits
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace

/-!
# Cohomology sheaves of an inverse limit of complexes on a ringed space

Let `X` be a ringed space and let `(ℱₙ)` be an inverse system, indexed by `ℕ`, of complexes
of sheaves of modules on `X`. Stacks 08BY says that if, over each member of a basis `B` of
the topology, the sections of the system have vanishing `R¹ lim` in degrees `m - 2` and
`m - 1` and on the degree-`m - 1` cohomology, and if the degree-`m` cohomology of those
sections is constant from some stage `n₀` on, then degree-`m` cohomology commutes with the
termwise inverse limit and the limit of the cohomology sheaves is already reached at `n₀`.

A ringed space is a ringed site whose underlying site is the site of opens, and a basis of
the topology gives a family of objects with the covering property
`GrothendieckTopology.HasEnoughObjects`. So both conclusions follow from the corresponding
statements for a ringed site, Stacks 08CT.

## Main results

* `Stacks.Cohomology.SpaceInverseSystems.basis_hasEnoughObjects`: a basis of the topology of
  a space is a family of objects of the site of opens with enough objects.
* `Stacks.Cohomology.SpaceInverseSystems.homology_isLimit_of_local_rlim_vanishing`: the
  canonical cone on the degree-`m` cohomology of the termwise inverse limit is a limit cone.
* `Stacks.Cohomology.SpaceInverseSystems.homology_limit_projection_isIso_of_local_rlim_vanishing`:
  the projection from the limit of the degree-`m` cohomology sheaves to stage `n₀` is an
  isomorphism.

## Implementation notes

Sections of a complex of sheaves of modules over an open, as a complex of abelian groups, are
`Stacks.Cohomology.InverseLimits.sectionsComplexFunctor` applied to the sheaf of rings
`structureSheafRing X`; no separate space-level version of that functor is
introduced. Vanishing of `R¹ lim` is `IsZero` applied to `Rlim.firstDerivedLimit`, and
eventual constancy of cohomology is invertibility of the canonical transition maps. Both
conclusions are stated about the canonical maps — the limit cone and the projection — rather
than merely asserting that some isomorphism exists.

The ringed site attached to a ringed space `X` has underlying category `Opens X`, the
topology `Opens.grothendieckTopology`, and structure sheaf `X.sheaf`; its sheaf of rings is
`structureSheafRing X` on the nose, so no comparison isomorphism is
needed.

## References

* [Stacks Project, Tag 08BY](https://stacks.math.columbia.edu/tag/08BY)
* [Stacks Project, Tag 08CT](https://stacks.math.columbia.edu/tag/08CT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction

namespace Stacks.Cohomology.SpaceInverseSystems

universe u

/-- The ringed site attached to a ringed space: the site of opens with its canonical topology
and the structure sheaf of the space. -/
abbrev ringedSiteOfSpace (X : RingedSpace.{u, u}) : RingedSite.{u, u, u} where
  C := Opens X.carrier
  J := Opens.grothendieckTopology X.carrier
  O := X.sheaf

/-- The sheaf of rings of the ringed site attached to a ringed space is the sheaf of rings of
that ringed space. -/
lemma ringedSiteOfSpace_ringSheaf (X : RingedSpace.{u, u}) :
    (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSiteOfSpace X).O) = structureSheafRing X :=
  rfl

/-- A basis of the topology of a space is a family of objects of the site of opens with
enough objects: every open is covered by members of the basis contained in it. -/
lemma basis_hasEnoughObjects (X : RingedSpace.{u, u})
    (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B) :
    (Opens.grothendieckTopology X.carrier).HasEnoughObjects (fun U => U ∈ B) := by
  show ∀ U : Opens X.carrier, ∃ (I : Type u) (Ui : I → Opens X.carrier)
    (f : ∀ i, Ui i ⟶ U),
      Sieve.ofArrows Ui f ∈ Opens.grothendieckTopology X.carrier U ∧ ∀ i, Ui i ∈ B
  intro U
  let I := {V : Opens X.carrier // V ∈ B ∧ V ≤ U}
  refine ⟨I, fun i => i.1, fun i => homOfLE i.2.2,
    (Opens.mem_grothendieckTopology X.carrier).2 fun x hx => ?_, fun i => i.2.1⟩
  obtain ⟨V, hV, hxV, hVU⟩ := (Opens.isBasis_iff_nbhd.mp hB) hx
  exact ⟨V, homOfLE hVU, (Sieve.mem_ofArrows_iff _ _ _).2 ⟨⟨V, hV, hVU⟩, 𝟙 V, by simp⟩, hxV⟩

/-- **Stacks 08BY.** Cohomology of the termwise inverse limit is the inverse limit of the
cohomology sheaves under local first-derived-limit vanishing and eventual stability. -/
@[stacks 08BY "canonical cohomology-limit comparison"]
theorem homology_isLimit_of_local_rlim_vanishing
    (X : RingedSpace.{u, u})
    (F : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (m : ℤ) (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B) (n₀ : ℕ)
    (hneg2 : ∀ U ∈ B, IsZero (Rlim.firstDerivedLimit
      (F ⋙ InverseLimits.sectionsComplexFunctor (structureSheafRing X) U ⋙
        HomologicalComplex.eval Ab.{u} (ComplexShape.up ℤ) (m - 2))))
    (hneg1 : ∀ U ∈ B, IsZero (Rlim.firstDerivedLimit
      (F ⋙ InverseLimits.sectionsComplexFunctor (structureSheafRing X) U ⋙
        HomologicalComplex.eval Ab.{u} (ComplexShape.up ℤ) (m - 1))))
    (hHneg1 : ∀ U ∈ B, IsZero (Rlim.firstDerivedLimit
      (F ⋙ InverseLimits.sectionsComplexFunctor (structureSheafRing X) U ⋙
        HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℤ) (m - 1))))
    (hstable : ∀ U ∈ B, ∀ (n : ℕ) (hn : n₀ ≤ n), IsIso
      ((HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℤ) m).map
        ((InverseLimits.sectionsComplexFunctor (structureSheafRing X) U).map
          (F.map (homOfLE hn).op)))) :
    Nonempty (IsLimit
      ((HomologicalComplex.homologyFunctor
        (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) m).mapCone
          (limit.cone F))) :=
  InverseLimits.homology_isLimit_of_local_rlim_vanishing (ringedSiteOfSpace X) F m B
    (basis_hasEnoughObjects X B hB) hneg2 hneg1 hHneg1 n₀ hstable

/-- **Stacks 08BY.** The projection from the limit of degree-`m` cohomology sheaves to the
stable stage is an isomorphism when the transition maps are locally isomorphisms on a
basis. -/
@[stacks 08BY "projection to the stable stage"]
theorem homology_limit_projection_isIso_of_local_rlim_vanishing
    (X : RingedSpace.{u, u})
    (F : ℕᵒᵖ ⥤ CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (m : ℤ) (B : Set (Opens X.carrier)) (hB : Opens.IsBasis B) (n₀ : ℕ)
    (hstable : ∀ U ∈ B, ∀ (n : ℕ) (hn : n₀ ≤ n), IsIso
      ((HomologicalComplex.homologyFunctor Ab.{u} (ComplexShape.up ℤ) m).map
        ((InverseLimits.sectionsComplexFunctor (structureSheafRing X) U).map
          (F.map (homOfLE hn).op)))) :
    IsIso (limit.π (F ⋙ HomologicalComplex.homologyFunctor
      (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ) m) (op n₀)) :=
  InverseLimits.homology_limit_projection_isIso_of_local_rlim_vanishing
    (ringedSiteOfSpace X) F m B (basis_hasEnoughObjects X B hB) n₀ hstable

end Stacks.Cohomology.SpaceInverseSystems

end
