module

public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.RingedSiteComparison

/-!
# Pseudo-coherence on the site of opens is pseudo-coherence on the ringed space

[Stacks, Tag 08CB] defines pseudo-coherence on a ringed space `X` point by point, and
[Stacks, Tag 08FT] defines it on a ringed site by coverings of objects. The first implies the
second on the ringed site of opens of `X`, by
`AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherentComplexFrom_ringedSite`. This file
proves the converse, so that the two notions agree.

## Main results

* `AlgebraicGeometry.RingedSpace.PseudoCoherence.hasSpaceApproximation_of_site`: a strictly
  perfect approximation over the slice at an open `U` is one over the open subspace `U`.
* `AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherentComplexFrom_of_ringedSite` and
  `isPseudoCoherentComplexFrom_ringedSite_iff`: the complex-level converse, and the equivalence.
* `AlgebraicGeometry.RingedSpace.PseudoCoherence.isPseudoCoherentFrom_of_ringedSite` and
  `isPseudoCoherentFrom_ringedSite_iff`: the same for objects of the derived category.

## Implementation notes

A covering sieve of the whole space in the site of opens contains, for each point `x`, an open
containing `x` over which the site predicate supplies a strictly perfect approximation on the
slice sheaf of rings. Mathlib's equivalence `TopologicalSpace.Opens.sheafOfModulesEquivOver`
carries it to the open subspace: it is exact, it carries the unit to the unit, and its value on
the restriction to the slice is the restriction to the open subspace, by
`AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictComplexBackwardIso` read backwards.

## References

* [Stacks Project, Tag 08CB](https://stacks.math.columbia.edu/tag/08CB)
* [Stacks Project, Tag 08FT](https://stacks.math.columbia.edu/tag/08FT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open StrictlyPerfect

universe u d

namespace AlgebraicGeometry.RingedSpace.PseudoCoherence

section Transport

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

/-- **A site approximation over `U` is a ringed-space approximation over `U`.** The equivalence of
the modules over the slice sheaf of rings with the modules on the open subspace `U` carries a
strictly perfect approximation of the restriction to the slice to one of the restriction to the
open subspace. -/
theorem hasSpaceApproximation_of_site (E : CochainComplex (OXMod.{u} X) ℤ) (m : ℤ)
    (h : HasSiteApproximation X E m U) :
    ∃ P : CochainComplex (OXMod.{u} (X.restrict U.isOpenEmbedding)) ℤ,
      StrictlyPerfect.IsStrictlyPerfect P ∧
      ∃ α : P ⟶ restrictComplex E U,
        (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j)) ∧
        Epi (HomologicalComplex.homologyMap α m) := by
  obtain ⟨P, hP, α, hiso, hepi⟩ := h
  let Φ := sheafOfModulesEquivRestrict.{u} X U
  let F := Φ.functor
  have : F.Additive := Functor.additive_of_preserves_binary_products _
  have : F.PreservesHomology := Functor.preservesHomologyOfExact F
  let Fc := F.mapHomologicalComplex (ComplexShape.up ℤ)
  let eUnit : F.obj (SheafOfModules.unit ((structureSheafOfRings X).over U)) ≅
      SheafOfModules.unit (structureSheafOfRings (X.restrict U.isOpenEmbedding)) :=
    F.mapIso (restrictBackwardUnitIso X U) ≪≫ Φ.counitIso.app _
  let eRes : Fc.obj ((Stacks.SheafOfModules.ringedSite X.sheaf).restrictComplex E U) ≅
      restrictComplex E U :=
    Fc.mapIso (restrictComplexBackwardIso X U E).symm ≪≫
      (Φ.mapHomologicalComplex (ComplexShape.up ℤ)).counitIso.app _
  refine ⟨Fc.obj P, (isStrictlyPerfect_iff (X.restrict U.isOpenEmbedding) _).2
    (Stacks.SheafOfModules.isStrictlyPerfect_mapHomologicalComplex F eUnit.symm hP),
    Fc.map α ≫ eRes.hom, ?_, ?_⟩
  · exact fun j hj => RingedSite.isIso_homologyMap_comp_iso _ _ j
      (RingedSite.isIso_homologyMap_map F α j (hiso j hj))
  · exact RingedSite.epi_homologyMap_comp_iso _ _ m (RingedSite.epi_homologyMap_map F α m hepi)

end Transport

section Main

variable (X : RingedSpace.{u, u})

/-- **`m`-pseudo-coherence of a complex on the site of opens is ringed-space
`m`-pseudo-coherence.** -/
theorem isPseudoCoherentComplexFrom_of_ringedSite (E : CochainComplex (OXMod.{u} X) ℤ) (m : ℤ)
    (h : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPseudoCoherentComplexFrom E m) :
    IsPseudoCoherentComplexFrom E m := by
  intro x
  obtain ⟨S, hS, hdata⟩ := h ⊤
  obtain ⟨V, f, ⟨V₀, b, f₀, hf₀, -⟩, hxV⟩ := hS x (Set.mem_univ x)
  exact ⟨V₀, (leOfHom b) hxV, hasSpaceApproximation_of_site X V₀ E m (hdata f₀ hf₀)⟩

/-- **The two notions of `m`-pseudo-coherence of a complex agree**: on the ringed space, and on
its site of opens. -/
theorem isPseudoCoherentComplexFrom_ringedSite_iff (E : CochainComplex (OXMod.{u} X) ℤ)
    (m : ℤ) :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPseudoCoherentComplexFrom E m ↔
      IsPseudoCoherentComplexFrom E m :=
  ⟨isPseudoCoherentComplexFrom_of_ringedSite X E m, isPseudoCoherentComplexFrom_ringedSite X E m⟩

variable [HasDerivedCategory.{d} (OXMod.{u} X)]

attribute [local instance] hasDerivedCategoryRingedSite

/-- **`m`-pseudo-coherence of an object of `D(O_X)` on the site of opens is ringed-space
`m`-pseudo-coherence.** -/
theorem isPseudoCoherentFrom_of_ringedSite (E : DerivedCategory (OXMod.{u} X)) (m : ℤ)
    (h : (Stacks.SheafOfModules.ringedSite X.sheaf).IsPseudoCoherentFrom E m) :
    IsPseudoCoherentFrom E m := by
  obtain ⟨K, hK, ⟨e⟩⟩ := h
  exact ⟨K, isPseudoCoherentComplexFrom_of_ringedSite X K m hK, ⟨e⟩⟩

/-- **The two notions of `m`-pseudo-coherence of an object of `D(O_X)` agree.** -/
theorem isPseudoCoherentFrom_ringedSite_iff (E : DerivedCategory (OXMod.{u} X)) (m : ℤ) :
    (Stacks.SheafOfModules.ringedSite X.sheaf).IsPseudoCoherentFrom E m ↔
      IsPseudoCoherentFrom E m :=
  ⟨isPseudoCoherentFrom_of_ringedSite X E m, isPseudoCoherentFrom_ringedSite X E m⟩

end Main

end AlgebraicGeometry.RingedSpace.PseudoCoherence
