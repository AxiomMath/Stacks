module

public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import StacksFrontier.AlgebraicGeometry.Cohomology.InjectiveFlasqueModules
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
import StacksCore.Tactic.StacksAttribute

/-!
# Bounded below complexes of modules admit bounded below flasque resolutions

Let `(X, 𝒪_X)` be a ringed space and let `F` be a bounded below complex of `𝒪_X`-modules.
Then there is a quasi-isomorphism `F ⟶ G` onto a complex `G` that is bounded below in the
same degree and all of whose terms are flasque `𝒪_X`-modules.

The resolution produced here is an injective resolution: `G` is degreewise injective, and an
injective sheaf of modules is flasque by Tag 09SX
(`Stacks.Cohomology.isFlasque_of_injective_module`). The existence of a degreewise injective
quasi-isomorphic replacement of a bounded below complex is Mathlib's
`CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective`, available because the
category of sheaves of modules on the open-cover site is Grothendieck abelian and therefore
has enough injectives.

## Main results

* `Stacks.Cohomology.exists_quasiIso_isStrictlyGE_isFlasque`: for a sheaf of rings `R` on the
  open-cover site of a topological space and a complex `F` of `R`-modules with
  `F.IsStrictlyGE n`, there is a quasi-isomorphism `F ⟶ G` with `G.IsStrictlyGE n` and every
  `G.X i` flasque.
* `Stacks.Cohomology.exists_quasiIso_boundedBelow_isFlasque_ringedSpace`: the same statement on
  a ringed space, with boundedness below written as an existential.

The full statement of [Stacks, Tag 0FKT], including the stalkwise homotopy equivalence
`F_x ⟶ G_x`, is `exists_quasiIso_boundedBelow_isFlasque_isHomotopyEquiv_stalk_godement` in the
namespace `AlgebraicGeometry.GodementResolution`, for the Godement resolution.

For a *single* sheaf of modules the stalkwise homotopy equivalence of the Godement complex is
`AlgebraicGeometry.GodementResolution.homotopyEquivalences_stalk_godementAugmentation`, and its
form that is natural in the sheaf is
`AlgebraicGeometry.GodementResolution.hasNaturalStalkHomotopy_godementAugmentation`.

## References

* [Stacks Project, Tag 0FKT](https://stacks.math.columbia.edu/tag/0FKT)
* [Stacks Project, Tag 09SX](https://stacks.math.columbia.edu/tag/09SX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology

/-- A bounded below complex of sheaves of modules on the open-cover site of a topological space
admits a quasi-isomorphism onto a complex that is bounded below in the same degree and whose
terms are all flasque.

The complex produced is degreewise injective; flasqueness is Tag 09SX. -/
theorem exists_quasiIso_isStrictlyGE_isFlasque {X : TopCat.{u}}
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    (F : CochainComplex (SheafOfModules.{u} R) ℤ) (n : ℤ) [F.IsStrictlyGE n] :
    ∃ (G : CochainComplex (SheafOfModules.{u} R) ℤ) (f : F ⟶ G),
      QuasiIso f ∧ G.IsStrictlyGE n ∧
        ∀ i : ℤ, TopCat.Sheaf.IsFlasque ((SheafOfModules.toSheaf R).obj (G.X i)) := by
  obtain ⟨G, f, hf, hinj, hGE⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective F n
  refine ⟨G, f, hf, hGE, fun i => ?_⟩
  have : Injective (G.X i) := hinj i
  exact isFlasque_of_injective_module R (G.X i)

/-- A bounded below complex `F` of modules on a ringed space `(X, 𝒪_X)` admits a
quasi-isomorphism `F ⟶ G` onto a complex `G` of flasque `𝒪_X`-modules that is bounded below in
the same degree. -/
theorem exists_quasiIso_boundedBelow_isFlasque_ringedSpace (X : RingedSpace.{u, u})
    (F : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
    (hF : ∃ n : ℤ, F.IsStrictlyGE n) :
    ∃ (G : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ)
      (f : F ⟶ G),
      QuasiIso f ∧ (∃ n : ℤ, G.IsStrictlyGE n) ∧
        ∀ i : ℤ, TopCat.Sheaf.IsFlasque
          ((SheafOfModules.toSheaf (structureSheafRing X)).obj (G.X i)) := by
  obtain ⟨n, hn⟩ := hF
  have : F.IsStrictlyGE n := hn
  obtain ⟨G, f, hf, hGE, hfl⟩ :=
    exists_quasiIso_isStrictlyGE_isFlasque (structureSheafRing X) F n
  exact ⟨G, f, hf, ⟨n, hGE⟩, hfl⟩

end Stacks.Cohomology

end
