module

public import Mathlib.Algebra.Homology.QuasiIso
public import StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplexComparison

/-!
# The alternating Čech complex computes Čech cohomology over the base ring, linearly

Let `A` be a commutative ring, let `f : X ⟶ Spec A` be a scheme over the affine base, let `F` be
a sheaf of `𝒪_X`-modules and let `U : I → X.Opens` be a family of open subsets indexed by a
linearly ordered type. The Čech complex of `F` with respect to `U` and its alternating
subcomplex are both complexes of `A`-modules, `Stacks.Cech.cechModuleComplex` and
`Stacks.Cech.alternatingCechModuleComplex`, and the inclusion of the second into the first is
`A`-linear.

Stacks 01FM says that inclusion is a homotopy equivalence. The library has that statement for
presheaves of abelian groups — `Stacks.Cech.alternatingCechInclusion_homotopyEquivalence`, and
its transport to Mathlib's Čech complex
`Stacks.Cech.alternatingCechModuleComplexToCechComplexFunctor_homotopyEquivalence` — where the
`A`-module structures have been forgotten. This file removes that forgetful functor: the
`A`-linear inclusion is a quasi-isomorphism of complexes of `A`-modules, so the alternating Čech
complex computes Čech cohomology **as `A`-modules** and not merely as abelian groups.

## Main definitions

* `Stacks.Cech.alternatingCechModuleHomologyIso` — **the cohomology of the alternating Čech
  complex of `A`-modules is the Čech cohomology of `F` for the family `U`**, in every degree, as
  `A`-modules.

## Main results

* `Stacks.Cech.quasiIsoAt_alternatingCechModuleComplex_inclusion` — **Stacks 01FM, `A`-linearly.**
  The inclusion of the alternating Čech complex of `A`-modules into the usual one is a
  quasi-isomorphism in `ModuleCat A`.
* `Stacks.Cech.isIso_homologyMap_map_alternatingCechModuleComplex_inclusion` — the same statement
  after forgetting the module structures, which is where Stacks 01FM is consumed.

## Implementation notes

**Why no homotopy is ported.** Stacks 01FM is proved by signed sorting of the index tuples. That
construction is additive but carries no linearity, and the chain homotopy witnessing it is
internal to `StacksFrontier.Topology.Sheaves.Cohomology.Cech.AlternatingHomotopyEquivalence`. None
of it has to be lifted: `forget₂ (ModuleCat A) AddCommGrpCat` is exact, hence preserves homology,
and it reflects isomorphisms, so `HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology`
turns the abelian-group-level statement into the `A`-linear one. The only input needed beyond
Stacks 01FM itself is that the forgetful image of
`Stacks.Cech.alternatingCechModuleComplex_inclusion` *is* the inclusion of Stacks 01FH, which is
`Stacks.Cech.alternatingCechModuleComplex_inclusion_forget`; that holds degreewise by `rfl`,
because the two `_forget` identifications of
`StacksFrontier.AlgebraicGeometry.Modules.AlternatingCechModuleComplex` are `Iso.refl`-valued. So
the chosen homotopy inverse of Stacks 01FM never appears here, and no statement is weakened in
passing from abelian groups to `A`-modules.

The same transfer for the slice-site Čech complex of a sheaf of modules over a sheaf of rings,
where the coefficients are modules over `R(V)` rather than over a fixed base ring `A`, is
`Stacks.Cohomology.CechSheaf.quasiIsoAt_alternatingModuleInclusion`. The two developments are
linear over different rings — they differ by restriction of scalars along
`Stacks.Cech.globalRingHom` — so neither subsumes the other.

**No `@[stacks]` attribute.** Stacks 01FM already carries its statement on
`Stacks.Cech.alternatingCechInclusion_homotopyEquivalence`; what is added here is the module
structure, which refines that statement rather than stating a different clause of the tag.

## References

* [Stacks Project, Tag 01FH](https://stacks.math.columbia.edu/tag/01FH)
* [Stacks Project, Tag 01FM](https://stacks.math.columbia.edu/tag/01FM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry

universe u

noncomputable section

namespace Stacks.Cech

variable {A : Type u} [CommRing A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
  {I : Type u} (U : I → X.Opens) (F : X.Modules) [LinearOrder I]

/-- **Stacks 01FM, after forgetting the module structures.** The forgetful image of the
`A`-linear inclusion of the alternating Čech complex induces an isomorphism on homology: it is
the inclusion of Stacks 01FH up to two isomorphisms of complexes, and that inclusion is a
homotopy equivalence by Stacks 01FM. -/
theorem isIso_homologyMap_map_alternatingCechModuleComplex_inclusion (p : ℕ) :
    IsIso (HomologicalComplex.homologyMap
      (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex
        (ComplexShape.up ℕ)).map (alternatingCechModuleComplex_inclusion f U F)) p) := by
  have hAb : IsIso (HomologicalComplex.homologyMap
      (alternatingCechInclusion U F.presheaf) p) := by
    obtain ⟨e, he⟩ := alternatingCechInclusion_homotopyEquivalence U F.presheaf
    rw [← he]
    exact (e.toHomologyIso p).isIso_hom
  rw [← alternatingCechModuleComplex_inclusion_forget f U F,
    HomologicalComplex.homologyMap_comp, HomologicalComplex.homologyMap_comp,
    isIso_comp_left_iff, isIso_comp_right_iff] at hAb
  exact hAb

/-- After forgetting the module structures, the inclusion of the alternating Čech complex of
`A`-modules into the Čech complex of `A`-modules is a quasi-isomorphism in every degree. -/
instance quasiIsoAt_map_alternatingCechModuleComplex_inclusion (p : ℕ) :
    QuasiIsoAt (((forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}).mapHomologicalComplex
      (ComplexShape.up ℕ)).map (alternatingCechModuleComplex_inclusion f U F)) p :=
  (quasiIsoAt_iff_isIso_homologyMap _ p).2
    (isIso_homologyMap_map_alternatingCechModuleComplex_inclusion f U F p)

/-- **Stacks 01FM, `A`-linearly.** For a linearly ordered index type the inclusion of the
alternating Čech complex of `A`-modules into the usual Čech complex of `A`-modules is a
quasi-isomorphism of complexes of `A`-modules: `forget₂ (ModuleCat A) AddCommGrpCat` is exact
and reflects isomorphisms, so the abelian-group-level statement of Stacks 01FM transfers. -/
instance quasiIsoAt_alternatingCechModuleComplex_inclusion (p : ℕ) :
    QuasiIsoAt (alternatingCechModuleComplex_inclusion f U F) p :=
  (HomologicalComplex.quasiIsoAt_map_iff_of_preservesHomology
    (alternatingCechModuleComplex_inclusion f U F)
    (forget₂ (ModuleCat.{u} A) AddCommGrpCat.{u}) p).1
    (quasiIsoAt_map_alternatingCechModuleComplex_inclusion f U F p)

/-- **The alternating Čech complex computes Čech cohomology over the base ring, as a module.**
For a linearly ordered index type the degree-`p` cohomology of the alternating Čech complex of
`A`-modules is the degree-`p` Čech cohomology of `F` for the family `U`, as `A`-modules — no
forgetful functor appears. -/
def alternatingCechModuleHomologyIso (p : ℕ) :
    (alternatingCechModuleComplex f U F).homology p ≅
      (cechModuleComplex f U F).homology p :=
  asIso (HomologicalComplex.homologyMap (alternatingCechModuleComplex_inclusion f U F) p)

end Stacks.Cech

end

end
