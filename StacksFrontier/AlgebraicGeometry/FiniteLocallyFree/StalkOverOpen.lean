module

public import StacksFrontier.AlgebraicGeometry.Divisors.RankLocalGenerators
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.DeterminantInvertible
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.LocallyFreeSite
public import StacksFrontier.AlgebraicGeometry.StalkFreeBridge.StalkFree

/-!
# Finite local freeness over an open, read at a point of that open

A module on a scheme which is finite locally free over an open `V`, in the slice-site spelling
of [Stacks, Tag 01C6], has a free stalk of finite rank at every point of `V`, and is of finite
presentation on a neighbourhood of that point. This is what the conclusion of [Stacks, Tag 0811]
is consumed as in the flattening theorem [Stacks, Tag 0815].

The trivialising covering family of `M.over V` lives on the slice site over `V`; one of its
members has an underlying open containing the given point
(`AlgebraicGeometry.Scheme.Modules.exists_mem_left_of_coversTop`), and over that member the
module is isomorphic to a free module on a finite index type. Descending that trivialisation
from the iterated slice to the slice over the open itself
(`AlgebraicGeometry.Scheme.Modules.freeIsoOverLeft`) gives generating sections of `M` over an
open neighbourhood of the point whose structure map is invertible, which is the input of both
conclusions: `Stacks.StalkFreeBridge.nonempty_stalkLinearEquiv` identifies the stalk with the
finitely supported functions on the index type, and `Stacks.Modules.restrictIsoFree` turns the
same trivialisation into one of the restriction, whence of the pullback.

## Main results

* `AlgebraicGeometry.exists_generatingSections_of_isFiniteLocallyFree_over`: the trivialisation
  at a point of the open, with its index type finite.
* `AlgebraicGeometry.free_stalk_finitePresentation_of_generatingSections`: the same conclusion
  from a finite free presentation over one open, which is what the pointwise form of the
  conclusion of [Stacks, Tag 0811] supplies directly.
* `AlgebraicGeometry.free_stalk_finitePresentation_of_isFiniteLocallyFree_over`: **the
  consequences of the conclusion of [Stacks, Tag 0811] at a point of the free open** — a finite
  free stalk, and finite presentation on a neighbourhood.

## References

* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- A module finite locally free over an open has, over a member of its trivialising covering
family whose underlying open contains a given point of that open, an isomorphism with a free
module on a finite index type. -/
private theorem exists_freeIso_over_of_isFiniteLocallyFree_over
    {X : Scheme.{u}} (M : X.Modules) (V : X.Opens)
    (hV : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (M.over V)) {z : X} (hz : z ∈ V) :
    ∃ (W : Over V) (_ : z ∈ W.left) (I : Type u) (_ : Finite I),
      Nonempty (SheafOfModules.free.{u} I ≅ (M.over V).over W) := by
  obtain ⟨q, hfree, hfin⟩ := hV.exists_isFiniteLocallyFreeData
  obtain ⟨i, hzi⟩ := Scheme.Modules.exists_mem_left_of_coversTop V q.X q.coversTop hz
  exact ⟨q.X i, hzi, (q.generators i).I, (hfin.isFiniteType i).finite,
    ⟨@asIso _ _ _ _ (q.generators i).π (hfree.isIso i)⟩⟩

/-- **A module finite locally free over an open is trivialised near every point of that open.**
On an open neighbourhood `W` of the point there are generating sections of `M.over W`, indexed
by a finite type, whose structure map is an isomorphism. -/
theorem exists_generatingSections_of_isFiniteLocallyFree_over
    {X : Scheme.{u}} (M : X.Modules) (V : X.Opens)
    (hV : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (M.over V)) {z : X} (hz : z ∈ V) :
    ∃ (W : X.Opens) (_ : z ∈ W) (σ : (M.over W).GeneratingSections),
      IsIso σ.π ∧ Finite σ.I := by
  obtain ⟨W, hzW, I, hIfin, ⟨e⟩⟩ := exists_freeIso_over_of_isFiniteLocallyFree_over M V hV hz
  exact ⟨W.left, hzW,
    (SheafOfModules.free.generatingSections (R := X.ringCatSheaf.over W.left) I).ofEpi
      (Scheme.Modules.freeIsoOverLeft M V W I e).hom,
    Stacks.SheafOfModules.isIso_generatingSections_ofEpi _, hIfin⟩

/-- **From a finite free presentation on an open to the stalk and a neighbourhood.** If a module
has generating sections over an open `W`, indexed by a finite type and with invertible structure
map, then at every point of `W` its stalk is finite free over the local ring, and it is of finite
presentation on a neighbourhood. -/
theorem free_stalk_finitePresentation_of_generatingSections {X : Scheme.{u}} (M : X.Modules)
    (W : X.Opens) (σ : (M.over W).GeneratingSections) (hσ : IsIso σ.π) (hIfin : Finite σ.I)
    (z : X) (hz : z ∈ W) :
    Module.Free (X.presheaf.stalk z) (M.presheaf.stalk z) ∧
      Module.Finite (X.presheaf.stalk z) (M.presheaf.stalk z) ∧
      ∃ V₂ : X.Opens, z ∈ V₂ ∧
        ((Scheme.Modules.pullback V₂.ι).obj M).IsFinitePresentation := by
  obtain ⟨e⟩ := Stacks.StalkFreeBridge.nonempty_stalkLinearEquiv W M σ hz
  let b : Module.Basis σ.I (X.presheaf.stalk z) (M.presheaf.stalk z) := Module.Basis.ofRepr e
  refine ⟨Module.Free.of_basis b, Module.Finite.of_basis b, W, hz, ?_⟩
  exact (SheafOfModules.isFinitePresentation W.toScheme.ringCatSheaf).prop_of_iso
    ((Stacks.Modules.restrictIsoFree W M σ.I (asIso σ.π)).symm ≪≫
      (Scheme.Modules.restrictFunctorIsoPullback W.ι).app M)
    (Stacks.AlgebraicGeometry.ModuleLimits.isFinitePresentation_free_of_finite W.toScheme σ.I)

/-- **The consequences of the conclusion of [Stacks, Tag 0811] at a point of the free open.**
Where a module is finite locally free, in the slice-site spelling, its stalk is finite free over
the local ring there, and the module is of finite presentation on a neighbourhood. -/
theorem free_stalk_finitePresentation_of_isFiniteLocallyFree_over
    {X : Scheme.{u}} (M : X.Modules) (V : X.Opens)
    (hV : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (M.over V)) (z : X) (hz : z ∈ V) :
    Module.Free (X.presheaf.stalk z) (M.presheaf.stalk z) ∧
      Module.Finite (X.presheaf.stalk z) (M.presheaf.stalk z) ∧
      ∃ V₂ : X.Opens, z ∈ V₂ ∧
        ((Scheme.Modules.pullback V₂.ι).obj M).IsFinitePresentation := by
  obtain ⟨W, hzW, σ, hσ, hIfin⟩ :=
    exists_generatingSections_of_isFiniteLocallyFree_over M V hV hz
  exact free_stalk_finitePresentation_of_generatingSections M W σ hσ hIfin z hzW

end AlgebraicGeometry

end
