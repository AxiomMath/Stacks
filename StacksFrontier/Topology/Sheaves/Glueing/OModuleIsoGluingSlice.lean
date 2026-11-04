module

public import StacksFrontier.Topology.Sheaves.Glueing.OModuleMapGluingSlice
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartModuleRestrictionExact

/-!
# Gluing an isomorphism of sheaves of modules given over the members of an open cover

`Stacks.SheafOfModules.existsUnique_hom_of_overMap_eq_of_isBasis` glues a *morphism* of sheaves
of modules out of morphisms over the members of an open covering which agree over the members of
a prescribed basis.  A local-to-global argument whose local data are *isomorphisms* wants the
glued morphism to be an isomorphism as well, and that is not part of the glueing.

This file puts the two together.  Nothing else is used: the glued morphism restricts to the given
isomorphism on each member of the covering by the defining property of the glueing, so it is
invertible there, and restriction to the slices at a covering family is jointly conservative by
`Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map`.  The sheaf of rings is arbitrary, so this
applies in particular to the Frobenius colimit `colim_F 𝒪_X` of [Stacks, Tag 0EXB], which is not
the structure sheaf of any ringed space in this development.

It is the form in which the final Zariski glueing of [Stacks, Tag 0EXD] assembles the two
component isomorphisms of an isomorphism in a categorical fibre product:  the covering of the
base is by basic opens, because only over a basic open is the almost blowup square of
[Stacks, Example 0EVH] again a two-generator square, and over such a member the comparison is
available only as an *isomorphism* of the local solutions, not as a morphism between two globally
given modules.

## Implementation notes

The compatibility hypothesis is the one of
`Stacks.SheafOfModules.existsUnique_hom_of_overMap_eq_of_isBasis`, on the `CategoryTheory.Iso.hom`
of the local isomorphisms:  an equality of *morphisms* over a basis open below two members of the
covering.  Asking instead for an equality of the local isomorphisms themselves would be the same
statement, since an isomorphism is determined by its underlying morphism, but it would force every
consumer to repackage.

The conclusion records the glued isomorphism together with its restrictions, rather than merely
the existence of an isomorphism:  a consumer that has to glue a *second* isomorphism compatibly --
as the two components of an isomorphism in a categorical fibre product have to be -- needs to know
what the glued one restricts to.

## Main results

* `Stacks.SheafOfModules.exists_iso_of_overMap_eq_of_isBasis`: **isomorphisms of sheaves of
  modules over the members of an open covering whose slice restrictions to the members of a basis
  agree glue to an isomorphism**, restricting to the given one on each member.

## References

* [Stacks Project, Tag 00AN](https://stacks.math.columbia.edu/tag/00AN)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

variable {X : TopCat.{u}} {R : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}}
  {M N : _root_.SheafOfModules.{u} R} {ι : Type u}

/-- **Isomorphisms of sheaves of modules given over the members of an open covering whose slice
restrictions to the members of a basis agree glue to an isomorphism of the two sheaves**, whose
restriction to each member of the covering is the given isomorphism.

The underlying morphism is glued by
`Stacks.SheafOfModules.existsUnique_hom_of_overMap_eq_of_isBasis`; it restricts to `(φ i).hom` on
the `i`-th member of the covering, so it is invertible there, and
`Stacks.SheafOfModules.isIso_of_isIso_overFunctor_map` makes it invertible, the covering family of
the terminal object being `TopologicalSpace.Opens.coversTop_iff` applied to the covering.

The sheaf of rings `R` is arbitrary; in particular it need not be the structure sheaf of a ringed
space. -/
theorem exists_iso_of_overMap_eq_of_isBasis
    {B : Set (Opens (X : TopCat))} (hB : Opens.IsBasis B)
    (V : ι → Opens (X : TopCat)) (hV : ⨆ i, V i = ⊤)
    (φ : ∀ i, M.over (V i) ≅ N.over (V i))
    (hφ : ∀ (i j : ι) (W : Opens (X : TopCat)), W ∈ B → ∀ (hWi : W ≤ V i) (hWj : W ≤ V j),
      (_root_.SheafOfModules.overMap R (homOfLE hWi)).map (φ i).hom =
        (_root_.SheafOfModules.overMap R (homOfLE hWj)).map (φ j).hom) :
    ∃ ψ : M ≅ N, ∀ i, (_root_.SheafOfModules.overFunctor R (V i)).mapIso ψ = φ i := by
  obtain ⟨ψ, hψ, -⟩ :=
    existsUnique_hom_of_overMap_eq_of_isBasis hB V hV (fun i => (φ i).hom) hφ
  have hiso : IsIso ψ :=
    isIso_of_isIso_overFunctor_map
      ((Opens.coversTop_iff X V).2 (TopologicalSpace.IsOpenCover.mk hV)) ψ
      fun i => by rw [hψ i]; infer_instance
  exact ⟨asIso ψ, fun i => Iso.ext (hψ i)⟩

end Stacks.SheafOfModules

end
