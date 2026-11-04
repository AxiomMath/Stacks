module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleSetBaseChangeMate

/-!
# The underlying sheaf of sets of the direct image and of étale restriction of modules

For a morphism `h : U ⟶ V` of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, the direct image of `𝒪_U`-modules of Stacks 03LU and the direct image
`AlgebraicGeometry.Space.smallEtaleDirectImage` of sheaves of sets on the small étale sites are
the same functor on underlying sheaves of sets, and for étale `h` so are étale restriction of
modules (Stacks 03LV) and restriction of sheaves of sets along small étale postcomposition.

Both hold by `rfl`: the direct image of modules applies the direct image of sheaves of sets to
the sheaf underlying a module and then restricts scalars along the structure map of Stacks 03G8,
and restriction of scalars does not change the underlying sheaf of sets; étale restriction only
reindexes sections.

These are the two commutation squares that the forgetful functor contributes to the cube along
which `Stacks.CategoryTheory.isIso_mateEquiv_symm_of_reflectsIsomorphisms` carries a base-change
statement about sheaves of sets to one about modules: with them the two comparisons of the
vertical functors of the cube are identities, and only the comparison of the two *left* adjoints
— étale restriction of modules against the inverse image of modules, which is Stacks 03LW —
remains.

## Main results

* `AlgebraicGeometry.Space.modulePushforward_comp_moduleSheafFunctor`
* `AlgebraicGeometry.Space.etaleModulePullback_comp_moduleSheafFunctor`

No `@[stacks]` attribute: neither statement is a numbered assertion.  Stacks 03LU is carried by
`AlgebraicGeometry.Space.modulePullbackAdjunction` and Stacks 03LV by
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback`.

## References

* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {U V : AlgebraicSpaces B S hS}

/-- **The direct image of modules is the direct image of sheaves of sets on underlying sheaves.**
Restriction of scalars along the structure map of Stacks 03G8 leaves the underlying sheaf of sets
alone. -/
theorem modulePushforward_comp_moduleSheafFunctor (h : U ⟶ V) :
    modulePushforward B S hS h ⋙ Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V) =
      Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U) ⋙
        smallEtaleDirectImage B S hS h :=
  rfl

/-- **Étale restriction of modules is restriction of sheaves of sets on underlying sheaves.**
Both only reindex sections along small étale postcomposition. -/
theorem etaleModulePullback_comp_moduleSheafFunctor (h : U ⟶ V) (hh : IsEtale B S hS h.hom) :
    etaleModulePullback.{u, u} B S hS h hh ⋙
        Sheaf.moduleSheafFunctor (structureRingSheaf B S hS U) =
      Sheaf.moduleSheafFunctor (structureRingSheaf B S hS V) ⋙
        smallEtaleSetRestriction B S hS h hh :=
  rfl

end AlgebraicGeometry.Space

end
