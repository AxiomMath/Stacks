module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFree.Local

/-!
# The tautological inclusions through the free comparison of a restriction

`Stacks.Modules.restrictFreeIso` identifies the restriction along an open immersion `g : T ⟶ S`
of the free `𝒪_S`-module on `I` with the free `𝒪_T`-module on `I`.  It is Mathlib's
`CategoryTheory.SheafOfModules.mapFreeIso` for the restriction functor, fed the structure-sheaf
comparison `AlgebraicGeometry.Scheme.Modules.restrictUnitIso`, and **nothing in the repository
computes it**:  it is a bare `def`, and every statement about a composite in which it occurs has
had to be left unproved.

This file supplies the two computing lemmas.  A free sheaf of modules is a coproduct of copies of
the structure sheaf, so a morphism out of it is determined by its restrictions along the
tautological inclusions `CategoryTheory.SheafOfModules.ιFree`, and the two lemmas below say what
`Stacks.Modules.restrictFreeIso` does to those:  in both directions it is the structure-sheaf
comparison `restrictUnitIso`, with the tautological inclusion carried along.  Every coherence of
`restrictFreeIso` therefore reduces, through
`CategoryTheory.Limits.Cofan.IsColimit.hom_ext` at `CategoryTheory.SheafOfModules.freeCofan`,
to the corresponding coherence of `restrictUnitIso`.

## The instance that is not found

`CategoryTheory.SheafOfModules.mapFreeIso` asks for
`CategoryTheory.Limits.PreservesColimitsOfShape (Discrete I)` of the functor, and instance search
does not find it for `AlgebraicGeometry.Scheme.Modules.restrictFunctor`:  the category structure
on `AlgebraicGeometry.Scheme.Modules` is a different instance from the one on
`CategoryTheory.SheafOfModules`, so the discrimination tree misses.  The definition of
`restrictFreeIso` supplies it as a `letI`, which is therefore invisible from outside, and the
lemmas here supply it the same way -- as an explicit argument of an `@`-application -- rather than
by `haveI`, which would be defeated by the same miss.

## Main results

* `Stacks.Modules.hom_ext_free`: **two morphisms out of a free sheaf of modules agree as soon as
  they agree after every tautological inclusion**, with the sheaf of rings in the scheme spelling.
* `Stacks.Modules.ιFree_restrictFreeIso_inv`: **the inverse of the free comparison carries the
  `i`-th tautological inclusion to the inverse of the structure-sheaf comparison followed by the
  restriction of the `i`-th tautological inclusion.**  This is the form in which a coherence whose
  two sides are morphisms *out of* a free module is reduced to the unit.
* `Stacks.Modules.restrictFunctor_map_ιFree_comp_restrictFreeIso_hom`: **the free comparison
  carries the restriction of the `i`-th tautological inclusion to the structure-sheaf comparison
  followed by the `i`-th tautological inclusion.**

## References

* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace
open AlgebraicGeometry.Scheme.Modules (restrictFunctor)

universe u

namespace Stacks.Modules

variable {T S : Scheme.{u}} (g : T ⟶ S) [IsOpenImmersion g] (I : Type u)

/-- The coproduct-preservation instance of the restriction functor at a discrete index type, in
the shape `CategoryTheory.SheafOfModules.mapFreeIso` consumes it.  Instance search does not find
it; see the module docstring. -/
theorem preservesColimitsOfShape_discrete_restrictFunctor :
    PreservesColimitsOfShape.{u, u} (Discrete I) (restrictFunctor g) :=
  Functor.instPreservesColimitsOfShapeOfIsLeftAdjoint.{u, u, u, u + 1, u, u + 1}
    (restrictFunctor g)

/-- **Two morphisms out of a free sheaf of modules on a scheme agree as soon as they agree after
every tautological inclusion.**

This is `CategoryTheory.Limits.Cofan.IsColimit.hom_ext` at
`CategoryTheory.SheafOfModules.isColimitFreeCofan`, restated so that its hypothesis is spelled
with the sheaf of rings written as `AlgebraicGeometry.Scheme.ringCatSheaf`.  The restatement is
not cosmetic:  the colimit of Mathlib spells the sheaf of rings through the Grothendieck topology
of the opens of the scheme, and although the two spellings are definitionally equal, `simp` and
`rw` compare them syntactically, so a goal produced by `Cofan.IsColimit.hom_ext` directly is not
matched by any lemma stated in the scheme spelling -- including the two below. -/
theorem hom_ext_free {T : Scheme.{u}} (I : Type u) {M : T.Modules}
    (φ ψ : SheafOfModules.free (R := T.ringCatSheaf) I ⟶ M)
    (hι : ∀ i : I, SheafOfModules.ιFree (R := T.ringCatSheaf) i ≫ φ =
      SheafOfModules.ιFree (R := T.ringCatSheaf) i ≫ ψ) :
    φ = ψ :=
  Cofan.IsColimit.hom_ext (SheafOfModules.isColimitFreeCofan I) φ ψ hι

/-- **The inverse of the free comparison carries the `i`-th tautological inclusion to the inverse
of the structure-sheaf comparison followed by the restriction of the `i`-th tautological
inclusion.**

This is Mathlib's `CategoryTheory.SheafOfModules.ιFree_mapFreeIso_hom` at the functor
`AlgebraicGeometry.Scheme.Modules.restrictFunctor g` and the comparison
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso g`, which is what
`Stacks.Modules.restrictFreeIso` is the inverse of. -/
theorem ιFree_restrictFreeIso_inv (i : I) :
    SheafOfModules.ιFree (R := T.ringCatSheaf) i ≫ (restrictFreeIso g I).inv =
      (Scheme.Modules.restrictUnitIso g).inv ≫
        (restrictFunctor g).map (SheafOfModules.ιFree (R := S.ringCatSheaf) i) :=
  @SheafOfModules.ιFree_mapFreeIso_hom _ _ _ _ _ _ _ _ _ _ _ _ (restrictFunctor g) I
    (preservesColimitsOfShape_discrete_restrictFunctor g I)
    (Scheme.Modules.restrictUnitIso g).symm i

/-- **The free comparison carries the restriction of the `i`-th tautological inclusion to the
structure-sheaf comparison followed by the `i`-th tautological inclusion.**

This is Mathlib's `CategoryTheory.SheafOfModules.map_ιFree_mapFreeIso_inv` at the same data, and
it is `Stacks.Modules.ιFree_restrictFreeIso_inv` read on the other side of the two
isomorphisms. -/
theorem restrictFunctor_map_ιFree_comp_restrictFreeIso_hom (i : I) :
    (restrictFunctor g).map (SheafOfModules.ιFree (R := S.ringCatSheaf) i) ≫
        (restrictFreeIso g I).hom =
      (Scheme.Modules.restrictUnitIso g).hom ≫ SheafOfModules.ιFree (R := T.ringCatSheaf) i :=
  @SheafOfModules.map_ιFree_mapFreeIso_inv _ _ _ _ _ _ _ _ _ _ _ _ (restrictFunctor g) I
    (preservesColimitsOfShape_discrete_restrictFunctor g I)
    (Scheme.Modules.restrictUnitIso g).symm i

end Stacks.Modules

end
