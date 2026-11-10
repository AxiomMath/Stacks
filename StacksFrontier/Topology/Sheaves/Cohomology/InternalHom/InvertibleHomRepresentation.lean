module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocallyFiniteFreeSummandBounded
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomRepresentation

/-!
# Derived internal Hom out of a bounded complex of invertible sheaves on a ringed space

Let `(X, O_X)` be a ringed space. Stacks 08JH represents the derived internal Hom
`RSheafHom(E, F)` by the ordinary internal Hom complex `SheafHom(E, F)` of Stacks 0A8Z when `E`
is strictly perfect — bounded, with every term a **global** direct summand of a finite free
`O_X`-module — and that is
`Stacks.SheafOfModules.strictlyPerfectHomComparison_isIso` in
`StrictlyPerfectHomRepresentation.lean` in this directory.

An invertible sheaf of modules is not such a global summand: on `P^1` there is no nonzero
morphism `O(1) ⟶ O^{⊕n}` at all. It is however rank-one locally free ([Stacks, Tag 0B8M]) and so
*locally* a direct summand of a finite free module, which is all the representation statement
needs. This file reads off, for a ringed space, the two ringed-site statements that supply the
local hypothesis: the single-degree one already in the library and the bounded one of the file
`LocallyFiniteFreeSummandBounded.lean` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/`.

## Main results

* `Stacks.SheafOfModules.strictlyPerfectHomComparison_isIso_of_isInvertible`: **an invertible
  sheaf of modules on a ringed space is its own derived dual** — the comparison is an
  isomorphism for a single-degree invertible source and any target.
* `Stacks.SheafOfModules.strictlyPerfectHomComparison_isIso_of_bounded_isLocallyFiniteFreeSummand`
  and `Stacks.SheafOfModules.strictlyPerfectHomComparison_isIso_of_bounded_isInvertible`:
  the same for a bounded source whose terms are only locally direct summands of finite free
  modules, and in particular for a bounded complex of invertible sheaves of modules.

## Implementation notes

A topological space with a sheaf of commutative rings *is* a ringed site, namely the site of its
opens with the open-cover topology, so each statement below is the site-level term type-checked
against the space-level statement, with no comparison layer between the two settings — exactly as
in `StrictlyPerfectHomRepresentation.lean` and in `DerivedInternalHom.lean` in this directory.

The site statements ask for `HasWeakSheafify` and `WEqualsLocallyBijective` over every slice
topology as well as over the site itself. For the site of opens of a space those are resolved by
instance search from the two hypotheses on the space, so they appear in none of the statements
below.

The invertibility hypothesis is `Stacks.SheafOfModules.IsInvertible` of [Stacks, Tag 01CS],
stated for the presheaf of commutative rings underlying the structure sheaf together with its
sheaf condition; for the ringed site of a space those are `Rc.obj` and
`(structureSheaf Rc).property`.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **An invertible sheaf of modules on a ringed space is its own derived dual.** For an
invertible sheaf of `O_X`-modules `L`, any degree `k` and any target complex `F`, the canonical
comparison

`Q(SheafHom(L[k], F)) ⟶ RSheafHom(L[k], F)`

is an isomorphism; at `k = 0` and `F = O_X[0]` the source is the class of the Hom complex
computing the dual sheaf `L^∨ = SheafHom(L, O_X)`, so the derived dual of `L` is its underived
dual.

The global hypothesis of `Stacks.SheafOfModules.strictlyPerfectHomComparison_isIso` is
unavailable — an invertible sheaf is in general not a direct summand of a finite free module —
and unnecessary: `L` is rank-one locally free ([Stacks, Tag 0B8M]) hence locally such a summand,
which is what the representation statement needs. -/
theorem strictlyPerfectHomComparison_isIso_of_isInvertible (k : ℤ)
    (L : StructureSheafModules Rc) [IsInvertible Rc.obj (structureSheaf Rc).property L]
    (F : CochainComplex (StructureSheafModules Rc) ℤ) :
    IsIso (strictlyPerfectHomComparison Rc
      ((HomologicalComplex.single (StructureSheafModules Rc) (ComplexShape.up ℤ) k).obj L) F) :=
  RingedSite.strictlyPerfectHomComparison_isIso_of_isInvertible
    (ringedSite Rc) (derivedInternalHom Rc) k L F

/-- **Stacks 08JH on a ringed space for a bounded source whose terms are only locally direct
summands of finite free modules.** If `E` has finitely many nonzero terms and each of them is
locally a direct summand of a finite free `O_X`-module then, for every target `F`, the canonical
comparison from the class of the internal Hom complex `SheafHom(E, F)` to the derived internal
Hom `RSheafHom(E, F)` is an isomorphism. -/
theorem strictlyPerfectHomComparison_isIso_of_bounded_isLocallyFiniteFreeSummand
    (E F : CochainComplex (StructureSheafModules Rc) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i, RingedSite.IsLocallyFiniteFreeSummand (ringedSite Rc) (E.X i)) :
    IsIso (strictlyPerfectHomComparison Rc E F) :=
  RingedSite.strictlyPerfectHomComparison_isIso_of_bounded_isLocallyFiniteFreeSummand
    (ringedSite Rc) (derivedInternalHom Rc) E F hbdd hterm

/-- **A bounded complex of invertible sheaves of modules on a ringed space is its own derived
dual.** For a bounded complex `E` of invertible sheaves of `O_X`-modules and any target `F`, the
canonical comparison `Q(SheafHom(E, F)) ⟶ RSheafHom(E, F)` is an isomorphism.

This is the shape the local computation of [Stacks, Tag 0B4B] needs: there the source is the
two-term complex `(ℐ_D ⟶ 𝒪_X)` resolving `i_* 𝒪_D` for an effective Cartier divisor, both of
whose terms are invertible. -/
theorem strictlyPerfectHomComparison_isIso_of_bounded_isInvertible
    (E F : CochainComplex (StructureSheafModules Rc) ℤ)
    (hbdd : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i, IsInvertible Rc.obj (structureSheaf Rc).property (E.X i)) :
    IsIso (strictlyPerfectHomComparison Rc E F) :=
  RingedSite.strictlyPerfectHomComparison_isIso_of_bounded_isInvertible
    (ringedSite Rc) (derivedInternalHom Rc) E F hbdd hterm

end Stacks.SheafOfModules

end
