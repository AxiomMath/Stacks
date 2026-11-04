module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleDualEvaluation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.LocallyFiniteFreeSummandSource
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.StrictlyPerfectHomFiniteFree

/-!
# Derived internal Hom out of a locally finite free single term

Let `(C, O)` be a ringed site. Stacks 08JH identifies the derived internal Hom
`RSheafHom(E, F)` with the ordinary internal Hom complex `SheafHom(E, F)` when `E` is *strictly
perfect*, that is bounded with every term a **global** direct summand of a finite free
`O`-module. That hypothesis is stronger than the geometry supplies: an invertible sheaf of
modules is only *locally* a direct summand of a finite free module, and in general is not one
globally — on `P^1` there is no nonzero morphism `O(1) ⟶ O^{⊕n}` at all. For a source
concentrated in a single degree the local hypothesis suffices:

`Q(SheafHom(A[k], F)) ⟶ RSheafHom(A[k], F)` is an isomorphism

whenever `A` is locally a direct summand of a finite free `O`-module, and in particular
whenever `A` is an invertible sheaf of `O`-modules. In the invertible case the left-hand side
is the (underived) dual sheaf `A^∨ = SheafHom(A, O)` when `F = O[0]`, so this is the statement
that **an invertible sheaf of modules is its own derived dual**.

The proof is a cancellation and a covering, with no new mathematics beyond its two inputs:
`AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_iff` reduces invertibility of
the comparison to quasi-isomorphy of the map of internal Hom complexes induced by the
K-injective augmentation of the target, and
`AlgebraicGeometry.RingedSite.homMap_single_quasiIso_of_isLocallyFiniteFreeSummand` discharges
that from the local hypothesis. Neither input constrains the target `F`.

## Main results

* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_isLocallyFiniteFreeSummand`:
  the comparison to derived internal Hom is an isomorphism for a single-degree source which is
  locally a direct summand of a finite free module.
* `AlgebraicGeometry.RingedSite.isLocallyFiniteFreeSummand_of_isInvertible`: an invertible sheaf
  of modules on a ringed site is locally a direct summand of a finite free module.
* `AlgebraicGeometry.RingedSite.strictlyPerfectHomComparison_isIso_of_isInvertible`: **an
  invertible sheaf of modules is its own derived dual** — the comparison is an isomorphism for a
  single-degree invertible source.

## Implementation notes

The covering family witnessing the local hypothesis for an invertible sheaf is the canonical one
of `Stacks.SheafOfModules.InvertibleSummandIndex`, whose objects cover the final object by
`Stacks.SheafOfModules.coversTop_invertibleSummandObj` (the site form of Stacks 0B8N (b)). That
index type already lives in the universe of the objects of the site, which is the universe
`AlgebraicGeometry.RingedSite.IsLocallyFiniteFreeSummand` asks for, so no reindexing is needed.
The splittings it carries are retracts onto `SheafOfModules.free`, and
`AlgebraicGeometry.RingedSite.isFiniteFreeSummand_of_retract_free` converts those into the
iterated-biproduct spelling `AlgebraicGeometry.RingedSite.IsFiniteFreeSummand`.

The invertibility hypothesis is `Stacks.SheafOfModules.IsInvertible` of Stacks 01CS, stated for
the presheaf of commutative rings underlying the structure sheaf together with its sheaf
condition; for a ringed site those are `X.O.obj` and
`(Stacks.SheafOfModules.Tensor.ringSheaf X.O).property`, and the structure sheaf they assemble
to is `Stacks.SheafOfModules.Tensor.ringSheaf X.O` on the nose.

That an invertible sheaf of modules on a ringed **space** is locally a direct summand of a
finite free module is already
`Stacks.SheafOfModules.LocallyFiniteFree.isLocallyFiniteFreeSummand_of_isInvertible`, which
carries the Stacks 0B8K clause; the
statement below is the same content over an arbitrary site, phrased against the ringed-site
predicate that the Stacks 08JH development consumes, so it carries no attribute of its own.

The two slice spellings of sheaves of modules over the site over `V` — indexed by the structure
sheaf of `X.over V` and by the restriction to `V` of the structure sheaf of `X` — agree, and the
local `implicit_reducible` attributes below are what lets the elaborator see it, exactly as for
`AlgebraicGeometry.RingedSite.homMap_single_quasiIso_of_isLocallyFiniteFreeSummand`.

## References

* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0B8K](https://stacks.math.columbia.edu/tag/0B8K)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u d

namespace AlgebraicGeometry.RingedSite

attribute [local implicit_reducible]
  CategoryTheory.sheafCompose
  CategoryTheory.Functor.sheafPushforwardContinuous
  SheafOfModules.pushforward
  SheafOfModules.overFunctor

variable (X : RingedSite.{u, u, u})

/-- **An invertible sheaf of modules on a ringed site is locally a direct summand of a finite
free module.**

The covering family is the canonical one attached to the invertible sheaf,
`Stacks.SheafOfModules.InvertibleSummandIndex`: its objects cover the final object by
`Stacks.SheafOfModules.coversTop_invertibleSummandObj`, and each of them carries a splitting of
the restriction onto a finite free sheaf of modules.

This is the content of the Stacks 0B8K clause carried, for a ringed space, by
`Stacks.SheafOfModules.LocallyFiniteFree.isLocallyFiniteFreeSummand_of_isInvertible`, stated
here against the ringed-site predicate. -/
theorem isLocallyFiniteFreeSummand_of_isInvertible
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
    [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L] :
    IsLocallyFiniteFreeSummand X L := by
  refine ⟨Stacks.SheafOfModules.InvertibleSummandIndex X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L,
    Stacks.SheafOfModules.invertibleSummandObj,
    Stacks.SheafOfModules.coversTop_invertibleSummandObj _ _ _, fun k => ?_⟩
  exact isFiniteFreeSummand_of_retract_free (X.over _)
    (ULift.{u} (Fin (Stacks.SheafOfModules.invertibleSummandRank k)))
    (Stacks.SheafOfModules.invertibleSummandRetract k)

variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))]
  (D : DerivedInternalHom.{u, d} X)

/-- **Stacks 08JH for a single-degree source which is only locally a direct summand of a finite
free module.** If `A` is locally a direct summand of a finite free `O`-module then, for every
target `F`, the canonical comparison from the class of the internal Hom complex
`SheafHom(A[k], F)` to the derived internal Hom `RSheafHom(A[k], F)` is an isomorphism.

By `strictlyPerfectHomComparison_isIso_iff` this is the quasi-isomorphy of the map of internal
Hom complexes induced by the K-injective augmentation of `F`, which is
`homMap_single_quasiIso_of_isLocallyFiniteFreeSummand`. The global hypothesis of
`strictlyPerfectHomComparison_isIso` is not available here, and is not needed. -/
theorem strictlyPerfectHomComparison_isIso_of_isLocallyFiniteFreeSummand
    (k : ℤ) {A : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (hA : IsLocallyFiniteFreeSummand X A)
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsIso (strictlyPerfectHomComparison X D
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj A) F) :=
  (strictlyPerfectHomComparison_isIso_iff X D _ F).2
    (homMap_single_quasiIso_of_isLocallyFiniteFreeSummand X
      ((kInjectiveAugmentation X).app F) k hA)

/-- **An invertible sheaf of modules is its own derived dual.** For an invertible sheaf of
`O`-modules `L` and any target `F`, the canonical comparison

`Q(SheafHom(L[k], F)) ⟶ RSheafHom(L[k], F)`

is an isomorphism; at `F = O[0]` and `k = 0` the source is the class of the Hom complex
computing the dual sheaf `L^∨ = SheafHom(L, O)`, so the derived dual of `L` is its underived
dual.

An invertible sheaf of modules is rank-one locally free, hence locally a direct summand of a
finite free module (`isLocallyFiniteFreeSummand_of_isInvertible`), which is the hypothesis of
`strictlyPerfectHomComparison_isIso_of_isLocallyFiniteFreeSummand`. It is **not** in general a
global direct summand of a finite free module, so the Stacks 08JH statement
`strictlyPerfectHomComparison_isIso` does not apply. -/
theorem strictlyPerfectHomComparison_isIso_of_isInvertible
    [HasWeakSheafify X.J AddCommGrpCat.{u}]
    [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ V : X.C, HasWeakSheafify (X.J.over V) AddCommGrpCat.{u}]
    [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]
    (k : ℤ) (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    [Stacks.SheafOfModules.IsInvertible X.O.obj
      (Stacks.SheafOfModules.Tensor.ringSheaf X.O).property L]
    (F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ) :
    IsIso (strictlyPerfectHomComparison X D
      ((HomologicalComplex.single (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (ComplexShape.up ℤ) k).obj L) F) :=
  strictlyPerfectHomComparison_isIso_of_isLocallyFiniteFreeSummand X D k
    (isLocallyFiniteFreeSummand_of_isInvertible X L) F

end AlgebraicGeometry.RingedSite

end
