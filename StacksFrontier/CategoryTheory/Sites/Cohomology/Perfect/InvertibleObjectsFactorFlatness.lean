module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjects
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Slice.FlatLocality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.FlatnessOfFiniteFreeSummands
public import Mathlib.CategoryTheory.Sites.CoversTop.Basic

/-!
# An invertible module over a factor is flat over the structure sheaf of a ringed site

Let `(C, O)` be a ringed site with a locally finite direct product decomposition
`O = ∏_{n ∈ ℤ} O_n` of its structure sheaf
(`AlgebraicGeometry.RingedSite.InvertibleDerived.ProductDecomposition`) and let `H` be an
invertible `O_n`-module.  Then `H`, read as an `O`-module along the projection `O ⟶ O_n`, is flat
over `O`.

This is the input that carries the *diagonal* identification of the implication `(2) ⟹ (1)` of
Stacks 0FPY from sheaves of modules into `D(O)`: the transport
`Stacks.SheafOfModules.DerivedMonoidal.derivedTensorSingleIso` needs one of the two modules to be
flat, and on the diagonal neither of them is a factor.

## Main results

* `...ProductDecomposition.isFlat_toOMod_of_isInvertibleModule`: **an invertible `O_n`-module
  read as an `O`-module is flat.**

The three dots abbreviate `AlgebraicGeometry.RingedSite.InvertibleDerived`.

## Route

The ringed-space proof of this statement goes through the transitivity of flatness along a
restriction of scalars,
`Stacks.SheafOfModules.FlatRestrictScalars.isFlat_restrictScalars_of_isFlat`: `H` is flat over
`O_n` and `O_n` is flat over `O`.  **That route is not available on a site**, and not for want of
a generalisation: the transitivity is proved by reading flatness on stalks (Stacks 05NE), through
`AlgebraicGeometry.SheafOfModules.isFlat_iff_stalk_flat`, and a general site has no points.

The route taken instead uses only facts already available for a ringed site, and the Stacks
argument's own local structure of invertible modules:

* Tag 0B8N, in the form `...ProductDecomposition.summandSieve_mem` of
  `StacksFrontier.CategoryTheory.Sites.Cohomology.Perfect.InvertibleObjects`: an invertible
  `O_n`-module, read as an `O`-module, is a direct summand of a finite free `O`-module on a
  covering of every object of the site.
* A direct summand of a finite free module is flat:
  `Stacks.SheafOfModules.isFlat_of_isDirectSummandOfFiniteFree`, available for a ringed
  site.
* Flatness is local on the site: `Stacks.SheafOfModules.isFlat_of_coversTop`.

The covering family required by the last step is the family of all objects over which the
restricted module is a direct summand of a finite free module; it covers the site because the
sieve of such arrows is a covering sieve of every object, each of whose members is itself such an
object.

Nothing here is a clause of Stacks 0FPY; everything is a step of the proof of its implication
`(2) ⟹ (1)`, so no declaration carries the project tag.

## References

* [Stacks Project, Tag 0FPY](https://stacks.math.columbia.edu/tag/0FPY) — the implication
  `(2) ⟹ (1)`, whose diagonal terms consume this flatness.
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N) — the local structure of
  an invertible module.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u

namespace AlgebraicGeometry.RingedSite.InvertibleDerived.ProductDecomposition

attribute [local instance] Stacks.hasSheafCompose_forget₂_commRingCat

variable {X : RingedSite.{u, u, u}}
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [∀ V : X.C, HasSheafify (X.J.over V) AddCommGrpCat.{u}]
  [∀ V : X.C, (X.J.over V).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The objects of the site over which a given `O`-module is a direct summand of a finite free
module, as a family indexed by itself. -/
def summandObject (D : ProductDecomposition X) (n : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n))) : Type u :=
  {W : X.C // IsDirectSummandOfFiniteFree ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over W)
    ((SheafOfModules.overFunctor.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O) W).obj
      ((D.toOMod n).obj L))}

omit [HasSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}] in
/-- **The objects over which an invertible factor module is a direct summand of a finite free
module cover the site.**  `ProductDecomposition.summandSieve_mem` is Tag 0B8N read at a factor:
the sieve of those arrows is a covering sieve of every object, and each of its members is itself
such an object, so the `Sieve.ofObjects` of the family contains it. -/
theorem coversTop_summand (D : ProductDecomposition X) (n : ℤ)
    (L : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (hL : Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) L) :
    X.J.CoversTop (fun W : D.summandObject n L => W.1) := by
  intro U
  refine X.J.superset_covering ?_ (summandSieve_mem D n L hL U)
  exact fun W g hg => ⟨⟨W, hg⟩, ⟨𝟙 W⟩⟩

/-- **An invertible module over a factor of a product decomposition, read as a module over the
structure sheaf, is flat.**  Tag 0B8N makes it a direct summand of a finite free `O`-module over
each member of a covering of every object of the site; a direct summand of a finite free module is
flat (`Stacks.SheafOfModules.isFlat_of_isDirectSummandOfFiniteFree`, read at the localized ringed
site); and flatness is local on the site (`Stacks.SheafOfModules.isFlat_of_coversTop`).

No transitivity of flatness along a restriction of scalars is used — see the module docstring,
where the reason it cannot be used on a site is recorded.

A step of the proof of an implication of Stacks 0FPY, not a clause of it, so it carries no
`@[stacks]` attribute. -/
theorem isFlat_toOMod_of_isInvertibleModule (D : ProductDecomposition X) (n : ℤ)
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf (D.factor n)))
    (hH : Stacks.SheafOfModules.Tensor.IsInvertibleModule (D.factor n) H) :
    AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.O)
      ((D.toOMod n).obj H) :=
  Stacks.SheafOfModules.isFlat_of_coversTop (D.coversTop_summand n H hH) _ fun W =>
    Stacks.SheafOfModules.isFlat_of_isDirectSummandOfFiniteFree (Y := X.over W.1) _ W.2

end AlgebraicGeometry.RingedSite.InvertibleDerived.ProductDecomposition

end
