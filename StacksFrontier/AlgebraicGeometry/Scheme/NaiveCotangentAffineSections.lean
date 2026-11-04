module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Affine.Over
public import StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentComplex
public import StacksFrontier.CategoryTheory.Sites.Modules.NaiveCotangentSections

/-!
# The naive cotangent complex of the sections of a morphism of schemes over an open

Let `f : X ⟶ Y` be a morphism of schemes and let `V ⊆ X` be an open.  Taking sections over `V`
turns the structural morphism `f^{-1}𝒪_Y ⟶ 𝒪_X` into the ring map
`(f^{-1}𝒪_Y)(V) → Γ(X, V)`, and this file reads the canonical map of two-term complexes of
`Γ(X, V)`-modules

`NL_{Γ(X,V)/(f^{-1}𝒪_Y)(V)} ⟶ NL_{X/Y}(V)`

of `Stacks.SheafOfModules.sectionsNaiveCotangentComparison` at the site of open subsets of `X`.
It is the first step of the proof of Stacks 0D0I, which takes `V` to be an affine open mapping
into an affine open of `Y`; nothing here needs either affineness.

## Main definitions

* `Stacks.NaiveCotangentAffineSections.algebraSections` is `Γ(X, V)` as an algebra over
  `(f^{-1}𝒪_Y)(V)`.
* `Stacks.NaiveCotangentAffineSections.sectionsConormalComparison` and
  `Stacks.NaiveCotangentAffineSections.sectionsTensorComparison` are the degree `-1` and degree
  `0` components of the comparison: maps of `Γ(X, V)`-modules from the conormal module and the
  cotangent space of `Algebra.Generators.self ((f^{-1}𝒪_Y)(V)) Γ(X, V)` into the sections over
  `V` of the conormal sheaf and of the tensor-differentials sheaf of the canonical presentation
  of `𝒪_X` over `f^{-1}𝒪_Y`.
* `Stacks.NaiveCotangentAffineSections.naiveCotangentSections` is the sections over `V` of
  `NL_{X/Y}` as a two-term complex of `Γ(X, V)`-modules, and
  `Stacks.NaiveCotangentAffineSections.sectionsComparison` is the comparison as a chain map of
  such complexes; its `comm` field is the commutation with the two differentials.

## Implementation notes

The structural morphism is spelled `AlgebraicGeometry.inverseImageStructureMap f`, with source
`(TopCat.Sheaf.pullback CommRingCat f.base).obj Y.sheaf`, which is the spelling the stalk
statements of `StacksFrontier.AlgebraicGeometry.Scheme.NaiveCotangentAffineStalk` use.  It is the
same morphism of sheaves of rings as the one `AlgebraicGeometry.Scheme.naiveCotangentComplex` is
built from — `Stacks.NaiveCotangentAffineStalk.inverseImageStructureMap_eq_ringedSpace` says so,
by `rfl` — so the two terms here are the sections over `V` of the two terms of `NL_{X/Y}` named
by `AlgebraicGeometry.Scheme.naiveCotangentComplex_X_negOne` and
`AlgebraicGeometry.Scheme.naiveCotangentComplex_X_zero`.

The types of the two components are left to be inferred from the site-level declarations rather
than written out: spelling them here means spelling the canonical presentation of `𝒪_X` over
`f^{-1}𝒪_Y` in the statement, and the instance that it is a locally surjective morphism of
sheaves is then not found while that spelling is being elaborated.

Everything is a reading of the site-level construction at
`Opens.grothendieckTopology X.toRingedSpace.carrier`: no geometry enters the construction of the
comparison, only the identification of the two sheaves of rings.

## References

* [Stacks Project, Tag 0D0I](https://stacks.math.columbia.edu/tag/0D0I), of whose proof this is
  the first step.
* [Stacks Project, Tag 08TW](https://stacks.math.columbia.edu/tag/08TW), the naive cotangent
  complex of a morphism of sheaves of rings.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

noncomputable section

namespace Stacks.NaiveCotangentAffineSections

open Stacks.Sites.FreeAlgebra Stacks.Sites.Conormal

variable {X Y : Scheme.{u}} (f : X ⟶ Y) (V : X.Opens)

/-- `Γ(X, V)` as an algebra over `(f^{-1}𝒪_Y)(V)`, through the sections over `V` of the
structural morphism `f^{-1}𝒪_Y ⟶ 𝒪_X`.  This is the ring map whose naive cotangent complex the
comparison below starts from. -/
abbrev algebraSections :
    Algebra ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj.obj (op V))
      ↑(X.sheaf.obj.obj (op V)) :=
  Stacks.SheafOfModules.algebraSections
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) (op V)

/-- **The comparison on sections in degree `-1`.**  The conormal module of the canonical
presentation of `Γ(X, V)` over `(f^{-1}𝒪_Y)(V)` maps, `Γ(X, V)`-linearly, to the sections over
`V` of the conormal sheaf of the canonical presentation of `𝒪_X` over `f^{-1}𝒪_Y`, which is the
degree `-1` term of `NL_{X/Y}`. -/
abbrev sectionsConormalComparison :=
  Stacks.SheafOfModules.sectionsConormalComparison.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) (op V)

/-- **The comparison on sections in degree `0`.**  The cotangent space of the canonical
presentation of `Γ(X, V)` over `(f^{-1}𝒪_Y)(V)` maps, `Γ(X, V)`-linearly, to the sections over
`V` of the tensor-differentials sheaf of the canonical presentation of `𝒪_X` over `f^{-1}𝒪_Y`,
which is the degree `0` term of `NL_{X/Y}`. -/
abbrev sectionsTensorComparison :=
  Stacks.SheafOfModules.sectionsTensorComparison.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) (op V)

/-- **The sections over `V` of `NL_{X/Y}`**, as a two-term complex of `Γ(X, V)`-modules. -/
abbrev naiveCotangentSections : NaiveCotangent.TwoTerm ↑(X.sheaf.obj.obj (op V)) :=
  Stacks.SheafOfModules.naiveCotangentSections.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) (op V)

/-- **The canonical map `NL_{Γ(X,V)/(f^{-1}𝒪_Y)(V)} ⟶ NL_{X/Y}(V)`**, the first step of the
proof of Stacks 0D0I: the naive cotangent complex of the sections over `V` of the structural
morphism maps canonically to the sections over `V` of `NL_{X/Y}`, as a chain map of two-term
complexes of `Γ(X, V)`-modules.  Its two components are
`Stacks.NaiveCotangentAffineSections.sectionsConormalComparison` and
`Stacks.NaiveCotangentAffineSections.sectionsTensorComparison`, and its `comm` field is their
commutation with the two differentials. -/
abbrev sectionsComparison :
    letI := algebraSections f V
    NaiveCotangent.ChainMap
      (NaiveCotangent.NL (Algebra.Generators.self
        ↑(((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf).obj.obj (op V))
        ↑(X.sheaf.obj.obj (op V))))
      (naiveCotangentSections f V) :=
  Stacks.SheafOfModules.sectionsNaiveCotangentComparison.{u, u, u, u}
    (Opens.grothendieckTopology X.toRingedSpace.carrier)
    ((TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj Y.sheaf) X.sheaf
    (AlgebraicGeometry.inverseImageStructureMap f) (op V)

end Stacks.NaiveCotangentAffineSections

end

end
