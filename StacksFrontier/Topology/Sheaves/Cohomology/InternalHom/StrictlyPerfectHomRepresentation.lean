module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexComparison
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexOfAStrictlyPerfectComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedInternalHom
import StacksCore.Tactic.StacksAttribute

/-!
# Derived internal Hom out of a strictly perfect complex on a ringed space

Let `(X, O_X)` be a ringed space, let `E` be a strictly perfect complex of `O_X`-modules —
bounded, with every term a direct summand of a finite free module — and let `F` be an arbitrary
complex of `O_X`-modules. **Stacks 08DM** says that the derived internal Hom `RSheafHom(E, F)`
needs no injective resolution of `F`: it is represented by the ordinary internal Hom complex
`SheafHom(E, F)`, whose degree-`n` term is the finite direct sum
`⊕_{n = p + q} Hom_{O_X}(E^{-q}, F^p)` and whose differential is the usual Hom-complex
differential.

A topological space with a sheaf of commutative rings *is* a ringed site, namely its site of
opens with the open-cover topology, so this is the ringed-site statement of Stacks 08JH read off
along `Stacks.SheafOfModules.ringedSite`, exactly as Stacks 08DL is read off Stacks 08JB in
`StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedRestrictionToOpens`.

## Main definitions

* `Stacks.SheafOfModules.strictlyPerfectHomComparison`: the canonical comparison from the class
  of the internal Hom complex `SheafHom(E, F)` to the derived internal Hom `RSheafHom(E, F)`.
* `Stacks.SheafOfModules.strictlyPerfectHomDegreeIso`: the degreewise finite direct-sum
  description of `SheafHom(E, F)`.

## Main results

* `Stacks.SheafOfModules.strictlyPerfectHomComparison_isIso`: **Stacks 08DM**, the comparison is
  an isomorphism for `E` bounded with every term a direct summand of a finite free module.

## Implementation notes

The termwise hypothesis is `AlgebraicGeometry.RingedSite.IsFiniteFreeSummand`, "a retract of an
iterated binary biproduct of copies of the structure sheaf", rather than the `IsStrictlyPerfect`
of Stacks 08FL. The two name the same notion, a direct summand of a finite free module; the
former is the spelling in which the ringed-site statement is universe polymorphic, the latter
being available only on the diagonal at `Type 0`. Boundedness is the finiteness of the set of
degrees in which `E` does not vanish, which is the `bounded` field of `IsStrictlyPerfect`.

The degreewise description needs only boundedness of `E`, with no condition on its terms; that
is the ringed-site statement and is a generalisation of the source lemma, whose hypothesis is
strict perfectness throughout.

That the differential is the Hom-complex differential needs no separate statement: it is part of
the data of `AlgebraicGeometry.RingedSite.SheafHomComplex`, whose `sectionsIso` identifies the
complex of sections over every open with `CochainComplex.HomComplex` of the restrictions.

## References

* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace Stacks.SheafOfModules

attribute [local instance] HasDerivedCategory.standard

universe u

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
  (E F : CochainComplex (StructureSheafModules Rc) ℤ)

/-- The canonical comparison from the class of the internal Hom complex `SheafHom(E, F)` of
Stacks 0A8Z to the derived internal Hom `RSheafHom(E, F)` on a ringed space: the map induced by
the K-injective augmentation of the target, read through the identification of derived internal
Hom with the internal Hom complex at a K-injective target. -/
abbrev strictlyPerfectHomComparison :
    DerivedCategory.Q.obj (RingedSite.sheafHomComplex (ringedSite Rc) E F).obj ⟶
      ((derivedSheafHom Rc).obj (op (DerivedCategory.Q.obj E))).obj
        (DerivedCategory.Q.obj F) :=
  RingedSite.strictlyPerfectHomComparison (ringedSite Rc) (derivedInternalHom Rc) E F

/-- **Stacks 08DM, the degreewise description.** The degree-`n` term of the internal Hom complex
`SheafHom(E, F)` of a bounded complex `E` is the finite direct sum `⊕_q Hom_{O_X}(E^{-q},
F^{n-q})`, that is `⊕_{n = p + q} Hom_{O_X}(E^{-q}, F^p)`. -/
@[stacks 08DM "finite direct-sum terms and Hom differential"]
def strictlyPerfectHomDegreeIso (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n : ℤ) :
    (RingedSite.sheafHomComplex (ringedSite Rc) E F).obj.X n ≅
      ∐ (fun q : ℤ => RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-q)) (F.X (n - q))) :=
  RingedSite.strictlyPerfectHomDegreeIso (ringedSite Rc) E F hE n

/-- **Stacks 08DM.** For `E` strictly perfect — bounded, with every term a direct summand of a
finite free `O_X`-module — the derived internal Hom `RSheafHom(E, F)` is represented by the
ordinary internal Hom complex `SheafHom(E, F)` of Stacks 0A8Z, for every complex `F`, the
comparison being the canonical one. No injective resolution of `F` is needed.

The comparison is an isomorphism exactly when the map of internal Hom complexes induced by the
K-injective augmentation of `F` is a quasi-isomorphism, and strict perfectness of `E` makes it
one: the statement holds for a source concentrated in one degree whose term is the structure
sheaf, hence for finite free terms by direct sums, hence for direct summands of those by
retracts, and the stupid filtration of the bounded complex `E` assembles the terms. -/
@[stacks 08DM "representation by the finite direct-sum Hom complex"]
theorem strictlyPerfectHomComparison_isIso
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hterm : ∀ i : ℤ, RingedSite.IsFiniteFreeSummand (ringedSite Rc) (E.X i)) :
    IsIso (strictlyPerfectHomComparison Rc E F) :=
  RingedSite.strictlyPerfectHomComparison_isIso (ringedSite Rc) (derivedInternalHom Rc) E F
    hE hterm

end Stacks.SheafOfModules

end
