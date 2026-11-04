module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.StrictlyPerfect.HomComplexIntoASingleComplex
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.StrictlyPerfectHomRepresentation

/-!
# The internal Hom complex into the structure sheaf on a ringed space

Let `(X, O_X)` be a ringed space and `E` a bounded complex of `O_X`-modules. This file reads
off, for a ringed space, the collapse of the internal Hom complex of Stacks 0A8Z into a complex
concentrated in one degree:

`SheafHom(E, O_X[0])^n = Hom_{O_X}(E^{-n}, O_X)`.

The degree-`n` term of `SheafHom(E, F)` is the direct sum over `q : ℤ` of the internal Hom
sheaves `Hom(E^{-q}, F^{n-q})` (Stacks 08DM, `strictlyPerfectHomDegreeIso` in
`StrictlyPerfectHomRepresentation.lean` in this directory); when `F` has a single nonzero term
every other summand has a zero target and so vanishes.

## Main results

* `Stacks.SheafOfModules.homSingleTargetDegreeIso`: the collapse, for a target concentrated in
  an arbitrary degree.
* `Stacks.SheafOfModules.homStructureSheafDegreeIso`: the collapse for the structure sheaf in
  degree zero, and `Stacks.SheafOfModules.homStructureSheafDegreeIso_naturality`: it is natural
  in the source complex.
* `Stacks.SheafOfModules.isZero_homStructureSheafDegree` and
  `Stacks.SheafOfModules.sheafHomComplex_structureSheaf_bounded`: the term vanishes where
  `E^{-n}` does, so `SheafHom(E, O_X[0])` is bounded when `E` is.

## Implementation notes

A topological space with a sheaf of commutative rings *is* a ringed site, namely the site of
its opens with the open-cover topology, so each statement below is the site-level statement of
`StacksFrontier/CategoryTheory/Sites/Cohomology/StrictlyPerfect/HomComplexIntoASingleComplex.lean`
type-checked against the space-level one, with no comparison layer between the two settings —
exactly as in `StrictlyPerfectHomRepresentation.lean` and `InvertibleHomRepresentation.lean` in
this directory.

This is the shape the local computation of [Stacks, Tag 0B4B] needs: there the source is the
two-term complex `(ℐ_D ⟶ 𝒪_X)` resolving `i_* 𝒪_D` for an effective Cartier divisor, and the
collapse gives `ℰom(𝒪_X, 𝒪_X)` in degree `0` and `ℰom(ℐ_D, 𝒪_X)` in degree `1`.

## References

* [Stacks Project, Tag 08DM](https://stacks.math.columbia.edu/tag/08DM)
* [Stacks Project, Tag 08JH](https://stacks.math.columbia.edu/tag/08JH)
* [Stacks Project, Tag 0A8Z](https://stacks.math.columbia.edu/tag/0A8Z)
* [Stacks Project, Tag 0B4B](https://stacks.math.columbia.edu/tag/0B4B)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite TopologicalSpace

namespace Stacks.SheafOfModules

universe u

variable {X : TopCat.{u}} (Rc : TopCat.Sheaf CommRingCat.{u} X)
  [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
  [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- **Stacks 08DM for a target concentrated in one degree, on a ringed space.** For `E` bounded
and `M` an `O_X`-module placed in degree `n - r`, the degree-`n` term of the internal Hom
complex `SheafHom(E, M[r - n])` is the single internal Hom sheaf `Hom_{O_X}(E^{-r}, M)`. -/
def homSingleTargetDegreeIso
    (E : CochainComplex (StructureSheafModules Rc) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (M : StructureSheafModules Rc) (n r : ℤ) :
    (RingedSite.sheafHomComplex (ringedSite Rc) E
        ((HomologicalComplex.single (StructureSheafModules Rc)
          (ComplexShape.up ℤ) (n - r)).obj M)).obj.X n ≅
      RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-r)) M :=
  RingedSite.homSingleTargetDegreeIso (ringedSite Rc) E hE M n r

/-- **Stacks 08DM into the structure sheaf, on a ringed space.** The degree-`n` term of the
internal Hom complex `SheafHom(E, O_X[0])` of a bounded complex `E` is the dual
`Hom_{O_X}(E^{-n}, O_X)` of its degree-`(-n)` term. -/
def homStructureSheafDegreeIso
    (E : CochainComplex (StructureSheafModules Rc) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n : ℤ) :
    (RingedSite.sheafHomComplex (ringedSite Rc) E
        (RingedSite.structureSheafComplex (ringedSite Rc))).obj.X n ≅
      RingedSite.internalHomSheaf (ringedSite Rc) (E.X (-n))
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf (ringedSite Rc).O)) :=
  RingedSite.homStructureSheafDegreeIso (ringedSite Rc) E hE n

/-- **The collapse into the structure sheaf is natural in the source complex, on a ringed
space.** A morphism `k : E' ⟶ E` of complexes induces the morphism
`AlgebraicGeometry.RingedSite.homMap` of internal Hom complexes in the other direction, and
through the collapse its degree-`n` component is precomposition with the component `k^{-n}`.

This is the space-level form of
`AlgebraicGeometry.RingedSite.homStructureSheafDegreeIso_naturality`, where it is proved: the
collapse is the `n`-th projection of the product description of the degree-`n` term, and that
projection is natural in the source. -/
theorem homStructureSheafDegreeIso_naturality
    (E E' : CochainComplex (StructureSheafModules Rc) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite)
    (hE' : {i : ℤ | ¬ IsZero (E'.X i)}.Finite) (k : E' ⟶ E) (n : ℤ) :
    (RingedSite.homMap (ringedSite Rc) k
          (𝟙 (RingedSite.structureSheafComplex (ringedSite Rc)))).f n ≫
        (homStructureSheafDegreeIso Rc E' hE' n).hom =
      (homStructureSheafDegreeIso Rc E hE n).hom ≫
        RingedSite.internalHomPre (ringedSite Rc) (k.f (-n)) :=
  RingedSite.homStructureSheafDegreeIso_naturality (ringedSite Rc) E E' hE hE' k n

/-- The degree-`n` term of `SheafHom(E, O_X[0])` vanishes where `E^{-n}` does. -/
theorem isZero_homStructureSheafDegree
    (E : CochainComplex (StructureSheafModules Rc) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) (n : ℤ) (h : IsZero (E.X (-n))) :
    IsZero ((RingedSite.sheafHomComplex (ringedSite Rc) E
      (RingedSite.structureSheafComplex (ringedSite Rc))).obj.X n) :=
  RingedSite.isZero_homStructureSheafDegree (ringedSite Rc) E hE n h

/-- The internal Hom complex `SheafHom(E, O_X[0])` is bounded when `E` is. -/
theorem sheafHomComplex_structureSheaf_bounded
    (E : CochainComplex (StructureSheafModules Rc) ℤ)
    (hE : {i : ℤ | ¬ IsZero (E.X i)}.Finite) :
    {i : ℤ | ¬ IsZero ((RingedSite.sheafHomComplex (ringedSite Rc) E
      (RingedSite.structureSheafComplex (ringedSite Rc))).obj.X i)}.Finite :=
  RingedSite.sheafHomComplex_structureSheaf_bounded (ringedSite Rc) E hE

end Stacks.SheafOfModules

end
