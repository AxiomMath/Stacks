module

public import StacksCore.Algebra.Homology.HomologicalTricomplex.Total23
public import StacksFrontier.Algebra.Homology.TotalComplexFiniteSupport
public import StacksFrontier.Algebra.Homology.TricomplexRotation
public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.TotalComplexRefinement

/-!
# The Čech tricomplex of a double complex of presheaves

Let `U : I → C` be a family of objects of a category with finite products and let
`L^{•,•}` be a double complex of abelian presheaves on `C`. Applying the Čech complex of `U`
to every term of `L` produces a *triple* complex, and the arrangement of its three indices is
what the Čech hypercohomology spectral sequence is built from. This file puts the Čech degree
**first**:

```
Č(U, L)^{p, q, m} = Č^p(U, L^{q, m}).
```

The Čech degree is the new index, so it appears last in the naive construction
`((cechComplexFunctorInt U).mapHC).mapHC` and has to be rotated to the front; that rotation is
`HomologicalComplex₃.rotateFunctor`, and the two identifications that make the result usable are
recorded here:

* the **slice** at a fixed `m` is the Čech bicomplex `Stacks.Cech.cechBicomplexFunctor` of the
  row `q ↦ L^{q, m}`, which is what makes the Čech degree and the first degree of `L` the two
  indices integrated by `HomologicalComplex₃.int₁₂`;
* the **column** at a fixed Čech degree `p` is the double complex obtained by applying the
  ordinary functor `L^{q, m} ↦ Č^p(U, L^{q, m})` to `L`, which is what makes the last two
  indices the ones integrated by `HomologicalComplex₃.int₂₃`.

## Main definitions

* `Stacks.Cech.cechTricomplexFunctor`: the triple complex `Č^p(U, L^{q, m})`, Čech degree first.
* `Stacks.Cech.int₂₃IsoCechBicomplex` and `Stacks.Cech.total₂₃IsoCechTotalComplex`: integrating
  its last two indices gives the Čech bicomplex, respectively the total Čech complex, of the
  total complex of `L`.

## Main results

* `Stacks.Cech.cechTricomplexFunctor_obj_X'` and `Stacks.Cech.cechTricomplexFunctor_obj_X`: its
  slices and its columns.

## Implementation notes

Both identifications are definitional equalities, not merely isomorphisms: the rotation is
built from `HomologicalComplex₂.flip`, which exchanges two directions of a bicomplex without
introducing any sign, so no transport of differentials is needed and in particular no sign has
to be tracked.

## References

* [Stacks Project, Tag 08BI](https://stacks.math.columbia.edu/tag/08BI)
* [Stacks Project, Tag 08BN](https://stacks.math.columbia.edu/tag/08BN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits ComplexShape

universe w v u

namespace Stacks.Cech

variable {C : Type u} [Category.{v} C] [HasFiniteProducts C] {I : Type w} (U : I → C)
  [(CategoryTheory.cechComplexFunctor (A := AddCommGrpCat.{w}) U).Additive]

/-- The Čech complex of a family, extended by zero to the integers, is additive: the Čech
complex functor is, and so is extension by zero. -/
noncomputable instance cechComplexFunctorInt_additive : (cechComplexFunctorInt U).Additive :=
  inferInstanceAs ((CategoryTheory.cechComplexFunctor U ⋙
    embeddingUpNat.extendFunctor AddCommGrpCat.{w}).Additive)

/-- **The Čech triple complex of a double complex of abelian presheaves**, with the Čech degree
placed first: its term in position `(p, q, m)` is `Č^p(U, L^{q, m})`. -/
noncomputable def cechTricomplexFunctor :
    HomologicalComplex₂ (Cᵒᵖ ⥤ AddCommGrpCat.{w}) (up ℤ) (up ℤ) ⥤
      HomologicalComplex₃ AddCommGrpCat.{w} (up ℤ) (up ℤ) (up ℤ) :=
  ((cechComplexFunctorInt U).mapHomologicalComplex (up ℤ)).mapHomologicalComplex (up ℤ) ⋙
    HomologicalComplex₃.rotateFunctor AddCommGrpCat.{w} (up ℤ) (up ℤ) (up ℤ)

variable (L : HomologicalComplex₂ (Cᵒᵖ ⥤ AddCommGrpCat.{w}) (up ℤ) (up ℤ))

/-- The Čech triple complex is the general construction
`HomologicalComplex₃.ofComplexValuedFunctor` for the integer-indexed Čech complex. -/
lemma cechTricomplexFunctor_obj :
    (cechTricomplexFunctor U).obj L =
      HomologicalComplex₃.ofComplexValuedFunctor (cechComplexFunctorInt U) L :=
  rfl

/-- The term of the Čech triple complex in position `(p, q, m)` is `Č^p(U, L^{q, m})`. -/
lemma cechTricomplexFunctor_obj_X_X_X (p q m : ℤ) :
    ((((cechTricomplexFunctor U).obj L).X p).X q).X m =
      ((cechComplexFunctorInt U).obj ((L.X q).X m)).X p :=
  rfl

/-- **The slice of the Čech triple complex at `m`** is the Čech bicomplex of the row
`q ↦ L^{q, m}`: the Čech degree and the first degree of `L` are its two indices. -/
lemma cechTricomplexFunctor_obj_X' (m : ℤ) :
    ((cechTricomplexFunctor U).obj L).X' m =
      (cechBicomplexFunctor U).obj (HomologicalComplex₂.flip L |>.X m) :=
  rfl

/-- **The column of the Čech triple complex at Čech degree `p`** is the double complex obtained
from `L` by applying `L^{q, m} ↦ Č^p(U, L^{q, m})` to each term: the two degrees of `L` are its
two indices. -/
lemma cechTricomplexFunctor_obj_X (p : ℤ) :
    ((cechTricomplexFunctor U).obj L).X p =
      HomologicalComplex₂.TotalMap.mapBicomplex
        (cechComplexFunctorInt U ⋙ HomologicalComplex.eval AddCommGrpCat.{w} (up ℤ) p) L :=
  rfl

/-- **Integrating the last two indices of the Čech triple complex gives the Čech bicomplex of
the total complex of `L`.** In Čech degree `p` this is the comparison
`Tot(Č^p(U, L^{•,•})) ≅ Č^p(U, Tot(L)^{•})`, an isomorphism because only finitely many terms of
`L` are nonzero in each total degree; the compatibility with the Čech differential is the
naturality of that comparison in the functor. -/
noncomputable def int₂₃IsoCechBicomplex
    (hL : ∀ n : ℤ, {qm : ℤ × ℤ | ComplexShape.π (up ℤ) (up ℤ) (up ℤ) qm = n ∧
      ¬ IsZero ((L.X qm.1).X qm.2)}.Finite) :
    ((cechTricomplexFunctor U).obj L).int₂₃ (up ℤ) ≅
      (cechBicomplexFunctor U).obj (L.total (up ℤ)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun p => HomologicalComplex₂.TotalMap.totalIsoOfFinite
      (cechComplexFunctorInt U ⋙ HomologicalComplex.eval AddCommGrpCat.{w} (up ℤ) p) L hL)
    (fun p p' _ => (HomologicalComplex₂.TotalMap.totalMap_naturality_functor
      (cechComplexFunctorInt U ⋙ HomologicalComplex.eval AddCommGrpCat.{w} (up ℤ) p) L
      (Functor.whiskerLeft (cechComplexFunctorInt U)
        (HomologicalComplex.dNatTrans AddCommGrpCat.{w} (up ℤ) p p'))).symm)

/-- **The total complex of the Čech triple complex, formed by integrating the last two indices
first, is the total Čech complex of the total complex of `L`.** Combined with the associator
`HomologicalComplex₃.totalAssociator` of [Stacks, Tag 08BI], this identifies the total complex
of the triple complex with `Tot(Č(U, Tot(L)))`. -/
noncomputable def total₂₃IsoCechTotalComplex
    (hL : ∀ n : ℤ, {qm : ℤ × ℤ | ComplexShape.π (up ℤ) (up ℤ) (up ℤ) qm = n ∧
      ¬ IsZero ((L.X qm.1).X qm.2)}.Finite) :
    HomologicalComplex₃.total₂₃ ((cechTricomplexFunctor U).obj L) (up ℤ) (up ℤ) ≅
      (cechTotalComplexFunctor U).obj (L.total (up ℤ)) :=
  (HomologicalComplex₂.totalFunctor AddCommGrpCat.{w} (up ℤ) (up ℤ) (up ℤ)).mapIso
    (int₂₃IsoCechBicomplex U L hL)

end Stacks.Cech

end
