module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Preadditive.Yoneda.Basic

/-! # The Hom complex out of a single complex is the degreewise `Hom(X, -)`

Let `C` be a preadditive category with a zero object, let `X` be an object of `C` and let `L` be
a cochain complex in `C`. Applying the additive functor `Hom(X, -) : C ⥤ AddCommGrpCat`
degreewise to `L` gives a cochain complex of abelian groups, and this file identifies it with
Mathlib's Hom complex `CochainComplex.HomComplex ((singleFunctor C 0).obj X) L` out of the
complex `X[0]`.

The identification is degreewise `CochainComplex.HomComplex.Cochain.fromSingleEquiv`, which
says that a degree-`n` cochain `X[0] ⟶ L` is a map `X ⟶ L.X n`, and it commutes with the
differentials because the differential of `X[0]` vanishes: the two terms of
`CochainComplex.HomComplex.Cochain.δ_single` degenerate to postcomposition with the
differential of `L`, with no sign. So the comparison is an isomorphism of complexes on the
nose, in both variables.

Combined with `CochainComplex.HomComplex.homologyAddEquiv` and
`CochainComplex.HomComplex.CohomologyClass.homAddEquiv`, this says that the degree-`n`
cohomology of `Hom(X, L^•)` is the group of morphisms `X[0] ⟶ L⟦n⟧` in the homotopy category.
That is the shape in which a functor of the form `Hom(X, -)` — for instance the sections of a
sheaf of modules over an object of a site — can be compared with the homotopy category, and
hence with the derived category.

## Main definitions

* `CochainComplex.HomComplex.coyonedaComplex`: the complex `Hom(X, L^•)`.
* `CochainComplex.HomComplex.coyonedaComplexIsoHomComplexSingle`: the isomorphism of complexes
  of abelian groups `Hom(X, L^•) ≅ Hom(X[0], L)`.
* `CochainComplex.HomComplex.coyonedaComplexFunctor`: the complex `Hom(X, L^•)` as a functor
  of `L`, which is what `coyonedaComplexIsoHomComplexSingle_naturality` is natural for.

## Main results

* `CochainComplex.HomComplex.coyonedaComplexIsoHomComplexSingle_naturality`: the isomorphism is
  natural in `L`.
* `CochainComplex.HomComplex.coyonedaHomologyAddEquiv`: the degree-`n` cohomology of
  `Hom(X, L^•)` is `X[0] ⟶ L⟦n⟧` in the homotopy category.
-/

@[expose] public section

open CategoryTheory Category Limits Preadditive Opposite

universe v u

namespace CochainComplex.HomComplex

variable {C : Type u} [Category.{v} C] [Preadditive C] [HasZeroObject C]

/-- The complex of abelian groups obtained by applying `Hom(X, -)` degreewise to `L`. For a
sheaf of modules this is the complex of sections over an object, once that functor has been
identified with a `Hom`. -/
noncomputable abbrev coyonedaComplex (X : C) (L : CochainComplex C ℤ) :
    CochainComplex AddCommGrpCat.{v} ℤ :=
  ((preadditiveCoyoneda.obj (op X)).mapHomologicalComplex (ComplexShape.up ℤ)).obj L

/-- Degreewise, a cochain `X[0] ⟶ L` of degree `n` is a map `X ⟶ L.X n`. -/
noncomputable def fromSingleIsoApp (X : C) (L : CochainComplex C ℤ) (n : ℤ) :
    (HomComplex ((singleFunctor C 0).obj X) L).X n ≅ (coyonedaComplex X L).X n :=
  (Cochain.fromSingleEquiv (X := X) (K := L) (p := 0) (q := n) (n := n)
    (zero_add n)).toAddCommGrpIso

/-- **The Hom complex out of `X[0]` is the degreewise `Hom(X, -)`.** The differential of `X[0]`
vanishes, so the differential of the Hom complex is postcomposition with the differential of
`L`, with no sign. -/
noncomputable def homComplexSingleIsoCoyonedaComplex (X : C) (L : CochainComplex C ℤ) :
    HomComplex ((singleFunctor C 0).obj X) L ≅ coyonedaComplex X L :=
  HomologicalComplex.Hom.isoOfComponents (fromSingleIsoApp X L) (by
    intro i j _
    ext z
    obtain ⟨f, rfl⟩ : ∃ f, z = Cochain.fromSingleMk (X := X) (K := L) f (zero_add i) :=
      ⟨Cochain.fromSingleEquiv (zero_add i) z,
        ((Cochain.fromSingleEquiv (zero_add i)).symm_apply_apply z).symm⟩
    change Cochain.fromSingleEquiv (zero_add i) (Cochain.fromSingleMk f (zero_add i)) ≫ L.d i j =
      Cochain.fromSingleEquiv (zero_add j) (δ i j (Cochain.fromSingleMk f (zero_add i)))
    rw [Cochain.δ_fromSingleMk f (zero_add i) j j (zero_add j)]
    simp)

/-- `Hom(X, L^•) ≅ Hom(X[0], L)`, the inverse of `homComplexSingleIsoCoyonedaComplex`. -/
noncomputable abbrev coyonedaComplexIsoHomComplexSingle (X : C) (L : CochainComplex C ℤ) :
    coyonedaComplex X L ≅ HomComplex ((singleFunctor C 0).obj X) L :=
  (homComplexSingleIsoCoyonedaComplex X L).symm

end CochainComplex.HomComplex

end
