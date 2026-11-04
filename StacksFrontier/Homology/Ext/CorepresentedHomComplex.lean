module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.RightDerivedSheafToPresheaf
public import StacksFrontier.Homology.HomComplex.RHom

/-!
# Cohomology of a corepresentable functor applied to a complex

Let `A` be an abelian category and let `T : A ⥤ AddCommGrpCat` be an additive functor which is
corepresented by an object `Z`, the corepresentation being an isomorphism `e : Hom(Z, -) ≅ T`.
For a cochain complex `L`, the cohomology of the complex obtained by applying `T` degreewise to `L`
is
`Hⁿ(T(L)) ≅ Hom_{K(A)}(Z[0], L⟦n⟧)`,
the group of morphisms in the homotopy category out of `Z` placed in degree `0`. This
identification is natural in `L`: a morphism `g : L ⟶ L'` acts on the left-hand side through `T`
and on the right-hand side by postcomposition with `g⟦n⟧`.

## Main definitions

* `Stacks.Cohomology.Corepresented.corepresentedHomComplexIso`: the isomorphism of cochain
  complexes of abelian groups `Hom^•(Z[0], L) ≅ T(L)` determined by a corepresentation of `T`
  by `Z`.
* `Stacks.Cohomology.Corepresented.corepresentedHomologyHomotopyIso`: the comparison
  `Hⁿ(T(L)) ≅ Hom_{K(A)}(Z[0], L⟦n⟧)`, as an isomorphism in `AddCommGrpCat`.
* `Stacks.Cohomology.Corepresented.corepresentedHomologyHomotopyAddEquiv`: the same comparison
  read as an additive equivalence.

## Main results

* `Stacks.Cohomology.Corepresented.homComplexHomologyAddEquiv_postcomp`: the identification
  `homComplexHomologyAddEquiv` intertwines the map induced on homology by
  `homComplexPostcomp K g` with postcomposition by `g⟦n⟧` in the homotopy category.
* `Stacks.Cohomology.Corepresented.corepresentedHomComplexIso_hom_naturality`: naturality of
  `corepresentedHomComplexIso` in the complex, at the level of Hom complexes.
* `Stacks.Cohomology.Corepresented.corepresentedHomologyHomotopyIso_hom_naturality`: naturality
  of the comparison in the complex.

## References

* [Stacks Project, Tag 0A5X](https://stacks.math.columbia.edu/tag/0A5X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.Corepresented

universe v u

variable {A : Type u} [Category.{v} A] [Abelian A]

/-- The identification `Hⁿ(Hom^•(K, L)) ≃+ Hom_{K(A)}(K, L⟦n⟧)` carries the map induced on
homology by `homComplexPostcomp K g` to postcomposition with `g⟦n⟧` in the homotopy category. -/
theorem homComplexHomologyAddEquiv_postcomp (K : CochainComplex A ℤ)
    {L L' : CochainComplex A ℤ} (g : L ⟶ L') (n : ℤ)
    (x : (K.HomComplex L).homology n) :
    homComplexHomologyAddEquiv K L' n
        (HomologicalComplex.homologyMap (homComplexPostcomp K g) n x) =
      homComplexHomologyAddEquiv K L n x ≫
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (g⟦n⟧') := by
  simp only [homComplexHomologyAddEquiv, AddEquiv.trans_apply,
    CochainComplex.HomComplex.CohomologyClass.homAddEquiv_apply]
  rw [← homologyAddEquiv_postcomp K g n x]
  exact toHom_cohomologyClassPostcomp g n _

variable (T : A ⥤ AddCommGrpCat.{v}) [T.Additive] (Z : A)
  (e : preadditiveCoyoneda.obj (op Z) ≅ T)

/-- For an additive functor `T` corepresented by `Z`, the Hom complex out of the single complex
`Z[0]` is the complex obtained by applying `T` degreewise. -/
noncomputable def corepresentedHomComplexIso (L : CochainComplex A ℤ) :
    ((CochainComplex.singleFunctor A 0).obj Z).HomComplex L ≅
      (T.mapHomologicalComplex (ComplexShape.up ℤ)).obj L :=
  Stacks.Cohomology.Locality.homComplexSingleIsoCoyoneda Z L ≪≫
    (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).app L

/-- `corepresentedHomComplexIso` is natural in the complex: it intertwines postcomposition on
Hom complexes with the degreewise action of `T`. -/
theorem corepresentedHomComplexIso_hom_naturality {L L' : CochainComplex A ℤ} (g : L ⟶ L') :
    homComplexPostcomp ((CochainComplex.singleFunctor A 0).obj Z) g ≫
        (corepresentedHomComplexIso T Z e L').hom =
      (corepresentedHomComplexIso T Z e L).hom ≫
        (T.mapHomologicalComplex (ComplexShape.up ℤ)).map g := by
  dsimp only [corepresentedHomComplexIso, Iso.trans_hom, Iso.app_hom]
  rw [← Category.assoc, Stacks.Cohomology.homComplexSingleIsoCoyoneda_naturality Z g,
    Category.assoc, (NatIso.mapHomologicalComplex e (ComplexShape.up ℤ)).hom.naturality g,
    ← Category.assoc]

/-- For an additive functor `T` corepresented by `Z`, the degree-`n`
cohomology of `T` applied degreewise to a cochain complex `L` is the group of morphisms
`Z[0] ⟶ L⟦n⟧` in the homotopy category. -/
noncomputable def corepresentedHomologyHomotopyIso (L : CochainComplex A ℤ) (n : ℤ) :
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homology n ≅
      (preadditiveCoyoneda.obj (op ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor A 0).obj Z)))).obj
        ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (L⟦n⟧)) :=
  HomologicalComplex.homologyMapIso (corepresentedHomComplexIso T Z e L).symm n ≪≫
    (homComplexHomologyAddEquiv ((CochainComplex.singleFunctor A 0).obj Z) L n).toAddCommGrpIso

/-- The comparison `Hⁿ(T(L)) ≅ Hom_{K(A)}(Z[0], L⟦n⟧)` is natural in the complex: the degreewise
action of `T` on homology corresponds to postcomposition with `g⟦n⟧` in the homotopy
category. -/
theorem corepresentedHomologyHomotopyIso_hom_naturality
    {L L' : CochainComplex A ℤ} (g : L ⟶ L') (n : ℤ) :
    HomologicalComplex.homologyMap ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map g) n ≫
        (corepresentedHomologyHomotopyIso T Z e L' n).hom =
      (corepresentedHomologyHomotopyIso T Z e L n).hom ≫
        (preadditiveCoyoneda.obj (op ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
            ((CochainComplex.singleFunctor A 0).obj Z)))).map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map (g⟦n⟧')) := by
  have hinv : (T.mapHomologicalComplex (ComplexShape.up ℤ)).map g ≫
      (corepresentedHomComplexIso T Z e L').inv =
    (corepresentedHomComplexIso T Z e L).inv ≫
      homComplexPostcomp ((CochainComplex.singleFunctor A 0).obj Z) g := by
    rw [Iso.eq_inv_comp, ← Category.assoc, ← corepresentedHomComplexIso_hom_naturality T Z e g,
      Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have key : HomologicalComplex.homologyMap
        ((T.mapHomologicalComplex (ComplexShape.up ℤ)).map g) n ≫
      HomologicalComplex.homologyMap (corepresentedHomComplexIso T Z e L').inv n =
    HomologicalComplex.homologyMap (corepresentedHomComplexIso T Z e L).inv n ≫
      HomologicalComplex.homologyMap
        (homComplexPostcomp ((CochainComplex.singleFunctor A 0).obj Z) g) n := by
    rw [← HomologicalComplex.homologyMap_comp, ← HomologicalComplex.homologyMap_comp, hinv]
  rw [corepresentedHomologyHomotopyIso, corepresentedHomologyHomotopyIso, Iso.trans_hom,
    Iso.trans_hom, HomologicalComplex.homologyMapIso_hom, HomologicalComplex.homologyMapIso_hom,
    Iso.symm_hom, Iso.symm_hom, ← Category.assoc, key, Category.assoc, Category.assoc]
  congr 1
  ext x
  exact homComplexHomologyAddEquiv_postcomp ((CochainComplex.singleFunctor A 0).obj Z) g n x

/-- The comparison of `corepresentedHomologyHomotopyIso`, read as an additive equivalence. -/
noncomputable def corepresentedHomologyHomotopyAddEquiv (L : CochainComplex A ℤ) (n : ℤ) :
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).homology n ≃+
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor A 0).obj Z) ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj (L⟦n⟧)) :=
  (corepresentedHomologyHomotopyIso T Z e L n).addCommGroupIsoToAddEquiv

end Stacks.Cohomology.Corepresented
