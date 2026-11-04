module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import Mathlib.Algebra.Homology.HomotopyCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.Pretriangulated

/-!
# Acyclicity of a Hom complex, read in the homotopy category

For cochain complexes `K` and `L` in an abelian category, the degree-`n` cohomology of Mathlib's
Hom complex `CochainComplex.HomComplex K L` is the group of morphisms `K ⟶ L⟦n⟧` in the homotopy
category. So acyclicity of `Hom(K, L)` is the vanishing of all of those groups, and the two
triangulated moves on them — along a distinguished triangle in the source and along one in the
target — become statements about mapping cones:

* the Hom complex out of the target of a morphism is acyclic as soon as the Hom complexes out of
  its source and out of its mapping cone are;
* the Hom complex into the mapping cone of a morphism is acyclic as soon as the Hom complexes
  into its source and into its target are.

Together with the vanishing at a K-injective target these are what reduces an acyclicity
statement about a Hom complex to acyclicity statements about the three terms of a triangle.

## Main results

* `CochainComplex.acyclic_homComplex_iff`: acyclicity of `Hom(K, L)` is the vanishing of every
  morphism `K ⟶ L⟦n⟧` of the homotopy category, for every `n`.
* `CochainComplex.acyclic_homComplex_of_isKInjective`: the Hom complex out of an acyclic complex
  into a K-injective complex is acyclic.
* `CochainComplex.acyclic_homComplex_of_mappingCone`: the move in the source variable.
* `CochainComplex.acyclic_homComplex_mappingCone`: the move in the target variable.

## Implementation notes

`CochainComplex.HomComplex.homologyAddEquiv` and
`CochainComplex.HomComplex.CohomologyClass.homAddEquiv` are the two identifications behind
`acyclic_homComplex_iff`, and `AddCommGrpCat.isZero_iff_subsingleton` turns exactness into the
vanishing of the group. The vanishing is stated as `∀ φ, φ = 0` rather than as `Subsingleton`,
because the groups in question are not instance-visible and a `Subsingleton` hypothesis on one of
them is not found by instance search at the point of use.

The shift is applied to the *image* of the complex, `(Q L)⟦n⟧` rather than `Q (L⟦n⟧)`: that is
the spelling in which the objects of a shifted distinguished triangle appear, and it is what the
move in the target variable consumes. The commutation isomorphism
`CategoryTheory.Functor.commShiftIso` of the quotient functor with the shift mediates between the
two, once, inside `acyclic_homComplex_iff`.

The move in the source variable is `CategoryTheory.Pretriangulated.Triangle.yoneda_exact₂` at
`CochainComplex.mappingCone.triangleh`, and needs no shift: the target of the morphisms being
killed is fixed while the triangle varies in the source. The move in the target variable is
`CategoryTheory.Pretriangulated.Triangle.coyoneda_exact₃` at the `n`-fold shift of that triangle,
distinguished by `CategoryTheory.Pretriangulated.Triangle.shift_distinguished`. The third map of
that shifted triangle lands in `(Q A)⟦n⟧⟦1⟧`, while the hypothesis speaks of `(Q A)⟦n + 1⟧`;
`CategoryTheory.shiftFunctorAdd'` is what re-reads the one as the other.

`CategoryTheory.shiftFunctorAdd'` is written with its namespace: inside `CochainComplex` the
unqualified name resolves to the cochain-complex one, whose argument is a complex of objects of
the homotopy category rather than an object of it.

Both triangle steps end on a goal `0 = 0` that the rewrite does not close, because the two zero
morphisms are at the two spellings of one object — `(mappingCone.triangleh f).obj₃` against
`Q (mappingCone f)` — which are definitionally but not syntactically equal; `rfl` closes it.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe v u

namespace CochainComplex

/-- A morphism into an object isomorphic to one receiving only the zero morphism is zero. -/
theorem hom_eq_zero_of_iso {D : Type*} [Category D] [Preadditive D] {X Y Y' : D}
    (e : Y ≅ Y') (h : ∀ φ : X ⟶ Y', φ = 0) (φ : X ⟶ Y) : φ = 0 := by
  calc φ = (φ ≫ e.hom) ≫ e.inv := by rw [Category.assoc, e.hom_inv_id, Category.comp_id]
    _ = 0 := by rw [h (φ ≫ e.hom), zero_comp]

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **Acyclicity of a Hom complex is the vanishing of the homotopy-category morphisms into the
shifts of its target.** -/
theorem acyclic_homComplex_iff (K L : CochainComplex C ℤ) :
    (HomComplex K L).Acyclic ↔ ∀ (n : ℤ)
      (φ : (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
        ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj L)⟦n⟧), φ = 0 := by
  refine forall_congr' fun n => ?_
  let e : (HomComplex K L).homology n ≃+
      ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj (L⟦n⟧)) :=
    (HomComplex.homologyAddEquiv K L n).trans HomComplex.CohomologyClass.homAddEquiv
  let i := ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso n).app L
  rw [HomologicalComplex.exactAt_iff_isZero_homology, AddCommGrpCat.isZero_iff_subsingleton]
  refine ⟨fun h => hom_eq_zero_of_iso i.symm fun φ => ?_, fun h => ⟨fun x y => e.injective ?_⟩⟩
  · simpa using e.symm.injective (Subsingleton.elim (e.symm φ) (e.symm 0))
  · rw [hom_eq_zero_of_iso i h (e x), hom_eq_zero_of_iso i h (e y)]

/-- **The Hom complex out of an acyclic complex into a K-injective complex is acyclic.** -/
theorem acyclic_homComplex_of_isKInjective (K L : CochainComplex C ℤ) (hK : K.Acyclic)
    [L.IsKInjective] : (HomComplex K L).Acyclic := by
  rw [acyclic_homComplex_iff]
  intro n
  refine hom_eq_zero_of_iso
    (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso n).app L).symm ?_
  intro φ
  obtain ⟨φ, rfl⟩ := (HomotopyCategory.quotient C (ComplexShape.up ℤ)).map_surjective φ
  rw [HomotopyCategory.eq_of_homotopy φ 0 (IsKInjective.homotopyZero φ hK), Functor.map_zero]

/-- **The move in the source variable**: the Hom complex out of the target of a morphism of
cochain complexes is acyclic as soon as the Hom complexes out of its source and out of its
mapping cone are. -/
theorem acyclic_homComplex_of_mappingCone {A B : CochainComplex C ℤ} (f : A ⟶ B)
    (X : CochainComplex C ℤ) (hA : (HomComplex A X).Acyclic)
    (hcone : (HomComplex (mappingCone f) X).Acyclic) :
    (HomComplex B X).Acyclic := by
  rw [acyclic_homComplex_iff] at hA hcone ⊢
  intro n φ
  obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ (mappingCone.triangleh f)
    (HomotopyCategory.mappingCone_triangleh_distinguished f) φ (hA n _)
  have hg0 : g = 0 := hcone n g
  rw [hg, hg0, comp_zero]
  rfl

/-- **The move in the target variable**: the Hom complex into the mapping cone of a morphism of
cochain complexes is acyclic as soon as the Hom complexes into its source and into its target
are. -/
theorem acyclic_homComplex_mappingCone (Z : CochainComplex C ℤ) {A B : CochainComplex C ℤ}
    (q : A ⟶ B) (hA : (HomComplex Z A).Acyclic) (hB : (HomComplex Z B).Acyclic) :
    (HomComplex Z (mappingCone q)).Acyclic := by
  rw [acyclic_homComplex_iff] at hA hB ⊢
  intro n φ
  set T := (Triangle.shiftFunctor (HomotopyCategory C (ComplexShape.up ℤ)) n).obj
    (mappingCone.triangleh q)
  have hzero : φ ≫ T.mor₃ = 0 :=
    hom_eq_zero_of_iso
      ((CategoryTheory.shiftFunctorAdd' (HomotopyCategory C (ComplexShape.up ℤ)) n 1 (n + 1)
        rfl).app ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj A)).symm
        (hA (n + 1)) _
  obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ T
    (Triangle.shift_distinguished _
      (HomotopyCategory.mappingCone_triangleh_distinguished q) n) φ hzero
  have hg0 : g = 0 := hB n g
  rw [hg, hg0, zero_comp]
  rfl

end CochainComplex

end
