module

public import StacksFrontier.Algebra.Homology.DerivedCategory.ConeHomologyFunctor07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.CosimplicialDeRhamZigzag07Q9
public import StacksFrontier.AlgebraicGeometry.Crystalline.Cosimplicial.PairHomColumnZero07Q9

/-!
# Cone cohomology of the column zero from the row zero

For a morphism `F : W ⟶ W'` of cosimplicial pairs whose double complexes have acyclic columns
`a > 0` and quasi-isomorphic coprojections of rows, the zigzag of [Stacks, Tag 07LG]

`M(•) ⟵ Tot(K) ⟶ Tot(Const(K^{*,0})) ⟵ K^{*,0}`

is natural in `F` and made of quasi-isomorphisms, so the morphism of Moore complexes of the
columns zero and the morphism of the completed de Rham complexes of the rows zero have isomorphic
images in the arrow category of the derived category.  In particular a scalar killing the
cohomology of the mapping cone of the second kills that of the first
(`smul_id_homology_columnZeroMooreMap_of_degreeDeRhamMap`).  This is the step of the proof of
[Stacks, Tag 07Q9] that reads the comparison of crystalline cohomology off the de Rham complexes.

## References

* [Stacks Project, Lemma 60.26.3, Tag 07Q9](https://stacks.math.columbia.edu/tag/07Q9)
* [Stacks Project, Proposition 60.21.3, Tag 07LG](https://stacks.math.columbia.edu/tag/07LG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicTopology DividedPowers

universe u v w w'

namespace Crystalline.CosimplicialCompletedPair.Hom

open Stacks.ConeLadder

variable {A : Type u} [CommRing A] {E E' : CosimplicialDPAlgebra.{u, v} A} {p : ℕ}
  {g : E.Hom E'} {W : CosimplicialCompletedPair.{u, v, w} E p}
  {W' : CosimplicialCompletedPair.{u, v, w} E' p} (F : Hom g W W')

/-- **The cone of the morphism of Moore complexes of the columns zero has its cohomology killed
by every scalar killing the cohomology of the cone of the morphism of the rows zero**, under the
hypotheses making the zigzag of [Stacks, Tag 07LG] consist of quasi-isomorphisms on both sides. -/
theorem smul_id_homology_columnZeroMooreMap_of_degreeDeRhamMap (q : ℤ)
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W.doubleComplex.X n)).homology j))
    (hrow : ∀ b : ℕ, QuasiIso (W.rowFromZeroHom b))
    (hcol' : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W'.doubleComplex.X n)).homology j))
    (hrow' : ∀ b : ℕ, QuasiIso (W'.rowFromZeroHom b))
    (h : ∀ j : ℤ, q • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap
      (F.degreeDeRhamMap 0) ComplexShape.embeddingUpNat)).homology j) = 0) (j : ℤ) :
    q • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap F.columnZeroMooreMap
      ComplexShape.embeddingUpNat)).homology j) = 0 := by
  let := HasDerivedCategory.standard AddCommGrpCat.{max v w}
  have := W.quasiIso_zigzagColumnZero hcol
  have := W'.quasiIso_zigzagColumnZero hcol'
  have := W.quasiIso_zigzagTotal hrow
  have := W'.quasiIso_zigzagTotal hrow'
  refine (coneHomologyKilled_Q_map_iff q _).1 ?_ j
  refine ConeHomologyKilled.of_arrowIso (arrowIsoOfQuasiIso _ _ W.zigzagColumnZero
    W'.zigzagColumnZero F.zigzagColumnZero_naturality).symm ?_
  refine ConeHomologyKilled.of_arrowIso (arrowIsoOfQuasiIso _ _ W.zigzagTotal
    W'.zigzagTotal F.zigzagTotal_naturality.symm) ?_
  refine ConeHomologyKilled.of_arrowIso (arrowIsoOfQuasiIso _ _ W.zigzagRowZero
    W'.zigzagRowZero F.zigzagRowZero_naturality.symm).symm ?_
  exact (coneHomologyKilled_Q_map_iff q _).2 h

variable [∀ b, IsAdicComplete (pAdicIdeal (A := E.completedRing p b) p) (W.carrier b)]
  [∀ b, IsAdicComplete (pAdicIdeal (A := E'.completedRing p b) p) (W'.carrier b)]

/-- **The cone of the morphism of Moore complexes of the cosimplicial modules has its cohomology
killed by every scalar killing the cohomology of the cone of the morphism of the rows zero.**  The
Moore complexes of the columns zero of the double complexes are those of the cosimplicial modules
(`columnZeroMooreMap_columnZeroIso07Q9`). -/
theorem smul_id_homology_carrierMooreMap_of_degreeDeRhamMap (q : ℤ)
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W.doubleComplex.X n)).homology j))
    (hrow : ∀ b : ℕ, QuasiIso (W.rowFromZeroHom b))
    (hcol' : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W'.doubleComplex.X n)).homology j))
    (hrow' : ∀ b : ℕ, QuasiIso (W'.rowFromZeroHom b))
    (h : ∀ j : ℤ, q • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap
      (F.degreeDeRhamMap 0) ComplexShape.embeddingUpNat)).homology j) = 0) (j : ℤ) :
    q • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap
      ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).map F.carrierMap07Q9)
      ComplexShape.embeddingUpNat)).homology j) = 0 := by
  refine smul_id_homology_mappingCone_extend_of_arrowIso q
    (Arrow.isoMk ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).mapIso
        W.toCosimplicialCompletedModule.columnZeroIso).symm
      ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).mapIso
        W'.toCosimplicialCompletedModule.columnZeroIso).symm ?_)
    (F.smul_id_homology_columnZeroMooreMap_of_degreeDeRhamMap q hcol hrow hcol' hrow' h) j
  change ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).mapIso
      W.toCosimplicialCompletedModule.columnZeroIso).inv ≫ F.columnZeroMooreMap =
    (alternatingCofaceMapComplex AddCommGrpCat.{max v w}).map F.carrierMap07Q9 ≫
      ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).mapIso
        W'.toCosimplicialCompletedModule.columnZeroIso).inv
  exact (Iso.inv_comp_eq _).2 (((Iso.eq_comp_inv _).2
    F.columnZeroMooreMap_columnZeroIso07Q9).trans (Category.assoc _ _ _))

/-- **The per-open step of [Stacks, Tag 07Q9] from the de Rham side**: a morphism `φ` of
`ℕ`-indexed complexes of abelian groups (in the application, the Čech pullback of sections of the
crystal) which is isomorphic, as an arrow, to the universe lift of the morphism of Moore complexes
of the cosimplicial modules of a morphism of pairs, has mapping cone with cohomology killed by
every scalar killing the cohomology of the cone of the morphism of the rows zero. -/
theorem smul_id_homology_of_arrowIso_ulift_carrierMooreMap (q : ℤ)
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W.doubleComplex.X n)).homology j))
    (hrow : ∀ b : ℕ, QuasiIso (W.rowFromZeroHom b))
    (hcol' : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W'.doubleComplex.X n)).homology j))
    (hrow' : ∀ b : ℕ, QuasiIso (W'.rowFromZeroHom b))
    {K L : CochainComplex AddCommGrpCat.{max (max v w) w'} ℕ} (φ : K ⟶ L)
    (i : Arrow.mk φ ≅ Arrow.mk ((AddCommGrpCat.uliftFunctor.{w', max v w}.mapHomologicalComplex
      _).map ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).map F.carrierMap07Q9)))
    (h : ∀ j : ℤ, q • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap
      (F.degreeDeRhamMap 0) ComplexShape.embeddingUpNat)).homology j) = 0) (j : ℤ) :
    q • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap φ
      ComplexShape.embeddingUpNat)).homology j) = 0 :=
  smul_id_homology_mappingCone_of_arrowIso_map AddCommGrpCat.uliftFunctor.{w', max v w} q φ _ i
    (F.smul_id_homology_carrierMooreMap_of_degreeDeRhamMap q hcol hrow hcol' hrow' h) j

omit [∀ b, IsAdicComplete (pAdicIdeal (A := E.completedRing p b) p) (W.carrier b)]
  [∀ b, IsAdicComplete (pAdicIdeal (A := E'.completedRing p b) p) (W'.carrier b)] in
/-- `smul_id_homology_of_arrowIso_ulift_carrierMooreMap` with the completeness of the modules of
the two pairs as explicit hypotheses. -/
theorem smul_id_homology_of_arrowIso_ulift_carrierMooreMap_of_complete (q : ℤ)
    (hc : ∀ b, IsAdicComplete (pAdicIdeal (A := E.completedRing p b) p) (W.carrier b))
    (hc' : ∀ b, IsAdicComplete (pAdicIdeal (A := E'.completedRing p b) p) (W'.carrier b))
    (hcol : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W.doubleComplex.X n)).homology j))
    (hrow : ∀ b : ℕ, QuasiIso (W.rowFromZeroHom b))
    (hcol' : ∀ n : ℕ, 0 < n → ∀ j : ℕ,
      IsZero (((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).obj
        (W'.doubleComplex.X n)).homology j))
    (hrow' : ∀ b : ℕ, QuasiIso (W'.rowFromZeroHom b))
    {K L : CochainComplex AddCommGrpCat.{max (max v w) w'} ℕ} (φ : K ⟶ L)
    (i : Arrow.mk φ ≅ Arrow.mk ((AddCommGrpCat.uliftFunctor.{w', max v w}.mapHomologicalComplex
      _).map ((alternatingCofaceMapComplex AddCommGrpCat.{max v w}).map
        F.carrierMap07Q9)))
    (h : ∀ j : ℤ, q • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap
      (F.degreeDeRhamMap 0) ComplexShape.embeddingUpNat)).homology j) = 0) (j : ℤ) :
    q • 𝟙 ((CochainComplex.mappingCone (HomologicalComplex.extendMap φ
      ComplexShape.embeddingUpNat)).homology j) = 0 :=
  have := hc
  have := hc'
  F.smul_id_homology_of_arrowIso_ulift_carrierMooreMap q hcol hrow hcol' hrow' φ i h j

end Crystalline.CosimplicialCompletedPair.Hom
