module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexSingle
public import Mathlib.CategoryTheory.Abelian.Injective.Basic
public import StacksFrontier.Algebra.Homology.DerivedCategory.Opposite
public import StacksFrontier.Algebra.Homology.HomBicomplexExt
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The rows of the Hom bicomplex and their cohomology

Let `C` be an abelian category, let `K` and `I` be cochain complexes of `C`, and let
`B = CochainComplex.homBicomplex K I` be their Hom bicomplex, whose `(p, q)` term is
`Hom_C(K⁻ᵖ, Iᑫ)`. This file computes the cohomology of `B` in the two directions in the case
relevant to the two spectral sequences converging to `Ext` ([Stacks 07AA]), namely when `I` is an
injective resolution of an object `F` placed in degree `0`.

* **Rows.** The `p`-th row `B^{p,•} = Hom_C(K⁻ᵖ, I^•)` is the complex obtained by applying
  `Hom_C(K⁻ᵖ, -)` to `I`, and it is the Hom complex of `K⁻ᵖ` placed in degree `0` and `I`; its
  degree `q` cohomology is therefore `Extᑫ(K⁻ᵖ, F)`.
* **Columns.** The cohomology of `B` in the *first* direction is computed by the exactness of
  `Hom_C(-, Iᑫ)` for an injective `Iᑫ`: the degree `j` cohomology of `B` is the row
  `Hom_C(H⁻ʲ(K), I^•)`, so its degree `i` cohomology is `Extⁱ(H⁻ʲ(K), F)`.

The first is the first page of the termwise spectral sequence of [Stacks 07AA] and the second is
the second page of its hyper-Ext spectral sequence.

## Main definitions

* `CochainComplex.HomBicomplex.homComplexSingleIso`: the Hom complex out of an object placed in
  degree `0` is the complex obtained by applying the coyoneda functor of that object.
* `CochainComplex.HomBicomplex.rowIso`: a row of the Hom bicomplex, read as such a complex.
* `CochainComplex.HomBicomplex.coyonedaHomologyAddEquivZExt`: the cohomology of
  `Hom_C(M, I^•)` is `Ext^*(M, F)` for `I` an injective resolution of `F`.
* `CochainComplex.HomBicomplex.homologyIsoRow`: the cohomology of the Hom bicomplex in the first
  direction, for `I` with injective terms.

## Main results

* `CochainComplex.HomBicomplex.rowHomologyAddEquivZExt`: `H^q(B^{p,•}) = Extᑫ(K⁻ᵖ, F)`.
* `CochainComplex.HomBicomplex.homologyHomologyAddEquivZExt`:
  `H^i(H^j(B)) = Extⁱ(H⁻ʲ(K), F)`.

## Implementation notes

The identification of a row with a coyoneda row is `Iso.refl`: the Hom bicomplex is built by
`CategoryTheory.Functor.mapBifunctorHomologicalComplex`, whose rows are literally the complexes
obtained by applying the bifunctor in one variable. Stating it as a named isomorphism rather than
relying on the definitional equality at each use keeps the later statements readable.

The cohomology of the opposite complex is `CochainComplex.homologyOpNatIso`, the homology exchange
of `StacksFrontier/Algebra/Homology/DerivedCategory/Opposite.lean`: the degree `j` cohomology of the
complex of `Cᵒᵖ` that `K` becomes is the opposite of `H⁻ʲ(K)`. Going through it is what keeps this
file free of the reindexing gymnastics of `ComplexShape.embeddingUpIntDownInt`.

The cohomology-to-`Ext` identifications are *additive equivalences* rather than isomorphisms of
`AddCommGrpCat`, exactly as the ones of
`StacksFrontier/Algebra/Homology/HomBicomplexExt.lean` they are built from: the Hom complex is a
complex of `AddCommGrpCat.{v}` for `Category.{v} C`, while `Ext` groups in `D(C)` live in the
universe of the `Hom` groups of the derived category. No universe is identified with another.

## References

* [Stacks, Tag 06XR](https://stacks.math.columbia.edu/tag/06XR)
* [Stacks, Tag 07AA](https://stacks.math.columbia.edu/tag/07AA)
* [Stacks, Tag 0136](https://stacks.math.columbia.edu/tag/0136)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v u

namespace CochainComplex

namespace HomBicomplex

variable {C : Type u} [Category.{v} C] [Abelian C]

/-- **The Hom complex out of an object placed in degree `0`.** For `M : C` and a cochain complex
`I`, the Hom complex of the single complex `M` in degree `0` and `I` is the complex obtained by
applying `Hom_C(M, -)` to `I`: a cochain of degree `i` out of a single complex is the same thing
as a morphism `M ⟶ Iⁱ`, by `CochainComplex.HomComplex.Cochain.fromSingleEquiv`, and under that
identification the differential `δ` of the Hom complex becomes postcomposition with `I`'s
differential. -/
def homComplexSingleIso (M : C) (I : CochainComplex C ℤ) :
    ((CochainComplex.singleFunctor C 0).obj M).HomComplex I ≅
      ((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex (ComplexShape.up ℤ)).obj I := by
  refine HomologicalComplex.Hom.isoOfComponents
    (fun i => (CochainComplex.HomComplex.Cochain.fromSingleEquiv (X := M) (K := I)
      (p := 0) (q := i) (n := i) (by omega)).toAddCommGrpIso) ?_
  rintro i _ rfl
  ext x
  obtain ⟨f, rfl⟩ := CochainComplex.HomComplex.Cochain.fromSingleMk_surjective x i (by omega)
  change (preadditiveYoneda.map (I.d i (i + 1))).app (op M)
      (CochainComplex.HomComplex.Cochain.fromSingleEquiv (X := M) (K := I)
        (p := 0) (q := i) (n := i) (by omega)
        (CochainComplex.HomComplex.Cochain.fromSingleMk (X := M) (K := I) f (by omega))) =
    CochainComplex.HomComplex.Cochain.fromSingleEquiv (X := M) (K := I)
      (p := 0) (q := i + 1) (n := i + 1) (by omega)
      (CochainComplex.HomComplex.δ i (i + 1)
        (CochainComplex.HomComplex.Cochain.fromSingleMk (X := M) (K := I) f (by omega)))
  simp only [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]
  rw [CochainComplex.HomComplex.Cochain.δ_fromSingleMk (X := M) (K := I) f (by omega)
    (i + 1) (i + 1) (by omega)]
  change f ≫ I.d i (i + 1) = _
  rw [CochainComplex.HomComplex.Cochain.fromSingleEquiv_fromSingleMk]

/-- **The cohomology of `Hom_C(M, I^•)` is `Ext^*(M, F)`**, for `I` an injective resolution of
`F` placed in degree `0`: the complex `Hom_C(M, I^•)` is the Hom complex of the single complex
`M` and `I` (`homComplexSingleIso`), whose cohomology is the group of homotopy classes of maps
`M ⟶ I⟦i⟧`, which computes `Ext` by [Stacks 06XR]. -/
def coyonedaHomologyAddEquivZExt [HasDerivedCategory C] (M F : C) (I : CochainComplex C ℤ)
    {f : (CochainComplex.singleFunctor C 0).obj F ⟶ I}
    (hf : ExtByResolutions.IsInjectiveResolution f) (i : ℤ) :
    (((preadditiveCoyoneda.obj (op M)).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I).homology i ≃+ Abelian.zExt M F i :=
  (HomologicalComplex.homologyMapIso (homComplexSingleIso M I).symm
      i).addCommGroupIsoToAddEquiv.trans
    ((CochainComplex.HomComplex.homologyAddEquiv _ I i).trans
      (CochainComplex.HomComplex.CohomologyClass.homAddEquiv.trans
        ((postcompAddEquiv
            (((HomotopyCategory.quotient C (ComplexShape.up ℤ)).commShiftIso i).app I)).trans
          (extAddEquivOfInjectiveResolution
            ((CochainComplex.singleFunctor C 0).obj M) _ I i hf))))

/-- **A row of the Hom bicomplex.** The `p`-th row of `homBicomplex K I` is the complex obtained
by applying `Hom_C(K⁻ᵖ, -)` to `I`; the Hom bicomplex is built by
`CategoryTheory.Functor.mapBifunctorHomologicalComplex`, so this is an equality of complexes. -/
def rowIso (K I : CochainComplex C ℤ) (p : ℤ) :
    (homBicomplex K I).X p ≅
      ((preadditiveCoyoneda.obj (op (K.X (-p)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I :=
  Iso.refl _

/-- **The cohomology of a row of the Hom bicomplex is `Ext` out of a term of `K`.** For `I` an
injective resolution of `F` placed in degree `0`, the degree `q` cohomology of the `p`-th row
`Hom_C(K⁻ᵖ, I^•)` of `homBicomplex K I` is `Extᑫ(K⁻ᵖ, F)`. This is the first page of the termwise
spectral sequence of [Stacks 07AA]. -/
def rowHomologyAddEquivZExt [HasDerivedCategory C] (K I : CochainComplex C ℤ) (F : C)
    {f : (CochainComplex.singleFunctor C 0).obj F ⟶ I}
    (hf : ExtByResolutions.IsInjectiveResolution f) (p q : ℤ) :
    ((homBicomplex K I).X p).homology q ≃+ Abelian.zExt (K.X (-p)) F q :=
  (HomologicalComplex.homologyMapIso (rowIso K I p) q).addCommGroupIsoToAddEquiv.trans
    (coyonedaHomologyAddEquivZExt (K.X (-p)) F I hf q)

/-- **The cohomology of the Hom bicomplex in the first direction**, for `I` with injective terms:
the degree `j` cohomology of `homBicomplex K I`, taken in the direction of the first index, is the
row `Hom_C(H⁻ʲ(K), I^•)`.

Each functor `Hom_C(-, Iᑫ)` is exact ([Stacks 0136]), so it commutes with the cohomology of the
complex `Kᵒᵖ` which fills the first slot; the cohomology of `Kᵒᵖ` in degree `j` is the opposite of
`H⁻ʲ(K)` by `CochainComplex.homologyOpNatIso`. -/
def homologyIsoRow (K I : CochainComplex C ℤ) (hI : ∀ i, Injective (I.X i)) (j : ℤ) :
    (homBicomplex K I).homology j ≅
      ((preadditiveCoyoneda.obj (op (K.homology (-j)))).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj I := by
  have hyoneda : ∀ i : ℤ, (preadditiveYoneda.obj (I.X i)).PreservesHomology := by
    intro i
    have := (Injective.injective_iff_preservesEpimorphisms_preadditiveYoneda_obj
      (I.X i)).mp (hI i)
    exact Functor.preservesHomology_of_preservesEpis_and_kernels _
  have hrow : (homBicomplex K I).homology j ≅
      ((preadditiveCoyoneda.obj
        (((CochainComplex.opEquivalence C).functor.obj (op K)).homology j)).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj I := by
    let Kop := (CochainComplex.opEquivalence C).functor.obj (op K)
    let T := ((preadditiveCoyoneda.obj (Kop.homology j)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj I
    let S := (homBicomplex K I).sc j
    let ev (i : ℤ) := HomologicalComplex.eval AddCommGrpCat (ComplexShape.up ℤ) i
    let e₁ (i : ℤ) : (S.map (ev i)).homology ≅ (ev i).obj S.homology := S.mapHomologyIso (ev i)
    let e₂ (i : ℤ) : (S.map (ev i)).homology ≅
        ((Kop.sc j).map (preadditiveYoneda.obj (I.X i))).homology := Iso.refl _
    let e₃ (i : ℤ) : ((Kop.sc j).map (preadditiveYoneda.obj (I.X i))).homology ≅
        (preadditiveYoneda.obj (I.X i)).obj ((Kop.sc j).homology) :=
      have := hyoneda i
      (Kop.sc j).mapHomologyIso (preadditiveYoneda.obj (I.X i))
    let e : ∀ i : ℤ, S.homology.X i ≅ T.X i := fun i => (e₁ i).symm ≪≫ e₂ i ≪≫ e₃ i
    refine HomologicalComplex.Hom.isoOfComponents e ?_
    rintro i _ rfl
    let τ := HomologicalComplex.dNatTrans AddCommGrpCat (ComplexShape.up ℤ) i (i + 1)
    have := hyoneda i
    have := hyoneda (i + 1)
    let η := preadditiveYoneda.map (I.d i (i + 1))
    dsimp only [e]
    change (e₁ i).inv ≫ (e₂ i).hom ≫ (e₃ i).hom ≫ η.app ((Kop.sc j).homology) =
      τ.app S.homology ≫ (e₁ (i + 1)).inv ≫ (e₂ (i + 1)).hom ≫ (e₃ (i + 1)).hom
    rw [NatTrans.app_homology η (Kop.sc j), (e₃ i).hom_inv_id_assoc, NatTrans.app_homology τ S]
    simp only [Category.assoc]
    rw [(e₁ (i + 1)).hom_inv_id_assoc]
    congr 1
  exact hrow ≪≫ (NatIso.mapHomologicalComplex
    (preadditiveCoyoneda.mapIso ((CochainComplex.homologyOpNatIso j).app (op K)))
    (ComplexShape.up ℤ)).app I

/-- **The iterated cohomology of the Hom bicomplex is `Ext` out of the cohomology of `K`.** For
`I` an injective resolution of `F` placed in degree `0`, the degree `i` cohomology of the degree
`j` cohomology of `homBicomplex K I` is `Extⁱ(H⁻ʲ(K), F)`. This is the second page of the
hyper-Ext spectral sequence of [Stacks 07AA]. -/
@[sga "2 VIII 1.4" "special case"]
def homologyHomologyAddEquivZExt [HasDerivedCategory C] (K I : CochainComplex C ℤ) (F : C)
    {f : (CochainComplex.singleFunctor C 0).obj F ⟶ I}
    (hf : ExtByResolutions.IsInjectiveResolution f) (i j : ℤ) :
    ((homBicomplex K I).homology j).homology i ≃+ Abelian.zExt (K.homology (-j)) F i :=
  (HomologicalComplex.homologyMapIso (homologyIsoRow K I hf.injective j)
      i).addCommGroupIsoToAddEquiv.trans
    (coyonedaHomologyAddEquivZExt (K.homology (-j)) F I hf i)

end HomBicomplex

end CochainComplex

end
