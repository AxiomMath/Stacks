module

public import StacksFrontier.CategoryTheory.Adjunction.PullbackInternalHomPushforward
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.AssociativityGeneral
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingCounitFormula
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedCurryingOnModels
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorMonoidalClosed
public import
  StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorSheafHomAdjunctionSlot
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.UncurryTensorHomInterchange
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorHomDiagonalModels
public meta import StacksFrontier.Tactic.HEqCongr

/-!
# The diagonal of Stacks 0BYS is the adjoint of the associator followed by evaluation

Let `X` be a ringed site and `P`, `K`, `M` objects of `D(O)`. The diagonal morphism of
Stacks 0BYS,

`P ⊗^𝐋_O RSheafHom(M, K) ⟶ RSheafHom(M, P ⊗^𝐋_O K)`,

constructed from complex models (`AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal`), is
the morphism corresponding under the tensor–internal-Hom adjunction of Stacks 08J8 to

`(P ⊗^𝐋 RSheafHom(M, K)) ⊗^𝐋 M ≅ P ⊗^𝐋 (RSheafHom(M, K) ⊗^𝐋 M) ⟶ P ⊗^𝐋 K`,

the associativity constraint of Stacks 0FPT followed by `P ⊗^𝐋 -` of the evaluation morphism;
that is, it is `CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal` for the derived tensor
product, the derived internal Hom and the adjunction of Stacks 08J8.

## Main results

* `AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_derivedTensorHomDiagonal_of_models`: the
  transpose of the diagonal under Stacks 08J8 is the associator followed by the evaluation.
* `AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_eq_leftTensorHomDiagonal`: the two
  descriptions of the diagonal agree.

## Implementation notes

The identification is checked on models: a K-flat `A` for `P`, a K-flat `B` for `M`, a
K-injective `I` for `K` and a K-flat resolution `s : F ⟶ SheafHom(B, I)`. Precomposing with the
class of `s`, the transposes of both sides are computed by the bijection of Stacks 08J8 on
representatives (`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv_model`), the associator on
K-flat complexes (`Stacks.SheafOfModules.DerivedTensorProduct.comparison_tensorComplexAssociator`)
and the characterisation of the diagonal at arbitrary models
(`AlgebraicGeometry.RingedSite.derivedTensorHomDiagonal_eq_ofModels`), and the comparison comes
down to the chain-level identity
`AlgebraicGeometry.RingedSite.uncurryMap_tensorHomInterchange`.

## References

* [Stacks Project, Tag 0BYS](https://stacks.math.columbia.edu/tag/0BYS)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.RingedSite

universe u

attribute [local instance] HasDerivedCategory.standard

attribute [local instance 5000] SheafOfModules.instAbelian

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]

/-- The hom-set bijection of the adjunction of Stacks 08J8 is the inverse of the bijection
`AlgebraicGeometry.RingedSite.derivedCurryHomEquiv` it is built from. -/
theorem derivedTensorSheafHomAdjunction_homEquiv_apply
    (A B Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
    (f : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj A).obj B ⟶ Z) :
    ((derivedTensorSheafHomAdjunction X B).homEquiv A Z) f =
      (derivedCurryHomEquiv X A B Z).symm f := by
  rw [derivedTensorSheafHomAdjunction, Adjunction.mkOfHomEquiv_homEquiv, Equiv.coe_fn_mk]

/-- **Reducing the identification of the diagonal along an isomorphism onto the internal Hom.**
If the transpose of `δ` agrees with the associator followed by the evaluation after
precomposing with `P ⊗^𝐋 σ` for an isomorphism `σ : Z ⟶ RSheafHom(M, K)`, it agrees without. -/
theorem derivedCurryHomEquiv_eq_of_whiskerLeft
    {P M K Z : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (σ : Z ⟶ ((derivedSheafHomBifunctor X).obj (op M)).obj K) [IsIso σ]
    (δ : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).obj
        (((derivedSheafHomBifunctor X).obj (op M)).obj K) ⟶
      ((derivedSheafHomBifunctor X).obj (op M)).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).obj K))
    (h : derivedCurryHomEquiv X _ M _
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).map σ ≫ δ) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).associatorGeneral P Z M).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).map
          (derivedCurryHomEquiv X Z M K σ)) :
    derivedCurryHomEquiv X _ M _ δ =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).associatorGeneral P
          (((derivedSheafHomBifunctor X).obj (op M)).obj K) M).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).map
          (derivedSheafHomCounit X M K) := by
  have h1 := derivedCurryHomEquiv_naturality_source X
    (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).map σ) δ
  have h2 := derivedCurryHomEquiv_apply X Z M K σ
  have h3 :=
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).associatorGeneral_naturality_middle
      P σ M
  rw [h1, h2, CategoryTheory.Functor.map_comp, ← reassoc_of% h3] at h
  exact (cancel_epi _).1 h

/-- **The evaluation on a K-flat resolution of an internal Hom complex.** For K-flat `F`, `B`,
a K-injective `I` and `s : F ⟶ SheafHom(B, I)`, the transpose of the class of `s` is the K-flat
comparison followed by the class of the uncurrying of `s`. -/
theorem derivedCurryHomEquiv_Q_map_comp_inv
    {M K : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {F B I : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (hF : Stacks.SheafOfModules.IsKFlat X.O F) (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (eB : DerivedCategory.Q.obj B ≅ M) (eI : DerivedCategory.Q.obj I ≅ K)
    (s : F ⟶ (sheafHomComplex X B I).obj) :
    derivedCurryHomEquiv X (DerivedCategory.Q.obj F) M K
        (DerivedCategory.Q.map s ≫
          (derivedSheafHomObjectsModelIso X eB eI ≪≫ derivedSheafHomComparison X B I).inv) =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
          (DerivedCategory.Q.obj F)).map eB.inv ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight F B hB).hom ≫
          DerivedCategory.Q.map (uncurryMap X s) ≫ eI.hom := by
  have hT := Stacks.SheafOfModules.kFlat_tensorComplex X.O hF hB
  have hm := derivedCurryHomEquiv_model X F B I hF hB hT s (uncurryMap X s)
    (homologyMap_globalHomologyClass_uncurryMap X s)
  have hn := derivedCurryHomEquiv_comp_map_of_id X (DerivedCategory.Q.obj F)
    (DerivedCategory.Q.obj B) M (DerivedCategory.Q.obj I) K eB.inv eI.hom
    (DerivedCategory.Q.map s ≫ (derivedSheafHomComparison X B I).inv)
  have hiso : (derivedSheafHomObjectsModelIso X eB eI ≪≫ derivedSheafHomComparison X B I).inv =
      (derivedSheafHomComparison X B I).inv ≫
        (((derivedSheafHomBifunctor X).map eB.inv.op).app (DerivedCategory.Q.obj I) ≫
          ((derivedSheafHomBifunctor X).obj (op M)).map eI.hom) := by
    simp only [derivedSheafHomObjectsModelIso, Iso.trans_inv, CategoryTheory.Functor.mapIso_inv,
      Iso.app_inv, Iso.symm_inv, Iso.op_inv]
    congr 1
    exact ((derivedSheafHomBifunctor X).map eB.inv.op).naturality eI.hom
  rw [hiso, ← Category.assoc, hn, hm, Category.assoc]

/-- The source comparison of the diagonal at arbitrary models, precomposed with the class of a
morphism `s : F ⟶ SheafHom(B, I)`, is the K-flat comparison at `(A, F)` followed by
`Tot(A ⊗ s)`. -/
theorem whiskerLeft_comp_derivedTensorHomSourceIsoOfModels_hom
    {P K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A I B F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (eA : DerivedCategory.Q.obj A ≅ P)
    (eI : DerivedCategory.Q.obj I ≅ K) (eB : DerivedCategory.Q.obj B ≅ M)
    (s : F ⟶ (sheafHomComplex X B I).obj) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).map
        (DerivedCategory.Q.map s ≫
          (derivedSheafHomObjectsModelIso X eB eI ≪≫ derivedSheafHomComparison X B I).inv) ≫
        (derivedTensorHomSourceIsoOfModels X hA eA eI eB).hom =
      ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map eA.inv).app
          (DerivedCategory.Q.obj F) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A F hA).hom ≫
          DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A F).inv ≫
            DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) s) := by
  dsimp only [derivedTensorHomSourceIsoOfModels, Iso.trans_hom, CategoryTheory.Functor.mapIso_hom,
    Iso.app_hom, Iso.symm_hom, CategoryTheory.Functor.mapIso_inv]
  rw [← Category.assoc, ← CategoryTheory.Functor.map_comp]
  simp only [Iso.trans_inv, Category.assoc, Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [reassoc_of% (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map eA.inv).naturality
      (DerivedCategory.Q.map s))]
  rw [comparisonLeft_tensorTotal_naturality_right X A s hA]

/-- The inverse of the target comparison of the diagonal at arbitrary models, written as a
morphism out of the class of `SheafHom(B, J)` followed by maps induced in the two variables of
the derived internal Hom. -/
theorem derivedTensorHomTargetIsoOfModels_inv_eq
    {P K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A I B J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [J.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (eA : DerivedCategory.Q.obj A ≅ P)
    (eI : DerivedCategory.Q.obj I ≅ K) (eB : DerivedCategory.Q.obj B ≅ M)
    (q : tensorTotal X A I ⟶ J) (hq : IsIso (DerivedCategory.Q.map q)) :
    (derivedTensorHomTargetIsoOfModels X hA eA eI eB q hq).inv =
      (derivedSheafHomComparison X B J).inv ≫
        (((derivedSheafHomBifunctor X).map eB.inv.op).app (DerivedCategory.Q.obj J) ≫
          ((derivedSheafHomBifunctor X).obj (op M)).map
            (inv (DerivedCategory.Q.map q) ≫
              (derivedTensorObjectsIsoOfModels X hA eA eI).inv)) := by
  dsimp only [derivedTensorHomTargetIsoOfModels, Iso.trans_inv, CategoryTheory.Functor.mapIso_inv,
    Iso.app_inv, asIso_inv, Iso.op_inv]
  rw [CategoryTheory.Functor.map_comp, Iso.op_inv]
  simp only [Category.assoc]
  rw [reassoc_of% (((derivedSheafHomBifunctor X).map eB.inv.op).naturality
    (inv (DerivedCategory.Q.map q)))]

/-- The diagram chase closing the identification of the diagonal on models, in an arbitrary
category with a bifunctor, every morphism being a variable. -/
private theorem diagonal_models_chase {D : Type*} [Category D] (T : D ⥤ D ⥤ D)
    {P QA QF QB M K QI QT QTB QFB QAFB QAI QJ QTI : D}
    (eA : QA ≅ P) (b : M ⟶ QB) (e : QI ⟶ K)
    (c : (T.obj QA).obj QF ⟶ QT) (r : (T.obj QT).obj QB ⟶ QTB)
    (r' : (T.obj QF).obj QB ⟶ QFB) (c'' : (T.obj QA).obj QFB ⟶ QAFB) (xa : QTB ⟶ QAFB)
    (xm : QAFB ⟶ QAI) (l : (T.obj QA).obj QI ≅ QAI) (ev : QFB ⟶ QI) (big : QTB ⟶ QJ)
    (iq : QJ ⟶ QTI) (qth : QTI ⟶ QAI)
    (α₁ : (T.obj ((T.obj P).obj QF)).obj M ⟶ (T.obj P).obj ((T.obj QF).obj M))
    (α₂ : (T.obj ((T.obj P).obj QF)).obj QB ⟶ (T.obj P).obj ((T.obj QF).obj QB))
    (α₃ : (T.obj ((T.obj QA).obj QF)).obj QB ⟶ (T.obj QA).obj ((T.obj QF).obj QB))
    (hbig : big ≫ iq ≫ qth = xa ≫ xm)
    (h4 : (T.map c).app QB ≫ r ≫ xa = α₃ ≫ (T.obj QA).map r' ≫ c'')
    (h5 : (T.obj QA).map ev ≫ l.hom = c'' ≫ xm)
    (hR : (T.obj ((T.obj P).obj QF)).map b ≫ α₂ = α₁ ≫ (T.obj P).map ((T.obj QF).map b))
    (hL : (T.map ((T.map eA.inv).app QF)).app QB ≫ α₃ =
      α₂ ≫ (T.map eA.inv).app ((T.obj QF).obj QB)) :
    (((T.map ((T.map eA.inv).app QF ≫ c)).app M ≫ (T.obj QT).map b) ≫ (r ≫ big) ≫ iq ≫ qth ≫
        l.inv ≫ (T.obj QA).map e ≫ (T.map eA.hom).app K) =
      α₁ ≫ (T.obj P).map ((T.obj QF).map b ≫ r' ≫ ev ≫ e) := by
  have h5' : c'' ≫ xm ≫ l.inv = (T.obj QA).map ev := by
    rw [← reassoc_of% h5, Iso.hom_inv_id, Category.comp_id]
  have hsw : ∀ {Y Y' : D} (g : Y ⟶ Y'),
      (T.map eA.inv).app Y ≫ (T.obj QA).map g = (T.obj P).map g ≫ (T.map eA.inv).app Y' :=
    fun g => ((T.map eA.inv).naturality g).symm
  have hinv : (T.map eA.inv).app K ≫ (T.map eA.hom).app K = 𝟙 _ := by
    rw [← NatTrans.comp_app, ← CategoryTheory.Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, NatTrans.id_app]
  simp only [CategoryTheory.Functor.map_comp, NatTrans.comp_app, Category.assoc]
  rw [← reassoc_of% ((T.map c).naturality b),
    ← reassoc_of% ((T.map ((T.map eA.inv).app QF)).naturality b), ← reassoc_of% hR]
  congr 1
  rw [reassoc_of% hbig, reassoc_of% h4, reassoc_of% h5', reassoc_of% hL, reassoc_of% (hsw r'),
    reassoc_of% (hsw ev), reassoc_of% (hsw e), hinv, Category.comp_id]

/-- **The left K-flat comparison is natural in the second complex**, at the uncurrying
`F ⊗ B ⟶ I` of a morphism `s : F ⟶ SheafHom(B, I)`, with the left comparison at the K-flat
complex `F ⊗ B` read as the K-flat comparison. -/
theorem tensorObj_map_Q_map_uncurryMap_comp_comparisonLeft
    {A I B F : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (hF : Stacks.SheafOfModules.IsKFlat X.O F) (s : F ⟶ (sheafHomComplex X B I).obj) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
        (DerivedCategory.Q.obj A)).map (DerivedCategory.Q.map (uncurryMap X s)) ≫
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A I hA).hom =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparison A
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj F).obj B) hA
          (Stacks.SheafOfModules.kFlat_tensorComplex X.O hF hB)).hom ≫
        DerivedCategory.Q.map
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map (uncurryMap X s)) := by
  have h := (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft_naturality
    (𝟙 A) (uncurryMap X s) hA hA
  simp only [CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp] at h
  rw [h, (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft_eq_comparison
    A _ hA (Stacks.SheafOfModules.kFlat_tensorComplex X.O hF hB)]
  rfl

/-- **The associator on K-flat complexes, through the one-sided comparisons**: the left
comparison at `(A, F)` followed by the right comparison at `(A ⊗ F, B)` and the associator of
total tensor complexes is the associator of `⊗^L` followed by the comparisons at `(F, B)` and
`(A, F ⊗ B)`. -/
theorem comparisonLeft_comparisonRight_tensorComplexAssociator
    {A F B : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hF : Stacks.SheafOfModules.IsKFlat X.O F)
    (hB : Stacks.SheafOfModules.IsKFlat X.O B) :
    ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A F hA).hom).app
          (DerivedCategory.Q.obj B) ≫
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight
          (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).obj F) B hB).hom ≫
        DerivedCategory.Q.map
          (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator A F B).hom =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).associatorGeneral
          (DerivedCategory.Q.obj A) (DerivedCategory.Q.obj F) (DerivedCategory.Q.obj B)).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj (DerivedCategory.Q.obj A)).map
          ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight F B hB).hom ≫
          ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparison A
            (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj F).obj B) hA
            (Stacks.SheafOfModules.kFlat_tensorComplex X.O hF hB)).hom := by
  have hT := Stacks.SheafOfModules.kFlat_tensorComplex X.O hA hF
  have hFB := Stacks.SheafOfModules.kFlat_tensorComplex X.O hF hB
  have f3a := (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft_eq_comparison
    A F hA hF
  have f3b := (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight_eq_comparison
    _ B hT hB
  have f3c := (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonRight_eq_comparison
    F B hF hB
  have f4 :=
    (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparison_tensorComplexAssociator
    hA hF hB
  rw [f3a, f3b, f4, f3c]

/-- The associator of total tensor complexes followed by `A ⊗ s♭` and a quasi-isomorphism
`q`, read in `D(O)` after `Q(q)⁻¹`. -/
theorem Q_map_tensorComplexAssociator_comp_uncurryMap
    {A I B F J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    (s : F ⟶ (sheafHomComplex X B I).obj) (q : tensorTotal X A I ⟶ J)
    [IsIso (DerivedCategory.Q.map q)] :
    DerivedCategory.Q.map
      ((Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator A F B).hom ≫
        ((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map (uncurryMap X s) ≫
        (tensorTotalIsoTensorComplex X A I).inv ≫ q) ≫ inv (DerivedCategory.Q.map q) ≫
      DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A I).hom =
    DerivedCategory.Q.map
        (Stacks.SheafOfModules.DerivedTensorProduct.tensorComplexAssociator A F B).hom ≫
      DerivedCategory.Q.map
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map (uncurryMap X s)) := by
  have e1 := (DerivedCategory.Q.map_comp
      (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map (uncurryMap X s))
      ((tensorTotalIsoTensorComplex X A I).inv ≫ q)).trans
    (congrArg (fun z => DerivedCategory.Q.map
        (((Stacks.SheafOfModules.Tensor.tensorComplex X.O).obj A).map (uncurryMap X s)) ≫ z)
      (DerivedCategory.Q.map_comp (tensorTotalIsoTensorComplex X A I).inv q))
  rw [CategoryTheory.Functor.map_comp, e1]
  simp only [Category.assoc, IsIso.hom_inv_id_assoc, Iso.inv_hom_id_map, Category.comp_id]

/-- **The identification of the diagonal after precomposing with a K-flat resolution of the
internal Hom.** On models `A` (K-flat) for `P`, `B` (K-flat) for `M`, `I` (K-injective) for
`K`, and `s : F ⟶ SheafHom(B, I)` with `F` K-flat, the transpose of `(P ⊗^𝐋 Q(s)) ≫ δ` is the
associator followed by `P ⊗^𝐋 -` of the transpose of `Q(s)`. -/
theorem derivedCurryHomEquiv_whiskerLeft_derivedTensorHomDiagonal_of_models
    {P K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A I B F J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [J.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (hF : Stacks.SheafOfModules.IsKFlat X.O F)
    (eA : DerivedCategory.Q.obj A ≅ P) (eI : DerivedCategory.Q.obj I ≅ K)
    (eB : DerivedCategory.Q.obj B ≅ M) (s : F ⟶ (sheafHomComplex X B I).obj)
    (q : tensorTotal X A I ⟶ J) (hq : IsIso (DerivedCategory.Q.map q))
    (σ : DerivedCategory.Q.obj F ⟶ ((derivedSheafHomBifunctor X).obj (op M)).obj K)
    (hσ : σ = DerivedCategory.Q.map s ≫
      (derivedSheafHomObjectsModelIso X eB eI ≪≫ derivedSheafHomComparison X B I).inv) :
    derivedCurryHomEquiv X _ M _
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).map σ ≫
          derivedTensorHomDiagonal X P K M) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).associatorGeneral P
          (DerivedCategory.Q.obj F) M).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).map
          (derivedCurryHomEquiv X (DerivedCategory.Q.obj F) M K σ) := by
  subst hσ
  have hδ := derivedTensorHomDiagonal_eq_ofModels X P K M hA eA eI eB q hq
  have hδ' : derivedTensorHomDiagonal X P K M =
      (derivedTensorHomSourceIsoOfModels X hA eA eI eB).hom ≫
        DerivedCategory.Q.map (derivedTensorHomMapOfModels X (N := B) q) ≫
          (derivedTensorHomTargetIsoOfModels X hA eA eI eB q hq).inv := by
    rw [← hδ]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  rw [hδ', ← Category.assoc, whiskerLeft_comp_derivedTensorHomSourceIsoOfModels_hom,
    derivedTensorHomTargetIsoOfModels_inv_eq, derivedCurryHomEquiv_Q_map_comp_inv X hF hB eB eI s]
  have harg : (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map eA.inv).app
          (DerivedCategory.Q.obj F) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A F hA).hom ≫
          DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A F).inv ≫
            DerivedCategory.Q.map (tensorTotalMap X (𝟙 A) s)) ≫
        DerivedCategory.Q.map (derivedTensorHomMapOfModels X (N := B) q) ≫
          (derivedSheafHomComparison X B J).inv ≫
            (((derivedSheafHomBifunctor X).map eB.inv.op).app (DerivedCategory.Q.obj J) ≫
              ((derivedSheafHomBifunctor X).obj (op M)).map
                (inv (DerivedCategory.Q.map q) ≫
                  (derivedTensorObjectsIsoOfModels X hA eA eI).inv)) =
      (((Stacks.SheafOfModules.derivedTensorProductFunctor X).map eA.inv).app
          (DerivedCategory.Q.obj F) ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A F hA).hom) ≫
        (DerivedCategory.Q.map ((tensorTotalIsoTensorComplex X A F).inv ≫
            tensorTotalMap X (𝟙 A) s ≫ tensorHomInterchange X A I B ≫ homMap X (𝟙 B) q) ≫
          (derivedSheafHomComparison X B J).inv) ≫
            (((derivedSheafHomBifunctor X).map eB.inv.op).app (DerivedCategory.Q.obj J) ≫
              ((derivedSheafHomBifunctor X).obj (op M)).map
                (inv (DerivedCategory.Q.map q) ≫
                  (derivedTensorObjectsIsoOfModels X hA eA eI).inv)) := by
    simp only [derivedTensorHomMapOfModels, CategoryTheory.Functor.map_comp, Category.assoc]
  rw [harg, derivedCurryHomEquiv_naturality]
  have hT := Stacks.SheafOfModules.kFlat_tensorComplex X.O hA hF
  have hTB := Stacks.SheafOfModules.kFlat_tensorComplex X.O hT hB
  rw [derivedCurryHomEquiv_model X _ B J hT hB hTB _ _
    (homologyMap_globalHomologyClass_uncurryMap X _), uncurryMap_tensorHomInterchange]
  have f5 := tensorObj_map_Q_map_uncurryMap_comp_comparisonLeft X hA hB hF s
  have hobj : (derivedTensorObjectsIsoOfModels X hA eA eI).inv =
      DerivedCategory.Q.map (tensorTotalIsoTensorComplex X A I).hom ≫
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).comparisonLeft A I hA).inv ≫
          ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj
            (DerivedCategory.Q.obj A)).map eI.hom ≫
            ((Stacks.SheafOfModules.derivedTensorProductFunctor X).map eA.hom).app K := by
    dsimp only [derivedTensorObjectsIsoOfModels, Iso.trans_inv, CategoryTheory.Functor.mapIso_inv,
      Iso.app_inv, Iso.symm_inv, CategoryTheory.Functor.mapIso_hom]
    simp only [Category.assoc]
  have h4 := comparisonLeft_comparisonRight_tensorComplexAssociator X hA hF hB
  have hbig := Q_map_tensorComplexAssociator_comp_uncurryMap X s q
  rw [hobj]
  exact diagonal_models_chase _ eA eB.inv eI.hom _ _ _ _ _ _ _
    (DerivedCategory.Q.map (uncurryMap X s))
    _ _ _ _ _ _ hbig h4 f5
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).associatorGeneral_naturality_right
      _ _ _)
    ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).associatorGeneral_naturality_left
      _ _ _)


/-- **The transpose of the diagonal of Stacks 0BYS on models**: for models `A` (K-flat) of `P`,
`B` (K-flat) of `M`, `I` (K-injective) of `K` and a quasi-isomorphism `s : F ⟶ SheafHom(B, I)`
from a K-flat `F`, the transpose of the diagonal is the associator followed by `P ⊗^𝐋 -` of the
evaluation morphism. -/
theorem derivedCurryHomEquiv_derivedTensorHomDiagonal_of_models
    {P K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    {A I B F J : CochainComplex (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    [I.IsKInjective] [J.IsKInjective]
    (hA : Stacks.SheafOfModules.IsKFlat X.O A) (hB : Stacks.SheafOfModules.IsKFlat X.O B)
    (hF : Stacks.SheafOfModules.IsKFlat X.O F)
    (eA : DerivedCategory.Q.obj A ≅ P) (eI : DerivedCategory.Q.obj I ≅ K)
    (eB : DerivedCategory.Q.obj B ≅ M) (s : F ⟶ (sheafHomComplex X B I).obj)
    [IsIso (DerivedCategory.Q.map s)]
    (q : tensorTotal X A I ⟶ J) (hq : IsIso (DerivedCategory.Q.map q)) :
    derivedCurryHomEquiv X _ M _ (derivedTensorHomDiagonal X P K M) =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).associatorGeneral P
          (((derivedSheafHomBifunctor X).obj (op M)).obj K) M).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).map
          (derivedSheafHomCounit X M K) := by
  have key : ∀ (σ : DerivedCategory.Q.obj F ⟶ ((derivedSheafHomBifunctor X).obj (op M)).obj K),
      [IsIso σ] → σ = DerivedCategory.Q.map s ≫
        (derivedSheafHomObjectsModelIso X eB eI ≪≫ derivedSheafHomComparison X B I).inv →
      derivedCurryHomEquiv X _ M _ (derivedTensorHomDiagonal X P K M) =
        ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).associatorGeneral P
            (((derivedSheafHomBifunctor X).obj (op M)).obj K) M).hom ≫
          ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).map
            (derivedSheafHomCounit X M K) := by
    intro σ _ hσ
    have h := derivedCurryHomEquiv_whiskerLeft_derivedTensorHomDiagonal_of_models X hA hB hF eA eI
      eB s q hq σ hσ
    exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
      (derivedCurryHomEquiv_eq_of_whiskerLeft X σ (derivedTensorHomDiagonal X P K M)
        (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq h) (by heq_congr))))))
      (by heq_congr)))
  exact key _ rfl


/-- A morphism `P ⊗^𝐋 RSheafHom(M, K) ⟶ RSheafHom(M, P ⊗^𝐋 K)` whose transpose under Stacks 08J8
is the associator followed by the evaluation morphism is the adjunction-theoretic diagonal. -/
theorem eq_leftTensorHomDiagonal_of_derivedCurryHomEquiv
    {P K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))}
    (δ : ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).obj
        (((derivedSheafHomBifunctor X).obj (op M)).obj K) ⟶
      ((derivedSheafHomBifunctor X).obj (op M)).obj
        (((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).obj K))
    (h : derivedCurryHomEquiv X _ M _ δ =
      ((Stacks.SheafOfModules.canonicalDerivedTensorProduct X).associatorGeneral P
          (((derivedSheafHomBifunctor X).obj (op M)).obj K) M).hom ≫
        ((Stacks.SheafOfModules.derivedTensorProductFunctor X).obj P).map
          (derivedSheafHomCounit X M K)) :
    δ = CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal
        (Stacks.SheafOfModules.derivedTensorProductFunctor X) (derivedSheafHomBifunctor X)
        (derivedTensorSheafHomAdjunction X)
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).associatorGeneral P M K := by
  rw [← (derivedCurryHomEquiv X _ M _).symm_apply_apply δ, h,
    CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal,
    derivedTensorSheafHomAdjunction_homEquiv_apply, derivedTensorSheafHomAdjunction_counit_app_eq]

/-- **The diagonal of Stacks 0BYS is the adjunction-theoretic tensor–Hom diagonal.** For objects
`P`, `K`, `M` of `D(O)` the diagonal morphism
`P ⊗^𝐋_O RSheafHom(M, K) ⟶ RSheafHom(M, P ⊗^𝐋_O K)` built from complex models is the morphism
corresponding under the adjunction of Stacks 08J8 to the associator of Stacks 0FPT followed by
`P ⊗^𝐋 -` of the evaluation morphism. -/
theorem derivedTensorHomDiagonal_eq_leftTensorHomDiagonal
    (P K M : DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))) :
    derivedTensorHomDiagonal X P K M =
      CategoryTheory.PullbackInternalHom.leftTensorHomDiagonal
        (Stacks.SheafOfModules.derivedTensorProductFunctor X) (derivedSheafHomBifunctor X)
        (derivedTensorSheafHomAdjunction X)
        (Stacks.SheafOfModules.canonicalDerivedTensorProduct X).associatorGeneral P M K := by
  obtain ⟨F, s, hF, hs⟩ := Stacks.SheafOfModules.exists_kFlat_quasiIso X
    (sheafHomComplex X (kFlatModel X M) (kInjectiveModel X K)).obj
  have hQs : IsIso (DerivedCategory.Q.map s) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 hs
  have hq : IsIso (DerivedCategory.Q.map ((kInjectiveAugmentation X).app
      (tensorTotal X (kFlatModel X P) (kInjectiveModel X K)))) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ _).2 inferInstance
  have h' := derivedCurryHomEquiv_derivedTensorHomDiagonal_of_models X
    (isKFlat_kFlatModel X P) (isKFlat_kFlatModel X M) hF (kFlatModelIso X P)
    (kInjectiveModelIso X K) (kFlatModelIso X M) s
    ((kInjectiveAugmentation X).app (tensorTotal X (kFlatModel X P) (kInjectiveModel X K))) hq
  exact eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq
    (eq_leftTensorHomDiagonal_of_derivedCurryHomEquiv X (derivedTensorHomDiagonal X P K M)
      (eq_of_heq (HEq.trans (by heq_congr) (HEq.trans (heq_of_eq h') (by heq_congr))))))
    (by heq_congr)))

end AlgebraicGeometry.RingedSite

end
