module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompIso

/-!
# An exact functor and the identification of `H ⁿ(Φ(A[-n]))` with `Φ A`

Let `F : C₁ ⥤ C₂` be an exact additive functor between abelian categories with derived
categories, and write `Φ` for `CategoryTheory.Functor.mapDerivedCategory`, the induced functor on
the unbounded derived categories.  For an object `A` of `C₁` there are two ways of identifying the
degree-`n` cohomology of `Φ(A[-n])` with `F A`:

* move `Φ` past the single functor by Mathlib's
  `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, which reads `Φ(A[-n])` as `(F A)[-n]`,
  and then compute the cohomology of a single complex by
  `DerivedCategory.singleFunctorCompHomologyFunctorIso`;
* move `Φ` past the cohomology functor by
  `CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, which reads `H ⁿ(Φ(A[-n]))` as
  `F(H ⁿ(A[-n]))`, and then apply `F` to
  `DerivedCategory.singleFunctorCompHomologyFunctorIso`.

**They agree**, and that is what this file proves.  Neither this library nor Mathlib asserted it:
the library carries four copies of "an exact functor commutes with `H ⁿ`", identified with one
another in `StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyCompIso`, and
Mathlib carries the single-functor comparison together with its degree-`0` factorisation
`CategoryTheory.Functor.mapDerivedCategoryFactors_inv_app_mapDerivedCategorySingleFunctor_hom_app`;
nothing related the two families.

The statement is what a diagram chase needs in order to carry a morphism out of a bottom
cohomology object across an exact functor, which is why it is stated here rather than beside the
comparisons it is about: `Stacks.BottomHomologyEdge.mapDerivedCategory_edge` is its one consumer.

## Main results

* `homologyMap_singleMapHomologicalComplex`: **the statement at the level of complexes.**  The
  degreewise comparison `HomologicalComplex.singleMapHomologicalComplex` followed by
  `HomologicalComplex.singleObjHomologySelfIso` is `CategoryTheory.ShortComplex.mapHomologyIso`
  followed by `F` applied to `HomologicalComplex.singleObjHomologySelfIso`.
* `homologyMap_mapDerivedCategorySingleFunctor`: **the statement on the derived category**, which
  is the form a consumer uses.

## Implementation notes

The complex-level statement is checked on the cycles: `HomologicalComplex.homologyπ` is an
epimorphism, and both sides composed with it are the inclusion of the cycles followed by `F`
applied to `HomologicalComplex.singleObjXSelf`.  For the left-hand side that is the naturality of
`homologyπ` together with `HomologicalComplex.singleMapHomologicalComplex_hom_app_self`, which is
where the whole content sits.  For the right-hand side,
`CategoryTheory.ShortComplex.mapHomologyIso` is read through the left homology datum
`CategoryTheory.ShortComplex.LeftHomologyData.ofZeros` of the short complex computing `H ⁿ` of a
single complex — both of whose maps are zero, a single complex having no differentials — in which
that comparison is carried by an identity.

The passage to the derived category is then the naturality of
`DerivedCategory.homologyFunctorFactors` at the degreewise comparison, and nothing else: at an
object both `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` and
`DerivedCategory.singleFunctorCompHomologyFunctorIso` collapse to one canonical factorisation
through `DerivedCategory.Q` followed by one complex-level comparison, which is what
`mapDerivedCategorySingleFunctor_hom_app` and `singleFunctorCompHomologyFunctorIso_hom_app`
record.

**Why the two rearrangements are stated at a variable category.**  The objects along these
composites are definitionally equal in several spellings each — `K.homology n`,
`(K.sc n).homology` and `(HomologicalComplex.homologyFunctor C (.up ℤ) n).obj K` are one object
written three ways — and in a goal containing one, `rw` reports that the target is not
type-correct and finds nothing to do.  `comp_map_cancel` and `assemble` are therefore stated at
variable categories, where every rewrite is immediate, and applied with `exact`, which works up
to default transparency.  This is the device of
`Stacks.Perfect.AbelianSupportedEndoModelFactors.assoc_of_head`, used there for the same reason.
For the same reason several short steps are written as `Eq.trans` of `congrArg` rather than as
rewrites.

**No declaration here carries a `@[stacks ...]` attribute.**  This is a coherence between two
canonical isomorphisms of Mathlib's and this library's making; it states no result of the source.
-/

@[expose] public noncomputable section

universe w₁ w₂ v₁ v₂ u₁ u₂ w v u

open CategoryTheory Category Limits

namespace Stacks.ExactFunctorSingleHomology

variable {C₁ : Type u₁} [Category.{v₁} C₁] [Abelian C₁]
  {C₂ : Type u₂} [Category.{v₂} C₂] [Abelian C₂]
  (F : C₁ ⥤ C₂) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Cancelling a composite against a functor's action, at abstract categories: the head of the
composite is shortened by `hq` and the two images are collapsed by `hr`.  Stated abstractly and
applied with `exact` because the objects along the composites below are definitionally equal in
two spellings each, which `rw` refuses to identify. -/
private lemma comp_map_cancel {D₁ D₂ : Type*} [Category* D₁] [Category* D₂] (G : D₁ ⥤ D₂)
    {x y : D₂} {u v w : D₁} (p : x ⟶ y) (a : y ⟶ G.obj u) (q : x ⟶ G.obj u)
    (b : u ⟶ v) (t : v ⟶ w) (r : u ⟶ w)
    (hq : p ≫ a = q) (hr : b ≫ t = r) :
    p ≫ (a ≫ G.map b) ≫ G.map t = q ≫ G.map r := by
  rw [Category.assoc, ← Category.assoc p a, hq, ← G.map_comp, hr]

/-! ### The comparison at the level of complexes -/

section Complexes

variable {ι : Type*} [DecidableEq ι] (c : ComplexShape ι) (j : ι) (A : C₁)

open HomologicalComplex

/-- The middle object as a left homology datum of the short complex computing `Hʲ` of `A` placed
in degree `j`: both maps of that short complex are zero, the single complex having no
differentials. -/
private def singleData : (((single C₁ c j).obj A).sc j).LeftHomologyData :=
  ShortComplex.LeftHomologyData.ofZeros _ rfl rfl

/-- `singleData` identifies the homology with the degree-`j` object. -/
private lemma singleData_homologyIso_hom :
    ((single C₁ c j).obj A).homologyπ j ≫ (singleData c j A).homologyIso.hom =
      ((single C₁ c j).obj A).iCycles j :=
  (singleData c j A).homologyπ_comp_homologyIso_hom.trans
    (singleData c j A).cyclesIso_hom_comp_i

/-- The identification of `Hʲ` of `A` placed in degree `j` with `A` factors through
`singleData`. -/
private lemma singleData_homologyIso_inv_comp :
    (singleData c j A).homologyIso.inv ≫ (singleObjHomologySelfIso c j A).hom =
      (singleObjXSelf c j A).hom := by
  have key : ((single C₁ c j).obj A).homologyπ j ≫
        ((singleData c j A).homologyIso.hom ≫ (singleObjXSelf c j A).hom) =
      ((single C₁ c j).obj A).homologyπ j ≫ (singleObjHomologySelfIso c j A).hom :=
    Eq.trans (Category.assoc _ _ _).symm
      (Eq.trans
        (congrArg (fun z => z ≫ (singleObjXSelf c j A).hom)
          (singleData_homologyIso_hom c j A))
        (Eq.trans (homologyπ_singleObjHomologySelfIso_hom c j A)
          (singleObjCyclesSelfIso_hom c j A)).symm)
  have h2 := (cancel_epi (((single C₁ c j).obj A).homologyπ j)).1 key
  exact Eq.trans
    (congrArg (fun z => (singleData c j A).homologyIso.inv ≫ z) h2.symm)
    (Iso.inv_hom_id_assoc _ _)

/-- The image of `singleData` under `F` identifies the homology with the degree-`j` object. -/
private lemma singleDataMap_homologyIso_hom :
    ((F.mapHomologicalComplex c).obj ((single C₁ c j).obj A)).homologyπ j ≫
        ((singleData c j A).map F).homologyIso.hom =
      ((F.mapHomologicalComplex c).obj ((single C₁ c j).obj A)).iCycles j :=
  ((singleData c j A).map F).homologyπ_comp_homologyIso_hom.trans
    ((singleData c j A).map F).cyclesIso_hom_comp_i

omit [PreservesFiniteLimits F] [PreservesFiniteColimits F] in
/-- The left-hand identification, read on the cycles. -/
private lemma homologyπ_lhs :
    ((F.mapHomologicalComplex c).obj ((single C₁ c j).obj A)).homologyπ j ≫
        homologyMap ((singleMapHomologicalComplex F c j).hom.app A) j ≫
          (singleObjHomologySelfIso c j (F.obj A)).hom =
      ((F.mapHomologicalComplex c).obj ((single C₁ c j).obj A)).iCycles j ≫
        F.map (singleObjXSelf c j A).hom := by
  dsimp only [Functor.comp_obj]
  rw [homologyπ_naturality_assoc, homologyπ_singleObjHomologySelfIso_hom,
    singleObjCyclesSelfIso_hom, cyclesMap_i_assoc, singleMapHomologicalComplex_hom_app_self,
    Category.assoc, Iso.inv_hom_id, Category.comp_id]

/-- The right-hand identification, read on the cycles. -/
private lemma homologyπ_rhs :
    ((F.mapHomologicalComplex c).obj ((single C₁ c j).obj A)).homologyπ j ≫
        ((((single C₁ c j).obj A).sc j).mapHomologyIso F).hom ≫
          F.map (singleObjHomologySelfIso c j A).hom =
      ((F.mapHomologicalComplex c).obj ((single C₁ c j).obj A)).iCycles j ≫
        F.map (singleObjXSelf c j A).hom := by
  have hmap : ((((single C₁ c j).obj A).sc j).mapHomologyIso F).hom =
      ((singleData c j A).map F).homologyIso.hom ≫
        F.map (singleData c j A).homologyIso.inv := by
    rw [(singleData c j A).mapHomologyIso_eq F]
    rfl
  rw [hmap]
  exact comp_map_cancel F _ _ _ _ _ _ (singleDataMap_homologyIso_hom F c j A)
    (singleData_homologyIso_inv_comp c j A)

/-- **The two identifications of `Hʲ(F(A[j]))` with `F A` agree, at the level of complexes.**
On the left, `HomologicalComplex.singleMapHomologicalComplex` moves `F` past `single` and then
`HomologicalComplex.singleObjHomologySelfIso` computes the homology; on the right,
`CategoryTheory.ShortComplex.mapHomologyIso` moves `F` past the homology and then `F` is applied
to `HomologicalComplex.singleObjHomologySelfIso`. -/
theorem homologyMap_singleMapHomologicalComplex :
    homologyMap ((singleMapHomologicalComplex F c j).hom.app A) j ≫
        (singleObjHomologySelfIso c j (F.obj A)).hom =
      ((((single C₁ c j).obj A).sc j).mapHomologyIso F).hom ≫
        F.map (singleObjHomologySelfIso c j A).hom :=
  (cancel_epi _).1 ((homologyπ_lhs F c j A).trans (homologyπ_rhs F c j A).symm)

end Complexes

/-! ### The identification of `singleFunctorCompHomologyFunctorIso` at a complex -/

section SingleHomology

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- **`DerivedCategory.singleFunctorCompHomologyFunctorIso` at an object**: the degree-`n`
cohomology of `A` placed in degree `n` is computed at the level of complexes by
`DerivedCategory.homologyFunctorFactors` followed by
`HomologicalComplex.singleObjHomologySelfIso`. -/
private lemma singleFunctorCompHomologyFunctorIso_hom_app (n : ℤ) (A : C) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso C n).hom.app A =
      (DerivedCategory.homologyFunctorFactors C n).hom.app
          ((HomologicalComplex.single C (ComplexShape.up ℤ) n).obj A) ≫
        (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n A).hom := by
  simp only [Functor.comp_obj, Functor.id_obj, DerivedCategory.singleFunctorCompHomologyFunctorIso,
    SingleFunctors.evaluation_obj, SingleFunctors.postcomp_functor,
    DerivedCategory.singleFunctorsPostcompQIso, Functor.mapIso_refl, Functor.isoWhiskerRight_refl,
    Iso.refl_trans, Iso.trans_hom, Functor.isoWhiskerLeft_hom, NatTrans.comp_app,
    Functor.associator_hom_app, Functor.whiskerLeft_app,
    HomologicalComplex.homologyFunctorSingleIso_hom_app, DerivedCategory.Q_obj_single_obj]
  exact Category.id_comp _

end SingleHomology

/-! ### The comparison on the derived category -/

section Derived

variable [HasDerivedCategory.{w₁} C₁] [HasDerivedCategory.{w₂} C₂]

/-- **Mathlib's `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` at an object**: the
canonical factorisation of the degreewise action of `F` through `DerivedCategory.Q`, followed by
the localisation of `HomologicalComplex.singleMapHomologicalComplex`. -/
private lemma mapDerivedCategorySingleFunctor_hom_app (n : ℤ) (A : C₁) :
    (F.mapDerivedCategorySingleFunctor n).hom.app A =
      F.mapDerivedCategoryFactors.hom.app
          ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℤ) n).hom.app A) := by
  simp only [Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ, Functor.isoWhiskerRight_refl,
    Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, DerivedCategory.Q_obj_single_obj, Functor.whiskerRight_app,
    NatTrans.id_app, comp_id, id_comp]
  exact Category.id_comp _

/-- `CategoryTheory.Functor.mapDerivedCategoryHomologyIso` at `A` placed in degree `n`. -/
private lemma mapDerivedCategoryHomologyIso_hom_app_single (n : ℤ) (A : C₁) :
    (F.mapDerivedCategoryHomologyIso n).hom.app ((DerivedCategory.singleFunctor C₁ n).obj A) =
      (DerivedCategory.homologyFunctor C₂ n).map
          (F.mapDerivedCategoryFactors.hom.app
            ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A)) ≫
        (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A)) ≫
          ((((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A).sc n).mapHomologyIso
              F).hom ≫
            F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app
              ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A)) := by
  rw [F.mapDerivedCategoryHomologyIso_eq_mapDerivedCategoryHomologyFunctorIso n]
  exact F.mapDerivedCategoryHomologyFunctorIso_hom_app_Q n
    ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A)

/-- Pasting the two squares, at abstract categories: `h1` rewrites the tail of the left-hand
composite and `h2` cancels the two factorisations of the cohomology functor against each other.
Stated abstractly and applied with `exact` because the objects along the composites are
definitionally equal in two spellings each, which `rw` refuses to identify. -/
private lemma assemble {D₁ D : Type*} [Category* D₁] [Category* D] (G : D₁ ⥤ D)
    {x y z t₁ t₂ : D} {u v w : D₁}
    (p : x ⟶ y) (m : y ⟶ z) (k : z ⟶ t₁) (e : t₁ ⟶ G.obj w)
    (nn : y ⟶ t₂) (xx : t₂ ⟶ G.obj u) (i : u ⟶ v) (jj : v ⟶ u) (yy : u ⟶ w)
    (h1 : m ≫ k ≫ e = nn ≫ xx ≫ G.map yy) (h2 : i ≫ jj = 𝟙 u) :
    (p ≫ m) ≫ k ≫ e = (p ≫ nn ≫ xx ≫ G.map i) ≫ G.map (jj ≫ yy) := by
  rw [Category.assoc p m, h1]
  simp only [G.map_comp, Category.assoc]
  rw [← Category.assoc (G.map i), ← G.map_comp, h2, G.map_id, Category.id_comp]

omit [HasDerivedCategory C₁] in
/-- **The naturality square of `DerivedCategory.homologyFunctorFactors` at
`HomologicalComplex.singleMapHomologicalComplex`, pasted with the complex-level comparison.**
This is the content of the coherence below; what is left is formal. -/
private lemma homologyFunctorFactors_single (n : ℤ) (A : C₁) :
    (DerivedCategory.homologyFunctor C₂ n).map
          (DerivedCategory.Q.map ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℤ) n).hom.app A)) ≫
        (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
            ((HomologicalComplex.single C₂ (ComplexShape.up ℤ) n).obj (F.obj A)) ≫
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n (F.obj A)).hom =
      (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
            ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A)) ≫
        ((((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A).sc n).mapHomologyIso
            F).hom ≫
          F.map (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n A).hom :=
  Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg
        (fun t => t ≫
          (HomologicalComplex.singleObjHomologySelfIso (ComplexShape.up ℤ) n (F.obj A)).hom)
        ((DerivedCategory.homologyFunctorFactors C₂ n).hom.naturality
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).hom.app A)))
      (Eq.trans (Category.assoc _ _ _)
        (congrArg
          (fun t => (DerivedCategory.homologyFunctorFactors C₂ n).hom.app
            ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              ((HomologicalComplex.single C₁ (ComplexShape.up ℤ) n).obj A)) ≫ t)
          (homologyMap_singleMapHomologicalComplex F (ComplexShape.up ℤ) n A))))

/-- **For an exact functor the two identifications of `H ⁿ(Φ(A[-n]))` with `Φ A` agree** — one
through Mathlib's `CategoryTheory.Functor.mapDerivedCategorySingleFunctor`, the other through
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` composed with
`DerivedCategory.singleFunctorCompHomologyFunctorIso`. -/
theorem homologyMap_mapDerivedCategorySingleFunctor (n : ℤ) (A : C₁) :
    (DerivedCategory.homologyFunctor C₂ n).map
          ((F.mapDerivedCategorySingleFunctor n).hom.app A) ≫
        (DerivedCategory.singleFunctorCompHomologyFunctorIso C₂ n).hom.app (F.obj A) =
      (F.mapDerivedCategoryHomologyIso n).hom.app
          ((DerivedCategory.singleFunctor C₁ n).obj A) ≫
        F.map ((DerivedCategory.singleFunctorCompHomologyFunctorIso C₁ n).hom.app A) := by
  rw [mapDerivedCategorySingleFunctor_hom_app, Functor.map_comp,
    singleFunctorCompHomologyFunctorIso_hom_app n (F.obj A),
    mapDerivedCategoryHomologyIso_hom_app_single,
    singleFunctorCompHomologyFunctorIso_hom_app n A]
  exact assemble F _ _ _ _ _ _ _ _ _ (homologyFunctorFactors_single F n A)
    (Iso.inv_hom_id_app _ _)

end Derived

end Stacks.ExactFunctorSingleHomology

end
