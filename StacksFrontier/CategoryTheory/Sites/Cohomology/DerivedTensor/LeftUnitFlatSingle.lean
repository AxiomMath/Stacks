module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.MonoidalSheafTensorBraidingUnitor
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryComparisons
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ConstraintNaturality
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.FlatSingleTensor
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.IdealActionVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.TorAmplitude.FlatRepresentative
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.SelfExtOnACollectionOfOpens
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedCategory.DerivedRestrictionDictionaryCoherence

/-!
# The left unit constraint against the flat-single identification

Let `(C, 𝒪)` be a ringed site and `T` a derived tensor product on it.  The left unit constraint
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.leftUnitIso` is *defined* as the
commutativity constraint followed by the unit constraint on the right, and so passes through a
chosen K-flat model of the right factor.  The structure sheaf is flat, so `𝒪[0]` is K-flat and
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.flatSingleTensorIso` identifies
`𝒪[0] ⊗^L_𝒪 -` with the derived functor of `𝒪 ⊗_𝒪 -` directly, with no model; composing that
with the derived functor of the sheaf-level left unitor gives a second isomorphism
`𝒪[0] ⊗^L_𝒪 A ≅ A`.  This file makes both available as natural transformations and **proves
that they agree**.

## Main definitions

* `leftUnitTrans`: **the left unit constraint as a natural transformation** `𝒪[0] ⊗^L_𝒪 - ⟶ id`,
  the commutativity constraint at the unit followed by the unit constraint on the right.
* `flatSingleLeftUnitTrans`: the flat-single identification followed by the derived functor of
  the sheaf-level left unitor, as a natural transformation `𝒪[0] ⊗^L_𝒪 - ⟶ id`.
* `LeftUnitFlatSingleAgree`: the statement that the two agree.

## Main results

* `leftUnitFlatSingleAgree`: **`LeftUnitFlatSingleAgree` holds** — the left unit constraint of a
  derived tensor product is the flat-single identification followed by the derived functor of
  the sheaf-level left unitor.
* `leftUnitTrans_app`: the transformation's value at an object is `leftUnitIso` there, so the
  objectwise constraint is recovered from it.  This is where the chosen K-flat models disappear:
  it is `braidingIso_hom_eq` and `rightUnitIso_hom_eq` composed.
* `leftUnitTrans_app_Q`: **at the class of a K-flat complex the left unit constraint is the
  K-flat comparison followed by the Koszul flip and the unit law of total complexes**, with no
  model and with the two comparisons of the exchanged pair cancelled against each other.
* `flatSingleLeftUnitTrans_app_Q`: the matching description of the second transformation, which
  needs no K-flatness at all.
* `Stacks.DerivedTensor.RingedSite.tensorComplexFlipIso_totalSingleIso` and
  `Stacks.DerivedTensor.RingedSite.tensorComplexFlipIso_tensorComplexUnitIso`: **the Koszul flip
  exchanges the single-row collapse of total complexes with the single-column one**, which is
  the whole content of the agreement.

## Implementation notes

**How the agreement is proved.**  Both transformations are natural, `D(𝒪)` is a localization of
the complexes of `𝒪`-modules, and both are computed on the class of a complex:

* the left side by `leftUnitTrans_app_Q` — for a K-flat `L` it is `comparison 𝒪[0] L` followed
  by `Q` of `tensorComplexFlipIso 𝒪[0] L ≫ tensorComplexUnitIso L`;
* the right side by `flatSingleLeftUnitTrans_app_Q` — for *any* `L` it is `comparisonLeft 𝒪[0]
  L` followed by `Q` of `mapBifunctorSingleLeftNatIso 𝒪 |>.app L ≫ (degreewise
  unitSheafTensorNatIso) ≫ mapHomologicalComplexIdIso`.

The second of those is pure localization plumbing: `flatSingleTensorIso_hom_app_Q` and
`flatSingleLifting_hom_app_eq` for the first factor, and
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q` and
`Stacks.DerivedGlueing.mapDerivedCategoryIdIso_hom_app_Q` for the other two — both of those
isomorphisms are lifted along `DerivedCategory.Q` rather than along `Qh`, so
`CategoryTheory.Localization.liftNatTrans_app` applies to each directly — after which the two
adjacent pairs of `CategoryTheory.Functor.mapDerivedCategoryFactors` cancel.  Two syntactic
obstructions in that computation are removed here, each by `rfl`:
`flatSingleLifting_hom_app_eq` separates the three factors of the lifting datum's component,
and `lifting_iso_eq_mapDerivedCategoryFactors` identifies the lifting isomorphism that
`liftNatTrans_app` produces with `CategoryTheory.Functor.mapDerivedCategoryFactors`, the two
being the same isomorphism but not syntactically so.

Those two lemmas and `flatSingleLeftUnitTrans_eq` carry the flat unit's two
`CategoryTheory.Limits.PreservesFiniteLimits`/`CategoryTheory.Limits.PreservesFiniteColimits`
instances as binders of the section they live in, not as `letI` in their statements.  A `letI`
in a statement makes the statement a `let`-expression, and then the instance exists only inside
it: the equation cannot be stated — let alone rewritten with — in any ambient context, because
the instance that elaborates `CategoryTheory.Functor.mapDerivedCategoryFactors` on the
right-hand side is not in scope there.  Section binders are sound because both classes are
`Prop`-valued, so a binder is definitionally the specific instance
`preservesFiniteLimits_sheafTensorObj` that the type of `flatSingleLifting` bakes in, and all
three lemmas still hold by `rfl`.  `flatSingleLeftUnitTrans` keeps its own `letI` on purpose, so
that `LeftUnitFlatSingleAgree` carries no instance hypothesis; `leftUnitFlatSingleAgree`
discharges the binders by `letI` and proof irrelevance matches them to it.

Granted those two descriptions, `comparisonLeft 𝒪[0] L = comparison 𝒪[0] L` for K-flat `L` by
`comparisonLeft_eq_comparison`, so the agreement at a K-flat `L` is exactly the total-complex
identity `tensorComplexFlipIso_tensorComplexUnitIso`, and the passage from K-flat `L` to an
arbitrary object of `D(𝒪)` is the naturality of both transformations along
`AlgebraicGeometry.RingedSite.kFlatModelIso`, as in `rightUnitIso_hom_eq`.

**The total-complex identity.**  It is unit-free once the common degreewise unit law is
cancelled from both sides: it says that the Koszul flip exchanges the single-row collapse
`CochainComplex.KFlatBifunctor.totalSingleIso` with the single-column collapse
`HomologicalComplex.mapBifunctorSingleLeftIso`, which is
`tensorComplexFlipIso_totalSingleIso`.  Its proof is the naturality of the tensor braiding.
The degreewise description of `totalSingleIso` that it needs is
`CochainComplex.KFlatBifunctor.ι_totalSingleIso_hom_f`, with its single-column mirror
`HomologicalComplex.singleLeftι_singleLeftXIso_hom`.  Writing both sides at the summand of
bidegree `(0, n)`, the only one that does not vanish by
`HomologicalComplex.isZero_obj_obj_single_obj_X_left`, the identity becomes

`(β.hom.app (𝒪[0]_0)).app L^n ≫ (𝒪 ⊗ -)(L^n).map σ.hom =
  (β.map σ.hom).app L^n ≫ (β.hom.app 𝒪).app L^n`,

for `β` the tensor braiding `Stacks.SheafOfModules.Tensor.sheafTensorBraiding` and `σ` the
identification `HomologicalComplex.singleObjXSelf` of the degree-zero term of `𝒪[0]` with `𝒪`:
the two legs of `β`'s naturality square at `σ.hom`.  Nothing else is left — the Koszul sign does
not appear, since `ComplexShape.σ` of the shape `ComplexShape.up ℤ` is `(p * q).negOnePow` and
both summands touched here have an index equal to zero, and the common degreewise unit law
`Stacks.SheafOfModules.sheafTensorUnitNatIso` cancels because
`Stacks.SheafOfModules.unitSheafTensorNatIso` is *defined* as the braiding followed by it.

**Two spellings, and how each is crossed.**  `Stacks.SheafOfModules.Tensor.tensorComplex` is
`CategoryTheory.Functor.map₂HomologicalComplex` while the collapses are stated for
`HomologicalComplex.mapBifunctor`; a `rfl` bridge splitting `tensorComplexFlipIso` *at a
component* (`.hom.f m`) is rejected on those two spellings, but splitting the whole composite's
degree-`j` component at once is accepted, which is what `tensorComplexFlipIso_totalSingleIso`
does.  Separately, `HomologicalComplex.singleLeftι` is stated for `(CochainComplex.singleFunctor
_ 0).obj 𝒪` and `unitComplex` for `(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj 𝒪`;
these are definitionally equal at default transparency but *not* at reducible transparency, so
`exact` bridges them and `rw` and `simp only` do not — the step through
`singleLeftι_singleLeftXIso_hom` is therefore whiskered with `CategoryTheory.eq_whisker` as a
term instead of rewritten.  The same choice is forced three more times, at each associativity
step where a composite's source is spelled one way on the left and the other on the right: a
`calc` block cannot be used there at all, because the two `Quiver.Hom` types are not
syntactically equal and `Trans Eq Eq` is not found.

**The sheaf-level left unitor.**  The sheaf-level left unit law used here is the existing
`Stacks.SheafOfModules.unitSheafTensorNatIso`, which is *defined* as the tensor braiding
followed by the right unit law.  That it is the honest left unitor — the one with a description
on local sections — is
`SheafOfModules.sheafTensorBraiding_comp_tensorSheafUnitRightIso`, the braided coherence law
`β ≫ ρ = λ` for the re-seated monoidal structure.

## References

* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

namespace Stacks.DerivedTensor.RingedSite

variable (X : RingedSite.{u, u, u})
  [HasSheafify X.J AddCommGrpCat.{u}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [hTensorAdditive : (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).Additive]
  [∀ A, ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u} X.O).obj A).Additive]
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)]

/-! ## The Koszul flip exchanges the two collapses -/

/-- **The Koszul flip exchanges the single-row collapse with the single-column collapse.**  Both
sides are maps out of `Tot(𝒪[0] ⊗_𝒪 L)`, so both are determined by their restriction to each
summand, and all summands of bidegree `(i, j)` with `i ≠ 0` vanish by
`HomologicalComplex.isZero_obj_obj_single_obj_X_left`.  At the summand of bidegree `(0, n)` the
left side is the braiding at the degree-zero term of `𝒪[0]` followed by the comparison
`CochainComplex.KFlatBifunctor.ι_totalSingleIso_hom_f`, and the right side is
`HomologicalComplex.singleLeftι_singleLeftXIso_hom` followed by the braiding at `𝒪`: the two
legs of the naturality square of the tensor braiding at
`HomologicalComplex.singleObjXSelf`.  No Koszul sign appears, since `ComplexShape.σ` of
`ComplexShape.up ℤ` is `(p * q).negOnePow` and both summands touched carry an index `0`. -/
lemma tensorComplexFlipIso_totalSingleIso (L : CochainComplex (Modules X.O) ℤ) :
    (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O (unitComplex X) L).hom ≫
        (CochainComplex.KFlatBifunctor.totalSingleIso
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O) L
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom =
      (HomologicalComplex.mapBifunctorSingleLeftNatIso
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app L ≫
        ((NatIso.mapHomologicalComplex
            ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).app
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
            (ComplexShape.up ℤ)).app L).hom := by
  apply HomologicalComplex.hom_ext
  intro n
  apply HomologicalComplex.mapBifunctor.hom_ext
  intro i j hij
  by_cases hi : i = 0
  · subst hi
    obtain rfl : j = n := by simpa using hij
    -- `Stacks.SheafOfModules.Tensor.tensorComplexFlipIso` is built from `map₂HomologicalComplex`
    -- and the collapses from `mapBifunctor`; the two spellings are separated once here, at the
    -- level of the degree-`j` component of the whole composite, rather than once per factor.
    have hdecomp : ((Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O (unitComplex X) L).hom ≫
          (CochainComplex.KFlatBifunctor.totalSingleIso
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) L
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom).f j =
        ((HomologicalComplex.mapBifunctorNatIso (unitComplex X) L (ComplexShape.up ℤ)
              (Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O)).hom.f j ≫
            (HomologicalComplex.mapBifunctorFlipIso L (unitComplex X)
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
              (ComplexShape.up ℤ)).hom.f j) ≫
          (CochainComplex.KFlatBifunctor.totalSingleIso
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O) L
            (_root_.SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.f j := rfl
    have hright : (((HomologicalComplex.mapBifunctorSingleLeftNatIso
              (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
              (_root_.SheafOfModules.unit
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app L) ≫
            ((NatIso.mapHomologicalComplex
              ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).app
                (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              (ComplexShape.up ℤ)).app L).hom).f j =
        (HomologicalComplex.singleLeftXIso (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) L j).hom ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.app
            (_root_.SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app (L.X j) := rfl
    -- `singleLeftι` is stated for `(CochainComplex.singleFunctor _ 0).obj 𝒪` and `unitComplex`
    -- for `(HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj 𝒪`; those are equal at
    -- default transparency but not at reducible, so the step is whiskered as a term rather
    -- than rewritten.
    have hRval : HomologicalComplex.ιMapBifunctor (unitComplex X) L
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
            (ComplexShape.up ℤ) 0 j j hij ≫
          (HomologicalComplex.singleLeftXIso (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) L j).hom ≫
            ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.app
              (_root_.SheafOfModules.unit
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app (L.X j) =
        ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.app ((unitComplex X).X 0)).app
          (L.X j) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj (L.X j)).map
            (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
              (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom := by
      rw [← Category.assoc]
      exact (HomologicalComplex.singleLeftι_singleLeftXIso_hom
            (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) L j =≫
          ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.app
            (_root_.SheafOfModules.unit
              (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).app (L.X j)).trans
        (NatTrans.congr_app ((Stacks.SheafOfModules.Tensor.sheafTensorBraiding X.O).hom.naturality
          (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom) (L.X j))
    rw [hdecomp, hright, Category.assoc,
      HomologicalComplex.ι_mapBifunctorNatIso_hom_assoc,
      HomologicalComplex.ι_mapBifunctorFlipIso_hom_assoc,
      show (ComplexShape.up ℤ).σ (ComplexShape.up ℤ) (ComplexShape.up ℤ) j 0 = 1 by simp,
      one_smul, CochainComplex.KFlatBifunctor.ι_totalSingleIso_hom_f]
    exact hRval.symm
  · exact (HomologicalComplex.isZero_obj_obj_single_obj_X_left
      (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) L i j hi).eq_of_src
        _ _

/-- **The total-complex identity behind `LeftUnitFlatSingleAgree`:** the Koszul flip followed by
the unit law of total complexes is the single-column collapse followed by the degreewise
sheaf-level left unit law.  The degreewise right unit law is common to both sides — the left
unit law `Stacks.SheafOfModules.unitSheafTensorNatIso` is *defined* as the braiding followed by
it — so this is `tensorComplexFlipIso_totalSingleIso` whiskered with
`Stacks.SheafOfModules.rowComplexUnitIso`.

The three associativity steps are supplied as terms rather than rewritten: the source of the
left side is spelled with `Stacks.SheafOfModules.Tensor.tensorComplex` and that of the right
side with `CategoryTheory.Functor.map₂HomologicalComplex`, so the two `Quiver.Hom` types are
equal only up to unfolding and a `calc` block cannot find its `Trans` instance. -/
lemma tensorComplexFlipIso_tensorComplexUnitIso (L : CochainComplex (Modules X.O) ℤ) :
    (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O (unitComplex X) L).hom ≫
        (Stacks.SheafOfModules.tensorComplexUnitIso X.O L).hom =
      (HomologicalComplex.mapBifunctorSingleLeftNatIso
          (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app L ≫
        ((NatIso.mapHomologicalComplex (Stacks.SheafOfModules.unitSheafTensorNatIso (Y := X))
            (ComplexShape.up ℤ)).app L).hom ≫
          ((Functor.mapHomologicalComplexIdIso (Modules X.O) (ComplexShape.up ℤ)).app L).hom := by
  refine (Category.assoc _ _ _).symm.trans
    ((tensorComplexFlipIso_totalSingleIso X L =≫
      (Stacks.SheafOfModules.rowComplexUnitIso X.O L).hom).trans ?_)
  exact Category.assoc _ _ _

namespace DerivedTensorProduct

variable (T : DerivedTensorProduct X.O)

/-- **The left unit constraint of a derived tensor product as a natural transformation**
`𝒪[0] ⊗^L_𝒪 - ⟶ id`: the commutativity constraint at the unit followed by the unit constraint
on the right, both of which are natural. -/
def leftUnitTrans : T.tensor.obj (unitObject X) ⟶ 𝟭 (DerivedModules X.O) :=
  (braidingTrans X T).app (unitObject X) ≫ rightUnitTrans X T

/-- **The left unit constraint is the transformation `leftUnitTrans` at that object.**  Both
factors are their own transformations there, by `braidingIso_hom_eq` and
`rightUnitIso_hom_eq`, and `leftUnitIso` is their composite by definition. -/
lemma leftUnitTrans_app (A : DerivedModules X.O) :
    (leftUnitTrans X T).app A = (T.leftUnitIso X A).hom := by
  rw [leftUnitTrans, NatTrans.comp_app, ← braidingIso_hom_eq, ← rightUnitIso_hom_eq]
  rfl

/-- **At the class of a K-flat complex the left unit constraint is model-free**: it is the
K-flat comparison of `(𝒪[0], L)` followed by the Koszul flip of total complexes and the unit
law of total complexes.  The comparison of the exchanged pair that the commutativity constraint
ends with is cancelled by the one the unit constraint on the right begins with, those two being
equal by `comparisonRight_eq_comparison`. -/
lemma leftUnitTrans_app_Q (L : CochainComplex (Modules X.O) ℤ)
    (hL : Stacks.SheafOfModules.IsKFlat X.O L) :
    (leftUnitTrans X T).app (DerivedCategory.Q.obj L) =
      (T.comparison (unitComplex X) L
          (Stacks.SheafOfModules.isKFlat_single_unit X.O) hL).hom ≫
        DerivedCategory.Q.map
          ((Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O (unitComplex X) L).hom ≫
            (Stacks.SheafOfModules.tensorComplexUnitIso X.O L).hom) := by
  have hb : ((braidingTrans X T).app (unitObject X)).app (DerivedCategory.Q.obj L) =
      (T.comparison (unitComplex X) L
          (Stacks.SheafOfModules.isKFlat_single_unit X.O) hL).hom ≫
        DerivedCategory.Q.map
            (Stacks.SheafOfModules.Tensor.tensorComplexFlipIso X.O (unitComplex X) L).hom ≫
          (T.comparison L (unitComplex X) hL
            (Stacks.SheafOfModules.isKFlat_single_unit X.O)).inv :=
    braidingTrans_app_app X T (unitComplex X) L
      (Stacks.SheafOfModules.isKFlat_single_unit X.O) hL
  rw [leftUnitTrans, NatTrans.comp_app, hb, rightUnitTrans_app_Q,
    T.comparisonRight_eq_comparison L (unitComplex X) hL
      (Stacks.SheafOfModules.isKFlat_single_unit X.O),
    DerivedCategory.Q.map_comp]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]

/-- The flat-single identification of `𝒪[0] ⊗^L_𝒪 -` with the derived functor of `𝒪 ⊗_𝒪 -`,
followed by the derived functor of the sheaf-level left unitor: a second natural transformation
`𝒪[0] ⊗^L_𝒪 - ⟶ id`, built with no choice of K-flat model. -/
def flatSingleLeftUnitTrans : T.tensor.obj (unitObject X) ⟶ 𝟭 (DerivedModules X.O) :=
  letI := preservesFiniteLimits_sheafTensorObj X.O
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := X))
  letI := preservesFiniteColimits_sheafTensorObj X.O
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := X))
  (flatSingleTensorIso X.O T
        (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
        (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := X))).hom ≫
    (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
          (𝟭 (Modules X.O))
          (Stacks.SheafOfModules.unitSheafTensorNatIso (Y := X))).hom ≫
      (Stacks.Homology.mapDerivedCategoryIdIso).hom

section AppQ

-- The flat unit's exactness instances are binders of this section rather than `letI` in each
-- statement: see the implementation notes on why a `letI` in a statement is not a rewrite rule.
variable [PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))]
  [PreservesFiniteColimits ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))]
  (L : CochainComplex (Modules X.O) ℤ)

/-- The component of the lifting datum behind `flatSingleTensorIso` at a complex, with the three
factors of the composite separated.  Stated on its own rather than unfolded inside a longer
`simp only`: a `simp only` that both δ-unfolds a definition and rewrites does not re-traverse
after the unfold, and leaves the `Iso.trans` projections standing while reporting progress. -/
lemma flatSingleLifting_hom_app_eq :
    (flatSingleLifting X.O T
          (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
          (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := X))).hom.app L =
      (T.comparisonLeft (unitComplex X) L
            (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
        DerivedCategory.Q.map
            ((HomologicalComplex.mapBifunctorSingleLeftNatIso
                  (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
                  (_root_.SheafOfModules.unit
                    (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app L) ≫
          ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (_root_.SheafOfModules.unit
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).mapDerivedCategoryFactors.inv.app
            L :=
  rfl

omit hTensorAdditive
  [∀ (K L : CochainComplex (Modules X.O) ℤ),
    HomologicalComplex.HasMapBifunctor K L (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
      (ComplexShape.up ℤ)] in
/-- The lifting isomorphism that `CategoryTheory.Localization.liftNatTrans_app` produces for
`𝒪 ⊗_𝒪 -` is `CategoryTheory.Functor.mapDerivedCategoryFactors`.  The two are the same
isomorphism — the `Localization.Lifting` instance is built from it — but not syntactically, so
the cancellation against the factor `flatSingleLifting` ends with needs this bridge. -/
lemma lifting_iso_eq_mapDerivedCategoryFactors :
    Localization.Lifting.iso DerivedCategory.Q
        (HomologicalComplex.quasiIso (Modules X.O) (ComplexShape.up ℤ))
        (((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
              (_root_.SheafOfModules.unit
                (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).mapHomologicalComplex
            (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
        ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
          (_root_.SheafOfModules.unit
            (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).mapDerivedCategory =
      ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
        (_root_.SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).mapDerivedCategoryFactors :=
  rfl

/-- The three factors of `flatSingleLeftUnitTrans`, separated.  Like the two lemmas above this
holds by `rfl` and exists only so that the factors can be rewritten: the definition is a
`let`-expression, and `rw` cannot enter one. -/
lemma flatSingleLeftUnitTrans_eq :
    flatSingleLeftUnitTrans X T =
      (flatSingleTensorIso X.O T
            (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
            (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := X))).hom ≫
        (Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso
              ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
                (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))
              (𝟭 (Modules X.O))
              (Stacks.SheafOfModules.unitSheafTensorNatIso (Y := X))).hom ≫
          (Stacks.Homology.mapDerivedCategoryIdIso).hom :=
  rfl

/-- **At the class of a complex the flat-single transformation is model-free**: it is the left
K-flat comparison of `(𝒪[0], L)` followed by `Q` of the single-column collapse, the degreewise
sheaf-level left unit law and the degreewise identification of the identity functor.  No
K-flatness of `L` is needed — the left comparison asks none.

Each of the three factors is evaluated at the image of `L` separately —
`flatSingleTensorIso_hom_app_Q` with `flatSingleLifting_hom_app_eq`,
`Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q` and
`Stacks.DerivedGlueing.mapDerivedCategoryIdIso_hom_app_Q` — after which the two adjacent pairs
of `CategoryTheory.Functor.mapDerivedCategoryFactors` cancel. -/
lemma flatSingleLeftUnitTrans_app_Q :
    (flatSingleLeftUnitTrans X T).app (DerivedCategory.Q.obj L) =
      (T.comparisonLeft (unitComplex X) L
          (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.mapBifunctorSingleLeftNatIso
                (Stacks.SheafOfModules.Tensor.sheafTensor X.O)
                (_root_.SheafOfModules.unit
                  (Stacks.SheafOfModules.Tensor.ringSheaf X.O))).hom.app L ≫
            ((NatIso.mapHomologicalComplex (Stacks.SheafOfModules.unitSheafTensorNatIso (Y := X))
                (ComplexShape.up ℤ)).app L).hom ≫
              ((Functor.mapHomologicalComplexIdIso (Modules X.O)
                (ComplexShape.up ℤ)).app L).hom) := by
  rw [flatSingleLeftUnitTrans_eq, NatTrans.comp_app, NatTrans.comp_app,
    flatSingleTensorIso_hom_app_Q, flatSingleLifting_hom_app_eq,
    Stacks.DerivedCategoryComparisons.mapDerivedCategoryIsoOfNatIso_hom_app_Q,
    Stacks.DerivedGlueing.mapDerivedCategoryIdIso_hom_app_Q]
  simp only [Category.assoc, Iso.inv_hom_id_app_assoc, ← Functor.map_comp]
  -- The last merge of two `Q.map`s is whiskered as a term: the source of the composite is
  -- spelled with `tensorComplex` on one side and with `map₂HomologicalComplex` on the other,
  -- and a rewrite builds the composite in the wrong spelling.
  exact (T.comparisonLeft (unitComplex X) L
    (Stacks.SheafOfModules.isKFlat_single_unit X.O)).hom ≫=
      (DerivedCategory.Q.map_comp _ _).symm

/-- **The two transformations agree at the class of a K-flat complex.**  Both are the K-flat
comparison of `(𝒪[0], L)` followed by `Q` of a morphism of total complexes — by
`leftUnitTrans_app_Q` and `flatSingleLeftUnitTrans_app_Q` — the two comparisons agree by
`comparisonLeft_eq_comparison`, and the two morphisms of complexes agree by
`tensorComplexFlipIso_tensorComplexUnitIso`. -/
lemma leftUnitTrans_app_eq_flatSingle_Q (hL : Stacks.SheafOfModules.IsKFlat X.O L) :
    (leftUnitTrans X T).app (DerivedCategory.Q.obj L) =
      (flatSingleLeftUnitTrans X T).app (DerivedCategory.Q.obj L) := by
  rw [leftUnitTrans_app_Q X T L hL, flatSingleLeftUnitTrans_app_Q,
    T.comparisonLeft_eq_comparison (unitComplex X) L
      (Stacks.SheafOfModules.isKFlat_single_unit X.O) hL,
    tensorComplexFlipIso_tensorComplexUnitIso X L]
  rfl

end AppQ

section Agree

variable [PreservesFiniteLimits ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))]
  [PreservesFiniteColimits ((Stacks.SheafOfModules.Tensor.sheafTensor X.O).obj
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O)))]

/-- **The two transformations agree at every object of `D(𝒪)`.**  Both are natural, so each is
determined by its value at the chosen K-flat model
`AlgebraicGeometry.RingedSite.kFlatModel`, where they agree by
`leftUnitTrans_app_eq_flatSingle_Q`; the model's augmentation becomes invertible in `D(𝒪)`, so
its image under `𝒪[0] ⊗^L_𝒪 -` is an epimorphism and can be cancelled. -/
lemma leftUnitTrans_app_eq_flatSingle (A : DerivedModules X.O) :
    (leftUnitTrans X T).app A = (flatSingleLeftUnitTrans X T).app A := by
  have h₁ := (leftUnitTrans X T).naturality
    (_root_.AlgebraicGeometry.RingedSite.kFlatModelIso X A).hom
  have h₂ := (flatSingleLeftUnitTrans X T).naturality
    (_root_.AlgebraicGeometry.RingedSite.kFlatModelIso X A).hom
  refine (cancel_epi (((T.tensor.obj (unitObject X)).mapIso
    (_root_.AlgebraicGeometry.RingedSite.kFlatModelIso X A)).hom)).1 ?_
  rw [Functor.mapIso_hom, h₁, h₂,
    leftUnitTrans_app_eq_flatSingle_Q X T _
      (_root_.AlgebraicGeometry.RingedSite.isKFlat_kFlatModel X A)]

end Agree

/-- **The left unit constraint of a derived tensor product agrees with the flat-single
identification followed by the derived functor of the sheaf-level left unitor.**

The reduction of it to an identity of total complexes, and that identity, are described in the
implementation notes of this file; `leftUnitTrans_app` turns it into the objectwise statement
about `leftUnitIso`.  It is proved by `leftUnitFlatSingleAgree`. -/
def LeftUnitFlatSingleAgree : Prop :=
  leftUnitTrans X T = flatSingleLeftUnitTrans X T

/-- **`LeftUnitFlatSingleAgree` holds.**  The two transformations agree at every object by
`leftUnitTrans_app_eq_flatSingle`.  The flat unit's two exactness instances are discharged here
by `letI`, so the statement carries neither of them. -/
theorem leftUnitFlatSingleAgree : LeftUnitFlatSingleAgree X T := by
  let := preservesFiniteLimits_sheafTensorObj X.O
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := X))
  let := preservesFiniteColimits_sheafTensorObj X.O
    (_root_.SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
    (Stacks.SheafOfModules.DerivedTensorProduct.isFlat_unit (Y := X))
  exact NatTrans.ext (funext (leftUnitTrans_app_eq_flatSingle X T))

end DerivedTensorProduct

end Stacks.DerivedTensor.RingedSite

end
