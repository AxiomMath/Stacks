module

public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.DerivedPushforwardOverPushforwardRing
public import StacksFrontier.AlgebraicGeometry.Duality.ClosedImmersionTwistedInverseImage
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ConstructedDerivedAdjunction
public import StacksFrontier.AlgebraicGeometry.Duality.RightAdjointPushforward.ConstructedDerivedAdjunctionRestrictScalars

/-!
# The trace of the right adjoint of pushforward is evaluation at one

Let `f : Y ⟶ X` be an affine morphism of schemes — a finite morphism is one — and let `a` be a
right adjoint of `Rf_* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`.  The trace map `Tr_{f, K} : Rf_* a(K) ⟶ K`,
that is the counit of `Rf_* ⊣ a`, agrees with the composite

`Rf_* a(K) = R ℰom_{𝒪_X}(f₊ 𝒪_Y, K) ⟶ K`

whose identification is the comparison map of [Stacks, Tag 0AX2] and whose arrow is induced by
the map `𝒪_X ⟶ f₊ 𝒪_Y`.  This is the square of [Stacks, Tag 0AX3].

## The square, and which of its edges are built here

The source draws

```
Rf_* a(K)                     --Tr_{f, K}-->   K
    ‖                                          ‖
R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)            -->          K
```

with both vertical edges equalities.  The right edge is an identity.  The left edge is the
identification of [Stacks, Tag 0AX2]: here it is the canonical comparison map
`AlgebraicGeometry.pushforwardRightAdjointToDerivedInternalHom`,
`Rf_* a(K) ⟶ R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)`, the transpose of the trace along the adjunction of
[Stacks, Tag 0BV0] read through the factorisation of `Rf_*` of [Stacks, Tag 0AVW].  The lower
horizontal edge is the map induced by `𝒪_X ⟶ f₊ 𝒪_Y`, defined directly as the right derived
functor of evaluation at `1`, `ℰom_{𝒪_X}(f₊ 𝒪_Y, F) ⟶ F`, `φ ↦ φ(1)`
(`AlgebraicGeometry.derivedInternalHomPushforwardEvaluationOne`).  The adjunction of
[Stacks, Tag 0BV0] is constructed as the derived adjunction of
`restriction of scalars ⊣ ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` of [Stacks, Tag 0BUZ], whose counit is
evaluation at `1`, and its counit, read through [Stacks, Tag 0BV1], is proved equal to that
lower edge (`AlgebraicGeometry.derivedInternalHomPushforwardEvaluation_eq_evaluationOne`).

This file builds the edges and proves that the square commutes, which holds for every affine
morphism and every `K` in `D_QCoh(𝒪_X)`.  That the left edge is an *isomorphism* when `f` is
finite, `X` is locally Noetherian and `K` lies in `D_QCoh^+(𝒪_X)` — so that it may be drawn as
an equality — is proved in
`StacksFrontier/AlgebraicGeometry/Duality/FiniteTraceDerivedInternalHomIso.lean`, where
[Stacks, Tag 0AX3] is registered on the two assertions together.

## Main definitions

* `AlgebraicGeometry.derivedRestrictionHomSheafAdjunction` — the adjunction of
  [Stacks, Tag 0BV0], constructed by deriving the adjunction of [Stacks, Tag 0BUZ].
* `AlgebraicGeometry.derivedHomSheafRestrictionIso` — the isomorphism of [Stacks, Tag 0BV1],
  the witness of that theorem's `∃!`.
* `AlgebraicGeometry.derivedInternalHomPushforwardEvaluationOne` — the lower horizontal arrow
  `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -) ⟶ 𝟭`, the right derived functor of evaluation at `1`.
* `AlgebraicGeometry.derivedInternalHomPushforwardEvaluation` — the isomorphism of
  [Stacks, Tag 0BV1] followed by the counit of [Stacks, Tag 0BV0].
* `AlgebraicGeometry.pushforwardTraceTranspose` — the adjunct of the trace.
* `AlgebraicGeometry.pushforwardRightAdjointToDerivedInternalHom` — the left vertical edge, the
  comparison map `Rf_* a(K) ⟶ R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)` of [Stacks, Tag 0AX2]; it is an
  isomorphism by `AlgebraicGeometry.isIso_pushforwardRightAdjointToDerivedInternalHom`.

## Main results

* `AlgebraicGeometry.derivedInternalHomPushforwardEvaluation_eq_evaluationOne` — the counit of
  [Stacks, Tag 0BV0], read through [Stacks, Tag 0BV1], is the derived evaluation at `1`.
* `AlgebraicGeometry.pushforwardRightAdjointToDerivedInternalHom_comp_evaluationOne` — the square
  of [Stacks, Tag 0AX3] commutes: the comparison map of [Stacks, Tag 0AX2] followed by the map
  induced by `𝒪_X ⟶ f₊ 𝒪_Y` is the trace map.

## Implementation notes

*What the content of the square is.*  The comparison map of [Stacks, Tag 0AX2] is, here as in
the source, the transpose of the trace: the source proves that tag by uniqueness of adjoints,
and the isomorphism uniqueness of adjoints produces between two right adjoints of one functor is
by construction built from the counits.  So, with the lower arrow read as the counit, the
square is the mate identity — the triangle `L(adjunct of u) ≫ ε = u` of the adjunction of
[Stacks, Tag 0BV0].  The geometric inputs that make it a statement about the source's square are
that this counit is the map induced by `𝒪_X ⟶ f₊ 𝒪_Y`, i.e. the right derived functor of
evaluation at `1` (`AlgebraicGeometry.derivedInternalHomPushforwardEvaluation_eq_evaluationOne`,
which uses that the adjunction is the derived adjunction of [Stacks, Tag 0BUZ] and not an
arbitrary one: between two fixed functors the counit is determined only up to an automorphism of
the right adjoint), and that `Rf_*` is `Φ` followed by restriction of scalars along
`𝒪_X ⟶ f₊ 𝒪_Y` ([Stacks, Tag 0AVW]).

*Why affineness suffices for the square.*  What the commutativity needs of `f` is only that
`Rf_*` carry `D_QCoh` into `D_QCoh`, so that there is a functor for `a` to be adjoint to at all;
that is part (1) of [Stacks, Tag 08D5], available here for an *affine* morphism as
`Stacks.Duality.isQuasicoherent_homology_derivedPushforward_of_isAffineHom`, and the restricted
functor it produces is the canonical `Stacks.Duality.affineHomQuasiCoherentDerivedPushforward`.

*The adjunction of [Stacks, Tag 0BV0]* is `AlgebraicGeometry.derivedRestrictScalarsHomAdjunction`,
the derived adjunction (`CategoryTheory.Adjunction.derived`) of
`restriction of scalars ⊣ ℰom_{𝒪_X}(f₊ 𝒪_Y, -)`; it is not a witness chosen from
`AlgebraicGeometry.derivedRestriction_adj_derivedHomSheaf`, since the counit of an arbitrary
witness need not be the map induced by `𝒪_X ⟶ f₊ 𝒪_Y`.  *The isomorphism of
[Stacks, Tag 0BV1]* is unique, so nothing is chosen there beyond reading off the witness of the
`∃!` of `AlgebraicGeometry.derivedHomSheaf_comp_derivedRestriction_iso`.

*The right adjoint `a`.*  The square is drawn with `Rf_* a(K)` in it and `Tr_{f, K}` the counit
of `Rf_* ⊣ a`, so every statement below is quantified over a right adjoint `a` of `Rf_*` and an
adjunction exhibiting it.  The model of the derived categories is
`CategoryTheory.HasDerivedCategory.standard`: the lower arrow is built from
`AlgebraicGeometry.derivedRestrictionOfScalars` and `AlgebraicGeometry.derivedHomSheaf`, which
pin that model in their own definitions.

## References

* [Stacks Project, Tag 0AX3](https://stacks.math.columbia.edu/tag/0AX3)
* [Stacks Project, Tag 0AX2](https://stacks.math.columbia.edu/tag/0AX2)
* [Stacks Project, Tag 0AVW](https://stacks.math.columbia.edu/tag/0AVW)
* [Stacks Project, Tag 0BV0](https://stacks.math.columbia.edu/tag/0BV0)
* [Stacks Project, Tag 0BV1](https://stacks.math.columbia.edu/tag/0BV1)
* [Stacks Project, Tag 0BUZ](https://stacks.math.columbia.edu/tag/0BUZ)
* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 0B6M](https://stacks.math.columbia.edu/tag/0B6M)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
-/

@[expose] public noncomputable section

open CategoryTheory
open Stacks.AlgebraicGeometry.DerivedAffinePushforward (derivedPushforwardOverRing
  derivedPushforwardOverRingCompRestrictScalarsIso)
open Stacks.Duality (affineHomQuasiCoherentDerivedPushforward derivedPushforward
  quasiCoherentDerivedCategory)

-- Standard model only: `AlgebraicGeometry.derivedRestrictionOfScalars`,
--   `AlgebraicGeometry.derivedHomSheaf`, `AlgebraicGeometry.derivedInternalHomPushforward`.
attribute [local instance 10000] HasDerivedCategory.standard

universe u

namespace AlgebraicGeometry

variable {X Y : Scheme.{u}} (f : Y ⟶ X)

/-- **The adjunction of [Stacks, Tag 0BV0]**: restriction of scalars along `𝒪_X ⟶ f₊ 𝒪_Y` is
left adjoint to `R ℰom(f₊ 𝒪_Y, -)`.  This is the specific adjunction
`AlgebraicGeometry.derivedRestrictScalarsHomAdjunction` obtained by deriving the adjunction
`restriction of scalars ⊣ ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` of [Stacks, Tag 0BUZ], not an arbitrary witness
of `AlgebraicGeometry.derivedRestriction_adj_derivedHomSheaf`: its counit is induced by the
underived counit, which is evaluation at the section `1`
(`AlgebraicGeometry.derivedRestrictScalarsHomAdjunction_counit_fac`).  This matters: the counit
of an adjunction between two fixed functors is only determined up to an automorphism of the right
adjoint, and it is the counit that the square of [Stacks, Tag 0AX3] is about. -/
def derivedRestrictionHomSheafAdjunction :
    derivedRestrictionOfScalars f ⊣ derivedHomSheaf f :=
  derivedRestrictScalarsHomAdjunction f

/-- **The isomorphism of [Stacks, Tag 0BV1]**: following `R ℰom(f₊ 𝒪_Y, -)` by restriction of
scalars gives `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)`.  This reads off the witness of the `∃!` of
`AlgebraicGeometry.derivedHomSheaf_comp_derivedRestriction_iso`, which holds for every morphism
of schemes with nothing assumed, and which pins the isomorphism uniquely. -/
def derivedHomSheafRestrictionIso :
    derivedHomSheaf f ⋙ derivedRestrictionOfScalars f ≅ derivedInternalHomPushforward f :=
  (derivedHomSheaf_comp_derivedRestriction_iso f).choose

/-- The isomorphism of [Stacks, Tag 0BV1] is compatible with the comparison maps: the comparison
map of `R ℰom(f₊ 𝒪_Y, -)` followed by restriction of scalars, followed by the isomorphism, is the
comparison map of `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)`. -/
theorem compositeDerivedHomSheafUnit_comp_derivedHomSheafRestrictionIso_hom :
    compositeDerivedHomSheafUnit f ≫
        Functor.whiskerLeft DerivedCategory.Qh (derivedHomSheafRestrictionIso f).hom =
      derivedInternalHomPushforwardUnit f :=
  (derivedHomSheaf_comp_derivedRestriction_iso f).choose_spec.1

/-- **Evaluation at `1` on complexes, in the homotopy category**: the natural transformation
`ℰom_{𝒪_X}(f₊ 𝒪_Y, -) ⟶ 𝟭` of [Stacks, Tag 0BUZ] — the counit of
`restriction of scalars ⊣ ℰom_{𝒪_X}(f₊ 𝒪_Y, -)`, which sends a local homomorphism
`φ : f₊ 𝒪_Y|_U ⟶ F|_U` to `φ(1)` and is the map `ℰom_{𝒪_X}(f₊ 𝒪_Y, F) ⟶ ℰom_{𝒪_X}(𝒪_X, F) = F`
induced by `𝒪_X ⟶ f₊ 𝒪_Y` — applied degreewise to complexes. -/
def homSheafEvaluationOneHomotopy :
    letI := homSheaf_comp_restrictScalars_additive f
    (RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom ⋙
        SheafOfModules.restrictScalars f.toRingCatSheafHom).mapHomotopyCategory
          (ComplexShape.up ℤ) ⟶
      𝟭 (HomotopyCategory (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) :=
  letI := homSheaf_comp_restrictScalars_additive f
  CategoryTheory.Quotient.natTransLift _
    (Functor.whiskerRight
      (NatTrans.mapHomologicalComplex
          (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction f.toRingCatSheafHom).counit
          (ComplexShape.up ℤ) ≫
        (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom)
      (HomotopyCategory.quotient _ _))

/-- **The map `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -) ⟶ 𝟭` induced by `𝒪_X ⟶ f₊ 𝒪_Y`**, defined directly as the
right derived functor of evaluation at `1`: the natural transformation out of the right derived
functor `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` of `ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` induced, by its universal property,
by `AlgebraicGeometry.homSheafEvaluationOneHomotopy`.  It is characterised by
`AlgebraicGeometry.derivedInternalHomPushforwardEvaluationOne_fac_app`: on a complex `K` it is
the localization of the degreewise evaluation at `1`, `ℰom_{𝒪_X}(f₊ 𝒪_Y, K) ⟶ K`.

This is the lower horizontal arrow of the square of [Stacks, Tag 0AX3]; it is equal to
`AlgebraicGeometry.derivedInternalHomPushforwardEvaluation`
(`AlgebraicGeometry.derivedInternalHomPushforwardEvaluation_eq_evaluationOne`). -/
def derivedInternalHomPushforwardEvaluationOne :
    derivedInternalHomPushforward f ⟶ 𝟭 (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :=
  (derivedInternalHomPushforward f).rightDerivedDesc (derivedInternalHomPushforwardUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) (𝟭 _)
    (Functor.whiskerRight (homSheafEvaluationOneHomotopy f) DerivedCategory.Qh ≫
      (Functor.leftUnitor _).hom ≫ (Functor.rightUnitor _).inv)

/-- On the image of a complex `K`, the comparison map of `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` followed by
`AlgebraicGeometry.derivedInternalHomPushforwardEvaluationOne` is the localization of evaluation
at `1`, `ℰom_{𝒪_X}(f₊ 𝒪_Y, K) ⟶ K`, applied degreewise. -/
theorem derivedInternalHomPushforwardEvaluationOne_fac_app
    (K : HomotopyCategory (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ)) :
    (derivedInternalHomPushforwardUnit f).app K ≫
        (derivedInternalHomPushforwardEvaluationOne f).app (DerivedCategory.Qh.obj K) =
      DerivedCategory.Qh.map ((homSheafEvaluationOneHomotopy f).app K) := by
  rw [derivedInternalHomPushforwardEvaluationOne, Functor.rightDerived_fac_app]
  simp

/-- **The counit of [Stacks, Tag 0BV0] as a map `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -) ⟶ 𝟭`**: the isomorphism
of [Stacks, Tag 0BV1] followed by the counit of the adjunction of [Stacks, Tag 0BV0], which is
the derived form of the adjunction `restriction of scalars ⊣ ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` of
[Stacks, Tag 0BUZ].

It is equal to the right derived functor of evaluation at `1`,
`AlgebraicGeometry.derivedInternalHomPushforwardEvaluationOne`, the lower horizontal arrow of the
square of [Stacks, Tag 0AX3], by
`AlgebraicGeometry.derivedInternalHomPushforwardEvaluation_eq_evaluationOne`.  It is built for
every morphism of schemes. -/
def derivedInternalHomPushforwardEvaluation :
    derivedInternalHomPushforward f ⟶ 𝟭 (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :=
  (derivedHomSheafRestrictionIso f).inv ≫ (derivedRestrictionHomSheafAdjunction f).counit

/-- Evaluation at one, precomposed with the identification of [Stacks, Tag 0BV1], is the counit
of the adjunction of [Stacks, Tag 0BV0]. -/
@[reassoc]
theorem derivedInternalHomPushforwardEvaluation_app (K : DerivedCategory
    (SheafOfModules.{u} X.ringCatSheaf)) :
    (derivedHomSheafRestrictionIso f).hom.app K ≫
        (derivedInternalHomPushforwardEvaluation f).app K =
      (derivedRestrictionHomSheafAdjunction f).counit.app K := by
  rw [derivedInternalHomPushforwardEvaluation, NatTrans.comp_app, Iso.hom_inv_id_app_assoc]

/-- Cancelling a split monomorphism inside a composite: if `i ≫ j = 𝟙` and `g ≫ e = j ≫ m`,
then `(a ≫ 𝟙 ≫ i ≫ 𝟙 ≫ g ≫ 𝟙) ≫ e = a ≫ m`. -/
private theorem comp_comp_comp_eq_of_hom_inv_id {C : Type*} [Category C] {P Q R S T : C}
    (a : P ⟶ Q) (i : Q ⟶ R) (j : R ⟶ Q) (g : R ⟶ S) (e : S ⟶ T) (m : Q ⟶ T)
    (hij : i ≫ j = 𝟙 Q) (h : g ≫ e = j ≫ m) :
    (a ≫ 𝟙 Q ≫ i ≫ 𝟙 R ≫ g ≫ 𝟙 S) ≫ e = a ≫ m := by
  simp only [Category.id_comp, Category.comp_id, Category.assoc, h, reassoc_of% hij]

/-- On the image of a complex `K`, evaluation at `1` in the homotopy category is the class of the
degreewise counit `ℰom_{𝒪_X}(f₊ 𝒪_Y, K) ⟶ K`. -/
theorem homSheafEvaluationOneHomotopy_app_quotient
    (K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) :
    letI := homSheaf_comp_restrictScalars_additive f
    (homSheafEvaluationOneHomotopy f).app ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map ((NatTrans.mapHomologicalComplex
          (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction f.toRingCatSheafHom).counit
          (ComplexShape.up ℤ)).app K ≫
        (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.app K) :=
  rfl

/-- The identification of `ℰom(f₊ 𝒪_Y, -)` followed by restriction of scalars with
`ℰom_{𝒪_X}(f₊ 𝒪_Y, -)`, on complexes, followed by the degreewise counit, is the degreewise
counit. -/
theorem mapHomologicalComplexCompIso_inv_app_comp_counit
    (K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) :
    letI := restrictScalars_additive f
    letI := homSheaf_additive f
    letI := homSheaf_comp_restrictScalars_additive f
    (Functor.mapHomologicalComplexCompIso (Iso.refl
        (RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom ⋙
          SheafOfModules.restrictScalars f.toRingCatSheafHom)) (ComplexShape.up ℤ)).inv.app K ≫
      ((RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction
          f.toRingCatSheafHom).mapHomologicalComplex (ComplexShape.up ℤ)).counit.app K =
    (NatTrans.mapHomologicalComplex
          (RingedSpaceModuleAdjunction.restrictScalarsHomAdjunction f.toRingCatSheafHom).counit
          (ComplexShape.up ℤ)).app K ≫
        (Functor.mapHomologicalComplexIdIso _ (ComplexShape.up ℤ)).hom.app K := by
  let := restrictScalars_additive f
  let := homSheaf_additive f
  let := homSheaf_comp_restrictScalars_additive f
  ext n
  simp [Functor.mapHomologicalComplexCompIso, Functor.mapHomologicalComplexIdIso]
  rfl

/-- The comparison map of the composite of `R ℰom(f₊ 𝒪_Y, -)` and derived restriction of scalars,
unfolded at the image of a complex `K`. -/
theorem compositeDerivedHomSheafUnit_app_quotient
    (K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) :
    letI := restrictScalars_additive f
    letI := homSheaf_additive f
    letI := homSheaf_comp_restrictScalars_additive f
    (compositeDerivedHomSheafUnit f).app ((HomotopyCategory.quotient _ _).obj K) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso (Iso.refl
            (RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom ⋙
              SheafOfModules.restrictScalars f.toRingCatSheafHom)) (ComplexShape.up ℤ)).inv.app
            K)) ≫ 𝟙 _ ≫
        (inv (derivedRestrictionOfScalarsFactors f).hom).app
          (((RingedSpaceModuleAdjunction.homSheaf f.toRingCatSheafHom).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj ((HomotopyCategory.quotient _ _).obj K)) ≫ 𝟙 _ ≫
        (derivedRestrictionOfScalars f).map
          ((derivedHomSheafUnit f).app ((HomotopyCategory.quotient _ _).obj K)) ≫ 𝟙 _ :=
  rfl

/-- On the image of a complex `K`, the comparison map of the composite of `R ℰom(f₊ 𝒪_Y, -)` and
derived restriction of scalars, followed by the counit of the adjunction of
[Stacks, Tag 0BV0], is the localization of evaluation at `1`. -/
theorem compositeDerivedHomSheafUnit_app_comp_counit
    (K : CochainComplex (SheafOfModules.{u} X.ringCatSheaf) ℤ) :
    (compositeDerivedHomSheafUnit f).app ((HomotopyCategory.quotient _ _).obj K) ≫
        (derivedRestrictionHomSheafAdjunction f).counit.app
          (DerivedCategory.Qh.obj ((HomotopyCategory.quotient _ _).obj K)) =
      DerivedCategory.Qh.map
        ((homSheafEvaluationOneHomotopy f).app ((HomotopyCategory.quotient _ _).obj K)) := by
  let := restrictScalars_additive f
  let := homSheaf_additive f
  let := homSheaf_comp_restrictScalars_additive f
  rw [compositeDerivedHomSheafUnit_app_quotient, homSheafEvaluationOneHomotopy_app_quotient]
  refine (comp_comp_comp_eq_of_hom_inv_id _ _ _ _ _ _
    (NatTrans.congr_app (IsIso.inv_hom_id (derivedRestrictionOfScalarsFactors f).hom) _)
    (derivedRestrictScalarsHomAdjunction_counit_fac f K)).trans ?_
  refine (Functor.map_comp _ _ _).symm.trans (congrArg _ ?_)
  exact ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map_comp _ _).symm.trans
    (congrArg _ (mapHomologicalComplexCompIso_inv_app_comp_counit f K))

/-- **The lower arrow is evaluation at `1`.**  The isomorphism of [Stacks, Tag 0BV1] followed by
the counit of the adjunction of [Stacks, Tag 0BV0] is the right derived functor of evaluation at
`1`, `AlgebraicGeometry.derivedInternalHomPushforwardEvaluationOne`: both are natural
transformations out of the right derived functor `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)`, and they agree after
the comparison map, on every complex, by
`AlgebraicGeometry.compositeDerivedHomSheafUnit_app_comp_counit`. -/
theorem derivedInternalHomPushforwardEvaluation_eq_evaluationOne :
    derivedInternalHomPushforwardEvaluation f = derivedInternalHomPushforwardEvaluationOne f := by
  apply Functor.rightDerived_ext (derivedInternalHomPushforward f)
    (derivedInternalHomPushforwardUnit f)
    (HomotopyCategory.quasiIso (SheafOfModules.{u} X.ringCatSheaf) (ComplexShape.up ℤ))
  ext ⟨K⟩
  have hA := congrArg (fun t => t.app ((HomotopyCategory.quotient _ _).obj K))
    (compositeDerivedHomSheafUnit_comp_derivedHomSheafRestrictionIso_hom f)
  exact ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) hA)).symm.trans
    ((congrArg (_ ≫ ·) (derivedInternalHomPushforwardEvaluation_app f _)).trans
      ((compositeDerivedHomSheafUnit_app_comp_counit f K).trans
        (derivedInternalHomPushforwardEvaluationOne_fac_app f _).symm))

section

variable [IsAffineHom f]
  {a : quasiCoherentDerivedCategory X ⥤ quasiCoherentDerivedCategory Y}
  (adj : affineHomQuasiCoherentDerivedPushforward f ⊣ a)

/-- **The adjunct of the trace map**: the transpose of

`Rf_* a(K) ⟶ K`,

read through the factorisation of `Rf_*` of [Stacks, Tag 0AVW], along the adjunction of
[Stacks, Tag 0BV0].  This is the map `Φ(a(K)) ⟶ R ℰom(f₊ 𝒪_Y, K)` of `f₊ 𝒪_Y`-modules out of
which the comparison map of [Stacks, Tag 0AX2] is built. -/
def pushforwardTraceTranspose (K : quasiCoherentDerivedCategory X) :
    (derivedPushforwardOverRing f).obj (a.obj K).obj ⟶ (derivedHomSheaf f).obj K.obj :=
  (derivedRestrictionHomSheafAdjunction f).homEquiv
    ((derivedPushforwardOverRing f).obj (a.obj K).obj) K.obj
    ((derivedPushforwardOverRingCompRestrictScalarsIso f).inv.app ((a.obj K).obj) ≫
      (adj.counit.app K).hom)

/-- **The comparison map of [Stacks, Tag 0AX2]**, the left vertical edge of the square of
[Stacks, Tag 0AX3]: the canonical map `Rf_* a(K) ⟶ R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)`.

It is the transpose of the trace `Rf_* a(K) ⟶ K` along the adjunction of [Stacks, Tag 0BV0],
taken through the factorisation `Rf_* = Φ` followed by restriction of scalars of
[Stacks, Tag 0AVW] and read into `R ℰom_{𝒪_X}(f₊ 𝒪_Y, -)` by [Stacks, Tag 0BV1].

[Stacks, Tag 0AX2] is the assertion that this map is invertible when `f` is a finite morphism of
Noetherian schemes and `K` lies in `D_QCoh^+(𝒪_X)`; that is
`AlgebraicGeometry.isIso_pushforwardRightAdjointToDerivedInternalHom`. -/
def pushforwardRightAdjointToDerivedInternalHom (K : quasiCoherentDerivedCategory X) :
    (derivedPushforward f).obj (a.obj K).obj ⟶
      (derivedInternalHomPushforward f).obj K.obj :=
  (derivedPushforwardOverRingCompRestrictScalarsIso f).hom.app ((a.obj K).obj) ≫
    (derivedRestrictionOfScalars f).map (pushforwardTraceTranspose f adj K) ≫
      (derivedHomSheafRestrictionIso f).hom.app K.obj

/-- **The mate identity behind the square of [Stacks, Tag 0AX3].** Let `f : Y ⟶ X` be an affine
morphism of schemes and let `a` be a right adjoint of `Rf_* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`.  Then
the comparison map of [Stacks, Tag 0AX2] followed by
`AlgebraicGeometry.derivedInternalHomPushforwardEvaluation` — the isomorphism of
[Stacks, Tag 0BV1] followed by the counit of [Stacks, Tag 0BV0] — is the trace map `Tr_{f, K}`,
that is the counit of `Rf_* ⊣ a`.  This is the triangle identity of the adjunction of
[Stacks, Tag 0BV0]; the square with the lower arrow stated as the derived evaluation at `1` is
`AlgebraicGeometry.pushforwardRightAdjointToDerivedInternalHom_comp_evaluationOne`. -/
theorem pushforwardRightAdjointToDerivedInternalHom_comp_evaluation
    (K : quasiCoherentDerivedCategory X) :
    pushforwardRightAdjointToDerivedInternalHom f adj K ≫
        (derivedInternalHomPushforwardEvaluation f).app K.obj =
      (adj.counit.app K).hom := by
  have hmid : ((derivedRestrictionOfScalars f).map (pushforwardTraceTranspose f adj K) ≫
          (derivedHomSheafRestrictionIso f).hom.app K.obj) ≫
        (derivedInternalHomPushforwardEvaluation f).app K.obj =
      (derivedPushforwardOverRingCompRestrictScalarsIso f).inv.app ((a.obj K).obj) ≫
        (adj.counit.app K).hom :=
    (Category.assoc _ _ _).trans
      ((congrArg (fun t => (derivedRestrictionOfScalars f).map
            (pushforwardTraceTranspose f adj K) ≫ t)
          (derivedInternalHomPushforwardEvaluation_app f K.obj)).trans
        ((Adjunction.homEquiv_counit (derivedRestrictionHomSheafAdjunction f)
              ((derivedPushforwardOverRing f).obj (a.obj K).obj) K.obj
              (pushforwardTraceTranspose f adj K)).symm.trans
          (Equiv.symm_apply_apply _ _)))
  exact (Category.assoc _ _ _).trans
    ((congrArg (fun t =>
          (derivedPushforwardOverRingCompRestrictScalarsIso f).hom.app ((a.obj K).obj) ≫ t)
        hmid).trans (Iso.hom_inv_id_app_assoc _ _ _))

/-- **The square of [Stacks, Tag 0AX3] commutes.** Let `f : Y ⟶ X` be an affine morphism of
schemes and let `a` be a right adjoint of `Rf_* : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)`.  Then the
comparison map `Rf_* a(K) ⟶ R ℰom_{𝒪_X}(f₊ 𝒪_Y, K)` of [Stacks, Tag 0AX2] followed by the map
`R ℰom_{𝒪_X}(f₊ 𝒪_Y, K) ⟶ K` induced by `𝒪_X ⟶ f₊ 𝒪_Y` — the right derived functor of
evaluation at `1`, `AlgebraicGeometry.derivedInternalHomPushforwardEvaluationOne` — is the trace
map `Tr_{f, K}`, that is the counit of `Rf_* ⊣ a`.

The whole remark — this together with the invertibility of the comparison map, for `f` finite
and `K` in `D_QCoh^+(𝒪_X)` — is
`AlgebraicGeometry.isIso_pushforwardRightAdjointToDerivedInternalHom_and_comp_evaluationOne`. -/
theorem pushforwardRightAdjointToDerivedInternalHom_comp_evaluationOne
    (K : quasiCoherentDerivedCategory X) :
    pushforwardRightAdjointToDerivedInternalHom f adj K ≫
        (derivedInternalHomPushforwardEvaluationOne f).app K.obj =
      (adj.counit.app K).hom :=
  (congrArg (fun t : derivedInternalHomPushforward f ⟶ 𝟭 _ =>
      pushforwardRightAdjointToDerivedInternalHom f adj K ≫ t.app K.obj)
    (derivedInternalHomPushforwardEvaluation_eq_evaluationOne f)).symm.trans
    (pushforwardRightAdjointToDerivedInternalHom_comp_evaluation f adj K)

end

end AlgebraicGeometry

end
