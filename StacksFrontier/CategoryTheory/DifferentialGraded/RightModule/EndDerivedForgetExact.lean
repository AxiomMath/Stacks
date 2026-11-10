module

public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedCochainComplex
public import StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedHomPhiReflectorExact

/-!
# Evaluation at an object commutes with the translations, and is exact

Let `C` be a differential graded category over a commutative ring `R` and let `X` be an object
of `C`. Evaluation at `X` is the functor `ev_X : K(Mod^dg(C)) ⥤ K(ModuleCat R)` of
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.CochainComplexFunctor`, and it
descends to `ev_X : D(C) ⥤ D(ModuleCat R)` in
`StacksFrontier.CategoryTheory.DifferentialGraded.RightModule.DerivedCochainComplex`. That descent
is obtained from the universal property of the localization alone, so it carries no
`CategoryTheory.Functor.CommShift ℤ`; this file supplies one, shows that evaluation at `X` is
exact for it, and hence supplies both for the forgetful functor
`U = DGCategory.endDerivedForget : D(C(K, K)) ⥤ D(ModuleCat R)` of step 3 of the replacement
proof of [Stacks, Tag 09LK] and for the composite `R̃ ⋙ U` that step 3 reads the values of `R̃`
through.

## Where the comparison comes from

The translation of `Mod^dg(C)` shifts the degrees of a module and multiplies its differential by
the Koszul sign `(-1)^n` (`DGCategory.RightModule.shift_obj`,
`DGCategory.RightModule.shift_d`); Mathlib's translation of `CochainComplex (ModuleCat R) ℤ`
reindexes degrees by `p + n` and multiplies the differential by `Int.negOnePow n`
(`CochainComplex.shiftFunctor_obj_X'`, `CochainComplex.shiftFunctor_obj_d'`). The two agree:
the underlying modules are *the same* in each degree, and the two signs agree because
`(n.negOnePow : R) = (-1)^|n|`. So `(M⟦n⟧) X` and `(M X)⟦n⟧` are identified by an isomorphism of
complexes which is the identity in every degree,
`DGCategory.RightModule.cochainComplexShiftIso`.

Everything else is bookkeeping around that one identification:

* on the homotopy categories the comparison is that isomorphism read through
  `HomotopyCategory.quotient`, composed with the quotient functor's own commutation with the
  shift; its naturality is the statement that the shift of a *closed degree-zero* morphism
  carries the Koszul sign `(-1)^{n·0} = 1`, that is no sign at all;
* the two coherences of a `CategoryTheory.Functor.CommShift` reduce to the corresponding
  coherences for `HomotopyCategory.quotient` together with two identities of maps of
  complexes, `DGCategory.RightModule.cochainComplexShiftIso_zero` and
  `DGCategory.RightModule.cochainComplexShiftIso_add`. Both hold because the translation of
  `Mod^dg(C)` is *strict* — `M⟦0⟧ = M` and `M⟦a + b⟧ = (M⟦a⟧)⟦b⟧` are equalities, and
  `DGCategory.strictHasShift` therefore has `CategoryTheory.shiftFunctorZero` and
  `CategoryTheory.shiftFunctorAdd` equal to the `eqToIso` of those equalities;
* on the derived categories the comparison is
  `CategoryTheory.Functor.commShiftOfLocalization` at the quotient functor
  `DGCategory.RightModule.derivedQ`, for which the required
  `CategoryTheory.Localization.Lifting` instance is the one `CategoryTheory.Localization.lift`
  carries.

## Where the exactness comes from

The distinguished triangles of `K(Mod^dg(C))` are those isomorphic to the triangle
`DGCategory.GradedSplitShortExact.associatedKTriangle` of an admissible short exact sequence
`E` (`DGCategory.distinguishedTriangles_rightModuleHomotopyCategory`); those of
`K(ModuleCat R)` are those isomorphic to `CochainComplex.trianglehOfDegreewiseSplit` of a
degreewise split short exact sequence of complexes. Evaluating `E` at `X` gives such a sequence,
`DGCategory.RightModule.gradedSplitShortComplex` with the splitting
`DGCategory.RightModule.gradedSplitSplitting`, and the two triangles are then *equal*: the
first two arrows are literally the same morphisms, and the third ones agree by
`DGCategory.RightModule.cochainMap_connectingCocycle_comp_shiftIso`.

That identity compares two spellings of the connecting map. On one side is the degree-one
morphism `π ∘ d(s)` of `DGCategory.GradedSplitShortExact.connectingHom`, moved into the shifted
target by axiom (B) as `DGCategory.GradedSplitShortExact.connectingCocycle` and then read at
`X`; on the other is Mathlib's `CochainComplex.homOfDegreewiseSplit`, with components
`(σ p).s ≫ d ≫ (σ (p + 1)).r`. Neither transport contributes a sign: axiom (B)'s
`DGCategory.ShiftAxiomB.toShift` is used here in degree `k = 0`, where
`DGCategory.RightModule.toShiftHom` is the morphism itself;
`DGCategory.RightModule.cochainComplexShiftIso` is the identity in every degree; and
`CochainComplex.HomComplex.Cochain.rightShift 1 0` contributes none either, by
`CochainComplex.homOfDegreewiseSplit_f`. The one sign that does appear is the `(-1)^|0| = 1` of
the Hom-complex differential `d(s) = d_y ∘ s - (-1)^0 s ∘ d_z`, whose second term is killed by
`π ∘ s = 0`. So in degree `p` both sides are `π(d_y(s(a)))`.

Exactness then passes to the derived categories by
`CategoryTheory.Functor.isTriangulated_of_localization` at `DGCategory.RightModule.derivedQ`,
for exactly the `CategoryTheory.Functor.commShiftOfLocalization` structure this file installs.

## Main definitions

* `DGCategory.RightModule.cochainComplexShiftIso`: **the identification `(M⟦n⟧) X ≅ (M X)⟦n⟧`.**
* `DGCategory.RightModule.cochainComplexOnKCommShiftIso`: the induced comparison of functors
  `K(Mod^dg(C)) ⥤ K(ModuleCat R)`.
* `DGCategory.endDerivedForgetCommShift`: **`U : D(C(K, K)) ⥤ D(ModuleCat R)` commutes with the
  translations.** A definition rather than an instance, since instance search already produces
  this term from `DGCategory.RightModule.derivedEvaluationForget_commShift` and
  `CategoryTheory.Functor.CommShift` is data.
* `DGCategory.phiReflectorForgetCommShift`: **`R̃ ⋙ U` commutes with the translations**, from
  that and `DGCategory.phiReflectorCommShift`.

## Main results

* `DGCategory.strictHasShift_shiftFunctorZero` and
  `DGCategory.strictHasShift_shiftFunctorAdd`: the two coherence isomorphisms of a translation
  assembled from strict equalities of functors are the `eqToIso` of those equalities.
* The instances `(DGCategory.RightModule.cochainComplexOnK X).CommShift ℤ` and
  `(DGCategory.RightModule.derivedEvaluationForget C X).CommShift ℤ`.
* `DGCategory.RightModule.cochainMap_connectingCocycle_comp_shiftIso`: **the two spellings of
  the connecting map of an admissible short exact sequence agree.**
* `DGCategory.RightModule.mapTriangle_associatedKTriangle`: the triangle of an admissible short
  exact sequence, carried over by evaluation at `X`, is Mathlib's triangle of the degreewise
  split sequence it becomes.
* The instances `(DGCategory.RightModule.cochainComplexOnK X).IsTriangulated` and
  `(DGCategory.RightModule.derivedEvaluationForget C X).IsTriangulated`.
* `DGCategory.endDerivedForget_isTriangulated`: **`U : D(C(K, K)) ⥤ D(ModuleCat R)` is exact.**
* `DGCategory.phiReflectorForget_isTriangulated`: **`R̃ ⋙ U : D(A) ⥤ D(Ab)` is exact.**

## References

* [Stacks Project, Tag 09LK](https://stacks.math.columbia.edu/tag/09LK)
* [Stacks Project, Tag 09P6](https://stacks.math.columbia.edu/tag/09P6), axiom (B)
-/
@[expose] public section

namespace DGCategory

universe w v u r

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

/-! ### The coherence isomorphisms of a strict translation -/

/-- For the translation `DGCategory.strictHasShift D F h0 ha` assembled from strict equalities of
functors, the isomorphism `shiftFunctorZero D ℤ` is the `eqToIso` of `F 0 = 𝟭 D`. -/
theorem strictHasShift_shiftFunctorZero (D : Type*) [Category D] (F : ℤ → D ⥤ D)
    (h0 : F 0 = 𝟭 D) (ha : ∀ n m, F (n + m) = F n ⋙ F m) :
    letI := strictHasShift D F h0 ha
    CategoryTheory.shiftFunctorZero D ℤ = eqToIso h0 := by
  let := strictHasShift D F h0 ha
  exact ShiftMkCore.shiftFunctorZero_eq _

/-- For the translation `DGCategory.strictHasShift D F h0 ha` assembled from strict equalities of
functors, the isomorphism `shiftFunctorAdd D a b` is the `eqToIso` of `F (a + b) = F a ⋙ F b`. -/
theorem strictHasShift_shiftFunctorAdd (D : Type*) [Category D] (F : ℤ → D ⥤ D)
    (h0 : F 0 = 𝟭 D) (ha : ∀ n m, F (n + m) = F n ⋙ F m) (a b : ℤ) :
    letI := strictHasShift D F h0 ha
    CategoryTheory.shiftFunctorAdd D a b = eqToIso (ha a b) := by
  let := strictHasShift D F h0 ha
  exact ShiftMkCore.shiftFunctorAdd_eq _ a b

variable {R : Type r} [CommRing R] {C : DGCategory.{v, u} R}

/-- On the homotopy category of right differential graded modules over `C`, the isomorphism
`shiftFunctorZero` is the `eqToIso` of the equality of the shift by `0` with the identity. -/
theorem shiftFunctorZero_rightModuleHomotopyCategory :
    CategoryTheory.shiftFunctorZero (rightModuleCategory.{w} C).K ℤ =
      eqToIso (rightModuleShift_onK_zero.{w} C) :=
  strictHasShift_shiftFunctorZero _ _ _ _

/-- On the homotopy category of right differential graded modules over `C`, the isomorphism
`shiftFunctorAdd a b` is the `eqToIso` of the equality of the shift by `a + b` with the composite
of the shifts by `a` and by `b`. -/
theorem shiftFunctorAdd_rightModuleHomotopyCategory (a b : ℤ) :
    CategoryTheory.shiftFunctorAdd (rightModuleCategory.{w} C).K a b =
      eqToIso (rightModuleShift_onK_add.{w} C a b) :=
  strictHasShift_shiftFunctorAdd _ _ _ _ a b

namespace RightModule

attribute [local implicit_reducible] DGCategory.K

/-! ### The shift of a module, evaluated at an object -/

/-- In an `R`-module, acting by the integer `n.negOnePow` is acting by `(-1 : R) ^ |n|`. -/
theorem negOnePow_zsmul_eq (R : Type r) [CommRing R] {W : Type*} [AddCommGroup W] [Module R W]
    (n : ℤ) (w : W) : (n.negOnePow : ℤ) • w = (-1 : R) ^ n.natAbs • w := by
  rw [← Int.cast_smul_eq_zsmul R, Int.coe_negOnePow R n]

/-- **`(M⟦n⟧) X = (M X)⟦n⟧`**: evaluating the shift of a right differential graded module at an
object gives Mathlib's shift of the evaluated complex, by an isomorphism which is the identity in
each degree. Both complexes have `M X` in degree `i + n`, and both differentials are that of `M`
multiplied by `(-1)^n`. -/
def cochainComplexShiftIso (M : RightModule.{w} C) (X : C.Obj) (n : ℤ) :
    ((rightModuleShiftFunctor.{w} C n).obj M).cochainComplex X ≅
      (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{w} R) ℤ) n).obj
        (M.cochainComplex X) :=
  HomologicalComplex.Hom.isoOfComponents (fun _ => Iso.refl _) (by
    intro i j hij
    have hij' : i + 1 = j := hij
    have hd : ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{w} R) ℤ) n).obj
        (M.cochainComplex X)).d i j = ((shift M n).cochainComplex X).d i j := by
      rw [CochainComplex.shiftFunctor_obj_d',
        cochainComplex_d M X (show i + n + 1 = j + n by omega),
        cochainComplex_d (shift M n) X hij']
      ext a
      change (n.negOnePow : ℤ) • M.d (show i + n + 1 = j + n by omega) a =
        (-1 : R) ^ n.natAbs • M.d (show i + n + 1 = j + n by omega) a
      exact negOnePow_zsmul_eq R n _
    exact (Category.id_comp _).trans (hd.trans (Category.comp_id _).symm))

/-- In each degree, `DGCategory.RightModule.cochainComplexShiftIso` is the identity. -/
@[simp] theorem cochainComplexShiftIso_hom_f (M : RightModule.{w} C) (X : C.Obj) (n i : ℤ) :
    (cochainComplexShiftIso M X n).hom.f i = 𝟙 _ := rfl

/-- The comparison in degree `0` is the transport along `M⟦0⟧ = M`. -/
theorem cochainComplexShiftIso_zero (M : RightModule.{w} C) (X : C.Obj) :
    (cochainComplexShiftIso M X 0).hom ≫
        (CategoryTheory.shiftFunctorZero (CochainComplex (ModuleCat.{w} R) ℤ) ℤ).hom.app
          (M.cochainComplex X) =
      eqToHom (congrArg (fun N : RightModule.{w} C => N.cochainComplex X)
        (RightModule.shift_zero M)) := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, cochainComplexShiftIso_hom_f]
  refine (Category.id_comp _).trans ?_
  rw [CochainComplex.shiftFunctorZero_hom_app_f, HomologicalComplex.eqToHom_f]
  rfl

/-- The shift of a module in the homotopy category `K(Mod^dg(C))` is its shift as a right
differential graded module. -/
theorem shiftFunctor_rightModuleHomotopyCategory_obj (n : ℤ) (M : (rightModuleCategory.{w} C).K) :
    (CategoryTheory.shiftFunctor (rightModuleCategory.{w} C).K n).obj M =
      (rightModuleShiftFunctor.{w} C n).obj M := rfl

/-- The shift of a module by `a + b` is its shift by `a` followed by its shift by `b`. -/
theorem rightModuleShiftFunctor_obj_add (a b : ℤ) (M : (rightModuleCategory.{w} C).K) :
    (rightModuleShiftFunctor.{w} C (a + b)).obj M =
      (rightModuleShiftFunctor.{w} C b).obj ((rightModuleShiftFunctor.{w} C a).obj M) :=
  rightModuleShift_obj_add C a b M

/-- The comparisons in degrees `a` and `b` compose to the comparison in degree `a + b`. -/
theorem cochainComplexShiftIso_add (M : (rightModuleCategory.{w} C).K) (X : C.Obj) (a b : ℤ) :
    (cochainComplexShiftIso M X (a + b)).hom ≫
        (CategoryTheory.shiftFunctorAdd (CochainComplex (ModuleCat.{w} R) ℤ) a b).hom.app
          (M.cochainComplex X) =
      (eqToHom (congrArg (fun N : RightModule.{w} C => N.cochainComplex X)
            (rightModuleShiftFunctor_obj_add a b M)) ≫
          (cochainComplexShiftIso ((rightModuleShiftFunctor.{w} C a).obj M) X b).hom) ≫
        (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{w} R) ℤ) b).map
          (cochainComplexShiftIso M X a).hom := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, HomologicalComplex.comp_f,
    cochainComplexShiftIso_hom_f, cochainComplexShiftIso_hom_f]
  refine (Category.id_comp _).trans ?_
  rw [CochainComplex.shiftFunctorAdd_hom_app_f, HomologicalComplex.eqToHom_f]
  refine Eq.trans ?_ (Category.comp_id _).symm
  rfl


/-! ### The shift comparison on the homotopy categories -/

/-- Evaluation at `X` commutes with the shift of a closed degree-zero morphism, up to the
identifications `DGCategory.RightModule.cochainComplexShiftIso`. -/
theorem cochainMap_mapCocycle_comm {M N : RightModule.{w} C}
    (φ : (rightModuleCategory.{w} C).Cocycle M N) (X : C.Obj) (n : ℤ) :
    cochainMap ((rightModuleShiftFunctor.{w} C n).mapCocycle φ) X ≫
        (cochainComplexShiftIso N X n).hom =
      (cochainComplexShiftIso M X n).hom ≫
        (CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{w} R) ℤ) n).map
          (cochainMap φ X) := by
  refine HomologicalComplex.hom_ext _ _ (fun i => ?_)
  have hf : (cochainMap ((rightModuleShiftFunctor.{w} C n).mapCocycle φ) X).f i =
      ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{w} R) ℤ) n).map
        (cochainMap φ X)).f i := by
    ext a
    change (-1 : R) ^ (n * 0).natAbs • app φ.1 (show i + n + 0 = i + n by omega) a =
      app φ.1 (add_zero (i + n)) a
    rw [mul_zero, Int.natAbs_zero, pow_zero, one_smul]
  rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, cochainComplexShiftIso_hom_f,
    cochainComplexShiftIso_hom_f]
  exact (Category.comp_id _).trans (hf.trans (Category.id_comp _).symm)

/-- The shift comparison for evaluation at `X` on the homotopy categories, at one module. -/
noncomputable def cochainComplexOnKShiftIsoApp (X : C.Obj) (n : ℤ)
    (M : (rightModuleCategory.{w} C).K) :
    (CategoryTheory.shiftFunctor (rightModuleCategory.{w} C).K n ⋙
        cochainComplexOnK.{w} X).obj M ≅
      (cochainComplexOnK.{w} X ⋙ CategoryTheory.shiftFunctor
        (HomotopyCategory (ModuleCat.{w} R) (ComplexShape.up ℤ)) n).obj M :=
  (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).mapIso
      (cochainComplexShiftIso M X n) ≪≫
    ((HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).commShiftIso n).app
      (M.cochainComplex X)

/-- The forward map of `DGCategory.RightModule.cochainComplexOnKShiftIsoApp` is the class of
`DGCategory.RightModule.cochainComplexShiftIso` followed by the quotient functor's commutation
with the shift. -/
theorem cochainComplexOnKShiftIsoApp_hom (X : C.Obj) (n : ℤ)
    (M : (rightModuleCategory.{w} C).K) :
    (cochainComplexOnKShiftIsoApp X n M).hom =
      (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
          (cochainComplexShiftIso M X n).hom ≫
        ((HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).commShiftIso n).hom.app
          (M.cochainComplex X) := rfl

/-- The comparisons `DGCategory.RightModule.cochainComplexOnKShiftIsoApp` are natural with respect
to the class of a closed degree-zero morphism `φ : M ⟶ N`. -/
theorem cochainComplexOnKShiftIso_naturality (X : C.Obj) (n : ℤ)
    {M N : (rightModuleCategory.{w} C).K} (φ : (rightModuleCategory.{w} C).Cocycle M N) :
    (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
          (cochainMap ((rightModuleShiftFunctor.{w} C n).mapCocycle φ) X) ≫
        ((HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
            (cochainComplexShiftIso N X n).hom ≫
          ((HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).commShiftIso n).hom.app
            (N.cochainComplex X)) =
      ((HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
            (cochainComplexShiftIso M X n).hom ≫
          ((HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).commShiftIso n).hom.app
            (M.cochainComplex X)) ≫
        (CategoryTheory.shiftFunctor (HomotopyCategory (ModuleCat.{w} R) (ComplexShape.up ℤ))
            n).map
          ((HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
            (cochainMap φ X)) := by
  have hnat := ((HomotopyCategory.quotient (ModuleCat.{w} R)
    (ComplexShape.up ℤ)).commShiftIso n).hom.naturality (cochainMap φ X)
  rw [Functor.comp_map, Functor.comp_map] at hnat
  rw [← Category.assoc, ← Functor.map_comp, cochainMap_mapCocycle_comm, Functor.map_comp,
    Category.assoc, hnat, Category.assoc]

/-- **Evaluation at `X` commutes with the translations of the homotopy categories.** -/
noncomputable def cochainComplexOnKCommShiftIso (X : C.Obj) (n : ℤ) :
    CategoryTheory.shiftFunctor (rightModuleCategory.{w} C).K n ⋙ cochainComplexOnK.{w} X ≅
      cochainComplexOnK.{w} X ⋙ CategoryTheory.shiftFunctor
        (HomotopyCategory (ModuleCat.{w} R) (ComplexShape.up ℤ)) n :=
  NatIso.ofComponents (cochainComplexOnKShiftIsoApp X n) (by
    intro M N f
    induction f using Quotient.inductionOn with
    | _ φ => exact cochainComplexOnKShiftIso_naturality X n φ)

/-- The component of `DGCategory.RightModule.cochainComplexOnKCommShiftIso X n` at `M` is
`DGCategory.RightModule.cochainComplexOnKShiftIsoApp X n M`. -/
theorem cochainComplexOnKCommShiftIso_hom_app (X : C.Obj) (n : ℤ)
    (M : (rightModuleCategory.{w} C).K) :
    (cochainComplexOnKCommShiftIso X n).hom.app M = (cochainComplexOnKShiftIsoApp X n M).hom :=
  rfl

/-! ### The two coherences -/

/-- Evaluation at `X` sends the component at `M` of `shiftFunctorZero` of `K(Mod^dg(C))` to the
class of the transport along `M⟦0⟧ = M`. -/
theorem cochainComplexOnK_map_shiftFunctorZero_hom_app (X : C.Obj)
    (M : (rightModuleCategory.{w} C).K) :
    (cochainComplexOnK.{w} X).map
        ((CategoryTheory.shiftFunctorZero (rightModuleCategory.{w} C).K ℤ).hom.app M) =
      (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
        (eqToHom (congrArg (fun N : RightModule.{w} C => N.cochainComplex X)
          (RightModule.shift_zero M))) := by
  rw [shiftFunctorZero_rightModuleHomotopyCategory, eqToIso.hom, eqToHom_app, eqToHom_map]
  exact eqToHom_map _ _

/-- Evaluation at `X` sends the component at `M` of `shiftFunctorAdd a b` of `K(Mod^dg(C))` to
the class of the transport along `M⟦a + b⟧ = (M⟦a⟧)⟦b⟧`. -/
theorem cochainComplexOnK_map_shiftFunctorAdd_hom_app (X : C.Obj) (a b : ℤ)
    (M : (rightModuleCategory.{w} C).K) :
    (cochainComplexOnK.{w} X).map
        ((CategoryTheory.shiftFunctorAdd (rightModuleCategory.{w} C).K a b).hom.app M) =
      (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
        (eqToHom (congrArg (fun N : RightModule.{w} C => N.cochainComplex X)
          (rightModuleShiftFunctor_obj_add a b M))) := by
  rw [shiftFunctorAdd_rightModuleHomotopyCategory, eqToIso.hom, eqToHom_app, eqToHom_map]
  exact eqToHom_map _ _

/-- The identity `DGCategory.RightModule.cochainComplexShiftIso_add`, read in the homotopy
category of complexes of `R`-modules. -/
@[reassoc]
theorem cochainComplexOnK_map_shiftIso_add (M : (rightModuleCategory.{w} C).K) (X : C.Obj)
    (a b : ℤ) :
    (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
          (cochainComplexShiftIso M X (a + b)).hom ≫
        (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
          ((CategoryTheory.shiftFunctorAdd (CochainComplex (ModuleCat.{w} R) ℤ) a b).hom.app
            (M.cochainComplex X)) =
      (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
          (eqToHom (congrArg (fun N : RightModule.{w} C => N.cochainComplex X)
            (rightModuleShiftFunctor_obj_add a b M))) ≫
        (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
            (cochainComplexShiftIso ((rightModuleShiftFunctor.{w} C a).obj M) X b).hom ≫
          (HomotopyCategory.quotient (ModuleCat.{w} R) (ComplexShape.up ℤ)).map
            ((CategoryTheory.shiftFunctor (CochainComplex (ModuleCat.{w} R) ℤ) b).map
              (cochainComplexShiftIso M X a).hom) := by
  rw [← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, cochainComplexShiftIso_add,
    Category.assoc]

/-- **Evaluation at `X` on the homotopy categories commutes with the translations.** -/
noncomputable instance cochainComplexOnK_commShift (X : C.Obj) :
    (cochainComplexOnK.{w} X).CommShift ℤ where
  commShiftIso := cochainComplexOnKCommShiftIso X
  commShiftIso_zero := by
    refine Iso.ext (NatTrans.ext (funext fun M => ?_))
    rw [cochainComplexOnKCommShiftIso_hom_app, Functor.CommShift.isoZero_hom_app,
      cochainComplexOnKShiftIsoApp_hom, cochainComplexOnK_map_shiftFunctorZero_hom_app,
      Functor.commShiftIso_zero, Functor.CommShift.isoZero_hom_app, ← Category.assoc,
      ← Functor.map_comp, cochainComplexShiftIso_zero]
    rfl
  commShiftIso_add a b := by
    refine Iso.ext (NatTrans.ext (funext fun M => ?_))
    have hnat := reassoc_of% (((HomotopyCategory.quotient (ModuleCat.{w} R)
      (ComplexShape.up ℤ)).commShiftIso b).hom.naturality (cochainComplexShiftIso M X a).hom)
    simp only [cochainComplexOnKCommShiftIso_hom_app, cochainComplexOnKShiftIsoApp_hom,
      Functor.CommShift.isoAdd_hom_app,
      Functor.commShiftIso_add, Functor.map_comp, Category.assoc,
      shiftFunctor_rightModuleHomotopyCategory_obj, cochainComplexOnK_obj, Functor.comp_obj,
      cochainComplexOnK_map_shiftIso_add_assoc, hnat]
    refine Eq.symm (congrArg (fun f => f ≫ _) ?_)
    exact cochainComplexOnK_map_shiftFunctorAdd_hom_app X a b M

/-- The comparison isomorphism of the `CategoryTheory.Functor.CommShift` instance of evaluation at
`X` is `DGCategory.RightModule.cochainComplexOnKCommShiftIso`. -/
theorem cochainComplexOnK_commShiftIso (X : C.Obj) (n : ℤ) :
    (cochainComplexOnK.{w} X).commShiftIso n = cochainComplexOnKCommShiftIso X n := rfl

/-! ### The two spellings of the connecting map -/

section Connecting

attribute [local implicit_reducible] rightModuleShiftAxiomB cochainComplexOnK

variable {x y z : RightModule.{v} C}
  (E : GradedSplitShortExact (A := rightModuleCategory.{v} C) x y z) (X : C.Obj)

/-- **The connecting cocycle of an admissible short exact sequence, read at `X` in degree `p`.**
Its value on `a` is `π` applied to the differential of `s a`: the identification of axiom (B)
is used in degree `0`, where it is the morphism itself, and of the two terms of the Hom-complex
differential `d(s) = d_y ∘ s - (-1)^0 s ∘ d_z` the second is killed by `π ∘ s = 0`. -/
theorem app_connectingCocycle (p : ℤ) (a : z.obj X p) :
    app (GradedSplitShortExact.connectingCocycle (rightModuleShiftAxiomB.{v} C) E).1
        (add_zero p) a =
      app E.π (add_zero (p + 1)) (y.d (rfl : p + 1 = p + 1) (app E.s (add_zero p) a)) := by
  have hzero : app E.π (add_zero (p + 1)) (app E.s (add_zero (p + 1)) (z.d rfl a)) = 0 :=
    (app_comp_eq E.π_s (p + 1) (z.d rfl a)).trans (zero_app _ _)
  change app (toShiftHom 1 (GradedSplitShortExact.connectingHom E)) (add_zero p) a = _
  rw [app_toShiftHom]
  change app (homComp (show (0 : ℤ) + (0 + 1) = 0 + 1 by omega) E.π (homD E.s)) _ a = _
  rw [app_homComp, app_homD, Int.natAbs_zero, pow_zero, one_smul, app_sub, hzero, sub_zero,
    d_app E.s (add_zero p) (rfl : p + 1 = p + 1) (show p + 0 + 1 = p + 1 by omega) a]

/-- Mathlib's connecting map of the evaluated sequence, in degree `p`: the splitting's section,
the differential, and the splitting's retraction. -/
theorem homOfDegreewiseSplit_f_eq (p : ℤ) :
    (CochainComplex.homOfDegreewiseSplit (gradedSplitShortComplex E X)
        (gradedSplitSplitting E X)).f p =
      cochainMapComponent E.s X p ≫
        (y.cochainComplex X).d p (p + 1) ≫ cochainMapComponent E.π X (p + 1) := by
  rw [CochainComplex.homOfDegreewiseSplit_f]
  rfl

/-- **The two spellings of the connecting map of an admissible short exact sequence agree.**
The connecting cocycle of axiom (B), read at `X` and moved into Mathlib's shift of the evaluated
complex, is Mathlib's connecting map of the degreewise split sequence that `E` becomes at `X`.
In degree `p` both sides send `a` to `π(d_y(s a))`; see this file's module documentation for the
audit of the signs the two transports carry. -/
theorem cochainMap_connectingCocycle_comp_shiftIso :
    cochainMap (GradedSplitShortExact.connectingCocycle (rightModuleShiftAxiomB.{v} C) E) X ≫
        (cochainComplexShiftIso x X 1).hom =
      CochainComplex.homOfDegreewiseSplit (gradedSplitShortComplex E X)
        (gradedSplitSplitting E X) := by
  refine HomologicalComplex.hom_ext _ _ (fun p => ?_)
  rw [HomologicalComplex.comp_f, cochainComplexShiftIso_hom_f, cochainMap_f,
    homOfDegreewiseSplit_f_eq]
  refine (Category.comp_id _).trans ?_
  ext a
  simp only [cochainComplex_d y X (rfl : p + 1 = p + 1), hom_cochainMapComponent]
  exact app_connectingCocycle E X p a

/-- The third arrow of the triangle of an admissible short exact sequence is the class of the
connecting cocycle: the transport that `DGCategory.GradedSplitShortExact.associatedKTriangle`
composes it with is the identity, axiom (B) for `Mod^dg(C)` having
`DGCategory.ShiftAxiomB.kShift_functor` by reflexivity. -/
theorem associatedKTriangle_mor₃ :
    (GradedSplitShortExact.associatedKTriangle (rightModuleShiftAxiomB.{v} C) E).mor₃ =
      Quotient.mk _ (GradedSplitShortExact.connectingCocycle (rightModuleShiftAxiomB.{v} C) E) :=
  Category.comp_id _

/-- The previous identity, read in the homotopy category of complexes of `R`-modules. -/
@[reassoc]
theorem quotient_map_homOfDegreewiseSplit :
    (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map
          (cochainMap
            (GradedSplitShortExact.connectingCocycle (rightModuleShiftAxiomB.{v} C) E) X) ≫
        (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map
          (cochainComplexShiftIso x X 1).hom =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map
        (CochainComplex.homOfDegreewiseSplit (gradedSplitShortComplex E X)
          (gradedSplitSplitting E X)) := by
  rw [← Functor.map_comp, cochainMap_connectingCocycle_comp_shiftIso]
  rfl

/-- The same, with the quotient functor's own commutation with the shift appended: this is the
third arrow of the evaluated triangle, in the form the two triangles share. -/
@[reassoc]
theorem quotient_map_connecting_comp_commShiftIso :
    (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map
          (cochainMap
            (GradedSplitShortExact.connectingCocycle (rightModuleShiftAxiomB.{v} C) E) X) ≫
        ((HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map
            (cochainComplexShiftIso x X 1).hom ≫
          ((HomotopyCategory.quotient (ModuleCat.{v} R)
            (ComplexShape.up ℤ)).commShiftIso 1).hom.app (x.cochainComplex X)) =
      (HomotopyCategory.quotient (ModuleCat.{v} R) (ComplexShape.up ℤ)).map
          (CochainComplex.homOfDegreewiseSplit (gradedSplitShortComplex E X)
            (gradedSplitSplitting E X)) ≫
        ((HomotopyCategory.quotient (ModuleCat.{v} R)
          (ComplexShape.up ℤ)).commShiftIso 1).hom.app (x.cochainComplex X) := by
  rw [← Category.assoc, quotient_map_homOfDegreewiseSplit]
  rfl

/-- **The third arrows of the two triangles agree.** -/
theorem mapTriangle_associatedKTriangle_mor₃ :
    ((cochainComplexOnK.{v} X).mapTriangle.obj
        (GradedSplitShortExact.associatedKTriangle (rightModuleShiftAxiomB.{v} C) E)).mor₃ =
      (CochainComplex.trianglehOfDegreewiseSplit (gradedSplitShortComplex E X)
        (gradedSplitSplitting E X)).mor₃ :=
  (congrArg (fun g => (cochainComplexOnK.{v} X).map g ≫
      ((cochainComplexOnK.{v} X).commShiftIso 1).hom.app x)
    (associatedKTriangle_mor₃ E)).trans (quotient_map_connecting_comp_commShiftIso E X)

/-- **The triangle of an admissible short exact sequence, carried over by evaluation at `X`, is
Mathlib's triangle of the degreewise split sequence it becomes.** The first two arrows are
literally the same morphisms and the third ones agree, so the two triangles are equal. -/
theorem mapTriangle_associatedKTriangle :
    (cochainComplexOnK.{v} X).mapTriangle.obj
        (GradedSplitShortExact.associatedKTriangle (rightModuleShiftAxiomB.{v} C) E) =
      CochainComplex.trianglehOfDegreewiseSplit (gradedSplitShortComplex E X)
        (gradedSplitSplitting E X) :=
  congrArg (fun f => Pretriangulated.Triangle.mk _ _ f)
    (mapTriangle_associatedKTriangle_mor₃ E X)

end Connecting

/-! ### Evaluation at an object is exact -/

attribute [local implicit_reducible] rightModuleShiftAxiomB cochainComplexOnK

/-- **Evaluation at `X` on the homotopy categories is exact.** -/
instance cochainComplexOnK_isTriangulated (X : C.Obj) :
    (cochainComplexOnK.{v} X).IsTriangulated where
  map_distinguished T hT := by
    rw [distinguishedTriangles_rightModuleHomotopyCategory] at hT
    obtain ⟨x, y, z, E, ⟨e⟩⟩ := hT
    have hd : (cochainComplexOnK.{v} X).mapTriangle.obj
        (GradedSplitShortExact.associatedKTriangle (rightModuleShiftAxiomB.{v} C) E) ∈
        distTriang (HomotopyCategory (ModuleCat.{v} R) (ComplexShape.up ℤ)) := by
      rw [mapTriangle_associatedKTriangle E X]
      exact CochainComplex.trianglehOfDegreewiseSplit_distinguished _ _
    exact Pretriangulated.isomorphic_distinguished _ hd _
      ((cochainComplexOnK.{v} X).mapTriangle.mapIso e)

/-! ### The descent to the derived categories -/

section Derived

universe w'

variable (C) (X : C.Obj) [HasDerivedCategory.{w'} (ModuleCat.{v} R)]

/-- Evaluation at `X` on the derived categories is a lifting, along the localization
`DGCategory.RightModule.derivedQ`, of evaluation at `X` followed by the localization of complexes
of `R`-modules. -/
noncomputable instance liftingDerivedEvaluationForget :
    Localization.Lifting (derivedQ C) (acyclicProperty C).trW
      (cochainComplexToDerived C X) (derivedEvaluationForget C X) :=
  Localization.liftingLift (cochainComplexToDerived C X)
    (trW_isInvertedBy_cochainComplexOnK_comp_Qh C X) (derivedQ C)

/-- **Evaluation at `X` on the derived categories commutes with the translations.** -/
noncomputable instance derivedEvaluationForget_commShift :
    (derivedEvaluationForget C X).CommShift ℤ :=
  Functor.commShiftOfLocalization (derivedQ C) (acyclicProperty C).trW ℤ
    (cochainComplexToDerived C X) (derivedEvaluationForget C X)

/-- Evaluation at `X` followed by the localization of complexes of `R`-modules is exact, being
a composite of exact functors. -/
instance cochainComplexToDerived_isTriangulated :
    (cochainComplexToDerived C X).IsTriangulated :=
  inferInstance

/-- **Evaluation at `X` on the derived categories is exact.** -/
instance derivedEvaluationForget_isTriangulated :
    (derivedEvaluationForget C X).IsTriangulated :=
  haveI := Localization.essSurj_mapArrow (derivedQ C) (acyclicProperty C).trW
  Functor.isTriangulated_of_localization (derivedQ C) (acyclicProperty C).trW
    (cochainComplexToDerived C X) (derivedEvaluationForget C X)

end Derived

end RightModule

/-- **The forgetful functor `U : D(C(K, K)) ⥤ D(ModuleCat R)` commutes with the
translations.** -/
@[instance_reducible]
noncomputable def endDerivedForgetCommShift {R : Type r} [CommRing R] (C : DGCategory.{v, u} R)
    (K : C.Obj) [HasDerivedCategory.{w} (ModuleCat.{v} R)] :
    (endDerivedForget C K).CommShift ℤ :=
  inferInstanceAs
    ((RightModule.derivedEvaluationForget (endDGCategory C K) PUnit.unit).CommShift ℤ)

/-- **The forgetful functor `U : D(C(K, K)) ⥤ D(ModuleCat R)` is exact**, for the translation
of `DGCategory.endDerivedForgetCommShift`. -/
theorem endDerivedForget_isTriangulated {R : Type r} [CommRing R] (C : DGCategory.{v, u} R)
    (K : C.Obj) [HasDerivedCategory.{w} (ModuleCat.{v} R)] :
    letI := endDerivedForgetCommShift C K
    (endDerivedForget C K).IsTriangulated :=
  let := endDerivedForgetCommShift C K
  inferInstanceAs
    ((RightModule.derivedEvaluationForget (endDGCategory C K) PUnit.unit).IsTriangulated)

/-! ### The composite `R̃ ⋙ U` of step 3 -/

section PhiForget

universe vA wZ

variable (A : Type) [Category.{0} A] [Abelian A] [HasDerivedCategory.{vA} A]
  (K : CochainComplex A ℤ) [HasDerivedCategory.{wZ} (ModuleCat.{0} ℤ)]
  [((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).CommShift ℤ]
  [((yonedaDGFunctor (CochainComplex.dgCategory A)).onK).IsTriangulated]
  (L : (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K ⥤
    (rightModuleCategory.{0} (CochainComplex.dgCategory A)).K)
  [L.CommShift ℤ] [L.IsTriangulated]
  (hΦ : ∀ X, RightModule.yonedaInverseImage (CochainComplex.dgCategory A) (phiGen A) X →
    IsZero (((yonedaDGFunctor (CochainComplex.dgCategory A)).onK ⋙ L).obj X))

/-- **`R̃ ⋙ U : D(A) ⥤ D(Ab)` commutes with the translations.** On the first factor this is
`DGCategory.phiReflectorCommShift`, which step 2 supplies; on the second it is
`DGCategory.endDerivedForgetCommShift`.

A definition rather than an instance, for the same reason as
`DGCategory.phiReflectorCommShift`: `CategoryTheory.Functor.CommShift` is data, and the two
factors' structures already determine this one. -/
@[instance_reducible]
noncomputable def phiReflectorForgetCommShift :
    (phiReflectorForget A K L hΦ).CommShift ℤ :=
  letI := phiReflectorCommShift A K L hΦ
  letI := endDerivedForgetCommShift (CochainComplex.dgCategory A) K
  inferInstanceAs ((phiReflector A K L hΦ ⋙
    endDerivedForget (CochainComplex.dgCategory A) K).CommShift ℤ)

/-- **`R̃ ⋙ U : D(A) ⥤ D(Ab)` is exact**, for the translation of
`DGCategory.phiReflectorForgetCommShift`. On the first factor this is
`DGCategory.phiReflector_isTriangulated`, which step 2 supplies; on the second it is
`DGCategory.endDerivedForget_isTriangulated`. -/
theorem phiReflectorForget_isTriangulated :
    letI := phiReflectorForgetCommShift A K L hΦ
    (phiReflectorForget A K L hΦ).IsTriangulated :=
  let := phiReflectorCommShift A K L hΦ
  let := endDerivedForgetCommShift (CochainComplex.dgCategory A) K
  have := endDerivedForget_isTriangulated (CochainComplex.dgCategory A) K
  inferInstanceAs ((phiReflector A K L hΦ ⋙
    endDerivedForget (CochainComplex.dgCategory A) K).IsTriangulated)

end PhiForget

end DGCategory

end
