module

public import StacksFrontier.Deformation.RingedSpaceThickening.CompatibleMorphismGluing
public import StacksFrontier.Algebra.Homology.DoubleMapFunctor
public import StacksFrontier.Algebra.Homology.DoubleMappingConeNaturality
public import StacksFrontier.Deformation.RingedSpaceThickening.ExtensionPresentationClass

/-!
# The two-term complex `N` and its maps to `g^*𝖭𝖫(α_X)` and `𝖭𝖫(α_Y)`

In the setting of `StacksFrontier/Deformation/RingedSpaceThickening/CompatibleMorphismGluing.lean`,
the termwise fibre product `N = g^*𝖭𝖫(α_X) ×_{𝖭𝖫_{Y/S}} 𝖭𝖫(α_Y)` is a two-term complex with
projections to `g^*𝖭𝖫(α_X)` and to `𝖭𝖫(α_Y)`; the two composites to `𝖭𝖫_{Y/S}` agree, and
in the derived category the projection to `𝖭𝖫(α_Y)` carries the class of a homomorphism
`δ : 𝒥_β/𝒥_β² ⟶ 𝒢` to the class of `δ` after the projection.

## Main definitions

* `AlgebraicGeometry.RingedSpaceThickening.LiftGluing.pullX`: the canonical map
  `g^*𝖭𝖫(α_X) ⟶ 𝖭𝖫_{Y/S}`.
* `AlgebraicGeometry.RingedSpaceThickening.LiftGluing.complexN`, `fstN`, `sndN`: the complex `N`
  and its two projections.

## Main results

* `LiftGluing.pullX_eq`: `pullX` is the pullback of the comparison `𝖭𝖫(α_X) ⟶ 𝖭𝖫_{X/S}` followed
  by the canonical map `g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`.
* `LiftGluing.fstN_comp_pullX`: the two composites `N ⟶ 𝖭𝖫_{Y/S}` agree.
* `LiftGluing.Q_map_sndN_comp_conormalExtClass`: the projection to `𝖭𝖫(α_Y)` on classes.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction HomologicalComplex
open AlgebraicGeometry.RingedSpaceThickening.CompatibleMorphism (comparisonX comparisonY)

universe u v w

namespace AlgebraicGeometry.RingedSpaceThickening.LiftGluing

variable {X S Y : RingedSpace.{u, u}} {f : X ⟶ S} (g : Y ⟶ X)
  {F : SheafOfModules.{u} (structureSheafRing X)} {G : SheafOfModules.{u} (structureSheafRing Y)}
  (P : SquareZeroAlgebraExtension f F) (Q : SquareZeroAlgebraExtension (g ≫ f) G)

/-- The transpose of a chain map along `F ⊣ G` applied degreewise is, in each degree, the
transpose of the component. -/
theorem mapHomologicalComplex_homEquiv_symm_f {A B : Type*} [Category A] [Abelian A] [Category B]
    [Abelian B] {L : A ⥤ B} {R : B ⥤ A} [L.Additive] [R.Additive] (adj : L ⊣ R)
    {K : CochainComplex A ℤ} {M : CochainComplex B ℤ}
    (φ : K ⟶ (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) (i : ℤ) :
    (((adj.mapHomologicalComplex (ComplexShape.up ℤ)).homEquiv K M).symm φ).f i =
      (adj.homEquiv _ _).symm (φ.f i) := by
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  rfl

/-- `𝖭𝖫(α_X)`, in the spelling of sheaves of modules over the structure sheaf. -/
abbrev KX : CochainComplex (SheafOfModules.{u} (structureSheafRing X)) ℤ :=
  double (dX P) ComplexShape.upIntRelNegOneZero

/-- `𝖭𝖫(α_Y)`, in the spelling of sheaves of modules over the structure sheaf. -/
abbrev KY : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ :=
  double (dβ g Q) ComplexShape.upIntRelNegOneZero

/-- `𝖭𝖫_{Y/S}`, in the spelling of sheaves of modules over the structure sheaf. -/
abbrev NLY (f : X ⟶ S) : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ :=
  PresentedSquareZeroExtension.relativeComplex (g ≫ f)

/-- The chain map `𝖭𝖫(α_X) ⟶ g_*𝖭𝖫_{Y/S}` of the presentation of `𝒪_X` by `𝒪_{X'}` along `g`. -/
def pushX : KX P ⟶ ((modulePushforward g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (NLY g f) :=
  Stacks.SheafOfModules.presentationNaiveCotangentPushMap g.hom.base
    (structureRingMap_comp_structureComorphism g f) (εX_comp g P)

/-- **The canonical map `g^*𝖭𝖫(α_X) ⟶ 𝖭𝖫_{Y/S}`**: the transpose of `pushX`. -/
def pullX : ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (KX P) ⟶ NLY g f :=
  ((Adjunction.mapHomologicalComplex (modulePullbackPushforwardAdjunction g)
    (ComplexShape.up ℤ)).homEquiv _ _).symm (pushX g P)

/-- The comparison `𝖭𝖫(α_X) ⟶ 𝖭𝖫_{X/S}`, with source written as `double d_X`. -/
def compX : KX P ⟶ PresentedSquareZeroExtension.relativeComplex f := comparisonX P

/-- `pushX` is the comparison `𝖭𝖫(α_X) ⟶ 𝖭𝖫_{X/S}` followed by the canonical map along `g`. -/
theorem pushX_eq : pushX g P = compX P ≫ naiveCotangentPushMap g f := by
  have h := Stacks.SheafOfModules.presentationNaiveCotangentPushMap_naturality g.hom.base
    P.generatorsMap (𝟙 (Y.sheaf.obj ⋙ forget CommRingCat)) (Category.comp_id _)
    (Category.comp_id _) (Category.id_comp _) (structureRingMap_comp_structureComorphism g f)
    (εX_comp g P) (underlyingPresheafMap_comp g)
  have hid := Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_id.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f)) (Y.sheaf.obj ⋙ forget CommRingCat) (𝟙 _)
  rw [hid, CategoryTheory.Functor.map_id, Category.comp_id] at h
  unfold pushX compX
  exact h

/-- **`pullX` is the pullback of the comparison followed by the canonical map**
`g^*𝖭𝖫_{X/S} ⟶ 𝖭𝖫_{Y/S}`. -/
theorem pullX_eq : pullX g P = ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).map
    (compX P) ≫ pullbackNaiveCotangentMap g f := by
  apply ((Adjunction.mapHomologicalComplex (modulePullbackPushforwardAdjunction g)
    (ComplexShape.up ℤ)).homEquiv _ _).injective
  refine (((Adjunction.mapHomologicalComplex (modulePullbackPushforwardAdjunction g)
    (ComplexShape.up ℤ)).homEquiv _ _).apply_symm_apply _).trans ?_
  refine Eq.trans ?_ ((Adjunction.mapHomologicalComplex (modulePullbackPushforwardAdjunction g)
    (ComplexShape.up ℤ)).homEquiv_naturality_left _ _).symm
  refine (pushX_eq g P).trans ?_
  exact congrArg (compX P ≫ ·) (((Adjunction.mapHomologicalComplex
    (modulePullbackPushforwardAdjunction g) (ComplexShape.up ℤ)).homEquiv _ _).apply_symm_apply
      (naiveCotangentPushMap g f)).symm

/-- `𝖭𝖫(α_X)` in degree `-1`. -/
theorem KX_X_negOne : (KX P).X (-1) =
    cX P :=
  Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
    P.generators P.generatorsMap

/-- `𝖭𝖫(α_X)` in degree `0`. -/
theorem KX_X_zero : (KX P).X 0 =
    bX P :=
  Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
    (Opens.grothendieckTopology X.carrier) (inverseImageBaseRing f) X.sheaf (structureRingMap f)
    P.generators P.generatorsMap

/-- `𝖭𝖫(α_Y)` in degree `-1`. -/
theorem KY_X_negOne : (KY g Q).X (-1) =
    cβ g Q :=
  Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f)) Q.generators Q.generatorsMap

/-- `𝖭𝖫(α_Y)` in degree `0`. -/
theorem KY_X_zero : (KY g Q).X 0 =
    bβ g Q :=
  Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f)) Q.generators Q.generatorsMap

/-- `𝖭𝖫_{Y/S}` in degree `-1`. -/
theorem NLY_X_negOne : (NLY g f).X (-1) =
    cY f g :=
  Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_negOne.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f)) (Y.sheaf.obj ⋙ forget CommRingCat) (𝟙 _)

/-- `𝖭𝖫_{Y/S}` in degree `0`. -/
theorem NLY_X_zero : (NLY g f).X 0 =
    bY f g :=
  Stacks.SheafOfModules.presentationNaiveCotangentComplex_X_zero.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Y.sheaf
    (structureRingMap (g ≫ f)) (Y.sheaf.obj ⋙ forget CommRingCat) (𝟙 _)

/-- The transpose of `pushX` in degree `i`, when `pushX` factors there as `a ≫ b ≫ g_* c`. -/
private theorem pullX_f_eq_of_pushX_f {i : ℤ} {A : SheafOfModules.{u} (structureSheafRing X)}
    {B : SheafOfModules.{u} (structureSheafRing Y)} (a : (KX P).X i ⟶ A)
    (b : A ⟶ (modulePushforward g).obj B) (c : B ⟶ (NLY g f).X i)
    (h : (pushX g P).f i = a ≫ b ≫ (modulePushforward g).map c) :
    (pullX g P).f i = (modulePullback g).map a ≫
      ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm b ≫ c := by
  refine (mapHomologicalComplex_homEquiv_symm_f _ _ _).trans ?_
  refine (congrArg ((modulePullbackPushforwardAdjunction g).homEquiv _ _).symm h).trans ?_
  refine ((modulePullbackPushforwardAdjunction g).homEquiv_naturality_left_symm _ _).trans ?_
  exact congrArg (_ ≫ ·) ((modulePullbackPushforwardAdjunction g).homEquiv_naturality_right_symm
    _ _)

/-- `pullX` in degree `-1` is `ψ₀`. -/
theorem pullX_f_negOne : (pullX g P).f (-1) =
    (modulePullback g).map (doubleXIso₀ (dX P) ComplexShape.upIntRelNegOneZero).hom ≫ ψ₀ g P ≫
      eqToHom (NLY_X_negOne (f := f) g).symm := by
  have h := Stacks.SheafOfModules.presentationNaiveCotangentPushMap_f_negOne g.hom.base
    (structureRingMap_comp_structureComorphism g f) (εX_comp g P)
  exact pullX_f_eq_of_pushX_f g P _ _ _ h

/-- `pullX` in degree `0` is `ψ₁`. -/
theorem pullX_f_zero : (pullX g P).f (0) =
    (modulePullback g).map (doubleXIso₁ (dX P) ComplexShape.upIntRelNegOneZero (by decide)).hom ≫
      ψ₁ g P ≫ eqToHom (NLY_X_zero (f := f) g).symm := by
  have h := Stacks.SheafOfModules.presentationNaiveCotangentPushMap_f_zero g.hom.base
    (structureRingMap_comp_structureComorphism g f) (εX_comp g P)
  exact pullX_f_eq_of_pushX_f g P _ _ _ h

/-! ### The complex `N` and its projections -/

/-- **The two-term complex `N`**, with `N₀` in degree `-1` and `N₁` in degree `0`. -/
abbrev complexN : CochainComplex (SheafOfModules.{u} (structureSheafRing Y)) ℤ :=
  double (dN g P Q) ComplexShape.upIntRelNegOneZero

/-- The projection `N ⟶ double (g^*d_X)`. -/
def fstN' : complexN g P Q ⟶ double ((modulePullback g).map (dX P))
    ComplexShape.upIntRelNegOneZero :=
  mkHomFromDouble _ (by decide) (pullback.fst _ _ ≫ (doubleXIso₀ _ _).inv)
    (pullback.fst _ _ ≫ (doubleXIso₁ _ _ (by decide)).inv)
    (by
      rw [Category.assoc, doubleXIso₀_inv_comp_double_d _ _ (by decide), ← Category.assoc,
        ← Category.assoc]
      exact congrArg (· ≫ _) (pullback.lift_fst _ _ _).symm)
    (fun k _ ↦ by rw [double_d_eq_zero₀ _ _ _ _ (by decide), comp_zero])

/-- The projection `N ⟶ 𝖭𝖫(α_Y)`. -/
def sndN : complexN g P Q ⟶ KY g Q :=
  mkHomFromDouble _ (by decide) (pullback.snd _ _ ≫ (doubleXIso₀ _ _).inv)
    (pullback.snd _ _ ≫ (doubleXIso₁ _ _ (by decide)).inv)
    (by
      rw [Category.assoc, doubleXIso₀_inv_comp_double_d _ _ (by decide), ← Category.assoc,
        ← Category.assoc]
      exact congrArg (· ≫ _) (pullback.lift_snd _ _ _).symm)
    (fun k _ ↦ by rw [double_d_eq_zero₀ _ _ _ _ (by decide), comp_zero])

/-- The comparison `𝖭𝖫(α_Y) ⟶ 𝖭𝖫_{Y/S}`, with source written as `double d_β`. -/
def compY : KY g Q ⟶ NLY g f :=
  comparisonY Q

/-- `compY` in degree `-1` is `ιβ₀`. -/
theorem compY_f_negOne : (compY g Q).f (-1) =
    (doubleXIso₀ (dβ g Q) ComplexShape.upIntRelNegOneZero).hom ≫ ιβ₀ g Q ≫
      eqToHom (NLY_X_negOne (f := f) g).symm := by
  have h := Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_f_negOne.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Q.generators
    (Y.sheaf.obj ⋙ forget CommRingCat) Q.generatorsMap Y.sheaf (structureRingMap (g ≫ f))
    Q.generatorsMap (𝟙 _) (Category.comp_id _)
  unfold compY comparisonY Stacks.SheafOfModules.naiveCotangentComplexComparison ιβ₀
  exact h

/-- `compY` in degree `0` is `ιβ₁`. -/
theorem compY_f_zero : (compY g Q).f 0 =
    (doubleXIso₁ (dβ g Q) ComplexShape.upIntRelNegOneZero (by decide)).hom ≫ ιβ₁ g Q ≫
      eqToHom (NLY_X_zero (f := f) g).symm := by
  have h := Stacks.SheafOfModules.presentationNaiveCotangentComplexMap_f_zero.{u, u, u, u}
    (Opens.grothendieckTopology Y.carrier) (inverseImageBaseRing (g ≫ f)) Q.generators
    (Y.sheaf.obj ⋙ forget CommRingCat) Q.generatorsMap Y.sheaf (structureRingMap (g ≫ f))
    Q.generatorsMap (𝟙 _) (Category.comp_id _)
  unfold compY comparisonY Stacks.SheafOfModules.naiveCotangentComplexComparison ιβ₁
  exact h

/-- The identification `double (g^*d_X) ≅ g^*𝖭𝖫(α_X)`. -/
def pullDoubleIso : double ((modulePullback g).map (dX P)) ComplexShape.upIntRelNegOneZero ≅
    ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj (KX P) :=
  doubleMapFunctorIso (modulePullback g) (dX P) ComplexShape.upIntRelNegOneZero (by decide)

/-- The projection `N ⟶ g^*𝖭𝖫(α_X)`. -/
def fstN : complexN g P Q ⟶ ((modulePullback g).mapHomologicalComplex (ComplexShape.up ℤ)).obj
    (KX P) :=
  fstN' g P Q ≫ (pullDoubleIso g P).hom

/-- **The two composites `N ⟶ 𝖭𝖫_{Y/S}` agree.** -/
theorem fstN_comp_pullX : fstN g P Q ≫ pullX g P = sndN g P Q ≫ compY g Q := by
  refine HomologicalComplex.from_double_hom_ext ?_ ?_
  on_goal 1 => rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, fstN,
      HomologicalComplex.comp_f, pullX_f_negOne, fstN', mkHomFromDouble_f₀, pullDoubleIso,
      doubleMapFunctorIso, asIso_hom, doubleMapFunctorHom, mkHomFromDouble_f₀, sndN,
      mkHomFromDouble_f₀, compY_f_negOne]
  on_goal 2 => rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, fstN,
      HomologicalComplex.comp_f, pullX_f_zero, fstN', mkHomFromDouble_f₁, pullDoubleIso,
      doubleMapFunctorIso, asIso_hom, doubleMapFunctorHom, mkHomFromDouble_f₁, sndN,
      mkHomFromDouble_f₁, compY_f_zero]
  all_goals
    rw [Category.assoc, Category.assoc, Category.assoc, Category.assoc, Iso.inv_hom_id_assoc,
      Category.assoc, Category.assoc, Iso.inv_hom_id_assoc, ← Functor.map_comp_assoc,
      Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp,
      ← Category.assoc (pullback.fst _ _), pullback.condition, Category.assoc]

/-! ### The projections on classes -/

section Classes

attribute [local instance] HasDerivedCategory.standard

/-- The class, in `Ext¹` of a `double`-built two-term complex, of a homomorphism out of the degree
`-1` term, after a chain map of `double`s: the class of the homomorphism after the degree `-1`
component. -/
theorem Q_map_comp_conormalExtClass_ofDoubleNegOne {C : Type*} [Category.{v} C] [Abelian C]
    [HasDerivedCategory.{w} C] {X₀ X₁ Y₀ Y₁ : C} {d : X₀ ⟶ X₁} {e : Y₀ ⟶ Y₁} {a₀ : X₀ ⟶ Y₀}
    {a₁ : X₁ ⟶ Y₁}
    (φ : double d ComplexShape.upIntRelNegOneZero ⟶ double e ComplexShape.upIntRelNegOneZero)
    (h₀ : φ.f (-1) = (doubleXIso₀ d _).hom ≫ a₀ ≫ (doubleXIso₀ e _).inv)
    (h₁ : φ.f 0 = (doubleXIso₁ d _ (by decide)).hom ≫ a₁ ≫ (doubleXIso₁ e _ (by decide)).inv)
    (H : C) (δ : Y₀ ⟶ H) :
    DerivedCategory.Q.map φ ≫ (NaiveCotangentTwoTerm.ofDoubleNegOne e).conormalExtClass H δ =
      (NaiveCotangentTwoTerm.ofDoubleNegOne d).conormalExtClass H (a₀ ≫ δ) := by
  have key := CochainComplex.doubleProjQ_naturality d e ComplexShape.upIntRelNegOneZero
    (by decide) a₀ a₁ φ h₀ h₁
  have e3 : ((DerivedCategory.singleFunctor C 0).map a₀)⟦(1 : ℤ)⟧' ≫
      ((DerivedCategory.singleFunctor C 0).map δ)⟦(1 : ℤ)⟧' =
      ((DerivedCategory.singleFunctor C 0).map (a₀ ≫ δ))⟦(1 : ℤ)⟧' :=
    (Functor.map_comp (shiftFunctor _ (1 : ℤ)) _ _).symm.trans
      (congrArg (shiftFunctor _ (1 : ℤ)).map (Functor.map_comp _ _ _).symm)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ ((DerivedCategory.singleFunctor C 0).map δ)⟦(1 : ℤ)⟧') key).trans
      ((Category.assoc _ _ _).trans (congrArg (CochainComplex.doubleProjQ d _ ≫ ·) e3)))

/-- **The projection `N ⟶ 𝖭𝖫(α_Y)` on classes.** -/
theorem Q_map_sndN_comp_conormalExtClass (δ : cβ g Q ⟶ G) :
    DerivedCategory.Q.map (sndN g P Q) ≫
        (NaiveCotangentTwoTerm.ofDoubleNegOne (dβ g Q)).conormalExtClass G δ =
      (NaiveCotangentTwoTerm.ofDoubleNegOne (dN g P Q)).conormalExtClass G
        (pullback.snd _ _ ≫ δ) :=
  Q_map_comp_conormalExtClass_ofDoubleNegOne (sndN g P Q)
    (mkHomFromDouble_f₀ _ _ _ _ _ _) (mkHomFromDouble_f₁ _ _ _ _ _ _) G δ

/-- **The projection `N ⟶ double (g^*d_X)` on classes.** -/
theorem Q_map_fstN'_comp_conormalExtClass (γ : (modulePullback g).obj (cX P) ⟶ G) :
    DerivedCategory.Q.map (fstN' g P Q) ≫
        (NaiveCotangentTwoTerm.ofDoubleNegOne ((modulePullback g).map (dX P))).conormalExtClass
          G γ =
      (NaiveCotangentTwoTerm.ofDoubleNegOne (dN g P Q)).conormalExtClass G
        (pullback.fst _ _ ≫ γ) :=
  Q_map_comp_conormalExtClass_ofDoubleNegOne (fstN' g P Q)
    (mkHomFromDouble_f₀ _ _ _ _ _ _) (mkHomFromDouble_f₁ _ _ _ _ _ _) G γ

end Classes

end AlgebraicGeometry.RingedSpaceThickening.LiftGluing

end
