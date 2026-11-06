module

public import StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactFunctorBoundedBelow

/-!
# Right derived functors on `D⁺` across a square with exact vertical functors

Consider a square of additive functors between abelian categories

```
A  --F-->  B
|U         |V
v          v
A' --F'--> B'
```

commuting up to an isomorphism `e : F ⋙ V ≅ U ⋙ F'`, with `U` and `V` exact and `A`, `A'` with
enough injectives. If `U` carries injective objects to objects right acyclic for `F'`, then the
square of right derived functors on bounded below derived categories commutes too:

`RF ⋙ V ≅ U ⋙ RF'`  as functors  `D⁺(A) ⥤ D⁺(B')`,

where `U` and `V` act degreewise (`CategoryTheory.Functor.mapDerivedCategoryPlus`). This is the
form in which the forgetful functor from sheaves of modules to abelian sheaves, which is exact,
commutes with derived direct images: injective sheaves of modules are acyclic for the direct
image of abelian sheaves although they need not be injective as abelian sheaves.

Both sides are right derived functors of one functor `K⁺(A) ⥤ D⁺(B')`, the degreewise `V ∘ F`
followed by localization, along `Qh : K⁺(A) ⥤ D⁺(A)`: on a bounded below complex `I` of
injectives the unit of `RF` is invertible, and the unit of `RF'` is invertible at `U(I)` by
Leray's acyclicity lemma ([Stacks, Tag 015E]). The isomorphism is the uniqueness of right derived
functors, and it is pinned by its compatibility with the two units
(`rightDerivedFunctorPlusExactSquareIso_fac`).

## Main definitions

* `CategoryTheory.Functor.exactSquarePlusUnitLeft`,
  `CategoryTheory.Functor.exactSquarePlusUnitRight` — the units exhibiting `RF ⋙ V` and
  `U ⋙ RF'` as right derived functors of the degreewise `V ∘ F`.
* `CategoryTheory.Functor.rightDerivedFunctorPlusExactSquareIso` — **`RF ⋙ V ≅ U ⋙ RF'`.**

## Main results

* `CategoryTheory.Functor.rightDerivedFunctorPlusExactSquareIso_fac` — the isomorphism carries
  one unit to the other.

## References

* [Stacks Project, Tag 015E](https://stacks.math.columbia.edu/tag/015E)
* [Stacks Project, Tag 015M](https://stacks.math.columbia.edu/tag/015M)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe wA wA' wB wB' vA vA' vB vB' uA uA' uB uB'

namespace CategoryTheory.Functor

variable {A : Type uA} [Category.{vA} A] [Abelian A] [HasDerivedCategory.{wA} A]
  [EnoughInjectives A]
  {A' : Type uA'} [Category.{vA'} A'] [Abelian A'] [HasDerivedCategory.{wA'} A']
  [EnoughInjectives A']
  {B : Type uB} [Category.{vB} B] [Abelian B] [HasDerivedCategory.{wB} B]
  {B' : Type uB'} [Category.{vB'} B'] [Abelian B'] [HasDerivedCategory.{wB'} B']
  (F : A ⥤ B) (F' : A' ⥤ B') [F.Additive] [F'.Additive]
  (U : A ⥤ A') [U.Additive] [PreservesFiniteLimits U] [PreservesFiniteColimits U]
  (V : B ⥤ B') [V.Additive] [PreservesFiniteLimits V] [PreservesFiniteColimits V]
  (e : F ⋙ V ≅ U ⋙ F')

-- See `StacksFrontier.Algebra.Homology.DerivedCategory.CompositionOfRightDerivedFunctors`: the
-- instance getting pointwise right derivability from `EnoughInjectives` is the cheap one.
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

/-- The unit exhibiting `RF ⋙ V` as a right derived functor of the degreewise `V ∘ F`: the unit
of `RF`, carried by `V`, read through the degreewise description of `V` on `D⁺`. -/
def exactSquarePlusUnitLeft :
    F.mapHomotopyCategoryPlus ⋙ V.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ (F.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus) :=
  Functor.whiskerLeft F.mapHomotopyCategoryPlus V.mapDerivedCategoryPlusFactorsh.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight F.rightDerivedFunctorPlusUnith V.mapDerivedCategoryPlus ≫
    (Functor.associator _ _ _).hom

/-- The unit exhibiting `U ⋙ RF'` as a right derived functor of the degreewise `V ∘ F`: the
square `e` read degreewise, the unit of `RF'` at `U`-images, and the degreewise description of
`U` on `D⁺`. -/
def exactSquarePlusUnitRight :
    F.mapHomotopyCategoryPlus ⋙ V.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh ⟶
      DerivedCategory.Plus.Qh ⋙ (U.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus) :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight
      ((mapHomotopyCategoryPlusCompIso e).hom ≫ (mapHomotopyCategoryPlusCompIso (Iso.refl _)).inv)
      DerivedCategory.Plus.Qh ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft U.mapHomotopyCategoryPlus F'.rightDerivedFunctorPlusUnith ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight U.mapDerivedCategoryPlusFactorsh.inv F'.rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom

omit [HasDerivedCategory A] [EnoughInjectives A] in
/-- Bounded below complexes of injectives, through the localizer morphism of the injective
derivability structure, have injective terms. -/
private lemma injective_localizerMorphism_obj (Y : HomotopyCategory.Plus (InjectiveObject A))
    (n : ℤ) :
    Injective ((((HomotopyCategory.Plus.localizerMorphism A).functor.obj Y).obj.as.X n)) := by
  obtain ⟨Y, hY⟩ := Y
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective Y
  exact (K.X n).property

/-- `RF ⋙ V` is a right derived functor of the degreewise `V ∘ F`, with unit
`exactSquarePlusUnitLeft`. -/
instance isRightDerivedFunctor_exactSquarePlusUnitLeft :
    (F.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus).IsRightDerivedFunctor
      (exactSquarePlusUnitLeft F V) (HomotopyCategory.Plus.quasiIso A) :=
  LocalizerMorphism.Derives.isRightDerivedFunctor_of_isIso
    (HomotopyCategory.Plus.localizerMorphism_derives _) _ (fun Y => by
        have : ∀ n : ℤ, Injective
            (((HomotopyCategory.Plus.localizerMorphism A).functor.obj Y).obj.as.X n) :=
          injective_localizerMorphism_obj Y
        simp only [exactSquarePlusUnitLeft, NatTrans.comp_app, Functor.whiskerLeft_app,
          Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
          Category.comp_id, Category.id_comp]
        infer_instance)

omit [HasDerivedCategory B] [PreservesFiniteLimits V] [PreservesFiniteColimits V] in
variable {F F' U V} in
/-- Under the acyclicity hypothesis, `U ⋙ RF'` is a right derived functor of the degreewise
`V ∘ F`, with unit `exactSquarePlusUnitRight`. -/
theorem isRightDerivedFunctor_exactSquarePlusUnitRight
    (hU : ∀ I : A, Injective I → F'.rightAcyclic (U.obj I)) :
    (U.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus).IsRightDerivedFunctor
      (exactSquarePlusUnitRight F F' U V e) (HomotopyCategory.Plus.quasiIso A) :=
  LocalizerMorphism.Derives.isRightDerivedFunctor_of_isIso
    (HomotopyCategory.Plus.localizerMorphism_derives _) _ (fun Y => by
        have := isIso_rightDerivedFunctorPlusUnit_app_of_rightAcyclic F'
          (U.mapHomotopyCategoryPlus.obj
            ((HomotopyCategory.Plus.localizerMorphism A).functor.obj Y))
          (fun n => hU _ (injective_localizerMorphism_obj Y n))
        simp only [exactSquarePlusUnitRight, NatTrans.comp_app, Functor.whiskerLeft_app,
          Functor.whiskerRight_app, Functor.associator_hom_app, Functor.associator_inv_app,
          Category.comp_id, Category.id_comp]
        infer_instance)

/-- The component of `exactSquarePlusUnitLeft`. -/
theorem exactSquarePlusUnitLeft_app (K : HomotopyCategory.Plus A) :
    (exactSquarePlusUnitLeft F V).app K =
      V.mapDerivedCategoryPlusFactorsh.inv.app (F.mapHomotopyCategoryPlus.obj K) ≫
        V.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app K) := by
  simp [exactSquarePlusUnitLeft]

omit [EnoughInjectives A] [HasDerivedCategory B] [PreservesFiniteLimits V]
  [PreservesFiniteColimits V] in
/-- The component of `exactSquarePlusUnitRight`. -/
theorem exactSquarePlusUnitRight_app (K : HomotopyCategory.Plus A) :
    (exactSquarePlusUnitRight F F' U V e).app K =
      DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusCompIso e).hom.app K ≫
          (mapHomotopyCategoryPlusCompIso (Iso.refl (U ⋙ F'))).inv.app K) ≫
        F'.rightDerivedFunctorPlusUnith.app (U.mapHomotopyCategoryPlus.obj K) ≫
          F'.rightDerivedFunctorPlus.map (U.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  simp only [exactSquarePlusUnitRight, NatTrans.comp_app, Functor.whiskerRight_app,
    Functor.whiskerLeft_app, Functor.associator_hom_app, Functor.associator_inv_app,
    Category.id_comp, Category.comp_id]

variable {F F' U V} in
/-- **The right derived functors on `D⁺` commute across a square with exact vertical functors**,
`RF ⋙ V ≅ U ⋙ RF'`, when `U` carries injective objects to objects right acyclic for `F'`. -/
def rightDerivedFunctorPlusExactSquareIso
    (hU : ∀ I : A, Injective I → F'.rightAcyclic (U.obj I)) :
    F.rightDerivedFunctorPlus ⋙ V.mapDerivedCategoryPlus ≅
      U.mapDerivedCategoryPlus ⋙ F'.rightDerivedFunctorPlus :=
  have := isRightDerivedFunctor_exactSquarePlusUnitRight e hU
  Functor.rightDerivedNatIso _ _ (exactSquarePlusUnitLeft F V)
    (exactSquarePlusUnitRight F F' U V e) (HomotopyCategory.Plus.quasiIso A) (Iso.refl _)

variable {F F' U V} in
/-- **The isomorphism `RF ⋙ V ≅ U ⋙ RF'` carries the unit of the left side to that of the
right side**, which determines it. -/
theorem rightDerivedFunctorPlusExactSquareIso_fac
    (hU : ∀ I : A, Injective I → F'.rightAcyclic (U.obj I)) :
    exactSquarePlusUnitLeft F V ≫
        Functor.whiskerLeft DerivedCategory.Plus.Qh
          (rightDerivedFunctorPlusExactSquareIso e hU).hom =
      exactSquarePlusUnitRight F F' U V e := by
  have := isRightDerivedFunctor_exactSquarePlusUnitRight e hU
  exact (Functor.rightDerivedNatTrans_fac _ _ (exactSquarePlusUnitLeft F V)
    (exactSquarePlusUnitRight F F' U V e) (HomotopyCategory.Plus.quasiIso A)
      (Iso.refl _).hom).trans (Category.id_comp _)

variable {F F' U V} in
/-- **`rightDerivedFunctorPlusExactSquareIso` at the image of a bounded below complex**, read
through the units of `RF` and of `RF'`. -/
theorem rightDerivedFunctorPlusExactSquareIso_hom_app_Qh
    (hU : ∀ I : A, Injective I → F'.rightAcyclic (U.obj I)) (K : HomotopyCategory.Plus A) :
    V.mapDerivedCategoryPlus.map (F.rightDerivedFunctorPlusUnith.app K) ≫
        (rightDerivedFunctorPlusExactSquareIso e hU).hom.app (DerivedCategory.Plus.Qh.obj K) =
      V.mapDerivedCategoryPlusFactorsh.hom.app (F.mapHomotopyCategoryPlus.obj K) ≫
        DerivedCategory.Plus.Qh.map ((mapHomotopyCategoryPlusCompIso e).hom.app K ≫
          (mapHomotopyCategoryPlusCompIso (Iso.refl (U ⋙ F'))).inv.app K) ≫
        F'.rightDerivedFunctorPlusUnith.app (U.mapHomotopyCategoryPlus.obj K) ≫
          F'.rightDerivedFunctorPlus.map (U.mapDerivedCategoryPlusFactorsh.inv.app K) := by
  have h := NatTrans.congr_app (rightDerivedFunctorPlusExactSquareIso_fac e hU) K
  rw [NatTrans.comp_app, Functor.whiskerLeft_app, exactSquarePlusUnitLeft_app,
    exactSquarePlusUnitRight_app, Category.assoc] at h
  rw [← h, Iso.hom_inv_id_app_assoc]

end CategoryTheory.Functor

end
