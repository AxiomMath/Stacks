module

public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.PullbackHgroupComposition
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.GysinCohomologyDeRham
public import StacksFrontier.AlgebraicGeometry.DeRham.DerivedDirectImage
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeUnit
public import StacksFrontier.Algebra.Homology.DerivedCategory.ExactCompositionQhComparison

/-!
# Derived global sections along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)`

Let `f : X ⟶ S` be a morphism of schemes and `c : (X, 𝒪_X) ⟶ (X♭, f⁻¹𝒪_S)` the morphism of
ringed spaces which is the identity on spaces (`Stacks.DeRhamDirectImage.toInverseImageBase`).
A de Rham differential is `f⁻¹𝒪_S`-linear but not `𝒪_X`-linear, so it is a morphism on `X♭` and
only a morphism of abelian sheaves on `X`. This file compares derived global sections on the two
ringed spaces, in the two ways available:

* through the pullback map of [Stacks, Tag 01F9]: the comparison `c_* ⟶ Rc_*` followed by the
  Leray identification of [Stacks, Tag 01EZ] (`coefficientLerayMap`);
* through the underlying complexes of abelian sheaves, which are the same on both sides, and
  [Stacks, Tag 0D5Y] (`coefficientForgetMap`).

## Main results

All in the namespace `Stacks.DeRham.GysinCohomologyBaseChange`.

* `sectionsForgetUnit_app`: the comparison unit of Tag 0D5Y, pointwise.
* `coefficientLerayMap_eq_coefficientForgetMap`: the two comparisons agree.
* `coefficientSingleMap_eq`: the pullback map of the identity of `c_*ℳ` on cohomology is
  `coefficientLerayMap` at the single complex.
* `pullbackHgroup_toInverseImageBase_abelianHgroupMap`: the pullback map `Hⁿ(X♭, c_*ℳ) ≅ Hⁿ(X, ℳ)`
  of the identity of `c_*ℳ` carries the map induced by an `f⁻¹𝒪_S`-linear morphism
  `ψ♭ : c_*ℳ ⟶ c_*𝒩` to the abelian action `abelianHgroupMap` of its underlying morphism of abelian
  sheaves. This is how a de Rham differential is moved past pullback maps on cohomology.
* `mapDerivedCategorySingleFunctor_hom_app_comp_singleFunctorIsoCompQh_of_degree`: the
  single-functor comparison of an exact functor through the homotopy category, in any degree.

## Implementation notes

The objects of the derived categories of `X` and of `X♭` built from the same complex are
definitionally equal at low cost; morphisms built through the quotient to the homotopy category
are not, unless they are applied to the class of a morphism of complexes. The chases are
therefore carried out by small lemmas at variables, applied with `exact`, and the comparisons of
morphisms are stated for classes of morphisms of complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.UnderlyingAbelianSheaf Stacks.Cohomology.OpenSubspace
open Stacks.DeRham.CohomologicalGysin Stacks.DeRham.GysinCohomologyDeRham
open Stacks.DeRhamDirectImage (inverseImageBase toInverseImageBase)
open scoped Stacks.StandardDerivedModel

namespace Stacks.DeRham.GysinCohomologyBaseChange

universe u

attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

/-! ### The single-functor comparison of an exact functor, through the homotopy category -/

section SingleCoherence

variable {C : Type*} {A : Type*} [Category* C] [Category* A] [Abelian C] [Abelian A]
  [HasDerivedCategory C] [HasDerivedCategory A]
  (F : C ⥤ A) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The components of `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` in degree `n`. -/
private lemma mapDerivedCategorySingleFunctor_hom_app_eq (n : ℤ) (X : C) :
    (F.mapDerivedCategorySingleFunctor n).hom.app X =
      F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C n).obj X) ≫
        DerivedCategory.Q.map
          ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).hom.app X) := by
  simp only [Functor.comp_obj, Functor.mapDerivedCategorySingleFunctor,
    DerivedCategory.singleFunctorIsoCompQ, Functor.isoWhiskerRight_refl,
    Functor.isoWhiskerLeft_refl, Iso.refl_symm, Iso.refl_trans, Iso.trans_hom,
    Functor.isoWhiskerLeft_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom, Iso.refl_hom,
    NatTrans.comp_app, Functor.associator_hom_app, Functor.whiskerLeft_app,
    Functor.associator_inv_app, DerivedCategory.Q_obj_single_obj, Functor.whiskerRight_app,
    NatTrans.id_app, Category.comp_id, Category.id_comp]
  exact Category.id_comp _

/-- The left half of the chase behind
`mapDerivedCategorySingleFunctor_hom_app_comp_singleFunctorIsoCompQh_of_degree`, at variables. -/
private lemma single_chase_left {E : Type*} [Category* E] {P₀ P₁ P₂ P₃ P₄ : E}
    (m : P₀ ⟶ P₂) (a : P₀ ⟶ P₁) (b : P₁ ⟶ P₂) (i : P₂ ⟶ P₃) (q : P₃ ⟶ P₄) (j : P₁ ⟶ P₄)
    (p : P₄ ⟶ P₃) (hm : m = a ≫ b) (hnat : b ≫ i = j ≫ p) (hpq : p ≫ q = 𝟙 P₄) :
    m ≫ i ≫ q = a ≫ j := by
  rw [hm, Category.assoc, ← Category.assoc b i q, hnat, Category.assoc, hpq, Category.comp_id]

/-- The right half of the same chase, at variables. -/
private lemma single_chase_right {E : Type*} [Category* E] {P₀ P₁ P₄ P₅ : E}
    (a : P₀ ⟶ P₁) (j : P₁ ⟶ P₄) (d : P₀ ⟶ P₅) (d' : P₅ ⟶ P₀) (h : P₅ ⟶ P₄)
    (hd : d ≫ d' = 𝟙 P₀) (hh : h = (d' ≫ a) ≫ j) : d ≫ h = a ≫ j := by
  rw [hh, ← Category.assoc, ← Category.assoc, hd, Category.id_comp]

/-- **The single-functor comparison of `F.mapDerivedCategory` in degree `n`, read at the homotopy
category**: the comparison `CategoryTheory.Functor.mapDerivedCategorySingleFunctor` followed by
the identification of the single functor with the single functor into the homotopy category
followed by `Qh`, and by the termwise comparison of `F` on a single complex, is the
factorization `CategoryTheory.Functor.mapDerivedCategoryFactorsh` precomposed with the same
identification on the source side. -/
theorem mapDerivedCategorySingleFunctor_hom_app_comp_singleFunctorIsoCompQh_of_degree (n : ℤ)
    (X : C) :
    (F.mapDerivedCategorySingleFunctor n).hom.app X ≫
        (DerivedCategory.singleFunctorIsoCompQh A n).hom.app (F.obj X) ≫
          DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            ((HomologicalComplex.singleMapHomologicalComplex F
              (ComplexShape.up ℤ) n).inv.app X)) =
      F.mapDerivedCategory.map ((DerivedCategory.singleFunctorIsoCompQh C n).hom.app X) ≫
        F.mapDerivedCategoryFactorsh.hom.app ((HomotopyCategory.singleFunctor C n).obj X) := by
  have hpq : DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℤ) n).hom.app X)) ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex F
            (ComplexShape.up ℤ) n).inv.app X)) = 𝟙 _ := by
    simp
  have hd : F.mapDerivedCategory.map ((DerivedCategory.singleFunctorIsoCompQh C n).hom.app X) ≫
      F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app
        ((CochainComplex.singleFunctor C n).obj X)) = 𝟙 _ := by
    rw [Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app]
    exact (F.mapDerivedCategory.mapIso ((DerivedCategory.quotientCompQhIso C).app
      ((CochainComplex.singleFunctor C n).obj X))).inv_hom_id
  refine (single_chase_left ((F.mapDerivedCategorySingleFunctor n).hom.app X)
    (F.mapDerivedCategoryFactors.hom.app ((CochainComplex.singleFunctor C n).obj X))
    (DerivedCategory.Q.map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).hom.app X))
    ((DerivedCategory.singleFunctorIsoCompQh A n).hom.app (F.obj X))
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).inv.app X)))
    ((DerivedCategory.quotientCompQhIso A).inv.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((CochainComplex.singleFunctor C n).obj X)))
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) n).hom.app X)))
    (mapDerivedCategorySingleFunctor_hom_app_eq F n X) ?_ hpq).trans
    (single_chase_right _ _ _
      (F.mapDerivedCategory.map ((DerivedCategory.quotientCompQhIso C).hom.app
        ((CochainComplex.singleFunctor C n).obj X))) _ hd ?_).symm
  · rw [Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app]
    exact (DerivedCategory.quotientCompQhIso A).inv.naturality _
  · exact (Iso.eq_comp_inv ((DerivedCategory.quotientCompQhIso A).app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
          ((CochainComplex.singleFunctor C n).obj X)))).2
      (Stacks.DerivedFunctor.mapDerivedCategoryFactorsh_hom_app_comp_quotientCompQhIso F
        ((CochainComplex.singleFunctor C n).obj X))

omit [HasDerivedCategory A] in
/-- The termwise comparisons of single complexes for `P` and for `F`, composed, are the one for
`P ⋙ F`. -/
theorem singleMapHomologicalComplex_inv_comp {C₁ C₂ : Type*} [Category* C₁]
    [Category* C₂] [Abelian C₁] [Abelian C₂] (P : C₁ ⥤ C₂) (F' : C₂ ⥤ A) [P.Additive]
    [F'.Additive] (n : ℤ) (X : C₁) :
    (HomologicalComplex.singleMapHomologicalComplex F' (ComplexShape.up ℤ) n).inv.app (P.obj X) ≫
        (F'.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((HomologicalComplex.singleMapHomologicalComplex P (ComplexShape.up ℤ) n).inv.app X) =
      (HomologicalComplex.singleMapHomologicalComplex (P ⋙ F')
        (ComplexShape.up ℤ) n).inv.app X := by
  ext i
  by_cases h : i = n
  · subst h
    simp only [HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self, Functor.comp_map,
      Functor.map_comp, Category.assoc]
    rw [← F'.map_comp_assoc, Iso.inv_hom_id, F'.map_id, Category.id_comp]
    rfl
  · simp [HomologicalComplex.singleMapHomologicalComplex_inv_app_ne _ _ h]


end SingleCoherence

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The direct image of modules along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` preserves finite colimits. -/
instance preservesFiniteColimits_modulePushforward_toInverseImageBase :
    PreservesFiniteColimits (modulePushforward (toInverseImageBase f)) :=
  Stacks.DeRhamDirectImage.preservesFiniteColimits_pushforward_toInverseImageBase f

/-- The comparison of derived global sections along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` built from the
pullback map of [Stacks, Tag 01F9]: the comparison `c_* ⟶ Rc_*` followed by the Leray
identification. -/
def coefficientLerayMap (K : HomotopyCategory (RModules X.toRingedSpace) (ComplexShape.up ℤ)) :
    (derivedGlobalSections (inverseImageBase f)).obj
        ((pushforwardToDerivedCategory (toInverseImageBase f)).obj K) ⟶
      (derivedGlobalSections X.toRingedSpace).obj (DerivedCategory.Qh.obj K) :=
  (derivedGlobalSections _).map ((derivedPushforwardUnit (toInverseImageBase f)).app K) ≫
    (CohomologyPullbackComparison.canonical (toInverseImageBase f)).leray.hom.app
      (DerivedCategory.Qh.obj K)

/-- The comparison of derived global sections along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` through the
underlying complexes of abelian sheaves, which are the same on both sides. -/
def coefficientForgetMap (K : HomotopyCategory (RModules X.toRingedSpace) (ComplexShape.up ℤ)) :
    (derivedGlobalSections (inverseImageBase f)).obj
        ((pushforwardToDerivedCategory (toInverseImageBase f)).obj K) ⟶
      (derivedGlobalSections X.toRingedSpace).obj (DerivedCategory.Qh.obj K) :=
  (globalSectionsForgetIso (inverseImageBase f)).hom.app _ ≫
    (derivedAbelianGlobalSections (inverseImageBase f)).map
      ((forgetModules (inverseImageBase f)).mapDerivedCategoryFactorsh.hom.app
          (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        (forgetModules X.toRingedSpace).mapDerivedCategoryFactorsh.inv.app K) ≫
    (globalSectionsForgetIso X.toRingedSpace).inv.app _

/-- Cancelling an inverse after a factorization, at variables. -/
private lemma unit_leray_chase {C : Type*} [Category* C] {A B D E : C} (q : A ⟶ A) (uY : A ⟶ B)
    (rη : B ⟶ D) (uX : A ⟶ E) (lc : E ⟶ D) (li : D ⟶ E)
    (hfac : uX ≫ lc = q ≫ uY ≫ rη) (hq : q = 𝟙 A) (hli : lc ≫ li = 𝟙 E) : uY ≫ rη ≫ li = uX := by
  subst hq
  rw [← Category.assoc, ← Category.id_comp (uY ≫ rη), ← hfac, Category.assoc, hli,
    Category.comp_id]

/-- The comparison through the Leray identification restricts, along the unit of `RΓ(X♭, -)`, to
the unit of `RΓ(X, -)`. -/
theorem unit_comp_coefficientLerayMap
    (K : HomotopyCategory (RModules X.toRingedSpace) (ComplexShape.up ℤ)) :
    (derivedGlobalSectionsUnit (inverseImageBase f)).app
        (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫ coefficientLerayMap f K =
      (derivedGlobalSectionsUnit X.toRingedSpace).app K := by
  have := isIso_lerayComparisonAb (toInverseImageBase f)
  have hfac := lerayComparisonAb_fac_app (toInverseImageBase f) K
  rw [lerayUnitAb_app] at hfac
  have hL : (CohomologyPullbackComparison.canonical (toInverseImageBase f)).leray.hom =
    inv (lerayComparisonAb (toInverseImageBase f)) := rfl
  unfold coefficientLerayMap
  rw [hL, NatIso.isIso_inv_app]
  exact unit_leray_chase _ _ _ _ _ _ hfac (by rw [← CategoryTheory.Functor.map_id]; rfl)
    (IsIso.hom_inv_id _)

/-- The algebra of `unit_comp_coefficientForgetMap`, at variables. -/
private lemma unit_forget_chase {C : Type*} [Category* C] {A B D₁ D₂ E : C} (uY : A ⟶ B)
    (gY : B ⟶ D₁) (sY : A ⟶ D₁) (r : D₁ ⟶ D₂) (gXi : D₂ ⟶ E) (uX : A ⟶ E) (gX : E ⟶ D₂)
    (sX : A ⟶ D₂) (hY : uY ≫ gY = sY) (hX : uX ≫ gX = sX) (hs : sY ≫ r = sX)
    (hg : gX ≫ gXi = 𝟙 E) : uY ≫ gY ≫ r ≫ gXi = uX := by
  rw [← Category.assoc, hY, ← Category.assoc, hs, ← hX, Category.assoc, hg, Category.comp_id]

/-- **The comparison unit through the underlying abelian sheaves, pointwise**: at a complex `K`
of modules it is the unit of derived sections of abelian sheaves at the underlying complex,
followed by the identification of the underlying complex in the derived category. -/
theorem sectionsForgetUnit_app {T : TopCat.{u}}
    (O : Sheaf (Opens.grothendieckTopology T) RingCat.{u})
    (U : Opens T) (K : HomotopyCategory (SheafOfModules.{u} O) (ComplexShape.up ℤ)) :
    (sectionsForgetUnit O U).app K =
      ((homotopyAbelianSectionsOnOpen T U).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (Sheaf (Opens.grothendieckTopology T) AddCommGrpCat.{u})
            (ComplexShape.up ℤ))).app
        (((SheafOfModules.toSheaf O).mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      (derivedAbelianSectionsOnOpen T U).map
        ((SheafOfModules.toSheaf O).mapDerivedCategoryFactorsh.inv.app K) := by
  unfold sectionsForgetUnit
  dsimp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app]
  simp only [Functor.associator_hom_app, Category.id_comp, ← Functor.map_comp_assoc]
  refine (congrArg (· ≫ _) (?_ : DerivedCategory.Qh.map _ = 𝟙 _)).trans (Category.id_comp _)
  rw [← CategoryTheory.Functor.map_id]
  rfl

/-- The algebra of the comparison of the two units through the underlying abelian sheaves, at
variables. -/
private lemma hs_chase {C D : Type*} [Category* C] [Category* D] (G : D ⥤ C) {A : C} {x y z : D}
    (U : A ⟶ G.obj x) (fi : x ⟶ y) (fh : y ⟶ x) (fx : x ⟶ z) (hfi : fi ≫ fh = 𝟙 x) :
    (U ≫ G.map fi) ≫ G.map (fh ≫ fx) = U ≫ G.map fx := by
  rw [Category.assoc, ← G.map_comp, ← Category.assoc fi, hfi, Category.id_comp]

/-- The comparison through the underlying abelian sheaves restricts, along the unit of
`RΓ(X♭, -)`, to the unit of `RΓ(X, -)`. -/
theorem unit_comp_coefficientForgetMap
    (K : HomotopyCategory (RModules X.toRingedSpace) (ComplexShape.up ℤ)) :
    (derivedGlobalSectionsUnit (inverseImageBase f)).app
        (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫ coefficientForgetMap f K =
      (derivedGlobalSectionsUnit X.toRingedSpace).app K := by
  have hY := (derivedSectionsOnOpen (structureSheafRing (inverseImageBase f))
      ⊤).rightDerived_fac_app
    ((homotopySectionsOnOpen (structureSheafRing (inverseImageBase f)) ⊤).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (RModules (inverseImageBase f)) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (RModules (inverseImageBase f)) (ComplexShape.up ℤ)) _
    (sectionsForgetUnit (structureSheafRing (inverseImageBase f)) ⊤)
    (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory (ComplexShape.up ℤ)).obj K)
  have hX := (derivedSectionsOnOpen (structureSheafRing X.toRingedSpace) ⊤).rightDerived_fac_app
    ((homotopySectionsOnOpen (structureSheafRing X.toRingedSpace) ⊤).totalRightDerivedUnit
      DerivedCategory.Qh
      (HomotopyCategory.quasiIso (RModules X.toRingedSpace) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (RModules X.toRingedSpace) (ComplexShape.up ℤ)) _
    (sectionsForgetUnit (structureSheafRing X.toRingedSpace) ⊤) K
  have hs : (sectionsForgetUnit (structureSheafRing (inverseImageBase f)) ⊤).app
        (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      (derivedAbelianGlobalSections (inverseImageBase f)).map
        ((forgetModules (inverseImageBase f)).mapDerivedCategoryFactorsh.hom.app
            (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory
              (ComplexShape.up ℤ)).obj K) ≫
          (forgetModules X.toRingedSpace).mapDerivedCategoryFactorsh.inv.app K) =
      (sectionsForgetUnit (structureSheafRing X.toRingedSpace) ⊤).app K := by
    rw [sectionsForgetUnit_app, sectionsForgetUnit_app]
    refine hs_chase (derivedAbelianSectionsOnOpen X.toRingedSpace.carrier ⊤) _ _ _ _ ?_
    exact Iso.inv_hom_id_app _ _
  have hX' : (derivedGlobalSectionsUnit X.toRingedSpace).app K ≫
      (globalSectionsForgetIso X.toRingedSpace).hom.app (DerivedCategory.Qh.obj K) =
      (sectionsForgetUnit (structureSheafRing X.toRingedSpace) ⊤).app K := hX
  have hY' : (derivedGlobalSectionsUnit (inverseImageBase f)).app
        (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) ≫
      (globalSectionsForgetIso (inverseImageBase f)).hom.app (DerivedCategory.Qh.obj
        (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K)) =
      (sectionsForgetUnit (structureSheafRing (inverseImageBase f)) ⊤).app
        (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory
          (ComplexShape.up ℤ)).obj K) := hY
  unfold coefficientForgetMap
  exact unit_forget_chase _ _ _ _ _ _ _ _ hY' hX' hs (Iso.hom_inv_id_app _ _)

/-- The algebra of `coefficientLerayMap_naturality`, at variables. -/
private lemma leray_naturality_chase {C D : Type*} [Category* C] [Category* D] (F : D ⥤ C)
    {a b c d : D} {e e' : C} (p : a ⟶ b) (ηL : b ⟶ c) (ηK : a ⟶ d) (r : d ⟶ c)
    (LL : F.obj c ⟶ e') (LK : F.obj d ⟶ e) (Gq : e ⟶ e') (h1 : p ≫ ηL = ηK ≫ r)
    (h2 : F.map r ≫ LL = LK ≫ Gq) :
    F.map p ≫ (F.map ηL ≫ LL) = (F.map ηK ≫ LK) ≫ Gq := by
  rw [← F.map_comp_assoc, h1, F.map_comp_assoc, h2, Category.assoc]

/-- The comparison through the Leray identification is natural in the complex. -/
theorem coefficientLerayMap_naturality
    {K L : HomotopyCategory (RModules X.toRingedSpace) (ComplexShape.up ℤ)} (g : K ⟶ L) :
    (derivedGlobalSections (inverseImageBase f)).map
        ((pushforwardToDerivedCategory (toInverseImageBase f)).map g) ≫ coefficientLerayMap f L =
      coefficientLerayMap f K ≫
        (derivedGlobalSections X.toRingedSpace).map (DerivedCategory.Qh.map g) := by
  have h1 := (derivedPushforwardUnit (toInverseImageBase f)).naturality g
  have h2 := (CohomologyPullbackComparison.canonical (toInverseImageBase f)).leray.hom.naturality
    (DerivedCategory.Qh.map g)
  dsimp only [Functor.comp_map] at h1 h2
  exact leray_naturality_chase _ _ _ _ _ _ _ _ h1 h2



/-- The underlying abelian complex of the direct image along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` of a
morphism of complexes is that of the morphism itself. -/
private lemma forget_pushforward_quotient_map {M N : CochainComplex (RModules X.toRingedSpace) ℤ}
    (ψ : M ⟶ N) :
    (DerivedCategory.Qh (C := AbSheaves (inverseImageBase f))).map
      ((HomotopyCategory.quotient (AbSheaves (inverseImageBase f)) (ComplexShape.up ℤ)).map
        (((forgetModules (inverseImageBase f)).mapHomologicalComplex (ComplexShape.up ℤ)).map
          (((modulePushforward (toInverseImageBase f)).mapHomologicalComplex
            (ComplexShape.up ℤ)).map ψ))) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient (AbSheaves X.toRingedSpace)
        (ComplexShape.up ℤ)).map
          (((forgetModules X.toRingedSpace).mapHomologicalComplex (ComplexShape.up ℤ)).map ψ)) :=
  rfl

/-- The algebra of `coefficientForgetMap_naturality`, at variables. -/
private lemma forget_naturality_chase {C D : Type*} [Category* C] [Category* D] (G : D ⥤ C)
    {a₀ a₁ : C} {x₀ x₁ y₀ y₁ z₀ z₁ : D} {b₀ b₁ : C}
    (s₀ : a₀ ⟶ G.obj x₀) (s₁ : a₁ ⟶ G.obj x₁) (t₀ : G.obj z₀ ⟶ b₀) (t₁ : G.obj z₁ ⟶ b₁)
    (ga : a₀ ⟶ a₁) (gx : x₀ ⟶ x₁) (gy gy' : y₀ ⟶ y₁) (gz : z₀ ⟶ z₁) (gb : b₀ ⟶ b₁)
    (h₀ : x₀ ⟶ y₀) (h₁ : x₁ ⟶ y₁) (k₀ : y₀ ⟶ z₀) (k₁ : y₁ ⟶ z₁)
    (hs : ga ≫ s₁ = s₀ ≫ G.map gx) (hh : gx ≫ h₁ = h₀ ≫ gy)
    (hk : gy' ≫ k₁ = k₀ ≫ gz) (ht : G.map gz ≫ t₁ = t₀ ≫ gb) (hy : gy = gy') :
    ga ≫ s₁ ≫ G.map (h₁ ≫ k₁) ≫ t₁ = (s₀ ≫ G.map (h₀ ≫ k₀) ≫ t₀) ≫ gb := by
  subst hy
  rw [reassoc_of% hs, ← G.map_comp_assoc, reassoc_of% hh, hk]
  simp only [G.map_comp, Category.assoc, ht]

/-- The comparison through the underlying abelian sheaves is natural in the complex. -/
theorem coefficientForgetMap_naturality
    {K₀ L₀ : CochainComplex (RModules X.toRingedSpace) ℤ} (φ : K₀ ⟶ L₀) :
    (derivedGlobalSections (inverseImageBase f)).map
        ((pushforwardToDerivedCategory (toInverseImageBase f)).map
          ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).map φ)) ≫
        coefficientForgetMap f
          ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).obj L₀) =
      coefficientForgetMap f
          ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).obj K₀) ≫
        (derivedGlobalSections X.toRingedSpace).map (DerivedCategory.Qh.map
          ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).map φ)) := by
  have hs := (globalSectionsForgetIso (inverseImageBase f)).hom.naturality
    ((pushforwardToDerivedCategory (toInverseImageBase f)).map
      ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).map φ))
  have hh := (forgetModules (inverseImageBase f)).mapDerivedCategoryFactorsh.hom.naturality
    (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory (ComplexShape.up ℤ)).map
      ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).map φ))
  have hk := (forgetModules X.toRingedSpace).mapDerivedCategoryFactorsh.inv.naturality
    ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).map φ)
  have ht := (globalSectionsForgetIso X.toRingedSpace).inv.naturality (DerivedCategory.Qh.map
    ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).map φ))
  dsimp only [Functor.comp_map] at hs hh hk ht
  unfold coefficientForgetMap
  exact forget_naturality_chase (derivedAbelianGlobalSections X.toRingedSpace) _ _ _ _ _ _ _ _ _
    _ _ _ _ _ hs hh hk ht (forget_pushforward_quotient_map f φ)

/-- `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` is the identity on spaces, a closed embedding. -/
theorem isClosedEmbedding_toInverseImageBase :
    Topology.IsClosedEmbedding (toInverseImageBase f).hom.base :=
  Topology.IsClosedEmbedding.id

/-- **The two comparisons of derived global sections along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` agree**:
the one through the pullback map of [Stacks, Tag 01F9] and the Leray identification, and the one
through the underlying complexes of abelian sheaves. -/
theorem coefficientLerayMap_eq_coefficientForgetMap
    (K : HomotopyCategory (RModules X.toRingedSpace) (ComplexShape.up ℤ)) :
    coefficientLerayMap f K = coefficientForgetMap f K := by
  obtain ⟨I, s, hI, hs⟩ := exists_quasiIso_isKInjective X.toRingedSpace K.as
  have hIK : coefficientLerayMap f
        ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).obj I) =
      coefficientForgetMap f
        ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).obj I) := by
    have := hI
    have hu : IsIso ((derivedGlobalSectionsUnit X.toRingedSpace).app
        ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).obj I)) :=
      Stacks.DerivedFunctor.isIso_totalRightDerivedUnit_app_of_isKInjective
        (secF (structureSheafRing X.toRingedSpace) ⊤) I
    have : IsIso ((derivedPushforwardUnit (toInverseImageBase f)).app
        ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).obj I)) :=
      Stacks.Cohomology.ClosedEmbeddingPushforward.isIso_derivedPushforwardUnit_app _
        (isClosedEmbedding_toInverseImageBase f) _
    have hT : IsIso (coefficientLerayMap f
        ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).obj I)) := by
      unfold coefficientLerayMap; infer_instance
    have hY := unit_comp_coefficientLerayMap f
      ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).obj I)
    have : IsIso ((derivedGlobalSectionsUnit (inverseImageBase f)).app
        (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).obj I))) := by
      have : IsIso ((derivedGlobalSectionsUnit (inverseImageBase f)).app
          (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).obj I)) ≫
          coefficientLerayMap f ((HomotopyCategory.quotient (RModules X.toRingedSpace)
            (ComplexShape.up ℤ)).obj I)) := by
        rw [hY]; exact hu
      exact IsIso.of_isIso_comp_right _ (coefficientLerayMap f
        ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).obj I))
    rw [← cancel_epi ((derivedGlobalSectionsUnit (inverseImageBase f)).app
        (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).obj I))),
      unit_comp_coefficientLerayMap, unit_comp_coefficientForgetMap]
  have : IsIso ((derivedGlobalSections X.toRingedSpace).map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).map s))) := by
    have : IsIso (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).map s)) :=
      (DerivedCategory.isIso_Qh_map_iff _).2
        ((HomotopyCategory.quotient_map_mem_quasiIso_iff _).2
          ((HomologicalComplex.mem_quasiIso_iff _).2 hs))
    infer_instance
  have hT := coefficientLerayMap_naturality f
    ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).map s)
  have hΘ := coefficientForgetMap_naturality f s
  refine (cancel_mono ((derivedGlobalSections X.toRingedSpace).map (DerivedCategory.Qh.map
      ((HomotopyCategory.quotient (RModules X.toRingedSpace) (ComplexShape.up ℤ)).map s)))).1 ?_
  exact hT.symm.trans ((congrArg (_ ≫ ·) hIK).trans hΘ)

/-! ### The pullback map of the identity of `c_*ℳ` on cohomology -/

/-- The morphism of derived global sections underlying the pullback map
`Hⁿ(X♭, c_*ℳ) ⟶ Hⁿ(X, ℳ)` of the identity of `c_*ℳ`, for `ℳ` placed in degree `a`. -/
def coefficientSingleMap (a : ℤ) (A : RModules X.toRingedSpace) :
    (derivedGlobalSections (inverseImageBase f)).obj
        ((DerivedCategory.singleFunctor _ a).obj
          ((modulePushforward (toInverseImageBase f)).obj A)) ⟶
      (derivedGlobalSections X.toRingedSpace).obj ((DerivedCategory.singleFunctor _ a).obj A) :=
  (derivedGlobalSections (inverseImageBase f)).map
      (derivedPushforwardMap (CohomologyPullbackComparison.canonical (toInverseImageBase f)) a
        (𝟙 _)) ≫
    (CohomologyPullbackComparison.canonical (toInverseImageBase f)).leray.hom.app
      ((DerivedCategory.singleFunctor _ a).obj A)

/-- The pullback map of the identity of `c_*ℳ` is the map induced by `coefficientSingleMap`. -/
theorem pullbackHgroup_toInverseImageBase_id (a m : ℤ) (n : ℕ) (hn : m - a = n)
    (A : RModules X.toRingedSpace) :
    pullbackHgroup (CohomologyPullbackComparison.canonical (toInverseImageBase f)) a m n hn
        (𝟙 ((modulePushforward (toInverseImageBase f)).obj A)) =
      (cohomologyDerivedSingleIso (inverseImageBase f) _ a m n hn).inv ≫
        (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map (coefficientSingleMap f a A) ≫
          (cohomologyDerivedSingleIso X.toRingedSpace A a m n hn).hom :=
  rfl

/-- The algebra of `coefficientSingleMap_eq`, at variables. -/
private lemma single_leray_chase {C D : Type*} [Category* C] [Category* D] (F : D ⥤ C)
    {d₀ d₁ d₂ d₃ d₄ d₅ : D} {e₁ e₂ : C} (s₁ : d₀ ⟶ d₁) (s₂ : d₁ ⟶ d₂) (s₃ : d₂ ⟶ d₃)
    (η : d₃ ⟶ d₄) (rτ : d₄ ⟶ d₅) (L₂ : F.obj d₅ ⟶ e₂) (L₁ : F.obj d₄ ⟶ e₁) (gτ : e₁ ⟶ e₂)
    (hL : F.map rτ ≫ L₂ = L₁ ≫ gτ) :
    F.map (s₁ ≫ s₂ ≫ s₃ ≫ η ≫ rτ) ≫ L₂ = F.map (s₁ ≫ s₂ ≫ s₃) ≫ (F.map η ≫ L₁) ≫ gτ := by
  simp only [F.map_comp, Category.assoc]
  rw [hL]

/-- `coefficientSingleMap` is the comparison `coefficientLerayMap` at the single complex, between
the identifications of the single functors with the single functors into the homotopy category. -/
theorem coefficientSingleMap_eq (a : ℤ) (A : RModules X.toRingedSpace) :
    coefficientSingleMap f a A =
      (derivedGlobalSections (inverseImageBase f)).map
          ((DerivedCategory.singleFunctor _ a).map (𝟙 _) ≫
            (DerivedCategory.singleFunctorIsoCompQh (RModules (inverseImageBase f)) a).hom.app
              ((modulePushforward (toInverseImageBase f)).obj A) ≫
            DerivedCategory.Qh.map ((Functor.mapHomotopyCategorySingleFunctor
              (modulePushforward (toInverseImageBase f)) a).inv.app A)) ≫
        coefficientLerayMap f
            ((HomotopyCategory.singleFunctor (RModules X.toRingedSpace) a).obj A) ≫
          (derivedGlobalSections X.toRingedSpace).map
            ((DerivedCategory.singleFunctorIsoCompQh (RModules X.toRingedSpace) a).inv.app A) := by
  have hL := (CohomologyPullbackComparison.canonical (toInverseImageBase f)).leray.hom.naturality
    ((DerivedCategory.singleFunctorIsoCompQh (RModules X.toRingedSpace) a).inv.app A)
  dsimp only [Functor.comp_map] at hL
  unfold coefficientSingleMap coefficientLerayMap derivedPushforwardMap
  dsimp only [CohomologyPullbackComparison.canonical, singleToDerivedPushforward, NatTrans.comp_app,
    Functor.whiskerLeft_app, Functor.whiskerRight_app]
  exact single_leray_chase _ _ _ _ _ _ _ _ _ hL


/-- The termwise comparison of single complexes for `c_* ⋙ (forget)` is that for `forget`, read
in the derived category of abelian sheaves. -/
private lemma forget_pushforward_singleMap (a : ℤ) (A : RModules X.toRingedSpace) :
    (DerivedCategory.Qh (C := AbSheaves (inverseImageBase f))).map
      ((HomotopyCategory.quotient (AbSheaves (inverseImageBase f)) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (modulePushforward (toInverseImageBase f) ⋙ forgetModules (inverseImageBase f))
          (ComplexShape.up ℤ) a).inv.app A)) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient (AbSheaves X.toRingedSpace)
        (ComplexShape.up ℤ)).map ((HomologicalComplex.singleMapHomologicalComplex
          (forgetModules X.toRingedSpace) (ComplexShape.up ℤ) a).inv.app A)) :=
  rfl

/-- The `(X, 𝒪_X)`-half of the algebra of `forgetSingle_coefficient`, at variables. -/
private lemma rho_chase_right {D : Type*} [Category* D] {o₃ o₄ o₅ o₇ o₈ : D}
    (SX : o₅ ⟶ o₇) (SXi : o₇ ⟶ o₅) (Q : o₇ ⟶ o₈) (m : o₈ ⟶ o₃)
    (τ' : o₅ ⟶ o₄) (fhX : o₄ ⟶ o₃) (fi : o₃ ⟶ o₄) (τ : o₄ ⟶ o₅)
    (h2 : SX ≫ Q ≫ m = τ' ≫ fhX) (hτ : τ' ≫ τ = 𝟙 o₅) (hfi : fhX ≫ fi = 𝟙 o₄)
    (hSX : SXi ≫ SX = 𝟙 o₇) :
    Q ≫ m ≫ fi ≫ τ = SXi := by
  rw [← Category.id_comp (Q ≫ m ≫ fi ≫ τ), ← hSX]
  simp only [Category.assoc]
  rw [reassoc_of% h2, reassoc_of% hfi, hτ, Category.comp_id]

/-- The `(X, f⁻¹𝒪_S)`-half of the algebra of `forgetSingle_coefficient`, at variables. -/
private lemma rho_chase_left {D : Type*} [Category* D] {o₀ o₁ o₂ o₃ o₆ o₇ o₈ : D}
    (σ₀ : o₀ ⟶ o₂) (σ₁ : o₀ ⟶ o₁) (σ₂ : o₁ ⟶ o₂) (fh₂ : o₂ ⟶ o₃) (fh₁ : o₁ ⟶ o₆)
    (gq : o₆ ⟶ o₃) (S : o₀ ⟶ o₇) (Q Q' : o₇ ⟶ o₈) (m₁ : o₈ ⟶ o₆) (m₂ : o₈ ⟶ o₃)
    (hσ : σ₀ = σ₁ ≫ σ₂) (hN : σ₂ ≫ fh₂ = fh₁ ≫ gq) (h1 : S ≫ Q ≫ m₁ = σ₁ ≫ fh₁)
    (hM : m₁ ≫ gq = m₂) (hQ : Q = Q') :
    σ₀ ≫ fh₂ = S ≫ Q' ≫ m₂ := by
  subst hM hQ
  rw [hσ, Category.assoc, hN, ← Category.assoc, ← h1]
  simp only [Category.assoc]

/-- **The identification of the underlying abelian complexes of `c_*ℳ[-a]` and `ℳ[-a]`** built
from the comparisons through the homotopy category is the one through the single functors of
abelian sheaves. -/
theorem forgetSingle_coefficient (a : ℤ) (A : RModules X.toRingedSpace) :
    (forgetModules (inverseImageBase f)).mapDerivedCategory.map
        ((DerivedCategory.singleFunctor _ a).map (𝟙 _) ≫
          (DerivedCategory.singleFunctorIsoCompQh (RModules (inverseImageBase f)) a).hom.app
            ((modulePushforward (toInverseImageBase f)).obj A) ≫
          DerivedCategory.Qh.map ((Functor.mapHomotopyCategorySingleFunctor
            (modulePushforward (toInverseImageBase f)) a).inv.app A)) ≫
      (forgetModules (inverseImageBase f)).mapDerivedCategoryFactorsh.hom.app
          (((modulePushforward (toInverseImageBase f)).mapHomotopyCategory (ComplexShape.up ℤ)).obj
            ((HomotopyCategory.singleFunctor (RModules X.toRingedSpace) a).obj A)) ≫
        (forgetModules X.toRingedSpace).mapDerivedCategoryFactorsh.inv.app
          ((HomotopyCategory.singleFunctor (RModules X.toRingedSpace) a).obj A) ≫
          (forgetModules X.toRingedSpace).mapDerivedCategory.map
            ((DerivedCategory.singleFunctorIsoCompQh (RModules X.toRingedSpace) a).inv.app A) =
      (forgetSingle (inverseImageBase f) a).hom.app
          ((modulePushforward (toInverseImageBase f)).obj A) ≫
        (forgetSingle X.toRingedSpace a).inv.app A := by
  have h1 := mapDerivedCategorySingleFunctor_hom_app_comp_singleFunctorIsoCompQh_of_degree
    (forgetModules (inverseImageBase f)) a ((modulePushforward (toInverseImageBase f)).obj A)
  have h2 := mapDerivedCategorySingleFunctor_hom_app_comp_singleFunctorIsoCompQh_of_degree
    (forgetModules X.toRingedSpace) a A
  have hN := (forgetModules (inverseImageBase f)).mapDerivedCategoryFactorsh.hom.naturality
    ((Functor.mapHomotopyCategorySingleFunctor (modulePushforward (toInverseImageBase f))
      a).inv.app A)
  dsimp only [Functor.comp_map] at hN
  have hq : (HomotopyCategory.quotient (AbSheaves (inverseImageBase f)) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex (forgetModules (inverseImageBase f))
          (ComplexShape.up ℤ) a).inv.app ((modulePushforward (toInverseImageBase f)).obj A)) ≫
      ((forgetModules (inverseImageBase f)).mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((Functor.mapHomotopyCategorySingleFunctor (modulePushforward (toInverseImageBase f))
          a).inv.app A) =
      (HomotopyCategory.quotient (AbSheaves (inverseImageBase f)) (ComplexShape.up ℤ)).map
        ((HomologicalComplex.singleMapHomologicalComplex
          (modulePushforward (toInverseImageBase f) ⋙ forgetModules (inverseImageBase f))
          (ComplexShape.up ℤ) a).inv.app A) := by
    rw [Stacks.DerivedIndexing.mapHomotopyCategorySingleFunctor_inv_app_degree]
    exact (Functor.map_comp _ _ _).symm.trans (congrArg _ (singleMapHomologicalComplex_inv_comp
      (modulePushforward (toInverseImageBase f)) (forgetModules (inverseImageBase f)) a A))
  have hM := congrArg (DerivedCategory.Qh (C := AbSheaves (inverseImageBase f))).map hq
  have hM' := ((DerivedCategory.Qh (C := AbSheaves (inverseImageBase f))).map_comp _ _).symm.trans
    (hM.trans (forget_pushforward_singleMap f a A))
  have hσ : (forgetModules (inverseImageBase f)).mapDerivedCategory.map
        ((DerivedCategory.singleFunctor _ a).map (𝟙 _) ≫
          (DerivedCategory.singleFunctorIsoCompQh (RModules (inverseImageBase f)) a).hom.app
            ((modulePushforward (toInverseImageBase f)).obj A) ≫
          DerivedCategory.Qh.map ((Functor.mapHomotopyCategorySingleFunctor
            (modulePushforward (toInverseImageBase f)) a).inv.app A)) =
      (forgetModules (inverseImageBase f)).mapDerivedCategory.map
          ((DerivedCategory.singleFunctorIsoCompQh (RModules (inverseImageBase f)) a).hom.app
            ((modulePushforward (toInverseImageBase f)).obj A)) ≫
        (forgetModules (inverseImageBase f)).mapDerivedCategory.map
          (DerivedCategory.Qh.map ((Functor.mapHomotopyCategorySingleFunctor
            (modulePushforward (toInverseImageBase f)) a).inv.app A)) := by
    rw [CategoryTheory.Functor.map_id, Category.id_comp, Functor.map_comp]
  have hQ : (DerivedCategory.singleFunctorIsoCompQh (AbSheaves (inverseImageBase f)) a).hom.app
        ((forgetModules (inverseImageBase f)).obj
          ((modulePushforward (toInverseImageBase f)).obj A)) =
      (DerivedCategory.singleFunctorIsoCompQh (AbSheaves X.toRingedSpace) a).hom.app
        ((forgetModules X.toRingedSpace).obj A) := by
    rw [Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app,
      Stacks.DerivedIndexing.singleFunctorIsoCompQh_hom_app]
    rfl
  have hX := rho_chase_right _ ((forgetSingle X.toRingedSpace a).inv.app A) _ _ _ _
    ((forgetModules X.toRingedSpace).mapDerivedCategoryFactorsh.inv.app
      ((HomotopyCategory.singleFunctor (RModules X.toRingedSpace) a).obj A))
    ((forgetModules X.toRingedSpace).mapDerivedCategory.map
      ((DerivedCategory.singleFunctorIsoCompQh (RModules X.toRingedSpace) a).inv.app A)) h2
    (by rw [← Functor.map_comp, Iso.hom_inv_id_app, CategoryTheory.Functor.map_id]; rfl)
    (Iso.hom_inv_id_app _ _) (Iso.inv_hom_id_app _ _)
  have hB := rho_chase_left _ _ _ _ _ _ _ _ _ _ _ hσ hN h1 hM' hQ
  refine (Category.assoc _ _ _).symm.trans ?_
  refine (congrArg (· ≫ _) hB).trans ?_
  refine (Category.assoc _ _ _).trans ?_
  exact congrArg (_ ≫ ·) ((Category.assoc _ _ _).trans hX)

/-- The algebra of `coefficientSingleMap_eq_forget`, at variables. -/
private lemma xi_chase {C D : Type*} [Category* C] [Category* D] (G : D ⥤ C)
    {a₀ a₁ b₂ b₃ : C} {y₀ y₁ y₂ y₃ y₄ : D} (rσ : a₀ ⟶ a₁) (g₁ : a₁ ⟶ G.obj y₁)
    (g₀ : a₀ ⟶ G.obj y₀) (fσ : y₀ ⟶ y₁) (m₁ : y₁ ⟶ y₂) (m₂ : y₂ ⟶ y₃) (gi₃ : G.obj y₃ ⟶ b₂)
    (rτ : b₂ ⟶ b₃) (fτ : y₃ ⟶ y₄) (gi₄ : G.obj y₄ ⟶ b₃)
    (hs1 : rσ ≫ g₁ = g₀ ≫ G.map fσ) (hs2 : gi₃ ≫ rτ = G.map fτ ≫ gi₄) :
    rσ ≫ (g₁ ≫ G.map (m₁ ≫ m₂) ≫ gi₃) ≫ rτ = g₀ ≫ G.map (fσ ≫ m₁ ≫ m₂ ≫ fτ) ≫ gi₄ := by
  simp only [Category.assoc, G.map_comp, hs2]
  rw [reassoc_of% hs1]

/-- **`coefficientSingleMap` through the underlying abelian sheaves**: it is the identification
of `c_*ℳ[-a]` and `ℳ[-a]` through the single functors of abelian sheaves, under derived global
sections of abelian sheaves. -/
theorem coefficientSingleMap_eq_forget (a : ℤ) (A : RModules X.toRingedSpace) :
    coefficientSingleMap f a A =
      (globalSectionsForgetIso (inverseImageBase f)).hom.app _ ≫
        (derivedAbelianGlobalSections (inverseImageBase f)).map
          ((forgetSingle (inverseImageBase f) a).hom.app
              ((modulePushforward (toInverseImageBase f)).obj A) ≫
            (forgetSingle X.toRingedSpace a).inv.app A) ≫
          (globalSectionsForgetIso X.toRingedSpace).inv.app _ := by
  have hs1 := (globalSectionsForgetIso (inverseImageBase f)).hom.naturality
    ((DerivedCategory.singleFunctor _ a).map (𝟙 _) ≫
      (DerivedCategory.singleFunctorIsoCompQh (RModules (inverseImageBase f)) a).hom.app
        ((modulePushforward (toInverseImageBase f)).obj A) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategorySingleFunctor
        (modulePushforward (toInverseImageBase f)) a).inv.app A))
  have hs2 := (globalSectionsForgetIso X.toRingedSpace).inv.naturality
    ((DerivedCategory.singleFunctorIsoCompQh (RModules X.toRingedSpace) a).inv.app A)
  dsimp only [Functor.comp_map] at hs1 hs2
  rw [coefficientSingleMap_eq, coefficientLerayMap_eq_coefficientForgetMap,
    ← forgetSingle_coefficient]
  unfold coefficientForgetMap
  exact xi_chase (derivedAbelianGlobalSections (inverseImageBase f)) _ _ _ _ _ _ _ _ _ _ hs1
    hs2.symm

/-- The algebra of `coefficientSingleMap_abelianDerivedMap`, at variables. -/
private lemma br_chase {C D : Type*} [Category* C] [Category* D] (G : D ⥤ C)
    {a₀ a₁ b₀ b₁ : C} {y₀ y₁ z₀ z₁ w₀ w₁ : D}
    (g₀ : a₀ ⟶ G.obj y₀) (g₁ : a₁ ⟶ G.obj y₁) (rψ : a₀ ⟶ a₁) (fψ : y₀ ⟶ y₁)
    (S₀ : y₀ ⟶ z₀) (S₁ : y₁ ⟶ z₁) (Si₀ : z₀ ⟶ w₀) (Si₁ : z₁ ⟶ w₁) (Sx₀ : w₀ ⟶ z₀)
    (sψ : z₀ ⟶ z₁) (k₀ : G.obj w₀ ⟶ b₀) (k₁ : G.obj w₁ ⟶ b₁) (ki₀ : b₀ ⟶ G.obj w₀)
    (hn : rψ ≫ g₁ = g₀ ≫ G.map fψ) (hS : fψ ≫ S₁ = S₀ ≫ sψ) (hk : k₀ ≫ ki₀ = 𝟙 _)
    (hSi : Si₀ ≫ Sx₀ = 𝟙 _) :
    (g₀ ≫ G.map (S₀ ≫ Si₀) ≫ k₀) ≫ ki₀ ≫ G.map (Sx₀ ≫ sψ ≫ Si₁) ≫ k₁ =
      rψ ≫ g₁ ≫ G.map (S₁ ≫ Si₁) ≫ k₁ := by
  rw [reassoc_of% hn]
  simp only [Category.assoc, ← G.map_comp_assoc]
  rw [reassoc_of% hk, ← G.map_comp_assoc]
  congr 2
  simp only [Category.assoc]
  rw [reassoc_of% hSi, reassoc_of% hS]

/-- **The comparison of derived global sections along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` is natural in
`f⁻¹𝒪_S`-linear maps read as maps of abelian sheaves.** For `ψ♭ : c_*ℳ ⟶ c_*𝒩`, a morphism of
`f⁻¹𝒪_S`-modules with underlying morphism of abelian sheaves `ψ`, `coefficientSingleMap` carries
derived global sections of `ψ♭` on `(X, f⁻¹𝒪_S)` to the abelian action of `ψ` on `(X, 𝒪_X)`. -/
theorem coefficientSingleMap_abelianDerivedMap (a : ℤ) {A B : RModules X.toRingedSpace}
    (ψf : (modulePushforward (toInverseImageBase f)).obj A ⟶
      (modulePushforward (toInverseImageBase f)).obj B)
    (ψ : (forgetModules X.toRingedSpace).obj A ⟶ (forgetModules X.toRingedSpace).obj B)
    (hψ : (forgetModules (inverseImageBase f)).map ψf = ψ) :
    coefficientSingleMap f a A ≫ abelianDerivedMap X.toRingedSpace a ψ =
      (derivedGlobalSections (inverseImageBase f)).map
          ((DerivedCategory.singleFunctor _ a).map ψf) ≫ coefficientSingleMap f a B := by
  subst hψ
  have hn := (globalSectionsForgetIso (inverseImageBase f)).hom.naturality
    ((DerivedCategory.singleFunctor _ a).map ψf)
  have hS := (forgetSingle (inverseImageBase f) a).hom.naturality ψf
  dsimp only [Functor.comp_map] at hn hS
  rw [coefficientSingleMap_eq_forget, coefficientSingleMap_eq_forget]
  unfold abelianDerivedMap forgetSingleMap
  exact br_chase (derivedAbelianGlobalSections (inverseImageBase f)) _ _ _ _ _ _ _ _ _ _ _ _ _
    hn hS (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _)

/-- **The pullback map along `(X, 𝒪_X) ⟶ (X, f⁻¹𝒪_S)` of the identity of `c_*ℳ` is
compatible with the abelian action of `f⁻¹𝒪_S`-linear maps.** For a morphism `ψ♭ : c_*ℳ ⟶ c_*𝒩`
of `f⁻¹𝒪_S`-modules with underlying morphism of abelian sheaves `ψ`, the square

```
Hⁿ(X♭, c_*ℳ) --pbH(𝟙)--> Hⁿ(X, ℳ)
     | Hⁿ(ψ♭)                | abelianHgroupMap ψ
     v                       v
Hⁿ(X♭, c_*𝒩) --pbH(𝟙)--> Hⁿ(X, 𝒩)
```

commutes, in any placement degree `a`. This is how a de Rham differential, which is
`f⁻¹𝒪_S`-linear but not `𝒪_X`-linear, is moved past pullback maps of cohomology. -/
theorem pullbackHgroup_toInverseImageBase_abelianHgroupMap (a m : ℤ) (n : ℕ) (hn : m - a = n)
    {A B : RModules X.toRingedSpace}
    (ψf : (modulePushforward (toInverseImageBase f)).obj A ⟶
      (modulePushforward (toInverseImageBase f)).obj B)
    (ψ : (forgetModules X.toRingedSpace).obj A ⟶ (forgetModules X.toRingedSpace).obj B)
    (hψ : (forgetModules (inverseImageBase f)).map ψf = ψ) :
    pullbackHgroup (CohomologyPullbackComparison.canonical (toInverseImageBase f)) a m n hn
        (𝟙 ((modulePushforward (toInverseImageBase f)).obj A)) ≫
      abelianHgroupMap X.toRingedSpace a m n hn ψ =
    (Hfunctor (structureSheafRing (inverseImageBase f)) ⊤ n).map ψf ≫
      pullbackHgroup (CohomologyPullbackComparison.canonical (toInverseImageBase f)) a m n hn
        (𝟙 ((modulePushforward (toInverseImageBase f)).obj B)) := by
  have hD := congrArg (DerivedCategory.homologyFunctor AddCommGrpCat.{u} m).map
    (coefficientSingleMap_abelianDerivedMap f a ψf ψ hψ)
  have hc := cohomologyDerivedSingleIso_hom_naturality (inverseImageBase f) ψf a m n hn
  simp only [Functor.map_comp] at hD
  rw [pullbackHgroup_toInverseImageBase_id, pullbackHgroup_toInverseImageBase_id]
  unfold abelianHgroupMap
  rw [← cancel_epi (cohomologyDerivedSingleIso (inverseImageBase f) _ a m n hn).hom]
  simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id_assoc]
  rw [reassoc_of% hD, ← reassoc_of% hc, Iso.hom_inv_id_assoc]

end Stacks.DeRham.GysinCohomologyBaseChange

end
