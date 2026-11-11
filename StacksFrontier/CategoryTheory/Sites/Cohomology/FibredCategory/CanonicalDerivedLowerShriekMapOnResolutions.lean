module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.FibredCategory.CanonicalDerivedLowerShriekMap
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.Algebra.Homology.DerivedCategory.KProjectiveLeftDerived
public import StacksFrontier.Algebra.Homology.Embedding.ExtendMap
public import StacksFrontier.CategoryTheory.Abelian.Projective.ResolutionLift
public import Mathlib.CategoryTheory.Abelian.Projective.Extend
import all Mathlib.Algebra.Homology.Localization
import all Mathlib.Algebra.Homology.DerivedCategory.Basic
import all Mathlib.Algebra.Homology.HomotopyCategory
import all Mathlib.CategoryTheory.Quotient

/-!
# The canonical map of Stacks 08PD on resolutions

Let `G ⊣ R`, `P ⊣ T` and `P' ⊣ T'` be adjunctions between abelian categories with
`T ⋙ R ≅ T'`, and let `LG`, `LP`, `LP'` be left derived functors adjoint to the derived functors
of the exact right adjoints. Remark 08PD of the Stacks project builds a canonical map
`LP'(F') ⟶ LP(F)` out of `t : F' ⟶ R F`: the identification `LP' = LP ∘ LG` followed by `LP`
applied to `LG(F') ⟶ G F' ⟶ F`. This file computes that map on resolutions: if `π' : K' ⟶ F'[0]`
and `π : K ⟶ F[0]` are quasi-isomorphisms and `φ : K' ⟶ R(K)` lifts `t`, then the canonical
map is the map of complexes `P'(K') ⟶ P(K)` whose components are the adjoints of the components
of `φ` (`resolutionMap`), read through `π'`, `π` and the comparisons of the derived functors with
the underived ones.

## Main results

* `Stacks.Homology.DerivedLeftAdjointComp.canonicalMap_eq`: the computation, for adjunctions
  whose derived units factor through the degreewise units (`UnitFac`) and an identification of
  derived functors compatible with the underived one (`CompIsoFac`).
* `Stacks.Sites.FibredCategory.MorphismSituation.canonicalDerivedLowerShriekMap_comp_eq`: the
  computation for the canonical map `Lπ'_!F' ⟶ Lπ_!F` of a situation of Stacks 08PA.
* `Stacks.Sites.FibredCategory.MorphismSituation.isIso_totalComparison_app` and
  `isIso_sourceComparison_app`: the comparisons `Lπ_!K ⟶ π_!K` and `Lπ'_!K ⟶ π'_!K` are
  invertible on K-projective complexes.
* `Stacks.Homology.DerivedLeftAdjointComp.liftCondition_extendLift`: a lift of `t` between
  projective resolutions extends to a lift between their cochain complexes.

## References

* [Stacks Project, Tag 08PD](https://stacks.math.columbia.edu/tag/08PD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace CategoryTheory.Adjunction

variable {C₀ C₁ C₂ : Type*} [Category* C₀] [Category* C₁] [Category* C₂]
  {F₀₁ : C₀ ⥤ C₁} {F₁₂ : C₁ ⥤ C₂} {F₀₂ : C₀ ⥤ C₂}
  {G₁₀ : C₁ ⥤ C₀} {G₂₁ : C₂ ⥤ C₁} {G₂₀ : C₂ ⥤ C₀}
  (adj₀₁ : F₀₁ ⊣ G₁₀) (adj₁₂ : F₁₂ ⊣ G₂₁) (adj₀₂ : F₀₂ ⊣ G₂₀) (e : G₂₁ ⋙ G₁₀ ≅ G₂₀)

/-- The adjoint of `F₁₂(h)` precomposed with the identification `F₁₂ ∘ F₀₁ ≅ F₀₂` of left
adjoints, through the adjunction `F₀₂ ⊣ G₂₀`, is the adjoint of `h` followed by the unit of
`F₁₂ ⊣ G₂₁` and the given isomorphism `G₂₁ ⋙ G₁₀ ≅ G₂₀`. -/
theorem homEquiv_leftAdjointCompIso_inv_app_comp {X₀ : C₀} {X₁ : C₁} (h : F₀₁.obj X₀ ⟶ X₁) :
    adj₀₂.homEquiv X₀ (F₁₂.obj X₁)
        ((leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).inv.app X₀ ≫ F₁₂.map h) =
      adj₀₁.homEquiv X₀ X₁ h ≫ G₁₀.map (adj₁₂.unit.app X₁) ≫ e.hom.app (F₁₂.obj X₁) := by
  have h₁ := unit_conjugateEquiv (adj₀₁.comp adj₁₂) adj₀₂
    (leftAdjointCompIso adj₀₁ adj₁₂ adj₀₂ e).inv X₀
  rw [conjugateEquiv_leftAdjointCompIso_inv] at h₁
  rw [homEquiv_unit, Functor.map_comp, ← Category.assoc, ← h₁, homEquiv_unit]
  have h₂ := e.hom.naturality (F₁₂.map h)
  have h₃ := adj₁₂.unit.naturality h
  dsimp at h₂ h₃ ⊢
  rw [Category.assoc, ← h₂, comp_unit_app, Category.assoc, ← G₁₀.map_comp_assoc, ← h₃,
    G₁₀.map_comp, Category.assoc, Category.assoc]

end CategoryTheory.Adjunction

namespace Stacks.Homology.DerivedLeftAdjointComp


variable {A' A Z : Type*} [Category* A'] [Category* A] [Category* Z]
  [Abelian A'] [Abelian A] [Abelian Z]
  [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory Z]

section UnitFormula

variable {G : A' ⥤ A} {R : A ⥤ A'} (adj : G ⊣ R) [G.Additive] [R.Additive]
  [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  {LG : DerivedCategory A' ⥤ DerivedCategory A}
  (α : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  (dadj : LG ⊣ R.mapDerivedCategory)

/-- The unit of a derived adjunction factors through the degreewise unit. -/
def UnitFac : Prop :=
  ∀ M : HomotopyCategory A' (ComplexShape.up ℤ),
    dadj.unit.app (DerivedCategory.Qh.obj M) ≫ R.mapDerivedCategory.map (α.app M) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app M) ≫
        R.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj M)

variable {adj α dadj}

/-- Under `UnitFac`, the adjoint of a map out of `LG(M)` that starts with the comparison
`α_M : LG(M) ⟶ G(M)` is computed by the degreewise unit. -/
theorem homEquiv_app_comp (h : UnitFac adj α dadj) (M : HomotopyCategory A' (ComplexShape.up ℤ))
    {Y : DerivedCategory A}
    (k : DerivedCategory.Qh.obj ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ⟶ Y) :
    dadj.homEquiv _ _ (α.app M ≫ k) =
      DerivedCategory.Qh.map ((adj.mapHomotopyCategory (ComplexShape.up ℤ)).unit.app M) ≫
        R.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
          R.mapDerivedCategory.map k := by
  rw [Adjunction.homEquiv_unit, Functor.map_comp, ← Category.assoc, h M, Category.assoc]

/-- `homEquiv_app_comp` at the image of a cochain complex in the homotopy category. -/
theorem homEquiv_app_comp_quotient (h : UnitFac adj α dadj) (K : CochainComplex A' ℤ)
    {Y : DerivedCategory A}
    (k : DerivedCategory.Qh.obj ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K)) ⟶ Y) :
    dadj.homEquiv _ _ (α.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K) ≫ k) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex adj.unit (ComplexShape.up ℤ)).app K)) ≫
        R.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K)) ≫
          R.mapDerivedCategory.map k :=
  homEquiv_app_comp h _ k

end UnitFormula


section Canonical

variable {G : A' ⥤ A} {R : A ⥤ A'} (adjG : G ⊣ R)
  {P : A ⥤ Z} {T : Z ⥤ A} (adjP : P ⊣ T)
  {P' : A' ⥤ Z} {T' : Z ⥤ A'} (adjP' : P' ⊣ T')
  [G.Additive] [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [P.Additive] [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T]
  [P'.Additive] [T'.Additive] [PreservesFiniteLimits T'] [PreservesFiniteColimits T']
  (e : T ⋙ R ≅ T')
  {LG : DerivedCategory A' ⥤ DerivedCategory A}
  (αG : DerivedCategory.Qh ⋙ LG ⟶ G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  (dG : LG ⊣ R.mapDerivedCategory)
  {LP : DerivedCategory A ⥤ DerivedCategory Z}
  (αP : DerivedCategory.Qh ⋙ LP ⟶ P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  (dP : LP ⊣ T.mapDerivedCategory)
  {LP' : DerivedCategory A' ⥤ DerivedCategory Z}
  (αP' : DerivedCategory.Qh ⋙ LP' ⟶
    P'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  (dP' : LP' ⊣ T'.mapDerivedCategory)
  (eD : T.mapDerivedCategory ⋙ R.mapDerivedCategory ≅ T'.mapDerivedCategory)

/-- The comparison `LG(F'[0]) ⟶ G(F')[0]`. -/
def singleComparison (F' : A') :
    LG.obj ((DerivedCategory.singleFunctor A' 0).obj F') ⟶
      (DerivedCategory.singleFunctor A 0).obj (G.obj F') :=
  LG.map ((DerivedCategory.singleFunctorIsoCompQh A' 0).hom.app F') ≫
    αG.app ((HomotopyCategory.singleFunctor A' 0).obj F') ≫
    DerivedCategory.Qh.map ((G.mapHomotopyCategorySingleFunctor 0).hom.app F') ≫
    (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app (G.obj F')

/-- The canonical map `LP'(F'[0]) ⟶ LP(F[0])` attached to `t : F' ⟶ R F`. -/
def canonicalMap (F : A) (F' : A') (t : F' ⟶ R.obj F) :
    LP'.obj ((DerivedCategory.singleFunctor A' 0).obj F') ⟶
      LP.obj ((DerivedCategory.singleFunctor A 0).obj F) :=
  (Adjunction.leftAdjointCompIso dG dP dP' eD).inv.app _ ≫
    LP.map (singleComparison αG F' ≫
      (DerivedCategory.singleFunctor A 0).map ((adjG.homEquiv F' F).symm t))

variable {K' : CochainComplex A' ℤ} {K : CochainComplex A ℤ}

omit [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory Z] in
/-- The degreewise map `P'(K') ⟶ P(K)` attached to a chain map `φ : K' ⟶ R(K)`. -/
def resolutionMap (φ : K' ⟶ (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :
    (P'.mapHomologicalComplex (ComplexShape.up ℤ)).obj K' ⟶
      (P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K where
  f i := (Adjunction.leftAdjointCompIso adjG adjP adjP' e).inv.app (K'.X i) ≫
    P.map (G.map (φ.f i) ≫ adjG.counit.app (K.X i))
  comm' i j _ := by
    have h1 := (Adjunction.leftAdjointCompIso adjG adjP adjP' e).inv.naturality (K'.d i j)
    have h2 := φ.comm i j
    have h3 := adjG.counit.naturality (K.d i j)
    dsimp at h1 h2 h3 ⊢
    rw [reassoc_of% h1]
    simp only [Category.assoc, ← P.map_comp]
    congr 2
    rw [← h3, ← G.map_comp_assoc, h2, G.map_comp_assoc]


omit [Abelian Z] [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory Z] in
/-- The map `F'[0] ⟶ R(F[0])` attached to `t : F' ⟶ R F`, on complexes. -/
def singleLiftTarget (R : A ⥤ A') [R.Additive] {F : A} {F' : A'} (t : F' ⟶ R.obj F) :
    (HomologicalComplex.single A' (ComplexShape.up ℤ) 0).obj F' ⟶
      (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj F) :=
  (HomologicalComplex.single A' (ComplexShape.up ℤ) 0).map t ≫
    (HomologicalComplex.singleMapHomologicalComplex R (ComplexShape.up ℤ) 0).inv.app F

omit [Abelian Z] [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory Z] in
/-- The condition that `φ : K' ⟶ R(K)` lifts `t` through the augmentations `π'` and `π`. -/
def LiftCondition (R : A ⥤ A') [R.Additive] {F : A} {F' : A'} (t : F' ⟶ R.obj F)
    (π' : K' ⟶ (HomologicalComplex.single A' (ComplexShape.up ℤ) 0).obj F')
    (π : K ⟶ (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj F)
    (φ : K' ⟶ (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) : Prop :=
  φ ≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).map π = π' ≫ singleLiftTarget R t

omit [Abelian Z] [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory Z] in
/-- A chain map `ψ : P' ⟶ R(P)` between the complexes of two projective resolutions, extended to
a cochain map between their cochain complexes indexed by `ℤ`. -/
def extendLift (R : A ⥤ A') [R.Additive] {F : A} {F' : A'}
    (P' : ProjectiveResolution F') (P : ProjectiveResolution F)
    (ψ : P'.complex ⟶ (R.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex) :
    P'.cochainComplex ⟶ (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj P.cochainComplex :=
  HomologicalComplex.extendMap ψ ComplexShape.embeddingDownNat ≫
    (HomologicalComplex.mapHomologicalComplexExtendIso R P.complex
      ComplexShape.embeddingDownNat).hom

omit [Abelian Z] [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory Z] in
/-- The components of `extendLift` in nonpositive degrees are those of the chain map. -/
theorem extendLift_f (R : A ⥤ A') [R.Additive] {F : A} {F' : A'}
    (P' : ProjectiveResolution F') (P : ProjectiveResolution F)
    (ψ : P'.complex ⟶ (R.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
    (n : ℤ) (m : ℕ) (h : -(m : ℤ) = n) :
    (extendLift R P' P ψ).f n =
      (P'.cochainComplexXIso n m h).hom ≫ ψ.f m ≫ R.map (P.cochainComplexXIso n m h).inv :=
  HomologicalComplex.extendMap_mapHomologicalComplexExtendIso_f R P.complex ψ
    ComplexShape.embeddingDownNat h

omit [Abelian Z] [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory Z] in
/-- **A lift of `t` between projective resolutions gives a lift on their cochain complexes.**
Extending a chain map `ψ : P' ⟶ R(P)` compatible with the augmentations to complexes indexed by
`ℤ` gives a cochain map compatible with the augmentations `P'.π'` and `P.π'`. -/
theorem liftCondition_extendLift (R : A ⥤ A') [R.Additive] {F : A} {F' : A'} (t : F' ⟶ R.obj F)
    (P' : ProjectiveResolution F') (P : ProjectiveResolution F)
    (ψ : P'.complex ⟶ (R.mapHomologicalComplex (ComplexShape.down ℕ)).obj P.complex)
    (hψ : ψ ≫ R.mapAugmentation P.π = P'.π ≫ (ChainComplex.single₀ A').map t) :
    LiftCondition R t P'.π' P.π' (extendLift R P' P ψ) := by
  have h0 := congrArg (fun g => HomologicalComplex.Hom.f g 0) hψ
  simp only [HomologicalComplex.comp_f, Functor.mapAugmentation_f_zero,
    ChainComplex.single₀_map_f_zero] at h0
  ext n
  by_cases hn : n = 0
  · subst hn
    rw [HomologicalComplex.comp_f, HomologicalComplex.comp_f, Functor.mapHomologicalComplex_map_f,
      extendLift_f R P' P ψ 0 0 (by simp), P.π'_f_zero, P'.π'_f_zero, singleLiftTarget,
      HomologicalComplex.comp_f, HomologicalComplex.single_map_f_self,
      HomologicalComplex.singleMapHomologicalComplex_inv_app_self]
    simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
    rw [← R.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id, Category.id_comp]
    have h1 : ψ.f 0 ≫ R.map (P.π.f 0 ≫
        (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv) =
        P'.π.f 0 ≫ t ≫ R.map (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F).inv :=
      (congrArg (ψ.f 0 ≫ ·) (R.map_comp _ _)).trans
        ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) h0).trans (Category.assoc _ _ _)))
    exact (congrArg (_ ≫ ·) h1).trans (congrArg (_ ≫ ·)
      ((congrArg (P'.π.f 0 ≫ ·) (Iso.inv_hom_id_assoc _ _).symm).trans (Category.assoc _ _ _).symm))
  · exact (R.map_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n
      hn)).eq_of_tgt _ _

omit [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory Z] in
/-- The transpose identity behind the canonical map: on complexes, the transpose of `φ`
through the comparison is the degreewise one. -/
theorem single_lift_eq {F : A} {F' : A'} (t : F' ⟶ R.obj F)
    (π' : K' ⟶ (HomologicalComplex.single A' (ComplexShape.up ℤ) 0).obj F')
    (π : K ⟶ (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj F)
    (φ : K' ⟶ (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (hφ : LiftCondition R t π' π φ) :
    (NatTrans.mapHomologicalComplex adjG.unit (ComplexShape.up ℤ)).app K' ≫
        (R.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map π' ≫
            (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F' ≫
            (HomologicalComplex.single A (ComplexShape.up ℤ) 0).map
              ((adjG.homEquiv F' F).symm t)) =
      φ ≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).map π := by
  rw [show φ ≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).map π = _ from hφ, singleLiftTarget]
  ext n
  by_cases hn : n = 0
  · subst hn
    have := (NatTrans.mapHomologicalComplex adjG.unit (ComplexShape.up ℤ)).naturality π'
    have h0 := congrArg (fun f => HomologicalComplex.Hom.f f 0) this
    simp only [HomologicalComplex.comp_f] at h0 ⊢
    simp [HomologicalComplex.single_map_f_self, Adjunction.homEquiv_counit] at h0 ⊢
  · exact (R.map_isZero (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 F n
      hn)).eq_of_tgt _ _

/-- The comparison of the derived factorization with the underived one, read on the homotopy
category. -/
def CompIsoFac : Prop :=
  ∀ M : HomotopyCategory Z (ComplexShape.up ℤ),
    R.mapDerivedCategoryFactorsh.inv.app ((T.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        R.mapDerivedCategory.map (T.mapDerivedCategoryFactorsh.inv.app M) ≫
        eD.hom.app (DerivedCategory.Qh.obj M) =
      DerivedCategory.Qh.map
          ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app M) ≫
        T'.mapDerivedCategoryFactorsh.inv.app M

omit [Abelian A'] [Abelian A] in
/-- The comparison of a derived exact functor with the underived one, at the image of a complex
in the homotopy category, is the comparison at the complex. -/
private theorem mapDerivedCategoryFactorsh_app_quotient {B C : Type*} [Category* B] [Category* C]
    [Abelian B] [Abelian C] [HasDerivedCategory B] [HasDerivedCategory C] (F : B ⥤ C) [F.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F] (L : CochainComplex B ℤ) :
    F.mapDerivedCategoryFactorsh.app ((HomotopyCategory.quotient B (ComplexShape.up ℤ)).obj L) =
      F.mapDerivedCategoryFactors.app L := by
  ext
  rw [Iso.app_hom, Functor.mapDerivedCategoryFactorsh_hom_app]
  have h1 : (DerivedCategory.quotientCompQhIso B).hom.app L = 𝟙 _ := rfl
  have h2 : (DerivedCategory.quotientCompQhIso C).inv.app
      ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L) = 𝟙 _ := rfl
  have h3 : (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).inv.app L = 𝟙 _ := rfl
  rw [h1, h2, h3]
  refine (congrArg (· ≫ _) (F.mapDerivedCategory.map_id _)).trans ((Category.id_comp _).trans ?_)
  refine (congrArg (_ ≫ ·) ((Category.id_comp _).trans (DerivedCategory.Qh.map_id _))).trans ?_
  exact Category.comp_id _

/-- The identification of derived functors obtained by lifting an isomorphism of underived
functors along the localization satisfies `CompIsoFac`. -/
theorem compIsoFac_liftNatIso :
    CompIsoFac e (Localization.liftNatIso DerivedCategory.Q
      (HomologicalComplex.quasiIso Z (ComplexShape.up ℤ))
      ((T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ R.mapDerivedCategory)
      (T'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (T.mapDerivedCategory ⋙ R.mapDerivedCategory) T'.mapDerivedCategory
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ R.mapDerivedCategoryFactors ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ))
          DerivedCategory.Q)) := by
  intro M
  obtain ⟨K, rfl⟩ := HomotopyCategory.quotient_obj_surjective M
  have hT := congrArg Iso.inv (mapDerivedCategoryFactorsh_app_quotient T K)
  have hR := congrArg Iso.inv (mapDerivedCategoryFactorsh_app_quotient R
    ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
  have hT' := congrArg Iso.inv (mapDerivedCategoryFactorsh_app_quotient T' K)
  simp only [Iso.app_inv] at hT hR hT'
  have hL := Localization.liftNatTrans_app DerivedCategory.Q
      (HomologicalComplex.quasiIso Z (ComplexShape.up ℤ))
      ((T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ R.mapDerivedCategory)
      (T'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      (T.mapDerivedCategory ⋙ R.mapDerivedCategory) T'.mapDerivedCategory
      (Functor.associator _ _ _ ≪≫
        Functor.isoWhiskerLeft _ R.mapDerivedCategoryFactors ≪≫
        (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ))
          DerivedCategory.Q).hom K
  rw [hT, hT', Localization.liftNatIso_hom]
  refine (congrArg₂ (fun x y => x ≫ y) hR (congrArg (fun z => _ ≫ z) hL)).trans ?_
  have l1 : (Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso Z (ComplexShape.up ℤ))
      ((T.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ R.mapDerivedCategory)
      (T.mapDerivedCategory ⋙ R.mapDerivedCategory)).hom.app K =
      R.mapDerivedCategory.map (T.mapDerivedCategoryFactors.hom.app K) := rfl
  have l2 : (Localization.Lifting.iso DerivedCategory.Q
      (HomologicalComplex.quasiIso Z (ComplexShape.up ℤ))
      (T'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q)
      T'.mapDerivedCategory).inv.app K = T'.mapDerivedCategoryFactors.inv.app K := rfl
  have l3 : DerivedCategory.Qh.map
      ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app
        ((HomotopyCategory.quotient Z (ComplexShape.up ℤ)).obj K)) =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app
          K) :=
    rfl
  rw [l1, l2, l3]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.associator_hom_app,
    Functor.isoWhiskerLeft_hom, Functor.whiskerLeft_app, Iso.symm_hom,
    Functor.associator_inv_app, Functor.isoWhiskerRight_hom, Functor.whiskerRight_app,
    Category.id_comp]
  have fin : R.mapDerivedCategoryFactors.inv.app ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      K) ≫
      R.mapDerivedCategory.map (T.mapDerivedCategoryFactors.inv.app K) ≫
        R.mapDerivedCategory.map (T.mapDerivedCategoryFactors.hom.app K) ≫
          (R.mapDerivedCategoryFactors.hom.app ((T.mapHomologicalComplex (ComplexShape.up ℤ)).obj
              K) ≫
              DerivedCategory.Q.map
                ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app K)) ≫
            T'.mapDerivedCategoryFactors.inv.app K =
      DerivedCategory.Q.map ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app
          K) ≫
        T'.mapDerivedCategoryFactors.inv.app K := by
    rw [← Functor.map_comp_assoc, Iso.inv_hom_id_app]
    refine (congrArg (_ ≫ ·) ((congrArg (· ≫ _) (R.mapDerivedCategory.map_id _)).trans
      (Category.id_comp _))).trans ?_
    rw [Category.assoc, Iso.inv_hom_id_app_assoc]
  exact fin

variable {adjG adjP adjP' αG αP αP' dG dP dP' e eD}

omit [Abelian Z] [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory Z] in
/-- A chain map into a complex concentrated in degree zero, read in the homotopy category with
target spelled through `HomotopyCategory.singleFunctor`. -/
def singleQuot {X : A'} {L : CochainComplex A' ℤ}
    (π' : L ⟶ (HomologicalComplex.single A' (ComplexShape.up ℤ) 0).obj X) :
    (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj L ⟶
      (HomotopyCategory.singleFunctor A' 0).obj X :=
  (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map π'

omit [Abelian Z] [R.Additive] [PreservesFiniteLimits R] [PreservesFiniteColimits R]
  [HasDerivedCategory A'] [HasDerivedCategory A] [HasDerivedCategory Z] in
/-- An additive functor applied to `singleQuot` is `singleQuot` of the functor applied degreewise,
up to the comparison of single complexes. -/
theorem map_singleQuot (G : A' ⥤ A) [G.Additive] {X : A'} {L : CochainComplex A' ℤ}
    (π' : L ⟶ (HomologicalComplex.single A' (ComplexShape.up ℤ) 0).obj X) :
    (G.mapHomotopyCategory (ComplexShape.up ℤ)).map (singleQuot π') ≫
        (G.mapHomotopyCategorySingleFunctor 0).hom.app X =
      singleQuot ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map π' ≫
        (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app X) := by
  have h1 : (HomotopyCategory.singleFunctorPostcompQuotientIso A' 0).hom.app X = 𝟙 _ := rfl
  have h2 : (G.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.app
      ((CochainComplex.singleFunctor A' 0).obj X) = 𝟙 _ := rfl
  have h3 : (HomotopyCategory.singleFunctorPostcompQuotientIso A 0).inv.app (G.obj X)
      = 𝟙 _ := rfl
  dsimp only [singleQuot, Functor.mapHomotopyCategorySingleFunctor]
  simp only [Iso.trans_hom, NatTrans.comp_app, Functor.isoWhiskerRight_hom,
    Functor.whiskerRight_app, Functor.associator_hom_app, Functor.isoWhiskerLeft_hom,
    Functor.whiskerLeft_app, Functor.associator_inv_app, Iso.symm_hom, h1, h2, h3,
    Category.id_comp]
  refine (congrArg (_ ≫ ·) ?_).trans ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map_comp
    ((G.mapHomologicalComplex (ComplexShape.up ℤ)).map π')
    ((HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app X)).symm
  refine ((congrArg (· ≫ _) ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map_id _)).trans
    (Category.id_comp _)).trans ?_
  refine (Category.id_comp _).trans ?_
  refine (congrArg (_ ≫ ·) (Category.id_comp _)).trans ?_
  exact Category.comp_id _

/-- **The canonical map of Stacks 08PD on resolutions.** Let `π' : K' ⟶ F'[0]` and
`π : K ⟶ F[0]` be quasi-isomorphisms and `φ : K' ⟶ R(K)` a lift of `t : F' ⟶ R F`. Then, read
through `π'`, `π` and the comparisons `α_P'`, `α_P` (the latter invertible at `K`), the canonical
map `canonicalMap` is the map of complexes `P'(K') ⟶ P(K)` assembled from `φ`, the counit of
`G ⊣ R` and the identification of the composite left adjoints (`resolutionMap`). -/
theorem canonicalMap_eq (hG : UnitFac adjG αG dG) (hP : UnitFac adjP αP dP)
    (hP' : UnitFac adjP' αP' dP') (he : CompIsoFac e eD)
    {F : A} {F' : A'} (t : F' ⟶ R.obj F)
    (π' : K' ⟶ (HomologicalComplex.single A' (ComplexShape.up ℤ) 0).obj F')
    (π : K ⟶ (HomologicalComplex.single A (ComplexShape.up ℤ) 0).obj F)
    (φ : K' ⟶ (R.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (hφ : LiftCondition R t π' π φ)
    (hK : IsIso (αP.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K))) :
    LP'.map (DerivedCategory.Qh.map (singleQuot π') ≫
        (DerivedCategory.singleFunctorIsoCompQh A' 0).inv.app F') ≫
        canonicalMap adjG αG dG dP dP' eD F F' t =
      αP'.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K') ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient Z (ComplexShape.up ℤ)).map
          (resolutionMap adjG adjP adjP' e φ)) ≫
        @CategoryTheory.inv _ _ _ _ (αP.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
            K))
          hK ≫
        LP.map (DerivedCategory.Qh.map (singleQuot π) ≫
          (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app F) := by
  apply (dP'.homEquiv _ _).injective
  have L2 : LG.map (DerivedCategory.Qh.map (singleQuot π') ≫
        (DerivedCategory.singleFunctorIsoCompQh A' 0).inv.app F') ≫ singleComparison αG F' =
      αG.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K') ≫
        DerivedCategory.Qh.map (singleQuot ((G.mapHomologicalComplex _).map π' ≫
            (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F')) ≫
        (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app (G.obj F') := by
    have hn : LG.map (DerivedCategory.Qh.map (singleQuot π')) ≫
        αG.app ((HomotopyCategory.singleFunctor A' 0).obj F') =
        αG.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K') ≫
          DerivedCategory.Qh.map ((G.mapHomotopyCategory (ComplexShape.up ℤ)).map
            (singleQuot π')) := αG.naturality _
    simp only [singleComparison, Functor.map_comp, Category.assoc]
    refine (congrArg (_ ≫ ·) ((LG.map_comp_assoc _ _ _).symm.trans
      ((congrArg (fun x => LG.map x ≫ _)
        (Iso.inv_hom_id_app (DerivedCategory.singleFunctorIsoCompQh A' 0) F')).trans
        ((congrArg (· ≫ _) (LG.map_id _)).trans (Category.id_comp _))))).trans ?_
    rw [reassoc_of% hn, ← DerivedCategory.Qh.map_comp_assoc, map_singleQuot]
  set tb := (adjG.homEquiv F' F).symm t with htb
  set X := (G.mapHomologicalComplex (ComplexShape.up ℤ)).map π' ≫
    (HomologicalComplex.singleMapHomologicalComplex G (ComplexShape.up ℤ) 0).hom.app F' with hX
  set qK' := (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K' with hqK'
  set qK := (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj K with hqK
  -- the chain-level identity behind the left-hand side
  have key : (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex adjG.unit (ComplexShape.up ℤ)).app K') ≫
      (R.mapHomotopyCategory (ComplexShape.up ℤ)).map (singleQuot X) ≫
        (R.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.singleFunctor A 0).map tb) =
      (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map φ ≫
        (R.mapHomotopyCategory (ComplexShape.up ℤ)).map (singleQuot π) := by
    have := single_lift_eq adjG t π' π φ hφ
    change (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex adjG.unit (ComplexShape.up ℤ)).app K') ≫
        (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map X) ≫
        (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map
            ((HomologicalComplex.single A (ComplexShape.up ℤ) 0).map tb)) =
      (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map φ ≫
        (HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map
          ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map π)
    simp only [← Functor.map_comp, hX, Category.assoc]
    exact congrArg _ this
  have L3 : DerivedCategory.Qh.map ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex adjG.unit (ComplexShape.up ℤ)).app K')) ≫
      R.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj qK') ≫
      R.mapDerivedCategory.map (DerivedCategory.Qh.map (singleQuot X) ≫
        (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app (G.obj F') ≫
        (DerivedCategory.singleFunctor A 0).map tb) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map φ) ≫
        R.mapDerivedCategoryFactorsh.inv.app qK ≫
        R.mapDerivedCategory.map (DerivedCategory.Qh.map (singleQuot π) ≫
          (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app F) := by
    have hs : DerivedCategory.Qh.map ((HomotopyCategory.singleFunctor A 0).map tb) ≫
        (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app F =
        (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app (G.obj F') ≫
          (DerivedCategory.singleFunctor A 0).map tb :=
      (DerivedCategory.singleFunctorIsoCompQh A 0).inv.naturality tb
    have hR := fun {M N : HomotopyCategory A (ComplexShape.up ℤ)} (y : M ⟶ N) =>
      (R.mapDerivedCategoryFactorsh.inv.naturality y)
    simp only [Functor.comp_map] at hR
    have key' : DerivedCategory.Qh.map
          ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex adjG.unit (ComplexShape.up ℤ)).app K')) ≫
        DerivedCategory.Qh.map ((R.mapHomotopyCategory (ComplexShape.up ℤ)).map (singleQuot X)) ≫
        DerivedCategory.Qh.map ((R.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.singleFunctor A 0).map tb)) =
        DerivedCategory.Qh.map ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map φ) ≫
          DerivedCategory.Qh.map ((R.mapHomotopyCategory (ComplexShape.up ℤ)).map
            (singleQuot π)) := by
      exact ((congrArg (fun x => _ ≫ x) (DerivedCategory.Qh.map_comp _ _).symm).trans
        (DerivedCategory.Qh.map_comp _ _).symm).trans
        ((congrArg DerivedCategory.Qh.map key).trans (DerivedCategory.Qh.map_comp _ _))
    rw [← hs]
    simp only [Functor.map_comp]
    refine (congrArg (_ ≫ ·) ((reassoc_of% (hR (M := (G.mapHomotopyCategory
      (ComplexShape.up ℤ)).obj qK') (singleQuot X))) _).symm).trans ?_
    refine (congrArg (fun x => _ ≫ _ ≫ x)
      ((reassoc_of% (hR ((HomotopyCategory.singleFunctor A 0).map tb))) _).symm).trans ?_
    refine Eq.trans ?_ (congrArg (_ ≫ ·) ((reassoc_of% (hR (M := qK) (singleQuot π))) _))
    exact (reassoc_of% key') _
  set qπ := DerivedCategory.Qh.map (singleQuot π) ≫
    (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app F with hqπ
  have LHS : dP'.homEquiv _ _ (LP'.map (DerivedCategory.Qh.map (singleQuot π') ≫
        (DerivedCategory.singleFunctorIsoCompQh A' 0).inv.app F') ≫
        canonicalMap adjG αG dG dP dP' eD F F' t) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map φ) ≫
        R.mapDerivedCategoryFactorsh.inv.app qK ≫ R.mapDerivedCategory.map qπ ≫
        R.mapDerivedCategory.map (dP.unit.app _) ≫ eD.hom.app _ := by
    calc _ = (DerivedCategory.Qh.map (singleQuot π') ≫
            (DerivedCategory.singleFunctorIsoCompQh A' 0).inv.app F') ≫
            dP'.homEquiv _ _ (canonicalMap adjG αG dG dP dP' eD F F' t) :=
          Adjunction.homEquiv_naturality_left _ _ _
      _ = (DerivedCategory.Qh.map (singleQuot π') ≫
            (DerivedCategory.singleFunctorIsoCompQh A' 0).inv.app F') ≫
            (dG.homEquiv _ _ (singleComparison αG F' ≫ (DerivedCategory.singleFunctor A 0).map tb) ≫
              R.mapDerivedCategory.map (dP.unit.app _) ≫ eD.hom.app _) :=
          congrArg (fun x => _ ≫ x)
            (Adjunction.homEquiv_leftAdjointCompIso_inv_app_comp _ _ _ _ _)
      _ = dG.homEquiv _ _ (LG.map (DerivedCategory.Qh.map (singleQuot π') ≫
            (DerivedCategory.singleFunctorIsoCompQh A' 0).inv.app F') ≫
              singleComparison αG F' ≫ (DerivedCategory.singleFunctor A 0).map tb) ≫
            R.mapDerivedCategory.map (dP.unit.app _) ≫ eD.hom.app _ :=
          (Category.assoc _ _ _).symm.trans
            (congrArg (fun x => x ≫ _) (Adjunction.homEquiv_naturality_left _ _ _).symm)
      _ = dG.homEquiv _ _ (αG.app ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K') ≫
            DerivedCategory.Qh.map (singleQuot X) ≫
              (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app (G.obj F') ≫
              (DerivedCategory.singleFunctor A 0).map tb) ≫
            R.mapDerivedCategory.map (dP.unit.app _) ≫ eD.hom.app _ := by
          congr 2
          exact ((Category.assoc _ _ _).symm.trans (congrArg (fun x => x ≫ _) L2)).trans
            (by simp only [Category.assoc])
      _ = (DerivedCategory.Qh.map ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex adjG.unit (ComplexShape.up ℤ)).app K')) ≫
            R.mapDerivedCategoryFactorsh.inv.app ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj
                qK') ≫
            R.mapDerivedCategory.map (DerivedCategory.Qh.map (singleQuot X) ≫
              (DerivedCategory.singleFunctorIsoCompQh A 0).inv.app (G.obj F') ≫
              (DerivedCategory.singleFunctor A 0).map tb)) ≫
            R.mapDerivedCategory.map (dP.unit.app _) ≫ eD.hom.app _ :=
          congrArg (fun x => x ≫ _) (homEquiv_app_comp_quotient hG K' _)
      _ = _ := by
          rw [L3]
          simp only [Category.assoc]
  have RHS := homEquiv_app_comp_quotient hP' K'
    (DerivedCategory.Qh.map ((HomotopyCategory.quotient Z (ComplexShape.up ℤ)).map
          (resolutionMap adjG adjP adjP' e φ)) ≫
        @CategoryTheory.inv _ _ _ _ (αP.app qK) hK ≫ LP.map qπ)
  rw [LHS, RHS]
  set M := (P.mapHomotopyCategory (ComplexShape.up ℤ)).obj qK with hM
  set y := @CategoryTheory.inv _ _ _ _ (αP.app qK) hK ≫ LP.map qπ with hy
  have hu : dP.unit.app (DerivedCategory.Qh.obj qK) ≫ T.mapDerivedCategory.map (LP.map qπ) =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex adjP.unit (ComplexShape.up ℤ)).app K)) ≫
        T.mapDerivedCategoryFactorsh.inv.app M ≫ T.mapDerivedCategory.map y := by
    have := homEquiv_app_comp_quotient hP K y
    rw [hy, IsIso.hom_inv_id_assoc, Adjunction.homEquiv_unit] at this
    exact this
  have e1 : R.mapDerivedCategory.map qπ ≫ R.mapDerivedCategory.map (dP.unit.app _) =
      R.mapDerivedCategory.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient A
          (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex adjP.unit
            (ComplexShape.up ℤ)).app K))) ≫
        R.mapDerivedCategory.map (T.mapDerivedCategoryFactorsh.inv.app M) ≫
        R.mapDerivedCategory.map (T.mapDerivedCategory.map y) := by
    exact (R.mapDerivedCategory.map_comp _ _).symm.trans
      ((congrArg R.mapDerivedCategory.map ((dP.unit.naturality qπ).trans hu)).trans
        ((R.mapDerivedCategory.map_comp _ _).trans
          (congrArg (fun x => _ ≫ x) (R.mapDerivedCategory.map_comp _ _))))
  have e2 : R.mapDerivedCategory.map (T.mapDerivedCategory.map y) ≫ eD.hom.app _ =
      eD.hom.app (DerivedCategory.Qh.obj M) ≫ T'.mapDerivedCategory.map y :=
    eD.hom.naturality y
  have e3 : R.mapDerivedCategoryFactorsh.inv.app qK ≫
      R.mapDerivedCategory.map (DerivedCategory.Qh.map ((HomotopyCategory.quotient A
          (ComplexShape.up ℤ)).map ((NatTrans.mapHomologicalComplex adjP.unit
            (ComplexShape.up ℤ)).app K))) =
      DerivedCategory.Qh.map ((R.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex adjP.unit (ComplexShape.up ℤ)).app K))) ≫
        R.mapDerivedCategoryFactorsh.inv.app ((T.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) :=
    (R.mapDerivedCategoryFactorsh.inv.naturality _).symm
  have e4 : T'.mapDerivedCategoryFactorsh.inv.app
        ((P'.mapHomotopyCategory (ComplexShape.up ℤ)).obj
          ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K')) ≫
      T'.mapDerivedCategory.map (DerivedCategory.Qh.map
        ((HomotopyCategory.quotient Z (ComplexShape.up ℤ)).map (resolutionMap adjG adjP adjP' e
            φ))) =
      DerivedCategory.Qh.map ((T'.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient Z (ComplexShape.up ℤ)).map (resolutionMap adjG adjP adjP' e
            φ))) ≫
        T'.mapDerivedCategoryFactorsh.inv.app M :=
    (T'.mapDerivedCategoryFactorsh.inv.naturality _).symm
  have key2 : DerivedCategory.Qh.map ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map φ) ≫
      DerivedCategory.Qh.map ((R.mapHomotopyCategory (ComplexShape.up ℤ)).map
          ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map
            ((NatTrans.mapHomologicalComplex adjP.unit (ComplexShape.up ℤ)).app K))) ≫
      DerivedCategory.Qh.map ((Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).hom.app M)
          =
      DerivedCategory.Qh.map ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex adjP'.unit (ComplexShape.up ℤ)).app K')) ≫
      DerivedCategory.Qh.map ((T'.mapHomotopyCategory (ComplexShape.up ℤ)).map
        ((HomotopyCategory.quotient Z (ComplexShape.up ℤ)).map (resolutionMap adjG adjP adjP' e
            φ))) := by
    have hc : φ ≫ (R.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex adjP.unit (ComplexShape.up ℤ)).app K) ≫
        (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).hom.app
          ((P.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
        (NatTrans.mapHomologicalComplex adjP'.unit (ComplexShape.up ℤ)).app K' ≫
          (T'.mapHomologicalComplex (ComplexShape.up ℤ)).map (resolutionMap adjG adjP adjP' e φ) :=
              by
      ext i
      have := Adjunction.homEquiv_leftAdjointCompIso_inv_app_comp adjG adjP adjP' e
        ((adjG.homEquiv _ _).symm (φ.f i))
      rw [Equiv.apply_symm_apply, Adjunction.homEquiv_unit, Adjunction.homEquiv_counit] at this
      simpa [resolutionMap] using this.symm
    have := congrArg (fun f => DerivedCategory.Qh.map
      ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map f)) hc
    simp only [Functor.map_comp] at this
    exact this
  refine (congrArg (fun x => _ ≫ _ ≫ x) ((reassoc_of% e1) _)).trans ?_
  refine (congrArg (fun x => _ ≫ _ ≫ _ ≫ _ ≫ x) e2).trans ?_
  refine (congrArg (fun x => _ ≫ x) ((reassoc_of% e3) _)).trans ?_
  refine (congrArg (fun x => _ ≫ _ ≫ x) ((reassoc_of% (he M)) _)).trans ?_
  refine ((reassoc_of% key2) _).trans ?_
  refine congrArg (DerivedCategory.Qh.map ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).map
    ((NatTrans.mapHomologicalComplex adjP'.unit (ComplexShape.up ℤ)).app K')) ≫ ·) ?_
  refine (congrArg (fun x => _ ≫ _ ≫ x) (T'.mapDerivedCategory.map_comp
    (@CategoryTheory.inv _ _ _ _ (αP.app qK) hK) (LP.map qπ))).trans ?_
  refine ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (T'.mapDerivedCategory.map
    (@CategoryTheory.inv _ _ _ _ (αP.app qK) hK) ≫ T'.mapDerivedCategory.map (LP.map qπ))) e4).trans
      (Category.assoc _ _ _))).symm.trans ?_
  refine congrArg (T'.mapDerivedCategoryFactorsh.inv.app
    ((P'.mapHomotopyCategory (ComplexShape.up ℤ)).obj
      ((HomotopyCategory.quotient A' (ComplexShape.up ℤ)).obj K')) ≫ ·) ?_
  exact ((T'.mapDerivedCategory.map_comp _ _).trans
    (congrArg (_ ≫ ·) (T'.mapDerivedCategory.map_comp _ _))).symm

end Canonical

end Stacks.Homology.DerivedLeftAdjointComp


namespace Stacks.Sites.FibredCategory.MorphismSituation

open Stacks.Homology.DerivedLeftAdjointComp

universe u₀ u₁ u₂ v₀ v₁ v₂ w

attribute [local instance] HasDerivedCategory.standard

variable (S : MorphismSituation.{u₀, u₁, u₂, v₀, v₁, v₂, max w u₀ u₁ u₂ v₀ v₁ v₂})

attribute [local instance 2000] Preadditive.preadditiveHasZeroMorphisms Abelian.toPreadditive

/-- The derived adjunction `Lg_! ⊣ g⁻¹` satisfies `UnitFac`. -/
theorem unitFac_derivedAbelianLowerShriekAdjunction (h : S.AbelianLowerShriekAcyclic) :
    UnitFac S.abelianLowerShriekAdjunction S.derivedAbelianLowerShriekComparison
      (S.derivedAbelianLowerShriekAdjunction h) := fun M => by
  have := Cohomology.DerivedLowerShriek.isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{max
    w u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₁, u₁} S.sourceTopology S.totalTopology S.u h DerivedCategory.Qh
    S.derivedAbelianLowerShriek S.derivedAbelianLowerShriekComparison S.derivedAbelianInverseImage
  exact Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction_unit_fac.{max
    w u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₁, u₁} S.sourceTopology S.totalTopology S.u M

/-- The derived adjunction `Lπ_! ⊣ π⁻¹` satisfies `UnitFac`. -/
theorem unitFac_derivedTotalAbelianLowerShriekAdjunction (h : S.TotalAbelianLowerShriekAcyclic) :
    UnitFac S.totalAbelianLowerShriekAdjunction
      (Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
        u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p)
      (S.derivedTotalAbelianLowerShriekAdjunction h) := fun M => by
  have := Cohomology.DerivedLowerShriek.isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{max
    w u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p h DerivedCategory.Qh
    S.derivedTotalAbelianLowerShriek
    (Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
      u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p)
    S.derivedTotalAbelianInverseImage
  exact Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction_unit_fac.{max
    w u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p M

/-- The derived adjunction `Lπ'_! ⊣ π'⁻¹` satisfies `UnitFac`. -/
theorem unitFac_derivedSourceAbelianLowerShriekAdjunction
    (h : S.SourceAbelianLowerShriekAcyclic) :
    UnitFac S.sourceAbelianLowerShriekAdjunction
      (Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
        u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p')
      (S.derivedSourceAbelianLowerShriekAdjunction h) := fun M => by
  have := Cohomology.DerivedLowerShriek.isLeftDerivedFunctor_abelianLowerShriek_comp_of_acyclic.{max
    w u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p' h DerivedCategory.Qh
    S.derivedSourceAbelianLowerShriek
    (Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
      u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p')
    S.derivedSourceAbelianInverseImage
  exact Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekAdjunction_unit_fac.{max
    w u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p' M

/-- The identification of derived restrictions `π⁻¹ ∘ g⁻¹ = π'⁻¹` satisfies `CompIsoFac`. -/
theorem compIsoFac_derivedAbelianInverseImageCompIso :
    CompIsoFac S.abelianInverseImageCompIso S.derivedAbelianInverseImageCompIso :=
  compIsoFac_liftNatIso S.abelianInverseImageCompIso


/-- The comparison `LΠ_! ⟶ Π_!` of the target's projection is invertible on a K-projective
complex. -/
theorem isIso_totalComparison_app (K : CochainComplex
    (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ℤ) [K.IsKProjective] :
    IsIso ((Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
      u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
  have _h1 : S.derivedTotalAbelianLowerShriek.IsLeftDerivedFunctor
      (Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
        u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p)
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
    Functor.instIsLeftDerivedFunctorTotalLeftDerivedTotalLeftDerivedCounit _ _ _
  have _h2 := S.hasPointwiseLeftDerivedFunctor_totalAbelianLowerShriekOnHomotopy
  Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective
    (G := S.totalAbelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh)
    (LG := S.derivedTotalAbelianLowerShriek)
    (α := Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
        u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p) K

/-- The comparison `LΠ'_! ⟶ Π'_!` of the source's projection is invertible on a K-projective
complex. -/
theorem isIso_sourceComparison_app (K : CochainComplex
    (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ℤ) [K.IsKProjective] :
    IsIso ((Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
      u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p').app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) :=
  have _h1 : S.derivedSourceAbelianLowerShriek.IsLeftDerivedFunctor
      (Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
        u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p')
      (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) :=
    Functor.instIsLeftDerivedFunctorTotalLeftDerivedTotalLeftDerivedCounit _ _ _
  have _h2 := S.hasPointwiseLeftDerivedFunctor_sourceAbelianLowerShriekOnHomotopy
  Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective
    (G := S.sourceAbelianLowerShriekOnHomotopy ⋙ DerivedCategory.Qh)
    (LG := S.derivedSourceAbelianLowerShriek)
    (α := Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
        u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p') K

/-- **The canonical map of Stacks 08PD on resolutions, for a situation of Stacks 08PA.** Read
through quasi-isomorphisms `π' : K' ⟶ F'[0]` and `π : K ⟶ F[0]` and a lift `φ : K' ⟶ g⁻¹K` of
`t`, the canonical map `Lπ'_!F' ⟶ Lπ_!F` is the map `π'_!K' ⟶ π_!K` assembled from `φ`, provided
the comparison `Lπ_!K ⟶ π_!K` is invertible (for instance when `K` is K-projective,
`isIso_totalComparison_app`). -/
theorem canonicalDerivedLowerShriekMap_comp_eq (h : S.AbelianLowerShriekAcyclic)
    (hp : S.TotalAbelianLowerShriekAcyclic) (hp' : S.SourceAbelianLowerShriekAcyclic)
    (F : Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
    (F' : Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂})
    (t : F' ⟶ S.abelianInverseImage.obj F)
    {K' : CochainComplex (Sheaf S.sourceTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ℤ}
    {K : CochainComplex (Sheaf S.totalTopology AddCommGrpCat.{max w u₀ u₁ u₂ v₀ v₁ v₂}) ℤ}
    (π' : K' ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F')
    (π : K ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)
    (φ : K' ⟶ (S.abelianInverseImage.mapHomologicalComplex (ComplexShape.up ℤ)).obj K)
    (hφ : LiftCondition S.abelianInverseImage t π' π φ)
    (hK : IsIso ((Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
      u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p).app
        ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K))) :
    S.derivedSourceAbelianLowerShriek.map (DerivedCategory.Qh.map (singleQuot π') ≫
        (DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app F') ≫
        S.canonicalDerivedLowerShriekMap h hp hp' F F' t =
      (Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
        u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p').app
          ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K') ≫
        DerivedCategory.Qh.map ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
          (resolutionMap S.abelianLowerShriekAdjunction S.totalAbelianLowerShriekAdjunction
            S.sourceAbelianLowerShriekAdjunction S.abelianInverseImageCompIso φ)) ≫
        @CategoryTheory.inv _ _ _ _
            ((Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
          u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p).app
            ((HomotopyCategory.quotient _ (ComplexShape.up ℤ)).obj K)) hK ≫
        S.derivedTotalAbelianLowerShriek.map (DerivedCategory.Qh.map (singleQuot π) ≫
          (DerivedCategory.singleFunctorIsoCompQh _ 0).inv.app F) :=
by
  have key := canonicalMap_eq (adjG := S.abelianLowerShriekAdjunction)
    (adjP := S.totalAbelianLowerShriekAdjunction) (adjP' := S.sourceAbelianLowerShriekAdjunction)
    (e := S.abelianInverseImageCompIso) (eD := S.derivedAbelianInverseImageCompIso)
    (αG := S.derivedAbelianLowerShriekComparison) (dG := S.derivedAbelianLowerShriekAdjunction h)
    (αP := Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
      u₀ u₁ u₂ v₀ v₁ v₂, v₁, u₁, v₀, u₀} S.totalTopology S.base.J S.p)
    (dP := S.derivedTotalAbelianLowerShriekAdjunction hp)
    (αP' := Cohomology.DerivedLowerShriek.derivedAbelianLowerShriekComparison.{max w
      u₀ u₁ u₂ v₀ v₁ v₂, v₂, u₂, v₀, u₀} S.sourceTopology S.base.J S.p')
    (dP' := S.derivedSourceAbelianLowerShriekAdjunction hp')
    (unitFac_derivedAbelianLowerShriekAdjunction S h)
    (unitFac_derivedTotalAbelianLowerShriekAdjunction S hp)
    (unitFac_derivedSourceAbelianLowerShriekAdjunction S hp')
    (compIsoFac_derivedAbelianInverseImageCompIso S) t π' π φ hφ hK
  exact key

end Stacks.Sites.FibredCategory.MorphismSituation

end
