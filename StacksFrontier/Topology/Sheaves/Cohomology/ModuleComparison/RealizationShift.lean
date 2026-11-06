module

public import StacksFrontier.AlgebraicGeometry.DeRham.RealizationComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.SectionsForgetCommShift
public import StacksFrontier.Homology.DerivedIndexing.SingleDegreeShift
public import StacksFrontier.Algebra.Homology.DerivedCategory.CochainComplexPlusDerivedUnit
public import
  StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.DerivedSectionsModelComparison
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomologyFactorsh
public import StacksFrontier.Homology.HomComplex.TargetShiftDegree

/-!
# The realization comparison of Stacks 01F1 and the shift

Let `X` be a ringed space. For a bounded below complex `𝒦^•` of `𝒪_X`-modules, Stacks 01F1
identifies the hypercohomology `Hⁿ(X, 𝒦^•)` of its underlying complex of abelian sheaves with its
hypercohomology computed in `𝒪_X`-modules, the module structure forgotten. Both sides carry
identifications `Hⁿ(X, 𝒦^•[s]) ≅ Hⁿ⁺ˢ(X, 𝒦^•)` coming from the commutation of the derived functors
with the shift. This file compares them.

## Main definitions

* `Stacks.Cohomology.RealizationShift.shiftHomologyIso`: for a functor `F` into `D⁺(ℬ)` commuting
  with the shift, the identification `Hⁿ(F(X[s])) ≅ Hⁿ⁺ˢ(F X)`.

## Main results

* `Stacks.Cohomology.RealizationShift.shiftHomologyIso_naturality_of_commShift`: a natural
  transformation commuting with the shift is compatible with these identifications.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.Cohomology.Leray (AbelianSheaf sectionsFunctor)

universe u

namespace Stacks.Cohomology.RealizationShift

attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso
attribute [local instance] Stacks.DerivedIndexing.commShiftRightDerivedFunctorPlus
  Stacks.DerivedIndexing.natTransCommShiftRightDerivedFunctorPlusUnit

section Generic

variable {C B : Type*} [Category* C] [Category* B] [Abelian B] [HasDerivedCategory B]
  [HasShift C ℤ]

/-- **The identification `Hⁿ(F(X[s])) ≅ Hⁿ⁺ˢ(F X)`** for a functor `F` into `D⁺(ℬ)` commuting with
the shift, for `s + n = n'`: the commutation of `F` with the shift followed by the shift sequence
of the cohomology functors. -/
def shiftHomologyIso (F : C ⥤ DerivedCategory.Plus B) [F.CommShift ℤ] (X : C) (s n n' : ℤ)
    (h : s + n = n') :
    (DerivedCategory.Plus.homologyFunctor B n).obj (F.obj (X⟦s⟧)) ≅
      (DerivedCategory.Plus.homologyFunctor B n').obj (F.obj X) :=
  (DerivedCategory.Plus.homologyFunctor B n).mapIso ((F.commShiftIso s).app X) ≪≫
    ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso s n n' h).app (F.obj X)

/-- Pasting a commutative square in the source with a naturality square of the target. -/
private theorem map_comp_paste_naturality {D E : Type*} [Category* D] [Category* E] (H : D ⥤ E)
    {A B A' B' : D} {S S' : E} (u : A ⟶ B) (cA : A ⟶ A') (cB : B ⟶ B') (w : A' ⟶ B')
    (hc : u ≫ cB = cA ≫ w) (sA : H.obj A' ⟶ S) (sB : H.obj B' ⟶ S') (g : S ⟶ S')
    (hs : H.map w ≫ sB = sA ≫ g) : H.map u ≫ H.map cB ≫ sB = (H.map cA ≫ sA) ≫ g := by
  rw [← Category.assoc, ← H.map_comp, hc, H.map_comp, Category.assoc, hs, Category.assoc]

/-- **A natural transformation commuting with the shift is compatible with the identifications
`Hⁿ(F(X[s])) ≅ Hⁿ⁺ˢ(F X)`.** -/
theorem shiftHomologyIso_naturality_of_commShift {F G : C ⥤ DerivedCategory.Plus B}
    [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ] (X : C) (s n n' : ℤ)
    (h : s + n = n') :
    (DerivedCategory.Plus.homologyFunctor B n).map (τ.app (X⟦s⟧)) ≫
        (shiftHomologyIso G X s n n' h).hom =
      (shiftHomologyIso F X s n n' h).hom ≫
        (DerivedCategory.Plus.homologyFunctor B n').map (τ.app X) := by
  exact map_comp_paste_naturality _ _ _ _ _ (NatTrans.shift_app_comm τ s X).symm _ _ _
    ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso_hom_naturality s n n' h (τ.app X))

/-- `shiftHomologyIso` of a composite functor: the commutation of the first functor with the
shift, followed by `shiftHomologyIso` of the second. -/
theorem shiftHomologyIso_comp {C' : Type*} [Category* C'] [HasShift C' ℤ] (G : C ⥤ C')
    (F : C' ⥤ DerivedCategory.Plus B) [G.CommShift ℤ] [F.CommShift ℤ] (X : C) (s n n' : ℤ)
    (h : s + n = n') :
    (shiftHomologyIso (G ⋙ F) X s n n' h).hom =
      (DerivedCategory.Plus.homologyFunctor B n).map (F.map ((G.commShiftIso s).hom.app X)) ≫
        (shiftHomologyIso F (G.obj X) s n n' h).hom :=
  (congrArg (· ≫ ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso s n n' h).hom.app
    (F.obj (G.obj X))) ((congrArg (DerivedCategory.Plus.homologyFunctor B n).map
      (Functor.commShiftIso_comp_hom_app G F s X)).trans
        ((DerivedCategory.Plus.homologyFunctor B n).map_comp _ _))).trans (Category.assoc _ _ _)

/-- **`shiftHomologyIso` is natural in the object.** -/
theorem shiftHomologyIso_naturality (F : C ⥤ DerivedCategory.Plus B) [F.CommShift ℤ] {X Y : C}
    (f : X ⟶ Y) (s n n' : ℤ) (h : s + n = n') :
    (DerivedCategory.Plus.homologyFunctor B n).map (F.map (f⟦s⟧')) ≫
        (shiftHomologyIso F Y s n n' h).hom =
      (shiftHomologyIso F X s n n' h).hom ≫
        (DerivedCategory.Plus.homologyFunctor B n').map (F.map f) := by
  exact map_comp_paste_naturality _ _ _ _ _ (F.commShiftIso_hom_naturality f s) _ _ _
    ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso_hom_naturality s n n' h (F.map f))

/-- A functor applied to a component of the inverse of an identity isomorphism is an
identity. -/
theorem map_refl_symm_hom_app {A₁ A₂ A₃ : Type*} [Category* A₁] [Category* A₂] [Category* A₃]
    (F : A₁ ⥤ A₂) (H : A₂ ⥤ A₃) (K : A₁) :
    H.map ((Iso.refl F).symm.hom.app K) = 𝟙 _ := by
  simp

/-- A component of the inverse of the whiskering of an identity isomorphism is an identity. -/
theorem isoWhiskerRight_refl_inv_app {A₁ A₂ A₃ : Type*} [Category* A₁] [Category* A₂]
    [Category* A₃] (F : A₁ ⥤ A₂) (H : A₂ ⥤ A₃) (K : A₁) :
    (Functor.isoWhiskerRight (Iso.refl F) H).inv.app K = 𝟙 _ := by
  simp

/-- An additive functor commutes with the action of the units of `ℤ` on morphisms. -/
theorem map_intUnits_smul {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Preadditive C₁]
    [Preadditive C₂] (F : C₁ ⥤ C₂) [F.Additive] {X Y : C₁} (u : ℤˣ) (f : X ⟶ Y) :
    F.map (u • f) = u • F.map f := by
  rw [Units.smul_def, Units.smul_def, Functor.map_zsmul]

/-- An additive functor carries the identification of two terms of a cochain complex of equal
degrees to the one of the image complex. -/
theorem map_XIsoOfEq_hom {C₁ C₂ : Type*} [Category* C₁] [Category* C₂] [Preadditive C₁]
    [Preadditive C₂] (F : C₁ ⥤ C₂) [F.Additive] (K : CochainComplex C₁ ℤ) {p q : ℤ} (h : p = q) :
    F.map (K.XIsoOfEq h).hom =
      (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).XIsoOfEq h).hom := by
  subst h
  simp

/-- **An exact functor commutes with the shift identifications of the homology of cochain
complexes**: the comparison `Hⁿ(F K) ≅ F(Hⁿ K)` carries the identification
`Hⁿ(K[s]) ≅ Hⁿ⁺ˢ(K)` of `F K` to the image under `F` of that of `K`. -/
theorem mapHomologicalComplexHomologyIso_shift {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [Abelian C₁] [Abelian C₂] (F : C₁ ⥤ C₂) [F.Additive] [F.PreservesHomology]
    (M : CochainComplex C₁ ℤ) (s n n' : ℤ) (h : s + n = n') :
    (HomologicalComplex.homologyFunctor C₂ (ComplexShape.up ℤ) n).map
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso s).hom.app M) ≫
      ((HomologicalComplex.homologyFunctor C₂ (ComplexShape.up ℤ) 0).shiftIso s n n' h).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
      (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n').hom.app M =
    (F.mapHomologicalComplexHomologyIso (ComplexShape.up ℤ) n).hom.app (M⟦s⟧) ≫
      F.map (((HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) 0).shiftIso
        s n n' h).hom.app M) := by
  have e₁ : ((HomologicalComplex.homologyFunctor C₂ (ComplexShape.up ℤ) 0).shiftIso s n n'
      h).hom.app ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) =
      ShortComplex.homologyMap ((CochainComplex.shiftShortComplexFunctorIso C₂ s n n' h).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) :=
    CochainComplex.ShiftSequence.shiftIso_hom_app s n n' h _
  have e₂ : ((HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) 0).shiftIso s n n'
      h).hom.app M =
      ShortComplex.homologyMap
        ((CochainComplex.shiftShortComplexFunctorIso C₁ s n n' h).hom.app M) :=
    CochainComplex.ShiftSequence.shiftIso_hom_app s n n' h _
  rw [e₁, e₂]
  have key : (HomologicalComplex.shortComplexFunctor C₂ (ComplexShape.up ℤ) n).map
        (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso s).hom.app M) ≫
      (CochainComplex.shiftShortComplexFunctorIso C₂ s n n' h).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) =
      F.mapShortComplex.map
        ((CochainComplex.shiftShortComplexFunctorIso C₁ s n n' h).hom.app M) := by
    ext
    all_goals simp only [CochainComplex.shiftShortComplexFunctorIso,
      CochainComplex.shiftShortComplexFunctor'_hom_app_τ₁,
      CochainComplex.shiftShortComplexFunctor'_hom_app_τ₂,
      CochainComplex.shiftShortComplexFunctor'_hom_app_τ₃, ShortComplex.comp_τ₁,
      ShortComplex.comp_τ₂, ShortComplex.comp_τ₃, Functor.mapShortComplex_map_τ₁,
      Functor.mapShortComplex_map_τ₂, Functor.mapShortComplex_map_τ₃]
    · exact (Category.id_comp _).trans ((congrArg (_ • ·) (map_XIsoOfEq_hom F M _).symm).trans
        (map_intUnits_smul F _ _).symm)
    · exact (Category.id_comp _).trans (map_XIsoOfEq_hom F M _).symm
    · exact (Category.id_comp _).trans ((congrArg (_ • ·) (map_XIsoOfEq_hom F M _).symm).trans
        (map_intUnits_smul F _ _).symm)
  show ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor C₂ (ComplexShape.up ℤ) n).map
          (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso s).hom.app M)) ≫
      ShortComplex.homologyMap ((CochainComplex.shiftShortComplexFunctorIso C₂ s n n' h).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
      (((HomologicalComplex.shortComplexFunctor C₁ (ComplexShape.up ℤ) n').obj M).mapHomologyIso
        F).hom =
    (((HomologicalComplex.shortComplexFunctor C₁ (ComplexShape.up ℤ) n).obj (M⟦s⟧)).mapHomologyIso
        F).hom ≫
      F.map (ShortComplex.homologyMap
        ((CochainComplex.shiftShortComplexFunctorIso C₁ s n n' h).hom.app M))
  have k2 : ShortComplex.homologyMap
        ((HomologicalComplex.shortComplexFunctor C₂ (ComplexShape.up ℤ) n).map
          (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso s).hom.app M)) ≫
      ShortComplex.homologyMap ((CochainComplex.shiftShortComplexFunctorIso C₂ s n n' h).hom.app
        ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) =
      ShortComplex.homologyMap (F.mapShortComplex.map
        ((CochainComplex.shiftShortComplexFunctorIso C₁ s n n' h).hom.app M)) := by
    rw [← ShortComplex.homologyMap_comp, key]
    rfl
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) k2).trans
    (ShortComplex.mapHomologyIso_hom_naturality _ F))

/-- The algebra of `mapDerivedCategoryHomologyIso_shift_Q`, with every object and morphism a
variable. -/
theorem homologyShift_chase {C : Type*} [Category* C]
    {P₀ P₁ P₂ P₃ P₄ P₅ B₁ B₂ B₃ B₄ B₅ B₆ B₇ B₈ B₉ B₁₀ : C}
    (a : P₀ ⟶ P₁) (x : P₁ ⟶ P₂) (y : P₂ ⟶ P₃) (z : P₃ ⟶ P₄) (w : P₁ ⟶ P₅) (v : P₅ ⟶ P₄)
    (f₁ : P₀ ⟶ B₁) (f₂ : B₁ ⟶ B₂) (f₃ : B₂ ⟶ B₃) (f₄ : B₃ ⟶ P₂) (sI : B₃ ⟶ B₄) (pinv : B₄ ⟶ P₃)
    (p : P₃ ⟶ B₄) (g₁ : B₂ ⟶ B₅) (cS : B₅ ⟶ B₆) (g₁' : B₆ ⟶ B₄) (g₂ : B₄ ⟶ B₆) (c' : B₆ ⟶ B₇)
    (k : B₇ ⟶ P₄) (g₃ : B₁ ⟶ B₈) (cF : B₈ ⟶ B₅) (c : B₈ ⟶ B₉) (fcS : B₉ ⟶ B₇) (m : P₀ ⟶ B₁₀)
    (fq : B₁₀ ⟶ P₅) (k' : B₉ ⟶ B₁₀) (k'' : B₁₀ ⟶ B₉)
    (hA : a ≫ x = f₁ ≫ f₂ ≫ f₃ ≫ f₄) (hB : f₄ ≫ y = sI ≫ pinv) (hC : f₃ ≫ sI = g₁ ≫ cS ≫ g₁')
    (hD : z = p ≫ g₂ ≫ c' ≫ k) (hE : pinv ≫ p = 𝟙 _) (hE₂ : g₁' ≫ g₂ = 𝟙 _)
    (hF : f₂ ≫ g₁ = g₃ ≫ cF) (hG : cF ≫ cS ≫ c' = c ≫ fcS) (hH : a ≫ w = m ≫ fq)
    (hI : m = f₁ ≫ g₃ ≫ c ≫ k') (hJ : fq ≫ v = k'' ≫ fcS ≫ k) (hK : k' ≫ k'' = 𝟙 _) :
    a ≫ x ≫ y ≫ z = a ≫ w ≫ v := by
  rw [reassoc_of% hA, reassoc_of% hB, hD, reassoc_of% hE, reassoc_of% hC, reassoc_of% hE₂,
    reassoc_of% hF, reassoc_of% hG, reassoc_of% hH, hJ, hI]
  simp only [Category.assoc]
  rw [reassoc_of% hK]

/-- **`mapDerivedCategoryHomologyIso_shift` at the class of a complex.** -/
theorem mapDerivedCategoryHomologyIso_shift_Q {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [Abelian C₁] [Abelian C₂] [HasDerivedCategory C₁] [HasDerivedCategory C₂] (F : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (M : CochainComplex C₁ ℤ) (s n n' : ℤ) (h : s + n = n') :
    (DerivedCategory.homologyFunctor C₂ n).map
        ((F.mapDerivedCategory.commShiftIso s).hom.app (DerivedCategory.Q.obj M)) ≫
      ((DerivedCategory.homologyFunctor C₂ 0).shiftIso s n n' h).hom.app
        (F.mapDerivedCategory.obj (DerivedCategory.Q.obj M)) ≫
      (F.mapDerivedCategoryHomologyIso n').hom.app (DerivedCategory.Q.obj M) =
    (F.mapDerivedCategoryHomologyIso n).hom.app ((DerivedCategory.Q.obj M)⟦s⟧) ≫
      F.map (((DerivedCategory.homologyFunctor C₁ 0).shiftIso s n n' h).hom.app
        (DerivedCategory.Q.obj M)) := by
  have hφ := NatTrans.shift_app_comm F.mapDerivedCategoryFactors.hom s M
  simp only [Functor.commShiftIso_comp_hom_app] at hφ
  have h1 := Functor.mapDerivedCategoryHomologyIso_hom_app_Q F n' M
  have h2 := Functor.mapDerivedCategoryHomologyIso_hom_app_Q F n (M⟦s⟧)
  have h3 := CochainComplex.HomComplex.shiftIso_hom_app_Q_obj
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) s n n' h
  have h4 := CochainComplex.HomComplex.shiftIso_hom_app_Q_obj M s n n' h
  have h5 := mapHomologicalComplexHomologyIso_shift F M s n n' h
  have hφ' : F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso s).hom.app M) ≫
      (F.mapDerivedCategory.commShiftIso s).hom.app (DerivedCategory.Q.obj M) =
      F.mapDerivedCategoryFactors.hom.app (M⟦s⟧) ≫
        DerivedCategory.Q.map
          (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso s).hom.app M) ≫
        (DerivedCategory.Q.commShiftIso s).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M) ≫
        (F.mapDerivedCategoryFactors.inv.app M)⟦s⟧' := by
    rw [← reassoc_of% hφ, ← Functor.map_comp, Iso.hom_inv_id_app]
    simp
  have hn := (F.mapDerivedCategoryHomologyIso n).hom.naturality
    ((DerivedCategory.Q.commShiftIso s).hom.app M)
  have hs := ((DerivedCategory.homologyFunctor C₂ 0).shiftIso s n n' h).hom.naturality
    (F.mapDerivedCategoryFactors.inv.app M)
  have hF := (DerivedCategory.homologyFunctorFactors C₂ n).hom.naturality
    (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso s).hom.app M)
  simp only [Functor.comp_map] at hn hs hF
  let Hn := DerivedCategory.homologyFunctor C₂ n
  let Hn' := DerivedCategory.homologyFunctor C₂ n'
  have hA : Hn.map (F.mapDerivedCategory.map ((DerivedCategory.Q.commShiftIso s).hom.app M)) ≫
      Hn.map ((F.mapDerivedCategory.commShiftIso s).hom.app (DerivedCategory.Q.obj M)) =
      Hn.map (F.mapDerivedCategoryFactors.hom.app (M⟦s⟧)) ≫
        Hn.map (DerivedCategory.Q.map
          (((F.mapHomologicalComplex (ComplexShape.up ℤ)).commShiftIso s).hom.app M)) ≫
        Hn.map ((DerivedCategory.Q.commShiftIso s).hom.app
          ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj M)) ≫
        Hn.map ((F.mapDerivedCategoryFactors.inv.app M)⟦s⟧') := by
    rw [← Hn.map_comp, hφ', Hn.map_comp, Hn.map_comp, Hn.map_comp]
  have hE : Hn'.map (F.mapDerivedCategoryFactors.inv.app M) ≫
      Hn'.map (F.mapDerivedCategoryFactors.hom.app M) = 𝟙 _ := by
    rw [← Hn'.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  have hJ : F.map ((DerivedCategory.homologyFunctor C₁ n).map
        ((DerivedCategory.Q.commShiftIso s).hom.app M)) ≫
      F.map (((DerivedCategory.homologyFunctor C₁ 0).shiftIso s n n' h).hom.app
        (DerivedCategory.Q.obj M)) =
      F.map ((DerivedCategory.homologyFunctorFactors C₁ n).hom.app (M⟦s⟧)) ≫
        F.map (((HomologicalComplex.homologyFunctor C₁ (ComplexShape.up ℤ) 0).shiftIso s n n'
          h).hom.app M) ≫
        F.map ((DerivedCategory.homologyFunctorFactors C₁ n').inv.app M) :=
    (F.map_comp _ _).symm.trans ((congrArg F.map h4).trans ((F.map_comp _ _).trans
      (congrArg (_ ≫ ·) (F.map_comp _ _))))
  have hK : F.map ((DerivedCategory.homologyFunctorFactors C₁ n).inv.app (M⟦s⟧)) ≫
      F.map ((DerivedCategory.homologyFunctorFactors C₁ n).hom.app (M⟦s⟧)) = 𝟙 _ := by
    rw [← F.map_comp, Iso.inv_hom_id_app, CategoryTheory.Functor.map_id]
  refine (cancel_epi (Hn.map (F.mapDerivedCategory.map
    ((DerivedCategory.Q.commShiftIso s).hom.app M)))).1 ?_
  exact homologyShift_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    hA hs h3 h1 hE (Iso.inv_hom_id_app _ _) hF h5 hn h2 hJ hK

/-- Pasting three commutative squares. -/
theorem paste_three {C : Type*} [Category* C] {a b c d a' b' c' d' : C} (f₀ : a ⟶ a')
    (x : a' ⟶ b') (y : b' ⟶ c') (z : c' ⟶ d') (x₀ : a ⟶ b) (y₀ : b ⟶ c) (z₀ : c ⟶ d)
    (g₁ : b ⟶ b') (g₂ : c ⟶ c') (g₃ : d ⟶ d') (h₁ : f₀ ≫ x = x₀ ≫ g₁) (h₂ : g₁ ≫ y = y₀ ≫ g₂)
    (h₃ : g₂ ≫ z = z₀ ≫ g₃) : f₀ ≫ x ≫ y ≫ z = (x₀ ≫ y₀ ≫ z₀) ≫ g₃ := by
  rw [reassoc_of% h₁, reassoc_of% h₂, h₃]
  simp only [Category.assoc]

/-- Pasting two commutative squares. -/
theorem paste_two {C : Type*} [Category* C] {a b c a' b' c' : C} (f₀ : a ⟶ a')
    (x : a' ⟶ b') (y : b' ⟶ c') (x₀ : a ⟶ b) (y₀ : b ⟶ c) (g₁ : b ⟶ b') (g₂ : c ⟶ c')
    (h₁ : f₀ ≫ x = x₀ ≫ g₁) (h₂ : g₁ ≫ y = y₀ ≫ g₂) : f₀ ≫ x ≫ y = (x₀ ≫ y₀) ≫ g₂ := by
  rw [reassoc_of% h₁, h₂]
  simp only [Category.assoc]

/-- **An exact functor commutes with the shift identifications of the homology of the derived
category**: the comparison `Hⁿ(F K) ≅ F(Hⁿ K)` carries the identification `Hⁿ(K[s]) ≅ Hⁿ⁺ˢ(K)`
of `F K` to the image under `F` of that of `K`. -/
theorem mapDerivedCategoryHomologyIso_shift {C₁ C₂ : Type*} [Category* C₁] [Category* C₂]
    [Abelian C₁] [Abelian C₂] [HasDerivedCategory C₁] [HasDerivedCategory C₂] (F : C₁ ⥤ C₂)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (Y : DerivedCategory C₁) (s n n' : ℤ) (h : s + n = n') :
    (DerivedCategory.homologyFunctor C₂ n).map
        ((F.mapDerivedCategory.commShiftIso s).hom.app Y) ≫
      ((DerivedCategory.homologyFunctor C₂ 0).shiftIso s n n' h).hom.app
        (F.mapDerivedCategory.obj Y) ≫
      (F.mapDerivedCategoryHomologyIso n').hom.app Y =
    (F.mapDerivedCategoryHomologyIso n).hom.app (Y⟦s⟧) ≫
      F.map (((DerivedCategory.homologyFunctor C₁ 0).shiftIso s n n' h).hom.app Y) := by
  let e := DerivedCategory.Q.objObjPreimageIso Y
  let Hn := DerivedCategory.homologyFunctor C₂ n
  have hL := paste_three (Hn.map (F.mapDerivedCategory.map (e.hom⟦s⟧')))
    (Hn.map ((F.mapDerivedCategory.commShiftIso s).hom.app Y))
    (((DerivedCategory.homologyFunctor C₂ 0).shiftIso s n n' h).hom.app
      (F.mapDerivedCategory.obj Y))
    ((F.mapDerivedCategoryHomologyIso n').hom.app Y)
    (Hn.map ((F.mapDerivedCategory.commShiftIso s).hom.app _))
    (((DerivedCategory.homologyFunctor C₂ 0).shiftIso s n n' h).hom.app
      (F.mapDerivedCategory.obj _))
    ((F.mapDerivedCategoryHomologyIso n').hom.app _)
    (Hn.map ((F.mapDerivedCategory.map e.hom)⟦s⟧'))
    ((DerivedCategory.homologyFunctor C₂ n').map (F.mapDerivedCategory.map e.hom))
    (F.map ((DerivedCategory.homologyFunctor C₁ n').map e.hom))
    ((Hn.map_comp _ _).symm.trans ((congrArg Hn.map
      (F.mapDerivedCategory.commShiftIso_hom_naturality e.hom s)).trans (Hn.map_comp _ _)))
    (((DerivedCategory.homologyFunctor C₂ 0).shiftIso_hom_naturality s n n' h
      (F.mapDerivedCategory.map e.hom)))
    ((F.mapDerivedCategoryHomologyIso n').hom.naturality e.hom)
  have hR := paste_two (Hn.map (F.mapDerivedCategory.map (e.hom⟦s⟧')))
    ((F.mapDerivedCategoryHomologyIso n).hom.app (Y⟦s⟧))
    (F.map (((DerivedCategory.homologyFunctor C₁ 0).shiftIso s n n' h).hom.app Y))
    ((F.mapDerivedCategoryHomologyIso n).hom.app (_⟦s⟧))
    (F.map (((DerivedCategory.homologyFunctor C₁ 0).shiftIso s n n' h).hom.app _))
    (F.map ((DerivedCategory.homologyFunctor C₁ n).map (e.hom⟦s⟧')))
    (F.map ((DerivedCategory.homologyFunctor C₁ n').map e.hom))
    ((F.mapDerivedCategoryHomologyIso n).hom.naturality (e.hom⟦s⟧'))
    ((F.map_comp _ _).symm.trans ((congrArg F.map
      ((DerivedCategory.homologyFunctor C₁ 0).shiftIso_hom_naturality s n n' h e.hom)).trans
        (F.map_comp _ _)))
  refine (cancel_epi (Hn.map (F.mapDerivedCategory.map (e.hom⟦s⟧')))).1 ?_
  refine hL.trans (Eq.trans ?_ hR.symm)
  exact congrArg (· ≫ _) (mapDerivedCategoryHomologyIso_shift_Q F _ s n n' h)

/-- **The identification `Hⁿ(F(X[s])) ≅ Hⁿ⁺ˢ(F X)`** for a functor `F` into `D(ℬ)` commuting with
the shift, for `s + n = n'`. -/
def shiftHomologyIsoU (F : C ⥤ DerivedCategory B) [F.CommShift ℤ] (X : C) (s n n' : ℤ)
    (h : s + n = n') :
    (DerivedCategory.homologyFunctor B n).obj (F.obj (X⟦s⟧)) ≅
      (DerivedCategory.homologyFunctor B n').obj (F.obj X) :=
  (DerivedCategory.homologyFunctor B n).mapIso ((F.commShiftIso s).app X) ≪≫
    ((DerivedCategory.homologyFunctor B 0).shiftIso s n n' h).app (F.obj X)

/-- A natural transformation commuting with the shift is compatible with the identifications
`Hⁿ(F(X[s])) ≅ Hⁿ⁺ˢ(F X)` of `D(ℬ)`. -/
theorem shiftHomologyIsoU_naturality_of_commShift {F G : C ⥤ DerivedCategory B}
    [F.CommShift ℤ] [G.CommShift ℤ] (τ : F ⟶ G) [NatTrans.CommShift τ ℤ] (X : C) (s n n' : ℤ)
    (h : s + n = n') :
    (DerivedCategory.homologyFunctor B n).map (τ.app (X⟦s⟧)) ≫
        (shiftHomologyIsoU G X s n n' h).hom =
      (shiftHomologyIsoU F X s n n' h).hom ≫
        (DerivedCategory.homologyFunctor B n').map (τ.app X) := by
  exact map_comp_paste_naturality _ _ _ _ _ (NatTrans.shift_app_comm τ s X).symm _ _ _
    ((DerivedCategory.homologyFunctor B 0).shiftIso_hom_naturality s n n' h (τ.app X))

/-- The algebra of `shiftHomologyIsoU_add`, with every object and morphism a variable. -/
theorem add_paste {V : Type*} [Category* V] {P Q R S U Q' Q'' P' : V} (c₁ : P ⟶ Q) (S₁ : Q ⟶ R)
    (c₂ : R ⟶ S) (S₂ : S ⟶ U) (c₂' : Q ⟶ Q') (S₁' : Q' ⟶ S) (d : Q' ⟶ Q'') (St : Q'' ⟶ U)
    (fa : P ⟶ P') (ct : P' ⟶ Q'') (e₂ : S₁ ≫ c₂ = c₂' ≫ S₁') (e₃ : S₁' ≫ S₂ = d ≫ St)
    (e₁ : fa ≫ ct = c₁ ≫ c₂' ≫ d) : (c₁ ≫ S₁) ≫ (c₂ ≫ S₂) = fa ≫ (ct ≫ St) := by
  rw [← Category.assoc fa, e₁]
  simp only [Category.assoc]
  rw [reassoc_of% e₂, e₃]

/-- **The identifications `Hⁿ(F(X[s])) ≅ Hⁿ⁺ˢ(F X)` compose**: shifting by `t₁` and then by
`t₂` is shifting by `t₂ + t₁`, through the composition of the shifts of `X`. -/
theorem shiftHomologyIsoU_add (F : C ⥤ DerivedCategory B) [F.CommShift ℤ] (X : C)
    (t₁ t₂ t : ℤ) (ht : t₂ + t₁ = t) (a a' a'' : ℤ) (h₁ : t₁ + a = a') (h₂ : t₂ + a' = a'') :
    (shiftHomologyIsoU F (X⟦t₂⟧) t₁ a a' h₁).hom ≫ (shiftHomologyIsoU F X t₂ a' a'' h₂).hom =
      (DerivedCategory.homologyFunctor B a).map
          (F.map ((shiftFunctorAdd' C t₂ t₁ t ht).inv.app X)) ≫
        (shiftHomologyIsoU F X t a a'' (by omega)).hom := by
  have e₁ : F.map ((shiftFunctorAdd' C t₂ t₁ t ht).inv.app X) ≫ (F.commShiftIso t).hom.app X =
      (F.commShiftIso t₁).hom.app (X⟦t₂⟧) ≫ ((F.commShiftIso t₂).hom.app X)⟦t₁⟧' ≫
        (shiftFunctorAdd' (DerivedCategory B) t₂ t₁ t ht).inv.app (F.obj X) := by
    rw [F.commShiftIso_add' ht, Functor.CommShift.isoAdd'_hom_app, ← Functor.map_comp_assoc,
      Iso.inv_hom_id_app, CategoryTheory.Functor.map_id, Category.id_comp]
  let H := DerivedCategory.homologyFunctor B a
  let H' := DerivedCategory.homologyFunctor B a'
  let H0 := DerivedCategory.homologyFunctor B 0
  have e₂ : (H0.shiftIso t₁ a a' h₁).hom.app (F.obj (X⟦t₂⟧)) ≫
      H'.map ((F.commShiftIso t₂).hom.app X) =
      H.map (((F.commShiftIso t₂).hom.app X)⟦t₁⟧') ≫
        (H0.shiftIso t₁ a a' h₁).hom.app ((F.obj X)⟦t₂⟧) :=
    (H0.shiftIso_hom_naturality t₁ a a' h₁ ((F.commShiftIso t₂).hom.app X)).symm
  have e₃ : (H0.shiftIso t₁ a a' h₁).hom.app ((F.obj X)⟦t₂⟧) ≫
      (H0.shiftIso t₂ a' a'' h₂).hom.app (F.obj X) =
      H.map ((shiftFunctorAdd' (DerivedCategory B) t₂ t₁ t ht).inv.app (F.obj X)) ≫
        (H0.shiftIso t a a'' (by omega)).hom.app (F.obj X) :=
    H0.shiftIso_hom_app_comp t₁ t₂ t ht a a' a'' h₁ h₂ (F.obj X)
  have e₁' : H.map (F.map ((shiftFunctorAdd' C t₂ t₁ t ht).inv.app X)) ≫
      H.map ((F.commShiftIso t).hom.app X) =
      H.map ((F.commShiftIso t₁).hom.app (X⟦t₂⟧)) ≫ H.map (((F.commShiftIso t₂).hom.app X)⟦t₁⟧') ≫
        H.map ((shiftFunctorAdd' (DerivedCategory B) t₂ t₁ t ht).inv.app (F.obj X)) := by
    rw [← H.map_comp, ← H.map_comp, ← H.map_comp, e₁]
  exact add_paste _ _ _ _ _ _ _ _ _ _ e₂ e₃ e₁'

/-- The shift sequence of the cohomology functors of `D⁺(ℬ)` is the one of `D(ℬ)`, read through
the inclusion. -/
theorem plus_shiftIso_hom_app (Y : DerivedCategory.Plus B) (s n n' : ℤ) (h : s + n = n') :
    ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso s n n' h).hom.app Y =
      (DerivedCategory.homologyFunctor B n).map
          ((DerivedCategory.Plus.ι.commShiftIso s).hom.app Y) ≫
        ((DerivedCategory.homologyFunctor B 0).shiftIso s n n' h).hom.app
          (DerivedCategory.Plus.ι.obj Y) := by
  refine Eq.trans (b := 𝟙 _ ≫ ((DerivedCategory.homologyFunctor B n).map
      ((DerivedCategory.Plus.ι.commShiftIso s).hom.app Y) ≫ 𝟙 _ ≫
      ((DerivedCategory.homologyFunctor B 0).shiftIso s n n' h).hom.app
        (DerivedCategory.Plus.ι.obj Y))) rfl ?_
  exact (Category.id_comp _).trans (congrArg (_ ≫ ·) (Category.id_comp _))

/-- **The identification `Hⁿ(F(X[s])) ≅ Hⁿ⁺ˢ(F X)` of `D⁺(ℬ)` is the one of `D(ℬ)`**, for the
composite of `F` with the inclusion `D⁺(ℬ) ⥤ D(ℬ)`. -/
theorem shiftHomologyIso_eq_U (F : C ⥤ DerivedCategory.Plus B) [F.CommShift ℤ] (X : C)
    (s n n' : ℤ) (h : s + n = n') :
    (shiftHomologyIso F X s n n' h).hom =
      (shiftHomologyIsoU (F ⋙ DerivedCategory.Plus.ι) X s n n' h).hom := by
  refine Eq.trans (b := (DerivedCategory.homologyFunctor B n).map
      (DerivedCategory.Plus.ι.map ((F.commShiftIso s).hom.app X)) ≫
      ((DerivedCategory.Plus.homologyFunctor B 0).shiftIso s n n' h).hom.app (F.obj X)) rfl ?_
  rw [plus_shiftIso_hom_app]
  exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ _)
    ((DerivedCategory.homologyFunctor B n).map_comp _ _).symm |>.trans
      (congrArg (fun x => (DerivedCategory.homologyFunctor B n).map x ≫ _)
        (Functor.commShiftIso_comp_hom_app F DerivedCategory.Plus.ι s X).symm))

/-- `shiftHomologyIsoU` of a composite functor, written out. -/
theorem shiftHomologyIsoU_comp_hom {C' : Type*} [Category* C'] [HasShift C' ℤ]
    (F : C ⥤ C') (G : C' ⥤ DerivedCategory B) [F.CommShift ℤ] [G.CommShift ℤ] (X : C)
    (s n n' : ℤ) (h : s + n = n') :
    (shiftHomologyIsoU (F ⋙ G) X s n n' h).hom =
      (DerivedCategory.homologyFunctor B n).map (G.map ((F.commShiftIso s).hom.app X)) ≫
        (DerivedCategory.homologyFunctor B n).map ((G.commShiftIso s).hom.app (F.obj X)) ≫
        ((DerivedCategory.homologyFunctor B 0).shiftIso s n n' h).hom.app (G.obj (F.obj X)) :=
  (congrArg (· ≫ ((DerivedCategory.homologyFunctor B 0).shiftIso s n n' h).hom.app
    (G.obj (F.obj X))) ((congrArg (DerivedCategory.homologyFunctor B n).map
      (Functor.commShiftIso_comp_hom_app F G s X)).trans
        ((DerivedCategory.homologyFunctor B n).map_comp _ _))).trans (Category.assoc _ _ _)

/-- The algebra of `realizationIsoAt_shift`, with every object and morphism a variable. -/
theorem realization_paste {C : Type*} [Category* C] {a₀ a₁ a₂ a₃ a₄ a₅ b₁ b₂ c₀ : C}
    (θs : a₀ ⟶ a₁) (x₁ : a₁ ⟶ a₂) (x₂ : a₂ ⟶ a₃) (x₃ : a₃ ⟶ a₄) (md' : a₄ ⟶ a₅) (md₁ : a₁ ⟶ b₁)
    (fg : b₁ ⟶ b₂) (fsi : b₂ ⟶ a₅) (md₂ : a₂ ⟶ b₂) (L : a₀ ⟶ c₀) (θ : c₀ ⟶ a₄)
    (e₂ : θs ≫ x₁ ≫ x₂ ≫ x₃ = L ≫ θ) (e₃ : x₂ ≫ x₃ ≫ md' = md₂ ≫ fsi)
    (e₄ : x₁ ≫ md₂ = md₁ ≫ fg) : (θs ≫ md₁) ≫ fg ≫ fsi = L ≫ θ ≫ md' := by
  rw [← reassoc_of% e₂, e₃, reassoc_of% e₄]
  simp only [Category.assoc]

end Generic

section Derived

variable {C₀ D₀ H₀ : Type*} [Category* C₀] [Category* D₀] [Category* H₀]
  [HasShift C₀ ℤ] [HasShift D₀ ℤ] [HasShift H₀ ℤ]

/-- **A transformation between two right derived functors of the same functor which is compatible
with their units commutes with the shift**, as soon as the two units do. Both sides of each
commutation equation are transformations out of `shiftFunctor a ⋙ RF₁`, itself a right derived
functor, so they agree as soon as they agree after its unit; there both reduce to the commutation
of the units. -/
theorem natTransCommShift_of_rightDerived (L : C₀ ⥤ H₀) (W : MorphismProperty C₀)
    [L.IsLocalization W] {F : C₀ ⥤ D₀} {RF₁ RF₂ : H₀ ⥤ D₀} (α₁ : F ⟶ L ⋙ RF₁)
    (α₂ : F ⟶ L ⋙ RF₂) [RF₁.IsRightDerivedFunctor α₁ W] [W.IsCompatibleWithShift ℤ]
    [F.CommShift ℤ] [L.CommShift ℤ] [RF₁.CommShift ℤ] [RF₂.CommShift ℤ]
    [NatTrans.CommShift α₁ ℤ] [NatTrans.CommShift α₂ ℤ] (τ : RF₁ ⟶ RF₂)
    (hτ : α₁ ≫ Functor.whiskerLeft L τ = α₂) : NatTrans.CommShift τ ℤ := by
  refine ⟨fun a => Functor.rightDerived_ext _
    (Functor.IsRightDerivedFunctor.precomposeShiftNatTrans RF₁ α₁ a) W _ _ _ ?_⟩
  ext X
  have h₁ := NatTrans.shift_app_comm α₁ a X
  have h₂ := NatTrans.shift_app_comm α₂ a X
  have hX := NatTrans.congr_app hτ X
  have hXa := NatTrans.congr_app hτ (X⟦a⟧)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.commShiftIso_comp_hom_app,
    Functor.comp_obj] at h₁ h₂ hX hXa
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.IsRightDerivedFunctor.precomposeShiftNatTrans_app, Category.assoc, Functor.comp_obj]
  have hn := τ.naturality ((L.commShiftIso a).hom.app X)
  have eL : (F.commShiftIso a).hom.app X ≫ (shiftFunctor D₀ a).map (α₂.app X) =
      α₁.app (X⟦a⟧) ≫ RF₁.map ((L.commShiftIso a).hom.app X) ≫
        (RF₁.commShiftIso a).hom.app (L.obj X) ≫ (shiftFunctor D₀ a).map (τ.app (L.obj X)) := by
    rw [← hX, Functor.map_comp, reassoc_of% h₁]
  have eR : (F.commShiftIso a).hom.app X ≫ (shiftFunctor D₀ a).map (α₂.app X) =
      α₁.app (X⟦a⟧) ≫ RF₁.map ((L.commShiftIso a).hom.app X) ≫
        τ.app ((L.obj X)⟦a⟧) ≫ (RF₂.commShiftIso a).hom.app (L.obj X) := by
    rw [reassoc_of% hn, reassoc_of% hXa, h₂]
  exact eL.symm.trans eR

end Derived



/-! ### The abelian half of the realization comparison -/

section Realization

variable (X : RingedSpace.{u, u})

/-- **The abelian half of the realization comparison of Stacks 01F1**, as a natural
transformation of functors on bounded below complexes of `𝒪_X`-modules: the unit of the bounded
below right derived functor of the exact functor `toSheaf`, followed by the comparison of
Stacks 01F1 between the derived sections of the underlying abelian sheaves and the derived
sections in modules, the module structure forgotten. -/
def realizationTrans :
    (SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus ⟶
      DerivedCategory.Plus.Q ⋙
        (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).rightDerivedFunctorPlus ⋙
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
          AddCommGrpCat.{u}).rightDerivedFunctorPlus :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.mapCochainComplexPlusDerivedUnit
      (SheafOfModules.toSheaf (structureSheafRing X)))
      (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft DerivedCategory.Plus.Q
      (Stacks.Cohomology.ModuleComparison.rightDerivedFunctorPlus_sections_forget_iso X ⊤).inv

/-- **The abelian half of the realization comparison commutes with the shift.** -/
instance natTransCommShift_realizationTrans : NatTrans.CommShift (realizationTrans X) ℤ := by
  have := Stacks.DerivedIndexing.natTransCommShift_mapCochainComplexPlusDerivedUnit
    (SheafOfModules.toSheaf (structureSheafRing X))
  dsimp only [realizationTrans]
  infer_instance

end Realization

/-! ### The two models of derived sections and the shift -/

section Models

variable (X : RingedSpace.{u, u}) (U : Opens X.carrier)

open Stacks.Cohomology.DerivedSectionsModels Stacks.Cohomology.DerivedSectionsLeray

/-- An additive functor on the bounded below homotopy category is the restriction of the
functor it induces on the homotopy category. -/
def mapPlusCompιIso {A₁ A₂ : Type*} [Category* A₁] [Category* A₂] [Preadditive A₁]
    [Preadditive A₂] [HasZeroObject A₁] [HasZeroObject A₂] (P : A₁ ⥤ A₂) [P.Additive] :
    P.mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι A₂ ≅
      HomotopyCategory.Plus.ι A₁ ⋙ P.mapHomotopyCategory (ComplexShape.up ℤ) :=
  ObjectProperty.liftCompιIso ..

/-- The isomorphism `mapPlusCompιIso P` commutes with the shift. -/
instance natTransCommShift_mapPlusCompιIso {A₁ A₂ : Type*} [Category* A₁] [Category* A₂]
    [Preadditive A₁] [Preadditive A₂] [HasZeroObject A₁] [HasZeroObject A₂] (P : A₁ ⥤ A₂)
    [P.Additive] : NatTrans.CommShift (mapPlusCompιIso P).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

/-- The localization of the bounded below homotopy category is the restriction of the
localization of the homotopy category. -/
def plusQhCompιIso (A : Type*) [Category* A] [Abelian A] [HasDerivedCategory A] :
    DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι ≅
      HomotopyCategory.Plus.ι A ⋙ DerivedCategory.Qh :=
  ObjectProperty.liftCompιIso ..

/-- The isomorphism `plusQhCompιIso A` commutes with the shift. -/
instance natTransCommShift_plusQhCompιIso (A : Type*) [Category* A] [Abelian A]
    [HasDerivedCategory A] : NatTrans.CommShift (plusQhCompιIso A).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

/-- The two presentations of an additive functor followed by the localization, on `K⁺(𝒜)`:
through the unbounded and through the bounded below homotopy and derived categories. Its
components are identities. -/
def presentationIso {A₁ A₂ : Type*} [Category* A₁] [Category* A₂] [Abelian A₁] [Abelian A₂]
    [HasDerivedCategory A₂] (P : A₁ ⥤ A₂) [P.Additive] :
    HomotopyCategory.Plus.ι A₁ ⋙ (P.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ≅
      (P.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙ DerivedCategory.Plus.ι :=
  (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (mapPlusCompιIso P).symm DerivedCategory.Qh ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft _ (plusQhCompιIso _).symm ≪≫
    (Functor.associator _ _ _).symm

/-- The isomorphism `presentationIso P` commutes with the shift. -/
instance natTransCommShift_presentationIso {A₁ A₂ : Type*} [Category* A₁] [Category* A₂]
    [Abelian A₁] [Abelian A₂] [HasDerivedCategory A₂] (P : A₁ ⥤ A₂) [P.Additive] :
    NatTrans.CommShift (presentationIso P).hom ℤ := by
  simp only [presentationIso, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerLeft_hom]
  infer_instance

/-- `presentationIso` for termwise sections. -/
abbrev sectionsPresentationIso :
    HomotopyCategory.Plus.ι (SheafOfModules.{u} (structureSheafRing X)) ⋙
        ((sectionsOverOpen X U).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh) ≅
      ((sectionsOverOpen X U).mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh) ⋙
        DerivedCategory.Plus.ι :=
  presentationIso (sectionsOverOpen X U)

/-- The comparison `Γ(U, K) ⟶ R⁺Γ(U, K)` commutes with the shift. -/
instance natTransCommShift_boundedSectionsUnitPlus :
    NatTrans.CommShift (boundedSectionsUnitPlus X U) ℤ := by
  have : NatTrans.CommShift (sectionsOverOpen X U).rightDerivedFunctorPlusUnith ℤ :=
    CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit _
  refine NatTrans.commShift_of_eq_conj (sectionsPresentationIso X U)
    (Functor.associator _ _ _).symm
    (Functor.whiskerRight (sectionsOverOpen X U).rightDerivedFunctorPlusUnith
      DerivedCategory.Plus.ι) ?_
  ext K
  simp only [Functor.comp_obj, ObjectProperty.ι_obj, boundedSectionsUnitPlus,
    Functor.whiskerRight_app, ObjectProperty.ι_map, sectionsPresentationIso, presentationIso,
    mapPlusCompιIso, ObjectProperty.liftCompιIso, plusQhCompιIso, Iso.trans_hom, Iso.symm_hom,
    Functor.isoWhiskerRight_hom, Functor.isoWhiskerLeft_hom, Iso.symm_inv, Category.assoc,
    NatTrans.comp_app, Functor.associator_inv_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.comp_id, Category.id_comp]
  refine Eq.trans (Category.id_comp _).symm ?_
  rw [← Category.assoc]
  congr 1
  exact ((Category.comp_id _).trans (map_refl_symm_hom_app
    ((sectionsOverOpen X U).mapHomotopyCategoryPlus ⋙ HomotopyCategory.Plus.ι _)
    DerivedCategory.Qh K)).symm

/-- The comparison `Γ(U, K) ⟶ RΓ(U, K)` commutes with the shift. -/
instance natTransCommShift_boundedSectionsUnitBig :
    NatTrans.CommShift (boundedSectionsUnitBig X U) ℤ := by
  have : NatTrans.CommShift (derivedSectionsOverOpenUnit X U) ℤ :=
    Functor.IsRightDerivedFunctor.natTrans_commShift (derivedSectionsOverOpen X U)
      (derivedSectionsOverOpenUnit X U)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (structureSheafRing X)) (ComplexShape.up ℤ)) ℤ
  have : NatTrans.CommShift (Iso.refl (boundedSectionsToDerivedCategory X U)).hom ℤ :=
    (inferInstance : NatTrans.CommShift (𝟙 (boundedSectionsToDerivedCategory X U)) ℤ)
  let eG : DerivedCategory.Plus.Qh ⋙ (DerivedCategory.Plus.ι ⋙ derivedSectionsOverOpen X U) ≅
      HomotopyCategory.Plus.ι _ ⋙ (DerivedCategory.Qh ⋙ derivedSectionsOverOpen X U) :=
    (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (plusQhCompιIso _) (derivedSectionsOverOpen X U) ≪≫
      Functor.associator _ _ _
  have : NatTrans.CommShift eG.hom ℤ := by
    simp only [eG, Iso.trans_hom, Iso.symm_hom, Functor.isoWhiskerRight_hom]
    infer_instance
  refine NatTrans.commShift_of_eq_conj (Iso.refl _) eG
    (Functor.whiskerLeft (HomotopyCategory.Plus.ι _) (derivedSectionsOverOpenUnit X U)) ?_
  ext K
  simp only [boundedSectionsUnitBig, eG, plusQhCompιIso, ObjectProperty.liftCompιIso, Iso.refl_hom,
    NatTrans.comp_app, Functor.whiskerLeft_app, Iso.trans_inv, Iso.symm_inv,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.comp_id, Category.id_comp]
  exact (Category.comp_id _).symm.trans (congrArg (_ ≫ ·) (isoWhiskerRight_refl_inv_app
    (DerivedCategory.Plus.Qh ⋙ DerivedCategory.Plus.ι) (derivedSectionsOverOpen X U) K).symm)

/-- **The comparison of the bounded below and the unbounded derived sections commutes with the
shift.** Both are right derived functors of termwise sections on `K⁺(𝒪_X)`, the comparison is
compatible with their units, and both units commute with the shift. -/
instance natTransCommShift_boundedDerivedSectionsIso :
    NatTrans.CommShift (boundedDerivedSectionsIso X U).hom ℤ :=
  natTransCommShift_of_rightDerived DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (SheafOfModules.{u} (structureSheafRing X)))
    (boundedSectionsUnitPlus X U) (boundedSectionsUnitBig X U) _
    (boundedDerivedSectionsIso_fac X U)

end Models

/-! ### Forgetting the module structure and the shift -/

section Forget

variable (R : Type u) [Ring R]

/-- The unit of the bounded below right derived functor of `forget : Mod(R) ⥤ Ab`, read in the
unbounded derived category. -/
def forgetPlusUnit :
    HomotopyCategory.Plus.ι (ModuleCat.{u} R) ⋙
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ⟶
      DerivedCategory.Plus.Qh ⋙
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).rightDerivedFunctorPlus ⋙
          DerivedCategory.Plus.ι) :=
  (presentationIso (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})).hom ≫
    Functor.whiskerRight (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).rightDerivedFunctorPlusUnith
      DerivedCategory.Plus.ι ≫
    (Functor.associator _ _ _).hom

/-- The comparison of the functor induced by `forget : Mod(R) ⥤ Ab` on derived categories with
its factorization through the localization, read on bounded below complexes. -/
def forgetUnbUnit :
    HomotopyCategory.Plus.ι (ModuleCat.{u} R) ⋙
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh) ⟶
      DerivedCategory.Plus.Qh ⋙
        (DerivedCategory.Plus.ι ⋙
          (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapDerivedCategory) :=
  Functor.whiskerLeft (HomotopyCategory.Plus.ι (ModuleCat.{u} R))
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapDerivedCategoryFactorsh.inv ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (plusQhCompιIso _).inv
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapDerivedCategory ≫
    (Functor.associator _ _ _).hom

/-- The transformation `forgetPlusUnit R` commutes with the shift. -/
instance natTransCommShift_forgetPlusUnit : NatTrans.CommShift (forgetPlusUnit R) ℤ := by
  have : NatTrans.CommShift
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).rightDerivedFunctorPlusUnith ℤ :=
    CategoryTheory.Functor.natTransCommShiftRightDerivedFunctorPlusUnit _
  dsimp only [forgetPlusUnit]
  infer_instance

/-- The transformation `forgetUnbUnit R` commutes with the shift. -/
instance natTransCommShift_forgetUnbUnit : NatTrans.CommShift (forgetUnbUnit R) ℤ := by
  dsimp only [forgetUnbUnit]
  infer_instance

/-- The transformation `forgetPlusUnit R` is an isomorphism, since `forget : Mod(R) ⥤ Ab` is
exact. -/
instance isIso_forgetPlusUnit : IsIso (forgetPlusUnit R) := by
  have := Functor.isIso_rightDerivedFunctorPlusUnit_of_preservesHomology
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u})
  dsimp only [forgetPlusUnit]
  infer_instance

/-- The transformation `forgetUnbUnit R` is an isomorphism. -/
instance isIso_forgetUnbUnit : IsIso (forgetUnbUnit R) := by
  dsimp only [forgetUnbUnit]
  infer_instance

/-- With the unit `forgetPlusUnit R`, the bounded below right derived functor of
`forget : Mod(R) ⥤ Ab`, read in the unbounded derived category, is a right derived functor of
`forget` on `K⁺(R)` with respect to quasi-isomorphisms. -/
instance isRightDerivedFunctor_forgetPlusUnit :
    ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι).IsRightDerivedFunctor (forgetPlusUnit R)
      (HomotopyCategory.Plus.quasiIso (ModuleCat.{u} R)) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (HomotopyCategory.Plus.ι (ModuleCat.{u} R) ⋙
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh))).isRightDerivedFunctor_of_isIso
    (forgetPlusUnit R) (fun _ => inferInstance)

/-- With the unit `forgetUnbUnit R`, the functor induced by `forget : Mod(R) ⥤ Ab` on derived
categories, restricted to `D⁺(R)`, is a right derived functor of `forget` on `K⁺(R)` with respect
to quasi-isomorphisms. -/
instance isRightDerivedFunctor_forgetUnbUnit :
    (DerivedCategory.Plus.ι ⋙
        (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapDerivedCategory).IsRightDerivedFunctor
      (forgetUnbUnit R) (HomotopyCategory.Plus.quasiIso (ModuleCat.{u} R)) :=
  (HomotopyCategory.Plus.localizerMorphism_derives
      (HomotopyCategory.Plus.ι (ModuleCat.{u} R) ⋙
        ((forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
          DerivedCategory.Qh))).isRightDerivedFunctor_of_isIso
    (forgetUnbUnit R) (fun _ => inferInstance)

/-- **The bounded below right derived functor of `forget : Mod(R) ⥤ Ab` is the functor induced on
derived categories**, read in the unbounded derived category: the uniqueness isomorphism of the
two right derived functors of `forget` on `K⁺(R)`. -/
def forgetComparisonIso :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).rightDerivedFunctorPlus ⋙
        DerivedCategory.Plus.ι ≅
      DerivedCategory.Plus.ι ⋙ (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).mapDerivedCategory :=
  Functor.rightDerivedUnique _ _ (forgetPlusUnit R) (forgetUnbUnit R)
    (HomotopyCategory.Plus.quasiIso (ModuleCat.{u} R))

/-- The isomorphism `forgetComparisonIso R` is compatible with the units `forgetPlusUnit R` and
`forgetUnbUnit R`. -/
theorem forgetComparisonIso_fac :
    forgetPlusUnit R ≫ Functor.whiskerLeft DerivedCategory.Plus.Qh (forgetComparisonIso R).hom =
      forgetUnbUnit R := by
  simp [forgetComparisonIso]

/-- **The comparison `forgetComparisonIso` commutes with the shift.** -/
instance natTransCommShift_forgetComparisonIso :
    NatTrans.CommShift (forgetComparisonIso R).hom ℤ :=
  natTransCommShift_of_rightDerived DerivedCategory.Plus.Qh
    (HomotopyCategory.Plus.quasiIso (ModuleCat.{u} R)) (forgetPlusUnit R) (forgetUnbUnit R) _
    (forgetComparisonIso_fac R)

end Forget

/-! ### The realization comparison as one transformation commuting with the shift -/

section Total

variable (X : RingedSpace.{u, u})

open Stacks.Cohomology.DerivedSectionsModels Stacks.Cohomology.DerivedSectionsLeray

/-- The localization of bounded below complexes is the restriction of the localization of all
complexes. -/
def plusQCompιIso (A : Type*) [Category* A] [Abelian A] [HasDerivedCategory A] :
    DerivedCategory.Plus.Q ⋙ DerivedCategory.Plus.ι ≅
      CochainComplex.Plus.ι A ⋙ DerivedCategory.Q :=
  ObjectProperty.liftCompιIso ..

/-- The isomorphism `plusQCompιIso A` commutes with the shift. -/
instance natTransCommShift_plusQCompιIso (A : Type*) [Category* A] [Abelian A]
    [HasDerivedCategory A] : NatTrans.CommShift (plusQCompιIso A).hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

/-- The abelian half of the realization comparison, read in `D(Ab)`, rebracketed. -/
def realizationAbelianPart :
    ((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.ι ⟶
      DerivedCategory.Plus.Q ⋙
        ((SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).rightDerivedFunctorPlus ⋙
          ((forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
              AddCommGrpCat.{u}).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι)) :=
  Functor.whiskerRight (realizationTrans X) DerivedCategory.Plus.ι ≫
    (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft DerivedCategory.Plus.Q (Functor.associator _ _ _).hom

/-- The transformation `realizationAbelianPart X` commutes with the shift. -/
instance natTransCommShift_realizationAbelianPart :
    NatTrans.CommShift (realizationAbelianPart X) ℤ := by
  dsimp only [realizationAbelianPart]
  infer_instance

/-- The module half of the realization comparison, on `D⁺(𝒪_X)`: forgetting the module structure
after the bounded below derived sections, compared with the unbounded derived sections. -/
def realizationModulePart :
    (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).rightDerivedFunctorPlus ⋙
        ((forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
            AddCommGrpCat.{u}).rightDerivedFunctorPlus ⋙ DerivedCategory.Plus.ι) ⟶
      (DerivedCategory.Plus.ι ⋙ derivedSectionsOverOpen X ⊤) ⋙
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
          AddCommGrpCat.{u}).mapDerivedCategory :=
  Functor.whiskerLeft
      (SheafOfModules.evaluation (structureSheafRing X) (op ⊤)).rightDerivedFunctorPlus
      (forgetComparisonIso ((structureSheafRing X).obj.obj (op ⊤))).hom ≫
    (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (boundedDerivedSectionsIso X ⊤).hom
      (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
        AddCommGrpCat.{u}).mapDerivedCategory

/-- The transformation `realizationModulePart X` commutes with the shift. -/
instance natTransCommShift_realizationModulePart :
    NatTrans.CommShift (realizationModulePart X) ℤ := by
  dsimp only [realizationModulePart]
  infer_instance

/-- The comparison of the localizations of bounded below and of all complexes, rebracketed. -/
def realizationLocalizationPart :
    DerivedCategory.Plus.Q ⋙ ((DerivedCategory.Plus.ι ⋙ derivedSectionsOverOpen X ⊤) ⋙
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
          AddCommGrpCat.{u}).mapDerivedCategory) ⟶
      ((CochainComplex.Plus.ι (SheafOfModules.{u} (structureSheafRing X)) ⋙ DerivedCategory.Q) ⋙
          derivedSectionsOverOpen X ⊤) ⋙
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
          AddCommGrpCat.{u}).mapDerivedCategory :=
  (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight (Functor.associator _ _ _).inv _ ≫
    Functor.whiskerRight (Functor.whiskerRight (plusQCompιIso _).hom
      (derivedSectionsOverOpen X ⊤)) _

/-- The transformation `realizationLocalizationPart X` commutes with the shift. -/
instance natTransCommShift_realizationLocalizationPart :
    NatTrans.CommShift (realizationLocalizationPart X) ℤ := by
  dsimp only [realizationLocalizationPart]
  infer_instance

/-- **The realization comparison of Stacks 01F1, as a natural transformation** from the derived
global sections of the underlying complex of abelian sheaves to the derived global sections in
modules, the module structure forgotten, both read in `D(Ab)`. -/
def realizationTotal :
    ((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus) ⋙
        DerivedCategory.Plus.ι ⟶
      ((CochainComplex.Plus.ι (SheafOfModules.{u} (structureSheafRing X)) ⋙ DerivedCategory.Q) ⋙
          derivedSectionsOverOpen X ⊤) ⋙
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
          AddCommGrpCat.{u}).mapDerivedCategory :=
  realizationAbelianPart X ≫ Functor.whiskerLeft DerivedCategory.Plus.Q (realizationModulePart X) ≫
    realizationLocalizationPart X

/-- **The realization comparison commutes with the shift.** -/
instance natTransCommShift_realizationTotal : NatTrans.CommShift (realizationTotal X) ℤ := by
  dsimp only [realizationTotal]
  infer_instance

/-- The unit of the bounded below right derived functor of an exact functor, on bounded below
complexes, is invertible. -/
instance isIso_mapCochainComplexPlusDerivedUnit {A₁ A₂ : Type*} [Category* A₁] [Category* A₂]
    [Abelian A₁] [Abelian A₂] [HasDerivedCategory A₁] [HasDerivedCategory A₂] [EnoughInjectives A₁]
    (T : A₁ ⥤ A₂) [T.Additive] [PreservesFiniteLimits T] [PreservesFiniteColimits T] :
    IsIso (Functor.mapCochainComplexPlusDerivedUnit T) := by
  have : ∀ K, IsIso ((Functor.mapCochainComplexPlusDerivedUnit T).app K) := fun K => by
    have hu : IsIso (T.rightDerivedFunctorPlusUnith.app
        ((HomotopyCategory.Plus.quotient A₁).obj K)) := by
      have h₀ := T.isIso_totalRightDerivedUnit_app_of_rightAcyclic K.obj K.property
        (fun n => Functor.rightAcyclic_of_exact T _)
      have h₂ := (Functor.isRightDerivedFunctor_iff_isIso_rightDerivedDesc
        ((T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
          DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A₁))
        ((T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
          DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A₁))
        (HomotopyCategory.Plus.quasiIso A₁) T.rightDerivedFunctorPlus
        T.rightDerivedFunctorPlusUnith).1 inferInstance
      rw [← Functor.rightDerived_fac_app
        ((T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerived
          DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A₁))
        ((T.mapHomotopyCategoryPlus ⋙ DerivedCategory.Plus.Qh).totalRightDerivedUnit
          DerivedCategory.Plus.Qh (HomotopyCategory.Plus.quasiIso A₁))
        (HomotopyCategory.Plus.quasiIso A₁) T.rightDerivedFunctorPlus
        T.rightDerivedFunctorPlusUnith]
      infer_instance
    have h₁ : IsIso ((DerivedCategory.Plus.quotientCompQhIso A₂).inv.app
        (T.mapCochainComplexPlus.obj K)) := inferInstance
    have h₃ : IsIso (T.rightDerivedFunctorPlus.map
        ((DerivedCategory.Plus.quotientCompQhIso A₁).hom.app K)) := inferInstance
    rw [Functor.mapCochainComplexPlusDerivedUnit_app]
    exact @IsIso.comp_isIso _ _ _ _ _ _ _ h₁ (@IsIso.comp_isIso _ _ _ _ _ _ _ hu h₃)
  exact NatIso.isIso_of_isIso_app _

/-- The abelian half `realizationTrans X` of the realization comparison is an isomorphism. -/
instance isIso_realizationTrans : IsIso (realizationTrans X) := by
  dsimp only [realizationTrans]
  infer_instance

/-- The realization comparison `realizationTotal X` is an isomorphism. -/
instance isIso_realizationTotal : IsIso (realizationTotal X) := by
  dsimp only [realizationTotal, realizationAbelianPart, realizationModulePart,
    realizationLocalizationPart]
  infer_instance

/-- **The realization comparison of Stacks 01F1 on cohomology**: the hypercohomology of the
underlying complex of abelian sheaves of a bounded below complex of `𝒪_X`-modules is its
hypercohomology computed in modules, the module structure forgotten. -/
def realizationIsoAt (N : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X)))
    (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).obj
        (((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus ⋙
          DerivedCategory.Plus.Q ⋙ (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus).obj N) ≅
      (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}).obj
        ((DerivedCategory.homologyFunctor _ n).obj
          ((derivedSectionsOverOpen X ⊤).obj (DerivedCategory.Q.obj N.1))) :=
  (DerivedCategory.homologyFunctor _ n).mapIso (asIso ((realizationTotal X).app N)) ≪≫
    ((forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).mapDerivedCategoryHomologyIso n).app _

/-- **The realization comparison of Stacks 01F1 commutes with the shift identifications**: it
carries the identification `Hⁿ(X, 𝒦^•[s]) ≅ Hⁿ⁺ˢ(X, 𝒦^•)` of abelian sheaves to the one of
modules. -/
theorem realizationIsoAt_shift (N : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X)))
    (s n n' : ℤ) (h : s + n = n') :
    (realizationIsoAt X (N⟦s⟧) n).hom ≫
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
          (shiftHomologyIsoU
            ((CochainComplex.Plus.ι (SheafOfModules.{u} (structureSheafRing X)) ⋙
              DerivedCategory.Q) ⋙ derivedSectionsOverOpen X ⊤) N s n n' h).hom =
      (shiftHomologyIso ((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus ⋙
          DerivedCategory.Plus.Q ⋙ (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus)
          N s n n' h).hom ≫
        (realizationIsoAt X N n').hom := by
  have e₁ := shiftHomologyIso_eq_U
    ((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus ⋙
      DerivedCategory.Plus.Q ⋙ (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus) N s n n' h
  have e₂ := shiftHomologyIsoU_naturality_of_commShift (realizationTotal X) N s n n' h
  have e₃ := mapDerivedCategoryHomologyIso_shift
    (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u})
    (((CochainComplex.Plus.ι (SheafOfModules.{u} (structureSheafRing X)) ⋙ DerivedCategory.Q) ⋙
      derivedSectionsOverOpen X ⊤).obj N) s n n' h
  have e₄ := ((forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).mapDerivedCategoryHomologyIso n).hom.naturality
    ((((CochainComplex.Plus.ι (SheafOfModules.{u} (structureSheafRing X)) ⋙ DerivedCategory.Q) ⋙
      derivedSectionsOverOpen X ⊤).commShiftIso s).hom.app N)
  simp only [Functor.comp_map] at e₄
  rw [shiftHomologyIsoU_comp_hom
    ((CochainComplex.Plus.ι (SheafOfModules.{u} (structureSheafRing X)) ⋙ DerivedCategory.Q) ⋙
      derivedSectionsOverOpen X ⊤)
    (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).mapDerivedCategory] at e₂
  have eL : (realizationIsoAt X (N⟦s⟧) n).hom ≫
      (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
        (shiftHomologyIsoU
          ((CochainComplex.Plus.ι (SheafOfModules.{u} (structureSheafRing X)) ⋙
            DerivedCategory.Q) ⋙ derivedSectionsOverOpen X ⊤) N s n n' h).hom =
      ((DerivedCategory.homologyFunctor _ n).map ((realizationTotal X).app (N⟦s⟧)) ≫
        ((forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
          AddCommGrpCat.{u}).mapDerivedCategoryHomologyIso n).hom.app
          (((CochainComplex.Plus.ι (SheafOfModules.{u} (structureSheafRing X)) ⋙
            DerivedCategory.Q) ⋙ derivedSectionsOverOpen X ⊤).obj (N⟦s⟧))) ≫
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor _ n).map
            ((((CochainComplex.Plus.ι (SheafOfModules.{u} (structureSheafRing X)) ⋙
              DerivedCategory.Q) ⋙ derivedSectionsOverOpen X ⊤).commShiftIso s).hom.app N)) ≫
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
          (((DerivedCategory.homologyFunctor _ 0).shiftIso s n n' h).hom.app
            (((CochainComplex.Plus.ι (SheafOfModules.{u} (structureSheafRing X)) ⋙
              DerivedCategory.Q) ⋙ derivedSectionsOverOpen X ⊤).obj N)) :=
    congrArg (_ ≫ ·)
      ((forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}).map_comp
        _ _)
  rw [eL, e₁]
  exact realization_paste _ _ _ _ _ _ _ _ _ _ _ e₂ e₃ e₄

/-- **The realization comparison is natural** in the complex. -/
theorem realizationIsoAt_naturality
    {N N' : CochainComplex.Plus (SheafOfModules.{u} (structureSheafRing X))} (g : N ⟶ N')
    (n : ℤ) :
    (DerivedCategory.Plus.homologyFunctor AddCommGrpCat.{u} n).map
        (((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus ⋙
          DerivedCategory.Plus.Q ⋙ (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus).map g) ≫
        (realizationIsoAt X N' n).hom =
      (realizationIsoAt X N n).hom ≫
        (forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤))) AddCommGrpCat.{u}).map
          ((DerivedCategory.homologyFunctor _ n).map
            ((derivedSectionsOverOpen X ⊤).map (DerivedCategory.Q.map g.hom))) := by
  have e₁ := (realizationTotal X).naturality g
  have e₂ := ((forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
      AddCommGrpCat.{u}).mapDerivedCategoryHomologyIso n).hom.naturality
    ((derivedSectionsOverOpen X ⊤).map (DerivedCategory.Q.map g.hom))
  simp only [Functor.comp_map] at e₁ e₂
  let H := DerivedCategory.homologyFunctor AddCommGrpCat.{u} n
  have e₁' : H.map (DerivedCategory.Plus.ι.map
      (((SheafOfModules.toSheaf (structureSheafRing X)).mapCochainComplexPlus ⋙
        DerivedCategory.Plus.Q ⋙ (sectionsFunctor X.carrier ⊤).rightDerivedFunctorPlus).map g)) ≫
      H.map ((realizationTotal X).app N') =
      H.map ((realizationTotal X).app N) ≫
        H.map ((forget₂ (ModuleCat.{u} ((structureSheafRing X).obj.obj (op ⊤)))
          AddCommGrpCat.{u}).mapDerivedCategory.map
          ((derivedSectionsOverOpen X ⊤).map (DerivedCategory.Q.map g.hom))) :=
    (H.map_comp _ _).symm.trans ((congrArg H.map e₁).trans (H.map_comp _ _))
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) e₁').trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e₂).trans (Category.assoc _ _ _).symm)))

end Total

end Stacks.Cohomology.RealizationShift

end
