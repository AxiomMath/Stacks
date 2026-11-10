module

public import StacksFrontier.Homology.DerivedIndexing.Composite
public import StacksFrontier.Topology.Sheaves.Cohomology.CechDerivedComparison.ConnectingMorphism

/-!
# The two comparisons of the indexings of right derived functors agree

Let `F : 𝒜 ⥤ ℬ` be an additive functor between abelian categories, `𝒜` with enough injectives.
The `ℕ`-indexed right derived functors `F.rightDerived n` (computed on injective resolutions) and
the `ℤ`-indexed ones `F.rightDerivedPlus n` (cohomology of `RF : D⁺(𝒜) ⥤ D⁺(ℬ)`) are compared in
the library twice: by `Stacks.DerivedIndexing.rightDerivedIso`, and by
`Stacks.Cohomology.HigherDirectImagePresheaf.derivedPlusToStandard` in the opposite direction.
This file proves that they are inverse to each other. Both are built from the chosen injective
resolutions; the content is that their constituent identifications agree.

## Main results

* `Stacks.DerivedIndexing.rightDerivedIso_inv_app_eq` and
  `Stacks.DerivedIndexing.rightDerivedIso_inv_eq`: **`rightDerivedIso` is the inverse of
  `derivedPlusToStandard`.**
* `Stacks.DerivedIndexing.resolutionDerivedIso_hom_eq`: the two identifications of `X[0]` with
  its chosen extended injective resolution in `D⁺(𝒜)` agree.
* `Stacks.DerivedIndexing.isoRightDerivedObj_inv_injectiveResolution`: at the chosen resolution,
  `isoRightDerivedObj` is the comparison of homology in the homotopy category with homology of
  complexes.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape
open Stacks.Cohomology.HigherDirectImagePresheaf

namespace Stacks.DerivedIndexing

variable {A : Type*} {B : Type*} [Category* A] [Category* B] [Abelian A] [Abelian B]
  [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] (F : A ⥤ B) [F.Additive]

/-- The identification `resolutionDerivedIso` of `M[0]` with the extension of the chosen injective
resolution of `M`, in `D⁺(𝒜)`, is the identification `singleIsoResPlusQh`. -/
theorem resolutionDerivedIso_hom_eq (M : A) :
    (resolutionDerivedIso (injectiveResolution M)).hom =
      (singleIsoResPlusQh (C := A)).hom.app M := by
  apply DerivedCategory.Plus.ι.map_injective
  have h1 := Q_map_resolutionSingleHom (injectiveResolution M)
  have hq : (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app M =
      (DerivedCategory.quotientCompQhIso A).inv.app ((CochainComplex.singleFunctor A 0).obj M) ≫
        𝟙 _ := rfl
  have h3 := DerivedCategory.quotientCompQhIso_hom_naturality (injectiveResolution M).ι'
  have key : DerivedCategory.Plus.ι.map ((singleIsoResPlusQh (C := A)).hom.app M) ≫
      (DerivedCategory.quotientCompQhIso A).hom.app
        ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat) =
      DerivedCategory.Q.map (resolutionSingleHom (injectiveResolution M)) := by
    have hs : (DerivedCategory.singleFunctorIsoCompQh A 0).hom.app M ≫
        (DerivedCategory.quotientCompQhIso A).hom.app ((CochainComplex.singleFunctor A 0).obj M) =
        𝟙 _ := (eq_whisker hq _).trans ((eq_whisker (Category.comp_id _) _).trans
          (Iso.inv_hom_id_app _ _))
    refine (eq_whisker (ι_map_singleIsoResPlusQh_hom_app_eq (C := A) M) _).trans ?_
    refine (Category.assoc _ _ _).trans ?_
    refine (whisker_eq _ h3).trans ?_
    exact (Category.assoc _ _ _).symm.trans ((eq_whisker hs _).trans (Category.id_comp _))
  exact (cancel_mono ((DerivedCategory.quotientCompQhIso A).app
    ((injectiveResolution M).cocomplex.extend ComplexShape.embeddingUpNat)).hom).mp
      (h1.trans key.symm)

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The two comparisons of the extension of `F(K)` with `F` of the extension of `K` are
mutually inverse. -/
theorem mapExtendIso_inv_eq_derivedMapExtendIso_hom (K : CochainComplex A ℕ) :
    (mapExtendIso F ComplexShape.embeddingUpNat K).inv =
      (derivedMapExtendIso F ComplexShape.embeddingUpNat K).hom := by
  have h : ∀ o : Option ℕ, (mapExtendXIso F K o).hom ≫ (derivedMapExtendXIso F K o).hom = 𝟙 _ := by
    intro o
    cases o with
    | some i => exact Category.id_comp _
    | none => exact (HomologicalComplex.extend.isZero_X _ rfl).eq_of_src _ _
  rw [← cancel_epi (mapExtendIso F ComplexShape.embeddingUpNat K).hom, Iso.hom_inv_id]
  ext j
  exact (h _).symm

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
/-- A conjugation, stated with every object and morphism a variable so that it applies across
the junction of two presentations of the same object. -/
private theorem conj_aux {C : Type*} [Category* C] {T S S' T' U V : C} (ai : T ⟶ S)
    (ahX : S ⟶ T) (Hqf : S ⟶ S') (one : S' ⟶ S') (ahY : S' ⟶ T') (g g' : T ⟶ T') (e : T' ⟶ U)
    (k : U ⟶ V) (hone : one = 𝟙 _) (hnat : Hqf ≫ ahY = ahX ≫ g) (hg : g = g')
    (hinv : ai ≫ ahX = 𝟙 _) :
    ai ≫ (Hqf ≫ one ≫ ahY ≫ e ≫ k) = 𝟙 _ ≫ (g' ≫ e) ≫ k := by
  subst hone hg
  rw [Category.id_comp, ← Category.assoc Hqf, hnat]
  simp only [Category.assoc, reassoc_of% hinv, Category.id_comp]

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The homotopy-category half of the comparison of `rightDerivedIso` with
`derivedPlusToStandardObj`: the two identifications of the cohomology of the extension of `F(K)`
with the cohomology of `F(K)` agree. -/
theorem homologyFunctorFactors_inv_extendMapHomologyIso_inv (K : CochainComplex A ℕ) (n : ℕ) :
    (HomotopyCategory.homologyFunctorFactors B (up ℤ) (n : ℤ)).inv.app
        ((F.mapHomologicalComplex (up ℤ)).obj (K.extend ComplexShape.embeddingUpNat)) ≫
      (extendMapHomologyIso F K n).inv =
    (homologyFunctorObjIso _ (n : ℤ)).hom ≫ (extendedHomologyTailIso F K n).hom ≫
      (HomotopyCategory.homologyFunctorFactors B (up ℕ) n).inv.app
        ((F.mapHomologicalComplex (up ℕ)).obj K) := by
  have hnat := (HomotopyCategory.homologyFunctorFactors B (up ℤ) (n : ℤ)).hom.naturality
    (mapExtendIso F ComplexShape.embeddingUpNat K).inv
  change (HomotopyCategory.homologyFunctorFactors B (up ℤ) (n : ℤ)).inv.app _ ≫
      ((HomotopyCategory.homologyFunctor B (up ℤ) (n : ℤ)).map
          ((HomotopyCategory.quotient B (up ℤ)).map
            (mapExtendIso F ComplexShape.embeddingUpNat K).inv) ≫
        (HomotopyCategory.homologyFunctor B (up ℤ) (n : ℤ)).map (𝟙 _) ≫
        (HomotopyCategory.homologyFunctorFactors B (up ℤ) (n : ℤ)).hom.app _ ≫
        (((F.mapHomologicalComplex (up ℕ)).obj K).extendHomologyIso
          ComplexShape.embeddingUpNat (j := n) (j' := (n : ℤ)) (by simp)).hom ≫
        (HomotopyCategory.homologyFunctorFactors B (up ℕ) n).inv.app _) = _
  exact conj_aux _ _ _ _ _ _ _ _ _ (CategoryTheory.Functor.map_id _ _) hnat
    (congrArg (fun φ => HomologicalComplex.homologyMap φ (n : ℤ))
      (mapExtendIso_inv_eq_derivedMapExtendIso_hom F K)) (Iso.inv_hom_id_app _ _)

/-- Precomposing with `G.map f` is the identity when `f` is the identity. -/
private theorem comp_map_eq_of_eq_id {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {X : C} {f : X ⟶ X} (hf : f = 𝟙 X) {Y : D} (u : Y ⟶ G.obj X) : u ≫ G.map f = u := by
  rw [hf, CategoryTheory.Functor.map_id, Category.comp_id]

omit [HasDerivedCategory A] [HasDerivedCategory B] in
/-- At the chosen injective resolution, `CategoryTheory.InjectiveResolution.isoRightDerivedObj`
is the identification of the homology of the homotopy category with the homology of complexes. -/
theorem isoRightDerivedObj_inv_injectiveResolution (M : A) (n : ℕ) :
    ((injectiveResolution M).isoRightDerivedObj F n).inv =
      (HomotopyCategory.homologyFunctorFactors B (up ℕ) n).inv.app
        ((F.mapHomologicalComplex (up ℕ)).obj (injectiveResolution M).cocomplex) := by
  have e : (injectiveResolution M).iso.inv = 𝟙 _ :=
    HomotopyCategory.eq_of_homotopy _ _ (InjectiveResolution.descIdHomotopy _ _)
  have h : ((injectiveResolution M).isoRightDerivedToHomotopyCategoryObj F).inv = 𝟙 _ := by
    change (F.mapHomotopyCategoryFactors (up ℕ)).inv.app _ ≫
      (F.mapHomotopyCategory (up ℕ)).map (injectiveResolution M).iso.inv = 𝟙 _
    exact comp_map_eq_of_eq_id (F.mapHomotopyCategory (up ℕ)) e _
  change (HomotopyCategory.homologyFunctorFactors B (up ℕ) n).inv.app _ ≫
    (HomotopyCategory.homologyFunctor B (up ℕ) n).map
      ((injectiveResolution M).isoRightDerivedToHomotopyCategoryObj F).inv = _
  exact comp_map_eq_of_eq_id (HomotopyCategory.homologyFunctor B (up ℕ) n) h _

omit [EnoughInjectives A] [HasDerivedCategory A] [HasDerivedCategory B] in
/-- The bookkeeping of `rightDerivedIso_inv_app_eq`, with every object and morphism a variable so
that it applies across the junctions between the different presentations of the same objects. -/
private theorem assemble_aux {C : Type*} [Category* C]
    {X₀ X₁ X₂ X₃ Y₁ Y₂ Y₃ Y₄ X₄ : C}
    (a a' : X₀ ⟶ X₁) (b b' : X₁ ⟶ X₂) (c : X₂ ⟶ X₃) (d : X₃ ⟶ X₄)
    (p : X₂ ⟶ Y₁) (q : Y₁ ⟶ Y₂) (r : Y₂ ⟶ X₃) (s : Y₂ ⟶ Y₃) (t : Y₃ ⟶ Y₄) (u u' : Y₄ ⟶ X₄)
    (dd : X₀ ⟶ X₂) (e : X₂ ⟶ Y₄)
    (ha : a = a') (hb : b = b') (hc : c = p ≫ q ≫ r) (hrd : r ≫ d = s ≫ t ≫ u')
    (hdd : dd = a' ≫ b') (he : e = p ≫ q ≫ s ≫ t) (hu : u' = u) :
    (a ≫ b ≫ c) ≫ d = dd ≫ e ≫ u := by
  subst ha hb hc hdd he hu
  simp only [Category.assoc, hrd]

/-- **`rightDerivedIso` is the inverse of `derivedPlusToStandard`**, at each object. -/
theorem rightDerivedIso_inv_app_eq (n : ℕ) (M : A) :
    (rightDerivedIso F n).inv.app M = (derivedPlusToStandardObj F M n).hom := by
  have h1 : (rightDerivedIso F n).inv.app M =
      (rightDerivedPlusIsoRes F n).hom.app M ≫ (rightDerivedIsoRes F n).inv.app M := rfl
  rw [h1, rightDerivedPlusIsoRes_hom_app, derivedPlusToStandardObj,
    derivedPlusToStandardObjOfResolution_eq_trans]
  set I := injectiveResolution M
  set L := (F.mapHomologicalComplex (up ℤ)).obj (I.cocomplex.extend ComplexShape.embeddingUpNat)
  have hunit : (resDerivedIso F).inv.app M =
      inv (F.rightDerivedFunctorPlusUnith.app (resPlus.obj M)) :=
    IsIso.eq_inv_of_hom_inv_id ((resDerivedIso F).hom_inv_id_app M)
  have hplus : (plusHomologyIso (D := B) (n : ℤ)).hom.app
      (F.mapHomotopyCategoryPlus.obj (resPlus.obj M)) =
      (DerivedCategory.homologyFunctor B (n : ℤ)).map
          ((DerivedCategory.quotientCompQhIso B).hom.app L) ≫
        (DerivedCategory.homologyFunctorFactors B (n : ℤ)).hom.app L ≫
          (HomotopyCategory.homologyFunctorFactors B (up ℤ) (n : ℤ)).inv.app L := by
    refine ((eq_whisker (CategoryTheory.Functor.map_id _ _) _).trans
      (Category.id_comp _)).trans ?_
    exact DerivedCategory.homologyFunctorFactorsh_hom_app_quotient_obj (C := B) L (n : ℤ)
  have htail := homologyFunctorFactors_inv_extendMapHomologyIso_inv F I.cocomplex n
  have hiso := isoRightDerivedObj_inv_injectiveResolution F M n
  have hd : (derivedPlusResolutionHomologyIso F I n).hom =
      (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
          (F.rightDerivedFunctorPlus.map (resolutionDerivedIso I).hom) ≫
        (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
          (inv (F.rightDerivedFunctorPlusUnith.app
            ((HomotopyCategory.Plus.quotient A).obj (resolutionCochainPlus I)))) :=
    CategoryTheory.Functor.map_comp _ _ _
  exact assemble_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (congrArg (fun φ => (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map
      (F.rightDerivedFunctorPlus.map φ)) (resolutionDerivedIso_hom_eq M).symm)
    (congrArg (fun φ => (DerivedCategory.Plus.homologyFunctor B (n : ℤ)).map φ) hunit)
    hplus htail hd rfl hiso.symm

/-- **`rightDerivedIso` is the inverse of `derivedPlusToStandard`.** -/
theorem rightDerivedIso_inv_eq (n : ℕ) :
    (rightDerivedIso F n).inv = (derivedPlusToStandard F n).hom := by
  ext M
  exact rightDerivedIso_inv_app_eq F n M

end Stacks.DerivedIndexing

end
