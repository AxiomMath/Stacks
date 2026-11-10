module

public import Mathlib
public import StacksFrontier.RingTheory.Flat.Nilpotent
public import StacksFrontier.RingTheory.Ideal.Quotient.MapBijective
public import StacksFrontier.RingTheory.Ideal.Quotient.Small
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryEquivalence
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Algebra.Homology.TotalComplexQuasiIso
public import StacksFrontier.Algebra.Module.IPowerTorsion
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.DerivedComplete.AdicKoszulCompletion
public import StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalars
public import StacksFrontier.Homology.KInjective.ChangeOfRings
public import StacksFrontier.RingTheory.Cech.Substrate
public import StacksFrontier.RingTheory.Etale.LiftFactorization
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingFlatIsomorphism
public import StacksFrontier.RingTheory.Localization.Glueing.FormalGlueingKoszulBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.ExtensionByZero.DerivedAdjunction
import StacksFrontier.AlgebraicGeometry.ProEtale.DerivedCompleteSections

/-!
# Derived adjunctions and Hom-vanishing against bounded complexes

First part of `StacksFrontier.Homology.DerivedComplete.CompleteRestrictScalarsEquivalence`.
It contains the general category-theoretic input: restricting an adjunction to an equivalence of
full subcategories, inducing adjunctions on homotopy and derived categories, the derived
adjunction for restriction of scalars, and the projection of a bounded below complex onto its
lowest term together with the resulting Hom-vanishing and bijectivity statements against
objects on which multiplication by an element is invertible or which are derived complete.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

attribute [local instance] HasDerivedCategory.standard

universe uA uB v u w

namespace CompleteRestrictScalarsEquivalence

set_option backward.isDefEq.respectTransparency false


open StacksDraft.TotalComplexQuasiIso
open scoped ZeroObject

private theorem isDerivedComplete_iff_isIso_difference
    (A : Type u) [CommRing A] (I : Ideal A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (K : DerivedCategory (ModuleCat.{v} A)) :
    IsDerivedComplete I K ↔ ∀ f ∈ I,
      IsIso (Pi.lift (fun n : ℕ => Pi.π (fun _ : ℕ => K) n -
        Pi.π (fun _ : ℕ => K) (n + 1) ≫ (f • 𝟙 K))) :=
  Iff.rfl

private theorem isDerivedComplete_of_iso
    (A : Type u) [CommRing A] (I : Ideal A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    {K L : DerivedCategory (ModuleCat.{v} A)} (e : K ≅ L)
    (hK : IsDerivedComplete I K) : IsDerivedComplete I L := by
  rw [isDerivedComplete_iff_isIso_difference] at hK ⊢
  intro f hf
  let eP := Pi.mapIso (fun _ : ℕ => e)
  let dK := Pi.lift (fun n : ℕ => Pi.π (fun _ : ℕ => K) n -
    Pi.π (fun _ : ℕ => K) (n + 1) ≫ (f • 𝟙 K))
  let dL := Pi.lift (fun n : ℕ => Pi.π (fun _ : ℕ => L) n -
    Pi.π (fun _ : ℕ => L) (n + 1) ≫ (f • 𝟙 L))
  have hd : eP.hom ≫ dL = dK ≫ eP.hom := by
    apply Pi.hom_ext
    intro n
    simp [dK, dL, eP, Category.assoc, Preadditive.comp_sub, Preadditive.sub_comp]
  have : IsIso dK := hK f hf
  have : IsIso (eP.hom ≫ dL) := by rw [hd]; infer_instance
  exact IsIso.of_isIso_comp_left eP.hom dL

/-- **A left adjoint whose counit is invertible on a subcategory, and which reflects
isomorphisms, restricts to an equivalence of full subcategories.** Let `F ⊣ G`, let `F` reflect
isomorphisms, let `F` carry the objects satisfying `Q` into those satisfying `P` and `G` the
objects satisfying `P` into those satisfying `Q`, and let the counit be invertible at every
object satisfying `P`. Then the lift of `F` to `Q.FullSubcategory ⥤ P.FullSubcategory` is an
equivalence. -/
theorem isEquivalence_lift_of_counit
    {C D : Type*} [Category C] [Category D]
    {F : C ⥤ D} {G : D ⥤ C} (adj : F ⊣ G) [F.ReflectsIsomorphisms]
    (P : ObjectProperty D) (Q : ObjectProperty C)
    (hF : ∀ X : Q.FullSubcategory, P (F.obj X.obj))
    (hG : ∀ Y : P.FullSubcategory, Q (G.obj Y.obj))
    (hε : ∀ Y : P.FullSubcategory, IsIso (adj.counit.app Y.obj)) :
    (P.lift (Q.ι ⋙ F) hF).IsEquivalence := by
  let F' := P.lift (Q.ι ⋙ F) hF
  let G' := Q.lift (P.ι ⋙ G) hG
  have hη (X : Q.FullSubcategory) : IsIso (adj.unit.app X.obj) := by
    have : IsIso (adj.counit.app (F.obj X.obj)) := hε (F'.obj X)
    have : IsIso (F.map (adj.unit.app X.obj) ≫ adj.counit.app (F.obj X.obj)) := by
      rw [adj.left_triangle_components X.obj]
      exact IsIso.id _
    have : IsIso (F.map (adj.unit.app X.obj)) :=
      IsIso.of_isIso_comp_right _ (adj.counit.app (F.obj X.obj))
    exact isIso_of_reflects_iso (adj.unit.app X.obj) F
  let e : Q.FullSubcategory ≌ P.FullSubcategory :=
    { functor := F'
      inverse := G'
      unitIso := NatIso.ofComponents
        (fun X ↦ by
          have := hη X
          exact Q.isoMk (asIso (adj.unit.app X.obj)))
        (fun f ↦ by ext; exact adj.unit.naturality f.hom)
      counitIso := NatIso.ofComponents
        (fun Y ↦ by
          have := hε Y
          exact P.isoMk (asIso (adj.counit.app Y.obj)))
        (fun f ↦ by ext; exact adj.counit.naturality f.hom) }
  exact e.isEquivalence_functor


/-- **An exact functor which reflects isomorphisms reflects them on derived categories**: if
`F` reflects isomorphisms of `C`, then `F.mapDerivedCategory` reflects isomorphisms of `D(C)`. -/
theorem reflectsIsomorphisms_mapDerivedCategory
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [F.ReflectsIsomorphisms] : F.mapDerivedCategory.ReflectsIsomorphisms where
  reflects {X Y} f hf := by
    rw [DerivedCategory.isIso_iff]
    intro n
    let e₀ : F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        HomologicalComplex.homologyFunctor D (ComplexShape.up ℤ) n ≅
        HomologicalComplex.homologyFunctor C (ComplexShape.up ℤ) n ⋙ F :=
      NatIso.ofComponents (fun K ↦ (K.sc n).mapHomologyIso F) (fun ψ ↦
        ShortComplex.mapHomologyIso_hom_naturality
          ((HomologicalComplex.shortComplexFunctor C (ComplexShape.up ℤ) n).map ψ) F)
    let e : F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n ≅
        DerivedCategory.homologyFunctor C n ⋙ F :=
      Localization.liftNatIso DerivedCategory.Q
        (HomologicalComplex.quasiIso C (ComplexShape.up ℤ))
        (DerivedCategory.Q ⋙ (F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n))
        (DerivedCategory.Q ⋙ (DerivedCategory.homologyFunctor C n ⋙ F)) _ _
        (Functor.isoWhiskerRight F.mapDerivedCategoryFactors
            (DerivedCategory.homologyFunctor D n) ≪≫
          Functor.isoWhiskerLeft (F.mapHomologicalComplex (ComplexShape.up ℤ))
            (DerivedCategory.homologyFunctorFactors D n) ≪≫ e₀ ≪≫
          Functor.isoWhiskerRight (DerivedCategory.homologyFunctorFactors C n).symm F)
    have : IsIso ((F.mapDerivedCategory ⋙ DerivedCategory.homologyFunctor D n).map f) :=
      inferInstanceAs (IsIso ((DerivedCategory.homologyFunctor D n).map
        (F.mapDerivedCategory.map f)))
    have : IsIso (F.map ((DerivedCategory.homologyFunctor C n).map f)) :=
      (NatIso.isIso_map_iff e f).mp this
    exact isIso_of_reflects_iso ((DerivedCategory.homologyFunctor C n).map f) F

universe u₁ u₂ u₃ u₄ v₁ v₂ v₃ v₄
/-- **An adjunction of additive functors induces one on homotopy categories.** -/
noncomputable def homotopyAdjunction
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G) :
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⊣
      G.mapHomotopyCategory (ComplexShape.up ℤ) := by
  let : CatCommSq (F.mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient C _) (HomotopyCategory.quotient D _)
      (F.mapHomotopyCategory (ComplexShape.up ℤ)) :=
    ⟨(F.mapHomotopyCategoryFactors _).symm⟩
  let : CatCommSq (G.mapHomologicalComplex (ComplexShape.up ℤ))
      (HomotopyCategory.quotient D _) (HomotopyCategory.quotient C _)
      (G.mapHomotopyCategory (ComplexShape.up ℤ)) :=
    ⟨(G.mapHomotopyCategoryFactors _).symm⟩
  exact (adj.mapHomologicalComplex (ComplexShape.up ℤ)).localization
    (HomotopyCategory.quotient C _) (HomologicalComplex.homotopyEquivalences C _)
    (HomotopyCategory.quotient D _) (HomologicalComplex.homotopyEquivalences D _) _ _

/-- The descent of an adjunction's Hom-bijection to localizations, at a fixed object `I` of the
target whose morphism groups the localization functor computes faithfully and fully. -/
lemma bijective_desc_of_adjunction
    {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₃} {D₂ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D₁] [Category.{v₄} D₂]
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (adj : F ⊣ G)
    (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) [L₁.EssSurj]
    (F' : D₁ ⥤ D₂) (e : L₁ ⋙ F' ≅ F ⋙ L₂) (I : C₂)
    (hI : ∀ X, Function.Bijective (L₂.map : (X ⟶ I) → _))
    (hGI : ∀ X, Function.Bijective (L₁.map : (X ⟶ G.obj I) → _))
    (X : D₁) :
    Function.Bijective (fun g : X ⟶ L₁.obj (G.obj I) =>
      F'.map g ≫ e.hom.app (G.obj I) ≫ L₂.map (adj.counit.app I)) := by
  have h (Y : C₁) : Function.Bijective (fun g : L₁.obj Y ⟶ L₁.obj (G.obj I) =>
      F'.map g ≫ e.hom.app (G.obj I) ≫ L₂.map (adj.counit.app I)) := by
    have hh := ((Iso.homCongr (e.app Y).symm (Iso.refl (L₂.obj I))).bijective).comp
      ((hI (F.obj Y)).comp (adj.homEquiv Y I).symm.bijective)
    have heq : (fun k : Y ⟶ G.obj I =>
        (Iso.homCongr (e.app Y).symm (Iso.refl (L₂.obj I)))
          (L₂.map ((adj.homEquiv Y I).symm k))) =
        (fun k : Y ⟶ G.obj I =>
          F'.map (L₁.map k) ≫ e.hom.app (G.obj I) ≫ L₂.map (adj.counit.app I)) := by
      funext k
      simp only [Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id,
        Adjunction.homEquiv_counit, Functor.map_comp]
      simpa only [Functor.comp_map, Category.assoc, Iso.app_hom] using
        congrArg (fun t => t ≫ L₂.map (adj.counit.app I)) (e.hom.naturality k).symm
    dsimp only [Function.comp_def] at hh
    rw [heq] at hh
    exact (Function.Bijective.of_comp_iff _ (hGI Y)).mp hh
  let i := L₁.objObjPreimageIso X
  have hh := (h (L₁.objPreimage X)).comp (Iso.homCongr i.symm (Iso.refl _)).bijective
  have heq : (fun g : X ⟶ L₁.obj (G.obj I) =>
      F'.map ((Iso.homCongr i.symm (Iso.refl _)) g) ≫
        e.hom.app (G.obj I) ≫ L₂.map (adj.counit.app I)) =
      (fun g : X ⟶ L₁.obj (G.obj I) =>
        (Iso.homCongr (F'.mapIso i).symm (Iso.refl _))
          (F'.map g ≫ e.hom.app (G.obj I) ≫ L₂.map (adj.counit.app I))) := by
    funext g
    simp only [Iso.homCongr_apply, Iso.symm_inv, Iso.refl_hom, Category.comp_id,
      Functor.map_comp, Functor.mapIso_hom, Category.assoc]
  dsimp only [Function.comp_def] at hh
  rw [heq] at hh
  exact (Function.Bijective.of_comp_iff' (Iso.homCongr (F'.mapIso i).symm
    (Iso.refl _)).bijective _).mp hh

/-- **An adjunction descends along localizations once the target has enough good models.** Let
`F ⊣ G`, let `L₁`, `L₂` be localization functors with `L₁` essentially surjective, and let `F'`
be a functor with `L₁ ⋙ F' ≅ F ⋙ L₂`. If every object of the localized target is isomorphic to
`L₂ I` for some `I` satisfying `P`, and if `L₂` and `L₁` compute the morphism groups into `I`
and into `G I` bijectively for such `I`, then `F'` has a right adjoint, whose counit is
computed from that of `F ⊣ G` at the chosen model. -/
theorem exists_adjunction_of_models
    {C₁ : Type u₁} {C₂ : Type u₂} {D₁ : Type u₃} {D₂ : Type u₄}
    [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} D₁] [Category.{v₄} D₂]
    {F : C₁ ⥤ C₂} {G : C₂ ⥤ C₁} (adj : F ⊣ G)
    (L₁ : C₁ ⥤ D₁) (L₂ : C₂ ⥤ D₂) [L₁.EssSurj]
    (F' : D₁ ⥤ D₂) (e : L₁ ⋙ F' ≅ F ⋙ L₂)
    (P : C₂ → Prop)
    (hmodel : ∀ Y : D₂, ∃ I : C₂, P I ∧ Nonempty (L₂.obj I ≅ Y))
    (hI : ∀ I, P I → ∀ X, Function.Bijective (L₂.map : (X ⟶ I) → _))
    (hGI : ∀ I, P I → ∀ X, Function.Bijective (L₁.map : (X ⟶ G.obj I) → _)) :
    ∃ (G' : D₂ ⥤ D₁) (adj' : F' ⊣ G'), ∀ Y,
      ∃ (I : C₂) (_ : P I) (i : L₂.obj I ≅ Y) (j : G'.obj Y ≅ L₁.obj (G.obj I)),
        adj'.counit.app Y = F'.map j.hom ≫ e.hom.app (G.obj I) ≫
          L₂.map (adj.counit.app I) ≫ i.hom := by
  classical
  choose I hP hi using hmodel
  let i (Y : D₂) := (hi Y).some
  let G₀ (Y : D₂) := L₁.obj (G.obj (I Y))
  let ε (Y : D₂) : F'.obj (G₀ Y) ⟶ Y :=
    e.hom.app (G.obj (I Y)) ≫ L₂.map (adj.counit.app (I Y)) ≫ (i Y).hom
  have hb (X : D₁) (Y : D₂) :
      Function.Bijective (fun g : X ⟶ G₀ Y => F'.map g ≫ ε Y) := by
    have h := ((Iso.homCongr (Iso.refl _) (i Y)).bijective).comp
      (bijective_desc_of_adjunction adj L₁ L₂ F' e (I Y) (hI _ (hP Y)) (hGI _ (hP Y)) X)
    simpa only [Function.comp_def, Iso.homCongr_apply, Iso.refl_inv, Category.id_comp,
      Category.assoc] using h
  let E (X : D₁) (Y : D₂) : (F'.obj X ⟶ Y) ≃ (X ⟶ G₀ Y) :=
    (Equiv.ofBijective _ (hb X Y)).symm
  have hE (X' X : D₁) (Y : D₂) (f : X' ⟶ X) (g : F'.obj X ⟶ Y) :
      E X' Y (F'.map f ≫ g) = f ≫ E X Y g := by
    apply (E X' Y).symm.injective
    rw [Equiv.symm_apply_apply]
    change F'.map f ≫ g = F'.map (f ≫ E X Y g) ≫ ε Y
    rw [F'.map_comp, Category.assoc]
    congr 1
    exact ((E X Y).symm_apply_apply g).symm
  refine ⟨Adjunction.rightAdjointOfEquiv E hE, Adjunction.adjunctionOfEquivRight E hE,
    fun Y => ⟨I Y, hP Y, i Y, Iso.refl _, ?_⟩⟩
  change (E (G₀ Y) Y).symm (𝟙 _) = _
  change F'.map (𝟙 _) ≫ ε Y = _
  change F'.map (𝟙 (G₀ Y)) ≫ ε Y = F'.map (𝟙 (G₀ Y)) ≫ ε Y
  rfl


/-- **An adjunction of exact functors induces one on derived categories, when the target has
K-injective resolutions.** For `F ⊣ G` with `F` additive and exact, the functor
`F.mapDerivedCategory` has a right adjoint, and its counit is computed at a K-injective model. -/
theorem exists_derivedAdjunction
    {C D : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    [Category D] [Abelian D] [HasDerivedCategory D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive]
    [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    (adj : F ⊣ G)
    (hres : ∀ K : CochainComplex D ℤ, ∃ (I : CochainComplex D ℤ)
      (f : K ⟶ I), QuasiIso f ∧ I.IsKInjective) :
    ∃ (RG : DerivedCategory D ⥤ DerivedCategory C)
      (adj' : F.mapDerivedCategory ⊣ RG), ∀ Y,
      ∃ (I : HomotopyCategory D (ComplexShape.up ℤ)) (_ : CochainComplex.IsKInjective I.as)
        (i : DerivedCategory.Qh.obj I ≅ Y)
        (j : RG.obj Y ≅ DerivedCategory.Qh.obj
          ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj I)),
        adj'.counit.app Y = F.mapDerivedCategory.map j.hom ≫
          F.mapDerivedCategoryFactorsh.hom.app
            ((G.mapHomotopyCategory (ComplexShape.up ℤ)).obj I) ≫
          DerivedCategory.Qh.map ((homotopyAdjunction adj).counit.app I) ≫ i.hom := by
  apply exists_adjunction_of_models (homotopyAdjunction adj)
    DerivedCategory.Qh DerivedCategory.Qh F.mapDerivedCategory
    F.mapDerivedCategoryFactorsh (fun I => CochainComplex.IsKInjective I.as)
  · intro Y
    obtain ⟨I, f, hf, hI⟩ := hres (DerivedCategory.Q.objPreimage Y)
    have := hf
    refine ⟨(HomotopyCategory.quotient D _).obj I, hI, ⟨?_⟩⟩
    exact (DerivedCategory.quotientCompQhIso D).app I ≪≫
      (asIso (DerivedCategory.Q.map f)).symm ≪≫ DerivedCategory.Q.objObjPreimageIso Y
  · intro I hI X
    have := hI
    exact CochainComplex.IsKInjective.Qh_map_bijective X I.as
  · intro I hI X
    have := hI
    have := CochainComplex.isKInjective_mapHomologicalComplex_of_exact G F adj I.as
    exact CochainComplex.IsKInjective.Qh_map_bijective X
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj I.as)


/-- **Postcomposing with the counit of `F ⊣ G` and precomposing with the unit of `L ⊣ F` are
bijective together.** For two adjunctions `L ⊣ F` and `F ⊣ G` sharing the middle functor, the
two Hom-set maps into `X ⟶ Y` differ by the composite of the two Hom-equivalences. -/
theorem bijective_postcomp_counit_iff_precomp_unit
    {C : Type u₁} {D : Type u₂} [Category.{v₁} C] [Category.{v₂} D]
    {L : C ⥤ D} {F : D ⥤ C} {G : C ⥤ D}
    (adj₁ : L ⊣ F) (adj₂ : F ⊣ G) (X Y : C) :
    Function.Bijective (fun g : X ⟶ F.obj (G.obj Y) => g ≫ adj₂.counit.app Y) ↔
      Function.Bijective (fun g : F.obj (L.obj X) ⟶ Y => adj₁.unit.app X ≫ g) := by
  change Function.Bijective (fun g : X ⟶ F.obj (G.obj Y) => (g ≫ adj₂.counit.app Y : X ⟶ Y)) ↔
    Function.Bijective (fun g : F.obj (L.obj X) ⟶ Y => (adj₁.unit.app X ≫ g : X ⟶ Y))
  let e := (adj₁.homEquiv X (G.obj Y)).symm.trans (adj₂.homEquiv (L.obj X) Y).symm
  have he : (fun g : X ⟶ F.obj (G.obj Y) => adj₁.unit.app X ≫ e g) =
      (fun g => g ≫ adj₂.counit.app Y) := by
    funext g
    dsimp only [e, Equiv.trans_apply]
    rw [adj₂.homEquiv_counit, ← Category.assoc]
    apply congrArg (fun k : X ⟶ F.obj (G.obj Y) => k ≫ adj₂.counit.app Y)
    simpa only [Equiv.apply_symm_apply] using
      (adj₁.homEquiv_unit (f := (adj₁.homEquiv X (G.obj Y)).symm g)).symm
  simpa only [Function.comp_def, he, CategoryTheory.catToReflQuiver, Functor.id_obj,
    Functor.comp_obj] using
    (Function.Bijective.of_comp_iff
      (fun g : F.obj (L.obj X) ⟶ Y => adj₁.unit.app X ≫ g) e.bijective)

private theorem exists_restrictScalars_derivedAdjunction
    (A : Type uA) (B : Type uB) [CommRing A] [CommRing B]
    (f : A →+* B) :
    ∃ (G : DerivedCategory (ModuleCat.{max uA uB v} A) ⥤
      DerivedCategory (ModuleCat.{max uA uB v} B)),
      Nonempty ((ModuleCat.restrictScalars.{max uA uB v} f).mapDerivedCategory ⊣ G) := by
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{max uA uB v} A) :=
    moduleCat_hasExactLimitsOfShape_discrete.{max uA uB v} A ℕ
  let : (ModuleCat.coextendScalars.{uA, uB, max uA uB v} f).Additive :=
    (ModuleCat.restrictCoextendScalarsAdj.{max uA uB v} f).right_adjoint_additive
  obtain ⟨G, adj, hG⟩ := exists_derivedAdjunction
    (ModuleCat.restrictCoextendScalarsAdj.{max uA uB v} f)
    (fun K => by
      obtain ⟨J, i, hi, hJ⟩ := CochainComplex.exists_quasiIso_isKInjective K
      exact ⟨J, i, hi, hJ⟩)
  exact ⟨G, ⟨adj⟩⟩


private lemma homotopyAdjunction_counit_app
    {C D : Type*} [Category C] [Category D] [Abelian C] [Abelian D]
    {F : C ⥤ D} {G : D ⥤ C} [F.Additive] [G.Additive] (adj : F ⊣ G)
    (I : CochainComplex D ℤ) :
    (homotopyAdjunction adj).counit.app ((HomotopyCategory.quotient D _).obj I) =
      (HomotopyCategory.quotient D _).map
        ((adj.mapHomologicalComplex (ComplexShape.up ℤ)).counit.app I) := by
  simp only [homotopyAdjunction, Adjunction.localization_counit_app, Iso.symm_inv,
    Functor.mapHomotopyCategoryFactors, Quotient.lift.isLift_hom]
  dsimp only [Functor.comp_obj]
  erw [CategoryTheory.Functor.map_id, Category.id_comp, Category.id_comp]

private noncomputable def bottomProjection
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (a : ℤ) (ha : IsZero (K.X (a - 1))) :
    K ⟶ (HomologicalComplex.single C (ComplexShape.up ℤ) a).obj (K.X a) :=
  HomologicalComplex.mkHomToSingle (𝟙 (K.X a)) (fun i hi => by
    obtain rfl : i = a - 1 := by have : i + 1 = a := hi; omega
    simpa only [Category.comp_id] using ha.eq_of_src (K.d (a - 1) a) 0)

private lemma bottomProjection_f_self
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (a : ℤ) (ha : IsZero (K.X (a - 1))) :
    (bottomProjection K a ha).f a =
      (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) a (K.X a)).inv := by
  rw [bottomProjection, HomologicalComplex.mkHomToSingle_f, Category.id_comp]

private lemma epi_bottomProjection
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (a : ℤ) (ha : IsZero (K.X (a - 1))) :
    Epi (bottomProjection K a ha) :=
  HomologicalComplex.epi_of_epi_f _ (fun p => by
    by_cases hp : p = a
    · subst hp
      rw [bottomProjection_f_self]
      infer_instance
    · exact ⟨fun _ _ _ => (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a
        (K.X a) p hp).eq_of_src _ _⟩)

private lemma isZero_kernel_bottomProjection_X_self
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (a : ℤ) (ha : IsZero (K.X (a - 1))) :
    IsZero ((kernel (bottomProjection K a ha)).X a) := by
  have h0 : (kernel.ι (bottomProjection K a ha)).f a = 0 := by
    have hiso : IsIso ((bottomProjection K a ha).f a) := by
      rw [bottomProjection_f_self]; infer_instance
    refine zero_of_comp_mono ((bottomProjection K a ha).f a) ?_
    rw [← HomologicalComplex.comp_f, kernel.condition, HomologicalComplex.zero_f]
  refine (IsZero.iff_id_eq_zero _).2 ?_
  rw [← cancel_mono ((kernel.ι (bottomProjection K a ha)).f a), Category.id_comp, zero_comp]
  exact h0

private lemma isIso_kernel_bottomProjection_f
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (a : ℤ) (ha : IsZero (K.X (a - 1)))
    (p : ℤ) (hp : p ≠ a) : IsIso ((kernel.ι (bottomProjection K a ha)).f p) :=
  isIso_of_isLimit_kernelFork_of_isZero _
    (isLimitForkMapOfIsLimit' (HomologicalComplex.eval C (ComplexShape.up ℤ) p)
      (kernel.condition (bottomProjection K a ha)) (kernelIsKernel (bottomProjection K a ha)))
    (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a (K.X a) p hp)

/-- The kernel of `bottomProjection K a ha` vanishes outside the degrees `a + 1, …, b`. -/
private lemma isZero_kernel_bottomProjection_X
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (a b : ℤ) (ha : IsZero (K.X (a - 1)))
    (hK : ∀ p, p < a ∨ b < p → IsZero (K.X p)) (p : ℤ) (hp : p < a + 1 ∨ b < p) :
    IsZero ((kernel (bottomProjection K a ha)).X p) := by
  by_cases hpa : p = a
  · subst p; exact isZero_kernel_bottomProjection_X_self K a ha
  · exact IsZero.of_mono ((kernel.ι (bottomProjection K a ha)).f p) (hK p (by omega))

/-- The kernel of `bottomProjection K a ha` sits in a short exact sequence with `K`. -/
private lemma shortExact_kernel_bottomProjection
    {C : Type*} [Category C] [Abelian C]
    (K : CochainComplex C ℤ) (a : ℤ) (ha : IsZero (K.X (a - 1))) :
    (ShortComplex.mk (kernel.ι (bottomProjection K a ha)) (bottomProjection K a ha)
      (kernel.condition _)).ShortExact :=
  { mono_f := by dsimp; infer_instance
    epi_g := epi_bottomProjection K a ha
    exact := ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _) }

private theorem mem_of_bounded_terms_aux
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (P : ObjectProperty (DerivedCategory C)) [P.ContainsZero]
    [P.IsClosedUnderIsomorphisms] [P.IsTriangulatedClosed₂] (k : ℕ) :
    ∀ (K : CochainComplex C ℤ) (a b : ℤ), (b - a + 1).toNat ≤ k →
      (∀ p, p < a ∨ b < p → IsZero (K.X p)) →
      (∀ p, P (DerivedCategory.Q.obj
        ((HomologicalComplex.single C (ComplexShape.up ℤ) p).obj (K.X p)))) →
      P (DerivedCategory.Q.obj K) := by
  induction k with
  | zero =>
    intro K a b hk hK _
    have hzero : IsZero K := by
      apply (IsZero.iff_id_eq_zero _).mpr
      apply HomologicalComplex.Hom.ext
      funext p
      exact (hK p (by omega)).eq_of_src _ _
    exact P.prop_of_isZero (DerivedCategory.Q.map_isZero hzero)
  | succ k ih =>
    intro K a b hk hK hP
    let ha := hK (a - 1) (Or.inl (by omega))
    let π := bottomProjection K a ha
    let L := kernel π
    have hLa : IsZero (L.X a) := isZero_kernel_bottomProjection_X_self K a ha
    have hL := isZero_kernel_bottomProjection_X K a b ha hK
    have hPL (p : ℤ) : P (DerivedCategory.Q.obj
        ((HomologicalComplex.single C (ComplexShape.up ℤ) p).obj (L.X p))) := by
      by_cases hpa : p = a
      · subst p
        exact P.prop_of_isZero (DerivedCategory.Q.map_isZero
          ((HomologicalComplex.single C (ComplexShape.up ℤ) a).map_isZero hLa))
      · have := isIso_kernel_bottomProjection_f K a ha p hpa
        exact P.prop_of_iso (DerivedCategory.Q.mapIso
          ((HomologicalComplex.single C (ComplexShape.up ℤ) p).mapIso
            (asIso ((kernel.ι π).f p)))).symm (hP p)
    have hS := shortExact_kernel_bottomProjection K a ha
    exact P.ext_of_isTriangulatedClosed₂ (DerivedCategory.triangleOfSES hS)
      (DerivedCategory.triangleOfSES_distinguished hS)
      (ih L (a + 1) b (by omega) hL hPL) (hP a)


private theorem subsingleton_hom_of_bounded_terms
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) (a b : ℤ)
    (hK : ∀ p, p < a ∨ b < p → IsZero (K.X p))
    (E : DerivedCategory C)
    (hE : ∀ p, Subsingleton (DerivedCategory.Q.obj
      ((HomologicalComplex.single C (ComplexShape.up ℤ) p).obj (K.X p)) ⟶ E)) :
    Subsingleton (DerivedCategory.Q.obj K ⟶ E) := by
  let P : ObjectProperty (DerivedCategory C) := ObjectProperty.leftOrthogonal (fun X => X = E)
  have hP : P (DerivedCategory.Q.obj K) :=
    mem_of_bounded_terms_aux P (b - a + 1).toNat K a b le_rfl hK (fun p X g hX => by
      subst X
      have := hE p
      exact Subsingleton.elim g 0)
  exact ⟨fun f g => (hP f rfl).trans (hP g rfl).symm⟩

private lemma bijective_precomp_of_distinguished
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C] [HasShift C ℤ]
    [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (T : Pretriangulated.Triangle C) (hT : T ∈ Pretriangulated.distinguishedTriangles) (E : C)
    (h₀ : Subsingleton (T.obj₁ ⟶ E)) (h₁ : Subsingleton (T.obj₁⟦(1 : ℤ)⟧ ⟶ E)) :
    Function.Bijective (fun g : T.obj₃ ⟶ E => T.mor₂ ≫ g) := by
  constructor
  · intro f g hfg
    dsimp only at hfg
    have hz : T.mor₂ ≫ (f - g) = 0 := by rw [Preadditive.comp_sub, hfg, sub_self]
    obtain ⟨z, hz⟩ := T.rotate.yoneda_exact₂ (Pretriangulated.rot_of_distTriang T hT)
      (f - g) hz
    rw [h₁.elim z 0, comp_zero] at hz
    exact sub_eq_zero.mp hz
  · intro f
    obtain ⟨g, hg⟩ := T.yoneda_exact₂ hT f (h₀.elim _ _)
    exact ⟨g, hg.symm⟩

private theorem bijective_precomp_bottomProjection
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (K : CochainComplex C ℤ) (a b : ℤ)
    (hK : ∀ p, p < a ∨ b < p → IsZero (K.X p))
    (E : DerivedCategory C)
    (hE : ∀ p, p ≠ a → ∀ n : ℤ, Subsingleton (DerivedCategory.Q.obj
      ((HomologicalComplex.single C (ComplexShape.up ℤ) p).obj (K.X p)) ⟶ E⟦n⟧)) :
    let ha := hK (a - 1) (Or.inl (by omega))
    Function.Bijective (fun g : DerivedCategory.Q.obj
        ((HomologicalComplex.single C (ComplexShape.up ℤ) a).obj (K.X a)) ⟶ E =>
      DerivedCategory.Q.map (bottomProjection K a ha) ≫ g) := by
  dsimp only
  let ha := hK (a - 1) (Or.inl (by omega))
  let π := bottomProjection K a ha
  let L := kernel π
  have hLa : IsZero (L.X a) := isZero_kernel_bottomProjection_X_self K a ha
  have hL := isZero_kernel_bottomProjection_X K a b ha hK
  have hLE (n : ℤ) : Subsingleton (DerivedCategory.Q.obj L ⟶ E⟦n⟧) := by
    apply subsingleton_hom_of_bounded_terms L (a + 1) b hL (E⟦n⟧)
    intro p
    by_cases hpa : p = a
    · subst p
      exact ⟨fun f g => (DerivedCategory.Q.map_isZero
        ((HomologicalComplex.single C (ComplexShape.up ℤ) a).map_isZero hLa)).eq_of_src f g⟩
    · have := isIso_kernel_bottomProjection_f K a ha p hpa
      have := hE p hpa n
      exact (Iso.homCongr (DerivedCategory.Q.mapIso
        ((HomologicalComplex.single C (ComplexShape.up ℤ) p).mapIso
          (asIso ((kernel.ι π).f p)))) (Iso.refl _)).injective.subsingleton
  have hS := shortExact_kernel_bottomProjection K a ha
  apply bijective_precomp_of_distinguished (DerivedCategory.triangleOfSES hS)
    (DerivedCategory.triangleOfSES_distinguished hS) E
  · change Subsingleton (DerivedCategory.Q.obj L ⟶ E)
    have := hLE 0
    exact (Iso.homCongr (Iso.refl _) ((shiftFunctorZero (DerivedCategory C) ℤ).app
      E).symm).injective.subsingleton
  · change Subsingleton ((DerivedCategory.Q.obj L)⟦(1 : ℤ)⟧ ⟶ E)
    let e : ((DerivedCategory.Q.obj L)⟦(1 : ℤ)⟧ ⟶ E) ≃
        (DerivedCategory.Q.obj L ⟶ E⟦(-1 : ℤ)⟧) :=
      (shiftEquiv (DerivedCategory C) (1 : ℤ)).toAdjunction.homEquiv
        (DerivedCategory.Q.obj L) E
    have := hLE (-1)
    exact e.injective.subsingleton


open scoped DirectSum

private lemma subsingleton_hom_map_directSum
    {R : Type u} [CommRing R] {ι : Type v} [Finite ι]
    (M : ι → Type (max v w)) [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)]
    {D : Type*} [Category D] [Preadditive D]
    (F : ModuleCat.{max v w} R ⥤ D) [F.Additive] (E : D)
    (hM : ∀ i, Subsingleton (F.obj (ModuleCat.of R (M i)) ⟶ E)) :
    Subsingleton (F.obj (ModuleCat.of R (⨁ i, M i)) ⟶ E) := by
  classical
  cases nonempty_fintype ι
  let N := fun i => M i
  let inc (i : ι) : ModuleCat.of R (N i) ⟶ ModuleCat.of R (⨁ i, N i) :=
    ModuleCat.ofHom (DirectSum.lof R ι N i)
  let pr (i : ι) : ModuleCat.of R (⨁ i, N i) ⟶ ModuleCat.of R (N i) :=
    ModuleCat.ofHom (DirectSum.component R ι N i)
  have hid : (𝟙 (ModuleCat.of R (⨁ i, N i))) = ∑ i, pr i ≫ inc i := by
    apply ModuleCat.hom_ext
    apply DirectSum.linearMap_ext
    intro i
    ext m
    simp only [ModuleCat.hom_id, ModuleCat.hom_sum, ModuleCat.hom_comp,
      ModuleCat.hom_ofHom, LinearMap.id_comp, LinearMap.sum_apply,
      LinearMap.comp_apply, pr, inc]
    symm
    rw [Finset.sum_eq_single i]
    · simp [N, DirectSum.component.lof_self]
    · intro j hj hji
      simp [N, DirectSum.component.of, Ne.symm hji]
    · simp
  constructor
  intro f g
  have hz (f : F.obj (ModuleCat.of R (⨁ i, N i)) ⟶ E) : f = 0 := by
    calc
      f = F.map (𝟙 _) ≫ f := by simp
      _ = F.map (∑ i, pr i ≫ inc i) ≫ f := by rw [hid]
      _ = ∑ i, F.map (pr i) ≫ (F.map (inc i) ≫ f) := by
        simp only [Functor.map_sum, Preadditive.sum_comp, Functor.map_comp, Category.assoc]
      _ = 0 := by
        apply Finset.sum_eq_zero
        intro i hi
        have := hM i
        rw [Subsingleton.elim (F.map (inc i) ≫ f) 0, comp_zero]
  exact (hz f).trans (hz g).symm

open scoped DirectSum

private lemma eq_zero_of_isIso_smul_of_isDerivedComplete
    {A : Type u} [CommRing A] (I : Ideal A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    {K : DerivedCategory (ModuleCat.{v} A)} (hK : IsDerivedComplete I K)
    {f : A} (hf : f ∈ I) {X : DerivedCategory (ModuleCat.{v} A)}
    (hu : IsIso (f • 𝟙 X)) (h : X ⟶ K) : h = 0 := by
  obtain ⟨L, ⟨p, δ, hT⟩, hL⟩ :=
    (isDerivedCompleteAt_iff_exists_isDerivedLimit_isZero K f).mp (hK f hf)
  have hiso := (Pretriangulated.Triangle.isZero₁_iff_isIso₂ _ hT).mp hL
  set d := (Pretriangulated.Triangle.mk p _ δ).mor₂ with hd
  have hmono : Mono d := by
    have := hiso; infer_instance
  let u := inv (f • 𝟙 X)
  let x : X ⟶ ∏ᶜ fun _ : ℕ => K :=
    Pi.lift fun n => (End.of u ^ n).asHom ≫ h
  have hx : x ≫ d = 0 := by
    apply Pi.hom_ext
    intro n
    simp only [hd, Pretriangulated.Triangle.mk_mor₂, x, Category.assoc, limit.lift_π,
      Fan.mk_π_app, Preadditive.comp_sub, zero_comp, Functor.ofOpSequence_map_homOfLE_succ]
    erw [limit.lift_π, limit.lift_π_assoc]
    dsimp
    have hc : (f • 𝟙 X) ≫ h = h ≫ (f • 𝟙 K) := by simp
    rw [pow_succ', End.mul_asHom]
    dsimp only
    rw [Category.assoc, Category.assoc, ← hc, ← Category.assoc u]
    simp only [u, IsIso.inv_hom_id, Category.id_comp]
    exact sub_self _
  have h0 : x = 0 := zero_of_comp_mono d hx
  have := congrArg (· ≫ Pi.π (fun _ : ℕ => K) 0) h0
  simpa [x] using this

private lemma subsingleton_hom_shift_of_isIso_smul
    {A : Type u} [CommRing A] (I : Ideal A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    {K : DerivedCategory (ModuleCat.{v} A)} (hK : IsDerivedComplete I K)
    {f : A} (hf : f ∈ I) {X : DerivedCategory (ModuleCat.{v} A)}
    (hu : IsIso (f • 𝟙 X)) (n : ℤ) : Subsingleton (X ⟶ K⟦n⟧) := by
  have hu' : IsIso (f • 𝟙 (X⟦-n⟧)) := by
    rw [← (shiftFunctor (DerivedCategory (ModuleCat.{v} A)) (-n)).map_id X,
      ← Functor.map_smul]
    infer_instance
  have hzero (h : X ⟶ K⟦n⟧) : h = 0 := by
    have h0 := eq_zero_of_isIso_smul_of_isDerivedComplete I hK hf hu'
      (h⟦-n⟧' ≫ (shiftFunctorCompIsoId _ n (-n) (add_neg_cancel n)).hom.app K)
    apply (shiftFunctor _ (-n)).map_injective
    rw [Functor.map_zero]
    simpa using h0
  exact ⟨fun g h => (hzero g).trans (hzero h).symm⟩

private lemma subsingleton_hom_single_of_isUnit_smul
    (A : Type u) [CommRing A] (I : Ideal A)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{v} A))]
    (K : DerivedCategory (ModuleCat.{v} A)) (hK : IsDerivedComplete I K)
    (f : A) (hf : f ∈ I) (M : Type v) [AddCommGroup M] [Module A M]
    (hu : IsUnit (algebraMap A (Module.End A M) f)) (p n : ℤ) :
    Subsingleton (DerivedCategory.Q.obj
      ((HomologicalComplex.single (ModuleCat.{v} A) (ComplexShape.up ℤ) p).obj
        (ModuleCat.of A M)) ⟶ K⟦n⟧) := by
  apply subsingleton_hom_shift_of_isIso_smul I hK hf _ n
  let S := HomologicalComplex.single (ModuleCat.{v} A) (ComplexShape.up ℤ) p
  have hM : IsIso (f • 𝟙 (ModuleCat.of A M)) := by
    obtain ⟨w, hw⟩ := hu
    refine ⟨ModuleCat.ofHom w⁻¹.1, ?_, ?_⟩
    · ext m
      change w⁻¹.1 (f • m) = m
      have := congrArg (fun g : Module.End A M => g m) w.inv_mul
      simp only [hw, Module.End.mul_apply, Module.End.one_apply] at this
      simpa [Module.algebraMap_end_apply] using this
    · ext m
      change f • w⁻¹.1 m = m
      have := congrArg (fun g : Module.End A M => g m) w.mul_inv
      simp only [hw, Module.End.mul_apply, Module.End.one_apply] at this
      simpa [Module.algebraMap_end_apply] using this
  have heq : f • 𝟙 (DerivedCategory.Q.obj (S.obj (ModuleCat.of A M))) =
      DerivedCategory.Q.map (S.map (f • 𝟙 (ModuleCat.of A M))) := by
    rw [← DerivedCategory.Q.map_id, ← Functor.map_smul]
    congr 1
    apply HomologicalComplex.Hom.ext
    funext q
    by_cases hq : q = p
    · subst hq
      simp [S]
    · exact (HomologicalComplex.isZero_single_obj_X _ p _ q hq).eq_of_src _ _
  rw [heq]
  infer_instance

private lemma bottomProjection_naturality
    {C : Type*} [Category C] [Abelian C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) (a : ℤ)
    (hK : IsZero (K.X (a - 1))) (hL : IsZero (L.X (a - 1))) :
    f ≫ bottomProjection L a hL = bottomProjection K a hK ≫
      (HomologicalComplex.single C (ComplexShape.up ℤ) a).map (f.f a) := by
  apply HomologicalComplex.Hom.ext
  funext p
  by_cases hp : p = a
  · subst p
    simp only [HomologicalComplex.comp_f, bottomProjection_f_self,
      HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc]
  · exact (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) a
      (L.X a) p hp).eq_of_tgt _ _

private theorem bijective_precomp_single_map_of_quasiIso
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    {K L : CochainComplex C ℤ} (f : K ⟶ L) [QuasiIso f] (a b : ℤ)
    (hK : ∀ p, p < a ∨ b < p → IsZero (K.X p))
    (hL : ∀ p, p < a ∨ b < p → IsZero (L.X p)) (E : DerivedCategory C)
    (hEK : ∀ p, p ≠ a → ∀ n : ℤ, Subsingleton (DerivedCategory.Q.obj
      ((HomologicalComplex.single C (ComplexShape.up ℤ) p).obj (K.X p)) ⟶ E⟦n⟧))
    (hEL : ∀ p, p ≠ a → ∀ n : ℤ, Subsingleton (DerivedCategory.Q.obj
      ((HomologicalComplex.single C (ComplexShape.up ℤ) p).obj (L.X p)) ⟶ E⟦n⟧)) :
    Function.Bijective (fun g : DerivedCategory.Q.obj
        ((HomologicalComplex.single C (ComplexShape.up ℤ) a).obj (L.X a)) ⟶ E =>
      DerivedCategory.Q.map ((HomologicalComplex.single C (ComplexShape.up ℤ) a).map (f.f a)) ≫ g)
        := by
  let hKa := hK (a - 1) (Or.inl (by omega))
  let hLa := hL (a - 1) (Or.inl (by omega))
  let πK := bottomProjection K a hKa
  let πL := bottomProjection L a hLa
  have hk := bijective_precomp_bottomProjection K a b hK E hEK
  have hl := bijective_precomp_bottomProjection L a b hL E hEL
  have hc : Function.Bijective (fun g : DerivedCategory.Q.obj L ⟶ E =>
      DerivedCategory.Q.map f ≫ g) := by
    constructor
    · intro g h heq
      exact (cancel_epi (DerivedCategory.Q.map f)).mp heq
    · intro g
      exact ⟨inv (DerivedCategory.Q.map f) ≫ g, by simp⟩
  dsimp only at hk hl
  have hcomp := hc.comp hl
  have heq : (fun g : DerivedCategory.Q.obj
      ((HomologicalComplex.single C (ComplexShape.up ℤ) a).obj (L.X a)) ⟶ E => DerivedCategory.Q.map
        f ≫ (DerivedCategory.Q.map πL ≫ g)) =
      (fun g => DerivedCategory.Q.map πK ≫
        (DerivedCategory.Q.map ((HomologicalComplex.single C (ComplexShape.up ℤ) a).map (f.f a)) ≫
          g)) := by
    funext g
    rw [← Category.assoc, ← Category.assoc, ← DerivedCategory.Q.map_comp,
      ← DerivedCategory.Q.map_comp, bottomProjection_naturality]
  dsimp only [Function.comp_def] at hcomp
  rw [heq] at hcomp
  exact (Function.Bijective.of_comp_iff' hk _).mp hcomp

end CompleteRestrictScalarsEquivalence

end
