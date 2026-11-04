module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.HigherDerivedFunctors
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.CategoryTheory.Localization.DerivingAdjoints
public import StacksFrontier.Homology.Injectives.GabrielPopescu
public import StacksFrontier.RingTheory.LocalCohomology.ModulesSupportedIn

/-!
# Derived sections with support as a right adjoint

Let `A` be a commutative ring and `T` a subset of its prime spectrum. Degree-zero sections with
support in `T` of an `A`-module are again supported in `T`, so the functor `H⁰_T` corestricts to a
functor `Mod_A ⥤ Mod_{A,T}` into the modules supported in `T`, right adjoint to the inclusion
`Mod_{A,T} ⥤ Mod_A`.

The inclusion is exact, so it induces a functor `D(Mod_{A,T}) ⥤ D(A)`, and the corestricted
section functor has a total right derived functor `RH⁰_T : D(A) ⥤ D(Mod_{A,T})`. These two
functors are adjoint, and composing `RH⁰_T` with the derived inclusion recovers the ambient
derived sections functor.

## Main definitions

* `Stacks.LocalCohomology.supportedSectionsFunctor` — degree-zero sections with support in `T`,
  valued in the modules supported in `T`.
* `Stacks.LocalCohomology.inclusion_adj_supportedSectionsFunctor` — the underived adjunction.
* `Stacks.LocalCohomology.derivedSupportedSections` — the total right derived functor
  `RH⁰_T : D(A) ⥤ D(Mod_{A,T})`.
* `Stacks.LocalCohomology.derivedSupportedSectionsUnit` — the canonical comparison exhibiting it
  as a right derived functor.

## Main results

* `Stacks.LocalCohomology.sectionsWithSupportIn_supported` — `H⁰_T M` is supported in `T`.
* `Stacks.LocalCohomology.derivedInclusion_adj_derivedSupportedSections` — `RH⁰_T` is right
  adjoint to the functor `D(Mod_{A,T}) ⥤ D(A)` induced by the inclusion.
* `Stacks.LocalCohomology.derivedSupportedSections_comp_inclusion_iso` — composing `RH⁰_T` with
  the derived inclusion gives the ambient derived sections functor
  `Stacks.LocalCohomology.derivedSectionsWithSupportIn`.

## References

* [Stacks Project, Tag 0EF0](https://stacks.math.columbia.edu/tag/0EF0)
* [Stacks Project, Tag 09T5](https://stacks.math.columbia.edu/tag/09T5)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

/-- Degree-zero sections with support in `T` are themselves supported in `T`. -/
theorem sectionsWithSupportIn_supported (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) (M : ModuleCat.{max u v} A) :
    (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A))
      ((sectionsWithSupportInFunctor.{u, v} A T).obj M) := by
  rw [supportModuleProperty]
  apply (sectionsWithSupportIn_eq_top_iff A T
    ((sectionsWithSupportInFunctor.{u, v} A T).obj M)).mp
  apply le_antisymm le_top
  intro x _
  rw [mem_sectionsWithSupportIn_iff]
  have hx' := (mem_sectionsWithSupportIn_iff A T M x.val).mp x.property
  show PrimeSpectrum.zeroLocus
    (Ideal.torsionOf A (sectionsWithSupportIn A T (↑M)) x : Set A) ⊆ T
  rw [torsionOf_submodule_eq]
  exact hx'

/-- Degree-zero sections with support in `T`, with their natural codomain: the functor
`H⁰_T : Mod_A ⥤ Mod_{A,T}` obtained by corestricting
`Stacks.LocalCohomology.sectionsWithSupportInFunctor` to the modules supported in `T`. -/
def supportedSectionsFunctor (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :
    ModuleCat.{max u v} A ⥤ ModulesSupportedIn.{u, max u v} A T :=
  (supportModuleProperty A T).lift (sectionsWithSupportInFunctor.{u, v} A T)
    (sectionsWithSupportIn_supported.{u, v} A T)

/-- Sections with support in `T`, valued in supported modules, is an additive functor. -/
instance supportedSectionsFunctor_additive (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    (supportedSectionsFunctor.{u, v} A T).Additive := by
  dsimp [supportedSectionsFunctor]
  infer_instance

/-- **The underived adjunction.** The inclusion of the modules supported in `T` is left adjoint to
degree-zero sections with support in `T`. -/
def inclusion_adj_supportedSectionsFunctor (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)).ι ⊣
      supportedSectionsFunctor.{u, v} A T := by
  let H := sectionsWithSupportInFunctor.{u, v} A T
  refine Adjunction.mkOfHomEquiv
    { homEquiv X M :=
        { toFun := fun f => by
            refine ⟨ModuleCat.ofHom (f.hom.codRestrict
              (sectionsWithSupportIn A T M) ?_)⟩
            intro x
            have hx : x ∈ sectionsWithSupportIn A T X.obj := by
              have htop := (sectionsWithSupportIn_eq_top_iff A T X.obj).2 X.property
              rw [htop]
              exact Submodule.mem_top
            exact ((H.map f).hom ⟨x, hx⟩).property
          invFun := fun g =>
            ModuleCat.ofHom ((sectionsWithSupportIn A T M).subtype.comp g.hom.hom)
          left_inv := by intro f; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl
          right_inv := by
            intro g; apply ObjectProperty.hom_ext; apply ModuleCat.hom_ext
            apply LinearMap.ext; intro x; rfl }
      homEquiv_naturality_left_symm := by
        intro X X' f M g; apply ModuleCat.hom_ext; apply LinearMap.ext; intro x; rfl
      homEquiv_naturality_right := by
        intro X M N f g; apply ObjectProperty.hom_ext; apply ModuleCat.hom_ext
        apply LinearMap.ext; intro x; rfl }

/-- Pointwise existence of the unbounded right derived functor of supported sections. -/
instance hasPointwiseRightDerivedSupportedSections (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    HasPointwiseRightDerivedFunctor
      ((supportedSectionsFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh)
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) := by
  let : EnoughInjectives (ModuleCat.{max u v} A) := ModuleCat.enoughInjectives A
  let F := supportedSectionsFunctor.{u, v} A T
  exact (hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
        max u v, max (u + 1) (v + 1), max (u + 1) (v + 1),
        max (u + 1) (v + 1), max (u + 1) (v + 1), max (u + 1) (v + 1)}
      (F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
      (fun K ↦ by
        obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective K
        exact ⟨I, q, hI, hq⟩)).1

/-- The total right derived functor `RH⁰_T : D(A) ⥤ D(Mod_{A,T})` of degree-zero sections with
support in `T`, valued in the derived category of the modules supported in `T`. -/
def derivedSupportedSections (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :
    DerivedCategory (ModuleCat.{max u v} A) ⥤
      DerivedCategory (ModulesSupportedIn.{u, max u v} A T) :=
  totalRightDerived
    ((supportedSectionsFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh) DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))

/-- The canonical comparison from supported sections of a complex to the value of
`Stacks.LocalCohomology.derivedSupportedSections` on it. -/
abbrev derivedSupportedSectionsUnit (A : Type u) [CommRing A] (T : Set (PrimeSpectrum A)) :
    (supportedSectionsFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ derivedSupportedSections.{u, v} A T :=
  ((supportedSectionsFunctor.{u, v} A T).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
    DerivedCategory.Qh).totalRightDerivedUnit DerivedCategory.Qh
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ))

/-- The comparison exhibits `Stacks.LocalCohomology.derivedSupportedSections` as the right derived
functor of supported sections. -/
instance derivedSupportedSections_isRightDerivedFunctor (A : Type u) [CommRing A]
    (T : Set (PrimeSpectrum A)) :
    (derivedSupportedSections.{u, v} A T).IsRightDerivedFunctor
      (derivedSupportedSectionsUnit.{u, v} A T)
      (HomotopyCategory.quasiIso (ModuleCat.{max u v} A) (ComplexShape.up ℤ)) := by
  dsimp only [derivedSupportedSections, derivedSupportedSectionsUnit]
  infer_instance

/-- Let `A` be a Noetherian ring and `T ⊆ Spec A` be stable under specialization. Then
`RH⁰_T : D(A) ⥤ D(Mod_{A,T})` is right adjoint to the functor `D(Mod_{A,T}) ⥤ D(A)` induced by
the inclusion. -/
@[stacks 0EF0 "adjunction"]
theorem derivedInclusion_adj_derivedSupportedSections (A : Type u) [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (_hT : StableUnderSpecialization T) :
    Nonempty
      ((supportModuleProperty A T :
          ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory ⊣
        derivedSupportedSections.{u, v} A T) := by
  let AMod := ModuleCat.{max u v} A
  let BMod := ModulesSupportedIn.{u, max u v} A T
  let F₀ := supportedSectionsFunctor.{u, v} A T
  let G₀ := (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)).ι
  let W := HomotopyCategory.quasiIso AMod (ComplexShape.up ℤ)
  let W' := HomotopyCategory.quasiIso BMod (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := AMod)
  let Q' := DerivedCategory.Qh (C := BMod)
  let F := F₀.mapHomotopyCategory (ComplexShape.up ℤ)
  let G := G₀.mapHomotopyCategory (ComplexShape.up ℤ)
  let LG := G₀.mapDerivedCategory
  let α := G₀.mapDerivedCategoryFactorsh.hom
  let : EnoughInjectives AMod := ModuleCat.enoughInjectives A
  let hPoint := hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      max u v, max (u + 1) (v + 1), max (u + 1) (v + 1),
      max (u + 1) (v + 1), max (u + 1) (v + 1), max (u + 1) (v + 1)}
    (F ⋙ Q') (fun K ↦ by
      obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective K
      exact ⟨I, q, hI, hq⟩)
  let RF := derivedSupportedSections.{u, v} A T
  let β := derivedSupportedSectionsUnit.{u, v} A T
  have hBase : RF.IsRightDerivedFunctor β W :=
    derivedSupportedSections_isRightDerivedFunctor.{u, v} A T
  have hInv : W'.IsInvertedBy (G ⋙ Q) :=
    Stacks.DerivedFunctor.HigherDerivedOfExact.mapHomotopyCategory_inverts_quasiIso G₀
  have hRF : ∀ K : HomotopyCategory AMod (ComplexShape.up ℤ),
      ∃ (c : Limits.Cocone (MorphismProperty.Under.forget W ⊤ K ⋙
        Under.forget K ⋙ F ⋙ Q')),
        ∃ (_ : (F ⋙ Q').IsRightDerivedValueAt W K c),
        ∃ (e : c.pt ≅ RF.obj (Q.obj K)),
          ∀ s : W.Under ⊤ K,
            c.ι.app s ≫ e.hom ≫ RF.map (Q.map s.hom) = β.app s.right := by
    intro K
    obtain ⟨Kc, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
    let K := (HomotopyCategory.quotient AMod (ComplexShape.up ℤ)).obj Kc
    obtain ⟨I, q, hq, hI⟩ := CochainComplex.exists_quasiIso_isKInjective Kc
    let qh := (HomotopyCategory.quotient AMod (ComplexShape.up ℤ)).map q
    have hqh : W qh := (HomotopyCategory.quotient_map_mem_quasiIso_iff q).2 hq
    let t₀ : W.Under ⊤ K := MorphismProperty.Under.mk ⊤ qh hqh
    let ht := Stacks.Injectives.isTerminalUnderKInjective I qh hqh
    let c := Limits.coconeOfDiagramTerminal ht
      (MorphismProperty.Under.forget W ⊤ K ⋙ Under.forget K ⋙ F ⋙ Q')
    have hc := Stacks.Injectives.coconeOfTerminalUnder_isRightDerivedValueAt
      (F ⋙ Q') W K t₀ ht
    have hβ : IsIso (β.app ((HomotopyCategory.quotient AMod _).obj I)) :=
      hPoint.2 Q RF β I hI
    let eβ : _ ≅ _ := by
      have : IsIso (β.app t₀.right) := by simpa [t₀] using hβ
      exact asIso (β.app t₀.right)
    let : IsIso (Q.map t₀.hom) := (Localization.inverts Q W) t₀.hom t₀.prop
    let eRF : _ ≅ _ := asIso (RF.map (Q.map t₀.hom))
    let e : c.pt ≅ RF.obj (Q.obj K) := eβ ≪≫ eRF.symm
    refine ⟨c, hc, e, fun s ↦ ?_⟩
    have hcomp : s.hom ≫ (ht.from s).right = t₀.hom :=
      MorphismProperty.Under.w (ht.from s)
    have hnat : (F ⋙ Q').map ((ht.from s).right) ≫ β.app t₀.right =
        β.app s.right ≫ RF.map (Q.map ((ht.from s).right)) :=
      β.naturality ((ht.from s).right)
    let : IsIso (Q.map s.hom) := (Localization.inverts Q W) s.hom s.prop
    have hcancel : RF.map (Q.map ((ht.from s).right)) ≫ eRF.inv ≫
        RF.map (Q.map s.hom) = 𝟙 _ := by
      rw [← cancel_epi (RF.map (Q.map s.hom)), ← Category.assoc, ← Functor.map_comp,
        ← Functor.map_comp, hcomp]
      exact (eRF.hom_inv_id_assoc _).trans (Category.comp_id _).symm
    show (F ⋙ Q').map ((ht.from s).right) ≫ (β.app t₀.right ≫ eRF.inv) ≫
      RF.map (Q.map s.hom) = β.app s.right
    rw [← Category.assoc, ← Category.assoc, hnat, Category.assoc, Category.assoc, hcancel]
    exact Category.comp_id _
  have hLG : ∀ M : HomotopyCategory BMod (ComplexShape.up ℤ),
      ∃ (d : Limits.Cone (MorphismProperty.Over.forget W' ⊤ M ⋙
        Over.forget M ⋙ G ⋙ Q)),
        ∃ (_ : (G ⋙ Q).IsLeftDerivedValueAt W' M d),
        ∃ (e : LG.obj (Q'.obj M) ≅ d.pt),
          ∀ t : W'.Over ⊤ M,
            LG.map (Q'.map t.hom) ≫ e.hom ≫ d.π.app t = α.app t.left := by
    intro M
    let d := Stacks.Injectives.coneOfInvertedMorphisms (G ⋙ Q) W' hInv M
    have hd := Stacks.Injectives.coneOfInvertedMorphisms_isLeftDerivedValueAt
      (G ⋙ Q) W' hInv M
    let e : LG.obj (Q'.obj M) ≅ d.pt := G₀.mapDerivedCategoryFactorsh.app M
    refine ⟨d, hd, e, ?_⟩
    intro t
    let : IsIso ((G ⋙ Q).map t.hom) := hInv t.hom t.prop
    have hn : LG.map (Q'.map t.hom) ≫ α.app M =
        α.app t.left ≫ (G ⋙ Q).map t.hom := by
      simpa [LG, Q', α, G, Q, Functor.comp_map] using
        G₀.mapDerivedCategoryFactorsh.hom.naturality t.hom
    show LG.map (Q'.map t.hom) ≫ α.app M ≫ inv ((G ⋙ Q).map t.hom) = α.app t.left
    rw [← Category.assoc, hn, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
  show Nonempty (LG ⊣ RF)
  obtain ⟨adjDerived, _, _⟩ :=
    CategoryTheory.Adjunction.exists_derived_of_isRightDerivedValueAt_of_isLeftDerivedValueAt
      (CategoryTheory.Adjunction.mapHomotopyCategoryAdjunction
        (inclusion_adj_supportedSectionsFunctor.{u, v} A T) (ComplexShape.up ℤ))
      W W' Q Q' RF β LG α hRF hLG
  exact ⟨adjDerived⟩

/-- Let `A` be a Noetherian ring and `T ⊆ Spec A` be stable under specialization. Composing
`RH⁰_T : D(A) ⥤ D(Mod_{A,T})` with the derived inclusion recovers the derived sections with
support in `T` taken in `D(A)`. -/
@[stacks 0EF0 "comparison with ambient derived sections"]
theorem derivedSupportedSections_comp_inclusion_iso (A : Type u) [CommRing A]
    [IsNoetherianRing A] (T : Set (PrimeSpectrum A)) (hT : StableUnderSpecialization T) :
    Nonempty
      (derivedSupportedSections.{u, v} A T ⋙
        (supportModuleProperty A T :
            ObjectProperty (ModuleCat.{max u v} A)).ι.mapDerivedCategory ≅
          derivedSectionsWithSupportIn.{u, v} A T) := by
  let AMod := ModuleCat.{max u v} A
  let BMod := ModulesSupportedIn.{u, max u v} A T
  let F₀ := supportedSectionsFunctor.{u, v} A T
  let G₀ := (supportModuleProperty A T : ObjectProperty (ModuleCat.{max u v} A)).ι
  let H := sectionsWithSupportInFunctor.{u, v} A T
  let W := HomotopyCategory.quasiIso AMod (ComplexShape.up ℤ)
  let Q := DerivedCategory.Qh (C := AMod)
  let Q' := DerivedCategory.Qh (C := BMod)
  let c := ComplexShape.up ℤ
  let F := F₀.mapHomotopyCategory c
  let LG := G₀.mapDerivedCategory
  let RF := derivedSupportedSections.{u, v} A T
  let : EnoughInjectives AMod := ModuleCat.enoughInjectives A
  let β : F ⋙ Q' ⟶ Q ⋙ RF := derivedSupportedSectionsUnit.{u, v} A T
  have : RF.IsRightDerivedFunctor β W :=
    derivedSupportedSections_isRightDerivedFunctor.{u, v} A T
  have hLeft : LG.IsLeftAdjoint :=
    (derivedInclusion_adj_derivedSupportedSections.{u, v} A T hT).some.isLeftAdjoint
  let βc := Functor.whiskerRight β LG ≫ (Functor.associator Q RF LG).hom
  have hComp : (RF ⋙ LG).IsRightDerivedFunctor βc W := by
    dsimp only [βc]
    infer_instance
  let e₀ : F₀ ⋙ G₀ ≅ H :=
    (supportModuleProperty A T).liftCompιIso H (sectionsWithSupportIn_supported.{u, v} A T)
  let e₁ : F ⋙ G₀.mapHomotopyCategory c ≅ H.mapHomotopyCategory c :=
    Functor.mapHomotopyCategoryCompIso e₀ c
  let τ : (F ⋙ Q') ⋙ LG ≅ H.mapHomotopyCategory c ⋙ Q :=
    ((Functor.associator F Q' LG).trans
      (Functor.isoWhiskerLeft F G₀.mapDerivedCategoryFactorsh)) ≪≫
    ((Functor.associator F (G₀.mapHomotopyCategory c) Q).symm.trans
      (Functor.isoWhiskerRight e₁ Q))
  let RA := derivedSectionsWithSupportIn.{u, v} A T
  let βA : H.mapHomotopyCategory c ⋙ Q ⟶ Q ⋙ RA := derivedSectionsWithSupportInUnit.{u, v} A T
  have : RA.IsRightDerivedFunctor βA W :=
    derivedSectionsWithSupportIn_isRightDerivedFunctor.{u, v} A T
  exact ⟨Functor.rightDerivedNatIso (RF ⋙ LG) RA βc βA W τ⟩

end Stacks.LocalCohomology

end
