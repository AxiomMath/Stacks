module

public import StacksFrontier.RingTheory.F6Sweep.LocalCohomologySupportSurjectivity
import all StacksFrontier.RingTheory.F6Sweep.LocalCohomologySupportSurjectivity

/-!
# Changing the support of local cohomology: injectivity and the isomorphism criterion

Let `I ≤ J` be finitely generated ideals of a Noetherian ring `A`, let `M` be an `A`-module, and
let `Ψ : Hⁱ_{V(J)}(M) ⟶ Hⁱ_{V(I)}(M)` be the degree-`i` cohomology of the canonical comparison
`Stacks.Algebraization.localCohomologyComparison`. This file proves that `Ψ` is injective as soon
as the local cohomology of `M_𝔭` with support in the maximal ideal of `A_𝔭` vanishes in degree
`i - 1` for every prime `𝔭 ∈ V(I) \ V(J)`, and deduces that `Ψ` is an isomorphism when both that
vanishing and its degree-`i` analogue hold.

## Main results

* `Stacks.LocalCohomology.localCohomologyModuleMapOfLE_injective`: `Ψ` is injective when the
  local cohomology of `M_𝔭` vanishes in degree `i - 1` for every `𝔭 ∈ V(I) \ V(J)`.
* `Stacks.LocalCohomology.isIso_localCohomologyModuleMapOfLE`: `Ψ` is an isomorphism when that
  local cohomology vanishes in degrees `i` and `i - 1` for every `𝔭 ∈ V(I) \ V(J)`.

## References

* [Stacks Project, Tag 0DWV](https://stacks.math.columbia.edu/tag/0DWV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open Dualizing.Coreflection

attribute [local instance] HasDerivedCategory.standard

universe u v

namespace Stacks.LocalCohomology

namespace SupportInjectivity

open SupportSurjectivity

attribute [local instance] smallLocalizationUnit_isLocalizedModule
  smallLocalizationFunctor_additive smallLocalizationFunctor_preservesFiniteLimits
  smallLocalizationFunctor_preservesFiniteColimits powers_small

/-- The derived localization unit for `F` is invertible on objects in the image of a second
localization functor `G` whenever its components there are. -/
private lemma derivedUnit_obj_isIso_of_comp
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (F G : C ⥤ C) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (η : 𝟭 C ⟶ F) (hη : ∀ X, IsIso (η.app (G.obj X))) (X : DerivedCategory C) :
    IsIso ((derivedUnit F η).app (G.mapDerivedCategory.obj X)) := by
  let K := DerivedCategory.Q.objPreimage X
  let e := DerivedCategory.Q.objObjPreimageIso X
  suffices h : IsIso ((derivedUnit F η).app
      (DerivedCategory.Q.obj ((G.mapHomologicalComplex (.up ℤ)).obj K))) by
    exact Dualizing.Coreflection.isIso_app_of_iso (derivedUnit F η)
      ((G.mapDerivedCategory.mapIso e).symm ≪≫ G.mapDerivedCategoryFactors.app K) h
  rw [derivedUnit_app_Q]
  have : IsIso ((complexUnit F η).app ((G.mapHomologicalComplex (.up ℤ)).obj K)) := by
    have : ∀ i, IsIso (((complexUnit F η).app
      ((G.mapHomologicalComplex (.up ℤ)).obj K)).f i) := fun i => hη (K.X i)
    exact HomologicalComplex.Hom.isIso_of_components _
  infer_instance

/-- Maps out of an object annihilated by a localization functor into the fibre of the
localization unit are detected by composing with the inclusion of that fibre. -/
private theorem localizationFiber_precomp_bijective
    {C : Type*} [Category C] [Preadditive C] [HasZeroObject C]
    [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]
    (F : C ⥤ C) [F.Additive] [F.CommShift ℤ] [F.IsTriangulated]
    (η : 𝟭 C ⟶ F) (hη : ∀ X, IsIso (η.app (F.obj X)))
    (X : C) (Z : C) (g : F.obj X ⟶ Z) (h : Z ⟶ X⟦1⟧)
    (hT : Triangle.mk (η.app X) g h ∈ distTriang C)
    (W : C) (hW : IsZero (F.obj W)) :
    Function.Bijective (fun k : W ⟶ (Triangle.mk (η.app X) g h).invRotate.obj₁ =>
      k ≫ (Triangle.mk (η.app X) g h).invRotate.mor₁) := by
  let T := (Triangle.mk (η.app X) g h).invRotate
  have hT' : T ∈ distTriang C := inv_rot_of_distTriang _ hT
  have hz : ∀ k : W ⟶ T.obj₃, k = 0 :=
    Dualizing.Coreflection.hom_eq_zero_of_localization F η hη hW
  have hz' : ∀ k : W ⟶ T.obj₃⟦(-1 : ℤ)⟧, k = 0 := fun k =>
    (cancel_mono ((F.commShiftIso (-1)).app X).inv).1
      ((Dualizing.Coreflection.hom_eq_zero_of_localization F η hη hW _).trans zero_comp.symm)
  exact fiber_hom_bijective T hT' W hz hz'

/-- Both `f` and `s` act invertibly on a module localized at the powers of `f * s`. -/
private lemma smallLocalization_mul_map_unit {A : Type u} [CommRing A]
    (f s : A) (M : ModuleCat.{v} A) :
    IsUnit (algebraMap A (Module.End A (smallLocalization (Submonoid.powers (f * s)) M)) f) ∧
    IsUnit (algebraMap A (Module.End A (smallLocalization (Submonoid.powers (f * s)) M)) s) := by
  let ρ := algebraMap A (Module.End A (smallLocalization (Submonoid.powers (f * s)) M))
  apply ((Commute.all f s).map ρ).isUnit_mul_iff.mp
  rw [← map_mul]
  exact IsLocalizedModule.map_units (smallLocalizationUnit (Submonoid.powers (f * s)) M)
    ⟨f * s, Submonoid.mem_powers (f * s)⟩

/-- The localization at the powers of `f` maps to the localization at the powers of `f * s`,
compatibly with the two localization units. -/
private lemma principalLocalization_comparison_exists {A : Type u} [CommRing A]
    (f s : A) (X : DerivedCategory (ModuleCat.{v} A)) :
    ∃ c : (smallLocalizationFunctor (Submonoid.powers f)).mapDerivedCategory.obj X ⟶
        (smallLocalizationFunctor (Submonoid.powers (f * s))).mapDerivedCategory.obj X,
      (derivedUnit _ (smallLocalizationNatTrans (Submonoid.powers f))).app X ≫ c =
        (derivedUnit _ (smallLocalizationNatTrans (Submonoid.powers (f * s)))).app X := by
  let F := smallLocalizationFunctor (Submonoid.powers f)
  let G := smallLocalizationFunctor (Submonoid.powers (f * s))
  let η := derivedUnit F (smallLocalizationNatTrans (Submonoid.powers f))
  let θ := derivedUnit G (smallLocalizationNatTrans (Submonoid.powers (f * s)))
  have hu (N : ModuleCat.{v} A) :
      IsIso ((smallLocalizationNatTrans (Submonoid.powers f)).app (G.obj N)) := by
    apply (ConcreteCategory.isIso_iff_bijective _).2
    apply smallLocalizationUnit_bijective
    rintro ⟨t, ht⟩
    obtain ⟨n, rfl⟩ := (Submonoid.mem_powers_iff _ _).mp ht
    rw [map_pow]
    exact (smallLocalization_mul_map_unit f s N).1.pow n
  have : IsIso (η.app (G.mapDerivedCategory.obj X)) :=
    derivedUnit_obj_isIso_of_comp F G _ hu X
  refine ⟨F.mapDerivedCategory.map (θ.app X) ≫ inv (η.app _), ?_⟩
  rw [← Category.assoc, ← η.naturality]
  show (θ.app X ≫ η.app (G.mapDerivedCategory.obj X)) ≫
    inv (η.app (G.mapDerivedCategory.obj X)) = θ.app X
  rw [Category.assoc, IsIso.hom_inv_id, Category.comp_id]

/-- The fibre of the localization unit at the powers of `f` on `RΓ_{V(I)}(M)` is
`RΓ_{V(I + (f))}(M)`, compatibly with the canonical comparison of supports. -/
private theorem localCohomology_fiber_iso
    (A : Type u) [CommRing A] (I : Ideal A) (hI : I.FG)
    (M : ModuleCat.{v} A) (f : A)
    (Z : DerivedCategory (ModuleCat.{v} A))
    (g : (smallLocalizationFunctor (Submonoid.powers f)).mapDerivedCategory.obj
      (localCohomologyObject A I hI M) ⟶ Z)
    (h : Z ⟶ (localCohomologyObject A I hI M)⟦(1 : ℤ)⟧)
    (hT : Triangle.mk ((derivedUnit _ (smallLocalizationNatTrans
      (Submonoid.powers f))).app (localCohomologyObject A I hI M)) g h ∈ distTriang _) :
    ∃ e : (Triangle.mk ((derivedUnit _ (smallLocalizationNatTrans
        (Submonoid.powers f))).app (localCohomologyObject A I hI M)) g h).invRotate.obj₁ ≅
        localCohomologyObject A (I ⊔ Ideal.span {f})
          (Submodule.FG.sup hI (Submodule.fg_span_singleton f)) M,
      e.hom ≫ mapOfLE A I (I ⊔ Ideal.span {f}) hI
          (Submodule.FG.sup hI (Submodule.fg_span_singleton f)) le_sup_left M =
        (Triangle.mk ((derivedUnit _ (smallLocalizationNatTrans
          (Submonoid.powers f))).app (localCohomologyObject A I hI M)) g h).invRotate.mor₁ := by
  classical
  let S := Submonoid.powers f
  let F := smallLocalizationFunctor S
  let D := F.mapDerivedCategory
  let η := derivedUnit F (smallLocalizationNatTrans S)
  let X := localCohomologyObject A I hI M
  let K := (DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M
  let T := (Triangle.mk (η.app X) g h).invRotate
  have hT' : T ∈ distTriang _ := inv_rot_of_distTriang _ hT
  have hF : IsZero (D.obj T.obj₁) :=
    Triangle.isZero₁_of_isIso₂ _ (D.map_distinguished _ hT')
      (derivedUnit_map_isIso F (smallLocalizationNatTrans S)
        (smallLocalizationNatTrans_map_isIso S) X)
  have hIcopy := hI
  obtain ⟨s, hs⟩ := hIcopy
  have hXI : Dualizing.derivedPowerTorsionProperty A I hI X :=
    (Dualizing.localCohomologyFunctor A I hI).obj K |>.property
  have hTI : Dualizing.derivedPowerTorsionProperty A I hI T.obj₁ := by
    apply (derivedPowerTorsion_iff_localizations I hI s hs T.obj₁).mpr
    intro a ha
    let G := (smallLocalizationFunctor (Submonoid.powers a)).mapDerivedCategory
    have hGX : IsZero (G.obj X) :=
      (derivedPowerTorsion_iff_localizations I hI s hs X).mp hXI a ha
    exact Triangle.isZero₁_of_isZero₂₃ _ (G.map_distinguished _ hT') hGX
      (derivedLocalization_preserves_kernel (Submonoid.powers a) S X hGX)
  let L := I ⊔ Ideal.span {f}
  let hL : L.FG := Submodule.FG.sup hI (Submodule.fg_span_singleton f)
  have hIL : I ≤ L := le_sup_left
  have hsL : Ideal.span ((insert f s : Finset A) : Set A) = L := by
    simp only [Finset.coe_insert, Ideal.span_insert, hs, L, sup_comm]
  have hTL : Dualizing.derivedPowerTorsionProperty A L hL T.obj₁ := by
    apply (derivedPowerTorsion_iff_localizations L hL (insert f s) hsL T.obj₁).mpr
    intro a ha
    rcases Finset.mem_insert.mp ha with rfl | ha
    · exact hF
    · exact (derivedPowerTorsion_iff_localizations I hI s hs T.obj₁).mp hTI a ha
  let adj := Dualizing.localCohomologyAdjunction A L hL
  let W : Dualizing.PowerTorsionDerivedCategory A L hL := ⟨T.obj₁, hTL⟩
  let a : T.obj₁ ⟶ localCohomologyObject A L hL M :=
    (adj.homEquiv W K (T.mor₁ ≫ localCohomologyAugmentation A I hI M)).hom
  have ha : a ≫ localCohomologyAugmentation A L hL M =
      T.mor₁ ≫ localCohomologyAugmentation A I hI M :=
    (adj.homEquiv_counit (g := adj.homEquiv W K
      (T.mor₁ ≫ localCohomologyAugmentation A I hI M))).symm.trans
        ((adj.homEquiv W K).symm_apply_apply _)
  have hacomp : a ≫ mapOfLE A I L hI hL hIL M = T.mor₁ := by
    apply (localCohomology_counit_bijective A I hI K T.obj₁ hTI).injective
    show (a ≫ mapOfLE A I L hI hL hIL M) ≫ localCohomologyAugmentation A I hI M =
      T.mor₁ ≫ localCohomologyAugmentation A I hI M
    rw [Category.assoc, localCohomologyMapOfLE_comp_augmentation I L hI hL hIL M, ha]
  let Y := localCohomologyObject A L hL M
  have hYL : Dualizing.derivedPowerTorsionProperty A L hL Y :=
    ((Dualizing.localCohomologyFunctor A L hL).obj K).property
  have hYF : IsZero (D.obj Y) :=
    (derivedPowerTorsion_iff_localizations L hL (insert f s) hsL Y).mp hYL f
      (Finset.mem_insert_self _ _)
  have hη : ∀ V, IsIso (η.app (D.obj V)) := fun V =>
    derivedUnit_obj_isIso F (smallLocalizationNatTrans S)
      (smallLocalizationNatTrans_obj_isIso S) V
  obtain ⟨b, hb⟩ := (localizationFiber_precomp_bijective D η hη X
    Z g h hT Y hYF).surjective (mapOfLE A I L hI hL hIL M)
  change b ≫ T.mor₁ = mapOfLE A I L hI hL hIL M at hb
  have hab : a ≫ b = 𝟙 T.obj₁ := by
    apply (localizationFiber_precomp_bijective D η hη X Z g h hT T.obj₁ hF).injective
    show (a ≫ b) ≫ T.mor₁ = (𝟙 T.obj₁) ≫ T.mor₁
    simp only [Category.assoc, Category.id_comp, hb]
    exact hacomp
  have hba : b ≫ a = 𝟙 Y := by
    apply (localCohomology_counit_bijective A L hL K Y hYL).injective
    show (b ≫ a) ≫ localCohomologyAugmentation A L hL M =
      (𝟙 Y) ≫ localCohomologyAugmentation A L hL M
    have e1 : (b ≫ a) ≫ localCohomologyAugmentation A L hL M =
        b ≫ (T.mor₁ ≫ localCohomologyAugmentation A I hI M) :=
      (Category.assoc b a _).trans (congrArg (fun t => b ≫ t) ha)
    have e2 : b ≫ (T.mor₁ ≫ localCohomologyAugmentation A I hI M) =
        localCohomologyAugmentation A L hL M :=
      (Category.assoc b T.mor₁ (localCohomologyAugmentation A I hI M)).symm.trans
        ((congrArg (fun t => t ≫ localCohomologyAugmentation A I hI M) hb).trans
          (localCohomologyMapOfLE_comp_augmentation I L hI hL hIL M))
    exact (e1.trans e2).trans (Category.id_comp _).symm
  exact ⟨⟨a, b, hab, hba⟩, hacomp⟩

/-- An element of a module that vanishes after localization at a multiplicative subset is
annihilated by some element of that subset. -/
private theorem exists_complement_smul_eq_zero
    {A : Type u} [CommRing A] (S : Submonoid A)
    (N : ModuleCat.{v} A) [Subsingleton (LocalizedModule S N)] (x : N) :
    ∃ s : S, (s : A) • x = 0 := by
  obtain ⟨s, hs, hkill⟩ := LocalizedModule.mem_ker_mkLinearMap_iff.mp
    (Subsingleton.elim (LocalizedModule.mkLinearMap S N x) 0)
  exact ⟨⟨s, hs⟩, hkill⟩

/-- **Stacks 0DWU, the enlargement step.** If `Hⁱ⁻¹_{V(I)}(M)` vanishes after localization at a
multiplicative subset `S` and a class on `V(I + (f))` dies on `V(I)`, then it dies already on
`V(I + (f s))` for some `s ∈ S`. -/
private theorem localCohomology_kernel_eventually_zero
    (A : Type u) [CommRing A] (I : Ideal A) (S : Submonoid A) (hI : I.FG)
    (M : ModuleCat.{v} A) (i : ℤ)
    (hvan : Subsingleton
      (LocalizedModule S (localCohomologyModule A I hI M (i - 1))))
    (f : A) (x : localCohomologyModule A (I ⊔ Ideal.span {f})
      (Submodule.FG.sup hI (Submodule.fg_span_singleton f)) M i)
    (hx : (localCohomologyModuleMapOfLE A I (I ⊔ Ideal.span {f}) hI
      (Submodule.FG.sup hI (Submodule.fg_span_singleton f)) le_sup_left M i).hom x = 0) :
    ∃ s : S,
      (localCohomologyModuleMapOfLE A (I ⊔ Ideal.span {f * (s : A)}) (I ⊔ Ideal.span {f})
        (Submodule.FG.sup hI (Submodule.fg_span_singleton (f * (s : A))))
        (Submodule.FG.sup hI (Submodule.fg_span_singleton f))
        (sup_le_sup_left
          (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right f (s : A))) I)
        M i).hom x = 0 := by
  classical
  let X := localCohomologyObject A I hI M
  let H := DerivedCategory.homologyFunctor (ModuleCat.{v} A) i
  let Hprev := DerivedCategory.homologyFunctor (ModuleCat.{v} A) (i - 1)
  let F := smallLocalizationFunctor (Submonoid.powers f)
  let η := derivedUnit F (smallLocalizationNatTrans (Submonoid.powers f))
  obtain ⟨Z, g, h, hT⟩ := distinguished_cocone_triangle (η.app X)
  let T := (Triangle.mk (η.app X) g h).invRotate
  have hT' : T ∈ distTriang _ := inv_rot_of_distTriang _ hT
  obtain ⟨e, he⟩ := localCohomology_fiber_iso A I hI M f Z g h hT
  let L := I ⊔ Ideal.span {f}
  let hL : L.FG := Submodule.FG.sup hI (Submodule.fg_span_singleton f)
  let ξ := (H.mapIso e).inv.hom x
  have hex : (H.mapIso e).hom.hom ξ = x := congrArg (fun k => k.hom x) (H.mapIso e).inv_hom_id
  have hξ : (H.map T.mor₁).hom ξ = 0 := by
    have h1 : (H.map T.mor₁).hom ξ =
        (H.map (e.hom ≫ mapOfLE A I L hI hL le_sup_left M)).hom ξ :=
      congrArg (fun k => (H.map k).hom ξ) he.symm
    have h2 : (H.map (e.hom ≫ mapOfLE A I L hI hL le_sup_left M)).hom ξ =
        (H.map (mapOfLE A I L hI hL le_sup_left M)).hom ((H.map e.hom).hom ξ) := by
      rw [Functor.map_comp, ModuleCat.comp_apply]
    exact (h1.trans h2).trans (hex ▸ hx)
  have hseq := DerivedCategory.HomologySequence.exact₁ T hT' (i - 1) i (by omega)
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hseq
  obtain ⟨z, hz⟩ := (hseq ξ).mp hξ
  change (DerivedCategory.HomologySequence.δ T (i - 1) i (by omega)).hom z = ξ at hz
  let ef := (Dualizing.mapDerivedCategoryHomologyIso F (i - 1)).app X
  have hkill : ∀ w : smallLocalization (Submonoid.powers f) (Hprev.obj X),
      ∃ s : S, (s : A) • w = 0 := by
    intro w
    obtain ⟨⟨m, t⟩, rfl⟩ := IsLocalizedModule.mk'_surjective (Submonoid.powers f)
      (smallLocalizationUnit (Submonoid.powers f) (Hprev.obj X)) w
    have : Subsingleton (LocalizedModule S (Hprev.obj X)) := hvan
    obtain ⟨s, hs⟩ := exists_complement_smul_eq_zero S (Hprev.obj X) m
    refine ⟨s, ?_⟩
    show (s : A) • IsLocalizedModule.mk'
      (smallLocalizationUnit (Submonoid.powers f) (Hprev.obj X)) m t = 0
    rw [← IsLocalizedModule.mk'_smul, hs, IsLocalizedModule.mk'_zero]
  obtain ⟨s, hs⟩ := hkill (ef.hom.hom z)
  have hsz : (s : A) • z = 0 := by
    apply (ModuleCat.mono_iff_injective ef.hom).mp inferInstance
    show ef.hom.hom ((s : A) • z) = ef.hom.hom 0
    rw [map_zero]
    exact (ef.hom.hom.map_smul (s : A) z).trans hs
  let G := smallLocalizationFunctor (Submonoid.powers (f * (s : A)))
  let θ := derivedUnit G (smallLocalizationNatTrans (Submonoid.powers (f * (s : A))))
  obtain ⟨Z', g', h', hU⟩ := distinguished_cocone_triangle (θ.app X)
  let U := (Triangle.mk (θ.app X) g' h').invRotate
  have hU' : U ∈ distTriang _ := inv_rot_of_distTriang _ hU
  obtain ⟨e', he'⟩ := localCohomology_fiber_iso A I hI M (f * (s : A)) Z' g' h' hU
  obtain ⟨c, hc⟩ := principalLocalization_comparison_exists f (s : A) X
  have hc' : T.mor₂ ≫ c = (𝟙 X) ≫ U.mor₂ := by
    show η.app X ≫ c = (𝟙 X) ≫ θ.app X
    rw [Category.id_comp]
    exact hc
  obtain ⟨a, ha₁, ha₃⟩ := complete_distinguished_triangle_morphism₁ T U hT' hU' (𝟙 X) c hc'
  let φ : T ⟶ U := ⟨a, 𝟙 X, c, ha₁, hc', ha₃⟩
  have hcz : (Hprev.map c).hom z = 0 := by
    let eg := (Dualizing.mapDerivedCategoryHomologyIso G (i - 1)).app X
    apply (ModuleCat.mono_iff_injective eg.hom).mp inferInstance
    apply IsLocalizedModule.smul_injective
      (smallLocalizationUnit (Submonoid.powers (f * (s : A))) (Hprev.obj X))
      (⟨f * (s : A), Submonoid.mem_powers (f * (s : A))⟩ :
        Submonoid.powers (f * (s : A)))
    have w1 : (s : A) • eg.hom.hom ((Hprev.map c).hom z) = 0 := by
      have u1 : eg.hom.hom ((Hprev.map c).hom ((s : A) • z)) =
          (s : A) • eg.hom.hom ((Hprev.map c).hom z) :=
        (congrArg eg.hom.hom ((Hprev.map c).hom.map_smul (s : A) z)).trans
          (eg.hom.hom.map_smul (s : A) ((Hprev.map c).hom z))
      have u2 : eg.hom.hom ((Hprev.map c).hom ((s : A) • z)) = 0 := by
        rw [hsz]
        exact (congrArg eg.hom.hom (Hprev.map c).hom.map_zero).trans eg.hom.hom.map_zero
      exact u1.symm.trans u2
    show (f * (s : A)) • eg.hom.hom ((Hprev.map c).hom z) =
      (f * (s : A)) • eg.hom.hom 0
    rw [mul_smul, w1]
    simp
  have haz : (H.map a).hom ξ = 0 := by
    have hn := (DerivedCategory.homologyFunctor (ModuleCat.{v} A) 0).homologySequenceδ_naturality
      φ (i - 1) i (by omega)
    have hn' := congrArg (fun k => k.hom z) hn
    change (DerivedCategory.HomologySequence.δ U (i - 1) i (by omega)).hom
        ((Hprev.map c).hom z) = (H.map a).hom
          ((DerivedCategory.HomologySequence.δ T (i - 1) i (by omega)).hom z) at hn'
    rw [hcz, hz] at hn'
    exact hn'.symm.trans
      (DerivedCategory.HomologySequence.δ U (i - 1) i (by omega)).hom.map_zero
  let L' := I ⊔ Ideal.span {f * (s : A)}
  let hL' : L'.FG := Submodule.FG.sup hI (Submodule.fg_span_singleton (f * (s : A)))
  have hLL : L' ≤ L :=
    sup_le_sup_left (Ideal.span_singleton_le_span_singleton.mpr (dvd_mul_right f (s : A))) I
  have ha : a ≫ U.mor₁ = T.mor₁ := by
    change T.mor₁ ≫ 𝟙 T.obj₂ = a ≫ U.mor₁ at ha₁
    rw [Category.comp_id] at ha₁
    exact ha₁.symm
  have heaug : e.hom ≫ localCohomologyAugmentation A L hL M =
      T.mor₁ ≫ localCohomologyAugmentation A I hI M := by
    rw [← localCohomologyMapOfLE_comp_augmentation I L hI hL le_sup_left M, ← Category.assoc]
    exact congrArg (· ≫ localCohomologyAugmentation A I hI M) he
  have heaug' : e'.hom ≫ localCohomologyAugmentation A L' hL' M =
      U.mor₁ ≫ localCohomologyAugmentation A I hI M := by
    rw [← localCohomologyMapOfLE_comp_augmentation I L' hI hL' le_sup_left M, ← Category.assoc]
    exact congrArg (· ≫ localCohomologyAugmentation A I hI M) he'
  have hmap : e.inv ≫ a ≫ e'.hom = mapOfLE A L' L hL' hL hLL M := by
    apply (localCohomology_counit_bijective A L' hL'
      ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M)
      (localCohomologyObject A L hL M)
      (restrictLocalCohomologySupport A L' L hL' hL hLL M).property).injective
    show (e.inv ≫ a ≫ e'.hom) ≫ localCohomologyAugmentation A L' hL' M =
      mapOfLE A L' L hL' hL hLL M ≫ localCohomologyAugmentation A L' hL' M
    have r1 : (e.inv ≫ a ≫ e'.hom) ≫ localCohomologyAugmentation A L' hL' M =
        e.inv ≫ ((a ≫ e'.hom) ≫ localCohomologyAugmentation A L' hL' M) :=
      Category.assoc e.inv (a ≫ e'.hom) (localCohomologyAugmentation A L' hL' M)
    have r2 : (a ≫ e'.hom) ≫ localCohomologyAugmentation A L' hL' M =
        a ≫ (e'.hom ≫ localCohomologyAugmentation A L' hL' M) :=
      Category.assoc a e'.hom (localCohomologyAugmentation A L' hL' M)
    have r3 : a ≫ (e'.hom ≫ localCohomologyAugmentation A L' hL' M) =
        a ≫ (U.mor₁ ≫ localCohomologyAugmentation A I hI M) :=
      congrArg (fun t => a ≫ t) heaug'
    have r4 : a ≫ (U.mor₁ ≫ localCohomologyAugmentation A I hI M) =
        (a ≫ U.mor₁) ≫ localCohomologyAugmentation A I hI M :=
      (Category.assoc a U.mor₁ (localCohomologyAugmentation A I hI M)).symm
    have r5 : (a ≫ U.mor₁) ≫ localCohomologyAugmentation A I hI M =
        T.mor₁ ≫ localCohomologyAugmentation A I hI M :=
      congrArg (fun t => t ≫ localCohomologyAugmentation A I hI M) ha
    have r6 : e.inv ≫ (e.hom ≫ localCohomologyAugmentation A L hL M) =
        localCohomologyAugmentation A L hL M := by
      rw [Iso.inv_hom_id_assoc]
    have rl : (e.inv ≫ a ≫ e'.hom) ≫ localCohomologyAugmentation A L' hL' M =
        localCohomologyAugmentation A L hL M :=
      r1.trans ((congrArg (fun t => e.inv ≫ t)
        ((((r2.trans r3).trans r4).trans r5).trans heaug.symm)).trans r6)
    exact rl.trans (localCohomologyMapOfLE_comp_augmentation L' L hL' hL hLL M).symm
  refine ⟨s, ?_⟩
  show (H.map (mapOfLE A L' L hL' hL hLL M)).hom x = 0
  rw [← hmap, Functor.map_comp, Functor.map_comp, ModuleCat.comp_apply, ModuleCat.comp_apply]
  show (H.map e'.hom).hom ((H.map a).hom ξ) = 0
  rw [haz, map_zero]

/-- Among the finitely generated intermediate supports `I ≤ K ≤ J` that already annihilate a
given class of `Hⁱ_{V(J)}(M)`, Noetherianity provides a maximal one. -/
private theorem exists_maximal_intermediate_kernel
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J)
    (M : ModuleCat.{v} A) (i : ℤ)
    (z : localCohomologyModule A J hJ M i)
    (hz : (localCohomologyModuleMapOfLE A I J hI hJ hIJ M i).hom z = 0) :
    ∃ K : Ideal A, I ≤ K ∧ ∃ hKJ : K ≤ J,
      (localCohomologyModuleMapOfLE A K J
        (Ideal.fg_of_isNoetherianRing K) hJ hKJ M i).hom z = 0 ∧
      ∀ L : Ideal A, I ≤ L → ∀ hLJ : L ≤ J,
        (localCohomologyModuleMapOfLE A L J
          (Ideal.fg_of_isNoetherianRing L) hJ hLJ M i).hom z = 0 →
        ¬ K < L := by
  classical
  let s : Set (Ideal A) := {K | I ≤ K ∧ ∃ hKJ : K ≤ J,
    (localCohomologyModuleMapOfLE A K J
      (Ideal.fg_of_isNoetherianRing K) hJ hKJ M i).hom z = 0}
  obtain ⟨K, ⟨hIK, hKJ, hKzero⟩, hmax⟩ :=
    (IsNoetherian.wf (inferInstance : IsNoetherian A A)).has_min s ⟨I, le_rfl, hIJ, hz⟩
  exact ⟨K, hIK, hKJ, hKzero, fun L hIL hLJ hLzero => hmax L ⟨hIL, hLJ, hLzero⟩⟩

end SupportInjectivity

open SupportInjectivity SupportSurjectivity

/-- **Injectivity of the change of support.** For finitely generated ideals `I ≤ J` of a
Noetherian ring, the canonical map `Hⁱ_{V(J)}(M) ⟶ Hⁱ_{V(I)}(M)` is injective as soon as the
local cohomology of `M_𝔭` with support in the maximal ideal of `A_𝔭` vanishes in degree `i - 1`
for every prime `𝔭 ∈ V(I) \ V(J)`. -/
@[stacks 0DWV "injectivity"]
public theorem localCohomologyModuleMapOfLE_injective
    {A : Type u} [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J)
    (M : ModuleCat.{v} A) (i : ℤ) (_hi : 0 ≤ i)
    (hvan : ∀ (p : Ideal A) [p.IsPrime], I ≤ p → ¬ J ≤ p →
      Subsingleton
        (localCohomologyModule (Localization.AtPrime p)
          (p.map (algebraMap A (Localization.AtPrime p)))
          ((Ideal.fg_of_isNoetherianRing p).map (algebraMap A (Localization.AtPrime p)))
          (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M))
          (i - 1))) :
    Function.Injective
      ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
        (Stacks.Algebraization.localCohomologyComparison A J I hJ hI hIJ
          ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M))).hom := by
  show Function.Injective (localCohomologyModuleMapOfLE A I J hI hJ hIJ M i).hom
  intro x y hxy
  classical
  let z : localCohomologyModule A J hJ M i := x - y
  have hz : (localCohomologyModuleMapOfLE A I J hI hJ hIJ M i).hom z = 0 := by
    simp only [z, map_sub, hxy, sub_self]
  obtain ⟨K, hIK, hKJ, hKzero, hKmax⟩ :=
    exists_maximal_intermediate_kernel I J hI hJ hIJ M i z hz
  suffices z = 0 from sub_eq_zero.mp this
  by_cases hradEq : K.radical = J.radical
  · let g := localCohomologyModuleMapOfLE A K J
      (Ideal.fg_of_isNoetherianRing K) hJ hKJ M i
    have : IsIso g := isIso_localCohomologyModuleMapOfLE_of_radical_eq K J
      (Ideal.fg_of_isNoetherianRing K) hJ hKJ hradEq M i
    exact (ModuleCat.mono_iff_injective g).mp inferInstance (by simpa using hKzero)
  · exfalso
    obtain ⟨p, hpK, hJp⟩ := exists_minimalPrime_not_contains_of_radical_ne K J hKJ hradEq
    have : p.IsPrime := hpK.1.1
    have hKp : K ≤ p := hpK.1.2
    let B := Localization.AtPrime p
    let fB := algebraMap A B
    let hKfg : K.FG := Ideal.fg_of_isNoetherianRing K
    let hKmap : (K.map fB).FG := hKfg.map fB
    let hpmap : (p.map fB).FG := (Ideal.fg_of_isNoetherianRing p).map fB
    have hprimeMap : (p.map fB).IsPrime := by
      rw [IsLocalization.AtPrime.map_eq_maximalIdeal]
      exact (IsLocalRing.maximalIdeal.isMaximal B).isPrime
    have hradp : (K.map fB).radical = (p.map fB).radical := by
      rw [IsLocalization.AtPrime.radical_map_of_mem_minimalPrimes
        (A := B) p K hpK, hprimeMap.radical]
    have hpvan : Subsingleton (localCohomologyModule B (p.map fB) hpmap
        (ModuleCat.of B (LocalizedModule p.primeCompl M)) (i - 1)) :=
      hvan p (hIK.trans hKp) hJp
    have hKmapvan : Subsingleton (localCohomologyModule B (K.map fB) hKmap
        (ModuleCat.of B (LocalizedModule p.primeCompl M)) (i - 1)) := by
      let gB := localCohomologyModuleMapOfLE B (K.map fB) (p.map fB)
        hKmap hpmap (Ideal.map_mono hKp)
        (ModuleCat.of B (LocalizedModule p.primeCompl M)) (i - 1)
      have : IsIso gB := isIso_localCohomologyModuleMapOfLE_of_radical_eq
        (K.map fB) (p.map fB) hKmap hpmap (Ideal.map_mono hKp) hradp
        (ModuleCat.of B (LocalizedModule p.primeCompl M)) (i - 1)
      let e := asIso gB
      refine ⟨fun a b => ?_⟩
      have hinv : Function.Injective e.inv.hom :=
        (ModuleCat.mono_iff_injective e.inv).mp inferInstance
      exact hinv (@Subsingleton.elim _ hpvan (e.inv.hom a) (e.inv.hom b))
    have hlocvan := localized_localCohomology_subsingleton A K hKfg M p (i - 1) hKmapvan
    obtain ⟨a, haJ, hap⟩ := SetLike.not_le_iff_exists.mp hJp
    let L := K ⊔ Ideal.span {a}
    let hL : L.FG := Submodule.FG.sup hKfg (Submodule.fg_span_singleton a)
    have hKL : K ≤ L := le_sup_left
    have hLJ : L ≤ J := sup_le hKJ ((Ideal.span_singleton_le_iff_mem J).mpr haJ)
    let zL := (localCohomologyModuleMapOfLE A L J hL hJ hLJ M i).hom z
    have hzL : (localCohomologyModuleMapOfLE A K L hKfg hL hKL M i).hom zL = 0 := by
      have hcomp := localCohomologyModuleMapOfLE_comp K L J hKfg hL hJ hKL hLJ M i
      have hEval := congrArg (fun q => q.hom z) hcomp
      change (localCohomologyModuleMapOfLE A K L hKfg hL hKL M i).hom
          ((localCohomologyModuleMapOfLE A L J hL hJ hLJ M i).hom z) =
        (localCohomologyModuleMapOfLE A K J hKfg hJ (hKL.trans hLJ) M i).hom z at hEval
      exact hEval.trans (by simpa using hKzero)
    obtain ⟨s, hs⟩ := localCohomology_kernel_eventually_zero A K p.primeCompl hKfg M i
      hlocvan a zL hzL
    let b := a * (s : A)
    let L' := K ⊔ Ideal.span {b}
    let hL' : L'.FG := Submodule.FG.sup hKfg (Submodule.fg_span_singleton b)
    have hL'L : L' ≤ L :=
      sup_le_sup_left (Ideal.span_singleton_le_span_singleton.mpr
        (dvd_mul_right a (s : A))) K
    have hbJ : b ∈ J := J.mul_mem_right (s : A) haJ
    have hbp : b ∉ p := p.primeCompl.mul_mem hap s.property
    have hL'J : L' ≤ J := sup_le hKJ ((Ideal.span_singleton_le_iff_mem J).mpr hbJ)
    have hL'zero : (localCohomologyModuleMapOfLE A L' J hL' hJ hL'J M i).hom z = 0 := by
      have hcomp := localCohomologyModuleMapOfLE_comp L' L J hL' hL hJ hL'L hLJ M i
      have hEval := congrArg (fun q => q.hom z) hcomp
      change (localCohomologyModuleMapOfLE A L' L hL' hL hL'L M i).hom
          ((localCohomologyModuleMapOfLE A L J hL hJ hLJ M i).hom z) =
        (localCohomologyModuleMapOfLE A L' J hL' hJ (hL'L.trans hLJ) M i).hom z at hEval
      exact hEval.symm.trans hs
    have hKL' : K ≤ L' := le_sup_left
    have hstrict : K < L' := by
      refine lt_of_le_of_ne hKL' fun heq => hbp (hKp ?_)
      exact heq ▸ Ideal.mem_sup_right (Ideal.mem_span_singleton_self b)
    exact hKmax L' (hIK.trans hKL') hL'J (by simpa using hL'zero) hstrict

/-- **The change of support is an isomorphism.** For finitely generated ideals `I ≤ J` of a
Noetherian ring, the canonical map `Hⁱ_{V(J)}(M) ⟶ Hⁱ_{V(I)}(M)` is an isomorphism as soon as the
local cohomology of `M_𝔭` with support in the maximal ideal of `A_𝔭` vanishes in degrees `i` and
`i - 1` for every prime `𝔭 ∈ V(I) \ V(J)`. -/
@[stacks 0DWV "isomorphism"]
public theorem isIso_localCohomologyModuleMapOfLE
    (A : Type u) [CommRing A] [IsNoetherianRing A]
    (I J : Ideal A) (hI : I.FG) (hJ : J.FG) (hIJ : I ≤ J)
    (M : ModuleCat.{v} A) (i : ℤ) (hi : 0 ≤ i)
    (hvan : ∀ (p : Ideal A) [p.IsPrime], I ≤ p → ¬ J ≤ p →
      (IsZero (localCohomologyModule (Localization.AtPrime p)
        (p.map (algebraMap A (Localization.AtPrime p)))
        ((Ideal.fg_of_isNoetherianRing p).map (algebraMap A (Localization.AtPrime p)))
        (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M)) i) ∧
      IsZero (localCohomologyModule (Localization.AtPrime p)
        (p.map (algebraMap A (Localization.AtPrime p)))
        ((Ideal.fg_of_isNoetherianRing p).map (algebraMap A (Localization.AtPrime p)))
        (ModuleCat.of (Localization.AtPrime p) (LocalizedModule p.primeCompl M))
        (i - 1)))) :
    IsIso ((DerivedCategory.homologyFunctor (ModuleCat.{v} A) i).map
      (Stacks.Algebraization.localCohomologyComparison A J I hJ hI hIJ
        ((DerivedCategory.singleFunctor (ModuleCat.{v} A) 0).obj M))) :=
  (ConcreteCategory.isIso_iff_bijective _).2
    ⟨localCohomologyModuleMapOfLE_injective I J hI hJ hIJ M i hi fun p _ hIp hJp =>
        ModuleCat.isZero_iff_subsingleton.mp (hvan p hIp hJp).2,
      localCohomologyModuleMapOfLE_surjective A I J hI hJ hIJ M i hi fun p _ hIp hJp =>
        (hvan p hIp hJp).1⟩

end Stacks.LocalCohomology
