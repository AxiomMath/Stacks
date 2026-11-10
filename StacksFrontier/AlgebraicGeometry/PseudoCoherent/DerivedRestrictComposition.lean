module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.RestrictPullbackCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.CompositionUnconditionalModels
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RelativeTorIndependentBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TrianglesComparison

/-!
# Restriction to opens as a derived pullback, along a composite

For open immersions `a : A ⟶ B` and `b : B ⟶ C`, the identification of `D(j^*)` with `Lj^*` of
`Scheme.Modules.derivedRestrictIsoDerivedPullback` for `j = a ≫ b` is the one for `b`, then the
one for `a`, through the composition isomorphisms of both sides ([Stacks, Tag 0D5S]).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Scheme.Modules

universe u

attribute [local instance 10000] HasDerivedCategory.standard

/-- `Functor.leftDerivedNatTrans_app` at the identity, with the instances passed explicitly. -/
theorem leftDerivedNatTrans_id_app_comp {𝒞 𝒟 ℋ : Type*} [Category 𝒞] [Category 𝒟] [Category ℋ]
    (L : 𝒞 ⥤ 𝒟) (W : MorphismProperty 𝒞) (hL : L.IsLocalization W) {F : 𝒞 ⥤ ℋ}
    (LF LF' : 𝒟 ⥤ ℋ) (α : L ⋙ LF ⟶ F) (α' : L ⋙ LF' ⟶ F) (hLF : LF.IsLeftDerivedFunctor α W)
    (X : 𝒞) :
    (Functor.leftDerivedNatTrans LF' LF α' α W (𝟙 F)).app (L.obj X) ≫ α.app X = α'.app X :=
  (Functor.leftDerivedNatTrans_app _ _ _ _ _ _ X).trans (Category.comp_id _)

/-- `(α ≪≫ β⁻¹)⁻¹` read through two characterizations. -/
theorem trans_symm_inv_app_comp {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟] {P Q R : 𝒞 ⥤ 𝒟}
    (α : P ≅ Q) (β : R ≅ Q) (X : 𝒞) {Y Z : 𝒟} (y : P.obj X ⟶ Y) (z : Q.obj X ⟶ Y)
    (w : Q.obj X ⟶ Z) (c : R.obj X ⟶ Z) (m : Z ⟶ Y) (h1 : α.hom.app X ≫ z = y)
    (h2 : β.hom.app X ≫ w = c) (h3 : z = w ≫ m) :
    (α ≪≫ β.symm).inv.app X ≫ y = c ≫ m := by
  subst h1 h2 h3
  simp

/-- **`D(j^*) ≅ Lj^*` on the homotopy category**: read through the structure maps, it is the
degreewise identification of restriction with pullback. -/
theorem derivedRestrictIsoDerivedPullback_inv_app_Qh {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (K : HomotopyCategory X.Modules (ComplexShape.up ℤ)) :
    (derivedRestrictIsoDerivedPullback j).inv.app (DerivedCategory.Qh.obj K) ≫
      (restrictFunctor j).mapDerivedCategoryFactorsh.hom.app K =
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        j.toLRSHom.toShHom).app K ≫
      DerivedCategory.Qh.map ((Stacks.Homology.mapHomotopyCategoryIso
        (restrictFunctorIsoPullback j).symm (ComplexShape.up ℤ)).hom.app K) := by
  dsimp only [derivedRestrictIsoDerivedPullback, Iso.trans_inv, Iso.symm_inv, NatTrans.comp_app]
  let : (pullback j).Additive := Functor.additive_of_iso (restrictFunctorIsoPullback j)
  let : PreservesFiniteLimits (pullback j) :=
    preservesFiniteLimits_of_natIso (restrictFunctorIsoPullback j)
  let : PreservesFiniteColimits (pullback j) :=
    preservesFiniteColimits_of_natIso (restrictFunctorIsoPullback j)
  rw [Stacks.Homology.mapDerivedCategoryIsoOfNatIso_eq]
  have h1 := Stacks.Homology.mapDerivedCategoryIsoOfIso_hom_app (restrictFunctor j)
    (pullback j) (restrictFunctorIsoPullback j) K
  have h2 : (SpecField.derivedPullbackMapDerivedIso j.toLRSHom.toShHom).hom.app
      (DerivedCategory.Qh.obj K) ≫
      (RingedSpaceModuleAdjunction.modulePullback
        j.toLRSHom.toShHom).mapDerivedCategoryFactorsh.hom.app K =
      (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
        j.toLRSHom.toShHom).app K := by
    simp only [SpecField.derivedPullbackMapDerivedIso, Functor.leftDerivedNatIso_hom]
    exact leftDerivedNatTrans_id_app_comp _ _ _ _ _ _ _ _ K
  refine trans_symm_inv_app_comp _ _ _ _ _ _ _ _ h1 h2 ?_
  rfl

/-- `restrictFunctorIsoPullback_inv_comp` with the two middle factors interchanged. -/
theorem restrictFunctorIsoPullback_inv_comp_app {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    [IsOpenImmersion a] [IsOpenImmersion b] (M : C.Modules) :
    (restrictFunctorIsoPullback (a ≫ b)).inv.app M =
      (pullbackComp a b).inv.app M ≫ (pullback a).map ((restrictFunctorIsoPullback b).inv.app M) ≫
        (restrictFunctorIsoPullback a).inv.app ((restrictFunctor b).obj M) ≫
        (restrictFunctorComp a b).inv.app M := by
  rw [Stacks.AlgebraicGeometry.ModuleLimits.restrictFunctorIsoPullback_inv_comp]
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app]
  rw [← (restrictFunctorIsoPullback a).inv.naturality_assoc]

/-- **The degreewise identification of restriction with pullback on homotopy categories is
compatible with composition.** -/
theorem mapHomotopyCategoryIso_restrictFunctorIsoPullback_comp {A B C : Scheme.{u}} (a : A ⟶ B)
    (b : B ⟶ C) [IsOpenImmersion a] [IsOpenImmersion b]
    (K : HomotopyCategory C.Modules (ComplexShape.up ℤ)) :
    (Stacks.Homology.mapHomotopyCategoryIso (restrictFunctorIsoPullback (a ≫ b)).symm
        (ComplexShape.up ℤ)).hom.app K =
      (Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso a.toLRSHom.toShHom
          b.toLRSHom.toShHom).inv.app K ≫
        ((RingedSpaceModuleAdjunction.modulePullback a.toLRSHom.toShHom).mapHomotopyCategory
          (ComplexShape.up ℤ)).map ((Stacks.Homology.mapHomotopyCategoryIso
            (restrictFunctorIsoPullback b).symm (ComplexShape.up ℤ)).hom.app K) ≫
        (Stacks.Homology.mapHomotopyCategoryIso (restrictFunctorIsoPullback a).symm
          (ComplexShape.up ℤ)).hom.app (((restrictFunctor b).mapHomotopyCategory
            (ComplexShape.up ℤ)).obj K) ≫
        (Functor.mapHomotopyCategoryCompIso (restrictFunctorComp a b).symm
          (ComplexShape.up ℤ)).hom.app K := by
  obtain ⟨P, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  simp only [Stacks.Homology.mapHomotopyCategoryIso,
    Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso,
    Functor.mapHomotopyCategoryCompIso, Quotient.natIsoLift, Functor.isoWhiskerRight_hom,
    Functor.isoWhiskerRight_inv]
  dsimp only [NatTrans.mapHomotopyCategory, Quotient.natTransLift]
  simp only [Functor.whiskerRight_app]
  congr 1
  refine HomologicalComplex.hom_ext _ _ (fun n => ?_)
  simp only [NatTrans.mapHomologicalComplex_app_f, Iso.symm_hom]
  exact restrictFunctorIsoPullback_inv_comp_app a b _

/-- The chase behind `derivedRestrictIsoDerivedPullback_inv_comp`. -/
theorem derivedRestrictIsoDerivedPullback_inv_comp_chase {𝒜 ℬ ℋ ℋ' : Type*} [Category 𝒜]
    [Category ℬ] [Category ℋ] [Category ℋ'] (G P : ℬ ⥤ 𝒜) (L : ℋ ⥤ 𝒜) (L' : ℋ' ⥤ ℬ)
    {a₀ e₀ : 𝒜} {b₀ b₁ : ℬ} {k₀ k₁ : ℋ'} {h₀ h₁ h₂ h₃ h₄ : ℋ}
    (γ : a₀ ⟶ e₀) (φ : e₀ ⟶ L.obj h₃) (φinv : L.obj h₃ ⟶ e₀)
    (i : P.obj b₀ ≅ a₀) (x : P.obj b₀ ⟶ G.obj b₀) (y : b₀ ⟶ b₁) (θ : G.obj b₁ ⟶ e₀)
    (f : b₁ ⟶ L'.obj k₁) (x' : P.obj (L'.obj k₁) ⟶ G.obj (L'.obj k₁))
    (g : G.obj (L'.obj k₁) ⟶ L.obj h₂)
    (hh : h₂ ⟶ h₃) (cab : a₀ ⟶ L.obj h₄) (mab : h₄ ⟶ h₃) (cb : b₀ ⟶ L'.obj k₀) (mb : k₀ ⟶ k₁)
    (ca' : P.obj (L'.obj k₁) ⟶ L.obj h₁) (ma : h₁ ⟶ h₂) (ca : P.obj (L'.obj k₀) ⟶ L.obj h₀)
    (pb : h₀ ⟶ h₁) (p : h₀ ≅ h₄)
    (F1 : γ ≫ φ = cab ≫ L.map mab) (F2 : θ = G.map f ≫ g ≫ L.map hh ≫ φinv) (hφ : φinv ≫ φ = 𝟙 _)
    (hx : P.map (y ≫ f) ≫ x' = x ≫ G.map (y ≫ f)) (F3 : y ≫ f = cb ≫ L'.map mb)
    (F4 : x' ≫ g = ca' ≫ L.map ma) (N2 : P.map (L'.map mb) ≫ ca' = ca ≫ L.map pb)
    (D : i.hom ≫ cab = P.map cb ≫ ca ≫ L.map p.hom) (Coh : mab = p.inv ≫ pb ≫ ma ≫ hh) :
    γ ≫ φ = (i.inv ≫ x ≫ G.map y ≫ θ) ≫ φ := by
  subst F2 Coh
  rw [F1]
  simp only [Category.assoc, hφ, Category.comp_id]
  rw [← G.map_comp_assoc, ← reassoc_of% hx, reassoc_of% F4, F3, P.map_comp_assoc, reassoc_of% N2,
    ← cancel_epi i.hom, Iso.hom_inv_id_assoc, reassoc_of% D]
  simp only [← L.map_comp, Iso.hom_inv_id_assoc]

attribute [local instance]
  Stacks.Cohomology.DerivedOpenImmersion.modulePullbackOpenImmersion_preservesFiniteColimits in
/-- **Restriction to an open as a derived pullback is compatible with composition.** -/
theorem derivedRestrictIsoDerivedPullback_inv_comp {A B C : Scheme.{u}} (a : A ⟶ B) (b : B ⟶ C)
    [IsOpenImmersion a] [IsOpenImmersion b] :
    (derivedRestrictIsoDerivedPullback (a ≫ b)).inv =
      (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a.toLRSHom.toShHom
        b.toLRSHom.toShHom).inv ≫
      Functor.whiskerLeft (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback
        b.toLRSHom.toShHom) (derivedRestrictIsoDerivedPullback a).inv ≫
      Functor.whiskerRight (derivedRestrictIsoDerivedPullback b).inv
        (restrictFunctor a).mapDerivedCategory ≫
      (Functor.mapDerivedCategoryCompIsoOfCompIso (restrictFunctorComp a b).symm).hom := by
  refine Functor.leftDerived_ext (restrictFunctor (a ≫ b)).mapDerivedCategory
    (restrictFunctor (a ≫ b)).mapDerivedCategoryFactorsh.hom
    (HomotopyCategory.quasiIso _ (ComplexShape.up ℤ)) _ _ _ ?_
  ext K
  open Stacks.Cohomology.DerivedPushforwardComposition in
  exact derivedRestrictIsoDerivedPullback_inv_comp_chase (restrictFunctor a).mapDerivedCategory
    (Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullback a.toLRSHom.toShHom)
    DerivedCategory.Qh DerivedCategory.Qh
    ((derivedRestrictIsoDerivedPullback (a ≫ b)).inv.app (DerivedCategory.Qh.obj K))
    ((restrictFunctor (a ≫ b)).mapDerivedCategoryFactorsh.hom.app K)
    ((restrictFunctor (a ≫ b)).mapDerivedCategoryFactorsh.inv.app K)
    ((Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical a.toLRSHom.toShHom
      b.toLRSHom.toShHom).app (DerivedCategory.Qh.obj K)) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((Stacks.DerivedPullback.Composition.pullbackOnHomotopyCompIso a.toLRSHom.toShHom
      b.toLRSHom.toShHom).app K)
    (derivedRestrictIsoDerivedPullback_inv_app_Qh (a ≫ b) K)
    (Functor.mapDerivedCategoryCompIso_hom_app_Qh (restrictFunctorComp a b).symm K)
    ((restrictFunctor (a ≫ b)).mapDerivedCategoryFactorsh.inv_hom_id_app K)
    ((derivedRestrictIsoDerivedPullback a).inv.naturality _)
    (derivedRestrictIsoDerivedPullback_inv_app_Qh b K)
    (derivedRestrictIsoDerivedPullback_inv_app_Qh a _)
    ((Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces.derivedPullbackComparison
      a.toLRSHom.toShHom).naturality _)
    (derivedPullbackCompIsoCanonical_hom_app_comp_comparison_of_models a.toLRSHom.toShHom
      b.toLRSHom.toShHom K)
    (mapHomotopyCategoryIso_restrictFunctorIsoPullback_comp a b K)

/-- `Stacks.MapDerivedHomologyCompat.mapDerivedCategoryHomologyIso_hom_app_of_comp_iso` for
restriction along a composite of open immersions. -/
theorem homologyFunctor_map_mapDerivedCategoryCompIso_restrictFunctorComp {A B C : Scheme.{u}}
    (a : A ⟶ B) (b : B ⟶ C) [IsOpenImmersion a] [IsOpenImmersion b]
    (K : DerivedCategory C.Modules) :
    (DerivedCategory.homologyFunctor A.Modules 0).map
        ((Functor.mapDerivedCategoryCompIsoOfCompIso (restrictFunctorComp a b).symm).hom.app K) ≫
      ((restrictFunctor (a ≫ b)).mapDerivedCategoryHomologyIso 0).hom.app K =
    ((restrictFunctor a).mapDerivedCategoryHomologyIso 0).hom.app
        ((restrictFunctor b).mapDerivedCategory.obj K) ≫
      (restrictFunctor a).map (((restrictFunctor b).mapDerivedCategoryHomologyIso 0).hom.app K) ≫
      (restrictFunctorComp a b).inv.app ((DerivedCategory.homologyFunctor C.Modules 0).obj K) :=
  Stacks.MapDerivedHomologyCompat.mapDerivedCategoryHomologyIso_hom_app_of_comp_iso _ _ _ _ 0 K

end AlgebraicGeometry.Scheme.Modules
