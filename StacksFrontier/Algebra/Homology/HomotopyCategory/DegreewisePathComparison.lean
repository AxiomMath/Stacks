module

public import Mathlib.Algebra.Homology.HomotopyCategory
public import StacksFrontier.CategoryTheory.Functor.Derived.BaseChangePathComparison

/-!
# Two composites of degreewise isomorphisms in homotopy categories

Two paths of degreewise isomorphisms between additive functors, read on homotopy categories, agree
up to a degreewise endomorphism as soon as the corresponding identity holds between the functors
themselves: every morphism in sight is the quotient of a morphism of complexes, computed degree
by degree.

## Main definitions

* `Stacks.Homology.homotopyEdgeIso`: the isomorphism on homotopy categories induced degreewise by
  an isomorphism of additive functors.

## Main results

* `Stacks.Homology.quotient_paths_eq`, `Stacks.Homology.quotient_paths_eq_of_eq`
* `Stacks.Homology.exists_app_eq_comp_map`: two such paths differ by an endomorphism.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Homology

variable {MR MR' MA MA' V₀ V₁ V₁' V₂ T : Type*} [Category MR] [Category MR'] [Category MA]
  [Category MA'] [Category V₀] [Category V₁] [Category V₁'] [Category V₂] [Preadditive MR]
  [Preadditive MR'] [Preadditive MA] [Preadditive MA'] [Preadditive V₀] [Preadditive V₁]
  [Preadditive V₁'] [Preadditive V₂]
  {F₀ : MR ⥤ V₀} {F₁ : MR' ⥤ V₁} {F₁' : MA ⥤ V₁'} {F₂ : MA' ⥤ V₂}
  [F₀.Additive] [F₁.Additive] [F₁'.Additive] [F₂.Additive]
  {q₁ : V₀ ⥤ V₁} {q₂ : V₁ ⥤ V₂} {q₁' : V₀ ⥤ V₁'} {q₂' : V₁' ⥤ V₂}
  [q₁.Additive] [q₂.Additive] [q₁'.Additive] [q₂'.Additive]
  {y₁ : MR ⥤ MR'} {y₂ : MR' ⥤ MA'} {y₁' : MR ⥤ MA} {y₂' : MA ⥤ MA'} {yc : MR ⥤ MA'}
  [y₁.Additive] [y₂.Additive] [y₁'.Additive] [y₂'.Additive] [yc.Additive]
  [(y₁ ⋙ F₁).Additive] [(y₂ ⋙ F₂).Additive] [(y₁' ⋙ F₁').Additive] [(y₂' ⋙ F₂).Additive]
  {Ψ : T → (V₀ ⥤ V₂)} [∀ t, (Ψ t).Additive]

/-- The isomorphism of functors on homotopy categories induced degreewise by an isomorphism
`r : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁` of additive functors. -/
noncomputable def homotopyEdgeIso (r : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁) :
    (F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙
        q₁.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      y₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _ :=
  NatIso.ofComponents (fun K => (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).mapIso
      ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (y₁ ⋙ F₁))
          (ComplexShape.up ℤ)).symm).app K))
    (fun {K L} φ => ((HomotopyCategory.quotient _ _).map_comp _ _).symm.trans
      ((congrArg (HomotopyCategory.quotient _ (ComplexShape.up ℤ)).map
        ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
          (Functor.mapHomologicalComplexCompIso (Iso.refl (y₁ ⋙ F₁))
            (ComplexShape.up ℤ)).symm).hom.naturality φ)).trans
        ((HomotopyCategory.quotient _ _).map_comp _ _)))

theorem homotopyEdgeIso_hom_app (r : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁) (K : CochainComplex MR ℤ) :
    (homotopyEdgeIso r).hom.app K = (HomotopyCategory.quotient _ _).map
      ((Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (y₁ ⋙ F₁))
          (ComplexShape.up ℤ)).symm).hom.app K) :=
  rfl

/-- The comparison of homotopy categories attached to `e : F ⋙ G ≅ H`, at the class of a
complex, is the class of the degreewise action of `e`. -/
theorem mapHomotopyCategoryCompIso_inv_app_quotient_obj {H : V₀ ⥤ V₂} [H.Additive]
    (e : q₁ ⋙ q₂ ≅ H) (K : CochainComplex V₀ ℤ) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app
        ((HomotopyCategory.quotient _ _).obj K) =
      (HomotopyCategory.quotient _ _).map
        ((Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).inv.app K) :=
  rfl

/-- **Two paths of degreewise isomorphisms, on complexes.** -/
theorem chain_paths_eq {H : V₀ ⥤ V₂} [H.Additive] (e : q₁ ⋙ q₂ ≅ H) (e' : q₁' ⋙ q₂' ≅ H)
    (r₁ : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁) (r₂ : F₁ ⋙ q₂ ≅ y₂ ⋙ F₂) (r₁' : F₀ ⋙ q₁' ≅ y₁' ⋙ F₁')
    (r₂' : F₁' ⋙ q₂' ≅ y₂' ⋙ F₂) (s : y₁ ⋙ y₂ ⟶ yc) (s' : y₁' ⋙ y₂' ⟶ yc) (τm : yc ⟶ yc)
    (hmod : ∀ M, e.inv.app (F₀.obj M) ≫ q₂.map (r₁.hom.app M) ≫ r₂.hom.app (y₁.obj M) ≫
        F₂.map (s.app M) =
      e'.inv.app (F₀.obj M) ≫ q₂'.map (r₁'.hom.app M) ≫ r₂'.hom.app (y₁'.obj M) ≫
        F₂.map (s'.app M) ≫ F₂.map (τm.app M))
    (K : CochainComplex MR ℤ) :
    (Functor.mapHomologicalComplexCompIso e (ComplexShape.up ℤ)).inv.app
          ((F₀.mapHomologicalComplex _).obj K) ≫
        (q₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso r₁ (ComplexShape.up ℤ) ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (y₁ ⋙ F₁))
              (ComplexShape.up ℤ)).symm).hom.app K) ≫
        (Functor.mapHomologicalComplexCompIso r₂ (ComplexShape.up ℤ) ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (y₂ ⋙ F₂))
              (ComplexShape.up ℤ)).symm).hom.app ((y₁.mapHomologicalComplex _).obj K) ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex s (ComplexShape.up ℤ)).app K) =
      ((Functor.mapHomologicalComplexCompIso e' (ComplexShape.up ℤ)).inv.app
          ((F₀.mapHomologicalComplex _).obj K) ≫
        (q₂'.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((Functor.mapHomologicalComplexCompIso r₁' (ComplexShape.up ℤ) ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (y₁' ⋙ F₁'))
              (ComplexShape.up ℤ)).symm).hom.app K) ≫
        (Functor.mapHomologicalComplexCompIso r₂' (ComplexShape.up ℤ) ≪≫
            (Functor.mapHomologicalComplexCompIso (Iso.refl (y₂' ⋙ F₂))
              (ComplexShape.up ℤ)).symm).hom.app ((y₁'.mapHomologicalComplex _).obj K) ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex s' (ComplexShape.up ℤ)).app K)) ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ)).map
          ((NatTrans.mapHomologicalComplex τm (ComplexShape.up ℤ)).app K) := by
  ext n
  simpa [Functor.mapHomologicalComplexCompIso] using hmod (K.X n)

/-- **Two paths of degreewise isomorphisms, on homotopy categories.**  If the identity holds
between the functors themselves, degree by degree, it holds on homotopy categories. -/
theorem quotient_paths_eq {h h' : T} (w : h = h') (e : q₁ ⋙ q₂ ≅ Ψ h') (e' : q₁' ⋙ q₂' ≅ Ψ h)
    (r₁ : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁) (r₂ : F₁ ⋙ q₂ ≅ y₂ ⋙ F₂) (r₁' : F₀ ⋙ q₁' ≅ y₁' ⋙ F₁')
    (r₂' : F₁' ⋙ q₂' ≅ y₂' ⋙ F₂) (s : y₁ ⋙ y₂ ⟶ yc) (s' : y₁' ⋙ y₂' ⟶ yc) (τm : yc ⟶ yc)
    (τ : 𝟭 (CochainComplex MA' ℤ) ⟶ 𝟭 (CochainComplex MA' ℤ))
    (ρ₁ : (F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙
        q₁.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      y₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _)
    (ρ₂ : (F₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙
        q₂.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      y₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _)
    (ρ₁' : (F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙
        q₁'.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      y₁'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F₁'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _)
    (ρ₂' : (F₁'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙
        q₂'.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      y₂'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _)
    (hρ₁ : ∀ K, ρ₁.app K = (HomotopyCategory.quotient _ _).map
      ((Functor.mapHomologicalComplexCompIso r₁ (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (y₁ ⋙ F₁))
          (ComplexShape.up ℤ)).symm).hom.app K))
    (hρ₂ : ∀ K, ρ₂.app K = (HomotopyCategory.quotient _ _).map
      ((Functor.mapHomologicalComplexCompIso r₂ (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (y₂ ⋙ F₂))
          (ComplexShape.up ℤ)).symm).hom.app K))
    (hρ₁' : ∀ K, ρ₁'.app K = (HomotopyCategory.quotient _ _).map
      ((Functor.mapHomologicalComplexCompIso r₁' (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (y₁' ⋙ F₁'))
          (ComplexShape.up ℤ)).symm).hom.app K))
    (hρ₂' : ∀ K, ρ₂'.app K = (HomotopyCategory.quotient _ _).map
      ((Functor.mapHomologicalComplexCompIso r₂' (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (y₂' ⋙ F₂))
          (ComplexShape.up ℤ)).symm).hom.app K))
    (hτ : ∀ K, τ.app ((yc.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (NatTrans.mapHomologicalComplex τm (ComplexShape.up ℤ)).app K)
    (hmod : ∀ M, e.inv.app (F₀.obj M) ≫ q₂.map (r₁.hom.app M) ≫ r₂.hom.app (y₁.obj M) ≫
        F₂.map (s.app M) =
      (eqToHom (congrArg Ψ w.symm) : Ψ h' ⟶ Ψ h).app (F₀.obj M) ≫ e'.inv.app (F₀.obj M) ≫
        q₂'.map (r₁'.hom.app M) ≫ r₂'.hom.app (y₁'.obj M) ≫ F₂.map (s'.app M) ≫
        F₂.map (τm.app M))
    (K : CochainComplex MR ℤ) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app
          ((HomotopyCategory.quotient _ _).obj ((F₀.mapHomologicalComplex _).obj K)) ≫
        (q₂.mapHomotopyCategory (ComplexShape.up ℤ)).map (ρ₁.app K) ≫
        ρ₂.app ((y₁.mapHomologicalComplex _).obj K) ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex s (ComplexShape.up ℤ)).app K) =
      (Functor.mapHomotopyCategoryCompIso e' (ComplexShape.up ℤ) ≪≫
          eqToIso (congrArg (fun t => (Ψ t).mapHomotopyCategory (ComplexShape.up ℤ)) w)).inv.app
          ((HomotopyCategory.quotient _ _).obj ((F₀.mapHomologicalComplex _).obj K)) ≫
        (q₂'.mapHomotopyCategory (ComplexShape.up ℤ)).map (ρ₁'.app K) ≫
        ρ₂'.app ((y₁'.mapHomologicalComplex _).obj K) ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex s' (ComplexShape.up ℤ)).app K) ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _).map
          (τ.app ((yc.mapHomologicalComplex _).obj K)) := by
  subst w
  rw [hρ₁, hρ₂, hρ₁', hρ₂', hτ, Iso.trans_inv, eqToIso_refl, Iso.refl_inv, NatTrans.comp_app,
    NatTrans.id_app, Category.id_comp,
    mapHomotopyCategoryCompIso_inv_app_quotient_obj,
    mapHomotopyCategoryCompIso_inv_app_quotient_obj]
  simp only [Functor.comp_map, Functor.mapHomotopyCategory_map, ← Functor.map_comp]
  refine congrArg (HomotopyCategory.quotient V₂ (ComplexShape.up ℤ)).map ?_
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp] at hmod
  have hc := chain_paths_eq e e' r₁ r₂ r₁' r₂' s s' τm hmod K
  simp only [Category.assoc, Functor.map_comp] at hc ⊢
  exact hc

/-- `Stacks.Homology.quotient_paths_eq` with the edges given as `homotopyEdgeIso` and the
compositors of degreewise pullbacks given by equations, in the form consumed by
`Stacks.CategoryTheory.BaseChange.paths_comp_eq_trans`. -/
theorem quotient_paths_eq_of_eq {h h' : T} (w : h = h') (e : q₁ ⋙ q₂ ≅ Ψ h')
    (e' : q₁' ⋙ q₂' ≅ Ψ h)
    (r₁ : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁) (r₂ : F₁ ⋙ q₂ ≅ y₂ ⋙ F₂) (r₁' : F₀ ⋙ q₁' ≅ y₁' ⋙ F₁')
    (r₂' : F₁' ⋙ q₂' ≅ y₂' ⋙ F₂) (s : y₁ ⋙ y₂ ⟶ yc) (s' : y₁' ⋙ y₂' ⟶ yc) (τm : yc ⟶ yc)
    (τ : 𝟭 (CochainComplex MA' ℤ) ⟶ 𝟭 (CochainComplex MA' ℤ))
    (γ : q₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ q₂.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (Ψ h').mapHomotopyCategory (ComplexShape.up ℤ))
    (γ' : q₁'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        q₂'.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (Ψ h').mapHomotopyCategory (ComplexShape.up ℤ))
    (ρ₁ : (F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙
        q₁.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      y₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _)
    (ρ₂ : (F₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙
        q₂.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      y₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _)
    (ρ₁' : (F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙
        q₁'.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      y₁'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F₁'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _)
    (ρ₂' : (F₁'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙
        q₂'.mapHomotopyCategory (ComplexShape.up ℤ) ⟶
      y₂'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
        F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _)
    (hγ : γ = Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ))
    (hγ' : γ' = Functor.mapHomotopyCategoryCompIso e' (ComplexShape.up ℤ) ≪≫
      eqToIso (congrArg (fun t => (Ψ t).mapHomotopyCategory (ComplexShape.up ℤ)) w))
    (hρ₁ : ρ₁ = (homotopyEdgeIso r₁).hom) (hρ₂ : ρ₂ = (homotopyEdgeIso r₂).hom)
    (hρ₁' : ρ₁' = (homotopyEdgeIso r₁').hom) (hρ₂' : ρ₂' = (homotopyEdgeIso r₂').hom)
    (hτ : ∀ K, τ.app ((yc.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (NatTrans.mapHomologicalComplex τm (ComplexShape.up ℤ)).app K)
    (hmod : ∀ M, e.inv.app (F₀.obj M) ≫ q₂.map (r₁.hom.app M) ≫ r₂.hom.app (y₁.obj M) ≫
        F₂.map (s.app M) =
      (eqToHom (congrArg Ψ w.symm) : Ψ h' ⟶ Ψ h).app (F₀.obj M) ≫ e'.inv.app (F₀.obj M) ≫
        q₂'.map (r₁'.hom.app M) ≫ r₂'.hom.app (y₁'.obj M) ≫ F₂.map (s'.app M) ≫
        F₂.map (τm.app M))
    (K : CochainComplex MR ℤ) :
    γ.inv.app ((F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient _ _).obj K) ≫
        (q₂.mapHomotopyCategory (ComplexShape.up ℤ)).map (ρ₁.app K) ≫
        ρ₂.app ((y₁.mapHomologicalComplex _).obj K) ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex s (ComplexShape.up ℤ)).app K) =
      γ'.inv.app ((F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient _ _).obj K) ≫
        (q₂'.mapHomotopyCategory (ComplexShape.up ℤ)).map (ρ₁'.app K) ≫
        ρ₂'.app ((y₁'.mapHomologicalComplex _).obj K) ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex s' (ComplexShape.up ℤ)).app K) ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _).map
          (τ.app ((yc.mapHomologicalComplex _).obj K)) := by
  subst hγ hγ' hρ₁ hρ₂ hρ₁' hρ₂'
  exact quotient_paths_eq w e e' r₁ r₂ r₁' r₂' s s' τm τ _ _ _ _
    (homotopyEdgeIso_hom_app r₁) (homotopyEdgeIso_hom_app r₂) (homotopyEdgeIso_hom_app r₁')
    (homotopyEdgeIso_hom_app r₂') hτ hmod K

/-- `Stacks.CategoryTheory.BaseChange.paths_comp_eq_congr` for degreewise functors on homotopy
categories: two paths of derived base change isomorphisms differ by `Φ₂` of `t` as soon as the
corresponding identity `hmod` holds between the degreewise functors themselves. -/
theorem paths_comp_eq_quotient {D₀ D₁ D₁' D₂ E₀ E₁ E₁' E₂ : Type*} [Category D₀] [Category D₁]
    [Category D₁'] [Category D₂] [Category E₀] [Category E₁] [Category E₁'] [Category E₂]
    {Q₀ : CochainComplex MR ℤ ⥤ D₀} {Q₁ : CochainComplex MR' ℤ ⥤ D₁}
    {Q₁' : CochainComplex MA ℤ ⥤ D₁'} {Q₂ : CochainComplex MA' ℤ ⥤ D₂}
    {P₀ : HomotopyCategory V₀ (ComplexShape.up ℤ) ⥤ E₀}
    {P₁ : HomotopyCategory V₁ (ComplexShape.up ℤ) ⥤ E₁}
    {P₁' : HomotopyCategory V₁' (ComplexShape.up ℤ) ⥤ E₁'}
    {P₂ : HomotopyCategory V₂ (ComplexShape.up ℤ) ⥤ E₂}
    {Φ₀ : D₀ ⥤ E₀} {Φ₁ : D₁ ⥤ E₁} {Φ₁' : D₁' ⥤ E₁'} {Φ₂ : D₂ ⥤ E₂}
    {e₀ : Q₀ ⋙ Φ₀ ≅
      (F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙ P₀}
    {e₁ : Q₁ ⋙ Φ₁ ≅
      (F₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙ P₁}
    {e₁' : Q₁' ⋙ Φ₁' ≅
      (F₁'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙ P₁'}
    {e₂ : Q₂ ⋙ Φ₂ ≅
      (F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙ P₂}
    {X₁ : D₀ ⥤ D₁} {X₂ : D₁ ⥤ D₂} {X₁' : D₀ ⥤ D₁'} {X₂' : D₁' ⥤ D₂} {X : D₀ ⥤ D₂}
    {κ₁ : Q₀ ⋙ X₁ ⟶ y₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q₁}
    {κ₂ : Q₁ ⋙ X₂ ⟶ y₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q₂}
    {κ₁' : Q₀ ⋙ X₁' ⟶ y₁'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q₁'}
    {κ₂' : Q₁' ⋙ X₂' ⟶ y₂'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q₂}
    {κ : Q₀ ⋙ X ⟶ yc.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q₂}
    {ε : X₁ ⋙ X₂ ⟶ X} {ε' : X₁' ⋙ X₂' ⟶ X}
    {L₁ : E₀ ⥤ E₁} {L₂ : E₁ ⥤ E₂} {L₁' : E₀ ⥤ E₁'} {L₂' : E₁' ⥤ E₂}
    {ℓ₁ : P₀ ⋙ L₁ ⟶ q₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ P₁}
    {ℓ₂ : P₁ ⋙ L₂ ⟶ q₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ P₂}
    {ℓ₁' : P₀ ⋙ L₁' ⟶ q₁'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ P₁'}
    {ℓ₂' : P₁' ⋙ L₂' ⟶ q₂'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ P₂}
    {β₁ : Φ₀ ⋙ L₁ ≅ X₁ ⋙ Φ₁} {β₂ : Φ₁ ⋙ L₂ ≅ X₂ ⋙ Φ₂} {β₁' : Φ₀ ⋙ L₁' ≅ X₁' ⋙ Φ₁'}
    {β₂' : Φ₁' ⋙ L₂' ≅ X₂' ⋙ Φ₂}
    (Lf : T → (E₀ ⥤ E₂))
    (ℓf : ∀ t, P₀ ⋙ Lf t ⟶ (Ψ t).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ P₂)
    {h h' : T} (w : h = h') {g : L₁ ⋙ L₂ ≅ Lf h'} {g₁ : L₁' ⋙ L₂' ≅ Lf h}
    {g' : L₁' ⋙ L₂' ≅ Lf h'}
    {γ : q₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ q₂.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (Ψ h').mapHomotopyCategory (ComplexShape.up ℤ)}
    {γ₁ : q₁'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        q₂'.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (Ψ h).mapHomotopyCategory (ComplexShape.up ℤ)}
    {γ' : q₁'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙
        q₂'.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (Ψ h').mapHomotopyCategory (ComplexShape.up ℤ)}
    (e : q₁ ⋙ q₂ ≅ Ψ h') (e' : q₁' ⋙ q₂' ≅ Ψ h)
    (r₁ : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁) (r₂ : F₁ ⋙ q₂ ≅ y₂ ⋙ F₂) (r₁' : F₀ ⋙ q₁' ≅ y₁' ⋙ F₁')
    (r₂' : F₁' ⋙ q₂' ≅ y₂' ⋙ F₂) (s : y₁ ⋙ y₂ ⟶ yc) (s' : y₁' ⋙ y₂' ⟶ yc) (τm : yc ⟶ yc)
    {t : 𝟭 D₂ ⟶ 𝟭 D₂} {τ : 𝟭 (CochainComplex MA' ℤ) ⟶ 𝟭 (CochainComplex MA' ℤ)}
    (hg' : g' = g₁ ≪≫ eqToIso (congrArg Lf w))
    (hγ' : γ' = γ₁ ≪≫
      eqToIso (congrArg (fun t => (Ψ t).mapHomotopyCategory (ComplexShape.up ℤ)) w))
    (hγ : γ = Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ))
    (hγ₁ : γ₁ = Functor.mapHomotopyCategoryCompIso e' (ComplexShape.up ℤ))
    (W : MorphismProperty (CochainComplex MR ℤ)) [Q₀.IsLocalization W]
    (hX : (X ⋙ Φ₂).IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight κ Φ₂) W)
    (ht : ∀ K, e₂.inv.app K ≫ Φ₂.map (t.app (Q₂.obj K)) =
      P₂.map ((F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _).map
        (τ.app K)) ≫ e₂.inv.app K)
    (hg : ∀ M, g.hom.app (P₀.obj M) ≫ (ℓf h').app M =
      L₂.map (ℓ₁.app M) ≫ ℓ₂.app ((q₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        P₂.map (γ.hom.app M))
    (h₁ : ∀ M, g₁.hom.app (P₀.obj M) ≫ (ℓf h).app M =
      L₂'.map (ℓ₁'.app M) ≫ ℓ₂'.app ((q₁'.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        P₂.map (γ₁.hom.app M))
    (hτ : ∀ K, τ.app ((yc.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) =
      (NatTrans.mapHomologicalComplex τm (ComplexShape.up ℤ)).app K)
    (hmod : ∀ M, e.inv.app (F₀.obj M) ≫ q₂.map (r₁.hom.app M) ≫ r₂.hom.app (y₁.obj M) ≫
        F₂.map (s.app M) =
      (eqToHom (congrArg Ψ w.symm) : Ψ h' ⟶ Ψ h).app (F₀.obj M) ≫ e'.inv.app (F₀.obj M) ≫
        q₂'.map (r₁'.hom.app M) ≫ r₂'.hom.app (y₁'.obj M) ≫ F₂.map (s'.app M) ≫
        F₂.map (τm.app M))
    (hε : ∀ K, ε.app (Q₀.obj K) ≫ κ.app K =
      X₂.map (κ₁.app K) ≫ κ₂.app ((y₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        Q₂.map ((NatTrans.mapHomologicalComplex s (ComplexShape.up ℤ)).app K))
    (hβ₁ : ∀ K, β₁.hom.app (Q₀.obj K) ≫ Φ₁.map (κ₁.app K) =
      L₁.map (e₀.hom.app K) ≫ ℓ₁.app ((F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient _ _).obj K) ≫ P₁.map ((homotopyEdgeIso r₁).hom.app K) ≫
        e₁.inv.app ((y₁.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (hβ₂ : ∀ K, β₂.hom.app (Q₁.obj K) ≫ Φ₂.map (κ₂.app K) =
      L₂.map (e₁.hom.app K) ≫ ℓ₂.app ((F₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient _ _).obj K) ≫ P₂.map ((homotopyEdgeIso r₂).hom.app K) ≫
        e₂.inv.app ((y₂.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (hε' : ∀ K, ε'.app (Q₀.obj K) ≫ κ.app K =
      X₂'.map (κ₁'.app K) ≫ κ₂'.app ((y₁'.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) ≫
        Q₂.map ((NatTrans.mapHomologicalComplex s' (ComplexShape.up ℤ)).app K))
    (hβ₁' : ∀ K, β₁'.hom.app (Q₀.obj K) ≫ Φ₁'.map (κ₁'.app K) =
      L₁'.map (e₀.hom.app K) ≫ ℓ₁'.app ((F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient _ _).obj K) ≫ P₁'.map ((homotopyEdgeIso r₁').hom.app K) ≫
        e₁'.inv.app ((y₁'.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (hβ₂' : ∀ K, β₂'.hom.app (Q₁'.obj K) ≫ Φ₂.map (κ₂'.app K) =
      L₂'.map (e₁'.hom.app K) ≫ ℓ₂'.app ((F₁'.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient _ _).obj K) ≫ P₂.map ((homotopyEdgeIso r₂').hom.app K) ≫
        e₂.inv.app ((y₂'.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (N : D₀) :
    L₂.map (β₁.hom.app N) ≫ β₂.hom.app (X₁.obj N) ≫ Φ₂.map (ε.app N) =
      g.hom.app (Φ₀.obj N) ≫ g'.inv.app (Φ₀.obj N) ≫
        L₂'.map (β₁'.hom.app N) ≫ β₂'.hom.app (X₁'.obj N) ≫ Φ₂.map (ε'.app N) ≫
        Φ₂.map (t.app (X.obj N)) :=
  Stacks.CategoryTheory.BaseChange.paths_comp_eq_congr Lf
    (fun t => (Ψ t).mapHomotopyCategory (ComplexShape.up ℤ)) ℓf w hg' hγ' W hX ht hg h₁
    (fun K => quotient_paths_eq_of_eq w e e' r₁ r₂ r₁' r₂' s s' τm τ γ γ' _ _ _ _ hγ
      (hγ'.trans (by rw [hγ₁])) rfl rfl rfl rfl hτ hmod K)
    hε hβ₁ hβ₂ hε' hβ₁' hβ₂' N

section Central

variable {M₀ M₁ M₂ N₀ N₁ N₂ M₁' N₁' : Type*} [Category M₀] [Category M₁] [Category M₂]
  [Category N₀] [Category N₁] [Category N₂] [Category M₁'] [Category N₁']

/-- The natural transformation `F₀ ⋙ H ⟶ yc ⋙ F₂` along a path of two edges: the inverse of
`e : q₁ ⋙ q₂ ≅ H`, then the two edge isomorphisms, then `F₂` of `s : y₁ ⋙ y₂ ⟶ yc`. -/
def pathNatTrans {F₀ : M₀ ⥤ N₀} {F₁ : M₁ ⥤ N₁} {F₂ : M₂ ⥤ N₂} {q₁ : N₀ ⥤ N₁} {q₂ : N₁ ⥤ N₂}
    {H : N₀ ⥤ N₂} {y₁ : M₀ ⥤ M₁} {y₂ : M₁ ⥤ M₂} {yc : M₀ ⥤ M₂} (e : q₁ ⋙ q₂ ≅ H)
    (r₁ : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁) (r₂ : F₁ ⋙ q₂ ≅ y₂ ⋙ F₂) (s : y₁ ⋙ y₂ ⟶ yc) :
    F₀ ⋙ H ⟶ yc ⋙ F₂ :=
  Functor.whiskerLeft F₀ e.inv ≫ (Functor.associator _ _ _).inv ≫
    Functor.whiskerRight r₁.hom q₂ ≫ (Functor.associator _ _ _).hom ≫
    Functor.whiskerLeft y₁ r₂.hom ≫ (Functor.associator _ _ _).inv ≫ Functor.whiskerRight s F₂

theorem pathNatTrans_app {F₀ : M₀ ⥤ N₀} {F₁ : M₁ ⥤ N₁} {F₂ : M₂ ⥤ N₂} {q₁ : N₀ ⥤ N₁}
    {q₂ : N₁ ⥤ N₂} {H : N₀ ⥤ N₂} {y₁ : M₀ ⥤ M₁} {y₂ : M₁ ⥤ M₂} {yc : M₀ ⥤ M₂}
    (e : q₁ ⋙ q₂ ≅ H) (r₁ : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁) (r₂ : F₁ ⋙ q₂ ≅ y₂ ⋙ F₂) (s : y₁ ⋙ y₂ ⟶ yc)
    (M : M₀) :
    (pathNatTrans e r₁ r₂ s).app M =
      e.inv.app (F₀.obj M) ≫ q₂.map (r₁.hom.app M) ≫ r₂.hom.app (y₁.obj M) ≫ F₂.map (s.app M) := by
  simp [pathNatTrans]

/-- An identity between two paths of degreewise isomorphisms, read at an object: the form of the
hypothesis `hmod` of `Stacks.Homology.quotient_paths_eq`. -/
theorem app_eq_of_pathNatTrans_eq {T : Type*} {Ψ : T → (N₀ ⥤ N₂)} {h h' : T} (w : h = h')
    {F₀ : M₀ ⥤ N₀} {F₁ : M₁ ⥤ N₁} {F₁' : M₁' ⥤ N₁'} {F₂ : M₂ ⥤ N₂} {q₁ : N₀ ⥤ N₁}
    {q₂ : N₁ ⥤ N₂} {q₁' : N₀ ⥤ N₁'} {q₂' : N₁' ⥤ N₂} {y₁ : M₀ ⥤ M₁} {y₂ : M₁ ⥤ M₂}
    {y₁' : M₀ ⥤ M₁'} {y₂' : M₁' ⥤ M₂} {yc : M₀ ⥤ M₂}
    (e : q₁ ⋙ q₂ ≅ Ψ h') (e' : q₁' ⋙ q₂' ≅ Ψ h) (r₁ : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁)
    (r₂ : F₁ ⋙ q₂ ≅ y₂ ⋙ F₂) (r₁' : F₀ ⋙ q₁' ≅ y₁' ⋙ F₁') (r₂' : F₁' ⋙ q₂' ≅ y₂' ⋙ F₂)
    (s : y₁ ⋙ y₂ ⟶ yc) (s' : y₁' ⋙ y₂' ⟶ yc) (τm : yc ⟶ yc)
    (hpath : pathNatTrans e r₁ r₂ s =
      (Functor.whiskerLeft F₀ (eqToHom (congrArg Ψ w.symm)) ≫ pathNatTrans e' r₁' r₂' s') ≫
        Functor.whiskerRight τm F₂)
    (M : M₀) :
    e.inv.app (F₀.obj M) ≫ q₂.map (r₁.hom.app M) ≫ r₂.hom.app (y₁.obj M) ≫ F₂.map (s.app M) =
      (eqToHom (congrArg Ψ w.symm) : Ψ h' ⟶ Ψ h).app (F₀.obj M) ≫ e'.inv.app (F₀.obj M) ≫
        q₂'.map (r₁'.hom.app M) ≫ r₂'.hom.app (y₁'.obj M) ≫ F₂.map (s'.app M) ≫
        F₂.map (τm.app M) := by
  have h₀ := congrArg (fun α => NatTrans.app α M) hpath
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    pathNatTrans_app, Category.assoc] at h₀
  exact h₀

instance isIso_pathNatTrans {F₀ : M₀ ⥤ N₀} {F₁ : M₁ ⥤ N₁} {F₂ : M₂ ⥤ N₂} {q₁ : N₀ ⥤ N₁}
    {q₂ : N₁ ⥤ N₂} {H : N₀ ⥤ N₂} {y₁ : M₀ ⥤ M₁} {y₂ : M₁ ⥤ M₂} {yc : M₀ ⥤ M₂}
    (e : q₁ ⋙ q₂ ≅ H) (r₁ : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁) (r₂ : F₁ ⋙ q₂ ≅ y₂ ⋙ F₂) (s : y₁ ⋙ y₂ ⟶ yc)
    [IsIso s] : IsIso (pathNatTrans e r₁ r₂ s) := by
  unfold pathNatTrans
  infer_instance

/-- Two natural transformations `F₀ ⋙ H ⟶ yc ⋙ F₂`, the second invertible, differ by `F₂` of
an endomorphism of `yc` when `F₂` is fully faithful. -/
theorem exists_app_eq_comp_map {F₀ : M₀ ⥤ N₀} {F₂ : M₂ ⥤ N₂} {H : N₀ ⥤ N₂} {yc : M₀ ⥤ M₂}
    (Ψa Ψb : F₀ ⋙ H ⟶ yc ⋙ F₂) (hb : IsIso Ψb) (hF : F₂.FullyFaithful) :
    ∃ δ : yc ⟶ yc, ∀ M, Ψa.app M = Ψb.app M ≫ F₂.map (δ.app M) := by
  refine ⟨{ app := fun M => hF.preimage (inv (Ψb.app M) ≫ Ψa.app M)
            naturality := fun M M' φ => hF.map_injective ?_ }, fun M => ?_⟩
  · simp only [Functor.map_comp, Functor.FullyFaithful.map_preimage]
    have ha := Ψa.naturality φ
    have hb := Ψb.naturality φ
    dsimp only [Functor.comp_obj, Functor.comp_map] at ha hb
    rw [← cancel_epi (Ψb.app M), ← reassoc_of% hb, IsIso.hom_inv_id_assoc, ha]
    simp only [Category.assoc, IsIso.hom_inv_id_assoc]
  · simp only [Functor.FullyFaithful.map_preimage, IsIso.hom_inv_id_assoc]

end Central

end Stacks.Homology
