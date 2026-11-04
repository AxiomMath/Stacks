module

public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedAffineDerivedBaseChangeCompExact

/-!
# Affine base change isomorphisms compose along a triangle

For morphisms `g : U' ⟶ U` and `g₂ : U'' ⟶ U'` of the big fppf site over `S` between objects
with affine underlying schemes, the derived affine base change isomorphisms
`Lg^* Φ_R ≅ Φ_{R'}(- ⊗ᴸ_R R')` compose exactly: `Lg₂^*` of the one along `g` followed by the one
along `g₂` is the one along `g₂ ≫ g`, through the composition laws of derived pullbacks and of
derived extensions of scalars.

## Main results

* `Stacks.CategoryTheory.BaseChange.path_comp_eq_edge_congr`: a path of two derived base change
  isomorphisms against a single edge.
* `AlgebraicGeometry.Space.representedAffinePathLeft_eq_edge`: the module-level path along a
  triangle of affines is the single edge.
* `AlgebraicGeometry.Space.representedAffineToposDerivedBaseChange_comp`: the derived affine base
  change isomorphisms compose along a triangle.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.CategoryTheory.BaseChange

variable {C₀ C₁ C₂ D₀ D₁ D₂ H₀ H₁ H₂ E₀ E₁ E₂ : Type*} [Category C₀] [Category C₁]
  [Category C₂] [Category D₀] [Category D₁] [Category D₂] [Category H₀] [Category H₁]
  [Category H₂] [Category E₀] [Category E₁] [Category E₂]
  {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂} {P₀ : H₀ ⥤ E₀} {P₁ : H₁ ⥤ E₁} {P₂ : H₂ ⥤ E₂}
  {A₀ : C₀ ⥤ H₀} {A₁ : C₁ ⥤ H₁} {A₂ : C₂ ⥤ H₂} {Φ₀ : D₀ ⥤ E₀} {Φ₁ : D₁ ⥤ E₁} {Φ₂ : D₂ ⥤ E₂}
  {e₀ : Q₀ ⋙ Φ₀ ≅ A₀ ⋙ P₀} {e₁ : Q₁ ⋙ Φ₁ ≅ A₁ ⋙ P₁} {e₂ : Q₂ ⋙ Φ₂ ≅ A₂ ⋙ P₂}
  {x₁ : C₀ ⥤ C₁} {x₂ : C₁ ⥤ C₂} {x : C₀ ⥤ C₂} {X₁ : D₀ ⥤ D₁} {X₂ : D₁ ⥤ D₂} {X : D₀ ⥤ D₂}
  {κ₁ : Q₀ ⋙ X₁ ⟶ x₁ ⋙ Q₁} {κ₂ : Q₁ ⋙ X₂ ⟶ x₂ ⋙ Q₂} {κ : Q₀ ⋙ X ⟶ x ⋙ Q₂}
  {σ : x₁ ⋙ x₂ ⟶ x} {ε : X₁ ⋙ X₂ ⟶ X}
  {p₁ : H₀ ⥤ H₁} {p₂ : H₁ ⥤ H₂} {L₁ : E₀ ⥤ E₁} {L₂ : E₁ ⥤ E₂}
  {ℓ₁ : P₀ ⋙ L₁ ⟶ p₁ ⋙ P₁} {ℓ₂ : P₁ ⋙ L₂ ⟶ p₂ ⋙ P₂}
  {ρ₁ : A₀ ⋙ p₁ ⟶ x₁ ⋙ A₁} {ρ₂ : A₁ ⋙ p₂ ⟶ x₂ ⋙ A₂}
  {β₁ : Φ₀ ⋙ L₁ ≅ X₁ ⋙ Φ₁} {β₂ : Φ₁ ⋙ L₂ ≅ X₂ ⋙ Φ₂}

/-- **A path of two derived base change isomorphisms against a single edge.**  If the derived
pullbacks form a family `Lf` with comparisons `ℓf`, the path composes to the member at `s'`, the
single edge `β` is attached to the member at `s`, and the underived composite along the path is the
underived edge transported along `w : s = s'`, then so are the derived ones, as soon as `X ⋙ Φ₂` is
a left derived functor through `κ`. -/
theorem path_comp_eq_edge_congr {T : Type*} (Lf : T → (E₀ ⥤ E₂)) (pf : T → (H₀ ⥤ H₂))
    (ℓf : ∀ s, P₀ ⋙ Lf s ⟶ pf s ⋙ P₂) {s s' : T} (w : s = s')
    {g : L₁ ⋙ L₂ ≅ Lf s'} {γ : p₁ ⋙ p₂ ≅ pf s'} {β : Φ₀ ⋙ Lf s ≅ X ⋙ Φ₂}
    {ρ : A₀ ⋙ pf s ⟶ x ⋙ A₂}
    (W : MorphismProperty C₀) [Q₀.IsLocalization W]
    (hX : (X ⋙ Φ₂).IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight κ Φ₂) W)
    (hg : ∀ M, g.hom.app (P₀.obj M) ≫ (ℓf s').app M =
      L₂.map (ℓ₁.app M) ≫ ℓ₂.app (p₁.obj M) ≫ P₂.map (γ.hom.app M))
    (hρ : ∀ K, γ.inv.app (A₀.obj K) ≫ p₂.map (ρ₁.app K) ≫ ρ₂.app (x₁.obj K) ≫
        A₂.map (σ.app K) =
      (eqToIso (congrArg pf w)).inv.app (A₀.obj K) ≫ ρ.app K)
    (hε : ∀ K, ε.app (Q₀.obj K) ≫ κ.app K =
      X₂.map (κ₁.app K) ≫ κ₂.app (x₁.obj K) ≫ Q₂.map (σ.app K))
    (hβ₁ : ∀ K, β₁.hom.app (Q₀.obj K) ≫ Φ₁.map (κ₁.app K) =
      L₁.map (e₀.hom.app K) ≫ ℓ₁.app (A₀.obj K) ≫ P₁.map (ρ₁.app K) ≫
        e₁.inv.app (x₁.obj K))
    (hβ₂ : ∀ K, β₂.hom.app (Q₁.obj K) ≫ Φ₂.map (κ₂.app K) =
      L₂.map (e₁.hom.app K) ≫ ℓ₂.app (A₁.obj K) ≫ P₂.map (ρ₂.app K) ≫
        e₂.inv.app (x₂.obj K))
    (hβ : ∀ K, β.hom.app (Q₀.obj K) ≫ Φ₂.map (κ.app K) =
      (Lf s).map (e₀.hom.app K) ≫ (ℓf s).app (A₀.obj K) ≫ P₂.map (ρ.app K) ≫
        e₂.inv.app (x.obj K))
    (N : D₀) :
    L₂.map (β₁.hom.app N) ≫ β₂.hom.app (X₁.obj N) ≫ Φ₂.map (ε.app N) =
      g.hom.app (Φ₀.obj N) ≫ (eqToIso (congrArg Lf w)).inv.app (Φ₀.obj N) ≫ β.hom.app N := by
  subst w
  simp only [eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Category.id_comp] at hρ ⊢
  let γ₁ : Φ₀ ⋙ L₁ ⋙ L₂ ⟶ X ⋙ Φ₂ :=
    { app := fun N => L₂.map (β₁.hom.app N) ≫ β₂.hom.app (X₁.obj N) ≫ Φ₂.map (ε.app N)
      naturality := fun N N' u => by
        have h₁ := β₁.hom.naturality u
        have h₂ := β₂.hom.naturality (X₁.map u)
        have h₃ := ε.naturality u
        dsimp only [Functor.comp_obj, Functor.comp_map] at h₁ h₂ h₃ ⊢
        rw [← L₂.map_comp_assoc, h₁, L₂.map_comp_assoc, reassoc_of% h₂, ← Φ₂.map_comp, h₃,
          Φ₂.map_comp]
        simp only [Category.assoc] }
  let γ₂ : Φ₀ ⋙ L₁ ⋙ L₂ ⟶ X ⋙ Φ₂ := Functor.whiskerLeft Φ₀ g.hom ≫ β.hom
  have key : γ₁ = γ₂ := by
    have := hX
    refine Functor.leftDerived_ext (X ⋙ Φ₂) ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight κ Φ₂) W _ γ₁ γ₂ (NatTrans.ext (funext fun K => ?_))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp]
    have ha := path_comp_comparison hε hβ₁ hβ₂ K
    have hga : L₂.map (L₁.map (e₀.hom.app K)) ≫ L₂.map (ℓ₁.app (A₀.obj K)) ≫
        ℓ₂.app (p₁.obj (A₀.obj K)) = g.hom.app _ ≫ (Lf s).map (e₀.hom.app K) ≫
          (ℓf s).app (A₀.obj K) ≫ P₂.map (γ.inv.app (A₀.obj K)) := by
      have hn₀ := g.hom.naturality (e₀.hom.app K)
      dsimp only [Functor.comp_obj, Functor.comp_map] at hn₀ ⊢
      rw [← reassoc_of% hn₀, reassoc_of% (hg (A₀.obj K))]
      simp only [← P₂.map_comp, Iso.hom_inv_id_app, Functor.comp_obj,
        CategoryTheory.Functor.map_id, Category.comp_id]
    show (L₂.map (β₁.hom.app (Q₀.obj K)) ≫ β₂.hom.app (X₁.obj (Q₀.obj K)) ≫
        Φ₂.map (ε.app (Q₀.obj K))) ≫ Φ₂.map (κ.app K) =
      (g.hom.app (Φ₀.obj (Q₀.obj K)) ≫ β.hom.app (Q₀.obj K)) ≫ Φ₂.map (κ.app K)
    simp only [Category.assoc] at ha ⊢
    rw [ha, hβ K, reassoc_of% hga, ← P₂.map_comp_assoc]
    rw [hρ K]
  exact congrArg (fun γ => NatTrans.app γ N) key

end Stacks.CategoryTheory.BaseChange

namespace Stacks.Homology

variable {MR MR' MA' V₀ V₁ V₂ T : Type*} [Category MR] [Category MR'] [Category MA']
  [Category V₀] [Category V₁] [Category V₂] [Preadditive MR] [Preadditive MR'] [Preadditive MA']
  [Preadditive V₀] [Preadditive V₁] [Preadditive V₂]
  {F₀ : MR ⥤ V₀} {F₁ : MR' ⥤ V₁} {F₂ : MA' ⥤ V₂} [F₀.Additive] [F₁.Additive] [F₂.Additive]
  {q₁ : V₀ ⥤ V₁} {q₂ : V₁ ⥤ V₂} [q₁.Additive] [q₂.Additive]
  {y₁ : MR ⥤ MR'} {y₂ : MR' ⥤ MA'} {yc : MR ⥤ MA'} [y₁.Additive] [y₂.Additive] [yc.Additive]
  [(y₁ ⋙ F₁).Additive] [(y₂ ⋙ F₂).Additive] [(yc ⋙ F₂).Additive]
  {Ψ : T → (V₀ ⥤ V₂)} [∀ t, (Ψ t).Additive]

/-- **A path of two degreewise isomorphisms against a single one, on complexes.** -/
theorem chain_path_eq_edge {H : V₀ ⥤ V₂} [H.Additive] (e : q₁ ⋙ q₂ ≅ H)
    (r₁ : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁) (r₂ : F₁ ⋙ q₂ ≅ y₂ ⋙ F₂) (s : y₁ ⋙ y₂ ⟶ yc)
    (r : F₀ ⋙ H ≅ yc ⋙ F₂)
    (hmod : ∀ M, e.inv.app (F₀.obj M) ≫ q₂.map (r₁.hom.app M) ≫ r₂.hom.app (y₁.obj M) ≫
        F₂.map (s.app M) = r.hom.app M)
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
      (Functor.mapHomologicalComplexCompIso r (ComplexShape.up ℤ) ≪≫
        (Functor.mapHomologicalComplexCompIso (Iso.refl (yc ⋙ F₂))
          (ComplexShape.up ℤ)).symm).hom.app K := by
  ext n
  simpa [Functor.mapHomologicalComplexCompIso] using hmod (K.X n)

/-- **A path of two degreewise isomorphisms against a single one, on homotopy categories.**  If
the identity holds between the functors themselves, degree by degree, it holds on homotopy
categories. -/
theorem quotient_path_eq_edge {h h' : T} (w : h = h') (e : q₁ ⋙ q₂ ≅ Ψ h')
    (r₁ : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁) (r₂ : F₁ ⋙ q₂ ≅ y₂ ⋙ F₂) (s : y₁ ⋙ y₂ ⟶ yc)
    (r : F₀ ⋙ Ψ h ≅ yc ⋙ F₂)
    (hmod : ∀ M, e.inv.app (F₀.obj M) ≫ q₂.map (r₁.hom.app M) ≫ r₂.hom.app (y₁.obj M) ≫
        F₂.map (s.app M) =
      (eqToHom (congrArg Ψ w.symm) : Ψ h' ⟶ Ψ h).app (F₀.obj M) ≫ r.hom.app M)
    (K : CochainComplex MR ℤ) :
    (Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ)).inv.app
          ((HomotopyCategory.quotient _ _).obj ((F₀.mapHomologicalComplex _).obj K)) ≫
        (q₂.mapHomotopyCategory (ComplexShape.up ℤ)).map ((homotopyEdgeIso r₁).hom.app K) ≫
        (homotopyEdgeIso r₂).hom.app ((y₁.mapHomologicalComplex _).obj K) ≫
        (F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _).map
          ((NatTrans.mapHomologicalComplex s (ComplexShape.up ℤ)).app K) =
      (eqToIso (congrArg (fun t => (Ψ t).mapHomotopyCategory (ComplexShape.up ℤ)) w)).inv.app
          ((HomotopyCategory.quotient _ _).obj ((F₀.mapHomologicalComplex _).obj K)) ≫
        (homotopyEdgeIso r).hom.app K := by
  subst w
  simp only [eqToHom_refl, NatTrans.id_app, Category.id_comp] at hmod
  rw [eqToIso_refl, Iso.refl_inv, NatTrans.id_app, Category.id_comp, homotopyEdgeIso_hom_app,
    homotopyEdgeIso_hom_app, homotopyEdgeIso_hom_app,
    mapHomotopyCategoryCompIso_inv_app_quotient_obj]
  simp only [Functor.comp_map]
  refine congrArg (HomotopyCategory.quotient V₂ (ComplexShape.up ℤ)).map ?_
  exact chain_path_eq_edge e r₁ r₂ s r hmod K

/-- `Stacks.CategoryTheory.BaseChange.path_comp_eq_edge_congr` for degreewise functors on
homotopy categories: a path of two derived base change isomorphisms is the single one, as soon as
the corresponding identity `hmod` holds between the degreewise functors themselves. -/
theorem path_comp_eq_edge_quotient {D₀ D₁ D₂ E₀ E₁ E₂ : Type*} [Category D₀] [Category D₁]
    [Category D₂] [Category E₀] [Category E₁] [Category E₂]
    {Q₀ : CochainComplex MR ℤ ⥤ D₀} {Q₁ : CochainComplex MR' ℤ ⥤ D₁}
    {Q₂ : CochainComplex MA' ℤ ⥤ D₂}
    {P₀ : HomotopyCategory V₀ (ComplexShape.up ℤ) ⥤ E₀}
    {P₁ : HomotopyCategory V₁ (ComplexShape.up ℤ) ⥤ E₁}
    {P₂ : HomotopyCategory V₂ (ComplexShape.up ℤ) ⥤ E₂}
    {Φ₀ : D₀ ⥤ E₀} {Φ₁ : D₁ ⥤ E₁} {Φ₂ : D₂ ⥤ E₂}
    {e₀ : Q₀ ⋙ Φ₀ ≅
      (F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙ P₀}
    {e₁ : Q₁ ⋙ Φ₁ ≅
      (F₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙ P₁}
    {e₂ : Q₂ ⋙ Φ₂ ≅
      (F₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ HomotopyCategory.quotient _ _) ⋙ P₂}
    {X₁ : D₀ ⥤ D₁} {X₂ : D₁ ⥤ D₂} {X : D₀ ⥤ D₂}
    {κ₁ : Q₀ ⋙ X₁ ⟶ y₁.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q₁}
    {κ₂ : Q₁ ⋙ X₂ ⟶ y₂.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q₂}
    {κ : Q₀ ⋙ X ⟶ yc.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ Q₂}
    {ε : X₁ ⋙ X₂ ⟶ X} {L₁ : E₀ ⥤ E₁} {L₂ : E₁ ⥤ E₂}
    {ℓ₁ : P₀ ⋙ L₁ ⟶ q₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ P₁}
    {ℓ₂ : P₁ ⋙ L₂ ⟶ q₂.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ P₂}
    {β₁ : Φ₀ ⋙ L₁ ≅ X₁ ⋙ Φ₁} {β₂ : Φ₁ ⋙ L₂ ≅ X₂ ⋙ Φ₂}
    (Lf : T → (E₀ ⥤ E₂))
    (ℓf : ∀ t, P₀ ⋙ Lf t ⟶ (Ψ t).mapHomotopyCategory (ComplexShape.up ℤ) ⋙ P₂)
    {h h' : T} (w : h = h') {g : L₁ ⋙ L₂ ≅ Lf h'} {β : Φ₀ ⋙ Lf h ≅ X ⋙ Φ₂}
    {γ : q₁.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ q₂.mapHomotopyCategory (ComplexShape.up ℤ) ≅
      (Ψ h').mapHomotopyCategory (ComplexShape.up ℤ)}
    (e : q₁ ⋙ q₂ ≅ Ψ h') (r₁ : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁) (r₂ : F₁ ⋙ q₂ ≅ y₂ ⋙ F₂)
    (s : y₁ ⋙ y₂ ⟶ yc) (r : F₀ ⋙ Ψ h ≅ yc ⋙ F₂)
    (hγ : γ = Functor.mapHomotopyCategoryCompIso e (ComplexShape.up ℤ))
    (W : MorphismProperty (CochainComplex MR ℤ)) [Q₀.IsLocalization W]
    (hX : (X ⋙ Φ₂).IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight κ Φ₂) W)
    (hg : ∀ M, g.hom.app (P₀.obj M) ≫ (ℓf h').app M =
      L₂.map (ℓ₁.app M) ≫ ℓ₂.app ((q₁.mapHomotopyCategory (ComplexShape.up ℤ)).obj M) ≫
        P₂.map (γ.hom.app M))
    (hmod : ∀ M, e.inv.app (F₀.obj M) ≫ q₂.map (r₁.hom.app M) ≫ r₂.hom.app (y₁.obj M) ≫
        F₂.map (s.app M) =
      (eqToHom (congrArg Ψ w.symm) : Ψ h' ⟶ Ψ h).app (F₀.obj M) ≫ r.hom.app M)
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
    (hβ : ∀ K, β.hom.app (Q₀.obj K) ≫ Φ₂.map (κ.app K) =
      (Lf h).map (e₀.hom.app K) ≫ (ℓf h).app ((F₀.mapHomologicalComplex (ComplexShape.up ℤ) ⋙
          HomotopyCategory.quotient _ _).obj K) ≫ P₂.map ((homotopyEdgeIso r).hom.app K) ≫
        e₂.inv.app ((yc.mapHomologicalComplex (ComplexShape.up ℤ)).obj K))
    (N : D₀) :
    L₂.map (β₁.hom.app N) ≫ β₂.hom.app (X₁.obj N) ≫ Φ₂.map (ε.app N) =
      g.hom.app (Φ₀.obj N) ≫ (eqToIso (congrArg Lf w)).inv.app (Φ₀.obj N) ≫ β.hom.app N := by
  subst hγ
  refine Stacks.CategoryTheory.BaseChange.path_comp_eq_edge_congr Lf
    (fun t => (Ψ t).mapHomotopyCategory (ComplexShape.up ℤ)) ℓf w W hX hg ?_ hε hβ₁ hβ₂ hβ N
  intro K
  exact quotient_path_eq_edge w e r₁ r₂ s r hmod K

section Edge

variable {M₀ M₁ M₂ N₀ N₁ N₂ : Type*} [Category M₀] [Category M₁] [Category M₂]
  [Category N₀] [Category N₁] [Category N₂]

/-- An identity between a path of degreewise isomorphisms and a single one transported along an
equality of indices, read at an object: the form of the hypothesis `hmod` of
`Stacks.Homology.quotient_path_eq_edge`. -/
theorem app_eq_of_pathNatTrans_eq_edge {T : Type*} {Ψ : T → (N₀ ⥤ N₂)} {h h' : T} (w : h = h')
    {F₀ : M₀ ⥤ N₀} {F₁ : M₁ ⥤ N₁} {F₂ : M₂ ⥤ N₂} {q₁ : N₀ ⥤ N₁} {q₂ : N₁ ⥤ N₂}
    {y₁ : M₀ ⥤ M₁} {y₂ : M₁ ⥤ M₂} {yc : M₀ ⥤ M₂} {e : q₁ ⋙ q₂ ≅ Ψ h'}
    {r₁ : F₀ ⋙ q₁ ≅ y₁ ⋙ F₁} {r₂ : F₁ ⋙ q₂ ≅ y₂ ⋙ F₂} {s : y₁ ⋙ y₂ ⟶ yc}
    {r : F₀ ⋙ Ψ h ≅ yc ⋙ F₂}
    (hpath : pathNatTrans e r₁ r₂ s =
      Functor.whiskerLeft F₀ (eqToHom (congrArg Ψ w.symm)) ≫ r.hom) (M : M₀) :
    e.inv.app (F₀.obj M) ≫ q₂.map (r₁.hom.app M) ≫ r₂.hom.app (y₁.obj M) ≫ F₂.map (s.app M) =
      (eqToHom (congrArg Ψ w.symm) : Ψ h' ⟶ Ψ h).app (F₀.obj M) ≫ r.hom.app M := by
  have h₀ := congrArg (fun α => NatTrans.app α M) hpath
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, pathNatTrans_app] at h₀
  exact h₀

end Edge

end Stacks.Homology

namespace AlgebraicGeometry.Space

open Stacks.Sheaves.RingedToposModules

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section Triangle

/- The sheafification of the small étale sites, found first, so that the categories of modules
below are formed without a search through the other sheafification instances. -/
attribute [local instance 5000] SmallEtale.instHasSheafify SmallEtale.instWEqualsLocallyBijective

variable {U U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (g : U' ⟶ U) (g₂ : U'' ⟶ U')

/-- The module-level comparison along the single edge `g₂ ≫ g`, transported to the composite of
the represented maps. -/
def representedAffineEdge :
    representedAffineToposAssociated B S hS U ⋙
      Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
        (X := smallEtaleRingedTopos B S hS _) (Y := smallEtaleRingedTopos B S hS _)
        (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS g₂ ≫ representedSpaceMap B S hS g)).toModulesHom ⟶
      ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom ⋙
        representedAffineToposAssociated B S hS U'' :=
  Functor.whiskerLeft (representedAffineToposAssociated B S hS U)
      (eqToHom (congrArg (smallEtaleModulePullbackFamily B S hS _ _)
        (representedSpaceMap_comp B S hS g₂ g))) ≫
    (representedAffineToposPullbackIso B S hS (g₂ ≫ g)).hom

/-- The comparison `representedAffineEdge` along `g₂ ≫ g` is an isomorphism. -/
instance isIso_representedAffineEdge : IsIso (representedAffineEdge B S hS g g₂) :=
  @IsIso.comp_isIso _ _ _ _ _ _ _
    (Functor.isoWhiskerLeft (representedAffineToposAssociated B S hS U)
      (eqToIso (congrArg (smallEtaleModulePullbackFamily B S hS _ _)
        (representedSpaceMap_comp B S hS g₂ g)))).isIso_hom
    (representedAffineToposPullbackIso B S hS (g₂ ≫ g)).isIso_hom

/-- The path through `U'` and the single edge differ by a scalar. -/
theorem exists_representedAffinePathLeft_eq_edge :
    ∃ c : Γ((BigFppfOver.toScheme B S hS).obj U'', ⊤),
      ∀ M, (representedAffinePathLeft B S hS g g₂).app M =
        (representedAffineEdge B S hS g g₂).app M ≫
          (representedAffineToposAssociated B S hS U'').map (c • 𝟙 _) := by
  obtain ⟨δ, hδ⟩ := Stacks.Homology.exists_app_eq_comp_map
    (F₀ := representedAffineToposAssociated B S hS U)
    (F₂ := representedAffineToposAssociated B S hS U'')
    (H := Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
      (X := smallEtaleRingedTopos B S hS _)
      (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS
        (representedSpaceMap B S hS g₂ ≫ representedSpaceMap B S hS g)).toModulesHom)
    (yc := ModuleCat.extendScalars.{u, u, u} (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom)
    (representedAffinePathLeft B S hS g g₂) (representedAffineEdge B S hS g g₂)
    (isIso_representedAffineEdge B S hS g g₂)
    (representedAffineToposAssociatedFullyFaithful B S hS U'')
  obtain ⟨c, hc⟩ := ModuleCat.ExtendScalars.natTrans_app_eq_smul
    (P := (⊤ : ObjectProperty (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))))
    trivial (Functor.whiskerLeft (⊤ : ObjectProperty _).ι δ)
  exact ⟨c, fun M => (hδ M).trans (congrArg (CategoryStruct.comp
    ((representedAffineEdge B S hS g g₂).app M))
    (congrArg (representedAffineToposAssociated B S hS U'').map (hc ⟨M, trivial⟩)))⟩

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj U')] in
/-- **The single edge at the ring of `U` is the trivialization.** -/
theorem representedAffineEdge_app_self :
    (representedAffineEdge B S hS g g₂).app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ≫
      (representedAffineToposAssociated B S hS U'').map
        (ModuleCat.ExtendScalars.objSelfIso
          (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom).hom =
      (Stacks.Sheaves.RingedToposModules.RingedToposHom.pullbackModules
          (X := smallEtaleRingedTopos B S hS _)
          (Y := smallEtaleRingedTopos B S hS _) (smallEtaleRingedToposHom B S hS
            (representedSpaceMap B S hS g₂ ≫ representedSpaceMap B S hS g)).toModulesHom).map
          (representedAffineToposObjUnitIso B S hS U).hom ≫
        (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS
          (representedSpaceMap B S hS g₂ ≫ representedSpaceMap B S hS g)).toModulesHom).inv ≫
        (representedAffineToposObjUnitIso B S hS U'').inv :=
  Stacks.Homology.app_comp_eq_of_whiskerLeft_eqToHom
    (Ψ := smallEtaleModulePullbackFamily B S hS _ _)
    (representedSpaceMap_comp B S hS g₂ g)
    (representedAffineToposPullbackIso B S hS (g₂ ≫ g)).hom
    (representedAffineEdge B S hS g g₂) rfl _ _
    (representedAffineToposObjUnitIso B S hS U)
    (fun t => (pullbackModulesObjUnitIso (smallEtaleRingedToposHom B S hS t).toModulesHom).inv)
    (representedAffineToposObjUnitIso B S hS U'').inv
    (representedAffineToposPullbackIso_hom_app_self B S hS (g₂ ≫ g))

/-- **The module-level path along a triangle of affines is the single edge.** -/
theorem representedAffinePathLeft_eq_edge :
    representedAffinePathLeft B S hS g g₂ = representedAffineEdge B S hS g g₂ := by
  obtain ⟨c, hc⟩ := exists_representedAffinePathLeft_eq_edge B S hS g g₂
  have hRi : IsIso ((representedAffineEdge B S hS g g₂).app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :=
    @NatIso.isIso_app_of_isIso _ _ _ _ _ _ _ (isIso_representedAffineEdge B S hS g g₂)
      (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
        Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))
  have h₁ : (representedAffineEdge B S hS g g₂).app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ≫
      (representedAffineToposAssociated B S hS U'').map (c • 𝟙 _) ≫
        (representedAffineToposAssociated B S hS U'').map
          (ModuleCat.ExtendScalars.objSelfIso
            (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom).hom =
      (representedAffineEdge B S hS g g₂).app
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)) ≫
        (representedAffineToposAssociated B S hS U'').map
          (ModuleCat.ExtendScalars.objSelfIso
            (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom).hom :=
    (Category.assoc _ _ _).symm.trans ((eq_whisker (hc _) _).symm.trans
      ((representedAffinePathLeft_app_self B S hS g g₂).trans
        (representedAffineEdge_app_self B S hS g g₂).symm))
  have h₂ := (@cancel_epi _ _ _ _ _ _ (@IsIso.epi_of_iso _ _ _ _ _ hRi) _ _).1 h₁
  have h₃ : c • 𝟙 ((ModuleCat.extendScalars.{u, u, u}
      (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom).obj
        (ModuleCat.of Γ((BigFppfOver.toScheme B S hS).obj U, ⊤)
          Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) = 𝟙 _ := by
    refine (Iso.cancel_iso_hom_right _ _
      (ModuleCat.ExtendScalars.objSelfIso
        (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom)).1 ?_
    apply (representedAffineToposAssociatedFullyFaithful B S hS U'').map_injective
    rwa [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp,
      CategoryTheory.Functor.map_id, Category.id_comp]
  obtain rfl := ModuleCat.ExtendScalars.eq_one_of_smul_id_eq_id _ h₃
  refine NatTrans.ext (funext fun M => (hc M).trans ?_)
  rw [one_smul, CategoryTheory.Functor.map_id]
  exact Category.comp_id _

end Triangle

section DerivedTriangle

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance 10000] HasDerivedCategory.standard

/- The filtered colimits used to form the étale sheafification, through Mathlib's instance, so that
the categories of `𝒪`-modules below are spelled as in the files of the derived pullback. -/
attribute [local instance 20000] AddCommGrpCat.FilteredColimits.forget_preservesFilteredColimits

attribute [local instance] additive_extendScalars_representedAffineRingHom
  additive_pullbackModules_representedSpaceMap

attribute [local instance 6000] preadditive_smallEtaleModules

variable {U U' U'' : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U')]
  [IsAffine ((BigFppfOver.toScheme B S hS).obj U'')] (g : U' ⟶ U) (g₂ : U'' ⟶ U')

/-- **The affine base change isomorphisms compose along a triangle**: `Lg₂^*` of the derived base
change isomorphism along `g`, followed by the one along `g₂` and the composition law of derived
extensions of scalars, is the one along `g₂ ≫ g`, through the composition law of derived
pullbacks. -/
theorem representedAffineToposDerivedBaseChange_comp
    (N : DerivedCategory (ModuleCat.{u} Γ((BigFppfOver.toScheme B S hS).obj U, ⊤))) :
    (smallEtaleDerivedModulePullback B S hS (representedSpaceMap B S hS g₂)).map
          ((representedAffineToposDerivedBaseChangeIso B S hS g).hom.app N) ≫
        (representedAffineToposDerivedBaseChangeIso B S hS g₂).hom.app
          ((representedAffineDerivedExtension B S hS g).functor.obj N) ≫
        (representedAffineToposDerivedAssociated B S hS U'').map
          ((RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
              (representedAffineCommRingCatHom B S hS g).hom
              (representedAffineCommRingCatHom B S hS g₂).hom
              (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
              (representedAffineRingHom_comp B S hS g₂ g).symm).hom.app N) =
      (smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₂)
          (representedSpaceMap B S hS g)).hom.app
          ((representedAffineToposDerivedAssociated B S hS U).obj N) ≫
        (eqToIso (congrArg (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
          (representedSpaceMap_comp B S hS g₂ g).symm)).inv.app
          ((representedAffineToposDerivedAssociated B S hS U).obj N) ≫
        (representedAffineToposDerivedBaseChangeIso B S hS (g₂ ≫ g)).hom.app N := by
  have : ∀ t : (⟨yoneda.obj U'', isAlgebraicSpace_yoneda B S hS U''⟩ : AlgebraicSpaces B S hS) ⟶
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩,
      (smallEtaleModulePullbackFamily B S hS _ _ t).Additive := fun t =>
    additive_smallEtaleModulePullbackFamily B S hS _ _ t
  exact Stacks.Homology.path_comp_eq_edge_quotient
    (Ψ := smallEtaleModulePullbackFamily B S hS ⟨yoneda.obj U'', isAlgebraicSpace_yoneda B S hS U''⟩
      ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
    (fun f ↦ smallEtaleDerivedModulePullback B S hS f)
    (fun f ↦ smallEtaleDerivedModulePullbackComparison B S hS f)
    (representedSpaceMap_comp B S hS g₂ g).symm
    (smallEtaleModulePullbackCompIso B S hS (representedSpaceMap B S hS g₂)
      (representedSpaceMap B S hS g))
    (representedAffineToposPullbackIso B S hS g) (representedAffineToposPullbackIso B S hS g₂)
    (RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u, u, u, u}
      (representedAffineCommRingCatHom B S hS g).hom (representedAffineCommRingCatHom B S hS g₂).hom
      (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
      (representedAffineRingHom_comp B S hS g₂ g).symm)
    (representedAffineToposPullbackIso B S hS (g₂ ≫ g))
    (smallEtaleUnderivedPullbackCompIso_eq B S hS _ _)
    (Q₀ := DerivedCategory.Q) (P₀ := DerivedCategory.Qh)
    (e₀ := representedAffineToposDerivedFactors B S hS U)
    (e₁ := representedAffineToposDerivedFactors B S hS U')
    (e₂ := representedAffineToposDerivedFactors B S hS U'')
    (κ₁ := (representedAffineDerivedExtension B S hS g).comparison)
    (κ₂ := (representedAffineDerivedExtension B S hS g₂).comparison)
    (κ := (representedAffineDerivedExtension B S hS (g₂ ≫ g)).comparison)
    (ℓ₁ := smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g))
    (ℓ₂ := smallEtaleDerivedModulePullbackComparison B S hS (representedSpaceMap B S hS g₂))
    (β₁ := representedAffineToposDerivedBaseChangeIso B S hS g)
    (β₂ := representedAffineToposDerivedBaseChangeIso B S hS g₂)
    (β := representedAffineToposDerivedBaseChangeIso B S hS (g₂ ≫ g))
    (g := smallEtaleDerivedModulePullbackCompIso B S hS (representedSpaceMap B S hS g₂)
      (representedSpaceMap B S hS g))
    (γ := smallEtaleUnderivedPullbackCompIso B S hS (representedSpaceMap B S hS g₂)
      (representedSpaceMap B S hS g))
    (ε := (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq
              (representedAffineCommRingCatHom B S hS g).hom
              (representedAffineCommRingCatHom B S hS g₂).hom
              (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
              (representedAffineRingHom_comp B S hS g₂ g).symm).hom)
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ))
    (isLeftDerivedFunctor_representedAffineToposDerivedExtension_comp B S hS (g₂ ≫ g))
    (smallEtaleDerivedModulePullbackCompIso_hom_app_comparison B S hS
      (representedSpaceMap B S hS g₂) (representedSpaceMap B S hS g))
    (Stacks.Homology.app_eq_of_pathNatTrans_eq_edge (representedSpaceMap_comp B S hS g₂ g).symm
      (Ψ := smallEtaleModulePullbackFamily B S hS
        ⟨yoneda.obj U'', isAlgebraicSpace_yoneda B S hS U''⟩
        ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (e := smallEtaleModulePullbackCompIso B S hS (representedSpaceMap B S hS g₂)
        (representedSpaceMap B S hS g))
      (r₁ := representedAffineToposPullbackIso B S hS g)
      (r₂ := representedAffineToposPullbackIso B S hS g₂)
      (s := RingTheory.TorIndependence.extendScalarsCompInvOfEq.{u, u, u, u}
        (representedAffineCommRingCatHom B S hS g).hom
        (representedAffineCommRingCatHom B S hS g₂).hom
        (representedAffineCommRingCatHom B S hS (g₂ ≫ g)).hom
        (representedAffineRingHom_comp B S hS g₂ g).symm)
      (r := representedAffineToposPullbackIso B S hS (g₂ ≫ g))
      (representedAffinePathLeft_eq_edge B S hS g g₂))
    (RingTheory.TorIndependence.totalDerivedExtensionScalarsCompOfEq_hom_app_comparison _ _ _ _)
    (representedAffineToposDerivedBaseChangeIso_hom_app_comparison B S hS g)
    (representedAffineToposDerivedBaseChangeIso_hom_app_comparison B S hS g₂)
    (representedAffineToposDerivedBaseChangeIso_hom_app_comparison B S hS (g₂ ≫ g)) N

end DerivedTriangle

end AlgebraicGeometry.Space

end
