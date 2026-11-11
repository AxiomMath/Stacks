module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.UnboundedCompositionIsoIndependence
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.CompositionIsoIndependence

/-!
# The isomorphisms of [Stacks, Tag 0F7J] on `D(X_étale, Λ)` do not depend on the compactification
of `g`

Let `Λ` be a torsion ring and let `f : X ⟶ Y`, `g : Y ⟶ Z` be separated morphisms of finite type
of quasi-compact and quasi-separated schemes. The isomorphism `R(g ∘ f)_! ≅ Rg_! ∘ Rf_!` on
unbounded derived categories, `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso`, is
built from a compactification `i : Y ⟶ Ȳ` of `g`. Along the comparisons of [Stacks, Tag 0F7I] it
does not depend on it, as the proof of [Stacks, Tag 0F7J] asserts.

For a morphism `ψ : Ȳ ⟶ Ȳ'` of compactifications of `g` and a compactification `X̄` of `X` over
`Ȳ`, read over `Ȳ'` through `ψ`, the comparison is a statement in `D(Ȳ')` about the maps of
[Stacks, Tag 0F7B] of the squares `X̄ ×_Ȳ Y ⟶ X̄` over `Y ⟶ Ȳ` and `X̄ ×_Ȳ' Y ⟶ X̄` over
`Y ⟶ Ȳ'`, the maps of [Stacks, Tag 0F7G] along `ψ`, along `X̄ ×_Ȳ Y ⟶ X̄ ×_Ȳ' Y` and along the
identity of `X̄`, and the map of the square `X̄ ×_Ȳ Y ⟶ X̄` over `X̄ ×_Ȳ' Y ⟶ X̄`, whose left side
is a proper open immersion. All of them are maps of squares of sheaves pinned by `ε : j_! ⟶ j_*`
(`Stacks.EtaleCohomology.IsExtensionByZeroBaseChange`), and the identity follows from their
vertical and horizontal pastings ([Stacks, Tags 0F7C and 0F7D]).

## Main results

* `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedLerayIso_id_left` and
  `Stacks.EtaleCohomology.etaleModuleDerivedDirectImageUnboundedLerayIso_id_right_hom_app`: the
  unit laws of the unbounded Leray isomorphisms.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso_hom_app_of_hom`: along a morphism of
  compactifications of `g`.
* `Stacks.EtaleCohomology.derivedLowerShriekUnboundedCompIso_hom_app_second`: for two arbitrary
  compactifications of `g`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

attribute [local instance high] CompactificationOf.etale_restrictBaseι
  CompactificationOf.etale_overBar_immersion

variable (Λ : Type) [Ring Λ] (hΛ : ∃ m : ℕ, 0 < m ∧ (m : Λ) = 0)

/-! ### The unit laws of the unbounded Leray isomorphisms -/

section LerayUnit

/-- Cancelling an epimorphism through two naturality squares, over plain objects. -/
private lemma faithful_chain {𝒞 : Type*} [Category* 𝒞] {A B A' B' : 𝒞} (Rx Ry : A' ⟶ B')
    (eA : A' ⟶ A) (eB : B' ⟶ B) (x y : A ⟶ B) [Epi eA] (n1 : Rx ≫ eB = eA ≫ x)
    (n2 : Ry ≫ eB = eA ≫ y) (h : Rx = Ry) : x = y := by
  rw [← cancel_epi eA, ← n1, ← n2, h]

/-- The unbounded Leray isomorphism is the composition isomorphism
`etaleModuleDerivedDirectImageUnboundedDerivedCompIso`: both are pinned by the iterated
derivation unit. -/
theorem etaleModuleDerivedDirectImageUnboundedLerayIso_hom_eq_derivedCompIso {X Y Z : Scheme.{u}}
    (f : X ⟶ Y) (g : Y ⟶ Z) (fg : X ⟶ Z) (hfg : fg = f ≫ g) :
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ f g fg hfg).hom =
      (etaleModuleDerivedDirectImageUnboundedDerivedCompIso.{u, 0} Λ f g fg hfg).hom := by
  refine Functor.rightDerived_ext _ (etaleModuleDerivedDirectImageUnboundedUnit.{u, 0} Λ fg)
    (HomologicalComplex.quasiIso _ (ComplexShape.up ℤ)) _ _ _ (NatTrans.ext (funext fun K => ?_))
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app]
  rw [etaleModuleDerivedDirectImageUnboundedLerayIso_hom_fac,
    etaleModuleDerivedDirectImageUnboundedDerivedCompIso_hom_fac_app]

/-- **The left unit law of the unbounded Leray isomorphisms**: `Rg_* ≅ R(𝟙)_* ⋙ Rg_*` is `Rg_*`
of `𝟭 ≅ R(𝟙)_*`. -/
theorem etaleModuleDerivedDirectImageUnboundedLerayIso_id_left {X Y : Scheme.{u}} (g : X ⟶ Y)
    (hg : g = 𝟙 X ≫ g) :
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (𝟙 X) g g hg).hom =
      (Functor.leftUnitor _).inv ≫
        Functor.whiskerRight (etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ X).inv
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ g) := by
  rw [etaleModuleDerivedDirectImageUnboundedLerayIso_hom_eq_derivedCompIso]
  exact etaleModuleDerivedDirectImageUnboundedDerivedCompIso_id_left Λ g hg

/-- **The right unit law of the unbounded Leray isomorphisms**: `Rq_* ≅ Rq_* ⋙ R(𝟙)_*` is
`𝟭 ≅ R(𝟙)_*` at `Rq_*`. It follows from the left unit law and associativity for `q, 𝟙, 𝟙`,
`R(𝟙)_*` being faithful. -/
theorem etaleModuleDerivedDirectImageUnboundedLerayIso_id_right_hom_app {X Y : Scheme.{u}}
    (q : X ⟶ Y) (h : q = q ≫ 𝟙 Y) (M : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ q (𝟙 Y) q h).hom.app M =
      (etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ Y).inv.app
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ q).obj M) := by
  have A := etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app Λ q (𝟙 Y) (𝟙 Y) q h (𝟙 Y)
    (Category.comp_id _).symm q h h M
  have hL := NatTrans.congr_app (etaleModuleDerivedDirectImageUnboundedLerayIso_id_left Λ (𝟙 Y)
    (Category.comp_id _).symm) ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ q).obj M)
  simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Category.id_comp] at hL
  have hmap : (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (𝟙 Y)).map
      ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ q (𝟙 Y) q h).hom.app M) =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (𝟙 Y)).map
        ((etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ Y).inv.app
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ q).obj M)) :=
    ((cancel_epi _).mp A).trans hL
  have n1 := (etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ Y).hom.naturality
    ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ q (𝟙 Y) q h).hom.app M)
  have n2 := (etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ Y).hom.naturality
    ((etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ Y).inv.app
      ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ q).obj M))
  simp only [Functor.id_map] at n1 n2
  exact faithful_chain _ _ _ _ _ _ n1 n2 hmap

end LerayUnit

/-! ### Maps of squares on sheaves -/

/-- The map `θ̃_ψ` of the square `j ≫ ψ̄ = 𝟙 ≫ k` is pinned by `ε`. -/
theorem isExtensionByZeroBaseChange_refinementSquareIso {X Y : Scheme.{u}} {f : X ⟶ Y}
    {j k : CompactificationOf (Over.mk f)} (ψ : j ⟶ k) :
    IsExtensionByZeroBaseChange Λ k.immersion (CompactificationOf.immersion_comp_map ψ).symm
      (Category.id_comp k.immersion).symm (refinementSquareIso Λ ψ).hom := by
  rw [refinementSquareIso_hom]
  exact isExtensionByZeroBaseChange_etaleModuleRefinementSquare Λ _

/-- The vertical pasting of two isomorphisms of squares satisfies the pasting identity. -/
lemma etaleModuleSquareVerticalPaste_paste {P T Y S Y₂ S₂ : Scheme.{u}}
    {b : P ⟶ T} {i : Y ⟶ S} {m : Y₂ ⟶ S₂} [IsOpenImmersion b] [IsOpenImmersion i]
    [IsOpenImmersion m] {f' : P ⟶ Y} {fb : T ⟶ S} {g' : Y ⟶ Y₂} {gb : S ⟶ S₂}
    {pg : P ⟶ Y₂} {pf : T ⟶ S₂} (hpg : pg = f' ≫ g') (hpf : pf = fb ≫ gb)
    (μ₁ : etaleModuleDirectImage.{u, 0} Λ f' ⋙ etaleModuleExtensionByZero.{u, 0} Λ i ≅
      etaleModuleExtensionByZero.{u, 0} Λ b ⋙ etaleModuleDirectImage.{u, 0} Λ fb)
    (μ₂ : etaleModuleDirectImage.{u, 0} Λ g' ⋙ etaleModuleExtensionByZero.{u, 0} Λ m ≅
      etaleModuleExtensionByZero.{u, 0} Λ i ⋙ etaleModuleDirectImage.{u, 0} Λ gb)
    (F : EtaleModules.{u, 0} Λ P) :
    (etaleModuleExtensionByZero.{u, 0} Λ m).map
        ((etaleModuleDirectImageComp.{u, 0} Λ f' g' pg hpg).hom.app F) ≫
      (etaleModuleSquareVerticalPaste Λ hpg hpf μ₁ μ₂).hom.app F =
    μ₂.hom.app ((etaleModuleDirectImage.{u, 0} Λ f').obj F) ≫
      (etaleModuleDirectImage.{u, 0} Λ gb).map (μ₁.hom.app F) ≫
      (etaleModuleDirectImageComp.{u, 0} Λ fb gb pf hpf).hom.app
        ((etaleModuleExtensionByZero.{u, 0} Λ b).obj F) := by
  rw [etaleModuleSquareVerticalPaste_hom_app, ← Functor.map_comp_assoc, Iso.hom_inv_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]

/-- The map of [Stacks, Tag 0F7G] along `ψ` at an object, through the map of its square. -/
lemma derivedRefinementComparisonUnboundedUniv_app_eq_squareMap {X Y : Scheme.{u}} {f : X ⟶ Y}
    {j k : CompactificationOf (Over.mk f)} (ψ : j ⟶ k)
    (N : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedRefinementComparisonUnboundedUniv.{u, 0} Λ ψ).app N =
      (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ k.immersion).map
          ((etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ X).inv.app N) ≫
        (derivedExtensionByZeroSquareMap Λ j.immersion k.immersion (𝟙 X)
          (CompactificationOf.Hom.map ψ) (refinementSquareIso Λ ψ)).app N := by
  rw [derivedRefinementComparisonUnboundedUniv_eq_squareMap]
  simp only [NatTrans.comp_app, Functor.leftUnitor_inv_app, Functor.whiskerRight_app,
    Category.id_comp]

/-- The open immersion case of [Stacks, Tag 0F7B] followed by the map of its square is the
identity. -/
lemma etaleModuleExtensionByZeroDirectImageUnboundedIsoE_hom_app_squareMap
    {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb] (i : Y ⟶ Ub) [IsOpenImmersion i]
    (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y) (sq : IsPullback b f' fb i) [CompactSpace Ub]
    (K : DerivedCategory (EtaleModules.{u, 0} Λ P)) :
    (etaleModuleExtensionByZeroDirectImageUnboundedIsoE Λ hΛ fb i b f' sq).hom.app K ≫
      (derivedExtensionByZeroSquareMap Λ b i f' fb
        (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb i b f' sq)).app K = 𝟙 _ := by
  rw [← etaleModuleExtensionByZeroDirectImageUnboundedIsoE_inv]
  exact Iso.hom_inv_id_app _ _

/-- The map of the square of the open immersion case of [Stacks, Tag 0F7B] followed by that
case is the identity. -/
lemma squareMap_app_etaleModuleExtensionByZeroDirectImageUnboundedIsoE_hom
    {T Ub P Y : Scheme.{u}} (fb : T ⟶ Ub) [IsProper fb] (i : Y ⟶ Ub) [IsOpenImmersion i]
    (b : P ⟶ T) [IsOpenImmersion b] (f' : P ⟶ Y) (sq : IsPullback b f' fb i) [CompactSpace Ub]
    (K : DerivedCategory (EtaleModules.{u, 0} Λ P)) :
    (derivedExtensionByZeroSquareMap Λ b i f' fb
        (etaleModuleDirectImageExtensionByZeroIso Λ hΛ fb i b f' sq)).app K ≫
      (etaleModuleExtensionByZeroDirectImageUnboundedIsoE Λ hΛ fb i b f' sq).hom.app K = 𝟙 _ := by
  rw [← etaleModuleExtensionByZeroDirectImageUnboundedIsoE_inv]
  exact Iso.inv_hom_id_app _ _

/-! ### Chases over plain objects -/

section Chain

/-- The chase behind `Stacks.EtaleCohomology.secondSlot_identity_square`, over plain objects:
a horizontal pasting of a map of [Stacks, Tag 0F7G] with a square read through the composition
isomorphisms of extensions by zero. -/
lemma identitySquare_chain {𝒞 : Type*} [Category* 𝒞] {e0 e1 e2 e3 e4 e7 e8 : 𝒞}
    (ec : e0 ⟶ e1) (ρc : e1 ⟶ e3) (Ry : e3 ⟶ e4) (et : e1 ⟶ e2) (sC : e2 ⟶ e3)
    (ecinv : e2 ⟶ e8) (Es : e8 ⟶ e7) (sG : e7 ⟶ e4) (Rx : e4 ⟶ e3) (Eat : e0 ⟶ e8)
    (ec' : e8 ⟶ e2) (Eρr : e0 ⟶ e7)
    (hρc : ρc = et ≫ sC) (hH : sC = ecinv ≫ Es ≫ sG ≫ Rx) (hRxy : Rx ≫ Ry = 𝟙 _)
    (nE : Eat ≫ ec' = ec ≫ et) (hcc : ec' ≫ ecinv = 𝟙 _) (hρr : Eρr = Eat ≫ Es) :
    ec ≫ ρc ≫ Ry = Eρr ≫ sG := by
  rw [hρc, hH, hρr]
  simp only [Category.assoc]
  rw [← reassoc_of% nE, reassoc_of% hcc, hRxy, Category.comp_id]

/-- The chase behind `Stacks.EtaleCohomology.secondSlot_right`. -/
private lemma la_chain {𝒞 : Type*} [Category* 𝒞] {A0 A1 A2 A3 B1 B2 C1 C2 D1 D2 D3 : 𝒞}
    (ρN : A0 ⟶ A1) (RH : A1 ⟶ A2) (RS : A2 ⟶ A3) (EH : A0 ⟶ B1) (ρM : B1 ⟶ A2)
    (ERid : B1 ⟶ B2) (sθ : B2 ⟶ A2) (sO : B1 ⟶ C1) (Lh : C1 ⟶ A3) (ELq : B1 ⟶ B2)
    (ERρ : A0 ⟶ D1) (ELi : D1 ⟶ B1) (ELh : B1 ⟶ D1) (sS'r : D1 ⟶ D2) (RG : D2 ⟶ C2)
    (Lch : C1 ⟶ C2) (Lci : C2 ⟶ C1) (sS'a : A0 ⟶ D3) (REρ : D3 ⟶ D2) (RX : D3 ⟶ C2)
    (n2 : EH ≫ ρM = ρN ≫ RH) (h3 : ρM = ERid ≫ sθ) (h5 : ELq = ERid)
    (h4 : sO ≫ Lh = ELq ≫ sθ ≫ RS) (h1 : EH = ERρ ≫ ELi)
    (h6 : sO ≫ Lch = ELh ≫ sS'r ≫ RG) (hLc : Lch ≫ Lci = 𝟙 _) (hLr : ELi ≫ ELh = 𝟙 _)
    (h7 : ERρ ≫ sS'r = sS'a ≫ REρ) (hRX : RX = REρ ≫ RG) :
    ρN ≫ RH ≫ RS = sS'a ≫ RX ≫ Lci ≫ Lh := by
  have e6 : ELi ≫ sO = sS'r ≫ RG ≫ Lci := by
    calc ELi ≫ sO = ELi ≫ (sO ≫ Lch) ≫ Lci := by
          rw [Category.assoc, hLc, Category.comp_id]
      _ = sS'r ≫ RG ≫ Lci := by
          rw [h6]
          simp only [Category.assoc]
          rw [reassoc_of% hLr]
  rw [← reassoc_of% n2, h3, ← h5, Category.assoc, ← h4, h1, Category.assoc, reassoc_of% e6,
    reassoc_of% h7, hRX]
  simp only [Category.assoc]

/-- The chase behind `Stacks.EtaleCohomology.secondSlot_left`. -/
private lemma lb_chain {𝒞 : Type*} [Category* 𝒞] {a0 a1 a2 a3 a4 a5 a6 a7 a8 a8' a9 : 𝒞}
    (S : a0 ⟶ a1) (Rec : a1 ⟶ a2) (Lh0 : a2 ⟶ a3) (Hc : a3 ⟶ a4) (Re : a4 ⟶ a5)
    (RRρ : a3 ⟶ a6) (RLci : a6 ⟶ a4) (Rρ : a2 ⟶ a7) (Lh1 : a7 ⟶ a6) (Lci : a7 ⟶ a8)
    (Lh2 : a8 ⟶ a4) (Rre : a8 ⟶ a9) (Lh3 : a9 ⟶ a5) (RRe : a7 ⟶ a8') (Lci3 : a8' ⟶ a9)
    (RX : a2 ⟶ a8')
    (hHc : Hc = RRρ ≫ RLci) (na : Lh0 ≫ RRρ = Rρ ≫ Lh1) (hb : Lh1 ≫ RLci = Lci ≫ Lh2)
    (nc : Lh2 ≫ Re = Rre ≫ Lh3) (nd : Lci ≫ Rre = RRe ≫ Lci3) (hRX : RX = Rρ ≫ RRe) :
    S ≫ Rec ≫ Lh0 ≫ Hc ≫ Re = S ≫ Rec ≫ RX ≫ Lci3 ≫ Lh3 := by
  rw [hHc, hRX]
  simp only [Category.assoc]
  rw [reassoc_of% na, reassoc_of% hb, nc, reassoc_of% nd]

/-- The chase behind `Stacks.EtaleCohomology.secondSlotUnbounded_Ybar`. -/
private lemma ybar_chain {𝒞 : Type*} [Category* 𝒞] {b0 b1 b2 b3 b4 b5 b6 b7 : 𝒞}
    (S' : b0 ⟶ b1) (Rec : b1 ⟶ b2) (L : b2 ⟶ b3) (Hc : b3 ⟶ b4) (Re : b4 ⟶ b5)
    (ρN : b0 ⟶ b6) (RH : b6 ⟶ b7) (RS : b7 ⟶ b5) (RΨ : b3 ⟶ b7) (RIso : b5 ⟶ b7)
    (Ψ'h : b2 ⟶ b0) (Rinv : b2 ⟶ b1) (IE'h : b1 ⟶ b0)
    (hcore : S' ≫ Rec ≫ L ≫ Hc ≫ Re = ρN ≫ RH ≫ RS) (hL : RΨ = Hc ≫ Re ≫ RIso)
    (hΨ' : Ψ'h = Rinv ≫ IE'h) (i1 : IE'h ≫ S' = 𝟙 _) (i2 : Rinv ≫ Rec = 𝟙 _)
    (i3 : RS ≫ RIso = 𝟙 _) :
    L ≫ RΨ = Ψ'h ≫ ρN ≫ RH := by
  rw [hL, hΨ']
  simp only [Category.assoc]
  calc L ≫ Hc ≫ Re ≫ RIso = (Rinv ≫ IE'h ≫ S' ≫ Rec) ≫ L ≫ Hc ≫ Re ≫ RIso := by
        rw [reassoc_of% i1, i2, Category.id_comp]
    _ = Rinv ≫ IE'h ≫ (S' ≫ Rec ≫ L ≫ Hc ≫ Re) ≫ RIso := by simp only [Category.assoc]
    _ = Rinv ≫ IE'h ≫ ρN ≫ RH := by
        rw [hcore]
        simp only [Category.assoc]
        rw [i3, Category.comp_id]

end Chain

/-! ### Along a morphism of compactifications of `g` -/

section SecondSlot

open CompactificationOf CompactificationOf.SecondSlot

variable {X Y Z : Scheme.{u}} {f : X ⟶ Y} {g : Y ⟶ Z} {jG jG' : CompactificationOf (Over.mk g)}
  (ψ : jG ⟶ jG') (jX : CompactificationOf (Over.mk (f ≫ jG.immersion)))

/-- `X̄ ×_Ȳ Y ⟶ X̄ ×_Ȳ' Y` is an open immersion, its composite with the open immersion
`X̄ ×_Ȳ' Y ⟶ X̄` being the open immersion `X̄ ×_Ȳ Y ⟶ X̄`. -/
instance (priority := high) isOpenImmersion_map_r : IsOpenImmersion (Hom.map (r ψ jX)) := by
  have : IsOpenImmersion (Hom.map (r ψ jX) ≫ restrictBaseι jG' (pushX ψ jX)) :=
    (congrArg (@IsOpenImmersion _ _) (rmap_fst ψ jX)).mpr
      (CompactificationOf.isOpenImmersion_restrictBaseι jG jX)
  exact IsOpenImmersion.of_comp _ (restrictBaseι jG' (pushX ψ jX))

/-- The ambient morphism of `c₀' ψ jX`, the identity of `X̄`. -/
local notation "c̄" => CompactificationOf.Hom.map (j := overBar jG jX) (k := k₂ ψ jX) (c₀' ψ jX)

/-- The ambient morphism of `c₀' ψ jX` is proper. -/
instance (priority := high) isProper_map_c₀' : IsProper (c̄) :=
  isProper_compactificationOf_hom_map _

/-- The ambient morphism of `c₀' ψ jX` is proper, read as a morphism `X̄ ⟶ X̄` over `Ȳ'`. -/
instance (priority := high) isProper_map_c₀'_pushX :
    IsProper (c̄ : jX.space ⟶ (pushX ψ jX).space) :=
  isProper_compactificationOf_hom_map _

/-- The open immersion `X̄ ×_Ȳ' Y ⟶ X̄`. -/
instance (priority := high) isOpenImmersion_restrictBaseι_pushX :
    IsOpenImmersion (restrictBaseι jG' (pushX ψ jX)) :=
  CompactificationOf.isOpenImmersion_restrictBaseι jG' (pushX ψ jX)

/-- The square `X̄ ×_Ȳ Y ⟶ X̄` over `X̄ ×_Ȳ' Y ⟶ X̄`, with sides `X̄ ×_Ȳ Y ⟶ X̄ ×_Ȳ' Y` and the
identity of `X̄`, commutes. -/
lemma secondSlot_w : restrictBaseι jG jX ≫ (c̄ : jX.space ⟶ (pushX ψ jX).space) =
    Hom.map (r ψ jX) ≫ restrictBaseι jG' (pushX ψ jX) :=
  (Category.comp_id _).trans (rmap_fst ψ jX).symm

/-- The map of [Stacks, Tag 0F7B] of the square `X̄ ×_Ȳ Y ⟶ X̄` over `X̄ ×_Ȳ' Y ⟶ X̄`, whose left
side is a proper open immersion. -/
abbrev secondSlotSquare :
    etaleModuleDirectImage.{u, 0} Λ (Hom.map (r ψ jX)) ⋙
        etaleModuleExtensionByZero.{u, 0} Λ (restrictBaseι jG' (pushX ψ jX)) ≅
      etaleModuleExtensionByZero.{u, 0} Λ (restrictBaseι jG jX) ⋙
        etaleModuleDirectImage.{u, 0} Λ (c̄ : jX.space ⟶ (pushX ψ jX).space) :=
  @etaleModuleSquareIsoOfIsProperOpen Λ _ _ _ _ _ (restrictBaseι jG jX)
    (restrictBaseι jG' (pushX ψ jX)) inferInstance (isOpenImmersion_restrictBaseι_pushX ψ jX)
    (Hom.map (r ψ jX)) (isOpenImmersion_map_r ψ jX) inferInstance
    (c̄ : jX.space ⟶ (pushX ψ jX).space) (isProper_map_c₀'_pushX ψ jX) (secondSlot_w ψ jX)

/-- `secondSlotSquare` is pinned by `ε`. -/
theorem isExtensionByZeroBaseChange_secondSlotSquare :
    IsExtensionByZeroBaseChange Λ (Hom.map (r ψ jX) ≫ restrictBaseι jG' (pushX ψ jX))
      (secondSlot_w ψ jX).symm rfl (secondSlotSquare Λ ψ jX).hom :=
  @isExtensionByZeroBaseChange_etaleModuleSquareIsoOfIsProperOpen Λ _ _ _ _ _
    (restrictBaseι jG jX) (restrictBaseι jG' (pushX ψ jX)) inferInstance
    (isOpenImmersion_restrictBaseι_pushX ψ jX) (Hom.map (r ψ jX)) (isOpenImmersion_map_r ψ jX)
    inferInstance (c̄ : jX.space ⟶ (pushX ψ jX).space) (isProper_map_c₀'_pushX ψ jX)
    (secondSlot_w ψ jX)

/-- **The identity of `X̄`, through `X̄ ×_Ȳ Y ⟶ X̄ ×_Ȳ' Y`** ([Stacks, Tag 0F7D]): the map of
[Stacks, Tag 0F7G] along the identity of `X̄`, read through the composition isomorphisms of
derived extensions by zero, is that along `X̄ ×_Ȳ Y ⟶ X̄ ×_Ȳ' Y` followed by the map of the square
`secondSlotSquare`. -/
theorem secondSlot_identity_square (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedExtensionByZeroUnboundedCompIso Λ (restrictBase jG' (pushX ψ jX)).immersion
        (restrictBaseι jG' (pushX ψ jX))).hom.app K ≫
      (derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (c₀' ψ jX)).app K ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (c̄)).map
        ((derivedExtensionByZeroUnboundedCompIso Λ (restrictBase jG jX).immersion
          (restrictBaseι jG jX)).inv.app K) =
    (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (restrictBaseι jG' (pushX ψ jX))).map
        ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (r ψ jX)).app K) ≫
      (derivedExtensionByZeroSquareMap Λ (restrictBaseι jG jX) (restrictBaseι jG' (pushX ψ jX))
        (Hom.map (r ψ jX)) (c̄) (secondSlotSquare Λ ψ jX)).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (restrictBase jG jX).immersion).obj K) := by
  have hpaste := fun F => IsExtensionByZeroBaseChange.horizontal_paste
    (isExtensionByZeroBaseChange_refinementSquareIso Λ (r ψ jX))
    (isExtensionByZeroBaseChange_secondSlotSquare Λ ψ jX)
    (isExtensionByZeroBaseChange_refinementSquareIso Λ (c₀' ψ jX)) F
  have hH := NatTrans.congr_app (derivedExtensionByZeroSquareMap_horizontal_paste Λ
    (restrictBase jG jX).immersion (restrictBaseι jG jX) (restrictBase jG' (pushX ψ jX)).immersion
    (restrictBaseι jG' (pushX ψ jX)) (𝟙 X) (Hom.map (r ψ jX)) (c̄)
    (refinementSquareIso Λ (r ψ jX)) (secondSlotSquare Λ ψ jX) (refinementSquareIso Λ (c₀' ψ jX))
    hpaste) K
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp] at hH
  have hρr := congrArg (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
      (restrictBaseι jG' (pushX ψ jX))).map
    (derivedRefinementComparisonUnboundedUniv_app_eq_squareMap Λ (r ψ jX) K)
  rw [Functor.map_comp] at hρr
  have nE := (derivedExtensionByZeroUnboundedCompIso Λ
    (restrictBase jG' (pushX ψ jX)).immersion (restrictBaseι jG' (pushX ψ jX))).hom.naturality
    ((etaleModuleDerivedDirectImageUnboundedIdIso.{u, 0} Λ X).inv.app K)
  simp only [Functor.comp_map] at nE
  exact identitySquare_chain _ _ _ _ _ _ _ _ _ _ _ _
    (derivedRefinementComparisonUnboundedUniv_app_eq_squareMap Λ (c₀' ψ jX) K) hH
    ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (c̄)).mapIso
      ((derivedExtensionByZeroUnboundedCompIso Λ (restrictBase jG jX).immersion
        (restrictBaseι jG jX)).app K)).hom_inv_id
    nE (Iso.hom_inv_id_app _ _) hρr

/-- `X̄ ×_Ȳ Y ⟶ X̄ ⟶ Ȳ'` is `X̄ ×_Ȳ Y ⟶ Y ⟶ Ȳ'`. -/
lemma secondSlot_hmH : restrictBaseι jG jX ≫ (pushX ψ jX).toBase =
    (restrictBase jG jX).toBase ≫ jG'.immersion :=
  calc restrictBaseι jG jX ≫ (pushX ψ jX).toBase
      = (restrictBaseι jG jX ≫ jX.toBase) ≫ Hom.map ψ := (Category.assoc _ _ _).symm
    _ = ((restrictBase jG jX).toBase ≫ jG.immersion) ≫ Hom.map ψ :=
        congrArg (· ≫ Hom.map ψ) (IsPullback.of_hasPullback jX.toBase jG.immersion).w
    _ = (restrictBase jG jX).toBase ≫ jG'.immersion := by
        rw [Category.assoc, immersion_comp_map]

variable [CompactSpace jG.space] [CompactSpace jG'.space]

/-- The map of [Stacks, Tag 0F7B] of the square `X̄ ×_Ȳ Y ⟶ X̄` over `Y ⟶ Ȳ'`, the vertical pasting
of that of `X̄ ×_Ȳ Y ⟶ X̄` over `Y ⟶ Ȳ` and of the map `θ̃_ψ` of [Stacks, Tag 0F7G]. -/
abbrev secondSlotRectangle :
    etaleModuleDirectImage.{u, 0} Λ (restrictBase jG jX).toBase ⋙
        etaleModuleExtensionByZero.{u, 0} Λ jG'.immersion ≅
      etaleModuleExtensionByZero.{u, 0} Λ (restrictBaseι jG jX) ⋙
        etaleModuleDirectImage.{u, 0} Λ (pushX ψ jX).toBase :=
  etaleModuleSquareVerticalPaste Λ (Category.comp_id _).symm rfl
    (etaleModuleDirectImageExtensionByZeroIso Λ hΛ jX.toBase jG.immersion (restrictBaseι jG jX)
      (restrictBase jG jX).toBase (IsPullback.of_hasPullback jX.toBase jG.immersion))
    (refinementSquareIso Λ ψ)

omit [CompactSpace jG.space] [CompactSpace jG'.space] in
/-- `secondSlotRectangle` is pinned by `ε`. -/
theorem isExtensionByZeroBaseChange_secondSlotRectangle :
    IsExtensionByZeroBaseChange Λ (restrictBaseι jG jX ≫ (pushX ψ jX).toBase) rfl
      (secondSlot_hmH ψ jX) (secondSlotRectangle Λ hΛ ψ jX).hom :=
  IsExtensionByZeroBaseChange.verticalPaste _ _
    (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ jX.toBase
      jG.immersion (restrictBaseι jG jX) (restrictBase jG jX).toBase
      (IsPullback.of_hasPullback jX.toBase jG.immersion))
    (isExtensionByZeroBaseChange_refinementSquareIso Λ ψ) _ _ _

omit [CompactSpace jG.space] [CompactSpace jG'.space] in
/-- **The right side of the comparison over `Ȳ'`**: the map `θ_ψ : i'_! ⟶ Rψ̄_* i_!` of
[Stacks, Tag 0F7G], followed by `Rψ̄_* i_!` of the comparison along `X̄ ×_Ȳ Y ⟶ X̄ ×_Ȳ' Y` and
by `Rψ̄_*` of the map of [Stacks, Tag 0F7B] of `X̄ ×_Ȳ Y`, is the map of [Stacks, Tag 0F7B] of
`X̄ ×_Ȳ' Y`, followed by the comparison `secondSlotSquare` and the Leray isomorphisms. -/
theorem secondSlot_right (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedRefinementComparisonUnboundedUniv.{u, 0} Λ ψ).app
        ((derivedLowerShriekUnbounded.{u, 0} f (restrictBase jG' (pushX ψ jX)) Λ).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jG.immersion).map
          ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r ψ jX)).app K)) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
        ((derivedExtensionByZeroSquareMap Λ (restrictBaseι jG jX) jG.immersion
          (restrictBase jG jX).toBase jX.toBase
          (etaleModuleDirectImageExtensionByZeroIso Λ hΛ jX.toBase jG.immersion
            (restrictBaseι jG jX) (restrictBase jG jX).toBase
            (IsPullback.of_hasPullback jX.toBase jG.immersion))).app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (restrictBase jG jX).immersion).obj K)) =
    (derivedExtensionByZeroSquareMap Λ (restrictBaseι jG' (pushX ψ jX)) jG'.immersion
        (restrictBase jG' (pushX ψ jX)).toBase (pushX ψ jX).toBase
        (etaleModuleDirectImageExtensionByZeroIso Λ hΛ (pushX ψ jX).toBase jG'.immersion
          (restrictBaseι jG' (pushX ψ jX)) (restrictBase jG' (pushX ψ jX)).toBase
          (IsPullback.of_hasPullback (pushX ψ jX).toBase jG'.immersion))).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (restrictBase jG' (pushX ψ jX)).immersion).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (pushX ψ jX).toBase).map
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (restrictBaseι jG' (pushX ψ jX))).map
            ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (r ψ jX)).app K) ≫
          (derivedExtensionByZeroSquareMap Λ (restrictBaseι jG jX) (restrictBaseι jG' (pushX ψ jX))
            (Hom.map (r ψ jX)) (c̄) (secondSlotSquare Λ ψ jX)).app
            ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
              (restrictBase jG jX).immersion).obj K)) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (c̄) (pushX ψ jX).toBase
          (pushX ψ jX).toBase (Category.id_comp _).symm).inv.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (restrictBaseι jG jX)).obj
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (restrictBase jG jX).immersion).obj K)) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase (Hom.map ψ)
          (pushX ψ jX).toBase rfl).hom.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (restrictBaseι jG jX)).obj
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (restrictBase jG jX).immersion).obj K)) := by
  -- the two pastings of the rectangle `X̄ ×_Ȳ Y ⟶ X̄` over `Y ⟶ Ȳ'`
  have P1 := NatTrans.congr_app (derivedExtensionByZeroSquareMap_vertical_paste Λ
    (restrictBaseι jG jX) jG.immersion jG'.immersion (restrictBase jG jX).toBase jX.toBase
    (𝟙 Y) (Hom.map ψ) (restrictBase jG jX).toBase (pushX ψ jX).toBase
    (Category.comp_id _).symm rfl _ (refinementSquareIso Λ ψ) (secondSlotRectangle Λ hΛ ψ jX)
    (etaleModuleSquareVerticalPaste_paste Λ _ _ _ _))
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (restrictBase jG jX).immersion).obj K)
  have P2 := NatTrans.congr_app (derivedExtensionByZeroSquareMap_vertical_paste Λ
    (restrictBaseι jG jX) (restrictBaseι jG' (pushX ψ jX)) jG'.immersion (Hom.map (r ψ jX)) (c̄)
    (restrictBase jG' (pushX ψ jX)).toBase (pushX ψ jX).toBase (restrictBase jG jX).toBase
    (pushX ψ jX).toBase (rmap_snd ψ jX).symm (Category.id_comp _).symm (secondSlotSquare Λ ψ jX)
    _ (secondSlotRectangle Λ hΛ ψ jX)
    (fun F => IsExtensionByZeroBaseChange.vertical_paste _ _
      (isExtensionByZeroBaseChange_secondSlotSquare Λ ψ jX)
      (isExtensionByZeroBaseChange_etaleModuleDirectImageExtensionByZeroIso Λ hΛ
        (pushX ψ jX).toBase jG'.immersion (restrictBaseι jG' (pushX ψ jX))
        (restrictBase jG' (pushX ψ jX)).toBase
        (IsPullback.of_hasPullback (pushX ψ jX).toBase jG'.immersion))
      (isExtensionByZeroBaseChange_secondSlotRectangle Λ hΛ ψ jX) F))
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (restrictBase jG jX).immersion).obj K)
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Functor.associator_hom_app, Functor.associator_inv_app, Category.id_comp,
    Category.comp_id] at P1 P2
  have h1 := (congrArg (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jG'.immersion).map
    (derivedLowerShriekUnboundedHomUniv_app_eq_leray Λ (r ψ jX) K)).trans (Functor.map_comp _ _ _)
  have h5 := congrArg (etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jG'.immersion).map
    (etaleModuleDerivedDirectImageUnboundedLerayIso_id_right_hom_app Λ (restrictBase jG jX).toBase
      (Category.comp_id _).symm
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (restrictBase jG jX).immersion).obj K))
  exact la_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ ψ).naturality
      ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r ψ jX)).app K))
    (derivedRefinementComparisonUnboundedUniv_app_eq_squareMap Λ ψ _) h5 P1 h1 P2
    (Iso.hom_inv_id_app _ _)
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jG'.immersion).mapIso
      ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (Hom.map (r ψ jX))
        (restrictBase jG' (pushX ψ jX)).toBase (restrictBase jG jX).toBase
        (CompactificationOf.map_comp_toBase (r ψ jX)).symm).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (restrictBase jG jX).immersion).obj K))).inv_hom_id
    ((derivedExtensionByZeroSquareMap Λ (restrictBaseι jG' (pushX ψ jX)) jG'.immersion
        (restrictBase jG' (pushX ψ jX)).toBase (pushX ψ jX).toBase
        (etaleModuleDirectImageExtensionByZeroIso Λ hΛ (pushX ψ jX).toBase jG'.immersion
          (restrictBaseι jG' (pushX ψ jX)) (restrictBase jG' (pushX ψ jX)).toBase
          (IsPullback.of_hasPullback (pushX ψ jX).toBase jG'.immersion))).naturality
      ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (r ψ jX)).app K))
    (Functor.map_comp _ _ _)

/-- An inverse pair moved across a square, over plain objects. -/
lemma invSwap_chain {𝒞 : Type*} [Category* 𝒞] {a b c d : 𝒞} (x : a ⟶ b)
    (Rh : b ⟶ c) (Ri : c ⟶ b) (Ch : a ⟶ d) (Ci : d ⟶ a) (y : d ⟶ c)
    (A : x ≫ Rh = Ch ≫ y) (hR : Rh ≫ Ri = 𝟙 _) (hC : Ci ≫ Ch = 𝟙 _) : y ≫ Ri = Ci ≫ x := by
  calc y ≫ Ri = Ci ≫ Ch ≫ y ≫ Ri := by rw [reassoc_of% hC]
    _ = Ci ≫ x ≫ Rh ≫ Ri := by rw [← reassoc_of% A]
    _ = Ci ≫ x := by rw [hR, Category.comp_id]

omit [CompactSpace jG.space] [CompactSpace jG'.space] in
/-- **The left side of the comparison over `Ȳ'`**: the Leray isomorphism of `X̄ ⟶ Ȳ ⟶ Ȳ'` followed
by `Rψ̄_*` of the comparison along the identity of `X̄`, read through the Leray isomorphisms of the
identity of `X̄`. -/
theorem secondSlot_left (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedExtensionByZeroSquareMap Λ (restrictBaseι jG' (pushX ψ jX)) jG'.immersion
        (restrictBase jG' (pushX ψ jX)).toBase (pushX ψ jX).toBase
        (etaleModuleDirectImageExtensionByZeroIso Λ hΛ (pushX ψ jX).toBase jG'.immersion
          (restrictBaseι jG' (pushX ψ jX)) (restrictBase jG' (pushX ψ jX)).toBase
          (IsPullback.of_hasPullback (pushX ψ jX).toBase jG'.immersion))).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (restrictBase jG' (pushX ψ jX)).immersion).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (pushX ψ jX).toBase).map
        ((derivedExtensionByZeroUnboundedCompIso Λ
          (restrictBase jG' (pushX ψ jX)).immersion (restrictBaseι jG' (pushX ψ jX))).hom.app K) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase (Hom.map ψ)
          (pushX ψ jX).toBase rfl).hom.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (k₂ ψ jX).immersion).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
        ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₀' ψ jX)).app K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase).map
          ((derivedExtensionByZeroUnboundedCompIso Λ (restrictBase jG jX).immersion
            (restrictBaseι jG jX)).inv.app K)) =
    (derivedExtensionByZeroSquareMap Λ (restrictBaseι jG' (pushX ψ jX)) jG'.immersion
        (restrictBase jG' (pushX ψ jX)).toBase (pushX ψ jX).toBase
        (etaleModuleDirectImageExtensionByZeroIso Λ hΛ (pushX ψ jX).toBase jG'.immersion
          (restrictBaseι jG' (pushX ψ jX)) (restrictBase jG' (pushX ψ jX)).toBase
          (IsPullback.of_hasPullback (pushX ψ jX).toBase jG'.immersion))).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (restrictBase jG' (pushX ψ jX)).immersion).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (pushX ψ jX).toBase).map
        ((derivedExtensionByZeroUnboundedCompIso Λ
          (restrictBase jG' (pushX ψ jX)).immersion (restrictBaseι jG' (pushX ψ jX))).hom.app K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (pushX ψ jX).toBase).map
        ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (c₀' ψ jX)).app K ≫
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (c̄)).map
            ((derivedExtensionByZeroUnboundedCompIso Λ (restrictBase jG jX).immersion
              (restrictBaseι jG jX)).inv.app K)) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (c̄) (pushX ψ jX).toBase
          (pushX ψ jX).toBase (Category.id_comp _).symm).inv.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (restrictBaseι jG jX)).obj
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (restrictBase jG jX).immersion).obj K)) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase (Hom.map ψ)
          (pushX ψ jX).toBase rfl).hom.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (restrictBaseι jG jX)).obj
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (restrictBase jG jX).immersion).obj K)) := by
  have A := etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app Λ (c̄) (k₂ ψ jX).toBase
    (Hom.map ψ) (overBar jG jX).toBase (CompactificationOf.map_comp_toBase (c₀' ψ jX)).symm
    (pushX ψ jX).toBase rfl (pushX ψ jX).toBase rfl (Category.id_comp _).symm
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (overBar jG jX).immersion).obj K)
  have hb := invSwap_chain _ _ _ _ _ _ A
    ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).mapIso
      ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (c̄) (k₂ ψ jX).toBase
        (overBar jG jX).toBase (CompactificationOf.map_comp_toBase (c₀' ψ jX)).symm).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (overBar jG jX).immersion).obj K))).hom_inv_id
    (Iso.inv_hom_id_app _ _)
  exact lb_chain _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    ((congrArg (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
      (derivedLowerShriekUnboundedHomUniv_app_eq_leray Λ (c₀' ψ jX) K)).trans
        (Functor.map_comp _ _ _))
    ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase (Hom.map ψ)
      (pushX ψ jX).toBase rfl).hom.naturality
        ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (c₀' ψ jX)).app K)).symm
    hb
    ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase (Hom.map ψ)
      (pushX ψ jX).toBase rfl).hom.naturality
        ((derivedExtensionByZeroUnboundedCompIso Λ (restrictBase jG jX).immersion
          (restrictBaseι jG jX)).inv.app K)).symm
    ((etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (c̄) (pushX ψ jX).toBase
      (pushX ψ jX).toBase (Category.id_comp _).symm).inv.naturality
        ((derivedExtensionByZeroUnboundedCompIso Λ (restrictBase jG jX).immersion
          (restrictBaseι jG jX)).inv.app K)).symm
    (Functor.map_comp _ _ _)


omit [CompactSpace jG.space] [CompactSpace jG'.space] in
/-- **The comparison over `Ȳ'`, through the maps of the squares**: both sides of
`Stacks.EtaleCohomology.secondSlotUnbounded_Ybar`, read through the maps of
[Stacks, Tag 0F7B] of `X̄ ×_Ȳ Y` and `X̄ ×_Ȳ' Y`. -/
theorem secondSlotUnbounded_Ybar_squares (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedExtensionByZeroSquareMap Λ (restrictBaseι jG' (pushX ψ jX)) jG'.immersion
        (restrictBase jG' (pushX ψ jX)).toBase (pushX ψ jX).toBase
        (etaleModuleDirectImageExtensionByZeroIso Λ hΛ (pushX ψ jX).toBase jG'.immersion
          (restrictBaseι jG' (pushX ψ jX)) (restrictBase jG' (pushX ψ jX)).toBase
          (IsPullback.of_hasPullback (pushX ψ jX).toBase jG'.immersion))).app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (restrictBase jG' (pushX ψ jX)).immersion).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (pushX ψ jX).toBase).map
        ((derivedExtensionByZeroUnboundedCompIso Λ
          (restrictBase jG' (pushX ψ jX)).immersion (restrictBaseι jG' (pushX ψ jX))).hom.app K) ≫
      (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase (Hom.map ψ)
          (pushX ψ jX).toBase rfl).hom.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (k₂ ψ jX).immersion).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
        ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₀' ψ jX)).app K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
        ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase).map
          ((derivedExtensionByZeroUnboundedCompIso Λ (restrictBase jG jX).immersion
            (restrictBaseι jG jX)).inv.app K)) =
    (derivedRefinementComparisonUnboundedUniv.{u, 0} Λ ψ).app
        ((derivedLowerShriekUnbounded.{u, 0} f (restrictBase jG' (pushX ψ jX)) Λ).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jG.immersion).map
          ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r ψ jX)).app K)) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
        ((derivedExtensionByZeroSquareMap Λ (restrictBaseι jG jX) jG.immersion
          (restrictBase jG jX).toBase jX.toBase
          (etaleModuleDirectImageExtensionByZeroIso Λ hΛ jX.toBase jG.immersion
            (restrictBaseι jG jX) (restrictBase jG jX).toBase
            (IsPullback.of_hasPullback jX.toBase jG.immersion))).app
          ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
            (restrictBase jG jX).immersion).obj K)) := by
  have hC : (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (pushX ψ jX).toBase).map
        ((derivedExtensionByZeroUnboundedCompIso Λ
          (restrictBase jG' (pushX ψ jX)).immersion (restrictBaseι jG' (pushX ψ jX))).hom.app K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (pushX ψ jX).toBase).map
        ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (c₀' ψ jX)).app K ≫
          (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (c̄)).map
            ((derivedExtensionByZeroUnboundedCompIso Λ (restrictBase jG jX).immersion
              (restrictBaseι jG jX)).inv.app K)) =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (pushX ψ jX).toBase).map
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (restrictBaseι jG' (pushX ψ jX))).map
            ((derivedRefinementComparisonUnboundedUniv.{u, 0} Λ (r ψ jX)).app K) ≫
          (derivedExtensionByZeroSquareMap Λ (restrictBaseι jG jX) (restrictBaseι jG' (pushX ψ jX))
            (Hom.map (r ψ jX)) (c̄) (secondSlotSquare Λ ψ jX)).app
            ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
              (restrictBase jG jX).immersion).obj K)) :=
    (Functor.map_comp _ _ _).symm.trans
      (congrArg (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (pushX ψ jX).toBase).map
        (secondSlot_identity_square Λ ψ jX K))
  rw [secondSlot_left Λ hΛ ψ jX K, reassoc_of% hC]
  exact (secondSlot_right Λ hΛ ψ jX K).symm

/-- **The comparison over `Ȳ'` along a morphism `ψ : jG ⟶ jG'` of compactifications of `g`**,
on `D(X_étale, Λ)`: `Rψ̄_*` of `Ψ : R(f ≫ i)_! ≅ i_! Rf_!` for `Y ⊂ Ȳ` agrees with `Ψ` for
`Y ⊂ Ȳ'` followed by the map `i'_! ⟶ Rψ̄_* i_!` of [Stacks, Tag 0F7G], read through the comparisons
of [Stacks, Tag 0F7I]. -/
theorem secondSlotUnbounded_Ybar (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ jX.toBase (Hom.map ψ)
        (pushX ψ jX).toBase rfl).hom.app
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (k₂ ψ jX).immersion).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
        ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₀' ψ jX)).app K ≫
          (derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ jG jX).hom.app K) =
    (derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ jG' (pushX ψ jX)).hom.app K ≫
      (derivedRefinementComparisonUnboundedUniv.{u, 0} Λ ψ).app
        ((derivedLowerShriekUnbounded.{u, 0} f (restrictBase jG' (pushX ψ jX)) Λ).obj K) ≫
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jG.immersion).map
          ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r ψ jX)).app K)) := by
  have hL : (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
      ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₀' ψ jX)).app K ≫
        (derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ jG jX).hom.app K) =
      (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
          ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c₀' ψ jX)).app K) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
          ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jX.toBase).map
            ((derivedExtensionByZeroUnboundedCompIso Λ (restrictBase jG jX).immersion
              (restrictBaseι jG jX)).inv.app K)) ≫
        (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
          ((etaleModuleExtensionByZeroDirectImageUnboundedIsoE Λ hΛ jX.toBase jG.immersion
            (restrictBaseι jG jX) (restrictBase jG jX).toBase
            (IsPullback.of_hasPullback jX.toBase jG.immersion)).hom.app
            ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
              (restrictBase jG jX).immersion).obj K)) := by
    exact (congrArg (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
      (congrArg (_ ≫ ·) (derivedLowerShriekUnboundedRestrictBaseIso_hom_app Λ hΛ jG jX K))).trans
      ((Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _)))
  have i3 := (Functor.map_comp _ _ _).symm.trans
    ((congrArg (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ)).map
      (squareMap_app_etaleModuleExtensionByZeroDirectImageUnboundedIsoE_hom Λ hΛ jX.toBase
        jG.immersion (restrictBaseι jG jX) (restrictBase jG jX).toBase
        (IsPullback.of_hasPullback jX.toBase jG.immersion)
        ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ
          (restrictBase jG jX).immersion).obj K))).trans
      (CategoryTheory.Functor.map_id _ _))
  exact ybar_chain _ _ _ _ _ _ _ _ _ _ _ _ _ (secondSlotUnbounded_Ybar_squares Λ hΛ ψ jX K) hL
    (derivedLowerShriekUnboundedRestrictBaseIso_hom_app Λ hΛ jG' (pushX ψ jX) K)
    (etaleModuleExtensionByZeroDirectImageUnboundedIsoE_hom_app_squareMap Λ hΛ
      (pushX ψ jX).toBase jG'.immersion (restrictBaseι jG' (pushX ψ jX))
      (restrictBase jG' (pushX ψ jX)).toBase
      (IsPullback.of_hasPullback (pushX ψ jX).toBase jG'.immersion) _)
    ((etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (pushX ψ jX).toBase).mapIso
      ((derivedExtensionByZeroUnboundedCompIso Λ
        (restrictBase jG' (pushX ψ jX)).immersion (restrictBaseι jG' (pushX ψ jX))).app
        K)).inv_hom_id
    i3

/-- **The comparison over `Z` along a morphism `ψ : jG ⟶ jG'` of compactifications of `g`**, on
`D(X_étale, Λ)`: the isomorphism of [Stacks, Tag 0F7J] through `jG` and `X̄`, read through the
comparisons of [Stacks, Tag 0F7I], is that through `jG'` and `X̄` followed by the comparison
`Rg_!^{jG'} ⟶ Rg_!^{jG}` along `ψ`. -/
theorem secondSlotUnbounded_core (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (c ψ jX)).app K ≫
        (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jG jX).hom.app K =
      (derivedLowerShriekUnboundedCompOverIso Λ hΛ f g jG' (pushX ψ jX)).hom.app K ≫
        (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ ψ).app
          ((derivedLowerShriekUnbounded.{u, 0} f (restrictBase jG' (pushX ψ jX)) Λ).obj K) ≫
        (derivedLowerShriekUnbounded.{u, 0} g jG Λ).map
          ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r ψ jX)).app K) := by
  have nBC1 := (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (Hom.map ψ) jG'.toBase
    jG.toBase (map_comp_toBase ψ).symm).hom.naturality
      ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ jG.immersion).map
        ((derivedLowerShriekUnboundedHomUniv.{u, 0} Λ (r ψ jX)).app K))
  have nBC2 := (etaleModuleDerivedDirectImageUnboundedLerayIso.{u, 0} Λ (Hom.map ψ) jG'.toBase
    jG.toBase (map_comp_toBase ψ).symm).hom.naturality
      ((derivedLowerShriekUnboundedRestrictBaseIso Λ hΛ jG jX).hom.app K)
  have A := etaleModuleDerivedDirectImageUnboundedLerayIso_assoc_app Λ jX.toBase (Hom.map ψ)
    jG'.toBase (k₁ ψ jX).toBase rfl jG.toBase (map_comp_toBase ψ).symm (bbar ψ jX)
    (toBase_comp_map ψ jX) rfl
    ((etaleModuleDerivedExtensionByZeroUnbounded.{u, 0} Λ (overBar jG jX).immersion).obj K)
  exact secondSlot_core_chain (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jG'.toBase)
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ (Hom.map ψ))
    (etaleModuleDerivedDirectImageUnbounded.{u, 0} Λ jG.toBase) _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    _ _ _ _ _ _
    (derivedLowerShriekUnboundedHomUniv_ofFactorHom Λ _ _ _ _ _ _ _ _ _ K)
    (derivedLowerShriekUnboundedHomUniv_ofFactorHom Λ _ _ _ _ _ _ _ _ _ K)
    (derivedLowerShriekUnboundedCompOverIso_hom_app Λ hΛ jG jX K)
    (derivedLowerShriekUnboundedCompOverIso_hom_app Λ hΛ jG' (pushX ψ jX) K)
    (derivedLowerShriekUnboundedHomUniv_app_eq_leray Λ ψ _) rfl nBC1 nBC2 A
    (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _) (Iso.inv_hom_id_app _ _)
    (secondSlotUnbounded_Ybar Λ hΛ ψ jX K) rfl

end SecondSlot

/-! ### Independence of the compactification of `g` -/

section Independence

open CompactificationOf CompactificationOf.SecondSlot

variable {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y] [CompactSpace Z] [QuasiSeparatedSpace Z]
  [IsSeparated f] [LocallyOfFiniteType f] [IsSeparated g] [LocallyOfFiniteType g]

/-- **The isomorphism of [Stacks, Tag 0F7J] on `D(X_étale, Λ)` along a morphism of
compactifications of `g`**: for `ψ : jG ⟶ jG'`, the isomorphism through `jG` is that through `jG'`
followed by the comparison `Rg_!^{jG'} ⟶ Rg_!^{jG}` of [Stacks, Tag 0F7I]. -/
theorem derivedLowerShriekUnboundedCompIso_hom_app_of_hom (jf : CompactificationOf (Over.mk f))
    {jG jG' : CompactificationOf (Over.mk g)} (ψ : jG ⟶ jG')
    (j : CompactificationOf (Over.mk (f ≫ g))) (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    (derivedLowerShriekUnboundedCompIso Λ hΛ f g jf jG j).hom.app K =
      (derivedLowerShriekUnboundedCompIso Λ hΛ f g jf jG' j).hom.app K ≫
        (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ ψ).app
          ((derivedLowerShriekUnbounded.{u, 0} f jf Λ).obj K) := by
  have : QuasiCompact f := quasiCompact_of_compactSpace f
  have : QuasiCompact (f ≫ g) := quasiCompact_of_compactSpace _
  have : CompactSpace jG.space := compactSpace_compactificationOf_space jG
  have : CompactSpace jG'.space := compactSpace_compactificationOf_space jG'
  obtain ⟨jX⟩ := nonempty_compactificationOf_comp_immersion f g jG
  have hL := derivedLowerShriekUnboundedCompIso_hom_app_eq Λ hΛ f g jf jG j jX K
  have hR := derivedLowerShriekUnboundedCompIso_hom_app_eq Λ hΛ f g jf jG' j (pushX ψ jX) K
  have i1 := derivedLowerShriekUnboundedCompactificationIsoUniv_hom_app_of_hom_comp Λ hΛ (f ≫ g) K
    (j := j) (c ψ jX)
  have i2 := derivedLowerShriekUnboundedCompactificationIsoUniv_hom_app_of_hom_source Λ hΛ f K
    (l := jf) (r ψ jX)
  exact secondSlot_hom_chain (derivedLowerShriekUnbounded.{u, 0} g jG Λ)
    (derivedLowerShriekUnbounded.{u, 0} g jG' Λ) (derivedLowerShriekUnboundedHomUniv.{u, 0} Λ ψ)
    _ _ _ _ _ _ _ _ _ _ hL hR i1 i2 (secondSlotUnbounded_core Λ hΛ ψ jX K)

/-- **The isomorphism of [Stacks, Tag 0F7J] on `D(X_étale, Λ)` does not depend on the
compactification of `g`**: for two compactifications `jG` and `jG'` of `g`, the isomorphisms
through them correspond under the comparison `Rg_!^{jG} ≅ Rg_!^{jG'}` of [Stacks, Tag 0F7I]. -/
theorem derivedLowerShriekUnboundedCompIso_hom_app_second (jf : CompactificationOf (Over.mk f))
    (jG jG' : CompactificationOf (Over.mk g)) (j : CompactificationOf (Over.mk (f ≫ g)))
    (K : DerivedCategory (EtaleModules.{u, 0} Λ X)) :
    haveI : QuasiCompact g := quasiCompact_of_compactSpace g
    (derivedLowerShriekUnboundedCompIso Λ hΛ f g jf jG' j).hom.app K =
      (derivedLowerShriekUnboundedCompIso Λ hΛ f g jf jG j).hom.app K ≫
        (derivedLowerShriekUnboundedCompactificationIsoUniv g jG jG' Λ hΛ).hom.app
          ((derivedLowerShriekUnbounded.{u, 0} f jf Λ).obj K) := by
  have : QuasiCompact g := quasiCompact_of_compactSpace g
  have h1 := derivedLowerShriekUnboundedCompIso_hom_app_of_hom Λ hΛ f g jf
    (IsCofiltered.minToLeft jG jG') j K
  have h2 := derivedLowerShriekUnboundedCompIso_hom_app_of_hom Λ hΛ f g jf
    (IsCofiltered.minToRight jG jG') j K
  have hs := derivedLowerShriekUnboundedCompactificationIsoUniv_hom_app_span Λ hΛ g
    ((derivedLowerShriekUnbounded.{u, 0} f jf Λ).obj K) (IsCofiltered.minToLeft jG jG')
    (IsCofiltered.minToRight jG jG')
  have hy := Iso.hom_inv_id_app (derivedLowerShriekUnboundedHomIsoUniv.{u, 0} Λ
    (IsCofiltered.minToRight jG jG') hΛ) ((derivedLowerShriekUnbounded.{u, 0} f jf Λ).obj K)
  rw [derivedLowerShriekUnboundedHomIsoUniv_hom] at hy
  rw [hs]
  exact span_chain _ _ _ _ _ _ h1 h2 hy

end Independence

end Stacks.EtaleCohomology

end
