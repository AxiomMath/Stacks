module

public import Mathlib.CategoryTheory.Functor.Derived.LeftDerived

/-!
# Comparing two composites of derived base change isomorphisms

Let `Q₀ : C₀ ⥤ D₀` and `P₀ : H₀ ⥤ E₀` be localization functors (for instance from cochain
complexes of modules over a ring, and from the homotopy category of a ringed topos, to the derived
categories), let `A₀ : C₀ ⥤ H₀` be an underived functor and `Φ₀ : D₀ ⥤ E₀` a derived version of
it, `e₀ : Q₀ ⋙ Φ₀ ≅ A₀ ⋙ P₀`, and similarly at further corners. An *edge* consists of a derived
extension `X₁` with comparison `κ₁ : Q₀ ⋙ X₁ ⟶ x₁ ⋙ Q₁` to an underived one `x₁`, a derived
pullback `L₁` with comparison `ℓ₁ : P₀ ⋙ L₁ ⟶ p₁ ⋙ P₁`, an underived morphism
`ρ₁ : A₀ ⋙ p₁ ⟶ x₁ ⋙ A₁` and a derived isomorphism `β₁ : Φ₀ ⋙ L₁ ≅ X₁ ⋙ Φ₁` induced by `ρ₁`
through the comparisons.

For two paths of two edges with the same ends, whose derived extensions compose to the same `X`
and whose derived pullbacks are identified with one `Lc`, the two composites of the `β` are
computed, after the comparison `κ` of `X`, by the two composites of the underived isomorphisms.
Hence, if those underived composites differ by an endomorphism `τ` of the identity of the last
corner which induces `t` on derived categories, the derived composites differ by `Φ₂` of `t`.

## Main definitions

* `Stacks.CategoryTheory.BaseChange.edgeComparison`: the comparison of an edge, out of which the
  derived isomorphism of the edge is built.

## Main results

* `Stacks.CategoryTheory.BaseChange.path_comp_comparison`: the composite of the `β` along a path,
  followed by the comparison of the composite derived extension.
* `Stacks.CategoryTheory.BaseChange.paths_comp_eq_app` and
  `Stacks.CategoryTheory.BaseChange.paths_comp_eq`: two paths differ by `Φ₂` of `t`.
* `Stacks.CategoryTheory.BaseChange.paths_comp_eq_congr`: the same when the second path is
  identified with the first one through a transport along an equality of indices.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.CategoryTheory.BaseChange

section Path

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

/-- **The comparison of an edge**: `Φ₀ ⋙ L` on a localized object is computed by the comparison
`ℓ` of `L` and the underived morphism `ρ`, read through `e₀` and `e₁`. -/
def edgeComparison (e₀ : Q₀ ⋙ Φ₀ ≅ A₀ ⋙ P₀) (L₁ : E₀ ⥤ E₁) (ℓ₁ : P₀ ⋙ L₁ ⟶ p₁ ⋙ P₁)
    (ρ₁ : A₀ ⋙ p₁ ⟶ x₁ ⋙ A₁) (e₁ : Q₁ ⋙ Φ₁ ≅ A₁ ⋙ P₁) :
    Q₀ ⋙ (Φ₀ ⋙ L₁) ⟶ (x₁ ⋙ Q₁) ⋙ Φ₁ :=
  (Functor.associator _ _ _).inv ≫ Functor.whiskerRight e₀.hom L₁ ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft A₀ ℓ₁ ≫
    (Functor.associator _ _ _).inv ≫ Functor.whiskerRight ρ₁ P₁ ≫
    (Functor.associator _ _ _).hom ≫ Functor.whiskerLeft x₁ e₁.inv ≫
    (Functor.associator _ _ _).inv

omit [Category C₂] [Category D₂] [Category H₂] [Category E₂] in
theorem edgeComparison_app (e₀ : Q₀ ⋙ Φ₀ ≅ A₀ ⋙ P₀) (L₁ : E₀ ⥤ E₁)
    (ℓ₁ : P₀ ⋙ L₁ ⟶ p₁ ⋙ P₁) (ρ₁ : A₀ ⋙ p₁ ⟶ x₁ ⋙ A₁) (e₁ : Q₁ ⋙ Φ₁ ≅ A₁ ⋙ P₁) (K : C₀) :
    (edgeComparison e₀ L₁ ℓ₁ ρ₁ e₁).app K =
      L₁.map (e₀.hom.app K) ≫ ℓ₁.app (A₀.obj K) ≫ P₁.map (ρ₁.app K) ≫ e₁.inv.app (x₁.obj K) := by
  simp [edgeComparison]

/-- **The composite of the derived base change isomorphisms along a path of two edges**, followed
by the comparison of the composite derived extension, is computed by the comparisons of the two
derived pullbacks followed by the composite of the underived isomorphisms. -/
theorem path_comp_comparison
    (hε : ∀ K, ε.app (Q₀.obj K) ≫ κ.app K =
      X₂.map (κ₁.app K) ≫ κ₂.app (x₁.obj K) ≫ Q₂.map (σ.app K))
    (hβ₁ : ∀ K, β₁.hom.app (Q₀.obj K) ≫ Φ₁.map (κ₁.app K) =
      L₁.map (e₀.hom.app K) ≫ ℓ₁.app (A₀.obj K) ≫ P₁.map (ρ₁.app K) ≫
        e₁.inv.app (x₁.obj K))
    (hβ₂ : ∀ K, β₂.hom.app (Q₁.obj K) ≫ Φ₂.map (κ₂.app K) =
      L₂.map (e₁.hom.app K) ≫ ℓ₂.app (A₁.obj K) ≫ P₂.map (ρ₂.app K) ≫
        e₂.inv.app (x₂.obj K))
    (K : C₀) :
    L₂.map (β₁.hom.app (Q₀.obj K)) ≫ β₂.hom.app (X₁.obj (Q₀.obj K)) ≫
        Φ₂.map (ε.app (Q₀.obj K)) ≫ Φ₂.map (κ.app K) =
      L₂.map (L₁.map (e₀.hom.app K)) ≫ L₂.map (ℓ₁.app (A₀.obj K)) ≫
        ℓ₂.app (p₁.obj (A₀.obj K)) ≫
        P₂.map (p₂.map (ρ₁.app K) ≫ ρ₂.app (x₁.obj K) ≫ A₂.map (σ.app K)) ≫
        e₂.inv.app (x.obj K) := by
  have s₁ : Φ₂.map (ε.app (Q₀.obj K)) ≫ Φ₂.map (κ.app K) =
      Φ₂.map (X₂.map (κ₁.app K)) ≫ Φ₂.map (κ₂.app (x₁.obj K)) ≫
        Φ₂.map (Q₂.map (σ.app K)) := by
    rw [← Φ₂.map_comp, hε, Φ₂.map_comp, Φ₂.map_comp]
  have s₂ : β₂.hom.app (X₁.obj (Q₀.obj K)) ≫ Φ₂.map (X₂.map (κ₁.app K)) =
      L₂.map (Φ₁.map (κ₁.app K)) ≫ β₂.hom.app (Q₁.obj (x₁.obj K)) :=
    (β₂.hom.naturality (κ₁.app K)).symm
  have s₄ : L₂.map (β₁.hom.app (Q₀.obj K)) ≫ L₂.map (Φ₁.map (κ₁.app K)) ≫
      L₂.map (e₁.hom.app (x₁.obj K)) =
      L₂.map (L₁.map (e₀.hom.app K)) ≫ L₂.map (ℓ₁.app (A₀.obj K)) ≫
        L₂.map (P₁.map (ρ₁.app K)) := by
    simp only [← L₂.map_comp, ← Category.assoc]
    rw [hβ₁ K]
    simp only [Category.assoc, Iso.inv_hom_id_app, Functor.comp_obj, Category.comp_id]
  have s₅ : L₂.map (P₁.map (ρ₁.app K)) ≫ ℓ₂.app (A₁.obj (x₁.obj K)) =
      ℓ₂.app (p₁.obj (A₀.obj K)) ≫ P₂.map (p₂.map (ρ₁.app K)) :=
    ℓ₂.naturality (ρ₁.app K)
  have s₆ : e₂.inv.app (x₂.obj (x₁.obj K)) ≫ Φ₂.map (Q₂.map (σ.app K)) =
      P₂.map (A₂.map (σ.app K)) ≫ e₂.inv.app (x.obj K) :=
    (e₂.inv.naturality (σ.app K)).symm
  have hβ₂' : β₂.hom.app (Q₁.obj (x₁.obj K)) ≫ Φ₂.map (κ₂.app (x₁.obj K)) =
      L₂.map (e₁.hom.app (x₁.obj K)) ≫ ℓ₂.app (A₁.obj (x₁.obj K)) ≫
        P₂.map (ρ₂.app (x₁.obj K)) ≫ e₂.inv.app (x₂.obj (x₁.obj K)) := hβ₂ (x₁.obj K)
  rw [s₁, reassoc_of% s₂, reassoc_of% hβ₂', s₆, reassoc_of% s₄, reassoc_of% s₅]
  simp only [Functor.map_comp, Category.assoc]

end Path

section TwoPaths

variable {C₀ C₁ C₂ C₁' D₀ D₁ D₂ D₁' H₀ H₁ H₂ H₁' E₀ E₁ E₂ E₁' : Type*} [Category C₀]
  [Category C₁] [Category C₂] [Category C₁'] [Category D₀] [Category D₁] [Category D₂]
  [Category D₁'] [Category H₀] [Category H₁] [Category H₂] [Category H₁'] [Category E₀]
  [Category E₁] [Category E₂] [Category E₁']
  {Q₀ : C₀ ⥤ D₀} {Q₁ : C₁ ⥤ D₁} {Q₂ : C₂ ⥤ D₂} {Q₁' : C₁' ⥤ D₁'}
  {P₀ : H₀ ⥤ E₀} {P₁ : H₁ ⥤ E₁} {P₂ : H₂ ⥤ E₂} {P₁' : H₁' ⥤ E₁'}
  {A₀ : C₀ ⥤ H₀} {A₁ : C₁ ⥤ H₁} {A₂ : C₂ ⥤ H₂} {A₁' : C₁' ⥤ H₁'}
  {Φ₀ : D₀ ⥤ E₀} {Φ₁ : D₁ ⥤ E₁} {Φ₂ : D₂ ⥤ E₂} {Φ₁' : D₁' ⥤ E₁'}
  {e₀ : Q₀ ⋙ Φ₀ ≅ A₀ ⋙ P₀} {e₁ : Q₁ ⋙ Φ₁ ≅ A₁ ⋙ P₁} {e₂ : Q₂ ⋙ Φ₂ ≅ A₂ ⋙ P₂}
  {e₁' : Q₁' ⋙ Φ₁' ≅ A₁' ⋙ P₁'}
  {x₁ : C₀ ⥤ C₁} {x₂ : C₁ ⥤ C₂} {x₁' : C₀ ⥤ C₁'} {x₂' : C₁' ⥤ C₂} {x : C₀ ⥤ C₂}
  {X₁ : D₀ ⥤ D₁} {X₂ : D₁ ⥤ D₂} {X₁' : D₀ ⥤ D₁'} {X₂' : D₁' ⥤ D₂} {X : D₀ ⥤ D₂}
  {κ₁ : Q₀ ⋙ X₁ ⟶ x₁ ⋙ Q₁} {κ₂ : Q₁ ⋙ X₂ ⟶ x₂ ⋙ Q₂} {κ₁' : Q₀ ⋙ X₁' ⟶ x₁' ⋙ Q₁'}
  {κ₂' : Q₁' ⋙ X₂' ⟶ x₂' ⋙ Q₂} {κ : Q₀ ⋙ X ⟶ x ⋙ Q₂}
  {σ : x₁ ⋙ x₂ ⟶ x} {σ' : x₁' ⋙ x₂' ⟶ x} {ε : X₁ ⋙ X₂ ⟶ X} {ε' : X₁' ⋙ X₂' ⟶ X}
  {p₁ : H₀ ⥤ H₁} {p₂ : H₁ ⥤ H₂} {p₁' : H₀ ⥤ H₁'} {p₂' : H₁' ⥤ H₂} {pc : H₀ ⥤ H₂}
  {L₁ : E₀ ⥤ E₁} {L₂ : E₁ ⥤ E₂} {L₁' : E₀ ⥤ E₁'} {L₂' : E₁' ⥤ E₂} {Lc : E₀ ⥤ E₂}
  {ℓ₁ : P₀ ⋙ L₁ ⟶ p₁ ⋙ P₁} {ℓ₂ : P₁ ⋙ L₂ ⟶ p₂ ⋙ P₂} {ℓ₁' : P₀ ⋙ L₁' ⟶ p₁' ⋙ P₁'}
  {ℓ₂' : P₁' ⋙ L₂' ⟶ p₂' ⋙ P₂} {ℓc : P₀ ⋙ Lc ⟶ pc ⋙ P₂}
  {ρ₁ : A₀ ⋙ p₁ ⟶ x₁ ⋙ A₁} {ρ₂ : A₁ ⋙ p₂ ⟶ x₂ ⋙ A₂} {ρ₁' : A₀ ⋙ p₁' ⟶ x₁' ⋙ A₁'}
  {ρ₂' : A₁' ⋙ p₂' ⟶ x₂' ⋙ A₂}
  {β₁ : Φ₀ ⋙ L₁ ≅ X₁ ⋙ Φ₁} {β₂ : Φ₁ ⋙ L₂ ≅ X₂ ⋙ Φ₂} {β₁' : Φ₀ ⋙ L₁' ≅ X₁' ⋙ Φ₁'}
  {β₂' : Φ₁' ⋙ L₂' ≅ X₂' ⋙ Φ₂}
  {g : L₁ ⋙ L₂ ≅ Lc} {g' : L₁' ⋙ L₂' ≅ Lc} {γ : p₁ ⋙ p₂ ≅ pc} {γ' : p₁' ⋙ p₂' ≅ pc}
  {t : 𝟭 D₂ ⟶ 𝟭 D₂} {τ : 𝟭 C₂ ⟶ 𝟭 C₂}

omit [Category C₀] [Category C₁] [Category C₂] [Category C₁'] [Category D₀] [Category D₁]
  [Category D₂] [Category D₁'] [Category H₁] [Category E₁] in
/-- The comparison of a composite identification `g ≪≫ e` of derived pullbacks with the
underived one, from those of `g` and `e`. -/
theorem trans_hom_app_comparison {Ld : E₀ ⥤ E₂} {pd : H₀ ⥤ H₂} {ℓd : P₀ ⋙ Ld ⟶ pd ⋙ P₂}
    (g₁ : L₁' ⋙ L₂' ≅ Ld) (g₂ : Ld ≅ Lc) (γ₁ : p₁' ⋙ p₂' ≅ pd) (γ₂ : pd ≅ pc)
    (h₁ : ∀ M, g₁.hom.app (P₀.obj M) ≫ ℓd.app M =
      L₂'.map (ℓ₁'.app M) ≫ ℓ₂'.app (p₁'.obj M) ≫ P₂.map (γ₁.hom.app M))
    (h₂ : ∀ M, g₂.hom.app (P₀.obj M) ≫ ℓc.app M = ℓd.app M ≫ P₂.map (γ₂.hom.app M)) (M : H₀) :
    (g₁ ≪≫ g₂).hom.app (P₀.obj M) ≫ ℓc.app M =
      L₂'.map (ℓ₁'.app M) ≫ ℓ₂'.app (p₁'.obj M) ≫ P₂.map ((γ₁ ≪≫ γ₂).hom.app M) := by
  simp only [Iso.trans_hom, NatTrans.comp_app, Category.assoc, h₂ M, reassoc_of% (h₁ M),
    Functor.map_comp]

/-- Naturality of a comparison `g` of derived pullbacks, rewritten through the underived one. -/
private theorem comp_map_comparison {Lx : E₀ ⥤ E₁} {Ly : E₁ ⥤ E₂} {px : H₀ ⥤ H₁} {py : H₁ ⥤ H₂}
    {ℓx : P₀ ⋙ Lx ⟶ px ⋙ P₁} {ℓy : P₁ ⋙ Ly ⟶ py ⋙ P₂} (g : Lx ⋙ Ly ≅ Lc) (γ : px ⋙ py ≅ pc)
    (hg : ∀ M, g.hom.app (P₀.obj M) ≫ ℓc.app M =
      Ly.map (ℓx.app M) ≫ ℓy.app (px.obj M) ≫ P₂.map (γ.hom.app M))
    {N : E₀} {M : H₀} (f : N ⟶ P₀.obj M) :
    Ly.map (Lx.map f) ≫ Ly.map (ℓx.app M) ≫ ℓy.app (px.obj M) =
      g.hom.app N ≫ Lc.map f ≫ ℓc.app M ≫ P₂.map (γ.inv.app M) := by
  have hn₀ := g.hom.naturality f
  dsimp only [Functor.comp_obj, Functor.comp_map] at hn₀ ⊢
  rw [← reassoc_of% hn₀, reassoc_of% (hg M)]
  simp only [← P₂.map_comp, Iso.hom_inv_id_app, Functor.comp_obj,
    CategoryTheory.Functor.map_id, Category.comp_id]

/-- **Two paths of derived base change isomorphisms differ by `Φ₂` of `t`** at `Q₀ K`, after the
comparison of the composite derived extension, as soon as the underived composites differ by `τ`,
which induces `t`. -/
theorem paths_comp_eq_app
    (ht : ∀ K, e₂.inv.app K ≫ Φ₂.map (t.app (Q₂.obj K)) = P₂.map (A₂.map (τ.app K)) ≫
      e₂.inv.app K)
    (hg : ∀ M, g.hom.app (P₀.obj M) ≫ ℓc.app M =
      L₂.map (ℓ₁.app M) ≫ ℓ₂.app (p₁.obj M) ≫ P₂.map (γ.hom.app M))
    (hg' : ∀ M, g'.hom.app (P₀.obj M) ≫ ℓc.app M =
      L₂'.map (ℓ₁'.app M) ≫ ℓ₂'.app (p₁'.obj M) ≫ P₂.map (γ'.hom.app M))
    (hρ : ∀ K, γ.inv.app (A₀.obj K) ≫ p₂.map (ρ₁.app K) ≫ ρ₂.app (x₁.obj K) ≫
        A₂.map (σ.app K) =
      γ'.inv.app (A₀.obj K) ≫ p₂'.map (ρ₁'.app K) ≫ ρ₂'.app (x₁'.obj K) ≫
        A₂.map (σ'.app K) ≫ A₂.map (τ.app (x.obj K)))
    (hε : ∀ K, ε.app (Q₀.obj K) ≫ κ.app K =
      X₂.map (κ₁.app K) ≫ κ₂.app (x₁.obj K) ≫ Q₂.map (σ.app K))
    (hβ₁ : ∀ K, β₁.hom.app (Q₀.obj K) ≫ Φ₁.map (κ₁.app K) =
      L₁.map (e₀.hom.app K) ≫ ℓ₁.app (A₀.obj K) ≫ P₁.map (ρ₁.app K) ≫
        e₁.inv.app (x₁.obj K))
    (hβ₂ : ∀ K, β₂.hom.app (Q₁.obj K) ≫ Φ₂.map (κ₂.app K) =
      L₂.map (e₁.hom.app K) ≫ ℓ₂.app (A₁.obj K) ≫ P₂.map (ρ₂.app K) ≫
        e₂.inv.app (x₂.obj K))
    (hε' : ∀ K, ε'.app (Q₀.obj K) ≫ κ.app K =
      X₂'.map (κ₁'.app K) ≫ κ₂'.app (x₁'.obj K) ≫ Q₂.map (σ'.app K))
    (hβ₁' : ∀ K, β₁'.hom.app (Q₀.obj K) ≫ Φ₁'.map (κ₁'.app K) =
      L₁'.map (e₀.hom.app K) ≫ ℓ₁'.app (A₀.obj K) ≫ P₁'.map (ρ₁'.app K) ≫
        e₁'.inv.app (x₁'.obj K))
    (hβ₂' : ∀ K, β₂'.hom.app (Q₁'.obj K) ≫ Φ₂.map (κ₂'.app K) =
      L₂'.map (e₁'.hom.app K) ≫ ℓ₂'.app (A₁'.obj K) ≫ P₂.map (ρ₂'.app K) ≫
        e₂.inv.app (x₂'.obj K))
    (K : C₀) :
    (L₂.map (β₁.hom.app (Q₀.obj K)) ≫ β₂.hom.app (X₁.obj (Q₀.obj K)) ≫
        Φ₂.map (ε.app (Q₀.obj K))) ≫ Φ₂.map (κ.app K) =
      (g.hom.app (Φ₀.obj (Q₀.obj K)) ≫ g'.inv.app (Φ₀.obj (Q₀.obj K)) ≫
        L₂'.map (β₁'.hom.app (Q₀.obj K)) ≫ β₂'.hom.app (X₁'.obj (Q₀.obj K)) ≫
        Φ₂.map (ε'.app (Q₀.obj K)) ≫ Φ₂.map (t.app (X.obj (Q₀.obj K)))) ≫
          Φ₂.map (κ.app K) := by
  have ha := path_comp_comparison hε hβ₁ hβ₂ K
  have hb := path_comp_comparison hε' hβ₁' hβ₂' K
  have hn : Φ₂.map (t.app (X.obj (Q₀.obj K))) ≫ Φ₂.map (κ.app K) =
      Φ₂.map (κ.app K) ≫ Φ₂.map (t.app (Q₂.obj (x.obj K))) := by
    rw [← Φ₂.map_comp, ← Φ₂.map_comp]
    exact congrArg Φ₂.map (t.naturality (κ.app K)).symm
  simp only [Category.assoc] at ha hb ⊢
  rw [ha, hn, reassoc_of% hb, reassoc_of% (comp_map_comparison g γ hg (e₀.hom.app K)),
    reassoc_of% (comp_map_comparison g' γ' hg' (e₀.hom.app K)), Iso.inv_hom_id_app_assoc,
    ht, ← P₂.map_comp_assoc, ← P₂.map_comp_assoc, ← P₂.map_comp_assoc]
  have := hρ K
  simp only [Category.assoc] at this ⊢
  rw [this]

/-- **Two paths of derived base change isomorphisms differ by `Φ₂` of `t`**, at every object,
when `X ⋙ Φ₂` is a left derived functor through the comparison `κ`. -/
theorem paths_comp_eq (W : MorphismProperty C₀) [Q₀.IsLocalization W]
    (hX : (X ⋙ Φ₂).IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight κ Φ₂) W)
    (ht : ∀ K, e₂.inv.app K ≫ Φ₂.map (t.app (Q₂.obj K)) = P₂.map (A₂.map (τ.app K)) ≫
      e₂.inv.app K)
    (hg : ∀ M, g.hom.app (P₀.obj M) ≫ ℓc.app M =
      L₂.map (ℓ₁.app M) ≫ ℓ₂.app (p₁.obj M) ≫ P₂.map (γ.hom.app M))
    (hg' : ∀ M, g'.hom.app (P₀.obj M) ≫ ℓc.app M =
      L₂'.map (ℓ₁'.app M) ≫ ℓ₂'.app (p₁'.obj M) ≫ P₂.map (γ'.hom.app M))
    (hρ : ∀ K, γ.inv.app (A₀.obj K) ≫ p₂.map (ρ₁.app K) ≫ ρ₂.app (x₁.obj K) ≫
        A₂.map (σ.app K) =
      γ'.inv.app (A₀.obj K) ≫ p₂'.map (ρ₁'.app K) ≫ ρ₂'.app (x₁'.obj K) ≫
        A₂.map (σ'.app K) ≫ A₂.map (τ.app (x.obj K)))
    (hε : ∀ K, ε.app (Q₀.obj K) ≫ κ.app K =
      X₂.map (κ₁.app K) ≫ κ₂.app (x₁.obj K) ≫ Q₂.map (σ.app K))
    (hβ₁ : ∀ K, β₁.hom.app (Q₀.obj K) ≫ Φ₁.map (κ₁.app K) =
      L₁.map (e₀.hom.app K) ≫ ℓ₁.app (A₀.obj K) ≫ P₁.map (ρ₁.app K) ≫
        e₁.inv.app (x₁.obj K))
    (hβ₂ : ∀ K, β₂.hom.app (Q₁.obj K) ≫ Φ₂.map (κ₂.app K) =
      L₂.map (e₁.hom.app K) ≫ ℓ₂.app (A₁.obj K) ≫ P₂.map (ρ₂.app K) ≫
        e₂.inv.app (x₂.obj K))
    (hε' : ∀ K, ε'.app (Q₀.obj K) ≫ κ.app K =
      X₂'.map (κ₁'.app K) ≫ κ₂'.app (x₁'.obj K) ≫ Q₂.map (σ'.app K))
    (hβ₁' : ∀ K, β₁'.hom.app (Q₀.obj K) ≫ Φ₁'.map (κ₁'.app K) =
      L₁'.map (e₀.hom.app K) ≫ ℓ₁'.app (A₀.obj K) ≫ P₁'.map (ρ₁'.app K) ≫
        e₁'.inv.app (x₁'.obj K))
    (hβ₂' : ∀ K, β₂'.hom.app (Q₁'.obj K) ≫ Φ₂.map (κ₂'.app K) =
      L₂'.map (e₁'.hom.app K) ≫ ℓ₂'.app (A₁'.obj K) ≫ P₂.map (ρ₂'.app K) ≫
        e₂.inv.app (x₂'.obj K))
    (N : D₀) :
    L₂.map (β₁.hom.app N) ≫ β₂.hom.app (X₁.obj N) ≫ Φ₂.map (ε.app N) =
      g.hom.app (Φ₀.obj N) ≫ g'.inv.app (Φ₀.obj N) ≫ L₂'.map (β₁'.hom.app N) ≫
        β₂'.hom.app (X₁'.obj N) ≫ Φ₂.map (ε'.app N) ≫ Φ₂.map (t.app (X.obj N)) := by
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
  let γ₂ : Φ₀ ⋙ L₁ ⋙ L₂ ⟶ X ⋙ Φ₂ :=
    { app := fun N => g.hom.app (Φ₀.obj N) ≫ g'.inv.app (Φ₀.obj N) ≫ L₂'.map (β₁'.hom.app N) ≫
        β₂'.hom.app (X₁'.obj N) ≫ Φ₂.map (ε'.app N) ≫ Φ₂.map (t.app (X.obj N))
      naturality := fun N N' u => by
        have h₀ := g.hom.naturality (Φ₀.map u)
        have h₀' := g'.inv.naturality (Φ₀.map u)
        have h₁ := β₁'.hom.naturality u
        have h₂ := β₂'.hom.naturality (X₁'.map u)
        have h₃ := ε'.naturality u
        have h₄ := t.naturality (X.map u)
        dsimp only [Functor.comp_obj, Functor.comp_map, Functor.id_obj, Functor.id_map]
          at h₀ h₀' h₁ h₂ h₃ h₄ ⊢
        rw [reassoc_of% h₀, reassoc_of% h₀', ← L₂'.map_comp_assoc, h₁, L₂'.map_comp_assoc,
          reassoc_of% h₂, ← Φ₂.map_comp_assoc, h₃, Φ₂.map_comp_assoc, ← Φ₂.map_comp (X.map u), h₄,
          Φ₂.map_comp]
        simp only [Category.assoc] }
  have key : γ₁ = γ₂ := by
    haveI := hX
    refine Functor.leftDerived_ext (X ⋙ Φ₂) ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight κ Φ₂) W _ γ₁ γ₂ (NatTrans.ext (funext fun K => ?_))
    simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.associator_inv_app,
      Functor.whiskerRight_app, Category.id_comp]
    exact paths_comp_eq_app ht hg hg' hρ hε hβ₁ hβ₂ hε' hβ₁' hβ₂' K
  exact congrArg (fun γ => NatTrans.app γ N) key

/-- `Stacks.CategoryTheory.BaseChange.paths_comp_eq` with the identification of the second
path's derived pullbacks given as a composite `g₁ ≪≫ g₂`, each piece compatible with the
underived ones. -/
theorem paths_comp_eq_trans {Ld : E₀ ⥤ E₂} {pd : H₀ ⥤ H₂} {ℓd : P₀ ⋙ Ld ⟶ pd ⋙ P₂}
    {g₁ : L₁' ⋙ L₂' ≅ Ld} {g₂ : Ld ≅ Lc} {γ₁ : p₁' ⋙ p₂' ≅ pd} {γ₂ : pd ≅ pc}
    (W : MorphismProperty C₀) [Q₀.IsLocalization W]
    (hX : (X ⋙ Φ₂).IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight κ Φ₂) W)
    (ht : ∀ K, e₂.inv.app K ≫ Φ₂.map (t.app (Q₂.obj K)) = P₂.map (A₂.map (τ.app K)) ≫
      e₂.inv.app K)
    (hg : ∀ M, g.hom.app (P₀.obj M) ≫ ℓc.app M =
      L₂.map (ℓ₁.app M) ≫ ℓ₂.app (p₁.obj M) ≫ P₂.map (γ.hom.app M))
    (h₁ : ∀ M, g₁.hom.app (P₀.obj M) ≫ ℓd.app M =
      L₂'.map (ℓ₁'.app M) ≫ ℓ₂'.app (p₁'.obj M) ≫ P₂.map (γ₁.hom.app M))
    (h₂ : ∀ M, g₂.hom.app (P₀.obj M) ≫ ℓc.app M = ℓd.app M ≫ P₂.map (γ₂.hom.app M))
    (hρ : ∀ K, γ.inv.app (A₀.obj K) ≫ p₂.map (ρ₁.app K) ≫ ρ₂.app (x₁.obj K) ≫
        A₂.map (σ.app K) =
      (γ₁ ≪≫ γ₂).inv.app (A₀.obj K) ≫ p₂'.map (ρ₁'.app K) ≫ ρ₂'.app (x₁'.obj K) ≫
        A₂.map (σ'.app K) ≫ A₂.map (τ.app (x.obj K)))
    (hε : ∀ K, ε.app (Q₀.obj K) ≫ κ.app K =
      X₂.map (κ₁.app K) ≫ κ₂.app (x₁.obj K) ≫ Q₂.map (σ.app K))
    (hβ₁ : ∀ K, β₁.hom.app (Q₀.obj K) ≫ Φ₁.map (κ₁.app K) =
      L₁.map (e₀.hom.app K) ≫ ℓ₁.app (A₀.obj K) ≫ P₁.map (ρ₁.app K) ≫
        e₁.inv.app (x₁.obj K))
    (hβ₂ : ∀ K, β₂.hom.app (Q₁.obj K) ≫ Φ₂.map (κ₂.app K) =
      L₂.map (e₁.hom.app K) ≫ ℓ₂.app (A₁.obj K) ≫ P₂.map (ρ₂.app K) ≫
        e₂.inv.app (x₂.obj K))
    (hε' : ∀ K, ε'.app (Q₀.obj K) ≫ κ.app K =
      X₂'.map (κ₁'.app K) ≫ κ₂'.app (x₁'.obj K) ≫ Q₂.map (σ'.app K))
    (hβ₁' : ∀ K, β₁'.hom.app (Q₀.obj K) ≫ Φ₁'.map (κ₁'.app K) =
      L₁'.map (e₀.hom.app K) ≫ ℓ₁'.app (A₀.obj K) ≫ P₁'.map (ρ₁'.app K) ≫
        e₁'.inv.app (x₁'.obj K))
    (hβ₂' : ∀ K, β₂'.hom.app (Q₁'.obj K) ≫ Φ₂.map (κ₂'.app K) =
      L₂'.map (e₁'.hom.app K) ≫ ℓ₂'.app (A₁'.obj K) ≫ P₂.map (ρ₂'.app K) ≫
        e₂.inv.app (x₂'.obj K))
    (N : D₀) :
    L₂.map (β₁.hom.app N) ≫ β₂.hom.app (X₁.obj N) ≫ Φ₂.map (ε.app N) =
      g.hom.app (Φ₀.obj N) ≫ (g₁ ≪≫ g₂).inv.app (Φ₀.obj N) ≫ L₂'.map (β₁'.hom.app N) ≫
        β₂'.hom.app (X₁'.obj N) ≫ Φ₂.map (ε'.app N) ≫ Φ₂.map (t.app (X.obj N)) :=
  paths_comp_eq W hX ht hg (trans_hom_app_comparison g₁ g₂ γ₁ γ₂ h₁ h₂) hρ hε hβ₁ hβ₂ hε' hβ₁'
    hβ₂' N

omit [Category C₁'] [Category D₁'] [Category H₁'] [Category E₁'] in
/-- The transport of an identification of derived pullbacks along an equality of indices is
induced by the transport of the underived ones. -/
theorem eqToIso_hom_app_comparison {T : Type*} (Lf : T → (E₀ ⥤ E₂)) (pf : T → (H₀ ⥤ H₂))
    (ℓf : ∀ s, P₀ ⋙ Lf s ⟶ pf s ⋙ P₂) {s s' : T} (w : s = s') (M : H₀) :
    (eqToIso (congrArg Lf w)).hom.app (P₀.obj M) ≫ (ℓf s').app M =
      (ℓf s).app M ≫ P₂.map ((eqToIso (congrArg pf w)).hom.app M) := by
  subst w
  simp

/-- `Stacks.CategoryTheory.BaseChange.paths_comp_eq_trans` when the derived pullbacks form a
family `Lf` indexed by `T` with comparisons `ℓf`, the two paths compose to the members at `s` and
`s'`, and the second identification is the transport along `w : s = s'`. -/
theorem paths_comp_eq_congr {T : Type*} (Lf : T → (E₀ ⥤ E₂)) (pf : T → (H₀ ⥤ H₂))
    (ℓf : ∀ s, P₀ ⋙ Lf s ⟶ pf s ⋙ P₂) {s s' : T} (w : s = s')
    {g : L₁ ⋙ L₂ ≅ Lf s'} {γ : p₁ ⋙ p₂ ≅ pf s'} {g₁ : L₁' ⋙ L₂' ≅ Lf s}
    {γ₁ : p₁' ⋙ p₂' ≅ pf s} {g' : L₁' ⋙ L₂' ≅ Lf s'} {γ' : p₁' ⋙ p₂' ≅ pf s'}
    (hg' : g' = g₁ ≪≫ eqToIso (congrArg Lf w)) (hγ' : γ' = γ₁ ≪≫ eqToIso (congrArg pf w))
    (W : MorphismProperty C₀) [Q₀.IsLocalization W]
    (hX : (X ⋙ Φ₂).IsLeftDerivedFunctor ((Functor.associator _ _ _).inv ≫
      Functor.whiskerRight κ Φ₂) W)
    (ht : ∀ K, e₂.inv.app K ≫ Φ₂.map (t.app (Q₂.obj K)) = P₂.map (A₂.map (τ.app K)) ≫
      e₂.inv.app K)
    (hg : ∀ M, g.hom.app (P₀.obj M) ≫ (ℓf s').app M =
      L₂.map (ℓ₁.app M) ≫ ℓ₂.app (p₁.obj M) ≫ P₂.map (γ.hom.app M))
    (h₁ : ∀ M, g₁.hom.app (P₀.obj M) ≫ (ℓf s).app M =
      L₂'.map (ℓ₁'.app M) ≫ ℓ₂'.app (p₁'.obj M) ≫ P₂.map (γ₁.hom.app M))
    (hρ : ∀ K, γ.inv.app (A₀.obj K) ≫ p₂.map (ρ₁.app K) ≫ ρ₂.app (x₁.obj K) ≫
        A₂.map (σ.app K) =
      γ'.inv.app (A₀.obj K) ≫ p₂'.map (ρ₁'.app K) ≫
        ρ₂'.app (x₁'.obj K) ≫ A₂.map (σ'.app K) ≫ A₂.map (τ.app (x.obj K)))
    (hε : ∀ K, ε.app (Q₀.obj K) ≫ κ.app K =
      X₂.map (κ₁.app K) ≫ κ₂.app (x₁.obj K) ≫ Q₂.map (σ.app K))
    (hβ₁ : ∀ K, β₁.hom.app (Q₀.obj K) ≫ Φ₁.map (κ₁.app K) =
      L₁.map (e₀.hom.app K) ≫ ℓ₁.app (A₀.obj K) ≫ P₁.map (ρ₁.app K) ≫
        e₁.inv.app (x₁.obj K))
    (hβ₂ : ∀ K, β₂.hom.app (Q₁.obj K) ≫ Φ₂.map (κ₂.app K) =
      L₂.map (e₁.hom.app K) ≫ ℓ₂.app (A₁.obj K) ≫ P₂.map (ρ₂.app K) ≫
        e₂.inv.app (x₂.obj K))
    (hε' : ∀ K, ε'.app (Q₀.obj K) ≫ κ.app K =
      X₂'.map (κ₁'.app K) ≫ κ₂'.app (x₁'.obj K) ≫ Q₂.map (σ'.app K))
    (hβ₁' : ∀ K, β₁'.hom.app (Q₀.obj K) ≫ Φ₁'.map (κ₁'.app K) =
      L₁'.map (e₀.hom.app K) ≫ ℓ₁'.app (A₀.obj K) ≫ P₁'.map (ρ₁'.app K) ≫
        e₁'.inv.app (x₁'.obj K))
    (hβ₂' : ∀ K, β₂'.hom.app (Q₁'.obj K) ≫ Φ₂.map (κ₂'.app K) =
      L₂'.map (e₁'.hom.app K) ≫ ℓ₂'.app (A₁'.obj K) ≫ P₂.map (ρ₂'.app K) ≫
        e₂.inv.app (x₂'.obj K))
    (N : D₀) :
    L₂.map (β₁.hom.app N) ≫ β₂.hom.app (X₁.obj N) ≫ Φ₂.map (ε.app N) =
      g.hom.app (Φ₀.obj N) ≫ g'.inv.app (Φ₀.obj N) ≫
        L₂'.map (β₁'.hom.app N) ≫ β₂'.hom.app (X₁'.obj N) ≫ Φ₂.map (ε'.app N) ≫
        Φ₂.map (t.app (X.obj N)) := by
  subst hg' hγ'
  exact paths_comp_eq_trans W hX ht hg h₁ (eqToIso_hom_app_comparison Lf pf ℓf w) hρ hε hβ₁ hβ₂
    hε' hβ₁' hβ₂' N

end TwoPaths


end Stacks.CategoryTheory.BaseChange
