module

public import Mathlib.CategoryTheory.Iso
public import Mathlib.CategoryTheory.Functor.Basic
public import Mathlib.CategoryTheory.NatIso

/-!
# Two diagram chases behind the box Künneth map at single complexes

These are the two abstract steps of the reduction of the relative box map at single complexes to
the scheme Künneth map along a morphism of diagrams `τ`, every object and morphism a variable.

## Main results

* `Stacks.Cohomology.BoxKunnethFlat.isIso_of_crossing_chain`: invertibility of the relative map
  from invertibility of the scheme map, the crossing square, the naturality of the Künneth map
  and the identification of steps (4)–(5) with the crossing map up to an isomorphism.
* `Stacks.Cohomology.BoxKunnethFlat.comp_eq_of_crossing_naive`: that identification, from the
  naive crossing square and the identity of complexes at single complexes.
-/

@[expose] public section

open CategoryTheory

namespace Stacks.Cohomology.BoxKunnethFlat

/-- **Invertibility along a crossing.**  If `κₛ ≫ Rₛ(Tₛ)` is invertible, the crossing square
`c ≫ κₛ = κ₁ ≫ R(χ) ≫ c_W` holds with `c` invertible and `c_W : R_τ ⋙ R ≅ Rₛ`, the Künneth map is
natural along an isomorphism `σ`, and `l_σ ≫ B = χ ≫ R_τ(Tₛ) ≫ ε` with `ε` invertible, then
`κ₂ ≫ R(B)` is invertible. -/
theorem isIso_of_crossing_chain {C D E : Type*} [Category* C] [Category* D] [Category* E]
    (R : D ⥤ C) (Rτ : E ⥤ D) (Rs : E ⥤ C) (cW : Rτ ⋙ R ≅ Rs)
    {Ps P₁ P₂ : C} {T₀ T₁ : E} {Y₁ Y₂ Z : D}
    (κs : Ps ⟶ Rs.obj T₀) (Ts : T₀ ⟶ T₁) (hS : IsIso (κs ≫ Rs.map Ts))
    (c : P₁ ≅ Ps) (κ₁ : P₁ ⟶ R.obj Y₁) (χ : Y₁ ⟶ Rτ.obj T₀)
    (hcross : c.hom ≫ κs = κ₁ ≫ R.map χ ≫ cW.hom.app T₀)
    (σ : P₁ ≅ P₂) (κ₂ : P₂ ⟶ R.obj Y₂) (lσ : Y₁ ⟶ Y₂)
    (hnat : σ.hom ≫ κ₂ = κ₁ ≫ R.map lσ)
    (B : Y₂ ⟶ Z) (ε : Rτ.obj T₁ ≅ Z) (hCI : lσ ≫ B = χ ≫ Rτ.map Ts ≫ ε.hom) :
    IsIso (κ₂ ≫ R.map B) := by
  have hn : R.map (Rτ.map Ts) ≫ cW.hom.app T₁ = cW.hom.app T₀ ≫ Rs.map Ts :=
    cW.hom.naturality Ts
  have e : σ.hom ≫ κ₂ ≫ R.map B =
      ((c.hom ≫ κs ≫ Rs.map Ts) ≫ cW.inv.app T₁) ≫ R.map ε.hom := by
    rw [reassoc_of% hnat, ← R.map_comp, hCI, R.map_comp, R.map_comp, ← Category.assoc c.hom,
      hcross]
    simp only [Category.assoc, ← reassoc_of% hn, Iso.hom_inv_id_app_assoc]
  have : IsIso (σ.hom ≫ κ₂ ≫ R.map B) := by
    rw [e]
    have : IsIso (c.hom ≫ κs ≫ Rs.map Ts) := inferInstance
    infer_instance
  exact (isIso_comp_left_iff σ.hom _).mp this

/-- **Steps (4)–(5) against the crossing map.**  From the naive crossing square
`N₀ ≫ Q(n) ≫ π = l_π ≫ χ ≫ R_τ(Tₛ)`, the naturality `l_ψ ≫ N₂ = N₀ ≫ Q(m)`, the factorization
`B = N₂ ≫ Q(b)`, `l_π ≫ l_σ = l_ψ` with `l_π` invertible, and the identity of complexes
`m ≫ b = n ≫ θ`, the map `l_σ ≫ B` is the crossing map followed by `R_τ(Tₛ)` and an isomorphism. -/
theorem comp_eq_of_crossing_naive {C K E : Type*} [Category* C] [Category* K] [Category* E]
    (Q : K ⥤ C) (Rτ : E ⥤ C) {Y₀ Y₁ Y₂ : C} {A₀ A₁ A₂ A₃ : K} {T₀ T₁ : E}
    (N₀ : Y₀ ⟶ Q.obj A₀) (n : A₀ ⟶ A₁) (π : Q.obj A₁ ≅ Rτ.obj T₁)
    (lπ : Y₀ ≅ Y₁) (χ : Y₁ ⟶ Rτ.obj T₀) (Ts : T₀ ⟶ T₁)
    (hnaive : N₀ ≫ Q.map n ≫ π.hom = lπ.hom ≫ χ ≫ Rτ.map Ts)
    (lψ : Y₀ ⟶ Y₂) (N₂ : Y₂ ⟶ Q.obj A₂) (m : A₀ ⟶ A₂) (hN : lψ ≫ N₂ = N₀ ≫ Q.map m)
    (bb : A₂ ⟶ A₃) (B : Y₂ ⟶ Q.obj A₃) (hB : B = N₂ ≫ Q.map bb)
    (lσ : Y₁ ⟶ Y₂) (hlσ : lπ.hom ≫ lσ = lψ) (θ : A₁ ⟶ A₃) (hc : m ≫ bb = n ≫ θ) :
    lσ ≫ B = χ ≫ Rτ.map Ts ≫ π.inv ≫ Q.map θ := by
  rw [← cancel_epi lπ.hom]
  calc lπ.hom ≫ lσ ≫ B = lψ ≫ N₂ ≫ Q.map bb := by rw [reassoc_of% hlσ, hB]
    _ = N₀ ≫ Q.map m ≫ Q.map bb := by rw [reassoc_of% hN]
    _ = N₀ ≫ Q.map n ≫ Q.map θ := by rw [← Q.map_comp, hc, Q.map_comp]
    _ = (N₀ ≫ Q.map n ≫ π.hom) ≫ π.inv ≫ Q.map θ := by simp
    _ = lπ.hom ≫ χ ≫ Rτ.map Ts ≫ π.inv ≫ Q.map θ := by
      rw [hnaive, Category.assoc, Category.assoc]

end Stacks.Cohomology.BoxKunnethFlat

end
