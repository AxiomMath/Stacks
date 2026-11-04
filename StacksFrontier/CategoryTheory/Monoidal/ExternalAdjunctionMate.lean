module

public import Mathlib.CategoryTheory.Monoidal.Functor

/-!
# The two-variable mate of a pair of comparisons of right adjoints

Let `L ⊣ R` be an adjunction with `R : E ⥤ A` lax monoidal, and let `L₁ ⊣ R₁`, `L₂ ⊣ R₂` be two
further adjunctions with the same target `E`. Given functors `S₁ : A₁ ⥤ A`, `S₂ : A₂ ⥤ A` and
natural transformations `α₁ : R₁ ⋙ S₁ ⟶ R`, `α₂ : R₂ ⋙ S₂ ⟶ R`, there is a canonical morphism

`L (S₁ M₁ ⊗ S₂ M₂) ⟶ L₁ M₁ ⊗ L₂ M₂`,

the *two-variable mate* `CategoryTheory.Adjunction.externalMate`. It is the morphism adjoint to

`S₁ M₁ ⊗ S₂ M₂ ⟶ R (L₁ M₁) ⊗ R (L₂ M₂) ⟶ R (L₁ M₁ ⊗ L₂ M₂)`,

the first map being `α₁ ∘ S₁(η₁)` tensored with `α₂ ∘ S₂(η₂)` and the second the tensorator
of `R`.

For a product of sites, with `A = ((C₁ × C₂)ᵒᵖ ⥤ E)`, `A_i = (C_iᵒᵖ ⥤ E)`, `S_i` the inverse
image along the `i`-th projection, `L` and `L_i` the (derived) lower shriek to the point, and `R`,
`R_i` the inverse images of the point, the two-variable mate is the comparison

`π_!(g₁^{-1}K₁ ⊗ g₂^{-1}K₂) ⟶ π_{1,!}K₁ ⊗ π_{2,!}K₂`

of Stacks 08QB. It is not the oplax tensorator `δ L` of the lower shriek on the product site,
whose target is `π_!(g₁^{-1}K₁) ⊗ π_!(g₂^{-1}K₂)`: it is `δ L` followed by the tensor product of
the two one-variable mates of `α₁` and `α₂`, the comparisons of Stacks 08QA for the two
projections.

## Main definitions

* `CategoryTheory.Adjunction.externalMate`: the two-variable mate
  `L (S₁ M₁ ⊗ S₂ M₂) ⟶ L₁ M₁ ⊗ L₂ M₂`.

## Main results

* `CategoryTheory.Adjunction.unit_comp_map_externalMate`: its defining property, which
  characterises it uniquely.
* `CategoryTheory.Adjunction.externalMate_eq_δ_comp`: the two-variable mate is the canonical
  oplax tensorator `δ L` followed by the tensor product of any two morphisms satisfying the
  defining property of the one-variable mates of `α₁` and `α₂`.
* `CategoryTheory.Adjunction.isIso_δ_of_isIso_externalMate` and
  `CategoryTheory.Adjunction.isIso_externalMate_of_isIso_δ`: the two consequences of that
  factorisation, when the two one-variable comparisons are invertible.

## References

* [Stacks Project, Tag 08QB](https://stacks.math.columbia.edu/tag/08QB)
* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

universe v₁ v₂ v vE u₁ u₂ u uE

variable {A₁ : Type u₁} [Category.{v₁} A₁] {A₂ : Type u₂} [Category.{v₂} A₂]
  {A : Type u} [Category.{v} A] {E : Type uE} [Category.{vE} E]
  [MonoidalCategory A] [MonoidalCategory E]
  {L : A ⥤ E} {R : E ⥤ A} (adj : L ⊣ R) [R.LaxMonoidal]
  {L₁ : A₁ ⥤ E} {R₁ : E ⥤ A₁} (adj₁ : L₁ ⊣ R₁)
  {L₂ : A₂ ⥤ E} {R₂ : E ⥤ A₂} (adj₂ : L₂ ⊣ R₂)
  (S₁ : A₁ ⥤ A) (S₂ : A₂ ⥤ A) (α₁ : R₁ ⋙ S₁ ⟶ R) (α₂ : R₂ ⋙ S₂ ⟶ R)

/-- The two-variable mate of `α₁ : R₁ ⋙ S₁ ⟶ R` and `α₂ : R₂ ⋙ S₂ ⟶ R`: the morphism

`L (S₁ M₁ ⊗ S₂ M₂) ⟶ L₁ M₁ ⊗ L₂ M₂`

adjoint to the composite of `(α₁ ∘ S₁ η₁) ⊗ (α₂ ∘ S₂ η₂)` with the tensorator of `R`, where
`η₁` and `η₂` are the units of `adj₁` and `adj₂`. -/
def externalMate (M₁ : A₁) (M₂ : A₂) :
    L.obj (S₁.obj M₁ ⊗ S₂.obj M₂) ⟶ L₁.obj M₁ ⊗ L₂.obj M₂ :=
  (adj.homEquiv _ _).symm
    (((S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁)) ⊗ₘ
        (S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂))) ≫ μ R (L₁.obj M₁) (L₂.obj M₂))

/-- The defining property of `CategoryTheory.Adjunction.externalMate`, written out with the unit
of `adj`; it characterises the two-variable mate uniquely. -/
@[reassoc]
lemma unit_comp_map_externalMate (M₁ : A₁) (M₂ : A₂) :
    adj.unit.app (S₁.obj M₁ ⊗ S₂.obj M₂) ≫
        R.map (externalMate adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁ M₂) =
      ((S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁)) ⊗ₘ
          (S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂))) ≫
        μ R (L₁.obj M₁) (L₂.obj M₂) :=
  (adj.homEquiv_unit _ _ _).symm.trans ((adj.homEquiv _ _).apply_symm_apply _)

section Oplax

variable [L.OplaxMonoidal] [adj.IsMonoidal]

/-- The two-variable mate factors through the canonical oplax tensorator of `L`: if `c₁` and `c₂`
satisfy the defining property of the one-variable mates of `α₁` and `α₂`, that is the property
`CategoryTheory.Adjunction.unit_comp_map_restrictionMate`, then

`externalMate = δ L (S₁ M₁) (S₂ M₂) ≫ (c₁ ⊗ c₂)`.

Here the oplax structure of `L` is the mate of the lax monoidal structure of `R`
(`adj.IsMonoidal`). -/
lemma externalMate_eq_δ_comp (M₁ : A₁) (M₂ : A₂)
    (c₁ : L.obj (S₁.obj M₁) ⟶ L₁.obj M₁) (c₂ : L.obj (S₂.obj M₂) ⟶ L₂.obj M₂)
    (hc₁ : adj.unit.app (S₁.obj M₁) ≫ R.map c₁ =
      S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁))
    (hc₂ : adj.unit.app (S₂.obj M₂) ≫ R.map c₂ =
      S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂)) :
    externalMate adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁ M₂ =
      δ L (S₁.obj M₁) (S₂.obj M₂) ≫ (c₁ ⊗ₘ c₂) := by
  apply (adj.homEquiv _ _).injective
  have hR : adj.homEquiv _ _ (δ L (S₁.obj M₁) (S₂.obj M₂) ≫ (c₁ ⊗ₘ c₂)) =
      ((S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁)) ⊗ₘ
          (S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂))) ≫
        μ R (L₁.obj M₁) (L₂.obj M₂) := by
    rw [homEquiv_unit, Functor.map_comp, ← Category.assoc, adj.unit_app_tensor_comp_map_δ,
      Category.assoc, ← μ_natural, ← Category.assoc, tensorHom_comp_tensorHom, hc₁, hc₂]
  rw [hR, homEquiv_unit, unit_comp_map_externalMate]

/-- The canonical oplax tensorator of `L` is invertible at `(S₁ M₁, S₂ M₂)` as soon as the
two-variable mate is invertible there and the two one-variable comparisons `c₁`, `c₂` are
invertible. -/
lemma isIso_δ_of_isIso_externalMate (M₁ : A₁) (M₂ : A₂)
    (c₁ : L.obj (S₁.obj M₁) ⟶ L₁.obj M₁) (c₂ : L.obj (S₂.obj M₂) ⟶ L₂.obj M₂)
    (hc₁ : adj.unit.app (S₁.obj M₁) ≫ R.map c₁ =
      S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁))
    (hc₂ : adj.unit.app (S₂.obj M₂) ≫ R.map c₂ =
      S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂))
    [IsIso c₁] [IsIso c₂] [IsIso (externalMate adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁ M₂)] :
    IsIso (δ L (S₁.obj M₁) (S₂.obj M₂)) := by
  have h : IsIso (δ L (S₁.obj M₁) (S₂.obj M₂) ≫ (c₁ ⊗ₘ c₂)) := by
    rw [← externalMate_eq_δ_comp adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁ M₂ c₁ c₂ hc₁ hc₂]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (c₁ ⊗ₘ c₂)

/-- The two-variable mate is invertible as soon as the canonical oplax tensorator of `L` is
invertible at `(S₁ M₁, S₂ M₂)` and the two one-variable comparisons `c₁`, `c₂` are invertible. -/
lemma isIso_externalMate_of_isIso_δ (M₁ : A₁) (M₂ : A₂)
    (c₁ : L.obj (S₁.obj M₁) ⟶ L₁.obj M₁) (c₂ : L.obj (S₂.obj M₂) ⟶ L₂.obj M₂)
    (hc₁ : adj.unit.app (S₁.obj M₁) ≫ R.map c₁ =
      S₁.map (adj₁.unit.app M₁) ≫ α₁.app (L₁.obj M₁))
    (hc₂ : adj.unit.app (S₂.obj M₂) ≫ R.map c₂ =
      S₂.map (adj₂.unit.app M₂) ≫ α₂.app (L₂.obj M₂))
    [IsIso c₁] [IsIso c₂] [IsIso (δ L (S₁.obj M₁) (S₂.obj M₂))] :
    IsIso (externalMate adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁ M₂) := by
  rw [externalMate_eq_δ_comp adj adj₁ adj₂ S₁ S₂ α₁ α₂ M₁ M₂ c₁ c₂ hc₁ hc₂]
  infer_instance

end Oplax

end CategoryTheory.Adjunction

end
