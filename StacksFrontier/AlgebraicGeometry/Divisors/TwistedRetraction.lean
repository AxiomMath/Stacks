module

public import StacksFrontier.AlgebraicGeometry.Divisors.CanonicalSectionPairing

/-!
# Inverting a morphism up to a trivialising pairing

Let `C` be a symmetric monoidal category, let `ev : L ⊗ I ≅ 𝟙` exhibit `L` as a tensor inverse of
`I`, and let `iota : I ⟶ 𝟙` and `c : 𝟙 ⟶ L` be paired by `ev`. Given `lam : F ⟶ G` and a
morphism `nu : I ⊗ G ⟶ F` restricting along `lam` to multiplication by `iota` on `F`, there is an
explicit composite

`psi : G ⟶ F ⊗ L`   with   `lam ≫ psi = ` multiplication by `c`,

so `psi` inverts `lam` at the cost of one factor of `L`.

For the second canonical map of [Stacks, Tag 0G5G], `C` is the category of `𝒪_X`-modules on a
scheme, `I` is the ideal sheaf `ℐ_D` of an effective Cartier divisor, `L` is `𝒪_X(D)`, `iota` is
the ideal inclusion, `c` is the canonical section `1_D`, and `nu` is the factorisation of the
action of `ℐ_D` through a submodule containing its multiples (`Stacks.Divisors.idealActionFactor`);
the composite with `lam` is then multiplication by `1_D`, that is, the map induced by the inclusion
`𝒪_X ⊆ 𝒪_X(D)`.

## Main results

* `Stacks.Monoidal.whiskerLeft_comp_unitAction`: multiplication by a morphism to the unit object
  is natural.
* `Stacks.Monoidal.twistPrefix_naturality`: the prefix `G ⟶ L ⊗ (I ⊗ G)` of the construction is
  natural in `G`.
* `Stacks.Monoidal.comp_invertibleTwistedRetraction`: **`lam ≫ psi` is multiplication by `c`.**

## References

* [Stacks Project, Tag 01WX](https://stacks.math.columbia.edu/tag/01WX)
* [Stacks Project, Tag 0G5G](https://stacks.math.columbia.edu/tag/0G5G)
-/

@[expose] public section

open CategoryTheory MonoidalCategory BraidedCategory

universe v u

namespace Stacks.Monoidal

variable {C : Type u} [Category.{v} C] [MonoidalCategory C]

/-- **Multiplication by a morphism to the unit object is natural.** For `iota : I ⟶ 𝟙`, the
induced map `I ⊗ G ⟶ G` is natural in `G`. -/
theorem whiskerLeft_comp_unitAction {I : C} (iota : I ⟶ 𝟙_ C) {G G' : C} (f : G ⟶ G') :
    I ◁ f ≫ (iota ▷ G' ≫ (λ_ G').hom) = (iota ▷ G ≫ (λ_ G).hom) ≫ f := by
  rw [← Category.assoc, whisker_exchange, Category.assoc, leftUnitor_naturality, Category.assoc]

/-- **The prefix of the twisted retraction is natural.** The composite `G ⟶ L ⊗ (I ⊗ G)` of the
inverse left unit constraint, the whiskered inverse trivialisation and the associator is natural in
`G`. -/
theorem twistPrefix_naturality {I L : C} (ev : L ⊗ I ≅ 𝟙_ C) {F G : C} (lam : F ⟶ G) :
    lam ≫ ((λ_ G).inv ≫ ev.inv ▷ G ≫ (α_ L I G).hom) =
      ((λ_ F).inv ≫ ev.inv ▷ F ≫ (α_ L I F).hom) ≫ L ◁ I ◁ lam := by
  simp only [Category.assoc, leftUnitor_inv_naturality_assoc, whisker_exchange_assoc,
    associator_naturality_right]

variable [SymmetricCategory C]

/-- **The twisted retraction attached to a trivialising pairing, in an arbitrary symmetric
monoidal category.** Let `ev : L ⊗ I ≅ 𝟙` be a trivialising pairing, let `iota : I ⟶ 𝟙` and
`c : 𝟙 ⟶ L` be paired by `hpair`, and let `nu : I ⊗ G ⟶ F` restrict along `lam : F ⟶ G` to
multiplication by `iota` on `F` (`hnu`). Then the composite displayed below is multiplication by
`c`. -/
theorem comp_invertibleTwistedRetraction {I L F G : C} (ev : L ⊗ I ≅ 𝟙_ C) (iota : I ⟶ 𝟙_ C)
    (c : 𝟙_ C ⟶ L) (hpair : L ◁ iota ≫ (ρ_ L).hom = ev.hom ≫ c)
    (lam : F ⟶ G) (nu : I ⊗ G ⟶ F) (hnu : I ◁ lam ≫ nu = iota ▷ F ≫ (λ_ F).hom) :
    lam ≫ ((λ_ G).inv ≫ ev.inv ▷ G ≫ (α_ L I G).hom ≫ L ◁ nu ≫ (β_ L F).hom) =
      (ρ_ F).inv ≫ F ◁ c := by
  have hcoh : (α_ L (𝟙_ C) F).hom ≫ L ◁ (λ_ F).hom = (ρ_ L).hom ▷ F := by monoidal
  have hmid : (α_ L I F).hom ≫ L ◁ (iota ▷ F ≫ (λ_ F).hom) = (ev.hom ≫ c) ▷ F := by
    rw [whiskerLeft_comp, ← associator_naturality_middle_assoc, hcoh, ← comp_whiskerRight, hpair]
  calc lam ≫ ((λ_ G).inv ≫ ev.inv ▷ G ≫ (α_ L I G).hom ≫ L ◁ nu ≫ (β_ L F).hom)
      = (lam ≫ ((λ_ G).inv ≫ ev.inv ▷ G ≫ (α_ L I G).hom)) ≫ L ◁ nu ≫ (β_ L F).hom := by
        simp only [Category.assoc]
    _ = ((λ_ F).inv ≫ ev.inv ▷ F ≫ (α_ L I F).hom) ≫ L ◁ (I ◁ lam ≫ nu) ≫ (β_ L F).hom := by
        rw [twistPrefix_naturality ev lam, whiskerLeft_comp]
        simp only [Category.assoc]
    _ = ((λ_ F).inv ≫ ev.inv ▷ F) ≫ (ev.hom ≫ c) ▷ F ≫ (β_ L F).hom := by
        rw [hnu]
        simp only [Category.assoc]
        rw [← Category.assoc ((α_ L I F).hom), hmid]
    _ = (λ_ F).inv ≫ c ▷ F ≫ (β_ L F).hom := by
        rw [Category.assoc, ← Category.assoc (ev.inv ▷ F), ← comp_whiskerRight,
          Iso.inv_hom_id_assoc]
    _ = (ρ_ F).inv ≫ F ◁ c := by
        rw [braiding_naturality_left c F, ← Category.assoc, leftUnitor_inv_braiding]

end Stacks.Monoidal


end
