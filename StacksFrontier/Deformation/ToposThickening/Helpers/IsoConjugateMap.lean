module

public import Mathlib.CategoryTheory.EqToHom

/-!
# A map read through identifications of its source and target

For a functor `J : C ⥤ D`, isomorphisms `ρ₁ : F'₁ ≅ G₁` in `D` and `ρ₂ : F'₂ ≅ G₂` in `C`,
equalities of objects `F₁ = F'₁`, `G₁ = G'₁`, `G'₂ = G₂`, `F₂ = F'₂` and a map
`ν' : G'₁ ⟶ J(G'₂)`, the map `F₁ ⟶ J(F₂)` obtained from `ν'` through these identifications is
`CategoryTheory.isoConjugateMap`.

## Main definitions

* `CategoryTheory.isoConjugateMap`: the map `F₁ ⟶ J(F₂)` obtained from `ν' : G'₁ ⟶ J(G'₂)`
  through the given identifications of source and target.

## References

* [Stacks Project, Tag 08WA](https://stacks.math.columbia.edu/tag/08WA)
-/

@[expose] public section

namespace CategoryTheory

variable {C D : Type*} [Category* C] [Category* D] (J : C ⥤ D) {F₁ F'₁ G₁ G'₁ : D}
  {F₂ F'₂ G₂ G'₂ : C}

/-- **A map `G'₁ ⟶ J(G'₂)` read as a map `F₁ ⟶ J(F₂)`** through `F₁ = F'₁ ≅ G₁ = G'₁` and
`J` of `G'₂ = G₂ ≅ F'₂ = F₂`. -/
def isoConjugateMap (Z₁ : F₁ = F'₁) (ρ₁ : F'₁ ≅ G₁) (c₁ : G₁ = G'₁) (ν' : G'₁ ⟶ J.obj G'₂)
    (c₂ : G'₂ = G₂) (ρ₂ : F'₂ ≅ G₂) (Z₂ : F₂ = F'₂) : F₁ ⟶ J.obj F₂ :=
  eqToHom Z₁ ≫ ρ₁.hom ≫ eqToHom c₁ ≫ ν' ≫ J.map (eqToHom c₂ ≫ ρ₂.inv ≫ eqToHom Z₂.symm)

end CategoryTheory

end
