module

public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartSmallerBase

/-!
# The étale-chart condition along isomorphic arrows (Stacks 03MJ)

Let `P` be a property of morphisms of schemes. The every-étale-chart condition of Stacks 03MJ,
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart`, is invariant under composing with an isomorphism
on either side (`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iso_comp_iff` and
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_comp_iso_iff`). This file records the consequence
for two morphisms that are isomorphic as arrows: given `g : F ⟶ G`, `g' : F' ⟶ G'` and
isomorphisms `eF : F ≅ F'`, `eG : G ≅ G'` with `eF.hom ≫ g' = g ≫ eG.hom`, the condition holds
for `g` exactly when it holds for `g'`. No hypothesis on `P` is needed: the isomorphisms are
absorbed into the charts, never into the morphism of schemes `P` is tested on.

## Main results

* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_comm_iso`: the statement for morphisms
  of presheaves on the big fppf site of `S`.
* `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_hom_iff_of_comm_iso`: the same for morphisms
  of the category `AlgebraicGeometry.AlgebraicSpaces` of algebraic spaces over `S`.

## References

* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (P : MorphismProperty Scheme.{u})

/-- **The every-étale-chart condition of Stacks 03MJ is the same for isomorphic arrows.** If
`eF.hom ≫ g' = g ≫ eG.hom` for isomorphisms `eF : F ≅ F'` and `eG : G ≅ G'` of presheaves on the
big fppf site of `S`, then `P` holds on every étale chart of `g` exactly when it holds on every
étale chart of `g'`, for every property `P` of morphisms of schemes.

Indeed `g' = eF.inv ≫ g ≫ eG.hom`, and the condition is unchanged by composing with an
isomorphism on either side. -/
theorem holdsOnEveryEtaleChart_iff_of_comm_iso {F G F' G' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : F ⟶ G) (g' : F' ⟶ G') (eF : F ≅ F') (eG : G ≅ G') (w : eF.hom ≫ g' = g ≫ eG.hom) :
    HoldsOnEveryEtaleChart B S hS P g ↔ HoldsOnEveryEtaleChart B S hS P g' := by
  have hg' : g' = eF.inv ≫ g ≫ eG.hom := by
    rw [← w, Iso.inv_hom_id_assoc]
  rw [hg', Space.holdsOnEveryEtaleChart_iso_comp_iff B S hS P eF.inv,
    Space.holdsOnEveryEtaleChart_comp_iso_iff B S hS P g eG.hom]

/-- **The every-étale-chart condition of Stacks 03MJ is the same for isomorphic arrows of
algebraic spaces.** This is `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_iff_of_comm_iso` for
morphisms and isomorphisms of the category `AlgebraicGeometry.AlgebraicSpaces` of algebraic spaces
over `S`, read on the underlying presheaves. -/
theorem holdsOnEveryEtaleChart_hom_iff_of_comm_iso {F G F' G' : AlgebraicSpaces B S hS}
    (g : F ⟶ G) (g' : F' ⟶ G') (eF : F ≅ F') (eG : G ≅ G') (w : eF.hom ≫ g' = g ≫ eG.hom) :
    HoldsOnEveryEtaleChart B S hS P g.hom ↔ HoldsOnEveryEtaleChart B S hS P g'.hom :=
  holdsOnEveryEtaleChart_iff_of_comm_iso B S hS P g.hom g'.hom
    ((ObjectProperty.ι _).mapIso eF) ((ObjectProperty.ι _).mapIso eG)
    (congrArg (ObjectProperty.ι _).map w)

end AlgebraicGeometry.Space

end
