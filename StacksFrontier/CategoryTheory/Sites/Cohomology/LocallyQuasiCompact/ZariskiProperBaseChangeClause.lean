module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiGermSectionsComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.ZariskiGermSectionsMapOut
import StacksCore.Tactic.StacksAttribute

/-!
# Proper base change for the Zariski comparison morphisms

Let `f : X ⟶ Y` be a morphism of the locally quasi-compact Zariski site whose underlying
continuous map is proper. This file proves that the base-change map

`π_Y^{-1} ∘ f_* ⟶ f_{Zar,*} ∘ π_X^{-1}`

of `ZariskiProperBaseChange.lean` is an isomorphism, which is clause (7a) of Stacks 0DCU, and
records the sections formula of Stacks 09X3 in its natural form on the way.

The two inputs are in this directory. The germ-model sections presheaf

`(h : W ⟶ X') ↦ Γ(W, h^{-1}F)`

is a sheaf on the localized Zariski site (`isSheaf_germSectionsPresheaf`), and together with the
germ map `germSectionsUnit` it corepresents morphisms out of the comparison inverse image
(`existsUnique_germSectionsMapOut`). Since the comparison inverse image corepresents the same
functor, by its adjunction, the two agree: `germSectionsPresheafIso`. Proper base change for
sheaves of sets on topological spaces (Stacks 0D90) is then transported along that isomorphism by
`isIso_zariskiComparisonBaseChangeMap_of_germSectionsIso`.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.germSectionsPresheafIso`: **the sections
  formula of Stacks 09X3 for the Zariski site, naturally in the object of the localized site** —
  the comparison inverse image `π_{X'}^{-1}F` is the germ-model sections presheaf.

## Main results

* `Stacks.Topology.LocallyQuasiCompactZariskiSituation.isIso_zariskiComparisonBaseChangeMap`:
  **clause (7a) of Stacks 0DCU** — the base-change map of the Zariski comparison morphisms is an
  isomorphism for a morphism of the site whose underlying continuous map is proper.

## Implementation notes

`germSectionsPresheafIso` is the second of the four assertions of Stacks 09X3; the first, that the
rule is a sheaf on `LC_Zar/X`, is `isSheaf_germSectionsPresheaf`, tagged where it is proved. The
remaining two — that the same rule is a sheaf on the *quasi-compact* site `LC_qc/X` and agrees
there with `ε_X^{-1}π_X^{-1}F` — are not proved here, but they are proved and tagged in
`QcGermSectionsSheaf.lean`, so the covering set of Stacks 09X3 is complete.

`isIso_zariskiComparisonBaseChangeMap` is not tagged, although it is a statement of clause (7a)
of Stacks 0DCU: the tag for that clause sits on `properDirectImageComparisonIsoOfProperMap` of
`ProperBaseChangeSurjective.lean`, which states the clause as the source does, as an isomorphism
of the two composite functors, and at the situation's coefficient universe rather than at
`Type u`.

## References

* [Stacks Project, Tag 0DCU](https://stacks.math.columbia.edu/tag/0DCU)
* [Stacks Project, Tag 09X3](https://stacks.math.columbia.edu/tag/09X3)
* [Stacks Project, Tag 0D90](https://stacks.math.columbia.edu/tag/0D90)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

namespace Stacks.Topology.LocallyQuasiCompactZariskiSituation

universe u w t

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactZariskiSituation.{u, w} S₀ Bound)

/-- The germ-model sections sheaf has the mapping-out property of the sections formula of
Stacks 09X3. -/
theorem germSectionsMapOutProperty (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) :
    GermSectionsMapOutProperty S X' F :=
  fun H φ => existsUnique_germSectionsMapOut S X' F H φ

/-- **The sections formula of Stacks 09X3 for the Zariski site, naturally in the object of the
localized site.** For an object `X'` of the locally quasi-compact Zariski site and a sheaf of sets
`F` on its space, the comparison inverse image `π_{X'}^{-1}F` is the germ-model sections presheaf

`(h : W ⟶ X') ↦ Γ(W, h^{-1}F)`,

as presheaves on the localized Zariski site `LC_Zar/X'`.

The identification is read off the universal property rather than computed on either side: the
germ-model sections sheaf corepresents morphisms out of the comparison inverse image
(`germSectionsMapOutProperty`), which the comparison inverse image corepresents by its own
adjunction, so the two agree. -/
@[stacks 09X3 "the sections formula on LC_Zar/X"]
def germSectionsPresheafIso (X' : S.category)
    (F : Sheaf (Opens.grothendieckTopology X'.obj) (Type (max u t))) :
    ((comparisonInverseImage.{u, w, t} S X').obj F).obj ≅ germSectionsPresheaf S X' F :=
  comparisonInverseImageGermSectionsNatIso S X' F (germSectionsMapOutProperty S X' F)

variable {X Y : S.category} (f : X ⟶ Y)

/-- **Clause (7a) of Stacks 0DCU.** If the underlying continuous map of a morphism
`f : X ⟶ Y` of the locally quasi-compact Zariski site is proper, then the base-change map

`π_Y^{-1} ∘ f_* ⟶ f_{Zar,*} ∘ π_X^{-1}`

of the Zariski comparison morphisms is an isomorphism.

The geometric content is proper base change for sheaves of sets on topological spaces,
Stacks 0D90; it is transported to the localized site by the sections formula of Stacks 09X3 in
its natural form, `germSectionsPresheafIso`. -/
theorem isIso_zariskiComparisonBaseChangeMap
    (hf : StacksDraft.Topology.IsProperMap.{u, u, u} ⇑((siteToTop S).map f)) :
    IsIso (zariskiComparisonBaseChangeMap.{u, w, u} S f) :=
  isIso_zariskiComparisonBaseChangeMap_of_univ.{u, w} S f hf
    (germSectionsMapOutProperty.{u, w, u} S X) (germSectionsMapOutProperty.{u, w, u} S Y)

end Stacks.Topology.LocallyQuasiCompactZariskiSituation

end
