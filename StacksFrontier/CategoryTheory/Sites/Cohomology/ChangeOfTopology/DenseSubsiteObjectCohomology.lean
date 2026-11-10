module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.SheafEquiv
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.BigSiteObjectCohomology
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.NoetherianSpaces

/-!
# Transport of the vanishing of the cohomology over an object between a dense subsite and its site

Let `G : C ⥤ D` be a fully faithful functor exhibiting `(C, J)` as a dense subsite of `(D, K)`.
Restriction of abelian sheaves along `G` is then an equivalence of sheaf categories, and the
cohomology over an object `U` of `C` of the restriction of an abelian sheaf `F` on `(D, K)` is the
cohomology of `F` itself over `G.obj U`. In particular one of those groups vanishes exactly when
the other does.

Cohomology over an object is Mathlib's `CategoryTheory.Sheaf.cohomologyPresheaf`, the `Ext`-groups
out of the free abelian sheaf on `CategoryTheory.yoneda.obj U`, written here through
`Stacks.Cohomology.BiggerSite.freeYonedaSheaf`.

This is the objectwise companion of
`Stacks.Cohomology.DenseSubsiteVanishing.subsingleton_H_restriction_of_isDenseSubsite`, and it
stands in the same
relation to `Stacks.Cohomology.BiggerSite.cohomologyPresheafFunctorIso` as that statement does to
`Stacks.Cohomology.DenseSubsiteGlobal.sheafCohomologyIsoOfIsEquivalence`: the hypotheses that the
general change-of-topology comparison needs in order to know that restriction is exact and
preserves injectives — fibre products and equalizers in `C`, preserved by `G` — are *not* needed
for a dense subsite, where restriction is an equivalence outright; and the two `Ext`-universes
stay unrelated, as do the two universes of objects. What `cohomologyPresheafFunctorIso` offers in
exchange, and what is not reproved here, is an isomorphism of functors rather than a transport of
vanishing.

## Main definitions

* `Stacks.Cohomology.DenseSubsiteObject.representableByCompYoneda` and
  `compYonedaIso`: for a fully faithful `G`, the presheaf `G.op ⋙ yoneda.obj (G.obj U)` on `C` is
  represented by `U`, so it is `yoneda.obj U`.
* `Stacks.Cohomology.DenseSubsiteObject.restrictFreeYonedaIso`: **the restriction to the dense
  subsite of the free abelian sheaf on `G.obj U` is the free abelian sheaf on `U`.** This is
  Mathlib's compatibility of restriction with sheafification, read at the free abelian presheaf on
  a representable.
* `Stacks.Cohomology.DenseSubsiteObject.pullbackFreeYonedaIso`: the same identification read
  through the inverse of the equivalence of sheaf categories, which is the form the transport of
  `Ext`-vanishing consumes. It is the objectwise counterpart of
  `CategoryTheory.equivCommuteConstant`.

## Main results

* `Stacks.Cohomology.DenseSubsiteObject.subsingleton_ext_freeYoneda_of_isDenseSubsite` and
  `subsingleton_ext_freeYoneda_of_isDenseSubsite'`: **the transport of the vanishing of the
  cohomology over an object between the dense subsite and the larger site, in both directions.**
* `Stacks.Cohomology.DenseSubsiteObject.subsingleton_cohomologyPresheaf_of_isDenseSubsite` and
  its primed variant: the same, phrased with `CategoryTheory.Sheaf.cohomologyPresheaf`.
* `Stacks.Cohomology.DenseSubsiteObject.subsingleton_cohomologyPresheaf_of_vanishesOnObjects`:
  **the consequence for `Stacks.Cohomology.VanishesOnObjects`.** If the restriction of `F` to the
  dense subsite has vanishing cohomology over every object of the subsite, then the cohomology of
  `F` over the image of every object of the subsite vanishes in positive degrees. The tree has no
  other transport of that predicate between two sites.

## Implementation notes

The vanishing is transported by `Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence`,
which crosses the two `Ext`-universes, and the object out of which `Ext` is taken is moved to its
intended spelling by `Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source` — exactly as in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/DenseSubsiteSheafVanishingTransport.lean`, of
which this file is the objectwise twin.

The two sites share their *morphism* universe. That is forced by the statement and not by the
proof: `CategoryTheory.yoneda` on a category with morphisms in `Type a` takes values in presheaves
of types in `Type a`, so the free abelian sheaf on a representable has coefficients
`AddCommGrpCat.{a}` on both sides, which is also the coefficient universe
`CategoryTheory.Sheaf.cohomologyPresheafFunctor` is defined at. The universes of *objects* of the
two sites and the two `Ext`-universes are unrelated.

Full faithfulness of `G` is a hypothesis rather than a consequence of
`CategoryTheory.Functor.IsDenseSubsite`, which asks only for local full faithfulness. It is what
identifies `G.op ⋙ yoneda.obj (G.obj U)` with `yoneda.obj U` on the nose; for a merely locally
fully faithful `G` the two differ, and only their sheafifications agree.

## References

* [Stacks Project, Tag 03YU](https://stacks.math.columbia.edu/tag/03YU)
* [Stacks Project, Tag 03CG](https://stacks.math.columbia.edu/tag/03CG)
* [Stacks Project, Tag 07A1](https://stacks.math.columbia.edu/tag/07A1)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe w w' a u₁ u₂

namespace Stacks.Cohomology.DenseSubsiteObject

open Stacks.Cohomology.BiggerSite (freeYonedaSheaf)

section Representable

variable {C : Type u₁} [Category.{a} C] {D : Type u₂} [Category.{a} D]
  (G : C ⥤ D) [G.Full] [G.Faithful]

/-- **The presheaf of morphisms into `G.obj U` from the images of the objects of `C` is
represented by `U`**, for a fully faithful `G`: a morphism `G.obj W ⟶ G.obj U` is the image of a
unique morphism `W ⟶ U`. -/
def representableByCompYoneda (U : C) : (G.op ⋙ yoneda.obj (G.obj U)).RepresentableBy U where
  homEquiv {_} := (Functor.FullyFaithful.ofFullyFaithful G).homEquiv
  homEquiv_comp _ _ := by simp

/-- **`G.op ⋙ yoneda.obj (G.obj U)` is `yoneda.obj U`** for a fully faithful `G`. -/
def compYonedaIso (U : C) : G.op ⋙ yoneda.obj (G.obj U) ≅ yoneda.obj U :=
  (representableByCompYoneda G U).toIso.symm

end Representable

section Transport

variable {C : Type u₁} [Category.{a} C] {D : Type u₂} [Category.{a} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.Full] [G.Faithful] [G.IsDenseSubsite J K]
  [∀ Y : Dᵒᵖ, HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{a}]
  [HasSheafify J AddCommGrpCat.{a}] [HasSheafify K AddCommGrpCat.{a}]

/-- **The restriction to the dense subsite of the free abelian sheaf on `G.obj U` is the free
abelian sheaf on `U`.** Restriction commutes with sheafification
(`CategoryTheory.Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility`), and the
restriction of the free abelian presheaf on `yoneda.obj (G.obj U)` is the free abelian presheaf on
`yoneda.obj U` because `G` is fully faithful. -/
def restrictFreeYonedaIso (U : C) :
    (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).inverse.obj
        (freeYonedaSheaf K (G.obj U)) ≅
      freeYonedaSheaf J U :=
  ((Functor.IsDenseSubsite.sheafEquivSheafificationCompatibility J K G
        AddCommGrpCat.{a}).app (yoneda.obj (G.obj U) ⋙ AddCommGrpCat.free)).symm ≪≫
    (presheafToSheaf J AddCommGrpCat.{a}).mapIso
      (Functor.isoWhiskerRight (compYonedaIso G U) AddCommGrpCat.free)

/-- **The free abelian sheaf on `U` is carried to the free abelian sheaf on `G.obj U`** by the
inverse of the equivalence of sheaf categories of a dense subsite. This is the objectwise
counterpart of `CategoryTheory.equivCommuteConstant`, and the identification the transport of
`Ext`-vanishing runs on. -/
def pullbackFreeYonedaIso (U : C) :
    (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).functor.obj
        (freeYonedaSheaf J U) ≅
      freeYonedaSheaf K (G.obj U) :=
  ((Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).functor.mapIso
      (restrictFreeYonedaIso J K G U)).symm ≪≫
    (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).counitIso.app _

/-- Restriction along a dense subsite is additive, being an equivalence. -/
private instance sheafEquiv_functor_additive :
    (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).functor.Additive :=
  have : (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).symm.functor.Additive :=
    { map_add := by intro X Y f g; ext U; exact rfl }
  Equivalence.inverse_additive (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).symm

private instance sheafEquiv_symm_functor_additive :
    (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).symm.functor.Additive :=
  Equivalence.inverse_additive _

variable [HasExt.{w} (Sheaf J AddCommGrpCat.{a})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{a})]

/-- **The vanishing of the cohomology over an object crosses a dense subsite**, read from the
subsite to the larger site: if the degree-`p` cohomology over `U` of the restriction of an abelian
sheaf `F` on `(D, K)` to the dense subsite `(C, J)` vanishes, then so does the degree-`p`
cohomology of `F` over `G.obj U`.

No hypothesis on `F` is made; the `Ext`-universes on the two sides are unrelated. -/
theorem subsingleton_ext_freeYoneda_of_isDenseSubsite (F : Sheaf K AddCommGrpCat.{a}) (U : C)
    (p : ℕ)
    (h : Subsingleton (Ext.{w} (freeYonedaSheaf J U)
      ((G.sheafPushforwardContinuous AddCommGrpCat.{a} J K).obj F) p)) :
    Subsingleton (Ext.{w'} (freeYonedaSheaf K (G.obj U)) F p) := by
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
    (pullbackFreeYonedaIso J K G U) p
    (Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence
      (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}) (freeYonedaSheaf J U) F p h)

/-- **The vanishing of the cohomology over an object crosses a dense subsite**, read from the
larger site to the subsite: if the degree-`p` cohomology of an abelian sheaf `F` on `(D, K)` over
`G.obj U` vanishes, then so does the degree-`p` cohomology of its restriction to the dense subsite
`(C, J)` over `U`.

No hypothesis on `F` is made; the `Ext`-universes on the two sides are unrelated. -/
theorem subsingleton_ext_freeYoneda_of_isDenseSubsite' (F : Sheaf K AddCommGrpCat.{a}) (U : C)
    (p : ℕ) (h : Subsingleton (Ext.{w'} (freeYonedaSheaf K (G.obj U)) F p)) :
    Subsingleton (Ext.{w} (freeYonedaSheaf J U)
      ((G.sheafPushforwardContinuous AddCommGrpCat.{a} J K).obj F) p) := by
  refine Stacks.CohomologyVanishing.subsingleton_ext_of_iso_source
    (restrictFreeYonedaIso J K G U) p ?_
  exact Stacks.CohomologyVanishing.subsingleton_ext_of_equivalence
    (Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).symm
    (freeYonedaSheaf K (G.obj U))
    ((Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).inverse.obj F) p
    (Stacks.CohomologyVanishing.subsingleton_ext_of_iso_target
      ((Functor.IsDenseSubsite.sheafEquiv J K G AddCommGrpCat.{a}).counitIso.app F).symm p h)

/-- `Stacks.Cohomology.DenseSubsiteObject.subsingleton_ext_freeYoneda_of_isDenseSubsite` phrased
with Mathlib's `CategoryTheory.Sheaf.cohomologyPresheaf`: the degree-`p` cohomology of `F` over
`G.obj U` vanishes as soon as the degree-`p` cohomology over `U` of the restriction of `F` to the
dense subsite does. -/
theorem subsingleton_cohomologyPresheaf_of_isDenseSubsite (F : Sheaf K AddCommGrpCat.{a}) (U : C)
    (p : ℕ)
    (h : Subsingleton ((((G.sheafPushforwardContinuous AddCommGrpCat.{a} J K).obj
      F).cohomologyPresheaf.{w} p).obj (op U))) :
    Subsingleton ((F.cohomologyPresheaf.{w'} p).obj (op (G.obj U))) :=
  subsingleton_ext_freeYoneda_of_isDenseSubsite J K G F U p h

/-- `Stacks.Cohomology.DenseSubsiteObject.subsingleton_ext_freeYoneda_of_isDenseSubsite'` phrased
with Mathlib's `CategoryTheory.Sheaf.cohomologyPresheaf`. -/
theorem subsingleton_cohomologyPresheaf_of_isDenseSubsite' (F : Sheaf K AddCommGrpCat.{a}) (U : C)
    (p : ℕ) (h : Subsingleton ((F.cohomologyPresheaf.{w'} p).obj (op (G.obj U)))) :
    Subsingleton ((((G.sheafPushforwardContinuous AddCommGrpCat.{a} J K).obj
      F).cohomologyPresheaf.{w} p).obj (op U)) :=
  subsingleton_ext_freeYoneda_of_isDenseSubsite' J K G F U p h

end Transport

section VanishesOnObjects

variable {C : Type a} [SmallCategory C] {D : Type u₂} [Category.{a} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.Full] [G.Faithful] [G.IsDenseSubsite J K]
  [∀ Y : Dᵒᵖ, HasLimitsOfShape (StructuredArrow Y G.op) AddCommGrpCat.{a}]
  [HasSheafify J AddCommGrpCat.{a}] [HasSheafify K AddCommGrpCat.{a}]
  [HasExt.{w} (Sheaf J AddCommGrpCat.{a})] [HasExt.{w'} (Sheaf K AddCommGrpCat.{a})]

/-- **Vanishing on the objects of a dense subsite gives vanishing over their images.** If the
restriction of an abelian sheaf `F` on `(D, K)` to the dense subsite `(C, J)` satisfies
`Stacks.Cohomology.VanishesOnObjects` — condition (1) of [Stacks, Tag 07A1] — then the cohomology
of `F` over the image of every object of `C` vanishes in every positive degree.

The `Ext`-universe of the conclusion is unrelated to the one the hypothesis is read in. -/
theorem subsingleton_cohomologyPresheaf_of_vanishesOnObjects (F : Sheaf K AddCommGrpCat.{a})
    (hF : VanishesOnObjects.{w} J
      ((G.sheafPushforwardContinuous AddCommGrpCat.{a} J K).obj F))
    (U : C) (p : ℕ) (hp : 0 < p) :
    Subsingleton ((F.cohomologyPresheaf.{w'} p).obj (op (G.obj U))) :=
  subsingleton_cohomologyPresheaf_of_isDenseSubsite J K G F U p
    (hF U (yoneda.obj U) (Functor.RepresentableBy.yoneda U) p hp)

end VanishesOnObjects

end Stacks.Cohomology.DenseSubsiteObject

end
