module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicCriterion
public import StacksFrontier.CategoryTheory.Sites.Cohomology.FilteredColimits.GlobalCohomologyVanishing
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites

/-! # Global-sections acyclicity of a colimit of pullbacks of a pointwise injective system

`Stacks.WeakSites.ColimitSiteCohomology.cohomology_isZero_of_pointwise_injective` says that
`𝒢 = colim_i f_i⁻¹F_i`, for a system `F` of abelian sheaves on the levels of an inverse system of
sites with finite coverings with every `F.obj i` injective, has vanishing right derived sections
over **every object** of the colimit site. Stacks 09YP over the terminal **sheaf** — the shape in
which Stacks 03Q6 is about the cohomology of a quasi-compact quasi-separated scheme rather than of
an affine chart of it — needs instead that `𝒢` is acyclic for `CategoryTheory.Sheaf.Γ`, the
sections over the terminal sheaf. On a site with no terminal object those are different
statements, and this file carries out the part of the passage between them that the library's
inputs support.

## What is proved here, and what the one remaining input is

The passage runs through the criterion of [Stacks, Tag 07A1],
`Stacks.Cohomology.isTotallyAcyclic_of_conditions`, whose two conditions on an abelian sheaf are

1. `Stacks.Cohomology.VanishesOnObjects`: `H^p(U, 𝒢) = 0` for `p > 0` and every object `U` of the
   site; and
2. `Stacks.Cohomology.CechComplexExactPos`: for every surjection `K' ⟶ K` of sheaves of sets the
   Čech complex `Hom(**Z**_{K'_•}^♯, 𝒢)` is exact in positive degrees.

Condition (1) is proved here, with no hypothesis beyond the system data:
`vanishesOnObjects_of_pointwise_injective_presentation` is the object-wise acyclicity read through
`Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections`, which identifies Mathlib's
`CategoryTheory.Sheaf.H'` — the `Ext`-group out of the free abelian sheaf on a representable — with
the right derived functor of sections. So the object-wise statement *is* condition (1), and nothing
about the colimit site beyond what that statement already needs enters.

Condition (2) is **not** proved here and is carried as a named hypothesis `hcech`. It is a `def` in
the library, not an unformalised assertion, and it is true; what is missing is a proof of it for
`𝒢`. Its two producers in the library do not apply: `Stacks.Cohomology.cechComplexExactPos_of_injective`
needs `𝒢` itself injective, which a colimit of pullbacks is not, and
`Stacks.Cohomology.DerivedLowerShriek.cechComplexExactPos_inverseImage` is for a single inverse
image of an injective sheaf of modules, not for a colimit of such.

One might expect that deriving it for `𝒢` from the levels needs `Hom(**Z**_{K'_n}^♯, -)` to
commute with the colimit for the Čech terms of an arbitrary surjection of sheaves of sets, which is
quasi-compactness of those terms — the same covering-set input that the other route needs.
**That is false.**
`Stacks.Cohomology.isTotallyAcyclic_of_conditions` applies condition (2) exactly once, inside
`Stacks.Cohomology.subsingleton_ext_freeAbelianSheaf_succ`, to the single epi that
`Stacks.Cohomology.exists_epi_subsingleton_ext` hands it, and only as the extension input of
`ext_eq_zero_of_exact_tower` at the top index. The acyclicity of the Čech *terms* in degrees
`1 ≤ q ≤ n` is already supplied there by the induction hypothesis, quantified over all presheaves
of sets, and the `i = 0` input by condition (1). So condition (2) contributes nothing but the top
degree `n + 1`, the degree the induction is trying to reach: it is an induction-breaking input of
the same strength as the conclusion, not a commutation or quasi-compactness matter, and no
weakening of it to epis with quasi-compact source, or source in `S`, or `F`-acyclic source, makes
it a covering-set consequence — the Čech terms of an epi one did not choose are fibre powers that
nothing about `S` bounds, `S` being stable under *covering* a product rather than under taking
one, and there is no refinement step, the induced map running
`Hom(**Z**_{K'_•}^♯, F) ⟶ Hom(**Z**_{K''_•}^♯, F)`. What `hcech` is missing is the top-degree
vanishing itself.

A covering set bears on this only through condition (1), and there it does help:
`Stacks.Cohomology.subsingleton_ext_freeAbelianSheaf_of_mem_finiteCoproductSheafifiedYoneda`
upgrades acyclicity over every object to acyclicity over every member of 0GN4's covering set, so
`vanishesOnObjects_of_pointwise_injective_presentation` below gives acyclicity of
`colim_i f_i⁻¹F_i` on all of `S`. That is condition (1) restated, not condition (2).

## Why the filtered-colimit route is not available at all

`Stacks.Cohomology.ColimitsOfCohomology.isZero_rightDerived_globalSections_colimit_of_isIso` and
its weakenings — up to Stacks 0GN3
(`...isIso_colimit_post_rightDerived_globalSections`) and Stacks 0GN4
(`...isIso_colimit_post_rightDerived_globalSections_of_finite_covers`) — all conclude about
`CategoryTheory.Limits.colimit G` for an honest filtered diagram `G : I ⥤ Sheaf J Ab`. This
development has no such diagram. The colimit `colim_i f_i⁻¹F_i` is pinned **only** by the universal
property `Stacks.WeakSites.ColimitSiteCohomology.IsColimitPresentation`, realised by
`systemColimitSheaf`, which is a pointwise left Kan extension of presheaves and not a colimit of a
diagram of sheaves; the implementation notes of Stacks 09YN and 0EXJ in
`CohomologyOfColimitOfFiniteSites.lean` record why — the diagram `i ↦ f_i⁻¹F_i` is not available as
a functor, its transition maps being given by data and equations, so there is no cocone on it whose
`CategoryTheory.Limits.IsColimit` could be asserted. There is also no functor
`Sheaf (D.J j) Ab ⥤ Sheaf K.toGrothendieck Ab` in the library for the colimit-site morphism `f_j`,
only the level-to-level `InverseSystemOfFiniteSites.abelianSheafPullback` along a transition. So
the filtered-colimit machinery cannot be applied to `𝒢` as it stands, whatever covering set the
colimit site may carry.

## Main results

* `Stacks.Cohomology.isZero_rightDerivedΓ_of_isTotallyAcyclic`: **part (3) of [Stacks, Tag 0731]
  for an abelian sheaf.** A totally acyclic abelian sheaf has vanishing
  `(CategoryTheory.Sheaf.Γ J Ab).rightDerived p` in every positive degree. The library had this
  only for sheaves of *modules* (`Stacks.Cohomology.isTotallyAcyclic_rightAcyclic_globalSections`),
  whose statement is right acyclicity of `SiteModules.globalSectionsFunctor`. Total acyclicity is
  vanishing of `Ext^p(**Z**_K^♯, -)` for every sheaf of sets `K`, so the abelian case needs no
  induction at all: take `K` to be the terminal sheaf, whose free abelian sheaf is the constant
  sheaf on `ℤ` (`...ColimitsOfCohomology.freeAbelianSheafTerminalIsoConstantSheaf`), and read the
  result through `...ColimitsOfCohomology.globalSectionsRightDerivedIsoFunctorH`.
* `Stacks.WeakSites.ColimitSiteCohomology.vanishesOnObjects_of_pointwise_injective_presentation`:
  **condition (1) of [Stacks, Tag 07A1] for `𝒢 = colim_i f_i⁻¹F_i`.** Unconditional on the system
  data.
* `Stacks.WeakSites.ColimitSiteCohomology.isTotallyAcyclic_of_pointwise_injective`: `𝒢` is totally
  acyclic, over the hypothesis `hcech` = condition (2).
* `Stacks.WeakSites.ColimitSiteCohomology.isZero_rightDerivedΓ_of_pointwise_injective`:
  **Γ-acyclicity of `𝒢` in positive degrees**, over the same single hypothesis `hcech`. This is the
  positive-degree input that Stacks 09YP over the terminal sheaf needs, with the gap reduced from
  prose to one named library predicate.

## Implementation notes

Everything is at the universe convention of the colimit site: the site `C`, the coefficients and
the `Ext`-groups all live in `max u v w`, which is what both the 07A1 criterion and
`cohomologyIsoRightDerivedSections` require, and which is the universe
`cohomology_isZero_of_pointwise_injective` is already stated at.

`EnoughInjectives` and additivity of global sections for abelian sheaves on a small site are
installed from `Stacks.Cohomology.ColimitsOfCohomology.enoughInjectives_sheaf_ab` and
`...additive_globalSections_ab` with `attribute [local instance]`, as every module of the
global-cohomology development does, so the global instance set is unchanged.

Nothing here closes the colimit statement of Stacks 09YP over the terminal sheaf. Its degree-zero
half is `Stacks.WeakSites.ColimitGlobalSections.abelianGlobalSections_colimit_pullback_of_colimit`,
in the jointly-surjective-and-separated idiom rather than as an
`CategoryTheory.Limits.IsColimit`; assembling the two into a colimit cocone is not done here.

## References

* [Stacks 07A1](https://stacks.math.columbia.edu/tag/07A1)
* [Stacks 0731](https://stacks.math.columbia.edu/tag/0731)
* [Stacks 072Y](https://stacks.math.columbia.edu/tag/072Y)
* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [local instance] Stacks.Cohomology.ColimitsOfCohomology.enoughInjectives_sheaf_ab
  Stacks.Cohomology.ColimitsOfCohomology.additive_globalSections_ab

/-! ### A totally acyclic abelian sheaf is acyclic for global sections -/

namespace Stacks.Cohomology

universe u

/-- **Part (3) of [Stacks, Tag 0731] for an abelian sheaf.** A totally acyclic abelian sheaf on a
small site — one whose cohomology over every sheaf of sets vanishes in positive degrees,
[Stacks, Tag 072Y] — has vanishing right derived global sections in every positive degree.

No induction and no Čech argument is involved: total acyclicity is vanishing of
`Ext^p(**Z**_K^♯, -)` for *every* sheaf of sets `K`, so it suffices to take `K` to be the terminal
sheaf. The free abelian sheaf on the terminal sheaf is the constant sheaf on `ℤ`
(`ColimitsOfCohomology.freeAbelianSheafTerminalIsoConstantSheaf`), `Ext` out of that is
`CategoryTheory.Sheaf.functorH`, and that is the right derived functor of global sections
(`ColimitsOfCohomology.globalSectionsRightDerivedIsoFunctorH`).

The library's `isTotallyAcyclic_rightAcyclic_globalSections` is the same part of the same tag for a
sheaf of *modules*, stated as right acyclicity of `SiteModules.globalSectionsFunctor`; it does not
specialise to an abelian sheaf, an injective object of `Sheaf J Ab` not being an injective module
over the constant sheaf of rings `ℤ`. -/
@[stacks 0731 "part (3) for an abelian sheaf, in the derived-functor spelling: a totally acyclic \
abelian sheaf has vanishing (Sheaf.Gamma J Ab).rightDerived p for p > 0. The tag's part (3) for a \
sheaf of MODULES, stated as right acyclicity of SiteModules.globalSectionsFunctor, is \
isTotallyAcyclic_rightAcyclic_globalSections; this is not that statement specialised, the abelian \
sheaf not being a module over the constant sheaf of rings. Parts (1), (2) and (4) are not here."]
theorem isZero_rightDerivedΓ_of_isTotallyAcyclic {C : Type u} [SmallCategory C]
    (J : GrothendieckTopology C) (F : Sheaf J Ab.{u}) (hF : IsTotallyAcyclic.{u} J F)
    (p : ℕ) (hp : 0 < p) :
    IsZero (((Sheaf.Γ J Ab.{u}).rightDerived p).obj F) := by
  have hz : ∀ a : Abelian.Ext.{u}
      ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) F p, a = 0 :=
    ColimitsOfCohomology.ext_eq_zero_of_iso_first
      (ColimitsOfCohomology.freeAbelianSheafTerminalIsoConstantSheaf J).symm p
      (fun a => (hF (⊤_ (Sheaf J (Type u))) p hp).elim a 0)
  have hExt : IsZero ((Sheaf.functorH J p).obj F) := by
    show IsZero (AddCommGrpCat.of (Abelian.Ext.{u}
      ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) F p))
    have : Subsingleton (Abelian.Ext.{u}
        ((constantSheaf J Ab.{u}).obj (AddCommGrpCat.of (ULift.{u} ℤ))) F p) :=
      ⟨fun a b => (hz a).trans (hz b).symm⟩
    exact AddCommGrpCat.isZero_of_subsingleton _
  exact hExt.of_iso ((ColimitsOfCohomology.globalSectionsRightDerivedIsoFunctorH J p).app F)

end Stacks.Cohomology

/-! ### The colimit of pullbacks of a pointwise injective system -/

namespace Stacks.WeakSites.ColimitSiteCohomology

open CategoryTheory.Sites.InverseSystem

universe v u w

variable (D : InverseSystemOfFiniteSites.{v, u, max u v w}) {C : Type (max u v w)}
  [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y),
    R ∈ K Y ↔
      ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
        S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
          R = h ▸ S.map (uC i))
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{v, u, max u v w, max u v w} D)
  (hF : ∀ i, Injective (F.obj i))
  (G : Sheaf K.toGrothendieck (Ab.{max u v w}))
  (ι : ∀ i, (F.obj i).obj ⟶ (uC i).op ⋙ G.obj)
  (hG : IsColimitPresentation D uC hu K F G ι)
  (hcech : Stacks.Cohomology.CechComplexExactPos K.toGrothendieck G)

/-- **The colimit of pullbacks of a pointwise injective system has no higher cohomology over any
object of the colimit site.** For a system `F` of abelian sheaves on the levels of an inverse
system of sites with finite coverings, with every `F.obj i` injective, and a sheaf `G` on the
colimit site presenting the colimit of the pullbacks, the right derived sections of `G` over every
object `U` of the colimit site vanish in positive degrees.

Every object of the colimit site is `u_i(X)` for some level `i` and some `X` (`hobj`), and over it
Stacks 09YP (`isColimitCohomologyCocone`) exhibits `Hᵖ(u_i(X), G)` as the filtered colimit of the
groups `Hᵖ(u_a(X), F_j)`, each of which vanishes as `F_j` is injective and `p > 0`. -/
public alias cohomology_isZero_of_pointwise_injective' := cohomology_isZero_of_pointwise_injective

include hobj hhom hhom_inj hK hF hG in
/-- **Condition (1) of [Stacks, Tag 07A1] for `𝒢 = colim_i f_i⁻¹F_i`.** For a system `F` of abelian
sheaves on the levels of an inverse system of sites with finite coverings, with every `F.obj i`
injective, and a sheaf `G` on the colimit site presenting the colimit of the pullbacks, the
cohomology of `G` over every object of the colimit site vanishes in positive degrees — in the
`Ext`-out-of-a-representable spelling that the criterion of Stacks 07A1 uses.

This is `cohomology_isZero_of_pointwise_injective'` read through
`Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections`, which identifies Mathlib's
`CategoryTheory.Sheaf.H'` with the right derived functor of sections over the object, and then
transported along the given representability of `Q` by `U`. No hypothesis is added. -/
public theorem vanishesOnObjects_of_pointwise_injective_presentation :
    Stacks.Cohomology.VanishesOnObjects.{max u v w} K.toGrothendieck G := by
  intro U Q hQ p hp
  have hzero : IsZero (Sheaf.H'.{max u v w, max u v w, max u v w} G p U) :=
    isZero_H'_of_pointwise_injective D uC hu hobj hhom hhom_inj K hK F hF G ι hG U p hp
  have hsub : Subsingleton (Abelian.Ext.{max u v w}
      ((presheafToSheaf K.toGrothendieck Ab.{max u v w}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free)) G p) :=
    AddCommGrpCat.subsingleton_of_isZero hzero
  let iso : (presheafToSheaf K.toGrothendieck Ab.{max u v w}).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free) ≅
      (presheafToSheaf K.toGrothendieck Ab.{max u v w}).obj (Q ⋙ AddCommGrpCat.free) :=
    (presheafToSheaf K.toGrothendieck Ab.{max u v w}).mapIso
      (Functor.isoWhiskerRight hQ.toIso AddCommGrpCat.free)
  exact (((Abelian.extFunctor p).mapIso iso.op).app G).addCommGroupIsoToAddEquiv
    |>.subsingleton_congr.mpr hsub

include hobj hhom hhom_inj hK hF hG hcech in
/-- **`𝒢 = colim_i f_i⁻¹F_i` is totally acyclic**, over condition (2) of [Stacks, Tag 07A1].

Condition (1) is `vanishesOnObjects_of_pointwise_injective_presentation`, which needs nothing
beyond the system data. Condition (2), `hcech`, is carried: it is the predicate
`Stacks.Cohomology.CechComplexExactPos`, a `def` in the library, and this file does not prove it
for `G`. Its producers in the library do not apply — `Stacks.Cohomology.cechComplexExactPos_of_injective`
needs `G` injective, and `Stacks.Cohomology.DerivedLowerShriek.cechComplexExactPos_inverseImage` is
for a single inverse image of an injective sheaf of modules. See the module documentation. -/
public theorem isTotallyAcyclic_of_pointwise_injective :
    Stacks.Cohomology.IsTotallyAcyclic.{max u v w} K.toGrothendieck G :=
  Stacks.Cohomology.isTotallyAcyclic_of_conditions K.toGrothendieck G
    (vanishesOnObjects_of_pointwise_injective_presentation D uC hu hobj hhom hhom_inj K hK F hF G
      ι hG) hcech

include hobj hhom hhom_inj hK hF hG hcech in
/-- **Γ-acyclicity of `𝒢 = colim_i f_i⁻¹F_i` in positive degrees**, over condition (2) of
[Stacks, Tag 07A1]. The right derived functors of `CategoryTheory.Sheaf.Γ` — sections over the
terminal *sheaf* of the colimit site, which for a site with no terminal object is not the derived
sections over any object — vanish on `G` in every positive degree.

This is the positive-degree input of Stacks 09YP over the terminal sheaf, and the statement
`isTotallyAcyclic_of_pointwise_injective` read through
`Stacks.Cohomology.isZero_rightDerivedΓ_of_isTotallyAcyclic`, part (3) of [Stacks, Tag 0731]. The
one hypothesis is `hcech`; the module documentation says what is known about it and why the
filtered-colimit route of Stacks 0GN3 is not an alternative here.

The criterion of Stacks 07A1 is applied here directly rather than through
`isTotallyAcyclic_of_pointwise_injective`, so that the instance arguments of
`Stacks.Cohomology.IsTotallyAcyclic` are fixed by unification with the hypothesis of
`isZero_rightDerivedΓ_of_isTotallyAcyclic` instead of being compared with a second, independently
synthesized set; the comparison exhausts the heartbeat budget. -/
public theorem isZero_rightDerivedΓ_of_pointwise_injective (p : ℕ) (hp : 0 < p) :
    IsZero (((Sheaf.Γ K.toGrothendieck Ab.{max u v w}).rightDerived p).obj G) :=
  Stacks.Cohomology.isZero_rightDerivedΓ_of_isTotallyAcyclic K.toGrothendieck G
    (Stacks.Cohomology.isTotallyAcyclic_of_conditions K.toGrothendieck G
      (vanishesOnObjects_of_pointwise_injective_presentation D uC hu hobj hhom hhom_inj K hK F hF
        G ι hG) hcech) p hp

end Stacks.WeakSites.ColimitSiteCohomology

end
