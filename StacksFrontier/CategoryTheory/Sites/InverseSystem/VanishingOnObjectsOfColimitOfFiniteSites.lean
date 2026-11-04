module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Acyclicity.TotallyAcyclicCriterion
import all StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSites
public import StacksFrontier.CategoryTheory.Sites.InverseSystem.CohomologyOfColimitOfFiniteSitesSystems

/-! # Condition (1) of Stacks 07A1 for the colimit of a pointwise injective system

Let `D` be an inverse system of sites with finite coverings (Stacks 00VH) and let `C` be its
colimit site in the sense of Stacks 09YL and 0A35. Let `(F_j, φ_a)` be a system of abelian
sheaves on the levels, every one of them an **injective** object of the category of abelian
sheaves on its level, and let `𝒢` on `C` present the colimit `colim f_j^{-1}F_j`. Then
`H^p(U, 𝒢) = 0` for every object `U` of `C` and every `p > 0`.

That vanishing is
`Stacks.WeakSites.ColimitSiteCohomology.cohomology_isZero_of_pointwise_injective`, proved on the
way to Stacks 09YP by the Čech route the source uses. This file restates it as
`Stacks.Cohomology.VanishesOnObjects`, which is literally condition (1) of the criterion for total
acyclicity, [Stacks, Tag 07A1], and is the form in which that criterion consumes it. Nothing about
the vanishing itself is reproved here.

## Why the restatement is wanted

`Stacks.Cohomology.VanishesOnObjects` and `Stacks.Cohomology.CechComplexExactPos` together give
total acyclicity (`Stacks.Cohomology.isTotallyAcyclic_of_conditions`), total acyclicity gives
right acyclicity for sections against any presheaf of sets (part (2) of [Stacks, Tag 0731],
`Stacks.Cohomology.rightAcyclic_sectionsOverPresheaf_of_isTotallyAcyclic`), and at the terminal
presheaf that is the vanishing of the higher cohomology of `𝒢` over the terminal **sheaf** of the
colimit site. For a site with no terminal object — the small affine étale site of a quasi-compact
quasi-separated scheme that is not affine — the cohomology over the terminal sheaf is not the
cohomology over any object, and that vanishing is the input the dimension shift of
[Stacks, Tag 09YQ] still lacks at such a level. Condition (1) alone does not supply it: an abelian
sheaf on the site of contractible opens of the circle has vanishing cohomology over every object
and nonvanishing `H^1` over the terminal sheaf.

## Main results

* `Stacks.WeakSites.ColimitSiteCohomology.vanishesOnObjects_of_pointwise_injective`.

## References

* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
* [Stacks 07A1](https://stacks.math.columbia.edu/tag/07A1)
* [Stacks 0731](https://stacks.math.columbia.edu/tag/0731)

Tags covered: none.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sites.InverseSystem Opposite

universe v u w

namespace Stacks.WeakSites.ColimitSiteCohomology

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
  (𝒢 : Sheaf K.toGrothendieck (Ab.{max u v w}))
  (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)

open Stacks.Cohomology in
include hobj hhom hhom_inj hK in
/-- **Condition (1) of the criterion for total acyclicity, [Stacks, Tag 07A1], for the colimit of
a pointwise injective system.** In the situation of Stacks 09YP, with every `F_j` injective, the
colimit sheaf `𝒢` satisfies `Stacks.Cohomology.VanishesOnObjects`: `Ext^p` out of the free abelian
sheaf on a representable presheaf of sets vanishes for every `p > 0`.

The vanishing is
`Stacks.WeakSites.ColimitSiteCohomology.cohomology_isZero_of_pointwise_injective`; what is added
is the passage from right-derived sections over an object to `Ext` out of the free abelian sheaf
on the representable presheaf of that object
(`Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections`, which is Mathlib's
`CategoryTheory.Sheaf.H'`), and from the representable presheaf `yoneda.obj U` to an arbitrary
presheaf representable by `U`, which is `CategoryTheory.Functor.RepresentableBy.toIso`.

With this in hand the only condition of Stacks 07A1 still missing for `𝒢` is condition (2),
`Stacks.Cohomology.CechComplexExactPos`; the module docstring says what the two of them would
give. -/
theorem vanishesOnObjects_of_pointwise_injective
    [HasSheafify K.toGrothendieck (Ab.{max u v w})]
    (hcolim : IsColimitPresentation.{v, u, max u v w, max u v w} D uC hu K F 𝒢 ι)
    (hF : ∀ j, Injective (F.obj j)) :
    VanishesOnObjects.{max u v w} K.toGrothendieck 𝒢 := by
  have := enoughInjectivesAb.{max u v w, max u v w} K.toGrothendieck
  have : HasExt.{max u v w} (Sheaf K.toGrothendieck (Ab.{max u v w})) :=
    hasExt_of_enoughInjectives _
  intro U Q hQ p hp
  have hzero : IsZero (Sheaf.H'.{max u v w, max u v w, max u v w} 𝒢 p U) :=
    IsZero.of_iso
      (cohomology_isZero_of_pointwise_injective D uC hu hobj hhom hhom_inj K hK F hF 𝒢 ι hcolim
        U p hp)
      (Stacks.Cohomology.SiteSections.cohomologyIsoRightDerivedSections K.toGrothendieck 𝒢 p U)
  have hsub : Subsingleton (Abelian.Ext.{max u v w}
      ((presheafToSheaf K.toGrothendieck (Ab.{max u v w})).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free)) 𝒢 p) :=
    AddCommGrpCat.subsingleton_of_isZero hzero
  let e : (presheafToSheaf K.toGrothendieck (Ab.{max u v w})).obj
        (yoneda.obj U ⋙ AddCommGrpCat.free) ≅
      (presheafToSheaf K.toGrothendieck (Ab.{max u v w})).obj (Q ⋙ AddCommGrpCat.free) :=
    (presheafToSheaf K.toGrothendieck (Ab.{max u v w})).mapIso
      (Functor.isoWhiskerRight hQ.toIso AddCommGrpCat.free)
  exact (((Abelian.extFunctor p).mapIso e.op).app 𝒢).addCommGroupIsoToAddEquiv
    |>.subsingleton_congr.mpr hsub

end Stacks.WeakSites.ColimitSiteCohomology

end
