module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Cech.VanishingAlongAFunctorEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaRightDerivedUnivLE

/-!
# Čech vanishing on a cofinal system gives vanishing of right-derived sections

Let `C` be a locally small site and `B` a collection of objects of `C`, with a cofinal system of
coverings of the objects of `B` whose members and nonempty finite fibre products lie in `B`. If
the positive-degree Čech cohomology of an abelian sheaf `F` vanishes on every selected covering,
then the positive-degree right-derived functors of sections over every object of `B` vanish at
`F` (Stacks 03F9). The coefficients may lie in any universe containing the objects, the morphisms
and the covering indices of the site.

## Main results

* `Stacks.CechSite.isZero_rightDerived_sheafSections_of_cechCohomology_isZero`: if the
  positive-degree Čech cohomology of `F` vanishes on a cofinal system of coverings as above, then
  `IsZero ((((sheafSections J AddCommGrpCat).obj (op U)).rightDerived p).obj F)` for every
  `U ∈ B` and `p > 0`.

## References

* [Stacks Project, Tag 03F9](https://stacks.math.columbia.edu/tag/03F9)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite
  Stacks.Cohomology.FreeYonedaUnivLE

universe a w v u

namespace Stacks.CechSite

/-- **Čech vanishing on a cofinal system of coverings gives vanishing of the right-derived
functors of sections.** Let `B` be a collection of objects of a locally small site `C` and let
`Cov` select, for each object, a collection of coverings whose members and whose nonempty finite
fibre products all lie in `B`, those fibre products being assumed to exist; assume the selected
coverings of the objects of `B` are cofinal among the covering sieves of those objects. If the
positive-degree Čech cohomology of an abelian sheaf `F`, with coefficients in any universe
`max a u v w` containing the objects, the morphisms and the covering indices, vanishes on every
selected covering, then the positive-degree right-derived functors of sections over any object of
`B` vanish at `F`. -/
theorem isZero_rightDerived_sheafSections_of_cechCohomology_isZero
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    [HasSheafify J AddCommGrpCat.{max a u v w}]
    [HasExt.{max a u v w} (Sheaf J AddCommGrpCat.{max a u v w})]
    [HasInjectiveResolutions (Sheaf J AddCommGrpCat.{max a u v w})]
    (B : Set C)
    (Cov : ∀ U : C, Set { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U })
    (hProducts : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
      E ∈ Cov U → ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
        HasProduct (fun a ↦ Over.mk (E.1.f (i a))))
    (hCovObjects : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U),
      U ∈ B ∧ (∀ i, E.1.X i ∈ B) ∧
        ∀ (p : ℕ) (i : Fin (p + 1) → E.1.I₀),
          letI : ∀ (q : ℕ) (j : Fin (q + 1) → E.1.I₀),
            HasProduct (fun a ↦ Over.mk (E.1.f (j a))) := hProducts E hE
          (∏ᶜ (fun a ↦ Over.mk (E.1.f (i a)))).left ∈ B)
    (hCovCofinal : ∀ U ∈ B, ∀ R ∈ J U,
      ∃ (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }),
        E ∈ Cov U ∧ E.1.sieve₀ ≤ R)
    (F : Sheaf J AddCommGrpCat.{max a u v w})
    (hCech : ∀ {U : C}
      (E : { E : PreZeroHypercover.{w} U // E.sieve₀ ∈ J U }) (hE : E ∈ Cov U)
      (p : ℕ), 0 < p →
        letI : ∀ (q : ℕ) (i : Fin (q + 1) → E.1.I₀),
          HasProduct (fun a ↦ Over.mk (E.1.f (i a))) := hProducts E hE
        IsZero (cechCohomology E.1 F.obj p))
    (U : C) (hU : U ∈ B) (p : ℕ) (hp : 0 < p) :
    IsZero ((((sheafSections J AddCommGrpCat.{max a u v w}).obj (op U)).rightDerived p).obj F) := by
  have hsub : Subsingleton
      (Ext.{max a u v w} ((freeYoneda.{max a u v w} J).obj U) F p) :=
    subsingleton_ext_of_cechCohomology_isZero.{max a u v w, a, w, v, u}
      J B Cov hProducts hCovObjects hCovCofinal F hCech U hU p hp
  have h0 : IsZero ((extFunctorObj ((freeYoneda.{max a u v w} J).obj U) p).obj F) :=
    @AddCommGrpCat.isZero_of_subsingleton _ hsub
  exact h0.of_iso
    ((nonempty_extFunctorObj_iso_rightDerived_sections.{max a u v w, v, u}
      J U p).some.app F).symm

end Stacks.CechSite

end
