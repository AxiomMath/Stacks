module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageFullyFaithful
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OverFiniteFree
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineSectionsFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentLocality
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal

/-!
# Quasi-coherence is reflected by restriction to a dense subsite

Let `i : C ⥤ D` exhibit `(C, J)` as a dense subsite of `(D, K)` and let `R` be a sheaf of rings
on `(D, K)`. `Stacks.SheafOfModules.isQuasicoherentOnSite_restriction` says that the restriction
along `i` of a quasi-coherent sheaf of `R`-modules is quasi-coherent over the restricted
structure sheaf. This file proves the **converse**: a sheaf of `R`-modules whose restriction to
the subsite is quasi-coherent is itself quasi-coherent. Together the two give an `iff`.

The content is the Comparison Lemma for sheaves of modules: restriction along a dense subsite is
an *equivalence*, so a global presentation upstairs can be read off one downstairs. The
Comparison Lemma is proved — `Stacks.DenseSubsiteModules.moduleRestrictionEquivalence` — but only
at a single universe serving both the sections of the structure sheaf and the sections of the
modules, and a global presentation lives at a *raised* module universe over the same structure
sheaf. So the first half of this file is the Comparison Lemma again with those two universes
independent, which takes only the essential surjectivity: full faithfulness at independent
universes is `Stacks.DenseSubsiteModules.full_pushforward` and
`Stacks.DenseSubsiteModules.faithful_pushforward`.

## Main definitions

* `Stacks.DenseSubsiteModules.moduleRestrictionOfUniv`: restriction of sheaves of modules along
  a dense subsite, at a module universe independent of the universe of the structure sheaf.
* `Stacks.DenseSubsiteModules.moduleRestrictionEquivalenceOfUniv`: **the Comparison Lemma for
  sheaves of modules with the module universe independent of the universe of the sections of the
  structure sheaf.**

## Main results

* `Stacks.DenseSubsiteModules.essSurj_moduleRestrictionOfUniv`: restriction along a dense
  subsite is essentially surjective at an independent module universe.
* `Stacks.SheafOfModules.hasGlobalPresentation_of_subsiteRestriction`: **a global presentation of
  the restriction to a dense subsite comes from a global presentation.** This is the direction
  that needs the equivalence; the other one is
  `Stacks.SheafOfModules.hasGlobalPresentation_pushforward`.
* `Stacks.SheafOfModules.coversTop_obj_of_coversTop`: the images under `i` of a family covering
  the final object of the subsite cover the final object of the ambient site.
* `Stacks.SheafOfModules.isQuasicoherentOnSite_of_subsiteRestriction`: **reflection of
  quasi-coherence across a dense subsite.**
* `Stacks.SheafOfModules.isQuasicoherentOnSite_subsiteRestriction_iff`: the resulting `iff`.

## Implementation notes

Essential surjectivity at an independent module universe is formal, and is where this file
differs from the single-universe Comparison Lemma: the direct image of sheaves of modules along a fully
faithful functor of sites is fully faithful, `SheafOfModules.full_directImage`, so the counit of
its adjunction with restriction is an isomorphism and every sheaf of modules on the subsite is
the restriction of its own direct image. The universe of the module sections is then the one the
direct image is built at, `max u v w`; the single-universe essential surjectivity instead glues the
action of the structure sheaf by hand, which forces the two universes together.

`Stacks.SheafOfModules.hasGlobalPresentation_map` transports a global presentation along a
functor which preserves colimits and zero morphisms and matches up the universe-lifted structure
sheaves; it is applied here to the *inverse* of the equivalence, which preserves colimits
because it is an equivalence and is additive because restriction is
(`SheafOfModules.instAdditivePushforward`). The two comparison isomorphisms come from the
corresponding comparisons for restriction itself —
`Stacks.SheafOfModules.pushforwardUliftForPresentationIso` and the identification of the
restricted structure sheaf with the structure sheaf of the subsite — composed with the unit of
the equivalence. The equivalence is therefore used at two module universes, the module's own and
the presentation's; both are of the form `max u v _`.

The reduction of quasi-coherence to a covering family carrying global presentations is
`Stacks.SheafOfModules.isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation`, whose module
universe is independent of the universe of the coefficient rings. On a member `W` of the
covering the two restrictions — of `M` to the slice of `D` at `i W` and then to the subsite, and
of the restriction of `M` to the slice of `C` at `W` — are the same sheaf of modules, because
both are precomposition with the same functor; so the slice case is the same statement for the
dense subsite inclusion `CategoryTheory.Over.post i`, which is one by
`Stacks.Sites.overPost_isDenseSubsite`.

## References

* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU), the Comparison Lemma
* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe r w m u v

namespace Stacks.DenseSubsiteModules

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  (i : C ⥤ D) [i.Full] [i.Faithful] [i.IsDenseSubsite J K] (R : Sheaf K RingCat.{r})

/-- Restriction of sheaves of modules along the inclusion of a dense subsite, at a module
universe independent of the universe of the sections of the structure sheaf. This is
`Stacks.DenseSubsiteModules.moduleRestriction` with the two universes separated. -/
abbrev moduleRestrictionOfUniv :
    _root_.SheafOfModules.{m} R ⥤ _root_.SheafOfModules.{m} (ringRestriction J K i R) :=
  _root_.SheafOfModules.pushforward.{m} (𝟙 (ringRestriction J K i R))

/-- **Restriction of sheaves of modules along a dense subsite is essentially surjective**, at a
module universe independent of the universe of the sections of the structure sheaf: a sheaf of
modules on the subsite is the restriction of its own direct image, because the direct image
along a fully faithful functor of sites is fully faithful. -/
instance essSurj_moduleRestrictionOfUniv :
    (moduleRestrictionOfUniv.{r, max u v w} J i R).EssSurj where
  mem_essImage N :=
    have _ : IsIso (_root_.SheafOfModules.pushforwardDirectImageAdjunction.{r, w}
        i J K R).counit := Adjunction.counit_isIso_of_R_fully_faithful _
    ⟨(_root_.SheafOfModules.directImage.{r, w} i J K R).obj N,
      ⟨asIso ((_root_.SheafOfModules.pushforwardDirectImageAdjunction.{r, w}
        i J K R).counit.app N)⟩⟩

/-- Restriction of sheaves of modules along a dense subsite is an equivalence, at a module
universe independent of the universe of the sections of the structure sheaf. -/
instance isEquivalence_moduleRestrictionOfUniv :
    (moduleRestrictionOfUniv.{r, max u v w} J i R).IsEquivalence where

/-- **The Comparison Lemma for sheaves of modules, with the module universe independent of the
universe of the sections of the structure sheaf.** Restriction along the inclusion of a dense
subsite is an equivalence from sheaves of `R`-modules to sheaves of modules over the restricted
sheaf of rings.

This is `Stacks.DenseSubsiteModules.moduleRestrictionEquivalence` with the two universes
separated, which is what a *global presentation* of a sheaf of modules — taken at a raised
module universe over the same sheaf of rings — needs. -/
def moduleRestrictionEquivalenceOfUniv :
    _root_.SheafOfModules.{max u v w} R ≌
      _root_.SheafOfModules.{max u v w} (ringRestriction J K i R) :=
  (moduleRestrictionOfUniv.{r, max u v w} J i R).asEquivalence

/-- The inverse of `Stacks.DenseSubsiteModules.moduleRestrictionEquivalenceOfUniv` is additive. -/
instance additive_moduleRestrictionEquivalenceOfUniv_inverse :
    (moduleRestrictionEquivalenceOfUniv.{r, w} J i R).inverse.Additive :=
  haveI : (moduleRestrictionEquivalenceOfUniv.{r, w} J i R).functor.Additive :=
    inferInstanceAs (moduleRestrictionOfUniv.{r, max u v w} J i R).Additive
  Equivalence.inverse_additive _

end Stacks.DenseSubsiteModules

namespace Stacks.SheafOfModules

open Stacks.DenseSubsiteModules

variable {C : Type u} [Category.{v} C] {D : Type u} [Category.{v} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  (i : C ⥤ D) [i.Full] [i.Faithful] [i.IsDenseSubsite J K] (R : Sheaf K RingCat.{r})

/-- **The structure sheaf of a dense subsite is the restriction of the structure sheaf of the
ambient site**, as sheaves of modules.

That the comparison is invertible is `Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit`, which
is stated over a variable functor and so applies verbatim to `i`. -/
def subsiteRestrictionUnitIso :
    (moduleRestrictionOfUniv.{r, r} J i R).obj (_root_.SheafOfModules.unit R) ≅
      _root_.SheafOfModules.unit (ringRestriction J K i R) :=
  have _ := isIso_unitToPushforwardObjUnit (𝟙 (ringRestriction J K i R))
  (asIso (_root_.SheafOfModules.unitToPushforwardObjUnit
    (𝟙 (ringRestriction J K i R)))).symm

/-- **A global presentation of the restriction of a sheaf of modules to a dense subsite comes
from a global presentation.** This is the direction of [Stacks, Tag 03DM] for clause (6) of
[Stacks, Tag 03DL] which is not covered by
`Stacks.SheafOfModules.hasGlobalPresentation_pushforward`, and it is where the Comparison Lemma
`Stacks.DenseSubsiteModules.moduleRestrictionEquivalenceOfUniv` is spent. -/
theorem hasGlobalPresentation_of_subsiteRestriction
    (M : _root_.SheafOfModules.{max u v m} R)
    (h : ((moduleRestrictionOfUniv.{r, max u v m} J i R).obj M).HasGlobalPresentation) :
    M.HasGlobalPresentation := by
  have : PreservesColimitsOfSize.{max u v r m, max u v r m}
      (moduleRestrictionEquivalenceOfUniv.{r, max r m} J i R).inverse := inferInstance
  have : (moduleRestrictionEquivalenceOfUniv.{r, max r m} J i
      R).inverse.PreservesZeroMorphisms := inferInstance
  have k₁ : (moduleRestrictionEquivalenceOfUniv.{r, max r m} J i R).functor.obj
        (_root_.SheafOfModules.uliftForPresentation.{u, v, r, r, max u v m}
          (_root_.SheafOfModules.unit R)) ≅
      _root_.SheafOfModules.uliftForPresentation.{u, v, r, r, max u v m}
        (_root_.SheafOfModules.unit (ringRestriction J K i R)) :=
    (pushforwardUliftForPresentationIso.{u, v, r, r, max u v m} (𝟙 _)
      (_root_.SheafOfModules.unit R)).trans
      (_root_.SheafOfModules.uliftForPresentationMapIso.{u, v, r, r, max u v m}
        (subsiteRestrictionUnitIso J i R))
  have kM : (moduleRestrictionEquivalenceOfUniv.{r, max r m} J i R).functor.obj
        (_root_.SheafOfModules.uliftForPresentation.{u, v, r, max u v m, max u v r} M) ≅
      _root_.SheafOfModules.uliftForPresentation.{u, v, r, max u v m, max u v r}
        ((moduleRestrictionEquivalenceOfUniv.{r, m} J i R).functor.obj M) :=
    pushforwardUliftForPresentationIso.{u, v, r, max u v m, max u v r} (𝟙 _) M
  refine _root_.SheafOfModules.HasGlobalPresentation.of_iso
    ((moduleRestrictionEquivalenceOfUniv.{r, m} J i R).unitIso.app M).symm
    (hasGlobalPresentation_map
      ((moduleRestrictionEquivalenceOfUniv.{r, m} J i R).functor.obj M)
      (F₀ := (moduleRestrictionEquivalenceOfUniv.{r, m} J i R).inverse)
      (F := (moduleRestrictionEquivalenceOfUniv.{r, max r m} J i R).inverse)
      ((moduleRestrictionEquivalenceOfUniv.{r, max r m} J i R).inverse.mapIso k₁.symm ≪≫
        ((moduleRestrictionEquivalenceOfUniv.{r, max r m} J i R).unitIso.app _).symm)
      ((moduleRestrictionEquivalenceOfUniv.{r, max r m} J i R).inverse.mapIso kM.symm ≪≫
        ((moduleRestrictionEquivalenceOfUniv.{r, max r m} J i R).unitIso.app _).symm ≪≫
        _root_.SheafOfModules.uliftForPresentationMapIso.{u, v, r, max u v m, max u v r}
          ((moduleRestrictionEquivalenceOfUniv.{r, m} J i R).unitIso.app M)) h)

omit [i.Full] [i.Faithful] in
/-- **The images of a family covering the final object of a dense subsite cover the final object
of the ambient site.** -/
theorem coversTop_obj_of_coversTop {I : Type*} {W : I → C} (hW : J.CoversTop W) :
    K.CoversTop (fun k ↦ i.obj (W k)) := by
  have _ : i.IsCoverDense K := Functor.IsDenseSubsite.isCoverDense J K i
  have himg : ∀ W₀ : C,
      Sieve.ofObjects (fun k ↦ i.obj (W k)) (i.obj W₀) ∈ K (i.obj W₀) := by
    intro W₀
    refine K.superset_covering ?_ ((i.functorPushforward_mem_iff J K).mpr (hW W₀))
    rintro Z g ⟨W₁, a, b, ha, rfl⟩
    obtain ⟨k, ⟨t⟩⟩ := (Sieve.mem_ofObjects_iff W a).mp ha
    exact (Sieve.mem_ofObjects_iff _ _).mpr ⟨k, ⟨b ≫ i.map t⟩⟩
  intro X
  refine K.transitive (i.is_cover_of_isCoverDense K X) _ ?_
  rintro Y g ⟨⟨W₀, l, b, fac⟩⟩
  exact K.pullback_stable l (himg W₀)

/-- **Reflection of quasi-coherence across a dense subsite.** A sheaf of `R`-modules on `(D, K)`
whose restriction along the inclusion of a dense subsite `(C, J)` is quasi-coherent over the
restricted structure sheaf is itself quasi-coherent.

This is the converse of `Stacks.SheafOfModules.isQuasicoherentOnSite_restriction`. -/
theorem isQuasicoherentOnSite_of_subsiteRestriction
    (M : _root_.SheafOfModules.{max u v m} R)
    (h : ((moduleRestrictionOfUniv.{r, max u v m} J i R).obj M).IsQuasicoherentOnSite) :
    M.IsQuasicoherentOnSite := by
  obtain ⟨I, W, hW, hpres⟩ :=
    (isQuasicoherentOnSite_iff_coversTop_hasGlobalPresentation _).mp h
  refine isQuasicoherentOnSite_of_coversTop_hasGlobalPresentation M
    (coversTop_obj_of_coversTop J i hW) fun k ↦ ?_
  have _ := Stacks.Sites.overPost_isDenseSubsite (J := J) (K := K) i (W k)
  exact hasGlobalPresentation_of_subsiteRestriction.{r, m, max u v, v} (J.over (W k))
    (Over.post i) (R.over (i.obj (W k))) (M.over (i.obj (W k))) (hpres k)

/-- **Quasi-coherence of a sheaf of modules is detected on a dense subsite.** The restriction of
a sheaf of `R`-modules along the inclusion of a dense subsite, over the restricted structure
sheaf, is quasi-coherent if and only if the sheaf itself is.

The forward implication is the reflection proved here; the backward one is
`Stacks.SheafOfModules.isQuasicoherentOnSite_restriction`, which is [Stacks, Tag 03DM] for
clause (6) of [Stacks, Tag 03DL] in the dense-subsite form. -/
theorem isQuasicoherentOnSite_subsiteRestriction_iff
    (M : _root_.SheafOfModules.{max u v m} R) :
    ((moduleRestrictionOfUniv.{r, max u v m} J i R).obj M).IsQuasicoherentOnSite ↔
      M.IsQuasicoherentOnSite :=
  ⟨isQuasicoherentOnSite_of_subsiteRestriction.{r, m} J i R M, fun hM ↦
    have _ : ∀ X : C, (Over.post (X := X) i).IsContinuous (J.over X) (K.over (i.obj X)) :=
      fun X ↦
        have := Stacks.Sites.overPost_isDenseSubsite (J := J) (K := K) i X
        inferInstance
    isQuasicoherentOnSite_restriction i R M hM⟩

end Stacks.SheafOfModules

end
