module

public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FlatLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleMorphisms
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.RepresentableByAlgebraicSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves

/-!
# A representable surjective flat morphism of finite presentation is locally surjective

Let `S` be a scheme contained in a big fppf site `B` and let `a : F ⟶ G` be a morphism of
presheaves on the big fppf site of `S` which is representable by algebraic spaces and whose
base change along every scheme-valued point of `G` is surjective, flat and locally of finite
presentation. Then `a` is *locally surjective*: every section of `G` over an object of the
site comes from a section of `F` after restriction along a covering sieve of the big fppf
topology.

Surjectivity of a map of sheaves in the sense of Sites, Definition **00WM** is
`CategoryTheory.Presheaf.IsLocallySurjective`, which Mathlib carries for an arbitrary
Grothendieck topology on an arbitrary site; nothing about the big fppf site is needed to state
it and nothing is introduced here to express it.

The argument is the source's own, and every step of it is a lemma this library already has.
Fix an object `U` of the site and a section `x` of `G` over `U`; by the Yoneda lemma `x` is a
morphism `ξ : h_U ⟶ G`. The fibre product `P = h_U ×_G F` is an algebraic space, because `a` is
representable by algebraic spaces, and its first projection `p : P ⟶ h_U` is surjective, flat
and locally of finite presentation by hypothesis. An algebraic space has a surjective étale
scheme atlas `φ : h_V ⟶ P`; an atlas is itself flat and locally of finite presentation, so the
composite `φ ≫ p : h_V ⟶ h_U` is surjective, flat and locally of finite presentation, and by
full faithfulness of Yoneda it is `h_j` for a morphism `j : V ⟶ U` of the site whose underlying
morphism of schemes has those three properties. The one-member family `j` therefore generates a
covering sieve of `U` every arrow of which factors through `j`. Finally the second projection
`P ⟶ F`, composed with the atlas, is a section of `F` over `V` whose image under `a` is the
restriction of `x`, so the covering sieve is contained in the image sieve of `x`.

## Main results

* `AlgebraicGeometry.Space` namespace,
  `isLocallySurjective_of_isSurjective_isFlat_isLocallyOfFinitePresentation`: the content of
  Bootstrap, Lemma **04S1**.

## Implementation notes

The three hypotheses are spelled as the universally quantified conditions on the base changes
of `a` rather than through `AlgebraicGeometry.Space.HasProperty`, the library's form
of Stacks **03XZ**. That predicate is an `abbrev` whose body is exactly this quantification, so a
consumer holding it at a `CategoryTheory.MorphismProperty` wrapper may pass it directly; writing
the quantification out avoids introducing wrappers for flatness and local finite presentation,
of which the library has none, purely to state this lemma.

The hypotheses that `F` and `G` are sheaves are *not* taken. They occur in the source's
statement, and the source's proof — like the proof here — never uses them: the conclusion is a
condition on the image sieves of sections of `G`, which is meaningful for an arbitrary presheaf.
Omitting them gives the stronger statement, and a consumer with the sheaf conditions in hand can
ignore them.

No `@[stacks 04S1]` attribute is placed. Tag **04S1** belongs to Bootstrap, Chapter 80; the
declaration is left unregistered here.

## References

* [Stacks Project, Tag 04S1](https://stacks.math.columbia.edu/tag/04S1)
* [Stacks Project, Tag 00WM](https://stacks.math.columbia.edu/tag/00WM)
* [Stacks Project, Tag 03XZ](https://stacks.math.columbia.edu/tag/03XZ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

/-- **Bootstrap, Lemma 04S1.** A morphism of presheaves on the big fppf site of `S` which is
representable by algebraic spaces and whose base change along every scheme-valued point of the
target is surjective, flat and locally of finite presentation is surjective as a map of
sheaves, that is, locally surjective for the big fppf topology. -/
public theorem isLocallySurjective_of_isSurjective_isFlat_isLocallyOfFinitePresentation
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (ha : IsRepresentableByAlgebraicSpaces B S hS a)
    (hsurj : ∀ (U : BigFppfOver B S hS) (ξ : yoneda.obj U ⟶ G),
      IsSurjective B S hS (pullback.fst ξ a))
    (hflat : ∀ (U : BigFppfOver B S hS) (ξ : yoneda.obj U ⟶ G),
      IsFlat B S hS (pullback.fst ξ a))
    (hlfp : ∀ (U : BigFppfOver B S hS) (ξ : yoneda.obj U ⟶ G),
      IsLocallyOfFinitePresentation B S hS (pullback.fst ξ a)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS) a := by
  refine ⟨fun {U} x => ?_⟩
  set ξ : yoneda.obj U ⟶ G := yonedaEquiv.symm x with hξ
  set p : pullback ξ a ⟶ yoneda.obj U := pullback.fst ξ a with hp
  have hP : IsAlgebraicSpace B S hS (pullback ξ a) := ha U ξ
  have hU : IsAlgebraicSpace B S hS (yoneda.obj U) := isAlgebraicSpace_yoneda B S hS U
  obtain ⟨V, φ, hφsurj, hφet⟩ := hP.exists_atlas
  have hV : IsAlgebraicSpace B S hS (yoneda.obj V) := isAlgebraicSpace_yoneda B S hS V
  have hφE : IsEtale B S hS φ := (isEtale_iff_presheaf_of_yoneda B S hS φ).2 hφet
  -- The atlas composed with the structure morphism, read as a morphism of the site.
  set j : V ⟶ U := yoneda.preimage (φ ≫ p) with hjdef
  have hjm : yoneda.map j = φ ≫ p := yoneda.map_preimage _
  -- Its three properties, at the level of schemes.
  have hmflat : Flat (B.inclusion.map j.left) := by
    refine (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      Flat.isEtaleLocalOnSourceAndTarget j).1 ?_
    rw [hjm]
    exact isFlat_comp B S hS hV hP hU φ p (isFlat_atlas B S hS hP hφE) (hflat U ξ)
  have hmlfp : LocallyOfFinitePresentation (B.inclusion.map j.left) := by
    refine (holdsOnEveryEtaleChart_yoneda_map_iff B S hS
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget j).1 ?_
    rw [hjm]
    exact isLocallyOfFinitePresentation_comp B S hS hV hP hU φ p
      (isLocallyOfFinitePresentation_atlas B S hS hP hφE) (hlfp U ξ)
  have hmsurj : Surjective (B.inclusion.map j.left) := by
    refine (presheaf_yoneda_map_iff B S hS
      (inferInstance : MorphismProperty.IsStableUnderBaseChange
        (@_root_.AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})) j).1 ?_
    refine (surjective_yonedaMap_iff_surjective_pointsMap B S hS j).2 ?_
    rw [hjm]
    exact isSurjective_comp B S hS
      ((surjective_iff_surjective_pointsMap B S hS (pullback ξ a) hP V φ).1 hφsurj)
      (hsurj U ξ)
  -- The one-member family generates a covering sieve whose arrows factor through `j`.
  obtain ⟨R, hR, hfac⟩ := exists_mem_topology_of_family B S hS (I := PUnit.{u + 2})
    (fun _ => V.left) (fun _ => j.left) (fun _ => hmflat) (fun _ => hmlfp)
    (fun z => ⟨PUnit.unit, hmsurj.1 z⟩)
  -- Every arrow factoring through `j` carries a section of `F` restricting `x`.
  have hgen : ∀ (W : BigFppfOver B S hS) (g : W ⟶ U) (β : W ⟶ V), β ≫ j = g →
      (Presheaf.imageSieve a x).arrows g := by
    intro W g β hβ
    rw [Presheaf.imageSieve_apply]
    refine ⟨(yoneda.map β ≫ φ ≫ pullback.snd ξ a).app (op W) (𝟙 W), ?_⟩
    have h : (yoneda.map β ≫ φ ≫ pullback.snd ξ a) ≫ a = yoneda.map g ≫ ξ := by
      subst hβ
      simp [hjm, hp, pullback.condition]
    have hh := congrArg (fun f => f.app (op W) (𝟙 W)) h
    simpa [hξ] using hh
  have hw : (𝟙 (Over.left V)) ≫ Over.hom V
      = Over.hom (Over.mk (j.left ≫ Over.hom U) : BigFppfOver B S hS) := by
    simp
  have hβj : (Over.homMk (𝟙 (Over.left V)) hw :
        (Over.mk (j.left ≫ Over.hom U) : BigFppfOver B S hS) ⟶ V) ≫ j
      = (Over.homMk j.left rfl :
        (Over.mk (j.left ≫ Over.hom U) : BigFppfOver B S hS) ⟶ U) :=
    Over.OverMorphism.ext (by simp)
  refine (BigFppfOver.topology B S hS).superset_covering (fun W k hk => ?_) hR
  obtain ⟨_, b, hb⟩ := hfac hk
  refine hgen W k (b ≫ Over.homMk (𝟙 (Over.left V)) hw) ?_
  rw [Category.assoc, hβj, hb]

end AlgebraicGeometry.Space

end
