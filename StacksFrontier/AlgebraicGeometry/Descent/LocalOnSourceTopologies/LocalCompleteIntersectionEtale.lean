module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleSourceLocality
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.OpenImmersion

/-!
# The Koszul property is local on the source for the smooth and étale topologies

A morphism of affine schemes is a local complete intersection morphism as soon as its
precomposition with a surjective *smooth* morphism of affine schemes is. Together with the three
remaining inputs of **Stacks 036H** — Zariski locality on the source and on the target, and
preservation under precomposition — this makes the Koszul property local on the source for the
étale topology, which is **Stacks 069P** restricted to étale coverings.

## Main results

* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_surjective_smooth_of_isAffine`: the
  affine descent along a surjective smooth morphism.
* `AlgebraicGeometry.isLocalCompleteIntersectionMorphism_isLocalAtSource_etale`: the Koszul
  property of morphisms of schemes is local on the source for the étale topology.

## Implementation notes

The smooth case of the descent needs no conormal sequence, which is what distinguishes it from
the syntomic case of
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersectionAffine`.
Given `g : X' ⟶ X` surjective smooth and `f : X ⟶ Y` with `g ≫ f` Koszul, `f` is locally of
finite presentation by faithfully flat descent, hence is a closed immersion `i : X ⟶ P` into a
relative affine space `P` over `Y` followed by the smooth projection `π`, and it suffices to see
that `i` is Koszul-regular. The smooth case of **Stacks 04E3** covers `X'` by base changes
`X ×_P V_a` of `i` along *smooth* morphisms `q_a : V_a ⟶ P`, through open immersions
`t_a : X ×_P V_a ⟶ X'` over `X`. Since `q_a` is smooth, so is `q_a ≫ π : V_a ⟶ Y`, and the base
change of `i` along `q_a` composed with it is `t_a ≫ (g ≫ f)`, which is Koszul because `t_a` is
an open immersion. **Stacks 069G** therefore makes that base change of `i` Koszul-regular
outright, and `i` is Koszul-regular by **Stacks 0694**.

In the syntomic case `q_a` is only syntomic, so `q_a ≫ π` is not smooth and Stacks 069G does not
apply; that is where the padding step and the conormal sequence of Stacks 062S are needed.

## References

* [The Stacks Project, Lemma 35.26.4 (036H)](https://stacks.math.columbia.edu/tag/036H)
* [The Stacks Project, Lemma 35.23.34 (0694)](https://stacks.math.columbia.edu/tag/0694)
* [The Stacks Project, Lemma 37.62.11 (069G)](https://stacks.math.columbia.edu/tag/069G)
* [The Stacks Project, Lemma 37.62.20 (069P)](https://stacks.math.columbia.edu/tag/069P)
* [The Stacks Project, Lemma 36.16.3 (04E3)](https://stacks.math.columbia.edu/tag/04E3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RegularIdealSheaf

universe u

namespace AlgebraicGeometry

/-- The Koszul property of morphisms of schemes is preserved by precomposition with an étale
morphism: an étale morphism is syntomic, hence Koszul by Stacks 069K, and Koszul morphisms
compose by Stacks 069J. -/
instance respectsLeft_etale_isLocalCompleteIntersectionMorphism :
    MorphismProperty.RespectsLeft
      (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u})
      (@Etale.{u} : MorphismProperty Scheme.{u}) :=
  ⟨fun i hi f hf => by
    have : Etale i := hi
    exact isLocalCompleteIntersectionMorphism_comp i f
      (isLocalCompleteIntersectionMorphism_of_syntomic (syntomic_of_etale i)) hf⟩

/-- A Koszul-regular immersion stays Koszul-regular when its name is rewritten: the
`AlgebraicGeometry.IsImmersion` argument of `AlgebraicGeometry.IsKoszulRegularImmersion` is a
proof, so the predicate transports along an equality of morphisms. -/
private theorem isKoszulRegularImmersion_of_eq {A C : Scheme.{u}} {k l : A ⟶ C}
    [IsImmersion k] [IsImmersion l] (h : k = l) (hk : IsKoszulRegularImmersion k) :
    IsKoszulRegularImmersion l := by
  subst h
  exact hk

/-- **The smooth case of the affine descent of Stacks 069P.** A morphism of affine schemes is a
local complete intersection morphism as soon as its precomposition with a surjective smooth
morphism of affine schemes is.

`f` is locally of finite presentation by faithfully flat descent along `g`, so it is a closed
immersion `i` into a relative affine space over its target followed by the smooth projection `π`,
and it suffices to see that `i` is Koszul-regular. The smooth case of Stacks 04E3 covers the
source of `g` by base changes of `i` along smooth morphisms `q_a` to that affine space, and by
Stacks 0694 it is enough to see that each base change of `i` along `q_a` is Koszul-regular. That
base change, composed with the smooth morphism `q_a ≫ π`, is the restriction of `g ≫ f` along an
open immersion, so Stacks 069G applies to it directly. -/
theorem isLocalCompleteIntersectionMorphism_of_surjective_smooth_of_isAffine
    {X' X Y : Scheme.{u}} [IsAffine X'] [IsAffine X] [IsAffine Y] (g : X' ⟶ X) (f : X ⟶ Y)
    (hsurj : Surjective g) (hsm : Smooth g)
    (hlci : IsLocalCompleteIntersectionMorphism (g ≫ f)) :
    IsLocalCompleteIntersectionMorphism f := by
  have : Flat g := flat (syntomic_of_smooth g)
  have := locallyOfFinitePresentation_of_isLocalCompleteIntersectionMorphism hlci
  have : LocallyOfFinitePresentation f := by
    rw [HasRingHomProperty.iff_of_isAffine (P := @LocallyOfFinitePresentation)]
    refine RingHom.finitePresentation_of_comp_of_faithfullyFlat f.appTop.hom g.appTop.hom ?_ ?_
      (Scheme.Hom.finitePresentation_appTop g)
    · simpa only [Scheme.Hom.comp_appTop, CommRingCat.hom_comp] using
        Scheme.Hom.finitePresentation_appTop (g ≫ f)
    · exact (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine g).mp ⟨inferInstance, hsurj⟩
  obtain ⟨n, i, hi, hbase⟩ := exists_closedImmersion_affineSpace_of_lfp f
  set π : AffineSpace (ULift.{u} (Fin n)) Y ⟶ Y :=
    AffineSpace (ULift.{u} (Fin n)) Y ↘ Y with hπ
  have hπsm : Smooth π := smooth_affineSpace_over _ _
  have hreg : IsKoszulRegularImmersion i := by
    obtain ⟨J, W, q, t, hq, ht, hcover⟩ :=
      exists_smooth_zariskiCover_baseChange_of_isClosedImmersion i g
    have hcov := (Scheme.ofArrows_mem_precoverage_iff _).mp hcover
    apply isKoszulRegularImmersion_of_flat_covers_image i W q
      (fun a => have := hq a; flat (syntomic_of_smooth (q a)))
      (fun a => have := hq a; locallyOfFinitePresentation (syntomic_of_smooth (q a)))
    · intro z
      obtain ⟨z', hz'⟩ := hsurj.surj z
      obtain ⟨a, w, hw⟩ := hcov.1 z'
      refine ⟨a, (pullback.fst (q a) i).base w, ?_⟩
      have htw : (pullback.snd (q a) i).base w = z := by
        rw [← ht a]
        change g.base ((t a).base w) = z
        rw [hw, hz']
      have hc := congrArg (fun k : pullback (q a) i ⟶ _ => k.base w)
        (pullback.condition (f := q a) (g := i))
      change (q a).base ((pullback.fst (q a) i).base w) =
        i.base ((pullback.snd (q a) i).base w) at hc
      exact hc.trans (congrArg i.base htw)
    · intro a
      let _ : IsOpenImmersion (t a) := hcov.2 a
      let _ : Smooth (q a) := hq a
      have : Smooth (q a ≫ π) := MorphismProperty.comp_mem _ _ _ (hq a) hπsm
      have hkey : IsLocalCompleteIntersectionMorphism (pullback.fst (q a) i ≫ q a ≫ π) := by
        rw [pullback.condition_assoc, hbase, ← ht a, Category.assoc]
        exact isLocalCompleteIntersectionMorphism_comp (t a) (g ≫ f)
          (isLocalCompleteIntersectionMorphism_of_syntomic (syntomic_of_isOpenImmersion (t a))) hlci
      exact isKoszulRegularImmersion_of_eq
        (k := (pullbackSymmetry i (q a)).hom ≫ pullback.fst (q a) i) (by simp)
        (Stacks.AlgebraicGeometry.isKoszulRegularImmersion_comp _ _
          (isKoszulRegularImmersion_of_isOpenImmersion _)
          (isKoszulRegularImmersion_of_koszul_comp_smooth (pullback.fst (q a) i) (q a ≫ π) hkey))
  exact isLocalCompleteIntersectionMorphism_of_koszulRegular_affineImmersion f n i hbase hreg

/-- **Stacks 069P, restricted to étale coverings.** The property of being a local complete
intersection morphism of schemes is local on the source for the étale topology: a morphism is
Koszul exactly when its composites with the members of an étale covering of its source are.

All four inputs of the étale case of Stacks 036H are available: Zariski locality on the source
and on the target come from
`StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.LocalCompleteIntersection`,
preservation under precomposition with an étale morphism is
`AlgebraicGeometry.respectsLeft_etale_isLocalCompleteIntersectionMorphism`, and the affine
descent is
`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_surjective_smooth_of_isAffine` read at
an étale `g`. -/
@[stacks 069P "the étale case, unconditionally: the Koszul property of morphisms of schemes is \
local on the source for the étale topology. The syntomic statement of the tag is not claimed \
here"]
theorem isLocalCompleteIntersectionMorphism_isLocalAtSource_etale :
    MorphismProperty.IsLocalAtSource
      (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u})
      Scheme.etalePrecoverage :=
  isLocalAtSource_etale_of_affine_descent
    (@IsLocalCompleteIntersectionMorphism.{u} : MorphismProperty Scheme.{u})
    fun g f hsurj hetale hcomp =>
      isLocalCompleteIntersectionMorphism_of_surjective_smooth_of_isAffine g f hsurj
        (have : Etale g := hetale; inferInstance) hcomp

end AlgebraicGeometry

end
