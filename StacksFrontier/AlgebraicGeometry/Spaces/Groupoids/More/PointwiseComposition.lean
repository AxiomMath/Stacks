module

public import Mathlib.CategoryTheory.Limits.Types.Pullbacks
public import StacksFrontier.Deformation.Groupoid.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Composition in a groupoid in functors: the cartesian square on the target side

For a `Deformation.PointwiseGroupoid`, composition and the *first* projection out of the set
of composable pairs form a cartesian square with two copies of the *target* map. This is the
mirror of `Deformation.PointwiseGroupoid.isPullback_comp_snd`, which is the same statement for
the second projection and the source map, and both are needed to recognize the two squares of
the standard composition diagram of a groupoid.

Separately, the identity arrow of a `Deformation.GroupoidInFunctors` is natural in the test
object: transporting a point of the object functor and then taking its identity arrow agrees
with taking the identity arrow and transporting it.

## Main results

* `Deformation.PointwiseGroupoid.isPullback_comp_fst`: a composable pair is determined by its
  first arrow together with its composite, and every pair consisting of an arrow and a
  prospective composite with the same target arises from one.
* `Deformation.GroupoidInFunctors.map_identity`: naturality of the identity arrow.

## Implementation notes

The two declarations are general statements about `Deformation.PointwiseGroupoid` and
`Deformation.GroupoidInFunctors`, so their mathematical home is
`StacksFrontier/Deformation/Groupoid/Basic.lean`, beside the notions themselves. They are stated
here, alongside `Deformation.PointwiseGroupoid.ofIndexing` in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/GroupoidInSpacesOfComposable.lean`, which is in the
same situation.

In `isPullback_comp_fst` the midpoint of the categorical composite is taken to be the source of
the first arrow rather than the target of the second, which the composability hypothesis says is
the same point. That choice keeps the arrow out of the midpoint fixed as the second arrow varies,
which is what makes the two composites cancellable against it.

## References

* [Stacks Project, Tag 06K3](https://stacks.math.columbia.edu/tag/06K3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w

namespace Deformation

namespace PointwiseGroupoid

variable {U R : Type w} {source target : R → U}
  {comp : { p : R × R // source p.1 = target p.2 } → R}

/-- Composition and the first projection out of the set of composable pairs form a cartesian
square with two copies of the target map: a composable pair is determined by its first arrow
together with its composite, and every pair of an arrow and a composite with matching targets
arises from one — the second arrow being the inverse of the first followed by the composite. -/
@[sga "3 V 1.2" "(1), X2 ≅ X1 ×_{d0"]
theorem isPullback_comp_fst (H : PointwiseGroupoid source target comp) :
    IsPullback (C := Type w)
      (TypeCat.ofHom fun p : { p : R × R // source p.1 = target p.2 } => p.1.1)
      (TypeCat.ofHom comp) (TypeCat.ofHom target) (TypeCat.ofHom target) := by
  classical
  let _inst := H.groupoid
  rw [Types.isPullback_iff]
  refine ⟨?_, ?_, ?_⟩
  · ext p
    exact (H.target_comp p.1.1 p.1.2 p.2).symm
  · rintro ⟨⟨a, b⟩, hab⟩ ⟨⟨a', b'⟩, hab'⟩ ⟨hfst, hcomp⟩
    change a = a' at hfst
    subst hfst
    change comp ⟨(a, b), hab⟩ = comp ⟨(a, b'), hab'⟩ at hcomp
    have hs : source b = source b' :=
      (H.source_comp a b hab).symm.trans
        ((congrArg source hcomp).trans (H.source_comp a b' hab'))
    let α : source a ⟶ target a := (H.arrowEquiv (source a) (target a)).symm ⟨a, rfl, rfl⟩
    let β : source b ⟶ source a := (H.arrowEquiv (source b) (source a)).symm ⟨b, rfl, hab.symm⟩
    let β' : source b ⟶ source a :=
      (H.arrowEquiv (source b) (source a)).symm ⟨b', hs.symm, hab'.symm⟩
    have hcat : β ≫ α = β' ≫ α := by
      apply (H.arrowEquiv (source b) (target a)).injective
      apply Subtype.ext
      calc (H.arrowEquiv (source b) (target a) (β ≫ α)).1 = comp ⟨(a, b), hab⟩ := by
            simpa [α, β] using H.comp_eq β α
        _ = comp ⟨(a, b'), hab'⟩ := hcomp
        _ = (H.arrowEquiv (source b) (target a) (β' ≫ α)).1 := by
            simpa [α, β'] using (H.comp_eq β' α).symm
    have hb : b = b' := by
      have heq : (⟨b, rfl, hab.symm⟩ : {r : R // source r = source b ∧ target r = source a}) =
          ⟨b', hs.symm, hab'.symm⟩ := by
        simpa [β, β'] using
          congrArg (H.arrowEquiv (source b) (source a)) ((cancel_mono α).1 hcat)
      exact congrArg Subtype.val heq
    exact Subtype.ext (Prod.ext rfl hb)
  · intro a d had
    change target a = target d at had
    let α : source a ⟶ target a := (H.arrowEquiv (source a) (target a)).symm ⟨a, rfl, rfl⟩
    let γ : source d ⟶ target a := (H.arrowEquiv (source d) (target a)).symm ⟨d, rfl, had.symm⟩
    let β : source d ⟶ source a := γ ≫ Groupoid.inv α
    refine ⟨⟨(a, (H.arrowEquiv (source d) (source a) β).1),
      (H.arrowEquiv (source d) (source a) β).2.2.symm⟩, rfl, ?_⟩
    calc comp ⟨(a, (H.arrowEquiv (source d) (source a) β).1), _⟩
          = (H.arrowEquiv (source d) (target a) (β ≫ α)).1 := by
            simpa [α, β] using (H.comp_eq β α).symm
      _ = (H.arrowEquiv (source d) (target a) γ).1 :=
            congrArg (fun f => (H.arrowEquiv (source d) (target a) f).1)
              (by simp [β, Category.assoc])
      _ = d := by simp [γ]

end PointwiseGroupoid

namespace GroupoidInFunctors

/-- The identity arrow is natural: transporting a point of the object functor along `f` and
taking its identity arrow gives the transport along `f` of its identity arrow.

An endomorphism of the evaluated groupoid which is idempotent is the identity, and the
transport of an identity arrow is idempotent because transport preserves composition. -/
theorem map_identity {C : Type u} [Category.{v} C] (D : GroupoidInFunctors.{u, v, w} C)
    {X Y : C} (f : X ⟶ Y) (x : D.objects.obj X) :
    D.arrows.map f (D.identity X x) = D.identity Y (D.objects.map f x) := by
  let _instX : Groupoid (D.objects.obj X) := D.evaluationGroupoid X
  let _instY : Groupoid (D.objects.obj Y) := D.evaluationGroupoid Y
  let a := D.identity X x
  let b := D.arrows.map f a
  let y := D.objects.map f x
  have haS : D.source.app X a = x := (D.evaluationArrowEquiv X x x (𝟙 x)).2.1
  have haT : D.target.app X a = x := (D.evaluationArrowEquiv X x x (𝟙 x)).2.2
  have hbS : D.source.app Y b = y := by
    show D.source.app Y (D.arrows.map f a) = D.objects.map f x
    rw [NatTrans.naturality_apply D.source f a, haS]
  have hbT : D.target.app Y b = y := by
    show D.target.app Y (D.arrows.map f a) = D.objects.map f x
    rw [NatTrans.naturality_apply D.target f a, haT]
  have hmulA : D.compose X a a (haS.trans haT.symm) = a := by
    simpa only [a, identity, Category.id_comp] using
      (D.evaluationArrowEquiv_comp X (𝟙 x) (𝟙 x)).symm
  have hmulB : D.compose Y b b (hbS.trans hbT.symm) = b := by
    have hn := NatTrans.naturality_apply D.comp f ⟨(a, a), haS.trans haT.symm⟩
    change D.compose Y b b (hbS.trans hbT.symm) =
      D.arrows.map f (D.compose X a a (haS.trans haT.symm)) at hn
    rwa [hmulA] at hn
  let β : y ⟶ y := (D.evaluationArrowEquiv Y y y).symm ⟨b, hbS, hbT⟩
  have hβ : β ≫ β = β := by
    apply (D.evaluationArrowEquiv Y y y).injective
    apply Subtype.ext
    rw [D.evaluationArrowEquiv_comp]
    simpa only [β, Equiv.apply_symm_apply] using hmulB
  have hβid : β = 𝟙 y := (cancel_mono β).1 (by rw [hβ, Category.id_comp])
  have h := congrArg (fun k : y ⟶ y => (D.evaluationArrowEquiv Y y y k).1) hβid
  simp only [β, Equiv.apply_symm_apply] at h
  exact h

end GroupoidInFunctors

end Deformation

end
