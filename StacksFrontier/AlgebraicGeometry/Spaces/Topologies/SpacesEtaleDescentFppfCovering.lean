module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatImageOpenSubspace
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentEtaleLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentSchemeTarget
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.SpacesEtaleDescentSurjective
public import StacksFrontier.CategoryTheory.Sites.Descent.MemberDescentOfBaseChange

/-!
# Descent of étale sheaves along an fppf covering of algebraic spaces

Let `{f i : X i ⟶ Y}` be an fppf covering of algebraic spaces over a scheme `S`. Sheaves on the
spaces-étale site of `Y` are equivalent, through the canonical descent datum, to descent data
for the covering. This is **Stacks 0GFX**, deduced here from the flat case of Stacks 0GFW, that
is, from effective descent along one surjective flat morphism locally of finite presentation,
which follows from Stacks 0GFV.

## Main results

All names below are in the namespace `AlgebraicGeometry.Space`.

* `isEquivalence_toDescentData_of_isFppfCovering_of_flat`: Stacks 0GFX from the flat case of
  Stacks 0GFW.
* `isEquivalence_toDescentData_of_isFppfCovering_of_representablePrecomposition`: Stacks 0GFX
  from Stacks 0GFV.
* `isEquivalence_toDescentData_of_isFppfCovering`: **Stacks 0GFX**, with no hypothesis.

## References

* [Stacks Project, Tag 0GFX](https://stacks.math.columbia.edu/tag/0GFX)
* [Stacks Project, Tag 0GFW](https://stacks.math.columbia.edu/tag/0GFW)
* [Stacks Project, Tag 0GFS](https://stacks.math.columbia.edu/tag/0GFS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0GFX, from the flat case of Stacks 0GFW.** Suppose that descent of spaces-étale
sheaves is effective along every surjective flat morphism of algebraic spaces locally of finite
presentation. Then for an fppf covering `{f i : X i ⟶ Y}` of algebraic spaces over `S`, sheaves
on the spaces-étale site of `Y` are equivalent, through the canonical descent datum, to descent
data for the covering. -/
theorem isEquivalence_toDescentData_of_isFppfCovering_of_flat
    (hflat : ∀ ⦃X Y : AlgebraicSpaces B S hS⦄ (f : X ⟶ Y), IsSurjective B S hS f.hom →
      IsFlat B S hS f.hom → IsLocallyOfFinitePresentation B S hS f.hom →
      ((spacesEtalePseudofunctor B S hS).toDescentData (fun _ : Unit => f)).IsEquivalence)
    {I : Type v} {X : I → AlgebraicSpaces B S hS} {Y : AlgebraicSpaces B S hS}
    (f : ∀ i, X i ⟶ Y) (hf : IsFppfCovering B S hS (fun i => (X i).1) (fun i => (f i).hom)) :
    ((spacesEtalePseudofunctor B S hS).toDescentData f).IsEquivalence := by
  let V : I → AlgebraicSpaces B S hS := fun i =>
    flatImage B S hS (f i) (hf.flat i) (hf.locallyOfFinitePresentation i)
  let g : ∀ i, V i ⟶ Y := fun i =>
    flatImageι B S hS (f i) (hf.flat i) (hf.locallyOfFinitePresentation i)
  have hg : IsEtaleCovering B S hS (fun i => (V i).1) (fun i => (g i).hom) :=
    isEtaleCovering_flatImageι B S hS f hf
  have hmem : ∀ (j : I) {T : AlgebraicSpaces B S hS} (t : T ⟶ Y) (a : T ⟶ V j), a ≫ g j = t →
      ((spacesEtalePseudofunctor B S hS).toDescentData
        (fun i => pullback.snd (f i) t)).IsEquivalence := fun j _ t a ha =>
    Pseudofunctor.isEquivalence_toDescentData_of_mem _ (surjectiveFlatLfp B S hS)
      (fun _ _ h hh => hflat h hh.1 hh.2.1 hh.2.2) _ j
      (surjectiveFlatLfp_pullback_snd_of_fac B S hS (f j) _ _ t a ha)
  refine Pseudofunctor.isEquivalence_toDescentData_of_baseChange_unconditional f g
    (SpacesEtale.isEquivalence_toDescentData_spacesEtalePseudofunctor_of_isEtaleCovering B S hS
      V g hg) (fun T t => ?_) (fun j => hmem j (g j) (𝟙 _) (Category.id_comp _))
    (fun j k => ?_) (fun j k l _ _ x y hxy => ?_)
  · let e : ∀ j, pullback t (g j) ≅ (spacesChosenPullback B S hS t (g j)).pullback := fun j =>
      (IsPullback.of_hasPullback t (g j)).isoIsPullback _ _
        (spacesChosenPullback B S hS t (g j)).isPullback
    have he : ∀ j, (e j).hom ≫ (spacesChosenPullback B S hS t (g j)).p₁ =
        pullback.fst t (g j) := fun j =>
      (IsPullback.of_hasPullback t (g j)).isoIsPullback_hom_fst _ _
        (spacesChosenPullback B S hS t (g j)).isPullback
    have hs : Sieve.ofArrows _ (fun j => pullback.fst t (g j)) =
        Sieve.ofArrows _ (fun j => (spacesChosenPullback B S hS t (g j)).p₁) := by
      refine le_antisymm (Sieve.generate_le_iff _ _ |>.2 ?_) (Sieve.generate_le_iff _ _ |>.2 ?_)
      · rintro _ _ ⟨j⟩
        exact ⟨_, (e j).hom, _, Presieve.ofArrows.mk j, he j⟩
      · rintro _ _ ⟨j⟩
        exact ⟨_, (e j).inv, _, Presieve.ofArrows.mk j, by rw [← he j, Iso.inv_hom_id_assoc]⟩
    have := (Pseudofunctor.DescentData.isEquivalence_toDescentData_iff_of_sieve_eq _ _ _ hs).2
      (isEquivalence_toDescentData_spacesChosenPullback_p₁ B S hS V g hg t)
    exact ⟨.ofFullyFaithful _⟩
  · have := hmem j _ (pullback.fst (g j) (g k)) rfl
    exact ⟨.ofFullyFaithful _⟩
  · have := hmem j _ (Pseudofunctor.tripleProj₁ g j k l) rfl
    exact Pseudofunctor.eq_of_toDescentData_faithful _ hxy

/-- **Stacks 0GFX, from Stacks 0GFV.** If Stacks 0GFV holds over the big fppf site `B`, then for
an fppf covering `{f i : X i ⟶ Y}` of algebraic spaces over `S`, sheaves on the spaces-étale site
of `Y` are equivalent, through the canonical descent datum, to descent data for the covering. -/
theorem isEquivalence_toDescentData_of_isFppfCovering_of_representablePrecomposition
    (hGFV : DescentEffectiveAlongRepresentablePrecomposition B S hS) {I : Type v}
    {X : I → AlgebraicSpaces B S hS} {Y : AlgebraicSpaces B S hS} (f : ∀ i, X i ⟶ Y)
    (hf : IsFppfCovering B S hS (fun i => (X i).1) (fun i => (f i).hom)) :
    ((spacesEtalePseudofunctor B S hS).toDescentData f).IsEquivalence :=
  isEquivalence_toDescentData_of_isFppfCovering_of_flat B S hS
    (fun _ _ ↦ isEquivalence_toDescentData_singleton_of_isFlat B S hS hGFV) f hf

/-- Let `S` be a scheme and let `{f i : X i ⟶ Y}` be an fppf covering of algebraic spaces over
`S`. Then the functor from sheaves on the spaces-étale site of `Y` (that is, `Sh(Y_étale)`) to
descent data for étale sheaves with respect to `{f i : X i ⟶ Y}` is an equivalence of
categories. -/
@[stacks 0GFX]
theorem isEquivalence_toDescentData_of_isFppfCovering {I : Type v}
    {X : I → AlgebraicSpaces B S hS} {Y : AlgebraicSpaces B S hS} (f : ∀ i, X i ⟶ Y)
    (hf : IsFppfCovering B S hS (fun i => (X i).1) (fun i => (f i).hom)) :
    ((spacesEtalePseudofunctor B S hS).toDescentData f).IsEquivalence :=
  isEquivalence_toDescentData_of_isFppfCovering_of_representablePrecomposition B S hS
    (isEquivalence_toDescentData_singleton_of_relativelyRepresentable_comp B S hS) f hf

end AlgebraicGeometry.Space

end
