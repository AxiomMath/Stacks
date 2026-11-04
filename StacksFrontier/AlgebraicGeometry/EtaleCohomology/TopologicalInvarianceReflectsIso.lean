module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceThickening

/-!
# A morphism of étale schemes which is an isomorphism over a thickening

Let `S₀ ⊆ S` be a closed subscheme with the same underlying topological space, of arbitrary
order, and let `f : P ⟶ Q` be a morphism of schemes étale over `S`. If the base change of `f`
along `S₀ ⟶ S` is an isomorphism, then `f` is an isomorphism.

This is the conservativity of base change along a thickening on étale schemes, which is part of
Stacks 039R: an equivalence of categories reflects isomorphisms.

## Main results

* `Stacks.Etale.isIso_of_isIso_pullbackMap_of_isClosedImmersion`: a morphism of schemes étale
  over `S` whose base change along a surjective closed immersion `S₀ ⟶ S` is an isomorphism is
  an isomorphism.
* `Stacks.Etale.isIso_of_isPullback_of_isClosedImmersion`: the same statement with the two base
  changes given by arbitrary cartesian squares rather than by the chosen pullbacks.

## Implementation notes

The morphism is read as a morphism in the category `S.Etale` of schemes étale over `S`, the
base change functor `MorphismProperty.Over.pullback` is an equivalence by
`Stacks.Etale.etalePullback_isEquivalence_of_surjective_isClosedImmersion`, and the forgetful
functors back to schemes reflect isomorphisms. The base change of `f` is stated as
`CategoryTheory.Limits.pullback.map`, which agrees with the morphism the base change functor
produces.

## References

* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace Stacks.Etale

variable {S₀ S : Scheme.{u}}

/-- **A morphism of étale schemes which is an isomorphism over a thickening is an
isomorphism.** Let `i : S₀ ⟶ S` be a closed immersion which is surjective on points, and let
`f : P ⟶ Q` be a morphism over `S` of schemes étale over `S`. If the base change of `f` along
`i` is an isomorphism then so is `f`, base change along `i` being an equivalence on étale
schemes (Stacks 039R). -/
theorem isIso_of_isIso_pullbackMap_of_isClosedImmersion (i : S₀ ⟶ S) [IsClosedImmersion i]
    (hi : Function.Surjective i.base) {P Q : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S) [Etale p]
    [Etale q] (f : P ⟶ Q) (hf : f ≫ q = p)
    [hiso : IsIso (pullback.map p i q i f (𝟙 S₀) (𝟙 S) (by simp [hf]) (by simp))] :
    IsIso f := by
  let : MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) i :=
    ⟨fun _ _ ↦ inferInstance⟩
  let : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) i :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  have hE := etalePullback_isEquivalence_of_surjective_isClosedImmersion i hi
  let F : S.Etale ⥤ S₀.Etale :=
    MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ i
  let P' : S.Etale := Scheme.Etale.mk p
  let Q' : S.Etale := Scheme.Etale.mk q
  let f' : P' ⟶ Q' := MorphismProperty.Over.homMk f hf
  have heq : (F.map f').left =
      pullback.map p i q i f (𝟙 S₀) (𝟙 S) (by simp [hf]) (by simp) := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (pullback.lift_fst _ _ _).symm
    · exact (pullback.lift_snd _ _ _).trans
        ((pullback.lift_snd _ _ _).trans (Category.comp_id _)).symm
  have h0 : IsIso (F.map f').left := by rwa [heq]
  have h2 : IsIso (F.map f') := by
    have : IsIso ((Scheme.Etale.forget S₀ ⋙ Over.forget S₀).map (F.map f')) := h0
    exact isIso_of_reflects_iso (F.map f') (Scheme.Etale.forget S₀ ⋙ Over.forget S₀)
  have h3 : IsIso f' := isIso_of_reflects_iso f' F
  exact inferInstanceAs (IsIso ((Scheme.Etale.forget S ⋙ Over.forget S).map f'))

/-- **A morphism of étale schemes which is an isomorphism over a thickening is an isomorphism**,
with the base changes given by cartesian squares. Let `i : S₀ ⟶ S` be a closed immersion which is
surjective on points, let `f : P ⟶ Q` be a morphism over `S` of schemes étale over `S`, and let
`P₀ ⟶ P` and `Q₀ ⟶ Q` be base changes of `P ⟶ S` and `Q ⟶ S` along `i`. If a morphism
`f₀ : P₀ ⟶ Q₀` lying over `f` is an isomorphism then so is `f`. -/
theorem isIso_of_isPullback_of_isClosedImmersion (i : S₀ ⟶ S) [IsClosedImmersion i]
    (hi : Function.Surjective i.base) {P Q P₀ Q₀ : Scheme.{u}} (p : P ⟶ S) (q : Q ⟶ S) [Etale p]
    [Etale q] (f : P ⟶ Q) (hf : f ≫ q = p) {a : P₀ ⟶ P} {p₀ : P₀ ⟶ S₀}
    (hP : IsPullback a p₀ p i) {b : Q₀ ⟶ Q} {q₀ : Q₀ ⟶ S₀} (hQ : IsPullback b q₀ q i)
    (f₀ : P₀ ⟶ Q₀) [IsIso f₀] (hf₀ : f₀ ≫ b = a ≫ f) : IsIso f := by
  have hq₀ : f₀ ≫ q₀ = p₀ := by
    rw [← cancel_mono i, Category.assoc, ← hQ.w, reassoc_of% hf₀, hf, hP.w]
  have heq : pullback.map p i q i f (𝟙 S₀) (𝟙 S) (by simp [hf]) (by simp) =
      hP.isoPullback.inv ≫ f₀ ≫ hQ.isoPullback.hom := by
    apply pullback.hom_ext
    · exact (pullback.lift_fst _ _ _).trans (by simp [hf₀])
    · exact (pullback.lift_snd _ _ _).trans (by simp [hq₀])
  have : IsIso (pullback.map p i q i f (𝟙 S₀) (𝟙 S) (by simp [hf]) (by simp)) := by
    rw [heq]
    infer_instance
  exact isIso_of_isIso_pullbackMap_of_isClosedImmersion i hi p q f hf

end Stacks.Etale

end
