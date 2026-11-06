module

public import StacksFrontier.AlgebraicGeometry.Etale.UniversallyInjectiveUnramified.Basic
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Stability
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.ThickeningMorphism.Topological

/-!
# A monomorphism deforms across a morphism of thickenings

Let

```
R  --j-->  W
|          |
i          k
v          v
R' --j'--> W'
```

be a commuting square of schemes in which the two vertical arrows are thickenings. If the upper
horizontal arrow `j` is a monomorphism and the lower one `j'` is unramified, then `j'` is a
monomorphism too. The thickenings are not required to be of bounded order.

## Main results

* `Stacks.Thickenings.mono_of_isThickening_of_unramified`: the statement above.
* `Stacks.Thickenings.isThickening_pullbackMapSelf`: the self-product of a thickening over a
  base is a thickening.
* `Stacks.Thickenings.mono_pullbackLift_of_isThickening`: if a pair of morphisms has a
  monomorphic lift into a self-product, then so does a compatible pair of morphisms between the
  thickened ends, provided one of the two is unramified.

## References

* [Stacks Project, Tag 05VH](https://stacks.math.columbia.edu/tag/05VH), monicity of a morphism
  of schemes from unramifiedness together with universal injectivity.
* [Stacks Project, Tag 09ZV](https://stacks.math.columbia.edu/tag/09ZV), the topological
  properties that are unchanged across a morphism of thickenings.
* [Stacks Project, Tag 02GG](https://stacks.math.columbia.edu/tag/02GG), unramifiedness of a
  left factor.
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Thickenings

/-- In a commuting square whose vertical arrows `i` and `k` are thickenings, if the upper
horizontal arrow `j` is a monomorphism and the lower one `j'` is unramified, then `j'` is a
monomorphism. -/
theorem mono_of_isThickening_of_unramified {R R' W W' : Scheme.{u}}
    {i : R ⟶ R'} {k : W ⟶ W'} {j : R ⟶ W} {j' : R' ⟶ W'}
    (hi : IsThickening i) (hk : IsThickening k) (hsq : j ≫ k = i ≫ j')
    (hmono : Mono j) (hunr : Unramified j') : Mono j' := by
  have := hmono
  have hui : UniversallyInjective j := inferInstance
  have hui' : UniversallyInjective j' :=
    (universallyInjective_left_iff_right hi hk (Arrow.homMk (u := j) (v := j') hsq)).mp hui
  have htfae : (Unramified j' ∧ UniversallyInjective j') ↔ (Unramified j' ∧ Mono j') :=
    (universallyInjective_unramified_tfae j').out 2 1
  exact (htfae.mp ⟨hunr, hui'⟩).2

/-- For a thickening `iU : U ⟶ U'` and a morphism `g : U' ⟶ T`, the induced morphism
`U ×_T U ⟶ U' ×_T U'` is a thickening. -/
theorem isThickening_pullbackMapSelf {U U' T : Scheme.{u}} {iU : U ⟶ U'}
    (hiU : IsThickening iU) (g : U' ⟶ T) :
    IsThickening (pullback.map (iU ≫ g) (iU ≫ g) g g iU iU (𝟙 T)
      (by simp) (by simp)) := by
  have : MorphismProperty.IsStableUnderComposition
      (@IsThickening : MorphismProperty Scheme.{u}) :=
    ⟨fun _ _ hf hg => isThickening_comp hf hg⟩
  exact MorphismProperty.pullbackMap hiU hiU rfl rfl

/-- Let `iR : R ⟶ R'` and `iU : U ⟶ U'` be thickenings, let `g : U' ⟶ T` be a morphism, and let
`p, q : R ⟶ U` and `p', q' : R' ⟶ U'` be compatible with `iR` and `iU`. If the induced
`R ⟶ U ×_T U` is a monomorphism and `p'` is unramified, then `R' ⟶ U' ×_T U'` is a
monomorphism. -/
theorem mono_pullbackLift_of_isThickening
    {R R' U U' T : Scheme.{u}} {iR : R ⟶ R'} {iU : U ⟶ U'} {g : U' ⟶ T}
    (hiR : IsThickening iR) (hiU : IsThickening iU)
    {p q : R ⟶ U} {p' q' : R' ⟶ U'}
    (hp : iR ≫ p' = p ≫ iU) (hq : iR ≫ q' = q ≫ iU)
    (h : p ≫ iU ≫ g = q ≫ iU ≫ g) (h' : p' ≫ g = q' ≫ g)
    (hmono : Mono (pullback.lift p q h)) (hunr : Unramified p') :
    Mono (pullback.lift p' q' h') := by
  have hfst : pullback.lift p' q' h' ≫ pullback.fst g g = p' := pullback.lift_fst _ _ _
  have : Unramified (pullback.lift p' q' h' ≫ pullback.fst g g) := by rwa [hfst]
  refine mono_of_isThickening_of_unramified hiR (isThickening_pullbackMapSelf hiU g) ?_ hmono
    (unramified_of_comp _ (pullback.fst g g))
  refine pullback.hom_ext ?_ ?_ <;>
    simp only [pullback.map, Category.assoc, pullback.lift_fst, pullback.lift_snd, hp, hq,
      pullback.lift_fst_assoc, pullback.lift_snd_assoc]

end Stacks.Thickenings

end
