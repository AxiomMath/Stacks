module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.RegularImmersion
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.LocalCompleteIntersection.SmoothComp
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartBridge
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.LocalCompleteIntersection
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.RegularImmersion

/-!
# A Koszul-regular immersion of algebraic spaces is a local complete intersection morphism

A Koszul-regular immersion of algebraic spaces over a scheme `S`, in the sense of Stacks 06BN
part (1), is a local complete intersection morphism in the sense of Stacks 06C4 part (1): this is
**Stacks 0CHK**.

## Main results

* `AlgebraicGeometry.Space.isLocalCompleteIntersection_of_isKoszulRegularImmersion` — a
  Koszul-regular immersion of algebraic spaces is a local complete intersection morphism.

## Implementation notes

The two conditions quantify over different data, and reconciling them is the whole content of
the proof. Koszul-regularity, `AlgebraicGeometry.Space.IsKoszulRegularImmersion`, is a condition
on the canonical represented base change of `i` over each étale scheme chart `b` of the *target*:
it says that `hrep.snd b` is a Koszul-regular immersion of schemes. The Koszul property,
`AlgebraicGeometry.Space.IsLocalCompleteIntersection`, is
`AlgebraicGeometry.Space.HoldsOnEveryEtaleChart` of Stacks 03MJ, a condition on every commuting
*square* of étale charts: for charts `a` of the source and `b` of the target over a morphism `h`
of the site, the scheme morphism underlying `h` must be Koszul.

Given such a square, the universal property of the base change factors `h` as
`l ≫ hrep.snd b`, and `l` is étale by the cancellation step
`AlgebraicGeometry.Space.etale_of_comp_etale_chart` of Stacks 03MJ. So the scheme morphism to be
handled is an étale morphism followed by a Koszul-regular immersion of schemes. Stacks 069L
(`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_of_isKoszulRegularImmersion`) makes the
second factor Koszul, and the smooth case of Stacks 069J
(`AlgebraicGeometry.isLocalCompleteIntersectionMorphism_comp_of_smooth`) absorbs the first,
étale being smooth. Note that the étale factor is genuinely there and genuinely needs absorbing:
a chart of the source need not be a base change of a chart of the target, and `h` itself is not
an immersion of schemes in general — already for `i` the identity of a scheme, `h` can be any
étale morphism between two charts.

The source argues instead from the one-surjective-chart form of Stacks 06C4, which is equivalent
to the every-chart form by Stacks 03MJ because the Koszul property of scheme morphisms is étale
local on source and target. That equivalence is not available here, so the every-chart form is
discharged directly, which is what the above does.

## References

* [Stacks Project, Tag 0CHK](https://stacks.math.columbia.edu/tag/0CHK)
* [Stacks Project, Tag 06BN](https://stacks.math.columbia.edu/tag/06BN)
* [Stacks Project, Tag 06C4](https://stacks.math.columbia.edu/tag/06C4)
* [Stacks Project, Tag 069L](https://stacks.math.columbia.edu/tag/069L)
* [Stacks Project, Tag 03MJ](https://stacks.math.columbia.edu/tag/03MJ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 0CHK.** A Koszul-regular immersion of algebraic spaces over `S` is a local complete
intersection morphism. -/
@[stacks 0CHK]
theorem isLocalCompleteIntersection_of_isKoszulRegularImmersion (i : X ⟶ Y)
    (hi : IsKoszulRegularImmersion B S hS i) :
    IsLocalCompleteIntersection B S hS i := by
  obtain ⟨hrep, hkoszul⟩ := hi
  intro U V a b h ha hb hcomm
  have hchart : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (hrep.fst b) :=
    presheaf_of_isPullback B S hS (hrep.isPullback b).flip hb
  have hsquare : a ≫ i = yoneda.map h ≫ b := hcomm.symm
  have hfst := hrep.lift_fst (g := b) a h hsquare
  have hsnd := hrep.lift_snd (g := b) a h hsquare
  have hlift : Etale ((BigFppfOver.toScheme B S hS).map (hrep.lift (g := b) a h hsquare)) :=
    etale_of_comp_etale_chart B S hS ha hchart hfst
  obtain ⟨himmersion, hregular⟩ := hkoszul V b hb
  let _ : _root_.AlgebraicGeometry.IsImmersion
    ((BigFppfOver.toScheme B S hS).map (hrep.snd b)) := himmersion
  rw [← hsnd, Functor.map_comp]
  exact isLocalCompleteIntersectionMorphism_comp_of_smooth _ _
    (isLocalCompleteIntersectionMorphism_of_isKoszulRegularImmersion _ hregular)

end AlgebraicGeometry.Space

end
