module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.FiniteType
public import StacksFrontier.AlgebraicGeometry.FormalSpace.LocalProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.LargeValuedEtaleSiteMorphism

/-!
# Representable étale morphisms are locally of finite type

Let `S` be a scheme contained in a big fppf site `B`. A morphism of fppf sheaves over `S` which
is representable by algebraic spaces inherits the theory of morphisms of algebraic spaces; in
particular a representable étale morphism is locally of finite type in the sense of Stacks 0AM4.

## Main results

* `AlgebraicGeometry.Space.isLocallyOfFiniteTypeULift_of_isEtaleULift_of_uliftYoneda`: an étale
  morphism of presheaves whose target is a universe-lifted Yoneda presheaf is locally of finite
  type.
* `AlgebraicGeometry.FormalSpace.IsLocallyOfFiniteType.of_isRepresentableEtale`:
  **Stacks 0AJG** in the instance the rig-surjectivity theory of this library needs: a morphism
  of fppf sheaves which is representable by algebraic spaces and étale is locally of finite
  type.

## Implementation notes

The test of Stacks 0AM4 and the test of representable étaleness are both evaluated on the
projection `X ×_Y U ⟶ U` of a represented base change, whose target is a universe-lifted Yoneda
presheaf, so the whole statement reduces to the implication between the two conditions of
Stacks 03XF and Stacks 03FR for a morphism with representable target.

For such a morphism the chart condition of Stacks 03MJ is read off on the site: a chart `b` of
the target is the universe-lifted Yoneda image of a morphism `β` of the site by full
faithfulness, the composite of a chart `a` of the source with the morphism is étale after every
represented base change, and the commuting square identifies that composite with the image of
`h ≫ β`. Étaleness after every represented base change of the image of a morphism of the site
is étaleness of the underlying morphism of schemes, so étale-cancellation of Stacks 02GW leaves
`h` étale on schemes, hence locally of finite type.

## References

* [Stacks Project, Tag 02GW](https://stacks.math.columbia.edu/tag/02GW)
* [Stacks Project, Tag 0AJG](https://stacks.math.columbia.edu/tag/0AJG)
* [Stacks Project, Tag 0AM4](https://stacks.math.columbia.edu/tag/0AM4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A morphism of presheaves on the big fppf site of `S` which is étale in the sense of
**Stacks 03FR** and whose target is a universe-lifted Yoneda presheaf is locally of finite type
in the sense of **Stacks 03XF**: in a commuting square of étale charts over a morphism `h` of
the site, the chart of the target and the composite of the chart of the source with the morphism
are both étale on schemes, so `h` is étale and a fortiori locally of finite type. -/
theorem isLocallyOfFiniteTypeULift_of_isEtaleULift_of_uliftYoneda
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max w u)} {T : BigFppfOver B S hS}
    (g : F ⟶ (uliftYoneda.{w}).obj T) (hg : IsEtaleULift.{w} B S hS g) :
    IsLocallyOfFiniteTypeULift.{w} B S hS g := by
  intro U V a b h ha hb hsq
  obtain ⟨β, rfl⟩ : ∃ β : V ⟶ T, (uliftYoneda.{w}).map β = b :=
    ⟨(uliftYoneda.{w}).preimage b, by simp⟩
  have hβ : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map β) :=
    (relative_etale_uliftYoneda_map_iff B S hS β).mp hb
  have key : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).relative (uliftYoneda.{w})
        ((uliftYoneda.{w}).map (h ≫ β)) := by
    rw [Functor.map_comp, hsq]
    exact hg U a ha
  have hcomp : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (h ≫ β)) :=
    (relative_etale_uliftYoneda_map_iff B S hS (h ≫ β)).mp key
  rw [Functor.map_comp] at hcomp
  have : AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map h) :=
    MorphismProperty.of_postcomp (@AlgebraicGeometry.Etale.{u}) _ _ hβ hcomp
  infer_instance

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.FormalSpace

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 0AJG.** A morphism of fppf sheaves on the big fppf site of `S` which is
representable by algebraic spaces and étale is locally of finite type in the sense of
Stacks 0AM4. This is the instance of the theory of morphisms representable by algebraic spaces
that the rig-surjectivity theory of Stacks 0AQS and Stacks 0AQV asks for: étaleness of the
morphism of algebraic spaces cut out by a represented base change already makes it locally of
finite type. -/
@[stacks 0AJG "the theory of morphisms of algebraic spaces available to a morphism representable \
by algebraic spaces, in the instance this library uses it: a representable etale morphism is \
locally of finite type in the sense of Definition 0AM4"]
theorem IsLocallyOfFiniteType.of_isRepresentableEtale {X Y : FppfSheaf B S hS} (f : X ⟶ Y)
    (hf : IsRepresentableEtale B S hS f) :
    IsLocallyOfFiniteType B S hS f := by
  obtain ⟨hrep, hetale⟩ := hf
  refine ⟨hrep, fun U ξ => ?_⟩
  change Space.IsLocallyOfFiniteTypeULift.{u + 1} B S hS (pullback.fst ξ f.hom)
  exact Space.isLocallyOfFiniteTypeULift_of_isEtaleULift_of_uliftYoneda B S hS
    (pullback.fst ξ f.hom) (hetale U ξ)

end AlgebraicGeometry.FormalSpace

end
