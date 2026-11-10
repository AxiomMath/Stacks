module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.Descent.Germs.EtaleLocalDimension
public import StacksFrontier.AlgebraicGeometry.Descent.LocalOnSourceTopologies.Unramified
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdealsCongr
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne
public import StacksFrontier.AlgebraicGeometry.FibreDimensionBaseChange.Composite
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Differentials.FiniteType
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Pullback
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Etale
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Differentials
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties

/-!
# At-worst-nodal families and étale morphisms of the source

Let `f : X ⟶ S` be at-worst-nodal of relative dimension one and let `g : Y ⟶ X` be étale. This
file assembles the two halves of the statement that the composite `g ≫ f : Y ⟶ S` is again
at-worst-nodal of relative dimension one.

Being at-worst-nodal of relative dimension one is being syntomic of relative dimension one
together with unramifiedness over the base of the relative singular subscheme, the closed
subscheme cut out by the first Fitting ideal of the sheaf of relative differentials. The first
half is unconditional: an étale morphism is syntomic, syntomicity is stable under composition,
and an étale morphism induces an étale morphism of fibres, which preserves the local dimension
of a fibre. The second half rests on the comparison of ideal sheaves `Sing(f)` pulled back
along `g` is `Sing(g ≫ f)`, which expresses that the singular subscheme of the composite is the
preimage of that of `f`; granted the comparison, the singular subscheme of the composite maps to
that of `f` through a closed immersion followed by a base change of `g`, and both are
unramified.

## Main results

* `AlgebraicGeometry.syntomicOfRelativeDimension_one_comp_etale`: syntomicity of relative
  dimension one is preserved by precomposition with an étale morphism.
* `AlgebraicGeometry.unramified_relativeSingular_comp_etale_of_comap_le`: unramifiedness of the
  relative singular subscheme over the base is preserved by precomposition with an étale
  morphism, granted the comparison of singular ideal sheaves.
* `AlgebraicGeometry.relativeSingularIdeal_comap_etale`: the comparison itself, for a morphism
  locally of finite type — the relative singular ideal sheaf of the composite is the pullback
  of that of `f`.
* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_comp_etale`: **Stacks Project,
  Tag 0C5C** — being at-worst-nodal of relative dimension one is preserved by precomposition
  with an étale morphism.

## Implementation notes

The comparison of singular ideal sheaves is an equality, not merely an inclusion. It is the
statement that forming the first Fitting ideal of the relative differentials commutes with the
étale pullback, and it has three ingredients: the canonical map `g^* Ω_{X/S} ⟶ Ω_{Y/S}` is an
isomorphism (`AlgebraicGeometry.Scheme.Hom.isIso_relativeDifferentialsMap_of_comp`), Fitting
ideal sheaves commute with arbitrary base change (`AlgebraicGeometry.fittingIdeal_comap`), and
they are an isomorphism invariant (`AlgebraicGeometry.fittingIdeal_congr`). The second of these
needs `Ω_{X/S}` to be quasi-coherent and of finite type, which is why the comparison carries
the hypothesis that `f` be locally of finite type
(`AlgebraicGeometry.Scheme.Hom.isFiniteType_relativeDifferentials`); for a syntomic `f` that
hypothesis is automatic, so the tagged statement is unconditional. The clause-2 lemma is left in
its hypothesis-carrying form, since it needs no finiteness of `f` at all.

The morphism of fibres induced by the first factor of a composition is
`AlgebraicGeometry.fiberMapOfComp`, which is the base change of that factor along the fibre
inclusion, so it is étale whenever the factor is; the local dimension of a fibre is therefore
read off at the image point.

## References

* [Stacks Project, Tag 0C5A](https://stacks.math.columbia.edu/tag/0C5A)
* [Stacks Project, Tag 0C5C](https://stacks.math.columbia.edu/tag/0C5C)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- Precomposing a morphism which is syntomic of relative dimension one with an étale morphism
again gives a morphism which is syntomic of relative dimension one: an étale morphism is
syntomic, syntomicity is stable under composition, and the induced morphism of fibres is étale,
so the local dimension of a fibre of the composite at a point is the local dimension of the
corresponding fibre of the original morphism at the image point. -/
public theorem syntomicOfRelativeDimension_one_comp_etale {X Y S : Scheme.{u}} (f : X ⟶ S)
    (g : Y ⟶ X) [Etale g] (hf : SyntomicOfRelativeDimension 1 f) :
    SyntomicOfRelativeDimension 1 (g ≫ f) := by
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1
  have : LocallyOfFiniteType f := inferInstance
  refine ⟨MorphismProperty.comp_mem _ g f (syntomic_of_etale g) hf.1, fun y => ?_⟩
  have : Etale (fiberMapOfComp g f ((g ≫ f) y)) :=
    MorphismProperty.of_isPullback (isPullback_fiberMapOfComp g f ((g ≫ f) y)).flip inferInstance
  rw [topologicalKrullDimAt_eq_of_etale (fiberMapOfComp g f ((g ≫ f) y)) ((g ≫ f).asFiber y),
    fiberMapOfComp_asFiber g f y]
  exact hf.2 (g y)

/-- If the relative singular subscheme of `f` pulled back along an étale morphism `g` is
contained in the relative singular subscheme of the composite, then unramifiedness of the
relative singular subscheme over the base passes from `f` to the composite: the singular
subscheme of the composite sits inside the pullback of that of `f` as a closed immersion, the
pullback projects to the singular subscheme of `f` by a base change of `g`, and a closed
immersion, an isomorphism and an étale morphism are all unramified. -/
public theorem unramified_relativeSingular_comp_etale_of_comap_le {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ X) [Etale g]
    (hf : Unramified ((relativeSingularIdeal f).subschemeι ≫ f))
    (hle : (relativeSingularIdeal f).comap g ≤ relativeSingularIdeal (g ≫ f)) :
    Unramified ((relativeSingularIdeal (g ≫ f)).subschemeι ≫ (g ≫ f)) := by
  set I := relativeSingularIdeal f with hI
  set J := relativeSingularIdeal (g ≫ f) with hJ
  have hcond : pullback.fst g I.subschemeι ≫ g ≫ f
      = pullback.snd g I.subschemeι ≫ I.subschemeι ≫ f := by
    rw [← Category.assoc, ← Category.assoc, pullback.condition]
  have key : J.subschemeι ≫ (g ≫ f) =
      (Scheme.IdealSheafData.inclusion hle ≫ (I.comapIso g).hom ≫
        pullback.snd g I.subschemeι) ≫ (I.subschemeι ≫ f) := by
    rw [← Scheme.IdealSheafData.inclusion_subschemeι hle,
      ← Scheme.IdealSheafData.comapIso_hom_fst I g]
    simp only [Category.assoc]
    rw [hcond]
  rw [key]
  have h1 : Unramified (Scheme.IdealSheafData.inclusion hle) := by
    rw [unramified_iff_locallyOfFiniteType_and_isZero_relativeDifferentials]
    exact ⟨inferInstance, Scheme.Hom.isZero_relativeDifferentials_of_mono _⟩
  have h2 : Unramified ((I.comapIso g).hom) := unramified_of_etale _
  have h3 : Unramified (pullback.snd g I.subschemeι) := unramified_of_etale _
  exact MorphismProperty.comp_mem _ _ _
    (MorphismProperty.comp_mem _ _ _ h1 (MorphismProperty.comp_mem _ _ _ h2 h3)) hf

/-- **The relative singular subscheme of a composite with an étale first factor is the preimage
of the relative singular subscheme of the second factor.** For `f : X ⟶ S` locally of finite
type and `g : Y ⟶ X` étale, the canonical map `g^* Ω_{X/S} ⟶ Ω_{Y/S}` is an isomorphism, the
sheaves of relative differentials are quasi-coherent and of finite type, and Fitting ideal
sheaves both commute with base change and are an isomorphism invariant. -/
public theorem relativeSingularIdeal_comap_etale {X Y S : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ X)
    [LocallyOfFiniteType f] [Etale g] :
    (relativeSingularIdeal f).comap g = relativeSingularIdeal (g ≫ f) := by
  have : LocallyOfFiniteType (g ≫ f) :=
    MorphismProperty.comp_mem _ g f inferInstance inferInstance
  have hiso := Scheme.Hom.isIso_relativeDifferentialsMap_of_comp g f
  change (fittingIdeal (Scheme.Hom.relativeDifferentials f) 1).comap g =
    fittingIdeal (Scheme.Hom.relativeDifferentials (g ≫ f)) 1
  rw [fittingIdeal_comap g (Scheme.Hom.relativeDifferentials f) 1]
  exact fittingIdeal_congr (asIso (Scheme.Hom.relativeDifferentialsMap g f (g ≫ f) (𝟙 S)
    (Category.comp_id (g ≫ f)).symm)) 1

/-- **Stacks Project, Tag 0C5C.** Precomposing an at-worst-nodal morphism of relative
dimension one with an étale morphism again gives an at-worst-nodal morphism of relative
dimension one. -/
@[stacks 0C5C]
public theorem isAtWorstNodalOfRelativeDimensionOne_comp_etale {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ X) [Etale g] (hf : IsAtWorstNodalOfRelativeDimensionOne f) :
    IsAtWorstNodalOfRelativeDimensionOne (g ≫ f) :=
  have : LocallyOfFinitePresentation f := locallyOfFinitePresentation hf.1.1
  have : LocallyOfFiniteType f := inferInstance
  ⟨syntomicOfRelativeDimension_one_comp_etale f g hf.1,
    unramified_relativeSingular_comp_etale_of_comap_le f g hf.2
      (le_of_eq (relativeSingularIdeal_comap_etale f g))⟩

end AlgebraicGeometry

end
