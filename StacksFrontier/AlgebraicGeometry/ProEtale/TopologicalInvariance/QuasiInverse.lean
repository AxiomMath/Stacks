module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance.DescentEffective
public import StacksFrontier.AlgebraicGeometry.PartTwoResidue.Complete
public import StacksFrontier.AlgebraicGeometry.ProEtale.TopologicalInvariance

/-!
# Topological invariance of the small pro-étale topos

Let `f : T ⟶ S` be an integral, universally injective and surjective morphism of schemes in a
chosen big pro-étale site. Then the direct image `f_*` and the inverse image `f⁻¹` of the induced
morphism of small pro-étale topoi are quasi-inverse equivalences: the unit `𝟭 ⟶ f_* f⁻¹` and the
counit `f⁻¹ f_* ⟶ 𝟭` of the adjunction `f⁻¹ ⊣ f_*` are both isomorphisms.

Over an affine base the source proves this by identifying both topoi with sheaves on the
category of ind-étale algebras, and the categories of ind-étale algebras over `Γ(S, 𝒪_S)` and
`Γ(T, 𝒪_T)` are equivalent because the categories of étale algebras are, by topological
invariance of the étale site; the general case reduces to an affine base. Both inputs of that
argument are available unconditionally: topological invariance of the small étale site along a
universal homeomorphism, `Stacks.Etale.etalePullback_isEquivalence`, and the description of an
integral morphism over a quasi-compact quasi-separated base as a limit of finite morphisms of
finite presentation, `Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`,
which is what the affine form of topological invariance uses.

## Main definitions

* `AlgebraicGeometry.ProEtale.smallProetaleEquivalence` — for `f` integral, universally
  injective and surjective, the equivalence of small pro-étale topoi with functor `f⁻¹` and
  inverse `f_*`.

## Main results

* `AlgebraicGeometry.ProEtale.smallProetaleMorphism_isIso_unit_and_counit` — for `f` integral,
  universally injective and surjective, the unit and the counit of `f⁻¹ ⊣ f_*` on small
  pro-étale topoi are isomorphisms.
* `AlgebraicGeometry.ProEtale.smallProetalePushforward_isEquivalence_of_isIntegralHom` and
  `AlgebraicGeometry.ProEtale.smallProetaleInverseImage_isEquivalence_of_isIntegralHom` — under
  the same three hypotheses, the direct image and the inverse image are equivalences.

Every statement here takes only `f` and the three conditions integral, universally injective and
surjective, and nothing else; the two equivalence statements take the three conditions as instance
arguments, as is usual for these classes of morphisms. The statements
`AlgebraicGeometry.ProEtale.smallProetalePushforward_isEquivalence` and
`AlgebraicGeometry.ProEtale.smallProetaleInverseImage_isEquivalence` of the parent module take in
addition, as section hypotheses, essential surjectivity of étale pullback along a universal
homeomorphism (Stacks 04DZ) and `AlgebraicGeometry.IntegralHasFinitePresentationLimit`
(Stacks 09YZ); the results here are those statements in the special case where the two
hypotheses are supplied by `Stacks.Etale.etalePullback_isEquivalence` and
`Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`, so they are
unconditional.

## Implementation notes

The quasi-inverse equivalence `AlgebraicGeometry.ProEtale.smallProetaleEquivalence` is
`CategoryTheory.Adjunction.toEquivalence` applied to the adjunction
`(smallProetaleMorphism B T S f).adj`, whose functor is the inverse image and whose inverse is the
direct image; `AlgebraicGeometry.ProEtale.smallProetaleMorphism_isIso_unit_and_counit` records the
two isomorphism conditions that make it one.

## References

* [Stacks Project, Tag 09AB](https://stacks.math.columbia.edu/tag/09AB)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
-/

@[expose] public section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProEtale

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

/-- **Topological invariance of the small pro-étale topos.** Let `f : T ⟶ S` be an integral,
universally injective and surjective morphism of schemes. Then the direct image `f_*` and the
inverse image `f⁻¹` of the induced morphism of small pro-étale topoi are quasi-inverse
equivalences: the unit and the counit of the adjunction `f⁻¹ ⊣ f_*` are isomorphisms.

The only hypotheses are `f` and the three conditions on it. The proof supplies Stacks 04DZ, by
`Stacks.Etale.etalePullback_isEquivalence`, and Stacks 09YZ, by
`Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`, to the base's
conditional `AlgebraicGeometry.ProEtale.smallProetalePushforward_isEquivalence`, so it has no
further hypotheses. -/
@[stacks 09AB "unit and counit of f^{-1} -| f_* are isomorphisms; unconditional: only f
integral, universally injective, surjective; 04DZ and 09YZ are proved and supplied, not assumed"]
theorem smallProetaleMorphism_isIso_unit_and_counit
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    IsIso (smallProetaleMorphism B T S f).adj.unit ∧
      IsIso (smallProetaleMorphism B T S f).adj.counit := by
  have : (smallProetaleMorphism B T S f).pushforward.IsEquivalence :=
    smallProetalePushforward_isEquivalence
      (fun g hg ↦ by
        obtain ⟨_, _, _⟩ :=
          (universalHomeomorphism_iff_integral_universallyInjective_surjective g).mp hg
        have := Stacks.Etale.etalePullback_isEquivalence g
        infer_instance)
      (fun _ _ g _ _ _ ↦
        Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation g)
      B T S f hIntegral hInjective hSurjective
  exact ⟨inferInstance, inferInstance⟩

/-- **Topological invariance of the small pro-étale topos, direct image, unconditionally.** Let
`f : T ⟶ S` be an integral, universally injective and surjective morphism of schemes. Then the
direct image `f_*` of the induced morphism of small pro-étale topoi is an equivalence.

The only hypotheses are `f` and the three conditions integral, universally injective and
surjective. The base's `AlgebraicGeometry.ProEtale.smallProetalePushforward_isEquivalence` is the
same statement taking in addition topological invariance of the étale site (Stacks 04DZ) and
integral morphisms as limits of finite ones (Stacks 09YZ) as section hypotheses; this theorem is
that one with both supplied, by `Stacks.Etale.etalePullback_isEquivalence` and
`Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`, so it has no
further hypotheses. -/
@[stacks 09AB "direct image f_* is an equivalence; unconditional: only f integral, universally
injective, surjective; 04DZ and 09YZ are proved and supplied, not assumed"]
theorem smallProetalePushforward_isEquivalence_of_isIntegralHom
    [IsIntegralHom (B.inclusion.map f)] [UniversallyInjective (B.inclusion.map f)]
    [Surjective (B.inclusion.map f)] :
    (smallProetaleMorphism B T S f).pushforward.IsEquivalence := by
  obtain ⟨_, _⟩ := smallProetaleMorphism_isIso_unit_and_counit B T S f
    inferInstance inferInstance inferInstance
  exact (smallProetaleMorphism B T S f).adj.toEquivalence.isEquivalence_inverse

/-- **Topological invariance of the small pro-étale topos, inverse image, unconditionally.** Let
`f : T ⟶ S` be an integral, universally injective and surjective morphism of schemes. Then the
inverse image `f⁻¹` of the induced morphism of small pro-étale topoi is an equivalence.

The only hypotheses are `f` and the three conditions integral, universally injective and
surjective. The base's `AlgebraicGeometry.ProEtale.smallProetaleInverseImage_isEquivalence` is the
same statement taking in addition Stacks 04DZ and Stacks 09YZ as section hypotheses; this theorem
is that one with both supplied, by `Stacks.Etale.etalePullback_isEquivalence` and
`Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`, so it has no
further hypotheses. -/
@[stacks 09AB "inverse image f^{-1} is an equivalence; unconditional: only f integral,
universally injective, surjective; 04DZ and 09YZ are proved and supplied, not assumed"]
theorem smallProetaleInverseImage_isEquivalence_of_isIntegralHom
    [IsIntegralHom (B.inclusion.map f)] [UniversallyInjective (B.inclusion.map f)]
    [Surjective (B.inclusion.map f)] :
    (smallProetaleMorphism B T S f).inverseImage.IsEquivalence := by
  have := smallProetalePushforward_isEquivalence_of_isIntegralHom B T S f
  exact (smallProetaleMorphism B T S f).adj.isEquivalence_left_of_isEquivalence_right

/-- **The small pro-étale topoi along an integral universal homeomorphism are equivalent.** For
`f : T ⟶ S` integral, universally injective and surjective, the equivalence between the small
pro-étale topos of `S` and that of `T` whose functor is the inverse image `f⁻¹` and whose inverse
is the direct image `f_*`, with unit and counit those of the adjunction `f⁻¹ ⊣ f_*`: these two
functors are quasi-inverse equivalences.

The only hypotheses are `f` and the three conditions on it; Stacks 04DZ and Stacks 09YZ, which
the base's conditional statements take as section hypotheses, are supplied by
`Stacks.Etale.etalePullback_isEquivalence` and
`Stacks.AlgebraicGeometry.Tag0817PartTwo.nonempty_integralLimitPresentation`. -/
@[stacks 09AB "f^{-1} and f_* as quasi-inverse equivalences of the small pro-etale topoi;
unconditional: only f integral, universally injective, surjective"]
noncomputable def smallProetaleEquivalence
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    Sheaf (SmallProetale.topology B S.obj S.property) (Type (u + 1)) ≌
      Sheaf (SmallProetale.topology B T.obj T.property) (Type (u + 1)) :=
  haveI := (smallProetaleMorphism_isIso_unit_and_counit B T S f
    hIntegral hInjective hSurjective).1
  haveI := (smallProetaleMorphism_isIso_unit_and_counit B T S f
    hIntegral hInjective hSurjective).2
  (smallProetaleMorphism B T S f).adj.toEquivalence

/-- The functor of `smallProetaleEquivalence` is the inverse image `f⁻¹`. -/
@[simp]
lemma smallProetaleEquivalence_functor
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    (smallProetaleEquivalence B T S f hIntegral hInjective hSurjective).functor =
      (smallProetaleMorphism B T S f).inverseImage :=
  rfl

/-- The inverse of `smallProetaleEquivalence` is the direct image `f_*`. -/
@[simp]
lemma smallProetaleEquivalence_inverse
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    (smallProetaleEquivalence B T S f hIntegral hInjective hSurjective).inverse =
      (smallProetaleMorphism B T S f).pushforward :=
  rfl

/-- The unit of `smallProetaleEquivalence` is the unit of the adjunction `f⁻¹ ⊣ f_*`. -/
@[simp]
lemma smallProetaleEquivalence_unit
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    (smallProetaleEquivalence B T S f hIntegral hInjective hSurjective).unit =
      (smallProetaleMorphism B T S f).adj.unit :=
  rfl

/-- The counit of `smallProetaleEquivalence` is the counit of the adjunction `f⁻¹ ⊣ f_*`. -/
@[simp]
lemma smallProetaleEquivalence_counit
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    (smallProetaleEquivalence B T S f hIntegral hInjective hSurjective).counit =
      (smallProetaleMorphism B T S f).adj.counit :=
  rfl

end AlgebraicGeometry.ProEtale

end
