module

public import StacksFrontier.AlgebraicGeometry.RelativeProjBridge.LocalConditions
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjPoint.EtaleChartReduction

/-!
# Étale-local conditions on the graded algebra of Situation 0849 are read on one étale covering

In Situation 0849 let `𝒜` be the quasi-coherent graded `𝒪_X`-algebra on the algebraic space `X`,
and for a scheme point `g : T ⟶ X` let `g^*𝒜` be its restriction of Stacks 084B
(`AlgebraicGeometry.Space.RelativeProjSituation.relativeProjPoints`). A condition on
quasi-coherent graded algebras on schemes is read on `𝒜` étale locally:
`AlgebraicGeometry.Space.RelativeProjSituation.HoldsAtEtalePoints` asks it of `g^*𝒜` for every
étale scheme point `g`. For a condition that is local in the étale topology — stable under
pullback along étale morphisms, descending along surjective étale morphisms, and invariant under
isomorphism — this is equivalent to asking it of `g^*𝒜` for one surjective étale scheme point
`g`, which is how the source reads properties of quasi-coherent sheaves on algebraic spaces.

The comparison uses the compatibility of the restrictions with further base change (Stacks 084B,
`AlgebraicGeometry.Space.GradedAlgebraRestriction.restrict`): for a morphism `τ : T' ⟶ T` of test
objects `(g ∘ τ)^*𝒜 ≅ τ^*(g^*𝒜)` as graded algebras.

## Main results

* `AlgebraicGeometry.Space.RelativeProjSituation.HoldsAtEtalePoints.iff_exists_surjective`: the
  general equivalence, for an étale-local condition.
* Its instances for the five conditions used in Stacks 084F, 084G and 084H:
  `…holdsAtEtalePoints_isFiniteTypeOverDegreeZero_iff`,
  `…holdsAtEtalePoints_isIntegralInDegreeZero_iff`,
  `…holdsAtEtalePoints_isFiniteType_iff`,
  `…holdsAtEtalePoints_isFinitelyGeneratedInDegreeOne_iff` and
  `…holdsAtEtalePoints_hasNilpotentPositiveQuotient_iff`.

## References

* [Stacks Project, Tag 084B](https://stacks.math.columbia.edu/tag/084B)
* [Stacks Project, Tag 084F](https://stacks.math.columbia.edu/tag/084F)
* [Stacks Project, Tag 084G](https://stacks.math.columbia.edu/tag/084G)
* [Stacks Project, Tag 084H](https://stacks.math.columbia.edu/tag/084H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf (situationAlgebra)

universe u m

namespace AlgebraicGeometry.Space.RelativeProjSituation

variable (s : RelativeProjSituation.{u, m})

/-- **The restriction to a composite scheme point is the pullback of the restriction**, as an
isomorphism of graded algebras in every degree (Stacks 084B, third assertion). -/
theorem holds_restrict_iff (p : ∀ {T : Scheme.{u}}, SheafGradedAlgebra T → Prop)
    (hiso : ∀ {T : Scheme.{u}} {A A' : SheafGradedAlgebra T}
      (ψ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A) (situationAlgebra A')),
      (∀ n, IsIso (ψ.app n)) → (p A ↔ p A'))
    {T T' : BigFppfOver s.site s.base s.containsBase} (τ : T' ⟶ T)
    (g : yoneda.obj T ⟶ s.space.1) :
    p (s.relativeProjPoints.algebra T' (yoneda.map τ ≫ g)) ↔
      p ((s.relativeProjPoints.algebra T g).pullback
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ)) := by
  rw [relativeProjPoints_algebra, relativeProjPoints_algebra]
  let ρ : SheafOfModules.GradedAlgebra.UnitalHom
      (situationAlgebra (s.shrink.pointAlgebra T' (yoneda.map τ ≫ g)))
      (situationAlgebra ((s.shrink.pointAlgebra T g).pullback
        ((BigFppfOver.toScheme s.site s.base s.containsBase).map τ))) :=
    s.quadrupleRestriction.restrict τ g (yoneda.map τ ≫ g) rfl
  have hρ : ∀ n, IsIso (ρ.app n) :=
    s.quadrupleRestriction.isIso_restrict_app τ g (yoneda.map τ ≫ g) rfl
  exact hiso ρ hρ

/-- **An étale-local condition on `𝒜` is read on one surjective étale scheme point.** If a
condition on quasi-coherent graded algebras on schemes is stable under pullback along étale
morphisms, descends along surjective étale morphisms and is invariant under isomorphism, then it
holds for the restriction `g^*𝒜` at every étale scheme point `g` of `X` exactly when it holds for
`g^*𝒜` at one surjective étale scheme point. -/
theorem HoldsAtEtalePoints.iff_exists_surjective
    (p : ∀ {T : Scheme.{u}}, SheafGradedAlgebra T → Prop)
    (hstab : ∀ {T T' : Scheme.{u}} (A : SheafGradedAlgebra T) (f : T' ⟶ T), Etale f →
      p A → p (A.pullback f))
    (hdesc : ∀ {T T' : Scheme.{u}} (A : SheafGradedAlgebra T) (f : T' ⟶ T), Etale f →
      Function.Surjective f.base → p (A.pullback f) → p A)
    (hiso : ∀ {T : Scheme.{u}} {A A' : SheafGradedAlgebra T}
      (ψ : SheafOfModules.GradedAlgebra.UnitalHom (situationAlgebra A) (situationAlgebra A')),
      (∀ n, IsIso (ψ.app n)) → (p A ↔ p A')) :
    s.HoldsAtEtalePoints p ↔
      ∃ (T : BigFppfOver s.site s.base s.containsBase) (g : yoneda.obj T ⟶ s.space.1),
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf g ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
          MorphismProperty Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf
            g ∧
        p (s.relativeProjPoints.algebra T g) := by
  refine ⟨fun h => ?_, fun ⟨T₀, g₀, hg₀Et, hg₀Surj, hp⟩ T g hgEt => ?_⟩
  · obtain ⟨T, g, hgEt, hgSurj⟩ := s.relativeProjPoints.exists_etalePoint s.space.2
    exact ⟨T, g, hgEt, hgSurj, h T g hgEt⟩
  let hrep := hg₀Et.rep
  let W := hrep.pullback g
  let mT : W ⟶ T := hrep.snd g
  let mT₀ : W ⟶ T₀ := yoneda.preimage (hrep.fst g)
  have hmT₀ : yoneda.map mT₀ = hrep.fst g := Functor.map_preimage _ _
  have hpb := hrep.isPullback g
  rw [← hmT₀] at hpb
  have h₀ : p (s.relativeProjPoints.algebra W (yoneda.map mT₀ ≫ g₀)) :=
    (s.holds_restrict_iff p hiso mT₀ g₀).2
      (hstab _ _ (hgEt.property g₀ (yoneda.map mT) mT₀ hpb.flip) hp)
  rw [hpb.w] at h₀
  exact hdesc _ _ (hg₀Et.property_snd g) (hg₀Surj.property g _ mT hpb).surj
    ((s.holds_restrict_iff p hiso mT g).1 h₀)

/-- **An étale-local condition on the graded rings of sections is read on one surjective étale
scheme point.** -/
theorem holdsAtEtalePoints_onAffines_iff (c : SectionCondition.{u}) :
    s.HoldsAtEtalePoints c.OnAffines ↔
      ∃ (T : BigFppfOver s.site s.base s.containsBase) (g : yoneda.obj T ⟶ s.space.1),
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf g ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
          MorphismProperty Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf
            g ∧
        c.OnAffines (s.relativeProjPoints.algebra T g) :=
  HoldsAtEtalePoints.iff_exists_surjective s c.OnAffines
    (fun A f _ h => c.onAffines_pullback A f h)
    (fun A f hf hs h => have := hf; c.onAffines_of_pullback A f hs h)
    (fun ψ hψ => have := hψ; c.onAffines_iff_of_unitalHom ψ)

/-- **`𝒜` of finite type over `𝒜₀`, read on one surjective étale scheme point.** -/
theorem holdsAtEtalePoints_isFiniteTypeOverDegreeZero_iff :
    s.HoldsAtEtalePoints SheafGradedAlgebra.IsFiniteTypeOverDegreeZero ↔
      ∃ (T : BigFppfOver s.site s.base s.containsBase) (g : yoneda.obj T ⟶ s.space.1),
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf g ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
          MorphismProperty Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf
            g ∧
        (s.relativeProjPoints.algebra T g).IsFiniteTypeOverDegreeZero :=
  s.holdsAtEtalePoints_onAffines_iff finiteTypeOverDegreeZeroCondition

/-- **`𝒪_X ⟶ 𝒜₀` integral, read on one surjective étale scheme point.** -/
theorem holdsAtEtalePoints_isIntegralInDegreeZero_iff :
    s.HoldsAtEtalePoints SheafGradedAlgebra.IsIntegralInDegreeZero ↔
      ∃ (T : BigFppfOver s.site s.base s.containsBase) (g : yoneda.obj T ⟶ s.space.1),
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf g ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
          MorphismProperty Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf
            g ∧
        (s.relativeProjPoints.algebra T g).IsIntegralInDegreeZero :=
  s.holdsAtEtalePoints_onAffines_iff integralInDegreeZeroCondition

/-- **`𝒜` generated over `𝒜₀` by a finite type `𝒜₁`, read on one surjective étale scheme
point.** -/
theorem holdsAtEtalePoints_isFinitelyGeneratedInDegreeOne_iff :
    s.HoldsAtEtalePoints SheafGradedAlgebra.IsFinitelyGeneratedInDegreeOne ↔
      ∃ (T : BigFppfOver s.site s.base s.containsBase) (g : yoneda.obj T ⟶ s.space.1),
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf g ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
          MorphismProperty Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf
            g ∧
        (s.relativeProjPoints.algebra T g).IsFinitelyGeneratedInDegreeOne :=
  s.holdsAtEtalePoints_onAffines_iff finitelyGeneratedInDegreeOneCondition

/-- **`𝒜₊` locally nilpotent modulo a finite type part, read on one surjective étale scheme
point.** -/
theorem holdsAtEtalePoints_hasNilpotentPositiveQuotient_iff :
    s.HoldsAtEtalePoints SheafGradedAlgebra.HasNilpotentPositiveQuotient ↔
      ∃ (T : BigFppfOver s.site s.base s.containsBase) (g : yoneda.obj T ⟶ s.space.1),
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf g ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
          MorphismProperty Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf
            g ∧
        (s.relativeProjPoints.algebra T g).HasNilpotentPositiveQuotient :=
  s.holdsAtEtalePoints_onAffines_iff nilpotentPositiveQuotientCondition

/-- **`𝒜` of finite type over `𝒪_X`, read on one surjective étale scheme point.** -/
theorem holdsAtEtalePoints_isFiniteType_iff :
    s.HoldsAtEtalePoints Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType ↔
      ∃ (T : BigFppfOver s.site s.base s.containsBase) (g : yoneda.obj T ⟶ s.space.1),
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Etale.{u} : MorphismProperty
          Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf g ∧
        (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
          MorphismProperty Scheme.{u}) (BigFppfOver.toScheme s.site s.base s.containsBase)).presheaf
            g ∧
        Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType
          (s.relativeProjPoints.algebra T g) :=
  by
  have e : (fun {T : Scheme.{u}} (A : SheafGradedAlgebra T) =>
      Stacks.AlgebraicGeometry.RelativeProjFiniteType.IsFiniteType A) =
        fun {T : Scheme.{u}} (A : SheafGradedAlgebra T) => finiteTypeCondition.OnAffines A := by
    funext T A
    exact propext (SheafGradedAlgebra.isFiniteType_iff_onAffines A)
  rw [e]
  simp only [SheafGradedAlgebra.isFiniteType_iff_onAffines]
  exact s.holdsAtEtalePoints_onAffines_iff finiteTypeCondition

end AlgebraicGeometry.Space.RelativeProjSituation

end
