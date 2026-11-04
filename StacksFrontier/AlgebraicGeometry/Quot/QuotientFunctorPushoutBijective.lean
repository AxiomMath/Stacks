module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPushoutSurjective

/-!
# Quotients over a pushout along a thickening

Stacks 08IW: in Situation 082M, let `Y' = Y ⊔_Z Z'` be a pushout of schemes over `B` along a
thickening `Z ⟶ Z'` and an affine morphism `Z ⟶ Y` (Stacks 07RT). Then the natural map
`Q_{F/X/B}(Y') ⟶ Q_{F/X/B}(Y) ×_{Q_{F/X/B}(Z)} Q_{F/X/B}(Z')` is bijective, and if `X ⟶ B` is
locally of finite presentation, so is the natural map for `Q^{fp}_{F/X/B}`.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.quotientsPushoutMap_bijective`: Stacks 08IW for
  `Q_{F/X/B}`.
* `AlgebraicGeometry.Space.QuotientSituation.finitePresentationQuotientsPushoutMap_bijective`:
  Stacks 08IW for `Q^{fp}_{F/X/B}`.

## References

* [Stacks Project, Tag 08IW](https://stacks.math.columbia.edu/tag/08IW)
* [Stacks Project, Tag 07RT](https://stacks.math.columbia.edu/tag/07RT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

variable {Z Z' Y₀ Y' : SchemesOver D.Y} (i : Z ⟶ Z') (f : Z ⟶ Y₀) (g : Z' ⟶ Y') (h : Y₀ ⟶ Y')
  (hpo : IsPushout ((BigFppfOver.toScheme B S hS).map i.left)
    ((BigFppfOver.toScheme B S hS).map f.left) ((BigFppfOver.toScheme B S hS).map g.left)
    ((BigFppfOver.toScheme B S hS).map h.left))
  (hi : Stacks.Thickenings.IsThickening ((BigFppfOver.toScheme B S hS).map i.left))
  (hf : _root_.AlgebraicGeometry.IsAffineHom ((BigFppfOver.toScheme B S hS).map f.left))

/-- **The natural map `Q^{fp}(Y') ⟶ Q^{fp}(Y) ×_{Q^{fp}(Z)} Q^{fp}(Z')`** of Stacks 08IW: a
finitely presented quotient over the pushout goes to its two pullbacks, which agree over `Z`. -/
def finitePresentationQuotientsPushoutMap :
    D.finitePresentationQuotientsFunctor.obj (op Y') →
      Types.PullbackObj (D.finitePresentationQuotientsFunctor.map f.op)
        (D.finitePresentationQuotientsFunctor.map i.op) :=
  fun K => ⟨(D.finitePresentationQuotientsFunctor.map h.op K,
    D.finitePresentationQuotientsFunctor.map g.op K), by
    change (D.finitePresentationQuotientsFunctor.map h.op ≫
        D.finitePresentationQuotientsFunctor.map f.op) K =
      (D.finitePresentationQuotientsFunctor.map g.op ≫
        D.finitePresentationQuotientsFunctor.map i.op) K
    rw [← Functor.map_comp, ← Functor.map_comp, ← op_comp, ← op_comp,
      D.pushout_w i f g h hpo]⟩

include hpo hi hf in
/-- **Stacks 08IW**, for `Q_{F/X/B}`: for a pushout `Y' = Y ⊔_Z Z'` of schemes over `B` along a
thickening `Z ⟶ Z'` and an affine morphism `Z ⟶ Y`, the natural map
`Q_{F/X/B}(Y') ⟶ Q_{F/X/B}(Y) ×_{Q_{F/X/B}(Z)} Q_{F/X/B}(Z')` is bijective. -/
@[stacks 08IW]
theorem quotientsPushoutMap_bijective :
    Function.Bijective (D.quotientsPushoutMap i f g h hpo) :=
  ⟨D.quotientsPushoutMap_injective i f g h hpo hi hf,
    D.quotientsPushoutMap_surjective i f g h hpo hi hf⟩

include hpo hi hf in
/-- **Stacks 08IW**, for `Q^{fp}_{F/X/B}`: if moreover `X ⟶ B` is locally of finite
presentation, the natural map `Q^{fp}(Y') ⟶ Q^{fp}(Y) ×_{Q^{fp}(Z)} Q^{fp}(Z')` is
bijective. -/
@[stacks 08IW]
theorem finitePresentationQuotientsPushoutMap_bijective
    (hlfp : IsLocallyOfFinitePresentation B S hS D.f.hom) :
    Function.Bijective (D.finitePresentationQuotientsPushoutMap i f g h hpo) := by
  refine ⟨fun K₁ K₂ he => ?_, ?_⟩
  · have h₁ := congrArg (fun p => (p.1.1 : D.finitePresentationQuotients Y₀).1) he
    have h₂ := congrArg (fun p => (p.1.2 : D.finitePresentationQuotients Z').1) he
    exact Subtype.ext (le_antisymm
      (D.le_of_quotientPullback_eq i f g h hpo hi hf K₁.1 K₂.1 K₂.2.1 h₁ h₂)
      (D.le_of_quotientPullback_eq i f g h hpo hi hf K₂.1 K₁.1 K₁.2.1 h₁.symm h₂.symm))
  · rintro ⟨⟨KY, KZ⟩, hKK⟩
    obtain ⟨K, hK, h₁, h₂, hfp⟩ := D.exists_quotientPullback_eq i f g h hpo hi hf KY.1 KZ.1
      KY.2.1 KZ.2.1 (congrArg Subtype.val hKK)
    exact ⟨⟨K, hK, hfp hlfp KY.2.2 KZ.2.2⟩,
      Subtype.ext (Prod.ext (Subtype.ext h₁) (Subtype.ext h₂))⟩

end QuotientSituation

end AlgebraicGeometry.Space

end
