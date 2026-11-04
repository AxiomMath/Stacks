module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorPushout
public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsComp

/-!
# The quotient over a pushout glued from two compatible quotients

In the situation of Stacks 08IW, two quotients `F_Y ⟶ A` and `F_{Z'} ⟶ B'` with the same pullback
to `Z` give an isomorphism `θ : c^*A ≅ d^*B'` compatible with the two projections from `F_Z`.

## Main results

* `AlgebraicGeometry.Space.QuotientSituation.pushoutGlue_compat`: the identification of the two
  restrictions to `X_Z` is compatible with the two projections from `F_Z`.

## References

* [Stacks Project, Tag 08IW](https://stacks.math.columbia.edu/tag/08IW)
* [Stacks Project, Tag 08KV](https://stacks.math.columbia.edu/tag/08KV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Space

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The projection onto the quotient by a subobject, transported along an equality of
subobjects. -/
theorem cokernel_π_comp_eqToHom_quotient {C : Type*} [Category* C] [Abelian C] {X : C}
    {K₁ K₂ : Subobject X} (h : K₁ = K₂) :
    cokernel.π K₂.arrow ≫ eqToHom (congrArg (fun K : Subobject X => cokernel K.arrow) h.symm) =
      cokernel.π K₁.arrow := by
  subst h
  simp

namespace QuotientSituation

variable (D : QuotientSituation B S hS)

/-- The inverse of the comparison of base changes depends only on the morphism of test schemes,
read through any identification of the morphism of base changes. -/
theorem baseChangeComparison_inv_app_congr {T'' T : SchemesOver D.Y} {k₁ k₂ : T'' ⟶ T}
    (w : k₁ = k₂) {m : D.space T'' ⟶ D.space T} (p₁ : m = D.relativeMap k₁)
    (p₂ : m = D.relativeMap k₂) :
    (eqToHom (congrArg (modulePullback B S hS) p₁)).app
        ((modulePullback B S hS (D.sourceProjection T)).obj D.F) ≫
      (D.baseChangeComparison k₁).inv.app D.F =
    (eqToHom (congrArg (modulePullback B S hS) p₂)).app
        ((modulePullback B S hS (D.sourceProjection T)).obj D.F) ≫
      (D.baseChangeComparison k₂).inv.app D.F := by
  subst w
  have hp : p₁ = p₂ := rfl
  subst hp
  rfl

/-- The projection onto the quotient by a submodule, transported along an equality of
submodules. -/
theorem quotientProjection_comp_eqToHom {T : SchemesOver D.Y}
    {K₁ K₂ : Subobject (D.baseChangeModule T)} (hK : K₁ = K₂)
    (p : D.quotientModule T K₂ = D.quotientModule T K₁) :
    D.quotientProjection T K₂ ≫ eqToHom p = D.quotientProjection T K₁ := by
  subst hK
  rw [eqToHom_refl, Category.comp_id]

section Pushout

variable {Z Z' Y₀ Y' : SchemesOver D.Y} (i : Z ⟶ Z') (f : Z ⟶ Y₀) (g : Z' ⟶ Y') (h : Y₀ ⟶ Y')
  (KY : Subobject (D.baseChangeModule Y₀)) (KZ : Subobject (D.baseChangeModule Z'))
  (heq : D.quotientPullback f KY = D.quotientPullback i KZ)

include heq in
/-- The identification `θ : d^*B' ⟶ c^*A` of the restrictions to `X_Z` of two quotients `A` of
`F_Y` and `B'` of `F_{Z'}` with the same pullback to `Z` is compatible with the two projections
from `F_Z`. -/
theorem pushoutGlue_compat
    (q : D.quotientModule Z (D.quotientPullback i KZ) =
      D.quotientModule Z (D.quotientPullback f KY)) :
    D.quotientPullbackProjection i KZ ≫ ((D.quotientPullbackCokernelIso i KZ).inv ≫
      eqToHom q ≫ (D.quotientPullbackCokernelIso f KY).hom) =
      D.quotientPullbackProjection f KY := by
  rw [← D.quotientProjection_comp_quotientPullbackCokernelIso_hom i KZ,
    Category.assoc, Iso.hom_inv_id_assoc, ← Category.assoc, D.quotientProjection_comp_eqToHom heq,
    D.quotientProjection_comp_quotientPullbackCokernelIso_hom f KY]

end Pushout

end QuotientSituation

end AlgebraicGeometry.Space

end
