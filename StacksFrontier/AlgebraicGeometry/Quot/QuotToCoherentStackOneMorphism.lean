module

public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackLimitPreserving
public import StacksFrontier.AlgebraicGeometry.Quot.QuotToCoherentStackMorphism

/-!
# The 1-morphism `Quot_{F/X/B} ⟶ Coh_{X/B}`

Let `f : X ⟶ B` be a morphism of algebraic spaces of finite presentation and `F` a
quasi-coherent `𝒪_X`-module, the standing data of Stacks 09TR.  The proof of Stacks 09TU views
the Quot functor as a stack in groupoids and uses the morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` of
Stacks 0DP6, sending a quotient `F_T ⟶ 𝒬` to the object `𝒬` of `Coh_{X/B}` over `T`.  This file
assembles that morphism as a 1-morphism of categories fibred in groupoids over the big fppf site
of `S`, out of the category of elements of the Quot presheaf
(`AlgebraicGeometry.Space.QuotSituation.quotCatFiberedInGroupoids`).

## Main definitions

* `AlgebraicGeometry.Space.QuotSituation.quotToCoherentCFGFunctor`: the functor underlying the
  1-morphism.
* `AlgebraicGeometry.Space.QuotSituation.quotToCoherentCFG`: the 1-morphism
  `Quot_{F/X/B} ⟶ Coh_{X/B}`.

## Main results

* `AlgebraicGeometry.Space.QuotSituation.cohHomOfData_id`: the unit law of the action on
  morphisms: the morphism attached to an identity of test schemes is the identity of
  `Coh_{X/B}`.

## Implementation notes

The unit law compares the comparison of `AlgebraicGeometry.Space.QuotSituation.quotientFibreIso`
at the identity, which `AlgebraicGeometry.Space.QuotSituation.quotientFibreIso_inv_id` writes at
the test scheme `T` and the module `F_T/K`, with the comparison of the identity of `Coh_{X/B}`,
which is written at the test scheme and the module of the object.  The two are identified for an
arbitrary object with that test scheme and that module, by destructuring the object, so that no
comparison of inverse images is unfolded.

## References

* [Stacks Project, Tag 0DP6](https://stacks.math.columbia.edu/tag/0DP6)
* [Stacks Project, Tag 09TU](https://stacks.math.columbia.edu/tag/09TU)
* [Stacks Project, Tag 08KB](https://stacks.math.columbia.edu/tag/08KB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local implicit_reducible] QuotSituation.toCoherentSituation

namespace QuotSituation

variable (D : QuotSituation B S hS)

/-- **The unit law for the action of `Quot_{F/X/B} ⟶ Coh_{X/B}` on morphisms.**  The morphism of
`Coh_{X/B}` attached to an identity of test schemes, together with any identification of the
kernel pulled back along it, is the identity of the object attached to the kernel. -/
theorem cohHomOfData_id (hc : ModulePushforwardCoherence B S hS) {T : SchemesOver D.Y}
    (h : T ⟶ T) (hh : h = 𝟙 T) {K : Subobject (D.baseChangeModule T)}
    (hK : D.quotientPullback h K = K) (hmem : K ∈ D.properlySupportedQuotients T) :
    D.cohHomOfData h hK hmem hmem = CoherentHom.id hc (D.cohObject T K hmem) := by
  subst hh
  have key : ∀ (T₁ T₂ : SchemesOver D.toCoherentSituation.Y) (e : T₁ = T₂)
      (F₁ : Modules.{u, u} B S hS (D.toCoherentSituation.space T₁).1
        (D.toCoherentSituation.space T₁).2)
      (F₂ : Modules.{u, u} B S hS (D.toCoherentSituation.space T₂).1
        (D.toCoherentSituation.space T₂).2), HEq F₁ F₂ →
      HEq ((D.toCoherentSituation.idComparison hc T₁).hom.app F₁)
        ((D.toCoherentSituation.idComparison hc T₂).hom.app F₂) := by
    rintro T₁ T₂ rfl F₁ F₂ hF
    obtain rfl := eq_of_heq hF
    exact HEq.rfl
  refine coherentHom_eq_of_heq rfl ?_
  rw [D.cohHomOfData_fibre, D.quotientFibreIso_inv_id hc K hK]
  refine HEq.trans ?_ (heq_of_eq (CoherentHom.id_fibre hc (D.cohObject T K hmem)).symm)
  exact key T (D.cohObject T K hmem).T rfl (D.quotientModule T K) (D.cohObject T K hmem).F HEq.rfl

/-- The functor underlying the 1-morphism `Quot_{F/X/B} ⟶ Coh_{X/B}`: a section of the Quot
presheaf goes to the object of `Coh_{X/B}` it names
(`AlgebraicGeometry.Space.QuotSituation.cohObjectOfFamily`), and a morphism of the category of
elements to the morphism of `Coh_{X/B}` attached to its underlying morphism of test schemes
(`AlgebraicGeometry.Space.QuotSituation.cohHomOfData`). -/
def quotToCoherentCFGFunctor :
    letI : Category.{u + 1} (CoherentObject D.toCoherentSituation) :=
      D.toCoherentSituation.categoryData.category
    D.quotCatFiberedInGroupoids.val.obj ⥤ CoherentObject D.toCoherentSituation :=
  let : Category.{u + 1} (CoherentObject D.toCoherentSituation) :=
    D.toCoherentSituation.categoryData.category
  { obj := fun X => D.cohObjectOfFamily X.fiber.as
    map := fun {X Y} g => D.cohHomOfData
      (D.familyBaseMap g.base Y.fiber.as (Discrete.eq_of_hom g.fiber))
      (D.quotientPullback_familyBaseMap g.base Y.fiber.as (Discrete.eq_of_hom g.fiber))
      Y.fiber.as.mem X.fiber.as.mem
    map_id := fun X => D.cohHomOfData_id (modulePushforwardCoherence B S hS) _
      (CostructuredArrow.hom_ext _ _ rfl) _ X.fiber.as.mem
    map_comp := fun {X Y Z} g₁ g₂ => D.cohHomOfData_comp (modulePushforwardCoherence B S hS)
      (D.familyBaseMap g₁.base Y.fiber.as (Discrete.eq_of_hom g₁.fiber))
      (D.familyBaseMap g₂.base Z.fiber.as (Discrete.eq_of_hom g₂.fiber)) _
      (CostructuredArrow.hom_ext _ _ rfl) _ _ _ Z.fiber.as.mem Y.fiber.as.mem X.fiber.as.mem }

/-- **The 1-morphism `Quot_{F/X/B} ⟶ Coh_{X/B}` of Stacks 0DP6**, out of the category of elements
of the Quot presheaf, as a 1-morphism of categories fibred in groupoids over the big fppf site
of `S`.  It lies over the identity of the site: both projections read off the scheme a section
or an object lies over. -/
def quotToCoherentCFG : D.quotCatFiberedInGroupoids ⟶ D.toCoherentSituation.coherentCFG :=
  Bicategory.InducedBicategory.mkHom
    { toFunctor := D.quotToCoherentCFGFunctor
      w := rfl }

end QuotSituation

end AlgebraicGeometry.Space

end
