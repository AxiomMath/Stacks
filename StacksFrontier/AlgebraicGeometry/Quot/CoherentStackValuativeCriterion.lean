module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackValuativeLattice
public import StacksFrontier.AlgebraicGeometry.Quot.CoherentStackValuativeTorsionFree
public import StacksFrontier.AlgebraicGeometry.Quot.ProperSupportAlongProper
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentModulesWitness

/-!
# The existence part of the valuative criterion for the stack of coherent sheaves (Stacks 0DM0)

Let `f : X ⟶ B` be a morphism of algebraic spaces over a scheme `S` of a big fppf site which is
proper and of finite presentation.  Stacks 0DM0 asserts that the projection
`Coh_{X/B} ⟶ B` satisfies the existence part of the valuative criterion (Stacks 0CLK).

## Main results

* `AlgebraicGeometry.Space.CoherentSituation.extendsOverValuationRings`: for `f` proper, every
  object of `Coh_{X/B}` over the generic point of a valuation ring extends over the valuation
  ring.
* `AlgebraicGeometry.Space.CoherentSituation.fiberedValuativeExistence_toBaseCFG`: for `f` proper
  and of finite presentation, `Coh_{X/B} ⟶ B` satisfies the existence part of the valuative
  criterion.

## Implementation notes

`Coh_{X/B}` is a category fibred in groupoids over the big fppf site of `S` whose hom-sets live one
universe above those of the site, so it is not an object of the 2-category of algebraic stacks.
The existence part of the valuative criterion is therefore stated as
`AlgebraicGeometry.Stack.FiberedValuativeExistence`, the data of Stacks 0CLK for an arbitrary
1-morphism of categories fibred in groupoids.  For a 1-morphism of algebraic stacks this is
equivalent to `AlgebraicGeometry.Stack.ValuativeCriterion.Existence`, by
`AlgebraicGeometry.Stack.valuativeCriterionExistence_iff_fiberedValuativeExistence`.

The base `B` of the source is the algebraic space `D.Y` of the standing datum, and
`Coh_{X/B} ⟶ B` is the 1-morphism `AlgebraicGeometry.Space.CoherentSituation.toBaseCFG` to the
category fibred in sets `𝒮_B` of test schemes over `B`, which is `B` read as a category fibred
in groupoids.

## References

* [Stacks Project, Tag 0DM0](https://stacks.math.columbia.edu/tag/0DM0)
* [Stacks Project, Tag 0CLK](https://stacks.math.columbia.edu/tag/0CLK)
* [Stacks Project, Tag 0829](https://stacks.math.columbia.edu/tag/0829)
* [Stacks Project, Tag 0539](https://stacks.math.columbia.edu/tag/0539)
* [Stacks Project, Tag 0DLR](https://stacks.math.columbia.edu/tag/0DLR)
* [Stacks Project, Tag 07U8](https://stacks.math.columbia.edu/tag/07U8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

attribute [local instance] pointTopology

/-- **Coherent sheaves extend over valuation rings when `f` is proper.**  For a valuation ring
`R` with fraction field `K`, the module `F_K` of an object of `Coh_{X/B}` over the generic point
of a test scheme `T = Spec R` extends to a quasi-coherent module of finite presentation on `X_T`,
flat over `T` and with support proper over `T`, whose inverse image on `X_K` is `F_K`. -/
theorem CoherentSituation.extendsOverValuationRings (D : CoherentSituation B S hS)
    (hp : IsProper B S hS D.f.hom) : D.ExtendsOverValuationRings := by
  intro R _ _ _ K _ _ _ hR hK b A T h hh
  have hAft : A.F.IsFiniteType :=
    Stacks.CoherentModulesWitness.isFiniteType_of_isFinitePresentationOnSite _ A.finitePresentation
  obtain ⟨G, hGq, hGf, hGiso⟩ := exists_lattice_modulePushforward_baseChangeMap D.f
    D.finitePresentation B.contains_terminal R K hR hK b h hh A.F A.quasicoherent hAft
  have hRK : ∀ r : R, r ≠ 0 → IsUnit (algebraMap R K r) := fun r hr =>
    isUnit_iff_ne_zero.mpr fun h0 =>
      hr (IsFractionRing.injective R K (h0.trans (map_zero _).symm))
  have := hGq
  have hGft : SheafOfModules.IsFiniteTypeOnSite
      (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2) :=
    Stacks.SheafOfModules.isFiniteTypeOnSite_of_isFiniteType _ hGf
  obtain ⟨hflat, hfp⟩ := isFlatOver_and_isFinitePresentationOnSite_of_isTorsionFreeOver
    (isoSpecOfIsHomLift R K h hh) (D.projection T)
    (G : Modules.{u, u} B S hS (D.space T).1 (D.space T).2)
    (D.isFinitePresentation_projection T).1 hGft
    (isTorsionFreeOver_subobject_modulePushforward_baseChangeMap D.f R K h hRK hh A.F
      A.quasicoherent G)
  have := hGft
  exact ⟨G, hGq, hfp, hflat, D.exists_isProperOver_support_of_isProper hp T _, _, hGiso⟩

/-- Let `f : X ⟶ B` be a morphism of algebraic spaces which is proper and of finite presentation.
Then `Coh_{X/B} ⟶ B` satisfies the existence part of the valuative criterion (Stacks 0CLK): every
2-commutative square with left edge `Spec K ⟶ Spec R`, for a valuation ring `R` with fraction field
`K`, admits a dotted arrow after an extension `K'/K` and passage to a valuation ring `R' ⊂ K'`
dominating `R` — here already with `K' = K` and `R' = R`.

The criterion is `AlgebraicGeometry.Stack.FiberedValuativeExistence`, the data of Stacks 0CLK
for a 1-morphism of categories fibred in groupoids; it agrees with
`AlgebraicGeometry.Stack.ValuativeCriterion.Existence` on 1-morphisms of algebraic stacks by
`AlgebraicGeometry.Stack.valuativeCriterionExistence_iff_fiberedValuativeExistence`. -/
@[stacks 0DM0]
theorem CoherentSituation.fiberedValuativeExistence_toBaseCFG (D : CoherentSituation B S hS)
    (hp : IsProper B S hS D.f.hom) :
    Stack.FiberedValuativeExistence.{u, u + 1, u + 1} B S hS D.toBaseCFG :=
  D.fiberedValuativeExistence_toBaseCFG_of_extendsOverValuationRings
    (D.extendsOverValuationRings hp)

end AlgebraicGeometry.Space

end
