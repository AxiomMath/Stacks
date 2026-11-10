module

public import StacksFrontier.AlgebraicGeometry.Duality.QuasiCoherentAdjoint.HomologyCoproducts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeQuasicoherentSubobjects
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDirectSums
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
import StacksCore.Tactic.StacksAttribute

/-!
# Direct sums in the quasi-coherent derived category of an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  The derived
category `D_QCoh(𝒪_F)` of `𝒪_F`-modules with quasi-coherent cohomology has direct sums.  That is
Stacks 08F3, proved here at the module universe `u` of the structure rings.  At a free module
universe the same argument runs, but on an explicit hypothesis: the direct-sum clause of
Stacks 03M1.

## Main results

* `AlgebraicGeometry.Space.derivedCategoryB_isQuasicoherentOnSite_isClosedUnderIsomorphisms`:
  having quasi-coherent cohomology is closed under isomorphism in `D(𝒪_F)`.
* `AlgebraicGeometry.Space.isClosedUnderCoproducts_quasicoherentDerivedCategory`: having
  quasi-coherent cohomology is closed under direct sums.
* `AlgebraicGeometry.Space.hasCoproducts_quasicoherentDerivedCategory`: `D_QCoh(𝒪_F)` has direct
  sums at a free module universe, granted that a direct sum of quasi-coherent `𝒪_F`-modules is
  quasi-coherent.
* `AlgebraicGeometry.Space.hasCoproducts_quasicoherentDerivedCategory_ringUniverse`: **Stacks
  08F3** itself — `D_QCoh(𝒪_F)` has direct sums — at the module universe `u` of the structure
  rings, where that closure property is a theorem rather than a hypothesis.

## Implementation notes

`D_QCoh(𝒪_F)` is `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` of Stacks 071X, the
full subcategory of `D(𝒪_F)` cut out by `DerivedCategoryB.derivedCategoryB` for
quasi-coherence; direct sums are categorical coproducts.

The source's proof is exactly the argument of
`Stacks.Duality.isoCoproductHomologyDerived`: direct sums in `D(𝒪_F)` are computed by termwise
direct sums of complexes, because the localization `Q : C(𝒪_F) ⥤ D(𝒪_F)` preserves them, and
cohomology commutes with direct sums because the direct-sum functor is exact.  That is the whole
analytic content, and it is not restated here; the hypothesis it needs is that the
`𝒪_F`-modules at the chosen universe form a Grothendieck abelian category, which is where the
exactness of direct sums (Grothendieck's axiom AB4) comes from.

What the source supplies on top of it is that a direct sum of quasi-coherent modules is
quasi-coherent, the direct-sum clause of Stacks 03M1.  At the module universe `u` of the
structure rings that clause is a theorem,
`AlgebraicGeometry.Space.isQuasicoherentOnSite_sigma_of_h03DX` applied to Descent, Proposition
03DX(2) in its equivalence form, which is unconditional there as
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`; that is how the
tagged statement discharges it.  At a free module universe the `←` direction of 03DX(2) is not
available, so there the clause stays a hypothesis.  The other closure property the argument
uses, stability of quasi-coherence under isomorphism, is not a hypothesis at either universe:
it is an instance of `StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels`, and is
transported to `D(𝒪_F)` here.

The module universe of the general statement is free, as in
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory`.  The two sheafification hypotheses are
the ones under which the `𝒪_F`-modules at that universe are abelian; the Grothendieck hypothesis
holds in every module universe at least `u + 1`, by
`SheafOfModules.isGrothendieckAbelian_of_univLE` together with
`AlgebraicGeometry.Space.hasSheafify_smallEtaleRingedSite_addCommGrpCat`.  At the module
universe `u` of the tagged statement all three are discharged: the sheafification hypotheses are
the instances of `StacksFrontier.AlgebraicGeometry.Spaces.ModulesAbelian`, and the Grothendieck
hypothesis is `SheafOfModules.isGrothendieckAbelian_of_essentiallySmall` applied to the small
étale site, which is essentially small at `u`.

## References

* [Stacks Project, Tag 08F3](https://stacks.math.columbia.edu/tag/08F3)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 07D9](https://stacks.math.columbia.edu/tag/07D9)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] Stacks.SmallDerivedCategory.hasColimitsOfShape_discrete_derivedCategory

universe u m

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- Having quasi-coherent cohomology in every degree is closed under isomorphism in `D(𝒪_F)`:
quasi-coherence itself is, and an isomorphism of derived objects induces isomorphisms of the
cohomology sheaves. -/
instance derivedCategoryB_isQuasicoherentOnSite_isClosedUnderIsomorphisms :
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)))).IsClosedUnderIsomorphisms where
  of_iso e h n :=
    SheafOfModules.IsQuasicoherentOnSite.of_iso
      ((DerivedCategory.homologyFunctor (Modules.{u, m} B S hS F hF) n).mapIso e) (h n)

variable [IsGrothendieckAbelian.{m} (Modules.{u, m} B S hS F hF)]

/-- Coproducts of `𝒪_F`-modules, from the Grothendieck hypothesis; supplied directly because
instance search for them times out. -/
local instance hasColimitsOfShape_discrete_modules (I : Type m) :
    HasColimitsOfShape (Discrete I) (Modules.{u, m} B S hS F hF) :=
  (IsGrothendieckAbelian.hasColimits (C := Modules.{u, m} B S hS F hF)).has_colimits_of_shape _

/-- **Stacks 08F3, closure under direct sums.**  Having quasi-coherent cohomology in every
degree is closed under `I`-indexed direct sums in `D(𝒪_F)`, as soon as an `I`-indexed direct
sum of quasi-coherent `𝒪_F`-modules is quasi-coherent. -/
theorem isClosedUnderCoproducts_quasicoherentDerivedCategory (I : Type m)
    (hsum : ∀ M : I → Modules.{u, m} B S hS F hF,
      (∀ i, (M i).IsQuasicoherentOnSite) → (∐ M).IsQuasicoherentOnSite) :
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)))).IsClosedUnderColimitsOfShape
      (Discrete I) := by
  refine ObjectProperty.IsClosedUnderColimitsOfShape.mk' ?_
  rintro _ ⟨G, hG⟩
  refine ObjectProperty.prop_of_iso _
    (HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := G))).symm (fun n => ?_)
  exact SheafOfModules.IsQuasicoherentOnSite.of_iso
    (Stacks.Duality.isoCoproductHomologyDerived (Modules.{u, m} B S hS F hF)
      (fun i => G.obj ⟨i⟩) n).symm (hsum _ fun i => hG ⟨i⟩ n)

/-- The derived category of `𝒪_F`-modules with quasi-coherent cohomology has direct sums, as
soon as a direct sum of quasi-coherent `𝒪_F`-modules is quasi-coherent.

The hypothesis `hsum` is the direct-sum clause of Stacks 03M1.  At the free module universe `m`
it has to be assumed, because the `←` direction of Descent, Proposition 03DX(2) is available
only at the module universe `u` of the structure rings; there it is a theorem, and
`AlgebraicGeometry.Space.hasCoproducts_quasicoherentDerivedCategory_ringUniverse` is this
statement with `hsum` supplied. -/
-- No `@[stacks 08F3]` attribute on this general-`m` statement, deliberately: `hsum` is a
-- hypothesis Stacks 08F3 does not have, and a statement carrying a hypothesis its source lacks
-- must not carry the tag.  The tag is on
-- `AlgebraicGeometry.Space.hasCoproducts_quasicoherentDerivedCategory_ringUniverse` below.
theorem hasCoproducts_quasicoherentDerivedCategory
    (hsum : ∀ (I : Type m) (M : I → Modules.{u, m} B S hS F hF),
      (∀ i, (M i).IsQuasicoherentOnSite) → (∐ M).IsQuasicoherentOnSite) :
    HasCoproducts.{m} (QuasicoherentDerivedCategory.{u, m} B S hS F hF) := fun I =>
  have := isClosedUnderCoproducts_quasicoherentDerivedCategory B S hS F hF I (hsum I)
  inferInstanceAs (HasColimitsOfShape (Discrete I)
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O)))).FullSubcategory)

omit [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
  [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [IsGrothendieckAbelian.{m} (Modules.{u, m} B S hS F hF)]

/-- **Stacks 08F3.**  Let `F` be an algebraic space over a scheme `S` contained in a big fppf
site `B`.  Then `D_QCoh(𝒪_F)`, the derived category of `𝒪_F`-modules with quasi-coherent
cohomology, has direct sums.

The tag lands at the module universe `u` of the structure rings, because the `←` direction of
Descent, Proposition 03DX(2) is available only there, and at a free module universe the
direct-sum clause of Stacks 03M1 would have to be assumed instead of proved.

This is `AlgebraicGeometry.Space.hasCoproducts_quasicoherentDerivedCategory` with its hypothesis
discharged by `AlgebraicGeometry.Space.isQuasicoherentOnSite_sigma_of_h03DX`, fed with
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`. -/
@[stacks 08F3]
theorem hasCoproducts_quasicoherentDerivedCategory_ringUniverse :
    HasCoproducts.{u} (QuasicoherentDerivedCategory.{u, u} B S hS F hF) := by
  have hes : EssentiallySmall.{u} (smallEtaleRingedSite B S hS F hF).C := by
    change EssentiallySmall.{u} (SmallEtale B S hS F)
    infer_instance
  have : IsGrothendieckAbelian.{u} (Modules.{u, u} B S hS F hF) :=
    SheafOfModules.isGrothendieckAbelian_of_essentiallySmall _
  exact hasCoproducts_quasicoherentDerivedCategory B S hS F hF
    fun _ M hM => isQuasicoherentOnSite_sigma_of_h03DX B S hS F hF
      (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS F hF) M hM

end AlgebraicGeometry.Space

end
