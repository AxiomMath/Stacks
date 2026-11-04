module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.AdjointExistence
import StacksCore.Tactic.StacksAttribute

/-!
# Derived lower shriek and direct sums

Let `f : X ⟶ Y` be a finite type separated morphism of quasi-compact and quasi-separated
schemes and let `Λ` be a ring.  [Stacks, Tag 0G29] asserts two things.

1. If `K_i ∈ D⁺_tors(X_étale, Λ)`, `i ∈ I`, is a family of objects and `a ∈ ℤ` is such that
   `H^n(K_i) = 0` for `n < a` and all `i ∈ I`, then `Rf_!(⨁ i, K_i) = ⨁ i, Rf_! K_i`.
2. If `Λ` is torsion, then `Rf_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` commutes with direct sums.

The proof of the source reduces, by the construction `Rf_! = R(fbar)_* ∘ j_!` along a
compactification `f = fbar ∘ j`, to the case of an open immersion and the case of a proper
morphism.  For an open immersion `j` the functor `j_!` is a left adjoint of `j^{-1}` and
therefore commutes with direct sums, [Stacks, Tag 08FJ]; for a proper morphism one has
`Rf_! = Rf_*`, and the assertion is [Stacks, Tag 0GIW] in the bounded below case of (1) and
[Stacks, Tag 0F0D] in the torsion case of (2).

"Commutes with direct sums" is `CategoryTheory.Limits.PreservesColimit` for a discrete
diagram: the image of a coproduct cocone on the family is a coproduct cocone on the images,
which is exactly the equality `Rf_!(⨁ i, K_i) = ⨁ i, Rf_! K_i` of the source read through its
canonical comparison map.  Stated this way it does not presuppose that either coproduct
exists.

## Main results

All in the namespace `Stacks.EtaleCohomology.DerivedUpperShriek`.

* `preservesColimit_derivedLowerShriek_of_isGE` — **clause (1)**, for
  `Stacks.EtaleCohomology.derivedLowerShriek`, the `Rf_! = R(fbar)_* ∘ j_!` of a
  compactification on bounded below derived categories of sheaves of `Λ`-modules.
* `preservesColimitsOfShape_derivedLowerShriek` and
  `CompactificationData.preservesColimitsOfShape_derivedLowerShriek` — **clause (2)**, for
  `Rf_! = R(fbar)_* ∘ j_!` on the unbounded derived categories.

## Implementation notes

*The one input that is carried rather than used.* The proper case — that `R(fbar)_*` commutes
with the direct sums at issue — is [Stacks, Tag 0GIW] for clause (1) and [Stacks, Tag 0F0D]
for clause (2).  Neither is in this repository, so each appears as a hypothesis, in the shape
in which the source cites it: for clause (1) quantified over all families of objects of
`D⁺(Xbar_étale, Λ)` with the common lower bound `a`, which is the statement of
[Stacks, Tag 0GIW] for the proper, hence quasi-compact and quasi-separated, morphism `fbar`;
for clause (2) as preservation of all direct sums of the given shape, which is
[Stacks, Tag 0F0D] for a torsion coefficient ring.  This is where the torsion hypothesis on
`Λ` in clause (2) and the lower bound `a` in clause (1) enter the source's argument, and the
only place they do.

*The two inputs about the open immersion.* The adjunction `j_! ⊣ j^{-1}` on derived categories
is [Stacks, Tag 08FJ].  It is proved for a ringed site, and the direct sum statement it gives
there is `Stacks.Cohomology.Localization.preservesColimitsOfSize_derivedExtensionByZero`, but
it is not available at the spelling of the small étale site with a coefficient ring, where
`Stacks.EtaleCohomology.derivedLowerShriek` lives; there it is a hypothesis, exactly as in
`Stacks.EtaleCohomology.derivedLowerShriekAdjunctionOfFactors`.  That a left adjoint commutes
with direct sums is *proved* from it, not assumed.  Clause (1) also needs that `j_!` preserves
the lower bound `a`, which holds because extension by zero is exact, [Stacks, Tag 03S5]; the
repository has that exactness for abelian but not for module coefficients, so it too is a
hypothesis here.

*What is proved.* Given those inputs, the reduction itself — that the composite
`R(fbar)_* ∘ j_!` commutes with the direct sums, that the family `j_! K_i` is again bounded
below by `a` and is the family [Stacks, Tag 0GIW] must be applied to, and that a left adjoint
commutes with direct sums — is proved.

*The domain of clause (1).* The source states clause (1) for `K_i` in the subcategory
`D⁺_tors(X_étale, Λ)` of objects with torsion cohomology sheaves, this being the domain on
which it defines `Rf_!`.  The repository's `Stacks.EtaleCohomology.derivedLowerShriek` is
defined on all of `D⁺(X_étale, Λ)`, for the reason recorded in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology`: the formula uses
no torsion hypothesis.  Clause (1) is therefore stated here for an arbitrary family in
`D⁺(X_étale, Λ)`, which contains `Stacks.EtaleCohomology.isTorsionPlus` and so is strictly
more general than the source.

*Clause (2) and unbounded derived categories.* The repository has no unbounded `Rf_!` on the
small étale site, so clause (2) is stated for `Rf_! = R(fbar)_* ∘ j_!` with the three derived
categories as parameters, as in
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedUpperShriek.AdjointExistence`, where
they are instantiated at `CategoryTheory.DerivedCategory` of the sheaves of `Λ`-modules on
`X_étale`.  `CompactificationData.preservesColimitsOfShape_derivedLowerShriek` is the form
that discharges the hypothesis
`[∀ J, PreservesColimitsOfShape (Discrete J) data.derivedLowerShriek]` of
`Stacks.EtaleCohomology.DerivedUpperShriek.CompactificationData.isLeftAdjoint_derivedLowerShriek`,
which is [Stacks, Tag 0G2C] and is the consumer of this tag in the repository.

## References

* [Stacks Project, Tag 0G29](https://stacks.math.columbia.edu/tag/0G29)
* [Stacks Project, Tag 0GIW](https://stacks.math.columbia.edu/tag/0GIW)
* [Stacks Project, Tag 0F0D](https://stacks.math.columbia.edu/tag/0F0D)
* [Stacks Project, Tag 08FJ](https://stacks.math.columbia.edu/tag/08FJ)
* [Stacks Project, Tag 03S5](https://stacks.math.columbia.edu/tag/03S5)
* [Stacks Project, Tag 0G2C](https://stacks.math.columbia.edu/tag/0G2C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme

attribute [local instance] HasDerivedCategory.standard

universe w u r v₁ u₁ v₂ u₂ v₃ u₃

namespace Stacks.EtaleCohomology.DerivedUpperShriek

/-! ### Clause (1): a family with a common lower bound -/

/-- **[Stacks, Tag 0G29] (1).** Let `f : X ⟶ Y` be a finite type separated morphism of
quasi-compact and quasi-separated schemes, let `Λ` be a ring, let `j` be a compactification of
`f` and let `Rf_! = R(fbar)_* ∘ j_!` be the derived lower shriek it determines.  Let
`K : I → D⁺(X_étale, Λ)` be a family of objects and let `a : ℤ` be such that `H^n(K i) = 0`
for `n < a` and all `i`, that is `(K i).IsGE a`.  Then
`Rf_!(⨁ i, K i) = ⨁ i, Rf_!(K i)`.

The three inputs are the ones the source cites.  `adjImmersion` is the adjunction
`j_! ⊣ j^{-1}` of [Stacks, Tag 08FJ]; from it, and not from any further hypothesis, `j_!`
commutes with the direct sum.  `hShriekGE` is exactness of extension by zero,
[Stacks, Tag 03S5], in the form that `j_!` preserves the lower bound, so that
[Stacks, Tag 0GIW] applies to the family `j_! (K i)`.  `hProper` is [Stacks, Tag 0GIW] itself
for the proper — hence quasi-compact and quasi-separated — morphism `fbar = j.toBase`. -/
@[stacks 0G29 "(1) Rf_!(⨁ K_i) = ⨁ Rf_! K_i for a family with common lower bound a"]
theorem preservesColimit_derivedLowerShriek_of_isGE {X Y : Scheme.{u}} {f : X ⟶ Y}
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    [CompactSpace X] [QuasiSeparatedSpace X] [CompactSpace Y] [QuasiSeparatedSpace Y]
    (j : CompactificationOf (Over.mk f)) (Λ : Type r) [Ring Λ]
    {I : Type w} (K : I → DerivedCategory.Plus (EtaleModules.{u, r} Λ X))
    (a : ℤ) (hK : ∀ i, (K i).IsGE a)
    {Uj : DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space) ⥤
      DerivedCategory.Plus (EtaleModules.{u, r} Λ X)}
    (adjImmersion : etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion ⊣ Uj)
    (hShriekGE : ∀ (b : ℤ) (M : DerivedCategory.Plus (EtaleModules.{u, r} Λ X)), M.IsGE b →
      ((etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion).obj M).IsGE b)
    (hProper : ∀ L : I → DerivedCategory.Plus (EtaleModules.{u, r} Λ j.space),
      (∀ i, (L i).IsGE a) →
      PreservesColimit (Discrete.functor L)
        (etaleModuleDerivedDirectImage.{u, r} Λ j.toBase)) :
    PreservesColimit (Discrete.functor K) (derivedLowerShriek.{u, r} f j Λ) := by
  have hShriek : PreservesColimit (Discrete.functor K)
      (etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion) :=
    adjImmersion.leftAdjoint_preservesColimits.preservesColimitsOfShape.preservesColimit
  have hSum : PreservesColimit
      (Discrete.functor ((etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion).obj ∘ K))
      (etaleModuleDerivedDirectImage.{u, r} Λ j.toBase) :=
    hProper ((etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion).obj ∘ K)
      fun i ↦ hShriekGE a (K i) (hK i)
  have hComp : PreservesColimit
      (Discrete.functor K ⋙ etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion)
      (etaleModuleDerivedDirectImage.{u, r} Λ j.toBase) :=
    (preservesColimit_iff_of_iso_diagram (etaleModuleDerivedDirectImage.{u, r} Λ j.toBase)
      (Discrete.compNatIsoDiscrete K
        (etaleModuleDerivedExtensionByZero.{u, r} Λ j.immersion))).mpr hSum
  exact @Limits.comp_preservesColimit _ _ _ _ _ _ _ _ _ _ _ hShriek hComp

/-! ### Clause (2): a torsion coefficient ring -/

/-- **[Stacks, Tag 0G29] (2).** Let `Λ` be a torsion ring and let
`Rf_! = R(fbar)_* ∘ j_! : D(X_étale, Λ) ⟶ D(Y_étale, Λ)` be the derived lower shriek of a
compactification `f = fbar ∘ j` of a finite type separated morphism of quasi-compact and
quasi-separated schemes.  Then `Rf_!` commutes with direct sums of every shape.

The two inputs are the ones the source cites: `adjImmersion` is the adjunction `j_! ⊣ j^{-1}`
of [Stacks, Tag 08FJ] for the open immersion `j`, and `hProper` is [Stacks, Tag 0F0D], that
`R(fbar)_*` commutes with direct sums for a torsion coefficient ring.  That a left adjoint
commutes with direct sums, and that the composite therefore does, is proved. -/
@[stacks 0G29 "(2) for Λ torsion, Rf_! = R(fbar)_* ∘ j_! commutes with direct sums"]
theorem preservesColimitsOfShape_derivedLowerShriek {DU : Type u₁} [Category.{v₁} DU]
    {DX : Type u₂} [Category.{v₂} DX] {DY : Type u₃} [Category.{v₃} DY]
    {shriek : DU ⥤ DX} {Uj : DX ⥤ DU} (adjImmersion : shriek ⊣ Uj)
    (pushforwardFbar : DX ⥤ DY) (I : Type w)
    (hProper : PreservesColimitsOfShape (Discrete I) pushforwardFbar) :
    PreservesColimitsOfShape (Discrete I) (shriek ⋙ pushforwardFbar) :=
  let : PreservesColimitsOfShape (Discrete I) shriek :=
    adjImmersion.leftAdjoint_preservesColimits.preservesColimitsOfShape
  let := hProper
  Limits.comp_preservesColimitsOfShape _ _

namespace CompactificationData

/-- **[Stacks, Tag 0G29] (2) for the derived lower shriek of a `CompactificationData`.**  The
functor `Rf_! = R(fbar)_* ∘ j_!` read off a compactification commutes with direct sums of
every shape, given the adjunction `j_! ⊣ j^{-1}` of [Stacks, Tag 08FJ] and
[Stacks, Tag 0F0D] for `R(fbar)_*`.

This is the form that discharges the hypothesis of
`Stacks.EtaleCohomology.DerivedUpperShriek.CompactificationData.isLeftAdjoint_derivedLowerShriek`,
which is [Stacks, Tag 0G2C]. -/
@[stacks 0G29 "(2) for a CompactificationData: Rf_! commutes with direct sums"]
theorem preservesColimitsOfShape_derivedLowerShriek {DU : Type u₁} [Category.{v₁} DU]
    {DX : Type u₂} [Category.{v₂} DX] {DY : Type u₃} [Category.{v₃} DY]
    (data : CompactificationData DU DX DY) {Uj : DX ⥤ DU} (adjImmersion : data.shriek ⊣ Uj)
    (I : Type w)
    (hProper : PreservesColimitsOfShape (Discrete I) data.pushforwardFbar) :
    PreservesColimitsOfShape (Discrete I) data.derivedLowerShriek :=
  DerivedUpperShriek.preservesColimitsOfShape_derivedLowerShriek adjImmersion
    data.pushforwardFbar I hProper

end CompactificationData

end Stacks.EtaleCohomology.DerivedUpperShriek

end
