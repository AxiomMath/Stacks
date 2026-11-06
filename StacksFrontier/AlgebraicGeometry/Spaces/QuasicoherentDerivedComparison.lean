module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.Spaces.CokernelAffineSurjectivity
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCartesianOnAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentCokernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsOnSite
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentKernelsUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.ShortExactQuasicoherent
public import StacksCore.CategoryTheory.Abelian.SerreClass.Weak
import StacksCore.Tactic.StacksAttribute

/-!
# The comparison `D(QCoh(𝒪_F)) ⥤ D_QCoh(𝒪_F)` on an algebraic space

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B`.  The inclusion
`QCoh(𝒪_F) ⥤ Mod(𝒪_F)` of the quasi-coherent `𝒪_F`-modules into all `𝒪_F`-modules is exact, so
its derived functor lands in the full subcategory `D_QCoh(𝒪_F)` of objects with quasi-coherent
cohomology.  The resulting functor

`D(QCoh(𝒪_F)) ⥤ D_QCoh(𝒪_F)`

is what Stacks 08F1 writes down.  It is reached twice here: at a free module universe under two
closure hypotheses, and — carrying the Stacks 08F1 tag — at the universe of the schemes, where
the source puts it, **with no hypothesis at all**.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentDerivedComparison` is the comparison functor at a free
  module universe, under the closure of quasi-coherence under kernels and under cokernels.
* `AlgebraicGeometry.Space.quasicoherentDerivedComparisonSchemeUniverse` is **the comparison
  functor of Stacks 08F1**, with its `𝒪_F`-modules at the universe of the schemes, where the
  source puts them, and with no open input.

## Main results

* `AlgebraicGeometry.Space.derivedCategoryB_mapDerivedCategory_obj`: the derived inclusion has
  quasi-coherent cohomology in every degree.
* `AlgebraicGeometry.Space.quasicoherentDerivedComparisonCompιIso`: the comparison followed by
  the inclusion of `D_QCoh(𝒪_F)` into `D(𝒪_F)` is the derived inclusion.
* `AlgebraicGeometry.Space.isClosedUnderExtensions_quasicoherentSheaves_of_h03DW`: the extension
  clause of Stacks 03M1 at the universe of the schemes, on the uniform form of Descent,
  Proposition 03DW alone.
* `AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass`: quasi-coherence on the small
  étale site of an algebraic space is a weak Serre class, given that extension clause.

## What each form of the comparison assumes

Stacks 08F1 is Equation 75.5.1.1, the single arrow `D(QCoh(𝒪_X)) ⟶ D_QCoh(𝒪_X)`, introduced
with "this makes sense by Properties of Spaces, Lemma 03M1".  So the source assumes Stacks 03M1
and the covering set of the tag is this one functor.  What the functor needs of Stacks 03M1 is
closure of quasi-coherence under kernels, under cokernels and under finite direct sums: the
first two make the inclusion `QCoh(𝒪_F) ⥤ Mod(𝒪_F)` exact, and together with the third they
make `QCoh(𝒪_F)` abelian, hence make `D(QCoh(𝒪_F))` — the source of the comparison — exist at
all.  That is what `AlgebraicGeometry.Space.quasicoherentSheaves_abelian_of_closure` carries.

The direct-sum clause is unconditional on every site and in every module universe, by
`SheafOfModules.isQuasicoherentOnSite_isClosedUnderFiniteProducts`, so it is never a binder.
`AlgebraicGeometry.Space.quasicoherentDerivedComparison` takes the other two as instance
binders at a free module universe `m`, and carries no tag for that reason.

`AlgebraicGeometry.Space.quasicoherentDerivedComparisonSchemeUniverse` takes no hypothesis, at
the module universe `u` of the schemes, and **carries the Stacks 08F1 tag**.  Both remaining
clauses are theorems of this development at `m := u`, resting on Descent, Proposition 03DX(2)
for the small étale site of `F`, which is
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`: the kernel clause
is `AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_schemeUniverse` and the
cokernel clause is `AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`, both
imported here rather than restated.  The free-`m` form stays untagged not because Stacks 03M1 is
missing but because Stacks 03DX(2) is available only at `m := u`; raising it is a universe
question, not a mathematical one.

The two clauses of Stacks 03M1 that 08F1 does not use — arbitrary direct sums and arbitrary
colimits — are not needed here at all, and neither is its extension clause: closure under
extensions is what upgrades quasi-coherence to a *weak Serre class* in the sense of Stacks 0754,
which is more than the comparison functor asks for.  That clause is still open, and is reduced
here to the uniform form of Descent, Proposition 03DW by
`AlgebraicGeometry.Space.isClosedUnderExtensions_quasicoherentSheaves_of_h03DW`; the weak Serre
class instance below carries it as a hypothesis.

## Implementation notes

`D_QCoh(𝒪_F)` is `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` of Stacks 071X and
`QCoh(𝒪_F)` is `AlgebraicGeometry.Space.QuasicoherentSheaves` of Stacks 03G9; no category is
restated.

Exactness of the inclusion is not assembled from the weak Serre property: left exactness is
`SheafOfModules.preservesFiniteLimits_ι_isQuasicoherentOnSite`, which needs the kernel clause
and the finite-product instance, and right exactness is the mirror argument through
`CategoryTheory.ObjectProperty.preservesCokernels_ι`, which needs the cokernel clause.  This is
the route taken for a bundled algebraic space in
`StacksFrontier/AlgebraicGeometry/Spaces/CoheratorFlatPushforward.lean`.  The two remaining
conditions of `CategoryTheory.ObjectProperty.IsWeakSerreClass` are not hypotheses either:
closure under isomorphisms and containing a zero object are instances already in the library,
from `StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels` and
`StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentGrothendieck`.

That the derived inclusion has quasi-coherent cohomology is the comparison
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso` for an exact functor, `Hⁿ(I(K)) ≅
I(Hⁿ(K))`, together with the fact that `I` takes values in the quasi-coherent modules.  The
comparison is obtained by corestricting the derived inclusion along
`CategoryTheory.ObjectProperty.lift`, so its composite with the inclusion of `D_QCoh(𝒪_F)` is
the derived inclusion on the nose, by `CategoryTheory.ObjectProperty.liftCompιIso`.

The module universe is free, as in `AlgebraicGeometry.Space.QuasicoherentDerivedCategory`, and
the two sheafification hypotheses are the ones under which the `𝒪_F`-modules at that universe
are abelian.

## References

* [Stacks Project, Tag 08F1](https://stacks.math.columbia.edu/tag/08F1)
* [Stacks Project, Tag 03M1](https://stacks.math.columbia.edu/tag/03M1)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03DW](https://stacks.math.columbia.edu/tag/03DW)
* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u m

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    [HasSheafify (smallEtaleRingedSite B S hS F hF).J AddCommGrpCat.{m}]
    [(smallEtaleRingedSite B S hS F hF).J.WEqualsLocallyBijective AddCommGrpCat.{m}]
    [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderKernels]
    [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderCokernels]

/-- The inclusion `QCoh(𝒪_F) ⥤ Mod(𝒪_F)` is left exact: quasi-coherence is closed under
kernels, so the inclusion creates them. -/
instance preservesFiniteLimits_ι_quasicoherentSheaves :
    PreservesFiniteLimits
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι :=
  SheafOfModules.preservesFiniteLimits_ι_isQuasicoherentOnSite _

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- The inclusion `QCoh(𝒪_F) ⥤ Mod(𝒪_F)` is right exact: quasi-coherence is closed under
cokernels, so the inclusion creates them. -/
instance preservesFiniteColimits_ι_quasicoherentSheaves :
    PreservesFiniteColimits
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι :=
  have : ∀ ⦃A C : QuasicoherentSheaves.{u, m} B S hS F hF⦄ (a : A ⟶ C),
      PreservesColimit (parallelPair a 0)
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι :=
    fun {_ _} a ↦ ObjectProperty.preservesCokernels_ι _ a
  have : HasFiniteProducts (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).FullSubcategory := inferInstance
  have : HasFiniteBiproducts (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).FullSubcategory :=
    HasFiniteBiproducts.of_hasFiniteProducts
  have : HasFiniteCoproducts (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).FullSubcategory :=
    hasFiniteCoproducts_of_hasFiniteBiproducts _
  Functor.preservesFiniteColimits_of_preservesCokernels _

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in
/-- The inclusion `QCoh(𝒪_F) ⥤ Mod(𝒪_F)` is additive: it preserves binary products. -/
instance additive_ι_quasicoherentSheaves :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O))).ι.Additive :=
  Functor.additive_of_preserves_binary_products _

/-- The derived functor of the inclusion of the quasi-coherent `𝒪_F`-modules has quasi-coherent
cohomology in every degree: the inclusion is exact, so it commutes with cohomology. -/
theorem derivedCategoryB_mapDerivedCategory_obj
    (K : DerivedCategory (QuasicoherentSheaves.{u, m} B S hS F hF)) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))
      ((SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O))).ι.mapDerivedCategory.obj K) := by
  set P := SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
    ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)) with hP
  intro n
  exact P.prop_of_iso ((P.ι.mapDerivedCategoryHomologyIso n).app K).symm
    (P.prop_ι_obj ((DerivedCategory.homologyFunctor _ n).obj K))

/-- The canonical functor from the derived category of the quasi-coherent `𝒪_F`-modules to the
derived category of all `𝒪_F`-modules with quasi-coherent cohomology, given the closure of
quasi-coherence under kernels and under cokernels.

Those two closure properties are two clauses of Stacks 03M1, which Stacks 08F1 assumes rather
than states.  At a free module universe they are not available here, so this form is left
untagged; `AlgebraicGeometry.Space.quasicoherentDerivedComparisonSchemeUniverse` is the tagged
form, at the module universe of the schemes and with no hypothesis.  See "What each form of the
comparison assumes" in the module documentation. -/
-- No `@[stacks 08F1]` attribute on this form, deliberately: the two `IsClosedUnder…` instance
-- binders in the section variables are hypotheses Stacks 08F1 does not have.  The tag sits on
-- the specialization to the module universe of the schemes further down, where both of them are
-- discharged.
noncomputable def quasicoherentDerivedComparison :
    DerivedCategory (QuasicoherentSheaves.{u, m} B S hS F hF) ⥤
      QuasicoherentDerivedCategory.{u, m} B S hS F hF :=
  (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))).lift
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).ι.mapDerivedCategory
    (derivedCategoryB_mapDerivedCategory_obj B S hS F hF)

/-- The comparison functor of Stacks 08F1 followed by the inclusion of `D_QCoh(𝒪_F)` into
`D(𝒪_F)` is the derived functor of the inclusion `QCoh(𝒪_F) ⥤ Mod(𝒪_F)`. -/
noncomputable def quasicoherentDerivedComparisonCompιIso :
    quasicoherentDerivedComparison B S hS F hF ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS F hF).O)))).ι ≅
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
        ((Stacks.SheafOfModules.Tensor.ringSheaf
          (smallEtaleRingedSite B S hS F hF).O))).ι.mapDerivedCategory :=
  ObjectProperty.liftCompιIso _ _ _

section WeakSerre

variable [(SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
    ((Stacks.SheafOfModules.Tensor.ringSheaf
      (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderExtensions]

/-- **Stacks 03M1, as a weak Serre class.**  Quasi-coherence of `𝒪_F`-modules on an algebraic
space is a weak Serre class in the sense of Stacks 0754, as soon as it is closed under kernels,
cokernels and extensions.

This is strictly more than the comparison functor of Stacks 08F1 needs; see "What each form of
the comparison assumes" in the module documentation. -/
instance quasicoherentSheaves_isWeakSerreClass :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, m}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsWeakSerreClass where

end WeakSerre

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Space

open Opposite

attribute [local instance] HasDerivedCategory.standard

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The extension clause of Stacks 03M1 at the universe of the schemes, on the uniform form of
Stacks 03DW alone.**  The middle term of a short exact sequence of `𝒪_F`-modules whose outer
terms are quasi-coherent is quasi-coherent: the right-hand map is surjective on affine-chart
sections by `AlgebraicGeometry.Space.surjective_g_val_app_of_shortExact_of_h03DW`, and Descent,
Proposition 03DX(2) supplies the cartesian hypotheses.

This clause is not used by the comparison functor of Stacks 08F1; it is what upgrades
quasi-coherence to a weak Serre class, through
`AlgebraicGeometry.Space.quasicoherentSheaves_isWeakSerreClass`. -/
theorem isClosedUnderExtensions_quasicoherentSheaves_of_h03DW
    (h03DW : ∀ {P Q : Modules.{u, u} B S hS F hF} (q : P ⟶ Q), Epi q →
      IsCartesianOnAffineCharts (kernel q) → ∀ W : SmallEtale B S hS F,
        IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj W) →
          Function.Surjective (q.val.app (op W))) :
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (smallEtaleRingedSite B S hS F hF).O))).IsClosedUnderExtensions where
  prop_X₂_of_shortExact {T} hT h₁ h₃ := by
    have : T.X₁.IsQuasicoherentOnSite := h₁
    have : T.X₃.IsQuasicoherentOnSite := h₃
    exact isQuasicoherent_middle_of_shortExact T hT
      (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF)
      (fun U hU => surjective_g_val_app_of_shortExact_of_h03DW T hT h03DW
        (isCartesianOnAffineCharts_of_isQuasicoherentOnSite B S hS F hF T.X₁ h₁) U hU)

/-- **Stacks 08F1**, the comparison functor `D(QCoh(𝒪_F)) ⥤ D_QCoh(𝒪_F)` of an algebraic space,
with its `𝒪_F`-modules taken at the universe of the schemes, where the source assumes them.

It has no open input.  What the functor needs of Properties of Spaces, Lemma 03M1 — the lemma
Stacks 08F1 points at for the comparison to make sense — is the closure of quasi-coherence under
kernels, under cokernels and under finite direct sums, and all three hold at this universe: the
kernel clause is
`AlgebraicGeometry.Space.isClosedUnderKernels_quasicoherentSheaves_schemeUniverse`, the cokernel
clause is `AlgebraicGeometry.Space.isClosedUnderCokernels_quasicoherentSheaves`, and the
direct-sum clause is the instance
`SheafOfModules.isQuasicoherentOnSite_isClosedUnderFiniteProducts`. -/
@[stacks 08F1]
noncomputable def quasicoherentDerivedComparisonSchemeUniverse :
    letI := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
    letI := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
    DerivedCategory (QuasicoherentSheaves.{u, u} B S hS F hF) ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS F hF :=
  letI := isClosedUnderKernels_quasicoherentSheaves_schemeUniverse B S hS F hF
  letI := isClosedUnderCokernels_quasicoherentSheaves B S hS F hF
  quasicoherentDerivedComparison B S hS F hF

end AlgebraicGeometry.Space

end
