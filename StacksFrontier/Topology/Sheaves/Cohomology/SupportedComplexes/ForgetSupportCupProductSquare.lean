module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedTensorReseatConstraints
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorComparisonBraiding
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.ForgetSupportCupProductTranspose

/-!
# [Stacks, Tag 0G77] as one closed equation

`Stacks.Cohomology.SupportedComplexes.forgetSupport_supportedCupProductOfClasses` derives
[Stacks, Tag 0G77] at the source's own corepresenting objects from
`Stacks.Cohomology.SupportedComplexes.ShiftedUnitCorepresentingCompatible`. This file writes the
square itself down as a closed equation,
`Stacks.Cohomology.SupportedComplexes.ForgetSupportSquare`, and derives
`ShiftedUnitCorepresentingCompatible` from two simpler equations:

* `Stacks.Cohomology.SupportedComplexes.BraidingIsoEqCanonical`, the identification of the two
  spellings of the commutativity constraint of [Stacks, Tag 0FPT] used in this development,
  `Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom` and
  `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso`;
* `Stacks.Cohomology.SupportedComplexes.ShiftedUnitTransposeClean`, the comparison of
  [Stacks, Tag 079U] read at the two shifted structure sheaves, against the degree identification
  of the cup product on `X` and the comparisons `Li^*(𝒪_X[-p]) ≅ 𝒪_Z[-p]` of [Stacks, Tag 01CD].

## Main results

* `ForgetSupportSquare` — the square of Tag 0G77 as a closed equation.
* `pullbackTensorComparison_braidingIso` — the braiding compatibility of the comparison of
  Tag 079U at the `braidingIso` spelling.
* `shiftedUnitCorepresentingCompatible_of_clean` and `forgetSupportSquare_of_clean` — the two
  equations above imply `ShiftedUnitCorepresentingCompatible`, hence the square.

## References

* [Stacks Project, Lemma 20.34.11 (Tag 0G77)](https://stacks.math.columbia.edu/tag/0G77)
* [Stacks Project, Remark 20.34.9 (Tag 0G75)](https://stacks.math.columbia.edu/tag/0G75)
* [Stacks Project, Remark 20.34.10 (Tag 0G76)](https://stacks.math.columbia.edu/tag/0G76)
* [Stacks Project, Lemma 20.34.4 (Tag 0G70)](https://stacks.math.columbia.edu/tag/0G70)
* [Stacks Project, Lemma 20.28.6 (Tag 0B53)](https://stacks.math.columbia.edu/tag/0B53)
* [Stacks Project, Tag 079U](https://stacks.math.columbia.edu/tag/079U)
* [Stacks Project, Tag 079W](https://stacks.math.columbia.edu/tag/079W)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0FNH](https://stacks.math.columbia.edu/tag/0FNH)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Lemma 20.28.10 (Tag 08KS)](https://stacks.math.columbia.edu/tag/08KS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.DerivedTensor.RingedSite
open Stacks.SheafOfModules.DerivedMonoidal (canonicalBraidingHom)
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.Cohomology.DerivedProjectionFormula
open Stacks.RingedSpace (shiftedUnitObject shiftedUnitTensorIso
  derivedPullbackShiftedUnitTensorIso derivedPullbackShiftedUnitIso)
open scoped CategoryTheory.Prod

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

namespace Stacks.Cohomology.SupportedComplexes

/-- **The two spellings of the commutativity constraint of [Stacks, Tag 0FPT] agree.**

`Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom` is the braiding of the re-seated
symmetric monoidal structure of Tag 0FPT, and
`Stacks.DerivedTensor.RingedSite.DerivedTensorProduct.braidingIso` is the isomorphism obtained
by descending the Koszul symmetry of complexes through the K-flat comparisons of
[Stacks, Tag 06YU].  Both are read on the same bifunctor, Tag 06YU's own derived tensor product,
so this is an equation and not a transport; it is proved as
`Stacks.Cohomology.SupportedComplexes.braidingIsoEqCanonical`. -/
def BraidingIsoEqCanonical (W : RingedSpace.{u, u}) : Prop :=
  ∀ A B : DerivedCategory (SheafOfModules.{u} (structureSheafRing W)),
    canonicalBraidingHom W.sheaf A B =
      ((canonicalDerivedTensorProduct W.sheaf).braidingIso
        (AlgebraicGeometry.RingedSpace.ringedSite W) A B).hom

section Comparison

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The comparison of [Stacks, Tag 079U] is compatible with the commutativity constraint of
[Stacks, Tag 0FPT]**, at the `braidingIso` spelling in which the square of [Stacks, Tag 0G77]
is written.

`Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding` is this statement
for arbitrary objects and with no flatness hypothesis, but at the pinned spelling
`Stacks.SheafOfModules.DerivedMonoidal.canonicalBraidingHom`; the two hypotheses are
`BraidingIsoEqCanonical` on each of the two spaces. -/
theorem pullbackTensorComparison_braidingIso
    (hX : BraidingIsoEqCanonical X) (hY : BraidingIsoEqCanonical Y)
    (A₁ A₂ : DerivedCategory (SheafOfModules.{u} (structureSheafRing Y))) :
    (derivedPullback f).map
          ((canonicalDerivedTensorProduct Y.sheaf).braidingIso
            (AlgebraicGeometry.RingedSpace.ringedSite Y) A₁ A₂).hom ≫
        (pullbackTensorComparison f).app (A₂, A₁) =
      (pullbackTensorComparison f).app (A₁, A₂) ≫
        ((canonicalDerivedTensorProduct X.sheaf).braidingIso
          (AlgebraicGeometry.RingedSpace.ringedSite X)
          ((derivedPullback f).obj A₁) ((derivedPullback f).obj A₂)).hom := by
  rw [← hY A₁ A₂, ← hX _ _]
  exact Stacks.Cohomology.DerivedPullbackTensor.derivedPullbackTensorIso_braiding f A₁ A₂

end Comparison

section Residual

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) (a b : ℤ)

variable [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]

/-- **The residual equation of [Stacks, Tag 0G77].**

This is the hypothesis `hclean` of
`Stacks.Cohomology.SupportedComplexes.transposeCompatible_of_braidedComparison` at the data of
Tag 0G77: the comparison of [Stacks, Tag 079U] read at the two shifted structure sheaves
`𝒪_X[-a]`, `𝒪_X[-b]` themselves, against the degree identification `𝒪_X[-a-b] ≅ 𝒪_X[-a] ⊗^𝐋
𝒪_X[-b]` of [Stacks, Tag 0FNH], the identification `𝒪_Z[-a-b] ≅ (𝒪_X[-a])|_Z ⊗^𝐋 𝒪_Z[-b]` with
which Tag 0G76's cup product is built, and the comparisons `Li^*(𝒪_X[-p]) ≅ 𝒪_Z[-p]` at
`p = a + b` and `p = b`.

Neither the right adjoint `Ri_*`, nor the counit of the adjunction of [Stacks, Tag 079W], nor
its hom-equivalence, nor any inverse of the projection-formula map of [Stacks, Tag 0B53] occurs
in it — which is what distinguishes it from
`Stacks.Cohomology.SupportedComplexes.ShiftedUnitCorepresentingCompatible`, where all four do.
-/
def ShiftedUnitTransposeClean : Prop :=
  (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) (a + b)).hom ≫
        (derivedPullbackShiftedUnitTensorIso (closedSubsetInclusion X Z) a b).hom ≫
        ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
          (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
          ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedUnitObject X a))
          (shiftedUnitObject (closedSubsetRingedSpace X Z) b)).hom =
      (derivedPullback (closedSubsetInclusion X Z)).map (shiftedUnitTensorIso X a b).hom ≫
        (pullbackTensorComparison (closedSubsetInclusion X Z)).app
          (shiftedUnitObject X a, shiftedUnitObject X b) ≫
        ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
          (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
          ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedUnitObject X b))
          ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedUnitObject X a))).inv ≫
        ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map
            (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) b).hom).app
          ((derivedPullback (closedSubsetInclusion X Z)).obj (shiftedUnitObject X a))

omit [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))] in
/-- The naturality of the commutativity constraint of [Stacks, Tag 0FPT] on the closed subset,
in the shape `transposeCompatible_of_braidedComparison` consumes. -/
theorem braidingIso_hom_naturality_closedSubset
    {B₁ B₁' B₂ B₂' : DerivedCategory (SheafOfModules.{u}
      (structureSheafRing (closedSubsetRingedSpace X Z)))}
    (p : B₁ ⟶ B₁') (q : B₂ ⟶ B₂') :
    (((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map p).app B₂ ≫
          ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj B₁').map q) ≫
        ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
          (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
          B₁' B₂').hom =
      ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
          (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z)) B₁ B₂).hom ≫
        (((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).map q).app B₁ ≫
          ((derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf).obj B₂').map p) := by
  simpa only [Category.assoc] using DerivedTensorProduct.braidingIso_hom_naturality
    (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z))
    (canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf) p q

/-- **The one hypothesis of [Stacks, Tag 0G77] left at the canonical corepresenting objects
follows from the bridge and the residual equation.**

`Stacks.Cohomology.SupportedComplexes.ShiftedUnitCorepresentingCompatible` is obtained from
`ShiftedUnitTransposeClean` in two steps, both already in the tree:
`transposeCompatible_of_braidedComparison` puts the right adjoint, the counit and the
hom-equivalence back in, and `shiftedUnitCorepresentingCompatible_of_transpose` transposes the
result back under the adjunction of [Stacks, Tag 079W].  The braiding compatibility of the
comparison of [Stacks, Tag 079U] that the first step consumes is
`pullbackTensorComparison_braidingIso`, whence the two `BraidingIsoEqCanonical` hypotheses. -/
theorem shiftedUnitCorepresentingCompatible_of_clean
    (hbrX : BraidingIsoEqCanonical X)
    (hbrZ : BraidingIsoEqCanonical (closedSubsetRingedSpace X Z))
    (hclean : ShiftedUnitTransposeClean X Z a b) :
    ShiftedUnitCorepresentingCompatible X Z hZ a b :=
  shiftedUnitCorepresentingCompatible_of_transpose X Z hZ a b
    (transposeCompatible_of_braidedComparison
      (derivedAdjunction (closedSubsetInclusion X Z))
      (derivedTensorProductFunctor X.sheaf)
      (derivedTensorProductFunctor (closedSubsetRingedSpace X Z).sheaf)
      (pullbackTensorComparison (closedSubsetInclusion X Z))
      ((canonicalDerivedTensorProduct X.sheaf).braidingIso
        (AlgebraicGeometry.RingedSpace.ringedSite X))
      ((canonicalDerivedTensorProduct (closedSubsetRingedSpace X Z).sheaf).braidingIso
        (AlgebraicGeometry.RingedSpace.ringedSite (closedSubsetRingedSpace X Z)))
      (pullbackTensorComparison_braidingIso (closedSubsetInclusion X Z) hbrZ hbrX)
      (braidingIso_hom_naturality_closedSubset X Z)
      (derivedPullbackShiftedUnitTensorIso (closedSubsetInclusion X Z) a b).hom
      (shiftedUnitTensorIso X a b).hom
      (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) (a + b)).hom
      (derivedPullbackShiftedUnitIso (closedSubsetInclusion X Z) b).hom
      hclean)

end Residual

section Square

variable (X : RingedSpace.{u, u}) (Z : Set X.carrier) (hZ : IsClosed Z) (a b : ℤ)

variable [PreservesFiniteLimits (modulePushforward (closedSubsetInclusion X Z))]
  [PreservesFiniteColimits (modulePushforward (closedSubsetInclusion X Z))]

/-- **The commuting square of [Stacks, Tag 0G77], as a closed equation.**

```
H^a(X, K) × H^b_Z(X, M) -----> H^{a+b}_Z(X, K ⊗^L M)
    |                                  |
    v                                  v
H^a(X, K) × H^b(X, M) -------> H^{a+b}(X, K ⊗^L M)
```

Nothing is quantified over but the ringed space, the closed subset, the two degrees, the two
objects of `D(𝒪_X)` and the two classes: the three groups are corepresented by the shifted
structure sheaves of [Stacks, Tag 0G70], the top arrow is the cup product with support of
[Stacks, Tag 0G76] in the source's degrees, `supportedCupProductOfClasses`, the bottom arrow is
the ordinary cup product written with the degree identification of [Stacks, Tag 0FNH], and the
verticals forget support.

It is proved as `Stacks.Cohomology.SupportedComplexes.forgetSupport_supportedCupProduct_square`. -/
def ForgetSupportSquare
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (ξ : shiftedUnitObject X a ⟶ K)
    (η : shiftedUnitObject (closedSubsetRingedSpace X Z) b ⟶
      (derivedSupportedSectionsOnClosed X Z hZ).obj M) : Prop :=
  shiftedUnitToPushforward Z (a + b) ≫
        (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map
          (supportedCupProductOfClasses X Z hZ K M a b ξ η) ≫
        (derivedPushforwardAdjunction X Z hZ).counit.app
          (((derivedTensorProductFunctor X.sheaf).obj K).obj M) =
      (shiftedUnitTensorIso X a b).hom ≫
        ((derivedTensorProductFunctor X.sheaf).map ξ).app (shiftedUnitObject X b) ≫
        ((derivedTensorProductFunctor X.sheaf).obj K).map
          (shiftedUnitToPushforward Z b ≫
            (modulePushforward (closedSubsetInclusion X Z)).mapDerivedCategory.map η ≫
            (derivedPushforwardAdjunction X Z hZ).counit.app M)

/-- **[Stacks, Tag 0G77] follows from the bridge and the residual equation.**  The square is
`forgetSupport_supportedCupProductOfClasses` fed `shiftedUnitCorepresentingCompatible_of_clean`;
no clause of Tags 0G75, 0G76, 0B53, 0B55, 0FPT or 0A3B is assumed, all of them being discharged
in `ForgetSupportAndCupProduct.lean` from unconditional results. -/
theorem forgetSupportSquare_of_clean
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (hbrX : BraidingIsoEqCanonical X)
    (hbrZ : BraidingIsoEqCanonical (closedSubsetRingedSpace X Z))
    (hclean : ShiftedUnitTransposeClean X Z a b)
    (ξ : shiftedUnitObject X a ⟶ K)
    (η : shiftedUnitObject (closedSubsetRingedSpace X Z) b ⟶
      (derivedSupportedSectionsOnClosed X Z hZ).obj M) :
    ForgetSupportSquare X Z hZ a b K M ξ η :=
  forgetSupport_supportedCupProductOfClasses X Z hZ a b K M
    (shiftedUnitCorepresentingCompatible_of_clean X Z hZ a b hbrX hbrZ hclean) ξ η

end Square

end Stacks.Cohomology.SupportedComplexes

end
