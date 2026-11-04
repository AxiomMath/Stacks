module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedModulePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedCategory
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.MayerVietorisTag
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedDirectSums
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentWeakSerreUnconditional
public import StacksFrontier.Algebra.Homology.DerivedCategory.BoundedBelowSerreImage
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.CartesianObjectsTriangulatedSubcategory
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentabilityShrinkHoms
public import StacksFrontier.Homology.DerivedCategory.LocallySmall

/-!
# The right adjoint of derived pushforward on algebraic spaces: the functors and Brown's step

Let `X`, `Y` be algebraic spaces over a scheme `S` contained in a big fppf site `B`. This file
sets up the shape in which [Stacks, Tag 0E55] is stated and proved: for an exact functor
`R : D(𝒪_X) ⥤ D(𝒪_Y)` sending `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)` (the case of interest is
`R = Rf_*`), its restriction `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, Brown representability for that
restriction, and its right adjoint `a` together with the adjunction.

## Main definitions

* `AlgebraicGeometry.Space.QuasicoherentDerivedCategoryOfModel` — `D_QCoh(𝒪_Z)` of
  [Stacks, Tag 071X] in an arbitrary model of `D(𝒪_Z)`. In the standard model it is
  `AlgebraicGeometry.Space.QuasicoherentDerivedCategory` at the module universe of the structure
  rings, by definition.
* `AlgebraicGeometry.Space.liftQuasicoherentDerived` — the restriction of `R` to the
  quasi-coherent derived categories.
* `AlgebraicGeometry.Space.twistedInverseImage` — the right adjoint `a` of that restriction, and
  `AlgebraicGeometry.Space.twistedInverseImageAdjunction`, the adjunction.

## Main results

* `AlgebraicGeometry.Space.quasicoherentDerivedProperty_isTriangulated`,
  `AlgebraicGeometry.Space.hasCoproducts_quasicoherentDerivedCategoryOfModel`,
  `AlgebraicGeometry.Space.locallySmall_quasicoherentDerivedCategoryOfModel` — `D_QCoh(𝒪_Z)` is a
  triangulated subcategory with direct sums ([Stacks, Tag 08F3]) and `u`-small morphism types, in
  every model.
* `AlgebraicGeometry.Space.isLeftAdjoint_liftQuasicoherentDerived_of_compact_generator` — the
  proof of [Stacks, Tag 0E55] from its inputs: if the restriction commutes with direct sums and
  `D_QCoh(𝒪_X)` has a compact weak generator, the restriction is a left adjoint.

## Implementation notes

*The model.* Every statement is made over arbitrary `[HasDerivedCategory]` instances for the two
module categories. The module universe is the universe `u` of the structure rings, which is the
source's: its `𝒪_X`-modules are sheaves of sets of the same universe as `𝒪_X`, and it is the
universe at which direct sums of quasi-coherent modules are quasi-coherent unconditionally
(`AlgebraicGeometry.Space.isQuasicoherentOnSite_sigma_of_h03DX` with
`AlgebraicGeometry.Space.isQuasicoherentOnSite_iff_isCartesianOnAffineCharts`).

*The functor is a parameter.* No derived direct image is fixed here: Brown's step and the right
adjoint are stated for any exact `R` preserving quasi-coherent cohomology, so they apply verbatim
to the derived direct image of a quasi-compact quasi-separated morphism, whose restriction is
literally `ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Rf_*) _`.

*The adjoint.* `twistedInverseImage R hR` is `Functor.rightAdjoint` of the restriction, under a
`Functor.IsLeftAdjoint` instance; any right adjoint is uniquely isomorphic to it, compatibly with
the adjunctions.

## References

* [Stacks Project, Tag 0E55](https://stacks.math.columbia.edu/tag/0E55)
* [Stacks Project, Tag 0A8G](https://stacks.math.columbia.edu/tag/0A8G)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
* [Stacks Project, Tag 08F3](https://stacks.math.columbia.edu/tag/08F3)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w w' u

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

attribute [local instance] isGrothendieckAbelian_modules

attribute [local instance] smallEtaleRingedSite_hasSheafify_addCommGrpCat
  smallEtaleRingedSite_wEqualsLocallyBijective_addCommGrpCat

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The predicate "every cohomology sheaf is quasi-coherent" on `D(𝒪_Z)`, for an algebraic space
`Z`, in an arbitrary model of `D(𝒪_Z)`. -/
abbrev quasicoherentDerivedProperty (Z : AlgebraicSpaces B S hS)
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS Z.1 Z.2)] :
    ObjectProperty (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :=
  DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O)))

/-- `D_QCoh(𝒪_Z)` ([Stacks, Tag 071X]) in an arbitrary model of `D(𝒪_Z)`: the full subcategory of
objects all of whose cohomology sheaves are quasi-coherent. In the standard model this is
`AlgebraicGeometry.Space.QuasicoherentDerivedCategory` at the module universe `u`. -/
abbrev QuasicoherentDerivedCategoryOfModel (Z : AlgebraicSpaces B S hS)
    [HasDerivedCategory.{w} (Modules.{u, u} B S hS Z.1 Z.2)] :=
  (quasicoherentDerivedProperty Z).FullSubcategory

/-! ### The triangulated structure on `D_QCoh` -/

section Triangulated

variable (Z : AlgebraicSpaces B S hS) [HasDerivedCategory.{w} (Modules.{u, u} B S hS Z.1 Z.2)]

omit [HasDerivedCategory.{w} (Modules.{u, u} B S hS Z.1 Z.2)] in
/-- Quasi-coherence of `𝒪_Z`-modules satisfies the five-term closure condition of a weak Serre
class ([Stacks, Tag 03M1] and [Stacks, Tag 0754]), at the module universe `u`. -/
theorem isWeakSerre_isQuasicoherentOnSite :
    WeakSerre.IsWeakSerre (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Z.1 Z.2).O))) :=
  have := quasicoherentSheaves_isWeakSerreClass_schemeUniverse B S hS Z.1 Z.2
  WeakSerre.isWeakSerre_of_isWeakSerreClass _

/-- `D_QCoh(𝒪_Z)` is a triangulated subcategory of `D(𝒪_Z)`, in every model. -/
instance quasicoherentDerivedProperty_isTriangulated :
    (quasicoherentDerivedProperty Z).IsTriangulated :=
  DerivedCategoryB.derivedCategoryB_isTriangulated _ (isWeakSerre_isQuasicoherentOnSite Z)

/-- `D_QCoh(𝒪_Z)` is strictly full in `D(𝒪_Z)`, in every model. -/
instance quasicoherentDerivedProperty_isClosedUnderIsomorphisms :
    (quasicoherentDerivedProperty Z).IsClosedUnderIsomorphisms :=
  DerivedCategoryB.derivedCategoryB_isClosedUnderIsomorphisms _
    (isWeakSerre_isQuasicoherentOnSite Z)

/-- `D_QCoh(𝒪_Z)` is closed under direct sums indexed by `Type u` in `D(𝒪_Z)`, in every model:
cohomology commutes with direct sums and a direct sum of quasi-coherent modules is quasi-coherent
([Stacks, Tag 08F3]). -/
instance quasicoherentDerivedProperty_isClosedUnderCoproducts (I : Type u) :
    (quasicoherentDerivedProperty Z).IsClosedUnderColimitsOfShape (Discrete I) :=
  Stacks.Duality.derivedCategoryB_isClosedUnderCoproducts _ _
    (isWeakSerre_isQuasicoherentOnSite Z)
    (fun M hM => isQuasicoherentOnSite_sigma_of_h03DX B S hS Z.1 Z.2
      (isQuasicoherentOnSite_iff_isCartesianOnAffineCharts B S hS Z.1 Z.2) M hM)

/-- **[Stacks, Tag 08F3] in every model.** `D_QCoh(𝒪_Z)` has direct sums indexed by `Type u`. -/
instance hasCoproducts_quasicoherentDerivedCategoryOfModel :
    HasCoproducts.{u} (QuasicoherentDerivedCategoryOfModel Z) := fun I =>
  haveI : HasCoproducts.{u} (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  inferInstanceAs (HasColimitsOfShape (Discrete I) (quasicoherentDerivedProperty Z).FullSubcategory)

/-- `D_QCoh(𝒪_Z)` has `u`-small morphism types, in every model. -/
instance locallySmall_quasicoherentDerivedCategoryOfModel :
    LocallySmall.{u} (QuasicoherentDerivedCategoryOfModel Z) :=
  haveI : LocallySmall.{u} (DerivedCategory (Modules.{u, u} B S hS Z.1 Z.2)) :=
    Stacks.ModulesOnACategory.CartesianSubcategory.locallySmall_derivedCategory _
  inferInstanceAs (LocallySmall.{u} (quasicoherentDerivedProperty Z).FullSubcategory)

end Triangulated

variable {X Y : AlgebraicSpaces B S hS}
  [HasDerivedCategory.{w} (Modules.{u, u} B S hS X.1 X.2)]
  [HasDerivedCategory.{w'} (Modules.{u, u} B S hS Y.1 Y.2)]
  (R : DerivedCategory (Modules.{u, u} B S hS X.1 X.2) ⥤
    DerivedCategory (Modules.{u, u} B S hS Y.1 Y.2))

/-- The hypothesis that `R : D(𝒪_X) ⥤ D(𝒪_Y)` sends `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`. For the
derived direct image of a quasi-compact and quasi-separated morphism this is
[Stacks, Tag 08FA], part (1). -/
abbrev PreservesQuasicoherentDerived : Prop :=
  ∀ K : QuasicoherentDerivedCategoryOfModel X,
    quasicoherentDerivedProperty Y (R.obj K.obj)

/-- The restriction `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of a functor `R : D(𝒪_X) ⥤ D(𝒪_Y)` preserving
quasi-coherent cohomology. For `R = Rf_*` this is the restricted derived direct image of
[Stacks, Tag 0E55]: in the standard model it is, by definition, the functor
`ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ Rf_*) _` of `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`. -/
abbrev liftQuasicoherentDerived (hR : PreservesQuasicoherentDerived R) :
    QuasicoherentDerivedCategoryOfModel X ⥤ QuasicoherentDerivedCategoryOfModel Y :=
  ObjectProperty.lift _ (ObjectProperty.ι _ ⋙ R) hR

/-- The restriction followed by the inclusion of `D_QCoh(𝒪_Y)` is `R` on `D_QCoh(𝒪_X)`. -/
def liftQuasicoherentDerivedCompιIso (hR : PreservesQuasicoherentDerived R) :
    liftQuasicoherentDerived R hR ⋙ (quasicoherentDerivedProperty Y).ι ≅
      (quasicoherentDerivedProperty X).ι ⋙ R :=
  ObjectProperty.liftCompιIso _ _ hR

/-! ### Brown representability -/

/-- **The proof of [Stacks, Tag 0E55], with its inputs as hypotheses.** Let `R : D(𝒪_X) ⥤ D(𝒪_Y)`
be an exact functor sending `D_QCoh(𝒪_X)` into `D_QCoh(𝒪_Y)`. If its restriction
`D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` commutes with direct sums and `D_QCoh(𝒪_X)` has a compact weak
generator, then the restriction has a right adjoint.

This is Brown representability ([Stacks, Tag 0A8G]) through
`CategoryTheory.Pretriangulated.isLeftAdjoint_lift_of_compact_generator`; that `D_QCoh(𝒪_X)` is
triangulated, has direct sums ([Stacks, Tag 08F3]) and small morphism types is supplied here, in
every model. For `R = Rf_*` along a quasi-compact quasi-separated morphism of quasi-compact
quasi-separated algebraic spaces the hypotheses are [Stacks, Tag 08FA] part (1), [Stacks, Tag
08FB], and the compact generator of [Stacks, Tag 09IY] (compact by [Stacks, Tag 09M8]). -/
theorem isLeftAdjoint_liftQuasicoherentDerived_of_compact_generator
    [R.CommShift ℤ] [R.IsTriangulated] (hR : PreservesQuasicoherentDerived R)
    [∀ I : Type u, PreservesColimitsOfShape (Discrete I) (liftQuasicoherentDerived R hR)]
    (G : QuasicoherentDerivedCategoryOfModel X) [IsCompactObject.{u} G]
    (hG : (ObjectProperty.singleton G).IsWeakTriangulatedGenerator) :
    (liftQuasicoherentDerived R hR).IsLeftAdjoint :=
  Pretriangulated.isLeftAdjoint_lift_of_compact_generator (quasicoherentDerivedProperty X)
    (quasicoherentDerivedProperty Y) R inferInstance inferInstance hR G hG

/-! ### The right adjoint -/

section Adjoint

variable (hR : PreservesQuasicoherentDerived R) [(liftQuasicoherentDerived R hR).IsLeftAdjoint]

/-- The right adjoint `a : D_QCoh(𝒪_Y) ⥤ D_QCoh(𝒪_X)` of the restriction of `R` to the
quasi-coherent derived categories, whenever the latter is a left adjoint. For `R = Rf_*` along a
morphism of quasi-compact and quasi-separated algebraic spaces it always is, by
[Stacks, Tag 0E55], and `a` is the twisted inverse image. -/
abbrev twistedInverseImage :
    QuasicoherentDerivedCategoryOfModel Y ⥤ QuasicoherentDerivedCategoryOfModel X :=
  (liftQuasicoherentDerived R hR).rightAdjoint

/-- The adjunction `R ⊣ a` on the quasi-coherent derived categories; for `R = Rf_*` its counit
`Rf_* a(K) ⟶ K` is the trace map of [Stacks, Section 0E54]. -/
def twistedInverseImageAdjunction :
    liftQuasicoherentDerived R hR ⊣ twistedInverseImage R hR :=
  Adjunction.ofIsLeftAdjoint _

end Adjoint

end AlgebraicGeometry.Space

end
