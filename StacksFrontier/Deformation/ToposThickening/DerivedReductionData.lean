module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.CategoryTheory.Functor.Derived.Adjunction
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ChangeOfRingsExactness
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Adjunction
public import StacksFrontier.Deformation.ToposThickening.DerivedComplexLift
public import StacksFrontier.Deformation.ToposThickening.DerivedExtensionOfScalarsExists
public import StacksFrontier.Deformation.ToposThickening.DerivedReductionTriangle

/-!
# Derived restriction of scalars, and the reduction triangle read on a ringed site

Let `f : O ⟶ O₀` be a morphism of sheaves of commutative rings on a site. A
`Deformation.ComplexLift.DerivedReduction` relative to a derived base change `T` along `f` is six
pieces of data: a functor `restriction : D(O₀) ⥤ D(O)`, its additivity, its commutation with the
shift, an adjunction `T.baseChange ⊣ restriction`, the inclusion of the ideal part of a complex
and the connecting morphism, the last two subject to the triangle being distinguished.

This file supplies the first four unconditionally, and records the identification of the two
conventions under which the category of sheaves of modules is written in the tree, which is what
lets the reduction triangle of
`StacksFrontier/Deformation/ToposThickening/DerivedReductionTriangle.lean` be compared with the
triangle a `DerivedReduction` asks for.

## Main definitions

* `Deformation.ComplexLift.restrictionOnDerived`: restriction of scalars along `f` on the
  unbounded derived categories, the candidate for the `restriction` field.
* `Deformation.ComplexLift.derivedAdjunction`: **Stacks 09T5 for change of rings**, the derived
  base change of Stacks 0794 is left adjoint to derived restriction of scalars.
* `Deformation.ComplexLift.derivedAdjunctionOf`: the same for an arbitrary derived base change
  along `f`, which is the `adjunction` field of a
  `Deformation.ComplexLift.DerivedReduction`.
* `Deformation.ComplexLift.ringedSiteOf`: the ringed site on which the derived tensor product of
  `O`-modules, and hence the reduction triangle, is stated.

## Main results

* `Deformation.ComplexLift.restrictionOnDerived_additive` and
  `Deformation.ComplexLift.restrictionOnDerived_commShift`: the `additive` and `commShift` fields
  of a `Deformation.ComplexLift.DerivedReduction` at `restrictionOnDerived`.
* `Deformation.ComplexLift.isRightDerivedFunctor_restrictionOnDerived` and
  `Deformation.ComplexLift.isRightDerivedFunctor_restrictionOnDerived_comp`: derived restriction
  of scalars is the right derived functor of restriction of scalars, and is absolute.
* `Deformation.ComplexLift.modules_ringedSiteOf`: the category of sheaves of modules on
  `ringedSiteOf J O` is the one the lift statements are written over, on the nose.

## Implementation notes

Restriction of scalars is exact
  (`Stacks.SheafOfModules.ChangeOfRings.exactFunctor_restrictScalars`),
so it needs no derived functor: `CategoryTheory.Functor.mapDerivedCategory` applies, and
additivity and the shift come with it.

**The adjunction.** `CategoryTheory.Adjunction.derived` (Stacks 09T5) asks for an adjunction on
the categories being localized — the homotopy categories, supplied by
`CategoryTheory.Adjunction.mapHomotopyCategory` from Stacks 03CZ — and for both derived functors
to be *absolute*. For derived restriction of scalars absoluteness is free: the comparison
`CategoryTheory.Functor.mapDerivedCategoryFactorsh` is an isomorphism, so it stays one after
whiskering, and `CategoryTheory.Functor.isRightDerivedFunctor_of_inverts` applies. For the
derived base change it is *not* part of the data of a
`Deformation.ComplexLift.DerivedExtensionOfScalars`, which records only
`CategoryTheory.Functor.IsLeftDerivedFunctor`; it holds for the functor produced by Stacks 0794
at a class of resolutions, and that statement is
`Deformation.ComplexLift.isLeftDerivedFunctor_comp_derivedExtensionOfScalars`. So the adjunction
is built for the *constructed* derived base change and transported to an arbitrary one by
uniqueness of left derived functors
(`Deformation.ComplexLift.DerivedExtensionOfScalars.baseChangeIso`).

**How the remaining two fields are obtained: three identifications of vertices.** The triangle
obtained by tensoring the square-zero ideal sequence `0 ⟶ I ⟶ O ⟶ O₀ ⟶ 0` with an object `K` of
`D(O)` — `Stacks.SheafOfModules.DerivedTensorProduct.tensorSingleTriangle`, distinguished
because tensoring with a fixed object is an exact functor of triangulated categories — has
vertices `K ⊗^L_O I`, `K ⊗^L_O O` and `K ⊗^L_O O₀` formed with the derived tensor product of
`O`-modules, whereas `Deformation.ComplexLift.DerivedReduction` asks for
`restriction (idealTensor (T.baseChange K))`, `K` and `restriction (T.baseChange K)`. The three
identifications are `Deformation.ComplexLift.idealVertexIso`,
`Deformation.ComplexLift.unitVertexIso` and `Deformation.ComplexLift.quotientVertexIso`: the
first rests on `Deformation.ComplexLift.derivedIdealTensorIsoOf`, which is where squareness of
the ideal enters — `I` is an `O₀`-module; the middle one on the unit law
`Deformation.ComplexLift.derivedTensorRightUnitIso`; the third on
`Deformation.ComplexLift.derivedRestrictExtensionIsoOf`. The transport along them is
`Deformation.ComplexLift.derivedReductionOfTriangle`, and the datum itself is
`Deformation.ComplexLift.nonempty_derivedReduction`.

**Why the unit law has to be an isomorphism of functors.**
`Stacks.SheafOfModules.DerivedTensorProduct.rightUnitor` identifies `K ⊗^L_O O` with `K` one
object at a time, through an arbitrary preimage of `K` under the localization, so the triangle
built with it is not natural in `K`; but the second morphism of a reduction triangle has to be
compared with the unit of an adjunction, which is natural. So the middle vertex is identified by
`Deformation.ComplexLift.derivedTensorRightUnitIso`, which exhibits the identity functor of
`D(O)` as a left derived functor of `- ⊗_O O` — the comparison being invertible — and is
therefore an isomorphism of functors. The comparison with the unit is then
`Deformation.ComplexLift.tensorMap_comp_quotientVertexIso`, an equality of natural
transformations `- ⊗^L_O O ⟶ - ⊗^L_O O₀|_O` proved by uniqueness of left derived functors from
one module-level input: `Deformation.ComplexLift.unit_comp_restrictExtensionIsoTensorRight`, that
the unit of the extension/restriction-of-scalars adjunction at `N`, read through
`Deformation.ComplexLift.restrictExtensionIsoTensorRight`, is the inverse right unit law
`N ≅ N ⊗_O O` followed by tensoring `N` with the surjection `O ⟶ O₀|_O`.

*The universes.* `Stacks.SheafOfModules.exists_derivedTensorProduct` is stated for an
`AlgebraicGeometry.RingedSite.{c, u, w}` whose object, morphism and section universes are
independent, so it applies to `Deformation.ComplexLift.ringedSiteOf J O` at a free module
universe `u`; that reading is
`Deformation.ComplexLift.nonempty_derivedTensorProductRingedSiteOf`. The K-flat resolution it
rests on, `Stacks.SheafOfModules.exists_kFlat_quasiIso`, never related the three universes. The
unit law is taken in the form `Stacks.SheafOfModules.sheafTensorUnitNatIsoOfSize`, whose module
universe is free of the site, rather than `Stacks.SheafOfModules.sheafTensorUnitNatIso`, which
reads the unitor off the monoidal structure of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/MonoidalSheafTensor.lean` and is available only for
a structure sheaf in `CommRingCat.{max u' v'}`. So the reduction triangle is available exactly
where Tags 0DIY and 0DIZ are stated.

The short exact sequence of *functors* `0 ⟶ (- ⊗_O I) ⟶ 𝟭 ⟶ (- ⊗_O O₀) ⟶ 0` would produce the
triangle in one step, but it is not the route taken: the distinguished triangle of the *total
left* derived functors of a short exact sequence of functors exact on a resolving class is in the
tree only for functors which are already exact, as
`CategoryTheory.DerivedCategory.exists_distTriang_of_natTrans_shortExact` of
`StacksFrontier/Algebra/Homology/DerivedCategory/ShortExactFunctorsTriangle.lean`, whose shape —
`L ⟶ 𝟭 ⟶ R` with an existential connecting morphism — is exactly the shape a `DerivedReduction`
asks for, but which asks short exactness at every object rather than at the flat ones.

## References

* [Stacks Project, Tag 0DIY](https://stacks.math.columbia.edu/tag/0DIY)
* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public section

open CategoryTheory

universe d d₀ v' u u'

namespace Deformation.ComplexLift

variable {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
variable [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})]
variable [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable {O O₀ : Sheaf J CommRingCat.{u}}

/-- Restriction of scalars along `f` is additive: it preserves finite limits, hence binary
products. -/
instance restrictScalars_additive (f : O ⟶ O₀) :
    (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).Additive :=
  Functor.additive_of_preserves_binary_products _

variable (f : O ⟶ O₀)
variable [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))]
variable [HasDerivedCategory.{d₀} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))]

/-- **Restriction of scalars along `f` on the unbounded derived categories.** Restriction of
scalars is exact, so it descends to the derived categories without being derived; this is the
candidate for the `restriction` field of a `Deformation.ComplexLift.DerivedReduction`. -/
noncomputable def restrictionOnDerived :
    DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀)) ⥤
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategory

/-- Derived restriction of scalars is additive: the `additive` field of a
`Deformation.ComplexLift.DerivedReduction`. -/
instance restrictionOnDerived_additive : (restrictionOnDerived.{d, d₀} f).Additive := by
  unfold restrictionOnDerived; infer_instance

/-- Derived restriction of scalars commutes with the shift: the `commShift` field of a
`Deformation.ComplexLift.DerivedReduction`. -/
noncomputable instance restrictionOnDerived_commShift :
    (restrictionOnDerived.{d, d₀} f).CommShift ℤ := by
  unfold restrictionOnDerived; infer_instance

/-! ### The adjunction -/

/-- **Extension of scalars is left adjoint to restriction of scalars** (Stacks 03CZ), at the
spelling of the underlying sheaf of rings that the lift statements of Tags 0DIY and 0DIZ are
written with. -/
noncomputable def extendRestrictAdjunction :
    extensionOfScalars f ⊣ SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f) :=
  Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction J f.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf O).property
    (Stacks.SheafOfModules.Tensor.ringSheaf O₀).property

/-- The same adjunction read on the homotopy categories of cochain complexes, which is the form
`CategoryTheory.Adjunction.derived` takes as input: the categories it localizes are the homotopy
categories. -/
noncomputable def extendRestrictAdjunctionHomotopy :
    (extensionOfScalars f).mapHomotopyCategory (ComplexShape.up ℤ) ⊣
      (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomotopyCategory
        (ComplexShape.up ℤ) :=
  (extendRestrictAdjunction f).mapHomotopyCategory (ComplexShape.up ℤ)

/-- The comparison exhibiting `Deformation.ComplexLift.restrictionOnDerived` as the right derived
functor of restriction of scalars along `Qh`. It is an isomorphism, restriction of scalars being
exact. -/
noncomputable def restrictionOnDerivedComparison :
    (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapHomotopyCategory
        (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ restrictionOnDerived.{d, d₀} f :=
  (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactorsh.inv

/-- The comparison `Deformation.ComplexLift.restrictionOnDerivedComparison` is an isomorphism. -/
instance isIso_restrictionOnDerivedComparison :
    IsIso (restrictionOnDerivedComparison.{d, d₀} f) :=
  (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactorsh.isIso_inv

/-- **Derived restriction of scalars is the right derived functor of restriction of scalars**,
with an invertible comparison: restriction of scalars is exact, so it inverts the
quasi-isomorphisms already on the homotopy category. -/
instance isRightDerivedFunctor_restrictionOnDerived :
    (restrictionOnDerived.{d, d₀} f).IsRightDerivedFunctor
      (restrictionOnDerivedComparison.{d, d₀} f)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
        (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _
    (SheafOfModules.restrictScalars.{u} (ringSheafMapOf J f)).mapDerivedCategoryFactorsh

/-- **Derived restriction of scalars is absolute**, which is the second hypothesis
`CategoryTheory.Adjunction.derived` imposes. For an exact functor this is free: the comparison is
an isomorphism, so it stays one after whiskering with any functor. -/
instance isRightDerivedFunctor_restrictionOnDerived_comp :
    (restrictionOnDerived.{d, d₀} f ⋙ derivedExtensionOfScalars.{d, d₀} f).IsRightDerivedFunctor
      (Functor.whiskerRight (restrictionOnDerivedComparison.{d, d₀} f)
          (derivedExtensionOfScalars.{d, d₀} f) ≫
        (Functor.associator DerivedCategory.Qh (restrictionOnDerived.{d, d₀} f)
          (derivedExtensionOfScalars.{d, d₀} f)).hom)
      (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
        (ComplexShape.up ℤ)) :=
  Functor.isRightDerivedFunctor_of_inverts _ _ (asIso (Functor.whiskerRight
      (restrictionOnDerivedComparison.{d, d₀} f) (derivedExtensionOfScalars.{d, d₀} f) ≫
    (Functor.associator DerivedCategory.Qh (restrictionOnDerived.{d, d₀} f)
      (derivedExtensionOfScalars.{d, d₀} f)).hom)).symm

/-- **Stacks 09T5 for change of rings on a site: the derived adjunction.** The derived base
change constructed by Stacks 0794 is left adjoint to derived restriction of scalars.

Both absoluteness hypotheses of `CategoryTheory.Adjunction.derived` are available: for the left
adjoint it is `Deformation.ComplexLift.isLeftDerivedFunctor_comp_derivedExtensionOfScalars`,
which comes from the construction by flat resolutions; for the right adjoint it is free, since
restriction of scalars is exact. -/
noncomputable def derivedAdjunction :
    derivedExtensionOfScalars.{d, d₀} f ⊣ restrictionOnDerived.{d, d₀} f :=
  haveI := isLeftDerivedFunctor_comp_derivedExtensionOfScalars.{d, d₀} f
    (restrictionOnDerived.{d, d₀} f)
  (extendRestrictAdjunctionHomotopy f).derived
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (ComplexShape.up ℤ))
    (HomotopyCategory.quasiIso (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O₀))
      (ComplexShape.up ℤ))
    (derivedExtensionOfScalarsCounitHomotopy f) (restrictionOnDerivedComparison f)

/-- **The `adjunction` field of a `Deformation.ComplexLift.DerivedReduction`, for an arbitrary
derived base change.** Any two derived base changes along `f` are canonically isomorphic, so the
adjunction above transports to the one chosen in the statements of Tags 0DIY and 0DIZ. -/
noncomputable def derivedAdjunctionOf (T : DerivedExtensionOfScalars f) :
    T.baseChange ⊣ restrictionOnDerived.{d, d₀} f :=
  (derivedAdjunction.{d, d₀} f).ofNatIsoLeft
    (DerivedExtensionOfScalars.baseChangeIso (derivedExtensionOfScalarsData.{d, d₀} f) T)

/-- The ringed site attached to a site and a sheaf of commutative rings on it: the form in which
the derived tensor product of sheaves of modules, and with it the reduction triangle of
`Stacks.Sites.idealReductionTriangle`, is stated. -/
abbrev ringedSiteOf (J : GrothendieckTopology C) (O : Sheaf J CommRingCat.{u}) :
    AlgebraicGeometry.RingedSite.{u', v', u} where
  C := C
  J := J
  O := O

omit [J.HasSheafCompose (forget₂ CommRingCat.{u} RingCat.{u})] [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasDerivedCategory.{d} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O))] in
/-- **The two conventions agree on the nose.** The category of sheaves of modules on
`Deformation.ComplexLift.ringedSiteOf J O`, over which the derived tensor product and the
reduction triangle are stated, is the category over which the lift statements of Tags 0DIY and
0DIZ are written. -/
theorem modules_ringedSiteOf :
    AlgebraicGeometry.RingedSite.Modules.{u', v', u} (ringedSiteOf J O) =
      SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  rfl

end Deformation.ComplexLift

end
