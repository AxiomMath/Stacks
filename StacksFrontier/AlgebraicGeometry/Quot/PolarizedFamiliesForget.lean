module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Quot.CartesianFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilies
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamilies
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Characterization
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FinitePresentationLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiSeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedTfae
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable

/-!
# Forgetting the polarization of a proper flat family (Stacks 0D3Y)

A polarized family `(X ⟶ S, ℒ)` of Stacks 0D1M is a proper, flat morphism of schemes of finite
presentation together with a relatively ample invertible module on its source. Forgetting the
module leaves a proper, flat morphism of finite presentation, and reading its source and target
as algebraic spaces over the terminal scheme presents it as an object of the category
`AlgebraicGeometry.CartesianProperFlatSpaces` of Stacks 0D1E. A morphism of polarized families is
a cartesian square, so it is carried to a strongly cartesian morphism of that category, and the
construction is the forgetful functor of Stacks 0D3Y.

The base of a polarized family is an arbitrary scheme of the site, so the ambient base of the
target category has to be a terminal scheme; `AlgebraicGeometry.integerBase` is the one the
chapter uses, and `AlgebraicGeometry.BigFppfSite.contains_integerBase` shows that every big fppf
site contains it, so no size hypothesis beyond the site itself is needed.

## Main definitions

* `AlgebraicGeometry.schemeOverIntegers`: the schemes of the site, read as schemes over the
  terminal scheme.
* `AlgebraicGeometry.forgetPolarization`: **Stacks 0D3Y**, the forgetful functor itself.

## Main results

* `AlgebraicGeometry.BigFppfSite.contains_integerBase`: every big fppf site contains the terminal
  scheme, so the absolute case of a category over the site needs no extra hypothesis.
* `AlgebraicGeometry.PolarizedFamily.contains_total`: the source of a polarized family lies in
  the site, because it is of finite type and quasi-compact over a base that does.
* `AlgebraicGeometry.Space.isQuasiCompact_yoneda_map`: the represented reading of Stacks 03HD,
  one of the ways a property of a morphism of schemes of the site transfers to the morphism of
  algebraic spaces it represents. The étale-chart way, through Stacks 04R1, is
  `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map`, proved in
  `StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Cancellation`. The third way used below,
  the represented reading of Stacks 03XD, is
  `AlgebraicGeometry.Space.universallyClosed_yoneda_map`, which is proved alongside Stacks 03XD
  itself in `StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable`.
* `AlgebraicGeometry.forgetPolarization_obj_base` and
  `AlgebraicGeometry.forgetPolarization_map_base`: the functor retains the base scheme and the
  morphism of base schemes, which is what makes it a functor over the site.

## Implementation notes

The three predicates of `AlgebraicGeometry.isProperFlatSpace` are built differently, so the image
of a polarized family is shown to satisfy them by three different routes. Flatness, being locally
of finite presentation and being locally of finite type are chart conditions in the sense of
Stacks 03MJ, so they come from `AlgebraicGeometry.Space.holdsOnEveryEtaleChart_yoneda_map` applied
to the three instances of Stacks 04R3. Quasi-compactness and universal closedness are conditions
on all base changes, so they come from the represented readings of Stacks 03HD and 03XD.
Separatedness and quasi-separatedness are conditions on the relative diagonal, and for a
represented morphism they are the corresponding conditions on the morphism of schemes by
Stacks 03KY.

In particular quasi-compactness of the represented morphism is obtained from quasi-compactness of
the morphism of schemes, which a morphism of finite presentation has by definition, rather than
from universal closedness of the morphism of algebraic spaces. Stacks 04XW — that a universally
closed morphism of algebraic spaces is quasi-compact — is therefore not needed here.

Morphisms are carried by `AlgebraicGeometry.spacesProjection_isStronglyCartesian_iff` of
Stacks 04U9: a cartesian square of schemes of the site stays cartesian after Yoneda, and the
comparison morphism into the fibre product of algebraic spaces is then an isomorphism, which is
exactly the condition defining the morphisms of `CartesianProperFlatSpaces`.

Both the object and the morphism assignment are given in term mode, with their proof obligations
split off as named results. The functor laws are equalities of morphisms of a wide subcategory of
a full subcategory of a comma category, and are proved by projecting to the underlying morphisms
of the site, which only reduce when the assignments are not built by tactic.

## References

* [Stacks Project, Tag 0D3Y](https://stacks.math.columbia.edu/tag/0D3Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### The terminal scheme as an ambient base -/

/-- Every big fppf site contains the terminal scheme `Spec (ULift ℤ)`: its size is `ℵ₀`, which is
below the cutoff of any big fppf site. -/
theorem BigFppfSite.contains_integerBase (B : BigFppfSite.{u}) : B.Contains integerBase.{u} := by
  change integerBase.{u}.size < B.cutoff
  simpa [integerBase, Scheme.size_Spec] using B.aleph0_lt_cutoff

/-- The schemes of the big fppf site of `B`, read as schemes over the terminal scheme: the
structure morphism is the unique morphism to `AlgebraicGeometry.integerBase`. -/
@[ega "I 3.3.15" "special case"]
def schemeOverIntegers (B : BigFppfSite.{u}) :
    B.Schemes ⥤ BigFppfOver B integerBase B.contains_integerBase where
  obj X := Over.mk (ObjectProperty.homMk (specULiftZIsTerminal.from X.obj))
  map f := Over.homMk f (ObjectProperty.hom_ext _ (specULiftZIsTerminal.hom_ext _ _))

/-! ### Transferring a property of schemes to the algebraic space it represents -/

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A quasi-compact morphism of schemes of the site represents a quasi-compact morphism of
algebraic spaces in the sense of Stacks 03HE.

This is the direction of `AlgebraicGeometry.Space.isQuasiCompact_of_presheaf_quasiCompact` that
needs no representability hypothesis beyond the one Yoneda supplies. -/
theorem isQuasiCompact_yoneda_map {X Y : BigFppfOver B S hS} (f : X ⟶ Y)
    (hf : QuasiCompact ((BigFppfOver.toScheme B S hS).map f)) :
    IsQuasiCompact B S hS (yoneda.map f) := by
  have := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have : (MorphismProperty.inverseImage (@QuasiCompact.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    ⟨fun hs hg => MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := @QuasiCompact) (hs.map (BigFppfOver.toScheme B S hS)) hg⟩
  exact isQuasiCompact_of_presheaf_quasiCompact B S hS (MorphismProperty.relative_map hf)

end Space

/-! ### The underlying family of algebraic spaces -/

namespace PolarizedFamily

variable {B : BigFppfSite.{u}}

/-- The source of a polarized family lies in the big fppf site: it is locally of finite type and
quasi-compact over its base, which lies in the site, so Stacks 000R, part (5) bounds its size. -/
theorem contains_total (X : PolarizedFamily B) : B.Contains X.total :=
  have := X.proper
  have := X.finitePresentation.quasiCompact
  Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact X.toBase X.base.property

/-- The source of a polarized family, as a scheme of the big fppf site. -/
def totalObj (X : PolarizedFamily B) : B.Schemes := B.obj X.contains_total

/-- The structure morphism of a polarized family, as a morphism of schemes of the site over the
terminal scheme. -/
def structureMapOverIntegers (X : PolarizedFamily B) :
    (schemeOverIntegers B).obj X.totalObj ⟶ (schemeOverIntegers B).obj X.base :=
  (schemeOverIntegers B).map (ObjectProperty.homMk X.toBase)

/-- A morphism of polarized families, as a morphism of schemes of the site over the terminal
scheme. -/
def totalMapOverIntegers {X Y : PolarizedFamily B} (f : X ⟶ Y) :
    (schemeOverIntegers B).obj X.totalObj ⟶ (schemeOverIntegers B).obj Y.totalObj :=
  (schemeOverIntegers B).map (ObjectProperty.homMk f.totalMap)

/-- The underlying morphism of schemes of `structureMapOverIntegers` is the structure morphism. -/
theorem toScheme_map_structureMapOverIntegers (X : PolarizedFamily B) :
    (BigFppfOver.toScheme B integerBase B.contains_integerBase).map
      X.structureMapOverIntegers = X.toBase :=
  rfl

/-- The square of structure morphisms of a morphism of polarized families stays cartesian in the
category of schemes of the site over the terminal scheme, because it is cartesian in schemes and
the functor to schemes is faithful. -/
theorem isPullback_totalMapOverIntegers {X Y : PolarizedFamily B} (f : X ⟶ Y) :
    IsPullback (totalMapOverIntegers f) X.structureMapOverIntegers Y.structureMapOverIntegers
      ((schemeOverIntegers B).map f.baseMap) :=
  IsPullback.of_map_of_faithful
    (BigFppfOver.toScheme B integerBase B.contains_integerBase) f.cartesian

/-- The structure morphism of a polarized family, read as a morphism of algebraic spaces over the
terminal scheme, is of finite presentation, flat and proper. -/
theorem isProperFlat_yoneda_structureMapOverIntegers (X : PolarizedFamily B) :
    Space.IsFinitePresentation B integerBase B.contains_integerBase
        (yoneda.map X.structureMapOverIntegers) ∧
      Space.IsFlat B integerBase B.contains_integerBase
        (yoneda.map X.structureMapOverIntegers) ∧
      Space.IsProper B integerBase B.contains_integerBase
        (yoneda.map X.structureMapOverIntegers) := by
  have := X.proper
  have hqc : Space.IsQuasiCompact B integerBase B.contains_integerBase
      (yoneda.map X.structureMapOverIntegers) :=
    Space.isQuasiCompact_yoneda_map B integerBase B.contains_integerBase _
      X.finitePresentation.quasiCompact
  refine ⟨⟨?_, hqc, ?_⟩, ?_, ?_, ⟨?_, hqc⟩, ?_⟩
  · exact Space.holdsOnEveryEtaleChart_yoneda_map B integerBase B.contains_integerBase
      LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget _
      X.finitePresentation.locallyOfFinitePresentation
  · rw [Space.isQuasiSeparated_iff_diagonalProp_quasiCompact B integerBase
      B.contains_integerBase (relativelyRepresentable_pullback_diagonal B integerBase
        B.contains_integerBase _ (Functor.relativelyRepresentable.map yoneda _)),
      Space.diagonalProp_quasiCompact_yoneda_map_iff]
    exact X.finitePresentation.quasiSeparated
  · exact Space.holdsOnEveryEtaleChart_yoneda_map B integerBase B.contains_integerBase
      Flat.isEtaleLocalOnSourceAndTarget _ X.flat
  · rw [Space.isSeparated_yoneda_map_iff]
    exact (inferInstance : IsSeparated X.toBase)
  · exact Space.holdsOnEveryEtaleChart_yoneda_map B integerBase B.contains_integerBase
      LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget _
      (inferInstance : LocallyOfFiniteType X.toBase)
  · exact Space.universallyClosed_yoneda_map B integerBase B.contains_integerBase _
      (inferInstance : _root_.AlgebraicGeometry.UniversallyClosed X.toBase)

end PolarizedFamily

/-! ### The forgetful functor -/

variable (B : BigFppfSite.{u})

/-- The family of algebraic spaces underlying a polarized family: its structure morphism is the
structure morphism of the family, read as a morphism of algebraic spaces over the terminal
scheme. -/
def forgetPolarizationObj (X : PolarizedFamily B) :
    CartesianProperFlatSpaces B integerBase B.contains_integerBase :=
  ⟨⟨⟨⟨yoneda.obj ((schemeOverIntegers B).obj X.totalObj),
      isAlgebraicSpace_yoneda B integerBase B.contains_integerBase _⟩,
      (schemeOverIntegers B).obj X.base, yoneda.map X.structureMapOverIntegers⟩,
    X.isProperFlat_yoneda_structureMapOverIntegers⟩⟩

/-- The morphism of families of algebraic spaces underlying a morphism of polarized families. -/
def forgetPolarizationComma {X Y : PolarizedFamily B} (f : X ⟶ Y) :
    (forgetPolarizationObj B X).obj.obj ⟶ (forgetPolarizationObj B Y).obj.obj where
  left := ObjectProperty.homMk (yoneda.map (PolarizedFamily.totalMapOverIntegers f))
  right := (schemeOverIntegers B).map f.baseMap
  w := by
    have h := congrArg yoneda.map (PolarizedFamily.isPullback_totalMapOverIntegers f).w
    rw [Functor.map_comp, Functor.map_comp] at h
    exact h

/-- The morphism of families of algebraic spaces underlying a morphism of polarized families is
strongly cartesian: by Stacks 04U9 that is the condition that the comparison morphism to the fibre
product of algebraic spaces be an isomorphism, and the comparison is the Yoneda image of the
cartesian square of structure morphisms. -/
theorem isStronglyCartesian_forgetPolarizationComma {X Y : PolarizedFamily B} (f : X ⟶ Y) :
    (spacesProjection B integerBase B.contains_integerBase).IsStronglyCartesian
      (forgetPolarizationComma B f).right (forgetPolarizationComma B f) := by
  refine (spacesProjection_isStronglyCartesian_iff (forgetPolarizationComma B f)).mpr ?_
  have hp := ((PolarizedFamily.isPullback_totalMapOverIntegers f).map yoneda).flip
  have := hp.hasPullback
  have he : pullback.lift (yoneda.map X.structureMapOverIntegers)
      (yoneda.map (PolarizedFamily.totalMapOverIntegers f)) hp.w = hp.isoPullback.hom :=
    pullback.hom_ext (by rw [pullback.lift_fst, hp.isoPullback_hom_fst])
      (by rw [pullback.lift_snd, hp.isoPullback_hom_snd])
  exact ⟨⟨ObjectProperty.homMk hp.isoPullback.inv,
    ObjectProperty.hom_ext _ (he ▸ hp.isoPullback.hom_inv_id),
    ObjectProperty.hom_ext _ (he ▸ hp.isoPullback.inv_hom_id)⟩⟩

/-- **Stacks 0D3Y.** Forget the polarization of a polarized family, keeping the finitely
presented, flat and proper family of algebraic spaces over the same base. -/
@[stacks 0D3Y "the forgetful functor"]
def forgetPolarization :
    PolarizedFamily B ⥤ CartesianProperFlatSpaces B integerBase B.contains_integerBase where
  obj := forgetPolarizationObj B
  map f := ⟨ObjectProperty.homMk (forgetPolarizationComma B f),
    isStronglyCartesian_forgetPolarizationComma B f⟩
  map_id X := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    apply CommaMorphism.ext
    · apply ObjectProperty.hom_ext
      change yoneda.map ((schemeOverIntegers B).map
        (ObjectProperty.homMk (PolarizedFamily.Hom.totalMap (𝟙 X)) :
          X.totalObj ⟶ X.totalObj)) = _
      rw [show (ObjectProperty.homMk (PolarizedFamily.Hom.totalMap (𝟙 X)) :
          X.totalObj ⟶ X.totalObj) = 𝟙 X.totalObj from
        ObjectProperty.hom_ext _ (PolarizedFamily.id_totalMap X)]
      simp only [CategoryTheory.Functor.map_id]
      rfl
    · apply Over.OverMorphism.ext
      change ((schemeOverIntegers B).map (PolarizedFamily.Hom.baseMap (𝟙 X))).left = _
      rw [PolarizedFamily.id_baseMap]
      simp only [CategoryTheory.Functor.map_id]
      rfl
  map_comp {X Y Z} f g := by
    apply WideSubcategory.hom_ext
    apply ObjectProperty.hom_ext
    apply CommaMorphism.ext
    · apply ObjectProperty.hom_ext
      change yoneda.map ((schemeOverIntegers B).map
        (ObjectProperty.homMk (PolarizedFamily.Hom.totalMap (f ≫ g)) :
          X.totalObj ⟶ Z.totalObj)) = _
      rw [show (ObjectProperty.homMk (PolarizedFamily.Hom.totalMap (f ≫ g)) :
            X.totalObj ⟶ Z.totalObj) =
          (ObjectProperty.homMk (PolarizedFamily.Hom.totalMap f) : X.totalObj ⟶ Y.totalObj) ≫
            (ObjectProperty.homMk (PolarizedFamily.Hom.totalMap g) :
              Y.totalObj ⟶ Z.totalObj) from
        ObjectProperty.hom_ext _ (PolarizedFamily.comp_totalMap f g)]
      simp only [CategoryTheory.Functor.map_comp]
      rfl
    · apply Over.OverMorphism.ext
      change ((schemeOverIntegers B).map (PolarizedFamily.Hom.baseMap (f ≫ g))).left = _
      rw [PolarizedFamily.comp_baseMap]
      simp only [CategoryTheory.Functor.map_comp]
      rfl

/-- **Stacks 0D3Y.** Forgetting the polarization keeps the base scheme, so the forgetful functor
is a functor over the big fppf site. -/
@[stacks 0D3Y "the forgetful functor is over the site"]
theorem forgetPolarization_obj_base (X : PolarizedFamily B) :
    (cartesianProperFlatProjection B integerBase B.contains_integerBase).obj
      ((forgetPolarization B).obj X) = (schemeOverIntegers B).obj X.base :=
  rfl

/-- **Stacks 0D3Y.** Forgetting the polarization keeps the morphism of base schemes. -/
@[stacks 0D3Y "the forgetful functor is over the site"]
theorem forgetPolarization_map_base {X Y : PolarizedFamily B} (f : X ⟶ Y) :
    (cartesianProperFlatProjection B integerBase B.contains_integerBase).map
      ((forgetPolarization B).map f) = (schemeOverIntegers B).map f.baseMap :=
  rfl

end AlgebraicGeometry

end
