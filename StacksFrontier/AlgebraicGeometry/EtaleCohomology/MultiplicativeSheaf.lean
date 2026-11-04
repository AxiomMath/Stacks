module

public import Mathlib.Algebra.Category.Grp.EquivalenceGroupAddGroup
public import Mathlib.CategoryTheory.Abelian.FunctorCategory
public import Mathlib.CategoryTheory.Sites.Limits
public import Mathlib.CategoryTheory.Sites.SubcanonicalOver
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.Multiplicative
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Sites
public import StacksFrontier.AlgebraicGeometry.Topologies.Fpqc.Comparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The multiplicative sheaf and the sheaf of roots of unity

For a category of schemes, the functor assigning to a scheme the units of its ring of global
sections is the multiplicative sheaf `𝒪^*`, also written `𝐆_m`. Written additively it is an
abelian presheaf, which is the form needed for cohomology; its kernel under the `n`-th power
endomorphism is the sheaf of `n`-th roots of unity.

The multiplicative presheaf is a sheaf for the fpqc topology on the schemes over a base,
because it is represented by the multiplicative group scheme and the fpqc topology is
subcanonical. Restricting along a continuous inclusion then gives the sheaf property on the
small étale site.

## Main definitions

* `AlgebraicGeometry.unitsGroupPresheaf` is the group of units of global functions on each
  object of a category of schemes.
* `AlgebraicGeometry.unitsPresheaf` is the same presheaf written additively, and
  `AlgebraicGeometry.unitsSheaf` is it together with a sheaf property.
* `AlgebraicGeometry.powerPresheaf` and `AlgebraicGeometry.powerSheaf` are the `n`-th power
  endomorphism.
* `AlgebraicGeometry.rootsOfUnitySheaf` is the sheaf of `n`-th roots of unity, the kernel of
  the power endomorphism.

## Main results

* `AlgebraicGeometry.unitsPresheaf_isSheaf_smallEtale`: the multiplicative presheaf is a
  sheaf on a chosen small étale site.
* `Stacks.Sites.isSheaf_fpqcOver_globalUnits`: the units of global functions are a sheaf of
  types for the fpqc topology on the schemes over a base.  Every sheaf condition for `𝐆_m` on a
  site of schemes over the base is this one restricted along the site's canonical functor, which
  is the route [Stacks, Tag 03O4] provides.

## Implementation notes

The underlying presheaf is formed by applying global sections and then taking units. The
additive presentation has the same sections and restriction maps; it is used so that
cohomology and exact sequences live in abelian sheaves. Since the sheaf condition for a
presheaf of abelian groups is the sheaf condition for the underlying presheaf of sets, the
fpqc sheaf property is proved for the composite with the forgetful functor and transported
back.

## References

* [Stacks Project, Tag 03P4](https://stacks.math.columbia.edu/tag/03P4)
* [Stacks Project, Tag 040N](https://stacks.math.columbia.edu/tag/040N)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u v

namespace AlgebraicGeometry

/-- The multiplicative group of units of global functions on each object of a category of
schemes. This is the sheaf written `𝒪^*` or `𝐆_m` in Tag 03P4. -/
@[ega "0 5.4.7" "partial", sga "4 IX 3.0" "partial", sga "4½ Arcata 2.2.2"]
def unitsGroupPresheaf {C : Type v} [Category C]
    (F : C ⥤ Scheme.{u}) : Cᵒᵖ ⥤ CommGrpCat.{u} :=
  F.op ⋙ Scheme.Γ ⋙ forget₂ CommRingCat CommMonCat ⋙ CommMonCat.units

/-- The units functor, written additively to regard it as an abelian presheaf. -/
def unitsPresheaf {C : Type v} [Category C]
    (F : C ⥤ Scheme.{u}) : Cᵒᵖ ⥤ AddCommGrpCat.{u} :=
  unitsGroupPresheaf F ⋙ CommGrpCat.toAddCommGrp

/-- The natural `n`-th-power endomorphism of the units presheaf. -/
def powerPresheaf {C : Type v} [Category C]
    (F : C ⥤ Scheme.{u}) (n : ℕ) :
    unitsPresheaf F ⟶ unitsPresheaf F :=
  n • 𝟙 (unitsPresheaf F)

/-- The sheaf of units, from the sheaf property of the units presheaf. -/
def unitsSheaf {C : Type v} [Category C]
    (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    (h : Presheaf.IsSheaf J (unitsPresheaf F)) : Sheaf J AddCommGrpCat.{u} :=
  ⟨unitsPresheaf F, h⟩

/-- The canonical `n`-th power map on the sheaf of units. -/
def powerSheaf {C : Type v} [Category C]
    (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    (h : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ) :
    unitsSheaf J F h ⟶ unitsSheaf J F h :=
  ObjectProperty.homMk (powerPresheaf F n)

/-- The sheaf of `n`-th roots of unity, canonically the kernel of the `n`-th power map on
the sheaf of units. -/
@[sga "4 IX 3.0", sga "4½ Arcata 2.2.4", sga "5 VI 3.2"]
def rootsOfUnitySheaf {C : Type v} [Category C]
    (J : GrothendieckTopology C) (F : C ⥤ Scheme.{u})
    (h : Presheaf.IsSheaf J (unitsPresheaf F)) (n : ℕ) :
    Sheaf J AddCommGrpCat.{u} :=
  Limits.kernel (powerSheaf J F h n)

/-- The units in global sections form a sheaf for the fpqc topology on the schemes over a
base: the functor is represented by the multiplicative group scheme over the base, and the
fpqc topology is subcanonical. -/
@[sga "4 IX 3.0" "partial", sga "4½ Arcata 2.2.2" "more general"]
private theorem unitsPresheaf_isSheaf_fpqc (S : Scheme.{u}) :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S)
      (unitsPresheaf (Over.forget S) ⋙ CategoryTheory.forget AddCommGrpCat) := by
  let X : Over S := Scheme.asOver (multiplicativeGroupBaseChange S) S
  have hYon : Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (yoneda.obj X) :=
    (CategoryTheory.isSheaf_iff_isSheaf_of_type (J := Scheme.fpqcTopology.over S)
      (yoneda.obj X)).2 <|
        CategoryTheory.GrothendieckTopology.Subcanonical.isSheaf_of_isRepresentable
          (J := Scheme.fpqcTopology.over S) (yoneda.obj X)
  have eYon : yoneda.obj X ≅
      (CategoryTheory.yonedaGrpObj X) ⋙ CategoryTheory.forget GrpCat := by
    refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
    intro Y Z f
    ext g
    rfl
  have eUnits : globalUnits S ⋙ CategoryTheory.forget GrpCat ≅
      unitsPresheaf (Over.forget S) ⋙ CategoryTheory.forget AddCommGrpCat := by
    refine NatIso.ofComponents (fun _ => Iso.refl _) ?_
    intro Y Z f
    ext g
    rfl
  exact (Presheaf.isSheaf_of_iso_iff eUnits).mp <|
    (Presheaf.isSheaf_of_iso_iff (Functor.isoWhiskerRight (baseChangePointsIsoGlobalUnits S)
      (CategoryTheory.forget GrpCat))).mp <| (Presheaf.isSheaf_of_iso_iff eYon).mp hYon

/-- The units in global sections form a sheaf on a chosen small étale site: the fpqc sheaf
property restricts along the continuous inclusion of the small étale site into the schemes
over the base. -/
theorem unitsPresheaf_isSheaf_smallEtale
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    Presheaf.IsSheaf (SmallEtale.topology B S hS)
      (unitsPresheaf (SmallEtale.toScheme B S hS)) :=
  Presheaf.isSheaf_of_isSheaf_comp _ _ (CategoryTheory.forget AddCommGrpCat) <|
    isSheaf_chosenSmallEtale_of_isSheaf_fpqc B S hS
      (unitsPresheaf (Over.forget S) ⋙ CategoryTheory.forget AddCommGrpCat)
      (unitsPresheaf_isSheaf_fpqc S)

end AlgebraicGeometry

namespace Stacks.Sites

open AlgebraicGeometry

variable (S : Scheme.{u})

/-- The presheaf of types of invertible global functions on the schemes over `S`.  It is the
underlying presheaf of types of `𝐆_m` on the schemes over `S`. -/
abbrev globalUnitsOver : (Over S)ᵒᵖ ⥤ Type u :=
  unitsPresheaf (Over.forget S) ⋙ CategoryTheory.forget AddCommGrpCat

/-- Invertible global functions on the schemes over `S` are a sheaf of types for the fpqc
topology induced on `Over S`: the functor is represented by the multiplicative group scheme
over `S`, and the fpqc topology is subcanonical. -/
@[sga "4 IX 3.0" "partial", sga "4½ Arcata 2.2.2" "more general"]
theorem isSheaf_fpqcOver_globalUnits :
    Presheaf.IsSheaf (Scheme.fpqcTopology.over S) (globalUnitsOver S) :=
  unitsPresheaf_isSheaf_fpqc S

end Stacks.Sites

end
