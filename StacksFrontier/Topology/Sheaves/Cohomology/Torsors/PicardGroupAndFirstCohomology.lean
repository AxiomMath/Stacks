module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.Picard
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorPowerCoherence
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.GlobalGeneratorsAndTriviality
public import StacksFrontier.Topology.Sheaves.Cohomology.Torsors.TensorOfGeneratorTorsors
import StacksCore.Tactic.EgaSgaAttribute

/-!
# First cohomology of the sheaf of units and the Picard group

Let `(X, 𝒪_X)` be a ringed space all of whose stalks `𝒪_{X, x}` are local rings.  Sending an
invertible `𝒪_X`-module to the torsor of its trivializing sections is an isomorphism of abelian
groups from the Picard group of `X` onto the group of isomorphism classes of torsors under the
sheaf of units `𝒪_X^*`, hence onto `H^1(X, 𝒪_X^*)`.

## Main definitions

* `Stacks.Cohomology.Generators.generatorTorsorClassOfPicard`: the generator-torsor class of a
  Picard class.
* `Stacks.Cohomology.Generators.generatorTorsorClassAddEquiv`: the resulting isomorphism of
  abelian groups between the Picard group and the group of torsor classes.
* `Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup`: the canonical isomorphism
  `H^1(X, 𝒪_X^*) ≅ Pic(X)`.

## Main results

* `Stacks.Cohomology.Generators.generatorTorsorClassOfPicard_classOf`: the isomorphism sends
  the class of `L` to the class of the generator torsor of `L`.
* `Stacks.Cohomology.Generators.generatorTorsorClassOfPicard_add`: it is additive.
* `Stacks.Cohomology.Generators.generatorTorsorClassOfPicard_surjective` and
  `Stacks.Cohomology.Generators.generatorTorsorClassOfPicard_eq_zero`: it is surjective and has
  trivial kernel.
* `Stacks.Cohomology.Generators.h1UnitsAddEquivPicardGroup_symm_classOf`: the inverse isomorphism
  sends the class of `L` to the first-cohomology class of the generator torsor of `L`.

## Implementation notes

The Picard group used is `Stacks.SheafOfModules.Picard.PicardGroup`, the small model of the
skeleton of the category of invertible modules, whose carrier lies in the universe of the
sections, so that the isomorphism with `Stacks.Cohomology.SheafTorsor.sheafCohomologyOne` can be
stated.  A Picard class is sent to the generator-torsor class of the chosen representative of its
skeleton class.

## References

* [Stacks Project, Tag 09NU](https://stacks.math.columbia.edu/tag/09NU)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
* [Stacks Project, Tag 02FQ](https://stacks.math.columbia.edu/tag/02FQ)
* [Stacks Project, Tag 01CT](https://stacks.math.columbia.edu/tag/01CT)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Cohomology.Generators

variable (X : RingedSpace.{u, u})

/-- The abelian group structure on the Picard group of a ringed space.  It is
`Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup`, named here because instance search
does not find that instance through the universe constraints of a ringed space. -/
local instance picardGroupAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :=
  Stacks.SheafOfModules.Picard.instAddCommGroupPicardGroup X.sheaf.obj
    (structureSheaf X.sheaf).property

/-- The tensor product of two invertible modules on a ringed space is invertible. -/
theorem isInvertible_tensorSheaf_of_isInvertible (L N : SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L)
    (hN : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property N) :
    Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N))) := by
  have := hL
  have := hN
  exact Stacks.SheafOfModules.isInvertible_tensorSheaf X.sheaf.obj
    (structureSheaf X.sheaf).property L N

/-- The class of the structure sheaf in the Picard group is zero. -/
theorem picardClassOf_unit_eq_zero :
    Stacks.SheafOfModules.Picard.classOf X.sheaf.obj (structureSheaf X.sheaf).property
      (SheafOfModules.unit (structureSheaf X.sheaf))
      (isInvertible_unit_structureSheaf X) = 0 := by
  set hU := isInvertible_unit_structureSheaf X with hUdef
  set a := Stacks.SheafOfModules.Picard.classOf X.sheaf.obj (structureSheaf X.sheaf).property
    (SheafOfModules.unit (structureSheaf X.sheaf)) hU with hadef
  have hUU := isInvertible_tensorSheaf_of_isInvertible X
    (SheafOfModules.unit (structureSheaf X.sheaf))
    (SheafOfModules.unit (structureSheaf X.sheaf)) hU hU
  have ha : a + a = a := by
    refine (Stacks.SheafOfModules.Picard.classOf_tensor X.sheaf.obj
      (structureSheaf X.sheaf).property _ _ hU hU hUU).trans ?_
    refine (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff X.sheaf.obj
      (structureSheaf X.sheaf).property _ _ hUU hU).2 ?_
    exact ⟨Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.sheaf.obj
      (structureSheaf X.sheaf).property (SheafOfModules.unit (structureSheaf X.sheaf))⟩
  exact add_right_cancel (ha.trans (zero_add a).symm)

/-- The class of the chosen representative of a Picard class is that Picard class. -/
private theorem classOf_fromSkeleton_classEquiv_symm
    (p : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    Stacks.SheafOfModules.Picard.classOf X.sheaf.obj (structureSheaf X.sheaf).property
      ((fromSkeleton (Stacks.SheafOfModules.InvertibleModules X.sheaf.obj
        (structureSheaf X.sheaf).property)).obj
          ((Stacks.SheafOfModules.Picard.picardGroupData X.sheaf.obj
            (structureSheaf X.sheaf).property).classEquiv.symm p)).obj
      ((fromSkeleton (Stacks.SheafOfModules.InvertibleModules X.sheaf.obj
        (structureSheaf X.sheaf).property)).obj
          ((Stacks.SheafOfModules.Picard.picardGroupData X.sheaf.obj
            (structureSheaf X.sheaf).property).classEquiv.symm p)).property = p := by
  change (Stacks.SheafOfModules.Picard.picardGroupData X.sheaf.obj
    (structureSheaf X.sheaf).property).classEquiv (toSkeleton _) = p
  rw [toSkeleton_fromSkeleton_obj]
  exact (Stacks.SheafOfModules.Picard.picardGroupData X.sheaf.obj
    (structureSheaf X.sheaf).property).classEquiv.apply_symm_apply p

variable [∀ x : X, IsLocalRing (X.presheaf.stalk x)]

/-- The generator-torsor class of a Picard class: the class of the generator torsor of the
chosen representative of the corresponding isomorphism class of invertible modules. -/
def generatorTorsorClassOfPicard
    (p : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    Stacks.Cohomology.SheafTorsor.TorsorClass X (unitsSheaf X) :=
  generatorTorsorClassOfInvertible X
    ((fromSkeleton (Stacks.SheafOfModules.InvertibleModules X.sheaf.obj
      (structureSheaf X.sheaf).property)).obj
        ((Stacks.SheafOfModules.Picard.picardGroupData X.sheaf.obj
          (structureSheaf X.sheaf).property).classEquiv.symm p)).obj
    ((fromSkeleton (Stacks.SheafOfModules.InvertibleModules X.sheaf.obj
      (structureSheaf X.sheaf).property)).obj
        ((Stacks.SheafOfModules.Picard.picardGroupData X.sheaf.obj
          (structureSheaf X.sheaf).property).classEquiv.symm p)).property

/-- The chosen representative of a Picard class has the generator-torsor class of every
representative. -/
theorem generatorTorsorClassOfPicard_classOf (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (structureSheaf X.sheaf).property L) :
    generatorTorsorClassOfPicard X (Stacks.SheafOfModules.Picard.classOf X.sheaf.obj
        (structureSheaf X.sheaf).property L hL) =
      generatorTorsorClassOfInvertible X L hL := by
  set S := Stacks.SheafOfModules.InvertibleModules X.sheaf.obj
    (structureSheaf X.sheaf).property with hS
  set d := Stacks.SheafOfModules.Picard.picardGroupData X.sheaf.obj
    (structureSheaf X.sheaf).property with hd
  set M := (fromSkeleton S).obj (d.classEquiv.symm
    (Stacks.SheafOfModules.Picard.classOf X.sheaf.obj
      (structureSheaf X.sheaf).property L hL)) with hM
  have hsk : toSkeleton M = toSkeleton (C := S) ⟨L, hL⟩ := by
    refine d.classEquiv.injective ?_
    rw [hM, toSkeleton_fromSkeleton_obj]
    exact d.classEquiv.apply_symm_apply _
  obtain ⟨e⟩ := toSkeleton_eq_toSkeleton_iff.mp hsk
  exact generatorTorsorClassOfInvertible_eq_of_iso X M.property hL
    ((ObjectProperty.ι _).mapIso e)

/-- Every class of a torsor under the sheaf of units comes from a Picard class. -/
theorem generatorTorsorClassOfPicard_surjective :
    Function.Surjective (generatorTorsorClassOfPicard X) := by
  intro c
  obtain ⟨L, hL, hLc⟩ := exists_generatorTorsorClassOfInvertible_eq X c
  exact ⟨Stacks.SheafOfModules.Picard.classOf X.sheaf.obj (structureSheaf X.sheaf).property L hL,
    (generatorTorsorClassOfPicard_classOf X L hL).trans hLc⟩

/-- The generator-torsor class of a tensor product is the sum of the generator-torsor
classes. -/
theorem generatorTorsorClassOfInvertible_tensorSheaf
    (L N : SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property L)
    (hN : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property N)
    (hLN : Stacks.SheafOfModules.IsInvertible X.sheaf.obj (structureSheaf X.sheaf).property
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N)))) :
    generatorTorsorClassOfInvertible X
        ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
          ((X)).IsSheaf⟩).obj (L)).obj (N))) hLN =
      generatorTorsorClassOfInvertible X L hL + generatorTorsorClassOfInvertible X N hN := by
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible X L hL
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible X N hN
  have := isFiniteLocallyFreeOfRank_one_of_isInvertible X
    ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
      ((X)).IsSheaf⟩).obj (L)).obj (N))) hLN
  exact Stacks.Cohomology.SheafTorsor.torsorClass_eq_add_of_pairing X (unitsSheaf X)
    (generatorTorsor X L).toTorsor (generatorTorsor X N).toTorsor
    (generatorTorsor X
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (L)).obj (N)))).toTorsor
    (generatorTorsorTensorPairing X L N)

/-- The generator-torsor class of a Picard class is additive. -/
theorem generatorTorsorClassOfPicard_add
    (p q : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property) :
    generatorTorsorClassOfPicard X (p + q) =
      generatorTorsorClassOfPicard X p + generatorTorsorClassOfPicard X q := by
  set S := Stacks.SheafOfModules.InvertibleModules X.sheaf.obj
    (structureSheaf X.sheaf).property with hS
  set d := Stacks.SheafOfModules.Picard.picardGroupData X.sheaf.obj
    (structureSheaf X.sheaf).property with hd
  set M := (fromSkeleton S).obj (d.classEquiv.symm p) with hM
  set N := (fromSkeleton S).obj (d.classEquiv.symm q) with hN
  have hp : Stacks.SheafOfModules.Picard.classOf X.sheaf.obj (structureSheaf X.sheaf).property
      M.obj M.property = p := by
    exact classOf_fromSkeleton_classEquiv_symm X p
  have hq : Stacks.SheafOfModules.Picard.classOf X.sheaf.obj (structureSheaf X.sheaf).property
      N.obj N.property = q := by
    exact classOf_fromSkeleton_classEquiv_symm X q
  have hMN := isInvertible_tensorSheaf_of_isInvertible X M.obj N.obj M.property N.property
  have hsum : p + q = Stacks.SheafOfModules.Picard.classOf X.sheaf.obj
      (structureSheaf X.sheaf).property
      ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
        ((X)).IsSheaf⟩).obj (M.obj)).obj (N.obj))) hMN := by
    rw [← hp, ← hq]
    exact Stacks.SheafOfModules.Picard.classOf_tensor X.sheaf.obj
      (structureSheaf X.sheaf).property M.obj N.obj M.property N.property hMN
  calc generatorTorsorClassOfPicard X (p + q)
      = generatorTorsorClassOfPicard X (Stacks.SheafOfModules.Picard.classOf X.sheaf.obj
          (structureSheaf X.sheaf).property
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
            ((X)).IsSheaf⟩).obj (M.obj)).obj (N.obj))) hMN) :=
        congrArg (generatorTorsorClassOfPicard X) hsum
    _ = generatorTorsorClassOfInvertible X
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X)).presheaf,
            ((X)).IsSheaf⟩).obj (M.obj)).obj (N.obj))) hMN :=
        generatorTorsorClassOfPicard_classOf X _ hMN
    _ = generatorTorsorClassOfInvertible X M.obj M.property +
          generatorTorsorClassOfInvertible X N.obj N.property :=
        generatorTorsorClassOfInvertible_tensorSheaf X M.obj N.obj M.property N.property hMN
    _ = generatorTorsorClassOfPicard X p + generatorTorsorClassOfPicard X q :=
        congrArg₂ (fun a b => a + b)
          ((generatorTorsorClassOfPicard_classOf X M.obj M.property).symm.trans
            (congrArg (generatorTorsorClassOfPicard X) hp))
          ((generatorTorsorClassOfPicard_classOf X N.obj N.property).symm.trans
            (congrArg (generatorTorsorClassOfPicard X) hq))

/-- A Picard class whose generator-torsor class vanishes is zero. -/
theorem generatorTorsorClassOfPicard_eq_zero
    (p : Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
      (structureSheaf X.sheaf).property)
    (hp : generatorTorsorClassOfPicard X p = 0) : p = 0 := by
  set S := Stacks.SheafOfModules.InvertibleModules X.sheaf.obj
    (structureSheaf X.sheaf).property with hS
  set d := Stacks.SheafOfModules.Picard.picardGroupData X.sheaf.obj
    (structureSheaf X.sheaf).property with hd
  set M := (fromSkeleton S).obj (d.classEquiv.symm p) with hM
  have hpM : Stacks.SheafOfModules.Picard.classOf X.sheaf.obj (structureSheaf X.sheaf).property
      M.obj M.property = p := by
    exact classOf_fromSkeleton_classEquiv_symm X p
  have hzero : generatorTorsorClassOfInvertible X M.obj M.property = 0 := by
    rwa [← generatorTorsorClassOfPicard_classOf X M.obj M.property, hpM]
  obtain ⟨e⟩ := nonempty_iso_unit_of_class_eq_zero X M.obj M.property hzero
  have hcl := (Stacks.SheafOfModules.Picard.classOf_eq_classOf_iff X.sheaf.obj
    (structureSheaf X.sheaf).property M.obj (SheafOfModules.unit (structureSheaf X.sheaf))
    M.property (isInvertible_unit_structureSheaf X)).2 ⟨e.symm⟩
  rwa [hpM, picardClassOf_unit_eq_zero] at hcl

/-- The generator-torsor class as a homomorphism of abelian groups. -/
def generatorTorsorClassHom :
    Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj (structureSheaf X.sheaf).property →+
      Stacks.Cohomology.SheafTorsor.TorsorClass X (unitsSheaf X) where
  toFun := generatorTorsorClassOfPicard X
  map_zero' := by
    rw [← picardClassOf_unit_eq_zero X, generatorTorsorClassOfPicard_classOf]
    exact generatorTorsorClassOfInvertible_unit X
  map_add' := generatorTorsorClassOfPicard_add X

/-- The Picard group is isomorphic, as an abelian group, to the group of isomorphism classes
of torsors under the sheaf of units. -/
def generatorTorsorClassAddEquiv :
    Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj (structureSheaf X.sheaf).property ≃+
      Stacks.Cohomology.SheafTorsor.TorsorClass X (unitsSheaf X) :=
  AddEquiv.ofBijective (generatorTorsorClassHom X) (by
    refine ⟨fun p q hpq => ?_, generatorTorsorClassOfPicard_surjective X⟩
    have hsub : generatorTorsorClassOfPicard X (p - q) = 0 := by
      have h := (generatorTorsorClassHom X).map_sub p q
      rwa [hpq, sub_self] at h
    exact sub_eq_zero.mp (generatorTorsorClassOfPicard_eq_zero X (p - q) hsub))

/-- For a ringed space all of whose stalks are local rings, the first cohomology of the sheaf of
units is canonically isomorphic, as an abelian group, to the Picard group. -/
@[stacks 09NU "the additive equivalence",
  sga "4½ Arcata 2.2.3" "ringed space case",
  ega "0 5.4.7" "special case",
  ega "IV 21.3.6" "special case",
  sga "1 XI 6.4" "more general",
  sga "3 VIII 4.4" "Pic(S) ≅ H¹(S, O_S^×)"]
def h1UnitsAddEquivPicardGroup :
    Stacks.Cohomology.SheafTorsor.sheafCohomologyOne X (unitsSheaf X) ≃+
      Stacks.SheafOfModules.Picard.PicardGroup X.sheaf.obj
        (structureSheaf X.sheaf).property :=
  (Stacks.Cohomology.SheafTorsor.torsorClassAddEquivSheafCohomologyOne X
    (unitsSheaf X)).symm.trans (generatorTorsorClassAddEquiv X).symm

/-- The inverse of the canonical isomorphism `H^1(X, 𝒪_X^*) ≅ Pic(X)` sends the class of an
invertible module to the first-cohomology class of its torsor of generators. -/
@[stacks 09NU "characterization by generator torsors"]
theorem h1UnitsAddEquivPicardGroup_symm_classOf
    (L : SheafOfModules.{u} (structureSheaf X.sheaf))
    (hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj
      (structureSheaf X.sheaf).property L) :
    (h1UnitsAddEquivPicardGroup X).symm (Stacks.SheafOfModules.Picard.classOf X.sheaf.obj
        (structureSheaf X.sheaf).property L hL) =
      Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne X (unitsSheaf X)
        (Quotient.mk _ (generatorTorsorOfInvertible X L hL).toTorsor) := by
  show Stacks.Cohomology.SheafTorsor.torsorClassEquivSheafCohomologyOne X (unitsSheaf X)
      (generatorTorsorClassOfPicard X (Stacks.SheafOfModules.Picard.classOf X.sheaf.obj
        (structureSheaf X.sheaf).property L hL)) = _
  rw [generatorTorsorClassOfPicard_classOf]
  rfl

end Stacks.Cohomology.Generators

end
