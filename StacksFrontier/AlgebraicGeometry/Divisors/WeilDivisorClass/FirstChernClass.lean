module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleCompare
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.TensorSection
public import StacksFrontier.AlgebraicGeometry.PicardGroup.Basic

/-!
# The first Chern class of an invertible module

Let `X` be a locally Noetherian integral scheme. The Weil divisor class of an invertible sheaf
of `𝒪_X`-modules depends only on its isomorphism class, so it defines a map from the Picard
group of `X` to the Weil divisor class group `Cl(X)`. This file constructs that map and
characterizes it on the class of an invertible module.

## Main definitions

* `AlgebraicGeometry.picardRepresentative`: an invertible module representing a Picard class.
* `AlgebraicGeometry.weilDivisorClassOfPicardClass`: the map `Pic(X) → Cl(X)`.
* `AlgebraicGeometry.picardToWeilDivisorClassGroup`: the same map as a group homomorphism.

## Main results

* `AlgebraicGeometry.weilDivisorClassOfPicardClass_picardClass`: the map sends the Picard class
  of an invertible module to its Weil divisor class.

## Implementation notes

**Where the additivity comes from.** Stacks 0BE7 is the *group homomorphism* `Pic(X) → Cl(X)`,
and the source obtains it from Tag 02SL: the Weil divisor class of `L ⊗_{𝒪_X} N` is the sum of
the Weil divisor classes of `L` and `N`. That is
`AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_tensorObj`, and it is the only input the
homomorphism needs beyond what this file proves on its own: the map is well defined on
isomorphism classes, by `AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_congr`, and
`AlgebraicGeometry.weilDivisorClassOfPicardClass_picardClass` characterizes it on classes of
invertible modules.

**Which invertibility.** The Picard group is built on
`Stacks.SheafOfModules.IsInvertible` and the Weil divisor class of Tag 0BE6 on
`AlgebraicGeometry.SheafOfModules.IsInvertible`; the two are exchanged by
`Stacks.SheafOfModules.IsInvertible.toAlgebraicGeometry`, the existing bridge, and no new one
is introduced.

**Which Picard group.** The development carries three constructions of the Picard group, all
tagged 01CX. This file uses `Stacks.SheafOfModules.PicardGroup` of
`StacksFrontier/AlgebraicGeometry/PicardGroup/Basic.lean`, the only one with the class API the
construction needs: `picardClass`, `picardClass_eq_iff` — equality of classes is exactly
isomorphism, which is what well-definedness is read from — and `picardClass_tensorSheaf`.

## References

* [Stacks Project, Tag 0BE7](https://stacks.math.columbia.edu/tag/0BE7)
* [Stacks Project, Tag 02SL](https://stacks.math.columbia.edu/tag/02SL)
* [Stacks Project, Tag 0BE6](https://stacks.math.columbia.edu/tag/0BE6)
* [Stacks Project, Tag 01CX](https://stacks.math.columbia.edu/tag/01CX)
-/
@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsIntegral X] [IsLocallyNoetherian X]

/-- The abelian group structure of the Picard group of a scheme, spelled at the structure
sheaf of the scheme so that instance synthesis finds it throughout this file. -/
noncomputable local instance schemePicardGroupAddCommGroup :
    AddCommGroup (Stacks.SheafOfModules.PicardGroup X.sheaf.obj X.ringCatSheaf.property) :=
  Stacks.SheafOfModules.instAddCommGroupPicardGroup X.sheaf.obj X.ringCatSheaf.property

/-- A representative invertible module of a class in the Picard group. -/
def picardRepresentative
    (x : Stacks.SheafOfModules.PicardGroup X.sheaf.obj X.ringCatSheaf.property) :
    Stacks.SheafOfModules.InvertibleModules X.sheaf.obj X.ringCatSheaf.property :=
  (fromSkeleton _).obj
    ((Stacks.SheafOfModules.picardClassEquiv X.sheaf.obj X.ringCatSheaf.property).symm x)

omit [IsIntegral X] [IsLocallyNoetherian X] in
/-- A representative of a Picard class has that class. -/
theorem picardClass_picardRepresentative
    (x : Stacks.SheafOfModules.PicardGroup X.sheaf.obj X.ringCatSheaf.property) :
    Stacks.SheafOfModules.picardClass X.sheaf.obj X.ringCatSheaf.property
        (picardRepresentative X x).obj (picardRepresentative X x).property = x := by
  change (Stacks.SheafOfModules.picardClassEquiv X.sheaf.obj X.ringCatSheaf.property)
      (toSkeleton ((fromSkeleton
        (Stacks.SheafOfModules.InvertibleModules X.sheaf.obj X.ringCatSheaf.property)).obj
          ((Stacks.SheafOfModules.picardClassEquiv X.sheaf.obj
            X.ringCatSheaf.property).symm x))) = x
  rw [toSkeleton_fromSkeleton_obj]
  exact Equiv.apply_symm_apply _ x

/-- The Weil divisor class of a class in the Picard group: the Weil divisor class of any
invertible module representing it. -/
def weilDivisorClassOfPicardClass
    (x : Stacks.SheafOfModules.PicardGroup X.sheaf.obj X.ringCatSheaf.property) :
    weilDivisorClassGroup X :=
  haveI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (picardRepresentative X x).obj :=
    (picardRepresentative X x).property.toAlgebraicGeometry
  weilDivisorClassOfInvertibleSheaf X (picardRepresentative X x).obj

/-- The Weil divisor class of the Picard class of an invertible module is its Weil divisor
class: the construction is well defined on isomorphism classes by
`AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_congr`. -/
theorem weilDivisorClassOfPicardClass_picardClass (L : X.Modules)
    [hL : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L] :
    weilDivisorClassOfPicardClass X
        (Stacks.SheafOfModules.picardClass X.sheaf.obj X.ringCatSheaf.property L hL) =
      haveI : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
          X.ringCatSheaf.property L := hL.toAlgebraicGeometry
      weilDivisorClassOfInvertibleSheaf X L := by
  have : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L :=
    hL.toAlgebraicGeometry
  have := (picardRepresentative X (Stacks.SheafOfModules.picardClass X.sheaf.obj
    X.ringCatSheaf.property L hL)).property.toAlgebraicGeometry
  obtain ⟨e⟩ := (Stacks.SheafOfModules.picardClass_eq_iff X.sheaf.obj X.ringCatSheaf.property _ L
    (picardRepresentative X _).property hL).mp (picardClass_picardRepresentative X _)
  exact weilDivisorClassOfInvertibleSheaf_congr _ L e

/-- **Stacks 0BE7: the first Chern class.** On a locally Noetherian integral scheme the Weil
divisor class of an invertible module defines a homomorphism from the Picard group to the Weil
divisor class group. Additivity is the divisor-class additivity of Tag 02SL,
`AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_tensorObj`, and well-definedness on
isomorphism classes is `AlgebraicGeometry.weilDivisorClassOfInvertibleSheaf_congr`;
`AlgebraicGeometry.weilDivisorClassOfPicardClass_picardClass` is the characterization of this
homomorphism on the class of an invertible module. -/
@[stacks 0BE7]
def picardToWeilDivisorClassGroup :
    Stacks.SheafOfModules.PicardGroup X.sheaf.obj X.ringCatSheaf.property →+
      weilDivisorClassGroup X := by
  have hadd : ∀ (L N : X.Modules)
      [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
      [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property N]
      [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
        (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
          Presheaf.isSheaf_of_isSheaf_comp _ X.sheaf.obj (forget₂ CommRingCat RingCat)
            X.ringCatSheaf.property⟩).obj L).obj N)],
      weilDivisorClassOfInvertibleSheaf X
          (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
            Presheaf.isSheaf_of_isSheaf_comp _ X.sheaf.obj (forget₂ CommRingCat RingCat)
              X.ringCatSheaf.property⟩).obj L).obj N) =
        weilDivisorClassOfInvertibleSheaf X L + weilDivisorClassOfInvertibleSheaf X N :=
    fun L N _ _ _ => weilDivisorClassOfInvertibleSheaf_tensorObj X L N
  refine AddMonoidHom.mk' (weilDivisorClassOfPicardClass X) ?_
  intro x y
  have hP : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ X.sheaf.obj (forget₂ CommRingCat RingCat)
          X.ringCatSheaf.property⟩).obj (picardRepresentative X x).obj).obj
        (picardRepresentative X y).obj) := by
    have h1 := (picardRepresentative X x).property
    have h2 := (picardRepresentative X y).property
    exact Stacks.SheafOfModules.isInvertible_tensorSheaf _ _ _ _
  have hxy : x + y = Stacks.SheafOfModules.picardClass X.sheaf.obj X.ringCatSheaf.property
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ X.sheaf.obj (forget₂ CommRingCat RingCat)
          X.ringCatSheaf.property⟩).obj (picardRepresentative X x).obj).obj
        (picardRepresentative X y).obj) hP := by
    conv_lhs => rw [← picardClass_picardRepresentative X x,
      ← picardClass_picardRepresentative X y]
    exact Stacks.SheafOfModules.picardClass_tensorSheaf X.sheaf.obj X.ringCatSheaf.property
      (picardRepresentative X x).obj (picardRepresentative X y).obj
      (picardRepresentative X x).property (picardRepresentative X y).property hP
  refine (congrArg (weilDivisorClassOfPicardClass X) hxy).trans
    ((weilDivisorClassOfPicardClass_picardClass X
      (((Stacks.SheafOfModules.Tensor.sheafTensor ⟨X.sheaf.obj,
        Presheaf.isSheaf_of_isSheaf_comp _ X.sheaf.obj (forget₂ CommRingCat RingCat)
          X.ringCatSheaf.property⟩).obj (picardRepresentative X x).obj).obj
        (picardRepresentative X y).obj)).trans ?_)
  exact @hadd (picardRepresentative X x).obj (picardRepresentative X y).obj
    (picardRepresentative X x).property.toAlgebraicGeometry
    (picardRepresentative X y).property.toAlgebraicGeometry hP.toAlgebraicGeometry

end AlgebraicGeometry

end
