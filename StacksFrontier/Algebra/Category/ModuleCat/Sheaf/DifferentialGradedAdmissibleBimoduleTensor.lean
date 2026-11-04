module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAdmissible
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedBimoduleTensorUniversal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RelativeTensorAdditive

/-!
# The relative tensor product of an admissible short exact sequence is admissible

Let `O` be a sheaf of commutative rings on a site, let `A` and `B` be sheaves of differential
graded `O`-algebras, let `N` be a differential graded `(A, B)`-bimodule and let

`K ⟶ L ⟶ M`

be an admissible short exact sequence of right differential graded `A`-modules, that is one
which is split after the differentials are forgotten. Then

`K ⊗_A N ⟶ L ⊗_A N ⟶ M ⊗_A N`

is again admissible: the retraction and the section are morphisms of the underlying *graded*
modules, and tensoring with `N` is a functor on those, so their tensor products with the
identity of `N` split the tensored sequence.

This is the half of the exactness of `- ⊗_A N` on homotopy categories which is a splitting
statement rather than an exactness statement — admissibility asks only for a degreewise
splitting, which any additive functor of the underlying graded modules preserves. It is the
companion of `SheafOfModules.DifferentialGradedModule.GradedSplitting.pullback`, which does the
same for the pullback along a morphism of ringed sites; together the two cover the functor
`ℳ ↦ f^*ℳ ⊗_𝒜 𝒩` of [Stacks, Tag 0FTE](https://stacks.math.columbia.edu/tag/0FTE).

## Main definitions

* `SheafOfModules.RelativeTensor.gradedTensorRightMap` is the tensor product `h ⊗ 1` of a
  homomorphism of the underlying right graded modules with the identity of the bimodule, a
  homomorphism of right graded `B`-modules.
* `SheafOfModules.DifferentialGradedModule.GradedSplitting.dgTensorRight` is the tensored
  splitting.

## Main results

* `SheafOfModules.RelativeTensor.gradedTensorRightMap_id`,
  `...gradedTensorRightMap_comp` and `...gradedTensorRightMap_add`: tensoring with the bimodule
  is an additive functor of right graded modules.
* `SheafOfModules.RelativeTensor.ofDifferentialGradedMap_dgTensorRightMap`: on a morphism of
  right differential graded modules it is the tensor product functor of
  `SheafOfModules.RelativeTensor.dgTensorRightMap`.
* `SheafOfModules.DifferentialGradedModule.IsAdmissibleShortExact.dgTensorRight`: **the relative
  tensor product of an admissible short exact sequence of right differential graded `A`-modules
  with a differential graded `(A, B)`-bimodule is an admissible short exact sequence of right
  differential graded `B`-modules.**

## Implementation notes

The underlying graded module of `M ⊗_A N` is `SheafOfModules.RelativeTensor.gradedTensorRight`
on the nose, and the degreewise components of `dgTensorRightMap` are those of
`SheafOfModules.RelativeTensor.gradedTensorMapRight`, so the two readings of the tensor product
need no transport: both identifications below hold by reflexivity.

Only the right action of `B` has to be checked for `gradedTensorRightMap`, which is
`SheafOfModules.RelativeTensor.gradedTensorMapRight_smul`; the degreewise functoriality and
additivity are `gradedTensorMapRight_id`, `gradedTensorMapRight_comp` and
`gradedTensorMapRight_add`, all of which hold for an arbitrary homomorphism of the underlying
graded modules and not only for one commuting with the differentials. That is the whole reason
the argument goes through.

## References

* [Stacks Project, Tag 0FSC](https://stacks.math.columbia.edu/tag/0FSC)
* [Stacks Project, Tag 0FRS](https://stacks.math.columbia.edu/tag/0FRS)
* [Stacks Project, Tag 09JT](https://stacks.math.columbia.edu/tag/09JT)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf

universe t v u

namespace SheafOfModules

namespace RelativeTensor

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  {A B : DifferentialGradedAlgebra.{t, max u v} (toRingCat J Osharp)}
  {M M' M'' : DifferentialGradedModule.{t, max u v, max u v} A}

/-- **The tensor product `h ⊗ 1` of a homomorphism of the underlying right graded `A`-modules
with the identity of the bimodule**, a homomorphism of right graded `B`-modules. The
differentials play no part: the degreewise maps are those of `gradedTensorMapRight`, and the
only thing to check is that they commute with the right action of `B`, which acts on the
bimodule factor. -/
noncomputable def gradedTensorRightMap
    (M : DifferentialGradedModule.{t, max u v, max u v} A)
    (N : DifferentialGradedBimodule.{t, max u v, max u v} A B) (hh : gP M ⟶ gP M') :
    gradedTensorRight (gP M) N.toGradedBimodule ⟶
      gradedTensorRight (gP M') N.toGradedBimodule where
  app n := gradedTensorMapRight hh N.toGradedBimodule.toLeftGradedModule n
  map_smul n i U x y := gradedTensorMapRight_smul M N hh n i U x y

/-- The degree `n` component of `h ⊗ 1` is the degree `n` component of `gradedTensorMapRight h`. -/
@[simp]
theorem gradedTensorRightMap_app
    (M : DifferentialGradedModule.{t, max u v, max u v} A)
    (N : DifferentialGradedBimodule.{t, max u v, max u v} A B) (hh : gP M ⟶ gP M') (n : ℤ) :
    (gradedTensorRightMap M N hh).app n =
      gradedTensorMapRight hh N.toGradedBimodule.toLeftGradedModule n :=
  rfl

/-- Tensoring with the bimodule takes the identity of the underlying graded module to the
identity. -/
theorem gradedTensorRightMap_id
    (M : DifferentialGradedModule.{t, max u v, max u v} A)
    (N : DifferentialGradedBimodule.{t, max u v, max u v} A B) :
    gradedTensorRightMap M N (𝟙 (gP M)) = 𝟙 _ :=
  GradedModule.Hom.ext fun n =>
    gradedTensorMapRight_id N.toGradedBimodule.toLeftGradedModule n

/-- Tensoring with the bimodule takes a composite of homomorphisms of the underlying graded
modules to the composite. -/
theorem gradedTensorRightMap_comp
    (M : DifferentialGradedModule.{t, max u v, max u v} A)
    (N : DifferentialGradedBimodule.{t, max u v, max u v} A B)
    (hh : gP M ⟶ gP M') (hh' : gP M' ⟶ gP M'') :
    gradedTensorRightMap M N (hh ≫ hh') =
      gradedTensorRightMap M N hh ≫ gradedTensorRightMap M' N hh' :=
  GradedModule.Hom.ext fun n =>
    gradedTensorMapRight_comp N.toGradedBimodule.toLeftGradedModule hh hh' n

/-- Tensoring with the bimodule is additive in the homomorphism of the underlying graded
modules. -/
theorem gradedTensorRightMap_add
    (M : DifferentialGradedModule.{t, max u v, max u v} A)
    (N : DifferentialGradedBimodule.{t, max u v, max u v} A B) (hh hh' : gP M ⟶ gP M') :
    gradedTensorRightMap M N (hh + hh') =
      gradedTensorRightMap M N hh + gradedTensorRightMap M N hh' :=
  GradedModule.Hom.ext fun n =>
    gradedTensorMapRight_add N.toGradedBimodule.toLeftGradedModule hh hh' n

/-- **On a morphism of right differential graded modules, `h ⊗ 1` on the underlying graded
modules is the underlying graded morphism of the tensor product `h ⊗ 1` of differential graded
modules.** -/
theorem ofDifferentialGradedMap_dgTensorRightMap
    (M : DifferentialGradedModule.{t, max u v, max u v} A)
    (N : DifferentialGradedBimodule.{t, max u v, max u v} A B) (h : M ⟶ M') :
    GradedModule.ofDifferentialGradedMap (dgTensorRightMap M N h) =
      gradedTensorRightMap M N (gMap h) :=
  rfl

end RelativeTensor

namespace DifferentialGradedModule

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{t} RingCat.{t})] {Osharp : Sheaf J CommRingCat.{t}}
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v}]
  [HasWeakSheafify J AddCommGrpCat.{max u v}]
  {A B : DifferentialGradedAlgebra.{t, max u v} (toRingCat J Osharp)}
  {K L M : DifferentialGradedModule.{t, max u v, max u v} A} {f : K ⟶ L} {g : L ⟶ M}

/-- **The relative tensor product of an admissible short exact sequence with a differential
graded bimodule is admissible**: the tensor products of the retraction and of the section with
the identity of the bimodule split the tensored sequence, tensoring being an additive functor of
the underlying right graded modules. -/
noncomputable def GradedSplitting.dgTensorRight (S : GradedSplitting f g)
    (N : DifferentialGradedBimodule.{t, max u v, max u v} A B) :
    GradedSplitting (RelativeTensor.dgTensorRightMap K N f)
      (RelativeTensor.dgTensorRightMap L N g) where
  r := RelativeTensor.gradedTensorRightMap L N S.r
  s := RelativeTensor.gradedTensorRightMap M N S.s
  f_r :=
    ((RelativeTensor.gradedTensorRightMap_comp K N (RelativeTensor.gMap f) S.r).symm.trans
        (congrArg (fun hh : RelativeTensor.gP K ⟶ RelativeTensor.gP K =>
          RelativeTensor.gradedTensorRightMap K N hh) S.f_r)).trans
      (RelativeTensor.gradedTensorRightMap_id K N)
  s_g :=
    ((RelativeTensor.gradedTensorRightMap_comp M N S.s (RelativeTensor.gMap g)).symm.trans
        (congrArg (fun hh : RelativeTensor.gP M ⟶ RelativeTensor.gP M =>
          RelativeTensor.gradedTensorRightMap M N hh) S.s_g)).trans
      (RelativeTensor.gradedTensorRightMap_id M N)
  id :=
    (congrArg₂ (fun a b => a + b)
        (RelativeTensor.gradedTensorRightMap_comp L N S.r (RelativeTensor.gMap f)).symm
        (RelativeTensor.gradedTensorRightMap_comp L N (RelativeTensor.gMap g) S.s).symm).trans
      (((RelativeTensor.gradedTensorRightMap_add L N (S.r ≫ RelativeTensor.gMap f)
            (RelativeTensor.gMap g ≫ S.s)).symm.trans
          (congrArg (fun hh : RelativeTensor.gP L ⟶ RelativeTensor.gP L =>
            RelativeTensor.gradedTensorRightMap L N hh) S.id)).trans
        (RelativeTensor.gradedTensorRightMap_id L N))

/-- **The relative tensor product of an admissible short exact sequence of right differential
graded `A`-modules with a differential graded `(A, B)`-bimodule is an admissible short exact
sequence of right differential graded `B`-modules.** -/
theorem IsAdmissibleShortExact.dgTensorRight (h : IsAdmissibleShortExact f g)
    (N : DifferentialGradedBimodule.{t, max u v, max u v} A B) :
    IsAdmissibleShortExact (RelativeTensor.dgTensorRightMap K N f)
      (RelativeTensor.dgTensorRightMap L N g) :=
  Nonempty.elim h fun S => ⟨S.dgTensorRight N⟩

end DifferentialGradedModule

end SheafOfModules

end
