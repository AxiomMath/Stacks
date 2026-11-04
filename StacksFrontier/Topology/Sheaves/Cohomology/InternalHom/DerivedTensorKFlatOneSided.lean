module

public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorCoproducts
public import StacksFrontier.Topology.Sheaves.Cohomology.InternalHom.DerivedTensorFlatVanishing

/-!
# The K-flat comparison with only one K-flat argument

Let `A` be a monoidal abelian category in which every complex receives a quasi-isomorphism from
a K-flat one, so that `D(A)` carries the derived tensor product.  The comparison recorded by
`CochainComplex.KFlatMonoidal.derivedTensorIso` identifies `Q(K) ⊗^L Q(L)` with `Q(K ⊗ L)` when
*both* `K` and `L` are K-flat.  Mathematically one K-flat argument suffices: if `P` is K-flat
then `P ⊗ -` preserves quasi-isomorphisms, so `Q(P ⊗ -)` already descends to `D(A)` and the
descent is `Q(P) ⊗^L -`.  That is what this file records, as
`CochainComplex.KFlatMonoidal.derivedTensorLeftKFlatIso`.

Nothing new is proved to get it: the descent and its identification with tensoring are
`CochainComplex.KFlatMonoidal.derivedTensorLeftLift` and `derivedTensorLeftLiftIso`, which
`StacksFrontier/Topology/Sheaves/Cohomology/InternalHom/DerivedTensorCoproducts.lean` built for the
preservation of direct sums, and the value of the descent at `Q(K)` is read off the `Lifting`
datum that defines it.  The comparison here is the composite of those two with the bridge
`quotient ⋙ Qh ≅ Q`.

## The consequence this file exists for

Half of the flatness in
`Stacks.SheafOfModules.DerivedMonoidal.isZero_derivedTensorSingle_of_isZero_tensorObj` is an
artefact of the two-sided comparison.  The vanishing of the *total* tensor product of two modules
placed in degree zero needs no flatness at all
(`Stacks.SheafOfModules.DerivedMonoidal.isZero_tensorObj_single_of_isZero`); flatness entered
only to make the comparison applicable to both arguments.  With the one-sided comparison the
second module's flatness is no longer used, which is
`isZero_derivedTensorSingle_of_isZero_tensorObj_left` and, on a ringed space,
`Stacks.Cohomology.MonoidalDerived.isZero_derivedTensor_of_isZero_tensor_of_isFlat_left`.

## Main definitions

* `CochainComplex.KFlatMonoidal.derivedTensorLeftKFlatIso`: **`Q(P) ⊗^L Q(K) ≅ Q(P ⊗ K)` for `P`
  K-flat and `K` arbitrary.**

## Main results

* `CategoryTheory.Limits.isZero_of_retract`: a retract of a zero object is a zero object.
* `Stacks.Cohomology.MonoidalDerived.isZero_tensorObj_of_isZero_left` and
  `isZero_tensorObj_of_isZero_right`: a zero object of `D(𝒪_X)` tensored with anything is a zero
  object.  `MonoidalPreadditive (DerivedModules X.sheaf)` is *not* synthesizable, so this goes
  through the preservation of empty direct sums instead.
* `CochainComplex.KFlatMonoidal.isZero_derivedTensor_of_isZero_of_kFlat_left` and
  `isZero_derivedTensor_of_isZero_of_kFlat_right`: if the total tensor product of a K-flat
  complex with an arbitrary one is a zero object then so is their derived tensor product, in
  either order.
* `Stacks.SheafOfModules.DerivedMonoidal.isZero_derivedTensorSingle_of_isZero_tensorObj_left`:
  on a ringed site, two modules in degree zero with vanishing tensor product have vanishing
  derived tensor product as soon as the *first* is flat.
* `Stacks.Cohomology.MonoidalDerived.isZero_derivedTensor_of_isZero_tensor_of_isFlat_left`: the
  same on a ringed space, for the derived tensor product of Stacks 0FPB.

## Implementation notes

`CochainComplex.KFlatMonoidal.derivedTensorLeftLiftIso` is stated with the K-flat complex read
as an object of the full subcategory of K-flat objects of `K(A)`, and
`CochainComplex.KFlatMonoidal.kFlatQ` of that object is `DerivedCategory.Qh` of the homotopy
class, definitionally.  The bridge to `DerivedCategory.Q` is
`CochainComplex.KFlatMonoidal.derivedQIso`, exactly as in the construction of
`derivedTensorIso`.  All three steps are object-level identifications inside a tensor product,
so no transport is paid.

The right-hand statements are obtained from the left-hand ones with the braiding of `Comp(A)`
and of `D(A)`, not by repeating the descent in the other variable.

Nothing in this file is a clause of a Stacks tag.  The one-sided comparison is a step of the
proof of the implication `(2) ⟹ (1)` of Stacks 0FPG: it is what kills the off-diagonal terms of
the assembly without assuming the two invertible modules flat over `𝒪_X`.  No declaration
carries the project tag, and the four existing attribute sites of Tag 0FPG are untouched.

## References

* [Stacks Project, Tag 06YN](https://stacks.math.columbia.edu/tag/06YN) — K-flat complexes and
  the fact that tensoring with one preserves quasi-isomorphisms.
* [Stacks Project, Tag 0FPB](https://stacks.math.columbia.edu/tag/0FPB) — the derived tensor
  product on `D(𝒪_X)`.
* [Stacks Project, Tag 0FPG](https://stacks.math.columbia.edu/tag/0FPG) — the implication
  `(2) ⟹ (1)`, whose assembly consumes the one-sided comparison.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Localization

universe w v u d

namespace CategoryTheory.Limits

/-- **A retract of a zero object is a zero object.**  The identity of the retract factors through
the zero object, so it is the zero morphism.

The same statement is a private lemma of
`StacksFrontier/CategoryTheory/Triangulated/Quotient.lean`, where it is used to show that the
property of becoming zero in a quotient is stable under retracts; it is stated publicly here
because it is what turns a retract of an off-diagonal term into the vanishing of that term. -/
theorem isZero_of_retract {C : Type*} [Category* C] [Limits.HasZeroMorphisms C] {A B : C}
    (ret : Retract A B) (hB : IsZero B) : IsZero A := by
  rw [IsZero.iff_id_eq_zero, ← ret.retract, hB.eq_zero_of_tgt ret.i, zero_comp]

end CategoryTheory.Limits

namespace CochainComplex.KFlatMonoidal

open CochainComplex.KFlatBifunctor

variable (A : Type u) [Category.{v} A] [Abelian A] [MonoidalCategory A]
  [(curriedTensor A).Additive] [∀ X : A, ((curriedTensor A).obj X).Additive]
  [∀ (X₁ X₂ : GradedObject ℤ A), GradedObject.HasTensor X₁ X₂]
  [∀ X₁ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).obj X₁)]
  [∀ X₂ : A, PreservesColimit (Functor.empty.{0} A) ((curriedTensor A).flip.obj X₂)]
  [∀ X₁ X₂ X₃ X₄ : GradedObject ℤ A, GradedObject.HasTensor₄ObjExt X₁ X₂ X₃ X₄]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensor₁₂Tensor X₁ X₂ X₃]
  [∀ X₁ X₂ X₃ : GradedObject ℤ A, GradedObject.HasGoodTensorTensor₂₃ X₁ X₂ X₃]

attribute [local instance] homotopyMonoidal homotopyBraided

section Braided

variable [HasDerivedCategory.{w} A] [BraidedCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)

include hres in
/-- **The K-flat comparison with only the first argument K-flat**: for `P` K-flat and `K`
arbitrary, `Q(P) ⊗^L Q(K) ≅ Q(P ⊗ K)`.

The three factors are: the bridge `quotient ⋙ Qh ≅ Q` at `P`, tensored on the right with `Q(K)`;
`derivedTensorLeftLiftIso`, which identifies the descent of `Q(P ⊗ -)` with `Q(P) ⊗^L -`, at
`Q(K)`; and the `Lifting` datum of that descent at `K`, which says its value at `Q(K)` is
`Q(P ⊗ K)`.

This is `derivedTensorIso` with the K-flatness of the second argument removed, which is what the
mathematics asks for: a K-flat complex tensored with a quasi-isomorphism is a
quasi-isomorphism, so no condition on the second argument is needed.

A step of the proof of an implication of Stacks 0FPG, not a clause of it, so it carries no
`@[stacks]` attribute. -/
def derivedTensorLeftKFlatIso {P : CochainComplex A ℤ}
    (hP : CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P) (K : CochainComplex A ℤ) :
    letI := derivedMonoidal A hres
    DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj K ≅ DerivedCategory.Q.obj (P ⊗ K) :=
  letI := kFlatQ_isLocalization (curriedTensor A) hres
  letI := derivedMonoidal A hres
  ((derivedLocalizedTensor A).mapIso (derivedQIso A P)).symm.app (DerivedCategory.Q.obj K) ≪≫
    (derivedTensorLeftLiftIso A hP).symm.app (DerivedCategory.Q.obj K) ≪≫
      (Localization.Lifting.iso (DerivedCategory.Q (C := A))
        (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
        (tensorLeft P ⋙ DerivedCategory.Q) (derivedTensorLeftLift A hP)).app K

include hres in
/-- **A K-flat complex whose total tensor product with an arbitrary complex is a zero object has
vanishing derived tensor product with it.**  `Q` carries a zero object to a zero object, and
`derivedTensorLeftKFlatIso` identifies the derived tensor product with its image. -/
theorem isZero_derivedTensor_of_isZero_of_kFlat_left {P K : CochainComplex A ℤ}
    (hP : CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P)
    (hz : IsZero (P ⊗ K)) :
    letI := derivedMonoidal A hres
    IsZero (DerivedCategory.Q.obj P ⊗ DerivedCategory.Q.obj K) :=
  let := derivedMonoidal A hres
  (Functor.map_isZero DerivedCategory.Q hz).of_iso
    (derivedTensorLeftKFlatIso A hres hP K)

end Braided

section Symmetric

variable [HasDerivedCategory.{w} A] [SymmetricCategory (CochainComplex A ℤ)]
  (hres : ∀ G : CochainComplex A ℤ, ∃ (P : CochainComplex A ℤ) (f : P ⟶ G),
      CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P ∧ QuasiIso f)

include hres in
/-- **The same with the K-flat complex on the right.**  The braiding of `Comp(A)` turns the
hypothesis into the one of `isZero_derivedTensor_of_isZero_of_kFlat_left` and the braiding of
`D(A)` turns that statement's conclusion into this one; the descent is not repeated. -/
theorem isZero_derivedTensor_of_isZero_of_kFlat_right {P K : CochainComplex A ℤ}
    (hP : CochainComplex.KFlatBifunctor.KFlat (curriedTensor A) P)
    (hz : IsZero (K ⊗ P)) :
    letI := derivedMonoidal A hres
    letI := derivedSymmetric A hres
    IsZero (DerivedCategory.Q.obj K ⊗ DerivedCategory.Q.obj P) :=
  let := derivedMonoidal A hres
  let := derivedSymmetric A hres
  (isZero_derivedTensor_of_isZero_of_kFlat_left A hres hP (hz.of_iso (β_ P K))).of_iso
    (β_ (DerivedCategory.Q.obj K) (DerivedCategory.Q.obj P))

end Symmetric

end CochainComplex.KFlatMonoidal

namespace Stacks.SheafOfModules.DerivedMonoidal

attribute [local instance] SheafOfModules.monoidalCategorySheafTensor
  SheafOfModules.symmetricCategorySheafTensor SheafOfModules.monoidalPreadditiveSheafTensor
  SheafOfModules.monoidalClosedSheafTensor
  SheafOfModules.preservesColimit_tensorRight_sheafTensor
  CochainComplex.symmetricCategory

variable {C : Type u} [SmallCategory.{u} C] {J : GrothendieckTopology C}
  (R : Sheaf J CommRingCat.{u})
variable [HasSheafify J AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
variable [HasDerivedCategory.{d} (Mod R)]

/-- **The derived tensor product of two modules in degree zero with vanishing tensor product
vanishes as soon as the first is flat**, on a ringed site.

The total tensor product `M[0] ⊗ N[0]` of complexes is a zero object with no flatness at all
(`isZero_tensorObj_single_of_isZero`); `M[0]` is a K-flat complex because `M` is flat, and the
one-sided comparison `CochainComplex.KFlatMonoidal.derivedTensorLeftKFlatIso` needs nothing of
the second argument.  This is
`isZero_derivedTensorSingle_of_isZero_tensorObj` with the second flatness hypothesis removed.

A step of the proof of an implication of Stacks 0FPG, not a clause of it, so it carries no
`@[stacks]` attribute. -/
theorem isZero_derivedTensorSingle_of_isZero_tensorObj_left (M N : Mod R)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) M)
    (h : IsZero (MonoidalCategory.tensorObj (C := Mod R) M N)) :
    letI := derivedMonoidal R
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod R) 0).obj M)
      ((DerivedCategory.singleFunctor (Mod R) 0).obj N)) :=
  CochainComplex.KFlatMonoidal.isZero_derivedTensor_of_isZero_of_kFlat_left (Mod R)
    (exists_kFlat_resolution R)
    (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R M hM 0)
    (isZero_tensorObj_single_of_isZero R M N h)

/-- **The same with the flat module on the right.**  Both braidings are supplied by
`derivedSymmetric` and by the symmetric structure of complexes; nothing is reproved. -/
theorem isZero_derivedTensorSingle_of_isZero_tensorObj_right (M N : Mod R)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := R) N)
    (h : IsZero (MonoidalCategory.tensorObj (C := Mod R) M N)) :
    letI := derivedMonoidal R
    letI := derivedSymmetric R
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod R) 0).obj M)
      ((DerivedCategory.singleFunctor (Mod R) 0).obj N)) :=
  CochainComplex.KFlatMonoidal.isZero_derivedTensor_of_isZero_of_kFlat_right (Mod R)
    (exists_kFlat_resolution R)
    (Stacks.SheafOfModules.KFlatResolution.kFlat_single_of_isFlat R N hN 0)
    (isZero_tensorObj_single_of_isZero R M N h)

end Stacks.SheafOfModules.DerivedMonoidal

namespace Stacks.Cohomology.MonoidalDerived

open AlgebraicGeometry Stacks.SheafOfModules.DerivedMonoidal

/-- **The derived tensor product of two modules in degree zero with vanishing tensor product
vanishes as soon as the first is flat**, on a ringed space, for the derived tensor product of
Stacks 0FPB.

A ringed space is a ringed site and `derivedCategoryMonoidalCategory X` is the ringed-site
structure `derivedMonoidal X.sheaf` at the site of opens of `X`, so nothing is transported.

This is `isZero_derivedTensor_of_isZero_tensor_of_isFlat` with the second flatness hypothesis
removed.  A step of the proof of an implication of Stacks 0FPG, not a clause of it, so it carries
no `@[stacks]` attribute. -/
theorem isZero_derivedTensor_of_isZero_tensor_of_isFlat_left (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (Mod X.sheaf)] (M N : Mod X.sheaf)
    (hM : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) M)
    (h : letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
      IsZero (MonoidalCategory.tensorObj (C := Mod X.sheaf) M N)) :
    letI := derivedCategoryMonoidalCategory.{u, d} X
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj M)
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj N)) :=
  isZero_derivedTensorSingle_of_isZero_tensorObj_left X.sheaf M N hM h

/-- **The same with the flat module on the right.** -/
theorem isZero_derivedTensor_of_isZero_tensor_of_isFlat_right (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (Mod X.sheaf)] (M N : Mod X.sheaf)
    (hN : AlgebraicGeometry.SheafOfModules.IsFlat.{u, u, u, u} (O := X.sheaf) N)
    (h : letI := SheafOfModules.monoidalCategorySheafTensor X.sheaf
      IsZero (MonoidalCategory.tensorObj (C := Mod X.sheaf) M N)) :
    letI := derivedCategoryMonoidalCategory.{u, d} X
    IsZero (MonoidalCategory.tensorObj
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj M)
      ((DerivedCategory.singleFunctor (Mod X.sheaf) 0).obj N)) :=
  isZero_derivedTensorSingle_of_isZero_tensorObj_right X.sheaf M N hN h

/-- **A zero object of `D(𝒪_X)` tensored on the right with anything is a zero object.**

`MonoidalPreadditive (DerivedModules X.sheaf)` is *not* available for the derived tensor product
of Stacks 0FPB — instance search fails on it — so this cannot be read off
`MonoidalCategory.whiskerRight_zero`.  What is available is that `- ⊗^L B` preserves direct sums
indexed by any type of the ringed space's universe
(`preservesCoproducts_derivedTensorRight`); an empty index gives preservation of the initial
object, and in a category with a zero object an initial object is a zero object.  The empty
index has to be transported from `PEmpty` in the space's universe to the `PEmpty` of
`CategoryTheory.Limits.IsInitial`, which is the equivalence of discrete categories on two empty
types. -/
theorem isZero_tensorObj_of_isZero_left (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (Mod X.sheaf)] (B : DerivedModules X.sheaf)
    {Z : DerivedModules X.sheaf} (hZ : IsZero Z) :
    letI := derivedCategoryMonoidalCategory.{u, d} X
    IsZero (MonoidalCategory.tensorObj Z B) := by
  let := derivedCategoryMonoidalCategory.{u, d} X
  let := derivedCategorySymmetricCategory.{u, d} X
  let : HasCoproducts.{u} (DerivedModules X.sheaf) :=
    Stacks.SmallDerivedCategory.hasCoproducts_derivedCategory _
  let := preservesCoproducts_derivedTensorRight X B PEmpty.{u + 1}
  let : PreservesColimitsOfShape (Discrete PEmpty.{1}) (MonoidalCategory.tensorRight B) :=
    preservesColimitsOfShape_of_equiv
      (Discrete.equivalence (Equiv.equivOfIsEmpty PEmpty.{u + 1} PEmpty.{1})) _
  exact (hZ.isInitial.isInitialObj (MonoidalCategory.tensorRight B) Z).isZero

/-- **A zero object of `D(𝒪_X)` tensored on the left with anything is a zero object.** -/
theorem isZero_tensorObj_of_isZero_right (X : RingedSpace.{u, u})
    [HasDerivedCategory.{d} (Mod X.sheaf)] (B : DerivedModules X.sheaf)
    {Z : DerivedModules X.sheaf} (hZ : IsZero Z) :
    letI := derivedCategoryMonoidalCategory.{u, d} X
    IsZero (MonoidalCategory.tensorObj B Z) := by
  let := derivedCategoryMonoidalCategory.{u, d} X
  let := derivedCategorySymmetricCategory.{u, d} X
  exact (isZero_tensorObj_of_isZero_left X B hZ).of_iso (β_ B Z)

end Stacks.Cohomology.MonoidalDerived

end
