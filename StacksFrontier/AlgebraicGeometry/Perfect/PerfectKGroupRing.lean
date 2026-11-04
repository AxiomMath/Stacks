module

public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TensorProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.PerfectComplexes.TriangulatedSubcategory
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafDegreeZero
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Monoidal.DerivedCategory
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.Ring
public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.CanonicalFunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# The Grothendieck ring of perfect complexes

Let `X` be a ringed space and `D(𝒪_X)` the unbounded derived category of `𝒪_X`-modules. The
derived tensor product of two perfect objects is perfect, so the perfect objects form a
tensor triangulated subcategory of `D(𝒪_X)` and their Grothendieck group `K₀(D_perf(𝒪_X))` is
a commutative ring: `[K] · [L] = [K ⊗^L L]`, with unit the class of `𝒪_X` in degree zero.

## Main definitions

* `AlgebraicGeometry.RingedSpace.derivedTensorObjIso`: for a derived tensor product `T` of
  `𝒪_X`-modules, an isomorphism `(T.tensor.obj K).obj L ≅ K ⊗ L` with the tensor product of
  the symmetric monoidal structure of [Stacks, Tag 0FPT] on `D(𝒪_X)`.
* `AlgebraicGeometry.RingedSpace.derivedTensorStructure`: the tensor structure on `D(𝒪_X)`
  whose bifunctor is `T.tensor`.
* `AlgebraicGeometry.RingedSpace.perfectTensorStructure`: its restriction to the perfect
  objects.

## Main results

* `AlgebraicGeometry.RingedSpace.exists_kFlatRepresentative`: every object of `D(𝒪_X)` is the
  image of a K-flat complex.
* `AlgebraicGeometry.RingedSpace.exists_derivedTensorProduct_commRing` ([stacks 0FDK]): the
  Grothendieck group of `D_perf(𝒪_X)` carries a commutative ring structure whose additive group
  is the given one, whose product of classes is the class of the derived tensor product, and
  whose unit is the class of the structure sheaf in degree zero.

## Implementation notes

The ring structure itself is not reproved here: `CategoryTheory.Pretriangulated.K0.TensorStructure`
and its `restrict` and `exists_commRing` already do that for an arbitrary tensor triangulated
category, asking only for *object-level* associativity, commutativity and unit isomorphisms,
which is all `K₀` can see. What this file supplies are the three inputs that specialize it to
`D_perf(𝒪_X)`:

* Exactness in each variable is not transported: the bifunctor of the tensor structure is
  `T.tensor` itself, so the four exactness fields are the `commShift_left`, `commShift_right`,
  `exact_left` and `exact_right` fields of `Stacks.DerivedTensor.RingedSite.DerivedTensorProduct`
  verbatim.
* The associator, braiding and left unitor come from the symmetric monoidal structure of
  Tag 0FPT through `AlgebraicGeometry.RingedSpace.derivedTensorObjIso`. That isomorphism is the
  only place where the two descriptions of the derived tensor product meet, and it is built on
  objects only: on a pair of K-flat complexes both `T.comparison` and the Tag 0FPT comparison
  identify the two with the image of the total tensor complex, and every object of `D(𝒪_X)` is
  the image of a K-flat complex. No naturality square and no coherence diagram is checked, and
  no heartbeat budget is raised.
* Closure of perfectness under the derived tensor product is Tag 09J5,
  `AlgebraicGeometry.RingedSpace.isPerfect_derivedTensorProduct`, and perfectness of the unit is
  the structure sheaf in degree zero being strictly perfect.

Perfectness is read at `Stacks.Cohomology.PerfectComplexes.IsPerfect`, the spelling the
triangulated-subcategory instance and the scheme-level `D_perf(𝒪_X)` of Tag 0F8I use; Tag 09J5
is stated at `AlgebraicGeometry.RingedSpace.IsPerfect`, which is the same predicate by `rfl`.

## References

* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 09J5](https://stacks.math.columbia.edu/tag/09J5)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open CategoryTheory.Pretriangulated
open AlgebraicGeometry StrictlyPerfect
open Stacks.SheafOfModules.DerivedMonoidal
open Stacks.Cohomology.PerfectComplexes

universe u d

namespace AlgebraicGeometry.RingedSpace

variable (X : RingedSpace.{u, u})
  [HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules X.sheaf)]

/-! ### K-flat representatives -/

/-- **Every object of `D(𝒪_X)` is the image of a K-flat complex.** The object is the image of
some complex, since `DerivedCategory.Q` is essentially surjective, and that complex receives a
quasi-isomorphism from a K-flat one by Tag 06YS. -/
theorem exists_kFlatRepresentative (A : DerivedModules X.sheaf) :
    ∃ P : CochainComplex (Mod X.sheaf) ℤ,
      Stacks.SheafOfModules.KFlat.KFlat X.sheaf P ∧
        Nonempty ((DerivedCategory.Q (C := Mod X.sheaf)).obj P ≅ A) := by
  obtain ⟨P, p, hP, hp⟩ :=
    exists_kFlat_resolution X.sheaf ((DerivedCategory.Q (C := Mod X.sheaf)).objPreimage A)
  refine ⟨P, hP, ⟨?_⟩⟩
  have : IsIso ((DerivedCategory.Q (C := Mod X.sheaf)).map p) :=
    (DerivedCategory.isIso_Q_map_iff_quasiIso _ p).mpr hp
  exact asIso ((DerivedCategory.Q (C := Mod X.sheaf)).map p) ≪≫
    (DerivedCategory.Q (C := Mod X.sheaf)).objObjPreimageIso A

/-! ### The derived tensor product is the monoidal tensor product, on objects -/

variable (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.sheaf)

/-- **A derived tensor product of two objects of `D(𝒪_X)` is isomorphic to their monoidal
tensor product.** Choosing K-flat representatives of both objects, the two agree with the image
of the total tensor complex of the representatives, by the `comparison` field of the derived
tensor product and by the comparison of the symmetric monoidal structure of Tag 0FPT. -/
theorem nonempty_derivedTensorObjIso (A B : DerivedModules X.sheaf) :
    letI := (symmetricMonoidalDerived X.sheaf).monoidal
    Nonempty ((T.tensor.obj A).obj B ≅ A ⊗ B) := by
  let := (symmetricMonoidalDerived X.sheaf).monoidal
  obtain ⟨P, hP, ⟨a⟩⟩ := exists_kFlatRepresentative X A
  obtain ⟨N, hN, ⟨b⟩⟩ := exists_kFlatRepresentative X B
  let key (F : DerivedModules X.sheaf ⥤ DerivedModules X.sheaf ⥤ DerivedModules X.sheaf) :=
    ((F.mapIso a).app B).symm ≪≫ ((F.obj _).mapIso b).symm
  exact ⟨key T.tensor ≪≫ T.comparison P N hP hN ≪≫
    ((symmetricMonoidalDerived X.sheaf).comparison P N hP hN).symm ≪≫
    (key (curriedTensor (DerivedModules X.sheaf))).symm⟩

/-- A choice of the isomorphism of `AlgebraicGeometry.RingedSpace.nonempty_derivedTensorObjIso`.
Only its existence is asserted there, since it depends on a choice of K-flat representatives;
nothing below depends on which one is taken, classes in `K₀` being invariant under
isomorphism. -/
def derivedTensorObjIso (A B : DerivedModules X.sheaf) :
    letI := (symmetricMonoidalDerived X.sheaf).monoidal
    (T.tensor.obj A).obj B ≅ A ⊗ B :=
  (nonempty_derivedTensorObjIso X T A B).some

/-! ### The tensor structure on `D(𝒪_X)` -/

/-- **The tensor structure on `D(𝒪_X)` given by a derived tensor product.** The bifunctor is
`T.tensor` and its exactness in each variable is the exactness recorded by `T`; the associator,
braiding and left unitor are those of the symmetric monoidal structure of Tag 0FPT, read
through `AlgebraicGeometry.RingedSpace.derivedTensorObjIso`. The unit object is the structure
sheaf in degree zero rather than the abstract monoidal unit, so that the unit of the resulting
ring is the class the source names. -/
def derivedTensorStructure : K0.TensorStructure (DerivedModules X.sheaf) :=
  letI := (symmetricMonoidalDerived X.sheaf).monoidal
  letI := (symmetricMonoidalDerived X.sheaf).symmetric
  let e := derivedTensorObjIso X T
  { tensor := T.tensor
    commShiftRight := T.commShift_right
    isTriangulatedRight := T.exact_right
    commShiftLeft := T.commShift_left
    isTriangulatedLeft := T.exact_left
    one := (DerivedCategory.Q (C := Mod X.sheaf)).obj
      ((CochainComplex.singleFunctor (Mod X.sheaf) 0).obj
        (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)))
    associator := fun A B C =>
      e ((T.tensor.obj A).obj B) C ≪≫ whiskerRightIso (e A B) C ≪≫ α_ A B C ≪≫
        (whiskerLeftIso A (e B C)).symm ≪≫ (e A ((T.tensor.obj B).obj C)).symm
    braiding := fun A B => e A B ≪≫ β_ A B ≪≫ (e B A).symm
    leftUnitor := fun A =>
      e _ A ≪≫ whiskerRightIso (symmetricMonoidalDerived X.sheaf).unitIso.symm A ≪≫ λ_ A }

/-! ### The tensor structure on `D_perf(𝒪_X)` -/

/-- **The tensor structure on the perfect objects of `D(𝒪_X)`.** The perfect objects form a
triangulated subcategory (Tag 08CR), are closed under the derived tensor product (Tag 09J5) and
contain the structure sheaf in degree zero, which is strictly perfect. -/
def perfectTensorStructure :
    K0.TensorStructure
      (ObjectProperty.FullSubcategory
        (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} (X := X))) :=
  @K0.TensorStructure.restrict _ _ _ _ _ _ _ (derivedTensorStructure X T)
    (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} (X := X))
    (Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect X)
    (fun _ _ hA hB => isPerfect_derivedTensorProduct X T _ _ hA hB)
    (isPerfect_Q_obj_of_isStrictlyPerfect
      (isStrictlyPerfect_single (isDirectSummandOfFiniteFree_structureModule X) 0))

/-! ### The Grothendieck ring -/

/-- **Stacks Project, Tag 0FDK.** The Grothendieck group `K₀(D_perf(𝒪_X))` of the perfect
objects of `D(𝒪_X)` carries a commutative ring structure whose additive group is the one it
already has, whose product of the classes of two perfect objects is the class of their derived
tensor product, and whose unit is the class of the structure sheaf in degree zero.

The source states this for a scheme; it holds for any ringed space, and for an arbitrary
derived tensor product of `𝒪_X`-modules, which is the generality Tag 09J5 is stated in. -/
@[stacks 0FDK "perfect_k_ring", sga "6 IV 2.7" "b) ring str. on K'"]
theorem exists_derivedTensorProduct_commRing :
    ∃ r : CommRing (K0 (ObjectProperty.FullSubcategory
        (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} (X := X)))),
      r.toAddCommGroup = (inferInstance : AddCommGroup (K0 (ObjectProperty.FullSubcategory
        (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} (X := X))))) ∧
      (∀ (K L : ObjectProperty.FullSubcategory
            (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} (X := X)))
          (h : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X)
            ((T.tensor.obj K.obj).obj L.obj)),
        r.mul (K0.cls K) (K0.cls L) = K0.cls ⟨(T.tensor.obj K.obj).obj L.obj, h⟩) ∧
      (∀ h : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X)
          ((DerivedCategory.Q (C := Mod X.sheaf)).obj
            ((CochainComplex.singleFunctor (Mod X.sheaf) 0).obj
              (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf.{u, u, u} X.sheaf)))),
        r.one = K0.cls ⟨_, h⟩) := by
  obtain ⟨r, hadd, hmul, hone⟩ := (perfectTensorStructure X T).exists_commRing
  exact ⟨r, hadd, fun K L _ => hmul K L, fun _ => hone⟩

end AlgebraicGeometry.RingedSpace

end
