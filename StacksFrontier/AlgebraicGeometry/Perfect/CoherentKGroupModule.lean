module

public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroup
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectBoundedCoherentTensor
public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectKGroupRing
public import StacksFrontier.CategoryTheory.Triangulated.KGroup.SubcategoryAction
import StacksCore.Tactic.StacksAttribute

/-!
# `K'₀(X)` as a module over the Grothendieck ring `K₀(X)`

Let `X` be a Noetherian scheme. The derived tensor product carries
`D_perf(𝒪_X) × D^b_Coh(𝒪_X)` into `D^b_Coh(𝒪_X)`, and that bifunctor is exact in each variable,
so the bilinear map on `K`-groups of [Stacks, Tag 0FCT] gives a bilinear multiplication
`K₀(X) × K'₀(X) ⟶ K'₀(X)` which makes `K'₀(X) = K₀(D^b_Coh(𝒪_X))` a module over the
Grothendieck ring `K₀(X) = K₀(D_perf(𝒪_X))`.

## Main definitions

* `AlgebraicGeometry.perfectAtScheme` and `AlgebraicGeometry.boundedCoherentAtScheme`: the two
  triangulated subcategories `D_perf(𝒪_X)` and `D^b_Coh(𝒪_X)` of `D(𝒪_X)`.
* `AlgebraicGeometry.derivedTensorStructureAtScheme`: the tensor structure on `D(𝒪_X)` given by
  the derived tensor product of [Stacks, Tag 06YU].
* `AlgebraicGeometry.perfectTensorStructureScheme`: its restriction to `D_perf(𝒪_X)`, whose
  Grothendieck ring is `K₀(X)`.

## Main results

* `AlgebraicGeometry.derivedCategoryBBounded_coherentModules_derivedTensor_of_isPerfect`
  ([stacks 0FDK]): the bifunctor
  `⊗^𝐋_{𝒪_X} : D_perf(𝒪_X) × D^b_Coh(𝒪_X) ⟶ D^b_Coh(𝒪_X)`.
* `AlgebraicGeometry.exists_derivedTensorProduct_module` ([stacks 0FDK]): `K₀(D^b_Coh(𝒪_X))`
  carries a module structure over the Grothendieck ring `K₀(D_perf(𝒪_X))` whose scalar
  multiplication of classes is the class of the derived tensor product.
* `AlgebraicGeometry.exists_module_coherentKZero` ([stacks 0FDK]): the same module structure
  read on `K'₀(X)`, the Grothendieck group of coherent `𝒪_X`-modules, through the isomorphism
  `K'₀(X) ≅ K₀(D^b_Coh(𝒪_X))` of [Stacks, Tag 0FDF].

## Implementation notes

The three inputs the source names are used exactly where it names them.

* The bifunctor is the closure statement
  `AlgebraicGeometry.derivedCategoryBBounded_derivedTensor_of_isPerfect`, read at the spelling
  of coherence that [Stacks, Tag 0FDF] uses. The two coherence classes of the library,
  `SheafOfModules.IsCoherent` and `Stacks.SheafOfModules.IsCoherent`, have the same objects but
  do not unify, so `derivedCategoryBBounded_coherentModules_iff` crosses between them; the
  weak-Serre instance, and with it the triangulated structure of `D^b_Coh(𝒪_X)`, is available
  at the second one.
* Bilinearity is [Stacks, Tag 0FCT],
  `CategoryTheory.Pretriangulated.K0.exists_bilinear_of_bifunctor`, which
  `CategoryTheory.Pretriangulated.K0.TensorAction.smul` applies to the bifunctor; the exactness
  in each variable that Tag 0FCT asks for is inherited from the ambient derived tensor product
  by `CategoryTheory.Pretriangulated.K0.liftBifunctorPair_isTriangulatedRight` and its left
  companion.
* The module axioms are the object-level associativity `(K ⊗ L) ⊗ M ≅ K ⊗ (L ⊗ M)` and unit
  `𝒪_X ⊗ M ≅ M` isomorphisms of the symmetric monoidal structure of [Stacks, Tag 0FPT], which
  is all `K₀` can see; this is
  `CategoryTheory.Pretriangulated.K0.TensorAction.exists_module_restrictPair`.

The ring `K₀(X)` is the one of the first clause of the tag,
`AlgebraicGeometry.RingedSpace.exists_derivedTensorProduct_commRing`:
`perfectTensorStructureScheme_eq` records that `perfectTensorStructureScheme` *is*
`AlgebraicGeometry.RingedSpace.perfectTensorStructure` at the derived tensor product of
[Stacks, Tag 06YU], which is the one the closure statement is stated at.

**One spelling of the category of `𝒪_X`-modules.** Three spellings of that category are in
play across the material used here — `SheafOfModules.{u} X.ringCatSheaf`, which coherence and
Tag 0FDF use; `StrictlyPerfect.OXMod X.toRingedSpace`, which perfectness uses; and
`Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf`, which the derived tensor
product uses. They are equal by `rfl` but instance search does not cross them, so everything
below is stated at the first one and each crossing is performed once, in the body of
`perfectAtScheme`, `isTriangulated_perfectAtScheme`, `derivedTensorStructureAtScheme`,
`perfectTensorStructureRingedSpace`, `perfectAtScheme_derivedTensor` and `perfectAtScheme_one`.
Leaving a crossing to be discovered inside a larger elaboration instead exhausts the heartbeat
budget.

The module structure on `K'₀(X)` is the one transported along the isomorphism of Tag 0FDF, and
`exists_module_coherentKZero` asserts the transport together with the two properties that pin
it down: the isomorphism takes the class of a coherent module to the class of that module placed
in degree zero, and the scalar multiple of the class of a coherent sheaf `ℱ` by the class of a
perfect object `K` is sent to the class of `K ⊗^𝐋 ℱ[0]`.

## References

* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 0FCT](https://stacks.math.columbia.edu/tag/0FCT)
* [Stacks Project, Tag 0FDF](https://stacks.math.columbia.edu/tag/0FDF)
* [Stacks Project, Tag 0FPT](https://stacks.math.columbia.edu/tag/0FPT)
* [Stacks Project, Tag 06YU](https://stacks.math.columbia.edu/tag/06YU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe u

attribute [local instance 100000] HasDerivedCategory.standard

namespace AlgebraicGeometry

variable (X : Scheme.{u}) [IsNoetherian X]

/-! ### The two coherence classes -/

omit [IsNoetherian X] in
/-- **Membership in `D^b_Coh(𝒪_X)` does not depend on which of the two coherence classes of the
library is used.** The two have the same objects. -/
theorem derivedCategoryBBounded_coherentModules_iff
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :
    DerivedCategoryB.derivedCategoryBBounded
        (Stacks.SheafOfModules.coherentModules X.ringCatSheaf) K ↔
      DerivedCategoryB.derivedCategoryBBounded
        (fun F : SheafOfModules.{u} X.ringCatSheaf => F.IsCoherent) K := by
  constructor
  · exact fun h => ⟨h.1, fun n => (h.2 n).rootIsCoherent⟩
  · exact fun h => ⟨h.1, fun n => (h.2 n).stacksIsCoherent⟩

/-! ### The bifunctor `D_perf(𝒪_X) × D^b_Coh(𝒪_X) ⟶ D^b_Coh(𝒪_X)` -/

/-- **Stacks Project, Tag 0FDK.** Let `X` be a Noetherian scheme. The derived tensor product of a
perfect object of `D(𝒪_X)` with an object of `D^b_Coh(𝒪_X)` is an object of `D^b_Coh(𝒪_X)`: the
derived tensor product produces the bifunctor
`⊗^𝐋_{𝒪_X} : D_perf(𝒪_X) × D^b_Coh(𝒪_X) ⟶ D^b_Coh(𝒪_X)`. -/
@[stacks 0FDK "the bifunctor D_perf × D^b_Coh ⟶ D^b_Coh"]
theorem derivedCategoryBBounded_coherentModules_derivedTensor_of_isPerfect
    (K L : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hK : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) K)
    (hL : DerivedCategoryB.derivedCategoryBBounded
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf) L) :
    DerivedCategoryB.derivedCategoryBBounded
      (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)
      (((TorFormula.derivedTensor X).obj K).obj L) :=
  (derivedCategoryBBounded_coherentModules_iff X _).2
    (derivedCategoryBBounded_derivedTensor_of_isPerfect X K L hK
      ((derivedCategoryBBounded_coherentModules_iff X L).1 hL))

/-! ### The two triangulated subcategories, at one spelling of `Mod(𝒪_X)` -/

/-- `D_perf(𝒪_X)`, the perfect objects, as a property of objects of `D(𝒪_X)` read at the
spelling `SheafOfModules.{u} X.ringCatSheaf` of the category of `𝒪_X`-modules. -/
def perfectAtScheme : ObjectProperty (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :=
  Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)

/-- **The perfect objects form a triangulated subcategory**, Tag 08CR, read at that spelling. -/
instance isTriangulated_perfectAtScheme : (perfectAtScheme X).IsTriangulated :=
  Stacks.Cohomology.PerfectTriangulatedSubcategory.isTriangulated_isPerfect X.toRingedSpace

/-- `D^b_Coh(𝒪_X)`, the cohomologically bounded objects with coherent cohomology sheaves, as a
property of objects of `D(𝒪_X)`. This is the subcategory whose `K`-group is `K'₀(X)` by
[Stacks, Tag 0FDF]. -/
abbrev boundedCoherentAtScheme :
    ObjectProperty (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :=
  DerivedCategoryB.derivedCategoryBBounded (Stacks.SheafOfModules.coherentModules X.ringCatSheaf)

/-! ### The tensor structures -/

/-- **The tensor structure on `D(𝒪_X)` given by the derived tensor product of
[Stacks, Tag 06YU]**, read at the spelling `SheafOfModules.{u} X.ringCatSheaf` of the category of
`𝒪_X`-modules. -/
def derivedTensorStructureAtScheme :
    K0.TensorStructure (DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :=
  RingedSpace.derivedTensorStructure X.toRingedSpace
    (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace)

omit [IsNoetherian X] in
/-- The bifunctor of that tensor structure is the derived tensor product. -/
theorem derivedTensorStructureAtScheme_tensor :
    (derivedTensorStructureAtScheme X).tensor = TorFormula.derivedTensor X := rfl

omit [IsNoetherian X] in
/-- **The derived tensor product of two perfect objects is perfect**, Tag 09J5, in the shape the
restriction of a tensor structure consumes. -/
theorem perfectAtScheme_derivedTensor
    (Y Z : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
    (hY : perfectAtScheme X Y) (hZ : perfectAtScheme X Z) :
    perfectAtScheme X (((derivedTensorStructureAtScheme X).tensor.obj Y).obj Z) :=
  RingedSpace.isPerfect_derivedTensorProduct X.toRingedSpace
    (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace) Y Z hY hZ

/-- `AlgebraicGeometry.RingedSpace.perfectTensorStructure` at the derived tensor product of
[Stacks, Tag 06YU], read at the spelling of the category of `𝒪_X`-modules that perfectness is
stated at. Its Grothendieck ring is the ring `K₀(X)` of
`AlgebraicGeometry.RingedSpace.exists_derivedTensorProduct_commRing`. -/
def perfectTensorStructureRingedSpace :
    K0.TensorStructure (ObjectProperty.FullSubcategory
      (Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace))) :=
  RingedSpace.perfectTensorStructure X.toRingedSpace
    (Stacks.Cohomology.TorAmplitude.derTensor X.toRingedSpace)

omit [IsNoetherian X] in
/-- **The unit of the tensor structure, the structure sheaf in degree zero, is perfect**: it is
strictly perfect, the structure sheaf being a direct summand of a finite free module. This is the
`one` field of `AlgebraicGeometry.RingedSpace.perfectTensorStructure`. -/
theorem perfectAtScheme_one : perfectAtScheme X (derivedTensorStructureAtScheme X).one :=
  (perfectTensorStructureRingedSpace X).one.property

/-- **The tensor structure on `D_perf(𝒪_X)`**, whose Grothendieck ring is `K₀(X)`. It is a
reducible abbreviation, so that the commutative ring structure it induces on `K₀` is the one
instance search sees through the restriction it is built by. -/
abbrev perfectTensorStructureScheme : K0.TensorStructure (perfectAtScheme X).FullSubcategory :=
  (derivedTensorStructureAtScheme X).restrict (perfectAtScheme X)
    (perfectAtScheme_derivedTensor X) (perfectAtScheme_one X)

omit [IsNoetherian X] in
/-- The tensor structure above *is*
`AlgebraicGeometry.RingedSpace.perfectTensorStructure`, so its Grothendieck ring is the ring
`K₀(X)` of `AlgebraicGeometry.RingedSpace.exists_derivedTensorProduct_commRing`. -/
theorem perfectTensorStructureScheme_eq :
    perfectTensorStructureScheme X = perfectTensorStructureRingedSpace X := rfl

/-! ### The module structure -/

/-- **Stacks Project, Tag 0FDK.** Let `X` be a Noetherian scheme. The zeroth `K`-group
`K₀(D^b_Coh(𝒪_X))` of the cohomologically bounded objects of `D(𝒪_X)` with coherent cohomology
sheaves carries a module structure over the Grothendieck ring `K₀(D_perf(𝒪_X))` of the perfect
objects for which the scalar multiple of the class of an object of `D^b_Coh(𝒪_X)` by the class of
a perfect object is the class of their derived tensor product. In particular that scalar
multiplication is bilinear.

The ring acting is the commutative ring of
`AlgebraicGeometry.RingedSpace.exists_derivedTensorProduct_commRing`
(`perfectTensorStructureScheme_eq`), and the group acted on is `K'₀(X)` by
[Stacks, Tag 0FDF]. -/
@[stacks 0FDK "K₀(D^b_Coh(𝒪_X)) is a module over the Grothendieck ring K₀(D_perf(𝒪_X))"]
theorem exists_derivedTensorProduct_module :
    letI := (perfectTensorStructureScheme X).commRing
    ∃ m : Module (K0 (perfectAtScheme X).FullSubcategory)
        (K0 (boundedCoherentAtScheme X).FullSubcategory),
      ∀ (K L : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf))
        (hK : perfectAtScheme X K) (hL : boundedCoherentAtScheme X L)
        (h : boundedCoherentAtScheme X (((TorFormula.derivedTensor X).obj K).obj L)),
        letI := m
        K0.cls (⟨K, hK⟩ : (perfectAtScheme X).FullSubcategory) •
            K0.cls (⟨L, hL⟩ : (boundedCoherentAtScheme X).FullSubcategory) =
          K0.cls (⟨((TorFormula.derivedTensor X).obj K).obj L, h⟩ :
            (boundedCoherentAtScheme X).FullSubcategory) := by
  obtain ⟨m, hm⟩ := K0.TensorAction.exists_module_restrictPair
    (perfectAtScheme X) (boundedCoherentAtScheme X) (derivedTensorStructureAtScheme X)
    (perfectAtScheme_derivedTensor X) (perfectAtScheme_one X)
    fun K L hK hL =>
      derivedCategoryBBounded_coherentModules_derivedTensor_of_isPerfect X K L hK hL
  exact ⟨m, fun K L hK hL h => hm K L hK hL h⟩

/-- **Stacks Project, Tag 0FDK.** Let `X` be a Noetherian scheme. The Grothendieck group
`K'₀(X)` of coherent `𝒪_X`-modules is a module over the Grothendieck ring
`K₀(X) = K₀(D_perf(𝒪_X))`: there is a module structure on `K'₀(X)` and an isomorphism of abelian
groups `K'₀(X) ≅ K₀(D^b_Coh(𝒪_X))` which takes the class of a coherent module to the class of
that module placed in degree zero — the isomorphism of [Stacks, Tag 0FDF] — and which carries the
scalar multiple of the class of a coherent sheaf `ℱ` by the class of a perfect object `K` to the
class of their derived tensor product `K ⊗^𝐋_{𝒪_X} ℱ[0]`. -/
@[stacks 0FDK "K'₀(X) is a module over the Grothendieck ring K₀(X)", sga "6 IV 3.2.3"]
theorem exists_module_coherentKZero :
    letI := (perfectTensorStructureScheme X).commRing
    ∃ (m : Module (K0 (perfectAtScheme X).FullSubcategory) (CoherentKZero X))
      (e : CoherentKZero X ≃+ K0 (boundedCoherentAtScheme X).FullSubcategory),
      (∀ F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf,
          ∃ K : (boundedCoherentAtScheme X).FullSubcategory,
            Nonempty (K.obj ≅ (DerivedCategory.singleFunctor
              (SheafOfModules.{u} X.ringCatSheaf) 0).obj F.obj)) ∧
      (∀ (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
          (K : (boundedCoherentAtScheme X).FullSubcategory),
          (K.obj ≅ (DerivedCategory.singleFunctor
              (SheafOfModules.{u} X.ringCatSheaf) 0).obj F.obj) →
            e (KZero.mk _ F) = K0.cls K) ∧
      ∀ (K : (perfectAtScheme X).FullSubcategory)
        (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf)
        (L : (boundedCoherentAtScheme X).FullSubcategory)
        (_ : L.obj ≅ (DerivedCategory.singleFunctor
          (SheafOfModules.{u} X.ringCatSheaf) 0).obj F.obj)
        (h : boundedCoherentAtScheme X (((TorFormula.derivedTensor X).obj K.obj).obj L.obj)),
        letI := m
        e (K0.cls K • KZero.mk _ F) =
          K0.cls (⟨((TorFormula.derivedTensor X).obj K.obj).obj L.obj, h⟩ :
            (boundedCoherentAtScheme X).FullSubcategory) := by
  let := (perfectTensorStructureScheme X).commRing
  obtain ⟨mod, hm⟩ := K0.TensorAction.exists_module_restrictPair
    (perfectAtScheme X) (boundedCoherentAtScheme X) (derivedTensorStructureAtScheme X)
    (perfectAtScheme_derivedTensor X) (perfectAtScheme_one X)
    fun K L hK hL =>
      derivedCategoryBBounded_coherentModules_derivedTensor_of_isPerfect X K L hK hL
  let := mod
  obtain ⟨e, he₁, he₂⟩ := exists_addEquiv_coherentKZero_K0 X
  refine ⟨{ smul := fun a w => e.symm (a • e w)
            one_smul := fun w =>
              (congrArg e.symm
                (one_smul (K0 (perfectAtScheme X).FullSubcategory) (e w))).trans
                  (e.symm_apply_apply w)
            mul_smul := fun a b w =>
              congrArg e.symm ((mul_smul a b (e w)).trans
                (congrArg (fun x => a • x) (e.apply_symm_apply (b • e w)).symm))
            smul_zero := fun a =>
              (congrArg e.symm ((congrArg (fun x => a • x) (map_zero e)).trans
                (smul_zero a))).trans (map_zero e.symm)
            smul_add := fun a w w' =>
              (congrArg e.symm ((congrArg (fun x => a • x) (map_add e w w')).trans
                (smul_add a (e w) (e w')))).trans (map_add e.symm _ _)
            add_smul := fun a b w =>
              (congrArg e.symm (add_smul a b (e w))).trans (map_add e.symm _ _)
            zero_smul := fun w =>
              (congrArg e.symm
                (zero_smul (K0 (perfectAtScheme X).FullSubcategory) (e w))).trans
                  (map_zero e.symm) },
    e, he₁, fun F K h => he₂ F K h, ?_⟩
  intro K F L hL h
  refine (e.apply_symm_apply (K0.cls K • e (KZero.mk _ F))).trans ?_
  rw [he₂ F L hL]
  exact hm K.obj L.obj K.property L.property h

end AlgebraicGeometry

end
