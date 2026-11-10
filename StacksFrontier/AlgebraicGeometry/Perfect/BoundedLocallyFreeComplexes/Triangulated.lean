module

public import StacksFrontier.AlgebraicGeometry.Perfect.BoundedLocallyFreeComplexes.Perfectness
public import StacksFrontier.Algebra.Homology.DerivedCategory.Basic
public import StacksFrontier.Algebra.Homology.HomotopyCategory.Triangulated
public import StacksFrontier.CategoryTheory.Triangulated.Localization

/-!
# `K^b(A)` is a triangulated subcategory, and its quasi-isomorphisms

This file continues Tag 0F8I. A bounded complex of finite locally free `O_X`-modules has perfect
image in the derived category
(`Stacks.Perfect.BoundedLocallyFreeComplexes.perfect_of_boundedFiniteLocallyFree`); here we show
that `K^b(A)` is a triangulated subcategory of the homotopy category, form the canonical functor
`K^b(A) ⥤ D_perf(O_X)`, and record the two properties of the system `S` of quasi-isomorphisms of
`K^b(A)` that the source needs of it: it is saturated, and it is compatible with the
triangulation.

## Main definitions

* `Stacks.Perfect.BoundedLocallyFreeComplexes.perfectComplexFunctor` is the canonical functor
  `K^b(A) ⥤ D_perf(O_X)`, obtained by lifting `CategoryTheory.DerivedCategory.Qh` along the
  perfectness of its values.

## Main results

* `boundedFiniteLocallyFreeHomotopyProperty_isTriangulated`: `K^b(A)` is a
  triangulated subcategory of `K(O_X)`.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.quasiIsomorphisms_isSaturated`: `S` is a saturated
  multiplicative system.
* `Stacks.Perfect.BoundedLocallyFreeComplexes.quasiIsomorphisms_isCompatibleWithTriangulation`:
  `S` is compatible with the triangulated structure of `K^b(A)`.

## Implementation notes

That `K^b(A)` is triangulated is `HomotopyCategory.isTriangulated_strictMap_quotient` applied to
the property of bounded complexes with finite locally free terms, so it reduces to three closure
properties of that property at the level of complexes: it holds of the zero complex, it is
stable under shift, and it is stable under mapping cones. The first two are degreewise
immediate once one knows that a zero module is finite locally free
(`Stacks.Perfect.BoundedLocallyFreeComplexes.finiteLocallyFree_of_isZero`); the third needs that
a biproduct of two finite locally free modules is finite locally free
(`Stacks.Perfect.BoundedLocallyFreeComplexes.finiteLocallyFree_biprod`), since
`(mappingCone f).X i` is `K.X (i + 1) ⊞ L.X i`.

For the biproduct, local generators data for `M` and for `N` are combined by intersecting the
two coverings pairwise and taking the disjoint union of the two generating families over each
intersection; `Stacks.Perfect.BoundedLocallyFreeComplexes.locallyFreeIso_restrict` restricts a
local free basis to a smaller open and
`Stacks.Perfect.BoundedLocallyFreeComplexes.freeSumBiprodIso` identifies a free module on a sum
type with a biproduct of free modules. Finiteness is then finiteness of a sum of two finite
types. Finite local freeness is invariant under isomorphism by
`Stacks.FiniteLocallyFree.IsFiniteLocallyFree.of_iso`.

Both properties of `S` come from the corresponding properties of the quasi-isomorphisms of the
whole homotopy category `K(O_X)`, of which `S` is by definition the inverse image along the
inclusion of `K^b(A)`; this is the omnibus statement
`isSaturated_and_isCompatibleWithTriangulation_inverseImage_ι_and_isLocalizedEquivalence`
of `CategoryTheory.ObjectProperty`.
Only its first two conjuncts are used: the third, the localized equivalence, needs a
left-resolution hypothesis on the inclusion, which is the content of Tags 0F8F, 0F8G and 0F8H.
The statement needs `K^b(A)` to be triangulated, which is why the two results about `S` depend
on the first result of this file.

## References

* [Stacks Project, Tag 0F8I](https://stacks.math.columbia.edu/tag/0F8I)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace StrictlyPerfect
open Stacks.Cohomology.PerfectComplexes Stacks.FiniteLocallyFree

universe u

namespace Stacks.Perfect.BoundedLocallyFreeComplexes

/-! ### Finite local freeness of zero modules and of biproducts -/

/-- **The free module on an empty index type is zero.** The free-module functor is a left
adjoint, hence preserves the initial object, and an initial object of a category with zero
morphisms is a zero object. -/
theorem free_empty_isZero {C : Type u} [Category.{u} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}] :
    IsZero (SheafOfModules.free (R := R) (ULift.{u} (Fin 0))) := by
  have hI : IsInitial (ULift.{u} (Fin 0)) :=
    Classical.choice ((Types.initial_iff_empty _).2 ⟨fun x => Fin.elim0 x.down⟩)
  exact (IsInitial.isInitialObj (SheafOfModules.freeFunctor (R := R)) _ hI).isZero

/-- A family of opens covers the top object iff every point lies in one of them. -/
private theorem coversTop_iff_forall_exists_mem {Y : Type u} [TopologicalSpace Y] {ι : Type*}
    (U : ι → Opens Y) :
    (Opens.grothendieckTopology Y).CoversTop U ↔ ∀ x, ∃ i, x ∈ U i := by
  simp [Opens.coversTop_iff, IsOpenCover, eq_top_iff, IsConcreteLE.le_iff, Opens.mem_iSup]

/-- **A zero module on a scheme is finite locally free.** Take the one-member covering by the
whole space and the empty generating family: the free module on the empty type is zero, so the
projection onto a zero module is an isomorphism. -/
theorem finiteLocallyFree_of_isZero (X : Scheme.{u}) (M : X.Modules)
    (hM : IsZero M) : IsFiniteLocallyFree (R := X.ringCatSheaf) M := by
  let R := X.ringCatSheaf
  let U : Opens X.carrier := ⊤
  let : (SheafOfModules.overFunctor R U).PreservesZeroMorphisms := ⟨by
    intros
    ext V x
    rfl⟩
  let hMtop : IsZero ((SheafOfModules.overFunctor R (⊤ : Opens X.carrier)).obj M) :=
    Functor.map_isZero _ hM
  let hfree : IsZero (SheafOfModules.free (R := R.over U) (ULift.{u} (Fin 0))) :=
    free_empty_isZero
  let q : M.LocalGeneratorsData.{u} := {
    I := ULift.{u} Unit
    X := fun _ => ⊤
    coversTop := (coversTop_iff_forall_exists_mem _).2 fun _ => ⟨ULift.up (), trivial⟩
    generators := fun _ => {
      I := ULift.{u} (Fin 0)
      s := fun z => Fin.elim0 z.down
      epi := hMtop.epi _
    }
  }
  have hq : q.IsLocallyFreeData := by
    constructor
    intro i
    exact (hfree.isIso hMtop ((q.generators i).π))
  let : Fintype (ULift.{u} (Fin 0)) := inferInstance
  have hqfin : q.IsFiniteType := by
    constructor
    intro i
    dsimp [q]
    constructor
    exact Finite.of_fintype (ULift.{u} (Fin 0))
  exact { exists_isFiniteLocallyFreeData := ⟨q, hq, hqfin⟩ }

/-- **The free module on a sum type is the biproduct of the two free modules.** The free-module
functor turns the sum into a coproduct, and a binary coproduct in a category with biproducts is
the biproduct. -/
def freeSumBiprodIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    (R : Sheaf J RingCat.{u})
    [HasWeakSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    (I K : Type u) :
    SheafOfModules.free (R := R) (Sum I K) ≅
      SheafOfModules.free (R := R) I ⊞ SheafOfModules.free (R := R) K :=
  (SheafOfModules.freeSumIso (R := R) I K).symm ≪≫
    (biprod.isoCoprod (SheafOfModules.free (R := R) I)
      (SheafOfModules.free (R := R) K)).symm

/-- **A local free basis restricts to a smaller open.** Restriction along `V ≤ q.X i` is a left
adjoint, so it carries the free module on the generating family of `M` over `q.X i` to the free
module on the same family over `V`, and the basis isomorphism along with it. -/
def locallyFreeIso_restrict
    {Y : RingedSpace.{u, u}} (M : OXMod.{u} Y)
    [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : Opens Y.carrier,
      HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over U) AddCommGrpCat.{u}]
    [∀ U : Opens Y.carrier,
      ((Opens.grothendieckTopology Y.carrier).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u}]
    (q : M.LocalGeneratorsData.{u}) (hq : q.IsLocallyFreeData)
    (V : Opens Y.carrier) (i : q.I) (hV : V ≤ q.X i) :
    SheafOfModules.free (R := (structureSheafOfRings Y).over V)
      (q.generators i).I ≅ M.over V := by
  let R := structureSheafOfRings Y
  let f : V ⟶ q.X i := homOfLE hV
  let F := SheafOfModules.overMap R f
  let eπ : SheafOfModules.free (R := R.over (q.X i)) (q.generators i).I ≅
      M.over (q.X i) := asIso (q.generators i).π
  let : PreservesColimitsOfShape (Discrete (q.generators i).I) F := inferInstance
  let eFree : SheafOfModules.free (R := R.over V) (q.generators i).I ≅
      F.obj (SheafOfModules.free (R := R.over (q.X i)) (q.generators i).I) :=
    SheafOfModules.mapFreeIso F (q.generators i).I
      (SheafOfModules.overMapUnitIso f).symm
  exact eFree ≪≫ F.mapIso eπ ≪≫ (SheafOfModules.overFunctorMap R f).app M

/-- **Transporting the canonical generating family of a free module along an isomorphism keeps
an isomorphic projection.** The transported projection is the canonical one composed with the
isomorphism, and the canonical one is the identity. -/
theorem freeGeneratingSectionsEquivOfIso_isIso
    {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}} [HasWeakSheafify J AddCommGrpCat.{u}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{u}] (I : Type u)
    {N : SheafOfModules.{u} R} (e : SheafOfModules.free I ≅ N) :
    IsIso ((SheafOfModules.free.generatingSections I).equivOfIso e).π := by
  change IsIso (((SheafOfModules.free.generatingSections I).ofEpi e.hom).π)
  rw [SheafOfModules.GeneratingSections.ofEpi_π, SheafOfModules.free.generatingSections_π]
  change IsIso (𝟙 (SheafOfModules.free I) ≫ e.hom)
  simpa only [Category.id_comp] using e.isIso_hom

/-- **A biproduct of two finite locally free modules is finite locally free.** Intersect the two
coverings pairwise; over each intersection the two local free bases restrict, and the disjoint
union of the two generating families is a free basis of the biproduct because the free module on
a sum type is the biproduct of the free modules and restriction preserves biproducts. -/
theorem finiteLocallyFree_biprod
    {Y : RingedSpace.{u, u}} (M N : OXMod.{u} Y)
    [HasWeakSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [∀ U : Opens Y.carrier,
      HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over U) AddCommGrpCat.{u}]
    [∀ U : Opens Y.carrier,
      ((Opens.grothendieckTopology Y.carrier).over U).WEqualsLocallyBijective
        AddCommGrpCat.{u}]
    [IsFiniteLocallyFree (R := structureSheafOfRings Y) M]
    [IsFiniteLocallyFree (R := structureSheafOfRings Y) N] :
    IsFiniteLocallyFree (R := structureSheafOfRings Y) (M ⊞ N) := by
  classical
  let hM := (inferInstance : IsFiniteLocallyFree
    (R := structureSheafOfRings Y) M).exists_isFiniteLocallyFreeData
  let hN := (inferInstance : IsFiniteLocallyFree
    (R := structureSheafOfRings Y) N).exists_isFiniteLocallyFreeData
  let q := Classical.choose hM
  let r := Classical.choose hN
  have hq : q.IsLocallyFreeData := (Classical.choose_spec hM).1
  have hr : r.IsLocallyFreeData := (Classical.choose_spec hN).1
  have hqfin : q.IsFiniteType := (Classical.choose_spec hM).2
  have hrfin : r.IsFiniteType := (Classical.choose_spec hN).2
  let V : q.I × r.I → Opens Y.carrier := fun ij => q.X ij.1 ⊓ r.X ij.2
  have hcover : (Opens.grothendieckTopology Y.carrier).CoversTop V := by
    refine (coversTop_iff_forall_exists_mem V).2 fun x => ?_
    obtain ⟨i, hi⟩ := (coversTop_iff_forall_exists_mem _).1 q.coversTop x
    obtain ⟨j, hj⟩ := (coversTop_iff_forall_exists_mem _).1 r.coversTop x
    exact ⟨(i, j), hi, hj⟩
  let e (ij : q.I × r.I) : SheafOfModules.free
      (R := (structureSheafOfRings Y).over (V ij))
      (Sum (q.generators ij.1).I (r.generators ij.2).I) ≅ (M ⊞ N).over (V ij) := by
    let U := V ij
    let eM := locallyFreeIso_restrict M q hq U ij.1 inf_le_left
    let eN := locallyFreeIso_restrict N r hr U ij.2 inf_le_right
    let eFree := freeSumBiprodIso
      ((structureSheafOfRings Y).over U) (q.generators ij.1).I
        (r.generators ij.2).I
    let F := SheafOfModules.pushforward
      (𝟙 ((structureSheafOfRings Y).over U))
    have hpc : PreservesColimitsOfSize.{0, 0} F :=
      (Adjunction.ofIsLeftAdjoint F).leftAdjoint_preservesColimits
    have : PreservesBinaryBiproduct M N F :=
      preservesBinaryBiproduct_of_preservesBinaryCoproduct F
    let eOver := F.mapBiprod M N
    let eMN := biprod.mapIso eM eN
    exact eFree ≪≫ eMN ≪≫ eOver.symm
  let σ : (M ⊞ N).LocalGeneratorsData.{u} := {
    I := q.I × r.I
    X := V
    coversTop := hcover
    generators := fun ij => (SheafOfModules.free.generatingSections _).equivOfIso (e ij)
  }
  have hσ : σ.IsLocallyFreeData := ⟨fun ij => freeGeneratingSectionsEquivOfIso_isIso _ (e ij)⟩
  have hσfin : σ.IsFiniteType := by
    refine ⟨fun ij => ⟨?_⟩⟩
    have := (hqfin.isFiniteType ij.1).finite
    have := (hrfin.isFiniteType ij.2).finite
    change Finite (Sum (q.generators ij.1).I (r.generators ij.2).I)
    infer_instance
  exact ⟨σ, hσ, hσfin⟩

/-! ### `K^b(A)` is triangulated, and the canonical functor -/

section Scheme

attribute [local instance] HasDerivedCategory.standard

/-- **`K^b(A)` is a triangulated subcategory of `K(O_X)`.** The property of being a bounded
complex with finite locally free terms holds of the zero complex, is stable under shift, and is
stable under mapping cones; the last because `(mappingCone f).X i` is `K.X (i + 1) ⊞ L.X i`. -/
@[stacks 0F8I "the homotopy subcategory is triangulated"]
instance boundedFiniteLocallyFreeHomotopyProperty_isTriangulated
    (X : Scheme.{u}) :
    (boundedFiniteLocallyFreeHomotopyProperty X).IsTriangulated := by
  apply HomotopyCategory.isTriangulated_strictMap_quotient
  · exact ⟨⟨⟨0, inferInstance⟩, ⟨0, inferInstance⟩⟩, fun i => finiteLocallyFree_of_isZero X _
      ((HomologicalComplex.eval X.Modules (ComplexShape.up ℤ) i).map_isZero (isZero_zero _))⟩
  · intro E n hE
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · obtain ⟨a, ha⟩ := (CochainComplex.plus_iff X.Modules E).mp hE.1.1
      apply (CochainComplex.plus_iff X.Modules _).mpr
      refine ⟨a - n, ?_⟩
      let : E.IsStrictlyGE a := ha
      exact E.isStrictlyGE_shift a n (a - n) (by omega)
    · obtain ⟨b, hb⟩ := (CochainComplex.minus_iff E).mp hE.1.2
      apply (CochainComplex.minus_iff _).mpr
      refine ⟨b - n, ?_⟩
      let : E.IsStrictlyLE b := hb
      exact E.isStrictlyLE_shift b n (b - n) (by omega)
    · intro i
      change IsFiniteLocallyFree (R := X.ringCatSheaf) (E.X (i + n))
      exact hE.2 (i + n)
  · intro K L f hK hL
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · obtain ⟨a, ha⟩ := (CochainComplex.plus_iff X.Modules K).mp hK.1.1
      obtain ⟨b, hb⟩ := (CochainComplex.plus_iff X.Modules L).mp hL.1.1
      apply (CochainComplex.plus_iff X.Modules _).mpr
      refine ⟨min (a - 1) b, ?_⟩
      let : K.IsStrictlyGE a := ha
      let : L.IsStrictlyGE b := hb
      exact CochainComplex.isStrictlyGE_mappingCone f a b _
    · obtain ⟨a, ha⟩ := (CochainComplex.minus_iff K).mp hK.1.2
      obtain ⟨b, hb⟩ := (CochainComplex.minus_iff L).mp hL.1.2
      apply (CochainComplex.minus_iff _).mpr
      refine ⟨max a b, ?_⟩
      let : K.IsStrictlyLE a := ha
      let : L.IsStrictlyLE b := hb
      exact CochainComplex.isStrictlyLE_mappingCone f a b _
    · intro i
      let Y : RingedSpace.{u, u} := X.toRingedSpace
      let : HasWeakSheafify (Opens.grothendieckTopology Y.carrier) AddCommGrpCat.{u} :=
        inferInstance
      let : (Opens.grothendieckTopology Y.carrier).WEqualsLocallyBijective
          AddCommGrpCat.{u} := inferInstance
      let : ∀ U : Opens Y.carrier,
          HasWeakSheafify ((Opens.grothendieckTopology Y.carrier).over U)
            AddCommGrpCat.{u} := inferInstance
      let : ∀ U : Opens Y.carrier,
          ((Opens.grothendieckTopology Y.carrier).over U).WEqualsLocallyBijective
            AddCommGrpCat.{u} := inferInstance
      let : IsFiniteLocallyFree (R := structureSheafOfRings Y) (K.X (i + 1)) := hK.2 (i + 1)
      let : IsFiniteLocallyFree (R := structureSheafOfRings Y) (L.X i) := hL.2 i
      let M : OXMod.{u} Y := K.X (i + 1)
      let N : OXMod.{u} Y := L.X i
      have hsum : IsFiniteLocallyFree
          (R := structureSheafOfRings Y)
          (M ⊞ N) := finiteLocallyFree_biprod (Y := Y) M N
      let e : (CochainComplex.mappingCone f).X i ≅ M ⊞ N :=
        HomologicalComplex.homotopyCofiber.XIsoBiprod f i (i + 1) (by simp)
      change IsFiniteLocallyFree
        (R := structureSheafOfRings Y) ((CochainComplex.mappingCone f).X i)
      exact IsFiniteLocallyFree.of_iso (h := hsum) e.symm

/-- **The canonical functor `K^b(A) ⥤ D_perf(O_X)`.** It is `DerivedCategory.Qh` restricted to
`K^b(A)`, lifted to the full subcategory of perfect objects along
`Stacks.Perfect.BoundedLocallyFreeComplexes.perfect_of_boundedFiniteLocallyFree`. -/
@[stacks 0F8I "the canonical functor"]
def perfectComplexFunctor (X : Scheme.{u}) :
    BoundedFiniteLocallyFreeHomotopyCategory X ⥤ PerfectDerivedCategory X :=
  ObjectProperty.lift _
    ((boundedFiniteLocallyFreeHomotopyProperty X).ι ⋙ DerivedCategory.Qh)
    (perfect_of_boundedFiniteLocallyFree X)

/-! ### The system `S` of quasi-isomorphisms -/

open ObjectProperty in
/-- **The quasi-isomorphisms of `K^b(A)` form a saturated multiplicative system compatible with
the triangulation.** Both assertions are inherited from the quasi-isomorphisms of the whole
homotopy category `K(O_X)`, of which they are the inverse image along the inclusion of
`K^b(A)`. -/
theorem boundedFiniteLocallyFree_quasiIsoFacts (X : Scheme.{u}) :
    (quasiIsomorphisms X).IsSaturated ∧
      (quasiIsomorphisms X).IsCompatibleWithTriangulation := by
  let P := boundedFiniteLocallyFreeHomotopyProperty X
  let W := HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ)
  have hW : W.IsSaturated :=
    (HomotopyCategory.isSaturated_subcategoryAcyclic_and_quasiIso_and_kernel_eq
      (DerivedCategory.Qh (C := X.Modules))).2.1.1
  have : W.IsCompatibleWithTriangulation := by
    rw [show W = HomotopyCategory.quasiIso X.Modules (ComplexShape.up ℤ) from rfl,
      HomotopyCategory.quasiIso_eq_trW_subcategoryAcyclic]
    infer_instance
  have hres :=
    isSaturated_and_isCompatibleWithTriangulation_inverseImage_ι_and_isLocalizedEquivalence
      P W hW
  exact ⟨hres.1, hres.2.1⟩

/-- **The system `S` of quasi-isomorphisms of `K^b(A)` is saturated.** -/
@[stacks 0F8I "saturation of the quasi-isomorphism system"]
theorem quasiIsomorphisms_isSaturated (X : Scheme.{u}) :
    (quasiIsomorphisms X).IsSaturated :=
  (boundedFiniteLocallyFree_quasiIsoFacts X).1

/-- **The system `S` of quasi-isomorphisms of `K^b(A)` is compatible with the triangulated
structure.** -/
@[stacks 0F8I "compatibility of quasi-isomorphisms with triangulation"]
instance quasiIsomorphisms_isCompatibleWithTriangulation (X : Scheme.{u}) :
    (quasiIsomorphisms X).IsCompatibleWithTriangulation :=
  (boundedFiniteLocallyFree_quasiIsoFacts X).2

end Scheme

end Stacks.Perfect.BoundedLocallyFreeComplexes

end
