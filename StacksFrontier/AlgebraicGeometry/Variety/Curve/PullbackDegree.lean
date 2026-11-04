module

public import StacksFrontier.AlgebraicGeometry.AffineMorphismEuler.Basic
public import StacksFrontier.AlgebraicGeometry.BirationalCurveFinite.Basic
public import StacksFrontier.AlgebraicGeometry.ClosedImmersionEuler.Basic
public import StacksFrontier.AlgebraicGeometry.ComponentMultiplicity.Reduced
public import StacksFrontier.AlgebraicGeometry.CurveEulerBridge.Basic
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.IntegralDevissage
public import StacksFrontier.AlgebraicGeometry.CurveTensorEulerUnit.Symmetry
public import StacksFrontier.AlgebraicGeometry.Divisors.Reflexive.ConstantRank
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionAssociatedPoints
public import StacksFrontier.AlgebraicGeometry.Duality.ProjectionFormulaLocal
public import StacksFrontier.AlgebraicGeometry.EulerCharIso.Basic
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.AlgebraicGeometry.FiniteDirectImageCoherent.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.FunctionFieldDegree
public import StacksFrontier.AlgebraicGeometry.ProperCohomologyFinite.OverFieldProper
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.Degree
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.CoherentFiniteness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorUnitSections
public import StacksCore.Tactic.StacksAttribute

/-!
# The degree of a pullback along a nonconstant morphism of proper curves

Let `k` be a field, let `f : X ⟶ Y` be a nonconstant morphism of proper curves over `k` and let
`ℰ` be a finite locally free `𝒪_Y`-module. Then

`deg(f^*ℰ) = deg(X/Y) · deg(ℰ)`,

where `deg(X/Y) = [R(X) : R(Y)]` is the degree of the extension of function fields and the degree
of a module is its Euler characteristic minus its rank times that of the structure sheaf.

## Main results

The elided prefix throughout is `AlgebraicGeometry`.

* `isDominant_of_not_constant`: a nonconstant morphism of curves over a field is dominant; it
  carries the generic point to the generic point.
* `preimage_genericPoint_of_not_constant`: the fibre of such a morphism over the generic point of
  the target is the generic point of the source.
* `isFinite_of_not_constant`: a nonconstant morphism of proper curves is finite.
* `fiberRank_pushforward_unit_genericPoint_eq_degreeOver`: the rank of `f_*𝒪_X` at the generic
  point of `Y` is `deg(X/Y)`.
* `curveDegree_pullback_eq_degreeOver_mul_of_isFiniteLocallyFree`: [Stacks, Tag 0AYZ] for a
  finite locally free module, taken at its rank at the generic point.
* `curveDegree_pullback_eq_degreeOver_mul`: [Stacks, Tag 0AYZ] at a prescribed constant rank.

## Implementation notes

Several applications are written with `@` and explicit coherence arguments: `Scheme.Modules` is
a `def` for a category of sheaves of modules, so instance search does not reliably cross between
the two spellings of `SheafOfModules.IsCoherent`.

## References

* [Stacks Project, Tag 0AYZ](https://stacks.math.columbia.edu/tag/0AYZ)
* [Stacks Project, Tag 02NY](https://stacks.math.columbia.edu/tag/02NY)
* [Stacks Project, Tag 0AYR](https://stacks.math.columbia.edu/tag/0AYR)
* [Stacks Project, Tag 0AYV](https://stacks.math.columbia.edu/tag/0AYV)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
* [Stacks Project, Tag 01E8](https://stacks.math.columbia.edu/tag/01E8)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 05B8](https://stacks.math.columbia.edu/tag/05B8)
* [Stacks Project, Tag 02O6](https://stacks.math.columbia.edu/tag/02O6)
* [Stacks Project, Tag 05P2](https://stacks.math.columbia.edu/tag/05P2)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace
open Stacks.AlgebraicGeometry.BirationalCurveFinite
open Stacks.AlgebraicGeometry.ComponentDegrees
open Stacks.SheafOfModules.TensorStalkRingedSpace
open scoped TensorProduct

universe u

namespace AlgebraicGeometry

/-! ### Nonconstancy -/

/-- A morphism of curves over a field `k`, commuting with the structure morphisms, is locally of
finite type. -/
theorem locallyOfFiniteType_of_isCurve_comp (k : Type u) [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (.of k)) (πY : Y ⟶ Spec (.of k)) [IsCurve k πX] [IsCurve k πY]
    (f : X ⟶ Y) (hf : f ≫ πY = πX) : LocallyOfFiniteType f :=
  have : LocallyOfFiniteType (f ≫ πY) := hf ▸ inferInstance
  locallyOfFiniteType_of_comp f πY

/-- On a curve over a field, every point other than the generic point is closed. -/
private theorem isClosed_singleton_of_ne_genericPoint (k : Type u) [Field k] {X : Scheme.{u}}
    (πX : X ⟶ Spec (.of k)) [IsCurve k πX] {x : X} (hx : x ≠ genericPoint (X : Type u)) :
    IsClosed ({x} : Set X) :=
  isClosed_singleton_of_notMem_genericPointsOne
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πX))) (by
      rw [genericPointsOne_eq_singleton X (IsCurve.topologicalKrullDim_eq_one (f := πX))]
      simpa using hx)

/-- **A nonconstant morphism of curves over a field carries the generic point to the generic
point.** -/
theorem map_genericPoint_of_not_constant (k : Type u) [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (.of k)) (πY : Y ⟶ Spec (.of k)) [IsCurve k πX] [IsCurve k πY]
    (f : X ⟶ Y) (hnc : ¬ ∃ y : Y, ∀ x : X, f.base x = y) :
    f.base (genericPoint (X : Type u)) = genericPoint (Y : Type u) := by
  by_contra hne
  have hclosed : IsClosed ({f.base (genericPoint (X : Type u))} : Set Y) :=
    isClosed_singleton_of_ne_genericPoint k πY hne
  refine hnc ⟨f.base (genericPoint (X : Type u)), fun z => ?_⟩
  exact Set.mem_singleton_iff.mp
    (((genericPoint_specializes z).map f.continuous).mem_closed hclosed rfl)

/-- **A nonconstant morphism of curves over a field is dominant.** -/
theorem isDominant_of_not_constant (k : Type u) [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (.of k)) (πY : Y ⟶ Spec (.of k)) [IsCurve k πX] [IsCurve k πY]
    (f : X ⟶ Y) (hnc : ¬ ∃ y : Y, ∀ x : X, f.base x = y) : IsDominant f := by
  have hgen := map_genericPoint_of_not_constant k πX πY f hnc
  have hsub : ({genericPoint (Y : Type u)} : Set Y) ⊆ Set.range f.base := by
    rw [Set.singleton_subset_iff, ← hgen]
    exact Set.mem_range_self _
  exact ⟨dense_iff_closure_eq.mpr (Set.eq_univ_of_subset (closure_mono hsub)
    (genericPoint_closure (α := (Y : Type u))))⟩

/-- **The fibre of a nonconstant morphism of proper curves over the generic point of the target
is the generic point of the source.** -/
theorem preimage_genericPoint_of_not_constant (k : Type u) [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (.of k)) (πY : Y ⟶ Spec (.of k)) [IsCurve k πX] [IsCurve k πY]
    [IsProper πX] [IsProper πY] (f : X ⟶ Y) (hf : f ≫ πY = πX)
    (hnc : ¬ ∃ y : Y, ∀ x : X, f.base x = y) :
    f.base ⁻¹' ({genericPoint (Y : Type u)} : Set Y) = {genericPoint (X : Type u)} := by
  have : IsProper f := isProper_of_comp_eq hf
  refine Set.Subset.antisymm (fun z hz => ?_) ?_
  · by_contra hzne
    have hzclosed : IsClosed ({z} : Set X) := isClosed_singleton_of_ne_genericPoint k πX hzne
    have himage : IsClosed ({genericPoint (Y : Type u)} : Set Y) := by
      have h := f.isClosedMap _ hzclosed
      rwa [Set.image_singleton, Set.mem_singleton_iff.mp hz] at h
    have hone : topologicalKrullDim (closure ({genericPoint (Y : Type u)} : Set Y)) = 1 :=
      (mem_genericPointsOne_iff.mp (genericPoint_self_mem_genericPointsOne Y
        (IsCurve.topologicalKrullDim_eq_one (f := πY)))).2
    rw [himage.closure_eq] at hone
    have hzero : topologicalKrullDim ({genericPoint (Y : Type u)} : Set Y) ≤ 0 :=
      topologicalKrullDim_zero_of_discreteTopology _
    rw [hone] at hzero
    norm_num at hzero
  · simpa using map_genericPoint_of_not_constant k πX πY f hnc

/-- **A nonconstant morphism of proper curves over a field is finite.** -/
theorem isFinite_of_not_constant (k : Type u) [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (.of k)) (πY : Y ⟶ Spec (.of k)) [IsCurve k πX] [IsCurve k πY]
    [IsProper πX] [IsProper πY] (f : X ⟶ Y) (hf : f ≫ πY = πX)
    (hnc : ¬ ∃ y : Y, ∀ x : X, f.base x = y) : IsFinite f := by
  have hbij : Set.BijOn f.base (genericPointsOne X) (genericPointsOne Y) := by
    rw [genericPointsOne_eq_singleton X (IsCurve.topologicalKrullDim_eq_one (f := πX)),
      genericPointsOne_eq_singleton Y (IsCurve.topologicalKrullDim_eq_one (f := πY))]
    exact Set.bijOn_singleton.mpr (map_genericPoint_of_not_constant k πX πY f hnc)
  exact isFinite_of_bijOn_genericPointsOne k πX πY
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πX)))
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πY))) f hf hbij

/-! ### The rank of `f_*𝒪_X` at the generic point -/

/-- **At a point whose local ring is a field the fibre rank is the dimension of the stalk** over
that local ring. -/
theorem fiberRank_eq_finrank_stalk_of_isField {Z : Scheme.{u}} (F : Z.Modules) (z : Z)
    (h : IsField (Z.presheaf.stalk z)) :
    let : Module (Z.presheaf.stalk z) (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf z) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Z.presheaf) F.val z
    Scheme.Modules.fiberRank F z =
      Module.finrank (Z.presheaf.stalk z)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf z) := by
  let : Module (Z.presheaf.stalk z)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf z) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Z.presheaf) F.val z
  let : Module (Z.presheaf.stalk z) (F.presheaf.stalk z) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Z.presheaf) F.val z
  let : Algebra (Z.presheaf.stalk z) (Z.residueField z) := (Z.residue z).hom.toAlgebra
  let : Field (Z.presheaf.stalk z) := h.toField
  have : Module.Free (Z.presheaf.stalk z)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf z) :=
    Module.Free.of_divisionRing _ _
  have : Module.Free (Z.presheaf.stalk z) (F.presheaf.stalk z) :=
    Module.Free.of_divisionRing _ _
  exact Module.finrank_baseChange

/-- **The local ring of an integral scheme at its generic point is a field.** -/
@[ega "I 8.2.1" "partial", ega "IV 8.1.2" "partial"]
theorem isField_stalk_genericPoint (Z : Scheme.{u}) [IsIntegral Z] :
    IsField (Z.presheaf.stalk (genericPoint (Z : Type u))) :=
  isField_stalk_of_closure_mem_irreducibleComponents Z _
    (by simp [irreducibleComponents_eq_singleton])

/-- For `h : g.base z = w`, the dimension of the stalk of `Z` at `z` over the stalk of `W` at
`g.base z` equals its dimension over the stalk of `W` at `w`, the module structures being given by
the stalk map of `g` transported along `h`. -/
private theorem finrank_compHom_transport {Z W : Scheme.{u}} (g : Z ⟶ W) (z : Z) {w : W}
    (h : g.base z = w) :
    let : Module (W.presheaf.stalk (g.base z)) (Z.presheaf.stalk z) :=
      Module.compHom _ (g.stalkMap z).hom
    let : Algebra (W.presheaf.stalk w) (Z.presheaf.stalk z) :=
      (h ▸ g.stalkMap z).hom.toAlgebra
    Module.finrank (W.presheaf.stalk (g.base z)) (Z.presheaf.stalk z) =
      Module.finrank (W.presheaf.stalk w) (Z.presheaf.stalk z) := by
  cases h
  rfl

/-- **The degree `[R(X) : R(Y)]` is the dimension of the stalk at the generic point of the source
over the stalk at its image.** -/
theorem finrank_stalk_genericPoint_eq_degreeOver {Z W : Scheme.{u}} (g : Z ⟶ W)
    [IsIntegral Z] [IsIntegral W] [LocallyOfFiniteType g] [IsDominant g]
    (hgen : g.base (genericPoint (Z : Type u)) = genericPoint (W : Type u)) :
    let : Module (W.presheaf.stalk (g.base (genericPoint (Z : Type u))))
        (Z.presheaf.stalk (genericPoint (Z : Type u))) :=
      Module.compHom _ (g.stalkMap (genericPoint (Z : Type u))).hom
    Module.finrank (W.presheaf.stalk (g.base (genericPoint (Z : Type u))))
        (Z.presheaf.stalk (genericPoint (Z : Type u))) = degreeOver g := by
  let : Algebra W.functionField Z.functionField :=
    (hgen ▸ g.stalkMap (genericPoint (Z : Type u))).hom.toAlgebra
  rw [degreeOver_eq_finrank g rfl]
  exact finrank_compHom_transport g (genericPoint (Z : Type u)) hgen

/-- **The rank of `f_*𝒪_X` at the generic point of `Y` is the degree `[R(X) : R(Y)]`** for a
finite dominant morphism `f : X ⟶ Y` of integral schemes whose fibre over the generic point of
`Y` is the generic point of `X`. -/
theorem fiberRank_pushforward_unit_genericPoint_eq_degreeOver_of_isFinite {X Y : Scheme.{u}}
    [IsIntegral X] [IsIntegral Y] (f : X ⟶ Y) [IsFinite f] [LocallyOfFiniteType f]
    [IsDominant f] (hgen : f.base (genericPoint (X : Type u)) = genericPoint (Y : Type u))
    (hpre : f.base ⁻¹' ({genericPoint (Y : Type u)} : Set Y) = {genericPoint (X : Type u)}) :
    Scheme.Modules.fiberRank
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
        (genericPoint (Y : Type u)) = degreeOver f := by
  have hfiber : f.base ⁻¹' ({f.base (genericPoint (X : Type u))} : Set Y) =
      {genericPoint (X : Type u)} := by
    rwa [hgen]
  let : Module (X.presheaf.stalk (genericPoint (X : Type u)))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit X.ringCatSheaf).val.presheaf (genericPoint (X : Type u))) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) (SheafOfModules.unit X.ringCatSheaf).val (genericPoint (X : Type u))
  let : Module (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        (SheafOfModules.unit X.ringCatSheaf).val.presheaf (genericPoint (X : Type u))) :=
    Module.compHom _ (f.stalkMap (genericPoint (X : Type u))).hom
  let : Module (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
      (X.presheaf.stalk (genericPoint (X : Type u))) :=
    Module.compHom _ (f.stalkMap (genericPoint (X : Type u))).hom
  let : Module (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
      (TopCat.Presheaf.stalk (C := Ab.{u})
        ((Scheme.Modules.pushforward f).obj
          (SheafOfModules.unit X.ringCatSheaf)).val.presheaf
        (f.base (genericPoint (X : Type u)))) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf)
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)).val
      (f.base (genericPoint (X : Type u)))
  have hfieldY : IsField (Y.presheaf.stalk (f.base (genericPoint (X : Type u)))) := by
    rw [hgen]
    exact isField_stalk_genericPoint Y
  obtain ⟨e05⟩ :=
    AlgebraicGeometry.stalk_isomorphic_pushforward_of_finite_singleton_fiber f
      (genericPoint (X : Type u)) hfiber (SheafOfModules.unit X.ringCatSheaf)
  have h1 := fiberRank_eq_finrank_stalk_of_isField
    ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
    (f.base (genericPoint (X : Type u))) hfieldY
  have h2 : Module.finrank (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf (genericPoint (X : Type u))) =
      Module.finrank (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pushforward f).obj
            (SheafOfModules.unit X.ringCatSheaf)).val.presheaf
          (f.base (genericPoint (X : Type u)))) :=
    LinearEquiv.finrank_eq e05.toLinearEquiv
  have h3 : Module.finrank (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
        (TopCat.Presheaf.stalk (C := Ab.{u})
          (SheafOfModules.unit X.ringCatSheaf).val.presheaf (genericPoint (X : Type u))) =
      Module.finrank (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
        (X.presheaf.stalk (genericPoint (X : Type u))) := by
    let : Module (X.presheaf.stalk (genericPoint (X : Type u)))
        ((Stacks.Divisors.structureModule X).presheaf.stalk (genericPoint (X : Type u))) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) (Stacks.Divisors.structureModule X).val (genericPoint (X : Type u))
    let : Module (Y.presheaf.stalk (f.base (genericPoint (X : Type u))))
        ((Stacks.Divisors.structureModule X).presheaf.stalk (genericPoint (X : Type u))) :=
      Module.compHom _ (f.stalkMap (genericPoint (X : Type u))).hom
    refine LinearEquiv.finrank_eq ?_
    let e := (Stacks.Divisors.unitStalkLinearEquiv (X := X) (genericPoint (X : Type u))).symm
    exact
      { toFun := e
        map_add' := e.map_add
        map_smul' := fun a m =>
          e.map_smul ((f.stalkMap (genericPoint (X : Type u))).hom a) m
        invFun := e.symm
        left_inv := e.left_inv
        right_inv := e.right_inv }
  rw [← hgen]
  exact h1.trans (h2.symm.trans (h3.trans (finrank_stalk_genericPoint_eq_degreeOver f hgen)))

/-- **The rank of `f_*𝒪_X` at the generic point of `Y` is the degree `[R(X) : R(Y)]`** for a
nonconstant morphism `f : X ⟶ Y` of proper curves over a field. -/
theorem fiberRank_pushforward_unit_genericPoint_eq_degreeOver (k : Type u) [Field k]
    {X Y : Scheme.{u}} (πX : X ⟶ Spec (.of k)) (πY : Y ⟶ Spec (.of k))
    [IsCurve k πX] [IsCurve k πY] [IsProper πX] [IsProper πY]
    (f : X ⟶ Y) (hf : f ≫ πY = πX) (hnc : ¬ ∃ y : Y, ∀ x : X, f.base x = y) :
    Scheme.Modules.fiberRank
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))
        (genericPoint (Y : Type u)) =
      @degreeOver X Y f _ _ (locallyOfFiniteType_of_isCurve_comp k πX πY f hf)
        (isDominant_of_not_constant k πX πY f hnc) :=
  have : IsFinite f := isFinite_of_not_constant k πX πY f hf hnc
  have : LocallyOfFiniteType f := locallyOfFiniteType_of_isCurve_comp k πX πY f hf
  have : IsDominant f := isDominant_of_not_constant k πX πY f hnc
  fiberRank_pushforward_unit_genericPoint_eq_degreeOver_of_isFinite f
    (map_genericPoint_of_not_constant k πX πY f hnc)
    (preimage_genericPoint_of_not_constant k πX πY f hf hnc)

/-! ### The degree formula -/

/-- Let `k` be a field, let `f : X ⟶ Y` be a nonconstant morphism of proper curves over `k` and
let `ℰ` be a finite locally free `𝒪_Y`-module of constant rank `n`. Then

`deg(f^*ℰ) = deg(X/Y)·deg(ℰ)`,

where `deg(X/Y) = [R(X) : R(Y)]` is `AlgebraicGeometry.degreeOver` ([Stacks, Tag 02NY]) and `deg`
is `AlgebraicGeometry.curveDegree` ([Stacks, Tag 0AYR]). -/
@[stacks 0AYZ]
theorem curveDegree_pullback_eq_degreeOver_mul (k : Type u) [Field k] {X Y : Scheme.{u}}
    (πX : X ⟶ Spec (.of k)) (πY : Y ⟶ Spec (.of k))
    [IsCurve k πX] [IsCurve k πY] [IsProper πX] [IsProper πY]
    (f : X ⟶ Y) (hf : f ≫ πY = πX) (hnc : ¬ ∃ y : Y, ∀ x : X, f.base x = y)
    (E : Y.Modules) (n : ℕ) [SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E n] :
    @curveDegree k _ X πX _ (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πX)))
        ((Scheme.Modules.pullback f).obj E) n (isFiniteLocallyFreeOfRank_pullback f E n) =
      (@degreeOver X Y f _ _ (locallyOfFiniteType_of_isCurve_comp k πX πY f hf)
          (isDominant_of_not_constant k πX πY f hnc) : ℤ) *
        curveDegree k πY (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πY))) E n := by
  subst hf
  have : IsFinite f := isFinite_of_not_constant k (f ≫ πY) πY f rfl hnc
  have : IsLocallyNoetherian Y :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isLocallyNoetherian_of_isProper_over_field k πY
  let : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u}
      ((Scheme.Modules.pullback f).obj E) n := isFiniteLocallyFreeOfRank_pullback f E n
  have hOX : SheafOfModules.IsCoherent (SheafOfModules.unit X.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k (f ≫ πY)
  have hOY : SheafOfModules.IsCoherent (SheafOfModules.unit Y.ringCatSheaf) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_unit k πY
  have hE : SheafOfModules.IsCoherent E :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k πY E n
  have hQ : SheafOfModules.IsCoherent ((Scheme.Modules.pullback f).obj E) :=
    Stacks.AlgebraicGeometry.CurveEulerBridge.isCoherent_of_isFiniteLocallyFreeOfRank k (f ≫ πY)
      ((Scheme.Modules.pullback f).obj E) n
  have hP : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) :=
    @Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
      X Y f _ _ _ hOX
  have hPQ : SheafOfModules.IsCoherent
      ((Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj E)) :=
    @Stacks.AlgebraicGeometry.FiniteDirectImageCoherent.isCoherent_pushforward_of_isFinite
      X Y f _ _ _ hQ
  have hUqc : (SheafOfModules.unit X.ringCatSheaf).IsQuasicoherent := inferInstance
  have hEqc : E.IsQuasicoherent := @_root_.isQuasicoherent_of_isCoherent _ _ _ E hE
  have hQqc : ((Scheme.Modules.pullback f).obj E).IsQuasicoherent :=
    @_root_.isQuasicoherent_of_isCoherent _ _ _ _ hQ
  obtain ⟨hT, hAYV⟩ :=
    @exists_eulerCharacteristic_tensorSheaf_eq_fiberRank_mul_curveDegree_add_of_h02O6
      k _ Y πY _ _ E n _
      (fun G _ _ _ _ hG m =>
        forall_finiteDimensional_cohomologyOverField_of_isProper k πY G hG m)
      (fun m => forall_finiteDimensional_cohomologyOverField_of_isProper k πY _ hOY m)
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) hP
  have hproj : ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj
          ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))).obj E) :
          Y.Modules) ≅
      (Scheme.Modules.pushforward f).obj ((Scheme.Modules.pullback f).obj E) :=
    Stacks.AlgebraicGeometry.ProjectionFormula.projectionFormulaIsoOfQuasicoherent f
        (SheafOfModules.unit X.ringCatSheaf) E hUqc hEqc ≪≫
      (Scheme.Modules.pushforward f).mapIso
        (SheafOfModules.tensorSheafUnitLeftIso X.toRingedSpace
          ((Scheme.Modules.pullback f).obj E))
  have hPEcoh : SheafOfModules.IsCoherent (((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))).obj E) :=
    @SheafOfModules.tensorSheaf_isCoherent Y.toRingedSpace _ E hP hE
  have htens : @eulerCharacteristic k _ Y πY _
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨Y.toRingedSpace.presheaf, Y.toRingedSpace.IsSheaf⟩).obj E).obj
            ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf))) hT =
      @eulerCharacteristic k _ X (f ≫ πY) _ ((Scheme.Modules.pullback f).obj E) hQ := by
    have h1 := @eulerCharacteristic_tensorSheaf_comm k _ Y πY _ E
      ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) hE hP
    have h2 := @eulerCharacteristic_eq_of_iso k _ Y πY _ _ _ hPEcoh hPQ hproj
    have h3 := @eulerCharacteristic_pushforward_of_isAffineHom k _ X Y f _ πY _ _
      ((Scheme.Modules.pullback f).obj E) hQqc hQ hPQ
    exact h1.trans (h2.trans h3)
  have hbase : @eulerCharacteristic k _ Y πY _
        ((Scheme.Modules.pushforward f).obj (SheafOfModules.unit X.ringCatSheaf)) hP =
      @eulerCharacteristic k _ X (f ≫ πY) _ (SheafOfModules.unit X.ringCatSheaf) hOX :=
    @eulerCharacteristic_pushforward_of_isAffineHom k _ X Y f _ πY _ _
      (SheafOfModules.unit X.ringCatSheaf) hUqc hOX hP
  rw [@curveDegree_eq_eulerCharacteristic_sub k _ X (f ≫ πY) _
    (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := (f ≫ πY))))
    ((Scheme.Modules.pullback f).obj E) n _ hQ hOX,
    ← htens, hAYV, hbase,
    fiberRank_pushforward_unit_genericPoint_eq_degreeOver k (f ≫ πY) πY f rfl hnc]
  ring

/-- Let `k` be a field, let `f : X ⟶ Y` be a nonconstant morphism of proper curves over `k` and
let `ℰ` be a finite locally free `𝒪_Y`-module. Then

`deg(f^*ℰ) = deg(X/Y)·deg(ℰ)`,

where `deg(X/Y) = [R(X) : R(Y)]` is `AlgebraicGeometry.degreeOver` ([Stacks, Tag 02NY]) and `deg`
is `AlgebraicGeometry.curveDegree` ([Stacks, Tag 0AYR]), both degrees taken at the fibre rank of
`ℰ` at the generic point of `Y`. -/
@[stacks 0AYZ, sga "6 X 4.4" "(4.4.3), special case"]
theorem curveDegree_pullback_eq_degreeOver_mul_of_isFiniteLocallyFree (k : Type u) [Field k]
    {X Y : Scheme.{u}} (πX : X ⟶ Spec (.of k)) (πY : Y ⟶ Spec (.of k))
    [IsCurve k πX] [IsCurve k πY] [IsProper πX] [IsProper πY]
    (f : X ⟶ Y) (hf : f ≫ πY = πX) (hnc : ¬ ∃ y : Y, ∀ x : X, f.base x = y)
    (E : Y.Modules)
    [SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := Y.ringCatSheaf) E] :
    letI _hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E
        (Scheme.Modules.fiberRank E (genericPoint (Y : Type u))) :=
      Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq E
        (Scheme.Modules.fiberRank E (genericPoint (Y : Type u)))
        (genericPoint (Y : Type u)) rfl
    @curveDegree k _ X πX _ (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πX)))
        ((Scheme.Modules.pullback f).obj E)
        (Scheme.Modules.fiberRank E (genericPoint (Y : Type u)))
        (isFiniteLocallyFreeOfRank_pullback f E
          (Scheme.Modules.fiberRank E (genericPoint (Y : Type u)))) =
      (@degreeOver X Y f _ _ (locallyOfFiniteType_of_isCurve_comp k πX πY f hf)
          (isDominant_of_not_constant k πX πY f hnc) : ℤ) *
        curveDegree k πY (le_of_eq (IsCurve.topologicalKrullDim_eq_one (f := πY))) E
          (Scheme.Modules.fiberRank E (genericPoint (Y : Type u))) :=
  have _hrank : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} E
      (Scheme.Modules.fiberRank E (genericPoint (Y : Type u))) :=
    Scheme.Modules.isFiniteLocallyFreeOfRank_of_fiberRank_eq E
      (Scheme.Modules.fiberRank E (genericPoint (Y : Type u)))
      (genericPoint (Y : Type u)) rfl
  curveDegree_pullback_eq_degreeOver_mul k πX πY f hf hnc E
    (Scheme.Modules.fiberRank E (genericPoint (Y : Type u)))

end AlgebraicGeometry

end
