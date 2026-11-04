module

public import StacksFrontier.AlgebraicGeometry.Perfect.PerfectKGroupRing
public import StacksFrontier.AlgebraicGeometry.Perfect.VectorBundleKGroup
public import StacksFrontier.Homology.TensorComplex.SingleBifunctorTensor
public import StacksFrontier.Topology.Sheaves.Cohomology.KFlat.OnARingedSpace
public import StacksFrontier.Topology.Sheaves.Cohomology.PseudoCoherence.ModuleInDegreeZero
public import Mathlib.Algebra.Homology.DerivedCategory.SingleTriangle
public import Mathlib.Algebra.Homology.Embedding.CochainComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# From vector bundles to perfect complexes

Let `X` be a scheme. A finite locally free `𝒪_X`-module, placed in degree zero, is a perfect
object of `D(𝒪_X)`, and the assignment `[ℰ] ↦ [ℰ[0]]` is the unique ring homomorphism
`K₀(Vect(X)) ⟶ K₀(D_perf(𝒪_X))` taking those values.

## Main results

* `AlgebraicGeometry.isPerfect_singleFunctor_of_isFiniteLocallyFree`: a finite locally free
  module in degree zero is a perfect object of the derived category.
* `AlgebraicGeometry.kFlat_single_of_isFiniteLocallyFree`: a finite locally free module in
  degree zero is a K-flat complex.
* `AlgebraicGeometry.nonempty_derivedTensorSingleIso`: the derived tensor product of two
  modules in degree zero, the second finite locally free, is their tensor product in degree
  zero.
* `AlgebraicGeometry.existsUnique_comparisonRingHom` ([stacks 0FDK]): the unique ring
  homomorphism `K₀(Vect(X)) ⟶ K₀(D_perf(𝒪_X))` sending the class of a finite locally free
  module to the class of that module in degree zero.

## Implementation notes

Perfectness of `ℰ[0]` is the source's: a finite locally free module is, over each member of a
covering, a finite free module, and a finite free module in degree zero is strictly perfect
(`StrictlyPerfect.isStrictlyPerfect_single` at
`StrictlyPerfect.isDirectSummandOfFiniteFree_free`). The local trivialisation used is the one
packaged by `SheafOfModules.LocalGeneratorsData.IsLocallyFreeData`, carried from the slice
category over the open to the open subspace by `TopologicalSpace.Opens.sheafOfModulesEquivOver`.

Additivity of `ℰ ↦ [ℰ[0]]` is the single triangle of a short exact sequence
(`CategoryTheory.ShortComplex.ShortExact.singleTriangle_distinguished`), read inside the
perfect objects by `CategoryTheory.Pretriangulated.K0.cls_eq_add_of_distinguished_of_prop`.
That the additive group of the Grothendieck *ring* of
`AlgebraicGeometry.RingedSpace.exists_derivedTensorProduct_commRing` is the additive group
`K₀` already has is `K0.TensorStructure.commRing_toAddCommGroup`, true by `rfl`, so the
additive map is built once and no transport between two additive structures is needed.

Multiplicativity needs the derived tensor product of two finite locally free modules in degree
zero to be their tensor product in degree zero. A finite locally free module is flat, so in
degree zero it is a K-flat complex (Tag 06YQ), and then the one-sided K-flat comparison of the
derived tensor product computes it as the total tensor complex of two complexes concentrated in
degree zero, which is `HomologicalComplex.mapBifunctorSingleIso`.

The two spellings of "module in degree zero" in the derived category —
`DerivedCategory.singleFunctor` and `DerivedCategory.Q` of `CochainComplex.singleFunctor` — are
isomorphic but not equal, by `DerivedCategory.singleFunctorIsoCompQ`. The statements below use
the first, which is the one the single triangle of a short exact sequence is stated at, and
cross to the second only where the comparison of the derived tensor product with the total
tensor complex requires it.

## References

* [Stacks Project, Tag 0FDK](https://stacks.math.columbia.edu/tag/0FDK)
* [Stacks Project, Tag 08CM](https://stacks.math.columbia.edu/tag/08CM)
* [Stacks Project, Tag 06YQ](https://stacks.math.columbia.edu/tag/06YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open AlgebraicGeometry StrictlyPerfect
open Stacks.SheafOfModules.DerivedMonoidal
open Stacks.Cohomology.PerfectComplexes
open Stacks.FiniteLocallyFree
open scoped ZeroObject

universe u d

namespace AlgebraicGeometry

/-- The derived category of `𝒪_X`-modules on a scheme, at Mathlib's
`AlgebraicGeometry.Scheme.Modules` spelling of that category. It is the same category as
`Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf`, by `rfl`, but instance search
does not cross the two spellings: their sheaves of rings are
`AlgebraicGeometry.Scheme.ringCatSheaf` and `Stacks.SheafOfModules.Tensor.ringSheaf`
respectively. Its priority is low, for the same reason as that of
`AlgebraicGeometry.RingedSpace.hasDerivedCategoryOXMod`: it must never be preferred to a
derived category a consumer has already fixed on `AlgebraicGeometry.Scheme.Modules`. -/
instance (priority := low) hasDerivedCategorySchemeModules (X : Scheme.{u})
    [HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf)] :
    HasDerivedCategory.{d} X.Modules :=
  inferInstanceAs (HasDerivedCategory.{d}
    (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf))

variable (X : Scheme.{u})
  [HasDerivedCategory.{d} (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf)]

/-! ### Finite locally free modules in degree zero are perfect -/

omit [HasDerivedCategory.{d}
  (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf)] in
/-- **A finite locally free module in degree zero is a perfect complex.** Over each member `U`
of a covering on which `ℰ` is finite free, the restriction of `ℰ[0]` receives an isomorphism
from the complex with that finite free module in degree zero, which is strictly perfect. -/
theorem isPerfectComplex_single_of_isFiniteLocallyFree (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    IsPerfectComplex (X := X.toRingedSpace)
      ((CochainComplex.singleFunctor X.Modules 0).obj M) := by
  classical
  obtain ⟨q, hq, hfin⟩ := hM.exists_isFiniteLocallyFreeData
  refine ⟨q.I, q.X, (Opens.coversTop_iff _ _).mp q.coversTop, fun i => ?_⟩
  have hfinI : Finite (q.generators i).I := (hfin.isFiniteType i).finite
  let U : TopologicalSpace.Opens X.toRingedSpace.carrier := q.X i
  let Y : RingedSpace.{u, u} := X.toRingedSpace.restrict U.isOpenEmbedding
  let F : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace ⥤ StrictlyPerfect.OXMod.{u, u} Y :=
    AlgebraicGeometry.RingedSpace.PseudoCoherence.restrictModules X.toRingedSpace U
  let T :=
    (U.sheafOfModulesEquivOver.{u} (StrictlyPerfect.structureSheafOfRings X.toRingedSpace)).functor
  let O : StrictlyPerfect.OXMod.{u, u} X.toRingedSpace ⥤
      SheafOfModules.{u} ((StrictlyPerfect.structureSheafOfRings X.toRingedSpace).over U) :=
    SheafOfModules.overFunctor (StrictlyPerfect.structureSheafOfRings X.toRingedSpace) U
  let e₁ : SheafOfModules.free (R := StrictlyPerfect.structureSheafOfRings Y)
      (q.generators i).I ≅
      T.obj (SheafOfModules.free
        (R := (StrictlyPerfect.structureSheafOfRings X.toRingedSpace).over U)
        (q.generators i).I) :=
    SheafOfModules.mapFreeIso T _ (Iso.refl _)
  let e₂ : T.obj (SheafOfModules.free
      (R := (StrictlyPerfect.structureSheafOfRings X.toRingedSpace).over U)
      (q.generators i).I) ≅ T.obj (O.obj M) :=
    T.mapIso (@asIso _ _ _ _ _ (hq.isIso i))
  let e₃ : T.obj (O.obj M) ≅ F.obj M := Iso.refl _
  let e : SheafOfModules.free (R := StrictlyPerfect.structureSheafOfRings Y)
      (q.generators i).I ≅ F.obj M := e₁ ≪≫ e₂ ≪≫ e₃
  let P : CochainComplex (StrictlyPerfect.OXMod.{u, u} Y) ℤ :=
    (CochainComplex.singleFunctor (StrictlyPerfect.OXMod.{u, u} Y) 0).obj
      (SheafOfModules.free (R := StrictlyPerfect.structureSheafOfRings Y) (q.generators i).I)
  let eP : P ≅ (F.mapHomologicalComplex (ComplexShape.up ℤ)).obj
      ((CochainComplex.singleFunctor X.Modules 0).obj M) :=
    (CochainComplex.singleFunctor (StrictlyPerfect.OXMod.{u, u} Y) 0).mapIso e ≪≫
      ((HomologicalComplex.singleMapHomologicalComplex F (ComplexShape.up ℤ) 0).app M).symm
  exact ⟨P, isStrictlyPerfect_single
    (AlgebraicGeometry.RingedSpace.isDirectSummandOfFiniteFree_free Y (q.generators i).I) 0,
    eP.hom, inferInstance⟩

/-- **A finite locally free module in degree zero is a perfect object of `D(𝒪_X)`.** -/
theorem isPerfect_singleFunctor_of_isFiniteLocallyFree (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj M) :=
  ⟨(CochainComplex.singleFunctor X.Modules 0).obj M,
    isPerfectComplex_single_of_isFiniteLocallyFree X M hM,
    ⟨((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app M).symm⟩⟩

/-! ### Finite locally free modules in degree zero are K-flat -/

omit [HasDerivedCategory.{d}
  (Stacks.DerivedTensor.RingedSite.Modules X.toRingedSpace.sheaf)] in
/-- **A finite locally free module in degree zero is a K-flat complex.** It is bounded above and
its only possibly nonzero term is flat, so Tag 06YQ applies. -/
theorem kFlat_single_of_isFiniteLocallyFree (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    Stacks.SheafOfModules.KFlat.KFlat X.toRingedSpace.sheaf
      ((CochainComplex.singleFunctor X.Modules 0).obj M) := by
  refine Stacks.SheafOfModules.kFlat_of_boundedAbove_of_flat (R := X.toRingedSpace.sheaf) _
    ⟨0, inferInstanceAs (CochainComplex.IsStrictlyLE
      ((HomologicalComplex.single X.Modules
        (ComplexShape.up ℤ) 0).obj M) 0)⟩ fun i => ?_
  by_cases hi : i = 0
  · subst hi
    exact @Scheme.Modules.isFlat_of_isFiniteLocallyFree X M hM
  · have hzero : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (((CochainComplex.singleFunctor X.Modules 0).obj M).X i) :=
      @IsFiniteLocallyFree.of_iso.{u, u, u} _ _ _ _ _ _ (0 : X.Modules) _
        ((isZero_zero X.Modules).iso
          (HomologicalComplex.isZero_single_obj_X (ComplexShape.up ℤ) 0 M i hi))
        (VectorBundleKZero.isFiniteLocallyFree_zero X)
    exact @Scheme.Modules.isFlat_of_isFiniteLocallyFree X _ hzero

/-! ### The derived tensor product of two modules in degree zero -/

variable (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct X.toRingedSpace.sheaf)

/-- **The derived tensor product of two modules in degree zero, the second finite locally free,
is their tensor product in degree zero.** The second factor is a K-flat complex, so the
one-sided K-flat comparison of the derived tensor product computes it as the total tensor
complex of the two, and that total complex is the tensor product in degree zero. -/
theorem nonempty_derivedTensorSingleIso (M N : X.Modules)
    (hN : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) N) :
    Nonempty ((T.tensor.obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj M)).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj N) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj
        (Scheme.Modules.tensorObjRingedSpace X M N)) := by
  let a := (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app M
  let b := (DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app N
  exact ⟨(T.tensor.mapIso a).app _ ≪≫
    (T.tensor.obj ((DerivedCategory.Q (C := X.Modules)).obj
      ((CochainComplex.singleFunctor X.Modules 0).obj M))).mapIso b ≪≫
    T.comparisonRight _ _ (kFlat_single_of_isFiniteLocallyFree X N hN) ≪≫
    (DerivedCategory.Q (C := X.Modules)).mapIso
      (HomologicalComplex.mapBifunctorSingleIso
        (Stacks.SheafOfModules.Tensor.sheafTensor X.toRingedSpace.sheaf) M N) ≪≫
    ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app
      (Scheme.Modules.tensorObjRingedSpace X M N)).symm⟩

/-! ### The comparison homomorphism -/

/-- The class in `K₀(D_perf(𝒪_X))` of a finite locally free module placed in degree zero, as a
function of the module, extended by zero to all sheaves of modules. -/
def singleClassOf (M : X.Modules) :
    K0 (ObjectProperty.FullSubcategory
      (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} (X := X.toRingedSpace))) :=
  @dite _ (IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) (Classical.dec _)
    (fun hM => K0.cls ⟨(DerivedCategory.singleFunctor X.Modules 0).obj M,
      isPerfect_singleFunctor_of_isFiniteLocallyFree X M hM⟩)
    (fun _ => 0)

/-- On a finite locally free module the comparison function is the class of that module placed
in degree zero. -/
theorem singleClassOf_of_isFiniteLocallyFree (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M)
    (h : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj M)) :
    singleClassOf X M =
      K0.cls ⟨(DerivedCategory.singleFunctor X.Modules 0).obj M, h⟩ :=
  dite_eq_left hM

/-- Off the finite locally free modules the comparison function is zero. -/
theorem singleClassOf_eq_zero_of_not_isFiniteLocallyFree (M : X.Modules)
    (hM : ¬ IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M) :
    singleClassOf X M = 0 :=
  dite_eq_right hM

/-- **A short exact sequence of finite locally free modules is additive on the classes of the
modules in degree zero.** The single triangle of the short exact sequence is distinguished and
has its three vertices among the perfect objects. -/
theorem clsSingle_eq_add_of_shortExact {E F G : X.Modules}
    (f : E ⟶ F) (g : F ⟶ G) (w : f ≫ g = 0) (hmono : Mono f) (hepi : Epi g)
    (hexact : (ShortComplex.mk f g w).Exact)
    (hE : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj E))
    (hF : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj F))
    (hG : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)) :
    K0.cls (⟨(DerivedCategory.singleFunctor X.Modules 0).obj F, hF⟩ :
        ObjectProperty.FullSubcategory
          (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} (X := X.toRingedSpace))) =
      K0.cls ⟨(DerivedCategory.singleFunctor X.Modules 0).obj E, hE⟩ +
        K0.cls ⟨(DerivedCategory.singleFunctor X.Modules 0).obj G, hG⟩ :=
  have := hmono
  have := hepi
  have hS : (ShortComplex.mk f g w).ShortExact := ⟨hexact⟩
  K0.cls_eq_add_of_distinguished_of_prop
    (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} (X := X.toRingedSpace)) hE hF hG
    ((DerivedCategory.singleFunctor X.Modules 0).map f)
    ((DerivedCategory.singleFunctor X.Modules 0).map g) hS.singleδ
    hS.singleTriangle_distinguished

/-- The function `ℰ ↦ [ℰ[0]]` is additive on a short exact sequence `0 → E → F → G → 0` of
finite locally free modules: the class of `F` is the sum of the classes of `E` and `G`. -/
theorem singleClassOf_eq_add_of_shortExact {E F G : X.Modules} (f : E ⟶ F) (g : F ⟶ G)
    (w : f ≫ g = 0) (hE : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hF : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) F)
    (hG : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (hmono : Mono f) (hepi : Epi g) (hexact : (ShortComplex.mk f g w).Exact) :
    singleClassOf X F = singleClassOf X E + singleClassOf X G :=
  have hEp := isPerfect_singleFunctor_of_isFiniteLocallyFree X E hE
  have hFp := isPerfect_singleFunctor_of_isFiniteLocallyFree X F hF
  have hGp := isPerfect_singleFunctor_of_isFiniteLocallyFree X G hG
  (singleClassOf_of_isFiniteLocallyFree X F hF hFp).trans
    ((clsSingle_eq_add_of_shortExact X f g w hmono hepi hexact hEp hFp hGp).trans
      (congr_arg₂ (· + ·) (singleClassOf_of_isFiniteLocallyFree X E hE hEp).symm
        (singleClassOf_of_isFiniteLocallyFree X G hG hGp).symm))

/-- **The comparison map on the Grothendieck group of vector bundles.** The function
`ℰ ↦ [ℰ[0]]` kills the relations defining `K₀(Vect(X))`: a module that is not finite locally
free is sent to zero by construction, and a short exact sequence of finite locally free modules
gives a distinguished triangle of the derived category whose three vertices are perfect. -/
def comparisonAddHom :
    VectorBundleKZero X →+
      K0 (ObjectProperty.FullSubcategory
        (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} (X := X.toRingedSpace))) :=
  VectorBundleKZero.liftAddHom (singleClassOf X)
    (singleClassOf_eq_zero_of_not_isFiniteLocallyFree X)
    (fun f g w hE hF hG hmono hepi hexact =>
      singleClassOf_eq_add_of_shortExact X f g w hE hF hG hmono hepi hexact)

/-- The comparison map sends the class of a finite locally free module to the class of that
module placed in degree zero. -/
theorem comparisonAddHom_classOf (M : X.Modules)
    (hM : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M)
    (h : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
      ((DerivedCategory.singleFunctor X.Modules 0).obj M)) :
    comparisonAddHom X (VectorBundleKZero.classOf X M) =
      K0.cls ⟨(DerivedCategory.singleFunctor X.Modules 0).obj M, h⟩ :=
  (VectorBundleKZero.liftAddHom_classOf (singleClassOf X) _ _ M).trans
    (singleClassOf_of_isFiniteLocallyFree X M hM h)

/-! ### The comparison ring homomorphism -/

/-- Isomorphic perfect objects of `D(𝒪_X)` have the same class in `K₀(D_perf(𝒪_X))`. -/
private theorem cls_eq_of_iso_isPerfect {A B : DerivedCategory X.Modules}
    (hA : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) A)
    (hB : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace) B) (e : A ≅ B) :
    K0.cls (⟨A, hA⟩ : ObjectProperty.FullSubcategory
        (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} (X := X.toRingedSpace))) =
      K0.cls ⟨B, hB⟩ :=
  K0.cls_eq_of_iso (ObjectProperty.isoMk _ e)

/-- There is a unique ring homomorphism from the Grothendieck ring of vector bundles on a scheme
`X` to the Grothendieck ring of perfect objects of `D(𝒪_X)` which sends the class of a finite
locally free module to the class of that module placed in degree zero.

The ring structure on the target is the one of
`AlgebraicGeometry.RingedSpace.exists_derivedTensorProduct_commRing`, for the given derived
tensor product. -/
@[stacks 0FDK "vector_bundle_comparison_ring_map", sga "6 IV 2.7" "b) K'_naif→K' ring"]
theorem existsUnique_comparisonRingHom :
    letI := (RingedSpace.perfectTensorStructure X.toRingedSpace T).commRing
    ∃! f : VectorBundleKZero X →+*
        K0 (ObjectProperty.FullSubcategory
          (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} (X := X.toRingedSpace))),
      ∀ (M : X.Modules) (_ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M)
        (h : Stacks.Cohomology.PerfectComplexes.IsPerfect (X := X.toRingedSpace)
          ((DerivedCategory.singleFunctor X.Modules 0).obj M)),
        f (VectorBundleKZero.classOf X M) = K0.cls ⟨_, h⟩ := by
  let := (RingedSpace.perfectTensorStructure X.toRingedSpace T).commRing
  have hmul : ∀ (M N : X.Modules)
      (_ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M)
      (_ : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) N),
      comparisonAddHom X (VectorBundleKZero.classOf X M * VectorBundleKZero.classOf X N) =
        comparisonAddHom X (VectorBundleKZero.classOf X M) *
          comparisonAddHom X (VectorBundleKZero.classOf X N) := by
    intro M N hM hN
    have hMN : IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf)
        (Scheme.Modules.tensorObjRingedSpace X M N) :=
      @isFiniteLocallyFree_tensorObj X M N hM hN
    have hMNp := isPerfect_singleFunctor_of_isFiniteLocallyFree X _ hMN
    have hMp := isPerfect_singleFunctor_of_isFiniteLocallyFree X M hM
    have hNp := isPerfect_singleFunctor_of_isFiniteLocallyFree X N hN
    have e1 := (congrArg (comparisonAddHom X)
      (VectorBundleKZero.classOf_mul M N hM hN)).trans
      (comparisonAddHom_classOf X _ hMN hMNp)
    have e2 := comparisonAddHom_classOf X M hM hMp
    have e3 := comparisonAddHom_classOf X N hN hNp
    have htens := RingedSpace.isPerfect_derivedTensorProduct X.toRingedSpace T
      ((DerivedCategory.singleFunctor X.Modules 0).obj M)
      ((DerivedCategory.singleFunctor X.Modules 0).obj N) hMp hNp
    have e4 := cls_eq_of_iso_isPerfect X htens hMNp
      (nonempty_derivedTensorSingleIso X T M N hN).some
    have e5 := (RingedSpace.perfectTensorStructure X.toRingedSpace T).cls_mul
      (⟨_, hMp⟩ : ObjectProperty.FullSubcategory
        (Stacks.Cohomology.PerfectComplexes.IsPerfect.{u, u, d} (X := X.toRingedSpace)))
      ⟨_, hNp⟩
    exact e1.trans (e4.symm.trans (e5.symm.trans (congr_arg₂ (· * ·) e2.symm e3.symm)))
  refine ⟨{ comparisonAddHom X with
    map_one' := ?_
    map_mul' := ?_ }, ?_, ?_⟩
  · have hu := isFiniteLocallyFree_unit X
    have hup := isPerfect_singleFunctor_of_isFiniteLocallyFree X _ hu
    have e1 := comparisonAddHom_classOf X (SheafOfModules.unit X.ringCatSheaf) hu hup
    have hq := AlgebraicGeometry.RingedSpace.isPerfect_Q_obj_of_isStrictlyPerfect
      (X := X.toRingedSpace) (isStrictlyPerfect_single
        (StrictlyPerfect.isDirectSummandOfFiniteFree_structureModule X.toRingedSpace) 0)
    have e2 := cls_eq_of_iso_isPerfect X hup hq
      ((DerivedCategory.singleFunctorIsoCompQ X.Modules 0).app (SheafOfModules.unit X.ringCatSheaf))
    exact e1.trans (e2.trans
      (RingedSpace.perfectTensorStructure X.toRingedSpace T).one_eq_cls_one.symm)
  · intro a b
    have step : ∀ M : X.Modules,
        IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) M →
        ∀ c : VectorBundleKZero X,
          comparisonAddHom X (VectorBundleKZero.classOf X M * c) =
            comparisonAddHom X (VectorBundleKZero.classOf X M) * comparisonAddHom X c := by
      intro M hM
      refine DFunLike.congr_fun (VectorBundleKZero.addHom_ext
        (φ := (comparisonAddHom X).comp (AddMonoidHom.mulLeft (VectorBundleKZero.classOf X M)))
        (ψ := (AddMonoidHom.mulLeft (comparisonAddHom X (VectorBundleKZero.classOf X M))).comp
          (comparisonAddHom X)) fun N hN => ?_)
      exact hmul M N hM hN
    refine DFunLike.congr_fun (VectorBundleKZero.addHom_ext
      (φ := (comparisonAddHom X).comp (AddMonoidHom.mulRight b))
      (ψ := (AddMonoidHom.mulRight (comparisonAddHom X b)).comp (comparisonAddHom X))
      fun M hM => step M hM b) a
  · intro M hM h
    exact comparisonAddHom_classOf X M hM h
  · intro g hg
    refine RingHom.coe_addMonoidHom_injective (VectorBundleKZero.addHom_ext fun M hM => ?_)
    exact (hg M hM (isPerfect_singleFunctor_of_isFiniteLocallyFree X M hM)).trans
      (comparisonAddHom_classOf X M hM
        (isPerfect_singleFunctor_of_isFiniteLocallyFree X M hM)).symm

end AlgebraicGeometry

end
