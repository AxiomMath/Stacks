module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Module.LocalizedModule.Away
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FlatShortExactSequence
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.StalkLinearEquiv
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.TwoPeriodic
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Multiplicity
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Chow.DeterminantsFiniteLength.RestrictScalars
public import StacksFrontier.AlgebraicGeometry.Chow.DimensionFunction.PrincipalDivisorFamily
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Comparison
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesHerbrand.Length
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicLengthDeterminantFormula
public import StacksFrontier.AlgebraicGeometry.Chow.RationalEquivalenceDefs
public import StacksFrontier.AlgebraicGeometry.Chow.RationalFunctions.FunctionField
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.FiberRank.GenericPoint
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.KernelCokernel
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.AffineOpen
public import StacksFrontier.AlgebraicGeometry.Properties.PrincipalOpens.Sections
public import StacksFrontier.Topology.Sheaves.Functors.Module.SemilinearStalk
public import StacksFrontier.Topology.Sheaves.Modules.Colimits
import StacksFrontier.AlgebraicGeometry.Chow.DivisorTransport.Order
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles.DeterminantsAndComponents
import all StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles.DeterminantsAndComponents
public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles.StalkComplex
import all StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexHomologyCycles.StalkComplex

/-!
# Two-periodic complexes on a coherent sheaf: stalks at generizations

Let `X` be a scheme locally of finite type over the base of chapter 42 of the Stacks Project, let
`F` be a coherent `𝒪_X`-module with a `(2, 1)`-periodic complex `(F, φ, ψ)`, and let `x` be a point
of `X`. On an integral scheme of delta-dimension `k + 1` a point of relative dimension `k` has
codimension one, and there the order of vanishing of a rational function is its order in the local
ring. For a prime `p` of the local ring `A = 𝒪_{X,x}`, cutting out a generization `ξ` of `x`, the
local ring at `ξ` is the localization `A_p` and the stalk `F_ξ` is the localization `(F_x)_p`,
compatibly with stalk maps. Consequently the order at `p` of the periodic determinant of the
localized stalk complex is the order of vanishing, in the local ring of an integral closed
subscheme through `x`, of the periodic determinant of the complex at the generic point of that
subscheme.

When `x` has relative dimension `k` and the support of `F` has dimension at most `k + 1`, the
support of the stalk `F_x` has dimension at most one, and the irreducible components of the support
of `F` through `x` correspond to the minimal primes of the support of `F_x`.

## References

* [Stacks Project, Tag 02QD](https://stacks.math.columbia.edu/tag/02QD)
* [Stacks Project, Tag 02SB](https://stacks.math.columbia.edu/tag/02SB)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.SheafOfModules.FlatShortExact TopologicalSpace

universe u

namespace Stacks.Chow

/-- On an integral scheme of delta-dimension `k + 1` over the base, a point of relative dimension
`k` has codimension one. -/
private theorem coheight_eq_one_of_relativeDimension
    (C : ChowSituation.{u}) {Y : Scheme.{u}}
    (p : Y ⟶ C.S) [LocallyOfFiniteType p] [IsIntegral Y]
    (k : ℤ) (hn : schemeDeltaDimension C p = ((k + 1 : ℤ) : EInt))
    (y : Y) (hy : relativeDimension C.dimensionFunction p y = k) :
    Order.coheight y = 1 := by
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
    C.isUniversallyCatenary C.dimensionFunction p
  have hη : d (genericPoint Y) = k + 1 := by
    have h := (schemeDeltaDimension_eq_genericPoint C p).symm.trans hn
    exact WithBotTop.coe_injective (by simpa only [hd] using h)
  have hdy : d y = k := (hd y).trans hy
  have hne : y ≠ genericPoint Y := by
    intro h
    rw [h] at hdy
    omega
  have hle : y ≤ genericPoint Y := genericPoint_specializes y
  have hlt : y < genericPoint Y :=
    lt_iff_le_not_ge.mpr ⟨hle, fun h ↦ hne (Specializes.antisymm h hle).eq⟩
  apply le_antisymm
  · apply (Order.coheight_le_coe_iff (n := 1)).2
    intro z hyz
    have hz : z = genericPoint Y := by
      by_contra hz
      have h₁ := d.strictAnti_specializes (show z ⤳ y from hyz.le) hyz.ne.symm
      have h₂ := d.strictAnti_specializes (genericPoint_specializes z) (Ne.symm hz)
      omega
    rw [hz]
    have hmax : IsMax (genericPoint Y) := by
      intro z _
      exact genericPoint_specializes z
    rw [Order.IsMax.coheight_eq_zero hmax]
    exact (show (0 : ℕ∞) < 1 by decide)
  · have hpos : 0 < Order.coheight y := Order.coheight_pos_of_lt_top hlt
    exact le_of_not_gt (fun h => (ne_of_gt hpos) (Order.lt_one_iff.mp h))

/-- At a codimension-one point the order of vanishing of a rational function is the order of that
function in the local ring there. -/
private theorem ord_eq_toAdd_unzeroD_ordFrac {Y : Scheme.{u}} [IsIntegral Y]
    [IsLocallyNoetherian Y] (g : Y.functionField) (y : Y)
    (hy : Order.coheight y = 1) :
    letI : Ring.KrullDimLE 1 (Y.presheaf.stalk y) :=
      AlgebraicGeometry.krullDimLE_of_coheight_le hy.le
    Y.ord g y =
      Multiplicative.toAdd ((Ring.ordFrac (Y.presheaf.stalk y) g).unzeroD 1) :=
  Y.ord_eq_ordHom_of_coheight_eq_one hy g

/-- A point of `U` lying in the basic open set of `r` lies in that of every power of `r`. -/
private theorem mem_basicOpen_pow {X : Scheme.{u}} {U : X.Opens} {x : X} (hx : x ∈ U)
    {r : Γ(X, U)} (hxr : x ∈ X.basicOpen r) (n : ℕ) : x ∈ X.basicOpen (r ^ n) := by
  rcases n with _ | n
  · simpa using hx
  · rwa [X.basicOpen_pow r (Nat.succ_pos n)]

/-- On an affine open, a germ of a quasi-coherent module becomes the germ of a section after
multiplication by a function not vanishing at the point. -/
private theorem exists_germ_smul_eq_of_isAffineOpen
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (m : F.presheaf.stalk x) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    ∃ (r : Γ(X, U)) (s : Γ(F, U)),
      x ∈ X.basicOpen r ∧ X.presheaf.germ U x hx r • m = F.presheaf.germ U x hx s := by
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
  obtain ⟨V, hxV, s, rfl⟩ := F.presheaf.exists_germ_eq m
  obtain ⟨r, hrV, hxr⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
  let t := F.presheaf.map (homOfLE hrV).op s
  let : Module Γ(X, U) Γ(F, X.basicOpen r) :=
    Module.compHom Γ(F, X.basicOpen r)
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let l := AlgebraicGeometry.Scheme.Modules.restrictionLinearMap F
    (homOfLE (X.basicOpen_le r))
  let : IsLocalizedModule.Away r l :=
    AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs F
      hU.isCompact hU.isQuasiSeparated r
  obtain ⟨n, z, hz⟩ := IsLocalizedModule.Away.surj l r t
  refine ⟨r ^ n, z, mem_basicOpen_pow hx hxr n, ?_⟩
  have h := congrArg (fun a : Γ(F, X.basicOpen r) =>
      F.presheaf.germ (X.basicOpen r) x hxr a) hz
  change F.presheaf.germ (X.basicOpen r) x hxr
      ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op (r ^ n)) • t) =
    F.presheaf.germ (X.basicOpen r) x hxr
      (F.presheaf.map (homOfLE (X.basicOpen_le r)).op z) at h
  have hg := PresheafOfModules.germ_smul (R := X.presheaf) F.val x (X.basicOpen r) hxr
    (X.presheaf.map (homOfLE (X.basicOpen_le r)).op (r ^ n)) t
  change F.presheaf.germ (X.basicOpen r) x hxr
      ((X.presheaf.map (homOfLE (X.basicOpen_le r)).op (r ^ n)) • t) =
    X.presheaf.germ (X.basicOpen r) x hxr
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op (r ^ n)) •
      F.presheaf.germ (X.basicOpen r) x hxr t at hg
  rw [hg, TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply] at h
  simpa only [t, TopCat.Presheaf.germ_res_apply] using h

/-- A section of a quasi-coherent module on an affine open whose germ at a point vanishes is
killed by a function not vanishing at that point. -/
private theorem exists_smul_eq_zero_of_germ_eq_zero
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    {U : X.Opens} (hU : IsAffineOpen U) (x : X) (hx : x ∈ U)
    (s : Γ(F, U)) (hs : F.presheaf.germ U x hx s = 0) :
    ∃ r : Γ(X, U), x ∈ X.basicOpen r ∧ r • s = 0 := by
  obtain ⟨V, hxV, i, j, hij⟩ := F.presheaf.germ_eq x hx hx s 0
    (by simpa only [map_zero] using hs)
  obtain ⟨r, hrV, hxr⟩ := hU.exists_basicOpen_le ⟨x, hxV⟩ hx
  let : Module Γ(X, U) Γ(F, X.basicOpen r) :=
    Module.compHom Γ(F, X.basicOpen r)
      (X.presheaf.map (homOfLE (X.basicOpen_le r)).op).hom
  let l := AlgebraicGeometry.Scheme.Modules.restrictionLinearMap F
    (homOfLE (X.basicOpen_le r))
  let : IsLocalizedModule.Away r l :=
    AlgebraicGeometry.isLocalizedModule_restriction_basicOpen_of_qcqs F
      hU.isCompact hU.isQuasiSeparated r
  have hzero : l s = l 0 := by
    have hh := congrArg (fun a : Γ(F, V) =>
      F.presheaf.map (homOfLE hrV).op a) hij
    change F.presheaf.map _ s = F.presheaf.map _ 0
    simp only [← F.presheaf.map_comp_apply, ← CategoryTheory.op_comp, map_zero] at hh ⊢
    have hi : homOfLE (X.basicOpen_le r) = homOfLE hrV ≫ i := Subsingleton.elim _ _
    rw [hi]
    exact hh
  obtain ⟨n, hn⟩ := IsLocalizedModule.Away.exists_of_eq r hzero
  exact ⟨r ^ n, mem_basicOpen_pow hx hxr n, by simpa only [smul_zero] using hn⟩

/-- Specialization of stalks is semilinear over the specialization map of local rings. -/
private theorem moduleStalkSpecializes_smul {X : Scheme.{u}} (F : X.Modules)
    {x y : X} (h : x ⤳ y) (r : X.presheaf.stalk y) (m : F.presheaf.stalk y) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    letI : Module (X.presheaf.stalk y) (F.presheaf.stalk y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val y
    F.presheaf.stalkSpecializes h (r • m) =
      X.presheaf.stalkSpecializes h r • F.presheaf.stalkSpecializes h m := by
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
  let : Module (X.presheaf.stalk y) (F.presheaf.stalk y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val y
  obtain ⟨U, hyU, a, rfl⟩ := X.presheaf.exists_germ_eq r
  obtain ⟨V, hyV, b, rfl⟩ := F.presheaf.exists_germ_eq m
  let W := U ⊓ V
  have hyW : y ∈ W := ⟨hyU, hyV⟩
  let aW := X.presheaf.map (homOfLE (inf_le_left : W ≤ U)).op a
  let bW := F.presheaf.map (homOfLE (inf_le_right : W ≤ V)).op b
  have ha : X.presheaf.germ W y hyW aW = X.presheaf.germ U y hyU a :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hb : F.presheaf.germ W y hyW bW = F.presheaf.germ V y hyV b :=
    TopCat.Presheaf.germ_res_apply _ _ _ _ _
  have hg : F.presheaf.germ W y hyW (aW • bW) =
      X.presheaf.germ W y hyW aW • F.presheaf.germ W y hyW bW :=
    PresheafOfModules.germ_smul (R := X.presheaf) F.val y W hyW aW bW
  rw [← ha, ← hb, ← hg]
  simp only [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes]
  exact PresheafOfModules.germ_smul (R := X.presheaf) F.val x W (h.mem_open W.isOpen hyW) aW bW

/-- The specialization map on the stalks of a module, as a linear map over the local ring at the
specialization. -/
private noncomputable def moduleStalkSpecializes {X : Scheme.{u}} (F : X.Modules)
    {x y : X} (h : x ⤳ y) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    letI : Module (X.presheaf.stalk y) (F.presheaf.stalk y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val y
    letI : Module (X.presheaf.stalk y) (F.presheaf.stalk x) :=
      Module.compHom (F.presheaf.stalk x) (X.presheaf.stalkSpecializes h).hom
    F.presheaf.stalk y →ₗ[X.presheaf.stalk y] F.presheaf.stalk x := by
  letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  letI : Module (X.presheaf.stalk y) (F.presheaf.stalk y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val y
  letI : Module (X.presheaf.stalk y) (F.presheaf.stalk x) :=
    Module.compHom (F.presheaf.stalk x) (X.presheaf.stalkSpecializes h).hom
  exact { toFun := F.presheaf.stalkSpecializes h,
          map_add' := map_add _,
          map_smul' := moduleStalkSpecializes_smul F h }

/-- A germ at `x` avoids a prime of the local ring exactly when the point of `X` cut out by that
prime lies in the basic open set of the section. -/
private theorem germ_not_mem_prime_iff {X : Scheme.{u}} (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) {U : X.Opens} (hU : IsAffineOpen U)
    (hxU : x ∈ U) (a : Γ(X, U)) :
    X.presheaf.germ U x hxU a ∉ p.asIdeal ↔ X.fromSpecStalk x p ∈ X.basicOpen a := by
  change p ∈ PrimeSpectrum.basicOpen (X.presheaf.germ U x hxU a) ↔ _
  rw [← hU.fromSpecStalk_eq_fromSpecStalk hxU, IsAffineOpen.fromSpecStalk]
  change _ ↔ p ∈ (Spec.map (X.presheaf.germ U x hxU)) ⁻¹ᵁ hU.fromSpec ⁻¹ᵁ X.basicOpen a
  rw [hU.fromSpec_preimage_basicOpen]
  rfl

/-- The specialization map to the local ring cut out by a prime sends an element to a unit exactly
when that element avoids the prime. -/
private theorem isUnit_stalkSpecializes_iff {X : Scheme.{u}} (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) (a : X.presheaf.stalk x) :
    IsUnit (X.presheaf.stalkSpecializes (specializes_fromSpecStalk x p) a) ↔
      a ∉ p.asIdeal := by
  obtain ⟨U, hxU, hU, r, rfl⟩ :=
    TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens X.presheaf x a
  rw [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes,
    ← Scheme.mem_basicOpen X r _ ((specializes_fromSpecStalk x p).mem_open U.isOpen hxU)]
  exact (germ_not_mem_prime_iff x p hU hxU r).symm

/-- A section on an affine open avoids the prime of a point exactly when that point lies in the
basic open set of the section. -/
private theorem primeIdealOf_not_mem_iff {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) (x : X) (hx : x ∈ U) (r : Γ(X, U)) :
    r ∉ (hU.primeIdealOf ⟨x, hx⟩).asIdeal ↔ x ∈ X.basicOpen r := by
  change hU.primeIdealOf ⟨x, hx⟩ ∈ PrimeSpectrum.basicOpen r ↔ _
  rw [← hU.fromSpec_preimage_basicOpen]
  change hU.fromSpec (hU.primeIdealOf ⟨x, hx⟩) ∈ X.basicOpen r ↔ _
  rw [hU.fromSpec_primeIdealOf]

/-- Stalk maps of a morphism of modules commute with specialization. -/
private theorem stalkLinearMap_stalkSpecializes {X : Scheme.{u}}
    {F G : X.Modules} (a : F ⟶ G) {x y : X} (h : x ⤳ y)
    (m : abStalk F y) :
    G.presheaf.stalkSpecializes h (stalkLinearMap a y m) =
      stalkLinearMap a x (F.presheaf.stalkSpecializes h m) := by
  have hh := TopCat.Presheaf.stalkSpecializes_stalkFunctor_map
    ((PresheafOfModules.toPresheaf X.ringCatSheaf.obj).map a.val) h
  exact (congrArg (fun q => q.hom m) hh).symm

/-- The inverse of the linear stalk equivalence of an isomorphism is the stalk map of the inverse
isomorphism. -/
private theorem stalkLinearEquivOfIso_symm_apply {X : Scheme.{u}} {F G : X.Modules}
    (e : F ≅ G) (x : X) (m : abStalk G x) :
    (stalkLinearEquivOfIso e x).symm m = stalkLinearMap e.inv x m := by
  have hh := congrArg AddEquiv.symm (stalkLinearEquivOfIso_toAddEquiv e x)
  exact DFunLike.congr_fun hh m

/-- Stalk maps are compatible with composites of three morphisms. -/
private theorem stalkLinearMap_comp₃ {X : Scheme.{u}} {A B C D : X.Modules}
    (a : A ⟶ B) (b : B ⟶ C) (c : C ⟶ D) (x : X) (m : abStalk A x) :
    stalkLinearMap c x (stalkLinearMap b x (stalkLinearMap a x m)) =
      stalkLinearMap (a ≫ b ≫ c) x m :=
  (congrArg (fun q => (ConcreteCategory.hom q) m) (stalkF_map_comp₃ x a b c)).symm

/-- The two conjugated endomorphisms of the stalk are the stalk maps of the two conjugated
differentials. -/
private theorem periodicStalkLinearMaps_eq {X : Scheme.{u}}
    (F : X.Modules) (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (x : X) :
    periodicStalkLinearMaps F K e x =
      (stalkLinearMap ((e 0).inv ≫ K.d 0 1 ≫ (e 1).hom) x,
        stalkLinearMap ((e 1).inv ≫ K.d 1 0 ≫ (e 0).hom) x) := by
  let := stalkModule (X := X.toRingedSpace) F x
  have hn : (ComplexShape.up (ZMod 2)).next 0 = 1 :=
    (ComplexShape.up (ZMod 2)).next_eq' (by decide)
  have hp : (ComplexShape.up (ZMod 2)).prev 0 = 1 :=
    (ComplexShape.up (ZMod 2)).prev_eq' (by decide)
  have h₀ : (e 0).inv ≫ (K.sc 0).g ≫
      (e ((ComplexShape.up (ZMod 2)).next 0)).hom =
      (e 0).inv ≫ K.d 0 1 ≫ (e 1).hom := by
    change (e 0).inv ≫ K.d 0 ((ComplexShape.up (ZMod 2)).next 0) ≫
      (e ((ComplexShape.up (ZMod 2)).next 0)).hom = _
    rw [hn]
  have h₁ : (e ((ComplexShape.up (ZMod 2)).prev 0)).inv ≫ (K.sc 0).f ≫ (e 0).hom =
      (e 1).inv ≫ K.d 1 0 ≫ (e 0).hom := by
    change (e ((ComplexShape.up (ZMod 2)).prev 0)).inv ≫
      K.d ((ComplexShape.up (ZMod 2)).prev 0) 0 ≫ (e 0).hom = _
    rw [hp]
  apply Prod.ext
  · apply LinearMap.ext
    intro m
    dsimp only [Prod.fst]
    change stalkLinearMap (e _).hom x
      (stalkLinearMap (K.sc 0).g x ((stalkLinearEquivOfIso (e 0) x).symm m)) = _
    rw [stalkLinearEquivOfIso_symm_apply]
    exact (stalkLinearMap_comp₃ _ _ _ x m).trans (congrArg (fun q => stalkLinearMap q x m) h₀)
  · apply LinearMap.ext
    intro m
    dsimp only [Prod.snd]
    change stalkLinearMap (e 0).hom x
      (stalkLinearMap (K.sc 0).f x ((stalkLinearEquivOfIso (e _) x).symm m)) = _
    rw [stalkLinearEquivOfIso_symm_apply]
    exact (stalkLinearMap_comp₃ _ _ _ x m).trans (congrArg (fun q => stalkLinearMap q x m) h₁)

/-- Conjugating a differential of the complex of stalks by the chosen isomorphisms gives the
stalk map of the conjugated differential. -/
private theorem moduleStalkComplex_conjugate_eq_stalkLinearMap {X : Scheme.{u}}
    (F : X.Modules) (K : CochainComplex X.Modules (ZMod 2))
    (e : ∀ i : ZMod 2, K.X i ≅ F) (x : X) (i j : ZMod 2) :
    let E (i : ZMod 2) := ((moduleStalkFunctor x).mapIso (e i)).trans (moduleStalkIso F x)
    ((E i).inv ≫ (moduleStalkComplex K x).d i j ≫ (E j).hom).hom =
      stalkLinearMap ((e i).inv ≫ K.d i j ≫ (e j).hom) x := by
  let := stalkModule (X := X.toRingedSpace) F x
  dsimp only
  apply LinearMap.ext
  intro m
  exact stalkLinearMap_comp₃ (e i).inv (K.d i j) (e j).hom x m

/-- The local ring at the point cut out by a prime of the local ring at `x` is the localization of
the latter at that prime. -/
private theorem isLocalization_stalkSpecializes {X : Scheme.{u}} (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    letI := (X.presheaf.stalkSpecializes (specializes_fromSpecStalk x p)).hom.toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk (X.fromSpecStalk x p)) p.asIdeal := by
  let η := X.fromSpecStalk x p
  let h := specializes_fromSpecStalk x p
  let := (X.presheaf.stalkSpecializes h).hom.toAlgebra
  have hzero (a : X.presheaf.stalk x) (ha : X.presheaf.stalkSpecializes h a = 0) :
      ∃ c : p.asIdeal.primeCompl, c * a = 0 := by
    obtain ⟨U, hxU, hU, s, rfl⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens X.presheaf x a
    have hηU : η ∈ U := h.mem_open U.isOpen hxU
    let := (X.presheaf.germ U η hηU).hom.toAlgebra
    let := hU.isLocalization_stalk ⟨η, hηU⟩
    have hs : algebraMap Γ(X, U) (X.presheaf.stalk η) s =
        algebraMap Γ(X, U) (X.presheaf.stalk η) 0 := by
      change X.presheaf.germ U η hηU s = X.presheaf.germ U η hηU 0
      simpa only [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes,
        map_zero] using ha
    obtain ⟨c, hc⟩ := IsLocalization.exists_of_eq
      (M := (hU.primeIdealOf ⟨η, hηU⟩).asIdeal.primeCompl) hs
    have hηc : η ∈ X.basicOpen (c : Γ(X, U)) :=
      (primeIdealOf_not_mem_iff hU η hηU c).mp c.2
    refine ⟨⟨X.presheaf.germ U x hxU c,
      (germ_not_mem_prime_iff x p hU hxU c).mpr hηc⟩, ?_⟩
    change X.presheaf.germ U x hxU c * X.presheaf.germ U x hxU s = 0
    simpa only [map_mul, mul_zero, map_zero] using
      congrArg (fun a : Γ(X, U) => X.presheaf.germ U x hxU a) hc
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro r
    exact (isUnit_stalkSpecializes_iff x p r).mpr r.2
  · intro a
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hηU : η ∈ U := h.mem_open U.isOpen hxU
    let := (X.presheaf.germ U η hηU).hom.toAlgebra
    let := hU.isLocalization_stalk ⟨η, hηU⟩
    obtain ⟨⟨s, r⟩, hr⟩ := IsLocalization.surj
      (hU.primeIdealOf ⟨η, hηU⟩).asIdeal.primeCompl a
    have hηr : η ∈ X.basicOpen (r : Γ(X, U)) :=
      (primeIdealOf_not_mem_iff hU η hηU r).mp r.2
    refine ⟨⟨X.presheaf.germ U x hxU s,
      ⟨X.presheaf.germ U x hxU r, (germ_not_mem_prime_iff x p hU hxU r).mpr hηr⟩⟩, ?_⟩
    change a * X.presheaf.stalkSpecializes h (X.presheaf.germ U x hxU r) =
      X.presheaf.stalkSpecializes h (X.presheaf.germ U x hxU s)
    change a * X.presheaf.germ U η hηU r = X.presheaf.germ U η hηU s at hr
    simpa only [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes] using hr
  · intro a b hab
    change X.presheaf.stalkSpecializes h a = X.presheaf.stalkSpecializes h b at hab
    obtain ⟨c, hc⟩ := hzero (a - b) (by simp only [map_sub, hab, sub_self])
    exact ⟨c, sub_eq_zero.mp (by simpa only [mul_sub] using hc)⟩

/-- The stalk of a quasi-coherent module at the point cut out by a prime is the localization at
that prime of its stalk at `x`. -/
private theorem isLocalizedModule_stalkSpecializes {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    let η := X.fromSpecStalk x p
    let h := specializes_fromSpecStalk x p
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    letI : Module (X.presheaf.stalk η) (F.presheaf.stalk η) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val η
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk η) :=
      Module.compHom (F.presheaf.stalk η) (X.presheaf.stalkSpecializes h).hom
    IsLocalizedModule p.asIdeal.primeCompl (moduleStalkSpecializes F h) := by
  dsimp only
  let η := X.fromSpecStalk x p
  let h := specializes_fromSpecStalk x p
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
  let : Module (X.presheaf.stalk η) (F.presheaf.stalk η) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val η
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk η) :=
    Module.compHom (F.presheaf.stalk η) (X.presheaf.stalkSpecializes h).hom
  have hzero (m : F.presheaf.stalk x) (hm : (moduleStalkSpecializes F h).toFun m = 0) :
      ∃ r : p.asIdeal.primeCompl, r • m = 0 := by
    obtain ⟨U, hxU, hU, s, rfl⟩ :=
      TopCat.Presheaf.exists_mem_germ_eq_of_isBasis X.isBasis_affineOpens F.presheaf x m
    have hηU : η ∈ U := h.mem_open U.isOpen hxU
    have hs : F.presheaf.germ U η hηU s = 0 := by
      change F.presheaf.stalkSpecializes h (F.presheaf.germ U x hxU s) = 0 at hm
      simpa only [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes] using hm
    obtain ⟨r, hr, hrs⟩ := exists_smul_eq_zero_of_germ_eq_zero F hU η hηU s hs
    refine ⟨⟨X.presheaf.germ U x hxU r, (germ_not_mem_prime_iff x p hU hxU r).mpr hr⟩, ?_⟩
    change X.presheaf.germ U x hxU r • F.presheaf.germ U x hxU s = 0
    calc
      _ = F.presheaf.germ U x hxU (r • s) :=
        (PresheafOfModules.germ_smul (R := X.presheaf) F.val x U hxU r s).symm
      _ = 0 := by rw [hrs, map_zero]
  refine { map_units := ?_, surj := ?_, exists_of_eq := ?_ }
  · intro r
    rw [Module.End.isUnit_iff]
    change Function.Bijective (fun m : F.presheaf.stalk η =>
      X.presheaf.stalkSpecializes h r • m)
    exact ((isUnit_stalkSpecializes_iff x p r).mpr r.2).smul_bijective
  · intro m
    obtain ⟨_, ⟨U, hU, rfl⟩, hxU, _⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have hηU : η ∈ U := h.mem_open U.isOpen hxU
    obtain ⟨r, s, hr, hrs⟩ := exists_germ_smul_eq_of_isAffineOpen F hU η hηU m
    refine ⟨⟨F.presheaf.germ U x hxU s,
      ⟨X.presheaf.germ U x hxU r, (germ_not_mem_prime_iff x p hU hxU r).mpr hr⟩⟩, ?_⟩
    change X.presheaf.stalkSpecializes h (X.presheaf.germ U x hxU r) • m =
      F.presheaf.stalkSpecializes h (F.presheaf.germ U x hxU s)
    simpa only [← ConcreteCategory.comp_apply, TopCat.Presheaf.germ_stalkSpecializes] using hrs
  · intro a b hab
    obtain ⟨r, hr⟩ := hzero (a - b) (by
      change F.presheaf.stalkSpecializes h (a - b) = 0
      have hab' : F.presheaf.stalkSpecializes h a = F.presheaf.stalkSpecializes h b := hab
      simp only [map_sub, hab', sub_self])
    exact ⟨r, sub_eq_zero.mp (by simpa only [smul_sub] using hr)⟩

/-- The localization statement for the local ring, for a point presented as the image of the
prime. -/
private theorem isLocalization_stalkSpecializes_of_eq {X : Scheme.{u}} (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) {η : X}
    (hp : X.fromSpecStalk x p = η) (h : η ⤳ x) :
    letI := (X.presheaf.stalkSpecializes h).hom.toAlgebra
    IsLocalization.AtPrime (X.presheaf.stalk η) p.asIdeal := by
  subst η
  exact isLocalization_stalkSpecializes x p

/-- The localization statement for the stalk of a module, for a point presented as the image of
the prime. -/
private theorem isLocalizedModule_stalkSpecializes_of_eq {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) {η : X}
    (hp : X.fromSpecStalk x p = η) (h : η ⤳ x) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    letI : Module (X.presheaf.stalk η) (F.presheaf.stalk η) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val η
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk η) :=
      Module.compHom (F.presheaf.stalk η) (X.presheaf.stalkSpecializes h).hom
    IsLocalizedModule p.asIdeal.primeCompl (moduleStalkSpecializes F h) := by
  subst η
  exact isLocalizedModule_stalkSpecializes F x p

/-- The order of the periodic determinant of the localized stalk complex at a prime is the order
of vanishing, in the local ring of an integral closed subscheme through the point, of the
periodic determinant of the complex at the generic point of that subscheme. -/
private theorem ordFrac_periodicDeterminant_stalk
    {X Y : Scheme.{u}} [IsLocallyNoetherian X] [IsIntegral Y]
    [IsLocallyNoetherian Y] (i : Y ⟶ X) [IsClosedImmersion i] (y : Y) (x : X) (hy : i y = x)
    [Ring.KrullDimLE 1 (Y.presheaf.stalk y)]
    (F : X.Modules) [F.IsQuasicoherent] (a b : F ⟶ F)
    (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : X.fromSpecStalk x p = i (genericPoint Y))
    [Ring.KrullDimLE 1 ((X.presheaf.stalk x) ⧸ p.asIdeal)] :
    letI := stalkModule (X := X.toRingedSpace) F x
    letI := stalkModule (X := X.toRingedSpace) F (i (genericPoint Y))
    ∀ (hex : Function.Exact
      (LocalizedModule.map p.asIdeal.primeCompl (stalkLinearMap a x))
      (LocalizedModule.map p.asIdeal.primeCompl (stalkLinearMap b x)))
    (hex' : Function.Exact
      (LocalizedModule.map p.asIdeal.primeCompl (stalkLinearMap b x))
      (LocalizedModule.map p.asIdeal.primeCompl (stalkLinearMap a x)))
    (hfin : letI := stalkModule (X := X.toRingedSpace) F x
      IsFiniteLength (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl (abStalk F x)))
    (hNex : Function.Exact (stalkLinearMap a (i (genericPoint Y)))
      (stalkLinearMap b (i (genericPoint Y))))
    (hNex' : Function.Exact (stalkLinearMap b (i (genericPoint Y)))
      (stalkLinearMap a (i (genericPoint Y))))
    (hNfin : letI := stalkModule (X := X.toRingedSpace) F (i (genericPoint Y))
      IsFiniteLength (X.presheaf.stalk (i (genericPoint Y)))
        (abStalk F (i (genericPoint Y)))),
    Ring.ordFrac ((X.presheaf.stalk x) ⧸ p.asIdeal)
      (AlgebraicGeometry.periodicDeterminant
        (LocalizedModule.map p.asIdeal.primeCompl (stalkLinearMap a x))
        (LocalizedModule.map p.asIdeal.primeCompl (stalkLinearMap b x))
        hex hex' hfin : p.asIdeal.ResidueField) =
      Ring.ordFrac (Y.presheaf.stalk y)
        ((rationalFunctionsEquivFunctionField Y).1
          ((rationalFunctionsEquivResidueField Y).1.symm
            (i.residueFieldMap (genericPoint Y)
              ((AlgebraicGeometry.periodicDeterminant
                (stalkLinearMap a (i (genericPoint Y)))
                (stalkLinearMap b (i (genericPoint Y)))
                hNex hNex' hNfin).val : X.residueField (i (genericPoint Y)))))) := by
  subst x
  dsimp only
  intro hex hex' hfin hNex hNex' hNfin
  let x := i y
  let η := i (genericPoint Y)
  let h : η ⤳ x := ((genericPoint_spec Y).specializes (Set.mem_univ y)).map i.continuous
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    stalkModule (X := X.toRingedSpace) F x
  let : Module (X.presheaf.stalk η) (F.presheaf.stalk η) :=
    stalkModule (X := X.toRingedSpace) F η
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk η) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk η) :=
    Module.compHom (F.presheaf.stalk η) (X.presheaf.stalkSpecializes h).hom
  let : IsScalarTower (X.presheaf.stalk x) (X.presheaf.stalk η) (F.presheaf.stalk η) :=
    IsScalarTower.of_algebraMap_smul (fun _ _ => rfl)
  have : IsLocalization.AtPrime (X.presheaf.stalk η) p.asIdeal :=
    isLocalization_stalkSpecializes_of_eq x p hp h
  have : IsLocalizedModule p.asIdeal.primeCompl (moduleStalkSpecializes F h) :=
    isLocalizedModule_stalkSpecializes_of_eq F x p hp h
  obtain ⟨t, ht, hdet⟩ := periodicDeterminant_localization
    (M := F.presheaf.stalk x) (N := F.presheaf.stalk η) p.asIdeal
    (moduleStalkSpecializes F h)
    (stalkLinearMap a x) (stalkLinearMap b x)
    (stalkLinearMap a η) (stalkLinearMap b η)
    (stalkLinearMap_stalkSpecializes a h) (stalkLinearMap_stalkSpecializes b h)
    hex hex' hNex hNex' hfin hNfin
  rw [ordFrac_eq_of_closedImmersion_residueField_equiv i y p t ht]
  have hd := congrArg Units.val hdet
  exact congrArg (fun z : X.residueField η =>
    Ring.ordFrac (Y.presheaf.stalk y)
      ((rationalFunctionsEquivFunctionField Y).1
        ((rationalFunctionsEquivResidueField Y).1.symm
          (i.residueFieldMap (genericPoint Y) z)))) hd

/-- A prime of the local ring at `x` lies in the support of the stalk of a quasi-coherent module
exactly when the point of `X` it cuts out lies in the support of the module. -/
private theorem mem_support_stalk_iff {X : Scheme.{u}}
    (F : X.Modules) [F.IsQuasicoherent] (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    p ∈ Module.support (X.presheaf.stalk x) (F.presheaf.stalk x) ↔
      X.fromSpecStalk x p ∈ SheafOfModules.supp F := by
  let η := X.fromSpecStalk x p
  let h := specializes_fromSpecStalk x p
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
  let : Module (X.presheaf.stalk η) (F.presheaf.stalk η) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val η
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk η) :=
    Module.compHom (F.presheaf.stalk η) (X.presheaf.stalkSpecializes h).hom
  let := isLocalizedModule_stalkSpecializes F x p
  exact Module.mem_support_iff.trans
    (((IsLocalizedModule.iso p.asIdeal.primeCompl
        (moduleStalkSpecializes F h)).toEquiv.nontrivial_congr).trans
      (SheafOfModules.mem_supp_iff_nontrivial_stalk F (X.fromSpecStalk x p)).symm)

/-- At a point of relative dimension `k`, the support of the stalk of a coherent sheaf supported
in delta-dimension at most `k + 1` has dimension at most one. -/
theorem supportDim_stalk_le_one_of_relativeDimension_support_le
    (C : ChowSituation.{u}) {X : Scheme.{u}}
    (f : X ⟶ C.S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsCoherent] (k : ℤ)
    (hsupport : ∀ y ∈ SheafOfModules.supp F,
      relativeDimension C.dimensionFunction f y ≤ k + 1)
    (x : X) (hx : relativeDimension C.dimensionFunction f x = k) :
    letI : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
    Module.supportDim (X.presheaf.stalk x) (F.presheaf.stalk x) ≤ 1 := by
  let : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  obtain ⟨d, hd⟩ := relativeDimension_isDimensionFunction
    C.isUniversallyCatenary C.dimensionFunction f
  change Order.krullDim (Module.support (X.presheaf.stalk x)
    (F.presheaf.stalk x)) ≤ 1
  apply Order.krullDim_le_one_iff.mpr
  intro p
  by_contra hp
  have hnotmin : ¬ IsMin p := fun h => hp (Or.inl h)
  have hnotmax : ¬ IsMax p := fun h => hp (Or.inr h)
  obtain ⟨q, hqp⟩ := not_isMin_iff.mp hnotmin
  obtain ⟨r, hpr⟩ := not_isMax_iff.mp hnotmax
  let v : PrimeSpectrum (X.presheaf.stalk x) → X := X.fromSpecStalk x
  have hinj : Function.Injective v := (X.fromSpecStalk x).isEmbedding.injective
  have hqp' : v q.1 ⤳ v p.1 :=
    (X.fromSpecStalk x).base.hom.map_specializes
      ((PrimeSpectrum.le_iff_specializes _ _).mp hqp.le)
  have hpr' : v p.1 ⤳ v r.1 :=
    (X.fromSpecStalk x).base.hom.map_specializes
      ((PrimeSpectrum.le_iff_specializes _ _).mp hpr.le)
  have hqr : d (v q.1) > d (v r.1) + 1 := by
    have h₁ := d.strictAnti_specializes hqp'
      (hinj.ne (fun h => hqp.ne (Subtype.ext h)))
    have h₂ := d.strictAnti_specializes hpr'
      (hinj.ne (fun h => hpr.ne (Subtype.ext h)))
    omega
  have hrx : v r.1 ⤳ x := by
    have h : v r.1 ∈ Set.range (X.fromSpecStalk x) := ⟨r.1, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h
  have hlow : k ≤ d (v r.1) := by
    by_cases heq : v r.1 = x
    · simpa only [heq, hd, hx] using (le_refl (d x))
    · have h := d.strictAnti_specializes hrx heq
      rw [hd x, hx] at h
      omega
  have hqF : v q.1 ∈ SheafOfModules.supp F :=
    mem_supp_fromSpecStalk_of_mem_support F x q.1 q.2
  have hupp : d (v q.1) ≤ k + 1 := by
    rw [hd]
    exact hsupport _ hqF
  omega

/-- A module whose support has dimension at most one and contains a prime other than the closed
point has support of dimension exactly one. -/
private theorem supportDim_eq_one_of_mem_nonclosed
    {R M : Type*} [CommRing R] [IsLocalRing R]
    [AddCommGroup M] [Module R M]
    (hbound : Module.supportDim R M ≤ 1)
    (p : PrimeSpectrum R) (hp : p ∈ Module.support R M)
    (hne : p ≠ IsLocalRing.closedPoint R) :
    Module.supportDim R M = 1 := by
  have hle : p ≤ IsLocalRing.closedPoint R :=
    IsLocalRing.le_maximalIdeal p.isPrime.ne_top
  have hclosed : IsLocalRing.closedPoint R ∈ Module.support R M :=
    Module.mem_support_mono hle hp
  have hlt : (⟨p, hp⟩ : Module.support R M) <
      ⟨IsLocalRing.closedPoint R, hclosed⟩ :=
    lt_of_le_of_ne hle (fun h => hne (congrArg Subtype.val h))
  exact le_antisymm hbound
    ((ENat.WithBot.add_one_le_iff (n := 0)).mpr (Order.krullDim_pos_iff.mpr ⟨_, _, hlt⟩))

/-- The generic point of an irreducible component of the support, read in the ambient scheme, is a
generic point of the image of that component. -/
private theorem supportComponent_isGenericPoint {X : Scheme.{u}}
    (F : X.Modules) [F.IsCoherent]
    [QuasiSober (SheafOfModules.supp F)]
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X)) :
    IsGenericPoint (Z.2.1.genericPoint).1
      (Subtype.val '' (Z : Set (SheafOfModules.supp F)) : Set X) := by
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  change closure ({(Z.2.1.genericPoint).1} : Set X) = _
  rw [← Set.image_singleton,
    (SheafOfModules.isClosed_supp F).isClosedEmbedding_subtypeVal.closure_image_eq,
    (Z.2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)).def]

/-- A component of the support passing through `x` is cut out by a minimal prime of the support of
the stalk at `x`. -/
private theorem exists_minimalSupportPrime_over_component {X : Scheme.{u}}
    (F : X.Modules) [F.IsCoherent]
    [QuasiSober (SheafOfModules.supp F)] (x : X)
    (Z : irreducibleComponents (SheafOfModules.supp F : Set X))
    (hxZ : x ∈ Subtype.val '' (Z : Set (SheafOfModules.supp F))) :
    letI := stalkModule (X := X.toRingedSpace) F x
    ∃ p : PrimeSpectrum (X.presheaf.stalk x),
      Minimal (· ∈ Module.support (X.presheaf.stalk x) (abStalk F x)) p ∧
        X.fromSpecStalk x p = (Z.2.1.genericPoint).1 := by
  let : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let := stalkModule (X := X.toRingedSpace) F x
  have hη := supportComponent_isGenericPoint F Z
  obtain ⟨p, hp⟩ : (Z.2.1.genericPoint).1 ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hη.specializes hxZ
  refine ⟨p, ⟨?_, ?_⟩, hp⟩
  · exact (mem_support_stalk_iff F x p).mpr (hp ▸ Z.2.1.genericPoint.property)
  · intro q hq hqp
    let ηq : SheafOfModules.supp F := ⟨X.fromSpecStalk x q,
      (mem_support_stalk_iff F x q).mp hq⟩
    have hspec : ηq ⤳ Z.2.1.genericPoint := by
      apply Topology.IsEmbedding.subtypeVal.isInducing.specializes_iff.mp
      change X.fromSpecStalk x q ⤳ (Z.2.1.genericPoint).1
      rw [← hp]
      exact ((PrimeSpectrum.le_iff_specializes q p).mp hqp).map
        (X.fromSpecStalk x).continuous
    have hZ := Z.2.1.isGenericPoint_genericPoint
      (isClosed_of_mem_irreducibleComponents _ Z.2)
    have hsub : (Z : Set (SheafOfModules.supp F)) ⊆ closure ({ηq} : Set _) := by
      rw [← hZ.def]
      exact hspec.closure_subset
    have heq : ηq = Z.2.1.genericPoint :=
      (show IsGenericPoint ηq (Z : Set (SheafOfModules.supp F)) from
        subset_antisymm (Z.2.2 isIrreducible_singleton.closure hsub) hsub).eq hZ
    exact le_of_eq ((X.fromSpecStalk x).isEmbedding.injective
      (hp.trans (congrArg Subtype.val heq).symm))

/-- Conversely, every minimal prime of the support of the stalk at `x` is cut out by a component
of the support passing through `x`. -/
private theorem exists_component_over_minimalSupportPrime {X : Scheme.{u}}
    (F : X.Modules) [F.IsCoherent]
    [QuasiSober (SheafOfModules.supp F)] (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x))
    (hp : letI := stalkModule (X := X.toRingedSpace) F x
      Minimal (· ∈ Module.support (X.presheaf.stalk x) (abStalk F x)) p) :
    ∃ Z : irreducibleComponents (SheafOfModules.supp F : Set X),
      x ∈ Subtype.val '' (Z : Set (SheafOfModules.supp F)) ∧
        X.fromSpecStalk x p = (Z.2.1.genericPoint).1 := by
  let : F.IsFiniteType := isFiniteType_of_isCoherent F
  let : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  let := stalkModule (X := X.toRingedSpace) F x
  let η : SheafOfModules.supp F := ⟨X.fromSpecStalk x p,
    (mem_support_stalk_iff F x p).mp hp.1⟩
  obtain ⟨Z, hZ, hsub⟩ := exists_mem_irreducibleComponents_subset_of_isIrreducible
    (closure ({η} : Set (SheafOfModules.supp F))) isIrreducible_singleton.closure
  let Z' : irreducibleComponents (SheafOfModules.supp F : Set X) := ⟨Z, hZ⟩
  have hxZ : x ∈ Subtype.val '' (Z' : Set (SheafOfModules.supp F)) := by
    have hclosed : IsClosed (Subtype.val '' (Z' : Set (SheafOfModules.supp F))) :=
      (SheafOfModules.isClosed_supp F).isClosedEmbedding_subtypeVal.isClosedMap _
        (isClosed_of_mem_irreducibleComponents _ hZ)
    apply (specializes_fromSpecStalk x p).mem_closed hclosed
    exact ⟨η, hsub (subset_closure rfl), rfl⟩
  obtain ⟨q, hq, heq⟩ := exists_minimalSupportPrime_over_component F x Z' hxZ
  have hqp : q ≤ p := by
    apply (PrimeSpectrum.le_iff_specializes q p).mpr
    apply (X.fromSpecStalk x).isEmbedding.isInducing.specializes_iff.mp
    rw [heq]
    exact (supportComponent_isGenericPoint F Z').specializes
      ⟨η, hsub (subset_closure rfl), rfl⟩
  have hpq : p = q := le_antisymm (hp.2 hq.1 hqp) hqp
  exact ⟨Z', hxZ, hpq ▸ heq⟩

end Stacks.Chow
