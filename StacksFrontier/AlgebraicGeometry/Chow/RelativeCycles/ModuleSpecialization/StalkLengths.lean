module

public import Mathlib.LinearAlgebra.TensorProduct.Quotient
public import Mathlib.RingTheory.Flat.TorsionFree
public import Mathlib.RingTheory.Ideal.Quotient.Operations
public import Mathlib.RingTheory.TensorProduct.Quotient
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.RestrictedDivisors
public import StacksFrontier.AlgebraicGeometry.Chow.CoherentCycle.Support
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.LocalizationSequence
public import StacksFrontier.AlgebraicGeometry.Chow.GysinCoherentSheaf
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleComposition
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ModuleFamily
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationCycle
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.Field
public import StacksFrontier.AlgebraicGeometry.Chow.Setup.JacobsonDimension
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Support
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.DimensionFormula
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenaryExamples
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.PullbackSkyscraper
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RelativeAssassin.FlatFibreSupportDimension
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Support
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalk
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.CalculationMultiplicities.SupportLength

/-!
# Specialization of the cycle of a module flat over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K` and residue field `kappa`, let `X`
be a scheme locally of finite type over `R`, let `r >= 0` and let `F` be a coherent
`O_X`-module flat over `R`. If the support of the generic fibre `F_K` has dimension at most `r`,
then the support of the special fibre `F_kappa` has dimension at most `r` as well, and the
specialization map `sp_{X/R} : Z_r(X_K) -> Z_r(X_kappa)` of
`StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecializationCycle` sends `[F_K]_r` to
`[F_kappa]_r`.

## Main results

* `Stacks.Chow.topologicalKrullDim_supp_fiberModule_closedPoint_le` — the dimension bound on the
  special fibre.
* `Stacks.Chow.specializationCycle_familyAssociatedToModule` — the specialization formula
  `sp_{X/R}([F_K]_r) = [F_kappa]_r`.

## Implementation notes

`dim(Supp(F_s))` is the topological Krull dimension of the support of the pullback of `F` to the
scheme-theoretic fibre over `s`. The dimension bound is Stacks 0H3X applied to the irreducible
base `Spec(R)`, whose generic point carries the generic fibre; it is stated for the closed point,
which is the tag's claim, and
`Stacks.Chow.topologicalKrullDim_supp_fiberModule_le_of_genericFibre` records the same bound on
every fibre, which is what the family of cycles of Stacks 0H4Q consumes. The two cycles
`[F_K]_r` and `[F_kappa]_r` are therefore the two members of the family
`Stacks.Chow.familyAssociatedToModule` over the generic and the closed point of `Spec(R)`, whose
residue fields are `K` and `kappa`, so no further identification of `Z_r(X_K)` and
`Z_r(X_kappa)` is needed.

The specialization formula is proved coefficientwise. Since the specialization map commutes with
locally finite sums of cycles, the coefficient of `sp_{X/R}([F_K]_r)` at a point `x` of the
special fibre of delta-dimension `r` is a sum, over the points `xi` of the generic fibre of
delta-dimension `r`, of the multiplicity of `F_K` at `xi` times the coefficient at `x` of
`[\overline{Z_xi}_kappa]_r`. Writing `A` for the local ring of `X` at the image `z` of `x` and
`M` for the stalk of `F` there, those two factors are the length of `M` localized at the prime
of `A` cut out by `xi` and the length of `A/(pi, that prime)`, while the coefficient of
`[F_kappa]_r` at `x` is the length of `M/pi M` for a uniformizer `pi`; the points `xi`
contributing are exactly the minimal primes of the support of `M`, because `pi` acts regularly
on the flat module `M`. The identity is then Stacks 02QG, in the form
`AlgebraicGeometry.length_quotSMulTop_eq_sum_minimal_support`, whose Cohen-Macaulay hypothesis
holds because `M/pi M` has finite length and `pi` is a regular parameter.

The two conclusions of the source are stated as two theorems rather than one conjunction; the
second uses the first to form `[F_kappa]_r`. Mathlib's category of schemes lives in a single
universe and `Spec` of a ring in `Type u` lands in `Scheme.{u}`, so `R` and `X` share the
universe variable `u`. Local Noetherianity of `Spec(R)` is automatic and is not assumed.

## References

* [Stacks Project, Tag 0H4I](https://stacks.math.columbia.edu/tag/0H4I)
* [Stacks Project, Tag 0H3X](https://stacks.math.columbia.edu/tag/0H3X)
* [Stacks Project, Tag 02QG](https://stacks.math.columbia.edu/tag/02QG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow.ModuleSpecialization

/-- The coefficient at a point `x` of the special fibre of the `r`-cycle
`[\overline{Z}_kappa]_r` attached to the point `xi` of the generic fibre. -/
def specializationCoeff {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (r : ℕ) (ξ : f.fiber (genericPoint (Spec (.of R))))
    (x : f.fiber (IsLocalRing.closedPoint R)) : ℤ :=
  let η := genericPoint (Spec (.of R))
  let s : Spec (.of R) := IsLocalRing.closedPoint R
  let J := Scheme.IdealSheafData.vanishingIdeal
    (Closeds.closure ({ξ} : Set (f.fiber η)))
  let h := J.subschemeι ≫ f.fiberι η
  closedSubschemeCycleCoeff (fieldChowSituation ((Spec (.of R)).residueField s))
    (f.fiberToSpecResidueField s) ((h.ker.comap (f.fiberι s)).subschemeι) (r : ℤ) x

/-- The coefficients of the `r`-cycle `[\overline{Z}_kappa]_r` of
`Stacks.Chow.specializationIntegralCycle` are these. -/
private theorem specializationIntegralCycle_apply {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (r : ℕ) (ξ : f.fiber (genericPoint (Spec (.of R))))
    (x : f.fiber (IsLocalRing.closedPoint R)) :
    (specializationIntegralCycle f r ξ).1 x = specializationCoeff f r ξ x :=
  rfl

/-- The specialization map sends the fundamental cycle of the integral closed subscheme of the
generic fibre with generic point `xi` to the cycle with these coefficients. -/
theorem specializationCycle_integralGenericCycle_coeff {R : Type u} [CommRing R]
    [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    [LocallyOfFiniteType f] (r : ℕ) (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hξ : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ))
    (x : f.fiber (IsLocalRing.closedPoint R)) :
    (specializationCycle f r (integralGenericCycle f r ξ)).1 x =
      specializationCoeff f r ξ x := by
  rw [specializationCycle_integralGenericCycle f r ξ hξ]
  exact specializationIntegralCycle_apply f r ξ x

section StalkModules

open Opposite

/-- The stalk `F_x` of an `O_X`-module `F` is a module over the local ring `O_{X,x}`. -/
local instance {X : Scheme.{u}} (F : X.Modules) (x : X) :
    Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
  PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
    (R := X.presheaf) F.val x


attribute [local instance] RingHomInvPair.of_ringEquiv

lemma length_eq_of_semilinearEquiv
    {A B M N : Type*} [Ring A] [Ring B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module B N]
    (σ : A ≃+* B) (e : M ≃ₛₗ[RingHomClass.toRingHom σ] N) :
    Module.length A M = Module.length B N := by
  simp only [Module.length, Order.krullDim_eq_of_orderIso (Submodule.orderIsoMapComap e)]

private lemma isSMulRegular_stalkMap_of_flat {X S : Scheme.{u}}
    (f : X ⟶ S) (F : X.Modules)
    (hflat : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F)
    (x : X) (a : S.presheaf.stalk (f x)) (ha : IsRegular a) :
    IsSMulRegular (F.presheaf.stalk x) ((f.stalkMap x).hom a) := by
  let : Module (S.presheaf.stalk (f x)) (F.presheaf.stalk x) :=
    Module.compHom _ (f.stalkMap x).hom
  have : Module.Flat (S.presheaf.stalk (f x)) (F.presheaf.stalk x) := hflat x
  exact ha.isSMulRegular (M := F.presheaf.stalk x)

end StalkModules

section StalkQuotients

open TensorProduct

private def tensorQuotientEquiv {A B M : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M]
    (h : Function.Surjective (algebraMap A B)) :
    B ⊗[A] M ≃ₗ[A] M ⧸ ((RingHom.ker (algebraMap A B)) • (⊤ : Submodule A M)) :=
  (TensorProduct.congr
    (Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId A B) h).symm.toLinearEquiv
    (LinearEquiv.refl A M)).trans
      (TensorProduct.quotTensorEquivQuotSMul M _)

private lemma length_tensor_eq_length_quotient {A B M : Type*} [CommRing A] [CommRing B]
    [Algebra A B] [AddCommGroup M] [Module A M]
    (h : Function.Surjective (algebraMap A B)) :
    Module.length B (B ⊗[A] M) =
      Module.length A (M ⧸ ((RingHom.ker (algebraMap A B)) • (⊤ : Submodule A M))) := by
  rw [← Module.length_eq_of_surjective h]
  exact (tensorQuotientEquiv (M := M) h).length_eq

lemma length_pullback_stalk_eq_length_quotient {Y X : Scheme.{u}} (i : Y ⟶ X)
    [IsPreimmersion i] (F : X.Modules) (y : Y) :
    letI : Module (X.presheaf.stalk (i y)) (F.presheaf.stalk (i y)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val (i y)
    let G := (Scheme.Modules.pullback i).obj F
    letI : Module (Y.presheaf.stalk y) (G.presheaf.stalk y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) G.val y
    Module.length (Y.presheaf.stalk y) (G.presheaf.stalk y) =
      Module.length (X.presheaf.stalk (i y))
        ((F.presheaf.stalk (i y)) ⧸ ((RingHom.ker (i.stalkMap y).hom) •
          (⊤ : Submodule (X.presheaf.stalk (i y)) (F.presheaf.stalk (i y))))) := by
  let A := X.presheaf.stalk (i y)
  let B := Y.presheaf.stalk y
  let M := F.presheaf.stalk (i y)
  let G := (Scheme.Modules.pullback i).obj F
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val (i y)
  let : Module B (G.presheaf.stalk y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := Y.presheaf) G.val y
  let : Algebra A B := (i.stalkMap y).hom.toAlgebra
  obtain ⟨e, _⟩ := RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
    i.toLRSHom.toShHom F y
  exact (@LinearEquiv.length_eq B (G.presheaf.stalk y) inferInstance inferInstance
      (PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := Y.presheaf) G.val y) (B ⊗[A] M) inferInstance inferInstance e).trans
    (length_tensor_eq_length_quotient (i.stalkMap_surjective y))

lemma length_pullback_stalk {Y X : Scheme.{u}} (i : Y ⟶ X)
    [IsPreimmersion i] (F : X.Modules) (y : Y) :
    letI : Module (X.presheaf.stalk (i y)) (F.presheaf.stalk (i y)) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val (i y)
    Stacks.Chow.sheafMultiplicity ((Scheme.Modules.pullback i).obj F) y =
      ((Module.length (X.presheaf.stalk (i y))
        ((F.presheaf.stalk (i y)) ⧸ ((RingHom.ker (i.stalkMap y).hom) •
          (⊤ : Submodule (X.presheaf.stalk (i y)) (F.presheaf.stalk (i y)))))).toNat : ℤ) := by
  exact congrArg (fun n : ℕ∞ ↦ (n.toNat : ℤ)) (length_pullback_stalk_eq_length_quotient i F y)

lemma sheafMultiplicity_pullback_of_stalkMap_isIso {Y X : Scheme.{u}}
    (i : Y ⟶ X) [IsPreimmersion i] (F : X.Modules) (y : Y)
    [IsIso (i.stalkMap y)] :
    Stacks.Chow.sheafMultiplicity ((Scheme.Modules.pullback i).obj F) y =
      Stacks.Chow.sheafMultiplicity F (i y) := by
  let : Module (X.presheaf.stalk (i y)) (F.presheaf.stalk (i y)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val (i y)
  have hker : RingHom.ker (i.stalkMap y).hom = ⊥ :=
    RingHom.ker_coe_equiv (asIso (i.stalkMap y)).commRingCatIsoToRingEquiv
  rw [length_pullback_stalk, hker,
    Submodule.bot_smul (⊤ : Submodule (X.presheaf.stalk (i y)) (F.presheaf.stalk (i y)))]
  rw [(Submodule.quotEquivOfEqBot
    (⊥ : Submodule (X.presheaf.stalk (i y)) (F.presheaf.stalk (i y))) rfl).length_eq]
  rfl

end StalkQuotients

section FiberParameters

open TensorProduct

private lemma injective_of_localization_of_isLocalHom {A B : Type*}
    [CommRing A] [CommRing B] [Algebra A B]
    (S : Submonoid A) [IsLocalization S B] [IsLocalHom (algebraMap A B)] :
    Function.Injective (algebraMap A B) := by
  have hS : S ≤ IsUnit.submonoid A := fun s hs ↦
    isUnit_of_map_unit (algebraMap A B) s (IsLocalization.map_units B ⟨s, hs⟩)
  exact (IsLocalization.atUnits A S hS (S := B)).injective

private lemma ker_tensor_includeLeft {R A B : Type*}
    [CommRing R] [CommRing A] [CommRing B] [Algebra R A] [Algebra R B]
    (hB : Function.Surjective (algebraMap R B)) :
    RingHom.ker (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) =
      (RingHom.ker (algebraMap R B)).map (algebraMap R A) := by
  let I := RingHom.ker (algebraMap R B)
  let eB : (R ⧸ I) ≃ₐ[R] B :=
    Ideal.quotientKerAlgEquivOfSurjective (f := Algebra.ofId R B) hB
  let e : (A ⧸ I.map (algebraMap R A)) ≃ₐ[A] A ⊗[R] B :=
    (Algebra.TensorProduct.quotIdealMapEquivTensorQuot A I).trans
      (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) eB)
  have he (a : A) : e (Ideal.Quotient.mk _ a) = a ⊗ₜ[R] (1 : B) := by
    simp [e]
  ext a
  change (a ⊗ₜ[R] (1 : B)) = 0 ↔ _
  rw [← he a, ← map_zero e, e.injective.eq_iff]
  exact Ideal.Quotient.eq_zero_iff_mem

private lemma ker_tensor_localization {R A B C : Type*}
    [CommRing R] [CommRing A] [CommRing B] [CommRing C]
    [Algebra R A] [Algebra R B]
    (hB : Function.Surjective (algebraMap R B))
    (φ : A ⊗[R] B →+* C)
    [IsLocalHom (φ.comp Algebra.TensorProduct.includeLeftRingHom)]
    (S : Submonoid (A ⊗[R] B))
    (hφ : letI : Algebra (A ⊗[R] B) C := φ.toAlgebra; IsLocalization S C) :
    RingHom.ker (φ.comp Algebra.TensorProduct.includeLeftRingHom) =
      (RingHom.ker (algebraMap R B)).map (algebraMap R A) := by
  let : Algebra (A ⊗[R] B) C := φ.toAlgebra
  let : IsLocalization S C := hφ
  have hsurj : Function.Surjective
      (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) :=
    Algebra.TensorProduct.includeLeft_surjective A A hB
  have : IsLocalHom φ := ⟨by
    intro z hz
    obtain ⟨a, rfl⟩ := hsurj z
    exact (isUnit_of_map_unit (φ.comp Algebra.TensorProduct.includeLeftRingHom) a hz).map
      Algebra.TensorProduct.includeLeftRingHom⟩
  have hφinj : Function.Injective φ := injective_of_localization_of_isLocalHom S
  rw [RingHom.ker_comp_of_injective _ hφinj]
  exact ker_tensor_includeLeft hB

private lemma pullback_fst_stalkMap_ker {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [SurjectiveOnStalks g]
    (x : (pullback f g).carrier) :
    let h : (pullback.fst f g ≫ f) x = (pullback.snd f g ≫ g) x :=
      congrArg (fun k : pullback f g ⟶ S ↦ k x) pullback.condition
    RingHom.ker ((pullback.fst f g).stalkMap x).hom =
      (RingHom.ker (eqToHom (congrArg S.presheaf.stalk h) ≫
        g.stalkMap (pullback.snd f g x)).hom).map
          (f.stalkMap (pullback.fst f g x)).hom := by
  dsimp only
  let h : (pullback.fst f g ≫ f) x = (pullback.snd f g ≫ g) x :=
    congrArg (fun k : pullback f g ⟶ S ↦ k x) pullback.condition
  let R := S.presheaf.stalk ((pullback.fst f g ≫ f) x)
  let A := X.presheaf.stalk (pullback.fst f g x)
  let B := Y.presheaf.stalk (pullback.snd f g x)
  let β : R ⟶ B := eqToHom (congrArg S.presheaf.stalk h) ≫
    g.stalkMap (pullback.snd f g x)
  let : Algebra R A := (f.stalkMap (pullback.fst f g x)).hom.toAlgebra
  let : Algebra R B := β.hom.toAlgebra
  have hβ : Function.Surjective β.hom :=
    (g.stalkMap_surjective _).comp
      (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg S.presheaf.stalk h))).2
  obtain ⟨φ, hφl, hφr, T, hT⟩ :=
    AlgebraicGeometry.BaseChangeStalk.pullback_stalk_isLocalization f g x
  change A ⊗[R] B →+* (pullback f g).presheaf.stalk x at φ
  change φ.comp (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B) =
    ((pullback.fst f g).stalkMap x).hom at hφl
  have : IsLocalHom (φ.comp (Algebra.TensorProduct.includeLeftRingHom : A →+* A ⊗[R] B)) := by
    rw [hφl]
    infer_instance
  have hk := ker_tensor_localization (R := R) (A := A) (B := B) hβ φ T hT
  rwa [hφl] at hk

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

private lemma isField_stalk_spec_field (k : Type u) [Field k]
    (p : Spec (.of k)) : IsField ((Spec (.of k)).presheaf.stalk p) := by
  obtain rfl : p = IsLocalRing.closedPoint k := Subsingleton.elim _ _
  exact (stalkClosedPointIso (.of k)).commRingCatIsoToRingEquiv.isField
    (Field.toIsField k)

lemma fiber_stalkMap_ker {X S : Scheme.{u}} (f : X ⟶ S)
    (s : S) (x : f.fiber s) :
    RingHom.ker ((f.fiberι s).stalkMap x).hom =
      (IsLocalRing.maximalIdeal (S.presheaf.stalk (f (f.fiberι s x)))).map
        (f.stalkMap (f.fiberι s x)).hom := by
  let pY := f.fiberToSpecResidueField s
  let h : (f.fiberι s ≫ f) x = (pY ≫ S.fromSpecResidueField s) x :=
    congrArg (fun k : f.fiber s ⟶ S ↦ k x) pullback.condition
  let β : S.presheaf.stalk ((f.fiberι s ≫ f) x) ⟶ (Spec (S.residueField s)).presheaf.stalk (pY x) :=
    eqToHom (congrArg S.presheaf.stalk h) ≫ (S.fromSpecResidueField s).stalkMap (pY x)
  have hβ : Function.Surjective β.hom :=
    ((S.fromSpecResidueField s).stalkMap_surjective (pY x)).comp
      (ConcreteCategory.bijective_of_isIso (eqToHom (congrArg S.presheaf.stalk h))).2
  have hfield := isField_stalk_spec_field (S.residueField s) (pY x)
  let : Field ((Spec (S.residueField s)).presheaf.stalk (pY x)) := hfield.toField
  have : IsLocalHom (β.hom : _ →+* _) := IsLocalHom.of_surjective _ hβ
  have hβker : RingHom.ker β.hom = IsLocalRing.maximalIdeal _ := by
    ext a
    change β.hom a = 0 ↔ _
    rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact ⟨fun ha hu ↦ not_isUnit_zero (ha ▸ hu.map β.hom), fun ha ↦ Classical.byContradiction
      fun hn ↦ ha (isUnit_of_map_unit β.hom a (isUnit_iff_ne_zero.mpr hn))⟩
  exact (pullback_fst_stalkMap_ker f (S.fromSpecResidueField s) x).trans
    (congrArg (Ideal.map _) hβker)

lemma exists_regular_fiber_parameter {R : Type u} [CommRing R] [IsDomain R]
    [IsDiscreteValuationRing R] {X : Scheme.{u}} (f : X ⟶ Spec (.of R))
    (F : X.Modules) (hflat : AlgebraicGeometry.IsFlatOver f.toLRSHom.toShHom F)
    (x : f.fiber (IsLocalRing.closedPoint R)) :
    let z := f.fiberι (IsLocalRing.closedPoint R) x
    letI : Module (X.presheaf.stalk z) (F.presheaf.stalk z) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val z
    ∃ a : X.presheaf.stalk z,
      a ∈ IsLocalRing.maximalIdeal (X.presheaf.stalk z) ∧
      IsSMulRegular (F.presheaf.stalk z) a ∧
      RingHom.ker ((f.fiberι (IsLocalRing.closedPoint R)).stalkMap x).hom = Ideal.span {a} := by
  let s : Spec (.of R) := IsLocalRing.closedPoint R
  let z := f.fiberι s x
  let D := (Spec (.of R)).presheaf.stalk (f z)
  let A := X.presheaf.stalk z
  let M := F.presheaf.stalk z
  let : Module A M :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val z
  have hz : f z = s := by
    have hz' : z ∈ Set.range (f.fiberι s) := ⟨x, rfl⟩
    rwa [f.range_fiberι s] at hz'
  let e : R ≃+* D := ((stalkClosedPointIso (.of R)).symm ≪≫
    eqToIso (congrArg (Spec (.of R)).presheaf.stalk hz.symm)).commRingCatIsoToRingEquiv
  have : IsDomain D := e.symm.toMulEquiv.isDomain_iff.mpr inferInstance
  have : IsDiscreteValuationRing D :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e
  obtain ⟨π, hπ⟩ := IsDiscreteValuationRing.exists_irreducible D
  let a := (f.stalkMap z).hom π
  refine ⟨a, ?_, ?_, ?_⟩
  · change ¬IsUnit a
    intro ha
    exact hπ.not_isUnit (isUnit_of_map_unit (f.stalkMap z).hom π ha)
  · exact isSMulRegular_stalkMap_of_flat f F hflat z π (IsRegular.of_ne_zero hπ.ne_zero)
  · rw [fiber_stalkMap_ker f (IsLocalRing.closedPoint R) x, hπ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]

end FiberParameters

section LocalizedStalks

attribute [local instance] RingHomInvPair.of_ringEquiv

private lemma comap_maximalIdeal_stalkSpecializes {X : Scheme.{u}} {x y : X} (h : y ⤳ x)
    (p : PrimeSpectrum (X.presheaf.stalk x)) (hp : y = X.fromSpecStalk x p) :
    (IsLocalRing.maximalIdeal (X.presheaf.stalk y)).comap
      (X.presheaf.stalkSpecializes h).hom = p.asIdeal := by
  have h' : PrimeSpectrum.comap (X.presheaf.stalkSpecializes h).hom
      (IsLocalRing.closedPoint (X.presheaf.stalk y)) = p := by
    apply (X.fromSpecStalk x).isEmbedding.injective
    change (Spec.map (X.presheaf.stalkSpecializes h) ≫ X.fromSpecStalk x)
      (IsLocalRing.closedPoint _) = _
    rw [Scheme.SpecMap_stalkSpecializes_fromSpecStalk, Scheme.fromSpecStalk_closedPoint]
    exact hp
  exact congrArg PrimeSpectrum.asIdeal h'

private lemma primeCompl_comap_maximalIdeal_stalkSpecializes {X : Scheme.{u}} (x : X)
    (p : PrimeSpectrum (X.presheaf.stalk x)) :
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk (X.fromSpecStalk x p))).comap
      (X.presheaf.stalkSpecializes (specializes_fromSpecStalk x p)).hom).primeCompl =
        p.asIdeal.primeCompl := by
  ext a
  change a ∉ _ ↔ a ∉ _
  rw [comap_maximalIdeal_stalkSpecializes _ p rfl]

/-- The stalk of `F` at `fromSpecStalk x p` is the localization of the stalk at `x` at `p`. -/
private lemma isLocalizedModule_primeCompl_fromSpecStalk {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule F x
    letI := Stacks.ModuleStalkSpecialization.stalkSpecializesModule F
      (specializes_fromSpecStalk x p)
    IsLocalizedModule p.asIdeal.primeCompl
      (Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F (specializes_fromSpecStalk x p)) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule F x
  let := Stacks.ModuleStalkSpecialization.stalkSpecializesModule F
    (specializes_fromSpecStalk x p)
  have hp := Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes F
    (specializes_fromSpecStalk x p)
  change IsLocalizedModule
    ((IsLocalRing.maximalIdeal (X.presheaf.stalk (X.fromSpecStalk x p))).comap
      (X.presheaf.stalkSpecializes (specializes_fromSpecStalk x p)).hom).primeCompl _ at hp
  rwa [primeCompl_comap_maximalIdeal_stalkSpecializes x p] at hp

lemma fromSpecStalk_mem_supp_iff {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule F x
    X.fromSpecStalk x p ∈ SheafOfModules.supp F ↔
      p ∈ Module.support (X.presheaf.stalk x) (F.presheaf.stalk x) := by
  let y := X.fromSpecStalk x p
  let h := specializes_fromSpecStalk x p
  let := Stacks.ModuleStalkSpecialization.stalkModule F x
  let := Stacks.ModuleStalkSpecialization.stalkModule F y
  let := Stacks.ModuleStalkSpecialization.stalkSpecializesModule F h
  have := isLocalizedModule_primeCompl_fromSpecStalk F x p
  let φ := Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F h
  let e := IsLocalizedModule.iso p.asIdeal.primeCompl φ
  change (∃ a : F.presheaf.stalk y, a ≠ 0) ↔ _
  simp only [Module.mem_support_iff]
  exact ⟨fun ⟨a, ha⟩ ↦ e.toEquiv.nontrivial_congr.mpr ⟨0, a, ha.symm⟩,
    fun hn ↦ have := e.toEquiv.nontrivial_congr.mp hn; exists_ne 0⟩

private lemma length_eq_localized_of_isLocalizedModule
    {A B M N : Type*} [CommRing A] [CommRing B] [Algebra A B]
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] [Module B N]
    [IsScalarTower A B N] (S : Submonoid A) [IsLocalization S B]
    (φ : M →ₗ[A] N) [IsLocalizedModule S φ] :
    Module.length B N = Module.length (Localization S) (LocalizedModule S M) := by
  let L := Localization S
  let eR : L ≃ₐ[A] B := IsLocalization.algEquiv S L B
  let eM := IsLocalizedModule.iso S φ
  let : Module L N := Module.compHom N eR.toRingHom
  have : IsScalarTower A L N := IsScalarTower.of_algebraMap_smul fun a n ↦ by
    change eR (algebraMap A L a) • n = a • n
    rw [eR.commutes, IsScalarTower.algebraMap_smul B]
  let e : LocalizedModule S M ≃ₛₗ[RingHomClass.toRingHom eR.toRingEquiv] N :=
    { __ := eM.toAddEquiv
      map_smul' a m :=
        (IsLocalization.linearMap_compatibleSMul S L (LocalizedModule S M) N).map_smul
          eM.toLinearMap a m }
  exact (length_eq_of_semilinearEquiv eR.toRingEquiv e).symm

lemma sheafMultiplicity_fromSpecStalk_eq_localized_length
    {X : Scheme.{u}} (F : X.Modules) [F.IsQuasicoherent]
    (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule F x
    Stacks.Chow.sheafMultiplicity F (X.fromSpecStalk x p) =
      ((Module.length (Localization.AtPrime p.asIdeal)
        (LocalizedModule p.asIdeal.primeCompl (F.presheaf.stalk x))).toNat : ℤ) := by
  let y := X.fromSpecStalk x p
  let h := specializes_fromSpecStalk x p
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes h).hom.toAlgebra
  let := Stacks.ModuleStalkSpecialization.stalkModule F x
  let := Stacks.ModuleStalkSpecialization.stalkModule F y
  let := Stacks.ModuleStalkSpecialization.stalkSpecializesModule F h
  have : IsScalarTower (X.presheaf.stalk x) (X.presheaf.stalk y)
      (F.presheaf.stalk y) := IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let φ := Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F h
  have := isLocalizedModule_primeCompl_fromSpecStalk F x p
  have : IsLocalization.AtPrime (X.presheaf.stalk y) p.asIdeal := by
    have hp := Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes h
    change IsLocalization
      ((IsLocalRing.maximalIdeal (X.presheaf.stalk y)).comap
        (X.presheaf.stalkSpecializes h).hom).primeCompl (X.presheaf.stalk y) at hp
    rwa [primeCompl_comap_maximalIdeal_stalkSpecializes x p] at hp
  exact congrArg (fun n : ℕ∞ ↦ (n.toNat : ℤ))
    (length_eq_localized_of_isLocalizedModule p.asIdeal.primeCompl φ)

lemma minimal_support_stalk_iff {X : Scheme.{u}} (F : X.Modules)
    [F.IsQuasicoherent] (x : X) (p : PrimeSpectrum (X.presheaf.stalk x)) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule F x
    Minimal (· ∈ Module.support (X.presheaf.stalk x) (F.presheaf.stalk x)) p ↔
      X.fromSpecStalk x p ∈ SheafOfModules.supp F ∧
        ∀ y ∈ SheafOfModules.supp F, y ⤳ X.fromSpecStalk x p → y = X.fromSpecStalk x p := by
  let := Stacks.ModuleStalkSpecialization.stalkModule F x
  refine ⟨fun hp ↦ ⟨(fromSpecStalk_mem_supp_iff F x p).mpr hp.1, fun y hy hyp ↦ ?_⟩,
    fun ⟨hp, hmin⟩ ↦ ⟨(fromSpecStalk_mem_supp_iff F x p).mp hp, fun q hq hqp ↦ ?_⟩⟩
  · have hyr : y ∈ Set.range (X.fromSpecStalk x) := by
      rw [Scheme.range_fromSpecStalk]
      exact hyp.trans (specializes_fromSpecStalk x p)
    obtain ⟨q, rfl⟩ := hyr
    have hq := (fromSpecStalk_mem_supp_iff F x q).mp hy
    have hqp : q.asIdeal ≤ p.asIdeal := (PrimeSpectrum.le_iff_specializes q p).mpr
      ((X.fromSpecStalk x).isEmbedding.isInducing.specializes_iff.mp hyp)
    exact congrArg (X.fromSpecStalk x) (PrimeSpectrum.ext (le_antisymm hqp (hp.2 hq hqp)))
  · have hspec := ((PrimeSpectrum.le_iff_specializes q p).mp hqp).map
      (X.fromSpecStalk x).continuous
    have heq := hmin (X.fromSpecStalk x q) ((fromSpecStalk_mem_supp_iff F x q).mpr hq) hspec
    rw [← (X.fromSpecStalk x).isEmbedding.injective heq]

lemma ker_stalkMap_le_of_fromSpecStalk_mem_range {X Y : Scheme.{u}}
    (i : Y ⟶ X) [IsPreimmersion i] (x : Y) (p : PrimeSpectrum (X.presheaf.stalk (i x)))
    (hp : X.fromSpecStalk (i x) p ∈ Set.range i) :
    RingHom.ker (i.stalkMap x).hom ≤ p.asIdeal := by
  obtain ⟨y, hy⟩ := hp
  have h : i y ⤳ i x := hy.symm ▸ specializes_fromSpecStalk (i x) p
  have h' : y ⤳ x := i.isEmbedding.isInducing.specializes_iff.mp h
  rw [← comap_maximalIdeal_stalkSpecializes h p hy]
  intro a ha
  change ¬IsUnit (X.presheaf.stalkSpecializes h a)
  intro hu
  have hz : (i.stalkMap y) (X.presheaf.stalkSpecializes h a) = 0 := by
    rw [i.stalkSpecializes_stalkMap_apply y x h', show (i.stalkMap x) a = 0 from ha, map_zero]
  exact not_isUnit_zero (hz ▸ hu.map (i.stalkMap y).hom)

end LocalizedStalks
section ClosureStalks

private lemma ker_stalkMap_eq_prime_of_genericPoint
    {X Y : Scheme.{u}} [IsIntegral Y] (i : Y ⟶ X) [IsPreimmersion i]
    (x : Y) (p : PrimeSpectrum (X.presheaf.stalk (i x)))
    (hp : X.fromSpecStalk (i x) p = i (genericPoint Y)) :
    RingHom.ker (i.stalkMap x).hom = p.asIdeal := by
  apply le_antisymm
  · exact ker_stalkMap_le_of_fromSpecStalk_mem_range i x p
      (hp.symm ▸ Set.mem_range_self (genericPoint Y))
  · let q : PrimeSpectrum (Y.presheaf.stalk x) := ⟨⊥, inferInstance⟩
    let t : PrimeSpectrum (X.presheaf.stalk (i x)) := PrimeSpectrum.comap (i.stalkMap x).hom q
    have ht : X.fromSpecStalk (i x) t = i (Y.fromSpecStalk x q) := by
      change (Spec.map (i.stalkMap x) ≫ X.fromSpecStalk (i x)) q = _
      rw [Scheme.SpecMap_stalkMap_fromSpecStalk]
      rfl
    have hspec : X.fromSpecStalk (i x) p ⤳ X.fromSpecStalk (i x) t := by
      rw [hp, ht]
      exact ((genericPoint_spec Y).specializes (Set.mem_univ _)).map i.continuous
    have hle : p.asIdeal ≤ t.asIdeal := (PrimeSpectrum.le_iff_specializes _ _).mpr
      ((X.fromSpecStalk (i x)).isEmbedding.isInducing.specializes_iff.mp hspec)
    exact hle

end ClosureStalks

section PullbackKernels

open TensorProduct

private lemma ker_stalkMap_comp {X Y S : Scheme.{u}} (i : X ⟶ Y) (f : Y ⟶ S)
    (x : X) :
    RingHom.ker ((i ≫ f).stalkMap x).hom =
      (RingHom.ker (i.stalkMap x).hom).comap (f.stalkMap (i x)).hom := by
  rw [Scheme.Hom.stalkMap_comp]
  rfl

lemma pullback_stalkMap_ker {X Y S : Scheme.{u}}
    (f : X ⟶ S) (g : Y ⟶ S) [SurjectiveOnStalks f] [SurjectiveOnStalks g]
    (x : (pullback f g).carrier) :
    let h : (pullback.fst f g ≫ f) x = (pullback.snd f g ≫ g) x :=
      congrArg (fun k : pullback f g ⟶ S ↦ k x) pullback.condition
    RingHom.ker ((pullback.fst f g ≫ f).stalkMap x).hom =
      RingHom.ker (f.stalkMap (pullback.fst f g x)).hom ⊔
      RingHom.ker (eqToHom (congrArg S.presheaf.stalk h) ≫
        g.stalkMap (pullback.snd f g x)).hom := by
  intro h
  have hsurj : Function.Surjective
      (CommRingCat.Hom.hom (f.stalkMap ((pullback.fst f g) x))) :=
    f.stalkMap_surjective _
  have hfst : RingHom.ker ((pullback.fst f g).stalkMap x).hom =
      (RingHom.ker (eqToHom (congrArg S.presheaf.stalk h) ≫
        g.stalkMap (pullback.snd f g x)).hom).map
          (f.stalkMap (pullback.fst f g x)).hom := pullback_fst_stalkMap_ker f g x
  rw [ker_stalkMap_comp, hfst]
  exact (Ideal.comap_map_of_surjective' _ hsurj _).trans (sup_comm _ _)

lemma ker_stalkMap_congr_eq_prime_of_genericPoint
    {X Y : Scheme.{u}} [IsIntegral Y] (i : Y ⟶ X) [IsPreimmersion i]
    (x : Y) (z : X) (hz : z = i x) (p : PrimeSpectrum (X.presheaf.stalk z))
    (hp : X.fromSpecStalk z p = i (genericPoint Y)) :
    RingHom.ker (eqToHom (congrArg X.presheaf.stalk hz) ≫ i.stalkMap x).hom =
      p.asIdeal := by
  subst z
  simpa using ker_stalkMap_eq_prime_of_genericPoint i x p hp

end PullbackKernels

end Stacks.Chow.ModuleSpecialization

end
