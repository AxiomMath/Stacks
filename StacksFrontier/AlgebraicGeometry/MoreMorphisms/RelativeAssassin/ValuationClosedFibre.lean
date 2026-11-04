module

public import Mathlib.RingTheory.Valuation.ValuationRing
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.ClosedFibreGenericPoint
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FibreStalkModule
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.Scheme.Points.ModuleStalkSpecialization
public import StacksFrontier.RingTheory.AssociatedPrime.FlatOverValuationRing

/-!
# Relative associated points in the closed fibre over a valuation ring

Let `A` be a valuation ring, `f : X ⟶ Spec A` a morphism locally of finite type and `F` a
quasi-coherent `𝒪_X`-module of finite type. Let `y` be a point of `Ass_{X/Spec A}(F)` lying over
the generic point of `Spec A`, let `Y` be the reduced closed subscheme supported on the closure
of `y`, and let `ξ` be a generic point of an irreducible component of the fibre of `Y` over the
closed point of `Spec A`. If `F` is flat over `Spec A` at the image `x` of `ξ` in `X`, then `x`
again lies in `Ass_{X/Spec A}(F)`.

This is the case of a valuation base to which the general statement about relative associated
points in fibres of such a closure is reduced.

## Main results

* `Stacks.RelativeAssassin.stalkFibreIdeal_eq_bot_genericPoint`
* `Stacks.RelativeAssassin.mem_associatedPrimes_stalk_of_mem_relativeAssassin`
* `Stacks.RelativeAssassin.mem_relativeAssassin_of_isGenericPoint_closedFibre`

## Implementation notes

The argument is the commutative algebra of
`Stacks.ValuationRingFibre.maximalIdeal_mem_associatedPrimes_quotient` read through the local
ring `B = 𝒪_{X,x}` and the stalk `N = F_x`, which `B` makes a finite module and `A` a flat one:

* the `A`-algebra structure on `B`, its essential finiteness and the `A`-flatness of `N` come
  from `Stacks.BaseStalk`, which needs only that `x` lies over the closed point of `Spec A`;
* the prime `q` of `B` belonging to `y` is the contraction of the maximal ideal of `𝒪_{X,y}`
  along the comparison of local rings, and that comparison exhibits `𝒪_{X,y}` and `F_y` as the
  localizations of `B` and `N` at `q` (`Stacks.StalkSpecialization` and
  `Stacks.ModuleStalkSpecialization`), which is the shape in which the algebra takes its
  localized hypothesis;
* the radical hypothesis `√(q + 𝔪_A B) = 𝔪_B` is
  `Stacks.ClosedFibreGenericPoint.radical_under_sup_stalkFibreIdeal`, the genericity of `ξ` in
  its component read on the stalk.

Both ends are translated by the fibre dictionary
`Stacks.Divisors.isAssociatedPoint_pullback_iff_quotient`: membership in the relative assassin
is a condition on `F_x ⧸ 𝔪_{Spec A, f x}·F_x`. Over the generic point of the spectrum of a
domain that ideal is zero, which is what turns the hypothesis on `y` into a statement about
`F_y` itself rather than a quotient of it; over the closed point it is the ideal the algebra
quotients by. The algebra delivers Mathlib's radical notion of associated prime and the relative
assassin wants the Stacks Project's strict one, so the conclusion is upgraded by
`Stacks.FibreStalkModule.isAssociatedPrimeStacks_maximalIdeal_of_mem_associatedPrimes`, whose
Noetherian hypothesis is on the closed fibre `B ⧸ 𝔪_A B` — essentially of finite type over the
residue field of `A` — and not on `B`, which need not be Noetherian.

## References

* [Stacks Project, Tag 0GSI](https://stacks.math.columbia.edu/tag/0GSI)
* [Stacks Project, Tag 0GSG](https://stacks.math.columbia.edu/tag/0GSG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace IsLocalRing

universe u

namespace Stacks.RelativeAssassin

/-- Over the generic point of the spectrum of a domain the fibre ideal `𝔪_{f y}·𝒪_{X,y}`
vanishes: the local ring of `Spec A` there is the fraction field of `A`. -/
@[ega "II 7.3.2" "partial"]
theorem stalkFibreIdeal_eq_bot_genericPoint {A : Type u} [CommRing A] [IsDomain A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) (y : X)
    (hy : f y = genericPoint (Spec (.of A))) : f.stalkFibreIdeal y = ⊥ := by
  refine Scheme.Hom.stalkFibreIdeal_eq_bot f y ?_
  rw [hy]
  let : Field ((Spec (.of A)).presheaf.stalk (genericPoint (Spec (.of A)))) :=
    inferInstanceAs (Field (Spec (.of A)).functionField)
  exact IsLocalRing.maximalIdeal_eq_bot

/-- A point of `Ass_{X/Spec A}(F)` lying over the generic point of the spectrum of a domain has
the maximal ideal of its local ring among the associated primes of the stalk `F_y` itself: the
fibre there is the whole generic fibre, so no quotient intervenes. -/
theorem mem_associatedPrimes_stalk_of_mem_relativeAssassin
    {A : Type u} [CommRing A] [IsDomain A] {X : Scheme.{u}} (f : X ⟶ Spec (.of A))
    (F : X.Modules) (y : X) (hy : y ∈ Stacks.Divisors.relativeAssassin f F)
    (hyt : f y = genericPoint (Spec (.of A))) :
    letI := Stacks.ModuleStalkSpecialization.stalkModule F y
    maximalIdeal (X.presheaf.stalk y) ∈
      associatedPrimes (X.presheaf.stalk y) (F.presheaf.stalk y) := by
  let := Stacks.ModuleStalkSpecialization.stalkModule F y
  rw [Stacks.Divisors.mem_relativeAssassin] at hy
  obtain ⟨s, ys, hys, hsy⟩ := hy
  rw [Stacks.Divisors.mem_associatedPoints_iff,
    Stacks.Divisors.isAssociatedPoint_pullback_iff_quotient (f.fiberι s) F ys,
    Scheme.Hom.ker_stalkMap_fiberι f s ys, hsy,
    stalkFibreIdeal_eq_bot_genericPoint f y hyt] at hys
  rw [← LinearEquiv.AssociatedPrimes.eq
    (Submodule.quotEquivOfEqBot
      ((⊥ : Ideal (X.presheaf.stalk y)) • (⊤ : Submodule (X.presheaf.stalk y)
        (F.presheaf.stalk y))) (by simp))]
  exact Stacks.FibreStalkModule.mem_associatedPrimes_of_isAssociatedPrimeStacks hys

/-- **Relative associated points in the closed fibre over a valuation ring.** Let `A` be a
valuation ring, `f : X ⟶ Spec A` locally of finite type and `F` a quasi-coherent finite type
`𝒪_X`-module. Let `y ∈ Ass_{X/Spec A}(F)` lie over the generic point of `Spec A` and let `Y` be
the reduced closed subscheme supported on the closure of `y`. Then a generic point of an
irreducible component of the fibre of `Y` over the closed point of `Spec A` whose image in `X`
is a point where `F` is flat over `Spec A` has that image in `Ass_{X/Spec A}(F)`. -/
theorem mem_relativeAssassin_of_isGenericPoint_closedFibre
    {A : Type u} [CommRing A] [IsDomain A] [ValuationRing A]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType]
    (y : X) (hy : y ∈ Stacks.Divisors.relativeAssassin f F)
    (hyt : f y = genericPoint (Spec (.of A)))
    (Y : X.IdealSheafData)
    (hY : Y = Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X)))
    (ξ : (Y.subschemeι ≫ f).fiber (closedPoint A))
    (hξ : closure ({ξ} : Set ((Y.subschemeι ≫ f).fiber (closedPoint A))) ∈
      irreducibleComponents ((Y.subschemeι ≫ f).fiber (closedPoint A)))
    (hflat : IsFlatOverAt f.toLRSHom.toShHom F
      (Y.subschemeι ((Y.subschemeι ≫ f).fiberι (closedPoint A) ξ))) :
    Y.subschemeι ((Y.subschemeι ≫ f).fiberι (closedPoint A) ξ)
      ∈ Stacks.Divisors.relativeAssassin f F := by
  subst hY
  set x := (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))).subschemeι
    (((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set X))).subschemeι ≫ f).fiberι (closedPoint A) ξ)
  have hx : f x = closedPoint A :=
    Stacks.ClosedFibreGenericPoint.apply_fiberι_comp f
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X))).subschemeι
      (closedPoint A) ξ
  have hyx : y ⤳ x :=
    Stacks.ClosedFibreGenericPoint.specializes_subschemeι_vanishingIdeal_closure y
      (((Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({y} : Set X))).subschemeι ≫ f).fiberι (closedPoint A) ξ)
  have hyJ : y ∈ (Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({y} : Set X))).support :=
    Stacks.ClosedFibreGenericPoint.mem_support_vanishingIdeal_closure y
  let : Algebra A (X.presheaf.stalk x) := (Stacks.BaseStalk.baseStalkHom f x hx).hom.toAlgebra
  let : IsLocalHom (algebraMap A (X.presheaf.stalk x)) :=
    Stacks.BaseStalk.isLocalHom_baseStalkHom f x hx
  let : Algebra.EssFiniteType A (X.presheaf.stalk x) :=
    Stacks.BaseStalk.essFiniteType_baseStalk f x hx
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    Stacks.ModuleStalkSpecialization.stalkModule F x
  let : Module A (F.presheaf.stalk x) := Stacks.BaseStalk.baseStalkModule f F x hx
  let : IsScalarTower A (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : Module.Finite (X.presheaf.stalk x) (F.presheaf.stalk x) :=
    SheafOfModules.finite_stalk X.sheaf F x
  let : Module.Flat A (F.presheaf.stalk x) :=
    Stacks.BaseStalk.flat_of_isFlatOverAt f F x hx hflat
  let : Algebra (X.presheaf.stalk x) (X.presheaf.stalk y) :=
    (X.presheaf.stalkSpecializes hyx).hom.toAlgebra
  let : ((maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x)).IsPrime :=
    Ideal.comap_isPrime _ _
  let : IsLocalization.AtPrime (X.presheaf.stalk y)
      ((maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x)) :=
    Stacks.StalkSpecialization.isLocalization_atPrime_stalkSpecializes hyx
  let : Module (X.presheaf.stalk x) (F.presheaf.stalk y) :=
    Stacks.ModuleStalkSpecialization.stalkSpecializesModule F hyx
  let : Module (X.presheaf.stalk y) (F.presheaf.stalk y) :=
    Stacks.ModuleStalkSpecialization.stalkModule F y
  let : IsScalarTower (X.presheaf.stalk x) (X.presheaf.stalk y) (F.presheaf.stalk y) :=
    IsScalarTower.of_algebraMap_smul fun _ _ ↦ rfl
  let : IsLocalizedModule
      ((maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x)).primeCompl
      (Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F hyx) :=
    Stacks.ModuleStalkSpecialization.isLocalizedModule_atPrime_stalkSpecializes F hyx
  have hI : Ideal.map (algebraMap A (X.presheaf.stalk x)) (maximalIdeal A)
      = f.stalkFibreIdeal x := Stacks.BaseStalk.map_maximalIdeal_baseStalkHom f x hx
  have hqrad : (((maximalIdeal (X.presheaf.stalk y)).under (X.presheaf.stalk x)) ⊔
      Ideal.map (algebraMap A (X.presheaf.stalk x)) (maximalIdeal A)).radical
      = maximalIdeal (X.presheaf.stalk x) := by
    rw [hI]
    exact Stacks.ClosedFibreGenericPoint.radical_under_sup_stalkFibreIdeal f
      (Scheme.IdealSheafData.vanishingIdeal (Closeds.closure ({y} : Set X)))
      (closedPoint A) ξ (by simpa only [genericPoints, Set.mem_ofPred_eq] using hξ) hyJ hyx
  have hcore := Stacks.ValuationRingFibre.maximalIdeal_mem_associatedPrimes_quotient
    (A := A) (Stacks.ModuleStalkSpecialization.stalkSpecializesₗ F hyx) hqrad
    (mem_associatedPrimes_stalk_of_mem_relativeAssassin f F y hy hyt)
  let : Field (A ⧸ maximalIdeal A) := Ideal.Quotient.field _
  let : IsNoetherianRing ((X.presheaf.stalk x) ⧸
      Ideal.map (algebraMap A (X.presheaf.stalk x)) (maximalIdeal A)) :=
    Algebra.EssFiniteType.isNoetherianRing (A ⧸ maximalIdeal A) _
  let : Nontrivial ((X.presheaf.stalk x) ⧸
      Ideal.map (algebraMap A (X.presheaf.stalk x)) (maximalIdeal A)) :=
    Ideal.Quotient.nontrivial_iff.mpr (hI ▸ f.stalkFibreIdeal_ne_top x)
  let : IsLocalRing ((X.presheaf.stalk x) ⧸
      Ideal.map (algebraMap A (X.presheaf.stalk x)) (maximalIdeal A)) :=
    IsLocalRing.of_surjective' (Ideal.Quotient.mk _) Ideal.Quotient.mk_surjective
  let : Module ((X.presheaf.stalk x) ⧸
        Ideal.map (algebraMap A (X.presheaf.stalk x)) (maximalIdeal A))
      ((F.presheaf.stalk x) ⧸
        (Ideal.map (algebraMap A (X.presheaf.stalk x)) (maximalIdeal A) •
          (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)))) :=
    Stacks.FibreStalkModule.quotSMulTopModule _ _
  let : IsScalarTower (X.presheaf.stalk x) ((X.presheaf.stalk x) ⧸
        Ideal.map (algebraMap A (X.presheaf.stalk x)) (maximalIdeal A))
      ((F.presheaf.stalk x) ⧸
        (Ideal.map (algebraMap A (X.presheaf.stalk x)) (maximalIdeal A) •
          (⊤ : Submodule (X.presheaf.stalk x) (F.presheaf.stalk x)))) :=
    Stacks.FibreStalkModule.isScalarTower_quotSMulTop _ _
  have hstrict :=
    Stacks.FibreStalkModule.isAssociatedPrimeStacks_maximalIdeal_of_mem_associatedPrimes
      (Ideal.map (algebraMap A (X.presheaf.stalk x)) (maximalIdeal A)) hcore
  rw [hI] at hstrict
  rw [Stacks.Divisors.mem_relativeAssassin]
  refine ⟨f x, f.asFiber x, ?_, f.fiberι_asFiber x⟩
  rw [Stacks.Divisors.mem_associatedPoints_iff,
    Stacks.Divisors.isAssociatedPoint_pullback_fiberι_iff]
  exact hstrict

end Stacks.RelativeAssassin

end
