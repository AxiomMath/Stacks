module

public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf
public import Mathlib.Algebra.Category.Ring.Limits
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.CategoryTheory.Category.Preorder
public import Mathlib.CategoryTheory.CofilteredSystem
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.Shapes.ConcreteCategory
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.RingTheory.AdicCompletion.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorsOnDerivedCategories
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.Limits.PseudoCoherent
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor
public import StacksFrontier.Homology.DerivedComplete
public import StacksFrontier.Homology.DerivedComplete.DerivedHomCompletionTorSequence
public import StacksFrontier.Homology.DerivedComplete.NoetherianCohomologyAdicCompletion
public import StacksFrontier.Homology.DerivedComplete.NoetherianCompleteIdealPowers
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedChangeOfRings
public import StacksFrontier.Homology.Tor.DerivedChangeOfRingsAdjunction
public import StacksFrontier.Homology.Tor.DerivedExtensionScalars
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.RingTheory.AdicCompletion.Flat

/-!
# Adic systems in the derived category: cohomology of derived reduction, and derived limits

Let `I` be an ideal in a Noetherian ring `A` and let `K` be an object of `D(A)`. If the
cohomology modules of `K` are finite and the cohomology inverse systems of the derived
reductions `K ⊗ᴸ[A] A/Iⁿ` satisfy the Mittag--Leffler condition, then the inverse limits
of those systems are the adic completions of the cohomology modules of `K`.

Conversely one may start from a compatible system of objects `Kₙ` of `D(A/Iⁿ)` rather than
from a single object of `D(A)`. If `A` is Noetherian, `K₁` is bounded above, and every
transition map induces an isomorphism `Kₙ₊₁ ⊗ᴸ[A/Iⁿ⁺¹] A/Iⁿ ≅ Kₙ`, then a derived limit of
the restricted system is bounded above and derived `I`-complete, and it recovers each `Kₙ`
by derived reduction.

## Main definitions

* `Stacks.DerivedLimit.AdicSystem.underlyingSystem`: the inverse system in `D(A)` obtained by
  restricting the
  scalars of a compatible system of objects of the `D(A/Iⁿ)` along the quotient maps.
* `Stacks.DerivedLimit.AdicSystem.restrictScalarsTransitionIso`: the comparison identifying
  restriction through a
  successive quotient with restriction along the composite quotient map.

## Main results

* `adicCompletion_homology_iso_limit_derivedReduction`: the Kollár--Kovács
  comparison between completed cohomology and the inverse limit of the cohomology of the
  derived reductions.
* `Stacks.DerivedLimit.AdicSystem.isDerivedComplete_and_reduction_isIso_of_isDerivedLimit` ([stacks
  09AU]): a
  derived limit of a bounded-above compatible adic system over a Noetherian ring is bounded
  above and derived complete, and its derived reduction to each `A/Iⁿ` is an isomorphism onto
  the given `Kₙ`.

## Implementation notes

Positive powers of `I` are indexed by `n : ℕ` using `I ^ (n + 1)`, as in
`NoetherianAdicCompletion.idealPowerQuotientSystem`. Equality of the two inverse limits in the
source is expressed as an isomorphism of `A`-modules.

The Mittag--Leffler hypothesis enters through the two-term product model for the derived
inverse limit of Stacks 091D: it makes the difference map
`(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))` surjective, hence its cokernel — the first derived inverse limit —
vanishes, and the Milnor sequence of Stacks 0EET collapses to an isomorphism.

For the derived-limit statement the system is presented abstractly: the inverse system in
`D(A)` is an arbitrary functor on `ℕᵒᵖ` together with isomorphisms onto the restrictions of
the `Kₙ`, and the derived limit is supplied together with its Milnor distinguished triangle,
whose middle map is `1 - shift` on the product of the terms. Derived extension of scalars is
taken in the total form of Stacks 0GMT, so the adjunction transposing a map into a derived
restriction is available at each level; boundedness above is recorded as membership in the
minus part of the standard `t`-structure. Rings live in universe `u` and modules in the
independent ambient universe `max u v`. Because the declarations of this section are shared
with `Limits.PseudoCoherent`, whose helpers carry their own universe parameters, the cross-module
calls are given explicit universe arguments; without them the module universe is not pinned
and elaboration reports `max u v =?= u`.

## References

* [Stacks Project, Tag 0EGS](https://stacks.math.columbia.edu/tag/0EGS)
* [Stacks Project, Tag 09AU](https://stacks.math.columbia.edu/tag/09AU)
* Email from Sándor Kovács, 23 February 2018.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.InverseSystem.AdicCompletionCohomology

/-- The constant inverse system of rings with value `A`, the base over which a diagram of
`A`-modules is a compatible system of modules. -/
private abbrev constantRingDiagram (A : Type u) [CommRing A] : ℕᵒᵖ ⥤ RingCat.{u} where
  obj _ := RingCat.of A
  map _ := 𝟙 _
  map_id _ := rfl
  map_comp _ _ := rfl

/-- A diagram of `A`-modules read as a presheaf of modules over the constant system of rings
with value `A`. -/
private def asPresheaf {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{u} A) :
    PresheafOfModules.{u} (constantRingDiagram A) :=
  letI (X : ℕᵒᵖ) : Module ((constantRingDiagram A).obj X)
      ((F ⋙ forget₂ (ModuleCat.{u} A) Ab).obj X) :=
    (F.obj X).isModule
  PresheafOfModules.ofPresheaf (F ⋙ forget₂ (ModuleCat.{u} A) Ab) (by
    intro X Y f r m
    change F.map f (r • m) = r • F.map f m
    exact (F.map f).hom.map_smul r m)

set_option maxHeartbeats 800000 in
-- Transporting the surjectivity across the two product models is elaboration-intensive.
/-- For a Mittag--Leffler inverse system of `A`-modules the difference map
`(xₙ) ↦ (xₙ - fₙ₊₁(xₙ₊₁))` on the product of its terms is surjective. This is the statement
that the system is right acyclic for the inverse-limit functor, transported from the
presheaf-of-modules formulation of Stacks 091D. -/
private theorem delta_epi {A : Type u} [CommRing A] (F : ℕᵒᵖ ⥤ ModuleCat.{u} A)
    (hML : (F ⋙ forget (ModuleCat.{u} A)).IsMittagLeffler) :
    Epi (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) := by
  let R : ℕᵒᵖ ⥤ RingCat.{u} := constantRingDiagram A
  let M : PresheafOfModules.{u} R := asPresheaf F
  obtain ⟨hadd, RF, α, -, -, -, hzero, hshort, -⟩ :=
    ModuleInverseLimit.inverseLimit_hasRightDerivedFunctor_and_computations R
  let := hadd
  have hML' : (M.presheaf ⋙ forget Ab).IsMittagLeffler := hML
  have hz := hzero M hML'
  obtain ⟨w, hw⟩ := hshort M hz
  have hs := (ModuleCat.epi_iff_surjective _).1 hw.epi_g
  rw [ModuleCat.epi_iff_surjective]
  intro y
  let G : ℕ → ModuleCat.{u} (limit R : RingCat.{u}) :=
    fun n ↦ (ModuleInverseLimit.moduleDiagram R M).obj (Opposite.op n)
  let toF : ∀ n : ℕ, G n → F.obj (Opposite.op n) := fun _ z ↦ z
  let toG : ∀ n : ℕ, F.obj (Opposite.op n) → G n := fun _ z ↦ z
  let d : (∏ᶜ G) ⟶ (∏ᶜ G) := 𝟙 _ - Pi.lift fun n : ℕ ↦
    Pi.π G (n + 1) ≫ (ModuleInverseLimit.moduleDiagram R M).map
      (homOfLE (Nat.le_succ n)).op
  let y' : ToType (∏ᶜ G) := (Concrete.productEquiv G).symm
    (fun n ↦ toG n (Concrete.productEquiv (fun n : ℕ ↦ F.obj (Opposite.op n)) y n))
  obtain ⟨x, hx⟩ := hs y'
  let x' : ToType (∏ᶜ fun n : ℕ ↦ F.obj (Opposite.op n)) :=
    (Concrete.productEquiv (fun n : ℕ ↦ F.obj (Opposite.op n))).symm
      (fun n ↦ toF n (Concrete.productEquiv G x n))
  refine ⟨x', ?_⟩
  apply Concrete.limit_ext
  rintro ⟨n⟩
  have hd : d ≫ Pi.π G n = Pi.π G n - Pi.π G (n + 1) ≫
      (ModuleInverseLimit.moduleDiagram R M).map (homOfLE (Nat.le_succ n)).op := by
    rw [show d = 𝟙 _ - Pi.lift (fun n : ℕ ↦ Pi.π G (n + 1) ≫
      (ModuleInverseLimit.moduleDiagram R M).map (homOfLE (Nat.le_succ n)).op) from rfl,
      CategoryTheory.Preadditive.sub_comp, Category.id_comp,
      CategoryTheory.Limits.Pi.lift_comp_π]
  have hn := ConcreteCategory.congr_hom hd x
  rw [ConcreteCategory.comp_apply, hx] at hn
  have heval : (Pi.π G n - Pi.π G (n + 1) ≫
      (ModuleInverseLimit.moduleDiagram R M).map (homOfLE (Nat.le_succ n)).op) x =
      Pi.π G n x - (ModuleInverseLimit.moduleDiagram R M).map
        (homOfLE (Nat.le_succ n)).op (Pi.π G (n + 1) x) := rfl
  rw [heval] at hn
  have hmap (z : G (n + 1)) :
      (ModuleInverseLimit.moduleDiagram R M).map (homOfLE (Nat.le_succ n)).op z =
        F.map (homOfLE (Nat.le_succ n)).op z := by
    rfl
  rw [hmap] at hn
  have hxcomp (j : ℕ) : Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) j x' =
      Pi.π G j x :=
    (Concrete.productEquiv_symm_apply_π _ _ j).trans (Concrete.productEquiv_apply_apply _ _ j)
  have hycomp : Pi.π G n y' = Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n y :=
    (Concrete.productEquiv_symm_apply_π _ _ n).trans (Concrete.productEquiv_apply_apply _ _ n)
  have htarget :
      (Pi.lift fun n : ℕ ↦ Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) ≫
          Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n =
        Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n -
          Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) (n + 1) ≫
            F.map (homOfLE (Nat.le_succ n)).op :=
    CategoryTheory.Limits.Pi.lift_comp_π _ n
  rw [← ConcreteCategory.comp_apply, htarget]
  show Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n x' -
      F.map (homOfLE (Nat.le_succ n)).op
        (Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) (n + 1) x') =
    Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n y
  rw [hxcomp, hxcomp, ← hycomp]
  exact hn.symm

/-- **Stacks 0EGS (Kollár--Kovács).** Let `I` be an ideal of a Noetherian ring `A` and
`K ∈ D(A)`. Suppose that every cohomology module of `K` is finite and, in every degree, the
cohomology inverse system of `K ⊗ᴸ[A] A/Iⁿ` is Mittag--Leffler. Then the inverse limit of
`Hⁱ(K ⊗ᴸ[A] A/Iⁿ)` is isomorphic to the `I`-adic completion of `Hⁱ(K)` for every `i`. -/
@[stacks 0EGS]
public theorem adicCompletion_homology_iso_limit_derivedReduction
    (A : Type u) [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (K : DerivedCategory (ModuleCat.{u} A))
    (T : CochainComplex.DerivedTensor.DerivedTensorProduct A)
    (hK : ∀ i : ℤ,
      Module.Finite A ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K))
    (hML : ∀ i : ℤ,
      (((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{u} A) i) ⋙
        forget (ModuleCat.{u} A)).IsMittagLeffler) :
    ∀ i : ℤ,
      Nonempty
        (ModuleCat.of A
            (AdicCompletion I
              ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) i).obj K)) ≅
          limit ((NoetherianAdicCompletion.idealPowerQuotientSystem I ⋙ T.tensor.obj K) ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{u} A) i)) := by
  let : HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{u} A) :=
    moduleCat_hasExactLimitsOfShape_discrete.{u} A ℕ
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{u} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  obtain ⟨L, hAdj, -, -, hseq⟩ :=
    AdicCompletionTor.derivedCompletion_homology_shortExact A I T
  intro i
  let F := AdicCompletionTor.derivedTensorHomologySystem T I K (i - 1)
  have : Epi (Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ ↦ F.obj (Opposite.op n)) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) :=
    delta_epi F (hML (i - 1))
  have hR1 : IsZero (AdicCompletionTor.firstDerivedInverseLimit F) :=
    isZero_cokernel_of_epi _
  obtain ⟨a, b, w, hab⟩ := hseq K i
  have : Mono b := hab.exact.mono_g_iff.mpr (hR1.eq_of_src _ _)
  let : Epi b := hab.epi_g
  have : IsIso b := isIso_of_mono_of_epi b
  let eb := asIso b
  obtain ⟨hAdj⟩ := hAdj
  obtain ⟨e⟩ := AdicCompletionCohomology.derivedCompletion_homology_iso_adicCompletion
    A I K hK L hAdj i
  exact ⟨e.symm ≪≫ eb⟩

end Stacks.InverseSystem.AdicCompletionCohomology

end

section AdicSystemTowerData

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace Stacks.DerivedLimit.AdicSystem

universe u v

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] StacksDraft.DerivedInverseLimit.extendScalarsGeneral_additive

/-- The canonical surjection from the next ideal-power quotient to the current one. -/
public abbrev quotientTransition {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) :
    A ⧸ I ^ (n + 2) →+* A ⧸ I ^ (n + 1) :=
  Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))

/-- The canonical comparison between successive and direct restriction to `A`.
It is the localization of the degreewise restriction-of-scalars composition isomorphism. -/
public noncomputable abbrev restrictScalarsTransitionIso
    {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) :
    (ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapDerivedCategory ⋙
      (ModuleCat.restrictScalars.{max u v}
        (Ideal.Quotient.mk (I ^ (n + 2)))).mapDerivedCategory ≅
        (ModuleCat.restrictScalars.{max u v}
          (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory :=
  StacksDraft.DerivedInverseLimit.derivedRestrictScalarsComp
    (Ideal.Quotient.mk (I ^ (n + 2))) (quotientTransition I n)
    (Ideal.Quotient.mk (I ^ (n + 1))) (Ideal.Quotient.factor_comp_mk _).symm

/-- The inverse system in `D(A)` obtained by restricting the given quotient-category maps.
Thus the underlying diagram required in 09AU is constructed from the source data. -/
public noncomputable def underlyingSystem
    {A : Type u} [CommRing A] (I : Ideal A)
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (t : ∀ n : ℕ, Kq (n + 1) ⟶
      (ModuleCat.restrictScalars.{max u v}
        (quotientTransition I n)).mapDerivedCategory.obj (Kq n)) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{max u v} A) :=
  Functor.ofOpSequence fun n =>
    (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (I ^ (n + 2)))).mapDerivedCategory.map
      (t n) ≫ (restrictScalarsTransitionIso I n).hom.app (Kq n)

/-- The successor map of the underlying system is the restriction of the given transition. -/
@[simp]
public theorem underlyingSystem_map_succ
    {A : Type u} [CommRing A] (I : Ideal A)
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (t : ∀ n : ℕ, Kq (n + 1) ⟶
      (ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapDerivedCategory.obj (Kq n))
    (n : ℕ) :
    (underlyingSystem I Kq t).map (homOfLE (Nat.le_succ n)).op =
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (I ^ (n + 2)))).mapDerivedCategory.map
        (t n) ≫ (restrictScalarsTransitionIso I n).hom.app (Kq n) :=
  Functor.ofOpSequence_map_homOfLE_succ _ n

/-- A bounded-above projective model of `Kq n` with a fixed upper bound. -/
public structure ProjectiveModel
    {A : Type u} [CommRing A] (I : Ideal A)
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (b : ℤ) (n : ℕ) where
  /-- The underlying complex. -/
  complex : CochainComplex (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))) ℤ
  /-- The complex vanishes above `b`. -/
  isStrictlyLE : complex.IsStrictlyLE b
  /-- Its terms are projective. -/
  projective : ∀ i, Module.Projective (A ⧸ I ^ (n + 1)) (complex.X i)
  /-- The projection to `Kq n`. -/
  iso : DerivedCategory.Q.obj complex ≅ Kq n

/-- The adjacent quotient transition is surjective. -/
public theorem quotientTransition_surjective {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) :
    Function.Surjective (quotientTransition I n) :=
  Ideal.Quotient.factor_surjective _

/-- The kernel of the adjacent quotient transition has square zero. -/
public theorem quotientTransition_ker_sq {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) :
    RingHom.ker (quotientTransition I n) ^ 2 = ⊥ := by
  show RingHom.ker (Ideal.Quotient.factor
    (Ideal.pow_le_pow_right (Nat.le_succ (n + 1)))) ^ 2 = ⊥
  rw [Ideal.Quotient.factor_ker, ← Ideal.map_pow]
  apply le_bot_iff.mp
  have powerLe : (I ^ (n + 1)) ^ 2 ≤ I ^ (n + 2) := by
    rw [← pow_mul]
    exact Ideal.pow_le_pow_right (by omega)
  simpa only [Ideal.map_quotient_self] using
    (Ideal.map_mono (f := Ideal.Quotient.mk (I ^ (n + 2))) powerLe)

/-- A bounded-above `Kq 0` has a bounded-above projective model. -/
public theorem exists_projectiveModel_zero
    {A : Type u} [CommRing A] (I : Ideal A)
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (hbounded : DerivedCategory.TStructure.t.minus (Kq 0)) :
    ∃ b : ℤ, Nonempty (ProjectiveModel.{u, v} I Kq b 0) := by
  obtain ⟨b, hb⟩ := hbounded
  let R := A ⧸ I ^ (0 + 1)
  let K := Kq 0
  have : K.IsLE b := hb
  let P₀ := (DerivedCategory.Q (C := ModuleCat.{max u v} R)).objPreimage K
  have : (DerivedCategory.Q.obj P₀).IsLE b :=
    DerivedCategory.TStructure.t.isLE_of_iso
      ((DerivedCategory.Q (C := ModuleCat.{max u v} R)).objObjPreimageIso K).symm b
  have : P₀.IsLE b := (DerivedCategory.isLE_Q_obj_iff P₀ b).mp inferInstance
  have : (CategoryTheory.isProjective (ModuleCat.{max u v} R)).ContainsZero :=
    ⟨⟨ModuleCat.of R (ULift.{v} (Fin 0 → R)), ModuleCat.isZero_of_subsingleton _,
      Limits.IsZero.projective (ModuleCat.isZero_of_subsingleton _)⟩⟩
  have hpr : ∀ X : ModuleCat.{max u v} R,
      ∃ (Y : ModuleCat.{max u v} R) (_ : Projective Y) (p : Y ⟶ X), Epi p :=
    fun X => ⟨Projective.over X, inferInstance, Projective.π X, inferInstance⟩
  obtain ⟨P, f, hq, hproj, hLE⟩ :=
    (CochainComplex.exists_quasiIso_prop
      (CategoryTheory.isProjective (ModuleCat.{max u v} R)) hpr b).2 P₀
  have := hq
  refine ⟨b, ⟨P, hLE, fun i => ?_, asIso (DerivedCategory.Q.map f) ≪≫
    (DerivedCategory.Q (C := ModuleCat.{max u v} R)).objObjPreimageIso K⟩⟩
  exact (IsProjective.iff_projective (R := R) (P.X i)).2 (hproj i)

/-- The chain-level transition out of the next projective model, with invertible base-change
adjoint and the prescribed derived transition. -/
public structure ProjectiveStep
    {A : Type u} [CommRing A] (I : Ideal A)
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (t : ∀ n : ℕ, Kq (n + 1) ⟶
      (ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapDerivedCategory.obj (Kq n))
    {b : ℤ} {n : ℕ} (model : ProjectiveModel.{u, v} I Kq b n) where
  /-- The next model. -/
  next : ProjectiveModel.{u, v} I Kq b (n + 1)
  /-- The chain-level transition. -/
  chainMap : next.complex ⟶
    ((ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapHomologicalComplex
      (.up ℤ)).obj model.complex
  /-- The degreewise base-change adjoint is invertible. -/
  isIso_adjoint : IsIso (((StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction
    (ModuleCat.extendRestrictScalarsAdj.{max u v} (quotientTransition I n)) (.up ℤ)).homEquiv
      _ _).symm chainMap)
  /-- The chain map localizes to the prescribed transition `t n`. -/
  comm : DerivedCategory.Q.map chainMap ≫
      (ModuleCat.restrictScalars.{max u v}
        (quotientTransition I n)).mapDerivedCategoryFactors.inv.app
        model.complex ≫
      (ModuleCat.restrictScalars.{max u v}
        (quotientTransition I n)).mapDerivedCategory.map model.iso.hom =
    next.iso.hom ≫ t n

/-- One-step lifting of projective models along the quotient transition (0BCA/09AR). -/
public theorem nonempty_projectiveStep
    {A : Type u} [CommRing A] (I : Ideal A)
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (t : ∀ n : ℕ, Kq (n + 1) ⟶
      (ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapDerivedCategory.obj (Kq n))
    (hcompat : ∀ n : ℕ,
      IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, v, u}
        (quotientTransition I n) (t n)))
    {b : ℤ} {n : ℕ} (model : ProjectiveModel.{u, v} I Kq b n) :
    Nonempty (ProjectiveStep.{u, v} I Kq t model) := by
  have := model.isStrictlyLE
  obtain ⟨P, hP, hproj, eP, g, hg, heq⟩ :=
    StacksDraft.DerivedInverseLimit.exists_projective_lift_of_derived_transition.{u, v, u}
      (quotientTransition I n) (quotientTransition_surjective I n)
      ⟨2, quotientTransition_ker_sq I n⟩ (Kq (n + 1)) (Kq n) (t n) (hcompat n)
      model.complex b model.projective model.iso
  exact ⟨⟨⟨P, hP, hproj, eP⟩, g, hg, heq⟩⟩

/-- The recursively chosen projective tower starting from a model of `Kq 0`. -/
public noncomputable def projectiveTower
    {A : Type u} [CommRing A] (I : Ideal A)
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (t : ∀ n : ℕ, Kq (n + 1) ⟶
      (ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapDerivedCategory.obj (Kq n))
    (hcompat : ∀ n : ℕ,
      IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, v, u}
        (quotientTransition I n) (t n)))
    {b : ℤ} (model : ProjectiveModel.{u, v} I Kq b 0) :
    ∀ n : ℕ, ProjectiveModel.{u, v} I Kq b n
  | 0 => model
  | n + 1 =>
    (nonempty_projectiveStep I Kq t hcompat (projectiveTower I Kq t hcompat model n)).some.next

/-- The transition data of the recursively chosen projective tower. -/
public noncomputable def projectiveTowerStep
    {A : Type u} [CommRing A] (I : Ideal A)
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (t : ∀ n : ℕ, Kq (n + 1) ⟶
      (ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapDerivedCategory.obj (Kq n))
    (hcompat : ∀ n : ℕ,
      IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, v, u}
        (quotientTransition I n) (t n)))
    {b : ℤ} (model : ProjectiveModel.{u, v} I Kq b 0) (n : ℕ) :
    ProjectiveStep.{u, v} I Kq t (projectiveTower I Kq t hcompat model n) :=
  (nonempty_projectiveStep I Kq t hcompat (projectiveTower I Kq t hcompat model n)).some

/-- The next model of the `n`-th step of `projectiveTower` is its `(n + 1)`-st model. -/
@[simp]
public theorem projectiveTowerStep_next
    {A : Type u} [CommRing A] (I : Ideal A)
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (t : ∀ n : ℕ, Kq (n + 1) ⟶
      (ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapDerivedCategory.obj (Kq n))
    (hcompat : ∀ n : ℕ,
      IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, v, u}
        (quotientTransition I n) (t n)))
    {b : ℤ} (model : ProjectiveModel.{u, v} I Kq b 0) (n : ℕ) :
    (projectiveTowerStep I Kq t hcompat model n).next =
      projectiveTower I Kq t hcompat model (n + 1) :=
  rfl

/-- **Coherent projective tower.** If `Kq 0` is bounded above and every quotient transition
`t n` has invertible derived base change, then there are bounded-above projective complexes
`P n` over `A ⧸ I ^ (n + 1)` with a common bound, projections `Q (P n) ≅ Kq n`, and chain maps
`P (n + 1) → P n` whose degreewise base changes are isomorphisms and which localize to `t n`. -/
public theorem exists_coherent_projectiveTower
    {A : Type u} [CommRing A] (I : Ideal A)
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (hbounded : DerivedCategory.TStructure.t.minus (Kq 0))
    (t : ∀ n : ℕ, Kq (n + 1) ⟶
      (ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapDerivedCategory.obj (Kq n))
    (hcompat : ∀ n : ℕ,
      IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, v, u}
        (quotientTransition I n) (t n))) :
    ∃ b : ℤ, ∃ P : ∀ n : ℕ, CochainComplex (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))) ℤ,
      (∀ n, (P n).IsStrictlyLE b) ∧
      (∀ n i, Module.Projective (A ⧸ I ^ (n + 1)) ((P n).X i)) ∧
      ∃ eP : ∀ n : ℕ, DerivedCategory.Q.obj (P n) ≅ Kq n,
      ∃ g : ∀ n : ℕ, P (n + 1) ⟶
        ((ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapHomologicalComplex
          (.up ℤ)).obj (P n),
        (∀ n, IsIso (((StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction
          (ModuleCat.extendRestrictScalarsAdj.{max u v} (quotientTransition I n)) (.up ℤ)).homEquiv
            _ _).symm (g n))) ∧
        ∀ n, DerivedCategory.Q.map (g n) ≫
            (ModuleCat.restrictScalars.{max u v}
              (quotientTransition I n)).mapDerivedCategoryFactors.inv.app
              (P n) ≫
            (ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapDerivedCategory.map
              (eP n).hom =
          (eP (n + 1)).hom ≫ t n := by
  obtain ⟨b, ⟨model⟩⟩ := exists_projectiveModel_zero.{u, v} I Kq hbounded
  let M := projectiveTower I Kq t hcompat model
  let S := projectiveTowerStep I Kq t hcompat model
  exact ⟨b, fun n => (M n).complex, fun n => (M n).isStrictlyLE, fun n => (M n).projective,
    fun n => (M n).iso, fun n => (S n).chainMap, fun n => (S n).isIso_adjoint,
    fun n => (S n).comm⟩

end Stacks.DerivedLimit.AdicSystem
end

end AdicSystemTowerData

section AdicSystemDerivedLimit

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated
open scoped ZeroObject

namespace Stacks.DerivedLimit.AdicSystem

universe u v

attribute [local instance] HasDerivedCategory.standard

section Completeness

variable {A : Type u} [CommRing A]

open StacksDraft.DerivedInverseLimit (shiftSubMul shiftSubMul_naturality shiftSubMul_isIso_pi
  shiftSubMul_isIso_of_pow_smul_id_eq_zero oneSubSmulShift_eq_shiftSubMul)

private theorem isDerivedComplete_of_milnorTriangle
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A))]
    (I : Ideal A) (D : ℕ → DerivedCategory (ModuleCat.{max u v} A))
    (t : ∀ n, D (n + 1) ⟶ D n) (K : DerivedCategory (ModuleCat.{max u v} A))
    (p : K ⟶ ∏ᶜ D) (δ : ∏ᶜ D ⟶ K⟦(1 : ℤ)⟧)
    (hTriangle : Triangle.mk p
      (Pi.lift fun n : ℕ ↦ Pi.π D n - Pi.π D (n + 1) ≫ t n) δ ∈
        distTriang (DerivedCategory (ModuleCat.{max u v} A)))
    (hzero : ∀ f ∈ I, ∀ n : ℕ, ∃ e : ℕ, f ^ e • 𝟙 (D n) = 0) :
    _root_.IsDerivedComplete I K := by
  intro f hf
  have hterm : ∀ n, IsIso (shiftSubMul (D n) f) := fun n ↦
    let ⟨e, he⟩ := hzero f hf n
    shiftSubMul_isIso_of_pow_smul_id_eq_zero (D n) f e he
  have hprod : IsIso (shiftSubMul (∏ᶜ D) f) := shiftSubMul_isIso_pi D f hterm
  let MT := Triangle.mk p (Pi.lift fun n : ℕ ↦
    Pi.π D n - Pi.π D (n + 1) ≫ t n) δ
  let Tfam : ℕ → Triangle (DerivedCategory (ModuleCat.{max u v} A)) := fun _ => MT
  have hPTdist := productTriangle_distinguished Tfam (fun _ => hTriangle)
  let ψ : productTriangle Tfam ⟶ productTriangle Tfam :=
    Triangle.homMk _ _ (shiftSubMul K f) (shiftSubMul (∏ᶜ D) f)
      (shiftSubMul (∏ᶜ D) f)
      (by rw [productTriangle_mor₁]; exact (shiftSubMul_naturality K _ f p).symm)
      (by rw [productTriangle_mor₂]; exact (shiftSubMul_naturality _ _ f _).symm)
      (by
        rw [productTriangle_mor₃]
        show (Limits.Pi.map (fun _ : ℕ => δ) ≫
            inv (piComparison (shiftFunctor _ (1 : ℤ)) (fun _ : ℕ => K))) ≫
              (shiftFunctor _ (1 : ℤ)).map (shiftSubMul K f) =
          shiftSubMul (∏ᶜ D) f ≫
            (Limits.Pi.map (fun _ : ℕ => δ) ≫
              inv (piComparison (shiftFunctor _ (1 : ℤ)) (fun _ : ℕ => K)))
        let pc := piComparison (shiftFunctor
          (DerivedCategory (ModuleCat.{max u v} A)) (1 : ℤ)) (fun _ : ℕ => K)
        have hnatδ := shiftSubMul_naturality (∏ᶜ D)
          ((shiftFunctor _ (1 : ℤ)).obj K) f δ
        have hshift : pc ≫ shiftSubMul ((shiftFunctor _ (1 : ℤ)).obj K) f =
            (shiftFunctor _ (1 : ℤ)).map (shiftSubMul K f) ≫ pc := by
          apply Pi.hom_ext
          intro m
          rw [Category.assoc, shiftSubMul, Pi.lift_comp_π, Preadditive.comp_sub,
            Linear.comp_smul, piComparison_comp_π, piComparison_comp_π,
            Category.assoc, piComparison_comp_π, shiftSubMul, ← Functor.map_comp,
            Pi.lift_comp_π, Functor.map_sub, Functor.Linear.map_smul]
        have hshift' : shiftSubMul ((shiftFunctor _ (1 : ℤ)).obj K) f ≫ inv pc =
            inv pc ≫ (shiftFunctor _ (1 : ℤ)).map (shiftSubMul K f) := by
          rw [IsIso.comp_inv_eq, Category.assoc, IsIso.eq_inv_comp]
          exact hshift
        rw [Category.assoc, ← hshift', ← Category.assoc, ← hnatδ, Category.assoc])
  have hK : IsIso ψ.hom₁ := isIso₁_of_isIso₂₃ ψ hPTdist hPTdist hprod hprod
  have hm : IsIso (shiftSubMul K f) := hK
  rw [isDerivedCompleteAt_iff_isIso, oneSubSmulShift_eq_shiftSubMul]
  exact hm
open scoped ModuleCat.Algebra in
/-- Every element of `I` acts nilpotently on the restriction of an object over `A ⧸ I ^ (n + 1)`.
-/
private theorem pow_smul_id_restrictScalars_eq_zero (I : Ideal A) (n : ℕ)
    (L : DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1)))) (f : A) (hf : f ∈ I) :
    f ^ (n + 1) • 𝟙 ((ModuleCat.restrictScalars.{max u v}
      (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory.obj L) = 0 := by
  let qn : A →+* A ⧸ I ^ (n + 1) := Ideal.Quotient.mk (I ^ (n + 1))
  let _ : Algebra A (A ⧸ I ^ (n + 1)) := qn.toAlgebra
  let F := (ModuleCat.restrictScalars.{max u v} qn).mapDerivedCategory
  have hF : F.Linear A := by
    show (ModuleCat.restrictScalars.{max u v} (Algebra.ofId A (A ⧸ I ^ (n + 1))).toRingHom)
      |>.mapDerivedCategory.Linear A
    infer_instance
  show f ^ (n + 1) • 𝟙 (F.obj L) = 0
  rw [← F.map_id, ← Functor.Linear.map_smul]
  have hq : algebraMap A (A ⧸ I ^ (n + 1)) (f ^ (n + 1)) = 0 :=
    Ideal.Quotient.eq_zero_iff_mem.mpr (Ideal.pow_mem_pow hf (n + 1))
  have hs : f ^ (n + 1) • 𝟙 L = 0 := by
    show algebraMap A (A ⧸ I ^ (n + 1)) (f ^ (n + 1)) • 𝟙 L = 0
    rw [hq, zero_smul]
  rw [hs, F.map_zero]

/-- A derived limit of a system restricted from the quotients `A ⧸ I ^ (n + 1)` is derived
`I`-complete. -/
private theorem isDerivedComplete_of_restricted_system
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A))] (I : Ideal A)
    (F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (e : ∀ n : ℕ, F.obj (.op n) ≅
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory.obj
        (Kq n))
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (p : K ⟶ ∏ᶜ fun n : ℕ => F.obj (.op n))
    (δ : (∏ᶜ fun n : ℕ => F.obj (.op n)) ⟶ K⟦(1 : ℤ)⟧)
    (hK : Triangle.mk p
      (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => F.obj (.op n)) n -
        Pi.π (fun n : ℕ => F.obj (.op n)) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (ModuleCat.{max u v} A))) :
    _root_.IsDerivedComplete I K := by
  refine isDerivedComplete_of_milnorTriangle I (fun n => F.obj (.op n))
    (fun n => F.map (homOfLE (Nat.le_succ n)).op) K p δ hK fun f hf n => ⟨n + 1, ?_⟩
  calc f ^ (n + 1) • 𝟙 (F.obj (.op n))
      = (e n).hom ≫ (f ^ (n + 1) • 𝟙 _) ≫ (e n).inv := by
        simp [Linear.comp_smul, Linear.smul_comp]
    _ = 0 := by
      rw [pow_smul_id_restrictScalars_eq_zero.{u, v} I n (Kq n) f hf]
      simp

end Completeness

section Tower

attribute [local instance] StacksDraft.DerivedInverseLimit.extendScalarsGeneral_additive

open StacksDraft.DerivedInverseLimit (restrictScalars_transition_compatibility)

/-- The unit of extension of scalars along a surjection is surjective. -/
private theorem surjective_extendRestrictScalarsAdj_unit {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) (X : ModuleCat.{max u v} R) :
    Function.Surjective ((ModuleCat.extendRestrictScalarsAdj.{max u v} f).unit.app X) := by
  intro y
  let _ := f.toAlgebra
  change TensorProduct R S X at y
  induction y using TensorProduct.induction_on with
  | zero => exact ⟨0, map_zero _⟩
  | tmul s x =>
    obtain ⟨r, rfl⟩ := hf s
    refine ⟨r • x, ?_⟩
    rw [ModuleCat.extendRestrictScalarsAdj_unit_app_apply]
    show (1 : S) ⊗ₜ[R] (r • x) = f r ⊗ₜ[R] x
    rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul', Algebra.smul_def, mul_one]
    rfl
  | add y z hy hz =>
    obtain ⟨a, rfl⟩ := hy
    obtain ⟨b, rfl⟩ := hz
    exact ⟨a + b, map_add _ _ _⟩

/-- A chain map into a restriction whose adjoint is invertible is degreewise surjective. -/
private theorem surjective_f_of_isIso_adjoint {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f)
    {P : CochainComplex (ModuleCat.{max u v} R) ℤ} {E : CochainComplex (ModuleCat.{max u v} S) ℤ}
    (g : P ⟶ ((ModuleCat.restrictScalars.{max u v} f).mapHomologicalComplex (.up ℤ)).obj E)
    (hg : IsIso (((StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{max u v} f) (.up ℤ)).homEquiv _ _).symm g)) (i : ℤ) :
    Function.Surjective (g.f i) := by
  let adj := StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{max u v} f) (.up ℤ)
  let a := (adj.homEquiv _ _).symm g
  have hga : g = adj.unit.app P ≫
      ((ModuleCat.restrictScalars.{max u v} f).mapHomologicalComplex (.up ℤ)).map a := by
    simpa only [a, Equiv.apply_symm_apply] using Adjunction.homEquiv_unit adj P E a
  have hai : IsIso (a.f i) := by
    have : IsIso a := hg
    infer_instance
  rw [hga]
  show Function.Surjective ((ModuleCat.restrictScalars.{max u v} f).map (a.f i) ∘
    (ModuleCat.extendRestrictScalarsAdj.{max u v} f).unit.app (P.X i))
  refine Function.Surjective.comp ?_ (surjective_extendRestrictScalarsAdj_unit f hf _)
  exact ((ConcreteCategory.isIso_iff_bijective _).mp
    (inferInstanceAs (IsIso ((ModuleCat.restrictScalars.{max u v} f).map (a.f i))))).2

private abbrev restrictedProjectiveTower
    {A : Type u} [CommRing A] (I : Ideal A)
    (P : ∀ n : ℕ, CochainComplex (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))) ℤ)
    (g : ∀ n, P (n + 1) ⟶
      ((ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapHomologicalComplex
        (.up ℤ)).obj (P n)) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{max u v} A) ℤ :=
  Functor.ofOpSequence fun n =>
    ((ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (I ^ (n + 2)))).mapHomologicalComplex
      (.up ℤ)).map (g n) ≫
        (StacksDraft.DerivedInverseLimit.restrictScalarsComplexComp.{u, v}
          (Ideal.Quotient.mk (I ^ (n + 2)))
          (quotientTransition I n) (Ideal.Quotient.mk (I ^ (n + 1)))
          (Ideal.Quotient.factor_comp_mk _).symm).hom.app (P n)

private lemma restrictedProjectiveTower_surjective
    {A : Type u} [CommRing A] (I : Ideal A)
    (P : ∀ n : ℕ, CochainComplex (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))) ℤ)
    (g : ∀ n, P (n + 1) ⟶
      ((ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapHomologicalComplex
        (.up ℤ)).obj (P n))
    (hg : ∀ n, IsIso (((StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{max u v} (quotientTransition I n))
        (.up ℤ)).homEquiv _ _).symm (g n))) (n : ℕ) (i : ℤ) :
    Function.Surjective (((restrictedProjectiveTower.{u, v} I P g).map
      (homOfLE (Nat.le_succ n)).op).f i) := by
  rw [show (restrictedProjectiveTower.{u, v} I P g).map (homOfLE (Nat.le_succ n)).op = _ from
    Functor.ofOpSequence_map_homOfLE_succ _ n]
  show Function.Surjective ((g n).f i)
  exact surjective_f_of_isIso_adjoint (quotientTransition I n)
    (quotientTransition_surjective I n) (g n) (hg n) i

set_option backward.isDefEq.respectTransparency false in
private lemma exists_restrictedProjectiveTower_iso
    {A : Type u} [CommRing A] (I : Ideal A)
    (F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (e : ∀ n : ℕ, F.obj (.op n) ≅
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory.obj
        (Kq n))
    (t : ∀ n : ℕ, Kq (n + 1) ⟶
      (ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapDerivedCategory.obj (Kq n))
    (htransition : ∀ n : ℕ,
      F.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
        (e (n + 1)).hom ≫
          (ModuleCat.restrictScalars.{max u v}
            (Ideal.Quotient.mk (I ^ (n + 2)))).mapDerivedCategory.map
            (t n) ≫ (restrictScalarsTransitionIso I n).hom.app (Kq n))
    (P : ∀ n : ℕ, CochainComplex (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))) ℤ)
    (eP : ∀ n, DerivedCategory.Q.obj (P n) ≅ Kq n)
    (g : ∀ n, P (n + 1) ⟶
      ((ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapHomologicalComplex
        (.up ℤ)).obj (P n))
    (hcomm : ∀ n, DerivedCategory.Q.map (g n) ≫
      (ModuleCat.restrictScalars.{max u v}
        (quotientTransition I n)).mapDerivedCategoryFactors.inv.app
        (P n) ≫ (ModuleCat.restrictScalars.{max u v}
          (quotientTransition I n)).mapDerivedCategory.map
          (eP n).hom = (eP (n + 1)).hom ≫ t n) :
    ∃ eM : ∀ n, DerivedCategory.Q.obj
        ((restrictedProjectiveTower.{u, v} I P g).obj (.op n)) ≅ F.obj (.op n),
      (∀ n, (eM n).hom ≫ (e n).hom =
        (ModuleCat.restrictScalars.{max u v}
          (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategoryFactors.inv.app
          (P n) ≫ (ModuleCat.restrictScalars.{max u v}
            (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory.map
            (eP n).hom) ∧
      ∀ n, DerivedCategory.Q.map ((restrictedProjectiveTower.{u, v} I P g).map
        (homOfLE (Nat.le_succ n)).op) ≫ (eM n).hom =
          (eM (n + 1)).hom ≫ F.map (homOfLE (Nat.le_succ n)).op := by
  let eM (n : ℕ) : DerivedCategory.Q.obj
      ((restrictedProjectiveTower.{u, v} I P g).obj (.op n)) ≅ F.obj (.op n) :=
    ((ModuleCat.restrictScalars.{max u v}
      (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategoryFactors.app
      (P n)).symm ≪≫
      (ModuleCat.restrictScalars.{max u v}
        (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory.mapIso
        (eP n) ≪≫ (e n).symm
  refine ⟨eM, fun n => by simp [eM], fun n => ?_⟩
  apply (cancel_mono (e n).hom).mp
  simp only [Category.assoc, htransition]
  simp only [eM, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_hom, Category.assoc,
    Iso.inv_hom_id_assoc, Iso.inv_hom_id, Category.comp_id]
  rw [show (restrictedProjectiveTower.{u, v} I P g).map (homOfLE (Nat.le_succ n)).op = _ from
    Functor.ofOpSequence_map_homOfLE_succ _ n]
  simpa only [Category.assoc, Iso.app_inv] using
    restrictScalars_transition_compatibility (Ideal.Quotient.mk (I ^ (n + 2)))
    (quotientTransition I n) (Ideal.Quotient.mk (I ^ (n + 1)))
    (Ideal.Quotient.factor_comp_mk _).symm (P (n + 1)) (P n) (g n)
    (eP (n + 1)) (eP n) (t n) (hcomm n)

end Tower

section FlatTranspose

attribute [local instance] StacksDraft.DerivedInverseLimit.extendScalarsGeneral_additive

private lemma isIso_transpose_iff
    {C D : Type*} [Category C] [Category D] {L₁ L₂ : C ⥤ D} {R : D ⥤ C}
    (a₁ : L₁ ⊣ R) (a₂ : L₂ ⊣ R) {X : C} {Y : D} (f : X ⟶ R.obj Y) :
    IsIso ((a₁.homEquiv X Y).symm f) ↔ IsIso ((a₂.homEquiv X Y).symm f) := by
  have h : (a₁.homEquiv X Y).symm f =
      (a₁.leftAdjointUniq a₂).hom.app X ≫ (a₂.homEquiv X Y).symm f := by
    apply (a₁.homEquiv X Y).injective
    rw [Equiv.apply_symm_apply, Adjunction.homEquiv_naturality_right,
      Adjunction.homEquiv_leftAdjointUniq_hom_app]
    exact ((a₂.homEquiv X Y).apply_symm_apply f).symm.trans
      (Adjunction.homEquiv_unit a₂ X Y ((a₂.homEquiv X Y).symm f))
  rw [h, isIso_comp_left_iff]

set_option backward.isDefEq.respectTransparency false in
private lemma isIso_derived_transpose_of_kFlat {R S : Type u}
    [CommRing R] [CommRing S] (f : R →+* S)
    (P : CochainComplex (ModuleCat.{max u v} R) ℤ) (hP : CochainComplex.KFlat P)
    (E : CochainComplex (ModuleCat.{max u v} S) ℤ)
    (g : P ⟶ ((ModuleCat.restrictScalars.{max u v} f).mapHomologicalComplex (.up ℤ)).obj E)
    (hg : IsIso (((StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{max u v} f) (.up ℤ)).homEquiv _ _).symm g))
    (adj : (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
      f).functor ⊣
      (ModuleCat.restrictScalars.{max u v} f).mapDerivedCategory) :
    IsIso ((adj.homEquiv _ _).symm (DerivedCategory.Q.map g ≫
      (ModuleCat.restrictScalars.{max u v} f).mapDerivedCategoryFactors.inv.app E)) := by
  let D := CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v} f
  let S₀ := ModuleCat.restrictScalars.{max u v} f
  let β := S₀.mapDerivedCategoryFactors.inv
  let α := D.comparison
  let W_R := HomologicalComplex.quasiIso (ModuleCat.{max u v} R) (.up ℤ)
  let W_S := HomologicalComplex.quasiIso (ModuleCat.{max u v} S) (.up ℤ)
  have : D.functor.IsLeftDerivedFunctor α W_R := D.isLeftDerived
  let adjC := StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction
    (ModuleCat.extendRestrictScalarsAdj.{max u v} f) (.up ℤ)
  have : S₀.mapDerivedCategory.IsRightDerivedFunctor β W_S :=
    Functor.isRightDerivedFunctor_of_inverts W_S _ S₀.mapDerivedCategoryFactors
  have : (S₀.mapDerivedCategory ⋙ D.functor).IsRightDerivedFunctor
      (Functor.whiskerRight β D.functor ≫ (Functor.associator _ _ _).hom) W_S :=
    Functor.isRightDerivedFunctor_of_inverts W_S _
      ((Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight S₀.mapDerivedCategoryFactors D.functor)
  have : (D.functor ⋙ S₀.mapDerivedCategory).IsLeftDerivedFunctor
      ((Functor.associator _ _ _).inv ≫ Functor.whiskerRight α S₀.mapDerivedCategory) W_R :=
    CochainComplex.DerivedTensor.KFlatDerived.isLeftDerivedFunctor_extension_postcomp.{u, u, v}
      f D.functor α S₀.mapDerivedCategory
  let adjD := adjC.derived W_R W_S α β
  apply (isIso_transpose_iff adj adjD _).mpr
  have htranspose : (adjD.homEquiv _ _).symm (DerivedCategory.Q.map g ≫ β.app E) =
      α.app P ≫ DerivedCategory.Q.map ((adjC.homEquiv _ _).symm g) := by
    rw [Adjunction.homEquiv_counit, Functor.map_comp, Category.assoc]
    show D.functor.map (DerivedCategory.Q.map g) ≫
      (D.functor.map (β.app E) ≫ (adjC.derivedε W_S α β).app (DerivedCategory.Q.obj E)) = _
    have hnat := α.naturality g
    simp only [Functor.comp_map] at hnat
    rw [Adjunction.derivedε_fac_app, ← Category.assoc, hnat, Category.assoc,
      Adjunction.homEquiv_counit, Functor.map_comp]
    rfl
  rw [htranspose]
  have : IsIso (α.app P) := D.comparison_isIso_of_kFlat P hP
  have : IsIso ((adjC.homEquiv _ _).symm g) := hg
  infer_instance

end FlatTranspose


section AdicTransport
open Opposite
set_option backward.isDefEq.respectTransparency false
private abbrev scalarLift (A : Type u) [CommRing A] :
    ModuleCat.{max u v} A ⥤ ModuleCat.{max u v} (ULift.{v} A) :=
  ModuleCat.restrictScalars.{max u v} (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom

private def quotientScalarLiftEquiv {A : Type u} [CommRing A] (I : Ideal A) (n : ℕ) :
    ULift.{v} A ⧸ (I.comap (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom) ^ n ≃+*
      A ⧸ I ^ n :=
  Ideal.quotientEquiv _ _ ULift.ringEquiv (by
    rw [Ideal.map_pow]
    change I ^ n = (Ideal.map ULift.ringEquiv.toRingHom
      (I.comap ULift.ringEquiv.toRingHom)) ^ n
    rw [Ideal.map_comap_of_surjective (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom
      (show Function.Surjective (ULift.ringEquiv : ULift.{v} A ≃+* A).toRingHom from
        ULift.ringEquiv.surjective)])

private lemma finite_scalarLift {A : Type u} [CommRing A]
    (Q : ModuleCat.{max u v} A) [Module.Finite A Q] :
    Module.Finite (ULift.{v} A) ((scalarLift A).obj Q) := by
  let := ULift.algebra' (R := A)
  have : Module.Finite (ULift.{v} A) A :=
    Module.Finite.of_surjective (Algebra.linearMap (ULift.{v} A) A)
      ULift.ringEquiv.surjective
  have : IsScalarTower (ULift.{v} A) A Q := ⟨fun r a q => (smul_smul r.down a q).symm⟩
  exact Module.Finite.trans A Q

private def quotientTensorScalarLiftIso {A : Type u} [CommRing A] (I : Ideal A) :
    scalarLift A ⋙ (MonoidalCategory.tensoringLeft (ModuleCat.{max u v} (ULift.{v} A))).obj
      (ModuleCat.of (ULift.{v} A) (ULift.{v} (A ⧸ I))) ≅
    (ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk I)) ⋙
      ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk I) ⋙ scalarLift A :=
  NatIso.ofComponents (fun M =>
    ((TensorProduct.congr (ULift.moduleEquiv : ULift.{v} (A ⧸ I) ≃ₗ[ULift.{v} A] (A ⧸ I))
      (LinearEquiv.refl (ULift.{v} A) M)) ≪≫ₗ
      TensorProduct.equivOfCompatibleSMul A (ULift.{v} A) (ULift.{v} A) (A ⧸ I) M).toModuleIso)
    (by
      intro M N f
      apply ModuleCat.hom_ext
      apply TensorProduct.ext
      ext x y
      rfl)
private lemma quotientScalarLiftEquiv_mk {A : Type u} [CommRing A]
    (I : Ideal A) (n : ℕ) (r : ULift.{v} A) :
    quotientScalarLiftEquiv I n (Ideal.Quotient.mk _ r) =
      Ideal.Quotient.mk (I ^ n) r.down :=
  Ideal.quotientEquiv_mk _ _ _ _ r

private lemma flat_limit_and_preservesLimit_quotient
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ℕᵒᵖ ⥤ ModuleCat.{max u v} A)
    (quotientModule : ∀ n : ℕ, Module (A ⧸ I ^ n) (M.obj (.op n)))
    (hscalar : ∀ n : ℕ, letI := quotientModule n
      IsScalarTower A (A ⧸ I ^ n) (M.obj (.op n)))
    (hflat : ∀ n : ℕ, letI := quotientModule n
      Module.Flat (A ⧸ I ^ n) (M.obj (.op n)))
    (hsurjective : ∀ n : ℕ, Function.Surjective
      (M.map (homOfLE (Nat.le_succ n)).op)) :
    Module.Flat A (limit M : ModuleCat.{max u v} A) ∧
      ∀ J : Ideal A, PreservesLimit M
        (ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk J)) := by
  let B := ULift.{v} A
  let E := scalarLift.{u, v} A
  let I' : Ideal B := I.comap (ULift.ringEquiv : B ≃+* A).toRingHom
  have : IsNoetherianRing B := isNoetherianRing_of_ringEquiv A ULift.ringEquiv.symm
  let qm (n : ℕ) : Module (B ⧸ I' ^ n) (M.obj (.op n)) := by
    let := quotientModule n
    exact Module.compHom _ (quotientScalarLiftEquiv.{u, v} I n).toRingHom
  have hs (n : ℕ) : let := qm n
      IsScalarTower B (B ⧸ I' ^ n) (M.obj (.op n)) := by
    let := quotientModule n
    let := hscalar n
    let := qm n
    constructor
    intro r s m
    show (quotientScalarLiftEquiv I n (Ideal.Quotient.mk _ r * s)) • m =
      r.down • ((quotientScalarLiftEquiv I n s) • m)
    rw [map_mul, quotientScalarLiftEquiv_mk, mul_smul]
    exact IsScalarTower.algebraMap_smul (A ⧸ I ^ n) r.down
      ((quotientScalarLiftEquiv I n s) • m)
  have hf (n : ℕ) : let := qm n
      Module.Flat (B ⧸ I' ^ n) (M.obj (.op n)) := by
    let := quotientModule n
    let := qm n
    let e := quotientScalarLiftEquiv.{u, v} I n
    let := e.toRingHom.toAlgebra
    have : Module.Flat (B ⧸ I' ^ n) (A ⧸ I ^ n) := RingHom.Flat.of_bijective e.bijective
    have : IsScalarTower (B ⧸ I' ^ n) (A ⧸ I ^ n) (M.obj (.op n)) :=
      ⟨fun r s m => mul_smul (e r) s m⟩
    have := hflat n
    exact Module.Flat.trans _ (A ⧸ I ^ n) _
  obtain ⟨hfM, hT⟩ := _root_.flat_limit_and_tensor_limit_of_flat_quotients I'
    (M ⋙ E) qm hs hf hsurjective
  constructor
  · have := hfM
    have h : Module.Flat B (E.obj (limit M)) :=
      Module.Flat.of_linearEquiv (preservesLimitIso E M).toLinearEquiv
    exact Module.Flat.ulift_left_iff.mp h
  · intro J
    let Q := ModuleCat.of B (ULift.{v} (A ⧸ J))
    have hQ : Module.Finite B Q :=
      finite_scalarLift (ModuleCat.of A (ULift.{v} (A ⧸ J)))
    let T := (MonoidalCategory.tensoringLeft (ModuleCat.{max u v} B)).obj Q
    have : IsIso (limit.post (M ⋙ E) T) := hT Q hQ
    have : PreservesLimit (M ⋙ E) T := preservesLimit_of_isIso_post T (M ⋙ E)
    have : PreservesLimit M (E ⋙ T) := inferInstance
    have : PreservesLimit M ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk J)) ⋙
        ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk J) ⋙ E) :=
      preservesLimit_of_natIso M (quotientTensorScalarLiftIso.{u, v} J)
    have : ReflectsLimit (M ⋙ ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk J))
        (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk J) ⋙ E) :=
      reflectsLimit_of_reflectsIsomorphisms _ _
    exact preservesLimit_of_reflects_of_preserves _
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk J) ⋙ E)

private abbrev prependZeroTower {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    (M : ℕᵒᵖ ⥤ C) : ℕᵒᵖ ⥤ C :=
  Functor.ofOpSequence (X := fun n => match n with | 0 => 0 | n + 1 => M.obj (op n))
    (fun n => match n with | 0 => 0 | n + 1 => M.map (homOfLE (Nat.le_succ n)).op)

private def prependZeroCone {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {M : ℕᵒᵖ ⥤ C} (s : Cone M) : Cone (prependZeroTower M) where
  pt := s.pt
  π := NatTrans.ofOpSequence
    (fun n => match n with | 0 => 0 | n + 1 => s.π.app (op n))
    (fun n => by
      cases n with
      | zero => simp [prependZeroTower, Functor.ofOpSequence_map_homOfLE_succ]
      | succ n => simp [prependZeroTower, Functor.ofOpSequence_map_homOfLE_succ])

private def tailCone {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {M : ℕᵒᵖ ⥤ C} (s : Cone (prependZeroTower M)) : Cone M where
  pt := s.pt
  π := NatTrans.ofOpSequence (fun n => s.π.app (op (n + 1)))
    (fun n => by
      simpa [prependZeroTower, Functor.ofOpSequence_map_homOfLE_succ] using
        (s.w (homOfLE (Nat.le_succ (n + 1))).op).symm)

private def prependZeroConeIsLimit {C : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C]
    {M : ℕᵒᵖ ⥤ C} (s : Cone M) (hs : IsLimit s) : IsLimit (prependZeroCone s) where
  lift t := hs.lift (tailCone t)
  fac t n := by
    rcases n with ⟨n⟩
    cases n with
    | zero => exact (isZero_zero C).eq_of_tgt _ _
    | succ n => exact hs.fac (tailCone t) (op n)
  uniq t m hm := hs.hom_ext fun n => (hm (op (n.unop + 1))).trans (hs.fac (tailCone t) n).symm

private lemma preservesLimit_of_prependZeroTower
    {C D : Type*} [Category C] [HasZeroMorphisms C] [HasZeroObject C] [Category D]
    (M : ℕᵒᵖ ⥤ C) (H : C ⥤ D) [PreservesLimit (prependZeroTower M) H] :
    PreservesLimit M H := by
  let S : ℕ ⥤ ℕ := (show Monotone Nat.succ from fun _ _ h => Nat.succ_le_succ h).functor
  have : S.Final := (Monotone.final_functor_iff _).mpr fun n => ⟨n, Nat.le_succ n⟩
  have : PreservesLimit (S.op ⋙ prependZeroTower M) H := inferInstance
  let f : M ⟶ S.op ⋙ prependZeroTower M :=
    NatTrans.ofOpSequence (fun _ => 𝟙 _) (fun n => by
      show M.map (homOfLE (Nat.le_succ n)).op ≫ 𝟙 _ =
        𝟙 _ ≫ (prependZeroTower M).map (homOfLE (Nat.le_succ (n + 1))).op
      simp [prependZeroTower, Functor.ofOpSequence_map_homOfLE_succ])
  have : ∀ n, IsIso (f.app n) := fun _ => inferInstanceAs (IsIso (𝟙 _))
  have : IsIso f := NatIso.isIso_of_isIso_app f
  exact preservesLimit_of_iso_diagram H (asIso f).symm

private lemma flat_limit_and_preservesLimit_quotient_positive
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (M : ℕᵒᵖ ⥤ ModuleCat.{max u v} A)
    (quotientModule : ∀ n : ℕ, Module (A ⧸ I ^ (n + 1)) (M.obj (.op n)))
    (hscalar : ∀ n : ℕ, letI := quotientModule n
      IsScalarTower A (A ⧸ I ^ (n + 1)) (M.obj (.op n)))
    (hflat : ∀ n : ℕ, letI := quotientModule n
      Module.Flat (A ⧸ I ^ (n + 1)) (M.obj (.op n)))
    (hsurjective : ∀ n : ℕ, Function.Surjective
      (M.map (homOfLE (Nat.le_succ n)).op)) :
    Module.Flat A (limit M : ModuleCat.{max u v} A) ∧
      ∀ J : Ideal A, PreservesLimit M
        (ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk J)) := by
  let N := prependZeroTower M
  have hzero : Subsingleton (N.obj (op 0)) := ModuleCat.subsingleton_of_isZero (isZero_zero _)
  let qm₀ : Module (A ⧸ I ^ 0) (N.obj (op 0)) :=
    { smul := fun _ _ => 0
      one_smul := fun _ => Subsingleton.elim _ _
      mul_smul := fun _ _ _ => Subsingleton.elim _ _
      smul_zero := fun _ => Subsingleton.elim _ _
      smul_add := fun _ _ _ => Subsingleton.elim _ _
      add_smul := fun _ _ _ => Subsingleton.elim _ _
      zero_smul := fun _ => Subsingleton.elim _ _ }
  let qm : ∀ n : ℕ, Module (A ⧸ I ^ n) (N.obj (op n))
    | 0 => qm₀
    | n + 1 => quotientModule n
  have hs : ∀ n : ℕ, let := qm n
      IsScalarTower A (A ⧸ I ^ n) (N.obj (op n)) := by
    intro n
    cases n with
    | zero => exact ⟨fun _ _ _ => Subsingleton.elim _ _⟩
    | succ n => exact hscalar n
  have hf : ∀ n : ℕ, let := qm n
      Module.Flat (A ⧸ I ^ n) (N.obj (op n)) := by
    intro n
    cases n with
    | zero =>
      let := qm 0
      infer_instance
    | succ n => exact hflat n
  have hn : ∀ n, Function.Surjective (N.map (homOfLE (Nat.le_succ n)).op) := by
    intro n
    cases n with
    | zero => intro x; exact ⟨0, Subsingleton.elim _ _⟩
    | succ n =>
      show Function.Surjective ((prependZeroTower M).map
        (homOfLE (Nat.le_succ (n + 1))).op)
      rw [show (prependZeroTower M).map (homOfLE (Nat.le_succ (n + 1))).op =
        M.map (homOfLE (Nat.le_succ n)).op from Functor.ofOpSequence_map_homOfLE_succ _ (n + 1)]
      exact hsurjective n
  obtain ⟨hN, hNJ⟩ := flat_limit_and_preservesLimit_quotient I N qm hs hf hn
  have := hN
  let e : limit M ≅ limit N :=
    (prependZeroConeIsLimit (limit.cone M) (limit.isLimit M)).conePointUniqueUpToIso
      (limit.isLimit N)
  refine ⟨Module.Flat.of_linearEquiv e.toLinearEquiv, fun J => ?_⟩
  have := hNJ J
  exact preservesLimit_of_prependZeroTower M _

end AdicTransport

section Assembly
attribute [local instance] StacksDraft.DerivedInverseLimit.extendScalarsGeneral_additive
set_option backward.isDefEq.respectTransparency false in
private theorem bounded_complete_and_reductions_of_flat_models
    {A : Type u} [CommRing A] (I : Ideal A)
    (F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (e : ∀ n : ℕ, F.obj (.op n) ≅
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory.obj
        (Kq n))
    (adj : ∀ n : ℕ,
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
          (Ideal.Quotient.mk (I ^ (n + 1)))).functor ⊣
        (ModuleCat.restrictScalars.{max u v}
          (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory)
    (P : ∀ n : ℕ, CochainComplex (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))) ℤ)
    (g : ∀ n, P (n + 1) ⟶
      ((ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapHomologicalComplex
        (.up ℤ)).obj (P n))
    (b : ℤ) (hb : ∀ n, (P n).IsStrictlyLE b)
    (hsurj : ∀ n i, Function.Surjective (((restrictedProjectiveTower.{u, v} I P g).map
      (homOfLE (Nat.le_succ n)).op).f i))
    (hflat : ∀ i, Module.Flat A ((limit (restrictedProjectiveTower.{u, v} I P g)).X i))
    (hred : ∀ n, IsIso (((StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{max u v}
        (Ideal.Quotient.mk (I ^ (n + 1)))) (.up ℤ)).homEquiv _ _).symm
          (limit.π (restrictedProjectiveTower.{u, v} I P g) (.op n))))
    (eP : ∀ n, DerivedCategory.Q.obj (P n) ≅ Kq n)
    (eM : ∀ n, DerivedCategory.Q.obj
      ((restrictedProjectiveTower.{u, v} I P g).obj (.op n)) ≅ F.obj (.op n))
    (heM : ∀ n, (eM n).hom ≫ (e n).hom =
      (ModuleCat.restrictScalars.{max u v}
        (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategoryFactors.inv.app
        (P n) ≫ (ModuleCat.restrictScalars.{max u v}
          (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory.map
          (eP n).hom)
    (hnat : ∀ n, DerivedCategory.Q.map ((restrictedProjectiveTower.{u, v} I P g).map
      (homOfLE (Nat.le_succ n)).op) ≫ (eM n).hom =
        (eM (n + 1)).hom ≫ F.map (homOfLE (Nat.le_succ n)).op)
    [HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A))]
    (K : DerivedCategory (ModuleCat.{max u v} A))
    (p : K ⟶ ∏ᶜ fun n : ℕ => F.obj (.op n))
    (δ : (∏ᶜ fun n : ℕ => F.obj (.op n)) ⟶ K⟦(1 : ℤ)⟧)
    (hK : Triangle.mk p
      (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => F.obj (.op n)) n -
        Pi.π (fun n : ℕ => F.obj (.op n)) (n + 1) ≫
          F.map (homOfLE (Nat.le_succ n)).op) δ ∈
        distTriang (DerivedCategory (ModuleCat.{max u v} A))) :
    DerivedCategory.TStructure.t.minus K ∧
      _root_.IsDerivedComplete I K ∧
      ∀ n : ℕ, IsIso (((adj n).homEquiv _ _).symm
        (p ≫ Pi.π (fun n : ℕ => F.obj (.op n)) n ≫ (e n).hom)) := by
  let M := restrictedProjectiveTower.{u, v} I P g
  let q := Pi.lift fun n => DerivedCategory.Q.map (limit.π M (.op n)) ≫ (eM n).hom
  obtain ⟨δ', hδ'⟩ :=
    StacksDraft.DerivedInverseLimit.exists_distTriang_of_degreewise_surjective_of_iso M hsurj
      (fun n => F.obj (.op n)) (fun n => F.map (homOfLE (Nat.le_succ n)).op) eM hnat
  obtain ⟨eK, heK⟩ :=
    StacksDraft.DerivedInverseLimit.exists_iso_comp_eq_of_distinguished_mk p q _ δ δ' hK hδ'
  have hbound : (limit M).IsStrictlyLE b :=
    StacksDraft.DerivedInverseLimit.isStrictlyLE_limit M b (fun n => by
      have := hb n.unop
      show CochainComplex.IsStrictlyLE
        (((ModuleCat.restrictScalars.{max u v}
          (Ideal.Quotient.mk (I ^ (n.unop + 1)))).mapHomologicalComplex
          (.up ℤ)).obj (P n.unop)) b
      infer_instance)
  have : (DerivedCategory.Q.obj (limit M)).IsLE b :=
    (DerivedCategory.isLE_Q_obj_iff (limit M) b).mpr inferInstance
  have hKb : K.IsLE b := DerivedCategory.TStructure.t.isLE_of_iso eK.symm b
  refine ⟨⟨b, hKb⟩, isDerivedComplete_of_restricted_system I F Kq e K p δ hK, ?_⟩
  intro n
  have hf (i : ℤ) : Module.Flat A ((limit M).X i) := hflat i
  have hKF : CochainComplex.KFlat (limit M) := CochainComplex.KFlat.kFlat_of_flat (limit M) b
  have hi := isIso_derived_transpose_of_kFlat (Ideal.Quotient.mk (I ^ (n + 1)))
    (limit M) hKF (P n) (limit.π M (.op n)) (hred n) (adj n)
  have hprojection : p ≫ Pi.π (fun n => F.obj (.op n)) n ≫ (e n).hom =
      eK.hom ≫ DerivedCategory.Q.map (limit.π M (.op n)) ≫
        (ModuleCat.restrictScalars.{max u v}
          (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategoryFactors.inv.app
          (P n) ≫ (ModuleCat.restrictScalars.{max u v}
            (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory.map
            (eP n).hom := by
    rw [← heK]
    simp only [q, Category.assoc, Pi.lift_comp_π_assoc, heM]
  rw [hprojection, Adjunction.homEquiv_naturality_left_symm]
  have hred' : IsIso (((adj n).homEquiv _ _).symm
      (DerivedCategory.Q.map (limit.π M (.op n)) ≫
        (ModuleCat.restrictScalars.{max u v}
          (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategoryFactors.inv.app
          (P n) ≫ (ModuleCat.restrictScalars.{max u v}
            (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory.map
            (eP n).hom)) := by
    rw [← Category.assoc, Adjunction.homEquiv_naturality_right_symm]
    infer_instance
  infer_instance


end Assembly


section AdicReduction
open Opposite
set_option backward.isDefEq.respectTransparency false
attribute [local instance] StacksDraft.DerivedInverseLimit.extendScalarsGeneral_additive

private lemma full_restrictScalars_of_surjective {R S : Type u} [CommRing R] [CommRing S]
    (f : R →+* S) (hf : Function.Surjective f) :
    (ModuleCat.restrictScalars.{max u v} f).Full := by
  constructor
  intro X Y a
  let b : X →ₗ[S] Y :=
    { a.hom with
      map_smul' := fun s x => by
        obtain ⟨r, rfl⟩ := hf s
        exact a.hom.map_smul r x }
  exact ⟨ModuleCat.ofHom b, by ext x; rfl⟩

private def restrictExtendScalarsIso {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    (f : R →+* S) (hf : Function.Surjective f) (g : S →+* T) :
    ModuleCat.restrictScalars.{max u v} f ⋙ ModuleCat.extendScalars (g.comp f) ≅
      ModuleCat.extendScalars g := by
  have := full_restrictScalars_of_surjective.{u, v} f hf
  let adj := ModuleCat.extendRestrictScalarsAdj.{max u v} f
  exact Functor.isoWhiskerLeft (ModuleCat.restrictScalars.{max u v}
    f) (ModuleCat.extendScalarsComp f g) ≪≫
    (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight (asIso adj.counit) (ModuleCat.extendScalars g) ≪≫
    (ModuleCat.extendScalars g).leftUnitor

private lemma isIso_extendScalars_restrict_map_of_isIso_adjoint
    {R S T U : Type u} [CommRing R] [CommRing S] [CommRing T] [CommRing U]
    (f : R →+* S) (hf : Function.Surjective f)
    (g : S →+* T) (hg : Function.Surjective g) (h : T →+* U)
    {X : ModuleCat.{max u v} S} {Y : ModuleCat.{max u v} T}
    (a : X ⟶ (ModuleCat.restrictScalars.{max u v} g).obj Y)
    (ha : IsIso (((ModuleCat.extendRestrictScalarsAdj.{max u v} g).homEquiv _ _).symm a)) :
    IsIso ((ModuleCat.extendScalars ((h.comp g).comp f)).map
      ((ModuleCat.restrictScalars.{max u v} f).map a)) := by
  have := full_restrictScalars_of_surjective.{u, v} g hg
  let adj := ModuleCat.extendRestrictScalarsAdj.{max u v} g
  have : IsIso ((ModuleCat.extendScalars g).map a) := by
    change IsIso ((adj.homEquiv _ _).symm a) at ha
    rwa [Adjunction.homEquiv_counit, isIso_comp_right_iff] at ha
  have : IsIso ((ModuleCat.extendScalars (h.comp g)).map a) :=
    (NatIso.isIso_map_iff (ModuleCat.extendScalarsComp g h) a).mpr (by
      show IsIso ((ModuleCat.extendScalars h).map ((ModuleCat.extendScalars g).map a))
      infer_instance)
  exact (NatIso.isIso_map_iff (restrictExtendScalarsIso f hf (h.comp g)) a).mpr this

private lemma isEventuallyConstantTo_of_isIso_succ {C : Type*} [Category C]
    (F : ℕᵒᵖ ⥤ C) (n₀ : ℕ)
    (h : ∀ n, n₀ ≤ n → IsIso (F.map (homOfLE (Nat.le_succ n)).op)) :
    F.IsEventuallyConstantTo (op n₀) := by
  have hmap (m : ℕ) (hm : n₀ ≤ m) : IsIso (F.map (homOfLE hm).op) := by
    induction m, hm using Nat.le_induction with
    | base =>
      rw [show (homOfLE (le_refl n₀)).op = 𝟙 (op n₀) from Subsingleton.elim _ _, F.map_id]
      infer_instance
    | succ m hm ih =>
      have := ih
      have := h m hm
      rw [show (homOfLE (Nat.le_succ_of_le hm)).op =
        (homOfLE (Nat.le_succ m)).op ≫ (homOfLE hm).op from Subsingleton.elim _ _, F.map_comp]
      infer_instance
  intro m f
  convert hmap m.unop (leOfHom f.unop) using 1
  exact congrArg F.map (Subsingleton.elim _ _)

private lemma isIso_reduced_transition
    {A : Type u} [CommRing A] (I : Ideal A)
    (P : ∀ n : ℕ, CochainComplex (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))) ℤ)
    (g : ∀ n, P (n + 1) ⟶
      ((ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapHomologicalComplex
        (.up ℤ)).obj (P n))
    (hg : ∀ n, IsIso (((StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{max u v} (quotientTransition I n))
        (.up ℤ)).homEquiv _ _).symm (g n)))
    (t n : ℕ) (ht : t ≤ n) (i : ℤ) :
    IsIso ((ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk (I ^ (t + 1)))).map
      (((restrictedProjectiveTower.{u, v} I P g).map (homOfLE (Nat.le_succ n)).op).f i)) := by
  let f := Ideal.Quotient.mk (I ^ (n + 2))
  let h : (A ⧸ I ^ (n + 1)) →+* (A ⧸ I ^ (t + 1)) :=
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.add_le_add_right ht 1))
  have ha : IsIso (((ModuleCat.extendRestrictScalarsAdj.{max u v} (quotientTransition I n)).homEquiv
      _ _).symm ((g n).f i)) := by
    have := hg n
    exact inferInstanceAs (IsIso ((((StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{max u v} (quotientTransition I n))
        (.up ℤ)).homEquiv _ _).symm (g n)).f i))
  have hi := isIso_extendScalars_restrict_map_of_isIso_adjoint f
    (Ideal.Quotient.mk_surjective) (quotientTransition I n)
    (quotientTransition_surjective I n) h ((g n).f i) ha
  have hcomp : (h.comp (quotientTransition I n)).comp f =
      Ideal.Quotient.mk (I ^ (t + 1)) := by
    rw [RingHom.comp_assoc]
    dsimp [f, quotientTransition]
    rw [Ideal.Quotient.factor_comp_mk]
    exact Ideal.Quotient.factor_comp_mk _
  rw [hcomp] at hi
  rw [show (restrictedProjectiveTower.{u, v} I P g).map (homOfLE (Nat.le_succ n)).op = _ from
    Functor.ofOpSequence_map_homOfLE_succ _ n, HomologicalComplex.comp_f, Functor.map_comp]
  have hfirst : IsIso ((ModuleCat.extendScalars.{u, u, max u v}
      (Ideal.Quotient.mk (I ^ (t + 1)))).map
        ((((ModuleCat.restrictScalars.{max u v}
          f).mapHomologicalComplex (.up ℤ)).map (g n)).f i)) := hi
  infer_instance

private lemma flat_limit_and_baseChange
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (P : ∀ n : ℕ, CochainComplex (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))) ℤ)
    (g : ∀ n, P (n + 1) ⟶
      ((ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapHomologicalComplex
        (.up ℤ)).obj (P n))
    (hP : ∀ n i, Module.Projective (A ⧸ I ^ (n + 1)) ((P n).X i))
    (hg : ∀ n, IsIso (((StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction
      (ModuleCat.extendRestrictScalarsAdj.{max u v} (quotientTransition I n))
        (.up ℤ)).homEquiv _ _).symm (g n))) :
    (∀ i, Module.Flat A ((limit (restrictedProjectiveTower.{u, v} I P g)).X i)) ∧
      ∀ n, IsIso (((StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction
        (ModuleCat.extendRestrictScalarsAdj.{max u v}
          (Ideal.Quotient.mk (I ^ (n + 1)))) (.up ℤ)).homEquiv _ _).symm
            (limit.π (restrictedProjectiveTower.{u, v} I P g) (.op n))) := by
  let M := restrictedProjectiveTower.{u, v} I P g
  have hterms (i : ℤ) : Module.Flat A ((limit M).X i) ∧
      ∀ n, IsIso (((ModuleCat.extendRestrictScalarsAdj.{max u v}
        (Ideal.Quotient.mk (I ^ (n + 1)))).homEquiv _ _).symm ((limit.π M (.op n)).f i)) := by
    let ev := HomologicalComplex.eval (ModuleCat.{max u v} A) (.up ℤ) i
    let G := M ⋙ ev
    let qm (n : ℕ) : Module (A ⧸ I ^ (n + 1)) (G.obj (.op n)) := ((P n).X i).isModule
    have hs (n : ℕ) : let := qm n
        IsScalarTower A (A ⧸ I ^ (n + 1)) (G.obj (.op n)) := by
      let := qm n
      constructor
      intro a b x
      show ((Ideal.Quotient.mk (I ^ (n + 1)) a) * b) • x =
        (Ideal.Quotient.mk (I ^ (n + 1)) a) • (b • x)
      exact mul_smul _ _ _
    have hf (n : ℕ) : let := qm n
        Module.Flat (A ⧸ I ^ (n + 1)) (G.obj (.op n)) := by
      have := hP n i
      show Module.Flat (A ⧸ I ^ (n + 1)) ((P n).X i)
      infer_instance
    obtain ⟨hF, hpres⟩ := flat_limit_and_preservesLimit_quotient_positive I G qm hs hf
      (fun n => restrictedProjectiveTower_surjective I P g hg n i)
    have := hF
    refine ⟨Module.Flat.of_linearEquiv (preservesLimitIso ev M).toLinearEquiv, ?_⟩
    intro n
    let E := ModuleCat.extendScalars.{u, u, max u v} (Ideal.Quotient.mk (I ^ (n + 1)))
    have : PreservesLimit G E := hpres (I ^ (n + 1))
    have hc : (G ⋙ E).IsEventuallyConstantTo (.op n) :=
      isEventuallyConstantTo_of_isIso_succ (G ⋙ E) n
        (fun k hk => isIso_reduced_transition I P g hg n k hk i)
    have hi : IsIso (E.map ((limit.π M (.op n)).f i)) :=
      hc.isIso_π_of_isLimit (isLimitOfPreserves E (isLimitOfPreserves ev (limit.isLimit M)))
    have := full_restrictScalars_of_surjective.{u, v} (Ideal.Quotient.mk (I ^ (n + 1)))
      Ideal.Quotient.mk_surjective
    rw [Adjunction.homEquiv_counit]
    infer_instance
  refine ⟨fun i => (hterms i).1, fun n => ?_⟩
  let a := ((StacksDraft.DerivedInverseLimit.mapHomologicalComplexAdjunction
    (ModuleCat.extendRestrictScalarsAdj.{max u v} (Ideal.Quotient.mk (I ^ (n + 1))))
      (.up ℤ)).homEquiv _ _).symm (limit.π M (.op n))
  have : ∀ i, IsIso (a.f i) := fun i => (hterms i).2 n
  exact HomologicalComplex.Hom.isIso_of_components a

end AdicReduction

attribute [local instance] StacksDraft.DerivedInverseLimit.extendScalarsGeneral_additive

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 09AU.** Let `A` be Noetherian and `I` an ideal. Suppose that `F` is an inverse
system in `D(A)` whose `n`-th member is the restriction of an object `Kq n` of
`D(A ⧸ I ^ (n + 1))`. If `Kq 0` is bounded above and every transition induces an isomorphism
after derived reduction to the preceding quotient, then a derived limit `K` is bounded above
and derived `I`-complete. Moreover, the canonical map from the derived reduction of `K` to
`Kq n` is an isomorphism for every `n`. -/
@[stacks 09AU]
public theorem isDerivedComplete_and_reduction_isIso_of_isDerivedLimit
    {A : Type u} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    (F : ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{max u v} A))
    (Kq : ∀ n : ℕ, DerivedCategory (ModuleCat.{max u v} (A ⧸ I ^ (n + 1))))
    (e : ∀ n : ℕ, F.obj (.op n) ≅
      (ModuleCat.restrictScalars.{max u v} (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory.obj
        (Kq n))
    (adj : ∀ n : ℕ,
      (CochainComplex.DerivedExtensionScalars.totalDerivedExtensionScalars.{u, u, v}
          (Ideal.Quotient.mk (I ^ (n + 1)))).functor ⊣
        (ModuleCat.restrictScalars.{max u v}
          (Ideal.Quotient.mk (I ^ (n + 1)))).mapDerivedCategory)
    (hbounded : DerivedCategory.TStructure.t.minus (Kq 0))
    (t : ∀ n : ℕ, Kq (n + 1) ⟶
      (ModuleCat.restrictScalars.{max u v} (quotientTransition I n)).mapDerivedCategory.obj (Kq n))
    (htransition : ∀ n : ℕ,
      F.map (homOfLE (Nat.le_succ n)).op ≫ (e n).hom =
        (e (n + 1)).hom ≫
          (ModuleCat.restrictScalars.{max u v}
            (Ideal.Quotient.mk (I ^ (n + 2)))).mapDerivedCategory.map
            (t n) ≫ (restrictScalarsTransitionIso I n).hom.app (Kq n))
    (hcompat : ∀ n : ℕ,
      IsIso (StacksDraft.DerivedInverseLimit.derivedBaseChangeComparison.{u, v, u}
        (quotientTransition I n) (t n))) :
    letI : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A)) :=
      Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
    ∀ (K : DerivedCategory (ModuleCat.{max u v} A))
      (p : K ⟶ ∏ᶜ fun n : ℕ => F.obj (.op n))
      (δ : (∏ᶜ fun n : ℕ => F.obj (.op n)) ⟶ K⟦(1 : ℤ)⟧),
      Triangle.mk p
          (Pi.lift fun n : ℕ => Pi.π (fun n : ℕ => F.obj (.op n)) n -
            Pi.π (fun n : ℕ => F.obj (.op n)) (n + 1) ≫
              F.map (homOfLE (Nat.le_succ n)).op) δ ∈
            distTriang (DerivedCategory (ModuleCat.{max u v} A)) →
        DerivedCategory.TStructure.t.minus K ∧
          _root_.IsDerivedComplete I K ∧
          ∀ n : ℕ, IsIso (((adj n).homEquiv _ _).symm
            (p ≫ Pi.π (fun n : ℕ => F.obj (.op n)) n ≫ (e n).hom)) := by
  let : HasProductsOfShape ℕ (DerivedCategory (ModuleCat.{max u v} A)) :=
    Stacks.DerivedProducts.hasProductsOfShape_derivedCategory
  intro K p δ hK
  obtain ⟨b, P, hb, hP, eP, g, hg, hcomm⟩ :=
    exists_coherent_projectiveTower I Kq hbounded t hcompat
  obtain ⟨eM, heM, hnat⟩ :=
    exists_restrictedProjectiveTower_iso I F Kq e t htransition P eP g hcomm
  obtain ⟨hflat, hred⟩ := flat_limit_and_baseChange I P g hP hg
  exact bounded_complete_and_reductions_of_flat_models I F Kq e adj P g b hb
    (restrictedProjectiveTower_surjective I P g hg) hflat hred eP eM heM hnat K p δ hK

end Stacks.DerivedLimit.AdicSystem

end

end AdicSystemDerivedLimit
