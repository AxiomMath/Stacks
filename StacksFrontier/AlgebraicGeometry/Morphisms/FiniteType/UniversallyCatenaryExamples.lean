module

public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteType.UniversallyCatenary
public import StacksFrontier.AlgebraicGeometry.Properties.CohenMacaulay
public import StacksFrontier.AlgebraicGeometry.Properties.SchemeTypesAndCatenary.Catenary
public import StacksFrontier.RingTheory.CohenMacaulay.Catenary
public import StacksFrontier.RingTheory.Depth.Dimension
public import StacksFrontier.RingTheory.Excellent.Basic
public import StacksFrontier.RingTheory.Noetherian.ULift

/-!
# Schemes that are universally catenary

A scheme locally of finite type over a base whose affine opens have universally catenary rings
of sections is universally catenary. This covers the standard examples: a scheme locally of
finite type over a field, over a Cohen–Macaulay scheme, over the integers, or over a
one-dimensional Noetherian domain.

## Main results

* `AlgebraicGeometry.Scheme.isUniversallyCatenary_spec`: the spectrum of a Noetherian
  universally catenary ring is universally catenary.
* `AlgebraicGeometry.Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_spec`: the general
  statement, for a scheme locally of finite type over such a spectrum.
* `AlgebraicGeometry.Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_field`: over a
  field.
* `AlgebraicGeometry.Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_isCohenMacaulay`:
  over a Cohen–Macaulay scheme.
* `AlgebraicGeometry.Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_int`: over the
  integers.
* `AlgebraicGeometry.Scheme.isUniversallyCatenary_of_locallyOfFiniteType_over_dimOneDomain`:
  over a one-dimensional Noetherian domain.

## Implementation notes

A scheme over a ring is represented by a morphism to the spectrum of that ring, and the spectrum
of a ring in `Type u` is a scheme in universe `u`. So "over the integers" is read as "over
`Spec (ULift ℤ)`", which is no restriction on the scheme: `Spec (ULift ℤ)` is the terminal
scheme of the ambient universe (`AlgebraicGeometry.specULiftZIsTerminal`), canonically
isomorphic to `Spec ℤ` when that universe is `0`. The Noetherianity of `ULift ℤ` that the
statement presupposes is `ULift.isNoetherianRing`, and its universal catenarity is excellence
transported along the finite type algebra map `ℤ → ULift ℤ`, at two independent universes.

Local Noetherianity of the source, which the definition of universal catenarity requires, is the
one inferred from the locally finite type morphism and the base. For a Cohen–Macaulay base the
local Noetherianity that is part of the mathematical content of being Cohen–Macaulay is made
explicit as the typeclass the definition asks for.

Catenarity of the source of a locally finite type morphism is checked on an affine open
covering: an affine open of the source contained in the inverse image of an affine open of the
base has a ring of sections of finite type over that of the base, hence catenary. The two ring
theoretic inputs are that a Cohen–Macaulay ring is universally catenary, which is the criterion
by a Cohen–Macaulay module of full support applied to the ring itself, and that a
one-dimensional Noetherian domain is Cohen–Macaulay, which is the computation of the depth of
such a local ring as `1` from a single nonzero element of the maximal ideal.

## References

* [Stacks Project, Tag 02JB](https://stacks.math.columbia.edu/tag/02JB)
-/

@[expose] public section

open CategoryTheory TopologicalSpace IrreducibleClosedsCodim

universe u

namespace AlgebraicGeometry.Scheme

/-! ### Cohen–Macaulay rings are universally catenary -/

private theorem localRingDepth_eq_depthSup (R : Type*) [CommRing R] [IsLocalRing R] :
    localRingDepth R = Module.depthSup R (IsLocalRing.maximalIdeal R) R := by
  unfold localRingDepth Module.depthSup
  refine le_antisymm (iSup_le fun s => le_sSup ⟨s.val, rfl, s.property⟩) (sSup_le fun n hn => ?_)
  obtain ⟨rs, rfl, hmem, hreg⟩ := hn
  exact le_iSup_of_le ⟨rs, hmem, hreg⟩ le_rfl

private theorem smul_top_ne_top (B : Type*) [CommRing B] [IsLocalRing B] :
    IsLocalRing.maximalIdeal B • (⊤ : Submodule B B) ≠ ⊤ := by
  simpa [smul_eq_mul, Ideal.mul_top] using (IsLocalRing.maximalIdeal.isMaximal B).ne_top

private theorem depth_self_eq_depthSup (B : Type*) [CommRing B] [IsNoetherianRing B]
    [IsLocalRing B] : Module.depth B (IsLocalRing.maximalIdeal B) B =
      (Module.depthSup B (IsLocalRing.maximalIdeal B) B : WithBot ℕ∞) := by
  rw [Module.depth, ite_eq_right (smul_top_ne_top B), ← Module.depthSup_eq_iSup]

private theorem isCohenMacaulayLocalRingPropForm_iff (B : Type*) [CommRing B] [IsNoetherianRing B]
    [IsLocalRing B] : IsCohenMacaulayLocalRingPropForm B ↔ Module.IsMaximalCohenMacaulay B B := by
  rw [IsCohenMacaulayLocalRingPropForm, Module.IsMaximalCohenMacaulay,
    localRingDepth_eq_depthSup, depth_self_eq_depthSup]

private theorem isCohenMacaulay_self_of_isCohenMacaulayRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] (hR : IsCohenMacaulayRing R) : Module.IsCohenMacaulay R R := by
  intro p _
  have : p.asIdeal.IsPrime := p.2
  let e : LocalizedModule p.asIdeal.primeCompl R ≃ₗ[Localization.AtPrime p.asIdeal]
      Localization.AtPrime p.asIdeal :=
    (IsLocalizedModule.linearEquiv p.asIdeal.primeCompl
      (LocalizedModule.mkLinearMap p.asIdeal.primeCompl R)
      (Algebra.linearMap R (Localization.AtPrime p.asIdeal))).extendScalarsOfIsLocalization
        p.asIdeal.primeCompl (Localization.AtPrime p.asIdeal)
  rw [Module.depth_eq_depth_of_linearEquiv _ e, Module.supportDim_eq_of_equiv e,
    Module.supportDim_self_eq_ringKrullDim]
  exact (isCohenMacaulayLocalRingPropForm_iff _).mp (hR p.asIdeal)

@[sga "6 X 1.5" "special case"]
private theorem isUniversallyCatenary_of_isCohenMacaulayRing (R : Type u) [CommRing R]
    [IsNoetherianRing R] (hR : IsCohenMacaulayRing R) : Ring.IsUniversallyCatenary R := by
  refine Ring.IsUniversallyCatenary.of_isCohenMacaulay_of_support_eq_univ
    (isCohenMacaulay_self_of_isCohenMacaulayRing R hR) ?_
  rw [Module.support_eq_zeroLocus,
    Module.annihilator_eq_bot.2 (inferInstance : FaithfulSMul R R), PrimeSpectrum.zeroLocus_bot]

/-! ### One-dimensional Noetherian domains are Cohen–Macaulay -/

private theorem isCohenMacaulayLocalRingPropForm_of_isDomain_of_ringKrullDim_eq_one
    (R : Type*) [CommRing R] [IsNoetherianRing R] [IsLocalRing R] [IsDomain R]
    (hR : ringKrullDim R = 1) : IsCohenMacaulayLocalRingPropForm R := by
  have hmax : IsLocalRing.maximalIdeal R ≠ ⊥ := by
    intro h
    have hzero := ringKrullDim_eq_zero_of_isField
      (IsLocalRing.isField_iff_maximalIdeal_eq.mpr h)
    rw [hR] at hzero
    norm_num at hzero
  obtain ⟨x, hxI, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hmax
  have hxreg : IsSMulRegular R x := by
    simpa [IsSMulRegular, Function.Injective] using
      fun a b (hab : x * a = x * b) => mul_left_cancel₀ hx0 hab
  have : Nontrivial (QuotSMulTop x R) := nontrivial_quotSMulTop_of_mem_maximalIdeal R hxI
  have hseq : RingTheory.Sequence.IsRegular R [x] :=
    (RingTheory.Sequence.isRegular_cons_iff R x []).2
      ⟨hxreg, RingTheory.Sequence.IsRegular.nil R _⟩
  have hmem : ∀ y ∈ [x], y ∈ IsLocalRing.maximalIdeal R :=
    fun y hy => List.mem_singleton.mp hy ▸ hxI
  have hlow : (1 : WithBot ℕ∞) ≤
      (Module.depthSup R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) := by
    have h := Module.le_depthSup (I := IsLocalRing.maximalIdeal R) (M := R) hmem hseq
    simp only [List.length_singleton, Nat.cast_one] at h
    exact_mod_cast h
  have hupp : (Module.depthSup R (IsLocalRing.maximalIdeal R) R : WithBot ℕ∞) ≤ 1 := by
    have h := Module.depth_le_supportDim R (IsLocalRing.maximalIdeal R) R (smul_top_ne_top R)
    rwa [depth_self_eq_depthSup, Module.supportDim_self_eq_ringKrullDim, hR] at h
  show (localRingDepth R : WithBot ℕ∞) = ringKrullDim R
  rw [localRingDepth_eq_depthSup, le_antisymm hupp hlow, hR]

@[ega "IV 6.11.9" "partial"]
private theorem isCohenMacaulayRing_of_isDomain_of_ringKrullDim_eq_one (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsDomain A] (hA : ringKrullDim A = 1) : IsCohenMacaulayRing A := by
  intro P hP
  have : P.IsPrime := hP
  have hdim : ringKrullDim (Localization.AtPrime P) = (P.height : WithBot ℕ∞) :=
    IsLocalization.AtPrime.ringKrullDim_eq_height P _
  by_cases hbot : P = ⊥
  · refine (isCohenMacaulayLocalRingPropForm_iff _).mpr
      (Module.isMaximalCohenMacaulay_self_of_ringKrullDim_eq_zero ?_)
    simp [hdim, hbot]
  · have hheight : P.height = 1 :=
      le_antisymm
        (by
          have hh := Ideal.height_le_ringKrullDim_of_isPrime (I := P)
          rw [hA] at hh
          exact_mod_cast hh)
        (Order.one_le_iff_ne_zero.mpr (mt Ideal.height_eq_zero_iff_eq_bot.mp hbot))
    exact isCohenMacaulayLocalRingPropForm_of_isDomain_of_ringKrullDim_eq_one _
      (by rw [hdim, hheight]; norm_num)

/-! ### The local criterion -/

private theorem isUniversallyCatenary_of_forall_exists_affineOpen (S : Scheme.{u})
    [IsLocallyNoetherian S]
    (hS : ∀ x : S, ∃ U : S.affineOpens, x ∈ U.1 ∧ Ring.IsUniversallyCatenary Γ(S, U.1)) :
    IsUniversallyCatenary S := by
  rw [isUniversallyCatenary_iff]
  intro X f hf
  have key : ∀ x : X, ∃ V : X.affineOpens, x ∈ V.1 ∧ Ring.IsCatenary Γ(X, V.1) := by
    intro x
    obtain ⟨U, hxU, hU⟩ := hS (f.base x)
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open
      (show x ∈ f ⁻¹ᵁ (U.1 : S.Opens) from hxU) (f ⁻¹ᵁ (U.1 : S.Opens)).isOpen
    let _ : Algebra Γ(S, U.1) Γ(X, V) := (f.appLE U.1 V hVU).hom.toAlgebra
    have : Algebra.FiniteType Γ(S, U.1) Γ(X, V) :=
      HasRingHomProperty.appLE @LocallyOfFiniteType f hf U ⟨V, hV⟩ hVU
    exact ⟨⟨V, hV⟩, hxV, hU Γ(X, V)⟩
  choose V hxV hVcat using key
  have htfae := (isCatenarySpace_tfae X).out 1 4
  exact htfae.mpr ⟨X, V,
    IsOpenCover.mk (top_unique fun y _ => Opens.mem_iSup.mpr ⟨y, hxV y⟩), hVcat⟩

/-! ### The examples -/

/-- The spectrum of a Noetherian universally catenary ring is a universally catenary scheme. -/
@[ega "IV 5.6.3" "(ii)"]
theorem isUniversallyCatenary_spec (A : Type u) [CommRing A] [IsNoetherianRing A]
    (hA : Ring.IsUniversallyCatenary A) : IsUniversallyCatenary (Spec (.of A)) := by
  refine isUniversallyCatenary_of_forall_exists_affineOpen _ fun x => ?_
  refine ⟨⟨⊤, isAffineOpen_top (Spec (.of A))⟩, by simp, ?_⟩
  exact Ring.IsUniversallyCatenary.of_surjective
    (Scheme.ΓSpecIso (.of A)).commRingCatIsoToRingEquiv.symm.surjective hA

/-- A scheme locally of finite type over the spectrum of a Noetherian universally catenary ring
is universally catenary. This is the general form of which the families listed in Stacks Project
Tag 02JB are instances. -/
@[ega "IV 10.6.1" "(i), special case", ega "IV 5.6.3" "(ii)"]
theorem isUniversallyCatenary_of_locallyOfFiniteType_over_spec (A : Type u) [CommRing A]
    [IsNoetherianRing A] (hA : Ring.IsUniversallyCatenary A) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    @IsUniversallyCatenary X (LocallyOfFiniteType.isLocallyNoetherian f) :=
  isUniversallyCatenary_of_locallyOfFiniteType f (isUniversallyCatenary_spec A hA)

/-- **Stacks Project, Tag 02JB, part (1).** A scheme locally of finite type over a field is
universally catenary. -/
@[stacks 02JB "part (1)", ega "IV 10.7.1" "2° over a field"]
theorem isUniversallyCatenary_of_locallyOfFiniteType_over_field (k : Type u) [Field k]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] :
    @IsUniversallyCatenary X (LocallyOfFiniteType.isLocallyNoetherian f) :=
  isUniversallyCatenary_of_locallyOfFiniteType_over_spec k
    ((isExcellent_of_standard_classes_and_finiteType.{u, u}).1 k).2 f

/-- **Stacks Project, Tag 02JB, part (2).** A scheme locally of finite type over a locally
Noetherian Cohen–Macaulay scheme is universally catenary. -/
@[stacks 02JB "part (2)",
  ega "IV 10.6.1" "(i), special case",
  ega "IV 10.7.1" "more general",
  ega "IV 5.2.5" "more general", sga "6 X 1.5" "more general"]
theorem isUniversallyCatenary_of_locallyOfFiniteType_over_isCohenMacaulay {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [IsLocallyNoetherian S] (hS : IsCohenMacaulay S) :
    @IsUniversallyCatenary X (LocallyOfFiniteType.isLocallyNoetherian f) := by
  refine isUniversallyCatenary_of_locallyOfFiniteType f
    (isUniversallyCatenary_of_forall_exists_affineOpen S fun x => ?_)
  obtain ⟨U, hxU, hN, hCM⟩ := hS.exists_affineOpen x
  exact ⟨U, hxU, @isUniversallyCatenary_of_isCohenMacaulayRing Γ(S, U.1) _ hN hCM⟩

/-- The integers, lifted to an arbitrary universe, are universally catenary: `ULift ℤ` is a
finite module algebra over `ℤ`, hence of finite type over it, and the integers are excellent. -/
private theorem isUniversallyCatenary_uliftInt :
    Ring.IsUniversallyCatenary (ULift.{u} ℤ) :=
  have : Algebra.FiniteType ℤ (ULift.{u} ℤ) := Module.Finite.finiteType _
  ((isExcellent_of_standard_classes_and_finiteType.{0, u}).2.2.2.2 ℤ (ULift.{u} ℤ)
    (isExcellent_of_standard_classes_and_finiteType.{0, 0}).2.2.1).2

/-- **Stacks Project, Tag 02JB, part (3).** A scheme locally of finite type over the integers is
universally catenary. The base is `Spec (ULift ℤ)`, the terminal scheme of the ambient universe,
so this is the statement for a scheme in an arbitrary universe. -/
@[stacks 02JB "part (3)", ega "IV 10.6.1" "(i), special case", ega "IV 10.7.1" "2° over Z"]
theorem isUniversallyCatenary_of_locallyOfFiniteType_over_int {X : Scheme.{u}}
    (f : X ⟶ Spec (.of (ULift.{u} ℤ))) [LocallyOfFiniteType f] :
    @IsUniversallyCatenary X (LocallyOfFiniteType.isLocallyNoetherian f) :=
  isUniversallyCatenary_of_locallyOfFiniteType_over_spec (ULift.{u} ℤ)
    isUniversallyCatenary_uliftInt f

/-- **Stacks Project, Tag 02JB, part (4).** A scheme locally of finite type over a
one-dimensional Noetherian domain is universally catenary. -/
@[stacks 02JB "part (4)"]
theorem isUniversallyCatenary_of_locallyOfFiniteType_over_dimOneDomain (A : Type u) [CommRing A]
    [IsNoetherianRing A] [IsDomain A] (hA : ringKrullDim A = 1) {X : Scheme.{u}}
    (f : X ⟶ Spec (.of A)) [LocallyOfFiniteType f] :
    @IsUniversallyCatenary X (LocallyOfFiniteType.isLocallyNoetherian f) :=
  isUniversallyCatenary_of_locallyOfFiniteType_over_spec A
    (isUniversallyCatenary_of_isCohenMacaulayRing A
      (isCohenMacaulayRing_of_isDomain_of_ringKrullDim_eq_one A hA)) f

end AlgebraicGeometry.Scheme
