module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.RingTheory.Ideal.IsPrincipal
public import Mathlib.RingTheory.Localization.AtPrime.Basic
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier
public import StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic

/-!
# Stalkwise principal ideal sheaves on a locally Noetherian scheme

On a locally Noetherian scheme a closed subscheme whose defining ideal becomes principal in the
local ring at every point of the subscheme is locally principal: the single generator of the
stalk ideal spreads to a generator on a whole affine neighbourhood. This is the first part of
Tag 0AG8, and `isLocallyPrincipal_of_stalk_isPrincipal` is how it reads here. The second part,
that a stalkwise generator which is a nonzerodivisor makes the subscheme an effective Cartier
divisor, is `Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor` of
`StacksFrontier/AlgebraicGeometry/Divisors/EffectiveCartierStalk/StalkwiseRegular.lean`, which
consumes the result below: the two carry the tag together.

The spreading-out step is pure commutative algebra and is isolated as
`exists_notMem_isPrincipal_localizationAway`: a finitely generated ideal `I` of a commutative
ring `A` whose image in the localization at a prime `p` is principal already has principal
image in a localization `A[1/h]` for some `h ∉ p`. Given a generator `x/c` of `I A_p` with
`x ∈ I` and `c ∉ p`, every one of the finitely many generators `f` of `I` satisfies
`d_f · c · f ∈ (x)` for some `d_f ∉ p`; the element `h = c · ∏_f d_f` is then outside `p` and
inverting it makes `x` generate.

Passing from that statement to the geometric one uses the local structure of a scheme at a
point of an affine open `V`: the stalk is the localization of `Γ(X, V)` at the prime
corresponding to the point, so principality of the stalk ideal is principality of the localized
ideal, and `Γ(X, V_h)` is the localization of `Γ(X, V)` away from `h`, so the conclusion of the
algebraic statement is principality of `I.ideal` on the affine open `V_h`.

## Main results

* `Stacks.Divisors.exists_notMem_isPrincipal_localizationAway`: principality of a finitely
  generated ideal at a prime spreads to a principal open neighbourhood of that prime.
* `Stacks.Divisors.isLocallyPrincipal_of_stalk_isPrincipal`: Tag 0AG8, local principality from
  principality of the stalk ideals along the subscheme.

## Implementation notes

The Noetherian hypothesis of the source enters only through finite generation of the ideal, so
`exists_notMem_isPrincipal_localizationAway` is stated for a finitely generated ideal directly;
the geometric statement supplies it from `IsLocallyNoetherian`, which makes `Γ(X, V)` Noetherian
for an affine open `V`.

The stalk ideal is `AlgebraicGeometry.IdealSheafData.stalk`. Two facts about it are needed and
proved here: it is computed from a single affine open containing the point
(`AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ`), and it is the unit ideal exactly off the
support of the ideal sheaf (`stalk_eq_top_iff_notMem_support`), which is what lets the hypothesis
of Tag 0AG8 be imposed only along the subscheme. The second goes through the characterization
`stalk_le_maximalIdeal_iff_mem_support`: a point lies in the support exactly when the stalk ideal
consists of non-units.

## References

* [Stacks Project, Tag 0AG8](https://stacks.math.columbia.edu/tag/0AG8)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

namespace Stacks.Divisors

section Algebra

open scoped Pointwise

/-- A finitely generated ideal which is principal at a prime is principal on some principal open
neighbourhood of that prime: there is `h ∉ p` such that the image of the ideal in the
localization of `A` away from `h` is principal. -/
theorem exists_notMem_isPrincipal_localizationAway {A : Type*} [CommRing A] (I p : Ideal A)
    [p.IsPrime] (hI : I.FG)
    (hp : (I.map (algebraMap A (Localization.AtPrime p))).IsPrincipal) :
    ∃ h : A, h ∉ p ∧ (I.map (algebraMap A (Localization.Away h))).IsPrincipal := by
  classical
  have := hp
  obtain ⟨s, hs, hspan⟩ := Submodule.fg_def.mp hI
  let z := Submodule.IsPrincipal.generator (I.map (algebraMap A (Localization.AtPrime p)))
  have hz : z ∈ I.map (algebraMap A (Localization.AtPrime p)) :=
    Submodule.IsPrincipal.generator_mem _
  obtain ⟨y, hc⟩ :=
    (IsLocalization.mem_map_algebraMap_iff p.primeCompl (Localization.AtPrime p)).mp hz
  let x : A := y.1.1
  have hx : x ∈ I := y.1.2
  let c := y.2
  have hd_exists : ∀ f : A, f ∈ s → ∃ d, d ∈ p.primeCompl ∧
      d * (c.1 * f) ∈ Ideal.span ({x} : Set A) := by
    intro f hf
    have hmf : algebraMap A (Localization.AtPrime p) f ∈
        I.map (algebraMap A (Localization.AtPrime p)) :=
      Ideal.mem_map_of_mem _ (hspan ▸ Submodule.subset_span hf)
    obtain ⟨q, hq⟩ :=
      (Submodule.IsPrincipal.mem_iff_eq_smul_generator
        (I.map (algebraMap A (Localization.AtPrime p)))).mp hmf
    have hcf : algebraMap A (Localization.AtPrime p) (c.1 * f) ∈
        (Ideal.span ({x} : Set A)).map (algebraMap A (Localization.AtPrime p)) := by
      rw [map_mul, hq, Algebra.smul_def, Algebra.algebraMap_self, RingHom.id_apply]
      have hcz : algebraMap A (Localization.AtPrime p) c.1 * (q * z) =
          algebraMap A (Localization.AtPrime p) x * q := by
        calc
          algebraMap A (Localization.AtPrime p) c.1 * (q * z) =
              (algebraMap A (Localization.AtPrime p) c.1 * z) * q := by ac_rfl
          _ = (z * algebraMap A (Localization.AtPrime p) c.1) * q := by ac_rfl
          _ = algebraMap A (Localization.AtPrime p) x * q := by rw [hc]
      rw [hcz]
      simpa [mul_comm] using
        (Ideal.mul_mem_left _ q
          (Ideal.mem_map_of_mem _ (Ideal.subset_span (Set.mem_singleton x))))
    exact (IsLocalization.algebraMap_mem_map_algebraMap_iff p.primeCompl
      (Localization.AtPrime p) (Ideal.span ({x} : Set A)) (c.1 * f)).mp hcf
  let d : A → A := fun f => if hf : f ∈ s then Classical.choose (hd_exists f hf) else 1
  have hd (f : A) (hf : f ∈ s) : d f ∈ p.primeCompl := by
    simp only [d, dite_eq_left hf]
    exact (Classical.choose_spec (hd_exists f hf)).1
  have hdf (f : A) (hf : f ∈ s) : d f * (c.1 * f) ∈ Ideal.span ({x} : Set A) := by
    simp only [d, dite_eq_left hf]
    exact (Classical.choose_spec (hd_exists f hf)).2
  let t := hs.toFinset
  let h := c.1 * t.prod d
  have hh : h ∈ p.primeCompl :=
    p.primeCompl.mul_mem c.2 (prod_mem fun a ha => hd a (hs.mem_toFinset.mp ha))
  refine ⟨h, hh, ?_⟩
  let K := I.map (algebraMap A (Localization.Away h))
  have hgen : K ≤ Ideal.span ({algebraMap A (Localization.Away h) x} : Set _) := by
    change Ideal.map (algebraMap A (Localization.Away h)) I ≤ _
    rw [Ideal.map_le_iff_le_comap, ← hspan]
    refine Ideal.span_le.2 fun f hf => ?_
    change algebraMap A (Localization.Away h) f ∈
      Ideal.span ({algebraMap A (Localization.Away h) x} : Set _)
    have hmap : Ideal.map (algebraMap A (Localization.Away h)) (Ideal.span ({x} : Set A)) =
        Ideal.span ({algebraMap A (Localization.Away h) x} : Set _) := by
      rw [Ideal.map_span]
      simp only [Set.image_singleton]
    rw [← hmap]
    refine (IsLocalization.algebraMap_mem_map_algebraMap_iff (Submonoid.powers h)
      (Localization.Away h) (Ideal.span ({x} : Set A)) f).2 ⟨h, Submonoid.mem_powers h, ?_⟩
    have hrest : (t.erase f).prod d * (d f * (c.1 * f)) ∈ Ideal.span ({x} : Set A) :=
      Ideal.mul_mem_left _ _ (hdf f hf)
    change c.1 * t.prod d * f ∈ Ideal.span ({x} : Set A)
    rw [← Finset.mul_prod_erase t d (hs.mem_toFinset.mpr hf)]
    simpa [mul_assoc, mul_left_comm, mul_comm] using hrest
  change K.IsPrincipal
  rw [le_antisymm hgen ((Ideal.span_singleton_le_iff_mem _).2 (Ideal.mem_map_of_mem _ hx))]
  infer_instance

end Algebra

section Stalk


/-- The stalk ideal at `x` consists of non-units exactly when `x` lies in the support of the
ideal sheaf. -/
theorem stalk_le_maximalIdeal_iff_mem_support {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk I x ≤ IsLocalRing.maximalIdeal (X.presheaf.stalk x) ↔
      x ∈ I.support := by
  simp only [IdealSheafData.stalk, iSup_le_iff]
  refine ⟨fun h ↦ ?_, fun h U hx ↦ ?_⟩
  · rw [Scheme.IdealSheafData.mem_support_iff]
    intro U
    rw [Scheme.mem_zeroLocus_iff]
    intro s hs
    by_cases hxU : x ∈ U.1
    · have hs' : (X.presheaf.germ U.1 x hxU).hom s ∈
          IsLocalRing.maximalIdeal (X.presheaf.stalk x) := h U hxU (Ideal.mem_map_of_mem _ hs)
      rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff] at hs'
      exact fun hbasic ↦ hs' ((Scheme.mem_basicOpen X s x hxU).mp hbasic)
    · exact fun hbasic ↦ hxU (X.basicOpen_le s hbasic)
  · rw [Ideal.map_le_iff_le_comap]
    intro s hs
    rw [Ideal.mem_comap, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    exact (Scheme.mem_basicOpen X s x hx).not.mp
      ((X.mem_zeroLocus_iff _ x).mp (Scheme.IdealSheafData.mem_support_iff.mp h U) s hs)

/-- The stalk ideal at `x` is the unit ideal exactly when `x` lies outside the support of the
ideal sheaf. -/
theorem stalk_eq_top_iff_notMem_support {X : Scheme.{u}} (I : X.IdealSheafData) (x : X) :
    IdealSheafData.stalk I x = ⊤ ↔ x ∉ I.support := by
  rw [← stalk_le_maximalIdeal_iff_mem_support]
  refine ⟨fun h hle ↦ ?_, Not.imp_symm IsLocalRing.le_maximalIdeal⟩
  exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.mp (h ▸ hle))

/-- If `I.map f` is principal and `g.comp f = h`, then `I.map h` is principal. -/
private theorem isPrincipal_map_of_comp_eq {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (I : Ideal A) (f : A →+* B) (g : B →+* C) (h : A →+* C) (hgf : g.comp f = h)
    (hI : (I.map f).IsPrincipal) : (I.map h).IsPrincipal := by
  subst hgf
  rw [← Ideal.map_map]
  exact hI.map_ringHom g

/-- **Principality of an ideal sheaf spreads from a local ring to an affine neighbourhood.**  If
the ideal an ideal sheaf induces in the local ring at `x` is principal, then `x` has an affine
open neighbourhood on which the ideal of the ideal sheaf is itself principal: the ideal is
finitely generated there, so finitely many denominators clear at once and the ideal becomes
principal on a basic open neighbourhood. -/
theorem exists_affineOpens_isPrincipal_of_stalk_isPrincipal {X : Scheme.{u}}
    [IsLocallyNoetherian X] (I : X.IdealSheafData) (x : X)
    (hstalk : (IdealSheafData.stalk I x).IsPrincipal) :
    ∃ U : X.affineOpens, x ∈ (U : Set X) ∧ (I.ideal U).IsPrincipal := by
  obtain ⟨U, hU, hxU, -⟩ := exists_isAffineOpen_mem_and_subset (U := ⊤) (Set.mem_univ x)
  let V : X.affineOpens := ⟨U, hU⟩
  have hxV : x ∈ V.1 := hxU
  have : IsNoetherianRing Γ(X, V) := IsLocallyNoetherian.component_noetherian V
  let p : PrimeSpectrum Γ(X, V) := V.2.primeIdealOf ⟨x, hxV⟩
  let P : Ideal Γ(X, V) := p.asIdeal
  have : P.IsPrime := p.isPrime
  let _ : Algebra Γ(X, V) (X.presheaf.stalk x) := X.presheaf.algebra_section_stalk ⟨x, hxV⟩
  have : IsLocalization P.primeCompl (X.presheaf.stalk x) := V.2.isLocalization_stalk ⟨x, hxV⟩
  have hprincipalStalk :
      ((I.ideal V).map (algebraMap Γ(X, V) (X.presheaf.stalk x))).IsPrincipal := by
    change ((I.ideal V).map (X.presheaf.germ V.1 x hxV).hom).IsPrincipal
    rwa [← AlgebraicGeometry.IdealSheafData.stalk_eq_map_germ I x V hxV]
  have hprincipalLocal :
      ((I.ideal V).map (algebraMap Γ(X, V) (Localization.AtPrime P))).IsPrincipal := by
    let e := IsLocalization.algEquiv P.primeCompl (Localization.AtPrime P)
      (X.presheaf.stalk x)
    exact isPrincipal_map_of_comp_eq _ _ e.symm.toRingHom _ (by ext a; exact e.symm.commutes a)
      hprincipalStalk
  obtain ⟨a, ha, hprincipalAway⟩ := exists_notMem_isPrincipal_localizationAway (I.ideal V) P
    (Ideal.fg_of_isNoetherianRing (I.ideal V)) hprincipalLocal
  let W := X.affineBasicOpen a
  have hxW : x ∈ W.1 := by
    refine (X.mem_basicOpen' a ⟨x, hxV⟩).2 ?_
    change IsUnit (algebraMap Γ(X, V) (X.presheaf.stalk x) a)
    exact IsLocalization.map_units (M := P.primeCompl) _ ⟨a, ha⟩
  let _ : Algebra Γ(X, V) Γ(X, W) :=
    (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom.toAlgebra
  have : IsLocalization.Away a Γ(X, W) := V.2.isLocalization_basicOpen a
  let e := IsLocalization.algEquiv (.powers a) (Localization.Away a) Γ(X, W)
  have hcomp : e.toRingHom.comp (algebraMap Γ(X, V) (Localization.Away a)) =
      (X.presheaf.map (homOfLE (X.basicOpen_le a)).op).hom := by
    ext r; exact e.commutes r
  refine ⟨W, hxW, ?_⟩
  rw [← I.map_ideal (X.basicOpen_le a)]
  exact isPrincipal_map_of_comp_eq _ _ e.toRingHom _ hcomp hprincipalAway

/-- **Stacks Project, Tag 0AG8.** A closed subscheme of a locally Noetherian scheme is locally
principal if its ideal is principal in the local ring at each point of the subscheme.

Outside the support the ideal of the local ring is the unit ideal, so the hypothesis is only
about points of the subscheme; at each point principality then spreads to an affine
neighbourhood by `Stacks.Divisors.exists_affineOpens_isPrincipal_of_stalk_isPrincipal`.

The companion
`Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor` upgrades the
conclusion to an effective Cartier divisor when the stalk generators are nonzerodivisors. -/
@[stacks 0AG8]
theorem isLocallyPrincipal_of_stalk_isPrincipal {X : Scheme.{u}} [IsLocallyNoetherian X]
    (I : X.IdealSheafData)
    (hI : ∀ x : X, x ∈ I.support → (IdealSheafData.stalk I x).IsPrincipal) :
    IsLocallyPrincipal I := fun x =>
  exists_affineOpens_isPrincipal_of_stalk_isPrincipal I x <| by
    by_cases hx : x ∈ I.support
    · exact hI x hx
    · rw [(stalk_eq_top_iff_notMem_support I x).2 hx]
      exact ⟨1, by simp⟩

end Stalk

end Stacks.Divisors

end
