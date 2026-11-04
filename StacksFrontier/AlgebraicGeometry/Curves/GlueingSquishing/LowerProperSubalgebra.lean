module

public import Mathlib.RingTheory.Localization.Ideal
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.SpreadOutSubalgebra

/-!
# The spread-out subalgebra of [Stacks, Tag 0C1L] is proper at the lower end too

`Stacks.GlueSquishFactor.exists_isFinite_subalg_ne_top` spreads the stalk subalgebra
`𝒪_{X,x} + m_x·(f_*𝒪_{X'})_x` out to a finite quasi-coherent `𝒜 = 𝒪_X + ℐ_x·f_*𝒪_{X'}` and
concludes that it is proper at the **upper** end: `𝒜(U) ≠ Γ(X', f⁻¹U)`. The measure of the
induction needs the *same* `𝒜` to be proper at the **lower** end as well — `𝒪_X ⊊ 𝒜` — because
that is what makes the measure of the upper half of the splitting drop, exactly as upper
properness is what makes the measure of the lower half drop
(`Stacks.GlueSquishFactor.sheafMultiplicity_cokernel_lt_of_mem_supp_left` and its `_right`
companion). This file supplies lower properness, over the same affine open `U`.

At the stalk both ends are proper at once in the branch `m_A·B ⊄ A` of the dichotomy
`Stacks.GlueSquishFactor.forall_exists_algebraMap_eq_or_exists_subalgebra`: the hypotheses of
`Stacks.GlueSquishFactor.addMapMaximalIdeal_ne_top` and of
`Stacks.GlueSquishFactor.bot_lt_addMapMaximalIdeal` are then both available for the one
subalgebra `𝒪_{X,x} + m_x·B`. So this is a spreading-out of something already proved, not new
mathematics.

## Main results

* `Stacks.GlueSquishFactor.primeIdealOf_le_ideal_closedIdeal_singleton` — the vanishing ideal of a
  closed point on an affine open containing it contains, hence is, the prime that point cuts out.
  The upper-end lemma `Stacks.GlueSquishFactor.ne_top_obj_idealSmulSubalg` uses the other
  inclusion, `Stacks.AlgebraicGeometry.IdealPowerSmul.mem_closed_iff_vanishingIdeal_le`.
* `Stacks.GlueSquishFactor.exists_mem_map_primeIdealOf_notMem_range` — **the core**: if some
  element of `m_x·(f_*𝒪_{X'})_x` is not a germ of `𝒪_{X,x}`, then some section of `f_*𝒪_{X'}` over
  `U` lying in `p_x·Γ(X', f⁻¹U)` is not a section of `𝒪_X`.
* `Stacks.GlueSquishFactor.exists_mem_obj_idealSmulSubalg_notMem_range` — **the core read on the
  spread-out subalgebra itself**: that section is a section of
  `𝒜 = 𝒪_X + ℐ_x·f_*𝒪_{X'}`, so `𝒪_X(U) ⊊ 𝒜(U)` for the very subalgebra whose *upper*
  properness is `Stacks.GlueSquishFactor.ne_top_obj_idealSmulSubalg`.

## Implementation notes

**The direction that works.** Upper properness had to carry *every* germ up to the stalk, which
is why `Stacks.GlueSquishFactor.ne_top_obj_idealSmulSubalg` runs an `Algebra.adjoin_induction` and
then divides out a denominator. Lower properness only needs *one* element to come back down, so
the whole argument is the identity

`m_x.map(𝒪_{X,x} → B) = (p_x.map(Γ(X,U) → Γ(X', f⁻¹U))).map(Γ(X', f⁻¹U) → B)`

— both sides are `p_x` pushed along the one commuting square of germ maps, by `Ideal.map_map` and
`IsLocalization.AtPrime.under_maximalIdeal` — followed by
`IsLocalization.mem_map_algebraMap_iff`, which presents the given stalk element as a germ over `U`
divided by a denominator that is a *unit of `𝒪_{X,x}`*. A germ coming from `𝒪_X` would then make
the stalk element come from `𝒪_{X,x}`, against the hypothesis.

**What was blocking the reading on the subalgebra, and it was not the `•`.** The section `s` the
core produces lies in `p_x · Γ(X', f⁻¹U)`, which
`Stacks.GlueSquishFactor.primeIdealOf_le_ideal_closedIdeal_singleton` and `Ideal.map_mono` put
inside `ℐ_x(U) · Γ(X', f⁻¹U)`, which `Ideal.smul_top_eq_map` identifies with the generating set
`Stacks.GlueSquishFactor.idealSmulSet` of the subalgebra, which
`Stacks.AlgebraicGeometry.SubalgebraGeneratedByModule.mem_adjoinSubmodule_of_mem` and
`Stacks.GlueSquishFactor.mem_idealSmulSubalg_iff` put inside the subalgebra. An earlier note here
diagnosed the obstruction as the `•` of `Stacks.GlueSquishFactor.sections_idealSmulModule` wanting
a `Semiring` on a spelling `Stacks.RelativeSpec.AlgebraSheaf.algebraSections` does not supply, and
prescribed a detour through `Stacks.GlueSquishFactor.submoduleSet_idealSmulModule`. **Neither was
the problem and the detour is not taken.** `Γ(AlgebraSheaf.underlyingModule (pushforwardAlgebra f),
U)` and `AlgebraSheaf.sections (pushforwardAlgebra f) U` are both `Γ(X', f⁻¹U)` at default
transparency, so the `•` is available directly. What fails is `rw [mem_idealSmulSubalg_iff]`: `rw`
re-elaborates the goal at *implicit* transparency, at which the two spellings are no longer the
same type, and reports an application type mismatch on the section. Applying the iff as a term,
`(mem_idealSmulSubalg_iff ..).mpr`, type-checks at default transparency and the proof is three
lines.

**The point of the support.** `𝒪_X(U) ⊊ 𝒜(U)` becomes a point of
`SheafOfModules.supp (cokernel (𝒪_X ⟶ 𝒜))` by
`Stacks.GlueSquishFactor.nonempty_supp_cokernel_unitModuleMap_of_notMem_range` in
`StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.BadPointsSupport` — the lower-end analogue
of `Stacks.GlueSquishFactor.nonempty_supp_cokernel_underlyingModuleMap_incl` — and the two ends
are packaged together as
`Stacks.GlueSquishFactor.exists_isFinite_subalg_mem_supp_cokernel_both` there. The `Mono` side
condition is `CategoryTheory.mono_of_mono` against the factorization
`Stacks.GlueSquishFactor.unitModuleMap_comp_underlyingModuleMap_incl`, or directly from
injectivity on sections as `Stacks.GlueSquishFactor.mono_unitModuleMap_subalg`.

## No stacks attribute

**No `@[stacks]` attribute is attached, and none is earned.** This is an input to the splitting
hypothesis `hsplit` of `Stacks.GlueSquishFactor.isElementaryChain_of_isAlmostIso`, which is still
unproved.

## References

* [Stacks Project, Tag 0C1L](https://stacks.math.columbia.edu/tag/0C1L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite AlgebraicGeometry
open Stacks.RelativeSpec Stacks.AffineAlgebraEquivalence
open Stacks.AlgebraicGeometry.SubalgebraGeneratedByModule
open Stacks.AlgebraicGeometry.IdealPowerSmul

universe u

namespace Stacks.GlueSquishFactor

/-! ### The vanishing ideal of a closed point -/

/-- **The prime cut out by a point of an affine open is contained in the vanishing ideal of that
point.** Together with `Stacks.AlgebraicGeometry.IdealPowerSmul.mem_closed_iff_vanishingIdeal_le`
the two are equal; the inclusion in this direction is what puts a section of `p_x·Γ(X', f⁻¹U)`
into the sections of `𝒪_X + ℐ_x·f_*𝒪_{X'}`. -/
theorem primeIdealOf_le_ideal_closedIdeal_singleton {X : Scheme.{u}} (U : X.affineOpens) {x : X}
    (hx : x ∈ U.1) (hcl : IsClosed ({x} : Set X)) :
    (U.2.primeIdealOf ⟨x, hx⟩).asIdeal ≤ (closedIdeal (⟨{x}, hcl⟩ : Closeds X)).ideal U := by
  have hsub : U.2.fromSpec ⁻¹' ({x} : Set X) ⊆ {U.2.primeIdealOf ⟨x, hx⟩} := by
    intro q hq
    have hq' : U.2.fromSpec q = x := hq
    exact Set.mem_singleton_iff.mpr
      ((primeIdealOf_fromSpec U q).symm.trans (congrArg _ (Subtype.ext hq')))
  rw [show (closedIdeal (⟨{x}, hcl⟩ : Closeds X)).ideal U
      = PrimeSpectrum.vanishingIdeal (U.2.fromSpec ⁻¹' ({x} : Set X)) from rfl]
  exact le_trans (le_of_eq (PrimeSpectrum.vanishingIdeal_singleton _).symm)
    (PrimeSpectrum.vanishingIdeal_anti_mono hsub)

/-! ### One section of `p_x · Γ(X', f⁻¹U)` which is not a section of `𝒪_X` -/

/-- **The core of lower properness.** Let `f : X' ⟶ X` be finite, let `U` be an affine open and
`x ∈ U`. If some element of `m_x · (f_*𝒪_{X'})_x` is not the image of an element of `𝒪_{X,x}`,
then some section of `f_*𝒪_{X'}` over `U` lying in `p_x · Γ(X', f⁻¹U)` is not the image of a
section of `𝒪_X` over `U`.

The hypothesis is the negation of the first disjunct of
`Stacks.GlueSquishFactor.forall_exists_algebraMap_eq_or_exists_subalgebra`, so it is exactly what
the branch of the dichotomy in which an intermediate subalgebra exists hands over. -/
theorem exists_mem_map_primeIdealOf_notMem_range {X' X : Scheme.{u}} (f : X' ⟶ X) [IsFinite f]
    {U : X.Opens} (hU : IsAffineOpen U) {x : X} (hx : x ∈ U)
    (hb : letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f.c).hom.toAlgebra
      ∃ b ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
          (algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)),
        ∀ a : X.presheaf.stalk x,
          algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) a ≠ b) :
    ∃ s ∈ (hU.primeIdealOf ⟨x, hx⟩).asIdeal.map (f.app U).hom,
      s ∉ Set.range (f.app U).hom := by
  let := X.presheaf.algebra_section_stalk (⟨x, hx⟩ : U)
  let : Algebra Γ(X, U) Γ(X', f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  let : Algebra Γ(X', f ⁻¹ᵁ U) ((f.base _* X'.presheaf).stalk x) :=
    ((f.base _* X'.presheaf).germ U x hx).hom.toAlgebra
  let : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
    ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f.c).hom.toAlgebra
  have hlocB : IsLocalization (Algebra.algebraMapSubmonoid Γ(X', f ⁻¹ᵁ U)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl) ((f.base _* X'.presheaf).stalk x) :=
    IsAffineOpen.isLocalization_pushforwardStalk f hU hx
  have hlocA : IsLocalization.AtPrime (X.presheaf.stalk x)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal := hU.isLocalization_stalk ⟨x, hx⟩
  -- the one commuting square of germ maps
  have hcomm : (algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)).comp
        (algebraMap Γ(X, U) (X.presheaf.stalk x))
      = (algebraMap Γ(X', f ⁻¹ᵁ U) ((f.base _* X'.presheaf).stalk x)).comp
        (algebraMap Γ(X, U) Γ(X', f ⁻¹ᵁ U)) := by
    refine RingHom.ext fun r => ?_
    simp only [RingHom.comp_apply]
    exact TopCat.Presheaf.stalkFunctor_map_germ_apply U x hx f.c r
  -- `m_x · B` is `p_x` pushed along either side of that square
  have hmapeq : (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
        (algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x))
      = ((hU.primeIdealOf ⟨x, hx⟩).asIdeal.map (algebraMap Γ(X, U) Γ(X', f ⁻¹ᵁ U))).map
        (algebraMap Γ(X', f ⁻¹ᵁ U) ((f.base _* X'.presheaf).stalk x)) := by
    have hm : (hU.primeIdealOf ⟨x, hx⟩).asIdeal.map
          (algebraMap Γ(X, U) (X.presheaf.stalk x))
        = IsLocalRing.maximalIdeal (X.presheaf.stalk x) := by
      rw [← IsLocalization.AtPrime.under_maximalIdeal (X.presheaf.stalk x)
        (hU.primeIdealOf ⟨x, hx⟩).asIdeal]
      exact IsLocalization.map_under (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl
        (X.presheaf.stalk x) _
    rw [← hm, Ideal.map_map, Ideal.map_map, hcomm]
  obtain ⟨b, hbmem, hbnot⟩ := hb
  rw [hmapeq] at hbmem
  obtain ⟨⟨⟨j, hj⟩, n⟩, hjn⟩ := (IsLocalization.mem_map_algebraMap_iff
    (Algebra.algebraMapSubmonoid Γ(X', f ⁻¹ᵁ U)
      (hU.primeIdealOf ⟨x, hx⟩).asIdeal.primeCompl)
    ((f.base _* X'.presheaf).stalk x)).mp hbmem
  obtain ⟨w, hw, hwn⟩ := n.2
  have hunit : IsUnit (X.presheaf.germ U x hx w) :=
    IsLocalRing.notMem_maximalIdeal.mp fun hcon =>
      hw (IsAffineOpen.comap_maximalIdeal_germ hU (⟨x, hx⟩ : U) ▸ Ideal.mem_comap.mpr hcon)
  obtain ⟨v, hv⟩ := hunit
  refine ⟨j, hj, ?_⟩
  rintro ⟨a, ha⟩
  refine hbnot (X.presheaf.germ U x hx a * ↑v⁻¹) ?_
  -- the denominator is a unit of `𝒪_{X,x}`
  have hn : algebraMap Γ(X', f ⁻¹ᵁ U) ((f.base _* X'.presheaf).stalk x) (n : Γ(X', f ⁻¹ᵁ U))
      = algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) ↑v := by
    rw [← hwn, hv]
    exact (RingHom.congr_fun hcomm w).symm
  -- and the numerator comes from `𝒪_X`
  have hjA : algebraMap Γ(X', f ⁻¹ᵁ U) ((f.base _* X'.presheaf).stalk x) j
      = algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)
        (X.presheaf.germ U x hx a) := by
    rw [← ha]
    exact (RingHom.congr_fun hcomm a).symm
  rw [hn, hjA] at hjn
  rw [map_mul]
  calc algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)
        (X.presheaf.germ U x hx a) *
      algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) ↑v⁻¹
      = b * algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) ↑v *
          algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) ↑v⁻¹ := by
        rw [hjn]
    _ = b := by
        rw [mul_assoc, ← map_mul, Units.mul_inv, map_one, mul_one]

/-! ### The core, read on the spread-out subalgebra -/

/-- **Lower properness of `𝒪_X + ℐ_x · f_*𝒪_{X'}` over an affine open around `x`.** Under the
hypothesis of `Stacks.GlueSquishFactor.exists_mem_map_primeIdealOf_notMem_range` the subalgebra
`𝒪_X + ℐ_x · f_*𝒪_{X'}` of `Stacks.GlueSquishFactor.idealSmulSubalg` — the very same subalgebra
whose *upper* properness is `Stacks.GlueSquishFactor.ne_top_obj_idealSmulSubalg` — has a section
over `U` which is not a section of `𝒪_X`.

The section is the one the core produces: it lies in `p_x · Γ(X', f⁻¹U)`, hence by
`Stacks.GlueSquishFactor.primeIdealOf_le_ideal_closedIdeal_singleton` and `Ideal.map_mono` in
`ℐ_x(U) · Γ(X', f⁻¹U)`, which is the generating set
`Stacks.GlueSquishFactor.idealSmulSet` of the subalgebra; `Ideal.smul_top_eq_map` identifies the
two spellings of that set and
`Stacks.AlgebraicGeometry.SubalgebraGeneratedByModule.mem_adjoinSubmodule_of_mem` puts a
generator in the subalgebra. -/
theorem exists_mem_obj_idealSmulSubalg_notMem_range {X' X : Scheme.{u}} (f : X' ⟶ X) [IsFinite f]
    [AlgebraSheaf.IsQuasicoherent (pushforwardAlgebra f)] {U : X.Opens} (hU : IsAffineOpen U)
    {x : X} (hx : x ∈ U) (hcl : IsClosed ({x} : Set X))
    (hb : letI : Algebra (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) :=
        ((TopCat.Presheaf.stalkFunctor CommRingCat.{u} x).map f.c).hom.toAlgebra
      ∃ b ∈ (IsLocalRing.maximalIdeal (X.presheaf.stalk x)).map
          (algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x)),
        ∀ a : X.presheaf.stalk x,
          algebraMap (X.presheaf.stalk x) ((f.base _* X'.presheaf).stalk x) a ≠ b) :
    ∃ s ∈ (idealSmulSubalg (pushforwardAlgebra f)
        (closedIdeal (⟨{x}, hcl⟩ : Closeds X))).obj U,
      s ∉ Set.range (f.app U).hom := by
  let := AlgebraSheaf.algebraSections (pushforwardAlgebra f) U
  let : Algebra Γ(X, U) Γ(X', f ⁻¹ᵁ U) := (f.app U).hom.toAlgebra
  obtain ⟨s, hs, hsnot⟩ := exists_mem_map_primeIdealOf_notMem_range f hU hx hb
  have hmap : s ∈ ((closedIdeal (⟨{x}, hcl⟩ : Closeds X)).ideal ⟨U, hU⟩).map
      (algebraMap Γ(X, U) Γ(X', f ⁻¹ᵁ U)) :=
    Ideal.map_mono (primeIdealOf_le_ideal_closedIdeal_singleton ⟨U, hU⟩ hx hcl) hs
  have h1 : s ∈ (closedIdeal (⟨{x}, hcl⟩ : Closeds X)).ideal ⟨U, hU⟩ •
      (⊤ : Submodule Γ(X, U) Γ(X', f ⁻¹ᵁ U)) := by
    rwa [Ideal.smul_top_eq_map]
  exact ⟨s, (mem_idealSmulSubalg_iff (pushforwardAlgebra f)
    (closedIdeal (⟨{x}, hcl⟩ : Closeds X)) ⟨U, hU⟩ s).mpr
      (mem_adjoinSubmodule_of_mem (pushforwardAlgebra f) h1), hsnot⟩

end Stacks.GlueSquishFactor

end
