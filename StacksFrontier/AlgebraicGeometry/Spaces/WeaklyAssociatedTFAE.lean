module

public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleLocalization.Henselization
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkLength
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartStalkTensorIsomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartZariskiStalkOrdinary
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.FlatEtaleLocalRing
public import StacksFrontier.AlgebraicGeometry.Spaces.NoetherianSpaces
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedAffinePushforward
public import StacksFrontier.AlgebraicGeometry.Spaces.WeaklyAssociatedPoints
public import StacksFrontier.RingTheory.Ideal.Annihilator.FlatBaseChange
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.WeaklyAssociated
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.FlatTensorProduct

/-!
# Weak and ordinary association at a geometric point of an algebraic space

Let `X` be an algebraic space over `S`, let `F` be an `𝒪_X`-module and let `x̄` be a geometric
point of `X`. The maximal ideal of the étale local ring `𝒪_{X, x̄}` is a weakly associated prime
of the geometric stalk `F_{x̄}` — minimal among the primes containing the annihilator of some
element — exactly when it is an associated prime of `F_{x̄}` — the annihilator of some element —
provided that maximal ideal is finitely generated, which it is when `X` is Noetherian. So on a
Noetherian algebraic space the weakly associated points of `F` are the points carrying a
geometric point at whose stalk the maximal ideal is an associated prime.

For a quasi-coherent `F` the weak-association condition is read off an étale scheme chart: if
`φ : U → X` is an étale neighbourhood of `x̄` with `U` a scheme, the Zariski stalk `(φ^*F)_u` has
`F_{x̄}` as its base change along the faithfully flat local map `𝒪_{U, u} → 𝒪_{X, x̄}`, which
carries the maximal ideal onto the maximal ideal, so weak association of the maximal ideal
passes from `U` to `X`; and it passes back, with no finiteness condition, because that map is
the strict henselization of `𝒪_{U, u}`, along which Stacks 0CTU descends weak association.

## Main results

* `AlgebraicGeometry.Space.isWeaklyAssociatedPrime_maximalIdeal_iff_isAssociatedPrimeStacks`:
  weak and ordinary association of the maximal ideal to the geometric stalk agree as soon as
  that maximal ideal is finitely generated.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_iff_exists_isAssociatedPrimeStacks` and
  `AlgebraicGeometry.Space.weaklyAssociatedPoints_eq_setOf_exists_isAssociatedPrimeStacks`:
  on a Noetherian algebraic space, weak association of a point is ordinary association of the
  maximal ideal to the geometric stalk at some geometric point above it.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPrime_maximalIdeal_geometricModuleStalk_of_chart`:
  **Stacks 0CTW, (1) ⟹ (3)**, and
  `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime`:
  **Stacks 0CTW, (3) ⟹ (1)**, for an arbitrary étale neighbourhood of `x̄`.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_iff` and
  `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_of_restrictToChart`:
  **Stacks 0CTW, conditions (1) and (2)**.
* `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_restrictToChart`
  and `AlgebraicGeometry.Space.isWeaklyAssociatedPoint_iff_exists_restrictToChart`: conditions
  (1) and (2) expressed through the weak association of Stacks 0CTX.

## Implementation notes

The conditions (4) and (5) of the source, which read *ordinary* association off a point of an
étale scheme chart, are not stated: their comparison with (1) and (2) is Stacks 05AR on the
chart together with local Noetherianity of the chart, which is not available here. Conditions
(1), (2) and (3) are, since the base-change formula `F_{x̄} = (φ^*F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}` of
Stacks 05VP is carried by
`AlgebraicGeometry.Space.isIso_chartStalkTensorComparison`, and the three properties of the
comparison map `𝒪_{U, u} → 𝒪_{X, x̄}` the transfer needs — flatness, locality, and the
generation of the maximal ideal of the target by that of the source — by
`AlgebraicGeometry.Space.flat_chartLocalRingToEtaleLocalRing`,
`AlgebraicGeometry.Space.isLocalHom_chartLocalRingToEtaleLocalRing` and
`AlgebraicGeometry.Space.map_maximalIdeal_chartLocalRingToEtaleLocalRing`.

Condition (1) is stated as the Zariski notion `Stacks.Divisors.IsWeaklyAssociatedPoint` of
Stacks 056L at the point `AlgebraicGeometry.Space.chartPoint` of the chart, applied to the
restriction `AlgebraicGeometry.Space.restrictToChart` of `F` to the chart's Zariski site; that
is the same thing as weak association of the maximal ideal of `𝒪_{U, u}` to
`AlgebraicGeometry.Space.chartZariskiModuleStalk`, which is the spelling the transfer works in,
and the two are matched by
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPrime`.
In that spelling two `𝒪_{U, u}`-module structures on the Zariski stalk are in scope — the one
of Stacks 01CB and the one `CategoryTheory.PresheafOfModules` carries — so the latter, which is
the one the Zariski notion is stated for, is pinned by hand.

The direction (3) ⟹ (1) is flat descent of weak association, proved below for a prime whose
contraction is finitely generated
(`Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_tensorProduct_of_fg`); the
contraction is the maximal ideal of `𝒪_{U, u}`, so the hypothesis is its finite generation, and
it holds whenever the chart is locally Noetherian. Unconditional descent along a strict
henselization is Stacks 0CTU, which is available as
`AlgebraicGeometry.weaklyAssociated_tfae_henselization`; it is stated for a quasi-coherent
`AlgebraicGeometry.Scheme.Modules`, and quasi-coherence of
`AlgebraicGeometry.Space.restrictToChart` is the hypothesis one then owes. The direction
(1) ⟹ (3) is unconditional.

The étale local ring is a local ring by
`AlgebraicGeometry.Space.isLocalRing_etaleLocalRing` and, on a Noetherian algebraic space, a
Noetherian ring by `AlgebraicGeometry.Space.isNoetherianRing_etaleLocalRing`; neither is an
instance, so both are supplied by hand, and the finite generation hypothesis of the first
result below therefore sits inside the scope of the `letI` providing the local ring structure.

The source asks only that `X` be locally Noetherian, whereas the Noetherianity of the étale
local ring is available here under the Noetherianity of Stacks 03EA, which also asks for quasi-
compactness and quasi-separatedness. The first result below is stated under the finite
generation of the maximal ideal alone, so it applies verbatim to any weaker hypothesis giving
that.

## References

* [Stacks Project, Lemma 71.2.1 (Tag 0CTW)](https://stacks.math.columbia.edu/tag/0CTW)
* [Stacks Project, Tag 056L](https://stacks.math.columbia.edu/tag/056L)
* [Stacks Project, Tag 058A](https://stacks.math.columbia.edu/tag/058A)
* [Stacks Project, Tag 04KF](https://stacks.math.columbia.edu/tag/04KF)
* [Stacks Project, Tag 05VP](https://stacks.math.columbia.edu/tag/05VP)
* [Stacks Project, Tag 08AH](https://stacks.math.columbia.edu/tag/08AH)
* [Stacks Project, Tag 0CTU](https://stacks.math.columbia.edu/tag/0CTU)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open scoped TensorProduct

universe u m

/-- For a finitely generated ideal, being the annihilator of an element of a module is the same
as being minimal among the primes containing the annihilator of an element. -/
private theorem isAssociatedPrimeStacks_iff_isWeaklyAssociatedPrime_of_fg {R : Type*}
    [CommRing R] {M : Type*} [AddCommGroup M] [Module R M] {p : Ideal R} (hp : p.FG) :
    IsAssociatedPrimeStacks R M p ↔ IsWeaklyAssociatedPrime R M p := by
  unfold IsAssociatedPrimeStacks IsWeaklyAssociatedPrime
  simpa only [Submodule.colon_span, Submodule.bot_colon', eq_comm] using
    ((isAssociatedPrime_tfae_of_fg (R := R) (M := M) hp).out 1 3)

/-- For a flat local extension carrying the maximal ideal onto the maximal ideal, weak
association of the maximal ideal is inherited by the base change: an element whose annihilator
has radical the maximal ideal is sent to one with the same property. -/
private theorem isWeaklyAssociatedPrime_maximalIdeal_tensorProduct_of_map_maximalIdeal
    {R T : Type*} [CommRing R] [IsLocalRing R] [CommRing T] [IsLocalRing T] [Algebra R T]
    [Module.Flat R T] {M : Type*} [AddCommGroup M] [Module R M]
    (hmax : Ideal.map (algebraMap R T) (IsLocalRing.maximalIdeal R) = IsLocalRing.maximalIdeal T)
    (h : IsWeaklyAssociatedPrime R M (IsLocalRing.maximalIdeal R)) :
    IsWeaklyAssociatedPrime T (T ⊗[R] M) (IsLocalRing.maximalIdeal T) := by
  change WeaklyAssociated (IsLocalRing.maximalIdeal R) M at h
  obtain ⟨m, hm⟩ :=
    (weaklyAssociated_maximalIdeal_iff_exists_radical_eq (S := R) (N := M)).mp h
  have hrad : (Ideal.torsionOf R M m).radical = IsLocalRing.maximalIdeal R := by
    simpa [annihilatorOfElem_semiring, Ideal.annihilator_span_singleton_eq_torsionOf] using hm
  refine (weaklyAssociated_maximalIdeal_iff_exists_radical_eq (S := T) (N := T ⊗[R] M)).mpr
    ⟨(1 : T) ⊗ₜ[R] m, ?_⟩
  rw [annihilatorOfElem_semiring, Ideal.annihilator_span_singleton_eq_torsionOf,
    ← ann_extension_eq_ann_baseChange_elem]
  refine le_antisymm ?_ ?_
  · calc
      (Ideal.map (algebraMap R T) (Ideal.torsionOf R M m)).radical ≤
          (Ideal.map (algebraMap R T) (IsLocalRing.maximalIdeal R)).radical :=
        Ideal.radical_mono (Ideal.map_mono
          ((Ideal.le_radical : Ideal.torsionOf R M m ≤ _).trans (le_of_eq hrad)))
      _ = IsLocalRing.maximalIdeal T := by
        rw [hmax, (IsLocalRing.maximalIdeal.isMaximal T).isPrime.radical]
  · rw [← hmax, ← hrad]
    exact Ideal.map_radical_le _

/-- Weak association of the maximal ideal to a base change is unchanged by an isomorphism of the
algebra base changed to: the two tensor products are matched by an additive isomorphism which is
semilinear along that isomorphism of rings. -/
private theorem isWeaklyAssociatedPrime_maximalIdeal_tensorProduct_congr_algEquiv
    {R A C : Type*} [CommRing R] [CommRing A] [IsLocalRing A] [CommRing C] [IsLocalRing C]
    [Algebra R A] [Algebra R C] {M : Type*} [AddCommGroup M] [Module R M] (e : A ≃ₐ[R] C) :
    IsWeaklyAssociatedPrime A (TensorProduct R A M) (IsLocalRing.maximalIdeal A) ↔
      IsWeaklyAssociatedPrime C (TensorProduct R C M) (IsLocalRing.maximalIdeal C) := by
  refine isWeaklyAssociatedPrime_maximalIdeal_congr_semilinearEquiv e.toRingEquiv
    (TensorProduct.congr e.toLinearEquiv (LinearEquiv.refl R M)).toAddEquiv ?_
  intro a z
  induction z using TensorProduct.inductionOn with
  | tmul b m => simp [TensorProduct.smul_tmul']
  | add z z' hz hz' => simp only [smul_add, map_add, hz, hz']

/-- **Stacks 0CTU at a chosen henselization tower.** For a quasi-coherent module on a scheme,
weak association at a point is weak association of the maximal ideal of the strict henselization
of the stalk to the base change of the stalk along it.

`AlgebraicGeometry.weaklyAssociated_tfae_henselization` takes the strict henselization to be any
ring whose residue field is a prescribed separable closure of the residue field of the stalk,
whereas `IsLocalRing.HenselizationTower` prescribes instead an isomorphism of its residue field
with a chosen separable closure; the residue extension and the separable closure of the former
are built here from that isomorphism. -/
private theorem isWeaklyAssociatedPoint_iff_isWeaklyAssociatedPrime_strictHenselization
    {Y : AlgebraicGeometry.Scheme.{u}} (G : Y.Modules) [G.IsQuasicoherent] (y : Y)
    {L : Type*} [Field L] [Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk y)) L]
    [IsSepClosure (IsLocalRing.ResidueField (Y.presheaf.stalk y)) L]
    (T : IsLocalRing.HenselizationTower (Y.presheaf.stalk y) L) :
    letI : Module (Y.presheaf.stalk y)
        (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf y) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val y
    Stacks.Divisors.IsWeaklyAssociatedPoint G y ↔
      IsWeaklyAssociatedPrime T.strictHenselization
        (TensorProduct (Y.presheaf.stalk y) T.strictHenselization
          (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf y))
        (IsLocalRing.maximalIdeal T.strictHenselization) := by
  let : Module (Y.presheaf.stalk y)
      (TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf y) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier G.val y
  let : Algebra (IsLocalRing.ResidueField (Y.presheaf.stalk y))
      (IsLocalRing.ResidueField T.strictHenselization) :=
    (T.strictHenselizationResidueEquiv.toRingHom.comp
      (algebraMap (IsLocalRing.ResidueField (Y.presheaf.stalk y)) L)).toAlgebra
  let eres : L ≃ₐ[IsLocalRing.ResidueField (Y.presheaf.stalk y)]
      IsLocalRing.ResidueField T.strictHenselization :=
    { T.strictHenselizationResidueEquiv with commutes' := fun _ => rfl }
  have : IsSepClosed L :=
    IsSepClosure.sep_closed (IsLocalRing.ResidueField (Y.presheaf.stalk y))
  have : IsSepClosed (IsLocalRing.ResidueField T.strictHenselization) :=
    IsSepClosed.of_ringEquiv T.strictHenselizationResidueEquiv.symm
  have : IsSepClosure (IsLocalRing.ResidueField (Y.presheaf.stalk y))
      (IsLocalRing.ResidueField T.strictHenselization) :=
    ⟨inferInstance, AlgEquiv.Algebra.isSeparable eres⟩
  let : IsLocalRing.IsHenselization (Y.presheaf.stalk y)
      (IsLocalRing.ResidueField T.strictHenselization) T.strictHenselization :=
    { henselian := IsLocalRing.IsHenselization.henselian
        (R := (Y.presheaf.stalk y : Type u)) (L := L)
      ind_etale := IsLocalRing.IsHenselization.ind_etale
        (R := (Y.presheaf.stalk y : Type u)) (L := L)
      exists_residueFieldEquiv :=
        ⟨RingEquiv.refl _, T.strictHenselizationResidueEquiv_residue⟩ }
  exact (AlgebraicGeometry.weaklyAssociated_tfae_henselization
    (Rh := T.henselization) (Rsh := T.strictHenselization) G y).out 1 4

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (X : AlgebraicSpaces B S hS)

/-- **Stacks 0CTW, (3) ⟺ (6).** Let `F` be an `𝒪_X`-module on an algebraic space and `x̄` a
geometric point of `X` at which the maximal ideal of `𝒪_{X, x̄}` is finitely generated. That
maximal ideal is a weakly associated prime of the geometric stalk `F_{x̄}` if and only if it is
an associated prime of `F_{x̄}`. -/
@[stacks 0CTW "conditions (3) and (6) at a geometric point"]
theorem isWeaklyAssociatedPrime_maximalIdeal_iff_isAssociatedPrimeStacks
    (F : Modules.{u, m} B S hS X.1 X.2) (xbar : GeometricPoint B S hS X.1) :
    letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
      isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
    letI : Module (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F) :=
      (geometricModuleStalk B S hS X xbar F).isModule
    (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar)).FG →
      (IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 xbar)
          (geometricModuleStalk B S hS X xbar F)
          (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar)) ↔
        IsAssociatedPrimeStacks (etaleLocalRing B S hS X.1 xbar)
          (geometricModuleStalk B S hS X xbar F)
          (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar))) :=
  fun hfg => (isAssociatedPrimeStacks_iff_isWeaklyAssociatedPrime_of_fg hfg).symm

/-- **Stacks 0CTW, (3) ⟺ (6)** on a Noetherian algebraic space: a point is weakly associated to
an `𝒪_X`-module exactly when, at some geometric point above it, the maximal ideal of the étale
local ring is an associated prime of the geometric stalk. -/
@[stacks 0CTW "conditions (3) and (6) on a Noetherian algebraic space"]
theorem isWeaklyAssociatedPoint_iff_exists_isAssociatedPrimeStacks
    (hZ : B.Contains (⊤_ Scheme.{u})) (hNoetherian : IsNoetherian B S hS hZ X.1)
    (F : Modules.{u, m} B S hS X.1 X.2) (x : points B S hS X.1) :
    IsWeaklyAssociatedPoint B S hS X F x ↔
      ∃ xbar : GeometricPoint B S hS X.1, xbar.LiesOver x ∧
        letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
          isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
        letI : Module (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F) :=
          (geometricModuleStalk B S hS X xbar F).isModule
        IsAssociatedPrimeStacks (etaleLocalRing B S hS X.1 xbar)
          (geometricModuleStalk B S hS X xbar F)
          (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar)) := by
  refine exists_congr fun xbar => and_congr_right fun _ => ?_
  have : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  have : IsNoetherianRing (etaleLocalRing B S hS X.1 xbar) :=
    isNoetherianRing_etaleLocalRing B S hS hZ X.1 X.2 hNoetherian xbar
  exact isWeaklyAssociatedPrime_maximalIdeal_iff_isAssociatedPrimeStacks B S hS X F xbar
    (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar)).fg_of_isNoetherianRing

/-- **Stacks 0CTW, (3) ⟺ (6)** on a Noetherian algebraic space, as an equality of sets of
points: `WeakAss(F)` is the set of points carrying a geometric point at whose stalk the maximal
ideal of the étale local ring is an associated prime. -/
@[stacks 0CTW "conditions (3) and (6) as a set of points"]
theorem weaklyAssociatedPoints_eq_setOf_exists_isAssociatedPrimeStacks
    (hZ : B.Contains (⊤_ Scheme.{u})) (hNoetherian : IsNoetherian B S hS hZ X.1)
    (F : Modules.{u, m} B S hS X.1 X.2) :
    weaklyAssociatedPoints B S hS X F =
      {x : points B S hS X.1 | ∃ xbar : GeometricPoint B S hS X.1, xbar.LiesOver x ∧
        letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
          isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
        letI : Module (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F) :=
          (geometricModuleStalk B S hS X xbar F).isModule
        IsAssociatedPrimeStacks (etaleLocalRing B S hS X.1 xbar)
          (geometricModuleStalk B S hS X xbar F)
          (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar))} :=
  Set.ext fun x =>
    isWeaklyAssociatedPoint_iff_exists_isAssociatedPrimeStacks B S hS X hZ hNoetherian F x

/-! ### Conditions (1) and (2): weak association read on an étale scheme chart -/

/-- Condition (1) of the source — the point `u` of the chart is weakly associated to `φ^*F` in
the Zariski sense of Stacks 056L — is weak association of the maximal ideal of `𝒪_{U, u}` to the
Zariski stalk `(φ^*F)_u`, the left-hand factor of the base-change formula of Stacks 05VP. -/
theorem isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPrime
    {xbar : GeometricPoint B S hS X.1} (V : SmallEtaleNeighborhood xbar)
    (F : Modules.{u, u} B S hS X.1 X.2) :
    Stacks.Divisors.IsWeaklyAssociatedPoint (restrictToChart B S hS X.2 F V.chart)
        (chartPoint B S hS X.1 V) ↔
      IsWeaklyAssociatedPrime (chartLocalRing B S hS X.1 V)
        (chartZariskiModuleStalk B S hS X.1 X.2 V F)
        (IsLocalRing.maximalIdeal (chartLocalRing B S hS X.1 V)) := by
  let _ : Module (chartLocalRing B S hS X.1 V)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (chartRestrictionPresheafOfModules B S hS X.2 V F).presheaf
        (chartPoint B S hS X.1 V)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (chartRestrictionPresheafOfModules B S hS X.2 V F) (chartPoint B S hS X.1 V)
  exact ⟨IsWeaklyAssociatedPrime.of_linearEquiv
      (chartZariskiModuleStalkStalkEquiv B S hS X.2 V F).symm,
    IsWeaklyAssociatedPrime.of_linearEquiv (chartZariskiModuleStalkStalkEquiv B S hS X.2 V F)⟩

/-- **Stacks 0CTW, (1) ⟹ (3).** Let `F` be a quasi-coherent `𝒪_X`-module and let
`φ : (U, ū) → (X, x̄)` be an étale neighbourhood of a geometric point `x̄` whose chart `U` is a
scheme. If `u` is weakly associated to `φ^*F`, then the maximal ideal of `𝒪_{X, x̄}` is a weakly
associated prime of the geometric stalk `F_{x̄}`.

By Stacks 05VP the geometric stalk is `(φ^*F)_u ⊗_{𝒪_{U, u}} 𝒪_{X, x̄}` and the comparison map
is flat and carries the maximal ideal of `𝒪_{U, u}` onto that of `𝒪_{X, x̄}`. -/
@[stacks 0CTW "condition (1) implies condition (3) at a geometric point"]
theorem isWeaklyAssociatedPrime_maximalIdeal_geometricModuleStalk_of_chart
    {xbar : GeometricPoint B S hS X.1} (V : SmallEtaleNeighborhood xbar)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (h : Stacks.Divisors.IsWeaklyAssociatedPoint (restrictToChart B S hS X.2 F V.chart)
      (chartPoint B S hS X.1 V)) :
    letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
      isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
    letI : Module (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F) :=
      (geometricModuleStalk B S hS X xbar F).isModule
    IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 xbar)
      (geometricModuleStalk B S hS X xbar F)
      (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar)) := by
  have : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  let _ : Algebra (chartLocalRing B S hS X.1 V) (etaleLocalRing B S hS X.1 xbar) :=
    (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 V).toAlgebra
  have _ : Module.Flat (chartLocalRing B S hS X.1 V) (etaleLocalRing B S hS X.1 xbar) :=
    flat_chartLocalRingToEtaleLocalRing B S hS X.1 X.2 V
  have hmax : Ideal.map (algebraMap (chartLocalRing B S hS X.1 V)
        (etaleLocalRing B S hS X.1 xbar))
      (IsLocalRing.maximalIdeal (chartLocalRing B S hS X.1 V)) =
      IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar) :=
    map_maximalIdeal_chartLocalRingToEtaleLocalRing B S hS X.1 X.2 V
  have _ := isIso_chartStalkTensorComparison B S hS X.2 V F
  exact IsWeaklyAssociatedPrime.of_linearEquiv
    (asIso (chartStalkTensorComparison B S hS X.2 V F)).toLinearEquiv
    (isWeaklyAssociatedPrime_maximalIdeal_tensorProduct_of_map_maximalIdeal hmax
      ((isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPrime
        B S hS X V F).mp h))

/-- **Stacks 0CTW, (3) ⟹ (1).** Let `F` be a quasi-coherent `𝒪_X`-module and let
`φ : (U, ū) → (X, x̄)` be an étale neighbourhood of a geometric point `x̄` whose chart `U` is a
scheme. If the maximal ideal of `𝒪_{X, x̄}` is a weakly associated prime of `F_{x̄}` then `u` is
weakly associated to `φ^*F`.

This is the descent of weak association from a strict henselization, Stacks 0CTU: the étale
local ring at `x̄` is the strict henselization of `𝒪_{U, u}` chosen in
`AlgebraicGeometry.Space.chartHenselizationTower` by Stacks 04KF, and the geometric stalk is the
base change of the Zariski stalk `(φ^*F)_u` along it by Stacks 05VP. -/
@[stacks 0CTW "condition (3) implies condition (1) at an étale neighbourhood"]
theorem isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime
    {xbar : GeometricPoint B S hS X.1} (V : SmallEtaleNeighborhood xbar)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (h : letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
          isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
        letI : Module (etaleLocalRing B S hS X.1 xbar)
            (geometricModuleStalk B S hS X xbar F) :=
          (geometricModuleStalk B S hS X xbar F).isModule
        IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 xbar)
          (geometricModuleStalk B S hS X xbar F)
          (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar))) :
    Stacks.Divisors.IsWeaklyAssociatedPoint (restrictToChart B S hS X.2 F V.chart)
      (chartPoint B S hS X.1 V) := by
  have : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  let _ : Algebra (chartLocalRing B S hS X.1 V) (etaleLocalRing B S hS X.1 xbar) :=
    (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 V).toAlgebra
  have _ := isIso_chartStalkTensorComparison B S hS X.2 V F
  have h2 : IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 xbar)
      (chartStalkTensorEtaleLocalRing B S hS X.1 X.2 V F)
      (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar)) :=
    IsWeaklyAssociatedPrime.of_linearEquiv
      (asIso (chartStalkTensorComparison B S hS X.2 V F)).toLinearEquiv.symm h
  let eR : (chartHenselizationTower B S hS X.1 V).strictHenselization ≃ₐ[
      chartLocalRing B S hS X.1 V] (etaleLocalRing B S hS X.1 xbar) :=
    { chartStrictHenselizationEquiv B S hS X.1 X.2 V with commutes' := fun _ => rfl }
  have h3 : IsWeaklyAssociatedPrime (chartHenselizationTower B S hS X.1 V).strictHenselization
      (TensorProduct (chartLocalRing B S hS X.1 V)
        (chartHenselizationTower B S hS X.1 V).strictHenselization
        (chartZariskiModuleStalk B S hS X.1 X.2 V F))
      (IsLocalRing.maximalIdeal
        (chartHenselizationTower B S hS X.1 V).strictHenselization) :=
    (isWeaklyAssociatedPrime_maximalIdeal_tensorProduct_congr_algEquiv eR).mpr h2
  have _ : (restrictToChart B S hS X.2 F V.chart).IsQuasicoherent :=
    isQuasicoherent_restrictToChart B S hS X F ‹_› V.chart
  let : Module (chartLocalRing B S hS X.1 V)
      (TopCat.Presheaf.stalk (C := AddCommGrpCat.{u})
        (chartRestrictionPresheafOfModules B S hS X.2 V F).presheaf
        (chartPoint B S hS X.1 V)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (chartRestrictionPresheafOfModules B S hS X.2 V F) (chartPoint B S hS X.1 V)
  exact (isWeaklyAssociatedPoint_iff_isWeaklyAssociatedPrime_strictHenselization
    (Y := chartScheme V.chart) (restrictToChart B S hS X.2 F V.chart)
    (chartPoint B S hS X.1 V) (chartHenselizationTower B S hS X.1 V)).mpr
    (IsWeaklyAssociatedPrime.of_linearEquiv
      (LinearEquiv.baseChange (chartLocalRing B S hS X.1 V)
        (chartHenselizationTower B S hS X.1 V).strictHenselization _ _
        (chartZariskiModuleStalkStalkEquiv B S hS X.2 V F)) h3)

/-- **Stacks 0CTW, (3) ⟹ (1), by flat descent over finitely many weakly associated primes.**
The conclusion of
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime`,
reached instead by flat descent of weak association along the comparison map of Stacks 05VP,
under finiteness of the set of weakly associated primes of the Zariski module stalk of the
chart.

`Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_tensorProduct`, used here, turns
the covering of the maximal ideal by the weakly associated primes of the localization into an
equality by prime avoidance over finitely many primes. That is not the source's own route:
Stacks 0CTW proves (1), (2) and (3) equivalent with nothing beyond quasi-coherence, by
More on Flatness, Lemma 38.2.9, which is Tag 0CTU, and which
`AlgebraicGeometry.Space.isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime`
above now takes. This form is retained as the one a local finiteness statement about the weakly
associated points of the chart discharges directly, since the primes of the local ring at a
point all lie in every neighbourhood of it. -/
@[stacks 0CTW "condition (3) implies condition (1) at a chart whose Zariski module stalk has
finitely many weakly associated primes"]
theorem isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime_of_finite
    {xbar : GeometricPoint B S hS X.1} (V : SmallEtaleNeighborhood xbar)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hfin : (weaklyAssociatedPrimes (chartLocalRing B S hS X.1 V)
      (chartZariskiModuleStalk B S hS X.1 X.2 V F)).Finite)
    (h : letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
          isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
        letI : Module (etaleLocalRing B S hS X.1 xbar)
            (geometricModuleStalk B S hS X xbar F) :=
          (geometricModuleStalk B S hS X xbar F).isModule
        IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 xbar)
          (geometricModuleStalk B S hS X xbar F)
          (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar))) :
    Stacks.Divisors.IsWeaklyAssociatedPoint (restrictToChart B S hS X.2 F V.chart)
      (chartPoint B S hS X.1 V) := by
  have : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
    isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
  let _ : Algebra (chartLocalRing B S hS X.1 V) (etaleLocalRing B S hS X.1 xbar) :=
    (chartLocalRingToEtaleLocalRing B S hS X.1 X.2 V).toAlgebra
  have _ : Module.Flat (chartLocalRing B S hS X.1 V) (etaleLocalRing B S hS X.1 xbar) :=
    flat_chartLocalRingToEtaleLocalRing B S hS X.1 X.2 V
  have _ : IsLocalHom (algebraMap (chartLocalRing B S hS X.1 V)
      (etaleLocalRing B S hS X.1 xbar)) :=
    isLocalHom_chartLocalRingToEtaleLocalRing B S hS X.1 X.2 V
  have _ := isIso_chartStalkTensorComparison B S hS X.2 V F
  have h2 : IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 xbar)
      (chartStalkTensorEtaleLocalRing B S hS X.1 X.2 V F)
      (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar)) :=
    IsWeaklyAssociatedPrime.of_linearEquiv
      (asIso (chartStalkTensorComparison B S hS X.2 V F)).toLinearEquiv.symm h
  have h3 := Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_tensorProduct
    (R := chartLocalRing B S hS X.1 V) (S := etaleLocalRing B S hS X.1 xbar)
    (N := etaleLocalRing B S hS X.1 xbar)
    (M := chartZariskiModuleStalk B S hS X.1 X.2 V F) hfin h2
  rw [IsLocalRing.maximalIdeal_comap] at h3
  exact (isWeaklyAssociatedPoint_restrictToChart_iff_isWeaklyAssociatedPrime
    B S hS X V F).mpr h3

/-- **Stacks 0CTW, (1) ⟺ (3)** at an étale neighbourhood: the point `u` of the chart is weakly
associated to `φ^*F` exactly when the maximal ideal of `𝒪_{X, x̄}` is a weakly associated prime
of `F_{x̄}`. -/
@[stacks 0CTW "conditions (1) and (3) at an étale neighbourhood"]
theorem isWeaklyAssociatedPoint_restrictToChart_iff
    {xbar : GeometricPoint B S hS X.1} (V : SmallEtaleNeighborhood xbar)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] :
    Stacks.Divisors.IsWeaklyAssociatedPoint (restrictToChart B S hS X.2 F V.chart)
        (chartPoint B S hS X.1 V) ↔
      letI : IsLocalRing (etaleLocalRing B S hS X.1 xbar) :=
        isLocalRing_etaleLocalRing B S hS X.1 X.2 xbar
      letI : Module (etaleLocalRing B S hS X.1 xbar) (geometricModuleStalk B S hS X xbar F) :=
        (geometricModuleStalk B S hS X xbar F).isModule
      IsWeaklyAssociatedPrime (etaleLocalRing B S hS X.1 xbar)
        (geometricModuleStalk B S hS X xbar F)
        (IsLocalRing.maximalIdeal (etaleLocalRing B S hS X.1 xbar)) :=
  ⟨isWeaklyAssociatedPrime_maximalIdeal_geometricModuleStalk_of_chart B S hS X V F,
    isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime B S hS X V F⟩

/-- **Stacks 0CTW, (1) ⟹ (3) in the form of Stacks 0CTX.** If the point `u` of an étale scheme
chart is weakly associated to `φ^*F` then the point of `X` it lies over is weakly associated
to `F`. -/
@[stacks 0CTW "condition (1) implies the weak association of Stacks 0CTX"]
theorem isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_restrictToChart
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (x : points B S hS X.1)
    {xbar : GeometricPoint B S hS X.1} (hxbar : xbar.LiesOver x)
    (V : SmallEtaleNeighborhood xbar)
    (h : Stacks.Divisors.IsWeaklyAssociatedPoint (restrictToChart B S hS X.2 F V.chart)
      (chartPoint B S hS X.1 V)) :
    IsWeaklyAssociatedPoint B S hS X F x :=
  ⟨xbar, hxbar,
    isWeaklyAssociatedPrime_maximalIdeal_geometricModuleStalk_of_chart B S hS X V F h⟩

/-- **Stacks 0CTW, conditions (1) and (2).** Weak association at a chart point does not depend
on the chart: if the point of one étale scheme chart of `x̄` is weakly associated to the
restriction of `F` there, so is the point of any other. -/
@[stacks 0CTW "conditions (1) and (2) for the étale neighbourhoods of a geometric point"]
theorem isWeaklyAssociatedPoint_restrictToChart_of_restrictToChart
    {xbar : GeometricPoint B S hS X.1} (V V' : SmallEtaleNeighborhood xbar)
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (h : Stacks.Divisors.IsWeaklyAssociatedPoint (restrictToChart B S hS X.2 F V.chart)
      (chartPoint B S hS X.1 V)) :
    Stacks.Divisors.IsWeaklyAssociatedPoint (restrictToChart B S hS X.2 F V'.chart)
      (chartPoint B S hS X.1 V') :=
  isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime B S hS X V' F
    (isWeaklyAssociatedPrime_maximalIdeal_geometricModuleStalk_of_chart B S hS X V F h)

/-- **Stacks 0CTW, conditions (1) and (2) in the form of Stacks 0CTX.** A point of `X` is weakly
associated to a quasi-coherent `F` exactly when, at some geometric point above it, the
corresponding point of some étale scheme chart is weakly associated to the restriction of `F`
there. -/
@[stacks 0CTW "conditions (1) and (2) as the weak association of Stacks 0CTX"]
theorem isWeaklyAssociatedPoint_iff_exists_restrictToChart
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite] (x : points B S hS X.1) :
    IsWeaklyAssociatedPoint B S hS X F x ↔
      ∃ (xbar : GeometricPoint B S hS X.1), xbar.LiesOver x ∧
        ∃ V : SmallEtaleNeighborhood xbar,
          Stacks.Divisors.IsWeaklyAssociatedPoint (restrictToChart B S hS X.2 F V.chart)
            (chartPoint B S hS X.1 V) := by
  refine ⟨fun ⟨xbar, hxbar, h3⟩ => ?_, fun ⟨_, hxbar, V, h1⟩ =>
    isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_restrictToChart B S hS X F x hxbar V h1⟩
  obtain ⟨V⟩ := nonempty_smallEtaleNeighborhood X.2 xbar
  exact ⟨xbar, hxbar, V,
    isWeaklyAssociatedPoint_restrictToChart_of_isWeaklyAssociatedPrime B S hS X V F h3⟩

end AlgebraicGeometry.Space

end
