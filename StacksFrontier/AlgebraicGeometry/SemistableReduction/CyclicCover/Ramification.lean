module

public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.SpecialFibre
public import Mathlib.AlgebraicGeometry.ValuativeCriterion
public import StacksFrontier.AlgebraicGeometry.SemistableReduction.CyclicCover.BaseChange
public import StacksFrontier.AlgebraicGeometry.Curves.NodalFamilySection
public import StacksFrontier.AlgebraicGeometry.Models.Basic
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne
public import StacksFrontier.RingTheory.MvPowerSeries.AdicTopology
public import StacksFrontier.RingTheory.Henselian.IntegralDomain
public import StacksFrontier.RingTheory.Henselian.StrictHenselization.QuasiFinite
public import StacksFrontier.RingTheory.DiscreteValuationRing.HenselianIntegralClosure
public import Mathlib.RingTheory.LaurentSeries
public import StacksCore.Tactic.StacksAttribute

/-!
# Points of the cyclic cover over discrete valuation rings

Let `X ⟶ Z_R` be the cyclic cover `Spec_{Z_R}(Sym(L_R)/(φ - π))` over `R = k[[π]]` of
[Stacks, Tag 0CEH]. On each chart `π = g xⁿ` with `g` a unit. Hence for a discrete valuation ring
`R'` with a map `j : R → R'`, every morphism `Spec R' ⟶ X` over `Spec R` forces the valuation of
`j(π)` to be divisible by `n`. Since `X ⟶ Spec R` is proper, the same holds for every point of
the generic fibre over the fraction field of `R'`, by the valuative criterion.

## Main results

* `Stacks.CyclicCover.isProper_coverSnd`: `X ⟶ Spec R` is proper when `Z` is proper over `k`.
* `Stacks.CyclicCover.exists_addVal_eq_mul_of_lift`: an `R'`-point of `X` gives `n ∣ v(j π)`.
* `Stacks.CyclicCover.exists_addVal_eq_mul_of_point`: a `K'`-point of `X` over `Spec R` gives
  `n ∣ v(j π)`.

## References

* [Stacks Project, Tag 0CEH](https://stacks.math.columbia.edu/tag/0CEH)
-/

@[expose] public noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite TopologicalSpace Polynomial
open scoped TensorProduct

universe u

namespace Stacks.CyclicCover

variable {k : Type u} [Field k] {Z : Scheme.{u}} (f : Z ⟶ Spec (.of k)) {L : Z.Modules}
  [SheafOfModules.IsInvertible Z.sheaf.obj Z.ringCatSheaf.property L] {n : ℕ}
  (φ : (situation f L).symmetricAlgebra.piece (n : ℤ) ≅ SheafOfModules.unit Z.ringCatSheaf)

/-- **`X ⟶ Spec R` is proper**: it is the finite `p : X ⟶ Z_R` followed by the base change
`Z_R ⟶ Spec R` of the proper `Z ⟶ Spec k`. -/
theorem isProper_coverSnd [IsProper f] (hn : n ≠ 0) :
    IsProper (coverSnd f φ (PowerSeries k) PowerSeries.X) := by
  have := isFinite_coverMap f φ (PowerSeries k) PowerSeries.X hn
  have h : coverSnd f φ (PowerSeries k) PowerSeries.X =
      coverMap f φ (PowerSeries k) PowerSeries.X ≫ baseChangeSnd f (PowerSeries k) :=
    (coverMap_snd f φ (PowerSeries k) PowerSeries.X).symm
  rw [h]
  infer_instance


/-- **A point of `X` over a discrete valuation ring `R'` over `R = k[[π]]` meets the special
fibre with multiplicity divisible by `n`**: if `j : R → R'` and `Spec R' ⟶ X` lies over `Spec R`,
then the valuation of `j(π)` is divisible by `n`, because on a chart `π = g xⁿ` with `g` a unit. -/
theorem exists_addVal_eq_mul_of_lift (R' : Type u) [CommRing R'] [IsDomain R']
    [IsDiscreteValuationRing R'] (hn : n ≠ 0) (j : PowerSeries k →+* R')
    (hj : j PowerSeries.X ≠ 0)
    (l : Spec (.of R') ⟶ coverR f φ)
    (hl : l ≫ coverSnd f φ (PowerSeries k) PowerSeries.X = Spec.map (CommRingCat.ofHom j)) :
    ∃ m : ℕ, IsDiscreteValuationRing.addVal R' (j PowerSeries.X) = (n * m : ℕ) := by
  -- the closed point of `Spec R'` lies in a chart
  obtain ⟨⟨U, ⟨b⟩⟩, hx⟩ := exists_mem_coverOpen f φ (l (IsLocalRing.closedPoint R'))
  let := (sectionsStructure f U.1).hom.toAlgebra
  set W := coverOpen f φ U (PowerSeries k) PowerSeries.X
  have hrange : Set.range l ⊆ (W : Set (coverR f φ)) := by
    rintro _ ⟨y, rfl⟩
    exact ((IsLocalRing.specializes_closedPoint y).map l.continuous).mem_open W.isOpen hx
  let l' : Spec (.of R') ⟶ W.toScheme :=
    IsOpenImmersion.lift W.ι l (by rw [Scheme.Opens.range_ι]; exact hrange)
  have hl' : l' ≫ W.ι = l := IsOpenImmersion.lift_fac _ _ _
  let ρ := Spec.preimage (l' ≫ (coverOpenIso f φ U b (PowerSeries k) PowerSeries.X).hom)
  have hρ : Spec.map ρ = l' ≫ (coverOpenIso f φ U b (PowerSeries k) PowerSeries.X).hom :=
    Spec.map_preimage _
  have hcomp : CommRingCat.ofHom (chartRight k n (chartCoeff f φ U b) PowerSeries.X) ≫ ρ =
      CommRingCat.ofHom j := by
    apply Spec.map_injective
    rw [Spec.map_comp, hρ, Category.assoc, coverOpenIso,
      IsPullback.isoIsPullback_hom_snd, ← Category.assoc, hl', hl]
  have hX : ρ.hom (chartRight k n (chartCoeff f φ U b) PowerSeries.X PowerSeries.X) =
      j PowerSeries.X := by
    simpa using ConcreteCategory.congr_hom hcomp PowerSeries.X
  rw [chartRight_eq_mul_root_pow (rootCoeff_mul_chartCoeff f φ U b), map_mul, map_pow] at hX
  have hu : IsUnit (ρ.hom (algebraMap (Γ(Z, U.1) ⊗[k] PowerSeries k) _
      (rootCoeff f φ U b ⊗ₜ 1))) :=
    (((IsUnit.of_mul_eq_one _ (rootCoeff_mul_chartCoeff f φ U b)).map
      Algebra.TensorProduct.includeLeftRingHom).map _).map _
  have hr : ρ.hom (AdjoinRoot.root _) ≠ 0 := by
    intro h0; apply hj; rw [← hX, h0, zero_pow hn, mul_zero]
  obtain ⟨m, hm⟩ : ∃ m : ℕ, IsDiscreteValuationRing.addVal R' (ρ.hom (AdjoinRoot.root _)) = m :=
    ENat.ne_top_iff_exists.1 (by rwa [Ne, IsDiscreteValuationRing.addVal_eq_top_iff])
      |>.imp fun _ h => h.symm
  refine ⟨m, ?_⟩
  have h0 : IsDiscreteValuationRing.addVal R' (ρ.hom (algebraMap (Γ(Z, U.1) ⊗[k] PowerSeries k)
      _ (rootCoeff f φ U b ⊗ₜ 1))) = 0 := by
    obtain ⟨v, hv⟩ := hu
    rw [← hv]
    exact IsDiscreteValuationRing.addVal_eq_zero_of_unit (R := R') v
  rw [← hX, IsDiscreteValuationRing.addVal_mul, IsDiscreteValuationRing.addVal_pow, hm, h0,
    zero_add]
  simp


/-- **A point of the generic fibre over the fraction field of a discrete valuation ring `R'`
over `R`** forces `n ∣ v_{R'}(π)`: by the valuative criterion of properness the point extends to
`Spec R' ⟶ X`, to which `Stacks.CyclicCover.exists_addVal_eq_mul_of_lift` applies. -/
theorem exists_addVal_eq_mul_of_point [IsProper f] (hn : n ≠ 0) (R' : Type u) [CommRing R']
    [IsDomain R'] [IsDiscreteValuationRing R'] (K' : Type u) [Field K'] [Algebra R' K']
    [IsFractionRing R' K'] (j : PowerSeries k →+* R') (hj : j PowerSeries.X ≠ 0)
    (a : Spec (.of K') ⟶ coverR f φ)
    (ha : a ≫ coverSnd f φ (PowerSeries k) PowerSeries.X =
      Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ Spec.map (CommRingCat.ofHom j)) :
    ∃ m : ℕ, IsDiscreteValuationRing.addVal R' (j PowerSeries.X) = (n * m : ℕ) := by
  have hp := isProper_coverSnd f φ hn
  rw [IsProper.eq_valuativeCriterion] at hp
  obtain ⟨⟨l⟩⟩ := hp.1.1.1.existence ⟨R', K', a, Spec.map (CommRingCat.ofHom j), ⟨ha⟩⟩
  exact exists_addVal_eq_mul_of_lift f φ R' hn j hj l.l l.fac_right


/-- The cyclic cover over a nonzero `k`-algebra is nonempty when `Z` is: `Z_S ⟶ Z` and
`p : X_S ⟶ Z_S` are surjective. -/
theorem nonempty_cover [Nonempty Z] (hn : n ≠ 0) (S : Type u) [CommRing S] [Algebra k S]
    [Nontrivial S] (c : S) : Nonempty (cover f φ S c) := by
  obtain ⟨z⟩ := ‹Nonempty Z›
  have : Surjective (baseChangeFst f S) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback f (Spec.map (CommRingCat.ofHom (algebraMap k S)))).flip
      inferInstance
  obtain ⟨w, -⟩ := (baseChangeFst f S).surjective z
  have := surjective_coverMap f φ S c hn
  obtain ⟨x, -⟩ := (coverMap f φ S c).surjective w
  exact ⟨x⟩

/-- **A proper semistable model of the curve over `K'` forces `n ∣ v_{R'}(π)`.** Let `R'` be a
henselian discrete valuation ring with separably closed residue field and fraction field `K'`, and
`j : R → R'` with `j(π) ≠ 0`. If `X_{K'} = X ×_{Spec R} Spec K'` is the generic fibre of a proper
flat model `Y ⟶ Spec R'` which is at-worst-nodal of relative dimension one, then `Y` has a section
(`AlgebraicGeometry.exists_section_of_nodal`), hence `X_{K'}` a `K'`-point, and
`Stacks.CyclicCover.exists_addVal_eq_mul_of_point` applies. -/
theorem exists_addVal_eq_mul_of_nodal_model [IsProper f] [Nonempty Z] (hn : n ≠ 0)
    (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R'] [HenselianLocalRing R']
    [IsSepClosed (IsLocalRing.ResidueField R')] (K' : Type u) [Field K'] [Algebra R' K']
    [IsFractionRing R' K'] (j : PowerSeries k →+* R') (hj : j PowerSeries.X ≠ 0)
    (j' : PowerSeries k →+* K') (hj' : (algebraMap R' K').comp j = j')
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R'))
    (e : pullback (coverSnd f φ (PowerSeries k) PowerSeries.X) (Spec.map (CommRingCat.ofHom j')) ≅
      pullback q (Spec.map (CommRingCat.ofHom (algebraMap R' K'))))
    (he : e.hom ≫ pullback.snd _ _ = pullback.snd _ _) [Flat q] [IsProper q]
    (hq : IsAtWorstNodalOfRelativeDimensionOne q) :
    ∃ m : ℕ, IsDiscreteValuationRing.addVal R' (j PowerSeries.X) = (n * m : ℕ) := by
  subst hj'
  -- the generic fibre is nonempty
  let : Algebra k K' := ((algebraMap R' K').comp (j.comp PowerSeries.C)).toAlgebra
  let σ : PowerSeries k →ₐ[k] K' :=
    { (algebraMap R' K').comp j with commutes' := fun _ => rfl }
  have := nonempty_cover f φ hn K' (σ PowerSeries.X)
  let x := (coverBaseChangeIso f φ PowerSeries.X σ).inv
    (Classical.arbitrary (cover f φ K' (σ PowerSeries.X)))
  have : Nonempty Y := ⟨pullback.fst q _ (e.hom x)⟩
  obtain ⟨s, hs⟩ := exists_section_of_nodal q hq
  let pt : Spec (.of K') ⟶ pullback q (Spec.map (CommRingCat.ofHom (algebraMap R' K'))) :=
    pullback.lift (Spec.map (CommRingCat.ofHom (algebraMap R' K')) ≫ s) (𝟙 _) (by
      rw [Category.assoc, hs, Category.comp_id, Category.id_comp])
  have he' : e.inv ≫ pullback.snd (coverSnd f φ (PowerSeries k) PowerSeries.X)
      (Spec.map (CommRingCat.ofHom ((algebraMap R' K').comp j))) = pullback.snd _ _ := by
    rw [Iso.inv_comp_eq, he]
  refine exists_addVal_eq_mul_of_point f φ hn R' K' j hj
    (pt ≫ e.inv ≫ pullback.fst _ _) ?_
  rw [Category.assoc, Category.assoc, pullback.condition, ← Category.assoc e.inv, he',
    ← Category.assoc, pullback.lift_snd, Category.id_comp, CommRingCat.ofHom_comp,
    Spec.map_comp]


variable (k) in
/-- **`k[[π]]` is a henselian local ring**, being complete for its maximal ideal. -/
instance henselianLocalRing_powerSeries : HenselianLocalRing (PowerSeries k) :=
  haveI : IsAdicComplete (IsLocalRing.maximalIdeal (PowerSeries k)) (PowerSeries k) :=
    PowerSeries.isAdicComplete_maximalIdeal
  haveI := IsAdicComplete.henselianRing (PowerSeries k) (IsLocalRing.maximalIdeal (PowerSeries k))
  { is_henselian := fun f hf a ha hd => HenselianRing.is_henselian f hf a ha
      (hd.map (Ideal.Quotient.mk _)) }

variable (k) in
/-- The residue field of `k[[π]]` is `k`. -/
def residueFieldPowerSeriesEquiv : IsLocalRing.ResidueField (PowerSeries k) ≃+* k :=
  (Ideal.quotEquivOfEq (by
    rw [PowerSeries.maximalIdeal_eq_span_X]
    ext φ
    rw [Ideal.mem_span_singleton, RingHom.mem_ker, PowerSeries.X_dvd_iff])).trans
    (RingHom.quotientKerEquivOfSurjective (f := PowerSeries.constantCoeff (R := k))
      fun a => ⟨PowerSeries.C a, by simp⟩)

/-- **The ramification index of a semistable extension is a positive multiple of `n`.** Let `R'`
be a discrete valuation ring with fraction field `K'` and `j : R = k[[π]] → R'` injective and
integral, with `k` separably closed. If `X_{K'}` has semistable reduction over `R'` — it is the
generic fibre of a proper flat model `Y ⟶ Spec R'` which is at-worst-nodal of relative dimension
one — then the ramification index `e = v_{R'}(π)` of `R'` over `R` is `n m` with `m ≥ 1`. Indeed
`R'` is henselian with separably closed residue field ([Stacks, Tag 092X]) and
`Stacks.CyclicCover.exists_addVal_eq_mul_of_nodal_model` applies. -/
theorem exists_ramificationIdx_eq_mul_of_semistable [IsSepClosed k] [IsProper f] [Nonempty Z]
    (hn : n ≠ 0) (R' : Type u) [CommRing R'] [IsDomain R'] [IsDiscreteValuationRing R']
    (K' : Type u) [Field K'] [Algebra R' K'] [IsFractionRing R' K'] (j : PowerSeries k →+* R')
    (hint : j.IsIntegral) (hinj : Function.Injective j)
    (j' : PowerSeries k →+* K') (hj' : (algebraMap R' K').comp j = j')
    {Y : Scheme.{u}} (q : Y ⟶ Spec (.of R'))
    (e : pullback (coverSnd f φ (PowerSeries k) PowerSeries.X) (Spec.map (CommRingCat.ofHom j')) ≅
      pullback q (Spec.map (CommRingCat.ofHom (algebraMap R' K'))))
    (he : e.hom ≫ pullback.snd _ _ = pullback.snd _ _) [Flat q] [IsProper q]
    (hq : IsAtWorstNodalOfRelativeDimensionOne q) :
    ∃ m : ℕ, 0 < m ∧ IsDiscreteValuationRing.addVal R' (j PowerSeries.X) = (n * m : ℕ) := by
  obtain ⟨hB, hloc, hsep⟩ := RingHom.exists_henselianLocalRing_of_isIntegral_of_isDomain j hint
  have := hB
  have := hloc
  have : IsSepClosed (IsLocalRing.ResidueField (PowerSeries k)) :=
    IsSepClosed.of_ringEquiv (residueFieldPowerSeriesEquiv k)
  have := (hsep inferInstance).1
  have hj : j PowerSeries.X ≠ 0 := by
    rw [Ne, ← map_zero j]; exact fun h => PowerSeries.X_ne_zero (hinj h)
  obtain ⟨m, hm⟩ :=
    exists_addVal_eq_mul_of_nodal_model f φ hn R' K' j hj j' hj' q e he hq
  refine ⟨m, Nat.pos_of_ne_zero fun h0 => ?_, hm⟩
  subst h0
  rw [mul_zero, Nat.cast_zero, IsDiscreteValuationRing.addVal_eq_zero_iff] at hm
  have hmem : PowerSeries.X ∈ IsLocalRing.maximalIdeal (PowerSeries k) := by
    rw [PowerSeries.maximalIdeal_eq_span_X]; exact Ideal.mem_span_singleton_self _
  exact (IsLocalRing.mem_maximalIdeal _).1 hmem (isUnit_of_map_unit j _ hm)


open Stacks.DiscreteValuationRing.Ramification in
/-- **Any finite extension `K'/K` over which `X_K` attains semistable reduction ramifies with
ramification index at least `n`**, in fact a positive multiple of `n`. Here `K = k((π))`, `R'` is
the integral closure of `R = k[[π]]` in `K'` — a discrete valuation ring with fraction field `K'` —
and semistable reduction means that `X_{K'} = X_K ×_K K'` is the generic fibre of a proper model
over `R'` which is at-worst-nodal of relative dimension one (Definition 0CDH). -/
theorem exists_ramificationIdx_eq_mul_of_hasSemistableReduction [IsSepClosed k] [IsProper f]
    [Nonempty Z] (hn : n ≠ 0) (K' : Type u) [Field K'] [Algebra (LaurentSeries k) K']
    [FiniteDimensional (LaurentSeries k) K'] [Algebra (PowerSeries k) K']
    [IsScalarTower (PowerSeries k) (LaurentSeries k) K'] :
    haveI := isDiscreteValuationRing_integralClosure (PowerSeries k) (LaurentSeries k) K'
    haveI := _root_.isFractionRing_integralClosure (PowerSeries k) (LaurentSeries k) K'
    (∃ (Y : Scheme.{u}) (q : Y ⟶ Spec (.of (integralClosure (PowerSeries k) K')))
      (e : pullback (coverSnd f φ (PowerSeries k) PowerSeries.X)
          (Spec.map (CommRingCat.ofHom (algebraMap (PowerSeries k) K'))) ≅
        pullback q (Spec.map (CommRingCat.ofHom
          (algebraMap (integralClosure (PowerSeries k) K') K')))),
      Stacks.Models.IsModel (pullback.snd _ _) q e ∧ IsProper q ∧
        IsAtWorstNodalOfRelativeDimensionOne q) →
    ∃ m : ℕ, 0 < m ∧ IsDiscreteValuationRing.addVal (integralClosure (PowerSeries k) K')
      (algebraMap (PowerSeries k) (integralClosure (PowerSeries k) K') PowerSeries.X) =
        (n * m : ℕ) := by
  have := isDiscreteValuationRing_integralClosure (PowerSeries k) (LaurentSeries k) K'
  have := _root_.isFractionRing_integralClosure (PowerSeries k) (LaurentSeries k) K'
  have := faithfulSMul_integralClosure (PowerSeries k) (LaurentSeries k) K'
  rintro ⟨Y, q, e, ⟨hflat, -, -, he⟩, hprop, hq⟩
  have := hflat
  have := hprop
  exact exists_ramificationIdx_eq_mul_of_semistable f φ hn (integralClosure (PowerSeries k) K') K'
    (algebraMap _ _) (fun x => integralClosure.isIntegral x)
    (FaithfulSMul.algebraMap_injective _ _) (algebraMap (PowerSeries k) K')
    (IsScalarTower.algebraMap_eq _ _ _).symm q e he hq

end Stacks.CyclicCover

end
