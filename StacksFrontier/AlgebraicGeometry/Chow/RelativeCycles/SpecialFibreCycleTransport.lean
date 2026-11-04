module

public import StacksFrontier.AlgebraicGeometry.Chow.Degrees.ClosedImmersionCycles
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardClosedSubscheme
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.ResidueTrdeg
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.DvrFibreDimension
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.SpecialFibreDimension
public import StacksFrontier.AlgebraicGeometry.Fibres.SectionsFromFibre

/-!
# Transporting cycles on a special fibre to the total space

Let `R` be a discrete valuation ring with closed point `s` and let `V` be a scheme locally of
finite type over `Spec R`. Since `{s}` is closed in `Spec R`, the inclusion of the special fibre
`V_s ⟶ V` is a closed immersion. A cycle on `V_s`, formed for the Chow situation on the spectrum
of the residue field `κ(s)`, is therefore the same datum as a cycle on `V` formed for
`Stacks.Chow.dvrChowSituation R` and supported on the special fibre: the closed immersion
identifies the points of `V_s` with the points of `V` above `s`, it does not change relative
dimensions — the dimension function of `dvrChowSituation` vanishes at the closed point — and it
has residue degree one everywhere.

This file makes that identification for the two things a degree computation on the special fibre
needs. The first is the cycle of the whole special fibre: the `r`-cycle of the trivial closed
subscheme `⊥` of `V_s`, read at a point `v` of `V_s`, is the coefficient at the image of `v` of
the `r`-cycle of the closed subscheme of `V` cut out by the kernel of the fibre inclusion. The
second is proper pushforward: given a proper `g : V ⟶ V'` over `Spec R` and a cycle on `V_s`
matching a cycle on `V` coefficientwise along the fibre inclusion, the pushforward along the
induced map of special fibres matches the pushforward along `g` in the same way.

Nothing in the arguments is special to a discrete valuation ring beyond the two properties of
the closed point just named, so the general statements are proved for an arbitrary Chow
situation `C` and a point `s` of its base that is closed and at which the dimension function
vanishes; the discrete valuation ring statements are immediate specialisations.

## Main results

* `Stacks.Chow.closedSubschemeCycleCoeff_congr_relativeDimension`,
  `Stacks.Chow.cycleAssociatedToClosedSubscheme_congr_relativeDimension` — the coefficient of
  the cycle of a closed subscheme depends on the Chow situation only through the dimension
  condition it imposes.
* `Stacks.Chow.fiberSubschemeCycle_bot_apply_fiberι_of_isClosed`,
  `Stacks.Chow.fiberSubschemeCycle_bot_apply_fiberι` — the cycle of the whole fibre over a
  closed point of dimension zero, read on the total space.
* `Stacks.Chow.properPushforward_fiber_apply_of_isClosed`,
  `Stacks.Chow.properPushforward_fiber_apply` — proper pushforward of a cycle on such a fibre,
  read on the total space.

## Implementation notes

The two general statements carry the hypotheses `IsClosed {s}` and `C.dimensionFunction s = 0`
rather than an assumption on the base ring, and the hypothesis `hclosed` is used only through
`Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι`, which is what makes the fibre
inclusion a closed immersion and hence injective, dimension preserving and of residue degree
one.

The pushforward on the fibre is named by `Stacks.Chow.fiberProperPushforward`, which is by
definition the proper pushforward for the Chow situation on the spectrum of the residue field
`κ(s)` along `Stacks.Chow.inducedFiberMap`. Writing that situation out at the concrete point
`IsLocalRing.closedPoint R` is not an option: instance resolution would then have to see
`PrimeSpectrum R` and the carrier of `Spec R` as the same type at reducible transparency in
order to find the field structure on `κ(s)`, which it cannot.

`Stacks.Chow.fiberSubschemeCycle_bot_apply_fiberι` is stated with the hypotheses that a degree
computation has at hand — `V` integral with generic point on the generic fibre, of dimension `r`
there — even though the proof needs none of them: the identification of the two cycles of the
special fibre needs neither, and the dimension bookkeeping that those hypotheses control
enters only when the coefficient is interpreted as the multiplicity of a prime divisor. The
corresponding hypothesis on the cycle supported off the special fibre is likewise absent from
`Stacks.Chow.properPushforward_fiber_apply`: every point of `V` lying over the image of a point
of the special fibre of `V'` already lies on the special fibre of `V`, so the locally finite sum
computing the pushforward on the total space is automatically indexed by the special fibre.

## References

* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 02R4](https://stacks.math.columbia.edu/tag/02R4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Changing the Chow situation -/

/-- The coefficient of the cycle of a closed subscheme depends on the Chow situation only
through the dimension condition it imposes: the multiplicity entering
`Stacks.Chow.closedSubschemeCycleCoeff` is that of a component of the subscheme and mentions no
situation, and the two components selected agree because a closed immersion is injective on
points. -/
theorem closedSubschemeCycleCoeff_congr_relativeDimension (C C' : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (f' : X ⟶ C'.S)
    [LocallyOfFiniteType f'] (i : Z ⟶ X) [IsClosedImmersion i] (k k' : ℤ) (x : X)
    (h : relativeDimension C.dimensionFunction f x = k ↔
      relativeDimension C'.dimensionFunction f' x = k') :
    closedSubschemeCycleCoeff C f i k x = closedSubschemeCycleCoeff C' f' i k' x := by
  classical
  unfold closedSubschemeCycleCoeff
  by_cases hex : ∃ ξ : genericPoints Z,
      i ξ.1 = x ∧ relativeDimension C.dimensionFunction f x = k
  · obtain ⟨ξ, hξ, hk⟩ := id hex
    have hex' : ∃ ξ : genericPoints Z,
        i ξ.1 = x ∧ relativeDimension C'.dimensionFunction f' x = k' := ⟨ξ, hξ, h.1 hk⟩
    rw [dite_eq_left hex, dite_eq_left hex']
    exact congrArg (componentMultiplicity i) (Subtype.ext (i.isClosedEmbedding.injective
      ((Classical.choose_spec hex).1.trans (Classical.choose_spec hex').1.symm)))
  · have hex' : ¬ ∃ ξ : genericPoints Z,
        i ξ.1 = x ∧ relativeDimension C'.dimensionFunction f' x = k' := by
      rintro ⟨ξ, hξ, hk⟩
      exact hex ⟨ξ, hξ, h.2 hk⟩
    rw [dite_eq_right hex, dite_eq_right hex']

/-- The cycle of a closed subscheme, read at one point, depends on the Chow situation only
through the dimension condition it imposes. This is
`Stacks.Chow.closedSubschemeCycleCoeff_congr_relativeDimension` phrased for the bundled
cycle. -/
theorem cycleAssociatedToClosedSubscheme_congr_relativeDimension (C C' : ChowSituation.{u})
    {X Z : Scheme.{u}} (f : X ⟶ C.S) [LocallyOfFiniteType f] (f' : X ⟶ C'.S)
    [LocallyOfFiniteType f'] (i : Z ⟶ X) [IsClosedImmersion i] (k k' : ℤ) (x : X)
    (h : relativeDimension C.dimensionFunction f x = k ↔
      relativeDimension C'.dimensionFunction f' x = k') :
    (cycleAssociatedToClosedSubscheme C f i k : AlgebraicCycle X ℤ) x =
      (cycleAssociatedToClosedSubscheme C' f' i k' : AlgebraicCycle X ℤ) x :=
  closedSubschemeCycleCoeff_congr_relativeDimension C C' f f' i k k' x h

/-! ### A fibre over a closed point of dimension zero -/

section Fibre

variable (C : ChowSituation.{u}) {X Y : Scheme.{u}}

/-- At a point of the base where the dimension function vanishes, the relative dimension of a
point of the fibre, read in the total space, is its dimension inside the fibre. -/
theorem relativeDimension_fiberι_of_dimensionFunction_eq_zero (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {s : C.S} (hs : C.dimensionFunction s = 0) (x : p.fiber s) :
    relativeDimension C.dimensionFunction p ((p.fiberι s).base x) =
      fiberPointDimension p s x := by
  rw [relativeDimension_fiberι, hs, zero_add]

/-- At a closed point of the base where the dimension function vanishes, the relative dimension
of a point of the fibre, computed through the closed immersion of that fibre, is its dimension
inside the fibre. -/
theorem relativeDimension_fiberι_comp_of_dimensionFunction_eq_zero (p : X ⟶ C.S)
    [LocallyOfFiniteType p] {s : C.S} (hclosed : IsClosed ({s} : Set C.S))
    (hs : C.dimensionFunction s = 0) (x : p.fiber s) :
    relativeDimension C.dimensionFunction (p.fiberι s ≫ p) x = fiberPointDimension p s x := by
  have := Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι p hclosed
  rw [relativeDimension_comp_closedImmersion,
    relativeDimension_fiberι_of_dimensionFunction_eq_zero C p hs]

/-- **The cycle of a whole fibre, read on the total space.** At a closed point `s` of the base
where the dimension function vanishes, the coefficient at `x` of the `r`-cycle of the fibre over
`s` equals the coefficient at the image of `x` of the `r`-cycle of the closed subscheme of the
total space cut out by the kernel of the fibre inclusion.

The fibre inclusion is a closed immersion, so the closed subscheme of the total space it cuts
out is the fibre itself; proper pushforward along it transports coefficients unchanged, and the
two Chow situations impose the same dimension condition. -/
theorem fiberSubschemeCycle_bot_apply_fiberι_of_isClosed (p : X ⟶ C.S) [LocallyOfFiniteType p]
    {s : C.S} (hclosed : IsClosed ({s} : Set C.S)) (hs : C.dimensionFunction s = 0) (r : ℕ)
    (x : p.fiber s) :
    (fiberSubschemeCycle p s r ⊥ : AlgebraicCycle (p.fiber s) ℤ) x =
      (cycleAssociatedToClosedSubscheme C p ((p.fiberι s).ker).subschemeι (r : ℤ) :
        AlgebraicCycle X ℤ) ((p.fiberι s).base x) := by
  have := Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι p hclosed
  have key : (cycleAssociatedToClosedSubscheme C p ((p.fiberι s).ker).subschemeι (r : ℤ) :
        AlgebraicCycle X ℤ) ((p.fiberι s).base x) =
      (cycleAssociatedToClosedSubscheme C (p.fiberι s ≫ p)
        (⊥ : (p.fiber s).IdealSheafData).subschemeι (r : ℤ) :
          AlgebraicCycle (p.fiber s) ℤ) x := by
    rw [← Scheme.IdealSheafData.map_bot (p.fiberι s),
      ← cycleAssociatedToClosedSubscheme_map C p (p.fiberι s) ⊥ (r : ℤ),
      ← properPushforward_cycleAssociatedToClosedSubscheme_of_isClosedImmersion_comp C
        (p.fiberι s ≫ p) p (p.fiberι s) rfl
        (⊥ : (p.fiber s).IdealSheafData).subschemeι (r : ℤ)]
    exact properPushforward_apply_image_of_isClosedImmersion C (p.fiberι s ≫ p) p
      (p.fiberι s) rfl (r : ℤ) _ x
  have hiff : fiberPointDimension p s x = (r : ℤ) ↔
      relativeDimension C.dimensionFunction (p.fiberι s ≫ p) x = (r : ℤ) := by
    rw [relativeDimension_fiberι_comp_of_dimensionFunction_eq_zero C p hclosed hs]
  rw [key]
  exact cycleAssociatedToClosedSubscheme_congr_relativeDimension
    (fieldChowSituation (C.S.residueField s)) C (p.fiberToSpecResidueField s)
    (p.fiberι s ≫ p) (⊥ : (p.fiber s).IdealSheafData).subschemeι (r : ℤ) (r : ℤ) x hiff

/-- **Proper pushforward on a fibre, read on the total space.** Let `s` be a closed point of the
base at which the dimension function vanishes, let `f : X ⟶ Y` be proper over the base, and let
`c` be an `r`-cycle on `X_s` whose coefficients are those of an `r`-cycle `d` on `X`, read along
the inclusion of `X_s`. Then the pushforward of `c` along the induced map of fibres has, at a
point `z` of `Y_s`, the coefficient of the pushforward of `d` along `f` at the image of `z`.

Both sides are locally finite sums over a fibre of a base change of `f`, and the two index sets
correspond: a point of `X` above the image of `z` lies over `s`, hence on `X_s`. The weights
agree because the fibre inclusions preserve relative dimension and have residue degree one. -/
theorem properPushforward_fiber_apply_of_isClosed (p : X ⟶ C.S) [LocallyOfFiniteType p]
    (q : Y ⟶ C.S) [LocallyOfFiniteType q] (f : X ⟶ Y) [IsProper f] (hf : f ≫ q = p) {s : C.S}
    (hclosed : IsClosed ({s} : Set C.S)) (hs : C.dimensionFunction s = 0) (r : ℕ)
    (c : FiberCycleGroup p s r) (d : CycleGroup C p (r : ℤ))
    (hcd : ∀ x : p.fiber s, (c : AlgebraicCycle (p.fiber s) ℤ) x =
      (d : AlgebraicCycle X ℤ) ((p.fiberι s).base x))
    (z : q.fiber s) :
    (fiberProperPushforward p q f hf s r c : AlgebraicCycle (q.fiber s) ℤ) z =
      (properPushforward C p q f hf (r : ℤ) d : AlgebraicCycle Y ℤ) ((q.fiberι s).base z) := by
  classical
  have := Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι p hclosed
  have := Stacks.AlgebraicGeometry.Fibres.isClosedImmersion_fiberι q hclosed
  have hcd' : ∀ x : p.fiber s, c.1 x = d.1 ((p.fiberι s).base x) := hcd
  -- every point of `X` above the image of `z` lies on the fibre over `s`
  have hpre : f.base ⁻¹' {(q.fiberι s).base z} =
      (p.fiberι s).base '' ((inducedFiberMap p q f hf s).base ⁻¹' {z}) := by
    ext w
    constructor
    · intro hw
      have hw' : f.base w = (q.fiberι s).base z := hw
      obtain ⟨v, hv⟩ : w ∈ Set.range (p.fiberι s).base := by
        rw [Scheme.Hom.range_fiberι, ← hf]
        change q.base (f.base w) = s
        rw [hw']
        exact base_fiberι q s z
      refine ⟨v, (q.fiberι s).isClosedEmbedding.injective ?_, hv⟩
      rw [inducedFiberMap_fiberι_base, hv]
      exact hw'
    · rintro ⟨v, hv, rfl⟩
      change f.base ((p.fiberι s).base v) = (q.fiberι s).base z
      rw [← inducedFiberMap_fiberι_base p q f hf s v]
      exact congrArg (q.fiberι s).base
        (show (inducedFiberMap p q f hf s).base v = z from hv)
  change (properPushforward (fieldChowSituation (C.S.residueField s))
      (p.fiberToSpecResidueField s) (q.fiberToSpecResidueField s)
      (inducedFiberMap p q f hf s) (inducedFiberMap_fiberToSpecResidueField p q f hf s)
      (r : ℤ) c).1 z =
    (properPushforward C p q f hf (r : ℤ) d).1 ((q.fiberι s).base z)
  rw [properPushforward_apply, properPushforward_apply, hpre,
    finsum_mem_image (p.fiberι s).isClosedEmbedding.injective.injOn]
  refine finsum_mem_congr rfl fun x _ ↦ ?_
  have hd : ∀ {W : Scheme.{u}} (w : W ⟶ C.S) [LocallyOfFiniteType w] (y : w.fiber s),
      relativeDimension C.dimensionFunction w ((w.fiberι s).base y) =
        relativeDimension (fieldChowSituation (C.S.residueField s)).dimensionFunction
          (w.fiberToSpecResidueField s) y :=
    fun w _ y ↦ relativeDimension_fiberι_of_dimensionFunction_eq_zero C w hs y
  have hdeg : f.residueDegree ((p.fiberι s).base x) =
      (inducedFiberMap p q f hf s).residueDegree x := by
    have h1 := residueDegree_comp (p.fiberι s) f x
    have h2 := residueDegree_comp (inducedFiberMap p q f hf s) (q.fiberι s) x
    rw [residueDegree_eq_one_of_isClosedImmersion (p.fiberι s) x, mul_one] at h1
    rw [inducedFiberMap_fiberι p q f hf s,
      residueDegree_eq_one_of_isClosedImmersion (q.fiberι s)
        ((inducedFiberMap p q f hf s).base x), one_mul] at h2
    rw [← h1, h2]
  rw [hcd' x, hd p x, ← inducedFiberMap_fiberι_base p q f hf s x, hd q, hdeg]

end Fibre

/-! ### The special fibre over a discrete valuation ring -/

section Dvr

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R]

/-- The closed point of the spectrum of a discrete valuation ring is a closed point of the base
scheme of `Stacks.Chow.dvrChowSituation`. -/
theorem isClosed_singleton_closedPoint_dvrChowSituation :
    IsClosed ({IsLocalRing.closedPoint R} : Set (dvrChowSituation R).S) :=
  IsLocalRing.isClosed_singleton_closedPoint R

/-- **The cycle of the whole special fibre, read on the total space.** For `V` locally of finite
type over a discrete valuation ring `R`, the coefficient at `v` of the `r`-cycle of the special
fibre equals the coefficient, at the image of `v`, of the `r`-cycle of the closed subscheme of
`V` cut out by the kernel of the inclusion of the special fibre.

The hypotheses on the generic point of `V` are not used: they record the situation of the degree
computation this statement serves, in which `r` is the dimension of the generic fibre. -/
theorem fiberSubschemeCycle_bot_apply_fiberι {V : Scheme.{u}} (sV : V ⟶ Spec (.of R))
    [LocallyOfFiniteType sV] [IsIntegral V] {r : ℕ}
    (ξ : sV.fiber (genericPoint (Spec (.of R))))
    (_hξ : (sV.fiberι (genericPoint (Spec (.of R)))).base ξ = genericPoint V)
    (_hdim : fiberPointDimension sV (genericPoint (Spec (.of R))) ξ = (r : ℤ))
    (v : sV.fiber (IsLocalRing.closedPoint R)) :
    (fiberSubschemeCycle sV (IsLocalRing.closedPoint R) r ⊥ :
        AlgebraicCycle (sV.fiber (IsLocalRing.closedPoint R)) ℤ) v =
      (cycleAssociatedToClosedSubscheme (dvrChowSituation R) sV
          ((sV.fiberι (IsLocalRing.closedPoint R)).ker).subschemeι (r : ℤ) :
        AlgebraicCycle V ℤ) ((sV.fiberι (IsLocalRing.closedPoint R)).base v) :=
  fiberSubschemeCycle_bot_apply_fiberι_of_isClosed (dvrChowSituation R) sV
    isClosed_singleton_closedPoint_dvrChowSituation
    (dvrChowSituation_dimensionFunction_closedPoint R) r v

/-- **Proper pushforward on the special fibre, read on the total space.** Let `g : V ⟶ V'` be
proper over a discrete valuation ring `R` and let `c` be an `r`-cycle on the special fibre of
`V` whose coefficients are those of an `r`-cycle `d` on `V`, read along the inclusion of the
special fibre. Then the coefficient at `z` of the pushforward of `c` along the induced map of
special fibres is the coefficient, at the image of `z`, of the pushforward of `d` along `g`. -/
theorem properPushforward_fiber_apply {V V' : Scheme.{u}} (sV : V ⟶ Spec (.of R))
    [LocallyOfFiniteType sV] (sV' : V' ⟶ Spec (.of R)) [LocallyOfFiniteType sV']
    (g : V ⟶ V') [IsProper g] (hg : g ≫ sV' = sV) (r : ℕ)
    (c : FiberCycleGroup sV (IsLocalRing.closedPoint R) r)
    (d : CycleGroup (dvrChowSituation R) sV (r : ℤ))
    (hcd : ∀ v : sV.fiber (IsLocalRing.closedPoint R),
      (c : AlgebraicCycle (sV.fiber (IsLocalRing.closedPoint R)) ℤ) v =
        (d : AlgebraicCycle V ℤ) ((sV.fiberι (IsLocalRing.closedPoint R)).base v))
    (z : sV'.fiber (IsLocalRing.closedPoint R)) :
    (fiberProperPushforward sV sV' g hg (IsLocalRing.closedPoint R) r c :
        AlgebraicCycle (sV'.fiber (IsLocalRing.closedPoint R)) ℤ) z =
      (properPushforward (dvrChowSituation R) sV sV' g hg (r : ℤ) d : AlgebraicCycle V' ℤ)
        ((sV'.fiberι (IsLocalRing.closedPoint R)).base z) :=
  properPushforward_fiber_apply_of_isClosed (dvrChowSituation R) sV sV' g hg
    isClosed_singleton_closedPoint_dvrChowSituation
    (dvrChowSituation_dimensionFunction_closedPoint R) r c d hcd z

end Dvr

end Stacks.Chow

end
