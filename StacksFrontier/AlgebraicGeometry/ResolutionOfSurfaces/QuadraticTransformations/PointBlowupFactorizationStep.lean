module

public import StacksFrontier.AlgebraicGeometry.Blowup.CartierCentre
public import StacksFrontier.AlgebraicGeometry.Blowup.ClassifyingMorphism
public import StacksFrontier.AlgebraicGeometry.Blowup.RegularSurfaceExceptionalCurveGlobal
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorStalkResidueCokernel
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartier.UFDExtension
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierPullbackCorollaries
public import StacksFrontier.AlgebraicGeometry.Divisors.EffectiveCartierStalk.StalkwiseRegular
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.NodalContraction.Basic
public import StacksFrontier.AlgebraicGeometry.Properties.RegularStalkDvr
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.Dimension.Basic
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ExceptionalSquareChain
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalSurfacesDimTwo
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocusCodimensionZero
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.DominateRationalMapNoetherian
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.ExceptionalCurveLocus
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMapsUnconditional
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocus
public import StacksFrontier.AlgebraicGeometry.Variety.Geometric.BirationalIsomorphismLocusDVR
import all StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.QuadraticTransformations.FactorizationBirationalMaps

/-!
# Proper birational morphisms of regular surfaces factor through blowups of fundamental points

Let `f : X ⟶ Y` be a proper birational morphism between integral Noetherian schemes regular of
dimension two. This file proves [Stacks, Tag 0C5R], that `f` is a sequence of blowups in closed
points, and with it the forward direction of [Stacks, Tag 0C5S].

## The step

The heart is the source's step: `f` factors through the blowup `Bl_y Y` at any closed point `y`
outside the maximal open over which `f` is an isomorphism. As in the source, [Stacks, Tag 0C5H]
dominates the rational map `X ⇢ Bl_y Y` by a chain of blowups at closed points of `X` over `y`, and
the chain is peeled one blowup at a time. At a single blowup `π : Bl_x W ⟶ W` with a morphism
`g' : Bl_x W ⟶ Bl_y Y` over `f_W : W ⟶ Y`, the source shows that the exceptional curve `E` of `π`
collapses under `g'` through the conormal sequence; here a valuation argument is used instead.

Let `I = 𝔪_y 𝒪_W`. If `I` is an effective Cartier divisor, the universal property of the blowup
gives the factorization of `f_W`. If `E` collapses, [Stacks, Tag 0C5J] gives it. Otherwise `I`
fails to be invertible at `x` (away from `x` it is the pullback of the invertible `g'^* E'`, `E'`
the exceptional curve of `Bl_y Y`), `g'` sends the generic point `ξ` of `E` to the generic point
`η` of `E'` (a dimension count in `Bl_y Y`), the local ring at `η` is a discrete valuation ring
with maximal ideal the stalk of `E'`, `g'` is an isomorphism near `η` by [Stacks, Tag 0BFP], and so
`I 𝒪_{Bl_x W, ξ}` is the maximal ideal of `𝒪_{Bl_x W, ξ}`. Since that maximal ideal is not
idempotent, some `t ∈ I_x` has image outside `𝔪_ξ²`. In the regular local ring `𝒪_{W,x}`, a unique
factorization domain of dimension two, either `I_x` is `𝔪_x`-primary, so `f_W` is quasi-finite at
`x` and [Stacks, Tag 0BFP] puts `y` in the isomorphism locus; or `I_x` lies in a height-one prime
`(h)`, so `t = h s` with `h, s ∈ 𝔪_x` and the image of `t` lies in `𝔪_ξ²`. Both are absurd.

## The induction

The induction runs on the number of contracted curves of `f`, counted as the non-closed points
sent to closed points (`Stacks.ResolutionOfSurfaces.contractedPointCount`). It is finite, and it
drops strictly when `f` is replaced by its factorization through `Bl_y Y`: the generic point of the
exceptional curve of `Bl_y Y` has a contracted preimage. The induction itself is the library's
`Stacks.ResolutionOfSurfaces.factorsAsPointBlowups_of_pointBlowupStep`.

## Main results

In the namespace `Stacks.ResolutionOfSurfaces`:

* `exists_comp_eq_pointBlowUpToBase_of_square` — the single-blowup step.
* `exists_comp_eq_pointBlowUpToBase_of_not_mem_isomorphismLocus` — the step of [Stacks, Tag 0C5R].
* `factorsAsPointBlowups_of_isProper_of_isBirational` — [Stacks, Tag 0C5R].
* `birationalOver_iff_exists_factorsAsPointBlowups_of_isIntegralRegularSurface` —
  [Stacks, Tag 0C5S].

## References

* [Stacks Project, Tag 0C5R](https://stacks.math.columbia.edu/tag/0C5R)
* [Stacks Project, Tag 0C5S](https://stacks.math.columbia.edu/tag/0C5S)
* [Stacks Project, Tag 0C5H](https://stacks.math.columbia.edu/tag/0C5H)
* [Stacks Project, Tag 0C5J](https://stacks.math.columbia.edu/tag/0C5J)
* [Stacks Project, Tag 0BFP](https://stacks.math.columbia.edu/tag/0BFP)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.ResolutionOfSurfaces

/-- Two lifts through the blowup at a closed point agree as soon as the generic point of their
integral source does not lie over the centre. -/
theorem eq_of_comp_pointBlowUpToBase_eq {A Z : Scheme.{u}} [IsIntegral Z] {a : A}
    (ha : IsClosed ({a} : Set A)) {g₁ g₂ : Z ⟶ pointBlowUp ha}
    (h : g₁ ≫ pointBlowUpToBase ha = g₂ ≫ pointBlowUpToBase ha)
    (hgen : (g₁ ≫ pointBlowUpToBase ha) (genericPoint Z) ≠ a) : g₁ = g₂ := by
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A) with hM
  set b := pointBlowUpToBase ha with hb
  let Vc : A.Opens := M.support.compl
  have hiso : IsIso (b ∣_ Vc) := isIso_blowUp_restrict_compl_support M
  have hmemVc : ∀ y : A, y ≠ a → y ∈ Vc := by
    intro y hy hy'
    have : y ∈ (M.support : Set A) := hy'
    rw [hM, Scheme.IdealSheafData.coe_support_vanishingIdeal] at this
    exact hy this
  let V : Z.Opens := (g₁ ≫ b) ⁻¹ᵁ Vc
  have hVne : (V : Set Z).Nonempty := ⟨genericPoint Z, hmemVc _ hgen⟩
  have hVd : Dense (V : Set Z) := V.2.dense hVne
  have := AlgebraicGeometry.Opens.isDominant_ι hVd
  have : IsSeparated b := Stacks.RelativeProj.Situation.isSeparated_relativeProjToBase _
  refine ext_of_isDominant_of_isSeparated b h V.ι ?_
  have hrange : ∀ g : Z ⟶ pointBlowUp ha, g ≫ b = g₁ ≫ b →
      Set.range (V.ι ≫ g).base ⊆ Set.range (b ⁻¹ᵁ Vc).ι.base := by
    intro g hg
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    change b (g (V.ι v)) ∈ Vc
    have hv : (g₁ ≫ b) (V.ι v) ∈ Vc := v.2
    rw [← hg] at hv
    simpa using hv
  let h₁ := IsOpenImmersion.lift (b ⁻¹ᵁ Vc).ι (V.ι ≫ g₁) (hrange g₁ rfl)
  let h₂ := IsOpenImmersion.lift (b ⁻¹ᵁ Vc).ι (V.ι ≫ g₂) (hrange g₂ h.symm)
  have hf₁ : h₁ ≫ (b ⁻¹ᵁ Vc).ι = V.ι ≫ g₁ := IsOpenImmersion.lift_fac _ _ _
  have hf₂ : h₂ ≫ (b ⁻¹ᵁ Vc).ι = V.ι ≫ g₂ := IsOpenImmersion.lift_fac _ _ _
  have key : h₁ ≫ (b ∣_ Vc) = h₂ ≫ (b ∣_ Vc) := by
    rw [← cancel_mono Vc.ι, Category.assoc, Category.assoc, morphismRestrict_ι,
      ← Category.assoc, ← Category.assoc, hf₁, hf₂, Category.assoc, Category.assoc, h]
  have h12 : h₁ = h₂ := (cancel_mono (b ∣_ Vc)).mp key
  rw [← hf₁, ← hf₂, h12]

/-- On an integral Noetherian scheme regular of dimension two every local ring has dimension at
most two. -/
theorem ringKrullDim_stalk_le_two {W : Scheme.{u}} (hW : IsIntegralRegularSurface W) (w : W) :
    ringKrullDim (W.presheaf.stalk w) ≤ 2 := by
  rw [← hW.topologicalKrullDim_eq, ← PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim]
  exact (W.fromSpecStalk w).isEmbedding.isInducing.topologicalKrullDim_le

/-- A proper generalization is strictly larger in the specialization order. -/
theorem lt_of_specializes_of_ne {X : Scheme.{u}} {x y : X} (h : y ⤳ x) (hne : x ≠ y) : x < y :=
  lt_of_le_not_ge (Scheme.le_iff_specializes.mpr h)
    fun h' => hne ((Scheme.le_iff_specializes.mp h').antisymm h).eq

/-- On an integral Noetherian scheme regular of dimension two there is no strict chain of three
generalizations. -/
theorem not_lt_lt_lt {W : Scheme.{u}} (hW : IsIntegralRegularSurface W) {q η ζ θ : W}
    (h₁ : q < η) (h₂ : η < ζ) (h₃ : ζ < θ) : False := by
  have e1 := Order.coheight_add_one_le h₃
  have e2 := Order.coheight_add_one_le h₂
  have e3 := Order.coheight_add_one_le h₁
  have h2 := ringKrullDim_stalk_le_two hW q
  rw [AlgebraicGeometry.ringKrullDim_stalk_eq_coheight] at h2
  have h3 : (3 : ℕ∞) ≤ Order.coheight q :=
    calc (3 : ℕ∞) = 0 + 1 + 1 + 1 := by norm_num
      _ ≤ Order.coheight θ + 1 + 1 + 1 := by gcongr; exact zero_le
      _ ≤ Order.coheight ζ + 1 + 1 := by gcongr
      _ ≤ Order.coheight η + 1 := by gcongr
      _ ≤ Order.coheight q := e3
  have : ((3 : ℕ∞) : WithBot ℕ∞) ≤ 2 := le_trans (by exact_mod_cast h3) h2
  exact absurd this (by decide)

/-- A morphism locally of finite type is quasi-finite at a closed point which has no proper
generalization in its own fibre. -/
theorem quasiFiniteAt_of_forall_specializes {W A : Scheme.{u}} (f : W ⟶ A)
    [LocallyOfFiniteType f] (w : W) (hw : IsClosed ({w} : Set W))
    (h : ∀ y : W, y ⤳ w → f y = f w → y = w) : quasiFiniteAt f w := by
  have hinj : Function.Injective (f.fiberι (f w)) := (f.fiberι (f w)).isEmbedding.injective
  have h1 : IsClosed ({f.asFiber w} : Set (f.fiber (f w))) := by
    have : ({f.asFiber w} : Set (f.fiber (f w))) = (f.fiberι (f w)) ⁻¹' {w} := by
      ext x
      simp only [Set.mem_singleton_iff, Set.mem_preimage]
      constructor
      · rintro rfl
        exact f.fiberι_asFiber w
      · intro hx
        exact hinj (by rw [hx, f.fiberι_asFiber w])
    rw [this]
    exact hw.preimage (f.fiberι (f w)).continuous
  have h2 : ¬ ∃ x' : f.fiber (f w), x' ≠ f.asFiber w ∧ x' ⤳ f.asFiber w := by
    rintro ⟨x', hne, hsp⟩
    have hsp' : f.fiberι (f w) x' ⤳ w := by
      simpa using hsp.map (f.fiberι (f w)).continuous
    have hfib : f.fiberι (f w) x' ∈ f ⁻¹' {f w} := by
      rw [← f.range_fiberι]
      exact ⟨x', rfl⟩
    exact hne (hinj (by rw [h _ hsp' hfib, f.fiberι_asFiber w]))
  have key := (quasiFiniteAt_tfae f w).out 1 3
  exact key.mpr ⟨h1, h2⟩

/-- A point specializing to `w` and lying over `f w` corresponds to a prime of `𝒪_{W,w}`
containing the image of the maximal ideal of `𝒪_{A, f w}`. -/
theorem eq_of_specializes_of_forall_prime {W A : Scheme.{u}} (f : W ⟶ A) (w : W)
    (hJ : ∀ p : Ideal (W.presheaf.stalk w), p.IsPrime →
      (IsLocalRing.maximalIdeal (A.presheaf.stalk (f w))).map (f.stalkMap w).hom ≤ p →
        p = IsLocalRing.maximalIdeal (W.presheaf.stalk w))
    (y : W) (hy : y ⤳ w) (hfy : f y = f w) : y = w := by
  obtain ⟨p, rfl⟩ : y ∈ Set.range (W.fromSpecStalk w) := by
    rw [Scheme.range_fromSpecStalk]
    exact hy
  have hinjA : Function.Injective (A.fromSpecStalk (f w)) :=
    (A.fromSpecStalk (f w)).isEmbedding.injective
  have hcomm : A.fromSpecStalk (f w) (Spec.map (f.stalkMap w) p) = f (W.fromSpecStalk w p) := by
    rw [← Scheme.Hom.comp_apply, Scheme.SpecMap_stalkMap_fromSpecStalk, Scheme.Hom.comp_apply]
  have hclosed : Spec.map (f.stalkMap w) p = IsLocalRing.closedPoint (A.presheaf.stalk (f w)) :=
    hinjA (by rw [hcomm, hfy, Scheme.fromSpecStalk_closedPoint])
  have hcomap : p.asIdeal.comap (f.stalkMap w).hom =
      IsLocalRing.maximalIdeal (A.presheaf.stalk (f w)) := by
    have := congrArg PrimeSpectrum.asIdeal hclosed
    rwa [Spec.map_apply] at this
  have hle : (IsLocalRing.maximalIdeal (A.presheaf.stalk (f w))).map (f.stalkMap w).hom ≤
      p.asIdeal := by
    rw [Ideal.map_le_iff_le_comap, hcomap]
  rw [show p = IsLocalRing.closedPoint (W.presheaf.stalk w) from
    PrimeSpectrum.ext (hJ p.asIdeal p.isPrime hle), Scheme.fromSpecStalk_closedPoint]

/-- In a local unique factorization domain of dimension at most two, an element of an ideal
which is contained in a non-maximal prime but is not principal on a nonzerodivisor is a product
of two non-units. -/
theorem exists_mul_of_mem_of_le_prime {B : Type*} [CommRing B] [IsDomain B] [IsLocalRing B]
    [UniqueFactorizationMonoid B] (hdim : ringKrullDim B ≤ 2) (J : Ideal B)
    (hJ : ∀ g ∈ nonZeroDivisors B, J ≠ Ideal.span {g}) {x : B} (hx : x ∈ J) (hx0 : x ≠ 0)
    (p : Ideal B) [hp : p.IsPrime] (hJp : J ≤ p) (hpm : p ≠ IsLocalRing.maximalIdeal B) :
    ∃ h y, h ∈ IsLocalRing.maximalIdeal B ∧ y ∈ IsLocalRing.maximalIdeal B ∧ x = h * y := by
  have hp0 : p ≠ ⊥ := fun h0 => hx0 ((Submodule.mem_bot B).mp (h0 ▸ hJp hx))
  obtain ⟨h, hhp, hprime⟩ := hp.exists_mem_prime_of_ne_bot hp0
  have hhprime : (Ideal.span {h}).IsPrime := (Ideal.span_singleton_prime hprime.ne_zero).mpr hprime
  have hheq : Ideal.span {h} = p := by
    by_contra hne
    have hle : Ideal.span {h} ≤ p := (Ideal.span_singleton_le_iff_mem p).mpr hhp
    let P0 : PrimeSpectrum B := ⟨⊥, Ideal.isPrime_bot⟩
    let P1 : PrimeSpectrum B := ⟨Ideal.span {h}, hhprime⟩
    let P2 : PrimeSpectrum B := ⟨p, hp⟩
    let P3 : PrimeSpectrum B := IsLocalRing.closedPoint B
    have h01 : P0 < P1 := by
      refine lt_of_le_of_ne bot_le (fun e => hprime.ne_zero ?_)
      have : h ∈ (Ideal.span {h} : Ideal B) := Ideal.subset_span rfl
      have e' : (⊥ : Ideal B) = Ideal.span {h} := congrArg PrimeSpectrum.asIdeal e
      rw [← e'] at this
      exact (Submodule.mem_bot B).mp this
    have h12 : P1 < P2 := lt_of_le_of_ne hle (fun e => hne (congrArg PrimeSpectrum.asIdeal e))
    have h23 : P2 < P3 := lt_of_le_of_ne (IsLocalRing.le_maximalIdeal hp.ne_top)
      (fun e => hpm (congrArg PrimeSpectrum.asIdeal e))
    have e1 := Order.height_add_one_le h01
    have e2 := Order.height_add_one_le h12
    have e3 := Order.height_add_one_le h23
    have h3 : (3 : ℕ∞) ≤ Order.height P3 :=
      calc (3 : ℕ∞) = 0 + 1 + 1 + 1 := by norm_num
        _ ≤ Order.height P0 + 1 + 1 + 1 := by gcongr; exact zero_le
        _ ≤ Order.height P1 + 1 + 1 := by gcongr
        _ ≤ Order.height P2 + 1 := by gcongr
        _ ≤ Order.height P3 := e3
    have hk := Order.height_le_krullDim P3
    have : ((3 : ℕ∞) : WithBot ℕ∞) ≤ 2 :=
      le_trans (le_trans (by exact_mod_cast h3) hk) hdim
    exact absurd this (by decide)
  obtain ⟨y, rfl⟩ := Ideal.mem_span_singleton.mp (hheq ▸ hJp hx : x ∈ Ideal.span {h})
  refine ⟨h, y, ?_, ?_, rfl⟩
  · exact (IsLocalRing.mem_maximalIdeal _).mpr hprime.not_isUnit
  · rw [IsLocalRing.mem_maximalIdeal, mem_nonunits_iff]
    intro hy
    refine hJ (h * y) (mem_nonZeroDivisors_of_ne_zero hx0) (le_antisymm ?_ ?_)
    · rw [← hheq] at hJp
      intro z hz
      obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.mp (hJp hz)
      refine Ideal.mem_span_singleton'.mpr ⟨c * ↑(hy.unit⁻¹), ?_⟩
      rw [mul_assoc, mul_comm _ (h * y), mul_assoc, IsUnit.mul_val_inv, mul_one]
    · exact (Ideal.span_singleton_le_iff_mem J).mpr hx

/-- A maximal ideal generated by a nonzerodivisor is not idempotent. -/
theorem maximalIdeal_ne_sq_of_eq_span {O : Type*} [CommRing O] [IsLocalRing O] {t : O}
    (ht : t ∈ nonZeroDivisors O) (hm : IsLocalRing.maximalIdeal O = Ideal.span {t}) :
    IsLocalRing.maximalIdeal O ≠ IsLocalRing.maximalIdeal O ^ 2 := by
  intro heq
  have htm : t ∈ IsLocalRing.maximalIdeal O := hm ▸ Ideal.subset_span rfl
  have ht2 : t ∈ Ideal.span {t} ^ 2 := by rw [← hm]; exact heq ▸ htm
  rw [Ideal.span_singleton_pow, Ideal.mem_span_singleton'] at ht2
  obtain ⟨c, hc⟩ := ht2
  have h1 : t * (1 - c * t) = 0 := by linear_combination -hc
  have h2 : 1 - c * t = 0 := (mem_nonZeroDivisors_iff.mp ht).2 _ (by rwa [mul_comm])
  have hunit : IsUnit t := IsUnit.of_mul_eq_one c (by linear_combination -h2)
  exact (IsLocalRing.mem_maximalIdeal t).mp htm hunit

/-- **The algebraic heart of the valuation argument.** Let `ν : B → O` be a local homomorphism
from a local unique factorization domain of dimension at most two to a local ring whose maximal
ideal is not idempotent, and let `J ⊆ B` be an ideal which is not principal on a nonzerodivisor
but generates the maximal ideal of `O`. Then every prime containing `J` is the maximal ideal. -/
theorem eq_maximalIdeal_of_map_eq_maximalIdeal {B O : Type*} [CommRing B] [IsDomain B]
    [IsLocalRing B] [UniqueFactorizationMonoid B] [CommRing O] [IsLocalRing O]
    (hdim : ringKrullDim B ≤ 2) (ν : B →+* O) [IsLocalHom ν]
    (hO : IsLocalRing.maximalIdeal O ≠ IsLocalRing.maximalIdeal O ^ 2) (J : Ideal B)
    (hJ : ∀ g ∈ nonZeroDivisors B, J ≠ Ideal.span {g})
    (hmap : J.map ν = IsLocalRing.maximalIdeal O) (p : Ideal B) [p.IsPrime] (hJp : J ≤ p) :
    p = IsLocalRing.maximalIdeal B := by
  by_contra hpm
  have hex : ∃ x ∈ J, ν x ∉ IsLocalRing.maximalIdeal O ^ 2 := by
    by_contra! hall
    have : J.map ν ≤ IsLocalRing.maximalIdeal O ^ 2 := Ideal.map_le_iff_le_comap.mpr hall
    rw [hmap] at this
    exact hO (le_antisymm this (Ideal.pow_le_self two_ne_zero))
  obtain ⟨x, hxJ, hx⟩ := hex
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hx
  obtain ⟨h, y, hh, hy, rfl⟩ := exists_mul_of_mem_of_le_prime hdim J hJ hxJ hx0 p hJp hpm
  apply hx
  rw [map_mul, pow_two]
  exact Ideal.mul_mem_mul (map_nonunit ν h hh) (map_nonunit ν y hy)

/-- If `f` restricts to an isomorphism over `U`, its stalk maps at points over `U` are
isomorphisms. -/
private theorem isIso_stalkMap_of_isIso_restrict {X Y : Scheme.{u}} (f : X ⟶ Y) (U : Y.Opens)
    [IsIso (f ∣_ U)] (x : f ⁻¹ᵁ U) : IsIso (f.stalkMap x.1) :=
  (MorphismProperty.isomorphisms CommRingCat).arrow_mk_iso_iff
    (morphismRestrictStalkMap f U x) |>.mp
    ((AlgebraicGeometry.isIso_iff_isIso_stalkMap (f ∣_ U)).mp ‹_› |>.2 x)

/-- The exceptional curve of the blowup at a closed point of codimension two is integral. -/
private theorem isIntegral_subscheme_exceptionalIdeal {W : Scheme.{u}} {w : W}
    (hw : IsClosed ({w} : Set W)) (hreg : IsRegularLocalRing (W.presheaf.stalk w))
    (hdim : ringKrullDim (W.presheaf.stalk w) = 2) :
    IsIntegral (exceptionalIdeal
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).subscheme := by
  obtain ⟨e, -⟩ :=
    Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal
      w hw hreg hdim
  exact AlgebraicGeometry.isIntegral_subscheme_of_iso_projectiveLineProj _ _ e

/-- The exceptional curve of the blowup at a closed point lies over that point. -/
theorem pointBlowUpToBase_subschemeι_exceptionalIdeal {W : Scheme.{u}} {w : W}
    (hw : IsClosed ({w} : Set W))
    (z : (exceptionalIdeal
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).subscheme) :
    pointBlowUpToBase hw
      ((exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))).subschemeι
        z) = w := by
  have hmem : ((exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : Closeds W))).subschemeι z) ∈
      (((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).comap
        (pointBlowUpToBase hw)).support : Set (pointBlowUp hw)) := by
    change _ ∈ ((exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal
      (⟨{w}, hw⟩ : Closeds W))).support : Set (pointBlowUp hw))
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact ⟨z, rfl⟩
  rwa [Scheme.IdealSheafData.support_comap, TopologicalSpace.Closeds.coe_preimage,
    Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem

/-- The local ring at a closed point of an integral Noetherian scheme regular of dimension two has
dimension one or two. -/
theorem ringKrullDim_stalk_eq_one_or_two_of_isClosed {W : Scheme.{u}}
    (hW : IsIntegralRegularSurface W) (w : W) (hw : IsClosed ({w} : Set W)) :
    ringKrullDim (W.presheaf.stalk w) = 1 ∨ ringKrullDim (W.presheaf.stalk w) = 2 := by
  have hint := hW.isIntegral
  have hreg : IsRegularLocalRing (W.presheaf.stalk w) :=
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hW.isRegular w
  have hle := ringKrullDim_stalk_le_two hW w
  have hne : ringKrullDim (W.presheaf.stalk w) ≠ 0 := by
    intro h0
    rw [ringKrullDim_stalk_eq_coheight] at h0
    have hc : Order.coheight w = 0 := by exact_mod_cast h0
    have hs : w ⤳ genericPoint W := Order.coheight_eq_zero.mp hc (show w ≤ (⊤ : W) from le_top)
    have hwη : w = genericPoint W := (hs.antisymm (genericPoint_specializes w)).eq
    refine genericPoint_notMem_supportSet
      (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))
      (vanishingIdeal_singleton_ne_bot hW.topologicalKrullDim_eq w hw) ?_
    change genericPoint W ∈
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W)).support : Set W)
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal]
    simpa using hwη.symm
  have hrl := (isRegularLocalRing_iff (W.presheaf.stalk w)).mp hreg
  rw [← hrl] at hle hne ⊢
  have hn : (IsLocalRing.maximalIdeal (W.presheaf.stalk w)).spanFinrank ≤ 2 := by
    exact_mod_cast hle
  have hn0 : (IsLocalRing.maximalIdeal (W.presheaf.stalk w)).spanFinrank ≠ 0 := by
    exact_mod_cast hne
  rcases (show (IsLocalRing.maximalIdeal (W.presheaf.stalk w)).spanFinrank = 1 ∨
      (IsLocalRing.maximalIdeal (W.presheaf.stalk w)).spanFinrank = 2 by omega) with h1 | h2
  · exact Or.inl (by exact_mod_cast h1)
  · exact Or.inr (by exact_mod_cast h2)

/-- **The single-blowup step of [Stacks, Tag 0C5R].** Let `f : W ⟶ A` be a proper birational
morphism of integral Noetherian schemes regular of dimension two, `a ∈ A` a closed point outside
the maximal open over which `f` is an isomorphism, `w ∈ W` a closed point over `a`, and
`g' : Bl_w W ⟶ Bl_a A` a morphism over `f`. Then `f` itself factors through `Bl_a A`. -/
theorem exists_comp_eq_pointBlowUpToBase_of_square {A W : Scheme.{u}}
    (hA : IsIntegralRegularSurface A) (hW : IsIntegralRegularSurface W) (f : W ⟶ A)
    (hf : IsProper f) (hbf : IsBirational f) {a : A} (ha : IsClosed ({a} : Set A))
    (haU : ∀ U : A.Opens, IsGreatest { V : A.Opens | IsIso (f ∣_ V) } U → a ∉ U)
    {w : W} (hw : IsClosed ({w} : Set W)) (hwa : f w = a)
    (g' : pointBlowUp hw ⟶ pointBlowUp ha)
    (hsq : g' ≫ pointBlowUpToBase ha = pointBlowUpToBase hw ≫ f) :
    ∃ ψ : W ⟶ pointBlowUp ha, ψ ≫ pointBlowUpToBase ha = f := by
  have hAnoe := hA.isNoetherian
  have hAint := hA.isIntegral
  have hWnoe := hW.isNoetherian
  have hWint := hW.isIntegral
  have hALN : IsLocallyNoetherian A := hAnoe.toIsLocallyNoetherian
  have hWLN : IsLocallyNoetherian W := hWnoe.toIsLocallyNoetherian
  have hfp := hf
  have hA' : IsIntegralRegularSurface (pointBlowUp ha) :=
    isIntegralRegularSurface_blowUp_vanishingIdeal_singleton A a ha hA
  have hZ : IsIntegralRegularSurface (pointBlowUp hw) :=
    isIntegralRegularSurface_blowUp_vanishingIdeal_singleton W w hw hW
  have hA'noe := hA'.isNoetherian
  have hA'int := hA'.isIntegral
  have hZnoe := hZ.isNoetherian
  have hZint := hZ.isIntegral
  set π := pointBlowUpToBase hw with hπdef
  set b := pointBlowUpToBase ha with hbdef
  set E := exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W))
    with hEdef
  have hπE : ∀ z : E.subscheme, π (E.subschemeι z) = w := fun z =>
    pointBlowUpToBase_subschemeι_exceptionalIdeal hw z
  rcases Stacks.ResolutionOfSurfaces.isIso_pointBlowUpToBase_or_ringKrullDim_stalk_eq_two hW w hw
    with hiso | hdim2
  · exact ⟨inv π ≫ g', by rw [Category.assoc, hsq, IsIso.inv_hom_id_assoc]⟩
  have hπbir : IsBirational π := isBirational_blowUpToBase _
    (vanishingIdeal_singleton_ne_bot hW.topologicalKrullDim_eq w hw)
  have hπprop : IsProper π := inferInstance
  have hcompprop : IsProper (π ≫ f) := MorphismProperty.comp_mem _ _ _ hπprop hfp
  have hcompbir : IsBirational (π ≫ f) := hπbir.comp hbf
  have hg'prop : IsProper g' := isProper_of_comp_pointBlowUpToBase ha hcompprop g' hsq
  have hg'bir : IsBirational g' :=
    isBirational_of_comp_pointBlowUpToBase hA.topologicalKrullDim_eq ha hcompbir g' hsq
  have hg'dom : IsDominant g' := hg'bir.isDominant
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A) with hMdef
  have hMbot : M ≠ ⊥ := vanishingIdeal_singleton_ne_bot hA.topologicalKrullDim_eq a ha
  have hgenA : genericPoint A ≠ a := by
    intro h
    apply genericPoint_notMem_supportSet M hMbot
    change genericPoint A ∈ (M.support : Set A)
    rw [hMdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
    exact h
  have hgenZ : (g' ≫ b) (genericPoint (pointBlowUp hw)) ≠ a := by
    rw [hsq, Scheme.Hom.comp_apply, hπbir.genericPoint_eq, hbf.genericPoint_eq]
    exact hgenA
  set IW := M.comap f with hIWdef
  by_cases hcart : Stacks.Divisors.IsEffectiveCartierDivisor IW
  · have := isIso_blowUp_restrict_compl_support M
    exact Stacks.Blowup.exists_hom_blowUp_of_isEffectiveCartierDivisor M f hcart
  have hregw : IsRegularLocalRing (W.presheaf.stalk w) :=
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hW.isRegular w
  -- if the exceptional curve collapses, Tag 0C5J factors `f`
  by_cases hconst : ∃ w' : pointBlowUp ha, ∀ z : E.subscheme, g' (E.subschemeι z) = w'
  · have hcontr : IsContractionOfExceptionalCurve E π :=
      isContractionOfExceptionalCurve_blowUpToBase w hw hregw hdim2
    obtain ⟨ψ, -, hψ⟩ :=
      exists_comp_eq_of_isContraction_of_const_on_exceptionalCurve hcontr f b g' hsq hconst
    exact ⟨ψ, hψ⟩
  exfalso
  have hnc := hconst
  -- the exceptional curve upstairs and its generic point
  have : IsIntegral E.subscheme := isIntegral_subscheme_exceptionalIdeal hw hregw hdim2
  set ξ := E.subschemeι (genericPoint E.subscheme) with hξdef
  have hξw : π ξ = w := hπE _
  -- the exceptional curve downstairs
  obtain ⟨U, hU⟩ := exists_maximal_isomorphism_open f
  have haU' : a ∉ U := haU U hU
  have hrega : IsRegularLocalRing (A.presheaf.stalk a) :=
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hA.isRegular a
  have hdima : ringKrullDim (A.presheaf.stalk a) = 2 :=
    Stacks.ResolutionOfSurfaces.ringKrullDim_stalk_eq_two_of_notMem_isomorphism_open hA f hbf U hU
      ha haU'
  set D' := exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))
    with hD'def
  have : IsIntegral D'.subscheme := isIntegral_subscheme_exceptionalIdeal ha hrega hdima
  have hD'cart : Stacks.Divisors.IsEffectiveCartierDivisor D' := inferInstance
  set η := g' ξ with hηdef
  set ζ := D'.subschemeι (genericPoint D'.subscheme) with hζdef
  have hbη : b η = a := by
    rw [hηdef, ← Scheme.Hom.comp_apply, hsq, Scheme.Hom.comp_apply, hξw, hwa]
  -- the inverse image of the centre upstairs
  have hIZ : IW.comap π = D'.comap g' := by
    rw [hIWdef, ← Scheme.IdealSheafData.comap_comp, ← hsq, Scheme.IdealSheafData.comap_comp]
  have hIZcart : Stacks.Divisors.IsEffectiveCartierDivisor (IW.comap π) := by
    rw [hIZ]; exact Stacks.Divisors.isPullbackDefined_of_isDominant g' D' hD'cart
  -- the image of the generic point of `E` is the generic point of `D'`
  have hηζ : η = ζ := by
    by_contra hne
    push Not at hnc
    obtain ⟨z, hz⟩ := hnc η
    have h1 : η ⤳ g' (E.subschemeι z) :=
      ((genericPoint_specializes z).map E.subschemeι.continuous).map g'.continuous
    obtain ⟨η', hη'⟩ : η ∈ Set.range D'.subschemeι.base :=
      Stacks.ResolutionOfSurfaces.preimage_singleton_subset_range_exceptionalIdeal ha hbη
    have h2 : ζ ⤳ η := hη' ▸ (genericPoint_specializes η').map D'.subschemeι.continuous
    have h3 : genericPoint (pointBlowUp ha) ⤳ ζ := genericPoint_specializes ζ
    have hζgen : ζ ≠ genericPoint (pointBlowUp ha) := by
      intro h
      apply genericPoint_notMem_supportSet_of_isEffectiveCartierDivisor hD'cart
      rw [← h, Scheme.IdealSheafData.mem_supportSet_iff_mem_support]
      change ζ ∈ (D'.support : Set (pointBlowUp ha))
      rw [← Scheme.IdealSheafData.range_subschemeι]
      exact ⟨_, rfl⟩
    exact not_lt_lt_lt hA' (lt_of_specializes_of_ne h1 hz)
      (lt_of_specializes_of_ne h2 hne) (lt_of_specializes_of_ne h3 hζgen)
  -- the local ring downstairs at `η` is a discrete valuation ring
  have hstD' : AlgebraicGeometry.IdealSheafData.stalk D' η =
      IsLocalRing.maximalIdeal ((pointBlowUp ha).presheaf.stalk η) := by
    rw [hηζ]
    exact AlgebraicGeometry.IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal D'
  obtain ⟨t, ht, hts⟩ :=
    AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor D' hD'cart η
  have hmη : IsLocalRing.maximalIdeal ((pointBlowUp ha).presheaf.stalk η) = Ideal.span {t} :=
    hstD' ▸ hts
  have hnf : ¬ IsField ((pointBlowUp ha).presheaf.stalk η) := by
    intro hfield
    have hbot := (IsLocalRing.isField_iff_maximalIdeal_eq).mp hfield
    rw [hmη, Ideal.span_singleton_eq_bot] at hbot
    exact ht.ne_zero hbot
  have htfae := (IsDiscreteValuationRing.TFAE ((pointBlowUp ha).presheaf.stalk η) hnf).out 1 5
  have hdvr : IsDiscreteValuationRing ((pointBlowUp ha).presheaf.stalk η) :=
    htfae.mpr ⟨t, hmη⟩
  -- `g'` is an isomorphism near `η`, so its stalk map at `ξ` is an isomorphism
  obtain ⟨U', hηU', hisoU'⟩ := exists_isIso_restrict_of_isDiscreteValuationRing g' hg'bir η
  have hstiso : IsIso (g'.stalkMap ξ) := isIso_stalkMap_of_isIso_restrict g' U' ⟨ξ, hηU'⟩
  -- the inverse image of the centre generates the maximal ideal at `ξ`
  have hIZξ : AlgebraicGeometry.IdealSheafData.stalk (IW.comap π) ξ =
      IsLocalRing.maximalIdeal ((pointBlowUp hw).presheaf.stalk ξ) := by
    rw [hIZ, AlgebraicGeometry.stalk_comap, hstD']
    let eR := (asIso (g'.stalkMap ξ)).commRingCatIsoToRingEquiv
    have hmax : ((IsLocalRing.maximalIdeal ((pointBlowUp ha).presheaf.stalk η)).map
        eR).IsMaximal := Ideal.map_isMaximal_of_equiv eR
    exact IsLocalRing.eq_maximalIdeal hmax
  have hmapJ : (AlgebraicGeometry.IdealSheafData.stalk IW (π ξ)).map (π.stalkMap ξ).hom =
      IsLocalRing.maximalIdeal ((pointBlowUp hw).presheaf.stalk ξ) := by
    rw [← AlgebraicGeometry.stalk_comap]; exact hIZξ
  -- the maximal ideal at `ξ` is not idempotent
  have hO : IsLocalRing.maximalIdeal ((pointBlowUp hw).presheaf.stalk ξ) ≠
      IsLocalRing.maximalIdeal ((pointBlowUp hw).presheaf.stalk ξ) ^ 2 := by
    obtain ⟨s, hs, hss⟩ :=
      AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor E
        inferInstance ξ
    rw [AlgebraicGeometry.IdealSheafData.stalk_subschemeι_genericPoint_eq_maximalIdeal E] at hss
    exact maximalIdeal_ne_sq_of_eq_span (hs.mem_nonZeroDivisors) hss
  -- the stalk of `IW` at `π ξ` is not principal on a nonzerodivisor
  have hJnp : ∀ g ∈ nonZeroDivisors (W.presheaf.stalk (π ξ)),
      AlgebraicGeometry.IdealSheafData.stalk IW (π ξ) ≠ Ideal.span {g} := by
    intro g hg heq
    apply hcart
    refine Stacks.Divisors.isEffectiveCartierDivisor_of_stalk_isPrincipal_nonZeroDivisor IW
      fun x hx => ?_
    by_cases hxw : x = π ξ
    · rw [hxw]; exact ⟨g, hg, heq⟩
    · have hxw' : x ≠ w := hξw ▸ hxw
      set Mw := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W) with hMwdef
      let Uw : W.Opens := ⟨Mw.supportᶜ, Mw.support.isClosed.isOpen_compl⟩
      have hxU : x ∈ Uw := by
        change x ∉ (Mw.support : Set W)
        rw [hMwdef, Scheme.IdealSheafData.coe_support_vanishingIdeal]
        exact hxw'
      have hisoU : IsIso (π ∣_ Uw) := isIso_blowUp_restrict_compl_support Mw
      obtain ⟨z, hz⟩ := (Scheme.homeoOfIso (asIso (π ∣_ Uw))).surjective ⟨x, hxU⟩
      have hπz : π z.1 = x :=
        (morphismRestrict_base_coe π Uw z).symm.trans (congrArg Subtype.val hz)
      have hst : IsIso (π.stalkMap z.1) := isIso_stalkMap_of_isIso_restrict π Uw z
      obtain ⟨g', hg', hgs⟩ :=
        AlgebraicGeometry.exists_isRegular_stalk_eq_span_of_isEffectiveCartierDivisor _ hIZcart z.1
      rw [AlgebraicGeometry.stalk_comap] at hgs
      rw [← hπz]
      let eR := (asIso (π.stalkMap z.1)).commRingCatIsoToRingEquiv
      refine ⟨eR.symm g', mem_nonZeroDivisors_of_ne_zero fun h0 => hg'.ne_zero ?_, ?_⟩
      · have := congrArg eR h0
        simpa using this
      · have hbij : Function.Bijective (π.stalkMap z.1).hom := eR.bijective
        calc AlgebraicGeometry.IdealSheafData.stalk IW (π z.1)
            = ((AlgebraicGeometry.IdealSheafData.stalk IW (π z.1)).map
                (π.stalkMap z.1).hom).comap (π.stalkMap z.1).hom :=
              (Ideal.comap_map_of_bijective _ hbij).symm
          _ = (Ideal.span {g'}).comap (eR : _ →+* _) := by rw [hgs]; rfl
          _ = (Ideal.span {g'}).map (eR.symm : _ →+* _) := (Ideal.map_symm eR).symm
          _ = Ideal.span {eR.symm g'} := by rw [Ideal.map_span, Set.image_singleton]; rfl
  -- every prime of `𝒪_{W, π ξ}` containing the stalk of `IW` is maximal
  have hdimB : ringKrullDim (W.presheaf.stalk (π ξ)) ≤ 2 := ringKrullDim_stalk_le_two hW _
  have : IsRegularLocalRing (W.presheaf.stalk (π ξ)) :=
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hW.isRegular _
  have : UniqueFactorizationMonoid (W.presheaf.stalk (π ξ)) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  have hprime : ∀ p : Ideal (W.presheaf.stalk (π ξ)), p.IsPrime →
      AlgebraicGeometry.IdealSheafData.stalk IW (π ξ) ≤ p →
        p = IsLocalRing.maximalIdeal (W.presheaf.stalk (π ξ)) := fun p hp hJp =>
    eq_maximalIdeal_of_map_eq_maximalIdeal hdimB (π.stalkMap ξ).hom hO _ hJnp hmapJ p hJp
  have hfξ : f (π ξ) = a := by rw [hξw, hwa]
  have hstM : ∀ y : A, y = a → AlgebraicGeometry.IdealSheafData.stalk M y =
      IsLocalRing.maximalIdeal (A.presheaf.stalk y) := by
    intro y hy
    rw [hy, hMdef]
    exact AlgebraicGeometry.IdealSheafData.stalk_vanishingIdeal_singleton a ha
  have hJ : AlgebraicGeometry.IdealSheafData.stalk IW (π ξ) =
      (IsLocalRing.maximalIdeal (A.presheaf.stalk (f (π ξ)))).map (f.stalkMap (π ξ)).hom := by
    rw [hIWdef, AlgebraicGeometry.stalk_comap, hstM _ hfξ]
  -- so `f` is quasi-finite at `π ξ`, and `a` lies in the isomorphism locus
  have hclosed : IsClosed ({π ξ} : Set W) := by rw [hξw]; exact hw
  have hqf : quasiFiniteAt f (π ξ) :=
    quasiFiniteAt_of_forall_specializes f (π ξ) hclosed
      (eq_of_specializes_of_forall_prime f (π ξ) fun p hp hle => hprime p hp (hJ ▸ hle))
  have : IsRegularLocalRing (A.presheaf.stalk (f (π ξ))) :=
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hA.isRegular _
  have : UniqueFactorizationMonoid (A.presheaf.stalk (f (π ξ))) :=
    IsRegularLocalRing.uniqueFactorizationMonoid _
  have hnormal : IsNormalRing (A.presheaf.stalk (f (π ξ))) :=
    IsNormalRing.of_isIntegrallyClosed _
  have hmem := mem_maximal_isomorphism_open_of_quasiFiniteAt_of_isNormal f hbf U hU (f (π ξ))
    hnormal (π ξ) rfl hqf
  exact haU' (hfξ ▸ hmem)



/-! ### The chain of blowups, peeled one blowup at a time -/

/-- A chain of blowups at closed points of an integral regular surface is birational. -/
theorem isBirational_of_pointBlowupChain_of_isIntegralRegularSurface {X Z : Scheme.{u}}
    {T : Set X} {p : Z ⟶ X} (hp : PointBlowupChain X T Z p) (hX : IsIntegralRegularSurface X) :
    IsBirational p := by
  have hXint := hX.isIntegral
  have hZint :=
    (isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hp hX).1.isIntegral
  exact isBirational_of_birationalOver_id p
    (by simpa using birationalOver_comp_of_pointBlowupChain_unconditional (𝟙 X) hp hX)

/-- A chain of blowups at closed points of an integral regular surface is surjective. -/
theorem surjective_of_pointBlowupChain_of_isIntegralRegularSurface {X Z : Scheme.{u}}
    {T : Set X} {p : Z ⟶ X} (hp : PointBlowupChain X T Z p) (hX : IsIntegralRegularSurface X) :
    Function.Surjective p.base := by
  obtain ⟨-, hproper⟩ :=
    isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hp hX
  have hdom := (isBirational_of_pointBlowupChain_of_isIntegralRegularSurface hp hX).isDominant
  exact p.surjective

/-- **Peeling a chain of blowups.** A commuting square over the blowup of `A` at a closed point
`a` outside the maximal isomorphism open of `g : B ⟶ A`, whose left edge is a chain of blowups at
closed points of `B` over `a`, yields a factorization of `g` through the blowup at `a`. -/
theorem exists_comp_eq_pointBlowUpToBase_of_pointBlowupChain_square {A B : Scheme.{u}}
    (hA : IsIntegralRegularSurface A) (hB : IsIntegralRegularSurface B) (g : B ⟶ A)
    (hg : IsProper g) (hbg : IsBirational g) {a : A} (ha : IsClosed ({a} : Set A))
    (haU : ∀ U : A.Opens, IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U → a ∉ U)
    {Z : Scheme.{u}} {T : Set B} {p : Z ⟶ B} (hT : ∀ b ∈ T, g b = a)
    (hchain : PointBlowupChain B T Z p) :
    ∀ φ : Z ⟶ pointBlowUp ha, φ ≫ pointBlowUpToBase ha = p ≫ g →
      ∃ ψ : B ⟶ pointBlowUp ha, ψ ≫ pointBlowUpToBase ha = g := by
  have hAnoe := hA.isNoetherian
  have hBint := hB.isIntegral
  induction hchain with
  | refl =>
    intro φ hsq
    rw [Category.id_comp] at hsq
    exact ⟨φ, hsq⟩
  | @step V q hq w hw hwT ih =>
    intro φ hsq
    obtain ⟨hVsurf, hqproper⟩ :=
      isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hq hB
    have hqbir : IsBirational q :=
      isBirational_of_pointBlowupChain_of_isIntegralRegularSurface hq hB
    have hqsurj : Function.Surjective q.base :=
      surjective_of_pointBlowupChain_of_isIntegralRegularSurface hq hB
    have hfp : IsProper (q ≫ g) := MorphismProperty.comp_mem _ _ _ hqproper hg
    have hfb : IsBirational (q ≫ g) := hqbir.comp hbg
    have hwa : (q ≫ g) w = a := by
      rw [Scheme.Hom.comp_apply]
      exact hT _ hwT
    have hsq' : φ ≫ pointBlowUpToBase ha = pointBlowUpToBase hw ≫ (q ≫ g) := by
      rwa [← Category.assoc]
    obtain ⟨ψ, hψ⟩ := exists_comp_eq_pointBlowUpToBase_of_square hA hVsurf (q ≫ g) hfp hfb ha
      (fun U' hU' => Stacks.ResolutionOfSurfaces.notMem_isomorphism_open_comp hA.isRegular g hg
        hbg haU q hqsurj U' hU')
      hw hwa φ hsq'
    exact ih ψ hψ

/-- **The step of [Stacks, Tag 0C5R].** A proper birational morphism `g : B ⟶ A` of integral
Noetherian schemes regular of dimension two factors through the blowup of `A` at any closed point
outside the maximal open over which `g` is an isomorphism. -/
theorem exists_comp_eq_pointBlowUpToBase_of_not_mem_isomorphismLocus {A B : Scheme.{u}}
    (hA : IsIntegralRegularSurface A) (hB : IsIntegralRegularSurface B) (g : B ⟶ A)
    (hg : IsProper g) (hbg : IsBirational g) {a : A} (ha : IsClosed ({a} : Set A))
    (haU : ∀ U : A.Opens, IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U → a ∉ U) :
    ∃ ψ : B ⟶ pointBlowUp ha, ψ ≫ pointBlowUpToBase ha = g := by
  classical
  have hAint := hA.isIntegral
  have hAnoe := hA.isNoetherian
  have hALN : IsLocallyNoetherian A := hAnoe.toIsLocallyNoetherian
  have hBint := hB.isIntegral
  have hBnoe := hB.isNoetherian
  have hMbot : Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A) ≠ ⊥ :=
    vanishingIdeal_singleton_ne_bot hA.topologicalKrullDim_eq a ha
  let Vc : A.Opens :=
    ⟨(Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)).supportᶜ,
      (Scheme.IdealSheafData.vanishingIdeal
        (⟨{a}, ha⟩ : Closeds A)).support.isClosed.isOpen_compl⟩
  have hbiso : IsIso (pointBlowUpToBase ha ∣_ Vc) :=
    isIso_blowUp_restrict_compl_support _
  let : B.Over A := ⟨g⟩
  let : (pointBlowUp ha).Over A := ⟨pointBlowUpToBase ha⟩
  have : IsProper (pointBlowUp ha ↘ A) := (inferInstance : IsProper (pointBlowUpToBase ha))
  have hgen : g (genericPoint B) = genericPoint A := hbg.genericPoint_eq
  have hdense : Dense ((g ⁻¹ᵁ Vc : B.Opens) : Set B) := by
    refine (g ⁻¹ᵁ Vc : B.Opens).2.dense ⟨genericPoint B, ?_⟩
    change g (genericPoint B) ∈ Vc
    rw [hgen]
    exact genericPoint_notMem_supportSet _ hMbot
  let fpm : B.PartialMap (pointBlowUp ha) :=
    { domain := g ⁻¹ᵁ Vc
      dense_domain := hdense
      hom := (g ∣_ Vc) ≫ (asIso (pointBlowUpToBase ha ∣_ Vc)).inv ≫
        (pointBlowUpToBase ha ⁻¹ᵁ Vc).ι }
  have : fpm.IsOver A := by
    refine ⟨?_⟩
    change ((g ∣_ Vc) ≫ (asIso (pointBlowUpToBase ha ∣_ Vc)).inv ≫
      (pointBlowUpToBase ha ⁻¹ᵁ Vc).ι) ≫ pointBlowUpToBase ha = (g ⁻¹ᵁ Vc).ι ≫ g
    have key : (asIso (pointBlowUpToBase ha ∣_ Vc)).inv ≫
        (pointBlowUpToBase ha ⁻¹ᵁ Vc).ι ≫ pointBlowUpToBase ha = Vc.ι := by
      rw [← morphismRestrict_ι (pointBlowUpToBase ha) Vc]
      exact (asIso (pointBlowUpToBase ha ∣_ Vc)).inv_hom_id_assoc Vc.ι
    rw [Category.assoc, Category.assoc, key, morphismRestrict_ι g Vc]
  have hreg : ∀ x : B, IsRegularLocalRing (B.presheaf.stalk x) := fun x =>
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hB.isRegular x
  obtain ⟨T, Z, p, φ, -, -, hTdom, hchain, hφS, -⟩ :=
    exists_pointBlowupChain_resolving_partialMap_of_isNoetherian (S := A) hreg
      (fun x => ringKrullDim_stalk_le_two hB x) fpm
  refine exists_comp_eq_pointBlowUpToBase_of_pointBlowupChain_square hA hB g hg hbg ha haU
    (T := (T : Set B)) (fun b hb => ?_) hchain φ hφS
  have hmem : g b ∈
      ((Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A)).support : Set A) :=
    not_not.mp fun h => hTdom b hb h
  rwa [Scheme.IdealSheafData.coe_support_vanishingIdeal] at hmem

/-! ### The measure: the number of contracted curves -/

/-- The points of the source of `g` which are not closed but are sent to closed points: for a
proper birational morphism of regular surfaces these are the generic points of the curves which
`g` contracts. -/
def contractedPoints {A B : Scheme.{u}} (g : B ⟶ A) : Set B :=
  {x | ¬ IsClosed ({x} : Set B) ∧ IsClosed ({g x} : Set A)}

/-- The number of curves contracted by `g`, the measure of the induction of [Stacks, Tag 0C5R]. -/
noncomputable def contractedPointCount (A B : Scheme.{u}) (g : B ⟶ A) : ℕ :=
  (contractedPoints g).ncard

/-- Along a factorization through a closed morphism, the contracted points can only grow. -/
theorem contractedPoints_mono {A A' B : Scheme.{u}} {ψ : B ⟶ A'} {b : A' ⟶ A} {g : B ⟶ A}
    (hb : IsClosedMap b.base) (hψ : ψ ≫ b = g) : contractedPoints ψ ⊆ contractedPoints g := by
  rintro x ⟨hx, hψx⟩
  refine ⟨hx, ?_⟩
  rw [← hψ, Scheme.Hom.comp_apply, ← Set.image_singleton]
  exact hb _ hψx

/-- **A proper birational morphism of integral regular surfaces contracts finitely many curves.**
A contracted point lies over the complement `T` of the maximal isomorphism open, which is a proper
closed subset; the closure of the point is an irreducible closed subset of one of the finitely many
irreducible closed pieces of `T`, and equals it, since otherwise a closed point of it, the point,
the generic point of the piece and the generic point of the source would be a chain of length three
in a scheme of dimension two. So a contracted point is the generic point of one of these pieces. -/
theorem finite_contractedPoints {A B : Scheme.{u}} (hA : IsIntegralRegularSurface A)
    (hB : IsIntegralRegularSurface B) (g : B ⟶ A) (hp : IsProper g) (hb : IsBirational g) :
    (contractedPoints g).Finite := by
  classical
  have hAnoe := hA.isNoetherian
  have hAint := hA.isIntegral
  have hBint := hB.isIntegral
  have hBnoe := hB.isNoetherian
  have hpi := hp
  obtain ⟨U, hU⟩ := exists_maximal_isomorphism_open g
  have hgenU : genericPoint A ∈ U :=
    mem_maximal_isomorphism_open_of_mem_genericPoints g hb U hU _
      (by rw [genericPoints_eq_singleton]; rfl)
  set T : Set B := g ⁻¹' ((U : Set A)ᶜ) with hT
  have hTcl : IsClosed T := (U.isOpen.isClosed_compl).preimage g.continuous
  have hgen : g (genericPoint B) = genericPoint A := hb.genericPoint_eq
  have hgenT : genericPoint B ∉ T := fun h => h (hgen ▸ hgenU)
  obtain ⟨S, hSfin, hScl, hSirr, hTS⟩ :=
    TopologicalSpace.NoetherianSpace.exists_finite_set_isClosed_irreducible hTcl
  -- each contracted point is the generic point of a piece
  have key : ∀ x ∈ contractedPoints g, ∃ Z ∈ S, closure ({x} : Set B) = Z := by
    rintro x ⟨hxcl, hgx⟩
    have hxT : x ∈ T := by
      intro hxU
      apply hxcl
      have hsub := subsingleton_fiber_of_isIso_restrict g U hU.1 hxU
      have : g ⁻¹' {g x} = {x} := by
        ext y; constructor
        · intro hy; exact hsub hy rfl
        · rintro rfl; rfl
      rw [← this]
      exact hgx.preimage g.continuous
    have hclT : closure ({x} : Set B) ⊆ T := hTcl.closure_subset_iff.mpr (by simpa using hxT)
    lift S to Finset (Set B) using hSfin
    obtain ⟨Z, hZS, hxZ⟩ := isIrreducible_iff_sUnion_isClosed.mp isIrreducible_singleton.closure S
      (fun Z hZ => hScl Z hZ) (hTS ▸ hclT)
    refine ⟨Z, hZS, ?_⟩
    by_contra hne
    obtain ⟨z, hz⟩ := QuasiSober.sober (hSirr Z hZS) (hScl Z hZS)
    have hzx : z ⤳ x := hz.specializes (hxZ (subset_closure rfl))
    have hzne : x ≠ z := by
      rintro rfl
      exact hne (hz.symm ▸ rfl)
    have hzT : z ∈ T := by
      have hZT : Z ⊆ T := by rw [hTS]; exact fun y hy => Set.mem_sUnion.mpr ⟨Z, hZS, hy⟩
      exact hZT (hz.mem)
    have hzgen : z ≠ genericPoint B := fun h => hgenT (h ▸ hzT)
    -- a closed point of the closure of `x`
    obtain ⟨c, hc, hccl⟩ :=
      (isClosed_closure : IsClosed (closure ({x} : Set B))).exists_closed_singleton
        ⟨x, subset_closure rfl⟩
    have hcx : x ⤳ c := specializes_iff_mem_closure.mpr hc
    have hcne : c ≠ x := by
      rintro rfl; exact hxcl hccl
    exact not_lt_lt_lt hB (lt_of_specializes_of_ne hcx hcne) (lt_of_specializes_of_ne hzx hzne)
      (lt_of_specializes_of_ne (genericPoint_specializes z) hzgen)
  choose! F hFS hF using key
  refine Set.Finite.of_finite_image (f := F) (hSfin.subset fun Z ⟨x, hx, hZ⟩ => hZ ▸ hFS x hx) ?_
  intro x hx y hy hxy
  have h1 := hF x hx
  have h2 := hF y hy
  rw [hxy, ← h2] at h1
  exact (isGenericPoint_closure.eq (h1 ▸ isGenericPoint_closure))

/-- **The measure drops along a factorization through the blowup at a closed point of codimension
two.** The generic point `η` of the exceptional curve of the blowup is not closed, the curve being
a projective line; a preimage of `η` under the surjection `ψ` is therefore a contracted point of
`g` which is not one of `ψ`. -/
theorem contractedPointCount_lt_of_comp_eq_pointBlowUpToBase {A B : Scheme.{u}}
    (hA : IsIntegralRegularSurface A) (hB : IsIntegralRegularSurface B) {g : B ⟶ A}
    (hp : IsProper g) (hb : IsBirational g) {a : A} (ha : IsClosed ({a} : Set A))
    (hdim : ringKrullDim (A.presheaf.stalk a) = 2) {ψ : B ⟶ pointBlowUp ha}
    (hψp : IsProper ψ) (hψb : IsBirational ψ) (hψ : ψ ≫ pointBlowUpToBase ha = g) :
    contractedPointCount (pointBlowUp ha) B ψ < contractedPointCount A B g := by
  have hAnoe := hA.isNoetherian
  have hALN : IsLocallyNoetherian A := hAnoe.toIsLocallyNoetherian
  have hreg : IsRegularLocalRing (A.presheaf.stalk a) :=
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hA.isRegular a
  set D' := exceptionalIdeal (Scheme.IdealSheafData.vanishingIdeal (⟨{a}, ha⟩ : Closeds A))
    with hD'def
  obtain ⟨e', -⟩ :=
    Stacks.Blowup.exists_isExceptionalCurveOfFirstKind_exceptionalIdeal_vanishingIdeal
      a ha hreg hdim
  have : IsIntegral D'.subscheme :=
    AlgebraicGeometry.isIntegral_subscheme_of_iso_projectiveLineProj D' _ e'
  set η := D'.subschemeι (genericPoint D'.subscheme) with hηdef
  have hηcl : ¬ IsClosed ({η} : Set (pointBlowUp ha)) := by
    intro hcl
    have hinj : Function.Injective D'.subschemeι.base := D'.subschemeι.isEmbedding.injective
    have hpre : D'.subschemeι.base ⁻¹' {η} = {genericPoint D'.subscheme} := by
      ext y; simp only [Set.mem_preimage, Set.mem_singleton_iff]
      exact ⟨fun h => hinj h, fun h => h ▸ rfl⟩
    have hcl' : IsClosed ({genericPoint D'.subscheme} : Set D'.subscheme) :=
      hpre ▸ hcl.preimage D'.subschemeι.continuous
    have hsub : Subsingleton D'.subscheme := by
      refine ⟨fun y z => ?_⟩
      have hy : y ∈ closure ({genericPoint D'.subscheme} : Set D'.subscheme) := by
        rw [genericPoint_closure]; trivial
      have hz : z ∈ closure ({genericPoint D'.subscheme} : Set D'.subscheme) := by
        rw [genericPoint_closure]; trivial
      rw [hcl'.closure_eq] at hy hz
      exact hy.trans hz.symm
    have h0 : topologicalKrullDim D'.subscheme ≤ 0 := topologicalKrullDim_zero_of_discreteTopology _
    have h1 : topologicalKrullDim D'.subscheme = 1 := by
      rw [← IsHomeomorph.topologicalKrullDim_eq _ e'.hom.homeomorph.isHomeomorph]
      exact Stacks.ProjectiveSpace.topologicalKrullDim_proj_fin _ (r := 2) (by norm_num)
    rw [h1] at h0
    exact absurd h0 (by decide)
  have := hψp
  have : IsDominant ψ := hψb.isDominant
  obtain ⟨x₀, hx₀⟩ := ψ.surjective η
  have hx₀cl : ¬ IsClosed ({x₀} : Set B) := by
    intro hcl
    apply hηcl
    have := ψ.isClosedMap _ hcl
    rwa [Set.image_singleton, hx₀] at this
  have hgx₀ : g x₀ = a := by
    rw [← hψ, Scheme.Hom.comp_apply, hx₀, hηdef]
    exact pointBlowUpToBase_subschemeι_exceptionalIdeal ha _
  have hsub : contractedPoints ψ ⊆ contractedPoints g :=
    contractedPoints_mono (pointBlowUpToBase ha).isClosedMap hψ
  have hmem : x₀ ∈ contractedPoints g := ⟨hx₀cl, hgx₀ ▸ ha⟩
  have hnmem : x₀ ∉ contractedPoints ψ := fun h => hηcl (hx₀ ▸ h.2)
  exact Set.ncard_lt_ncard ⟨hsub, fun h => hnmem (h hmem)⟩
    (finite_contractedPoints hA hB g hp hb)

/-- **Stacks Project, Tag 0C5R.** Let `f : X ⟶ Y` be a proper birational morphism between
integral Noetherian schemes regular of dimension two. Then `f` is a sequence of blowups in closed
points. -/
@[stacks 0C5R]
theorem factorsAsPointBlowups_of_isProper_of_isBirational {X Y : Scheme.{u}} (f : X ⟶ Y)
    (hY : IsIntegralRegularSurface Y) (hX : IsIntegralRegularSurface X) (hproper : IsProper f)
    (hbirational : IsBirational f) : FactorsAsPointBlowups Y Set.univ X f := by
  refine factorsAsPointBlowups_of_pointBlowupStep contractedPointCount
    (fun A a ha hA => isIntegralRegularSurface_blowUp_vanishingIdeal_singleton A a ha hA)
    (fun A B g hA hB hp hb hiso => ?_) f hY hX hproper hbirational
  have hAnoe := hA.isNoetherian
  have hAint := hA.isIntegral
  have hBint := hB.isIntegral
  have hALN : IsLocallyNoetherian A := hAnoe.toIsLocallyNoetherian
  have hpi := hp
  obtain ⟨U, hU⟩ := exists_maximal_isomorphism_open g
  obtain ⟨a, ha, haU⟩ := exists_isClosed_singleton_notMem_isomorphism_open g U hU hiso
  have haU' : ∀ U' : A.Opens, IsGreatest { V : A.Opens | IsIso (g ∣_ V) } U' → a ∉ U' :=
    fun U' hU' => by
      have : U' = U := le_antisymm (hU.2 hU'.1) (hU'.2 hU.1)
      rw [this]; exact haU
  obtain ⟨ψ, hψ⟩ := exists_comp_eq_pointBlowUpToBase_of_not_mem_isomorphismLocus hA hB g hp hb ha
    haU'
  have hψp : IsProper ψ := isProper_of_comp_pointBlowUpToBase ha hp ψ hψ
  have hψb : IsBirational ψ :=
    isBirational_of_comp_pointBlowUpToBase hA.topologicalKrullDim_eq ha hb ψ hψ
  exact ⟨a, ha, ψ, hψ, hψp, hψb, contractedPointCount_lt_of_comp_eq_pointBlowUpToBase hA hB hp hb
    ha (Stacks.ResolutionOfSurfaces.ringKrullDim_stalk_eq_two_of_notMem_isomorphism_open hA g hb
      U hU ha haU) hψp hψb hψ⟩

/-- **Stacks Project, Tag 0C5S.** Let `S` be a Noetherian scheme and let `X` and `Y` be proper
integral schemes over `S` which are regular of dimension two. Then `X` and `Y` are `S`-birational
if and only if there is a scheme `Z` with `S`-morphisms `Z ⟶ X` and `Z ⟶ Y`, each a sequence of
blowups in closed points. -/
@[stacks 0C5S]
theorem birationalOver_iff_exists_factorsAsPointBlowups_of_isIntegralRegularSurface
    {S X Y : Scheme.{u}} [AlgebraicGeometry.IsNoetherian S] [X.Over S] [Y.Over S]
    [IsProper (X ↘ S)] [IsProper (Y ↘ S)] (hX : IsIntegralRegularSurface X)
    (hY : IsIntegralRegularSurface Y) :
    Scheme.BirationalOver (X ↘ S) (Y ↘ S) ↔
      ∃ (Z : Scheme.{u}) (f : Z ⟶ X) (g : Z ⟶ Y),
        f ≫ (X ↘ S) = g ≫ (Y ↘ S) ∧
          FactorsAsPointBlowups X Set.univ Z f ∧ FactorsAsPointBlowups Y Set.univ Z g := by
  refine ⟨fun hbirational => ?_, birationalOver_of_exists_factorsAsPointBlowups hX hY⟩
  have hXint := hX.isIntegral
  have hYint := hY.isIntegral
  have hXnoetherian := hX.isNoetherian
  have hreg : ∀ x : X, IsRegularLocalRing (X.presheaf.stalk x) := fun x =>
    AlgebraicGeometry.IsRegular.isRegularLocalRing_stalk hX.isRegular x
  set pIso := hbirational.partialIso (X ↘ S) (Y ↘ S)
  have hover := hbirational.partialIso_isOver (X ↘ S) (Y ↘ S)
  have hpmOver : pIso.toPartialMap.IsOver S := by
    refine ⟨?_⟩
    change (pIso.iso.hom ≫ pIso.target.ι) ≫ (Y ↘ S) = pIso.source.ι ≫ (X ↘ S)
    rw [Category.assoc]
    exact hover
  obtain ⟨T, Z, p, q, -, -, -, hchain, hqS, hagree⟩ :=
    exists_pointBlowupChain_resolving_partialMap_of_isNoetherian (S := S) hreg
      (fun x => ringKrullDim_stalk_le_two hX x) pIso.toPartialMap
  obtain ⟨hZsurface, hZproper⟩ :=
    isIntegralRegularSurface_and_isProper_of_pointBlowupChain_unconditional hchain hX
  have hZint := hZsurface.isIntegral
  have hpbirational : IsBirational p :=
    isBirational_of_pointBlowupChain_of_isIntegralRegularSurface hchain hX
  have hqbirational : IsBirational q :=
    isBirational_of_resolves_partialIso pIso p q hpbirational hagree
  have hqproper : IsProper q := by
    have hcomp : IsProper (p ≫ (X ↘ S)) := inferInstance
    rw [← hqS] at hcomp
    exact IsProper.of_comp q (Y ↘ S)
  exact ⟨Z, p, q, hqS.symm,
    ⟨Z, p, pointBlowupChain_univ hchain, Iso.refl Z, by simp⟩,
    factorsAsPointBlowups_of_isProper_of_isBirational q hY hZsurface hqproper hqbirational⟩

end Stacks.ResolutionOfSurfaces

end
