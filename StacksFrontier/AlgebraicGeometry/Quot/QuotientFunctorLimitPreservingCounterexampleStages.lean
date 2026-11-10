module

public import StacksFrontier.AlgebraicGeometry.Quot.QuotientFunctorLimitPreservingCounterexample
public import Mathlib.Algebra.Category.Ring.Constructions
public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.AlgebraicGeometry.Pullbacks
public import Mathlib.Data.Finsupp.Encodable
public import Mathlib.Data.Rat.Encodable
public import Mathlib.Algebra.Polynomial.Cardinal
public import Mathlib.Algebra.MvPolynomial.Cardinal

/-!
# The stages of the counterexample to Stacks 082Q as written

The commutative algebra of the stages `T_g = Spec ℚ[t]_g` of the counterexample of
`StacksFrontier/AlgebraicGeometry/Quot/QuotientFunctorLimitPreservingCounterexample.lean`, in the
form in which the algebraic-space argument consumes it.

## Main results

* `AlgebraicGeometry.QuotientFunctorCounterexample.false_of_flat_of_finitePresentation`: the
  algebra of the counterexample read through ring isomorphisms: a nonzero cyclic module of
  finite presentation over `R ≅ R_g` which is flat over `A ≅ ℚ[t]_g` does not exist.
* `AlgebraicGeometry.QuotientFunctorCounterexample.isPushout_fibreRing`: `R_g` is the base change
  of `B₀ = R_1` along `ℚ[t] → ℚ[t]_g`, as a pushout of rings in the universe `u`.
* `AlgebraicGeometry.QuotientFunctorCounterexample.isColimitFractionCocone`: `ℚ(t)` is the
  filtered colimit of the rings `ℚ[t]_g`, `g ≠ 0`, in the universe `u`.

## Implementation notes

The base ring `ℚ[t]` is `StageRing 1 = ℚ[t]_1` and `B₀` is `FibreRing 1`, so that the transition
maps and the base change maps are the special cases `g = 1` of maps between stages.  The rings are
lifted to the universe of the schemes with `ULift`.

## References

* [Stacks Project, Tag 082Q](https://stacks.math.columbia.edu/tag/082Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Polynomial

universe u

namespace AlgebraicGeometry.QuotientFunctorCounterexample

/-- The polynomial ring `ℚ[t]` is countable. -/
theorem countable_polynomial : Countable ℚ[X] := by
  rw [← Cardinal.mk_le_aleph0_iff, Polynomial.cardinalMk_eq_max]
  exact max_le Cardinal.mk_le_aleph0 le_rfl

attribute [local instance] countable_polynomial

/-- The localization `ℚ[t]_g` is countable. -/
theorem countable_stageRing (g : ℚ[X]) : Countable (StageRing g) :=
  Function.Surjective.countable
    (IsLocalization.mk'_surjective (Submonoid.powers g) (S := StageRing g))

attribute [local instance] countable_stageRing

/-- The fibre ring `R_g` is countable. -/
theorem countable_fibreRing (g : ℚ[X]) : Countable (FibreRing g) :=
  have : Countable (MvPolynomial ℚ (StageRing g)) := by
    rw [← Cardinal.mk_le_aleph0_iff]
    refine (MvPolynomial.cardinalMk_le_max).trans ?_
    exact max_le (max_le Cardinal.mk_le_aleph0 Cardinal.mk_le_aleph0) le_rfl
  Function.Surjective.countable (Ideal.Quotient.mk_surjective (I := relations g))

/-- The field of rational functions `ℚ(t)` is countable. -/
theorem countable_fractionRing : Countable (FractionRing ℚ[X]) :=
  Function.Surjective.countable
    (IsLocalization.mk'_surjective (nonZeroDivisors ℚ[X]) (S := FractionRing ℚ[X]))

/-! ### The transition maps -/

/-- If `g ∣ h`, then `g` is a unit in `ℚ[t]_h`. -/
theorem isUnit_algebraMap_of_dvd {g h : ℚ[X]} (hgh : g ∣ h) :
    IsUnit (algebraMap ℚ[X] (StageRing h) g) := by
  obtain ⟨k, rfl⟩ := hgh
  exact isUnit_of_mul_isUnit_left (x := algebraMap ℚ[X] (StageRing (g * k)) g)
    (y := algebraMap ℚ[X] (StageRing (g * k)) k)
    (by rw [← map_mul]; exact IsLocalization.Away.algebraMap_isUnit (g * k))

/-- The transition map `ℚ[t]_g → ℚ[t]_h` for `g ∣ h`. -/
def stageMap {g h : ℚ[X]} (hgh : g ∣ h) : StageRing g →+* StageRing h :=
  IsLocalization.Away.lift g (isUnit_algebraMap_of_dvd hgh)

/-- The transition map `ℚ[t]_g → ℚ[t]_h` sends the image of a polynomial `p` to the image of
`p`. -/
theorem stageMap_algebraMap {g h : ℚ[X]} (hgh : g ∣ h) (p : ℚ[X]) :
    stageMap hgh (algebraMap ℚ[X] (StageRing g) p) = algebraMap ℚ[X] (StageRing h) p :=
  IsLocalization.lift_eq _ _

/-- The transition map `ℚ[t]_g → ℚ[t]_h` is a map of `ℚ[t]`-algebras. -/
theorem stageMap_comp_algebraMap {g h : ℚ[X]} (hgh : g ∣ h) :
    (stageMap hgh).comp (algebraMap ℚ[X] (StageRing g)) = algebraMap ℚ[X] (StageRing h) :=
  RingHom.ext (stageMap_algebraMap hgh)

/-- Two ring maps out of `ℚ[t]_g` agreeing on `ℚ[t]` are equal. -/
theorem stageRing_ringHom_ext {g : ℚ[X]} {A : Type*} [CommRing A] {φ ψ : StageRing g →+* A}
    (h : φ.comp (algebraMap ℚ[X] (StageRing g)) = ψ.comp (algebraMap ℚ[X] (StageRing g))) :
    φ = ψ :=
  IsLocalization.ringHom_ext (Submonoid.powers g) h

/-- The transition map `ℚ[t]_g → ℚ[t]_g` is the identity. -/
theorem stageMap_refl (g : ℚ[X]) : stageMap (dvd_refl g) = RingHom.id (StageRing g) :=
  stageRing_ringHom_ext (by rw [stageMap_comp_algebraMap]; rfl)

/-- The transition maps compose: `ℚ[t]_g → ℚ[t]_h → ℚ[t]_k` is `ℚ[t]_g → ℚ[t]_k`. -/
theorem stageMap_trans {g h k : ℚ[X]} (hgh : g ∣ h) (hhk : h ∣ k) :
    (stageMap hhk).comp (stageMap hgh) = stageMap (hgh.trans hhk) :=
  stageRing_ringHom_ext (by
    rw [RingHom.comp_assoc, stageMap_comp_algebraMap, stageMap_comp_algebraMap,
      stageMap_comp_algebraMap])

/-- The maps `ℚ[t]_g → ℚ(t)` are compatible with the transition maps. -/
theorem toFraction_comp_stageMap {g h : ℚ[X]} (hgh : g ∣ h) (hg : g ≠ 0) (hh : h ≠ 0) :
    (toFraction hh).comp (stageMap hgh) = toFraction hg :=
  stageRing_ringHom_ext (by
    rw [RingHom.comp_assoc, stageMap_comp_algebraMap]
    exact RingHom.ext fun p => (toFraction_algebraMap hh p).trans (toFraction_algebraMap hg p).symm)

/-! ### Ring maps out of the fibre ring -/

/-- Two ring maps out of `R_g` agreeing on `ℚ[t]_g` and on the `y_a` are equal. -/
theorem fibreRing_ringHom_ext {g : ℚ[X]} {A : Type*} [CommRing A] {φ ψ : FibreRing g →+* A}
    (h₁ : φ.comp (algebraMap (StageRing g) (FibreRing g)) =
      ψ.comp (algebraMap (StageRing g) (FibreRing g)))
    (h₂ : ∀ a, φ (y g a) = ψ (y g a)) : φ = ψ := by
  refine Ideal.Quotient.ringHom_ext (MvPolynomial.ringHom_ext (fun c => ?_) (fun a => h₂ a))
  simpa [algebraMap_fibreRing] using congrArg (fun k => k c) h₁

/-- The base change map `B₀ = R_1 → R_g`. -/
def fibreMap (g : ℚ[X]) : FibreRing 1 →+* FibreRing g :=
  lift ((algebraMap (StageRing g) (FibreRing g)).comp (stageMap (one_dvd g))) (y g) (fun a => by
    rw [RingHom.comp_apply, stageMap_algebraMap]
    exact algebraMap_mul_y a)

/-- The base change map `R_1 → R_g` sends `y_a` to `y_a`. -/
theorem fibreMap_y (g : ℚ[X]) (a : ℚ) : fibreMap g (y 1 a) = y g a :=
  lift_y _ _ _ a

/-- The base change map `R_1 → R_g` restricts to the transition map `ℚ[t]_1 → ℚ[t]_g`. -/
theorem fibreMap_algebraMap (g : ℚ[X]) (c : StageRing 1) :
    fibreMap g (algebraMap (StageRing 1) (FibreRing 1) c) =
      algebraMap (StageRing g) (FibreRing g) (stageMap (one_dvd g) c) :=
  lift_algebraMap _ _ _ c

/-- The generic point `B₀ → ℚ(t)` of `X = Spec B₀`, `y_a ↦ 0`. -/
abbrev genericFibre : FibreRing 1 →+* FractionRing ℚ[X] := generic one_ne_zero

/-- The map `B₀ → ℚ(t)` restricts to `ℚ[t]_1 → ℚ(t)`. -/
theorem genericFibre_algebraMap (c : StageRing 1) :
    genericFibre (algebraMap (StageRing 1) (FibreRing 1) c) = toFraction one_ne_zero c :=
  lift_algebraMap _ _ _ c

/-! ### The commutative algebra of the stage, in an abstract form -/

/-- **The algebra behind the failure of Stacks 082Q, read through ring isomorphisms.**  Let
`A ≅ ℚ[t]_g` and `R ≅ R_g` compatibly with the structure maps, and let `M` be an `R`-module of
finite presentation, flat over `A`, which is a nonzero quotient of `R`.  This is impossible:
flatness kills the images of the `y_a`, and then `M` is a quotient of `R/(y_a) ≅ ℚ[t]_g` whose
kernel is a nonzero-divisor-free ideal, so `M ≅ R/(y_a)`, whose kernel is not finitely
generated. -/
theorem false_of_flat_of_finitePresentation {g : ℚ[X]} (hg : g ≠ 0) {A R : Type*} [CommRing A]
    [CommRing R] (φ : A →+* R) (α : A ≃+* StageRing g) (β : R ≃+* FibreRing g)
    (hαβ : ∀ c, β (φ c) = algebraMap (StageRing g) (FibreRing g) (α c))
    (M : Type*) [AddCommGroup M] [Module R M]
    (hflat : letI : Module A M := Module.compHom M φ; Module.Flat A M)
    (hfp : Module.FinitePresentation R M) (σ : R →ₗ[R] M) (hσ : Function.Surjective σ)
    (h1 : σ 1 ≠ 0) : False := by
  let _ : Module A M := Module.compHom M φ
  have := isDomain_stageRing hg
  have : IsDomain A := α.toMulEquiv.isDomain
  -- a nonzero element of `A` acts injectively on `M`
  have hreg : ∀ c : A, c ≠ 0 → ∀ m : M, φ c • m = 0 → m = 0 := fun c hc m hm =>
    Module.Flat.isSMulRegular_of_nonZeroDivisors (R := A) (M := M)
      (mem_nonZeroDivisors_of_ne_zero hc)
      (show c • m = c • (0 : M) from hm.trans (smul_zero c).symm)
  have hσφ : ∀ r : R, σ r = r • σ 1 := fun r => by rw [← σ.map_smul, smul_eq_mul, mul_one]
  let J : Ideal R := LinearMap.ker σ
  have hJfg : J.FG := Module.FinitePresentation.fg_ker σ hσ
  let J' : Ideal (FibreRing g) := J.comap (β.symm : FibreRing g →+* R)
  have hJ'fg : J'.FG := by
    have h := hJfg.map (β : R →+* FibreRing g)
    rwa [Ideal.map_comap_of_equiv] at h
  have hmem : ∀ r', r' ∈ J' ↔ σ (β.symm r') = 0 := fun r' => Iff.rfl
  have hy : ∀ a, y g a ∈ J' := fun a => by
    rw [hmem]
    let c : A := α.symm (algebraMap ℚ[X] (StageRing g) (X - C a))
    have hc : c ≠ 0 := (map_ne_zero_iff _ α.symm.injective).2
      ((map_ne_zero_iff _ (IsLocalization.injective (StageRing g) (powers_le hg))).2
        (X_sub_C_ne_zero a))
    have hprod : φ c * β.symm (y g a) = 0 := by
      apply β.injective
      rw [map_mul, hαβ, β.apply_symm_apply, map_zero, RingEquiv.apply_symm_apply]
      exact algebraMap_mul_y a
    refine hreg c hc _ ?_
    rw [← σ.map_smul, smul_eq_mul, hprod, map_zero]
  have hyle : yIdeal g ≤ J' := Ideal.span_le.2 (by rintro _ ⟨a, rfl⟩; exact hy a)
  have hle : J' ≤ yIdeal g := by
    intro r' hr'
    have hsub := sub_retraction_mem r'
    have halg : algebraMap (StageRing g) (FibreRing g) (retraction r') ∈ J' := by
      have := J'.sub_mem hr' (hyle hsub)
      rwa [sub_sub_cancel] at this
    let x : A := α.symm (retraction r')
    have hx : β.symm (algebraMap (StageRing g) (FibreRing g) (retraction r')) = φ x := by
      apply β.injective
      rw [RingEquiv.apply_symm_apply, hαβ, RingEquiv.apply_symm_apply]
    rw [hmem, hx, hσφ] at halg
    by_cases hx0 : x = 0
    · have hr0 : retraction r' = 0 := (map_eq_zero_iff _ α.symm.injective).1 hx0
      simpa [hr0] using hsub
    · exact absurd (hreg x hx0 _ halg) h1
  exact not_fg_yIdeal hg (le_antisymm hle hyle ▸ hJ'fg)

/-! ### The rings in the universe of the schemes -/

/-- A commutative ring of `Type`, lifted to the universe `u`. -/
abbrev uR (R : Type) [CommRing R] : CommRingCat.{u} := CommRingCat.of (ULift.{u} R)

/-- A ring map of `Type`, lifted to the universe `u`. -/
abbrev uHom {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) : uR.{u} R ⟶ uR.{u} S :=
  CommRingCat.ofHom ((ULift.ringEquiv.symm.toRingHom.comp φ).comp ULift.ringEquiv.toRingHom)

/-- The lifted ring map `uHom φ` acts as `φ` on the underlying elements. -/
theorem uHom_apply {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (x : ULift.{u} R) :
    uHom.{u} φ x = ULift.up (φ x.down) := rfl

/-- Lifting ring maps to the universe `u` preserves composition. -/
theorem uHom_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (φ : R →+* S)
    (ψ : S →+* T) : uHom.{u} φ ≫ uHom.{u} ψ = uHom.{u} (ψ.comp φ) := rfl

/-- Lifting ring maps to the universe `u` preserves identities. -/
theorem uHom_id (R : Type) [CommRing R] : uHom.{u} (RingHom.id R) = 𝟙 (uR.{u} R) := rfl

/-- Equal ring maps have equal lifts to the universe `u`. -/
theorem uHom_congr {R S : Type} [CommRing R] [CommRing S] {φ ψ : R →+* S} (h : φ = ψ) :
    uHom.{u} φ = uHom.{u} ψ := h ▸ rfl

/-- The square formed by `ℚ[t]_1 → R_1 → R_g` and `ℚ[t]_1 → ℚ[t]_g → R_g` commutes. -/
theorem fibreMap_comp_algebraMap (g : ℚ[X]) :
    (fibreMap g).comp (algebraMap (StageRing 1) (FibreRing 1)) =
      (algebraMap (StageRing g) (FibreRing g)).comp (stageMap (one_dvd g)) :=
  RingHom.ext (fibreMap_algebraMap g)

/-- Given ring maps `a : R_1 → Z` and `b : ℚ[t]_g → Z` agreeing on `ℚ[t]_1`, the image of
`t - c` under `b` times the image of `y_c` under `a` vanishes. -/
theorem pushoutLift_rel (g : ℚ[X]) {Z : CommRingCat.{u}} (a : uR.{u} (FibreRing 1) ⟶ Z)
    (b : uR.{u} (StageRing g) ⟶ Z)
    (h : uHom.{u} (algebraMap (StageRing 1) (FibreRing 1)) ≫ a =
      uHom.{u} (stageMap (one_dvd g)) ≫ b) (c : ℚ) :
    (b.hom.comp ULift.ringEquiv.symm.toRingHom) (algebraMap ℚ[X] (StageRing g) (X - C c)) *
      a (ULift.up (y 1 c)) = 0 := by
  have e2 : a (ULift.up (algebraMap (StageRing 1) (FibreRing 1)
      (algebraMap ℚ[X] (StageRing 1) (X - C c)))) =
      b (ULift.up (stageMap (one_dvd g) (algebraMap ℚ[X] (StageRing 1) (X - C c)))) :=
    ConcreteCategory.congr_hom h _
  rw [RingHom.comp_apply, ← stageMap_algebraMap (one_dvd g)]
  change b (ULift.up _) * _ = _
  rw [← e2, ← map_mul]
  change a (ULift.up (algebraMap (StageRing 1) (FibreRing 1) _ * y 1 c)) = 0
  rw [algebraMap_mul_y]
  exact map_zero a.hom

/-- The map out of `R_g` induced by a cocone on the square of `isPushout_fibreRing`. -/
def pushoutLift (g : ℚ[X]) {Z : CommRingCat.{u}} (a : uR.{u} (FibreRing 1) ⟶ Z)
    (b : uR.{u} (StageRing g) ⟶ Z)
    (h : uHom.{u} (algebraMap (StageRing 1) (FibreRing 1)) ≫ a =
      uHom.{u} (stageMap (one_dvd g)) ≫ b) :
    uR.{u} (FibreRing g) ⟶ Z :=
  CommRingCat.ofHom ((lift (b.hom.comp ULift.ringEquiv.symm.toRingHom)
    (fun c => a (ULift.up (y 1 c))) (pushoutLift_rel g a b h)).comp ULift.ringEquiv.toRingHom)

/-- The map `pushoutLift g a b h` restricts to `b` on `ℚ[t]_g`. -/
theorem pushoutLift_apply_algebraMap (g : ℚ[X]) {Z : CommRingCat.{u}}
    (a : uR.{u} (FibreRing 1) ⟶ Z) (b : uR.{u} (StageRing g) ⟶ Z)
    (h : uHom.{u} (algebraMap (StageRing 1) (FibreRing 1)) ≫ a =
      uHom.{u} (stageMap (one_dvd g)) ≫ b) (c : StageRing g) :
    pushoutLift g a b h (ULift.up (algebraMap (StageRing g) (FibreRing g) c)) = b (ULift.up c) :=
  lift_algebraMap _ _ (pushoutLift_rel g a b h) c

/-- The map `pushoutLift g a b h` sends `y_c` to the image of `y_c` under `a`. -/
theorem pushoutLift_apply_y (g : ℚ[X]) {Z : CommRingCat.{u}}
    (a : uR.{u} (FibreRing 1) ⟶ Z) (b : uR.{u} (StageRing g) ⟶ Z)
    (h : uHom.{u} (algebraMap (StageRing 1) (FibreRing 1)) ≫ a =
      uHom.{u} (stageMap (one_dvd g)) ≫ b) (c : ℚ) :
    pushoutLift g a b h (ULift.up (y g c)) = a (ULift.up (y 1 c)) :=
  lift_y _ _ (pushoutLift_rel g a b h) c

/-- Two maps out of `R_g`, lifted, agree as soon as they agree on `ℚ[t]_g` and on the `y_a`. -/
theorem uR_fibreRing_hom_ext {g : ℚ[X]} {Z : CommRingCat.{u}} {φ ψ : uR.{u} (FibreRing g) ⟶ Z}
    (h₁ : ∀ c, φ (ULift.up (algebraMap (StageRing g) (FibreRing g) c)) =
      ψ (ULift.up (algebraMap (StageRing g) (FibreRing g) c)))
    (h₂ : ∀ a, φ (ULift.up (y g a)) = ψ (ULift.up (y g a))) : φ = ψ := by
  have key : φ.hom.comp ULift.ringEquiv.symm.toRingHom =
      ψ.hom.comp ULift.ringEquiv.symm.toRingHom :=
    fibreRing_ringHom_ext (RingHom.ext fun c => h₁ c) h₂
  ext x
  exact congrArg (fun k => k x.down) key

/-- **`R_g` is the base change of `B₀ = R_1` to `ℚ[t]_g`**: the square of rings is a pushout. -/
theorem isPushout_fibreRing (g : ℚ[X]) :
    IsPushout (uHom.{u} (algebraMap (StageRing 1) (FibreRing 1)))
      (uHom.{u} (stageMap (one_dvd g))) (uHom.{u} (fibreMap g))
      (uHom.{u} (algebraMap (StageRing g) (FibreRing g))) := by
  have hcomm : uHom.{u} (algebraMap (StageRing 1) (FibreRing 1)) ≫ uHom.{u} (fibreMap g) =
      uHom.{u} (stageMap (one_dvd g)) ≫ uHom.{u} (algebraMap (StageRing g) (FibreRing g)) := by
    rw [uHom_comp, uHom_comp, fibreMap_comp_algebraMap]
  refine IsPushout.of_isColimit' ⟨hcomm⟩ (PushoutCocone.IsColimit.mk _
    (fun s => pushoutLift g s.inl s.inr s.condition) ?_ ?_ ?_)
  · intro s
    refine uR_fibreRing_hom_ext (fun c => ?_) (fun c => ?_)
    · change pushoutLift g s.inl s.inr s.condition
        (ULift.up (fibreMap g (algebraMap (StageRing 1) (FibreRing 1) c))) = _
      rw [fibreMap_algebraMap, pushoutLift_apply_algebraMap]
      exact (ConcreteCategory.congr_hom s.condition _).symm
    · change pushoutLift g s.inl s.inr s.condition (ULift.up (fibreMap g (y 1 c))) = _
      rw [fibreMap_y, pushoutLift_apply_y]
  · intro s
    ext x
    exact pushoutLift_apply_algebraMap g s.inl s.inr s.condition x.down
  · intro s m hl hr
    refine uR_fibreRing_hom_ext (fun c => ?_) (fun c => ?_)
    · rw [pushoutLift_apply_algebraMap]
      exact ConcreteCategory.congr_hom hr _
    · rw [pushoutLift_apply_y, ← fibreMap_y]
      exact ConcreteCategory.congr_hom hl _

/-! ### `ℚ(t)` is the filtered colimit of the `ℚ[t]_g` -/

/-- The nonzero polynomials `g`, in the universe `u`: the index of the inverse system of the
stages `T_g = Spec ℚ[t]_g`, ordered by `g ≤ h` when `h ∣ g`. -/
structure Stage : Type u where
  /-- The polynomial inverted at the stage. -/
  poly : ℚ[X]
  /-- It is nonzero. -/
  ne_zero : poly ≠ 0

/-- The order on stages: `i ≤ j` when `j.poly ∣ i.poly`. -/
instance : Preorder Stage.{u} where
  le i j := j.poly ∣ i.poly
  le_refl i := dvd_refl i.poly
  le_trans _ _ _ hij hjk := hjk.trans hij

/-- For stages, `i ≤ j` if and only if `j.poly ∣ i.poly`. -/
theorem Stage.le_def {i j : Stage.{u}} : i ≤ j ↔ j.poly ∣ i.poly := Iff.rfl

/-- Any two stages have a common lower bound, given by the product of their polynomials. -/
instance : IsDirected Stage.{u} (· ≥ ·) where
  directed i j := ⟨⟨i.poly * j.poly, mul_ne_zero i.ne_zero j.ne_zero⟩,
    dvd_mul_right i.poly j.poly, dvd_mul_left j.poly i.poly⟩

/-- There is a stage, the one with `g = 1`. -/
instance : Nonempty Stage.{u} := ⟨⟨1, one_ne_zero⟩⟩

/-- The stages form a cofiltered category. -/
instance : IsCofiltered Stage.{u} := inferInstance

/-- The rings `ℚ[t]_g` of the stages, with the transition maps. -/
def stageRingDiagram : Stage.{u}ᵒᵖ ⥤ CommRingCat.{u} where
  obj i := uR.{u} (StageRing i.unop.poly)
  map f := uHom.{u} (stageMap (leOfHom f.unop))
  map_id i := (uHom_congr (stageMap_refl i.unop.poly)).trans (uHom_id _)
  map_comp f g := (uHom_congr (stageMap_trans (leOfHom f.unop) (leOfHom g.unop))).symm.trans
    (uHom_comp _ _).symm

/-- The cocone `ℚ[t]_g → ℚ(t)`. -/
def fractionCocone : Cocone stageRingDiagram.{u} where
  pt := uR.{u} (FractionRing ℚ[X])
  ι :=
    { app i := uHom.{u} (toFraction i.unop.ne_zero)
      naturality i j f := by
        refine (uHom_comp _ _).trans ?_
        rw [toFraction_comp_stageMap]
        exact (Category.comp_id _).symm }

/-- The map `ℚ[t]_q → ℚ(t)` sends the fraction `p / q` to `p / q`. -/
theorem toFraction_mk' {q : ℚ[X]} (hq : q ≠ 0) (p : ℚ[X]) :
    toFraction hq (IsLocalization.mk' (StageRing q) p (⟨q, Submonoid.mem_powers q⟩ :
      Submonoid.powers q)) =
      IsLocalization.mk' (FractionRing ℚ[X]) p
        (⟨q, mem_nonZeroDivisors_of_ne_zero hq⟩ : nonZeroDivisors ℚ[X]) := by
  rw [IsLocalization.eq_mk'_iff_mul_eq, ← toFraction_algebraMap hq, ← toFraction_algebraMap hq,
    ← map_mul]
  exact congrArg _ (IsLocalization.mk'_spec (StageRing q) p ⟨q, Submonoid.mem_powers q⟩)

/-- **`ℚ(t)` is the filtered colimit of the `ℚ[t]_g`.** -/
def isColimitFractionCocone : IsColimit fractionCocone.{u} := by
  haveI : ReflectsColimitsOfShape Stage.{u}ᵒᵖ (forget CommRingCat.{u}) :=
    reflectsColimitsOfShape_of_reflectsIsomorphisms
  refine isColimitOfReflects (forget CommRingCat.{u})
    (Types.FilteredColimit.isColimitOf' _ _ ?_ ?_)
  · intro x
    obtain ⟨x, rfl⟩ : ∃ x' : FractionRing ℚ[X], ULift.up x' = x := ⟨ULift.down x, rfl⟩
    obtain ⟨⟨p, q⟩, rfl⟩ := IsLocalization.mk'_surjective (nonZeroDivisors ℚ[X]) x
    have hq : (q : ℚ[X]) ≠ 0 := nonZeroDivisors.ne_zero q.2
    refine ⟨Opposite.op ⟨q, hq⟩, ULift.up (IsLocalization.mk' (StageRing (q : ℚ[X])) p
      (⟨q, Submonoid.mem_powers _⟩ : Submonoid.powers (q : ℚ[X]))), ?_⟩
    exact congrArg ULift.up (toFraction_mk' hq p).symm
  · intro i a b hab
    refine ⟨i, 𝟙 i, ?_⟩
    have hab' : ULift.down (uHom.{u} (toFraction i.unop.ne_zero) a) =
        ULift.down (uHom.{u} (toFraction i.unop.ne_zero) b) := congrArg ULift.down hab
    have : a = b := ULift.ext (toFraction_injective i.unop.ne_zero hab')
    rw [this]

end AlgebraicGeometry.QuotientFunctorCounterexample
