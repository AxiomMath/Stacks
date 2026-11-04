module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import Mathlib.RingTheory.DiscreteValuationRing.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.KeyFormula.ComponentPushforward
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Basic
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Specialization of cycles over a discrete valuation ring

Let `R` be a discrete valuation ring with fraction field `K` and residue field `κ`, let
`f : X ⟶ Spec R` be locally of finite type and let `r ≥ 0`. The *specialization map*
`sp_{X/R} : Z_r(X_K) ⟶ Z_r(X_κ)` is the unique homomorphism commuting with locally finite sums
of cycles whose value on the fundamental cycle `[Z]` of an integral closed subscheme `Z ⊆ X_K`
of dimension `r` is `[\overline{Z}_κ]_r`, the `r`-cycle associated to the special fibre of the
scheme-theoretic image `\overline{Z}` of `Z ⟶ X`.

An integral closed subscheme of the generic fibre is the reduced closure of its generic point
`ξ`, so the construction is indexed by the points of the generic fibre: the scheme-theoretic
image of the reduced closure of `ξ` is `Stacks.Chow.specializationClosure`, its special fibre is
`Stacks.Chow.specializationSpecialFibre`, and the resulting `r`-cycle on `X_κ` is
`Stacks.Chow.specializationIntegralCycle`. A general `r`-cycle on `X_K` is a locally finite sum
`∑ a_ξ [Z_ξ]`, and its specialization is the corresponding locally finite sum of the
`[\overline{Z_ξ}_κ]_r`, computed coefficientwise; that is `Stacks.Chow.specializationCycle`.

## Main definitions

* `Stacks.Chow.fiberPointDimension` — the dimension of a point of a scheme-theoretic fibre, that
  is, its relative dimension over the spectrum of the residue field of its base point.
* `Stacks.Chow.fiberSubschemeCycle` — the cycle `[W]_r` of a closed subscheme `W` of a
  scheme-theoretic fibre.
* `Stacks.Chow.specializationClosure` — the scheme-theoretic image `\overline{Z} ⊆ X` of the
  reduced closure of a point of the generic fibre.
* `Stacks.Chow.specializationSpecialFibre` — its special fibre `\overline{Z}_κ`.
* `Stacks.Chow.specializationIntegralCycle` — the `r`-cycle `[\overline{Z}_κ]_r` on `X_κ`, the
  value of the specialization map on the fundamental cycle of `Z`.
* `Stacks.Chow.integralGenericCycle` — the fundamental cycle `[Z]` on the generic fibre.
* `Stacks.Chow.specializationCycle` and `Stacks.Chow.specializationCycleHom` — the
  specialization map `sp_{X/R} : Z_r(X_K) ⟶ Z_r(X_κ)`, as a map and as a homomorphism.

## Main results

* `Stacks.Chow.coe_support_specializationClosure` — the scheme-theoretic image of the reduced
  closure of `ξ` is supported on the closure in `X` of the image of `ξ`; in particular it is the
  integral closed subscheme of `X` with that generic point.
* `Stacks.Chow.specializationCycle_integralGenericCycle` — the specialization map sends `[Z]` to
  `[\overline{Z}_κ]_r`.
* `Stacks.Chow.hasSum_specializationCycle` — the specialization map commutes with locally finite
  sums: each coefficient of `sp_{X/R}(c)` is the sum of the contributions of the integral closed
  subschemes of dimension `r` occurring in `c`.
* `Stacks.Chow.specializationCycle_unique` — those two properties determine the specialization
  map.
* `Stacks.Chow.specializationClosure_eq_bot`,
  `Stacks.Chow.specializationSpecialFibre_eq_bot` — for a point of the generic fibre lying over
  the generic point of an irreducible reduced `X`, the scheme-theoretic image of its reduced
  closure is all of `X` and the special fibre of that image is all of `X_κ`.
* `Stacks.Chow.base_genericPoint_eq_genericPoint` — the generic point of an irreducible scheme
  flat over `Spec R` lies on the generic fibre.
* `Stacks.Chow.specializationCycle_fiberSubschemeCycle_bot` and
  `Stacks.Chow.specializationCycle_fiberSubschemeCycle_bot_of_flat` — the case `W = X` of
  Tag 0H4J: `sp_{X/R}([X_K]_r) = [X_κ]_r` for an irreducible reduced `X` with reduced generic
  fibre.

## Implementation notes

The specialization map is *defined* by the coefficientwise formula
`sp(c)(x) = ∑ᶠ ξ, c(ξ) * [\overline{Z_ξ}_κ]_r(x)`, not chosen from an existence statement; the
characterization by its values on fundamental cycles is then a theorem. Local finiteness of that
sum is the geometric input: a point of the special fibre can only receive a contribution from a
point `ξ` of the generic fibre whose image specializes to it, and the images of the points of
the support of a cycle on the generic fibre form a locally finite family of closures in `X`
because `X_K ⟶ X` is quasi-compact.

No dimension hypothesis is imposed on `ξ`: the fundamental cycle
`Stacks.Chow.integralGenericCycle` of a point of the wrong dimension is zero, and such a point
contributes nothing to a cycle in `Z_r(X_K)`.

Tag 0H4J computes `sp_{X/R}([W_K]_r)` for a closed subscheme `W ⊆ X` flat over `R` with
`dim(W_K) ≤ r`, and no `@[stacks 0H4J]` attribute is placed here: it is proved in general in
the theory of flat cycle classes, as
`Stacks.Chow.specializationCycle_familyAssociatedToClosedSubscheme_of_genericFibre`, out of the
length computation of Tag 0H4I. What is proved below is the case `W = X` for irreducible reduced
`X` with reduced generic fibre, where `[X_K]_r` and `[X_κ]_r` are the fundamental cycles of the
two fibres and every multiplicity involved is one, so that no length computation is needed.

## References

* [Stacks Project, Section 0H4H](https://stacks.math.columbia.edu/tag/0H4H)
* [Stacks Project, Tag 02QU](https://stacks.math.columbia.edu/tag/02QU)
* [Stacks Project, Tag 0H4J](https://stacks.math.columbia.edu/tag/0H4J)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace Stacks.Chow

/-! ### Locally finite families of coefficients -/

/-- A function with finite support is summable, with its locally finite sum as sum. -/
private theorem hasSum_finsum_of_hasFiniteSupport {ι A : Type*} [AddCommMonoid A]
    [TopologicalSpace A] (c : ι → A) (hc : Function.HasFiniteSupport c) :
    HasSum c (∑ᶠ i, c i) := by
  classical
  rw [finsum_eq_sum _ hc]
  exact hasSum_sum_of_ne_finset_zero fun i hi ↦ not_ne_iff.mp fun h ↦ hi (hc.mem_toFinset.mpr h)

/-- An integer multiple of a function with locally finite support has locally finite
support. -/
theorem locallyFiniteSupport_const_mul {Y : Type*} [TopologicalSpace Y] (n : ℤ)
    (c : Y → ℤ) (hc : LocallyFiniteSupport c) : LocallyFiniteSupport fun y ↦ n * c y := by
  intro y
  obtain ⟨t, ht, hfin⟩ := hc y
  refine ⟨t, ht, hfin.subset ?_⟩
  rintro z ⟨hzt, hz⟩
  refine ⟨hzt, fun h ↦ hz ?_⟩
  change n * c z = 0
  rw [h, mul_zero]

/-- The images under a spectral map of the points of the support of a function with locally
finite support form a locally finite family of singletons: every point of the target has a
quasi-compact open neighbourhood, whose inverse image is quasi-compact and therefore meets the
support in a finite set. -/
theorem locallyFinite_singleton_image {A Y : Type*} [TopologicalSpace A]
    [TopologicalSpace Y] [PrespectralSpace Y] (g : A → Y) (hg : IsSpectralMap g)
    (c : Function.locallyFinsupp A ℤ) :
    LocallyFinite fun a : Function.support c ↦ ({g a.1} : Set Y) := by
  intro y
  obtain ⟨U, hU⟩ := (PrespectralSpace.isTopologicalBasis (X := Y)).exists_subset_of_mem_open
    (show y ∈ (Set.univ : Set Y) from trivial) isOpen_univ
  refine ⟨U, hU.1.1.mem_nhds hU.2.1, ?_⟩
  have hfin := c.locallyFiniteSupport.finite_inter_support_of_isCompact (hg.2 hU.1.1 hU.1.2)
  have hpre := hfin.preimage (f := fun a : Function.support c ↦ a.1) Subtype.val_injective.injOn
  apply hpre.subset
  rintro a ⟨z, hz, hzU⟩
  have hz' : z = g a.1 := hz
  exact ⟨show g a.1 ∈ U from hz' ▸ hzU, a.2⟩

/-! ### Cycles on a scheme-theoretic fibre -/

/-- The dimension of a point `x` of the scheme-theoretic fibre of `f` over `s`: its relative
dimension over `Spec κ(s)`, taken for the Chow situation on the spectrum of the residue
field. -/
abbrev fiberPointDimension {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S)
    (x : f.fiber s) : ℤ :=
  relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
    (f.fiberToSpecResidueField s) x

/-- The `r`-cycle `[W]_r` of a closed subscheme `W` of the scheme-theoretic fibre of `f`
over `s`. -/
def fiberSubschemeCycle {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f] (s : S) (r : ℕ)
    (W : (f.fiber s).IdealSheafData) : FiberCycleGroup f s r :=
  cycleAssociatedToClosedSubscheme (fieldChowSituation (S.residueField s))
    (f.fiberToSpecResidueField s) W.subschemeι (r : ℤ)

/-- A point of the fibre which is not the image of the generic point of a component of `W` of
dimension `r` has coefficient zero in `[W]_r`. -/
theorem fiberSubschemeCycle_apply_eq_zero {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (s : S) (r : ℕ) (W : (f.fiber s).IdealSheafData) (x : f.fiber s)
    (hx : ¬ ∃ ξ : genericPoints W.subscheme,
      W.subschemeι ξ.1 = x ∧ fiberPointDimension f s x = (r : ℤ)) :
    (fiberSubschemeCycle f s r W).1 x = 0 :=
  cycleAssociatedToClosedSubscheme_apply_eq_zero _ _ _ _ x hx

/-- The fundamental cycle of the reduced closure of a point `x` of dimension `r` of the fibre
over `s` has coefficient one at `x`. -/
theorem fiberSubschemeCycle_integralComponentAt_self {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (s : S) (r : ℕ) (x : f.fiber s)
    (hx : fiberPointDimension f s x = (r : ℤ)) :
    (fiberSubschemeCycle f s r (integralComponentAt x)).1 x = 1 := by
  have hint : IsIntegral (integralComponentAt x).subscheme := isIntegral_integralComponentAt x
  have hgen : (integralComponentAt x).subschemeι.base
      (genericPoint (integralComponentAt x).subscheme) = x := by
    simpa [genericPointOf] using genericPointOf_integralComponentAt x
  have hdim : schemeDeltaDimension (fieldChowSituation (S.residueField s))
      ((integralComponentAt x).subschemeι ≫ f.fiberToSpecResidueField s) = ((r : ℤ) : EInt) := by
    rw [schemeDeltaDimension_eq_genericPoint, relativeDimension_comp_closedImmersion, hgen]
    exact congrArg (fun z : ℤ ↦ (z : EInt)) hx
  have h := cycleAssociatedToClosedSubscheme_integral_apply
    (fieldChowSituation (S.residueField s)) (f.fiberToSpecResidueField s)
    (integralComponentAt x) hint hdim
  rwa [genericPointOf_integralComponentAt] at h

/-- The fundamental cycle of the reduced closure of a point `x` of the fibre over `s` vanishes
at every other point of that fibre. -/
theorem fiberSubschemeCycle_integralComponentAt_of_ne {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (s : S) (r : ℕ) (x y : f.fiber s) (hy : y ≠ x) :
    (fiberSubschemeCycle f s r (integralComponentAt x)).1 y = 0 :=
  cycleAssociatedToClosedSubscheme_integral_apply_of_ne _ _ (integralComponentAt x)
    (isIntegral_integralComponentAt x) (r : ℤ) (by rwa [genericPointOf_integralComponentAt])

section Specialization

variable {R : Type u} [CommRing R] [IsDomain R] [IsDiscreteValuationRing R] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of R)) [LocallyOfFiniteType f] (r : ℕ)

/-! ### The schematic closure of an integral subscheme of the generic fibre -/

/-- The scheme-theoretic image `\overline{Z} ⊆ X` of the integral closed subscheme `Z` of the
generic fibre `X_K` whose generic point is `ξ`: the pushforward along `X_K ⟶ X` of the ideal
sheaf cutting out the reduced closure of `ξ`. -/
@[ega "IV 12.1.1.4" "partial"]
def specializationClosure (ξ : f.fiber (genericPoint (Spec (.of R)))) : X.IdealSheafData :=
  (integralComponentAt ξ).map (f.fiberι (genericPoint (Spec (.of R))))

omit [IsDiscreteValuationRing R] [LocallyOfFiniteType f] in
/-- The inclusion of the generic fibre is quasi-compact: it is a base change of the affine
morphism `Spec K ⟶ Spec R`. -/
private theorem quasiCompact_fiberι_genericPoint :
    QuasiCompact (f.fiberι (genericPoint (Spec (.of R)))) := by
  change QuasiCompact (pullback.fst f ((Spec (.of R)).fromSpecResidueField _))
  infer_instance

omit [IsDiscreteValuationRing R] [LocallyOfFiniteType f] in
/-- The scheme-theoretic image of the reduced closure of a point `ξ` of the generic fibre is
supported on the closure in `X` of the image of `ξ`. In particular it is the integral closed
subscheme of `X` whose generic point is that image, as the Stacks Project observes in Section
0H4H. -/
theorem coe_support_specializationClosure (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    ((specializationClosure f ξ).support : Set X) =
      closure ({f.fiberι (genericPoint (Spec (.of R))) ξ} : Set X) := by
  have := quasiCompact_fiberι_genericPoint f
  rw [specializationClosure, Scheme.IdealSheafData.support_map, Closeds.coe_closure,
    coe_support_integralComponentAt, ← Set.image_singleton]
  exact closure_image_closure (f.fiberι (genericPoint (Spec (.of R)))).continuous

/-- The special fibre `\overline{Z}_κ` of the scheme-theoretic image of the integral closed
subscheme of the generic fibre with generic point `ξ`: the inverse image in `X_κ` of the ideal
sheaf of `\overline{Z}`. -/
def specializationSpecialFibre (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    (f.fiber (IsLocalRing.closedPoint R)).IdealSheafData :=
  (specializationClosure f ξ).comap (f.fiberι (IsLocalRing.closedPoint R))

/-! ### Specialization of a fundamental cycle -/

/-- The fundamental cycle `[Z]` on the generic fibre of the integral closed subscheme
`Z ⊆ X_K` whose generic point is `ξ`. -/
def integralGenericCycle (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    FiberCycleGroup f (genericPoint (Spec (.of R))) r :=
  fiberSubschemeCycle f (genericPoint (Spec (.of R))) r (integralComponentAt ξ)

/-- `sp_{X/R}([Z])`: the `r`-cycle `[\overline{Z}_κ]_r` of the special fibre of the
scheme-theoretic image of the integral closed subscheme of the generic fibre with generic point
`ξ`. -/
def specializationIntegralCycle (ξ : f.fiber (genericPoint (Spec (.of R)))) :
    FiberCycleGroup f (IsLocalRing.closedPoint R) r :=
  fiberSubschemeCycle f (IsLocalRing.closedPoint R) r (specializationSpecialFibre f ξ)

/-- The coefficient of `[\overline{Z}_κ]_r` vanishes at every point of the special fibre whose
image in `X` is not a specialization of the image of `ξ`: the special fibre of the
scheme-theoretic image of `Z` lies over the closure of the image of `ξ`. -/
theorem specializationIntegralCycle_apply_eq_zero_of_not_specializes
    (ξ : f.fiber (genericPoint (Spec (.of R)))) (x : f.fiber (IsLocalRing.closedPoint R))
    (hx : ¬ f.fiberι (genericPoint (Spec (.of R))) ξ ⤳
      f.fiberι (IsLocalRing.closedPoint R) x) :
    (specializationIntegralCycle f r ξ).1 x = 0 := by
  apply fiberSubschemeCycle_apply_eq_zero
  rintro ⟨z, hz, -⟩
  apply hx
  rw [specializes_iff_mem_closure]
  have hmem : (specializationSpecialFibre f ξ).subschemeι.base z.1 ∈
      ((specializationSpecialFibre f ξ).support :
        Set (f.fiber (IsLocalRing.closedPoint R))) := by
    rw [← Scheme.IdealSheafData.range_subschemeι]
    exact Set.mem_range_self _
  rwa [hz, specializationSpecialFibre, Scheme.IdealSheafData.support_comap, Closeds.coe_preimage,
    coe_support_specializationClosure] at hmem

/-! ### The specialization map -/

/-- The terms of the coefficientwise sum defining the specialization map form a locally finite
family: a point of the special fibre only receives a contribution from the points of the generic
fibre whose image in `X` specializes to its image, and the closures of the images of the support
of a cycle on the generic fibre form a locally finite family in `X`. -/
theorem locallyFinite_support_specializationTerm
    (a : AlgebraicCycle (f.fiber (genericPoint (Spec (.of R)))) ℤ) :
    LocallyFinite fun ξ ↦
      Function.support fun x ↦ a ξ * (specializationIntegralCycle f r ξ).1 x := by
  have := quasiCompact_fiberι_genericPoint f
  have hlf := ((locallyFinite_singleton_image (f.fiberι (genericPoint (Spec (.of R))))
    (f.fiberι (genericPoint (Spec (.of R)))).isSpectralMap a).closure).preimage_continuous
      (f.fiberι (IsLocalRing.closedPoint R)).continuous
  intro x
  obtain ⟨U, hU, hfin⟩ := hlf x
  refine ⟨U, hU, (hfin.image Subtype.val).subset ?_⟩
  rintro ξ ⟨y, hy, hyU⟩
  have hy' : a ξ * (specializationIntegralCycle f r ξ).1 y ≠ 0 := hy
  refine ⟨⟨ξ, (mul_ne_zero_iff.mp hy').1⟩, ⟨y, ?_, hyU⟩, rfl⟩
  change f.fiberι (IsLocalRing.closedPoint R) y ∈
    closure ({f.fiberι (genericPoint (Spec (.of R))) ξ} : Set X)
  rw [← specializes_iff_mem_closure]
  by_contra h
  exact (mul_ne_zero_iff.mp hy').2
    (specializationIntegralCycle_apply_eq_zero_of_not_specializes f r ξ y h)

/-- At a fixed point of the special fibre only finitely many points of the generic fibre
contribute to the specialization. -/
private theorem hasFiniteSupport_specializationTerm
    (a : AlgebraicCycle (f.fiber (genericPoint (Spec (.of R)))) ℤ)
    (x : f.fiber (IsLocalRing.closedPoint R)) :
    Function.HasFiniteSupport fun ξ ↦ a ξ * (specializationIntegralCycle f r ξ).1 x := by
  have h := (locallyFinite_support_specializationTerm f r a).point_finite x
  simpa only [Function.HasFiniteSupport, Function.support, Function.mem_support,
    Set.mem_ofPred_eq] using h

/-- **Stacks Project, Section 0H4H.** The specialization map
`sp_{X/R} : Z_r(X_K) ⟶ Z_r(X_κ)` for a scheme locally of finite type over a discrete valuation
ring: the coefficient of `sp_{X/R}(c)` at a point `x` of the special fibre is the locally finite
sum, over the points `ξ` of the generic fibre, of the coefficient of `c` at `ξ` times the
coefficient at `x` of the `r`-cycle of the special fibre of the scheme-theoretic image of the
reduced closure of `ξ`. -/
def specializationCycle (c : FiberCycleGroup f (genericPoint (Spec (.of R))) r) :
    FiberCycleGroup f (IsLocalRing.closedPoint R) r := by
  refine ⟨⟨fun x ↦ ∑ᶠ ξ, c.1 ξ * (specializationIntegralCycle f r ξ).1 x,
    Set.subset_univ _, ?_⟩, ?_⟩
  · intro x _
    exact locallyFiniteSupport_finsum _ (locallyFinite_support_specializationTerm f r c.1)
      (fun ξ x ↦ c.1 ξ * (specializationIntegralCycle f r ξ).1 x)
      (fun ξ ↦ locallyFiniteSupport_const_mul _ _
        (specializationIntegralCycle f r ξ).1.locallyFiniteSupport)
      (fun _ ↦ subset_rfl) x
  · intro Z hZ
    by_contra hdim
    have hz (ξ) : (specializationIntegralCycle f r ξ).1 Z.isIrreducible.genericPoint = 0 := by
      by_contra hξ
      exact hdim ((specializationIntegralCycle f r ξ).2 Z hξ)
    change (∑ᶠ ξ, c.1 ξ * (specializationIntegralCycle f r ξ).1
      Z.isIrreducible.genericPoint) ≠ 0 at hZ
    simp only [hz, mul_zero, finsum_zero] at hZ
    exact hZ rfl

/-- The coefficientwise formula for the specialization map. -/
theorem specializationCycle_apply (c : FiberCycleGroup f (genericPoint (Spec (.of R))) r)
    (x : f.fiber (IsLocalRing.closedPoint R)) :
    (specializationCycle f r c).1 x =
      ∑ᶠ ξ, c.1 ξ * (specializationIntegralCycle f r ξ).1 x :=
  rfl

/-- The specialization of the zero cycle is zero. -/
@[simp]
theorem specializationCycle_zero :
    specializationCycle f r (0 : FiberCycleGroup f (genericPoint (Spec (.of R))) r) = 0 := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [specializationCycle_apply]
  simp

/-- The specialization map is additive. -/
theorem specializationCycle_add (c d : FiberCycleGroup f (genericPoint (Spec (.of R))) r) :
    specializationCycle f r (c + d) = specializationCycle f r c + specializationCycle f r d := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [specializationCycle_apply]
  change (∑ᶠ ξ, (c.1 ξ + d.1 ξ) * (specializationIntegralCycle f r ξ).1 x) =
    (∑ᶠ ξ, c.1 ξ * (specializationIntegralCycle f r ξ).1 x) +
      ∑ᶠ ξ, d.1 ξ * (specializationIntegralCycle f r ξ).1 x
  simp_rw [add_mul]
  exact finsum_add_distrib (hasFiniteSupport_specializationTerm f r c.1 x)
    (hasFiniteSupport_specializationTerm f r d.1 x)

/-- **Stacks Project, Section 0H4H.** The specialization map `sp_{X/R}` as a homomorphism of
cycle groups `Z_r(X_K) ⟶ Z_r(X_κ)`. -/
def specializationCycleHom :
    FiberCycleGroup f (genericPoint (Spec (.of R))) r →+
      FiberCycleGroup f (IsLocalRing.closedPoint R) r where
  toFun := specializationCycle f r
  map_zero' := specializationCycle_zero f r
  map_add' := specializationCycle_add f r

/-- The underlying map of `Stacks.Chow.specializationCycleHom` is
`Stacks.Chow.specializationCycle`. -/
@[simp]
theorem specializationCycleHom_apply (c : FiberCycleGroup f (genericPoint (Spec (.of R))) r) :
    specializationCycleHom f r c = specializationCycle f r c :=
  rfl

/-! ### The characterizing properties of the specialization map -/

/-- **Stacks Project, Section 0H4H.** The specialization map sends the fundamental cycle `[Z]`
of an integral closed subscheme of the generic fibre of dimension `r` to the `r`-cycle
`[\overline{Z}_κ]_r` of the special fibre of its scheme-theoretic image. -/
theorem specializationCycle_integralGenericCycle (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hξ : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)) :
    specializationCycle f r (integralGenericCycle f r ξ) = specializationIntegralCycle f r ξ := by
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  rw [specializationCycle_apply, finsum_eq_single _ ξ fun ζ hζ ↦ by
    rw [show (integralGenericCycle f r ξ).1 ζ = 0 from
      fiberSubschemeCycle_integralComponentAt_of_ne f _ r ξ ζ hζ, zero_mul],
    show (integralGenericCycle f r ξ).1 ξ = 1 from
      fiberSubschemeCycle_integralComponentAt_self f _ r ξ hξ, one_mul]

/-- **Stacks Project, Section 0H4H.** The specialization map commutes with locally finite sums
of cycles: at every point of the special fibre the coefficient of `sp_{X/R}(c)` is the sum, over
the points of the generic fibre of dimension `r`, of the coefficient of `c` there times the
corresponding coefficient of the specialized fundamental cycle. -/
theorem hasSum_specializationCycle (c : FiberCycleGroup f (genericPoint (Spec (.of R))) r)
    (x : f.fiber (IsLocalRing.closedPoint R)) :
    HasSum (fun ξ : {ξ : f.fiber (genericPoint (Spec (.of R))) //
        fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)} ↦
      c.1 ξ.1 * (specializationCycle f r (integralGenericCycle f r ξ.1)).1 x)
      ((specializationCycle f r c).1 x) := by
  have hterm : ∀ ξ : {ξ : f.fiber (genericPoint (Spec (.of R))) //
      fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)},
      c.1 ξ.1 * (specializationCycle f r (integralGenericCycle f r ξ.1)).1 x =
        c.1 ξ.1 * (specializationIntegralCycle f r ξ.1).1 x := fun ξ ↦ by
    rw [specializationCycle_integralGenericCycle f r ξ.1 ξ.2]
  simp_rw [hterm]
  rw [specializationCycle_apply]
  refine (hasSum_subtype_iff_of_support_subset ?_).2
    (hasSum_finsum_of_hasFiniteSupport _ (hasFiniteSupport_specializationTerm f r c.1 x))
  intro ξ hξ
  exact (mem_cyclesOfDimension_iff_forall_point _ _ (r : ℤ) c.1).mp c.2 ξ
    (mul_ne_zero_iff.mp hξ).1

/-- **Stacks Project, Section 0H4H.** The specialization map is the *unique* map on cycle groups
which commutes with locally finite sums of cycles and whose value on the fundamental cycle of an
integral closed subscheme `Z ⊆ X_K` of dimension `r` is `[\overline{Z}_κ]_r`. -/
theorem specializationCycle_unique
    (sp : FiberCycleGroup f (genericPoint (Spec (.of R))) r →
      FiberCycleGroup f (IsLocalRing.closedPoint R) r)
    (hsp : ∀ ξ : f.fiber (genericPoint (Spec (.of R))),
      fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ) →
      sp (integralGenericCycle f r ξ) = specializationIntegralCycle f r ξ)
    (hloc : ∀ (c : FiberCycleGroup f (genericPoint (Spec (.of R))) r)
      (x : f.fiber (IsLocalRing.closedPoint R)),
      HasSum (fun ξ : {ξ : f.fiber (genericPoint (Spec (.of R))) //
          fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)} ↦
        c.1 ξ.1 * (sp (integralGenericCycle f r ξ.1)).1 x) ((sp c).1 x)) :
    sp = specializationCycle f r := by
  have hterm : ∀ ξ : {ξ : f.fiber (genericPoint (Spec (.of R))) //
      fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)},
      sp (integralGenericCycle f r ξ.1) = specializationCycle f r (integralGenericCycle f r ξ.1) :=
    fun ξ ↦ (hsp ξ.1 ξ.2).trans (specializationCycle_integralGenericCycle f r ξ.1 ξ.2).symm
  simp only [hterm] at hloc
  funext c
  apply Subtype.ext
  apply Function.locallyFinsuppWithin.ext
  intro x
  exact (hloc c x).unique (hasSum_specializationCycle f r c x)

/-! ### Specialization of the fundamental cycle of the whole generic fibre -/

/-- On a reduced scheme the reduced closure of a dense point is the whole scheme: its support is
everything, and on a reduced scheme the only ideal sheaf with full support is the zero one. -/
private theorem integralComponentAt_eq_bot_of_closure_eq_univ {Y : Scheme.{u}} [IsReduced Y]
    (y : Y) (hy : closure ({y} : Set Y) = Set.univ) : integralComponentAt y = ⊥ := by
  rw [← Scheme.IdealSheafData.support_eq_top_iff]
  exact TopologicalSpace.Closeds.ext (by rw [coe_support_integralComponentAt, hy]; rfl)

omit [IsDiscreteValuationRing R] [LocallyOfFiniteType f] in
/-- If `ξ` is a point of the generic fibre lying over the generic point of an irreducible reduced
`X`, then the scheme-theoretic image of the reduced closure of `ξ` is the whole of `X`: that
image is supported on the closure of the image of `ξ`, which is everything. -/
theorem specializationClosure_eq_bot [IsReduced X] [IrreducibleSpace X]
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hξ : f.fiberι (genericPoint (Spec (.of R))) ξ = genericPoint X) :
    specializationClosure f ξ = ⊥ := by
  rw [← Scheme.IdealSheafData.support_eq_top_iff]
  refine TopologicalSpace.Closeds.ext ?_
  rw [coe_support_specializationClosure, hξ]
  exact genericPoint_spec X

omit [LocallyOfFiniteType f] in
/-- For such a `ξ` the special fibre of the scheme-theoretic image of the reduced closure of `ξ`
is the whole special fibre `X_κ`. -/
theorem specializationSpecialFibre_eq_bot [IsReduced X] [IrreducibleSpace X]
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hξ : f.fiberι (genericPoint (Spec (.of R))) ξ = genericPoint X) :
    specializationSpecialFibre f ξ = ⊥ := by
  rw [specializationSpecialFibre, specializationClosure_eq_bot f ξ hξ,
    Scheme.IdealSheafData.comap_bot]

omit [IsDiscreteValuationRing R] [LocallyOfFiniteType f] in
/-- A point of the generic fibre lying over the generic point of an irreducible `X` is dense in
that fibre: the generic fibre carries the subspace topology of `X`, in which the closure of such
a point is the trace of the closure of the generic point of `X`. -/
@[ega "0 2.1.8" "special case"]
theorem closure_eq_univ_of_fiberι_eq_genericPoint [IrreducibleSpace X]
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hξ : f.fiberι (genericPoint (Spec (.of R))) ξ = genericPoint X) :
    closure ({ξ} : Set (f.fiber (genericPoint (Spec (.of R))))) = Set.univ := by
  rw [(f.fiberι (genericPoint (Spec (.of R)))).isEmbedding.closure_eq_preimage_closure_image,
    Set.image_singleton, hξ, genericPoint_spec X]
  exact Set.preimage_univ

omit [IsDiscreteValuationRing R] in
/-- If the generic fibre is reduced and `ξ` lies over the generic point of the irreducible `X`,
then the fundamental cycle of the reduced closure of `ξ` is the cycle `[X_K]_r` of the whole
generic fibre. -/
theorem integralGenericCycle_eq_fiberSubschemeCycle_bot [IrreducibleSpace X]
    [IsReduced (f.fiber (genericPoint (Spec (.of R))))]
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hξ : f.fiberι (genericPoint (Spec (.of R))) ξ = genericPoint X) :
    integralGenericCycle f r ξ = fiberSubschemeCycle f (genericPoint (Spec (.of R))) r ⊥ := by
  rw [integralGenericCycle, integralComponentAt_eq_bot_of_closure_eq_univ ξ
    (closure_eq_univ_of_fiberι_eq_genericPoint f ξ hξ)]

/-- **The case `W = X` of Stacks Project, Tag 0H4J.** Let `R` be a discrete valuation ring with
fraction field `K` and residue field `κ` and let `X` be an irreducible reduced scheme locally of
finite type over `R` whose generic fibre is reduced. If the point `ξ` of `X_K` over the generic
point of `X` has dimension `r`, then the specialization homomorphism `sp_{X/R}` of
Section 0H4H carries the cycle `[X_K]_r` of the generic fibre to the cycle `[X_κ]_r` of the
special fibre.

No `@[stacks 0H4J]` attribute is placed: the tag is the statement for an arbitrary closed
subscheme `W ⊆ X` flat over `R` with `dim(W_K) ≤ r`, whose coefficients are the multiplicities
of the components of `W_K` and of `W_κ`, and whose proof is the length computation of
Tag 0H4I; that general statement is
`Stacks.Chow.specializationCycle_familyAssociatedToClosedSubscheme_of_genericFibre`. Here
`W = X` is reduced and irreducible, so every multiplicity in sight is one and no length
computation is needed. -/
theorem specializationCycle_fiberSubschemeCycle_bot [IsReduced X] [IrreducibleSpace X]
    [IsReduced (f.fiber (genericPoint (Spec (.of R))))]
    (ξ : f.fiber (genericPoint (Spec (.of R))))
    (hξ : f.fiberι (genericPoint (Spec (.of R))) ξ = genericPoint X)
    (hdim : fiberPointDimension f (genericPoint (Spec (.of R))) ξ = (r : ℤ)) :
    specializationCycle f r (fiberSubschemeCycle f (genericPoint (Spec (.of R))) r ⊥) =
      fiberSubschemeCycle f (IsLocalRing.closedPoint R) r ⊥ := by
  rw [← integralGenericCycle_eq_fiberSubschemeCycle_bot f r ξ hξ,
    specializationCycle_integralGenericCycle f r ξ hdim]
  change fiberSubschemeCycle f (IsLocalRing.closedPoint R) r (specializationSpecialFibre f ξ) = _
  rw [specializationSpecialFibre_eq_bot f ξ hξ]

omit [IsDiscreteValuationRing R] [LocallyOfFiniteType f] in
/-- The generic point of an irreducible scheme flat over `Spec R` lies over the generic point of
`Spec R`: flatness lifts the generization of its image to a generization of it, and a
generization of the generic point is the generic point. -/
theorem base_genericPoint_eq_genericPoint [Flat f] [IrreducibleSpace X] :
    f.base (genericPoint X) = genericPoint (Spec (.of R)) := by
  obtain ⟨ζ, hζ, hfζ⟩ := Flat.generalizingMap f
    (genericPoint_specializes (f.base (genericPoint X)))
  have hdense : closure ({ζ} : Set X) = Set.univ :=
    Set.eq_univ_of_univ_subset <| (genericPoint_spec X).symm.trans_le <|
      closure_minimal (Set.singleton_subset_iff.mpr hζ.mem_closure) isClosed_closure
  rw [← IsGenericPoint.eq hdense (genericPoint_spec X)]
  exact hfζ

/-- **The case `W = X` of Stacks Project, Tag 0H4J**, for a flat `X`. Let `R` be a discrete
valuation ring with fraction field `K` and residue field `κ` and let `X` be an irreducible
reduced scheme locally of finite type and flat over `R` with integral generic fibre. If the
generic point of `X_K` has dimension `r`, then `sp_{X/R}([X_K]_r) = [X_κ]_r`.

Flatness is used only to place the generic point of `X` on the generic fibre; the statement
above it imposes no flatness and asks instead for a point of `X_K` over that generic point. -/
theorem specializationCycle_fiberSubschemeCycle_bot_of_flat [Flat f] [IsReduced X]
    [IrreducibleSpace X] [IsIntegral (f.fiber (genericPoint (Spec (.of R))))]
    (hdim : fiberPointDimension f (genericPoint (Spec (.of R)))
      (genericPoint (f.fiber (genericPoint (Spec (.of R))))) = (r : ℤ)) :
    specializationCycle f r (fiberSubschemeCycle f (genericPoint (Spec (.of R))) r ⊥) =
      fiberSubschemeCycle f (IsLocalRing.closedPoint R) r ⊥ := by
  have hmem : genericPoint X ∈ Set.range (f.fiberι (genericPoint (Spec (.of R)))) := by
    rw [Scheme.Hom.range_fiberι]
    exact base_genericPoint_eq_genericPoint f
  obtain ⟨ξ, hξ⟩ := hmem
  have hgen : ξ = genericPoint (f.fiber (genericPoint (Spec (.of R)))) :=
    IsGenericPoint.eq (closure_eq_univ_of_fiberι_eq_genericPoint f ξ hξ)
      (genericPoint_spec (f.fiber (genericPoint (Spec (.of R)))))
  exact specializationCycle_fiberSubschemeCycle_bot f r ξ hξ (hgen ▸ hdim)

end Specialization

end Stacks.Chow

end
