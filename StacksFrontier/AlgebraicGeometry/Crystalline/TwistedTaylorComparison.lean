module

public import StacksFrontier.AlgebraicGeometry.Crystalline.TaylorConvergence

/-!
# The twisted Taylor comparison of [Stacks, Tag 07JH]

The proof of [Stacks, Proposition 60.17.4, Tag 07JH] uses, for a pair `(M, ∇)`, the comparison

`c_{f,g} : M ⊗_{D,f} B ⟶ M ⊗_{D,g} B`,  `m ⊗ 1 ↦ ∑_K θ_K(m) ⊗ ∏_i ξ_i^{[k_i]}`,

for two divided power maps `f, g : D → B` agreeing modulo the divided power ideal `J_B` of an
object of `Cris(X/S)`, with `ξ_i = f(x_i) - g(x_i) ∈ J_B`.  Source and target carry different
`D`-algebra structures, so on generators the comparison obeys the twisted rule
`T(a · m) = f(a) · T(m)`.  This module formalizes the second divided power map `f` and the
twisted comparison, and relates it to `Crystalline.IsTaylorComparison`, which has a single
`Algebra D B` and is the case `f = g`.

## Main definitions

* `Crystalline.SecondDividedPowerMap`: a divided power map `f : D → B` agreeing with the structure
  map `g = algebraMap D B` modulo `J_B`.
* `Crystalline.SecondDividedPowerMap.diffFamily`: the family `ξ_i = f(x_i) - g(x_i)`.
* `Crystalline.IsTwistedTaylorComparison`: the Taylor series `∑_K ξ^{[K]} ⊗ θ_K(m)` converges to
  `T m` for an `f`-semilinear `T : M →ₛₗ[f] B ⊗_D M`.
* `Crystalline.HasTwistedTaylorComparison`: the existence form of the previous predicate.
* `Crystalline.taylorFirstOrderPart`, `Crystalline.taylorRemainder`: the parts of the series in
  total degree `≤ 1` and `≥ 2`.

## Main results

* `Crystalline.SecondDividedPowerMap.diffFamily_mem`: the differences `ξ_i` lie in `J_B`.
* `Crystalline.ringHom_eq_algebraMap_of_untwisted` and
  `Crystalline.ringHom_eq_algebraMap_of_untwisted_self`: a twisted comparison whose Taylor sums
  also satisfy the untwisted identity `∑_K ξ^{[K]} ⊗ θ_K(a m) = a · T m` forces `f = g`; for
  `M = D` it suffices that `T 1 = 1 ⊗ 1`.
* `Crystalline.isTaylorComparison_liftBaseChange_of_eq_algebraMap`: when `f = g` a twisted
  comparison gives a `Crystalline.IsTaylorComparison`.
* `Crystalline.hasTaylorSum_smul_of_isTwistedTaylorComparison`: a twisted comparison satisfies
  `∑_K ξ^{[K]} ⊗ θ_K(a m) = f(a) · ∑_K ξ^{[K]} ⊗ θ_K(m)`.
* `Crystalline.exists_isTwistedTaylorComparison_of_sum`: the twisted comparison exists as soon as
  the Taylor sums form an additive, `f`-semilinear function of `m`.
* `Crystalline.isTwistedTaylorComparison_refl`: the twisted comparison for the identity datum
  `Crystalline.SecondDividedPowerMap.refl`, with `ξ = 0` and `T m = 1 ⊗ m`.
* `Crystalline.hasTaylorSum_split_degree` and
  `Crystalline.hasTaylorSum_of_taylorRemainder_eq_zero`: the series splits by total degree, and
  when the remainder in degree `≥ 2` vanishes the sum is the part in degree `≤ 1`.

## References

* [Stacks Project, Proposition 60.17.4, Tag 07JH](https://stacks.math.columbia.edu/tag/07JH)
* [Stacks Project, Lemma 60.17.3, Tag 07JG](https://stacks.math.columbia.edu/tag/07JG)
* [Stacks Project, Tag 07JE](https://stacks.math.columbia.edu/tag/07JE)
* [Stacks Project, Tag 07GU](https://stacks.math.columbia.edu/tag/07GU)
* [Stacks Project, Tag 07HM](https://stacks.math.columbia.edu/tag/07HM)
-/

@[expose] public section

open scoped TensorProduct

universe u uI

namespace Crystalline

/-! ### The second divided power map -/

section Datum

variable (D : DividedPowerRing.{u}) (B : DividedPowerRing.{u})
  [Algebra (D : Type u) (B : Type u)] {ι : Type uI}

/-- **The second divided power map of the proof of [Stacks, Tag 07JH]**: a divided power map
`f : D → B` agreeing with the structure map `g = algebraMap D B` modulo the divided power ideal
`J_B` of `B`. -/
structure SecondDividedPowerMap where
  /-- The divided power map `f : D → B`. -/
  hom : DividedPowers.DPMorphism D.dividedPowers B.dividedPowers
  /-- `f` and `g = algebraMap D B` agree modulo the divided power ideal of `B`. -/
  sub_algebraMap_mem : ∀ a : (D : Type u),
    hom a - algebraMap (D : Type u) (B : Type u) a ∈ B.ideal

namespace SecondDividedPowerMap

variable {D B}

/-- The ring homomorphism underlying the second divided power map. -/
def ringHom (f : SecondDividedPowerMap D B) : (D : Type u) →+* (B : Type u) := f.hom.toRingHom

/-- The ring homomorphism underlying the datum has the datum's divided power map for its
underlying function. -/
@[simp] theorem ringHom_apply (f : SecondDividedPowerMap D B) (a : (D : Type u)) :
    f.ringHom a = f.hom a :=
  rfl

/-- **The family `ξ_i = f(x_i) - g(x_i)` of the proof of [Stacks, Tag 07JH]**, read off the datum
and a family `x : ι → D` of coordinates. -/
def diffFamily (f : SecondDividedPowerMap D B) (x : ι → (D : Type u)) : ι → (B : Type u) :=
  fun i ↦ f.hom (x i) - algebraMap (D : Type u) (B : Type u) (x i)

/-- **The differences `ξ_i` lie in the divided power ideal of `B`.** -/
theorem diffFamily_mem (f : SecondDividedPowerMap D B) (x : ι → (D : Type u)) (i : ι) :
    f.diffFamily x i ∈ B.ideal :=
  f.sub_algebraMap_mem (x i)

/-- **The differences vanish exactly when the two divided power maps agree on the coordinates.** -/
theorem diffFamily_eq_zero_iff (f : SecondDividedPowerMap D B) (x : ι → (D : Type u)) :
    f.diffFamily x = 0 ↔ ∀ i, f.hom (x i) = algebraMap (D : Type u) (B : Type u) (x i) := by
  simp [diffFamily, funext_iff, sub_eq_zero]

end SecondDividedPowerMap

end Datum

/-! ### The twisted Taylor comparison -/

section Twisted

variable (p : ℕ) (D : DividedPowerRing.{u}) (B : DividedPowerRing.{u})
  [Algebra (D : Type u) (B : Type u)] (M : Type u) [AddCommGroup M] [Module (D : Type u) M]
  {ι : Type uI} (f : SecondDividedPowerMap D B) (thetaPow : (ι →₀ ℕ) → (M → M))

/-- **The Taylor comparison of the proof of [Stacks, Tag 07JH], twisted as the source has it.**
The datum is an `f`-semilinear map `T : M →ₛₗ[f] B ⊗_D M`, that is one with
`T (a · m) = f(a) · T(m)`, and the condition is that the Taylor series

`∑_K ξ^{[K]} ⊗ θ_K(m)`

converges to `T m` in the `p`-adic topology of `B ⊗_D M` for every `m`. -/
def IsTwistedTaylorComparison (xi : ι → (B : Type u))
    (T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M)) : Prop :=
  ∀ m : M, HasTaylorSum p D B M thetaPow xi m (T m)

/-- **The twisted form of `Crystalline.HasTaylorComparison`**: for every family `ξ` of elements
of the divided power ideal of `B` there is an `f`-semilinear map whose values are the sums of the
Taylor series. -/
def HasTwistedTaylorComparison : Prop :=
  ∀ xi : ι → (B : Type u), (∀ i, xi i ∈ B.ideal) →
    ∃ T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M),
      IsTwistedTaylorComparison p D B M f thetaPow xi T

variable {p D B M f thetaPow}

/-- **The twisted comparison is the convergence of the series at the values of `T`.** -/
theorem isTwistedTaylorComparison_iff_hasTaylorSum (xi : ι → (B : Type u))
    (T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M)) :
    IsTwistedTaylorComparison p D B M f thetaPow xi T ↔
      ∀ m : M, HasTaylorSum p D B M thetaPow xi m (T m) :=
  Iff.rfl

/-- A twisted comparison satisfies

`∑_K ξ^{[K]} ⊗ θ_K(a m) = f(a) · ∑_K ξ^{[K]} ⊗ θ_K(m)`    for every `a ∈ D` and `m ∈ M`. -/
theorem hasTaylorSum_smul_of_isTwistedTaylorComparison {xi : ι → (B : Type u)}
    {T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M)}
    (hT : IsTwistedTaylorComparison p D B M f thetaPow xi T) (a : (D : Type u)) (m : M) :
    HasTaylorSum p D B M thetaPow xi (a • m) (f.ringHom a • T m) := by
  simpa only [map_smulₛₗ] using hT (a • m)

/-- **A twisted comparison exists as soon as the Taylor sums assemble into an additive,
`f`-semilinear function** `Tfun` of `m`. -/
theorem exists_isTwistedTaylorComparison_of_sum (xi : ι → (B : Type u))
    (Tfun : M → (B : Type u) ⊗[(D : Type u)] M)
    (hsum : ∀ m : M, HasTaylorSum p D B M thetaPow xi m (Tfun m))
    (hadd : ∀ m m' : M, Tfun (m + m') = Tfun m + Tfun m')
    (hsmul : ∀ (a : (D : Type u)) (m : M), Tfun (a • m) = f.ringHom a • Tfun m) :
    ∃ T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M),
      IsTwistedTaylorComparison p D B M f thetaPow xi T :=
  ⟨{ toFun := Tfun, map_add' := hadd, map_smul' := hsmul }, hsum⟩

end Twisted

/-! ### The case `f = g` -/

section Shadow

variable {p : ℕ} {D : DividedPowerRing.{u}} {B : DividedPowerRing.{u}}
  [Algebra (D : Type u) (B : Type u)] {M : Type u} [AddCommGroup M] [Module (D : Type u) M]
  {ι : Type uI} {f : SecondDividedPowerMap D B} {thetaPow : (ι →₀ ℕ) → (M → M)}

/-- **An `f`-semilinear map with `f = g` is a `D`-linear map.** -/
def SecondDividedPowerMap.toLinearMapOfEq
    (hf : f.ringHom = algebraMap (D : Type u) (B : Type u))
    (T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M)) :
    M →ₗ[(D : Type u)] ((B : Type u) ⊗[(D : Type u)] M) where
  toFun := T
  map_add' := T.map_add
  map_smul' a m := by
    rw [map_smulₛₗ, DFunLike.congr_fun hf a, algebraMap_smul]
    rfl

/-- The `D`-linear map `SecondDividedPowerMap.toLinearMapOfEq hf T` has the same values as `T`. -/
@[simp] theorem SecondDividedPowerMap.toLinearMapOfEq_apply
    (hf : f.ringHom = algebraMap (D : Type u) (B : Type u))
    (T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M)) (m : M) :
    f.toLinearMapOfEq hf T m = T m :=
  rfl

/-- **At `f = g` a twisted comparison gives a `Crystalline.IsTaylorComparison`.**  The `B`-linear
extension of the `D`-linear map underlying a twisted comparison with `f = algebraMap D B` is a
`Crystalline.IsTaylorComparison`. -/
theorem isTaylorComparison_liftBaseChange_of_eq_algebraMap
    (hf : f.ringHom = algebraMap (D : Type u) (B : Type u)) {xi : ι → (B : Type u)}
    {T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M)}
    (hT : IsTwistedTaylorComparison p D B M f thetaPow xi T) :
    IsTaylorComparison p D B M thetaPow xi
      ((f.toLinearMapOfEq hf T).liftBaseChange (B : Type u)) :=
  isTaylorComparison_liftBaseChange p D B M xi _ hT

/-- **An untwisted comparison forces `f = g`.**  Let `T` be a twisted comparison for the datum
`f`.  If the Taylor sums are also untwisted, in the sense that the series at `a · m` converges to
`a · T m` (`huntwisted`), if sums are unique (`huniq`) and if no nonzero element of `B` annihilates
`T m` (`hannih`), then `f(a) = g(a)`. -/
theorem ringHom_eq_algebraMap_of_untwisted {xi : ι → (B : Type u)}
    {T : M →ₛₗ[f.ringHom] ((B : Type u) ⊗[(D : Type u)] M)}
    (hT : IsTwistedTaylorComparison p D B M f thetaPow xi T)
    (huniq : ∀ (m : M) (t t' : (B : Type u) ⊗[(D : Type u)] M),
      HasTaylorSum p D B M thetaPow xi m t → HasTaylorSum p D B M thetaPow xi m t' → t = t')
    (huntwisted : ∀ (a : (D : Type u)) (m : M),
      HasTaylorSum p D B M thetaPow xi (a • m) (a • T m))
    {m : M} (hannih : ∀ b : (B : Type u), b • T m = 0 → b = 0) (a : (D : Type u)) :
    f.ringHom a = algebraMap (D : Type u) (B : Type u) a := by
  have htw : T (a • m) = f.ringHom a • T m := map_smulₛₗ T a m
  have hun : T (a • m) = a • T m := huniq (a • m) _ _ (hT (a • m)) (huntwisted a m)
  refine sub_eq_zero.mp (hannih _ ?_)
  rw [sub_smul, algebraMap_smul, ← htw, ← hun, sub_self]

/-- **An untwisted comparison forces `f = g`, for `M = D`.**  Let `T` be a twisted comparison for
the module `D` with `T 1 = 1 ⊗ 1`.  If sums of Taylor series are unique (`huniq`) and the Taylor
sums are untwisted (`huntwisted`), then the two divided power maps agree. -/
theorem ringHom_eq_algebraMap_of_untwisted_self {D B : DividedPowerRing.{u}}
    [Algebra D.carrier B.carrier] {f : SecondDividedPowerMap D B} {p : ℕ} {ι : Type uI}
    {thetaPow : (ι →₀ ℕ) → D.carrier → D.carrier} {xi : ι → B.carrier}
    {T : D.carrier →ₛₗ[f.ringHom] (B.carrier ⊗[D.carrier] D.carrier)}
    (hT : IsTwistedTaylorComparison p D B D.carrier f thetaPow xi T)
    (huniq : ∀ (m t t' : _),
      HasTaylorSum p D B D.carrier thetaPow xi m t →
        HasTaylorSum p D B D.carrier thetaPow xi m t' → t = t')
    (huntwisted : ∀ a m : D.carrier,
      HasTaylorSum p D B D.carrier thetaPow xi (a • m) (a • T m))
    (hone : T 1 = (1 : B.carrier) ⊗ₜ[D.carrier] (1 : D.carrier)) (a : D.carrier) :
    f.ringHom a = algebraMap D.carrier B.carrier a := by
  refine ringHom_eq_algebraMap_of_untwisted hT huniq huntwisted (m := 1) (fun b hb ↦ ?_) a
  have h := congrArg (TensorProduct.AlgebraTensorModule.rid D.carrier B.carrier B.carrier) hb
  rw [hone, map_smul, map_zero] at h
  simpa using h

end Shadow

/-! ### The identity datum -/

section Satisfiable

variable (p : ℕ) (D : DividedPowerRing.{u}) {ι : Type uI}

/-- **The identity datum**: the identity divided power map of `D`, which agrees with the structure
map of `D` over itself. -/
def SecondDividedPowerMap.refl : SecondDividedPowerMap D D where
  hom := DividedPowers.DPMorphism.id D.dividedPowers
  sub_algebraMap_mem a := by
    change a - a ∈ D.ideal
    simp

/-- **The twisted comparison for the identity datum.**  For the identity datum `f = g`, no
coordinate differences (`ξ = 0`) and composite coordinate operators vanishing away from the empty
multi-index, the map `T m = 1 ⊗ m` is a twisted comparison. -/
theorem isTwistedTaylorComparison_refl
    (thetaPow : (ι →₀ ℕ) → D.carrier → D.carrier) (hzero : thetaPow 0 = _root_.id)
    (hne : ∀ K : ι →₀ ℕ, K ≠ 0 → thetaPow K = 0) :
    IsTwistedTaylorComparison p D D D.carrier (SecondDividedPowerMap.refl D) thetaPow 0
      (TensorProduct.mk D.carrier D.carrier D.carrier 1) := by
  classical
  intro m
  have hterms : ∀ K ∉ ({0} : Finset (ι →₀ ℕ)),
      taylorMonomial D (0 : ι → D.carrier) K ⊗ₜ[D.carrier] thetaPow K m = 0 := by
    intro K hK
    simp [hne K (by simpa using hK)]
  have h := hasTaylorSum_of_eq_zero p D D D.carrier thetaPow (0 : ι → D.carrier) m
    ({0} : Finset (ι →₀ ℕ)) hterms
  rwa [Finset.sum_singleton, taylorMonomial_zero, hzero] at h

end Satisfiable

/-! ### The series by total degree -/

section Degree

variable (p : ℕ) (D : DividedPowerRing.{u}) (B : DividedPowerRing.{u})
  [Algebra (D : Type u) (B : Type u)] (M : Type u) [AddCommGroup M] [Module (D : Type u) M]
  {ι : Type uI} (thetaPow : (ι →₀ ℕ) → (M → M))

/-- **The part of the Taylor series of [Stacks, Tag 07JH] in total degree `≤ 1`**, summed over a
finite set `s` of multi-indices. -/
noncomputable def taylorFirstOrderPart (xi : ι → (B : Type u)) (m : M) (s : Finset (ι →₀ ℕ)) :
    (B : Type u) ⊗[(D : Type u)] M :=
  ∑ K ∈ s with K.degree ≤ 1, taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K m

/-- **The remainder of the Taylor series of [Stacks, Tag 07JH] in total degree `≥ 2`**, summed over
a finite set `s` of multi-indices. -/
noncomputable def taylorRemainder (xi : ι → (B : Type u)) (m : M) (s : Finset (ι →₀ ℕ)) :
    (B : Type u) ⊗[(D : Type u)] M :=
  ∑ K ∈ s with ¬ K.degree ≤ 1, taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K m

/-- **The Taylor series splits by total degree.**  A series with finitely many nonzero terms, all
inside `s`, converges to the sum of its degree `≤ 1` part and its degree `≥ 2` remainder. -/
theorem hasTaylorSum_split_degree (xi : ι → (B : Type u)) (m : M) (s : Finset (ι →₀ ℕ))
    (hs : ∀ K ∉ s, taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K m = 0) :
    HasTaylorSum p D B M thetaPow xi m
      (taylorFirstOrderPart D B M thetaPow xi m s +
        taylorRemainder D B M thetaPow xi m s) := by
  rw [taylorFirstOrderPart, taylorRemainder,
    Finset.sum_filter_add_sum_filter_not s (fun K : ι →₀ ℕ ↦ K.degree ≤ 1)]
  exact hasTaylorSum_of_eq_zero p D B M thetaPow xi m s hs

/-- **When the degree `≥ 2` remainder vanishes, the series converges to its degree `≤ 1` part**
`Crystalline.taylorFirstOrderPart`. -/
theorem hasTaylorSum_of_taylorRemainder_eq_zero (xi : ι → (B : Type u)) (m : M)
    (s : Finset (ι →₀ ℕ))
    (hs : ∀ K ∉ s, taylorMonomial B xi K ⊗ₜ[(D : Type u)] thetaPow K m = 0)
    (hrem : taylorRemainder D B M thetaPow xi m s = 0) :
    HasTaylorSum p D B M thetaPow xi m (taylorFirstOrderPart D B M thetaPow xi m s) := by
  simpa only [hrem, add_zero] using hasTaylorSum_split_degree p D B M thetaPow xi m s hs

end Degree

end Crystalline
