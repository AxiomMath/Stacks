module

public import Mathlib.Algebra.Ring.Fin
public import Mathlib.RingTheory.LocalRing.Pullback
public import Mathlib.RingTheory.MvPowerSeries.Equiv
public import StacksFrontier.AlgebraicGeometry.Curves.Node.Multicross
public import StacksFrontier.RingTheory.CompleteLocalRing.Regular
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Power series whose constant coefficient lies in the base

Let `k` be a field and `K` a commutative `k`-algebra. This file studies the subring
```
{f ∈ K⟦s⟧ : f(0) ∈ k}
```
of the power series over `K` whose constant coefficient comes from `k`. It is the completed local
ring of the point obtained by gluing the branches of a curve whose completed local rings are the
`K⟦s⟧` for the factors `K` of a finite product, and as such it is a fibre product: it is the
pullback of `k ⟶ K` along the constant coefficient `K⟦s⟧ ⟶ K`.

Two comparisons make that description usable. Power series over a product ring are the product of
the power series rings over the factors (`PowerSeries.piRingEquiv`), coefficientwise; and over a
product of copies of `k` itself the subring above becomes the multicross ring
`Stacks.Curves.multicross k n` of tuples of power series with a common constant coefficient,
which for two factors is `k⟦x, y⟧/(xy)` by `Stacks.Curves.quotientAlgEquivMulticross`.

## Main definitions

* `PowerSeries.piRingEquiv` — power series over a product ring, read coefficientwise.
* `PowerSeries.mapRingEquiv` — the isomorphism of power series rings induced by one of the
  coefficient rings.
* `PowerSeries.finOneRingEquiv` — power series in one variable as multivariable power series
  indexed by `Fin 1`.
* `PowerSeries.constantCoeffInBase` — the subring `{f ∈ K⟦s⟧ : f(0) ∈ k}`.

## Main results

* `PowerSeries.nonempty_ringEquiv_constantCoeffInBase_of_isPullback_data` — the fibre product of
  `k` and a ring isomorphic to `K⟦s⟧` over `K` is `{f ∈ K⟦s⟧ : f(0) ∈ k}`.
* `PowerSeries.nonempty_ringEquiv_constantCoeffInBase_congr` — the construction only depends on
  the `k`-algebra `K` up to isomorphism.
* `PowerSeries.nonempty_ringEquiv_multicross` — over `K = kⁿ` it is the multicross ring.
* `PowerSeries.exists_ringEquiv_powerSeries_of_isRegularLocalRing` — a complete regular local
  algebra of dimension one over a field is the power series ring over a field it surjects onto,
  compatibly with the surjection.
* `IsLocalRing.exists_residueFieldRingEquiv_of_surjective` — a surjection from a local ring onto
  a field identifies that field with the residue field.

## Implementation notes

`PowerSeries.constantCoeffInBase` is a `Subring`, not a `Subalgebra`: only ring isomorphisms are
compared below, and the three subrings in play — this one, `Stacks.Curves.multicross` and
Mathlib's `RingHom.pullback` — are then all of the same kind, so `RingEquiv.restrict` serves for
each comparison.

One-variable power series over a product are a product of power series rings for an arbitrary
index type, not only a finite one: the forward map is `PowerSeries.map` of the projections and is
bijective coefficientwise. (The polynomial analogue, `Polynomial.piEquiv`, needs finiteness for
its support argument.)

## References

* [Stacks Project, Tag 0C0S](https://stacks.math.columbia.edu/tag/0C0S)
* [Stacks Project, Tag 0C1U](https://stacks.math.columbia.edu/tag/0C1U)
* [Stacks Project, Tag 0E36](https://stacks.math.columbia.edu/tag/0E36)
-/

@[expose] public noncomputable section

universe u v w

namespace PowerSeries

/-! ### Power series over a product ring -/

/-- **Power series over a product of rings are the product of the power series rings over the
factors.** The isomorphism applies the projections coefficientwise. -/
def piRingEquiv {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)] :
    PowerSeries (∀ i, R i) ≃+* ∀ i, PowerSeries (R i) where
  toFun f i := PowerSeries.map (Pi.evalRingHom R i) f
  invFun g := PowerSeries.mk fun n i => PowerSeries.coeff n (g i)
  left_inv f := by
    refine PowerSeries.ext fun n => ?_
    rw [coeff_mk]
    funext i
    exact coeff_map (Pi.evalRingHom R i) n f
  right_inv g := by
    funext i
    refine PowerSeries.ext fun n => ?_
    rw [coeff_map, coeff_mk]
    rfl
  map_mul' f g := funext fun i => map_mul (PowerSeries.map (Pi.evalRingHom R i)) f g
  map_add' f g := funext fun i => map_add (PowerSeries.map (Pi.evalRingHom R i)) f g

/-- The `i`-th component of `piRingEquiv R f` is the image of `f` under the `i`-th projection,
applied coefficientwise. -/
@[simp]
theorem piRingEquiv_apply {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)]
    (f : PowerSeries (∀ i, R i)) (i : ι) :
    piRingEquiv R f i = PowerSeries.map (Pi.evalRingHom R i) f :=
  rfl

/-- The constant coefficient of the `i`-th component of `piRingEquiv R f` is the `i`-th
component of the constant coefficient of `f`. -/
@[simp]
theorem constantCoeff_piRingEquiv {ι : Type*} (R : ι → Type*) [∀ i, CommRing (R i)]
    (f : PowerSeries (∀ i, R i)) (i : ι) :
    constantCoeff (piRingEquiv R f i) = constantCoeff f i :=
  rfl

/-- **An isomorphism of coefficient rings induces an isomorphism of power series rings.** -/
def mapRingEquiv {R : Type*} {S : Type*} [CommRing R] [CommRing S] (e : R ≃+* S) :
    PowerSeries R ≃+* PowerSeries S where
  toFun := PowerSeries.map (e : R →+* S)
  invFun := PowerSeries.map (e.symm : S →+* R)
  left_inv f := by
    refine PowerSeries.ext fun n => ?_
    rw [coeff_map, coeff_map]
    exact e.symm_apply_apply _
  right_inv f := by
    refine PowerSeries.ext fun n => ?_
    rw [coeff_map, coeff_map]
    exact e.apply_symm_apply _
  map_mul' := map_mul (PowerSeries.map (e : R →+* S))
  map_add' := map_add (PowerSeries.map (e : R →+* S))

/-- The constant coefficient of `mapRingEquiv e f` is the image under `e` of the constant
coefficient of `f`. -/
@[simp]
theorem constantCoeff_mapRingEquiv {R : Type*} {S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (f : PowerSeries R) :
    constantCoeff (mapRingEquiv e f) = e (constantCoeff f) :=
  rfl

/-! ### The power series with constant coefficient in the base -/

/-- The subring `{f ∈ K⟦s⟧ : f(0) ∈ k}` of the power series over a `k`-algebra `K` whose constant
coefficient comes from `k`. -/
def constantCoeffInBase (k : Type*) (K : Type*) [CommRing k] [CommRing K] [Algebra k K] :
    Subring (PowerSeries K) where
  carrier := {f | constantCoeff f ∈ Set.range (algebraMap k K)}
  one_mem' := ⟨1, by rw [map_one, map_one]⟩
  mul_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a * b, by rw [map_mul, map_mul, ha, hb]⟩
  zero_mem' := ⟨0, by rw [map_zero, map_zero]⟩
  add_mem' := by
    rintro f g ⟨a, ha⟩ ⟨b, hb⟩
    exact ⟨a + b, by rw [map_add, map_add, ha, hb]⟩
  neg_mem' := by
    rintro f ⟨a, ha⟩
    exact ⟨-a, by rw [map_neg, map_neg, ha]⟩

/-- A power series lies in `constantCoeffInBase k K` if and only if its constant coefficient lies
in the image of `algebraMap k K`. -/
@[simp]
theorem mem_constantCoeffInBase {k : Type*} {K : Type*} [CommRing k] [CommRing K] [Algebra k K]
    (f : PowerSeries K) :
    f ∈ constantCoeffInBase k K ↔ constantCoeff f ∈ Set.range (algebraMap k K) :=
  Iff.rfl

/-- **The power series with constant coefficient in the base are a fibre product.**  Let `k` be a
field, `K` a nontrivial `k`-algebra and `g : S →+* K` a ring map carried to the constant
coefficient of `K⟦s⟧` by an isomorphism `Θ : S ≃+* K⟦s⟧`.  Then the fibre product of
`algebraMap k K` and `g` is the ring of power series over `K` whose constant coefficient lies in
`k`.

The fibre product is Mathlib's `RingHom.pullback`, the subring of pairs with the same image. The
first coordinate of such a pair is determined by the second, `algebraMap k K` being injective, so
the projection to the second coordinate is injective; its image consists of those `a` with `g a`
in the image of `k`, which through `Θ` is the asserted condition on the constant coefficient. -/
theorem nonempty_ringEquiv_constantCoeffInBase_of_isPullback_data
    (k : Type*) (K : Type*) (S : Type*) [Field k] [CommRing K] [Nontrivial K] [Algebra k K]
    [CommRing S] (g : S →+* K) (Θ : S ≃+* PowerSeries K)
    (hΘ : ∀ a, constantCoeff (Θ a) = g a) :
    Nonempty (↥(RingHom.pullback (algebraMap k K) g) ≃+* ↥(constantCoeffInBase k K)) := by
  have hinj : Function.Injective (algebraMap k K) := (algebraMap k K).injective
  have hpair : ∀ p : ↥(RingHom.pullback (algebraMap k K) g),
      algebraMap k K (p : k × S).1 = g (p : k × S).2 :=
    fun p => RingHom.mem_eqLocus.mp p.2
  have hmem : ∀ p : ↥(RingHom.pullback (algebraMap k K) g),
      Θ (p : k × S).2 ∈ constantCoeffInBase k K := by
    intro p
    refine ⟨(p : k × S).1, ?_⟩
    rw [hΘ]
    exact hpair p
  refine ⟨RingEquiv.ofBijective
    (RingHom.codRestrict (Θ.toRingHom.comp (RingHom.pullbackSnd (algebraMap k K) g))
      (constantCoeffInBase k K) hmem) ⟨?_, ?_⟩⟩
  · intro p q hpq
    have h2 : (p : k × S).2 = (q : k × S).2 :=
      Θ.injective (congrArg Subtype.val hpq)
    have h1 : (p : k × S).1 = (q : k × S).1 := by
      refine hinj ?_
      rw [hpair p, hpair q]
      exact congrArg g h2
    exact Subtype.ext (Prod.ext h1 h2)
  · rintro ⟨f, c, hc⟩
    refine ⟨⟨(c, Θ.symm f), ?_⟩, Subtype.ext ?_⟩
    · refine RingHom.mem_eqLocus.mpr ?_
      change algebraMap k K c = g (Θ.symm f)
      rw [← hΘ, Θ.apply_symm_apply, hc]
    · change Θ (Θ.symm f) = f
      exact Θ.apply_symm_apply f

/-- **The power series with constant coefficient in the base depend only on the base algebra up to
isomorphism.** -/
theorem nonempty_ringEquiv_constantCoeffInBase_congr {k : Type*} {K : Type*} {K' : Type*}
    [CommRing k] [CommRing K] [CommRing K'] [Algebra k K] [Algebra k K'] (e : K ≃ₐ[k] K') :
    Nonempty (↥(constantCoeffInBase k K) ≃+* ↥(constantCoeffInBase k K')) := by
  refine ⟨RingEquiv.restrict (mapRingEquiv e.toRingEquiv) _ _ fun f => ?_⟩
  rw [mem_constantCoeffInBase, mem_constantCoeffInBase, constantCoeff_mapRingEquiv]
  refine ⟨fun ⟨c, hc⟩ => ⟨c, ?_⟩, fun ⟨c, hc⟩ => ⟨c, ?_⟩⟩
  · rw [← hc]
    exact (e.commutes c).symm
  · exact e.injective ((e.commutes c).trans hc)

/-- **A `Fin 2`-indexed product of algebras is the product of its two factors.** -/
def _root_.AlgEquiv.piFinTwo (k : Type*) [CommSemiring k] (R : Fin 2 → Type*)
    [∀ i, Semiring (R i)] [∀ i, Algebra k (R i)] : (∀ i, R i) ≃ₐ[k] R 0 × R 1 :=
  AlgEquiv.ofRingEquiv (f := RingEquiv.piFinTwo R) fun _ => rfl

/-- **Over a finite product of copies of the base field, the power series with constant
coefficient in the base are the multicross ring.** -/
theorem nonempty_ringEquiv_multicross (k : Type*) [CommRing k] (n : ℕ) [NeZero n] :
    Nonempty (↥(constantCoeffInBase k (Fin n → k)) ≃+* ↥(Stacks.Curves.multicross k n)) := by
  have : Nonempty (Fin n) := Fin.pos_iff_nonempty.mp (Nat.pos_of_ne_zero (NeZero.ne n))
  refine ⟨RingEquiv.restrict (piRingEquiv fun _ : Fin n => k) _ _ fun f => ?_⟩
  rw [mem_constantCoeffInBase, Stacks.Curves.mem_multicross]
  simp only [constantCoeff_piRingEquiv (fun _ : Fin n => k)]
  refine ⟨fun ⟨c, hc⟩ i j => ?_, fun h => ?_⟩
  · rw [← hc, Pi.algebraMap_apply, Pi.algebraMap_apply]
  · obtain ⟨i₀⟩ := ‹Nonempty (Fin n)›
    refine ⟨constantCoeff f i₀, funext fun i => ?_⟩
    rw [Pi.algebraMap_apply, Algebra.algebraMap_self_apply]
    exact h i₀ i

/-! ### Complete regular local rings of dimension one -/

/-- **Power series in one variable are the multivariable power series indexed by `Fin 1`.** -/
def finOneRingEquiv (R : Type*) [CommRing R] : MvPowerSeries (Fin 1) R ≃+* PowerSeries R :=
  (MvPowerSeries.finSuccEquiv R 0).toRingEquiv.trans
    (mapRingEquiv (MvPowerSeries.isEmptyEquiv (Fin 0) R).toRingEquiv)

/-- **A surjection from a local ring onto a field identifies that field with the residue
field.**  The kernel of such a surjection is a maximal ideal, hence *the* maximal ideal, so the
surjection descends to the residue field and the descent is bijective. -/
theorem _root_.IsLocalRing.exists_residueFieldRingEquiv_of_surjective
    {A : Type*} {K : Type*} [CommRing A] [IsLocalRing A] [Field K] (r : A →+* K)
    (hr : Function.Surjective r) :
    ∃ θ : IsLocalRing.ResidueField A ≃+* K, ∀ a, θ (IsLocalRing.residue A a) = r a := by
  have hmax : (RingHom.ker r).IsMaximal := RingHom.ker_isMaximal_of_surjective r hr
  have hker : RingHom.ker r = IsLocalRing.maximalIdeal A := IsLocalRing.eq_maximalIdeal hmax
  have : IsLocalHom r := by
    refine ⟨fun a ha => ?_⟩
    by_contra hna
    have hmem : r a = 0 := by
      rw [← RingHom.mem_ker, hker]
      exact (IsLocalRing.mem_maximalIdeal a).mpr (mem_nonunits_iff.mpr hna)
    rw [hmem] at ha
    exact not_isUnit_zero ha
  refine ⟨RingEquiv.ofBijective (IsLocalRing.ResidueField.lift r)
    ⟨RingHom.injective _, fun x => ?_⟩, fun a => ?_⟩
  · obtain ⟨a, ha⟩ := hr x
    exact ⟨IsLocalRing.residue A a, by
      change IsLocalRing.ResidueField.lift r (IsLocalRing.residue A a) = x
      rw [IsLocalRing.ResidueField.lift_residue_apply]
      exact ha⟩
  · change IsLocalRing.ResidueField.lift r (IsLocalRing.residue A a) = r a
    rw [IsLocalRing.ResidueField.lift_residue_apply]

/-- **A complete regular local algebra of dimension one over a field is the power series ring in
one variable over a field onto which it surjects, compatibly with the surjection.**

This is [Stacks, Tag 0C0S] in one variable: the embedding dimension of a regular local ring is
its Krull dimension, here one, and the ring contains the ground field, so it is the power series
ring over its residue field. A surjection onto a field identifies that field with the residue
field (`IsLocalRing.exists_residueFieldRingEquiv_of_surjective`), and so does the constant
coefficient of the power series presentation; composing the presentation with the induced
automorphism of the residue field matches the constant coefficient with the given surjection. -/
@[ega "0 19.8.8" "(i), special case"]
theorem exists_ringEquiv_powerSeries_of_isRegularLocalRing
    (k : Type u) (A : Type v) (K : Type w) [Field k] [CommRing A] [Field K] [IsLocalRing A]
    [IsNoetherianRing A] [Algebra k A] [IsRegularLocalRing A]
    [IsAdicComplete (IsLocalRing.maximalIdeal A) A]
    (hdim : ringKrullDim A = 1) (r : A →+* K) (hr : Function.Surjective r) :
    ∃ e : A ≃+* PowerSeries K, ∀ a, constantCoeff (e a) = r a := by
  have hfin : Module.finrank (IsLocalRing.ResidueField A) (IsLocalRing.CotangentSpace A) = 1 := by
    have h := (IsRegularLocalRing.iff_finrank_cotangentSpace (R := A)).mp ‹_›
    rw [hdim] at h
    exact_mod_cast h
  obtain ⟨φ₀⟩ :=
    (IsRegularLocalRing.nonempty_ringEquiv_and_algEquiv_mvPowerSeries.{v, u, 0} A 1 hfin).1 k
  let φ : A ≃+* PowerSeries (IsLocalRing.ResidueField A) :=
    φ₀.trans (finOneRingEquiv (IsLocalRing.ResidueField A))
  have hsurj : Function.Surjective
      ((constantCoeff (R := IsLocalRing.ResidueField A)).comp φ.toRingHom) := by
    intro x
    obtain ⟨a, ha⟩ := φ.surjective (PowerSeries.C x)
    refine ⟨a, ?_⟩
    change constantCoeff (φ a) = x
    rw [ha, constantCoeff_C]
  obtain ⟨θ', hθ'⟩ := IsLocalRing.exists_residueFieldRingEquiv_of_surjective
    ((constantCoeff (R := IsLocalRing.ResidueField A)).comp φ.toRingHom) hsurj
  obtain ⟨θ, hθ⟩ := IsLocalRing.exists_residueFieldRingEquiv_of_surjective r hr
  refine ⟨φ.trans (mapRingEquiv (θ'.symm.trans θ)), fun a => ?_⟩
  rw [RingEquiv.trans_apply, constantCoeff_mapRingEquiv, RingEquiv.trans_apply]
  have key : constantCoeff (φ a) = θ' (IsLocalRing.residue A a) := (hθ' a).symm
  rw [key, θ'.symm_apply_apply, hθ]

end PowerSeries

end
