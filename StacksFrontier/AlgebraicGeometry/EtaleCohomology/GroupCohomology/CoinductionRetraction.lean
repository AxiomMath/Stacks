module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupCohomology.Shapiro
import Mathlib.Topology.Algebra.ClopenNhdofOne

/-!
# Averaging over a subgroup of index prime to `ℓ`

Let `G` be a profinite group, `ℓ` a natural number and `H ⊆ G` a subgroup such that every open
subgroup of `G` containing `H` has index prime to `ℓ`; for instance a maximal pro-`ℓ` subgroup,
by `IsMaximalProPSubgroup.not_dvd_index`. Let `M` be a discrete `G`-module which is `ℓ`-power
torsion. Then the unit `M → Coind_H^G M` of the adjunction between restriction and coinduction
has a `G`-equivariant retraction.

The retraction is an average. For `f` in the coinduced module choose an open normal subgroup
`N` of `G` such that `f` is invariant under right translation by `N` and `N` fixes the values of
`f`. The function `y ↦ y • f (y⁻¹)` is then invariant under right translation by the open
subgroup `U = H ⊔ N`, and the retraction sends `f` to
`[G : U]⁻¹ • ∑_{y ∈ G ⧸ U} y • f (y⁻¹)`, the index being invertible on `M`. This does not depend
on `N`. Consequently `Hⁿ(G, M)` injects into `Hⁿ(G, Coind_H^G M) = Hⁿ(H, M)`: this is the
argument "la méthode de la trace" of the source, for a subgroup of possibly infinite index.

## Main definitions

* `Stacks.GroupCohomology.coinductionRetraction`: the retraction `Coind_H^G M → M`.

## Main results

* `Stacks.GroupCohomology.unit_comp_coinductionRetraction`: it is a retraction of the unit.
* `Stacks.GroupCohomology.injective_ext_comp_unit`: the induced map on cohomology from `M` to the
  coinduced module is injective.
* `Stacks.GroupCohomology.subsingleton_ext_of_subsingleton_ext_restriction`: if `Hⁿ(H, M)`
  vanishes then so does `Hⁿ(G, M)`.
* `Stacks.GroupCohomology.exists_pow_smul_coinduction_eq_zero`: the module coinduced from an
  `ℓ`-power torsion module is `ℓ`-power torsion.

## References

* [Stacks Project, Tag 0DV8](https://stacks.math.columbia.edu/tag/0DV8)
* [J.-P. Serre, *Galois cohomology*, I.3.3][serre1997galois]
-/

@[expose] public noncomputable section

open CategoryTheory Limits

universe v w

namespace Stacks.GroupCohomology

section Torsion

variable {A : Type*} [AddCommGroup A] {ℓ : ℕ}

/-- On an `ℓ`-power torsion abelian group, multiplication by an integer prime to `ℓ` is
bijective. -/
theorem bijective_nsmul_of_coprime (hA : ∀ x : A, ∃ k : ℕ, ℓ ^ k • x = 0) {d : ℕ}
    (hd : d.Coprime ℓ) : Function.Bijective (fun x : A ↦ d • x) := by
  have key : ∀ x : A, ∃ a : ℤ, x = (a * d) • x := by
    intro x
    obtain ⟨k, hk⟩ := hA x
    obtain ⟨a, b, hab⟩ := (Nat.Coprime.pow_right k hd).isCoprime
    refine ⟨a, ?_⟩
    have : x = (a * d + b * (ℓ ^ k : ℕ)) • x := by
      push_cast at hab ⊢
      rw [hab, one_smul]
    rw [add_smul, mul_smul b, natCast_zsmul, hk, smul_zero, add_zero] at this
    exact this
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
  · have hz : d • (x - y) = 0 := by
      simp only at hxy
      rw [smul_sub, hxy, sub_self]
    obtain ⟨a, ha⟩ := key (x - y)
    rw [mul_smul, natCast_zsmul, hz, smul_zero] at ha
    exact sub_eq_zero.mp ha
  · obtain ⟨a, ha⟩ := key y
    refine ⟨a • y, ?_⟩
    simp only
    rw [← natCast_zsmul, smul_smul, mul_comm]
    exact ha.symm

/-- The inverse of multiplication by an integer prime to `ℓ` on an `ℓ`-power torsion abelian
group. -/
def nsmulInv (hA : ∀ x : A, ∃ k : ℕ, ℓ ^ k • x = 0) {d : ℕ} (hd : d.Coprime ℓ) : A →+ A :=
  ((AddEquiv.ofBijective (nsmulAddMonoidHom d : A →+ A) (bijective_nsmul_of_coprime hA hd)).symm
    : A ≃+ A).toAddMonoidHom

/-- `nsmulInv` is a right inverse of multiplication by `d`. -/
lemma nsmul_nsmulInv (hA : ∀ x : A, ∃ k : ℕ, ℓ ^ k • x = 0) {d : ℕ} (hd : d.Coprime ℓ) (x : A) :
    d • nsmulInv hA hd x = x :=
  (AddEquiv.ofBijective (nsmulAddMonoidHom d : A →+ A)
    (bijective_nsmul_of_coprime hA hd)).apply_symm_apply x

/-- `nsmulInv hA hd x = y` exactly when `d • y = x`. -/
lemma nsmulInv_eq_iff (hA : ∀ x : A, ∃ k : ℕ, ℓ ^ k • x = 0) {d : ℕ} (hd : d.Coprime ℓ)
    (x y : A) : nsmulInv hA hd x = y ↔ d • y = x := by
  constructor
  · rintro rfl
    exact nsmul_nsmulInv hA hd x
  · rintro rfl
    exact (AddEquiv.ofBijective (nsmulAddMonoidHom d : A →+ A)
      (bijective_nsmul_of_coprime hA hd)).symm_apply_apply y

/-- `nsmulInv` is a left inverse of multiplication by `d`. -/
lemma nsmulInv_nsmul (hA : ∀ x : A, ∃ k : ℕ, ℓ ^ k • x = 0) {d : ℕ} (hd : d.Coprime ℓ) (x : A) :
    nsmulInv hA hd (d • x) = x :=
  (nsmulInv_eq_iff hA hd _ _).mpr rfl

/-- The inverse of multiplication by `d` commutes with every additive endomorphism. -/
lemma nsmulInv_comm (hA : ∀ x : A, ∃ k : ℕ, ℓ ^ k • x = 0) {d : ℕ} (hd : d.Coprime ℓ)
    (φ : A →+ A) (x : A) : nsmulInv hA hd (φ x) = φ (nsmulInv hA hd x) := by
  rw [nsmulInv_eq_iff, ← map_nsmul, nsmul_nsmulInv]

/-- `(d * e)⁻¹ • (e • x) = d⁻¹ • x`. -/
lemma nsmulInv_mul_nsmul (hA : ∀ x : A, ∃ k : ℕ, ℓ ^ k • x = 0) {d e : ℕ} (hd : d.Coprime ℓ)
    (hde : (e * d).Coprime ℓ) (x : A) :
    nsmulInv hA hde (e • x) = nsmulInv hA hd x := by
  rw [nsmulInv_eq_iff, mul_smul, nsmul_nsmulInv]

end Torsion

variable {G : Type v} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [CompactSpace G]
  [TotallyDisconnectedSpace G] {H : Subgroup G} {ℓ : ℕ}

section Coinduced

variable {N : ContinuousGModule.{v, w} H}

/-- A function in a coinduced module takes finitely many values. -/
theorem finite_range_coinductionCarrier (f : coinductionCarrier H N) :
    (Set.range (f : G → N.obj.obj.V)).Finite := by
  obtain ⟨N₀, hN₀⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_rightStabilizer f) (rightStabilizer (f : G → N.obj.obj.V)).one_mem
  have := Subgroup.quotient_finite_of_isOpen N₀.toSubgroup N₀.isOpen'
  refine (Set.finite_range (fun q : G ⧸ N₀.toSubgroup ↦ (f : G → N.obj.obj.V) q.out)).subset ?_
  rintro _ ⟨x, rfl⟩
  refine ⟨(x : G ⧸ N₀.toSubgroup), ?_⟩
  obtain ⟨n, hn, hxn⟩ : ∃ n ∈ N₀.toSubgroup, (x : G ⧸ N₀.toSubgroup).out = x * n :=
    ⟨x⁻¹ * (x : G ⧸ N₀.toSubgroup).out, QuotientGroup.eq.mp (QuotientGroup.out_eq' _).symm,
      by group⟩
  simp only
  rw [hxn]
  exact hN₀ hn x

/-- **The module coinduced from an `ℓ`-power torsion module is `ℓ`-power torsion.** -/
theorem exists_pow_smul_coinduction_eq_zero
    (hN : ∀ x : N.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0) (f : coinductionCarrier H N) :
    ∃ k : ℕ, ℓ ^ k • f = 0 := by
  choose k hk using hN
  set S := (finite_range_coinductionCarrier f).toFinset
  refine ⟨S.sup k, Subtype.ext (funext fun x ↦ ?_)⟩
  have hle : k ((f : G → N.obj.obj.V) x) ≤ S.sup k :=
    Finset.le_sup (by simp [S])
  show ℓ ^ S.sup k • (f : G → N.obj.obj.V) x = 0
  rw [← Nat.sub_add_cancel hle, pow_add, mul_smul, hk, smul_zero]

end Coinduced

section Average

variable (H) in
/-- The underlying group of the module coinduced from the restriction of `M`. -/
abbrev CoindRes (M : ContinuousGModule.{v, w} G) :=
  coinductionCarrier H ((restriction.{v, v, w} H.subtype continuous_subtype_val).obj M)

variable {M : ContinuousGModule.{v, w} G}

/-- A function in the coinduced module, with values read in `M`. -/
abbrev coindVal (f : CoindRes H M) : G → M.obj.obj.V := f.1

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- A function `f` in the coinduced module satisfies `f (h * x) = h • f x` for `h ∈ H`. -/
lemma coindVal_mul (f : CoindRes H M) (h : G) (hh : h ∈ H) (x : G) :
    coindVal f (h * x) = (M.obj.obj.ρ h).hom (coindVal f x) :=
  coinductionCarrier_apply_mul f ⟨h, hh⟩ x

/-- An open normal subgroup is *adapted* to `f` if `f` is invariant under right translation by
it and it fixes the values of `f`. -/
def IsAdapted (f : CoindRes H M) (N : OpenNormalSubgroup G) : Prop :=
  N.toSubgroup ≤ rightStabilizer (coindVal f) ∧
    ∀ x, ∀ n ∈ N.toSubgroup, (M.obj.obj.ρ n).hom (coindVal f x) = coindVal f x

/-- An open normal subgroup contained in one adapted to `f` is adapted to `f`. -/
lemma IsAdapted.mono {f : CoindRes H M} {N N' : OpenNormalSubgroup G} (h : IsAdapted f N)
    (hle : N' ≤ N) : IsAdapted f N' :=
  ⟨fun _ hn ↦ h.1 (hle hn), fun x n hn ↦ h.2 x n (hle hn)⟩

/-- Every function in the coinduced module has an adapted open normal subgroup. -/
lemma exists_isAdapted (f : CoindRes H M) : ∃ N : OpenNormalSubgroup G, IsAdapted f N := by
  have hfin := finite_range_coinductionCarrier f
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    ((hfin.isOpen_biInter fun s _ ↦ isOpen_stabilizer ℤ G M s).inter (isOpen_rightStabilizer f))
    ⟨Set.mem_iInter₂.mpr fun s _ ↦ (elementStabilizer G M s).one_mem,
      Subgroup.one_mem _⟩
  exact ⟨N, fun n hn ↦ (hN hn).2, fun x n hn ↦
    Set.mem_iInter₂.mp (hN hn).1 (f.1 x) ⟨x, rfl⟩⟩

/-- The averaged function `y ↦ y • f (y⁻¹)`. -/
def averagedFunction (f : CoindRes H M) (y : G) : M.obj.obj.V :=
  (M.obj.obj.ρ y).hom (coindVal f y⁻¹)

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- If `N` is adapted to `f`, the averaged function `y ↦ y • f (y⁻¹)` is invariant under right
translation by `H ⊔ N`. -/
lemma averagedFunction_mul_right {f : CoindRes H M} {N : OpenNormalSubgroup G}
    (hN : IsAdapted f N) (y u : G) (hu : u ∈ H ⊔ N.toSubgroup) :
    averagedFunction f (y * u) = averagedFunction f y := by
  obtain ⟨h, hh, n, hn, rfl⟩ := Subgroup.mem_sup_of_normal_right.mp hu
  have h1 : coindVal f (n⁻¹ * h⁻¹ * y⁻¹) = coindVal f (h⁻¹ * y⁻¹) := by
    have : n⁻¹ * h⁻¹ * y⁻¹ = h⁻¹ * y⁻¹ * ((y * h) * n⁻¹ * (y * h)⁻¹) := by group
    rw [this]
    exact hN.1 (N.isNormal'.conj_mem _ (N.toSubgroup.inv_mem hn) _) _
  have h2 : coindVal f (h⁻¹ * y⁻¹) = (M.obj.obj.ρ h⁻¹).hom (coindVal f y⁻¹) :=
    coinductionCarrier_apply_mul f ⟨h⁻¹, H.inv_mem hh⟩ y⁻¹
  unfold averagedFunction
  rw [mul_inv_rev, mul_inv_rev, ← mul_assoc, h1, ρ_mul_apply, ρ_mul_apply, hN.2 _ n hn, h2,
    ρ_apply_ρ_inv_apply]

/-- If every open subgroup of `G` containing `H` has index prime to `ℓ`, then so does `H ⊔ N`. -/
lemma coprime_index_sup (hH : ∀ U : Subgroup G, IsOpen (U : Set G) → H ≤ U → U.index.Coprime ℓ)
    (N : OpenNormalSubgroup G) : (H ⊔ N.toSubgroup).index.Coprime ℓ :=
  hH (H ⊔ N.toSubgroup) (Subgroup.isOpen_mono le_sup_right N.isOpen') le_sup_left

/-- The averaged function on the finite quotient `G ⧸ (H ⊔ N)`. -/
def averagedQuotient (f : CoindRes H M) (N : OpenNormalSubgroup G) (hN : IsAdapted f N) :
    G ⧸ (H ⊔ N.toSubgroup) → M.obj.obj.V :=
  Quotient.lift (averagedFunction f) fun a b hab ↦ by
    have hab' : a⁻¹ * b ∈ H ⊔ N.toSubgroup := QuotientGroup.leftRel_apply.mp hab
    rw [← averagedFunction_mul_right hN a _ hab', mul_inv_cancel_left]

omit [CompactSpace G] [TotallyDisconnectedSpace G] in
/-- On the class of `y`, `averagedQuotient` is the averaged function at `y`. -/
@[simp]
lemma averagedQuotient_mk (f : CoindRes H M) (N : OpenNormalSubgroup G) (hN : IsAdapted f N)
    (y : G) :
    averagedQuotient f N hN (y : G ⧸ (H ⊔ N.toSubgroup)) = averagedFunction f y := rfl

/-- The quotient of `G` by the open subgroup `H ⊔ N` is finite. -/
instance (N : OpenNormalSubgroup G) : Fintype (G ⧸ (H ⊔ N.toSubgroup)) :=
  have := Subgroup.quotient_finite_of_isOpen (H ⊔ N.toSubgroup)
    (Subgroup.isOpen_mono le_sup_right N.isOpen')
  Fintype.ofFinite _

/-- The sum of the averaged function over `G ⧸ (H ⊔ N)`. -/
def averagedSum (f : CoindRes H M) (N : OpenNormalSubgroup G) (hN : IsAdapted f N) :
    M.obj.obj.V :=
  ∑ c, averagedQuotient f N hN c

variable (hH : ∀ U : Subgroup G, IsOpen (U : Set G) → H ≤ U → U.index.Coprime ℓ)
  (hM : ∀ x : M.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0)

/-- The average over `G ⧸ (H ⊔ N)`. -/
def averageAt (f : CoindRes H M) (N : OpenNormalSubgroup G) (hN : IsAdapted f N) :
    M.obj.obj.V :=
  nsmulInv hM (coprime_index_sup hH N) (averagedSum f N hN)

/-- Refining the open normal subgroup shrinks `H ⊔ N`. -/
private lemma sup_le_sup_of_le {K : Type*} [Group K] [TopologicalSpace K] [IsTopologicalGroup K]
    (H : Subgroup K) {N N' : OpenNormalSubgroup K} (hle : N' ≤ N) :
    H ⊔ N'.toSubgroup ≤ H ⊔ N.toSubgroup :=
  sup_le_sup_left (show N'.toSubgroup ≤ N.toSubgroup from fun _ hx ↦ hle hx) _

/-- Refining the open normal subgroup multiplies the sum by the relative index. -/
lemma averagedSum_of_le (f : CoindRes H M) {N N' : OpenNormalSubgroup G}
    (hN : IsAdapted f N) (hle : N' ≤ N) :
    averagedSum f N' (hN.mono hle) =
      (H ⊔ N'.toSubgroup).relIndex (H ⊔ N.toSubgroup) • averagedSum f N hN := by
  have hUU := sup_le_sup_of_le H hle
  let e := Subgroup.quotientEquivProdOfLE hUU
  have hfin : Finite ((H ⊔ N.toSubgroup : Subgroup G) ⧸
      (H ⊔ N'.toSubgroup).subgroupOf (H ⊔ N.toSubgroup)) :=
    Finite.of_surjective (fun c ↦ (e c).2) (fun c ↦ ⟨e.symm ((e (1 : G)).1, c), by simp⟩)
  let := Fintype.ofFinite ((H ⊔ N.toSubgroup : Subgroup G) ⧸
      (H ⊔ N'.toSubgroup).subgroupOf (H ⊔ N.toSubgroup))
  unfold averagedSum
  rw [← Equiv.sum_comp e.symm, Fintype.sum_prod_type]
  have hval : ∀ (c : G ⧸ (H ⊔ N.toSubgroup)) (u : (H ⊔ N.toSubgroup : Subgroup G) ⧸
      (H ⊔ N'.toSubgroup).subgroupOf (H ⊔ N.toSubgroup)),
      averagedQuotient f N' (hN.mono hle) (e.symm (c, u)) = averagedQuotient f N hN c := by
    have key : ∀ a, averagedQuotient f N' (hN.mono hle) a =
        averagedQuotient f N hN (e a).1 := by
      intro a
      induction a using QuotientGroup.induction_on with
      | H y => rfl
    intro c u
    rw [key, Equiv.apply_symm_apply]
  simp only [hval, Finset.sum_const, Finset.card_univ, ← Finset.smul_sum]
  rw [Subgroup.relIndex, Subgroup.index_eq_card, Nat.card_eq_fintype_card]

include hH hM

/-- The average does not depend on the adapted open normal subgroup, comparing nested ones. -/
lemma averageAt_of_le (f : CoindRes H M) {N N' : OpenNormalSubgroup G}
    (hN : IsAdapted f N) (hle : N' ≤ N) :
    averageAt hH hM f N' (hN.mono hle) = averageAt hH hM f N hN := by
  have hUU := sup_le_sup_of_le H hle
  unfold averageAt
  rw [averagedSum_of_le f hN hle, nsmulInv_eq_iff, ← Subgroup.relIndex_mul_index hUU, mul_smul,
    nsmul_nsmulInv]

/-- The average does not depend on the adapted open normal subgroup. -/
lemma averageAt_eq (f : CoindRes H M) {N N' : OpenNormalSubgroup G} (hN : IsAdapted f N)
    (hN' : IsAdapted f N') : averageAt hH hM f N hN = averageAt hH hM f N' hN' := by
  rw [← averageAt_of_le hH hM f hN (inf_le_left : N ⊓ N' ≤ N),
    ← averageAt_of_le hH hM f hN' (inf_le_right : N ⊓ N' ≤ N')]

/-- The average of a function in the coinduced module. -/
def average (f : CoindRes H M) : M.obj.obj.V :=
  averageAt hH hM f (exists_isAdapted f).choose (exists_isAdapted f).choose_spec

/-- The average may be computed with any adapted open normal subgroup. -/
lemma average_eq (f : CoindRes H M) {N : OpenNormalSubgroup G} (hN : IsAdapted f N) :
    average hH hM f = averageAt hH hM f N hN :=
  averageAt_eq hH hM f _ hN

/-- The average is additive. -/
lemma average_add (f g : CoindRes H M) :
    average hH hM (f + g) = average hH hM f + average hH hM g := by
  obtain ⟨N, hN⟩ := exists_isAdapted f
  obtain ⟨N', hN'⟩ := exists_isAdapted g
  have hf : IsAdapted f (N ⊓ N') := hN.mono inf_le_left
  have hg : IsAdapted g (N ⊓ N') := hN'.mono inf_le_right
  have hfg : IsAdapted (f + g) (N ⊓ N') :=
    ⟨fun n hn x ↦ by
      show coindVal f (x * n) + coindVal g (x * n) = coindVal f x + coindVal g x
      rw [hf.1 hn x, hg.1 hn x],
      fun x n hn ↦ by
        show (M.obj.obj.ρ n).hom (coindVal f x + coindVal g x) =
          coindVal f x + coindVal g x
        rw [map_add, hf.2 x n hn, hg.2 x n hn]⟩
  rw [average_eq hH hM _ hfg, average_eq hH hM _ hf, average_eq hH hM _ hg]
  unfold averageAt averagedSum
  rw [← map_add, ← Finset.sum_add_distrib]
  congr 2
  funext c
  induction c using QuotientGroup.induction_on with
  | H y =>
    show (M.obj.obj.ρ y).hom (coindVal f y⁻¹ + coindVal g y⁻¹) = _
    rw [map_add]
    rfl

/-- The average of `0` is `0`. -/
lemma average_zero : average hH hM (0 : CoindRes H M) = 0 := by
  have h := average_add hH hM 0 0
  rw [add_zero] at h
  exact left_eq_add.mp h

/-- The average is equivariant. -/
lemma average_translate (g : G) (f : CoindRes H M) :
    average hH hM (coinductionTranslate g f) = (M.obj.obj.ρ g).hom (average hH hM f) := by
  obtain ⟨N, hN⟩ := exists_isAdapted f
  have hgN : IsAdapted (coinductionTranslate g f) N :=
    ⟨fun n hn x ↦ by
      show coindVal f (x * n * g) = coindVal f (x * g)
      have : x * n * g = x * g * (g⁻¹ * n * g) := by group
      rw [this]
      exact hN.1 (by simpa using N.isNormal'.conj_mem n hn g⁻¹) _,
      fun x n hn ↦ hN.2 (x * g) n hn⟩
  rw [average_eq hH hM _ hgN, average_eq hH hM _ hN]
  unfold averageAt averagedSum
  have hcomm := nsmulInv_comm hM (coprime_index_sup hH N) (M.obj.obj.ρ g).hom.toAddMonoidHom
    (∑ c, averagedQuotient f N hN c)
  simp only [LinearMap.toAddMonoidHom_coe] at hcomm
  rw [← hcomm]
  congr 1
  rw [map_sum]
  refine Fintype.sum_equiv (MulAction.toPerm g⁻¹ : Equiv.Perm (G ⧸ (H ⊔ N.toSubgroup))) _ _
    fun c ↦ ?_
  induction c using QuotientGroup.induction_on with
  | H y =>
    show (M.obj.obj.ρ y).hom (coindVal f (y⁻¹ * g)) =
      (M.obj.obj.ρ g).hom ((M.obj.obj.ρ (g⁻¹ * y)).hom (coindVal f (g⁻¹ * y)⁻¹))
    rw [← ρ_mul_apply, mul_inv_cancel_left, mul_inv_rev, inv_inv]

end Average

section Retraction

variable {M : ContinuousGModule.{v, max v w} G}
  (hH : ∀ U : Subgroup G, IsOpen (U : Set G) → H ≤ U → U.index.Coprime ℓ)
  (hM : ∀ x : M.obj.obj.V, ∃ k : ℕ, ℓ ^ k • x = 0)

include hH hM

/-- The average of the unit of `m` is `m`. -/
lemma average_unit (m : M.obj.obj.V) :
    average hH hM
      (((restrictionCoinductionAdjunction.{v, w} H).unit.app M).hom.hom.hom.hom m) = m := by
  set f : CoindRes H M :=
    ((restrictionCoinductionAdjunction.{v, w} H).unit.app M).hom.hom.hom.hom m
  have hf : ∀ x, coindVal f x = (M.obj.obj.ρ x).hom m :=
    restrictionCoinductionAdjunction_unit_app_apply M m
  obtain ⟨N, hN⟩ := ProfiniteGrp.exist_openNormalSubgroup_sub_open_nhds_of_one
    (isOpen_stabilizer ℤ G M m) (elementStabilizer G M m).one_mem
  have hNf : IsAdapted f N :=
    ⟨fun n hn x ↦ by
      show coindVal f (x * n) = coindVal f x
      rw [hf, hf, ρ_mul_apply, show (M.obj.obj.ρ n).hom m = m from hN hn],
      fun x n hn ↦ by
        rw [hf]
        have : n * x = x * (x⁻¹ * n * x) := by group
        rw [← ρ_mul_apply, this, ρ_mul_apply,
          show (M.obj.obj.ρ (x⁻¹ * n * x)).hom m = m from
            hN (show x⁻¹ * n * x ∈ (N.toSubgroup : Set G) by
              simpa using N.isNormal'.conj_mem n hn x⁻¹)]⟩
  rw [average_eq hH hM _ hNf]
  unfold averageAt averagedSum
  have hc : ∀ c, averagedQuotient f N hNf c = m := by
    intro c
    induction c using QuotientGroup.induction_on with
    | H y =>
      show (M.obj.obj.ρ y).hom (coindVal f y⁻¹) = m
      rw [hf, ρ_apply_ρ_inv_apply]
  simp only [hc, Finset.sum_const, Finset.card_univ]
  rw [← Nat.card_eq_fintype_card, ← Subgroup.index_eq_card, nsmulInv_nsmul]

/-- **The averaging retraction** `Coind_H^G M → M` of the unit of restriction and coinduction,
for an `ℓ`-power torsion discrete `G`-module `M` and a subgroup `H` all of whose open overgroups
have index prime to `ℓ`. -/
def coinductionRetraction :
    (coinduction.{v, w} H).obj ((restriction H.subtype continuous_subtype_val).obj M) ⟶ M :=
  (gModuleHomEquiv G _ _).symm
    ⟨{ toFun := average hH hM
       map_zero' := average_zero hH hM
       map_add' := average_add hH hM },
      fun g f ↦ average_translate hH hM g f⟩

/-- The averaging map is a retraction of the unit. -/
theorem unit_comp_coinductionRetraction :
    (restrictionCoinductionAdjunction.{v, w} H).unit.app M ≫
      coinductionRetraction.{v, w} hH hM = 𝟙 M :=
  hom_ext fun m ↦ average_unit hH hM m

variable [HasExt.{max v w} (ContinuousGModule.{v, max v w} G)]

/-- The map on cohomology induced by the unit `M → Coind_H^G M` is injective. -/
theorem injective_ext_comp_unit (X : ContinuousGModule.{v, max v w} G) (n : ℕ) :
    Function.Injective (fun e : Abelian.Ext X M n ↦
      e.comp (Abelian.Ext.mk₀ ((restrictionCoinductionAdjunction.{v, w} H).unit.app M))
        (add_zero n)) := by
  intro e e' hee'
  have key : ∀ e : Abelian.Ext X M n,
      (e.comp (Abelian.Ext.mk₀ ((restrictionCoinductionAdjunction.{v, w} H).unit.app M))
        (add_zero n)).comp (Abelian.Ext.mk₀ (coinductionRetraction.{v, w} hH hM))
          (add_zero n) = e := by
    intro e
    rw [Abelian.Ext.comp_assoc_of_second_deg_zero, Abelian.Ext.mk₀_comp_mk₀,
      unit_comp_coinductionRetraction, Abelian.Ext.comp_mk₀_id]
  rw [← key e, ← key e']
  exact congrArg
    (fun x ↦ x.comp (Abelian.Ext.mk₀ (coinductionRetraction.{v, w} hH hM)) (add_zero n)) hee'

variable [HasExt.{max v w} (ContinuousGModule.{v, max v w} H)]

/-- **If the cohomology of `H` with coefficients in `M` vanishes in degree `n`, so does the
cohomology of `G`.** Here `M` is an `ℓ`-power torsion discrete `G`-module and every open subgroup
of `G` containing `H` has index prime to `ℓ`. -/
theorem subsingleton_ext_of_subsingleton_ext_restriction (n : ℕ)
    [Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} H (ULift.{max v w} ℤ))
      ((restriction H.subtype continuous_subtype_val).obj M) n)] :
    Subsingleton (Abelian.Ext (trivialGModule.{v, max v w} G (ULift.{max v w} ℤ)) M n) :=
  ⟨fun e e' ↦ injective_ext_comp_unit hH hM _ n
    ((shapiroAddEquiv.{v, w} H _ n).symm.injective (Subsingleton.elim _ _))⟩

end Retraction

end Stacks.GroupCohomology

end
