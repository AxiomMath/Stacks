module

public import Mathlib.RingTheory.Noetherian.Basic
public import StacksFrontier.AlgebraicGeometry.Discriminant.FactorizationRefinement

/-!
# Local annihilation after an away localization of the target

Comparing the relative dualizing modules of two finite-open factorizations of a quasi-finite
algebra uses a hypothesis that is local on the target: near every prime, the kernel of the
larger intermediate algebra is annihilated by a power of an element of the smaller one. This
file verifies that hypothesis in the two cases an away localization of the target produces,
together with the two general module-theoretic facts the verification rests on.

## Main results

* `LinearMap.exists_factor_functional`: a functional vanishing on the kernel of a surjection
  factors through it.
* `Submodule.exists_uniform_pow_annihilator`: on a finitely generated submodule, pointwise
  annihilation by powers of a scalar is annihilation by one power.
* `Stacks.Discriminant.locFact_local_annihilation` and
  `Stacks.Discriminant.locFact_refinement_local_annihilation` are the two local annihilation
  statements for the factorization of an away localization of the target induced by one of the
  target itself.

## Implementation notes

In both cases the element of the intermediate algebra is produced by the basic opens, which form
a basis of the image of the spectrum of the target, and the uniform exponent comes from
Noetherianity of the kernel ideal.

## References

* [Stacks Project, Tag 0BT2](https://stacks.math.columbia.edu/tag/0BT2)
-/

@[expose] public section

universe u v w x y

open Topology

namespace LinearMap

/-- A linear functional vanishing on the kernel of a surjective linear map factors through that
map. -/
theorem exists_factor_functional
    {R : Type u} {M : Type v} {N : Type w}
    [CommRing R] [AddCommGroup M] [AddCommGroup N] [Module R M] [Module R N]
    (q : M →ₗ[R] N) (hq : Function.Surjective q) (f : M →ₗ[R] R)
    (hf : ∀ m, q m = 0 → f m = 0) :
    ∃ g : N →ₗ[R] R, g.comp q = f := by
  let e := q.quotKerEquivOfSurjective hq
  let g := (q.ker.liftQ f hf).comp e.symm.toLinearMap
  refine ⟨g, ?_⟩
  ext m
  show (q.ker.liftQ f hf) (e.symm (q m)) = f m
  rw [show e.symm (q m) = Submodule.Quotient.mk m from e.symm_apply_eq.mpr rfl]
  rfl

end LinearMap

namespace Submodule

/-- If every element of a finitely generated submodule is annihilated by some power of a scalar,
then a single power of that scalar annihilates the whole submodule. -/
theorem exists_uniform_pow_annihilator
    {R : Type u} {M : Type v} [CommRing R] [AddCommGroup M] [Module R M]
    (N : Submodule R M) (hN : N.FG) (r : R)
    (h : ∀ m ∈ N, ∃ n : ℕ, r ^ n • m = 0) :
    ∃ n : ℕ, ∀ m ∈ N, r ^ n • m = 0 := by
  classical
  obtain ⟨s, hs⟩ := hN
  have ht : ∀ m ∈ s, ∃ n : ℕ, r ^ n • m = 0 := by
    intro m hm
    exact h m (hs ▸ Submodule.subset_span hm)
  choose n hn using ht
  let k := ∑ m ∈ s, if hm : m ∈ s then n m hm else 0
  refine ⟨k, ?_⟩
  intro m hm
  rw [← hs] at hm
  induction hm using Submodule.span_induction with
  | mem m hm =>
    have hle : n m hm ≤ k := by
      simpa [k, show m ∈ s from hm] using
        (Finset.single_le_sum (f := fun m => if hm : m ∈ s then n m hm else 0)
          (fun i hi => Nat.zero_le _) hm :
          (if hm : m ∈ s then n m hm else 0) ≤ k)
    obtain ⟨l, hl⟩ := Nat.exists_eq_add_of_le hle
    rw [hl, add_comm, pow_add, mul_smul, hn m hm, smul_zero]
  | zero => simp
  | add m m' _ _ hm hm' => simp [smul_add, hm, hm']
  | smul a m _ hm => simpa [smul_comm (r ^ k) a m] using congrArg (a • ·) hm

end Submodule

namespace Stacks.Discriminant

/-- If the localization map at `c` of a ring hom `f` is injective, every element killed by `f` is
killed by a power of `c`. -/
private theorem exists_pow_mul_eq_zero_of_awayMap_injective
    {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) (c : R)
    (hf : Function.Injective (Localization.awayMap f c)) {k : R} (hk : f k = 0) :
    ∃ n : ℕ, c ^ n * k = 0 := by
  have h : algebraMap R (Localization.Away c) k = 0 := hf (by
    rw [Localization.awayMap, IsLocalization.Away.map, IsLocalization.map_eq]
    simp [hk])
  obtain ⟨n, hn⟩ := IsLocalization.Away.exists_of_eq c (h.trans (map_zero _).symm)
  exact ⟨n, by simpa using hn⟩

/-- In a Noetherian ring, if every element of an ideal is killed by some power of `c`, then one
power of `c` kills the whole ideal. -/
private theorem exists_uniform_pow_mul_eq_zero
    {R : Type*} [CommRing R] [IsNoetherianRing R] (I : Ideal R) (c : R)
    (h : ∀ k ∈ I, ∃ n : ℕ, c ^ n * k = 0) : ∃ n : ℕ, ∀ k ∈ I, c ^ n * k = 0 := by
  obtain ⟨n, hn⟩ := Submodule.exists_uniform_pow_annihilator I (IsNoetherian.noetherian I) c
    (fun k hk => (h k hk).imp fun n hn => by simpa [Algebra.smul_def] using hn)
  exact ⟨n, fun k hk => by simpa [Algebra.smul_def] using hn k hk⟩

/-- The target algebra structure on an intermediate algebra `C` obtained by restricting along
`C → B` is compatible with `A`. -/
private theorem isScalarTower_compHom
    {A B C : Type*} (Bg : Type*) [CommRing A] [CommRing B] [CommRing C] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg] [Algebra A C]
    [Algebra C B] [IsScalarTower A C B] :
    letI : Algebra C Bg := Algebra.compHom Bg (algebraMap C B)
    IsScalarTower A C Bg := by
  let : Algebra C Bg := Algebra.compHom Bg (algebraMap C B)
  refine IsScalarTower.of_algebraMap_eq' ?_
  ext a
  calc
    algebraMap A Bg a = algebraMap B Bg (algebraMap A B a) :=
      IsScalarTower.algebraMap_apply A B Bg a
    _ = algebraMap B Bg (algebraMap C B (algebraMap A C a)) := by
      rw [IsScalarTower.algebraMap_apply A C B]



/-- The local annihilation hypothesis for an away localization of the target, comparing the
induced factorization with a factorization of the localization whose intermediate algebra is
isomorphic to the original one. -/
theorem locFact_local_annihilation
    {A : Type u} {B : Type v} {Bg : Type w}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (G : FiniteOpenFactorization.{u, w, y} A Bg)
    (r : G.middle ≃ₐ[A] F.middle)
    (hr : ∀ c : G.middle,
      algebraMap B Bg (F.algebraTarget.algebraMap (r c)) =
        G.algebraTarget.algebraMap c) :
    ∀ p : PrimeSpectrum Bg, ∃ c : G.middle,
      G.algebraTarget.algebraMap c ∉ p.asIdeal ∧
        ∃ n : ℕ, ∀ k : F.middle,
          ((algebraMap B Bg).comp F.algebraTarget.algebraMap) k = 0 →
            (r c) ^ n * k = 0 := by
  let : IsNoetherianRing F.middle :=
    isNoetherianRing_iff.mpr (isNoetherian_of_tower A inferInstance)
  let fMap : F.middle →+* Bg := (algebraMap B Bg).comp F.algebraTarget.algebraMap
  let I : Ideal F.middle := RingHom.ker fMap
  intro p
  let pG := PrimeSpectrum.comap (algebraMap G.middle Bg) p
  obtain ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, hpc, haway⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show pG ∈ Set.range (PrimeSpectrum.comap (algebraMap G.middle Bg)) from ⟨p, rfl⟩)
      G.isOpenEmbedding_comap.isOpen_range
  have hnot : G.algebraTarget.algebraMap c ∉ p.asIdeal := by
    simpa [pG, PrimeSpectrum.comap_asIdeal] using hpc
  have hBij := G.awayMap_bijective c haway
  have hker : ∀ k ∈ I, ∃ n : ℕ, (r c) ^ n * k = 0 := by
    intro k hk
    let x : G.middle := r.symm k
    have hx : G.algebraTarget.algebraMap x = 0 := by
      rw [← hr x]
      simpa [x, I, fMap] using (RingHom.mem_ker.mp hk)
    obtain ⟨n, hn⟩ := exists_pow_mul_eq_zero_of_awayMap_injective
      (algebraMap G.middle Bg) c hBij.1 hx
    refine ⟨n, ?_⟩
    simpa [x] using congrArg r hn
  obtain ⟨n, hn⟩ := exists_uniform_pow_mul_eq_zero I (r c) hker
  refine ⟨c, ?_, n, ?_⟩
  · simpa using hnot
  · exact fun k hk => hn k (RingHom.mem_ker.mpr hk)

/-- The local annihilation hypothesis for an away localization of the target, comparing the
induced factorization with that of a refinement of the intermediate algebra whose own map to
the target is injective. -/
theorem locFact_refinement_local_annihilation
    {A : Type u} {B : Type v} {Bg : Type w}
    [CommRing A] [CommRing B] [CommRing Bg]
    [Algebra A B] [Algebra B Bg] [Algebra A Bg] [IsScalarTower A B Bg]
    [IsNoetherianRing A]
    (g : B) [IsLocalization.Away g Bg]
    (F : FiniteOpenFactorization.{u, v, x} A B)
    (H : FiniteOpenFactorization.{u, v, y} A B)
    (r : F.middle →ₐ[A] H.middle)
    (hr : ∀ c, algebraMap H.middle B (r c) = algebraMap F.middle B c)
    (hH : Function.Injective (algebraMap H.middle B)) :
    letI : Algebra F.middle Bg := Algebra.compHom Bg (algebraMap F.middle B)
    letI : IsScalarTower F.middle B Bg := IsScalarTower.of_algebraMap_eq' (by
      ext c
      rfl)
    letI : IsScalarTower A F.middle Bg := IsScalarTower.of_algebraMap_eq' (by
      ext a
      calc
        algebraMap A Bg a = algebraMap B Bg (algebraMap A B a) :=
          IsScalarTower.algebraMap_apply A B Bg a
        _ = algebraMap B Bg (algebraMap F.middle B (algebraMap A F.middle a)) := by
          rw [IsScalarTower.algebraMap_apply A F.middle B])
    letI : Algebra H.middle Bg := Algebra.compHom Bg (algebraMap H.middle B)
    letI : IsScalarTower H.middle B Bg := IsScalarTower.of_algebraMap_eq' (by
      ext c
      rfl)
    letI : IsScalarTower A H.middle Bg := IsScalarTower.of_algebraMap_eq' (by
      ext a
      calc
        algebraMap A Bg a = algebraMap B Bg (algebraMap A B a) :=
          IsScalarTower.algebraMap_apply A B Bg a
        _ = algebraMap B Bg (algebraMap H.middle B (algebraMap A H.middle a)) := by
          rw [IsScalarTower.algebraMap_apply A H.middle B])
    ∀ p : PrimeSpectrum Bg, ∃ c : F.middle,
      algebraMap F.middle Bg c ∉ p.asIdeal ∧
        ∃ n : ℕ, ∀ k : H.middle,
          algebraMap H.middle Bg k = 0 → (r c) ^ n * k = 0 := by
  let : IsNoetherianRing H.middle :=
    isNoetherianRing_iff.mpr (isNoetherian_of_tower A inferInstance)
  let : Algebra F.middle Bg := Algebra.compHom Bg (algebraMap F.middle B)
  let : IsScalarTower F.middle B Bg := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rfl)
  let : IsScalarTower A F.middle Bg := isScalarTower_compHom (B := B) Bg
  let : Algebra H.middle Bg := Algebra.compHom Bg (algebraMap H.middle B)
  let : IsScalarTower H.middle B Bg := IsScalarTower.of_algebraMap_eq' (by
    ext c
    rfl)
  let : IsScalarTower A H.middle Bg := isScalarTower_compHom (B := B) Bg
  let fMap : H.middle →+* Bg := (algebraMap B Bg).comp (algebraMap H.middle B)
  let I : Ideal H.middle := RingHom.ker fMap
  intro p
  let FLoc := locFact (Bg := Bg) g F
  let pF := PrimeSpectrum.comap (algebraMap F.middle Bg) p
  obtain ⟨_, ⟨_, ⟨c, rfl⟩, rfl⟩, hpc, haway⟩ :=
    PrimeSpectrum.isBasis_basic_opens.exists_subset_of_mem_open
      (show pF ∈ Set.range (PrimeSpectrum.comap (algebraMap F.middle Bg)) from ⟨p, rfl⟩)
      FLoc.isOpenEmbedding_comap.isOpen_range
  have hnot : algebraMap F.middle Bg c ∉ p.asIdeal := by
    simpa [pF, PrimeSpectrum.comap_asIdeal] using hpc
  have hcb : (PrimeSpectrum.basicOpen c : Set (PrimeSpectrum F.middle)) ⊆
      Set.range (PrimeSpectrum.comap (algebraMap F.middle B)) := by
    intro q hq
    obtain ⟨q', hq'⟩ := haway hq
    refine ⟨PrimeSpectrum.comap (algebraMap B Bg) q', ?_⟩
    apply PrimeSpectrum.ext
    show Ideal.comap (algebraMap F.middle B)
      (Ideal.comap (algebraMap B Bg) q'.asIdeal) = q.asIdeal
    rw [Ideal.comap_comap]
    rw [← IsScalarTower.algebraMap_eq F.middle B Bg]
    exact congrArg PrimeSpectrum.asIdeal hq'
  have hFaway := F.awayMap_bijective c hcb
  have hunit := unit_image_of_range_localization (g := g) F c haway
  let cB := algebraMap F.middle B c
  have hHaway := awayMap_bijective_refinement_at F r (RingHom.ext hr) hH c hFaway
  have hBaway := awayMap_bijective_if_unit (B := B) (Bg := Bg) g cB hunit
  have hdenB : algebraMap H.middle B (r c) = cB := hr c
  let Bc := Localization.Away cB
  let : IsLocalization.Away (algebraMap H.middle B (r c)) Bc := by
    rw [hdenB]
    infer_instance
  let eHB : Localization.Away (algebraMap H.middle B (r c)) ≃ₐ[B] Bc :=
    IsLocalization.algEquiv
      (Submonoid.powers (algebraMap H.middle B (r c))) _ _
  have hden : algebraMap H.middle Bg (r c) = algebraMap B Bg cB := by
    rw [IsScalarTower.algebraMap_apply H.middle B Bg]
    exact congrArg (algebraMap B Bg) (hr c)
  let : IsLocalization.Away (algebraMap B Bg cB)
      (Localization.Away (algebraMap H.middle Bg (r c))) := by
    rw [← hden]
    infer_instance
  let eT : Localization.Away (algebraMap B Bg cB) ≃ₐ[Bg]
      Localization.Away (algebraMap H.middle Bg (r c)) :=
    IsLocalization.algEquiv (Submonoid.powers (algebraMap B Bg cB)) _ _
  have hcompAway :
      (eT.toRingHom.comp (Localization.awayMap (algebraMap B Bg) cB)).comp
        (eHB.toRingHom.comp (Localization.awayMap (algebraMap H.middle B) (r c))) =
      Localization.awayMap (algebraMap H.middle Bg) (r c) := by
    apply IsLocalization.ringHom_ext (.powers (r c))
    ext k
    simp only [RingHom.comp_apply]
    have hHB : ∀ x : B,
        eHB.toRingHom (algebraMap B (Localization.Away (algebraMap H.middle B (r c))) x) =
          algebraMap B Bc x := by
      intro x
      show eHB (algebraMap B (Localization.Away (algebraMap H.middle B (r c))) x) = _
      exact eHB.commutes x
    have hT : ∀ x : Bg,
        eT.toRingHom (algebraMap Bg (Localization.Away (algebraMap B Bg cB)) x) =
          algebraMap Bg (Localization.Away (algebraMap H.middle Bg (r c))) x := by
      intro x
      show eT (algebraMap Bg (Localization.Away (algebraMap B Bg cB)) x) = _
      exact eT.commutes x
    calc
      _ = eT.toRingHom (algebraMap Bg (Localization.Away (algebraMap B Bg cB))
          (algebraMap B Bg (algebraMap H.middle B k))) := by
        simp only [Localization.awayMap, IsLocalization.Away.map,
          IsLocalization.map_eq]
        rw [hHB]
        rw [IsLocalization.map_eq]
      _ = algebraMap Bg (Localization.Away (algebraMap H.middle Bg (r c)))
          (algebraMap B Bg (algebraMap H.middle B k)) := hT _
      _ = algebraMap Bg (Localization.Away (algebraMap H.middle Bg (r c)))
          (algebraMap H.middle Bg k) := by
        exact congrArg
          (algebraMap Bg (Localization.Away (algebraMap H.middle Bg (r c))))
          (IsScalarTower.algebraMap_apply H.middle B Bg k).symm
      _ = Localization.awayMap (algebraMap H.middle Bg) (r c)
          (algebraMap H.middle (Localization.Away (r c)) k) := by
        simp only [Localization.awayMap, IsLocalization.Away.map,
          IsLocalization.map_eq]
  have hHtarget : Function.Bijective
      (Localization.awayMap (algebraMap H.middle Bg) (r c)) := by
    rw [← hcompAway]
    exact eT.bijective.comp (hBaway.comp (eHB.bijective.comp hHaway))
  have hker : ∀ k ∈ I, ∃ n : ℕ, (r c) ^ n * k = 0 := by
    intro k hk
    exact exists_pow_mul_eq_zero_of_awayMap_injective _ (r c) hHtarget.1 (RingHom.mem_ker.mp hk)
  obtain ⟨n, hn⟩ := exists_uniform_pow_mul_eq_zero I (r c) hker
  refine ⟨c, hnot, n, ?_⟩
  intro k hk
  exact hn k (RingHom.mem_ker.mpr hk)

end Stacks.Discriminant
