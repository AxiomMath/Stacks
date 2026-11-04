module

public import StacksFrontier.RingTheory.Cech.DegreeZeroTowerComparison
public import StacksFrontier.Algebra.Homology.CochainHomologyElements

/-!
# The degree-zero tower comparison, on cohomology

Let `K` be a cochain complex of modules and `Kₙ` an inverse system of cochain complexes with
compatible maps `πₙ : K ⟶ Kₙ`. Suppose the cochains of `K` are identified with the degree-zero
part of a graded complex `C` with a degree-one endomorphism `f`, the maps `πₙ` are surjective,
and the kernel of `πₙ` is, under that identification, the set of multiples of `f^{c n}` by
elements of degree `-c n`. This is the situation of the Čech complexes computing `Hᵖ(X, ℱ)` and
the cohomology of the restrictions of `ℱ` to the infinitesimal neighbourhoods `Q_{c n}` of a zero
scheme, in the proof of [Stacks, Tag 0EL1].

Given the injectivity and descent hypotheses of the degree-zero comparison
`Stacks.DegreeZeroTower.bijective_toCompatible`, the map `Hᵖ(K) ⟶ lim Hᵖ(Kₙ)` is injective and
every compatible family is in its image.

## Main results

* `Stacks.DegreeZeroTower.homology_tower_bijective`: the statement above.

## References

* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
-/

@[expose] public section

open CategoryTheory Stacks.CochainHomologyElements

universe u v w t

namespace Stacks.DegreeZeroTower

variable {S : Type u} [Ring S] {R : Type t} [CommRing R] {C : ℕ → Type w}
  [∀ p, AddCommGroup (C p)] [∀ p, Module R (C p)]
  (d : ∀ p, C p →ₗ[R] C (p + 1)) (D : ∀ p, ℤ → AddSubgroup (C p)) (f : R)
  (K : CochainComplex (ModuleCat.{v} S) ℕ) (Kt : ℕ → CochainComplex (ModuleCat.{v} S) ℕ)
  (π : ∀ n, K ⟶ Kt n) (τ : ∀ n, Kt (n + 1) ⟶ Kt n)

/-- The composite of the transition maps of the inverse system of complexes. -/
noncomputable def descendHom : ∀ (n k : ℕ), Kt (n + k) ⟶ Kt n
  | _, 0 => 𝟙 _
  | n, k + 1 => τ (n + k) ≫ descendHom n k

/-- If the maps `π n` are compatible with the transition maps, then `π (n + k)` followed by
`descendHom Kt τ n k` is `π n`. -/
theorem descendHom_comp (hπτ : ∀ n, π (n + 1) ≫ τ n = π n) (n k : ℕ) :
    π (n + k) ≫ descendHom Kt τ n k = π n := by
  induction k with
  | zero => exact Category.comp_id _
  | succ k ih =>
    show π (n + k + 1) ≫ τ (n + k) ≫ descendHom Kt τ n k = π n
    rw [← Category.assoc, hπτ, ih]

/-- Descending a cohomology class of `Kt (n + k)` along the maps induced by the transition maps
agrees with applying the map induced on cohomology by `descendHom Kt τ n k`. -/
theorem descend_homologyMap (p n k : ℕ) (y : (Kt (n + k)).homology p) :
    descend (G := fun n => ((Kt n).homology p : Type v))
        (fun n => (HomologicalComplex.homologyMap (τ n) p).hom.toAddMonoidHom) n k y =
      HomologicalComplex.homologyMap (descendHom Kt τ n k) p y := by
  induction k with
  | zero =>
    show y = (HomologicalComplex.homologyMap (𝟙 (Kt (n + 0))) p) y
    rw [HomologicalComplex.homologyMap_id]
    rfl
  | succ k ih =>
    show descend (G := fun n => ((Kt n).homology p : Type v)) _ n k
      (HomologicalComplex.homologyMap (τ (n + k)) p y) = _
    rw [ih]
    show _ = HomologicalComplex.homologyMap (τ (n + k) ≫ descendHom Kt τ n k) p y
    rw [HomologicalComplex.homologyMap_comp]
    rfl

variable {d D f K Kt π τ}

/-- **The degree-zero tower comparison, on cohomology.** Under the hypotheses above, the map
`Hᵖ(K) ⟶ ∏ₙ Hᵖ(Kₙ)` induced by the `π n` is injective, and every family of classes compatible
with the transition maps `τ n` lies in its image. -/
theorem homology_tower_bijective (hπτ : ∀ n, π (n + 1) ≫ τ n = π n)
    (hfD : ∀ p m (x : C p), x ∈ D p m → f • x ∈ D p (m + 1))
    (ψ : ∀ p, K.X p →+ C p) (hψinj : ∀ p, Function.Injective (ψ p))
    (hψrange : ∀ p (z : C p), z ∈ D p 0 ↔ ∃ x, ψ p x = z)
    (hψd : ∀ p (x : K.X p), ψ (p + 1) (K.d p (p + 1) x) = d p (ψ p x))
    {c : ℕ} (hc : 1 ≤ c)
    (hπsurj : ∀ n p, Function.Surjective ((π n).f p))
    (hπker : ∀ n p (x : K.X p), (π n).f p x = 0 ↔
      ∃ w ∈ D p (-(c * n : ℕ)), ψ p x = f ^ (c * n) • w)
    (p : ℕ)
    (Hinj : ∃ N₀ : ℕ, ∀ N, N₀ ≤ N → ∀ z u : C p, z ∈ D p 0 → d p z = 0 →
      u ∈ D p (-N) → z - f ^ N • u ∈ bd d D p 0 → z ∈ bd d D p 0)
    (Hsurj : ∃ e : ℕ, ∀ n (y : C p) (u : C (p + 1)), y ∈ D p 0 →
      u ∈ D (p + 1) (-(n + e : ℕ)) → d p y = f ^ (n + e) • u →
      ∃ x ∈ D p 0, d p x = 0 ∧ ∃ w ∈ D p (-n), y - x = f ^ n • w) :
    Function.Injective (fun x : K.homology p => fun n =>
        HomologicalComplex.homologyMap (π n) p x) ∧
      ∀ y : ∀ n, (Kt n).homology p,
        (∀ n, HomologicalComplex.homologyMap (τ n) p (y (n + 1)) = y n) →
        ∃ x : K.homology p, ∀ n, HomologicalComplex.homologyMap (π n) p x = y n := by
  obtain ⟨N₀, hinj⟩ := Hinj
  obtain ⟨e, hsurj⟩ := Hsurj
  have hψD : ∀ p (x : K.X p), ψ p x ∈ D p 0 := fun p x => (hψrange p _).2 ⟨x, rfl⟩
  have hφτ : ∀ n (x : K.homology p),
      HomologicalComplex.homologyMap (τ n) p (HomologicalComplex.homologyMap (π (n + 1)) p x) =
        HomologicalComplex.homologyMap (π n) p x := fun n x => by
    rw [← ConcreteCategory.comp_apply, ← HomologicalComplex.homologyMap_comp, hπτ]
  refine bijective_toCompatible
    (fun n => (HomologicalComplex.homologyMap (π n) p).hom.toAddMonoidHom)
    (fun n => (HomologicalComplex.homologyMap (τ n) p).hom.toAddMonoidHom) hφτ N₀ ?_ ?_
  · intro n hn
    have hN : N₀ ≤ c * n := le_trans hn (Nat.le_mul_of_pos_left n hc)
    refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
    obtain ⟨z, hz, rfl⟩ := exists_eq_cls K p x
    change HomologicalComplex.homologyMap (π n) p (cls K z hz) = 0 at hx
    rw [homologyMap_cls (π n) p z hz (isCocycle_map (π n) hz)] at hx
    have hdz : d p (ψ p z) = 0 := by rw [← hψd, hz, map_zero]
    cases p with
    | zero =>
      rw [cls_eq_zero_iff_zero] at hx
      obtain ⟨w, hw, hzw⟩ := (hπker n 0 z).1 hx
      have h0 := hinj (c * n) hN (ψ 0 z) w (hψD 0 z) hdz hw
        (by rw [hzw, sub_self]; exact zero_mem _)
      rw [bd_zero, AddSubgroup.mem_bot] at h0
      obtain rfl : z = 0 := hψinj 0 (h0.trans (map_zero _).symm)
      exact (cls_eq_zero_iff_zero K 0 hz).2 rfl
    | succ q =>
      rw [cls_eq_zero_iff_succ] at hx
      obtain ⟨y', hy'⟩ := hx
      obtain ⟨y, rfl⟩ := hπsurj n q y'
      have hker : (π n).f (q + 1) (z - K.d q (q + 1) y) = 0 := by
        rw [map_sub, ← hy']
        show ((π n).f q ≫ (Kt n).d q (q + 1)) y - (K.d q (q + 1) ≫ (π n).f (q + 1)) y = 0
        rw [HomologicalComplex.Hom.comm, sub_self]
      obtain ⟨w, hw, hzw⟩ := (hπker n (q + 1) _).1 hker
      have hmem : ψ (q + 1) z - f ^ (c * n) • w ∈ bd d D (q + 1) 0 := by
        rw [map_sub, hψd] at hzw
        refine (mem_bd_succ d D).2 ⟨ψ q y, hψD q y, ?_⟩
        rw [← hzw]
        abel
      obtain ⟨v, hv, hvz⟩ := (mem_bd_succ d D).1
        (hinj (c * n) hN (ψ (q + 1) z) w (hψD _ z) hdz hw hmem)
      obtain ⟨y₀, rfl⟩ := (hψrange q v).1 hv
      rw [← hψd] at hvz
      exact (cls_eq_zero_iff_succ K q z hz).2 ⟨y₀, hψinj _ hvz⟩
  · intro n
    refine ⟨e, fun y => ?_⟩
    rw [descend_homologyMap]
    obtain ⟨y'', hy'', rfl⟩ := exists_eq_cls (Kt (n + e)) p y
    obtain ⟨y₁, rfl⟩ := hπsurj (n + e) p y''
    have hd1 : (π (n + e)).f (p + 1) (K.d p (p + 1) y₁) = 0 := by
      show (K.d p (p + 1) ≫ (π (n + e)).f (p + 1)) y₁ = 0
      rwa [← HomologicalComplex.Hom.comm]
    obtain ⟨u, hu, hdu⟩ := (hπker (n + e) (p + 1) _).1 hd1
    rw [hψd] at hdu
    have hexp : c * (n + e) = (c * n + e) + (c - 1) * e := by
      obtain ⟨c', rfl⟩ := Nat.exists_eq_add_of_le hc
      simp only [Nat.add_sub_cancel_left]
      ring
    have hu' : f ^ ((c - 1) * e) • u ∈ D (p + 1) (-(c * n + e : ℕ)) := by
      convert pow_smul_mem f hfD (p + 1) hu ((c - 1) * e) using 2
      rw [hexp]
      push_cast
      ring
    obtain ⟨x, hx, hdx, w, hw, hyx⟩ := hsurj (c * n) (ψ p y₁) _ (hψD p y₁) hu' (by
      rw [hdu, smul_smul, ← pow_add, ← hexp])
    obtain ⟨x₀, rfl⟩ := (hψrange p x).1 hx
    have hx₀ : IsCocycle K x₀ := hψinj (p + 1) (by
      show ψ (p + 1) (K.d p (p + 1) x₀) = ψ (p + 1) 0
      rw [hψd, hdx, map_zero])
    refine ⟨cls K x₀ hx₀, ?_⟩
    show HomologicalComplex.homologyMap (π n) p (cls K x₀ hx₀) =
      HomologicalComplex.homologyMap (descendHom Kt τ n e) p (cls _ _ hy'')
    rw [homologyMap_cls (π n) p x₀ hx₀ (isCocycle_map (π n) hx₀),
      homologyMap_cls _ p _ hy'' (isCocycle_map _ hy'')]
    have hcomp : (descendHom Kt τ n e).f p ((π (n + e)).f p y₁) = (π n).f p y₁ := by
      rw [← descendHom_comp K Kt π τ hπτ n e]
      rfl
    congr 1
    rw [hcomp, ← sub_eq_zero, ← map_sub]
    exact (hπker n p _).2 ⟨-w, neg_mem hw, by rw [map_sub, smul_neg, ← hyx, neg_sub]⟩

end Stacks.DegreeZeroTower

end
