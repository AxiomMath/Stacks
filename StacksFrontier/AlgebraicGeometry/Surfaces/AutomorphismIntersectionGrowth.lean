module

public import StacksFrontier.AlgebraicGeometry.SectionProduct.Tensor
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.IsomorphismInvariance
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.Positivity
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersections.ChowDegree

/-!
# Unbounded intersection numbers from the automorphisms of a surface

Let `S` be an integral scheme of dimension two, proper over a field `k`, and write
`(𝓐 · 𝓑)` for the intersection number `(𝓐 𝓑 · S)` of two invertible `𝒪_S`-modules
([Stacks, Tag 0BEP]).  Suppose `S` carries invertible modules `𝓗_0, 𝓗_1, 𝓗_2` and two
automorphisms `ρ`, `σ` over `k` which act on them, up to numerical equivalence, as

* `ρ^*𝓗_i ≡ 𝓗_{i+1}` (indices modulo three),
* `σ^*𝓗_0 ≡ 𝓗_0`, `σ^*𝓗_1 ≡ 𝓗_1` and `σ^*𝓗_2 + 𝓗_2 ≡ 2𝓗_0 + 2𝓗_1`,

and suppose `𝓐 ≡ 𝓗_0 + 𝓗_1 + 𝓗_2` is ample.  This is the situation of a smooth
hypersurface `S ⊂ ℙ^1 × ℙ^1 × ℙ^1` of tridegree `(2, 2, 2)` whose equation is invariant under
the cyclic permutation of the factors (a K3 surface): `𝓗_i` is the pullback of `𝒪(1)` along the
`i`-th projection, `ρ` permutes the factors and `σ` is the covering involution of the projection
to the first two factors, which has degree two.

The relations force the intersection matrix of the `𝓗_i` to be `b (J - I)` with `b > 0`: the
self-intersections vanish because `σ` preserves `(𝓗_2 · 𝓗_2)`, and `b > 0` because
`(𝓐 · 𝓐) = 6 b` is positive by [Stacks, Tag 0BEV].  The automorphism `τ = σ ∘ ρ` then acts on
the numbers `((τ^n)^*𝓗_j · 𝓐)` through the matrix with characteristic polynomial
`(λ + 1)(λ² - 3λ + 1)`, which has the eigenvalue `(3 + √5)/2 > 1`.  Consequently the ample
modules `𝓝_n = (τ^n)^*𝓐` all have the self-intersection `(𝓐 · 𝓐)`, while
`(𝓐 · 𝓝_n) ≥ (𝓐 · 𝓐) + n` is unbounded, and `τ` has infinite order.

This is the mechanism behind [Stacks, Tag 0DSR]: on a projective surface the intersection
number `(𝓗_1 · 𝓗_2)` of two ample divisors is not bounded in terms of `(𝓗_1 · 𝓗_1)` and
`(𝓗_2 · 𝓗_2)`, and K3 surfaces can have infinite automorphism groups.

## Main results

* `AlgebraicGeometry.intersectionNumber_vecCons_comm`: the intersection pairing on a surface is
  symmetric.
* `AlgebraicGeometry.intersectionNumber_pullback_vecCons`: invariance of the pairing under an
  automorphism over `k`.
* `AlgebraicGeometry.intersectionNumber_vecCons_pullback_right`: `(𝓧 · g^*𝓜) = ((g⁻¹)^*𝓧 · 𝓜)`.
* `AlgebraicGeometry.intersectionNumber_add_le_pow_pullback`: the growth
  `(𝓐 · 𝓐) + n ≤ (𝓐 · (τ^n)^*𝓐)`.
* `AlgebraicGeometry.pow_ne_one_of_threeCycleInvolution`: `τ` has infinite order.
* `AlgebraicGeometry.WehlerRelations.of_isos_of_twist`: the relations from isomorphisms of
  invertible modules, with `σ^*𝓗_2 ⊗ 𝓗_2² ≅ ((𝓗_0 ⊗ 𝓗_0) ⊗ (𝓗_1 ⊗ 𝓗_1)) ⊗ 𝓗_2`.

## References

* [Stacks Project, Tag 0DSR](https://stacks.math.columbia.edu/tag/0DSR)
* [Stacks Project, Tag 0BEP](https://stacks.math.columbia.edu/tag/0BEP)
* [Stacks Project, Tag 0BEV](https://stacks.math.columbia.edu/tag/0BEV)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry

attribute [local instance] isInvertible_update

/-- The two members of a pair of invertible modules are invertible. -/
public instance isInvertible_vecCons_two {X : Scheme.{u}} (A B : X.Modules)
    [hA : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 A]
    [hB : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 B] (j : Fin 2) :
    SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 (![A, B] j) :=
  Fin.cases hA (fun j => Fin.cases hB (fun j => j.elim0) j) j

section Pairing

variable (k : Type u) [Field k] {S : Scheme.{u}} (p : S ⟶ Spec (.of k)) [IsProper p]

/-- **The intersection pairing on a surface is symmetric**: `(𝓐 𝓑 · S) = (𝓑 𝓐 · S)`. -/
public theorem intersectionNumber_vecCons_comm (hS : topologicalKrullDim S ≤ (2 : ℕ))
    (A B : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 B] :
    intersectionNumber k p (𝟙 S) 2 hS ![A, B] = intersectionNumber k p (𝟙 S) 2 hS ![B, A] := by
  rw [← intersectionNumber_comp_perm k p (𝟙 S) 2 hS ![A, B] (Equiv.swap 0 1)]
  exact intersectionNumber_congr_family k p (𝟙 S) 2 hS (funext fun j => by fin_cases j <;> rfl)

/-- **The intersection pairing in the first slot is an isomorphism invariant.** -/
public theorem intersectionNumber_vecCons_congr_left (hS : topologicalKrullDim S ≤ (2 : ℕ))
    {A A' : S.Modules} (B : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A']
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 B] (e : A ≅ A') :
    intersectionNumber k p (𝟙 S) 2 hS ![A, B] = intersectionNumber k p (𝟙 S) 2 hS ![A', B] :=
  intersectionNumber_eq_of_iso_at k p (𝟙 S) 2 hS ![A, B] ![A', B] 0
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl) e

/-- **The intersection pairing in the second slot is an isomorphism invariant.** -/
public theorem intersectionNumber_vecCons_congr_right (hS : topologicalKrullDim S ≤ (2 : ℕ))
    (A : S.Modules) {B B' : S.Modules} [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 B]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 B'] (e : B ≅ B') :
    intersectionNumber k p (𝟙 S) 2 hS ![A, B] = intersectionNumber k p (𝟙 S) 2 hS ![A, B'] :=
  intersectionNumber_eq_of_iso_at k p (𝟙 S) 2 hS ![A, B] ![A, B'] 1
    (fun q hq => by fin_cases q <;> first | exact absurd rfl hq | rfl) e

/-- **The intersection pairing is additive in the second slot** ([Stacks, Tag 0BER]):
`(𝓨 · 𝓜 ⊗ 𝓝) = (𝓨 · 𝓜) + (𝓨 · 𝓝)`. -/
public theorem intersectionNumber_vecCons_tensor_right (hS : topologicalKrullDim S ≤ (2 : ℕ))
    (Y M N : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 Y]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 M]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 N] :
    intersectionNumber k p (𝟙 S) 2 hS ![Y, Scheme.Modules.tensorObj M N] =
      intersectionNumber k p (𝟙 S) 2 hS ![Y, M] + intersectionNumber k p (𝟙 S) 2 hS ![Y, N] := by
  have e1 : Function.update ![Y, Scheme.Modules.tensorObj M N] 1 M = ![Y, M] :=
    funext fun j => by fin_cases j <;> rfl
  have e2 : Function.update ![Y, Scheme.Modules.tensorObj M N] 1 N = ![Y, N] :=
    funext fun j => by fin_cases j <;> rfl
  refine (intersectionNumber_update_tensor k p (𝟙 S) 2 hS 1 ![Y, Scheme.Modules.tensorObj M N]
    M N (Iso.refl _)).trans ?_
  exact congrArg₂ (· + ·) (intersectionNumber_congr_family k p (𝟙 S) 2 hS e1)
    (intersectionNumber_congr_family k p (𝟙 S) 2 hS e2)

/-- Pulling back along the identity does not change the second slot of the pairing. -/
private theorem intersectionNumber_vecCons_pullback_id_right (hS : topologicalKrullDim S ≤ (2 : ℕ))
    (A B : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 B] :
    intersectionNumber k p (𝟙 S) 2 hS ![A, (Scheme.Modules.pullback (𝟙 S)).obj B] =
      intersectionNumber k p (𝟙 S) 2 hS ![A, B] :=
  intersectionNumber_vecCons_congr_right k p hS A ((Scheme.Modules.pullbackId S).app B)

variable [IsIntegral S]

/-- **The intersection pairing on a surface is invariant under its automorphisms over `k`**:
`(g^*𝓐 · g^*𝓑) = (𝓐 · 𝓑)`.  This is `AlgebraicGeometry.intersectionNumber_pullback_of_isIso`. -/
public theorem intersectionNumber_pullback_vecCons (hS : topologicalKrullDim S = (2 : ℕ))
    (g : S ⟶ S) [IsIso g] (hg : g ≫ p = p) (A B : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 B] :
    intersectionNumber k p (𝟙 S) 2 hS.le
        ![(Scheme.Modules.pullback g).obj A, (Scheme.Modules.pullback g).obj B] =
      intersectionNumber k p (𝟙 S) 2 hS.le ![A, B] := by
  rw [← intersectionNumber_pullback_of_isIso k p p g hg 2 hS hS.le ![A, B]]
  exact intersectionNumber_congr_family k p (𝟙 S) 2 hS.le
    (funext fun j => by fin_cases j <;> rfl)

/-- **Moving an automorphism across the intersection pairing**:
`(𝓧 · g^*𝓜) = ((g⁻¹)^*𝓧 · 𝓜)` for an automorphism `g` of `S` over `k`. -/
public theorem intersectionNumber_vecCons_pullback_right (hS : topologicalKrullDim S = (2 : ℕ))
    (g : S ≅ S) (hg : g.hom ≫ p = p) (X M : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 X]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 M] :
    intersectionNumber k p (𝟙 S) 2 hS.le ![X, (Scheme.Modules.pullback g.hom).obj M] =
      intersectionNumber k p (𝟙 S) 2 hS.le ![(Scheme.Modules.pullback g.inv).obj X, M] := by
  have hginv : g.inv ≫ p = p := (Iso.inv_comp_eq g).mpr hg.symm
  rw [← intersectionNumber_pullback_vecCons k p hS g.inv hginv X]
  refine intersectionNumber_vecCons_congr_right k p hS.le _ ?_
  exact (Scheme.Modules.pullbackComp g.inv g.hom).app M ≪≫
    (Scheme.Modules.pullbackCongr g.inv_hom_id).app M ≪≫ (Scheme.Modules.pullbackId S).app M

/-- **Moving an automorphism across the intersection pairing**, the other way round:
`((g⁻¹)^*𝓧 · 𝓜) = (𝓧 · g^*𝓜)`. -/
public theorem intersectionNumber_vecCons_pullback_inv_left (hS : topologicalKrullDim S = (2 : ℕ))
    (g : S ≅ S) (hg : g.hom ≫ p = p) (X M : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 X]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 M] :
    intersectionNumber k p (𝟙 S) 2 hS.le ![(Scheme.Modules.pullback g.inv).obj X, M] =
      intersectionNumber k p (𝟙 S) 2 hS.le ![X, (Scheme.Modules.pullback g.hom).obj M] :=
  (intersectionNumber_vecCons_pullback_right k p hS g hg X M).symm

/-- Moving an automorphism `a` across the pairing when pulling back along `a ≫ b`. -/
private theorem intersectionNumber_vecCons_pullback_comp_right
    (hS : topologicalKrullDim S = (2 : ℕ)) (a b : S ≅ S) (ha : a.hom ≫ p = p)
    (X M : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 X]
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 M] :
    intersectionNumber k p (𝟙 S) 2 hS.le ![X, (Scheme.Modules.pullback (a.hom ≫ b.hom)).obj M] =
      intersectionNumber k p (𝟙 S) 2 hS.le
        ![(Scheme.Modules.pullback a.inv).obj X, (Scheme.Modules.pullback b.hom).obj M] :=
  (intersectionNumber_vecCons_congr_right k p hS.le X
    (B' := (Scheme.Modules.pullback a.hom).obj ((Scheme.Modules.pullback b.hom).obj M))
    ((Scheme.Modules.pullbackComp a.hom b.hom).app M).symm).trans
    (intersectionNumber_vecCons_pullback_right k p hS a ha X _)

/-- **An automorphism over `k` carries ample modules to ample modules and preserves their
self-intersection**: `g^*𝓐` is ample and `(g^*𝓐 · g^*𝓐) = (𝓐 · 𝓐)`. -/
public theorem isAmple_pullback_and_intersectionNumber_eq (hS : topologicalKrullDim S = (2 : ℕ))
    (g : S ⟶ S) [IsIso g] (hg : g ≫ p = p) (A : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A] (hA : Scheme.Modules.IsAmple S A) :
    Scheme.Modules.IsAmple S ((Scheme.Modules.pullback g).obj A) ∧
      intersectionNumber k p (𝟙 S) 2 hS.le
          ![(Scheme.Modules.pullback g).obj A, (Scheme.Modules.pullback g).obj A] =
        intersectionNumber k p (𝟙 S) 2 hS.le ![A, A] :=
  ⟨isAmple_pullback_of_isFinite g A hA, intersectionNumber_pullback_vecCons k p hS g hg A A⟩

end Pairing

/-! ### The relations of a cyclic triple of pencils with a covering involution -/

section Growth

variable (k : Type u) [Field k] {S : Scheme.{u}} (p : S ⟶ Spec (.of k)) [IsProper p]
  [IsIntegral S] (hS : topologicalKrullDim S = (2 : ℕ))

/-- **The numerical relations of a Wehler pair of automorphisms.**  On an integral surface `S`
proper over `k`, invertible modules `𝓗_0, 𝓗_1, 𝓗_2`, an ample invertible module `𝓐` and
automorphisms `ρ`, `σ` of `S` over `k` such that, against every invertible module `𝓨`,

* `(𝓨 · 𝓐) = (𝓨 · 𝓗_0) + (𝓨 · 𝓗_1) + (𝓨 · 𝓗_2)`,
* `(𝓨 · ρ^*𝓗_i) = (𝓨 · 𝓗_{i+1})`, the index read modulo three,
* `(𝓨 · σ^*𝓗_0) = (𝓨 · 𝓗_0)`, `(𝓨 · σ^*𝓗_1) = (𝓨 · 𝓗_1)` and
  `(𝓨 · σ^*𝓗_2) + (𝓨 · 𝓗_2) = 2 (𝓨 · 𝓗_0) + 2 (𝓨 · 𝓗_1)`.

These are the relations satisfied, up to numerical equivalence, by the three pencils, the
cyclic permutation of the factors and the covering involution of the second projection on a
cyclically symmetric smooth `(2, 2, 2)`-hypersurface of `ℙ^1 × ℙ^1 × ℙ^1`. -/
public structure WehlerRelations (H : Fin 3 → S.Modules)
    [∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (H i)] (A : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A] (ρ σ : Aut S) : Prop where
  hom_ρ : ρ.asIso.hom ≫ p = p
  hom_σ : σ.asIso.hom ≫ p = p
  isAmple : Scheme.Modules.IsAmple S A
  pair_ample : ∀ (Y : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 Y],
    intersectionNumber k p (𝟙 S) 2 hS.le ![Y, A] =
      intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 0] +
        intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 1] +
          intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 2]
  pair_ρ : ∀ (Y : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 Y]
    (i : Fin 3),
      intersectionNumber k p (𝟙 S) 2 hS.le ![Y, (Scheme.Modules.pullback ρ.asIso.hom).obj (H i)] =
        intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H (i + 1)]
  pair_σ_zero : ∀ (Y : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 Y],
    intersectionNumber k p (𝟙 S) 2 hS.le ![Y, (Scheme.Modules.pullback σ.asIso.hom).obj (H 0)] =
      intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 0]
  pair_σ_one : ∀ (Y : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 Y],
    intersectionNumber k p (𝟙 S) 2 hS.le ![Y, (Scheme.Modules.pullback σ.asIso.hom).obj (H 1)] =
      intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 1]
  pair_σ_two : ∀ (Y : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 Y],
    intersectionNumber k p (𝟙 S) 2 hS.le ![Y, (Scheme.Modules.pullback σ.asIso.hom).obj (H 2)] +
        intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 2] =
      2 * intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 0] +
        2 * intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 1]

namespace WehlerRelations

variable {k p hS} {H : Fin 3 → S.Modules}
  [∀ i, SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 (H i)] {A : S.Modules}
  [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 A] {ρ σ : Aut S}

omit [IsIntegral S] in
/-- The self-intersection of the ample module is the sum of the entries of the intersection
matrix of the three pencils. -/
private theorem intersectionNumber_self_eq_sum (h : WehlerRelations k p hS H A ρ σ) :
    intersectionNumber k p (𝟙 S) 2 hS.le ![A, A] =
      ∑ i : Fin 3, ∑ j : Fin 3, intersectionNumber k p (𝟙 S) 2 hS.le ![H i, H j] := by
  have hAj : ∀ j, intersectionNumber k p (𝟙 S) 2 hS.le ![A, H j] =
      ∑ i : Fin 3, intersectionNumber k p (𝟙 S) 2 hS.le ![H i, H j] := fun j => by
    rw [intersectionNumber_vecCons_comm, h.pair_ample (H j), Fin.sum_univ_three]
    linarith [intersectionNumber_vecCons_comm k p hS.le (H j) (H 0),
      intersectionNumber_vecCons_comm k p hS.le (H j) (H 1),
      intersectionNumber_vecCons_comm k p hS.le (H j) (H 2)]
  rw [h.pair_ample A, hAj 0, hAj 1, hAj 2]
  simp only [Fin.sum_univ_three]
  ring

/-- **The intersection matrix of the three pencils** is `b (J - I)` with `b > 0`: the
self-intersections `(𝓗_i · 𝓗_i)` vanish and the mixed ones `(𝓗_i · 𝓗_j)`, `i ≠ j`, are all
equal to one positive integer `b`, with `(𝓐 · 𝓐) = 6 b`. -/
public theorem exists_intersectionMatrix (h : WehlerRelations k p hS H A ρ σ) :
    ∃ b : ℤ, 0 < b ∧
      (∀ i j : Fin 3, intersectionNumber k p (𝟙 S) 2 hS.le ![H i, H j] = if i = j then 0 else b) ∧
      intersectionNumber k p (𝟙 S) 2 hS.le ![A, A] = 6 * b := by
  have : IsIso ρ.asIso.hom := @Iso.isIso_hom _ _ S S ρ.asIso
  have : IsIso σ.asIso.hom := @Iso.isIso_hom _ _ S S σ.asIso
  set x : Fin 3 → Fin 3 → ℤ := fun i j => intersectionNumber k p (𝟙 S) 2 hS.le ![H i, H j]
    with hx
  have hcomm : ∀ i j, x i j = x j i := fun i j =>
    intersectionNumber_vecCons_comm k p hS.le (H i) (H j)
  have hshift : ∀ i j, x (i + 1) (j + 1) = x i j := fun i j => by
    have h1 := intersectionNumber_pullback_vecCons k p hS ρ.asIso.hom h.hom_ρ (H i) (H j)
    rw [h.pair_ρ, intersectionNumber_vecCons_comm, h.pair_ρ] at h1
    exact (hcomm _ _).trans h1
  -- the covering involution
  set Q := (Scheme.Modules.pullback σ.asIso.hom).obj (H 2) with hQ
  have hQQ : intersectionNumber k p (𝟙 S) 2 hS.le ![Q, Q] = x 2 2 :=
    intersectionNumber_pullback_vecCons k p hS σ.asIso.hom h.hom_σ (H 2) (H 2)
  have hQ2 := h.pair_σ_two Q
  have hQj : ∀ j, intersectionNumber k p (𝟙 S) 2 hS.le ![Q, H j] =
      2 * x j 0 + 2 * x j 1 - x j 2 := fun j => by
    have := h.pair_σ_two (H j)
    rw [intersectionNumber_vecCons_comm k p hS.le Q (H j)]
    simp only [hx]
    linarith
  rw [hQQ, hQj 0, hQj 1, hQj 2] at hQ2
  have e00 : x 1 1 = x 0 0 := hshift 0 0
  have e11 : x 2 2 = x 1 1 := hshift 1 1
  have e01 : x 1 2 = x 0 1 := hshift 0 1
  have e12 : x 2 0 = x 1 2 := hshift 1 2
  have c10 := hcomm 1 0
  have c20 := hcomm 2 0
  have c21 := hcomm 2 1
  have c02 := hcomm 0 2
  have ha : x 0 0 = 0 := by linarith
  -- the ample module
  have hAA : intersectionNumber k p (𝟙 S) 2 hS.le ![A, A] = ∑ i : Fin 3, ∑ j : Fin 3, x i j :=
    h.intersectionNumber_self_eq_sum
  simp only [Fin.sum_univ_three] at hAA
  have hpos : 0 < intersectionNumber k p (𝟙 S) 2 hS.le ![A, A] :=
    intersectionNumber_pos k p (𝟙 S) 2 hS ![A, A] fun j => by fin_cases j <;> exact h.isAmple
  refine ⟨x 0 1, by linarith, fun i j => ?_, by linarith⟩
  fin_cases i <;> fin_cases j <;> simp <;> linarith

omit [IsIntegral S] in
/-- **The Wehler relations from isomorphisms of invertible modules.**  If `ρ^*𝓗_i ≅ 𝓗_{i+1}`,
`σ^*𝓗_0 ≅ 𝓗_0`, `σ^*𝓗_1 ≅ 𝓗_1`, `σ^*𝓗_2 ⊗ 𝓗_2 ≅ (𝓗_0 ⊗ 𝓗_0) ⊗ (𝓗_1 ⊗ 𝓗_1)` and
`𝓐 ≅ (𝓗_0 ⊗ 𝓗_1) ⊗ 𝓗_2` is ample, then the numerical relations hold, by additivity of the
intersection pairing ([Stacks, Tag 0BER]). -/
public theorem of_isos (hρ : ρ.asIso.hom ≫ p = p) (hσ : σ.asIso.hom ≫ p = p)
    (hA : Scheme.Modules.IsAmple S A)
    (eA : A ≅ Scheme.Modules.tensorObj (Scheme.Modules.tensorObj (H 0) (H 1)) (H 2))
    (eρ : ∀ i : Fin 3, (Scheme.Modules.pullback ρ.asIso.hom).obj (H i) ≅ H (i + 1))
    (eσ0 : (Scheme.Modules.pullback σ.asIso.hom).obj (H 0) ≅ H 0)
    (eσ1 : (Scheme.Modules.pullback σ.asIso.hom).obj (H 1) ≅ H 1)
    (eσ2 : Scheme.Modules.tensorObj ((Scheme.Modules.pullback σ.asIso.hom).obj (H 2)) (H 2) ≅
      Scheme.Modules.tensorObj (Scheme.Modules.tensorObj (H 0) (H 0))
        (Scheme.Modules.tensorObj (H 1) (H 1))) :
    WehlerRelations k p hS H A ρ σ where
  hom_ρ := hρ
  hom_σ := hσ
  isAmple := hA
  pair_ample Y _ := by
    rw [intersectionNumber_vecCons_congr_right k p hS.le Y eA,
      intersectionNumber_vecCons_tensor_right, intersectionNumber_vecCons_tensor_right]
  pair_ρ Y _ i := intersectionNumber_vecCons_congr_right k p hS.le Y (eρ i)
  pair_σ_zero Y _ := intersectionNumber_vecCons_congr_right k p hS.le Y eσ0
  pair_σ_one Y _ := intersectionNumber_vecCons_congr_right k p hS.le Y eσ1
  pair_σ_two Y _ := by
    rw [← intersectionNumber_vecCons_tensor_right,
      intersectionNumber_vecCons_congr_right k p hS.le Y eσ2,
      intersectionNumber_vecCons_tensor_right, intersectionNumber_vecCons_tensor_right,
      intersectionNumber_vecCons_tensor_right]
    ring

omit [IsIntegral S] in
/-- **The Wehler relations from isomorphisms, with the involution relation in its twisted
form.** As `AlgebraicGeometry.WehlerRelations.of_isos`, with the relation for `σ` given as
`σ^*𝓗_2 ⊗ 𝓗_2² ≅ ((𝓗_0 ⊗ 𝓗_0) ⊗ (𝓗_1 ⊗ 𝓗_1)) ⊗ 𝓗_2`, the form in which the covering involution
of a family of binary quadrics provides it (`Stacks.BinaryQuadric.quadricInvolutionTwistIso`):
cancelling one `𝓗_2` numerically gives the relation of `of_isos`. -/
public theorem of_isos_of_twist (hρ : ρ.asIso.hom ≫ p = p) (hσ : σ.asIso.hom ≫ p = p)
    (hA : Scheme.Modules.IsAmple S A)
    (eA : A ≅ Scheme.Modules.tensorObj (Scheme.Modules.tensorObj (H 0) (H 1)) (H 2))
    (eρ : ∀ i : Fin 3, (Scheme.Modules.pullback ρ.asIso.hom).obj (H i) ≅ H (i + 1))
    (eσ0 : (Scheme.Modules.pullback σ.asIso.hom).obj (H 0) ≅ H 0)
    (eσ1 : (Scheme.Modules.pullback σ.asIso.hom).obj (H 1) ≅ H 1)
    (eσ2 : Scheme.Modules.tensorObj ((Scheme.Modules.pullback σ.asIso.hom).obj (H 2))
        (Scheme.Modules.tensorObj (H 2) (H 2)) ≅
      Scheme.Modules.tensorObj (Scheme.Modules.tensorObj (Scheme.Modules.tensorObj (H 0) (H 0))
        (Scheme.Modules.tensorObj (H 1) (H 1))) (H 2)) :
    WehlerRelations k p hS H A ρ σ where
  hom_ρ := hρ
  hom_σ := hσ
  isAmple := hA
  pair_ample Y _ := by
    rw [intersectionNumber_vecCons_congr_right k p hS.le Y eA,
      intersectionNumber_vecCons_tensor_right, intersectionNumber_vecCons_tensor_right]
  pair_ρ Y _ i := intersectionNumber_vecCons_congr_right k p hS.le Y (eρ i)
  pair_σ_zero Y _ := intersectionNumber_vecCons_congr_right k p hS.le Y eσ0
  pair_σ_one Y _ := intersectionNumber_vecCons_congr_right k p hS.le Y eσ1
  pair_σ_two Y _ := by
    have h := intersectionNumber_vecCons_congr_right k p hS.le Y eσ2
    rw [intersectionNumber_vecCons_tensor_right, intersectionNumber_vecCons_tensor_right,
      intersectionNumber_vecCons_tensor_right, intersectionNumber_vecCons_tensor_right,
      intersectionNumber_vecCons_tensor_right, intersectionNumber_vecCons_tensor_right] at h
    linarith

omit [IsIntegral S] in
/-- The composite `τ = σ ∘ ρ` of the two automorphisms is again an automorphism over `k`, and so
are all its powers. -/
public theorem pow_hom_comp (h : WehlerRelations k p hS H A ρ σ) (n : ℕ) :
    ((σ * ρ) ^ n).asIso.hom ≫ p = p := by
  induction n with
  | zero =>
    rw [pow_zero]
    exact Category.id_comp p
  | succ n ih =>
    have e : ((σ * ρ) ^ (n + 1)).asIso.hom =
        ((σ * ρ) ^ n).asIso.hom ≫ ρ.asIso.hom ≫ σ.asIso.hom := by
      rw [pow_succ']
      rfl
    rw [e, Category.assoc, Category.assoc, h.hom_σ, h.hom_ρ, ih]

/-- **The action of `τ = σ ∘ ρ` on the three pencils**, against an arbitrary invertible module:
`τ^*𝓗_0 ≡ 𝓗_1`, `τ^*𝓗_1 ≡ 𝓗_2` and `τ^*𝓗_2 ≡ 2 𝓗_1 + 2 𝓗_2 - 𝓗_0`. -/
public theorem pair_mul_pullback (h : WehlerRelations k p hS H A ρ σ) (Y : S.Modules)
    [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 Y] :
    intersectionNumber k p (𝟙 S) 2 hS.le
        ![Y, (Scheme.Modules.pullback (σ * ρ).asIso.hom).obj (H 0)] =
        intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 1] ∧
      intersectionNumber k p (𝟙 S) 2 hS.le
          ![Y, (Scheme.Modules.pullback (σ * ρ).asIso.hom).obj (H 1)] =
        intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 2] ∧
      intersectionNumber k p (𝟙 S) 2 hS.le
          ![Y, (Scheme.Modules.pullback (σ * ρ).asIso.hom).obj (H 2)] =
        2 * intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 1] +
          2 * intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 2] -
            intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 0] := by
  have hM : ∀ (M : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 M],
      intersectionNumber k p (𝟙 S) 2 hS.le ![Y, (Scheme.Modules.pullback (σ * ρ).asIso.hom).obj M] =
        intersectionNumber k p (𝟙 S) 2 hS.le
          ![(Scheme.Modules.pullback ρ.asIso.inv).obj Y,
            (Scheme.Modules.pullback σ.asIso.hom).obj M] := by
    intro M _
    exact intersectionNumber_vecCons_pullback_comp_right k p hS ρ.asIso σ.asIso h.hom_ρ Y M
  have hρY : ∀ i : Fin 3, intersectionNumber k p (𝟙 S) 2 hS.le
      ![(Scheme.Modules.pullback ρ.asIso.inv).obj Y, H i] =
        intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H (i + 1)] := fun i => by
    rw [intersectionNumber_vecCons_pullback_inv_left k p hS ρ.asIso h.hom_ρ, h.pair_ρ]
  refine ⟨?_, ?_, ?_⟩
  · rw [hM, h.pair_σ_zero, hρY]
    rfl
  · rw [hM, h.pair_σ_one, hρY]
    rfl
  · have h2 := h.pair_σ_two ((Scheme.Modules.pullback ρ.asIso.inv).obj Y)
    rw [hM]
    have e0 : _ = intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 1] := hρY 0
    have e1 : _ = intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 2] := hρY 1
    have e2 : _ = intersectionNumber k p (𝟙 S) 2 hS.le ![Y, H 0] := hρY 2
    linarith

/-- **The intersection numbers `(𝓐 · (τ^n)^*𝓗_j)` obey a linear recursion**, and pairing with
`(τ^n)^*𝓐` is their sum. -/
public theorem pair_pow_succ_pullback (h : WehlerRelations k p hS H A ρ σ) (n : ℕ) :
    (intersectionNumber k p (𝟙 S) 2 hS.le
        ![A, (Scheme.Modules.pullback ((σ * ρ) ^ (n + 1)).asIso.hom).obj (H 0)] =
      intersectionNumber k p (𝟙 S) 2 hS.le
        ![A, (Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj (H 1)]) ∧
    (intersectionNumber k p (𝟙 S) 2 hS.le
        ![A, (Scheme.Modules.pullback ((σ * ρ) ^ (n + 1)).asIso.hom).obj (H 1)] =
      intersectionNumber k p (𝟙 S) 2 hS.le
        ![A, (Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj (H 2)]) ∧
    (intersectionNumber k p (𝟙 S) 2 hS.le
        ![A, (Scheme.Modules.pullback ((σ * ρ) ^ (n + 1)).asIso.hom).obj (H 2)] =
      2 * intersectionNumber k p (𝟙 S) 2 hS.le
          ![A, (Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj (H 1)] +
        2 * intersectionNumber k p (𝟙 S) 2 hS.le
          ![A, (Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj (H 2)] -
        intersectionNumber k p (𝟙 S) 2 hS.le
          ![A, (Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj (H 0)]) := by
  set g := (σ * ρ) ^ n with hg
  have hgp : g.asIso.hom ≫ p = p := h.pow_hom_comp n
  have hsplit : ∀ (M : S.Modules) [SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 M],
      intersectionNumber k p (𝟙 S) 2 hS.le
          ![A, (Scheme.Modules.pullback ((σ * ρ) ^ (n + 1)).asIso.hom).obj M] =
        intersectionNumber k p (𝟙 S) 2 hS.le
          ![(Scheme.Modules.pullback g.asIso.inv).obj A,
            (Scheme.Modules.pullback (σ * ρ).asIso.hom).obj M] := by
    intro M _
    have e : ((σ * ρ) ^ (n + 1)).asIso.hom = g.asIso.hom ≫ (σ * ρ).asIso.hom := by
      rw [hg, pow_succ']; rfl
    rw [e]
    exact intersectionNumber_vecCons_pullback_comp_right k p hS g.asIso (σ * ρ).asIso hgp A M
  have hback : ∀ i : Fin 3, intersectionNumber k p (𝟙 S) 2 hS.le
      ![(Scheme.Modules.pullback g.asIso.inv).obj A, H i] =
        intersectionNumber k p (𝟙 S) 2 hS.le
          ![A, (Scheme.Modules.pullback g.asIso.hom).obj (H i)] :=
    fun i => intersectionNumber_vecCons_pullback_inv_left k p hS g.asIso hgp A (H i)
  obtain ⟨t0, t1, t2⟩ := h.pair_mul_pullback ((Scheme.Modules.pullback g.asIso.inv).obj A)
  refine ⟨?_, ?_, ?_⟩
  · rw [hsplit, t0, hback]
  · rw [hsplit, t1, hback]
  · rw [hsplit, t2, hback, hback, hback]

/-- Pairing with `(τ^n)^*𝓐` is the sum of the pairings with the `(τ^n)^*𝓗_j`. -/
public theorem pair_pow_pullback_ample (h : WehlerRelations k p hS H A ρ σ) (n : ℕ) :
    intersectionNumber k p (𝟙 S) 2 hS.le
        ![A, (Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj A] =
      intersectionNumber k p (𝟙 S) 2 hS.le
          ![A, (Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj (H 0)] +
        intersectionNumber k p (𝟙 S) 2 hS.le
          ![A, (Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj (H 1)] +
        intersectionNumber k p (𝟙 S) 2 hS.le
          ![A, (Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj (H 2)] := by
  have hgp := h.pow_hom_comp n
  simp only [← intersectionNumber_vecCons_pullback_inv_left k p hS _ hgp A]
  exact h.pair_ample _

/-- **The growth of the intersection numbers.**  For every `n`, with `τ = σ ∘ ρ`,

`(𝓐 · 𝓐) + n ≤ (𝓐 · (τ^n)^*𝓐)`,

while `(τ^n)^*𝓐` is ample with `((τ^n)^*𝓐 · (τ^n)^*𝓐) = (𝓐 · 𝓐)`
(`AlgebraicGeometry.isAmple_pullback_and_intersectionNumber_eq`). -/
public theorem intersectionNumber_add_le_pow_pullback (h : WehlerRelations k p hS H A ρ σ)
    (n : ℕ) :
    intersectionNumber k p (𝟙 S) 2 hS.le ![A, A] + n ≤
      intersectionNumber k p (𝟙 S) 2 hS.le
        ![A, (Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj A] := by
  obtain ⟨b, hb, hx, hAA⟩ := h.exists_intersectionMatrix
  set u : ℕ → Fin 3 → ℤ := fun n j => intersectionNumber k p (𝟙 S) 2 hS.le
    ![A, (Scheme.Modules.pullback ((σ * ρ) ^ n).asIso.hom).obj (H j)] with hu
  have hu0 : ∀ j, u 0 j = 2 * b := by
    intro j
    simp only [hu]
    have e0 : ((σ * ρ) ^ 0).asIso.hom = 𝟙 S := by
      rw [pow_zero]
      rfl
    rw [e0, intersectionNumber_vecCons_pullback_id_right, intersectionNumber_vecCons_comm,
      h.pair_ample (H j), hx, hx, hx]
    fin_cases j <;> simp <;> ring
  have hrec : ∀ n, u (n + 1) 0 = u n 1 ∧ u (n + 1) 1 = u n 2 ∧
      u (n + 1) 2 = 2 * u n 1 + 2 * u n 2 - u n 0 := fun n => h.pair_pow_succ_pullback n
  have key : ∀ n : ℕ, 0 < u n 0 ∧ u n 0 ≤ u n 1 ∧ u n 1 ≤ u n 2 ∧
      6 * b + n ≤ u n 0 + u n 1 + u n 2 := by
    intro n
    induction n with
    | zero =>
      rw [hu0, hu0, hu0]
      exact ⟨by linarith, le_rfl, le_rfl, by push_cast; linarith⟩
    | succ n ih =>
      obtain ⟨r0, r1, r2⟩ := hrec n
      obtain ⟨i0, i1, i2, i3⟩ := ih
      rw [r0, r1, r2]
      refine ⟨by linarith, i2, by linarith, by push_cast; linarith⟩
  rw [h.pair_pow_pullback_ample n, hAA]
  exact (key n).2.2.2

/-- **The automorphism `τ = σ ∘ ρ` has infinite order**: none of its positive powers is the
identity.  In particular the automorphism group of `S` over `k` is infinite. -/
public theorem pow_ne_one (h : WehlerRelations k p hS H A ρ σ) {n : ℕ} (hn : 0 < n) :
    (σ * ρ) ^ n ≠ 1 := by
  intro h1
  have hle := h.intersectionNumber_add_le_pow_pullback n
  rw [h1] at hle
  change _ ≤ intersectionNumber k p (𝟙 S) 2 hS.le
    ![A, (Scheme.Modules.pullback (𝟙 S)).obj A] at hle
  rw [intersectionNumber_vecCons_pullback_id_right] at hle
  change _ + _ ≤ intersectionNumber k p (𝟙 S) 2 hS.le ![A, A] at hle
  linarith [show (0 : ℤ) < n by exact_mod_cast hn]

/-- **No bound on `(𝓗_1 · 𝓗_2)` in terms of `(𝓗_1 · 𝓗_1)` and `(𝓗_2 · 𝓗_2)`.**  On a surface
with Wehler relations, the ample invertible modules `𝓐` and `𝓝 = (τ^n)^*𝓐` have the fixed
self-intersections `(𝓐 · 𝓐)`, while `(𝓐 · 𝓝)` exceeds any given integer for suitable `n`. -/
public theorem exists_isAmple_intersectionNumber_gt (h : WehlerRelations k p hS H A ρ σ)
    (N : ℤ) : ∃ (B : S.Modules) (_ : SheafOfModules.IsInvertible S.presheaf S.ringCatSheaf.2 B),
      Scheme.Modules.IsAmple S B ∧
      intersectionNumber k p (𝟙 S) 2 hS.le ![B, B] =
        intersectionNumber k p (𝟙 S) 2 hS.le ![A, A] ∧
      N < intersectionNumber k p (𝟙 S) 2 hS.le ![A, B] := by
  obtain ⟨n, hn⟩ := exists_nat_gt (N - intersectionNumber k p (𝟙 S) 2 hS.le ![A, A])
  have hgp := h.pow_hom_comp n
  have : IsIso ((σ * ρ) ^ n).asIso.hom := @Iso.isIso_hom _ _ S S ((σ * ρ) ^ n).asIso
  obtain ⟨hamp, hself⟩ := isAmple_pullback_and_intersectionNumber_eq k p hS
    ((σ * ρ) ^ n).asIso.hom hgp A h.isAmple
  refine ⟨_, inferInstance, hamp, hself, ?_⟩
  linarith [h.intersectionNumber_add_le_pow_pullback n]

end WehlerRelations

end Growth

end AlgebraicGeometry

end
