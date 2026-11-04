module

public import StacksFrontier.AlgebraicGeometry.Chow.PeriodicComplexesDeterminants.Formula

/-!
# Determinants along a local homomorphism with extended maximal ideal

Let `(R, 𝔪, κ) → (R', 𝔪', κ')` be a local homomorphism with `𝔪' = 𝔪 R'`, let `M` be a
finite-length `R`-module, `M'` a finite-length `R'`-module and `g : M → M'` an `R`-linear map
with `length_{R'}(M') = length_R(M)`. Then `g` carries admissible sequences of `M` (Stacks 02P6)
to admissible sequences of `M'`: if `𝔪 x` lies in the span of some elements of `M`, then
`𝔪' g(x) = 𝔪 R' g(x)` lies in the `R'`-span of their images. The three families of admissible
relations are preserved as well, so `g` induces a map of determinants

`det_κ(M) → det_{κ'}(M')`, `[x_1, …, x_l] ↦ [g(x_1), …, g(x_l)]`,

semilinear over the induced map `κ → κ'` of residue fields.

For a map of exact two-periodic complexes `(M, φ, ψ) → (M', φ', ψ')` along which the two images
keep their lengths and whose target is generated over `R'` by the image of `M`, this map carries
the signed comparison of symbols characterizing the periodic determinant of Stacks 02PK over `R`
to the one over `R'`. Hence the periodic determinant of `(M', φ', ψ')` is the image in `κ'` of
the periodic determinant of `(M, φ, ψ)`.

## Main definitions

* `Stacks.Chow.mapSequence` — the image of a finite sequence, reindexed along an equality of
  lengths.
* `Stacks.Chow.mapAdmissibleSequence` — the image of an admissible symbol.
* `Stacks.Chow.determinantMap` — the induced semilinear map of determinants.
* `Stacks.Chow.rangeMap` — the map induced on the images of two compatible endomorphisms.

## Main results

* `Stacks.Chow.isAdmissibleSequence_mapSequence` — images of admissible sequences are admissible.
* `Stacks.Chow.determinantMap_symbol` — the determinant map on symbols.
* `Stacks.Chow.map_periodicDeterminant_of_map` — the periodic determinant is carried to the
  periodic determinant.

## References

* [Stacks Project, Tag 02P6](https://stacks.math.columbia.edu/tag/02P6)
* [Stacks Project, Tag 02PK](https://stacks.math.columbia.edu/tag/02PK)
-/

@[expose] public section

noncomputable section

open IsLocalRing Module.FiniteLength

universe u v w x

namespace Stacks.Chow

section Sequences

variable {R : Type u} {R' : Type v} [CommRing R] [CommRing R'] [Algebra R R']
  {M : Type w} [AddCommGroup M] [Module R M]
  {M' : Type x} [AddCommGroup M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']

/-- The image of a finite sequence under a map, reindexed along an equality of lengths. -/
def mapSequence (g : M →ₗ[R] M') {n n' : ℕ} (h : n' = n) (e : Fin n → M) : Fin n' → M' :=
  fun i ↦ g (e (Fin.cast h i))

omit [IsScalarTower R R' M'] in
/-- The `i`-th term of `mapSequence g h e` is `g` applied to the corresponding term of `e`. -/
@[simp]
theorem mapSequence_apply (g : M →ₗ[R] M') {n n' : ℕ} (h : n' = n) (e : Fin n → M)
    (i : Fin n') : mapSequence g h e i = g (e (Fin.cast h i)) :=
  rfl

omit [IsScalarTower R R' M'] in
/-- The term of `mapSequence g h e` at the index corresponding to `a` is `g (e a)`. -/
theorem mapSequence_cast_symm (g : M →ₗ[R] M') {n n' : ℕ} (h : n' = n) (e : Fin n → M)
    (a : Fin n) : mapSequence g h e (Fin.cast h.symm a) = g (e a) :=
  rfl

omit [IsScalarTower R R' M'] in
/-- The terms of `mapSequence g h e` before `i` are the images under `g` of the terms of `e`
before the corresponding index. -/
theorem image_mapSequence_Iio (g : M →ₗ[R] M') {n n' : ℕ} (h : n' = n) (e : Fin n → M)
    (i : Fin n') :
    mapSequence g h e '' Set.Iio i = g '' (e '' Set.Iio (Fin.cast h i)) := by
  ext y
  constructor
  · rintro ⟨j, hj, rfl⟩
    exact ⟨e (Fin.cast h j), ⟨Fin.cast h j, hj, rfl⟩, rfl⟩
  · rintro ⟨_, ⟨k, hk, rfl⟩, rfl⟩
    exact ⟨Fin.cast h.symm k, hk, rfl⟩

omit [IsScalarTower R R' M'] in
/-- Mapping a sequence with one term replaced by `m` replaces the corresponding term of the mapped
sequence by `g m`. -/
theorem mapSequence_update (g : M →ₗ[R] M') {n n' : ℕ} (h : n' = n) (e : Fin n → M)
    (a : Fin n) (m : M) :
    mapSequence g h (Function.update e a m) =
      Function.update (mapSequence g h e) (Fin.cast h.symm a) (g m) := by
  funext i
  by_cases hi : i = Fin.cast h.symm a
  · subst hi
    simp [mapSequence]
  · have hne : Fin.cast h i ≠ a := fun h' ↦ hi (by rw [← h']; rfl)
    simp [mapSequence, Function.update_of_ne hne, Function.update_of_ne hi]

/-- If `m` lies in the `R`-span of `T`, then `g m` lies in the `R'`-span of `g '' T`. -/
private theorem map_mem_span_image (g : M →ₗ[R] M') {T : Set M} {m : M}
    (hm : m ∈ Submodule.span R T) : g m ∈ Submodule.span R' (g '' T) :=
  Submodule.span_le_restrictScalars R R' _ (Submodule.apply_mem_span_image_of_mem_span g hm)

/-- If `m` lies in the `R`-span of the terms of `e` before an index, then `g m` lies in the
`R'`-span of the terms of `mapSequence g h e` before the corresponding index. -/
theorem map_mem_spanBefore (g : M →ₗ[R] M') {n n' : ℕ} (h : n' = n) (e : Fin n → M)
    (i : Fin n') {m : M} (hm : m ∈ spanBefore (R := R) e (Fin.cast h i)) :
    g m ∈ spanBefore (R := R') (mapSequence g h e) i := by
  rw [spanBefore, image_mapSequence_Iio]
  exact map_mem_span_image g hm

/-- If the terms of `e` span `M` over `R` and the image of `g` spans `M'` over `R'`, then the
terms of `mapSequence g h e` span `M'` over `R'`. -/
theorem span_range_mapSequence (g : M →ₗ[R] M')
    (hg : Submodule.span R' (Set.range g) = ⊤) {n n' : ℕ} (h : n' = n) {e : Fin n → M}
    (he : Submodule.span R (Set.range e) = ⊤) :
    Submodule.span R' (Set.range (mapSequence g h e)) = ⊤ := by
  have himage : Set.range (mapSequence g h e) = g '' Set.range e := by
    ext y
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨e (Fin.cast h i), ⟨_, rfl⟩, rfl⟩
    · rintro ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨Fin.cast h.symm i, rfl⟩
  rw [eq_top_iff, ← hg, Submodule.span_le]
  rintro _ ⟨m, rfl⟩
  have hm : m ∈ Submodule.span R (Set.range e) := he ▸ Submodule.mem_top
  rw [himage]
  exact map_mem_span_image g hm

/-- Reading a concatenation through a map and through equalities of lengths. -/
theorem map_append_cast (g : M →ₗ[R] M') {n m n' m' L L' : ℕ} (u : Fin n → M) (v : Fin m → M)
    (hn : n' = n) (hm : m' = m) (h : L = n + m) (h' : L' = n' + m') (hL : L' = L)
    (i : Fin L') :
    g (Fin.append u v (Fin.cast h (Fin.cast hL i))) =
      Fin.append (fun j ↦ g (u (Fin.cast hn j))) (fun j ↦ g (v (Fin.cast hm j)))
        (Fin.cast h' i) := by
  subst hn hm
  have hcast : Fin.cast h (Fin.cast hL i) = Fin.cast h' i := Fin.ext rfl
  rw [hcast]
  generalize Fin.cast h' i = k
  refine Fin.addCases (fun j ↦ ?_) (fun j ↦ ?_) k <;> simp

end Sequences

section DeterminantMap

variable {R : Type u} {R' : Type v} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
  [Algebra R R'] [IsLocalHom (algebraMap R R')]
  {M : Type w} [AddCommGroup M] [Module R M]
  {M' : Type x} [AddCommGroup M'] [Module R' M'] [Module R M'] [IsScalarTower R R' M']

omit [IsLocalHom (algebraMap R R')] in
/-- If the maximal ideal of `R'` is generated by that of `R`, and the maximal ideal of `R` moves
`m` into the span of `T`, then the maximal ideal of `R'` moves `g m` into the `R'`-span of the
image of `T`. -/
theorem smul_mem_span_image_of_le_map
    (hm : maximalIdeal R' ≤ Ideal.map (algebraMap R R') (maximalIdeal R))
    (g : M →ₗ[R] M') {T : Set M} {m : M}
    (h : ∀ r ∈ maximalIdeal R, r • m ∈ Submodule.span R T) :
    ∀ r' ∈ maximalIdeal R', r' • g m ∈ Submodule.span R' (g '' T) := by
  intro r' hr'
  have hr'' : r' ∈ Ideal.span (algebraMap R R' '' (maximalIdeal R : Set R)) := hm hr'
  clear hr'
  induction hr'' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨r, hr, rfl⟩ := hy
    rw [algebraMap_smul, ← map_smul]
    exact map_mem_span_image g (h r hr)
  | zero => simp
  | add y z _ _ hy hz =>
    rw [add_smul]
    exact add_mem hy hz
  | smul c y _ hy =>
    rw [smul_eq_mul, mul_smul]
    exact Submodule.smul_mem _ c hy

omit [IsLocalHom (algebraMap R R')] in
/-- **The image of an admissible sequence is admissible**, when the maximal ideal of `R'` is
generated by that of `R`. -/
theorem isAdmissibleSequence_mapSequence
    (hm : maximalIdeal R' ≤ Ideal.map (algebraMap R R') (maximalIdeal R))
    (g : M →ₗ[R] M') {n n' : ℕ} (h : n' = n) {e : Fin n → M}
    (he : IsAdmissibleSequence (R := R) e) :
    IsAdmissibleSequence (R := R') (mapSequence g h e) := by
  intro i r hr
  rw [spanBefore, image_mapSequence_Iio]
  exact smul_mem_span_image_of_le_map hm g (he (Fin.cast h i)) r hr

variable (hm : maximalIdeal R' ≤ Ideal.map (algebraMap R R') (maximalIdeal R))
  (g : M →ₗ[R] M') (hlen : moduleLength R' M' = moduleLength R M)

/-- The image of an admissible symbol of `M` in `M'`. -/
def mapAdmissibleSequence (e : AdmissibleSequence R M) : AdmissibleSequence R' M' :=
  ⟨mapSequence g hlen e.1, isAdmissibleSequence_mapSequence hm g hlen e.2⟩

omit [IsLocalHom (algebraMap R R')] in
/-- The underlying sequence of `mapAdmissibleSequence hm g hlen e` is the image of that of `e`. -/
@[simp]
theorem mapAdmissibleSequence_val (e : AdmissibleSequence R M) :
    (mapAdmissibleSequence hm g hlen e).1 = mapSequence g hlen e.1 :=
  rfl

/-- The map on the free vector spaces of admissible symbols, semilinear over the induced map of
residue fields. -/
def determinantFreeMap :
    DeterminantFree R M →ₛₗ[ResidueField.map (algebraMap R R')] determinant R' M' where
  toFun z := z.sum fun e c ↦
    ResidueField.map (algebraMap R R') c • symbol (mapAdmissibleSequence hm g hlen e)
  map_add' z w := Finsupp.sum_add_index' (fun _ ↦ by simp) (fun _ _ _ ↦ by rw [map_add, add_smul])
  map_smul' c z := by
    rw [Finsupp.sum_smul_index' (b := c) (g := z)
      (h := fun e c ↦ ResidueField.map (algebraMap R R') c •
        symbol (mapAdmissibleSequence hm g hlen e)) (fun _ ↦ by simp), Finsupp.smul_sum]
    simp only [smul_eq_mul, map_mul, mul_smul]

/-- The map `determinantFreeMap` sends `c` times the basis vector of an admissible symbol `e` to
the image of `c` in `κ'` times the symbol of the image of `e`. -/
theorem determinantFreeMap_single (e : AdmissibleSequence R M) (c : ResidueField R) :
    determinantFreeMap hm g hlen (Finsupp.single e c) =
      ResidueField.map (algebraMap R R') c • symbol (mapAdmissibleSequence hm g hlen e) := by
  show (Finsupp.single e c).sum (fun e c ↦ ResidueField.map (algebraMap R R') c •
    symbol (mapAdmissibleSequence hm g hlen e)) = _
  exact Finsupp.sum_single_index (by simp)

/-- The map `determinantFreeMap` kills the admissible relation swapping two adjacent terms. -/
theorem determinantFreeMap_swap (e : AdmissibleSequence R M) (a b : Fin (moduleLength R M))
    (hba : b.val + 1 = a.val) (ha : ∀ r ∈ maximalIdeal R, r • e.1 a ∈ spanBefore (R := R) e.1 b)
    (hswap : IsAdmissibleSequence (R := R)
      (Function.update (Function.update e.1 b (e.1 a)) a (e.1 b))) :
    determinantFreeMap hm g hlen (Finsupp.single e 1 +
      Finsupp.single ⟨Function.update (Function.update e.1 b (e.1 a)) a (e.1 b), hswap⟩ 1) = 0 := by
  rw [map_add, determinantFreeMap_single, determinantFreeMap_single, map_one, one_smul,
    one_smul, add_eq_zero_iff_eq_neg]
  have ha' : ∀ r ∈ maximalIdeal R',
      r • (mapAdmissibleSequence hm g hlen e).1 (Fin.cast hlen.symm a) ∈
        spanBefore (R := R') (mapAdmissibleSequence hm g hlen e).1 (Fin.cast hlen.symm b) := by
    intro r hr
    rw [spanBefore, mapAdmissibleSequence_val, image_mapSequence_Iio]
    exact smul_mem_span_image_of_le_map hm g ha r hr
  have hupdate : mapSequence g hlen
      (Function.update (Function.update e.1 b (e.1 a)) a (e.1 b)) =
      Function.update (Function.update (mapAdmissibleSequence hm g hlen e).1
          (Fin.cast hlen.symm b) ((mapAdmissibleSequence hm g hlen e).1 (Fin.cast hlen.symm a)))
        (Fin.cast hlen.symm a) ((mapAdmissibleSequence hm g hlen e).1 (Fin.cast hlen.symm b)) := by
    rw [mapSequence_update, mapSequence_update]
    rfl
  have hswap' : IsAdmissibleSequence (R := R')
      (Function.update (Function.update (mapAdmissibleSequence hm g hlen e).1
          (Fin.cast hlen.symm b) ((mapAdmissibleSequence hm g hlen e).1 (Fin.cast hlen.symm a)))
        (Fin.cast hlen.symm a) ((mapAdmissibleSequence hm g hlen e).1 (Fin.cast hlen.symm b))) :=
    hupdate ▸ isAdmissibleSequence_mapSequence hm g hlen hswap
  rw [symbol_swap (mapAdmissibleSequence hm g hlen e) (Fin.cast hlen.symm a)
    (Fin.cast hlen.symm b) hba ha' hswap']
  congr 2
  exact Subtype.ext hupdate.symm

/-- The admissible relations are carried to admissible relations. -/
theorem determinantRelations_le_ker :
    determinantRelations R M ≤ LinearMap.ker (determinantFreeMap hm g hlen) := by
  rw [determinantRelations, Submodule.span_le]
  intro z hz
  simp only [SetLike.mem_coe, LinearMap.mem_ker]
  cases hz with
  | dependent e a ha =>
    rw [determinantFreeMap_single, map_one, one_smul]
    exact symbol_eq_zero_of_mem_spanBefore _ (Fin.cast hlen.symm a)
      (map_mem_spanBefore g hlen e.1 (Fin.cast hlen.symm a) ha)
  | unitChange e a unit replacement y ha hy hreplacement =>
    rw [map_sub, LinearMap.map_smulₛₗ, determinantFreeMap_single, determinantFreeMap_single,
      map_one, one_smul, one_smul, sub_eq_zero]
    have ha' : (mapAdmissibleSequence hm g hlen e).1 (Fin.cast hlen.symm a) =
        ((Units.map (algebraMap R R').toMonoidHom unit : R'ˣ) : R') • g replacement + g y := by
      rw [mapAdmissibleSequence_val, mapSequence_cast_symm, ha, map_add, map_smul,
        Units.coe_map, RingHom.toMonoidHom_eq_coe, MonoidHom.coe_coe, algebraMap_smul]
    have hy' : g y ∈ spanBefore (R := R')
        (mapAdmissibleSequence hm g hlen e).1 (Fin.cast hlen.symm a) :=
      map_mem_spanBefore g hlen e.1 (Fin.cast hlen.symm a) hy
    have hupdate := mapSequence_update g hlen e.1 a replacement
    have hrep' : IsAdmissibleSequence (R := R')
        (Function.update (mapAdmissibleSequence hm g hlen e).1 (Fin.cast hlen.symm a)
          (g replacement)) :=
      hupdate ▸ isAdmissibleSequence_mapSequence hm g hlen hreplacement
    rw [symbol_unitChange (mapAdmissibleSequence hm g hlen e) (Fin.cast hlen.symm a)
      (Units.map (algebraMap R R').toMonoidHom unit) (g replacement) (g y) ha' hy' hrep',
      ResidueField.map_residue]
    congr 2
    exact Subtype.ext hupdate.symm
  | swap e a b hba ha hswap => exact determinantFreeMap_swap hm g hlen e a b hba ha hswap

/-- **The map of determinants induced by `g`**, semilinear over the induced map of residue
fields: `[x_1, …, x_l] ↦ [g(x_1), …, g(x_l)]`. -/
def determinantMap :
    determinant R M →ₛₗ[ResidueField.map (algebraMap R R')] determinant R' M' :=
  (determinantRelations R M).liftQ (determinantFreeMap hm g hlen)
    (determinantRelations_le_ker hm g hlen)

/-- The map `determinantMap` sends the symbol `[x_1, …, x_l]` to `[g(x_1), …, g(x_l)]`. -/
@[simp]
theorem determinantMap_symbol (e : AdmissibleSequence R M) :
    determinantMap hm g hlen (symbol e) = symbol (mapAdmissibleSequence hm g hlen e) := by
  rw [determinantMap, symbol, Submodule.liftQ_apply, determinantFreeMap_single, map_one,
    one_smul]

end DeterminantMap

section Periodic

variable {R : Type u} {R' : Type v} [CommRing R] [IsLocalRing R] [CommRing R'] [IsLocalRing R']
  [Algebra R R'] [IsLocalHom (algebraMap R R')]
  {N : Type w} [AddCommGroup N] [Module R N]
  {N' : Type x} [AddCommGroup N'] [Module R' N'] [Module R N'] [IsScalarTower R R' N']

/-- The map induced by `g` on the images of two endomorphisms it intertwines. -/
def rangeMap (g : N →ₗ[R] N') (φ : N →ₗ[R] N) (φ' : N' →ₗ[R'] N')
    (hgφ : ∀ n, g (φ n) = φ' (g n)) : LinearMap.range φ →ₗ[R] LinearMap.range φ' where
  toFun z := ⟨g z, by
    obtain ⟨n, hn⟩ := z.2
    exact ⟨g n, by rw [← hgφ, hn]⟩⟩
  map_add' _ _ := Subtype.ext (map_add g _ _)
  map_smul' c z := Subtype.ext (map_smul g c (z : N))

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] in
/-- The map `rangeMap g φ φ' hgφ` is the restriction of `g`. -/
@[simp]
theorem rangeMap_apply_coe (g : N →ₗ[R] N') (φ : N →ₗ[R] N) (φ' : N' →ₗ[R'] N')
    (hgφ : ∀ n, g (φ n) = φ' (g n)) (z : LinearMap.range φ) :
    (rangeMap g φ φ' hgφ z : N') = g z :=
  rfl

omit [IsLocalRing R] [IsLocalRing R'] [IsLocalHom (algebraMap R R')] in
/-- If `N'` is generated over `R'` by the image of `N`, then the image of `φ'` is generated over
`R'` by the image of the image of `φ`. -/
theorem span_range_rangeMap (g : N →ₗ[R] N') (hg : Submodule.span R' (Set.range g) = ⊤)
    (φ : N →ₗ[R] N) (φ' : N' →ₗ[R'] N') (hgφ : ∀ n, g (φ n) = φ' (g n)) :
    Submodule.span R' (Set.range (rangeMap g φ φ' hgφ)) = ⊤ := by
  have h1 : Submodule.map φ'.rangeRestrict (Submodule.span R' (Set.range g)) = ⊤ := by
    rw [hg, Submodule.map_top, LinearMap.range_rangeRestrict]
  rw [eq_top_iff, ← h1, Submodule.map_span, Submodule.span_le]
  rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
  exact Submodule.subset_span ⟨φ.rangeRestrict n, Subtype.ext (hgφ n)⟩

/-- **The periodic determinant along a local homomorphism with extended maximal ideal.** Let
`(R, 𝔪) → (R', 𝔪')` be a local homomorphism with `𝔪' = 𝔪 R'`, and let `g` be an `R`-linear map
from an exact two-periodic complex `(N, φ, ψ)` of finite length over `R` to an exact two-periodic
complex `(N', φ', ψ')` of finite length over `R'`, intertwining the differentials, whose image
generates `N'` over `R'`, and along which the images of the two differentials keep their
lengths. Then the periodic determinant of `(N', φ', ψ')` is the image of that of `(N, φ, ψ)`
under the induced map of residue fields. -/
theorem map_periodicDeterminant_of_map
    (hm : maximalIdeal R' ≤ Ideal.map (algebraMap R R') (maximalIdeal R))
    (φ ψ : N →ₗ[R] N) (hφψ : Function.Exact φ ψ) (hψφ : Function.Exact ψ φ)
    (hN : IsFiniteLength R N)
    (φ' ψ' : N' →ₗ[R'] N') (hφψ' : Function.Exact φ' ψ') (hψφ' : Function.Exact ψ' φ')
    (hN' : IsFiniteLength R' N')
    (g : N →ₗ[R] N') (hg : Submodule.span R' (Set.range g) = ⊤)
    (hgφ : ∀ n, g (φ n) = φ' (g n)) (hgψ : ∀ n, g (ψ n) = ψ' (g n))
    (hlenφ : moduleLength R' (LinearMap.range φ') = moduleLength R (LinearMap.range φ))
    (hlenψ : moduleLength R' (LinearMap.range ψ') = moduleLength R (LinearMap.range ψ)) :
    Units.map (ResidueField.map (algebraMap R R')).toMonoidHom
        (AlgebraicGeometry.periodicDeterminant φ ψ hφψ hψφ hN) =
      AlgebraicGeometry.periodicDeterminant φ' ψ' hφψ' hψφ' hN' := by
  classical
  have hφr := hN.of_injective (LinearMap.range φ).subtype_injective
  have hψr := hN.of_injective (LinearMap.range ψ).subtype_injective
  have hφr' := hN'.of_injective (LinearMap.range φ').subtype_injective
  have hψr' := hN'.of_injective (LinearMap.range ψ').subtype_injective
  obtain ⟨x, -, hxs⟩ := AlgebraicGeometry.exists_spanning_symbol hφr
  obtain ⟨y, -, hys⟩ := AlgebraicGeometry.exists_spanning_symbol hψr
  have hx := span_symbol_eq_top hφr x hxs
  have hy := span_symbol_eq_top hψr y hys
  choose xLift hxLift using fun i ↦ (x.1 i).2
  choose yLift hyLift using fun j ↦ (y.1 j).2
  obtain ⟨hl, hr, hleft, hright, hd⟩ := AlgebraicGeometry.periodicDeterminant_symbol_eq
    φ ψ hφψ hψφ hN x y hx hy xLift yLift hxLift hyLift
  let x' := mapAdmissibleSequence hm (rangeMap g φ φ' hgφ) hlenφ x
  let y' := mapAdmissibleSequence hm (rangeMap g ψ ψ' hgψ) hlenψ y
  have hx' : (ResidueField R') ∙ symbol x' = ⊤ := span_symbol_eq_top hφr' x'
    (span_range_mapSequence _ (span_range_rangeMap g hg φ φ' hgφ) hlenφ hxs)
  have hy' : (ResidueField R') ∙ symbol y' = ⊤ := span_symbol_eq_top hψr' y'
    (span_range_mapSequence _ (span_range_rangeMap g hg ψ ψ' hgψ) hlenψ hys)
  let xLift' := mapSequence g hlenφ xLift
  let yLift' := mapSequence g hlenψ yLift
  have hxLift' : ∀ i, φ' (xLift' i) = (x'.1 i : N') := fun i ↦
    (hgφ _).symm.trans (congrArg g (hxLift _))
  have hyLift' : ∀ j, ψ' (yLift' j) = (y'.1 j : N') := fun j ↦
    (hgψ _).symm.trans (congrArg g (hyLift _))
  obtain ⟨hl', hr', hleft', hright', -⟩ := AlgebraicGeometry.periodicDeterminant_symbol_eq
    φ' ψ' hφψ' hψφ' hN' x' y' hx' hy' xLift' yLift' hxLift' hyLift'
  have hlen : moduleLength R' N' = moduleLength R N := by rw [hl, hl', hlenφ, hlenψ]
  refine AlgebraicGeometry.eq_periodicDeterminant_of_symbol_eq φ' ψ' hφψ' hψφ' hN' x' y' hx' hy'
    xLift' yLift' hxLift' hyLift' hl' hr' hleft' hright' _ ?_
  have key := congrArg (determinantMap hm g hlen) hd
  rw [LinearMap.map_smulₛₗ, determinantMap_symbol, determinantMap_symbol] at key
  have e1 : mapAdmissibleSequence hm g hlen
      ⟨fun i ↦ Fin.append (fun j ↦ (x.1 j : N)) yLift (Fin.cast hl i), hleft⟩ =
      ⟨fun i ↦ Fin.append (fun j ↦ (x'.1 j : N')) yLift' (Fin.cast hl' i), hleft'⟩ :=
    Subtype.ext (funext fun i ↦
      map_append_cast g (fun j ↦ (x.1 j : N)) yLift hlenφ hlenψ hl hl' hlen i)
  have e2 : mapAdmissibleSequence hm g hlen
      ⟨fun i ↦ Fin.append (fun j ↦ (y.1 j : N)) xLift (Fin.cast hr i), hright⟩ =
      ⟨fun i ↦ Fin.append (fun j ↦ (y'.1 j : N')) xLift' (Fin.cast hr' i), hright'⟩ :=
    Subtype.ext (funext fun i ↦
      map_append_cast g (fun j ↦ (y.1 j : N)) xLift hlenψ hlenφ hr hr' hlen i)
  rw [e1, e2] at key
  rw [key]
  congr 1
  rw [hlenφ, hlenψ]
  simp

end Periodic

end Stacks.Chow

end
