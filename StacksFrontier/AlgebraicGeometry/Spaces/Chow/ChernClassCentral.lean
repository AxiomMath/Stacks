module

public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassBivariant
public import StacksFrontier.AlgebraicGeometry.Spaces.Chow.ChernClassCommutation

/-!
# The Chern classes of Stacks 0ERZ are central in the Chow cohomology

In Situation 0EDT let `X/B` be good and let `ℰ` be a finite locally free `𝒪_X`-module of rank
`r`. **Stacks 0ES1** asserts that `c_j(ℰ) ∈ A^j(X)` commutes with every element `c ∈ A^p(X)`, and
in particular that `c_i(ℰ) ∩ c_j(ℱ) ∩ α = c_j(ℱ) ∩ c_i(ℰ) ∩ α` for a second finite locally free
`ℱ` of rank `s` and every `α ∈ CH_k(X)`. (The statement in the source reads `c_j(ℒ)`; the proof
and the "in particular" make clear that `c_j(ℰ)` is meant.)

The Chern classes here are those of Stacks 0ERY and 0ERZ: on a good test space `g : X' ⟶ X` the
maps `c_j(ℰ) ∩ - : CH_k(X') ⟶ CH_{k-j}(X')` of `AlgebraicGeometry.Space.chernCap`, the unique
family with `c₀ = id` satisfying the projective bundle relation on `P' = P ×_X X'`, whose
bivariant class is `AlgebraicGeometry.Space.chernClass`. The Chow cohomology algebra `A^*(X)`
of Stacks 0ERK is `AlgebraicGeometry.Space.ChowCohomologyAlgebra`, the product being composition
of bivariant classes. The class `c_j(ℰ)`, as an element of the degree `j` part
`AlgebraicGeometry.Space.ChowCohomologyClass` of that algebra, is
`AlgebraicGeometry.Space.chernCohomologyClass`: it caps as `c_j(ℰ) ∩ -` on every test space,
which is the cap operation of `AlgebraicGeometry.Space.chernClass` read on `X ×_X X' ≅ X'`
(`AlgebraicGeometry.Space.chernClass_cap_eq_chernCohomologyClass_cap`).

The proof is that of the source. For `α ∈ CH_k(X')` the classes `c ∩ (c_j(ℰ) ∩ α)` satisfy the
relation of Stacks 0ERY for `c ∩ α`: `c` commutes with the flat pullback `π'^*` (axiom (2) of a
bivariant class, Stacks 0ERJ) and with the cap products with `c₁(𝒪_{P'}(1))` (Stacks 0ERR), so
it carries the relation for `α` to the relation for `c ∩ α`. By the uniqueness in Stacks 0ERY,
`c ∩ (c_j(ℰ) ∩ α) = c_j(ℰ) ∩ (c ∩ α)`.

## Main definitions

* `AlgebraicGeometry.Space.chernCohomologyClass`: `c_j(ℰ) ∈ A^j(X)` as an element of
  `AlgebraicGeometry.Space.ChowCohomologyClass`, capping as `AlgebraicGeometry.Space.chernCap`.

## Main results

* `AlgebraicGeometry.Space.ChowCohomologyClass.cap_chernCap`: `c ∩ (c_j(ℰ) ∩ α) = c_j(ℰ) ∩ (c ∩ α)`
  on every good test space.
* `AlgebraicGeometry.Space.ChowCohomologyClass.comp_chernCohomologyClass`: **Stacks 0ES1**,
  `c ∘ c_j(ℰ) = c_j(ℰ) ∘ c` for every `c ∈ A^p(X)`.
* `AlgebraicGeometry.Space.commute_of_chernCohomologyClass`: **Stacks 0ES1**, `c_j(ℰ)` is central
  in `A^*(X)`.
* `AlgebraicGeometry.Space.chernCap_apply_chernCap_comm`: **Stacks 0ES1, in particular**,
  `c_i(ℰ) ∩ c_j(ℱ) ∩ α = c_j(ℱ) ∩ c_i(ℰ) ∩ α`.

## References

* [Stacks Project, Tag 0ES1](https://stacks.math.columbia.edu/tag/0ES1)
* [Stacks Project, Tag 0ERY](https://stacks.math.columbia.edu/tag/0ERY)
* [Stacks Project, Tag 0ERZ](https://stacks.math.columbia.edu/tag/0ERZ)
* [Stacks Project, Tag 0ERR](https://stacks.math.columbia.edu/tag/0ERR)
* [Stacks Project, Tag 0ERK](https://stacks.math.columbia.edu/tag/0ERK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-! ### Operations commuting with the pullback and the caps preserve the relation -/

namespace ProjectiveBundleRelation

variable {A : ℤ → Type*} {P : ℤ → Type*} [∀ k, AddCommGroup (A k)] [∀ k, AddCommGroup (P k)]
  (e : ℤ) (pull : ∀ m n : ℤ, m + e = n → A m →+ P n)
  (cap : ∀ (s : ℕ) (n m : ℤ), n = m + s → P n →+ P m)
  (p : ℤ) (φA : ∀ m m' : ℤ, m' + p = m → A m →+ A m')
  (φP : ∀ n n' : ℤ, n' + p = n → P n →+ P n')

/-- **An operation of degree `-p` commuting with the pullback and the caps carries the left-hand
side of the relation of Stacks 0ERY to itself**: if `φ` commutes with `π^*` and with every
`c₁^s ∩ -`, then `φ(∑ (-1)^i c₁^i ∩ π^*(b_{r-i})) = ∑ (-1)^i c₁^i ∩ π^*(φ b_{r-i})`. -/
theorem relationSumAt_map
    (hpull : ∀ (m n m' n' : ℤ) (h : m + e = n) (h' : m' + e = n') (hm : m' + p = m)
      (hn : n' + p = n) (x : A m), φP n n' hn (pull m n h x) = pull m' n' h' (φA m m' hm x))
    (hcap : ∀ (s : ℕ) (n m n' m' : ℤ) (h : n = m + s) (h' : n' = m' + s) (hn : n' + p = n)
      (hm : m' + p = m) (x : P n), φP m m' hm (cap s n m h x) = cap s n' m' h' (φP n n' hn x))
    (r : ℕ) (k : ℤ) (b : ∀ j : Fin (r + 1), A (k - ((j : ℕ) : ℤ))) :
    φP (k - r + e) (k - p - r + e) (by ring) (relationSumAt e pull cap r k b) =
      relationSumAt e pull cap r (k - p) fun j => φA _ _ (by ring) (b j) := by
  simp only [relationSumAt, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [relationTerm, map_zsmul]
  rw [hcap (i : ℕ) (k - r + e + (i : ℕ)) (k - r + e) (k - p - r + e + (i : ℕ)) (k - p - r + e)
      rfl rfl (by ring) (by ring),
    hpull (k - ((Fin.rev i : ℕ) : ℤ)) (k - r + e + (i : ℕ)) (k - p - ((Fin.rev i : ℕ) : ℤ))
      (k - p - r + e + (i : ℕ)) (relationTerm_degree e r k i) (relationTerm_degree e r (k - p) i)
      (by ring) (by ring)]

/-- A family satisfying the relation of Stacks 0ERY is carried by an operation commuting with
the pullback and the caps to a family satisfying the relation. -/
theorem relationSumAt_map_eq_zero
    (hpull : ∀ (m n m' n' : ℤ) (h : m + e = n) (h' : m' + e = n') (hm : m' + p = m)
      (hn : n' + p = n) (x : A m), φP n n' hn (pull m n h x) = pull m' n' h' (φA m m' hm x))
    (hcap : ∀ (s : ℕ) (n m n' m' : ℤ) (h : n = m + s) (h' : n' = m' + s) (hn : n' + p = n)
      (hm : m' + p = m) (x : P n), φP m m' hm (cap s n m h x) = cap s n' m' h' (φP n n' hn x))
    (r : ℕ) (k : ℤ) (b : ∀ j : Fin (r + 1), A (k - ((j : ℕ) : ℤ)))
    (hb : relationSumAt e pull cap r k b = 0) :
    relationSumAt e pull cap r (k - p) (fun j => φA _ _ (by ring) (b j)) = 0 := by
  rw [← relationSumAt_map e pull cap p φA φP hpull hcap r k b, hb, map_zero]

end ProjectiveBundleRelation

/-! ### A class of `A^p(X)` against casts, caps with first Chern classes and flat pullback -/

namespace ChowCohomologyClass

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX} {p : ℤ} (c : ChowCohomologyClass D sX hX p)

/-- The cap operation of `c` commutes with the identification of Chow groups of equal degrees. -/
theorem cap_degreeCast {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) {a b a' b' : ℤ}
    (h : a = b) (h' : a' = b') (ha : a' + p = a) (hb : b' + p = b)
    (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY a) :
    c.cap g hY b b' hb
        (ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m)
          h x) =
      ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) h'
        (c.cap g hY a a' ha x) := by
  subst h h'
  rfl

/-- The cap operation of `c` into a degree `m`, written as the cap into an equal degree `m'`
followed by the identification `CH_{m'} = CH_m`. -/
theorem cap_eq_degreeCast_cap {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) {k m m' : ℤ}
    (hm : m + p = k) (hm' : m' + p = k) (h : m' = m)
    (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    c.cap g hY k m hm x =
      ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) h
        (c.cap g hY k m' hm' x) := by
  subst h
  rfl

/-- The cap operation of `c` commutes with the identification `CH_a = CH_b` of
`AlgebraicGeometry.Space.chowGroupCanonicalCast`. -/
theorem cap_chowGroupCanonicalCast {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    {a b a' b' : ℤ} (h : a = b) (h' : a' = b') (ha : a' + p = a) (hb : b' + p = b)
    (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY a) :
    c.cap g hY b b' hb (chowGroupCanonicalCast.{u + 1} D (g ≫ sX) hY h x) =
      chowGroupCanonicalCast.{u + 1} D (g ≫ sX) hY h' (c.cap g hY a a' ha x) := by
  subst h h'
  have hid : ∀ {m : ℤ} (y : chowGroupCanonical.{u + 1} D (g ≫ sX) hY m),
      chowGroupCanonicalCast.{u + 1} D (g ≫ sX) hY rfl y = y := by
    intro m y
    obtain ⟨ξ, rfl⟩ : ∃ ξ, chowClassCanonical.{u + 1} D (g ≫ sX) hY m ξ = y :=
      QuotientAddGroup.mk'_surjective _ y
    exact chowGroupCanonicalCast_chowClassCanonical D (g ≫ sX) hY rfl ξ
  rw [hid, hid]

end ChowCohomologyClass

section Powers

variable (D : BaseSpaceDimensionSituation.{u})
    {X : (BigFppfOver D.site D.base D.base_mem)ᵒᵖ ⥤ Type u} (sX : X ⟶ D.space)
    (hX : D.IsGood sX) (L : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (hL : IsInvertibleModule (⟨X, hX.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L)

/-- `c₁(ℒ)^0 ∩ -` is the identification `CH_{m+0} = CH_m`. -/
theorem firstChernCapPowChowMap_zero (m : ℤ)
    (x : chowGroupCanonical.{u + 1} D sX hX (m + ((0 : ℕ) : ℤ))) :
    firstChernCapPowChowMap D sX hX L hL 0 m x =
      chowGroupCanonicalCast.{u + 1} D sX hX (by simp) x := by
  obtain ⟨ξ, rfl⟩ : ∃ ξ, chowClassCanonical.{u + 1} D sX hX _ ξ = x :=
    QuotientAddGroup.mk'_surjective _ x
  rw [firstChernCapPowChowMap_chowClassCanonical, chowGroupCanonicalCast_chowClassCanonical]
  rfl

/-- `c₁(ℒ)^{s+1} ∩ - = c₁(ℒ) ∩ (c₁(ℒ)^s ∩ -)` on Chow groups. -/
theorem firstChernCapPowChowMap_succ (s : ℕ) (m : ℤ)
    (x : chowGroupCanonical.{u + 1} D sX hX (m + ((s + 1 : ℕ) : ℤ))) :
    firstChernCapPowChowMap D sX hX L hL (s + 1) m x =
      canonicalFirstChernCapCanonicalChowMap D sX hX m L hL
        (firstChernCapPowChowMap D sX hX L hL s (m + 1)
          (chowGroupCanonicalCast.{u + 1} D sX hX (by push_cast; ring) x)) := by
  obtain ⟨ξ, rfl⟩ : ∃ ξ, chowClassCanonical.{u + 1} D sX hX _ ξ = x :=
    QuotientAddGroup.mk'_surjective _ x
  rw [firstChernCapPowChowMap_chowClassCanonical, chowGroupCanonicalCast_chowClassCanonical,
    firstChernCapPowChowMap_chowClassCanonical,
    canonicalFirstChernCapCanonicalChowMap_chowClassCanonical]
  rfl

end Powers

namespace ChowCohomologyClass

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX} {p : ℤ} (c : ChowCohomologyClass D sX hX p)

/-- **Stacks 0ERR, iterated**: `c ∩ (c₁(ℒ)^s ∩ x) = c₁(ℒ)^s ∩ (c ∩ x)` for an invertible `ℒ` on a
good test space. -/
theorem cap_firstChernCapPowChowMap {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L) (s : ℕ) :
    ∀ (m m' : ℤ) (hm : m' + p = m) (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY (m + s)),
      c.cap g hY m m' hm (firstChernCapPowChowMap D (g ≫ sX) hY L hL s m x) =
        firstChernCapPowChowMap D (g ≫ sX) hY L hL s m'
          (c.cap g hY (m + s) (m' + s) (by omega) x) := by
  induction s with
  | zero =>
    intro m m' hm x
    rw [firstChernCapPowChowMap_zero, firstChernCapPowChowMap_zero,
      c.cap_chowGroupCanonicalCast g hY (a := m + ((0 : ℕ) : ℤ)) (b := m)
        (a' := m' + ((0 : ℕ) : ℤ)) (b' := m') (by simp) (by simp) (by omega) hm]
  | succ s ih =>
    intro m m' hm x
    rw [firstChernCapPowChowMap_succ, firstChernCapPowChowMap_succ,
      c.cap_canonicalFirstChernCapCanonicalChowMap g hY L hL m m' hm,
      ih (m + 1) (m' + 1) (by omega),
      c.cap_chowGroupCanonicalCast g hY (a := m + ((s + 1 : ℕ) : ℤ)) (b := m + 1 + s)
        (a' := m' + ((s + 1 : ℕ) : ℤ)) (b' := m' + 1 + s) (by push_cast; ring)
        (by push_cast; ring) (by omega) (by omega)]

/-- The cap operation of `c` on a test space `g : Y ⟶ X` whose structure morphism is given as any
morphism equal to `g ≫ sX`. -/
def capAt {Y : D.Ambient} (g : Y ⟶ X) {s : Y ⟶ D.space} (hs : g ≫ sX = s) (hY : D.IsGood s)
    (k l : ℤ) (hkl : l + p = k) :
    chowGroupCanonical.{u + 1} D s hY k →+ chowGroupCanonical.{u + 1} D s hY l := by
  subst hs
  exact c.cap g hY k l hkl

/-- **Axiom (2) of Stacks 0ERJ along `capAt`**: `c ∩ h^*x = h^*(c ∩ x)` for `h : Z ⟶ Y` flat. -/
theorem capAt_flatPullbackChowMapCanonical {Y Z : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (h : Z ⟶ Y) {s : Z ⟶ D.space} (hs : (h ≫ g) ≫ sX = s)
    (hZ : D.IsGood s) (hb : h ≫ g ≫ sX = s) (n : ℕ) (hh : IsFlat D.site D.base D.base_mem h)
    (hr : HasRelativeDimension n D.site D.base D.base_mem h) (k l k' l' : ℤ) (hkl : l + p = k)
    (hk : k + (n : ℤ) = k') (hl : l + (n : ℤ) = l') (hkl' : l' + p = k')
    (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    c.capAt (h ≫ g) hs hZ k' l' hkl'
        (flatPullbackChowMapCanonical.{u + 1} D s hZ (g ≫ sX) hY h hb n hh hr k k' hk x) =
      flatPullbackChowMapCanonical.{u + 1} D s hZ (g ≫ sX) hY h hb n hh hr l l' hl
        (c.cap g hY k l hkl x) := by
  subst hs
  exact c.flat_naturality g hY h hZ n hh hr k l hkl k' l' hk hl x

/-- **Stacks 0ERR, iterated, along `capAt`**: `c` commutes with the cap powers
`c₁(ℒ)^t ∩ -` of `AlgebraicGeometry.Space.bundleFormulaCap`. -/
theorem capAt_bundleFormulaCap {Y : D.Ambient} (g : Y ⟶ X) {s : Y ⟶ D.space}
    (hs : g ≫ sX = s) (hY : D.IsGood s) (L : Modules.{u, u} D.site D.base D.base_mem Y hY.1)
    (hL : IsInvertibleModule (⟨Y, hY.1⟩ : AlgebraicSpaces D.site D.base D.base_mem) L) (t : ℕ)
    (N m N' m' : ℤ) (h : N = m + t) (h' : N' = m' + t) (hN : N' + p = N) (hm : m' + p = m)
    (x : chowGroupCanonical.{u + 1} D s hY N) :
    c.capAt g hs hY m m' hm (bundleFormulaCap D s hY L hL t N m h x) =
      bundleFormulaCap D s hY L hL t N' m' h' (c.capAt g hs hY N N' hN x) := by
  subst hs
  change c.cap g hY m m' hm (firstChernCapPowChowMap D (g ≫ sX) hY L hL t m
      (chowGroupCanonicalCast.{u + 1} D (g ≫ sX) hY h x)) =
    firstChernCapPowChowMap D (g ≫ sX) hY L hL t m'
      (chowGroupCanonicalCast.{u + 1} D (g ≫ sX) hY h' (c.cap g hY N N' hN x))
  rw [c.cap_firstChernCapPowChowMap g hY L hL t m m' hm,
    c.cap_chowGroupCanonicalCast g hY h h' hN (by omega)]

end ChowCohomologyClass

/-! ### Classes of `A^p(X)` commute with the Chern classes -/

section Chern

variable {D : BaseSpaceDimensionSituation.{u}} {X : D.Ambient} {sX : X ⟶ D.space}
  {hX : D.IsGood sX} (E : Modules.{u, u} D.site D.base D.base_mem X hX.1) (r : ℕ)
  (hE : RingedSite.IsFiniteLocallyFreeOfRank
    (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) E r)

/-- **Uniqueness in Stacks 0ERY, pointwise**: a family `b_j ∈ CH_{k-j}(X')` with `b₀ = α` which
satisfies the relation on `P' = P ×_X X'` is `c_j(ℰ) ∩ α`. -/
theorem eq_chernCap_of_relationSumAt_eq_zero {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (k : ℤ) (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k)
    (b : ∀ j : Fin (r + 1), chowGroupCanonical.{u + 1} D (g ≫ sX) hY (k - ((j : ℕ) : ℤ)))
    (h0 : b 0 = ProjectiveBundleRelation.degreeCast
      (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) (by simp) α)
    (hb : ProjectiveBundleRelation.relationSumAt
      (A := fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m)
      (P := fun m => chowGroupCanonical.{u + 1} D
        (pullback.snd (chernProj D sX hX E r hE) g ≫ g ≫ sX)
        (isGood_chernTestBundle D sX hX E r hE g hY) m) ((r : ℤ) - 1)
      (chernTestPull D sX hX E r hE g hY)
      (bundleFormulaCap D _ (isGood_chernTestBundle D sX hX E r hE g hY)
        (chernTestTwist D sX hX E r hE g hY)
        (isInvertibleModule_chernTestTwist D sX hX E r hE g hY)) r k b = 0)
    (j : Fin (r + 1)) : b j = chernCap D sX hX E r hE g hY j k α := by
  cases r with
  | zero =>
    obtain rfl : j = 0 := Subsingleton.elim (α := Fin 1) _ _
    exact h0
  | succ n =>
    have := isQuasicoherentOnSite_of_isFiniteLocallyFreeOfRank hX.1 hE
    exact congrFun (eq_of_chernRelationSumAt_eq_zero D sX hX E n hE g hY k b _
      (h0.trans (chernCapFamily_zero D sX hX E n hE g hY k α).symm) hb
      (chernRelationSumAt_chernCapFamily D sX hX E n hE g hY k α)) j

/-- **Stacks 0ES1 on a test space.** A class `c ∈ A^p(X)` commutes with the Chern classes of
Stacks 0ERY: for every good test space `g : X' ⟶ X`, every `α ∈ CH_k(X')` and every `j`,
`c ∩ (c_j(ℰ) ∩ α) = c_j(ℰ) ∩ (c ∩ α)` in `CH_{k-p-j}(X')`. The proof is that of the source: the
classes `c ∩ (c_j(ℰ) ∩ α)` satisfy the relation of Stacks 0ERY for `c ∩ α`, since `c` commutes with
`π'^*` and with `c₁(𝒪_{P'}(1)) ∩ -`, and the uniqueness of Stacks 0ERY applies. -/
theorem ChowCohomologyClass.cap_chernCap {p : ℤ} (c : ChowCohomologyClass D sX hX p)
    {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) (j : Fin (r + 1)) :
    c.cap g hY (k - ((j : ℕ) : ℤ)) (k - p - ((j : ℕ) : ℤ)) (by ring)
        (chernCap D sX hX E r hE g hY j k α) =
      chernCap D sX hX E r hE g hY j (k - p) (c.cap g hY k (k - p) (by ring) α) := by
  refine eq_chernCap_of_relationSumAt_eq_zero E r hE g hY (k - p) _
    (fun j => c.cap g hY (k - ((j : ℕ) : ℤ)) (k - p - ((j : ℕ) : ℤ)) (by ring)
      (chernCap D sX hX E r hE g hY j k α)) ?_ ?_ j
  · change c.cap g hY _ _ _ (chernCap D sX hX E r hE g hY 0 k α) = _
    rw [chernCap_zero]
    exact c.cap_degreeCast g hY _ _ _ _ α
  · refine ProjectiveBundleRelation.relationSumAt_map_eq_zero _ _ _ p
      (fun m m' hm => c.cap g hY m m' hm)
      (fun n n' hn => c.capAt (pullback.snd (chernProj D sX hX E r hE) g ≫ g)
        (Category.assoc _ _ _) (isGood_chernTestBundle D sX hX E r hE g hY) n n' hn) ?_ ?_ r k
      (fun j => chernCap D sX hX E r hE g hY j k α)
      (chernRelationSum_chernCap D sX hX E r hE g hY k α)
    · intro m n m' n' h h' hm hn x
      cases r with
      | zero =>
        change c.capAt _ _ _ n n' hn ((0 : _ →+ _) x) = (0 : _ →+ _) (c.cap g hY m m' hm x)
        rw [AddMonoidHom.zero_apply, AddMonoidHom.zero_apply, map_zero]
      | succ n₀ =>
        exact c.capAt_flatPullbackChowMapCanonical g hY _ (Category.assoc _ _ _) _ rfl n₀ _ _
          m m' n n' hm (by push_cast at h; omega) (by push_cast at h'; omega) hn x
    · intro t N M N' M' h h' hN hM x
      exact c.capAt_bundleFormulaCap _ (Category.assoc _ _ _) _ _ _ t N M N' M' h h' hN hM x

/-- **Stacks 0ERZ, the class `c_j(ℰ) ∈ A^j(X)` in the Chow cohomology algebra.** The bivariant
class of degree `j` of Stacks 0ERY of a finite locally free `𝒪_X`-module `ℰ` of rank `r` on a good
`X/B`, as an element of the degree `j` part `AlgebraicGeometry.Space.ChowCohomologyClass` of
`A^*(X)` (Stacks 0ERK): on a good test space `g : X' ⟶ X` it caps as
`c_j(ℰ) ∩ - : CH_k(X') ⟶ CH_{k-j}(X')` (`AlgebraicGeometry.Space.chernCap`). This is the class
`AlgebraicGeometry.Space.chernClass` of Stacks 0ERZ, whose cap operation is the same map read on
`X ×_X X' ≅ X'` (`AlgebraicGeometry.Space.chernClass_cap_eq_chernCohomologyClass_cap`). -/
def chernCohomologyClass (j : Fin (r + 1)) : ChowCohomologyClass D sX hX ((j : ℕ) : ℤ) where
  cap g hY k l hkl :=
    (ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m)
      (by omega)).comp (chernCap D sX hX E r hE g hY j k)
  proper_naturality g hY h hY'' hh k l hkl α := by
    obtain rfl : l = k - ((j : ℕ) : ℤ) := by omega
    obtain ⟨β, hβ⟩ : ∃ β, chowClassCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY'' (k - ((j : ℕ) : ℤ)) β =
        chernCap D sX hX E r hE (h ≫ g) hY'' j k
          (chowClassCanonical.{u + 1} D ((h ≫ g) ≫ sX) hY'' k α) :=
      QuotientAddGroup.mk'_surjective _ _
    refine ⟨β, hβ.symm, ?_⟩
    change chernCap D sX hX E r hE g hY j k (chowClassCanonical.{u + 1} D (g ≫ sX) hY k
        (properCyclePushforward D ((h ≫ g) ≫ sX) hY'' (g ≫ sX) hY (Category.assoc h g sX).symm
          hh.2.1.2 k α)) = _
    rw [← chowGroupCanonicalProperPushforward_chowClassCanonical D _ hY'' _ hY
        (Category.assoc h g sX).symm hh k α,
      chernCap_properPushforward D sX hX E r hE j g hY h hY'' hh k, ← hβ,
      chowGroupCanonicalProperPushforward_chowClassCanonical]
  flat_naturality g hY h hY'' n hh hr k l hkl k' l' hk hl x := by
    subst hk hl
    obtain rfl : l = k - ((j : ℕ) : ℤ) := by omega
    change ProjectiveBundleRelation.degreeCast _ _
        (chernCap D sX hX E r hE (h ≫ g) hY'' j (k + n)
          (flatPullbackChowMapCanonical D ((h ≫ g) ≫ sX) hY'' (g ≫ sX) hY h
            (Category.assoc h g sX).symm n hh hr k (k + n) rfl x)) =
      flatPullbackChowMapCanonical D ((h ≫ g) ≫ sX) hY'' (g ≫ sX) hY h
        (Category.assoc h g sX).symm n hh hr _ _ rfl
        (ProjectiveBundleRelation.degreeCast _ rfl (chernCap D sX hX E r hE g hY j k x))
    rw [chernCap_flatPullback D sX hX E r hE j g hY h hY'' n hh hr k x,
      flatPullbackChowMapCanonical_degreeCast D _ hY'' _ hY h _ n hh hr rfl
        (chernDegree_sub_add k n _).symm (chernDegree_sub_add k n _) rfl]
  gysin_naturality g hY L σ hL k l hkl x := by
    obtain rfl : l = k - ((j : ℕ) : ℤ) := by omega
    exact chernCap_gysin D sX hX E r hE j g hY L σ hL k x

/-- **`c_j(ℰ)` is the class `AlgebraicGeometry.Space.chernClass` of Stacks 0ERZ**: the cap
operation of `chernClass` on a test space `g : X' ⟶ X`, which lands in `X ×_X X'`, is the cap
operation of `chernCohomologyClass` on `X'` followed by the flat pullback along the isomorphism
`X ×_X X' ≅ X'`. -/
theorem chernClass_cap_eq_chernCohomologyClass_cap (j : Fin (r + 1)) {Y : D.Ambient}
    (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX)) (hXg : D.IsGood (pullback.fst (𝟙 X) g ≫ sX)) (k : ℤ)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    (chernClass D sX hX E r hE j).cap g hY hXg k α =
      testSpacePullbackChowMap D sX hX g hY hXg _
        ((chernCohomologyClass (hX := hX) E r hE j).cap g hY k (k - ((j : ℕ) : ℤ)) (by ring)
          α) :=
  rfl

/-- The cap operation of `c_j(ℰ) ∈ A^j(X)` is `c_j(ℰ) ∩ -` followed by the identification of the
target degree. -/
theorem chernCohomologyClass_cap (j : Fin (r + 1)) {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) (k l : ℤ) (hkl : l + ((j : ℕ) : ℤ) = k)
    (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    (chernCohomologyClass (hX := hX) E r hE j).cap g hY k l hkl α =
      ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m)
        (by omega) (chernCap D sX hX E r hE g hY j k α) :=
  rfl

/-- `c_j(ℰ) ∩ -` commutes with the identification of Chow groups of equal degrees. -/
theorem chernCap_degreeCast (j : Fin (r + 1)) {Y : D.Ambient} (g : Y ⟶ X)
    (hY : D.IsGood (g ≫ sX)) {a b : ℤ} (h : a = b) (h' : a - ((j : ℕ) : ℤ) = b - ((j : ℕ) : ℤ))
    (x : chowGroupCanonical.{u + 1} D (g ≫ sX) hY a) :
    chernCap D sX hX E r hE g hY j b
        (ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m)
          h x) =
      ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m) h'
        (chernCap D sX hX E r hE g hY j a x) := by
  subst h
  rfl

/-- **Stacks 0ES1.** In Situation 0EDT let `X/B` be good and let `ℰ` be a finite locally free
`𝒪_X`-module of rank `r`. Then `c_j(ℰ) ∈ A^j(X)` commutes with every `c ∈ A^p(X)`:
`c ∘ c_j(ℰ) = c_j(ℰ) ∘ c` in `A^{p+j}(X) = A^{j+p}(X)`, the product of Stacks 0ERK being
composition of bivariant classes (`AlgebraicGeometry.Space.ChowCohomologyClass.comp`). Here
`c_j(ℰ)` is the Chern class of Stacks 0ERY and 0ERZ (`AlgebraicGeometry.Space.chernCohomologyClass`,
the class `AlgebraicGeometry.Space.chernClass` read in `A^j(X)`). (The source's `c_j(ℒ)` is a
typo for `c_j(ℰ)`.) -/
@[stacks 0ES1 "the main assertion: c_j(E) ∈ A^j(X), the Chern class of Lemma 0ERY / Definition \
0ERZ (chernCohomologyClass, the class chernClass read in A^j(X)), commutes with every \
c ∈ A^p(X): c ∘ c_j(E) = c_j(E) ∘ c, composition being the product of A^*(X) (0ERK). The \
source's c_j(L) is a typo for c_j(E)"]
theorem ChowCohomologyClass.comp_chernCohomologyClass {p : ℤ} (c : ChowCohomologyClass D sX hX p)
    (j : Fin (r + 1)) :
    (⟨p + ((j : ℕ) : ℤ), c.comp (chernCohomologyClass E r hE j)⟩ :
        GradedMonoid (ChowCohomologyClass D sX hX)) =
      ⟨((j : ℕ) : ℤ) + p, (chernCohomologyClass E r hE j).comp c⟩ := by
  refine ChowCohomologyClass.gradedMonoid_mk_eq (add_comm _ _) fun g hY k l hkl hkl' x => ?_
  rw [ChowCohomologyClass.comp_cap, ChowCohomologyClass.comp_cap, chernCohomologyClass_cap,
    chernCohomologyClass_cap,
    c.cap_degreeCast g hY (a := k - ((j : ℕ) : ℤ)) (b := l + p)
      (a' := k - p - ((j : ℕ) : ℤ)) (b' := l) (by omega) (by omega) (by ring) rfl,
    c.cap_chernCap E r hE g hY k x j,
    c.cap_eq_degreeCast_cap g hY (k := k) (m := l + ((j : ℕ) : ℤ)) (m' := k - p) (by omega)
      (by ring) (by omega) x,
    chernCap_degreeCast E r hE j g hY (by omega) (by omega),
    ProjectiveBundleRelation.degreeCast_degreeCast]

/-- **Stacks 0ES1**, in the Chow cohomology algebra: `c_j(ℰ)` commutes with every element of
`A^*(X) = ⊕_p A^p(X)` (`AlgebraicGeometry.Space.ChowCohomologyAlgebra`), so lies in its centre. -/
@[stacks 0ES1 "the main assertion in the algebra A^*(X) of 0ERK: c_j(E) (chernCohomologyClass, \
the class chernClass of 0ERZ read in A^j(X)) commutes with every element of A^*(X) = ⊕_p A^p(X), \
in particular with every c ∈ A^p(X)"]
theorem commute_of_chernCohomologyClass (j : Fin (r + 1)) (x : ChowCohomologyAlgebra D sX hX) :
    Commute (DirectSum.of (ChowCohomologyClass D sX hX) ((j : ℕ) : ℤ)
      (chernCohomologyClass E r hE j)) x := by
  induction x using DirectSum.induction_on with
  | zero => exact Commute.zero_right _
  | of p c =>
    change _ * _ = _ * _
    rw [DirectSum.of_mul_of, DirectSum.of_mul_of]
    exact DirectSum.of_eq_of_gradedMonoid_eq (c.comp_chernCohomologyClass E r hE j).symm
  | add x y hx hy => exact hx.add_right hy

/-- **Stacks 0ES1, in particular.** In Situation 0EDT let `X/B` be good and let `ℰ`, `ℱ` be finite
locally free `𝒪_X`-modules of ranks `r` and `s`. Then for every good `g : X' ⟶ X` (for instance
`X' = X`) and every `α ∈ CH_k(X')`,

  `c_i(ℰ) ∩ c_j(ℱ) ∩ α = c_j(ℱ) ∩ c_i(ℰ) ∩ α`  in `CH_{k-i-j}(X')`,

the Chern classes being those of Stacks 0ERY and 0ERZ (`AlgebraicGeometry.Space.chernCap`), and
`CH_{k-j-i} = CH_{k-i-j}` the identification of equal degrees. -/
@[stacks 0ES1 "in particular: c_i(E) ∩ c_j(F) ∩ α = c_j(F) ∩ c_i(E) ∩ α in CH_{k-i-j} for every \
α ∈ CH_k, E, F finite locally free of ranks r, s on X, the Chern classes being chernCap of Lemma \
0ERY; stated on every good X' → X, X' = X included"]
theorem chernCap_apply_chernCap_comm (F : Modules.{u, u} D.site D.base D.base_mem X hX.1)
    (s : ℕ) (hF : RingedSite.IsFiniteLocallyFreeOfRank
      (smallEtaleRingedSite D.site D.base D.base_mem X hX.1) F s)
    (i : Fin (r + 1)) (j : Fin (s + 1)) {Y : D.Ambient} (g : Y ⟶ X) (hY : D.IsGood (g ≫ sX))
    (k : ℤ) (α : chowGroupCanonical.{u + 1} D (g ≫ sX) hY k) :
    chernCap D sX hX E r hE g hY i (k - ((j : ℕ) : ℤ)) (chernCap D sX hX F s hF g hY j k α) =
      ProjectiveBundleRelation.degreeCast (fun m => chowGroupCanonical.{u + 1} D (g ≫ sX) hY m)
        (by ring)
        (chernCap D sX hX F s hF g hY j (k - ((i : ℕ) : ℤ)) (chernCap D sX hX E r hE g hY i k α)) :=
  ((chernCohomologyClass F s hF j).cap_chernCap E r hE g hY k α i).symm

end Chern

end AlgebraicGeometry.Space

end
