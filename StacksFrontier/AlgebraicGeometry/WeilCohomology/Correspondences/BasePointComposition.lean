module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackClass
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.FlatPullbackCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Restriction
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.Class
public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassDivisorClass
public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.BasePoint
public import StacksFrontier.AlgebraicGeometry.WeilCohomology.Correspondences.Composition

/-!
# Correspondences with the base point, and composition

Let `k` be a field and let `X`, `X'`, `Y` be schemes locally of finite type over `k` of
constant dimensions. Stacks 0FG0 (2) and (3) identify the correspondences having `Spec k` as a
factor with rational Chow groups,

  `CH_{-r}(X) ⊗ ℚ = Corrʳ(X, Spec k)`  and  `CH^r(X) ⊗ ℚ = Corrʳ(Spec k, X)`,

(`Stacks.WeilCohomology.correspondenceToPointEquiv`,
`Stacks.WeilCohomology.correspondenceFromPointEquiv`) and assert that under these
identifications the action of correspondences on Chow groups becomes composition:

* for `c ∈ Corrˢ(X', X)` and `β ∈ CH_{-r}(X) ⊗ ℚ`, the pullback `c^*(β)` corresponds to the
  composition `β ∘ c ∈ Corr^{s+r}(X', Spec k)`;
* for `c ∈ Corrˢ(X, Y)` and `α ∈ CH^i(X) ⊗ ℚ`, the pushforward `c_*(α)` corresponds to the
  composition `c ∘ α ∈ Corr^{i+s}(Spec k, Y)`.

The proof is bookkeeping on the triple products. For `X' × X × Spec k` the projection `pr₁₂` onto
`X' × X` is an isomorphism, flat pullback along it is pushforward along its inverse, the
pullback of `β` along `pr₂₃` is transported from the pullback along `pr₂ : X' × X ⟶ X` by the
isomorphism case of Stacks 02RG, the intersection product is moved across `pr₁₂`, and the two
pushforwards to `X'` agree by functoriality of proper pushforward (Stacks 02R5). The case
`Spec k × X × Y` is the same with `pr₂₃` in the role of the isomorphism.

## Main definitions

* `Stacks.WeilCohomology.DiagonalClassFamily.IsoInvariant`: the intersection products formed
  with a family of diagonal classes are transported by isomorphisms over `k`.
* `Stacks.WeilCohomology.DiagonalClassFamily.IsSymmetric`: the intersection products formed with
  a family of diagonal classes are commutative.

## Main results

* `Stacks.Chow.flatPullbackChow_heq_chowPushforwardOfIso_inv`: flat pullback along an
  isomorphism is pushforward along its inverse.
* `Stacks.WeilCohomology.correspondenceToPointEquiv_correspondencePullback`: the second half of
  Stacks 0FG0 (2), `c^*(β) = β ∘ c`, for an iso-invariant family of diagonal classes.
* `Stacks.WeilCohomology.correspondenceFromPointEquiv_correspondencePushforward`: the second half
  of Stacks 0FG0 (3), `c_*(α) = c ∘ α`, for an iso-invariant and symmetric family of diagonal
  classes.

## Implementation notes

The composition `c' ∘ c` is `pr₁₃,*(pr₁₂^* c · pr₂₃^* c')` and the actions are
`c^*(β) = pr₁,*(c · pr₂^* β)` and `c_*(α) = pr₂,*(c · pr₁^* α)`. In part (2) the class `c` is the
left factor on both sides; in part (3) the composition `c ∘ α` puts the class coming from `α`
on the left while `c_*(α)` puts `c` on the left, so the comparison uses that the intersection
product is commutative, which the source records in Section 0FC0 ("this product is clearly
symmetric"). Both properties of the family of diagonal classes hold for the canonical family
of Stacks 0FBR and are recorded as hypotheses on the family, in the way
`Stacks.WeilCohomology.DiagonalClassFamily.CompositionAssoc` records associativity.

The degree `-r - s` of `c^*(β)` and the degree `-(s + r)` of the identification of
`Corr^{s+r}(X', Spec k)` are the same integer written two ways, and are compared through the
base change to `ℚ` of `Stacks.Chow.chowGroupDegreeEquiv`.

## References

* [Stacks Project, Tag 0FG0](https://stacks.math.columbia.edu/tag/0FG0)
* [Stacks Project, Section 0FFZ](https://stacks.math.columbia.edu/tag/0FFZ)
* [Stacks Project, Section 0FC0](https://stacks.math.columbia.edu/tag/0FC0)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

section Transport

variable (C : ChowSituation.{u}) {A B : Scheme.{u}} (sA : A ⟶ C.S) [LocallyOfFiniteType sA]
    [Smooth sA] [IsSeparated sA]
  (sB : B ⟶ C.S) [LocallyOfFiniteType sB] [Smooth sB] [IsSeparated sB]

omit [Smooth sA] [IsSeparated sA] [Smooth sB] [IsSeparated sB] in
/-- **Flat pullback along an isomorphism is pushforward along its inverse.** For an isomorphism
`f : A ⟶ B` over the base, flat of relative dimension `0`, the flat pullback
`f^* : A_k(B) ⟶ A_{k+0}(A)` is the pushforward along `f⁻¹`, up to the transport of degrees. This
is the isomorphism case of Stacks 02RG, applied to the square with horizontal legs `𝟙 B` and
`f⁻¹`. -/
theorem flatPullbackChow_heq_chowPushforwardOfIso_inv (f : A ⟶ B) [IsIso f]
    [LocallyOfFiniteType f] [Flat f] (hf : f ≫ sB = sA)
    (hr : AlgebraicGeometry.RelativeDimension f 0) (k : ℤ)
    (hfac : FlatPullbackFactorsThroughRationalEquivalence C sA sB f hf 0 hr k)
    (x : chowGroup C sB k) :
    flatPullbackChow C sA sB f hf 0 hr k hfac x ≍
      chowPushforwardOfIso C sB sA (inv f) (by rw [IsIso.inv_comp_eq, hf]) k x := by
  have h := flatPullbackChow_chowPushforwardOfIso C sB sB sB sA (𝟙 B) (Category.id_comp sB)
    (inv f) (by rw [IsIso.inv_comp_eq, hf]) (𝟙 B) (Category.id_comp sB) f hf
    (by simp) 0 (relativeDimension_identity B) hr k
    (flatPullbackFactorsThroughRationalEquivalence_id C sB k) hfac x
  rw [chowPushforwardOfIso_id, flatPullbackChow_id] at h
  rw [h]
  exact chowPushforwardOfIso_heq_congr C sB sA (inv f) _ (by simp) _ _ (cast_heq _ x)

end Transport

section SelfIntersection

variable (C : ChowSituation.{u}) [Subsingleton C.S] [IsIntegral C.S] [JacobsonSpace C.S]
  (hδ : ∀ s : C.S, IsClosed ({s} : Set C.S) → C.dimensionFunction s = 0) (G : GysinSystem C)
  {W : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW] [Smooth sW] [IsSeparated sW]

omit [Smooth sW] in
/-- The self-intersection product respects heterogeneous equality in the degree of the diagonal
class, the class itself, the two degrees and the two arguments. -/
theorem selfIntersectionProduct_heq {D D' : ℤ} (hD : D = D')
    {Dc : BivariantClass C G sW (selfProductStructure C sW) (pullback.diagonal sW)
      (diagonal_comp_selfProductStructure C sW) D}
    {Dc' : BivariantClass C G sW (selfProductStructure C sW) (pullback.diagonal sW)
      (diagonal_comp_selfProductStructure C sW) D'} (hDc : Dc ≍ Dc')
    {n n' m m' : ℤ} (hn : n = n') (hm : m = m') {x : chowGroup C sW n}
    {x' : chowGroup C sW n'} {y : chowGroup C sW m} {y' : chowGroup C sW m'} (hx : x ≍ x')
    (hy : y ≍ y') :
    selfIntersectionProduct C hδ G sW D Dc n m x y ≍
      selfIntersectionProduct C hδ G sW D' Dc' n' m' x' y' := by
  subst hD hn hm
  cases hDc
  cases hx
  cases hy
  rfl

end SelfIntersection

end Stacks.Chow

namespace Stacks.WeilCohomology

open Stacks.Chow

/-! ### Products one of whose factors is the base -/

section Products

variable {S X Y : Scheme.{u}} (sX : X ⟶ S) (sY : Y ⟶ S)

/-- When the first factor is the base, `pr₂₃ : S × X × Y ⟶ X × Y` is an isomorphism: it is the
base change of the isomorphism `S ×_S X ⟶ X`. -/
instance isIso_pr₂₃_baseLeft : IsIso (pr₂₃ (𝟙 S) sX sY) :=
  (isPullback_pr₁₂_pr₂₃ (𝟙 S) sX sY).isIso_snd_of_isIso

/-- When the last factor is the base, the second projection `X × Y ⟶ Y` is `pr₂₃` read through
the isomorphisms `pr₁₂ : X × Y × S ≅ X × Y` and `Y × S ≅ Y`. -/
theorem pullback_snd_inv_fst_eq_inv_pr₁₂_pr₂₃ :
    pullback.snd sX sY ≫ inv (pullback.fst sY (𝟙 S)) =
      inv (pr₁₂ sX sY (𝟙 S)) ≫ pr₂₃ sX sY (𝟙 S) := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq, pr₂₃_fst]

/-- When the last factor is the base, `pr₁₃ : X × Y × S ⟶ X × S` is the first projection
`X × Y ⟶ X` read through the isomorphisms `pr₁₂ : X × Y × S ≅ X × Y` and `X × S ≅ X`. -/
theorem inv_pr₁₂_pr₁₃_eq_fst_inv_fst :
    inv (pr₁₂ sX sY (𝟙 S)) ≫ pr₁₃ sX sY (𝟙 S) =
      pullback.fst sX sY ≫ inv (pullback.fst sX (𝟙 S)) := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, pr₁₃_fst]

/-- When the first factor is the base, the first projection `X × Y ⟶ X` is `pr₁₂` read through
the isomorphisms `pr₂₃ : S × X × Y ≅ X × Y` and `S × X ≅ X`. -/
theorem pullback_fst_inv_snd_eq_inv_pr₂₃_pr₁₂ :
    pullback.fst sX sY ≫ inv (pullback.snd (𝟙 S) sX) =
      inv (pr₂₃ (𝟙 S) sX sY) ≫ pr₁₂ (𝟙 S) sX sY := by
  rw [IsIso.eq_inv_comp, ← Category.assoc, IsIso.comp_inv_eq, pr₂₃_fst]

/-- When the first factor is the base, `pr₁₃ : S × X × Y ⟶ S × Y` is the second projection
`X × Y ⟶ Y` read through the isomorphisms `pr₂₃ : S × X × Y ≅ X × Y` and `S × Y ≅ Y`. -/
theorem inv_pr₂₃_pr₁₃_eq_snd_inv_snd :
    inv (pr₂₃ (𝟙 S) sX sY) ≫ pr₁₃ (𝟙 S) sX sY =
      pullback.snd sX sY ≫ inv (pullback.snd (𝟙 S) sY) := by
  rw [IsIso.inv_comp_eq, ← Category.assoc, IsIso.eq_comp_inv, pr₁₃_snd, pr₂₃_snd]

end Products

/-! ### Diagonal classes whose products are natural -/

/-- A family of diagonal classes is **invariant under isomorphisms** if the intersection products
it defines are transported by isomorphisms over `k`: for an isomorphism `φ : W' ⟶ W` over `k`
of schemes of dimension `n`, the product on `W'` of `a` and `b` is the pushforward along `φ⁻¹`
of the product on `W` of `φ_* a` and `φ_* b`. -/
def DiagonalClassFamily.IsoInvariant {k : Type u} [Field k] (Δ : DiagonalClassFamily k) :
    Prop :=
  ∀ {W W' : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW]
    [Smooth sW] (sW' : W' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW']
    [Smooth sW']
    (φ : W' ⟶ W) [IsIso φ]
    (hφ : φ ≫ sW = sW') (n : ℕ) (hn : RelativeDimension sW n)
    (hn' : RelativeDimension sW' n) (a b : ℤ) (x : chowGroup (fieldChowSituation k) sW' a)
    (y : chowGroup (fieldChowSituation k) sW' b),
    selfIntersectionProduct (fieldChowSituation k)
        (fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW' n (Δ sW' n hn') a b x y =
      chowPushforwardOfIso (fieldChowSituation k) sW sW' (inv φ)
        (by rw [IsIso.inv_comp_eq, hφ]) (a + b - n)
        (selfIntersectionProduct (fieldChowSituation k)
            (fieldChowSituation_dimensionFunction_of_isClosed k)
          (fieldGysinSystem k) sW n (Δ sW n hn) a b
          (chowPushforwardOfIso (fieldChowSituation k) sW' sW φ hφ a x)
          (chowPushforwardOfIso (fieldChowSituation k) sW' sW φ hφ b y))

/-- A family of diagonal classes is **symmetric** if the intersection products it defines are
commutative. -/
def DiagonalClassFamily.IsSymmetric {k : Type u} [Field k] (Δ : DiagonalClassFamily k) :
    Prop :=
  ∀ {W : Scheme.{u}} (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW]
    (n : ℕ) (hn : RelativeDimension sW n) (a b : ℤ) (x : chowGroup (fieldChowSituation k) sW a)
    (y : chowGroup (fieldChowSituation k) sW b),
    selfIntersectionProduct (fieldChowSituation k)
        (fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW n (Δ sW n hn) a b x y =
      chowGroupDegreeEquiv (fieldChowSituation k) sW (by ring)
        (selfIntersectionProduct (fieldChowSituation k)
            (fieldChowSituation_dimensionFunction_of_isClosed k)
          (fieldGysinSystem k) sW n (Δ sW n hn) b a y x)

variable {k : Type u} [Field k] {Δ : DiagonalClassFamily k}

/-- The product of an iso-invariant family on `W'`, transported to `W` along an isomorphism,
read in heterogeneous form, allowing the dimension of `W` to be written differently. -/
theorem DiagonalClassFamily.IsoInvariant.heq (hΔ : Δ.IsoInvariant) {W W' : Scheme.{u}}
    (sW : W ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW] [Smooth sW]
    (sW' : W' ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sW'] [Smooth sW']
    (φ : W' ⟶ W) [IsIso φ]
    (hφ : φ ≫ sW = sW') {n n' : ℕ} (hnn : n = n') (hn : RelativeDimension sW n)
    (hn' : RelativeDimension sW' n') (a b : ℤ) (x : chowGroup (fieldChowSituation k) sW a)
    (y : chowGroup (fieldChowSituation k) sW b) :
    selfIntersectionProduct (fieldChowSituation k)
        (fieldChowSituation_dimensionFunction_of_isClosed k)
        (fieldGysinSystem k) sW' n' (Δ sW' n' hn') a b
        (chowPushforwardOfIso (fieldChowSituation k) sW sW' (inv φ)
          (by rw [IsIso.inv_comp_eq, hφ]) a x)
        (chowPushforwardOfIso (fieldChowSituation k) sW sW' (inv φ)
          (by rw [IsIso.inv_comp_eq, hφ]) b y) ≍
      chowPushforwardOfIso (fieldChowSituation k) sW sW' (inv φ)
        (by rw [IsIso.inv_comp_eq, hφ]) (a + b - n)
        (selfIntersectionProduct (fieldChowSituation k)
            (fieldChowSituation_dimensionFunction_of_isClosed k)
          (fieldGysinSystem k) sW n (Δ sW n hn) a b x y) := by
  subst hnn
  have hinv : ∀ (j : ℤ) (z : chowGroup (fieldChowSituation k) sW j),
      chowPushforwardOfIso (fieldChowSituation k) sW' sW φ hφ j
        (chowPushforwardOfIso (fieldChowSituation k) sW sW' (inv φ)
          (by rw [IsIso.inv_comp_eq, hφ]) j z) = z :=
    fun j z ↦ (chowGroupEquivOfIso (fieldChowSituation k) sW' sW φ hφ j).apply_symm_apply z
  rw [hΔ sW sW' φ hφ n hn hn' a b, hinv, hinv]

section ToPoint

variable {X' X : Scheme.{u}} (sX' : X' ⟶ (fieldChowSituation k).S)
  (sX : X ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX'] [Smooth sX'] [IsSeparated sX']
  [LocallyOfFiniteType sX] [Smooth sX] [IsSeparated sX]

/-- The integral form of `Stacks.WeilCohomology.correspondenceToPointEquiv_correspondencePullback`:
for `c ∈ A_{b-s}(X' × X)` and `β ∈ CH_{-r}(X)`, the composition of `c` with the class of `β` in
`Corrʳ(X, Spec k)` is the class in `Corr^{s+r}(X', Spec k)` of `c^*(β) = pr₁,*(c · pr₂^* β)`. -/
theorem compositionInt_toPoint (hΔ : Δ.IsoInvariant) [IsProper sX] {a b : ℕ}
    (hX' : RelativeDimension sX' a) (hX : RelativeDimension sX b) (s r : ℤ)
    (c : chowGroup (fieldChowSituation k) (prodBase sX' sX) ((b : ℤ) - s))
    (β : chowGroup (fieldChowSituation k) sX (-r)) :
    compositionInt k sX' sX (𝟙 _) Δ hX' hX (relativeDimension_identity _) s r c
        (chowGroupDegreeEquiv _ _ (show (-r : ℤ) = 0 - r by omega)
          (chowGroupEquivPullbackUnitRight _ sX (-r) β)) =
      chowGroupDegreeEquiv _ _ (show (-(s + r) : ℤ) = 0 - (s + r) by omega)
        (chowGroupEquivPullbackUnitRight _ sX' (-(s + r))
          (chowGroupDegreeEquiv _ sX' (show -r - s = -(s + r) by ring)
            (properChowPushforward _ (prodBase sX' sX) sX' (pullback.fst sX' sX) rfl _
              (properPushforwardDescends _ _ _ _ _ _)
              (pullbackCycle k sX' sX Δ hX' hX s (-r) c β)))) := by
  apply eq_of_heq
  simp only [compositionInt, compositionCycle, pullbackCycle, LinearMap.compr₂_apply,
    LinearMap.compl₁₂_apply, LinearMap.compl₂_apply, AddMonoidHom.coe_toIntLinearMap,
    LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv]
  have hB := flatPullbackChow_heq_chowPushforwardOfIso_inv (fieldChowSituation k)
    (tripleBase sX' sX (𝟙 _)) (prodBase sX' sX) (pr₁₂ sX' sX (𝟙 _)) (pr₁₂_comp_prodBase _ _ _)
    (relativeDimension_pr₁₂ k sX' sX (𝟙 _) (relativeDimension_identity _)) ((b : ℤ) - s)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) c
  have hA := (flatPullbackChow_heq_of_degree (fieldChowSituation k) (tripleBase sX' sX (𝟙 _))
    (prodBase sX (𝟙 _)) (pr₂₃ sX' sX (𝟙 _)) (pr₂₃_comp_prodBase _ _ _) a
    (relativeDimension_pr₂₃ k sX' sX (𝟙 _) hX') (k := ((0 : ℕ) : ℤ) - r) (l := -r) (by simp)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (chowGroupDegreeEquiv_heq _ _ (show (-r : ℤ) = ((0 : ℕ) : ℤ) - r by simp)
      (chowGroupEquivPullbackUnitRight _ sX (-r) β))).trans
    (heq_of_eq (flatPullbackChow_chowPushforwardOfIso (fieldChowSituation k) sX (prodBase sX' sX)
      (prodBase sX (𝟙 _)) (tripleBase sX' sX (𝟙 _)) (inv (pullback.fst sX (𝟙 _)))
      (by rw [IsIso.inv_comp_eq]) (inv (pr₁₂ sX' sX (𝟙 _))) (by rw [IsIso.inv_comp_eq])
      (pullback.snd sX' sX) pullback.condition.symm (pr₂₃ sX' sX (𝟙 _))
      (pr₂₃_comp_prodBase _ _ _) (pullback_snd_inv_fst_eq_inv_pr₁₂_pr₂₃ sX' sX) a
      (relativeDimension_snd k sX' sX hX') (relativeDimension_pr₂₃ k sX' sX (𝟙 _) hX') (-r)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) β))
  have hC := selfIntersectionProduct_heq (fieldChowSituation k)
      (fieldChowSituation_dimensionFunction_of_isClosed k)
    (fieldGysinSystem k) (tripleBase sX' sX (𝟙 _)) rfl
    (HEq.rfl (a := Δ _ _ (relativeDimension_tripleBase k sX' sX (𝟙 _) hX' hX
      (relativeDimension_identity _))))
    (show (b : ℤ) - s + ((0 : ℕ) : ℤ) = b - s by simp)
    (show ((0 : ℕ) : ℤ) - r + a = -r + a by simp) hB hA
  have hD := hΔ.heq (prodBase sX' sX) (tripleBase sX' sX (𝟙 _)) (pr₁₂ sX' sX (𝟙 _))
    (pr₁₂_comp_prodBase _ _ _) (Nat.zero_add (b + a)).symm
    (relativeDimension_prodBase k sX' sX hX' hX)
    (relativeDimension_tripleBase k sX' sX (𝟙 _) hX' hX (relativeDimension_identity _))
    ((b : ℤ) - s) (-r + a) c
    (flatPullbackChow (fieldChowSituation k) (prodBase sX' sX) sX (pullback.snd sX' sX)
      pullback.condition.symm a (relativeDimension_snd k sX' sX hX') (-r)
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) β)
  have hF := (properChowPushforward_comp_apply (fieldChowSituation k) (prodBase sX' sX)
    (tripleBase sX' sX (𝟙 _)) (prodBase sX' (𝟙 _)) (inv (pr₁₂ sX' sX (𝟙 _)))
    (pr₁₃ sX' sX (𝟙 _)) (pullback.fst sX' sX ≫ inv (pullback.fst sX' (𝟙 _)))
    (inv_pr₁₂_pr₁₃_eq_fst_inv_fst sX' sX) (by rw [IsIso.inv_comp_eq]) (pr₁₃_comp_prodBase _ _ _)
    (by simp)
    ((b : ℤ) - s + (-r + a) - ((b + a : ℕ) : ℤ))
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso _ _ _ _ _ _)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
    (selfIntersectionProduct (fieldChowSituation k)
        (fieldChowSituation_dimensionFunction_of_isClosed k)
      (fieldGysinSystem k) (prodBase sX' sX) _ (Δ _ _ (relativeDimension_prodBase k sX' sX hX' hX))
      ((b : ℤ) - s) (-r + a) c
      (flatPullbackChow (fieldChowSituation k) (prodBase sX' sX) sX (pullback.snd sX' sX)
        pullback.condition.symm a (relativeDimension_snd k sX' sX hX') (-r)
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) β))).symm.trans
    (properChowPushforward_comp_apply (fieldChowSituation k) (prodBase sX' sX) sX'
      (prodBase sX' (𝟙 _)) (pullback.fst sX' sX) (inv (pullback.fst sX' (𝟙 _)))
      (pullback.fst sX' sX ≫ inv (pullback.fst sX' (𝟙 _))) rfl rfl (by rw [IsIso.inv_comp_eq])
      (by simp) _ (properPushforwardDescends _ _ _ _ _ _)
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso _ _ _ _ _ _)
      (properPushforwardDescends _ _ _ _ _ _) _)
  refine HEq.trans ?_ ((heq_of_eq hF).trans (HEq.symm ?_))
  · exact properChowPushforward_heq_congr (fieldChowSituation k) (tripleBase sX' sX (𝟙 _))
      (prodBase sX' (𝟙 _)) (pr₁₃ sX' sX (𝟙 _)) (pr₁₃_comp_prodBase _ _ _)
      (show ((0 : ℕ) : ℤ) - (s + r) = (b : ℤ) - s + (-r + a) - ((b + a : ℕ) : ℤ) by push_cast; ring)
      (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
      _ _ ((chowGroupDegreeEquiv_heq _ _ _ _).trans (hC.trans hD))
  · exact (chowGroupDegreeEquiv_heq _ _ _ _).trans
      (chowPushforwardOfIso_heq_congr (fieldChowSituation k) sX' (prodBase sX' (𝟙 _))
        (inv (pullback.fst sX' (𝟙 _))) (by rw [IsIso.inv_comp_eq])
        (show -(s + r) = (b : ℤ) - s + (-r + a) - ((b + a : ℕ) : ℤ) by push_cast; ring) _ _
        ((chowGroupDegreeEquiv_heq _ _ _ _).trans
          (properChowPushforward_heq_congr (fieldChowSituation k) (prodBase sX' sX) sX'
            (pullback.fst sX' sX) rfl
            (show -r - s = (b : ℤ) - s + (-r + a) - ((b + a : ℕ) : ℤ) by push_cast; ring)
            (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
            _ _ (chowGroupDegreeEquiv_heq _ _ _ _))))

/-- **Stacks 0FG0 (2), pullback by correspondences corresponds to composition.** For an
iso-invariant family of diagonal classes, `c ∈ Corrˢ(X', X)` and `β ∈ CH_{-r}(X) ⊗ ℚ`, the
identification `CH_{-(s+r)}(X') ⊗ ℚ = Corr^{s+r}(X', Spec k)` carries `c^*(β)` to `β ∘ c`. -/
theorem correspondenceToPointEquiv_correspondencePullback (hΔ : Δ.IsoInvariant) [IsProper sX]
    {a b : ℕ} (hX' : RelativeDimension sX' a) (hX : RelativeDimension sX b) (s r : ℤ)
    (c : Correspondence (fieldChowSituation k) sX' sX b s)
    (β : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX (-r))) :
    correspondenceToPointEquiv _ sX' (s + r)
        ((chowGroupDegreeEquiv _ sX' (show -r - s = -(s + r) by ring)).toIntLinearEquiv.baseChange
            ℤ ℚ _ _ (correspondencePullback k sX' sX Δ hX' hX s (-r) c β)) =
      composition k sX' sX (𝟙 _) Δ hX' hX (relativeDimension_identity _) s r c
        (correspondenceToPointEquiv _ sX r β) := by
  induction c using TensorProduct.inductionOn with
  | tmul q c =>
    induction β using TensorProduct.inductionOn with
    | tmul q' β =>
      simp only [correspondencePullback, rationalBilin_tmul, LinearEquiv.baseChange_tmul,
        LinearMap.compr₂_apply, AddMonoidHom.coe_toIntLinearMap]
      rw [correspondenceToPointEquiv_tmul, correspondenceToPointEquiv_tmul, composition_tmul,
        compositionInt_toPoint sX' sX hΔ hX' hX s r c β]
      rfl
    | add x y hx hy => simp only [map_add, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end ToPoint

section FromPoint

variable {X Y : Scheme.{u}} (sX : X ⟶ (fieldChowSituation k).S)
  (sY : Y ⟶ (fieldChowSituation k).S) [LocallyOfFiniteType sX] [Smooth sX] [IsSeparated sX]
  [LocallyOfFiniteType sY] [Smooth sY] [IsSeparated sY]

/-- The integral form of
`Stacks.WeilCohomology.correspondenceFromPointEquiv_correspondencePushforward`: for
`α ∈ A_{a-i}(X)` and `c ∈ A_{b-s}(X × Y)`, the composition of the class of `α` in
`Corrⁱ(Spec k, X)` with `c` is the class in `Corr^{i+s}(Spec k, Y)` of
`c_*(α) = pr₂,*(c · pr₁^* α)`. -/
theorem compositionInt_fromPoint (hΔ : Δ.IsoInvariant) (hΔs : Δ.IsSymmetric) [IsProper sX]
    {a b : ℕ} (hX : RelativeDimension sX a) (hY : RelativeDimension sY b) (i s : ℤ)
    (α : chowGroup (fieldChowSituation k) sX ((a : ℤ) - i))
    (c : chowGroup (fieldChowSituation k) (prodBase sX sY) ((b : ℤ) - s)) :
    compositionInt k (𝟙 _) sX sY Δ (relativeDimension_identity _) hX hY i s
        (chowGroupEquivPullbackUnitLeft _ sX ((a : ℤ) - i) α) c =
      chowGroupEquivPullbackUnitLeft _ sY ((b : ℤ) - (i + s))
        (properChowPushforward _ (prodBase sX sY) sY (pullback.snd sX sY)
          pullback.condition.symm _ (properPushforwardDescends _ _ _ _ _ _)
          (pushforwardCycle k sX sY Δ hX hY s i c α)) := by
  apply eq_of_heq
  simp only [compositionInt, compositionCycle, pushforwardCycle, LinearMap.compr₂_apply,
    LinearMap.compl₁₂_apply, LinearMap.compl₂_apply, AddMonoidHom.coe_toIntLinearMap,
    LinearEquiv.coe_coe, AddEquiv.coe_toIntLinearEquiv]
  have hB := flatPullbackChow_heq_chowPushforwardOfIso_inv (fieldChowSituation k)
    (tripleBase (𝟙 _) sX sY) (prodBase sX sY) (pr₂₃ (𝟙 _) sX sY) (pr₂₃_comp_prodBase _ _ _)
    (relativeDimension_pr₂₃ k (𝟙 _) sX sY (relativeDimension_identity _)) ((b : ℤ) - s)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) c
  have hA := flatPullbackChow_chowPushforwardOfIso (fieldChowSituation k) sX (prodBase sX sY)
    (prodBase (𝟙 _) sX) (tripleBase (𝟙 _) sX sY) (inv (pullback.snd (𝟙 _) sX))
    (by rw [IsIso.inv_comp_eq]; exact pullback.condition) (inv (pr₂₃ (𝟙 _) sX sY))
    (by rw [IsIso.inv_comp_eq, pr₂₃_comp_prodBase]) (pullback.fst sX sY) rfl
    (pr₁₂ (𝟙 _) sX sY) (pr₁₂_comp_prodBase _ _ _) (pullback_fst_inv_snd_eq_inv_pr₂₃_pr₁₂ sX sY) b
    (relativeDimension_fst k sX sY hY) (relativeDimension_pr₁₂ k (𝟙 _) sX sY hY) ((a : ℤ) - i)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _)
    (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α
  have hC := selfIntersectionProduct_heq (fieldChowSituation k)
      (fieldChowSituation_dimensionFunction_of_isClosed k)
    (fieldGysinSystem k) (tripleBase (𝟙 _) sX sY) rfl
    (HEq.rfl (a := Δ _ _ (relativeDimension_tripleBase k (𝟙 _) sX sY (relativeDimension_identity _)
      hX hY)))
    rfl (show (b : ℤ) - s + ((0 : ℕ) : ℤ) = b - s by simp) (heq_of_eq hA) hB
  have hD := hΔ.heq (prodBase sX sY) (tripleBase (𝟙 _) sX sY) (pr₂₃ (𝟙 _) sX sY)
    (pr₂₃_comp_prodBase _ _ _) rfl (relativeDimension_prodBase k sX sY hX hY)
    (relativeDimension_tripleBase k (𝟙 _) sX sY (relativeDimension_identity _) hX hY)
    ((a : ℤ) - i + b) ((b : ℤ) - s)
    (flatPullbackChow (fieldChowSituation k) (prodBase sX sY) sX (pullback.fst sX sY) rfl b
      (relativeDimension_fst k sX sY hY) _
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α) c
  have hS := (heq_of_eq (hΔs (prodBase sX sY) (b + a) (relativeDimension_prodBase k sX sY hX hY)
    ((a : ℤ) - i + b) ((b : ℤ) - s)
    (flatPullbackChow (fieldChowSituation k) (prodBase sX sY) sX (pullback.fst sX sY) rfl b
      (relativeDimension_fst k sX sY hY) _
      (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α) c)).trans
    (chowGroupDegreeEquiv_heq _ _ _ _)
  have hF := (properChowPushforward_comp_apply (fieldChowSituation k) (prodBase sX sY)
    (tripleBase (𝟙 _) sX sY) (prodBase (𝟙 _) sY) (inv (pr₂₃ (𝟙 _) sX sY))
    (pr₁₃ (𝟙 _) sX sY) (pullback.snd sX sY ≫ inv (pullback.snd (𝟙 _) sY))
    (inv_pr₂₃_pr₁₃_eq_snd_inv_snd sX sY) (by rw [IsIso.inv_comp_eq, pr₂₃_comp_prodBase])
    (pr₁₃_comp_prodBase _ _ _) (by simp [pullback.condition])
    ((b : ℤ) - s + ((a : ℤ) - i + b) - ((b + a : ℕ) : ℤ))
    (properPushforwardFactorsThroughRationalEquivalence_of_isIso _ _ _ _ _ _)
    (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
    (selfIntersectionProduct (fieldChowSituation k)
        (fieldChowSituation_dimensionFunction_of_isClosed k)
      (fieldGysinSystem k) (prodBase sX sY) _ (Δ _ _ (relativeDimension_prodBase k sX sY hX hY))
      ((b : ℤ) - s) ((a : ℤ) - i + b) c
      (flatPullbackChow (fieldChowSituation k) (prodBase sX sY) sX (pullback.fst sX sY) rfl b
        (relativeDimension_fst k sX sY hY) _
        (flatPullbackFactorsThroughRationalEquivalence_general _ _ _ _ _ _ _ _) α))).symm.trans
    (properChowPushforward_comp_apply (fieldChowSituation k) (prodBase sX sY) sY
      (prodBase (𝟙 _) sY) (pullback.snd sX sY) (inv (pullback.snd (𝟙 _) sY))
      (pullback.snd sX sY ≫ inv (pullback.snd (𝟙 _) sY)) rfl pullback.condition.symm
      (by rw [IsIso.inv_comp_eq]; exact pullback.condition) (by simp [pullback.condition]) _
      (properPushforwardDescends _ _ _ _ _ _)
      (properPushforwardFactorsThroughRationalEquivalence_of_isIso _ _ _ _ _ _)
      (properPushforwardDescends _ _ _ _ _ _) _)
  refine HEq.trans ?_ ((heq_of_eq hF).trans (HEq.symm ?_))
  · exact properChowPushforward_heq_congr (fieldChowSituation k) (tripleBase (𝟙 _) sX sY)
      (prodBase (𝟙 _) sY) (pr₁₃ (𝟙 _) sX sY) (pr₁₃_comp_prodBase _ _ _)
      (show (b : ℤ) - (i + s) = (b : ℤ) - s + ((a : ℤ) - i + b) - ((b + a : ℕ) : ℤ) by
        push_cast; ring)
      (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
      _ _ ((chowGroupDegreeEquiv_heq _ _ _ _).trans (hC.trans (hD.trans
        (chowPushforwardOfIso_heq_congr (fieldChowSituation k) (prodBase sX sY)
          (tripleBase (𝟙 _) sX sY) (inv (pr₂₃ (𝟙 _) sX sY))
          (by rw [IsIso.inv_comp_eq, pr₂₃_comp_prodBase]) (by ring) _ _ hS))))
  · exact chowPushforwardOfIso_heq_congr (fieldChowSituation k) sY (prodBase (𝟙 _) sY)
      (inv (pullback.snd (𝟙 _) sY)) (by rw [IsIso.inv_comp_eq]; exact pullback.condition)
      (show (b : ℤ) - (i + s) = (b : ℤ) - s + ((a : ℤ) - i + b) - ((b + a : ℕ) : ℤ) by
        push_cast; ring) _ _
      (properChowPushforward_heq_congr (fieldChowSituation k) (prodBase sX sY) sY
        (pullback.snd sX sY) pullback.condition.symm
        (show (b : ℤ) - (i + s) = (b : ℤ) - s + ((a : ℤ) - i + b) - ((b + a : ℕ) : ℤ) by
          push_cast; ring)
        (properPushforwardDescends _ _ _ _ _ _) (properPushforwardDescends _ _ _ _ _ _)
        _ _ (chowGroupDegreeEquiv_heq _ _ _ _))

/-- **Stacks 0FG0 (3), pushforward by correspondences corresponds to composition.** For an
iso-invariant and symmetric family of diagonal classes, `c ∈ Corrˢ(X, Y)` and
`α ∈ CH^i(X) ⊗ ℚ`, the identification `CH^{i+s}(Y) ⊗ ℚ = Corr^{i+s}(Spec k, Y)` carries `c_*(α)`
to `c ∘ α`. -/
theorem correspondenceFromPointEquiv_correspondencePushforward (hΔ : Δ.IsoInvariant)
    (hΔs : Δ.IsSymmetric) [IsProper sX] {a b : ℕ} (hX : RelativeDimension sX a)
    (hY : RelativeDimension sY b) (i s : ℤ) (c : Correspondence (fieldChowSituation k) sX sY b s)
    (α : TensorProduct ℤ ℚ (chowGroup (fieldChowSituation k) sX ((a : ℤ) - i))) :
    correspondenceFromPointEquiv _ sY b (i + s)
        (correspondencePushforward k sX sY Δ hX hY s i c α) =
      composition k (𝟙 _) sX sY Δ (relativeDimension_identity _) hX hY i s
        (correspondenceFromPointEquiv _ sX a i α) c := by
  induction c using TensorProduct.inductionOn with
  | tmul q c =>
    induction α using TensorProduct.inductionOn with
    | tmul q' α =>
      simp only [correspondencePushforward, rationalBilin_tmul, LinearMap.compr₂_apply,
        AddMonoidHom.coe_toIntLinearMap]
      rw [correspondenceFromPointEquiv_tmul, correspondenceFromPointEquiv_tmul, composition_tmul,
        compositionInt_fromPoint sX sY hΔ hΔs hX hY i s α c, mul_comm]
    | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]
  | add x y hx hy => simp only [map_add, LinearMap.add_apply, hx, hy]

end FromPoint

end Stacks.WeilCohomology

end
