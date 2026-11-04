module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation
public import StacksFrontier.AlgebraicGeometry.Chow.ProperPushforwardPrincipal.GenericFibre

/-!
# Proper pushforward and the Chern class cap products

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `p : X ⟶ Y` be a
proper morphism between schemes locally of finite type over `S`, and let `ℰ` be a finite locally
free `O_Y`-module of rank `r`. Stacks 02U9 asserts the projection formula

  `p_*(c_j(p^*ℰ) ∩ α) = c_j(ℰ) ∩ p_*α`

for every `k`-cycle `α` on `X`.

The Stacks proof runs through the projective-bundle characterization of Stacks 02U6, which
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation` supplies. Let
`(π : P ⟶ Y, O_P(1))` be the projective bundle of `ℰ` and `(π_X : P_X ⟶ X, O_{P_X}(1))` that of
`p^*ℰ`; then `P_X = X ×_Y P`, the morphism `p' : P_X ⟶ P` is proper and `O_{P_X}(1)` is the
pullback of `O_P(1)`. Applying `(p')_*` to the relation satisfied by the family
`α_j = c_j(p^*ℰ) ∩ α` turns each summand into the corresponding summand for the family
`p_*α_j`, by Stacks 02SU for the first Chern class caps and Stacks 02RG for the `π^*`, so that
family satisfies the relation over `Y`; its zeroth member is `p_*α`; and the uniqueness of Stacks
02U6 identifies it with the family `c_j(ℰ) ∩ p_*α`.

This is the proper-pushforward twin of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleFlatPullback`, and is
simpler in one respect: proper pushforward preserves the degree of a Chow class, so the family
transported here needs no transport along an equality of degrees.

## Main definitions

* `Stacks.Chow.ChernTermsCompatibleWithPushforward` — **Stacks 02SU and 02RG, assembled**: proper
  pushforward along `p'` carries each summand of the relation over `X` to the corresponding
  summand over `Y`.
* `Stacks.Chow.properPushforwardChernFamily` — the proper pushforward of a family of Chow classes
  on `X`, degree by degree.

## Main results

* `Stacks.Chow.properChowPushforward_chowGroupCast` — proper pushforward commutes with transport
  along an equality of degrees.
* `Stacks.Chow.properPushforward_projectiveBundleChernRelation` — the proper pushforward of a
  family satisfying the relation over `X` satisfies the relation over `Y`.
* `Stacks.Chow.properPushforward_isChernCapFamily` — the proper pushforward of a characterizing
  family is a characterizing family of the proper pushforward of the class.
* `Stacks.Chow.isChernCapFamily_properPushforward` — **Stacks 02U9**: proper pushforward commutes
  with the Chern class cap products.

## Implementation notes

### The compatibility of the summands is one hypothesis, and which tags it is

A summand of the relation is `c₁(O_P(1))^i ∩ π^*(-)`. Carrying it past `(p')_*` is Stacks 02RG
(proper pushforward commutes with flat pullback across the cartesian square with sides `p` and
`π`, applied to `π ∘ p' = p ∘ π_X`) followed by `i` applications of Stacks 02SU (proper
pushforward commutes with the first Chern class cap). Neither tag's statement about the *Chow*
groups occurring here is available unconditionally in this repository — Stacks 02SU appears only
as `Stacks.Chow.properChowPushforward_firstChernClassCap`, which carries the component rules of
the two cap products and their compatibility `Stacks.Chow.FirstChernCapCompatibleWithPushforward`
along `p'` as hypotheses, and the first Chern class cap operators of the two bundles here are
unrelated data — so the composite identity is taken as the single hypothesis
`Stacks.Chow.ChernTermsCompatibleWithPushforward`, stated on the summands themselves. Stating it
summand by summand rather than on the whole relation is what keeps it a statement about Stacks
02SU and 02RG: the passage from the summands to the relation is the additivity of `(p')_*`, and
that is `Stacks.Chow.properPushforward_projectiveBundleChernRelation` below.

### Stacks 02S2 is not a hypothesis

Proper pushforward on Chow groups, `Stacks.Chow.properChowPushforward`, needs the vanishing of
Stacks 02S2, and that vanishing is a theorem in this repository for every proper morphism over
the base: `Stacks.Chow.properPushforwardFactorsThroughRationalEquivalence_of_isProper`. It is
supplied from there at each degree below rather than carried, so `p` and `p'` enter with no
hypothesis beyond properness and commutation with the structure morphisms. This is the one place
where this file is unconditional and its flat-pullback twin is not: the corresponding statement
for flat pullback, Stacks 02S1, is a hypothesis there.

### The second bundle is a parameter too

Nothing here asserts that `P_X` is `X ×_Y P`, nor that `O_{P_X}(1)` is the pullback of `O_P(1)`,
nor that `p'` is the base change of `p`: those facts enter only through the compatibility
hypothesis, which is exactly what they are used for in the source. So the statements hold for any
pair of bundles and any proper `p'` over `p` with that compatibility, which is a generalization
of Stacks 02U9 and not a weakening.

## References

* [Stacks Project, Tag 02U9](https://stacks.math.columbia.edu/tag/02U9)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02SU](https://stacks.math.columbia.edu/tag/02SU)
* [Stacks Project, Tag 02RG](https://stacks.math.columbia.edu/tag/02RG)
* [Stacks Project, Tag 02S2](https://stacks.math.columbia.edu/tag/02S2)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 0GU8](https://stacks.math.columbia.edu/tag/0GU8)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Proper pushforward and transport of degrees -/

/-- Proper pushforward on Chow groups commutes with transport along an equality of degrees. -/
theorem properChowPushforward_chowGroupCast (C : ChowSituation.{u}) {X Y : Scheme.{u}}
    (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
    (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX) {k l : ℤ} (h : k = l) (x : chowGroup C sX k) :
    chowGroupCast C sY h
        (properChowPushforward C sX sY p hp k
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp k) x) =
      properChowPushforward C sX sY p hp l
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp l)
        (chowGroupCast C sX h x) := by
  subst h; rfl

/-! ### The two bundles and the compatibility of their relations -/

variable (C : ChowSituation.{u}) {X Y PX PY : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sY : Y ⟶ C.S) [LocallyOfFiniteType sY]
  (sPX : PX ⟶ C.S) [LocallyOfFiniteType sPX] (sPY : PY ⟶ C.S) [LocallyOfFiniteType sPY]
  (πX : PX ⟶ X) [LocallyOfFiniteType πX] [Flat πX] (hsPX : πX ≫ sX = sPX)
  (πY : PY ⟶ Y) [LocallyOfFiniteType πY] [Flat πY] (hsPY : πY ≫ sY = sPY)
  (r : ℕ) (hπX : AlgebraicGeometry.RelativeDimension πX (r - 1))
  (hπY : AlgebraicGeometry.RelativeDimension πY (r - 1))
  (hfacX : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sPX sX πX hsPX (r - 1) hπX k)
  (hfacY : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sPY sY πY hsPY (r - 1) hπY k)
  (twistX : ChernCapOperator C sPX) (twistY : ChernCapOperator C sPY)
  (p : X ⟶ Y) [IsProper p] (hp : p ≫ sY = sX)
  (p' : PX ⟶ PY) [IsProper p'] (hp' : p' ≫ sPY = sPX)

/-- **Stacks 02SU and 02RG, assembled.** Proper pushforward along `p' : P_X ⟶ P` carries the
`i`-th summand `c₁(O_{P_X}(1))^i ∩ π_X^*(-)` of the relation over `X` to the `i`-th summand
`c₁(O_P(1))^i ∩ π^*(-)` of the relation over `Y`, precomposed with proper pushforward along `p`.

This is Stacks 02RG for the square `π ∘ p' = p ∘ π_X` followed by `i` applications of Stacks
02SU; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProperPushforward`. -/
def ChernTermsCompatibleWithPushforward : Prop :=
  ∀ (k : ℤ) (i : ℕ) (hi : i ≤ r) (x : chowGroup C sX (k - ((r - i : ℕ) : ℤ))),
    properChowPushforward C sPX sPY p' hp' (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPX sPY p' hp'
          (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)))
        (projectiveBundleChernTerm C sX sPX πX hsPX r hπX hfacX twistX k i hi x) =
      projectiveBundleChernTerm C sY sPY πY hsPY r hπY hfacY twistY k i hi
        (properChowPushforward C sX sY p hp (k - ((r - i : ℕ) : ℤ))
          (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp
            (k - ((r - i : ℕ) : ℤ))) x)

/-- The proper pushforward of a family of Chow classes on `X`. Proper pushforward preserves the
degree of a class, so the pushed-forward family is read in the same degrees. -/
def properPushforwardChernFamily (k : ℤ)
    (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ))) (j : Fin (r + 1)) :
    chowGroup C sY (k - (j : ℤ)) :=
  properChowPushforward C sX sY p hp (k - (j : ℤ))
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp (k - (j : ℤ)))
    (c j)

/-- The proper pushforward of a family satisfying the projective-bundle relation over `X`
satisfies the projective-bundle relation over `Y`: apply `(p')_*` to the relation and use the
compatibility of the summands. -/
theorem properPushforward_projectiveBundleChernRelation
    (hcompat : ChernTermsCompatibleWithPushforward C sX sY sPX sPY πX hsPX πY hsPY r hπX hπY
      hfacX hfacY twistX twistY p hp p' hp') (k : ℤ)
    (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)))
    (hc : ProjectiveBundleChernRelation C sX sPX πX hsPX r hπX hfacX twistX k c) :
    ProjectiveBundleChernRelation C sY sPY πY hsPY r hπY hfacY twistY k
      (properPushforwardChernFamily C sX sY r p hp k c) := by
  unfold ProjectiveBundleChernRelation at hc ⊢
  rw [← map_zero (properChowPushforward C sPX sPY p' hp' (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))
    (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sPX sPY p' hp'
      (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)))), ← hc, map_sum]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [map_zsmul, hcompat k i.val (Nat.lt_succ_iff.mp i.isLt) (c ⟨r - i.val, by omega⟩)]
  rfl

/-- The proper pushforward of a family characterizing the Chern class cap products of `α` is a
family characterizing the Chern class cap products of `p_*α`. -/
theorem properPushforward_isChernCapFamily
    (hcompat : ChernTermsCompatibleWithPushforward C sX sY sPX sPY πX hsPX πY hsPY r hπX hπY
      hfacX hfacY twistX twistY p hp p' hp') (k : ℤ)
    (α : chowGroup C sX k) (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)))
    (hc : IsChernCapFamily C sX sPX πX hsPX r hπX hfacX twistX k α c) :
    IsChernCapFamily C sY sPY πY hsPY r hπY hfacY twistY k
      (properChowPushforward C sX sY p hp k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp k) α)
      (properPushforwardChernFamily C sX sY r p hp k c) := by
  refine ⟨?_, properPushforward_projectiveBundleChernRelation C sX sY sPX sPY πX hsPX πY hsPY r
    hπX hπY hfacX hfacY twistX twistY p hp p' hp' hcompat k c hc.2⟩
  simp only [properPushforwardChernFamily]
  rw [properChowPushforward_chowGroupCast C sX sY p hp
    (show k - ((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) : ℤ) = k from by simp), hc.1]

/-- **Stacks 02U9.** Proper pushforward commutes with the Chern class cap products: if `c` is the
family of Chern class cap products of `α ∈ A_k(X)` for `p^*ℰ` and `e` is the family of Chern
class cap products of `p_*α ∈ A_k(Y)` for `ℰ`, then `e_j = p_*(c_j)`, that is

  `c_j(ℰ) ∩ p_*α = p_*(c_j(p^*ℰ) ∩ α)`.

The proof is the one in the source: the proper pushforward of `c` satisfies the relation over `Y`
and has `p_*α` in degree `k`, so the uniqueness of Stacks 02U6 identifies it with `e`. -/
@[stacks 02U9 "carries both projective bundles as flat morphisms of relative dimension r - 1 with
first Chern class cap operators for their twists (Stacks 01O4, 02SO, 02TI), Stacks 02S1 for their
projections, a proper morphism between the two bundles lying over p, the injectivity half of
Stacks 02TX over the target, the compatibility of the summands of the relation with proper
pushforward (Stacks 02SU and Stacks 02RG), and the cap products of Stacks 02U5 as families
satisfying the characterization of Stacks 02U6"]
theorem isChernCapFamily_properPushforward
    (hinjY : ProjectiveBundleRelationInjective C sY sPY πY hsPY r hπY hfacY twistY)
    (hcompat : ChernTermsCompatibleWithPushforward C sX sY sPX sPY πX hsPX πY hsPY r hπX hπY
      hfacX hfacY twistX twistY p hp p' hp') (k : ℤ)
    (α : chowGroup C sX k) (c : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)))
    (e : ∀ j : Fin (r + 1), chowGroup C sY (k - (j : ℤ)))
    (hc : IsChernCapFamily C sX sPX πX hsPX r hπX hfacX twistX k α c)
    (he : IsChernCapFamily C sY sPY πY hsPY r hπY hfacY twistY k
      (properChowPushforward C sX sY p hp k
        (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp k) α) e) :
    e = properPushforwardChernFamily C sX sY r p hp k c :=
  eq_of_isChernCapFamily C sY sPY πY hsPY r hπY hfacY twistY hinjY k
    (properChowPushforward C sX sY p hp k
      (properPushforwardFactorsThroughRationalEquivalence_of_isProper C sX sY p hp k) α) he
    (properPushforward_isChernCapFamily C sX sY sPX sPY πX hsPX πY hsPY r hπX hπY hfacX hfacY
      twistX twistY p hp p' hp' hcompat k α c hc)

end Stacks.Chow

end
