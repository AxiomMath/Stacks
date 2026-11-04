module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation
public import StacksFrontier.AlgebraicGeometry.Chow.GysinRationalEquivalenceInvertible

/-!
# Gysin pullback and the Chern class cap products

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `ℰ` be a finite locally free `O_X`-module of rank `r`, and
let `(L, s, i : D ⟶ X)` be the datum of Stacks 02T8: an invertible module `L` on `X`, a global
section `s` of `L`, and the closed immersion of its zero scheme `D = Z(s)`. Stacks 0B7G asserts

  `c_j(ℰ|_D) ∩ i^*α = i^*(c_j(ℰ) ∩ α)`

for every `α ∈ A_{k+1}(X)`.

The Stacks proof runs through the projective-bundle characterization of Stacks 02U6, which
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation` supplies. Let
`(π : P ⟶ X, O_P(1))` be the projective bundle of `ℰ` and `(π_D : P_D ⟶ D, O_{P_D}(1))` that of
`ℰ|_D`; then `P_D = D ×_X P`, the morphism `i' : P_D ⟶ P` is the Gysin datum of the pulled-back
section `π^*s` of `π^*L`, and `O_{P_D}(1)` is the restriction of `O_P(1)`. Applying `(i')^*` to
the relation satisfied by the family `c_j(ℰ) ∩ α` turns each summand into the corresponding
summand for the family `i^*(c_j(ℰ) ∩ α)`, by Stacks 0B72 for the first Chern class caps and
Stacks 0B71 for the `π^*`, so that family satisfies the relation over `D`; its zeroth member is
`i^*α`; and the uniqueness of Stacks 02U6 identifies it with the family `c_j(ℰ|_D) ∩ i^*α`.

## Main definitions

* `Stacks.Chow.ChernTermsCompatibleWithGysin` — **Stacks 0B72 and 0B71, assembled**: Gysin
  pullback along `i'` carries each summand of the relation over `X` to the corresponding summand
  over `D`.
* `Stacks.Chow.gysinChernFamily` — the Gysin pullback of a family of Chow classes, read in the
  degrees of a family based at `k`.

## Main results

* `Stacks.Chow.gysinHomomorphismOnChowOfInvertible_chowGroupCast` — Gysin pullback commutes with
  transport along an equality of degrees.
* `Stacks.Chow.gysin_projectiveBundleChernRelation` — the Gysin pullback of a family satisfying
  the relation over `X` satisfies the relation over `D`.
* `Stacks.Chow.gysin_isChernCapFamily` — the Gysin pullback of a characterizing family is a
  characterizing family of the Gysin pullback of the class.
* `Stacks.Chow.isChernCapFamily_gysin` — **Stacks 0B7G**: Gysin pullback commutes with the Chern
  class cap products.

## Implementation notes

### The compatibility of the summands is one hypothesis, and which tags it is

A summand of the relation is `c₁(O_P(1))^i ∩ π^*(-)`. Carrying it past `(i')^*` is Stacks 0B71
(the Gysin map commutes with flat pullback, applied to the cartesian square
`π ∘ i' = i ∘ π_D`) followed by `i` applications of Stacks 0B72 (the Gysin map commutes with the
first Chern class cap). Neither tag is available unconditionally here — Stacks 0B71 appears only
as `Stacks.Chow.gysinHomomorphism_flatPullback` of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.FlatPullback` and Stacks 0B72 only as
`Stacks.Chow.gysinHomomorphismOnChow_firstChernClassCapOnChow` of
`StacksFrontier.AlgebraicGeometry.Chow.Gysin42.ChernCap`, both carrying their integral-component
case as a hypothesis, and the first Chern class cap operators of the two bundles here are
unrelated data — so the composite identity is taken as the single hypothesis
`Stacks.Chow.ChernTermsCompatibleWithGysin`, stated on the summands themselves. Stating it
summand by summand rather than on the whole relation is what keeps it a statement about Stacks
0B71 and 0B72: the passage from the summands to the relation is the additivity of `(i')^*`, and
that is `Stacks.Chow.gysin_projectiveBundleChernRelation` below.

### The second bundle, and the second zero scheme

The projective bundle of `ℰ|_D` is realized here as the zero scheme of a section `t` of an
invertible module `M` on `P`, which is what `(L, s)` pulls back to along `π`; that realization
is what makes `(i')^*` a Gysin map of Stacks 02T8 at all, so it is built into the statements
rather than assumed. Nothing here asserts that `M` is `π^*L` and `t` is `π^*s`, nor that the
resulting square is cartesian, nor that the twist of the second bundle restricts the twist of
the first: those facts enter only through the compatibility hypothesis, which is exactly what
they are used for in the source. So the statements hold for any such pair `(M, t)`, any
`π_D : Z(t) ⟶ D` flat of relative dimension `r - 1`, and any first Chern class cap operator on
`Z(t)` with that compatibility, which is a generalization of Stacks 0B7G and not a weakening.

### Degrees

The Gysin map lowers the degree by one, so the base degree on `X` is written `k + 1` and the
base degree on `D` is written `k`; a family on `X` based at `k + 1` has `j`-th member of degree
`k + 1 - j` and its Gysin pullback has `j`-th member of degree `k - j`. The summands of the
relation over `X` land in degree `k + 1 + (r-1) - r` and those over `D` in degree `k + (r-1) - r`,
which differ by one as they must; the two are not the same term, so one transport of
`Stacks.Chow.chowGroupCast` appears in the compatibility hypothesis.

### Stacks 02TO is carried for the invertible module itself

Both Gysin maps are `Stacks.Chow.gysinHomomorphismOnChowOfInvertible`, so the only hypothesis
they carry is the vanishing of Stacks 02TO for the first Chern class component rule of the
invertible module in question. No component rule is threaded, and
`Stacks.Chow.gysinOfInvertibleFactorsThroughRationalEquivalence_iff_exists` says that carrying
the vanishing loses nothing: it is equivalent to the existence of the descended Gysin map, which
is the content of Stacks 02TO.

## References

* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TO](https://stacks.math.columbia.edu/tag/02TO)
* [Stacks Project, Tag 0B71](https://stacks.math.columbia.edu/tag/0B71)
* [Stacks Project, Tag 0B72](https://stacks.math.columbia.edu/tag/0B72)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
* [Stacks Project, Tag 02OQ](https://stacks.math.columbia.edu/tag/02OQ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Chow

/-! ### Gysin pullback and transport of degrees -/

/-- Gysin pullback on Chow groups commutes with transport along an equality of degrees. -/
theorem gysinHomomorphismOnChowOfInvertible_chowGroupCast (C : ChowSituation.{u})
    {X : Scheme.{u}} (p : X ⟶ C.S) [LocallyOfFiniteType p] (L : X.Modules)
    [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
    (s : Γ(L, ⊤)) {k l : ℤ} (h : k = l)
    (hk : GysinOfInvertibleFactorsThroughRationalEquivalence C p k L s)
    (hl : GysinOfInvertibleFactorsThroughRationalEquivalence C p l L s)
    (x : chowGroup C p (k + 1)) :
    chowGroupCast C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ p) h
        (gysinHomomorphismOnChowOfInvertible C p k L s hk x) =
      gysinHomomorphismOnChowOfInvertible C p l L s hl
        (chowGroupCast C p (show k + 1 = l + 1 from by rw [h]) x) := by
  subst h; rfl

/-! ### The two bundles and the compatibility of their relations -/

variable (C : ChowSituation.{u}) {X P : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π]
  (hsP : π ≫ sX = sP) (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (M : P.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible P.sheaf.obj P.ringCatSheaf.property M]
  (t : Γ(M, ⊤))
  (πD : (Stacks.Divisors.zeroScheme P M t).subscheme ⟶
    (Stacks.Divisors.zeroScheme X L s).subscheme)
  [LocallyOfFiniteType πD] [Flat πD]
  (hsPD : πD ≫ ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX) =
    (Stacks.Divisors.zeroScheme P M t).subschemeι ≫ sP)
  (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hπD : AlgebraicGeometry.RelativeDimension πD (r - 1))
  (hfacπ : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)
  (hfacπD : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C
    ((Stacks.Divisors.zeroScheme P M t).subschemeι ≫ sP)
    ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX) πD hsPD (r - 1) hπD k)
  (twistP : ChernCapOperator C sP)
  (twistD : ChernCapOperator C ((Stacks.Divisors.zeroScheme P M t).subschemeι ≫ sP))
  (hgysX : ∀ k : ℤ, GysinOfInvertibleFactorsThroughRationalEquivalence C sX k L s)
  (hgysP : ∀ k : ℤ, GysinOfInvertibleFactorsThroughRationalEquivalence C sP k M t)

/-- **Stacks 0B72 and 0B71, assembled.** Gysin pullback along `i' : P_D ⟶ P` carries the `i`-th
summand `c₁(O_P(1))^i ∩ π^*(-)` of the relation over `X` to the `i`-th summand
`c₁(O_{P_D}(1))^i ∩ π_D^*(-)` of the relation over `D`, precomposed with Gysin pullback along
`i`.

This is Stacks 0B71 for the square `π ∘ i' = i ∘ π_D` followed by `i` applications of Stacks
0B72; see the implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleGysin`. -/
def ChernTermsCompatibleWithGysin : Prop :=
  ∀ (k : ℤ) (i : ℕ) (hi : i ≤ r) (x : chowGroup C sX (k + 1 - ((r - i : ℕ) : ℤ))),
    gysinHomomorphismOnChowOfInvertible C sP (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)) M t
        (hgysP (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)))
        (chowGroupCast C sP
          (show k + 1 + ((r - 1 : ℕ) : ℤ) - (r : ℤ) =
              k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + 1 from by omega)
          (projectiveBundleChernTerm C sX sP π hsP r hπ hfacπ twistP (k + 1) i hi x)) =
      projectiveBundleChernTerm C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX)
        ((Stacks.Divisors.zeroScheme P M t).subschemeι ≫ sP) πD hsPD r hπD hfacπD twistD k i hi
        (gysinHomomorphismOnChowOfInvertible C sX (k - ((r - i : ℕ) : ℤ)) L s
          (hgysX (k - ((r - i : ℕ) : ℤ)))
          (chowGroupCast C sX
            (show k + 1 - ((r - i : ℕ) : ℤ) = k - ((r - i : ℕ) : ℤ) + 1 from by omega) x))

/-- The Gysin pullback of a family of Chow classes on `X` based at `k + 1`, read in the degrees
of a family on `D` based at `k`. -/
def gysinChernFamily (k : ℤ)
    (c : ∀ j : Fin (r + 1), chowGroup C sX (k + 1 - (j : ℤ))) (j : Fin (r + 1)) :
    chowGroup C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX) (k - (j : ℤ)) :=
  gysinHomomorphismOnChowOfInvertible C sX (k - (j : ℤ)) L s (hgysX (k - (j : ℤ)))
    (chowGroupCast C sX (show k + 1 - (j : ℤ) = k - (j : ℤ) + 1 from by omega) (c j))

/-- The Gysin pullback of a family satisfying the projective-bundle relation over `X` satisfies
the projective-bundle relation over `D`: apply `(i')^*` to the relation and use the
compatibility of the summands. -/
theorem gysin_projectiveBundleChernRelation
    (hcompat : ChernTermsCompatibleWithGysin C sX sP π hsP L s M t πD hsPD r hπ hπD hfacπ
      hfacπD twistP twistD hgysX hgysP) (k : ℤ)
    (c : ∀ j : Fin (r + 1), chowGroup C sX (k + 1 - (j : ℤ)))
    (hc : ProjectiveBundleChernRelation C sX sP π hsP r hπ hfacπ twistP (k + 1) c) :
    ProjectiveBundleChernRelation C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX)
      ((Stacks.Divisors.zeroScheme P M t).subschemeι ≫ sP) πD hsPD r hπD hfacπD twistD k
      (gysinChernFamily C sX L s r hgysX k c) := by
  have hrel : ∑ i : Fin (r + 1), (-1 : ℤ) ^ i.val •
      projectiveBundleChernTerm C sX sP π hsP r hπ hfacπ twistP (k + 1) i.val
        (Nat.lt_succ_iff.mp i.isLt) (c ⟨r - i.val, by omega⟩) = 0 := hc
  have h := congrArg (fun y ↦ gysinHomomorphismOnChowOfInvertible C sP
    (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)) M t (hgysP (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)))
    (chowGroupCast C sP (show k + 1 + ((r - 1 : ℕ) : ℤ) - (r : ℤ) =
      k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) + 1 from by omega) y)) hrel
  simp only [map_sum, map_zsmul, map_zero] at h
  refine Eq.trans ?_ h
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  exact congrArg (fun y ↦ (-1 : ℤ) ^ i.val • y)
    (hcompat k i.val (Nat.lt_succ_iff.mp i.isLt) (c ⟨r - i.val, by omega⟩)).symm

/-- The Gysin pullback of a family characterizing the Chern class cap products of `α` is a
family characterizing the Chern class cap products of `i^*α`. -/
theorem gysin_isChernCapFamily
    (hcompat : ChernTermsCompatibleWithGysin C sX sP π hsP L s M t πD hsPD r hπ hπD hfacπ
      hfacπD twistP twistD hgysX hgysP) (k : ℤ) (α : chowGroup C sX (k + 1))
    (c : ∀ j : Fin (r + 1), chowGroup C sX (k + 1 - (j : ℤ)))
    (hc : IsChernCapFamily C sX sP π hsP r hπ hfacπ twistP (k + 1) α c) :
    IsChernCapFamily C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX)
      ((Stacks.Divisors.zeroScheme P M t).subschemeι ≫ sP) πD hsPD r hπD hfacπD twistD k
      (gysinHomomorphismOnChowOfInvertible C sX k L s (hgysX k) α)
      (gysinChernFamily C sX L s r hgysX k c) := by
  refine ⟨?_, gysin_projectiveBundleChernRelation C sX sP π hsP L s M t πD hsPD r hπ hπD hfacπ
    hfacπD twistP twistD hgysX hgysP hcompat k c hc.2⟩
  simp only [gysinChernFamily]
  rw [gysinHomomorphismOnChowOfInvertible_chowGroupCast C sX L s
      (show k - ((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) : ℤ) = k from by simp)
      (hgysX (k - ((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) : ℤ))) (hgysX k),
    chowGroupCast_chowGroupCast]
  exact congrArg _ hc.1

/-- **Stacks 0B7G.** Gysin pullback commutes with the Chern class cap products: if `c` is the
family of Chern class cap products of `α ∈ A_{k+1}(X)` for `ℰ` and `e` is the family of Chern
class cap products of `i^*α ∈ A_k(D)` for `ℰ|_D`, then `e_j = i^*(c_j)`, that is

  `c_j(ℰ|_D) ∩ i^*α = i^*(c_j(ℰ) ∩ α)`.

The proof is the one in the source: the Gysin pullback of `c` satisfies the relation over `D`
and has `i^*α` in degree `k`, so the uniqueness of Stacks 02U6 identifies it with `e`. -/
theorem isChernCapFamily_gysin
    (hinjD : ProjectiveBundleRelationInjective C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX)
      ((Stacks.Divisors.zeroScheme P M t).subschemeι ≫ sP) πD hsPD r hπD hfacπD twistD)
    (hcompat : ChernTermsCompatibleWithGysin C sX sP π hsP L s M t πD hsPD r hπ hπD hfacπ
      hfacπD twistP twistD hgysX hgysP) (k : ℤ) (α : chowGroup C sX (k + 1))
    (c : ∀ j : Fin (r + 1), chowGroup C sX (k + 1 - (j : ℤ)))
    (e : ∀ j : Fin (r + 1), chowGroup C
      ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX) (k - (j : ℤ)))
    (hc : IsChernCapFamily C sX sP π hsP r hπ hfacπ twistP (k + 1) α c)
    (he : IsChernCapFamily C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX)
      ((Stacks.Divisors.zeroScheme P M t).subschemeι ≫ sP) πD hsPD r hπD hfacπD twistD k
      (gysinHomomorphismOnChowOfInvertible C sX k L s (hgysX k) α) e) :
    e = gysinChernFamily C sX L s r hgysX k c :=
  eq_of_isChernCapFamily C ((Stacks.Divisors.zeroScheme X L s).subschemeι ≫ sX)
    ((Stacks.Divisors.zeroScheme P M t).subschemeι ≫ sP) πD hsPD r hπD hfacπD twistD hinjD k
    (gysinHomomorphismOnChowOfInvertible C sX k L s (hgysX k) α) he
    (gysin_isChernCapFamily C sX sP π hsP L s M t πD hsPD r hπ hπD hfacπ hfacπD twistP twistD
      hgysX hgysP hcompat k α c hc)

end Stacks.Chow

end
