module

public import StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleExistence
public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Basic

/-!
# Bivariant classes and the Chern class cap products

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `ℰ` be a finite locally free `O_X`-module of rank `r`, let
`f : X' ⟶ X` be locally of finite type and let `c ∈ A^p(X' ⟶ X)` be a bivariant class of degree
`p`. Stacks 02UA asserts

  `c ∘ c_j(ℰ) = c_j(f^*ℰ) ∘ c`   in   `A^{p+j}(X' ⟶ X)`,

which is clause (2) of the tag; clause (1), that `c_j(ℰ)` lies in the center of `A^*(X)`, is the
case `f = 𝟙 X`, and the "in particular" of the tag is the resulting commutation

  `c_i(ℰ) ∩ c_j(ℱ) ∩ α = c_j(ℱ) ∩ c_i(ℰ) ∩ α`

of the cap products of two finite locally free modules.

The proof in the source runs through the projective-bundle characterization of Stacks 02U6, which
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleRelation` supplies. Let
`(π : P ⟶ X, O_P(1))` be the projective bundle of `ℰ` and `(π' : P' ⟶ X', O_{P'}(1))` its base
change along `f`. Applying `c` to the relation satisfied by the family `c_j(ℰ) ∩ α` turns each
summand into the corresponding summand for the family `c ∩ (c_j(ℰ) ∩ α)`, by Stacks 0B7B; so that
family satisfies the relation downstairs, its zeroth member is `c ∩ α`, and the uniqueness of
Stacks 02U6 identifies it with the family `c_j(f^*ℰ) ∩ (c ∩ α)`.

Nothing in that argument uses what the operation `c ∩ -` *is*, only that it lowers degrees by a
fixed amount and carries each summand of the relation to the corresponding summand. So the
argument is carried out here once, for an arbitrary such operation, and then instantiated twice:
at the cap product of a bivariant class, which is clause (2), and at the cap product with the
`j`-th Chern class of a second module, which is the "in particular". The three earlier instances
of the same pattern — Stacks 02U8 in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleFlatPullback`, Stacks 02U9
in `StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleProperPushforward` and
Stacks 0B7G in `StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleGysin` — each
write the argument out for their one operation. Of those three, proper pushforward (at `q = 0`)
and the Gysin map (at `q = 1`) are instances of the general form below and flat pullback is not,
since it *raises* the degree; none of the three is refactored onto it here, and their statements
are left unchanged.

## Main definitions

* `Stacks.Chow.ChernTermsCompatibleWithOperation` — that a degree-lowering operation carries each
  summand of the relation over `X` to the corresponding summand over `X'`.
* `Stacks.Chow.operationChernFamily` — the image of a family of Chow classes under such an
  operation, read in the degrees of a family based at `k - q`.
* `Stacks.Chow.ChernTermsCompatibleWithBivariantClass` — **Stacks 0B7B**: the compatibility above
  for the cap product of a bivariant class.
* `Stacks.Chow.bivariantChernFamily` — the cap product of a bivariant class with a family.
* `Stacks.Chow.ChernTermsCompatibleWithChernCap` — the compatibility above for the cap product
  with the `j`-th Chern class of a second module.

## Main results

* `Stacks.Chow.chowGroupCast_apply_comm` — a degree-indexed family of maps commutes with
  transport along an equality of degrees.
* `Stacks.Chow.operation_projectiveBundleChernRelation` — the image of a family satisfying the
  relation over `X` satisfies the relation over `X'`.
* `Stacks.Chow.operation_isChernCapFamily` — the image of a characterizing family is a
  characterizing family of the image of the class.
* `Stacks.Chow.isChernCapFamily_operation` — the uniqueness of Stacks 02U6 identifies the two.
* `Stacks.Chow.isChernCapFamily_bivariantClass` — **Stacks 02UA (2)**: a bivariant class carries
  the Chern class cap products of `ℰ` to those of `f^*ℰ`.
* `Stacks.Chow.chernCap_bivariantClass_comm` — the same read member by member, which is the form
  clause (1) takes at `f = 𝟙 X`.
* `Stacks.Chow.chernCapOnChow_comm` — **the "in particular" of Stacks 02UA**: the cap products of
  two finite locally free modules commute.

## Implementation notes

### Where a bivariant class acts, and why the test scheme is a parameter

A bivariant class of degree `p` for `f : X' ⟶ X` is not an operation on `A_*(X)` alone: by the
definition of Stacks 0B76, which is `Stacks.Chow.BivariantClass` here, it is a rule assigning to
every `g : T ⟶ X` locally of finite type a map `A_k(T) ⟶ A_{k-p}(T ×_X X')`. Composition of
bivariant classes is composition of those rules test scheme by test scheme, so the identity
`c ∘ c_j(ℰ) = c_j(f^*ℰ) ∘ c` of the source is, for each test scheme `g`, the identity

  `c ∩ (c_j(ℰ|_T) ∩ α) = c_j(f^*ℰ|_{T ×_X X'}) ∩ (c ∩ α)`   for `α ∈ A_k(T)`.

The clause (2) statements below are that identity, with `g` a parameter. Nothing is lost: an
equality of bivariant classes is by `Stacks.Chow.BivariantClass.ext` exactly an equality of all
their cap operations, so quantifying over `g` and over `α` recovers the equality of composites.
And nothing is gained by fixing `g` to be the identity of `X`: the Chern classes of `ℰ` would then
have to be read on `X ×_X X'` rather than on `X'`, so that specialization needs the invariance of
everything below under the canonical isomorphism `X ×_X X' ≅ X'` and is strictly more work.

### What clause (1) is here, and what it is not

Clause (1) says `c_j(ℰ)` is central in `A^*(X)`, and the source deduces it from clause (2) by
taking `f = 𝟙 X`. That specialization of `Stacks.Chow.isChernCapFamily_bivariantClass` is
immediate and is the content of clause (1); what it is *not* is a statement about the commuting
relation `Stacks.Chow.BivariantCommute` of Stacks 0FA2, because exhibiting `c_j(ℰ)` as a term of
`Stacks.Chow.BivariantClass` is Stacks 0B7H, which is not available here, and because reading the
two iterated cap products on `X` rather than on `X ×_X X` needs the transport of
`Stacks.Chow.IsChernCapFamily` along the identity base change isomorphism, which no declaration
in this repository provides. So no statement below is tagged as clause (1) on its own.

What *is* proved here is the consequence the source draws from clause (1), the "in particular":
`Stacks.Chow.chernCapOnChow_comm`. It needs no bivariant class at all — the cap product with
`c_j(ℱ)` is an operation on `A_*(X)` itself, by
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleExistence` — so it is an
instance of the general form with `X' = X` and the same bundle on both sides.

### The two bundles, and what is not required of the second

The bundle downstairs is not required to be the base change of the bundle upstairs, nor its twist
to be the pullback of the twist upstairs, nor the module downstairs to be `f^*ℰ`: exactly as in
the three earlier instances of the pattern, those facts enter only through the compatibility
hypothesis, which is what they are used for in the source. The statements below therefore hold
for any projection flat of relative dimension `r - 1` and any first Chern class cap operator with
that compatibility, which generalizes Stacks 02UA rather than weakening it.

### The compatibility of the summands is one hypothesis, and which tag it is

A summand of the relation is `c₁(O_P(1))^i ∩ π^*(-)`. Carrying it past the cap product of a
bivariant class `c` is Stacks 0B7B: `c` commutes with flat pullback — which is part of the
definition, the field `Stacks.Chow.BivariantClass.flat_naturality` — and with the first Chern
class cap of an invertible module. The second half is not available unconditionally. The first
Chern class cap operators of the two bundles are unrelated data in this repository, as they are in
the three earlier instances, and the invertible module whose cap they perform is not even named;
and `Stacks.Chow.BivariantClass.gysin_naturality` gives the Gysin map of a zero scheme rather than
the first Chern class cap. So the composite identity is taken as the single hypothesis
`Stacks.Chow.ChernTermsCompatibleWithOperation`, stated on the summands themselves. Stating it
summand by summand rather than on the whole relation is what keeps it a statement about Stacks
0B7B: the passage from the summands to the relation is the additivity of the operation, and that
is `Stacks.Chow.operation_projectiveBundleChernRelation` below.

For the "in particular" the same hypothesis is Stacks 02SS together with Stacks 02U8: it says
that capping with `c_j(ℱ)` commutes with `π^*` and with the first Chern class cap of the twist on
the bundle of `ℰ`.

### Degrees

An operation of degree `q` lowers the degree by `q`, so a family on `X` based at `k` has `j`-th
member of degree `k - j` and its image is read as a family on `X'` based at `k - q`, whose `j`-th
member has degree `k - q - j`. The summands of the relation upstairs land in degree `k + (r-1) - r`
and those downstairs in degree `k - q + (r-1) - r`; the image of the first is in degree
`k + (r-1) - r - q`, the same integer but not the same term, so one transport of
`Stacks.Chow.chowGroupCast` appears in the compatibility hypothesis and one in the definition of
the image family.

### Why the structure morphisms of the bundles are composites in the clause (2) section

`chowGroup` is indexed by a morphism to `S`, and the cap product of `c` for the test scheme
`πT ≫ g` is a map out of `chowGroup C ((πT ≫ g) ≫ sX) _`. So the structure morphism of the
bundle upstairs has to be that composite rather than an abstract `sPT`, and the hypothesis
`hsPT : πT ≫ (g ≫ sX) = (πT ≫ g) ≫ sX` plays the role the equation `hsPX` plays in
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleFlatPullback`. It is
provable — it is associativity — but it is threaded as a hypothesis so that the flat pullback of
the projection, which is indexed by it, is the same term in every statement. For the same reason
the total space of the bundle downstairs is not a parameter: the cap product of `c` for the test
scheme `πT ≫ g` lands on `PT ×_X X'`, which is `pullback f (πT ≫ g)`, so that is the scheme the
bundle downstairs lives on and only its projection is a parameter.

## References

* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02U6](https://stacks.math.columbia.edu/tag/02U6)
* [Stacks Project, Tag 02U5](https://stacks.math.columbia.edu/tag/02U5)
* [Stacks Project, Tag 02U8](https://stacks.math.columbia.edu/tag/02U8)
* [Stacks Project, Tag 02TX](https://stacks.math.columbia.edu/tag/02TX)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B7B](https://stacks.math.columbia.edu/tag/0B7B)
* [Stacks Project, Tag 0B7H](https://stacks.math.columbia.edu/tag/0B7H)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 02S1](https://stacks.math.columbia.edu/tag/02S1)
* [Stacks Project, Tag 0FVK](https://stacks.math.columbia.edu/tag/0FVK)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Limits

universe u

namespace Stacks.Chow

/-! ### A degree-indexed family of maps and transport of degrees -/

/-- A degree-indexed family of maps commutes with transport along an equality of degrees. The
family is a function of the degree, so substituting the equality identifies the two sides. -/
theorem chowGroupCast_apply_comm (C : ChowSituation.{u}) {X X' : Scheme.{u}} (sX : X ⟶ C.S)
    [LocallyOfFiniteType sX] (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (q : ℤ)
    (op : ∀ m : ℤ, chowGroup C sX m →+ chowGroup C sX' (m - q)) {k l : ℤ} (h : k = l)
    (x : chowGroup C sX k) :
    chowGroupCast C sX' (show k - q = l - q from by rw [h]) (op k x) =
      op l (chowGroupCast C sX h x) := by
  subst h; rfl

/-! ### The argument, for an arbitrary degree-lowering operation -/

section Operation

variable (C : ChowSituation.{u}) {X X' P P' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX']
  (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sP' : P' ⟶ C.S) [LocallyOfFiniteType sP']
  (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP)
  (π' : P' ⟶ X') [LocallyOfFiniteType π'] [Flat π'] (hsP' : π' ≫ sX' = sP')
  (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hπ' : AlgebraicGeometry.RelativeDimension π' (r - 1))
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)
  (hfac' : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP' sX' π' hsP' (r - 1) hπ' k)
  (twist : ChernCapOperator C sP) (twist' : ChernCapOperator C sP') (q : ℤ)
  (op : ∀ m : ℤ, chowGroup C sX m →+ chowGroup C sX' (m - q))
  (opP : ∀ m : ℤ, chowGroup C sP m →+ chowGroup C sP' (m - q))

/-- That a degree-lowering operation carries the `i`-th summand `c₁(O_P(1))^i ∩ π^*(-)` of the
relation over `X` to the `i`-th summand `c₁(O_{P'}(1))^i ∩ (π')^*(-)` of the relation over `X'`,
precomposed with the operation on the base.

For the cap product of a bivariant class this is Stacks 0B7B, and for the cap product with the
Chern class of a second module it is Stacks 02SS together with Stacks 02U8; see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleBivariantClass`. -/
def ChernTermsCompatibleWithOperation : Prop :=
  ∀ (k : ℤ) (i : ℕ) (hi : i ≤ r) (x : chowGroup C sX (k - ((r - i : ℕ) : ℤ))),
    chowGroupCast C sP'
        (show k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) - q =
            k - q + ((r - 1 : ℕ) : ℤ) - (r : ℤ) from by omega)
        (opP (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ))
          (projectiveBundleChernTerm C sX sP π hsP r hπ hfac twist k i hi x)) =
      projectiveBundleChernTerm C sX' sP' π' hsP' r hπ' hfac' twist' (k - q) i hi
        (chowGroupCast C sX'
          (show k - ((r - i : ℕ) : ℤ) - q = k - q - ((r - i : ℕ) : ℤ) from by omega)
          (op (k - ((r - i : ℕ) : ℤ)) x))

/-- The image under a degree-`q` operation of a family of Chow classes on `X` based at `k`, read
in the degrees of a family on `X'` based at `k - q`. -/
def operationChernFamily (k : ℤ)
    (d : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ))) (j : Fin (r + 1)) :
    chowGroup C sX' (k - q - (j : ℤ)) :=
  chowGroupCast C sX' (show k - (j : ℤ) - q = k - q - (j : ℤ) from by omega)
    (op (k - (j : ℤ)) (d j))

/-- The image of a family satisfying the projective-bundle relation over `X` satisfies the
projective-bundle relation over `X'`: apply the operation to the relation and use the
compatibility of the summands. -/
theorem operation_projectiveBundleChernRelation
    (hcompat : ChernTermsCompatibleWithOperation C sX sX' sP sP' π hsP π' hsP' r hπ hπ' hfac
      hfac' twist twist' q op opP) (k : ℤ)
    (d : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)))
    (hd : ProjectiveBundleChernRelation C sX sP π hsP r hπ hfac twist k d) :
    ProjectiveBundleChernRelation C sX' sP' π' hsP' r hπ' hfac' twist' (k - q)
      (operationChernFamily C sX sX' r q op k d) := by
  have h := congrArg (fun y ↦ chowGroupCast C sP'
    (show k + ((r - 1 : ℕ) : ℤ) - (r : ℤ) - q = k - q + ((r - 1 : ℕ) : ℤ) - (r : ℤ) from by omega)
    (opP (k + ((r - 1 : ℕ) : ℤ) - (r : ℤ)) y)) hd
  simp only [map_sum, map_zsmul, map_zero] at h
  refine Eq.trans ?_ h
  exact Finset.sum_congr rfl fun i _ ↦ congrArg (fun y ↦ (-1 : ℤ) ^ i.val • y)
    (hcompat k i.val (Nat.lt_succ_iff.mp i.isLt) (d ⟨r - i.val, by omega⟩)).symm

/-- The image of a family characterizing the Chern class cap products of `α` is a family
characterizing the Chern class cap products of the image of `α`. -/
theorem operation_isChernCapFamily
    (hcompat : ChernTermsCompatibleWithOperation C sX sX' sP sP' π hsP π' hsP' r hπ hπ' hfac
      hfac' twist twist' q op opP) (k : ℤ) (α : chowGroup C sX k)
    (d : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)))
    (hd : IsChernCapFamily C sX sP π hsP r hπ hfac twist k α d) :
    IsChernCapFamily C sX' sP' π' hsP' r hπ' hfac' twist' (k - q) (op k α)
      (operationChernFamily C sX sX' r q op k d) := by
  refine ⟨?_, operation_projectiveBundleChernRelation C sX sX' sP sP' π hsP π' hsP' r hπ hπ'
    hfac hfac' twist twist' q op opP hcompat k d hd.2⟩
  simp only [operationChernFamily, chowGroupCast_chowGroupCast]
  rw [chowGroupCast_apply_comm C sX sX' q op
    (show k - ((⟨0, Nat.zero_lt_succ r⟩ : Fin (r + 1)) : ℤ) = k from by simp)]
  exact congrArg _ hd.1

/-- The uniqueness of Stacks 02U6 identifies the image of a characterizing family with the
characterizing family of the image of the class. -/
theorem isChernCapFamily_operation
    (hinj' : ProjectiveBundleRelationInjective C sX' sP' π' hsP' r hπ' hfac' twist')
    (hcompat : ChernTermsCompatibleWithOperation C sX sX' sP sP' π hsP π' hsP' r hπ hπ' hfac
      hfac' twist twist' q op opP) (k : ℤ) (α : chowGroup C sX k)
    (d : ∀ j : Fin (r + 1), chowGroup C sX (k - (j : ℤ)))
    (e : ∀ j : Fin (r + 1), chowGroup C sX' (k - q - (j : ℤ)))
    (hd : IsChernCapFamily C sX sP π hsP r hπ hfac twist k α d)
    (he : IsChernCapFamily C sX' sP' π' hsP' r hπ' hfac' twist' (k - q) (op k α) e) :
    e = operationChernFamily C sX sX' r q op k d :=
  eq_of_isChernCapFamily C sX' sP' π' hsP' r hπ' hfac' twist' hinj' (k - q) (op k α) he
    (operation_isChernCapFamily C sX sX' sP sP' π hsP π' hsP' r hπ hπ' hfac hfac' twist twist' q
      op opP hcompat k α d hd)

end Operation

/-! ### Clause (2): the operation is the cap product of a bivariant class -/

section BivariantClass

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X' X T PT : Scheme.{u}}
  (sX' : X' ⟶ C.S) [LocallyOfFiniteType sX'] (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (f : X' ⟶ X) [LocallyOfFiniteType f] (hf : f ≫ sX = sX') (p : ℤ)
  (c : BivariantClass C G sX' sX f hf p) (g : T ⟶ X) [LocallyOfFiniteType g]
  (πT : PT ⟶ T) [LocallyOfFiniteType πT] [Flat πT]
  (hsPT : πT ≫ (g ≫ sX) = (πT ≫ g) ≫ sX)
  (πT' : pullback f (πT ≫ g) ⟶ pullback f g) [LocallyOfFiniteType πT'] [Flat πT']
  (hsPT' : πT' ≫ (pullback.fst f g ≫ sX') = pullback.fst f (πT ≫ g) ≫ sX')
  (r : ℕ) (hπT : AlgebraicGeometry.RelativeDimension πT (r - 1))
  (hπT' : AlgebraicGeometry.RelativeDimension πT' (r - 1))
  (hfacT : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C ((πT ≫ g) ≫ sX) (g ≫ sX)
    πT hsPT (r - 1) hπT k)
  (hfacT' : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C
    (pullback.fst f (πT ≫ g) ≫ sX') (pullback.fst f g ≫ sX') πT' hsPT' (r - 1) hπT' k)
  (twistT : ChernCapOperator C ((πT ≫ g) ≫ sX))
  (twistT' : ChernCapOperator C (pullback.fst f (πT ≫ g) ≫ sX'))

/-- **Stacks 0B7B.** The cap product of a bivariant class `c` carries each summand of the
relation over the test scheme `T` to the corresponding summand over `T ×_X X'`. -/
def ChernTermsCompatibleWithBivariantClass : Prop :=
  ChernTermsCompatibleWithOperation C (g ≫ sX) (pullback.fst f g ≫ sX') ((πT ≫ g) ≫ sX)
    (pullback.fst f (πT ≫ g) ≫ sX') πT hsPT πT' hsPT' r hπT hπT' hfacT hfacT' twistT twistT' p
    (fun m ↦ c.cap g m) (fun m ↦ c.cap (πT ≫ g) m)

/-- The cap product of a bivariant class with a family of Chow classes on `T` based at `k`, read
in the degrees of a family on `T ×_X X'` based at `k - p`. -/
def bivariantChernFamily (k : ℤ)
    (d : ∀ j : Fin (r + 1), chowGroup C (g ≫ sX) (k - (j : ℤ))) (j : Fin (r + 1)) :
    chowGroup C (pullback.fst f g ≫ sX') (k - p - (j : ℤ)) :=
  operationChernFamily C (g ≫ sX) (pullback.fst f g ≫ sX') r p (fun m ↦ c.cap g m) k d j

/-- **Stacks 02UA (2).** A bivariant class carries the Chern class cap products of `ℰ` to those
of `f^*ℰ`: if `d` is the family of Chern class cap products of `α ∈ A_k(T)` for `ℰ|_T` and `e` is
the family of Chern class cap products of `c ∩ α ∈ A_{k-p}(T ×_X X')` for the pullback of `ℰ`,
then `e_j = c ∩ d_j`, that is

  `c_j(f^*ℰ) ∩ (c ∩ α) = c ∩ (c_j(ℰ) ∩ α)`,

which is the identity `c ∘ c_j(ℰ) = c_j(f^*ℰ) ∘ c` of the tag, read on the test scheme `g`.

The proof is the one in the source: the cap product of `c` with `d` satisfies the relation
downstairs and has `c ∩ α` in degree `k - p`, so the uniqueness of Stacks 02U6 identifies it
with `e`. -/
@[stacks 02UA "clause (2), read on a test scheme; carries both projective bundles as flat
morphisms of relative dimension r - 1 with first Chern class cap operators for their twists
(01O4, 02SO, 02TI, 02S1), the injectivity half of 02TX downstairs, the compatibility of the
summands with the cap product of the bivariant class (0B7B), and 02U5 as 02U6-families"]
theorem isChernCapFamily_bivariantClass
    (hinj' : ProjectiveBundleRelationInjective C (pullback.fst f g ≫ sX')
      (pullback.fst f (πT ≫ g) ≫ sX') πT' hsPT' r hπT' hfacT' twistT')
    (hcompat : ChernTermsCompatibleWithBivariantClass C G sX' sX f hf p c g πT hsPT πT' hsPT' r
      hπT hπT' hfacT hfacT' twistT twistT') (k : ℤ) (α : chowGroup C (g ≫ sX) k)
    (d : ∀ j : Fin (r + 1), chowGroup C (g ≫ sX) (k - (j : ℤ)))
    (e : ∀ j : Fin (r + 1), chowGroup C (pullback.fst f g ≫ sX') (k - p - (j : ℤ)))
    (hd : IsChernCapFamily C (g ≫ sX) ((πT ≫ g) ≫ sX) πT hsPT r hπT hfacT twistT k α d)
    (he : IsChernCapFamily C (pullback.fst f g ≫ sX') (pullback.fst f (πT ≫ g) ≫ sX') πT' hsPT'
      r hπT' hfacT' twistT' (k - p) (c.cap g k α) e) :
    e = bivariantChernFamily C G sX' sX f hf p c g r k d :=
  isChernCapFamily_operation C (g ≫ sX) (pullback.fst f g ≫ sX') ((πT ≫ g) ≫ sX)
    (pullback.fst f (πT ≫ g) ≫ sX') πT hsPT πT' hsPT' r hπT hπT' hfacT hfacT' twistT twistT' p
    (fun m ↦ c.cap g m) (fun m ↦ c.cap (πT ≫ g) m) hinj' hcompat k α d e hd he

/-- **Stacks 02UA (2)** read member by member: the two composites `c ∘ c_j(ℰ)` and
`c_j(f^*ℰ) ∘ c` agree,

  `c_j(f^*ℰ) ∩ (c ∩ α) = c ∩ (c_j(ℰ) ∩ α)`   in   `A_{k-p-j}(T ×_X X')`.

At `f = 𝟙 X` and `c` an arbitrary element of `A^p(X)` this is the centrality of `c_j(ℰ)` in
`A^*(X)`, which is how the source deduces clause (1) from clause (2); see the implementation
notes for what separates it from the commuting relation of Stacks 0FA2. -/
theorem chernCap_bivariantClass_comm
    (hinj' : ProjectiveBundleRelationInjective C (pullback.fst f g ≫ sX')
      (pullback.fst f (πT ≫ g) ≫ sX') πT' hsPT' r hπT' hfacT' twistT')
    (hcompat : ChernTermsCompatibleWithBivariantClass C G sX' sX f hf p c g πT hsPT πT' hsPT' r
      hπT hπT' hfacT hfacT' twistT twistT') (k : ℤ) (α : chowGroup C (g ≫ sX) k)
    (d : ∀ j : Fin (r + 1), chowGroup C (g ≫ sX) (k - (j : ℤ)))
    (e : ∀ j : Fin (r + 1), chowGroup C (pullback.fst f g ≫ sX') (k - p - (j : ℤ)))
    (hd : IsChernCapFamily C (g ≫ sX) ((πT ≫ g) ≫ sX) πT hsPT r hπT hfacT twistT k α d)
    (he : IsChernCapFamily C (pullback.fst f g ≫ sX') (pullback.fst f (πT ≫ g) ≫ sX') πT' hsPT'
      r hπT' hfacT' twistT' (k - p) (c.cap g k α) e) (j : Fin (r + 1)) :
    e j = chowGroupCast C (pullback.fst f g ≫ sX')
        (show k - (j : ℤ) - p = k - p - (j : ℤ) from by omega)
        (c.cap g (k - (j : ℤ)) (d j)) :=
  congrFun (isChernCapFamily_bivariantClass C G sX' sX f hf p c g πT hsPT πT' hsPT' r hπT hπT'
    hfacT hfacT' twistT twistT' hinj' hcompat k α d e hd he) j

end BivariantClass

/-! ### The "in particular": the cap products of two modules commute -/

section TwoModules

variable (C : ChowSituation.{u}) {X P Q QP : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (sP : P ⟶ C.S) [LocallyOfFiniteType sP] (sQ : Q ⟶ C.S)
  [LocallyOfFiniteType sQ] (sQP : QP ⟶ C.S) [LocallyOfFiniteType sQP]
  (π : P ⟶ X) [LocallyOfFiniteType π] [Flat π] (hsP : π ≫ sX = sP)
  (r : ℕ) (hπ : AlgebraicGeometry.RelativeDimension π (r - 1))
  (hfac : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sP sX π hsP (r - 1) hπ k)
  (twist : ChernCapOperator C sP)
  (ρ : Q ⟶ X) [LocallyOfFiniteType ρ] [Flat ρ] (hsQ : ρ ≫ sX = sQ)
  (s : ℕ) (hρ : AlgebraicGeometry.RelativeDimension ρ (s - 1))
  (hfacQ : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sQ sX ρ hsQ (s - 1) hρ k)
  (twistQ : ChernCapOperator C sQ)
  (ρP : QP ⟶ P) [LocallyOfFiniteType ρP] [Flat ρP] (hsQP : ρP ≫ sP = sQP)
  (hρP : AlgebraicGeometry.RelativeDimension ρP (s - 1))
  (hfacQP : ∀ k : ℤ, FlatPullbackFactorsThroughRationalEquivalence C sQP sP ρP hsQP (s - 1) hρP k)
  (twistQP : ChernCapOperator C sQP)
  (hinjQ : ProjectiveBundleRelationInjective C sX sQ ρ hsQ s hρ hfacQ twistQ)
  (hsurjQ : ProjectiveBundleRelationSurjective C sX sQ ρ hsQ s hρ hfacQ twistQ)
  (hinjQP : ProjectiveBundleRelationInjective C sP sQP ρP hsQP s hρP hfacQP twistQP)
  (hsurjQP : ProjectiveBundleRelationSurjective C sP sQP ρP hsQP s hρP hfacQP twistQP)
  (j : Fin (s + 1))

/-- **Stacks 02SS and 02U8 for the second module.** That capping with `c_j(ℱ)` carries each
summand `c₁(O_P(1))^i ∩ π^*(-)` of the relation for `ℰ` over `X` to itself: it commutes with the
flat pullback along `π` and with the first Chern class cap of the twist of the bundle of `ℰ`.

This is what clause (2) of Stacks 02UA supplies once `c_j(ℱ)` is known to be a bivariant class,
which is Stacks 0B7H; carried here directly, since that construction is not available. -/
def ChernTermsCompatibleWithChernCap : Prop :=
  ChernTermsCompatibleWithOperation C sX sX sP sP π hsP π hsP r hπ hπ hfac hfac twist twist
    (j : ℤ) (fun m ↦ chernCapOnChow C sX sQ ρ hsQ s hρ hfacQ twistQ hinjQ hsurjQ m j)
    (fun m ↦ chernCapOnChow C sP sQP ρP hsQP s hρP hfacQP twistQP hinjQP hsurjQP m j)

/-- **The "in particular" of Stacks 02UA.** The Chern class cap products of two finite locally
free modules commute:

  `c_i(ℰ) ∩ (c_j(ℱ) ∩ α) = c_j(ℱ) ∩ (c_i(ℰ) ∩ α)`   in   `A_{k-j-i}(X)`

for every `α ∈ A_k(X)`, which is the displayed identity of the tag.

The proof is the one in the source, with `c = c_j(ℱ) ∩ -` playing the role of the bivariant class
of clause (2): the family `(c_j(ℱ) ∩ (c_i(ℰ) ∩ α))_i` satisfies the relation of Stacks 02U6 over
`X` for the class `c_j(ℱ) ∩ α`, because capping with `c_j(ℱ)` carries each summand of the
relation to itself, and its zeroth member is `c_j(ℱ) ∩ α`; so the uniqueness of Stacks 02U6
identifies it with the family `(c_i(ℰ) ∩ (c_j(ℱ) ∩ α))_i`. -/
@[stacks 02UA "the 'in particular' clause, for the cap products of Stacks 02U6; carries both
projective bundles of F and that of E as flat morphisms of relative dimension one less than the
rank, with first Chern class cap operators for their twists (01O4, 02SO, 02TI, 02S1), both halves
of 02TX, and the commutation of c_j(F) with the summands of E's relation (02SS and 02U8)"]
theorem chernCapOnChow_comm
    (hinj : ProjectiveBundleRelationInjective C sX sP π hsP r hπ hfac twist)
    (hsurj : ProjectiveBundleRelationSurjective C sX sP π hsP r hπ hfac twist)
    (hcompat : ChernTermsCompatibleWithChernCap C sX sP sQ sQP π hsP r hπ hfac twist ρ hsQ s hρ
      hfacQ twistQ ρP hsQP hρP hfacQP twistQP hinjQ hsurjQ hinjQP hsurjQP j)
    (k : ℤ) (α : chowGroup C sX k) (i : Fin (r + 1)) :
    chernCapOnChow C sX sP π hsP r hπ hfac twist hinj hsurj (k - (j : ℤ)) i
        (chernCapOnChow C sX sQ ρ hsQ s hρ hfacQ twistQ hinjQ hsurjQ k j α) =
      chowGroupCast C sX (show k - (i : ℤ) - (j : ℤ) = k - (j : ℤ) - (i : ℤ) from by omega)
        (chernCapOnChow C sX sQ ρ hsQ s hρ hfacQ twistQ hinjQ hsurjQ (k - (i : ℤ)) j
          (chernCapOnChow C sX sP π hsP r hπ hfac twist hinj hsurj k i α)) :=
  congrFun
    (isChernCapFamily_operation C sX sX sP sP π hsP π hsP r hπ hπ hfac hfac twist twist (j : ℤ)
      (fun m ↦ chernCapOnChow C sX sQ ρ hsQ s hρ hfacQ twistQ hinjQ hsurjQ m j)
      (fun m ↦ chernCapOnChow C sP sQP ρP hsQP s hρP hfacQP twistQP hinjQP hsurjQP m j) hinj
      hcompat k α (projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k α)
      (projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj (k - (j : ℤ))
        (chernCapOnChow C sX sQ ρ hsQ s hρ hfacQ twistQ hinjQ hsurjQ k j α))
      (isChernCapFamily_projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj k α)
      (isChernCapFamily_projectiveBundleChernCapFamily C sX sP π hsP r hπ hfac twist hsurj
        (k - (j : ℤ))
        (chernCapOnChow C sX sQ ρ hsQ s hρ hfacQ twistQ hinjQ hsurjQ k j α)))
    i

end TwoModules

end Stacks.Chow

end
