module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DivisorVirtualNormalClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClass
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalSubbundle
public import StacksCore.Tactic.StacksAttribute

/-!
# The Gysin class of a closed subscheme commutes with every bivariant class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S`, let `Z ⊆ X` be a closed subscheme with virtual normal sheaf `𝒩`
of constant rank `r`, let `g : Y ⟶ X` be locally of finite type and let `c ∈ A^p(Y ⟶ X)` be a
bivariant class. **Stacks 0FBP** says that `c` and the Gysin class `c(Z ⟶ X, 𝒩) ∈ A^r(Z ⟶ X)` of
Stacks 0FBK commute in the sense of Stacks 0FA2.

The source proves this by reducing to `X` integral (Stacks 02UC), then either `Z = X`, where
`c(Z ⟶ X, 𝒩) = c_top(𝒩)` by Stacks 0FBM and the commutation is Stacks 02UA, or `Z ≠ X`, where
blowing `X` up in the ideal sheaf of `Z` makes `Z` an effective Cartier divisor (Divisors,
Stacks 02OS) and the second half of Stacks 02UC transports the conclusion back. In the effective
Cartier divisor case

  `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ i^*`

by Stacks 0FBL and Stacks 0FBN, with `i^* ∈ A^1(Z ⟶ X)` the Gysin homomorphism of Stacks 0B79 and
`ℰ` the dual of the kernel of `𝒩^∨ ⟶ 𝒞_{Z/X}`; and then `c` commutes with `c_top(ℰ)` because
Chern classes are central in the strong sense of Stacks 02UA, and with `i^*` by the Gysin
condition in the definition of a bivariant class, which is Stacks 0FA3.

This module formalizes that last step — the assembly of the two commutations across the
factorization — and instantiates it three times. In the sharpest instance, where `Z` is the zero
scheme of a section and so already an effective Cartier divisor, everything in the source's final
paragraph is **proved** from results this repository has: the factorization is Stacks 0FBL, the
identification of its second factor with the Gysin homomorphism is Stacks 0FBN, and the
commutation of that factor with `c` is Stacks 0FA3. The one input carried there is the centrality
of the top Chern cap of `ℰ`, Stacks 02UA, and the implementation notes say exactly why the library's
form of that tag cannot be applied to the Chern cap this directory uses.

## Main definitions

* `Stacks.Chow.IsExcessChernGysinFactorization` — the shape of the factorization: that the cap
  operation of a bivariant class for `Z ⟶ X` is a degree-shifting operator on the Chow groups of
  the base changes of `Z` applied after the cap operation of a second bivariant class for
  `Z ⟶ X`. At `c_top(ℰ)` for the operator and `i^*` for the second class this is the displayed
  factorization of Stacks 0FBL and Stacks 0FBN.
* `Stacks.Chow.ExcessChernCapCommutesWithCap` — **Stacks 02UA** for that operator: it carries
  the relation "`x` upstairs is `c` capped with `y` downstairs" to itself, which is the identity
  `c ∘ c_top(ℰ) = c_top(ℰ) ∘ c` read on the base changes of `Z`.
* `Stacks.Chow.subbundleExcessChernOperator` — the top Chern cap of the excess sheaf of a short
  exact sequence `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0`, in the degrees the assembly asks of its operator. With
  it the factorization of Stacks 0FBL is literally the predicate above.

## Main results

* `Stacks.Chow.bivariantCommute_of_isExcessChernGysinFactorization` — the assembly: a bivariant
  class whose cap operation factors as above commutes with `c` as soon as the operator and the
  second factor do.
* `Stacks.Chow.virtualNormalGysinClass_bivariantCommute_of_subbundle` — **Stacks 0FBP** with the
  factorization **proved**, by consuming Stacks 0FBL for a short exact sequence
  `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0`; the commutation of `c` with `c(Z ⟶ X, 𝒩')` is still a hypothesis.
* `Stacks.Chow.virtualNormalGysinClass_bivariantCommute_of_divisor` — **Stacks 0FBP in the
  effective Cartier divisor case**, the case the source's reduction lands in, with Stacks 0FBL,
  Stacks 0FBN and Stacks 0FA3 all consumed and only Stacks 02UA carried.

## Implementation notes

### What is proved, what is carried, and that the carried input is not the conclusion

`Stacks.Chow.IsExcessChernGysinFactorization` is the shape of the factorization of Stacks 0FBL
and Stacks 0FBN. Both tags are available in this repository —
`Stacks.Chow.virtualNormalGysinCap_eq_topChernCap_comp` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalSubbundle` is Stacks 0FBL, the
identity `c(Z ⟶ X, 𝒩) ∩ α = c_top(ℰ) ∩ (c(Z ⟶ X, 𝒩') ∩ α)` for a short exact sequence
`0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0`, and `Stacks.Chow.gysinBivariantClass_eq_virtualNormalGysinClass` of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.DivisorVirtualNormalClass` is Stacks 0FBN,
that for a zero scheme the rank-one class `c(Z ⟶ X, i^*𝓛)` is the Gysin homomorphism. So the
predicate is a shape and not an assumption: it is **discharged** from those two in the subbundle
and divisor instances below, with their own hypotheses threaded through.

`Stacks.Chow.ExcessChernCapCommutesWithCap` is Stacks 02UA, and it is carried in all three
instances. That tag is proved in this repository, as
`Stacks.Chow.isChernCapFamily_bivariantClass`, and it cannot be used here, for two independent
reasons. The first is that the library's form is the identity the projective bundle characterization
of Stacks 02U6 gives: an identity between two families `Stacks.Chow.IsChernCapFamily`, one per
test scheme, each carrying the projective bundle of the module with its relative dimension, its
first Chern class cap operator and both halves of Stacks 02TX, so applying it would mean carrying
such a package for every test scheme over `X` together with Stacks 0B7B for each, and then
transporting the identity across the comparison isomorphism of the two iterated base changes,
which no declaration here performs. The implementation notes of
`StacksFrontier.AlgebraicGeometry.Chow.ChernClassHigher.ProjectiveBundleBivariantClass` record the
matching gap on their side: clause (1) of Stacks 02UA, the centrality of `c_j(ℰ)`, is not
available there as a statement about `Stacks.Chow.BivariantCommute`. The second reason is
decisive: the Chern cap that Stacks 0FBL's factorization produces is
`Stacks.Chow.subbundleTopChernCap`, built from the `Stacks.Chow.HigherChernCapRule` that this
directory carries as its stand-in for Stacks 0B7G, not yet formalized, whereas the library's Stacks
02UA is
a statement about `Stacks.Chow.chernCapOnChow`, the cap product the projective bundle relation
constructs. Nothing in this repository identifies the two, so even a complete transport of the
library's tag would be about a different operation than the one appearing in the factorization.

The carried centrality has the same *shape* as the conclusion — it is a commutation of the
operator with the cap of `c`, where the conclusion is a commutation of `c(Z ⟶ X, 𝒩)` with `c` —
and it is worth being precise about why it is nevertheless a different statement. The operator is
not a bivariant class for `Z ⟶ X`: it is a degree-shifting family of endomorphisms of the Chow
groups of the base changes of `Z`, which is what the cap product with a Chern class of a module on
`Z` is. The hypothesis mentions neither `c(Z ⟶ X, 𝒩)` nor the second factor, and the conclusion
mentions neither the operator nor the factorization. What the assembly contributes is exactly the
source's "conclude because Chern classes are in the centre and `c` commutes with `i^*`": the two
commutations plus the factorization give the third.

### Why the conditional form, and that it is not weaker

`Stacks.Chow.ExcessChernCapCommutesWithCap` is stated as an implication: if a class `x` on
`Z ×_X (Y ×_X T)` and a class `y` on `Z ×_X T` are related by capping with `c`, then so are their
images under the operator. The two sides of the relation live on the two iterated fibre products
`Z ×_X (Y ×_X T)` and `Y ×_X (Z ×_X T)`, and are compared by pushing forward along
`Stacks.Chow.commuteComparisonHom`, exactly as `Stacks.Chow.BivariantCommute` compares them. That
pushforward is an isomorphism, so the implication determines `x` from `y` and the conditional form
is equivalent to the unconditional identity `c_top(ℰ) ∘ (c ∩ -) = (c ∩ -) ∘ c_top(ℰ)`; it is
written as an implication only so that the assembly can be the composite of the two hypotheses
with no further transport.

### The degrees

The operator is indexed by the degree `k` of the class on the test scheme rather than by its own
input degree, so that it maps the degree `k - pb` that the second factor produces to the degree
`k - pN` that the Gysin class produces. No equality between `pN`, `pb` and the degree of the
operator is needed anywhere below — in the source's case `pb = 1`, `pN = r` and the operator has
degree `r - 1`, the rank of `ℰ` — and the indexing is what keeps every identity below a
homogeneous equality rather than a transport. This is the idiom of
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClass`, which indexes its
flat pullback `π` the same way and for the same reason.

### The reduction of the source, and what is therefore missing

The passage from a general closed subscheme to an effective Cartier divisor is not carried out.
It needs Stacks 02UC applied to the difference of the two composites `res(c₁) ∘ c₂` and
`res(c₂) ∘ c₁`, and this repository constructs no composite of bivariant classes — only
`Stacks.Chow.IsBivariantClassComposition`, the characterizing property, as
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.Commuting` records. It also needs the blowup of
Stacks 02OS and the base change compatibility of Stacks 0FBJ for the Gysin class, which
`StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.VirtualNormalBundleClass` records as
unproved.
So `Stacks.Chow.virtualNormalGysinClass_bivariantCommute_of_subbundle` proves the factorization
whenever `𝒩` has a subsheaf with locally free quotient, which is the situation Stacks 0FBL
covers; and
`Stacks.Chow.virtualNormalGysinClass_bivariantCommute_of_divisor` is the case where `Z` is
already the zero scheme of a section, where no reduction is needed at all.

## References

* [Stacks Project, Tag 0FBP](https://stacks.math.columbia.edu/tag/0FBP)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBL](https://stacks.math.columbia.edu/tag/0FBL)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBN](https://stacks.math.columbia.edu/tag/0FBN)
* [Stacks Project, Tag 0FA2](https://stacks.math.columbia.edu/tag/0FA2)
* [Stacks Project, Tag 0FA3](https://stacks.math.columbia.edu/tag/0FA3)
* [Stacks Project, Tag 0FAA](https://stacks.math.columbia.edu/tag/0FAA)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02UA](https://stacks.math.columbia.edu/tag/02UA)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 0FBJ](https://stacks.math.columbia.edu/tag/0FBJ)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits
open Stacks.AlgebraicGeometry.ReflexiveModules

universe u

namespace Stacks.Chow

/-! ### The factorization and the centrality of the excess Chern cap -/

section Factorization

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Z Y : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (i : Z ⟶ X) [LocallyOfFiniteType i] (f : Y ⟶ X) [LocallyOfFiniteType f]
  (pb pN p : ℤ)
  (b : BivariantClass C G (i ≫ sX) sX i rfl pb)
  (cN : BivariantClass C G (i ≫ sX) sX i rfl pN)
  (c : BivariantClass C G (f ≫ sX) sX f rfl p)
  (Φ : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ),
    chowGroup C (pullback.fst i t ≫ (i ≫ sX)) (k - pb) →+
      chowGroup C (pullback.fst i t ≫ (i ≫ sX)) (k - pN))

/-- **Stacks 0FBL and Stacks 0FBN.** The factorization `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ i^*` of the
Gysin class of a virtual normal sheaf on an effective Cartier divisor, written on cap operations:
on every test scheme `t : T ⟶ X` and in every degree, capping with `cN` is capping with `b` and
then applying the operator `Φ` on the Chow groups of the base change `Z ×_X T`.

In the source `b` is the Gysin homomorphism `i^* ∈ A^1(Z ⟶ X)` of Stacks 0B79 and `Φ` is the cap
product with the top Chern class of the excess sheaf `ℰ`, the dual of the kernel of
`𝒩^∨ ⟶ 𝒞_{Z/X}`; the sheaf `ℰ` and the exact sequence producing it are Stacks 0FBL and the
factorization is Stacks 0FBN, and neither tag has a carrier in this repository. What the assembly
below uses is only the displayed factorization, so `Φ` is an arbitrary degree-shifting operator
and `b` an arbitrary bivariant class for `Z ⟶ X`. -/
def IsExcessChernGysinFactorization : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (α : chowGroup C (t ≫ sX) k), cN.cap t k α = Φ t k (b.cap t k α)

/-- **Stacks 02UA.** That the operator `Φ` is central for `c`: whenever a class `x` on
`Z ×_X (Y ×_X T)` is the cap product of `c` with a class `y` on `Z ×_X T`, read through the
comparison isomorphism of the two iterated fibre products and the equality of their degrees, the
same holds of `Φ x` and `Φ y`.

With `Φ` the cap product with the top Chern class of the excess sheaf this is the identity
`c ∘ c_top(ℰ) = c_top(ℰ) ∘ c` of Stacks 02UA, read on the base changes of `Z` along the test
schemes of `X`. The comparison of the two iterated fibre products and of the two degrees is the
one `Stacks.Chow.BivariantCommute` uses. Since the comparison morphism is an isomorphism, the
implication determines `x` from `y`, so this is no weaker than the unconditional identity; see
the implementation notes. -/
def ExcessChernCapCommutesWithCap : Prop :=
  ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ)
    (x : chowGroup C (pullback.fst i (pullback.fst f t ≫ f) ≫ (i ≫ sX)) (k - p - pb))
    (y : chowGroup C (pullback.fst i t ≫ (i ≫ sX)) (k - pb)),
    chowPushforwardOfIso C (pullback.fst i (pullback.fst f t ≫ f) ≫ (i ≫ sX))
          (pullback.fst f (pullback.fst i t ≫ i) ≫ (f ≫ sX)) (commuteComparisonHom i f t)
          (commuteComparisonHom_comp_structureMorphism C sX i f t) (k - p - pb) x =
        chowGroupDegreeEquiv C (pullback.fst f (pullback.fst i t ≫ i) ≫ (f ≫ sX))
          (show k - pb - p = k - p - pb by ring)
          (c.cap (pullback.fst i t ≫ i) (k - pb)
            (chowGroupCongr C (Category.assoc (pullback.fst i t) i sX).symm (k - pb) y)) →
      chowPushforwardOfIso C (pullback.fst i (pullback.fst f t ≫ f) ≫ (i ≫ sX))
            (pullback.fst f (pullback.fst i t ≫ i) ≫ (f ≫ sX)) (commuteComparisonHom i f t)
            (commuteComparisonHom_comp_structureMorphism C sX i f t) (k - p - pN)
            (Φ (pullback.fst f t ≫ f) (k - p) x) =
          chowGroupDegreeEquiv C (pullback.fst f (pullback.fst i t ≫ i) ≫ (f ≫ sX))
            (show k - pN - p = k - p - pN by ring)
            (c.cap (pullback.fst i t ≫ i) (k - pN)
              (chowGroupCongr C (Category.assoc (pullback.fst i t) i sX).symm (k - pN)
                (Φ t k y)))

/-- **The assembly step of the proof of Stacks 0FBP.** Let `cN ∈ A^{pN}(Z ⟶ X)` have a cap
operation factoring as an operator `Φ` applied after the cap operation of `b ∈ A^{pb}(Z ⟶ X)`.
If `Φ` is central for `c ∈ A^p(Y ⟶ X)` and `b` commutes with `c`, then `cN` commutes with `c`.

This is the source's "conclude because Chern classes are in the centre of the bivariant ring in
the strong sense of Stacks 02UA, and `c` commutes with the Gysin homomorphism `i^*` by the
definition of a bivariant class": the two iterated cap operations of `cN` and `c` are, by the
factorization, the images under `Φ` of the two iterated cap operations of `b` and `c`, and those
two are related by the commutation of `b` with `c`, which centrality of `Φ` then carries along. -/
theorem bivariantCommute_of_isExcessChernGysinFactorization
    (hfact : IsExcessChernGysinFactorization C G sX i pb pN b cN Φ)
    (hcentral : ExcessChernCapCommutesWithCap C G sX i f pb pN p c Φ)
    (hb : BivariantCommute C G sX i f pb p b c) :
    BivariantCommute C G sX i f pN p cN c := by
  intro T t _ k α
  have hb' := hb t k α
  simp only [bivariantIteratedCap_apply] at hb' ⊢
  rw [hfact, hfact]
  exact hcentral t k _ _ hb'

end Factorization

/-! ### Stacks 0FBP for the Gysin class of a virtual normal sheaf -/

section VirtualNormal

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Z Y N : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sN : N ⟶ C.S) [LocallyOfFiniteType sN]
  (i : Z ⟶ X) [IsImmersion i] [LocallyOfFiniteType i]
  (q : N ⟶ Z) [LocallyOfFiniteType q] (hq : q ≫ (i ≫ sX) = sN) (r : ℕ) (e : ℤ)
  (E : BivariantClass C G sN sX (q ≫ i) (comp_comp_structureMorphism_eq hq rfl) e)
  (π : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
    chowGroup C (pullback.fst i g ≫ (i ≫ sX)) (k - (r : ℤ)) →+
      chowGroup C (pullback.fst (q ≫ i) g ≫ sN) (k - e))
  (P : VirtualNormalBundleProjection i q r)
  (f : Y ⟶ X) [LocallyOfFiniteType f] (pb p : ℤ)
  (b : BivariantClass C G (i ≫ sX) sX i rfl pb)
  (cN : BivariantClass C G (i ≫ sX) sX i rfl (r : ℤ))
  (c : BivariantClass C G (f ≫ sX) sX f rfl p)
  (Φ : ∀ {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ),
    chowGroup C (pullback.fst i t ≫ (i ≫ sX)) (k - pb) →+
      chowGroup C (pullback.fst i t ≫ (i ≫ sX)) (k - (r : ℤ)))

end VirtualNormal

/-! ### The top Chern cap of the excess sheaf as the operator the assembly consumes -/

section Operator

variable (C : ChowSituation.{u}) {X Z N N' : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (i : Z ⟶ X) [IsImmersion i] [LocallyOfFiniteType i]
  {q : N ⟶ Z} [LocallyOfFiniteType q] {q' : N' ⟶ Z} [LocallyOfFiniteType q']
  (m m' e : ℕ) (Eb : Z.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Eb e]
  (cap : HigherChernCapRule C e)
  (P : VirtualNormalBundleProjection i q m) (P' : VirtualNormalBundleProjection i q' m')
  (inc : P'.normalBundle.bundle ⟶ P.normalBundle.bundle) (pr : P.normalBundle.bundle ⟶ Eb)
  (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact) (x : Z)

/-- The cap product with the top Chern class of the excess sheaf `ℰ` of a short exact sequence
`0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0`, read in the degrees the assembly above asks of its operator: it takes the
degree `k - m'` that `c(Z ⟶ X, 𝒩')` produces to the degree `k - m` that `c(Z ⟶ X, 𝒩)` produces.

This is `Stacks.Chow.subbundleTopChernCap` transported along the equality
`(k - m') - e = k - m`, which the short exact sequence supplies through
`Stacks.Chow.subbundleVirtualNormalDegree_eq`. With this operator the factorization of
Stacks 0FBL is exactly `Stacks.Chow.IsExcessChernGysinFactorization`. -/
def subbundleExcessChernOperator {T : Scheme.{u}} (t : T ⟶ X) [LocallyOfFiniteType t] (k : ℤ) :
    chowGroup C (pullback.fst i t ≫ (i ≫ sX)) (k - (m' : ℤ)) →+
      chowGroup C (pullback.fst i t ≫ (i ≫ sX)) (k - (m : ℤ)) :=
  (chowGroupDegreeEquiv C (pullback.fst i t ≫ (i ≫ sX))
      (subbundleVirtualNormalDegree_eq P P' Eb inc pr w hseq x k)).toAddMonoidHom.comp
    (subbundleTopChernCap C (i ≫ sX) i m' e Eb cap t k)

end Operator

/-! ### Stacks 0FBP with the factorization supplied by Stacks 0FBL -/

section Subbundle

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Z Y N N' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sN : N ⟶ C.S) [LocallyOfFiniteType sN]
  (sN' : N' ⟶ C.S) [LocallyOfFiniteType sN']
  (i : Z ⟶ X) [IsImmersion i] [LocallyOfFiniteType i]
  (q : N ⟶ Z) [LocallyOfFiniteType q] (q' : N' ⟶ Z) [LocallyOfFiniteType q']
  (hq : q ≫ (i ≫ sX) = sN) (hq' : q' ≫ (i ≫ sX) = sN')
  (j : N' ⟶ N) [IsClosedImmersion j] (hj : j ≫ q = q')
  (m m' e : ℕ) (Eb : Z.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Eb e]
  (cap : HigherChernCapRule C e) (hdesc : FlatPullbackDescends C)
  (E : BivariantClass C G sN sX (q ≫ i) (comp_comp_structureMorphism_eq hq rfl) 0)
  (E' : BivariantClass C G sN' sX (q' ≫ i) (comp_comp_structureMorphism_eq hq' rfl) 0)
  (P : VirtualNormalBundleProjection i q m) (P' : VirtualNormalBundleProjection i q' m')
  (inc : P'.normalBundle.bundle ⟶ P.normalBundle.bundle) (pr : P.normalBundle.bundle ⟶ Eb)
  (f : Y ⟶ X) [LocallyOfFiniteType f] (p : ℤ)

/-- **Stacks 0FBP with the factorization proved.** Let `i : Z ⟶ X` be a closed subscheme with
virtual normal sheaf `𝒩` of constant rank `m`, let `0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0` be a short exact
sequence of finite locally free modules whose conormal surjection factors as Stacks 0FBL asks,
let `g : Y ⟶ X` be locally of finite type and let `c ∈ A^p(Y ⟶ X)`. If `c` commutes with
`c(Z ⟶ X, 𝒩')` and the top Chern cap of `ℰ` is central for `c`, then `c` commutes with
`c(Z ⟶ X, 𝒩)`.

The factorization `c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')` is **not** carried here: it is
Stacks 0FBL, `Stacks.Chow.virtualNormalGysinCap_eq_topChernCap_comp`, and its hypotheses — the
short exact sequence, the factoring of the conormal surjection, the injectivity of Stacks 02TY,
and the two carried inputs of that tag — are threaded through. What is carried is the centrality
of the top Chern cap, which is Stacks 02UA; the commutation with `c(Z ⟶ X, 𝒩')` is a hypothesis
here and is discharged for a divisor in
`Stacks.Chow.virtualNormalGysinClass_bivariantCommute_of_divisor`. -/
@[stacks 0FBP "with the factorization c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩') PROVED, by \
consuming Stacks 0FBL for a short exact sequence 0 ⟶ 𝒩' ⟶ 𝒩 ⟶ ℰ ⟶ 0. CARRIED: the \
centrality of the top Chern cap of ℰ for c (Stacks 02UA, formalized only against the projective \
bundle rule and not this directory's carried cap rule), and that c commutes with c(Z ⟶ X, 𝒩')"]
theorem virtualNormalGysinClass_bivariantCommute_of_subbundle
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hsigma : dualMap inc ≫ P'.normalBundle.surjection = P.normalBundle.surjection) (x : Z)
    (hinj : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C (i ≫ sX) sN i q hq m P.flat P.relativeDimension hdesc g k))
    (hfactor : SubbundleGysinFactorization C G (i ≫ sX) sX sN sN' i rfl q q' hq hq' j hj E E')
    (hstep : SubbundleGysinTopChernStep C (i ≫ sX) sN sN' i q q' hq hq' j hj m m' e Eb cap hdesc
      P P')
    {cN : BivariantClass C G (i ≫ sX) sX i rfl (m : ℤ)}
    {cN' : BivariantClass C G (i ≫ sX) sX i rfl (m' : ℤ)}
    (c : BivariantClass C G (f ≫ sX) sX f rfl p)
    (hcN : IsVirtualNormalGysinClass C G (i ≫ sX) sX sN i rfl q hq m 0 E
      (bundleFlatPullback C (i ≫ sX) sN i q hq m P.flat P.relativeDimension hdesc) P cN)
    (hcN' : IsVirtualNormalGysinClass C G (i ≫ sX) sX sN' i rfl q' hq' m' 0 E'
      (bundleFlatPullback C (i ≫ sX) sN' i q' hq' m' P'.flat P'.relativeDimension hdesc) P' cN')
    (hcentral : ExcessChernCapCommutesWithCap C G sX i f (m' : ℤ) (m : ℤ) p c
      (subbundleExcessChernOperator C sX i m m' e Eb cap P P' inc pr w hseq x))
    (hb : BivariantCommute C G sX i f (m' : ℤ) p cN' c) :
    BivariantCommute C G sX i f (m : ℤ) p cN c := by
  refine bivariantCommute_of_isExcessChernGysinFactorization C G sX i f (m' : ℤ) (m : ℤ) p cN'
    cN c (subbundleExcessChernOperator C sX i m m' e Eb cap P P' inc pr w hseq x) ?_ hcentral hb
  intro T t _ k α
  exact virtualNormalGysinCap_eq_topChernCap_comp (C := C) (G := G) (sZ := i ≫ sX) (sX := sX)
    (sN := sN) (sN' := sN') (i := i) (hi := rfl) (q := q) (q' := q') (hq := hq) (hq' := hq')
    (j := j) (hj := hj) (m := m) (m' := m') (e := e) (Eb := Eb) (cap := cap) (hdesc := hdesc)
    (E := E) (E' := E') (P := P) (P' := P') (inc := inc) (pr := pr) w hseq hsigma x hinj hfactor
    hstep hcN hcN' t k α

end Subbundle

/-! ### Stacks 0FBP when the subscheme is an effective Cartier divisor -/

section Divisor

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X Y N N' : Scheme.{u}}
  (sX : X ⟶ C.S) [LocallyOfFiniteType sX] (sN : N ⟶ C.S) [LocallyOfFiniteType sN]
  (sN' : N' ⟶ C.S) [LocallyOfFiniteType sN']
  (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤))
  (q : N ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme) [LocallyOfFiniteType q]
  (q' : N' ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme) [LocallyOfFiniteType q']
  (hq : q ≫ (gysinTripleInclusion L s ≫ sX) = sN)
  (hq' : q' ≫ (gysinTripleInclusion L s ≫ sX) = sN')
  (j : N' ⟶ N) [IsClosedImmersion j] (hj : j ≫ q = q')
  (m e : ℕ) (Eb : (Stacks.Divisors.zeroScheme X L s).subscheme.Modules)
  [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} Eb e]
  (cap : HigherChernCapRule C e) (hdesc : FlatPullbackDescends C)
  (E : BivariantClass C G sN sX (q ≫ gysinTripleInclusion L s)
    (comp_comp_structureMorphism_eq hq rfl) 0)
  (E' : BivariantClass C G sN' sX (q' ≫ gysinTripleInclusion L s)
    (comp_comp_structureMorphism_eq hq' rfl) 0)
  (P : VirtualNormalBundleProjection (gysinTripleInclusion L s) q m)
  (P' : VirtualNormalBundleProjection (gysinTripleInclusion L s) q' 1)
  (inc : P'.normalBundle.bundle ⟶ P.normalBundle.bundle) (pr : P.normalBundle.bundle ⟶ Eb)
  (f : Y ⟶ X) [LocallyOfFiniteType f] (p : ℤ)

/-- **Stacks 0FBP for an effective Cartier divisor**, the case the source's reduction lands in.
Let `(𝓛, s, i : Z ⟶ X)` be a triple as in Stacks 02T8, so that `Z` is the zero scheme of `s` and
hence an effective Cartier divisor, let `𝒩` be a virtual normal sheaf for `i` of constant rank
`m`, let `𝒩' = i^*𝓛` be the rank-one virtual normal sheaf of the divisor sitting inside `𝒩` with
quotient the excess sheaf `ℰ`, let `g : Y ⟶ X` be locally of finite type and let
`c ∈ A^p(Y ⟶ X)`. Then `c(Z ⟶ X, 𝒩)` commutes with `c`.

This is the source's argument with everything but one input discharged. The factorization
`c(Z ⟶ X, 𝒩) = c_top(ℰ) ∘ c(Z ⟶ X, 𝒩')` is Stacks 0FBL; the identification of the second factor
with the Gysin homomorphism `i^*` of Stacks 0B79 is Stacks 0FBN,
`Stacks.Chow.gysinBivariantClass_eq_virtualNormalGysinClass`; and the commutation of `i^*` with
`c` is Stacks 0FA3, `Stacks.Chow.gysinBivariantCommute`, which derives it from the Gysin
condition in the definition of a bivariant class. The one carried input is the centrality of the
top Chern cap of `ℰ`, Stacks 02UA. -/
@[stacks 0FBP "the effective Cartier divisor case, the case the source's reduction lands in. \
PROVED by consuming Stacks 0FBL (the factorization through the rank-one subsheaf), \
0FBN (that factor is the Gysin class i^*) and 0FA3 (i^* commutes with c), with their own \
hypotheses threaded. CARRIED: only the centrality of the top Chern cap of ℰ, Stacks 02UA"]
theorem virtualNormalGysinClass_bivariantCommute_of_divisor
    (w : inc ≫ pr = 0) (hseq : (ShortComplex.mk inc pr w).ShortExact)
    (hsigma : dualMap inc ≫ P'.normalBundle.surjection = P.normalBundle.surjection)
    (x : (Stacks.Divisors.zeroScheme X L s).subscheme)
    (hinj : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C (gysinTripleInclusion L s ≫ sX) sN (gysinTripleInclusion L s) q hq
          m P.flat P.relativeDimension hdesc g k))
    (hinj' : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C (gysinTripleInclusion L s ≫ sX) sN' (gysinTripleInclusion L s) q'
          hq' 1 P'.flat P'.relativeDimension hdesc g k))
    (hfactor : SubbundleGysinFactorization C G (gysinTripleInclusion L s ≫ sX) sX sN sN'
      (gysinTripleInclusion L s) rfl q q' hq hq' j hj E E')
    (hstep : SubbundleGysinTopChernStep C (gysinTripleInclusion L s ≫ sX) sN sN'
      (gysinTripleInclusion L s) q q' hq hq' j hj m 1 e Eb cap hdesc P P')
    (cTop : DivisorTopChernCapFamily C sX L s)
    (hbundle : P'.normalBundle.bundle =
      (Scheme.Modules.pullback (gysinTripleInclusion L s)).obj L)
    (hG : G.IsNaturalUnderPullbackCompPushforward)
    {cN : BivariantClass C G (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s)
      rfl (m : ℤ)}
    {cN' gys : BivariantClass C G (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s)
      rfl ((1 : ℕ) : ℤ)}
    (c : BivariantClass C G (f ≫ sX) sX f rfl p)
    (hcN : IsVirtualNormalGysinClass C G (gysinTripleInclusion L s ≫ sX) sX sN
      (gysinTripleInclusion L s) rfl q hq m 0 E
      (bundleFlatPullback C (gysinTripleInclusion L s ≫ sX) sN (gysinTripleInclusion L s) q hq m
        P.flat P.relativeDimension hdesc) P cN)
    (hcN' : IsVirtualNormalGysinClass C G (gysinTripleInclusion L s ≫ sX) sX sN'
      (gysinTripleInclusion L s) rfl q' hq' 1 0 E'
      (bundleFlatPullback C (gysinTripleInclusion L s ≫ sX) sN' (gysinTripleInclusion L s) q'
        hq' 1 P'.flat P'.relativeDimension hdesc) P' cN')
    (hgys : IsGysinBivariantClass C G sX L s gys)
    (hoff : GysinCapFundamentalOffDivisor C G sX L s)
    (hon : GysinCapFundamentalOnDivisor C G sX L s cTop)
    (hvn : VirtualNormalCapFundamentalOnDivisor C G sX L s cTop cN')
    (hdim : ∀ {W : Scheme.{u}} (g : W ⟶ X) [LocallyOfFiniteType g] (n : ℤ),
      (¬ ∃ h : W ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme,
        h ≫ gysinTripleInclusion L s = g) →
      schemeDeltaDimension C
          (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) ≤
        ((n - ((1 : ℕ) : ℤ) : ℤ) : EInt))
    (hcone : ∀ {W : Scheme.{u}} (g : W ⟶ X) [LocallyOfFiniteType g] (n : ℤ),
      (¬ ∃ h : W ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme,
        h ≫ gysinTripleInclusion L s = g) →
      chowGroupDegreeEquiv C (pullback.fst (q' ≫ gysinTripleInclusion L s) g ≫ sN')
          (by omega : n - (0 : ℤ) = (n - ((1 : ℕ) : ℤ)) + ((1 : ℕ) : ℤ))
          (E'.cap g n (fundamentalChowClass C (g ≫ sX) n)) =
        fundamentalChowClass C (pullback.fst (q' ≫ gysinTripleInclusion L s) g ≫ sN')
          ((n - ((1 : ℕ) : ℤ)) + ((1 : ℕ) : ℤ)))
    (hcentral : ExcessChernCapCommutesWithCap C G sX (gysinTripleInclusion L s) f
      ((1 : ℕ) : ℤ) (m : ℤ) p c
      (subbundleExcessChernOperator C sX (gysinTripleInclusion L s) m 1 e Eb cap P P' inc pr w
        hseq x)) :
    BivariantCommute C G sX (gysinTripleInclusion L s) f (m : ℤ) p cN c := by
  have hFBN : gys = cN' :=
    gysinBivariantClass_eq_virtualNormalGysinClass C G sX L s sN' q' hq' E' P' hdesc cTop
      hinj' hbundle hgys hcN' hoff hon hvn hdim hcone
  have hb : BivariantCommute C G sX (gysinTripleInclusion L s) f ((1 : ℕ) : ℤ) p cN' c := by
    rw [← hFBN]
    exact gysinBivariantCommute C G sX L s f p hG c gys hgys
  intro T t _ k α
  exact virtualNormalGysinClass_bivariantCommute_of_subbundle C G sX sN sN'
    (gysinTripleInclusion L s) q q' hq hq' j hj m 1 e Eb cap hdesc E E' P P' inc pr f p w hseq
    hsigma x hinj hfactor hstep c hcN hcN' hcentral hb t k α

end Divisor

end Stacks.Chow

end
