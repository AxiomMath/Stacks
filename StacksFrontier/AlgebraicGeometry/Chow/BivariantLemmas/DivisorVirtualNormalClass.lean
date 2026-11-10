module

public import StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinCommuting
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.ExcessIntersection

/-!
# The Gysin class of a divisor as a virtual normal class

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project, let `X` be a scheme
locally of finite type over `S` and let `(ℒ, s, i : D ⟶ X)` be a triple as in Definition 02T8:
`ℒ` an invertible module on `X`, `s` a global section and `i` the closed immersion of its zero
scheme. The module `𝒩 = i^*ℒ` is a virtual normal sheaf for `D` in `X`, of rank one, and
**Stacks 0FBN** asserts that the Gysin homomorphism `i^*`, viewed as an element of `A^1(D ⟶ X)`
by Stacks 0B79, is the bivariant class `c(D ⟶ X, 𝒩)` of Stacks 0FBK built from it.

The source's proof has three steps. By Stacks 02UC it suffices to compare the two classes on the
fundamental class of every integral scheme `Y` locally of finite type over `X`; if
`dim_δ(Y) = n`, then for `Y` not contained in `D` the divisor `D ×_X Y ⟶ Y` is effective
Cartier, hence a regular immersion of codimension one, and both classes send `[Y]_n` to
`[D ×_X Y]_{n-1}` — the Gysin class by the definition of the Gysin homomorphism and
`c(D ⟶ X, 𝒩)` by Stacks 0FBM; while for `Y` contained in `D` both send `[Y]_n` to
`c_1(𝒩) ∩ [Y]_n`, again by Definition 02T8 and by Stacks 0FBM.

All three steps are carried out here. The reduction is proved from Stacks 02UC, and
the value of `c(D ⟶ X, 𝒩)` in the first case is Stacks 0FBM. What is carried are the
values of the *Gysin* homomorphism on a fundamental class in the two cases, and the value of
`c(D ⟶ X, 𝒩)` in the second; see the implementation notes for exactly which statements those are
and why none of them is the conclusion.

## Main definitions

* `Stacks.Chow.DivisorTopChernCapFamily` — the cap product with the first Chern class of the
  virtual normal sheaf on the base change of the divisor along a test scheme.
* `Stacks.Chow.GysinCapFundamentalOffDivisor` — the value `i^*[Y]_n = [D ×_X Y]_{n-1}` of the
  Gysin homomorphism on the fundamental class of an integral test scheme not contained in `D`.
* `Stacks.Chow.GysinCapFundamentalOnDivisor`,
  `Stacks.Chow.VirtualNormalCapFundamentalOnDivisor` — the two values `c_1(𝒩) ∩ [Y]_n` taken on
  an integral test scheme contained in `D`, by the Gysin homomorphism and by `c(D ⟶ X, 𝒩)`.

## Main results

* `Stacks.Chow.BivariantClass.eq_of_cap_fundamentalChowClass_eq` — **the reduction step of
  Stacks 02UC**: two bivariant classes of the same degree that agree on the fundamental class of
  every integral test scheme are equal.
* `Stacks.Chow.gysinBivariantCap_eq_virtualNormalGysinCap_of_offDivisor` — the first case of the
  source's proof: off the divisor both operations give `[D ×_X Y]_{n-1}`.
* `Stacks.Chow.gysinBivariantClass_eq_virtualNormalGysinClass` — **Stacks 0FBN**: the Gysin
  class of the triple and the virtual normal class of `i^*ℒ` are the same element of
  `A^1(D ⟶ X)`.

## Implementation notes

### The two classes

The Gysin class appears as a bivariant class `gys` of degree one for `i : D ⟶ X` satisfying
`Stacks.Chow.IsGysinBivariantClass`, the characterization of Stacks 0B79: its cap operation on
every test scheme is the Gysin map of the pulled-back section, read on `D ×_X T` through the
identification of Stacks 0B6Y. That characterization determines the class, by
`Stacks.Chow.BivariantClass.ext`. The class itself is `Stacks.Chow.gysinBivariantClass` of
`StacksFrontier.AlgebraicGeometry.Chow.Bivariant.GysinClass` (Stacks 0B79), whose Gysin axiom is
Stacks 0B73, `Stacks.Chow.gysinChowOfInvertible_comm`. This is
exactly the tag's "the Gysin homomorphism `i^*` viewed as an element of `A^1(D ⟶ X)`".

The virtual normal class appears as a bivariant class `c` of degree one satisfying
`Stacks.Chow.IsVirtualNormalGysinClass`, the characterizing relation of Stacks 0FBK, against the
genuine flat pullback `Stacks.Chow.bundleFlatPullback` of the bundle projection. That the
virtual normal sheaf of the tag is `i^*ℒ` is the hypothesis `_hbundle`.

### The virtual normal sheaf `i^*ℒ` is given, not built

`Stacks.Chow.VirtualNormalBundle` asks for a surjection `𝒩^∨ ⟶ 𝒞_{D/X}` onto the conormal
sheaf. For `𝒩 = i^*ℒ` the tag's surjection is the canonical isomorphism
`𝒞_{D/X} ≅ (i^*ℒ)^∨`, and nothing in this repository produces it: no declaration relates the
zero scheme of a section to its conormal sheaf, or to a regular immersion of codimension one.
So the virtual normal bundle and its bundle projection are data, as they are in every other
consumer of Stacks 0FBK here, and the identification of the underlying module with `i^*ℒ` is
the hypothesis `_hbundle`. The same choice is made in the statement of Stacks 0FBN.

### What is carried in each case, and why

* `Stacks.Chow.GysinCapFundamentalOffDivisor` is the source's "which is true by definition for
  the Gysin homomorphism": for an integral `Y` on which the pulled-back section does not vanish
  identically, `i^*[Y]_n = [D ×_X Y]_{n-1}`. The component formula behind it is proved, as
  `Stacks.Chow.gysinHomomorphismOfInvertible_of_not_le` (Stacks 02T8) and
  `Stacks.Chow.gysinHomomorphismOfInvertible_cycleAssociatedToClosedSubscheme` (Stacks 02TB),
  but at a *closed subscheme* of `Y` rather than at `Y` itself, and against the cycle of the
  scheme-theoretic intersection rather than the fundamental class of the base change `D ×_X Y`.
  Passing between the two needs the identity ideal sheaf of `Y` to be identified with `𝟙 Y` and
  the fundamental class to be transported along the isomorphism of Stacks 0B6Y; neither is in
  this repository. The statement is about the Gysin cap operation alone: it mentions no virtual
  normal sheaf and no bivariant class for `D ⟶ X`.
* `Stacks.Chow.GysinCapFundamentalOnDivisor` is Definition 02T8 in the contained case,
  `i^*[Y]_n = c_1(ℒ|_Y) ∩ [Y]_n`, written against the carried first-Chern cap family `cTop`.
  The lemma `Stacks.Chow.gysinHomomorphismOfInvertible_of_le` gives the value as the
  pushforward of `Stacks.Chow.firstChernComponentClass`, which is a *component* rule of Stacks
  02SO and is not connected to any cap product on Chow groups: that connection is
  `chernClassCapOnChow` of Stacks 0B7G, which is not formalized. Again it mentions no bivariant
  class for `D ⟶ X`.
* `Stacks.Chow.VirtualNormalCapFundamentalOnDivisor` is **Stacks 0FBM at full excess** for a
  zero scheme: `c(D ⟶ X, 𝒩) ∩ [Y]_n = c_top(𝒩) ∩ [D ×_X Y]_n`, the case where the conormal
  sheaf of `D ×_X Y ⟶ Y` has rank zero. Stacks 0FBM is proved, as
  `Stacks.Chow.virtualNormalGysinCap_fundamentalChowClass_excess`, but its rank-zero instance
  needs the zero section `D ×_X Y ⟶ N ×_X Y` of the bundle as a closed immersion, which this
  repository does not construct. It is not the conclusion: it is one value of one cap operation,
  on one class, pinned against the same carried `cTop` as the Gysin side.

The first case carries nothing on the side of `c(D ⟶ X, 𝒩)`: its value there is
`Stacks.Chow.virtualNormalGysinCap_fundamentalChowClass`, Stacks 0FBM at vanishing excess, whose
own hypotheses — the injectivity of Stacks 02TY, the value of `ι_* ∘ j^* ∘ C` on a fundamental
class, and a δ-dimension bound — are threaded through quantified over the integral test schemes
of that case.

### Representability

Stacks 02UC is unconditional: its reduction to integral test schemes needs only the
local finiteness of the support of a cycle, which is part of the definition of a cycle. Nothing
about the representability of Chow classes is assumed here.

## References

* [Stacks Project, Tag 0FBN](https://stacks.math.columbia.edu/tag/0FBN)
* [Stacks Project, Tag 0FBK](https://stacks.math.columbia.edu/tag/0FBK)
* [Stacks Project, Tag 0FBM](https://stacks.math.columbia.edu/tag/0FBM)
* [Stacks Project, Tag 0FBQ](https://stacks.math.columbia.edu/tag/0FBQ)
* [Stacks Project, Tag 02QL](https://stacks.math.columbia.edu/tag/02QL)
* [Stacks Project, Tag 02T8](https://stacks.math.columbia.edu/tag/02T8)
* [Stacks Project, Tag 02TB](https://stacks.math.columbia.edu/tag/02TB)
* [Stacks Project, Tag 02SO](https://stacks.math.columbia.edu/tag/02SO)
* [Stacks Project, Tag 02UC](https://stacks.math.columbia.edu/tag/02UC)
* [Stacks Project, Tag 02TY](https://stacks.math.columbia.edu/tag/02TY)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0B73](https://stacks.math.columbia.edu/tag/0B73)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
* [Stacks Project, Tag 0B79](https://stacks.math.columbia.edu/tag/0B79)
* [Stacks Project, Tag 0B7G](https://stacks.math.columbia.edu/tag/0B7G)
* [Stacks Project, Tag 0FA4](https://stacks.math.columbia.edu/tag/0FA4)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Chow

/-! ### The reduction of Stacks 02UC -/

/-- **The reduction step of Stacks 02UC.** Two bivariant classes of the same degree for the same
morphism are equal as soon as they agree on the fundamental class of every integral scheme
locally of finite type over the target. This is the source's "by Stacks 02UC it suffices to show
the identity for `X` integral", applied to the difference of the two classes.

It is unconditional, as Stacks 02UC is. -/
theorem BivariantClass.eq_of_cap_fundamentalChowClass_eq (C : ChowSituation.{u})
    (G : GysinSystem C) {W Y : Scheme.{u}} (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
    (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (f : W ⟶ Y) [LocallyOfFiniteType f]
    (hf : f ≫ sY = sW) (p : ℤ)
    {c d : BivariantClass C G sW sY f hf p}
    (h : ∀ {T : Scheme.{u}} (g : T ⟶ Y) [LocallyOfFiniteType g] [IsIntegral T] (k : ℤ),
      c.cap g k (fundamentalChowClass C (g ≫ sY) k) =
        d.cap g k (fundamentalChowClass C (g ≫ sY) k)) :
    c = d := by
  refine eq_of_sub_eq_zero ?_
  rw [BivariantClass.eq_zero_iff_capsIntegralFundamentalClassesToZero C G sW sY f hf p (c - d)]
  intro T g _ _ k
  rw [BivariantClass.sub_cap, h g k, sub_self]

/-! ### Stacks 0FBN -/

section Divisor

variable (C : ChowSituation.{u}) (G : GysinSystem C) {X NB : Scheme.{u}} (sX : X ⟶ C.S)
  [LocallyOfFiniteType sX] (L : X.Modules)
  [AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L]
  (s : Γ(L, ⊤)) (sNB : NB ⟶ C.S) [LocallyOfFiniteType sNB]
  (q : NB ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme) [LocallyOfFiniteType q]
  (hq : q ≫ (gysinTripleInclusion L s ≫ sX) = sNB)

/-- The cap product with the first Chern class of the virtual normal sheaf on the base change
`D ×_X Y` of the divisor along a test scheme: the operation both classes reduce to on an integral
test scheme contained in `D`.

It is carried rather than constructed because the cap product with the Chern classes is
`chernClassCapOnChow` of Stacks 0B7G, which is not formalized; only its degree, one, enters below,
and that is fixed by the typing. -/
abbrev DivisorTopChernCapFamily : Type (u + 1) :=
  ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] (n : ℤ),
    chowGroup C (pullback.fst (gysinTripleInclusion L s) g ≫
        (gysinTripleInclusion L s ≫ sX)) n →+
      chowGroup C (pullback.fst (gysinTripleInclusion L s) g ≫
        (gysinTripleInclusion L s ≫ sX)) (n - 1)

/-- **The value of the Gysin homomorphism on the fundamental class of an integral test scheme
not contained in the divisor.** If the section pulled back to an integral `Y` does not vanish
identically — equivalently if `Y ⟶ X` does not factor through `i` — then
`i^*[Y]_n = [D ×_X Y]_{n-1}`.

This is the source's "which is true by definition for the Gysin homomorphism". The component
formula behind it is proved, as Stacks 02T8 and Stacks 02TB, but at a closed subscheme of `Y`
and against the cycle of a scheme-theoretic intersection; see the implementation notes. The
statement is about the Gysin cap operation alone. -/
def GysinCapFundamentalOffDivisor : Prop :=
  ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] [IsIntegral Y] (n : ℤ),
    (¬ ∃ h : Y ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme,
      h ≫ gysinTripleInclusion L s = g) →
    gysinBivariantCap C G sX L s g n (fundamentalChowClass C (g ≫ sX) n) =
      fundamentalChowClass C
        (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) (n - 1)

/-- **The value of the Gysin homomorphism on the fundamental class of an integral test scheme
contained in the divisor.** If the section pulled back to an integral `Y` vanishes identically
then `i^*[Y]_n = c_1(ℒ|_Y) ∩ [Y]_n`.

This is Definition 02T8 in the contained case. The lemma
`Stacks.Chow.gysinHomomorphismOfInvertible_of_le` gives the value as a pushforward of the
component rule of Stacks 02SO, which is not connected to any cap product on Chow groups — that
is Stacks 0B7G, which is not formalized — so the value is carried against the family `cTop`. -/
def GysinCapFundamentalOnDivisor (cTop : DivisorTopChernCapFamily C sX L s) : Prop :=
  ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] [IsIntegral Y] (n : ℤ),
    (∃ h : Y ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme,
      h ≫ gysinTripleInclusion L s = g) →
    gysinBivariantCap C G sX L s g n (fundamentalChowClass C (g ≫ sX) n) =
      cTop g n (fundamentalChowClass C
        (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) n)

variable (E : BivariantClass C G sNB sX (q ≫ gysinTripleInclusion L s)
    (comp_comp_structureMorphism_eq hq rfl) 0)
  (P : VirtualNormalBundleProjection (gysinTripleInclusion L s) q 1)
  (hdesc : FlatPullbackDescends C)

/-- **Stacks 0FBM at full excess for a zero scheme.** On an integral test scheme contained in the
divisor the conormal sheaf of `D ×_X Y ⟶ Y` has rank zero, the excess normal sheaf is all of
`𝒩`, and Stacks 0FBM reads `c(D ⟶ X, 𝒩) ∩ [Y]_n = c_top(𝒩) ∩ [D ×_X Y]_n`.

Stacks 0FBM is proved, as
`Stacks.Chow.virtualNormalGysinCap_fundamentalChowClass_excess`, but its rank-zero instance asks
for the zero section `D ×_X Y ⟶ N ×_X Y` of the bundle as a closed immersion over `D ×_X Y`,
which this repository does not construct; so this one value is carried. It is pinned against the
same family `cTop` as the Gysin side. -/
def VirtualNormalCapFundamentalOnDivisor (cTop : DivisorTopChernCapFamily C sX L s)
    (c : BivariantClass C G (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s) rfl
      ((1 : ℕ) : ℤ)) : Prop :=
  ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] [IsIntegral Y] (n : ℤ),
    (∃ h : Y ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme,
      h ≫ gysinTripleInclusion L s = g) →
    c.cap g n (fundamentalChowClass C (g ≫ sX) n) =
      cTop g n (fundamentalChowClass C
        (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) n)

/-- **The first case of the proof of Stacks 0FBN.** On an integral test scheme `Y` not contained
in the divisor, the Gysin cap operation and the cap operation of `c(D ⟶ X, 𝒩)` both send `[Y]_n`
to the fundamental class of `D ×_X Y` in degree `n - 1`.

The Gysin value is the carried `Stacks.Chow.GysinCapFundamentalOffDivisor`; the value of
`c(D ⟶ X, 𝒩)` is Stacks 0FBM at vanishing excess,
`Stacks.Chow.virtualNormalGysinCap_fundamentalChowClass`, whose three hypotheses — the
injectivity of Stacks 02TY, the value of `ι_* ∘ j^* ∘ C` on the fundamental class, and the
δ-dimension bound — appear here as `hinj`, `hcone` and `hdim`. -/
@[stacks 0FBN "the case of a test scheme not contained in D: the value of the virtual
normal class there, which is Tag 0FBM at vanishing excess. The Gysin side of this
case is carried; see `Stacks.Chow.gysinBivariantClass_eq_virtualNormalGysinClass`"]
theorem gysinBivariantCap_eq_virtualNormalGysinCap_of_offDivisor
    (hinj : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C (gysinTripleInclusion L s ≫ sX) sNB (gysinTripleInclusion L s) q hq
          1 P.flat P.relativeDimension hdesc g k))
    {c : BivariantClass C G (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s) rfl
      ((1 : ℕ) : ℤ)}
    (hc : IsVirtualNormalGysinClass C G (gysinTripleInclusion L s ≫ sX) sX sNB
      (gysinTripleInclusion L s) rfl q hq 1 0 E
      (bundleFlatPullback C (gysinTripleInclusion L s ≫ sX) sNB (gysinTripleInclusion L s) q hq 1
        P.flat P.relativeDimension hdesc) P c)
    (hoff : GysinCapFundamentalOffDivisor C G sX L s)
    {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] [IsIntegral Y] (n : ℤ)
    (hY : ¬ ∃ h : Y ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme,
      h ≫ gysinTripleInclusion L s = g)
    (hdim : schemeDeltaDimension C
        (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) ≤
      ((n - ((1 : ℕ) : ℤ) : ℤ) : EInt))
    (hcone : chowGroupDegreeEquiv C
        (pullback.fst (q ≫ gysinTripleInclusion L s) g ≫ sNB)
        (by omega : n - (0 : ℤ) = (n - ((1 : ℕ) : ℤ)) + ((1 : ℕ) : ℤ))
        (E.cap g n (fundamentalChowClass C (g ≫ sX) n)) =
      fundamentalChowClass C (pullback.fst (q ≫ gysinTripleInclusion L s) g ≫ sNB)
        ((n - ((1 : ℕ) : ℤ)) + ((1 : ℕ) : ℤ))) :
    gysinBivariantCap C G sX L s g n (fundamentalChowClass C (g ≫ sX) n) =
      c.cap g n (fundamentalChowClass C (g ≫ sX) n) := by
  rw [hoff g n hY]
  exact (virtualNormalGysinCap_fundamentalChowClass C G (gysinTripleInclusion L s ≫ sX) sX sNB
    (gysinTripleInclusion L s) rfl q hq 1 E P hdesc hinj hc g n hdim hcone).symm

/-- **Stacks 0FBN.** Let `(S, δ)` be the base situation of chapter 42, let `X` be locally of
finite type over `S` and let `(ℒ, s, i : D ⟶ X)` be a triple as in Definition 02T8. Let
`𝒩 = i^*ℒ`, a virtual normal sheaf of rank one for `D` in `X`. Then the Gysin homomorphism `i^*`,
viewed as an element of `A^1(D ⟶ X)` by Stacks 0B79, is the bivariant class `c(D ⟶ X, 𝒩)` of
Stacks 0FBK.

The proof is the source's: by Stacks 02UC it is enough to compare the two classes on the
fundamental class of every integral test scheme, and there the two cases of the source are
`Stacks.Chow.gysinBivariantCap_eq_virtualNormalGysinCap_of_offDivisor` and the pair of carried
values `hon`, `hvn` on an integral test scheme contained in `D`. See the implementation notes
for what is carried in each case. -/
@[stacks 0FBN "the Gysin homomorphism i^* of a triple (L, s, i : D -> X) as in Definition
02T8 and the virtual normal class c(D -> X, i^*L) of Tag 0FBK agree in A^1(D -> X). Both
classes are the ones CHARACTERIZED by their tags (Tag 0B79 via `IsGysinBivariantClass`, Tag
0FBK via `IsVirtualNormalGysinClass`), neither being constructed here; the virtual normal
sheaf is data with its module identified with i^*L, the canonical surjection C_{D/X} = (i^*L)^v
being absent. THE TAG IS NOT FULLY CLOSED. Proved: the Tag 02UC reduction to integral test
schemes, and for a test scheme NOT contained in D the value of the virtual normal class, which
is Tag 0FBM at vanishing excess. CARRIED: the value of the Gysin homomorphism on a
fundamental class in BOTH cases (Definition 02T8 and Tag 02TB are proved only at a closed
subscheme of the test scheme against an intersection cycle, not at the fundamental class of
the base change D x_X Y), and the value of the virtual normal class in the case Y contained in
D (Tag 0FBM at full excess). THE CONTAINED CASE IS THEREFORE DOCUMENTED BUT NOT DISCHARGED.
Also carried: Tag 02TY injectivity and Tag 02S1 descent. The Tag 02UC used for the
reduction to integral test schemes is unconditional"]
theorem gysinBivariantClass_eq_virtualNormalGysinClass
    (cTop : DivisorTopChernCapFamily C sX L s)
    (hinj : ∀ {T : Scheme.{u}} (g : T ⟶ X) [LocallyOfFiniteType g] (k : ℤ),
      Function.Injective
        (bundleFlatPullback C (gysinTripleInclusion L s ≫ sX) sNB (gysinTripleInclusion L s) q hq
          1 P.flat P.relativeDimension hdesc g k))
    (_hbundle : P.normalBundle.bundle =
      (Scheme.Modules.pullback (gysinTripleInclusion L s)).obj L)
    {gys c : BivariantClass C G (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s) rfl
      ((1 : ℕ) : ℤ)}
    (hgys : IsGysinBivariantClass C G sX L s gys)
    (hc : IsVirtualNormalGysinClass C G (gysinTripleInclusion L s ≫ sX) sX sNB
      (gysinTripleInclusion L s) rfl q hq 1 0 E
      (bundleFlatPullback C (gysinTripleInclusion L s ≫ sX) sNB (gysinTripleInclusion L s) q hq 1
        P.flat P.relativeDimension hdesc) P c)
    (hoff : GysinCapFundamentalOffDivisor C G sX L s)
    (hon : GysinCapFundamentalOnDivisor C G sX L s cTop)
    (hvn : VirtualNormalCapFundamentalOnDivisor C G sX L s cTop c)
    (hdim : ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] (n : ℤ),
      (¬ ∃ h : Y ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme,
      h ≫ gysinTripleInclusion L s = g) →
      schemeDeltaDimension C
          (pullback.fst (gysinTripleInclusion L s) g ≫ (gysinTripleInclusion L s ≫ sX)) ≤
        ((n - ((1 : ℕ) : ℤ) : ℤ) : EInt))
    (hcone : ∀ {Y : Scheme.{u}} (g : Y ⟶ X) [LocallyOfFiniteType g] (n : ℤ),
      (¬ ∃ h : Y ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme,
      h ≫ gysinTripleInclusion L s = g) →
      chowGroupDegreeEquiv C (pullback.fst (q ≫ gysinTripleInclusion L s) g ≫ sNB)
          (by omega : n - (0 : ℤ) = (n - ((1 : ℕ) : ℤ)) + ((1 : ℕ) : ℤ))
          (E.cap g n (fundamentalChowClass C (g ≫ sX) n)) =
        fundamentalChowClass C (pullback.fst (q ≫ gysinTripleInclusion L s) g ≫ sNB)
          ((n - ((1 : ℕ) : ℤ)) + ((1 : ℕ) : ℤ))) :
    gys = c := by
  refine BivariantClass.eq_of_cap_fundamentalChowClass_eq C G
    (gysinTripleInclusion L s ≫ sX) sX (gysinTripleInclusion L s) rfl ((1 : ℕ) : ℤ) ?_
  intro Y g _ _ n
  rw [hgys g n (fundamentalChowClass C (g ≫ sX) n)]
  by_cases hY : ∃ h : Y ⟶ (Stacks.Divisors.zeroScheme X L s).subscheme,
      h ≫ gysinTripleInclusion L s = g
  · rw [hon g n hY, hvn g n hY]
  · exact gysinBivariantCap_eq_virtualNormalGysinCap_of_offDivisor C G sX L s sNB q hq E P hdesc
      hinj hc hoff g n hY (hdim g n hY) (hcone g n hY)

end Divisor

end Stacks.Chow

end
