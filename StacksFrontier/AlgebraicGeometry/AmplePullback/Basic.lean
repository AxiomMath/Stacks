module

public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Basic
public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.ClosedImmersion

/-!
# Stacks Tag 0B3E: ampleness pulls back

Stacks Tag 0B3E says that for `L` an ample invertible `𝒪_X`-module and `i : X' ⟶ X` a morphism of
schemes satisfying at least one of

1. `i` quasi-compact and an immersion,
2. `X'` quasi-compact and `i` an immersion,
3. `i` quasi-compact and a homeomorphism onto its image,
4. `X'` quasi-compact and a homeomorphism onto its image,

the pullback `i^* L` is ample on `X'`.

Two cases are proved here **unconditionally**, by a route the source does not use: the case of an
affine `X'` and the case of an affine morphism `i`, which between them cover every closed
immersion. The general case is then proved on a single premise, which is isolated, stated, and
named below; it is not Stacks Tag 01Q3, and that is the point of this file.

## Main definitions

* `Stacks.AmplePullback.BasicOpenIsPowNonvanishing`: **the one premise the general case still
  stands on.** Every basic open of an affine `X_s` is itself an `X_t`, for `t` a global section of
  some positive tensor power of `L`. This is the consequence of Stacks Tag 01PW that clause (3) of
  Stacks Tag 01Q3 is built out of; see "The premise, and why it is the right one".

## Main results

* `Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection`: `X'_{i^* s} = i^{-1}(X_s)` as open
  subsets, which is Stacks Tag 0H78 in the form used throughout this file.
* `Stacks.AmplePullback.isAmple_modulePullback_of_isAffine`: **Stacks Tag 0B3E for an affine `X'`,
  with no hypothesis on `i` at all.** Unconditional.
* `Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`: **Stacks Tag 0B3E for an affine
  morphism.** Unconditional.
* `Stacks.AmplePullback.isAmple_modulePullback_of_isClosedImmersion`: the case of a closed
  immersion, which is the above since a closed immersion is affine. Unconditional.
* `Stacks.AmplePullback.isBasisNonvanishing_of_isAmple`: **clause (1) implies clause (3) of Stacks
  Tag 01Q3**, on the premise `BasicOpenIsPowNonvanishing`. Three lines; the premise is the whole
  content.
* `Stacks.AmplePullback.isAmple_modulePullback`: **Stacks Tag 0B3E in the shape of its statement**,
on
  that one premise.
* `Stacks.AmplePullback.amplePullbackGap_of_basicOpenIsPowNonvanishing` and
  `Stacks.AmplePullback.isRelativelyAmple_of_hasRelativeTwistImmersion`: the same narrowing carried
  on to `Stacks.RelativeVeryAmple.AmplePullbackGap` and to the content of Stacks Tag 01VN, which
  `Stacks.NonvanishingPullback` had reduced to clause (1) implies (3) of Stacks Tag 01Q3.

## The unconditional cases, and why they are available

Ampleness of `L` hands out, through each point `x` of `X`, an affine `X_s` for `s` a global
section of a positive tensor power. Pulling `s` back gives a global section `i^* s` of the same
power of `i^* L` whose nonvanishing locus is `i^{-1}(X_s)` — Stacks Tag 0H78, proved
as `Stacks.NonvanishingPullback.sectionPullbackCompatible`. So the opens `X'_{i^* s}` always cover
`X'`, for any `i` whatever, and ampleness of `i^* L` is exactly the assertion that one may be
chosen **affine** through each point. Hence:

* if `i` is an affine morphism, `i^{-1}(X_s)` is affine outright, by
  `AlgebraicGeometry.IsAffineOpen.preimage`;
* if `X'` is affine, `X'_{i^* s}` is contained in the affine open `⊤` and is therefore affine by
  Stacks Tag 01PV, through
  `Stacks.NonvanishingPullback.isAffineOfLeAffine`.

Neither case needs the source's reduction to case (4), its basis argument, or any hypothesis on
the topology of `i`. The second in particular has no hypothesis on `i`, and is not a case of the
source statement at all: an arbitrary morphism from an affine scheme need be neither an immersion
nor injective.

## The premise, and why it is the right one

For a general `i` the source's route is forced, and its one input is clause (3) of Stacks Tag
01Q3: the opens `X_s` form a basis for the topology of `X`. Everything else is discharged —
`Stacks.AmpleLocallyClosed.compactSpace_and_isEmbedding_iff` collapses the four hypotheses to
case (4), `Stacks.AmpleLocallyClosed.isBasisNonvanishing_pullback` transports the basis along the
embedding, and Stacks Tags 01PX and 01PV turn the transported basis back into ampleness.

Clause (3) of Tag 01Q3 is proved in the source only through clause (2), hence through the open
immersion into `Proj Γ_*(X, L)`; of what that route needs this repository has only Tag 01Q2
(`Stacks.AlgebraicGeometry.ProjAmpleTwist.exists_isAmple_pullback_twistingSheaf`), which is the
implication out of `Proj` rather than the open immersion into it, and neither Tag 01Q1 nor Tag
01PZ nor the graded structure both need. **That is not the obstruction.** Given ampleness, the
basis statement follows from a single much smaller fact, and
`Stacks.AmplePullback.isBasisNonvanishing_of_isAmple` is the proof: an ample `L` already puts an
affine `X_s` through every point, the basic opens of an affine open are a basis of it, so the only
thing missing is that a basic open of an affine `X_s` is again some `X_t`. That is
`BasicOpenIsPowNonvanishing`, and it is the consequence of Stacks Tag 01PW — Properties of
Schemes, Lemma 28.17.2 — that the source itself uses for this purpose:

> for `X` quasi-compact, `s` a global section of `L ^⊗ d` and `g` a section of `𝒪_X` over `X_s`,
> there are `m ≥ 1` and a global section `t` of `L ^⊗ (m d)` with `t|_{X_s} = g • s^m|_{X_s}`.

Given Tag 01PW the premise follows: `X_t ⊓ X_s` is the basic open of `g`, because `s` trivializes
`L ^⊗ d` on `X_s` (`Stacks.NonvanishingTrivialize.bijective_smul`), and `X_{t · s} = X_t ⊓ X_s`
by `Stacks.SectionProduct.nonvanishingOpen_mul`, so `t · s` is the global section the premise
asks for. One piece of bookkeeping is owed there and is not done here: that product lemma is
stated over `Stacks.TensorPowers.natTensorPow` and the sections of the graded ring, while
ampleness is stated over `Stacks.Ample.tensorPowModule`, so the transfer goes through
`Stacks.PowerFamilyBridge`. Tag 01PW itself has no attachment anywhere in either tree, and its
proof is a finite-affine-cover gluing argument rather than anything about `Proj`.

So the honest account of where Tag 0B3E stands is: **one elementary gluing lemma**, not a graded
ring and a homogeneous spectrum.

## Implementation notes

The nonvanishing locus is `Stacks.AmpleTheory.powNonvanishingOpen`, the bundled `X_s` of the
positive tensor powers `Stacks.Ample.tensorPowModule` of Stacks Tag 01CU; ampleness is
`Stacks.Ample.IsAmple` and invertibility `Stacks.Ample.IsInvertibleModule`. Invertibility of the
pullback is Stacks Tag 0B8L as an instance, so it is never written down. The pullback of a section
is `Stacks.NonvanishingPullback.pullbackPowSection`.

`Stacks.AmplePullback.powNonvanishingOpen_pullbackPowSection` upgrades
`Stacks.NonvanishingPullback.sectionPullbackCompatible` from an equality of sets to an equality of
opens, which is what `AlgebraicGeometry.IsAffineOpen.preimage` needs; the two sides are equal on
the nose once the carriers are, by `TopologicalSpace.Opens.ext`.

## References

* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 0B8L](https://stacks.math.columbia.edu/tag/0B8L)

## What is not done

**No Stacks attribute is attached.** The covering set of Tag 0B3E is the single assertion of the
statement — the four-way disjunction — and the general case is still conditional, so by the
covering-set
rule the tag is not earned by the unconditional special cases below.

**Stacks Tag 01PW is not proved.** It is the only missing input, and
`Stacks.AmplePullback.BasicOpenIsPowNonvanishing` is the exact consequence of it that is needed.
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory

universe u

namespace Stacks.AmplePullback

section Pullback

variable {X' X : Scheme.{u}} (i : X' ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-! ### The pullback of a nonvanishing locus, as an open subset -/

/-- **`X'_{i^* s} = i^{-1}(X_s)` as open subsets of `X'`.** This is Stacks Tag 0H78: the equality
of sets `Stacks.NonvanishingPullback.sectionPullbackCompatible`, stated as an equality of opens. -/
theorem powNonvanishingOpen_pullbackPowSection (n : ℕ)
    (s : Γ(tensorPowModule X L (n : ℤ), ⊤)) :
    powNonvanishingOpen X' (Stacks.AmpleLocallyClosed.pullbackModule i L) n
        (Stacks.NonvanishingPullback.pullbackPowSection i L n s) =
      i ⁻¹ᵁ powNonvanishingOpen X L n s :=
  Opens.ext (Stacks.NonvanishingPullback.sectionPullbackCompatible i L n s)

/-- Every point of `X'` lies in the pullback of an affine nonvanishing locus, for any morphism
`i` whatever: this is ampleness of `L` at the image point together with Stacks Tag 0H78. -/
theorem exists_mem_powNonvanishingOpen_pullbackPowSection (hL : IsAmple X L) (x' : X') :
    ∃ n : ℕ, 1 ≤ n ∧ ∃ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
      IsAffineOpen (powNonvanishingOpen X L n s) ∧
        x' ∈ powNonvanishingOpen X' (Stacks.AmpleLocallyClosed.pullbackModule i L) n
          (Stacks.NonvanishingPullback.pullbackPowSection i L n s) := by
  obtain ⟨n, hn, s, haff, hxs⟩ :=
    IsAmple.exists_affine_nonvanishingOpen X L hL (i.base x')
  refine ⟨n, hn, s, haff, ?_⟩
  rw [powNonvanishingOpen_pullbackPowSection i L n s]
  exact hxs

/-- Ampleness of the pullback follows from compactness of `X'` and affineness of each pulled-back
affine nonvanishing locus. -/
private theorem isAmple_modulePullback_of_forall_isAffineOpen (hc : CompactSpace X')
    (hL : IsAmple X L)
    (h : ∀ n : ℕ, 1 ≤ n → ∀ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
      IsAffineOpen (powNonvanishingOpen X L n s) →
        IsAffineOpen (powNonvanishingOpen X' (Stacks.AmpleLocallyClosed.pullbackModule i L) n
          (Stacks.NonvanishingPullback.pullbackPowSection i L n s))) :
    IsAmple X' (Stacks.AmpleLocallyClosed.pullbackModule i L) := by
  refine (isAmple_iff_forall_affine_nonvanishingOpen X' _).mpr ⟨hc, fun x' => ?_⟩
  obtain ⟨n, hn, s, haff, hx'⟩ := exists_mem_powNonvanishingOpen_pullbackPowSection i L hL x'
  exact ⟨n, hn, _, h n hn s haff, hx'⟩

/-! ### Stacks Tag 0B3E for an affine source -/

/-- **Stacks Tag 0B3E for an affine `X'`, with no hypothesis on `i`.** The pullback of an ample
invertible module along *any* morphism from an affine scheme is ample.

Every `X'_{i^* s}` is contained in the affine open `⊤`, hence is affine by Stacks Tag
01PV in the form `Stacks.NonvanishingPullback.isAffineOfLeAffine`; and the `X'_{i^* s}` cover `X'`
because the `X_s` cover `X`. No reduction to case (4) of the source and no basis argument is
involved. -/
theorem isAmple_modulePullback_of_isAffine [IsAffine X'] (hL : IsAmple X L) :
    IsAmple X' (Stacks.AmpleLocallyClosed.pullbackModule i L) := by
  refine isAmple_modulePullback_of_forall_isAffineOpen i L inferInstance hL fun n hn s _ => ?_
  exact Stacks.NonvanishingPullback.isAffineOfLeAffine X' _ n hn _ ⊤
    (isAffineOpen_top X') le_top

/-! ### Stacks Tag 0B3E for an affine morphism -/

/-- **Stacks Tag 0B3E for an affine morphism `i`.** The preimage of an affine open under an affine
morphism is affine, so the affine `X_s` supplied by ampleness pull back to affine `X'_{i^* s}`
directly. Quasi-compactness of `X'` comes from quasi-compactness of `i` — every affine morphism is
quasi-compact — and of `X`, which ampleness of `L` provides. -/
theorem isAmple_modulePullback_of_isAffineHom [IsAffineHom i] (hL : IsAmple X L) :
    IsAmple X' (Stacks.AmpleLocallyClosed.pullbackModule i L) := by
  refine isAmple_modulePullback_of_forall_isAffineOpen i L
    (Stacks.AmpleLocallyClosed.compactSpace_of_quasiCompact i inferInstance hL.compactSpace) hL
    fun n hn s haff => ?_
  rw [powNonvanishingOpen_pullbackPowSection i L n s]
  exact haff.preimage i

/-- **Stacks Tag 0B3E for a closed immersion.** A closed immersion is an affine morphism, so this
is `Stacks.AmplePullback.isAmple_modulePullback_of_isAffineHom`. It is case (1) of the source
statement restricted to closed immersions, and it is unconditional. -/
theorem isAmple_modulePullback_of_isClosedImmersion [IsClosedImmersion i] (hL : IsAmple X L) :
    IsAmple X' (Stacks.AmpleLocallyClosed.pullbackModule i L) :=
  isAmple_modulePullback_of_isAffineHom i L hL

end Pullback

/-! ### The premise of the general case -/

section Premise

variable (X : Scheme.{u}) (L : X.Modules) [IsInvertibleModule X L]

/-- **Every basic open of an affine `X_s` is an `X_t`.** This is the consequence of Stacks Tag
01PW that clause (3) of Stacks Tag 01Q3 is built from, and the single premise the general case of
Stacks Tag 0B3E still stands on in this repository.

Given Tag 01PW — a section of `𝒪_X` over `X_s` extends to a global section of `L ^⊗ (m d)` after
multiplication by `s^m` — this follows by taking the product with `s` itself, since
`X_{t · s} = X_t ⊓ X_s` and `X_t ⊓ X_s` is the basic open of the extended function. -/
def BasicOpenIsPowNonvanishing : Prop :=
  ∀ (n : ℕ), 1 ≤ n → ∀ s : Γ(tensorPowModule X L (n : ℤ), ⊤),
    IsAffineOpen (powNonvanishingOpen X L n s) →
      ∀ g : Γ(X, powNonvanishingOpen X L n s), ∃ m : ℕ, 1 ≤ m ∧
        ∃ t : Γ(tensorPowModule X L (m : ℤ), ⊤),
          powNonvanishingOpen X L m t = X.basicOpen g

/-- **Clause (1) implies clause (3) of Stacks Tag 01Q3**, on the premise
`Stacks.AmplePullback.BasicOpenIsPowNonvanishing`: if `L` is ample then the opens `X_s`, for `s` a
global section of a positive tensor power, form a basis for the topology of `X`.

The source proves this only through clause (2) and the open immersion into `Proj Γ_*(X, L)`. This
proof uses neither. Ampleness already puts an *affine* `X_s` through the given point `x`; the basic
opens of an affine open form a basis of it, so some `X.basicOpen g` with `g` a section over that
`X_s` sits between `x` and the prescribed open `U`; and the premise says that basic open is itself
an `X_t`. -/
theorem isBasisNonvanishing_of_isAmple (h : BasicOpenIsPowNonvanishing X L) (hL : IsAmple X L) :
    IsBasisNonvanishing X L := by
  intro x U hx
  obtain ⟨n, hn, s, haff, hxs⟩ := IsAmple.exists_affine_nonvanishingOpen X L hL x
  obtain ⟨g, hgU, hxg⟩ := haff.exists_basicOpen_le (V := U) ⟨x, hx⟩ hxs
  obtain ⟨m, hm, t, ht⟩ := h n hn s haff g
  exact ⟨m, hm, t, ht ▸ hxg, ht ▸ hgU⟩

end Premise

/-! ### Stacks Tag 0B3E -/

section Main

variable {X' X : Scheme.{u}} (i : X' ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- **Stacks Tag 0B3E**, in the shape of the tagged statement, on the single premise
`Stacks.AmplePullback.BasicOpenIsPowNonvanishing`.

Every other input of the source proof is a theorem: the four-way disjunction collapses to case (4)
by `Stacks.AmpleLocallyClosed.compactSpace_and_isEmbedding_iff`, the nonvanishing loci pull back by
Stacks Tag 0H78 (`Stacks.NonvanishingPullback.sectionPullbackCompatible`), the basis transports
along the embedding by `Stacks.AmpleLocallyClosed.isBasisNonvanishing_pullback`, and Stacks Tags
01PX and 01PV return ampleness. -/
theorem isAmple_modulePullback (hL : IsAmple X L)
    (hi : (QuasiCompact i ∧ IsImmersion i) ∨ (CompactSpace X' ∧ IsImmersion i) ∨
      (QuasiCompact i ∧ Topology.IsEmbedding i) ∨
      (CompactSpace X' ∧ Topology.IsEmbedding i))
    (h : BasicOpenIsPowNonvanishing X L) :
    IsAmple X' (Stacks.AmpleLocallyClosed.pullbackModule i L) :=
  Stacks.NonvanishingPullback.isAmple_modulePullback' i L hL hi
    (isBasisNonvanishing_of_isAmple X L h hL)

end Main

/-! ### The same premise for the rest of the cluster -/

/-- **`Stacks.RelativeVeryAmple.AmplePullbackGap` on the premise
`Stacks.AmplePullback.BasicOpenIsPowNonvanishing`.** `Stacks.NonvanishingPullback` reduced this gap
to clause (1) implies (3) of Stacks Tag 01Q3; this reduces it further to the one basic-open
statement. -/
theorem amplePullbackGap_of_basicOpenIsPowNonvanishing
    (h : ∀ (B : Scheme.{u}) (N : B.Modules) [IsInvertibleModule B N],
      IsAmple B N → BasicOpenIsPowNonvanishing B N) :
    Stacks.RelativeVeryAmple.AmplePullbackGap.{u} := by
  refine Stacks.NonvanishingPullback.amplePullbackGap_of_isBasisNonvanishing ?_
  exact fun B N _ hN => isBasisNonvanishing_of_isAmple B N (h B N hN) hN

/-- **The content of Stacks Tag 01VN on the premise
`Stacks.AmplePullback.BasicOpenIsPowNonvanishing`.** Relative ampleness is inherited by an
immersion over the base, given the one basic-open statement and nothing else. -/
theorem isRelativelyAmple_of_hasRelativeTwistImmersion
    (h : ∀ (B : Scheme.{u}) (N : B.Modules) [IsInvertibleModule B N],
      IsAmple B N → BasicOpenIsPowNonvanishing B N)
    {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules) [IsInvertibleModule Y M]
    (hf : QuasiCompact f) (hr : Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f M) :
    Stacks.RelativeAmple.IsRelativelyAmple f M := by
  refine Stacks.NonvanishingPullback.isRelativelyAmple_of_hasRelativeTwistImmersion ?_ f M hf hr
  exact fun B N _ hN => isBasisNonvanishing_of_isAmple B N (h B N hN) hN

end Stacks.AmplePullback

end
