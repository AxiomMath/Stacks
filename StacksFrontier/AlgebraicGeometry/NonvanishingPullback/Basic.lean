module

public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.RelativeVeryAmple.Basic
public import StacksFrontier.AlgebraicGeometry.NonvanishingAffineIntersection.Basic
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Stacks Tag 01VN: two of the three premises its proof was left standing on, discharged

`StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/Basic.lean` proves the content of Stacks Tag
01VN — relative ampleness is inherited by an immersion over the base — modulo one hypothesis,
`Stacks.RelativeVeryAmple.AmplePullbackGap`, which is Stacks Tag 0B3E; and
`Stacks.RelativeVeryAmple.amplePullbackGap_of_premises` reduces that hypothesis to exactly three
premises of `Stacks.AmpleLocallyClosed.isAmple_modulePullback`.

**This file discharges two of the three, leaving one.**

* `hsect`, **Stacks Tag 0H78**: the compatibility of nonvanishing loci with pullback, which the
  sibling result `Stacks.NonvanishingPullback.preimage_nonvanishingLocus` (`Nonvanishing.lean` of
  this directory) now proves for an
  arbitrary module and an arbitrary morphism of schemes. Specialising it to the tensor powers of
  an invertible module and reading it through
  `Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso` produces the section maps
  `Stacks.AmpleLocallyClosed.SectionPullbackCompatible` asks for, so they are no longer a
  parameter.
* `haff`, the **Stacks Tag 01PV** consequence Stacks Tag 01PX consumes: this needed no new
  mathematics at all. Tag 01PV is proved and tagged, as
  `Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen`, and
  `Stacks.NonvanishingPullback.isAffineOfLeAffine` is the three-line derivation of the consequence
  from it.

## Main definitions

* `Stacks.NonvanishingPullback.pullbackPowSection`: the pullback of a global section of `L ^⊗ n`,
  read as a global section of `(i^* L) ^⊗ n`. This is the `φ` that
  `Stacks.AmpleLocallyClosed.isAmple_modulePullback` takes as a parameter, now constructed.

## Main results

* `Stacks.NonvanishingPullback.sectionPullbackCompatible`: **Stacks Tag 0H78 in the form Stacks Tag
  0B3E consumes it.** `X'_{i^* s} = i^{-1}(X_s)` for every positive tensor power.
* `Stacks.NonvanishingPullback.isAffineOfLeAffine`: **the Stacks Tag 01PV consequence**, from the
  statement of Tag 01PV.
* `Stacks.NonvanishingPullback.isAmple_modulePullback` and `isAmple_modulePullback'`: **Stacks Tag
  0B3E** on two premises and then on one.
* `Stacks.NonvanishingPullback.amplePullbackGap_of_isBasisNonvanishing`:
  `Stacks.RelativeVeryAmple.AmplePullbackGap` on that one premise.
* `Stacks.NonvanishingPullback.isRelativelyAmple_of_hasRelativeTwistImmersion`: **the content of
  Stacks Tag 01VN** on that one premise, obtained by feeding the above to
  `Stacks.RelativeVeryAmple.isRelativelyAmple_of_hasRelativeTwistImmersion`.

## What is still missing, named

One premise remains, and it is not discharged here: `hbasis`, **Stacks Tag 01Q3, (1) ⟹ (3)**, i.e.
`Stacks.AmpleTheory.IsBasisNonvanishing X L` for every ample invertible `L`. It is not a gap in
the repository any more — `Stacks.SectionExtension.isBasisNonvanishing_of_isAmple`
(`../SectionExtension/AmpleConsumers.lean`) proves it from ampleness alone, by way of the
surjectivity half of Stacks Tag 01PW — but no declaration below applies it, so the theorems here
still carry it as a hypothesis. `StacksFrontier/AlgebraicGeometry/AmpleTheory/Basic.lean` has only
the weaker forms: the structure sheaf
(`Stacks.AmpleTheory.isBasisNonvanishing_unitModule`) and a module with a nowhere-vanishing
global basis in every tensor degree. The route the source takes is a different one — the open
immersion into `Proj Γ_*(X, L)`, which needs Stacks Tags 01Q1 and 01Q2 and a graded ring
structure on the section ring — and it remains unavailable: of those three only Tag 01Q2 has an
attachment (`Stacks.AlgebraicGeometry.ProjAmpleTwist.exists_isAmple_pullback_twistingSheaf`), and
it runs the other way — from an open immersion into `Proj` to ampleness of a twist — so it gives
the source's argument nothing; Tag 01Q1 and the graded structure are absent.

And Stacks Tag 01VN itself does not close here, nor would it close if `hbasis` were discharged:
its statement quantifies over the projective bundle of a module — Stacks Tag 01OB — which has no
library form; see
"What is not done" in `StacksFrontier/AlgebraicGeometry/RelativeVeryAmple/Basic.lean`.

## References

* [Stacks Project, Tag 01VN](https://stacks.math.columbia.edu/tag/01VN)
* [Stacks Project, Tag 0B3E](https://stacks.math.columbia.edu/tag/0B3E)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01PV](https://stacks.math.columbia.edu/tag/01PV)
* [Stacks Project, Tag 01PX](https://stacks.math.columbia.edu/tag/01PX)
* [Stacks Project, Tag 01Q3](https://stacks.math.columbia.edu/tag/01Q3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite
open RingedSpaceModuleAdjunction
open Stacks.Ample Stacks.AmpleTheory
open scoped Stacks.ModuleStalk

universe u

namespace Stacks.NonvanishingPullback

variable {X' X : Scheme.{u}} (i : X' ⟶ X) (L : X.Modules) [IsInvertibleModule X L]

/-- **The pullback of a global section of a tensor power**, read as a global section of the tensor
power of the pullback: the section is pulled back by
`Stacks.NonvanishingPullback.pullbackGlobalSection` and then transported along
`Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso`, `i^* (L ^⊗ n) ≅ (i^* L) ^⊗ n`. -/
def pullbackPowSection (n : ℕ) (s : Γ(tensorPowModule X L (n : ℤ), ⊤)) :
    Γ(tensorPowModule X' (Stacks.AmpleLocallyClosed.pullbackModule i L) (n : ℤ), ⊤) :=
  ConcreteCategory.hom (Scheme.Modules.Hom.app
      (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso i L n).hom ⊤)
    (pullbackGlobalSection i (tensorPowModule X L (n : ℤ)) s)

/-- **Stacks Tag 0H78 in the form Stacks Tag 0B3E consumes it.** The nonvanishing locus of the
pulled-back section of a tensor power is the inverse image of the nonvanishing locus upstairs.

`Stacks.AmpleLocallyClosed.SectionPullbackCompatible` was a premise precisely because no such
family of maps was available; `Stacks.NonvanishingPullback.pullbackPowSection` is one. -/
@[ega "II 4.6.13.1" "more general"]
theorem sectionPullbackCompatible :
    Stacks.AmpleLocallyClosed.SectionPullbackCompatible i L (pullbackPowSection i L) := by
  intro n s
  refine Eq.trans ?_ (congrArg (fun T : Set X => i.base ⁻¹' T)
    (coe_powNonvanishingOpen X L n s).symm)
  refine Eq.trans (coe_powNonvanishingOpen X' _ n (pullbackPowSection i L n s)) ?_
  refine Eq.trans (Stacks.Ample.nonvanishingLocus_congr
    (Stacks.RelativeVeryAmple.pullbackTensorPowModuleIso i L n)
    (pullbackGlobalSection i (tensorPowModule X L (n : ℤ)) s)) ?_
  exact (preimage_nonvanishingLocus i (tensorPowModule X L (n : ℤ)) s).symm

/-- **Stacks Tag 0B3E on two premises.** Ampleness pulls back along an immersion, or along any
morphism inducing a homeomorphism onto its image, with the source or the morphism quasi-compact —
given clause (1) ⟹ (3) of Stacks Tag 01Q3 and the Stacks Tag 01PV consequence Stacks Tag 01PX
consumes. The third premise of `Stacks.AmpleLocallyClosed.isAmple_modulePullback`, Stacks Tag 0H78,
is `Stacks.NonvanishingPullback.sectionPullbackCompatible`. -/
theorem isAmple_modulePullback (hL : IsAmple X L)
    (hi : (QuasiCompact i ∧ IsImmersion i) ∨ (CompactSpace X' ∧ IsImmersion i) ∨
      (QuasiCompact i ∧ Topology.IsEmbedding i) ∨
      (CompactSpace X' ∧ Topology.IsEmbedding i))
    (hbasis : IsBasisNonvanishing X L)
    (haff : IsAffineOfLeAffine X' (Stacks.AmpleLocallyClosed.pullbackModule i L)) :
    IsAmple X' (Stacks.AmpleLocallyClosed.pullbackModule i L) :=
  Stacks.AmpleLocallyClosed.isAmple_modulePullback i L hL hi hbasis
    (sectionPullbackCompatible i L) haff

/-- **The Stacks Tag 01PV consequence that Stacks Tag 01PX consumes, discharged.** A nonvanishing
locus of a global section of a positive tensor power that is contained in an affine open is itself
affine.

`Stacks.AmpleTheory.IsAffineOfLeAffine` was isolated as a hypothesis in
`StacksFrontier/AlgebraicGeometry/AmpleTheory/Basic.lean` on the ground that Tag 01PV was "not
available", and `StacksFrontier/AlgebraicGeometry/AmpleLocallyClosed/Basic.lean` once called Tag
01PV "the keystone the ample theory in this repository is missing". **Both claims have been
withdrawn in those files:** Tag 01PV is proved and tagged, as
`Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen`, and it gives the full
statement `X_s ⊓ U` affine for every affine `U`. The containment hypothesis then turns `X_s ⊓ U`
into `X_s`. -/
theorem isAffineOfLeAffine (Z : Scheme.{u}) (N : Z.Modules) [IsInvertibleModule Z N] :
    IsAffineOfLeAffine Z N := by
  intro n _ s U hU hle
  have h := Stacks.NonvanishingAffineIntersection.isAffineOpen_inf_nonvanishingOpen
    (tensorPowModule Z N (n : ℤ)) s hU
  have he : U ⊓ Stacks.NonvanishingOpen.nonvanishingOpen Z (tensorPowModule Z N (n : ℤ)) s =
      powNonvanishingOpen Z N n s := inf_eq_right.mpr hle
  exact he ▸ h

/-- **Stacks Tag 0B3E on one premise.** Two of the three premises of
`Stacks.AmpleLocallyClosed.isAmple_modulePullback` are now theorems — Stacks Tag 0H78 is
`Stacks.NonvanishingPullback.sectionPullbackCompatible` and the Stacks Tag 01PV consequence is
`Stacks.NonvanishingPullback.isAffineOfLeAffine` — so only clause (1) ⟹ (3) of Stacks Tag 01Q3 is
left. -/
theorem isAmple_modulePullback' (hL : IsAmple X L)
    (hi : (QuasiCompact i ∧ IsImmersion i) ∨ (CompactSpace X' ∧ IsImmersion i) ∨
      (QuasiCompact i ∧ Topology.IsEmbedding i) ∨
      (CompactSpace X' ∧ Topology.IsEmbedding i))
    (hbasis : IsBasisNonvanishing X L) :
    IsAmple X' (Stacks.AmpleLocallyClosed.pullbackModule i L) :=
  isAmple_modulePullback i L hL hi hbasis
    (isAffineOfLeAffine X' (Stacks.AmpleLocallyClosed.pullbackModule i L))

/-- **`Stacks.RelativeVeryAmple.AmplePullbackGap` on one premise instead of three.** Of the three
premises `Stacks.RelativeVeryAmple.amplePullbackGap_of_premises` names, `hsect` (Stacks Tag 0H78)
and `haff` (the Stacks Tag 01PV consequence) are discharged; only `hbasis`, clause (1) ⟹ (3) of
Stacks Tag 01Q3, remains. -/
theorem amplePullbackGap_of_isBasisNonvanishing
    (hbasis : ∀ (B : Scheme.{u}) (N : B.Modules) [IsInvertibleModule B N],
      IsAmple B N → IsBasisNonvanishing B N) :
    Stacks.RelativeVeryAmple.AmplePullbackGap.{u} := by
  intro A B j N _ hj hA hN
  exact isAmple_modulePullback' j N hN (Or.inr (Or.inl ⟨hA, hj⟩)) (hbasis B N hN)

/-- **The content of Stacks Tag 01VN on one premise.** Relative ampleness is inherited by an
immersion over the base, given clause (1) ⟹ (3) of Stacks Tag 01Q3 and nothing else. -/
theorem isRelativelyAmple_of_hasRelativeTwistImmersion
    (hbasis : ∀ (B : Scheme.{u}) (N : B.Modules) [IsInvertibleModule B N],
      IsAmple B N → IsBasisNonvanishing B N)
    {Y S : Scheme.{u}} (f : Y ⟶ S) (M : Y.Modules) [IsInvertibleModule Y M]
    (hf : QuasiCompact f) (h : Stacks.RelativeVeryAmple.HasRelativeTwistImmersion f M) :
    Stacks.RelativeAmple.IsRelativelyAmple f M :=
  Stacks.RelativeVeryAmple.isRelativelyAmple_of_hasRelativeTwistImmersion
    (amplePullbackGap_of_isBasisNonvanishing hbasis) f M hf h

end Stacks.NonvanishingPullback

end
