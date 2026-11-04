module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Module.Reflexive
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.UnramifiedCodimensionOneFlatAt
public import StacksFrontier.AlgebraicGeometry.Properties.Dimension
public import StacksFrontier.RingTheory.CohenMacaulay.RegularSequence
public import StacksFrontier.RingTheory.Flat.MiracleFlatness
public import StacksFrontier.RingTheory.IntegrallyClosed.Defs
public import StacksFrontier.RingTheory.Serre.Criterion

/-!
# Purity of the branch locus in dimension at most two

Let `f : X ⟶ Y` be a morphism of locally Noetherian schemes, let `x` be a point of `X` and let
`y = f x`. Assume the local ring of `X` at `x` is normal, the local ring of `Y` at `y` is
regular, `f` is quasi-finite at `x`, the two local rings have the same dimension, and `f` is
unramified at every point specializing to `x` whose local ring has dimension one. Purity of the
branch locus, [Stacks, Tag 0BMB], asserts that `f` is then étale at `x`. This file proves the
case in which the common dimension `d` satisfies `1 ≤ d ≤ 2`.

The whole content is flatness of `𝒪_{Y,y} → 𝒪_{X,x}`. Once that is available, étaleness at `x`
is [Stacks, Tag 0BJH] in the pointwise form
`AlgebraicGeometry.etaleAt_of_isFlatAt_of_unramifiedAt_codimensionOne`: the point is not the
generic point of an irreducible component, its local ring having positive dimension, and the
hypothesis on one-dimensional generizations is exactly what that criterion consumes.

Flatness is miracle flatness, [Stacks, Tag 00R4]. The target local ring is regular; the source
local ring `B = 𝒪_{X,x}` is a normal Noetherian local ring of dimension at most two, hence
Cohen–Macaulay, because Serre's criterion ([Stacks, Tag 031S]) gives `depth B ≥ min {2, dim B}`
and `depth B ≤ dim B` is [Stacks, Tag 00LK]; and the fibre ring `B ⧸ 𝔪_A B` is zero-dimensional
because a quasi-finite algebra admits no strict inclusion between two primes with the same
contraction (`Algebra.QuasiFinite.eq_of_le_of_under_eq`), so the maximal ideal of `B` is the only
prime of `B` above `𝔪_A`. That is the dimension identity `dim B = dim A + dim (B ⧸ 𝔪_A B)`.

## Main results

* `Stacks.PurityBranchLocus.isMaximalCohenMacaulay_of_isNormalRing_of_le_two` — a normal
  Noetherian local ring of dimension at most two is Cohen–Macaulay.
* `Stacks.PurityBranchLocus.ringKrullDim_fiber_eq_zero_of_quasiFinite` — the fibre ring of a
  quasi-finite local homomorphism is zero-dimensional.
* `Stacks.PurityBranchLocus.flat_of_quasiFinite_of_isMaximalCohenMacaulay` — a quasi-finite
  local homomorphism from a regular local ring to a Cohen–Macaulay local ring of the same
  dimension is flat.
* `Stacks.PurityBranchLocus.flat_of_quasiFinite_of_le_two` — a quasi-finite local
  homomorphism from a regular local ring to a normal local ring of the same dimension, at most
  two, is flat.
* `etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_isMaximalCohenMacaulay`, in
  `AlgebraicGeometry` — the tag's conclusion at a point whose local ring is Cohen–Macaulay, in
  any dimension.
* `AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_dim_le_two` —
  **[Stacks, Tag 0BMB] in the case `1 ≤ dim 𝒪_{X,x} = dim 𝒪_{Y,y} ≤ 2`.**

## Implementation notes

**Normality** of the source local ring is `IsNormalRing`, the predicate of
`StacksFrontier/RingTheory/IntegrallyClosed/Defs.lean`: every localization at a prime is an
integrally closed domain. For a local ring that is the source's "normal", by
`IsNormalRing.of_isLocalRing`, which yields the domain and integrally closed structure Serre's
criterion needs.

**The dimension hypothesis** is stated as the tag states it, `dim 𝒪_{X,x} = dim 𝒪_{Y,y}`,
together with the tag's `1 ≤ dim 𝒪_{X,x}` and the case restriction `dim 𝒪_{X,x} ≤ 2`. The case
`d = 1` of the tag is
`AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_dim_eq_one`, whose
argument is the source's own treatment of that case — a one-dimensional regular local ring is a
discrete valuation ring, over which flatness is torsion-freeness. The theorem here covers that
case too, by the uniform argument above; the earlier statement is left where it is, with its own
proof.

**What the case `d ≥ 3` needs.** The reduction above is dimension-free except for
Cohen–Macaulayness of `𝒪_{X,x}`, which for a normal local ring is Serre's criterion only up to
dimension two. So the general case of the tag comes down to flatness of `𝒪_{Y,y} → 𝒪_{X,x}` for
`A = 𝒪_{Y,y}` regular local of dimension `d ≥ 3`, `B = 𝒪_{X,x}` normal local of the same
dimension, `A → B` a quasi-finite local homomorphism which is étale over the punctured spectrum
of `A`. That is [Stacks, Tag 0BMA] clause (2) at a general `d`, for a quasi-finite rather than a
finite `B`; this library has that tag for `d = 2` and for a finite `B`
(`Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_ringKrullDim_eq_two`), where miracle
flatness is also what supplies flatness. The passage from a finite to a quasi-finite `B` is the
source's own first step: by [Stacks, Tag 02LK] an elementary étale change of the base makes `f`
finite near `x` with `x` the only point above `f x`, which turns `𝒪_{X,x}` into a finite algebra
over the new base local ring, and étaleness at a point is insensitive to that change by
[Stacks, Tags 02VN and 036W]. Its torsion-freeness hypothesis, on the other hand, is no
obstacle: `B` is a domain and `A → B` is injective, the kernel being a prime of the domain `A`
whose height is `dim A - dim B = 0`.

## References

* [Stacks Project, Tag 0BMB](https://stacks.math.columbia.edu/tag/0BMB)
* [Stacks Project, Tag 00R4](https://stacks.math.columbia.edu/tag/00R4)
* [Stacks Project, Tag 031S](https://stacks.math.columbia.edu/tag/031S)
* [Stacks Project, Tag 0BJH](https://stacks.math.columbia.edu/tag/0BJH)
-/

@[expose] public section

open CategoryTheory IsLocalRing

universe u

namespace Stacks.PurityBranchLocus

/-- **A normal Noetherian local ring of dimension at most two is Cohen–Macaulay.** Serre's
criterion ([Stacks, Tag 031S]) gives `depth ≥ min {2, dim}`, which in dimension at most two is
`depth ≥ dim`; the reverse inequality is [Stacks, Tag 00LK]. -/
public lemma isMaximalCohenMacaulay_of_isNormalRing_of_le_two (B : Type u) [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] (hB : IsNormalRing B)
    (hone : 1 ≤ ringKrullDim B) (hle : ringKrullDim B ≤ 2) :
    Module.IsMaximalCohenMacaulay B B := by
  obtain ⟨_, _⟩ := hB.of_isLocalRing
  have hS2 := min_two_le_moduleDepth_of_isIntegrallyClosed B
  rw [moduleDepth_eq_depth] at hS2
  obtain ⟨d, hd⟩ := WithBot.ne_bot_iff_exists.mp (ne_bot_of_le_ne_bot WithBot.coe_ne_bot hone)
  rw [← hd, WithBot.unbotD_coe] at hS2
  have hd2 : d ≤ 2 := by
    rw [← hd] at hle
    have h2 : (d : WithBot ℕ∞) ≤ ((2 : ℕ∞) : WithBot ℕ∞) := hle
    exact WithBot.coe_le_coe.mp h2
  rw [min_eq_right hd2] at hS2
  have hmin : ringKrullDim B ≤ (Module.depth B (maximalIdeal B) B : WithBot ℕ∞) := by
    rw [← hd]
    exact_mod_cast hS2
  show (Module.depth B (maximalIdeal B) B : WithBot ℕ∞) = ringKrullDim B
  exact le_antisymm ((Module.depth_le_supportDim B _ B
    (Module.maximalIdeal_smul_top_ne_top B)).trans_eq
      (Module.supportDim_self_eq_ringKrullDim B)) hmin

/-- **The fibre ring of a quasi-finite local homomorphism is zero-dimensional.** A prime of `B`
containing the image of `𝔪_A` contracts to `𝔪_A`, as does the maximal ideal of `B`; so the two
agree, quasi-finiteness forbidding a strict inclusion between primes with the same contraction.
The maximal ideal is therefore the only prime of `B` over `𝔪_A`. -/
public lemma ringKrullDim_fiber_eq_zero_of_quasiFinite (A B : Type u) [CommRing A]
    [CommRing B] [IsLocalRing A] [IsLocalRing B] [Algebra A B] [IsLocalHom (algebraMap A B)]
    [Algebra.QuasiFinite A B] :
    ringKrullDim (B ⧸ (maximalIdeal A).map (algebraMap A B)) = 0 := by
  have hcomap : Ideal.under A (maximalIdeal B) = maximalIdeal A :=
    IsLocalRing.maximalIdeal_comap (algebraMap A B)
  have hle : (maximalIdeal A).map (algebraMap A B) ≤ maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, ← hcomap]
  have _ : Nontrivial (B ⧸ (maximalIdeal A).map (algebraMap A B)) :=
    Ideal.Quotient.nontrivial_iff.mpr (ne_top_of_le_ne_top (maximalIdeal.isMaximal B).ne_top hle)
  refine ringKrullDimZero_iff_ringKrullDim_eq_zero.mp
    (Ideal.krullDimLE_zero_quotient_iff_forall_minimalPrimes_isMaximal.mpr fun J hJ => ?_)
  have _ : J.IsPrime := hJ.1.1
  have hmA : maximalIdeal A ≤ Ideal.under A J := fun a ha => hJ.1.2 (Ideal.mem_map_of_mem _ ha)
  have hunder : Ideal.under A J = Ideal.under A (maximalIdeal B) := by
    rw [hcomap]
    exact ((maximalIdeal.isMaximal A).eq_of_le (Ideal.IsPrime.ne_top inferInstance) hmA).symm
  rw [Algebra.QuasiFinite.eq_of_le_of_under_eq (R := A) J (maximalIdeal B)
    (IsLocalRing.le_maximalIdeal_of_isPrime J) hunder]
  exact maximalIdeal.isMaximal B

/-- **A quasi-finite local homomorphism from a regular local ring to a Cohen–Macaulay local ring
of the same dimension is flat.** This is miracle flatness, [Stacks, Tag 00R4]: the fibre ring is
zero-dimensional by quasi-finiteness, so the dimension identity
`dim B = dim A + dim (B ⧸ 𝔪_A B)` holds. -/
@[ega "IV 15.4.2" "e′)⇒b), partial"]
public lemma flat_of_quasiFinite_of_isMaximalCohenMacaulay {A B : Type u} [CommRing A]
    [CommRing B] [IsLocalRing B] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ]
    (hA : IsRegularLocalRing A) (hB : Module.IsMaximalCohenMacaulay B B)
    (hdim : ringKrullDim B = ringKrullDim A) (hqf : φ.QuasiFinite) : φ.Flat := by
  let _ := hA
  let _ : Algebra A B := φ.toAlgebra
  have halg : algebraMap A B = φ := φ.algebraMap_toAlgebra
  have _ : IsLocalHom (algebraMap A B) := by rwa [halg]
  have _ : Algebra.QuasiFinite A B := RingHom.quasiFinite_algebraMap.mp (by rwa [halg])
  rw [← halg, RingHom.flat_algebraMap_iff]
  exact Module.Flat.of_isMaximalCohenMacaulay_of_ringKrullDim_eq_add hB
    (by rwa [ringKrullDim_fiber_eq_zero_of_quasiFinite A B, add_zero])

/-- **A quasi-finite local homomorphism from a regular local ring to a normal local ring of the
same dimension, at most two, is flat.** Such a target is Cohen–Macaulay by Serre's criterion,
and then miracle flatness applies. -/
@[ega "IV 15.4.2" "e′)⇒b), partial", ega "IV 6.1.5" "special case"]
public lemma flat_of_quasiFinite_of_le_two {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing B] [IsNoetherianRing B] (φ : A →+* B) [IsLocalHom φ]
    (hA : IsRegularLocalRing A) (hB : IsNormalRing B)
    (hdim : ringKrullDim B = ringKrullDim A) (hone : 1 ≤ ringKrullDim B)
    (hle : ringKrullDim B ≤ 2) (hqf : φ.QuasiFinite) : φ.Flat :=
  flat_of_quasiFinite_of_isMaximalCohenMacaulay φ hA
    (isMaximalCohenMacaulay_of_isNormalRing_of_le_two B hB hone hle) hdim hqf

end Stacks.PurityBranchLocus

namespace AlgebraicGeometry

/-- **Purity of the branch locus at a Cohen–Macaulay point, in any dimension.** Let
`f : X ⟶ Y` be a morphism of locally Noetherian schemes and let `x : X` be a point at which `f`
is quasi-finite, with regular local ring at `f x` and Cohen–Macaulay local ring at `x` of the
same, positive, dimension. If `f` is unramified at every point specializing to `x` whose local
ring has dimension one, then `f` is étale at `x`.

This is the engine behind [Stacks, Tag 0BMB]: flatness of the stalk map is miracle flatness
([Stacks, Tag 00R4]) and étaleness at `x` is then [Stacks, Tag 0BJH]. The tag's hypothesis that
`𝒪_{X,x}` be normal enters only through Cohen–Macaulayness, which Serre's criterion supplies for
a normal local ring of dimension at most two. -/
@[sga "1 X 3.1" "partial, special case"]
public theorem etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_isMaximalCohenMacaulay
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : X)
    (hX : Module.IsMaximalCohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x))
    (hY : IsRegularLocalRing (Y.presheaf.stalk (f x)))
    (hqf : quasiFiniteAt f x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (hone : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hunr : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 → UnramifiedAt f x') :
    EtaleAt f x := by
  refine etaleAt_of_isFlatAt_of_unramifiedAt_codimensionOne f x hqf
    (Stacks.PurityBranchLocus.flat_of_quasiFinite_of_isMaximalCohenMacaulay
      (f.stalkMap x).hom hY hX hdim hqf.2) (fun hmem => ?_) hunr
  rw [(ringKrullDim_stalk_eq_zero_iff_mem_genericPoints X x).mpr hmem] at hone
  norm_num at hone

/-- **Purity of the branch locus, [Stacks, Tag 0BMB], in dimension at most two.** Let
`f : X ⟶ Y` be a morphism of locally Noetherian schemes and let `x : X` be a point whose local
ring is normal, with regular local ring at `f x`, at which `f` is quasi-finite, and such that the
two local rings have the same dimension, which is at least one and at most two. If `f` is
unramified at every point specializing to `x` whose local ring has dimension one, then `f` is
étale at `x`.

This is the tag with its hypothesis `1 ≤ dim 𝒪_{X,x}` supplemented by `dim 𝒪_{X,x} ≤ 2`. See the
module docstring for what the case `dim 𝒪_{X,x} ≥ 3` comes down to. -/
@[stacks 0BMB "the case `1 ≤ dim 𝒪_{X,x} = dim 𝒪_{Y,f x} ≤ 2`. Hypotheses (1), (2), (3) and (5) \
are the tag's own; hypothesis (4) is the tag's `dim 𝒪_{X,x} = dim 𝒪_{Y,f x} ≥ 1` together with \
the case restriction `dim 𝒪_{X,x} ≤ 2`. Flatness of `𝒪_{Y,f x} → 𝒪_{X,x}` is miracle flatness \
(tag 00R4), a normal Noetherian local ring of dimension at most two being Cohen–Macaulay by \
Serre's criterion (tag 031S) and the fibre ring being zero-dimensional by quasi-finiteness; \
étaleness at `x` then follows from tag 0BJH. For `dim 𝒪_{X,x} ≥ 3` the same reduction leaves \
exactly the flatness of `𝒪_{Y,f x} → 𝒪_{X,x}`, which is tag 0BMA clause (2) at a general \
dimension. See the module docstring.",
  ega "IV 21.12.14" "(v), (v), special case",
  sga "1 X 3.1" "partial, special case"]
public theorem etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_dim_le_two
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : X)
    (hX : IsNormalRing (X.presheaf.stalk x))
    (hY : IsRegularLocalRing (Y.presheaf.stalk (f x)))
    (hqf : quasiFiniteAt f x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (hone : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hle : ringKrullDim (X.presheaf.stalk x) ≤ 2)
    (hunr : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 → UnramifiedAt f x') :
    EtaleAt f x :=
  etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_isMaximalCohenMacaulay f x
    (Stacks.PurityBranchLocus.isMaximalCohenMacaulay_of_isNormalRing_of_le_two _ hX hone hle)
    hY hqf hdim hone hunr

end AlgebraicGeometry

end
