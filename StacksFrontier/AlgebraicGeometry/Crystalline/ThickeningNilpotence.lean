module

public import Mathlib.AlgebraicGeometry.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Crystalline.BigSite.Basic
public import StacksFrontier.AlgebraicGeometry.LiftInvertible.NilpotentUnits

/-!
# `p` is locally nilpotent on the ambient scheme of an object of `CRIS(X/S)`

Fix a global crystalline situation `(p, (S, I, γ), X)`.  Its datum
`Crystalline.GlobalCrystallineSituation.prime_locallyNilpotent` asks that `p` be nilpotent in
every local ring of `X`, and says nothing about the ambient divided power schemes `T` of the
objects `(U, T, δ)` of `CRIS(X/S)`.  This file proves that `p` is nilpotent on the sections of
every affine open of such a `T`, and in every local ring of `T`.

The statement is **not** a formality: `p` nilpotent on `U` and `U ↪ T` a closed immersion whose
ideal carries divided powers is *not* enough.  Take `p` a prime, `A = ℤ_p`, `I = (p)` with the
divided powers `δ_n(x) = x ^ n / n!`, so that `(A, I, δ)` is a divided power ring over `ℤ_(p)`;
with `T = Spec ℤ_p` and `U = Spec 𝔽_p` the closed immersion `U ⟶ T` has the divided power ideal
of `T` as its ideal and `p` nilpotent — indeed zero — on `U`, yet `p` is a nonzerodivisor on `T`.
What rules this out is that `U ⟶ T` is a *thickening*: `Spec 𝔽_p ⟶ Spec ℤ_p` is not surjective,
`Spec ℤ_p` having a generic point as well.  So the proof below runs entirely through the
surjectivity half of `Stacks.Thickenings.IsThickening`, which forces the ideal of the immersion
into the nilradical, and the divided powers play no part.

## Main results

* `AlgebraicGeometry.Scheme.isNilpotent_of_forall_isNilpotent_germ_of_isCompact` — a section over
  a *compact open* which is nilpotent in every local ring is nilpotent.  This is
  `AlgebraicGeometry.Scheme.isNilpotent_of_forall_isNilpotent_germ` of
  `StacksFrontier/AlgebraicGeometry/Crystalline/BigSite/BinaryProductPatch.lean` with the open
  allowed to be smaller than `⊤`, which is what an affine open of a non-quasi-compact `T` needs.
* `Crystalline.SchemeThickening.isNilpotent_of_app_eq_zero` — **a section of the ambient scheme of
  a divided power thickening that restricts to zero on the thickened scheme is nilpotent**, over
  any affine open.
* `Crystalline.GlobalCrystallineSituation.Thickening.isNilpotent_prime_sections_target` — **`p` is
  nilpotent on the sections of every affine open of the ambient scheme `T`**, and
  `prime_locallyNilpotent_target` — **`p` is nilpotent in every local ring of `T`.**
* `Crystalline.GlobalCrystallineSituation.Thickening.exists_isAffineOpen_mem_and_pow_eq_zero` —
  **every point of `T` has an affine open neighbourhood on which some power `p ^ e` vanishes**,
  with the exponent depending on the neighbourhood.

## What is and is not proved

**No tag attribute is placed in this file.**  Nothing here is [Stacks, Tag 07MV], and nothing here
is the definition of the crystalline site.  What is proved is one input that remark's argument
uses and that the library did not have: the "`p` is locally nilpotent on `T`" of the discussion
following [Stacks, Tag 07I5], the sentence behind the hint of [Stacks, Tag 07MV] that *any object
of `Cris(X/S)` is locally an object of one of the categories `Cris(X/S_e)`*.

What is **not** proved is the passage from that to the statement the hint actually uses, namely
`Γ(Cris(X/S), F) = lim_e Γ(Cris(X/S_e), F_e)`.  Two things stand in the way and neither is
touched here.  First, `exists_isAffineOpen_mem_and_pow_eq_zero` gives an exponent `e` *per affine
open*, and an object of `Cris(X/S)` whose ambient scheme is not quasi-compact need not admit a
single `e` for the whole of `T`; the covering families of the site are what repair this, and
turning the local statement into the assertion that the full subcategories `Cris(X/S_e)` are
jointly covering is a separate step.  Second, the vanishing `p ^ e = 0` on an affine open of `T`
is not yet a factorization of `T|_V ⟶ S` through `S_e = Spec(A/p^eA)`: that needs the divided
power structure of the quotient, which is `Crystalline.pAdicLevelRing` of
`StacksFrontier/AlgebraicGeometry/Crystalline/FiniteLevelBase.lean`, and a comparison of the
structure map of the object with it.

The nilpotence order is genuinely local, and the counterexample in the module header above shows
the hypothesis cannot be dropped, so nothing below is stated with a uniform exponent.

## References

* [Stacks Project, Tag 07I5](https://stacks.math.columbia.edu/tag/07I5)
* [Stacks Project, Tag 07I6](https://stacks.math.columbia.edu/tag/07I6)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
* [Stacks Project, Tag 07MV](https://stacks.math.columbia.edu/tag/07MV)
* [Stacks Project, Tag 04EX](https://stacks.math.columbia.edu/tag/04EX)
-/

@[expose] public section

open CategoryTheory AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

/-- **A section over a compact open of a scheme which is nilpotent in every local ring is
nilpotent.**  The basic open of the section is the locus where it is a unit, and a nilpotent
element of a local ring is not a unit, so that locus is empty; a section over a compact open with
empty basic open is nilpotent.

This is `AlgebraicGeometry.Scheme.isNilpotent_of_forall_isNilpotent_germ` with the open allowed to
be smaller than `⊤`.  Without the compactness the statement fails: the nilpotence orders at the
individual points need not be bounded. -/
theorem isNilpotent_of_forall_isNilpotent_germ_of_isCompact {X : Scheme.{u}} {U : X.Opens}
    (hU : IsCompact (U : Set X)) (f : Γ(X, U))
    (h : ∀ (x : X) (hx : x ∈ U), IsNilpotent (X.presheaf.germ U x hx f)) : IsNilpotent f := by
  rw [Scheme.isNilpotent_iff_basicOpen_eq_bot_of_isCompact hU]
  refine le_antisymm (fun x hx ↦ ?_) bot_le
  have hxU : x ∈ U := X.basicOpen_le f hx
  exact absurd ((X.mem_basicOpen f x hxU).mp hx) (h x hxU).not_isUnit

end AlgebraicGeometry.Scheme

namespace Crystalline

namespace SchemeThickening

variable (D : SchemeThickening.{u})

/-- **A section of the ambient scheme of a divided power thickening which restricts to zero on the
thickened scheme is nilpotent**, over any affine open of the ambient scheme.

The immersion is a thickening, so its underlying map is onto; the support of the kernel ideal
sheaf of a quasi-compact morphism is the closure of its range
(`AlgebraicGeometry.Scheme.Hom.support_ker`), hence everything, and an ideal sheaf with that
support lies in the nilradical by `Stacks.LiftInvertible.ker_le_nilradical_of_surjective`.  Over an
affine open the kernel ideal sheaf *is* the kernel of the restriction map, by
`AlgebraicGeometry.Scheme.Hom.ker_apply`.

The divided powers are not used.  This is the non-affine, affine-open-indexed form of
`Stacks.Thickenings.IsThickening.isNilpotent_of_mem_ker_appTop`, which asks the ambient scheme to
be affine and speaks only about global sections. -/
theorem isNilpotent_of_app_eq_zero (V : D.target.scheme.affineOpens)
    {a : Γ(D.target.scheme, (V : D.target.scheme.Opens))}
    (ha : (D.immersion.app (V : D.target.scheme.Opens)).hom a = 0) : IsNilpotent a := by
  have hmem : a ∈ D.immersion.ker.ideal V := by
    rw [Scheme.Hom.ker_apply]
    exact RingHom.mem_ker.mpr ha
  have hnil : a ∈ D.target.scheme.nilradical.ideal V :=
    Stacks.LiftInvertible.ker_le_nilradical_of_surjective D.immersion
      D.isThickening.2 V hmem
  rw [Scheme.nilradical, Scheme.IdealSheafData.radical_ideal,
    Scheme.IdealSheafData.ideal_bot] at hnil
  exact mem_nilradical.mp hnil

/-- **A section of the ambient scheme of a divided power thickening whose restriction to the
thickened scheme is nilpotent is itself nilpotent**, over any affine open.  A power of it
restricts to zero, so `Crystalline.SchemeThickening.isNilpotent_of_app_eq_zero` applies to that
power. -/
theorem isNilpotent_of_isNilpotent_app (V : D.target.scheme.affineOpens)
    {a : Γ(D.target.scheme, (V : D.target.scheme.Opens))}
    (ha : IsNilpotent ((D.immersion.app (V : D.target.scheme.Opens)).hom a)) :
    IsNilpotent a := by
  obtain ⟨n, hn⟩ := ha
  refine IsNilpotent.of_pow (m := n) (D.isNilpotent_of_app_eq_zero V ?_)
  rw [map_pow]
  exact hn

/-- **The preimage of an affine open of the ambient scheme is a compact open of the thickened
scheme.**  The immersion of a divided power thickening is a closed immersion, hence a closed
embedding, and a closed embedding is proper: preimages of compact sets are compact. -/
theorem isCompact_preimage_of_isAffineOpen (V : D.target.scheme.affineOpens) :
    IsCompact (((D.immersion ⁻¹ᵁ (V : D.target.scheme.Opens)) : D.source.Opens) :
      Set D.source) :=
  D.immersion.isClosedEmbedding.isCompact_preimage V.2.isCompact

end SchemeThickening

namespace GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}}

namespace Thickening

/-- **The fixed prime is nilpotent in every local ring of the thickened scheme of an object of
`CRIS(X/S)`.**  The thickened scheme maps to `X`, and the induced map of local rings carries the
nilpotence of `p` on `X` — the datum
`Crystalline.GlobalCrystallineSituation.prime_locallyNilpotent` — forward. -/
theorem isNilpotent_prime_stalk_source (A : Thickening S) (y : A.thickening.source) :
    IsNilpotent ((S.p : ℕ) : A.thickening.source.presheaf.stalk y) := by
  have h := (S.prime_locallyNilpotent (A.toX.base y)).map (A.toX.stalkMap y).hom
  rwa [map_natCast] at h

/-- **The fixed prime is nilpotent on the sections of every compact open of the thickened scheme
of an object of `CRIS(X/S)`.**  It is nilpotent in every local ring by
`isNilpotent_prime_stalk_source`, and on a compact open that upgrades to nilpotence of the section
by `AlgebraicGeometry.Scheme.isNilpotent_of_forall_isNilpotent_germ_of_isCompact`. -/
theorem isNilpotent_prime_sections_source (A : Thickening S) {W : A.thickening.source.Opens}
    (hW : IsCompact (W : Set A.thickening.source)) :
    IsNilpotent ((S.p : ℕ) : Γ(A.thickening.source, W)) := by
  refine Scheme.isNilpotent_of_forall_isNilpotent_germ_of_isCompact hW _ fun y hy ↦ ?_
  rw [map_natCast]
  exact isNilpotent_prime_stalk_source A y

/-- **The fixed prime is nilpotent on the sections of every affine open of the ambient scheme of an
object of `CRIS(X/S)`.**

The preimage of the affine open is a compact open of the thickened scheme, on which `p` is
nilpotent by `isNilpotent_prime_sections_source`; so a power of `p` restricts to zero along the
immersion, and `Crystalline.SchemeThickening.isNilpotent_of_isNilpotent_app` carries nilpotence
back across it.

This is the "`p` is locally nilpotent on `T`" of the discussion following [Stacks, Tag 07I5].  It
is not assumed: the situation asks only for nilpotence of `p` in the local rings of `X`, and the
work is done by the surjectivity of the immersion. -/
theorem isNilpotent_prime_sections_target (A : Thickening S)
    (V : A.thickening.target.scheme.affineOpens) :
    IsNilpotent ((S.p : ℕ) : Γ(A.thickening.target.scheme,
      (V : A.thickening.target.scheme.Opens))) := by
  refine A.thickening.isNilpotent_of_isNilpotent_app V ?_
  rw [map_natCast]
  exact isNilpotent_prime_sections_source A
    (A.thickening.isCompact_preimage_of_isAffineOpen V)

/-- Every point of the ambient scheme has an affine open neighbourhood on which `p` is nilpotent. -/
private theorem exists_isAffineOpen_mem_isNilpotent_prime (A : Thickening S)
    (t : A.thickening.target.scheme) :
    ∃ (V : A.thickening.target.scheme.Opens) (_ : IsAffineOpen V) (_ : t ∈ V),
      IsNilpotent ((S.p : ℕ) : Γ(A.thickening.target.scheme, V)) := by
  obtain ⟨V, hV, htV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (X := A.thickening.target.scheme) (x := t)
      (U := ⊤) trivial
  exact ⟨V, hV, htV, isNilpotent_prime_sections_target A ⟨V, hV⟩⟩

/-- **The fixed prime is nilpotent in every local ring of the ambient scheme of an object of
`CRIS(X/S)`.**  Every point has an affine open neighbourhood, on which `p` is nilpotent by
`isNilpotent_prime_sections_target`, and the germ map is a ring homomorphism. -/
theorem prime_locallyNilpotent_target (A : Thickening S)
    (t : A.thickening.target.scheme) :
    IsNilpotent ((S.p : ℕ) : A.thickening.target.scheme.presheaf.stalk t) := by
  obtain ⟨V, -, htV, h⟩ := exists_isAffineOpen_mem_isNilpotent_prime A t
  have h := h.map (A.thickening.target.scheme.presheaf.germ V t htV).hom
  rwa [map_natCast] at h

/-- **Every point of the ambient scheme of an object of `CRIS(X/S)` has an affine open
neighbourhood on which some power of `p` vanishes.**  This is
`isNilpotent_prime_sections_target` with the nilpotence order named; it is the local statement
behind the hint of [Stacks, Tag 07MV] that any object of `Cris(X/S)` is locally an object of one
of the `Cris(X/S_e)`.

The exponent depends on the neighbourhood.  No uniform exponent is claimed, and none is available
for an object whose ambient scheme is not quasi-compact. -/
theorem exists_isAffineOpen_mem_and_pow_eq_zero (A : Thickening S)
    (t : A.thickening.target.scheme) :
    ∃ (V : A.thickening.target.scheme.Opens) (_ : IsAffineOpen V) (_ : t ∈ V) (e : ℕ),
      ((S.p : ℕ) : Γ(A.thickening.target.scheme, V)) ^ e = 0 := by
  obtain ⟨V, hV, htV, e, he⟩ := exists_isAffineOpen_mem_isNilpotent_prime A t
  exact ⟨V, hV, htV, e, he⟩

end Thickening

end GlobalCrystallineSituation

end Crystalline

end
