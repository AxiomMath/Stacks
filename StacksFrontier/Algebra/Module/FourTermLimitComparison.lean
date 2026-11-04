module

public import Mathlib

/-!
# Comparing two right-exact three-term sequences, one of them a limit

Let `R` be a commutative ring and let

`Mm --r--> G --δ--> D --> 0`     and     `Lb --rl--> Lc --δl--> Ld`

be two sequences of `R`-modules, the first with `δ` surjective and `δ ∘ r = 0`, the second
exact at `Lc`, together with a map of sequences `(cB, cC, cD)` from the first to the second.
This file proves the two implications that make such a square decide the bijectivity of the
middle comparison `cC`:

* if `cB` is surjective and `cC` is injective, then `cD` is injective;
* if moreover `cB` is surjective, `D` is Artinian and `D` is *abstractly* isomorphic to `Ld`,
  then `cC` is surjective, hence bijective.

The second implication is the point. An injective endomorphism of an Artinian module is
surjective, so an injective map `cD : D ⟶ Ld` between modules that are isomorphic by *some*
`R`-linear isomorphism — not necessarily by `cD` — is already surjective; and a surjective `cD`
together with exactness at `Lc` and surjectivity of `cB` makes `cC` surjective. In the intended
application the isomorphism `D ≅ Ld` is an abstract one, produced by a chain of comparison maps
that is not known to be compatible with `cD`, and the argument above is what makes that
sufficient.

## Main results

* `Stacks.LimitComparison.injective_right` — the first implication.
* `Stacks.LimitComparison.surjective_right_of_isArtinian` — an injective `cD` into an abstractly
  isomorphic Artinian module is surjective.
* `Stacks.LimitComparison.surjective_middle` — the second implication.
* `Stacks.LimitComparison.bijective_middle` — the two together: `cC` is bijective.

## Implementation notes

Nothing here is about limits; the names `Lb`, `Lc`, `Ld` record the intended reading of the
bottom row as the inverse limit of a tower of three-term sequences, where exactness at `Lc` is
what a Mittag-Leffler condition on the kernel tower supplies and the surjectivity of `cB` is
what adic completeness supplies. The statements are element-wise, which is how the sequences of
sections and of local cohomology that they are applied to are stated.
-/

@[expose] public noncomputable section

namespace Stacks.LimitComparison

variable {R : Type*} [CommRing R]
  {Mm : Type*} [AddCommGroup Mm] [Module R Mm]
  {G : Type*} [AddCommGroup G] [Module R G]
  {D : Type*} [AddCommGroup D] [Module R D]
  {Lb : Type*} [AddCommGroup Lb] [Module R Lb]
  {Lc : Type*} [AddCommGroup Lc] [Module R Lc]
  {Ld : Type*} [AddCommGroup Ld] [Module R Ld]
  (r : Mm →ₗ[R] G) (δ : G →ₗ[R] D) (rl : Lb →ₗ[R] Lc) (δl : Lc →ₗ[R] Ld)
  (cB : Mm →ₗ[R] Lb) (cC : G →ₗ[R] Lc) (cD : D →ₗ[R] Ld)

/-- An element killed by `δl` is the image under `cC ∘ r` of some element. -/
private theorem exists_cC_r_eq_of_map_eq_zero
    (hsq₁ : ∀ x, cC (r x) = rl (cB x)) (hcB : Function.Surjective cB)
    (hex : Function.Exact rl δl) {z : Lc} (hz : δl z = 0) : ∃ m, cC (r m) = z := by
  obtain ⟨b, hb⟩ := (hex z).1 hz
  obtain ⟨m, rfl⟩ := hcB b
  exact ⟨m, (hsq₁ m).trans hb⟩

/-- **The comparison on the right is injective.** If the two squares commute, the top row is a
complex with `δ` surjective, the bottom row is exact at `Lc`, the comparison `cB` on the left is
surjective and the comparison `cC` in the middle is injective, then the comparison `cD` on the
right is injective.

A class killed by `cD` is `δ y`; then `cC y` is killed by `δl`, so it is `rl b` for some `b`,
which is `cB m` for some `m`; the left square rewrites that as `cC (r m)`, so `y = r m` by the
injectivity of `cC`, and `δ y = δ (r m) = 0`. -/
theorem injective_right
    (hsq₁ : ∀ x, cC (r x) = rl (cB x)) (hsq₂ : ∀ x, cD (δ x) = δl (cC x))
    (hδr : ∀ x, δ (r x) = 0) (hδ : Function.Surjective δ) (hcB : Function.Surjective cB)
    (hex : Function.Exact rl δl) (hcC : Function.Injective cC) :
    Function.Injective cD := by
  refine (injective_iff_map_eq_zero _).2 fun x hx => ?_
  obtain ⟨y, rfl⟩ := hδ x
  obtain ⟨m, hm⟩ := exists_cC_r_eq_of_map_eq_zero r rl δl cB cC hsq₁ hcB hex
    ((hsq₂ y).symm.trans hx)
  rw [← hcC hm, hδr m]

/-- **An injective map into an abstractly isomorphic Artinian module is surjective.** The
composite of `cD` with the inverse of any `R`-linear isomorphism `D ≃ₗ[R] Ld` is an injective
endomorphism of the Artinian module `D`, hence surjective; composing back with the isomorphism
makes `cD` surjective.

The isomorphism is *data not related to* `cD`: this is what lets an abstract comparison, known
to exist but not known to be the canonical map, be used. -/
theorem surjective_right_of_isArtinian [IsArtinian R D] (e : D ≃ₗ[R] Ld)
    (hcD : Function.Injective cD) :
    Function.Surjective cD := by
  have hcomp : Function.Injective ((e.symm : Ld →ₗ[R] D).comp cD) :=
    e.symm.injective.comp hcD
  have hsurj : Function.Surjective ((e.symm : Ld →ₗ[R] D).comp cD) :=
    IsArtinian.surjective_of_injective_endomorphism _ hcomp
  intro z
  obtain ⟨x, hx⟩ := hsurj (e.symm z)
  exact ⟨x, e.symm.injective hx⟩

/-- **The comparison in the middle is surjective.** With the two squares commuting, the top row
a complex with `δ` surjective, the bottom row exact at `Lc`, the comparison `cB` surjective and
the comparison `cD` on the right surjective, the comparison `cC` in the middle is surjective.

Given `s : Lc`, its image `δl s` is `cD (δ y)` for some `y`, which is `δl (cC y)`; so
`s - cC y` is killed by `δl`, hence is `rl (cB m) = cC (r m)` for some `m`, and
`s = cC (y + r m)`. -/
theorem surjective_middle
    (hsq₁ : ∀ x, cC (r x) = rl (cB x)) (hsq₂ : ∀ x, cD (δ x) = δl (cC x))
    (hδ : Function.Surjective δ) (hcB : Function.Surjective cB)
    (hex : Function.Exact rl δl) (hcD : Function.Surjective cD) :
    Function.Surjective cC := by
  intro s
  obtain ⟨x, hx⟩ := hcD (δl s)
  obtain ⟨y, rfl⟩ := hδ x
  obtain ⟨m, hm⟩ := exists_cC_r_eq_of_map_eq_zero r rl δl cB cC hsq₁ hcB hex
    (show δl (s - cC y) = 0 by rw [map_sub, ← hsq₂ y, hx, sub_self])
  exact ⟨y + r m, by rw [map_add, hm, add_sub_cancel]⟩

/-- **The comparison in the middle is bijective.** The hypotheses are those of
`Stacks.LimitComparison.injective_right` together with an Artinian `D` and an abstract
`R`-linear isomorphism `D ≃ₗ[R] Ld`: the right comparison is then injective, hence surjective by
`Stacks.LimitComparison.surjective_right_of_isArtinian`, hence the middle one is surjective by
`Stacks.LimitComparison.surjective_middle`, and it was assumed injective. -/
theorem bijective_middle [IsArtinian R D] (e : D ≃ₗ[R] Ld)
    (hsq₁ : ∀ x, cC (r x) = rl (cB x)) (hsq₂ : ∀ x, cD (δ x) = δl (cC x))
    (hδr : ∀ x, δ (r x) = 0) (hδ : Function.Surjective δ) (hcB : Function.Surjective cB)
    (hex : Function.Exact rl δl) (hcC : Function.Injective cC) :
    Function.Bijective cC :=
  ⟨hcC, surjective_middle r δ rl δl cB cC cD hsq₁ hsq₂ hδ hcB hex
    (surjective_right_of_isArtinian cD e
      (injective_right r δ rl δl cB cC cD hsq₁ hsq₂ hδr hδ hcB hex hcC))⟩

end Stacks.LimitComparison

end
