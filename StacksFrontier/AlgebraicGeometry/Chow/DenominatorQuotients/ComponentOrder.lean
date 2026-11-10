module

public import StacksFrontier.AlgebraicGeometry.Chow.FibreCycles.StalkPrimes
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FibreStalkBridges
public import StacksFrontier.RingTheory.Length.SemilinearTransfer

/-!
# The order of vanishing in the residue ring of a minimal prime is the order on the component

Let `X` be a scheme, `ξ` a point and `q` a prime of the local ring `A = 𝒪_{X, ξ}`. The length
formula of [Stacks, Tag 02QH] produces, for each minimal prime `q` of `A`, the order of vanishing
`Ring.ord (A ⧸ q)` of the image of a germ; part (4) of [Stacks, Tag 02SW] states its right-hand
side in terms of the order of vanishing *on the irreducible component* that `q` indexes. This
file identifies the two rings in which those two orders are taken.

The component is the reduced closed subscheme supported on the closure of
`η = X.fromSpecStalk ξ q`, and
`Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk` says that the stalk of its ideal
sheaf at `ξ` is exactly `q`. So `A ⧸ q` is the quotient of `A` by the stalk of that ideal sheaf,
which `AlgebraicGeometry.Scheme.IdealSheafData.subschemeStalkRingEquiv` identifies with the local
ring of the component at the point above `ξ`. Transporting `Ring.ord` across that ring
isomorphism is the content here, and the result is hypothesis-free: no Noetherian, integral or
dimension assumption appears, because none appears in the statements being composed.

## Main results

* `Ring.ord_ringEquiv` — the order of vanishing is invariant under a ring isomorphism. Mathlib's
  `Ring.ord` API has `ord_mul`, `ord_pow`, `ord_eq_of_associated` and the rest, but no
  congruence under a `RingEquiv`.
* `AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_stalk` — the bridge between the two
  spellings of the stalk of an ideal sheaf that this development carries; see the implementation
  notes.
* `Stacks.Chow.ord_subschemeStalk` — `Ring.ord` of a germ in `A ⧸ I_ξ` is `Ring.ord` of its image
  in the local ring of the closed subscheme cut out by `I`.
* `Stacks.Chow.stalkIdeal_vanishingIdeal_closure_fromSpecStalk` — the ideal of the reduced
  component indexed by `q` has stalk exactly `q`, in the spelling the previous statement needs.
* `Stacks.Chow.exists_subschemeι_vanishingIdeal_closure_eq` — `ξ` is a point of that component,
  so that the previous two compose at `ξ`.

What is **not** here is the passage from `Ring.ord` on the component to
`AlgebraicGeometry.Scheme.ord`, the order of vanishing of the rational function the section
represents: that is `Stacks.Chow.ord_eq_ringOrd_germ`, which wants `[IsIntegral]` on
the component — free, by
`AlgebraicGeometry.Scheme.IdealSheafData.isIntegral_subscheme_vanishingIdeal_closure` — and
`coheight ξ = 1` *on the component*, which is not free and is the one hypothesis this route still
owes. See the implementation notes.

## Implementation notes

**Two spellings of the stalk of an ideal sheaf are in the tree and there was no bridge.**
`AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal` (in
`StacksFrontier.AlgebraicGeometry.Morphisms.Support.FibreStalkBridges`) is an `⨆` over the subtype
`{U : X.affineOpens // x ∈ U}`, while `AlgebraicGeometry.IdealSheafData.stalk` (in
`StacksFrontier.AlgebraicGeometry.Divisors.FittingIdeals.Basic`) is the same supremum written as an
iterated `⨆ (U) (hx : x ∈ U)`. They are equal by `iSup_subtype'` and nothing more, but each has
its own consumers — the subscheme stalk comparison is stated for the first and the
minimal-primes correspondence for the second — so the bridge is what lets the two be composed.
It is proved here because it is needed here; it belongs with one of the two definitions, and a
reader consolidating this area should move it.

**`Ring.ord` has no congruence under a ring isomorphism in Mathlib**, which is what forces
`Ring.ord_ringEquiv`. It is proved from `Module.length_eq_of_surjective_of_addEquiv` — the
semilinear length transfer of `StacksFrontier.RingTheory.Length.SemilinearTransfer` — applied to the
quotient isomorphism `Ideal.quotientEquiv`, since `Ring.ord R x` is by definition
`Module.length R (R ⧸ Ideal.span {x})`. `LinearEquiv.length_eq` is not enough on its own: the two
lengths are taken over *different* rings, so the transfer has to move the scalars as well as the
module.

**The remaining hypothesis.** `Stacks.Chow.ord_eq_ringOrd_germ` takes `coheight ξ = 1` in the
component, which is where the one-dimensionality of the local ring enters on that side. In the
situation of part (4) of [Stacks, Tag 02SW] what is available is
`ringKrullDim 𝒪_{X, ξ} = 1`, from
`Stacks.Chow.StalkLocalSituation.ringKrullDim_stalk_eq_one_of_mem_isNowhereDense`, and the
component's local ring at `ξ` is `𝒪_{X, ξ} ⧸ q` for a *minimal* `q` — so its Krull dimension is
at most one, and the question is whether it is exactly one. That is not proved here and is not
assumed here: the statements above are hypothesis-free and stop short of `Scheme.ord` precisely
so that the hypothesis is not smuggled in.

The compatibility of the subscheme comparison with the projection,
`AlgebraicGeometry.Scheme.IdealSheafData.subschemeStalkRingEquiv_toSubschemeStalk`, holds by
`rfl`, so the two `Ring.ord`s are compared at the same element without a further bridge.

## References

* [Stacks Project, Tag 02SW](https://stacks.math.columbia.edu/tag/02SW)
* [Stacks Project, Tag 02QH](https://stacks.math.columbia.edu/tag/02QH)
* [Stacks Project, Tag 02MD](https://stacks.math.columbia.edu/tag/02MD)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory TopologicalSpace

universe u

/-- **The order of vanishing is invariant under a ring isomorphism.** Mathlib's `Ring.ord` API
has no congruence under a `RingEquiv`; this is it, proved by transporting the length of the
quotient by the principal ideal along the induced quotient isomorphism. -/
theorem Ring.ord_ringEquiv {R T : Type*} [CommRing R] [CommRing T] (φ : R ≃+* T) (x : R) :
    Ring.ord R x = Ring.ord T (φ x) := by
  have hspan : Ideal.span {φ x} = (Ideal.span {x}).map (φ : R →+* T) := by
    rw [Ideal.map_span, Set.image_singleton]
    rfl
  change Module.length R (R ⧸ Ideal.span {x}) = Module.length T (T ⧸ Ideal.span {φ x})
  refine Module.length_eq_of_surjective_of_addEquiv (φ : R →+* T) φ.surjective
    (Ideal.quotientEquiv (Ideal.span {x}) (Ideal.span {φ x}) φ hspan).symm.toAddEquiv ?_
  intro r n
  obtain ⟨m, rfl⟩ := Ideal.Quotient.mk_surjective n
  change Ideal.Quotient.mk (Ideal.span {x}) (φ.symm (φ r * m)) =
    Ideal.Quotient.mk (Ideal.span {x}) (r * φ.symm m)
  rw [map_mul, φ.symm_apply_apply]

namespace AlgebraicGeometry.Scheme.IdealSheafData

variable {X : Scheme.{u}}

/-- **The two spellings of the stalk of an ideal sheaf agree.** One is an `⨆` over a subtype of
affine opens containing the point, the other the same supremum written as an iterated `⨆`. -/
theorem stalkIdeal_eq_stalk (I : X.IdealSheafData) (x : X) :
    I.stalkIdeal x = AlgebraicGeometry.IdealSheafData.stalk I x :=
  le_antisymm
    (iSup_le fun U => le_iSup_of_le U.1 (le_iSup_of_le U.2 le_rfl))
    (iSup_le fun U => iSup_le fun hx => le_iSup_of_le ⟨U, hx⟩ le_rfl)

end AlgebraicGeometry.Scheme.IdealSheafData

namespace Stacks.Chow

variable {X : Scheme.{u}}

/-- **The order of vanishing in the stalk of a closed subscheme.** For `z` a point of the closed
subscheme cut out by `I`, the order of vanishing of the image of a germ `r` in `𝒪_{X,x} / I_x` is
its order of vanishing in the local ring of the subscheme at `z`. -/
theorem ord_subschemeStalk (I : X.IdealSheafData) (z : I.subscheme)
    (r : X.presheaf.stalk (I.subschemeι z)) :
    Ring.ord (X.presheaf.stalk (I.subschemeι z) ⧸ I.stalkIdeal (I.subschemeι z))
        (Ideal.Quotient.mk (I.stalkIdeal (I.subschemeι z)) r) =
      Ring.ord (I.subscheme.presheaf.stalk z) ((I.subschemeι.stalkMap z).hom r) :=
  Ring.ord_ringEquiv (I.subschemeStalkRingEquiv z) _

/-- **The ideal of the reduced component indexed by `q` has stalk exactly `q`**, in the
`stalkIdeal` spelling that the subscheme-stalk comparison is stated for. This is
`Stacks.Chow.idealStalk_vanishingIdeal_closure_fromSpecStalk` carried across
`AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_stalk`. -/
theorem stalkIdeal_vanishingIdeal_closure_fromSpecStalk (ξ : X)
    (q : PrimeSpectrum (X.presheaf.stalk ξ)) :
    (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({X.fromSpecStalk ξ q} : Set X))).stalkIdeal ξ = q.asIdeal :=
  (AlgebraicGeometry.Scheme.IdealSheafData.stalkIdeal_eq_stalk _ ξ).trans
    (idealStalk_vanishingIdeal_closure_fromSpecStalk ξ q)

/-- **The point `ξ` is a point of the reduced component indexed by `q`.** It lies in the closure
of the generic point of that component, which is the support of the component's ideal sheaf, and
the subscheme inclusion has the support as its range. -/
theorem exists_subschemeι_vanishingIdeal_closure_eq (ξ : X)
    (q : PrimeSpectrum (X.presheaf.stalk ξ)) :
    ∃ z : (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({X.fromSpecStalk ξ q} : Set X))).subscheme,
      (Scheme.IdealSheafData.vanishingIdeal
        (Closeds.closure ({X.fromSpecStalk ξ q} : Set X))).subschemeι z = ξ := by
  have hgen : X.fromSpecStalk ξ q ⤳ ξ := by
    have h : X.fromSpecStalk ξ q ∈ Set.range ⇑(X.fromSpecStalk ξ) := ⟨q, rfl⟩
    rwa [Scheme.range_fromSpecStalk] at h
  have hmem : ξ ∈ ((Scheme.IdealSheafData.vanishingIdeal
      (Closeds.closure ({X.fromSpecStalk ξ q} : Set X))).support : Set X) := by
    rw [Scheme.IdealSheafData.coe_support_vanishingIdeal, Closeds.coe_closure]
    exact hgen.mem_closure
  rwa [← Scheme.IdealSheafData.range_subschemeι] at hmem

end Stacks.Chow

end
