module

public import StacksFrontier.AlgebraicGeometry.Crystalline.CrystallineDifferentials
public import StacksFrontier.AlgebraicGeometry.Crystalline.ModuleDifferentials.Diagonal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SelfProductDiagonal

/-!
# The conormal module of the diagonal of a self-product

Fix a global crystalline situation `(p, (S, I, γ), X)` and let `(U(1), T(1), δ(1))` be a product
of an object `(U, T, δ)` of the small crystalline site `Cris(X/S)` with itself, presented by a
limit binary fan with projections `pr₀, pr₁`.  Write `p₀, p₁ : T(1) ⟶ T` for the ambient
components of the two projections and `Δ : T ⟶ T(1)` for the ambient component of the diagonal,
and let `K ⊆ 𝒪_{T(1)}` be the diagonal ideal, the kernel of `Δ` on sections.

[Stacks, Tag 07J1] asserts first that `K ⊆ J_{T(1)}` is preserved by the divided structure, which
is proved in `StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductDiagonal.lean`, and second
that `(Ω_{X/S})_T = K/K^{[2]}`.  This module builds the second assertion's objects and its
comparison map: the divided square `K^{[2]}`, the conormal module `K/K^{[2]}` as a module over
the sections of `𝒪_T`, and a comparison map from the divided power differentials of `T` over `S`
— which is `(Ω_{X/S})_T` by [Stacks, Tag 07IZ] — carrying the universal divided power
differential of `f` to the class of `p₁^♯ f - p₀^♯ f`.

## Main definitions

* `Crystalline.GlobalCrystallineSituation.smallSelfProductDividedSquare` — the divided square
  `K^{[2]} = K² + ⟨δ(1)_n(k) : n ≥ 2, k ∈ K⟩` on an open of `T(1)`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductOpen` — the open `p₀⁻¹V ⊓ p₁⁻¹V` of
  `T(1)` over an open `V` of `T`, on which both coprojections act on sections.
* `Crystalline.GlobalCrystallineSituation.firstCoprojectionSection` and
  `secondCoprojectionSection` — the two coprojections on sections over that open.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductConormal` — the conormal module
  `K/K^{[2]}` over `Γ(V, 𝒪_T)`, the scalars acting through the first coprojection.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductDifference` — the class of
  `p₁^♯ f - p₀^♯ f` in the conormal module.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductConormalDerivation` — that map read as
  a divided power derivation of `Γ(V, 𝒪_T)` over the global sections of the base.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductConormalComparison` — the induced
  comparison map out of the divided power differentials of `T` over `S` on an open of `T`.
* `Crystalline.GlobalCrystallineSituation.restrictedCrysDifferentialsConormalComparison` — the
  same map read out of `(Ω_{X/S})_T`, through [Stacks, Tag 07IZ].
* `Crystalline.GlobalCrystallineSituation.smallSelfProductRestrict` and
  `smallSelfProductRestrictIdeal` — restriction of sections of `𝒪_{T(1)}`, and of sections of the
  diagonal ideal, along `p₀⁻¹V' ⊓ p₁⁻¹V' ≤ p₀⁻¹V ⊓ p₁⁻¹V`.

## Main results

* `Crystalline.GlobalCrystallineSituation.smallSelfProductDividedSquare_le` — `K^{[2]} ⊆ K`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductDividedSquare_isSubDPIdeal` —
  `K^{[2]}` is itself preserved by the divided structure on `J_{T(1)}`.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductDifference_add`,
  `smallSelfProductDifference_mul`, `smallSelfProductDifference_base` and
  `smallSelfProductDifference_dpow` — additivity, the Leibniz rule, the vanishing on sections
  pulled back from the base, and the divided power chain rule for `f ↦ [p₁^♯ f - p₀^♯ f]`; these
  are what make the comparison map exist.
* `Crystalline.GlobalCrystallineSituation.smallSelfProductConormalComparison_d` — the comparison
  map carries the universal divided power differential of `f` to the class of
  `p₁^♯ f - p₀^♯ f`.
* `Crystalline.GlobalCrystallineSituation.comparisonIsoApp_comp_conormalComparison` — the
  comparison map out of `(Ω_{X/S})_T` agrees with it through [Stacks, Tag 07IZ].
* `Crystalline.GlobalCrystallineSituation.smallSelfProductDifferenceHom_restrict` — the
  difference of the two coprojections commutes with restriction to a smaller open of `T`; with
  `map_smallSelfProductDiagonalIdeal_le` and `map_smallSelfProductDividedSquare_le`, which say
  that restriction preserves `K` and `K^{[2]}`, this is the compatibility of the comparison with
  restriction, read on representatives.
* `Crystalline.GlobalCrystallineSituation.isClosedImmersion_smallSelfProductAmbientDiagonal` —
  **Stacks, Tag 07J1**: the ambient diagonal `Δ : T ⟶ T(1)` is a closed immersion.
* `Crystalline.GlobalCrystallineSituation.ker_ideal_smallSelfProductAmbientDiagonal` — on an
  affine open of `T(1)` the quasi-coherent sheaf of ideals of that closed immersion is the
  diagonal ideal `K`.

## Implementation notes

As in `SelfProductDiagonal.lean` the product is supplied as limit data,
`IsLimit (BinaryFan.mk pr₀ pr₁)`, rather than constructed.  That is generality, not a gap: the
library does have the existence half of [Stacks, Tag 07I9], as the unconditional instance
`Crystalline.GlobalCrystallineSituation.instHasBinaryProductsThickening` together with
`Crystalline.GlobalCrystallineSituation.hasLimitsOfShape` for the small site, so such limit data
always exist.

An open of `T(1)` relevant to the comparison is addressed by the open `V` of `T` it lies over:
`smallSelfProductOpen pr₀ pr₁ V` is `p₀⁻¹V ⊓ p₁⁻¹V`, which both coprojections map into with no
side condition, so `p₀^♯` and `p₁^♯` are `Scheme.Hom.appLE` at `smallSelfProductOpen_le_fst` and
`smallSelfProductOpen_le_snd`.  The diagonal pulls that open back to `V`, which is why the two
coprojections become equal after `Δ^♯` and the difference `p₁^♯ f - p₀^♯ f` lands in `K`.

`K^{[2]}` is written as `K² + ⟨δ(1)_n(k) : n ≥ 2, k ∈ K⟩`, the second summand being
`Crystalline.secondDividedPowerIdeal`.  The affine statement [Stacks, Tag 07HT] intersects `K`
with `J_{T(1)}` in that summand because over a general base the containment `K ⊆ J_{T(1)}` is not
available; here it is, by `smallSelfProductDiagonalIdeal_le`, so the intersection is `K` and the
definition is the `K^{[2]}` of the source with no intersection written.

`(Ω_{X/S})_T` is the restriction of the presheaf `Ω_{X/S}` to the opens of `T`, which by
[Stacks, Tag 07IZ] — `Crystalline.GlobalCrystallineSituation.comparisonIsoApp` — is the presheaf
`Crystalline.dpDifferentialsPresheaf` of divided power differentials of `T` over `S`.  The
comparison map is therefore built out of the latter, by the universal property
`Crystalline.dpConstDesc` of its sections, and then transported; both forms are recorded.

The arithmetic lemma behind the divided power chain rule appears here as
`dpow_add_sub_sub_mem_secondDividedPowerIdeal`.  A computation of the same kind is made inside
`StacksFrontier/AlgebraicGeometry/Crystalline/ModuleDifferentials/Diagonal.lean`, but privately.

## What is and is not proved

The first assertion of [Stacks, Tag 07J1] is proved in `SelfProductDiagonal.lean`.  Of the second
assertion, `(Ω_{X/S})_T = K/K^{[2]}`, what is proved here is that both sides exist and that there
is a canonical map from the left to the right carrying the universal divided power differential to
the difference of the two coprojections — the map the source's equality is an equality of.

That map **is** an isomorphism over an affine open `V` of `T` lying over an affine open of `S`,
which is where the source's proof establishes it: the source works affine locally on `T`.  The
proof is split over three further modules.

`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormalThickening.lean` builds the map
back.  The first-order universal thickening `T'` of [Stacks, Tag 07J2] receives a unique morphism
`q : T' ⟶ T(1)` from the universal property of the product, and the `Ω`-coordinate of `q` on
sections is a map `K/K^{[2]} → Ω_{T/S,δ}(V)`, `smallSelfProductConormalInverse`, which composed
after the comparison above is the canonical map from the presheaf of divided power differentials
to the sheaf it generates.

`StacksFrontier/AlgebraicGeometry/Crystalline/DifferentialsAffinePresheaf.lean` settles the
presheaf-versus-sheaf mismatch that this leaves.  The comparison map here is a map out of the
*presheaf* `Crystalline.dpDifferentialsPresheaf`, whose sections over `V` are
`Crystalline.dpConstDifferentials` — the divided power differentials of `Γ(V, 𝒪_T)` modulo the
differentials of *every* section pulled back from *some* open of `S`, which is
`Crystalline.baseSections` — while the first-order thickening is built from the sheafification
`Crystalline.dpDifferentialsSheaf`.  On an affine open `V` lying over an affine open of `S` the
canonical map between them is bijective,
`Crystalline.bijective_dpDifferentialsToSheaf_app`, by [Stacks, Tag 07IY] clause (2),
`Crystalline.affineSectionsEquiv`.  In particular the comparison map is injective there.

`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormalIso.lean` supplies surjectivity —
equivalently that `K` is generated modulo `K^{[2]}` by the differences of the two coprojections,
equivalently injectivity of `smallSelfProductConormalInverse`.  It is the *uniqueness* half of
the product's universal property, tested against the square-zero extension
`Γ(V, 𝒪_T) ⊕ K/K^{[2]}`: that extension is the quotient of `Γ(p₀⁻¹V ⊓ p₁⁻¹V, 𝒪_{T(1)})` by
`K^{[2]}`, so `Spec` of it is a closed subscheme of an affine open of `T(1)` — the open
`p₀⁻¹V ⊓ p₁⁻¹V` being affine by Limits, [Stacks, Tag 01ZT], applied to the restriction of the
diagonal, which is `isAffineOpen_smallSelfProductOpen` in
`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormalAffine.lean` — and it carries two
morphisms to `T(1)` which agree after both projections and are therefore equal.  Realising that
quotient as an object of `Cris(X/S)` is
`Crystalline.GlobalCrystallineSituation.affineQuotientCrystalline` in
`StacksFrontier/AlgebraicGeometry/Crystalline/CrystallineAffineQuotient.lean`, built from
`Crystalline.DividedPowerScheme.specDividedPowerScheme`.

The affineness hypotheses are hypotheses of the source's *proof* and not of its statement, and
they are discharged: the affine opens over affine opens of `S` form a basis, by
`Crystalline.exists_isAffineOpen_over_isAffineOpen`, so the comparison is an isomorphism on a
neighbourhood of every point of every open of `T`, and the opens on which it is one form a basis
of the topology of `T`.  That is
`Crystalline.GlobalCrystallineSituation.exists_isIso_restrictedCrysDifferentialsConormalComparison`
and `isBasis_isIso_restrictedCrysDifferentialsConormalComparison` in
`SelfProductConormalIso.lean`, which carry the tag for the second assertion.

What is **not** proved is the globalisation as a single morphism: the comparison is not assembled
into an isomorphism of sheaves of `𝒪_T`-modules on all of `T`.  The comparison is compatible with
restriction on representatives by `smallSelfProductDifferenceHom_restrict` below; but `K/K^{[2]}`
is built open by open here rather than as a sheaf, for the reason given below, so there is no
morphism of sheaves to call an isomorphism.

No *coproduct datum* is needed for any of this: [Stacks, Tag 07HT] and [Stacks, Tag 07HV] — in
the library as `Crystalline.Pushout.dividedPowerDifferentialsEquivDiagonalConormal` and
`Crystalline.dividedPowerDifferentialsEquivDiagonalConormal` — do take the self-product as an
`IsPushout` square respectively an `IsColimit` of a binary cofan, but the route above goes through
`T'` and the product's own universal property instead.  A `GlobalCrystallineSituation` and the
`AffineCrystallineSituation` of [Stacks, Tag 07MD] are related by the bridge
`Crystalline.GlobalCrystallineSituation.affineSituation` and `wholeThickeningToAffine` in
`StacksFrontier/AlgebraicGeometry/Crystalline/SmallSite/AffineGlobalBridge.lean`, which do carry the
hypothesis that `p` is nilpotent on the global sections of `X`.

As in `SelfProductDiagonal.lean`, `K` is presented open by open as a kernel on sections.  That
presentation is reconciled with the source's here: the ambient diagonal is a closed immersion, by
`isClosedImmersion_smallSelfProductAmbientDiagonal`, so it has a quasi-coherent sheaf of ideals —
Mathlib's `AlgebraicGeometry.Scheme.Hom.ker` — and on every affine open of `T(1)` the ideal of
that sheaf is the kernel on sections, by `ker_ideal_smallSelfProductAmbientDiagonal`.  Since a
quasi-coherent ideal sheaf is determined by its values on affine opens, the two readings of `K`
agree.

`K^{[2]}` and `K/K^{[2]}` are nevertheless still built open by open.  The divided second power
exists only for an ideal of a ring, as `Crystalline.secondDividedPowerIdeal`; the library has no
divided power of a quasi-coherent subsheaf of the structure sheaf, and no `IsSubDPIdeal`-style
notion for one.  So the conormal family is indexed by the opens of `T` through
`smallSelfProductOpen`, and the comparison is a family of `Γ(V, 𝒪_T)`-linear maps on those opens
together with the restriction compatibilities above, rather than a morphism of
`PresheafOfModules`-objects.

## References

* [Stacks Project, Tag 07J1](https://stacks.math.columbia.edu/tag/07J1)
* [Stacks Project, Tag 07HT](https://stacks.math.columbia.edu/tag/07HT)
* [Stacks Project, Tag 07HV](https://stacks.math.columbia.edu/tag/07HV)
* [Stacks Project, Tag 07IZ](https://stacks.math.columbia.edu/tag/07IZ)
* [Stacks Project, Tag 07I9](https://stacks.math.columbia.edu/tag/07I9)
* [Stacks Project, Tag 07MD](https://stacks.math.columbia.edu/tag/07MD)
* [Stacks Project, Tag 07MF](https://stacks.math.columbia.edu/tag/07MF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u

namespace Crystalline.GlobalCrystallineSituation

variable {S : GlobalCrystallineSituation.{u}} {B D : CrystallineThickening S} {pr₀ pr₁ : D ⟶ B}


/-! ### Two auxiliary facts about divided powers -/

/-- **A map on sections of a morphism of divided power schemes cut down to a smaller open is a
homomorphism of divided power rings.**  It is the map on sections over the larger open followed by
a restriction map, and both are compatible with the divided power structures. -/
theorem appLE_isDPMorphism {X Y : DividedPowerScheme.{u}} (f : X ⟶ Y) (W : Y.scheme.Opens)
    (V : X.scheme.Opens) (e : V ≤ f.hom ⁻¹ᵁ W) :
    (Y.dividedPowers.dividedPowers (op W)).IsDPMorphism
      (X.dividedPowers.dividedPowers (op V)) (f.hom.appLE W V e).hom :=
  DividedPowers.IsDPMorphism.comp _ (X.dividedPowers.naturality (homOfLE e).op) (f.compatible W)

/-- **Equal morphisms of schemes induce the same map on sections cut down to the same pair of
opens.**  The two containment hypotheses prove the same proposition once the morphisms are
identified. -/
theorem appLE_congr_hom {X Y : Scheme.{u}} {f g : X ⟶ Y} (hfg : f = g) (W : Y.Opens)
    (V : X.Opens) (ef : V ≤ f ⁻¹ᵁ W) (eg : V ≤ g ⁻¹ᵁ W) :
    f.appLE W V ef = g.appLE W V eg := by
  subst hfg
  rfl

/-- **Translating the argument of a divided power of positive order by an element of an ideal `K`
changes it by the linear term, modulo the divided powers of order at least two of `K`.**  Expand
`δ_{n+1}(x + t)` by the addition formula: the term of index `0` is `δ_{n+1}(x)`, the term of index
`1` is `δ_n(x) t`, and every later term carries a divided power of `t` of order at least two. -/
theorem dpow_add_sub_sub_mem_secondDividedPowerIdeal {R : Type u} [CommRing R]
    {J : Ideal R} (δ : DividedPowers J) (K : Ideal R) (x t : R) (n : ℕ) (hx : x ∈ J)
    (htK : t ∈ K) (htJ : t ∈ J) :
    δ.dpow (n + 1) (x + t) - δ.dpow (n + 1) x - δ.dpow n x * t ∈
      secondDividedPowerIdeal δ K := by
  have hsum : δ.dpow (n + 1) (x + t) =
      (Finset.range (n + 2)).sum (fun k ↦ δ.dpow k t * δ.dpow (n + 1 - k) x) := by
    rw [add_comm x t]
    exact δ.dpow_add' htJ hx
  have h0 : 0 ∈ Finset.range (n + 2) := by simp
  have h1 : 1 ∈ (Finset.range (n + 2)).erase 0 :=
    Finset.mem_erase.mpr ⟨one_ne_zero, by simp⟩
  have hsplit : (Finset.range (n + 2)).sum (fun k ↦ δ.dpow k t * δ.dpow (n + 1 - k) x) =
      (((Finset.range (n + 2)).erase 0).erase 1).sum
          (fun k ↦ δ.dpow k t * δ.dpow (n + 1 - k) x) +
        δ.dpow 1 t * δ.dpow (n + 1 - 1) x + δ.dpow 0 t * δ.dpow (n + 1 - 0) x := by
    rw [← Finset.sum_erase_add (Finset.range (n + 2)) _ h0,
      ← Finset.sum_erase_add ((Finset.range (n + 2)).erase 0) _ h1]
  have hrest : (((Finset.range (n + 2)).erase 0).erase 1).sum
      (fun k ↦ δ.dpow k t * δ.dpow (n + 1 - k) x) ∈ secondDividedPowerIdeal δ K := by
    refine Ideal.sum_mem _ fun k hk ↦ ?_
    have hk1 : k ≠ 1 := (Finset.mem_erase.mp hk).1
    have hk0 : k ≠ 0 := (Finset.mem_erase.mp (Finset.mem_erase.mp hk).2).1
    exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨k, by omega, t, htK, rfl⟩)
  have hid : δ.dpow (n + 1) (x + t) - δ.dpow (n + 1) x - δ.dpow n x * t =
      (((Finset.range (n + 2)).erase 0).erase 1).sum
        (fun k ↦ δ.dpow k t * δ.dpow (n + 1 - k) x) := by
    rw [hsum, hsplit, δ.dpow_zero htJ, δ.dpow_one htJ, Nat.add_sub_cancel, Nat.sub_zero, one_mul]
    ring
  rw [hid]
  exact hrest

/-- **A divided power of positive order changes by the linear term when its argument moves by an
element of an ideal `K`, modulo the divided powers of order at least two of `K`.**  The same
statement as `dpow_add_sub_sub_mem_secondDividedPowerIdeal` with the two arguments given rather
than one argument and the displacement. -/
theorem dpow_sub_sub_mem_secondDividedPowerIdeal {R : Type u} [CommRing R]
    {J : Ideal R} (δ : DividedPowers J) (K : Ideal R) (x y : R) (n : ℕ) (hx : x ∈ J)
    (hyK : y - x ∈ K) (hyJ : y - x ∈ J) :
    δ.dpow (n + 1) y - δ.dpow (n + 1) x - δ.dpow n x * (y - x) ∈
      secondDividedPowerIdeal δ K := by
  have hmem := dpow_add_sub_sub_mem_secondDividedPowerIdeal δ K x (y - x) n hx hyK hyJ
  have hxy : x + (y - x) = y := by ring
  rw [hxy] at hmem
  exact hmem

/-! ### The divided square of the diagonal ideal -/

section DividedSquare

/-- **The divided square `K^{[2]}` of the diagonal ideal** on an open `W` of `T(1)`: the sum of
the square of `K` and the ideal generated by the divided powers of order at least two of the
elements of `K`.  Over the small crystalline site `K ⊆ J_{T(1)}`, so those divided powers are
defined, and this is the `K^{[2]}` of [Stacks, Tag 07J1]. -/
def smallSelfProductDividedSquare (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (W : D.obj.thickening.target.scheme.Opens) :
    Ideal Γ(D.obj.thickening.target.scheme, W) :=
  smallSelfProductDiagonalIdeal h W ^ 2 +
    (secondDividedPowerIdeal (D.obj.thickening.target.dividedPowers.dividedPowers (op W))
      (smallSelfProductDiagonalIdeal h W) : Ideal Γ(D.obj.thickening.target.scheme, W))

/-- The square of the diagonal ideal is contained in its divided square. -/
theorem sq_le_smallSelfProductDividedSquare (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (W : D.obj.thickening.target.scheme.Opens) :
    smallSelfProductDiagonalIdeal h W ^ 2 ≤ smallSelfProductDividedSquare h W := by
  rw [smallSelfProductDividedSquare, Ideal.add_eq_sup]
  exact le_sup_left

/-- The divided powers of order at least two of the diagonal ideal lie in its divided square. -/
theorem secondDividedPowerIdeal_le_smallSelfProductDividedSquare
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (W : D.obj.thickening.target.scheme.Opens) :
    (secondDividedPowerIdeal (D.obj.thickening.target.dividedPowers.dividedPowers (op W))
        (smallSelfProductDiagonalIdeal h W) : Ideal Γ(D.obj.thickening.target.scheme, W)) ≤
      smallSelfProductDividedSquare h W := by
  rw [smallSelfProductDividedSquare, Ideal.add_eq_sup]
  exact le_sup_right

/-- **Stacks Project, Tag 07J1.**  The divided square of the diagonal ideal is a sub-ideal of the
diagonal ideal: the square of an ideal is contained in it, and the diagonal ideal is preserved by
the divided powers of `J_{T(1)}`. -/
@[stacks 07J1 "second assertion: K^{[2]} is a sub-ideal of K; sections over each open of T(1)"]
theorem smallSelfProductDividedSquare_le (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (W : D.obj.thickening.target.scheme.Opens) :
    smallSelfProductDividedSquare h W ≤ smallSelfProductDiagonalIdeal h W := by
  rw [smallSelfProductDividedSquare, Ideal.add_eq_sup]
  refine sup_le (Ideal.pow_le_self two_ne_zero) (Ideal.span_le.mpr ?_)
  rintro y ⟨n, hn, x, hx, rfl⟩
  exact (smallSelfProductDiagonalIdeal_isSubDPIdeal h W).dpow_mem n (by omega) hx

/-- **The divided square is itself preserved by the divided structure on `J_{T(1)}`.**  A divided
power of order one is the element itself, and a divided power of order at least two of an element
of the divided square is a generator of the divided square, the divided square being contained in
the diagonal ideal. -/
theorem smallSelfProductDividedSquare_isSubDPIdeal (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (W : D.obj.thickening.target.scheme.Opens) :
    (D.obj.thickening.target.dividedPowers.dividedPowers (op W)).IsSubDPIdeal
      (smallSelfProductDividedSquare h W) := by
  have hle := smallSelfProductDividedSquare_le h W
  have hKJ := smallSelfProductDiagonalIdeal_le h W
  refine ⟨hle.trans hKJ, fun n hn y hy ↦ ?_⟩
  rcases Nat.lt_or_ge n 2 with hn2 | hn2
  · obtain rfl : n = 1 := by omega
    rwa [(D.obj.thickening.target.dividedPowers.dividedPowers (op W)).dpow_one (hKJ (hle hy))]
  · exact secondDividedPowerIdeal_le_smallSelfProductDividedSquare h W
      (Ideal.subset_span ⟨n, hn2, y, hle hy, rfl⟩)

end DividedSquare

/-! ### The opens of `T(1)` over an open of `T`, and the coprojections on sections -/

section Coprojections

/-- **The open `p₀⁻¹V ⊓ p₁⁻¹V` of `T(1)` over an open `V` of `T`.**  Both coprojections map it
into `V`, so both act on sections over it, and the diagonal pulls it back to `V`. -/
def smallSelfProductOpen (pr₀ pr₁ : D ⟶ B) (V : B.obj.thickening.target.scheme.Opens) :
    D.obj.thickening.target.scheme.Opens :=
  pr₀.hom.targetHom.hom ⁻¹ᵁ V ⊓ pr₁.hom.targetHom.hom ⁻¹ᵁ V

/-- The first coprojection maps `p₀⁻¹V ⊓ p₁⁻¹V` into `V`. -/
theorem smallSelfProductOpen_le_fst (pr₀ pr₁ : D ⟶ B)
    (V : B.obj.thickening.target.scheme.Opens) :
    smallSelfProductOpen pr₀ pr₁ V ≤ pr₀.hom.targetHom.hom ⁻¹ᵁ V := inf_le_left

/-- The second coprojection maps `p₀⁻¹V ⊓ p₁⁻¹V` into `V`. -/
theorem smallSelfProductOpen_le_snd (pr₀ pr₁ : D ⟶ B)
    (V : B.obj.thickening.target.scheme.Opens) :
    smallSelfProductOpen pr₀ pr₁ V ≤ pr₁.hom.targetHom.hom ⁻¹ᵁ V := inf_le_right

/-- The open over a smaller open is smaller. -/
theorem smallSelfProductOpen_mono (pr₀ pr₁ : D ⟶ B)
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V) :
    smallSelfProductOpen pr₀ pr₁ V' ≤ smallSelfProductOpen pr₀ pr₁ V :=
  inf_le_inf (fun _ hz ↦ hle hz) (fun _ hz ↦ hle hz)

/-- The ambient diagonal is a section of the ambient component of the first projection. -/
theorem ambientDiagonal_comp_fst (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    (smallSelfProductAmbientDiagonal h).hom ≫ pr₀.hom.targetHom.hom = 𝟙 _ :=
  congrArg (fun φ : B ⟶ B ↦ φ.hom.targetHom.hom) (smallSelfProductDiagonal_fst h)

/-- The ambient diagonal is a section of the ambient component of the second projection. -/
theorem ambientDiagonal_comp_snd (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    (smallSelfProductAmbientDiagonal h).hom ≫ pr₁.hom.targetHom.hom = 𝟙 _ :=
  congrArg (fun φ : B ⟶ B ↦ φ.hom.targetHom.hom) (smallSelfProductDiagonal_snd h)

/-- **The diagonal pulls `p₀⁻¹V ⊓ p₁⁻¹V` back to `V`.**  Both composites of the diagonal with a
coprojection are the identity. -/
theorem diagonal_preimage_smallSelfProductOpen (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    (smallSelfProductAmbientDiagonal h).hom ⁻¹ᵁ smallSelfProductOpen pr₀ pr₁ V = V := by
  have hrw : (smallSelfProductAmbientDiagonal h).hom ⁻¹ᵁ smallSelfProductOpen pr₀ pr₁ V =
      ((smallSelfProductAmbientDiagonal h).hom ≫ pr₀.hom.targetHom.hom) ⁻¹ᵁ V ⊓
        ((smallSelfProductAmbientDiagonal h).hom ≫ pr₁.hom.targetHom.hom) ⁻¹ᵁ V := rfl
  rw [hrw, ambientDiagonal_comp_fst h, ambientDiagonal_comp_snd h]
  simp

/-- **`p₀^♯ : Γ(V, 𝒪_T) ⟶ Γ(p₀⁻¹V ⊓ p₁⁻¹V, 𝒪_{T(1)})`**, the first coprojection on sections. -/
def firstCoprojectionSection (pr₀ pr₁ : D ⟶ B) (V : B.obj.thickening.target.scheme.Opens) :
    Γ(B.obj.thickening.target.scheme, V) ⟶
      Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V) :=
  pr₀.hom.targetHom.hom.appLE V (smallSelfProductOpen pr₀ pr₁ V)
    (smallSelfProductOpen_le_fst pr₀ pr₁ V)

/-- **`p₁^♯ : Γ(V, 𝒪_T) ⟶ Γ(p₀⁻¹V ⊓ p₁⁻¹V, 𝒪_{T(1)})`**, the second coprojection on sections. -/
def secondCoprojectionSection (pr₀ pr₁ : D ⟶ B) (V : B.obj.thickening.target.scheme.Opens) :
    Γ(B.obj.thickening.target.scheme, V) ⟶
      Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V) :=
  pr₁.hom.targetHom.hom.appLE V (smallSelfProductOpen pr₀ pr₁ V)
    (smallSelfProductOpen_le_snd pr₀ pr₁ V)

/-- The first coprojection on sections is a homomorphism of divided power rings. -/
theorem firstCoprojectionSection_isDPMorphism (pr₀ pr₁ : D ⟶ B)
    (V : B.obj.thickening.target.scheme.Opens) :
    (B.obj.thickening.target.dividedPowers.dividedPowers (op V)).IsDPMorphism
      (D.obj.thickening.target.dividedPowers.dividedPowers
        (op (smallSelfProductOpen pr₀ pr₁ V)))
      (firstCoprojectionSection pr₀ pr₁ V).hom :=
  appLE_isDPMorphism pr₀.hom.targetHom V (smallSelfProductOpen pr₀ pr₁ V)
    (smallSelfProductOpen_le_fst pr₀ pr₁ V)

/-- The second coprojection on sections is a homomorphism of divided power rings. -/
theorem secondCoprojectionSection_isDPMorphism (pr₀ pr₁ : D ⟶ B)
    (V : B.obj.thickening.target.scheme.Opens) :
    (B.obj.thickening.target.dividedPowers.dividedPowers (op V)).IsDPMorphism
      (D.obj.thickening.target.dividedPowers.dividedPowers
        (op (smallSelfProductOpen pr₀ pr₁ V)))
      (secondCoprojectionSection pr₀ pr₁ V).hom :=
  appLE_isDPMorphism pr₁.hom.targetHom V (smallSelfProductOpen pr₀ pr₁ V)
    (smallSelfProductOpen_le_snd pr₀ pr₁ V)

/-- **The two coprojections become equal after the diagonal.**  Composing either with the
diagonal gives restriction along `Δ⁻¹(p₀⁻¹V ⊓ p₁⁻¹V) = V`. -/
theorem secondCoprojectionSection_comp_diagonal_eq (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    secondCoprojectionSection pr₀ pr₁ V ≫
        (smallSelfProductAmbientDiagonal h).hom.app (smallSelfProductOpen pr₀ pr₁ V) =
      firstCoprojectionSection pr₀ pr₁ V ≫
        (smallSelfProductAmbientDiagonal h).hom.app (smallSelfProductOpen pr₀ pr₁ V) := by
  have hdiag : (smallSelfProductAmbientDiagonal h).hom ≫ pr₁.hom.targetHom.hom =
      (smallSelfProductAmbientDiagonal h).hom ≫ pr₀.hom.targetHom.hom := by
    rw [ambientDiagonal_comp_snd h, ambientDiagonal_comp_fst h]
  have hΔ : (smallSelfProductAmbientDiagonal h).hom.app (smallSelfProductOpen pr₀ pr₁ V) =
      (smallSelfProductAmbientDiagonal h).hom.appLE (smallSelfProductOpen pr₀ pr₁ V)
        ((smallSelfProductAmbientDiagonal h).hom ⁻¹ᵁ smallSelfProductOpen pr₀ pr₁ V) le_rfl :=
    Scheme.Hom.app_eq_appLE _
  have h1 := Scheme.Hom.appLE_comp_appLE (smallSelfProductAmbientDiagonal h).hom
    pr₁.hom.targetHom.hom V (smallSelfProductOpen pr₀ pr₁ V)
    ((smallSelfProductAmbientDiagonal h).hom ⁻¹ᵁ smallSelfProductOpen pr₀ pr₁ V)
    (smallSelfProductOpen_le_snd pr₀ pr₁ V) le_rfl
  have h0 := Scheme.Hom.appLE_comp_appLE (smallSelfProductAmbientDiagonal h).hom
    pr₀.hom.targetHom.hom V (smallSelfProductOpen pr₀ pr₁ V)
    ((smallSelfProductAmbientDiagonal h).hom ⁻¹ᵁ smallSelfProductOpen pr₀ pr₁ V)
    (smallSelfProductOpen_le_fst pr₀ pr₁ V) le_rfl
  rw [hΔ]
  exact h1.trans ((appLE_congr_hom hdiag V
    ((smallSelfProductAmbientDiagonal h).hom ⁻¹ᵁ smallSelfProductOpen pr₀ pr₁ V) _ _).trans
      h0.symm)

/-- **The difference of the two coprojections of a section lies in the diagonal ideal.** -/
theorem sub_coprojectionSection_mem (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (f : Γ(B.obj.thickening.target.scheme, V)) :
    secondCoprojectionSection pr₀ pr₁ V f - firstCoprojectionSection pr₀ pr₁ V f ∈
      smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V) := by
  have hap := congrArg
    (fun φ : Γ(B.obj.thickening.target.scheme, V) ⟶
        Γ(B.obj.thickening.target.scheme,
          (smallSelfProductAmbientDiagonal h).hom ⁻¹ᵁ smallSelfProductOpen pr₀ pr₁ V) ↦ φ f)
    (secondCoprojectionSection_comp_diagonal_eq h V)
  simp only [CommRingCat.comp_apply] at hap
  rw [RingHom.mem_ker, map_sub, hap, sub_self]

/-- **The two coprojections agree on a section pulled back from the base.**  The ambient
components of the two projections are both morphisms over the divided power base. -/
theorem coprojectionSection_base_eq (pr₀ pr₁ : D ⟶ B)
    (V : B.obj.thickening.target.scheme.Opens) {V' : S.S.scheme.Opens}
    (hle : V ≤ B.obj.toBase.hom ⁻¹ᵁ V') (a : Γ(S.S.scheme, V')) :
    secondCoprojectionSection pr₀ pr₁ V (B.obj.toBase.hom.appLE V' V hle a) =
      firstCoprojectionSection pr₀ pr₁ V (B.obj.toBase.hom.appLE V' V hle a) := by
  have hb1 : pr₁.hom.targetHom.hom ≫ B.obj.toBase.hom = D.obj.toBase.hom :=
    congrArg DividedPowerScheme.Hom.hom pr₁.hom.base_naturality
  have hb0 : pr₀.hom.targetHom.hom ≫ B.obj.toBase.hom = D.obj.toBase.hom :=
    congrArg DividedPowerScheme.Hom.hom pr₀.hom.base_naturality
  have h1 := Scheme.Hom.appLE_comp_appLE pr₁.hom.targetHom.hom B.obj.toBase.hom
    V' V (smallSelfProductOpen pr₀ pr₁ V) hle (smallSelfProductOpen_le_snd pr₀ pr₁ V)
  have h0 := Scheme.Hom.appLE_comp_appLE pr₀.hom.targetHom.hom B.obj.toBase.hom
    V' V (smallSelfProductOpen pr₀ pr₁ V) hle (smallSelfProductOpen_le_fst pr₀ pr₁ V)
  have key := h1.trans ((appLE_congr_hom (hb1.trans hb0.symm) V'
    (smallSelfProductOpen pr₀ pr₁ V) _ _).trans h0.symm)
  have hap := congrArg
    (fun φ : Γ(S.S.scheme, V') ⟶
        Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V) ↦ φ a) key
  change pr₁.hom.targetHom.hom.appLE V (smallSelfProductOpen pr₀ pr₁ V)
      (smallSelfProductOpen_le_snd pr₀ pr₁ V) (B.obj.toBase.hom.appLE V' V hle a) =
    pr₀.hom.targetHom.hom.appLE V (smallSelfProductOpen pr₀ pr₁ V)
      (smallSelfProductOpen_le_fst pr₀ pr₁ V) (B.obj.toBase.hom.appLE V' V hle a)
  simpa only [CommRingCat.comp_apply] using hap

/-! ### The diagonal on sections over an open of `T` -/

/-- **An endomorphism of a scheme that is the identity acts as the identity on sections cut down
to one open.**  Substituting the identity turns the map on sections into a composite of the
identity on sections with a restriction along the identity of the open. -/
private theorem appLE_eq_self {X : Scheme.{u}} (f : X ⟶ X) (hf : f = 𝟙 X) (U : X.Opens)
    (e : U ≤ f ⁻¹ᵁ U) (x : Γ(X, U)) : f.appLE U U e x = x := by
  subst hf
  have hid : (𝟙 X : X ⟶ X).appLE U U e = 𝟙 Γ(X, U) := by
    change Scheme.Hom.app (𝟙 X) U ≫ X.presheaf.map (homOfLE e).op = _
    rw [Scheme.Hom.id_app]
    change 𝟙 Γ(X, U) ≫ X.presheaf.map (𝟙 U).op = _
    rw [Category.id_comp]
    exact X.presheaf.map_id _
  rw [hid]
  rfl

/-- **`Δ^♯ : Γ(p₀⁻¹V ⊓ p₁⁻¹V, 𝒪_{T(1)}) ⟶ Γ(V, 𝒪_T)`**, the map on sections of the ambient
diagonal cut down to `V`.  The diagonal pulls `p₀⁻¹V ⊓ p₁⁻¹V` back to exactly `V`, so no
containment has to be chosen. -/
def smallSelfProductDiagonalSection (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V) ⟶
      Γ(B.obj.thickening.target.scheme, V) :=
  (smallSelfProductAmbientDiagonal h).hom.appLE (smallSelfProductOpen pr₀ pr₁ V) V
    (le_of_eq (diagonal_preimage_smallSelfProductOpen h V).symm)

/-- **`Δ^♯` splits a coprojection.**  The composite of the diagonal with a morphism `g` that is a
retraction of it, with `g` mapping `p₀⁻¹V ⊓ p₁⁻¹V` into `V`, is the identity on sections. -/
private theorem smallSelfProductDiagonalSection_appLE
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (g : D.obj.thickening.target.scheme ⟶
      B.obj.thickening.target.scheme)
    (hg : (smallSelfProductAmbientDiagonal h).hom ≫ g = 𝟙 _)
    (V : B.obj.thickening.target.scheme.Opens) (e : smallSelfProductOpen pr₀ pr₁ V ≤ g ⁻¹ᵁ V)
    (f : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductDiagonalSection h V (g.appLE V (smallSelfProductOpen pr₀ pr₁ V) e f) = f := by
  have hc := Scheme.Hom.appLE_comp_appLE (smallSelfProductAmbientDiagonal h).hom g V
    (smallSelfProductOpen pr₀ pr₁ V) V e
    (le_of_eq (diagonal_preimage_smallSelfProductOpen h V).symm)
  have hap := congrArg
    (fun φ : Γ(B.obj.thickening.target.scheme, V) ⟶
        Γ(B.obj.thickening.target.scheme, V) ↦ φ f) hc
  simp only [CommRingCat.comp_apply] at hap
  exact hap.trans (appLE_eq_self _ hg V _ f)

/-- **`Δ^♯` splits the first coprojection.**  The composite of the diagonal with the ambient
component of the first projection is the identity. -/
theorem smallSelfProductDiagonalSection_firstCoprojectionSection
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (V : B.obj.thickening.target.scheme.Opens)
    (f : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductDiagonalSection h V (firstCoprojectionSection pr₀ pr₁ V f) = f :=
  smallSelfProductDiagonalSection_appLE h _ (ambientDiagonal_comp_fst h) V _ f

/-- **`Δ^♯` splits the second coprojection.**  The composite of the diagonal with the ambient
component of the second projection is the identity. -/
theorem smallSelfProductDiagonalSection_secondCoprojectionSection
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) (V : B.obj.thickening.target.scheme.Opens)
    (f : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductDiagonalSection h V (secondCoprojectionSection pr₀ pr₁ V f) = f :=
  smallSelfProductDiagonalSection_appLE h _ (ambientDiagonal_comp_snd h) V _ f

end Coprojections

/-! ### The conormal module and the difference of the coprojections -/

section Conormal

/-- **The divided square `K^{[2]}` seen as a submodule of the diagonal ideal `K`.** -/
def smallSelfProductDiagonalRelations (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    Submodule Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)
      (smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) :=
  Submodule.comap
    (Submodule.subtype
      ((smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V) :
          Ideal Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) :
        Submodule _ Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)))
    ((smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V) :
        Ideal Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) :
      Submodule _ Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V))

/-- **The conormal module `K/K^{[2]}` of the diagonal over an open `V` of `T`**: the quotient of
the diagonal ideal on `p₀⁻¹V ⊓ p₁⁻¹V` by its divided square, a module over `Γ(V, 𝒪_T)` through the
first coprojection.  Modulo the square of `K` the two coprojections induce the same action. -/
def smallSelfProductConormal (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    ModuleCat.{u} Γ(B.obj.thickening.target.scheme, V) :=
  (ModuleCat.restrictScalars (firstCoprojectionSection pr₀ pr₁ V).hom).obj
    (ModuleCat.of Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)
      (↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) ⧸
        smallSelfProductDiagonalRelations h V))

/-- **The class of an element of the diagonal ideal in the conormal module `K/K^{[2]}`.** -/
def smallSelfProductClass (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (y : ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))) :
    smallSelfProductConormal h V :=
  (smallSelfProductDiagonalRelations h V).mkQ y

/-- Taking classes is additive. -/
theorem smallSelfProductClass_add (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    (y z : ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))) :
    smallSelfProductClass h V (y + z) =
      smallSelfProductClass h V y + smallSelfProductClass h V z :=
  map_add (smallSelfProductDiagonalRelations h V).mkQ y z

/-- The scalars of the conormal module act through the first coprojection. -/
theorem smallSelfProductClass_smul (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (c : Γ(B.obj.thickening.target.scheme, V))
    (y : ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))) :
    smallSelfProductClass h V (firstCoprojectionSection pr₀ pr₁ V c • y) =
      c • smallSelfProductClass h V y :=
  map_smul (smallSelfProductDiagonalRelations h V).mkQ
    (firstCoprojectionSection pr₀ pr₁ V c) y

/-- **Two classes in the conormal module agree when their representatives differ by an element of
the divided square.** -/
theorem smallSelfProductClass_eq (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens)
    {y z : ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))}
    (hyz : (y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) - z ∈
      smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V)) :
    smallSelfProductClass h V y = smallSelfProductClass h V z := by
  have hq : (Submodule.Quotient.mk y :
      ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) ⧸
        smallSelfProductDiagonalRelations h V) = Submodule.Quotient.mk z := by
    rw [Submodule.Quotient.eq, smallSelfProductDiagonalRelations, Submodule.mem_comap]
    simpa using hyz
  exact hq

/-- **`f ↦ p₁^♯ f - p₀^♯ f`, as an additive map into the diagonal ideal.** -/
def smallSelfProductDifferenceHom (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    Γ(B.obj.thickening.target.scheme, V) →+
      ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) where
  toFun f := ⟨secondCoprojectionSection pr₀ pr₁ V f - firstCoprojectionSection pr₀ pr₁ V f,
    sub_coprojectionSection_mem h V f⟩
  map_zero' := by
    apply Subtype.ext
    change secondCoprojectionSection pr₀ pr₁ V 0 - firstCoprojectionSection pr₀ pr₁ V 0 = 0
    rw [map_zero, map_zero, sub_zero]
  map_add' f g := by
    apply Subtype.ext
    change secondCoprojectionSection pr₀ pr₁ V (f + g) -
        firstCoprojectionSection pr₀ pr₁ V (f + g) =
      (secondCoprojectionSection pr₀ pr₁ V f - firstCoprojectionSection pr₀ pr₁ V f) +
        (secondCoprojectionSection pr₀ pr₁ V g - firstCoprojectionSection pr₀ pr₁ V g)
    rw [map_add, map_add]
    abel

/-- The section underlying `p₁^♯ f - p₀^♯ f` read in the diagonal ideal is that difference. -/
@[simp]
theorem smallSelfProductDifferenceHom_coe (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (f : Γ(B.obj.thickening.target.scheme, V)) :
    (smallSelfProductDifferenceHom h V f :
        Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) =
      secondCoprojectionSection pr₀ pr₁ V f - firstCoprojectionSection pr₀ pr₁ V f := rfl

/-- **The class of `p₁^♯ f - p₀^♯ f` in the conormal module `K/K^{[2]}`.**  Under the
identification of [Stacks, Tag 07J1] this is the image of the universal divided power
differential of `f`. -/
def smallSelfProductDifference (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (f : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductConormal h V :=
  smallSelfProductClass h V (smallSelfProductDifferenceHom h V f)

/-- The difference of the coprojections is the class of `p₁^♯ f - p₀^♯ f`, by definition. -/
theorem smallSelfProductDifference_eq_class (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (f : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductDifference h V f =
      smallSelfProductClass h V (smallSelfProductDifferenceHom h V f) := rfl

/-- The difference of the coprojections is additive in the section. -/
theorem smallSelfProductDifference_add (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (f g : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductDifference h V (f + g) =
      smallSelfProductDifference h V f + smallSelfProductDifference h V g := by
  rw [smallSelfProductDifference, smallSelfProductDifference, smallSelfProductDifference,
    map_add, smallSelfProductClass_add]

/-- **The Leibniz rule for the difference of the coprojections.**  The error term is
`(p₁^♯ f - p₀^♯ f)(p₁^♯ g - p₀^♯ g)`, a product of two elements of the diagonal ideal. -/
theorem smallSelfProductDifference_mul (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (f g : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductDifference h V (f * g) =
      f • smallSelfProductDifference h V g + g • smallSelfProductDifference h V f := by
  have hmem : ((smallSelfProductDifferenceHom h V (f * g) :
        ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))) :
      Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) -
      ((firstCoprojectionSection pr₀ pr₁ V f • smallSelfProductDifferenceHom h V g +
          firstCoprojectionSection pr₀ pr₁ V g • smallSelfProductDifferenceHom h V f :
            ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))) :
        Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) ∈
      smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V) := by
    have hid : ((smallSelfProductDifferenceHom h V (f * g) :
          ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))) :
        Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) -
        ((firstCoprojectionSection pr₀ pr₁ V f • smallSelfProductDifferenceHom h V g +
            firstCoprojectionSection pr₀ pr₁ V g • smallSelfProductDifferenceHom h V f :
              ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))) :
          Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) =
        (secondCoprojectionSection pr₀ pr₁ V f - firstCoprojectionSection pr₀ pr₁ V f) *
          (secondCoprojectionSection pr₀ pr₁ V g -
            firstCoprojectionSection pr₀ pr₁ V g) := by
      change (secondCoprojectionSection pr₀ pr₁ V (f * g) -
            firstCoprojectionSection pr₀ pr₁ V (f * g)) -
          (firstCoprojectionSection pr₀ pr₁ V f *
              (secondCoprojectionSection pr₀ pr₁ V g -
                firstCoprojectionSection pr₀ pr₁ V g) +
            firstCoprojectionSection pr₀ pr₁ V g *
              (secondCoprojectionSection pr₀ pr₁ V f -
                firstCoprojectionSection pr₀ pr₁ V f)) = _
      rw [map_mul, map_mul]
      ring
    rw [hid]
    refine sq_le_smallSelfProductDividedSquare h _ ?_
    rw [pow_two]
    exact Ideal.mul_mem_mul (sub_coprojectionSection_mem h V f)
      (sub_coprojectionSection_mem h V g)
  rw [smallSelfProductDifference, smallSelfProductDifference, smallSelfProductDifference,
    ← smallSelfProductClass_smul, ← smallSelfProductClass_smul, ← smallSelfProductClass_add]
  exact smallSelfProductClass_eq h V hmem

/-- **The difference of the coprojections vanishes on a section pulled back from the base.** -/
theorem smallSelfProductDifference_base (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) {f : Γ(B.obj.thickening.target.scheme, V)}
    (hf : f ∈ baseSections B.obj.thickening.target S.S.scheme B.obj.toBase.hom V) :
    smallSelfProductDifference h V f = 0 := by
  obtain ⟨V', hle, a, rfl⟩ := hf
  have hzero : smallSelfProductDifferenceHom h V (B.obj.toBase.hom.appLE V' V hle a) = 0 := by
    apply Subtype.ext
    change secondCoprojectionSection pr₀ pr₁ V (B.obj.toBase.hom.appLE V' V hle a) -
        firstCoprojectionSection pr₀ pr₁ V (B.obj.toBase.hom.appLE V' V hle a) = 0
    rw [coprojectionSection_base_eq pr₀ pr₁ V hle a, sub_self]
  rw [smallSelfProductDifference, hzero, smallSelfProductClass, map_zero]
  rfl

/-- **The ring-level divided power chain rule for a difference of two homomorphisms of divided
power rings.**  If `p₀, p₁ : (A, I, γ) → (R, J, δ)` agree modulo an ideal `K` of `R`, then
`p₁(γ_{n+1} x) - p₀(γ_{n+1} x)` and `p₀(γ_n x)(p₁ x - p₀ x)` agree modulo the divided powers of
order at least two of `K`: both coprojections turn `γ` into `δ`, and the expansion of
`δ_{n+1}(p₀ x + (p₁ x - p₀ x))` has the first as its linear term. -/
private theorem dpow_chain_rule_mem {A R : Type u} [CommRing A] [CommRing R] {I : Ideal A}
    {J : Ideal R} (γ : DividedPowers I) (δ : DividedPowers J) (K : Ideal R)
    (p₀ p₁ : A →+* R) (hp₀ : γ.IsDPMorphism δ p₀) (hp₁ : γ.IsDPMorphism δ p₁)
    (hK : ∀ a : A, p₁ a - p₀ a ∈ K) (n : ℕ) (x : A) (hx : x ∈ I) :
    p₁ (γ.dpow (n + 1) x) - p₀ (γ.dpow (n + 1) x) - p₀ (γ.dpow n x) * (p₁ x - p₀ x) ∈
      secondDividedPowerIdeal δ K := by
  have hu : p₀ x ∈ J := hp₀.ideal_comp (Ideal.mem_map_of_mem _ hx)
  have hv : p₁ x ∈ J := hp₁.ideal_comp (Ideal.mem_map_of_mem _ hx)
  have hmem := dpow_sub_sub_mem_secondDividedPowerIdeal δ K (p₀ x) (p₁ x) n hu (hK x)
    (Ideal.sub_mem _ hv hu)
  have hid : p₁ (γ.dpow (n + 1) x) - p₀ (γ.dpow (n + 1) x) -
      p₀ (γ.dpow n x) * (p₁ x - p₀ x) =
      δ.dpow (n + 1) (p₁ x) - δ.dpow (n + 1) (p₀ x) - δ.dpow n (p₀ x) * (p₁ x - p₀ x) := by
    rw [← hp₁.dpow_comp (n := n + 1) x hx, ← hp₀.dpow_comp (n := n + 1) x hx,
      ← hp₀.dpow_comp (n := n) x hx]
  rw [hid]
  exact hmem

/-- **The divided power chain rule for the difference of the coprojections.**  Both coprojections
are homomorphisms of divided power rings, so the two sides differ by the terms of order at least
two in the expansion of `δ(1)_{n+1}(p₀^♯ x + (p₁^♯ x - p₀^♯ x))`, which lie in `K^{[2]}`. -/
theorem smallSelfProductDifference_dpow (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (n : ℕ)
    (x : Γ(B.obj.thickening.target.scheme, V))
    (hx : x ∈ B.obj.thickening.target.ideal.obj (op V)) :
    smallSelfProductDifference h V
        ((B.obj.thickening.target.dividedPowers.dividedPowers (op V)).dpow (n + 1) x) =
      smallSelfProductClass h V
        (firstCoprojectionSection pr₀ pr₁ V
            ((B.obj.thickening.target.dividedPowers.dividedPowers (op V)).dpow n x) •
          smallSelfProductDifferenceHom h V x) := by
  have hmem : ((smallSelfProductDifferenceHom h V
          ((B.obj.thickening.target.dividedPowers.dividedPowers (op V)).dpow (n + 1) x) :
        ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))) :
      Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) -
      ((firstCoprojectionSection pr₀ pr₁ V
            ((B.obj.thickening.target.dividedPowers.dividedPowers (op V)).dpow n x) •
          smallSelfProductDifferenceHom h V x :
            ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))) :
        Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)) ∈
      smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V) :=
    secondDividedPowerIdeal_le_smallSelfProductDividedSquare h _
      (dpow_chain_rule_mem (B.obj.thickening.target.dividedPowers.dividedPowers (op V))
        (D.obj.thickening.target.dividedPowers.dividedPowers
          (op (smallSelfProductOpen pr₀ pr₁ V)))
        (smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V))
        (firstCoprojectionSection pr₀ pr₁ V).hom (secondCoprojectionSection pr₀ pr₁ V).hom
        (firstCoprojectionSection_isDPMorphism pr₀ pr₁ V)
        (secondCoprojectionSection_isDPMorphism pr₀ pr₁ V)
        (fun a ↦ sub_coprojectionSection_mem h V a) n x hx)
  exact (smallSelfProductDifference_eq_class h V _).trans (smallSelfProductClass_eq h V hmem)


end Conormal

/-! ### The comparison map -/

section Comparison

/-- **The difference of the two coprojections, as a divided power derivation.**  Additivity, the
Leibniz rule and the vanishing on sections pulled back from the base make `f ↦ [p₁^♯ f - p₀^♯ f]`
a derivation of `Γ(V, 𝒪_T)` over the global sections of the divided power base, with values in the
conormal module of the diagonal. -/
def smallSelfProductConormalDerivation (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    (smallSelfProductConormal h V).Derivation
      (baseAppLE B.obj.thickening.target S.S.scheme B.obj.toBase.hom V) :=
  ModuleCat.Derivation.mk (smallSelfProductDifference h V)
    (smallSelfProductDifference_add h V) (smallSelfProductDifference_mul h V)
    (fun a ↦ smallSelfProductDifference_base h V
      (appLE_mem_baseSections B.obj.thickening.target S.S.scheme B.obj.toBase.hom V ⊤
        (le_preimage_top B.obj.toBase.hom V) a))

/-- The derivation of the conormal module sends `f` to the class of `p₁^♯ f - p₀^♯ f`. -/
@[simp]
theorem smallSelfProductConormalDerivation_d (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (f : Γ(B.obj.thickening.target.scheme, V)) :
    (smallSelfProductConormalDerivation h V).d f = smallSelfProductDifference h V f := rfl

/-- **Stacks Project, Tag 07J1, the comparison map of the second assertion.**  The universal
property of the divided power differentials of `T` over `S` on an open `V` applied to the
difference of the two coprojections: a `Γ(V, 𝒪_T)`-linear map from `Ω_{T/S,δ}(V)`, which is
`(Ω_{X/S})_T(V)` by [Stacks, Tag 07IZ], to the conormal module `K/K^{[2]}` of the diagonal,
carrying `d f` to the class of `p₁^♯ f - p₀^♯ f`.

This is the map the equality `(Ω_{X/S})_T = K/K^{[2]}` of the source is an equality of.  It is an
isomorphism over an affine open of `T` lying over an affine open of `S` — the hypotheses under
which the source's proof works — by
`Crystalline.GlobalCrystallineSituation.isIso_smallSelfProductConormalComparison` in
`StacksFrontier/AlgebraicGeometry/Crystalline/SelfProductConormalIso.lean`. -/
@[stacks 07J1 "second assertion: the comparison map (Ω_{X/S})_T → K/K^{[2]} on each open of T; \
an isomorphism on an affine open of T lying over an affine open of S"]
def smallSelfProductConormalComparison (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    (dpDifferentialsPresheaf B.obj.thickening.target S.S.scheme B.obj.toBase.hom).obj (op V) ⟶
      smallSelfProductConormal h V :=
  dpConstDesc (smallSelfProductConormalDerivation h V)
    (fun n x hx ↦ (smallSelfProductDifference_dpow h V n x hx).trans
      (smallSelfProductClass_smul h V _ _))
    (fun _ hs ↦ smallSelfProductDifference_base h V hs)

/-- **The comparison map carries the universal divided power differential of `f` to the class of
`p₁^♯ f - p₀^♯ f`.** -/
@[simp]
theorem smallSelfProductConormalComparison_d (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) (f : Γ(B.obj.thickening.target.scheme, V)) :
    (smallSelfProductConormalComparison h V).hom
        ((presheafD B.obj.thickening.target S.S.scheme B.obj.toBase.hom V).d f) =
      smallSelfProductDifference h V f :=
  dpConstDesc_d _ _ _ f

/-- **The comparison map read out of `(Ω_{X/S})_T`.**  The restriction of `Ω_{X/S}` to the opens
of `T` is the presheaf of divided power differentials of `T` over `S` by [Stacks, Tag 07IZ], and
this is the comparison map transported along that identification. -/
def restrictedCrysDifferentialsConormalComparison (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    (restrictedCrysDifferentials S B.obj).obj (op V) ⟶ smallSelfProductConormal h V :=
  (comparisonIsoApp B.obj V).inv ≫ smallSelfProductConormalComparison h V

/-- The comparison map out of `(Ω_{X/S})_T` is the comparison map out of the divided power
differentials of `T`, read through [Stacks, Tag 07IZ]. -/
theorem comparisonIsoApp_comp_conormalComparison (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (V : B.obj.thickening.target.scheme.Opens) :
    (comparisonIsoApp B.obj V).hom ≫ restrictedCrysDifferentialsConormalComparison h V =
      smallSelfProductConormalComparison h V := by
  have hcomp : (comparisonIsoApp B.obj V).hom ≫ ((comparisonIsoApp B.obj V).inv ≫
      smallSelfProductConormalComparison h V) = smallSelfProductConormalComparison h V :=
    (comparisonIsoApp B.obj V).hom_inv_id_assoc _
  exact hcomp

end Comparison

/-! ### Compatibility with restriction to a smaller open of `T` -/

section Restriction

/-- Restriction of sections of `𝒪_{T(1)}` from `p₀⁻¹V ⊓ p₁⁻¹V` to `p₀⁻¹V' ⊓ p₁⁻¹V'`. -/
def smallSelfProductRestrict (pr₀ pr₁ : D ⟶ B)
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V) :
    Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V) ⟶
      Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V') :=
  D.obj.thickening.target.scheme.presheaf.map
    (homOfLE (smallSelfProductOpen_mono pr₀ pr₁ hle)).op

/-- Restricting the sections of a morphism `g` to smaller opens, before or after applying `g`. -/
private theorem appLE_comp_restrict_eq {X Y : Scheme.{u}} (g : X ⟶ Y) {V V' : Y.Opens}
    {W W' : X.Opens} (hV : V' ≤ V) (hW : W' ≤ W) (e : W ≤ g ⁻¹ᵁ V) (e' : W' ≤ g ⁻¹ᵁ V') :
    g.appLE V W e ≫ X.presheaf.map (homOfLE hW).op =
      Y.presheaf.map (homOfLE hV).op ≫ g.appLE V' W' e' :=
  (Scheme.Hom.appLE_map _ _ _).trans (Scheme.Hom.map_appLE _ _ _).symm

/-- The first coprojection on sections commutes with restriction. -/
theorem firstCoprojectionSection_restrict (pr₀ pr₁ : D ⟶ B)
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V) :
    firstCoprojectionSection pr₀ pr₁ V ≫ smallSelfProductRestrict pr₀ pr₁ hle =
      B.obj.thickening.target.scheme.presheaf.map (homOfLE hle).op ≫
        firstCoprojectionSection pr₀ pr₁ V' :=
  appLE_comp_restrict_eq _ hle _ _ _

/-- The second coprojection on sections commutes with restriction. -/
theorem secondCoprojectionSection_restrict (pr₀ pr₁ : D ⟶ B)
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V) :
    secondCoprojectionSection pr₀ pr₁ V ≫ smallSelfProductRestrict pr₀ pr₁ hle =
      B.obj.thickening.target.scheme.presheaf.map (homOfLE hle).op ≫
        secondCoprojectionSection pr₀ pr₁ V' :=
  appLE_comp_restrict_eq _ hle _ _ _

/-- **Restriction carries the diagonal ideal into the diagonal ideal.**  The map on sections of
the ambient diagonal commutes with restriction, so a section killed over the larger open is
killed over the smaller one. -/
theorem smallSelfProductRestrict_mem_diagonalIdeal (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V)
    {y : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V)}
    (hy : y ∈ smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) :
    smallSelfProductRestrict pr₀ pr₁ hle y ∈
      smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V') := by
  have hnat := (smallSelfProductAmbientDiagonal h).hom.naturality
    (homOfLE (smallSelfProductOpen_mono pr₀ pr₁ hle)).op
  have hap := congrArg
    (fun φ : Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V) ⟶
        Γ(B.obj.thickening.target.scheme,
          (smallSelfProductAmbientDiagonal h).hom ⁻¹ᵁ smallSelfProductOpen pr₀ pr₁ V') ↦ φ y)
    hnat
  simp only [CommRingCat.comp_apply] at hap
  have h0 : (smallSelfProductAmbientDiagonal h).hom.app (smallSelfProductOpen pr₀ pr₁ V) y = 0 :=
    RingHom.mem_ker.mp hy
  have hz : (smallSelfProductAmbientDiagonal h).hom.app (smallSelfProductOpen pr₀ pr₁ V')
      (smallSelfProductRestrict pr₀ pr₁ hle y) = 0 := by
    rw [smallSelfProductRestrict, hap, h0, map_zero]
  exact RingHom.mem_ker.mpr hz

/-- **Restriction of a representative, as an additive map of diagonal ideals.** -/
def smallSelfProductRestrictIdeal (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V) :
    ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) →+
      ↥(smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V')) where
  toFun y := ⟨smallSelfProductRestrict pr₀ pr₁ hle y,
    smallSelfProductRestrict_mem_diagonalIdeal h hle y.2⟩
  map_zero' := Subtype.ext (map_zero _)
  map_add' _ _ := Subtype.ext (map_add _ _ _)

/-- **The difference of the two coprojections commutes with restriction.**  This is the content
of the naturality of the comparison map: a representative of the class of `d f` restricts to a
representative of the class of `d (f|_{V'})`. -/
theorem smallSelfProductDifferenceHom_restrict (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V)
    (f : Γ(B.obj.thickening.target.scheme, V)) :
    smallSelfProductRestrictIdeal h hle (smallSelfProductDifferenceHom h V f) =
      smallSelfProductDifferenceHom h V'
        (B.obj.thickening.target.scheme.presheaf.map (homOfLE hle).op f) := by
  have h1 := congrArg
    (fun φ : Γ(B.obj.thickening.target.scheme, V) ⟶
        Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V') ↦ φ f)
    (firstCoprojectionSection_restrict pr₀ pr₁ hle)
  have h2 := congrArg
    (fun φ : Γ(B.obj.thickening.target.scheme, V) ⟶
        Γ(D.obj.thickening.target.scheme, smallSelfProductOpen pr₀ pr₁ V') ↦ φ f)
    (secondCoprojectionSection_restrict pr₀ pr₁ hle)
  simp only [CommRingCat.comp_apply] at h1 h2
  apply Subtype.ext
  change smallSelfProductRestrict pr₀ pr₁ hle
      (secondCoprojectionSection pr₀ pr₁ V f - firstCoprojectionSection pr₀ pr₁ V f) =
    secondCoprojectionSection pr₀ pr₁ V'
        (B.obj.thickening.target.scheme.presheaf.map (homOfLE hle).op f) -
      firstCoprojectionSection pr₀ pr₁ V'
        (B.obj.thickening.target.scheme.presheaf.map (homOfLE hle).op f)
  rw [map_sub, h1, h2]

/-- Restriction carries the diagonal ideal into the diagonal ideal, as ideals. -/
theorem map_smallSelfProductDiagonalIdeal_le (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V) :
    Ideal.map (smallSelfProductRestrict pr₀ pr₁ hle).hom
        (smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V)) ≤
      smallSelfProductDiagonalIdeal h (smallSelfProductOpen pr₀ pr₁ V') :=
  Ideal.map_le_iff_le_comap.mpr fun _ hy ↦
    smallSelfProductRestrict_mem_diagonalIdeal h hle hy

/-- **Restriction carries the divided square into the divided square.**  Restriction is a
homomorphism of divided power rings, so it takes a divided power of order at least two of a
section of the diagonal ideal to one of the restricted section. -/
theorem map_smallSelfProductDividedSquare_le (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    {V V' : B.obj.thickening.target.scheme.Opens} (hle : V' ≤ V) :
    Ideal.map (smallSelfProductRestrict pr₀ pr₁ hle).hom
        (smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V)) ≤
      smallSelfProductDividedSquare h (smallSelfProductOpen pr₀ pr₁ V') := by
  have hK := map_smallSelfProductDiagonalIdeal_le h hle
  refine le_trans ?_ (sup_le (sq_le_smallSelfProductDividedSquare h _)
    (secondDividedPowerIdeal_le_smallSelfProductDividedSquare h _))
  rw [smallSelfProductDividedSquare, Ideal.add_eq_sup, Ideal.map_sup]
  refine sup_le (le_sup_of_le_left ?_) (le_sup_of_le_right ?_)
  · rw [pow_two, Ideal.map_mul, pow_two]
    exact Ideal.mul_mono hK hK
  · refine Ideal.map_le_iff_le_comap.mpr (Ideal.span_le.mpr ?_)
    rintro v ⟨n, hn, y, hy, rfl⟩
    have hyJ : y ∈ D.obj.thickening.target.ideal.obj (op (smallSelfProductOpen pr₀ pr₁ V)) :=
      smallSelfProductDiagonalIdeal_le h _ hy
    have hdp := (D.obj.thickening.target.dividedPowers.naturality
      (homOfLE (smallSelfProductOpen_mono pr₀ pr₁ hle)).op).dpow_comp (n := n) y hyJ
    simp only [SetLike.mem_coe, Ideal.mem_comap]
    exact Ideal.subset_span ⟨n, hn, smallSelfProductRestrict pr₀ pr₁ hle y,
      smallSelfProductRestrict_mem_diagonalIdeal h hle hy, hdp.symm⟩

end Restriction

/-! ### The diagonal is a closed immersion -/

section ClosedImmersion

/-- **The immersion of a divided power thickening of schemes is a homeomorphism on spaces.**  It
is a closed immersion, hence a closed embedding, and it is surjective. -/
theorem isHomeomorph_thickeningImmersion (E : SchemeThickening.{u}) :
    IsHomeomorph (Scheme.forgetToTop.map E.immersion) := by
  have hce := IsClosedImmersion.isClosedEmbedding E.immersion
  exact isHomeomorph_iff_continuous_isClosedMap_bijective.mpr
    ⟨E.immersion.continuous, hce.isClosedMap, hce.injective, E.isThickening.2⟩

/-- **The ambient diagonal is a homeomorphism on spaces.**  The immersions of the two thickenings
are homeomorphisms, and `U(1) = U`: the component of the diagonal on thickened schemes is an
isomorphism, so the diagonal is that isomorphism read through the two immersions. -/
theorem isHomeomorph_smallSelfProductAmbientDiagonal (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    IsHomeomorph (Scheme.forgetToTop.map (smallSelfProductAmbientDiagonal h).hom) := by
  let e₀ : B.obj.thickening.source ≃ₜ B.obj.thickening.target.scheme :=
    (isHomeomorph_thickeningImmersion B.obj.thickening).homeomorph
      (Scheme.forgetToTop.map B.obj.thickening.immersion)
  let e₁ : D.obj.thickening.source ≃ₜ D.obj.thickening.target.scheme :=
    (isHomeomorph_thickeningImmersion D.obj.thickening).homeomorph
      (Scheme.forgetToTop.map D.obj.thickening.immersion)
  have : IsIso (smallSelfProductDiagonal h).hom.sourceHom :=
    isIso_smallSelfProductDiagonal_sourceHom h
  let ed : B.obj.thickening.source ≃ₜ D.obj.thickening.source :=
    TopCat.homeoOfIso (asIso (Scheme.forgetToTop.map (smallSelfProductDiagonal h).hom.sourceHom))
  have hsquare := congrArg Scheme.forgetToTop.map
    (smallSelfProductDiagonal h).hom.immersion_naturality
  rw [Functor.map_comp, Functor.map_comp] at hsquare
  have hpoint (x : B.obj.thickening.source) :
      (Scheme.forgetToTop.map (smallSelfProductAmbientDiagonal h).hom) (e₀ x) = e₁ (ed x) := by
    change (Scheme.forgetToTop.map (smallSelfProductAmbientDiagonal h).hom)
        ((Scheme.forgetToTop.map B.obj.thickening.immersion) x) =
      (Scheme.forgetToTop.map D.obj.thickening.immersion)
        ((Scheme.forgetToTop.map (smallSelfProductDiagonal h).hom.sourceHom) x)
    exact congrArg (fun φ ↦ φ x) hsquare
  have hfun : (Scheme.forgetToTop.map (smallSelfProductAmbientDiagonal h).hom) =
      (ed.trans e₁).toFun ∘ e₀.symm.toFun := by
    funext x
    have hx := hpoint (e₀.symm x)
    rwa [e₀.apply_symm_apply] at hx
  rw [hfun]
  exact (e₀.symm.trans (ed.trans e₁)).isHomeomorph

/-- **Stacks Project, Tag 07J1.**  The ambient diagonal `Δ : T ⟶ T(1)` of a self-product taken in
`Cris(X/S)` is a closed immersion.  It is surjective on stalks because it is a section of either
coprojection, and a closed embedding because it is a homeomorphism on spaces: that is `U(1) = U`
read through the immersions of the two thickenings. -/
@[stacks 07J1 "the diagonal Δ : T ⟶ T(1) is a closed immersion"]
theorem isClosedImmersion_smallSelfProductAmbientDiagonal
    (h : IsLimit (BinaryFan.mk pr₀ pr₁)) :
    IsClosedImmersion (smallSelfProductAmbientDiagonal h).hom := by
  have hcomp : SurjectiveOnStalks
      ((smallSelfProductAmbientDiagonal h).hom ≫ pr₀.hom.targetHom.hom) := by
    rw [ambientDiagonal_comp_fst h]
    infer_instance
  exact
    { toSurjectiveOnStalks := .of_comp _ pr₀.hom.targetHom.hom
      isClosedEmbedding := ((isHomeomorph_smallSelfProductAmbientDiagonal h).homeomorph
        (Scheme.forgetToTop.map (smallSelfProductAmbientDiagonal h).hom)).isClosedEmbedding }

/-- **Stacks Project, Tag 07J1.**  On an affine open of `T(1)` the quasi-coherent sheaf of ideals
of the closed immersion `Δ` is the diagonal ideal.  This is what reconciles the presentation of
`K` used here and in `SelfProductDiagonal.lean` — the kernel of `Δ` on sections over each open —
with the source's, the quasi-coherent sheaf of ideals of the closed immersion `Δ`. -/
@[stacks 07J1 "K is the quasi-coherent ideal sheaf of the closed immersion Δ, on affine opens"]
theorem ker_ideal_smallSelfProductAmbientDiagonal (h : IsLimit (BinaryFan.mk pr₀ pr₁))
    (W : D.obj.thickening.target.scheme.affineOpens) :
    (smallSelfProductAmbientDiagonal h).hom.ker.ideal W =
      smallSelfProductDiagonalIdeal h (W : D.obj.thickening.target.scheme.Opens) := by
  have := isClosedImmersion_smallSelfProductAmbientDiagonal h
  exact Scheme.Hom.ker_apply _ W

end ClosedImmersion

end Crystalline.GlobalCrystallineSituation

end
