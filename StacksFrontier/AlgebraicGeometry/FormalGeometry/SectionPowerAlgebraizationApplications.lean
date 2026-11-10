module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.SectionPowerAlgebraization
public import StacksFrontier.AlgebraicGeometry.Variety.CohenMacaulayDepthDimensionBound
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.CohomologyVanishesLocally
public import StacksFrontier.Topology.Sheaves.Modules.LocallyFree

/-!
# Lefschetz applications of the algebraization along a zero scheme

Let `X` be a scheme proper over a field `k`, let `L` be an ample invertible `𝒪_X`-module, let `s`
be a global section of `L`, let `Y = Z(s)` be its zero scheme and let `Yₙ = Z(sⁿ)` be the `n`-th
infinitesimal neighbourhood of `Y`. For a quasi-coherent `𝓕` on `X` with restrictions `𝓕ₙ` to
`Yₙ`, [Stacks, Tag 0EL1] — proved as
`Stacks.Algebraization.isIso_zeroSchemeComparison_of_depthAddDim_gt` — says that

`Hⁱ(X, 𝓕) ⟶ lim Hⁱ(Yₙ, 𝓕ₙ)`

is an isomorphism for `i < σ` as soon as `depth(𝓕_x) + dim({x}‾) > σ` at every `x ∈ X ∖ Y`.

This file is the rest of the source's section: [Stacks, Tag 0EL2], which replaces `X` by an
arbitrary open neighbourhood `V` of `Y` in degree `0`, and [Stacks, Tag 0EL3], which records what
the bound gives on a Cohen–Macaulay variety of a given dimension.

## How the two tags sit over `σ`

[Stacks, Tag 0EL2] is exactly `σ = 1`: the source's hypothesis `depth(𝓕_x) + dim({x}‾) > 1`
off `Y` is the hypothesis of [Stacks, Tag 0EL1] at `σ = 1`, whose conclusion is then the
degree-`0` case `i = 0 < 1 = σ`. Nothing else in the inequality is used, and no larger `σ` is
available: the content of the lemma beyond the proposition is the passage from `X` to `V`.

[Stacks, Tag 0EL3] is the same inequality read on a Cohen–Macaulay variety. If `X` is a
Cohen–Macaulay variety of dimension `d` over `k` and `𝓔` is finite locally free, then at every
point `x` of `X` the stalk `𝓔_x` is free over the Cohen–Macaulay local ring `𝒪_{X,x}`, so
`depth(𝓔_x) = dim(𝒪_{X,x})`, while `dim({x}‾) = d - dim(𝒪_{X,x})` by the dimension formula on a
variety; hence

`depth(𝓔_x) + dim({x}‾) = d`

and [Stacks, Tag 0EL1] applies with any `σ < d`, the largest being `σ = d - 1`. The source's
three cases are the three smallest values of `d`:

* `d = 1`, a curve: `σ = 0`, so the range `0 ≤ i < σ` is empty — this is the source's "we don't
  learn anything", a remark about the *absence* of a conclusion and not a statement. No
  declaration is attached to it.
* `d = 2`, a Cohen–Macaulay (for example normal) surface: `σ = 1`, so `H⁰` only.
* `d = 3`, a Cohen–Macaulay threefold: `σ = 2`, so `H⁰` and `H¹`.

The source's closing remark, that on a *normal* threefold one still gets `H⁰` but not `H¹`, is the
same computation with the bound `≥ 2` in place of `= 3`: a normal local ring has depth at least
`min(2, dim)`, so `depth(𝓔_x) + dim({x}‾) ≥ 2` with equality at the closed points, and `σ = 1` is
the best available. That is the general theorem below at the bound `2`; the half of the remark
which says `H¹` is *not* obtained is again an absence of a conclusion, not a statement.

## What is carried, and why

Each of the two results is stated on top of
`Stacks.Algebraization.isIso_zeroSchemeComparison_of_depthAddDim_gt`, so it inherits that tag's
three carried inputs. They are bundled once here as
`Stacks.Algebraization.ZeroSchemeAlgebraizationInput`, whose fields are verbatim the hypotheses
`hI`, `hfam`, `hf`, `hproj`, `hsplit` and `halg` of that statement; see the module
documentation of
`StacksFrontier/AlgebraicGeometry/FormalGeometry/SectionPowerAlgebraization.lean` for why the fibre
dichotomy of the punctured cone, the section ring data and the algebraization square cannot be
produced in this library.

Beyond those, [Stacks, Tag 0EL2] carries one further named fact and [Stacks, Tag 0EL3] carries
nothing.

* **[Stacks, Tag 0EL2]** carries
  `Stacks.Algebraization.OpenNeighbourhoodSections.isIso_Hrestrict`: that restriction of sections
  `Γ(X, 𝓕) ⟶ Γ(V, 𝓕)` along an open `V ⊇ Y` is bijective. This is the whole content of the
  lemma over the proposition. The source gets it from the depth hypothesis: the complement
  `T = X ∖ V` is closed in `X` and misses `Y`, so it is proper over `k` and closed in the affine
  scheme `X ∖ Y` of [Stacks, Tag 0EKE]
  (`Stacks.AmpleNonvanishingUniversallyClosed.isAffineHom_nonvanishingOpen`), hence
  finite over `k`; so `T` is a finite set of closed points, where `dim({x}‾) = 0` and the
  hypothesis forces `depth(𝓕_x) ≥ 2`; and depth at least two along a closed set is exactly the
  bijectivity of restriction across it, which is [Stacks, Tag 0E9I] and *is* proved, as
  `AlgebraicGeometry.restriction_bijective_of_depth_ge_two`. Two links of that chain are not
  available here, and the field is their single joint consequence.
  - "Proper and affine over a field implies finite" — `IsFinite.iff_isProper_and_isAffineHom` is
    in Mathlib, but the step from there to `dim({x}‾) = 0` for `x ∈ T`, that is [Stacks, Tag
    01WN] and [Stacks, Tag 0A28] for the closed subscheme `T`, is not in this library; the
    nearest statement, `topologicalKrullDim_eq_zero_of_isAffine`, assumes `X` itself affine.
  - The degree-zero comparison of the two spellings of sections, *naturally in the open*. The
    statement of [Stacks, Tag 0E9I] is about `F.presheaf.map`, the presheaf restriction, whereas
    `Hrestrict` is `CategoryTheory.NatTrans.rightDerived` of the restriction of the sections
    functor. Identifying the two needs the naturality square for
    `CategoryTheory.Functor.toRightDerivedZero` against `NatTrans.rightDerived _ 0`, which
    neither Mathlib nor this library has in any degree-zero form.
* **[Stacks, Tag 0EL3]** carries nothing beyond that. The displayed identity
  `depth(𝓔_x) + dim({x}‾) = d` is proved, in the form of the lower bound that
  [Stacks, Tag 0EL1] consumes, as
  `Stacks.Algebraization.intCast_le_sheafDepthAt_add_dimClosureAt_of_isCohenMacaulay` in
  `StacksFrontier/AlgebraicGeometry/Variety/CohenMacaulayDepthDimensionBound.lean`: the stalk `𝓔_x`
  is finite free over `𝒪_{X,x}` because `𝓔` is finite locally free, so its depth is at least
  that of `𝒪_{X,x}`; a Cohen–Macaulay scheme satisfies every Serre condition
  ([Stacks, Tag 0342]), which bounds `depth(𝒪_{X,x})` below by `min(d, dim(𝒪_{X,x}))`; and the
  dimension formula `dim(𝒪_{X,x}) + dim({x}‾) = dim(X)` on an irreducible scheme locally of
  finite type over a field ([Stacks, Tag 0A21]) absorbs the truncation. Only the inequality
  `dim ≤ depth` of the Cohen–Macaulay condition is used, never the equality.

## Main definitions

* `Stacks.Algebraization.ZeroSchemeAlgebraizationInput` — the carried input of
  [Stacks, Tag 0EL1], bundled.
* `Stacks.Algebraization.OpenNeighbourhoodSections` — the carried input of [Stacks, Tag 0EL2]:
  that `V` contains `Y`, and that restriction of sections from `X` to `V` is bijective.

## Main results

* `Stacks.Algebraization.ZeroSchemeAlgebraizationInput.isIso_zeroSchemeComparison` —
  [Stacks, Tag 0EL1] read off the bundled input.
* `Stacks.Algebraization.isIso_openNeighbourhoodComparison_of_depthAddDim_gt` —
  **[Stacks, Tag 0EL2]**.
* `Stacks.Algebraization.isIso_zeroSchemeComparison_of_cohenMacaulayDepthDimBound` — the general
  pattern of [Stacks, Tag 0EL3]: a Cohen–Macaulay proper variety of dimension at least `d` gives
  every degree `i < d - 1`.
* `Stacks.Algebraization.isIso_zeroSchemeComparison_zero_of_cohenMacaulaySurface` and
  `Stacks.Algebraization.isIso_zeroSchemeComparison_of_cohenMacaulayThreefold` —
  **[Stacks, Tag 0EL3]**, clauses (2) and (3).

## Implementation notes

`Γ(V, 𝓕)` is `Hgroup X.ringCatSheaf V 0 F`, the degree-zero cohomology over the open `V`, which
is the same functor in which [Stacks, Tag 0EL1] states `Γ(X, 𝓕) = H⁰(X, 𝓕)`; the restriction map
`Γ(X, 𝓕) ⟶ Γ(V, 𝓕)` is `Hrestrict` at `le_top`.

The comparison map on `V` is not constructed. Building it directly would mean factoring each
`Γ(V, 𝓕) ⟶ Γ(Yₙ, 𝓕ₙ)` through the open immersion `V ⟶ X`, which is available only through the
lift of `Yₙ ⟶ X` along it. Instead the theorem takes *any* map `c` out of `Γ(V, 𝓕)` whose
composite with restriction is the comparison map of [Stacks, Tag 0EL1], which is the equation the
canonical map satisfies, and concludes that `c` is an isomorphism. Since restriction is
bijective, that equation determines `c` uniquely, so nothing is lost: the hypothesis names the
canonical map and no other.

## References

* [Stacks Project, Tag 0EL2](https://stacks.math.columbia.edu/tag/0EL2)
* [Stacks Project, Tag 0EL3](https://stacks.math.columbia.edu/tag/0EL3)
* [Stacks Project, Tag 0EL1](https://stacks.math.columbia.edu/tag/0EL1)
* [Stacks Project, Tag 0EKE](https://stacks.math.columbia.edu/tag/0EKE)
* [Stacks Project, Tag 0E9I](https://stacks.math.columbia.edu/tag/0E9I)
* [Stacks Project, Tag 01WN](https://stacks.math.columbia.edu/tag/01WN)
* [Stacks Project, Tag 0A28](https://stacks.math.columbia.edu/tag/0A28)
* [Stacks Project, Tag 0342](https://stacks.math.columbia.edu/tag/0342)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

attribute [local instance] HasDerivedCategory.standard

universe u

namespace Stacks.Algebraization

/-! ### The carried input of [Stacks, Tag 0EL1], bundled -/

/-- The three inputs which `Stacks.Algebraization.isIso_zeroSchemeComparison_of_depthAddDim_gt`
carries, together with the section ring data they are stated over, bundled so that the
applications of [Stacks, Tag 0EL1] in this file do not repeat them.

The fields are verbatim the hypotheses of that theorem; `A` is the section ring
`⨁_{m ≥ 0} Γ(X, L^m)` of [Stacks, Tag 0B5T] as an abstract Noetherian `k`-algebra of finite type,
`M` the finite `A`-module of [Stacks, Tag 0BK0], `I` the irrelevant ideal, `fam` a finite
generating family of it, `f` the image of `s` in degree one and `proj` the projection of the
punctured cone `Spec A ∖ V(I)` to `X`. -/
structure ZeroSchemeAlgebraizationInput (k : Type u) [Field k] (X : Scheme.{u}) (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (s : Γ(L, ⊤)) (F : X.Modules) [F.IsQuasicoherent]
    (σ : ℕ) (A : Type u) [CommRing A] [IsNoetherianRing A] [Algebra k A]
    [Algebra.FiniteType k A] (M : Type u) [AddCommGroup M] [Module A M] [Module.Finite A M]
    (I : Ideal A) {r : ℕ} (fam : Fin r → A) (f : A) [IsAdicComplete (Ideal.span {f}) A]
    (proj : PrimeSpectrum A → X) : Prop where
  /-- The irrelevant ideal is finitely generated. -/
  hI : I.FG
  /-- The family `fam` generates the irrelevant ideal. -/
  hfam : Ideal.span (Set.range fam) = I
  /-- The image `f` of the section `s` lies in the irrelevant ideal. -/
  hf : f ∈ I
  /-- The primes of the punctured cone lie over the complement of the zero scheme of `s`. -/
  hproj : ∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
    proj p ∉ ((zeroScheme X L s).support : Set X)
  /-- The fibre dichotomy of the punctured cone: a point of `Spec A ∖ V(I)` is either the generic
  point of its fibre, where the depth is that of the base point and the relative dimension is one
  more, or a closed point of it, where the depth is one more and the relative dimension is that
  of the base point. -/
  hsplit : ∀ p : PrimeSpectrum A, p ∉ PrimeSpectrum.zeroLocus (I : Set A) →
    ∀ q : PrimeSpectrum A, q ∈ PrimeSpectrum.zeroLocus (I : Set A) →
    p.asIdeal ≤ q.asIdeal →
    (localizedDepth A M p = sheafDepthAt F (proj p) ∧
        relativeDimAt A p q = dimClosureAt X (proj p) + 1) ∨
      (localizedDepth A M p = sheafDepthAt F (proj p) + 1 ∧
        relativeDimAt A p q = dimClosureAt X (proj p))
  /-- The algebraization square: in every degree below `σ` the geometric comparison map is the
  comparison map of [Stacks, Tag 0EKM] under the graded decomposition of [Stacks, Tag 0EKH]. -/
  halg : ∀ i : ℕ, i < σ →
    ∃ (e₁ : Hgroup X.ringCatSheaf ⊤ i F ≃+
        (complementCohomologyFunctor fam (i : ℤ)).obj (ModuleCat.of A M))
      (e₂ : ↥(limit (IdealTower.cohomologyTower (zeroSchemeTowerIdeal X L s)
          (zeroSchemeTowerIdeal_succ_le X L s) F i)) ≃+
        ↥(Stacks.ProZero.towerSections
          (HigherComplementTower.quotientCohomologyTower fam f (ModuleCat.of A M) (i : ℤ))
          (HigherComplementTower.quotientCohomologyTransition fam f (ModuleCat.of A M)
            (i : ℤ)))),
      ∀ x : Hgroup X.ringCatSheaf ⊤ i F,
        e₂ (zeroSchemeComparison X L s F i x) =
          HigherComplementTower.toTowerSections fam f (ModuleCat.of A M) (i : ℤ) (e₁ x)

/-- **[Stacks, Tag 0EL1] read off the bundled input.** Under the depth–dimension bound `> σ` off
the zero scheme of `s`, the comparison map `Hⁱ(X, 𝓕) ⟶ lim Hⁱ(Yₙ, 𝓕ₙ)` is an isomorphism in every
degree `i < σ`. -/
theorem ZeroSchemeAlgebraizationInput.isIso_zeroSchemeComparison
    {k : Type u} [Field k] {X : Scheme.{u}} {L : X.Modules}
    [Stacks.Ample.IsInvertibleModule X L] {s : Γ(L, ⊤)} {F : X.Modules} [F.IsQuasicoherent]
    {σ : ℕ} {A : Type u} [CommRing A] [IsNoetherianRing A] [Algebra k A]
    [Algebra.FiniteType k A] {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {I : Ideal A} {r : ℕ} {fam : Fin r → A} {f : A} [IsAdicComplete (Ideal.span {f}) A]
    {proj : PrimeSpectrum A → X}
    (hin : ZeroSchemeAlgebraizationInput k X L s F σ A M I fam f proj)
    (hdepth : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) →
      enatToEInt (sheafDepthAt F x) + krullDimToEInt (dimClosureAt X x) > ((σ : ℤ) : EInt))
    (i : ℕ) (hi : i < σ) :
    IsIso (zeroSchemeComparison X L s F i) :=
  isIso_zeroSchemeComparison_of_depthAddDim_gt k X L s F σ hdepth A M I hin.hI fam hin.hfam f
    hin.hf proj hin.hproj hin.hsplit hin.halg i hi

/-! ### Stacks 0EL2 -/

/-- **The carried input of [Stacks, Tag 0EL2].** For `X` proper over a field `k`, `L` an ample
invertible `𝒪_X`-module, `s` a global section of `L` with zero scheme `Y = Z(s)` and `𝓕` a
coherent `𝒪_X`-module satisfying `depth(𝓕_x) + dim({x}‾) > 1` off `Y`, this holds for every open
`V ⊇ Y`.

The second field is the geometric content of the lemma over [Stacks, Tag 0EL1] and is not proved
here. The source's argument for it: the complement `T = X ∖ V` is closed in `X` and misses `Y`,
so it is proper over `k` and closed in the affine scheme `X ∖ Y` of [Stacks, Tag 0EKE], hence
finite over `k`; thus `T` is a finite set of closed points, where `dim({x}‾) = 0` and the
hypothesis gives `depth(𝓕_x) ≥ 2`; and depth at least two along a closed set is exactly the
bijectivity of restriction across it, which is [Stacks, Tag 0E9I] and is proved as
`AlgebraicGeometry.restriction_bijective_of_depth_ge_two` (for `𝓕` coherent on a locally
Noetherian scheme, which is the source's situation). What is missing is the vanishing
`dim({x}‾) = 0` on `T`, that is [Stacks, Tag 01WN] and [Stacks, Tag 0A28] for the closed
subscheme `T`, and the identification of `Hrestrict` — the derived-functor restriction in degree
zero — with the presheaf restriction that [Stacks, Tag 0E9I] is stated for; see the module
documentation for both. -/
structure OpenNeighbourhoodSections (k : Type u) [Field k] {X : Scheme.{u}}
    (fX : X ⟶ Spec (CommRingCat.of k)) [IsProper fX] (L : X.Modules)
    [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L) (s : Γ(L, ⊤))
    (F : X.Modules) (V : X.Opens) : Prop where
  /-- `V` contains the zero scheme `Y = Z(s)`, which is the source's hypothesis on `V`. -/
  support_subset : ((zeroScheme X L s).support : Set X) ⊆ (V : Set X)
  /-- Restriction of sections `Γ(X, 𝓕) ⟶ Γ(V, 𝓕)` along `V ⊆ X` is bijective. -/
  isIso_Hrestrict : IsIso (Hrestrict X.ringCatSheaf (le_top : V ≤ ⊤) 0 F)

/-- **Stacks Project, Tag 0EL2 (Lemma 52.28.2).** Let `k` be a field, `X` a scheme proper over
`k`, `L` an ample invertible `𝒪_X`-module, `s` a global section of `L`, `Y = Z(s)` its zero
scheme with `n`-th infinitesimal neighbourhood `Yₙ = Z(sⁿ)`, and `𝓕` a coherent `𝒪_X`-module
with

`depth(𝓕_x) + dim({x}‾) > 1`

at every `x ∈ X ∖ Y`. Then `Γ(V, 𝓕) ⟶ lim Γ(Yₙ, 𝓕ₙ)` is an isomorphism for every open subscheme
`V ⊆ X` containing `Y`.

The displayed hypothesis is the hypothesis of [Stacks, Tag 0EL1] at `σ = 1`, and the conclusion
for `V = X` is that tag in degree `i = 0 < 1`. The map on `V` is `c`, characterized — uniquely,
restriction being bijective — by its composite with restriction from `X` being the comparison
map of [Stacks, Tag 0EL1].

Two things are carried: the input `hin` of [Stacks, Tag 0EL1], and the bijectivity of
`Γ(X, 𝓕) ⟶ Γ(V, 𝓕)`, which is the field
`Stacks.Algebraization.OpenNeighbourhoodSections.isIso_Hrestrict` and is the whole content of
this lemma beyond the proposition; see that structure for the source's argument and for the two
library gaps it runs through. -/
@[stacks 0EL2 "Gamma(V,F) -> lim Gamma(Y_n,F_n) is an isomorphism for every open V containing \
Y = Z(s), from depth(F_x) + dim(closure{x}) > 1 off Y; carried: the input of 0EL1 (hin) and the \
bijectivity of Gamma(X,F) -> Gamma(V,F) (hV.isIso_Hrestrict)"]
theorem isIso_openNeighbourhoodComparison_of_depthAddDim_gt
    {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k)) [IsProper fX]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] (hL : Stacks.Ample.IsAmple X L)
    {s : Γ(L, ⊤)} {F : X.Modules} [F.IsQuasicoherent]
    (hdepth : ∀ x : X, x ∉ ((zeroScheme X L s).support : Set X) →
      enatToEInt (sheafDepthAt F x) + krullDimToEInt (dimClosureAt X x) > ((1 : ℤ) : EInt))
    {A : Type u} [CommRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FiniteType k A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {I : Ideal A} {r : ℕ} {fam : Fin r → A} {f : A} [IsAdicComplete (Ideal.span {f}) A]
    {proj : PrimeSpectrum A → X}
    (hin : ZeroSchemeAlgebraizationInput k X L s F 1 A M I fam f proj)
    {V : X.Opens} (hV : OpenNeighbourhoodSections k fX L hL s F V)
    (c : Hgroup X.ringCatSheaf V 0 F ⟶
      limit (IdealTower.cohomologyTower (zeroSchemeTowerIdeal X L s)
        (zeroSchemeTowerIdeal_succ_le X L s) F 0))
    (hc : Hrestrict X.ringCatSheaf (le_top : V ≤ ⊤) 0 F ≫ c = zeroSchemeComparison X L s F 0) :
    IsIso c := by
  have := hV.isIso_Hrestrict
  have := hin.isIso_zeroSchemeComparison (fun x hx => by simpa using hdepth x hx) 0 Nat.one_pos
  have hcc : c = inv (Hrestrict X.ringCatSheaf (le_top : V ≤ ⊤) 0 F) ≫
      zeroSchemeComparison X L s F 0 := by
    rw [← hc, IsIso.inv_hom_id_assoc]
  rw [hcc]
  infer_instance

/-! ### Stacks 0EL3 -/

/-- **The general pattern of [Stacks, Tag 0EL3].** If `X` is a Cohen–Macaulay proper variety
over `k` of dimension at least `d` and `𝓔` is finite locally free, then
`Hⁱ(X, 𝓔) ⟶ lim Hⁱ(Yₙ, 𝓔ₙ)` is an isomorphism in every degree `i < d - 1`, that is whenever
`i + 1 < d`.

The depth–dimension bound `depth(𝓔_x) + dim({x}‾) ≥ d` that [Stacks, Tag 0EL1] consumes is
`Stacks.Algebraization.intCast_le_sheafDepthAt_add_dimClosureAt_of_isCohenMacaulay`: the stalk
`𝓔_x` is finite free over `𝒪_{X,x}`, so its depth is at least that of `𝒪_{X,x}`, which the
Cohen–Macaulay condition bounds below by `min(d, dim(𝒪_{X,x}))` ([Stacks, Tag 0342]), and the
dimension formula `dim(𝒪_{X,x}) + dim({x}‾) = dim(X)` on a variety ([Stacks, Tag 0A21]) turns
that truncation into `dim(X) ≥ d`.

This is then [Stacks, Tag 0EL1] at `σ = d - 1`: the bound `≥ d` is strictly greater than
`d - 1`. The source spells out `d = 1, 2, 3`; the first gives an empty range of degrees. -/
theorem isIso_zeroSchemeComparison_of_cohenMacaulayDepthDimBound
    {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [IsProperVariety k fX]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {s : Γ(L, ⊤)} {E : X.Modules}
    [E.IsQuasicoherent] [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    {σ : ℕ} (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hdim : ((σ + 1 : ℕ) : WithBot ℕ∞) ≤ topologicalKrullDim X)
    {A : Type u} [CommRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FiniteType k A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {I : Ideal A} {r : ℕ} {fam : Fin r → A} {f : A} [IsAdicComplete (Ideal.span {f}) A]
    {proj : PrimeSpectrum A → X}
    (hin : ZeroSchemeAlgebraizationInput k X L s E σ A M I fam f proj)
    (i : ℕ) (hi : i < σ) :
    IsIso (zeroSchemeComparison X L s E i) := by
  refine hin.isIso_zeroSchemeComparison (fun x _ => ?_) i hi
  refine lt_of_lt_of_le ?_
    (intCast_le_sheafDepthAt_add_dimClosureAt_of_isCohenMacaulay k fX E hCM (σ + 1) hdim x)
  exact WithBotTop.coe_lt_coe.mpr (by push_cast; omega)

/-- **Stacks Project, Tag 0EL3 (Example 52.28.3), clause (2).** Let `k` be a field, `X` a proper
variety over `k`, `L` an ample invertible `𝒪_X`-module — the source's `𝒪_X(Y)` — `s` a global
section with zero scheme `Y` and `n`-th infinitesimal neighbourhood `Yₙ`, and `𝓔` a finite
locally free `𝒪_X`-module. If `X` is a Cohen–Macaulay surface, for example a normal one, then

`H⁰(X, 𝓔) ⟶ lim H⁰(Yₙ, 𝓔ₙ)`

is an isomorphism.

This is the general pattern at `d = 2`, hence `σ = 1` and the single degree `i = 0`: the
Cohen–Macaulay condition and the dimension `2` supply the depth–dimension bound through
`Stacks.Algebraization.intCast_le_sheafDepthAt_add_dimClosureAt_of_isCohenMacaulay`. The
remaining hypothesis `hin` is the input of [Stacks, Tag 0EL1]. -/
@[stacks 0EL3 "clause (2): on a Cohen-Macaulay (for example normal) surface, H^0(X,E) -> \
lim H^0(Y_n,E_n) is an isomorphism; the depth-dimension bound is proved from the Cohen-Macaulay \
condition and the dimension formula, hin bundles the three inputs of 0EL1"]
theorem isIso_zeroSchemeComparison_zero_of_cohenMacaulaySurface
    {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [IsProperVariety k fX]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {s : Γ(L, ⊤)} {E : X.Modules}
    [E.IsQuasicoherent] [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hdim : topologicalKrullDim X = ((2 : ℕ) : WithBot ℕ∞))
    {A : Type u} [CommRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FiniteType k A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {I : Ideal A} {r : ℕ} {fam : Fin r → A} {f : A} [IsAdicComplete (Ideal.span {f}) A]
    {proj : PrimeSpectrum A → X}
    (hin : ZeroSchemeAlgebraizationInput k X L s E 1 A M I fam f proj) :
    IsIso (zeroSchemeComparison X L s E 0) :=
  isIso_zeroSchemeComparison_of_cohenMacaulayDepthDimBound fX hCM (by norm_num [hdim]) hin 0
    Nat.one_pos

/-- **Stacks Project, Tag 0EL3 (Example 52.28.3), clause (3).** In the situation of clause (2),
if `X` is a Cohen–Macaulay threefold then both

`H⁰(X, 𝓔) ⟶ lim H⁰(Yₙ, 𝓔ₙ)` and `H¹(X, 𝓔) ⟶ lim H¹(Yₙ, 𝓔ₙ)`

are isomorphisms.

This is the general pattern at `d = 3`, hence `σ = 2` and the two degrees `i = 0, 1`. The
source's closing remark that a *normal* threefold still gives `H⁰` is the general pattern at
`d = 2` applied to it: a normal local ring has depth at least `min(2, dim)`, so the bound `2`
holds although the dimension is three. -/
@[stacks 0EL3 "clause (3): on a Cohen-Macaulay threefold, H^i(X,E) -> lim H^i(Y_n,E_n) is an \
isomorphism for i = 0 and i = 1; the depth-dimension bound is proved from the Cohen-Macaulay \
condition and the dimension formula, hin bundles the three inputs of 0EL1"]
theorem isIso_zeroSchemeComparison_of_cohenMacaulayThreefold
    {k : Type u} [Field k] {X : Scheme.{u}} (fX : X ⟶ Spec (CommRingCat.of k))
    [IsProperVariety k fX]
    {L : X.Modules} [Stacks.Ample.IsInvertibleModule X L] {s : Γ(L, ⊤)} {E : X.Modules}
    [E.IsQuasicoherent] [_root_.AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} E]
    (hCM : AlgebraicGeometry.IsCohenMacaulay X)
    (hdim : topologicalKrullDim X = ((3 : ℕ) : WithBot ℕ∞))
    {A : Type u} [CommRing A] [IsNoetherianRing A] [Algebra k A] [Algebra.FiniteType k A]
    {M : Type u} [AddCommGroup M] [Module A M] [Module.Finite A M]
    {I : Ideal A} {r : ℕ} {fam : Fin r → A} {f : A} [IsAdicComplete (Ideal.span {f}) A]
    {proj : PrimeSpectrum A → X}
    (hin : ZeroSchemeAlgebraizationInput k X L s E 2 A M I fam f proj)
    (i : ℕ) (hi : i < 2) :
    IsIso (zeroSchemeComparison X L s E i) :=
  isIso_zeroSchemeComparison_of_cohenMacaulayDepthDimBound fX hCM (by norm_num [hdim]) hin i hi

end Stacks.Algebraization

end
