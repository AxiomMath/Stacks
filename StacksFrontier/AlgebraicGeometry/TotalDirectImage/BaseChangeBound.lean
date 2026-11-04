module

public import StacksFrontier.AlgebraicGeometry.TotalDirectImage.BoundedCohomologicalDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A degree bound for the total direct image, uniform in the base change

Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism of schemes with `S`
quasi-compact. There is an integer `N`, depending only on `f`, such that for *every* morphism
`g : S' ⟶ S` the base change `f' : X ×_S S' ⟶ S'` satisfies `H^q(Rf'_* E) = 0` for all `q ≥ N`
and every object `E` of `D(𝒪_{X ×_S S'})` with quasi-coherent cohomology sheaves and vanishing
cohomology in positive degrees.

The argument is the one in the source, and it is the argument of
`AlgebraicGeometry.exists_isZero_homology_derivedPushforward_of_isLE_zero` with the basis and
the degree produced for the base change instead of for `f` itself. Nothing about the morphism
enters
`AlgebraicGeometry.isZero_homology_derivedPushforward_of_isBasis`: it takes a basis `B` of the
opens of the target and a degree beyond which the higher cohomology of quasi-coherent modules
over the preimages of the members of `B` vanishes, and derives the bound on the cohomology
sheaves of the derived direct image. So all that is needed is that basis and that degree for
the base change, with the degree independent of `g`, and that is exactly what
`AlgebraicGeometry.exists_affine_cover_data` and
`AlgebraicGeometry.exists_isBasis_affine_cover_preimage_of_commSq` supply: a finite affine open
covering `S = S₁ ∪ … ∪ S_m` together with finite affine open coverings of the `f⁻¹(S_j)` and a
single degree `d` dominating the bound of [Stacks, Tag 071L] for each of them, transported
across the square to a basis of `S'` and coverings of the preimages under `f'` with the same
`d`.

The intermediate `isZero_homology_derivedPushforward_of_commSq` is stated for a bare commutative
square, as its input `AlgebraicGeometry.isZero_rightDerivedPlus_pushforward_of_commSq` is: the
only thing the construction of the coverings uses is `pr⁻¹(f⁻¹(S_j)) = f'⁻¹(g⁻¹(S_j))`, with the
affineness of the opens `pr⁻¹(A) ⊓ f'⁻¹(V)` as a separate hypothesis. For a cartesian square
that hypothesis is `AlgebraicGeometry.isAffineOpen_inf_preimage`.

## Main results

* `AlgebraicGeometry.isZero_homology_derivedPushforward_of_commSq`: the bound on the cohomology
  sheaves of `Rf'_*` for a commutative square, from affine covering data for `f`.
* `AlgebraicGeometry.exists_uniform_isZero_homology_derivedPushforward`:
  **[Stacks, Tag 08D5] part (3)**, the bound chosen uniformly in an arbitrary base change.

The other two parts of [Stacks, Tag 08D5], which complete the covering set of the tag, are
`AlgebraicGeometry.isQuasicoherent_derivedPushforward` and
`AlgebraicGeometry.exists_isZero_homology_derivedPushforward_of_isLE_zero`.

## Implementation notes

`AlgebraicGeometry.isZero_homology_derivedPushforward_of_isBasis` wants the vanishing for the
`ℤ`-indexed `CategoryTheory.Functor.rightDerivedPlus` of the abelian-group-valued sections
functor `secF`, whereas `AlgebraicGeometry.isZero_cohomology_of_affine_cover_bound` produces it
for the `ℕ`-indexed cohomology groups `Hgroup`, which are by construction the `ℕ`-indexed right
derived functors of `secF`; `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff` is the
change of indexing. This is the same step as in
`AlgebraicGeometry.exists_isBasis_isZero_rightDerivedPlus_sectionsOnPreimage`, which cannot be
reused here because its basis is a basis of `S` and bases do not transport along `g`.

The base change `X ×_S S'` of a quasi-compact quasi-separated `X` need not be quasi-separated as
a space, `S'` being arbitrary, so no quasi-separatedness of the total space may be used; the
covering data carries its own quasi-compactness, which is why
`AlgebraicGeometry.exists_isBasis_affine_cover_preimage_of_commSq` asks for affine coverings of
the finite intersections rather than for a bound on `AlgebraicGeometry.Scheme.affineCoverNum`.

Everything here is at `HasDerivedCategory.standard`, the model [Stacks, Tag 0D5W] and
[Stacks, Tag 0BKJ] are stated in.

## References

* [Stacks Project, Tag 08D5](https://stacks.math.columbia.edu/tag/08D5)
* [Stacks Project, Tag 01XJ](https://stacks.math.columbia.edu/tag/01XJ)
* [Stacks Project, Tag 071L](https://stacks.math.columbia.edu/tag/071L)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPushforward)

universe u

attribute [local instance] HasDerivedCategory.standard

namespace AlgebraicGeometry

/-- **The bound on the cohomology sheaves of a derived direct image across a commutative
square.** Let `pr ≫ f = f' ≫ g` be a commutative square of schemes, let `S = S₁ ∪ … ∪ S_m` be a
finite affine open covering of the target of `f` and let `f⁻¹(S_j) = U_{j1} ∪ … ∪ U_{jt_j}` be
finite affine open coverings each of whose nonempty finite intersections is covered by affine
opens in a number bounded by `d` in the sense of [Stacks, Tag 071L]; assume that
`pr⁻¹(A) ⊓ f'⁻¹(V)` is affine whenever `A ⊆ f⁻¹(S_j)` and `V ⊆ g⁻¹(S_j)` are affine opens. Then
`H^q(Rf'_* E) = 0` for every `q ≥ d` and every `E` in `D(𝒪_{X'})` with quasi-coherent cohomology
sheaves and vanishing cohomology in positive degrees.

The covering data transports across the square by
`AlgebraicGeometry.exists_isBasis_affine_cover_preimage_of_commSq`, giving a basis of the opens
of `S'` over whose preimages the higher cohomology of quasi-coherent modules vanishes from
degree `d` onwards; `AlgebraicGeometry.isZero_homology_derivedPushforward_of_isBasis` turns that
into the bound. -/
@[ega "III 1.4.12" "more general"]
theorem isZero_homology_derivedPushforward_of_commSq {X S X' S' : Scheme.{u}} (f : X ⟶ S)
    (f' : X' ⟶ S') (pr : X' ⟶ X) (g : S' ⟶ S) (hsq : pr ≫ f = f' ≫ g)
    {m : ℕ} {S₀ : Fin m → S.Opens} (hS₀cov : ⨆ j, S₀ j = ⊤)
    (haff : ∀ (j : Fin m) (A : X.Opens) (V : S'.Opens), IsAffineOpen A → IsAffineOpen V →
      A ≤ f ⁻¹ᵁ S₀ j → V ≤ g ⁻¹ᵁ S₀ j → IsAffineOpen (pr ⁻¹ᵁ A ⊓ f' ⁻¹ᵁ V))
    {t : Fin m → ℕ} {U : ∀ j, Fin (t j) → X.Opens} (hUaff : ∀ j i, IsAffineOpen (U j i))
    (hUcov : ∀ j, ⨆ i, U j i = f ⁻¹ᵁ S₀ j) {d : ℕ}
    (hUbd : ∀ (j : Fin m) (s : Finset (Fin (t j))), s.Nonempty →
      ∃ (c : ℕ) (A : Fin c → X.Opens), (∀ a, IsAffineOpen (A a)) ∧
        (⨆ a, A a = s.inf (U j)) ∧ s.card + c - 1 ≤ d)
    (E : DerivedCategory.{u + 1} X'.Modules)
    (hcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X'.Modules i).obj E).IsQuasicoherent)
    (hE : E.IsLE 0) (q : ℤ) (hq : (d : ℤ) ≤ q) :
    IsZero ((DerivedCategory.homologyFunctor S'.Modules q).obj
      ((derivedPushforward f'.toLRSHom.toShHom).obj E)) := by
  obtain ⟨B, hB, hcov⟩ := exists_isBasis_affine_cover_preimage_of_commSq f f' pr g hsq hS₀cov
    haff hUaff hUcov hUbd
  refine isZero_homology_derivedPushforward_of_isBasis f' (N := d) hB
    (fun V hV M hM p hp ↦ ?_) E hcoh 0 hE q (by omega)
  have : M.IsQuasicoherent := hM
  obtain ⟨k, W, hWaff, hWcov, hWbd⟩ := hcov V hV
  obtain ⟨P, hP⟩ : ∃ P : ℕ, p = (P : ℤ) :=
    ⟨p.toNat, (Int.toNat_of_nonneg (le_trans (Int.natCast_nonneg d) hp)).symm⟩
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff
    (secF X'.ringCatSheaf (f' ⁻¹ᵁ V)) hP M).2 ?_
  exact isZero_cohomology_of_affine_cover_bound M d W hWaff hWcov hWbd P (by omega)

/-- **Stacks 08D5, part (3).** Let `f : X ⟶ S` be a quasi-compact and quasi-separated morphism
of schemes with `S` quasi-compact. There is an integer `N`, depending only on `f`, such that for
every morphism `g : S' ⟶ S` the base change `f' : X ×_S S' ⟶ S'` satisfies `H^q(Rf'_* E) = 0`
for every `q ≥ N` and every object `E` of `D(𝒪_{X ×_S S'})` with quasi-coherent cohomology
sheaves and vanishing cohomology in positive degrees.

The covering data of `f` is extracted once, by
`AlgebraicGeometry.exists_affine_cover_data`, and
`isZero_homology_derivedPushforward_of_commSq` is applied to the cartesian square, whose
affineness hypothesis is `AlgebraicGeometry.isAffineOpen_inf_preimage`. The degree `N` is read
off the covering data alone, so it does not depend on `g`.

This is one of the three declarations carrying [Stacks, Tag 08D5]; the other two are
`AlgebraicGeometry.isQuasicoherent_derivedPushforward` (part (1)) and
`AlgebraicGeometry.exists_isZero_homology_derivedPushforward_of_isLE_zero` (part (2)). -/
@[stacks 08D5 "uniform_bound_after_base_change"]
theorem exists_uniform_isZero_homology_derivedPushforward {X S : Scheme.{u}} (f : X ⟶ S)
    [QuasiCompact f] [QuasiSeparated f] [CompactSpace S] :
    ∃ N : ℤ, ∀ (S' : Scheme.{u}) (g : S' ⟶ S)
      (E : DerivedCategory.{u + 1} (pullback f g).Modules),
      (∀ i : ℤ, ((DerivedCategory.homologyFunctor (pullback f g).Modules i).obj
        E).IsQuasicoherent) →
      E.IsLE 0 → ∀ q : ℤ, N ≤ q →
        IsZero ((DerivedCategory.homologyFunctor S'.Modules q).obj
          ((derivedPushforward (pullback.snd f g).toLRSHom.toShHom).obj E)) := by
  obtain ⟨m, S₀, t, U, d, hS₀aff, hS₀cov, hUaff, hUcov, hUbd⟩ := exists_affine_cover_data f
  refine ⟨(d : ℤ), fun S' g E hcoh hE q hq ↦ ?_⟩
  refine isZero_homology_derivedPushforward_of_commSq f (pullback.snd f g) (pullback.fst f g) g
    pullback.condition hS₀cov (fun j A V hA hV hAle hVle ↦ ?_) hUaff hUcov hUbd E hcoh hE q hq
  have : IsAffine A.toScheme := hA
  have : IsAffine V.toScheme := hV
  have : IsAffine (S₀ j).toScheme := hS₀aff j
  exact isAffineOpen_inf_preimage f g hAle hVle

end AlgebraicGeometry

end
