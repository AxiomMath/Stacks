module

public import Mathlib.Algebra.Homology.HomologicalComplexAbelian
public import Mathlib.Algebra.Homology.HomologySequence
public import StacksFrontier.CategoryTheory.Sites.GlobalSections.CohomologyAtTheTerminalObject
public import StacksFrontier.Topology.Constructible.MeetConstructible
public import StacksFrontier.Topology.Sheaves.Cohomology.Locality.OpensSiteResolution
public import StacksFrontier.Topology.Sheaves.Cohomology.SupportedComplexes.UnderlyingAbelianLocalCohomologyInvertible
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces
public import StacksCore.Tactic.StacksAttribute

/-!
# Cohomology with support in a constructible closed subset of a spectral space

Let `X` be a spectral space of Krull dimension at most `d`, let `F` be an abelian sheaf on `X`
and let `Z ⊆ X` be a closed subset which is constructible. Then the cohomology of `F` with
support in `Z` vanishes in every degree above `d`. Together with the vanishing of `H^q(X, F)`
and the surjectivity of `H^d(X, F) → H^d(U, F)` onto a quasi-compact open, which
`StacksFrontier/Topology/Sheaves/Cohomology/Vanishing/SpectralSpaces.lean` proves, this completes
[Stacks, Tag 0A3G].

## Main definitions

* `CohomologyVanishing.supportPairShortComplex`: the short complex of complexes of abelian
  groups `Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(X ∖ Z, I)` obtained from an injective resolution `I` of the
  sheaf.

## Main results

* `CohomologyVanishing.supportPairShortComplex_shortExact`: the short complex is short exact,
  because an injective abelian sheaf is flasque.
* `CohomologyVanishing.subsingleton_rightDerived_supportedSections_of_topologicalKrullDim_le`:
  clause (3) of [Stacks, Tag 0A3G].

## The argument

This is the source's own proof. Cohomology with support in `Z` is the right derived functor of
`Stacks.Cohomology.SupportedComplexes.supportedSectionsEvaluation Z ⊤`, the sections over `X`
of the subsheaf of sections supported on `Z`, and that functor is the kernel of restriction to
`U = X ∖ Z`. On an injective — hence flasque — abelian sheaf the restriction to `U` is
surjective, so applying the three functors degreewise to an injective resolution `I` of `F`
gives a short exact sequence of complexes of abelian groups, whose long exact homology sequence
is the long exact sequence of the pair

`H^{q-1}(X, F) ⟶ H^{q-1}(U, F) ⟶ H^q_Z(X, F) ⟶ H^q(X, F)`.

For `q > d` the right-hand term vanishes by clause (1), so `H^q_Z(X, F)` is the image of the
connecting map out of `H^{q-1}(U, F)`. Constructibility of the closed set `Z` makes `U` a
quasi-compact open, so clause (2) — applied in degree `q - 1`, which is at least `d` — says
that `H^{q-1}(X, F) ⟶ H^{q-1}(U, F)` is surjective; the connecting map therefore vanishes, and
with it `H^q_Z(X, F)`.

## Implementation notes

Clauses (1) and (2) are stated for Mathlib's `Ext`-theoretic cohomology, while the long exact
sequence lives on the injective resolution. The two are matched by the comparison layer of
`StacksFrontier/Topology/Sheaves/Cohomology/Locality/OpensSiteResolution.lean`, which is compatible
with restriction and so can carry clause (2) — a statement about a restriction map — onto the
resolution.

The open complement is spelled `⊤ ⊓ ⟨Zᶜ, _⟩` rather than `⟨Zᶜ, _⟩` because that is the form in
which `Stacks.Cohomology.SupportedComplexes.restrictionToSupportComplement` presents restriction
away from `Z`; over the open `⊤` the two agree.

## References

* [Stacks Project, Lemma 20.33.5 (Tag 0A3G)](https://stacks.math.columbia.edu/tag/0A3G)
* [Stacks Project, Lemma 20.8.1 (Tag 01EA)](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Lemma 21.7.2 (Tag 03AY)](https://stacks.math.columbia.edu/tag/03AY)
* [Stacks Project, Section 20.34 (Tag 0G6W)](https://stacks.math.columbia.edu/tag/0G6W)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open Stacks.Cohomology.SupportedComplexes
open Stacks.Cohomology.UnderlyingAbelianSheaf

universe u

namespace Stacks.CohomologyVanishing

variable {X : TopCat.{u}}

/-! ### The short exact sequence of the pair on an injective resolution -/

/-- The short complex of complexes of abelian groups

`Γ_Z(X, I) ⟶ Γ(X, I) ⟶ Γ(X ∖ Z, I)`

obtained by applying, degreewise, the sections supported on `Z`, the sections over `X` and the
sections over `X ∖ Z` to an injective resolution `I` of an abelian sheaf `F`. -/
def supportPairShortComplex (Z : Set X) (hZ : IsClosed Z)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (I : InjectiveResolution F) :
    ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) :=
  ShortComplex.mk
    (((supportedSectionsEvaluationInclusion Z ⊤).mapHomologicalComplex
      (ComplexShape.up ℕ)).app I.cocomplex)
    (((restrictionToSupportComplement Z hZ ⊤).mapHomologicalComplex
      (ComplexShape.up ℕ)).app I.cocomplex)
    (HomologicalComplex.hom_ext _ _ fun n =>
      supportedSectionsEvaluation_comp_zero Z hZ ⊤ (I.cocomplex.X n))

/-- **The short exact sequence of the pair `(X, X ∖ Z)` on an injective resolution.** The terms
of an injective resolution are injective, hence flasque by [Stacks, Tag 01EA], so restriction to
the open complement of `Z` is surjective on them, and the sections supported on `Z` are by
construction the kernel of that surjection. -/
@[sga "2 I 1.8" "special case"]
lemma supportPairShortComplex_shortExact (Z : Set X) (hZ : IsClosed Z)
    {F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}} (I : InjectiveResolution F) :
    (supportPairShortComplex Z hZ I).ShortExact := by
  rw [HomologicalComplex.shortExact_iff_degreewise_shortExact]
  exact fun n => ClosedImmersionSheaves.supportedSections_restriction_shortExact Z hZ
    (I.cocomplex.X n)
    (@Stacks.Cohomology.isFlasque_of_injective X (I.cocomplex.X n) (I.injective n)) ⊤

/-! ### Clause (3) of Stacks 0A3G -/

/-- **[Stacks, Tag 0A3G], clause (3).** Let `X` be a spectral space of Krull dimension at most
`d`, let `F` be an abelian sheaf on `X` and let `Z` be a constructible closed subset of `X`.
Then the cohomology of `F` with support in `Z` vanishes in every degree `q > d`.

Cohomology with support in `Z` is the right derived functor of the sections over `X` of the
subsheaf of sections supported on `Z`. The proof is the source's: the long exact sequence of the
pair `(X, X ∖ Z)`, built on an injective resolution, together with clause (1) for `H^q(X, F)`
and clause (2) for the surjectivity of `H^{q-1}(X, F) → H^{q-1}(X ∖ Z, F)`, the complement of a
constructible closed set being a quasi-compact open. -/
@[stacks 0A3G "clause (3): cohomology with support in a constructible closed subset vanishes \
  above the dimension"]
theorem subsingleton_rightDerived_supportedSections_of_topologicalKrullDim_le
    [SpectralSpace X]
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) (d q : ℕ)
    (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (Z : Set X) (hZ : IsClosed Z)
    (hZc : IsConstructible Z) (hq : d < q) :
    Subsingleton (((supportedSectionsEvaluation Z ⊤).rightDerived q).obj F) := by
  obtain ⟨n, rfl⟩ : ∃ n : ℕ, q = n + 1 := ⟨q - 1, by omega⟩
  have hdn : d ≤ n := by omega
  let I : InjectiveResolution F := injectiveResolution F
  let S : ShortComplex (CochainComplex AddCommGrpCat.{u} ℕ) := supportPairShortComplex Z hZ I
  have hS : S.ShortExact := supportPairShortComplex_shortExact Z hZ I
  -- The open complement of `Z` is quasi-compact, because `Z` is constructible.
  have hUcompact :
      IsCompact (((⊤ : Opens X) ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩ : Opens X) : Set X) := by
    simpa using (IsRetrocompact_of_IsConstructible hZc.compl).isCompact
  -- Clause (2), in degree `n ≥ d`: restriction to the complement is surjective.
  have hsurj := surjective_cohomologyPresheaf_map_top_of_topologicalKrullDim_le
    F n (hdim.trans (by exact_mod_cast hdn))
    ((⊤ : Opens X) ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩) hUcompact
  -- `inf_le_left` and `le_top` prove the same proposition, so the two restriction maps agree.
  have hepiPresheaf :
      Epi ((F.cohomologyPresheaf n).map
        (homOfLE (inf_le_left :
          (⊤ : Opens X) ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩ ≤ ⊤)).op) :=
    (AddCommGrpCat.epi_iff_surjective _).2 hsurj
  -- Transport that surjectivity onto the injective resolution.  `S.g` is restriction applied
  -- degreewise to `I`, which is the restriction of sections the comparison layer speaks about.
  have hepi : Epi (HomologicalComplex.homologyMap S.g n) :=
    Stacks.Cohomology.OpensSite.epi_homologyMap_sections_of_epi_cohomologyPresheaf_map
      (homOfLE (inf_le_left : (⊤ : Opens X) ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩ ≤ ⊤)) I n hepiPresheaf
  -- The connecting map out of `H^n(X ∖ Z, F)` therefore vanishes.
  -- Exactness at `H^{n+1}_Z(X, F)` makes the map to `H^{n+1}(X, F)` injective.
  have hmono : Mono (HomologicalComplex.homologyMap S.f (n + 1)) :=
    (ShortComplex.exact_iff_mono _ (zero_of_epi_comp _ (hS.comp_δ n (n + 1) rfl))).mp
      (hS.homology_exact₁ n (n + 1) rfl)
  -- Clause (1): `H^{n+1}(X, F)` vanishes.
  have hmid : IsZero ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
      (ComplexShape.up ℕ) (n + 1)).obj S.X₂) := by
    have h1 : Subsingleton (Sheaf.H.{u, u, u, u} F (n + 1)) :=
      subsingleton_sheafH_of_topologicalKrullDim_le d ↥X inferInstance inferInstance F (n + 1)
        hdim hq
    have : Subsingleton ((F.cohomologyPresheaf (n + 1)).obj (op (⊤ : Opens X))) :=
      (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top F
        (n + 1)).mp h1
    exact IsZero.of_iso (AddCommGrpCat.isZero_of_subsingleton _)
      (Stacks.Cohomology.OpensSite.sectionsHomologyIsoCohomologyPresheaf ⊤ I (n + 1))
  -- Hence `H^{n+1}_Z(X, F)` vanishes.
  have hleft : IsZero ((HomologicalComplex.homologyFunctor AddCommGrpCat.{u}
      (ComplexShape.up ℕ) (n + 1)).obj S.X₁) := by
    rw [IsZero.iff_id_eq_zero]
    exact hmono.right_cancellation _ _ (hmid.eq_of_tgt _ _)
  exact AddCommGrpCat.subsingleton_of_isZero
    (hleft.of_iso (I.isoRightDerivedObj (supportedSectionsEvaluation Z ⊤) (n + 1)))

end Stacks.CohomologyVanishing

end
