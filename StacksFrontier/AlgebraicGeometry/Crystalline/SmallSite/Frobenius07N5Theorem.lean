module

public import StacksFrontier.AlgebraicGeometry.Crystalline.FrobeniusNondegeneracyBoundedRank
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.FrobeniusFactorization07N5
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.BaseChangeArrow07QC
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.ChangeBaseQuasicoherentCrystal
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.InvertPrimeAnnihilation
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RelativeFrobeniusArrowCohomology07N5
public import StacksFrontier.AlgebraicGeometry.Crystalline.SmallSite.RelativeFrobeniusSmoothBound07N5

/-!
# [Stacks, Tag 07N5]: the Frobenius on crystalline cohomology is an isogeny

In Situation [Stacks, Tag 07N2], let `(E, F_E)` be a nondegenerate `F`-crystal, let
`A = Γ(S, 𝒪_S)` be Noetherian and `p`-adically complete and let `X → S₀` be proper and smooth.
Then the canonical map

`F_E ∘ (F_X)^*_cris : RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), E)`

becomes an isomorphism after inverting `p`.  That is `statement07N5`, where the tag is
registered.

## The source's proof, and the three arrows

The source factors its map through `X^{(1)} = X ×_{S₀, F_{S₀}} S₀` into

1. the base change map (07QC) `RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X^{(1)}/S), E^{(1)})`;
2. the pullback (07N6) `F_{X/S₀}^* : RΓ(Cris(X^{(1)}/S), E^{(1)}) ⟶ RΓ(Cris(X/S), (F_X)^*_cris E)`;
3. the map (07QD) induced by `F_E`;

and shows each becomes an isomorphism after inverting `p`: the first is an isomorphism outright,
by [Stacks, Tag 07MU] modulo every power of `p` together with the perfectness
[Stacks, Tag 07MY]; the second is an isogeny by [Stacks, Tag 07QB]; the third is an isogeny
because `F_E` has an inverse up to a power of `p`, [Stacks, Tag 07N4].

All three arrows exist in this library.  Arrows 1 and 2 are
`...SmallSite.baseChangeArrow07QC` and `...SmallSite.relativeFrobeniusArrow07N6` of
`SmallSite/FrobeniusTwistArrows.lean`; arrow 3 is `...SmallSite.frobeniusCohomologyMap`.

**Arrow 1 is an isomorphism**: `...SmallSite.isIso_baseChangeArrow07QC`
(`SmallSite/BaseChangeArrow07QC.lean`), the source's "the first is a quasi-isomorphism modulo all
powers of `p` by [Stacks, Tag 07MU]; hence it is a quasi-isomorphism since the complexes involved
are perfect in `D(A)`, see [Stacks, Tag 07MY]", proved at any models of the derived categories.

**Arrow 3's isogeny is proved**, as
`...SmallSite.becomesIsoAfterInvertingPrime_frobeniusCohomologyMap`, from
`Crystalline.FCrystal.Nondegenerate` and a bound on the rank.

**Arrow 2's isogeny is proved**, `becomesIsoAfterInvertingPrime_relativeFrobeniusArrow07N6`:
[Stacks, Tag 07QB] — for `X ⟶ S₀` smooth with `X` quasi-compact, through [Stacks, Tag 07Q9] and
[Stacks, Tag 07QA] —
(`...SmallSite.exists_bound_crisModuleCohomologyMap_relativeFrobeniusToTwist_of_smooth`) bounds the
kernel and the cokernel of every cohomology map of `F_{X/S₀}^*` at the crystal `E^{(1)}` by a
power of `p`; the identification of that map with arrow 2 on cohomology
(`...SmallSite.relativeFrobeniusArrow07N6_annihilation_of_crisModuleCohomologyMap`) carries the
bound to arrow 2; and `...SmallSite.becomesIsoAfterInvertingPrime_of_homology_annihilation`
(`SmallSite/InvertPrimeAnnihilation.lean`) turns it into invertibility after inverting `p`,
inverting `p` being induced by an exact functor and a module over `A[1/p]` killed by a power of
`p` being zero.

## The factorization and the rank bound

* The source's "the map of the theorem is the composition of the three maps": the composite of
  arrows 1 and 2 is the one-step comparison for the Frobenius square,
  `...SmallSite.frobeniusBaseChangeArrows07N5_eq_comp` (so `frobeniusMap07N5Canonical_eq_comp`)
  (`SmallSite/FrobeniusFactorization07N5.lean`), the compatibility of the canonical
  transformation of [Stacks, Tag 05T2] with the composition of the two change-of-base squares.
* The bound on the rank of `E` that [Stacks, Tag 07N4] uses:
  `exists_hasBoundedCommonLocalRank_of_isProper`, from the quasi-compactness of `X` that
  properness of `X ⟶ S₀` over the affine `S₀` gives.

## Faithfulness

The conclusion is `...SmallSite.Statement07N5` at `...SmallSite.frobeniusMap07N5Canonical`, the
library's canonical `F_E ∘ (F_X)^*_cris`, whose underived input is pinned pointwise to
`Crystalline.FCrystal.sectionsFrobenius` by
`...SmallSite.sectionsMap_frobeniusBigSections_val`.  Its standing hypotheses are the tag's own,
one for one, as the table in `SmallSite/FrobeniusInvertPrime.lean` records; none is weakened and
none is dropped.  `Crystalline.FCrystal` is [Stacks, Tag 07N3]'s pair — a crystal in finite
locally free quasi-coherent `𝒪_{X/S}`-modules together with `F_E : (F_X)^*_cris E ⟶ E` — and
`Crystalline.FCrystal.Nondegenerate` is 07N3's `V ∘ F_E = p ^ i`.

## Main results

Everything lives in the namespace `Crystalline.GlobalCrystallineSituation.SmallSite`.

* `relativeFrobeniusArrow07N6_homology_annihilation` — [Stacks, Tag 07QB] at arrow 2.
* `becomesIsoAfterInvertingPrime_relativeFrobeniusArrow07N6` — **arrow 2 becomes an isomorphism
  after inverting `p`**.
* `becomesIsoAfterInvertingPrime_baseChangeArrow07QC_comp` — **arrows 1 and 2 together**.
* `exists_hasBoundedCommonLocalRank_of_isProper` — the rank bound of [Stacks, Tag 07N4].
* `statement07N5` — **[Stacks, Tag 07N5]**.

## References

* [Stacks Project, Tag 07N5](https://stacks.math.columbia.edu/tag/07N5)
* [Stacks Project, Tag 07N2](https://stacks.math.columbia.edu/tag/07N2)
* [Stacks Project, Tag 07N3](https://stacks.math.columbia.edu/tag/07N3)
* [Stacks Project, Tag 07N4](https://stacks.math.columbia.edu/tag/07N4)
* [Stacks Project, Tag 07MU](https://stacks.math.columbia.edu/tag/07MU)
* [Stacks Project, Tag 07MY](https://stacks.math.columbia.edu/tag/07MY)
* [Stacks Project, Tag 07QB](https://stacks.math.columbia.edu/tag/07QB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite
open scoped AlgebraicGeometry

universe u wS wB wA wP

noncomputable section

namespace Crystalline.GlobalCrystallineSituation.SmallSite

/-! ### Auxiliary derived categories -/

/-- The standard model of the derived category of abelian sheaves on `Cris(X/S)`, used only
inside proofs, where [Stacks, Tag 07QA] passes through abelian cohomology. -/
abbrev smallSheafDerivedCategory (S : GlobalCrystallineSituation.{u}) :
    HasDerivedCategory (Sheaf (smallTopology S) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _

/-- The standard model of the derived category of abelian sheaves on `X_Zar`, used only inside
proofs. -/
abbrev opensSheafDerivedCategory (S : GlobalCrystallineSituation.{u}) :
    HasDerivedCategory (Sheaf (opensTopology S) AddCommGrpCat.{u + 1}) :=
  HasDerivedCategory.standard _


variable (T : Crystalline.FCrystalSituation.{u})
  [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]
  [HasDerivedCategory.{wP} (ModuleCat.{u + 1} (invertPrimeRing T.global))]

/-! ### Arrows 1 and 2 -/

omit [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]
  [HasDerivedCategory.{wP} (ModuleCat.{u + 1} (invertPrimeRing T.global))] in
/-- **The space of `X` is quasi-compact** when `X ⟶ S₀` is proper: the closed fibre `S₀` of the
affine `S` is affine, hence quasi-compact, and a proper morphism is quasi-compact. -/
theorem compactSpace_of_isProper (hproper : IsProper T.global.toClosedFiber) :
    CompactSpace T.global.X :=
  QuasiCompact.compactSpace_of_compactSpace T.global.toClosedFiber

omit [HasDerivedCategory.{wP} (ModuleCat.{u + 1} (invertPrimeRing T.global))] in
/-- **[Stacks, Tag 07QB] at arrow 2 of the proof of [Stacks, Tag 07N5]**: for `X ⟶ S₀` proper
and smooth, in every degree some power of `p` annihilates the kernel and the cokernel of the map
that arrow 2, `F_{X/S₀}^* : RΓ(Cris(X^{(1)}/S), E^{(1)}) ⟶ RΓ(Cris(X/S), (F_X)^*_cris E)`, induces
on cohomology.

The bound is `...SmallSite.exists_bound_crisModuleCohomologyMap_relativeFrobeniusToTwist_of_smooth`
— [Stacks, Tag 07QB] for `X ⟶ S₀` smooth of locally bounded relative dimension, through
[Stacks, Tag 07Q9] and [Stacks, Tag 07QA] — at the crystal in quasi-coherent modules
`E^{(1)}` (`Crystalline.FCrystal.` …
`isQuasiCoherentCrystal_restrictSheafOfModules_sigmaModulePullback`),
carried to arrow 2 by the identification of the two maps on cohomology,
`...SmallSite.relativeFrobeniusArrow07N6_annihilation_of_crisModuleCohomologyMap`.  The derived
categories of abelian sheaves through which [Stacks, Tag 07QA] passes appear only inside the
proof, at Mathlib's standard model. -/
theorem relativeFrobeniusArrow07N6_homology_annihilation (hproper : IsProper T.global.toClosedFiber)
    (hsmooth : Smooth T.global.toClosedFiber) (E : Crystalline.FCrystal T) (n : ℤ) :
    ∃ k : ℕ,
      (T.global.p ^ k) • 𝟙 (kernel ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} ↥Γ(T.global.S.scheme, ⊤)) n).map
            (relativeFrobeniusArrow07N6 T E))) = 0 ∧
      (T.global.p ^ k) • 𝟙 (cokernel ((DerivedCategory.homologyFunctor
          (ModuleCat.{u + 1} ↥Γ(T.global.S.scheme, ⊤)) n).map
            (relativeFrobeniusArrow07N6 T E))) = 0 := by
  let i1 := smallSheafDerivedCategory T.global
  let i2 := smallSheafDerivedCategory (T.global.frobeniusTwistSituation T.prime_mem)
  let i3 := opensSheafDerivedCategory T.global
  let i4 := opensSheafDerivedCategory (T.global.frobeniusTwistSituation T.prime_mem)
  let i5 := HasDerivedCategory.standard AddCommGrpCat.{u + 1}
  have hb := @exists_bound_crisModuleCohomologyMap_relativeFrobeniusToTwist_of_smooth
    T.global T.prime_mem i1 i2 i3 i4 i5 hsmooth (compactSpace_of_isProper T hproper)
  obtain ⟨D, hD⟩ := hb
  have hG := E.isQuasiCoherentCrystal_restrictSheafOfModules_sigmaModulePullback
  have hb' := hD (restrictSheafOfModules (T.sigmaModulePullback.obj E.crystal)) hG
  exact @relativeFrobeniusArrow07N6_annihilation_of_crisModuleCohomologyMap T _ _ _ _ _
    i1 i2 i3 i4 i5 E (fun i => ⟨D * (i + 1), hb' i⟩) n

/-- **Arrow 2 of the proof of [Stacks, Tag 07N5] becomes an isomorphism after inverting `p`**,
for `X ⟶ S₀` proper and smooth.

`...SmallSite.becomesIsoAfterInvertingPrime_of_homology_annihilation` is the whole argument from
`relativeFrobeniusArrow07N6_homology_annihilation`: a morphism of `D(Mod_A)` whose cohomology maps
have kernels and cokernels annihilated by powers of `p` is inverted by the exact functor
`- ⊗_A A[1/p]`. -/
theorem becomesIsoAfterInvertingPrime_relativeFrobeniusArrow07N6
    (hproper : IsProper T.global.toClosedFiber) (hsmooth : Smooth T.global.toClosedFiber)
    (E : Crystalline.FCrystal T) :
    BecomesIsoAfterInvertingPrime T.global (relativeFrobeniusArrow07N6 T E) :=
  becomesIsoAfterInvertingPrime_of_homology_annihilation T.global _
    (relativeFrobeniusArrow07N6_homology_annihilation T hproper hsmooth E)

/-- **The composite of arrows 1 and 2 becomes an isomorphism after inverting `p`** as soon as
arrow 1 is an isomorphism: an isomorphism is an isogeny, arrow 2 is an isogeny, and the property
is closed under composition. -/
theorem becomesIsoAfterInvertingPrime_baseChangeArrow07QC_comp (E : Crystalline.FCrystal T)
    (h1 : IsIso (baseChangeArrow07QC T E))
    (hproper : IsProper T.global.toClosedFiber) (hsmooth : Smooth T.global.toClosedFiber) :
    BecomesIsoAfterInvertingPrime T.global
      (baseChangeArrow07QC T E ≫ relativeFrobeniusArrow07N6 T E) :=
  (becomesIsoAfterInvertingPrime_of_isIso T.global (baseChangeArrow07QC T E)).comp
    T.global (becomesIsoAfterInvertingPrime_relativeFrobeniusArrow07N6 T hproper hsmooth E)

/-! ### The rank bound -/

omit [HasDerivedCategory.{wS} (ModuleSheaf T.global)]
  [HasDerivedCategory.{wS} (ModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.global)]
  [HasDerivedCategory.{wB} (BigModuleSheaf T.frobeniusTwistSituation)]
  [HasDerivedCategory.{wA} (ModuleCat.{u + 1} Γ(T.global.S.scheme, ⊤))]
  [HasDerivedCategory.{wP} (ModuleCat.{u + 1} (invertPrimeRing T.global))] in
/-- **An `F`-crystal over a proper `X ⟶ S₀` has a bounded common local rank**, the hypothesis
under which [Stacks, Tag 07N4] gives `F_E` a two-sided inverse up to a power of `p`.  The base
`S₀` is affine (`S` is), so properness of `X ⟶ S₀` makes `X` quasi-compact, and on a quasi-compact
`X` the local ranks of a finite locally free crystal are bounded
(`Crystalline.FCrystal.exists_hasBoundedCommonLocalRank_of_compactSpace`). -/
theorem exists_hasBoundedCommonLocalRank_of_isProper (hproper : IsProper T.global.toClosedFiber)
    (E : Crystalline.FCrystal T) : ∃ rmax : ℕ, E.HasBoundedCommonLocalRank rmax :=
  have := compactSpace_of_isProper T hproper
  E.exists_hasBoundedCommonLocalRank_of_compactSpace

/-! ### The theorem -/

omit [HasDerivedCategory.{wP} (ModuleCat.{u + 1} (invertPrimeRing T.global))] in
/-- **The map of [Stacks, Tag 07N5] is the composite of the three arrows of its proof**: the
canonical `F_E ∘ (F_X)^*_cris` is `baseChangeArrow07QC`, then `relativeFrobeniusArrow07N6`, then
`...SmallSite.frobeniusCohomologyMap` — the source's "the map of the theorem is the composition of
the three maps (60.26.4.1), (60.26.4.2) and (60.26.4.3)". -/
theorem frobeniusMap07N5Canonical_eq_comp (E : Crystalline.FCrystal T) :
    frobeniusMap07N5Canonical T E =
      (baseChangeArrow07QC T E ≫ relativeFrobeniusArrow07N6 T E) ≫ frobeniusCohomologyMap T E := by
  rw [frobeniusMap07N5Canonical, frobeniusBaseChangeArrows07N5_eq_comp]
  rfl

/-- **[Stacks, Tag 07N5].**  In Situation [Stacks, Tag 07N2] let `(E, F_E)` be a nondegenerate
`F`-crystal.  Assume `A` is a `p`-adically complete Noetherian ring and that `X → S₀` is proper
smooth.  Then the canonical map

`F_E ∘ (F_X)^*_cris : RΓ(Cris(X/S), E) ⊗^L_{A, σ} A ⟶ RΓ(Cris(X/S), E)`

becomes an isomorphism after inverting `p`.

The conclusion is `...SmallSite.Statement07N5` at `...SmallSite.frobeniusMap07N5Canonical`, the
canonical `F_E ∘ (F_X)^*_cris`, and its standing hypotheses — `A` Noetherian, `A` `p`-adically
complete, `X ⟶ S₀` proper, `X ⟶ S₀` smooth, `E` an `F`-crystal, `E` nondegenerate — are the
tag's own.

The proof is the source's.  The map of the theorem is the composite of the three arrows
(`frobeniusMap07N5Canonical_eq_comp`).  Arrow 1 is an isomorphism
(`...SmallSite.isIso_baseChangeArrow07QC`, from [Stacks, Tag 07MU] and [Stacks, Tag 07MY]);
arrow 2 is an isogeny (`becomesIsoAfterInvertingPrime_relativeFrobeniusArrow07N6`, from
[Stacks, Tag 07QB]), so arrows 1 and 2 together are an isogeny
(`becomesIsoAfterInvertingPrime_baseChangeArrow07QC_comp`); arrow 3 is an isogeny by
nondegeneracy (`...SmallSite.becomesIsoAfterInvertingPrime_frobeniusCohomologyMap`,
[Stacks, Tag 07N4], with the rank bound `exists_hasBoundedCommonLocalRank_of_isProper`); and the
three combine by `...SmallSite.becomesIsoAfterInvertingPrime_iff_of_factors`. -/
@[stacks 07N5 "the theorem: for a nondegenerate F-crystal over a p-adically complete Noetherian \
A with X -> S_0 proper smooth, the canonical map F_E o (F_X)_cris^* on RGamma(Cris(X/S), E) \
becomes an isomorphism after inverting p"]
theorem statement07N5 : Statement07N5 T (frobeniusMap07N5Canonical T) := by
  intro hnoeth hcomplete hproper hsmooth E hE
  obtain ⟨rmax, hr⟩ := exists_hasBoundedCommonLocalRank_of_isProper T hproper E
  exact (becomesIsoAfterInvertingPrime_iff_of_factors T E hr hE
      (frobeniusMap07N5Canonical_eq_comp T E)).2
    (becomesIsoAfterInvertingPrime_baseChangeArrow07QC_comp T E
      (isIso_baseChangeArrow07QC T hnoeth hcomplete hproper hsmooth E) hproper hsmooth)

end Crystalline.GlobalCrystallineSituation.SmallSite

end

end
