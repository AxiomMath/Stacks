module

public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteLocallyFreeOfRank
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteStratificationRank
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineLocalFree
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.PushforwardAffine

/-!
# The rank of the source map of a groupoid scheme on a Fitting stratum

Let `G` be a groupoid scheme whose source map `s` is finite. The `r`-th stratum of the Fitting
stratification of `s_* 𝒪_R` is a locally closed subscheme of the object scheme, realized as an
open subscheme `W` of the closed subscheme cut out by the `(r-1)`st Fitting ideal sheaf. This
file proves that the base change of `s` to `W` is finite locally free of rank `r`, which is the
rank assertion of [Stacks Project, Tag 0AB9].

## Main results

* `Stacks.Groupoids.finiteStratification_rank`: the rank assertion of Stacks Tag 0AB9, in the
  morphism-level vocabulary `Stacks.Morphisms.IsFiniteLocallyFreeOfRank` of Stacks Tag 02KA.

## Implementation notes

The affine-local, module-theoretic half of this statement is
`Stacks.Groupoids.module_isFiniteLocallyFreeOfRank_finiteStratification_stratum`: on every
affine open `V'` of the stratum lying over an affine open `V` of the object scheme, the sections
of the pushforward of the structure sheaf along the base change form a finite locally free
module of rank `r`. Those pairs `(V, V')` cover the stratum by
`Stacks.Morphisms.exists_affineOpens_le_preimage`.

Three further ingredients turn that into the morphism-level statement, which unfolds to the
sheaf-level predicate `AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank` on the
Zariski site.

* Quasi-coherence of the pushforward: the base change of a finite morphism is finite, hence
  affine, so `Stacks.Modules.isQuasicoherent_pushforwardStructureSheaf` applies. This is what
  the implementation notes of
  `StacksFrontier.AlgebraicGeometry.Morphisms.FiniteStratificationRank` recorded as missing.
* The passage from the sections over an affine open to the sheaf: Stacks Tag 05JM in the form
  `Stacks.Modules.isFiniteLocallyFreeOfRank_of_module_affineOpens`.
* The comparison of the two sheaf-level spellings of local freeness:
  `Stacks.Modules.isFiniteLocallyFreeOfRank_iff_localGenerators`, which is Stacks Tag 01C6.

The universe arguments `.{u, u, u}` on the sheaf-level predicate and on the comparison are
load-bearing: `AlgebraicGeometry.Scheme.Modules` is a non-reducible `def` for
`SheafOfModules.{u} X.ringCatSheaf`, so elaboration cannot read the universe parameters off a
module on a scheme and silently defaults them to `0`.

## References

* [Stacks Project, Tag 0AB9](https://stacks.math.columbia.edu/tag/0AB9)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
* [Stacks Project, Tag 02KA](https://stacks.math.columbia.edu/tag/02KA)
* [Stacks Project, Tag 05JM](https://stacks.math.columbia.edu/tag/05JM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.Groupoids

open Stacks.Fitting Stacks.Modules Stacks.Morphisms

/-- **Stacks Project, Tag 0AB9: the rank of each stratum.** For a groupoid scheme with finite
source and target there is an open subscheme `W` of the closed subscheme cut out by the
`(r-1)`st Fitting ideal sheaf of `s_* 𝒪_R` whose image in the object scheme is the difference of
the supports of the `(r-1)`st and `r`th Fitting ideal sheaves, and the base change of source to
`W` is finite locally free of rank `r`.

The open subscheme is `Stacks.Groupoids.exists_opens_finiteStratification_stratum`. Finite local
freeness is checked affine-locally by
`Stacks.Groupoids.module_isFiniteLocallyFreeOfRank_finiteStratification_stratum` and assembled
into the sheaf-level statement by
`Stacks.Modules.isFiniteLocallyFreeOfRank_of_module_affineOpens` and
`Stacks.Modules.isFiniteLocallyFreeOfRank_iff_localGenerators`. -/
@[stacks 0AB9 "rank of each stratum"]
theorem finiteStratification_rank {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsFinite G.source.left] [IsFinite G.target.left] (r : ℕ) (hr : 0 < r) :
    ∃ W : (finiteStratification G (r - 1)).subscheme.Opens,
      Set.range (W.ι ≫ (finiteStratification G (r - 1)).subschemeι) =
          ((finiteStratification G (r - 1)).support : Set G.objects.left) \
            ((finiteStratification G r).support : Set G.objects.left) ∧
        IsFiniteLocallyFreeOfRank
          (pullback.snd G.source.left
            (W.ι ≫ (finiteStratification G (r - 1)).subschemeι)) r := by
  obtain ⟨W, hW⟩ := exists_opens_finiteStratification_stratum G r
  refine ⟨W, hW, ?_⟩
  have hq : IsFinite (pullback.snd G.source.left
      (W.ι ≫ (finiteStratification G (r - 1)).subschemeι)) :=
    MorphismProperty.of_isPullback (P := @IsFinite) (.of_hasPullback _ _) ‹IsFinite G.source.left›
  have hmod : ∀ z : W.toScheme, ∃ V' : W.toScheme.affineOpens, z ∈ V'.1 ∧
      Module.IsFiniteLocallyFreeOfRank Γ(W.toScheme, V'.1)
        Γ(pushforwardStructureSheaf (pullback.snd G.source.left
          (W.ι ≫ (finiteStratification G (r - 1)).subschemeι)), V'.1) r := by
    intro z
    obtain ⟨V, V', hV', hzV'⟩ := exists_affineOpens_le_preimage
      (W.ι ≫ (finiteStratification G (r - 1)).subschemeι) z
    exact ⟨V', hzV',
      module_isFiniteLocallyFreeOfRank_finiteStratification_stratum G r hr W hW V V' hV'⟩
  exact (isFiniteLocallyFreeOfRank_iff _ r).mpr ⟨inferInstance,
    (isFiniteLocallyFreeOfRank_iff_localGenerators.{u} _ r).mp
      (isFiniteLocallyFreeOfRank_of_module_affineOpens _ r hmod)⟩

end Stacks.Groupoids

end
