module

public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.IsomorphismApproximation
public import StacksCore.Tactic.StacksAttribute

/-!
# The truncated local rings of an elementary étale neighbourhood

Let `(V, v)` be an elementary étale neighbourhood of a point `s` of a locally Noetherian scheme
`S`. This file proves that the map of local rings `𝒪_{S, s} → 𝒪_{V, v}` becomes an isomorphism
after dividing by the `N`-th power of the maximal ideal on each side, for every `N`, and records
the same isomorphism with the completed local ring `𝒪^∧_{S, s}` in place of `𝒪_{S, s}`.

This is the equality of rings
```
𝒪_{V, v}/𝔪_v ^ N = 𝒪_{S, s}/𝔪_s ^ N
```
that clause (5) of Stacks Tag 0CAW cites by name — "the equality comes from the fact that `Y_σ`
and `Y ×_{T, τ} V` are canonically isomorphic over `𝒪_{V, v}/𝔪_v ^ N = 𝒪_{S, s}/𝔪_s ^ N` by
parts (2) and (3)" — namely the part of it for which clause (2), elementariness, is responsible.

## Main results

* `AlgebraicGeometry.EtaleNeighborhood.bijective_residueField_map_stalkHom`: an elementary étale
  neighbourhood induces a bijection of residue fields.
* `AlgebraicGeometry.EtaleNeighborhood.isEtaleLocalHom_stalkHom`: the map of local rings of an
  étale neighbourhood is an étale local homomorphism.
* `AlgebraicGeometry.EtaleNeighborhood.bijective_completionMap`: an elementary étale
  neighbourhood does not change the completed local ring — the canonical map
  `𝒪^∧_{S, s} → 𝒪^∧_{V, v}` is bijective. This is Tag 0AGX in the form in which the canonical
  map itself, and not merely some isomorphism of the two completions, is inverted.
* `AlgebraicGeometry.EtaleNeighborhood.truncationEquiv` and
  `AlgebraicGeometry.EtaleNeighborhood.truncationEquiv_mk`: the isomorphism
  `𝒪_{S, s}/𝔪_s ^ N ≅ 𝒪_{V, v}/𝔪_v ^ N`, together with the statement that it is the map induced
  by `𝒪_{S, s} → 𝒪_{V, v}`, which is what pins it down.
* `AlgebraicGeometry.EtaleNeighborhood.completedTruncationEquiv` and
  `AlgebraicGeometry.EtaleNeighborhood.completedTruncationEquiv_mk`: the same isomorphism read
  out of `𝒪^∧_{S, s}/𝔪̂_s ^ N`, which is the side on which the map `σ` of Tag 0CAW lands.

## Implementation notes

*Why this is not Tag 0H1D.* Tag 0H1D gives the bijectivity of `R/I ^ n → S/J ^ n` for a formally
étale ring map, which would give `truncationEquiv` directly; but its hypothesis is
`RingHom.FormallyEtale`, whereas what an étale morphism of schemes gives at a point is
`RingHom.IsEtaleLocalHom` — flat, formally unramified and essentially of finite type. Those do
not immediately yield formal étaleness, essentially of finite type not being finitely presented.
The route taken instead goes through the completions, where the implication is proved as Tag 039H
part (2) together with Tag 0C4G: `RingHom.bijective_adicCompletionMap_of_isEtaleLocalHom` makes
the canonical map of completions bijective, and `completionQuotientEquiv` identifies `𝒪^∧/𝔪̂ ^ N`
with `𝒪/𝔪 ^ N` on each side. The bijection of completions carries `𝔪̂_s` onto `𝔪̂_v`, being a ring
isomorphism of local rings, hence carries `𝔪̂_s ^ N` onto `𝔪̂_v ^ N`, which is what lets
`Ideal.quotientEquiv` descend it. That last step is
`StacksDraft.ArtinApproximation.map_maximalIdeal_eq_ringEquiv`, not a new lemma.

*Why the `_mk` lemmas are part of the statement.* An abstract isomorphism of the two truncations
carries no information: the content is that it is the map induced by `𝒪_{S, s} → 𝒪_{V, v}`, and
without that nothing can be transported along it. The two `_mk` lemmas are therefore stated
alongside the two definitions and are what consumers use.

*Which Noetherian hypotheses appear where.* `IsLocallyNoetherian S` makes `𝒪_{S, s}` Noetherian
by instance resolution, but nothing makes `𝒪_{V, v}` Noetherian by instance resolution: that
needs `IsLocallyNoetherian V`, which follows from `LocallyOfFiniteType V.toBase` and is
introduced by hand wherever it is wanted. The statements below are arranged so that only the two
auxiliary declarations whose *types* mention the maximal ideal of `𝒪^∧_{V, v}` carry it as a
hypothesis; `truncationEquiv` and `completedTruncationEquiv` do not, their types mentioning only
maximal ideals of local rings.

*What this does not do.* It is the base half of the identification clause (5) of Tag 0CAW cites.
The other half — the identification
`𝒪_{Y_σ, y_σ}/𝔪_{y_σ} ^ N = 𝒪_{Y ×_{T, τ} V, (y, v)}/𝔪_{(y, v)} ^ N` of the local rings of the
two base changes of `Y` — is *not* proved here. It is proved, for two base changes along the
spectra of two local rings whose `N`-th truncations are identified over the base, by
`StacksDraft.ArtinApproximation.exists_truncationEquiv_stalk_pullback_fromSpecStalk`, which takes
the identification of the truncated bases — namely
`AlgebraicGeometry.EtaleNeighborhood.completedTruncationEquiv` together with clause (3) — as its
hypothesis. The replacement of `V` by `Spec 𝒪_{V, v}` which lets that statement be read at
`Y ×_{T, τ} V` is
`StacksDraft.ArtinApproximation.exists_point_ringEquiv_stalk_pullback_fromSpecStalk_comp`, and
the two halves assembled at Tag 0CAW's own data are
`StacksDraft.ArtinApproximation.exists_truncationEquiv_stalk_relativeBaseChange`.

## References

* [Stacks Project, Tag 0CAW](https://stacks.math.columbia.edu/tag/0CAW)
* [Stacks Project, Tag 0AGX](https://stacks.math.columbia.edu/tag/0AGX)
* [Stacks Project, Tag 039H](https://stacks.math.columbia.edu/tag/039H)
* [Stacks Project, Tag 02LE](https://stacks.math.columbia.edu/tag/02LE)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry IsLocalRing AdicCompletion

universe u

namespace AlgebraicGeometry.EtaleNeighborhood

variable {S : Scheme.{u}} {s : S}

/-- **An elementary étale neighbourhood induces a bijection of residue fields.** This is
`AlgebraicGeometry.EtaleNeighborhood.IsElementary` read on the map of local rings rather than on
the residue field map of the structure morphism. -/
theorem bijective_residueField_map_stalkHom (U : EtaleNeighborhood S s) (hU : U.IsElementary) :
    Function.Bijective (ResidueField.map U.stalkHom) :=
  (StacksDraft.ArtinApproximation.bijective_residueField_map_stalkHomAt_iff
    U.toBase U.point U.map_point).mpr ((isElementary_iff U).mp hU)

/-- **The map of local rings of an étale neighbourhood is an étale local homomorphism.** The
structure morphism is étale, hence étale at the distinguished point, and that is exactly this
condition on the induced map of local rings. -/
theorem isEtaleLocalHom_stalkHom [IsLocallyNoetherian S] (U : EtaleNeighborhood S s)
    [IsNoetherianRing (U.scheme.presheaf.stalk U.point)] :
    RingHom.IsEtaleLocalHom U.stalkHom :=
  StacksDraft.ArtinApproximation.isEtaleLocalHom_stalkCongr_comp U.toBase U.point U.map_point
    ((etale_iff_forall_isEtaleAt U.toBase).mp inferInstance U.point)

/-- **An elementary étale neighbourhood does not change the completed local ring**: the canonical
map `𝒪^∧_{S, s} → 𝒪^∧_{V, v}` is bijective.

This is the content of Tag 0AGX for an étale neighbourhood, in the form in which the canonical
map itself is inverted — `StacksDraft.exists_adicCompletion_ringEquiv_of_flat` produces some
isomorphism of the two completions, which carries no information about the canonical map, and
every consumer needs the canonical map. -/
@[sga "3 XI 1.4" "(ii)"]
theorem bijective_completionMap [IsLocallyNoetherian S] (U : EtaleNeighborhood S s)
    (hU : U.IsElementary) : Function.Bijective U.completionMap := by
  let : IsLocallyNoetherian U.scheme := LocallyOfFiniteType.isLocallyNoetherian U.toBase
  rw [EtaleNeighborhood.completionMap, Scheme.Hom.completionMapAt]
  exact RingHom.bijective_adicCompletionMap_of_isEtaleLocalHom U.stalkHom
    (isEtaleLocalHom_stalkHom U) (bijective_residueField_map_stalkHom U hU)

/-- The isomorphism of completed local rings attached to an elementary étale neighbourhood: the
canonical map `𝒪^∧_{S, s} → 𝒪^∧_{V, v}`, which
`AlgebraicGeometry.EtaleNeighborhood.bijective_completionMap` shows to be bijective, packaged as
a `RingEquiv`. -/
def completionRingEquiv [IsLocallyNoetherian S] (U : EtaleNeighborhood S s)
    (hU : U.IsElementary) :
    AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s) ≃+*
      AdicCompletion (maximalIdeal (U.scheme.presheaf.stalk U.point))
        (U.scheme.presheaf.stalk U.point) :=
  RingEquiv.ofBijective U.completionMap (bijective_completionMap U hU)

/-- `AlgebraicGeometry.EtaleNeighborhood.completionRingEquiv` is the canonical map of completed
local rings. -/
theorem completionRingEquiv_apply [IsLocallyNoetherian S] (U : EtaleNeighborhood S s)
    (hU : U.IsElementary)
    (z : AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) :
    completionRingEquiv U hU z = U.completionMap z := rfl

/-- The isomorphism of completed local rings of an elementary étale neighbourhood carries the
`N`-th power of the maximal ideal onto the `N`-th power of the maximal ideal. This is what lets
it descend to the truncations. -/
theorem map_maximalIdeal_pow_completionRingEquiv [IsLocallyNoetherian S]
    (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    [IsNoetherianRing (U.scheme.presheaf.stalk U.point)] (N : ℕ) :
    maximalIdeal (AdicCompletion (maximalIdeal (U.scheme.presheaf.stalk U.point))
        (U.scheme.presheaf.stalk U.point)) ^ N =
      (maximalIdeal (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
          (S.presheaf.stalk s)) ^ N).map
        ((completionRingEquiv U hU :
          AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s) →+*
            AdicCompletion (maximalIdeal (U.scheme.presheaf.stalk U.point))
              (U.scheme.presheaf.stalk U.point))) := by
  rw [Ideal.map_pow]
  congr 1
  exact (StacksDraft.ArtinApproximation.map_maximalIdeal_eq_ringEquiv
    (completionRingEquiv U hU)).symm

/-- **The truncated local rings of an elementary étale neighbourhood agree**:
`𝒪_{S, s}/𝔪_s ^ N ≅ 𝒪_{V, v}/𝔪_v ^ N`.

This is the equality of rings `𝒪_{V, v}/𝔪_v ^ N = 𝒪_{S, s}/𝔪_s ^ N` that clause (5) of Stacks
Tag 0CAW cites, attributing it to clause (2), elementariness. It is pinned down by
`AlgebraicGeometry.EtaleNeighborhood.truncationEquiv_mk`, which says that it is the map induced
by the map of local rings `𝒪_{S, s} → 𝒪_{V, v}`. -/
def truncationEquiv [IsLocallyNoetherian S] (U : EtaleNeighborhood S s) (hU : U.IsElementary)
    (N : ℕ) :
    (S.presheaf.stalk s ⧸ maximalIdeal (S.presheaf.stalk s) ^ N) ≃+*
      (U.scheme.presheaf.stalk U.point ⧸
        maximalIdeal (U.scheme.presheaf.stalk U.point) ^ N) :=
  letI : IsLocallyNoetherian U.scheme := LocallyOfFiniteType.isLocallyNoetherian U.toBase
  (completionQuotientEquiv (S.presheaf.stalk s) N).symm.trans
    ((Ideal.quotientEquiv _ _ (completionRingEquiv U hU)
        (map_maximalIdeal_pow_completionRingEquiv U hU N)).trans
      (completionQuotientEquiv (U.scheme.presheaf.stalk U.point) N))

/-- **The isomorphism of truncated local rings of an elementary étale neighbourhood is the one
induced by the map of local rings.** This is what makes
`AlgebraicGeometry.EtaleNeighborhood.truncationEquiv` usable: an abstract isomorphism of the two
truncations would say nothing. -/
theorem truncationEquiv_mk [IsLocallyNoetherian S] (U : EtaleNeighborhood S s)
    (hU : U.IsElementary) (N : ℕ) (a : S.presheaf.stalk s) :
    truncationEquiv U hU N (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (U.stalkHom a) := by
  let : IsLocallyNoetherian U.scheme := LocallyOfFiniteType.isLocallyNoetherian U.toBase
  have hsymm : (completionQuotientEquiv (S.presheaf.stalk s) N).symm
        (Ideal.Quotient.mk _ a) =
      Ideal.Quotient.mk _ (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) a) := by
    rw [RingEquiv.symm_apply_eq, completionQuotientEquiv_mk]
  have hmap : U.completionMap (algebraMap (S.presheaf.stalk s)
        (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) a) =
      algebraMap (U.scheme.presheaf.stalk U.point)
        (AdicCompletion (maximalIdeal (U.scheme.presheaf.stalk U.point))
          (U.scheme.presheaf.stalk U.point)) (U.stalkHom a) := by
    rw [EtaleNeighborhood.completionMap, Scheme.Hom.completionMapAt]
    exact RingHom.congr_fun (adicCompletionMap_comp_algebraMap U.stalkHom
      (maximalIdeal (S.presheaf.stalk s))
      (maximalIdeal (U.scheme.presheaf.stalk U.point)) (map_maximalIdeal_le _)) a
  simp only [truncationEquiv, RingEquiv.trans_apply]
  rw [hsymm, Ideal.quotientEquiv_mk, completionRingEquiv_apply, hmap,
    completionQuotientEquiv_mk]

/-- **The truncation of the completed local ring of the base agrees with the truncation of the
local ring of an elementary étale neighbourhood**:
`𝒪^∧_{S, s}/𝔪̂_s ^ N ≅ 𝒪_{V, v}/𝔪_v ^ N`.

This is the side of the identification of clause (5) of Stacks Tag 0CAW on which the map `σ` of
that lemma lands: `σ` goes into `𝒪^∧_{S, s}`, and clause (3) compares it with `τ^♯_v` after both
have been read in these truncations. -/
def completedTruncationEquiv [IsLocallyNoetherian S] (U : EtaleNeighborhood S s)
    (hU : U.IsElementary) (N : ℕ) :
    (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s) ⧸
        maximalIdeal (AdicCompletion (maximalIdeal (S.presheaf.stalk s))
          (S.presheaf.stalk s)) ^ N) ≃+*
      (U.scheme.presheaf.stalk U.point ⧸
        maximalIdeal (U.scheme.presheaf.stalk U.point) ^ N) :=
  (completionQuotientEquiv (S.presheaf.stalk s) N).trans (truncationEquiv U hU N)

/-- The isomorphism `𝒪^∧_{S, s}/𝔪̂_s ^ N ≅ 𝒪_{V, v}/𝔪_v ^ N` is, on the image of `𝒪_{S, s}`, the
map induced by the map of local rings `𝒪_{S, s} → 𝒪_{V, v}`. -/
theorem completedTruncationEquiv_mk [IsLocallyNoetherian S] (U : EtaleNeighborhood S s)
    (hU : U.IsElementary) (N : ℕ) (a : S.presheaf.stalk s) :
    completedTruncationEquiv U hU N (Ideal.Quotient.mk _
        (algebraMap (S.presheaf.stalk s)
          (AdicCompletion (maximalIdeal (S.presheaf.stalk s)) (S.presheaf.stalk s)) a)) =
      Ideal.Quotient.mk _ (U.stalkHom a) := by
  simp only [completedTruncationEquiv, RingEquiv.trans_apply]
  rw [completionQuotientEquiv_mk, truncationEquiv_mk]

end AlgebraicGeometry.EtaleNeighborhood

end
