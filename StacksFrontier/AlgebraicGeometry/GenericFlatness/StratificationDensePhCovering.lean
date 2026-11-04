module

public import Mathlib.AlgebraicGeometry.Morphisms.Immersion
public import StacksFrontier.AlgebraicGeometry.GenericFlatness.StratificationPhCovering

/-!
# The strata of a flat stratification may be taken dense

The proofs of Stacks 0ETR and Stacks 0ETT stratify the base by generic flatness and then replace
the `k`-th closed subscheme `S_k` of the stratification by the *scheme-theoretic closure* `Y_k` of
the stratum `U_k = S_k ∖ S_{k+1}` inside it. The point of the replacement is that `U_k` is a
**dense** open of `Y_k`, whereas it is only a locally closed subset of the base; density is what
the flattening blowup of Stacks 0815 consumes, through Stacks 080Y, and what the valuative step at
the end of both proofs needs in order to see the generic point of a valuation ring inside the flat
locus.

This file carries out that replacement. `AlgebraicGeometry.Scheme.Opens.exists_denseOpens_closure`
constructs the scheme-theoretic closure of a quasi-compact open as a closed subscheme of the
ambient scheme in which that open sits as a dense open, and
`AlgebraicGeometry.HasFlatStratification.exists_isPHCovering_dense_flat_stratum` feeds it the
strata of a flat stratification over a Noetherian base, upgrading
`AlgebraicGeometry.HasFlatStratification.exists_isPHCovering_flat_stratum` with the density clause
the sources use.

## Main results

* `AlgebraicGeometry.Scheme.Opens.exists_denseOpens_closure`: a quasi-compact open `U` of a scheme
  `Z` is a dense open of a closed subscheme `Y ⊆ Z`, namely of its scheme-theoretic closure, whose
  underlying closed set is the closure of `U`.
* `AlgebraicGeometry.HasFlatStratification.exists_isPHCovering_dense_flat_stratum`: a morphism
  with a flat stratification of its Noetherian base admits a finite ph covering of that base by
  closed subschemes, each carrying a **dense** open over which the morphism base changes flat.

## Implementation notes

The scheme-theoretic closure of `U ⊆ Z` is the scheme-theoretic image of the open immersion
`U.ι : U ⟶ Z`, that is Mathlib's `AlgebraicGeometry.Scheme.Hom.image` of `U.ι`. Two Mathlib
instances do all the work once the open immersion is known to be quasi-compact: `U.ι.toImage` is
an open immersion, because a quasi-compact immersion factors as an open immersion followed by a
closed immersion onto its image, and it is dominant, because a quasi-compact morphism is dominant
onto its scheme-theoretic image. The dense open of the closure is therefore
`U.ι.toImage.opensRange`, and `AlgebraicGeometry.Scheme.Hom.isoOpensRange` identifies it with `U`.
The underlying closed set of the closure is `closure (U : Set Z)` by
`AlgebraicGeometry.Scheme.Hom.support_ker`, Stacks 01R8 part (4).

Quasi-compactness of `U.ι` is what restricts the statement about stratifications to a Noetherian
base: over such a base an open immersion is automatically quasi-compact (Stacks 01OX), and the
closed subschemes of the stratification are again locally Noetherian because a closed immersion
is locally of finite type. Over a general quasi-compact base it would instead come from the finite
type clause of `AlgebraicGeometry.HasFlatStratification` on the ideal sheaf `I (k+1)` cutting out
the removed part, which is not used here.

Flatness is transported to the dense open by a private helper, which is pure base change: the
pullback of `f` along `g' ≫ g` is the pullback along `g'` of the pullback along `g`, by Mathlib's
`AlgebraicGeometry.pullbackLeftPullbackSndIso`. The morphism `g'` it is applied with is the
composite of the identification `U ≅ U.ι.toImage.opensRange` with the open immersion of that
range, so no isomorphism-chasing is needed. The same fact is stated publicly, in the richer
company of its biconditional form, as `AlgebraicGeometry.flat_pullback_snd_comp` of
`StacksFrontier/AlgebraicGeometry/Topologies/V/PhVStratification.lean`. Neither module is in the
other's transitive import closure, so importing that one here would not be a cycle, but it
would pull in 1,889 further modules for a four-line lemma; the fact is therefore re-derived
here, and the helper is kept private so that the two spellings do not collide in the library
umbrella.

## References

* [Stacks Project, Tag 0ETR](https://stacks.math.columbia.edu/tag/0ETR)
* [Stacks Project, Tag 0ETT](https://stacks.math.columbia.edu/tag/0ETT)
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8)
* [Stacks Project, Tag 0H3Z](https://stacks.math.columbia.edu/tag/0H3Z)
* [Stacks Project, Tag 01OX](https://stacks.math.columbia.edu/tag/01OX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- **Flatness of a base change passes to a further base change.** If `X ×_S T` is flat over `T`,
then `X ×_S W` is flat over `W` for any `W ⟶ T`.

The pullback of `f` along `g' ≫ g` is the pullback along `g'` of the pullback along `g`, by
`AlgebraicGeometry.pullbackLeftPullbackSndIso`; flatness is stable under base change and an
isomorphism is flat.

Private: `AlgebraicGeometry.flat_pullback_snd_comp` of
`StacksFrontier/AlgebraicGeometry/Topologies/V/PhVStratification.lean` is this statement in public,
with the biconditional it is a corollary of, but that module is not in this one's import
closure and importing it would add 1,889 modules. -/
private theorem flat_pullback_snd_comp {X S T W : Scheme.{u}} (f : X ⟶ S) {g : T ⟶ S} (g' : W ⟶ T)
    (h : Flat (pullback.snd f g)) : Flat (pullback.snd f (g' ≫ g)) := by
  have h2 : Flat (pullback.snd (pullback.snd f g) g') :=
    MorphismProperty.of_isPullback (IsPullback.of_hasPullback (pullback.snd f g) g') h
  rw [← pullbackLeftPullbackSndIso_inv_snd_snd f g g']
  infer_instance

/-- **The scheme-theoretic closure of a quasi-compact open.** A quasi-compact open `U` of a
scheme `Z` is a dense open of a closed subscheme `Y` of `Z`, whose underlying closed set is the
closure of `U` in `Z`.

The closed subscheme is the scheme-theoretic image of the open immersion `U.ι`: that morphism is a
quasi-compact immersion, so `U.ι.toImage` is an open immersion, and it is dominant because a
quasi-compact morphism is dominant onto its scheme-theoretic image. -/
theorem Scheme.Opens.exists_denseOpens_closure {Z : Scheme.{u}} (U : Z.Opens)
    [QuasiCompact U.ι] :
    ∃ (Y : Scheme.{u}) (y : Y ⟶ Z) (V : Y.Opens) (e : U.toScheme ≅ V.toScheme),
      IsClosedImmersion y ∧ Dense (V : Set Y) ∧ Set.range y.base = closure (U : Set Z) ∧
        e.hom ≫ V.ι ≫ y = U.ι := by
  refine ⟨U.ι.image, U.ι.imageι, U.ι.toImage.opensRange, U.ι.toImage.isoOpensRange,
    inferInstance, U.ι.toImage.denseRange, ?_, ?_⟩
  · rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι, Scheme.Hom.support_ker,
      Scheme.Opens.range_ι]
  · rw [← Category.assoc, Scheme.Hom.isoOpensRange_hom_ι, Scheme.Hom.toImage_imageι]

/-- **The covering step of the proofs of Stacks 0ETR and Stacks 0ETT, with dense strata.** A
morphism `f : X ⟶ S` with a flat stratification of its Noetherian base admits a finite ph covering
`{Z k ⟶ S}` of that base by closed subschemes, together with, for each `k`, a **dense** open `U k`
of `Z k` such that `f` base changes to a flat morphism over `U k`.

This is `AlgebraicGeometry.HasFlatStratification.exists_isPHCovering_flat_stratum` with the
replacement both sources perform carried out: the `k`-th closed subscheme of the stratification is
replaced by the scheme-theoretic closure of the `k`-th stratum inside it, which is still a closed
subscheme of `S` and in which the stratum is now dense. Joint surjectivity survives the
replacement because every point of `S` already lies in the image of one of the *strata*, and
flatness survives it because the stratum is carried into the closure isomorphically. -/
theorem HasFlatStratification.exists_isPHCovering_dense_flat_stratum {X S : Scheme.{u}}
    [IsNoetherian S] {f : X ⟶ S} (h : HasFlatStratification f) :
    ∃ (K : Type) (_ : Finite K) (Z : K → Scheme.{u}) (z : ∀ k, Z k ⟶ S)
      (U : ∀ k, (Z k).Opens),
      IsPHCovering Z z ∧ (∀ k, IsClosedImmersion (z k)) ∧
        (∀ k, Flat (pullback.snd f ((U k).ι ≫ z k))) ∧
        (∀ k, Dense (U k : Set (Z k))) ∧
        ∀ s : S, ∃ (k : K) (x : Z k), x ∈ U k ∧ (z k).base x = s := by
  classical
  obtain ⟨K, hK, Z, z, U, -, hclosed, hflat, hmem⟩ := h.exists_isPHCovering_flat_stratum
  have _ : Finite K := hK
  have _ : ∀ k, IsClosedImmersion (z k) := hclosed
  -- each closed subscheme of the stratification is locally Noetherian, so its opens are
  -- quasi-compact
  have _ : ∀ k, IsLocallyNoetherian (Z k) := fun k ↦
    LocallyOfFiniteType.isLocallyNoetherian (z k)
  choose Y y V e hyclosed hVdense hyrange hefac using fun k ↦ (U k).exists_denseOpens_closure
  have _ : ∀ k, IsClosedImmersion (y k ≫ z k) := fun k ↦ have := hyclosed k; inferInstance
  have hc : ∀ k, (V k).ι ≫ y k ≫ z k = (e k).inv ≫ (U k).ι ≫ z k := fun k ↦ by
    rw [← hefac k]; simp
  -- every point of the base is hit by the dense open of one of the new members
  have key : ∀ s : S, ∃ (k : K) (p : Y k), p ∈ V k ∧ (y k ≫ z k).base p = s := by
    intro s
    obtain ⟨k, x, hx, hxs⟩ := hmem s
    obtain ⟨w, hw⟩ := (U k).range_ι.ge hx
    refine ⟨k, (V k).ι.base ((e k).hom.base w), (V k).range_ι.le ⟨_, rfl⟩, ?_⟩
    calc (y k ≫ z k).base ((V k).ι.base ((e k).hom.base w))
        = ((e k).inv ≫ (U k).ι ≫ z k).base ((e k).hom.base w) := by
          rw [← hc k]; simp only [Scheme.Hom.comp_apply]
      _ = (z k).base ((U k).ι.base w) := by simp
      _ = s := by rw [hw, hxs]
  refine ⟨K, hK, Y, fun k ↦ y k ≫ z k, V, ?_, fun k ↦ inferInstance, fun k ↦ ?_, hVdense, key⟩
  · refine isPHCovering_of_isProper_of_exists_mem_range _ _ fun s ↦ ?_
    obtain ⟨k, p, -, hps⟩ := key s
    exact ⟨k, p, hps⟩
  · rw [hc k]
    exact flat_pullback_snd_comp f (e k).inv (hflat k)

end AlgebraicGeometry

end
