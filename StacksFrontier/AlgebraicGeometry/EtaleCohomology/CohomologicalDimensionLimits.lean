module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.Limits.IndexHomUniverse

/-!
# Cohomological dimension of a limit of schemes with affine transition morphisms

[Stacks, Tag 0F0R] (Étale Cohomology, Lemma 59.95.2) says that if `X = lim X_i` is a directed
limit of a system of quasi-compact and quasi-separated schemes with affine transition
morphisms, then

`cd(X) ≤ max cd(X_i)`,

the maximum being taken over the index set. Cohomological dimension here is the cohomological
dimension of [Stacks, Tag 0F0Q]: the least `d ∈ {0, 1, 2, …} ∪ {∞}` such that the étale
cohomology `H^q_étale(X, 𝓕)` of every torsion abelian sheaf `𝓕` on `X_étale` vanishes for
`q > d`. It is `AlgebraicGeometry.Scheme.etaleCohomologicalDimension`, valued in `ℕ∞`, which
is a complete lattice; so the maximum over the index set is the supremum
`⨆ i, cd(X_i)`, and it is a genuine maximum rather than a supremum of the empty family
because a cofiltered index category is nonempty.

The proof in the source has two steps. Write `f_i : X ⟶ X_i` for the projections of the limit
and let `𝓕` be a torsion abelian sheaf on `X_étale`. [Stacks, Tag 0EYN] presents `𝓕` as the
colimit `𝓕 = colim f_i^{-1} f_{i,*}𝓕` of the inverse images of its direct images, and
[Stacks, Tag 09YQ] turns that presentation into the identification

`H^q_étale(X, 𝓕) = colim H^q_étale(X_i, f_{i,*}𝓕)`.

Every cohomology class on `X` therefore comes from a stage. A stage contributes nothing in a
degree `q` exceeding `cd(X_i)`, because the direct image `f_{i,*}𝓕` of a torsion sheaf along
the quasi-compact and quasi-separated `f_i` is again torsion — [Stacks, Tag 0DDD] part (1) in
degree zero. As `cd(X_i) ≤ ⨆ j, cd(X_j)`, a degree above the supremum is above every
`cd(X_i)`, and the lemma follows.

## Main results

* `AlgebraicGeometry.Scheme.quasiSeparatedSpace_pt_of_isLimit`: the limit of a cofiltered
  system of quasi-separated schemes with affine transition morphisms is quasi-separated.
* `AlgebraicGeometry.Scheme.etaleCohomologicalDimension_le_iSup_of_isLimit`: Tag 0F0R, over the
  colimit identification of Tags 0EYN and 09YQ as a named hypothesis.

## Implementation notes

*The directed limit.* A directed system with affine transition morphisms is a diagram
`D : I ⥤ Scheme` over a cofiltered index category — the opposite of a directed set is
cofiltered — all of whose maps `D.map a` are affine, and the limit is a cone `c` over it
together with `hc : IsLimit c`, so that `c.pt` is `X` and `c.π.app i` is the projection
`f_i`. The quasi-compactness and quasi-separatedness of the stages are the instance
hypotheses `[∀ i, CompactSpace (D.obj i)]` and `[∀ i, QuasiSeparatedSpace (D.obj i)]`, which
is what makes each `cd(X_i)` defined.

*Why `c.pt` carries the same two instances.* They are what makes `cd(X)` defined, so they
appear in the statement rather than inside the proof. They are not extra assumptions:
`AlgebraicGeometry.Scheme.compactSpace_of_isLimit'` supplies the first from `hc` and the
hypotheses on the stages, and `quasiSeparatedSpace_pt_of_isLimit` below supplies the second.

*The torsion direct image.* That the direct image of a torsion abelian sheaf along a
quasi-compact and quasi-separated morphism is torsion is [Stacks, Tag 0DDD] part (1) in degree
zero, and this library proves part (1) in every degree, as
`Stacks.EtaleCohomology.torsionSheafProperty_rightDerived_smallEtaleDirectImageAb`. The proof
below applies it to the projections `f_i` of the limit. Two reductions get it there: the
degree-zero right derived functor of the direct image is the direct image itself, the direct
image on abelian sheaves of small étale sites being a right adjoint and hence left exact
(`CategoryTheory.Functor.rightDerivedZeroIsoSelf`); and the quasi-compactness and
quasi-separatedness of `f_i` come from `hc`, a projection of a limit with affine transition
morphisms being affine (`AlgebraicGeometry.isAffineHom_π_app'`), hence quasi-compact and
separated, hence quasi-separated.

*The colimit identification.* `H^q_étale(X, 𝓕) = colim H^q_étale(X_i, f_{i,*}𝓕)` cannot yet be
assembled here, so the consequence of it that the source's proof consumes is a hypothesis
`h09YQ` of the theorem below, in exactly the form in which it is consumed: vanishing of `H^q` at
every stage forces vanishing of `H^q` on the limit. It says nothing about cohomological
dimension, and in particular it is not the conclusion of Tag 0F0R, which is an inequality of
suprema in `ℕ∞`.

Of [Stacks, Tag 0EYN] this library has the system of sheaves and the cocone, namely
`Stacks.EtaleCohomology.directImageSystem` — `(f_{i,*}𝓕, φ_{i'i})` is a system of sheaves — and
`Stacks.EtaleCohomology.coneDirectImageCounit_cocone` — the counits `f_i^{-1}f_{i,*}𝓕 ⟶ 𝓕` form
a cocone on it. The remaining content of the tag is that this cocone is a colimit,
`𝓕 = colim f_i^{-1}f_{i,*}𝓕`.

A colimit presentation in that sense *is* constructed in this library, but for the sheaf the
construction builds rather than for a given one:
`Stacks.WeakSites.ColimitSiteCohomology.systemColimitSheaf_isColimitPresentation` presents the
left Kan extension `Stacks.WeakSites.ColimitSiteCohomology.systemColimitSheaf` of the system,
the general criterion behind it being that a candidate sheaf is a presentation as soon as it is
the pointwise left Kan extension of the system. What Tag 0EYN adds is that `𝓕` together with the
counits is itself such a candidate, and that is the step this library lacks — which is why every
statement of [Stacks, Tag 09YP] and [Stacks, Tag 09YQ] here takes the presentation as a
hypothesis instead. The uniqueness companion
`Stacks.WeakSites.ColimitSiteCohomology.colimitPresentation_uniqueIso` does not supply it: it
compares two presentations, so it needs one for `𝓕` already, and its hypothesis cannot be
weakened to `Stacks.WeakSites.ColimitSiteCohomology.IsCompatible`, which the zero sheaf with the
zero family satisfies.

[Stacks, Tag 09YQ] is here for the small *affine* étale sites and the right-derived
`sheafSections` of the colimit-of-sites machinery of [Stacks, Tag 09YP], as
`Stacks.EtaleCohomology.QcqsLimitCohomology.etaleCohomologyColimit_isColimit`, over an object of
a level and with such a colimit presentation among its own hypotheses. Two further steps
separate it from the identification above. The first is the Čech / Mayer-Vietoris descent from
an object of the small affine étale site of `X_i` to the quasi-compact quasi-separated `X_i`
itself. Its covering data is available in two shapes —
`Stacks.EtaleCohomology.QcqsLimitCohomology.exists_finite_jointlySurjective_smallAffineEtale`
for the first layer as objects of the site, and
`Stacks.QcqsOneHypercover.exists_finite_affine_oneHypercover_opens` for both layers as opens —
but the descent itself is not: the library's descent theorem
`Stacks.Cohomology.isIso_colimit_post_rightDerived_sheafSections` needs
`Stacks.Cohomology.HasIntersectionsIn`, the iterated fibre products of the covering family
inside the chosen collection of objects, and a pairwise intersection of two affine opens of a
quasi-compact quasi-separated `X_i` is quasi-affine rather than affine, which is exactly what
the second layer of that one-hypercover replaces and what no variant of the descent theorem here
consumes. The second step is the passage to the mainstream étale cohomology,
where the cohomological form of [Stacks, Tag 04HR] is available —
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.affineEtaleCohomologyFunctorIso` identifies `H^p`
on the small affine étale site with `H^p` on the small étale site, and
`Stacks.EtaleCohomology.BaseChangeAlgebraSystem.rightDerivedSectionsFinalIsoEtaleCohomology` does
so for sections over the terminal object of an affine scheme — while the transport of cohomology
across `CategoryTheory.AsSmall.equiv` onto the universe-raised site that Tag 09YP is stated over
is not performed.

*Why a separate module.* `StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension`
defines `cd(X)` and `cd(f)` and proves that each is the least bound of its kind; it has no
dependency on limits of schemes. The statement here needs the inverse limits of
`StacksFrontier.AlgebraicGeometry.Limits.IndexHomUniverse`, the direct images along the
projections of `StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.DirectImageSystem` and
Tag 0DDD from
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.TorsionHigherDirectImage`, so it is kept beside
those modules rather than inside it.

## References

* [Stacks Project, Tag 0F0R](https://stacks.math.columbia.edu/tag/0F0R)
* [Stacks Project, Tag 0F0Q](https://stacks.math.columbia.edu/tag/0F0Q)
* [Stacks Project, Tag 0EYN](https://stacks.math.columbia.edu/tag/0EYN)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks Project, Tag 09YP](https://stacks.math.columbia.edu/tag/09YP)
* [Stacks Project, Tag 04HR](https://stacks.math.columbia.edu/tag/04HR)
* [Stacks Project, Tag 0DDD](https://stacks.math.columbia.edu/tag/0DDD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

universe u

namespace AlgebraicGeometry.Scheme

variable {I : Type u} [Category.{u} I] [IsCofiltered I] (D : I ⥤ Scheme.{u})
  [∀ {i j : I} (a : i ⟶ j), IsAffineHom (D.map a)] (c : Cone D)

section QuasiSeparated

variable [∀ i : I, QuasiSeparatedSpace (D.obj i)]

/-- The limit of a cofiltered system of quasi-separated schemes with affine transition
morphisms is quasi-separated: the projection to any stage is affine, hence separated, hence
quasi-separated, and the stage is quasi-separated. The index category is nonempty because it
is cofiltered. -/
public theorem quasiSeparatedSpace_pt_of_isLimit (hc : IsLimit c) :
    QuasiSeparatedSpace c.pt := by
  obtain ⟨i⟩ : Nonempty I := IsCofiltered.nonempty
  have : IsAffineHom (c.π.app i) := isAffineHom_π_app' D c hc i
  exact quasiSeparatedSpace_of_quasiSeparated (c.π.app i)

end QuasiSeparated

section Dimension

variable [∀ i : I, CompactSpace (D.obj i)] [∀ i : I, QuasiSeparatedSpace (D.obj i)]

/-- **Stacks Project, Tag 0F0R** (Étale Cohomology, Lemma 59.95.2). Let `X = lim X_i` be a
directed limit of a system of quasi-compact and quasi-separated schemes with affine transition
morphisms. Then `cd(X) ≤ max cd(X_i)`.

The directed system is the cofiltered diagram `D` with affine maps and quasi-compact,
quasi-separated values, the limit is the cone `c` with `hc : IsLimit c`, the projections
`f_i : X ⟶ X_i` are `c.π.app i`, and the maximum over the index set is the supremum in the
complete lattice `ℕ∞`, which is attained because a cofiltered category is nonempty.

`h09YQ` is the consequence of [Stacks, Tag 0EYN] and [Stacks, Tag 09YQ] that the proof uses:
since `𝓕 = colim f_i^{-1} f_{i,*}𝓕` and hence
`H^q_étale(X, 𝓕) = colim H^q_étale(X_i, f_{i,*}𝓕)`, a degree in which the cohomology of every
`f_{i,*}𝓕` vanishes is a degree in which the cohomology of `𝓕` vanishes.

The proof is then the source's: a degree above `⨆ i, cd(X_i)` is above every `cd(X_i)`, so each
`H^q_étale(X_i, f_{i,*}𝓕)` vanishes by the defining property of `cd(X_i)` applied to the sheaf
`f_{i,*}𝓕`, which is torsion by [Stacks, Tag 0DDD] part (1) in degree zero —
`Stacks.EtaleCohomology.torsionSheafProperty_rightDerived_smallEtaleDirectImageAb` read through
`CategoryTheory.Functor.rightDerivedZeroIsoSelf`, the projection `f_i` being affine and hence
quasi-compact and quasi-separated — and `h09YQ` transports the vanishing to `X`. -/
@[stacks 0F0R "the hypothesis `h09YQ` of this declaration is the transport of vanishing that \
Tags 0EYN and 09YQ supply: a degree in which the étale cohomology of every direct image \
`f_{i,*}𝓕` vanishes is a degree in which that of `𝓕` vanishes"]
public theorem etaleCohomologicalDimension_le_iSup_of_isLimit
    [CompactSpace c.pt] [QuasiSeparatedSpace c.pt]
    [HasSheafify c.pt.smallEtaleTopology AddCommGrpCat.{u + 1}]
    [HasExt.{u + 1} (Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1})]
    [∀ i : I, HasSheafify (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1}]
    [∀ i : I, HasExt.{u + 1} (Sheaf (D.obj i).smallEtaleTopology AddCommGrpCat.{u + 1})]
    (hc : IsLimit c)
    (h09YQ : ∀ F : Sheaf c.pt.smallEtaleTopology AddCommGrpCat.{u + 1},
      Stacks.Torsion.torsionSheafProperty c.pt.smallEtaleTopology F →
        ∀ q : ℕ, (∀ i : I, Subsingleton (Sheaf.H.{u + 1, u + 1}
            ((Stacks.EtaleCohomology.smallEtalePushforward
              (c.π.app i) AddCommGrpCat.{u + 1}).obj F) q)) →
          Subsingleton (Sheaf.H.{u + 1, u + 1} F q)) :
    etaleCohomologicalDimension c.pt ≤
      ⨆ i : I, etaleCohomologicalDimension (D.obj i) := by
  refine etaleCohomologicalDimension_le c.pt _ fun F hF q hq => h09YQ F hF q fun i => ?_
  have : IsAffineHom (c.π.app i) := isAffineHom_π_app' D c hc i
  have htorsion : Stacks.Torsion.torsionSheafProperty (D.obj i).smallEtaleTopology
      ((Stacks.EtaleCohomology.smallEtalePushforward
        (c.π.app i) AddCommGrpCat.{u + 1}).obj F) :=
    Stacks.EtaleCohomology.torsionSheafProperty_smallEtaleDirectImageAb.{u + 1, u}
      (c.π.app i) F hF
  exact isEtaleCohomologyBound_etaleCohomologicalDimension (D.obj i) _ htorsion q
    (lt_of_le_of_lt (le_iSup (fun j : I => etaleCohomologicalDimension (D.obj j)) i) hq)

end Dimension

end AlgebraicGeometry.Scheme

end
