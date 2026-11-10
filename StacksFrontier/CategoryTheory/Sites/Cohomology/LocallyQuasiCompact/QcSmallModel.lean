module

public import Mathlib.CategoryTheory.Sites.DenseSubsite.InducedTopology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.QcSite
public import StacksFrontier.CategoryTheory.Sites.Hypercovering.Map
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.SliceEquivalence
public import StacksFrontier.CategoryTheory.Sites.MorphismOfSites.SmallModel
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringBySimplicialObject
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationDescent
public import StacksFrontier.CategoryTheory.Sites.Simplicial.HypercoveringSituationDescentAb
import StacksCore.Tactic.StacksAttribute

/-!
# A small model of the big quasi-compact site

The underlying category of `LC_qc`, the site of Stacks 09X2, is
`Stacks.Topology.LocallyQuasiCompactQcSite.category`, a full subcategory of the category `LC` of
Hausdorff, locally quasi-compact spaces. Its objects live in `Type (u + 1)` while its morphisms
live in `Type u`, so it is a `Category.{u, u + 1}` and *not* a `CategoryTheory.SmallCategory`.
Nothing about this is a proper-class phenomenon: the bounded subcategory has only a set of
objects up to isomorphism, by
`Stacks.Topology.essentiallySmall_LCSizeCutoff`. The obstruction is the universe *level* of the
type of objects, nothing more.

That level matters, because the simplicial-site apparatus of Stacks 09WE is built out of
`CategoryTheory.Cat.{u, u}`: a `CategoryTheory.SimplicialSiteSituation.{u}` is a simplicial
diagram of categories whose objects *and* morphisms are in `Type u`. So
`CategoryTheory.SimplicialSemiRepresentable.totalSituation` and everything downstream of it ---
the augmentation morphism of topoi and the four clauses of Stacks 0DA8 --- are stated for a
`SmallCategory`, and cannot be applied to `LC_qc` as it stands.

This file closes that gap by replacing `LC_qc` by a genuinely small model and transporting the
site structure to it. The pieces are assembled from existing machinery rather than built:

* the model is `CategoryTheory.SmallModel` of the underlying category, which is available because
  the category is essentially small at `u`, and the comparison is Mathlib's
  `CategoryTheory.equivSmallModel`;
* the topology is transported by `CategoryTheory.Functor.inducedTopology` along the comparison,
  which is the standard idiom for carrying a topology along an equivalence and is already used
  in this tree as `smallModelTopology'`;
* a *pretopology* generating it is `CategoryTheory.GrothendieckTopology.toPretopology`, which is
  a section of `CategoryTheory.Pretopology.toGrothendieck` by
  `CategoryTheory.Pretopology.gi`. No transport of a pretopology along an equivalence is needed,
  and none is defined here: the apparatus consumes a pretopology only through the topology it
  generates, so the maximal pretopology generating the transported topology serves;
* the identification of the two topoi is Mathlib's
  `CategoryTheory.Equivalence.sheafCongr`.

What is proved here is that the result deserves to be called the quasi-compact site:
`mem_smallPretopology_iff_isQcCovering` says a presieve of the small model is covering exactly
when its image in `LC_qc` is refined by a quasi-compact covering family, and
`map_mem_smallPretopology_iff` says the covering sieves correspond under the comparison.

## Main definitions

* `Stacks.Topology.LocallyQuasiCompactQcSite.smallSite`: a small model of the underlying
  category of `LC_qc`.
* `Stacks.Topology.LocallyQuasiCompactQcSite.smallTopology` and `.smallPretopology`: the
  quasi-compact topology and a pretopology generating it, on the small model.
* `Stacks.Topology.LocallyQuasiCompactQcSite.smallSheafEquiv`: sheaves on `LC_qc` and on its
  small model are the same.
* `Stacks.Topology.LocallyQuasiCompactQcSite.smallAugmentation`: a hypercovering augmentation
  of `LC_qc`, read as an augmentation in the small model.

## Main results

* `Stacks.Topology.LocallyQuasiCompactQcSite.mem_smallPretopology_iff_isQcCovering`: the
  coverings of the small model are exactly the quasi-compact coverings, read through the
  comparison.
* `Stacks.Topology.LocallyQuasiCompactQcSite.map_mem_smallPretopology_iff`: a family of `LC_qc`
  generates a covering sieve exactly when its image in the small model is covering.
* `Stacks.Topology.LocallyQuasiCompactQcSite.isHypercovering_map_smallSite`: **Stacks 0DAZ** for
  the comparison --- a hypercovering of `LC_qc` is a hypercovering of the small model.
* `Stacks.Topology.LocallyQuasiCompactQcSite.mem_essImage_iff_isCartesianSheaf_qcAugmentation`
  and `.mem_essImage_iff_isCartesianAbSheaf_qcAugmentation`: **Stacks 0D8K** for a hypercovering
  augmentation *of `LC_qc`*, which is the statement the reconciliation buys.
* `Stacks.Topology.LocallyQuasiCompactQcSite.associatedSimplicialObject_smallAugmentation`: the
  simplicial semi-representable object of the augmentation formed in the small model is the one
  carried there from `LC_qc`.
* `Stacks.Topology.LocallyQuasiCompactQcSite.isHypercoveringAugmentation_smallAugmentation`: a
  hypercovering augmentation of `LC_qc` is one of the small model.
* `Stacks.Topology.LocallyQuasiCompactQcSite.fullyFaithfulInverseImage_smallAugmentation`:
  **Stacks 0DA8 (1)** for a hypercovering augmentation of `LC_qc`.
* `Stacks.Topology.LocallyQuasiCompactQcSite.smallOverSheafEquiv`: the *localizations* of
  `LC_qc` and of its small model have the same topos.

## Implementation notes

`Stacks.Topology.essentiallySmall_LCSizeCutoff` is a global instance on the size cutoff rather
than a use of the `category_essentiallySmall` field of
`Stacks.Topology.BoundedLCSubcategory`, because `CategoryTheory.SmallModel` needs the smallness
instance in the *type* of every declaration below, where a `haveI` cannot reach. The cutoff
lemma holds for every cardinal, so no hypothesis is lost.

The augmentation predicate
`Stacks.CategoryTheory.Hypercovering.IsHypercoveringAugmentation` is stated for an arbitrary
category and so already applies to `LC_qc` itself; it is the total site and the morphism of
topoi that need the small model. Nor is the augmentation itself transported: what the apparatus
consumes is an `Stacks.CategoryTheory.Hypercovering.IsHypercovering` of a simplicial
semi-representable object, and
`Stacks.CategoryTheory.Hypercovering.IsHypercovering.map` already carries one along any functor
taking coverings to coverings and preserving fibre products. So the bridge is the covering
clause of Stacks 00WV for the comparison, which is `mapsCoveringsToCoverings_smallEquivalence`.

That identification is `associatedSimplicialObject_smallAugmentation`, and it holds by `rfl`.
It was the next prerequisite for Stacks 0DAF, and the reason it is needed is that the 0D8K
statements above are about the *image* of a hypercovering of `LC_qc`, whereas the apparatus of
Stacks 09X8 consumes an augmentation given on the small model and forms the simplicial
semi-representable object itself. With the two identified,
`CategoryTheory.SimplicialSemiRepresentable.totalSituation` and the augmentation morphism of
topoi are available for a hypercovering augmentation of `LC_qc`, which is
`fullyFaithfulInverseImage_smallAugmentation`.

The comparison of the *localized* sites is here too, as `smallOverSheafEquiv`:
`smallSheafEquiv` identifies the two base topoi, and this identifies `Sh(LC_qc/Y)` with the
sheaves on `smallOverTopology Y`. That is what lets the inverse image along the comparison
morphism of topoi of Stacks 09X3 — the bottom horizontal arrow `(h_{-1})^{-1}` of the diagram
of Stacks 0DAF, which lands in `Sh(LC_qc/Y)` — be read as a functor into the sheaves on the
small model's localization, where the total site of Stacks 09WE lives.

What is still *not* here is the remaining horizontal arrow of Stacks 0DAF, the morphism `h`
itself: it is formed in the source as a morphism of simplicial sites in case (A) of
Situation 09WE, and `CategoryTheory.SimplicialSite` demands a strict functor
`SimplexCategory ⥤ Cat` while base change `CategoryTheory.Over.pullback` is only
pseudo-functorial.

## References

* [Stacks Project, Tag 09X2](https://stacks.math.columbia.edu/tag/09X2)
* [Stacks Project, Tag 09WE](https://stacks.math.columbia.edu/tag/09WE)
* [Stacks Project, Tag 09X8](https://stacks.math.columbia.edu/tag/09X8)
* [Stacks Project, Tag 0DA8](https://stacks.math.columbia.edu/tag/0DA8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Topology.LocallyQuasiCompactQcSite

universe u w t₁ t₂

variable {S₀ : Set LocallyQuasiCompactHausdorff.{u}} {Bound : Cardinal.{u} → Cardinal.{u}}
  (S : LocallyQuasiCompactQcSite.{u, w} S₀ Bound)

/-- A genuinely small model of the underlying category of `LC_qc`: its objects live in `Type u`,
one universe below those of `LC_qc`, while the two categories are equivalent. -/
abbrev smallSite : Type u :=
  SmallModel.{u} S.category

/-- The comparison equivalence between `LC_qc` and its small model. -/
abbrev smallEquivalence : S.category ≌ S.smallSite :=
  equivSmallModel.{u} S.category

/-- The small model has the fibre products a pretopology needs, transported from `LC_qc` along
the comparison. -/
instance hasPullbacks_smallSite : HasPullbacks S.smallSite :=
  Adjunction.hasLimitsOfShape_of_equivalence (equivSmallModel.{u} S.category).inverse

/-- The quasi-compact topology carried over to the small model, as the finest topology making
the comparison with `LC_qc` continuous. -/
abbrev smallTopology : GrothendieckTopology S.smallSite :=
  smallModelTopology'.{u} S.grothendieckTopology

/-- A pretopology on the small model generating the quasi-compact topology there: the maximal
one, whose coverings are the presieves generating a covering sieve. -/
abbrev smallPretopology : Pretopology S.smallSite :=
  S.smallTopology.toPretopology

/-- The chosen pretopology of the small model does generate its topology. This is the only
property of it the simplicial-site apparatus uses. -/
theorem toGrothendieck_smallPretopology :
    S.smallPretopology.toGrothendieck = S.smallTopology :=
  (Pretopology.gi (C := S.smallSite)).l_u_eq _

/-- Membership in the pretopology of the small model, unwound: a presieve is covering exactly
when the sieve it generates, pushed forward into `LC_qc`, is covering there. -/
theorem mem_smallPretopology_iff {Y : S.smallSite} (R : Presieve Y) :
    R ∈ S.smallPretopology Y ↔
      (Sieve.generate R).functorPushforward S.smallEquivalence.inverse ∈
        S.grothendieckTopology (S.smallEquivalence.inverse.obj Y) :=
  S.smallEquivalence.inverse.mem_inducedTopology_iff_of_isCoverDense
    (K := S.grothendieckTopology) (Sieve.generate R)

/-- **Stacks 09X2, the smallness clause.** The small model really is the quasi-compact site: a
presieve of it is covering exactly when the sieve it generates, read in `LC_qc`, is refined by a
quasi-compact covering family.

The pretopology of the small model is the maximal one generating the transported topology, so
membership in it unwinds to membership of a generated sieve in the topology generated by the
chosen set `Cov` of quasi-compact coverings, which is `isCovering_iff_isQcCovering`. -/
@[stacks 09X2 "the coverings of a small model of LC_qc are the quasi-compact coverings"]
theorem mem_smallPretopology_iff_isQcCovering {Y : S.smallSite} (R : Presieve Y) :
    R ∈ S.smallPretopology Y ↔
      ∃ E : PreZeroHypercover.{u + 1} (S.smallEquivalence.inverse.obj Y),
        S.IsQcCovering E ∧
          E.presieve₀ ≤
            ((Sieve.generate R).functorPushforward S.smallEquivalence.inverse).arrows := by
  rw [S.mem_smallPretopology_iff]
  constructor
  · rintro ⟨R', hR', hle⟩
    refine ⟨R'.preZeroHypercover, ?_, ?_⟩
    · refine (S.isCovering_iff_isQcCovering R'.preZeroHypercover).1 ?_
      change R'.preZeroHypercover.presieve₀ ∈ S.pretopology _
      rwa [Presieve.presieve₀_preZeroHypercover]
    · rwa [Presieve.presieve₀_preZeroHypercover]
  · rintro ⟨E, hE, hle⟩
    exact ⟨E.presieve₀, (S.isCovering_iff_isQcCovering E).2 hE, hle⟩

/-- The covering sieves of `LC_qc` and of its small model correspond: a presieve of `LC_qc`
generates a covering sieve exactly when its image in the small model is covering.

Pushing a sieve forward along the comparison and back is pulling it back along the unit
isomorphism, which a topology is stable under in both directions. -/
theorem map_mem_smallPretopology_iff {X : S.category} (R : Presieve X) :
    R.map S.smallEquivalence.functor ∈
        S.smallPretopology (S.smallEquivalence.functor.obj X) ↔
      Sieve.generate R ∈ S.grothendieckTopology X := by
  rw [S.mem_smallPretopology_iff, Sieve.generate_map_eq_functorPushforward]
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have h' := S.grothendieckTopology.pullback_stable
      (S.smallEquivalence.unit.app X) h
    rwa [Sieve.pullback_functorPushforward_equivalence_eq] at h'
  · rw [Sieve.functorPushforward_equivalence_eq_pullback]
    exact S.grothendieckTopology.pullback_stable _ h

/-- A quasi-compact covering family of `LC_qc` is a covering of the small model. -/
theorem map_mem_smallPretopology {X : S.category} {R : Presieve X}
    (hR : R ∈ S.pretopology X) :
    R.map S.smallEquivalence.functor ∈
      S.smallPretopology (S.smallEquivalence.functor.obj X) :=
  (S.map_mem_smallPretopology_iff R).2 ⟨R, hR, Sieve.le_generate R⟩

/-- **Stacks 09X2, the topos clause.** Sheaves on `LC_qc` and sheaves on its small model are the
same, at any coefficients. The comparison is a dense subsite inclusion for the transported
topology, so restriction along it is an equivalence. -/
@[stacks 09X2 "LC_qc and a small model of it have the same topos"]
def smallSheafEquiv (A : Type t₁) [Category.{t₂} A] :
    Sheaf S.grothendieckTopology A ≌ Sheaf S.smallTopology A :=
  (equivSmallModel.{u} S.category).sheafCongr S.grothendieckTopology S.smallTopology A

/-! ### Transporting a hypercovering of `LC_qc` to the small model -/

open Stacks.CategoryTheory.Hypercovering CategoryTheory.SimplicialSemiRepresentable

/-- **Stacks 00WV (1) for the comparison with the small model.** The comparison functor takes
quasi-compact covering families of `LC_qc` to covering families of the small model, with the
same index type and the same image family. -/
theorem mapsCoveringsToCoverings_smallEquivalence :
    MapsCoveringsToCoverings.{t₁} S.smallEquivalence.functor S.pretopology S.smallPretopology := by
  intro V ι A g hA
  have h := S.map_mem_smallPretopology hA
  rwa [Presieve.map_ofArrows] at h

/-- **Stacks 0DAZ at the comparison with the small model.** A hypercovering of an object of
`LC_qc`, carried degreewise to the small model, is a hypercovering of the image object there.

This is the transport the simplicial-hypercovering apparatus needs: that apparatus consumes a
hypercovering of a *small* site --- `isLocallyFull_totalForget_over` and
`essImage_of_isCartesianSheaf` take an `IsHypercovering` --- and `LC_qc` is not one. The
comparison functor preserves fibre products, being an equivalence, and takes coverings to
coverings by `mapsCoveringsToCoverings_smallEquivalence`, which are exactly the two hypotheses
of Stacks 0DAZ. -/
@[stacks 0DAZ "a hypercovering of LC_qc transported to a small model of it"]
theorem isHypercovering_map_smallSite {Y : S.category}
    (K : SimplicialObject (FormalCoproduct.{t₁} (Over Y)))
    (hK : IsHypercovering S.pretopology K) :
    IsHypercovering S.smallPretopology
      (K ⋙ mapFormalCoproduct.{t₁} (Over.post S.smallEquivalence.functor)) :=
  IsHypercovering.map S.pretopology S.smallPretopology S.smallEquivalence.functor
    S.mapsCoveringsToCoverings_smallEquivalence K hK

/-- A hypercovering augmentation of `LC_qc` --- the datum Stacks 09X8 starts from, which is
already meaningful for `LC_qc` because
`Stacks.CategoryTheory.Hypercovering.IsHypercoveringAugmentation` is stated for an arbitrary
category --- gives a hypercovering of the small model, where the total site and the
augmentation morphism of topoi exist. -/
theorem isHypercovering_map_smallSite_of_isHypercoveringAugmentation {Y : S.category}
    (U : SimplicialObject S.category)
    (a : U ⟶ (SimplicialObject.const S.category).obj Y)
    (h : IsHypercoveringAugmentation S.pretopology U a) :
    IsHypercovering S.smallPretopology
      (associatedSimplicialObject.{t₁} U a ⋙
        mapFormalCoproduct.{t₁} (Over.post S.smallEquivalence.functor)) :=
  S.isHypercovering_map_smallSite _ (h.isHypercovering S.pretopology U a)

/-! ### Stacks 0D8K for a hypercovering augmentation of the quasi-compact site -/

/-- The simplicial semi-representable object of the small model of `LC_qc` determined by a
hypercovering augmentation `a : U ⟶ Y` given on `LC_qc` itself: the object `n ↦ {U_n ⟶ Y}` of
Stacks 09X8, carried degreewise along the comparison. Its index universe is that of the small
model, as it must be for the total site of Stacks 0D8B to be a site in the same universe. -/
abbrev smallAssociatedSimplicialObject {Y : S.category} (U : SimplicialObject S.category)
    (a : U ⟶ (SimplicialObject.const S.category).obj Y) :
    SimplicialObject (FormalCoproduct.{u} (Over (S.smallEquivalence.functor.obj Y))) :=
  associatedSimplicialObject.{u} U a ⋙
    mapFormalCoproduct.{u} (Over.post S.smallEquivalence.functor)

/-- The localized site `LC_qc/Y` of a hypercovering augmentation, read on the small model. -/
abbrev smallOverTopology (Y : S.category) :
    GrothendieckTopology (Over (S.smallEquivalence.functor.obj Y)) :=
  S.smallPretopology.toGrothendieck.over (S.smallEquivalence.functor.obj Y)

/-- The localized site of the small model is the localization of its topology: the chosen
pretopology generates the transported topology, so localizing it at `F(Y)` and localizing the
transported topology there agree. -/
theorem smallOverTopology_eq (Y : S.category) :
    S.smallOverTopology Y = S.smallTopology.over (S.smallEquivalence.functor.obj Y) :=
  congrArg (fun T => T.over (S.smallEquivalence.functor.obj Y))
    S.toGrothendieck_smallPretopology

/-- **The localizations of `LC_qc` and of its small model have the same topos.** Sheaves on
`LC_qc/Y` and sheaves on the localized site of the small model at `F(Y)` agree, at any
coefficients.

`smallSheafEquiv` identifies the two *base* topoi; this identifies the two localizations, which
is what Stacks 0DAF's diagram needs, its bottom horizontal arrow landing in `Sh(LC_qc/Y)` while
the total site of Stacks 09WE lives over the small model. It is
`CategoryTheory.Over.postEquivSheafCongr` for the comparison equivalence, whose two
cocontinuity hypotheses hold because the comparison is a dense subsite inclusion in both
directions. -/
def smallOverSheafEquiv (Y : S.category) (A : Type t₁) [Category.{t₂} A] :
    Sheaf (S.grothendieckTopology.over Y) A ≌ Sheaf (S.smallOverTopology Y) A := by
  rw [S.smallOverTopology_eq Y]
  exact Over.postEquivSheafCongr S.smallEquivalence Y A

/-- **Stacks 0D8K (1) for a hypercovering augmentation of `LC_qc`.** Let `a : U ⟶ Y` be a
hypercovering augmentation of an object `Y` of the quasi-compact site, in the sense of
Stacks 09X8. Then on the total site of the associated simplicial semi-representable object,
carried to the small model, the sheaves of sets which are inverse images along the augmentation
are exactly the cartesian ones.

This is the statement the smallness reconciliation buys. Its hypothesis is a datum on `LC_qc`,
which is where Stacks 0DAF's diagram lives; its conclusion is about the total site of the small
model, which is where the apparatus of Stacks 09WE exists at all; and
`smallSheafEquiv` identifies the base topos of the two. -/
@[stacks 0D8K "part (1) for a hypercovering augmentation of the quasi-compact site LC_qc"]
theorem mem_essImage_iff_isCartesianSheaf_qcAugmentation {Y : S.category}
    (U : SimplicialObject S.category)
    (a : U ⟶ (SimplicialObject.const S.category).obj Y)
    (h : IsHypercoveringAugmentation S.pretopology U a)
    (E : Sheaf (situation (S.smallOverTopology Y)
      (S.smallAssociatedSimplicialObject U a)).totalTopology (Type u)) :
    (totalLocalizationMorphism (S.smallOverTopology Y)
        (S.smallAssociatedSimplicialObject U a)).inverseImage.essImage E ↔
      (situation (S.smallOverTopology Y)
        (S.smallAssociatedSimplicialObject U a)).IsCartesianSheaf E :=
  mem_essImage_inverseImage_iff_isCartesianSheaf_over S.smallPretopology
    (S.smallAssociatedSimplicialObject U a)
    (S.isHypercovering_map_smallSite_of_isHypercoveringAugmentation U a h) E

/-- **Stacks 0D8K (2) for a hypercovering augmentation of `LC_qc`.** The same for sheaves of
abelian groups: on the total site of the associated simplicial semi-representable object carried
to the small model, the abelian sheaves which are inverse images along the augmentation are
exactly the cartesian ones. -/
@[stacks 0D8K "part (2) for a hypercovering augmentation of the quasi-compact site LC_qc"]
theorem mem_essImage_iff_isCartesianAbSheaf_qcAugmentation {Y : S.category}
    (U : SimplicialObject S.category)
    (a : U ⟶ (SimplicialObject.const S.category).obj Y)
    (h : IsHypercoveringAugmentation S.pretopology U a)
    (G : Sheaf (situation (S.smallOverTopology Y)
      (S.smallAssociatedSimplicialObject U a)).totalTopology Ab.{u}) :
    ((totalForget (S.smallAssociatedSimplicialObject U a)).sheafPushforwardContinuous Ab.{u}
        ((situation (S.smallOverTopology Y)
          (S.smallAssociatedSimplicialObject U a)).totalTopology)
        (S.smallOverTopology Y)).essImage G ↔
      (situation (S.smallOverTopology Y)
        (S.smallAssociatedSimplicialObject U a)).IsCartesianAbSheaf G :=
  mem_essImage_abelianInverseImage_iff_isCartesianAbSheaf_over S.smallPretopology
    (S.smallAssociatedSimplicialObject U a)
    (S.isHypercovering_map_smallSite_of_isHypercoveringAugmentation U a h) G

/-! ### The augmentation formed in the small model

The statements above are about the *image* of a hypercovering augmentation of `LC_qc`: the
simplicial semi-representable object `smallAssociatedSimplicialObject` is built by carrying
`associatedSimplicialObject` degreewise along the comparison. The apparatus of Stacks 09X8,
by contrast, consumes an augmentation given on the small model to begin with, and forms the
simplicial semi-representable object itself. This section identifies the two, which is what
lets `CategoryTheory.SimplicialSemiRepresentable.totalSituation` and everything downstream of
it be applied to a hypercovering augmentation of `LC_qc`. -/

/-- A hypercovering augmentation of `LC_qc`, read as an augmentation *in the small model*: the
simplicial object is carried along the comparison and the augmentation is its image, the
constant simplicial object being carried to the constant simplicial object on the image.

The components are literally `F(a_n)` rather than `F(a_n)` composed with the identification of
`F ∘ const Y` with `const F(Y)`, so that `Over.lift` of this augmentation is *equal*, and not
merely isomorphic, to `Over.lift` of the original followed by `Over.post`; that equality is
`associatedSimplicialObject_smallAugmentation`. -/
def smallAugmentation {Y : S.category} (U : SimplicialObject S.category)
    (a : U ⟶ (SimplicialObject.const S.category).obj Y) :
    (U ⋙ S.smallEquivalence.functor) ⟶
      (SimplicialObject.const S.smallSite).obj (S.smallEquivalence.functor.obj Y) where
  app j := S.smallEquivalence.functor.map (a.app j)
  naturality j k φ := by
    have h : U.map φ ≫ a.app k = a.app j := by simp
    change S.smallEquivalence.functor.map (U.map φ) ≫
      S.smallEquivalence.functor.map (a.app k) = _
    rw [← Functor.map_comp, h]
    exact (Category.comp_id _).symm

/-- **The identification the simplicial-site apparatus needs.** The simplicial
semi-representable object of the augmentation `smallAugmentation` formed in the small model is
the object `smallAssociatedSimplicialObject` obtained by carrying the simplicial
semi-representable object of the original augmentation degreewise along the comparison.

This holds by `rfl`: `associatedSimplicialObject` is `Over.lift` followed by
`FormalCoproduct.incl`, the comparison commutes with `FormalCoproduct.incl` because
`mapFormalCoproduct` acts componentwise, and `Over.lift` of `smallAugmentation` is `Over.lift`
of the original followed by `CategoryTheory.Over.post` by the choice of components made
there. -/
theorem associatedSimplicialObject_smallAugmentation {Y : S.category}
    (U : SimplicialObject S.category)
    (a : U ⟶ (SimplicialObject.const S.category).obj Y) :
    associatedSimplicialObject.{u} (U ⋙ S.smallEquivalence.functor)
        (S.smallAugmentation U a) =
      S.smallAssociatedSimplicialObject U a :=
  rfl

/-- A hypercovering augmentation of `LC_qc` is a hypercovering augmentation of the small model,
in the sense of Stacks 09X8 read there.

Via `associatedSimplicialObject_smallAugmentation` this is
`isHypercovering_map_smallSite_of_isHypercoveringAugmentation`, read through the
characterization of Stacks 0GM9 of the augmentation condition by the hypercovering condition
on the associated simplicial semi-representable object. -/
theorem isHypercoveringAugmentation_smallAugmentation {Y : S.category}
    (U : SimplicialObject S.category)
    (a : U ⟶ (SimplicialObject.const S.category).obj Y)
    (h : IsHypercoveringAugmentation S.pretopology U a) :
    IsHypercoveringAugmentation S.smallPretopology (U ⋙ S.smallEquivalence.functor)
      (S.smallAugmentation U a) := by
  rw [isHypercoveringAugmentation_iff_isHypercovering.{u},
    S.associatedSimplicialObject_smallAugmentation U a]
  exact S.isHypercovering_map_smallSite_of_isHypercoveringAugmentation U a h

/-- The total site of Stacks 09X8 formed from the augmentation of the small model is the
situation the two Stacks 0D8K statements above are about. Both sides are the simplicial-site
situation of the same simplicial semi-representable object over the same localized site, by
`associatedSimplicialObject_smallAugmentation`. -/
theorem totalSituation_smallAugmentation {Y : S.category}
    (U : SimplicialObject S.category)
    (a : U ⟶ (SimplicialObject.const S.category).obj Y) :
    totalSituation S.smallPretopology (U ⋙ S.smallEquivalence.functor)
        (S.smallAugmentation U a) =
      situation (S.smallOverTopology Y) (S.smallAssociatedSimplicialObject U a) :=
  rfl

/-- **Stacks 0DA8 (1) for a hypercovering augmentation of `LC_qc`.** The inverse image along
the augmentation morphism of topoi of the total site, formed in the small model from a
hypercovering augmentation given on `LC_qc`, is fully faithful.

This is what the identification buys that the `qcAugmentation` statements above cannot state:
the augmentation morphism of topoi itself, rather than only its essential image, is now
available for a datum given on `LC_qc`. -/
def fullyFaithfulInverseImage_smallAugmentation {Y : S.category}
    (U : SimplicialObject S.category)
    (a : U ⟶ (SimplicialObject.const S.category).obj Y)
    (h : IsHypercoveringAugmentation S.pretopology U a) :
    (augmentationMorphismOfTopoi S.smallPretopology (U ⋙ S.smallEquivalence.functor)
      (S.smallAugmentation U a)).inverseImage.FullyFaithful :=
  fullyFaithfulInverseImageAugmented' _ _ _
    (S.isHypercoveringAugmentation_smallAugmentation U a h)

end Stacks.Topology.LocallyQuasiCompactQcSite

end
