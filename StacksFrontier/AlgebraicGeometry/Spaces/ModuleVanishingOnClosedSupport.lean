module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleVanishingAboveTheDimension
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianCohomology
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.AbelianExact
public import StacksFrontier.Topology.Sheaves.ClosedImmersion.SupportedSectionsOnClosed

/-!
# Grothendieck vanishing for a sheaf supported on a closed subset

`StacksFrontier/AlgebraicGeometry/Spaces/ModuleVanishingAboveTheDimension.lean` reads
[Stacks, Tag 02UZ] for sheaves of modules, and then — in the shape the proof of
[Stacks, Tag 02V7] consumes it — for a module *pushed forward along a closed immersion* whose
source has Noetherian underlying space of bounded dimension. The hypothesis there is the
pushforward, which is a statement about where the module comes from; what a geometric input
actually supplies is a bound on the module's **support**.

This file closes that distance. For a closed subset `S` of the space, Noetherian of dimension at
most `d`, a sheaf whose stalks vanish off `S` has no cohomology above degree `d`. Nothing about
`X` is assumed: not Noetherian, not quasi-compact, and for the module statements neither
quasi-coherence nor a morphism.

The step that was missing is [Stacks, Tag 01AX]: a sheaf of abelian groups supported on a closed
subset *is* pushed forward from that subset. That is
`Stacks.ClosedImmersion.essImage_closedInclusionPushforward_iff_forall_stalk_isZero`; the
cohomology of the subset and of its pushforward agree by [Stacks, Tag 02UV],
`Stacks.ClosedImmersion.cohomologyPushforwardIso`, and on the subset Grothendieck's theorem
[Stacks, Tag 02UZ] applies. The passage from abelian sheaves to modules is the comparison of
[Stacks, Tag 03FD] and [Stacks, Tag 01F1], exactly as in the pushforward form.

## Main results

All in the namespace `Stacks.CohomologyVanishing`.

* `subsingleton_sheafH_of_forall_stalk_isZero_of_isClosedEmbedding` and
  `subsingleton_sheafH_of_forall_stalk_isZero`: **[Stacks, Tag 02UZ] for an abelian sheaf
  supported on a closed subset**, the second with the subset itself rather than a closed
  embedding onto it.
* `isZero_hgroup_top_of_forall_stalk_isZero`: the same for a sheaf of modules over a sheaf of
  rings on an arbitrary topological space, in the `Hgroup` spelling.
* `isZero_rightDerived_moduleGlobalSections_of_forall_stalk_isZero` and
  `isZero_rightDerivedPlus_moduleGlobalSections_of_forall_stalk_isZero`: the same on a scheme, in
  the two indexings of the derived functors of `moduleGlobalSections`.

## Implementation notes

The support hypothesis is spelled out as vanishing of the stalks outside `S`, rather than as
containment of `Stacks.AbelianSheaf.support`, so that it can be verified pointwise; the two are
`Stacks.AbelianSheaf.support_subset_iff` apart. For a sheaf of modules the stalk in question is
that of the underlying presheaf of abelian groups, `F.val.presheaf`, which is the spelling
`AlgebraicGeometry.CohomologySupportedOn` uses and is the same term as the stalk of
`(SheafOfModules.toSheaf R).obj F`.

`NoetherianSpace ↥S` is a hypothesis on the *subspace* and does not follow from anything about
`X`; conversely it is automatic when `X` itself is Noetherian, by
`TopologicalSpace.NoetherianSpace.set`. The dimension bound is likewise on the subspace, where
`topologicalKrullDim_subspace_le` makes it weaker than a bound on `X`.

The abelian statements are written for a space in `Type u` while
`Stacks.ClosedImmersion.essImage_closedInclusionPushforward_iff_forall_stalk_isZero` and
`Stacks.ClosedImmersion.cohomologyPushforwardIso` are written for objects of `TopCat`; the two
are crossed by `TopCat.of`, whose carrier is the type it is built from, so the sheaf categories
agree on the nose and only the applications inside the proof mention it.

## References

* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 01AX](https://stacks.math.columbia.edu/tag/01AX)
* [Stacks Project, Tag 02UV](https://stacks.math.columbia.edu/tag/02UV)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace Topology
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.CohomologyVanishing

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-! ### Abelian sheaves -/

/-- **[Stacks, Tag 02UZ] for an abelian sheaf supported on the image of a closed embedding.**
Let `i : Z ⟶ X` be a closed embedding of topological spaces with `Z` Noetherian of topological
Krull dimension at most `d`, and let `G` be a sheaf of abelian groups on `X` whose stalks vanish
at every point outside the image of `i`. Then `Hᵖ(X, G) = 0` for every `p > d`.

**No hypothesis on `X`.** By [Stacks, Tag 01AX] the support condition puts `G` in the essential
image of `i_*`, so `G ≅ i_* A` for a sheaf `A` on `Z`; cohomology does not change along the
pushforward ([Stacks, Tag 02UV]), and on `Z` Grothendieck's vanishing theorem applies. -/
theorem subsingleton_sheafH_of_forall_stalk_isZero_of_isClosedEmbedding
    {Z X : Type u} [TopologicalSpace Z] [TopologicalSpace X] [NoetherianSpace Z]
    (i : Z → X) (hi : IsClosedEmbedding i) {d p : ℕ}
    (hdim : topologicalKrullDim Z ≤ (d : WithBot ℕ∞)) (hp : d < p)
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hG : ∀ x : X, x ∉ Set.range i → IsZero (TopCat.Presheaf.stalk (X := TopCat.of X) G.obj x)) :
    Subsingleton (Sheaf.H.{u} G p) := by
  obtain ⟨A, ⟨e⟩⟩ :=
    (Stacks.ClosedImmersion.essImage_closedInclusionPushforward_iff_forall_stalk_isZero
      (Z := TopCat.of Z) (X := TopCat.of X) (TopCat.ofHom ⟨i, hi.continuous⟩) hi G).2 hG
  have hA : IsZero ((Sheaf.functorH (Opens.grothendieckTopology Z) p).obj A) :=
    AddCommGrpCat.isZero_iff_subsingleton.2
      (subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le hdim hp A)
  have h0 : IsZero ((Sheaf.functorH (Opens.grothendieckTopology X) p).obj G) :=
    IsZero.of_iso hA
      (((Sheaf.functorH (Opens.grothendieckTopology X) p).mapIso e).symm.trans
        ((Stacks.ClosedImmersion.cohomologyPushforwardIso
          (Z := TopCat.of Z) (X := TopCat.of X) (TopCat.ofHom ⟨i, hi.continuous⟩) hi p).app A).symm)
  rw [← Sheaf.functorH_obj_coe]
  exact AddCommGrpCat.subsingleton_of_isZero h0

/-- **[Stacks, Tag 02UZ] for an abelian sheaf supported on a closed subset.** Let `S` be a
closed subset of a topological space `X` which is Noetherian of topological Krull dimension at
most `d`, and let `G` be a sheaf of abelian groups on `X` whose stalks vanish outside `S`. Then
`Hᵖ(X, G) = 0` for every `p > d`.

This is `subsingleton_sheafH_of_forall_stalk_isZero_of_isClosedEmbedding` at the inclusion of
`S`, whose image is `S`. -/
theorem subsingleton_sheafH_of_forall_stalk_isZero {X : Type u} [TopologicalSpace X]
    (S : Set X) (hS : IsClosed S) [NoetherianSpace S] {d p : ℕ}
    (hdim : topologicalKrullDim S ≤ (d : WithBot ℕ∞)) (hp : d < p)
    (G : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    (hG : ∀ x : X, x ∉ S → IsZero (TopCat.Presheaf.stalk (X := TopCat.of X) G.obj x)) :
    Subsingleton (Sheaf.H.{u} G p) :=
  subsingleton_sheafH_of_forall_stalk_isZero_of_isClosedEmbedding Subtype.val
    hS.isClosedEmbedding_subtypeVal hdim hp G
    fun x hx => hG x fun hxS => hx ⟨⟨x, hxS⟩, rfl⟩

/-! ### Sheaves of modules -/

/-- **[Stacks, Tag 02UZ] for a sheaf of modules supported on a closed subset.** Let `R` be a
sheaf of rings on a topological space `X`, let `S ⊆ X` be closed, Noetherian and of topological
Krull dimension at most `d`, and let `ℱ` be *any* sheaf of `R`-modules whose stalks vanish
outside `S`. Then `Hᵖ(X, ℱ) = 0` for every `p > d`, the cohomology being the `p`-th right
derived functor of sections over the whole space taken in `Mod(R)`.

The module-valued reading of the abelian statement is the comparison of [Stacks, Tag 03FD],
`Stacks.Cohomology.ModuleComparison.isZero_hgroupTop_iff_subsingleton_sheafH`; the stalk of the
underlying abelian sheaf of `ℱ` is the stalk of `ℱ.val.presheaf`, so the support hypothesis
transfers unchanged. -/
theorem isZero_hgroup_top_of_forall_stalk_isZero {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} R)]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    (S : Set X) (hS : IsClosed S) [NoetherianSpace S] {d p : ℕ}
    (hdim : topologicalKrullDim S ≤ (d : WithBot ℕ∞)) (hp : d < p)
    (F : SheafOfModules.{u} R)
    (hF : ∀ x : X, x ∉ S → IsZero (TopCat.Presheaf.stalk (X := TopCat.of X) F.val.presheaf x)) :
    IsZero (Hgroup R ⊤ p F) :=
  (Stacks.Cohomology.ModuleComparison.isZero_hgroupTop_iff_subsingleton_sheafH R p F).2
    (subsingleton_sheafH_of_forall_stalk_isZero S hS hdim hp
      ((SheafOfModules.toSheaf.{u} R).obj F) hF)

/-- **[Stacks, Tag 02UZ] for the modules on a scheme supported on a closed subset.** If `S` is a
closed subset of `X` which is Noetherian of dimension at most `d`, then `Hᵖ(X, ℱ) = 0` for every
`p > d` and every `ℱ : X.Modules` whose stalks vanish outside `S`, in the
`Functor.rightDerived` indexing.

This is `isZero_hgroup_top_of_forall_stalk_isZero` at `R = 𝒪_X` read through [Stacks, Tag 01F1],
namely `Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup`;
`moduleGlobalSections X` *is* `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`, so there is
nothing further to transport. -/
theorem isZero_rightDerived_moduleGlobalSections_of_forall_stalk_isZero
    (X : Scheme.{u}) (S : Set (X : Type u)) (hS : IsClosed S) [NoetherianSpace S] {d p : ℕ}
    (hdim : topologicalKrullDim S ≤ (d : WithBot ℕ∞)) (hp : d < p) (F : X.Modules)
    (hF : ∀ x : (X : Type u), x ∉ S →
      IsZero (TopCat.Presheaf.stalk (X := X.toTopCat) F.val.presheaf x)) :
    IsZero (((moduleGlobalSections X).rightDerived p).obj F) :=
  (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      X.ringCatSheaf ⊤ p F).2
    (isZero_hgroup_top_of_forall_stalk_isZero X.ringCatSheaf S hS hdim hp F hF)

/-- **[Stacks, Tag 02UZ] for the modules on a scheme supported on a closed subset, in the
`ℤ`-indexed spelling.** The same vanishing as
`isZero_rightDerived_moduleGlobalSections_of_forall_stalk_isZero`, stated for
`Functor.rightDerivedPlus`, which is the indexing
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/` is written in.

The degree is a natural number because `(d : ℤ) < i` forces `0 ≤ i`, and the two indexings are
compared by `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff`. -/
theorem isZero_rightDerivedPlus_moduleGlobalSections_of_forall_stalk_isZero
    (X : Scheme.{u}) (S : Set (X : Type u)) (hS : IsClosed S) [NoetherianSpace S] {d : ℕ} {i : ℤ}
    (hdim : topologicalKrullDim S ≤ (d : WithBot ℕ∞)) (hi : (d : ℤ) < i) (F : X.Modules)
    (hF : ∀ x : (X : Type u), x ∉ S →
      IsZero (TopCat.Presheaf.stalk (X := X.toTopCat) F.val.presheaf x)) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus i).obj F) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ i by omega)
  refine (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (moduleGlobalSections X)
    (n := p) rfl F).2 ?_
  exact isZero_rightDerived_moduleGlobalSections_of_forall_stalk_isZero X S hS hdim
    (by exact_mod_cast hi) F hF

end

end Stacks.CohomologyVanishing

end
