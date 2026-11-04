module

public import StacksFrontier.AlgebraicGeometry.ClosedImmersionCohomology.Basic
public import StacksFrontier.Homology.DerivedIndexing.Basic
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.GlobalSheafCohomologyComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.ModuleComparison.VanishingTransfer
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.SpectralSpaces

/-!
# Grothendieck vanishing for sheaves of modules on a Noetherian space

[Stacks, Tag 02UZ] says: *let `X` be a Noetherian topological space; if `dim(X) ≤ d` then
`Hᵖ(X, ℱ) = 0` for all `p > d` and any abelian sheaf `ℱ` on `X`.* The tag is about abelian
sheaves, and that is how
`Stacks.CohomologyVanishing.subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le` states
it, in Mathlib's `Ext`-theoretic `CategoryTheory.Sheaf.H`.

Every consumer of cohomological vanishing in this development works instead with modules: the
derived functors of `Stacks.Cohomology.AffineBase.moduleGlobalSections`, computed in
`Mod(𝒪_X)`. An abelian sheaf is not a module, so the tag as stated does not apply to them, and
until now the only module-valued reading of it in the library was
`AlgebraicGeometry.isZero_cohomologyOverField_of_topologicalKrullDim_le`, which needs a proper
structure morphism to the spectrum of a *field* and lands in `cohomologyOverField`.

This file reads [Stacks, Tag 02UZ] for sheaves of modules with **no** hypothesis beyond the
tag's own: a sheaf of rings on a Noetherian space of dimension at most `d`, and an arbitrary
sheaf of modules over it — not quasi-coherent, not coherent, no base field, no morphism. The
three comparisons that do it are all already in the library; what was missing was their
composite.

* `Stacks.Cohomology.ModuleComparison.isZero_hgroupTop_iff_subsingleton_sheafH`
  ([Stacks, Tag 03FD]) identifies `Hgroup R ⊤ p F`, the derived sections of `F` over the whole
  space taken in `Mod(𝒪_X)`, with the sheaf cohomology of the underlying abelian sheaf.
* `Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup`
  ([Stacks, Tag 01F1]) identifies that with the right derived functors of the *module-valued*
  evaluation functor, which on a scheme is `moduleGlobalSections` on the nose.
* `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff` crosses between Mathlib's
  `ℕ`-indexed `Functor.rightDerived` and the `ℤ`-indexed `Functor.rightDerivedPlus` that
  `StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/` is written in.

The last group of statements is the form the proof of [Stacks, Tag 02V7] consumes. There the
space whose dimension is bounded is not `X` itself but a closed subscheme of it — an
infinitesimal neighbourhood of a fibre, which has the same underlying space as the fibre — and
the module on `X` is the pushforward of a module on that subscheme. Cohomology does not change
along a closed immersion (`Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward`,
[Stacks, Tag 01EX]), so the bound on the subscheme suffices.

## Main results

All in the namespace `Stacks.CohomologyVanishing`.

* `isZero_hgroup_top_of_noetherianSpace_of_dim_le`: **[Stacks, Tag 02UZ] for sheaves of
  modules**, over a sheaf of rings on a Noetherian topological space, in the `Hgroup` spelling.
* `isZero_rightDerived_moduleGlobalSections_of_noetherianSpace_of_dim_le` and
  `isZero_rightDerivedPlus_moduleGlobalSections_of_noetherianSpace_of_dim_le`: the same on a
  scheme, in the two indexings of the derived functors of `moduleGlobalSections`.
* `isZero_rightDerived_pushforward_of_noetherianSpace_of_dim_le` and
  `isZero_rightDerivedPlus_pushforward_of_noetherianSpace_of_dim_le`: the vanishing of
  `Hᵖ(X, i_* 𝒢)` for a closed immersion `i : Z ⟶ X` whose source has Noetherian underlying
  space of dimension at most `d`, with no hypothesis on `X`.

## Implementation notes

The hypothesis is `NoetherianSpace ↥X` on the underlying space, not `IsNoetherian X` on the
scheme: Grothendieck's theorem is topological, and a scheme-level Noetherian hypothesis would be
strictly stronger. `AlgebraicGeometry.IsNoetherian.noetherianSpace` supplies the instance where
a consumer has the scheme-level condition instead.

`Stacks.Cohomology.AffineBase.moduleGlobalSections X` is a reducible abbreviation for
`SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`, so the scheme statements are the
ringed-space one at `R = X.ringCatSheaf` and `U = ⊤` with no transport; this is why no
separate comparison appears in their proofs.

Nothing here is quasi-coherent. That is deliberate and is where this differs from
`subsingleton_smallEtaleCohomology_quasicoherent_of_topologicalKrullDim_le` of
`StacksFrontier/AlgebraicGeometry/Spaces/VanishingAboveTheDimension.lean`, which proves clause
(1) of [Stacks, Tag 0A4R] and whose quasi-coherence hypothesis is load-bearing because it works
on the small étale site, where the abelian-sheaf reading is false. On the Zariski site, which is
the site of the opens of `X` and the one `moduleGlobalSections` is taken over, the abelian-sheaf
reading is [Stacks, Tag 02UZ] itself and no quasi-coherence is needed.

## References

* [Stacks Project, Tag 02UZ](https://stacks.math.columbia.edu/tag/02UZ)
* [Stacks Project, Tag 03FD](https://stacks.math.columbia.edu/tag/03FD)
* [Stacks Project, Tag 01F1](https://stacks.math.columbia.edu/tag/01F1)
* [Stacks Project, Tag 01EX](https://stacks.math.columbia.edu/tag/01EX)
* [Stacks Project, Tag 02V7](https://stacks.math.columbia.edu/tag/02V7)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Cohomology.AffineBase

universe u

namespace Stacks.CohomologyVanishing

attribute [local instance] HasDerivedCategory.standard

noncomputable section

/-- **[Stacks, Tag 02UZ] for sheaves of modules.** Let `R` be a sheaf of rings on a Noetherian
topological space `X` of topological Krull dimension at most `d`, and let `ℱ` be *any* sheaf of
`R`-modules. Then `Hᵖ(X, ℱ) = 0` for every `p > d`, the cohomology being the `p`-th right
derived functor of sections over the whole space taken in `Mod(R)`.

The tag is about abelian sheaves. Its module-valued reading is the tag itself composed with
[Stacks, Tag 03FD], which identifies the two: that comparison is
`Stacks.Cohomology.ModuleComparison.isZero_hgroupTop_iff_subsingleton_sheafH`. No quasi-coherence
and no hypothesis on `R` enter, because neither enters [Stacks, Tag 02UZ].

[Stacks, Tag 02UZ] (not registered here: this is not the whole statement of the tag): for a sheaf
of modules on a Noetherian space, read through the comparison of Tag 03FD with the cohomology of
the underlying abelian sheaf
-/
theorem isZero_hgroup_top_of_noetherianSpace_of_dim_le
    {X : Type u} [TopologicalSpace X] [NoetherianSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{u})
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{u}]
    [(Opens.grothendieckTopology X).WEqualsLocallyBijective AddCommGrpCat.{u}]
    [EnoughInjectives (SheafOfModules.{u} R)]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    [HasInjectiveResolutions (Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})]
    {d p : ℕ} (hdim : topologicalKrullDim X ≤ (d : WithBot ℕ∞)) (hp : d < p)
    (F : SheafOfModules.{u} R) :
    IsZero (Hgroup R ⊤ p F) :=
  (Stacks.Cohomology.ModuleComparison.isZero_hgroupTop_iff_subsingleton_sheafH R p F).2
    (subsingleton_sheafCohomology_of_noetherianSpace_of_dim_le hdim hp _)

/-- **[Stacks, Tag 02UZ] for the modules on a scheme with Noetherian underlying space.** If
`dim(X) ≤ d` then `Hᵖ(X, ℱ) = 0` for every `p > d` and every `ℱ : X.Modules`, in the
`Functor.rightDerived` indexing.

This is `isZero_hgroup_top_of_noetherianSpace_of_dim_le` at `R = 𝒪_X` read through
[Stacks, Tag 01F1], namely `Stacks.Cohomology.ModuleComparison`'s
`isZero_rightDerived_evaluation_iff_isZero_hgroup`;
`moduleGlobalSections X` *is* `SheafOfModules.evaluation X.ringCatSheaf (op ⊤)`, so there is
nothing further to transport.

[Stacks, Tag 02UZ] (not registered here: this is not the whole statement of the tag): for the
modules on a scheme whose underlying space is Noetherian, with no quasi-coherence, no base field
and no morphism
-/
theorem isZero_rightDerived_moduleGlobalSections_of_noetherianSpace_of_dim_le
    (X : Scheme.{u}) [NoetherianSpace (X : Type u)] {d p : ℕ}
    (hdim : topologicalKrullDim (X : Type u) ≤ (d : WithBot ℕ∞)) (hp : d < p)
    (F : X.Modules) :
    IsZero (((moduleGlobalSections X).rightDerived p).obj F) :=
  (Stacks.Cohomology.ModuleComparison.isZero_rightDerived_evaluation_iff_isZero_hgroup
      X.ringCatSheaf ⊤ p F).2
    (isZero_hgroup_top_of_noetherianSpace_of_dim_le X.ringCatSheaf hdim hp F)

/-- Vanishing of `rightDerived p` for all `p > d` gives vanishing of `rightDerivedPlus i` for
all `i > d`. -/
private theorem isZero_rightDerivedPlus_moduleGlobalSections_of_forall {X : Scheme.{u}} {d : ℕ}
    {i : ℤ} (hi : (d : ℤ) < i) (F : X.Modules)
    (h : ∀ p : ℕ, d < p → IsZero (((moduleGlobalSections X).rightDerived p).obj F)) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus i).obj F) := by
  obtain ⟨p, rfl⟩ := Int.eq_ofNat_of_zero_le (show (0 : ℤ) ≤ i by omega)
  exact (Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff (moduleGlobalSections X)
    (n := p) rfl F).2 (h p (by exact_mod_cast hi))

/-- **[Stacks, Tag 02UZ] for the modules on a scheme, in the `ℤ`-indexed spelling.** The same
vanishing as `isZero_rightDerived_moduleGlobalSections_of_noetherianSpace_of_dim_le`, stated for
`Functor.rightDerivedPlus`, which is the indexing
`StacksFrontier/AlgebraicGeometry/TopDegreeBaseChange/` and the statements of [Stacks, Tag 0E7D]
and [Stacks, Tag 0E7H] are written in.

The degree is a natural number because `(d : ℤ) < i` forces `0 ≤ i`, and the two indexings are
compared by `Stacks.DerivedIndexing.isZero_rightDerivedPlus_obj_iff`.

[Stacks, Tag 02UZ] (not registered here: this is not the whole statement of the tag): for the
modules on a scheme whose underlying space is Noetherian, in the rightDerivedPlus indexing
-/
theorem isZero_rightDerivedPlus_moduleGlobalSections_of_noetherianSpace_of_dim_le
    (X : Scheme.{u}) [NoetherianSpace (X : Type u)] {d : ℕ} {i : ℤ}
    (hdim : topologicalKrullDim (X : Type u) ≤ (d : WithBot ℕ∞)) (hi : (d : ℤ) < i)
    (F : X.Modules) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus i).obj F) :=
  isZero_rightDerivedPlus_moduleGlobalSections_of_forall hi F fun _ hp ↦
    isZero_rightDerived_moduleGlobalSections_of_noetherianSpace_of_dim_le X hdim hp F

/-- **Vanishing above the dimension of a closed subscheme.** Let `i : Z ⟶ X` be a closed
immersion whose source has Noetherian underlying space of topological Krull dimension at most
`d`, and let `𝒢` be any sheaf of modules on `Z`. Then `Hᵖ(X, i_* 𝒢) = 0` for every `p > d`.

**No hypothesis on `X`**: neither Noetherian, nor a dimension bound, nor quasi-coherence of `𝒢`.
Cohomology does not change along a closed immersion
(`Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward`, [Stacks, Tag 01EX]), and
restriction of scalars along `i^♯` changes neither the carrier of a module nor therefore its
being a zero object, so the vanishing on `Z` is the vanishing on `X`.

This is the shape in which the proof of [Stacks, Tag 02V7] uses Grothendieck vanishing: there
`Z` is an infinitesimal neighbourhood `X_n` of the fibre `X_y`, whose underlying space is that
of `X_y` and hence Noetherian of dimension `dim(X_y)`, while `X` itself is only proper over a
Noetherian base and has no such dimension bound. -/
theorem isZero_rightDerived_pushforward_of_noetherianSpace_of_dim_le
    {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    [NoetherianSpace (Z : Type u)] {d p : ℕ}
    (hdim : topologicalKrullDim (Z : Type u) ≤ (d : WithBot ℕ∞)) (hp : d < p)
    (G : Z.Modules) :
    IsZero (((moduleGlobalSections X).rightDerived p).obj
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G)) := by
  have : (ModuleCat.restrictScalars.{u} i.appTop.hom).Additive := ⟨by intros; rfl⟩
  refine IsZero.of_iso ?_ (Stacks.Cohomology.ClosedImmersion.cohomologyObjIsoPushforward i G p)
  exact Functor.map_isZero (ModuleCat.restrictScalars.{u} i.appTop.hom)
    (isZero_rightDerived_moduleGlobalSections_of_noetherianSpace_of_dim_le Z hdim hp G)

/-- **Vanishing above the dimension of a closed subscheme, in the `ℤ`-indexed spelling.** This
is `isZero_rightDerived_pushforward_of_noetherianSpace_of_dim_le` for
`Functor.rightDerivedPlus`, the indexing the statements of [Stacks, Tag 0E7D] use here. -/
theorem isZero_rightDerivedPlus_pushforward_of_noetherianSpace_of_dim_le
    {Z X : Scheme.{u}} (i : Z ⟶ X) [AlgebraicGeometry.IsClosedImmersion i]
    [NoetherianSpace (Z : Type u)] {d : ℕ} {j : ℤ}
    (hdim : topologicalKrullDim (Z : Type u) ≤ (d : WithBot ℕ∞)) (hj : (d : ℤ) < j)
    (G : Z.Modules) :
    IsZero (((moduleGlobalSections X).rightDerivedPlus j).obj
      ((AlgebraicGeometry.Scheme.Modules.pushforward i).obj G)) :=
  isZero_rightDerivedPlus_moduleGlobalSections_of_forall hj _ fun _ hp ↦
    isZero_rightDerived_pushforward_of_noetherianSpace_of_dim_le i hdim hp G

end

end Stacks.CohomologyVanishing

end
