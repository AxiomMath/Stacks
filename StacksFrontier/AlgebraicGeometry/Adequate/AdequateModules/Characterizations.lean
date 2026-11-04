module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedAffineSections
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AssociatedKernel

/-!
# The characterisations of adequate sheaves of modules

[Stacks, Tag 06VK] states five equivalent conditions on an `𝒪`-module `𝓕` on the big `τ`-site
over a scheme `S`:

1. `𝓕` is adequate;
2. there is an affine open covering `S = ⋃ Sᵢ` and maps `𝓖ᵢ ⟶ 𝓗ᵢ` of quasi-coherent
   `𝒪_{Sᵢ}`-modules with `𝓕|_(Sch/Sᵢ)_τ = Ker(𝓖ᵢᵃ ⟶ 𝓗ᵢᵃ)`;
3. the same with an arbitrary `τ`-covering `{Sᵢ → S}` in place of the affine open covering;
4. there is a `τ`-covering `{fᵢ : Sᵢ → S}` with every pullback `fᵢ^*𝓕` adequate;
5. for every affine scheme `U` over `S` the restriction `𝓕|_(Sch/U)_τ` is the kernel of a map
   `𝓖ᵃ ⟶ 𝓗ᵃ` of quasi-coherent `𝒪_U`-modules.

The individual implications towards adequacy are
`Stacks.Adequate.isAdequate_of_coveringPullback` and
`Stacks.Adequate.isAdequate_of_coveringAssociatedKernel`, which take the covering apart as
explicit data. This module packages conditions (2), (3), (4) and (5) as predicates on `𝓕`, so
that the implications between them can be stated, and proves:

* the implication (1) ⇒ (4), **with no hypotheses at all**, which closes the equivalence of
  conditions (1) and (4) outright; and
* the source's "immediate" chain (5) ⇒ (2) ⇒ (3).

The remaining direction, (1) ⇒ (5) and with it (1) ⇒ (2) and (1) ⇒ (3), is
`Stacks.Adequate.hasAssociatedKernelOnEveryAffine_of_isAdequate` in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AssociatedKernelConverse.lean`, which
is downstream of this module because it states its conclusion with the conditions defined
here.

## Main definitions

* `Stacks.Adequate.HasAdequatePullbackCover` — condition (4).
* `Stacks.Adequate.HasCoveringAssociatedKernel` — condition (3).
* `Stacks.Adequate.HasAffineOpenAssociatedKernelCover` — condition (2).
* `Stacks.Adequate.HasAssociatedKernelOnEveryAffine` — condition (5).

## Main results

* `Stacks.Adequate.isAdequateOnPullback_id` — an adequate `𝓕` restricts to an adequate module
  along the identity of `S`. The big site over `S` obtained from `B` by base change along `𝟙 S`
  with the data of `B` itself *is* `B`, the index functor of that base change *is* the identity
  functor, and the restriction of `𝓕` along it *is* `𝓕`; all three hold definitionally, so no
  transport is involved and the sheaf condition the pullback asks for is the sheaf condition of
  `𝓕`.
* `Stacks.Adequate.isAdequate_iff_hasAdequatePullbackCover` — **[Stacks, Tag 06VK], the
  equivalence of conditions (1) and (4), with no hypotheses.** The implication (4) ⇒ (1) is
  `Stacks.Adequate.isAdequate_of_coveringPullback`; for (1) ⇒ (4) the one-member covering of `S`
  by its own identity serves, which is why this direction appeals to neither
  [Stacks, Tag 06VJ] nor [Stacks, Tag 06VI].
* `Stacks.Adequate.hasCoveringAssociatedKernel_of_hasAffineOpenAssociatedKernelCover` — the
  implication (2) ⇒ (3), because an open immersion has the covering morphism property of each of
  the five topologies.
* `Stacks.Adequate.hasAffineOpenAssociatedKernelCover_of_hasAssociatedKernelOnEveryAffine` — the
  implication (5) ⇒ (2), by taking the affine open cover of `S`, whose members belong to the site
  because an open immersion does not raise the size of a scheme.
* `Stacks.Adequate.isAdequate_of_hasAffineOpenAssociatedKernelCover` and
  `Stacks.Adequate.isAdequate_of_hasAssociatedKernelOnEveryAffine` — the resulting implications
  (2) ⇒ (1) and (5) ⇒ (1).

## Implementation notes

The source's proof of (1) ⇒ (4) goes through [Stacks, Tag 06VJ], that the pullback of an adequate
module is adequate. Condition (4) is however an *existential* over `τ`-coverings, and for the
one-member covering of `S` by `𝟙 S` the pullback is `𝓕` itself. So the implication (1) ⇒ (4) is
strictly weaker than Tag 06VJ, and the proof here does not go through that tag at all; nothing
is weakened, the conclusion being condition (4) exactly as the source states it. The converse
direction (4) ⇒ (1) is likewise direct, so conditions (1) and (4) are *equivalent* in this
library with no hypotheses, by an argument independent of Tags 06VJ and 06VI.

Conditions (2), (3) and (5) are built from `Stacks.Adequate.IsAssociatedKernelOnPullback`, which
carries `Stacks.Adequate.AffineAssociatedSections` for the site over each member of the covering
along with the kernel presentation. That makes these three conditions *stronger* than the
source's, and the implications (2) ⇒ (1), (3) ⇒ (1) and (5) ⇒ (1) correspondingly weaker; the
bundled hypothesis is the one input of the source's proof that the library does not supply, and
it is carried in the condition rather than in the theorems because it is a statement about the
site the presentation lives on. The implications (5) ⇒ (2) ⇒ (3) proved here are insensitive to
the bundling: it is carried along unchanged.

The converse implications (1) ⇒ (5), and hence (1) ⇒ (2) and (1) ⇒ (3), are proved in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AssociatedKernelConverse.lean`, with no
hypotheses, and so the bundled `Stacks.Adequate.AffineAssociatedSections` conjunct costs
nothing: it is supplied there by the theorem
`Stacks.Adequate.affineAssociatedSections`. Reconstructing `𝓕|_(Sch/U)_τ` as a kernel of
associated modules from the adequacy of `F_{𝓕, A}` does **not** need the quasi-inverse of the
equivalence of [Stacks, Tag 06ZJ], of which the library has only the comparison functor
`Stacks.Adequate.adequateComparison`: a quasi-inverse would build a sheaf from an arbitrary
adequate module-valued functor, whereas all that is needed is a sheaf whose affine sections are
a *module extension*, and the associated module of `AlgebraicGeometry.tilde` of an `A`-module is
one. See the module documentation there.

## References

* [Stacks Project, Tag 06VK](https://stacks.math.columbia.edu/tag/06VK)
* [Stacks Project, Tag 06VI](https://stacks.math.columbia.edu/tag/06VI)
* [Stacks Project, Tag 06VJ](https://stacks.math.columbia.edu/tag/06VJ)
* [Stacks Project, Tag 06ZJ](https://stacks.math.columbia.edu/tag/06ZJ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}} (B : BigSite τ S)

/-! ### Condition (4): adequacy after pullback along a covering -/

/-- **Condition (4) of [Stacks, Tag 06VK]:** there is a `τ`-covering `{gᵢ : Tᵢ → S}` of `S` by
schemes of the site such that every pullback `gᵢ^*𝓕` is an adequate `𝒪`-module on the big
`τ`-site over `Tᵢ`. -/
public abbrev HasAdequatePullbackCover (F : SheafOfModules.{u} B.structureSheaf) : Prop :=
  ∃ (I : Type (u + 1)) (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S),
    (∀ i, coveringMorphismProperty τ (g i)) ∧
    ((⋃ i, Set.range (g i)) = Set.univ) ∧
    ∀ i, IsAdequateOnPullback B F (g i)

/-- An adequate `𝒪`-module restricts along the identity of `S` to an adequate `𝒪`-module.

The big site over `S` produced by base change from `B` along `𝟙 S`, with the cutoff, the base
membership, the topology, the sheaf condition and the choice data of `B` itself, is `B`; the
index functor of that base change is the identity functor of `B.category`; and the restriction
of `𝓕` along it is `𝓕`. All three are definitional, so the sheaf condition which
`Stacks.Adequate.IsAdequateOnPullback` requires of the restriction is the sheaf condition of
`𝓕`, and the adequacy it requires of the restriction is the adequacy of `𝓕`. -/
public theorem isAdequateOnPullback_id (F : SheafOfModules.{u} B.structureSheaf)
    (hF : IsAdequate B F) :
    IsAdequateOnPullback B F (𝟙 S) :=
  ⟨B.base_mem, B.topology, B.isSheaf, B.chosen, F.isSheaf, hF⟩

/-- **[Stacks, Tag 06VK], the implication (1) ⇒ (4).** An adequate `𝒪`-module satisfies
condition (4): the one-member covering of `S` by `𝟙 S` is a `τ`-covering, and the pullback of
`𝓕` along it is `𝓕`.

The source argues this implication from [Stacks, Tag 06VJ], that the pullback of an adequate
module along *any* morphism is adequate. Condition (4) only asks for *some* `τ`-covering with
adequate pullbacks, so the identity covering suffices and that tag is not appealed to here at
all. -/
public theorem hasAdequatePullbackCover_of_isAdequate
    (F : SheafOfModules.{u} B.structureSheaf) (hF : IsAdequate B F) :
    HasAdequatePullbackCover B F :=
  ⟨PUnit.{u + 2}, fun _ => S, fun _ => 𝟙 S,
    fun _ => coveringMorphismProperty_of_isOpenImmersion τ _,
    Set.eq_univ_of_forall fun x => Set.mem_iUnion.mpr ⟨PUnit.unit, x, rfl⟩,
    fun _ => isAdequateOnPullback_id B F hF⟩

/-- **[Stacks, Tag 06VK], the implication (4) ⇒ (1)**, in the packaged form: this is
`Stacks.Adequate.isAdequate_of_coveringPullback` with the covering taken from condition (4). -/
public theorem isAdequate_of_hasAdequatePullbackCover
    (F : SheafOfModules.{u} B.structureSheaf) (hF : HasAdequatePullbackCover B F) :
    IsAdequate B F := by
  obtain ⟨I, T, g, hg, hsurj, hadq⟩ := hF
  exact isAdequate_of_coveringPullback B F I T g hg hsurj hadq

/-- **[Stacks, Tag 06VK], the equivalence of conditions (1) and (4), with no hypotheses.** An
`𝒪`-module on the big `τ`-site over `S` is adequate exactly when there is a `τ`-covering of `S`
all of whose pullbacks of it are adequate.

Both directions are unconditional. For (4) ⇒ (1) a covering of each member by affine schemes of
the site composes with the covering of `S`, and the affine-section functors along the composite
are those of the pullback; for (1) ⇒ (4) the identity covering of `S` serves. In particular this
clause of the source does not depend on `Stacks.Adequate.AffineAssociatedSections`, which the
chapter still carries as a hypothesis; nor, a fortiori, on any of the three steps of the proof
of [Stacks, Tag 06VI], all of which are now theorems —
`Stacks.Adequate.standardAffineRefinement`, `Stacks.Adequate.affineSectionRestriction` and
`Stacks.Adequate.standardAffineDescent`. -/
public theorem isAdequate_iff_hasAdequatePullbackCover
    (F : SheafOfModules.{u} B.structureSheaf) :
    IsAdequate B F ↔ HasAdequatePullbackCover B F :=
  ⟨hasAdequatePullbackCover_of_isAdequate B F, isAdequate_of_hasAdequatePullbackCover B F⟩

/-! ### Conditions (2), (3) and (5): local kernel presentations -/

/-- **Condition (3) of [Stacks, Tag 06VK]:** there is a `τ`-covering `{gᵢ : Sᵢ → S}` of `S` by
schemes of the site and, for each `i`, a presentation of `𝓕|_(Sch/Sᵢ)_τ` as the kernel of a map
`𝓖ᵢᵃ ⟶ 𝓗ᵢᵃ` of associated modules of quasi-coherent `𝒪_{Sᵢ}`-modules. -/
public abbrev HasCoveringAssociatedKernel (F : SheafOfModules.{u} B.structureSheaf) : Prop :=
  ∃ (I : Type (u + 1)) (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S),
    (∀ i, coveringMorphismProperty τ (g i)) ∧
    ((⋃ i, Set.range (g i)) = Set.univ) ∧
    ∀ i, IsAssociatedKernelOnPullback B F (g i)

/-- **Condition (2) of [Stacks, Tag 06VK]:** there is an affine open covering `S = ⋃ Spec Aᵢ`
and, for each `i`, a presentation of `𝓕|_(Sch/Spec Aᵢ)_τ` as the kernel of a map
`𝓖ᵢᵃ ⟶ 𝓗ᵢᵃ` of associated modules of quasi-coherent `𝒪_{Spec Aᵢ}`-modules.

The covering is by *affine opens* of `S`: the members are spectra of rings and the morphisms to
`S` are open immersions, which is the source's `S = ⋃ Sᵢ` with the `Sᵢ` affine open. -/
public abbrev HasAffineOpenAssociatedKernelCover
    (F : SheafOfModules.{u} B.structureSheaf) : Prop :=
  ∃ (I : Type (u + 1)) (A : I → CommRingCat.{u}) (f : ∀ i, Spec (A i) ⟶ S),
    (∀ i, IsOpenImmersion (f i)) ∧
    ((⋃ i, Set.range (f i)) = Set.univ) ∧
    ∀ i, IsAssociatedKernelOnPullback B F (f i)

/-- **Condition (5) of [Stacks, Tag 06VK]:** for every affine scheme `Spec A` of the site over
`S` the restriction `𝓕|_(Sch/Spec A)_τ` is the kernel of a map `𝓖ᵃ ⟶ 𝓗ᵃ` of associated modules
of quasi-coherent `𝒪_{Spec A}`-modules.

The membership `schemeSizeBelow B.cutoff (Spec A)` is the source's "affine scheme `U` over `S`",
read on `(Sch/S)_τ`: the site's cardinal cutoff makes it explicit which affine schemes over `S`
are objects of the site. -/
public abbrev HasAssociatedKernelOnEveryAffine
    (F : SheafOfModules.{u} B.structureSheaf) : Prop :=
  ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S), schemeSizeBelow B.cutoff (Spec A) →
    IsAssociatedKernelOnPullback B F f

/-! ### Passing between covering families

The two implications (5) ⇒ (2) and (2) ⇒ (3) are statements about covering families of `S` and
not about kernel presentations. They are proved here for a *variable* property `P` of morphisms
to `S`, which is what keeps them cheap: a proof which assembles the existential of condition (2)
or (3) with `Stacks.Adequate.IsAssociatedKernelOnPullback` in place of `P` makes the kernel check
each component against the five-way disjunction over the chosen big sites that predicate unfolds
to, and exhausts its budget. With `P` abstract nothing unfolds, and the two implications below
are instances. -/

/-- Every affine scheme of the site over `S` has the property `P` only if some affine open
covering of `S` by affine schemes of the site has it, namely the affine open cover of `S`.

Membership of each member in the site is `Scheme.size_lt_of_isOpenImmersion`: an open immersion
does not raise the size of a scheme, so an affine open of `S` is below the cutoff because `S`
is. -/
private theorem exists_affineOpenCover_forall (P : ∀ T : Scheme.{u}, (T ⟶ S) → Prop)
    (hP : ∀ (A : CommRingCat.{u}) (f : Spec A ⟶ S),
      schemeSizeBelow B.cutoff (Spec A) → P (Spec A) f) :
    ∃ (I : Type (u + 1)) (A : I → CommRingCat.{u}) (f : ∀ i, Spec (A i) ⟶ S),
      (∀ i, IsOpenImmersion (f i)) ∧
      ((⋃ i, Set.range (f i)) = Set.univ) ∧
      ∀ i, P (Spec (A i)) (f i) := by
  refine ⟨ULift.{u + 1} S.affineOpenCover.I₀,
    fun i => S.affineOpenCover.X i.down,
    fun i => S.affineOpenCover.f i.down,
    fun _ => inferInstance, ?_, ?_⟩
  · refine Set.eq_univ_of_forall fun x => ?_
    obtain ⟨i, y, hy⟩ := S.affineOpenCover.openCover.exists_eq x
    exact Set.mem_iUnion.mpr ⟨⟨i⟩, y, hy⟩
  · intro i
    exact hP _ _ (Scheme.size_lt_of_isOpenImmersion (S.affineOpenCover.f i.down) B.base_mem)

/-- An affine open covering of `S` all of whose members have the property `P` is in particular a
`τ`-covering of `S` all of whose members have it, because an open immersion has the covering
morphism property of each of the five topologies. -/
private theorem exists_covering_of_exists_affineOpenCover (P : ∀ T : Scheme.{u}, (T ⟶ S) → Prop)
    (h : ∃ (I : Type (u + 1)) (A : I → CommRingCat.{u}) (f : ∀ i, Spec (A i) ⟶ S),
      (∀ i, IsOpenImmersion (f i)) ∧
      ((⋃ i, Set.range (f i)) = Set.univ) ∧
      ∀ i, P (Spec (A i)) (f i)) :
    ∃ (I : Type (u + 1)) (T : I → Scheme.{u}) (g : ∀ i, T i ⟶ S),
      (∀ i, coveringMorphismProperty τ (g i)) ∧
      ((⋃ i, Set.range (g i)) = Set.univ) ∧
      ∀ i, P (T i) (g i) := by
  obtain ⟨I, A, f, hopen, hsurj, hP⟩ := h
  exact ⟨I, fun i => Spec (A i), f,
    fun i => @coveringMorphismProperty_of_isOpenImmersion τ _ _ (f i) (hopen i), hsurj, hP⟩

/-- **[Stacks, Tag 06VK], the implication (2) ⇒ (3).** An affine open covering is a
`τ`-covering, because an open immersion has the covering morphism property of each of the five
topologies. This is the source's "(2) ⇒ (3) is immediate". -/
public theorem hasCoveringAssociatedKernel_of_hasAffineOpenAssociatedKernelCover
    (F : SheafOfModules.{u} B.structureSheaf) (hF : HasAffineOpenAssociatedKernelCover B F) :
    HasCoveringAssociatedKernel B F :=
  exists_covering_of_exists_affineOpenCover
    (fun _ g => IsAssociatedKernelOnPullback B F g) hF

/-- **[Stacks, Tag 06VK], the implication (5) ⇒ (2).** The affine open cover of `S` is an affine
open covering whose members are affine schemes of the site, so condition (5) applies to each of
them. This is the source's "(5) ⇒ (2) is immediate". -/
public theorem hasAffineOpenAssociatedKernelCover_of_hasAssociatedKernelOnEveryAffine
    (F : SheafOfModules.{u} B.structureSheaf) (hF : HasAssociatedKernelOnEveryAffine B F) :
    HasAffineOpenAssociatedKernelCover B F :=
  exists_affineOpenCover_forall B (fun _ g => IsAssociatedKernelOnPullback B F g) hF

/-- **[Stacks, Tag 06VK], the implication (3) ⇒ (1)**, in the packaged form: this is
`Stacks.Adequate.isAdequate_of_coveringAssociatedKernel` with the covering taken from
condition (3). -/
public theorem isAdequate_of_hasCoveringAssociatedKernel
    (F : SheafOfModules.{u} B.structureSheaf) (hF : HasCoveringAssociatedKernel B F) :
    IsAdequate B F := by
  obtain ⟨I, T, g, hg, hsurj, hker⟩ := hF
  exact isAdequate_of_coveringAssociatedKernel B F I T g hg hsurj hker

/-- **[Stacks, Tag 06VK], the implication (2) ⇒ (1)**, through condition (3). -/
public theorem isAdequate_of_hasAffineOpenAssociatedKernelCover
    (F : SheafOfModules.{u} B.structureSheaf) (hF : HasAffineOpenAssociatedKernelCover B F) :
    IsAdequate B F :=
  isAdequate_of_hasCoveringAssociatedKernel B F
    (hasCoveringAssociatedKernel_of_hasAffineOpenAssociatedKernelCover B F hF)

/-- **[Stacks, Tag 06VK], the implication (5) ⇒ (1)**, through conditions (2) and (3). -/
public theorem isAdequate_of_hasAssociatedKernelOnEveryAffine
    (F : SheafOfModules.{u} B.structureSheaf) (hF : HasAssociatedKernelOnEveryAffine B F) :
    IsAdequate B F :=
  isAdequate_of_hasAffineOpenAssociatedKernelCover B F
    (hasAffineOpenAssociatedKernelCover_of_hasAssociatedKernelOnEveryAffine B F hF)

end Stacks.Adequate

end
