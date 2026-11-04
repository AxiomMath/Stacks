module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.BigSiteColimits.AffineRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeNaturality

/-!
# The fppf sheaf condition from flat base change (Stacks 076T)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `F` be a presheaf of
modules over the structure sheaf of Stacks 06TV. **Stacks 076T** says that `F` is a sheaf for
the fppf topology of Stacks 06TP as soon as

* (a) `F` is locally quasi-coherent (**Stacks 06WJ**), and
* (b) for every arrow `φ : x ⟶ y` of `𝒳` lying over a morphism of schemes `f : U ⟶ V` which is
  flat *and locally of finite presentation*, the comparison map
  `c_φ : f_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 06WC** is an isomorphism.

Hypothesis (b) is the flat base change property of **Stacks 0762** with its arrows cut down to
those lying over a morphism which is in addition locally of finite presentation: it is asked of
exactly the morphisms which occur in an fppf covering, and it is weaker than Stacks 0762, which
asks the same of every arrow lying over a flat morphism. It is recorded here as
`AlgebraicGeometry.Stack.HasFlatLfpBaseChangeProperty`, and
`AlgebraicGeometry.Stack.hasFlatLfpBaseChangeProperty_of_hasFlatBaseChangeProperty` is the
implication from Stacks 0762.

The source's proof is one step: an fppf covering `{x_i → x}` of `𝒳` lies over an fppf covering
`{f_i : U_i → U}` of schemes, hypothesis (a) makes `G = F|_{U_ét}` quasi-coherent, hypothesis
(b) makes the comparison maps along the `f_i` isomorphisms, and therefore the sheaf condition
for `F` and `{x_i → x}` *is* the sheaf condition for `G^a` on `(Sch/U)_{fppf}` and
`{U_i → U}` — which is Descent, **Stacks 03DT**.

This file proves the reduction to such families and carries that one step as an explicit
hypothesis; see "What is carried, and why" below for what the step still needs and what it does
not.

## Main definitions

* `AlgebraicGeometry.Stack.flatLfpPrecoverage`: the covering families of the inherited fppf site
  whose members lie over a flat morphism of schemes locally of finite presentation — the
  coverings `{x_i → x}` of `𝒳` lying over an fppf covering of schemes.
* `AlgebraicGeometry.Stack.HasFlatLfpBaseChangeProperty`: hypothesis (b) of Stacks 076T.
* `AlgebraicGeometry.Stack.IsSheafForLiftedFppfFamily`: the step of the proof of Stacks 076T
  this file reduces the lemma to. It is reduced further to a single composition compatibility,
  `AlgebraicGeometry.Stack.LiftedSectionsCocycle`, in
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedFppfFamilySheafCondition`, and
  proved in
  `StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFlatBaseChangeProved`.

## Main results

* `AlgebraicGeometry.Stack.generates_flatLfpPrecoverage`: **the coverings lying over an fppf
  covering of schemes generate the inherited fppf topology.**
* `AlgebraicGeometry.Stack.isSheaf_of_isSheafFor_flatLfp`: **the fppf sheaf condition on the
  inherited site may be tested on the families lying over an fppf covering of schemes.**
* `AlgebraicGeometry.Stack.hasFlatLfpBaseChangeProperty_of_hasFlatBaseChangeProperty`: the flat
  base change property of Stacks 0762 implies hypothesis (b).
* `AlgebraicGeometry.Stack.hasFlatLfpBaseChangeProperty_of_iso`: hypothesis (b) only depends on
  the isomorphism class of the module.
* `AlgebraicGeometry.Stack.isSheafFor_of_isLocallyQuasicoherent`: for a locally quasi-coherent
  module the sheaf condition along a family generating an *étale* covering sieve is free, so the
  step this file reduces to is only about the families which cover for the fppf topology alone.
* `AlgebraicGeometry.Stack.isSheafForLiftedFppfFamily_of_imp`: that step is *implied by* the
  statement of Stacks 076T, so it asserts neither more nor less than the one step of the
  source's proof it stands for.

## The step this file reduces to

`AlgebraicGeometry.Stack.IsSheafForLiftedFppfFamily` is the sheaf condition, for a module
satisfying (a) and (b), along a family of arrows of `𝒳` lying over an fppf covering of schemes.
Together with `AlgebraicGeometry.Stack.isSheaf_of_isSheafFor_flatLfp` it is equivalent to the
conclusion of Stacks 076T — that is the content of
`AlgebraicGeometry.Stack.isSheafForLiftedFppfFamily_of_imp` — so it is exactly the source's one
step and nothing more, and what is proved here is the reduction to it.  It is proved, and Stacks
076T with it, in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfSheafFlatBaseChangeProved`.

Four inputs go into that step. The first three are available directly; the fourth — the
identification of the two sheaf conditions — is built in
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.LiftedFppfFamilySheafCondition` and
`StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.PullbackCompatibleTransport` over one
further compatibility, `AlgebraicGeometry.Stack.LiftedSectionsCocycle`, described at the end of
this section.

Descent, **Stacks 03DT** — the sheaf condition for the pullback-sections presheaf of a
quasi-coherent module — *is* available, unconditionally, on the big fppf site of a scheme:
`AlgebraicGeometry.BigFppfOver.isSheaf_sectionsPresheafOfModules_baseOverTopology`. So is the
identification of the fppf site of `𝒳` localized at `x` with the big fppf site of the scheme
below `x`, by the localization equivalence of **Stacks 06W0**
(`AlgebraicGeometry.Stack.isEquivalence_overPost`) together with
`AlgebraicGeometry.Stack.inducedTopology_overPost`.

So is the passage from `G = F|_{U_ét}`, which local quasi-coherence gives as a module
quasi-coherent *on the small étale site* in the sense of Stacks 03DL, to the quasi-coherent
`𝒪_U`-module that `G^a` is formed from. That is the essential-surjectivity half of Descent,
**Stacks 03DX**, at `τ = étale` and on the *small* étale site, and it is proved here with no
hypothesis, as `AlgebraicGeometry.SmallEtale.quasicoherentIsEssImageAssociatedModule`. (The
hypothesis `AlgebraicGeometry.BigFppfOver.QuasicoherentIsEssImageAssociatedModule` that this
repository does carry everywhere is Stacks 03DX on the *big* fppf site, which this step does not
use.) `AlgebraicGeometry.Stack.exists_isSheaf_sectionsPresheafOfModules_of_isLocallyQuasicoherent`
puts that passage and Stacks 03DT together: at every object of `𝒳` the `G^a` of the source's
proof exists and is an fppf sheaf.

The fourth input is the identification of the two sheaf conditions, that is of the sections of
`F` over the lifted family with the sections of `G^a` over the family downstairs — the word
"equivalent" in the source's proof. `AlgebraicGeometry.Stack.liftedSectionsIso` is that
identification at one arrow, as a five-factor composite, and
`AlgebraicGeometry.Stack.overPostSectionsIso_naturality` is its naturality over the slice.

The factors of that identification are available, none of them carrying a hypothesis:

* the *site* half, `AlgebraicGeometry.Stack.isSheafFor_iff_overPost` (and its family form
  `AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_overPost`): the sheaf condition for a presieve
  on `x` and the sheaf condition downstairs for the presieve of its images agree, once the two
  presheaves have been identified on the slice `𝒳/x`;
* the *base-change* half, `AlgebraicGeometry.Stack.associatedModuleSmallEtaleBaseChangeIso` and
  `AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso`: the sheafified
  Stacks 06WC pullback of `𝓕^a` along an arrow is `(a^*𝓕)^a`;
* the *global-sections* half, `AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso` and
  `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFinalIso`: `Γ(U_ét, F|_{U_ét}) = F(x)`.
  `AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso_inv` identifies that isomorphism's
  inverse with the canonical evaluation map of the Stacks 06W1 restriction, which is what makes
  it composable with the comparison maps;
* and `AlgebraicGeometry.SmallEtale.associatedModuleIsoSectionsPresheaf`, which reads `𝓕^a` as
  the Stacks 03DS pullback-sections presheaf that `G^a` downstairs is built from — with the
  sheafification *stripped*, that presheaf already being a sheaf on the small étale site. So this
  end of the chain crosses no sheafification coherence.

The *equalizer reduction* is also done, and unconditionally. The identification above exists only
along arrows lying over a flat morphism locally of finite presentation, since that is all
hypothesis (b) speaks about, whereas `CategoryTheory.Presieve.IsSheafFor` — and the hypothesis
`e` of `AlgebraicGeometry.Stack.isSheafFor_iff_overPost` — range over *every* object of the
slice. `AlgebraicGeometry.Stack.isSheafFor_ofArrows_iff_pullbackCompatible_overPostTransport`
cuts the condition down to the members of the covering and their fibre products, taken downstairs
where fibre products exist (`AlgebraicGeometry.hasPullbacks_bigFppfOver`), and
`AlgebraicGeometry.Stack.flat_hom_pullback_overPost` and
`AlgebraicGeometry.Stack.locallyOfFinitePresentation_hom_pullback_overPost` certify that every
object it quantifies over lies over a flat morphism locally of finite presentation. So hypothesis
(b) reaches all of them, and the slice-wide isomorphism — which is clause (b) of Stacks 06WK, and
is *strictly stronger* than what 076T assumes — is never needed.
`CategoryTheory.Presieve.Arrows.isSheafFor_ofArrows_of_maps` transports the sheaf condition
across that reduction given a bijection over the base, an injection over each member and a bare
function over each fibre product, with fibre products as `CategoryTheory.IsPullback` data.

What remains is the *cocycle*: the composite has to be natural in the arrow, so that it is a map
of equalizer diagrams and not several unrelated bijections. Two of the factors supply their own
composition law already — for the comparison map of Stacks 06WC that is Stacks 075D (1), as
`AlgebraicGeometry.Stack.smallEtaleStructureComparison_app_comp`,
`AlgebraicGeometry.Stack.restrictModulePushforwardComparison_app_comp` and
`AlgebraicGeometry.Stack.restrictionPushforwardComparison_app_eval_comp`; the final-object factor
against those comparison maps is
`AlgebraicGeometry.Stack.restrictToSmallEtaleFinalIso_inv_comp_comparison`; and the naturality
half of the sections factor is
`AlgebraicGeometry.SmallEtale.associatedModulePresheafIso_hom_naturality`.

`AlgebraicGeometry.Stack.LiftedSectionsCocycle` is what is left. It is *not* an isomorphism of
functors but an equality of two composites of maps on sections, over a composable pair of arrows,
with hypothesis (b) supplied explicitly at each of the two arrows separately; it is consumed in
exactly one place, `AlgebraicGeometry.Stack.overPostSectionsIso_naturality`. Discharging it needs
a composition compatibility from each of the two factors that do not yet have one: from
`AlgebraicGeometry.Stack.associatedModuleObjSmallEtaleBaseChangeIso`, and from
`Stacks.Sites.quasiCoherentPresheafBaseChangeIso` together with its source
`Stacks.Sites.pullbackSectionsBaseChangeIso` — those two are natural in the slice argument, but
nothing yet relates the isomorphism for `g : W ⟶ U` at `Over.mk k` to the one for `k ≫ g` at
`Over.mk (𝟙 _)`.

The gap is not about hypothesis (b), which is used here in full: the members of a family in
`AlgebraicGeometry.Stack.flatLfpPrecoverage` do lie over flat morphisms locally of finite
presentation, and that is what `AlgebraicGeometry.Stack.generates_flatLfpPrecoverage` is for.

## Implementation notes

Hypothesis (b) is stated for an arbitrary topology `τ` on the underlying category of schemes
coarser than the fppf one, as Stacks 0762 is; the module universe is fixed to the universe of
the schemes wherever the comparison map appears, for the reason recorded in the implementation
notes of `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtaleModuleComparison.lean`.
Local quasi-coherence names the étale topology, so that is the instance Stacks 076T is stated
at.

Flatness and local finite presentation of the morphism below an arrow are read off the morphism
of schemes `B.inclusion.map (p.map φ).left`, as in
`AlgebraicGeometry.Stack.HasFlatBaseChangeProperty`. For a member of a family of
`AlgebraicGeometry.Stack.flatLfpPrecoverage` they come from membership of the family of images
in `AlgebraicGeometry.Scheme.fppfPrecoverage`, whose morphism property is
`Flat ⊓ LocallyOfFinitePresentation`.

The testing criterion is the exact analogue, for a morphism condition, of
`AlgebraicGeometry.FibredSite.isSheaf_of_isSheafFor_affine`, which tests the same sheaf
condition on the families whose members have affine source; both are instances of
`CategoryTheory.Precoverage.generates_of_refines`, and the refinement input is
`AlgebraicGeometry.FibredSite.exists_fppf_ofArrows_le`.

## References

* [Stacks Project, Tag 076T](https://stacks.math.columbia.edu/tag/076T)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 03DT](https://stacks.math.columbia.edu/tag/03DT)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Opposite

universe u v w

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)

/-! ### Testing the fppf sheaf condition on the coverings that lie over an fppf covering -/

/-- The covering families of the inherited fppf site of Stacks 06TP whose members lie over a
morphism of schemes which is flat and locally of finite presentation.

These are the coverings `{x_i → x}` of `𝒳` lying over an fppf covering `{f_i : U_i → U}` of
schemes with which the source's arguments about the fppf topology on `𝒳` begin; being a covering
is asked of the sieve they generate, as in
`CategoryTheory.GrothendieckTopology.precoverageOfObjects`. -/
def flatLfpPrecoverage : Precoverage 𝒳 where
  coverings x := {R | Sieve.generate R ∈ associatedTopology B S hS p B.topology x ∧
    ∀ ⦃z : 𝒳⦄ (φ : z ⟶ x), R φ →
      Flat (B.inclusion.map (p.map φ).left) ∧
        LocallyOfFinitePresentation (B.inclusion.map (p.map φ).left)}

/-- Membership in `AlgebraicGeometry.Stack.flatLfpPrecoverage`, unfolded. -/
theorem mem_flatLfpPrecoverage_iff {x : 𝒳} (R : Presieve x) :
    R ∈ flatLfpPrecoverage B S hS p x ↔
      Sieve.generate R ∈ associatedTopology B S hS p B.topology x ∧
        ∀ ⦃z : 𝒳⦄ (φ : z ⟶ x), R φ →
          Flat (B.inclusion.map (p.map φ).left) ∧
            LocallyOfFinitePresentation (B.inclusion.map (p.map φ).left) :=
  Iff.rfl

include hp in
/-- **Every covering sieve of the inherited fppf site contains a covering family lying over an
fppf covering of schemes.**

`AlgebraicGeometry.FibredSite.exists_fppf_ofArrows_le` produces a family of arrows of the sieve
whose family of images in schemes is an fppf covering family; the members of such a family are
flat and locally of finite presentation because that is the morphism property of
`AlgebraicGeometry.Scheme.fppfPrecoverage`, and the family generates a covering sieve again by
`AlgebraicGeometry.FibredSite.ofArrows_mem_associatedTopology`. -/
theorem exists_flatLfp_le {x : 𝒳} (T : Sieve x)
    (hT : T ∈ associatedTopology B S hS p B.topology x) :
    ∃ R ∈ flatLfpPrecoverage B S hS p x, R ≤ T.arrows := by
  obtain ⟨I, z, φ, hle, hfppf⟩ := FibredSite.exists_fppf_ofArrows_le B S hS p hp hT
  have hmem := ((Scheme.ofArrows_mem_precoverage_iff
    (P := @Flat ⊓ @LocallyOfFinitePresentation)).1 hfppf).2
  refine ⟨Presieve.ofArrows z φ, ⟨?_, ?_⟩, ?_⟩
  · exact FibredSite.ofArrows_mem_associatedTopology B S hS p hp z φ
      (BigFppfOver.ofArrows_mem_baseOverTopology B S hS _ _ hfppf)
  · rintro _ _ ⟨i⟩
    exact ⟨(hmem i).1, (hmem i).2⟩
  · rintro _ _ ⟨i⟩
    exact hle i

include hp in
/-- **The coverings lying over an fppf covering of schemes generate the inherited fppf
topology.** -/
theorem generates_flatLfpPrecoverage :
    (flatLfpPrecoverage B S hS p).Generates (associatedTopology B S hS p B.topology) :=
  Precoverage.generates_of_refines _ _ (fun _ _ hR => hR.1)
    fun {_} T hT => exists_flatLfp_le B S hS p hp T hT

variable {A : Type*} [Category* A]

include hp in
/-- **A presheaf on the inherited fppf site which satisfies the sheaf condition for the covering
families lying over an fppf covering of schemes is a sheaf.**

This is the first step of the proof of Stacks 076T: it is what lets the sheaf condition be
checked only for the coverings `{x_i → x}` of `𝒳` lying over an fppf covering of schemes, the
coverings hypothesis (b) of that lemma speaks about. It is the analogue for a condition on the
morphisms of the family of `AlgebraicGeometry.FibredSite.isSheaf_of_isSheafFor_affine`, which is
the same statement for a condition on their sources. -/
theorem isSheaf_of_isSheafFor_flatLfp (F : 𝒳ᵒᵖ ⥤ A)
    (hF : ∀ ⦃x : 𝒳⦄ (R : Presieve x),
      Sieve.generate R ∈ associatedTopology B S hS p B.topology x →
      (∀ ⦃z : 𝒳⦄ (φ : z ⟶ x), R φ → Flat (B.inclusion.map (p.map φ).left) ∧
        LocallyOfFinitePresentation (B.inclusion.map (p.map φ).left)) →
      ∀ M : A, Presieve.IsSheafFor (F ⋙ coyoneda.obj (op M)) R) :
    Presheaf.IsSheaf (associatedTopology B S hS p B.topology) F :=
  (generates_flatLfpPrecoverage B S hS p hp).isSheaf_iff.2 fun {_} R hR M => hF R hR.1 hR.2 M

/-! ### Hypothesis (b) of Stacks 076T -/

/-- **Hypothesis (b) of Stacks 076T.** A presheaf of modules over the structure sheaf of a
category fibred in groupoids has *flat base change along the morphisms of an fppf covering* when
the comparison map `c_φ` of Stacks 06WC is an isomorphism for every arrow `φ` of `𝒳` lying over
a morphism of schemes which is flat and locally of finite presentation.

Both conditions on the morphism are those of the source and neither may be dropped. Asking the
isomorphism of every arrow lying over a flat morphism, local finite presentation or not, is the
flat base change property of Stacks 0762 — a strictly stronger hypothesis on the module, and not
the one Stacks 076T makes. What this condition covers is exactly the arrows of `𝒳` lying over a
member of an fppf covering of schemes, which is all the proof of Stacks 076T looks at. -/
noncomputable abbrev HasFlatLfpBaseChangeProperty (τ : GrothendieckTopology B.Schemes)
    (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj) : Prop :=
  ∀ {x y : 𝒳} (φ : x ⟶ y), Flat (B.inclusion.map (p.map φ).left) →
    LocallyOfFinitePresentation (B.inclusion.map (p.map φ).left) →
      IsIso (restrictModulePullbackComparison B E h S hS p hp φ τ hτ F)

/-- The flat base change property of **Stacks 0762** implies hypothesis (b) of Stacks 076T: it
asks for the same isomorphism along every arrow lying over a flat morphism, whether or not the
morphism is locally of finite presentation. -/
theorem hasFlatLfpBaseChangeProperty_of_hasFlatBaseChangeProperty
    (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj)
    (hF : HasFlatBaseChangeProperty B E h S hS p hp τ hτ F) :
    HasFlatLfpBaseChangeProperty B E h S hS p hp τ hτ F :=
  fun φ hflat _ => hF φ hflat

/-- Hypothesis (b) of Stacks 076T transports along an isomorphism of presheaves of modules. -/
theorem hasFlatLfpBaseChangeProperty_of_iso (τ : GrothendieckTopology B.Schemes)
    (hτ : τ ≤ B.topology)
    {F F' : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj} (e : F ≅ F')
    (hF : HasFlatLfpBaseChangeProperty B E h S hS p hp τ hτ F) :
    HasFlatLfpBaseChangeProperty B E h S hS p hp τ hτ F' :=
  fun ψ hflat hlfp =>
    isIso_restrictModulePullbackComparison_of_iso B E h S hS p hp τ hτ e ψ (hF ψ hflat hlfp)

/-! ### Stacks 076T -/

/-- For a locally quasi-coherent presheaf of modules the sheaf condition along a family of arrows
is free whenever the sieve the family generates covers for the inherited *étale* topology: local
quasi-coherence carries the étale sheaf condition, and the sheaf condition for a presieve is the
sheaf condition for the sieve it generates.

This locates the content of the step of Stacks 076T which is carried below: nothing has to be
assumed about the families which already cover étale-locally, only about those which cover for
the fppf topology alone. -/
theorem isSheafFor_of_isLocallyQuasicoherent
    (F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj)
    (hlqc : IsLocallyQuasicoherent B E h S hS p hp F) {x : 𝒳} (R : Presieve x)
    (hR : Sieve.generate R ∈ associatedTopology B S hS p (etaleTopology B) x)
    (M : AddCommGrpCat.{u}) :
    Presieve.IsSheafFor (F.presheaf ⋙ coyoneda.obj (op M)) R :=
  (Presieve.isSheafFor_iff_generate R).2 (hlqc.1 M _ hR)

/-- **The step of the proof of Stacks 076T this development does not have.** For a presheaf of
modules satisfying hypotheses (a) and (b) of Stacks 076T, the sheaf condition holds along every
family of arrows of `𝒳` which generates a covering sieve of the inherited fppf topology and lies
over an fppf covering of schemes.

This is the source's single step: the restriction `G = F|_{U_ét}` is quasi-coherent by (a), the
comparison maps along the members of the family are isomorphisms by (b), and the sheaf condition
for the family therefore *is* the sheaf condition for `G^a` on `(Sch/U)_{fppf}` and the covering
downstairs, which is Descent, Stacks 03DT. The inputs of that step, and which of them are
available here, are discussed in the implementation notes of this file; everything but the
identification of the two sheaf conditions is available, and
`AlgebraicGeometry.Stack.exists_isSheaf_sectionsPresheafOfModules_of_isLocallyQuasicoherent`
produces the `G^a` of the source's proof, together with its fppf sheaf condition, at every
object of `𝒳`. -/
abbrev IsSheafForLiftedFppfFamily : Prop :=
  ∀ F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B)).obj,
    IsLocallyQuasicoherent B E h S hS p hp F →
    HasFlatLfpBaseChangeProperty B E h S hS p hp (etaleTopology B)
      (etaleTopology_le_topology B) F →
    ∀ ⦃x : 𝒳⦄ (R : Presieve x),
      Sieve.generate R ∈ associatedTopology B S hS p B.topology x →
      (∀ ⦃z : 𝒳⦄ (φ : z ⟶ x), R φ → Flat (B.inclusion.map (p.map φ).left) ∧
        LocallyOfFinitePresentation (B.inclusion.map (p.map φ).left)) →
      ∀ M : AddCommGrpCat.{u}, Presieve.IsSheafFor (F.presheaf ⋙ coyoneda.obj (op M)) R

/-- `AlgebraicGeometry.Stack.IsSheafForLiftedFppfFamily` is *implied by* the statement of Stacks
076T: a module which is a sheaf for the fppf topology satisfies the sheaf condition for every
presieve generating a covering sieve. So that step asserts neither more nor less than the lemma,
and what this file adds to it is the reduction of the sheaf condition to the families lying over
an fppf covering of schemes.  The step itself, and Stacks 076T with it, is proved in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FppfSheafFlatBaseChangeProved.lean`. -/
theorem isSheafForLiftedFppfFamily_of_imp
    (hstm : ∀ F : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B)).obj,
      IsLocallyQuasicoherent B E h S hS p hp F →
      HasFlatLfpBaseChangeProperty B E h S hS p hp (etaleTopology B)
        (etaleTopology_le_topology B) F →
      Presheaf.IsSheaf (associatedTopology B S hS p B.topology) F.presheaf) :
    IsSheafForLiftedFppfFamily B E h S hS p hp := by
  intro F hlqc hbc x R hR _ M
  exact (Presieve.isSheafFor_iff_generate R).2 (hstm F hlqc hbc M _ hR)

end AlgebraicGeometry.Stack

end
