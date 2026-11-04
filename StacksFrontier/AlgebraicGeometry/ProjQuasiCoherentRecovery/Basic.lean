module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionComparison
public import StacksFrontier.AlgebraicGeometry.ProjTwistDegreeOneCover.GlobalSections

/-!
# Recovering a quasi-coherent sheaf on `Proj` from its twisted global sections

Let `S` be a graded ring, `X = Proj S`, and let `ℱ` be a sheaf of `𝒪_X`-modules.  The twisted
global sections `M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` form a graded `S`-module (Tag 03GK), so they have an
associated sheaf `M̃`, and Tag 0B5I produces a comparison morphism `M̃ ⟶ ℱ`.  Tag 0AG5 asserts
two things about it when `X` is quasi-compact and `ℱ` is quasi-coherent:

* the comparison `M̃ ⟶ ℱ` is an **isomorphism**;
* if moreover `X` is covered by the standard opens `D₊(f)` of the degree-one elements, the
  induced maps `M_n → Γ(X, ℱ(n))` are the **identity** maps.

Both are stated here, each at the source's own conclusion, and each taking as an input one
*local* half of the source's own proof; see *What is carried, and why* below.

**The tag itself is not attached in this file.**  Both of its assertions are proved with no input
at all — the canonically constructed comparison of Tag 0B5I, `Proj S` quasi-compact, `ℱ`
quasi-coherent, and for the second assertion the degree-one covering hypothesis — in
`StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/ProjTwistComparisonCompact.lean`, which
carries the attributes: the first is
`Stacks.AlgebraicGeometry.ProjTwistComparisonCompact.isIso_integerComparison`, which consumes
`isIso_of_bijective_app_onBasis` below as its globalization step, and the second is
`Stacks.AlgebraicGeometry.ProjTwistComparisonCompact`
`.twistSheafMap_integerComparison_degreeNToTwistedGlobalSections`, whose local identity — the one
the source omits — is proved there on the standard opens of the degree-one elements.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery.twistedComparison`: the `n`-th twist
  `M̃(n) ⟶ ℱ(n)` of the comparison morphism, namely the comparison tensored with the identity
  of `𝒪_X(n)`.
* `Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery.ofTwistedSection`: a global section of
  `ℱ(n)` read as a homogeneous element of degree `n` of `M`.  This is the identification
  `M_n = Γ(X, ℱ(n))` under which the source's last assertion is an assertion about the
  *identity* map.

## Main results

* `Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery.isIso_of_bijective_app_onBasis`: **a
  morphism of sheaves of modules whose components on the members of a basis are bijective is an
  isomorphism.**  This is proved here in full: the inverses of the components are compatible
  with the restriction maps, so Tag 009U glues them into a morphism, and that morphism is a
  two-sided inverse because it is one on the basis.  No `stacks` attribute: it is a general
  sheaf-theoretic statement, not part of the tag.
* `Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery.isIso_comparison`: **Tag 0AG5's first
  assertion**, that the comparison `M̃ ⟶ ℱ` is an isomorphism.
* `Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery`
  `.twistedComparison_degreeNToTwistedGlobalSections`: the local-to-global step of Tag 0AG5's
  second assertion at an *arbitrary* family of local maps — an identity of sections over `X`
  that holds after restriction to every positive-degree standard open holds over `X`.  The
  assertion itself, for the canonical comparison of Tag 0B5I, is proved with nothing
  hypothesised in `StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/ProjTwistComparisonCompact.lean`; see the note above.

## What is carried, and why

The comparison morphism of Tag 0B5I is not canonically constructed in this repository:
`Stacks.AlgebraicGeometry.ProjTwistComparison.comparison` takes the local maps `θ` on the
positive-degree standard opens, and their compatibility `hθ`, as hypotheses, for the reason
recorded in the module docstring of
`StacksFrontier/AlgebraicGeometry/Constructions/ProjTwistSectionComparison.lean`.  Every statement
below therefore quantifies over `θ` and `hθ` as well, exactly as the statements of Tag 0B5I do.

Beyond that, each assertion carries one further hypothesis, and each is the *local* half of the
source's own proof:

* `isIso_comparison` carries `hloc`, the bijectivity of each local map `θ p`. The source gets this
  from the chain `M_{(f)} = Γ_*(X, 𝓛, ℱ)_{(s)} → Γ(X_s, ℱ)` of Properties, Lemma 01PW, for a cover
  by standard opens of a common degree `d` obtained from quasi-compactness. Both halves of Tag 01PW
  are available: the second is `Stacks.SheafOfModules.sectionLocalizationMap_bijective` in
  `StacksFrontier/AlgebraicGeometry/Properties/PrincipalOpens/GradedSectionInjective.lean`, read on a
  chart of `Proj 𝒮` by `bijective_sectionLocalizationMap_degreeSection` in the namespace
  `Stacks.AlgebraicGeometry.ProjChartNonvanishingOpen`. The *first* equality of that chain, the
  identification of `M_{(f)}` with `Γ_*(X, 𝓛, ℱ)_{(s)}`, is reduced to a degreewise comparison of
  the two graded modules by
  `Stacks.AlgebraicGeometry.ProjTwistLocalComparison.bijective_chartHom_of_degreewise`, and no
  declaration supplies that comparison. That is not why `hloc` is carried here. The local
  bijectivity *is* available, for the ℕ-graded module of [Stacks, Tag 03GM] and without any
  comparison of graded modules, as
  `Stacks.AlgebraicGeometry.ProjTwistChartBijective.bijective_chartHom_of_cover`. What it does not
  cover is the generality of the statements here: `hloc` below is asked of an *arbitrary* family
  `θ` of local maps, since the comparison morphism of Tag 0B5I is not canonically constructed in
  this repository, and it is asked for the ℤ-graded module of Tag 0B5I rather than the ℕ-graded
  module of Tag 03GM. For the canonical comparison of the ℕ-graded module on `ℙᵐ_R` the hypothesis
  is discharged, by
  `Stacks.AlgebraicGeometry.ProjTwistComparisonIso.gradedModule_and_isIso_comparison`. What *is*
  proved here is the remaining step of the source's proof — "hence an isomorphism as `X` is covered
  by these opens" — namely `isIso_of_bijective_app_onBasis`. Note that this step asks for
  bijectivity on a **basis** of `X`, that is at every positive-degree homogeneous element, and not
  merely on a cover.
* `twistedComparison_degreeNToTwistedGlobalSections` carries `hloc`, the same identity after
  restriction to each positive-degree standard open.  The source omits the proof of this
  assertion outright ("We omit the proof of the final statement"), and what is proved here is
  the local-to-global step: an identity between sections over `X` that holds after restriction
  to every member of a basis holds over `X`.  This is the same shape, and for the same reason,
  as `Stacks.AlgebraicGeometry.ProjTwistComparison.comparison_degreeZeroToGlobalSections`,
  which carries the degree-zero case of the same local datum.  **The assertion itself is not
  conditional in this repository**: for the canonical comparison of Tag 0B5I the local identity
  is proved on the standard opens of the *degree-one* elements — which the tag's own hypothesis
  makes a cover — by
  `Stacks.AlgebraicGeometry.ProjTwistComparisonCompact`
  `.twistSheafMap_integerComparison_degreeNToTwistedGlobalSections`.
  What is carried here is the basis-indexed `hloc` of the general statement, which is asked at
  *every* positive-degree element and not only on that cover.

The source's own hypotheses are kept in the signature of `isIso_comparison` — quasi-compactness
of `Proj S` and quasi-coherence of `ℱ` — even though the proof does not use them: they are the
hypotheses from which the source derives the carried `hloc`, and dropping them would state a
different lemma.  The binder for quasi-compactness is named `_hqc` to record that it is not
used.  By contrast the degree-one covering hypothesis of the second assertion *is* used: the
map `M_n → Γ(X, M̃(n))` of Tag 0AG3 is not even defined without it.

## References

* [Stacks Project, Tag 0AG5](https://stacks.math.columbia.edu/tag/0AG5)
* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 0AG3](https://stacks.math.columbia.edu/tag/0AG3)
* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
* [Stacks Project, Tag 01PW](https://stacks.math.columbia.edu/tag/01PW)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj
  (associatedModuleSheaf twistingSheaf twistSheafOfModules)
open Stacks.AlgebraicGeometry.ProjTwistedSections
  (TwistedGlobalSectionsModule twistedGlobalSectionsGrading twistedGlobalSectionsAssociatedSheaf
    twistedSectionsComponent)
open Stacks.AlgebraicGeometry.ProjTwistComparison
  (PositiveElem positiveBasicOpen isBasis_positiveBasicOpen comparison comparison_app)
open Stacks.AlgebraicGeometry.ProjTwistDegreeOneCover
  (DegreeOneCover degreeNToTwistedGlobalSections)
open Stacks.SheafOfModules.TensorStalkRingedSpace

namespace Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery

universe u w

attribute [local instance_reducible] ProjectiveSpectrum.top TopCat.Sheaf
attribute [local implicit_reducible] sheafCompose PresheafOfModules.presheaf
  SheafOfModules.toSheaf

section Globalization

variable {X : TopCat.{u}} {𝒪 : TopCat.Sheaf RingCat.{u} X}

/-- **A morphism of sheaves of modules whose components on the members of a basis are bijective
is an isomorphism.**

The inverses of the components are compatible with the restriction maps between the members of
the basis, because the components are; so Tag 009U glues them into a morphism in the opposite
direction, and that morphism is a two-sided inverse because its composites with the given one
agree with the identity on every member of the basis, where morphisms of sheaves of modules are
determined. -/
public theorem isIso_of_bijective_app_onBasis (F G : SheafOfModules.{u} 𝒪)
    {ι : Type*} (U : ι → Opens X) (hU : Opens.IsBasis (Set.range U)) (φ : F ⟶ G)
    (hbij : ∀ a, Function.Bijective (φ.val.app (op (U a))).hom) : IsIso φ := by
  let i : ∀ a, F.val.obj (op (U a)) ≅ G.val.obj (op (U a)) := fun a =>
    @asIso _ _ _ _ (φ.val.app (op (U a))) ((ConcreteCategory.isIso_iff_bijective _).mpr (hbij a))
  have hcomp : Stacks.BasisRestriction.IsCompatibleOnBasis G F U (fun a => (i a).inv) := by
    intro a b h t
    exact (congrArg (fun y => (i b).inv y)
      ((PresheafOfModules.naturality_apply φ.val (homOfLE h).op ((i a).inv t)).trans
        (congrArg (fun y => (G.val.map (homOfLE h).op) y)
          (ModuleCat.hom_inv_apply (i a) t)))).symm.trans (ModuleCat.inv_hom_apply (i b) _)
  refine ⟨Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis G F U
    (fun a => (i a).inv) hU hcomp, ?_, ?_⟩ <;>
  refine Stacks.BasisRestriction.moduleSheafHom_ext_onBasis _ _ U hU _ _ fun a => ?_ <;>
  rw [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app G F U
      (fun a => (i a).inv) hU hcomp a,
    SheafOfModules.id_val, PresheafOfModules.id_app]
  exacts [(i a).hom_inv_id, (i a).inv_hom_id]

end Globalization

section Comparison

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]
  (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))
  (D : TwistedGlobalSectionsModule 𝒮 F)

/-- **Tag 0AG5, first assertion: the comparison `M̃ ⟶ ℱ` is an isomorphism.**

Here `M = ⨁_{n ∈ ℤ} Γ(Proj 𝒮, ℱ(n))` carries the graded `S`-module structure `D` of Tag 03GK,
`M̃` is its associated sheaf, and the comparison is the morphism of Tag 0B5I glued from the
local maps `θ` on the positive-degree standard opens.

The hypothesis `hloc`, that each local map is bijective, is carried: it is what the source
derives from quasi-compactness and quasi-coherence through Properties, Lemma 01PW, which this
repository does not have in the applicable form.  The source's own hypotheses are retained —
`_hqc`, quasi-compactness of `Proj S`, and quasi-coherence of `ℱ` — and neither is used by the
proof, whose content is the globalization step `isIso_of_bijective_app_onBasis`.

No `stacks` attribute.  Tag 0AG5 is proved with no local input at all, for the canonically
constructed comparison morphism of Tag 0B5I and at the source's own two hypotheses, by
`Stacks.AlgebraicGeometry.ProjTwistComparisonCompact.isIso_integerComparison`
(`StacksFrontier/AlgebraicGeometry/TensorSectionNonvanishing/ProjTwistComparisonCompact.lean`).
What is left here is the globalization step at an *arbitrary* family of local maps, which is
what the conditional statements of Tag 0B5I consume. -/
public theorem isIso_comparison
    (_hqc : CompactSpace (ProjectiveSpectrum.top 𝒮))
    [F.IsQuasicoherent]
    (θ : ∀ p : PositiveElem 𝒮,
      (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
        F.val.obj (op (positiveBasicOpen 𝒮 p)))
    (hθ : ∀ (p q : PositiveElem 𝒮)
        (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
        (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj
          (op (positiveBasicOpen 𝒮 p))),
      θ q ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE h).op s) =
        F.val.map (homOfLE h).op (θ p s))
    (hloc : ∀ p : PositiveElem 𝒮, Function.Bijective (θ p).hom) :
    IsIso (comparison 𝒮 F D θ hθ) := by
  refine isIso_of_bijective_app_onBasis _ F (positiveBasicOpen 𝒮)
    (isBasis_positiveBasicOpen 𝒮) _ fun p => ?_
  rw [comparison_app 𝒮 F D θ hθ p]
  exact hloc p

/-- **The `n`-th twist `M̃(n) ⟶ ℱ(n)` of the comparison morphism**: the comparison of Tag 0B5I
tensored with the identity of the twisting sheaf `𝒪_X(n)`.  Taking global sections of this is
the second map in the composite `M_n → Γ(X, M̃(n)) → Γ(X, ℱ(n))` whose identity the source's
last assertion is about. -/
public noncomputable def twistedComparison
    (θ : ∀ p : PositiveElem 𝒮,
      (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
        F.val.obj (op (positiveBasicOpen 𝒮 p)))
    (hθ : ∀ (p q : PositiveElem 𝒮)
        (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
        (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj
          (op (positiveBasicOpen 𝒮 p))),
      θ q ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE h).op s) =
        F.val.map (homOfLE h).op (θ p s))
    (n : ℤ) :
    twistSheafOfModules 𝒮 (twistedGlobalSectionsAssociatedSheaf 𝒮 F D) n ⟶
      twistSheafOfModules 𝒮 F n :=
  (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      (ProjectiveSpectrum.Proj.structureSheaf 𝒮))).map
    (X := (twistedGlobalSectionsAssociatedSheaf 𝒮 F D, twistingSheaf 𝒮 n))
    (Y := (F, twistingSheaf 𝒮 n))
    (comparison 𝒮 F D θ hθ, 𝟙 (twistingSheaf 𝒮 n))

/-- **A global section of `ℱ(n)` read as a homogeneous element of degree `n` of `M`.**  The
degree-`n` piece of `M = ⨁_{m ∈ ℤ} Γ(X, ℱ(m))` is the range of the inclusion of the `n`-th
summand, so a section of `ℱ(n)` gives one, and this identification `Γ(X, ℱ(n)) = M_n` is what
makes the source's last assertion an assertion about the identity map. -/
public def ofTwistedSection (n : ℤ) (s : twistedSectionsComponent 𝒮 F n) :
    twistedGlobalSectionsGrading 𝒮 F n :=
  ⟨DirectSum.of (fun m : ℤ => twistedSectionsComponent 𝒮 F m) n s,
    ⟨s, DirectSum.lof_eq_of ℤ ℤ (fun m : ℤ => twistedSectionsComponent 𝒮 F m) n s⟩⟩

/-- **Tag 0AG5, second assertion: under the degree-one covering hypothesis the induced map
`M_n → Γ(X, ℱ(n))` is the identity.**

The induced map is the composite of Equation 0AG3, `M_n → Γ(X, M̃(n))`, with the global
sections of the `n`-th twist of the comparison; the source's assertion is that it is the
identity of `Γ(X, ℱ(n)) = M_n`.  The covering hypothesis `hcover` is load-bearing: Equation
0AG3 is not defined without it.

The hypothesis `hloc` — the same identity after restriction to each positive-degree standard
open — is carried.  The source omits the proof of this assertion; what is proved here is the
local-to-global step, that an identity of sections holding on a basis holds globally.

No `stacks` attribute.  The local datum `hloc` is an input here, so this statement does not
assert the tag's second clause; that clause, for the canonical comparison morphism of Tag 0B5I
and with nothing hypothesised, is
`Stacks.AlgebraicGeometry.ProjTwistComparisonCompact`
`.twistSheafMap_integerComparison_degreeNToTwistedGlobalSections`, which proves the local
identity on the standard opens of the degree-one elements and glues it over that cover rather
than over the whole basis. -/
public theorem twistedComparison_degreeNToTwistedGlobalSections
    (hcover : DegreeOneCover 𝒮)
    (θ : ∀ p : PositiveElem 𝒮,
      (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
        F.val.obj (op (positiveBasicOpen 𝒮 p)))
    (hθ : ∀ (p q : PositiveElem 𝒮)
        (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
        (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj
          (op (positiveBasicOpen 𝒮 p))),
      θ q ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE h).op s) =
        F.val.map (homOfLE h).op (θ p s))
    (n : ℤ) (s : twistedSectionsComponent 𝒮 F n)
    (hloc : letI := D.moduleInst; letI := D.gradedSMul
      ∀ (p : PositiveElem 𝒮) (hle : positiveBasicOpen 𝒮 p ≤ ⊤),
        (twistedComparison 𝒮 F D θ hθ n).val.app (op (positiveBasicOpen 𝒮 p))
            ((twistSheafOfModules 𝒮 (twistedGlobalSectionsAssociatedSheaf 𝒮 F D) n).val.map
              (homOfLE hle).op
              (degreeNToTwistedGlobalSections 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hcover n
                (ofTwistedSection 𝒮 F n s))) =
          (twistSheafOfModules 𝒮 F n).val.map (homOfLE hle).op s) :
    letI := D.moduleInst; letI := D.gradedSMul
    (twistedComparison 𝒮 F D θ hθ n).val.app (op ⊤)
        (degreeNToTwistedGlobalSections 𝒮 (twistedGlobalSectionsGrading 𝒮 F) hcover n
          (ofTwistedSection 𝒮 F n s)) = s :=
  Stacks.BasisRestriction.moduleSheafSection_ext_onBasis (twistSheafOfModules 𝒮 F n)
    (positiveBasicOpen 𝒮) (isBasis_positiveBasicOpen 𝒮) _ s fun p hle =>
      (PresheafOfModules.naturality_apply (twistedComparison 𝒮 F D θ hθ n).val
        (homOfLE hle).op _).symm.trans (hloc p hle)

end Comparison

end Stacks.AlgebraicGeometry.ProjQuasiCoherentRecovery

end
