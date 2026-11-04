module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleFunctorial
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjTwistSectionModuleGraded
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjVeroneseAssociatedSheaf
public import StacksFrontier.AlgebraicGeometry.ProjSheafFunctoriality.Basic
public import StacksFrontier.Topology.Sheaves.Basis.ModuleHomOnBasis

/-!
# The comparison map from the twisted global sections to a sheaf on `Proj`

Let `S = ⨁_{d ≥ 0} 𝒮 d` be a nonnegatively graded ring, `X = Proj 𝒮`, and let `ℱ` be a sheaf of
`𝒪_X`-modules. The twisted global sections

`M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))`

form a graded `S`-module
(`Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsModule`), so they have an
associated sheaf `M̃` on `X`
(`Stacks.AlgebraicGeometry.ProjTwistedSections.twistedGlobalSectionsAssociatedSheaf`). Tag 0B5I
asserts that there is a canonical morphism `M̃ ⟶ ℱ`, functorial in `ℱ` and inducing the identity
on `Γ(X, ℱ)` in degree zero.

This file supplies **the globalization step**, which the source omits. Tag 0B5I's proof
constructs the comparison only on the standard opens `D₊(f)` with `f` homogeneous of positive
degree, by sending the degree-zero fraction `m / f ^ k` to the restriction of `m` multiplied by
the inverse `k`-th power of the trivializing section `f`; the gluing of those local maps into a
morphism of sheaves, and the verification that the result is well defined, are stated there as
"the proof is omitted". The content here is exactly that omitted step, for `M̃` and for an
arbitrary sheaf of modules in place of `ℱ`: a family of maps on the sections over the
positive-degree standard opens, compatible with the restriction maps, extends to a *unique*
morphism of sheaves of modules, and any identity between the glued morphism's values can be
checked on those standard opens.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjTwistComparison.PositiveElem`: a homogeneous element of
  strictly positive degree, used to index the standard opens.
* `Stacks.AlgebraicGeometry.ProjTwistComparison.positiveBasicOpen`: the standard open it cuts
  out.
* `Stacks.AlgebraicGeometry.ProjTwistComparison.StandardOpenHomData`: a family of maps on the
  sections of `M̃` over the positive-degree standard opens, compatible with restriction — the
  local datum Tag 0B5I's proof produces.
* `Stacks.AlgebraicGeometry.ProjTwistComparison.homOfStandardOpenHomData`: the morphism of
  sheaves of modules it glues to, constructed by lifting the family along the restriction
  functor to the basis.
* `Stacks.AlgebraicGeometry.ProjTwistComparison.comparison`: **the comparison morphism
  `M̃ ⟶ ℱ` of Tag 0B5I**, built from such a datum for the twisted global sections.
* `Stacks.AlgebraicGeometry.ProjTwistComparison.twistedGlobalSectionsAssociatedSheafMap`: the
  morphism `M̃_ℰ ⟶ M̃_ℱ` of associated sheaves induced by a morphism `ℰ ⟶ ℱ`, in which the
  functoriality of the comparison is phrased.

## Main results

* `Stacks.AlgebraicGeometry.ProjTwistComparison.isBasis_positiveBasicOpen`: the positive-degree
  standard opens form a basis of `Proj 𝒮`.
* `Stacks.AlgebraicGeometry.ProjTwistComparison.existsUnique_hom_of_standardOpenHomData`: the
  gluing principle, in the general form for the sheaf associated to any graded module and any
  sheaf of modules as target: the glued morphism is the unique one with the given values.
* `Stacks.AlgebraicGeometry.ProjTwistComparison.existsUnique_comparison`: **Tag 0B5I's
  comparison morphism**, with its uniqueness, from the standard-open data.
* `Stacks.AlgebraicGeometry.ProjTwistComparison.comparison_app` and
  `Stacks.AlgebraicGeometry.ProjTwistComparison.eq_comparison`: the comparison restricts to the
  given local maps, and is the only morphism that does.
* `Stacks.AlgebraicGeometry.ProjTwistComparison.comparison_app_eq_of_restrict`: a value of the
  comparison is pinned down by the standard-open data — the local-to-global step by which every
  assertion about the comparison is reduced to the standard opens.
* `Stacks.AlgebraicGeometry.ProjTwistComparison.comparison_degreeZeroToGlobalSections`: **the
  degree-zero normalization of Tag 0B5I**, from the degree-zero normalization of the local data.
* `Stacks.AlgebraicGeometry.ProjTwistComparison.comparison_naturality`: **the functoriality of
  Tag 0B5I's comparison in `ℱ`**, the commuting square attached to a morphism `ℰ ⟶ ℱ`, with
  `Stacks.AlgebraicGeometry.ProjTwistComparison.twistedGlobalSectionsAssociatedSheafMap_id` and
  `twistedGlobalSectionsAssociatedSheafMap_comp` the functoriality of `ℱ ↦ M̃_ℱ` that makes it a
  statement about a morphism of functors.
* `Stacks.AlgebraicGeometry.ProjTwistComparison.twistedSectionsMap_mem_grading`: the map induced
  on twisted global sections preserves the grading.

## What is carried, and why

The local maps are *hypotheses*, not constructions: the general statements take a
`StandardOpenHomData`, and the statements about the comparison take the maps `θ` together with
their compatibility `hθ`. Producing them is the other half of Tag 0B5I's proof. On `D₊(f)` with
`f ∈ 𝒮 d`, `d > 0`, the local map divides by the trivializing section, which asks for the
identification `Γ(W, ℱ(k d)) ≅ Γ(W, ℱ)` for every open `W ⊆ D₊(f)`. For the twisting sheaves
themselves that identification is Tag 01MS,
`Stacks.AlgebraicGeometry.ProjTrivialization.bijective_trivializingHom`.

**The reason this file gave for carrying `θ` is wrong, and the record is withdrawn.** It said
that for the twists of an *arbitrary* `ℱ` the identification is unavailable because
`ℱ(k d) = ℱ ⊗ 𝒪(k d)` and "the repository has no compatibility of the sheafified tensor product
with restriction to an open — nothing identifies `(ℱ ⊗ 𝒪(k d))|_W` with `ℱ|_W ⊗ 𝒪(k d)|_W`, so
the trivialization of the second factor cannot be tensored with the identity of `ℱ`". Both halves
are available, **at the very spelling used here**, which was checked rather than assumed:
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules` is
`Stacks.SheafOfModules.TensorSheafification.tensorSheaf` of `ℱ` with `twistingSheaf`, and

* `Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso` is `(ℱ ⊗ 𝒢)|_{C'} ≅ ℱ|_{C'} ⊗ 𝒢|_{C'}`
  for restriction along **any** continuous cocontinuous functor of sites, with
  `whiskerTensorSheafIso_hom` its characterizing equation on the sheafification unit of the
  objectwise tensor product — that is, its formula on local pure tensors;
* the open-image functor `Opens W ⥤ Opens (Proj 𝒮)` is such a functor, by
  `Stacks.SheafOfModules.TensorPower.openImageFunctor_isCocontinuous`, so the above applies to
  restriction to an open of `Proj 𝒮`;
* tensoring a trivialization with an identity is
  `Stacks.SheafOfModules.TensorPower.whiskerTensorSheafIso_naturality_right`, and the consequence
  wanted here is `Stacks.InverseSection.isIso_whiskerRestriction_map_tensorSectionHom`: **if
  `σ : 𝒪 ⟶ 𝒩` becomes an isomorphism after restriction, so does multiplication by `σ` on an
  arbitrary `ℱ`.**

So what producing `θ` still needs is not that compatibility. It is (i) Tag 01MS's trivialization
of `𝒪(k d)` on `D₊(f)` put in the shape `σ : 𝒪 ⟶ 𝒪(k d)` with `IsIso` of its restriction, which
is what the last result consumes, and (ii) the field `StandardOpenHomData.app_restrict`, the
compatibility between two standard opens — the step Tag 0B5I's own source calls omitted. The
unit and associativity laws for
`AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafMultiplicationMap` that this file also named
are still unavailable, and that record stands; it is simply no longer what the local maps are
blocked on, since the route above goes through the trivialization and not through the
multiplication map. The attributes below carry a clause naming what is assumed. Nothing here is
weakened by the
assumption: the local maps are quantified over, so the statements apply to whatever local
comparison that work produces, and the uniqueness clause then identifies the morphism it glues
to with the one the source calls canonical.

The remaining assertion of the tag, functoriality of the comparison in `ℱ`, is **not** covered.
It needs the degree-preserving map `⨁ₙ Γ(X, ℱ(n)) → ⨁ₙ Γ(X, 𝒢(n))` induced by a morphism
`ℱ ⟶ 𝒢`. **The reason given here for that being unavailable is likewise withdrawn:** the map
`ℱ(n) ⟶ 𝒢(n)` is `Stacks.SheafOfModules.TensorSheafification.tensorSheafMap` of `φ` with the
identity of `twistingSheaf 𝒮 n`, checked to elaborate at this spelling, and it needs no
compatibility of the tensor product with restriction at all. What functoriality still owes is
the degree-preserving linear map this assembles to and the naturality square for the glued
morphism, neither of which is stated here.

## Implementation notes

The gluing is not done by hand. The positive-degree standard opens are a basis
(`Stacks.Veronese.positiveBasicOpenSet_isBasis`), and
`Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis` builds a morphism of sheaves of
modules out of compatible section maps on a basis, by lifting them along the restriction functor
of Tag 009U, and `existsUnique_moduleSheafHom_of_sectionHom_onBasis` adds that it is the only
such morphism. So the only Proj-specific inputs are the basis statement and the indexing of the
basis by positive-degree homogeneous elements. Nothing here extracts a morphism from an
existence statement: `comparison` is a construction and the `∃!` statements are derived from
it.

The index type is the subtype `PositiveElem` rather than a pair `(f, d)` with `f ∈ 𝒮 d`: the
degree is existentially quantified, so two data differing only in the chosen degree are the same
datum, and the compatibility hypothesis — asked for every pair of indices with comparable opens,
including the reflexive case — already forces the maps attached to two elements with the same
standard open to agree.

The module structure on the twisted global sections is not an instance; it is the datum `D` of
`Stacks.AlgebraicGeometry.ProjTwistedSections.TwistedGlobalSectionsModule`. The statements about
the comparison are therefore phrased through `twistedGlobalSectionsAssociatedSheaf 𝒮 ℱ D`, which
already hides those instances, and they take the local maps as a bare family `θ` with a
compatibility hypothesis `hθ` rather than as a `StandardOpenHomData`: the structure's parameters
include the module structure, so a hypothesis of that type has to be written behind a `letI`, and
the projections `A.app` in the conclusion then no longer find the instances. Only the two places
that genuinely mention the module structure — `hs` and `h` of
`comparison_degreeZeroToGlobalSections` — are written behind a `letI`, exactly as the fields of
`TwistedGlobalSectionsModule` are.

The general gluing statement is given for a graded module whose carrier lies in the universe of
the ring. That is not a restriction for the use made of it — the twisted global sections are a
direct sum of groups of sections over `Proj 𝒮`, hence live in the ring's universe — and it is
forced by Tag 009U's restriction functor, which is stated for `SheafOfModules.{u}` on a space in
`TopCat.{u}`.

## References

* [Stacks Project, Tag 0B5I](https://stacks.math.columbia.edu/tag/0B5I)
* [Stacks Project, Tag 009U](https://stacks.math.columbia.edu/tag/009U)
* [Stacks Project, Tag 01M6](https://stacks.math.columbia.edu/tag/01M6)
* [Stacks Project, Tag 01M7](https://stacks.math.columbia.edu/tag/01M7)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace DirectSum
open AlgebraicGeometry.ProjectiveSpectrum.Proj (associatedModuleSheaf twistedGlobalSections)
open Stacks.AlgebraicGeometry.ProjSheafFunctoriality (associatedModuleSheafMap
  associatedModuleSheafMap_id associatedModuleSheafMap_comp)
open Stacks.AlgebraicGeometry.ProjStalkGlobalSections (degreeZeroToGlobalSections)
open Stacks.AlgebraicGeometry.ProjTwistedSections
  (TwistedGlobalSectionsModule twistedGlobalSectionsGrading
    twistedGlobalSectionsAssociatedSheaf twistedSectionsMap twistedSectionsMapComponent
    twistedSectionsLinearMap isTwistedSectionsSMul_twistedGlobalSectionsModule
    twistedSectionsMap_of twistedSectionsMap_id twistedSectionsMap_comp)
open scoped Stacks.GradedLocalization

namespace Stacks.AlgebraicGeometry.ProjTwistComparison

universe u w t

attribute [local instance] ProjectiveSpectrum.isPrime
attribute [local instance_reducible] ProjectiveSpectrum.top TopCat.Sheaf
attribute [local implicit_reducible] sheafCompose PresheafOfModules.presheaf
  SheafOfModules.toSheaf

section Basis

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]

/-- A homogeneous element of `S` of strictly positive degree. These index the standard opens
that Tag 0B5I's local construction lives on. -/
public def PositiveElem : Type u := {f : S // ∃ d : ℕ, 0 < d ∧ f ∈ 𝒮 d}

/-- The standard open `D₊(f)` cut out by a positive-degree homogeneous element. -/
public def positiveBasicOpen (p : PositiveElem 𝒮) : Opens (ProjectiveSpectrum.top 𝒮) :=
  ProjectiveSpectrum.basicOpen 𝒮 p.1

/-- The standard opens of positive-degree homogeneous elements are exactly the members of
`Stacks.Veronese.positiveBasicOpenSet`. -/
public theorem range_positiveBasicOpen :
    Set.range (positiveBasicOpen 𝒮) = Stacks.Veronese.positiveBasicOpenSet (𝒮 := 𝒮) := by
  ext V
  constructor
  · rintro ⟨⟨f, d, hd, hf⟩, rfl⟩
    exact ⟨f, d, hd, hf, rfl⟩
  · rintro ⟨f, d, hd, hf, rfl⟩
    exact ⟨(⟨f, d, hd, hf⟩ : PositiveElem 𝒮), rfl⟩

/-- **The positive-degree standard opens form a basis of `Proj 𝒮`.** -/
public theorem isBasis_positiveBasicOpen :
    Opens.IsBasis (Set.range (positiveBasicOpen 𝒮)) := by
  rw [range_positiveBasicOpen]
  exact Stacks.Veronese.positiveBasicOpenSet_isBasis (𝒮 := 𝒮)

end Basis

section Gluing

variable {S M : Type u} {σ : Type w} {τ : Type t}
  [CommRing S] [AddCommGroup M] [Module S M]
  [SetLike σ S] [AddSubgroupClass σ S] (𝒮 : ℕ → σ) [GradedRing 𝒮]
  [SetLike τ M] [AddSubgroupClass τ M] (𝒨 : ℤ → τ)
  [SetLike.GradedSMul 𝒮 𝒨]
  (G : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))

/-- **The local datum Tag 0B5I's proof produces:** a map on the sections of the sheaf associated
to a graded module over each positive-degree standard open, compatible with the restriction maps
between those opens. The maps are morphisms in the category of modules over the sections of the
structure sheaf, so each is linear over `Γ(D₊(f), 𝒪)`. -/
public structure StandardOpenHomData where
  /-- The comparison on the sections over a positive-degree standard open. -/
  app : ∀ p : PositiveElem 𝒮,
    (associatedModuleSheaf 𝒮 𝒨).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
      G.val.obj (op (positiveBasicOpen 𝒮 p))
  /-- Compatibility with the restriction between two standard opens. -/
  app_restrict : ∀ (p q : PositiveElem 𝒮)
      (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
      (s : (associatedModuleSheaf 𝒮 𝒨).val.obj (op (positiveBasicOpen 𝒮 p))),
    app q ((associatedModuleSheaf 𝒮 𝒨).val.map (homOfLE h).op s) =
      G.val.map (homOfLE h).op (app p s)

/-- **The gluing principle: the morphism `M̃ ⟶ 𝒢` built from the standard-open data.** This is
the step Tag 0B5I leaves out; the construction is the hom-level reading of Tag 009U applied to
the basis of positive-degree standard opens. -/
public noncomputable def homOfStandardOpenHomData (A : StandardOpenHomData 𝒮 𝒨 G) :
    associatedModuleSheaf 𝒮 𝒨 ⟶ G :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis
    (associatedModuleSheaf 𝒮 𝒨) G (positiveBasicOpen 𝒮) A.app
    (isBasis_positiveBasicOpen 𝒮) A.app_restrict

/-- The glued morphism restricts on each positive-degree standard open to the given map. -/
public theorem homOfStandardOpenHomData_app (A : StandardOpenHomData 𝒮 𝒨 G)
    (p : PositiveElem 𝒮) :
    (homOfStandardOpenHomData 𝒮 𝒨 G A).val.app (op (positiveBasicOpen 𝒮 p)) = A.app p :=
  Stacks.BasisRestriction.moduleSheafHomOfSectionHomOnBasis_app
    (associatedModuleSheaf 𝒮 𝒨) G (positiveBasicOpen 𝒮) A.app
    (isBasis_positiveBasicOpen 𝒮) A.app_restrict p

/-- The glued morphism is the only one with the given values on the positive-degree standard
opens. -/
public theorem eq_homOfStandardOpenHomData (A : StandardOpenHomData 𝒮 𝒨 G)
    (φ : associatedModuleSheaf 𝒮 𝒨 ⟶ G)
    (hφ : ∀ p : PositiveElem 𝒮, φ.val.app (op (positiveBasicOpen 𝒮 p)) = A.app p) :
    φ = homOfStandardOpenHomData 𝒮 𝒨 G A :=
  Stacks.BasisRestriction.moduleSheafHom_ext_onBasis (associatedModuleSheaf 𝒮 𝒨) G
    (positiveBasicOpen 𝒮) (isBasis_positiveBasicOpen 𝒮) φ _
    fun p => (hφ p).trans (homOfStandardOpenHomData_app 𝒮 𝒨 G A p).symm

/-- A compatible family of maps on the positive-degree standard opens extends to a unique
morphism of sheaves of modules out of the sheaf associated to a graded module. -/
public theorem existsUnique_hom_of_standardOpenHomData (A : StandardOpenHomData 𝒮 𝒨 G) :
    ∃! φ : associatedModuleSheaf 𝒮 𝒨 ⟶ G,
      ∀ p : PositiveElem 𝒮, φ.val.app (op (positiveBasicOpen 𝒮 p)) = A.app p :=
  ⟨homOfStandardOpenHomData 𝒮 𝒨 G A, homOfStandardOpenHomData_app 𝒮 𝒨 G A,
    fun φ hφ => eq_homOfStandardOpenHomData 𝒮 𝒨 G A φ hφ⟩

/-- **The local-to-global step.** A value of the glued morphism is determined by the local
data: if a section `t` of the target over `W` restricts, on every positive-degree standard open
inside `W`, to the local map applied to the restriction of `s`, then `t` is the value of the
glued morphism on `s`. -/
public theorem homOfStandardOpenHomData_app_eq_of_restrict (A : StandardOpenHomData 𝒮 𝒨 G)
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (s : (associatedModuleSheaf 𝒮 𝒨).val.obj (op W)) (t : G.val.obj (op W))
    (h : ∀ (p : PositiveElem 𝒮) (hle : positiveBasicOpen 𝒮 p ≤ W),
      A.app p ((associatedModuleSheaf 𝒮 𝒨).val.map (homOfLE hle).op s) =
        G.val.map (homOfLE hle).op t) :
    (homOfStandardOpenHomData 𝒮 𝒨 G A).val.app (op W) s = t := by
  refine Stacks.BasisRestriction.moduleSheafSection_ext_onBasis G (positiveBasicOpen 𝒮)
    (isBasis_positiveBasicOpen 𝒮) _ t ?_
  intro p hle
  rw [← PresheafOfModules.naturality_apply (homOfStandardOpenHomData 𝒮 𝒨 G A).val
    (homOfLE hle).op s, homOfStandardOpenHomData_app]
  exact h p hle

end Gluing

section Comparison

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]
  (F : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮)))
  (D : TwistedGlobalSectionsModule 𝒮 F)

/-- **The comparison morphism `M̃ ⟶ ℱ` of Tag 0B5I**, where
`M = ⨁_{n ∈ ℤ} Γ(Proj 𝒮, ℱ(n))` carries the graded `S`-module structure `D` of Tag 03GK: it is
the morphism glued from the standard-open comparison maps `θ`.

No `stacks` attribute. This is the construction; the tag's assertion that such a morphism exists
and is unique is `existsUnique_comparison`, which carries the attribute. A second attribute here
would report the same content twice. -/
public noncomputable def comparison
    (θ : ∀ p : PositiveElem 𝒮,
      (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
        F.val.obj (op (positiveBasicOpen 𝒮 p)))
    (hθ : ∀ (p q : PositiveElem 𝒮)
        (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
        (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj
          (op (positiveBasicOpen 𝒮 p))),
      θ q ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE h).op s) =
        F.val.map (homOfLE h).op (θ p s)) :
    twistedGlobalSectionsAssociatedSheaf 𝒮 F D ⟶ F :=
  letI := D.moduleInst
  letI := D.gradedSMul
  homOfStandardOpenHomData 𝒮 (twistedGlobalSectionsGrading 𝒮 F) F
    { app := θ, app_restrict := hθ }

/-- The comparison restricts on each positive-degree standard open to the given local map. -/
public theorem comparison_app
    (θ : ∀ p : PositiveElem 𝒮,
      (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
        F.val.obj (op (positiveBasicOpen 𝒮 p)))
    (hθ : ∀ (p q : PositiveElem 𝒮)
        (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
        (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj
          (op (positiveBasicOpen 𝒮 p))),
      θ q ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE h).op s) =
        F.val.map (homOfLE h).op (θ p s))
    (p : PositiveElem 𝒮) :
    (comparison 𝒮 F D θ hθ).val.app (op (positiveBasicOpen 𝒮 p)) = θ p := by
  let := D.moduleInst
  let := D.gradedSMul
  exact homOfStandardOpenHomData_app 𝒮 (twistedGlobalSectionsGrading 𝒮 F) F
    { app := θ, app_restrict := hθ } p

/-- The comparison is the only morphism `M̃ ⟶ ℱ` with the given values on the positive-degree
standard opens. -/
public theorem eq_comparison
    (θ : ∀ p : PositiveElem 𝒮,
      (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
        F.val.obj (op (positiveBasicOpen 𝒮 p)))
    (hθ : ∀ (p q : PositiveElem 𝒮)
        (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
        (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj
          (op (positiveBasicOpen 𝒮 p))),
      θ q ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE h).op s) =
        F.val.map (homOfLE h).op (θ p s))
    (φ : twistedGlobalSectionsAssociatedSheaf 𝒮 F D ⟶ F)
    (hφ : ∀ p : PositiveElem 𝒮, φ.val.app (op (positiveBasicOpen 𝒮 p)) = θ p) :
    φ = comparison 𝒮 F D θ hθ := by
  let := D.moduleInst
  let := D.gradedSMul
  exact eq_homOfStandardOpenHomData 𝒮 (twistedGlobalSectionsGrading 𝒮 F) F
    { app := θ, app_restrict := hθ } φ hφ

/-- **Tag 0B5I: the comparison morphism `M̃ ⟶ ℱ` from the twisted global sections exists and is
unique.** Here `M = ⨁_{n ∈ ℤ} Γ(Proj 𝒮, ℱ(n))` carries the graded `S`-module structure `D` of
Tag 03GK and `M̃` is its associated sheaf. Given the standard-open comparison maps `θ` and their
compatibility with restriction `hθ` — the local half of the source's proof — there is exactly
one morphism `M̃ ⟶ ℱ` restricting to them, namely `comparison`. -/
-- [Stacks, Tag 0B5I] is carried by
-- `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.existsUnique_comparison`, which is this
-- statement instantiated at the constructed `localComparison` / `localComparison_restrict`.
-- This is the conditional form and carries its hypotheses, so it does not claim the tag; its
-- content is unchanged.
public theorem existsUnique_comparison
    (θ : ∀ p : PositiveElem 𝒮,
      (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
        F.val.obj (op (positiveBasicOpen 𝒮 p)))
    (hθ : ∀ (p q : PositiveElem 𝒮)
        (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
        (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj
          (op (positiveBasicOpen 𝒮 p))),
      θ q ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE h).op s) =
        F.val.map (homOfLE h).op (θ p s)) :
    ∃! φ : twistedGlobalSectionsAssociatedSheaf 𝒮 F D ⟶ F,
      ∀ p : PositiveElem 𝒮, φ.val.app (op (positiveBasicOpen 𝒮 p)) = θ p :=
  ⟨comparison 𝒮 F D θ hθ, comparison_app 𝒮 F D θ hθ,
    fun φ hφ => eq_comparison 𝒮 F D θ hθ φ hφ⟩

/-- **Every value of the comparison is pinned down on the standard opens.** This is the
local-to-global step by which the remaining assertions of Tag 0B5I are reduced to the
standard-open data: in particular it reduces the degree-zero normalization to the degree-zero
normalization of the local maps. -/
public theorem comparison_app_eq_of_restrict
    (θ : ∀ p : PositiveElem 𝒮,
      (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
        F.val.obj (op (positiveBasicOpen 𝒮 p)))
    (hθ : ∀ (p q : PositiveElem 𝒮)
        (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
        (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj
          (op (positiveBasicOpen 𝒮 p))),
      θ q ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE h).op s) =
        F.val.map (homOfLE h).op (θ p s))
    {W : Opens (ProjectiveSpectrum.top 𝒮)}
    (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj (op W))
    (t : F.val.obj (op W))
    (h : ∀ (p : PositiveElem 𝒮) (hle : positiveBasicOpen 𝒮 p ≤ W),
      θ p ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE hle).op s) =
        F.val.map (homOfLE hle).op t) :
    (comparison 𝒮 F D θ hθ).val.app (op W) s = t := by
  let := D.moduleInst
  let := D.gradedSMul
  exact homOfStandardOpenHomData_app_eq_of_restrict 𝒮 (twistedGlobalSectionsGrading 𝒮 F) F
    { app := θ, app_restrict := hθ } s t h

/-- **The degree-zero normalization of Tag 0B5I.** A degree-zero element `m` of
`M = ⨁_{n ∈ ℤ} Γ(X, ℱ(n))` — that is, a global section of `ℱ(0)` — gives a global section `s` of
`M̃` by Tag 01M7, and the comparison carries it to the section `t` of `ℱ` that the local maps
produce on every positive-degree standard open. Together with the identification
`Γ(X, ℱ(0)) = Γ(X, ℱ)` this is the source's assertion that the comparison induces the identity
on `Γ(X, ℱ)` in degree zero. -/
public theorem comparison_degreeZeroToGlobalSections
    (θ : ∀ p : PositiveElem 𝒮,
      (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
        F.val.obj (op (positiveBasicOpen 𝒮 p)))
    (hθ : ∀ (p q : PositiveElem 𝒮)
        (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
        (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj
          (op (positiveBasicOpen 𝒮 p))),
      θ q ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE h).op s) =
        F.val.map (homOfLE h).op (θ p s))
    (m : twistedGlobalSectionsGrading 𝒮 F 0)
    (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.obj
      (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))))
    (hs : letI := D.moduleInst; letI := D.gradedSMul
      s = degreeZeroToGlobalSections 𝒮 (twistedGlobalSectionsGrading 𝒮 F) m)
    (t : F.val.obj (op (⊤ : Opens (ProjectiveSpectrum.top 𝒮))))
    (h : letI := D.moduleInst; letI := D.gradedSMul
      ∀ (p : PositiveElem 𝒮) (hle : positiveBasicOpen 𝒮 p ≤ ⊤),
        θ p ((twistedGlobalSectionsAssociatedSheaf 𝒮 F D).val.map (homOfLE hle).op
            (degreeZeroToGlobalSections 𝒮 (twistedGlobalSectionsGrading 𝒮 F) m)) =
          F.val.map (homOfLE hle).op t) :
    (comparison 𝒮 F D θ hθ).val.app (op ⊤) s = t := by
  subst hs
  exact comparison_app_eq_of_restrict 𝒮 F D θ hθ _ t h

end Comparison

section Functoriality

variable {S : Type u} {σ : Type w} [CommRing S] [SetLike σ S] [AddSubgroupClass σ S]
  (𝒮 : ℕ → σ) [GradedRing 𝒮]
  {E F G : SheafOfModules.{u}
    ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒮))
      (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒮))}

/-- The map on twisted global sections induced by a morphism `ℰ ⟶ ℱ` preserves the grading: it
carries the degree-`i` summand into the degree-`i` summand, because it is the degreewise twist of
the morphism read on global sections. -/
public theorem twistedSectionsMap_mem_grading (ψ : E ⟶ F) (i : ℤ)
    (m : twistedGlobalSections 𝒮 E) (hm : m ∈ twistedGlobalSectionsGrading 𝒮 E i) :
    twistedSectionsMap 𝒮 ψ m ∈ twistedGlobalSectionsGrading 𝒮 F i := by
  obtain ⟨a, rfl⟩ := (DirectSum.mem_rangeGrading ℤ _ i m).mp hm
  refine (DirectSum.mem_rangeGrading ℤ _ i _).mpr ⟨twistedSectionsMapComponent 𝒮 ψ i a, ?_⟩
  exact twistedSectionsMap_of 𝒮 ψ i a

/-- **The morphism `M̃_ℰ ⟶ M̃_ℱ` induced by a morphism `ψ : ℰ ⟶ ℱ`**: the associated sheaf of the
degree-preserving `S`-linear map that `ψ` induces on twisted global sections, by Tag 01M7's
functoriality of the associated-sheaf construction.

No `stacks` attribute. This is the construction in which the functoriality of Tag 0B5I is
phrased; the assertions are `comparison_naturality` and the two functor laws below. -/
public noncomputable def twistedGlobalSectionsAssociatedSheafMap
    (DE : TwistedGlobalSectionsModule 𝒮 E) (DF : TwistedGlobalSectionsModule 𝒮 F) (ψ : E ⟶ F) :
    twistedGlobalSectionsAssociatedSheaf 𝒮 E DE ⟶ twistedGlobalSectionsAssociatedSheaf 𝒮 F DF :=
  letI := DE.moduleInst
  letI := DE.gradedSMul
  letI := DF.moduleInst
  letI := DF.gradedSMul
  associatedModuleSheafMap 𝒮 (twistedGlobalSectionsGrading 𝒮 E)
    (twistedGlobalSectionsGrading 𝒮 F)
    (twistedSectionsLinearMap 𝒮 (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 E DE)
      (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F DF) ψ)
    (twistedSectionsMap_mem_grading 𝒮 ψ)

/-- The identity of `ℱ` induces the identity of `M̃_ℱ`. -/
public theorem twistedGlobalSectionsAssociatedSheafMap_id
    (DE : TwistedGlobalSectionsModule 𝒮 E) :
    twistedGlobalSectionsAssociatedSheafMap 𝒮 DE DE (𝟙 E) = 𝟙 _ := by
  let := DE.moduleInst
  let := DE.gradedSMul
  have h : twistedSectionsLinearMap 𝒮 (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 E DE)
      (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 E DE) (𝟙 E) = LinearMap.id :=
    LinearMap.ext fun x => DFunLike.congr_fun (twistedSectionsMap_id (E := E) 𝒮) x
  refine Eq.trans ?_ (associatedModuleSheafMap_id
    (𝒮 := 𝒮) (𝒨 := twistedGlobalSectionsGrading 𝒮 E))
  rw [twistedGlobalSectionsAssociatedSheafMap]
  congr 1

/-- A composite of morphisms induces the composite of the morphisms of associated sheaves. -/
public theorem twistedGlobalSectionsAssociatedSheafMap_comp
    (DE : TwistedGlobalSectionsModule 𝒮 E) (DF : TwistedGlobalSectionsModule 𝒮 F)
    (DG : TwistedGlobalSectionsModule 𝒮 G) (ψ : E ⟶ F) (χ : F ⟶ G) :
    twistedGlobalSectionsAssociatedSheafMap 𝒮 DE DG (ψ ≫ χ) =
      twistedGlobalSectionsAssociatedSheafMap 𝒮 DE DF ψ ≫
        twistedGlobalSectionsAssociatedSheafMap 𝒮 DF DG χ := by
  let := DE.moduleInst
  let := DE.gradedSMul
  let := DF.moduleInst
  let := DF.gradedSMul
  let := DG.moduleInst
  let := DG.gradedSMul
  have h : twistedSectionsLinearMap 𝒮 (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 E DE)
      (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 G DG) (ψ ≫ χ) =
      (twistedSectionsLinearMap 𝒮 (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F DF)
        (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 G DG) χ).comp
        (twistedSectionsLinearMap 𝒮 (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 E DE)
          (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F DF) ψ) :=
    LinearMap.ext fun x => DFunLike.congr_fun (twistedSectionsMap_comp 𝒮 ψ χ) x
  refine Eq.trans ?_ (associatedModuleSheafMap_comp
    𝒮 (twistedGlobalSectionsGrading 𝒮 E) (twistedGlobalSectionsGrading 𝒮 F)
    (twistedGlobalSectionsGrading 𝒮 G)
    (twistedSectionsLinearMap 𝒮 (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 E DE)
      (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F DF) ψ)
    (twistedSectionsMap_mem_grading 𝒮 ψ)
    (twistedSectionsLinearMap 𝒮 (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 F DF)
      (isTwistedSectionsSMul_twistedGlobalSectionsModule 𝒮 G DG) χ)
    (twistedSectionsMap_mem_grading 𝒮 χ))
  rw [twistedGlobalSectionsAssociatedSheafMap]
  congr 1

/-- **Tag 0B5I: the comparison morphism is functorial in `ℱ`.** Let `ψ : ℰ ⟶ ℱ` be a morphism of
modules on `Proj 𝒮`, let `D_ℰ` and `D_ℱ` be the graded module structures of Tag 03GK on the two
modules of twisted global sections, and let `θ_ℰ` and `θ_ℱ` be standard-open comparison maps for
them. If those local maps are natural in the sheaf — on every positive-degree standard open,
`θ_ℱ` after the map induced on the sections of `M̃` agrees with `ψ` after `θ_ℰ` — then the square

`M̃_ℰ ⟶ M̃_ℱ ⟶ ℱ = M̃_ℰ ⟶ ℰ ⟶ ℱ`

commutes. Both composites are morphisms `M̃_ℰ ⟶ ℱ`, and a morphism out of `M̃_ℰ` is determined by
its values on the positive-degree standard opens, where the two agree by hypothesis. -/
-- [Stacks, Tag 0B5I] is carried by
-- `Stacks.AlgebraicGeometry.ProjTwistIntegerComparison.integerComparison_naturality`, which is
-- this statement instantiated at the constructed `localComparison` / `localComparison_restrict`
-- and `localComparison_naturality`. This is the conditional form and carries its hypotheses, so
-- it does not claim the tag; its content is unchanged.
public theorem comparison_naturality
    (DE : TwistedGlobalSectionsModule 𝒮 E) (DF : TwistedGlobalSectionsModule 𝒮 F) (ψ : E ⟶ F)
    (θE : ∀ p : PositiveElem 𝒮,
      (twistedGlobalSectionsAssociatedSheaf 𝒮 E DE).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
        E.val.obj (op (positiveBasicOpen 𝒮 p)))
    (hθE : ∀ (p q : PositiveElem 𝒮)
        (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
        (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 E DE).val.obj
          (op (positiveBasicOpen 𝒮 p))),
      θE q ((twistedGlobalSectionsAssociatedSheaf 𝒮 E DE).val.map (homOfLE h).op s) =
        E.val.map (homOfLE h).op (θE p s))
    (θF : ∀ p : PositiveElem 𝒮,
      (twistedGlobalSectionsAssociatedSheaf 𝒮 F DF).val.obj (op (positiveBasicOpen 𝒮 p)) ⟶
        F.val.obj (op (positiveBasicOpen 𝒮 p)))
    (hθF : ∀ (p q : PositiveElem 𝒮)
        (h : positiveBasicOpen 𝒮 q ≤ positiveBasicOpen 𝒮 p)
        (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 F DF).val.obj
          (op (positiveBasicOpen 𝒮 p))),
      θF q ((twistedGlobalSectionsAssociatedSheaf 𝒮 F DF).val.map (homOfLE h).op s) =
        F.val.map (homOfLE h).op (θF p s))
    (hnat : ∀ (p : PositiveElem 𝒮)
        (s : (twistedGlobalSectionsAssociatedSheaf 𝒮 E DE).val.obj
          (op (positiveBasicOpen 𝒮 p))),
      θF p ((twistedGlobalSectionsAssociatedSheafMap 𝒮 DE DF ψ).val.app
          (op (positiveBasicOpen 𝒮 p)) s) =
        ψ.val.app (op (positiveBasicOpen 𝒮 p)) (θE p s)) :
    twistedGlobalSectionsAssociatedSheafMap 𝒮 DE DF ψ ≫ comparison 𝒮 F DF θF hθF =
      comparison 𝒮 E DE θE hθE ≫ ψ := by
  refine Stacks.BasisRestriction.moduleSheafHom_ext_onBasis _ F (positiveBasicOpen 𝒮)
    (isBasis_positiveBasicOpen 𝒮) _ _ fun p => ?_
  simp only [SheafOfModules.comp_val, PresheafOfModules.comp_app,
    comparison_app 𝒮 F DF θF hθF p, comparison_app 𝒮 E DE θE hθE p]
  exact ModuleCat.hom_ext (LinearMap.ext fun s => hnat p s)

end Functoriality

end Stacks.AlgebraicGeometry.ProjTwistComparison

end
