module

public import Mathlib.CategoryTheory.Limits.Shapes.Equalizers
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.FaithfulRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.FinitePresentationAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.FlatAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Cech.RelativeSpectralSequence
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Equalizers
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothAlgebraicStack
public import StacksFrontier.AlgebraicGeometry.Stacks.Surjective
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.CohomologyOfModules
import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.EtaleLocalLifts
import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveFlatFppfLocalSections
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.CoveringSieves
import StacksFrontier.CategoryTheory.FiberedCategory.FiberedInSetoids

/-!
# Čech-to-cohomology for a smooth or flat presentation of an algebraic stack

Let `f : 𝒰 ⟶ 𝒳` be a `1`-morphism of algebraic stacks which is representable by algebraic
spaces. If `f` is surjective and smooth, every abelian sheaf on the étale site of `𝒳` carries a
first-quadrant spectral sequence whose first page is étale cohomology on the terms of the
relative Čech nerve of `f` and which abuts to étale cohomology on `𝒳`; if `f` is surjective,
flat and locally of finite presentation, the same holds for the fppf topology.

Given a further `1`-morphism `g : 𝒳 ⟶ 𝒴` of algebraic stacks, the same two coverings produce
spectral sequences of abelian sheaves on `𝒴` whose first page is the higher direct image along
`g ∘ fₚ` of the inverse image of the sheaf on the degree `p` term of the Čech nerve and which
abut to the higher direct images along `g`.

## Main results

* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_etaleCechSpectralSequence`:
  Tag 06XJ, part (1).
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfCechSpectralSequence`:
  Tag 06XJ, part (2).
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_etaleSpectralSequenceData` and
  `AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfSpectralSequenceData`: the same two
  spectral sequences with the cohomology groups in an arbitrary universe in which they exist.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_etaleDirectImageSpectralSequenceData`:
  Tag 072G, part (1)(a).
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfDirectImageSpectralSequenceData`:
  Tag 072G, part (2)(a).

## Implementation notes

The two parts of Tag 06XJ are the relative Čech-to-cohomology spectral sequence of Tag 06XF,
and the two parts of Tag 072G its direct-image companion Tag 072D, whose four hypotheses are
the same and are discharged here. Faithfulness of the underlying functor is Tag 04Y5 for a
`1`-morphism representable by algebraic spaces. That the image of `f` covers every object of
`𝒳` locally is Tag 06XH, in the sharper singleton form the source's own proof produces: part (2)
of that tag for the étale topology, and for the fppf topology the same passage from the single
flat, locally finitely presented, surjective morphism of the site along which an object lifts
(Tag 06QA) to a covering sieve upstairs. The remaining hypothesis of Tag 06XF and Tag 072D,
that `𝒰` has equalizers, is part (3) of Tag 06WY for the algebraic stack `𝒰`, the instance
`AlgebraicGeometry.Stack.AlgebraicStacks.hasEqualizers`.

Cohomology on a site is defined through `Ext` groups, whose existence in a given universe is the
smallness condition `CategoryTheory.HasExt`. At the universe of the coefficients it holds for the
sites of a category fibred in groupoids over the big fppf site, since abelian sheaves there have
enough injectives; together with the existence of sheafification at that universe this is what
lets the two parts of Tag 06XJ be stated without any further hypothesis.

The spectral sequences themselves, their first pages, their first-quadrant vanishing and their
finite abutments are those recorded by `Stacks.RelativeCech.SpectralSequenceData` and
`Stacks.RelativeCech.PushforwardSpectralSequenceData`; no parallel datum is introduced.

Parts (1)(b) and (2)(b) of Tag 072G, the versions for sheaves of `𝒪`-modules, are not here:
they are Tag 072E, the module companion of Tag 072D, applied in
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_etaleModuleDirectImageSpectralSequence` and
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfModuleDirectImageSpectralSequence`, where
the two parts (1)(a) and (2)(a) are also stated with the sheafification and Kan extension
instances supplied.

## References

* [Stacks Project, Tag 06XJ](https://stacks.math.columbia.edu/tag/06XJ)
* [Stacks Project, Tag 072G](https://stacks.math.columbia.edu/tag/072G)
* [Stacks Project, Tag 06XF](https://stacks.math.columbia.edu/tag/06XF)
* [Stacks Project, Tag 072D](https://stacks.math.columbia.edu/tag/072D)
* [Stacks Project, Tag 06XH](https://stacks.math.columbia.edu/tag/06XH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry

namespace AlgebraicGeometry.Stack.AlgebraicStacks

universe u w a b

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

section

variable {𝒰 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)

/-- Along a surjective, flat, locally finitely presented `1`-morphism of algebraic stacks every
object of the target receives a morphism from the image of an object of the source whose
singleton generates a covering sieve of the fppf topology. This is the fppf companion of
`AlgebraicGeometry.Stack.exists_etaleLocalLift`, obtained from Tag 06QA in the same way. -/
theorem exists_fppfLocalLift_singleton
    (hsurj : Stack.IsSurjective B S hS f)
    (hflat : IsFlat B S hS f)
    (hlfp : IsLocallyOfFinitePresentation B S hS f)
    (x : 𝒳.val.val.obj) :
    ∃ (z : 𝒰.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj z ⟶ x),
      Sieve.generate (Presieve.singleton α) ∈
        BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf x := by
  obtain ⟨T, m, hm, hm', hm'', z, α, hα⟩ :=
    Stack.exists_scheme_lift_of_isSurjective_isFlat_isLfp B S hS f hsurj hflat hlfp
      (𝒳.val.val.p.obj x) (Functor.Fiber.mk rfl)
  have : 𝒳.val.val.p.IsFibered := 𝒳.val.isFiberedInGroupoids.isFibered
  refine ⟨z, α, ?_⟩
  refine Functor.generate_singleton_mem_inheritedTopology_of_isHomLift 𝒳.val.val.p
    (BigFppfOver.baseOverTopology B S hS .fppf) α
    (𝒳.val.isFiberedInGroupoids.isStronglyCartesian α) _ hα
    (mem_topology_of_family B S hS (I := PUnit.{u + 2}) (fun _ => T) (fun _ => m)
      (fun _ => hm) (fun _ => hm') (fun t => ⟨PUnit.unit, hm''.1 t⟩)) ?_
  rintro W u ⟨W', k, -, ⟨i⟩, rfl⟩
  exact ⟨k, rfl⟩

/-- A cover by singletons of morphisms out of images of objects is a cover by a presieve all of
whose members have source isomorphic to such an image. -/
private theorem exists_presieve_of_singleton_cover {C D : Type*} [Category C] [Category D]
    (F : C ⥤ D) {J : ∀ x : D, Set (Sieve x)}
    (hcover : ∀ x : D, ∃ (z : C) (α : F.obj z ⟶ x), Sieve.generate (Presieve.singleton α) ∈ J x) :
    ∀ x : D, ∃ R : Presieve x, Sieve.generate R ∈ J x ∧
      ∀ ⦃y : D⦄ (g : y ⟶ x), R g → ∃ z : C, Nonempty (y ≅ F.obj z) := by
  intro x
  obtain ⟨z, α, hα⟩ := hcover x
  exact ⟨Presieve.singleton α, hα, fun y g ⟨⟩ => ⟨z, ⟨Iso.refl _⟩⟩⟩

variable (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
  (τ : SiteKind)
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
    AddCommGrpCat.{max (u + 1) a}]
  [HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
    AddCommGrpCat.{max (u + 1) a})]
  [∀ n : ℕ, HasSheafify (BigFppfOver.associatedTopology B S hS
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p) τ)
    AddCommGrpCat.{max (u + 1) a}]
  [∀ n : ℕ, HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p) τ)
    AddCommGrpCat.{max (u + 1) a})]

include hrep in
/-- The relative Čech-to-cohomology spectral sequence of Tag 06XF for a `1`-morphism of
algebraic stacks which is representable by algebraic spaces and whose image covers every object
of the target by a singleton for the topology `τ`; the source has equalizers, being an algebraic
stack. -/
private theorem exists_spectralSequenceData_of_cover
    (hcover : ∀ x : 𝒳.val.val.obj,
      ∃ (z : 𝒰.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj z ⟶ x),
        Sieve.generate (Presieve.singleton α) ∈
          BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ x)
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
      AddCommGrpCat.{max (u + 1) a}) :
    Nonempty (Stacks.RelativeCech.SpectralSequenceData B S hS 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) τ 𝓕) := by
  have : (CatFiberedInGroupoids.homFunctor f.hom).Faithful :=
    AlgebraicStacks.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f hrep
  refine Stacks.RelativeCech.exists_spectralSequenceData.{u, u + 1, u + 1, u, u, a, b}
    B S hS 𝒰.val.val.p 𝒳.val.val.p (CatFiberedInGroupoids.homFunctor f.hom) τ
    𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
    (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      f.hom.hom.w) (exists_presieve_of_singleton_cover _ hcover) 𝓕

end

section Etale

variable {𝒰 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)
  (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
  (hsurj : Stack.IsSurjective B S hS f) (hsmooth : IsSmooth B S hS f)
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.etale)
    AddCommGrpCat.{max (u + 1) a}]
  [HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.etale)
    AddCommGrpCat.{max (u + 1) a})]
  [∀ n : ℕ, HasSheafify (BigFppfOver.associatedTopology B S hS
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p) SiteKind.etale)
    AddCommGrpCat.{max (u + 1) a}]
  [∀ n : ℕ, HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p) SiteKind.etale)
    AddCommGrpCat.{max (u + 1) a})]

include hrep hsurj hsmooth in
/-- The étale Čech-to-cohomology spectral sequence of a `1`-morphism `f : 𝒰 ⟶ 𝒳` of algebraic
stacks which is representable by algebraic spaces, surjective and smooth, for cohomology groups
taken in an arbitrary universe `b` in which they exist: for an abelian sheaf `𝓕` on the étale site
of `𝒳` there is a first-quadrant spectral sequence
`E₁^{p,q} = H^q_étale(𝒰ₚ, fₚ⁻¹𝓕) ⇒ H^{p+q}_étale(𝒳, 𝓕)`, where `𝒰ₚ` is the degree `p` term of the
relative Čech nerve of `f` and `fₚ` its projection to `𝒳`. For the cohomology groups in the
universe of the coefficients, where they always exist, this is
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_etaleCechSpectralSequence`. -/
theorem exists_etaleSpectralSequenceData
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.etale)
      AddCommGrpCat.{max (u + 1) a}) :
    Nonempty (Stacks.RelativeCech.SpectralSequenceData B S hS 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) SiteKind.etale 𝓕) :=
  exists_spectralSequenceData_of_cover.{u, w, a, b} B S hS f hrep SiteKind.etale
    (fun x => Stack.exists_etaleLocalLift B S hS f hsurj hsmooth x) 𝓕

end Etale

section Fppf

variable {𝒰 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)
  (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
  (hsurj : Stack.IsSurjective B S hS f) (hflat : IsFlat B S hS f)
  (hlfp : IsLocallyOfFinitePresentation B S hS f)
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a}]
  [HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a})]
  [∀ n : ℕ, HasSheafify (BigFppfOver.associatedTopology B S hS
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p) SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a}]
  [∀ n : ℕ, HasExt.{b} (Sheaf (BigFppfOver.associatedTopology B S hS
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p) SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a})]

include hrep hsurj hflat hlfp in
/-- The fppf Čech-to-cohomology spectral sequence of a `1`-morphism `f : 𝒰 ⟶ 𝒳` of algebraic
stacks which is representable by algebraic spaces, surjective, flat and locally of finite
presentation, for cohomology groups taken in an arbitrary universe `b` in which they exist: for an
abelian sheaf `𝓕` on the fppf site of `𝒳` there is a first-quadrant spectral sequence
`E₁^{p,q} = H^q_fppf(𝒰ₚ, fₚ⁻¹𝓕) ⇒ H^{p+q}_fppf(𝒳, 𝓕)`, where `𝒰ₚ` is the degree `p` term of the
relative Čech nerve of `f` and `fₚ` its projection to `𝒳`. For the cohomology groups in the
universe of the coefficients, where they always exist, this is
`AlgebraicGeometry.Stack.AlgebraicStacks.exists_fppfCechSpectralSequence`. -/
theorem exists_fppfSpectralSequenceData
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
      AddCommGrpCat.{max (u + 1) a}) :
    Nonempty (Stacks.RelativeCech.SpectralSequenceData B S hS 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) SiteKind.fppf 𝓕) :=
  exists_spectralSequenceData_of_cover.{u, w, a, b} B S hS f hrep SiteKind.fppf
    (exists_fppfLocalLift_singleton B S hS f hsurj hflat hlfp) 𝓕

end Fppf

section Cohomology

attribute [local instance] Stacks.Cohomology.SiteModules.site_hasSheafify_addCommGrp
  Stacks.Cohomology.SiteModules.site_hasExt_addCommGrp

variable {𝒰 𝒳 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳)

/-- **Stacks 06XJ, part (1).** Let `f : 𝒰 ⟶ 𝒳` be a `1`-morphism of algebraic stacks which is
representable by algebraic spaces, surjective and smooth, and let `𝓕` be an abelian sheaf on the
étale site of `𝒳`. Then there is a first-quadrant spectral sequence
`E₁^{p,q} = H^q_étale(𝒰ₚ, fₚ⁻¹𝓕) ⇒ H^{p+q}_étale(𝒳, 𝓕)`, where
`𝒰ₚ = 𝒰 ×_𝒳 ⋯ ×_𝒳 𝒰` (`p + 1` factors) is the degree `p` term of the relative Čech nerve of `f`
and `fₚ : 𝒰ₚ ⟶ 𝒳` its projection; the first page, the first-quadrant vanishing and the
convergence to the étale cohomology of `𝓕` are the fields of
`Stacks.RelativeCech.SpectralSequenceData`. -/
@[stacks 06XJ "part (1): the étale spectral sequence of a presentation which is representable \
by algebraic spaces, surjective and smooth"]
theorem exists_etaleCechSpectralSequence
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hsmooth : IsSmooth B S hS f)
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.etale)
      AddCommGrpCat.{max (u + 1) a}) :
    Nonempty (Stacks.RelativeCech.SpectralSequenceData B S hS 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) SiteKind.etale 𝓕) :=
  exists_etaleSpectralSequenceData.{u, w, a, max (u + 1) a} B S hS f hrep hsurj hsmooth 𝓕

/-- **Stacks 06XJ, part (2).** Let `f : 𝒰 ⟶ 𝒳` be a `1`-morphism of algebraic stacks which is
representable by algebraic spaces, surjective, flat and locally of finite presentation, and let
`𝓕` be an abelian sheaf on (the fppf site of) `𝒳`. Then there is a first-quadrant spectral
sequence `E₁^{p,q} = H^q_fppf(𝒰ₚ, fₚ⁻¹𝓕) ⇒ H^{p+q}_fppf(𝒳, 𝓕)`, where
`𝒰ₚ = 𝒰 ×_𝒳 ⋯ ×_𝒳 𝒰` (`p + 1` factors) is the degree `p` term of the relative Čech nerve of `f`
and `fₚ : 𝒰ₚ ⟶ 𝒳` its projection; the first page, the first-quadrant vanishing and the
convergence to the fppf cohomology of `𝓕` are the fields of
`Stacks.RelativeCech.SpectralSequenceData`. -/
@[stacks 06XJ "part (2): the fppf spectral sequence of a presentation which is representable \
by algebraic spaces, surjective, flat and locally of finite presentation"]
theorem exists_fppfCechSpectralSequence
    (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
    (hsurj : Stack.IsSurjective B S hS f) (hflat : IsFlat B S hS f)
    (hlfp : IsLocallyOfFinitePresentation B S hS f)
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
      AddCommGrpCat.{max (u + 1) a}) :
    Nonempty (Stacks.RelativeCech.SpectralSequenceData B S hS 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) SiteKind.fppf 𝓕) :=
  exists_fppfSpectralSequenceData.{u, w, a, max (u + 1) a} B S hS f hrep hsurj hflat hlfp 𝓕

end Cohomology

section DirectImage

variable {𝒰 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (g : 𝒳 ⟶ 𝒴)
  (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
  (τ : SiteKind)
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
    AddCommGrpCat.{max (u + 1) a}]
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p τ)
    AddCommGrpCat.{max (u + 1) a}]
  [∀ n : ℕ, HasSheafify (BigFppfOver.associatedTopology B S hS
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p) τ)
    AddCommGrpCat.{max (u + 1) a}]
  [∀ P : 𝒳.val.val.objᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a},
    (CatFiberedInGroupoids.homFunctor g.hom).op.HasPointwiseRightKanExtension P]
  [∀ (n : ℕ) (P : (Stacks.RelativeCech.Tuple 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a}),
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) n ⋙
      CatFiberedInGroupoids.homFunctor g.hom).op.HasPointwiseRightKanExtension P]

include hrep in
/-- The relative Čech spectral sequence for higher direct images of Tag 072D, for a `1`-morphism
`f : 𝒰 ⟶ 𝒳` of algebraic stacks which is representable by algebraic spaces, whose source has
equalizers and whose image covers every object of `𝒳` by a singleton for the topology `τ`, and a
further `1`-morphism `g : 𝒳 ⟶ 𝒴` along which the direct images are taken. -/
private theorem exists_pushforwardSpectralSequenceData_of_cover
    (hcover : ∀ x : 𝒳.val.val.obj,
      ∃ (z : 𝒰.val.val.obj) (α : (CatFiberedInGroupoids.homFunctor f.hom).obj z ⟶ x),
        Sieve.generate (Presieve.singleton α) ∈
          BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ x)
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
      AddCommGrpCat.{max (u + 1) a}) :
    Nonempty (Stacks.RelativeCech.PushforwardSpectralSequenceData B S hS 𝒳.val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom) τ 𝓕) := by
  have : (CatFiberedInGroupoids.homFunctor f.hom).Faithful :=
    AlgebraicStacks.faithful_homFunctor_of_isRepresentableByAlgebraicSpaces B S hS f hrep
  refine Stacks.RelativeCech.exists_pushforwardSpectralSequenceData.{u, u + 1, u + 1, u + 1,
      u, u, u, a}
    B S hS 𝒰.val.val.p 𝒳.val.val.p 𝒴.val.val.p
    (CatFiberedInGroupoids.homFunctor f.hom) (CatFiberedInGroupoids.homFunctor g.hom) τ
    𝒰.val.isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
    (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒳.val.isFiberedInGroupoids
      f.hom.hom.w)
    (Functor.isFibredOneMorphism_of_isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      g.hom.hom.w) (exists_presieve_of_singleton_cover _ hcover) 𝓕

end DirectImage

section EtaleDirectImage

variable {𝒰 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (g : 𝒳 ⟶ 𝒴)
  (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
  (hsurj : Stack.IsSurjective B S hS f) (hsmooth : IsSmooth B S hS f)
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.etale)
    AddCommGrpCat.{max (u + 1) a}]
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p SiteKind.etale)
    AddCommGrpCat.{max (u + 1) a}]
  [∀ n : ℕ, HasSheafify (BigFppfOver.associatedTopology B S hS
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p) SiteKind.etale)
    AddCommGrpCat.{max (u + 1) a}]
  [∀ P : 𝒳.val.val.objᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a},
    (CatFiberedInGroupoids.homFunctor g.hom).op.HasPointwiseRightKanExtension P]
  [∀ (n : ℕ) (P : (Stacks.RelativeCech.Tuple 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a}),
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) n ⋙
      CatFiberedInGroupoids.homFunctor g.hom).op.HasPointwiseRightKanExtension P]

include hrep hsurj hsmooth in
/-- **Stacks 072G, part (1)(a).** Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable `1`-morphisms of
algebraic stacks and assume `f` is representable by algebraic spaces, surjective and smooth. For
an abelian sheaf `𝓕` on the étale site of `𝒳` there is a first-quadrant spectral sequence of
abelian sheaves on the étale site of `𝒴`
`E₁^{p,q} = R^q (g ∘ fₚ)_* fₚ⁻¹𝓕 ⇒ R^{p+q} g_* 𝓕`,
all higher direct images computed in the étale topology, where `𝒰ₚ` is the degree `p` term of the
relative Čech nerve of `f`, that is the `(p+1)`-fold fibre product of `𝒰` over `𝒳`, and `fₚ` its
projection to `𝒳`. -/
@[stacks 072G "part (1)(a): the étale spectral sequence for higher direct images along a smooth \
surjective presentation"]
theorem exists_etaleDirectImageSpectralSequenceData
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.etale)
      AddCommGrpCat.{max (u + 1) a}) :
    Nonempty (Stacks.RelativeCech.PushforwardSpectralSequenceData B S hS 𝒳.val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom) SiteKind.etale 𝓕) :=
  exists_pushforwardSpectralSequenceData_of_cover.{u, w, a} B S hS f g hrep SiteKind.etale
    (fun x => Stack.exists_etaleLocalLift B S hS f hsurj hsmooth x) 𝓕

end EtaleDirectImage

section FppfDirectImage

variable {𝒰 𝒳 𝒴 : Stack.AlgebraicStacks.{u, w} B S hS} (f : 𝒰 ⟶ 𝒳) (g : 𝒳 ⟶ 𝒴)
  (hrep : Stack.IsRepresentableByAlgebraicSpaces B S hS f.hom.hom)
  (hsurj : Stack.IsSurjective B S hS f) (hflat : IsFlat B S hS f)
  (hlfp : IsLocallyOfFinitePresentation B S hS f)
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a}]
  [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒴.val.val.p SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a}]
  [∀ n : ℕ, HasSheafify (BigFppfOver.associatedTopology B S hS
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n ⋙ 𝒳.val.val.p) SiteKind.fppf)
    AddCommGrpCat.{max (u + 1) a}]
  [∀ P : 𝒳.val.val.objᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a},
    (CatFiberedInGroupoids.homFunctor g.hom).op.HasPointwiseRightKanExtension P]
  [∀ (n : ℕ) (P : (Stacks.RelativeCech.Tuple 𝒳.val.val.p
      (CatFiberedInGroupoids.homFunctor f.hom) n)ᵒᵖ ⥤ AddCommGrpCat.{max (u + 1) a}),
    (Stacks.RelativeCech.Tuple.projection 𝒳.val.val.p
        (CatFiberedInGroupoids.homFunctor f.hom) n ⋙
      CatFiberedInGroupoids.homFunctor g.hom).op.HasPointwiseRightKanExtension P]

include hrep hsurj hflat hlfp in
/-- **Stacks 072G, part (2)(a).** Let `f : 𝒰 ⟶ 𝒳` and `g : 𝒳 ⟶ 𝒴` be composable `1`-morphisms of
algebraic stacks and assume `f` is representable by algebraic spaces, surjective, flat and
locally of finite presentation. For an abelian sheaf `𝓕` on the fppf site of `𝒳` there is a
first-quadrant spectral sequence of abelian sheaves on the fppf site of `𝒴`
`E₁^{p,q} = R^q (g ∘ fₚ)_* fₚ⁻¹𝓕 ⇒ R^{p+q} g_* 𝓕`,
all higher direct images computed in the fppf topology, where `𝒰ₚ` is the degree `p` term of the
relative Čech nerve of `f`, that is the `(p+1)`-fold fibre product of `𝒰` over `𝒳`, and `fₚ` its
projection to `𝒳`. -/
@[stacks 072G "part (2)(a): the fppf spectral sequence for higher direct images along a flat \
surjective presentation"]
theorem exists_fppfDirectImageSpectralSequenceData
    (𝓕 : Sheaf (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p SiteKind.fppf)
      AddCommGrpCat.{max (u + 1) a}) :
    Nonempty (Stacks.RelativeCech.PushforwardSpectralSequenceData B S hS 𝒳.val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor g.hom) SiteKind.fppf 𝓕) :=
  exists_pushforwardSpectralSequenceData_of_cover.{u, w, a} B S hS f g hrep SiteKind.fppf
    (exists_fppfLocalLift_singleton B S hS f hsurj hflat hlfp) 𝓕

end FppfDirectImage

end AlgebraicGeometry.Stack.AlgebraicStacks

end
