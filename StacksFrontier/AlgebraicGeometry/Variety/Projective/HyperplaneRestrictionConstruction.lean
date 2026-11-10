module

public import StacksFrontier.AlgebraicGeometry.Chow.FlatPullback.IsomorphismBaseChange
public import StacksFrontier.AlgebraicGeometry.Chow.ZeroSchemePullback.Basic
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceHyperplaneSection
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjectiveSpaceSectionMulShape
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.RegularSectionCorrespondence
public import StacksFrontier.AlgebraicGeometry.NonvanishingPullback.Nonvanishing
public import StacksFrontier.AlgebraicGeometry.NonvanishingSpelling.Basic
public import StacksFrontier.AlgebraicGeometry.ProjModelStructureMap.TwistSectionTransport
public import StacksFrontier.AlgebraicGeometry.ProjNoetherian.Basic
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneIsProjectiveSpace
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.HyperplaneTwistSequence
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceBaseChange.FieldExtension
public import StacksFrontier.AlgebraicGeometry.RelativeProjChain.EventualBijective
public import StacksFrontier.AlgebraicGeometry.Variety.EulerChar.ProjectiveTwistQuasicoherent
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The hyperplane restriction sequences on `ℙⁿ_k`

Let `k` be an infinite field, let `N = m + 1 ≥ 1` and let `ℱ` be a coherent sheaf on `ℙᴺ_k`.
This file constructs, with no hypothesis beyond those, a hyperplane `j : ℙᵐ_k ⟶ ℙᴺ_k`, the
coherent restriction `𝒢 = j^*ℱ` of `ℱ` to it, and for every twist `d` the short exact sequence

`0 ⟶ ℱ(d-1) ⟶ ℱ(d) ⟶ j_*𝒢(d) ⟶ 0`

of [Stacks, Tag 08A0] twisted as in [Stacks, Tag 0EGK], with the hyperplane identified with
`ℙᵐ_k` as in [Stacks, Tag 089Z]. This is exactly the data that the induction of
[Stacks, Tag 08A6] consumes.

## Main results

* `AlgebraicGeometry.exists_form_section_nonvanishing`: **the hyperplane section of
  [Stacks, Tag 08A0] on the base-change model.** Over an infinite field, every coherent sheaf on
  `ℙⁿ_k = AlgebraicGeometry.projectiveSpaceOverRing n k` admits a global section of `𝒪(1)` that
  vanishes at no associated point of it and that corresponds to a nonzero degree-one form on
  `Proj k[T₀, …, Tₙ]`.
* `AlgebraicGeometry.exists_iso_zeroScheme_projectiveSpaceOverRing`: **[Stacks, Tag 089Z] on the
  base-change model.** The zero scheme of such a section is isomorphic to `ℙ^{n-1}_k`, and
  `𝒪(1)` pulls back to `𝒪(1)` along the composite with the inclusion.
* `AlgebraicGeometry.HasMulRestrictionSequences`: the restriction sequences in the shape the
  induction of [Stacks, Tag 08A7] consumes — first arrow multiplication by the section on the
  nose.
* `AlgebraicGeometry.exists_restrictionSequences`: **the twisted restriction sequences**, in
  that shape and in the shape [Stacks, Tag 0EGK] leaves them in.

## The mathematics

Three results from the library are glued together, each stated on a different model or at a
different
spelling, so the work is transport.

[Stacks, Tag 08A0] splits in two. Its short exact sequence,
`…ProjectiveSpaceHyperplaneSection.shortExact_hyperplaneUnit_of_nonvanishing` in
`StacksFrontier/AlgebraicGeometry/Constructions/ProjectiveSpaceHyperplaneSection.lean`,
holds on the base-change model `ℙⁿ_S` for an arbitrary module, on the single geometric
hypothesis that the chosen section of `𝒪(1)` does not vanish near any associated point of
`ℱ(-1)`. Its choice of such a section,
`…ProjectiveSpaceHyperplaneSection.exists_homogeneousSection_nonvanishing`, is made on the
`Proj k[T₀, …, Tₙ]` model, which is where a global section of `𝒪(1)` is a linear form and where
the "finite union of proper subspaces" argument over an infinite field lives. The two are
joined here: global sections of the two models' `𝒪(1)` correspond by
`Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso` read on `Γ(·, ⊤)`, associated
points correspond by `Stacks.Divisors.associatedPoints_pullback_of_iso`, and nonvanishing loci
correspond by [Stacks, Tag 0H78] (`Stacks.NonvanishingPullback.preimage_nonvanishingLocus`); the
comparison of models is a homeomorphism, so an inclusion of preimages is an inclusion.

[Stacks, Tag 089Z] is proved on the `Proj` model, for a hyperplane presented by a nonzero
degree-one form, as `Stacks.ProjectiveSpace.exists_iso_projectiveSpace_hyperplane`. It is moved
across the comparison of models by [Stacks, Tag 0B6Y]
(`Stacks.Divisors.zeroScheme_pullback`): the zero scheme of the transported section is the
inverse image of the zero scheme of the section, and the inverse image of an ideal sheaf along an
isomorphism has an isomorphic subscheme (`Stacks.Chow.comapSubschemeIsoOfIsIso`), compatibly with
the two closed immersions. The degree-one twist comparison is then transported by composing
pullbacks.

The first arrow of [Stacks, Tag 0EGK]'s twisted sequence is the twist of multiplication by the
section, not `…ProjectiveSpaceSectionMultiplication.twistSectionMul` on the nose; identifying
the two outright would need a coherence for the isomorphisms `𝒪(a) ⊗ 𝒪(b) ≅ 𝒪(a + b)` that this
development does not have.
`StacksFrontier/AlgebraicGeometry/Constructions/ProjectiveSpaceSectionMulShape.lean` supplies what
is needed instead: multiplication by the section is recognised only up to an isomorphism of the
target, which is a property closed under whiskering, and the isomorphism is then absorbed into
the sequence's second arrow.

[Stacks, Tag 0EGK] is proved at the `Stacks.Ample.tensorPowModule` spelling of the twists, as
`Stacks.AlgebraicGeometry.HyperplaneTwistSequence.shortExact_twistedSequence`. Its three terms
are moved to the `AlgebraicGeometry.projectiveTwist` spelling by
`Stacks.AlgebraicGeometry.ProjTwistTensorPow.tensorPowModuleProjectiveTwistIso`, and its third
term — a direct image along the hyperplane inclusion — is moved down to `ℙᵐ_k` by
`AlgebraicGeometry.Scheme.Modules.pushforwardObjIsoOfPullbackIso`, the unit of `φ^* ⊣ φ_*` being
invertible for an isomorphism `φ`. Only the three objects have to be matched, the restriction
sequences being asserted up to the choice of their two arrows.

## References

* [Stacks Project, Tag 08A0](https://stacks.math.columbia.edu/tag/08A0)
* [Stacks Project, Tag 089Z](https://stacks.math.columbia.edu/tag/089Z)
* [Stacks Project, Tag 0EGK](https://stacks.math.columbia.edu/tag/0EGK)
* [Stacks Project, Tag 0B6Y](https://stacks.math.columbia.edu/tag/0B6Y)
* [Stacks Project, Tag 0H78](https://stacks.math.columbia.edu/tag/0H78)
* [Stacks Project, Tag 01N2](https://stacks.math.columbia.edu/tag/01N2)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Opposite
open AlgebraicGeometry.ProjectiveSpectrum.Proj
open Stacks.AlgebraicGeometry.ProjTwistTensorPow Stacks.RelativeVeryAmple
open Stacks.ProjectiveCohomology (polyGrading projModelIso)

universe u

namespace AlgebraicGeometry

attribute [local instance] MvPolynomial.gradedAlgebra

/-! ### Global sections across an isomorphism of schemes -/

/-- **The transport of global sections across an isomorphism of schemes is the canonical
pullback of sections followed by the given isomorphism of modules.**
`AlgebraicGeometry.Scheme.Modules.gammaTopIsoOfPullbackIso` is built from the unit of
`f^* ⊣ f_*`, which is what `AlgebraicGeometry.pullbackGlobalSections` is; the two differ only by
the restriction along `⊤ = f^{-1}⊤`, which is the identity. -/
theorem Scheme.Modules.gammaTopIsoOfPullbackIso_hom_apply {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsIso f] {M : Y.Modules} {N : X.Modules}
    (e : (Scheme.Modules.pullback f).obj M ≅ N) (x : Γ(M, ⊤)) :
    ConcreteCategory.hom (Scheme.Modules.gammaTopIsoOfPullbackIso f e).hom x
      = ConcreteCategory.hom (Scheme.Modules.Hom.app e.hom ⊤)
        (pullbackGlobalSections f M x) := by
  rw [pullbackGlobalSections_eq_unit]
  simp only [Scheme.Modules.gammaTopIsoOfPullbackIso, Scheme.Modules.pushforwardGammaTopIso,
    Iso.trans_hom, asIso_hom, Functor.mapIso_hom]
  simp only [pushforward_obj_obj, TopologicalSpace.Opens.map_top, Functor.id_obj,
    Functor.comp_obj, Hom.comp_app, pushforward_map_app, Functor.op_obj, Iso.trans_hom,
    asIso_hom, Functor.mapIso_hom, Iso.op_hom, AddCommGrpCat.hom_comp, AddMonoidHom.coe_comp,
    Function.comp_apply]
  exact Functor.map_id_apply _ _ _

/-- The two spellings of the pullback of a global section agree: the one built from the unit of
`f^* ⊣ f_*` and the ringed-space one that the nonvanishing-locus API uses. -/
private theorem pullbackGlobalSections_eq_pullbackGlobalSection {X Y : Scheme.{u}} (f : X ⟶ Y)
    (M : Y.Modules) (s : Γ(M, ⊤)) :
    pullbackGlobalSections f M s = Stacks.NonvanishingPullback.pullbackGlobalSection f M s := by
  change ((Scheme.Modules.pullback f).obj M).presheaf.map
      (eqToHom (show f ⁻¹ᵁ (⊤ : Y.Opens) = ⊤ from rfl)).op
      (Stacks.NonvanishingPullback.pullbackGlobalSection f M s) = _
  exact Functor.map_id_apply _ _ _

/-- **[Stacks, Tag 0H78]** at the `AlgebraicGeometry.pullbackGlobalSections` spelling: the
nonvanishing locus of a pulled-back global section is the inverse image of the nonvanishing
locus. -/
@[ega "II 4.6.13.1" "more general"]
private theorem preimage_nonvanishingLocus_pullbackGlobalSections {X Y : Scheme.{u}}
    (f : X ⟶ Y) (M : Y.Modules) (s : Γ(M, ⊤)) :
    f ⁻¹' Stacks.Ample.nonvanishingLocus M s =
      Stacks.Ample.nonvanishingLocus ((Scheme.Modules.pullback f).obj M)
        (pullbackGlobalSections f M s) := by
  rw [pullbackGlobalSections_eq_pullbackGlobalSection]
  exact Stacks.NonvanishingPullback.preimage_nonvanishingLocus f M s

/-! ### Generic transport helpers -/

/-- Pulling back along a composite, as an isomorphism of objects, from the composite towards the
iterated pullback.  This is the direction opposite to
`AlgebraicGeometry.Scheme.Modules.pullbackCompObjIso`, which takes the composite as an equation. -/
private def Scheme.Modules.pullbackCompObjIsoSymm {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (A : Z.Modules) :
    (Scheme.Modules.pullback (f ≫ g)).obj A
      ≅ (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj A) :=
  ((Scheme.Modules.pullbackComp f g).app A).symm

/-- For an isomorphism `h : X ≅ Y` of schemes, an isomorphism `h^*M ≅ N` gives `(h⁻¹)^*N ≅ M`. -/
def Scheme.Modules.pullbackInvObjIso {X Y : Scheme.{u}} (h : X ≅ Y) {M : Y.Modules}
    {N : X.Modules} (e : (Scheme.Modules.pullback h.hom).obj M ≅ N) :
    (Scheme.Modules.pullback h.inv).obj N ≅ M :=
  (Scheme.Modules.pullback h.inv).mapIso e.symm ≪≫
    (Scheme.Modules.pullbackComp h.inv h.hom).app M ≪≫
    eqToIso (congrArg (fun φ => (Scheme.Modules.pullback φ).obj M) h.inv_hom_id) ≪≫
    (Scheme.Modules.pullbackId Y).app M

/-- For an isomorphism `h : X ≅ Y` of schemes, an isomorphism `N ≅ h^*M` gives `h_*N ≅ M`. -/
def Scheme.Modules.pushforwardObjIsoOfPullbackIso {X Y : Scheme.{u}} (h : X ≅ Y)
    {M : Y.Modules} {N : X.Modules} (e : N ≅ (Scheme.Modules.pullback h.hom).obj M) :
    (Scheme.Modules.pushforward h.hom).obj N ≅ M :=
  haveI := Stacks.AlgebraicGeometry.RelativeProjChain.isIso_pullbackPushforwardAdjunction_unit_app
    h.hom M
  (Scheme.Modules.pushforward h.hom).mapIso e ≪≫
    (asIso ((Scheme.Modules.pullbackPushforwardAdjunction h.hom).unit.app M)).symm

/-- **A short exact sequence transported along isomorphisms of its three terms.** The two arrows
are conjugated by the isomorphisms, so only the three objects have to be named. -/
theorem exists_shortExact_of_objIso {C : Type*} [Category C] [Abelian C] {S : ShortComplex C}
    (hS : S.ShortExact) {A₁ A₂ A₃ : C} (e₁ : S.X₁ ≅ A₁) (e₂ : S.X₂ ≅ A₂) (e₃ : S.X₃ ≅ A₃) :
    ∃ (a : A₁ ⟶ A₂) (b : A₂ ⟶ A₃) (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  refine ⟨e₁.inv ≫ S.f ≫ e₂.hom, e₂.inv ≫ S.g ≫ e₃.hom, ?_, ?_⟩
  · simp only [Category.assoc, Iso.hom_inv_id_assoc]
    rw [← Category.assoc S.f, S.zero, Limits.zero_comp, Limits.comp_zero]
  · exact ShortComplex.shortExact_of_iso
      (ShortComplex.isoMk e₁ e₂ e₃ (by simp) (by simp)) hS

/-! ### The hyperplane section of [Stacks, Tag 08A0] on the base-change model -/

/-- **The transport of global sections of `𝒪(1)` between the two models of `ℙⁿ_k`**, read on
`Γ(·, ⊤)`. -/
abbrev twistGammaTopIso (k : Type u) [Field k] (n : ℕ) :
    Γ(twistOver n (Spec (CommRingCat.of k)) 1, ⊤) ≅
      Γ(twistingSheafModule (polyGrading k n) (1 : ℤ), ⊤) :=
  Scheme.Modules.gammaTopIsoOfPullbackIso (projModelIso k n).hom
    (Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso k n 1)

/-- Transporting a global section of `𝒪(1)` from the base-change model to the `Proj` model by
pullback and by `twistGammaTopIso` agree. -/
private theorem hom_app_pullbackGlobalSections_twistOver (k : Type u) [Field k] (n : ℕ)
    (v : Γ(twistOver n (Spec (CommRingCat.of k)) 1, ⊤)) :
    ConcreteCategory.hom (Scheme.Modules.Hom.app
        (Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso k n 1).hom ⊤)
      (pullbackGlobalSections (projModelIso k n).hom (twistOver n (Spec (CommRingCat.of k)) 1) v)
      = ConcreteCategory.hom (twistGammaTopIso k n).hom v :=
  (Scheme.Modules.gammaTopIsoOfPullbackIso_hom_apply _ _ v).symm

/-- **The hyperplane section of [Stacks, Tag 08A0], on the base-change model of `ℙⁿ_k`.** Let `k`
be an infinite field and let `ℱ` be a coherent sheaf on
`AlgebraicGeometry.projectiveSpaceOverRing n k`. Then there are a nonzero degree-one form `f` on
`Proj k[T₀, …, Tₙ]` and a global section `v` of `𝒪(1)` on the base-change model which `f`
corresponds to under `AlgebraicGeometry.twistGammaTopIso`, and which vanishes at no associated
point of `ℱ`.

The choice of `f` is `…ProjectiveSpaceHyperplaneSection.exists_homogeneousSection_nonvanishing`,
made on the `Proj` model and applied to the inverse image of `ℱ`; it is the only step at which
`k` has to be infinite. Transporting it back uses that the comparison of models is an
isomorphism of schemes in three ways: it carries associated points to associated points, it
carries nonvanishing loci to nonvanishing loci ([Stacks, Tag 0H78]), and it is surjective on
points, so an inclusion between inverse images is an inclusion. -/
theorem exists_form_section_nonvanishing (k : Type u) [Field k] [Infinite k] (n : ℕ)
    (F : (projectiveSpaceOverRing n (CommRingCat.of k)).Modules) [F.IsCoherent] :
    ∃ (f : MvPolynomial (Fin (n + 1)) k) (hf : f ∈ polyGrading k n 1)
      (v : Γ(twistOver n (Spec (CommRingCat.of k)) 1, ⊤)),
      f ≠ 0 ∧
      ConcreteCategory.hom (twistGammaTopIso k n).hom v
        = degreeSection (polyGrading k n) 1 ⟨f, hf⟩ ∧
      Stacks.Divisors.associatedPoints F ⊆
        Stacks.Ample.nonvanishingLocus (twistOver n (Spec (CommRingCat.of k)) 1) v := by
  have : IsLocallyNoetherian (AlgebraicGeometry.Proj (polyGrading k n)) := inferInstance
  set g := (projModelIso k n).hom
  have : (((Scheme.Modules.pullback g).obj F)).IsCoherent := isCoherent_pullback g F
  obtain ⟨f, hf, hf0, hev, hsub⟩ :=
    Stacks.AlgebraicGeometry.ProjectiveSpaceHyperplaneSection.exists_homogeneousSection_nonvanishing
      k n ((Scheme.Modules.pullback g).obj F)
  refine ⟨f, hf, ConcreteCategory.hom (twistGammaTopIso k n).inv
    (degreeSection (polyGrading k n) 1 ⟨f, hf⟩), hf0, ?_, ?_⟩
  · exact Iso.inv_hom_id_apply (twistGammaTopIso k n) _
  · have hE := (hom_app_pullbackGlobalSections_twistOver k n
      (ConcreteCategory.hom (twistGammaTopIso k n).inv
        (degreeSection (polyGrading k n) 1 ⟨f, hf⟩))).trans
      (Iso.inv_hom_id_apply (twistGammaTopIso k n) _)
    have h1 := preimage_nonvanishingLocus_pullbackGlobalSections g
      (twistOver n (Spec (CommRingCat.of k)) 1)
      (ConcreteCategory.hom (twistGammaTopIso k n).inv
        (degreeSection (polyGrading k n) 1 ⟨f, hf⟩))
    have h2 := Stacks.Ample.nonvanishingLocus_congr
      (Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso k n 1)
      (pullbackGlobalSections g (twistOver n (Spec (CommRingCat.of k)) 1)
        (ConcreteCategory.hom (twistGammaTopIso k n).inv
          (degreeSection (polyGrading k n) 1 ⟨f, hf⟩)))
    rw [hE] at h2
    have h3 := Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq
      (AlgebraicGeometry.Proj (polyGrading k n))
      (twistingSheafModule (polyGrading k n) (1 : ℤ))
      (Stacks.ProjTwistSection.homogeneousSection (polyGrading k n) f hf)
    have hev' : PresheafOfModules.sections.eval
        (Stacks.ProjTwistSection.homogeneousSection (polyGrading k n) f hf) (op ⊤)
        = degreeSection (polyGrading k n) 1 ⟨f, hf⟩ :=
      Stacks.SheafOfModules.sectionsOfTop_eval_top _ _
    rw [Stacks.NonvanishingSpelling.sectionsEquiv_apply, hev'] at h3
    have hsurj : Function.Surjective (g : _ → _) := Surjective.surj
    refine hsurj.preimage_subset_preimage_iff.mp ?_
    rwa [h1, ← h2, ← h3, ← Stacks.Divisors.associatedPoints_pullback_of_iso (projModelIso k n) F]

/-! ### [Stacks, Tag 089Z] on the base-change model -/

/-- **[Stacks, Tag 089Z] on the base-change model of `ℙ^{m+1}_k`.** Let `v` be a global section
of `𝒪(1)` on `AlgebraicGeometry.projectiveSpaceOverRing (m + 1) k` corresponding to a nonzero
degree-one form `f` on `Proj k[T₀, …, T_{m+1}]`. Then the zero scheme of `v` is isomorphic to
`ℙᵐ_k`, and `𝒪(1)` pulls back to `𝒪(1)` along the composite of that isomorphism with the
inclusion of the zero scheme.

The statement is proved on the `Proj` model for the hyperplane of the form `f`
(`Stacks.ProjectiveSpace.exists_iso_projectiveSpace_hyperplane`). [Stacks, Tag 0B6Y] identifies
the inverse image of the zero scheme of `v` with the zero scheme of the transported section,
hence with that hyperplane; the inverse image of an ideal sheaf along an isomorphism has an
isomorphic subscheme over the ambient scheme, and the degree-one twist comparison is transported
by composing pullbacks.

The last clause records that the composite is a morphism **over `Spec k`**. On the `Proj` model
that is the last clause of `Stacks.ProjectiveSpace.exists_iso_projectiveSpace_hyperplane`, written
there with `AlgebraicGeometry.Proj.toSpecZero` and `Spec` of the constants, which is
`Stacks.ProjectiveCohomology.projModelToSpec` by
`Stacks.ProjectiveCohomology.toSpecZero_comp_Spec_map_ofHom_algebraMap`; the comparison of models
carries `projModelToSpec` to the structure morphism of the base-change model
(`Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism`), at both `m + 1` and `m`. -/
theorem exists_iso_zeroScheme_projectiveSpaceOverRing (k : Type u) [Field k] (m : ℕ)
    (f : MvPolynomial (Fin (m + 2)) k) (hf : f ∈ polyGrading k (m + 1) 1) (hf0 : f ≠ 0)
    (v : Γ(twistOver (m + 1) (Spec (CommRingCat.of k)) 1, ⊤))
    (hv : ConcreteCategory.hom (twistGammaTopIso k (m + 1)).hom v
      = degreeSection (polyGrading k (m + 1)) 1 ⟨f, hf⟩) :
    ∃ φ : projectiveSpaceOverRing m (CommRingCat.of k) ≅
        (AlgebraicGeometry.zeroScheme (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v).subscheme,
      Nonempty ((Scheme.Modules.pullback (φ.hom ≫
          (AlgebraicGeometry.zeroScheme (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
            (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v).subschemeι)).obj
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)
          ≅ twistOver m (Spec (CommRingCat.of k)) 1) ∧
      φ.hom ≫ (AlgebraicGeometry.zeroScheme
            (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
            (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v).subschemeι ≫
          (projectiveSpaceOverRing (m + 1) (CommRingCat.of k) ↘ Spec (CommRingCat.of k)) =
        projectiveSpaceOverRing m (CommRingCat.of k) ↘ Spec (CommRingCat.of k) := by
  set g := (projModelIso k (m + 1)).hom
  set J := AlgebraicGeometry.zeroScheme (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
    (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v with hJdef
  have hE := (hom_app_pullbackGlobalSections_twistOver k (m + 1) v).trans hv
  have hJ : J.comap g = Stacks.ProjectiveSpace.hyperplane ⟨f, hf⟩ := by
    rw [hJdef, ← Stacks.Divisors.zeroScheme_pullback g
      (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) v]
    exact AlgebraicGeometry.zeroScheme_eq_of_iso
      (Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso k (m + 1) 1) hE
  obtain ⟨φP, ⟨eP⟩, hover⟩ : ∃ φ : AlgebraicGeometry.Proj (polyGrading k m) ≅ (J.comap g).subscheme,
      Nonempty ((Scheme.Modules.pullback (φ.hom ≫ (J.comap g).subschemeι)).obj
        (twistingSheafModule (polyGrading k (m + 1)) (1 : ℤ))
          ≅ twistingSheafModule (polyGrading k m) (1 : ℤ)) ∧
      φ.hom ≫ (J.comap g).subschemeι ≫
          Stacks.ProjectiveCohomology.projModelToSpec k (m + 1) =
        Stacks.ProjectiveCohomology.projModelToSpec k m := by
    rw [hJ, ← Stacks.ProjectiveCohomology.toSpecZero_comp_Spec_map_ofHom_algebraMap k (m + 1),
      ← Stacks.ProjectiveCohomology.toSpecZero_comp_Spec_map_ofHom_algebraMap k m]
    exact Stacks.ProjectiveSpace.exists_iso_projectiveSpace_hyperplane ⟨f, hf⟩ hf0
  set χ := Stacks.Chow.comapSubschemeIsoOfIsIso g J
  have hcomp : ((projModelIso k m).symm ≪≫ φP ≪≫ χ).hom ≫ J.subschemeι
      = (projModelIso k m).inv ≫ ((φP.hom ≫ (J.comap g).subschemeι) ≫ g) := by
    simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc]
    rw [Stacks.Chow.comapSubschemeIsoOfIsIso_hom_subschemeι]
  refine ⟨(projModelIso k m).symm ≪≫ φP ≪≫ χ, ⟨?_⟩, ?_⟩
  swap
  · have hstr1 : g ≫ (projectiveSpaceOverRing (m + 1) (CommRingCat.of k) ↘
          Spec (CommRingCat.of k)) =
        Stacks.ProjectiveCohomology.projModelToSpec k (m + 1) :=
      Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism k (m + 1)
    have hstr0 : (projModelIso k m).hom ≫ (projectiveSpaceOverRing m (CommRingCat.of k) ↘
          Spec (CommRingCat.of k)) =
        Stacks.ProjectiveCohomology.projModelToSpec k m :=
      Stacks.ProjectiveCohomology.projModelIso_hom_structureMorphism k m
    rw [← Category.assoc, hcomp]
    simp only [Category.assoc]
    rw [hstr1, hover, ← hstr0, Iso.inv_hom_id_assoc]
  refine eqToIso (congrArg
    (fun ψ => (Scheme.Modules.pullback ψ).obj (twistOver (m + 1) (Spec (CommRingCat.of k)) 1))
      hcomp) ≪≫ ?_
  refine Scheme.Modules.pullbackCompObjIsoSymm (projModelIso k m).inv
      ((φP.hom ≫ (J.comap g).subschemeι) ≫ g) _ ≪≫ ?_
  refine (Scheme.Modules.pullback (projModelIso k m).inv).mapIso
      (Scheme.Modules.pullbackCompObjIsoSymm (φP.hom ≫ (J.comap g).subschemeι) g _) ≪≫ ?_
  refine (Scheme.Modules.pullback (projModelIso k m).inv).mapIso
      ((Scheme.Modules.pullback (φP.hom ≫ (J.comap g).subschemeι)).mapIso
        (Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso k (m + 1) 1)) ≪≫ ?_
  exact (Scheme.Modules.pullback (projModelIso k m).inv).mapIso eP ≪≫
    Scheme.Modules.pullbackInvObjIso (projModelIso k m)
      (Stacks.ProjectiveCohomology.pullbackProjModelIsoHomTwistOverIso k m 1)

/-! ### The twisted hyperplane restriction sequences -/

section Sequences

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

open CategoryTheory.MonoidalCategory
open Stacks.AlgebraicGeometry.HyperplaneTwistSequence
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMultiplication
open Stacks.AlgebraicGeometry.ProjectiveSpaceHyperplaneSection
  (shortExact_hyperplaneUnit_of_nonvanishing)
open Stacks.AlgebraicGeometry.ProjectiveSpaceSectionMulShape (IsSectionMul
  isSectionMul_twistSectionMulNegOne exists_shortExact_twistSectionMul_of_objIso)

/-- **The twisted hyperplane restriction sequences in the form the induction of
[Stacks, Tag 08A7] consumes**: for every `d` a short exact sequence

`0 ⟶ ℱ(d) ⟶ ℱ(d+1) ⟶ j_*(𝒢(d+1)) ⟶ 0`

whose first arrow is, on the nose, multiplication by the global section `s` of `𝒪(1)`
(`…ProjectiveSpaceSectionMultiplication.twistSectionMul`) — and not merely the twist of
multiplication by `s`, which is the shape [Stacks, Tag 0EGK] leaves it in. -/
def HasMulRestrictionSequences (k : Type u) [Field k] (m : ℕ)
    (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules)
    (G : (projectiveSpaceOverRing m (CommRingCat.of k)).Modules)
    (j : projectiveSpaceOverRing m (CommRingCat.of k) ⟶
      projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
    (s : (twistOver (m + 1) (Spec (CommRingCat.of k)) 1).sections) : Prop :=
  ∀ d : ℤ, ∃ (b : projectiveTwist (m + 1) F (d + 1) ⟶
      (Scheme.Modules.pushforward j).obj (projectiveTwist m G (d + 1)))
    (w : twistSectionMul (m + 1) (Spec (CommRingCat.of k)) F s d ≫ b = 0),
    (ShortComplex.mk (twistSectionMul (m + 1) (Spec (CommRingCat.of k)) F s d) b w).ShortExact

/-- The pullback to `ℙᵐ_k` of the `e`-th twist of the restriction of `ℱ` to the hyperplane cut
out by `s` is the `e`-th twist of the restriction of `ℱ` along `φ ≫ i`. -/
private def pullbackHyperplaneTwistIso (k : Type u) [Field k] (m : ℕ)
    (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules)
    (s : (twistOver (m + 1) (Spec (CommRingCat.of k)) 1).sections)
    (φ : projectiveSpaceOverRing m (CommRingCat.of k) ≅
      (hyperplane (m + 1) (Spec (CommRingCat.of k)) s).subscheme)
    (eφ : (Scheme.Modules.pullback (φ.hom ≫ hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) ≅ twistOver m (Spec (CommRingCat.of k)) 1)
    (e : ℤ) :
    (Scheme.Modules.pullback φ.hom).obj
        (twistModule _
          ((Scheme.Modules.pullback (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj
            (twistOver (m + 1) (Spec (CommRingCat.of k)) 1))
          ((Scheme.Modules.pullback (hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj F) e)
      ≅ projectiveTwist m
        ((Scheme.Modules.pullback (φ.hom ≫ hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj F)
        e :=
  let i := hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s
  pullbackTensorModulesIso φ.hom ((Scheme.Modules.pullback i).obj F)
      (Stacks.Ample.tensorPowModule _ ((Scheme.Modules.pullback i).obj
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)) e) ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso _ (Iso.refl _)
      (pullbackTensorPowModuleIntIso φ.hom ((Scheme.Modules.pullback i).obj
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)) e) ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso _
      (Scheme.Modules.pullbackCompObjIsoSymm φ.hom i F).symm
      (tensorPowModuleIsoOfIsoInt _ _ (twistOver m (Spec (CommRingCat.of k)) 1)
        ((Scheme.Modules.pullbackCompObjIsoSymm φ.hom i
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)).symm ≪≫ eφ) e) ≪≫
    Stacks.RelativeVeryAmple.tensorModulesMapIso _ (Iso.refl _)
      (tensorPowModuleProjectiveTwistIso m (Spec (CommRingCat.of k)) e)

/-- **The restriction sequences in the shape of `AlgebraicGeometry.HasMulRestrictionSequences`**
for the hyperplane `j = φ ≫ i` cut out by `s`, from the short exactness of the untwisted sequence
of [Stacks, Tag 08A0]. -/
theorem hasMulRestrictionSequences_of_shortExact (k : Type u) [Field k] (m : ℕ)
    (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules)
    (s : (twistOver (m + 1) (Spec (CommRingCat.of k)) 1).sections)
    (φ : projectiveSpaceOverRing m (CommRingCat.of k) ≅
      (hyperplane (m + 1) (Spec (CommRingCat.of k)) s).subscheme)
    (eφ : (Scheme.Modules.pullback (φ.hom ≫ hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) ≅ twistOver m (Spec (CommRingCat.of k)) 1)
    (w : twistSectionMulNegOne (m + 1) (Spec (CommRingCat.of k)) F s ≫
      hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s = 0)
    (hSE : (ShortComplex.mk _ _ w).ShortExact) :
    HasMulRestrictionSequences k m F
      ((Scheme.Modules.pullback (φ.hom ≫ hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s)).obj F)
      (φ.hom ≫ hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s) s := by
  set i := hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s
  set G := (Scheme.Modules.pullback (φ.hom ≫ i)).obj F
  set τ := fun e : ℤ => Stacks.RelativeVeryAmple.tensorModulesMapIso
    (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) (Iso.refl F)
    (tensorPowModuleProjectiveTwistIso (m + 1) (Spec (CommRingCat.of k)) e)
  set fp := (τ (-1)).hom ≫ twistSectionMulNegOne (m + 1) (Spec (CommRingCat.of k)) F s with hfp
  have wp : fp ≫ hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s = 0 := by
    rw [hfp, Category.assoc, w, Limits.comp_zero]
  have hiso : (ShortComplex.mk (twistSectionMulNegOne (m + 1) (Spec (CommRingCat.of k)) F s)
        (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) w)
      ≅ ShortComplex.mk fp (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) wp :=
    ShortComplex.isoMk (τ (-1)).symm (Iso.refl _) (Iso.refl _) (by simp [hfp]) (by simp)
  have hSE' : (ShortComplex.mk fp
      (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) wp).ShortExact :=
    ShortComplex.shortExact_of_iso hiso hSE
  intro d
  have h0EGK := shortExact_twistedSequence i (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F
    ((Scheme.Modules.pullback i).obj F) fp
    (hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s) wp hSE' (d + 1)
  refine exists_shortExact_twistSectionMul_of_objIso (m + 1) (Spec (CommRingCat.of k)) F s d
    h0EGK ?_
    (τ (d + 1 - 1)) (τ (d + 1))
    (((Scheme.Modules.pushforward i).mapIso
      (Scheme.Modules.pushforwardObjIsoOfPullbackIso φ
        (pullbackHyperplaneTwistIso k m F s φ eφ (d + 1)).symm)).symm ≪≫
        (Scheme.Modules.pushforwardComp φ.hom i).app (projectiveTwist m G (d + 1)))
    (eqToIso (congrArg (projectiveTwist (m + 1) F) (show d = d + 1 - 1 by ring)))
  have hfpmul : IsSectionMul (m + 1) (Spec (CommRingCat.of k)) s fp := by
    rw [hfp]
    exact (isSectionMul_twistSectionMulNegOne (m + 1) (Spec (CommRingCat.of k)) F s).iso_comp
      (τ (-1))
  exact (((hfpmul.whiskerRight (Stacks.Ample.tensorPowModule
        (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) (d + 1))).comp_iso
      (tensorRightModulesObjIso (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F (d + 1))).iso_comp
    (twistTwistIso (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F (-1) (d + 1) ≪≫
      twistModuleCongr (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) F
        (show (-1 : ℤ) + (d + 1) = d + 1 - 1 by ring)).symm)

/-- **The restriction sequences of `AlgebraicGeometry.HasMulRestrictionSequences`, reindexed**
so that the middle term is `ℱ(d)`. -/
theorem HasMulRestrictionSequences.exists_shortExact {k : Type u} [Field k] {m : ℕ}
    {F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules}
    {G : (projectiveSpaceOverRing m (CommRingCat.of k)).Modules}
    {j : projectiveSpaceOverRing m (CommRingCat.of k) ⟶
      projectiveSpaceOverRing (m + 1) (CommRingCat.of k)}
    {s : (twistOver (m + 1) (Spec (CommRingCat.of k)) 1).sections}
    (h : HasMulRestrictionSequences k m F G j s) (d : ℤ) :
    ∃ (a : projectiveTwist (m + 1) F (d - 1) ⟶ projectiveTwist (m + 1) F d)
      (b : projectiveTwist (m + 1) F d ⟶
        (Scheme.Modules.pushforward j).obj (projectiveTwist m G d))
      (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  obtain ⟨b, w, hSE⟩ := h (d - 1)
  exact exists_shortExact_of_objIso hSE (Iso.refl _)
    (eqToIso (congrArg (projectiveTwist (m + 1) F) (show d - 1 + 1 = d by ring)))
    (eqToIso (congrArg (fun e => (Scheme.Modules.pushforward j).obj (projectiveTwist m G e))
      (show d - 1 + 1 = d by ring)))

/-- **The section and short exact sequence of [Stacks, Tag 08A0] on `ℙ^{m+1}_k`.** Over an
infinite field, a coherent `ℱ` admits a global section `s` of `𝒪(1)`, corresponding to a nonzero
degree-one form, for which `0 ⟶ ℱ(-1) ⟶ ℱ ⟶ i_*i^*ℱ ⟶ 0` is short exact. -/
theorem exists_form_section_shortExact_hyperplaneUnit (k : Type u) [Field k] [Infinite k]
    (m : ℕ) (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules) [F.IsCoherent] :
    ∃ (f : MvPolynomial (Fin (m + 2)) k) (hf : f ∈ polyGrading k (m + 1) 1) (_ : f ≠ 0)
      (s : (twistOver (m + 1) (Spec (CommRingCat.of k)) 1).sections)
      (_ : ConcreteCategory.hom (twistGammaTopIso k (m + 1)).hom
          (PresheafOfModules.sections.eval s (op ⊤))
        = degreeSection (polyGrading k (m + 1)) 1 ⟨f, hf⟩)
      (w : twistSectionMulNegOne (m + 1) (Spec (CommRingCat.of k)) F s ≫
        hyperplaneUnit (m + 1) (Spec (CommRingCat.of k)) F s = 0),
      (ShortComplex.mk _ _ w).ShortExact := by
  have : IsLocallyNoetherian (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) :=
    projectiveSpaceOver_isLocallyNoetherian (m + 1) (Spec (CommRingCat.of k))
  have : (projectiveTwist (m + 1) F (-1)).IsCoherent :=
    isCoherent_projectiveTwist (m + 1) F (-1)
  obtain ⟨f, hf, v, hf0, hv, hsub⟩ :=
    exists_form_section_nonvanishing k (m + 1) (projectiveTwist (m + 1) F (-1))
  set s := (Stacks.NonvanishingSpelling.sectionsEquiv
    (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
    (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)).symm v with hs
  have hsv : PresheafOfModules.sections.eval s (op ⊤) = v := by
    rw [hs, ← Stacks.NonvanishingSpelling.sectionsEquiv_apply, Equiv.apply_symm_apply]
  rw [← hsv] at hv hsub
  have hnv : Stacks.SheafOfModules.nonvanishingLocus
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) s
      = Stacks.Ample.nonvanishingLocus (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)
        (PresheafOfModules.sections.eval s (op ⊤)) :=
    Stacks.NonvanishingSpelling.stalkNonvanishingLocus_eq
      (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
      (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) s
  have hW : ∀ x ∈ Stacks.Divisors.associatedPoints
      (Stacks.RelativeVeryAmple.tensorModules
        (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) F
        (twistOver (m + 1) (Spec (CommRingCat.of k)) (-1))),
      ∃ W : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Opens, x ∈ W ∧ ∀ y ∈ W,
        y ∈ Stacks.SheafOfModules.nonvanishingLocus
          (twistOver (m + 1) (Spec (CommRingCat.of k)) 1) s := by
    intro x hx
    refine ⟨Stacks.NonvanishingOpen.nonvanishingOpen
      (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
      (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)
      (PresheafOfModules.sections.eval s (op ⊤)), hsub hx, fun y hy => ?_⟩
    rwa [hnv]
  have : F.IsQuasicoherent := isQuasicoherent_of_isCoherent F
  have : (Stacks.RelativeVeryAmple.tensorModules
          (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) F
        (twistOver (m + 1) (Spec (CommRingCat.of k)) (-1))
      ⊗ twistOver (m + 1) (Spec (CommRingCat.of k)) 1).IsQuasicoherent :=
    (SheafOfModules.isQuasicoherent
        (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).ringCatSheaf).prop_of_iso
      (Stacks.AmplePullbackPart1.tensorIsoTensorModules
        (projectiveSpaceOverRing (m + 1) (CommRingCat.of k))
        (Stacks.RelativeVeryAmple.tensorModules
          (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) F
          (twistOver (m + 1) (Spec (CommRingCat.of k)) (-1)))
        (twistOver (m + 1) (Spec (CommRingCat.of k)) 1)).symm
      inferInstance
  obtain ⟨w, hSE⟩ :=
    shortExact_hyperplaneUnit_of_nonvanishing (m + 1) (Spec (CommRingCat.of k)) F s hW
  exact ⟨f, hf, hf0, s, hv, w, hSE⟩

/-- **The twisted hyperplane restriction sequences of [Stacks, Tag 08A0] and
[Stacks, Tag 0EGK], over an infinite field.** Let `k` be an infinite field and let `ℱ` be a
coherent sheaf on `ℙ^{m+1}_k`. Then there are a coherent sheaf `𝒢` on `ℙᵐ_k` and an affine
morphism `j : ℙᵐ_k ⟶ ℙ^{m+1}_k` such that for every `d ∈ ℤ` the sequence

`0 ⟶ ℱ(d-1) ⟶ ℱ(d) ⟶ j_*𝒢(d) ⟶ 0`

is short exact.

`j` is the inclusion of the hyperplane cut out by the section of
`AlgebraicGeometry.exists_form_section_nonvanishing`, composed with the identification of that
hyperplane with `ℙᵐ_k` of [Stacks, Tag 089Z]; it is affine because a closed immersion is and an
isomorphism is. `𝒢` is `j^*ℱ`, coherent by [Stacks, Tag 0EBF]. Short exactness is
[Stacks, Tag 0EGK] applied to the untwisted sequence of [Stacks, Tag 08A0], whose only
hypothesis — that the section does not vanish near an associated point of `ℱ(-1)` — is what the
choice of the section provides, `ℱ(-1)` being coherent. The index is written `m + 1` rather than
`n` with `1 ≤ n` so that the hyperplane is `ℙᵐ_k` with no truncated subtraction.

`j` is moreover a morphism **over `Spec k`**: it carries the structure morphism of `ℙ^{m+1}_k` to
that of `ℙᵐ_k`. That is the last clause of
`AlgebraicGeometry.exists_iso_zeroScheme_projectiveSpaceOverRing` composed with the fact that the
inclusion of a closed subscheme of `ℙ^{m+1}_k` is a morphism over `ℙ^{m+1}_k` by construction.
It is what makes `j` proper and the comparison of cohomologies along it `k`-linear, hence what
lets an Euler characteristic be transported down to `ℙᵐ_k`.

`j` is recorded to be a **closed immersion**, not only affine: that is the hypothesis of
`AlgebraicGeometry.cohomologyOverFieldPushforwardIsoOfIsClosedImmersion`, which together with
the over-`Spec k` clause identifies cohomology on `ℙᵐ_k` with cohomology of the direct image on
`ℙ^{m+1}_k` (`AlgebraicGeometry.projectiveHPushforwardIso`). -/
@[sga "6 XIII 6.4" "partial"]
theorem exists_restrictionSequences (k : Type u) [Field k] [Infinite k] (m : ℕ)
    (F : (projectiveSpaceOverRing (m + 1) (CommRingCat.of k)).Modules) (hFc : F.IsCoherent) :
    ∃ (G : (projectiveSpaceOverRing m (CommRingCat.of k)).Modules) (_ : G.IsCoherent)
      (j : projectiveSpaceOverRing m (CommRingCat.of k) ⟶
        projectiveSpaceOverRing (m + 1) (CommRingCat.of k)) (_ : IsAffineHom j)
      (_ : j ≫ (projectiveSpaceOverRing (m + 1) (CommRingCat.of k) ↘
          Spec (CommRingCat.of k)) =
        projectiveSpaceOverRing m (CommRingCat.of k) ↘ Spec (CommRingCat.of k))
      (_ : IsClosedImmersion j)
      (s : (twistOver (m + 1) (Spec (CommRingCat.of k)) 1).sections),
      HasMulRestrictionSequences k m F G j s ∧
      ∀ d : ℤ, ∃ (a : projectiveTwist (m + 1) F (d - 1) ⟶ projectiveTwist (m + 1) F d)
        (b : projectiveTwist (m + 1) F d ⟶
          (Scheme.Modules.pushforward j).obj (projectiveTwist m G d))
        (w : a ≫ b = 0), (ShortComplex.mk a b w).ShortExact := by
  have : F.IsCoherent := hFc
  have : IsLocallyNoetherian (projectiveSpaceOverRing m (CommRingCat.of k)) :=
    projectiveSpaceOver_isLocallyNoetherian m (Spec (CommRingCat.of k))
  obtain ⟨f, hf, hf0, s, hv, w, hSE⟩ := exists_form_section_shortExact_hyperplaneUnit k m F
  obtain ⟨φ, ⟨eφ⟩, hφover⟩ := exists_iso_zeroScheme_projectiveSpaceOverRing k m f hf hf0
    (PresheafOfModules.sections.eval s (op ⊤)) hv
  set i := hyperplaneι (m + 1) (Spec (CommRingCat.of k)) s with hi
  set j := φ.hom ≫ i with hj
  have : IsAffineHom j := by
    rw [hj]
    infer_instance
  have : IsClosedImmersion j := by
    rw [hj]
    infer_instance
  have hjover : j ≫ (projectiveSpaceOverRing (m + 1) (CommRingCat.of k) ↘
        Spec (CommRingCat.of k)) =
      projectiveSpaceOverRing m (CommRingCat.of k) ↘ Spec (CommRingCat.of k) := by
    rwa [hj, hi, Category.assoc]
  have : (Scheme.Modules.pullback j).obj F |>.IsCoherent := isCoherent_pullback j F
  exact ⟨_, inferInstance, j, inferInstance, hjover, inferInstance, s,
    hasMulRestrictionSequences_of_shortExact k m F s φ eφ w hSE,
    (hasMulRestrictionSequences_of_shortExact k m F s φ eφ w hSE).exists_shortExact⟩

end Sequences

end AlgebraicGeometry

end
