module

public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.DegreeZero
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.MonomialSectionTransport
public import StacksFrontier.AlgebraicGeometry.ProjectiveSpace.TwistSectionsAreForms
public import StacksFrontier.AlgebraicGeometry.ProperCoherentFiniteType.Basic
public import StacksFrontier.AlgebraicGeometry.Scheme.QuasiCoherent.AffineIsoCriterion
public import StacksFrontier.AlgebraicGeometry.Spaces.SliceAssociatedModuleFree
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasiCompactCoproductSections
public import StacksFrontier.RingTheory.MvPolynomial.HomogeneousBasis
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The degree-`d` part of `𝒪_S[T₀, …, Tₙ]` is `f_* 𝒪(d)` over a spectrum

Let `A` be a commutative ring, let `n` be a natural number, let `d` be an integer and let
`f : ℙⁿ_{Spec A} ⟶ Spec A` be the structure morphism of projective `n`-space. The canonical
morphism of `𝒪_{Spec A}`-modules

`(𝒪_{Spec A}[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)`

of `Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.toPushforwardTwistOver` is an
isomorphism whenever `0 ≤ d` or `n ≥ 1`. Both sides are quasi-coherent, so it suffices to invert
the morphism on global sections, and there the statement is that the degree-`d` forms in
`T₀, …, Tₙ` exhaust `Γ(ℙⁿ_A, 𝒪(d))` and are free on the degree-`d` monomials.

The names in the lists below are relative to the
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage` namespace.

## Main definitions

* `monomialIndexEquivDegree` and `monomialFormEquiv`: the degree-`m` multidegrees in the
  `ULift`ed variables are the degree-`m` multidegrees, and the degree-`m` part of
  `A[T₀, …, Tₙ]` is free on them.
* `specGlobalFunctions`: the coefficients as the global functions of `Spec A`.
* `monomialFormSection`: the degree-`m` section map read on the monomial coefficients, a map
  from the finitely supported families of coefficients to `Γ(ℙⁿ_A, 𝒪(m))`.

## Main results

* `app_top_freeSectionsMap_single`: **the canonical morphism on global sections.** It carries
  the global section of the free sheaf attached to a degree-`d` multidegree `e` and a regular
  function `r` on the base to `r` times the global section `T^e` of `𝒪(d)`.
* `canonicalTwistGammaTopIso_hom_smul`: the canonical identification of the two models'
  `Γ(𝒪(d), ⊤)` is semilinear over their global functions.
* `canonical_app_top_freeSectionsMap_single`: **the canonical morphism on global sections, read
  on the `Proj` model.** The basis vector of `T^e` scaled by a coefficient `a` goes to the
  degree-`m` section of the form `a T^e` of `A[T₀, …, Tₙ]`.
* `bijective_monomialFormSection`: **the degree-`m` forms are free on the degree-`m` monomials
  and exhaust `Γ(ℙⁿ_A, 𝒪(m))`.**
* `isIso_toPushforwardTwistOver_spec_natCast`: **the canonical morphism is an isomorphism over
  `Spec A` at a nonnegative twist.**
* `subsingleton_twistSections_of_neg` and `isIso_toPushforwardTwistOver_spec_neg`: for `n ≥ 1`
  and `d < 0` both sides vanish, so the canonical morphism is an isomorphism there too.
* `isIso_toPushforwardTwistOver_spec`: the two cases combined.

## The mathematics

Over a spectrum both sides of the canonical morphism are quasi-coherent — the source is free and
the target is a direct image of a quasi-coherent module along a proper, hence quasi-compact
quasi-separated, morphism — so `Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top`
reduces the assertion to bijectivity on global sections. The global sections of a free sheaf over
a quasi-compact open are the finitely supported families of regular functions
(`Stacks.Sites.bijective_freeSectionsMap`), and `Spec A` is quasi-compact, so the question is
whether

`(e ↦ aₑ) ↦ ∑ₑ aₑ T^e`

is a bijection from the finitely supported families of coefficients indexed by the degree-`d`
multidegrees onto `Γ(ℙⁿ_A, 𝒪(d))`.

Transport along `Stacks.ProjectiveCohomology.canonicalTwistGammaTopIso` puts the target on the
model `Proj A[T₀, …, Tₙ]`, where `Stacks.ProjectiveSpace.Cohomology.bijective_degreeSection`
says the degree-`d` section map is bijective on the degree-`d` forms and
`MvPolynomial.homogeneousSubmoduleEquivFinsupp` says those forms are free on the degree-`d`
monomials. The transport is semilinear rather than linear, over the map on global functions
induced by the comparison of the two models; that map carries the image of a coefficient under
the structure morphism of the base-change model to its image under the structure morphism of the
`Proj` model, which is `Stacks.ProjectiveSpace.Cohomology.coeffScalar`, the scalar action
`Stacks.ProjectiveSpace.Cohomology.degreeSection_smul` is stated for.

For `d < 0` the index set of multidegrees is empty, so the source has no nonzero global section;
and for `n ≥ 1` the target has none either, which is the degree-zero case of
[Stacks, Tag 01XT] outside its non-vanishing range. A morphism between two groups with no
nonzero element is bijective. The hypothesis `n ≥ 1` cannot be dropped: on `ℙ⁰_A = Spec A` the
variable `T₀` is invertible, so `𝒪(d) ≅ 𝒪` for every `d` and `Γ(ℙ⁰_A, 𝒪(d)) ≅ A` is nonzero
while the degree-`d` part of `A[T₀]` is zero for `d < 0`.

## Implementation notes

The scalars of the two sides are different rings: the global sections of a free sheaf on `Spec A`
are indexed families of elements of `Γ(Spec A, ⊤)` while the degree-`m` forms are a module over
`A`. The two are identified by `specGlobalFunctions`, and the identity of the two section maps is
checked on the generators `Finsupp.single e a` and extended by additivity with
`Finsupp.induction_linear`; the additivity steps are chains of `congrArg` rather than rewrites,
because the additive structures of a `ModuleCat` carrier and of the `Finsupp` it is built from
are the same term reached through different instance paths and a rewrite does not cross them.

**No `stacks` attribute is attached.** The degree-zero row of the display of [Stacks, Tag 01XW]
is the assertion over an arbitrary base, assembled in
`StacksFrontier/AlgebraicGeometry/ProjectiveSpaceHigherDirectImage/DegreeZeroRow.lean`, and a row of
that display is in any case only a component of the tag.

## References

* [Stacks Project, Tag 01XW](https://stacks.math.columbia.edu/tag/01XW)
* [Stacks Project, Tag 01XT](https://stacks.math.columbia.edu/tag/01XT)
* [Stacks Project, Tag 01MY](https://stacks.math.columbia.edu/tag/01MY)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ProjTwistTensorPow
open Stacks.ProjectiveCohomology

universe u

namespace Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

attribute [local instance] MvPolynomial.gradedAlgebra
attribute [local instance_reducible] ProjectiveSpectrum.top
attribute [local implicit_reducible] TopCat.Sheaf sheafCompose AlgebraicGeometry.Proj

/-! ### The canonical morphism on global sections -/

/-- The section of `f_* 𝒪(d)` named by `T^e` has, over the whole base, the value `T^e`. -/
theorem pushforwardTwistOverSection_val_top (n : ℕ) (S : Scheme.{u}) (d : ℤ)
    (e : MonomialIndex.{u} n d) :
    (pushforwardTwistOverSection n S d e).val (op ⊤) = twistOverSection n S d e := by
  rw [pushforwardTwistOverSection_val n S d e ⊤]
  exact Functor.map_id_apply _ _ _

/-- **The canonical morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)` on global sections.** The global
section of the free sheaf attached to a degree-`d` multidegree `e` and a regular function `r` on
the base goes to `r` times the global section `T^e` of `𝒪(d)`. -/
theorem app_top_freeSectionsMap_single (n : ℕ) (S : Scheme.{u}) (d : ℤ)
    (e : MonomialIndex.{u} n d) (r : Γ(S, ⊤)) :
    ((toPushforwardTwistOver n S d).val.app (op ⊤)).hom
        ((Stacks.Sites.freeSectionsMap (R := S.ringCatSheaf) (MonomialIndex.{u} n d)
          (op ⊤)).hom (Finsupp.single e r)) =
      (projectiveSpaceOver n S ↘ S).appTop r • twistOverSection n S d e :=
  (Stacks.SheafOfModules.freeHomEquiv_symm_val_app_freeSectionsMap_single
      ((Scheme.Modules.pushforward (projectiveSpaceOver n S ↘ S)).obj (twistOver n S d))
      (pushforwardTwistOverSection n S d) (op ⊤) e r).trans
    (congrArg (fun z : Γ(twistOver n S d, ⊤) =>
        (projectiveSpaceOver n S ↘ S).appTop r • z)
      (pushforwardTwistOverSection_val_top n S d e))

/-! ### The monomial basis of the degree-`m` forms -/

/-- The degree-`m` multidegrees in the `ULift`ed variables are the degree-`m` multidegrees. -/
def monomialIndexEquivDegree (n m : ℕ) :
    MonomialIndex.{u} n (m : ℤ) ≃ {e : Fin (n + 1) →₀ ℕ | e.degree = m} :=
  Equiv.subtypeEquiv
    (Finsupp.equivCongrLeft (Equiv.ulift : ULift.{u} (Fin (n + 1)) ≃ Fin (n + 1)))
    fun e => by
      simp only [Finsupp.equivCongrLeft_apply, Set.mem_ofPred_eq, degree_equivMapDomain_ulift]
      exact Nat.cast_inj

variable (A : Type u) [CommRing A] (n : ℕ)

/-- **The degree-`m` part of `A[T₀, …, Tₙ]` is free on the degree-`m` multidegrees.** -/
def monomialFormEquiv (m : ℕ) : (MonomialIndex.{u} n (m : ℤ) →₀ A) ≃ₗ[A]
    MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A m :=
  (Finsupp.domLCongr (monomialIndexEquivDegree.{u} n m)).trans
    (MvPolynomial.homogeneousSubmoduleEquivFinsupp (Fin (n + 1)) A m).symm

/-- The form attached to a single coefficient is the corresponding scaled monomial. -/
theorem coe_monomialFormEquiv_single (m : ℕ) (e : MonomialIndex.{u} n (m : ℤ)) (a : A) :
    ((monomialFormEquiv A n m (Finsupp.single e a) :
        MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A m) :
      MvPolynomial (Fin (n + 1)) A) = a • coordMonomialOver A e := by
  rw [monomialFormEquiv, LinearEquiv.trans_apply, Finsupp.domLCongr_single,
    MvPolynomial.coe_homogeneousSubmoduleEquivFinsupp_symm_single, coordMonomialOver,
    MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  rfl

/-! ### Transport to the `Proj` model -/

/-- The canonical identification of the two models' `Γ(𝒪(d), ⊤)` is semilinear over the map
their comparison induces on global functions. -/
theorem canonicalTwistGammaTopIso_hom_smul (d : ℤ)
    (c : Γ(projectiveSpaceOver n (Spec (CommRingCat.of A)), ⊤))
    (x : Γ(twistOver n (Spec (CommRingCat.of A)) d, ⊤)) :
    (canonicalTwistGammaTopIso A n d).hom (c • x) =
      (projModelIso A n).hom.appTop c • (canonicalTwistGammaTopIso A n d).hom x := by
  rw [canonicalTwistGammaTopIso,
    Scheme.Modules.gammaTopIsoOfPullbackIso_hom_apply,
    Scheme.Modules.gammaTopIsoOfPullbackIso_hom_apply,
    AlgebraicGeometry.SectionsEqualizer.pullbackGlobalSections_smul]
  exact ((canonicalPullbackProjModelIsoHomTwistOverIso A n d).hom.val.app
    (op ⊤)).hom.map_smul _ _

/-- The degree-`m` section map is linear over the coefficients, which act on the sections
through the structure morphism of the `Proj` model. -/
theorem degreeSection_coeffScalar_smul (m : ℕ) (a : A)
    (z : MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A m) :
    Stacks.ProjectiveSpace.Cohomology.coeffScalar A n a •
        AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
          (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A n) m z =
      AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A n) m (a • z) :=
  Stacks.ProjectiveSpace.Cohomology.degreeSection_smul A n m a z

/-- The two structure morphisms `Proj A[T₀, …, Tₙ] ⟶ Spec A` the development carries agree.

Kept private: the general form, universally quantified over the base ring, is
`Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage.projToSpecCoeff_eq_projModelToSpec`
in `…ProjectiveSpaceHigherDirectImage.TopDegreeAffineBase`. The two rows of [Stacks, Tag 01XW]
are independent, so this module does not import that one; the specialisation is re-proved here
instead, and hidden so that the two modules can be imported together. -/
private theorem projToSpecCoeff_eq_projModelToSpec :
    Stacks.AlgebraicGeometry.ProjPolyChart.projToSpecCoeff (CommRingCat.of A) n =
      projModelToSpec A n :=
  congrArg (fun φ => AlgebraicGeometry.Proj.toSpecZero
      (MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A) ≫ Spec.map φ)
    (polyDegreeZeroHom_eq A n)

/-- The comparison of models carries the structure morphism of the base-change model to the
structure morphism of the `Proj` model, read on global functions. -/
theorem projModelIso_hom_appTop_structureMorphism_appTop
    (r : Γ(Spec (CommRingCat.of A), ⊤)) :
    (projModelIso A n).hom.appTop
        ((projectiveSpaceOver n (Spec (CommRingCat.of A)) ↘
          Spec (CommRingCat.of A)).appTop r) =
      (projModelToSpec A n).appTop r := by
  conv_rhs => rw [← projModelIso_hom_structureMorphism A n]
  rw [Scheme.Hom.comp_appTop]
  rfl

/-- The structure morphism of the `Proj` model carries a coefficient to the global function it
names. -/
theorem projModelToSpec_appTop_ΓSpecIso_inv (a : A) :
    (projModelToSpec A n).appTop ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) =
      Stacks.ProjectiveSpace.Cohomology.coeffScalar A n a := by
  rw [← projToSpecCoeff_eq_projModelToSpec A n]
  rfl

/-- **The canonical morphism on global sections, read on the `Proj` model.** The basis vector of
the degree-`m` monomial `T^e` scaled by a coefficient `a` goes to the degree-`m` section of the
form `a T^e` of `A[T₀, …, Tₙ]`. -/
theorem canonical_app_top_freeSectionsMap_single (m : ℕ)
    (e : MonomialIndex.{u} n (m : ℤ)) (a : A) :
    (canonicalTwistGammaTopIso A n (m : ℤ)).hom
        (((toPushforwardTwistOver n (Spec (CommRingCat.of A)) (m : ℤ)).val.app (op ⊤)).hom
          ((Stacks.Sites.freeSectionsMap (R := (Spec (CommRingCat.of A)).ringCatSheaf)
              (MonomialIndex.{u} n (m : ℤ)) (op ⊤)).hom
            (Finsupp.single e ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a)))) =
      AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A n) m
        (monomialFormEquiv A n m (Finsupp.single e a)) := by
  obtain ⟨e, he⟩ := e
  have hdeg : e.degree = m := by exact_mod_cast he
  subst hdeg
  rw [app_top_freeSectionsMap_single, canonicalTwistGammaTopIso_hom_smul,
    projModelIso_hom_appTop_structureMorphism_appTop, projModelToSpec_appTop_ΓSpecIso_inv,
    canonicalTwistGammaTopIso_hom_twistOverSection]
  simp only [eqToHom_refl, Scheme.Modules.Hom.id_app]
  have hform : (a • (⟨coordMonomialOver A (⟨e, he⟩ : MonomialIndex.{u} n (e.degree : ℤ)),
        coordMonomialOver_mem A (⟨e, he⟩ : MonomialIndex.{u} n (e.degree : ℤ))⟩ :
      MvPolynomial.homogeneousSubmodule (Fin (n + 1)) A e.degree)) =
      monomialFormEquiv A n e.degree (Finsupp.single ⟨e, he⟩ a) :=
    Subtype.ext (coe_monomialFormEquiv_single A n e.degree ⟨e, he⟩ a).symm
  exact (degreeSection_coeffScalar_smul A n e.degree a _).trans
    (congrArg (AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A n) e.degree) hform)

/-! ### The isomorphism over a spectrum -/

/-- The coefficients as the global functions of the spectrum. -/
def specGlobalFunctions : A ≃+* Γ(Spec (CommRingCat.of A), ⊤) :=
  (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv

/-- The ring isomorphism `specGlobalFunctions A` sends `a : A` to its image under the inverse
of `Scheme.ΓSpecIso`. -/
@[simp] theorem specGlobalFunctions_apply (a : A) :
    specGlobalFunctions A a = (Scheme.ΓSpecIso (CommRingCat.of A)).inv a := rfl

/-- **The degree-`m` section map read on the monomial coefficients**: the map carrying a
finitely supported family of coefficients indexed by the degree-`m` multidegrees to the global
section of `𝒪(m)` on `ℙⁿ_A` attached to the corresponding form. -/
def monomialFormSection (m : ℕ) :
    (MonomialIndex.{u} n (m : ℤ) →₀ A) →ₗ[A]
      Stacks.ProjectiveSpace.Cohomology.twistSectionsModule A n (m : ℤ) :=
  (Stacks.ProjectiveSpace.Cohomology.degreeSectionLinear A n m).comp
    (monomialFormEquiv A n m).toLinearMap

/-- The map `monomialFormSection A n m` sends a family of coefficients `z` to the degree-`m`
section of the form `monomialFormEquiv A n m z`. -/
theorem monomialFormSection_apply (m : ℕ) (z : MonomialIndex.{u} n (m : ℤ) →₀ A) :
    monomialFormSection A n m z =
      AlgebraicGeometry.ProjectiveSpectrum.Proj.degreeSection
        (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A n) m
        (monomialFormEquiv A n m z) := rfl

/-- **The degree-`m` forms are free on the degree-`m` monomials and exhaust
`Γ(ℙⁿ_A, 𝒪(m))`.** -/
theorem bijective_monomialFormSection (m : ℕ) :
    Function.Bijective (monomialFormSection A n m) :=
  (Stacks.ProjectiveSpace.Cohomology.bijective_degreeSectionLinear n m).comp
    (monomialFormEquiv A n m).bijective

/-- The direct image of the twist along the structure morphism over a spectrum is
quasi-coherent. -/
private theorem isQuasicoherent_pushforward_twistOver_spec (d : ℤ) :
    ((Scheme.Modules.pushforward
      (projectiveSpaceOver n (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A))).obj
      (twistOver n (Spec (CommRingCat.of A)) d)).IsQuasicoherent :=
  ProperCoherentFiniteType.isQuasicoherent_pushforward _ _ inferInstance

/-- Free sections over the whole spectrum are the finitely supported families of global
functions. -/
private theorem bijective_freeSectionsMap_spec (ι : Type u) :
    Function.Bijective (Stacks.Sites.freeSectionsMap
      (R := (Spec (CommRingCat.of A)).ringCatSheaf) ι (op ⊤)).hom :=
  Stacks.Sites.bijective_freeSectionsMap _ ⊤
    (Stacks.SheafOfModules.isQuasiCompactObject_of_isCompact
      (X := TopCat.of ↥(Spec (CommRingCat.of A))) ⊤
      (by simpa using isCompact_univ (X := ↥(Spec (CommRingCat.of A)))))

/-- **The canonical morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)` is an isomorphism over the
spectrum of a commutative ring at a nonnegative twist.** -/
theorem isIso_toPushforwardTwistOver_spec_natCast (m : ℕ) :
    IsIso (toPushforwardTwistOver n (Spec (CommRingCat.of A)) (m : ℤ)) := by
  have hqc := isQuasicoherent_pushforward_twistOver_spec A n (m : ℤ)
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top _ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  set F := (Stacks.Sites.freeSectionsMap (R := (Spec (CommRingCat.of A)).ringCatSheaf)
    (MonomialIndex.{u} n (m : ℤ)) (op ⊤)).hom with hFdef
  set P := ((toPushforwardTwistOver n (Spec (CommRingCat.of A)) (m : ℤ)).val.app (op ⊤)).hom
    with hPdef
  set Q := ConcreteCategory.hom (canonicalTwistGammaTopIso A n (m : ℤ)).hom with hQdef
  set εE := (Finsupp.mapRange.addEquiv (specGlobalFunctions A).toAddEquiv :
    (MonomialIndex.{u} n (m : ℤ) →₀ A) ≃+
      (MonomialIndex.{u} n (m : ℤ) →₀ Γ(Spec (CommRingCat.of A), ⊤))) with hεdef
  have hF : Function.Bijective F := bijective_freeSectionsMap_spec A _
  have hQ : Function.Bijective Q := ConcreteCategory.bijective_of_isIso _
  have hε : Function.Bijective εE := εE.bijective
  have key : ∀ z : MonomialIndex.{u} n (m : ℤ) →₀ A,
      Q (P (F (εE z))) = monomialFormSection A n m z := by
    intro z
    induction z using Finsupp.induction_linear with
    | zero =>
        refine Eq.trans ?_ (map_zero (monomialFormSection A n m)).symm
        refine Eq.trans (congrArg (fun y => Q (P (F y))) (map_zero εE)) ?_
        refine Eq.trans (congrArg (fun y => Q (P y)) (map_zero F)) ?_
        exact (congrArg Q (map_zero P)).trans (map_zero Q)
    | add f g hf hg =>
        refine Eq.trans ?_ (((congrArg (fun y => y + Q (P (F (εE g)))) hf).trans
          (congrArg (fun y => monomialFormSection A n m f + y) hg)).trans
            (map_add (monomialFormSection A n m) f g).symm)
        refine Eq.trans (congrArg (fun y => Q (P (F y))) (map_add εE f g)) ?_
        refine Eq.trans (congrArg (fun y => Q (P y)) (map_add F (εE f) (εE g))) ?_
        exact (congrArg Q (map_add P (F (εE f)) (F (εE g)))).trans
          (map_add Q (P (F (εE f))) (P (F (εE g))))
    | single e a =>
        refine Eq.trans ?_ (monomialFormSection_apply A n m _).symm
        rw [hQdef, hPdef, hFdef, hεdef,
          show (Finsupp.mapRange.addEquiv (specGlobalFunctions A).toAddEquiv :
              (MonomialIndex.{u} n (m : ℤ) →₀ A) ≃+ _) (Finsupp.single e a) =
            Finsupp.single e ((Scheme.ΓSpecIso (CommRingCat.of A)).inv a) from
              Finsupp.mapRange_single (f := (specGlobalFunctions A).toAddEquiv)
                (hf := map_zero _)]
        exact canonical_app_top_freeSectionsMap_single A n m e a
  have hbij : Function.Bijective (fun z : MonomialIndex.{u} n (m : ℤ) →₀ A =>
      Q (P (F (εE z)))) := by
    simp only [key]
    exact bijective_monomialFormSection A n m
  have hg : Function.Bijective (fun z : MonomialIndex.{u} n (m : ℤ) →₀ A => F (εE z)) :=
    hF.comp hε
  exact (hQ.of_comp_iff' _).mp
    ((Function.Bijective.of_comp_iff (fun y => Q (P y)) hg).mp hbij)

/-- **In a negative degree `𝒪(d)` has no nonzero global section on `ℙⁿ_A`**, for `n ≥ 1`: this
is the degree-zero case of [Stacks, Tag 01XT] outside its non-vanishing range. -/
@[sga "6 XIII 2.5" "special case"]
theorem subsingleton_twistSections_of_neg (hn : 0 < n) {d : ℤ} (hd : d < 0) :
    Subsingleton Γ(twistOver n (Spec (CommRingCat.of A)) d, ⊤) := by
  have h0 : IsZero (Stacks.ProjectiveSpace.Cohomology.twistCohomology A n d 0) :=
    Stacks.ProjectiveSpace.Cohomology.isZero_twistCohomology A n d 0
      (by rintro (⟨-, h⟩ | ⟨h, -⟩) <;> omega)
  have h1 : Subsingleton (Stacks.ProjectiveSpace.Cohomology.twistSectionsModule A n d) :=
    ModuleCat.subsingleton_of_isZero
      (h0.of_iso (Stacks.ProjectiveSpace.Cohomology.twistCohomologyZeroIsoSections A n d).symm)
  have h2 : Subsingleton Γ(ProjectiveSpectrum.Proj.twistingSheafModule
      (Stacks.AlgebraicGeometry.ProjPolyChart.polyGrading A n) d, ⊤) := h1
  exact Function.Injective.subsingleton
    (ConcreteCategory.bijective_of_isIso (canonicalTwistGammaTopIso A n d).hom).injective

/-- **The canonical morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)` is an isomorphism over the
spectrum of a commutative ring at a negative twist in positive relative dimension**: there
neither side has a nonzero global section. -/
theorem isIso_toPushforwardTwistOver_spec_neg (hn : 0 < n) {d : ℤ} (hd : d < 0) :
    IsIso (toPushforwardTwistOver n (Spec (CommRingCat.of A)) d) := by
  have hqc := isQuasicoherent_pushforward_twistOver_spec A n d
  have : IsEmpty (MonomialIndex.{u} n d) := isEmpty_monomialIndex n hd
  have hsrc : Subsingleton Γ(baseDegreeSheaf n (Spec (CommRingCat.of A)) d, ⊤) :=
    (bijective_freeSectionsMap_spec A (MonomialIndex.{u} n d)).surjective.subsingleton
  have htgt : Subsingleton Γ((Scheme.Modules.pushforward
      (projectiveSpaceOver n (Spec (CommRingCat.of A)) ↘ Spec (CommRingCat.of A))).obj
      (twistOver n (Spec (CommRingCat.of A)) d), ⊤) :=
    subsingleton_twistSections_of_neg A n hn hd
  refine Stacks.AlgebraicGeometry.AffineBaseChange.isIso_of_isIso_app_top _ ?_
  rw [ConcreteCategory.isIso_iff_bijective]
  exact ⟨fun _ _ _ => Subsingleton.elim _ _, fun y => ⟨0, Subsingleton.elim _ _⟩⟩

/-- **The canonical morphism `(𝒪_S[T₀, …, Tₙ])_d ⟶ f_* 𝒪(d)` is an isomorphism over the
spectrum of a commutative ring**, in every degree `d` with `0 ≤ d` and, when `n ≥ 1`, in every
degree. -/
theorem isIso_toPushforwardTwistOver_spec {d : ℤ} (hd : 0 ≤ d ∨ 0 < n) :
    IsIso (toPushforwardTwistOver n (Spec (CommRingCat.of A)) d) := by
  rcases lt_or_ge d 0 with h | h
  · exact isIso_toPushforwardTwistOver_spec_neg A n (hd.resolve_left (by omega)) h
  · obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le h
    exact isIso_toPushforwardTwistOver_spec_natCast A n m

end Stacks.AlgebraicGeometry.ProjectiveSpaceHigherDirectImage

end
