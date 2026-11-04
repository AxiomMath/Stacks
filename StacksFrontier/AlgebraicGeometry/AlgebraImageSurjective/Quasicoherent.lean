module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.Quasicoherent
public import StacksFrontier.AlgebraicGeometry.AlgebraImageSurjective.Inputs

/-!
# Quasi-coherence of the image of a morphism of algebra sheaves

**The image of a morphism of quasi-coherent sheaves of `𝒪_X`-algebras is quasi-coherent.**  This
is Input 1 of [Stacks, Tag 05JT] as
`StacksFrontier/AlgebraicGeometry/FiniteTypeSubalgebraJoin/Directedness.lean` states it, and with
`StacksFrontier/AlgebraicGeometry/AlgebraImageSurjective/Inputs.lean` it leaves that tag with one
outstanding input instead of three.

The content is the identification that the `Directedness` file above names: the underlying
`𝒪_X`-module of the image *algebra* sheaf is the image of the underlying morphism of modules. Once
that is in hand the module-level closure fact is already available, as
`AlgebraicGeometry.isQuasicoherent_image`, for an arbitrary scheme.

## The identification

The image of `φ` in the category of algebra sheaves is a sheafification, so its underlying module
is not visibly an image of anything.  What makes the identification available is that the two
legs of the image factorisation have the right categorical properties *after* passing to modules,
and that the category of sheaves of modules is balanced:

* the corestriction `A ⟶ image φ` is locally surjective, by
  `Stacks.AlgebraImageSurjective.isLocallySurjective_factorThruImage_algebraSheaf`, hence its
  underlying morphism of modules is an **epimorphism** by
  `Stacks.SectionEpiAffine.epi_underlyingModuleMap_of_isLocallySurjective`;
* the inclusion `image φ ⟶ B` is a monomorphism of algebra sheaves, hence injective on sections,
  hence its underlying morphism of modules is a **monomorphism**;
* an epi-mono factorisation in a balanced category is the image, so the comparison morphism out
  of `CategoryTheory.Limits.image` is simultaneously a monomorphism and an epimorphism and
  therefore an isomorphism.

No `CategoryTheory.Limits.StrongEpi` is involved and no abelian-category image comparison is
built by hand: the comparison is `CategoryTheory.Limits.image.lift` of the explicit
factorisation, and the two properties are read off `CategoryTheory.Limits.image.lift_fac` and
`CategoryTheory.Limits.image.fac_lift` with `CategoryTheory.mono_of_mono_fac` and
`CategoryTheory.epi_of_epi_fac`.

Two names in scope here are `isFiniteType_image`, one in this namespace (from
`StacksFrontier/AlgebraicGeometry/AlgebraImageSurjective/Algebra.lean`, taking quasi-coherence of
the image as a hypothesis) and one in
`Stacks.AlgebraicGeometry.FiniteTypeSubalgebras` (taking Input 1 and Input 2 as hypotheses).  The
latter is written out in full below; leaving it unqualified resolves to the former
and fails with a type mismatch rather than an ambiguity error.

## Main results

* `Stacks.AlgebraImageSurjective.mono_underlyingModuleMap_of_mono`: the underlying morphism of
  modules of a monomorphism of algebra sheaves is a monomorphism.
* `Stacks.AlgebraImageSurjective.underlyingModuleImageIso`: **the identification**, as an
  isomorphism `image (underlyingModuleMap φ) ≅ underlyingModule (image φ)`.
* `Stacks.AlgebraImageSurjective.isQuasicoherent_image`: **the image of a morphism of
  quasi-coherent algebra sheaves is quasi-coherent.**
* `Stacks.AlgebraImageSurjective.imageIsQuasicoherent`: **Input 1, discharged.**
* `Stacks.AlgebraImageSurjective.nonempty_finiteTypeSubalgebra_of_isQuasicoherent`:
  **unconditional nonemptiness** of the finite type quasi-coherent subalgebras of a
  quasi-coherent algebra sheaf, with no hypothesis on `X`.
* `Stacks.AlgebraImageSurjective.isFiltered_of_dominating` and
  `Stacks.AlgebraImageSurjective.nonempty_isColimit_of_coprod`: the two assertions of
  [Stacks, Tag 05JT] with Inputs 1 and 2 both filled, so that the single remaining input is
  visible in the statement.

## Implementation notes

`Stacks.AlgebraImageSurjective.isQuasicoherent_image` is **not** a duplicate of
`AlgebraicGeometry.isQuasicoherent_image`: the latter is about sheaves of *modules* on a scheme
and is the input used here, while this one is about sheaves of *algebras*, whose images are
computed in a different category and whose quasi-coherence is a statement about the underlying
module.  The two live in different namespaces and neither can be stated at the other's signature.

Injectivity on sections of a monomorphism of algebra sheaves is obtained by stripping two layers:
`CategoryTheory.Under.mono_right_of_mono` takes the monomorphism under `𝒪_X` to a monomorphism
of sheaves of commutative rings, and `CategoryTheory.presheaf_mono_of_mono` with
`CategoryTheory.NatTrans.mono_iff_mono_app` takes that to a monomorphism of commutative rings at
each open, which is injective.  `Mono` is taken as an *explicit argument* rather than an instance
throughout, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/AlgebraImageSurjective/Transport.lean`: the ambient category
here is `TopCat.Sheaf`, whose category instance is not the one the Mathlib lemmas are stated
against, and only term-level application identifies the two.

`CategoryTheory.isIso_of_mono_of_epi` is not an instance and must be invoked by hand even with
both `Mono` and `Epi` in scope, which is why the isomorphism is produced by an explicit
`IsIso` step before `CategoryTheory.asIso`.

**No stacks attribute is attached.**  The assertions of [Stacks, Tag 05JT] still carry Input 3 as
a hypothesis -- and the colimit assertion the affine sections statement besides -- so neither is
proved here.

## References

* [Stacks Project, Tag 05JT](https://stacks.math.columbia.edu/tag/05JT)
* [Stacks Project, Tag 0817](https://stacks.math.columbia.edu/tag/0817)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry
open Stacks.RelativeSpec
open Stacks.AlgebraicGeometry.FiniteTypeSubalgebras

universe u

namespace Stacks.AlgebraImageSurjective

/-- A monomorphism of sheaves of commutative rings is injective on sections. -/
theorem injective_app_of_mono_sheaf {C : Type u} [Category.{u} C] (J : GrothendieckTopology C)
    {F G : Sheaf J CommRingCat.{u}} (f : F ⟶ G) (hf : Mono f) (U : Cᵒᵖ) :
    Function.Injective (f.hom.app U) := by
  have := hf
  have h1 : Mono f.hom := inferInstance
  have h2 : Mono (f.hom.app U) := (NatTrans.mono_iff_mono_app f.hom).mp h1 U
  exact (ConcreteCategory.injective_eq_monomorphisms (C := CommRingCat.{u})).ge
    (X := F.obj.obj U) (Y := G.obj.obj U) (f.hom.app U) h2

variable {X : Scheme.{u}}

/-- A monomorphism of algebra sheaves is injective on sections. -/
theorem injective_ringSheafMap_app_of_mono {A B : AlgebraSheaf X} (i : A ⟶ B) (hi : Mono i)
    (U : (X.Opens)ᵒᵖ) : Function.Injective ((AlgebraSheaf.ringSheafMap i).hom.app U) :=
  injective_app_of_mono_sheaf (_root_.Opens.grothendieckTopology X) i.right
    (have := hi; Under.mono_right_of_mono i) U

/-- **The underlying morphism of modules of a monomorphism of algebra sheaves is a
monomorphism.** -/
theorem mono_underlyingModuleMap_of_mono {A B : AlgebraSheaf X} (i : A ⟶ B) (hi : Mono i) :
    Mono (AlgebraSheaf.underlyingModuleMap i) :=
  have hinj : ∀ ⦃U : (X.Opens)ᵒᵖ⦄,
      Function.Injective ((AlgebraSheaf.underlyingModuleValMap i).app U) :=
    fun U => injective_ringSheafMap_app_of_mono i hi U
  (SheafOfModules.forget X.ringCatSheaf).mono_of_mono_map
    (PresheafOfModules.mono_of_injective hinj)

/-- **The underlying module of the image of a morphism of algebra sheaves is the image of the
underlying morphism of modules.**  The corestriction is an epimorphism of modules because it is
locally surjective, and the inclusion is a monomorphism of modules because it is injective on
sections; an epi-mono factorisation in a balanced category is the image. -/
noncomputable def underlyingModuleImageIso {A B : AlgebraSheaf X} (φ : A ⟶ B) :
    image (AlgebraSheaf.underlyingModuleMap φ) ≅ AlgebraSheaf.underlyingModule (image φ) :=
  have hfac : AlgebraSheaf.underlyingModuleMap (factorThruImage φ)
      ≫ AlgebraSheaf.underlyingModuleMap (image.ι φ)
      = AlgebraSheaf.underlyingModuleMap φ :=
    ((AlgebraSheaf.underlyingModuleFunctor X).map_comp (factorThruImage φ) (image.ι φ)).symm.trans
      (congrArg (AlgebraSheaf.underlyingModuleFunctor X).map (image.fac φ))
  have hp : Epi (AlgebraSheaf.underlyingModuleMap (factorThruImage φ)) :=
    Stacks.SectionEpiAffine.epi_underlyingModuleMap_of_isLocallySurjective (factorThruImage φ)
      (isLocallySurjective_factorThruImage_algebraSheaf φ)
  have hm : Mono (AlgebraSheaf.underlyingModuleMap (image.ι φ)) :=
    mono_underlyingModuleMap_of_mono (image.ι φ) inferInstance
  let F' : MonoFactorisation (AlgebraSheaf.underlyingModuleMap φ) :=
    { I := AlgebraSheaf.underlyingModule (image φ)
      m := AlgebraSheaf.underlyingModuleMap (image.ι φ)
      m_mono := hm
      e := AlgebraSheaf.underlyingModuleMap (factorThruImage φ)
      fac := hfac }
  have hu1 : image.lift F' ≫ AlgebraSheaf.underlyingModuleMap (image.ι φ)
      = image.ι (AlgebraSheaf.underlyingModuleMap φ) := image.lift_fac F'
  have hu2 : factorThruImage (AlgebraSheaf.underlyingModuleMap φ) ≫ image.lift F'
      = AlgebraSheaf.underlyingModuleMap (factorThruImage φ) := image.fac_lift F'
  have hmu : Mono (image.lift F') := mono_of_mono_fac hu1
  have heu : Epi (image.lift F') :=
    have := hp
    epi_of_epi_fac hu2
  have := hmu
  have := heu
  have : IsIso (image.lift F') := isIso_of_mono_of_epi _
  asIso (image.lift F')

/-- **The image of a morphism of quasi-coherent algebra sheaves is quasi-coherent.**  Its
underlying module is the image of the underlying morphism of modules, by
`underlyingModuleImageIso`, and the image of a morphism of quasi-coherent modules is
quasi-coherent by `AlgebraicGeometry.isQuasicoherent_image`. -/
theorem isQuasicoherent_image {A B : AlgebraSheaf X} (φ : A ⟶ B)
    (hA : AlgebraSheaf.IsQuasicoherent A) (hB : AlgebraSheaf.IsQuasicoherent B) :
    AlgebraSheaf.IsQuasicoherent (image φ) :=
  have := hA
  have := hB
  ObjectProperty.prop_of_iso (SheafOfModules.isQuasicoherent X.ringCatSheaf)
    (underlyingModuleImageIso φ)
    (_root_.AlgebraicGeometry.isQuasicoherent_image (AlgebraSheaf.underlyingModuleMap φ))

/-! ### Input 1, and what the two discharged inputs leave -/

/-- **Input 1 of [Stacks, Tag 05JT], discharged.** -/
theorem imageIsQuasicoherent (X : Scheme.{u}) : ImageIsQuasicoherent X :=
  fun _ _ φ hC hD => isQuasicoherent_image φ hC hD

/-- **The finite type quasi-coherent subalgebras of a quasi-coherent algebra sheaf are nonempty**
-- unconditionally.  Both image inputs are now discharged and the third is not needed here, the
witness being the image of the initial algebra sheaf. -/
theorem nonempty_finiteTypeSubalgebra_of_isQuasicoherent (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) : Nonempty (FiniteTypeSubalgebra A) :=
  nonempty_finiteTypeSubalgebra_of_imageIsQuasicoherent (imageIsQuasicoherent X) A hA

/-- **The image of a quasi-coherent algebra sheaf of finite type is of finite type**, with both
image inputs discharged. -/
theorem isFiniteType_image_of_isQuasicoherent {A C : AlgebraSheaf X} (φ : C ⟶ A)
    (hC : AlgebraSheaf.IsQuasicoherent C) (hA : AlgebraSheaf.IsQuasicoherent A)
    (hCft : AlgebraSheaf.IsFiniteType C) : AlgebraSheaf.IsFiniteType (image φ) :=
  Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiniteType_image
    (imageIsQuasicoherent X) (imageIsLocallySurjective X) φ hC hA hCft

/-- **The directedness assertion of [Stacks, Tag 05JT], granted Input 3 alone.** -/
theorem isFiltered_of_dominating (h₃ : ExistsFiniteTypeDominating X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) : IsFiltered (FiniteTypeSubalgebra A) :=
  isFiltered_of_imageIsQuasicoherent_of_dominating (imageIsQuasicoherent X) h₃ A hA

/-- **The directedness assertion of [Stacks, Tag 05JT] through the coproduct form of Input 3**,
i.e. `Stacks.AlgebraicGeometry.FiniteTypeSubalgebras.isFiltered_of_imageData` with slots 1 and 2
filled by this directory's theorems. -/
theorem isFiltered_of_coprod (h₃ : CoprodIsQuasicoherentFiniteType X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A) : IsFiltered (FiniteTypeSubalgebra A) :=
  isFiltered_of_imageData (imageIsQuasicoherent X) (imageIsLocallySurjective X) h₃ A hA

/-- **The colimit assertion of [Stacks, Tag 05JT], granted Input 3 and the affine sections
statement alone.** -/
theorem nonempty_isColimit_of_coprod [CompactSpace X] [QuasiSeparatedSpace X]
    (h₃ : CoprodIsQuasicoherentFiniteType X) (A : AlgebraSheaf X)
    (hA : AlgebraSheaf.IsQuasicoherent A)
    (hsec : ∀ U : X.Opens, IsAffineOpen U → ∀ x : A.right.obj.obj (Opposite.op U),
      ∃ (B : FiniteTypeSubalgebra A) (y : (B.obj : AlgebraSheaf X).right.obj.obj (Opposite.op U)),
        (B.obj.arrow.right.hom.app (Opposite.op U)) y = x) :
    Nonempty (IsColimit (finiteTypeSubalgebraCocone A)) :=
  nonempty_isColimit_of_imageIsQuasicoherent (imageIsQuasicoherent X) h₃ A hA hsec

end Stacks.AlgebraImageSurjective
