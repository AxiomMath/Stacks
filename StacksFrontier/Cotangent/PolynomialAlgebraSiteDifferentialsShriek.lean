module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.ProjectiveSections
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackModel
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ModulesOnACategory.DerivedPullbackOfModules
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteCoefficientChange
public import StacksFrontier.Cotangent.PolynomialAlgebraSiteModuleShriek
import StacksCore.Tactic.StacksAttribute

/-!
# The sheaf `Ω_{𝒪/A}` on the small model of `C_{B/A}`, and base change along `𝒪 ⟶ B̲`

Let `A → B` be a ring map and let `𝒪` be the structure presheaf of rings on the small model
`CommAlgCat.smallBoundedPolynomialSite A B κ` of the footnote-restricted site `C_{B/A}`, as in
`StacksFrontier/Cotangent/PolynomialAlgebraSiteCoefficientChange.lean`. That file carries `𝒪`, the
constant presheaf `B̲` and the augmentation `𝒪 ⟶ B̲`; this file adds the sheaf of relative
differentials `Ω_{𝒪/A}` there, with its sections `Ω[P⁄A]` in `Type u`, and the general
homological input that the comparison `Lπ_!(Ω_{𝒪/A}) = Lπ_!(Ω_{𝒪/A} ⊗_𝒪 B̲)` of
[Stacks, Tag 08QJ] needs at a sheaf which is only *objectwise* free, rather than projective as a
presheaf of modules.

**Why this is the obstruction.** The dévissage of [Stacks, Tag 08RX] carried by
`Stacks.ChaoticSite.quasiIso_mooreCochainUnit_app_of_projective` inverts the
change-of-coefficients unit at a *projective* presheaf of `𝒪`-modules. `Ω_{𝒪/A}` is not
projective — a natural family of derivations cannot be lifted coherently along an epimorphism —
but each of its sections `Ω[P⁄A]` is a free `P`-module. The passage from one to the other is the
source's step `Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}`, and in Lean it is the statement that extension of
scalars carries a projective resolution of `Ω_{𝒪/A}` to a resolution of `Ω_{𝒪/A} ⊗_𝒪 B̲`, which
is `Stacks.PullbackModel.quasiIso_extendScalars_of_projective_sections` below.

## Main definitions

* `KaehlerDifferential.congrAlgebraIso`: the differentials of two *equal* `A`-algebra structures
  on the same ring agree, with the universal derivations matching. This is what identifies the
  sections of Mathlib's
  `PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'`,
  which are formed for the algebra structure `(algebraMap A P).toAlgebra` induced by the ring
  map, with `Ω[P⁄A]` for the algebra structure instance resolution finds.
* `CommAlgCat.smallPolynomialStructureCommPresheaf`,
  `CommAlgCat.smallPolynomialConstantCommPresheaf` and
  `CommAlgCat.smallPolynomialAugmentationComm`: `𝒪`, `B̲` and `𝒪 ⟶ B̲` read as presheaves of
  *commutative* rings; each is the existing `RingCat`-valued construction on the nose.
* `CommAlgCat.smallPolynomialBaseCommPresheaf` and `CommAlgCat.smallPolynomialBaseHom`: the
  constant presheaf `A̲` and the map `A̲ ⟶ 𝒪` given by the `A`-algebra structures.
* `CommAlgCat.smallPolynomialDifferentials`: **`Ω_{𝒪/A}` on the small model**, the presheaf of
  relative differentials of `A̲ ⟶ 𝒪`, with sections in `Type u`.

## Main results

* `Stacks.PullbackModel.quasiIso_extendScalars_of_projective_sections`: **extension of scalars
  carries a projective resolution of a presheaf of modules with projective sections to a
  resolution of its base change.** Objectwise the two complexes are bounded above complexes of
  projective modules, so the resolution is a homotopy equivalence there, and an additive functor
  preserves homotopy equivalences.
* `CommAlgCat.smallPolynomialDifferentialsSectionsIso` and
  `CommAlgCat.free_smallPolynomialDifferentials_obj`: the sections of `Ω_{𝒪/A}` over `(P, α)` are
  `Ω[P⁄A]`, and they are free over `P` because `P` is a polynomial algebra over `A`.
* `CommAlgCat.projective_smallPolynomialDifferentials_obj`: hence the sections are projective,
  which is the hypothesis of
  `Stacks.PullbackModel.quasiIso_extendScalars_of_projective_sections`.

The two general inputs — that a projective presheaf of modules has projective sections, and that
evaluation detects quasi-isomorphisms — are
`PresheafOfModules.categoricalProjective_obj` and `PresheafOfModules.quasiIso_iff_evaluation` of
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/ProjectiveSections.lean`.

## References

* [Stacks Project, Tag 08PR](https://stacks.math.columbia.edu/tag/08PR)
* [Stacks Project, Tag 08PU](https://stacks.math.columbia.edu/tag/08PU)
* [Stacks Project, Tag 08QJ](https://stacks.math.columbia.edu/tag/08QJ)
* [Stacks Project, Tag 08RX](https://stacks.math.columbia.edu/tag/08RX)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks

section ZeroAndKProjective

/-- A functor preserving zero morphisms carries a zero object to a zero object. -/
lemma isZero_map {D₁ : Type*} [Category D₁] [Limits.HasZeroMorphisms D₁]
    {D₂ : Type*} [Category D₂] [Limits.HasZeroMorphisms D₂] (G : D₁ ⥤ D₂)
    [G.PreservesZeroMorphisms] {X : D₁} (hX : Limits.IsZero X) :
    Limits.IsZero (G.obj X) := by
  rw [Limits.IsZero.iff_id_eq_zero, ← G.map_id,
    (Limits.IsZero.iff_id_eq_zero X).1 hX, G.map_zero]

/-- The image of a complex supported in nonpositive degrees under a zero-morphism-preserving
functor is again supported in nonpositive degrees. -/
lemma isStrictlyLE_mapHomologicalComplex
    {D₁ : Type*} [Category D₁] [Limits.HasZeroMorphisms D₁]
    {D₂ : Type*} [Category D₂] [Limits.HasZeroMorphisms D₂] (G : D₁ ⥤ D₂)
    [G.PreservesZeroMorphisms] (X : CochainComplex D₁ ℤ) (n : ℤ)
    (h : CochainComplex.IsStrictlyLE X n) :
    CochainComplex.IsStrictlyLE ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) n := by
  have := h
  rw [CochainComplex.isStrictlyLE_iff]
  intro i hi
  exact isZero_map _ (CochainComplex.isZero_of_isStrictlyLE X n i hi)

/-- The image of a complex supported in nonpositive degrees under an additive functor is
K-projective as soon as its terms are projective. -/
private lemma isKProjective_mapHC
    {D₁ : Type*} [Category D₁] [Abelian D₁] {D₂ : Type*} [Category D₂] [Abelian D₂]
    (G : D₁ ⥤ D₂) [G.Additive]
    (X : CochainComplex D₁ ℤ) [CochainComplex.IsStrictlyLE X 0]
    (hp : ∀ i : ℤ, Projective (((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X).X i)) :
    CochainComplex.IsKProjective ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) := by
  let : CochainComplex.IsStrictlyLE
      ((G.mapHomologicalComplex (ComplexShape.up ℤ)).obj X) 0 :=
    isStrictlyLE_mapHomologicalComplex G X 0 inferInstance
  let := hp
  exact CochainComplex.isKProjective_of_projective _ 0

end ZeroAndKProjective


namespace PullbackModel

variable {C : Type u} [SmallCategory C] {O O' : Cᵒᵖ ⥤ CommRingCat.{u}} (α : O ⟶ O')

/-- **Extension of scalars carries a projective resolution of a presheaf of modules with
projective sections to a resolution of its base change.** This is the step
`Li^*ℱ = i^*ℱ` of [Stacks, Tag 08PU] and [Stacks, Tag 08QJ], for a sheaf `ℱ` which is only
objectwise projective rather than projective as a presheaf of modules.

The proof is objectwise: over each object the resolution and the single complex are both bounded
above complexes of projective modules, hence K-projective, so a quasi-isomorphism between them is
a homotopy equivalence ([Stacks, Tag 064B]); an additive functor preserves homotopy
equivalences; and a homotopy equivalence is a quasi-isomorphism. Evaluation then detects the
conclusion by `Stacks.PresheafOfModules.quasiIso_of_forall_evaluation`. -/
lemma quasiIso_extendScalars_of_projective_sections
    {K : CochainComplex (_root_.PresheafOfModules.{u}
      (O ⋙ forget₂ CommRingCat.{u} RingCat.{u})) ℤ}
    (hle : CochainComplex.IsStrictlyLE K 0) (hK : ∀ n : ℤ, Projective (K.X n))
    {F : _root_.PresheafOfModules.{u} (O ⋙ forget₂ CommRingCat.{u} RingCat.{u})}
    (hF : ∀ V : Cᵒᵖ, Projective (F.obj V))
    (f : K ⟶ (HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F) (hf : QuasiIso f) :
    QuasiIso ((((Stacks.PullbackModel.extendScalars α)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map f) := by
  have := hle
  have := hf
  rw [_root_.PresheafOfModules.quasiIso_iff_evaluation]
  intro V
  let EV := _root_.PresheafOfModules.evaluation.{u}
    (O ⋙ forget₂ CommRingCat.{u} RingCat.{u}) V
  have hfV : QuasiIso ((EV.mapHomologicalComplex (ComplexShape.up ℤ)).map f) :=
    (_root_.PresheafOfModules.quasiIso_iff_evaluation f).1 inferInstance V
  have hsrc : CochainComplex.IsKProjective
      ((EV.mapHomologicalComplex (ComplexShape.up ℤ)).obj K) :=
    isKProjective_mapHC EV K fun i => by
      have := hK i
      exact _root_.PresheafOfModules.categoricalProjective_obj (K.X i) V
  have htgt : CochainComplex.IsKProjective
      ((EV.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj F)) :=
    isKProjective_mapHC EV _ fun i => by
      by_cases hi : i = 0
      · subst hi
        exact Projective.of_iso
          (EV.mapIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F)).symm (hF V)
      · exact (isZero_map EV (HomologicalComplex.isZero_single_obj_X
          (ComplexShape.up ℤ) 0 F i hi)).projective
  obtain ⟨e, he⟩ := (CochainComplex.IsKProjective.quasiIso_iff
    ((EV.mapHomologicalComplex (ComplexShape.up ℤ)).map f)).1 inferInstance
  have hrfl : ((_root_.PresheafOfModules.evaluation.{u}
        (O' ⋙ forget₂ CommRingCat.{u} RingCat.{u}) V).mapHomologicalComplex
          (ComplexShape.up ℤ)).map
        (((Stacks.PullbackModel.extendScalars α).mapHomologicalComplex
          (ComplexShape.up ℤ)).map f) =
      ((ModuleCat.extendScalars ((α.app V).hom)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map ((EV.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := rfl
  rw [hrfl, ← he]
  exact ((ModuleCat.extendScalars ((α.app V).hom)).mapHomotopyEquiv e).quasiIso_hom

end PullbackModel

end Stacks

namespace KaehlerDifferential

variable {A P : Type u} [CommRing A] [CommRing P]

/-- **The differentials of two equal `A`-algebra structures agree.** This is the comparison that
identifies the sections of Mathlib's `relativeDifferentials'`, formed for the algebra structure
`(algebraMap A P).toAlgebra` that a ring map induces, with `Ω[P⁄A]` for the algebra structure
instance resolution finds: the two structures have the same `algebraMap`, hence are equal by
`Algebra.algebra_ext`, and the comparison is then the identity. -/
def congrAlgebraIso (i₁ i₂ : Algebra A P) (h : i₁ = i₂) :
    (letI := i₁; ModuleCat.of P (KaehlerDifferential A P)) ≅
      (letI := i₂; ModuleCat.of P (KaehlerDifferential A P)) := by
  subst h; exact Iso.refl _

/-- The comparison of `KaehlerDifferential.congrAlgebraIso` matches the universal derivations. -/
lemma congrAlgebraIso_hom_D (i₁ i₂ : Algebra A P) (h : i₁ = i₂) (b : P) :
    (congrAlgebraIso i₁ i₂ h).hom (letI := i₁; KaehlerDifferential.D A P b) =
      (letI := i₂; KaehlerDifferential.D A P b) := by
  subst h; rfl

end KaehlerDifferential

namespace CommAlgCat

variable (A : Type u) [CommRing A] (B : CommAlgCat.{u} A) (κ : Cardinal.{u})

/-! ### `𝒪`, `A̲` and `B̲` as presheaves of commutative rings -/

/-- **The tautological presheaf of commutative rings `𝒪` on the small model of `C_{B/A}`.** It is
`CommAlgCat.smallPolynomialStructurePresheaf` before the forgetful functor to `RingCat`, which is
the shape Mathlib's presheaf of relative differentials is stated for. -/
abbrev smallPolynomialStructureCommPresheaf :
    (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ CommRingCat.{u} :=
  smallSiteToOver A B κ ⋙ Over.forget B ⋙ forget₂ (CommAlgCat.{u} A) CommRingCat.{u}

/-- The structure presheaf of rings of the small model is the one above, read in `RingCat`. -/
lemma smallPolynomialStructureCommPresheaf_comp :
    smallPolynomialStructureCommPresheaf A B κ ⋙ forget₂ CommRingCat.{u} RingCat.{u} =
      smallPolynomialStructurePresheaf A B κ :=
  rfl

/-- **The constant presheaf of commutative rings `A̲` on the small model of `C_{B/A}`.** -/
abbrev smallPolynomialBaseCommPresheaf :
    (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const (smallBoundedPolynomialSite A B κ)ᵒᵖ).obj (CommRingCat.of A)

/-- **The map of presheaves of commutative rings `A̲ ⟶ 𝒪`**, given by the `A`-algebra structures
of the objects of the site. -/
def smallPolynomialBaseHom :
    smallPolynomialBaseCommPresheaf A B κ ⟶ smallPolynomialStructureCommPresheaf A B κ where
  app V := CommRingCat.ofHom (algebraMap A (((smallSiteToOver A B κ).obj V).left : Type u))
  naturality V W f := by
    refine CommRingCat.hom_ext (RingHom.ext fun a => ?_)
    exact (((smallSiteToOver A B κ).map f).left.hom.commutes a).symm

/-- **The constant presheaf of commutative rings `B̲` on the small model of `C_{B/A}`.** -/
abbrev smallPolynomialConstantCommPresheaf :
    (smallBoundedPolynomialSite A B κ)ᵒᵖ ⥤ CommRingCat.{u} :=
  (Functor.const (smallBoundedPolynomialSite A B κ)ᵒᵖ).obj (CommRingCat.of (B : Type u))

/-- The constant presheaf of rings of the small model is the one above, read in `RingCat`. -/
lemma smallPolynomialConstantCommPresheaf_comp :
    smallPolynomialConstantCommPresheaf A B κ ⋙ forget₂ CommRingCat.{u} RingCat.{u} =
      smallPolynomialConstantPresheaf A B κ :=
  rfl

/-- **The augmentation `𝒪 ⟶ B̲` as a map of presheaves of commutative rings.** -/
def smallPolynomialAugmentationComm :
    smallPolynomialStructureCommPresheaf A B κ ⟶ smallPolynomialConstantCommPresheaf A B κ where
  app V := (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).map ((smallSiteToOver A B κ).obj V).hom
  naturality V W f := by
    have hw := congrArg
      (fun g : ((smallSiteToOver A B κ).obj V).left ⟶ B =>
        (forget₂ (CommAlgCat.{u} A) CommRingCat.{u}).map g)
      (Over.w ((smallSiteToOver A B κ).map f))
    exact hw.trans (Category.comp_id _).symm

/-- The augmentation of presheaves of commutative rings is the `RingCat`-valued one, on the nose. -/
lemma toRingCat_smallPolynomialAugmentationComm :
    Stacks.PullbackModel.toRingCat (smallPolynomialAugmentationComm A B κ) =
      smallPolynomialAugmentation A B κ :=
  rfl

/-! ### `Ω_{𝒪/A}` on the small model -/

/-- **`Ω_{𝒪/A}` on the small model of the footnote-restricted site `C_{B/A}`**: the presheaf of
relative differentials of `A̲ ⟶ 𝒪`, whose sections over `(P, α)` are `Ω[P⁄A]`, in `Type u`. The
topology of `C_{B/A}` being chaotic, no sheafification intervenes and the sections are read off
objectwise.

This is the `Type u` model of the sheaf `CommAlgCat.polynomialRelativeDifferentials` of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteDifferentials.lean`, whose sections
`Ω[ULift P⁄ULift A]` live in `Type (u + 1)` because the morphism of topoi of [Stacks, Tag 08PR]
is formed at a coefficient universe at least `u + 1`; the relation between the two is the same as
between `CommAlgCat.smallPolynomialCotangentModulePresheaf` and
`CommAlgCat.polynomialRelativeDifferentialsBaseChange`. -/
def smallPolynomialDifferentials :
    PresheafOfModules.{u} (smallPolynomialStructurePresheaf A B κ) :=
  PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'
    (smallPolynomialBaseHom A B κ)

/-- The algebra structure induced by the structure map of an `A`-algebra is the one instance
resolution finds: both have `algebraMap a = algebraMap a`. -/
lemma algebraMap_toAlgebra_eq (P : CommAlgCat.{u} A) :
    (CommRingCat.ofHom (algebraMap A (P : Type u))).hom.toAlgebra =
      (inferInstance : Algebra A (P : Type u)) :=
  Algebra.algebra_ext _ _ fun _ => rfl

/-- **The sections of `Ω_{𝒪/A}` over `(P, α)` are `Ω[P⁄A]`**, by the comparison of the two
`A`-algebra structures on `P`. -/
def kaehlerDifferentialSectionsIso (P : CommAlgCat.{u} A) :
    CommRingCat.KaehlerDifferential (CommRingCat.ofHom (algebraMap A (P : Type u))) ≅
      ModuleCat.of (P : Type u) (KaehlerDifferential A (P : Type u)) :=
  KaehlerDifferential.congrAlgebraIso _ _ (algebraMap_toAlgebra_eq A P)

/-- The identification of the sections of `Ω_{𝒪/A}` matches the universal derivations. -/
lemma kaehlerDifferentialSectionsIso_hom_d (P : CommAlgCat.{u} A) (b : (P : Type u)) :
    (kaehlerDifferentialSectionsIso A P).hom (CommRingCat.KaehlerDifferential.d b) =
      KaehlerDifferential.D A (P : Type u) b :=
  KaehlerDifferential.congrAlgebraIso_hom_D _ _ (algebraMap_toAlgebra_eq A P) b

/-- **The differentials of each object of the small model of `C_{B/A}` are free over it**: the
object is a polynomial algebra over `A`, so its differentials are free on the variables. This is
the `Type u` form of `CommAlgCat.free_kaehlerDifferential_polynomialSite`. -/
lemma free_smallPolynomialDifferentials_obj
    (V : (smallBoundedPolynomialSite A B κ)ᵒᵖ) :
    Module.Free (((smallSiteToOver A B κ).obj V).left : Type u)
      (KaehlerDifferential A (((smallSiteToOver A B κ).obj V).left : Type u)) :=
  free_kaehlerDifferential_polynomialSite A B
    ((smallBoundedPolynomialSiteToPolynomialSite A B κ).obj V.unop)

/-- **The sections of `Ω_{𝒪/A}` are projective**, being free. This is the hypothesis under which
`Stacks.PullbackModel.quasiIso_extendScalars_of_projective_sections` identifies the derived base
change of `Ω_{𝒪/A}` with the underived one, which is the step `Li^*Ω_{𝒪/A} = i^*Ω_{𝒪/A}` of
[Stacks, Tag 08PU]. -/
lemma projective_smallPolynomialDifferentials_obj
    (V : (smallBoundedPolynomialSite A B κ)ᵒᵖ) :
    Projective ((smallPolynomialDifferentials A B κ).obj V) := by
  have := free_smallPolynomialDifferentials_obj A B κ V
  exact Projective.of_iso
    (kaehlerDifferentialSectionsIso A ((smallSiteToOver A B κ).obj V).left).symm
    (ModuleCat.projective_of_free
      (Module.Free.chooseBasis (((smallSiteToOver A B κ).obj V).left : Type u)
        (KaehlerDifferential A (((smallSiteToOver A B κ).obj V).left : Type u))))

/-- The identification of the sections of `Ω_{𝒪/A}`, read in the other direction. -/
lemma kaehlerDifferentialSectionsIso_inv_D (P : CommAlgCat.{u} A) (b : (P : Type u)) :
    (kaehlerDifferentialSectionsIso A P).inv (KaehlerDifferential.D A (P : Type u) b) =
      CommRingCat.KaehlerDifferential.d b := by
  conv_lhs => rw [← kaehlerDifferentialSectionsIso_hom_d A P b]
  exact ConcreteCategory.congr_hom (kaehlerDifferentialSectionsIso A P).hom_inv_id _

/-! ### `Ω_{𝒪/A} ⊗_𝒪 B̲ = i^*Ω_{𝒪/A}` -/

/-- `i^*Ω_{𝒪/A}` on the small model, spelled through `CommAlgCat.smallSiteToOver` rather than
through the unrestricted site. The two spellings are the same functor on the nose; this is the
one whose restriction maps are `CommAlgCat.overDifferentialsPush` of a morphism of the model. -/
lemma smallPolynomialCotangentModulePresheaf_eq :
    smallPolynomialCotangentModulePresheaf A B κ =
      smallSiteToOver A B κ ⋙ overDifferentialsFunctor :=
  rfl

/-- **The base change of `Ω_{𝒪/A}` along the augmentation has sections `B ⊗_P Ω[P⁄A]`**, which is
`CommAlgCat.overDifferentials`, the sections of `i^*Ω_{𝒪/A}`. -/
def extendScalarsDifferentialsObjIso (V : (smallBoundedPolynomialSite A B κ)ᵒᵖ) :
    ((Stacks.PullbackModel.extendScalars (smallPolynomialAugmentationComm A B κ)).obj
        (smallPolynomialDifferentials A B κ)).obj V ≅
      overDifferentials ((smallSiteToOver A B κ).obj V) :=
  (ModuleCat.extendScalars ((smallPolynomialAugmentationComm A B κ).app V).hom).mapIso
    (kaehlerDifferentialSectionsIso A ((smallSiteToOver A B κ).obj V).left)

/-- The identification of sections is compatible with the restriction maps, in the form in which
it is checked: both composites send the pure differential `1 ⊗ d p` to `1 ⊗ d (g p)`. -/
lemma extendScalarsDifferentialsObjIso_inv_naturality
    {V W : (smallBoundedPolynomialSite A B κ)ᵒᵖ} (g : V ⟶ W) :
    (extendScalarsDifferentialsObjIso A B κ V).inv ≫
        ((Stacks.PullbackModel.extendScalars (smallPolynomialAugmentationComm A B κ)).obj
            (smallPolynomialDifferentials A B κ)).map g ≫
          (extendScalarsDifferentialsObjIso A B κ W).hom =
      overDifferentialsFunctor.map ((smallSiteToOver A B κ).map g) := by
  refine overDifferentials_hom_ext _ _ fun p => ?_
  refine Eq.trans ?_ (overDifferentialsPush_mk ((smallSiteToOver A B κ).map g).left
    (augmentationRingHom_comp ((smallSiteToOver A B κ).map g)) p).symm
  exact congrArg
    (Stacks.PullbackModel.tmul ((smallPolynomialAugmentationComm A B κ).app W).hom 1)
    ((congrArg
        (fun y => (kaehlerDifferentialSectionsIso A
          ((smallSiteToOver A B κ).obj W).left).hom y)
        ((congrArg (fun y => (smallPolynomialDifferentials A B κ).map g y)
            (kaehlerDifferentialSectionsIso_inv_D A
              ((smallSiteToOver A B κ).obj V).left p)).trans
          (PresheafOfModulesOfCommRing.DifferentialsConstruction.relativeDifferentials'_map_d
            (smallPolynomialBaseHom A B κ) g p))).trans
      (kaehlerDifferentialSectionsIso_hom_d A ((smallSiteToOver A B κ).obj W).left _))

/-- The identification of sections is natural in the object of the site. -/
lemma extendScalarsDifferentialsObjIso_naturality
    {V W : (smallBoundedPolynomialSite A B κ)ᵒᵖ} (g : V ⟶ W) :
    ((Stacks.PullbackModel.extendScalars (smallPolynomialAugmentationComm A B κ)).obj
          (smallPolynomialDifferentials A B κ)).map g ≫
        (extendScalarsDifferentialsObjIso A B κ W).hom =
      (extendScalarsDifferentialsObjIso A B κ V).hom ≫
        overDifferentialsFunctor.map ((smallSiteToOver A B κ).map g) :=
  (Iso.inv_comp_eq _).1 (extendScalarsDifferentialsObjIso_inv_naturality A B κ g)

/-- **`Ω_{𝒪/A} ⊗_𝒪 B̲ = i^*Ω_{𝒪/A}` on underlying abelian presheaves.** The base change of
`Ω_{𝒪/A}` along the augmentation `𝒪 ⟶ B̲` is the sheaf
`CommAlgCat.smallPolynomialCotangentModulePresheaf` of
`StacksFrontier/Cotangent/PolynomialAlgebraSiteCotangentComplex.lean`, whose derived lower shriek
[Stacks, Tag 08PU] computes: both assign to `(P, α)` the module `B ⊗_{P,α} Ω[P⁄A]` and both send
the pure differential `1 ⊗ d p` to `1 ⊗ d (g p)`. -/
def extendScalarsDifferentialsIso :
    (PresheafOfModules.toPresheaf (smallPolynomialConstantPresheaf A B κ)).obj
        ((Stacks.PullbackModel.extendScalars (smallPolynomialAugmentationComm A B κ)).obj
          (smallPolynomialDifferentials A B κ)) ≅
      smallPolynomialCotangentModulePresheaf A B κ ⋙
        forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u} :=
  NatIso.ofComponents
    (fun V => (forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).mapIso
      (extendScalarsDifferentialsObjIso A B κ V))
    (fun g => congrArg (forget₂ (ModuleCat.{u} (B : Type u)) AddCommGrpCat.{u}).map
      (extendScalarsDifferentialsObjIso_naturality A B κ g))

end CommAlgCat

end
