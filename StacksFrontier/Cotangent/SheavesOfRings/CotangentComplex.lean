module

public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.Algebra.Homology.DerivedCategory.Basic
public import Mathlib.Algebra.Homology.Embedding.Extend
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.StandardResolution
public import StacksFrontier.CategoryTheory.Sites.AbelianSheafificationExistence
public import StacksFrontier.CategoryTheory.Sites.Modules.Differentials

/-!
# The cotangent complex of a morphism of sheaves of rings

For a morphism `f : A ⟶ B` of sheaves of commutative rings on a site, the standard resolution
supplies an augmented simplicial sheaf of `A`-algebras `P_•`. Extending the sheaves of relative
differentials `Ω_{P_n/A}` along the augmentation `P_n ⟶ B` gives a simplicial sheaf of
`B`-modules `Ω_{P_•/A} ⊗_{P_•} B`, and its alternating-face complex is the cotangent complex
of `f`.

## Main definitions

* `CategoryTheory.Sheaf.resolutionTerm` is a term of the standard resolution.
* `CategoryTheory.Sheaf.resolutionAugmentation` is its map to `B`.
* `CategoryTheory.Sheaf.resolutionDifferentials` is its sheaf of relative differentials.
* `CategoryTheory.Sheaf.cotangentSimplicialModule` is the base-changed simplicial module.
* `CategoryTheory.Sheaf.cotangentComplex` is its associated cochain complex.
* `CategoryTheory.Sheaf.cotangentComplexDerived` is its image in the derived category.

## Main results

* `CategoryTheory.Sheaf.cotangentComplex_degreeIso` identifies degree `-n` with the base-changed
  differentials in degree `n` of the standard resolution.
* `CategoryTheory.Sheaf.cotangentComplex_d` computes the differential as the alternating sum of
  the face maps.
* `CategoryTheory.Sheaf.cotangentComplex_isZero_pos` records the zero terms in positive degrees.

## Implementation notes

The sheaf of differentials is the corepresenting object of the derivations functor. The
base-changed differentials are constructed through their universal property rather than by
choosing a tensor-product presentation: the specification of `cotangentSimplicialModule` is the
natural equivalence `Hom_B(B ⊗_{P_n} Ω_{P_n/A}, M) ≃ Der_A(P_n, M)`, and its compatibility with
every simplex map specifies the canonical face and degeneracy maps. The equivalence is obtained
from the extension–restriction adjunction for sheaves of modules, and the simplex maps are
obtained by transposing precomposition of derivations.

The associated complex `cotangentComplex` is the alternating-face complex, reindexed so that
simplicial degree `n` lies in cohomological degree `-n`. The degree isomorphisms, the
differential formula and the positive-degree vanishing give its termwise interface without
unfolding this reindexing. `cotangentComplexDerived` is its image under the localization
functor; the derived-category instance chooses a localization, and is not an additional
condition on the morphism of sheaves.

The site-object and site-morphism universes are independent of the universe of sections.
Sheafification of abelian groups in the common coefficient universe is transported from a small
model of the site, so the site is not required to be a small category.

## References

* [Stacks Project, Tag 08SS](https://stacks.math.columbia.edu/tag/08SS)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open AlgebraicGeometry.SheafOfModules (derivationsFunctor)
open Stacks.Sheaves.RingedToposModules (extendScalars extendRestrictScalarsAdjunction)

universe u v w t

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)

/-- Abelian-group sheafification in a universe containing the site. -/
instance hasSheafifyAddCommGrpCat : HasSheafify J AddCommGrpCat.{max u v w} :=
  GrothendieckTopology.hasSheafify_addCommGrpCat_of_essentiallySmall.{max u v w, v, u} J

/-- In this universe, sheafification inverts exactly the locally bijective maps. -/
instance wEqualsLocallyBijectiveAddCommGrpCat :
    J.WEqualsLocallyBijective AddCommGrpCat.{max u v w} := by
  let : ((equivSmallModel.{max u v w} C).inverse.inducedTopology J).WEqualsLocallyBijective
      AddCommGrpCat.{max u v w} :=
    CategoryTheory.smallSiteWEqualsLocallyBijective _
  exact GrothendieckTopology.WEqualsLocallyBijective.ofEssentiallySmall.{v, _, u, _, max u v w} J

variable {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B)

/-- The `n`th algebra sheaf in the standard resolution. -/
noncomputable abbrev resolutionTerm (n : SimplexCategoryᵒᵖ) :
    Sheaf J CommRingCat.{max u v w} :=
  ((standardResolution J f).left.obj n).right

/-- The structure map from the base sheaf to a term of the resolution. -/
noncomputable abbrev resolutionBase (n : SimplexCategoryᵒᵖ) : A ⟶ resolutionTerm J f n :=
  ((standardResolution J f).left.obj n).hom

/-- The augmentation of a term of the standard resolution. -/
noncomputable abbrev resolutionAugmentation (n : SimplexCategoryᵒᵖ) :
    resolutionTerm J f n ⟶ B :=
  ((standardResolution J f).hom.app n).right

/-- The category of modules over the sheaf of rings underlying a sheaf of commutative rings. -/
noncomputable abbrev targetModules (B : Sheaf J CommRingCat.{max u v w}) :=
  SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B)

/-- The sheaf of relative differentials of a term of the standard resolution, obtained from the
universal property of derivations. -/
noncomputable abbrev resolutionDifferentials (n : SimplexCategoryᵒᵖ) :
    targetModules J (resolutionTerm J f n) :=
  (derivationsFunctor.{max u v w} A (resolutionTerm J f n) (resolutionBase J f n)).coreprX

/-- The augmentation after forgetting commutativity of the ring sheaves. -/
noncomputable abbrev resolutionAugmentationRing (n : SimplexCategoryᵒᵖ) :
    Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (resolutionTerm J f n) ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B :=
  (sheafCompose J (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})).map
    (resolutionAugmentation J f n)

/-- The derivations into a `B`-module, with its `P_n`-module structure obtained from the
augmentation `P_n ⟶ B`. -/
noncomputable abbrev resolutionDerivations (n : SimplexCategoryᵒᵖ) (M : targetModules J B) :=
  PresheafOfModulesOfCommRing.Derivation'
    (((SheafOfModules.restrictScalars (resolutionAugmentationRing J f n)).obj M).val)
    (resolutionBase J f n).hom

/-- A simplicial `B`-module with its universal characterization as `Ω_{P_•/A} ⊗_{P_•} B`.
Naturality in both the coefficient module and the simplex variable fixes all faces and
degeneracies. -/
structure CotangentSimplicialModuleData where
  /-- The underlying simplicial sheaf of `B`-modules. -/
  object : SimplicialObject (targetModules J B)
  /-- Its term in simplicial degree `n` corepresents the `A`-derivations of `P_n`. -/
  derivationEquiv (n : SimplexCategoryᵒᵖ) (M : targetModules J B) :
    (object.obj n ⟶ M) ≃ resolutionDerivations J f n M
  /-- The corepresentation is natural in the coefficient module. -/
  naturality (n : SimplexCategoryᵒᵖ) {M N : targetModules J B}
      (g : object.obj n ⟶ M) (h : M ⟶ N) :
    derivationEquiv n N (g ≫ h) =
      (derivationEquiv n M g).postcomp
        ((SheafOfModules.restrictScalars (resolutionAugmentationRing J f n)).map h).val
  /-- Every simplex map acts on derivations by precomposition with the corresponding map of
  the standard resolution. -/
  simplex_naturality {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) (M : targetModules J B)
      (h : object.obj j ⟶ M) (U : Cᵒᵖ) (x : (resolutionTerm J f i).obj.obj U) :
    (derivationEquiv i M (object.map g ≫ h)).d x =
      (derivationEquiv j M h).d (((standardResolution J f).left.map g).right.hom.app U x)

/-- The sections of a sheaf of commutative rings act on the sections of a module over the
underlying sheaf of rings. -/
@[instance_reducible]
def moduleOfSections (O : Sheaf J CommRingCat.{max u v w}) (M : targetModules J O)
    (U : Cᵒᵖ) : Module (O.obj.obj U) (M.val.obj U) :=
  inferInstanceAs (Module
    ((Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} O).obj.obj U) (M.val.obj U))

attribute [local instance] moduleOfSections

/-- Extension of scalars along the augmentation of a term of the standard resolution. -/
private noncomputable abbrev extendAlongAugmentation (n : SimplexCategoryᵒᵖ) :
    targetModules J (resolutionTerm J f n) ⥤ targetModules J B :=
  extendScalars J (resolutionAugmentation J f n).hom
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (resolutionTerm J f n)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).property

/-- Extension of scalars along the augmentation is left adjoint to restriction of scalars. -/
private noncomputable abbrev augmentationAdjunction (n : SimplexCategoryᵒᵖ) :
    extendAlongAugmentation J f n ⊣
      SheafOfModules.restrictScalars (resolutionAugmentationRing J f n) :=
  extendRestrictScalarsAdjunction J (resolutionAugmentation J f n).hom
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} (resolutionTerm J f n)).property
    (Stacks.SheafOfModules.Tensor.ringSheaf.{u, v, max u v w} B).property

/-- The base-changed sheaf of differentials `Ω_{P_n/A} ⊗_{P_n} B` in simplicial degree `n`. -/
private noncomputable abbrev cotangentTerm (n : SimplexCategoryᵒᵖ) : targetModules J B :=
  (extendAlongAugmentation J f n).obj (resolutionDifferentials J f n)

/-- The base-changed differentials corepresent the `A`-derivations of a resolution term. -/
private noncomputable def cotangentEquiv (n : SimplexCategoryᵒᵖ) (M : targetModules J B) :
    (cotangentTerm J f n ⟶ M) ≃ resolutionDerivations J f n M :=
  ((augmentationAdjunction J f n).homEquiv (resolutionDifferentials J f n) M).trans
    (derivationsFunctor.{max u v w} A (resolutionTerm J f n)
      (resolutionBase J f n)).corepresentableBy.homEquiv

/-- The derivations functor acts on a morphism of coefficient modules by postcomposition. -/
private lemma derivationsFunctor_map_apply (n : SimplexCategoryᵒᵖ)
    {M N : targetModules J B} (k : M ⟶ N) (D : resolutionDerivations J f n M) :
    (derivationsFunctor.{max u v w} A (resolutionTerm J f n) (resolutionBase J f n)).map
        ((SheafOfModules.restrictScalars (resolutionAugmentationRing J f n)).map k) D =
      D.postcomp ((SheafOfModules.restrictScalars
        (resolutionAugmentationRing J f n)).map k).val := rfl

/-- The corepresentation of base-changed differentials is natural in the coefficient module. -/
private lemma cotangentEquiv_naturality (n : SimplexCategoryᵒᵖ)
    {M N : targetModules J B} (g : cotangentTerm J f n ⟶ M) (h : M ⟶ N) :
    cotangentEquiv J f n N (g ≫ h) =
      (cotangentEquiv J f n M g).postcomp
        ((SheafOfModules.restrictScalars (resolutionAugmentationRing J f n)).map h).val := by
  have h1 : (augmentationAdjunction J f n).homEquiv (resolutionDifferentials J f n) N (g ≫ h) =
      (augmentationAdjunction J f n).homEquiv (resolutionDifferentials J f n) M g ≫
        (SheafOfModules.restrictScalars (resolutionAugmentationRing J f n)).map h :=
    Adjunction.homEquiv_naturality_right _ _ _
  exact ((congrArg (fun k : resolutionDifferentials J f n ⟶
        (SheafOfModules.restrictScalars (resolutionAugmentationRing J f n)).obj N =>
      (derivationsFunctor.{max u v w} A (resolutionTerm J f n)
        (resolutionBase J f n)).corepresentableBy.homEquiv k) h1).trans
    ((derivationsFunctor.{max u v w} A (resolutionTerm J f n)
      (resolutionBase J f n)).corepresentableBy.homEquiv_comp _ _)).trans
    (derivationsFunctor_map_apply J f n h _)

/-- The map of resolution terms attached to a map of simplices. -/
private noncomputable abbrev resolutionMap {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    resolutionTerm J f i ⟶ resolutionTerm J f j :=
  ((standardResolution J f).left.map g).right

/-- The maps of the standard resolution are maps of `A`-algebras. -/
private lemma resolutionMap_base {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j)
    (U : Cᵒᵖ) (x : A.obj.obj U) :
    (resolutionMap J f g).hom.app U ((resolutionBase J f i).hom.app U x) =
      (resolutionBase J f j).hom.app U x :=
  congrArg (fun k : A ⟶ resolutionTerm J f j => k.hom.app U x)
    (Under.w ((standardResolution J f).left.map g))

/-- The maps of the standard resolution are compatible with the augmentation. -/
private lemma resolutionMap_augmentation {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j)
    (U : Cᵒᵖ) (x : (resolutionTerm J f i).obj.obj U) :
    (resolutionAugmentation J f j).hom.app U ((resolutionMap J f g).hom.app U x) =
      (resolutionAugmentation J f i).hom.app U x :=
  congrArg (fun k => k.right.hom.app U x) ((standardResolution J f).hom.naturality g)

/-- Precomposition of an `A`-derivation of `P_j` with a map `P_i ⟶ P_j` of the standard
resolution is an `A`-derivation of `P_i`. -/
private noncomputable def derivationPrecomp {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j)
    (M : targetModules J B) (D : resolutionDerivations J f j M) :
    resolutionDerivations J f i M where
  d {U} := (D.d (X := U)).comp ((resolutionMap J f g).hom.app U).hom.toAddMonoidHom
  d_mul {U} x y := by
    change D.d ((resolutionMap J f g).hom.app U (x * y)) =
      (resolutionAugmentation J f i).hom.app U x •
        (show M.val.obj U from D.d ((resolutionMap J f g).hom.app U y)) +
      (resolutionAugmentation J f i).hom.app U y •
        (show M.val.obj U from D.d ((resolutionMap J f g).hom.app U x))
    rw [map_mul ((resolutionMap J f g).hom.app U).hom, D.d_mul,
      ← resolutionMap_augmentation J f g U x, ← resolutionMap_augmentation J f g U y]
    rfl
  d_map {U V} a x := by
    have h := congrArg (fun k => k x) ((resolutionMap J f g).hom.naturality a)
    dsimp at h
    change D.d ((resolutionMap J f g).hom.app V ((resolutionTerm J f i).obj.map a x)) =
      M.val.map a (D.d ((resolutionMap J f g).hom.app U x))
    rw [h]
    exact D.d_map a _
  d_app {U} x := by
    change D.d ((resolutionMap J f g).hom.app U ((resolutionBase J f i).hom.app U x)) = 0
    rw [resolutionMap_base]
    exact D.d_app x

/-- The map between base-changed differentials transposing precomposition of derivations. -/
private noncomputable def cotangentMap {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    cotangentTerm J f i ⟶ cotangentTerm J f j :=
  (cotangentEquiv J f i _).symm
    (derivationPrecomp J f g _ (cotangentEquiv J f j _ (𝟙 _)))

/-- A natural corepresentation is determined by the derivation matching the identity. -/
private lemma corepresentation_eq_postcomp (n : SimplexCategoryᵒᵖ) {X : targetModules J B}
    (e : ∀ M, (X ⟶ M) ≃ resolutionDerivations J f n M)
    (he : ∀ {M N} (g : X ⟶ M) (h : M ⟶ N), e N (g ≫ h) =
      (e M g).postcomp ((SheafOfModules.restrictScalars (resolutionAugmentationRing J f n)).map
        h).val)
    {M : targetModules J B} (h : X ⟶ M) :
    e M h = (e X (𝟙 X)).postcomp
      ((SheafOfModules.restrictScalars (resolutionAugmentationRing J f n)).map h).val := by
  simpa using he (𝟙 X) h

/-- The map transposing `derivationPrecomp` is characterized by its effect on derivations. -/
private lemma cotangentMap_naturality {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j)
    (M : targetModules J B) (h : cotangentTerm J f j ⟶ M) :
    cotangentEquiv J f i M (cotangentMap J f g ≫ h) =
      derivationPrecomp J f g M (cotangentEquiv J f j M h) := by
  rw [cotangentEquiv_naturality, cotangentMap, Equiv.apply_symm_apply,
    corepresentation_eq_postcomp J f j (cotangentEquiv J f j) (cotangentEquiv_naturality J f j) h]
  rfl

/-- The transposed simplex maps send an identity to an identity. -/
private lemma cotangentMap_id (i : SimplexCategoryᵒᵖ) :
    cotangentMap J f (𝟙 i) = 𝟙 (cotangentTerm J f i) := by
  apply (cotangentEquiv J f i _).injective
  rw [cotangentMap, Equiv.apply_symm_apply]
  ext U x
  show (cotangentEquiv J f i _ (𝟙 _)).d ((resolutionMap J f (𝟙 i)).hom.app U x) = _
  simp [resolutionMap]

/-- The transposed simplex maps are compatible with composition. -/
private lemma cotangentMap_comp {i j k : SimplexCategoryᵒᵖ} (g : i ⟶ j) (h : j ⟶ k) :
    cotangentMap J f (g ≫ h) = cotangentMap J f g ≫ cotangentMap J f h := by
  apply (cotangentEquiv J f i _).injective
  rw [cotangentMap_naturality]
  simp only [cotangentMap, Equiv.apply_symm_apply]
  ext U x
  show (cotangentEquiv J f k _ (𝟙 _)).d ((resolutionMap J f (g ≫ h)).hom.app U x) =
    (cotangentEquiv J f k _ (𝟙 _)).d
      ((resolutionMap J f h).hom.app U ((resolutionMap J f g).hom.app U x))
  simp [resolutionMap]

/-- The data characterizing the base-changed simplicial module exists: its terms are obtained
by extending scalars along the augmentation, and its simplex maps by transposing precomposition
of derivations. -/
private lemma cotangentSimplicialModuleData_nonempty :
    Nonempty (CotangentSimplicialModuleData J f) :=
  ⟨{ object :=
      { obj := cotangentTerm J f
        map := cotangentMap J f
        map_id := cotangentMap_id J f
        map_comp := cotangentMap_comp J f }
     derivationEquiv := cotangentEquiv J f
     naturality := cotangentEquiv_naturality J f
     simplex_naturality g M h U x :=
       PresheafOfModulesOfCommRing.Derivation.congr_d (X := U)
         (cotangentMap_naturality J f g M h) x }⟩

/-- **Stacks 08SS.** The canonical simplicial sheaf of `B`-modules `Ω_{P_•/A} ⊗_{P_•} B` of the
standard resolution. -/
@[stacks 08SS "the simplicial module", implicit_reducible]
noncomputable def cotangentSimplicialModule : CotangentSimplicialModuleData J f :=
  Classical.choice (by exact cotangentSimplicialModuleData_nonempty J f)

/-- **Stacks 08SS.** The cotangent complex of a morphism of sheaves of commutative rings. -/
@[stacks 08SS "the associated complex"]
noncomputable def cotangentComplex : CochainComplex (targetModules J B) ℤ :=
  ((AlgebraicTopology.alternatingFaceMapComplex (targetModules J B)).obj
    (cotangentSimplicialModule J f).object).extend (ComplexShape.embeddingUpIntLE 0)

/-- **Stacks 08SS.** The cotangent complex regarded as an object of the derived category. -/
@[stacks 08SS "the derived object"]
noncomputable abbrev cotangentComplexDerived [HasDerivedCategory.{t} (targetModules J B)] :
    DerivedCategory (targetModules J B) :=
  DerivedCategory.Q.obj (cotangentComplex J f)

/-- The term in degree `-n` is the universal sheaf of base-changed differentials in simplicial
degree `n`. -/
@[implicit_reducible]
noncomputable def cotangentComplex_degreeIso (n : ℕ) :
    (cotangentComplex J f).X (-(n : ℤ)) ≅
      (cotangentSimplicialModule J f).object.obj (op ⦋n⦌) :=
  ((AlgebraicTopology.alternatingFaceMapComplex (targetModules J B)).obj
    (cotangentSimplicialModule J f).object).extendXIso
      (ComplexShape.embeddingUpIntLE 0) (by simp)

/-- **Stacks 08SS.** The cotangent complex is zero in positive cohomological degrees. -/
@[stacks 08SS "the positive-degree terms"]
theorem cotangentComplex_isZero_pos (m : ℤ) (hm : 0 < m) :
    IsZero ((cotangentComplex J f).X m) := by
  apply HomologicalComplex.isZero_extend_X
  intro n
  simp only [ComplexShape.embeddingUpIntLE_f]
  omega

/-- **Stacks 08SS.** The differential is the alternating sum of the face maps, transported
through the canonical degree isomorphisms. -/
@[stacks 08SS "the differential"]
theorem cotangentComplex_d (n : ℕ) :
    (cotangentComplex J f).d (-((n + 1 : ℕ) : ℤ)) (-(n : ℤ)) =
      (cotangentComplex_degreeIso J f (n + 1)).hom ≫
        AlgebraicTopology.AlternatingFaceMapComplex.objD
          (cotangentSimplicialModule J f).object n ≫
      (cotangentComplex_degreeIso J f n).inv := by
  refine (HomologicalComplex.extend_d_eq
      ((AlgebraicTopology.alternatingFaceMapComplex (targetModules J B)).obj
        (cotangentSimplicialModule J f).object) (ComplexShape.embeddingUpIntLE 0)
      (i := n + 1) (j := n) (i' := -((n + 1 : ℕ) : ℤ)) (j' := -(n : ℤ))
      (by simp) (by simp)).trans ?_
  exact congrArg (fun d => (cotangentComplex_degreeIso J f (n + 1)).hom ≫ d ≫
    (cotangentComplex_degreeIso J f n).inv)
    (AlgebraicTopology.alternatingFaceMapComplex_obj_d
      (cotangentSimplicialModule J f).object n)

/-! ## Uniqueness of the base-changed simplicial module

`cotangentSimplicialModule` is a choice of `CotangentSimplicialModuleData`, and
`cotangentComplex` is built from that choice. The data is a corepresentation of the derivations
of the standard resolution, so it is unique up to a unique isomorphism; this section proves it,
so that any other construction of `Ω_{P_•/A} ⊗_{P_•} B` computes the same cotangent complex.
-/

section Uniqueness

variable {J f}

/-- Two relative derivations of a presheaf of modules agreeing on sections are equal. -/
private theorem derivation_ext {C' : Type*} [Category C'] {D' : Type*} [Category D']
    {S : C'ᵒᵖ ⥤ CommRingCat.{t}} {F : C' ⥤ D'} {R : D'ᵒᵖ ⥤ CommRingCat.{t}}
    {M : PresheafOfModules.{t} (R ⋙ forget₂ _ _)} {φ : S ⟶ F.op ⋙ R}
    {D₁ D₂ : PresheafOfModulesOfCommRing.Derivation M φ}
    (h : ∀ (X : D'ᵒᵖ) (x : R.obj X), D₁.d x = D₂.d x) : D₁ = D₂ :=
  PresheafOfModulesOfCommRing.Derivation.ext (funext fun X => AddMonoidHom.ext (h X))

namespace CotangentSimplicialModuleData

/-- The universal `A`-derivation of `P_n` corepresented by a choice of base-changed simplicial
module: the derivation matching the identity morphism of its degree-`n` term. -/
noncomputable def universalDerivation (D : CotangentSimplicialModuleData J f)
    (n : SimplexCategoryᵒᵖ) : resolutionDerivations J f n (D.object.obj n) :=
  D.derivationEquiv n _ (𝟙 _)

/-- The derivation matching a morphism out of the degree-`n` term is the universal derivation
postcomposed with it. -/
theorem derivationEquiv_eq_postcomp (D : CotangentSimplicialModuleData J f)
    (n : SimplexCategoryᵒᵖ) {M : targetModules J B} (h : D.object.obj n ⟶ M) :
    D.derivationEquiv n M h = (D.universalDerivation n).postcomp
      ((SheafOfModules.restrictScalars (resolutionAugmentationRing J f n)).map h).val := by
  exact corepresentation_eq_postcomp J f n (D.derivationEquiv n) (D.naturality n) h

/-- The comparison morphism in simplicial degree `n` between two choices of the base-changed
simplicial module: the morphism matching the universal derivation of the second. -/
noncomputable def compareApp (D₁ D₂ : CotangentSimplicialModuleData J f)
    (n : SimplexCategoryᵒᵖ) : D₁.object.obj n ⟶ D₂.object.obj n :=
  (D₁.derivationEquiv n (D₂.object.obj n)).symm (D₂.universalDerivation n)

/-- The comparison morphism from `D₁` to `D₂` in degree `n` matches the universal derivation
of `D₂`. -/
@[simp]
theorem derivationEquiv_compareApp (D₁ D₂ : CotangentSimplicialModuleData J f)
    (n : SimplexCategoryᵒᵖ) :
    D₁.derivationEquiv n (D₂.object.obj n) (compareApp D₁ D₂ n) = D₂.universalDerivation n :=
  (D₁.derivationEquiv n (D₂.object.obj n)).apply_symm_apply _

/-- The comparison morphism of a choice with itself is the identity. -/
@[simp]
theorem compareApp_self (D : CotangentSimplicialModuleData J f) (n : SimplexCategoryᵒᵖ) :
    compareApp D D n = 𝟙 _ :=
  (D.derivationEquiv n (D.object.obj n)).injective (derivationEquiv_compareApp D D n)

/-- The comparison morphisms of three choices compose. -/
@[reassoc (attr := simp)]
theorem compareApp_comp (D₁ D₂ D₃ : CotangentSimplicialModuleData J f)
    (n : SimplexCategoryᵒᵖ) :
    compareApp D₁ D₂ n ≫ compareApp D₂ D₃ n = compareApp D₁ D₃ n := by
  refine (D₁.derivationEquiv n (D₃.object.obj n)).injective ?_
  rw [D₁.naturality n (compareApp D₁ D₂ n) (compareApp D₂ D₃ n),
    derivationEquiv_compareApp, ← D₂.derivationEquiv_eq_postcomp n (compareApp D₂ D₃ n),
    derivationEquiv_compareApp, derivationEquiv_compareApp]

/-- The comparison morphisms commute with the simplex maps of the two choices. -/
theorem compareApp_naturality (D₁ D₂ : CotangentSimplicialModuleData J f)
    {i j : SimplexCategoryᵒᵖ} (g : i ⟶ j) :
    D₁.object.map g ≫ compareApp D₁ D₂ j = compareApp D₁ D₂ i ≫ D₂.object.map g := by
  refine (D₁.derivationEquiv i (D₂.object.obj j)).injective (derivation_ext fun U x => ?_)
  rw [D₁.simplex_naturality g (D₂.object.obj j) (compareApp D₁ D₂ j) U x,
    derivationEquiv_compareApp,
    D₁.naturality i (compareApp D₁ D₂ i) (D₂.object.map g), derivationEquiv_compareApp,
    ← D₂.derivationEquiv_eq_postcomp i (D₂.object.map g)]
  have h0 := D₂.simplex_naturality g (D₂.object.obj j) (𝟙 _) U x
  rw [Category.comp_id] at h0
  exact h0.symm

/-- **Two choices of the base-changed simplicial module are canonically isomorphic.** Both
corepresent the `A`-derivations of the standard resolution, degreewise and compatibly with the
simplex maps, so the transposed identities are mutually inverse. -/
@[simps! hom_app inv_app]
noncomputable def compare (D₁ D₂ : CotangentSimplicialModuleData J f) :
    D₁.object ≅ D₂.object where
  hom := { app := compareApp D₁ D₂, naturality := fun _ _ => compareApp_naturality D₁ D₂ }
  inv := { app := compareApp D₂ D₁, naturality := fun _ _ => compareApp_naturality D₂ D₁ }
  hom_inv_id := NatTrans.ext (funext fun n =>
    (compareApp_comp D₁ D₂ D₁ n).trans (compareApp_self D₁ n))
  inv_hom_id := NatTrans.ext (funext fun n =>
    (compareApp_comp D₂ D₁ D₂ n).trans (compareApp_self D₂ n))

/-- The cochain complex attached to a choice of base-changed simplicial module: its
alternating-face complex, reindexed so that simplicial degree `n` lies in degree `-n`. -/
noncomputable def complex (D : CotangentSimplicialModuleData J f) :
    CochainComplex (targetModules J B) ℤ :=
  ((AlgebraicTopology.alternatingFaceMapComplex (targetModules J B)).obj D.object).extend
    (ComplexShape.embeddingUpIntLE 0)

/-- The complex attached to `cotangentSimplicialModule J f` is `cotangentComplex J f`. -/
theorem complex_cotangentSimplicialModule (J : GrothendieckTopology C)
    {A B : Sheaf J CommRingCat.{max u v w}} (f : A ⟶ B) :
    (cotangentSimplicialModule J f).complex = cotangentComplex J f := rfl

/-- **The cotangent complex is independent of the choice of base-changed simplicial module.** -/
noncomputable def complexIso (D₁ D₂ : CotangentSimplicialModuleData J f) :
    D₁.complex ≅ D₂.complex :=
  ((ComplexShape.embeddingUpIntLE 0).extendFunctor (targetModules J B)).mapIso
    ((AlgebraicTopology.alternatingFaceMapComplex (targetModules J B)).mapIso (compare D₁ D₂))

/-- Any choice of base-changed simplicial module computes the cotangent complex. -/
noncomputable def complexIsoCotangentComplex (D : CotangentSimplicialModuleData J f) :
    D.complex ≅ cotangentComplex J f :=
  complexIso D (cotangentSimplicialModule J f)

end CotangentSimplicialModuleData

end Uniqueness

end CategoryTheory.Sheaf

end
