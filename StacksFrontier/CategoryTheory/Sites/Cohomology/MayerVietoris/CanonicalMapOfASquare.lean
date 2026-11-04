module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCocone
public import Mathlib.CategoryTheory.Functor.Derived.RightDerived
public import Mathlib.CategoryTheory.Square
public import StacksFrontier.Algebra.Homology.DerivedCategory.KInjective
public import StacksFrontier.Algebra.Homology.MappingCoconeFunctoriality
public import StacksFrontier.CategoryTheory.Functor.Derived.LocalizationLeftKanExtension
public import StacksFrontier.CategoryTheory.Sites.Modules.GrothendieckAbelianSmall
public import StacksFrontier.CategoryTheory.Sites.Modules.RingedSite
public import StacksFrontier.CategoryTheory.Sites.Cohomology.MayerVietoris.CanonicalMapOfComplexes
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Derived functors from K-injective resolutions, and the Mayer–Vietoris map at a ringed site

The first part of this file concerns an arbitrary abelian category `𝒜`. A functor out of the
unbounded homotopy category of `𝒜` has a pointwise right derived functor as soon as every complex
admits a K-injective resolution, and that derived functor is computed by K-injective complexes;
in a Grothendieck abelian category every complex admits a K-injective resolution. It also
records that an additive functor identifies the image of a binary biproduct with the biproduct of
the images.

The second part specializes the sections functors of
`Stacks.MayerVietoris.CanonicalMapOfComplexes` and its canonical map of complexes
`I(X) ⟶ C(β)[-1]` to the structure sheaf of a bundled `AlgebraicGeometry.RingedSite` `S`. Here a
square of the site has `sq.X₁, sq.X₂, sq.X₃, sq.X₄` equal to `E, Y, Z, X`, and `C(β)[-1]` is
`CochainComplex.mappingCocone β`.

## Main results

* `hasPointwiseRightDerivedFunctor_of_kInjectiveResolutions` and
  `isIso_unit_app_of_isKInjective`: existence of a pointwise right derived functor from
  K-injective resolutions, and its computation on a K-injective complex.
* `exists_quasiIso_isKInjective`: every complex in a Grothendieck abelian category admits a
  K-injective resolution.
* `isIso_biprodComparison`, `isIso_map_biprod_map` and `hom_ext_of_additive` describe the
  comparison between the image of a binary biproduct under an additive functor and the
  biproduct of the images.

## Main definitions

* `sections`, `sectionsComplex`, `sectionsRestriction` and `sectionsRestrictionComplex` are
  the sections functors of
  `Stacks.MayerVietoris.CanonicalMapOfComplexes` at the structure sheaf of `S`.
* `cSquare` is the canonical map of complexes `I(X) ⟶ C(β)[-1]` at the structure sheaf of `S`.

## References

* [Stacks Project, Tag 0F16](https://stacks.math.columbia.edu/tag/0F16)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CategoryTheory.Pretriangulated

namespace Stacks.Cohomology.MayerVietoris

universe v₁ v₂ v₃ u₁ u₂ u₃ u v w r

attribute [local instance] HasDerivedCategory.standard

section Wrappers

/-- Existence of a pointwise right derived functor on the unbounded homotopy category, from
the existence of K-injective resolutions. -/
theorem hasPointwiseRightDerivedFunctor_of_kInjectiveResolutions
    {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] {H : Type u₂} [Category.{v₂} H]
    (F : HomotopyCategory 𝒜 (ComplexShape.up ℤ) ⥤ H)
    (h : ∀ K : CochainComplex 𝒜 ℤ, ∃ (I : CochainComplex 𝒜 ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    F.HasPointwiseRightDerivedFunctor (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{v₁,
    v₂, 0, u₁, u₂, 0} F h).1

/-- A K-injective complex computes any right derived functor on the unbounded homotopy
category. -/
theorem isIso_unit_app_of_isKInjective
    {𝒜 : Type u₁} [Category.{v₁} 𝒜] [Abelian 𝒜] {H : Type u₂} [Category.{v₂} H]
    (F : HomotopyCategory 𝒜 (ComplexShape.up ℤ) ⥤ H)
    (h : ∀ K : CochainComplex 𝒜 ℤ, ∃ (I : CochainComplex 𝒜 ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    {D : Type u₃} [Category.{v₃} D] (L : HomotopyCategory 𝒜 (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ))]
    (RF : D ⥤ H) (α : F ⟶ L ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso 𝒜 (ComplexShape.up ℤ))]
    (I : CochainComplex 𝒜 ℤ) [I.IsKInjective] :
    IsIso (α.app ((HomotopyCategory.quotient 𝒜 (ComplexShape.up ℤ)).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{v₁,
    v₂, v₃, u₁, u₂, u₃} F h).2 L RF α I ‹_›

/-- Every complex in a Grothendieck abelian category admits a K-injective resolution. -/
theorem exists_quasiIso_isKInjective (𝒜 : Type u₁) [Category.{v₁} 𝒜] [Abelian 𝒜]
    [IsGrothendieckAbelian.{u₃} 𝒜] (K : CochainComplex 𝒜 ℤ) :
    ∃ (I : CochainComplex 𝒜 ℤ) (f : K ⟶ I), I.IsKInjective ∧ QuasiIso f :=
  ⟨(Stacks.Injectives.kInjectiveResolutionFunctor 𝒜).obj K,
    (Stacks.Injectives.kInjectiveResolutionInclusion 𝒜).app K, inferInstance, inferInstance⟩

/-- Evaluating a sheaf at an object of the site is additive. -/
instance sheafSections_additive {C : Type u} [Category.{w} C] (J : GrothendieckTopology C)
    (A : Type v) [Category.{v₁} A] [Preadditive A] (X : Cᵒᵖ) :
    ((sheafSections J A).obj X).Additive :=
  ⟨fun {_ _ _ _} ↦ rfl⟩

section Biproducts

variable {A : Type u₁} [Category.{v₁} A] [Preadditive A] [HasBinaryBiproducts A]
  {B : Type u₂} [Category.{v₂} B] [Preadditive B] [HasBinaryBiproducts B]
  (F : A ⥤ B) [F.Additive]

/-- An additive functor identifies the image of a binary biproduct with the biproduct of the
images. -/
lemma isIso_biprodComparison (X Y : A) : IsIso (Functor.biprodComparison F X Y) := by
  refine ⟨Functor.biprodComparison' F X Y, ?_,
    Functor.biprodComparison'_comp_biprodComparison F X Y⟩
  rw [Functor.biprodComparison, Functor.biprodComparison', biprod.lift_desc, ← F.map_comp,
    ← F.map_comp, ← F.map_add, biprod.total, F.map_id]

omit [F.Additive] in
/-- The biproduct comparison is natural. -/
lemma biprodComparison_naturality {X Y X' Y' : A} (a : X ⟶ X') (b : Y ⟶ Y') :
    Functor.biprodComparison F X Y ≫ biprod.map (F.map a) (F.map b) =
      F.map (biprod.map a b) ≫ Functor.biprodComparison F X' Y' := by
  apply biprod.hom_ext
  · rw [Category.assoc, biprod.map_fst, Functor.biprodComparison_fst_assoc,
      Category.assoc, Functor.biprodComparison_fst, ← F.map_comp, ← F.map_comp,
      biprod.map_fst]
  · rw [Category.assoc, biprod.map_snd, Functor.biprodComparison_snd_assoc,
      Category.assoc, Functor.biprodComparison_snd, ← F.map_comp, ← F.map_comp,
      biprod.map_snd]

/-- An additive functor sends the biproduct of two morphisms it inverts to an
isomorphism. -/
lemma isIso_map_biprod_map {X Y X' Y' : A} (a : X ⟶ X') (b : Y ⟶ Y')
    [IsIso (F.map a)] [IsIso (F.map b)] : IsIso (F.map (biprod.map a b)) := by
  have h1 := isIso_biprodComparison F X Y
  have h2 := isIso_biprodComparison F X' Y'
  have h3 : IsIso (biprod.map (F.map a) (F.map b)) :=
    (biprod.mapIso (asIso (F.map a)) (asIso (F.map b))).isIso_hom
  have h := biprodComparison_naturality F a b
  have hc : IsIso (F.map (biprod.map a b) ≫ Functor.biprodComparison F X' Y') := by
    rw [← h]; infer_instance
  exact (isIso_comp_right_iff _ _).mp hc

/-- The reverse biproduct comparison of an additive functor is invertible. -/
lemma isIso_biprodComparison' (X Y : A) : IsIso (Functor.biprodComparison' F X Y) := by
  have := isIso_biprodComparison F X Y
  exact IsIso.of_isIso_fac_right (Functor.biprodComparison'_comp_biprodComparison F X Y)

/-- A morphism out of the image of a binary biproduct under an additive functor is
determined by its two components. -/
lemma hom_ext_of_additive {X Y : A} {T : B} {φ ψ : F.obj (X ⊞ Y) ⟶ T}
    (h₁ : F.map biprod.inl ≫ φ = F.map biprod.inl ≫ ψ)
    (h₂ : F.map biprod.inr ≫ φ = F.map biprod.inr ≫ ψ) : φ = ψ := by
  have hiso := isIso_biprodComparison' F X Y
  rw [← cancel_epi (Functor.biprodComparison' F X Y)]
  apply biprod.hom_ext'
  · rw [← Category.assoc, Functor.inl_biprodComparison', ← Category.assoc,
      Functor.inl_biprodComparison', h₁]
  · rw [← Category.assoc, Functor.inr_biprodComparison', ← Category.assoc,
      Functor.inr_biprodComparison', h₂]

end Biproducts

end Wrappers

variable {S : AlgebraicGeometry.RingedSite.{u, w, r}}

section Chain

variable [HasSheafify S.J AddCommGrpCat.{v}]
  [S.J.WEqualsLocallyBijective AddCommGrpCat.{v}]

/-- Sections, regarded as abelian groups.  This is
`Stacks.MayerVietoris.CanonicalMapOfComplexes.sections` at the structure sheaf of `S`. -/
abbrev sections (S : AlgebraicGeometry.RingedSite.{u, w, r})
    [HasSheafify S.J AddCommGrpCat.{v}]
    [S.J.WEqualsLocallyBijective AddCommGrpCat.{v}] (U : S.C) :
    SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O) ⥤ AddCommGrpCat.{v} :=
  Stacks.MayerVietoris.CanonicalMapOfComplexes.sections.{u, v, w, r}
    (Stacks.SheafOfModules.Tensor.ringSheaf S.O) U

/-- Degreewise sections of a complex of module sheaves.  This is
`Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsComplex` at the structure sheaf of `S`. -/
abbrev sectionsComplex (S : AlgebraicGeometry.RingedSite.{u, w, r})
    [HasSheafify S.J AddCommGrpCat.{v}]
    [S.J.WEqualsLocallyBijective AddCommGrpCat.{v}] (U : S.C) :
    CochainComplex (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) ℤ ⥤
      CochainComplex AddCommGrpCat.{v} ℤ :=
  Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsComplex.{u, v, w, r}
    (Stacks.SheafOfModules.Tensor.ringSheaf S.O) U

/-- Restriction of sections along a morphism of the site.  This is
`Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsRestriction` at the structure sheaf
of `S`. -/
abbrev sectionsRestriction (S : AlgebraicGeometry.RingedSite.{u, w, r})
    [HasSheafify S.J AddCommGrpCat.{v}]
    [S.J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    {U V : S.C} (f : U ⟶ V) : sections.{u, v, w, r} S V ⟶ sections.{u, v, w, r} S U :=
  Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsRestriction.{u, v, w, r}
    (Stacks.SheafOfModules.Tensor.ringSheaf S.O) f

/-- Restriction of sections along the identity morphism of `U` is the identity. -/
@[simp]
lemma sectionsRestriction_id (U : S.C) :
    sectionsRestriction.{u, v, w, r} S (𝟙 U) = 𝟙 _ :=
  Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsRestriction_id.{u, v}
    (Stacks.SheafOfModules.Tensor.ringSheaf S.O) U

/-- Restriction of sections along `f ≫ g` is restriction along `g` followed by restriction along
`f`. -/
@[simp]
lemma sectionsRestriction_comp {U V W : S.C} (f : U ⟶ V) (g : V ⟶ W) :
    sectionsRestriction.{u, v, w, r} S (f ≫ g) =
      sectionsRestriction.{u, v, w, r} S g ≫ sectionsRestriction.{u, v, w, r} S f :=
  Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsRestriction_comp.{u, v}
    (Stacks.SheafOfModules.Tensor.ringSheaf S.O) f g

/-- Degreewise restriction of sections.  This is
`Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsRestrictionComplex` at the structure
sheaf of `S`. -/
abbrev sectionsRestrictionComplex (S : AlgebraicGeometry.RingedSite.{u, w, r})
    [HasSheafify S.J AddCommGrpCat.{v}]
    [S.J.WEqualsLocallyBijective AddCommGrpCat.{v}]
    {U V : S.C} (f : U ⟶ V) :
    sectionsComplex.{u, v, w, r} S V ⟶ sectionsComplex.{u, v, w, r} S U :=
  Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsRestrictionComplex.{u, v}
    (Stacks.SheafOfModules.Tensor.ringSheaf S.O) f

/-- Degreewise restriction of sections along the identity morphism of `U` is the identity. -/
@[simp]
lemma sectionsRestrictionComplex_id (U : S.C) :
    sectionsRestrictionComplex.{u, v, w, r} S (𝟙 U) = 𝟙 _ :=
  Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsRestrictionComplex_id.{u, v}
    (Stacks.SheafOfModules.Tensor.ringSheaf S.O) U

/-- Degreewise restriction of sections along `f ≫ g` is restriction along `g` followed by
restriction along `f`, as morphisms of functors. -/
@[simp]
lemma sectionsRestrictionComplex_comp' {U V W : S.C} (f : U ⟶ V) (g : V ⟶ W) :
    sectionsRestrictionComplex.{u, v, w, r} S (f ≫ g) =
      sectionsRestrictionComplex.{u, v, w, r} S g ≫
        sectionsRestrictionComplex.{u, v, w, r} S f :=
  Stacks.MayerVietoris.CanonicalMapOfComplexes.sectionsRestrictionComplex_comp.{u, v}
    (Stacks.SheafOfModules.Tensor.ringSheaf S.O) f g

/-- At a complex `I`, degreewise restriction of sections along `g` followed by restriction along
`f` is restriction along `f ≫ g`. -/
@[simp]
lemma sectionsRestrictionComplex_comp_app {U V W : S.C} (f : U ⟶ V) (g : V ⟶ W)
    (I : CochainComplex (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) ℤ) :
    (sectionsRestrictionComplex.{u, v, w, r} S g).app I ≫
        (sectionsRestrictionComplex.{u, v, w, r} S f).app I =
      (sectionsRestrictionComplex.{u, v, w, r} S (f ≫ g)).app I := by
  rw [sectionsRestrictionComplex_comp']
  rfl

variable (sq : Square S.C)

/-- The canonical map `I(X) ⟶ C(β)[-1]`, using the zero null-homotopy.  This is
`Stacks.MayerVietoris.CanonicalMapOfComplexes.cSquare` at the structure sheaf of `S`. -/
abbrev cSquare (I : CochainComplex
    (SheafOfModules.{v} (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) ℤ) :
    (sectionsComplex S sq.X₄).obj I ⟶
      CochainComplex.mappingCocone
        (Stacks.MayerVietoris.CanonicalMapOfComplexes.secondMap.{u, v}
          (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) sq I) :=
  Stacks.MayerVietoris.CanonicalMapOfComplexes.cSquare.{u, v}
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf S.O)) sq I

end Chain

end Stacks.Cohomology.MayerVietoris

end
