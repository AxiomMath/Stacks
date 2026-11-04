module

public import Mathlib.CategoryTheory.Monoidal.NaturalTransformation
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.CategoryTheory.Limits.Preserves.FunctorCategory
public import StacksFrontier.CategoryTheory.Monoidal.ExternalAdjunctionMate
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.DiagonalPointResolution
public import StacksFrontier.Homology.ConstMapDerivedCategoryMonoidal
import StacksCore.Tactic.StacksAttribute

/-!
# The Eilenberg–Zilber comparison for derived lower shriek on a chaotic site

Let `C` be a small category with the chaotic topology and let `E` be a coefficient category. The
total left derived functor `Lπ_! = Stacks.CategoryHomology.totalDerivedColimit` of the colimit over
`Cᵒᵖ` is left adjoint to `π^{-1} = (Functor.const Cᵒᵖ).mapDerivedCategory`, which is strong
monoidal for the derived tensor products, so `Lπ_!` carries the induced oplax monoidal structure.
Its comparison morphism

`Lπ_!(K₁ ⊗^L K₂) ⟶ Lπ_!(K₁) ⊗^L Lπ_!(K₂)`

is `Stacks.CategoryHomology.totalDerivedColimitTensorComparison`. This file shows that it is an
isomorphism when `C` carries a cosimplicial object which is a point resolution, given as
hypotheses the derived-category comparisons along the diagonal `Δ : C ⥤ C × C` and the two
projections `g₁, g₂ : C × C ⥤ C`.

## Main definitions

* `CategoryTheory.Adjunction.restrictionMate`: for two adjunctions `L ⊣ R`, `L' ⊣ R'` and a
  natural transformation `α : R' ⋙ S ⟶ R` between the right adjoints, the mate
  `L (S M) ⟶ L' M`.
* `CategoryTheory.Functor.mapDerivedCategoryCompIsoId`: two exact functors whose composite is the
  identity induce functors on the unbounded derived categories whose composite is isomorphic to
  the identity.
* `Stacks.ChaoticSite.diagPresheafRestriction`,
  `Stacks.ChaoticSite.fstPresheafRestriction`, `Stacks.ChaoticSite.sndPresheafRestriction`:
  restriction of presheaves along the diagonal and the two projections of `C × C`, that is the
  inverse images `Δ^{-1}`, `g₁^{-1}`, `g₂^{-1}` of the corresponding morphisms of chaotic topoi.
* `Stacks.ChaoticSite.fstDerivedRestrictionCompDiagIso`,
  `Stacks.ChaoticSite.sndDerivedRestrictionCompDiagIso`: the derived form of
  `Δ^{-1} ∘ g_i^{-1} = id`.

## Main results

* `CategoryTheory.Adjunction.δ_comp_restrictionMate`: the canonical oplax comparison of a left
  adjoint is transported by the mate of a monoidal natural transformation of the right adjoints.
* `CategoryTheory.Adjunction.isIso_δ_of_isIso_restrictionMate`: the oplax comparison of `L` at
  `(S M₁, S M₂)` is invertible when the mates, the lax structure of `S` and the oplax comparison
  of `L'` are.
* `CategoryTheory.Adjunction.isIso_δ_of_iso`: invertibility of an oplax comparison at a pair of
  objects depends on the pair only up to isomorphism.
* `Stacks.ChaoticSite.diagPresheafRestriction_monoidal`: restriction along the diagonal is strong
  monoidal.
* `Stacks.ChaoticSite.fstPresheafRestriction_comp_diagPresheafRestriction`,
  `Stacks.ChaoticSite.sndPresheafRestriction_comp_diagPresheafRestriction`,
  `Stacks.ChaoticSite.const_comp_diagPresheafRestriction`,
  `Stacks.ChaoticSite.const_comp_fstPresheafRestriction` and
  `Stacks.ChaoticSite.const_comp_sndPresheafRestriction`: the diagonal restriction of an
  external image is the presheaf itself, and the inverse images of the point along the diagonal
  and along the two projections compose as they should, on the nose.
* `Stacks.ChaoticSite.isIso_totalDerivedColimitTensorComparison`: the canonical comparison is an
  isomorphism, given a point resolution `U`, strong monoidality of the derived `Δ^{-1}`, a
  monoidal comparison of the derived inverse images of the point along `Δ`, invertibility of the
  derived mate comparisons along `Δ`, `g₁` and `g₂`, and invertibility of the external mate
  comparison on `C × C`.

## References

* [Stacks Project, Tag 08QC](https://stacks.math.columbia.edu/tag/08QC)
* [Stacks Project, Tag 08QA](https://stacks.math.columbia.edu/tag/08QA)
* [Stacks Project, Tag 08QB](https://stacks.math.columbia.edu/tag/08QB)
* [Stacks Project, Tag 08Q4](https://stacks.math.columbia.edu/tag/08Q4)
* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
* [Stacks Project, Tag 08PH](https://stacks.math.columbia.edu/tag/08PH)
* [Stacks Project, Tag 07A4](https://stacks.math.columbia.edu/tag/07A4)
-/

@[expose] public noncomputable section

open CategoryTheory Limits MonoidalCategory Functor.LaxMonoidal Functor.OplaxMonoidal

namespace CategoryTheory.Adjunction

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]
  {E : Type u₃} [Category.{v₃} E]
  {L : B ⥤ E} {R : E ⥤ B} (adj : L ⊣ R)
  {L' : A ⥤ E} {R' : E ⥤ A} (adj' : L' ⊣ R')
  (S : A ⥤ B) (α : R' ⋙ S ⟶ R)

/-- The comparison morphism `L (S M) ⟶ L' M` attached to a natural transformation
`α : R' ⋙ S ⟶ R` between the right adjoints of two adjunctions: the mate of `α`, that is, the
morphism adjoint to `S (η' M) ≫ α`, where `η'` is the unit of `adj'`. -/
def restrictionMate (M : A) : L.obj (S.obj M) ⟶ L'.obj M :=
  (adj.homEquiv _ _).symm (S.map (adj'.unit.app M) ≫ α.app (L'.obj M))

/-- The defining property of `CategoryTheory.Adjunction.restrictionMate`, written out with the
unit of `adj`. -/
@[reassoc]
lemma unit_comp_map_restrictionMate (M : A) :
    adj.unit.app (S.obj M) ≫ R.map (restrictionMate adj adj' S α M) =
      S.map (adj'.unit.app M) ≫ α.app (L'.obj M) := by
  have h := (adj.homEquiv (S.obj M) (L'.obj M)).apply_symm_apply
    (S.map (adj'.unit.app M) ≫ α.app (L'.obj M))
  rw [homEquiv_unit] at h
  exact h

section Monoidal

variable [MonoidalCategory A] [MonoidalCategory B] [MonoidalCategory E]
  [R.LaxMonoidal] [L.OplaxMonoidal] [adj.IsMonoidal]
  [R'.LaxMonoidal] [L'.OplaxMonoidal] [adj'.IsMonoidal]
  [S.LaxMonoidal] [NatTrans.IsMonoidal α]

/-- **The oplax comparison of a left adjoint is transported by the mate of a monoidal comparison
of the right adjoints.** With `α : R' ⋙ S ⟶ R` a monoidal natural transformation and `c` the
induced comparison `L (S -) ⟶ L'` of `CategoryTheory.Adjunction.restrictionMate`, the square

```
L (S M₁ ⊗ S M₂) --- L (μ S) ---> L (S (M₁ ⊗ M₂)) --- c ---> L' (M₁ ⊗ M₂)
      |                                                           |
      | δ L                                                       | δ L'
      v                                                           v
L (S M₁) ⊗ L (S M₂) ------------- c ⊗ c -----------------> L' M₁ ⊗ L' M₂
```

commutes.  Both oplax structures are the canonical ones, that is, the mates of the lax monoidal
structures of the right adjoints; that is what `adj.IsMonoidal` and `adj'.IsMonoidal` say. -/
lemma δ_comp_restrictionMate (M₁ M₂ : A) :
    δ L (S.obj M₁) (S.obj M₂) ≫
        (restrictionMate adj adj' S α M₁ ⊗ₘ restrictionMate adj adj' S α M₂) =
      L.map (μ S M₁ M₂) ≫ restrictionMate adj adj' S α (M₁ ⊗ M₂) ≫ δ L' M₁ M₂ := by
  apply (adj.homEquiv _ _).injective
  have hα : μ S (R'.obj (L'.obj M₁)) (R'.obj (L'.obj M₂)) ≫
      S.map (μ R' (L'.obj M₁) (L'.obj M₂)) ≫ α.app (L'.obj M₁ ⊗ L'.obj M₂) =
      (α.app (L'.obj M₁) ⊗ₘ α.app (L'.obj M₂)) ≫ μ R (L'.obj M₁) (L'.obj M₂) := by
    simpa only [Functor.LaxMonoidal.comp_μ, Category.assoc] using
      NatTrans.IsMonoidal.tensor (τ := α) (L'.obj M₁) (L'.obj M₂)
  have hL : adj.homEquiv _ _ (δ L (S.obj M₁) (S.obj M₂) ≫
      (restrictionMate adj adj' S α M₁ ⊗ₘ restrictionMate adj adj' S α M₂)) =
      ((S.map (adj'.unit.app M₁) ≫ α.app (L'.obj M₁)) ⊗ₘ
        (S.map (adj'.unit.app M₂) ≫ α.app (L'.obj M₂))) ≫ μ R (L'.obj M₁) (L'.obj M₂) := by
    rw [homEquiv_unit, Functor.map_comp, ← Category.assoc, adj.unit_app_tensor_comp_map_δ,
      Category.assoc, ← μ_natural, ← Category.assoc, tensorHom_comp_tensorHom,
      unit_comp_map_restrictionMate, unit_comp_map_restrictionMate]
  have hR : adj.homEquiv _ _ (L.map (μ S M₁ M₂) ≫
      restrictionMate adj adj' S α (M₁ ⊗ M₂) ≫ δ L' M₁ M₂) =
      ((S.map (adj'.unit.app M₁) ≫ α.app (L'.obj M₁)) ⊗ₘ
        (S.map (adj'.unit.app M₂) ≫ α.app (L'.obj M₂))) ≫ μ R (L'.obj M₁) (L'.obj M₂) := by
    rw [homEquiv_unit, Functor.map_comp, ← Category.assoc, adj.unit_naturality,
      Category.assoc, Functor.map_comp, unit_comp_map_restrictionMate_assoc,
      ← α.naturality, Functor.comp_map,
      ← Functor.map_comp_assoc, adj'.unit_app_tensor_comp_map_δ, Functor.map_comp,
      ← tensorHom_comp_tensorHom]
    simp only [Category.assoc]
    rw [← hα, ← μ_natural_assoc]
    rfl
  rw [hL, hR]

/-- **The canonical oplax comparison of `L` is invertible at `(S M₁, S M₂)`** as soon as the
comparison of `L (S -)` with `L'` is invertible at `M₁`, at `M₂` and at `M₁ ⊗ M₂`, the lax
structure of `S` is invertible at `(M₁, M₂)`, and the canonical oplax comparison of `L'` is
invertible at `(M₁, M₂)`. -/
lemma isIso_δ_of_isIso_restrictionMate (M₁ M₂ : A)
    [IsIso (restrictionMate adj adj' S α M₁)] [IsIso (restrictionMate adj adj' S α M₂)]
    [IsIso (restrictionMate adj adj' S α (M₁ ⊗ M₂))] [IsIso (μ S M₁ M₂)]
    [IsIso (δ L' M₁ M₂)] :
    IsIso (δ L (S.obj M₁) (S.obj M₂)) := by
  have h : IsIso (δ L (S.obj M₁) (S.obj M₂) ≫
      (restrictionMate adj adj' S α M₁ ⊗ₘ restrictionMate adj adj' S α M₂)) := by
    rw [δ_comp_restrictionMate]; infer_instance
  exact IsIso.of_isIso_comp_right _ (restrictionMate adj adj' S α M₁ ⊗ₘ
    restrictionMate adj adj' S α M₂)

end Monoidal

section Transport

variable [MonoidalCategory B] [MonoidalCategory E] (L) [L.OplaxMonoidal]

/-- The invertibility of the canonical oplax comparison of a functor at a pair of objects only
depends on that pair up to isomorphism. -/
lemma isIso_δ_of_iso {X₁ X₂ Y₁ Y₂ : B} (e₁ : X₁ ≅ Y₁) (e₂ : X₂ ≅ Y₂)
    [IsIso (δ L X₁ X₂)] : IsIso (δ L Y₁ Y₂) := by
  have h : IsIso (L.map (e₁.hom ⊗ₘ e₂.hom) ≫ δ L Y₁ Y₂) := by
    rw [← δ_natural L e₁.hom e₂.hom]; infer_instance
  exact IsIso.of_isIso_comp_left (L.map (e₁.hom ⊗ₘ e₂.hom)) _

end Transport

end CategoryTheory.Adjunction

/-! ### Functoriality of `mapDerivedCategory` -/

namespace CategoryTheory.Functor

universe v₁ v₂ u₁ u₂ w₁ w₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] [HasDerivedCategory.{w₁} A]
  {B : Type u₂} [Category.{v₂} B] [Abelian B] [HasDerivedCategory.{w₂} B]

attribute [local instance] comp_preservesFiniteLimits comp_preservesFiniteColimits

/-- **Two exact functors whose composite is the identity induce functors on the unbounded derived
categories whose composite is isomorphic to the identity.**  The isomorphism is obtained from the
universal property of the quasi-isomorphism localization: on cochain complexes the two composites
agree up to the canonical comparisons of `CategoryTheory.Functor.mapHomologicalComplex` with
composition and with the identity. -/
def mapDerivedCategoryCompIsoId (F : A ⥤ B) (G : B ⥤ A)
    [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]
    [G.Additive] [PreservesFiniteLimits G] [PreservesFiniteColimits G]
    (h : F ⋙ G = 𝟭 A) :
    F.mapDerivedCategory ⋙ G.mapDerivedCategory ≅ 𝟭 (DerivedCategory A) :=
  Localization.liftNatIso DerivedCategory.Q
    (HomologicalComplex.quasiIso A (ComplexShape.up ℤ))
    ((F.mapHomologicalComplex (ComplexShape.up ℤ) ⋙ DerivedCategory.Q) ⋙ G.mapDerivedCategory)
    DerivedCategory.Q
    (F.mapDerivedCategory ⋙ G.mapDerivedCategory) (𝟭 _)
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ G.mapDerivedCategoryFactors ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexCompIso (Iso.refl (F ⋙ G)) (ComplexShape.up ℤ)).symm
        DerivedCategory.Q ≪≫
      Functor.isoWhiskerRight
        (NatIso.mapHomologicalComplex (eqToIso h) (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      Functor.isoWhiskerRight
        (Functor.mapHomologicalComplexIdIso A (ComplexShape.up ℤ)) DerivedCategory.Q ≪≫
      Functor.leftUnitor _)

end CategoryTheory.Functor

/-! ### Restriction of presheaves along the diagonal and the two projections -/

namespace Stacks.ChaoticSite

open Stacks.CategoryHomology CochainComplex.KFlatMonoidal CochainComplex.KFlatBifunctor

attribute [local instance] HasDerivedCategory.standard

universe v u

section Presheaves

variable (C : Type u) [SmallCategory C] (E : Type v) [Category.{v} E]

/-- Restriction of presheaves along the diagonal `C ⥤ C × C`: the inverse image of the induced
morphism of chaotic topoi. -/
def diagPresheafRestriction : ((C × C)ᵒᵖ ⥤ E) ⥤ (Cᵒᵖ ⥤ E) :=
  (Functor.whiskeringLeft _ _ _).obj (Functor.diag C).op

/-- Restriction of presheaves along the first projection `C × C ⥤ C`. -/
def fstPresheafRestriction : (Cᵒᵖ ⥤ E) ⥤ ((C × C)ᵒᵖ ⥤ E) :=
  (Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.fst C C).op

/-- Restriction of presheaves along the second projection `C × C ⥤ C`. -/
def sndPresheafRestriction : (Cᵒᵖ ⥤ E) ⥤ ((C × C)ᵒᵖ ⥤ E) :=
  (Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.snd C C).op

/-- Restriction along the diagonal is additive, being computed pointwise. -/
instance diagPresheafRestriction_additive [Preadditive E] :
    (diagPresheafRestriction C E).Additive :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ _).obj (Functor.diag C).op).Additive

/-- Restriction along the diagonal preserves finite limits. -/
instance diagPresheafRestriction_preservesFiniteLimits [HasFiniteLimits E] :
    PreservesFiniteLimits (diagPresheafRestriction C E) :=
  ⟨fun _ ↦ inferInstanceAs
    (PreservesLimitsOfShape _ ((Functor.whiskeringLeft _ _ _).obj (Functor.diag C).op))⟩

/-- Restriction along the diagonal preserves finite colimits. -/
instance diagPresheafRestriction_preservesFiniteColimits [HasFiniteColimits E] :
    PreservesFiniteColimits (diagPresheafRestriction C E) :=
  ⟨fun _ ↦ inferInstanceAs
    (PreservesColimitsOfShape _ ((Functor.whiskeringLeft _ _ _).obj (Functor.diag C).op))⟩

/-- **Restriction along the diagonal is strong monoidal for the pointwise tensor product.**  On a
chaotic site the tensor product of presheaves of modules is computed sectionwise, so the
restriction of `g₁^{-1}F ⊗ g₂^{-1}G` along the diagonal is `F ⊗ G` on the nose; this is the
functorial form of that identity. -/
instance diagPresheafRestriction_monoidal [MonoidalCategory E] :
    (diagPresheafRestriction C E).Monoidal :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ _).obj (Functor.diag C).op).Monoidal

/-- **The diagonal restriction of the first external image is the identity.** Restricting a
presheaf on `C` to `C × C` along the first projection and then back along the diagonal returns
it unchanged, because `Δ ⋙ pr₁ = 𝟙`. -/
lemma fstPresheafRestriction_comp_diagPresheafRestriction :
    fstPresheafRestriction C E ⋙ diagPresheafRestriction C E = 𝟭 (Cᵒᵖ ⥤ E) :=
  rfl

/-- **The diagonal restriction of the second external image is the identity.** -/
lemma sndPresheafRestriction_comp_diagPresheafRestriction :
    sndPresheafRestriction C E ⋙ diagPresheafRestriction C E = 𝟭 (Cᵒᵖ ⥤ E) :=
  rfl

/-- **The diagonal restriction of a constant presheaf is constant.** This is the identity
`Δ^{-1} ∘ π^{-1}_{C × C} = π^{-1}_C` between the inverse images of the two projections to the
point; it holds on the nose. -/
lemma const_comp_diagPresheafRestriction :
    (Functor.const ((C × C)ᵒᵖ) : E ⥤ _) ⋙ diagPresheafRestriction C E =
      (Functor.const Cᵒᵖ : E ⥤ _) :=
  rfl

/-- **Restricting a constant presheaf along the first projection gives a constant presheaf.**
This is the identity `g₁^{-1} ∘ π_1^{-1} = π^{-1}` between the inverse images of the point; it
holds on the nose. -/
lemma const_comp_fstPresheafRestriction :
    (Functor.const Cᵒᵖ : E ⥤ _) ⋙ fstPresheafRestriction C E =
      (Functor.const ((C × C)ᵒᵖ) : E ⥤ _) :=
  rfl

/-- **Restricting a constant presheaf along the second projection gives a constant presheaf.** -/
lemma const_comp_sndPresheafRestriction :
    (Functor.const Cᵒᵖ : E ⥤ _) ⋙ sndPresheafRestriction C E =
      (Functor.const ((C × C)ᵒᵖ) : E ⥤ _) :=
  rfl

/-- Restriction along the first projection is additive, being computed pointwise. -/
instance fstPresheafRestriction_additive [Preadditive E] :
    (fstPresheafRestriction C E).Additive :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.fst C C).op).Additive

/-- Restriction along the second projection is additive, being computed pointwise. -/
instance sndPresheafRestriction_additive [Preadditive E] :
    (sndPresheafRestriction C E).Additive :=
  inferInstanceAs ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.snd C C).op).Additive

/-- Restriction along the first projection preserves finite limits. -/
instance fstPresheafRestriction_preservesFiniteLimits [HasFiniteLimits E] :
    PreservesFiniteLimits (fstPresheafRestriction C E) :=
  ⟨fun _ ↦ inferInstanceAs (PreservesLimitsOfShape _
    ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.fst C C).op))⟩

/-- Restriction along the second projection preserves finite limits. -/
instance sndPresheafRestriction_preservesFiniteLimits [HasFiniteLimits E] :
    PreservesFiniteLimits (sndPresheafRestriction C E) :=
  ⟨fun _ ↦ inferInstanceAs (PreservesLimitsOfShape _
    ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.snd C C).op))⟩

/-- Restriction along the first projection preserves finite colimits. -/
instance fstPresheafRestriction_preservesFiniteColimits [HasFiniteColimits E] :
    PreservesFiniteColimits (fstPresheafRestriction C E) :=
  ⟨fun _ ↦ inferInstanceAs (PreservesColimitsOfShape _
    ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.fst C C).op))⟩

/-- Restriction along the second projection preserves finite colimits. -/
instance sndPresheafRestriction_preservesFiniteColimits [HasFiniteColimits E] :
    PreservesFiniteColimits (sndPresheafRestriction C E) :=
  ⟨fun _ ↦ inferInstanceAs (PreservesColimitsOfShape _
    ((Functor.whiskeringLeft _ _ _).obj (CategoryTheory.Prod.snd C C).op))⟩

/-- **The diagonal restriction of the first external image is the identity on derived
categories.**  This is the derived form of
`Stacks.ChaoticSite.fstPresheafRestriction_comp_diagPresheafRestriction`: the two restrictions are
exact, so the definitional identity of presheaf-level functors descends through the
quasi-isomorphism localization. -/
def fstDerivedRestrictionCompDiagIso [Abelian E] :
    (fstPresheafRestriction C E).mapDerivedCategory ⋙
        (diagPresheafRestriction C E).mapDerivedCategory ≅
      𝟭 (DerivedCategory (Cᵒᵖ ⥤ E)) :=
  Functor.mapDerivedCategoryCompIsoId _ _
    (fstPresheafRestriction_comp_diagPresheafRestriction C E)

/-- **The diagonal restriction of the second external image is the identity on derived
categories.** -/
def sndDerivedRestrictionCompDiagIso [Abelian E] :
    (sndPresheafRestriction C E).mapDerivedCategory ⋙
        (diagPresheafRestriction C E).mapDerivedCategory ≅
      𝟭 (DerivedCategory (Cᵒᵖ ⥤ E)) :=
  Functor.mapDerivedCategoryCompIsoId _ _
    (sndPresheafRestriction_comp_diagPresheafRestriction C E)
end Presheaves

/-! ### The Eilenberg–Zilber comparison -/

section EilenbergZilber

variable (C : Type u) [SmallCategory C] (E : Type v) [Category.{v} E] [Abelian E]
  [MonoidalCategory E] [MonoidalPreadditive E]
  [HasCoproducts.{0} E] [HasColimitsOfSize.{0, 0} E] [HasInitial E]
  [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorLeft X)]
  [∀ X : E, PreservesColimitsOfSize.{0, 0} (tensorRight X)]
  [∀ X : E, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorLeft X)]
  [∀ X : E, PreservesColimitsOfShape (Discrete PEmpty.{1}) (tensorRight X)]
  [BraidedCategory (CochainComplex E ℤ)] [BraidedCategory (CochainComplex (Cᵒᵖ ⥤ E) ℤ)]
  [BraidedCategory (CochainComplex ((C × C)ᵒᵖ ⥤ E) ℤ)]
  [EnoughProjectives (Cᵒᵖ ⥤ E)] [EnoughProjectives ((C × C)ᵒᵖ ⥤ E)]
  [HasColimitsOfShape ℕ E] [HasExactColimitsOfShape ℕ E]
  [HasColimitsOfShape Cᵒᵖ E] [HasColimitsOfShape (C × C)ᵒᵖ E]
  (hresE : ∀ G : CochainComplex E ℤ, ∃ (P : CochainComplex E ℤ) (f : P ⟶ G),
    KFlat (curriedTensor E) P ∧ QuasiIso f)
  (hresCE : ∀ G : CochainComplex (Cᵒᵖ ⥤ E) ℤ, ∃ (P : CochainComplex (Cᵒᵖ ⥤ E) ℤ) (f : P ⟶ G),
    KFlat (curriedTensor (Cᵒᵖ ⥤ E)) P ∧ QuasiIso f)
  (hresCCE : ∀ G : CochainComplex ((C × C)ᵒᵖ ⥤ E) ℤ,
    ∃ (P : CochainComplex ((C × C)ᵒᵖ ⥤ E) ℤ) (f : P ⟶ G),
      KFlat (curriedTensor ((C × C)ᵒᵖ ⥤ E)) P ∧ QuasiIso f)

omit [HasColimitsOfSize.{0, 0} E] in
/-- The canonical comparison `Lπ_!(K₁ ⊗^L K₂) ⟶ Lπ_!(K₁) ⊗^L Lπ_!(K₂)` of derived lower shriek on
the chaotic site `C`, `Stacks.CategoryHomology.totalDerivedColimitTensorComparison`, is an
isomorphism when `C` carries a cosimplicial object `U` which is a point resolution, given the
following hypotheses:

* `_h07A4`: `(diagPresheafRestriction C E).mapDerivedCategory` is strong monoidal;
* `_h08PH`: the transformation `α` from the derived `Δ^{-1} ∘ π^{-1}_{C × C}` to the derived
  `π^{-1}_C` is monoidal;
* `_h08QA`: the mate `Lπ_!(Δ^{-1}M) ⟶ L(π × π)_!(M)` of `α` is invertible whenever some
  cosimplicial object `V` of `C` and its diagonal image are point resolutions;
* `_h08QA₁`, `_h08QA₂`: the mates `L(π × π)_!(g_i^{-1}M) ⟶ Lπ_!(M)` of the transformations `α₁`,
  `α₂` are invertible whenever some cosimplicial object `V` of `C × C` and its `i`-th projection
  are point resolutions;
* `_h08QB`: the external mate `L(π × π)_!(g₁^{-1}K₁ ⊗^L g₂^{-1}K₂) ⟶ Lπ_!K₁ ⊗^L Lπ_!K₂` of `α₁`
  and `α₂` is invertible.

The hypotheses `hresE`, `hresCE`, `hresCCE` provide the K-flat resolutions defining the three
derived tensor products. -/
@[stacks 08QC "RESTRICTED: assumes Tags 07A4, 08PH, 08QA (diagonal and both projections) and 08QB at the derived level"]
theorem isIso_totalDerivedColimitTensorComparison
    (U : CosimplicialObject C) (hU : IsPointResolution U)
    (K₁ K₂ : DerivedCategory (Cᵒᵖ ⥤ E)) :
    letI := derivedMonoidal E hresE
    letI := derivedMonoidal (Cᵒᵖ ⥤ E) hresCE
    letI := derivedMonoidal ((C × C)ᵒᵖ ⥤ E) hresCCE
    letI := Functor.constMapDerivedCategoryMonoidal hresE hresCE
    letI := Functor.constMapDerivedCategoryMonoidal hresE hresCCE
    letI := totalDerivedColimitOplaxMonoidal C E hresE hresCE
    letI := totalDerivedColimitOplaxMonoidal (C × C) E hresE hresCCE
    ∀ (_h07A4 : (diagPresheafRestriction C E).mapDerivedCategory.Monoidal)
      (α : (Functor.const ((C × C)ᵒᵖ) : E ⥤ _).mapDerivedCategory ⋙
            (diagPresheafRestriction C E).mapDerivedCategory ⟶
          (Functor.const Cᵒᵖ : E ⥤ _).mapDerivedCategory)
      (_h08PH : NatTrans.IsMonoidal α)
      (_h08QA : ∀ V : CosimplicialObject C, IsPointResolution V →
          IsPointResolution (V ⋙ Functor.diag C) →
          ∀ M : DerivedCategory ((C × C)ᵒᵖ ⥤ E),
            IsIso ((totalDerivedColimitAdjunction C E).restrictionMate
              (totalDerivedColimitAdjunction (C × C) E)
              (diagPresheafRestriction C E).mapDerivedCategory α M))
      (α₁ : (Functor.const Cᵒᵖ : E ⥤ _).mapDerivedCategory ⋙
            (fstPresheafRestriction C E).mapDerivedCategory ⟶
          (Functor.const ((C × C)ᵒᵖ) : E ⥤ _).mapDerivedCategory)
      (α₂ : (Functor.const Cᵒᵖ : E ⥤ _).mapDerivedCategory ⋙
            (sndPresheafRestriction C E).mapDerivedCategory ⟶
          (Functor.const ((C × C)ᵒᵖ) : E ⥤ _).mapDerivedCategory)
      (_h08QA₁ : ∀ V : CosimplicialObject (C × C), IsPointResolution V →
          IsPointResolution (V ⋙ CategoryTheory.Prod.fst C C) →
          ∀ M : DerivedCategory (Cᵒᵖ ⥤ E),
            IsIso ((totalDerivedColimitAdjunction (C × C) E).restrictionMate
              (totalDerivedColimitAdjunction C E)
              (fstPresheafRestriction C E).mapDerivedCategory α₁ M))
      (_h08QA₂ : ∀ V : CosimplicialObject (C × C), IsPointResolution V →
          IsPointResolution (V ⋙ CategoryTheory.Prod.snd C C) →
          ∀ M : DerivedCategory (Cᵒᵖ ⥤ E),
            IsIso ((totalDerivedColimitAdjunction (C × C) E).restrictionMate
              (totalDerivedColimitAdjunction C E)
              (sndPresheafRestriction C E).mapDerivedCategory α₂ M))
      (_h08QB : IsIso ((totalDerivedColimitAdjunction (C × C) E).externalMate
          (totalDerivedColimitAdjunction C E) (totalDerivedColimitAdjunction C E)
          (fstPresheafRestriction C E).mapDerivedCategory
          (sndPresheafRestriction C E).mapDerivedCategory α₁ α₂ K₁ K₂)),
      IsIso (totalDerivedColimitTensorComparison C E hresE hresCE K₁ K₂) := by
  let _ := derivedMonoidal E hresE
  let _ := derivedMonoidal (Cᵒᵖ ⥤ E) hresCE
  let _ := derivedMonoidal ((C × C)ᵒᵖ ⥤ E) hresCCE
  let _ := Functor.constMapDerivedCategoryMonoidal hresE hresCE
  let _ := Functor.constMapDerivedCategoryMonoidal hresE hresCCE
  let _ := totalDerivedColimitOplaxMonoidal C E hresE hresCE
  let _ := totalDerivedColimitOplaxMonoidal (C × C) E hresE hresCCE
  intro h07A4 α h08PH h08QA α₁ α₂ h08QA₁ h08QA₂ h08QB
  let _ := h07A4
  have _hc₁ := h08QA₁ (U ⋙ Functor.diag C) (isPointResolution_comp_diag U hU) hU K₁
  have _hc₂ := h08QA₂ (U ⋙ Functor.diag C) (isPointResolution_comp_diag U hU) hU K₂
  have _hδ : IsIso (Functor.OplaxMonoidal.δ (totalDerivedColimit (C × C) E)
      ((fstPresheafRestriction C E).mapDerivedCategory.obj K₁)
      ((sndPresheafRestriction C E).mapDerivedCategory.obj K₂)) :=
    (totalDerivedColimitAdjunction (C × C) E).isIso_δ_of_isIso_externalMate
      (totalDerivedColimitAdjunction C E) (totalDerivedColimitAdjunction C E)
      (fstPresheafRestriction C E).mapDerivedCategory
      (sndPresheafRestriction C E).mapDerivedCategory α₁ α₂ K₁ K₂ _ _
      ((totalDerivedColimitAdjunction (C × C) E).unit_comp_map_restrictionMate
        (totalDerivedColimitAdjunction C E)
        (fstPresheafRestriction C E).mapDerivedCategory α₁ K₁)
      ((totalDerivedColimitAdjunction (C × C) E).unit_comp_map_restrictionMate
        (totalDerivedColimitAdjunction C E)
        (sndPresheafRestriction C E).mapDerivedCategory α₂ K₂)
  have := h08QA U hU (isPointResolution_comp_diag U hU)
  have : IsIso (Functor.OplaxMonoidal.δ (totalDerivedColimit C E)
      (((fstPresheafRestriction C E).mapDerivedCategory ⋙
        (diagPresheafRestriction C E).mapDerivedCategory).obj K₁)
      (((sndPresheafRestriction C E).mapDerivedCategory ⋙
        (diagPresheafRestriction C E).mapDerivedCategory).obj K₂)) :=
    (totalDerivedColimitAdjunction C E).isIso_δ_of_isIso_restrictionMate
      (totalDerivedColimitAdjunction (C × C) E)
      (diagPresheafRestriction C E).mapDerivedCategory α _ _
  exact Adjunction.isIso_δ_of_iso (totalDerivedColimit C E)
    ((fstDerivedRestrictionCompDiagIso C E).app K₁)
    ((sndDerivedRestrictionCompDiagIso C E).app K₂)

end EilenbergZilber

end Stacks.ChaoticSite

end
