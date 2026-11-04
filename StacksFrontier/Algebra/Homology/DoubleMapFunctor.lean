module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.Double

/-!
# A functor applied termwise to a two-term complex

Let `f : X₀ ⟶ X₁` be a morphism in a category with zero morphisms and a zero object, let `i₀`,
`i₁` be two degrees with `c.Rel i₀ i₁` and `i₀ ≠ i₁`, and let `F` be a functor preserving zero
morphisms. The complex `HomologicalComplex.double f` is `f` placed in degrees `i₀` and `i₁` and
zero elsewhere, so applying `F` termwise to it gives a complex which is `F.map f` in those two
degrees and `F.obj 0` elsewhere. That complex is canonically isomorphic to
`HomologicalComplex.double (F.map f)`.

The point of the identification is that a construction available for a `double` — for instance
the distinguished triangle relating it to its two terms — becomes available for the termwise
image of a `double` under a functor.

## Main definitions

* `HomologicalComplex.doubleMapFunctorHom`: the comparison morphism
  `double (F.map f) ⟶ (F.mapHomologicalComplex c).obj (double f)`, given in the two nonzero
  degrees by `F` applied to the identifications of the terms of `double f`.
* `HomologicalComplex.doubleMapFunctorIso`: that morphism as an isomorphism.

## Main results

* `HomologicalComplex.isIso_doubleMapFunctorHom`: the comparison morphism is an isomorphism. In
  the two degrees `i₀` and `i₁` it is `F` applied to an isomorphism, and in every other degree
  both complexes vanish, the termwise image because `F` preserves zero morphisms and hence zero
  objects.

## Implementation notes

The comparison morphism goes *out of* `double (F.map f)` so that it can be produced by
`HomologicalComplex.mkHomFromDouble`, whose only data are the two nonzero components. Only
`CategoryTheory.Functor.PreservesZeroMorphisms` is required of `F`, not additivity: that is
already what `CategoryTheory.Functor.mapHomologicalComplex` asks for.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Category CategoryTheory.Limits

universe v₁ u₁ v₂ u₂

namespace HomologicalComplex

variable {C : Type u₁} [Category.{v₁} C] [HasZeroMorphisms C] [HasZeroObject C]
  {D : Type u₂} [Category.{v₂} D] [HasZeroMorphisms D] [HasZeroObject D]
  (F : C ⥤ D) [F.PreservesZeroMorphisms] {X₀ X₁ : C} (f : X₀ ⟶ X₁)
  {ι : Type*} {c : ComplexShape ι} {i₀ i₁ : ι} (hi₀₁ : c.Rel i₀ i₁) (h : i₀ ≠ i₁)

/-- The comparison morphism from the two-term complex `HomologicalComplex.double (F.map f)` to
the termwise image under `F` of `HomologicalComplex.double f`. In degree `i₀` and in degree `i₁`
it is `F` applied to the identification of the corresponding term of `double f`. -/
def doubleMapFunctorHom :
    double (F.map f) hi₀₁ ⟶ (F.mapHomologicalComplex c).obj (double f hi₀₁) :=
  mkHomFromDouble hi₀₁ h (F.map (doubleXIso₀ f hi₀₁).inv)
    (F.map (doubleXIso₁ f hi₀₁ h).inv)
    (by
      dsimp only [Functor.mapHomologicalComplex_obj_d]
      rw [double_d f hi₀₁ h, ← F.map_comp, ← F.map_comp, Iso.inv_hom_id_assoc])
    (fun k _ => by
      dsimp only [Functor.mapHomologicalComplex_obj_d]
      rw [double_d_eq_zero₀ f hi₀₁ i₁ k h.symm, F.map_zero, comp_zero])

/-- A morphism of complexes which is an isomorphism in degrees `i₀` and `i₁`, between complexes
vanishing in all other degrees, is an isomorphism. -/
private theorem isIso_of_isIso_f_of_isZero_X {E : Type*} [Category E] [HasZeroMorphisms E]
    {K L : HomologicalComplex E c} (φ : K ⟶ L) (e₀ : IsIso (φ.f i₀)) (e₁ : IsIso (φ.f i₁))
    (hK : ∀ n, n ≠ i₀ → n ≠ i₁ → IsZero (K.X n)) (hL : ∀ n, n ≠ i₀ → n ≠ i₁ → IsZero (L.X n)) :
    IsIso φ := by
  have : ∀ n, IsIso (φ.f n) := by
    intro n
    by_cases h₀ : n = i₀
    · rw [h₀]; exact e₀
    by_cases h₁ : n = i₁
    · rw [h₁]; exact e₁
    have hn : φ.f n = ((hK n h₀ h₁).iso (hL n h₀ h₁)).hom := (hK n h₀ h₁).eq_of_src _ _
    rw [hn]
    infer_instance
  exact HomologicalComplex.Hom.isIso_of_components _

/-- **A functor preserving zero morphisms commutes with the two-term complex construction.** The
comparison morphism from `HomologicalComplex.double (F.map f)` to the termwise image under `F`
of `HomologicalComplex.double f` is an isomorphism. -/
theorem isIso_doubleMapFunctorHom : IsIso (doubleMapFunctorHom F f hi₀₁ h) := by
  refine isIso_of_isIso_f_of_isZero_X _ ?_ ?_ (fun n h₀ h₁ => isZero_double_X _ hi₀₁ n h₀ h₁)
    (fun n h₀ h₁ => F.map_isZero (isZero_double_X f hi₀₁ n h₀ h₁))
  · rw [doubleMapFunctorHom, mkHomFromDouble_f₀]
    infer_instance
  · rw [doubleMapFunctorHom, mkHomFromDouble_f₁]
    infer_instance

/-- **A functor preserving zero morphisms commutes with the two-term complex construction.** The
identification of `HomologicalComplex.double (F.map f)` with the termwise image under `F` of
`HomologicalComplex.double f`, for `f` in degrees `i₀` and `i₁` with `i₀ ≠ i₁`. -/
def doubleMapFunctorIso :
    (double (F.map f) hi₀₁ : HomologicalComplex D c) ≅
      (F.mapHomologicalComplex c).obj (double f hi₀₁) :=
  have := isIso_doubleMapFunctorHom F f hi₀₁ h
  asIso (doubleMapFunctorHom F f hi₀₁ h)

/-- The differential of a two-term complex, read through the canonical identification of its
target term, is the morphism the complex is built from, read through the identification of its
source term. -/
@[reassoc]
theorem double_d_comp_doubleXIso₁_hom :
    (double f hi₀₁).d i₀ i₁ ≫ (doubleXIso₁ f hi₀₁ h).hom = (doubleXIso₀ f hi₀₁).hom ≫ f := by
  rw [double_d f hi₀₁ h, assoc, assoc, Iso.inv_hom_id, comp_id]

/-- The differential of a two-term complex, precomposed with the canonical identification of its
source term, is the morphism the complex is built from, postcomposed with the identification of
its target term. -/
@[reassoc]
theorem doubleXIso₀_inv_comp_double_d :
    (doubleXIso₀ f hi₀₁).inv ≫ (double f hi₀₁).d i₀ i₁ = f ≫ (doubleXIso₁ f hi₀₁ h).inv := by
  rw [double_d f hi₀₁ h, Iso.inv_hom_id_assoc]

section Square

variable {Y₀ Y₁ : C} (g : Y₀ ⟶ Y₁) (e₀ : X₀ ≅ Y₀) (e₁ : X₁ ≅ Y₁)

/-- The comparison morphism `double f ⟶ double g` attached to a commuting square whose two
vertical maps are isomorphisms: in the two nonzero degrees it is `e₀` resp. `e₁`, read through
the canonical identifications of the terms. -/
def doubleSquareHom (w : f ≫ e₁.hom = e₀.hom ≫ g) : double f hi₀₁ ⟶ double g hi₀₁ :=
  mkHomFromDouble hi₀₁ h (e₀.hom ≫ (doubleXIso₀ g hi₀₁).inv)
    (e₁.hom ≫ (doubleXIso₁ g hi₀₁ h).inv)
    (by rw [double_d g hi₀₁ h, assoc, Iso.inv_hom_id_assoc, ← assoc, ← w, assoc])
    (fun k _ ↦ by rw [double_d_eq_zero₀ g hi₀₁ i₁ k h.symm, comp_zero])

/-- **The two-term complexes of the two horizontal sides of a commuting square whose vertical
maps are isomorphisms are isomorphic.** -/
theorem isIso_doubleSquareHom (w : f ≫ e₁.hom = e₀.hom ≫ g) :
    IsIso (doubleSquareHom f hi₀₁ h g e₀ e₁ w) := by
  refine isIso_of_isIso_f_of_isZero_X _ ?_ ?_ (fun n h₀ h₁ => isZero_double_X _ hi₀₁ n h₀ h₁)
    (fun n h₀ h₁ => isZero_double_X _ hi₀₁ n h₀ h₁)
  · rw [doubleSquareHom, mkHomFromDouble_f₀]
    infer_instance
  · rw [doubleSquareHom, mkHomFromDouble_f₁]
    infer_instance

/-- **A commuting square whose vertical maps are isomorphisms induces an isomorphism of the
two-term complexes of its two horizontal sides.** -/
def doubleSquareIso (w : f ≫ e₁.hom = e₀.hom ≫ g) :
    (double f hi₀₁ : HomologicalComplex C c) ≅ double g hi₀₁ :=
  have := isIso_doubleSquareHom f hi₀₁ h g e₀ e₁ w
  asIso (doubleSquareHom f hi₀₁ h g e₀ e₁ w)

end Square

end HomologicalComplex

end
