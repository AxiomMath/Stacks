module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughInjectives
public import StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents

/-!
# An injective object represents cohomology in the derived category

Let `𝒜` be an abelian category, `E` an injective object of `𝒜` and `q : ℤ`. Writing `E[q]` for
the image of `E` under `𝒜 ⥤ D(𝒜)`, the complex concentrated in degree `q`, this file proves that
taking cohomology in degree `q` is a bijection
`Hom_{D(𝒜)}(X, E[q]) ≅ Hom_𝒜(H^q(X), E)`
for an **arbitrary** object `X` of the unbounded derived category: no boundedness and no
`IsLE q` hypothesis. In other words `E[q]` represents the functor `H^q` on all of `D(𝒜)`.

This is the dual of `StacksFrontier.Algebra.Homology.DerivedCategory.ProjectiveCorepresents`. For
`X` with `X.IsLE q` the statement holds for every object `E` of `𝒜`, by full faithfulness of
`𝒜 ⥤ D(𝒜)` (Stacks 06XS). Injectivity of `E` is needed only to make `Hom_{D(𝒜)}(Z, E[q])`
vanish for every `Z` in degrees `> q`, which reduces a general `X` to its truncation `τ_{<q+1}X`.

## Main results

* `DerivedCategory.to_singleFunctor_obj_eq_zero_of_isGE_of_injective` — for `E` injective,
  every morphism `X ⟶ E[q]` with `X` in degrees `≥ n > q` is zero.
* `DerivedCategory.homologyToSingle` — the comparison map
  `Hom_{D(𝒜)}(X, E[q]) →+ Hom_𝒜(H^q(X), E)`, defined for every `E` and every `X`, natural in
  `X` (`DerivedCategory.homologyToSingle_comp`).
* `DerivedCategory.bijective_homologyToSingle_of_isLE` — it is bijective when `X.IsLE q`, with
  no hypothesis on `E`.
* `DerivedCategory.bijective_homologyToSingle_of_injective` — it is bijective for `E` injective
  and `X` arbitrary.
* `DerivedCategory.homologyToSingleAddEquiv` — the resulting additive isomorphism
  `Hom_{D(𝒜)}(X, E[q]) ≃+ Hom_𝒜(H^q(X), E)`.
* `DerivedCategory.homologyToSingleLinearEquiv` — the same isomorphism as a map of `R`-modules
  when `𝒜` is `R`-linear.

## References

* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated Triangulated

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If `E` is injective and `X` is an object of `D(𝒜)` concentrated in degrees `≥ n` with
`q < n`, then every morphism `X ⟶ E[q]` vanishes. This is the derived-category form of
Mathlib's `DerivedCategory.to_singleFunctor_obj_eq_zero_of_injective`, which is stated for
morphisms between the images of two cochain complexes. -/
theorem to_singleFunctor_obj_eq_zero_of_isGE_of_injective {E : C} [Injective E] {q n : ℤ}
    (hn : q < n) (X : DerivedCategory C) [X.IsGE n]
    (f : X ⟶ (singleFunctor C q).obj E) : f = 0 := by
  obtain ⟨L, _, ⟨e⟩⟩ := X.exists_iso_Q_obj_of_isGE n
  have he := (singleFunctorIsoCompQ C q).app E
  rw [← cancel_epi e.inv, ← cancel_mono he.hom, comp_zero, zero_comp, assoc]
  exact to_singleFunctor_obj_eq_zero_of_injective (e.inv ≫ f ≫ he.hom) n hn

variable (X : DerivedCategory C) (E : C) (q : ℤ)

/-- Taking cohomology in degree `q` of a morphism `X ⟶ E[q]` in the derived category of an
abelian category `𝒜`, read through the identification `H^q(E[q]) = E`: the comparison map
`Hom_{D(𝒜)}(X, E[q]) ⟶ Hom_𝒜(H^q(X), E)`. It is an isomorphism as soon as `E` is injective
(`DerivedCategory.homologyToSingleAddEquiv`). -/
def homologyToSingle :
    (X ⟶ (singleFunctor C q).obj E) →+ ((homologyFunctor C q).obj X ⟶ E) where
  toFun f := (homologyFunctor C q).map f ≫ (singleFunctorCompHomologyFunctorIso C q).hom.app E
  map_zero' := by simp
  map_add' f g := by simp only [Functor.map_add, Preadditive.add_comp]

/-- The comparison map of `DerivedCategory.homologyToSingle` on a morphism. -/
@[simp]
lemma homologyToSingle_apply (f : X ⟶ (singleFunctor C q).obj E) :
    homologyToSingle X E q f =
      (homologyFunctor C q).map f ≫ (singleFunctorCompHomologyFunctorIso C q).hom.app E :=
  rfl

/-- The comparison map `Hom_{D(𝒜)}(-, E[q]) ⟶ Hom_𝒜(H^q(-), E)` is natural in its variable. -/
lemma homologyToSingle_comp {X' : DerivedCategory C} (g : X' ⟶ X)
    (f : X ⟶ (singleFunctor C q).obj E) :
    homologyToSingle X' E q (g ≫ f) =
      (homologyFunctor C q).map g ≫ homologyToSingle X E q f := by
  simp

/-- Postcomposition with the isomorphism `H^q(E[q]) ≅ E` is bijective on morphisms, so the
comparison map of `DerivedCategory.homologyToSingle` is bijective exactly when taking cohomology
in degree `q` is. -/
private lemma bijective_homologyToSingle_iff :
    Function.Bijective (homologyToSingle X E q) ↔
      Function.Bijective (fun f : X ⟶ (singleFunctor C q).obj E ↦
        (homologyFunctor C q).map f) := by
  have key : (homologyToSingle X E q : _ → _) =
      (fun k : (homologyFunctor C q).obj X ⟶
          (homologyFunctor C q).obj ((singleFunctor C q).obj E) ↦
        k ≫ (singleFunctorCompHomologyFunctorIso C q).hom.app E) ∘
        (fun f : X ⟶ (singleFunctor C q).obj E ↦ (homologyFunctor C q).map f) := rfl
  rw [key]
  exact Function.Bijective.of_comp_iff'
    (Iso.homToEquiv ((singleFunctorCompHomologyFunctorIso C q).app E)).bijective _

/-- An object of `D(𝒜)` concentrated in degrees `≤ q` sees `E[q]` as a representative of `H^q`,
for every object `E` of `𝒜`: this is the full faithfulness of `𝒜 ⥤ D(𝒜)`, and needs no
injectivity. -/
theorem bijective_homologyToSingle_of_isLE [X.IsLE q] :
    Function.Bijective (homologyToSingle X E q) := by
  rw [bijective_homologyToSingle_iff]
  have key : (fun f : X ⟶ (singleFunctor C q).obj E ↦ (homologyFunctor C q).map f) =
      (fun g : X ⟶ ((singleFunctor C q).obj E)⟦(0 : ℤ)⟧ ↦
        ((homologyFunctor C 0).shiftMap g q q (zero_add q) :
          (homologyFunctor C q).obj X ⟶
            (homologyFunctor C q).obj ((singleFunctor C q).obj E))) ∘
        (Iso.homToEquiv
          ((shiftFunctorZero (DerivedCategory C) ℤ).app
            ((singleFunctor C q).obj E)).symm) := by
    funext f
    dsimp only [Function.comp_apply, Iso.homToEquiv_apply, Iso.symm_hom]
    simp only [Functor.shiftMap, Functor.shiftIso_zero_hom_app, shift_homologyFunctor,
      ← Functor.map_comp, assoc]
    simp
  rw [key]
  exact (bijective_homologyFunctor_shiftMap_of_isLE_of_isGE X _ q q 0 q (zero_add q)
    le_rfl).comp (Equiv.bijective _)

/-- For `E` injective, the comparison map of `DerivedCategory.homologyToSingle` is bijective at
`X` as soon as `X` sits in a distinguished triangle `X₁ ⟶ X ⟶ X₃ ⟶ X₁⟦1⟧` with `X₁` in degrees
`≤ q` and `X₃` in degrees `≥ q + 1`. -/
private lemma bijective_homologyToSingle_of_distTriang [Injective E]
    {X₁ X₃ : DerivedCategory C} [X₁.IsLE q] [X₃.IsGE (q + 1)]
    (f₁ : X₁ ⟶ X) (f₂ : X ⟶ X₃) (f₃ : X₃ ⟶ X₁⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang (DerivedCategory C)) :
    Function.Bijective (homologyToSingle X E q) := by
  have : TStructure.t.IsGE (X₃⟦(-1 : ℤ)⟧) (q + 2) :=
    TStructure.t.isGE_shift _ (q + 1) (-1) (q + 2) (by omega)
  have hcomp : Function.Bijective (fun f : X ⟶ (singleFunctor C q).obj E ↦ f₁ ≫ f) := by
    refine ⟨fun g₁ g₂ hg ↦ ?_, fun k ↦ ?_⟩
    · rw [← sub_eq_zero]
      obtain ⟨g, hg'⟩ := Triangle.yoneda_exact₂ _ hT (g₁ - g₂)
        (by rw [Preadditive.comp_sub, sub_eq_zero]; exact hg)
      rw [hg', to_singleFunctor_obj_eq_zero_of_isGE_of_injective (n := q + 1) (by omega) X₃ g,
        comp_zero]
    · obtain ⟨g, hg⟩ := Triangle.yoneda_exact₂ _ (inv_rot_of_distTriang _ hT) k
        (to_singleFunctor_obj_eq_zero_of_isGE_of_injective (n := q + 2) (by omega) (X₃⟦(-1 : ℤ)⟧) _)
      exact ⟨g, hg.symm⟩
  have : Epi ((homologyFunctor C q).map f₁) :=
    (HomologySequence.epi_homologyMap_mor₁_iff _ hT q).2 
      ((isZero_of_isGE X₃ (q + 1) q (by omega)).eq_of_tgt _ _)
  have : Mono ((homologyFunctor C q).map f₁) :=
    (HomologySequence.mono_homologyMap_mor₁_iff _ hT (q - 1) q (by omega)).2
      ((isZero_of_isGE X₃ (q + 1) (q - 1) (by omega)).eq_of_src _ _)
  have : IsIso ((homologyFunctor C q).map f₁) := isIso_of_mono_of_epi _
  have hkey : Function.Bijective (fun f : X ⟶ (singleFunctor C q).obj E ↦
      (homologyFunctor C q).map f₁ ≫ (homologyFunctor C q).map f) := by
    have key : (fun f : X ⟶ (singleFunctor C q).obj E ↦
        (homologyFunctor C q).map f₁ ≫ (homologyFunctor C q).map f) =
        (fun g : X₁ ⟶ (singleFunctor C q).obj E ↦ (homologyFunctor C q).map g) ∘
          (fun f : X ⟶ (singleFunctor C q).obj E ↦ f₁ ≫ f) := by
      funext f
      simp
    rw [key]
    exact ((bijective_homologyToSingle_iff X₁ E q).1
      (bijective_homologyToSingle_of_isLE X₁ E q)).comp hcomp
  rw [bijective_homologyToSingle_iff]
  exact (Function.Bijective.of_comp_iff'
    (Iso.homFromEquiv (asIso ((homologyFunctor C q).map f₁)).symm).bijective _).mp hkey

/-- An injective object `E` of an abelian category `𝒜` represents cohomology in degree `q` on
the whole unbounded derived category: for every object `X` of `D(𝒜)`, taking cohomology in
degree `q` is a bijection `Hom_{D(𝒜)}(X, E[q]) ⟶ Hom_𝒜(H^q(X), E)`. -/
theorem bijective_homologyToSingle_of_injective [Injective E] :
    Function.Bijective (homologyToSingle X E q) :=
  bijective_homologyToSingle_of_distTriang X E q
    ((TStructure.t.truncLTι (q + 1)).app X) ((TStructure.t.truncGEπ (q + 1)).app X)
    ((TStructure.t.truncGEδLT (q + 1)).app X)
    (TStructure.t.triangleLTGE_distinguished (q + 1) X)

/-- **An injective object represents cohomology in the derived category.** For `E` an injective
object of an abelian category `𝒜`, `q : ℤ` and `X` an arbitrary object of the unbounded derived
category `D(𝒜)`, taking cohomology in degree `q` is an isomorphism of abelian groups
`Hom_{D(𝒜)}(X, E[q]) ≅ Hom_𝒜(H^q(X), E)`. Naturality in `X` is
`DerivedCategory.homologyToSingleAddEquiv_comp`. -/
def homologyToSingleAddEquiv [Injective E] :
    (X ⟶ (singleFunctor C q).obj E) ≃+ ((homologyFunctor C q).obj X ⟶ E) :=
  AddEquiv.ofBijective (homologyToSingle X E q) (bijective_homologyToSingle_of_injective ..)

/-- `DerivedCategory.homologyToSingleAddEquiv` is `DerivedCategory.homologyToSingle`. -/
@[simp]
lemma homologyToSingleAddEquiv_apply [Injective E] (f : X ⟶ (singleFunctor C q).obj E) :
    homologyToSingleAddEquiv X E q f =
      (homologyFunctor C q).map f ≫ (singleFunctorCompHomologyFunctorIso C q).hom.app E :=
  rfl

/-- The isomorphism `Hom_{D(𝒜)}(-, E[q]) ≅ Hom_𝒜(H^q(-), E)` of
`DerivedCategory.homologyToSingleAddEquiv` is natural in its variable. -/
lemma homologyToSingleAddEquiv_comp [Injective E] {X' : DerivedCategory C} (g : X' ⟶ X)
    (f : X ⟶ (singleFunctor C q).obj E) :
    homologyToSingleAddEquiv X' E q (g ≫ f) =
      (homologyFunctor C q).map g ≫ homologyToSingleAddEquiv X E q f :=
  homologyToSingle_comp X E q g f

/-! ### The `R`-linear form of the identification

When `𝒜` is `R`-linear, all the Hom-groups above are `R`-modules and the identification is
`R`-linear. -/

section Linear

variable (R : Type*) [Ring R] [Linear R C]

/-- `DerivedCategory.homologyToSingle` as an `R`-linear map, when `𝒜` is `R`-linear. -/
def homologyToSingleLinearMap :
    (X ⟶ (singleFunctor C q).obj E) →ₗ[R] ((homologyFunctor C q).obj X ⟶ E) where
  toFun := homologyToSingle X E q
  map_add' := (homologyToSingle X E q).map_add
  map_smul' r f := by
    have : Functor.Linear R (homologyFunctor C q) := homologyFunctor_linear R q
    simp only [homologyToSingle_apply, Functor.map_smul, Linear.smul_comp, RingHom.id_apply]

/-- **An injective object represents cohomology, `R`-linearly.** For `𝒜` an `R`-linear abelian
category, `E` an injective object of `𝒜`, `q : ℤ` and `X` an arbitrary object of the unbounded
derived category `D(𝒜)`, taking cohomology in degree `q` is an isomorphism of `R`-modules
`Hom_{D(𝒜)}(X, E[q]) ≅ Hom_𝒜(H^q(X), E)`. Naturality in `X` is
`DerivedCategory.homologyToSingleLinearEquiv_comp`. -/
def homologyToSingleLinearEquiv [Injective E] :
    (X ⟶ (singleFunctor C q).obj E) ≃ₗ[R] ((homologyFunctor C q).obj X ⟶ E) :=
  LinearEquiv.ofBijective (homologyToSingleLinearMap X E q R)
    (bijective_homologyToSingle_of_injective X E q)

/-- `DerivedCategory.homologyToSingleLinearEquiv` is `DerivedCategory.homologyToSingle`. -/
@[simp]
lemma homologyToSingleLinearEquiv_apply [Injective E] (f : X ⟶ (singleFunctor C q).obj E) :
    homologyToSingleLinearEquiv X E q R f =
      (homologyFunctor C q).map f ≫ (singleFunctorCompHomologyFunctorIso C q).hom.app E :=
  rfl

/-- The isomorphism `Hom_{D(𝒜)}(-, E[q]) ≅ Hom_𝒜(H^q(-), E)` of
`DerivedCategory.homologyToSingleLinearEquiv` is natural in its variable. -/
lemma homologyToSingleLinearEquiv_comp [Injective E] {X' : DerivedCategory C} (g : X' ⟶ X)
    (f : X ⟶ (singleFunctor C q).obj E) :
    homologyToSingleLinearEquiv X' E q R (g ≫ f) =
      (homologyFunctor C q).map g ≫ homologyToSingleLinearEquiv X E q R f :=
  homologyToSingle_comp X E q g f

end Linear

end DerivedCategory
