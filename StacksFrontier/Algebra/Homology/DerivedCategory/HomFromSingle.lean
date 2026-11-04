module

public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLEGT
public import StacksFrontier.CategoryTheory.Triangulated.OperationsOnFullSubcategories

/-!
# Morphisms out of an object of degree zero

Let `C` be an abelian category, `A` an object of `C` and `E` an object of `D(C)`. Morphisms
`A[0] ⟶ E` in `D(C)` and morphisms `A ⟶ H⁰(E)` in `C` are compared by `H⁰`. That comparison is
bijective once `A[0]` has no nonzero morphisms into the objects of degrees `≤ -1` built from `E`
by truncation and shift. Taking `A` to be the structure sheaf on a site with a final object gives
morphisms `𝒪[0] ⟶ E` as global sections of `H⁰(E)`.

## Main results

* `CategoryTheory.Pretriangulated.Triangle.bijective_comp_mor₂`,
  `CategoryTheory.Pretriangulated.Triangle.bijective_comp_mor₁`: postcomposition with a map of a
  distinguished triangle is bijective on morphisms from a test object which has no nonzero
  morphisms into the two adjacent vertices.
* `DerivedCategory.bijective_homologyFunctor_map_singleFunctor`: the comparison by `H⁰` is
  bijective, for `E` in a class of objects stable under truncation and shift and on whose members
  of degrees `≤ -1` the object `A[0]` admits only zero morphisms.
-/

@[expose] public section

open CategoryTheory Limits Pretriangulated

universe w v u

namespace CategoryTheory.Pretriangulated

/-- Postcomposition with `g` is injective once it is injective on morphisms killed by `g`. -/
private lemma injective_comp_of_eq_zero {D : Type u} [Category.{v} D] [Preadditive D] {X Y Z : D}
    (g : Y ⟶ Z) (h : ∀ f : X ⟶ Y, f ≫ g = 0 → f = 0) :
    Function.Injective (fun f : X ⟶ Y => f ≫ g) := fun f₁ f₂ hf =>
  sub_eq_zero.1 (h _ (by rw [Preadditive.sub_comp]; exact sub_eq_zero.2 hf))

variable {D : Type u} [Category.{v} D] [Preadditive D] [HasZeroObject D] [HasShift D ℤ]
  [∀ n : ℤ, (CategoryTheory.shiftFunctor D n).Additive] [Pretriangulated D]

/-- Postcomposition with the second map of a distinguished triangle is bijective on morphisms
from `X` once `X` has only zero morphisms into the first vertex and into its shift. -/
lemma Triangle.bijective_comp_mor₂ (T : Triangle D) (hT : T ∈ distTriang D) (X : D)
    (h₁ : ∀ f : X ⟶ T.obj₁, f = 0)
    (h₂ : ∀ f : X ⟶ T.obj₁⟦(1 : ℤ)⟧, f = 0) :
    Function.Bijective (fun f : X ⟶ T.obj₂ => f ≫ T.mor₂) := by
  refine ⟨injective_comp_of_eq_zero _ fun f hf => ?_, fun g => ?_⟩
  · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T hT f hf
    exact hg.trans ((congrArg (· ≫ T.mor₁) (h₁ g)).trans zero_comp)
  · obtain ⟨f, hf⟩ := Triangle.coyoneda_exact₃ T hT g (h₂ _)
    exact ⟨f, hf.symm⟩

/-- Postcomposition with the first map of a distinguished triangle is bijective on morphisms
from `X` once `X` has only zero morphisms into the third vertex and into its shift by `-1`. -/
lemma Triangle.bijective_comp_mor₁ (T : Triangle D) (hT : T ∈ distTriang D) (X : D)
    (h₃ : ∀ f : X ⟶ T.obj₃, f = 0)
    (h₃' : ∀ f : X ⟶ T.obj₃⟦(-1 : ℤ)⟧, f = 0) :
    Function.Bijective (fun f : X ⟶ T.obj₁ => f ≫ T.mor₁) := by
  refine ⟨injective_comp_of_eq_zero _ fun f hf => ?_, fun g => ?_⟩
  · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₂ T.invRotate (inv_rot_of_distTriang T hT) f hf
    exact hg.trans ((congrArg (· ≫ T.invRotate.mor₁) (h₃' g)).trans zero_comp)
  · obtain ⟨f, hf⟩ := Triangle.coyoneda_exact₂ T hT g (h₃ _)
    exact ⟨f, hf.symm⟩

end CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

open TStructure

/-- `H⁰` is bijective on morphisms between objects of degree zero. -/
lemma bijective_homologyFunctor_map_of_isGE_of_isLE (A : C) (H : DerivedCategory C)
    [H.IsGE 0] [H.IsLE 0] :
    Function.Bijective (fun z : (singleFunctor C 0).obj A ⟶ H => (homologyFunctor C 0).map z) := by
  obtain ⟨B, ⟨e⟩⟩ := H.exists_iso_singleFunctor_obj_of_isGE_of_isLE 0
  let φ := singleFunctorCompHomologyFunctorIso C 0
  let ff := Functor.FullyFaithful.ofFullyFaithful (singleFunctor C 0)
  have key : (fun z : (singleFunctor C 0).obj A ⟶ H => (homologyFunctor C 0).map z) =
      (fun g : A ⟶ B => φ.hom.app A ≫ g ≫ φ.inv.app B ≫ (homologyFunctor C 0).map e.inv) ∘
        ff.preimage ∘ (fun z => z ≫ e.hom) := by
    funext z
    simp only [Function.comp_apply]
    have hn := φ.hom.naturality (ff.preimage (z ≫ e.hom))
    simp only [Functor.comp_map, Functor.id_map, ff.map_preimage] at hn
    rw [← Category.assoc, ← hn, Category.assoc, φ.hom_inv_id_app_assoc,
      ← Functor.map_comp, Category.assoc, e.hom_inv_id, Category.comp_id]
  rw [key]
  refine Function.Bijective.comp ?_ (Function.Bijective.comp ff.homEquiv.symm.bijective ?_)
  · refine ⟨fun g₁ g₂ hg => ?_, fun y => ⟨φ.inv.app A ≫ y ≫ (homologyFunctor C 0).map e.hom ≫
      φ.hom.app B, ?_⟩⟩
    · have := congrArg (fun k => φ.inv.app A ≫ k ≫ (homologyFunctor C 0).map e.hom ≫
        φ.hom.app B) hg
      simpa [← Functor.map_comp] using this
    · simp [← Functor.map_comp]
  · exact ⟨fun z₁ z₂ h => by simpa using congrArg (· ≫ e.inv) h,
      fun y => ⟨y ≫ e.inv, by simp⟩⟩

/-- **Morphisms out of an object of degree zero.** Let `P` be a class of objects of `D(C)` stable
under the truncations `τ_{≤ n}`, `τ_{≥ n}` and the shift, and suppose `A[0]` admits only zero
morphisms into the members of `P` concentrated in degrees `≤ -1`. Then for `E` in `P`, the
comparison `(A[0] ⟶ E) → (H⁰(A[0]) ⟶ H⁰(E))` given by `H⁰` is bijective. -/
theorem bijective_homologyFunctor_map_singleFunctor (A : C) (P : ObjectProperty (DerivedCategory C))
    (hPle : ∀ (X : DerivedCategory C) (n : ℤ), P X → P ((t.truncLE n).obj X))
    (hPshift : ∀ (X : DerivedCategory C), P X → P (X⟦(1 : ℤ)⟧))
    (hP : ∀ (X : DerivedCategory C), P X → X.IsLE (-1) →
      ∀ f : (singleFunctor C 0).obj A ⟶ X, f = 0)
    (E : DerivedCategory C) (hE : P E) :
    Function.Bijective (fun x : (singleFunctor C 0).obj A ⟶ E => (homologyFunctor C 0).map x) := by
  set S := (singleFunctor C 0).obj A
  set E₀ := (t.truncLE 0).obj E
  set ι₀ := (t.truncLEι 0).app E
  set H := (t.truncGE 0).obj E₀
  set π := (t.truncGEπ 0).app E₀
  -- Step 1: morphisms into `E` are morphisms into `τ_{≤ 0} E`.
  have h1 : Function.Bijective (fun y : S ⟶ E₀ => y ≫ ι₀) :=
    Triangle.bijective_comp_mor₁ _ (t.triangleLEGE_distinguished 0 1 rfl E) S
      (fun f => t.zero_of_isLE_of_isGE f 0 1 (by omega) inferInstance
        (inferInstanceAs (t.IsGE ((t.truncGE 1).obj E) 1))) (fun f => by
        have : ((t.truncGE 1).obj E⟦(-1 : ℤ)⟧).IsGE 2 :=
          t.isGE_shift ((t.truncGE 1).obj E) 1 (-1) 2
        exact t.zero_of_isLE_of_isGE f 0 2 (by omega) inferInstance this)
  -- Step 2: morphisms into `τ_{≤ 0} E` are morphisms into `τ_{≥ 0} τ_{≤ 0} E`.
  have hPE₀ : P E₀ := hPle E 0 hE
  have hP₁ : P ((t.truncLE (-1)).obj E₀) := hPle E₀ (-1) hPE₀
  have h2 : Function.Bijective (fun y : S ⟶ E₀ => y ≫ π) :=
    Triangle.bijective_comp_mor₂ _ (t.triangleLEGE_distinguished (-1) 0 (by omega) E₀) S
      (fun f => hP _ hP₁ inferInstance f)
      (fun f => by
        have : (((t.truncLE (-1)).obj E₀)⟦(1 : ℤ)⟧).IsLE (-2) :=
          t.isLE_shift ((t.truncLE (-1)).obj E₀) (-1) 1 (-2) (by omega)
        exact hP _ (hPshift _ hP₁) (t.isLE_of_le _ (-2) (-1) (by omega)) f)
  -- Step 3: `H⁰` is bijective on morphisms into the object `H` of degree zero.
  have h3 := bijective_homologyFunctor_map_of_isGE_of_isLE A H
  have hι : IsIso ((homologyFunctor C 0).map ι₀) :=
    isIso_homologyFunctor_map_truncLTι (0 + 1) 0 (by omega) E
  have hπ : IsIso ((homologyFunctor C 0).map π) :=
    isIso_homologyFunctor_map_truncGEπ 0 0 le_rfl E₀
  have key : (fun x : S ⟶ E => (homologyFunctor C 0).map x) ∘ (fun y : S ⟶ E₀ => y ≫ ι₀) =
      (fun g => g ≫ inv ((homologyFunctor C 0).map π) ≫ (homologyFunctor C 0).map ι₀) ∘
        (fun z : S ⟶ H => (homologyFunctor C 0).map z) ∘ (fun y : S ⟶ E₀ => y ≫ π) := by
    funext y
    simp
  have hrhs : Function.Bijective
      ((fun g => g ≫ inv ((homologyFunctor C 0).map π) ≫ (homologyFunctor C 0).map ι₀) ∘
        (fun z : S ⟶ H => (homologyFunctor C 0).map z) ∘ (fun y : S ⟶ E₀ => y ≫ π)) := by
    refine Function.Bijective.comp ?_ (h3.comp h2)
    refine ⟨fun g₁ g₂ hg => by simpa [cancel_mono] using hg,
      fun y => ⟨y ≫ inv ((homologyFunctor C 0).map ι₀) ≫ (homologyFunctor C 0).map π, by simp⟩⟩
  rw [← key] at hrhs
  exact (Function.Bijective.of_comp_iff _ h1).1 hrhs

end DerivedCategory

end
