module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import Mathlib.Algebra.Homology.DerivedCategory.Linear
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear
public import Mathlib.CategoryTheory.Triangulated.TStructure.TruncLTGE
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic

/-!
# A projective object corepresents cohomology in the derived category

Let `𝒜` be an abelian category, `P` a projective object of `𝒜` and `q : ℤ`. Writing `P[q]` for
the image of `P` under `𝒜 ⥤ D(𝒜)`, the complex concentrated in degree `q`, this file proves that
taking cohomology in degree `q` is a bijection
`Hom_{D(𝒜)}(P[q], Y) ≅ Hom_𝒜(P, H^q(Y))`
for an **arbitrary** object `Y` of the unbounded derived category: no boundedness and no
`IsGE q` hypothesis. In other words `P[q]` corepresents the functor `H^q` on all of `D(𝒜)`.

## Main results

* `DerivedCategory.from_singleFunctor_obj_eq_zero_of_isLE_of_projective` — for `P` projective,
  every morphism `P[q] ⟶ Y` with `Y` in degrees `≤ n < q` is zero.
* `DerivedCategory.homologyFromSingle` — the comparison map
  `Hom_{D(𝒜)}(P[q], Y) →+ Hom_𝒜(P, H^q(Y))`, defined for every `P` and every `Y`, natural
  in `Y` (`DerivedCategory.homologyFromSingle_comp`).
* `DerivedCategory.bijective_homologyFromSingle_of_isGE` — it is bijective when `Y.IsGE q`,
  with no hypothesis on `P`.
* `DerivedCategory.bijective_homologyFromSingle_of_projective` — it is bijective for `P`
  projective and `Y` arbitrary.
* `DerivedCategory.homologyFromSingleAddEquiv` — the resulting additive isomorphism
  `Hom_{D(𝒜)}(P[q], Y) ≃+ Hom_𝒜(P, H^q(Y))`.
* `DerivedCategory.homologyFromSingleLinearEquiv` — the same isomorphism as a map of
  `R`-modules when `𝒜` is `R`-linear.
* `DerivedCategory.homologyFunctor_linear` — the cohomology functors of `D(𝒜)` are `R`-linear
  when `𝒜` is.

## References

* [Stacks Project, Tag 06XS](https://stacks.math.columbia.edu/tag/06XS)
-/

@[expose] public noncomputable section

open CategoryTheory Category Limits Pretriangulated Triangulated

universe w v u

namespace DerivedCategory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]

/-- If `P` is projective and `Y` is an object of `D(𝒜)` concentrated in degrees `≤ n` with
`n < q`, then every morphism `P[q] ⟶ Y` vanishes. -/
theorem from_singleFunctor_obj_eq_zero_of_isLE_of_projective {P : C} [Projective P] {q n : ℤ}
    (hn : n < q) (Y : DerivedCategory C) [Y.IsLE n]
    (f : (singleFunctor C q).obj P ⟶ Y) : f = 0 := by
  obtain ⟨L, _, ⟨e⟩⟩ := Y.exists_iso_Q_obj_of_isLE n
  have he := (singleFunctorIsoCompQ C q).app P
  rw [← cancel_mono e.hom, ← cancel_epi he.inv, zero_comp, comp_zero]
  exact from_singleFunctor_obj_eq_zero_of_projective (he.inv ≫ f ≫ e.hom) n hn

/-- The cohomology functors of the derived category of an `R`-linear abelian category are
`R`-linear. -/
theorem homologyFunctor_linear (R : Type*) [Ring R] [Linear R C] (q : ℤ) :
    Functor.Linear R (homologyFunctor C q) := by
  have : Functor.Linear R (HomologicalComplex.homologyFunctor C (.up ℤ) q) := by
    refine ⟨fun g r ↦ ?_⟩
    change HomologicalComplex.homologyMap (r • g) q = r • HomologicalComplex.homologyMap g q
    rw [HomologicalComplex.homologyMap, HomologicalComplex.homologyMap,
      show (HomologicalComplex.shortComplexFunctor C (.up ℤ) q).map (r • g) =
        r • (HomologicalComplex.shortComplexFunctor C (.up ℤ) q).map g from by ext <;> rfl]
    exact ShortComplex.homologyMap_smul _ _
  exact (Localization.functor_linear_iff Q (HomologicalComplex.quasiIso C (.up ℤ)) R
    (Q ⋙ homologyFunctor C q) (homologyFunctor C q)).mp
      (Functor.linear_of_iso R (homologyFunctorFactors C q).symm)

variable (P : C) (Y : DerivedCategory C) (q : ℤ)

/-- Taking cohomology in degree `q` of a morphism `P[q] ⟶ Y` in the derived category of an
abelian category `𝒜`, read through the identification `H^q(P[q]) = P`: the comparison map
`Hom_{D(𝒜)}(P[q], Y) ⟶ Hom_𝒜(P, H^q(Y))`. -/
def homologyFromSingle :
    ((singleFunctor C q).obj P ⟶ Y) →+ (P ⟶ (homologyFunctor C q).obj Y) where
  toFun f := (singleFunctorCompHomologyFunctorIso C q).inv.app P ≫ (homologyFunctor C q).map f
  map_zero' := by simp
  map_add' f g := by simp only [Functor.map_add, Preadditive.comp_add]

/-- The comparison map of `DerivedCategory.homologyFromSingle` on a morphism. -/
@[simp]
lemma homologyFromSingle_apply (f : (singleFunctor C q).obj P ⟶ Y) :
    homologyFromSingle P Y q f =
      (singleFunctorCompHomologyFunctorIso C q).inv.app P ≫ (homologyFunctor C q).map f :=
  rfl

/-- The comparison map `Hom_{D(𝒜)}(P[q], -) ⟶ Hom_𝒜(P, H^q(-))` is natural in its second
variable. -/
lemma homologyFromSingle_comp {Y' : DerivedCategory C}
    (f : (singleFunctor C q).obj P ⟶ Y) (g : Y ⟶ Y') :
    homologyFromSingle P Y' q (f ≫ g) =
      homologyFromSingle P Y q f ≫ (homologyFunctor C q).map g := by
  simp

/-- The comparison map of `DerivedCategory.homologyFromSingle` is bijective if and only if taking
cohomology in degree `q` is a bijection on morphisms `P[q] ⟶ Y`. -/
private lemma bijective_homologyFromSingle_iff :
    Function.Bijective (homologyFromSingle P Y q) ↔
      Function.Bijective (fun f : (singleFunctor C q).obj P ⟶ Y ↦ (homologyFunctor C q).map f) := by
  have key : (homologyFromSingle P Y q : _ → _) =
      (fun k : (homologyFunctor C q).obj ((singleFunctor C q).obj P) ⟶
          (homologyFunctor C q).obj Y ↦
        (singleFunctorCompHomologyFunctorIso C q).inv.app P ≫ k) ∘
        (fun f : (singleFunctor C q).obj P ⟶ Y ↦ (homologyFunctor C q).map f) := rfl
  rw [key]
  exact Function.Bijective.of_comp_iff'
    (Iso.homFromEquiv ((singleFunctorCompHomologyFunctorIso C q).app P)).bijective _

/-- For every object `P` of `𝒜` and every object `Y` of `D(𝒜)` concentrated in degrees `≥ q`,
the comparison map `Hom_{D(𝒜)}(P[q], Y) ⟶ Hom_𝒜(P, H^q(Y))` is bijective. -/
theorem bijective_homologyFromSingle_of_isGE [Y.IsGE q] :
    Function.Bijective (homologyFromSingle P Y q) := by
  rw [bijective_homologyFromSingle_iff]
  have key : (fun f : (singleFunctor C q).obj P ⟶ Y ↦ (homologyFunctor C q).map f) =
      (fun g : (singleFunctor C q).obj P ⟶ Y⟦(0 : ℤ)⟧ ↦
        ((homologyFunctor C 0).shiftMap g q q (zero_add q) :
          (homologyFunctor C q).obj ((singleFunctor C q).obj P) ⟶
            (homologyFunctor C q).obj Y)) ∘
        (Iso.homToEquiv ((shiftFunctorZero (DerivedCategory C) ℤ).app Y).symm) := by
    funext f
    dsimp only [Function.comp_apply, Iso.homToEquiv_apply, Iso.symm_hom]
    simp only [Functor.shiftMap, Functor.shiftIso_zero_hom_app, shift_homologyFunctor,
      ← Functor.map_comp, assoc]
    simp
  rw [key]
  exact (bijective_homologyFunctor_shiftMap_of_isLE_of_isGE _ Y q q 0 q (zero_add q)
    le_rfl).comp (Equiv.bijective _)

/-- Let `P` be projective and `Y₁ ⟶ Y ⟶ Y₃ ⟶ Y₁⟦1⟧` a distinguished triangle with `Y₁` in
degrees `≤ q - 1` and `Y₃` in degrees `≥ q`. Then the comparison map
`Hom_{D(𝒜)}(P[q], Y) ⟶ Hom_𝒜(P, H^q(Y))` is bijective. -/
private lemma bijective_homologyFromSingle_of_distTriang [Projective P]
    {Y₁ Y₃ : DerivedCategory C} [Y₁.IsLE (q - 1)] [Y₃.IsGE q]
    (f₁ : Y₁ ⟶ Y) (f₂ : Y ⟶ Y₃) (f₃ : Y₃ ⟶ Y₁⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f₁ f₂ f₃ ∈ distTriang (DerivedCategory C)) :
    Function.Bijective (homologyFromSingle P Y q) := by
  have : TStructure.t.IsLE (Y₁⟦(1 : ℤ)⟧) (q - 2) :=
    TStructure.t.isLE_shift _ (q - 1) 1 (q - 2) (by omega)
  have hcomp : Function.Bijective (fun f : (singleFunctor C q).obj P ⟶ Y ↦ f ≫ f₂) := by
    refine ⟨fun g₁ g₂ hg ↦ ?_, fun h ↦ ?_⟩
    · rw [← sub_eq_zero]
      obtain ⟨g, hg'⟩ := Triangle.coyoneda_exact₂ _ hT (g₁ - g₂)
        (by rw [Preadditive.sub_comp, sub_eq_zero]; exact hg)
      rw [hg', from_singleFunctor_obj_eq_zero_of_isLE_of_projective (n := q - 1) (by omega) Y₁ g,
        zero_comp]
    · obtain ⟨g, hg⟩ := Triangle.coyoneda_exact₃ _ hT h
        (from_singleFunctor_obj_eq_zero_of_isLE_of_projective (n := q - 2) (by omega)
          (Y₁⟦(1 : ℤ)⟧) _)
      exact ⟨g, hg.symm⟩
  have h₀ : IsZero ((homologyFunctor C q).obj Y₁) := isZero_of_isLE _ (q - 1) q (by omega)
  have h₁ : IsZero ((homologyFunctor C (q + 1)).obj Y₁) :=
    isZero_of_isLE _ (q - 1) (q + 1) (by omega)
  have : Mono ((homologyFunctor C q).map f₂) :=
    (HomologySequence.mono_homologyMap_mor₂_iff _ hT q).2 (h₀.eq_of_src _ _)
  have : Epi ((homologyFunctor C q).map f₂) :=
    (HomologySequence.epi_homologyMap_mor₂_iff _ hT q (q + 1) rfl).2 (h₁.eq_of_tgt _ _)
  have : IsIso ((homologyFunctor C q).map f₂) := isIso_of_mono_of_epi _
  have hkey := ((bijective_homologyFromSingle_iff P Y₃ q).1
    (bijective_homologyFromSingle_of_isGE P Y₃ q)).comp hcomp
  rw [bijective_homologyFromSingle_iff]
  refine (Function.Bijective.of_comp_iff'
    (Iso.homToEquiv (asIso ((homologyFunctor C q).map f₂))).bijective _).mp ?_
  convert hkey using 1
  funext f
  simp

/-- A projective object `P` of an abelian category `𝒜` corepresents cohomology in degree `q` on
the whole unbounded derived category: for every object `Y` of `D(𝒜)`, taking cohomology in
degree `q` is a bijection `Hom_{D(𝒜)}(P[q], Y) ⟶ Hom_𝒜(P, H^q(Y))`. -/
theorem bijective_homologyFromSingle_of_projective [Projective P] :
    Function.Bijective (homologyFromSingle P Y q) :=
  bijective_homologyFromSingle_of_distTriang P Y q
    ((TStructure.t.truncLTι q).app Y) ((TStructure.t.truncGEπ q).app Y)
    ((TStructure.t.truncGEδLT q).app Y) (TStructure.t.triangleLTGE_distinguished q Y)

/-- **A projective object corepresents cohomology in the derived category.** For `P` a
projective object of an abelian category `𝒜`, `q : ℤ` and `Y` an arbitrary object of the
unbounded derived category `D(𝒜)`, taking cohomology in degree `q` is an isomorphism of
abelian groups `Hom_{D(𝒜)}(P[q], Y) ≅ Hom_𝒜(P, H^q(Y))`. -/
def homologyFromSingleAddEquiv [Projective P] :
    ((singleFunctor C q).obj P ⟶ Y) ≃+ (P ⟶ (homologyFunctor C q).obj Y) :=
  AddEquiv.ofBijective (homologyFromSingle P Y q) (bijective_homologyFromSingle_of_projective ..)

/-- `DerivedCategory.homologyFromSingleAddEquiv` is `DerivedCategory.homologyFromSingle`. -/
@[simp]
lemma homologyFromSingleAddEquiv_apply [Projective P] (f : (singleFunctor C q).obj P ⟶ Y) :
    homologyFromSingleAddEquiv P Y q f =
      (singleFunctorCompHomologyFunctorIso C q).inv.app P ≫ (homologyFunctor C q).map f :=
  rfl

/-- The isomorphism `Hom_{D(𝒜)}(P[q], -) ≅ Hom_𝒜(P, H^q(-))` of
`DerivedCategory.homologyFromSingleAddEquiv` is natural in its second variable. -/
lemma homologyFromSingleAddEquiv_comp [Projective P] {Y' : DerivedCategory C}
    (f : (singleFunctor C q).obj P ⟶ Y) (g : Y ⟶ Y') :
    homologyFromSingleAddEquiv P Y' q (f ≫ g) =
      homologyFromSingleAddEquiv P Y q f ≫ (homologyFunctor C q).map g :=
  homologyFromSingle_comp P Y q f g

/-! ### The `R`-linear form of the identification

When `𝒜` is `R`-linear, all the Hom-groups above are `R`-modules and the identification is
`R`-linear. -/

section Linear

variable (R : Type*) [Ring R] [Linear R C]

/-- `DerivedCategory.homologyFromSingle` as an `R`-linear map, when `𝒜` is `R`-linear. -/
def homologyFromSingleLinearMap :
    ((singleFunctor C q).obj P ⟶ Y) →ₗ[R] (P ⟶ (homologyFunctor C q).obj Y) where
  toFun := homologyFromSingle P Y q
  map_add' := (homologyFromSingle P Y q).map_add
  map_smul' r f := by
    have : Functor.Linear R (homologyFunctor C q) := homologyFunctor_linear R q
    simp only [homologyFromSingle_apply, Functor.map_smul, Linear.comp_smul, RingHom.id_apply]

/-- **A projective object corepresents cohomology, `R`-linearly.** For `𝒜` an `R`-linear
abelian category, `P` a projective object of `𝒜`, `q : ℤ` and `Y` an arbitrary object of the
unbounded derived category `D(𝒜)`, taking cohomology in degree `q` is an isomorphism of
`R`-modules `Hom_{D(𝒜)}(P[q], Y) ≅ Hom_𝒜(P, H^q(Y))`. -/
def homologyFromSingleLinearEquiv [Projective P] :
    ((singleFunctor C q).obj P ⟶ Y) ≃ₗ[R] (P ⟶ (homologyFunctor C q).obj Y) :=
  LinearEquiv.ofBijective (homologyFromSingleLinearMap P Y q R)
    (bijective_homologyFromSingle_of_projective P Y q)

/-- `DerivedCategory.homologyFromSingleLinearEquiv` is `DerivedCategory.homologyFromSingle`. -/
@[simp]
lemma homologyFromSingleLinearEquiv_apply [Projective P] (f : (singleFunctor C q).obj P ⟶ Y) :
    homologyFromSingleLinearEquiv P Y q R f =
      (singleFunctorCompHomologyFunctorIso C q).inv.app P ≫ (homologyFunctor C q).map f :=
  rfl

/-- The isomorphism `Hom_{D(𝒜)}(P[q], -) ≅ Hom_𝒜(P, H^q(-))` of
`DerivedCategory.homologyFromSingleLinearEquiv` is natural in its second variable. -/
lemma homologyFromSingleLinearEquiv_comp [Projective P] {Y' : DerivedCategory C}
    (f : (singleFunctor C q).obj P ⟶ Y) (g : Y ⟶ Y') :
    homologyFromSingleLinearEquiv P Y' q R (f ≫ g) =
      homologyFromSingleLinearEquiv P Y q R f ≫ (homologyFunctor C q).map g :=
  homologyFromSingle_comp P Y q f g

end Linear

end DerivedCategory
