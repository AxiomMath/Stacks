module

public import Mathlib.CategoryTheory.Monoidal.Cartesian.Mod

/-!
# Transporting a module object along a monoidal functor

A monoidal functor `F` carries a monoid object `M` of `C` to a monoid object of `D`, and a
module object over `M` to a module object over the image.  The image monoid structure is not
assumed to be the transported one: it is supplied as data together with the two equations
identifying its unit and multiplication with the images of those of `M`.  This is what makes
the construction usable when the image monoid structure arises from some other source, as it
does for a group scheme pulled back along a morphism of base schemes.

## Main definitions

* `CategoryTheory.Functor.LaxMonoidal.modObj` is the transported module structure on `F.obj X`
  over a prescribed monoid structure on `F.obj M`.

## Main results

* `CategoryTheory.Functor.LaxMonoidal.mapModObj_leftSMul` computes the action morphism
  `(m, x) ↦ (m • x, x)` of the transported structure in a cartesian monoidal category: it is
  the image of the corresponding morphism for `X`, conjugated by the product comparisons.  This
  is the form in which a pseudo-torsor property transports.
-/

@[expose] public section

open CategoryTheory CartesianMonoidalCategory MonoidalCategory MonObj

universe v w

namespace CategoryTheory.Functor.LaxMonoidal

/-- The module structure on `F.obj X` over a monoid structure `M'` on `F.obj M` obtained from a
module structure on `X` over `M`, given that the unit and multiplication of `M'` are the images
of those of `M` under the lax monoidal structure of `F`.  The action is the image of the action
of `M` on `X`, precomposed with the lax monoidal comparison. -/
@[instance_reducible]
def modObj {C D : Type*} [Category.{v} C] [MonoidalCategory C]
    [Category.{w} D] [MonoidalCategory D] (F : C ⥤ D) [F.Monoidal]
    {M X : C} [MonObj M] [ModObj M X] (M' : MonObj (F.obj M))
    (hone : Functor.LaxMonoidal.ε F ≫ F.map η[M] = M'.one)
    (hmul : Functor.LaxMonoidal.μ F M M ≫ F.map μ[M] = M'.mul) :
    @ModObj D _ _ D _ _ (F.obj M) M' (F.obj X) where
  smul := Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X]
  one_smul := by
    rw [← hone]
    change (Functor.LaxMonoidal.ε F ≫ F.map η[M]) ▷ F.obj X ≫
      Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X] = _
    calc
      _ = Functor.LaxMonoidal.ε F ▷ F.obj X ≫
          Functor.LaxMonoidal.μ F (𝟙_ C) X ≫
            F.map ((η[M] ▷ X) ≫ γ[M, X]) := by
        simp only [MonoidalCategory.comp_whiskerRight, Category.assoc,
          Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp]
      _ = Functor.LaxMonoidal.ε F ▷ F.obj X ≫
          Functor.LaxMonoidal.μ F (𝟙_ C) X ≫ F.map (λ_ X).hom := by
        congr 4
        exact ModObj.one_smul (M := M) X
      _ = _ := by simp
  mul_smul := by
    rw [← hmul]
    change (Functor.LaxMonoidal.μ F M M ≫ F.map μ[M]) ▷ F.obj X ≫
      Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X] = _
    calc
      _ = Functor.LaxMonoidal.μ F M M ▷ F.obj X ≫
          Functor.LaxMonoidal.μ F (M ⊗ M) X ≫
            F.map ((μ[M] ▷ X) ≫ γ[M, X]) := by
        simp only [MonoidalCategory.comp_whiskerRight, Category.assoc,
          Functor.LaxMonoidal.μ_natural_left_assoc, ← F.map_comp]
      _ = Functor.LaxMonoidal.μ F M M ▷ F.obj X ≫
          Functor.LaxMonoidal.μ F (M ⊗ M) X ≫
            F.map ((α_ M M X).hom ≫ M ◁ γ[M, X] ≫ γ[M, X]) := by
        rw [show (μ[M] ▷ X) ≫ γ[M, X] =
          (α_ M M X).hom ≫ M ◁ γ[M, X] ≫ γ[M, X] from by
            simp]
      _ = (α_ (F.obj M) (F.obj M) (F.obj X)).hom ≫
          F.obj M ◁ (Functor.LaxMonoidal.μ F M X) ≫
            Functor.LaxMonoidal.μ F M (M ⊗ X) ≫ F.map (M ◁ γ[M, X]) ≫
              F.map γ[M, X] := by
        simp only [Functor.map_comp, Functor.LaxMonoidal.associativity_assoc]
      _ = (α_ (F.obj M) (F.obj M) (F.obj X)).hom ≫
          F.obj M ◁ (Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X]) ≫
            Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X] := by
        simp only [Category.assoc, ← Functor.LaxMonoidal.μ_natural_right_assoc,
          MonoidalCategory.whiskerLeft_comp]

/-- In a cartesian monoidal category the action morphism of the transported module structure is
the image of the action morphism of `X`, read through the product comparison isomorphisms. -/
lemma mapModObj_leftSMul {C D : Type*} [Category.{v} C] [CartesianMonoidalCategory C]
    [Category.{w} D] [CartesianMonoidalCategory D]
    (F : C ⥤ D) [F.Monoidal] [Limits.PreservesFiniteProducts F]
    {M X : C} [MonObj M] [ModObj M X] (M' : MonObj (F.obj M))
    (hone : Functor.LaxMonoidal.ε F ≫ F.map η[M] = M'.one)
    (hmul : Functor.LaxMonoidal.μ F M M ≫ F.map μ[M] = M'.mul) :
    letI : MonObj (F.obj M) := M'
    letI : ModObj (F.obj M) (F.obj X) := modObj F M' hone hmul
    ModObj.leftSMul (F.obj M) (F.obj X) =
      (prodComparisonIso F M X).inv ≫
        F.map (ModObj.leftSMul M X) ≫
          (prodComparisonIso F X X).hom := by
  let _ : MonObj (F.obj M) := M'
  let _ : ModObj (F.obj M) (F.obj X) := modObj F M' hone hmul
  have hμ : Functor.LaxMonoidal.μ F M X = (prodComparisonIso F M X).inv :=
    Functor.Monoidal.μ_of_cartesianMonoidalCategory F M X
  apply CartesianMonoidalCategory.hom_ext
  · rw [ModObj.leftSMul_fst]
    show (modObj F M' hone hmul).smul = _
    show (Functor.LaxMonoidal.μ F M X ≫ F.map γ[M, X]) = _
    rw [hμ]
    simp only [Category.assoc, prodComparisonIso_hom,
      CartesianMonoidalCategory.prodComparison_fst, ModObj.leftSMul_fst,
      ← Functor.map_comp]
  · rw [ModObj.leftSMul_snd]
    simp only [prodComparisonIso_hom, CartesianMonoidalCategory.prodComparison_snd,
      Category.assoc]
    rw [← Functor.map_comp, ModObj.leftSMul_snd]
    rw [← hμ]
    exact (Functor.Monoidal.μ_snd F M X).symm

end CategoryTheory.Functor.LaxMonoidal

end
