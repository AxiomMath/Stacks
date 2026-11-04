module

public import Mathlib.Algebra.Homology.DerivedCategory.ExactFunctor
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.Algebra.Homology.DerivedCategory.TStructure
public import Mathlib.Algebra.Homology.Factorizations.CM5a
public import Mathlib.CategoryTheory.Preadditive.Injective.Preserves
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Exact fully faithful functors preserving injectives on morphisms into `D⁺`

Let `F : A ⥤ B` be an exact, fully faithful functor between abelian categories which carries
injective objects to injective objects, `A` having enough injectives.  Then the induced functor
`D(A) ⥤ D(B)` is bijective on morphisms `K ⟶ L` as soon as `L` is cohomologically bounded below.

Indeed `L` is represented by a bounded below complex `I` of injectives, which is K-injective, so
morphisms into `L` in `D(A)` are morphisms into `I` up to homotopy; `F` carries `I` to a bounded
below complex of injectives, again K-injective, so morphisms into `F(L)` in `D(B)` are morphisms
into `F(I)` up to homotopy; and `F`, being fully faithful and additive, is bijective on morphisms
up to homotopy.

## Main results

* `CategoryTheory.Functor.mapDerivedCategory_map_bijective_of_isKInjective`: the bijectivity into
  the image of a complex `I` which is K-injective and whose image is K-injective.
* `CategoryTheory.Functor.mapDerivedCategory_map_bijective_of_isGE`: the bijectivity into an
  object cohomologically bounded below.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits DerivedCategory

namespace CategoryTheory.Functor

universe w₁ w₂ v₁ v₂ u₁ u₂

variable {A : Type u₁} [Category.{v₁} A] [Abelian A] {B : Type u₂} [Category.{v₂} B] [Abelian B]
  [HasDerivedCategory.{w₁} A] [HasDerivedCategory.{w₂} B]
  (F : A ⥤ B) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- Bijectivity of a functor on morphisms transfers along isomorphisms of the source and the
target. -/
theorem map_bijective_of_iso_of_iso {C D : Type*} [Category* C] [Category* D] (G : C ⥤ D)
    {K L K' L' : C} (eK : K ≅ K') (eL : L ≅ L')
    (h : Function.Bijective (G.map : (K' ⟶ L') → (G.obj K' ⟶ G.obj L'))) :
    Function.Bijective (G.map : (K ⟶ L) → (G.obj K ⟶ G.obj L)) := by
  have hcomm : (G.map : (K ⟶ L) → (G.obj K ⟶ G.obj L)) =
      ((G.mapIso eK).homCongr (G.mapIso eL)).symm ∘ G.map ∘ (eK.homCongr eL) := by
    funext f
    simp [Iso.homCongr_apply]
  rw [hcomm]
  exact ((G.mapIso eK).homCongr (G.mapIso eL)).symm.bijective.comp
    (h.comp (eK.homCongr eL).bijective)

/-- **`D(F)` is bijective on morphisms into a K-injective complex with K-injective image**, for
`F` exact and fully faithful. -/
theorem mapDerivedCategory_map_bijective_of_isKInjective [F.Full] [F.Faithful]
    (X : HomotopyCategory A (ComplexShape.up ℤ)) (I : CochainComplex A ℤ)
    [CochainComplex.IsKInjective I]
    [CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)] :
    Function.Bijective (F.mapDerivedCategory.map :
      (Qh.obj X ⟶ Qh.obj ((HomotopyCategory.quotient _ _).obj I)) → _) := by
  let e := F.mapDerivedCategoryFactorsh
  have hQh' := CochainComplex.IsKInjective.Qh_map_bijective
    ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj X)
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)
  let c := (e.app X).homCongr (e.app ((HomotopyCategory.quotient _ _).obj I))
  have hcomm : (F.mapDerivedCategory.map :
      (Qh.obj X ⟶ Qh.obj ((HomotopyCategory.quotient _ _).obj I)) → _) ∘ Qh.map =
      c.symm ∘ (Qh.map ∘ (F.mapHomotopyCategory (ComplexShape.up ℤ)).map) := by
    funext φ
    have hn := e.hom.naturality φ
    simp only [Functor.comp_map] at hn
    simp only [Function.comp_apply, c, Iso.homCongr_symm, Iso.homCongr_apply, Iso.symm_inv,
      Iso.symm_hom, Iso.app_hom, Iso.app_inv]
    rw [← Category.assoc, ← hn, Category.assoc, Iso.hom_inv_id_app, Category.comp_id]
  have hcomp : Function.Bijective ((F.mapDerivedCategory.map :
      (Qh.obj X ⟶ Qh.obj ((HomotopyCategory.quotient _ _).obj I)) → _) ∘ Qh.map) := by
    rw [hcomm]
    exact c.symm.bijective.comp
      (hQh'.comp ⟨(F.mapHomotopyCategory (ComplexShape.up ℤ)).map_injective,
        (F.mapHomotopyCategory (ComplexShape.up ℤ)).map_surjective⟩)
  exact (Function.Bijective.of_comp_iff _
    (CochainComplex.IsKInjective.Qh_map_bijective X I)).1 hcomp

/-- **`D(F)` is bijective on morphisms into an object cohomologically bounded below**, for `F`
exact, fully faithful and preserving injective objects, `A` having enough injectives. -/
@[sga "4 V 2.5.1" "more general"]
theorem mapDerivedCategory_map_bijective_of_isGE [EnoughInjectives A] [F.Full] [F.Faithful]
    [F.PreservesInjectiveObjects] (K L : DerivedCategory A) (n : ℤ) [L.IsGE n] :
    Function.Bijective (F.mapDerivedCategory.map : (K ⟶ L) → _) := by
  obtain ⟨L₀, _, ⟨eL₀⟩⟩ := L.exists_iso_Q_obj_of_isGE n
  obtain ⟨I, i, _, hI, _⟩ :=
    CochainComplex.Plus.modelCategoryQuillen.exists_quasiIso_injective (K := L₀) n
  have : ∀ m, Injective (I.X m) := hI
  have : CochainComplex.IsKInjective I := CochainComplex.isKInjective_of_injective I n
  have : ∀ m, Injective (((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I).X m) :=
    fun m => F.injective_obj (I.X m)
  have : CochainComplex.IsKInjective ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) :=
    CochainComplex.isKInjective_of_injective _ n
  have eL : L ≅ Qh.obj ((HomotopyCategory.quotient _ _).obj I) :=
    eL₀ ≪≫ asIso (Q.map i) ≪≫ ((quotientCompQhIso A).app I).symm
  exact map_bijective_of_iso_of_iso F.mapDerivedCategory (Qh.objObjPreimageIso K).symm eL
    (mapDerivedCategory_map_bijective_of_isKInjective F _ I)

end CategoryTheory.Functor
