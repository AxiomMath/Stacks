module

public import Mathlib.Algebra.Category.ModuleCat.AB
public import Mathlib.Algebra.Homology.GrothendieckAbelian
public import Mathlib.Algebra.Homology.DerivedCategory.KInjective
public import Mathlib.CategoryTheory.Localization.LocallySmall
public import Mathlib.CategoryTheory.Quotient.LocallySmall
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.SheafOfModules
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
import StacksCore.Tactic.StacksAttribute

/-!
# Existence of derived categories of Grothendieck abelian categories

Let `C` be a Grothendieck abelian category which is locally small in a universe `w`. Tag 079Q
says that the unbounded derived category of `C` exists with morphism types in `w`, and that
its morphisms are computed by homotopy classes of maps into a K-injective resolution of the
target.

Both statements come from the functorial K-injective resolution of a Grothendieck abelian
category. Fix a complex `L` and let `L → R` be its chosen resolution. Since `R` is
K-injective, the localization functor `DerivedCategory.Qh` out of the homotopy category is
bijective on morphisms into `R`; composing that bijection with the isomorphism
`DerivedCategory.quotientCompQhIso` and with the isomorphism induced by the
quasi-isomorphism `L → R` identifies homotopy classes of maps `K → R` with derived morphisms
`K → L`. Local smallness of the derived category follows: the homotopy category of `C` is
locally small in `w` as a quotient of the category of complexes, every object of the derived
category comes from the homotopy category, and the bijection above exhibits each derived
morphism type as a subquotient of a morphism type of the homotopy category. A localization
whose morphism types are small therefore exists.

## Main definitions

* `Stacks.Injectives.kInjectiveResolutionHomMap`: the canonical map from homotopy classes of
  maps into the chosen K-injective resolution of `L` to derived morphisms into `L`.

## Main results

* `Stacks.Injectives.kInjectiveResolutionHomMap_bijective`: that map is a bijection.
* `Stacks.Injectives.hasDerivedCategory_of_isGrothendieckAbelian`: a Grothendieck abelian
  category which is locally small in `w` has a derived category with morphism types in `w`.

## Implementation notes

The displayed equality of the source is represented here by a canonical bijection, from a
morphism type of the homotopy category to the corresponding morphism type of the derived
category, rather than by an equality of types.

The local-smallness argument is run with the standard model
`HasDerivedCategory.standard C`, whose morphisms live in `max u v`; the conclusion is the
existence of a model with morphisms in `w`, obtained from
`MorphismProperty.hasLocalizationOfLocallySmall`. No such construction is available for a
general abelian category, where the derived category can fail to exist.

Mathlib's Grothendieck-category instances for `ModuleCat` and for `SheafOfModules` give the
two classes of examples of the source; they are registered against this tag below.

## References

* [Stacks Project, Tag 079Q](https://stacks.math.columbia.edu/tag/079Q)
-/

@[expose] public noncomputable section

open CategoryTheory

universe w' w v u

namespace Stacks.Injectives

variable (C : Type u) [Category.{v} C] [Abelian C]

section

variable [IsGrothendieckAbelian.{w} C] [HasDerivedCategory.{w'} C]

/-- The canonical map from homotopy classes of maps into the chosen K-injective resolution of
`L` to derived morphisms from `K` to `L`: compose in the homotopy category, pass to the
derived category, and invert the quasi-isomorphism from `L` to
`(kInjectiveResolutionFunctor C).obj L`. -/
def kInjectiveResolutionHomMap (K L : CochainComplex C ℤ) :
    ((HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj K ⟶
        (HomotopyCategory.quotient C (ComplexShape.up ℤ)).obj
          ((kInjectiveResolutionFunctor C).obj L)) →
      (DerivedCategory.Q.obj K ⟶ DerivedCategory.Q.obj L) :=
  fun f ↦
    (DerivedCategory.quotientCompQhIso C).inv.app K ≫
      DerivedCategory.Qh.map f ≫
      (DerivedCategory.quotientCompQhIso C).hom.app
        ((kInjectiveResolutionFunctor C).obj L) ≫
      inv (DerivedCategory.Q.map ((kInjectiveResolutionInclusion C).app L))

/-- Derived morphisms into a complex `L` are computed by homotopy classes of maps into the
chosen K-injective resolution of `L`. -/
@[stacks 079Q "morphisms via a K-injective resolution"]
theorem kInjectiveResolutionHomMap_bijective (K L : CochainComplex C ℤ) :
    Function.Bijective (kInjectiveResolutionHomMap C K L) := by
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let qh := DerivedCategory.Qh (C := C)
  let R := (kInjectiveResolutionFunctor C).obj L
  let η := (kInjectiveResolutionInclusion C).app L
  let i := DerivedCategory.quotientCompQhIso C
  let e := asIso (DerivedCategory.Q.map η)
  have hEq : kInjectiveResolutionHomMap C K L =
      (fun f : q.obj K ⟶ q.obj R =>
        Iso.homCongr (Iso.refl _) e.symm
          (Iso.homCongr (i.app K) (i.app R) (qh.map f))) := by
    funext f
    simp [kInjectiveResolutionHomMap, Iso.homCongr_apply, i, e, qh, R, η, Category.assoc]
  rw [hEq]
  exact (Iso.homCongr _ _).bijective.comp <| (Iso.homCongr (i.app K) (i.app R)).bijective.comp
    (CochainComplex.IsKInjective.Qh_map_bijective (q.obj K) R)

end

/-- A Grothendieck abelian category which is locally small in the universe `w` admits a
derived category whose morphism types lie in `w`. -/
@[stacks 079Q "existence of the derived category", instance_reducible]
noncomputable def hasDerivedCategory_of_isGrothendieckAbelian
    [inst_groth : IsGrothendieckAbelian.{w} C] :
    HasDerivedCategory.{w} C := by
  let : HasDerivedCategory.{max u v} C := HasDerivedCategory.standard C
  let q := HomotopyCategory.quotient C (ComplexShape.up ℤ)
  let qh := DerivedCategory.Qh (C := C)
  let : LocallySmall.{w} (HomotopyCategory C (ComplexShape.up ℤ)) :=
    CategoryTheory.Quotient.instLocallySmall (homotopic C (ComplexShape.up ℤ))
  let : qh.EssSurj :=
    Localization.essSurj qh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))
  let : LocallySmall.{w, max u v, max u v} (DerivedCategory C) := by
    refine ⟨fun X Y => ?_⟩
    obtain ⟨A, ⟨eA⟩⟩ := Functor.EssSurj.mem_essImage qh X
    obtain ⟨B, ⟨eB⟩⟩ := Functor.EssSurj.mem_essImage qh Y
    obtain ⟨L, rfl⟩ := HomotopyCategory.quotient_obj_surjective B
    let R := (kInjectiveResolutionFunctor C).obj L
    let η := (kInjectiveResolutionInclusion C).app L
    let i := DerivedCategory.quotientCompQhIso C
    let eη : qh.obj (q.obj L) ≅ qh.obj (q.obj R) :=
      i.app L ≪≫ asIso (DerivedCategory.Q.map η) ≪≫ (i.app R).symm
    let eY : qh.obj (q.obj R) ≅ Y := eη.symm ≪≫ eB
    let hbij := CochainComplex.IsKInjective.Qh_map_bijective A R
    let preimage (f : X ⟶ Y) : A ⟶ q.obj R :=
      Classical.choose (hbij.surjective (eA.hom ≫ f ≫ eY.inv))
    have preimage_spec (f : X ⟶ Y) :
        qh.map (preimage f) = eA.hom ≫ f ≫ eY.inv :=
      Classical.choose_spec (hbij.surjective (eA.hom ≫ f ≫ eY.inv))
    refine small_of_injective (f := preimage) fun f g hfg => ?_
    apply (Iso.homCongr eA.symm eY.symm).injective
    simpa only [Iso.homCongr_apply, Iso.symm_inv, Iso.symm_hom] using
      (preimage_spec f).symm.trans ((congrArg qh.map hfg).trans (preimage_spec g))
  exact MorphismProperty.hasLocalizationOfLocallySmall
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) DerivedCategory.Q

add_to_stacks 079Q "modules over a ring" instIsGrothendieckAbelianModuleCat
add_to_stacks 079Q "sheaves of modules on a ringed site"
  SheafOfModules.instIsGrothendieckAbelian
add_to_sga "3 I 3.2.1" "special case" SheafOfModules.instIsGrothendieckAbelian
add_to_sga "4 II 6.7" "special case" SheafOfModules.instIsGrothendieckAbelian
add_to_sga "6 I 1.3" "partial" SheafOfModules.instIsGrothendieckAbelian

end Stacks.Injectives
