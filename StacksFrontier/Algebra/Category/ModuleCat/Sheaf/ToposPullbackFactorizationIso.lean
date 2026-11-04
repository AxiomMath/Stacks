module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackFactorizationSheaf

/-! # The sheaf of factorizations of the inverse images is the inverse image of the sheaf of
factorizations

Let `Φ : Sh(D) ⥤ Sh(C)` be a left exact functor between categories of sheaves of sets — the
inverse image of a morphism of topoi, in the application — let `R` be a sheaf of rings on `(D, K)`
and `M` a sheaf of `R`-modules.
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPullbackFactorizationSheaf.lean` builds the
comparison

`factorizationSheafComparison : Φ(Fact_l(R, M, n)) ⟶ Fact_l(Φ R, Φ M, n)`

with no hypothesis on `Φ` beyond preservation of finite products, because the matrix condition is
a polynomial identity between generalized elements. This file proves that for a left exact `Φ`
the comparison is an **isomorphism**, which is the statement
`Stacks.Sheaves.ToposPullback.isIso_relationSheafComparison` already records for the sheaf of
relations.

The reason is the same as there: the sheaf of rank-`l` factorizations is the equalizer of the
matrix condition and of zero on the ambient product `Rⁿ ⨯ (Mˡ ⨯ (Rⁿ)ˡ)`, the ambient product is a
finite product, and a left exact functor preserves both.

## Main results

* `Stacks.Sheaves.ToposPullback.factorizationEqualizerIso`: the sheaf of factorizations of the
  inverse images is the equalizer of the inverse images of the matrix condition and of zero.
* `Stacks.Sheaves.ToposPullback.isIso_factorizationSheafComparison`: **the comparison morphism is
  an isomorphism.**
* `Stacks.Sheaves.ToposPullback.factorizationSheafIsoPullback`: that isomorphism, named.

## Implementation notes

The two equalizer lifts, their compatibilities with the inclusion into the ambient product, and
the assembly into an isomorphism follow
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/ToposPullbackRelationSheaf.lean` step for step; the
only difference is that the second leg of the equalizer is the explicit zero morphism
`factorizationZero` of that development rather than `0`, since `Sheaf J (Type w)` has no zero
morphisms.

That the comparison is the equalizer comparison followed by the second of those lifts is
proved by the universal property, both sides being determined by their composite with the
inclusion of the sheaf of factorizations into its ambient product.

## References

* [Stacks Project, Tag 08FC](https://stacks.math.columbia.edu/tag/08FC)
* [Stacks Project, Tag 05VD](https://stacks.math.columbia.edu/tag/05VD)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf
open Stacks.Sheaves.RelationSheaf

universe ww ww' vv uu vv' uu'

namespace Stacks.Sheaves.ToposPullback

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteLimits Φ]
  (R : Sheaf K RingCat.{ww'}) (M : SheafOfModules.{ww'} R) (n l : ℕ)

/-- Read through the comparison of the ambient products, the equalizer of the inverse images of
the matrix condition and of zero satisfies the matrix condition of the inverse images. -/
lemma equalizerι_comp_hom_comp_factorizationContract :
    (equalizer.ι (Φ.map (factorizationContract R M n l))
          (Φ.map (factorizationZero R M n l)) ≫
        (factorizationAmbientComparison J Φ R M n l).hom) ≫
      factorizationContract (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l =
    (equalizer.ι (Φ.map (factorizationContract R M n l))
          (Φ.map (factorizationZero R M n l)) ≫
        (factorizationAmbientComparison J Φ R M n l).hom) ≫
      factorizationZero (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l := by
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  erw [factorizationAmbientComparison_hom_comp_factorizationContract,
    factorizationAmbientComparison_hom_comp_factorizationZero, ← Category.assoc,
    ← Category.assoc, equalizer.condition]

/-- Transporting a commutation relation along an isomorphism: `e.hom ≫ f = g ≫ h.hom` gives
`e.inv ≫ g = f ≫ h.inv`. -/
private theorem inv_comp_eq_comp_inv_of_hom_comp_eq {𝒞 : Type*} [Category 𝒞] {X Y Z W : 𝒞}
    (e : X ≅ Y) (h : W ≅ Z) {f : Y ⟶ Z} {g : X ⟶ W} (H : e.hom ≫ f = g ≫ h.hom) :
    e.inv ≫ g = f ≫ h.inv := by
  rw [Iso.eq_comp_inv, Category.assoc, ← H, Iso.inv_hom_id_assoc]

/-- The comparison of the ambient products carries the matrix condition of the inverse images
to the inverse image of the matrix condition. -/
lemma inv_comp_map_factorizationContract :
    (factorizationAmbientComparison J Φ R M n l).inv ≫
        Φ.map (factorizationContract R M n l) =
      factorizationContract (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l ≫
        (PreservesProduct.iso Φ (fun _ : Fin l => ringSheaf R)).inv :=
  inv_comp_eq_comp_inv_of_hom_comp_eq _ _
    (factorizationAmbientComparison_hom_comp_factorizationContract J Φ R M n l)

/-- The counterpart of `Stacks.Sheaves.ToposPullback.inv_comp_map_factorizationContract` for the
zero morphism into `Rˡ`. -/
lemma inv_comp_map_factorizationZero :
    (factorizationAmbientComparison J Φ R M n l).inv ≫
        Φ.map (factorizationZero R M n l) =
      factorizationZero (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l ≫
        (PreservesProduct.iso Φ (fun _ : Fin l => ringSheaf R)).inv :=
  inv_comp_eq_comp_inv_of_hom_comp_eq _ _
    (factorizationAmbientComparison_hom_comp_factorizationZero J Φ R M n l)

/-- Read through the comparison of the ambient products, the sheaf of factorizations of the
inverse images equalizes the inverse images of the matrix condition and of zero. -/
lemma factorizationIota_comp_inv_comp_map_factorizationContract :
    (factorizationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l ≫
        (factorizationAmbientComparison J Φ R M n l).inv) ≫
      Φ.map (factorizationContract R M n l) =
    (factorizationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l ≫
        (factorizationAmbientComparison J Φ R M n l).inv) ≫
      Φ.map (factorizationZero R M n l) := by
  refine (Category.assoc _ _ _).trans (Eq.trans ?_ (Category.assoc _ _ _).symm)
  refine (congrArg _ (inv_comp_map_factorizationContract J Φ R M n l)).trans ?_
  refine Eq.trans ?_ (congrArg _ (inv_comp_map_factorizationZero J Φ R M n l).symm)
  exact (Category.assoc _ _ _).symm.trans
    ((congrArg (· ≫ _) (factorizationIota_comp_factorizationContract _ _ n l)).trans
      (Category.assoc _ _ _))

/-- The morphism from the equalizer of the inverse images to the sheaf of factorizations of the
inverse images. -/
def factorizationEqualizerInv :
    equalizer (Φ.map (factorizationContract R M n l)) (Φ.map (factorizationZero R M n l)) ⟶
      factorizationSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l :=
  equalizer.lift
    (equalizer.ι (Φ.map (factorizationContract R M n l))
        (Φ.map (factorizationZero R M n l)) ≫
      (factorizationAmbientComparison J Φ R M n l).hom)
    (equalizerι_comp_hom_comp_factorizationContract J Φ R M n l)

/-- The morphism from the sheaf of factorizations of the inverse images to the equalizer of the
inverse images. -/
def factorizationEqualizerHom :
    factorizationSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l ⟶
      equalizer (Φ.map (factorizationContract R M n l)) (Φ.map (factorizationZero R M n l)) :=
  equalizer.lift
    (factorizationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l ≫
      (factorizationAmbientComparison J Φ R M n l).inv)
    (factorizationIota_comp_inv_comp_map_factorizationContract J Φ R M n l)

/-- `factorizationEqualizerInv` followed by the inclusion into the ambient product. -/
lemma factorizationEqualizerInv_comp_factorizationIota :
    factorizationEqualizerInv J Φ R M n l ≫
        factorizationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l =
      equalizer.ι (Φ.map (factorizationContract R M n l))
          (Φ.map (factorizationZero R M n l)) ≫
        (factorizationAmbientComparison J Φ R M n l).hom :=
  equalizer.lift_ι _ _

/-- `factorizationEqualizerHom` followed by the inclusion into the ambient product. -/
lemma factorizationEqualizerHom_comp_ι :
    factorizationEqualizerHom J Φ R M n l ≫
        equalizer.ι (Φ.map (factorizationContract R M n l))
          (Φ.map (factorizationZero R M n l)) =
      factorizationIota (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l ≫
        (factorizationAmbientComparison J Φ R M n l).inv :=
  equalizer.lift_ι _ _

/-- **The sheaf of rank-`l` factorizations of the inverse images is the equalizer of the inverse
images of the matrix condition and of zero.** -/
def factorizationEqualizerIso :
    factorizationSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l ≅
      equalizer (Φ.map (factorizationContract R M n l))
        (Φ.map (factorizationZero R M n l)) where
  hom := factorizationEqualizerHom J Φ R M n l
  inv := factorizationEqualizerInv J Φ R M n l
  hom_inv_id := by
    refine equalizer.hom_ext ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (fun m => factorizationEqualizerHom J Φ R M n l ≫ m)
      (factorizationEqualizerInv_comp_factorizationIota J Φ R M n l)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg
      (fun m => m ≫ (factorizationAmbientComparison J Φ R M n l).hom)
      (factorizationEqualizerHom_comp_ι J Φ R M n l)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun m => factorizationIota (pullbackRingSheaf J Φ R)
        (pullbackModuleObj J Φ R M) n l ≫ m)
      (factorizationAmbientComparison J Φ R M n l).inv_hom_id) ?_
    exact (Category.comp_id _).trans (Category.id_comp _).symm
  inv_hom_id := by
    refine equalizer.hom_ext ?_
    refine (Category.assoc _ _ _).trans ?_
    refine Eq.trans (congrArg (fun m => factorizationEqualizerInv J Φ R M n l ≫ m)
      (factorizationEqualizerHom_comp_ι J Φ R M n l)) ?_
    refine Eq.trans (Category.assoc _ _ _).symm ?_
    refine Eq.trans (congrArg
      (fun m => m ≫ (factorizationAmbientComparison J Φ R M n l).inv)
      (factorizationEqualizerInv_comp_factorizationIota J Φ R M n l)) ?_
    refine Eq.trans (Category.assoc _ _ _) ?_
    refine Eq.trans (congrArg (fun m => equalizer.ι (Φ.map (factorizationContract R M n l))
        (Φ.map (factorizationZero R M n l)) ≫ m)
      (factorizationAmbientComparison J Φ R M n l).hom_inv_id) ?_
    exact (Category.comp_id _).trans (Category.id_comp _).symm

/-- The comparison morphism is the equalizer comparison of `Φ` followed by the identification of
the equalizer of the inverse images with the sheaf of factorizations of the inverse images: both
sides are determined by their composite with the inclusion into the ambient product. -/
lemma factorizationSheafComparison_eq :
    factorizationSheafComparison J Φ R M n l =
      equalizerComparison (factorizationContract R M n l) (factorizationZero R M n l) Φ ≫
        factorizationEqualizerInv J Φ R M n l := by
  refine equalizer.hom_ext ?_
  refine (factorizationSheafComparison_comp_factorizationIota J Φ R M n l).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  erw [factorizationEqualizerInv_comp_factorizationIota,
    ← Category.assoc (equalizerComparison _ _ _), equalizerComparison_comp_π]
  rfl

/-- **The comparison morphism is an isomorphism.** A factorization of a relation among sections
of the inverse-image module is not merely the image of a factorization downstairs: the sheaf of
factorizations of the inverse images *is* the inverse image of the sheaf of factorizations. -/
instance isIso_factorizationSheafComparison :
    IsIso (factorizationSheafComparison J Φ R M n l) := by
  rw [factorizationSheafComparison_eq]
  have hcomparison : IsIso (equalizerComparison (factorizationContract R M n l)
      (factorizationZero R M n l) Φ) := by
    rw [← PreservesEqualizer.iso_hom]
    infer_instance
  have hinv : IsIso (factorizationEqualizerInv J Φ R M n l) :=
    (factorizationEqualizerIso J Φ R M n l).isIso_inv
  exact IsIso.comp_isIso' hcomparison hinv

/-- The sheaf of rank-`l` factorizations of the inverse images, as an isomorphism from the
inverse image of the sheaf of rank-`l` factorizations. -/
def factorizationSheafIsoPullback :
    Φ.obj (factorizationSheaf R M n l) ≅
      factorizationSheaf (pullbackRingSheaf J Φ R) (pullbackModuleObj J Φ R M) n l :=
  asIso (factorizationSheafComparison J Φ R M n l)

end Stacks.Sheaves.ToposPullback

end
