module

public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Products
public import StacksCore.Tactic.StacksAttribute

/-!
# A coproduct of left adjoints is left adjoint to the product of the right adjoints

Let `L i : C ⥤ D` and `R i : D ⥤ C` be families of functors indexed by `i : I`, with
`L i ⊣ R i` for every `i`. If `F : C ⥤ D` is a coproduct of the `L i` and `G : D ⥤ C` is a
product of the `R i`, then `F ⊣ G`. Indeed
`Mor(F X, Y) = ∏ᵢ Mor(L i X, Y) = ∏ᵢ Mor(X, R i Y) = Mor(X, G Y)`,
the outer two identifications because coproducts and products in a functor category are
computed pointwise.

This is the formal half of the direct-sum formulas of Stacks 09WG (3) and (6): there the
left adjoint `g_{n!}` of restriction to a simplicial component, followed by restriction to
another component, is a coproduct of the inverse images of the simplicial transitions, and
the identification is proved by comparing the right adjoints, which form a product of the
direct images.

## Main definitions

* `CategoryTheory.Adjunction.ofCofanFan`: the adjunction, from a cofan exhibiting `F X` as
  the coproduct of the `L i X` and a fan exhibiting `G Y` as the product of the `R i Y`,
  whose legs are the components of natural transformations `L i ⟶ F` and `G ⟶ R i`.
* `CategoryTheory.Adjunction.sigmaPi`: its instance at `F = ∐ L` and `G = ∏ᶜ R`.
* `CategoryTheory.Limits.coproductObjIso`, `CategoryTheory.Limits.productObjIso`: a
  coproduct (product) of functors, evaluated at an object, is the coproduct (product) of
  the values, with `coproductObjIsColimit` and `productObjIsLimit` the corresponding
  universal properties in `Cofan`/`Fan` form.

## Implementation notes

`ofCofanFan` takes the two universal properties as hypotheses rather than deriving them,
because that is the form in which they arise: in a concrete identification one has a
specific functor `F` together with maps `L i ⟶ F`, not a chosen colimit. `sigmaPi` is the
specialization to Mathlib's chosen coproduct and product, which is what a statement written
with `∐` and `∏ᶜ` needs; the evaluation isomorphisms it rests on are `coproductObjIso` and
`productObjIso`, stated separately since they are independently useful.

The index type `I` lives in its own universe and the only size hypotheses are
`HasColimitsOfShape (Discrete I) D` and `HasLimitsOfShape (Discrete I) C`, which also supply
the coproduct of `L` in `C ⥤ D` and the product of `R` in `D ⥤ C`.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe w v₁ v₂ u₁ u₂

namespace CategoryTheory.Limits

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {I : Type w}

section Coproduct

variable (L : I → (C ⥤ D)) [HasColimitsOfShape (Discrete I) D]

/-- A coproduct of functors, evaluated at an object, is the coproduct of the values. -/
public noncomputable def coproductObjIso (X : C) :
    (∐ L).obj X ≅ ∐ fun i => (L i).obj X :=
  colimitObjIsoColimitCompEvaluation (Discrete.functor L) X ≪≫
    HasColimit.isoOfNatIso (Discrete.compNatIsoDiscrete L ((evaluation C D).obj X))

/-- The `i`-th coproduct inclusion of the values, followed by the inverse of `coproductObjIso L X`,
is the component at `X` of the `i`-th coproduct inclusion of `∐ L`. -/
@[simp]
public theorem Sigma.ι_comp_coproductObjIso_inv (X : C) (i : I) :
    Sigma.ι (fun i => (L i).obj X) i ≫ (coproductObjIso L X).inv =
      (Sigma.ι L i).app X := by
  simp only [coproductObjIso, Iso.trans_inv, HasColimit.ι_isoOfNatIso_inv_assoc]
  simp [colimitObjIsoColimitCompEvaluation_ι_inv (Discrete.functor L) ⟨i⟩ X]

/-- The cofan on the values of a family of functors at an object, with legs the components
of the coproduct inclusions, is a colimit. -/
public noncomputable def coproductObjIsColimit (X : C) :
    IsColimit (Cofan.mk ((∐ L).obj X) fun i => (Sigma.ι L i).app X) :=
  IsColimit.ofIsoColimit (coproductIsCoproduct fun i => (L i).obj X)
    (Cocone.ext (coproductObjIso L X).symm (by rintro ⟨i⟩; simp))

end Coproduct

section Product

variable (R : I → (D ⥤ C)) [HasLimitsOfShape (Discrete I) C]

/-- A product of functors, evaluated at an object, is the product of the values. -/
public noncomputable def productObjIso (Y : D) :
    (∏ᶜ R).obj Y ≅ ∏ᶜ fun i => (R i).obj Y :=
  limitObjIsoLimitCompEvaluation (Discrete.functor R) Y ≪≫
    HasLimit.isoOfNatIso (Discrete.compNatIsoDiscrete R ((evaluation D C).obj Y))

/-- `productObjIso R Y` followed by the `i`-th product projection of the values is the component
at `Y` of the `i`-th product projection of `∏ᶜ R`. -/
public theorem productObjIso_hom_comp_Pi_π (Y : D) (i : I) :
    (productObjIso R Y).hom ≫ Pi.π (fun i => (R i).obj Y) i = (Pi.π R i).app Y := by
  simp only [productObjIso, Iso.trans_hom, Category.assoc, HasLimit.isoOfNatIso_hom_π]
  simp [limitObjIsoLimitCompEvaluation_hom_π (Discrete.functor R) ⟨i⟩ Y]

/-- The inverse of `productObjIso R Y` followed by the component at `Y` of the `i`-th product
projection of `∏ᶜ R` is the `i`-th product projection of the values. -/
@[simp]
public theorem productObjIso_inv_comp_Pi_π_app (Y : D) (i : I) :
    (productObjIso R Y).inv ≫ (Pi.π R i).app Y = Pi.π (fun i => (R i).obj Y) i := by
  rw [Iso.inv_comp_eq]
  exact (productObjIso_hom_comp_Pi_π R Y i).symm

/-- The fan on the values of a family of functors at an object, with legs the components of
the product projections, is a limit. -/
public noncomputable def productObjIsLimit (Y : D) :
    IsLimit (Fan.mk ((∏ᶜ R).obj Y) fun i => (Pi.π R i).app Y) :=
  IsLimit.ofIsoLimit (productIsProduct fun i => (R i).obj Y)
    (Cone.ext (productObjIso R Y).symm (by rintro ⟨i⟩; simp))

end Product

end CategoryTheory.Limits

namespace CategoryTheory.Adjunction

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D] {I : Type w}
  {L : I → (C ⥤ D)} {R : I → (D ⥤ C)} {F : C ⥤ D} {G : D ⥤ C}
  {ι : ∀ i, L i ⟶ F} {π : ∀ i, G ⟶ R i}

private theorem app_comp_desc
    (hF : ∀ X : C, IsColimit (Cofan.mk (F.obj X) fun i => (ι i).app X))
    (X : C) {A : D} (f : ∀ i, (L i).obj X ⟶ A) (i : I) :
    (ι i).app X ≫ Cofan.IsColimit.desc (hF X) f = f i :=
  Cofan.IsColimit.fac (hF X) f i

private theorem lift_comp_app
    (hG : ∀ Y : D, IsLimit (Fan.mk (G.obj Y) fun i => (π i).app Y))
    (Y : D) {A : C} (f : ∀ i, A ⟶ (R i).obj Y) (i : I) :
    Fan.IsLimit.lift (hG Y) f ≫ (π i).app Y = f i :=
  Fan.IsLimit.fac (hG Y) f i

/-- A coproduct of left adjoints is left adjoint to the product of the right adjoints.

The coproduct and the product are given pointwise, by universal properties whose legs are
the components of natural transformations `ι i : L i ⟶ F` and `π i : G ⟶ R i`. -/
public def ofCofanFan (adj : ∀ i, L i ⊣ R i)
    (ι : ∀ i, L i ⟶ F) (π : ∀ i, G ⟶ R i)
    (hF : ∀ X : C, IsColimit (Cofan.mk (F.obj X) fun i => (ι i).app X))
    (hG : ∀ Y : D, IsLimit (Fan.mk (G.obj Y) fun i => (π i).app Y)) :
    F ⊣ G :=
  Adjunction.mkOfHomEquiv
    { homEquiv := fun X Y =>
        { toFun := fun f =>
            Fan.IsLimit.lift (hG Y) fun i => (adj i).homEquiv X Y ((ι i).app X ≫ f)
          invFun := fun g =>
            Cofan.IsColimit.desc (hF X) fun i =>
              ((adj i).homEquiv X Y).symm (g ≫ (π i).app Y)
          left_inv := fun f => by
            refine Cofan.IsColimit.hom_ext (hF X) _ _ fun i => ?_
            simp only [cofan_mk_inj]
            rw [app_comp_desc hF, lift_comp_app hG]
            simp
          right_inv := fun g => by
            refine Fan.IsLimit.hom_ext (hG Y) _ _ fun i => ?_
            simp only [fan_mk_proj]
            rw [lift_comp_app hG, app_comp_desc hF]
            simp }
      homEquiv_naturality_left_symm := fun {X' X Y} f g => by
        refine Cofan.IsColimit.hom_ext (hF X') _ _ fun i => ?_
        simp only [cofan_mk_inj, Equiv.coe_fn_symm_mk]
        conv_lhs => rw [app_comp_desc hF, Category.assoc]
        conv_rhs => rw [← Category.assoc, ← (ι i).naturality f, Category.assoc,
          app_comp_desc hF]
        exact (adj i).homEquiv_naturality_left_symm f (g ≫ (π i).app Y)
      homEquiv_naturality_right := fun {X Y Y'} f g => by
        refine Fan.IsLimit.hom_ext (hG Y') _ _ fun i => ?_
        simp only [fan_mk_proj, Equiv.coe_fn_mk]
        conv_rhs => rw [Category.assoc, (π i).naturality, ← Category.assoc,
          lift_comp_app hG]
        conv_lhs => rw [lift_comp_app hG, ← Category.assoc]
        exact (adj i).homEquiv_naturality_right ((ι i).app X ≫ f) g }

/-- A coproduct of left adjoints is left adjoint to the product of the right adjoints, for
Mathlib's chosen coproduct `∐ L` and product `∏ᶜ R`. -/
public noncomputable def sigmaPi (adj : ∀ i, L i ⊣ R i)
    [HasColimitsOfShape (Discrete I) D] [HasLimitsOfShape (Discrete I) C] :
    (∐ L) ⊣ (∏ᶜ R) :=
  ofCofanFan adj (Sigma.ι L) (Pi.π R) (coproductObjIsColimit L) (productObjIsLimit R)

end CategoryTheory.Adjunction

end
