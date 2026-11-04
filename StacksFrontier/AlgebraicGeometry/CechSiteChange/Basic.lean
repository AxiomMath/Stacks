module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Cech

/-!
# Čech complexes under a change of site

`CategoryTheory.cechComplexFunctor U : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` is attached to a family
`U : ι → C` of objects of a category with finite products.  This file proves that the complex
depends on the pair `(C, U)` only through the finite products of the members of the family:

* an isomorphism of families gives an isomorphism of Čech complex functors
  (`cechComplexFunctorIsoOfFamilyIso`);
* a functor `Φ : C ⥤ D` preserving finite products identifies the Čech complex of the image
  family `Φ ∘ U` with coefficients in a presheaf `P` on `D` and the Čech complex of `U` with
  coefficients in the restricted presheaf `Φ.op ⋙ P` (`cechComplexFunctorSiteIso`).

Both are isomorphisms of *functors* of the coefficient presheaf.

## Main definitions

* `Stacks.CechSiteChange.formalCoproductMap`: the functor
  `FormalCoproduct C ⥤ FormalCoproduct D` induced by a functor `Φ : C ⥤ D`.
* `Stacks.CechSiteChange.powerMapIso`: for `Φ` preserving `α`-indexed products, the
  identification of `((formalCoproductMap Φ).obj Z).power α` with
  `(formalCoproductMap Φ).obj (Z.power α)` — the only place where products are compared.
* `Stacks.CechSiteChange.cechFormalCoproductMapIso`: the same identification as an isomorphism of
  simplicial objects, `((formalCoproductMap Φ).obj Z).cech ≅ Z.cech ⋙ formalCoproductMap Φ`.
* `Stacks.CechSiteChange.cechComplexFunctorSiteIso`: **the change-of-site isomorphism.**
* `Stacks.CechSiteChange.cechComplexFunctorIsoOfFamilyIso`: **invariance under an isomorphism of
  families.**

## Implementation notes

The construction factors entirely through Mathlib's own tower

`cechComplexFunctor U = cochainComplexFunctor (FormalCoproduct.mk _ U).cech`,
`cochainComplexFunctor E = evalOp _ _ ⋙ (whiskeringLeft _ _ _).obj E.rightOp ⋙
  alternatingCofaceMapComplex _`,

so that the only mathematical input is a comparison of *simplicial objects in
`FormalCoproduct D`*, and everything above it is whiskering.  In particular no naturality square
in the coefficient presheaf is ever proved by hand: the isomorphism of Čech complex functors is
obtained from the isomorphism of simplicial objects by `Functor.mapIso` and
`Functor.isoWhiskerLeft`/`isoWhiskerRight` alone.

Two compatibilities hold on the nose and are recorded as equalities rather than isomorphisms,
which is what keeps the construction free of `eqToHom`:

* `evalOp_formalCoproductMap`: evaluating a presheaf on `D` at the formal coproducts of `C`
  obtained by applying `Φ` *is* evaluating `Φ.op ⋙ P` at the formal coproducts of `C`.  Both
  sides are the product, over the same index type, of the values of `P` at `Φ` of the
  components.
* `Functor.rightOpComp` (in Mathlib, an `Iso.refl`): `(E ⋙ G).rightOp = E.rightOp ⋙ G.op`.

The comparison of products is `CategoryTheory.Limits.PreservesProduct.iso`, and its naturality in
the index map — the one genuine computation — is `Limits.piComparison_comp_π` on each coordinate,
after `Limits.Pi.hom_ext`.

## References

* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w t v v' v'' u u' u''

namespace Stacks.CechSiteChange

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]

/-! ### Functoriality of formal coproducts -/

/-- The functor on formal coproducts induced by a functor of the underlying categories: it keeps
the index type and applies `Φ` to every component. -/
@[simps]
def formalCoproductMap (Φ : C ⥤ D) :
    FormalCoproduct.{w} C ⥤ FormalCoproduct.{w} D where
  obj Z := { I := Z.I, obj i := Φ.obj (Z.obj i) }
  map f := { f := f.f, φ i := Φ.map (f.φ i) }
  map_id _ := FormalCoproduct.hom_ext rfl (fun i ↦ by simp)
  map_comp _ _ := FormalCoproduct.hom_ext rfl (fun i ↦ by simp)

/-- The `Functor.rightOp` of an isomorphism of functors. -/
@[simps]
def rightOpIso {E E' : Cᵒᵖ ⥤ D} (e : E ≅ E') : E.rightOp ≅ E'.rightOp where
  hom := e.inv.rightOp
  inv := e.hom.rightOp
  hom_inv_id := by ext n; exact congrArg Quiver.Hom.op (e.hom_inv_id_app (op n))
  inv_hom_id := by ext n; exact congrArg Quiver.Hom.op (e.inv_hom_id_app (op n))

variable {A : Type u''} [Category.{v''} A]

/-- **Evaluating a presheaf on `D` at the image formal coproducts is evaluating the restricted
presheaf.**  Both sides send `Z : FormalCoproduct C` to the product, over `Z.I`, of the values of
`P` at `Φ` of the components of `Z`, and send a morphism to the same lift of projections. -/
theorem evalOp_formalCoproductMap [HasProducts.{w} A] (Φ : C ⥤ D) (P : Dᵒᵖ ⥤ A) :
    (formalCoproductMap.{w} Φ).op ⋙ (FormalCoproduct.evalOp.{w} D A).obj P =
      (FormalCoproduct.evalOp.{w} C A).obj (Φ.op ⋙ P) :=
  rfl

/-- `evalOp_formalCoproductMap` with the presheaf as a variable: restricting along `Φ.op` and
then evaluating at the formal coproducts of `C` is evaluating at the formal coproducts of `D` and
then restricting along `formalCoproductMap Φ`. -/
theorem whiskeringLeft_op_comp_evalOp [HasProducts.{w} A] (Φ : C ⥤ D) :
    (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj Φ.op ⋙ FormalCoproduct.evalOp.{w} C A =
      FormalCoproduct.evalOp.{w} D A ⋙
        (Functor.whiskeringLeft (FormalCoproduct.{w} C)ᵒᵖ (FormalCoproduct.{w} D)ᵒᵖ A).obj
          (formalCoproductMap.{w} Φ).op :=
  rfl

/-! ### The comparison of powers -/

section Power

/-- **The product comparison is natural in the index map.**  This is the one genuine computation
of the file: both sides are determined by their projections, and on the projection indexed by
`a : α` both are `Φ.map (Pi.π _ (g a))`. -/
theorem piComparison_naturality {α β : Type} (Φ : C ⥤ D) (V : β → C) (g : α → β)
    [HasProduct V] [HasProduct (fun b ↦ Φ.obj (V b))] [HasProduct (fun a ↦ V (g a))]
    [HasProduct (fun a ↦ Φ.obj (V (g a)))] :
    piComparison Φ V ≫ Pi.lift (fun a ↦ Pi.π (fun b ↦ Φ.obj (V b)) (g a)) =
      Φ.map (Pi.lift (fun a ↦ Pi.π V (g a))) ≫ piComparison Φ (fun a ↦ V (g a)) := by
  refine Pi.hom_ext _ _ (fun a ↦ ?_)
  rw [Category.assoc, Pi.lift_π, piComparison_comp_π, Category.assoc, piComparison_comp_π,
    ← Φ.map_comp, Pi.lift_π]

variable [HasFiniteProducts C] [HasFiniteProducts D] (Φ : C ⥤ D) [PreservesFiniteProducts Φ]
  (Z : FormalCoproduct.{w} C)

/-- **The comparison of the Čech powers.**  For a functor preserving finite products, the image of
the `α`-indexed power of a formal coproduct is the `α`-indexed power of its image: both are
indexed by the maps `α → Z.I`, and at such a map the comparison is the product comparison for
`Φ`. -/
noncomputable def powerMapIso (α : Type) [Finite α] :
    (formalCoproductMap.{w} Φ).obj (Z.power α) ≅
      ((formalCoproductMap.{w} Φ).obj Z).power α :=
  FormalCoproduct.isoOfComponents (Equiv.refl _)
    (fun x ↦ PreservesProduct.iso Φ (Z.obj ∘ x))

/-- The coordinates of `powerMapIso` are the product comparisons. -/
theorem powerMapIso_hom_φ (α : Type) [Finite α] (x : (Z.power α).I) :
    (powerMapIso.{w} Φ Z α).hom.φ x = piComparison Φ (Z.obj ∘ x) :=
  rfl

/-- The comparison of powers is compatible with reindexing along a map of index types, which is
what makes it a morphism of simplicial objects. -/
theorem mapPower_powerMapIso {α β : Type} [Finite α] [Finite β] (g : α → β) :
    (formalCoproductMap.{w} Φ).map (Z.mapPower g) ≫ (powerMapIso.{w} Φ Z α).hom =
      (powerMapIso.{w} Φ Z β).hom ≫ ((formalCoproductMap.{w} Φ).obj Z).mapPower g :=
  FormalCoproduct.hom_ext rfl (fun x ↦ (Category.comp_id _).trans
    (piComparison_naturality Φ (fun b ↦ Z.obj (x b)) g).symm)

/-- **The comparison of Čech objects.**  The Čech simplicial object of the image formal coproduct
is the image of the Čech simplicial object: degreewise this is `powerMapIso`, and the simplicial
structure maps are reindexings, handled by `mapPower_powerMapIso`. -/
noncomputable def cechFormalCoproductMapIso :
    ((formalCoproductMap.{w} Φ).obj Z).cech ≅ Z.cech ⋙ formalCoproductMap.{w} Φ :=
  (NatIso.ofComponents (fun n ↦ powerMapIso.{w} Φ Z (ToType n.unop))
    (fun {n m : SimplexCategoryᵒᵖ} (f : n ⟶ m) ↦
      mapPower_powerMapIso.{w} Φ Z (SimplexCategory.Hom.toOrderHom f.unop).toFun)).symm

end Power

/-! ### The change of site -/

section Site

variable [HasProducts.{w} A] [Preadditive A] [HasFiniteProducts C]

/-- Transport of the cosimplicial object attached to a presheaf along an isomorphism of
simplicial objects in the category of formal coproducts: pure whiskering. -/
noncomputable def cosimplicialObjectFunctorIsoOfIso
    {E E' : SimplicialObject (FormalCoproduct.{w} C)} (e : E ≅ E') :
    FormalCoproduct.cosimplicialObjectFunctor.{w} (A := A) E ≅
      FormalCoproduct.cosimplicialObjectFunctor.{w} (A := A) E' :=
  Functor.isoWhiskerLeft (FormalCoproduct.evalOp.{w} C A)
    ((Functor.whiskeringLeft SimplexCategory (FormalCoproduct.{w} C)ᵒᵖ A).mapIso (rightOpIso e))

/-- Transport of the Čech cochain complex functor along an isomorphism of simplicial objects in
the category of formal coproducts.  Everything above the simplicial object is whiskering, so this
needs no computation. -/
noncomputable def cochainComplexFunctorIsoOfIso
    {E E' : SimplicialObject (FormalCoproduct.{w} C)} (e : E ≅ E') :
    FormalCoproduct.cochainComplexFunctor.{w} (A := A) E ≅
      FormalCoproduct.cochainComplexFunctor.{w} (A := A) E' :=
  Functor.isoWhiskerRight (cosimplicialObjectFunctorIsoOfIso (A := A) e)
    (AlgebraicTopology.alternatingCofaceMapComplex A)

/-- **The Čech complex of an isomorphic family is isomorphic.**  The Čech complex functor depends
on the family only through the formal coproduct of its members, and `FormalCoproduct.cechFunctor`
is a functor. -/
noncomputable def cechComplexFunctorIsoOfFamilyIso {ι : Type w}
    {U U' : ι → C} (e : ∀ i, U i ≅ U' i) :
    cechComplexFunctor (A := A) U ≅ cechComplexFunctor (A := A) U' :=
  cochainComplexFunctorIsoOfIso
    (FormalCoproduct.cechFunctor.mapIso
      (FormalCoproduct.isoOfComponents (Equiv.refl ι) e))

variable [HasFiniteProducts D] (Φ : C ⥤ D) [PreservesFiniteProducts Φ]

/-- **The change-of-site isomorphism for Čech complexes.**  For a functor `Φ : C ⥤ D` preserving
finite products and a family `U : ι → C`, the Čech complex of the image family `Φ ∘ U` with
coefficients in a presheaf on `D` is the Čech complex of `U` with coefficients in the restriction
of that presheaf along `Φ`, naturally in the presheaf. -/
noncomputable def cechComplexFunctorSiteIso {ι : Type w} (U : ι → C) :
    cechComplexFunctor (A := A) (fun i ↦ Φ.obj (U i)) ≅
      (Functor.whiskeringLeft Cᵒᵖ Dᵒᵖ A).obj Φ.op ⋙ cechComplexFunctor (A := A) U :=
  cochainComplexFunctorIsoOfIso (cechFormalCoproductMapIso.{w} Φ { I := ι, obj := U })

end Site

end Stacks.CechSiteChange
