module

public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesOverSpace
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedStackUnconditional
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicSpaceStackPresentation
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.SchemeStack
public import StacksFrontier.AlgebraicGeometry.Stacks.SurjectiveBaseChange
public import StacksFrontier.CategoryTheory.FiberedCategory.ElementsSection
public import StacksFrontier.CategoryTheory.FiberedCategory.SliceAsElements
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.EquivalenceOverComp
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverFunctoriality
public import StacksFrontier.AlgebraicGeometry.Quot.PolarizedFamiliesOverSpaceAlgebraic

/-!
# Polarized proper schemes over an algebraic space, as a 2-fibre product

Let `A` be an algebraic space over a terminal base `S` of the big fppf site. Remark 0D1N describes
the category `A-Polarized` of triples `(X ⟶ T, ℒ, h : T ⟶ A)`, where `(X ⟶ T, ℒ)` is a polarized
proper family, as the 2-fibre product of `𝒫olarized` with `(Sch/A)_{fppf}` over the big fppf site.
The second sentence of Stacks 0D4X deduces from it that `A-Polarized` is algebraic as soon as
`𝒫olarized` is, since algebraic stacks have 2-fibre products (Stacks 04T2). This file carries out
that deduction.

* The category `AlgebraicGeometry.PolarizedFamilyOver` of polarized families over `A` lies over
  the big fppf site of `S` through the base scheme of a family and its structure morphism,
  `AlgebraicGeometry.PolarizedFamilyOver.projection`, and is fibred in groupoids there: a
  morphism of base schemes lifts by base change of the polarized family and pullback of the point
  of `A`.
* It is equivalent over the site to the 2-fibre product of `𝒫olarized` with the stack `𝒮_A` of
  `A` over the stack of the terminal object of the site. The latter is an algebraic stack
  (Stacks 04X5) and so is `𝒮_A` (Stacks 026O), so the 2-fibre product is an algebraic stack by
  Stacks 04TF once `𝒫olarized` is.

## Main definitions

* `AlgebraicGeometry.PolarizedFamilyOver.projection`: the category `A-Polarized` of Remark
  0D1N, as a category over the big fppf site of `S`.

## Main results

* `AlgebraicGeometry.PolarizedFamilyOver.siteProjection_isFiberedInGroupoids`: `A-Polarized` is
  fibred in groupoids over the big fppf site.
* `AlgebraicGeometry.PolarizedFamilyOver.isAlgebraicStack_siteProjection_of_isAlgebraicStack`:
  if `𝒫olarized` is an algebraic stack, so is `A-Polarized` for every algebraic space `A`.

## Implementation notes

The 2-fibre product is taken over the stack `(Sch/S)_{fppf}` of the terminal object, which is the
whole big fppf site of `S`; this is the 2-fibre product over `Sch_{fppf}` of Remark 0D1N, the
base being `Spec(ℤ)` there. The comparison functor sends a family to its polarized family and its
point of `A`, with the identity comparison; it is fully faithful because a morphism of families
over `A` is a morphism of polarized families compatible with the points, and essentially
surjective by transport of the point along the comparison isomorphism of an object of the 2-fibre
product.

## References

* [Stacks Project, Tag 0D1N](https://stacks.math.columbia.edu/tag/0D1N)
* [Stacks Project, Tag 0D4X](https://stacks.math.columbia.edu/tag/0D4X)
* [Stacks Project, Tag 04T2](https://stacks.math.columbia.edu/tag/04T2)
* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.PolarizedFamilyOver

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {A : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

variable (B S hS A) in
/-- The image of a polarized family over `A` in the big fppf site is its base scheme, over `S`
through its structure morphism. -/
@[simp]
theorem siteProjection_obj (X : PolarizedFamilyOver B S hS A) :
    (AlgebraicGeometry.PolarizedFamilyOver.projection B S hS A).obj X = Over.mk X.toBase := rfl

/-- The image of a morphism of polarized families over `A` in the big fppf site is the morphism
of base schemes of its morphism of polarized families. -/
@[simp]
theorem siteProjection_map_left {X Y : PolarizedFamilyOver B S hS A} (f : X ⟶ Y) :
    ((AlgebraicGeometry.PolarizedFamilyOver.projection B S hS A).map f).left =
      PolarizedFamily.Hom.baseMap f.polarizedHom := rfl

namespace SiteLift

/-- The morphism of polarized families over `A` from a base change to the family it is a base
change of. -/
def ofLiftHom (X : PolarizedFamilyOver B S hS A) {y : PolarizedFamily B}
    (φ : y ⟶ X.polarized) : ofLift X φ ⟶ X where
  polarizedHom := φ
  base_comm := rfl
  point_comm := rfl

end SiteLift

open SiteLift in
/-- **Polarized families over `A` form a category fibred in groupoids** over the big fppf site of
`S`: a morphism of base schemes lifts by base change of the polarized family and pullback of the
point, and fill-ins are those of the polarized families, the compatibility with the points being
automatic. -/
theorem siteProjection_isFiberedInGroupoids :
    (AlgebraicGeometry.PolarizedFamilyOver.projection B S hS A).IsFiberedInGroupoids :=
  projection_isFiberedInGroupoids

/-! ### The 2-fibre product with the stack of the algebraic space -/

namespace SiteTwoFibreProduct

variable (hT : IsTerminal (B.obj hS))

variable (B S hS) in
/-- The terminal object of the big fppf site of `S`. -/
abbrev terminalObj : BigFppfOver B S hS := Over.mk (𝟙 (B.obj hS))

variable (B hS A) in
/-- The objects of the stack `𝒮_A`: the elements of `A`. -/
abbrev SpaceObj :=
  Pseudofunctor.CoGrothendieck ((A ⋙ typeToGrpd) ⋙ Grpd.forgetToCat).toPseudofunctor'

variable (B hS A) in
/-- The 2-fibre product, over the stack of the terminal object of the site, of `𝒫olarized` with
the stack `𝒮_A` of the presheaf `A`. -/
abbrev TwoFibreProductPt :=
  TwoFibreProductOver (polarizedSliceProjection B hS hT) (spaceForget B hS A)
    (Over.forget (terminalObj B S hS))
    (polarizedSliceProjection B hS hT ⋙ toTerminalSlice B S hS)
    ((spaceForget B hS A) ⋙ toTerminalSlice B S hS)

/-- Over a terminal base the comparison functor lies over the big fppf site: its composite with
the projection of the 2-fibre product is the projection of the polarized families over `A`. -/
theorem toTwoFibreProduct_comp_structureFunctor :
    toTwoFibreProduct hT ⋙ TwoFibreProductOver.structureFunctor _ _ _ _ _ =
      AlgebraicGeometry.PolarizedFamilyOver.projection B S hS A :=
  AlgebraicGeometry.PolarizedFamilyOver.toTwoFibreProduct_comp_structureFunctor hT

/-- The comparison functor is faithful: a morphism of polarized families over `A` is determined
by its morphism of polarized families. -/
instance : (toTwoFibreProduct (A := A) hT).Faithful where
  map_injective {_ _} _ _ h :=
    Hom.ext (congrArg TwoFibreProductOver.Hom.a h)

/-- The comparison functor is full. -/
instance : (toTwoFibreProduct (A := A) hT).Full where
  map_surjective {X Y} h := by
    have hφ : PolarizedFamily.Hom.baseMap h.a ≫ Y.toBase = X.toBase := hT.hom_ext _ _
    have key := sliceProjection_map_comp_eqToHom' hT h.a hφ
    have hbase : h.b.base = eqToHom (sliceProjection_obj_polarized hT X) ≫
        (Over.homMk (PolarizedFamily.Hom.baseMap h.a) hφ : Over.mk X.toBase ⟶ Over.mk Y.toBase) ≫
          eqToHom (sliceProjection_obj_polarized hT Y).symm :=
      (sliceProjection_map_a_eq_base hT h).symm.trans (by
        rw [← Category.assoc, ← key, Category.assoc, eqToHom_trans, eqToHom_refl,
          Category.comp_id])
    have hfib : A.map (eqToHom (sliceProjection_obj_polarized hT X)).op X.point =
        A.map h.b.base.op (A.map (eqToHom (sliceProjection_obj_polarized hT Y)).op Y.point) :=
      Discrete.eq_of_hom h.b.fiber
    have hpt : A.map (eqToHom (sliceProjection_obj_polarized hT X)).op X.point =
        A.map (eqToHom (sliceProjection_obj_polarized hT X)).op
          (A.map (Over.homMk (PolarizedFamily.Hom.baseMap h.a) hφ :
            Over.mk X.toBase ⟶ Over.mk Y.toBase).op Y.point) := by
      refine hfib.trans ?_
      refine (Functor.map_comp_apply A _ _ _).symm.trans
        (Eq.trans ?_ (Functor.map_comp_apply A _ _ _))
      change A.map ((h.b.base ≫ eqToHom (sliceProjection_obj_polarized hT Y)).op) Y.point =
        A.map ((eqToHom (sliceProjection_obj_polarized hT X) ≫
          (Over.homMk (PolarizedFamily.Hom.baseMap h.a) hφ :
            Over.mk X.toBase ⟶ Over.mk Y.toBase)).op) Y.point
      have hm : h.b.base ≫ eqToHom (sliceProjection_obj_polarized hT Y) =
          eqToHom (sliceProjection_obj_polarized hT X) ≫
            (Over.homMk (PolarizedFamily.Hom.baseMap h.a) hφ :
              Over.mk X.toBase ⟶ Over.mk Y.toBase) := by
        rw [hbase]
        exact eqToHom_comp_assoc_eqToHom _ _ _ _
      rw [hm]
      rfl
    let u : X ⟶ Y :=
      { polarizedHom := h.a
        base_comm := hφ
        point_comm :=
          ((A.mapIso (eqToIso (sliceProjection_obj_polarized hT X)).op).toEquiv.injective
            hpt).symm }
    exact ⟨u, TwoFibreProductOver.Hom.ext' rfl
      (PresheafOfCategories.elements_hom_ext (G := A) _ _ (sliceProjection_map_a_eq_base hT h))⟩

/-- The comparison isomorphism from the image of `ofTwoFibreProduct P` to `P`. -/
def ofTwoFibreProductHom (P : TwoFibreProductPt B hS A hT) :
    (toTwoFibreProduct hT).obj (ofTwoFibreProduct hT P) ⟶ P where
  hbase := eqToHom P.hx
  a := 𝟙 P.x
  b := (ofTwoFibreProductElementIso hT P).hom
  ha := IsHomLift.id_lift_eqToHom_domain P.hx rfl
  hb := by
    refine IsHomLift.of_fac' _ _ _ rfl P.hy ?_
    change eqToHom (ofTwoFibreProduct_base_eq hT P) = _
    simp only [eqToHom_trans]
    rfl
  w := by
    apply (Over.forget (terminalObj B S hS)).map_injective
    have hv := P.vertical
    simp only [CategoryTheory.Functor.map_comp]
    rw [IsHomLift.fac' (Over.forget (terminalObj B S hS)) (𝟙 P.base) P.iso.hom]
    change 𝟙 _ ≫ eqToHom P.hx ≫ 𝟙 P.base ≫ eqToHom P.hy.symm =
      𝟙 _ ≫ eqToHom (ofTwoFibreProduct_base_eq hT P)
    simp only [Category.id_comp, eqToHom_trans]
    rfl

/-- The comparison morphism from the image of `ofTwoFibreProduct P` to `P` is an isomorphism. -/
instance (P : TwoFibreProductPt B hS A hT) : IsIso (ofTwoFibreProductHom hT P) := by
  have : IsIso (ofTwoFibreProductHom hT P).b := by
    change IsIso (ofTwoFibreProductElementIso hT P).hom
    infer_instance
  have : IsIso (ofTwoFibreProductHom hT P).a := by
    change IsIso (𝟙 P.x)
    infer_instance
  have : IsIso (ofTwoFibreProductHom hT P).hbase := by
    change IsIso (eqToHom P.hx)
    infer_instance
  exact TwoFibreProductOver.isIso_of_components _

/-- The comparison functor is essentially surjective. -/
instance : (toTwoFibreProduct (A := A) hT).EssSurj where
  mem_essImage P := ⟨ofTwoFibreProduct hT P, ⟨asIso (ofTwoFibreProductHom hT P)⟩⟩

/-- The comparison functor is an equivalence. -/
instance : (toTwoFibreProduct (A := A) hT).IsEquivalence where

end SiteTwoFibreProduct

open SiteTwoFibreProduct

universe w in
/-- Over a terminal base `S` of the site, if `𝒫olarized` is an algebraic stack, then for every
algebraic space `A` over `S` the category `A-Polarized` of Remark 0D1N, of polarized proper
schemes `(X ⟶ T, ℒ)` together with a morphism `T ⟶ A`, is an algebraic stack. -/
theorem isAlgebraicStack_siteProjection_of_isAlgebraicStack (hT : IsTerminal (B.obj hS))
    (hA : IsAlgebraicSpace B S hS A)
    (h : Stack.IsAlgebraicStack.{u, w} B S hS (polarizedStackUnconditional B hS hT).val) :
    Stack.IsAlgebraicStack.{u, w} B S hS
      (BasedCategory.ofFunctor (AlgebraicGeometry.PolarizedFamilyOver.projection B S hS A)) :=
  isAlgebraicStack_of_isAlgebraicStack hT hA h

end AlgebraicGeometry.PolarizedFamilyOver

end
