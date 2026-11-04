module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PolynomialTransport
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposPullbackHomAlgebra

/-!
# Postcomposition of generalized elements of a sheaf of rings, as a ring homomorphism

The generalized elements `Z ⟶ ringSheaf R` of a sheaf of rings `R` of shape `Z` form a ring. This
file shows that postcomposition with a morphism of sheaves of rings is a ring homomorphism of
generalized elements, so a polynomial relation `Pⱼ(a₁, …, a_n) = 0` among generalized elements is
preserved by it. Precomposition with a morphism of sheaves of sets and the inverse image along a
finite-product-preserving functor are `CategoryTheory.Sheaf.compRingHom` and
`Stacks.Sheaves.ToposPullback.inverseImageRingEltRingHom`.

## Main definitions

* `CategoryTheory.Sheaf.postcompRingHom`: postcomposition with a morphism of sheaves of rings, as
  a ring homomorphism of generalized elements.

## Main results

* `CategoryTheory.Sheaf.postcomp_hom_add`, `CategoryTheory.Sheaf.postcomp_hom_mul`,
  `CategoryTheory.Sheaf.postcomp_hom_ringZero`, `CategoryTheory.Sheaf.postcomp_hom_one`:
  postcomposition with a morphism of sheaves of rings respects the ring operations on generalized
  elements.

## References

* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 00X1](https://stacks.math.columbia.edu/tag/00X1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe t w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget RingCat.{w})] [J.HasSheafCompose (forget AddCommGrpCat.{w})]
  {R R' : Sheaf J RingCat.{w}} {Z Z' : Sheaf J (Type w)}

section Postcomposition

omit [J.HasSheafCompose (forget AddCommGrpCat)] in
  /-- On sections over `X`, postcomposition with `θ` is the component `θ.app X`. -/
  private theorem sectionsFunctor_map_comp_postcomp (θ : R ⟶ R') (a : Z ⟶ ringSheaf R) (X : Cᵒᵖ)
      (s : (sectionsFunctor J X).obj Z) :
      (sectionsFunctor J X).map (a ≫ (sheafCompose J (forget RingCat.{w})).map θ) s =
        (θ.hom.app X).hom ((sectionsFunctor J X).map a s) :=
    (sectionsFunctor J X).map_comp_apply ..

omit [J.HasSheafCompose (forget AddCommGrpCat)] in
/-- Postcomposition with a morphism of sheaves of rings is additive on generalized elements. -/
theorem postcomp_hom_add (θ : R ⟶ R') (a b : Z ⟶ ringSheaf R) :
    (a + b) ≫ (sheafCompose J (forget RingCat.{w})).map θ =
      a ≫ (sheafCompose J (forget RingCat.{w})).map θ +
        b ≫ (sheafCompose J (forget RingCat.{w})).map θ := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp only [sectionsFunctor_map_comp_postcomp, sectionsFunctor_map_hom_add]
  exact map_add (θ.hom.app X).hom _ _

omit [J.HasSheafCompose (forget AddCommGrpCat)] in
/-- Postcomposition with a morphism of sheaves of rings is multiplicative on generalized
elements. -/
theorem postcomp_hom_mul (θ : R ⟶ R') (a b : Z ⟶ ringSheaf R) :
    (a * b) ≫ (sheafCompose J (forget RingCat.{w})).map θ =
      (a ≫ (sheafCompose J (forget RingCat.{w})).map θ) *
        (b ≫ (sheafCompose J (forget RingCat.{w})).map θ) := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp only [sectionsFunctor_map_comp_postcomp, sectionsFunctor_map_hom_mul]
  exact map_mul (θ.hom.app X).hom _ _

omit [J.HasSheafCompose (forget AddCommGrpCat)] in
/-- Postcomposition with a morphism of sheaves of rings kills the zero generalized element. -/
theorem postcomp_hom_ringZero (θ : R ⟶ R') :
    (0 : Z ⟶ ringSheaf R) ≫ (sheafCompose J (forget RingCat.{w})).map θ = 0 := by
  refine hom_ext_sections (fun X s ↦ ?_)
  simp only [sectionsFunctor_map_comp_postcomp, sectionsFunctor_map_hom_ringZero]
  exact map_zero (θ.hom.app X).hom

omit [J.HasSheafCompose (forget AddCommGrpCat)] in
/-- Postcomposition with a morphism of sheaves of rings preserves the unit generalized
element. -/
theorem postcomp_hom_one (θ : R ⟶ R') :
    (1 : Z ⟶ ringSheaf R) ≫ (sheafCompose J (forget RingCat.{w})).map θ = 1 := by
  refine hom_ext_sections (fun X s ↦ ?_)
  rw [sectionsFunctor_map_comp_postcomp,
    show (sectionsFunctor J X).map (1 : Z ⟶ ringSheaf R) s = 1 from
      (map_hom_one (sectionsFunctor J X) s).trans (sectionsFunctor_map_ringOneHom R X _),
    show (sectionsFunctor J X).map (1 : Z ⟶ ringSheaf R') s = 1 from
      (map_hom_one (sectionsFunctor J X) s).trans (sectionsFunctor_map_ringOneHom R' X _)]
  exact map_one (θ.hom.app X).hom

/-- Postcomposition with a morphism `θ : R ⟶ R'` of sheaves of rings, as a ring homomorphism from
the generalized elements of `R` of shape `Z` to those of `R'`. -/
def postcompRingHom (θ : R ⟶ R') : (Z ⟶ ringSheaf R) →+* (Z ⟶ ringSheaf R') where
  toFun a := a ≫ (sheafCompose J (forget RingCat.{w})).map θ
  map_one' := postcomp_hom_one θ
  map_mul' a b := postcomp_hom_mul θ a b
  map_zero' := postcomp_hom_ringZero θ
  map_add' a b := postcomp_hom_add θ a b

omit [J.HasSheafCompose (forget AddCommGrpCat)] in
/-- `postcompRingHom θ` sends `a` to its composite with the morphism of underlying sheaves of sets
of `θ`. -/
@[simp]
theorem postcompRingHom_apply (θ : R ⟶ R') (a : Z ⟶ ringSheaf R) :
    postcompRingHom (Z := Z) θ a = a ≫ (sheafCompose J (forget RingCat.{w})).map θ :=
  rfl

end Postcomposition

end CategoryTheory.Sheaf

namespace Stacks.Sheaves.ToposPullback

open CategoryTheory Limits Sheaf Functor Opposite

universe ww ww' vv uu vv' uu'

variable {C : Type uu} [Category.{vv} C] {D : Type uu'} [Category.{vv'} D]
  (J : GrothendieckTopology C) {K : GrothendieckTopology D}
  [J.HasSheafCompose (forget RingCat.{ww})] [K.HasSheafCompose (forget RingCat.{ww'})]
  [J.HasSheafCompose (forget AddCommGrpCat.{ww})]
  [K.HasSheafCompose (forget AddCommGrpCat.{ww'})]
  (Φ : Sheaf K (Type ww') ⥤ Sheaf J (Type ww)) [PreservesFiniteProducts Φ]
  {R : Sheaf K RingCat.{ww'}} {Z : Sheaf K (Type ww')} {W : Sheaf J (Type ww)}

end Stacks.Sheaves.ToposPullback

end
