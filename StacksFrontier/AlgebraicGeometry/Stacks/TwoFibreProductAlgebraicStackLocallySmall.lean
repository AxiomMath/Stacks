module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.AlgebraicStackEquivalenceUniverses
public import StacksFrontier.AlgebraicGeometry.Stacks.TwoFibreProductAlgebraicStack
public import StacksFrontier.CategoryTheory.FiberedCategory.ShrinkHomsBasedCategory
public import StacksFrontier.CategoryTheory.FiberedCategory.PresheafElementsEquivalence

/-!
# Stacks 04TF for algebraic stacks with locally small morphisms in any universe

`AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct`, the library's Stacks 04TF, is stated
for categories over the big fppf site whose morphisms live in the universe of the site,
`CategoryTheory.BasedCategory.{u, u + 1}`. A moduli stack such as the stack of curves has
morphisms which are morphisms of algebraic spaces, i.e. of presheaves on the site, and those live
one universe up. This file removes the restriction on the two algebraic factors: their morphism
universes are arbitrary, provided their hom-sets are `u`-small, which is the case for every
category whose morphisms are morphisms of sheaves on an essentially small site.

The proof replaces each factor by `CategoryTheory.BasedCategory.shrinkHoms` of it, which has the
same objects and `u`-small morphisms and is equivalent to it over the site *strictly*: the
comparison functors are the identity on objects and commute on the nose with the structure
functors. Algebraicity transports along that equivalence by
`AlgebraicGeometry.Stack.isAlgebraicStack_of_equivalenceOver` (Stacks 03YQ in independent
universes), `AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct` applies to the shrunken
factors, and the 2-fibre product of the shrunken factors is again strictly equivalent over the site
to that of the given ones.

## Main definitions

* `StacksRepresentableCFG.EquivalenceOver.ofStrictInverse`: an equivalence over a base from two
  functors over it which are inverse to each other on the nose.

## Main results

* `AlgebraicGeometry.Stack.isAlgebraicStack_shrinkHoms_iff`: a category with `u`-small
  hom-sets is an algebraic stack exactly when its shrunken form is.
* `AlgebraicGeometry.Stack.isAlgebraicStack_twoFibreProduct_of_locallySmall`: **Stacks 04TF**
  with the two algebraic factors in arbitrary morphism universes.

## References

* [Stacks Project, Tag 04TF](https://stacks.math.columbia.edu/tag/04TF)
* [Stacks Project, Tag 03YQ](https://stacks.math.columbia.edu/tag/03YQ)
-/

@[expose] public noncomputable section

open CategoryTheory

namespace StacksRepresentableCFG

universe v₀ u₀ v₁ u₁ v₂ u₂

variable {𝒞 : Type u₀} [Category.{v₀} 𝒞] {D₁ : Type u₁} [Category.{v₁} D₁]
  {D₂ : Type u₂} [Category.{v₂} D₂]

/-- The equivalence over `𝒞` given by two functors over `𝒞` whose composites are the identity
functors on the nose, with unit and counit the canonical `eqToIso`s. -/
def EquivalenceOver.ofStrictInverse {p : D₁ ⥤ 𝒞} {q : D₂ ⥤ 𝒞} (F : D₁ ⥤ D₂) (G : D₂ ⥤ D₁)
    (hF : F ⋙ q = p) (hG : G ⋙ p = q) (h₁ : F ⋙ G = 𝟭 D₁) (h₂ : G ⋙ F = 𝟭 D₂) :
    EquivalenceOver p q where
  hom := ⟨F, hF⟩
  inv := ⟨G, hG⟩
  unitIso := eqToIso h₁.symm
  counitIso := eqToIso h₂
  unit_over := by
    ext X
    simp [eqToHom_map]
  counit_over := by
    ext X
    simp [eqToHom_map]

end StacksRepresentableCFG

namespace AlgebraicGeometry.Stack

universe u w v₁ v₂

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- A category over the big fppf site with `u`-small hom-sets is an algebraic stack if and only if
its shrunken form `CategoryTheory.BasedCategory.shrinkHoms` is. -/
theorem isAlgebraicStack_shrinkHoms_iff
    (𝒳 : BasedCategory.{v₁, u + 1} (BigFppfOver B S hS)) [LocallySmall.{u} 𝒳.obj] :
    IsAlgebraicStack.{u, w} B S hS (𝒳.shrinkHoms) ↔
      IsAlgebraicStack.{u, w} B S hS 𝒳 :=
  ⟨isAlgebraicStack_of_equivalenceOver B S hS (BasedCategory.shrinkHomsEquivalenceOver 𝒳).symm,
    isAlgebraicStack_of_equivalenceOver B S hS (BasedCategory.shrinkHomsEquivalenceOver 𝒳)⟩

/-- A 1-morphism into `𝒵` read on the shrunken form of its source. -/
def shrinkHomsBasedFunctor {𝒳 : BasedCategory.{v₁, u + 1} (BigFppfOver B S hS)}
    [LocallySmall.{u} 𝒳.obj] {𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
    (f : 𝒳 ⥤ᵇ 𝒵) : 𝒳.shrinkHoms ⥤ᵇ 𝒵 where
  toFunctor := ShrinkHoms.inverse 𝒳.obj ⋙ f.toFunctor
  w := by
    change (ShrinkHoms.inverse 𝒳.obj ⋙ f.toFunctor) ⋙ 𝒵.p = ShrinkHoms.inverse 𝒳.obj ⋙ 𝒳.p
    rw [Functor.assoc, f.w]

section Comparison

variable {B S hS}
variable {𝒳 : BasedCategory.{v₁, u + 1} (BigFppfOver B S hS)}
  {𝒴 : BasedCategory.{v₂, u + 1} (BigFppfOver B S hS)}
  {𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS)}
  [LocallySmall.{u} 𝒳.obj] [LocallySmall.{u} 𝒴.obj] (f : 𝒳 ⥤ᵇ 𝒵) (g : 𝒴 ⥤ᵇ 𝒵)

/-- The 2-fibre product of the given factors, mapped to that of their shrunken forms. -/
def twoFibreProductToShrink :
    TwoFibreProductOver 𝒳.p 𝒴.p 𝒵.p f.toFunctor g.toFunctor ⥤
      TwoFibreProductOver (𝒳.shrinkHoms).p (𝒴.shrinkHoms).p 𝒵.p
        (shrinkHomsBasedFunctor B S hS f).toFunctor
        (shrinkHomsBasedFunctor B S hS g).toFunctor where
  obj P :=
    { base := P.base
      x := ShrinkHoms.toShrinkHoms P.x
      y := ShrinkHoms.toShrinkHoms P.y
      hx := P.hx
      hy := P.hy
      iso := P.iso
      vertical := P.vertical }
  map φ :=
    { hbase := φ.hbase
      a := (ShrinkHoms.functor 𝒳.obj).map φ.a
      b := (ShrinkHoms.functor 𝒴.obj).map φ.b
      ha := PresheafOfCategories.isHomLift_map_of_comp (BasedCategory.shrinkHoms_functor_comp 𝒳)
        φ.hbase φ.a φ.ha
      hb := PresheafOfCategories.isHomLift_map_of_comp (BasedCategory.shrinkHoms_functor_comp 𝒴)
        φ.hbase φ.b φ.hb
      w := by
        have h := φ.w
        change f.toFunctor.map ((equivShrink _).symm (equivShrink _ φ.a)) ≫ _ =
          _ ≫ g.toFunctor.map ((equivShrink _).symm (equivShrink _ φ.b))
        simpa using h }
  map_id P := TwoFibreProductOver.Hom.ext' ((ShrinkHoms.functor 𝒳.obj).map_id _)
    ((ShrinkHoms.functor 𝒴.obj).map_id _)
  map_comp φ ψ := TwoFibreProductOver.Hom.ext' ((ShrinkHoms.functor 𝒳.obj).map_comp _ _)
    ((ShrinkHoms.functor 𝒴.obj).map_comp _ _)

/-- The 2-fibre product of the shrunken forms, mapped back to that of the given factors. -/
def twoFibreProductFromShrink :
    TwoFibreProductOver (𝒳.shrinkHoms).p (𝒴.shrinkHoms).p 𝒵.p
        (shrinkHomsBasedFunctor B S hS f).toFunctor
        (shrinkHomsBasedFunctor B S hS g).toFunctor ⥤
      TwoFibreProductOver 𝒳.p 𝒴.p 𝒵.p f.toFunctor g.toFunctor where
  obj P :=
    { base := P.base
      x := ShrinkHoms.fromShrinkHoms P.x
      y := ShrinkHoms.fromShrinkHoms P.y
      hx := P.hx
      hy := P.hy
      iso := P.iso
      vertical := P.vertical }
  map φ :=
    { hbase := φ.hbase
      a := (ShrinkHoms.inverse 𝒳.obj).map φ.a
      b := (ShrinkHoms.inverse 𝒴.obj).map φ.b
      ha := PresheafOfCategories.isHomLift_map_of_comp (H := ShrinkHoms.inverse 𝒳.obj) rfl
        φ.hbase φ.a φ.ha
      hb := PresheafOfCategories.isHomLift_map_of_comp (H := ShrinkHoms.inverse 𝒴.obj) rfl
        φ.hbase φ.b φ.hb
      w := φ.w }
  map_id _ := TwoFibreProductOver.Hom.ext' ((ShrinkHoms.inverse 𝒳.obj).map_id _)
    ((ShrinkHoms.inverse 𝒴.obj).map_id _)
  map_comp _ _ := TwoFibreProductOver.Hom.ext' ((ShrinkHoms.inverse 𝒳.obj).map_comp _ _)
    ((ShrinkHoms.inverse 𝒴.obj).map_comp _ _)

/-- `twoFibreProductFromShrink` is a left inverse of `twoFibreProductToShrink` on the nose. -/
theorem twoFibreProductToShrink_comp_fromShrink :
    twoFibreProductToShrink f g ⋙ twoFibreProductFromShrink f g = 𝟭 _ :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq <|
    TwoFibreProductOver.Hom.ext' (Equiv.symm_apply_apply _ _) (Equiv.symm_apply_apply _ _))

/-- `twoFibreProductToShrink` is a left inverse of `twoFibreProductFromShrink` on the nose. -/
theorem twoFibreProductFromShrink_comp_toShrink :
    twoFibreProductFromShrink f g ⋙ twoFibreProductToShrink f g = 𝟭 _ :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq <|
    TwoFibreProductOver.Hom.ext' (Equiv.apply_symm_apply _ _) (Equiv.apply_symm_apply _ _))

/-- `twoFibreProductToShrink` commutes on the nose with the structure functors to the site. -/
theorem twoFibreProductToShrink_comp_structureFunctor :
    twoFibreProductToShrink f g ⋙ TwoFibreProductOver.structureFunctor
        (𝒳.shrinkHoms).p (𝒴.shrinkHoms).p 𝒵.p
        (shrinkHomsBasedFunctor B S hS f).toFunctor (shrinkHomsBasedFunctor B S hS g).toFunctor =
      TwoFibreProductOver.structureFunctor 𝒳.p 𝒴.p 𝒵.p f.toFunctor g.toFunctor :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq <| by
    rfl)

/-- `twoFibreProductFromShrink` commutes on the nose with the structure functors to the site. -/
theorem twoFibreProductFromShrink_comp_structureFunctor :
    twoFibreProductFromShrink f g ⋙
        TwoFibreProductOver.structureFunctor 𝒳.p 𝒴.p 𝒵.p f.toFunctor g.toFunctor =
      TwoFibreProductOver.structureFunctor
        (𝒳.shrinkHoms).p (𝒴.shrinkHoms).p 𝒵.p
        (shrinkHomsBasedFunctor B S hS f).toFunctor (shrinkHomsBasedFunctor B S hS g).toFunctor :=
  CategoryTheory.Functor.hext (fun _ => rfl) (fun _ _ _ => heq_of_eq <| by
    rfl)

end Comparison

/-- Let `𝒵` be a stack in groupoids over the big fppf site of `S` whose diagonal is representable
by algebraic spaces, let `𝒳` and `𝒴` be algebraic stacks over `S` whose hom-sets are `u`-small, in
any morphism universes, and let `f : 𝒳 ⟶ 𝒵`, `g : 𝒴 ⟶ 𝒵` be 1-morphisms. Then the 2-fibre product
`𝒳 ×_{f, 𝒵, g} 𝒴` is an algebraic stack over `S`. -/
@[stacks 04TF "the two algebraic factors with locally small morphisms in any universe"]
theorem isAlgebraicStack_twoFibreProduct_of_locallySmall
    (𝒳 : BasedCategory.{v₁, u + 1} (BigFppfOver B S hS))
    (𝒴 : BasedCategory.{v₂, u + 1} (BigFppfOver B S hS))
    (𝒵 : BasedCategory.{u, u + 1} (BigFppfOver B S hS))
    [LocallySmall.{u} 𝒳.obj] [LocallySmall.{u} 𝒴.obj]
    (f : 𝒳 ⥤ᵇ 𝒵) (g : 𝒴 ⥤ᵇ 𝒵)
    (h𝒵 : 𝒵.p.IsStack (BigFppfOver.topology B S hS) ∧
      𝒵.p.IsStackInGroupoids.{w} (BigFppfOver.topology B S hS))
    (hdiag : HasRepresentableDiagonal B S hS
      (CatFiberedInGroupoids.mk 𝒵 h𝒵.2.isFiberedInGroupoids))
    (h𝒳 : IsAlgebraicStack.{u, w} B S hS 𝒳)
    (h𝒴 : IsAlgebraicStack.{u, w} B S hS 𝒴) :
    IsAlgebraicStack.{u, w} B S hS
      (BasedCategory.ofFunctor
        (TwoFibreProductOver.structureFunctor 𝒳.p 𝒴.p 𝒵.p f.toFunctor g.toFunctor)) := by
  have hsmall := isAlgebraicStack_twoFibreProduct.{u, w} B S hS (𝒳.shrinkHoms)
    (𝒴.shrinkHoms) 𝒵 (shrinkHomsBasedFunctor B S hS f)
    (shrinkHomsBasedFunctor B S hS g) h𝒵 hdiag
    ((isAlgebraicStack_shrinkHoms_iff B S hS 𝒳).2 h𝒳)
    ((isAlgebraicStack_shrinkHoms_iff B S hS 𝒴).2 h𝒴)
  exact isAlgebraicStack_of_equivalenceOver B S hS
    (StacksRepresentableCFG.EquivalenceOver.ofStrictInverse
      (twoFibreProductFromShrink f g) (twoFibreProductToShrink f g)
      (twoFibreProductFromShrink_comp_structureFunctor f g)
      (twoFibreProductToShrink_comp_structureFunctor f g)
      (twoFibreProductFromShrink_comp_toShrink f g)
      (twoFibreProductToShrink_comp_fromShrink f g)) hsmall

end AlgebraicGeometry.Stack

end
