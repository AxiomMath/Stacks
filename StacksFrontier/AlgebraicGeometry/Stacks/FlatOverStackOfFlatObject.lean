module

public import StacksFrontier.AlgebraicGeometry.Stacks.FlatOverStackExtComparison
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CoverDescent.ComponentPresheafFstIso

/-!
# The presheaf `x ↦ Hom(f(x), y)` of a flat object `y`

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks and let `y` be a flat object of `𝒴`
(**Stacks 0787**), lying over the scheme `V`. Sections over `y` of a direct image along `f` are
corepresented by the free abelian sheaf on the presheaf

`f^p h_y : x ↦ Hom_𝒴(f(x), y)`

on `𝒳`. This file proves that `f^p h_y` is, up to isomorphism, the presheaf of components of the
projection `𝒳 ×_𝒴 (Sch/V) ⟶ 𝒳` of the 2-fibre product with the 1-morphism `(Sch/V) ⟶ 𝒴` named
by `y`, and that this projection is flat, being a base change of a flat 1-morphism
(**Stacks 06PY**), with faithful underlying functor. So `f^p h_y` lies, up to isomorphism, in
the class `AlgebraicGeometry.Stack.FlatOverStack`, whose `Ext`-groups
`AlgebraicGeometry.Stack.extFreeAbelianSheafFlatOverStackIso` computes on the flat-fppf site.

## Main results

* `CategoryTheory.TwoFibreProductOver.faithful_fst`: the first projection of a 2-fibre product
  is faithful when the second factor is faithful over the base.
* `AlgebraicGeometry.Stack.exists_flatOverStack_iso_restriction_uliftYoneda`: the membership.

## References

* [Stacks Project, Tag 0787](https://stacks.math.columbia.edu/tag/0787)
* [Stacks Project, Tag 06PY](https://stacks.math.columbia.edu/tag/06PY)
* [Stacks Project, Tag 0775](https://stacks.math.columbia.edu/tag/0775)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.Sites.CoverDescent

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ u₁ u₂ u₃ u₄

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  (p𝒳 : 𝒳 ⥤ 𝒞) (p𝒴 : 𝒴 ⥤ 𝒞) (p𝒮 : 𝒮 ⥤ 𝒞) (F : 𝒳 ⥤ 𝒮) (G : 𝒴 ⥤ 𝒮)

/-- **The first projection of a 2-fibre product is faithful when the second factor is faithful
over the base.** A morphism of the 2-fibre product is determined by its first component: that
component determines the base morphism, and the second component, lying over it, is determined
by it. -/
theorem faithful_fst [p𝒴.Faithful] : (fst p𝒳 p𝒴 p𝒮 F G).Faithful where
  map_injective {P Q} m m' h := by
    change m.a = m'.a at h
    refine Hom.ext' h (p𝒴.map_injective ?_)
    have key : ∀ k : P ⟶ Q, p𝒴.map k.b = eqToHom P.hy ≫ k.hbase ≫ eqToHom Q.hy.symm :=
      fun k => by
        have := k.hb
        rw [IsHomLift.fac' p𝒴 k.hbase k.b]
    have e3 : m.hbase = m'.hbase := by rw [m.hbase_eq, m'.hbase_eq, h]
    rw [key m, key m', e3]

end CategoryTheory.TwoFibreProductOver

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The presheaf `x ↦ Hom_𝒴(f(x), y)` of a flat object `y` is represented by a flat
1-morphism.** For a 1-morphism `f : 𝒳 ⟶ 𝒴` of algebraic stacks and a flat object `y` of `𝒴`,
the restriction along `f` of the representable presheaf of `y` is isomorphic to the presheaf of
components of the projection `𝒳 ×_𝒴 (Sch/V) ⟶ 𝒳`, which is flat with faithful underlying
functor; so it lies, up to isomorphism, in `AlgebraicGeometry.Stack.FlatOverStack`. -/
theorem exists_flatOverStack_iso_restriction_uliftYoneda {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (y : 𝒴.val.val.obj) (hy : flatObject B S hS 𝒴.val y) :
    ∃ Ψ : 𝒳.val.val.objᵒᵖ ⥤ Type (u + 1), FlatOverStack 𝒳 Ψ ∧
      Nonempty ((CatFiberedInGroupoids.homFunctor f.hom).op ⋙
        uliftYoneda.{u + 1}.obj y ≅ Ψ) := by
  let V := 𝒴.val.val.p.obj y
  let gy : schemeStack.{u, w} B S hS V ⟶ 𝒴 := Bicategory.InducedBicategory.mkHom
    (objectMorphism B S hS 𝒴.val (Functor.Fiber.mk (a := y) rfl))
  have hgy : AlgebraicStacks.IsFlat B S hS gy := hy
  let sq := twoFibreProductSquareAlgebraicStacks B S hS f gy
  have hflat : AlgebraicStacks.IsFlat B S hS sq.fst :=
    AlgebraicStacks.isFlat_baseChange B S hS gy f sq
      (isTwoFibreProduct_twoFibreProductSquareAlgebraicStacks B S hS f gy) hgy
  have : (schemeStack.{u, w} B S hS V).val.val.p.Faithful :=
    inferInstanceAs (Over.forget V).Faithful
  have hfaith : (CatFiberedInGroupoids.homFunctor sq.fst.hom).Faithful :=
    TwoFibreProductOver.faithful_fst 𝒳.val.val.p (schemeStack.{u, w} B S hS V).val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor gy.hom)
  refine ⟨componentPresheaf (CatFiberedInGroupoids.homFunctor sq.fst.hom),
    ⟨sq.pt, sq.fst, hfaith, hflat, rfl⟩, ⟨?_⟩⟩
  let e := Functor.TwoYoneda.liftBasedEvaluationIso 𝒴.val.val.p 𝒴.val.isFiberedInGroupoids
    V (Functor.Fiber.mk (a := y) rfl)
  refine Functor.isoWhiskerLeft (CatFiberedInGroupoids.homFunctor f.hom).op
      (uliftYoneda.{u + 1}.mapIso (Functor.Fiber.fiberInclusion.mapIso e).symm ≪≫
        (componentPresheafIsoOfIsTerminal (CatFiberedInGroupoids.homFunctor gy.hom)
          (Over.mkIdTerminal (X := V))).symm) ≪≫
    (componentPresheafFstIso 𝒳.val.val.p (schemeStack.{u, w} B S hS V).val.val.p
      𝒴.val.val.p (CatFiberedInGroupoids.homFunctor f.hom)
      (CatFiberedInGroupoids.homFunctor gy.hom) 𝒳.val.isFiberedInGroupoids
      (schemeStack.{u, w} B S hS V).val.isFiberedInGroupoids 𝒴.val.isFiberedInGroupoids
      f.hom.hom.w gy.hom.hom.w).symm

end AlgebraicGeometry.Stack

end
