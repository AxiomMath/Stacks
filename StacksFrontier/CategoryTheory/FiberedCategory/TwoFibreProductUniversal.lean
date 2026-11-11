module

public import StacksFrontier.CategoryTheory.FiberedCategory.TwoFibreProduct
public import StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase

/-!
# The universal property of the 2-fibre product in `Fib/𝒞` (Stacks 02XQ)

Stacks 02XQ says that the (2,1)-category of fibred categories over `𝒞` (Stacks 02XP) has
2-fibre products, described as in Stacks 0040. Its 1-morphisms are the functors strictly over
`𝒞` preserving strongly cartesian morphisms (`Functor.IsFibredOneMorphism`), and its 2-morphisms
are all the 2-morphisms of the 2-category of categories over `𝒞`, the vertical natural
transformations. So, beyond the 2-fibre product of Stacks 0040 itself, 02XQ requires:

* the 2-fibre product `𝒳 ×_𝒮 𝒴` is a fibred category:
  `TwoFibreProductOver.isFibered_structureFunctor`;
* the two projections are 1-morphisms of fibred categories:
  `TwoFibreProductOver.fst_isFibredOneMorphism`, `TwoFibreProductOver.snd_isFibredOneMorphism`;
* the mediating 1-morphism `TwoFibreProductOver.lift` of a test cone `(H, K, t)` whose legs
  `H`, `K` are 1-morphisms of fibred categories is again one:
  `TwoFibreProductOver.lift_isFibredOneMorphism` (this file).

The remaining clauses are those of Stacks 0040 verbatim, because the 2-morphisms of `Fib/𝒞` are
those of the 2-category of categories over `𝒞`: the 2-cell `psiIso` is vertical
(`psiIso_hom_vertical`), `lift` factors the test cone (`liftCompFst`, `liftCompSnd`, their
verticality, `lift_whiskerRight_psi`), and any other factorisation is 2-isomorphic to `lift`
(`liftIso`) by a unique 2-isomorphism (`natTrans_ext`). This file adds that the 2-isomorphism
`liftIso` is a 2-morphism over `𝒞`: its components are vertical for the structure functor
(`TwoFibreProductOver.liftIso_hom_app_isHomLift`).
-/

@[expose] public section

namespace CategoryTheory.TwoFibreProductOver

universe v₁ v₂ v₃ v₄ v₅ u₁ u₂ u₃ u₄ u₅

/- As in `StacksFrontier.CategoryTheory.TwoFibreProduct.OverBase`: the `implicit` transparency level
does not unfold `fst`, `structureFunctor` and `lift`, so for instance
`(structureFunctor _ _ _ _ _).obj P` and `P.base` would not match in the `eqToHom` bookkeeping
below. -/
attribute [local implicit_reducible] fst structureFunctor lift

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒳 : Type u₂} [Category.{v₂} 𝒳]
  {𝒴 : Type u₃} [Category.{v₃} 𝒴] {𝒮 : Type u₄} [Category.{v₄} 𝒮]
  {p𝒳 : 𝒳 ⥤ 𝒞} {p𝒴 : 𝒴 ⥤ 𝒞} {p𝒮 : 𝒮 ⥤ 𝒞} {F : 𝒳 ⥤ 𝒮} {G : 𝒴 ⥤ 𝒮}

/-- **Stacks 02XQ, universal property in `Fib/𝒞`.** Let `F : 𝒳 ⥤ 𝒮` and `G : 𝒴 ⥤ 𝒮` be
1-morphisms of fibred categories over `𝒞`, and let `(W, pW)` be a category over `𝒞` with
1-morphisms of fibred categories `H : W ⥤ 𝒳`, `K : W ⥤ 𝒴` and a vertical isomorphism
`t : H ⋙ F ≅ K ⋙ G`. Then the mediating 1-morphism `lift : W ⥤ 𝒳 ×_𝒮 𝒴` of Stacks 0040 is a
1-morphism of fibred categories: it is strictly over `𝒞` and preserves strongly cartesian
morphisms. The image of a strongly cartesian `φ` has the strongly cartesian components `H φ` and
`K φ`, so it is strongly cartesian by `isStronglyCartesian_of_components`.

Fibredness of `p𝒳`, `p𝒴`, `p𝒮` and `pW` is not used, so the statement is made without it. -/
@[stacks 02XQ "universal property in Fib/C"]
theorem lift_isFibredOneMorphism
    (hF : Functor.IsFibredOneMorphism p𝒳 p𝒮 F) (hG : Functor.IsFibredOneMorphism p𝒴 p𝒮 G)
    {W : Type u₅} [Category.{v₅} W] {pW : W ⥤ 𝒞} {H : W ⥤ 𝒳} {K : W ⥤ 𝒴}
    (hH : Functor.IsFibredOneMorphism pW p𝒳 H) (hK : Functor.IsFibredOneMorphism pW p𝒴 K)
    (t : H ⋙ F ≅ K ⋙ G) (ht : ∀ w, p𝒮.IsHomLift (𝟙 (pW.obj w)) (t.hom.app w)) :
    Functor.IsFibredOneMorphism pW (structureFunctor p𝒳 p𝒴 p𝒮 F G)
      (lift p𝒳 p𝒴 p𝒮 F G pW H K hH.comp_eq hK.comp_eq t ht) where
  comp_eq := lift_comp_structureFunctor p𝒳 p𝒴 p𝒮 F G pW H K hH.comp_eq hK.comp_eq t ht
  map_isStronglyCartesian := by
    intro _ _ f _ _ φ hφ
    have := hφ.toIsHomLift
    exact isStronglyCartesian_of_components hF hG f _
      (Functor.isHomLift_map_of_comp_eq
        (lift_comp_structureFunctor p𝒳 p𝒴 p𝒮 F G pW H K hH.comp_eq hK.comp_eq t ht) f φ)
      (hH.map_isStronglyCartesian f φ hφ) (hK.map_isStronglyCartesian f φ hφ)

/-- **Stacks 02XQ, uniqueness in `Fib/𝒞`.** The 2-isomorphism `liftIso` between another
factorisation `γ` of the test cone and the mediating 1-morphism `lift` is a 2-morphism over `𝒞`:
each of its components lies over an identity of `𝒞` for the structure functor. Together with
`natTrans_ext` this makes the factorisation unique up to a unique 2-isomorphism of `Fib/𝒞`,
whose 2-morphisms are those of the 2-category of categories over `𝒞`. -/
@[stacks 02XQ "uniqueness of the factorisation"]
theorem liftIso_hom_app_isHomLift
    {W : Type u₅} [Category.{v₅} W] {pW : W ⥤ 𝒞} {H : W ⥤ 𝒳} {K : W ⥤ 𝒴}
    {t : H ⋙ F ≅ K ⋙ G} (γ : W ⥤ TwoFibreProductOver p𝒳 p𝒴 p𝒮 F G)
    (a : γ ⋙ fst p𝒳 p𝒴 p𝒮 F G ≅ H) (b : γ ⋙ snd p𝒳 p𝒴 p𝒮 F G ≅ K)
    (ha : ∀ w, p𝒳.IsHomLift (𝟙 (pW.obj w)) (a.hom.app w))
    (hb : ∀ w, p𝒴.IsHomLift (𝟙 (pW.obj w)) (b.hom.app w))
    (hab : Functor.whiskerRight a.hom F ≫ t.hom =
      Functor.whiskerLeft γ (psiIso p𝒳 p𝒴 p𝒮 F G).hom ≫ Functor.whiskerRight b.hom G)
    (hH : H ⋙ p𝒳 = pW) (hK : K ⋙ p𝒴 = pW)
    (ht : ∀ w, p𝒮.IsHomLift (𝟙 (pW.obj w)) (t.hom.app w)) (w : W) :
    (structureFunctor p𝒳 p𝒴 p𝒮 F G).IsHomLift (𝟙 (pW.obj w))
      ((liftIso γ a b ha hb hab hH hK ht).hom.app w) := by
  -- The base morphism of the component is induced by its `𝒳`-component `a.hom.app w`, which is
  -- vertical.
  have := ha w
  refine IsHomLift.of_fac _ _ _
    ((γ.obj w).hx.symm.trans (IsHomLift.domain_eq p𝒳 (𝟙 (pW.obj w)) (a.hom.app w)))
    (((lift p𝒳 p𝒴 p𝒮 F G pW H K hH hK t ht).obj w).hx.symm.trans
      (IsHomLift.codomain_eq p𝒳 (𝟙 (pW.obj w)) (a.hom.app w))) ?_
  refine (IsHomLift.fac p𝒳 (𝟙 (pW.obj w)) (a.hom.app w)).trans ?_
  rw [structureFunctor_map, Hom.hbase_eq,
    show ((liftIso γ a b ha hb hab hH hK ht).hom.app w).a = a.hom.app w from rfl]
  simp

end CategoryTheory.TwoFibreProductOver
