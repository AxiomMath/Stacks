module

public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubstackCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.ClosedSubstackIntersection
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Stacks.DimensionSchemeTheoreticImage
public import StacksFrontier.AlgebraicGeometry.Stacks.ImmersionMonomorphism
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothLocalMorphismBaseChange

/-!
# Closed substacks holding everywhere

A closed substack `P` of the algebraic stack of a scheme `U` cuts out a closed subscheme of `U`
(Stacks 0507). If a morphism `γ : V ⟶ U` lands in `P` and every closed immersion into `U` through
which `γ` factors is an isomorphism, then that closed subscheme is `U` and `P` holds at every
object. A substack holding at every object is the whole stack up to equivalence: its inclusion is
smooth, so the dimension of Stacks 0AFN of the substack at a point is that of the ambient stack.

## Main results

* `AlgebraicGeometry.Stack.forall_prop_of_isClosedSubstack_schemeStack`.
* `AlgebraicGeometry.Stack.isSmooth_fullSubcategoryInclusion_of_forall` and
  `AlgebraicGeometry.Stack.dimensionAtPoint_fullSubcategory_eq_of_forall`.

## References

* [Stacks Project, Tag 0507](https://stacks.math.columbia.edu/tag/0507)
* [Stacks Project, Tag 0AFN](https://stacks.math.columbia.edu/tag/0AFN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **A closed substack of the stack of a scheme `U` containing a point `γ : V ⟶ U` holds at every
object**, as soon as every closed immersion into `U` through which `γ` factors is an
isomorphism: the closed subspace that the substack cuts out of `U` is such a closed immersion. -/
theorem forall_prop_of_isClosedSubstack_schemeStack {U V : BigFppfOver B S hS}
    {P : ObjectProperty (schemeStack.{u, w} B S hS U).val.val.obj}
    (hP : IsClosedSubstack (schemeStack.{u, w} B S hS U) P) (γ : V ⟶ U) (hγ : P (Over.mk γ))
    (hiso : ∀ {W : BigFppfOver B S hS} (i : W ⟶ U),
      _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) →
        ∀ h : V ⟶ W, h ≫ i = γ → IsIso ((BigFppfOver.toScheme B S hS).map i))
    (z : (schemeStack.{u, w} B S hS U).val.val.obj) : P z := by
  have hinh : ∀ {a b : (schemeStack.{u, w} B S hS U).val.val.obj}, (a ⟶ b) → P b → P a :=
    fun φ hb => hP.prop_of_hom φ hb
  let y0 : (schemeStack.{u, w} B S hS U).val.val.p.Fiber U := ⟨Over.mk (𝟙 U), rfl⟩
  let G := objSubfunctor hinh y0
  have hG := isClosedSubspace_objSubfunctor hinh hP y0
  -- membership of an arrow `t : T ⟶ U` in `G` is `P` at the object `t`
  have hmem : ∀ {T : BigFppfOver B S hS} (t : T ⟶ U), t ∈ G.obj (op T) ↔ P (Over.mk t) := by
    intro T t
    let α : (Over.mk t : Over U) ⟶ Over.mk (𝟙 U) := Over.homMk t (Category.comp_id _)
    have : (schemeStack.{u, w} B S hS U).val.val.p.IsHomLift t α :=
      (inferInstance : (Over.forget U).IsHomLift ((Over.forget U).map α) α)
    exact mem_objSubfunctor_iff hinh y0 t α
  -- the closed subscheme representing `G`
  have hrep := hG.2.rep
  set W := hrep.pullback (𝟙 (yoneda.obj U))
  set i : W ⟶ U := hrep.snd (𝟙 (yoneda.obj U))
  have hi : _root_.AlgebraicGeometry.IsClosedImmersion ((BigFppfOver.toScheme B S hS).map i) :=
    hG.2.property_snd (𝟙 (yoneda.obj U))
  have hpb := hrep.isPullback (𝟙 (yoneda.obj U))
  -- `γ` factors through `W`
  obtain ⟨h, hh⟩ : ∃ h : V ⟶ W, h ≫ i = γ := by
    let c : yoneda.obj V ⟶ G.toFunctor := yonedaEquiv.symm ⟨γ, (hmem γ).2 hγ⟩
    have hc : c ≫ G.ι = yoneda.map γ := by
      ext T t
      rfl
    let l := hpb.lift c (yoneda.map γ) (by rw [hc, Category.comp_id])
    refine ⟨Yoneda.fullyFaithful.preimage l, Yoneda.fullyFaithful.map_injective ?_⟩
    rw [Functor.map_comp, Functor.FullyFaithful.map_preimage]
    exact hpb.lift_snd _ _ _
  have hI : IsIso ((BigFppfOver.toScheme B S hS).map i) := hiso i hi h hh
  have hI' : IsIso i := isIso_of_reflects_iso i (BigFppfOver.toScheme B S hS)
  -- so every arrow into `U` lies in `G`
  have hall : ∀ {T : BigFppfOver B S hS} (t : T ⟶ U), t ∈ G.obj (op T) := by
    intro T t
    have hw := congrArg (fun φ => φ.app (op T) (t ≫ inv i)) hpb.w
    simp only [FunctorToTypes.comp, Category.comp_id] at hw
    have : t = G.ι.app (op T) (hrep.fst (𝟙 (yoneda.obj U)) |>.app (op T) (t ≫ inv i)) := by
      rw [hw]
      simp
    rw [this]
    exact Subtype.property _
  obtain ⟨z, rfl⟩ : ∃ z' : Over U, z' = z := ⟨z, rfl⟩
  exact (hmem z.hom).1 (hall z.hom)

/-- **The inclusion of a substack holding at every object is smooth**: it is an equivalence of
categories over the site, with quasi-inverse the corestriction of the identity. -/
theorem isSmooth_fullSubcategoryInclusion_of_forall (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {P : ObjectProperty 𝒳.val.val.obj}
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) (hall : ∀ z, P z) :
    AlgebraicStacks.IsSmooth B S hS (fullSubcategoryInclusion 𝒳 P hA) := by
  let s : 𝒳.val ⟶ (fullSubcategoryAlgebraicStack 𝒳 P hA).val :=
    Bicategory.InducedBicategory.mkHom ⟨P.lift (𝟭 _) hall, rfl⟩
  have hι : (P.ι : P.FullSubcategory ⥤ 𝒳.val.val.obj).IsEquivalence :=
    { essSurj := ⟨fun z => ⟨⟨z, hall z⟩, ⟨Iso.refl _⟩⟩⟩ }
  have hs : (CatFiberedInGroupoids.homFunctor s).IsEquivalence := by
    have : (P.lift (𝟭 _) hall ⋙ P.ι).IsEquivalence :=
      Functor.isEquivalence_of_iso (P.liftCompιIso (𝟭 _) hall).symm
    exact Functor.isEquivalence_of_comp_right (P.lift (𝟭 _) hall) P.ι
  exact hasPropertyOnSomeSmoothDiagram_of_isEquivalence B S hS _
    (fullSubcategoryInclusion 𝒳 P hA).hom (𝟙 𝒳.val) s hs (Iso.refl _)
    (AlgebraicStacks.isSmooth_id B S hS 𝒳)

/-- **A closed substack holding at every object has the dimension of the ambient stack at every
point.** -/
theorem dimensionAtPoint_fullSubcategory_eq_of_forall (𝒳 : AlgebraicStacks.{u, w} B S hS)
    {P : ObjectProperty 𝒳.val.val.obj} (hP : IsClosedSubstack 𝒳 P)
    (hA : IsAlgebraicStack.{u, w} B S hS (fullSubcategoryBased 𝒳 P)) (hall : ∀ z, P z)
    (h𝒳 : IsLocallyNoetherianStack.{u, w} B S hS 𝒳)
    (z : points B S hS (fullSubcategoryAlgebraicStack 𝒳 P hA).val.val
      (fullSubcategoryAlgebraicStack 𝒳 P hA).val.property) :
    dimensionAtPoint B S hS (fullSubcategoryAlgebraicStack 𝒳 P hA)
        (isLocallyNoetherianStack_of_isClosedSubstack B S hS 𝒳 P hP hA h𝒳) z =
      dimensionAtPoint B S hS 𝒳 h𝒳 (pointsMap B S hS _ _ 𝒳.val.property
        (fullSubcategoryInclusion 𝒳 P hA).hom.hom z) :=
  dimensionAtPoint_eq_of_isMonomorphism_of_isSmooth B S hS _
    (AlgebraicStacks.isMonomorphism_of_isImmersion B S hS _
      (AlgebraicStacks.isImmersion_of_isClosedImmersion B S hS _ hP.2.choose_spec))
    (isSmooth_fullSubcategoryInclusion_of_forall 𝒳 hA hall) _ h𝒳 z

end AlgebraicGeometry.Stack

end
