module

public import StacksFrontier.AlgebraicGeometry.Stacks.DiagonalPointFibre

/-!
# The fibres of the diagonal, as categories over the base

`StacksFrontier.AlgebraicGeometry.Stacks.DiagonalPointFibre` studies the 2-fibre product

`𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳`

of the proof of Stacks 07Y5 through its projection to `(Sch/V)_{fppf}`. The axioms of the
proof (Stacks 05UI, 07WR, 07XM, 07X9, …) are stated for `𝒴` through its structure functor to
`(Sch/S)_{fppf}`, and Proposition 07Y1 is applied to the functor of isomorphism classes of `𝒴`
as a category over `(Sch/S)_{fppf}`. This file shows that `𝒴` is fibred in setoids over
`(Sch/S)_{fppf}` too, and that this functor of isomorphism classes, `Y`, takes `u`-small values,
so that it has a `Type u` model.

## Main definitions

* `AlgebraicGeometry.Stack.diagonalPointFibreOverBase`: the structure functor
  `𝒴 ⥤ (Sch/S)_{fppf}`.
* `AlgebraicGeometry.Stack.diagonalPointFunctorOverBase`: the functor `Y` of the proof of
  Stacks 07Y5, valued in `Type u`.
* `AlgebraicGeometry.Stack.diagonalPointFibreOverBaseEquivalenceOver`: the equivalence over
  `(Sch/S)_{fppf}` of `𝒴` with the category fibred in sets attached to `Y`.

## Main results

* `AlgebraicGeometry.Stack.diagonalPointFibreOverBase_isFiberedInSetoids`.
* `AlgebraicGeometry.Stack.small_isoClassPresheaf_diagonalPointFibreOverBase`: an object of `𝒴`
  over `T` is a morphism `t : T ⟶ V` together with an object `x` of `𝒳` over `T` and an
  isomorphism `(x, x) ≅ y|_t`; its class is determined by `t` and by the twist `y₁|_t ≅ y₂|_t`.

## References

* [Stacks Project, Tag 07Y5](https://stacks.math.columbia.edu/tag/07Y5)
-/

@[expose] public section

open CategoryTheory

namespace CategoryTheory.TwoFibreProductOver.DiagonalPoint

universe v₁ v₂ v₃ u₁ u₂ u₃

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞] {𝒯 : Type u₂} [Category.{v₂} 𝒯]
  {𝒮 : Type u₃} [Category.{v₃} 𝒮]
  {pT : 𝒯 ⥤ 𝒞} {p : 𝒮 ⥤ 𝒞} {y : 𝒯 ⥤ TwoFibreProductOver p p (𝟭 𝒞) p p}

attribute [local instance_reducible] diagonal

/-- If `pT` is faithful, every fibre of the structure functor of `𝒯 ×_{y, 𝒮 × 𝒮, Δ} 𝒮` is thin. -/
lemma structureFunctor_fiber_isThin [pT.Faithful] (c : 𝒞) :
    Quiver.IsThin ((structureFunctor pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).Fiber c) := by
  have := faithful_diagonal (Functor.comp_id p)
  refine fun P Q => ⟨fun f g => Functor.Fiber.hom_ext ?_⟩
  refine hom_ext_of_faithful ?_
  have hf : (structureFunctor pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).IsHomLift (𝟙 c) (Functor.Fiber.fiberInclusion.map f) := f.2
  have hg : (structureFunctor pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).IsHomLift (𝟙 c) (Functor.Fiber.fiberInclusion.map g) := g.2
  have ha := isHomLift_a_of_isHomLift (𝟙 c) (Functor.Fiber.fiberInclusion.map f)
  have hb := isHomLift_a_of_isHomLift (𝟙 c) (Functor.Fiber.fiberInclusion.map g)
  apply pT.map_injective
  rw [IsHomLift.fac' pT (𝟙 c) (Functor.Fiber.fiberInclusion.map f).a,
    IsHomLift.fac' pT (𝟙 c) (Functor.Fiber.fiberInclusion.map g).a]

/-- The class of an object of a fibre of the structure functor of `𝒯 ×_{y, 𝒮 × 𝒮, Δ} 𝒮`: its
`𝒯`-component together with its twist. -/
def structureTwist {c : 𝒞}
    (P : (structureFunctor pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).Fiber c) :
    Σ t : {t : 𝒯 // pT.obj t = c}, ((y.obj t.1).x ⟶ (y.obj t.1).y) :=
  ⟨⟨P.1.x, P.1.hx.trans P.2⟩, twist P.1⟩

/-- Two objects of a fibre of the structure functor of `𝒯 ×_{y, 𝒮 × 𝒮, Δ} 𝒮` with the same
`𝒯`-component and the same twist are isomorphic. -/
lemma nonempty_iso_of_structureTwist_eq [pT.Faithful] {c : 𝒞}
    (P Q : (structureFunctor pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).Fiber c)
    (h : structureTwist P = structureTwist Q) : Nonempty (P ≅ Q) := by
  have hthin := structureFunctor_fiber_isThin (pT := pT) (p := p) (y := y) c
  suffices H : ∀ (P Q : (structureFunctor pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).Fiber c),
      structureTwist P = structureTwist Q → Nonempty (P ⟶ Q) by
    obtain ⟨f⟩ := H P Q h
    obtain ⟨g⟩ := H Q P h.symm
    exact ⟨⟨f, g, (hthin _ _).allEq _ _, (hthin _ _).allEq _ _⟩⟩
  rintro ⟨⟨bP, xP, sP, hxP, hsP, iP, vP⟩, hP⟩ ⟨⟨bQ, xQ, sQ, hxQ, hsQ, iQ, vQ⟩, hQ⟩ hPQ
  change bP = c at hP
  change bQ = c at hQ
  subst hP hQ
  obtain ⟨h₁, h₂⟩ := Sigma.mk.inj_iff.1 hPQ
  have hx : xP = xQ := congrArg Subtype.val h₁
  subst hx
  subst hxP
  have h₃ : iP.hom.a ≫ iP.inv.b = iQ.hom.a ≫ iQ.inv.b := eq_of_heq h₂
  obtain ⟨φ, -, hφ⟩ := exists_hom_of_twist_eq xP sP sQ hsP.symm hsQ.symm iP iQ vP vQ h₃
  have : (structureFunctor pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).IsHomLift (𝟙 (pT.obj xP)) φ := by
    have h₄ : (structureFunctor pT p (structureFunctor p p (𝟭 𝒞) p p) y
        (diagonal (Functor.comp_id p))).map φ = 𝟙 (pT.obj xP) := hφ
    rw [← h₄]
    exact IsHomLift.map _ φ
  exact ⟨Functor.Fiber.homMk _ _ φ⟩

/-- The presheaf of isomorphism classes of the structure functor of `𝒯 ×_{y, 𝒮 × 𝒮, Δ} 𝒮` is
small for the universe of the morphisms of `𝒮`, as soon as `pT` is faithful and the objects of
`𝒯` over each object of `𝒞` form a small set. -/
lemma small_isoClassPresheaf_structureFunctor [pT.Faithful]
    (hT : ∀ c : 𝒞, Small.{v₃} {t : 𝒯 // pT.obj t = c})
    [hfib : (structureFunctor pT p (structureFunctor p p (𝟭 𝒞) p p) y
      (diagonal (Functor.comp_id p))).IsFibered] :
    FunctorToTypes.Small.{v₃}
      (structureFunctor pT p (structureFunctor p p (𝟭 𝒞) p p) y
        (diagonal (Functor.comp_id p))).isoClassPresheaf := by
  intro c
  have := hT c.unop
  refine small_of_injective
    (f := fun q : _root_.Quotient (isIsomorphicSetoid
      ((structureFunctor pT p (structureFunctor p p (𝟭 𝒞) p p) y
        (diagonal (Functor.comp_id p))).Fiber c.unop)) => structureTwist q.out) ?_
  intro q q' hq
  rw [← _root_.Quotient.out_eq q, ← _root_.Quotient.out_eq q']
  exact Functor.isoClassMk_eq_of_iso (nonempty_iso_of_structureTwist_eq _ _ hq).some

end CategoryTheory.TwoFibreProductOver.DiagonalPoint

namespace AlgebraicGeometry.Stack

universe u

/-- The slice functor `Over.map f` is faithful. -/
lemma faithful_sliceMap {C : Type*} [Category C] {X Y : C} (f : X ⟶ Y) : (Over.map f).Faithful where
  map_injective {_ _} g g' h := by
    ext
    simpa using congrArg CommaMorphism.left h

/-- The objects of a slice over `X` lying over a given object of the slice over `Y` form a set
of the size of the morphisms of the ambient category. -/
lemma small_overMap_fiber {C : Type*} [Category.{u} C] {X Y : C} (f : X ⟶ Y) (c : Over Y) :
    Small.{u} {t : Over X // (Over.map f).obj t = c} := by
  refine small_of_injective
    (f := fun t => eqToHom (congrArg Comma.left t.2).symm ≫ t.1.hom) ?_
  rintro ⟨⟨tl, ⟨⟩, th⟩, ht⟩ ⟨⟨tl', ⟨⟩, th'⟩, ht'⟩ h
  obtain rfl : tl = c.left := congrArg Comma.left ht
  obtain rfl : tl' = c.left := congrArg Comma.left ht'
  simp only [eqToHom_refl, Category.id_comp] at h
  subst h
  rfl

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
  (V : BigFppfOver B S hS)
  (y : BigFppfOver B V.left.1 V.left.2 ⥤ (CatFiberedInGroupoids.product 𝒳 𝒳).val.obj)

/-- The 2-fibre product `𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` of the proof of Stacks 07Y5, as a
category over `(Sch/S)_{fppf}` through its structure functor. -/
abbrev diagonalPointFibreOverBase :
    TwoFibreProductOver (Over.map V.hom) 𝒳.val.p (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y
        (diagonalBasedFunctor B S hS 𝒳).toFunctor ⥤ BigFppfOver B S hS :=
  TwoFibreProductOver.structureFunctor (Over.map V.hom) 𝒳.val.p
    (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y (diagonalBasedFunctor B S hS 𝒳).toFunctor

/-- The structure functor of `𝒴` is the projection to `(Sch/V)_{fppf}` followed by
`Over.map V.hom`. -/
lemma diagonalPointFibre_comp_overMap :
    diagonalPointFibre B S hS 𝒳 V y ⋙ Over.map V.hom = diagonalPointFibreOverBase B S hS 𝒳 V y :=
  TwoFibreProductOver.fst_comp_eq

variable {B S hS 𝒳 V y}
variable (hy : y ⋙ (CatFiberedInGroupoids.product 𝒳 𝒳).val.p = Over.map V.hom)

include hy in
/-- `𝒴` is fibred in groupoids over `(Sch/S)_{fppf}`. -/
theorem diagonalPointFibreOverBase_isFiberedInGroupoids :
    (diagonalPointFibreOverBase B S hS 𝒳 V y).IsFiberedInGroupoids :=
  TwoFibreProductOver.isFiberedInGroupoids (Over.map V.hom) 𝒳.val.p
    (CatFiberedInGroupoids.product 𝒳 𝒳).val.p y (diagonalBasedFunctor B S hS 𝒳).toFunctor
    (Functor.IsFiberedInGroupoids.over_map V.hom) 𝒳.isFiberedInGroupoids
    (CatFiberedInGroupoids.product 𝒳 𝒳).isFiberedInGroupoids hy
    (diagonalBasedFunctor B S hS 𝒳).w

include hy in
/-- **`𝒴` is fibred in setoids** over `(Sch/S)_{fppf}`. -/
theorem diagonalPointFibreOverBase_isFiberedInSetoids :
    (diagonalPointFibreOverBase B S hS 𝒳 V y).IsFiberedInSetoids :=
  have := faithful_sliceMap V.hom
  ⟨diagonalPointFibreOverBase_isFiberedInGroupoids hy,
    fun T => TwoFibreProductOver.DiagonalPoint.structureFunctor_fiber_isThin T⟩

include hy in
/-- The presheaf of isomorphism classes of `𝒴` over `(Sch/S)_{fppf}` is `u`-small. -/
theorem small_isoClassPresheaf_diagonalPointFibreOverBase :
    letI := (diagonalPointFibreOverBase_isFiberedInGroupoids hy).isFibered
    FunctorToTypes.Small.{u} (diagonalPointFibreOverBase B S hS 𝒳 V y).isoClassPresheaf :=
  have := faithful_sliceMap V.hom
  TwoFibreProductOver.DiagonalPoint.small_isoClassPresheaf_structureFunctor
    (fun c => small_overMap_fiber V.hom c)
    (hfib := (diagonalPointFibreOverBase_isFiberedInGroupoids hy).isFibered)

/-- **The functor `Y` of the proof of Stacks 07Y5**: the presheaf of isomorphism classes of
`𝒴 = (Sch/V)_{fppf} ×_{y, 𝒳 × 𝒳, Δ} 𝒳` on `(Sch/S)_{fppf}`, in its `Type u` model. -/
noncomputable def diagonalPointFunctorOverBase : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u :=
  letI := (diagonalPointFibreOverBase_isFiberedInGroupoids hy).isFibered
  letI := small_isoClassPresheaf_diagonalPointFibreOverBase hy
  Functor.isoClassPresheafModel.{u} (diagonalPointFibreOverBase B S hS 𝒳 V y)

/-- The equivalence over `(Sch/S)_{fppf}` of `𝒴` with the category fibred in sets attached to
its functor `Y` of isomorphism classes. -/
noncomputable def diagonalPointFibreOverBaseEquivalenceOver :
    StacksRepresentableCFG.EquivalenceOver (diagonalPointFibreOverBase B S hS 𝒳 V y)
      (presheafOfCategories (diagonalPointFunctorOverBase hy ⋙ typeToCat)).p :=
  letI := diagonalPointFibreOverBase_isFiberedInSetoids hy
  letI := (diagonalPointFibreOverBase_isFiberedInGroupoids hy).isFibered
  letI := small_isoClassPresheaf_diagonalPointFibreOverBase hy
  isoClassEquivalenceOverModel B S hS (diagonalPointFibreOverBase B S hS 𝒳 V y)

end AlgebraicGeometry.Stack

end
