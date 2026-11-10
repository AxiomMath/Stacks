module

public import StacksFrontier.CategoryTheory.DottedArrows.Defs
public import StacksFrontier.CategoryTheory.FiberedCategory.Inertia
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.Representability.SliceProduct
public import StacksFrontier.CategoryTheory.FiberedInGroupoids.TwoCategory
public import StacksFrontier.CategoryTheory.TwoYoneda.OverBase
public import StacksFrontier.CategoryTheory.FiberedCategory.IsoOver

/-!
# Dotted arrows out of a slice, from data at the unit object

Let `𝒞` be a category and let `𝒳`, `𝒴` be categories fibred in groupoids over `𝒞`. Consider a
2-commutative square

```text
  𝒞/U --x--> 𝒳
   |          |
   j          f
   v          v
  𝒞/V --y--> 𝒴
```

in the 2-category of categories fibred in groupoids over `𝒞`, whose left edge `j` is the
restriction functor along a morphism `r : U ⟶ V` of `𝒞`, with filling 2-morphism `γ`. A dotted
arrow for it is a 1-morphism `𝒞/V ⟶ 𝒳` together with two 2-morphisms pasting to `γ`.

This file shows that such a dotted arrow can be produced from data at the unit objects alone: a
1-morphism `a : 𝒞/V ⟶ 𝒳`, a morphism `x(1_U) ⟶ a(1_V)` of `𝒳` over `r` and a morphism
`y(1_V) ⟶ f(a(1_V))` of `𝒴` over `𝟙 V` through which `γ` factors at `1_U`. The diagonal may
equivalently be given as an object of the fibre of `𝒳` over `V`.

## Main definitions

* `CategoryTheory.CatFiberedInGroupoids.slice`: the slice `𝒞/U` as an object of the 2-category of
  categories fibred in groupoids over `𝒞`.

## Main results

* `CategoryTheory.CatFiberedInGroupoids.nonempty_dottedArrow_of_unitHom`: a dotted arrow from a
  1-morphism and a factorisation of `γ` at the unit object.
* `CategoryTheory.CatFiberedInGroupoids.nonempty_dottedArrow_of_fiberObj`: the same with the
  diagonal presented as an object of a fibre of `𝒳`.
* `CategoryTheory.CatFiberedInGroupoids.exists_whiskerLeft_of_unitHom`: a 2-endomorphism of
  `y ∘ j` is the left whiskering of one of `y` as soon as its value at the unit object is the
  pullback of an endomorphism of `y(1_V)` along the canonical arrow `j(1_U) ⟶ 1_V`.

## Implementation notes

The hypothesis on the left edge is `j.hom.toFunctor = Over.map r` rather than
`j = CategoryTheory.BasedFunctor.overMap r`; the two are identified by
`CategoryTheory.BasedCategory.BasedFunctor.ext'`.

`CategoryTheory.BasedCategory.ofFunctor` is made `implicit_reducible` locally so that the
underlying based category `𝒳.val` of an object of the 2-category is recognised as the based
category attached to its own structure functor.

## References

* [Stacks Project, Tag 004B](https://stacks.math.columbia.edu/tag/004B)
* [Stacks Project, Tag 0H18](https://stacks.math.columbia.edu/tag/0H18)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor.TwoYoneda

attribute [local implicit_reducible] CategoryTheory.BasedCategory.ofFunctor

namespace CategoryTheory.CatFiberedInGroupoids

universe v₁ u₁

variable {𝒞 : Type u₁} [Category.{v₁} 𝒞]

/-- The slice `𝒞/U`, with its forgetful functor, as an object of the 2-category of categories
fibred in groupoids over `𝒞`. -/
abbrev slice (U : 𝒞) : CatFiberedInGroupoids.{v₁, v₁, u₁, max u₁ v₁} 𝒞 :=
  CatFiberedInGroupoids.mk (BasedCategory.slice U) (Functor.IsFiberedInGroupoids.over_forget U)

variable {𝒳 𝒴 : CatFiberedInGroupoids.{v₁, v₁, u₁, max u₁ v₁} 𝒞} {U V : 𝒞} (r : U ⟶ V)
  {x : slice U ⟶ 𝒳} {j : slice U ⟶ slice V} {f : 𝒳 ⟶ 𝒴} {y : slice V ⟶ 𝒴}
  {γ : (j ≫ y) ⟶ (x ≫ f)}

/-- Let the left edge `j` of the square be the restriction along `r : U ⟶ V`. Given a 1-morphism
`a : 𝒞/V ⟶ 𝒳`, a morphism `m : x(1_U) ⟶ a(1_V)` of `𝒳` lying over `r` and a morphism
`b : y(1_V) ⟶ f(a(1_V))` of `𝒴` lying over `𝟙 V` such that `γ` factors through them at the unit
object of `𝒞/U`, the square has a dotted arrow with diagonal `a`. -/
theorem nonempty_dottedArrow_of_unitHom (hj : j.hom.toFunctor = Over.map r)
    (a : slice V ⟶ 𝒳)
    (m : x.hom.obj (Over.mk (𝟙 U)) ⟶ a.hom.obj (Over.mk (𝟙 V)))
    (hm : 𝒳.val.p.IsHomLift r m)
    (b : y.hom.obj (Over.mk (𝟙 V)) ⟶ f.hom.obj (a.hom.obj (Over.mk (𝟙 V))))
    (hb : 𝒴.val.p.IsHomLift (𝟙 V) b)
    (h : γ.hom.app (Over.mk (𝟙 U)) ≫ f.hom.map m =
      y.hom.map (Over.mkIdTerminal.from (j.hom.obj (Over.mk (𝟙 U)))) ≫ b) :
    Nonempty (DottedArrow x j f y γ) := by
  obtain rfl : j = Bicategory.InducedBicategory.mkHom (BasedFunctor.overMap r) :=
    Bicategory.InducedBicategory.hom_ext (BasedCategory.BasedFunctor.ext' hj)
  obtain ⟨α, β, he⟩ := Functor.TwoYoneda.exists_factorisation_of_unitHom
    𝒳.val.p 𝒴.val.p 𝒳.isFiberedInGroupoids 𝒴.isFiberedInGroupoids r f.hom γ.hom a.hom m hm b hb h
  refine ⟨{ a := a, α := ⟨α⟩, β := ⟨β⟩, compat := ?_ }⟩
  apply Bicategory.InducedBicategory.hom₂_ext
  apply BasedNatTrans.ext
  apply NatTrans.ext
  funext z
  change γ.hom.app z = β.app ((Over.map r).obj z) ≫ 𝟙 _ ≫ f.hom.map (α.app z)
  exact (he z).trans (congrArg (fun t => β.app ((Over.map r).obj z) ≫ t)
    (Category.id_comp (f.hom.map (α.app z))).symm)

/-- Let the left edge `j` of the square be the restriction along `r : U ⟶ V`. Given an object `Z`
of `𝒳` lying over `V`, a morphism `m : x(1_U) ⟶ Z` of `𝒳` lying over `r` and a morphism
`b : y(1_V) ⟶ f(Z)` of `𝒴` lying over `𝟙 V` such that `γ` factors through them at the unit object
of `𝒞/U`, the square has a dotted arrow. -/
theorem nonempty_dottedArrow_of_fiberObj (hj : j.hom.toFunctor = Over.map r)
    (Z : 𝒳.val.obj) (hZ : 𝒳.val.p.obj Z = V)
    (m : x.hom.obj (Over.mk (𝟙 U)) ⟶ Z) (hm : 𝒳.val.p.IsHomLift r m)
    (b : y.hom.obj (Over.mk (𝟙 V)) ⟶ f.hom.obj Z) (hb : 𝒴.val.p.IsHomLift (𝟙 V) b)
    (h : γ.hom.app (Over.mk (𝟙 U)) ≫ f.hom.map m =
      y.hom.map (Over.mkIdTerminal.from (j.hom.obj (Over.mk (𝟙 U)))) ≫ b) :
    Nonempty (DottedArrow x j f y γ) := by
  obtain ⟨A, c, hc⟩ := Functor.TwoYoneda.exists_basedFunctor_unitHom
    𝒳.val.p 𝒳.isFiberedInGroupoids Z hZ
  have hciso : IsIso c :=
    Functor.isIso_of_fiber_isGroupoid (𝒳.isFiberedInGroupoids.fiber_isGroupoid V) c hc
  have hcinv : 𝒳.val.p.IsHomLift (𝟙 V) (inv c) :=
    have := hc
    IsHomLift.lift_id_inv_isIso 𝒳.val.p V c
  have hmc : 𝒳.val.p.IsHomLift r (m ≫ inv c) :=
    have := hm
    IsHomLift.comp_lift_id_right 𝒳.val.p r m (inv c)
  have hfc : 𝒴.val.p.IsHomLift (𝟙 V) (f.hom.map (inv c)) :=
    have : (BasedCategory.ofFunctor 𝒳.val.p).p.IsHomLift (𝟙 V) (inv c) := hcinv
    f.hom.preserves_isHomLift _ _
  have hbc : 𝒴.val.p.IsHomLift (𝟙 V) (b ≫ f.hom.map (inv c)) :=
    have := hb
    IsHomLift.comp_lift_id_right 𝒴.val.p (𝟙 V) b (f.hom.map (inv c))
  refine nonempty_dottedArrow_of_unitHom r hj (Bicategory.InducedBicategory.mkHom A)
    (m ≫ inv c) hmc (b ≫ f.hom.map (inv c)) hbc ?_
  refine Eq.trans (congrArg (fun t => γ.hom.app (Over.mk (𝟙 U)) ≫ t)
    (f.hom.toFunctor.map_comp m (inv c))) ?_
  refine Eq.trans (Category.assoc _ _ _).symm ?_
  exact Eq.trans (congrArg (fun t => t ≫ f.hom.map (inv c)) h) (Category.assoc _ _ _)

/-- Let the left edge `j` of the square be the restriction along `r : U ⟶ V`, and let `m` be an
endomorphism of `y(1_V)` over `𝟙 V` whose pullback along the canonical arrow `j(1_U) ⟶ 1_V` is
the value of `ε` at the unit object of `𝒞/U`. Then `ε = j ◁ δ` for the 2-morphism `δ : y ⟶ y`
the 2-Yoneda lemma attaches to `m`. -/
theorem exists_whiskerLeft_of_unitHom (hj : j.hom.toFunctor = Over.map r)
    (ε : (j ≫ y) ⟶ (j ≫ y))
    (m : y.hom.obj (Over.mk (𝟙 V)) ⟶ y.hom.obj (Over.mk (𝟙 V)))
    (hm : 𝒴.val.p.IsHomLift (𝟙 V) m)
    (h : ε.hom.app (Over.mk (𝟙 U)) ≫
          y.hom.map (Over.mkIdTerminal.from (j.hom.obj (Over.mk (𝟙 U)))) =
        y.hom.map (Over.mkIdTerminal.from (j.hom.obj (Over.mk (𝟙 U)))) ≫ m) :
    ∃ δ : y ⟶ y, Bicategory.whiskerLeft j δ = ε := by
  have hp := 𝒴.isFiberedInGroupoids
  set δ := (homEquivBasedNatTrans y y).symm (Functor.TwoYoneda.homOfUnitHom 𝒴.val.p hp m hm)
  refine ⟨δ, ?_⟩
  apply Bicategory.InducedBicategory.hom₂_ext
  refine Functor.TwoYoneda.hom_ext_of_app_unit 𝒴.val.p hp _ _ ?_
  have hjo : j.hom.obj (Over.mk (𝟙 U)) = Functor.TwoYoneda.unitOver r := by
    rw [hj]
  have hcart : 𝒴.val.p.IsHomLift r
      (y.hom.map (Over.mkIdTerminal.from (j.hom.obj (Over.mk (𝟙 U))))) :=
    Functor.TwoYoneda.isHomLift_map_from_mkIdTerminal_of_eq 𝒴.val.p r _ hjo
  have hsc : 𝒴.val.p.IsStronglyCartesian r
      (y.hom.map (Over.mkIdTerminal.from (j.hom.obj (Over.mk (𝟙 U))))) :=
    have := hcart
    hp.isStronglyCartesian_homLift r _
  have key : ∀ ψ ψ' : y.hom.obj (j.hom.obj (Over.mk (𝟙 U))) ⟶
        y.hom.obj (j.hom.obj (Over.mk (𝟙 U))),
      𝒴.val.p.IsHomLift (𝟙 U) ψ → 𝒴.val.p.IsHomLift (𝟙 U) ψ' →
        ψ ≫ y.hom.map (Over.mkIdTerminal.from (j.hom.obj (Over.mk (𝟙 U)))) =
          ψ' ≫ y.hom.map (Over.mkIdTerminal.from (j.hom.obj (Over.mk (𝟙 U)))) → ψ = ψ' := by
    intro ψ ψ' hψ hψ' he
    have := hsc
    have := hψ
    have := hψ'
    exact Functor.IsStronglyCartesian.ext 𝒴.val.p r
      (y.hom.map (Over.mkIdTerminal.from (j.hom.obj (Over.mk (𝟙 U))))) (𝟙 U) he
  refine key _ _ ((Bicategory.whiskerLeft j δ).hom.isHomLift' (Over.mk (𝟙 U)))
    (ε.hom.isHomLift' (Over.mk (𝟙 U))) ?_
  exact (Functor.TwoYoneda.unitHomApp_fac 𝒴.val.p hp m hm
    (j.hom.obj (Over.mk (𝟙 U)))).trans h.symm

end CategoryTheory.CatFiberedInGroupoids

end
