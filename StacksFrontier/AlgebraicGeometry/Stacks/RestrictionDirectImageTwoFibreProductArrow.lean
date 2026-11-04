module

public import StacksFrontier.AlgebraicGeometry.Stacks.RestrictionDirectImageLeftEqualizer

/-!
# The objects of the 2-fibre product of equation 075M as pairs

Equation 075M computes the sections of `(f_*ℱ)|_{G_étale}` over an étale scheme chart `V` of `G`
as the global sections of the pullback of `ℱ` to the 2-fibre product `(Sch/V)_{fppf} ×_𝒴 𝒳`
(`AlgebraicGeometry.Space.restrictedDirectImageChartEquiv`, Stacks 06W6), the component of such a
global section at an object `P` being the value of the section at the pair
`(P.y, P.iso.inv ≫ c.map P.x.hom y)` — an object of `𝒳` together with a morphism of `𝒴` from its
image into `u_G V`.

This file is the dictionary between the objects and morphisms of that 2-fibre product and those
pairs. It says that the 2-fibre product *is* the category of such pairs: every pair is the pair
of an object (`AlgebraicGeometry.Space.twoFibreProductMk`), and a morphism into the object of a
pair is the same thing as a morphism of `𝒳` compatible with the two arrows into `u_G V`
(`AlgebraicGeometry.Space.twoFibreProductArrow_comp`).

With the dictionary, a global section of the pullback of `ℱ` to the 2-fibre product is the same
thing as a family of sections indexed by the pairs and compatible with the morphisms of `𝒴`, a
statement in which no 2-fibre product occurs.

## Main definitions

* `AlgebraicGeometry.Space.twoFibreProductArrow`: the morphism `f(P.y) ⟶ u_G V` attached to an
  object of the 2-fibre product; this is the arrow at which Stacks 06W6 reads the component of a
  global section.
* `AlgebraicGeometry.Space.twoFibreProductMk`: the object of the 2-fibre product attached to an
  object `Z` of `𝒳` and a morphism `κ : f(Z) ⟶ u_G V`.

## Main results

* `AlgebraicGeometry.Space.twoFibreProductArrow_comp`: a morphism of the 2-fibre product is
  compatible with the comparison arrows of its source and target.
* `AlgebraicGeometry.Space.twoFibreProductMk_y` and
  `AlgebraicGeometry.Space.twoFibreProductArrow_twoFibreProductMk`: the pair of
  `twoFibreProductMk Z κ` is `(Z, κ)`.

## References

* [Stacks Project, Tag 075M](https://stacks.math.columbia.edu/tag/075M)
* [Stacks Project, Tag 06W6](https://stacks.math.columbia.edu/tag/06W6)
* [Stacks Project, Tag 02XN](https://stacks.math.columbia.edu/tag/02XN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Space

-- The instance arguments of `CategoryTheory.Functor.IsHomLift` and of
-- `CategoryTheory.Functor.IsStronglyCartesian` are only found after unfolding the inclusion of a
-- fibre into the ambient category, `CategoryTheory.Functor.Fiber` being a plain `def` for a
-- subtype; this is the same local attribute
-- `StacksFrontier/CategoryTheory/FiberedCategory/ChoiceOfPullbacks.lean` sets for the same reason.
attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion

universe u v w v' w'

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hq : q.IsFiberedInGroupoids)
  (eG : StacksRepresentableCFG.EquivalenceOver q
    (presheafOfCategories (G ⋙ typeToCat)).p)
  (f : 𝒳 ⥤ 𝒴) (hf : p.IsFibredOneMorphism q f) (c : q.ChoiceOfPullbacks)
  (V : SmallEtale B S hS G)

/-- The comparison arrow of an object of the 2-fibre product `(Sch/V)_{fppf} ×_𝒴 𝒳` of
equation 075M: the comparison isomorphism of the object followed by the chosen cartesian lift of
its structure morphism.

This is the morphism of `𝒴` at which the pushforward formula of Stacks 06W6,
`CategoryTheory.Presheaf.pushforwardSectionsEquiv_apply`, reads the component of a global
section at that object. -/
noncomputable def twoFibreProductArrow
    (P : TwoFibreProductOver (Over.forget ((SmallEtale.toOver B S hS G).obj V)) p q
      (c.sliceFunctor (chartFiberObj B S hS G q eG V)) f) :
    f.obj P.y ⟶ (restrictionFunctor B S hS G q eG).obj V :=
  P.iso.inv ≫ c.map P.x.hom (chartFiberObj B S hS G q eG V)

/-- **A morphism of the 2-fibre product is compatible with the comparison arrows.** The morphism
of `𝒳` underlying it carries the comparison arrow of the target to that of the source.

This is the square of the morphism of the 2-fibre product together with the defining
factorization of the transition maps of
`CategoryTheory.Functor.ChoiceOfPullbacks.sliceFunctor`. -/
theorem twoFibreProductArrow_comp
    {P Q : TwoFibreProductOver (Over.forget ((SmallEtale.toOver B S hS G).obj V)) p q
      (c.sliceFunctor (chartFiberObj B S hS G q eG V)) f} (u : P ⟶ Q) :
    f.map u.b ≫ twoFibreProductArrow B S hS G p q eG f c V Q =
      twoFibreProductArrow B S hS G p q eG f c V P := by
  have hb : f.map u.b =
      P.iso.inv ≫ (c.sliceFunctor (chartFiberObj B S hS G q eG V)).map u.a ≫ Q.iso.hom := by
    rw [u.w, ← Category.assoc, P.iso.inv_hom_id, Category.id_comp]
  show f.map u.b ≫ Q.iso.inv ≫ c.map Q.x.hom (chartFiberObj B S hS G q eG V) =
    P.iso.inv ≫ c.map P.x.hom (chartFiberObj B S hS G q eG V)
  rw [hb]
  simp only [Category.assoc]
  refine congrArg (fun m ↦ P.iso.inv ≫ m) ?_
  refine Eq.trans (congrArg (fun m ↦
    (c.sliceFunctor (chartFiberObj B S hS G q eG V)).map u.a ≫ m)
      (Q.iso.hom_inv_id_assoc (c.map Q.x.hom (chartFiberObj B S hS G q eG V)))) ?_
  exact Functor.ChoiceOfPullbacks.sliceFunctor_map_fac c
    (chartFiberObj B S hS G q eG V) u.a

/-! ### The object attached to a pair -/

include hf in
/-- The object of the big fppf site of `S` over which an object of `𝒳` lies, read through the
verticality of the 1-morphism `f`. -/
theorem obj_eq_obj_map (Z : 𝒳) : p.obj Z = q.obj (f.obj Z) :=
  (Functor.congr_obj hf.comp_eq Z).symm

include hf in
/-- The first factor of the object of the 2-fibre product of equation 075M attached to an object
`Z` of `𝒳` and a morphism `κ : f(Z) ⟶ u_G V` of `𝒴`: the scheme underlying `Z`, over the scheme
of the chart `V` through the image of `κ` in the big fppf site of `S`. -/
noncomputable def twoFibreProductMkOver (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    Over ((SmallEtale.toOver B S hS G).obj V) :=
  Over.mk (eqToHom (obj_eq_obj_map B S hS p q f hf Z) ≫ q.map κ ≫
    eqToHom (chartFiberObj B S hS G q eG V).2)

include hf in
/-- The morphism of `𝒴` of a pair lies over the structure morphism of the first factor the pair
induces. -/
theorem isHomLift_twoFibreProductMkOver_hom (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    q.IsHomLift (twoFibreProductMkOver B S hS G p q eG f hf V Z κ).hom κ :=
  CategoryTheory.IsHomLift.of_fac q _ κ
    (obj_eq_obj_map B S hS p q f hf Z).symm (chartFiberObj B S hS G q eG V).2 rfl

include hf in
/-- The comparison morphism of the object of the 2-fibre product attached to a pair: the unique
vertical morphism through which the morphism of `𝒴` of the pair factors the chosen cartesian
lift. -/
noncomputable def twoFibreProductMkLift (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    f.obj Z ⟶ (c.sliceFunctor (chartFiberObj B S hS G q eG V)).obj
      (twoFibreProductMkOver B S hS G p q eG f hf V Z κ) :=
  @CategoryTheory.Functor.IsStronglyCartesian.map _ _ _ _ q _ _ _ _
    (twoFibreProductMkOver B S hS G p q eG f hf V Z κ).hom
    (c.map (twoFibreProductMkOver B S hS G p q eG f hf V Z κ).hom
      (chartFiberObj B S hS G q eG V))
    (c.isStronglyCartesian _ _) _ _ _ _
    (Category.id_comp (twoFibreProductMkOver B S hS G p q eG f hf V Z κ).hom).symm κ
    (isHomLift_twoFibreProductMkOver_hom B S hS G p q eG f hf V Z κ)

include hf in
/-- The comparison morphism of a pair is vertical. -/
theorem isHomLift_twoFibreProductMkLift (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    q.IsHomLift (𝟙 (p.obj Z)) (twoFibreProductMkLift B S hS G p q eG f hf c V Z κ) :=
  @CategoryTheory.Functor.IsStronglyCartesian.map_isHomLift _ _ _ _ q _ _ _ _ _
    (c.map _ (chartFiberObj B S hS G q eG V)) (c.isStronglyCartesian _ _) _ _ _ _
    (Category.id_comp _).symm κ (isHomLift_twoFibreProductMkOver_hom B S hS G p q eG f hf V Z κ)

include hf in
/-- The comparison morphism of a pair factors the chosen cartesian lift through the morphism of
`𝒴` of the pair. -/
theorem twoFibreProductMkLift_fac (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    twoFibreProductMkLift B S hS G p q eG f hf c V Z κ ≫
        c.map (twoFibreProductMkOver B S hS G p q eG f hf V Z κ).hom
          (chartFiberObj B S hS G q eG V) = κ :=
  @CategoryTheory.Functor.IsStronglyCartesian.fac _ _ _ _ q _ _ _ _ _
    (c.map _ (chartFiberObj B S hS G q eG V)) (c.isStronglyCartesian _ _) _ _ _ _
    (Category.id_comp _).symm κ (isHomLift_twoFibreProductMkOver_hom B S hS G p q eG f hf V Z κ)

include hq hf in
/-- The comparison morphism of a pair is an isomorphism: it is a vertical morphism of a category
fibred in groupoids. -/
theorem isIso_twoFibreProductMkLift (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    IsIso (twoFibreProductMkLift B S hS G p q eG f hf c V Z κ) := by
  have := isHomLift_twoFibreProductMkLift B S hS G p q eG f hf c V Z κ
  have := CategoryTheory.Functor.isStronglyCartesian_of_isFiberedInGroupoids hq
    (𝟙 (p.obj Z)) (twoFibreProductMkLift B S hS G p q eG f hf c V Z κ)
    (isHomLift_twoFibreProductMkLift B S hS G p q eG f hf c V Z κ)
  exact CategoryTheory.Functor.IsStronglyCartesian.isIso_of_base_isIso q
    (𝟙 (p.obj Z)) (twoFibreProductMkLift B S hS G p q eG f hf c V Z κ)

include hq hf in
/-- **The object of the 2-fibre product of equation 075M attached to a pair** consisting of an
object `Z` of `𝒳` and a morphism `κ : f(Z) ⟶ u_G V` of `𝒴`.

Its first factor is the scheme of `Z` over the scheme of `V` through `κ`, its second factor is
`Z`, and its comparison isomorphism is the unique vertical morphism factoring `κ` through the
chosen cartesian lift — an isomorphism because `𝒴` is fibred in groupoids. -/
noncomputable def twoFibreProductMk (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    TwoFibreProductOver (Over.forget ((SmallEtale.toOver B S hS G).obj V)) p q
      (c.sliceFunctor (chartFiberObj B S hS G q eG V)) f where
  base := p.obj Z
  x := twoFibreProductMkOver B S hS G p q eG f hf V Z κ
  y := Z
  hx := rfl
  hy := rfl
  iso :=
    haveI := isIso_twoFibreProductMkLift B S hS G p q hq eG f hf c V Z κ
    (asIso (twoFibreProductMkLift B S hS G p q eG f hf c V Z κ)).symm
  vertical := by
    have := isIso_twoFibreProductMkLift B S hS G p q hq eG f hf c V Z κ
    have : q.IsHomLift (𝟙 (p.obj Z))
        (asIso (twoFibreProductMkLift B S hS G p q eG f hf c V Z κ)).hom :=
      isHomLift_twoFibreProductMkLift B S hS G p q eG f hf c V Z κ
    exact CategoryTheory.IsHomLift.lift_id_inv q (p.obj Z)
      (asIso (twoFibreProductMkLift B S hS G p q eG f hf c V Z κ))

include hq hf in
/-- The second factor of the object attached to a pair `(Z, κ)` is `Z`. -/
@[simp] theorem twoFibreProductMk_y (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    (twoFibreProductMk B S hS G p q hq eG f hf c V Z κ).y = Z :=
  rfl

include hq hf in
/-- **The comparison arrow of the object attached to a pair is the morphism of the pair.** -/
theorem twoFibreProductArrow_twoFibreProductMk (Z : 𝒳)
    (κ : f.obj Z ⟶ (restrictionFunctor B S hS G q eG).obj V) :
    twoFibreProductArrow B S hS G p q eG f c V
        (twoFibreProductMk B S hS G p q hq eG f hf c V Z κ) = κ :=
  twoFibreProductMkLift_fac B S hS G p q eG f hf c V Z κ

end AlgebraicGeometry.Space

end
