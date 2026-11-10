module

public import StacksFrontier.AlgebraicGeometry.Stacks.SelfIntersectionGroupoid
public import StacksFrontier.CategoryTheory.FiberedCategory.Strictification

/-!
# The canonical 1-morphism to the stack

Let `S` be a scheme contained in a big fppf site `B`, let `𝒰` and `𝒳` be categories fibred in
groupoids over the big fppf site of `S`, let `f : 𝒰 ⟶ 𝒳` be a 1-morphism and let
`ℛ = 𝒰 ×_{f, 𝒳, f} 𝒰` be its self-intersection. Suppose `𝒰` and `ℛ` are represented by algebraic
spaces `U` and `R` over `S` through chosen equivalences `eU` and `eR` over the site, and that `𝒰`
is fibred in setoids, so that
`AlgebraicGeometry.Stack.SelfIntersection.selfIntersectionGroupoid` — the groupoid in algebraic
spaces of Stacks 04T4 (4) — is available.

Evaluating that groupoid at every object of the site gives a presheaf of groupoids, and its
Grothendieck construction is the *pointwise groupoid fibration*
`AlgebraicGeometry.Stack.SelfIntersection.pointwiseFibration`, whose stackification is the quotient
stack `[U/R]` of Stacks 044Q. This file builds the 1-morphism from that pointwise groupoid
fibration to `𝒳` of Stacks 04T4 (5), together with two facts about it: its composite with the
canonical inclusion of the object space is `f` up to a *vertical* 2-isomorphism, and it satisfies
the descent compatibility, equation (04TG) of the source.

## Main definitions

* `AlgebraicGeometry.Stack.SelfIntersection.pointwiseFibration`: the pointwise groupoid fibration
  of the self-intersection groupoid.
* `AlgebraicGeometry.Stack.SelfIntersection.pointwiseSection`: the section of the arrow space that
  a morphism of that fibration names.
* `AlgebraicGeometry.Stack.SelfIntersection.toStackOfPointwiseGroupoid`: the 1-morphism, over the
  big fppf site.
* `AlgebraicGeometry.Stack.SelfIntersection.representingComparisonIso`: the vertical isomorphism of
  `𝒳` comparing the image under `f` of the chosen representative of the section an object of `𝒰`
  names with the image under `f` of that object.
* `AlgebraicGeometry.Stack.SelfIntersection.extendsF`: the vertical 2-isomorphism identifying the
  composite of the 1-morphism with the canonical inclusion of the object space with `f`.
* `AlgebraicGeometry.Stack.SelfIntersection.transportFiberHom`: the transport of a morphism of a
  fibre of `𝒳` along a morphism of the site, through the canonical morphisms between the chosen
  representatives.
* `AlgebraicGeometry.Stack.SelfIntersection.descentArrow`: the arrow of the pointwise groupoid
  fibration that an arrow of the relation names.

## Main results

* `AlgebraicGeometry.Stack.SelfIntersection.toStackOfPointwiseGroupoidMap_eq`: any fibre morphism
  naming the right section, and any morphism of `𝒰` over the right morphism of the site, compute
  the 1-morphism on morphisms.
* `AlgebraicGeometry.Stack.SelfIntersection.arrowOfFiberHom_restrict`: the section attached to a
  morphism of a fibre of `𝒳` restricts to the section attached to the transported morphism.
* `AlgebraicGeometry.Stack.SelfIntersection.arrowOfFiberHom_id` and
  `AlgebraicGeometry.Stack.SelfIntersection.arrowOfFiberHom_eq_identity`: the section attached to
  an identity, and more generally to a vertical morphism of `𝒰` between the chosen representatives
  of one section, is the identity arrow of the groupoid.
* `AlgebraicGeometry.Stack.SelfIntersection.descent_compatible`: equation (04TG): the arrow of the
  pointwise groupoid fibration that an arrow `(x, y, α)` of the relation names is carried, after
  the vertical comparison with `f`, to the inverse of `α`.

## References

* [Stacks Project, Tag 02XV](https://stacks.math.columbia.edu/tag/02XV)
* [Stacks Project, Tag 043W](https://stacks.math.columbia.edu/tag/043W)
* [Stacks Project, Tag 044Q](https://stacks.math.columbia.edu/tag/044Q)
* [Stacks Project, Tag 044R](https://stacks.math.columbia.edu/tag/044R)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 04T4](https://stacks.math.columbia.edu/tag/04T4)
* [Stacks Project, Tag 06KB](https://stacks.math.columbia.edu/tag/06KB)
-/


@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack.SelfIntersection

universe u

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
variable {𝒰 𝒳 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS)}
variable {f : 𝒰.val ⥤ᵇ 𝒳.val}
variable {U R : AlgebraicSpaces B S hS}
variable
  (eU : StacksRepresentableCFG.EquivalenceOver
    𝒰.val.p (presheafOfCategories (U.obj ⋙ typeToCat)).p)
  (eR : StacksRepresentableCFG.EquivalenceOver
    (relation B S hS 𝒰 𝒳 f).val.p
    (presheafOfCategories (R.obj ⋙ typeToCat)).p)

/-! ### Restriction of the chosen representatives -/

/-- The canonical restriction morphism of the split fibration of the object space: over
`g : V ⟶ W` it carries the restricted section to the section. -/
def splitRestrict {V W : BigFppfOver B S hS} (g : V ⟶ W) (a : U.obj.obj (op W)) :
    (⟨V, Discrete.mk (U.obj.map g.op a)⟩ : (presheafOfCategories (U.obj ⋙ typeToCat)).obj) ⟶
      ⟨W, Discrete.mk a⟩ :=
  ⟨g, 𝟙 _⟩

/-- The canonical restriction morphism lies over the morphism of the site it restricts along. -/
theorem isHomLift_splitRestrict {V W : BigFppfOver B S hS} (g : V ⟶ W) (a : U.obj.obj (op W)) :
    (presheafOfCategories (U.obj ⋙ typeToCat)).p.IsHomLift g (splitRestrict (U := U) g a) :=
  CategoryTheory.IsHomLift.of_fac' _ g (splitRestrict (U := U) g a) rfl rfl
    ((Category.comp_id g).symm.trans (Category.id_comp _).symm)

/-- The morphism of `𝒰` between the chosen representatives of a section and of its restriction,
over the morphism of the site restricted along. -/
noncomputable def representingObjRestrict {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (a : U.obj.obj (op W)) :
    representingObj eU (U.obj.map g.op a) ⟶ representingObj eU a :=
  eU.inv.functor.map (splitRestrict g a)

/-- The comparison of chosen representatives lies over the morphism of the site. -/
theorem isHomLift_representingObjRestrict {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (a : U.obj.obj (op W)) :
    𝒰.val.p.IsHomLift g (representingObjRestrict eU g a) :=
  CategoryTheory.Functor.isHomLift_map_of_comp_eq' eU.inv.w g _ (isHomLift_splitRestrict g a)

/-- The image under `f` of the comparison of chosen representatives: the canonical morphism
`f (j⁻¹ (a|g)) ⟶ f (j⁻¹ a)` of the target. -/
noncomputable def fRestrict {V W : BigFppfOver B S hS} (g : V ⟶ W) (a : U.obj.obj (op W)) :
    f.toFunctor.obj (representingObj eU (U.obj.map g.op a)) ⟶
      f.toFunctor.obj (representingObj eU a) :=
  f.toFunctor.map (representingObjRestrict eU g a)

/-- The canonical morphism of the target lies over the morphism of the site. -/
theorem isHomLift_fRestrict {V W : BigFppfOver B S hS} (g : V ⟶ W) (a : U.obj.obj (op W)) :
    𝒳.val.p.IsHomLift g (fRestrict (f := f) eU g a) :=
  CategoryTheory.Functor.isHomLift_map_of_comp_eq' f.w g _
    (isHomLift_representingObjRestrict eU g a)

/-- The canonical morphism of the target is strongly cartesian. -/
theorem isStronglyCartesian_fRestrict {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (a : U.obj.obj (op W)) :
    𝒳.val.p.IsStronglyCartesian g (fRestrict (f := f) eU g a) :=
  have := isHomLift_fRestrict (f := f) eU g a
  𝒳.isFiberedInGroupoids.isStronglyCartesian_homLift g _

/-! ### Uniqueness of morphisms of the source, and the identity sections -/

/-- Two morphisms of the source over one morphism of the site, with the same endpoints, are
equal. -/
theorem sourceHom_unique (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {V W : BigFppfOver B S hS} (g : V ⟶ W) {x y : 𝒰.val.obj} (κ κ' : x ⟶ y)
    (h : 𝒰.val.p.IsHomLift g κ) (h' : 𝒰.val.p.IsHomLift g κ') : κ = κ' :=
  have : 𝒰.val.p.IsFibered := hsetU.isFiberedInGroupoids.isFibered
  CategoryTheory.Functor.hom_unique_of_fiber_isThin 𝒰.val.p g (hsetU.fiber_isThin V) κ κ' h h'

/-- The composition law of the underlying groupoid in presheaves is the composition law built
from the self-intersection. -/
theorem toGroupoidInFunctors_comp (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.comp =
      compositionLaw eU eR hsetU :=
  toGroupoidInFunctors_ofComposable_comp U R _ _ _ _

/-- Composition in the underlying groupoid in presheaves is the composition law, with the two
sections composed read through equalities. -/
theorem compositionLaw_app_compose (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (T : (BigFppfOver B S hS)ᵒᵖ) {A A' A₂ A₂' : R.obj.obj T} (hA : A = A₂) (hA' : A' = A₂')
    (h : (relationSourceMap eU eR).app T A = (relationTargetMap eU eR).app T A')
    (h₂ : (relationSourceMap eU eR).app T A₂ = (relationTargetMap eU eR).app T A₂') :
    (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.compose T A A' h =
      (compositionLaw eU eR hsetU).app T ⟨(A₂, A₂'), h₂⟩ := by
  subst hA
  subst hA'
  exact congrArg
    (fun c : Deformation.composableArrows U.obj R.obj
        (relationSourceMap eU eR) (relationTargetMap eU eR) ⟶ R.obj =>
      c.app T ⟨(A, A'), h⟩)
    (toGroupoidInFunctors_comp eU eR hsetU)

/-- The composition law on two sections attached to fibre morphisms, read through the attachment
of a section of the arrow space to a morphism of a fibre of the target. -/
theorem compositionLaw_app_arrowOfFiberHom (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {W : BigFppfOver B S hS} (x y z : U.obj.obj (op W))
    (g : (Functor.Fiber.mk (fObj_over (f := f) eU y) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU x))
    (fh : (Functor.Fiber.mk (fObj_over (f := f) eU z) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU y))
    (h : (relationSourceMap eU eR).app (op W) (arrowOfFiberHom eU eR y z fh) =
      (relationTargetMap eU eR).app (op W) (arrowOfFiberHom eU eR x y g)) :
    (compositionLaw eU eR hsetU).app (op W)
        ⟨(arrowOfFiberHom eU eR y z fh, arrowOfFiberHom eU eR x y g), h⟩ =
      arrowOfFiberHom eU eR x z (fh ≫ g) :=
  (compositionLaw_app_sectionOfObj eU eR hsetU (composableOfFiberHoms eU x y z g fh)).trans
    (sectionOfObj_composition_composableOfFiberHoms eU eR x y z g fh)

/-- The section attached to the identity fibre morphism is the identity arrow. -/
theorem arrowOfFiberHom_id (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {W : BigFppfOver B S hS} (a : U.obj.obj (op W)) :
    arrowOfFiberHom eU eR a a (𝟙 (Functor.Fiber.mk (fObj_over (f := f) eU a))) =
      (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.identity (op W) a := by
  have hs := relationSourceMap_arrowOfFiberHom eU eR a a
    (𝟙 (Functor.Fiber.mk (fObj_over (f := f) eU a)))
  have ht := relationTargetMap_arrowOfFiberHom eU eR a a
    (𝟙 (Functor.Fiber.mk (fObj_over (f := f) eU a)))
  let a' : (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.Evaluation (op W) := a
  let m : a' ⟶ a' :=
    ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv
      (op W) a' a').symm
      ⟨arrowOfFiberHom eU eR a a (𝟙 (Functor.Fiber.mk (fObj_over (f := f) eU a))), hs, ht⟩
  have hm : ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv
        (op W) a' a' m).1 =
      arrowOfFiberHom eU eR a a (𝟙 (Functor.Fiber.mk (fObj_over (f := f) eU a))) :=
    congrArg Subtype.val (Equiv.apply_symm_apply _ _)
  have hmm : m ≫ m = m := by
    refine ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv
      (op W) a' a').injective (Subtype.ext ?_)
    refine (Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp _ (op W) m m).trans ?_
    refine (compositionLaw_app_compose eU eR hsetU (op W) hm hm _ (hs.trans ht.symm)).trans ?_
    refine Eq.trans ?_ hm.symm
    exact (compositionLaw_app_arrowOfFiberHom eU eR hsetU a a a _ _ _).trans
      (congrArg (arrowOfFiberHom eU eR a a) (Category.id_comp _))
  exact hm.symm.trans (congrArg
    (fun k => ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv
      (op W) a' a' k).1) ((cancel_mono m).1 (hmm.trans (Category.id_comp m).symm)))

/-- A fibre morphism coming from a vertical morphism of the source between the chosen
representatives of one section attaches the identity arrow. -/
theorem arrowOfFiberHom_eq_identity (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {W : BigFppfOver B S hS} (a b : U.obj.obj (op W)) (hab : b = a)
    (ψ : representingObj eU b ⟶ representingObj eU a)
    (hψ : 𝒰.val.p.IsHomLift (𝟙 W) ψ)
    (θ : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a))
    (hθ : Functor.Fiber.fiberInclusion.map θ = f.toFunctor.map ψ) :
    arrowOfFiberHom eU eR a b θ =
      (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.identity (op W) a := by
  subst hab
  have hψid : ψ = 𝟙 (representingObj eU b) :=
    sourceHom_unique hsetU (𝟙 W) ψ (𝟙 _) hψ
      (CategoryTheory.IsHomLift.id (representingObj_over eU b))
  have hθid : θ = 𝟙 (Functor.Fiber.mk (fObj_over (f := f) eU b)) :=
    Functor.Fiber.hom_ext
      ((hθ.trans ((congrArg f.toFunctor.map hψid).trans (f.toFunctor.map_id _))).trans
        (Functor.Fiber.fiberInclusion.map_id
          (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W)).symm)
  exact (congrArg (arrowOfFiberHom eU eR b b) hθid).trans (arrowOfFiberHom_id eU eR hsetU b)

/-! ### Restriction of the sections attached to fibre morphisms -/

section Cartesian

universe v₁ v₂ w₁ w₂

variable {𝒞 : Type w₁} [Category.{v₁} 𝒞] {𝒜 : Type w₂} [Category.{v₂} 𝒜]

/-- A morphism over a morphism of the base followed by a vertical morphism lies over the first
morphism. -/
theorem isHomLift_comp_of_isHomLift_id_right (p : 𝒜 ⥤ 𝒞) {V W : 𝒞} {x y z : 𝒜} (π : x ⟶ y)
    (ε : y ⟶ z) (g : V ⟶ W) (hπ : p.IsHomLift g π) (hε : p.IsHomLift (𝟙 W) ε) :
    p.IsHomLift g (π ≫ ε) :=
  have := hπ
  have := hε
  CategoryTheory.IsHomLift.comp_lift_id_right' p g π W ε

/-- The factorisation a strongly cartesian morphism induces, together with the two properties
characterising it. -/
noncomputable def cartesianFactor (p : 𝒜 ⥤ 𝒞) {V W T : 𝒞} {x y z : 𝒜} (g : V ⟶ W) (k : W ⟶ T)
    (φ : y ⟶ z) (hφ : p.IsStronglyCartesian k φ) (k' : V ⟶ T) (hk' : k' = g ≫ k) (φ' : x ⟶ z)
    (hφ' : p.IsHomLift k' φ') : { χ : x ⟶ y // p.IsHomLift g χ ∧ χ ≫ φ = φ' } := by
  have h1 := hφ
  have h2 := hφ'
  exact ⟨CategoryTheory.Functor.IsStronglyCartesian.map p k φ hk' φ', inferInstance,
    CategoryTheory.Functor.IsStronglyCartesian.fac p k φ hk' φ'⟩

end Cartesian

/-- The factorisation of the composite of a canonical morphism of the target with a vertical
morphism through the canonical morphism at the other section. -/
noncomputable def transportFactor {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (a b : U.obj.obj (op W))
    (α : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a)) :
    { χ : f.toFunctor.obj (representingObj eU (U.obj.map g.op b)) ⟶
        f.toFunctor.obj (representingObj eU (U.obj.map g.op a)) //
      𝒳.val.p.IsHomLift (𝟙 V) χ ∧ χ ≫ fRestrict eU g a =
        fRestrict (f := f) eU g b ≫ Functor.Fiber.fiberInclusion.map α } :=
  cartesianFactor 𝒳.val.p (𝟙 V) g (fRestrict eU g a)
    (isStronglyCartesian_fRestrict eU g a) g (Category.id_comp g).symm
    (fRestrict (f := f) eU g b ≫ Functor.Fiber.fiberInclusion.map α)
    (isHomLift_comp_of_isHomLift_id_right 𝒳.val.p (fRestrict (f := f) eU g b)
      (Functor.Fiber.fiberInclusion.map α) g (isHomLift_fRestrict eU g b) α.2)

/-- The transport of a fibre morphism of the target along a morphism of the site: the unique
vertical morphism making the square with the two canonical morphisms of the target commute. -/
noncomputable def transportFiberHom {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (a b : U.obj.obj (op W))
    (α : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a)) :
    (Functor.Fiber.mk (fObj_over (f := f) eU (U.obj.map g.op b)) : 𝒳.val.p.Fiber V) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU (U.obj.map g.op a)) :=
  ⟨(transportFactor eU g a b α).1, (transportFactor eU g a b α).2.1⟩

/-- The defining square of the transport of a fibre morphism. -/
theorem fRestrict_comp_transportFiberHom {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (a b : U.obj.obj (op W))
    (α : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a)) :
    Functor.Fiber.fiberInclusion.map (transportFiberHom eU g a b α) ≫ fRestrict eU g a =
      fRestrict (f := f) eU g b ≫ Functor.Fiber.fiberInclusion.map α :=
  (transportFactor eU g a b α).2.2

/-- The section attached to a fibre morphism restricts to the section attached to the
transported fibre morphism. -/
theorem arrowOfFiberHom_restrict {V W : BigFppfOver B S hS} (g : V ⟶ W)
    (a b : U.obj.obj (op W))
    (α : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a)) :
    R.obj.map g.op (arrowOfFiberHom eU eR a b α) =
      arrowOfFiberHom eU eR (U.obj.map g.op a) (U.obj.map g.op b)
        (transportFiberHom eU g a b α) :=
  let φ : relationOfFiberHom eU (U.obj.map g.op a) (U.obj.map g.op b)
      (transportFiberHom eU g a b α) ⟶ relationOfFiberHom eU a b α :=
    { hbase := g
      a := representingObjRestrict eU g b
      b := representingObjRestrict eU g a
      ha := isHomLift_representingObjRestrict eU g b
      hb := isHomLift_representingObjRestrict eU g a
      w := (fRestrict_comp_transportFiberHom eU g a b α).symm }
  (PresheafOfCategories.sectionOfObj_map eR
    (rfl : (relation B S hS 𝒰 𝒳 f).val.p.obj (relationOfFiberHom eU a b α) = W)
    (rfl : (relation B S hS 𝒰 𝒳 f).val.p.obj
      (relationOfFiberHom eU (U.obj.map g.op a) (U.obj.map g.op b)
        (transportFiberHom eU g a b α)) = V)
    g φ (TwoFibreProductOver.structureFunctor_isHomLift φ g
      (isHomLift_representingObjRestrict eU g b))).symm

/-! ### The sections named by the morphisms of the pointwise groupoid fibration -/

/-- The pointwise groupoid fibration of the self-intersection groupoid: the category fibred in
groupoids over the big fppf site attached to the presheaf of groupoids obtained by evaluating the
self-intersection groupoid at every object of the site. -/
noncomputable abbrev pointwiseFibration (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    BasedCategory (BigFppfOver B S hS) :=
  presheafOfGroupoids (Stack.evaluationGroupoidFunctor
    (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors)

/-- The section of the arrow space that a morphism of the pointwise groupoid fibration names: an
arrow of an evaluated groupoid *is* a section of the arrow space with prescribed endpoints. -/
noncomputable def pointwiseSection (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (u : X ⟶ Y) : R.obj.obj (op X.base) :=
  ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv
    (op X.base) X.fiber (U.obj.map u.base.op Y.fiber) u.fiber).1

/-- The source of the section named by a morphism of the pointwise groupoid fibration is the
point the morphism starts at. -/
theorem relationSourceMap_pointwiseSection (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (u : X ⟶ Y) :
    (relationSourceMap eU eR).app (op X.base) (pointwiseSection eU eR hsetU u) = X.fiber :=
  ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv
    (op X.base) X.fiber (U.obj.map u.base.op Y.fiber) u.fiber).2.1

/-- The target of the section named by a morphism of the pointwise groupoid fibration is the
restriction, along the morphism of the site, of the point the morphism ends at. -/
theorem relationTargetMap_pointwiseSection (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (u : X ⟶ Y) :
    (relationTargetMap eU eR).app (op X.base) (pointwiseSection eU eR hsetU u) =
      U.obj.map u.base.op Y.fiber :=
  ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv
    (op X.base) X.fiber (U.obj.map u.base.op Y.fiber) u.fiber).2.2

/-- An arrow of an evaluated groupoid followed by an arrow coming from an equality of its target
names the same section. -/
theorem evaluationArrowEquiv_comp_eqToHom {D : Type (u + 1)} [Category.{u} D]
    (G : Deformation.GroupoidInFunctors.{u + 1, u, u} D) (T : D)
    {x y z : G.Evaluation T} (m : x ⟶ y) (e : y = z) :
    (G.evaluationArrowEquiv T x z (m ≫ eqToHom e)).1 =
      (G.evaluationArrowEquiv T x y m).1 := by
  cases e
  rw [eqToHom_refl, Category.comp_id]

/-- The section named by an identity is the identity arrow. -/
theorem pointwiseSection_id (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (X : (pointwiseFibration eU eR hsetU).obj) :
    pointwiseSection eU eR hsetU (𝟙 X) =
      (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.identity (op X.base) X.fiber :=
  (congrArg
      (fun m => ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv
        (op X.base) X.fiber (U.obj.map (𝟙 X.base).op X.fiber) m).1)
      (Cat.eqToHom_app _ _
        (((Stack.evaluationGroupoidFunctor
          (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors ⋙
            Grpd.forgetToCat).map_id (op X.base)).symm) X.fiber)).trans
    (evaluationArrow_eqToHom_identity
      (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors (op X.base) _)

/-- Composition in an evaluated groupoid, with the two sections composed read through
equalities. -/
theorem compose_congr {D : Type (u + 1)} [Category.{u} D]
    (G : Deformation.GroupoidInFunctors.{u + 1, u, u} D) (T : D)
    {A A' A₂ A₂' : G.arrows.obj T} (h1 : A = A₂) (h2 : A' = A₂')
    (h : G.source.app T A = G.target.app T A')
    (h₂ : G.source.app T A₂ = G.target.app T A₂') :
    G.compose T A A' h = G.compose T A₂ A₂' h₂ := by
  subst h1
  subst h2
  rfl

/-- The section named by a morphism of the pointwise groupoid fibration, restricted along the
morphism of the site of a second one, is composable with the section the second one names. -/
theorem pointwiseSection_composable (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y Z : (pointwiseFibration eU eR hsetU).obj} (u : X ⟶ Y) (v : Y ⟶ Z) :
    (relationSourceMap eU eR).app (op X.base)
        (R.obj.map u.base.op (pointwiseSection eU eR hsetU v)) =
      (relationTargetMap eU eR).app (op X.base) (pointwiseSection eU eR hsetU u) :=
  (NatTrans.naturality_apply (relationSourceMap eU eR) u.base.op _).trans
    ((congrArg (U.obj.map u.base.op) (relationSourceMap_pointwiseSection eU eR hsetU v)).trans
      (relationTargetMap_pointwiseSection eU eR hsetU u).symm)

/-- An arrow of an evaluated groupoid followed by the component of the coherence isomorphism of a
functor into `Cat` names the same section. -/
theorem evaluationArrowEquiv_comp_catEqToHom {D : Type (u + 1)} [Category.{u} D]
    (G : Deformation.GroupoidInFunctors.{u + 1, u, u} D) (T : D) {C : Cat.{u, u}}
    {F₁ F₂ : C ⟶ Cat.of (G.Evaluation T)} (h : F₁ = F₂) (x : C) {w : G.Evaluation T}
    (m : w ⟶ F₁.toFunctor.obj x) :
    (G.evaluationArrowEquiv T w (F₂.toFunctor.obj x)
        (m ≫ (eqToHom h).toNatTrans.app x)).1 =
      (G.evaluationArrowEquiv T w (F₁.toFunctor.obj x) m).1 := by
  cases h
  rw [eqToHom_refl]
  exact congrArg (fun k => (G.evaluationArrowEquiv T w (F₁.toFunctor.obj x) k).1)
    (Category.comp_id m)

/-- The section named by a composite is the composite of the two sections named, the second
restricted along the morphism of the site of the first. -/
theorem pointwiseSection_comp (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y Z : (pointwiseFibration eU eR hsetU).obj} (u : X ⟶ Y) (v : Y ⟶ Z) :
    pointwiseSection eU eR hsetU (u ≫ v) =
      (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.compose (op X.base)
        (R.obj.map u.base.op (pointwiseSection eU eR hsetU v))
        (pointwiseSection eU eR hsetU u)
        (pointwiseSection_composable eU eR hsetU u v) := by
  refine (Deformation.GroupoidInFunctors.evaluationArrowEquiv_comp
    (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors (op X.base) u.fiber ?_).trans ?_
  refine compose_congr _ (op X.base) ?_ rfl _ _
  refine (evaluationArrowEquiv_comp_catEqToHom
    (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors (op X.base)
    (((Stack.evaluationGroupoidFunctor
      (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors ⋙
        Grpd.forgetToCat).map_comp v.base.op u.base.op).symm) Z.fiber _).trans ?_
  exact Deformation.evaluationMap_map_arrow
    (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors u.base.op v.fiber

/-! ### The 1-morphism from the pointwise groupoid fibration to the target -/

/-- The fibre morphism of the target that a morphism of the pointwise groupoid fibration names:
the arrow of the relation it names, read through the hom-set bijection of the pointwise
groupoid. -/
noncomputable def pointwiseFiberHom (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (u : X ⟶ Y) :
    (Functor.Fiber.mk (fObj_over (f := f) eU (U.obj.map u.base.op Y.fiber)) :
        𝒳.val.p.Fiber X.base) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU X.fiber) :=
  ((arrowEquivOfSection eU eR hsetU X.fiber (U.obj.map u.base.op Y.fiber)).symm
    ⟨pointwiseSection eU eR hsetU u, relationSourceMap_pointwiseSection eU eR hsetU u,
      relationTargetMap_pointwiseSection eU eR hsetU u⟩).unop

/-- The fibre morphism named by a morphism of the pointwise groupoid fibration names back the
section that morphism names. -/
theorem arrowOfFiberHom_pointwiseFiberHom (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (u : X ⟶ Y) :
    arrowOfFiberHom eU eR X.fiber (U.obj.map u.base.op Y.fiber)
        (pointwiseFiberHom eU eR hsetU u) =
      pointwiseSection eU eR hsetU u :=
  congrArg Subtype.val
    (Equiv.apply_symm_apply
      (arrowEquivOfSection eU eR hsetU X.fiber (U.obj.map u.base.op Y.fiber))
      ⟨pointwiseSection eU eR hsetU u, relationSourceMap_pointwiseSection eU eR hsetU u,
        relationTargetMap_pointwiseSection eU eR hsetU u⟩)

/-- Reading a composite of fibre morphisms as an isomorphism of the target is reading each factor
as one. -/
theorem fiberHomIso_comp {W : BigFppfOver B S hS} (a b c : U.obj.obj (op W))
    (α : (Functor.Fiber.mk (fObj_over (f := f) eU c) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU b))
    (β : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber W) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU a)) :
    fiberHomIso eU a c (α ≫ β) = fiberHomIso eU b c α ≪≫ fiberHomIso eU a b β :=
  Iso.ext (Functor.Fiber.fiberInclusion.map_comp α β)

/-- The value on morphisms of the 1-morphism from the pointwise groupoid fibration to `𝒳`: the
inverse of the isomorphism of the target that the named arrow of the relation gives, followed by
the canonical morphism between the chosen representatives. -/
noncomputable def toStackOfPointwiseGroupoidMap (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (u : X ⟶ Y) :
    f.toFunctor.obj (representingObj eU X.fiber) ⟶
      f.toFunctor.obj (representingObj eU Y.fiber) :=
  (fiberHomIso eU X.fiber (U.obj.map u.base.op Y.fiber)
      (pointwiseFiberHom eU eR hsetU u)).inv ≫ fRestrict eU u.base Y.fiber

/-- Any fibre morphism naming the section named by `u`, and any morphism of the source over the
morphism of the site `u` lies over, compute the value of the 1-morphism on `u`. -/
theorem toStackOfPointwiseGroupoidMap_eq (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (u : X ⟶ Y) (b : U.obj.obj (op X.base))
    (θ : (Functor.Fiber.mk (fObj_over (f := f) eU b) : 𝒳.val.p.Fiber X.base) ⟶
      Functor.Fiber.mk (fObj_over (f := f) eU X.fiber))
    (hθ : arrowOfFiberHom eU eR X.fiber b θ = pointwiseSection eU eR hsetU u)
    (κ : representingObj eU b ⟶ representingObj eU Y.fiber)
    (hκ : 𝒰.val.p.IsHomLift u.base κ) :
    toStackOfPointwiseGroupoidMap eU eR hsetU u =
      (fiberHomIso eU X.fiber b θ).inv ≫ f.toFunctor.map κ := by
  have hb : b = U.obj.map u.base.op Y.fiber :=
    (relationTargetMap_arrowOfFiberHom eU eR X.fiber b θ).symm.trans
      ((congrArg (fun r => (relationTargetMap eU eR).app (op X.base) r) hθ).trans
        (relationTargetMap_pointwiseSection eU eR hsetU u))
  subst hb
  have hθθ : θ = pointwiseFiberHom eU eR hsetU u :=
    arrowOfFiberHom_injective eU eR hsetU X.fiber _ θ _
      (hθ.trans (arrowOfFiberHom_pointwiseFiberHom eU eR hsetU u).symm)
  have hκκ : κ = representingObjRestrict eU u.base Y.fiber :=
    sourceHom_unique hsetU u.base κ _ hκ (isHomLift_representingObjRestrict eU u.base Y.fiber)
  rw [hθθ, hκκ]
  rfl

/-- The value on morphisms lies over the morphism of the site. -/
theorem isHomLift_toStackOfPointwiseGroupoidMap (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (u : X ⟶ Y) :
    𝒳.val.p.IsHomLift u.base (toStackOfPointwiseGroupoidMap eU eR hsetU u) :=
  CategoryTheory.Functor.isHomLift_comp_of_isHomLift_id 𝒳.val.p _ _ u.base
    (@CategoryTheory.IsHomLift.lift_id_inv _ _ _ _ 𝒳.val.p _ _ _
      (fiberHomIso eU X.fiber (U.obj.map u.base.op Y.fiber) (pointwiseFiberHom eU eR hsetU u))
      (pointwiseFiberHom eU eR hsetU u).2)
    (isHomLift_fRestrict eU u.base Y.fiber)

/-- The value on morphisms preserves identities. -/
theorem toStackOfPointwiseGroupoidMap_id (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (X : (pointwiseFibration eU eR hsetU).obj) :
    toStackOfPointwiseGroupoidMap eU eR hsetU (𝟙 X) =
      𝟙 (f.toFunctor.obj (representingObj eU X.fiber)) := by
  have hvert : 𝒳.val.p.IsHomLift (𝟙 X.base) (fRestrict (f := f) eU (𝟙 X.base) X.fiber) :=
    isHomLift_fRestrict eU (𝟙 X.base) X.fiber
  have hθ : arrowOfFiberHom eU eR X.fiber (U.obj.map (𝟙 X.base).op X.fiber)
        ⟨fRestrict (f := f) eU (𝟙 X.base) X.fiber, hvert⟩ =
      pointwiseSection eU eR hsetU (𝟙 X) :=
    (arrowOfFiberHom_eq_identity eU eR hsetU X.fiber (U.obj.map (𝟙 X.base).op X.fiber)
      (U.obj.map_id_apply (op X.base) X.fiber)
      (representingObjRestrict eU (𝟙 X.base) X.fiber)
      (isHomLift_representingObjRestrict eU (𝟙 X.base) X.fiber) _ rfl).trans
      (pointwiseSection_id eU eR hsetU X).symm
  rw [toStackOfPointwiseGroupoidMap_eq eU eR hsetU (𝟙 X) (U.obj.map (𝟙 X.base).op X.fiber)
    ⟨fRestrict (f := f) eU (𝟙 X.base) X.fiber, hvert⟩ hθ
    (representingObjRestrict eU (𝟙 X.base) X.fiber)
    (isHomLift_representingObjRestrict eU (𝟙 X.base) X.fiber)]
  exact (fiberHomIso eU X.fiber (U.obj.map (𝟙 X.base).op X.fiber)
    ⟨fRestrict (f := f) eU (𝟙 X.base) X.fiber, hvert⟩).inv_hom_id

/-- The value on morphisms, as defined. -/
theorem toStackOfPointwiseGroupoidMap_def (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (u : X ⟶ Y) :
    toStackOfPointwiseGroupoidMap eU eR hsetU u =
      (fiberHomIso eU X.fiber (U.obj.map u.base.op Y.fiber)
        (pointwiseFiberHom eU eR hsetU u)).inv ≫ fRestrict eU u.base Y.fiber := rfl

/-- The value on morphisms preserves composition. -/
theorem toStackOfPointwiseGroupoidMap_comp (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y Z : (pointwiseFibration eU eR hsetU).obj} (u : X ⟶ Y) (v : Y ⟶ Z) :
    toStackOfPointwiseGroupoidMap eU eR hsetU (u ≫ v) =
      toStackOfPointwiseGroupoidMap eU eR hsetU u ≫
        toStackOfPointwiseGroupoidMap eU eR hsetU v := by
  have hR : R.obj.map u.base.op (pointwiseSection eU eR hsetU v) =
      arrowOfFiberHom eU eR (U.obj.map u.base.op Y.fiber)
        (U.obj.map u.base.op (U.obj.map v.base.op Z.fiber))
        (transportFiberHom eU u.base Y.fiber (U.obj.map v.base.op Z.fiber)
          (pointwiseFiberHom eU eR hsetU v)) :=
    (congrArg (fun r => R.obj.map u.base.op r)
      (arrowOfFiberHom_pointwiseFiberHom eU eR hsetU v).symm).trans
      (arrowOfFiberHom_restrict eU eR u.base Y.fiber (U.obj.map v.base.op Z.fiber)
        (pointwiseFiberHom eU eR hsetU v))
  have hc2 : (relationSourceMap eU eR).app (op X.base)
        (arrowOfFiberHom eU eR (U.obj.map u.base.op Y.fiber)
          (U.obj.map u.base.op (U.obj.map v.base.op Z.fiber))
          (transportFiberHom eU u.base Y.fiber (U.obj.map v.base.op Z.fiber)
            (pointwiseFiberHom eU eR hsetU v))) =
      (relationTargetMap eU eR).app (op X.base)
        (arrowOfFiberHom eU eR X.fiber (U.obj.map u.base.op Y.fiber)
          (pointwiseFiberHom eU eR hsetU u)) :=
    (relationSourceMap_arrowOfFiberHom eU eR _ _ _).trans
      (relationTargetMap_arrowOfFiberHom eU eR _ _ _).symm
  have hθ : arrowOfFiberHom eU eR X.fiber
        (U.obj.map u.base.op (U.obj.map v.base.op Z.fiber))
        (transportFiberHom eU u.base Y.fiber (U.obj.map v.base.op Z.fiber)
            (pointwiseFiberHom eU eR hsetU v) ≫ pointwiseFiberHom eU eR hsetU u) =
      pointwiseSection eU eR hsetU (u ≫ v) :=
    ((pointwiseSection_comp eU eR hsetU u v).trans
      ((compositionLaw_app_compose eU eR hsetU (op X.base) hR
        (arrowOfFiberHom_pointwiseFiberHom eU eR hsetU u).symm _ hc2).trans
        (compositionLaw_app_arrowOfFiberHom eU eR hsetU X.fiber _ _ _ _ hc2))).symm
  have h1 := isHomLift_representingObjRestrict eU u.base (U.obj.map v.base.op Z.fiber)
  have h2 := isHomLift_representingObjRestrict eU v.base Z.fiber
  have hκ : 𝒰.val.p.IsHomLift (u ≫ v).base
      (representingObjRestrict eU u.base (U.obj.map v.base.op Z.fiber) ≫
        representingObjRestrict eU v.base Z.fiber) :=
    CategoryTheory.IsHomLift.comp 𝒰.val.p u.base v.base _ _
  have hsq : (fiberHomIso eU (U.obj.map u.base.op Y.fiber)
          (U.obj.map u.base.op (U.obj.map v.base.op Z.fiber))
          (transportFiberHom eU u.base Y.fiber (U.obj.map v.base.op Z.fiber)
            (pointwiseFiberHom eU eR hsetU v))).hom ≫ fRestrict eU u.base Y.fiber =
      fRestrict (f := f) eU u.base (U.obj.map v.base.op Z.fiber) ≫
        (fiberHomIso eU Y.fiber (U.obj.map v.base.op Z.fiber)
          (pointwiseFiberHom eU eR hsetU v)).hom :=
    fRestrict_comp_transportFiberHom eU u.base Y.fiber (U.obj.map v.base.op Z.fiber)
      (pointwiseFiberHom eU eR hsetU v)
  have hinner : (fiberHomIso eU (U.obj.map u.base.op Y.fiber)
          (U.obj.map u.base.op (U.obj.map v.base.op Z.fiber))
          (transportFiberHom eU u.base Y.fiber (U.obj.map v.base.op Z.fiber)
            (pointwiseFiberHom eU eR hsetU v))).inv ≫
        fRestrict eU u.base (U.obj.map v.base.op Z.fiber) =
      fRestrict (f := f) eU u.base Y.fiber ≫
        (fiberHomIso eU Y.fiber (U.obj.map v.base.op Z.fiber)
          (pointwiseFiberHom eU eR hsetU v)).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, hsq, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [toStackOfPointwiseGroupoidMap_eq eU eR hsetU (u ≫ v) _ _ hθ _ hκ,
    toStackOfPointwiseGroupoidMap_def eU eR hsetU u,
    toStackOfPointwiseGroupoidMap_def eU eR hsetU v,
    fiberHomIso_comp eU X.fiber (U.obj.map u.base.op Y.fiber)
      (U.obj.map u.base.op (U.obj.map v.base.op Z.fiber))
      (transportFiberHom eU u.base Y.fiber (U.obj.map v.base.op Z.fiber)
        (pointwiseFiberHom eU eR hsetU v)) (pointwiseFiberHom eU eR hsetU u),
    Iso.trans_inv, Functor.map_comp]
  have hinner2 : (fiberHomIso eU (U.obj.map u.base.op Y.fiber)
          (U.obj.map u.base.op (U.obj.map v.base.op Z.fiber))
          (transportFiberHom eU u.base Y.fiber (U.obj.map v.base.op Z.fiber)
            (pointwiseFiberHom eU eR hsetU v))).inv ≫
        fRestrict eU u.base (U.obj.map v.base.op Z.fiber) ≫ fRestrict eU v.base Z.fiber =
      fRestrict (f := f) eU u.base Y.fiber ≫
        (fiberHomIso eU Y.fiber (U.obj.map v.base.op Z.fiber)
          (pointwiseFiberHom eU eR hsetU v)).inv ≫ fRestrict eU v.base Z.fiber := by
    rw [← Category.assoc, hinner, Category.assoc]
  simp only [Category.assoc]
  exact congrArg
    (fun k => (fiberHomIso eU X.fiber (U.obj.map u.base.op Y.fiber)
      (pointwiseFiberHom eU eR hsetU u)).inv ≫ k) hinner2

/-- The 1-morphism from the pointwise groupoid fibration of the self-intersection groupoid to
the algebraic stack, as a functor: on objects the image under `f` of the chosen representative,
on morphisms the value above. -/
noncomputable def toStackOfPointwiseGroupoidFunctor (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    (pointwiseFibration eU eR hsetU).obj ⥤ 𝒳.val.obj where
  obj X := f.toFunctor.obj (representingObj eU X.fiber)
  map u := toStackOfPointwiseGroupoidMap eU eR hsetU u
  map_id X := toStackOfPointwiseGroupoidMap_id eU eR hsetU X
  map_comp u v := toStackOfPointwiseGroupoidMap_comp eU eR hsetU u v

/-- The 1-morphism from the pointwise groupoid fibration of the self-intersection groupoid to
`𝒳`, as a 1-morphism over the big fppf site. -/
noncomputable def toStackOfPointwiseGroupoid (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    BasedFunctor (pointwiseFibration eU eR hsetU) 𝒳.val where
  toFunctor := toStackOfPointwiseGroupoidFunctor eU eR hsetU
  w := CategoryTheory.Functor.ext (fun X => fObj_over eU X.fiber) (fun _ _ u =>
    have := isHomLift_toStackOfPointwiseGroupoidMap eU eR hsetU u
    CategoryTheory.IsHomLift.fac' 𝒳.val.p u.base (toStackOfPointwiseGroupoidMap eU eR hsetU u))

/-- The value of the 1-morphism on a morphism naming an identity arrow is the image under `f` of
a morphism of the source. -/
theorem toStackOfPointwiseGroupoidMap_eq_map (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    {X Y : (pointwiseFibration eU eR hsetU).obj} (u : X ⟶ Y)
    (hab : U.obj.map u.base.op Y.fiber = X.fiber)
    (hid : pointwiseSection eU eR hsetU u =
      (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.identity (op X.base) X.fiber)
    (ψI : representingObj eU (U.obj.map u.base.op Y.fiber) ≅ representingObj eU X.fiber)
    (hψ : 𝒰.val.p.IsHomLift (𝟙 X.base) ψI.hom)
    (κ : representingObj eU (U.obj.map u.base.op Y.fiber) ⟶ representingObj eU Y.fiber)
    (hκ : 𝒰.val.p.IsHomLift u.base κ) :
    toStackOfPointwiseGroupoidMap eU eR hsetU u = f.toFunctor.map (ψI.inv ≫ κ) := by
  have hlift : 𝒳.val.p.IsHomLift (𝟙 X.base) (f.toFunctor.map ψI.hom) :=
    CategoryTheory.Functor.isHomLift_map_of_comp_eq' f.w (𝟙 X.base) ψI.hom hψ
  have hθ : arrowOfFiberHom eU eR X.fiber (U.obj.map u.base.op Y.fiber)
        ⟨f.toFunctor.map ψI.hom, hlift⟩ = pointwiseSection eU eR hsetU u :=
    (arrowOfFiberHom_eq_identity eU eR hsetU X.fiber (U.obj.map u.base.op Y.fiber) hab
      ψI.hom hψ ⟨f.toFunctor.map ψI.hom, hlift⟩ rfl).trans hid.symm
  have hiso : fiberHomIso eU X.fiber (U.obj.map u.base.op Y.fiber)
      ⟨f.toFunctor.map ψI.hom, hlift⟩ = f.toFunctor.mapIso ψI := Iso.ext rfl
  rw [toStackOfPointwiseGroupoidMap_eq eU eR hsetU u (U.obj.map u.base.op Y.fiber)
    ⟨f.toFunctor.map ψI.hom, hlift⟩ hθ κ hκ, hiso, Functor.map_comp]
  rfl

/-! ### The comparison with the given 1-morphism -/

/-- The vertical isomorphism of the source comparing an object with the chosen representative of
the section it names, for an arbitrary identification of the object it lies over. -/
noncomputable def representingObjIsoOfSection (z : 𝒰.val.obj) {W : BigFppfOver B S hS}
    (h : 𝒰.val.p.obj z = W) :
    (Functor.Fiber.mk
        (representingObj_over eU (PresheafOfCategories.sectionOfObj eU z h)) :
        𝒰.val.p.Fiber W) ≅ Functor.Fiber.mk h :=
  PresheafOfCategories.fiberIsoOfSectionOfObj_eq eU
    (representingObj_over eU (PresheafOfCategories.sectionOfObj eU z h)) h
    (sectionOfObj_representingObj eU (PresheafOfCategories.sectionOfObj eU z h))

/-- The comparison isomorphism of the target between the image under `f` of the chosen
representative of the section an object names and the image under `f` of that object. -/
noncomputable def representingComparisonIso (z : 𝒰.val.obj) {W : BigFppfOver B S hS}
    (h : 𝒰.val.p.obj z = W) :
    f.toFunctor.obj (representingObj eU (PresheafOfCategories.sectionOfObj eU z h)) ≅
      f.toFunctor.obj z :=
  f.toFunctor.mapIso (Functor.Fiber.fiberInclusion.mapIso (representingObjIsoOfSection eU z h))

/-- The comparison isomorphism is vertical over the big fppf site. -/
theorem isHomLift_representingComparisonIso (z : 𝒰.val.obj) {W : BigFppfOver B S hS}
    (h : 𝒰.val.p.obj z = W) :
    𝒳.val.p.IsHomLift (𝟙 W) (representingComparisonIso (f := f) eU z h).hom :=
  CategoryTheory.Functor.isHomLift_map_of_comp_eq' f.w (𝟙 W) _
    (representingObjIsoOfSection eU z h).hom.2

/-- The hom of the comparison isomorphism. -/
@[simp] theorem representingComparisonIso_hom (z : 𝒰.val.obj) {W : BigFppfOver B S hS}
    (h : 𝒰.val.p.obj z = W) :
    (representingComparisonIso (f := f) eU z h).hom =
      f.toFunctor.map
        (Functor.Fiber.fiberInclusion.map (representingObjIsoOfSection eU z h).hom) := rfl

/-- The component of the comparison with `f`: the image under `f` of the comparison of an object
with the chosen representative of the section it names. -/
noncomputable def extendsFApp (z : 𝒰.val.obj) :
    f.toFunctor.obj (representingObj eU (Discrete.as (eU.hom.functor.obj z).fiber)) ≅
      f.toFunctor.obj z :=
  representingComparisonIso eU z (Functor.congr_obj eU.hom.w z).symm

/-- The component of the comparison with `f` is vertical over the big fppf site. -/
theorem isHomLift_extendsFApp (z : 𝒰.val.obj) :
    𝒳.val.p.IsHomLift (𝟙 (𝒰.val.p.obj z)) (extendsFApp (f := f) eU z).hom := by
  rw [← Functor.congr_obj eU.hom.w z]
  exact isHomLift_representingComparisonIso eU z _

/-- The composite of the 1-morphism with the canonical inclusion of the object space is the
given 1-morphism, up to a vertical 2-isomorphism. -/
noncomputable def extendsF (hsetU : 𝒰.val.p.IsFiberedInSetoids) :
    eU.hom.functor ⋙ Stack.pointwiseObjectInclusion (selfIntersectionGroupoid eU eR hsetU) ⋙
        (toStackOfPointwiseGroupoid eU eR hsetU).toFunctor ≅ f.toFunctor :=
  NatIso.ofComponents (fun z => extendsFApp eU z) (by
    intro z z' φ
    have hab : U.obj.map (eU.hom.functor.map φ).base.op
          (Discrete.as (eU.hom.functor.obj z').fiber) =
        Discrete.as (eU.hom.functor.obj z).fiber :=
      (CategoryTheory.Discrete.eq_of_hom (eU.hom.functor.map φ).fiber).symm
    have hid : pointwiseSection eU eR hsetU
          ((Stack.pointwiseObjectInclusion
            (selfIntersectionGroupoid eU eR hsetU)).map (eU.hom.functor.map φ)) =
        (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.identity
          (op (eU.hom.functor.obj z).base) (Discrete.as (eU.hom.functor.obj z).fiber) :=
      Stack.evaluationArrow_eqToHom_identity
        (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors
        (op (eU.hom.functor.obj z).base)
        (CategoryTheory.Discrete.eq_of_hom (eU.hom.functor.map φ).fiber)
    have hψ : 𝒰.val.p.IsHomLift (𝟙 (eU.hom.functor.obj z).base)
        (eqToIso (congrArg (fun a => representingObj eU a) hab)).hom :=
      CategoryTheory.IsHomLift.eqToHom_domain_lift_id
        (congrArg (fun a => representingObj eU a) hab) (representingObj_over eU _)
    have hinv : 𝒰.val.p.IsHomLift (𝟙 (eU.hom.functor.obj z).base)
        (eqToIso (congrArg (fun a => representingObj eU a) hab)).inv :=
      @CategoryTheory.IsHomLift.lift_id_inv _ _ _ _ 𝒰.val.p _ _ _ _ hψ
    have hres := isHomLift_representingObjRestrict eU (eU.hom.functor.map φ).base
      (Discrete.as (eU.hom.functor.obj z').fiber)
    have hmap := toStackOfPointwiseGroupoidMap_eq_map eU eR hsetU
      ((Stack.pointwiseObjectInclusion
        (selfIntersectionGroupoid eU eR hsetU)).map (eU.hom.functor.map φ)) hab hid
      (eqToIso (congrArg (fun a => representingObj eU a) hab)) hψ
      (representingObjRestrict eU (eU.hom.functor.map φ).base
        (Discrete.as (eU.hom.functor.obj z').fiber)) hres
    have hvz' : 𝒰.val.p.IsHomLift (𝟙 (eU.hom.functor.obj z').base)
        (Functor.Fiber.fiberInclusion.map
          (representingObjIsoOfSection eU z' (Functor.congr_obj eU.hom.w z').symm).hom) :=
      (representingObjIsoOfSection eU z' (Functor.congr_obj eU.hom.w z').symm).hom.2
    have hvz : 𝒰.val.p.IsHomLift (𝟙 (eU.hom.functor.obj z).base)
        (Functor.Fiber.fiberInclusion.map
          (representingObjIsoOfSection eU z (Functor.congr_obj eU.hom.w z).symm).hom) :=
      (representingObjIsoOfSection eU z (Functor.congr_obj eU.hom.w z).symm).hom.2
    have hφ : 𝒰.val.p.IsHomLift (eU.hom.functor.map φ).base φ := by
      have : (presheafOfCategories (U.obj ⋙ typeToCat)).p.IsHomLift
          (eU.hom.functor.map φ).base (eU.hom.functor.map φ) :=
        CategoryTheory.IsHomLift.map (presheafOfCategories (U.obj ⋙ typeToCat)).p
          (eU.hom.functor.map φ)
      exact CategoryTheory.Functor.isHomLift_of_isHomLift_map eU.hom.w _ φ
    have h1 : 𝒰.val.p.IsHomLift (eU.hom.functor.map φ).base
        (((eqToIso (congrArg (fun a => representingObj eU a) hab)).inv ≫
          representingObjRestrict eU (eU.hom.functor.map φ).base
            (Discrete.as (eU.hom.functor.obj z').fiber)) ≫
          Functor.Fiber.fiberInclusion.map
            (representingObjIsoOfSection eU z' (Functor.congr_obj eU.hom.w z').symm).hom) :=
      isHomLift_comp_of_isHomLift_id_right 𝒰.val.p _ _ _
        (CategoryTheory.Functor.isHomLift_comp_of_isHomLift_id 𝒰.val.p _ _ _ hinv hres) hvz'
    have h2 : 𝒰.val.p.IsHomLift (eU.hom.functor.map φ).base
        (Functor.Fiber.fiberInclusion.map
          (representingObjIsoOfSection eU z (Functor.congr_obj eU.hom.w z).symm).hom ≫ φ) :=
      CategoryTheory.Functor.isHomLift_comp_of_isHomLift_id 𝒰.val.p _ _ _ hvz hφ
    change toStackOfPointwiseGroupoidMap eU eR hsetU
        ((Stack.pointwiseObjectInclusion (selfIntersectionGroupoid eU eR hsetU)).map
          (eU.hom.functor.map φ)) ≫ (extendsFApp eU z').hom = _
    rw [hmap]
    exact (((f.toFunctor.map_comp _ _).symm.trans
      (congrArg f.toFunctor.map
        (sourceHom_unique hsetU (eU.hom.functor.map φ).base _ _ h1 h2))).trans
      (f.toFunctor.map_comp _ _)))

/-! ### The descent compatibility, equation (04TG) -/

/-- An arrow of an evaluated groupoid obtained from an equality of its endpoints. -/
noncomputable def evaluationArrowOfEq {D : Type (u + 1)} [Category.{u} D]
    (G : Deformation.GroupoidInFunctors.{u + 1, u, u} D) (T : D)
    {x y : G.Evaluation T} (h : x = y) : x ⟶ y :=
  eqToHom h

/-- The arrow of the pointwise groupoid fibration that an arrow of the relation names: the
vertical arrow from the section named by its source to the section named by its target whose own
section of the arrow space is the one the arrow of the relation names. -/
noncomputable def descentArrow (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (r : (relation B S hS 𝒰 𝒳 f).val.obj) {W : BigFppfOver B S hS}
    (hr : (relation B S hS 𝒰 𝒳 f).val.p.obj r = W) :
    (⟨W, PresheafOfCategories.sectionOfObj eU r.y (relation_obj_y hr)⟩ :
        (pointwiseFibration eU eR hsetU).obj) ⟶
      ⟨W, PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x hr)⟩ where
  base := 𝟙 W
  fiber :=
    ((selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors.evaluationArrowEquiv (op W)
        (PresheafOfCategories.sectionOfObj eU r.y (relation_obj_y hr))
        (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x hr))).symm
      ⟨PresheafOfCategories.sectionOfObj eR r hr,
        relationSourceMap_sectionOfObj eU eR r hr, relationTargetMap_sectionOfObj eU eR r hr⟩ ≫
      evaluationArrowOfEq (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors (op W)
        (U.obj.map_id_apply (op W)
          (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x hr))).symm

/-- The section named by that arrow is the section the arrow of the relation names. -/
theorem pointwiseSection_descentArrow (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (r : (relation B S hS 𝒰 𝒳 f).val.obj) {W : BigFppfOver B S hS}
    (hr : (relation B S hS 𝒰 𝒳 f).val.p.obj r = W) :
    pointwiseSection eU eR hsetU (descentArrow eU eR hsetU r hr) =
      PresheafOfCategories.sectionOfObj eR r hr :=
  (evaluationArrowEquiv_comp_eqToHom
      (selfIntersectionGroupoid eU eR hsetU).toGroupoidInFunctors (op W) _ _).trans
    (congrArg Subtype.val (Equiv.apply_symm_apply _ _))

/-- The composite of four isomorphisms, read backwards, cancels down to the inverse of the
third. -/
theorem iso_descent_cancel {C : Type (u + 1)} [Category.{u} C] {P Q T V Y : C} (a : P ≅ Q)
    (bx : Q ≅ T) (ri : T ≅ V) (by' : Y ≅ V) (Θ : P ≅ Y)
    (hΘ : Θ = a ≪≫ bx ≪≫ ri ≪≫ by'.symm) :
    by'.inv ≫ (Θ.inv ≫ a.hom) ≫ bx.hom = ri.inv := by
  subst hΘ
  simp

/-- Cancelling an isomorphism inserted in the middle of a composite. -/
theorem comp_cancel_inv_hom {C : Type (u + 1)} [Category.{u} C] {P Q T V Y : C} (a : P ⟶ Q)
    (b : Q ⟶ T) (c : T ⟶ V) (d : Y ≅ V) :
    (a ≫ b) ≫ c = (a ≫ b ≫ c ≫ d.inv) ≫ d.hom := by
  simp

/-- Equation (04TG): the arrow of the pointwise groupoid fibration that an arrow `(x, y, α)` of
the relation names is carried by the 1-morphism, after the vertical comparison with `f`, to the
inverse of the defining isomorphism `α`. -/
theorem descent_compatible (hsetU : 𝒰.val.p.IsFiberedInSetoids)
    (r : (relation B S hS 𝒰 𝒳 f).val.obj) :
    (representingComparisonIso eU r.y (relation_obj_y rfl)).inv ≫
        (toStackOfPointwiseGroupoid eU eR hsetU).toFunctor.map
          (descentArrow eU eR hsetU r rfl) ≫
        (representingComparisonIso eU r.x (relation_obj_x rfl)).hom = r.iso.inv := by
  have hriso : 𝒳.val.p.IsHomLift (𝟙 r.base) r.iso.hom := r.vertical
  have hA : 𝒳.val.p.IsHomLift (𝟙 r.base)
      (f.toFunctor.map (representingObjRestrict eU (𝟙 r.base)
        (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x rfl)))) :=
    isHomLift_fRestrict eU (𝟙 r.base) _
  have hBx := isHomLift_representingComparisonIso (f := f) eU r.x (relation_obj_x rfl)
  have hByinv : 𝒳.val.p.IsHomLift (𝟙 r.base)
      (representingComparisonIso (f := f) eU r.y (relation_obj_y rfl)).inv :=
    @CategoryTheory.IsHomLift.lift_id_inv _ _ _ _ 𝒳.val.p _ _ _ _
      (isHomLift_representingComparisonIso eU r.y (relation_obj_y rfl))
  have hΘ : 𝒳.val.p.IsHomLift (𝟙 r.base)
      (f.toFunctor.map (representingObjRestrict eU (𝟙 r.base)
          (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x rfl))) ≫
        (representingComparisonIso eU r.x (relation_obj_x rfl)).hom ≫ r.iso.hom ≫
          (representingComparisonIso eU r.y (relation_obj_y rfl)).inv) :=
    CategoryTheory.Functor.isHomLift_comp_of_isHomLift_id 𝒳.val.p _ _ (𝟙 r.base) hA
      (CategoryTheory.Functor.isHomLift_comp_of_isHomLift_id 𝒳.val.p _ _ (𝟙 r.base) hBx
        (CategoryTheory.Functor.isHomLift_comp_of_isHomLift_id 𝒳.val.p _ _ (𝟙 r.base) hriso
          hByinv))
  have ha : 𝒰.val.p.IsHomLift (𝟙 r.base)
      (representingObjRestrict eU (𝟙 r.base)
          (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x rfl)) ≫
        Functor.Fiber.fiberInclusion.map
          (representingObjIsoOfSection eU r.x (relation_obj_x rfl)).hom) :=
    CategoryTheory.Functor.isHomLift_comp_of_isHomLift_id 𝒰.val.p _ _ (𝟙 r.base)
      (isHomLift_representingObjRestrict eU (𝟙 r.base) _)
      (representingObjIsoOfSection eU r.x (relation_obj_x rfl)).hom.2
  have hw :
      f.toFunctor.map (representingObjRestrict eU (𝟙 r.base)
            (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x rfl)) ≫
          Functor.Fiber.fiberInclusion.map
            (representingObjIsoOfSection eU r.x (relation_obj_x rfl)).hom) ≫ r.iso.hom =
      (f.toFunctor.map (representingObjRestrict eU (𝟙 r.base)
          (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x rfl))) ≫
        (representingComparisonIso eU r.x (relation_obj_x rfl)).hom ≫ r.iso.hom ≫
          (representingComparisonIso eU r.y (relation_obj_y rfl)).inv) ≫
        f.toFunctor.map (Functor.Fiber.fiberInclusion.map
          (representingObjIsoOfSection eU r.y (relation_obj_y rfl)).hom) :=
    Eq.trans (congrArg (fun k => k ≫ r.iso.hom) (f.toFunctor.map_comp
      (representingObjRestrict eU (𝟙 r.base)
        (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x rfl)))
      (Functor.Fiber.fiberInclusion.map
        (representingObjIsoOfSection eU r.x (relation_obj_x rfl)).hom)))
      (comp_cancel_inv_hom _ _ _ (representingComparisonIso eU r.y (relation_obj_y rfl)))
  have hθ : arrowOfFiberHom eU eR
        (PresheafOfCategories.sectionOfObj eU r.y (relation_obj_y rfl))
        (U.obj.map (𝟙 r.base).op
          (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x rfl))) ⟨_, hΘ⟩ =
      pointwiseSection eU eR hsetU (descentArrow eU eR hsetU r rfl) := by
    refine Eq.trans ?_ (pointwiseSection_descentArrow eU eR hsetU r rfl).symm
    exact PresheafOfCategories.sectionOfObj_eq_of_hom eR
      (z := relationOfFiberHom eU
        (PresheafOfCategories.sectionOfObj eU r.y (relation_obj_y rfl))
        (U.obj.map (𝟙 r.base).op
          (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x rfl))) ⟨_, hΘ⟩)
      (z' := r) (W := r.base) rfl rfl
      { hbase := 𝟙 r.base
        a := representingObjRestrict eU (𝟙 r.base)
              (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x rfl)) ≫
            Functor.Fiber.fiberInclusion.map
              (representingObjIsoOfSection eU r.x (relation_obj_x rfl)).hom
        b := Functor.Fiber.fiberInclusion.map
            (representingObjIsoOfSection eU r.y (relation_obj_y rfl)).hom
        ha := ha
        hb := (representingObjIsoOfSection eU r.y (relation_obj_y rfl)).hom.2
        w := hw }
      (TwoFibreProductOver.structureFunctor_isHomLift _ (𝟙 r.base) ha)
  change (representingComparisonIso eU r.y (relation_obj_y rfl)).inv ≫
      toStackOfPointwiseGroupoidMap eU eR hsetU (descentArrow eU eR hsetU r rfl) ≫
      (representingComparisonIso eU r.x (relation_obj_x rfl)).hom = r.iso.inv
  rw [toStackOfPointwiseGroupoidMap_eq eU eR hsetU (descentArrow eU eR hsetU r rfl)
    (U.obj.map (𝟙 r.base).op
      (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x rfl))) ⟨_, hΘ⟩ hθ
    (representingObjRestrict eU (𝟙 r.base)
      (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x rfl)))
    (isHomLift_representingObjRestrict eU (𝟙 r.base) _)]
  exact iso_descent_cancel
    (fiberHomIso eU (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x rfl))
      (U.obj.map (𝟙 r.base).op
        (PresheafOfCategories.sectionOfObj eU r.x (relation_obj_x rfl))) ⟨_, hA⟩)
    (representingComparisonIso eU r.x (relation_obj_x rfl)) r.iso
    (representingComparisonIso eU r.y (relation_obj_y rfl)) _ (Iso.ext rfl)

end AlgebraicGeometry.Stack.SelfIntersection

end
