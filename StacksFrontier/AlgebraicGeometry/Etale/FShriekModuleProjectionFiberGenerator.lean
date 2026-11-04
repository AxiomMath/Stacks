module

public import StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionFiberIso

/-!
# The fibre comparison of the projection formula on a generator

Let `f : X ⟶ Y` be a locally quasi-finite morphism of a big étale site, let `Λ` be a commutative
ring, let `F` be a sheaf of `Λ`-modules on `X_étale` and `G` one on `Y_étale`. This file computes
the summand of `AlgebraicGeometry.SmallEtale.modProjectionFiberIso` at a point `x̄` of the
geometric fibre on the germ of a generator: the germ of a section `a` supported on a support `Z`
finite over a pointed étale neighbourhood `V` of `ȳ`, tensored with the germ of a section `t` of
`G` over `V`, goes to the germ of the supported section `a ⊗ f^{-1}t`.

This is the identity on which the projection map of [Stacks, Tag 0GKF] and the fibre comparison
`AlgebraicGeometry.SmallEtale.modProjectionFiberIso` are compared. That the two agree on every
element of the fibre, and hence that the comparison map of the source is an isomorphism, is
proved in `StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionIso`.

## Main definitions

* `AlgebraicGeometry.SmallEtale.modFiberComponent` — the germ at a point of the geometric fibre
  of a supported section, as an element of the stalk formed in `Λ`-modules.

## Main results

* `AlgebraicGeometry.SmallEtale.stalkPullbackFiberIso_germ` — **Stacks 03Q1 above a point of the
  geometric fibre, on germs**: the germ of `t` goes to the germ of `f^{-1}t`.
* `AlgebraicGeometry.SmallEtale.modProjectionFiberSummandIso_germ` — **the summandwise identity**:
  `germ(a) ⊗ germ(t) ↦ germ(a ⊗ f^{-1}t)`, with the two cases of whether the point of the fibre
  lifts into the canonical open of the support.

## Implementation notes

`AlgebraicGeometry.SmallEtale.stalkPullbackFiberIso` transports along the propositional equality
`AlgebraicGeometry.SmallEtale.toGeometricPoint_map` of geometric points, so the germ formula for
it needs the transport of a germ across an identification of equal geometric points; that is
`AlgebraicGeometry.toPresheafFiber_eqToHom`, proved by cases on an equality of two *free*
geometric points, which is why it is stated separately and not inlined.

Both cases of `AlgebraicGeometry.SmallEtale.modFiberComponent` have to be treated: away from the
canonical open of the support both sides vanish, which is a second computation and not an
instance of the first.

Nothing here carries a `stacks` attribute: this is the germ computation behind
[Stacks, Tag 0GKF], which is proved in
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionIso`. The passage from this
summandwise identity to an identity of maps out of the whole fibre — matching the two sides
component by component through `AlgebraicGeometry.SmallEtale.modFiniteSupportFiberIso`,
`AlgebraicGeometry.SmallEtale.moduleFiberStalksIso` and
`AlgebraicGeometry.SmallEtale.modFiberStalksTensorIso`, extending from a generator to an
arbitrary section by the formal-sum presentation of Stacks 0F6J, and from a pure tensor to an
arbitrary element of the fibre by
`CategoryTheory.GrothendieckTopology.Point.presheafFiber_hom_ext` and `TensorProduct.ext'` — is
`StacksFrontier.AlgebraicGeometry.Etale.FShriekModuleProjectionFiberComponents` and that file.

## References

* [Stacks Project, Tag 0GKF](https://stacks.math.columbia.edu/tag/0GKF)
* [Stacks Project, Tag 03Q1](https://stacks.math.columbia.edu/tag/03Q1)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits MonoidalCategory Opposite
open scoped DirectSum

namespace Stacks

/-- **Cancelling an isomorphism between two readings of a germ.** Isolated as a statement about
abstract morphisms so that it applies to terms whose types agree only up to unfolding a
definition. -/
public theorem comp_comp_cancel_right {C : Type*} [Category* C] {A P Q R T : C} (g : A ⟶ P)
    (e : P ⟶ Q) (i : Q ⟶ R) (m : A ⟶ T) (k : T ⟶ R) (j : R ⟶ Q) (g' : A ⟶ Q)
    (h1 : g ≫ e = g') (h2 : m ≫ k ≫ j = g') (h3 : j ≫ i = 𝟙 R) :
    g ≫ e ≫ i = m ≫ k := by
  rw [← Category.assoc, h1, ← h2, Category.assoc, Category.assoc, h3, Category.comp_id]

/-- Re-associating a composite of four morphisms around the middle pair. Isolated as a statement
about abstract morphisms so that it applies to terms whose types agree only up to unfolding a
definition. -/
public theorem assoc_mid {C : Type*} [Category* C] {A P Q R S : C} (a : A ⟶ P) (b : P ⟶ Q)
    (c : Q ⟶ R) (d : R ⟶ S) : (a ≫ b) ≫ c ≫ d = a ≫ (b ≫ c) ≫ d := by
  simp only [Category.assoc]

end Stacks

namespace AlgebraicGeometry

universe u v

section Transport

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {A : Type*} [Category* A]
  [HasColimitsOfSize.{u, u} A]

/-- **Germs transport across the identification of the fibres at two equal geometric points.**
Proved by cases on the equality, so that no reasoning about `eqToHom` is left in the proofs that
use it. -/
public theorem toPresheafFiber_eqToHom {t t' : GeometricPoint S} (h : t = t')
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ A) (V : SmallEtale B S hS)
    (q : (geometricPointFiber B S hS t).obj V)
    (q' : (geometricPointFiber B S hS t').obj V) (hq : HEq q q') :
    (geometricPointSitePoint B S hS t).toPresheafFiber V q P ≫
        eqToHom (congrArg
          (fun r => (geometricPointSitePoint B S hS r).presheafFiber.obj P) h) =
      (geometricPointSitePoint B S hS t').toPresheafFiber V q' P := by
  cases h
  cases hq
  rw [eqToHom_refl, Category.comp_id]

end Transport

namespace SmallEtale

variable (B : BigEtaleSite.{u}) (Λ : Type (max (u + 1) v)) [CommRing Λ] {X Y : B.Scheme}
  (f : X ⟶ Y)

attribute [local instance] moduleSheafMonoidal
attribute [local instance] SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat
attribute [local instance] hasLimitsOfSizeModuleCatSmall
attribute [local instance] preservesFilteredColimitsTensorLeftSmall
attribute [local instance] preservesFilteredColimitsTensorRightSmall

/-- A lift of a geometric point `ȳ` of `Y` to an étale neighbourhood, read as a lift of the image
under `f` of a point of the geometric fibre above `ȳ`. The two geometric points of `Y` are equal,
so this changes nothing but the spelling. -/
public def fiberBaseLift (s : GeometricPoint Y.obj) (x : GeometricFiberPoint B f s)
    (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V) :
    (geometricPointFiber B Y.obj Y.property
      ((x.toGeometricPoint B f s).map (B.inclusion.map f))).obj V :=
  ⟨u.1, u.2.trans x.2.symm⟩

/-- The two spellings of a lift of a geometric point of `Y` agree. -/
public theorem heq_fiberBaseLift (s : GeometricPoint Y.obj) (x : GeometricFiberPoint B f s)
    (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V) :
    HEq u (fiberBaseLift B f s x V u) :=
  (Subtype.heq_iff_coe_eq (fun p => by
    rw [show ((x.toGeometricPoint B f s).map (B.inclusion.map f)).hom = s.hom from x.2])).2 rfl

/-- **Stacks 03Q1 above a point of the geometric fibre, on germs.** The comparison identifying
the stalk of `G` at `ȳ` with the stalk of `f^{-1}G` at a point `x̄` of the geometric fibre carries
the germ of a section `t` of `G` over a pointed étale neighbourhood `V` of `ȳ` to the germ of
`f^{-1}t`, restricted along any arrow of a pointed étale neighbourhood of `x̄` into `X_V`
compatible with the two markings. -/
public theorem stalkPullbackFiberIso_germ (s : GeometricPoint Y.obj)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (x : GeometricFiberPoint B f s)
    (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V)
    (W : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).Elements)
    (c : W.1 ⟶ baseChange B f V)
    (hc : W.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map c ≫
      B.inclusion.map (pullback.fst V.obj.hom f) = u.1) :
    (geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber V u G.obj ≫
        (stalkPullbackFiberIso.{u, v} B Λ f s G x).hom =
      (modPullbackUnitSection B Λ f G V ≫
          ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map c.op) ≫
        (geometricPointSitePoint B X.obj X.property
            (x.toGeometricPoint B f s)).toPresheafFiber W.1 W.2
          ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj :=
  Stacks.comp_comp_cancel_right _ _ _ _ _ _ _
    (toPresheafFiber_eqToHom B Y.obj Y.property (toGeometricPoint_map B f s x).symm G.obj V u
      (fiberBaseLift B f s x V u) (heq_fiberBaseLift B f s x V u))
    (modPullbackUnitSection_comp_toPresheafFiber B Λ f G (x.toGeometricPoint B f s) W
      ⟨V, fiberBaseLift B f s x V u⟩ c hc)
    (((modPullbackStalkIso.{u, v, max (u + 1) v} B Λ f
      (x.toGeometricPoint B f s)).app G).hom_inv_id)

variable [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)]

open Classical in
/-- **The germ at a point of the geometric fibre of a section supported on a support finite over
the étale neighbourhood, as an element of the stalk formed in `Λ`-modules**: the germ of the
section itself where the lift meets the canonical open of the support, and zero otherwise. This
is `AlgebraicGeometry.SmallEtale.fiberStalkComponent` read in `Λ`-modules. -/
public def modFiberComponent (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (s : GeometricPoint Y.obj) (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B f V)
    (a : (finiteSupportDiagram B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)
      V).obj E) (x : GeometricFiberPoint B f s) :
    (modStalkFunctor.{u, v, max (u + 1) v} B Λ X (x.toGeometricPoint B f s)).obj F :=
  if h : HasFiberLift B f s V u E x then
    (geometricPointSitePoint B X.obj X.property (x.toGeometricPoint B f s)).toPresheafFiber
      (finiteSupportOpenObject B f V E)
      (openObjectLift B X.obj X.property (x.toGeometricPoint B f s) (baseChange B f V)
        (fiberPointElement B f s V u x) (finiteSupportOpen B f V E) h)
      F.obj a.val
  else 0

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
public theorem modFiberComponent_of_hasFiberLift (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (s : GeometricPoint Y.obj) (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B f V)
    (a : (finiteSupportDiagram B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)
      V).obj E) (x : GeometricFiberPoint B f s) (h : HasFiberLift B f s V u E x) :
    modFiberComponent B Λ f F s V u E a x =
      (geometricPointSitePoint B X.obj X.property (x.toGeometricPoint B f s)).toPresheafFiber
        (finiteSupportOpenObject B f V E)
        (openObjectLift B X.obj X.property (x.toGeometricPoint B f s) (baseChange B f V)
          (fiberPointElement B f s V u x) (finiteSupportOpen B f V E) h)
        F.obj a.val :=
  dite_eq_left h

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
public theorem modFiberComponent_of_not_hasFiberLift
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (s : GeometricPoint Y.obj) (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B f V)
    (a : (finiteSupportDiagram B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)
      V).obj E) (x : GeometricFiberPoint B f s) (h : ¬ HasFiberLift B f s V u E x) :
    modFiberComponent B Λ f F s V u E a x = 0 :=
  dite_eq_right h

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The `Λ`-module germ of a supported section is the abelian germ, read through the comparison
of the two `Λ`-module structures on a stalk. -/
public theorem moduleEtaleStalkIso_fiberStalkComponent
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (s : GeometricPoint Y.obj) (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B f V)
    (a : (finiteSupportDiagram B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)
      V).obj E) (x : GeometricFiberPoint B f s) :
    ((moduleEtaleStalkIso.{u, v, max (u + 1) v} B Λ X
          (x.toGeometricPoint B f s)).app F).hom
        (fiberStalkComponent.{u, max (u + 1) v} B f s
          ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V u E a x) =
      modFiberComponent B Λ f F s V u E a x := by
  by_cases h : HasFiberLift B f s V u E x
  · rw [fiberStalkComponent_of_hasFiberLift B f s
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V u E a x h,
      modFiberComponent_of_hasFiberLift B Λ f F s V u E a x h]
    exact ConcreteCategory.congr_hom
      ((geometricPointSitePoint B X.obj X.property
          (x.toGeometricPoint B f s)).toPresheafFiber_presheafFiberCompIso_hom_app
        (forget₂ (ModuleCat.{max (u + 1) v} Λ) AddCommGrpCat.{max (u + 1) v})
        (finiteSupportOpenObject B f V E)
        (openObjectLift B X.obj X.property (x.toGeometricPoint B f s) (baseChange B f V)
          (fiberPointElement B f s V u x) (finiteSupportOpen B f V E) h)
        F.obj) a.val
  · rw [fiberStalkComponent_of_not_hasFiberLift B f s
        ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F) V u E a x h,
      modFiberComponent_of_not_hasFiberLift B Λ f F s V u E a x h]
    exact map_zero _

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- The summand of the fibre comparison, with its three legs exposed. -/
public theorem modProjectionFiberSummandIso_hom (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (x : GeometricFiberPoint B f s) :
    (modProjectionFiberSummandIso.{u, v} B Λ f s F G x).hom =
      (𝟙 ((modStalkFunctor.{u, v, max (u + 1) v} B Λ X
            (x.toGeometricPoint B f s)).obj F) ⊗ₘ
          (stalkPullbackFiberIso.{u, v} B Λ f s G x).hom) ≫
        Functor.LaxMonoidal.μ ((geometricPointSitePoint B X.obj X.property
            (x.toGeometricPoint B f s)).presheafFiber) F.obj
          ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj ≫
        (geometricPointSitePoint B X.obj X.property
            (x.toGeometricPoint B f s)).presheafFiber.map
          (Stacks.ModuleSheafTensorSection.moduleToTensorSection
            (SmallEtale.topology B X.obj X.property) Λ F
            ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) :=
  rfl

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **The summand of the fibre comparison on a pure tensor of germs**, as an identity of
morphisms: the germ of `a` tensored with the germ of `t` is the germ of `a ⊗ f^{-1}t`. The two
germs are taken at the same pointed étale neighbourhood of `x̄`, which is what lets the
monoidality of the fibre functor split the germ of the pure tensor. -/
public theorem germTensor_comp_modProjectionFiberSummandIso (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (x : GeometricFiberPoint B f s)
    (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V)
    (W : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).Elements)
    (c : W.1 ⟶ baseChange B f V)
    (hc : W.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map c ≫
      B.inclusion.map (pullback.fst V.obj.hom f) = u.1) :
    ((geometricPointSitePoint B X.obj X.property
            (x.toGeometricPoint B f s)).toPresheafFiber W.1 W.2 F.obj ⊗ₘ
          (geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber V u G.obj) ≫
        (modProjectionFiberSummandIso.{u, v} B Λ f s F G x).hom =
      (𝟙 (F.obj.obj (op W.1)) ⊗ₘ (modPullbackUnitSection B Λ f G V ≫
            ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map c.op)) ≫
        (geometricPointSitePoint B X.obj X.property
            (x.toGeometricPoint B f s)).toPresheafFiber W.1 W.2
            (F.obj ⊗ ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj) ≫
          (geometricPointSitePoint B X.obj X.property
              (x.toGeometricPoint B f s)).presheafFiber.map
            (Stacks.ModuleSheafTensorSection.moduleToTensorSection
              (SmallEtale.topology B X.obj X.property) Λ F
              ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)) := by
  refine ModuleCat.hom_ext (TensorProduct.ext' fun z y => ?_)
  have hp := ConcreteCategory.congr_hom
    (stalkPullbackFiberIso_germ B Λ f s G x V u W c hc) y
  have hm := ConcreteCategory.congr_hom
    ((geometricPointSitePoint B X.obj X.property
        (x.toGeometricPoint B f s)).tensorHom_comp_toPresheafFiber_μ W.1 W.2 F.obj
      ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj)
    (z ⊗ₜ[Λ] (((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map c.op
      (modPullbackUnitSection B Λ f G V y)))
  exact congrArg
    ((geometricPointSitePoint B X.obj X.property
        (x.toGeometricPoint B f s)).presheafFiber.map
      (Stacks.ModuleSheafTensorSection.moduleToTensorSection
        (SmallEtale.topology B X.obj X.property) Λ F
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)))
    ((congrArg (fun w => Functor.LaxMonoidal.μ
          ((geometricPointSitePoint B X.obj X.property
            (x.toGeometricPoint B f s)).presheafFiber) F.obj
          ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj
        ((geometricPointSitePoint B X.obj X.property
            (x.toGeometricPoint B f s)).toPresheafFiber W.1 W.2 F.obj z ⊗ₜ[Λ] w)) hp).trans hm)

omit [LocallyOfFiniteType (B.inclusion.map f)] [LocallyQuasiFinite (B.inclusion.map f)] in
/-- **The summandwise identity behind the projection formula.** At a point `x̄` of the geometric
fibre above `ȳ`, the summand of the fibre comparison carries the germ at `x̄` of a supported
section `a`, tensored with the germ at `ȳ` of a section `t` of `G`, to the germ at `x̄` of the
supported section `a ⊗ f^{-1}t`. -/
public theorem modProjectionFiberSummandIso_germ (s : GeometricPoint Y.obj)
    (F : ModuleSheaf.{u, v, max (u + 1) v} B X Λ)
    (G : ModuleSheaf.{u, v, max (u + 1) v} B Y Λ) (V : SmallEtale B Y.obj Y.property)
    (u : (geometricPointFiber B Y.obj Y.property s).obj V) (E : FiniteSupport B f V)
    (a : (finiteSupportDiagram B f ((forgetModuleSheaf.{u, v, max (u + 1) v} B X Λ).obj F)
      V).obj E) (t : G.obj.obj (op V)) (x : GeometricFiberPoint B f s) :
    (modProjectionFiberSummandIso.{u, v} B Λ f s F G x).hom
        (modFiberComponent B Λ f F s V u E a x ⊗ₜ[Λ]
          (geometricPointSitePoint B Y.obj Y.property s).toPresheafFiber V u G.obj t) =
      modFiberComponent B Λ f (F ⊗ (modPullback.{u, v, max (u + 1) v} B Λ f).obj G) s V u E
        (tensorSupportedSectionsHom B Λ F ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G)
          (baseChange B f V) (modPullbackUnitSection B Λ f G V t) E.1
          (finiteSupport_isLocallyClosed B f V E) a) x := by
  by_cases h : HasFiberLift B f s V u E x
  · let W : (geometricPointFiber B X.obj X.property (x.toGeometricPoint B f s)).Elements :=
      ⟨finiteSupportOpenObject B f V E, openObjectLift B X.obj X.property
        (x.toGeometricPoint B f s) (baseChange B f V) (fiberPointElement B f s V u x)
        (finiteSupportOpen B f V E) h⟩
    let c := openObjectι B X.obj X.property (baseChange B f V) (finiteSupportOpen B f V E)
    have hc : W.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map c ≫
        B.inclusion.map (pullback.fst V.obj.hom f) = u.1 := by
      have hlift : W.2.1 ≫ (SmallEtale.toScheme B X.obj X.property).map c =
          fiberPointLift B f s V u x :=
        congrArg Subtype.val (openObjectLift_map B X.obj X.property
          (x.toGeometricPoint B f s) (baseChange B f V) (fiberPointElement B f s V u x)
          (finiteSupportOpen B f V E) h)
      rw [← Category.assoc, hlift]
      exact fiberPointLift_comp_fst B f s V u x
    have hpull := ConcreteCategory.congr_hom
      (stalkPullbackFiberIso_germ B Λ f s G x V u W c hc) t
    have hmu := ConcreteCategory.congr_hom
      ((geometricPointSitePoint B X.obj X.property
          (x.toGeometricPoint B f s)).tensorHom_comp_toPresheafFiber_μ W.1 W.2
        F.obj ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj)
      ((show ↥(F.obj.obj (op W.1)) from a.val) ⊗ₜ[Λ]
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G).obj.map c.op
          (modPullbackUnitSection B Λ f G V t))
    refine Eq.trans ?_ (modFiberComponent_of_hasFiberLift B Λ f _ s V u E _ x h).symm
    rw [modFiberComponent_of_hasFiberLift B Λ f F s V u E a x h,
      toPresheafFiber_tensorSupportedSectionsHom_val B Λ X F
        ((modPullback.{u, v, max (u + 1) v} B Λ f).obj G) (x.toGeometricPoint B f s)
        (baseChange B f V) (modPullbackUnitSection B Λ f G V t) E.1
        (finiteSupport_isLocallyClosed B f V E) a _,
      modProjectionFiberSummandIso_hom]
    exact ConcreteCategory.congr_hom
      (germTensor_comp_modProjectionFiberSummandIso B Λ f s F G x V u W c hc)
      ((show ↥(F.obj.obj (op W.1)) from a.val) ⊗ₜ[Λ] t)
  · refine Eq.trans ?_ (modFiberComponent_of_not_hasFiberLift B Λ f _ s V u E _ x h).symm
    rw [modFiberComponent_of_not_hasFiberLift B Λ f F s V u E a x h]
    exact Eq.trans (congrArg _ (TensorProduct.zero_tmul _ _)) (map_zero _)

end SmallEtale

end AlgebraicGeometry

end
