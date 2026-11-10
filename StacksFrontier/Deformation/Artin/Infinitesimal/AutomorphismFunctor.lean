module

public import StacksFrontier.Deformation.Artin.Infinitesimal.TangentFunctor
public import StacksFrontier.CategoryTheory.Sites.Descent.IsStack.MorPresheaf

/-!
# Infinitesimal automorphisms of the trivial deformation

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `A` be
an `S`-algebra whose spectrum lies in the site, and let `x` be an object of `𝒳` over
`Spec A`. For an `A`-module `M` write `A[M]` for the trivial square-zero extension of `A` by
`M`. The inclusion `A → A[M]` is a section of the projection `A[M] → A`, so the
corresponding retraction `Spec A[M] ⟶ Spec A` pulls `x` back to a distinguished lift of `x`
to `Spec A[M]`: the *trivial deformation* of `x`.

Its *infinitesimal automorphisms* `Inf(x'_M/x)` are the automorphisms of that lift over
`Spec A[M]` which restrict to the identity of `x`, that is, the lifts of `id_x` over
`Spec A[M]`. They form a functor of `M` with values in sets, and, when `𝒳` satisfies the
Rim–Schlessinger condition (RS*), the underlying sets of an `A`-linear functor `Inf_x`.

## Main definitions

* `Deformation.Artin.squareZeroRetraction` — the retraction `Spec A[M] ⟶ Spec A`.
* `Deformation.Artin.liftBaseId`, `Deformation.Artin.liftBaseSection`,
  `Deformation.Artin.liftBaseOverFunctor` — the trivial square-zero thickenings of `Spec A`
  as a functor of `M`, with values in the thickenings lying over the trivial one.
* `Deformation.Artin.liftId`, `Deformation.Artin.trivialDeformation` — `x` as a lift of
  itself along the identity, and its pullback along the retraction: the trivial deformation.
* `Deformation.Artin.fiberEndRestrict` — the endomorphism of the source of an arrow of a
  category fibred in groupoids determined by an endomorphism of its target.
* `Deformation.Artin.infinitesimalAutomorphismSetFunctor` — the functor
  `M ↦ Inf(x'_M/x)` with values in sets.
* `Deformation.Artin.isoFiberRestrictMap`, `Deformation.Artin.underRestrictArrow` —
  restriction of a morphism of lifts along a factorization of the base arrow, in the
  iso-fibre of a pullback functor and in the fibre of lifts.
* `Deformation.Artin.InfinitesimalAutomorphismFunctorData` — an `A`-linear functor on the
  site modules together with its identification with the infinitesimal automorphisms.
* `Deformation.Artin.infinitesimalAutomorphismFunctor` — the chosen linear functor `Inf_x`.

## Main results

* `Deformation.Artin.infinitesimalAutomorphismSetFunctor_obj` — its value at `M` is the set
  of infinitesimal automorphisms of the trivial deformation to `Spec A[M]`.
* `Deformation.Artin.isIso_infinitesimalAutomorphism` — those endomorphisms are
  automorphisms, so the set is a group.
* `Deformation.Artin.subsingleton_infinitesimalAutomorphisms`,
  `Deformation.Artin.uniqueInfinitesimalAutomorphisms` — when the square-zero immersion is an
  isomorphism, in particular for the zero module, the group is trivial.
* `Deformation.Artin.infinitesimalAutomorphismSetFunctor_product_bijective`,
  `Deformation.Artin.infinitesimalAutomorphismSetFunctor_preservesFiniteProducts` — under
  (RS*) the set-valued functor preserves finite products.
* `Deformation.Artin.exists_infinitesimalAutomorphismFunctor` — under (RS*) the `A`-linear
  functor of infinitesimal automorphisms exists.
* `Deformation.Artin.nonempty_infinitesimalAutomorphismFunctorData_of_bijective` — it exists as
  soon as restriction to the two factors of `A[M × N]` is bijective.

## References

* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor

universe u v w

namespace Deformation.Artin

/-! ### Endomorphisms of a lift along a cartesian arrow -/

section FiberEnd

open Functor

variable {C : Type*} [Category C] {Y : Type*} [Category Y]
  (q : Y ⥤ C) (hq : q.IsFiberedInGroupoids)

include hq in
/-- The endomorphism of the source of an arrow `φ` of a category fibred in groupoids
determined by an endomorphism `θ` of its target: the unique endomorphism of the source lying
over the identity whose composite with `φ` is `φ ≫ θ`. -/
public def fiberEndRestrict {U V : C} {g : V ⟶ U} {a : q.Fiber U} {b : q.Fiber V}
    (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) (θ : a ⟶ a) : b ⟶ b :=
  haveI := hφ
  haveI : q.IsCartesian g φ :=
    (hq.isStronglyCartesian_homLift g φ).isCartesian_of_isStronglyCartesian
  haveI : q.IsHomLift (𝟙 U) (Fiber.fiberInclusion.map θ) := θ.2
  haveI : q.IsHomLift g (φ ≫ Fiber.fiberInclusion.map θ) := by
    simpa only [Category.comp_id] using
      (inferInstance : q.IsHomLift (g ≫ 𝟙 U) (φ ≫ Fiber.fiberInclusion.map θ))
  ⟨IsCartesian.map q g φ (φ ≫ Fiber.fiberInclusion.map θ), inferInstance⟩

/-- An arrow lying over a base arrow is cartesian when the category is fibred in groupoids. -/
private theorem isCartesian_of_isHomLift (hq : q.IsFiberedInGroupoids) {U V : C} {g : V ⟶ U}
    {a b : Y} (φ : b ⟶ a) (hφ : q.IsHomLift g φ) : q.IsCartesian g φ :=
  have := hφ
  (hq.isStronglyCartesian_homLift g φ).isCartesian_of_isStronglyCartesian

/-- An arrow over `g` followed by a fibre morphism still lies over `g`. -/
private theorem isHomLift_comp_fiberInclusion_map {U V : C} {g : V ⟶ U} {a a' : q.Fiber U}
    {b : q.Fiber V} (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) (θ : a ⟶ a') :
    q.IsHomLift g (φ ≫ Fiber.fiberInclusion.map θ) := by
  have := hφ
  have : q.IsHomLift (𝟙 U) (Fiber.fiberInclusion.map θ) := θ.2
  simpa only [Category.comp_id] using
    (inferInstance : q.IsHomLift (g ≫ 𝟙 U) (φ ≫ Fiber.fiberInclusion.map θ))

include hq in
/-- The defining square of `Deformation.Artin.fiberEndRestrict` commutes. -/
public theorem fiberEndRestrict_fac {U V : C} {g : V ⟶ U} {a : q.Fiber U} {b : q.Fiber V}
    (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) (θ : a ⟶ a) :
    Fiber.fiberInclusion.map (fiberEndRestrict q hq φ hφ θ) ≫ φ =
      φ ≫ Fiber.fiberInclusion.map θ :=
  have := isCartesian_of_isHomLift q hq φ hφ
  have := isHomLift_comp_fiberInclusion_map q φ hφ θ
  IsCartesian.fac q g φ (φ ≫ Fiber.fiberInclusion.map θ)

include hq in
/-- The defining square determines `Deformation.Artin.fiberEndRestrict`. -/
public theorem fiberEndRestrict_eq {U V : C} {g : V ⟶ U} {a : q.Fiber U} {b : q.Fiber V}
    (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) (θ : a ⟶ a) (χ : b ⟶ b)
    (hχ : Fiber.fiberInclusion.map χ ≫ φ = φ ≫ Fiber.fiberInclusion.map θ) :
    χ = fiberEndRestrict q hq φ hφ θ :=
  fiber_hom_ext_of_cartesian g φ (isCartesian_of_isHomLift q hq φ hφ) χ _
    (by rw [hχ, fiberEndRestrict_fac])

include hq in
/-- Restriction along an identity arrow does nothing. -/
public theorem fiberEndRestrict_id {U : C} {a : q.Fiber U} (θ : a ⟶ a) :
    fiberEndRestrict q hq (𝟙 a.1) (IsHomLift.id a.2) θ = θ :=
  (fiberEndRestrict_eq q hq (𝟙 a.1) (IsHomLift.id a.2) θ θ
    ((Category.comp_id _).trans (Category.id_comp _).symm)).symm

include hq in
/-- Restriction of endomorphisms preserves the identity. -/
public theorem fiberEndRestrict_map_id {U V : C} {g : V ⟶ U} {a : q.Fiber U} {b : q.Fiber V}
    (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) :
    fiberEndRestrict q hq φ hφ (𝟙 a) = 𝟙 b :=
  (fiberEndRestrict_eq q hq φ hφ (𝟙 a) (𝟙 b) (by
    rw [CategoryTheory.Functor.map_id, CategoryTheory.Functor.map_id, Category.id_comp]
    exact (Category.comp_id φ).symm)).symm

include hq in
/-- Restriction of endomorphisms preserves composition: it is a homomorphism of monoids
from the endomorphisms of the target to those of the source. -/
public theorem fiberEndRestrict_map_comp {U V : C} {g : V ⟶ U} {a : q.Fiber U}
    {b : q.Fiber V} (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) (θ θ' : a ⟶ a) :
    fiberEndRestrict q hq φ hφ (θ ≫ θ') =
      fiberEndRestrict q hq φ hφ θ ≫ fiberEndRestrict q hq φ hφ θ' :=
  (fiberEndRestrict_eq q hq φ hφ (θ ≫ θ') _ (by
    rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp, Category.assoc,
      fiberEndRestrict_fac q hq φ hφ θ', ← Category.assoc,
      fiberEndRestrict_fac q hq φ hφ θ, Category.assoc])).symm

include hq in
/-- Restriction along a composite is restriction twice. -/
public theorem fiberEndRestrict_comp {U V W : C} {g : V ⟶ U} {g' : W ⟶ V}
    {a : q.Fiber U} {b : q.Fiber V} {d : q.Fiber W}
    (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) (ψ : d.1 ⟶ b.1) (hψ : q.IsHomLift g' ψ)
    (hψφ : q.IsHomLift (g' ≫ g) (ψ ≫ φ)) (θ : a ⟶ a) :
    fiberEndRestrict q hq (ψ ≫ φ) hψφ θ =
      fiberEndRestrict q hq ψ hψ (fiberEndRestrict q hq φ hφ θ) :=
  (fiberEndRestrict_eq q hq (ψ ≫ φ) hψφ θ _ (by
    rw [← Category.assoc, fiberEndRestrict_fac q hq ψ hψ, Category.assoc,
      fiberEndRestrict_fac q hq φ hφ, Category.assoc])).symm

include hq in
/-- Restriction does not depend on the chosen cartesian arrow: two cartesian arrows over one
and the same base arrow with one and the same target give conjugate restrictions. -/
public theorem fiberEndRestrict_conj {U V : C} {g : V ⟶ U} {a : q.Fiber U} {b b' : q.Fiber V}
    (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) (φ' : b'.1 ⟶ a.1) (hφ' : q.IsHomLift g φ')
    (e : b ≅ b') (he : Fiber.fiberInclusion.map e.hom ≫ φ' = φ) (θ : a ⟶ a) :
    fiberEndRestrict q hq φ hφ θ = e.hom ≫ fiberEndRestrict q hq φ' hφ' θ ≫ e.inv := by
  refine (fiberEndRestrict_eq q hq φ hφ θ _ ?_).symm
  have hinv : Fiber.fiberInclusion.map e.inv ≫ φ = φ' := by simp [← he]
  rw [Functor.map_comp, Functor.map_comp, Category.assoc, Category.assoc, hinv,
    fiberEndRestrict_fac, ← Category.assoc, he]

include hq in
/-- Restriction does not depend on the chosen arrow or on the spelling of the base arrow. -/
public theorem fiberEndRestrict_congr {U V : C} {g g' : V ⟶ U} {a : q.Fiber U}
    {b : q.Fiber V} (φ φ' : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) (hφ' : q.IsHomLift g' φ')
    (hff : φ = φ') (θ : a ⟶ a) :
    fiberEndRestrict q hq φ hφ θ = fiberEndRestrict q hq φ' hφ' θ := by
  subst hff
  exact (fiberEndRestrict_eq q hq φ hφ θ _ (fiberEndRestrict_fac q hq φ hφ' θ)).symm

/-- An arrow lying over one base arrow lies over any base arrow equal to it. -/
public theorem isHomLift_congr (p : Y ⥤ C) {U V : C} {g g' : V ⟶ U} (hg : g = g')
    {a b : Y} (φ : a ⟶ b) (h : p.IsHomLift g φ) : p.IsHomLift g' φ :=
  hg ▸ h

/-- Conjugation by an isomorphism, as a bijection between endomorphism sets. -/
public def conjEndEquiv {E : Type*} [Category E] {a a' : E} (e : a ≅ a') :
    (a ⟶ a) ≃ (a' ⟶ a') where
  toFun θ := e.inv ≫ θ ≫ e.hom
  invFun θ := e.hom ≫ θ ≫ e.inv
  left_inv θ := by simp
  right_inv θ := by simp

include hq in
/-- Restriction along an arrow followed by an isomorphism of its target is restriction along
the arrow itself, precomposed with conjugation by that isomorphism. -/
public theorem fiberEndRestrict_comp_iso {U V : C} {g : V ⟶ U} {a a' : q.Fiber U}
    {b : q.Fiber V} (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) (e : a ≅ a')
    (hφ' : q.IsHomLift g (φ ≫ Fiber.fiberInclusion.map e.hom)) (θ : a' ⟶ a') :
    fiberEndRestrict q hq (φ ≫ Fiber.fiberInclusion.map e.hom) hφ' θ =
      fiberEndRestrict q hq φ hφ (e.hom ≫ θ ≫ e.inv) := by
  have h2 : (e.hom ≫ θ ≫ e.inv) ≫ e.hom = e.hom ≫ θ := by simp
  refine (fiberEndRestrict_eq q hq _ hφ' θ _ ?_).symm
  rw [← Category.assoc, fiberEndRestrict_fac q hq φ hφ, Category.assoc,
    ← CategoryTheory.Functor.map_comp, h2, CategoryTheory.Functor.map_comp, Category.assoc]

omit hq in
/-- A cartesian arrow followed by an isomorphism of its target lies over the same base
arrow. -/
public theorem isHomLift_comp_fiberIso {U V : C} {g : V ⟶ U} {a a' : q.Fiber U}
    {b : q.Fiber V} (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift g φ) (e : a ≅ a') :
    q.IsHomLift g (φ ≫ Fiber.fiberInclusion.map e.hom) :=
  isHomLift_comp_fiberInclusion_map q φ hφ e.hom

include hq in
/-- If restriction of endomorphisms along a pair of arrows with common target `a` is a
bijection onto pairs, so is restriction along any pair of arrows over the same two base arrows
whose common target is isomorphic to `a`. -/
public theorem fiberEndRestrict_pair_bijective_of_iso {U V₁ V₂ : C}
    {β₁ : V₁ ⟶ U} {β₂ : V₂ ⟶ U} {a a' : q.Fiber U}
    {b₁ b₁' : q.Fiber V₁} {b₂ b₂' : q.Fiber V₂}
    (φ₁ : b₁.1 ⟶ a.1) (hφ₁ : q.IsHomLift β₁ φ₁)
    (φ₂ : b₂.1 ⟶ a.1) (hφ₂ : q.IsHomLift β₂ φ₂)
    (φ₁' : b₁'.1 ⟶ a'.1) (hφ₁' : q.IsHomLift β₁ φ₁')
    (φ₂' : b₂'.1 ⟶ a'.1) (hφ₂' : q.IsHomLift β₂ φ₂') (e : a ≅ a')
    (hbij : Function.Bijective (fun θ : a ⟶ a =>
      (fiberEndRestrict q hq φ₁ hφ₁ θ, fiberEndRestrict q hq φ₂ hφ₂ θ))) :
    Function.Bijective (fun θ : a' ⟶ a' =>
      (fiberEndRestrict q hq φ₁' hφ₁' θ, fiberEndRestrict q hq φ₂' hφ₂' θ)) := by
  have key : ∀ {V : C} {β : V ⟶ U} {b b' : q.Fiber V} (φ : b.1 ⟶ a.1) (hφ : q.IsHomLift β φ)
      (φ' : b'.1 ⟶ a'.1) (hφ' : q.IsHomLift β φ'), ∃ e' : b ≅ b', ∀ θ : a' ⟶ a',
      (conjEndEquiv e').symm (fiberEndRestrict q hq φ' hφ' θ) =
        fiberEndRestrict q hq φ hφ ((conjEndEquiv e).symm θ) := by
    intro V β b b' φ hφ φ' hφ'
    have hc := isHomLift_comp_fiberIso q φ hφ e
    have hc₁ := isCartesian_of_isHomLift q hq _ hc
    have hc₂ := isCartesian_of_isHomLift q hq _ hφ'
    refine ⟨Functor.fiberIsoOfCartesian β _ φ' hc₁ hc₂, fun θ ↦ ?_⟩
    exact (fiberEndRestrict_conj q hq _ hc φ' hφ' _
        (Functor.fiberIsoOfCartesian_hom_fac β _ φ' hc₁ hc₂) θ).symm.trans
      (fiberEndRestrict_comp_iso q hq φ hφ e hc θ)
  obtain ⟨e₁, hk₁⟩ := key φ₁ hφ₁ φ₁' hφ₁'
  obtain ⟨e₂, hk₂⟩ := key φ₂ hφ₂ φ₂' hφ₂'
  have hcomp : (Equiv.prodCongr (conjEndEquiv e₁).symm (conjEndEquiv e₂).symm) ∘
      (fun θ : a' ⟶ a' ↦
        (fiberEndRestrict q hq φ₁' hφ₁' θ, fiberEndRestrict q hq φ₂' hφ₂' θ)) =
      (fun θ : a ⟶ a ↦
        (fiberEndRestrict q hq φ₁ hφ₁ θ, fiberEndRestrict q hq φ₂ hφ₂ θ)) ∘
        (conjEndEquiv e).symm :=
    funext fun θ ↦ Prod.ext (hk₁ θ) (hk₂ θ)
  refine (Function.Bijective.of_comp_iff'
    (Equiv.prodCongr (conjEndEquiv e₁).symm (conjEndEquiv e₂).symm).bijective _).mp ?_
  rw [hcomp]
  exact hbij.comp (conjEndEquiv e).symm.bijective

include hq in
/-- Restricting a section of the presheaf of endomorphisms of `x` along an arrow of the base
slice is restriction of endomorphisms along the canonical comparison of chosen pullbacks. -/
public theorem morRestrict_eq_fiberEndRestrict [q.IsFibered] {U : C} (x : q.Fiber U)
    {g₁ g₂ : Over U} (h : g₁ ⟶ g₂)
    (m : Functor.pullbackFiber q x g₂.hom ⟶ Functor.pullbackFiber q x g₂.hom) :
    Functor.morRestrict q x x h m =
      fiberEndRestrict q hq (Functor.pullbackFiberMap q x h)
        (Functor.pullbackFiberMap_isHomLift q x h) m := by
  refine (Functor.morRestrict_uniq q x x h m _ ?_).symm
  rw [← Functor.pullbackFiberMap_fac q x h, ← Category.assoc,
    fiberEndRestrict_fac q hq _ _ m, Category.assoc]

/-- A choice of cartesian lifts for the fibred category of lifts under `x`. -/
public def underPostPullbacks (p : Y ⥤ C) (x : Y) (hp : p.IsFiberedInGroupoids) :
    (Under.post p : Under x ⥤ Under (p.obj x)).ChoiceOfPullbacks :=
  letI : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  Functor.chosenPullbacks _

end FiberEnd

/-! ### Restriction of infinitesimal automorphisms along a factorization -/

section IsoFiberRestriction

open Functor

variable {C : Type*} [Category C] {D : Type*} [Category D]
  (p : D ⥤ C) (hp : p.IsFiberedInGroupoids) (c : p.ChoiceOfPullbacks)
  {U V : C} (f : U ⟶ V) (x : p.Fiber U)

omit hp in
/-- The chosen pullback along `i` of the underlying morphism of a morphism of the iso-fibre
over `k` is compatible with the identifications of the restricted objects. -/
public theorem isoFiberRestrictMap_w {W : C} (i : V ⟶ W) (k : U ⟶ W) (h : f ≫ i = k)
    {s t : Functor.IsoFiber (c.pullbackFunctor k) x} (m : s ⟶ t) :
    (c.pullbackFunctor f).map (c.homMap i m.hom.left) ≫
        (isoFiberRestrict p c f x i k h t).obj.hom =
      (isoFiberRestrict p c f x i k h s).obj.hom := by
  subst h
  have hm : c.homMap (f ≫ i) m.hom.left ≫ t.obj.hom = s.obj.hom := CostructuredArrow.w m.hom
  have hfe : c.homMap f (c.homMap i m.hom.left) =
      (c.objCompIso f i s.obj.left).inv ≫ c.homMap (f ≫ i) m.hom.left ≫
        (c.objCompIso f i t.obj.left).hom := by
    rw [c.objCompIso_hom_naturality f i m.hom.left, Iso.inv_hom_id_assoc]
  change c.homMap f (c.homMap i m.hom.left) ≫
      (isoFiberRestrict p c f x i (f ≫ i) rfl t).obj.hom =
    (isoFiberRestrict p c f x i (f ≫ i) rfl s).obj.hom
  rw [hfe]
  simp only [isoFiberRestrict, CostructuredArrow.mk_hom_eq_self, eqToHom_refl,
    Category.id_comp, Category.assoc, Iso.hom_inv_id_assoc, hm]

omit hp f in
/-- An endomorphism of an object of an iso-fibre is the identity after the pullback
functor. -/
public theorem isoFiber_pullbackFunctor_map_hom_left {V' : C} {f' : U ⟶ V'}
    {s : Functor.IsoFiber (c.pullbackFunctor f') x} (u : s ⟶ s) :
    (c.pullbackFunctor f').map u.hom.left = 𝟙 _ := by
  have : IsIso s.obj.hom := s.property
  exact (cancel_mono s.obj.hom).1 ((CostructuredArrow.w u.hom).trans (Category.id_comp _).symm)

omit hp in
/-- Restriction along `i` of a morphism of the iso-fibre of the pullback functor along a
factorization `f ≫ i = k`: the chosen pullback along `i` of the underlying morphism. -/
public def isoFiberRestrictMap {W : C} (i : V ⟶ W) (k : U ⟶ W) (h : f ≫ i = k)
    {s t : Functor.IsoFiber (c.pullbackFunctor k) x} (m : s ⟶ t) :
    isoFiberRestrict p c f x i k h s ⟶ isoFiberRestrict p c f x i k h t :=
  ObjectProperty.homMk (CostructuredArrow.homMk (c.homMap i m.hom.left)
    (isoFiberRestrictMap_w p c f x i k h m))

omit hp in
/-- The cartesian arrow of lifts from the restriction along `i` of a lift to the lift
itself. -/
public def underRestrictArrow {W : C} (i : V ⟶ W) (k : U ⟶ W) (h : f ≫ i = k)
    (t : Functor.IsoFiber (c.pullbackFunctor k) x) :
    (isoFiberToUnderObj p c f x (isoFiberRestrict p c f x i k h t)).1 ⟶
      (isoFiberToUnderObj p c k x t).1 :=
  Under.homMk (c.map i t.obj.left) (isoFiberRestrict_fac p c f x i k h t)

omit hp in
/-- The arrow of `Deformation.Artin.underRestrictArrow` lies over the base arrow given by
`i`. -/
public theorem underRestrictArrow_isHomLift {W : C} (i : V ⟶ W) (k : U ⟶ W) (h : f ≫ i = k)
    (t : Functor.IsoFiber (c.pullbackFunctor k) x) :
    (Under.post p).IsHomLift (underBaseMap p f x i k h)
      (underRestrictArrow p c f x i k h t) := by
  apply IsHomLift.of_fac' _ _ _ (isoFiberToUnderObj p c f x _).2
    (isoFiberToUnderObj p c k x t).2
  apply Under.UnderMorphism.ext
  change p.map (c.map i t.obj.left) = _
  simp only [Under.comp_right, Under.eqToHom_right, underBaseMap, Under.homMk_right]
  exact IsHomLift.fac' p i (c.map i t.obj.left)

include hp in
/-- The comparison to the fibre of lifts turns restriction along `i` in the iso-fibre into
restriction of endomorphisms along the cartesian arrow of the restricted lift. -/
public theorem isoFiberToUnder_map_isoFiberRestrictMap {W : C} (i : V ⟶ W) (k : U ⟶ W)
    (h : f ≫ i = k) (t : Functor.IsoFiber (c.pullbackFunctor k) x) (θ : t ⟶ t) :
    (isoFiberToUnder p c f x).map (isoFiberRestrictMap p c f x i k h θ) =
      fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x.1)
        (underRestrictArrow p c f x i k h t)
        (underRestrictArrow_isHomLift p c f x i k h t) ((isoFiberToUnder p c k x).map θ) := by
  refine fiberEndRestrict_eq (Under.post p) (underPost_isFiberedInGroupoids p hp x.1) _
    (underRestrictArrow_isHomLift p c f x i k h t) _ _ ?_
  apply Under.UnderMorphism.ext
  exact c.homMap_fac i θ.hom.left

omit hp in
/-- The comparison to the fibre of lifts is a bijection on endomorphism sets. -/
public theorem isoFiberToUnder_map_bijective (t : Functor.IsoFiber (c.pullbackFunctor f) x) :
    Function.Bijective (fun θ : t ⟶ t => (isoFiberToUnder p c f x).map θ) := by
  have := isoFiberToUnder_full p c f x
  have := isoFiberToUnder_faithful p c f x
  exact ⟨(isoFiberToUnder p c f x).map_injective, (isoFiberToUnder p c f x).map_surjective⟩

omit hp in
/-- The comparison functor of a square in the base sends a morphism to the pair of its
chosen pullbacks along the two legs. -/
public theorem fiberSquareComparison_map {W Z : C} (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (h : f ≫ i = g ≫ j) {z z' : p.Fiber Z} (m : z ⟶ z') :
    ((fiberSquareComparison p c f g i j h).map m).fst = c.homMap i m ∧
      ((fiberSquareComparison p c f g i j h).map m).snd = c.homMap j m :=
  ⟨rfl, rfl⟩

omit hp in
/-- If the comparison functor of a square in the base is an equivalence, restriction along the
two legs is a bijection from the endomorphisms of an object of the iso-fibre over the fourth
corner to pairs of endomorphisms of its two restrictions. -/
public theorem isoFiberRestrictMap_bijective {W Z : C} (g : U ⟶ W) (i : V ⟶ Z) (j : W ⟶ Z)
    (h : f ≫ i = g ≫ j) (k : U ⟶ Z) (hk : f ≫ i = k)
    (hE : (fiberSquareComparison p c f g i j h).IsEquivalence)
    (t : Functor.IsoFiber (c.pullbackFunctor k) x) :
    Function.Bijective (fun θ : t ⟶ t =>
      (isoFiberRestrictMap p c f x i k hk θ,
        isoFiberRestrictMap p c g x j k (h.symm.trans hk) θ)) := by
  subst hk
  have := hE
  have hfull : (fiberSquareComparison p c f g i j h).Full := inferInstance
  refine ⟨fun θ θ' hθ ↦ ?_, fun uv ↦ ?_⟩
  · apply ObjectProperty.hom_ext
    apply CostructuredArrow.hom_ext
    refine (fiberSquareComparison p c f g i j h).map_injective
      (a₁ := θ.hom.left) (a₂ := θ'.hom.left) ?_
    exact Limits.CategoricalPullback.Hom.ext (congrArg (fun r ↦ r.1.hom.left) hθ)
      (congrArg (fun r ↦ r.2.hom.left) hθ)
  · obtain ⟨u, v⟩ := uv
    let I := ((fiberSquareComparison p c f g i j h).obj t.obj.left).iso.hom
    let Ψ : (fiberSquareComparison p c f g i j h).obj t.obj.left ⟶
        (fiberSquareComparison p c f g i j h).obj t.obj.left :=
      { fst := u.hom.left
        snd := v.hom.left
        w := ((congrArg (fun y ↦ y ≫ I)
              (isoFiber_pullbackFunctor_map_hom_left p c x u)).trans
            (Category.id_comp I)).trans
          ((Category.comp_id I).symm.trans
            (congrArg (fun y ↦ I ≫ y)
              (isoFiber_pullbackFunctor_map_hom_left p c x v)).symm) }
    obtain ⟨m, hm⟩ := hfull.map_surjective Ψ
    have hmi : c.homMap i m = u.hom.left :=
      ((fiberSquareComparison_map p c f g i j h m).1).symm.trans
        (congrArg (fun y ↦ y.fst) hm)
    have hmj : c.homMap j m = v.hom.left :=
      ((fiberSquareComparison_map p c f g i j h m).2).symm.trans
        (congrArg (fun y ↦ y.snd) hm)
    have hu2 : c.homMap f (c.homMap i m) = 𝟙 (c.obj f (c.obj i t.obj.left)) := by
      rw [hmi]
      exact isoFiber_pullbackFunctor_map_hom_left p c x u
    have hmk : c.homMap (f ≫ i) m = 𝟙 (c.obj (f ≫ i) t.obj.left) := by
      refine (cancel_mono (c.objCompIso f i t.obj.left).hom).1 ?_
      rw [c.objCompIso_hom_naturality f i m, hu2]
      simp
    refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk m ?_), ?_⟩
    · change c.homMap (f ≫ i) m ≫ t.obj.hom = t.obj.hom
      rw [hmk, Category.id_comp]
    · refine Prod.ext ?_ ?_ <;> apply ObjectProperty.hom_ext <;> apply CostructuredArrow.hom_ext
      exacts [hmi, hmj]

include hp in
/-- Under (RS*) for a square in the base, restriction of endomorphisms of a lift along the two
legs is a bijection onto pairs of endomorphisms of the two restricted lifts. -/
public theorem fiberEndRestrict_underRestrictArrow_bijective {W Z : C} (g : U ⟶ W)
    (i : V ⟶ Z) (j : W ⟶ Z) (h : f ≫ i = g ≫ j) (k : U ⟶ Z) (hk : f ≫ i = k)
    (hE : (fiberSquareComparison p c f g i j h).IsEquivalence)
    (t : Functor.IsoFiber (c.pullbackFunctor k) x) :
    Function.Bijective
      (fun θ : isoFiberToUnderObj p c k x t ⟶ isoFiberToUnderObj p c k x t =>
        (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x.1)
            (underRestrictArrow p c f x i k hk t)
            (underRestrictArrow_isHomLift p c f x i k hk t) θ,
          fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x.1)
            (underRestrictArrow p c g x j k (h.symm.trans hk) t)
            (underRestrictArrow_isHomLift p c g x j k (h.symm.trans hk) t) θ)) := by
  have hbij := isoFiberRestrictMap_bijective p c f x g i j h k hk hE t
  have hG := isoFiberToUnder_map_bijective p c k x t
  have hG₁ := isoFiberToUnder_map_bijective p c f x (isoFiberRestrict p c f x i k hk t)
  have hG₂ := isoFiberToUnder_map_bijective p c g x
    (isoFiberRestrict p c g x j k (h.symm.trans hk) t)
  have hstep : ∀ η : t ⟶ t,
      (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x.1)
          (underRestrictArrow p c f x i k hk t)
          (underRestrictArrow_isHomLift p c f x i k hk t)
          ((isoFiberToUnder p c k x).map η),
        fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x.1)
          (underRestrictArrow p c g x j k (h.symm.trans hk) t)
          (underRestrictArrow_isHomLift p c g x j k (h.symm.trans hk) t)
          ((isoFiberToUnder p c k x).map η)) =
      ((isoFiberToUnder p c f x).map (isoFiberRestrictMap p c f x i k hk η),
        (isoFiberToUnder p c g x).map
          (isoFiberRestrictMap p c g x j k (h.symm.trans hk) η)) := fun η ↦
    Prod.ext (isoFiberToUnder_map_isoFiberRestrictMap p hp c f x i k hk t η).symm
      (isoFiberToUnder_map_isoFiberRestrictMap p hp c g x j k (h.symm.trans hk) t η).symm
  refine ⟨fun θ θ' hθ ↦ ?_, fun χ ↦ ?_⟩
  · obtain ⟨η, rfl⟩ := hG.2 θ
    obtain ⟨η', rfl⟩ := hG.2 θ'
    have hθ' := (hstep η).symm.trans (hθ.trans (hstep η'))
    exact congrArg _ (hbij.1 (Prod.ext (hG₁.1 (congrArg Prod.fst hθ'))
      (hG₂.1 (congrArg Prod.snd hθ'))))
  · obtain ⟨χ₁, χ₂⟩ := χ
    obtain ⟨u, rfl⟩ := hG₁.2 χ₁
    obtain ⟨v, rfl⟩ := hG₂.2 χ₂
    obtain ⟨η, hη⟩ := hbij.2 (u, v)
    obtain ⟨rfl, rfl⟩ := Prod.mk.inj hη
    exact ⟨_, hstep η⟩

end IsoFiberRestriction

/-! ### The trivial deformation -/

section TrivialDeformation

open Functor

variable (A : Type u) [CommRing A] (B : BigFppfSite.{u}) (S : Scheme.{u})
  (hS : B.Contains S) (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))

/-- The retraction `Spec A[M] ⟶ Spec A` induced by the inclusion `A → A[M]`. -/
public def squareZeroRetraction (M : SiteModule A B) :
    squareZeroOver A B S hS toS M ⟶ algebraOver A B S hS toS hA := by
  refine Over.homMk (ObjectProperty.homMk
    (Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj))) :
      B.obj M.property ⟶ B.obj hA) ?_
  apply ObjectProperty.hom_ext
  rfl

/-- The retraction is a section of the square-zero closed immersion. -/
public theorem squareZeroArrow_comp_squareZeroRetraction (M : SiteModule A B) :
    squareZeroArrow A B S hS toS hA M ≫ squareZeroRetraction A B S hS toS hA M =
      𝟙 (algebraOver A B S hS toS hA) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) = 𝟙 _
  rw [← Spec.map_comp]
  have h : CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj) ≫
      CommRingCat.ofHom (TrivSqZeroExt.fstHom A A M.obj).toRingHom =
        𝟙 (CommRingCat.of A) := by
    apply CommRingCat.hom_ext
    ext a
    simp
  rw [h, Spec.map_id]

/-- The retractions are compatible with the maps of trivial square-zero extensions. -/
public theorem squareZeroOverMap_comp_squareZeroRetraction {M N : SiteModule A B} (f : M ⟶ N) :
    squareZeroOverMap A B S hS toS f ≫ squareZeroRetraction A B S hS toS hA M =
      squareZeroRetraction A B S hS toS hA N := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map f.hom.hom).toRingHom) ≫
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) =
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A N.obj))
  rw [← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  · simp
  · change (TrivSqZeroExt.map f.hom.hom (TrivSqZeroExt.inl a)).snd =
      (TrivSqZeroExt.inl a).snd
    rw [TrivSqZeroExt.map_inl]

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)

/-- The trivial thickening of `Spec A`: the base of the lifts of `x` to `Spec A` itself. -/
public abbrev liftBaseId : Under (p.obj x) := Under.mk (eqToHom hx)

/-- The retraction, read as a morphism of thickenings of `Spec A` under `x`. -/
public def liftBaseSection (M : SiteModule A B) :
    (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj x)) ⟶
      liftBaseId A B S hS toS hA p x hx :=
  Under.homMk (squareZeroRetraction A B S hS toS hA M) (by
    change (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) ≫
      squareZeroRetraction A B S hS toS hA M = eqToHom hx
    rw [Category.assoc, squareZeroArrow_comp_squareZeroRetraction, Category.comp_id])

/-- The map of base thickenings induced by a module map. -/
public def liftBaseThickeningMap {M N : SiteModule A B} (f : M ⟶ N) :
    (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA N) : Under (p.obj x)) ⟶
      Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) :=
  Under.homMk (squareZeroOverMap A B S hS toS f) (by
    change (eqToHom hx ≫ squareZeroArrow A B S hS toS hA N) ≫
      squareZeroOverMap A B S hS toS f = eqToHom hx ≫ squareZeroArrow A B S hS toS hA M
    rw [Category.assoc, squareZeroArrow_naturality])

/-- The retractions are compatible with the maps of base thickenings. -/
public theorem liftBaseThickeningMap_comp_liftBaseSection {M N : SiteModule A B} (f : M ⟶ N) :
    liftBaseThickeningMap A B S hS toS hA p x hx f ≫
        liftBaseSection A B S hS toS hA p x hx M =
      liftBaseSection A B S hS toS hA p x hx N :=
  Under.UnderMorphism.ext (squareZeroOverMap_comp_squareZeroRetraction A B S hS toS hA f)

/-- `x` itself, as a lift of `x` along the trivial thickening. -/
public def liftId : (Under.post p).Fiber (liftBaseId A B S hS toS hA p x hx) := by
  refine ⟨Under.mk (𝟙 x), ?_⟩
  refine StructuredArrow.obj_ext _ _ hx ?_
  change p.map (𝟙 x) ≫ eqToHom hx = eqToHom hx
  rw [p.map_id, Category.id_comp]

variable (hp : p.IsFiberedInGroupoids)

include hp in
/-- The trivial deformation of `x` to `Spec A[M]`: the pullback of `x` along the retraction
`Spec A[M] ⟶ Spec A`, together with its identification with `x` over `Spec A`. -/
public def trivialDeformation (M : SiteModule A B) :
    (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj x)) :=
  letI : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  Functor.pullbackFiber (Under.post p) (liftId A B S hS toS hA p x hx)
    (liftBaseSection A B S hS toS hA p x hx M)

/-- The chosen cartesian arrow exhibiting the trivial deformation as a pullback of `x`. -/
public def trivialDeformationMap (M : SiteModule A B) :
    (trivialDeformation A B S hS toS hA p x hx hp M).1 ⟶
      (liftId A B S hS toS hA p x hx).1 :=
  letI : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  Functor.IsPreFibered.pullbackMap (liftId A B S hS toS hA p x hx).2
    (liftBaseSection A B S hS toS hA p x hx M)

/-! ### Functoriality -/

/-- The map of base thickenings attached to an identity is the identity. -/
public theorem liftBaseThickeningMap_id (M : SiteModule A B) :
    liftBaseThickeningMap A B S hS toS hA p x hx (𝟙 M) =
      𝟙 (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj x)) :=
  Under.UnderMorphism.ext (squareZeroOverMap_id A B S hS toS M)

/-- The maps of base thickenings compose contravariantly. -/
public theorem liftBaseThickeningMap_comp {M N P : SiteModule A B} (f : M ⟶ N) (g : N ⟶ P) :
    liftBaseThickeningMap A B S hS toS hA p x hx (f ≫ g) =
      liftBaseThickeningMap A B S hS toS hA p x hx g ≫
        liftBaseThickeningMap A B S hS toS hA p x hx f :=
  Under.UnderMorphism.ext (squareZeroOverMap_comp A B S hS toS f g)

/-- `Spec A[M]`, with its retraction, as a thickening of `Spec A` over the trivial one. -/
public def liftBaseOver (M : SiteModule A B) : Over (liftBaseId A B S hS toS hA p x hx) :=
  Over.mk (liftBaseSection A B S hS toS hA p x hx M)

/-- The map of thickenings over `Spec A` induced by a module map. -/
public def liftBaseOverMap {M N : SiteModule A B} (f : M ⟶ N) :
    liftBaseOver A B S hS toS hA p x hx N ⟶ liftBaseOver A B S hS toS hA p x hx M :=
  Over.homMk (liftBaseThickeningMap A B S hS toS hA p x hx f)
    (liftBaseThickeningMap_comp_liftBaseSection A B S hS toS hA p x hx f)

/-- The trivial square-zero thickenings of `Spec A`, as a functor of the module. -/
public def liftBaseOverFunctor :
    SiteModule A B ⥤ (Over (liftBaseId A B S hS toS hA p x hx))ᵒᵖ where
  obj M := Opposite.op (liftBaseOver A B S hS toS hA p x hx M)
  map f := (liftBaseOverMap A B S hS toS hA p x hx f).op
  map_id M := Quiver.Hom.unop_inj (Over.OverMorphism.ext
    (liftBaseThickeningMap_id A B S hS toS hA p x hx M))
  map_comp f g := Quiver.Hom.unop_inj (Over.OverMorphism.ext
    (liftBaseThickeningMap_comp A B S hS toS hA p x hx f g))

/-- The functor `Inf_x` with values in sets: the infinitesimal automorphisms of the trivial
deformation of `x` to `Spec A[M]` — the automorphisms of that deformation over `Spec A[M]` which
restrict to the identity of `x` — as a functor of `M`. -/
public def infinitesimalAutomorphismSetFunctor : SiteModule A B ⥤ Type w :=
  letI : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  liftBaseOverFunctor A B S hS toS hA p x hx ⋙
    Functor.morPresheaf (Under.post p) (liftId A B S hS toS hA p x hx)
      (liftId A B S hS toS hA p x hx)

/-- The value of `Inf_x` at `M` is the set of infinitesimal automorphisms of the trivial
deformation of `x` to `Spec A[M]`. -/
public theorem infinitesimalAutomorphismSetFunctor_obj (M : SiteModule A B) :
    (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).obj M =
      (trivialDeformation A B S hS toS hA p x hx hp M ⟶
        trivialDeformation A B S hS toS hA p x hx hp M) :=
  rfl

/-! ### Infinitesimal automorphisms are automorphisms -/

/-- Every infinitesimal automorphism of the trivial deformation is an isomorphism, so
`Inf_x(M)` is a group. -/
public theorem isIso_infinitesimalAutomorphism (M : SiteModule A B)
    (θ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) : IsIso θ :=
  have : CategoryTheory.IsGroupoid ((Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj x))) :=
    (underPost_isFiberedInGroupoids p hp x).fiber_isGroupoid _
  CategoryTheory.IsGroupoid.all_isIso θ

/-- A lift of `x` along the square-zero immersion lies over that immersion. -/
private theorem liftFiber_isHomLift (M : SiteModule A B)
    (a : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj x))) :
    p.IsHomLift (squareZeroArrow A B S hS toS hA M) a.1.hom := by
  have hy : p.obj a.1.right = squareZeroOver A B S hS toS M := congrArg Under.right a.2
  apply IsHomLift.of_fac p (squareZeroArrow A B S hS toS hA M) a.1.hom hx hy
  have hw := Under.w (eqToHom a.2)
  simp only [Under.eqToHom_right] at hw
  change p.map a.1.hom ≫ eqToHom hy = eqToHom hx ≫ squareZeroArrow A B S hS toS hA M at hw
  rw [hw]
  simp

include hp in
/-- When the square-zero immersion `Spec A ⟶ Spec A[M]` is an isomorphism — for instance for
the zero module — a lift of `x` to `Spec A[M]` has no non-trivial infinitesimal automorphism:
`Inf_x(M)` is trivial. -/
public theorem subsingleton_infinitesimalAutomorphisms (M : SiteModule A B)
    (hiso : IsIso (squareZeroArrow A B S hS toS hA M))
    (a : (Under.post p).Fiber
      (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M) : Under (p.obj x))) :
    Subsingleton (a ⟶ a) := by
  have := hiso
  have : p.IsHomLift (squareZeroArrow A B S hS toS hA M) a.1.hom :=
    liftFiber_isHomLift A B S hS toS hA p x hx M a
  have : p.IsStronglyCartesian (squareZeroArrow A B S hS toS hA M) a.1.hom :=
    hp.isStronglyCartesian_homLift _ _
  have : IsIso a.1.hom :=
    Functor.IsStronglyCartesian.isIso_of_base_isIso p
      (squareZeroArrow A B S hS toS hA M) a.1.hom
  refine ⟨fun θ η ↦ ?_⟩
  apply Functor.Fiber.hom_ext
  apply Under.UnderMorphism.ext
  apply (cancel_epi a.1.hom).1
  exact (Under.w (Functor.Fiber.fiberInclusion.map θ)).trans
    (Under.w (Functor.Fiber.fiberInclusion.map η)).symm

/-- The infinitesimal automorphisms of the trivial deformation along a square-zero immersion
which is an isomorphism form a one-element set: this is the value of `Inf_x` at the zero
module. -/
@[instance_reducible]
public def uniqueInfinitesimalAutomorphisms (M : SiteModule A B)
    (hiso : IsIso (squareZeroArrow A B S hS toS hA M)) :
    Unique (trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :=
  haveI := subsingleton_infinitesimalAutomorphisms A B S hS toS hA p x hx hp M hiso
    (trivialDeformation A B S hS toS hA p x hx hp M)
  ⟨⟨𝟙 _⟩, fun _ ↦ Subsingleton.elim _ _⟩

/-! ### The linear structure on the infinitesimal automorphisms -/

include hp in
/-- The transition map of `Inf_x` along a module map is restriction of endomorphisms along
the canonical comparison of the two trivial deformations. -/
public theorem infinitesimalAutomorphismSetFunctor_map {M N : SiteModule A B} (f : M ⟶ N) :
    letI : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
    ∀ θ : (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).obj M,
      (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map f θ =
        fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x)
          (Functor.pullbackFiberMap (Under.post p) (liftId A B S hS toS hA p x hx)
            (liftBaseOverMap A B S hS toS hA p x hx f))
          (Functor.pullbackFiberMap_isHomLift _ _ _) θ := by
  let : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  intro θ
  exact morRestrict_eq_fiberEndRestrict (Under.post p)
    (underPost_isFiberedInGroupoids p hp x) (liftId A B S hS toS hA p x hx)
    (liftBaseOverMap A B S hS toS hA p x hx f) θ

omit hp in
/-- The base arrow of the restriction of lifts along a module map is the arrow of base
thickenings induced by that map. -/
public theorem underBaseMap_eq_liftBaseOverMap_left {M N : SiteModule A B} (g : M ⟶ N)
    (hg : squareZeroArrow A B S hS toS hA N ≫ squareZeroOverMap A B S hS toS g =
      squareZeroArrow A B S hS toS hA M) :
    underBaseMap p (squareZeroArrow A B S hS toS hA N)
        (⟨x, hx⟩ : p.Fiber (algebraOver A B S hS toS hA))
        (squareZeroOverMap A B S hS toS g) (squareZeroArrow A B S hS toS hA M) hg =
      (liftBaseOverMap A B S hS toS hA p x hx g).left :=
  Under.UnderMorphism.ext rfl

include hp in
/-- Under (RS*), restriction to the two factors is a bijection from the infinitesimal
automorphisms of the trivial deformation over `A[M × N]` to pairs of infinitesimal automorphisms
over `A[M]` and `A[N]`. -/
public theorem infinitesimalAutomorphismSetFunctor_product_bijective
    (hRS : SatisfiesRSStar B S hS p hp) (M N : SiteModule A B) :
    Function.Bijective (fun θ :
        (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).obj
          (siteModuleProd A B hA M N) =>
      ((infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map
          (siteModuleFst A B hA M N) θ,
        (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map
          (siteModuleSnd A B hA M N) θ)) := by
  let : p.IsFibered := hp.isFibered
  let : (Under.post p : Under x ⥤ Under (p.obj x)).IsFibered := underPost_isFibered p hp x
  have hsq : squareZeroArrow A B S hS toS hA M ≫
        squareZeroOverMap A B S hS toS (siteModuleFst A B hA M N) =
      squareZeroArrow A B S hS toS hA N ≫
        squareZeroOverMap A B S hS toS (siteModuleSnd A B hA M N) :=
    (squareZeroArrow_naturality A B S hS toS hA _).trans
      (squareZeroArrow_naturality A B S hS toS hA _).symm
  have hk : squareZeroArrow A B S hS toS hA M ≫
        squareZeroOverMap A B S hS toS (siteModuleFst A B hA M N) =
      squareZeroArrow A B S hS toS hA (siteModuleProd A B hA M N) :=
    squareZeroArrow_naturality A B S hS toS hA _
  have hk' : squareZeroArrow A B S hS toS hA N ≫
        squareZeroOverMap A B S hS toS (siteModuleSnd A B hA M N) =
      squareZeroArrow A B S hS toS hA (siteModuleProd A B hA M N) :=
    hsq.symm.trans hk
  obtain ⟨t, ht⟩ := isoFiberToUnder_surjective p hp (Functor.chosenPullbacks p)
    (squareZeroArrow A B S hS toS hA (siteModuleProd A B hA M N))
    (⟨x, hx⟩ : p.Fiber (algebraOver A B S hS toS hA))
    (trivialDeformation A B S hS toS hA p x hx hp (siteModuleProd A B hA M N))
  have hbij := fiberEndRestrict_underRestrictArrow_bijective p hp (Functor.chosenPullbacks p)
    (squareZeroArrow A B S hS toS hA M) (⟨x, hx⟩ : p.Fiber (algebraOver A B S hS toS hA))
    (squareZeroArrow A B S hS toS hA N)
    (squareZeroOverMap A B S hS toS (siteModuleFst A B hA M N))
    (squareZeroOverMap A B S hS toS (siteModuleSnd A B hA M N)) hsq
    (squareZeroArrow A B S hS toS hA (siteModuleProd A B hA M N)) hk
    (squareZeroProd_isEquivalence A B S hS toS hA p hp hRS M N) t
  have hφ₁' := isHomLift_congr (Under.post p)
    (underBaseMap_eq_liftBaseOverMap_left A B S hS toS hA p x hx
      (siteModuleFst A B hA M N) hk).symm
    (Functor.pullbackFiberMap (Under.post p) (liftId A B S hS toS hA p x hx)
      (liftBaseOverMap A B S hS toS hA p x hx (siteModuleFst A B hA M N)))
    (Functor.pullbackFiberMap_isHomLift _ _ _)
  have hφ₂' := isHomLift_congr (Under.post p)
    (underBaseMap_eq_liftBaseOverMap_left A B S hS toS hA p x hx
      (siteModuleSnd A B hA M N) hk').symm
    (Functor.pullbackFiberMap (Under.post p) (liftId A B S hS toS hA p x hx)
      (liftBaseOverMap A B S hS toS hA p x hx (siteModuleSnd A B hA M N)))
    (Functor.pullbackFiberMap_isHomLift _ _ _)
  have hfinal := fiberEndRestrict_pair_bijective_of_iso (Under.post p)
    (underPost_isFiberedInGroupoids p hp x) _
    (underRestrictArrow_isHomLift p (Functor.chosenPullbacks p)
      (squareZeroArrow A B S hS toS hA M)
      (⟨x, hx⟩ : p.Fiber (algebraOver A B S hS toS hA))
      (squareZeroOverMap A B S hS toS (siteModuleFst A B hA M N))
      (squareZeroArrow A B S hS toS hA (siteModuleProd A B hA M N)) hk t)
    _
    (underRestrictArrow_isHomLift p (Functor.chosenPullbacks p)
      (squareZeroArrow A B S hS toS hA N)
      (⟨x, hx⟩ : p.Fiber (algebraOver A B S hS toS hA))
      (squareZeroOverMap A B S hS toS (siteModuleSnd A B hA M N))
      (squareZeroArrow A B S hS toS hA (siteModuleProd A B hA M N)) hk' t)
    _ hφ₁' _ hφ₂' (eqToIso ht) hbij
  have hpt : ∀ θ : (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).obj
        (siteModuleProd A B hA M N),
      ((infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map
          (siteModuleFst A B hA M N) θ,
        (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map
          (siteModuleSnd A B hA M N) θ) =
      (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x) _ hφ₁' θ,
        fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x) _ hφ₂' θ) :=
    fun θ ↦ Prod.ext
      (infinitesimalAutomorphismSetFunctor_map A B S hS toS hA p x hx hp
        (siteModuleFst A B hA M N) θ)
      (infinitesimalAutomorphismSetFunctor_map A B S hS toS hA p x hx hp
        (siteModuleSnd A B hA M N) θ)
  exact ⟨fun θ θ' hθ ↦ hfinal.1 ((hpt θ).symm.trans (hθ.trans (hpt θ'))),
    fun χ ↦ (hfinal.2 χ).imp fun θ ↦ (hpt θ).trans⟩

include hp in
/-- Under (RS*), `Inf_x` preserves finite products. -/
public theorem infinitesimalAutomorphismSetFunctor_preservesFiniteProducts
    (hRS : SatisfiesRSStar B S hS p hp) :
    PreservesFiniteProducts
      (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp) :=
  preservesFiniteProducts_of_product_bijective A B hA _
    (uniqueInfinitesimalAutomorphisms A B S hS toS hA p x hx hp (siteModuleZero A B hA)
      (squareZeroArrow_zero_isIso A B S hS toS hA))
    (infinitesimalAutomorphismSetFunctor_product_bijective A B S hS toS hA p x hx hp hRS)

/-- An `A`-linear functor on the site modules together with its pointwise identification
with the infinitesimal automorphisms of the trivial deformations. -/
public structure InfinitesimalAutomorphismFunctorData where
  /-- The functor `Inf_x`, linear over the base algebra. -/
  functor : SiteModule A B ⥤ ModuleCat.{w} A
  [additive : functor.Additive]
  [linear : functor.Linear A]
  /-- Its underlying sets are the infinitesimal automorphisms of the trivial deformations. -/
  autEquiv : ∀ M : SiteModule A B,
    (functor.obj M : Type w) ≃
      (trivialDeformation A B S hS toS hA p x hx hp M ⟶
        trivialDeformation A B S hS toS hA p x hx hp M)
  /-- The identifications are natural for the transition maps of the infinitesimal
  automorphisms. -/
  autEquiv_natural : ∀ {M N : SiteModule A B} (f : M ⟶ N) (θ : functor.obj M),
    autEquiv N (functor.map f θ) =
      (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map f (autEquiv M θ)

attribute [instance] InfinitesimalAutomorphismFunctorData.additive
  InfinitesimalAutomorphismFunctorData.linear

include hp in
/-- Suppose that, for all site modules `M` and `N`, restriction along the two projections is
a bijection from the infinitesimal automorphisms of the trivial deformation over `A[M × N]` to
pairs of infinitesimal automorphisms over `A[M]` and `A[N]`. Then these are the underlying sets
of an `A`-linear functor of `M`. -/
public theorem nonempty_infinitesimalAutomorphismFunctorData_of_bijective
    (hprod : ∀ M N : SiteModule A B,
      Function.Bijective (fun θ :
          (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).obj
            (siteModuleProd A B hA M N) =>
        ((infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map
            (siteModuleFst A B hA M N) θ,
          (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp).map
            (siteModuleSnd A B hA M N) θ))) :
    Nonempty (InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp) := by
  have : HasTerminal (SiteModule A B) := siteModuleHasTerminal A B hA
  have : HasZeroObject (SiteModule A B) := Limits.hasZeroObject_of_hasTerminal_object
  have : ∀ M N : SiteModule A B, HasLimit (pair M N) :=
    fun M N ↦ siteModuleHasLimitPair A B hA
  have : HasBinaryProducts (SiteModule A B) := hasBinaryProducts_of_hasLimit_pair _
  have : PreservesFiniteProducts
      (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp) :=
    preservesFiniteProducts_of_product_bijective A B hA _
      (uniqueInfinitesimalAutomorphisms A B S hS toS hA p x hx hp (siteModuleZero A B hA)
        (squareZeroArrow_zero_isIso A B S hS toS hA)) hprod
  let L := Deformation.linearFunctorLift A
    (infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp)
  let e : L.functor ⋙ forget (ModuleCat A) ≅
      infinitesimalAutomorphismSetFunctor A B S hS toS hA p x hx hp := eqToIso L.forget_comp
  exact ⟨{
    functor := L.functor
    autEquiv := fun M ↦ (e.app M).toEquiv
    autEquiv_natural := fun f θ ↦ ConcreteCategory.congr_hom (e.hom.naturality f) θ }⟩

include hp in
/-- For `𝒳` satisfying (RS*), the infinitesimal automorphisms of the trivial deformations of
`x` over the trivial square-zero extensions `A[M]` are the underlying sets of an `A`-linear
functor of `M`. -/
@[stacks 07Y9 "part (1), the A-linear functor Inf_x on trivial square-zero extensions"]
public theorem exists_infinitesimalAutomorphismFunctor (hRS : SatisfiesRSStar B S hS p hp) :
    Nonempty (InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp) :=
  nonempty_infinitesimalAutomorphismFunctorData_of_bijective A B S hS toS hA p x hx hp
    (infinitesimalAutomorphismSetFunctor_product_bijective A B S hS toS hA p x hx hp hRS)

/-- The chosen `A`-linear functor `Inf_x` of infinitesimal automorphisms. -/
public def infinitesimalAutomorphismFunctor (hRS : SatisfiesRSStar B S hS p hp) :
    InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp :=
  Classical.choice (exists_infinitesimalAutomorphismFunctor A B S hS toS hA p x hx hp hRS)

end TrivialDeformation

end Deformation.Artin
