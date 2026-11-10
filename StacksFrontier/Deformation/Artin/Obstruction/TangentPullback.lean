module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.LiftSituationPullback

/-!
# The map of tangent modules along a ring map (Stacks 07YA)

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S`, let `x` be an
object of `𝒳` over `Spec A`, let `f : A ⟶ C` be a homomorphism of `S`-algebras and let `y ⟶ x`
be a morphism of `𝒳` lying over `Spec C ⟶ Spec A`, so that `y = x|_{Spec C}`. For `M ∈ Mod_A`,
`N ∈ Mod_C` and an `A`-linear map `M ⟶ N`, **Stacks 07YA** produces a canonical `A`-linear map
`T_x(M) ⟶ T_y(N)`, out of the pullback functor `Lift(x, A[M]) ⟶ Lift(y, C[N])` along
`Spec C[N] ⟶ Spec A[M]`.

The pullback on isomorphism classes of lifts is `Deformation.Artin.underFiberClassPullback`,
along the commuting square formed by the two square-zero immersions `Spec A ⟶ Spec A[M]`,
`Spec C ⟶ Spec C[N]` and the morphisms `Spec C ⟶ Spec A`, `Spec C[N] ⟶ Spec A[M]`
(`Deformation.Artin.algebraOverMap_comp_squareZeroArrow`). It is defined for an arbitrary
category fibred in groupoids and an arbitrary commuting square of the base, so nothing here
depends on a chart of `S`. This file reads it on tangent modules and proves the assertion of the
source, that the resulting map is linear: the source's reason is that addition and scalar
multiplication on `T_x` are built from morphisms in the categories of lifts alone, and the
form that argument takes here is naturality of the map in the two coefficient modules.

## Main definitions

* `Deformation.Artin.tangentPullbackFun` — the map `T_x(M) ⟶ T_y(N)` as a bare function: the
  pullback of lift classes read through the two identifications of the tangent modules with
  the lift classes.
* `Deformation.Artin.tangentPullbackHom` — the same map as an `f`-semilinear map, which is the
  same datum as the source's `A`-linear map `T_x(M) ⟶ T_y(N)`.

## Main results

* `Deformation.Artin.tangentPullbackFun_natural` — the map is natural in the two coefficient
  modules.
* `Deformation.Artin.tangentPullbackFun_comp` — the map is functorial in the ring map.
* `Deformation.Artin.existsUnique_tangentBaseChange` — **Stacks 07YA on tangent modules**: there
  is exactly one `f`-semilinear map `T_x(M) ⟶ T_y(N)` carrying each class of lifts of `x` over
  `Spec A[M]` to the class of its pullback along `Spec C[N] ⟶ Spec A[M]`.

## Implementation notes

The two tangent functors enter as arbitrary members of `Deformation.Artin.TangentFunctorData`,
as in the sibling base-change statements of this development: `T_x(M)` is a chosen object and
the only handle on its values is the family of bijections with the isomorphism classes of
lifts. The source's (RS*) is what produces such members (Stacks 07Y9 (2)(a),
`Deformation.Artin.exists_tangentFunctor`); the map of this file does not use it otherwise.

The map of coefficients is a morphism `M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj` of
`A`-modules, and the resulting map of tangent modules is written as `f`-semilinear, which is the
same datum as an `A`-linear map into the restriction of scalars of `T_y(N)`.

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
* [Stacks Project, Tag 07Y9](https://stacks.math.columbia.edu/tag/07Y9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

namespace Deformation.Artin

section TangentPullback

universe u v w

variable {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C)
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {toSC : Spec (.of C) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {hC : B.Contains (Spec (.of C))}
  (hf : Spec.map (CommRingCat.ofHom f) ≫ toS = toSC)
  {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)
  {x y : X} {hx : p.obj x = algebraOver A B S hS toS hA}
  {hy : p.obj y = algebraOver C B S hS toSC hC}
  (φ : y ⟶ x) (hφ : p.IsHomLift (algebraOverMapOfRingHom f B S hS toS toSC hA hC hf) φ)
  (F : TangentFunctorData A B S hS toS hA p x hx)
  (G : TangentFunctorData C B S hS toSC hC p y hy)

/-- The morphism `Spec C[N] ⟶ Spec A[M]` of Stacks 07YA attached to a map of coefficients. -/
public abbrev tangentPullbackBase {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    squareZeroOver C B S hS toSC N ⟶ squareZeroOver A B S hS toS M :=
  squareZeroOverBaseMap f B S hS toS toSC hf M N (restrictScalarsAddHom f ψ)
    (restrictScalarsAddHom_smul f ψ)

/-- The square of Stacks 07YA: the two square-zero immersions commute with the two morphisms
induced by the ring map. -/
public theorem tangentPullbackBase_square {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    algebraOverMapOfRingHom f B S hS toS toSC hA hC hf ≫ squareZeroArrow A B S hS toS hA M =
      squareZeroArrow C B S hS toSC hC N ≫ tangentPullbackBase f hf ψ :=
  algebraOverMap_comp_squareZeroArrow f B S hS toS toSC hA hC hf M N _ _

/-- The pullback of lift classes of Stacks 07YA along `Spec C[N] ⟶ Spec A[M]`. -/
public abbrev liftClassPullback {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M) :
    squareZeroLiftClasses C B S hS toSC hC p y hy N :=
  underFiberClassPullback p hp (tangentPullbackBase f hf ψ)
    (tangentPullbackBase_square f hf ψ) φ hφ a

/-- **The map of Stacks 07YA on tangent modules**, as a bare function: the pullback of lift
classes along `Spec C[N] ⟶ Spec A[M]`, read through the two identifications of the tangent
modules with the lift classes. -/
public def tangentPullbackFun {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    ↥(F.functor.obj M) → ↥(G.functor.obj N) :=
  fun z => (G.liftEquiv N).symm (liftClassPullback f hf hp φ hφ ψ (F.liftEquiv M z))

public theorem liftEquiv_tangentPullbackFun {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (z : ↥(F.functor.obj M)) :
    G.liftEquiv N (tangentPullbackFun f hf hp φ hφ F G ψ z) =
      liftClassPullback f hf hp φ hφ ψ (F.liftEquiv M z) := by
  rw [tangentPullbackFun, Equiv.apply_symm_apply]

/-- The class attached by the map to a *representative* of a class of lifts of `x` is the
class of its chosen pullback. -/
public theorem liftEquiv_tangentPullbackFun_of_rep {M : SiteModule A B}
    {N : SiteModule C B} (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (z : ↥(F.functor.obj M))
    (u : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ squareZeroArrow A B S hS toS hA M)))
    (hu : Quotient.mk _ u = F.liftEquiv M z) :
    G.liftEquiv N (tangentPullbackFun f hf hp φ hφ F G ψ z) =
      Quotient.mk _ (underFiberPullback p hp (tangentPullbackBase f hf ψ)
        (tangentPullbackBase_square f hf ψ) φ hφ (hy := hy) u).1 := by
  rw [liftEquiv_tangentPullbackFun, ← hu]
  rfl

/-- **The map of Stacks 07YA on tangent modules is natural in the two coefficient modules.**
The map `s` of coefficients on the source side and the map `t` on the target side are
compatible with the two maps of coefficients across the ring map. -/
public theorem tangentPullbackFun_natural
    {M₁ M₂ : SiteModule A B} {N₁ N₂ : SiteModule C B}
    (s : M₁ ⟶ M₂) (t : N₁ ⟶ N₂)
    (ψ₁ : M₁.obj ⟶ (ModuleCat.restrictScalars f).obj N₁.obj)
    (ψ₂ : M₂.obj ⟶ (ModuleCat.restrictScalars f).obj N₂.obj)
    (hcompat : s.hom ≫ ψ₂ = ψ₁ ≫ (ModuleCat.restrictScalars f).map t.hom)
    (z : ↥(F.functor.obj M₁)) :
    tangentPullbackFun f hf hp φ hφ F G ψ₂ (F.functor.map s z) =
      G.functor.map t (tangentPullbackFun f hf hp φ hφ F G ψ₁ z) := by
  apply (G.liftEquiv N₂).injective
  -- A representative `uw` of the class of lifts of `x` over `A[M₁]` attached to `z`.
  obtain ⟨uw, huw⟩ := Quotient.exists_rep (F.liftEquiv M₁ z)
  -- The source side: the pullback of `z` along `s`, with its cartesian comparison to `uw`.
  obtain ⟨u₁, u₂, hu₁, hu₂, φs, hφs, hws⟩ := F.liftEquiv_natural s z
  obtain ⟨φs', hφs', hws'⟩ := exists_cartesian_of_underFiber_iso p hp
    (squareZeroOverMap A B S hS toS s) (𝟙 x)
    (Quotient.exact (hu₁.trans huw.symm)).some φs hφs (by rwa [Category.id_comp])
  -- Its pullback across the ring map, at `(M₂, N₂, ψ₂)`.
  obtain ⟨ρ₂, hρ₂, hw₂⟩ := (underFiberPullback p hp (tangentPullbackBase f hf ψ₂)
    (tangentPullbackBase_square f hf ψ₂) φ hφ (hy := hy) u₂).2
  -- The target side: the pullback at `(M₁, N₁, ψ₁)`, then the pullback along `t`.
  obtain ⟨ρ₁, hρ₁, hw₁⟩ := (underFiberPullback p hp (tangentPullbackBase f hf ψ₁)
    (tangentPullbackBase_square f hf ψ₁) φ hφ (hy := hy) uw).2
  obtain ⟨v₁, v₂, hv₁, hv₂, φt, hφt, hwt⟩ :=
    G.liftEquiv_natural t (tangentPullbackFun f hf hp φ hφ F G ψ₁ z)
  obtain ⟨φt', hφt', hwt'⟩ := exists_cartesian_of_underFiber_iso p hp
    (squareZeroOverMap C B S hS toSC t) (𝟙 y)
    (Quotient.exact (hv₁.trans (liftEquiv_tangentPullbackFun_of_rep f hf hp φ hφ F G ψ₁ z
      uw huw))).some φt hφt (by rwa [Category.id_comp])
  -- Both composites are cartesian over the same arrow of the base.
  have hsquare := squareZeroOverBaseMap_naturality f B S hS toS toSC hf s t ψ₁ ψ₂ hcompat
  have hcart₁ : p.IsStronglyCartesian
      (tangentPullbackBase f hf ψ₂ ≫ squareZeroOverMap A B S hS toS s) (ρ₂ ≫ φs') := by
    have := hρ₂
    have := hφs'
    exact hp.isStronglyCartesian_homLift _ _
  have hcart₂ : p.IsStronglyCartesian
      (tangentPullbackBase f hf ψ₂ ≫ squareZeroOverMap A B S hS toS s) (φt' ≫ ρ₁) := by
    rw [hsquare]
    have := hφt'
    have := hρ₁
    exact hp.isStronglyCartesian_homLift _ _
  have heq₁ : (underFiberPullback p hp (tangentPullbackBase f hf ψ₂)
      (tangentPullbackBase_square f hf ψ₂) φ hφ (hy := hy) u₂).1.1.hom ≫ (ρ₂ ≫ φs') =
        φ ≫ uw.1.hom := by
    rw [← Category.assoc, hw₂, Category.assoc, hws', Category.id_comp]
  have heq₂ : v₂.1.hom ≫ (φt' ≫ ρ₁) = φ ≫ uw.1.hom := by
    rwa [← Category.assoc, hwt', Category.id_comp]
  rw [liftEquiv_tangentPullbackFun_of_rep f hf hp φ hφ F G ψ₂ (F.functor.map s z) u₂ hu₂,
    ← hv₂]
  exact underFiberClass_eq_of_cartesian p _ φ rfl _ _ hcart₁ hcart₂ heq₁ heq₂

/-- **The map of Stacks 07YA on tangent modules is additive.** -/
public theorem tangentPullbackFun_add {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (z₁ z₂ : ↥(F.functor.obj M)) :
    tangentPullbackFun f hf hp φ hφ F G ψ (z₁ + z₂) =
      tangentPullbackFun f hf hp φ hφ F G ψ z₁ + tangentPullbackFun f hf hp φ hφ F G ψ z₂ := by
  have := F.additive
  have := G.additive
  have := F.linear
  have := G.linear
  set i₁ := siteModuleInl A B hA M M
  set i₂ := siteModuleInr A B hA M M
  set q₁ := siteModuleFst A B hA M M
  set q₂ := siteModuleSnd A B hA M M
  set r₁ := siteModuleFst C B hC N N
  set r₂ := siteModuleSnd C B hC N N
  set Ψ := prodRestrictScalarsHom f hA hC ψ
  have hc (q : siteModuleProd A B hA M M ⟶ M) (r : siteModuleProd C B hC N N ⟶ N)
      (h : ∀ m, ψ (q.hom m) = r.hom (Ψ m)) :
      q.hom ≫ ψ = Ψ ≫ (ModuleCat.restrictScalars f).map r.hom :=
    ModuleCat.hom_ext (LinearMap.ext h)
  have hc₁ := hc q₁ r₁ fun m => by rw [prodRestrictScalarsHom_apply]; rfl
  have hc₂ := hc q₂ r₂ fun m => by rw [prodRestrictScalarsHom_apply]; rfl
  have hcs := hc (q₁ + q₂) (r₁ + r₂) fun m => by
    rw [prodRestrictScalarsHom_apply]
    exact map_add ψ.hom m.1 m.2
  set z := F.functor.map i₁ z₁ + F.functor.map i₂ z₂ with hz
  have hmap (j : M ⟶ siteModuleProd A B hA M M) (k : siteModuleProd A B hA M M ⟶ M)
      (y : ↥(F.functor.obj M)) :
      F.functor.map k (F.functor.map j y) = F.functor.map (j ≫ k) y := by simp
  have hz₁ : F.functor.map q₁ z = z₁ := by
    rw [hz, map_add, hmap, hmap, siteModuleInl_comp_fst, siteModuleInr_comp_fst]
    simp
  have hz₂ : F.functor.map q₂ z = z₂ := by
    rw [hz, map_add, hmap, hmap, siteModuleInl_comp_snd, siteModuleInr_comp_snd]
    simp
  have hn₁ := tangentPullbackFun_natural f hf hp φ hφ F G q₁ r₁ Ψ ψ hc₁ z
  have hn₂ := tangentPullbackFun_natural f hf hp φ hφ F G q₂ r₂ Ψ ψ hc₂ z
  have hns := tangentPullbackFun_natural f hf hp φ hφ F G (q₁ + q₂) (r₁ + r₂) Ψ ψ hcs z
  rw [hz₁] at hn₁
  rw [hz₂] at hn₂
  have hsum : F.functor.map (q₁ + q₂) z = z₁ + z₂ := by
    rw [F.functor.map_add]
    change F.functor.map q₁ z + F.functor.map q₂ z = z₁ + z₂
    rw [hz₁, hz₂]
  rw [hsum, G.functor.map_add] at hns
  change tangentPullbackFun f hf hp φ hφ F G ψ (z₁ + z₂) =
    G.functor.map r₁ (tangentPullbackFun f hf hp φ hφ F G Ψ z) +
      G.functor.map r₂ (tangentPullbackFun f hf hp φ hφ F G Ψ z) at hns
  rw [hns, ← hn₁, ← hn₂]

/-- **The map of Stacks 07YA on tangent modules is semilinear over the ring map**, that is,
`A`-linear into the restriction of scalars of `T_y(N)`. -/
public theorem tangentPullbackFun_smul {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (a : A)
    (z : ↥(F.functor.obj M)) :
    tangentPullbackFun f hf hp φ hφ F G ψ (a • z) =
      f a • tangentPullbackFun f hf hp φ hφ F G ψ z := by
  have := F.additive
  have := G.additive
  have := F.linear
  have := G.linear
  have hcompat : (a • (𝟙 M)).hom ≫ ψ =
      ψ ≫ (ModuleCat.restrictScalars f).map ((f a • (𝟙 N)).hom) := by
    apply ModuleCat.hom_ext
    apply LinearMap.ext
    intro m
    change ψ (a • m) = f a • ψ m
    exact restrictScalarsAddHom_smul f ψ a m
  have hn := tangentPullbackFun_natural f hf hp φ hφ F G (a • (𝟙 M)) (f a • (𝟙 N)) ψ ψ
    hcompat z
  have hF : F.functor.map (a • (𝟙 M)) z = a • z := by
    rw [Functor.map_smul, F.functor.map_id]
    rfl
  have hG : ∀ y : ↥(G.functor.obj N), G.functor.map (f a • (𝟙 N)) y = f a • y := by
    intro y
    rw [Functor.map_smul, G.functor.map_id]
    rfl
  rwa [hF, hG] at hn

/-- **The map of Stacks 07YA on tangent modules**, as an `f`-semilinear map — the `A`-linear
map `T_x(M) ⟶ T_y(N)` of the source. -/
public def tangentPullbackHom {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    ↥(F.functor.obj M) →ₛₗ[f] ↥(G.functor.obj N) where
  toFun := tangentPullbackFun f hf hp φ hφ F G ψ
  map_add' := tangentPullbackFun_add f hf hp φ hφ F G ψ
  map_smul' := tangentPullbackFun_smul f hf hp φ hφ F G ψ

@[simp]
public theorem tangentPullbackHom_apply {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (z : ↥(F.functor.obj M)) :
    tangentPullbackHom f hf hp φ hφ F G ψ z = tangentPullbackFun f hf hp φ hφ F G ψ z := rfl

/-- **Stacks 07YA on tangent modules.** Let `x` be an object over `Spec A` of a category fibred
in groupoids over the big fppf site of `S`, let `f : A ⟶ C` be a homomorphism of `S`-algebras
and let `y ⟶ x` be a morphism lying over `Spec C ⟶ Spec A`, so that `y = x|_{Spec C}`. For
`M ∈ Mod_A`, `N ∈ Mod_C` and an `A`-linear map `M ⟶ N` there is exactly one `A`-linear map
`T_x(M) ⟶ T_y(N)` — written as an `f`-semilinear map — carrying each class of lifts of `x`
over `Spec A[M]` to the class of its pullback along `Spec C[N] ⟶ Spec A[M]`.

The tangent functors `T_x`, `T_y` are arbitrary members of
`Deformation.Artin.TangentFunctorData`, which (RS*) supplies by Stacks 07Y9 (2)(a). -/
@[stacks 07YA "tangent_base_change"]
public theorem existsUnique_tangentBaseChange {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    ∃! τ : ↥(F.functor.obj M) →ₛₗ[f] ↥(G.functor.obj N),
      ∀ z, G.liftEquiv N (τ z) = liftClassPullback f hf hp φ hφ ψ (F.liftEquiv M z) := by
  refine ⟨tangentPullbackHom f hf hp φ hφ F G ψ,
    liftEquiv_tangentPullbackFun f hf hp φ hφ F G ψ, fun τ hτ => ?_⟩
  refine LinearMap.ext fun z => (G.liftEquiv N).injective ?_
  rw [hτ z, tangentPullbackHom_apply, liftEquiv_tangentPullbackFun]

end TangentPullback

/-! ### The map of Stacks 07YA is functorial in the ring map -/

section Composition

universe u v w

/-- The pullback of lift classes depends only on the arrows of the base square, not on the
proofs that it commutes. -/
public theorem underFiberClassPullback_congr {C : Type*} [Category C] {X : Type*} [Category X]
    (p : X ⥤ C) (hp : p.IsFiberedInGroupoids) {U U' V V' : C} {aa : U ⟶ U'} {cc : V ⟶ V'}
    {bb bb' : V ⟶ U} {D D' : V' ⟶ U'} (hb : bb = bb') (hD : D = D')
    (hsq : bb ≫ aa = cc ≫ D) (hsq' : bb' ≫ aa = cc ≫ D')
    {x y : X} {hx : p.obj x = U} {hy : p.obj y = V} (φ : y ⟶ x) (hφ : p.IsHomLift bb φ)
    (hφ' : p.IsHomLift bb' φ)
    (a : Quotient (isIsomorphicSetoid ((Under.post p).Fiber (Under.mk (eqToHom hx ≫ aa))))) :
    underFiberClassPullback p hp D hsq φ hφ (hy := hy) a =
      underFiberClassPullback p hp D' hsq' φ hφ' (hy := hy) a := by
  subst hb hD
  rfl

variable {A C E : Type u} [CommRing A] [CommRing C] [CommRing E] (f₁ : A →+* C) (f₂ : C →+* E)
  {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {toS : Spec (.of A) ⟶ S} {toSC : Spec (.of C) ⟶ S} {toSE : Spec (.of E) ⟶ S}
  {hA : B.Contains (Spec (.of A))} {hC : B.Contains (Spec (.of C))}
  {hE : B.Contains (Spec (.of E))}
  (hf₁ : Spec.map (CommRingCat.ofHom f₁) ≫ toS = toSC)
  (hf₂ : Spec.map (CommRingCat.ofHom f₂) ≫ toSC = toSE)
  (hf₁₂ : Spec.map (CommRingCat.ofHom (f₂.comp f₁)) ≫ toS = toSE)

/-- The morphisms `Spec C ⟶ Spec A` attached to ring maps compose. -/
public theorem algebraOverMapOfRingHom_comp :
    algebraOverMapOfRingHom f₂ B S hS toSC toSE hC hE hf₂ ≫
        algebraOverMapOfRingHom f₁ B S hS toS toSC hA hC hf₁ =
      algebraOverMapOfRingHom (f₂.comp f₁) B S hS toS toSE hA hE hf₁₂ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom f₂) ≫ Spec.map (CommRingCat.ofHom f₁) =
    Spec.map (CommRingCat.ofHom (f₂.comp f₁))
  rw [← Spec.map_comp]
  rfl

/-- The morphisms `Spec C[N] ⟶ Spec A[M]` of Stacks 07YA compose. -/
public theorem tangentPullbackBase_comp {M : SiteModule A B} {N : SiteModule C B}
    {K : SiteModule E B} (ψ₁ : M.obj ⟶ (ModuleCat.restrictScalars f₁).obj N.obj)
    (ψ₂ : N.obj ⟶ (ModuleCat.restrictScalars f₂).obj K.obj)
    (ψ₁₂ : M.obj ⟶ (ModuleCat.restrictScalars (f₂.comp f₁)).obj K.obj)
    (hψ : ∀ m, ψ₁₂ m = ψ₂ (ψ₁ m)) :
    tangentPullbackBase (hS := hS) f₂ hf₂ ψ₂ ≫ tangentPullbackBase (hS := hS) f₁ hf₁ ψ₁ =
      tangentPullbackBase (hS := hS) (f₂.comp f₁) hf₁₂ ψ₁₂ := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap f₂ (restrictScalarsAddHom f₂ ψ₂)
      (restrictScalarsAddHom_smul f₂ ψ₂))) ≫
    Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap f₁ (restrictScalarsAddHom f₁ ψ₁)
      (restrictScalarsAddHom_smul f₁ ψ₁))) =
    Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap (f₂.comp f₁)
      (restrictScalarsAddHom (f₂.comp f₁) ψ₁₂) (restrictScalarsAddHom_smul (f₂.comp f₁) ψ₁₂)))
  rw [← Spec.map_comp]
  congr 2
  apply CommRingCat.hom_ext
  apply RingHom.ext
  intro z
  exact TrivSqZeroExt.ext rfl (hψ z.snd).symm

variable {X : Type v} [Category.{w} X] {p : X ⥤ BigFppfOver B S hS} (hp : p.IsFiberedInGroupoids)
  {x y z : X} {hx : p.obj x = algebraOver A B S hS toS hA}
  {hy : p.obj y = algebraOver C B S hS toSC hC} {hz : p.obj z = algebraOver E B S hS toSE hE}
  (φ₁ : y ⟶ x) (hφ₁ : p.IsHomLift (algebraOverMapOfRingHom f₁ B S hS toS toSC hA hC hf₁) φ₁)
  (φ₂ : z ⟶ y) (hφ₂ : p.IsHomLift (algebraOverMapOfRingHom f₂ B S hS toSC toSE hC hE hf₂) φ₂)
  (hφ₁₂ : p.IsHomLift (algebraOverMapOfRingHom (f₂.comp f₁) B S hS toS toSE hA hE hf₁₂)
    (φ₂ ≫ φ₁))
  (F : TangentFunctorData A B S hS toS hA p x hx)
  (G : TangentFunctorData C B S hS toSC hC p y hy)
  (H : TangentFunctorData E B S hS toSE hE p z hz)

/-- **The map of Stacks 07YA on tangent modules is functorial in the ring map.** Along
`A ⟶ C ⟶ E`, the map for the composite is the composite of the maps. -/
public theorem tangentPullbackFun_comp {M : SiteModule A B} {N : SiteModule C B}
    {K : SiteModule E B} (ψ₁ : M.obj ⟶ (ModuleCat.restrictScalars f₁).obj N.obj)
    (ψ₂ : N.obj ⟶ (ModuleCat.restrictScalars f₂).obj K.obj)
    (ψ₁₂ : M.obj ⟶ (ModuleCat.restrictScalars (f₂.comp f₁)).obj K.obj)
    (hψ : ∀ m, ψ₁₂ m = ψ₂ (ψ₁ m)) (t : ↥(F.functor.obj M)) :
    tangentPullbackFun (f₂.comp f₁) hf₁₂ hp (φ₂ ≫ φ₁) hφ₁₂ F H ψ₁₂ t =
      tangentPullbackFun f₂ hf₂ hp φ₂ hφ₂ G H ψ₂
        (tangentPullbackFun f₁ hf₁ hp φ₁ hφ₁ F G ψ₁ t) := by
  apply (H.liftEquiv K).injective
  rw [liftEquiv_tangentPullbackFun, liftEquiv_tangentPullbackFun,
    liftEquiv_tangentPullbackFun]
  have hbb := algebraOverMapOfRingHom_comp (B := B) (hS := hS) (hA := hA) (hC := hC) (hE := hE)
    f₁ f₂ hf₁ hf₂ hf₁₂
  have hDD := tangentPullbackBase_comp (hS := hS) f₁ f₂ hf₁ hf₂ hf₁₂ ψ₁ ψ₂ ψ₁₂ hψ
  have hsqc : (algebraOverMapOfRingHom f₂ B S hS toSC toSE hC hE hf₂ ≫
      algebraOverMapOfRingHom f₁ B S hS toS toSC hA hC hf₁) ≫ squareZeroArrow A B S hS toS hA M =
        squareZeroArrow E B S hS toSE hE K ≫
          tangentPullbackBase f₂ hf₂ ψ₂ ≫ tangentPullbackBase f₁ hf₁ ψ₁ := by
    rw [Category.assoc, tangentPullbackBase_square, ← Category.assoc,
      tangentPullbackBase_square, Category.assoc]
  have hφc : p.IsHomLift (algebraOverMapOfRingHom f₂ B S hS toSC toSE hC hE hf₂ ≫
      algebraOverMapOfRingHom f₁ B S hS toS toSC hA hC hf₁) (φ₂ ≫ φ₁) := by
    rwa [hbb]
  rw [liftClassPullback, underFiberClassPullback_congr p hp hbb.symm hDD.symm
    (tangentPullbackBase_square (f₂.comp f₁) hf₁₂ ψ₁₂) hsqc (φ₂ ≫ φ₁) hφ₁₂ hφc]
  exact underFiberClassPullback_comp p hp _ _ (tangentPullbackBase_square f₁ hf₁ ψ₁)
    (tangentPullbackBase_square f₂ hf₂ ψ₂) φ₁ hφ₁ φ₂ hφ₂ hsqc hφc _

end Composition

end Deformation.Artin

end
