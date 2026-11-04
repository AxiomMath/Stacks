module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Infinitesimal.AutomorphismCommute
public import StacksFrontier.Deformation.Artin.Obstruction.NaiveTheorySiteComparison

/-!
# Functoriality of the tangent functor along a ring map

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S` satisfying
(RS*), let `A` and `C` be `S`-algebras whose spectra lie in the site, let `f : A ⟶ C` be a map
of `S`-algebras, let `x` be an object of `𝒳` over `Spec A` and let `y = x|_{Spec C}`. Remark
07YA asserts that for an `A`-module `M`, a `C`-module `N` and an `f`-semilinear map `M ⟶ N`
there is a canonical `A`-linear map

`T_x(M) ⟶ T_y(N)`

on the tangent functors of Stacks 07Y9, "simply because there is a pullback functor
`Lift(x, A[M]) ⟶ Lift(y, C[N])`". This file builds that map and proves it `A`-linear.

The pullback on isomorphism classes of lifts is
`Deformation.Artin.siteSquareZeroLiftBaseChangeMap`; the morphism `Spec C[N] ⟶ Spec A[M]` it
pulls back along is `Deformation.Artin.squareZeroOverBaseMap`, so no datum has to be assumed:
`Deformation.Artin.tangentBaseChangeMap` depends only on `f`, on `ψ` and on the restriction
arrow `y ⟶ x`.

`A`-linearity is the source's "the construction of the action, the addition, and the scalar
multiplication on `Inf_x` and `T_x` use only morphisms in the categories of lifts, so the
constructions above are functorial". Concretely it is deduced from naturality of the
transition in *both* coefficient modules at once
(`Deformation.Artin.tangentBaseChangeMap_natural`): additivity is naturality at the two
projections and the codiagonal of `M × M` and `N × N`, and semilinearity is naturality at the
pair `r • 𝟙` and `f r • 𝟙`. Naturality in turn rests on single-valuedness of the transition,
`Deformation.Artin.eq_of_isSiteSquareZeroLiftBaseChange`, together with the two statements
that the transition composes with a pullback along a module map of the source or of the target
coefficients.

The `A`-module structure on `T_y(N)`, which is a `C`-module, is restriction of scalars along
`f`, written with `Module.compHom` as in `Deformation.Artin.ObstructionTheory.map`.

## Main definitions

* `Deformation.Artin.squareZeroLiftClassesBaseChange` — the transition of Remark 07YA on
  isomorphism classes of lifts, with the morphism of trivial square-zero extensions supplied
  rather than assumed.
* `Deformation.Artin.tangentBaseChangeMap` — the map `T_x(M) ⟶ T_y(N)`, read through the two
  `liftEquiv` bijections.
* `Deformation.Artin.tangentBaseChangeLinearMap` — the same map as an `A`-linear map.

## Main results

* `Deformation.Artin.isSiteSquareZeroLiftBaseChange_comp_target`,
  `Deformation.Artin.isSiteSquareZeroLiftBaseChange_comp_source` — the transition composes with
  a pullback along a module map of the target, resp. of the source, coefficients.
* `Deformation.Artin.tangentBaseChangeMap_natural` — naturality in both coefficient modules.
* `Deformation.Artin.isLinearMap_tangentBaseChangeMap` — **Remark 07YA for the tangent
  functor**: the map `T_x(M) ⟶ T_y(N)` is `A`-linear.

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory

universe u v w

namespace Deformation.Artin

attribute [local implicit_reducible] CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor
  CategoryTheory.Under.post

/-! ### Composing the transition with a pullback along a module map -/

section Composition

open CategoryTheory.Functor

variable {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C)
  (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
  (toSC : Spec (.of C) ⟶ S) (hC : B.Contains (Spec (.of C)))
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x y : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hy : p.obj y = algebraOver C B S hS toSC hC)
  (φ₀ : y ⟶ x) (hp : p.IsFiberedInGroupoids)

/-- A morphism over `f₁`, a morphism over an identity and a morphism over `f₂` compose to a
morphism over `f₁ ≫ f₂`. -/
private theorem isHomLift_comp_comp_of_id {F D : Type*} [Category F] [Category D] {p : F ⥤ D}
    {R S T : D} {a b c d : F} {f₁ : R ⟶ S}
    {f₂ : S ⟶ T} {φ₁ : a ⟶ b} {α : b ⟶ c} {φ₂ : c ⟶ d} (h₁ : p.IsHomLift f₁ φ₁)
    (hα : p.IsHomLift (𝟙 S) α) (h₂ : p.IsHomLift f₂ φ₂) :
    p.IsHomLift (f₁ ≫ f₂) (φ₁ ≫ α ≫ φ₂) := by
  simpa using isHomLift_comp p h₁ (isHomLift_comp p hα h₂)

include hp in
/-- The transition of Remark 07YA composed with the pullback along a module map of the target
coefficients is the transition at the composite semilinear map. -/
public theorem isSiteSquareZeroLiftBaseChange_comp_target
    {M : SiteModule A B} {N N' : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (χ : N ⟶ N')
    {a : squareZeroLiftClasses A B S hS toS hA p x hx M}
    {b : squareZeroLiftClasses C B S hS toSC hC p y hy N}
    {b' : squareZeroLiftClasses C B S hS toSC hC p y hy N'}
    (hb : IsSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f ψ a b)
    (hc : IsPullbackOfSquareZeroLift C B S hS toSC hC p y hy χ b b') :
    IsSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f
      (ψ ≫ (ModuleCat.restrictScalars f).map χ.hom) a b' := by
  obtain ⟨a₁, b₁, ha₁, hb₁, g₁, ⟨e₁, he₁, hge₁⟩, φ₁, hφ₁, hcc₁⟩ := hb
  obtain ⟨c₁, c₂, hc₁, hc₂, φ₂, hφ₂, hcc₂⟩ := hc
  obtain ⟨α⟩ := Quotient.exact (hb₁.trans hc₁.symm)
  have hαlift : p.IsHomLift (𝟙 (squareZeroOver C B S hS toSC N)) α.inv.1.right :=
    underPost_isHomLift_right p (𝟙 _) α.inv.1 α.inv.2
  have hwi : c₁.1.hom ≫ α.inv.1.right = b₁.1.hom := Under.w α.inv.1
  have h₁ : p.IsHomLift g₁ φ₁ := hφ₁.toIsHomLift
  have h₂ : p.IsHomLift (squareZeroOverMap C B S hS toSC χ) φ₂ := hφ₂.toIsHomLift
  have hlift := isHomLift_comp_comp_of_id h₂ hαlift h₁
  refine ⟨a₁, c₂, ha₁, hc₂, squareZeroOverMap C B S hS toSC χ ≫ g₁,
    ⟨((TrivSqZeroExt.map χ.hom.hom).toRingHom).comp e₁, fun z => ?_, ?_⟩,
    φ₂ ≫ α.inv.1.right ≫ φ₁, hp.isStronglyCartesian_homLift _ _, ?_⟩
  · change TrivSqZeroExt.map χ.hom.hom (e₁ z) = _
    rw [he₁ z]
    exact TrivSqZeroExt.ext (TrivSqZeroExt.fst_map _ _) (TrivSqZeroExt.snd_map _ _)
  · have hmap : (BigFppfOver.toScheme B S hS).map (squareZeroOverMap C B S hS toSC χ) =
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map χ.hom.hom).toRingHom) := rfl
    rw [(BigFppfOver.toScheme B S hS).map_comp, hge₁, hmap]
    exact (Spec.map_comp _ _).symm.trans (congrArg Spec.map (CommRingCat.ofHom_comp _ _).symm)
  · rw [← Category.assoc, hcc₂, ← Category.assoc, hwi, hcc₁]

include hp in
/-- The pullback along a module map of the source coefficients composed with the transition of
Remark 07YA is the transition at the composite semilinear map. -/
public theorem isSiteSquareZeroLiftBaseChange_comp_source
    {M M' : SiteModule A B} {N : SiteModule C B}
    (ξ : M ⟶ M') (ψ : M'.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    {a : squareZeroLiftClasses A B S hS toS hA p x hx M}
    {a' : squareZeroLiftClasses A B S hS toS hA p x hx M'}
    {b : squareZeroLiftClasses C B S hS toSC hC p y hy N}
    (ha : IsPullbackOfSquareZeroLift A B S hS toS hA p x hx ξ a a')
    (hb : IsSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f ψ a' b) :
    IsSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f
      (ξ.hom ≫ ψ) a b := by
  obtain ⟨a₁, a₂, ha₁, ha₂, φξ, hφξ, hcca⟩ := ha
  obtain ⟨a₃, b₁, ha₃, hb₁, g₁, ⟨e₁, he₁, hge₁⟩, φ₁, hφ₁, hcc₁⟩ := hb
  obtain ⟨α⟩ := Quotient.exact (ha₃.trans ha₂.symm)
  have hαlift : p.IsHomLift (𝟙 (squareZeroOver A B S hS toS M')) α.hom.1.right :=
    underPost_isHomLift_right p (𝟙 _) α.hom.1 α.hom.2
  have hwh : a₃.1.hom ≫ α.hom.1.right = a₂.1.hom := Under.w α.hom.1
  have h₁ : p.IsHomLift g₁ φ₁ := hφ₁.toIsHomLift
  have h₂ : p.IsHomLift (squareZeroOverMap A B S hS toS ξ) φξ := hφξ.toIsHomLift
  have hlift := isHomLift_comp_comp_of_id h₁ hαlift h₂
  refine ⟨a₁, b₁, ha₁, hb₁, g₁ ≫ squareZeroOverMap A B S hS toS ξ,
    ⟨e₁.comp (TrivSqZeroExt.map ξ.hom.hom).toRingHom, fun z => ?_, ?_⟩,
    φ₁ ≫ α.hom.1.right ≫ φξ, hp.isStronglyCartesian_homLift _ _, ?_⟩
  · change e₁ (TrivSqZeroExt.map ξ.hom.hom z) = _
    rw [he₁ (TrivSqZeroExt.map ξ.hom.hom z)]
    exact TrivSqZeroExt.ext (congrArg f (TrivSqZeroExt.fst_map _ _))
      (congrArg ψ (TrivSqZeroExt.snd_map _ _))
  · have hmap : (BigFppfOver.toScheme B S hS).map (squareZeroOverMap A B S hS toS ξ) =
        Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map ξ.hom.hom).toRingHom) := rfl
    rw [(BigFppfOver.toScheme B S hS).map_comp, hge₁, hmap]
    exact (Spec.map_comp _ _).symm.trans (congrArg Spec.map (CommRingCat.ofHom_comp _ _).symm)
  · have hcompat : a₃.1.hom ≫ α.hom.1.right ≫ φξ = a₁.1.hom := by
      rw [← Category.assoc, hwh, hcca]
    rw [← Category.assoc, hcc₁, Category.assoc, hcompat]

end Composition

/-! ### The split square of a product of site modules -/

section ProdSplit

universe z₁ z₂ uR

/-- The product of two site modules is a biproduct: the two projections followed by the two
inclusions sum to the identity. -/
public theorem siteModuleFst_comp_inl_add_snd_comp_inr {A : Type u} [CommRing A]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A))) (M N : SiteModule A B) :
    siteModuleFst A B hA M N ≫ siteModuleInl A B hA M N +
        siteModuleSnd A B hA M N ≫ siteModuleInr A B hA M N =
      𝟙 (siteModuleProd A B hA M N) := by
  apply ObjectProperty.hom_ext
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  exact Prod.ext (add_zero z.1) (zero_add z.2)

/-- Every value of an additive functor at a product of site modules is the sum of the images of
its two components. -/
public theorem eq_add_of_siteModuleProd {A : Type u} [CommRing A] (B : BigFppfSite.{u})
    (hA : B.Contains (Spec (.of A))) (F : SiteModule A B ⥤ ModuleCat.{z₁} A) [F.Additive]
    (M N : SiteModule A B) (b : (F.obj (siteModuleProd A B hA M N) : Type z₁)) :
    b = F.map (siteModuleInl A B hA M N) (F.map (siteModuleFst A B hA M N) b) +
      F.map (siteModuleInr A B hA M N) (F.map (siteModuleSnd A B hA M N) b) := by
  have h : F.map (siteModuleFst A B hA M N ≫ siteModuleInl A B hA M N +
      siteModuleSnd A B hA M N ≫ siteModuleInr A B hA M N) =
      𝟙 (F.obj (siteModuleProd A B hA M N)) := by
    rw [siteModuleFst_comp_inl_add_snd_comp_inr B hA M N, F.map_id]
  rw [F.map_add, F.map_comp, F.map_comp] at h
  have h2 := congrArg (fun k : F.obj (siteModuleProd A B hA M N) ⟶
    F.obj (siteModuleProd A B hA M N) => (ModuleCat.Hom.hom k) b) h
  simpa using h2.symm

/-- A linear functor into modules carries the `r`-fold identity of an object to multiplication
by `r` on its value. -/
public theorem map_smul_id_apply {R : Type uR} [CommRing R] {D : Type*} [Category D]
    [Preadditive D] [CategoryTheory.Linear R D] (F : D ⥤ ModuleCat.{z₁} R) [F.Additive]
    [F.Linear R] (M : D) (r : R) (a : (F.obj M : Type z₁)) :
    F.map (r • 𝟙 M) a = r • a := by
  rw [F.map_smul, F.map_id]
  rfl

/-- **Additivity from naturality over a product square.** A map between the values of two
additive functors on the site modules over two different rings is additive as soon as it is
natural at the two projections and at the codiagonal of `M × M` and `N × N`. This is the
argument of Tag 06I7 with the two functors allowed to live over different rings and over
different categories of coefficient modules, which is what the transition of Remark 07YA along
a ring map needs. -/
public theorem add_of_natural_siteModuleProd {A C : Type u} [CommRing A] [CommRing C]
    (B : BigFppfSite.{u}) (hA : B.Contains (Spec (.of A))) (hC : B.Contains (Spec (.of C)))
    (F : SiteModule A B ⥤ ModuleCat.{z₁} A) [F.Additive]
    (G : SiteModule C B ⥤ ModuleCat.{z₂} C) [G.Additive]
    (M : SiteModule A B) (N : SiteModule C B)
    (s : F.obj M → G.obj N)
    (t : F.obj (siteModuleProd A B hA M M) → G.obj (siteModuleProd C B hC N N))
    (hfst : ∀ a, s (F.map (siteModuleFst A B hA M M) a) =
      G.map (siteModuleFst C B hC N N) (t a))
    (hsnd : ∀ a, s (F.map (siteModuleSnd A B hA M M) a) =
      G.map (siteModuleSnd C B hC N N) (t a))
    (hcod : ∀ a, s (F.map (siteModuleCodiag A B hA M) a) =
      G.map (siteModuleCodiag C B hC N) (t a))
    (u v : (F.obj M : Type z₁)) : s (u + v) = s u + s v := by
  set z := F.map (siteModuleInl A B hA M M) u + F.map (siteModuleInr A B hA M M) v with hz
  have eval (ξ : siteModuleProd A B hA M M ⟶ M) :
      F.map ξ z = F.map (siteModuleInl A B hA M M ≫ ξ) u +
        F.map (siteModuleInr A B hA M M ≫ ξ) v := by
    rw [hz, _root_.map_add, F.map_comp, F.map_comp]
    rfl
  have hu : F.map (siteModuleFst A B hA M M) z = u := by
    rw [eval, siteModuleInl_comp_fst, siteModuleInr_comp_fst, F.map_id, F.map_zero]
    simp
  have hv : F.map (siteModuleSnd A B hA M M) z = v := by
    rw [eval, siteModuleInl_comp_snd, siteModuleInr_comp_snd, F.map_zero, F.map_id]
    simp
  have hcz : F.map (siteModuleCodiag A B hA M) z = u + v := by
    rw [eval, siteModuleInl_comp_codiag, siteModuleInr_comp_codiag, F.map_id]
    simp
  have h1 : G.map (siteModuleFst C B hC N N) (t z) = s u := by rw [← hfst z, hu]
  have h2 : G.map (siteModuleSnd C B hC N N) (t z) = s v := by rw [← hsnd z, hv]
  have hdec : t z = G.map (siteModuleInl C B hC N N) (s u) +
      G.map (siteModuleInr C B hC N N) (s v) := by
    rw [← h1, ← h2]
    exact eq_add_of_siteModuleProd B hC G N N (t z)
  have hcomp (ξ : N ⟶ siteModuleProd C B hC N N)
      (hξ : ξ ≫ siteModuleCodiag C B hC N = 𝟙 N) (b : (G.obj N : Type z₂)) :
      G.map (siteModuleCodiag C B hC N) (G.map ξ b) = b := by
    have hh := congrArg (fun k : N ⟶ N => (ModuleCat.Hom.hom (G.map k)) b) hξ
    simpa [G.map_comp] using hh
  calc s (u + v) = s (F.map (siteModuleCodiag A B hA M) z) := by rw [hcz]
    _ = G.map (siteModuleCodiag C B hC N) (t z) := hcod z
    _ = s u + s v := by
        rw [hdec, _root_.map_add, hcomp _ (siteModuleInl_comp_codiag C B hC N),
          hcomp _ (siteModuleInr_comp_codiag C B hC N)]

end ProdSplit

/-! ### The transition of Remark 07YA on lift classes, with its base morphism supplied -/

section Transition

open CategoryTheory.Functor

variable {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C)
  (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
  (toSC : Spec (.of C) ⟶ S) (hC : B.Contains (Spec (.of C)))
  (hf : Spec.map (CommRingCat.ofHom f) ≫ toS = toSC)
  {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x y : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hy : p.obj y = algebraOver C B S hS toSC hC)
  (φ₀ : y ⟶ x)
  (hφ₀ : p.IsHomLift (algebraOverMapOfRingHom f B S hS toS toSC hA hC hf) φ₀)
  (hp : p.IsFiberedInGroupoids)

include hf hφ₀ hp in
/-- **The transition of Remark 07YA on isomorphism classes of lifts.** Pullback along the
morphism `Spec C[N] ⟶ Spec A[M]` determined by the ring map `f` and the `f`-semilinear map `ψ`
of coefficients. Unlike `Deformation.Artin.siteSquareZeroLiftBaseChangeMap`, that morphism is
supplied here rather than assumed: it is `Deformation.Artin.squareZeroOverBaseMap`. -/
public def squareZeroLiftClassesBaseChange {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M) :
    squareZeroLiftClasses C B S hS toSC hC p y hy N :=
  siteSquareZeroLiftBaseChangeMap B S hS toS hA toSC hC p x y hx hy φ₀ f ψ hp
    (algebraOverMapOfRingHom f B S hS toS toSC hA hC hf) hφ₀
    (squareZeroOverBaseMap f B S hS toS toSC hf M N (restrictScalarsAddHom f ψ)
      (restrictScalarsAddHom_smul f ψ))
    (algebraOverMap_comp_squareZeroArrow f B S hS toS toSC hA hC hf M N
      (restrictScalarsAddHom f ψ) (restrictScalarsAddHom_smul f ψ))
    (isSiteSquareZeroBaseMap_squareZeroOverBaseMap f B S hS toS toSC hf ψ) a

include hf hφ₀ hp in
/-- The transition of Remark 07YA on lift classes has its defining property. -/
public theorem isSiteSquareZeroLiftBaseChange_squareZeroLiftClassesBaseChange
    {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (a : squareZeroLiftClasses A B S hS toS hA p x hx M) :
    IsSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f ψ a
      (squareZeroLiftClassesBaseChange f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ a) :=
  isSiteSquareZeroLiftBaseChange_siteSquareZeroLiftBaseChangeMap B S hS toS hA toSC hC
    p x y hx hy φ₀ f ψ hp (algebraOverMapOfRingHom f B S hS toS toSC hA hC hf) hφ₀ _ _ _ a

/-! ### The induced map on tangent modules -/

variable (Tx : TangentFunctorData A B S hS toS hA p x hx)
  (Ty : TangentFunctorData C B S hS toSC hC p y hy)

include hf hφ₀ hp in
/-- **The map `T_x(M) ⟶ T_y(N)` of Remark 07YA.** The transition on lift classes read through
the two bijections of the tangent functors with lift classes. -/
public def tangentBaseChangeMap {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (a : (Tx.functor.obj M : Type (max (u + 1) v w))) :
    (Ty.functor.obj N : Type (max (u + 1) v w)) :=
  (Ty.liftEquiv N).symm (squareZeroLiftClassesBaseChange f B S hS toS hA toSC hC hf
    p x y hx hy φ₀ hφ₀ hp ψ (Tx.liftEquiv M a))

include hf hφ₀ hp in
/-- The map `T_x(M) ⟶ T_y(N)` of Remark 07YA realizes the transition on lift classes. -/
public theorem isSiteSquareZeroLiftBaseChange_tangentBaseChangeMap
    {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (a : (Tx.functor.obj M : Type (max (u + 1) v w))) :
    IsSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f ψ
      (Tx.liftEquiv M a)
      (Ty.liftEquiv N (tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
        Tx Ty ψ a)) := by
  have he : Ty.liftEquiv N (tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀
      hφ₀ hp Tx Ty ψ a) =
      squareZeroLiftClassesBaseChange f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ
        (Tx.liftEquiv M a) :=
    (Ty.liftEquiv N).apply_symm_apply _
  rw [he]
  exact isSiteSquareZeroLiftBaseChange_squareZeroLiftClassesBaseChange f B S hS toS hA
    toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ (Tx.liftEquiv M a)

include hf hφ₀ hp in
/-- **The map of Remark 07YA is natural in both coefficient modules.** Given module maps
`ξ : M ⟶ M'` and `χ : N ⟶ N'` and semilinear maps `ψ`, `ψ'` making the square of coefficients
commute, the two routes from `T_x(M)` to `T_y(N')` agree. -/
public theorem tangentBaseChangeMap_natural
    {M M' : SiteModule A B} {N N' : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (ψ' : M'.obj ⟶ (ModuleCat.restrictScalars f).obj N'.obj)
    (ξ : M ⟶ M') (χ : N ⟶ N')
    (hcomm : ξ.hom ≫ ψ' = ψ ≫ (ModuleCat.restrictScalars f).map χ.hom)
    (a : (Tx.functor.obj M : Type (max (u + 1) v w))) :
    tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Tx Ty ψ'
        (Tx.functor.map ξ a) =
      Ty.functor.map χ (tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
        Tx Ty ψ a) := by
  apply (Ty.liftEquiv N').injective
  refine eq_of_isSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f
    (ξ.hom ≫ ψ') (a := Tx.liftEquiv M a) ?_ ?_
  · exact isSiteSquareZeroLiftBaseChange_comp_source f B S hS toS hA toSC hC p x y hx hy φ₀ hp
      ξ ψ' (Tx.liftEquiv_natural ξ a)
      (isSiteSquareZeroLiftBaseChange_tangentBaseChangeMap f B S hS toS hA toSC hC hf
        p x y hx hy φ₀ hφ₀ hp Tx Ty ψ' (Tx.functor.map ξ a))
  · rw [hcomm]
    exact isSiteSquareZeroLiftBaseChange_comp_target f B S hS toS hA toSC hC p x y hx hy φ₀ hp
      ψ χ
      (isSiteSquareZeroLiftBaseChange_tangentBaseChangeMap f B S hS toS hA toSC hC hf
        p x y hx hy φ₀ hφ₀ hp Tx Ty ψ a)
      (Ty.liftEquiv_natural χ _)

/-! ### `A`-linearity of the map on tangent modules -/

/-- The `f`-semilinear map `M × M ⟶ N × N` attached to an `f`-semilinear map `M ⟶ N`. -/
public def siteModuleProdSemilinear {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    (siteModuleProd A B hA M M).obj ⟶
      (ModuleCat.restrictScalars f).obj (siteModuleProd C B hC N N).obj :=
  restrictScalarsHom f (fun z => (ψ z.1, ψ z.2))
    (fun _ _ => Prod.ext (_root_.map_add _ _ _) (_root_.map_add _ _ _))
    (fun r z => Prod.ext (restrictScalarsAddHom_smul f ψ r z.1)
      (restrictScalarsAddHom_smul f ψ r z.2))

/-- The first projection commutes with the product of a semilinear map with itself. -/
public theorem siteModuleFst_comp_prodSemilinear {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    (siteModuleFst A B hA M M).hom ≫ ψ =
      siteModuleProdSemilinear f B hA hC ψ ≫
        (ModuleCat.restrictScalars f).map (siteModuleFst C B hC N N).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

/-- The second projection commutes with the product of a semilinear map with itself. -/
public theorem siteModuleSnd_comp_prodSemilinear {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    (siteModuleSnd A B hA M M).hom ≫ ψ =
      siteModuleProdSemilinear f B hA hC ψ ≫
        (ModuleCat.restrictScalars f).map (siteModuleSnd C B hC N N).hom := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  rfl

/-- The codiagonal commutes with the product of a semilinear map with itself: this is
additivity of the semilinear map. -/
public theorem siteModuleCodiag_comp_prodSemilinear {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    (siteModuleCodiag A B hA M).hom ≫ ψ =
      siteModuleProdSemilinear f B hA hC ψ ≫
        (ModuleCat.restrictScalars f).map (siteModuleCodiag C B hC N).hom :=
  ModuleCat.hom_ext (LinearMap.ext fun z => _root_.map_add (ModuleCat.Hom.hom ψ) z.1 z.2)

/-- Scalar multiplication by `r : A` on the source corresponds to scalar multiplication by
`f r` on the target. -/
public theorem smul_comp_semilinear {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (r : A) :
    ((r • 𝟙 M : M ⟶ M)).hom ≫ ψ =
      ψ ≫ (ModuleCat.restrictScalars f).map ((f r • 𝟙 N : N ⟶ N)).hom := by
  ext m
  exact restrictScalarsAddHom_smul f ψ r m

include hf hφ₀ hp in
/-- **The map `T_x(M) ⟶ T_y(N)` of Remark 07YA is additive.** The three naturality squares at
the two projections and the codiagonal of `M × M` and `N × N` turn the addition on `T_x` into
the addition on `T_y`. -/
public theorem tangentBaseChangeMap_add {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (u v : (Tx.functor.obj M : Type (max (u + 1) v w))) :
    tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Tx Ty ψ (u + v) =
      tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Tx Ty ψ u +
        tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Tx Ty ψ v :=
  add_of_natural_siteModuleProd B hA hC Tx.functor Ty.functor M N _ _
    (fun a => tangentBaseChangeMap_natural f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
      Tx Ty (siteModuleProdSemilinear f B hA hC ψ) ψ (siteModuleFst A B hA M M)
      (siteModuleFst C B hC N N) (siteModuleFst_comp_prodSemilinear f B hA hC ψ) a)
    (fun a => tangentBaseChangeMap_natural f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
      Tx Ty (siteModuleProdSemilinear f B hA hC ψ) ψ (siteModuleSnd A B hA M M)
      (siteModuleSnd C B hC N N) (siteModuleSnd_comp_prodSemilinear f B hA hC ψ) a)
    (fun a => tangentBaseChangeMap_natural f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
      Tx Ty (siteModuleProdSemilinear f B hA hC ψ) ψ (siteModuleCodiag A B hA M)
      (siteModuleCodiag C B hC N) (siteModuleCodiag_comp_prodSemilinear f B hA hC ψ) a)
    u v

include hf hφ₀ hp in
/-- **The map `T_x(M) ⟶ T_y(N)` of Remark 07YA is semilinear over `f`.** -/
public theorem tangentBaseChangeMap_smul {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (r : A)
    (a : (Tx.functor.obj M : Type (max (u + 1) v w))) :
    tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Tx Ty ψ (r • a) =
      f r • tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Tx Ty ψ a := by
  have h := tangentBaseChangeMap_natural f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
    Tx Ty ψ ψ (r • 𝟙 M) (f r • 𝟙 N) (smul_comp_semilinear f B ψ r) a
  rw [map_smul_id_apply Tx.functor M r a,
    map_smul_id_apply Ty.functor N (f r) _] at h
  exact h

include hf hφ₀ hp in
/-- **Remark 07YA for the tangent functor.** For a ring map `f : A ⟶ C`, the restriction
`y = x|_{Spec C}` and an `f`-semilinear map `M ⟶ N` of coefficients, the induced map
`T_x(M) ⟶ T_y(N)` is `A`-linear, where `T_y(N)` is viewed as an `A`-module by restriction of
scalars along `f`. -/
@[stacks 07YA "the A-linear map T_x(M) → T_y(N)"]
public theorem isLinearMap_tangentBaseChangeMap {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    letI : Module A ((Ty.functor.obj N : Type (max (u + 1) v w))) := Module.compHom _ f
    IsLinearMap A
      (tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Tx Ty ψ) :=
  let : Module A ((Ty.functor.obj N : Type (max (u + 1) v w))) := Module.compHom _ f
  { map_add := tangentBaseChangeMap_add f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
      Tx Ty ψ
    map_smul := tangentBaseChangeMap_smul f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
      Tx Ty ψ }

include hf hφ₀ hp in
/-- The map `T_x(M) ⟶ T_y(N)` of Remark 07YA, packaged as an `A`-linear map. -/
public def tangentBaseChangeLinearMap {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    letI : Module A ((Ty.functor.obj N : Type (max (u + 1) v w))) := Module.compHom _ f
    ((Tx.functor.obj M : Type (max (u + 1) v w))) →ₗ[A]
      ((Ty.functor.obj N : Type (max (u + 1) v w))) :=
  letI : Module A ((Ty.functor.obj N : Type (max (u + 1) v w))) := Module.compHom _ f
  IsLinearMap.mk' _ (isLinearMap_tangentBaseChangeMap f B S hS toS hA toSC hC hf
    p x y hx hy φ₀ hφ₀ hp Tx Ty ψ)

end Transition

end Deformation.Artin
