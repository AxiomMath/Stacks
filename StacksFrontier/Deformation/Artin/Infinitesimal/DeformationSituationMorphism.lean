module

public import StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLiftsRestriction
public import StacksFrontier.Deformation.Artin.Infinitesimal.BaseChangeLinear

/-!
# Functoriality of `Inf_x` and `T_x` (Stacks 07YA)

Let `𝒳` be a category fibred in groupoids over the big fppf site of a scheme `S` satisfying
(RS*), let `f : A ⟶ C` be a map of `S`-algebras and `y = x|_{Spec C}`, presented by an arrow
`φ₀ : y ⟶ x` over `Spec C ⟶ Spec A`. Remark 07YA asserts:

1. for an `A`-module `M`, a `C`-module `N` and an `A`-linear map `M ⟶ N`, the pullback functor
   `Lift(x, A[M]) ⟶ Lift(y, C[N])` induces `A`-linear maps `Inf_x(M) ⟶ Inf_y(N)` and
   `T_x(M) ⟶ T_y(N)` on the functors of Stacks 07Y9;
2. for a morphism of deformation situations `(y, C' → C) ⟶ (x, A' → A)`, with kernels `I`
   and `J`, the comparison `Inf_x(I) ≅ Inf(x'/x)` and the action of `T_x(I)` on `Lift(x, A')`
   of Stacks 07Y9 are compatible with these maps and with pullback along `Spec C' ⟶ Spec A'`.

The map on tangent modules and its `A`-linearity are
`Deformation.Artin.tangentBaseChangeMap` and `Deformation.Artin.isLinearMap_tangentBaseChangeMap`
(`StacksFrontier.Deformation.Artin.Infinitesimal.BaseChangeLinear`). This file builds the map on
infinitesimal automorphisms, `Deformation.Artin.infBaseChangeMap`: an automorphism of the
trivial deformation of `x` over `Spec A[M]` is restricted along the arrow of trivial
deformations over `Spec C[N] ⟶ Spec A[M]` (`Deformation.Artin.infBaseChangeArrow`), which is
pinned by its compatibility with the two retractions. Its `A`-linearity is again naturality in
both coefficient modules, here using that the infinitesimal automorphisms of a trivial
deformation commute (Stacks 06I6, a consequence of (RS*)) so that the restriction does not
depend on the arrow used.

For the two squares, the comparisons and the actions of Stacks 07Y9 are pinned by geometric
differences (`Deformation.Artin.IsGeometricInfDifference`,
`Deformation.Artin.IsGeometricDifference`), these pins are unique
(`Deformation.Artin.InfComparisonData.equiv_eq_of_isGeometricInfDifference`,
`Deformation.Artin.ActionOnLiftsData.action_eq_of_isGeometricDifference`) and they restrict
along a morphism of deformation situations (`Deformation.Artin.IsGeometricInfDifference.restrict`,
`Deformation.Artin.IsGeometricDifference.restrict`); these live in
`StacksFrontier.Deformation.Artin.Infinitesimal.ActionOnLifts`, beside the private constructions
they use.

## Main definitions

* `Deformation.Artin.infBaseChangeMap` — the map `Inf_x(M) ⟶ Inf_y(N)` of Remark 07YA.
* `Deformation.Artin.kernelBaseChange` — the semilinear map of kernels `I ⟶ J` of a morphism of
  deformation situations.
* `Deformation.Artin.deformationSituationMap` — the morphism `Spec C' ⟶ Spec A'` of the site.

## Main results

* `Deformation.Artin.isLinearMap_infBaseChangeMap` — the map on `Inf` is `A`-linear.
* `Deformation.Artin.isLinearMap_infBaseChangeMap_tangentBaseChangeMap` — **Stacks 07YA, the
  maps**: both maps are induced by the pullback functor on lifts and are `A`-linear.
* `Deformation.Artin.infComparison_restrict`, `Deformation.Artin.action_restrict` — the two
  squares of Remark 07YA.
* `Deformation.Artin.infComparison_restrict_and_action_restrict` — **Stacks 07YA, the two
  squares**.

## References

* [Stacks Project, Tag 07YA](https://stacks.math.columbia.edu/tag/07YA)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Functor

attribute [local implicit_reducible] Deformation.Artin.squareZeroRing
  CategoryTheory.Functor.Fiber
  CategoryTheory.Functor.Fiber.fiberInclusion
  CategoryTheory.Functor.ChoiceOfPullbacks.pullbackFunctor

universe u v w

namespace Deformation.Artin

/-! ### The map `Inf_x(M) ⟶ Inf_y(N)` -/

section InfBaseChange

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

include hf in
/-- The morphism `Spec C[N] ⟶ Spec A[M]` of Stacks 07YA is compatible with the two
retractions onto `Spec A` and `Spec C`. -/
public theorem squareZeroOverBaseMap_comp_squareZeroRetraction {M : SiteModule A B}
    {N : SiteModule C B} (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    squareZeroOverBaseMap f B S hS toS toSC hf M N (restrictScalarsAddHom f ψ)
        (restrictScalarsAddHom_smul f ψ) ≫ squareZeroRetraction A B S hS toS hA M =
      squareZeroRetraction C B S hS toSC hC N ≫
        algebraOverMapOfRingHom f B S hS toS toSC hA hC hf := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ)
      (restrictScalarsAddHom_smul f ψ))) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom A M.obj)) =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.inlHom C N.obj)) ≫
      Spec.map (CommRingCat.ofHom f)
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext a
  · rfl
  · change restrictScalarsAddHom f ψ (TrivSqZeroExt.inl a).snd = (TrivSqZeroExt.inl (f a)).snd
    rw [TrivSqZeroExt.snd_inl, TrivSqZeroExt.snd_inl, map_zero]

include hf hφ₀ hp in
/-- **The arrow of trivial deformations of Stacks 07YA.** The trivial deformation of `y` over
`Spec C[N]` maps to the trivial deformation of `x` over `Spec A[M]` over the morphism
`Spec C[N] ⟶ Spec A[M]` induced by `f` and `ψ`, compatibly with the retractions to `y ⟶ x`. -/
public def infBaseChangeArrow {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    (trivialDeformation C B S hS toSC hC p y hy hp N).1.right ⟶
      (trivialDeformation A B S hS toS hA p x hx hp M).1.right :=
  haveI := trivialRetract_isHomLift A B S hS toS hA p x hx hp M
  haveI := hp.isStronglyCartesian_homLift (squareZeroRetraction A B S hS toS hA M)
    (trivialRetract A B S hS toS hA p x hx hp M)
  haveI := trivialRetract_isHomLift C B S hS toSC hC p y hy hp N
  haveI := hφ₀
  IsStronglyCartesian.map p (squareZeroRetraction A B S hS toS hA M)
    (trivialRetract A B S hS toS hA p x hx hp M)
    (squareZeroOverBaseMap_comp_squareZeroRetraction f B S hS toS hA toSC hC hf ψ).symm
    (trivialRetract C B S hS toSC hC p y hy hp N ≫ φ₀)

include hf hφ₀ hp in
/-- The arrow of trivial deformations lies over `Spec C[N] ⟶ Spec A[M]`. -/
public theorem infBaseChangeArrow_isHomLift {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    p.IsHomLift (squareZeroOverBaseMap f B S hS toS toSC hf M N (restrictScalarsAddHom f ψ)
        (restrictScalarsAddHom_smul f ψ))
      (infBaseChangeArrow f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ) := by
  have := trivialRetract_isHomLift A B S hS toS hA p x hx hp M
  have := hp.isStronglyCartesian_homLift (squareZeroRetraction A B S hS toS hA M)
    (trivialRetract A B S hS toS hA p x hx hp M)
  have := trivialRetract_isHomLift C B S hS toSC hC p y hy hp N
  have := hφ₀
  exact IsStronglyCartesian.map_isHomLift p _ _ _ _

include hf hφ₀ hp in
/-- The arrow of trivial deformations is compatible with `y ⟶ x`. -/
public theorem infBaseChangeArrow_compat {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    (trivialDeformation C B S hS toSC hC p y hy hp N).1.hom ≫
        infBaseChangeArrow f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ =
      φ₀ ≫ (trivialDeformation A B S hS toS hA p x hx hp M).1.hom := by
  have := trivialRetract_isHomLift A B S hS toS hA p x hx hp M
  have := hp.isStronglyCartesian_homLift (squareZeroRetraction A B S hS toS hA M)
    (trivialRetract A B S hS toS hA p x hx hp M)
  have := trivialRetract_isHomLift C B S hS toSC hC p y hy hp N
  have := hφ₀
  have := infBaseChangeArrow_isHomLift f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ
  have := underFiber_isHomLift p hy (squareZeroArrow C B S hS toSC hC N)
    (trivialDeformation C B S hS toSC hC p y hy hp N)
  have := underFiber_isHomLift p hx (squareZeroArrow A B S hS toS hA M)
    (trivialDeformation A B S hS toS hA p x hx hp M)
  have hsq := algebraOverMap_comp_squareZeroArrow f B S hS toS toSC hA hC hf M N
    (restrictScalarsAddHom f ψ) (restrictScalarsAddHom_smul f ψ)
  have : p.IsHomLift (algebraOverMapOfRingHom f B S hS toS toSC hA hC hf ≫
      squareZeroArrow A B S hS toS hA M)
      ((trivialDeformation C B S hS toSC hC p y hy hp N).1.hom ≫
        infBaseChangeArrow f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ) := by
    rw [hsq]
    infer_instance
  refine IsStronglyCartesian.ext p (squareZeroRetraction A B S hS toS hA M)
    (trivialRetract A B S hS toS hA p x hx hp M)
    (algebraOverMapOfRingHom f B S hS toS toSC hA hC hf ≫
      squareZeroArrow A B S hS toS hA M) ?_
  rw [Category.assoc, Category.assoc, trivialRetract_fac]
  change _ ≫ IsStronglyCartesian.map p _ _ _ _ ≫ _ = _
  rw [IsStronglyCartesian.fac, ← Category.assoc, trivialRetract_fac, Category.id_comp,
    Category.comp_id]

variable (Inf : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
  (Inf' : InfinitesimalAutomorphismFunctorData C B S hS toSC hC p y hy hp)

include hf hφ₀ hp in
/-- **The map `Inf_x(M) ⟶ Inf_y(N)` of Remark 07YA.** An infinitesimal automorphism of the
trivial deformation of `x` over `Spec A[M]` is restricted along the arrow of trivial
deformations over `Spec C[N] ⟶ Spec A[M]`, and read through the two identifications of the
functors of Stacks 07Y9 with infinitesimal automorphisms. -/
public def infBaseChangeMap {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (a : (Inf.functor.obj M : Type w)) : (Inf'.functor.obj N : Type w) :=
  (Inf'.autEquiv N).symm (liftEndRestrict p hp φ₀
    (infBaseChangeArrow f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ)
    (infBaseChangeArrow_isHomLift f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ)
    (infBaseChangeArrow_compat f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ)
    (Inf.autEquiv M a))

include hf hφ₀ hp in
/-- The map `Inf_x(M) ⟶ Inf_y(N)` of Remark 07YA restricts along the arrow of trivial
deformations. -/
public theorem infBaseChangeMap_fac {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (a : (Inf.functor.obj M : Type w)) :
    (Inf'.autEquiv N (infBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf'
        ψ a)).1.right ≫ infBaseChangeArrow f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ =
      infBaseChangeArrow f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ ≫
        (Inf.autEquiv M a).1.right := by
  rw [infBaseChangeMap, Equiv.apply_symm_apply]
  exact liftEndRestrict_fac p hp φ₀ _ _ _ _

include hf hφ₀ hp in
/-- **The map `Inf_x(M) ⟶ Inf_y(N)` is the pullback functor on infinitesimal automorphisms.**
It realizes the transition `Deformation.Artin.IsSiteInfinitesimalAutomorphismBaseChange`. -/
public theorem isSiteInfinitesimalAutomorphismBaseChange_infBaseChangeMap
    {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (a : (Inf.functor.obj M : Type w)) :
    IsSiteInfinitesimalAutomorphismBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f ψ hp
      (Inf.autEquiv M a)
      (Inf'.autEquiv N (infBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
        Inf Inf' ψ a)) := by
  have := infBaseChangeArrow_isHomLift f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ
  exact ⟨_, isSiteSquareZeroBaseMap_squareZeroOverBaseMap f B S hS toS toSC hf ψ,
    infBaseChangeArrow f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ,
    hp.isStronglyCartesian_homLift _ _,
    infBaseChangeArrow_compat f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ,
    infBaseChangeMap_fac f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf' ψ a⟩

include hf in
/-- The morphisms `Spec C[N] ⟶ Spec A[M]` of Stacks 07YA are natural in both coefficient
modules. -/
public theorem squareZeroOverBaseMap_natural {M M' : SiteModule A B} {N N' : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (ψ' : M'.obj ⟶ (ModuleCat.restrictScalars f).obj N'.obj)
    (ξ : M ⟶ M') (χ : N ⟶ N')
    (hcomm : ξ.hom ≫ ψ' = ψ ≫ (ModuleCat.restrictScalars f).map χ.hom) :
    squareZeroOverBaseMap f B S hS toS toSC hf M' N' (restrictScalarsAddHom f ψ')
        (restrictScalarsAddHom_smul f ψ') ≫ squareZeroOverMap A B S hS toS ξ =
      squareZeroOverMap C B S hS toSC χ ≫
        squareZeroOverBaseMap f B S hS toS toSC hf M N (restrictScalarsAddHom f ψ)
          (restrictScalarsAddHom_smul f ψ) := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ')
      (restrictScalarsAddHom_smul f ψ'))) ≫
      Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map ξ.hom.hom).toRingHom) =
    Spec.map (CommRingCat.ofHom (TrivSqZeroExt.map χ.hom.hom).toRingHom) ≫
      Spec.map (CommRingCat.ofHom (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ)
        (restrictScalarsAddHom_smul f ψ)))
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  apply CommRingCat.hom_ext
  ext z
  · change f (TrivSqZeroExt.map ξ.hom.hom z).fst = (TrivSqZeroExt.map χ.hom.hom
      (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ) (restrictScalarsAddHom_smul f ψ) z)).fst
    rw [TrivSqZeroExt.fst_map, TrivSqZeroExt.fst_map]
    rfl
  · change restrictScalarsAddHom f ψ' (TrivSqZeroExt.map ξ.hom.hom z).snd =
      (TrivSqZeroExt.map χ.hom.hom (squareZeroRingBaseMap f (restrictScalarsAddHom f ψ)
        (restrictScalarsAddHom_smul f ψ) z)).snd
    rw [TrivSqZeroExt.snd_map, TrivSqZeroExt.snd_map]
    exact ConcreteCategory.congr_hom hcomm z.snd

/-- Restricting an endomorphism of a trivial deformation along a transition map of trivial
deformations commutes with the transition map. -/
private theorem fiberEndRestrict_trivialTransitionUnder_fac {M M' : SiteModule A B}
    (ξ : M ⟶ M')
    (θ₀ : trivialDeformation A B S hS toS hA p x hx hp M ⟶
      trivialDeformation A B S hS toS hA p x hx hp M) :
    (fiberEndRestrict (Under.post p) (underPost_isFiberedInGroupoids p hp x)
      (trivialTransitionUnder A B S hS toS hA p x hx hp ξ)
      (trivialTransitionUnder_isHomLift A B S hS toS hA p x hx hp ξ) θ₀).1.right ≫
        trivialTransition A B S hS toS hA p x hx hp ξ =
      trivialTransition A B S hS toS hA p x hx hp ξ ≫ θ₀.1.right :=
  congrArg Under.Hom.right (fiberEndRestrict_fac (Under.post p)
    (underPost_isFiberedInGroupoids p hp x) (trivialTransitionUnder A B S hS toS hA p x hx hp ξ)
    (trivialTransitionUnder_isHomLift A B S hS toS hA p x hx hp ξ) θ₀)

include hf hφ₀ hp in
/-- **The map of Remark 07YA on infinitesimal automorphisms is natural in both coefficient
modules.** -/
public theorem infBaseChangeMap_natural (hRS : SatisfiesRSStar B S hS p hp)
    {M M' : SiteModule A B} {N N' : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (ψ' : M'.obj ⟶ (ModuleCat.restrictScalars f).obj N'.obj)
    (ξ : M ⟶ M') (χ : N ⟶ N')
    (hcomm : ξ.hom ≫ ψ' = ψ ≫ (ModuleCat.restrictScalars f).map χ.hom)
    (a : (Inf.functor.obj M : Type w)) :
    infBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf' ψ'
        (Inf.functor.map ξ a) =
      Inf'.functor.map χ (infBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
        Inf Inf' ψ a) := by
  apply (Inf'.autEquiv N').injective
  rw [Inf'.autEquiv_natural, infBaseChangeMap, infBaseChangeMap, Equiv.apply_symm_apply,
    Equiv.apply_symm_apply, Inf.autEquiv_natural, infAutSetFunctor_map_eq,
    infAutSetFunctor_map_eq]
  set θ := Inf.autEquiv M a
  let ρ := infBaseChangeArrow f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ
  let ρ' := infBaseChangeArrow f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ'
  let τA := trivialTransition A B S hS toS hA p x hx hp ξ
  let τC := trivialTransition C B S hS toSC hC p y hy hp χ
  have := infBaseChangeArrow_isHomLift f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ
  have := infBaseChangeArrow_isHomLift f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp ψ'
  have := trivialTransition_isHomLift A B S hS toS hA p x hx hp ξ
  have := trivialTransition_isHomLift C B S hS toSC hC p y hy hp χ
  have hbase := squareZeroOverBaseMap_natural f B S hS toS toSC hf ψ ψ' ξ χ hcomm
  have h₁ : p.IsHomLift (squareZeroOverMap C B S hS toSC χ ≫
      squareZeroOverBaseMap f B S hS toS toSC hf M N (restrictScalarsAddHom f ψ)
        (restrictScalarsAddHom_smul f ψ)) (ρ' ≫ τA) := by
    rw [← hbase]
    infer_instance
  have h₂ : p.IsHomLift (squareZeroOverMap C B S hS toSC χ ≫
      squareZeroOverBaseMap f B S hS toS toSC hf M N (restrictScalarsAddHom f ψ)
        (restrictScalarsAddHom_smul f ψ)) (τC ≫ ρ) := inferInstance
  have hτA : (trivialDeformation A B S hS toS hA p x hx hp M').1.hom ≫ τA =
      (trivialDeformation A B S hS toS hA p x hx hp M).1.hom :=
    Under.w (trivialTransitionUnder A B S hS toS hA p x hx hp ξ)
  have hτC : (trivialDeformation C B S hS toSC hC p y hy hp N').1.hom ≫ τC =
      (trivialDeformation C B S hS toSC hC p y hy hp N).1.hom :=
    Under.w (trivialTransitionUnder C B S hS toSC hC p y hy hp χ)
  refine liftEnd_eq_of_comm p hp φ₀
    (comp_comm_infinitesimalAutomorphism C B S hS toSC hC p y hy hp hRS N')
    (ρ' ≫ τA) (τC ≫ ρ) h₁ h₂ ?_ ?_ θ _ _ ?_ ?_
  · rw [← Category.assoc, infBaseChangeArrow_compat, Category.assoc, hτA]
  · rw [← Category.assoc, hτC, infBaseChangeArrow_compat]
  · rw [← Category.assoc, liftEndRestrict_fac, Category.assoc,
      fiberEndRestrict_trivialTransitionUnder_fac B S hS toS hA p x hx hp ξ, ← Category.assoc]
  · rw [← Category.assoc, fiberEndRestrict_trivialTransitionUnder_fac B S hS toSC hC p y hy hp χ,
      Category.assoc, liftEndRestrict_fac, ← Category.assoc]

include hf hφ₀ hp in
/-- **The map `Inf_x(M) ⟶ Inf_y(N)` of Remark 07YA is additive.** -/
public theorem infBaseChangeMap_add (hRS : SatisfiesRSStar B S hS p hp)
    {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj)
    (u v : (Inf.functor.obj M : Type w)) :
    infBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf' ψ (u + v) =
      infBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf' ψ u +
        infBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf' ψ v :=
  add_of_natural_siteModuleProd B hA hC Inf.functor Inf'.functor M N _ _
    (fun a => infBaseChangeMap_natural f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
      Inf Inf' hRS (siteModuleProdSemilinear f B hA hC ψ) ψ (siteModuleFst A B hA M M)
      (siteModuleFst C B hC N N) (siteModuleFst_comp_prodSemilinear f B hA hC ψ) a)
    (fun a => infBaseChangeMap_natural f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
      Inf Inf' hRS (siteModuleProdSemilinear f B hA hC ψ) ψ (siteModuleSnd A B hA M M)
      (siteModuleSnd C B hC N N) (siteModuleSnd_comp_prodSemilinear f B hA hC ψ) a)
    (fun a => infBaseChangeMap_natural f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
      Inf Inf' hRS (siteModuleProdSemilinear f B hA hC ψ) ψ (siteModuleCodiag A B hA M)
      (siteModuleCodiag C B hC N) (siteModuleCodiag_comp_prodSemilinear f B hA hC ψ) a)
    u v

include hf hφ₀ hp in
/-- **The map `Inf_x(M) ⟶ Inf_y(N)` of Remark 07YA is semilinear over `f`.** -/
public theorem infBaseChangeMap_smul (hRS : SatisfiesRSStar B S hS p hp)
    {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) (r : A)
    (a : (Inf.functor.obj M : Type w)) :
    infBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf' ψ (r • a) =
      f r • infBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf' ψ a := by
  have h := infBaseChangeMap_natural f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf'
    hRS ψ ψ (r • 𝟙 M) (f r • 𝟙 N) (smul_comp_semilinear f B ψ r) a
  rw [map_smul_id_apply Inf.functor M r a, map_smul_id_apply Inf'.functor N (f r) _] at h
  exact h

include hf hφ₀ hp in
/-- The map `Inf_x(M) ⟶ Inf_y(N)` of Remark 07YA is `A`-linear, where `Inf_y(N)` is an
`A`-module by restriction of scalars along `f`. -/
public theorem isLinearMap_infBaseChangeMap (hRS : SatisfiesRSStar B S hS p hp)
    {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    letI : Module A (Inf'.functor.obj N : Type w) := Module.compHom _ f
    IsLinearMap A (infBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf' ψ) :=
  let : Module A (Inf'.functor.obj N : Type w) := Module.compHom _ f
  { map_add := infBaseChangeMap_add f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf'
      hRS ψ
    map_smul := infBaseChangeMap_smul f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf'
      hRS ψ }

include hf hφ₀ hp in
/-- **Stacks 07YA, the maps.** Let `𝒳` satisfy (RS*), let `f : A ⟶ C` be a map of
`S`-algebras, `y = x|_{Spec C}` (the arrow `φ₀ : y ⟶ x` over `Spec C ⟶ Spec A`), `M` an
`A`-module, `N` a `C`-module and `ψ : M ⟶ N` an `A`-linear map. The pullback functor on lifts
along `Spec C[N] ⟶ Spec A[M]` induces maps `Inf_x(M) ⟶ Inf_y(N)` and `T_x(M) ⟶ T_y(N)` on the
functors of Stacks 07Y9, and both are `A`-linear (with `A` acting on the targets through `f`).
That the maps are induced by the pullback functor is the transition relation each of them
realizes: `Deformation.Artin.IsSiteInfinitesimalAutomorphismBaseChange` and
`Deformation.Artin.IsSiteSquareZeroLiftBaseChange`. The statement holds for every choice of
the functors `Inf_x`, `Inf_y`, `T_x`, `T_y` of Stacks 07Y9. -/
@[stacks 07YA "the A-linear maps Inf_x(M) → Inf_y(N) and T_x(M) → T_y(N) induced by pullback"]
public theorem isLinearMap_infBaseChangeMap_tangentBaseChangeMap
    (hRS : SatisfiesRSStar B S hS p hp)
    (Tx : TangentFunctorData A B S hS toS hA p x hx)
    (Ty : TangentFunctorData C B S hS toSC hC p y hy)
    {M : SiteModule A B} {N : SiteModule C B}
    (ψ : M.obj ⟶ (ModuleCat.restrictScalars f).obj N.obj) :
    letI : Module A (Inf'.functor.obj N : Type w) := Module.compHom _ f
    letI : Module A ((Ty.functor.obj N : Type (max (u + 1) v w))) := Module.compHom _ f
    IsLinearMap A (infBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf'
        ψ) ∧
      (∀ a, IsSiteInfinitesimalAutomorphismBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f ψ hp
        (Inf.autEquiv M a)
        (Inf'.autEquiv N (infBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
          Inf Inf' ψ a))) ∧
      IsLinearMap A (tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
        Tx Ty ψ) ∧
      (∀ a, IsSiteSquareZeroLiftBaseChange B S hS toS hA toSC hC p x y hx hy φ₀ f ψ
        (Tx.liftEquiv M a)
        (Ty.liftEquiv N (tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
          Tx Ty ψ a))) :=
  ⟨isLinearMap_infBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Inf Inf' hRS ψ,
    isSiteInfinitesimalAutomorphismBaseChange_infBaseChangeMap f B S hS toS hA toSC hC hf p x y
      hx hy φ₀ hφ₀ hp Inf Inf' ψ,
    isLinearMap_tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Tx Ty ψ,
    isSiteSquareZeroLiftBaseChange_tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy
      φ₀ hφ₀ hp Tx Ty ψ⟩

end InfBaseChange

/-! ### Morphisms of deformation situations -/

section KernelBaseChange

variable {A C A' C' : Type u} [CommRing A] [CommRing C] [CommRing A'] [CommRing C']
  {f : A →+* C} {q : A' →+* A} (hq : Function.Surjective q) (hsq : RingHom.ker q ^ 2 = ⊥)
  {qC : C' →+* C} (hqC : Function.Surjective qC) (hsqC : RingHom.ker qC ^ 2 = ⊥)
  {f' : A' →+* C'} (hff : qC.comp f' = f.comp q)

include hff in
/-- The image of an element of the kernel of `q` under `f'` lies in the kernel of `qC`. -/
public theorem map_mem_ker_of_comp_eq (i : RingHom.ker q) : f' i ∈ RingHom.ker qC := by
  change qC (f' i) = 0
  rw [← RingHom.comp_apply, hff, RingHom.comp_apply, i.2, map_zero]

include hff in
/-- **The map of kernels of a morphism of deformation situations.** A morphism
`(C' → C) ⟶ (A' → A)` of square-zero thickenings, given by `f' : A' → C'` over `f : A → C`,
restricts to an `f`-semilinear map `I = Ker(A' → A) ⟶ J = Ker(C' → C)`. -/
public def kernelBaseChange :
    letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
    ModuleCat.of A (RingHom.ker q) ⟶
      (ModuleCat.restrictScalars f).obj (ModuleCat.of C (RingHom.ker qC)) :=
  let : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
  let : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
  restrictScalarsHom f
    (fun i : RingHom.ker q => (⟨f' i.1, map_mem_ker_of_comp_eq hff i⟩ : RingHom.ker qC))
    (fun i i' => Subtype.ext (_root_.map_add f' i.1 i'.1))
    (fun a i => by
      obtain ⟨a', rfl⟩ := hq a
      apply Subtype.ext
      have h₁ : ((q a' • i : RingHom.ker q) : A') = a' * i.1 := by
        rw [Stacks.Smooth.kerModule_smul hq hsq a' i]
        rfl
      have h₂ : f (q a') = qC (f' a') := (RingHom.congr_fun hff a').symm
      have h₃ : ((qC (f' a') • (⟨f' i.1, map_mem_ker_of_comp_eq hff i⟩ : RingHom.ker qC) :
          RingHom.ker qC) : C') = f' a' * f' i.1 := by
        rw [Stacks.Smooth.kerModule_smul hqC hsqC (f' a')]
        rfl
      change f' ((q a' • i : RingHom.ker q) : A') =
        ((f (q a') • (⟨f' i.1, map_mem_ker_of_comp_eq hff i⟩ : RingHom.ker qC) :
          RingHom.ker qC) : C')
      rw [h₁, h₂, h₃]
      exact map_mul f' a' i.1)

end KernelBaseChange

section Remark

variable {A C : Type u} [CommRing A] [CommRing C] (f : A →+* C)
  (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  (toS : Spec (.of A) ⟶ S) (hA : B.Contains (Spec (.of A)))
  (toSC : Spec (.of C) ⟶ S) (hC : B.Contains (Spec (.of C)))
  {A' C' : Type u} [CommRing A'] [CommRing C']
  (hA' : B.Contains (Spec (.of A'))) (toS' : B.obj hA' ⟶ B.obj hS)
  (q : A' →+* A) (hq : Function.Surjective q) (hsq : RingHom.ker q ^ 2 = ⊥)
  (gA : algebraOver A B S hS toS hA ⟶ (Over.mk toS' : BigFppfOver B S hS))
  (hgA : B.inclusion.map gA.left = Spec.map (CommRingCat.ofHom q))
  (hC' : B.Contains (Spec (.of C'))) (toSC' : B.obj hC' ⟶ B.obj hS)
  (qC : C' →+* C) (hqC : Function.Surjective qC) (hsqC : RingHom.ker qC ^ 2 = ⊥)
  (gC : algebraOver C B S hS toSC hC ⟶ (Over.mk toSC' : BigFppfOver B S hS))
  (hgC : B.inclusion.map gC.left = Spec.map (CommRingCat.ofHom qC))
  (f' : A' →+* C') (hff : qC.comp f' = f.comp q)
  (hf' : Spec.map (CommRingCat.ofHom f') ≫ B.inclusion.map toS' = B.inclusion.map toSC')

include hgA hgC hff hf' in
/-- A morphism of deformation situations over `S` is in particular a map of `S`-algebras
`A ⟶ C`: the structure morphisms of `Spec A` and `Spec C` factor through those of `Spec A'`
and `Spec C'`. -/
public theorem specMap_comp_eq_of_deformationSituation :
    Spec.map (CommRingCat.ofHom f) ≫ toS = toSC := by
  have wA : B.inclusion.map gA.left ≫ B.inclusion.map toS' = toS :=
    (Functor.map_comp _ _ _).symm.trans (congrArg B.inclusion.map (Over.w gA))
  have wC : B.inclusion.map gC.left ≫ B.inclusion.map toSC' = toSC :=
    (Functor.map_comp _ _ _).symm.trans (congrArg B.inclusion.map (Over.w gC))
  have key : Spec.map (CommRingCat.ofHom f) ≫ Spec.map (CommRingCat.ofHom q) =
      Spec.map (CommRingCat.ofHom qC) ≫ Spec.map (CommRingCat.ofHom f') := by
    rw [← Spec.map_comp, ← Spec.map_comp]
    exact congrArg Spec.map (CommRingCat.hom_ext hff.symm)
  calc Spec.map (CommRingCat.ofHom f) ≫ toS
      = Spec.map (CommRingCat.ofHom f) ≫ (Spec.map (CommRingCat.ofHom q) ≫
          B.inclusion.map toS') :=
        congrArg (Spec.map (CommRingCat.ofHom f) ≫ ·)
          (wA.symm.trans (congrArg (· ≫ B.inclusion.map toS') hgA))
    _ = (Spec.map (CommRingCat.ofHom qC) ≫ Spec.map (CommRingCat.ofHom f')) ≫
          B.inclusion.map toS' :=
        (Category.assoc _ _ _).symm.trans (congrArg (· ≫ B.inclusion.map toS') key)
    _ = Spec.map (CommRingCat.ofHom qC) ≫ B.inclusion.map toSC' :=
        (Category.assoc _ _ _).trans (congrArg (Spec.map (CommRingCat.ofHom qC) ≫ ·) hf')
    _ = toSC := (congrArg (· ≫ B.inclusion.map toSC') hgC.symm).trans wC

include hf' in
/-- The morphism `Spec C' ⟶ Spec A'` of objects of the site over `S` of a morphism of
deformation situations. -/
public def deformationSituationMap :
    (Over.mk toSC' : BigFppfOver B S hS) ⟶ Over.mk toS' :=
  Over.homMk (ObjectProperty.homMk (Spec.map (CommRingCat.ofHom f'))) (ObjectProperty.hom_ext _ hf')

include hgA hgC hff in
/-- The two thickenings and the two maps of a morphism of deformation situations form a
commutative square of objects of the site over `S`. -/
public theorem algebraOverMap_comp_deformationSituation :
    algebraOverMapOfRingHom f B S hS toS toSC hA hC
        (specMap_comp_eq_of_deformationSituation f B S hS toS hA toSC hC hA' toS' q gA hgA hC'
          toSC' qC gC hgC f' hff hf') ≫ gA =
      gC ≫ deformationSituationMap B S hS hA' toS' hC' toSC' f' hf' := by
  apply Over.OverMorphism.ext
  apply ObjectProperty.hom_ext
  change Spec.map (CommRingCat.ofHom f) ≫ B.inclusion.map gA.left =
    B.inclusion.map gC.left ≫ Spec.map (CommRingCat.ofHom f')
  rw [hgA, hgC]
  refine (Spec.map_comp _ _).symm.trans (Eq.trans ?_ (Spec.map_comp _ _))
  exact congrArg Spec.map (CommRingCat.hom_ext hff.symm)

variable {X : Type v} [Category.{w} X] (p : X ⥤ BigFppfOver B S hS) (x y : X)
  (hx : p.obj x = algebraOver A B S hS toS hA)
  (hy : p.obj y = algebraOver C B S hS toSC hC)
  (φ₀ : y ⟶ x)
  (hφ₀ : p.IsHomLift (algebraOverMapOfRingHom f B S hS toS toSC hA hC
    (specMap_comp_eq_of_deformationSituation f B S hS toS hA toSC hC hA' toS' q gA hgA hC'
      toSC' qC gC hgC f' hff hf')) φ₀)
  (hp : p.IsFiberedInGroupoids)

include hφ₀ in
/-- **Stacks 07YA, the square of `Inf`.** Let `(y, C' → C) ⟶ (x, A' → A)` be a morphism of
deformation situations, with kernels `I` and `J`, let `x'` be a lift of `x` to `A'` and
`y' = x'|_{Spec C'}` its restriction. Then the square

`Inf_x(I) ⟶ Inf(x'/x)`, `Inf_y(J) ⟶ Inf(y'/y)`

formed by the comparisons of Stacks 07Y9, the map `Inf_x(I) ⟶ Inf_y(J)` of Remark 07YA and
restriction of infinitesimal automorphisms along `y' ⟶ x'` commutes. -/
public theorem infComparison_restrict (hRS : SatisfiesRSStar B S hS p hp)
    (Infx : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
    (Infy : InfinitesimalAutomorphismFunctorData C B S hS toSC hC p y hy hp)
    (x' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ gA)))
    (y' : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC)))
    (φ : y'.1.right ⟶ x'.1.right)
    (hφ : p.IsHomLift (deformationSituationMap B S hS hA' toS' hC' toSC' f' hf') φ)
    (hφc : y'.1.hom ≫ φ = φ₀ ≫ x'.1.hom)
    (Cx : InfComparisonData A B S hS toS hA p x hx hp Infx A' hA' toS' q hq hsq gA x')
    (Cy : InfComparisonData C B S hS toSC hC p y hy hp Infy C' hC' toSC' qC hqC hsqC gC y')
    (a : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      (Infx.functor.obj ⟨ModuleCat.of A (RingHom.ker q), Cx.kernelIsSiteModule⟩ : Type w)) :
    letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
    Cy.equiv (infBaseChangeMap f B S hS toS hA toSC hC
        (specMap_comp_eq_of_deformationSituation f B S hS toS hA toSC hC hA' toS' q gA hgA hC'
          toSC' qC gC hgC f' hff hf') p x y hx hy φ₀ hφ₀ hp Infx Infy
        (M := ⟨ModuleCat.of A (RingHom.ker q), Cx.kernelIsSiteModule⟩)
        (N := ⟨ModuleCat.of C (RingHom.ker qC), Cy.kernelIsSiteModule⟩)
        (kernelBaseChange hq hsq hqC hsqC hff) a) =
      liftEndRestrict p hp φ₀ φ hφ hφc (Cx.equiv a) := by
  let : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
  let : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
  have hf := specMap_comp_eq_of_deformationSituation f B S hS toS hA toSC hC hA' toS' q gA hgA
    hC' toSC' qC gC hgC f' hff hf'
  let ψ := kernelBaseChange hq hsq hqC hsqC hff
  obtain ⟨e, he, hge⟩ := isSiteSquareZeroBaseMap_squareZeroOverBaseMap f B S hS toS toSC hf
    (M := ⟨ModuleCat.of A (RingHom.ker q), Cx.kernelIsSiteModule⟩)
    (N := ⟨ModuleCat.of C (RingHom.ker qC), Cy.kernelIsSiteModule⟩) ψ
  let kI := squareZeroOverBaseMap f B S hS toS toSC hf
    ⟨ModuleCat.of A (RingHom.ker q), Cx.kernelIsSiteModule⟩
    ⟨ModuleCat.of C (RingHom.ker qC), Cy.kernelIsSiteModule⟩ (restrictScalarsAddHom f ψ)
    (restrictScalarsAddHom_smul f ψ)
  have hρ := infBaseChangeArrow_isHomLift f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
    (M := ⟨ModuleCat.of A (RingHom.ker q), Cx.kernelIsSiteModule⟩)
    (N := ⟨ModuleCat.of C (RingHom.ker qC), Cy.kernelIsSiteModule⟩) ψ
  have hρc := infBaseChangeArrow_compat f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
    (M := ⟨ModuleCat.of A (RingHom.ker q), Cx.kernelIsSiteModule⟩)
    (N := ⟨ModuleCat.of C (RingHom.ker qC), Cy.kernelIsSiteModule⟩) ψ
  have hαI := infBaseChangeMap_fac f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp Infx Infy
    (M := ⟨ModuleCat.of A (RingHom.ker q), Cx.kernelIsSiteModule⟩)
    (N := ⟨ModuleCat.of C (RingHom.ker qC), Cy.kernelIsSiteModule⟩) ψ a
  have hα := liftEndRestrict_fac p hp φ₀ φ hφ hφc (Cx.equiv a)
  refine InfComparisonData.equiv_eq_of_isGeometricInfDifference C B S hS toSC hC p y hy hp hRS
    hgC Cy _ _ (IsGeometricInfDifference.restrict p hp φ₀ hq hsq hqC hsqC hgC hff
      (k := deformationSituationMap B S hS hA' toS' hC' toSC' f' hf') rfl
      Cx.kernelIsSiteModule Cy.kernelIsSiteModule _ ?_ kI hge x' y' φ hφ hφc
      (infBaseChangeArrow f B S hS toS hA toSC hC hf p x y hx hy φ₀ hφ₀ hp
        (M := ⟨ModuleCat.of A (RingHom.ker q), Cx.kernelIsSiteModule⟩)
        (N := ⟨ModuleCat.of C (RingHom.ker qC), Cy.kernelIsSiteModule⟩) ψ) hρ hρc
      _ _ hαI _ _ hα (Cx.equiv_geometric a))
  intro z
  exact ⟨congrArg TrivSqZeroExt.fst (he z), congrArg (fun t => t.snd.1) (he z)⟩

include hφ₀ in
/-- **Stacks 07YA, the square of the actions.** Let `(y, C' → C) ⟶ (x, A' → A)` be a morphism of
deformation situations with kernels `I` and `J`. Pulling back lifts along `Spec C' ⟶ Spec A'`
carries the action of Stacks 07Y9 (2)(b) of `T_x(I)` on `Lift(x, A')` to the action of
`T_y(J)` on `Lift(y, C')`, through the map `T_x(I) ⟶ T_y(J)` of Remark 07YA:
`(a · z)|_{C'} = a|_{T_y(J)} · z|_{C'}`. This holds for every choice of the tangent functors
and of the actions, each action being the one pinned by its geometric difference. -/
public theorem action_restrict (hRS : SatisfiesRSStar B S hS p hp)
    (Tx : TangentFunctorData A B S hS toS hA p x hx)
    (Ty : TangentFunctorData C B S hS toSC hC p y hy)
    (Dx : ActionOnLiftsData A B S hS toS hA p x hx Tx A' hA' toS' q hq hsq gA)
    (Dy : ActionOnLiftsData C B S hS toSC hC p y hy Ty C' hC' toSC' qC hqC hsqC gC)
    (a : letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
      (Tx.functor.obj ⟨ModuleCat.of A (RingHom.ker q), Dx.kernelIsSiteModule⟩ : Type _))
    (z : liftClassesOver A B S hS toS hA p x hx gA) :
    letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
    liftClassesRestrict p hp φ₀ _ hφ₀
        (algebraOverMap_comp_deformationSituation f B S hS toS hA toSC hC hA' toS' q gA hgA hC'
          toSC' qC gC hgC f' hff hf') (Dx.action a z) =
      Dy.action (tangentBaseChangeMap f B S hS toS hA toSC hC
        (specMap_comp_eq_of_deformationSituation f B S hS toS hA toSC hC hA' toS' q gA hgA hC'
          toSC' qC gC hgC f' hff hf') p x y hx hy φ₀ hφ₀ hp Tx Ty
        (M := ⟨ModuleCat.of A (RingHom.ker q), Dx.kernelIsSiteModule⟩)
        (N := ⟨ModuleCat.of C (RingHom.ker qC), Dy.kernelIsSiteModule⟩)
        (kernelBaseChange hq hsq hqC hsqC hff) a)
        (liftClassesRestrict p hp φ₀ _ hφ₀
          (algebraOverMap_comp_deformationSituation f B S hS toS hA toSC hC hA' toS' q gA hgA
            hC' toSC' qC gC hgC f' hff hf') z) := by
  let : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
  let : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
  have hf := specMap_comp_eq_of_deformationSituation f B S hS toS hA toSC hC hA' toS' q gA hgA
    hC' toSC' qC gC hgC f' hff hf'
  let ψ := kernelBaseChange hq hsq hqC hsqC hff
  obtain ⟨e, he, hge⟩ := isSiteSquareZeroBaseMap_squareZeroOverBaseMap f B S hS toS toSC hf
    (M := ⟨ModuleCat.of A (RingHom.ker q), Dx.kernelIsSiteModule⟩)
    (N := ⟨ModuleCat.of C (RingHom.ker qC), Dy.kernelIsSiteModule⟩) ψ
  let kI := squareZeroOverBaseMap f B S hS toS toSC hf
    ⟨ModuleCat.of A (RingHom.ker q), Dx.kernelIsSiteModule⟩
    ⟨ModuleCat.of C (RingHom.ker qC), Dy.kernelIsSiteModule⟩ (restrictScalarsAddHom f ψ)
    (restrictScalarsAddHom_smul f ψ)
  have hkM := algebraOverMap_comp_squareZeroArrow f B S hS toS toSC hA hC hf
    ⟨ModuleCat.of A (RingHom.ker q), Dx.kernelIsSiteModule⟩
    ⟨ModuleCat.of C (RingHom.ker qC), Dy.kernelIsSiteModule⟩ (restrictScalarsAddHom f ψ)
    (restrictScalarsAddHom_smul f ψ)
  have hdiff : IsGeometricDifference A B S hS toS hA p x hx Tx A' hA' toS' q hq hsq gA
      Dx.kernelIsSiteModule (Dx.action a z) z a := by
    have h := Dx.difference_geometric (Dx.action a z) z
    rwa [Dx.action_difference] at h
  -- the tangent vector `a|_{T_y(J)}` is the restriction of `a`
  have hab : ∀ (t : (Under.post p).Fiber (Under.mk (eqToHom hx ≫
        squareZeroArrow A B S hS toS hA ⟨ModuleCat.of A (RingHom.ker q), Dx.kernelIsSiteModule⟩)))
      (t' : (Under.post p).Fiber (Under.mk (eqToHom hy ≫
        squareZeroArrow C B S hS toSC hC ⟨ModuleCat.of C (RingHom.ker qC), Dy.kernelIsSiteModule⟩)))
      (ρ : t'.1.right ⟶ t.1.right), p.IsHomLift kI ρ → t'.1.hom ≫ ρ = φ₀ ≫ t.1.hom →
      Quotient.mk _ t = Tx.liftEquiv _ a →
      Quotient.mk _ t' = Ty.liftEquiv _ (tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx
        hy φ₀ hφ₀ hp Tx Ty (M := ⟨ModuleCat.of A (RingHom.ker q), Dx.kernelIsSiteModule⟩)
        (N := ⟨ModuleCat.of C (RingHom.ker qC), Dy.kernelIsSiteModule⟩) ψ a) := by
    intro t t' ρ hρ hρc ht
    obtain ⟨a₁, b₁, ha₁, hb₁, g, hg, φ, hφ, hφc⟩ :=
      isSiteSquareZeroLiftBaseChange_tangentBaseChangeMap f B S hS toS hA toSC hC hf p x y hx hy
        φ₀ hφ₀ hp Tx Ty (M := ⟨ModuleCat.of A (RingHom.ker q), Dx.kernelIsSiteModule⟩)
        (N := ⟨ModuleCat.of C (RingHom.ker qC), Dy.kernelIsSiteModule⟩) ψ a
    have hgk : g = kI := eq_of_isSiteSquareZeroBaseMap B S hS toS toSC hg
      (isSiteSquareZeroBaseMap_squareZeroOverBaseMap f B S hS toS toSC hf
        (M := ⟨ModuleCat.of A (RingHom.ker q), Dx.kernelIsSiteModule⟩)
        (N := ⟨ModuleCat.of C (RingHom.ker qC), Dy.kernelIsSiteModule⟩) ψ)
    subst hgk
    rw [← hb₁]
    exact liftClass_eq_of_restriction p hp φ₀ ρ hρ hρc φ hφ.toIsHomLift hφc (ht.trans ha₁.symm)
  refine (ActionOnLiftsData.action_eq_of_isGeometricDifference C B S hS toSC hC p y hy hp hRS
    hgC Dy _ _ _ ?_).symm
  refine IsGeometricDifference.restrict p hp φ₀ hq hsq hqC hsqC hgC hff
    (k := deformationSituationMap B S hS hA' toS' hC' toSC' f' hf') rfl
    Dx.kernelIsSiteModule Dy.kernelIsSiteModule _ ?_ kI hge _ hφ₀
    (algebraOverMap_comp_deformationSituation f B S hS toS hA toSC hC hA' toS' q gA hgA hC'
      toSC' qC gC hgC f' hff hf') hkM Tx Ty a _ hab (Dx.action a z) z hdiff
  intro z
  exact ⟨congrArg TrivSqZeroExt.fst (he z), congrArg (fun t => t.snd.1) (he z)⟩

include hφ₀ in
/-- **Stacks 07YA, the two squares.** Let `𝒳` satisfy (RS*) and let `(y, C' → C) ⟶ (x, A' → A)`
be a morphism of deformation situations: `f' : A' → C'` over `f : A → C`, compatibly with the
structure morphisms to `S`, and `φ₀ : y ⟶ x` over `Spec C ⟶ Spec A`. Let `I = Ker(A' → A)`,
`J = Ker(C' → C)`, with the map `I ⟶ J` induced by `f'`.

* For a lift `x'` of `x` to `A'` and its restriction `y'` to `C'` (any lift of `y` with an
  arrow `y' ⟶ x'` over `Spec C' ⟶ Spec A'` compatible with `φ₀`), the square
  `Inf_x(I) ⟶ Inf(x'/x) ⟶ Inf(y'/y)` = `Inf_x(I) ⟶ Inf_y(J) ⟶ Inf(y'/y)` commutes.
* The square `T_x(I) × Lift(x, A') ⟶ Lift(x, A') ⟶ Lift(y, C')` =
  `T_x(I) × Lift(x, A') ⟶ T_y(J) × Lift(y, C') ⟶ Lift(y, C')` commutes.

The horizontal maps are the comparisons and the actions of Stacks 07Y9, the vertical ones the
maps of Remark 07YA and the pullback of lifts along `Spec C' ⟶ Spec A'`. All the data of
Stacks 07Y9 (the functors `Inf`, `T`, the comparisons and the actions) are arbitrary: each is
pinned by its geometric difference, which is what the proof restricts. -/
@[stacks 07YA "the two commutative squares for a morphism of deformation situations"]
public theorem infComparison_restrict_and_action_restrict (hRS : SatisfiesRSStar B S hS p hp)
    (Infx : InfinitesimalAutomorphismFunctorData A B S hS toS hA p x hx hp)
    (Infy : InfinitesimalAutomorphismFunctorData C B S hS toSC hC p y hy hp)
    (x' : (Under.post p).Fiber (Under.mk (eqToHom hx ≫ gA)))
    (y' : (Under.post p).Fiber (Under.mk (eqToHom hy ≫ gC)))
    (φ : y'.1.right ⟶ x'.1.right)
    (hφ : p.IsHomLift (deformationSituationMap B S hS hA' toS' hC' toSC' f' hf') φ)
    (hφc : y'.1.hom ≫ φ = φ₀ ≫ x'.1.hom)
    (Cx : InfComparisonData A B S hS toS hA p x hx hp Infx A' hA' toS' q hq hsq gA x')
    (Cy : InfComparisonData C B S hS toSC hC p y hy hp Infy C' hC' toSC' qC hqC hsqC gC y')
    (Tx : TangentFunctorData A B S hS toS hA p x hx)
    (Ty : TangentFunctorData C B S hS toSC hC p y hy)
    (Dx : ActionOnLiftsData A B S hS toS hA p x hx Tx A' hA' toS' q hq hsq gA)
    (Dy : ActionOnLiftsData C B S hS toSC hC p y hy Ty C' hC' toSC' qC hqC hsqC gC) :
    letI : Module A (RingHom.ker q) := Stacks.Smooth.kerModule hq hsq
    letI : Module C (RingHom.ker qC) := Stacks.Smooth.kerModule hqC hsqC
    (∀ a : (Infx.functor.obj ⟨ModuleCat.of A (RingHom.ker q), Cx.kernelIsSiteModule⟩ : Type w),
      Cy.equiv (infBaseChangeMap f B S hS toS hA toSC hC
          (specMap_comp_eq_of_deformationSituation f B S hS toS hA toSC hC hA' toS' q gA hgA hC'
          toSC' qC gC hgC f' hff hf') p x y hx hy φ₀ hφ₀ hp Infx Infy
          (M := ⟨ModuleCat.of A (RingHom.ker q), Cx.kernelIsSiteModule⟩)
          (N := ⟨ModuleCat.of C (RingHom.ker qC), Cy.kernelIsSiteModule⟩)
          (kernelBaseChange hq hsq hqC hsqC hff) a) =
        liftEndRestrict p hp φ₀ φ hφ hφc (Cx.equiv a)) ∧
    (∀ (a : (Tx.functor.obj ⟨ModuleCat.of A (RingHom.ker q), Dx.kernelIsSiteModule⟩ : Type _))
      (z : liftClassesOver A B S hS toS hA p x hx gA),
      liftClassesRestrict p hp φ₀ _ hφ₀
          (algebraOverMap_comp_deformationSituation f B S hS toS hA toSC hC hA' toS' q gA hgA
            hC' toSC' qC gC hgC f' hff hf') (Dx.action a z) =
        Dy.action (tangentBaseChangeMap f B S hS toS hA toSC hC
          (specMap_comp_eq_of_deformationSituation f B S hS toS hA toSC hC hA' toS' q gA hgA hC'
          toSC' qC gC hgC f' hff hf') p x y hx hy φ₀ hφ₀ hp Tx Ty
          (M := ⟨ModuleCat.of A (RingHom.ker q), Dx.kernelIsSiteModule⟩)
          (N := ⟨ModuleCat.of C (RingHom.ker qC), Dy.kernelIsSiteModule⟩)
          (kernelBaseChange hq hsq hqC hsqC hff) a)
          (liftClassesRestrict p hp φ₀ _ hφ₀
            (algebraOverMap_comp_deformationSituation f B S hS toS hA toSC hC hA' toS' q gA hgA
              hC' toSC' qC gC hgC f' hff hf') z)) :=
  ⟨infComparison_restrict f B S hS toS hA toSC hC hA' toS' q hq hsq gA hgA hC' toSC' qC hqC hsqC
      gC hgC f' hff hf' p x y hx hy φ₀ hφ₀ hp hRS Infx Infy x' y' φ hφ hφc Cx Cy,
    action_restrict f B S hS toS hA toSC hC hA' toS' q hq hsq gA hgA hC' toSC' qC hqC hsqC gC hgC
      f' hff hf' p x y hx hy φ₀ hφ₀ hp hRS Tx Ty Dx Dy⟩

end Remark

end Deformation.Artin
