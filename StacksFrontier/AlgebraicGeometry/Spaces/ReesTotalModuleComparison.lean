module

public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraImageModuleDegreeMaps
public import StacksFrontier.AlgebraicGeometry.Spaces.ReesModuleCohomologyFinite
public import StacksFrontier.AlgebraicGeometry.Spaces.PolynomialBaseChangeCohomologyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineCohomologyPushforwardNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedFibreGradedTwistVanishing

/-!
# The total module of a Rees algebra base change

Let `T` be an affine object of the site, `A = Γ(T₀, ⊤)`, `f : X ⟶ h_T`, `J ⊆ A` an ideal,
`R = A[Jt] ⊆ A[t]` the Rees algebra, `π : X_R ⟶ X`, `π' : X_{A[t]} ⟶ X`, `ψ : X_{A[t]} ⟶ X_R` the
base changes and, for an `𝒪_X`-module `N`, `V = π_*ψ_*ψ^*π^*N`. We define the action of `A[t]` on
`H^p(X, V)` and show that `V ≅ π'_*π'^*N`, compatibly with the units and with the action. We also
compute, for abstract functors, the image of an element under such a comparison followed by the
action of a scalar.

## Main definitions

* `AlgebraicGeometry.Space.modulesCohomologyFunctor`: `H^p(Y, −)` as a functor.
* `AlgebraicGeometry.Space.baseScalarRingHom`: `A ⟶ Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.Space.reesTotalCohomologyAction`: `A[t] ⟶ End(H^p(X, V))`.

## Main results

* `AlgebraicGeometry.Space.reesTotalCohomologyAction_C`: the constants act through `Γ(X, 𝒪_X)`.
* `AlgebraicGeometry.Space.exists_isIso_algebraImageTotal`: `V ≅ π'_*π'^*N`.
* `ModuleCat.comparison_apply_of_fac`: the element computation for abstract functors.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Polynomial
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.SiteModules

universe v u

/-- An additive functor to modules turns a ring hom into endomorphisms of an object into a ring
hom into the additive endomorphisms of its image. -/
def CategoryTheory.Functor.endRingHomOfMap {C : Type*} [Category C] [Preadditive C] {Γ : Type*}
    [Ring Γ] (H : C ⥤ ModuleCat.{v} Γ) [H.Additive] {R : Type*} [CommRing R] (V : C)
    (ρ : R → (V ⟶ V)) (h1 : ρ 1 = 𝟙 V) (hmul : ∀ c d, ρ (c * d) = ρ c ≫ ρ d)
    (hadd : ∀ c d, ρ (c + d) = ρ c + ρ d) : R →+* AddMonoid.End (H.obj V) where
  toFun c := (H.map (ρ c)).hom.toAddMonoidHom
  map_one' := by rw [h1, H.map_id]; rfl
  map_mul' c d := by
    rw [mul_comm, hmul, H.map_comp]
    rfl
  map_zero' := by
    have h0 : ρ 0 = 0 := by simpa using hadd 0 0
    rw [h0, H.map_zero]
    rfl
  map_add' c d := by
    rw [hadd, H.map_add]
    rfl

/-- `CategoryTheory.Functor.endRingHomOfMap` sends `c` to the additive endomorphism `H(ρ c)`. -/
theorem CategoryTheory.Functor.endRingHomOfMap_apply {C : Type*} [Category C] [Preadditive C]
    {Γ : Type*} [Ring Γ] (H : C ⥤ ModuleCat.{v} Γ) [H.Additive] {R : Type*} [CommRing R] (V : C)
    (ρ : R → (V ⟶ V)) (h1 : ρ 1 = 𝟙 V) (hmul : ∀ c d, ρ (c * d) = ρ c ≫ ρ d)
    (hadd : ∀ c d, ρ (c + d) = ρ c + ρ d) (c : R) (x : H.obj V) :
    H.endRingHomOfMap V ρ h1 hmul hadd c x = (H.map (ρ c)).hom x :=
  rfl

/-- Finiteness over a ring transported along a ring equivalence into the scalars. -/
theorem Module.Finite.of_restrictScalars_ringEquiv {R₁ R₂ Γ : Type*} [CommRing R₁] [CommRing R₂]
    [Ring Γ] (g : R₁ →+* Γ) (e : R₂ ≃+* R₁) (M : ModuleCat.{v} Γ)
    [hM : Module.Finite R₁ ((ModuleCat.restrictScalars g).obj M)] :
    @Module.Finite R₂ M _ _ (Module.compHom M (g.comp e.toRingHom)) := by
  let : Module R₂ M := Module.compHom M (g.comp e.toRingHom)
  obtain ⟨s, hs⟩ := hM.fg_top
  refine ⟨⟨s, ?_⟩⟩
  rw [eq_top_iff]
  have key : ∀ y : (ModuleCat.restrictScalars g).obj M,
      y ∈ Submodule.span R₁ (s : Set ((ModuleCat.restrictScalars g).obj M)) →
        (show M from y) ∈
          Submodule.span R₂ (show Set M from (s : Set ((ModuleCat.restrictScalars g).obj M))) := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span hy
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul r y _ hy =>
      have : (show M from r • y) = (e.symm r) • (show M from y) := by
        show g r • (show M from y) = g (e (e.symm r)) • (show M from y)
        rw [RingEquiv.apply_symm_apply]
      rw [this]
      exact Submodule.smul_mem _ _ hy
  intro x _
  exact key x (hs ▸ trivial)

/-- The unit of a composite adjunction read through an isomorphism of right adjoints, followed by
a comparison of left adjoints compatible with the units, is the unit of the other adjunction. -/
theorem CategoryTheory.Adjunction.comp_ofNatIsoRight_unit_app_comp {C D E : Type*} [Category C]
    [Category D] [Category E] {F₁ : C ⥤ D} {G₁ : D ⥤ C} {F₂ : D ⥤ E} {G₂ : E ⥤ D} {H : E ⥤ C}
    {F' : C ⥤ E} (adj₁ : F₁ ⊣ G₁) (adj₂ : F₂ ⊣ G₂) (e : G₂ ⋙ G₁ ≅ H) (adj' : F' ⊣ H)
    (i : F₁ ⋙ F₂ ≅ F')
    (hunit : ((adj₁.comp adj₂).ofNatIsoRight e).unit ≫ Functor.whiskerRight i.hom H = adj'.unit)
    (N : C) :
    (adj₁.unit.app N ≫ G₁.map (adj₂.unit.app (F₁.obj N))) ≫
      (e.hom.app ((F₁ ⋙ F₂).obj N) ≫ H.map (i.hom.app N)) = adj'.unit.app N := by
  have h := congrArg (fun t => NatTrans.app t N) hunit
  simp only [Adjunction.ofNatIsoRight_unit, NatTrans.comp_app, Functor.whiskerLeft_app,
    Functor.whiskerRight_app, Adjunction.comp_unit_app, Category.assoc] at h
  simpa only [Category.assoc] using h

/-- Let `u ≫ β = η`, let `ρc` and `g` be compatible along `β`, let `pb` followed by the
isomorphism `c'` be `H η`, and let `H' g` be multiplication by `b`. Then `H β ∘ H ρc ∘ H u` sends
`y` to `c' (b • pb y)`. -/
theorem ModuleCat.comparison_apply_of_fac {C C' : Type*} [Category C] [Category C'] {Γ Γ' : Type*}
    [CommRing Γ] [CommRing Γ'] (H : C ⥤ ModuleCat.{v} Γ) (H' : C' ⥤ ModuleCat.{v} Γ')
    (φ : Γ →+* Γ') (P : C' ⥤ C) {N V : C} {K : C'} (u : N ⟶ V) (β : V ⟶ P.obj K)
    (η : N ⟶ P.obj K) (ρc : V ⟶ V) (g : K ⟶ K)
    (c' : (ModuleCat.restrictScalars φ).obj (H'.obj K) ≅ H.obj (P.obj K))
    (pb : H.obj N ⟶ (ModuleCat.restrictScalars φ).obj (H'.obj K))
    (hu : u ≫ β = η) (hρ : ρc ≫ β = β ≫ P.map g) (hfac : pb ≫ c'.hom = H.map η)
    (hnat : (ModuleCat.restrictScalars φ).map (H'.map g) ≫ c'.hom = c'.hom ≫ H.map (P.map g))
    (b : Γ') (hg : H'.map g = b • 𝟙 _) (y : H.obj N) :
    (H.map β).hom ((H.map ρc).hom ((H.map u).hom y)) =
      c'.hom.hom (b • (show H'.obj K from pb.hom y)) := by
  have e1 : u ≫ ρc ≫ β = η ≫ P.map g := by rw [hρ, ← Category.assoc, hu]
  have e2 : (H.map β).hom ((H.map ρc).hom ((H.map u).hom y)) =
      (H.map (u ≫ ρc ≫ β)).hom y := by
    simp only [Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]
  have e3 : (b • (show H'.obj K from pb.hom y)) = (H'.map g).hom (pb.hom y) := by
    rw [hg]
    rfl
  rw [e2, e1, e3]
  have e4 := congrArg (fun m => m.hom (pb.hom y)) hnat
  have e5 := congrArg (fun m => m.hom y) hfac
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply] at e4 e5
  rw [show (H'.map g).hom (pb.hom y) = ((ModuleCat.restrictScalars φ).map (H'.map g)).hom
    (pb.hom y) from rfl, e4, e5, Functor.map_comp, ModuleCat.hom_comp, LinearMap.comp_apply]

namespace AlgebraicGeometry.Space

attribute [local instance 5000] SheafOfModules.instAbelian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The cohomology `H^p(Y, −)` of modules on an algebraic space, as a functor to modules over
`Γ(Y, 𝒪_Y)`. -/
abbrev modulesCohomologyFunctor (Y : AlgebraicSpaces B S hS) (p : ℕ) :
    Modules.{u, u} B S hS Y.1 Y.2 ⥤ ModuleCat.{u + 1}
      (RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O).obj) :=
  have := hasInjectiveResolutions_modules B S hS Y.1 Y.2
  (globalSectionsFunctor.{u + 1, u, u, u}
    (ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)).rightDerived p

section Composite

variable {X X₁ X₂ : AlgebraicSpaces B S hS}

/-- The comparison carries the composite of the units to the unit of `ψ ≫ π`. -/
theorem unit_comp_modulePushforwardPullbackComp (ψ : X₂ ⟶ X₁) (π : X₁ ⟶ X)
    (N : Modules.{u, u} B S hS X.1 X.2) :
    ((modulePullbackAdjunction B S hS π).unit.app N ≫ (modulePushforward B S hS π).map
      ((modulePullbackAdjunction B S hS ψ).unit.app ((modulePullback B S hS π).obj N))) ≫
      ((modulePushforwardCompIso B S hS ψ π).hom.app
        ((modulePullback B S hS π ⋙ modulePullback B S hS ψ).obj N) ≫
        (modulePushforward B S hS (ψ ≫ π)).map ((modulePullbackCompIso B S hS ψ π).hom.app N)) =
      (modulePullbackAdjunction B S hS (ψ ≫ π)).unit.app N :=
  CategoryTheory.Adjunction.comp_ofNatIsoRight_unit_app_comp
    (modulePullbackAdjunction B S hS π) (modulePullbackAdjunction B S hS ψ)
    (modulePushforwardCompIso B S hS ψ π) (modulePullbackAdjunction B S hS (ψ ≫ π))
    (modulePullbackCompIso B S hS ψ π)
    (unit_comp_whiskerRight_modulePullbackCompIso_hom B S hS ψ π) N

/-- The comparison commutes with the multiplications by a global function of the source. -/
theorem globalSmul_comp_modulePushforwardPullbackComp (ψ : X₂ ⟶ X₁) (π : X₁ ⟶ X)
    (N : Modules.{u, u} B S hS X.1 X.2)
    (c : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X₂.1 X₂.2).O).obj) :
    (modulePushforward B S hS π).map ((modulePushforward B S hS ψ).map
        (globalSmul _ c ((modulePullback B S hS π ⋙ modulePullback B S hS ψ).obj N))) ≫
      ((modulePushforwardCompIso B S hS ψ π).hom.app
        ((modulePullback B S hS π ⋙ modulePullback B S hS ψ).obj N) ≫
        (modulePushforward B S hS (ψ ≫ π)).map ((modulePullbackCompIso B S hS ψ π).hom.app N)) =
      ((modulePushforwardCompIso B S hS ψ π).hom.app
        ((modulePullback B S hS π ⋙ modulePullback B S hS ψ).obj N) ≫
        (modulePushforward B S hS (ψ ≫ π)).map ((modulePullbackCompIso B S hS ψ π).hom.app N)) ≫
        (modulePushforward B S hS (ψ ≫ π)).map
          (globalSmul _ c ((modulePullback B S hS (ψ ≫ π)).obj N)) := by
  have n1 := (modulePushforwardCompIso B S hS ψ π).hom.naturality
    (globalSmul _ c ((modulePullback B S hS π ⋙ modulePullback B S hS ψ).obj N))
  have n3 := congrArg (modulePushforward B S hS (ψ ≫ π)).map
    (Stacks.Cohomology.SiteModules.comp_globalSmul _ c
      ((modulePullbackCompIso B S hS ψ π).hom.app N)).symm
  rw [CategoryTheory.Functor.map_comp, CategoryTheory.Functor.map_comp] at n3
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) n1).trans
    ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) n3).trans (Category.assoc _ _ _).symm)))

/-- **`π_*ψ_*ψ^*π^*N ≅ π'_*π'^*N` for `π' = ψ ≫ π`**, compatibly with the units and with the
direct images of the multiplications by global functions. -/
theorem exists_isIso_modulePushforward_pullback_of_comp_eq (ψ : X₂ ⟶ X₁) (π : X₁ ⟶ X)
    (π' : X₂ ⟶ X) (h : ψ ≫ π = π') (N : Modules.{u, u} B S hS X.1 X.2) :
    ∃ β : (modulePushforward B S hS π).obj ((modulePushforward B S hS ψ).obj
        ((modulePullback B S hS ψ).obj ((modulePullback B S hS π).obj N))) ⟶
      (modulePushforward B S hS π').obj ((modulePullback B S hS π').obj N), IsIso β ∧
      ((modulePullbackAdjunction B S hS π).unit.app N ≫ (modulePushforward B S hS π).map
        ((modulePullbackAdjunction B S hS ψ).unit.app ((modulePullback B S hS π).obj N))) ≫ β =
        (modulePullbackAdjunction B S hS π').unit.app N ∧
      ∀ c : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X₂.1 X₂.2).O).obj,
        (modulePushforward B S hS π).map ((modulePushforward B S hS ψ).map
          (globalSmul _ c ((modulePullback B S hS ψ).obj ((modulePullback B S hS π).obj N)))) ≫ β =
          β ≫ (modulePushforward B S hS π').map
            (globalSmul _ c ((modulePullback B S hS π').obj N)) := by
  subst h
  exact ⟨_, inferInstance,
    unit_comp_modulePushforwardPullbackComp B S hS ψ π N,
    globalSmul_comp_modulePushforwardPullbackComp B S hS ψ π N⟩

end Composite

variable (T : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj T)]
  {X : AlgebraicSpaces B S hS} (f : X ⟶ schemeSpace T)

/-- **Functions on the base as global functions on `X`**, as a ring map
`A = Γ(T₀, ⊤) ⟶ Γ(X, 𝒪_X)`; its values are `AlgebraicGeometry.Space.baseScalar`. -/
def baseScalarRingHom :
    Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) →+*
      RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj :=
  (globalSectionsRingHomSite B S hS f).comp (schemeSpaceGlobalSectionsEquiv B S hS T).symm.toRingHom

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T)] in
/-- `AlgebraicGeometry.Space.baseScalarRingHom` sends `a` to
`AlgebraicGeometry.Space.baseScalar f a`. -/
theorem baseScalarRingHom_apply (a : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    baseScalarRingHom B S hS T f a = baseScalar f a :=
  (baseScalar_eq_globalSectionsRingHomSite B S hS T f a).symm

section Rees

variable (J : Ideal Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
  [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)]

/-- The action of `A[t]` on `H^p(X, π_*ψ_*ψ^*π^*N)`, through `ρ`. -/
def reesTotalCohomologyAction (N : Modules.{u, u} B S hS X.1 X.2) (p : ℕ) :
    basePolynomialRing B S hS T →+* AddMonoid.End ((modulesCohomologyFunctor B S hS X p).obj
      (algebraImageTotal B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
        (reesAlgebra J).val N)) :=
  (modulesCohomologyFunctor B S hS X p).endRingHomOfMap _
    (fun c => algebraImageScalarEnd B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
      (reesAlgebra J).val N (algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T) c))
    ((congrArg (algebraImageScalarEnd B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
      (reesAlgebra J).val N) (map_one _)).trans
      (algebraImageScalarEnd_one B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
        (reesAlgebra J).val N))
    (fun c d => (congrArg (algebraImageScalarEnd B S hS T f (reesAlgebra J)
      (basePolynomialRing B S hS T) (reesAlgebra J).val N) (map_mul _ c d)).trans
      (algebraImageScalarEnd_mul B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
        (reesAlgebra J).val N _ _))
    (fun c d => (congrArg (algebraImageScalarEnd B S hS T f (reesAlgebra J)
      (basePolynomialRing B S hS T) (reesAlgebra J).val N) (map_add _ c d)).trans
      (algebraImageScalarEnd_add B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
        (reesAlgebra J).val N _ _))

omit [IsNoetherianRing Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] in
/-- `ψ♯ ∘ π♯ = π'♯` on global functions of `X`. -/
theorem globalSectionsRingHomSite_algebraBaseChangeMap_projection (R R' : Type u) [CommRing R]
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R]
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R] [CommRing R']
    [Algebra Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    [Algebra.FiniteType Γ((BigFppfOver.toScheme B S hS).obj T, ⊤) R']
    (φ : R →ₐ[Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)] R')
    (b : RingCat.sectionsSubring (ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O).obj) :
    globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f R R' φ)
        (globalSectionsRingHomSite B S hS (algebraBaseChangeProjection B S hS T f R) b) =
      globalSectionsRingHomSite B S hS (algebraBaseChangeProjection B S hS T f R') b := by
  have h : globalSectionsRingHomSite B S hS
      (algebraBaseChangeMap B S hS T f R R' φ ≫ algebraBaseChangeProjection B S hS T f R) b =
      globalSectionsRingHomSite B S hS (algebraBaseChangeProjection B S hS T f R') b :=
    congrArg (fun k => globalSectionsRingHomSite B S hS k b)
      (algebraBaseChangeMap_projection B S hS T f R R' φ)
  rwa [globalSectionsRingHomSite_comp, RingHom.comp_apply] at h

/-- The constant `C a ∈ A[t]`, as a global function on `X_{A[t]}`, is the pullback along `π` and
then `ψ` of the global function of `X` given by `a`. -/
theorem algebraBaseChangeScalar_polynomial_C (a : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤)) :
    algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T) (Polynomial.C a) =
      globalSectionsRingHomSite B S hS (algebraBaseChangeMap B S hS T f (reesAlgebra J)
          (basePolynomialRing B S hS T) (reesAlgebra J).val)
        (globalSectionsRingHomSite B S hS (algebraBaseChangeProjection B S hS T f (reesAlgebra J))
          (baseScalarRingHom B S hS T f a)) := by
  have e1 := algebraBaseChangeScalar_algebraMap B S hS T f (basePolynomialRing B S hS T) a
  have e2 := globalSectionsRingHomSite_algebraBaseChangeMap_projection B S hS T f
    (reesAlgebra J) (basePolynomialRing B S hS T) (reesAlgebra J).val (baseScalar f a)
  have e3 := baseScalarRingHom_apply B S hS T f a
  exact e1.trans (e2.symm.trans (congrArg (globalSectionsRingHomSite B S hS
    (algebraBaseChangeMap B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
      (reesAlgebra J).val)) (congrArg (globalSectionsRingHomSite B S hS
        (algebraBaseChangeProjection B S hS T f (reesAlgebra J))) e3.symm)))

/-- **The constants act on `H^p(X, π_*ψ_*ψ^*π^*N)` through `Γ(X, 𝒪_X)`.** -/
theorem reesTotalCohomologyAction_C (N : Modules.{u, u} B S hS X.1 X.2) (p : ℕ)
    (a : Γ((BigFppfOver.toScheme B S hS).obj T, ⊤))
    (q : (modulesCohomologyFunctor B S hS X p).obj
      (algebraImageTotal B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
        (reesAlgebra J).val N)) :
    reesTotalCohomologyAction B S hS T f J N p (Polynomial.C a) q =
      baseScalarRingHom B S hS T f a • q := by
  have h1 := algebraImageScalarEnd_globalSectionsRingHomSite_comp B S hS T f (reesAlgebra J)
    (basePolynomialRing B S hS T) (reesAlgebra J).val N (baseScalarRingHom B S hS T f a)
  rw [← algebraBaseChangeScalar_polynomial_C] at h1
  have h2 := rightDerived_globalSections_map_globalSmul B S hS X (baseScalarRingHom B S hS T f a)
    (algebraImageTotal B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
        (reesAlgebra J).val N) p
  show ((modulesCohomologyFunctor B S hS X p).map (algebraImageScalarEnd B S hS T f
    (reesAlgebra J) (basePolynomialRing B S hS T) (reesAlgebra J).val N
    (algebraBaseChangeScalar B S hS T f (basePolynomialRing B S hS T) (Polynomial.C a)))).hom q = _
  rw [h1]
  exact congrArg (fun m => ModuleCat.Hom.hom m q) h2

/-- `π_*ψ_*ψ^*π^*N ≅ π'_*π'^*N` for the Rees algebra `R = A[Jt]`, compatibly with the unit
`AlgebraicGeometry.Space.algebraImageTotalUnit` and the action
`AlgebraicGeometry.Space.algebraImageScalarEnd`. -/
theorem exists_isIso_algebraImageTotal (N : Modules.{u, u} B S hS X.1 X.2) :
    ∃ β : algebraImageTotal B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
        (reesAlgebra J).val N ⟶
      (modulePushforward B S hS (algebraBaseChangeProjection B S hS T f
        (basePolynomialRing B S hS T))).obj ((modulePullback B S hS
          (algebraBaseChangeProjection B S hS T f (basePolynomialRing B S hS T))).obj N),
      IsIso β ∧
      algebraImageTotalUnit B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
          (reesAlgebra J).val N ≫ β =
        (modulePullbackAdjunction B S hS (algebraBaseChangeProjection B S hS T f
          (basePolynomialRing B S hS T))).unit.app N ∧
      ∀ c, algebraImageScalarEnd B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
          (reesAlgebra J).val N c ≫ β = β ≫ (modulePushforward B S hS
            (algebraBaseChangeProjection B S hS T f (basePolynomialRing B S hS T))).map
            (globalSmul _ c ((modulePullback B S hS (algebraBaseChangeProjection B S hS T f
              (basePolynomialRing B S hS T))).obj N)) :=
  exists_isIso_modulePushforward_pullback_of_comp_eq B S hS
    (algebraBaseChangeMap B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
      (reesAlgebra J).val) (algebraBaseChangeProjection B S hS T f (reesAlgebra J))
    (algebraBaseChangeProjection B S hS T f (basePolynomialRing B S hS T))
    (algebraBaseChangeMap_projection B S hS T f (reesAlgebra J) (basePolynomialRing B S hS T)
      (reesAlgebra J).val) N

end Rees

end AlgebraicGeometry.Space

end
