module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapResolution
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.RingCohomologyMapNaturality

/-!
# Flat base change of the action on the cohomology of a derived base change

Let `R → A`, `R → R'` be ring maps and `A → A₁` a flat ring map. For `K ∈ D(A)` the
`A`-module `Hⁿ(K|_R ⊗ᴸ_R R')` and the `A₁`-module `Hⁿ((K ⊗ᴸ_A A₁)|_R ⊗ᴸ_R R')`, the actions
coming from scalar multiplication on `K` and on `K ⊗ᴸ_A A₁`, are related by base change: the map
induced by the unit `K → (K ⊗ᴸ_A A₁)|_A` exhibits the second as `A₁ ⊗_A` the first.

## Main definitions

* `RingTheory.TorIndependence.IsBaseChangeOfActions`: a linear map `θ : M → N` of `R`-modules
  together with actions of `A` on `M` and of `A₁` on `N` is a base change along `A → A₁`.
* `RingTheory.TorIndependence.functorAction`: the action of `A` on the values of a functor out of
  an `A`-linear category.

## Main results

* `RingTheory.TorIndependence.isBaseChangeOfActions_derivedUnit`: the base-change statement above.

## References

* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open scoped TensorProduct

universe u

namespace RingTheory.TorIndependence

/-! ### Base change for modules given by actions -/

section Actions

variable {A A₁ : Type*} [CommRing A] [CommRing A₁] [Algebra A A₁]
  {M N M' N' : Type*} [AddCommGroup M] [AddCommGroup N] [AddCommGroup M'] [AddCommGroup N']

/-- **Base change for modules given by actions.** For an action `α` of `A` on `M` and an action
`β` of `A₁` on `N` by additive endomorphisms, the additive map `θ : M → N` is semilinear along
`A → A₁` and exhibits `N` as the base change `A₁ ⊗_A M`. -/
def IsBaseChangeOfActions (α : A →+* AddMonoid.End M) (β : A₁ →+* AddMonoid.End N)
    (θ : M →+ N) : Prop :=
  letI : Module A M := Module.compHom M α
  letI : Module A₁ N := Module.compHom N β
  letI : Module A N := Module.compHom N (algebraMap A A₁)
  haveI : IsScalarTower A A₁ N := IsScalarTower.of_compHom _ _ _
  ∃ h : ∀ (x : A) (m : M), θ (α x m) = β (algebraMap A A₁ x) (θ m),
    IsBaseChange A₁ ({ toFun := θ, map_add' := θ.map_add, map_smul' := h } : M →ₗ[A] N)

/-- `IsBaseChangeOfActions` is invariant under isomorphisms compatible with the actions. -/
theorem IsBaseChangeOfActions.of_equiv {α : A →+* AddMonoid.End M} {β : A₁ →+* AddMonoid.End N}
    {θ : M →+ N} {α' : A →+* AddMonoid.End M'} {β' : A₁ →+* AddMonoid.End N'}
    {θ' : M' →+ N'} (eM : M ≃+ M') (eN : N ≃+ N')
    (hα : ∀ x m, eM (α x m) = α' x (eM m)) (hβ : ∀ y n, eN (β y n) = β' y (eN n))
    (hθ : ∀ m, eN (θ m) = θ' (eM m)) (h : IsBaseChangeOfActions α β θ) :
    IsBaseChangeOfActions α' β' θ' := by
  obtain ⟨h₀, hb⟩ := h
  letI : Module A M := Module.compHom M α
  letI : Module A₁ N := Module.compHom N β
  letI : Module A N := Module.compHom N (algebraMap A A₁)
  haveI : IsScalarTower A A₁ N := IsScalarTower.of_compHom _ _ _
  letI : Module A M' := Module.compHom M' α'
  letI : Module A₁ N' := Module.compHom N' β'
  letI : Module A N' := Module.compHom N' (algebraMap A A₁)
  haveI : IsScalarTower A A₁ N' := IsScalarTower.of_compHom _ _ _
  have h₁ : ∀ (x : A) (m : M'), θ' (α' x m) = β' (algebraMap A A₁ x) (θ' m) := by
    intro x m'
    obtain ⟨m, rfl⟩ := eM.surjective m'
    rw [← hα, ← hθ, h₀, hβ, hθ]
  refine ⟨h₁, ?_⟩
  let eMA : M ≃ₗ[A] M' := { eM with map_smul' := hα }
  let eNA : N ≃ₗ[A₁] N' := { eN with map_smul' := hβ }
  exact (IsBaseChange.iff_of_equiv_comm eMA eNA (LinearMap.ext fun m => (hθ m).symm)).mp hb

/-- `IsBaseChangeOfActions` is invariant under isomorphisms compatible with the actions. -/
theorem IsBaseChangeOfActions.iff_of_equiv {α : A →+* AddMonoid.End M}
    {β : A₁ →+* AddMonoid.End N}
    {θ : M →+ N} {α' : A →+* AddMonoid.End M'} {β' : A₁ →+* AddMonoid.End N'}
    {θ' : M' →+ N'} (eM : M ≃+ M') (eN : N ≃+ N')
    (hα : ∀ x m, eM (α x m) = α' x (eM m)) (hβ : ∀ y n, eN (β y n) = β' y (eN n))
    (hθ : ∀ m, eN (θ m) = θ' (eM m)) :
    IsBaseChangeOfActions α β θ ↔ IsBaseChangeOfActions α' β' θ' := by
  refine ⟨IsBaseChangeOfActions.of_equiv eM eN hα hβ hθ,
    IsBaseChangeOfActions.of_equiv eM.symm eN.symm (fun x m => ?_) (fun y n => ?_) fun m => ?_⟩
  · obtain ⟨m, rfl⟩ := eM.surjective m
    rw [← hα, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  · obtain ⟨n, rfl⟩ := eN.surjective n
    rw [← hβ, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]
  · obtain ⟨m, rfl⟩ := eM.surjective m
    rw [← hθ, AddEquiv.symm_apply_apply, AddEquiv.symm_apply_apply]

/-- Base change for actions agreeing with honest module structures is honest base change. -/
private theorem isBaseChangeOfActions_iff_isBaseChange [instM : Module A M]
    [instN₁ : Module A₁ N] [instN : Module A N] [instT : IsScalarTower A A₁ N]
    {α : A →+* AddMonoid.End M} {β : A₁ →+* AddMonoid.End N} {θ : M →+ N}
    (hα : ∀ x m, α x m = x • m) (hβ : ∀ y n, β y n = y • n) (θl : M →ₗ[A] N)
    (hθ : ∀ m, θ m = θl m) : IsBaseChangeOfActions α β θ ↔ IsBaseChange A₁ θl := by
  have e1 : Module.compHom M α = instM := Module.ext' _ _ fun x m => hα x m
  have e2 : Module.compHom N β = instN₁ := Module.ext' _ _ fun y n => hβ y n
  subst e1 e2
  letI : Module A M := Module.compHom M α
  letI : Module A₁ N := Module.compHom N β
  have e3 : (Module.compHom N (algebraMap A A₁) : Module A N) = instN :=
    Module.ext' _ _ fun x n => (algebraMap_smul A₁ x n)
  subst e3
  letI : Module A N := Module.compHom N (algebraMap A A₁)
  have hθ' : ∀ (x : A) (m : M), θ (α x m) = β (algebraMap A A₁ x) (θ m) := by
    intro x m
    rw [hα, hθ, hθ, θl.map_smul, hβ, algebraMap_smul]
  have hl : θl = { toFun := θ, map_add' := θ.map_add, map_smul' := hθ' } :=
    LinearMap.ext fun m => (hθ m).symm
  rw [hl]
  exact ⟨fun ⟨_, hb⟩ => hb, fun hb => ⟨hθ', hb⟩⟩

/-- Base change for honest module structures, read through actions agreeing with them. -/
theorem isBaseChangeOfActions_of_isBaseChange [instM : Module A M] [instN₁ : Module A₁ N]
    [instN : Module A N] [instT : IsScalarTower A A₁ N] {α : A →+* AddMonoid.End M}
    {β : A₁ →+* AddMonoid.End N} {θ : M →+ N} (hα : ∀ x m, α x m = x • m)
    (hβ : ∀ y n, β y n = y • n) (θl : M →ₗ[A] N) (hθ : ∀ m, θ m = θl m)
    (h : IsBaseChange A₁ θl) : IsBaseChangeOfActions α β θ :=
  (isBaseChangeOfActions_iff_isBaseChange hα hβ θl hθ).2 h

/-- Base change for actions agreeing with honest module structures is honest base change. -/
theorem IsBaseChangeOfActions.isBaseChange [instM : Module A M] [instN₁ : Module A₁ N]
    [instN : Module A N] [instT : IsScalarTower A A₁ N] {α : A →+* AddMonoid.End M}
    {β : A₁ →+* AddMonoid.End N} {θ : M →+ N} (hα : ∀ x m, α x m = x • m)
    (hβ : ∀ y n, β y n = y • n) (θl : M →ₗ[A] N) (hθ : ∀ m, θ m = θl m)
    (h : IsBaseChangeOfActions α β θ) : IsBaseChange A₁ θl :=
  (isBaseChangeOfActions_iff_isBaseChange hα hβ θl hθ).1 h

end Actions

/-! ### The action of the scalars on the values of a functor -/

section FunctorAction

variable {A R : Type*} [CommRing A] [CommRing R] {𝒞 : Type*} [Category 𝒞] [Preadditive 𝒞]
  [Linear A 𝒞]

/-- **The action of `A` on the values of an additive functor.** An element `a` acts on `G(X)` by
`G` of multiplication by `a` on `X`. -/
def functorAction (G : 𝒞 ⥤ ModuleCat.{u} R) [G.Additive] (X : 𝒞) :
    A →+* AddMonoid.End (G.obj X) where
  toFun a := (G.map (a • 𝟙 X)).hom.toAddMonoidHom
  map_one' := by
    rw [one_smul, G.map_id]
    rfl
  map_mul' a b := by
    have hab : (a * b) • (𝟙 X) = (b • (𝟙 X)) ≫ (a • (𝟙 X)) := by
      simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, smul_smul]
    rw [hab, G.map_comp]
    rfl
  map_zero' := by
    rw [zero_smul, G.map_zero]
    rfl
  map_add' a b := by
    rw [add_smul, G.map_add]
    rfl

theorem functorAction_apply (G : 𝒞 ⥤ ModuleCat.{u} R) [G.Additive] (X : 𝒞) (a : A)
    (m : G.obj X) : functorAction G X a m = (G.map (a • 𝟙 X)).hom m :=
  rfl

/-- `G` of a morphism commutes with the actions. -/
theorem functorAction_map (G : 𝒞 ⥤ ModuleCat.{u} R) [G.Additive] {X Y : 𝒞} (φ : X ⟶ Y) (a : A)
    (m : G.obj X) :
    (G.map φ).hom (functorAction G X a m) = functorAction G Y a ((G.map φ).hom m) := by
  have h : (a • 𝟙 X) ≫ φ = φ ≫ (a • 𝟙 Y) := by
    simp only [Linear.smul_comp, Linear.comp_smul, Category.id_comp, Category.comp_id]
  have h' := congrArg (fun t => (G.map t).hom m) h
  simp only [G.map_comp] at h'
  exact h'

/-- A natural transformation commutes with the actions. -/
theorem functorAction_natTrans {G G' : 𝒞 ⥤ ModuleCat.{u} R} [G.Additive] [G'.Additive]
    (τ : G ⟶ G') (X : 𝒞) (a : A) (m : G.obj X) :
    (τ.app X).hom (functorAction G X a m) = functorAction G' X a ((τ.app X).hom m) :=
  congrArg (fun t => t.hom m) (τ.naturality (a • 𝟙 X))

variable {A₁ : Type*} [CommRing A₁] [Algebra A A₁] {𝒞₁ : Type*} [Category 𝒞₁] [Preadditive 𝒞₁]
  [Linear A₁ 𝒞₁]

/-- **Transport along natural transformations.** If `σ : S ⟶ S'` and `τ : T ⟶ T'` are invertible
at `X` and `Z`, base change for `θ : S X ⟶ T Z` and for `θ' : S' X ⟶ T' Z` are equivalent as soon
as the square commutes. -/
theorem isBaseChangeOfActions_iff_of_natTrans {S S' : 𝒞 ⥤ ModuleCat.{u} R} [S.Additive]
    [S'.Additive] {T T' : 𝒞₁ ⥤ ModuleCat.{u} R} [T.Additive] [T'.Additive]
    (σ : S ⟶ S') (τ : T ⟶ T') {X : 𝒞} {Z : 𝒞₁} [IsIso (σ.app X)] [IsIso (τ.app Z)]
    (θ : S.obj X ⟶ T.obj Z) (θ' : S'.obj X ⟶ T'.obj Z) (h : θ ≫ τ.app Z = σ.app X ≫ θ') :
    IsBaseChangeOfActions (functorAction (A := A) S X) (functorAction (A := A₁) T Z)
        θ.hom.toAddMonoidHom ↔
      IsBaseChangeOfActions (functorAction (A := A) S' X) (functorAction (A := A₁) T' Z)
        θ'.hom.toAddMonoidHom :=
  IsBaseChangeOfActions.iff_of_equiv (asIso (σ.app X)).toLinearEquiv.toAddEquiv
    (asIso (τ.app Z)).toLinearEquiv.toAddEquiv
    (fun x m => functorAction_natTrans σ X x m)
    (fun y n => functorAction_natTrans τ Z y n)
    (fun m => congrArg (fun t => t.hom m) h)

/-- **Transport along isomorphisms of the objects.** -/
theorem isBaseChangeOfActions_iff_of_iso (S : 𝒞 ⥤ ModuleCat.{u} R) [S.Additive]
    (T : 𝒞₁ ⥤ ModuleCat.{u} R) [T.Additive] {X X' : 𝒞} {Z Z' : 𝒞₁} (e : X ≅ X') (e' : Z ≅ Z')
    (θ : S.obj X ⟶ T.obj Z) (θ' : S.obj X' ⟶ T.obj Z') (h : θ ≫ T.map e'.hom = S.map e.hom ≫ θ') :
    IsBaseChangeOfActions (functorAction (A := A) S X) (functorAction (A := A₁) T Z)
        θ.hom.toAddMonoidHom ↔
      IsBaseChangeOfActions (functorAction (A := A) S X') (functorAction (A := A₁) T Z')
        θ'.hom.toAddMonoidHom :=
  IsBaseChangeOfActions.iff_of_equiv (S.mapIso e).toLinearEquiv.toAddEquiv
    (T.mapIso e').toLinearEquiv.toAddEquiv
    (fun x m => functorAction_map S e.hom x m)
    (fun y n => functorAction_map T e'.hom y n)
    (fun m => congrArg (fun t => t.hom m) h)

/-- The action through a linear functor is the action on its values. -/
theorem functorAction_comp {𝒟 : Type*} [Category 𝒟] [Preadditive 𝒟] [Linear A 𝒟]
    (L : 𝒞 ⥤ 𝒟) [L.Additive] [L.Linear A] (S : 𝒟 ⥤ ModuleCat.{u} R) [S.Additive] (X : 𝒞) :
    functorAction (A := A) (L ⋙ S) X = functorAction (A := A) S (L.obj X) := by
  refine RingHom.ext fun x => ?_
  change (S.map (L.map (x • 𝟙 X))).hom.toAddMonoidHom = (S.map (x • 𝟙 (L.obj X))).hom.toAddMonoidHom
  rw [Functor.map_smul, L.map_id]

end FunctorAction

end RingTheory.TorIndependence

end
