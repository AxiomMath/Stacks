module

public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictedCohomologyDelta
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.FiniteTypeGroupHomology

/-!
# Inflation and restriction as morphisms of δ-functors

Let `R` be a finite ring and `φ : Γ' → Γ` a continuous homomorphism of compact groups, `Γ`
profinite. On the finite `R`-modules with a continuous action of `Γ`, the cohomology
`X ↦ H^•(Γ, X)` (`Stacks.ContinuousCohomology.cohomologyDelta`) is a universal δ-functor, so the
inclusion of invariants `X^Γ ⊆ (res_φ X)^{Γ'}` extends uniquely to a morphism of δ-functors
`H^•(Γ, X) ⟶ H^•(Γ', res_φ X)` (`Stacks.ContinuousCohomology.inflation`). For `φ` surjective this
is inflation, for `φ` an inclusion it is restriction. Uniqueness makes these maps transitive
(`Stacks.ContinuousCohomology.inflation_comp`) and trivial along the identity
(`Stacks.ContinuousCohomology.inflation_id`).

For `G` profinite and an open normal subgroup `U`, the quotient `G ⧸ U` is finite and discrete,
and `quotientMk U : G → G ⧸ U`, `quotientMap h : G ⧸ V → G ⧸ U` are the continuous quotient maps.

## Main definitions

* `Stacks.ContinuousCohomology.cohomologyDelta`: `X ↦ H^•(Γ, X)` on finite modules.
* `Stacks.ContinuousCohomology.inflation`: the morphism of δ-functors along `φ`.
* `Stacks.ContinuousCohomology.quotientMk`, `Stacks.ContinuousCohomology.quotientMap`.

## Main results

* `Stacks.ContinuousCohomology.inflation_comp`, `inflation_comp_self`: transitivity.
* `Stacks.ContinuousCohomology.inflation_id`,
  `Stacks.ContinuousCohomology.inflation_comp_comparison_of_eq_id`: inflation along the
  identity is the identity.
* `Stacks.ContinuousCohomology.bijective_inflation_app_zero`: for `φ` surjective, inflation is
  bijective in degree zero.

## References

* [Stacks Project, Section 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

universe w

namespace Stacks.ContinuousCohomology

section Quotient

variable {G : Type w} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

/-- The quotient by an open normal subgroup is discrete. -/
instance discreteTopology_quotient_openNormalSubgroup (U : OpenNormalSubgroup G) :
    DiscreteTopology (G ⧸ (U : Subgroup G)) :=
  inferInstanceAs (DiscreteTopology (G ⧸ U.toOpenSubgroup.toSubgroup))

/-- The quotient map `G → G ⧸ U` as a continuous homomorphism. -/
def quotientMk (U : OpenNormalSubgroup G) : G →ₜ* G ⧸ (U : Subgroup G) where
  toMonoidHom := QuotientGroup.mk' (U : Subgroup G)
  continuous_toFun := continuous_quot_mk

/-- The map `G ⧸ V → G ⧸ U` for `V ≤ U`. -/
def quotientMap {U V : OpenNormalSubgroup G} (h : V ≤ U) :
    G ⧸ (V : Subgroup G) →ₜ* G ⧸ (U : Subgroup G) where
  toMonoidHom := QuotientGroup.map (V : Subgroup G) (U : Subgroup G) (MonoidHom.id G) h
  continuous_toFun := continuous_of_discreteTopology

variable [CompactSpace G]

/-- The quotient by an open normal subgroup is compact. -/
instance (U : OpenNormalSubgroup G) : CompactSpace (G ⧸ (U : Subgroup G)) :=
  Quotient.compactSpace

/-- The quotient by an open normal subgroup of a compact group is finite. -/
instance (U : OpenNormalSubgroup G) : Finite (G ⧸ (U : Subgroup G)) :=
  finite_of_compact_of_discrete

end Quotient

section Conj

variable {C₁ C₂ C₃ D : Type*} [Category C₁] [Category C₂] [Category C₃] [Category D]

/-- Composing two morphisms conjugated by isomorphisms: the middle isomorphism cancels. -/
lemma conj_comp_conj (Φ : C₁ ⥤ C₂) (Ψ : C₂ ⥤ C₃) (Θ : C₁ ⥤ C₃) (β : Φ ⋙ Ψ ⟶ Θ)
    {F₁ G₁ : C₁ ⥤ D} {F₂ G₂ : C₂ ⥤ D} {F₃ G₃ : C₃ ⥤ D} (e₁ : F₁ ≅ G₁) (e₂ : F₂ ≅ G₂)
    (e₃ : F₃ ≅ G₃) (a : G₁ ⟶ Φ ⋙ G₂) (b : G₂ ⟶ Ψ ⋙ G₃) (c : G₁ ⟶ Θ ⋙ G₃)
    (h : a ≫ Functor.whiskerLeft Φ b ≫ Functor.whiskerRight β G₃ = c) :
    (e₁.hom ≫ a ≫ Functor.whiskerLeft Φ e₂.inv) ≫
        Functor.whiskerLeft Φ (e₂.hom ≫ b ≫ Functor.whiskerLeft Ψ e₃.inv) ≫
          Functor.whiskerRight β F₃ =
      e₁.hom ≫ c ≫ Functor.whiskerLeft Θ e₃.inv := by
  subst h
  ext X
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.whiskerRight_app,
    Category.assoc, Iso.inv_hom_id_app_assoc, NatTrans.naturality]
  rfl

end Conj

/-- Enough injectives for continuous discrete modules at the module universe of the group,
pinned. -/
local instance (priority := 3000) enoughInjectives_continuousModule_inflation (Λ : Type)
    [Ring Λ] (G : Type w) [Group G] [TopologicalSpace G] [IsTopologicalGroup G] :
    EnoughInjectives (Stacks.Injectives.ContinuousModule.{0, w, w} Λ G) :=
  Stacks.ContinuousCohomology.enoughInjectives.{0, w, 0} Λ G

section Inflation

variable (R : Type) [Ring R] [Finite R]
  {Γ Γ' : Type w} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ] [CompactSpace Γ]
  [Group Γ'] [TopologicalSpace Γ'] [IsTopologicalGroup Γ'] [CompactSpace Γ']

/-- Restriction along `φ` preserves finite limits (instance form). -/
local instance (φ : Γ' →ₜ* Γ) :
    PreservesFiniteLimits (finiteTypeContinuousModuleRes.{0, w, w} R φ) :=
  Stacks.GroupHomology.preservesFiniteLimits_finiteTypeContinuousModuleRes φ

/-- Restriction along `φ` preserves finite colimits (instance form). -/
local instance (φ : Γ' →ₜ* Γ) :
    PreservesFiniteColimits (finiteTypeContinuousModuleRes.{0, w, w} R φ) :=
  Stacks.GroupHomology.preservesFiniteColimits_finiteTypeContinuousModuleRes φ

/-- The cohomology `H^•(Γ, -)` on finite modules with continuous `Γ`-action. -/
abbrev cohomologyDelta (Γ : Type w) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] :
    DeltaFunctor (FiniteTypeContinuousModule.{0, w, w} R Γ) (ModuleCat.{w} R) :=
  restrictedCohomologyDelta R (ContinuousMonoidHom.id Γ)

/-- The target of inflation: `X ↦ H^•(Γ', res_φ X)`. -/
abbrev inflationTarget (φ : Γ' →ₜ* Γ) :
    DeltaFunctor (FiniteTypeContinuousModule.{0, w, w} R Γ) (ModuleCat.{w} R) :=
  (cohomologyDelta R Γ').precomp (finiteTypeContinuousModuleRes.{0, w, w} R φ)

/-- `H⁰(Γ, -)` is the invariants. -/
def cohomologyDeltaZeroIso (Γ : Type w) [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
    [CompactSpace Γ] :
    (cohomologyDelta R Γ).functor 0 ≅
      finiteTypeContinuousModuleToRes R (ContinuousMonoidHom.id Γ) ⋙
        continuousModuleRingInvariants.{0, w, w} R Γ :=
  Functor.isoWhiskerLeft _
    (eqToIso (rfl : (invariantsDelta.{0, w, w} R (G := Γ)).functor 0 =
        (continuousModuleRingInvariants.{0, w, w} R Γ).rightDerived 0) ≪≫
      (continuousModuleRingInvariants.{0, w, w} R Γ).rightDerivedZeroIsoSelf)

/-- The inclusion `X^Γ ⊆ (res_φ X)^{Γ'}` of invariants. -/
def invariantsInclusion (φ : Γ' →ₜ* Γ) :
    finiteTypeContinuousModuleToRes R (ContinuousMonoidHom.id Γ) ⋙
        continuousModuleRingInvariants.{0, w, w} R Γ ⟶
      finiteTypeContinuousModuleRes.{0, w, w} R φ ⋙
        finiteTypeContinuousModuleToRes R (ContinuousMonoidHom.id Γ') ⋙
          continuousModuleRingInvariants.{0, w, w} R Γ' where
  app _ := ModuleCat.ofHom
    { toFun := fun x ↦ ⟨x.1, fun g ↦ x.2 (φ g)⟩
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }
  naturality _ _ _ := rfl

/-- The degree-zero part of inflation. -/
def inflationZero (φ : Γ' →ₜ* Γ) :
    (cohomologyDelta R Γ).functor 0 ⟶ (inflationTarget R φ).functor 0 :=
  (cohomologyDeltaZeroIso R Γ).hom ≫ invariantsInclusion R φ ≫
    Functor.whiskerLeft (finiteTypeContinuousModuleRes.{0, w, w} R φ)
      (cohomologyDeltaZeroIso R Γ').inv

variable [TotallyDisconnectedSpace Γ]

/-- `H^•(Γ, -)` is universal. -/
instance isUniversal_cohomologyDelta : (cohomologyDelta R Γ).IsUniversal :=
  isUniversal_restrictedCohomologyDelta R _ Topology.IsInducing.id

/-- **Inflation** `H^•(Γ, X) ⟶ H^•(Γ', res_φ X)`: the morphism of δ-functors extending the
inclusion of invariants. -/
def inflation (φ : Γ' →ₜ* Γ) : cohomologyDelta R Γ ⟶ inflationTarget R φ :=
  DeltaFunctor.IsUniversal.lift _ (inflationZero R φ)

variable {Γ'' : Type w} [Group Γ''] [TopologicalSpace Γ''] [IsTopologicalGroup Γ'']
  [CompactSpace Γ'']

/-- The identity of underlying modules, as a natural transformation `res_{φ ∘ ψ} ⟶ res_χ` when
`φ ∘ ψ = χ` pointwise. -/
def resComparison (φ : Γ' →ₜ* Γ) (ψ : Γ'' →ₜ* Γ') (χ : Γ'' →ₜ* Γ) (h : ∀ g, φ (ψ g) = χ g) :
    finiteTypeContinuousModuleRes.{0, w, w} R (φ.comp ψ) ⟶
      finiteTypeContinuousModuleRes.{0, w, w} R χ where
  app X := ObjectProperty.homMk ((Stacks.GroupCohomology.homEquiv R Γ'' _ _).symm
    ⟨LinearMap.id, fun g x ↦ by
      change (X.obj.obj.obj.ρ (φ (ψ g))).asHom.hom x = (X.obj.obj.obj.ρ (χ g)).asHom.hom x
      rw [h]⟩)
  naturality _ _ _ := rfl

/-- The morphism `H^•(Γ'', res_{φ ∘ ψ} -) ⟶ H^•(Γ'', res_χ -)` induced by `res_{φ ∘ ψ} = res_χ`. -/
def inflationTargetComparison (φ : Γ' →ₜ* Γ) (ψ : Γ'' →ₜ* Γ') (χ : Γ'' →ₜ* Γ)
    (h : ∀ g, φ (ψ g) = χ g) :
    inflationTarget R (φ.comp ψ) ⟶ inflationTarget R χ :=
  (cohomologyDelta R Γ'').precompNatTrans (resComparison R φ ψ χ h)

/-- Inflation along `ψ`, precomposed with restriction along `φ`. -/
def inflationPrecomp [TotallyDisconnectedSpace Γ'] (φ : Γ' →ₜ* Γ) (ψ : Γ'' →ₜ* Γ') :
    inflationTarget R φ ⟶ inflationTarget R (φ.comp ψ) :=
  DeltaFunctor.precompHom (finiteTypeContinuousModuleRes.{0, w, w} R φ) (inflation R ψ)

/-- **Inflation is transitive**: inflating along `φ` and then along `ψ` is inflating along
`χ = φ ∘ ψ`. -/
theorem inflation_comp [TotallyDisconnectedSpace Γ'] (φ : Γ' →ₜ* Γ) (ψ : Γ'' →ₜ* Γ')
    (χ : Γ'' →ₜ* Γ) (h : ∀ g, φ (ψ g) = χ g) :
    inflation R φ ≫ inflationPrecomp R φ ψ ≫ inflationTargetComparison R φ ψ χ h =
      inflation R χ := by
  apply DeltaFunctor.IsUniversal.hom_ext_zero
  change (inflation R φ).app 0 ≫ (inflationPrecomp R φ ψ).app 0 ≫
    (inflationTargetComparison R φ ψ χ h).app 0 = (inflation R χ).app 0
  simp only [inflationPrecomp, inflationTargetComparison,
    DeltaFunctor.precompHom_app, DeltaFunctor.precompNatTrans_app, inflation,
    DeltaFunctor.IsUniversal.lift_app_zero]
  exact conj_comp_conj _ _ _ _ _ _ _ _ _ _ (NatTrans.ext (funext fun X ↦ rfl))

omit [Finite R] [IsTopologicalGroup Γ] [CompactSpace Γ] [IsTopologicalGroup Γ'] [CompactSpace Γ']
  [TotallyDisconnectedSpace Γ] [IsTopologicalGroup Γ''] [CompactSpace Γ''] in
/-- `res_{φ ∘ ψ} ⟶ res_{φ ∘ ψ}` is the identity. -/
theorem resComparison_self (φ : Γ' →ₜ* Γ) (ψ : Γ'' →ₜ* Γ') :
    resComparison R φ ψ (φ.comp ψ) (fun _ ↦ rfl) = 𝟙 _ := by
  ext X : 2
  apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext; apply ObjectProperty.hom_ext
  apply Action.hom_ext; apply ModuleCat.hom_ext; rfl

/-- **Inflation is transitive**, the case `χ = φ ∘ ψ`. -/
theorem inflation_comp_self [TotallyDisconnectedSpace Γ'] (φ : Γ' →ₜ* Γ) (ψ : Γ'' →ₜ* Γ') :
    inflation R φ ≫ inflationPrecomp R φ ψ = inflation R (φ.comp ψ) := by
  have h := inflation_comp R φ ψ (φ.comp ψ) (fun _ ↦ rfl)
  have h1 : inflationTargetComparison R φ ψ (φ.comp ψ) (fun _ ↦ rfl) = 𝟙 _ := by
    apply DeltaFunctor.hom_ext
    intro n
    change Functor.whiskerRight (resComparison R φ ψ (φ.comp ψ) (fun _ ↦ rfl)) _ = 𝟙 _
    rw [resComparison_self, Functor.whiskerRight_id']
  rwa [h1, Category.comp_id] at h

omit [Finite R] [IsTopologicalGroup Γ] [CompactSpace Γ] [IsTopologicalGroup Γ']
  [CompactSpace Γ'] [TotallyDisconnectedSpace Γ] in
/-- For `φ` surjective the inclusion of invariants is bijective. -/
theorem bijective_invariantsInclusion_app (φ : Γ' →ₜ* Γ) (hφ : Function.Surjective φ)
    (X : FiniteTypeContinuousModule.{0, w, w} R Γ) :
    Function.Bijective ((invariantsInclusion R φ).app X) := by
  refine ⟨fun x y hxy ↦ ?_, fun y ↦ ⟨⟨y.1, fun g ↦ ?_⟩, rfl⟩⟩
  · have h := congrArg Subtype.val hxy
    exact Subtype.ext h
  obtain ⟨g', rfl⟩ := hφ g
  exact y.2 g'

omit [TotallyDisconnectedSpace Γ] in
/-- For `φ` surjective, inflation is bijective in degree zero. -/
theorem bijective_inflationZero_app (φ : Γ' →ₜ* Γ) (hφ : Function.Surjective φ)
    (X : FiniteTypeContinuousModule.{0, w, w} R Γ) :
    Function.Bijective ((inflationZero R φ).app X) := by
  have h1 := ((cohomologyDeltaZeroIso R Γ).app X).toLinearEquiv.bijective
  have h3 := ((cohomologyDeltaZeroIso R Γ').app
    ((finiteTypeContinuousModuleRes R φ).obj X)).symm.toLinearEquiv.bijective
  change Function.Bijective (fun x ↦ ((cohomologyDeltaZeroIso R Γ').inv.app _)
    ((invariantsInclusion R φ).app X ((cohomologyDeltaZeroIso R Γ).hom.app X x)))
  exact h3.comp ((bijective_invariantsInclusion_app R φ hφ X).comp h1)

/-- For `φ` surjective, inflation is bijective in degree zero. -/
theorem bijective_inflation_app_zero (φ : Γ' →ₜ* Γ) (hφ : Function.Surjective φ)
    (X : FiniteTypeContinuousModule.{0, w, w} R Γ) :
    Function.Bijective (((inflation R φ).app 0).app X) := by
  rw [inflation, DeltaFunctor.IsUniversal.lift_app_zero]
  exact bijective_inflationZero_app R φ hφ X

/-- **Inflation along the identity is the identity.** -/
theorem inflation_id : inflation R (ContinuousMonoidHom.id Γ) = 𝟙 (cohomologyDelta R Γ) := by
  apply DeltaFunctor.IsUniversal.hom_ext_zero
  rw [inflation, DeltaFunctor.IsUniversal.lift_app_zero]
  change inflationZero R (ContinuousMonoidHom.id Γ) = 𝟙 _
  rw [inflationZero]
  exact (Iso.hom_inv_id (cohomologyDeltaZeroIso R Γ))

/-- **Inflation along a homomorphism which is the identity pointwise** is the identity, up to the
identification of the restriction with the original module. -/
theorem inflation_comp_comparison_of_eq_id (φ : Γ →ₜ* Γ) (h : ∀ g, φ g = g) :
    inflation R φ ≫ inflationTargetComparison R φ (ContinuousMonoidHom.id Γ)
      (ContinuousMonoidHom.id Γ) h = 𝟙 (cohomologyDelta R Γ) := by
  have h₁ := inflation_comp R φ (ContinuousMonoidHom.id Γ) (ContinuousMonoidHom.id Γ) h
  have h₂ : inflationPrecomp R φ (ContinuousMonoidHom.id Γ) = 𝟙 _ := by
    rw [inflationPrecomp, inflation_id]
    rfl
  refine Eq.trans ?_ (h₁.trans (inflation_id R))
  rw [h₂]
  exact congrArg (inflation R φ ≫ ·) (Category.id_comp _).symm

end Inflation

end Stacks.ContinuousCohomology

end
