module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.GroupHomology.DerivedCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.FiniteTypeContinuousModuleCoinvariants
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FundamentalGroupLocallyConstant.ModuleBaseChange
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.LeftDerived
public import StacksFrontier.CategoryTheory.Abelian.DeltaFunctor.HomologicalPrecompose
public import StacksFrontier.AlgebraicGeometry.ContinuousCohomology.RestrictedCohomologyDelta

/-!
# Group homology of finite modules with continuous action

Let `Λ` be a ring and `G` a topological group. A finite `Λ`-module `M` with a continuous action of
`G` is acted on through a finite discrete quotient, hence is a module over the completed group
algebra `Λ[[G]]`. Following [Stacks, Tag 03VI], "Notes on Homology": for `Λ`-modules over a finite
ring `Λ`, `H_i(G, M) = Tor_i^{Λ[[G]]}(M, Λ)`, the left derived functors of the coinvariants
`M ↦ M_G = Λ ⊗_{Λ[[G]]} M`. These form a homological δ-functor on the finite `Λ`-modules with
continuous `Γ`-action, restricted along a continuous homomorphism `φ : G →ₜ* Γ`; this is the
functor `(M, ρ) ↦ H_i(π₁(X_{k̄}), M)` of [Stacks, Tag 03VI].

All names are in the namespace `Stacks.GroupHomology`.

## Main definitions

* `finiteTypeCompletedModule`: a finite `Λ`-module with continuous `G`-action as a `Λ[[G]]`-module;
  as a functor it is exact.
* `finiteTypeGroupHomology`: the homological δ-functor `M ↦ Tor_i^{Λ[[G]]}(res_φ M, Λ)`.

## Implementation notes

The completed group algebra and its coinvariants functor are `CompletedGroupAlgebra` and
`coinvariantsFunctor`, which take the ring and the group in one universe; the coefficients are
therefore lifted to `ULift Λ`, which changes nothing about the modules.

## References

* [Stacks Project, Tag 03VI](https://stacks.math.columbia.edu/tag/03VI)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.GroupCohomology

universe v

namespace Stacks.GroupHomology

open CompletedGroupAlgebra

variable (Λ : Type) [Ring Λ] (G : Type v) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]

section Action

variable {Λ G}

/-- The action of `G` on a finite module with continuous action, by additive endomorphisms. -/
def finiteTypeAddAction (N : FiniteTypeContinuousModule.{0, v, v} Λ G) :
    G →* AddMonoid.End N.obj.obj.obj.V where
  toFun g := (finiteTypeContinuousModuleRepresentation Λ G N g).toAddMonoidHom
  map_one' := by ext x; simp; rfl
  map_mul' g h := by ext x; simp; rfl

/-- `G` acting on a finite module with continuous action. -/
@[instance_reducible]
def finiteTypeDistribMulAction (N : FiniteTypeContinuousModule.{0, v, v} Λ G) :
    DistribMulAction G N.obj.obj.obj.V :=
  DistribMulAction.compHom _ (finiteTypeAddAction N)

attribute [local instance] finiteTypeDistribMulAction

omit [IsTopologicalGroup G] in
/-- An element `g` acts on `N` through the representation of `N`. -/
theorem finiteTypeSmul_def (N : FiniteTypeContinuousModule.{0, v, v} Λ G) (g : G)
    (x : N.obj.obj.obj.V) : g • x = finiteTypeContinuousModuleRepresentation Λ G N g x := rfl

omit [IsTopologicalGroup G] in
/-- The action of `G` commutes with the scalars. -/
theorem finiteTypeSMulCommClass (N : FiniteTypeContinuousModule.{0, v, v} Λ G) :
    SMulCommClass G (ULift.{v} Λ) N.obj.obj.obj.V where
  smul_comm g a x := (finiteTypeContinuousModuleRepresentation Λ G N g).map_smul a.down x

attribute [local instance] finiteTypeSMulCommClass

/-- A finite module with continuous action is acted on trivially by an open normal subgroup. -/
theorem exists_openNormalSubgroup_smul_eq_finiteType
    (N : FiniteTypeContinuousModule.{0, v, v} Λ G) :
    ∃ U : OpenNormalSubgroup G, ∀ g ∈ U, ∀ x : N.obj.obj.obj.V, g • x = x := by
  obtain ⟨H, hn, ho, hH⟩ := exists_isOpen_normal_subgroup_ρ_eq_one_finiteType Λ G N
  refine ⟨⟨⟨H, ho⟩, hn⟩, fun g hg x => ?_⟩
  show (N.obj.obj.obj.ρ g).asHom.hom x = x
  rw [hH g hg]
  rfl

/-- The action of `Λ[[G]]` on a finite module with continuous action. -/
def finiteTypeCompletedAction (N : FiniteTypeContinuousModule.{0, v, v} Λ G) :
    CompletedGroupAlgebra (ULift.{v} Λ) G →+* AddMonoid.End N.obj.obj.obj.V :=
  CompletedGroupAlgebra.toAddMonoidEnd N.obj.obj.obj.V
    (exists_openNormalSubgroup_smul_eq_finiteType N)

/-- A morphism of finite modules with continuous action commutes with the action of `Λ[[G]]`. -/
theorem finiteTypeCompletedAction_comm {N N' : FiniteTypeContinuousModule.{0, v, v} Λ G}
    (u : N ⟶ N') (a : CompletedGroupAlgebra (ULift.{v} Λ) G) (x : N.obj.obj.obj.V) :
    u.hom.hom.hom.hom.hom (finiteTypeCompletedAction N a x) =
      finiteTypeCompletedAction N' a (u.hom.hom.hom.hom.hom x) := by
  obtain ⟨U, hU⟩ := exists_openNormalSubgroup_smul_eq_finiteType N
  obtain ⟨U', hU'⟩ := exists_openNormalSubgroup_smul_eq_finiteType N'
  have hW : ∀ g ∈ U ⊓ U', ∀ y : N.obj.obj.obj.V, g • y = y := fun g hg => hU g hg.1
  have hW' : ∀ g ∈ U ⊓ U', ∀ y : N'.obj.obj.obj.V, g • y = y := fun g hg => hU' g hg.2
  rw [finiteTypeCompletedAction, finiteTypeCompletedAction,
    CompletedGroupAlgebra.toAddMonoidEnd_eq _ _ (U ⊓ U') hW,
    CompletedGroupAlgebra.toAddMonoidEnd_eq _ _ (U ⊓ U') hW']
  induction CompletedGroupAlgebra.eval (U ⊓ U') a using MonoidAlgebra.induction_linear with
  | zero => simp
  | add p q hp hq =>
    rw [map_add, map_add]
    show u.hom.hom.hom.hom.hom (_ + _) = _ + _
    exact (map_add _ _ _).trans (congrArg₂ (· + ·) hp hq)
  | single q c =>
    induction q using QuotientGroup.induction_on with
    | H g =>
      rw [quotientAlgebraAction_single, quotientAlgebraAction_single]
      show u.hom.hom.hom.hom.hom (c.down • finiteTypeContinuousModuleRepresentation Λ G N g x) =
        c.down • finiteTypeContinuousModuleRepresentation Λ G N' g (u.hom.hom.hom.hom.hom x)
      rw [map_smul, finiteTypeContinuousModule_hom_comm]

end Action

variable {Λ G} in
/-- **A finite `Λ`-module with continuous `G`-action as a `Λ[[G]]`-module.** -/
def finiteTypeCompletedModuleObj (N : FiniteTypeContinuousModule.{0, v, v} Λ G) :
    ModuleCat.{v} (CompletedGroupAlgebra (ULift.{v} Λ) G) :=
  let : Module (CompletedGroupAlgebra (ULift.{v} Λ) G) N.obj.obj.obj.V :=
    Module.compHom _ (finiteTypeCompletedAction N)
  ModuleCat.of _ N.obj.obj.obj.V

/-- **Finite `Λ`-modules with continuous `G`-action as `Λ[[G]]`-modules.** The underlying abelian
group and maps are unchanged. -/
def finiteTypeCompletedModule :
    FiniteTypeContinuousModule.{0, v, v} Λ G ⥤
      ModuleCat.{v} (CompletedGroupAlgebra (ULift.{v} Λ) G) where
  obj N := finiteTypeCompletedModuleObj N
  map {N N'} u :=
    let : Module (CompletedGroupAlgebra (ULift.{v} Λ) G) N.obj.obj.obj.V :=
      Module.compHom _ (finiteTypeCompletedAction N)
    let : Module (CompletedGroupAlgebra (ULift.{v} Λ) G) N'.obj.obj.obj.V :=
      Module.compHom _ (finiteTypeCompletedAction N')
    ModuleCat.ofHom (X := N.obj.obj.obj.V) (Y := N'.obj.obj.obj.V)
    { toFun := u.hom.hom.hom.hom.hom
      map_add' := map_add _
      map_smul' := fun a x => finiteTypeCompletedAction_comm u a x }
  map_id _N := rfl
  map_comp _u _u' := rfl

/-- `finiteTypeCompletedModule` does not change the underlying abelian group. -/
def finiteTypeCompletedModuleForgetIso :
    finiteTypeCompletedModule Λ G ⋙ forget₂ _ AddCommGrpCat.{v} ≅
      finiteTypeContinuousModuleι.{0, v, v} Λ G ⋙
        Stacks.Injectives.continuousModuleUnderlying.{0, v, v} Λ G ⋙
          forget₂ (ModuleCat.{v} Λ) AddCommGrpCat.{v} :=
  NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl)

variable [Finite Λ]

/-- **`finiteTypeCompletedModule` preserves finite limits.** -/
theorem preservesFiniteLimits_finiteTypeCompletedModule :
    PreservesFiniteLimits (finiteTypeCompletedModule Λ G) := by
  have h1 := preservesFiniteLimits_finiteTypeContinuousModuleι.{0, v, v} Λ G
  have h2 := preservesFiniteLimits_continuousModuleToModuleCat.{0, v, v} Λ G
  have : PreservesFiniteLimits (finiteTypeCompletedModule Λ G ⋙ forget₂ _ AddCommGrpCat.{v}) :=
    preservesFiniteLimits_of_natIso (finiteTypeCompletedModuleForgetIso Λ G).symm
  exact preservesFiniteLimits_of_reflects_of_preserves _ (forget₂ _ AddCommGrpCat.{v})

/-- **`finiteTypeCompletedModule` preserves finite colimits.** -/
theorem preservesFiniteColimits_finiteTypeCompletedModule :
    PreservesFiniteColimits (finiteTypeCompletedModule Λ G) := by
  have h1 := preservesFiniteColimits_finiteTypeContinuousModuleι.{0, v, v} Λ G
  have h2 := preservesFiniteColimits_continuousModuleToModuleCat.{0, v, v} Λ G
  have : PreservesFiniteColimits
      (finiteTypeCompletedModule Λ G ⋙ forget₂ _ AddCommGrpCat.{v}) :=
    preservesFiniteColimits_of_natIso (finiteTypeCompletedModuleForgetIso Λ G).symm
  exact preservesFiniteColimits_of_reflects_of_preserves _ (forget₂ _ AddCommGrpCat.{v})

/-- `finiteTypeCompletedModule` is additive. -/
instance : (finiteTypeCompletedModule Λ G).Additive where
  map_add := rfl

variable {Λ G} [CompactSpace G] {Γ : Type v} [Group Γ] [TopologicalSpace Γ] [IsTopologicalGroup Γ]
  [CompactSpace Γ] (φ : G →ₜ* Γ)

/-- Restriction of finite modules with continuous action along `φ` preserves finite limits. -/
theorem preservesFiniteLimits_finiteTypeContinuousModuleRes :
    PreservesFiniteLimits (finiteTypeContinuousModuleRes.{0, v, v} Λ φ) := by
  have : PreservesFiniteLimits (finiteTypeContinuousModuleRes.{0, v, v} Λ φ ⋙
      finiteTypeContinuousModuleι.{0, v, v} Λ G) :=
    Stacks.ContinuousCohomology.preservesFiniteLimits_finiteTypeContinuousModuleToRes Λ φ
  exact preservesFiniteLimits_of_reflects_of_preserves _ (finiteTypeContinuousModuleι.{0, v, v} Λ G)

/-- Restriction of finite modules with continuous action along `φ` preserves finite colimits. -/
theorem preservesFiniteColimits_finiteTypeContinuousModuleRes :
    PreservesFiniteColimits (finiteTypeContinuousModuleRes.{0, v, v} Λ φ) := by
  have : PreservesFiniteColimits (finiteTypeContinuousModuleRes.{0, v, v} Λ φ ⋙
      finiteTypeContinuousModuleι.{0, v, v} Λ G) :=
    Stacks.ContinuousCohomology.preservesFiniteColimits_finiteTypeContinuousModuleToRes Λ φ
  exact preservesFiniteColimits_of_reflects_of_preserves _
    (finiteTypeContinuousModuleι.{0, v, v} Λ G)

/-- Restriction of finite modules with continuous action is additive. -/
instance additive_finiteTypeContinuousModuleRes :
    (finiteTypeContinuousModuleRes.{0, v, v} Λ φ).Additive :=
  have := preservesFiniteLimits_finiteTypeContinuousModuleRes (Λ := Λ) φ
  Functor.additive_of_preserves_binary_products _

/-- **The group homology `M ↦ H_i(G, M) = Tor_i^{Λ[[G]]}(res_φ M, Λ)`** of finite `Λ`-modules with
continuous `Γ`-action, as a homological δ-functor: the left derived functors of the coinvariants of
`Λ[[G]]`-modules ([Stacks, Tag 03VI]), precomposed with the exact functor `M ↦ res_φ M` viewed as a
`Λ[[G]]`-module. -/
def finiteTypeGroupHomology :
    Stacks.CategoryHomology.HomologicalDeltaFunctor (FiniteTypeContinuousModule.{0, v, v} Λ Γ)
      (ModuleCat.{v} (ULift.{v} Λ)) :=
  have := preservesFiniteLimits_finiteTypeContinuousModuleRes (Λ := Λ) φ
  have := preservesFiniteColimits_finiteTypeContinuousModuleRes (Λ := Λ) φ
  have := preservesFiniteLimits_finiteTypeCompletedModule Λ G
  have := preservesFiniteColimits_finiteTypeCompletedModule Λ G
  (coinvariantsFunctor (ULift.{v} Λ) G).leftDerivedHomologicalDeltaFunctor.precomp
    (finiteTypeContinuousModuleRes.{0, v, v} Λ φ ⋙ finiteTypeCompletedModule Λ G)

/-- The functors of `finiteTypeGroupHomology` are the derived coinvariants of the restriction. -/
theorem finiteTypeGroupHomology_functor (n : ℕ) :
    (finiteTypeGroupHomology (Λ := Λ) φ).functor n =
      (finiteTypeContinuousModuleRes.{0, v, v} Λ φ ⋙ finiteTypeCompletedModule Λ G) ⋙
        (coinvariantsFunctor (ULift.{v} Λ) G).leftDerived n :=
  rfl

end Stacks.GroupHomology

end
