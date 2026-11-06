module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveRepresentationCoinvariantsInjective
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurveRepresentationCoindTrace

/-!
# `ψ_N : H²(C, j_!ℱ_N) ⟶ N_π` is bijective

Let `U` be a connected curve with smooth projective model `C` over an algebraically closed field,
`Λ` a finite ring of order invertible in the field and `N` a finite `Λ`-module with continuous
action of `π = π₁(U, y)`. The map `ψ_N` of
`Stacks.EtaleCohomology.curveRepresentationCoinvariantsMap` is bijective; this is the computation
`H²_c(X_k̄, ℱ_ρ) = M_π` of Tag 03VK.

## Main definitions

* `Stacks.EtaleCohomology.permutationModuleSum`: the map `N[π/H] ⟶ N`, `f ↦ Σ_x x · f(x)`, for
  an open subgroup `H` acting trivially on `N`.
* `Stacks.EtaleCohomology.permutationModuleCoinvariantsSum`: the sum `N[π/H]_π ⟶ N`,
  `f ↦ Σ_x f(x)`.

## Main results

* `Stacks.EtaleCohomology.bijective_curveRepresentationCoinvariantsMap_coind`: `ψ` is bijective
  on a permutation module `N[π/H]`.
* `Stacks.EtaleCohomology.bijective_curveRepresentationCoinvariantsMap`: `ψ_N` is bijective.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry Stacks.GroupCohomology

universe u

attribute [local instance] HasDerivedCategory.standard compactSpace_etaleFundamentalGroup

namespace Stacks.EtaleCohomology

/-- The underlying finite `Λ`-module of a finite `Λ`-module with continuous action. -/
abbrev finiteTypeContinuousModuleUnderlying (Λ : Type) [Ring Λ] {G : Type (u + 1)} [Group G]
    [TopologicalSpace G] (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G) :
    ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ) :=
  ⟨(continuousModuleToModuleCat.{0, u + 1, u + 1} Λ G).obj N.obj, N.property⟩

section Permutation

variable (Λ : Type) [Ring Λ] {G : Type (u + 1)} [Group G] [TopologicalSpace G]
  [IsTopologicalGroup G] [CompactSpace G] (H : OpenSubgroup G)

/-- **`N[G/H] ⟶ N`, `f ↦ Σ_x x · f(x)`**, for `H` acting trivially on `N`. -/
def permutationModuleSum (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G)
    (hH : ∀ h ∈ (H : Subgroup G), N.obj.obj.obj.ρ h = 1) :
    (finiteTypeContinuousModuleCoind Λ H).obj
        ((finiteTypeContinuousModuleTrivial Λ G).obj (finiteTypeContinuousModuleUnderlying Λ N)) ⟶
      N :=
  haveI : Fintype (G ⧸ (H : Subgroup G)) := Fintype.ofFinite _
  ObjectProperty.homMk (ObjectProperty.homMk (ObjectProperty.homMk
    { hom := ModuleCat.ofHom
        { toFun := fun f => ∑ x : G ⧸ (H : Subgroup G), (N.obj.obj.obj.ρ x.out).asHom.hom (f x)
          map_add' := fun f f' => by
            rw [← Finset.sum_add_distrib]
            exact Finset.sum_congr rfl fun x _ => map_add _ _ _
          map_smul' := fun a f => by
            rw [RingHom.id_apply, Finset.smul_sum]
            exact Finset.sum_congr rfl fun x _ => map_smul _ _ _ }
      comm := fun g => by
        ext f
        change ∑ x : G ⧸ (H : Subgroup G), (N.obj.obj.obj.ρ x.out).asHom.hom (f (g⁻¹ • x)) =
          (N.obj.obj.obj.ρ g).asHom.hom (∑ x : G ⧸ (H : Subgroup G), (N.obj.obj.obj.ρ x.out).asHom.hom (f x))
        rw [map_sum]
        refine Fintype.sum_equiv (MulAction.toPerm g⁻¹) _ _ fun x => ?_
        have hx : g⁻¹ • x = ((g⁻¹ * x.out : G) : G ⧸ (H : Subgroup G)) := by
          conv_lhs => rw [← QuotientGroup.out_eq' x]
          rfl
        obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H : Subgroup G) (g⁻¹ * x.out)
        have hout : (g⁻¹ • x).out = g⁻¹ * x.out * h := by rw [hx]; exact hh
        change (N.obj.obj.obj.ρ x.out).asHom.hom (f (g⁻¹ • x)) =
          (N.obj.obj.obj.ρ g).asHom.hom ((N.obj.obj.obj.ρ (g⁻¹ • x).out).asHom.hom (f (g⁻¹ • x)))
        rw [hout]
        refine Eq.trans ?_ (finiteTypeContinuousModule_ρ_mul_apply Λ N g _ _)
        refine Eq.trans ?_ (congrArg (fun k => (N.obj.obj.obj.ρ k).asHom.hom (f (g⁻¹ • x)))
          (show x.out * h = g * (g⁻¹ * x.out * h) by group))
        refine Eq.trans ?_ (finiteTypeContinuousModule_ρ_mul_apply Λ N x.out h _).symm
        exact congrArg (fun m => (N.obj.obj.obj.ρ x.out).asHom.hom m)
          (congrArg (fun φ => φ.asHom.hom (f (g⁻¹ • x))) (hH h h.2)).symm }))

/-- `permutationModuleSum` sends `f` to `Σ_x x · f(x)`. -/
lemma permutationModuleSum_apply (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G)
    (hH : ∀ h ∈ (H : Subgroup G), N.obj.obj.obj.ρ h = 1)
    (f : G ⧸ (H : Subgroup G) → N.obj.obj.obj.V) :
    haveI : Fintype (G ⧸ (H : Subgroup G)) := Fintype.ofFinite _
    (permutationModuleSum Λ H N hH).hom.hom.hom.hom.hom f =
      ∑ x : G ⧸ (H : Subgroup G), (N.obj.obj.obj.ρ x.out).asHom.hom (f x) := rfl

/-- The map `N[G/H] ⟶ N`, `f ↦ Σ_x x · f(x)`, is surjective. -/
theorem surjective_permutationModuleSum (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G)
    (hH : ∀ h ∈ (H : Subgroup G), N.obj.obj.obj.ρ h = 1) :
    Function.Surjective (permutationModuleSum Λ H N hH).hom.hom.hom.hom.hom := by
  classical
  let : Fintype (G ⧸ (H : Subgroup G)) := Fintype.ofFinite _
  intro m
  refine ⟨fun x => if x = ((1 : G) : G ⧸ (H : Subgroup G)) then m else 0, ?_⟩
  refine (permutationModuleSum_apply Λ H N hH _).trans ?_
  refine (Finset.sum_eq_single ((1 : G) : G ⧸ (H : Subgroup G))
    (fun x _ hx => (congrArg (N.obj.obj.obj.ρ x.out).asHom.hom (if_neg hx)).trans (map_zero _))
    (fun h => absurd (Finset.mem_univ _) h)).trans ?_
  obtain ⟨h, hh⟩ := QuotientGroup.mk_out_eq_mul (H : Subgroup G) (1 : G)
  exact (congrArg (N.obj.obj.obj.ρ ((1 : G) : G ⧸ (H : Subgroup G)).out).asHom.hom (if_pos rfl)).trans
    ((congrArg (fun k => (N.obj.obj.obj.ρ k).asHom.hom m) (hh.trans (one_mul _))).trans
      (congrArg (fun φ => φ.asHom.hom m) (hH h h.2)))

/-- The map `N[G/H] ⟶ N`, `f ↦ Σ_x x · f(x)`, is an epimorphism. -/
theorem epi_permutationModuleSum (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ G)
    (hH : ∀ h ∈ (H : Subgroup G), N.obj.obj.obj.ρ h = 1) :
    Epi (permutationModuleSum Λ H N hH) :=
  (finiteTypeContinuousModuleToAction Λ G ⋙ Action.forget (ModuleCat.{u + 1} Λ) G).epi_of_epi_map
    ((ModuleCat.epi_iff_surjective _).2 (surjective_permutationModuleSum Λ H N hH))

/-- The submodule defining the coinvariants of `N[G/H]` lies in the kernel of the sum
`f ↦ Σ_x f(x)`. -/
theorem permutationModule_coinvariantsKer_le_ker [Fintype (G ⧸ (H : Subgroup G))]
    (N : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ)) :
    Stacks.Trace.coinvariantsKer (finiteTypeContinuousModuleRepresentation Λ G
      ((finiteTypeContinuousModuleCoind Λ H).obj ((finiteTypeContinuousModuleTrivial Λ G).obj N))) ≤
      LinearMap.ker (∑ x : G ⧸ (H : Subgroup G),
        (LinearMap.proj x : (G ⧸ (H : Subgroup G) → N.obj) →ₗ[Λ] N.obj)) := by
  refine Submodule.span_le.2 ?_
  rintro _ ⟨⟨g, f⟩, rfl⟩
  let S : (G ⧸ (H : Subgroup G) → N.obj) →ₗ[Λ] N.obj :=
    ∑ x : G ⧸ (H : Subgroup G), LinearMap.proj x
  have hS : ∀ f' : G ⧸ (H : Subgroup G) → N.obj, S f' = ∑ x, f' x := fun f' =>
    LinearMap.sum_apply _ _ _
  have key : ∀ f' : G ⧸ (H : Subgroup G) → N.obj, S ((fun y => f' (g⁻¹ • y)) - f') = 0 :=
    fun f' => (map_sub S _ _).trans (sub_eq_zero.2
      ((hS _).trans ((Fintype.sum_equiv (MulAction.toPerm (β := G ⧸ (H : Subgroup G)) g⁻¹) _ _
        fun x => rfl).trans (hS f').symm)))
  exact key f

/-- **The sum `N[G/H]_G ⟶ N`, `f ↦ Σ_x f(x)`**, for a finite `Λ`-module `N`. -/
def permutationModuleCoinvariantsSum [Fintype (G ⧸ (H : Subgroup G))]
    (N : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ)) :
    Stacks.Trace.coinvariants (finiteTypeContinuousModuleRepresentation Λ G
      ((finiteTypeContinuousModuleCoind Λ H).obj ((finiteTypeContinuousModuleTrivial Λ G).obj N)))
      →ₗ[Λ] N.obj :=
  Submodule.liftQ _ _ (permutationModule_coinvariantsKer_le_ker Λ H N)

/-- The sum `N[G/H]_G ⟶ N`, `f ↦ Σ_x f(x)`, is surjective. -/
theorem surjective_permutationModuleCoinvariantsSum [Fintype (G ⧸ (H : Subgroup G))]
    (N : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ)) :
    Function.Surjective (permutationModuleCoinvariantsSum Λ H N) := by
  classical
  intro m
  refine ⟨Stacks.Trace.coinvariantsMk _
    (fun x => if x = ((1 : G) : G ⧸ (H : Subgroup G)) then m else 0), ?_⟩
  refine (Submodule.liftQ_apply _ (∑ x : G ⧸ (H : Subgroup G),
    (LinearMap.proj x : (G ⧸ (H : Subgroup G) → N.obj) →ₗ[Λ] N.obj)) _).trans
    ((LinearMap.sum_apply _ _ _).trans ?_)
  exact (Finset.sum_ite_eq' Finset.univ ((1 : G) : G ⧸ (H : Subgroup G)) (fun _ => m)).trans
    (if_pos (Finset.mem_univ _))

end Permutation

section Psi

variable {K : Type u} [Field K] [IsAlgClosed K] {C : Scheme.{u}} (q : C ⟶ Spec (.of K))
  [IsCurve K q] [Smooth q] [IsProper q] (Λ : Type) [Ring Λ] [Fintype Λ]
  (B : BigEtaleSite.{u}) (U : B.Scheme) [ConnectedSpace U.1] (y : GeometricPoint U.1)
  (hn : IsUnit ((Fintype.card Λ : ℕ) : K)) {ζ : K} (hζ : IsPrimitiveRoot ζ (Fintype.card Λ))
  (jC : U.1 ⟶ C) [IsOpenImmersion jC] (hfin : ((Set.range jC.base)ᶜ).Finite)

/-- **`ψ` is bijective on a permutation module `N[π/H]`**, for an open subgroup `H` of `π` and
a finite `Λ`-module `N`. -/
theorem bijective_curveRepresentationCoinvariantsMap_coind
    (H : OpenSubgroup (EtaleFundamentalGroup U.1 y))
    (N : ObjectProperty.FullSubcategory (ModuleCat.isFG.{u + 1} Λ)) :
    Function.Bijective (curveRepresentationCoinvariantsMap B U y q Λ hn hζ jC hfin
      ((finiteTypeContinuousModuleCoind Λ H).obj
        ((finiteTypeContinuousModuleTrivial Λ _).obj N))) := by
  let : Fintype (EtaleFundamentalGroup U.1 y ⧸ (H : Subgroup _)) := Fintype.ofFinite _
  have : Module.Finite Λ N.obj := N.property
  have : Finite N.obj := Module.finite_of_finite Λ
  let e := curveExtensionByZeroCoindTrace B U y H q Λ hn hζ jC N
  have : Finite (((etaleModuleGlobalSections.{u, 0} Λ C).rightDerivedPlus ((2 : ℕ) : ℤ)).obj
      ((etaleModuleExtensionByZero.{u, 0} Λ jC).obj
        ((representationSheaf B U y Λ).obj ((finiteTypeContinuousModuleCoind Λ H).obj
          ((finiteTypeContinuousModuleTrivial Λ _).obj N))))) :=
    Finite.of_equiv _ e.toEquiv.symm
  have : Finite ((finiteTypeContinuousModuleCoind Λ H).obj
      ((finiteTypeContinuousModuleTrivial Λ _).obj N)).obj.obj.obj.V :=
    (inferInstance : Finite (EtaleFundamentalGroup U.1 y ⧸ (H : Subgroup _) → N.obj))
  have : Finite (Stacks.Trace.coinvariants (finiteTypeContinuousModuleRepresentation Λ _
      ((finiteTypeContinuousModuleCoind Λ H).obj
        ((finiteTypeContinuousModuleTrivial Λ _).obj N)))) :=
    Finite.of_surjective _ (Submodule.mkQ_surjective _)
  have hsurj := surjective_curveRepresentationCoinvariantsMap q Λ B U y hn hζ jC hfin
    ((finiteTypeContinuousModuleCoind Λ H).obj ((finiteTypeContinuousModuleTrivial Λ _).obj N))
  refine hsurj.bijective_of_nat_card_le ?_
  rw [Nat.card_congr e.toEquiv]
  exact Nat.card_le_card_of_surjective _ (surjective_permutationModuleCoinvariantsSum Λ H N)

/-- **`ψ_N : H²(C, j_!ℱ_N) ⟶ N_π` is bijective** (the computation of Tag 03VK). -/
theorem bijective_curveRepresentationCoinvariantsMap
    (N : FiniteTypeContinuousModule.{0, u + 1, u + 1} Λ (EtaleFundamentalGroup U.1 y)) :
    Function.Bijective (curveRepresentationCoinvariantsMap B U y q Λ hn hζ jC hfin N) := by
  obtain ⟨S, -, hSo, hS1⟩ := exists_isOpen_normal_subgroup_ρ_eq_one_finiteType Λ _ N
  let H : OpenSubgroup (EtaleFundamentalGroup U.1 y) := ⟨S, hSo⟩
  have := epi_permutationModuleSum Λ H N hS1
  exact ⟨injective_curveRepresentationCoinvariantsMap_of_epi q Λ B U y hn hζ jC hfin
    (permutationModuleSum Λ H N hS1) (bijective_curveRepresentationCoinvariantsMap_coind q Λ B U y
      hn hζ jC hfin H (finiteTypeContinuousModuleUnderlying Λ N)).1,
    surjective_curveRepresentationCoinvariantsMap q Λ B U y hn hζ jC hfin N⟩

end Psi

end Stacks.EtaleCohomology

end
