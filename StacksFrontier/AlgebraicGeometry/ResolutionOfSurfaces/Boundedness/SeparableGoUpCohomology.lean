module

public import StacksFrontier.AlgebraicGeometry.AffineCohomologyComparison.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Basic
public import StacksFrontier.AlgebraicGeometry.TopDegreeBaseChange.DerivedFunctorAdditive
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.Reduction
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.Boundedness.SeparableGoUpTrace

/-!
# Bounding `H¹(Y, 𝒪_Y)` along a finite morphism with a trace identity

Let `π : Y ⟶ X` be a finite surjective morphism of integral schemes with `X` normal, lying over
a morphism `f : X ⟶ Spec A`. Suppose global functions `b₁, …, bₙ, e₁, …, eₙ` of `Y` and an
element `d ∈ A` satisfy `d σ = ∑ⱼ Trace(bⱼ σ) eⱼ` in the function field of `Y`. Then

  `length_A H¹(Y, 𝒪_Y) ≤ n · length_A H¹(X, 𝒪_X) + length_A H¹(Y, 𝒪_Y)[d]`.

This is the cohomological step of the source's proof of [Stacks, Tag 0AXL]. The source runs it
through the cokernel of `Φ : π_* 𝒪_Y → 𝒪_X^{⊕ n}` and the exact sequence
`H⁰(X, Coker Φ) → H¹(Y, 𝒪_Y) → H¹(X, 𝒪_X)^{⊕ n}`; here the same conclusion is drawn without
the cokernel: the maps `Φⱼ = Trace(bⱼ -)` and `Θⱼ = (- · eⱼ)` satisfy `∑ⱼ Θⱼ ∘ Φⱼ = d`, so on
`H¹(X, π_* 𝒪_Y) = H¹(Y, 𝒪_Y)` the kernel of `(H¹(Φⱼ))ⱼ` is killed by `d`.

## Main results

* `Module.length_le_of_ker_le_torsionBy`: a linear map to `Pⁿ` whose kernel is killed by `d`
  bounds the length of its source by `n · length P` plus the length of the `d`-torsion.
* `AlgebraicGeometry.SeparableGoUp.length_firstCohomology_le`: the bound displayed above.

## Implementation notes

`H¹(Y, 𝒪_Y)` is compared with `H¹(X, π_* 𝒪_Y)` by [Stacks, Tag 089W],
`Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward`, a finite morphism being affine.

## References

* [Stacks Project, Tag 0AXL](https://stacks.math.columbia.edu/tag/0AXL)
* [Stacks Project, Tag 089W](https://stacks.math.columbia.edu/tag/089W)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

/-- **A linear map to `Pⁿ` whose kernel is killed by `d`.** The source has length at most
`n · length P` plus the length of its `d`-torsion. -/
theorem Module.length_le_of_ker_le_torsionBy {R M P : Type*} [CommRing R] [AddCommGroup M]
    [Module R M] [AddCommGroup P] [Module R P] {n : ℕ} (Λ : M →ₗ[R] (Fin n → P)) (d : R)
    (h : ∀ x, Λ x = 0 → d • x = 0) :
    Module.length R M ≤ n * Module.length R P + Module.length R (Submodule.torsionBy R M d) := by
  have hker : LinearMap.ker Λ ≤ Submodule.torsionBy R M d := fun x hx =>
    (Submodule.mem_torsionBy_iff _ _).mpr (h x hx)
  rw [Module.length_eq_add_of_exact (LinearMap.ker Λ).subtype Λ.rangeRestrict
    (Submodule.subtype_injective _) Λ.surjective_rangeRestrict
    (LinearMap.exact_iff.mpr (by rw [LinearMap.ker_rangeRestrict, Submodule.range_subtype])),
    add_comm]
  gcongr
  · calc Module.length R (LinearMap.range Λ) ≤ Module.length R (Fin n → P) :=
          Module.length_le_of_injective _ (Submodule.subtype_injective _)
      _ = n * Module.length R P := by simp
  · exact Module.length_le_of_injective (Submodule.inclusion hker)
      (Submodule.inclusion_injective hker)

namespace AlgebraicGeometry.SeparableGoUp

attribute [local instance] HasDerivedCategory.standard

variable {A : Type u} [CommRing A] {X Y : Scheme.{u}} (f : X ⟶ Spec (.of A)) (π : Y ⟶ X)

/-- The first cohomology on `X` of a sheaf of modules, as a module over `A`. -/
abbrev firstCohomologyBase (F : X.Modules) : ModuleCat.{u} A :=
  (ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).obj
    (((Scheme.sectionsFunctor X).rightDerived 1).obj F)

/-- **`H¹(Y, 𝒪_Y) = H¹(X, π_* 𝒪_Y)` as `A`-modules**, for an affine morphism `π`. -/
def firstCohomologyPushforwardEquiv [IsAffineHom π] :
    firstCohomologyAsBaseModule Y (π ≫ f) ≃ₗ[A]
      firstCohomologyBase f ((Scheme.Modules.pushforward π).obj
        (SheafOfModules.unit Y.ringCatSheaf)) := by
  let e := Stacks.Cohomology.AffineComparison.cohomologyIsoPushforward π
    (SheafOfModules.unit Y.ringCatSheaf) 1
  exact
    { toFun := fun x => e.hom.hom x
      invFun := fun y => e.inv.hom y
      left_inv := fun x => by
        change (e.hom ≫ e.inv).hom x = x
        rw [e.hom_inv_id]
        rfl
      right_inv := fun y => by
        change (e.inv ≫ e.hom).hom y = y
        rw [e.inv_hom_id]
        rfl
      map_add' := fun x y => map_add e.hom.hom x y
      map_smul' := fun a x =>
        e.hom.hom.map_smul (((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom a) x }

/-- The `A`-linear map `H¹(X, F) ⟶ H¹(X, G)` induced by a morphism of sheaves of modules. -/
def firstCohomologyBaseMap {F G : X.Modules} (φ : F ⟶ G) :
    firstCohomologyBase f F →ₗ[A] firstCohomologyBase f G :=
  ((ModuleCat.restrictScalars ((Scheme.ΓSpecIso (.of A)).inv ≫ f.appTop).hom).map
    (((Scheme.sectionsFunctor X).rightDerived 1).map φ)).hom

/-- The map `firstCohomologyBaseMap f φ` is the map induced by `φ` on first right derived functors
of global sections. -/
theorem firstCohomologyBaseMap_apply {F G : X.Modules} (φ : F ⟶ G) (x : firstCohomologyBase f F) :
    firstCohomologyBaseMap f φ x = (((Scheme.sectionsFunctor X).rightDerived 1).map φ).hom x :=
  rfl

/-- The map induced on first cohomology by a composite `φ ≫ ψ` is the composite of the induced
maps. -/
theorem firstCohomologyBaseMap_comp {F G H : X.Modules} (φ : F ⟶ G) (ψ : G ⟶ H)
    (x : firstCohomologyBase f F) :
    firstCohomologyBaseMap f (φ ≫ ψ) x =
      firstCohomologyBaseMap f ψ (firstCohomologyBaseMap f φ x) :=
  congrArg (fun g : ((Scheme.sectionsFunctor X).rightDerived 1).obj F ⟶
      ((Scheme.sectionsFunctor X).rightDerived 1).obj H => g.hom x)
    (((Scheme.sectionsFunctor X).rightDerived 1).map_comp φ ψ)

/-- Evaluation at a class of the maps induced on first cohomology, as an additive map. -/
def firstCohomologyBaseEval {F G : X.Modules} (x : firstCohomologyBase f F) :
    (F ⟶ G) →+ firstCohomologyBase f G where
  toFun φ := firstCohomologyBaseMap f φ x
  map_zero' := (congrArg (fun g : ((Scheme.sectionsFunctor X).rightDerived 1).obj F ⟶
      ((Scheme.sectionsFunctor X).rightDerived 1).obj G => g.hom x)
    (((Scheme.sectionsFunctor X).rightDerived 1).map_zero F G)).trans rfl
  map_add' φ ψ := (congrArg (fun g : ((Scheme.sectionsFunctor X).rightDerived 1).obj F ⟶
      ((Scheme.sectionsFunctor X).rightDerived 1).obj G => g.hom x)
    (((Scheme.sectionsFunctor X).rightDerived 1).map_add (f := φ) (g := ψ))).trans rfl

/-- The map induced on first cohomology by a finite sum of morphisms is the sum of the induced
maps. -/
theorem firstCohomologyBaseMap_sum {F G : X.Modules} {ι : Type*}
    (s : Finset ι) (φ : ι → (F ⟶ G)) (x : firstCohomologyBase f F) :
    firstCohomologyBaseMap f (∑ i ∈ s, φ i) x = ∑ i ∈ s, firstCohomologyBaseMap f (φ i) x :=
  map_sum (firstCohomologyBaseEval f x) φ s

variable [IsIntegral X] [IsIntegral Y] [IsFinite π] [Surjective π] [IsNormal X]

/-- **Stacks Project, Tag 0AXL, the cohomological step.** Let `π : Y ⟶ X` be a finite surjective
morphism of integral schemes with `X` normal, over `f : X ⟶ Spec A`. If global functions
`b₁, …, bₙ, e₁, …, eₙ` of `Y` and `d ∈ A` satisfy `d σ = ∑ⱼ Trace(bⱼ σ) eⱼ` for every `σ` in the
function field of `Y`, then
`length_A H¹(Y, 𝒪_Y) ≤ n · length_A H¹(X, 𝒪_X) + length_A H¹(Y, 𝒪_Y)[d]`. -/
theorem length_firstCohomology_le {n : ℕ} (b e : Fin n → Γ(Y, ⊤)) (d : A)
    (h : letI := functionFieldAlgebra π
      ∀ σ : Y.functionField,
        dominantFunctionFieldMap π (X.presheaf.germ ⊤ (genericPoint X) trivial
            (baseSection X f d)) * σ =
          ∑ i, dominantFunctionFieldMap π (Algebra.trace X.functionField Y.functionField
            (Y.presheaf.germ ⊤ (genericPoint Y) trivial (b i) * σ)) *
              Y.presheaf.germ ⊤ (genericPoint Y) trivial (e i)) :
    Module.length A (firstCohomologyAsBaseModule Y (π ≫ f)) ≤
      n * Module.length A (firstCohomologyAsBaseModule X f) +
        Module.length A (Submodule.torsionBy A (firstCohomologyAsBaseModule Y (π ≫ f)) d) := by
  let F := (Scheme.Modules.pushforward π).obj (SheafOfModules.unit Y.ringCatSheaf)
  let E := firstCohomologyPushforwardEquiv f π
  let φ : Fin n → (F ⟶ (SheafOfModules.unit X.ringCatSheaf : X.Modules)) := fun j =>
    pushMulHom π (b j) ≫ traceHom π
  let Λ : firstCohomologyBase f F →ₗ[A] (Fin n → firstCohomologyAsBaseModule X f) :=
    LinearMap.pi fun j => firstCohomologyBaseMap f (φ j)
  have hker : ∀ x, Λ x = 0 → d • x = 0 := by
    intro x hx
    have hsum := congrArg (fun ψ => firstCohomologyBaseMap f ψ x)
      (sum_traceHom_comp_mulHom π b e (baseSection X f d) h)
    rw [firstCohomologyBaseMap_sum] at hsum
    have hzero : ∀ j, firstCohomologyBaseMap f (pushMulHom π (b j) ≫ traceHom π ≫
        mulHom π (e j)) x = 0 := fun j => by
      have hassoc : (pushMulHom π (b j) ≫ traceHom π ≫ mulHom π (e j) : F ⟶ F) =
          φ j ≫ mulHom π (e j) := (Category.assoc _ _ _).symm
      rw [hassoc]
      refine (firstCohomologyBaseMap_comp f _ _ x).trans ?_
      have hj : firstCohomologyBaseMap f (φ j) x = 0 := congrFun hx j
      rw [hj, map_zero]
    simp only [hzero, Finset.sum_const_zero] at hsum
    exact hsum.trans
      (Scheme.rightDerived_sectionsFunctor_map_smulEnd_apply X (baseSection X f d) 1 F x) |>.symm
  have key := Module.length_le_of_ker_le_torsionBy Λ d hker
  have htors : Module.length A (Submodule.torsionBy A (firstCohomologyBase f F) d) =
      Module.length A (Submodule.torsionBy A (firstCohomologyAsBaseModule Y (π ≫ f)) d) := by
    let e' : Submodule.torsionBy A (firstCohomologyAsBaseModule Y (π ≫ f)) d ≃ₗ[A]
        Submodule.torsionBy A (firstCohomologyBase f F) d :=
      { toFun := fun x => ⟨E x.1, by
          rw [Submodule.mem_torsionBy_iff, ← map_smul,
            (Submodule.mem_torsionBy_iff _ _).mp x.2, map_zero]⟩
        invFun := fun y => ⟨E.symm y.1, by
          rw [Submodule.mem_torsionBy_iff, ← map_smul,
            (Submodule.mem_torsionBy_iff _ _).mp y.2, map_zero]⟩
        left_inv := fun x => Subtype.ext (E.symm_apply_apply x.1)
        right_inv := fun y => Subtype.ext (E.apply_symm_apply y.1)
        map_add' := fun x y => Subtype.ext (map_add E x.1 y.1)
        map_smul' := fun a x => Subtype.ext (map_smul E a x.1) }
    exact e'.length_eq.symm
  rw [E.length_eq, ← htors]
  exact key

end AlgebraicGeometry.SeparableGoUp

end
