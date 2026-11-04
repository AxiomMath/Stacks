module

public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayCupPairingBase

/-!
# The relative cup product induces the cup product on cohomology

Let `f : (X, 𝒪_X) ⟶ (Y, 𝒪_Y)` be a morphism of ringed spaces and `K, M ∈ D(𝒪_X)`.  The relative
cup product `μ_f : Rf_*K ⊗^𝐋_{𝒪_Y} Rf_*M ⟶ Rf_*(K ⊗^𝐋_{𝒪_X} M)` of Tag 0B68 induces, through the
Leray identification `Hⁿ(Y, Rf_*-) = Hⁿ(X, -)` of Tag 0D5W, the cup product of Cohomology,
Section 0FKU on `X`: for `ξ ∈ Hⁱ(Y, Rf_*K)` and `η ∈ Hʲ(Y, Rf_*M)`,

`leray(Hⁱ⁺ʲ(RΓ(Y, μ_f))(ξ ∪_Y η)) = leray(ξ) ∪_X leray(η)`.

This is the statement of Differential Graded Sheaves, Section 0FU3 that `μ` induces the cup
product on cohomology.

## Main definitions

* `Stacks.Cohomology.LerayCupPairing.lerayMap`: the Leray identification on cohomology,
  `Hⁿ(Y, Rf_*K) ⟶ Hⁿ(X, K)`.

## Main results

* `Stacks.Cohomology.LerayCupPairing.lerayCohomologyIso_relativeCupProduct_cupPairing`: **the
  relative cup product induces the cup product on cohomology.**
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits CategoryTheory.MonoidalCategory
open Opposite TopologicalSpace
open Stacks.Cohomology.GlobalKunneth
open Stacks.Cohomology.DerivedSectionsLeray
open Stacks.Cohomology.DerivedGlobalCupProduct
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite
open Stacks.Cohomology.DerivedRelativeCupProduct (relativeCupProduct)
open scoped TensorProduct CategoryTheory.Prod

universe u

namespace Stacks.Cohomology.LerayCupPairing

attribute [local instance] HasDerivedCategory.standard

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

/-- **The Leray identification on cohomology**, as a map `Hⁿ(Y, Rf_*K) ⟶ Hⁿ(X, K)` of
abelian groups (it is `Γ(Y, 𝒪_Y)`-linear for the module structure on the target restricted along
`f^♯`). -/
noncomputable def lerayMap (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (n : ℤ)
    (ξ : cohomologyModule ((derivedPushforward f).obj K) n) : cohomologyModule K n :=
  (lerayCohomologyIso f K n).hom ξ

/-- The Leray identification `Hⁿ(Y, Rf_*K) ⟶ Hⁿ(X, K)` is injective. -/
theorem lerayMap_injective (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X)))
    (n : ℤ) : Function.Injective (lerayMap f K n) :=
  (lerayCohomologyIso f K n).toLinearEquiv.injective

/-- The Leray identification is natural in `K`: it commutes with the maps induced on cohomology by
a morphism `g : K ⟶ K'` and by `Rf_*g`. -/
theorem lerayMap_naturality
    {K K' : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))} (g : K ⟶ K') (n : ℤ)
    (x : cohomologyModule ((derivedPushforward f).obj K) n) :
    lerayMap f K' n (((DerivedCategory.homologyFunctor _ n).map
          ((baseSections Y).map ((derivedPushforward f).map g))).hom x) =
      ((DerivedCategory.homologyFunctor _ n).map ((baseSections X).map g)).hom
        (lerayMap f K n x) :=
  lerayCohomologyIso_naturality_apply f g n x

/-- The Leray identification sends the pushed-forward class of a global cocycle `c` of a complex
`N` of `𝒪_X`-modules to the class of `c` in `Hⁿ(X, N)`. -/
theorem lerayMap_pushClass
    (N : CochainComplex (AlgebraicGeometry.RingedSpace.KFlatDerivedPullback.Modules X) ℤ)
    (n : ℤ) (c : (sectionsComplex X N).cycles n) :
    lerayMap f (DerivedCategory.Q.obj N) n (pushClass f N n c) = globalClass N n c :=
  lerayCohomologyIso_pushClass f N n c

/-- The class of `ξ ∈ Hⁱ(Y, Rf_*K)` is the image of the class of `1` under `Rf_*φ`, for the
morphism `φ : 𝒪_X[-i] ⟶ K` evaluating to the Leray image of `ξ`. -/
theorem eq_pushClass_of_evalUnit
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i : ℤ)
    (ξ : cohomologyModule ((derivedPushforward f).obj K) i)
    (φ : DerivedCategory.Q.obj (unitComplex X i) ⟶ K)
    (hφ : evalUnit K i φ = lerayMap f K i ξ) :
    ξ = ((DerivedCategory.homologyFunctor _ i).map ((baseSections Y).map
      ((derivedPushforward f).map φ))).hom (pushClass f (unitComplex X i) i (unitCycle X i)) := by
  apply lerayMap_injective f K i
  refine Eq.trans ?_ (lerayMap_naturality f φ i _).symm
  refine hφ.symm.trans ?_
  exact congrArg _ (lerayMap_pushClass f (unitComplex X i) i (unitCycle X i)).symm

/-- Every class of `Hⁱ(Y, Rf_*K)` is pushed forward from the class of `1`. -/
theorem exists_eq_pushClass
    (K : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i : ℤ)
    (ξ : cohomologyModule ((derivedPushforward f).obj K) i) :
    ∃ φ : DerivedCategory.Q.obj (unitComplex X i) ⟶ K,
      ξ = ((DerivedCategory.homologyFunctor _ i).map ((baseSections Y).map
        ((derivedPushforward f).map φ))).hom (pushClass f (unitComplex X i) i (unitCycle X i)) ∧
      evalUnit K i φ = lerayMap f K i ξ := by
  obtain ⟨φ, hφ⟩ := evalUnit_surjective K i (lerayMap f K i ξ)
  exact ⟨φ, eq_pushClass_of_evalUnit f K i ξ φ hφ, hφ⟩

/-- The Leray identification carries the image under `Hⁱ⁺ʲ(RΓ(Y, μ_f))` of the cup product on
`Y` of the classes `Rf_*φ(1)` and `Rf_*ψ(1)` to the cup product on `X` of `evalUnit K i φ` and
`evalUnit M j ψ`. -/
theorem lerayCohomologyIso_relativeCupProduct_cupPairing_unit
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i j : ℤ)
    (φ : DerivedCategory.Q.obj (unitComplex X i) ⟶ K)
    (ψ : DerivedCategory.Q.obj (unitComplex X j) ⟶ M) :
    (lerayCohomologyIso f (((derivedTensorProductFunctor X.sheaf).obj K).obj M) (i + j)).hom
      (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections Y).map
        (relativeCupProduct f K M))).hom
        ((cupPairing (cupProductOnSpace Y) _ _ i j).hom
          (((DerivedCategory.homologyFunctor _ i).map ((baseSections Y).map
            ((derivedPushforward f).map φ))).hom
              (pushClass f (unitComplex X i) i (unitCycle X i)) ⊗ₜ
           ((DerivedCategory.homologyFunctor _ j).map ((baseSections Y).map
            ((derivedPushforward f).map ψ))).hom
              (pushClass f (unitComplex X j) j (unitCycle X j))))) =
      (cupPairing (cupProductOnSpace X) K M i j).hom (evalUnit K i φ ⊗ₜ evalUnit M j ψ) := by
  have e1 := cupPairing_naturality_apply (cupProductOnSpace Y) ((derivedPushforward f).map φ)
    ((derivedPushforward f).map ψ) i j (pushClass f (unitComplex X i) i (unitCycle X i))
    (pushClass f (unitComplex X j) j (unitCycle X j))
  have e4 := lerayCohomologyIso_relativeCupProduct_pushClass f (unitComplex X i) (unitComplex X j)
    (Stacks.SheafOfModules.isKFlat_single_obj_unit X.sheaf i)
    (Stacks.SheafOfModules.isKFlat_single_obj_unit X.sheaf j) i j (unitCycle X i) (unitCycle X j)
  have e5 := cupPairing_naturality_apply (cupProductOnSpace X) φ ψ i j
    (globalClass (unitComplex X i) i (unitCycle X i))
    (globalClass (unitComplex X j) j (unitCycle X j))
  have e2 := Stacks.Cohomology.DerivedRelativeCupProduct.relativeCupProduct_natural f φ ψ
  let G := baseSections Y ⋙ DerivedCategory.homologyFunctor (ModuleCat.{u} (baseRing Y)) (i + j)
  let w := (cupPairing (cupProductOnSpace Y) _ _ i j).hom
      (pushClass f (unitComplex X i) i (unitCycle X i) ⊗ₜ
        pushClass f (unitComplex X j) j (unitCycle X j))
  have e3 : (G.map (relativeCupProduct f K M)).hom
      ((G.map ((Functor.uncurry.obj (derivedTensorProductFunctor Y.sheaf)).map
        ((derivedPushforward f).map φ ×ₘ (derivedPushforward f).map ψ))).hom w) =
      (G.map ((derivedPushforward f).map
        ((Functor.uncurry.obj (derivedTensorProductFunctor X.sheaf)).map (φ ×ₘ ψ)))).hom
        ((G.map (relativeCupProduct f (DerivedCategory.Q.obj (unitComplex X i))
          (DerivedCategory.Q.obj (unitComplex X j)))).hom w) := by
    refine (functor_map_comp₂_apply G _ _ w).symm.trans ?_
    refine (congrArg (fun g => (G.map g).hom w) e2).trans ?_
    exact functor_map_comp₂_apply G _ _ w
  refine (congrArg (lerayCohomologyIso f _ (i + j)).hom
    ((congrArg (G.map (relativeCupProduct f K M)).hom e1).trans e3)).trans ?_
  refine (lerayCohomologyIso_naturality_apply f _ (i + j) _).trans ?_
  exact (congrArg _ e4).trans e5.symm

/-- The relative cup product induces the cup product on cohomology, for classes `ξ` and `η`
given as `Rf_*φ(1)` and `Rf_*ψ(1)` with `φ` and `ψ` evaluating at the unit to their Leray
images. -/
theorem lerayCohomologyIso_relativeCupProduct_cupPairing_of_eq
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i j : ℤ)
    (ξ : cohomologyModule ((derivedPushforward f).obj K) i)
    (η : cohomologyModule ((derivedPushforward f).obj M) j)
    (φ : DerivedCategory.Q.obj (unitComplex X i) ⟶ K)
    (ψ : DerivedCategory.Q.obj (unitComplex X j) ⟶ M)
    (hξ : ξ = ((DerivedCategory.homologyFunctor _ i).map ((baseSections Y).map
        ((derivedPushforward f).map φ))).hom (pushClass f (unitComplex X i) i (unitCycle X i)))
    (hφ : evalUnit K i φ = lerayMap f K i ξ)
    (hη : η = ((DerivedCategory.homologyFunctor _ j).map ((baseSections Y).map
        ((derivedPushforward f).map ψ))).hom (pushClass f (unitComplex X j) j (unitCycle X j)))
    (hψ : evalUnit M j ψ = lerayMap f M j η) :
    lerayMap f (((derivedTensorProductFunctor X.sheaf).obj K).obj M) (i + j)
      (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections Y).map
        (relativeCupProduct f K M))).hom
        ((cupPairing (cupProductOnSpace Y) _ _ i j).hom (ξ ⊗ₜ η))) =
      (cupPairing (cupProductOnSpace X) K M i j).hom
        (lerayMap f K i ξ ⊗ₜ lerayMap f M j η) := by
  subst hξ hη
  exact (lerayCohomologyIso_relativeCupProduct_cupPairing_unit f K M i j φ ψ).trans
    (congrArg (cupPairing (cupProductOnSpace X) K M i j).hom (congrArg₂ (· ⊗ₜ ·) hφ hψ))

/-- **The relative cup product induces the cup product on cohomology.**  For a morphism of
ringed spaces `f : X ⟶ Y`, `K, M ∈ D(𝒪_X)` and classes `ξ ∈ Hⁱ(Y, Rf_*K)`, `η ∈ Hʲ(Y, Rf_*M)`,
the Leray identification `Hⁿ(Y, Rf_*-) ≅ Hⁿ(X, -)` carries `Hⁱ⁺ʲ(RΓ(Y, μ_f))(ξ ∪ η)` — the
cup product on `Y` followed by the relative cup product `μ_f` of Tag 0B68 — to the cup product on
`X` of the images of `ξ` and `η`. -/
theorem lerayCohomologyIso_relativeCupProduct_cupPairing
    (K M : DerivedCategory (SheafOfModules.{u} (structureSheafRing X))) (i j : ℤ)
    (ξ : cohomologyModule ((derivedPushforward f).obj K) i)
    (η : cohomologyModule ((derivedPushforward f).obj M) j) :
    lerayMap f (((derivedTensorProductFunctor X.sheaf).obj K).obj M) (i + j)
      (((DerivedCategory.homologyFunctor _ (i + j)).map ((baseSections Y).map
        (relativeCupProduct f K M))).hom
        ((cupPairing (cupProductOnSpace Y) _ _ i j).hom (ξ ⊗ₜ η))) =
      (cupPairing (cupProductOnSpace X) K M i j).hom
        (lerayMap f K i ξ ⊗ₜ lerayMap f M j η) := by
  have h1 := exists_eq_pushClass f K i ξ
  have h2 := exists_eq_pushClass f M j η
  exact lerayCohomologyIso_relativeCupProduct_cupPairing_of_eq f K M i j ξ η h1.choose h2.choose
    h1.choose_spec.1 h1.choose_spec.2 h2.choose_spec.1 h2.choose_spec.2

end Stacks.Cohomology.LerayCupPairing

end
