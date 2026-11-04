module

public import StacksFrontier.Algebra.Homology.DerivedCategory.RightDerivedCorepresented
public import StacksFrontier.AlgebraicGeometry.DeRham.Gysin.CohomologicalGysinMap

/-!
# Injectivity of a map on cohomology induced by a morphism of the derived category

Let `X` be a ringed space. Derived global sections `RΓ(X, -)` are the total right derived functor
of `Γ(X, -) = Hom(𝒪_X, -)`, so the cohomology `H^n(X, K) = H^n(RΓ(X, K))` of an object `K` of
`D(𝒪_X)` is corepresented by `𝒪_X` placed in degree `n`:
`Hom_{D(𝒪_X)}(𝒪_X[-n], K) ≅ H^n(X, K)`, naturally in `K`.

The consequence used for the Gysin maps of [Stacks, Tag 0G8A]: a morphism
`φ : 𝒜[-c] ⟶ ℱ` of `D(𝒪_X)` induces an injective map `H^0(X, 𝒜) ⟶ H^c(X, ℱ)` as soon as
`v[-c] ≫ φ ≠ 0` for every nonzero `v : 𝒪_X ⟶ 𝒜`. This is how a map on cohomology defined through
the derived category can be shown injective without computing it: the comparison isomorphisms
`cohomologyDerivedSingleIso` it is read through carry no naturality, and none is needed.

## Main results

* `Stacks.DeRham.CohomologicalGysin.exists_bijective_derivedGlobalSections`: the
  corepresentability of `H^n(RΓ(X, -))` by `𝒪_X[-n]`.
* `Stacks.DeRham.CohomologicalGysin.injective_cohomologyMapOfSingleHom`: the injectivity
  criterion for `cohomologyMapOfSingleHom` in degree `0`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite DerivedCategory
  AlgebraicGeometry
open RingedSpaceModuleAdjunction Stacks.Cohomology.SupportedComplexes

namespace Stacks.DeRham.CohomologicalGysin

universe u

-- `derivedGlobalSections` of `CohomologicalGysinMap` takes values in the standard model of
-- `D(Ab)`; the statements below are about that functor, so they are read in the same model.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.RingedSpaceSheafifyOpens.opensHasSheafifyAddCommGrpCat
  Stacks.Topology.RingedSpaceSheafifyOpens.opensWEqualsLocallyBijectiveAddCommGrpCat

attribute [local instance] moduleSheavesHasDerivedCategory

variable (X : RingedSpace.{u, u})

/-- The section `1` of the structure sheaf, as a global section of the free module of rank
one. -/
def unitSection :
    (secF (structureSheafRing X) ⊤).obj (_root_.SheafOfModules.unit (structureSheafRing X)) :=
  (1 : (structureSheafRing X).obj.obj (op ⊤))

/-- A section of a presheaf of modules on the opens of a space is determined by its value on the
whole space, and every value there is attained. -/
theorem bijective_sections_eval_top (M : PresheafOfModules.{u} (structureSheafRing X).obj) :
    Function.Bijective (fun s : M.sections => s.val (op ⊤)) := by
  refine ⟨fun s t h => ?_, fun x₀ => ?_⟩
  · refine PresheafOfModules.sections_ext s t fun U => ?_
    rw [← PresheafOfModules.sections_property s (homOfLE (le_top : U.unop ≤ ⊤)).op,
      ← PresheafOfModules.sections_property t (homOfLE (le_top : U.unop ≤ ⊤)).op]
    exact congrArg _ h
  · let x : M.obj (op ⊤) := x₀
    refine ⟨PresheafOfModules.sectionsMk
      (fun U => M.map (homOfLE (le_top : U.unop ≤ ⊤)).op x) (fun U V f => ?_), ?_⟩
    · rw [← PresheafOfModules.map_comp_apply]
      rfl
    · show M.map (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op x = x
      rw [show (homOfLE (le_top : (⊤ : Opens X) ≤ ⊤)).op = 𝟙 (op ⊤) from rfl,
        PresheafOfModules.map_id]
      rfl

/-- **`Γ(X, -)` is corepresented by `𝒪_X` with universal element `1`.** -/
theorem bijective_secF_map_unitSection (M : _root_.SheafOfModules.{u} (structureSheafRing X)) :
    Function.Bijective (fun f : _root_.SheafOfModules.unit (structureSheafRing X) ⟶ M =>
      (secF (structureSheafRing X) ⊤).map f (unitSection X)) := by
  have h : (fun f : _root_.SheafOfModules.unit (structureSheafRing X) ⟶ M =>
      (secF (structureSheafRing X) ⊤).map f (unitSection X)) =
        (fun s : M.val.sections => s.val (op ⊤)) ∘ M.unitHomEquiv := by
    funext f
    rfl
  rw [h]
  exact (bijective_sections_eval_top X M.val).comp M.unitHomEquiv.bijective

/-- **`H^n(RΓ(X, -))` is corepresented by `𝒪_X[-n]`.** Some `e ∈ H^n(RΓ(X, 𝒪_X[-n]))` makes
`u ↦ H^n(RΓ(u))(e)` a bijection `Hom_{D(𝒪_X)}(𝒪_X[-n], K) ≅ H^n(RΓ(X, K))` for every `K`. -/
theorem exists_bijective_derivedGlobalSections (n : ℤ) :
    ∃ e : (homologyFunctor AddCommGrpCat.{u} n).obj ((derivedGlobalSections X).obj
        ((singleFunctor _ n).obj (_root_.SheafOfModules.unit (structureSheafRing X)))),
      ∀ K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)),
        Function.Bijective (fun u : (singleFunctor _ n).obj
            (_root_.SheafOfModules.unit (structureSheafRing X)) ⟶ K =>
          (homologyFunctor AddCommGrpCat.{u} n).map ((derivedGlobalSections X).map u) e) :=
  Stacks.DerivedFunctor.exists_bijective_homologyFunctor_map_rightDerived
    (secF (structureSheafRing X) ⊤) _ (unitSection X) (derivedGlobalSections X)
    (derivedGlobalSectionsUnit X) n (bijective_secF_map_unitSection X)
    (fun I hI => Stacks.Perfect.CechAugmentation.isIso_app_quotient_obj_of_isKInjective _ _ _
      (exists_isKInjective_quasiIso_moduleSheaves X) I hI)
    (exists_isKInjective_quasiIso_moduleSheaves X)

/-- Derived global sections are additive (indeed triangulated). -/
theorem derivedGlobalSections_map_zero
    {K L : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X))} :
    (derivedGlobalSections X).map (0 : K ⟶ L) = 0 := by
  let := Functor.IsRightDerivedFunctor.commShift (derivedGlobalSections X)
    (derivedGlobalSectionsUnit X)
    (HomotopyCategory.quasiIso (_root_.SheafOfModules.{u} (structureSheafRing X))
      (ComplexShape.up ℤ)) ℤ
  have := Stacks.Perfect.CechAugmentation.isTriangulated_of_isRightDerivedFunctor
    (secF (structureSheafRing X) ⊤) (derivedGlobalSections X) (derivedGlobalSectionsUnit X)
  exact Functor.map_zero _ _ _

/-- **The injectivity criterion, in any degree `d`.** A morphism `φ : 𝒜[-d] ⟶ ℱ` of `D(𝒪_X)`
induces an injective map on `H^d(RΓ(X, -))` as soon as `v[-d] ≫ φ = 0` forces `v = 0` for
`v : 𝒪_X ⟶ 𝒜`. -/
theorem injective_homologyFunctor_map_derivedGlobalSections
    (A F : _root_.SheafOfModules.{u} (structureSheafRing X)) (d m : ℤ) (hdm : d = m)
    (φ : (singleFunctor _ d).obj A ⟶ (singleFunctor _ (0 : ℤ)).obj F)
    (hφ : ∀ v : _root_.SheafOfModules.unit (structureSheafRing X) ⟶ A,
      (singleFunctor _ d).map v ≫ φ = 0 → v = 0) :
    Function.Injective
      ((homologyFunctor AddCommGrpCat.{u} m).map ((derivedGlobalSections X).map φ)) := by
  subst hdm
  obtain ⟨e, he⟩ := exists_bijective_derivedGlobalSections X d
  have hzero : ∀ K : DerivedCategory (_root_.SheafOfModules.{u} (structureSheafRing X)),
      (homologyFunctor AddCommGrpCat.{u} d).map
        ((derivedGlobalSections X).map (0 : (singleFunctor _ d).obj
          (_root_.SheafOfModules.unit (structureSheafRing X)) ⟶ K)) e = 0 := by
    intro K
    rw [derivedGlobalSections_map_zero, Functor.map_zero]
    rfl
  rw [injective_iff_map_eq_zero]
  intro y hy
  obtain ⟨u, rfl⟩ := (he _).2 y
  obtain ⟨v, rfl⟩ := (singleFunctor _ d).map_surjective u
  have h0 : (singleFunctor _ d).map v ≫ φ = 0 := by
    refine (he _).1 ?_
    dsimp only
    rw [hzero, Functor.map_comp, Functor.map_comp, ConcreteCategory.comp_apply]
    exact hy
  rw [hφ v h0, Functor.map_zero]
  exact hzero _

/-- **The injectivity criterion for `cohomologyMapOfSingleHom` in degree `0`.** A morphism
`φ : 𝒜[-c] ⟶ ℱ` of `D(𝒪_X)` induces an injective map `H^0(X, 𝒜) ⟶ H^c(X, ℱ)` as soon as
`v[-c] ≫ φ = 0` forces `v = 0` for every `v : 𝒪_X ⟶ 𝒜`. -/
theorem injective_cohomologyMapOfSingleHom
    (A F : _root_.SheafOfModules.{u} (structureSheafRing X)) (c : ℕ)
    (φ : (singleFunctor _ (c : ℤ)).obj A ⟶ (singleFunctor _ (0 : ℤ)).obj F)
    (hφ : ∀ v : _root_.SheafOfModules.unit (structureSheafRing X) ⟶ A,
      (singleFunctor _ (c : ℤ)).map v ≫ φ = 0 → v = 0) :
    Function.Injective (cohomologyMapOfSingleHom X A F c 0 φ) := by
  have hmid := injective_homologyFunctor_map_derivedGlobalSections X A F (c : ℤ)
    (((0 : ℕ) : ℤ) + (c : ℤ)) (by simp) φ hφ
  intro a b h
  have h' := congrArg (cohomologyDerivedSingleIso X F (0 : ℤ) (((0 : ℕ) : ℤ) + (c : ℤ)) (0 + c)
    (by omega)).inv h
  simp only [cohomologyMapOfSingleHom, ConcreteCategory.comp_apply, Iso.hom_inv_id_apply] at h'
  exact ((ConcreteCategory.bijective_of_isIso
    (cohomologyDerivedSingleIso X A (c : ℤ) (((0 : ℕ) : ℤ) + (c : ℤ)) 0 (by omega)).inv).1)
      (hmid h')

end Stacks.DeRham.CohomologicalGysin
