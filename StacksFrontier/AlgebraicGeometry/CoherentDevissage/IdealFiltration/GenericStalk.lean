module

public import Mathlib.Algebra.Category.Grp.Zero
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.AlgebraicGeometry.FunctionField
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.CategoryTheory.Abelian.CommSq
public import Mathlib.CategoryTheory.Limits.Shapes.Kernels
public import Mathlib.CategoryTheory.Subobject.Lattice
public import Mathlib.Topology.Sheaves.Abelian
public import StacksCore.CategoryTheory.Abelian.Subobject
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocallyFiniteFreeSummand.TensorDualEndomorphism
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafHomSlice
public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.DevissageFiltration
public import StacksFrontier.AlgebraicGeometry.CoherentDevissage.SupportSeparation
public import StacksFrontier.AlgebraicGeometry.Cohomology.Coherent.IdealPowerSupport
public import StacksFrontier.AlgebraicGeometry.IrreducibleDevissage.GenericIdealPushforward
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.Defs
public import StacksFrontier.AlgebraicGeometry.PushforwardCoherent
public import StacksFrontier.AlgebraicGeometry.RegularIdealSheaf.Immersion
public import StacksFrontier.Topology.Noetherian.Defs

/-!
# The defining ideal of a closed immersion kills the generic stalk

Auxiliary results for [Stacks, Tag 01YF]: for an integral closed subscheme `i : Z ⟶ X` with
generic point `η`, the kernel of the stalk map of `i` at `η` is the maximal ideal, every element
of it is the germ of a section of the defining ideal of `i`, and so a module whose sections are
killed by that ideal has its stalk at `i η` killed by the maximal ideal.

## Main results

In the namespace `Stacks.AlgebraicGeometry.CoherentDevissage`:

* `exists_definingIdealOfHom_section_germ_eq_of_stalkMap_eq_zero`: a germ killed by the stalk map
  of a closed immersion is the germ of a section of its defining ideal.
* `stalkKilledByMaximalIdeal_of_definingIdeal_kills_sections`: a module killed by the defining
  ideal of an integral closed subscheme has its generic stalk killed by the maximal ideal.
-/

@[expose] public section

noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.AlgebraicGeometry.DevissageNoetherian (isClosed_supp_of_isCoherent
  isZero_of_supp_eq_empty)
open Stacks.AlgebraicGeometry.IrreducibleDevissage (supp_subset_of_epi)
open Stacks.AlgebraicGeometry.RegularIdealSheaf (kernelSubmodule definingIdealOfHom
  mem_definingIdealOfHom)
open Stacks.SheafOfModules.OnSpace (sheafHom)

universe u

namespace Stacks.AlgebraicGeometry.CoherentDevissage

attribute [local instance_reducible] AlgebraicGeometry.Scheme.Modules

/-! ### The defining ideal of a closed immersion kills the generic stalk -/

/-- A germ killed by the stalk map of a closed immersion `i : Z ⟶ X` is the germ of a section of
the defining ideal of `i`. -/
private theorem exists_definingIdeal_section_germ_of_stalkMap_eq_zero
    {X Z : Scheme.{u}} (i : Z ⟶ X) [IsClosedImmersion i]
    (z : Z) (a : X.presheaf.stalk (i z))
    (ha : (i.stalkMap z).hom a = 0) :
    ∃ (U : X.Opens) (hx : i z ∈ U) (s : Γ(X, U)),
    s ∈ (definingIdealOfHom i).obj (op U) ∧
        X.presheaf.germ U (i z) hx s = a := by
  obtain ⟨U, hxU, s, rfl⟩ := X.presheaf.exists_germ_eq a
  have hxpre : z ∈ i ⁻¹ᵁ U := hxU
  have hzero : Z.presheaf.germ (i ⁻¹ᵁ U) z hxpre (i.app U s) = 0 := by
    simpa [Scheme.Hom.germ_stalkMap_apply] using ha
  obtain ⟨W, w, hzW, hw⟩ :=
    Z.toRingedSpace.exists_res_eq_zero_of_germ_eq_zero (i ⁻¹ᵁ U)
      (i.app U s) ⟨z, hxpre⟩ hzero
  obtain ⟨T, hT, hTW⟩ := i.isClosedEmbedding.isInducing.isOpen_iff.mp W.2
  let V : X.Opens := U ⊓ ⟨T, hT⟩
  have hxV : i z ∈ V := ⟨hxU, by
    change z ∈ i.base ⁻¹' T
    rw [hTW]
    exact hzW⟩
  have hVleU : V ≤ U := inf_le_left
  have hVpre : i ⁻¹ᵁ V ≤ W := by
    intro z' hz'
    change i.base z' ∈ V at hz'
    change z' ∈ W.1
    rw [← hTW]
    exact hz'.2
  let sV := X.presheaf.map (homOfLE hVleU).op s
  have hmapzero : i.appLE V (i ⁻¹ᵁ V) (by simp) sV = 0 := by
    have hnat := i.map_appLE le_rfl (homOfLE hVleU).op
    have heval := ConcreteCategory.congr_hom hnat s
    have hfactor : homOfLE (show i ⁻¹ᵁ V ≤ i ⁻¹ᵁ U from hVpre.trans w.le) =
        homOfLE hVpre ≫ w := Subsingleton.elim _ _
    change i.appLE V (i ⁻¹ᵁ V) (by simp) sV =
      i.appLE U (i ⁻¹ᵁ V) _ s at heval
    rw [heval, Scheme.Hom.appLE, hfactor]
    change Z.presheaf.map (homOfLE hVpre ≫ w).op (i.app U s) = 0
    have hcomp : (homOfLE hVpre ≫ w).op = w.op ≫ (homOfLE hVpre).op := rfl
    rw [hcomp, Functor.map_comp]
    simpa using congrArg (fun t => Z.presheaf.map (homOfLE hVpre).op t) hw
  have hsV : sV ∈ (definingIdealOfHom i).obj (op V) := by
    apply (mem_definingIdealOfHom i V sV).2
    change i.app V sV = 0
    simpa [Scheme.Hom.appLE] using hmapzero
  refine ⟨V, hxV, sV, hsV, ?_⟩
  simp [sV]

/-- **The stalk of the defining ideal of a closed immersion is the kernel of its stalk map.** A
germ of `𝒪_X` at `i z` killed by the stalk map of the closed immersion `i : Z ⟶ X` is the germ of
a section of the defining ideal of `i`. This is what carries an annihilation of sections by the
ideal sheaf to an annihilation of germs. -/
alias exists_definingIdealOfHom_section_germ_eq_of_stalkMap_eq_zero :=
  exists_definingIdeal_section_germ_of_stalkMap_eq_zero

/-- The germ of a product of a section of the structure sheaf with a section of a module is the
product of the germs. -/
private theorem schemeModule_germ_smul {X : Scheme.{u}} (F : X.Modules) (x : X)
    (U : X.Opens) (hx : x ∈ U) (r : Γ(X, U)) (s : Γ(F, U)) :
    (letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) F.val x
     (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf U x hx)) (r • s) =
       (ConcreteCategory.hom (X.presheaf.germ U x hx)) r •
         (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf U x hx)) s) := by
  let : Module (X.presheaf.stalk x)
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val x
  exact PresheafOfModules.germ_smul F.val x U hx r s

/-- At the generic point of an integral closed subscheme `i : Z ⟶ X` the kernel of the stalk map
of `i` is the whole maximal ideal, the stalk of `Z` there being a field. -/
private theorem ker_stalkMap_eq_maximalIdeal
    {X Z : Scheme.{u}} [IsIntegral Z] (i : Z ⟶ X) [IsClosedImmersion i]
    (η : Z) (hη : IsGenericPoint η (Set.univ : Set Z)) :
    RingHom.ker (i.stalkMap η).hom =
      IsLocalRing.maximalIdeal (X.presheaf.stalk (i η)) := by
  let f : X.presheaf.stalk (i η) →+* Z.presheaf.stalk η := (i.stalkMap η).hom
  have hηfield : IsField (Z.presheaf.stalk η) := by
    let : IrreducibleSpace Z := irreducibleSpace_of_isIntegral Z
    rw [hη.eq (genericPoint_spec Z)]
    exact Field.toIsField Z.functionField
  have hbot : (⊥ : Ideal (Z.presheaf.stalk η)).IsMaximal := by
    rw [← IsLocalRing.isField_iff_maximalIdeal_eq.mp hηfield]
    exact IsLocalRing.maximalIdeal.isMaximal _
  have hker : (RingHom.ker f).IsMaximal := by
    change (Ideal.comap f (⊥ : Ideal (Z.presheaf.stalk η))).IsMaximal
    exact Ideal.comap_isMaximal_of_surjective f (i.stalkMap_surjective η) (K := ⊥) (H := hbot)
  exact IsLocalRing.eq_maximalIdeal hker

/-- A module whose sections are killed by the defining ideal of an integral closed subscheme
`i : Z ⟶ X` has its stalk at `i η`, for `η` the generic point of `Z`, killed by the maximal
ideal there: that maximal ideal is the kernel of the stalk map of `i`, and every element of it
is the germ of a section of the defining ideal. -/
theorem stalkKilledByMaximalIdeal_of_definingIdeal_kills_sections
    {X Z : Scheme.{u}} [IsIntegral Z] (i : Z ⟶ X) [IsClosedImmersion i]
    (η : Z) (hη : IsGenericPoint η (Set.univ : Set Z)) (F : X.Modules)
    (hkill : ∀ (U : X.Opens) (_hx : i η ∈ U)
      (r : Γ(X, U)) (s : Γ(F, U)),
      r ∈ (definingIdealOfHom i).obj (op U) → r • s = 0) :
    Stacks.ClosedImmersion.StalkKilledByMaximalIdeal F (i η) := by
  let : Module (X.presheaf.stalk (i η))
      (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf (i η)) :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) F.val (i η)
  intro a ha s
  have ha0 : (i.stalkMap η).hom a = 0 := by
    rwa [← RingHom.mem_ker, ker_stalkMap_eq_maximalIdeal i η hη]
  obtain ⟨U, hxU, r, hrJ, hr⟩ :=
    exists_definingIdeal_section_germ_of_stalkMap_eq_zero i η a ha0
  obtain ⟨V, hxV, t, ht⟩ := TopCat.Presheaf.exists_germ_eq F.val.presheaf s
  let W : X.Opens := U ⊓ V
  have hxW : i η ∈ W := ⟨hxU, hxV⟩
  let iU : W ⟶ U := homOfLE inf_le_left
  let iV : W ⟶ V := homOfLE inf_le_right
  let rW := X.presheaf.map iU.op r
  let tW := F.val.presheaf.map iV.op t
  have hrW : (ConcreteCategory.hom (X.presheaf.germ W (i η) hxW)) rW = a := by
    dsimp [rW]
    rwa [TopCat.Presheaf.germ_res_apply X.presheaf iU (i η) hxW r]
  have htW : (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf W (i η) hxW)) tW = s := by
    dsimp [tW]
    exact (TopCat.Presheaf.germ_res_apply F.val.presheaf iV (i η) hxW t).trans ht
  have hrWJ : rW ∈ (definingIdealOfHom i).obj (op W) :=
    (definingIdealOfHom i).map iU.op hrJ
  let : Module Γ(X, W) Γ(F, W) := (F.val.obj (op W)).isModule
  have hz := hkill W hxW (show Γ(X, W) from rW) (show Γ(F, W) from tW) hrWJ
  calc
    a • s = (ConcreteCategory.hom (X.presheaf.germ W (i η) hxW)) rW •
        (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf W (i η) hxW)) tW := by
          rw [hrW, htW]
    _ = (ConcreteCategory.hom
        (TopCat.Presheaf.germ F.val.presheaf W (i η) hxW))
          (show Γ(F, W) from (show Γ(X, W) from rW) • (show Γ(F, W) from tW)) :=
          (schemeModule_germ_smul F (i η) W hxW
            (show Γ(X, W) from rW) (show Γ(F, W) from tW)).symm
    _ = 0 :=
      (congrArg (ConcreteCategory.hom (TopCat.Presheaf.germ F.val.presheaf W (i η) hxW)) hz).trans
        (map_zero _)

end Stacks.AlgebraicGeometry.CoherentDevissage

end

end
