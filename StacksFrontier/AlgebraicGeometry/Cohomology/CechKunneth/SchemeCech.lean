module

public import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.HypercohomologyCechComputes
public import StacksFrontier.Topology.Sheaves.Cohomology.CechKunneth.Kunneth
public import StacksFrontier.Topology.Sheaves.Cohomology.CechKunneth.Transport
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCechTransfer
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyFixedCover
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyGlobalScalars

/-!
# The cohomology of a module on a scheme computed by a fixed covering, linearly over a base

Let `X` be a scheme, `φ : k ⟶ Γ(X, 𝒪_X)` a ring map and `ℱ` an `𝒪_X`-module. The sections of `ℱ`
form a presheaf of `k`-modules `Stacks.CechKunneth.sectionsK X φ ℱ` on the opens of `X`, whose
Čech complex for a family `𝒰` of opens is the Čech complex of [Stacks, Tag 01ED]. When the Čech
class map of an open covering `𝒰` is bijective — for instance when `ℱ` is quasi-coherent and the
finite intersections of `𝒰` are affine, by [Stacks, Tag 01XD] — the classes of Čech cocycles give
a `k`-linear isomorphism `Ȟ^p(𝒰, ℱ) ≅ H^p(X, ℱ)`.

## Main definitions

* `Stacks.CechKunneth.sectionsK`: the sections of `ℱ` as a presheaf of `k`-modules.
* `Stacks.CechKunneth.cechToHyper`: the class map `Ȟ^p(𝒰, ℱ) ⟶ H^p(X, ℱ)`.
* `Stacks.CechKunneth.cechEquiv`: the `k`-linear isomorphism, with Mathlib's right derived
  functors of global sections as target.

## Main results

* `Stacks.CechKunneth.bijective_cechToHyper`: the class map is bijective when the Čech class map
  of the covering is.
* `Stacks.CechKunneth.bijective_cechClass_of_isAffineOpen`: the Čech class map of a covering with
  affine finite intersections is bijective, for a quasi-coherent module.

## References

* [Stacks Project, Tag 01XD](https://stacks.math.columbia.edu/tag/01XD)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing abSections)
open Stacks.Cech.Hypercohomology

universe u

namespace Stacks.CechKunneth

attribute [local instance] HasDerivedCategory.standard

variable {k : Type u} [CommRing k] (X : Scheme.{u}) (φ : k →+* Γ(X, ⊤)) (F : X.Modules)

/-- **The sections of an `𝒪_X`-module as a presheaf of `k`-modules**, through
`φ : k ⟶ Γ(X, 𝒪_X)`. -/
def sectionsK : X.Opensᵒᵖ ⥤ ModuleCat.{u} k :=
  (PresheafOfModules.forgetToPresheafModuleCat (op ⊤) (Limits.isTerminalTop).op).obj F.val ⋙
    ModuleCat.restrictScalars φ

/-- The action of `a : k` on a section of `sectionsK` over `V` is multiplication by the
restriction of `φ a` to `V`. -/
theorem sectionsK_smul (V : X.Opens) (x : (sectionsK X φ F).obj (op V)) (a : k) :
    (show Γ(F, V) from a • x) =
      (X.presheaf.map (homOfLE (le_top : V ≤ ⊤)).op).hom (φ a) • (show Γ(F, V) from x) :=
  rfl

variable {I : Type u} (U : I → X.Opens) (hU : ⊤ = ⨆ i, U i)

/-- The Čech differential of `sectionsK` is the Čech differential of the underlying abelian
presheaf. -/
theorem d_sectionsK {p : ℕ} (c : Cochain (sectionsK X φ F) U p) :
    d (sectionsK X φ F) U p c =
      CechCochains.cechD U (abSections (R := ringSheaf X.sheaf) F) p c := by
  funext s
  rw [d_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rfl

/-- The class of a Čech cocycle of `sectionsK`. -/
def classK {p : ℕ} (c : Cochain (sectionsK X φ F) U p) (hc : d (sectionsK X φ F) U p c = 0) :
    hypercohomology X.sheaf (singlePlus X.sheaf F 0) ((p : ℤ) + 0) :=
  cechCocycleClassAt U hU F 0 c ((d_sectionsK X φ F U c).symm.trans hc)

/-- The class of a sum of Čech cocycles is the sum of their classes. -/
theorem classK_add {p : ℕ} (c c' : Cochain (sectionsK X φ F) U p)
    (hc : d (sectionsK X φ F) U p c = 0) (hc' : d (sectionsK X φ F) U p c' = 0) :
    classK X φ F U hU (c + c') (by rw [map_add, hc, hc', add_zero]) =
      classK X φ F U hU c hc + classK X φ F U hU c' hc' :=
  cechCocycleClassAt_add U hU F 0 c c' _ _

/-- The cochain `a • c` is the cochain obtained by multiplying `c` with the global function
`φ(a)`. -/
theorem smul_eq_push {p : ℕ} (a : k) (c : Cochain (sectionsK X φ F) U p) :
    (a • c : Cochain (sectionsK X φ F) U p) =
      Stacks.Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map
        (Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace) (φ a) F)).hom p c :=
  rfl

/-- The class of the cocycle `a • c` is the global function `φ a` times the class of `c`. -/
theorem classK_smul {p : ℕ} (a : k) (c : Cochain (sectionsK X φ F) U p)
    (hc : d (sectionsK X φ F) U p c = 0) :
    classK X φ F U hU (a • c) (by rw [map_smul, hc, smul_zero]) =
      (show SectionRing (ringSheaf X.sheaf) ⊤ from φ a) • classK X φ F U hU c hc := by
  have h := hypercohomologyMap_smulHom_cechCocycleClassAt (X := X.toRingedSpace) (φ a) U hU F 0 c
    ((d_sectionsK X φ F U c).symm.trans hc)
  exact (hypercohomologyMap_cechCocycleClassAt U hU 0
    (Stacks.Cohomology.InvertibleDerived.smulHom (X := X.toRingedSpace) (φ a) F) c _).symm.trans h

/-- **The class map** `Ȟ^p(𝒰, ℱ) ⟶ H^p(X, ℱ)`, linear over `k`. -/
def cechToHyper (p : ℕ) : H (sectionsK X φ F) U p →ₗ[k]
    (ModuleCat.restrictScalars (show k →+* SectionRing (ringSheaf X.sheaf) ⊤ from φ)).obj
      (hypercohomology X.sheaf (singlePlus X.sheaf F 0) ((p : ℤ) + 0)) :=
  Submodule.liftQ _
    { toFun := fun c => classK X φ F U hU c.1 c.2
      map_add' := fun c c' => classK_add X φ F U hU c.1 c'.1 c.2 c'.2
      map_smul' := fun a c => classK_smul X φ F U hU a c.1 c.2 }
    (by
      cases p with
      | zero =>
        intro c hc
        simp only [coboundaries, Submodule.mem_bot] at hc
        subst hc
        exact cechCocycleClassAt_eq_zero_of_eq_zero U hU 0 _ (map_zero _) rfl
      | succ q =>
        rintro ⟨c, hc⟩ ⟨t, rfl⟩
        exact cechCocycleClassAt_eq_zero U hU F 0 t _ ((d_sectionsK X φ F U _).symm.trans hc)
          (d_sectionsK X φ F U t).symm)

/-- The class map sends the Čech cohomology class of a cocycle `c` to `classK c`. -/
theorem cechToHyper_Hmk {p : ℕ} (c : Cochain (sectionsK X φ F) U p)
    (hc : d (sectionsK X φ F) U p c = 0) :
    cechToHyper X φ F U hU p (Hmk _ U c hc) = classK X φ F U hU c hc :=
  rfl

/-- **The class map is bijective** as soon as the Čech class map of the covering is. -/
theorem bijective_cechToHyper (p : ℕ)
    (hb : Function.Bijective (cechClass X.sheaf U hU (singlePlus X.sheaf F 0) ((p : ℤ) + 0))) :
    Function.Bijective (cechToHyper X φ F U hU p) := by
  refine ⟨?_, fun x => ?_⟩
  · rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    obtain ⟨c, hc, rfl⟩ := Hmk_surjective _ U x
    rw [cechToHyper_Hmk] at hx
    cases p with
    | zero =>
      rw [Hmk_eq_zero_iff_zero]
      exact eq_zero_of_cechCocycleClassAt_eq_zero U hU F 0 hb.1 c _ hx
    | succ q =>
      rw [Hmk_eq_zero_iff_succ]
      obtain ⟨t, ht⟩ := exists_cechD_eq_of_cechCocycleClassAt_eq_zero U hU F 0 hb.1 c _ hx
      exact ⟨t, (d_sectionsK X φ F U t).trans ht⟩
  · obtain ⟨c, hc, rfl⟩ := exists_cechCocycleClassAt_eq_of_surjective U hU F 0 p hb.2 x
    exact ⟨Hmk _ U c ((d_sectionsK X φ F U c).trans hc), rfl⟩

/-- **The cohomology of `ℱ` computed by the covering `𝒰`**, as a `k`-linear isomorphism onto
Mathlib's right derived functors of global sections. -/
def cechEquiv (p : ℕ)
    (hb : Function.Bijective (cechClass X.sheaf U hU (singlePlus X.sheaf F 0) ((p : ℤ) + 0))) :
    H (sectionsK X φ F) U p ≃ₗ[k]
      (ModuleCat.restrictScalars φ).obj
        (((_root_.SheafOfModules.evaluation X.ringCatSheaf (op ⊤)).rightDerived p).obj F) :=
  (LinearEquiv.ofBijective _ (bijective_cechToHyper X φ F U hU p hb)).trans
    ((ModuleCat.restrictScalars (show k →+* SectionRing (ringSheaf X.sheaf) ⊤ from φ)).mapIso
      (rightDerivedIsoHypercohomology X F p).symm).toLinearEquiv

/-- **The class of a Čech cocycle is unchanged by refinement** ([Stacks, Tag 01FD]). -/
theorem classK_refCochain {J : Type u} (V : J → X.Opens) (hV : ⊤ = ⨆ j, V j) (r : J → I)
    (hr : ∀ j, V j ≤ U (r j)) {p : ℕ} (c : Cochain (sectionsK X φ F) U p)
    (hc : d (sectionsK X φ F) U p c = 0) :
    classK X φ F V hV (refCochain _ U V r hr p c) (by rw [refCochain_d, hc, map_zero]) =
      classK X φ F U hU c hc :=
  cechCocycleClassAt_refinement U hU F 0 V hV r hr c _

/-- **The comparison isomorphism is compatible with refinement of coverings.** -/
theorem cechEquiv_refCochain {J : Type u} (V : J → X.Opens) (hV : ⊤ = ⨆ j, V j) (r : J → I)
    (hr : ∀ j, V j ≤ U (r j)) {p : ℕ} (hb hb')
    (c : Cochain (sectionsK X φ F) U p) (hc : d (sectionsK X φ F) U p c = 0) :
    cechEquiv X φ F V hV p hb' (Hmk _ V (refCochain _ U V r hr p c)
        (by rw [refCochain_d, hc, map_zero])) = cechEquiv X φ F U hU p hb (Hmk _ U c hc) :=
  congrArg ((ModuleCat.restrictScalars (show k →+* SectionRing (ringSheaf X.sheaf) ⊤ from φ)).mapIso
      (rightDerivedIsoHypercohomology X F p).symm).toLinearEquiv
    (classK_refCochain X φ F U hU V hV r hr c hc)

/-- **A quasi-coherent module placed in degree zero is acyclic on the finite intersections of a
covering whose finite intersections are affine** ([Stacks, Tag 01XB]). -/
theorem isZero_rightDerived_singlePlus_of_isAffineOpen_inter (F : X.Modules) [F.IsQuasicoherent]
    {J : Type u} (V : J → X.Opens)
    (hV : ∀ (r : ℕ) (s : Fin (r + 1) → J), IsAffineOpen (⨅ j, V (s j))) (q : ℤ) (r : ℕ)
    (s : Fin (r + 1) → J) (m : ℕ) (hm : 0 < m) :
    IsZero
      (((_root_.SheafOfModules.evaluation.{u} (ringSheaf X.sheaf) (op (⨅ k, V (s k)))).rightDerived
        m).obj ((singlePlus X.sheaf F 0).1.X q)) := by
  by_cases hq : q = 0
  · subst hq
    exact (Stacks.Cohomology.Cech.isZero_rightDerived_evaluation_of_isZero_hgroup X _ F m
      (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X F _ (hV r s) m hm)).of_iso
      (((_root_.SheafOfModules.evaluation.{u} (ringSheaf X.sheaf) (op (⨅ k, V (s k)))).rightDerived
        m).mapIso (HomologicalComplex.singleObjXSelf (ComplexShape.up ℤ) 0 F))
  · have := Stacks.Cohomology.FlasqueAcyclic.evaluation_additive.{u, u} (ringSheaf X.sheaf)
      (op (⨅ k, V (s k)))
    exact Functor.map_isZero _ (HomologicalComplex.isZero_single_obj_X _ _ _ _ hq)

/-- **The Čech class map of a covering with affine finite intersections is bijective**, for a
quasi-coherent module ([Stacks, Tag 01XD]). -/
theorem bijective_cechClass_of_isAffineOpen (F : X.Modules) [F.IsQuasicoherent]
    (hV : ∀ (r : ℕ) (s : Fin (r + 1) → I), IsAffineOpen (⨅ j, U (s j))) (n : ℤ) :
    Function.Bijective (cechClass X.sheaf U hU (singlePlus X.sheaf F 0) n) :=
  bijective_cechClass_of_acyclic X.sheaf U hU (singlePlus X.sheaf F 0)
    (isZero_rightDerived_singlePlus_of_isAffineOpen_inter X F U hV) n

end Stacks.CechKunneth

end
