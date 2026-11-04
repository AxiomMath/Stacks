module

public import Mathlib.CategoryTheory.Linear.Yoneda
public import Mathlib.CategoryTheory.ObjectProperty.FullSubcategory
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.RingTheory.CohenMacaulay.Defs
public import StacksFrontier.RingTheory.CohenMacaulay.Module
public import StacksFrontier.RingTheory.Dualizing.CohenMacaulayCriterion
public import StacksFrontier.RingTheory.Dualizing.DepthFromExt
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.Duality
public import StacksFrontier.RingTheory.Dualizing.DerivedHomDuality.ExtComparison
public import StacksFrontier.RingTheory.Dualizing.DualizingDerivedHom
public import StacksFrontier.RingTheory.Dualizing.ExtCompletionComparison
public import StacksFrontier.RingTheory.Dualizing.Normalized

/-!
# Duality on Cohen--Macaulay modules of fixed depth

Let `A` be a Noetherian local ring with a normalized dualizing complex `ω_A`, and fix a natural
number `d`. For a finite Cohen--Macaulay `A`-module `M` of depth `d`, the complex
`RHom_A(M, ω_A)` is concentrated in degree `-d`, so it is the single module `Ext^{-d}_A(M, ω_A)`
placed there. Biduality on objects with finite cohomology then turns `M ↦ Ext^{-d}_A(M, ω_A)`
into an anti-autoequivalence of the category of finite Cohen--Macaulay `A`-modules of depth `d`.

## Main definitions

* `Dualizing.IsCohenMacaulayModuleOfDepth` — the property of being a finite Cohen--Macaulay
  module of a fixed depth.
* `Dualizing.CohenMacaulayModulesOfDepth` — the full category these modules span.
* `Dualizing.extIntoDualizingComplex` — the contravariant functor `M ↦ Ext^{-d}_A(M, ω_A)`.

## Main results

* `Dualizing.cohenMacaulayExtDuality` — the anti-autoequivalence of the category of finite
  Cohen--Macaulay modules of depth `d`.
* `Dualizing.cohenMacaulayExtDuality_forget` — its underlying functor is naturally the
  contravariant `Ext^{-d}` functor, so the equivalence is the one the source asserts rather than
  an abstract equivalence of the two categories.

## Implementation notes

An anti-autoequivalence is represented as an equivalence out of the opposite category. Morphisms
in the derived category of `max u v`-small modules live in a higher universe, so `Ext` does too
and the codomain of the equivalence is the universe-enlarged copy of the same full category; the
two copies are identified by universe lifting, which is essentially surjective because a finite
module admits a model in the universe of the ring. The third universe `w` is used only by that
small-model lemma.

The comparison of `Ext^i_A(K, ω)` with `H^i(RHom_A(K, ω))` is `Dualizing.extDerivedHomLinearEquiv`,
which holds for an arbitrary object `K` of the derived category — in particular for a module
placed in a nonzero degree — and needs no hypothesis on `ω`. Its natural form, used to identify
the underlying functor of the equivalence, is `Dualizing.extIntoOmegaAtIso` at degree `-d`.

## References

* [Stacks Project, Tag 0B5A](https://stacks.math.columbia.edu/tag/0B5A)
-/

@[expose] public section

open CategoryTheory

attribute [local instance] HasDerivedCategory.standard

universe u v w

namespace Dualizing

/-- A finite module in a larger universe is the universe lift of a module in the universe of the
ring, namely of a quotient of a finite free module. -/
private theorem exists_small_model_of_finite
    {A : Type u} [CommRing A]
    {M : Type (max w u)} [AddCommGroup M] [Module A M] [Module.Finite A M] :
    ∃ N : ModuleCat.{u} A,
      Nonempty ((ModuleCat.uliftFunctor.{w, u} A).obj N ≅ ModuleCat.of A M) := by
  obtain ⟨n, f, hf⟩ := Module.Finite.exists_fin' A M
  let Q : ModuleCat.{u} A := ModuleCat.of A ((Fin n → A) ⧸ LinearMap.ker f)
  let e : (ULift.{w, u} ((Fin n → A) ⧸ LinearMap.ker f)) ≃ₗ[A] M :=
    ULift.moduleEquiv.trans (LinearMap.quotKerEquivOfSurjective f hf)
  exact ⟨Q, ⟨e.toModuleIso⟩⟩

/-- Cohen--Macaulayness at the maximal ideal transports along a linear equivalence of finite
modules: depth and support dimension are both invariant. -/
private theorem isCohenMacaulayAtMaximalIdeal_iff_of_linearEquiv
    {A : Type u} [CommRing A] [IsLocalRing A]
    {M N : Type*} [AddCommGroup M] [Module A M] [Module.Finite A M]
    [AddCommGroup N] [Module A N] [Module.Finite A N] (e : M ≃ₗ[A] N) :
    Module.IsCohenMacaulayAtMaximalIdeal A M ↔
      Module.IsCohenMacaulayAtMaximalIdeal A N := by
  unfold Module.IsCohenMacaulayAtMaximalIdeal
  rw [Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal A) e,
    supportDim_eq_of_linearEquiv e]

/-- A module whose depth at the maximal ideal is a natural number is nonzero, the zero module
having depth `⊤`. -/
private theorem nontrivial_of_depth_eq_nat
    {A : Type u} [CommRing A] [IsLocalRing A]
    {M : Type (max u v)} [AddCommGroup M] [Module A M]
    (d : ℕ) (h : Module.depth A (IsLocalRing.maximalIdeal A) M = (d : ℕ∞)) :
    Nontrivial M := by
  by_contra hnt
  have : Subsingleton M := not_nontrivial_iff_subsingleton.mp hnt
  have htopM : (⊤ : Submodule A M) = ⊥ :=
    Submodule.eq_bot_of_subsingleton (p := (⊤ : Submodule A M))
  have htop : IsLocalRing.maximalIdeal A • (⊤ : Submodule A M) = ⊤ := by
    rw [htopM]
    simp
  simp [Module.depth, htop] at h

/-- For a nonzero finite Cohen--Macaulay module of depth `d`, `Ext^i` into a normalized dualizing
complex vanishes in every degree `i ≠ -d`. -/
private theorem ext_subsingleton_off_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max u v)} [AddCommGroup M] [Module A M]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega)
    (d : ℕ) (hcm : Module.Finite A M ∧
      Module.IsCohenMacaulayAtMaximalIdeal A M ∧
      Module.depth A (IsLocalRing.maximalIdeal A) M = (d : ℕ∞))
    (hnt : Nontrivial M) (i : ℤ) (hi : i ≠ -(d : ℤ)) :
    Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        (ModuleCat.of A M)) omega i) := by
  let : Nontrivial M := hnt
  rcases hcm with ⟨_, hcm, hdepth⟩
  have hdim : Module.supportDim A M = ((d : ℕ∞) : WithBot ℕ∞) := by
    change (Module.depth A (IsLocalRing.maximalIdeal A) M : WithBot ℕ∞) = _ at hcm
    rw [hdepth] at hcm
    exact hcm.symm
  have hthird :=
    ((isCohenMacaulay_iff_ext_concentrated (A := A) (M := M) omega homega).out 1 3).mp hcm
  have hnot : ¬ (0 ≤ -i ∧ Module.supportDim A M =
      (((-i).toNat : ℕ∞) : WithBot ℕ∞)) := by
    intro hdeg
    have hcast : d = (-i).toNat := by
      apply_mod_cast hdim.symm.trans hdeg.2
    have hEq : (d : ℤ) = -i := by
      simpa [hcast] using (Int.toNat_of_nonneg hdeg.1)
    exact hi (by omega)
  simpa using hthird (-i) hnot

/-- The cohomology of `RHom_A(M, ω)` vanishes outside degree `-d` for a nonzero finite
Cohen--Macaulay module of depth `d`, that cohomology being `Ext^i_A(M, ω)`. -/
private theorem dualizingHomology_isZero_off_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max u v)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega)
    (d : ℕ) (hcm : Module.Finite A M ∧
      Module.IsCohenMacaulayAtMaximalIdeal A M ∧
      Module.depth A (IsLocalRing.maximalIdeal A) M = (d : ℕ∞))
    (hnt : Nontrivial M) (i : ℤ) (hi : i ≠ -(d : ℤ)) :
    CategoryTheory.Limits.IsZero
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) i).obj
      ((dualizingDerivedHomFunctor A omega).obj
        (.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A M))))) := by
  let : Subsingleton (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        (ModuleCat.of A M)) omega i) :=
    ext_subsingleton_off_depth omega homega d hcm hnt i hi
  exact ModuleCat.isZero_iff_subsingleton.mpr
    (Equiv.subsingleton.symm (extDerivedHomLinearEquiv A omega i
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        (ModuleCat.of A M))).toEquiv)

/-- `RHom_A(M, ω)` is bounded below by `-d` for a nonzero finite Cohen--Macaulay module of
depth `d`. -/
private theorem dualizingHom_isGE_of_cm_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max u v)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega)
    (d : ℕ) (hcm : Module.Finite A M ∧
      Module.IsCohenMacaulayAtMaximalIdeal A M ∧
      Module.depth A (IsLocalRing.maximalIdeal A) M = (d : ℕ∞))
    (hnt : Nontrivial M) :
    ((dualizingDerivedHomFunctor A omega).obj
      (.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        (ModuleCat.of A M)))).IsGE (-(d : ℤ)) := by
  rw [DerivedCategory.isGE_iff]
  intro i hi
  exact dualizingHomology_isZero_off_depth omega homega d hcm hnt i (by omega)

/-- `RHom_A(M, ω)` is bounded above by `-d` for a nonzero finite Cohen--Macaulay module of
depth `d`. -/
private theorem dualizingHom_isLE_of_cm_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max u v)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega)
    (d : ℕ) (hcm : Module.Finite A M ∧
      Module.IsCohenMacaulayAtMaximalIdeal A M ∧
      Module.depth A (IsLocalRing.maximalIdeal A) M = (d : ℕ∞))
    (hnt : Nontrivial M) :
    ((dualizingDerivedHomFunctor A omega).obj
      (.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        (ModuleCat.of A M)))).IsLE (-(d : ℤ)) := by
  rw [DerivedCategory.isLE_iff]
  intro i hi
  exact dualizingHomology_isZero_off_depth omega homega d hcm hnt i (by omega)

/-- A complex isomorphic to a module `H` placed in degree `n` has degree `n` cohomology `H`. -/
private noncomputable def homologyIsoOfIsoSingle
    {A : Type u} [CommRing A] {K : DerivedCategory (ModuleCat.{max u v} A)}
    {H : ModuleCat.{max u v} A} {n : ℤ}
    (e : K ≅ (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) n).obj H) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj K ≅ H :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).mapIso e ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} A) n).app H

/-- The isomorphism of a complex `K` with its degree `n` cohomology placed in degree `n`, induced by
an isomorphism of `K` with some module placed in degree `n`. -/
private noncomputable def isoSingleHomology
    {A : Type u} [CommRing A] {K : DerivedCategory (ModuleCat.{max u v} A)}
    {H : ModuleCat.{max u v} A} {n : ℤ}
    (e : K ≅ (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) n).obj H) :
    K ≅ (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) n).obj
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj K) :=
  e ≪≫ (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) n).mapIso
    (homologyIsoOfIsoSingle e).symm

/-- On the degree `n` cohomology of `K`, the comparison of `single ⋙ homology` with the identity is
the inverse of the map induced by `isoSingleHomology`. -/
private theorem singleFunctorCompHomologyFunctorIso_hom_app_eq
    {A : Type u} [CommRing A] {K : DerivedCategory (ModuleCat.{max u v} A)}
    {H : ModuleCat.{max u v} A} {n : ℤ}
    (e : K ≅ (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) n).obj H) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso (ModuleCat.{max u v} A) n).hom.app
        ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).obj K) =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map
        (isoSingleHomology e).inv := by
  have hNat := (DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{max u v} A) n).hom.naturality (homologyIsoOfIsoSingle e).inv
  rw [← cancel_epi ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map
    (isoSingleHomology e).hom), ← Functor.map_comp, Iso.hom_inv_id, CategoryTheory.Functor.map_id]
  simp only [isoSingleHomology, Iso.trans_hom, Functor.map_comp, Category.assoc]
  dsimp at hNat ⊢
  rw [hNat, ← Category.assoc]
  exact (homologyIsoOfIsoSingle e).hom_inv_id

/-- A finite module placed in degree zero is isomorphic to its double dual
`RHom_A(RHom_A(M, ω), ω)`, by biduality on objects with finite cohomology. -/
private noncomputable def singleBidualIso
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega)
    (M : ModuleCat.{max u v} A) [Module.Finite A M] :
    (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M ≅
      (dualizingDerivedHomFunctor A omega).obj (.op ((dualizingDerivedHomFunctor A omega).obj
        (.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj M)))) :=
  (ObjectProperty.ι _).mapIso ((coherentDerivedBidualityIso A omega homega.1).app
    ⟨_, finiteCohomology_single A M⟩)

/-- The property of being finite, Cohen--Macaulay and of depth `d` transports along a linear
equivalence. -/
private theorem finite_isCohenMacaulay_depth_of_linearEquiv
    {A : Type u} [CommRing A] [IsLocalRing A] {M N : Type*}
    [AddCommGroup M] [Module A M] [AddCommGroup N] [Module A N] {d : ℕ} (e : M ≃ₗ[A] N)
    (h : Module.Finite A N ∧ Module.IsCohenMacaulayAtMaximalIdeal A N ∧
      Module.depth A (IsLocalRing.maximalIdeal A) N = (d : ℕ∞)) :
    Module.Finite A M ∧ Module.IsCohenMacaulayAtMaximalIdeal A M ∧
      Module.depth A (IsLocalRing.maximalIdeal A) M = (d : ℕ∞) := by
  have hfin : Module.Finite A M := (Module.Finite.equiv_iff e).mpr h.1
  have := h.1
  exact ⟨hfin, (isCohenMacaulayAtMaximalIdeal_iff_of_linearEquiv e).mpr h.2.1,
    (Module.depth_eq_depth_of_linearEquiv (IsLocalRing.maximalIdeal A) e).trans h.2.2⟩

/-- For a nonzero finite Cohen--Macaulay module `M` of depth `d`, the complex `RHom_A(M, ω)` is
isomorphic to a finite module placed in degree `-d`. -/
private theorem exists_dualizing_homology_iso_single
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max u v)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega)
    (d : ℕ) (hcm : Module.Finite A M ∧
      Module.IsCohenMacaulayAtMaximalIdeal A M ∧
      Module.depth A (IsLocalRing.maximalIdeal A) M = (d : ℕ∞))
    (hnt : Nontrivial M) :
    ∃ H : ModuleCat.{max u v} A,
      Module.Finite A H ∧ Nonempty (((dualizingDerivedHomFunctor A omega).obj
        (.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A M)))) ≅
        (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).obj H) := by
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
    (ModuleCat.of A M)
  have hX := finiteCohomology_single A (ModuleCat.of A M)
  have hfinite := dualizingDerivedHom_finiteCohomology A omega homega.1 X hX
  let D := (dualizingDerivedHomFunctor A omega).obj (.op X)
  let : D.IsGE (-(d : ℤ)) := dualizingHom_isGE_of_cm_depth omega homega d hcm hnt
  let : D.IsLE (-(d : ℤ)) := dualizingHom_isLE_of_cm_depth omega homega d hcm hnt
  obtain ⟨H, ⟨e⟩⟩ :=
    DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE D (-(d : ℤ))
  refine ⟨H, ?_, ⟨e⟩⟩
  exact (Module.Finite.equiv_iff (homologyIsoOfIsoSingle e).toLinearEquiv).mp
    (hfinite (-(d : ℤ)))

/-- The degree `-d` cohomology of `RHom_A(M, ω)` is nonzero for a nonzero finite Cohen--Macaulay
module of depth `d`, since otherwise biduality would force `M` to vanish. -/
private theorem dualizingHomology_nontrivial_of_cm_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max u v)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega)
    (d : ℕ) (hcm : Module.Finite A M ∧
      Module.IsCohenMacaulayAtMaximalIdeal A M ∧
      Module.depth A (IsLocalRing.maximalIdeal A) M = (d : ℕ∞))
    (hnt : Nontrivial M) :
    Nontrivial ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).obj
      ((dualizingDerivedHomFunctor A omega).obj
        (.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A M))))) := by
  obtain ⟨H, hHfin, ⟨e⟩⟩ :=
    exists_dualizing_homology_iso_single omega homega d hcm hnt
  by_contra hnot
  have hDsub : Subsingleton
      ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).obj
        ((dualizingDerivedHomFunctor A omega).obj
          (.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
            (ModuleCat.of A M))))) := not_nontrivial_iff_subsingleton.mp hnot
  have hH : Subsingleton H := ⟨fun x y => by
    apply (homologyIsoOfIsoSingle e).toLinearEquiv.symm.injective
    exact Subsingleton.elim _ _⟩
  have hSingle : CategoryTheory.Limits.IsZero
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).obj H) :=
    (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).map_isZero
      (ModuleCat.isZero_iff_subsingleton.mpr hH)
  have hD : CategoryTheory.Limits.IsZero
      ((dualizingDerivedHomFunctor A omega).obj
        (.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A M)))) := hSingle.of_iso e
  let X : CoherentDerivedCategory A :=
    ⟨(DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj (ModuleCat.of A M),
      finiteCohomology_single A (ModuleCat.of A M)⟩
  let F := coherentDualizingDerivedHomFunctor A omega homega.1
  let : F.IsEquivalence := coherentDualizingDerivedHom_isEquivalence A omega homega.1
  have hFX : CategoryTheory.Limits.IsZero (F.obj (Opposite.op X)) :=
    CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero
      (ObjectProperty.ι _) (F.obj (Opposite.op X)) hD
  have hXop : CategoryTheory.Limits.IsZero (Opposite.op X) :=
    CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero F (Opposite.op X) hFX
  have hX : CategoryTheory.Limits.IsZero X := hXop.unop
  have hSX : CategoryTheory.Limits.IsZero X.obj := (ObjectProperty.ι _).map_isZero hX
  have hMzero : CategoryTheory.Limits.IsZero (ModuleCat.of A M) :=
    CategoryTheory.Limits.IsZero.of_full_of_faithful_of_isZero
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0)
      (ModuleCat.of A M) hSX
  exact (not_nontrivial_iff_subsingleton.mpr (ModuleCat.isZero_iff_subsingleton.mp hMzero)) hnt

/-- `Ext^i` out of a module placed in degree `-d` is `Ext^{i-d}` out of the same module placed in
degree zero, by the adjunction between the shifts. -/
private noncomputable def extShiftedSourceLinearEquiv
    {A : Type u} [CommRing A]
    (E : Type (max u v)) [AddCommGroup E] [Module A E]
    (omega : DerivedCategory (ModuleCat.{max u v} A)) (d : ℕ) (i : ℤ) :
    DerivedCategory.Ext
        (DerivedCategory.Q.obj
          ((CochainComplex.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).obj
            (ModuleCat.of A E))) omega i ≃ₗ[A]
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj (ModuleCat.of A E))
        omega (i - (d : ℤ)) := by
  let eSrc := (DerivedCategory.singleFunctors (ModuleCat.{max u v} A)).shiftIso
      (d : ℤ) (-(d : ℤ)) 0 (by simp)
  let X0 := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
    (ModuleCat.of A E)
  let Xd := DerivedCategory.Q.obj
    ((CochainComplex.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).obj
      (ModuleCat.of A E))
  have hsource : Xd = (DerivedCategory.singleFunctor
      (ModuleCat.{max u v} A) (-(d : ℤ))).obj (ModuleCat.of A E) := rfl
  let e0Lin : DerivedCategory.Ext Xd omega i ≃ₗ[A]
      (Xd ⟶ (shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj omega) :=
    LinearEquiv.refl A _
  let e1Lin : (Xd ⟶ (shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj omega) ≃ₗ[A]
      ((shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) (d : ℤ)).obj X0 ⟶
        (shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj omega) :=
    CategoryTheory.Linear.homCongr A
      ((eqToIso hsource) ≪≫ (eSrc.app (ModuleCat.of A E)).symm) (Iso.refl _)
  let adj := shiftEquiv (DerivedCategory (ModuleCat.{max u v} A)) (d : ℤ)
  letI : adj.functor.Additive := by
    change (shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) (d : ℤ)).Additive
    infer_instance
  let adj' := adj.toAdjunction
  letI : adj.inverse.Linear A := by
    change (shiftFunctor (DerivedCategory (ModuleCat.{max u v} A))
      (-(d : ℤ))).Linear A
    infer_instance
  let Y := (shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) i).obj omega
  let e2 : (((shiftFunctor (DerivedCategory (ModuleCat.{max u v} A))
      (d : ℤ)).obj X0) ⟶ Y) ≃+ (X0 ⟶
        (shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) (-(d : ℤ))).obj Y) :=
    CategoryTheory.Adjunction.homAddEquiv (adj := adj') X0 Y
  let e2Lin : (((shiftFunctor (DerivedCategory (ModuleCat.{max u v} A))
      (d : ℤ)).obj X0) ⟶ Y) ≃ₗ[A] (X0 ⟶
        (shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) (-(d : ℤ))).obj Y) :=
    e2.toLinearEquiv (by
      intro a f
      let f' : adj.functor.obj X0 ⟶ Y := f
      change adj'.homAddEquiv X0 Y (a • f') = a • adj'.homAddEquiv X0 Y f'
      change adj'.homEquiv X0 Y (a • f') = a • adj'.homEquiv X0 Y f'
      rw [CategoryTheory.Adjunction.homEquiv_apply,
        CategoryTheory.Adjunction.homEquiv_apply]
      simp only [Functor.map_smul, Linear.comp_smul])
  let eK : ((shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) (-(d : ℤ))).obj Y) ≅
      (shiftFunctor (DerivedCategory (ModuleCat.{max u v} A)) (i - (d : ℤ))).obj omega :=
    (shiftFunctorAdd' (DerivedCategory (ModuleCat.{max u v} A)) i (-(d : ℤ))
      (i - (d : ℤ)) (by ring)).symm.app omega
  let e3Lin : (X0 ⟶ (shiftFunctor (DerivedCategory (ModuleCat.{max u v} A))
      (-(d : ℤ))).obj Y) ≃ₗ[A] (X0 ⟶
        (shiftFunctor (DerivedCategory (ModuleCat.{max u v} A))
          (i - (d : ℤ))).obj omega) :=
    CategoryTheory.Linear.homCongr A (Iso.refl _) eK
  let e4Lin : DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj (ModuleCat.of A E))
      omega (i - (d : ℤ)) ≃ₗ[A] (X0 ⟶
        (shiftFunctor (DerivedCategory (ModuleCat.{max u v} A))
          (i - (d : ℤ))).obj omega) := LinearEquiv.refl A _
  exact e0Lin.trans (e1Lin.trans (e2Lin.trans (e3Lin.trans e4Lin.symm)))

/-- The module `Ext^{-d}_A(M, ω)`, taken in the universe of the derived category as the degree
`-d` cohomology of `RHom_A(M, ω)`. -/
private noncomputable abbrev dualModuleOf
    {A : Type u} [CommRing A] {M : Type (max u v)}
    [AddCommGroup M] [Module A M]
    (omega : DerivedCategory (ModuleCat.{max u v} A)) (d : ℕ) :
    ModuleCat.{max u v} A :=
  (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).obj
    ((dualizingDerivedHomFunctor A omega).obj
      (.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        (ModuleCat.of A M))))

/-- The degree zero cohomology of `RHom_A(E[d], ω)` is `Ext^{-d}_A(E, ω)`, by shifting the source
back to degree zero. -/
private noncomputable def shiftedDualHomologyLinearEquiv
    {A : Type u} [CommRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (E : Type (max u v)) [AddCommGroup E] [Module A E] (d : ℕ) :
    (((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).obj
      ((dualizingDerivedHomFunctor A omega).obj
        (.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).obj
          (ModuleCat.of A E))))) : Type (max u v)) ≃ₗ[A]
      dualModuleOf (M := E) omega d := by
  let Ld := (CochainComplex.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).obj
    (ModuleCat.of A E)
  let L0 := (CochainComplex.singleFunctor (ModuleCat.{max u v} A) 0).obj
    (ModuleCat.of A E)
  let e0 := extDerivedHomLinearEquiv A omega 0 (DerivedCategory.Q.obj Ld)
  let e1 := extDerivedHomLinearEquiv A omega (-(d : ℤ)) (DerivedCategory.Q.obj L0)
  let es := extShiftedSourceLinearEquiv (A := A) E omega d 0
  have es' : DerivedCategory.Ext
      (DerivedCategory.Q.obj Ld) omega 0 ≃ₗ[A]
      DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj (ModuleCat.of A E))
        omega (-(d : ℤ)) := by
    have hdeg : (0 : ℤ) - (d : ℤ) = -(d : ℤ) := by omega
    exact Eq.mp (congrArg (fun j : ℤ =>
      DerivedCategory.Ext (DerivedCategory.Q.obj Ld) omega 0 ≃ₗ[A]
        DerivedCategory.Ext
          ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
            (ModuleCat.of A E)) omega j) hdeg) (by simpa [Ld] using es)
  exact e0.symm.trans (es'.trans e1)

/-- For a nonzero finite Cohen--Macaulay module `M` of depth `d`, the module `Ext^{-d}_A(M, ω)` is
again Cohen--Macaulay of depth `d`. -/
private theorem dualizingHomology_isCM_and_depth
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max u v)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega)
    (d : ℕ) (hcm : Module.Finite A M ∧
      Module.IsCohenMacaulayAtMaximalIdeal A M ∧
      Module.depth A (IsLocalRing.maximalIdeal A) M = (d : ℕ∞))
    (hnt : Nontrivial M) :
    Module.IsCohenMacaulayAtMaximalIdeal A (dualModuleOf (M := M) omega d) ∧
    Module.depth A (IsLocalRing.maximalIdeal A) (dualModuleOf (M := M) omega d) = (d : ℕ∞) := by
  obtain ⟨H, hHfin, ⟨eD⟩⟩ :=
    exists_dualizing_homology_iso_single omega homega d hcm hnt
  let : Module.Finite A H := hHfin
  let X := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
    (ModuleCat.of A M)
  let S := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).obj H
  let eHmod := homologyIsoOfIsoSingle eD
  let : Module.Finite A (dualModuleOf (M := M) omega d) :=
    (Module.Finite.equiv_iff eHmod.toLinearEquiv).mpr hHfin
  have hDualne : Nontrivial (dualModuleOf (M := M) omega d) :=
    dualizingHomology_nontrivial_of_cm_depth omega homega d hcm hnt
  have hHne : Nontrivial H := by
    simpa using (Equiv.nontrivial_congr eHmod.toLinearEquiv.toEquiv).mp hDualne
  let F := dualizingDerivedHomFunctor A omega
  have eHdual : F.obj (.op S) ≅ X :=
    F.mapIso eD.op ≪≫ (singleBidualIso omega homega (ModuleCat.of A M)).symm
  let L := (CochainComplex.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).obj H
  have hcohIso : ∀ m : ℤ, ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) m).obj
      (F.obj (.op S))) ≃ ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) m).obj X) :=
    fun m => ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) m).mapIso
      eHdual).toLinearEquiv.toEquiv
  have hExtEquiv : ∀ n : ℤ, Nonempty (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj (ModuleCat.of A H)) omega n ≃
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (n + (d : ℤ))).obj
        (F.obj (.op S))) := fun n => by
    have e := extShiftedSourceLinearEquiv (A := A) H omega d (n + (d : ℤ))
    rw [add_sub_cancel_right] at e
    exact ⟨e.symm.toEquiv.trans
      (extDerivedHomLinearEquiv A omega (n + (d : ℤ)) (DerivedCategory.Q.obj L)).toEquiv⟩
  have hUnique : ∀ i j : ℤ,
      Nontrivial (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A H)) omega i) →
      Nontrivial (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A H)) omega j) → i = j := by
    have hforced : ∀ n : ℤ, Nontrivial (DerivedCategory.Ext
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A H)) omega n) → n = -(d : ℤ) := by
      intro n hn
      by_contra hne
      have hdegree : n + (d : ℤ) ≠ 0 := fun h => hne (by omega)
      have hzero : CategoryTheory.Limits.IsZero
          ((DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (n + (d : ℤ))).obj X) := by
        rcases lt_or_gt_of_ne hdegree with hlt | hgt
        · exact DerivedCategory.isZero_of_isGE X 0 (n + (d : ℤ)) hlt
        · exact DerivedCategory.isZero_of_isLE X 0 (n + (d : ℤ)) hgt
      have hsub := (Equiv.subsingleton_congr (hExtEquiv n).some).mpr
        ((Equiv.subsingleton_congr (hcohIso _)).mpr (ModuleCat.isZero_iff_subsingleton.mp hzero))
      exact (not_subsingleton_iff_nontrivial.mpr hn) hsub
    intro i j hi hj
    exact (hforced i hi).trans (hforced j hj).symm
  have hExtd : Nontrivial (DerivedCategory.Ext
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        (ModuleCat.of A H)) omega (-(d : ℤ))) := by
    refine (Equiv.nontrivial_congr (hExtEquiv _).some).mpr ?_
    rw [neg_add_cancel]
    refine (Equiv.nontrivial_congr (hcohIso 0)).mpr ?_
    exact (Equiv.nontrivial_congr ((DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{max u v} A) 0).app (ModuleCat.of A M)).toLinearEquiv.toEquiv).mpr hnt
  have hCM := ((isCohenMacaulay_iff_ext_concentrated
      (A := A) (M := H) omega homega).out 2 1).mp hUnique
  have ⟨delta, hleast, hdepth⟩ :=
    depth_eq_least_nonzero_negative_ext (M := H) omega homega hHne
  have hdelta : delta = d := by
    have hd' := hUnique (-(delta : ℤ)) (-(d : ℤ)) hleast.1 hExtd
    omega
  exact (finite_isCohenMacaulay_depth_of_linearEquiv eHmod.toLinearEquiv
    ⟨hHfin, hCM, by simpa [hdelta] using hdepth⟩).2

/-- The property of being a finite Cohen--Macaulay `A`-module of depth `d`. -/
public abbrev IsCohenMacaulayModuleOfDepth
    (A : Type u) [CommRing A] [IsLocalRing A] (d : ℕ) :
    ObjectProperty (ModuleCat.{v} A) := fun M ↦
  Module.Finite A M ∧ Module.IsCohenMacaulayAtMaximalIdeal A M ∧
    Module.depth A (IsLocalRing.maximalIdeal A) M = (d : ℕ∞)

/-- The full category of finite Cohen--Macaulay `A`-modules having depth `d`. -/
public abbrev CohenMacaulayModulesOfDepth
    (A : Type u) [CommRing A] [IsLocalRing A] (d : ℕ) :=
  (IsCohenMacaulayModuleOfDepth.{u, v} A d).FullSubcategory

/-- The contravariant functor `M ↦ Ext^{-d}_A(M, ω)` on finite Cohen--Macaulay modules of
depth `d`, realized through the degree `-d` cohomology of `RHom_A(M, ω)`. -/
private noncomputable def cmHomologyFunctor
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega) (d : ℕ) :
    (CohenMacaulayModulesOfDepth.{u, max u v} A d)ᵒᵖ ⥤
      CohenMacaulayModulesOfDepth.{u, max u v} A d where
  obj X := by
    let M := X.unop.obj
    letI : Module.Finite A M := X.unop.property.1
    have hnt := nontrivial_of_depth_eq_nat d X.unop.property.2.2
    let H := dualModuleOf (M := M) omega d
    have hHfin : Module.Finite A H := dualizingDerivedHom_finiteCohomology A omega homega.1
      ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
        (ModuleCat.of A M)) (finiteCohomology_single A (ModuleCat.of A M)) (-(d : ℤ))
    letI : Module.Finite A H := hHfin
    have hH := dualizingHomology_isCM_and_depth omega homega d X.unop.property hnt
    exact ⟨H, hHfin, hH.1, hH.2⟩
  map f := by
    let g := dualizingDerivedHomFunctor A omega
    exact ⟨(DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).map
      (g.map ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map
        ((ObjectProperty.ι _).map f.unop)).op)⟩
  map_id X := by
    apply ObjectProperty.hom_ext
    dsimp
    simp
  map_comp f g := by
    apply ObjectProperty.hom_ext
    dsimp
    simp

/-- For a Cohen--Macaulay module `M` of depth `d`, an isomorphism of `RHom_A(M, ω)` with
`Ext^{-d}_A(M, ω)` placed in degree `-d`. -/
private noncomputable def cmHomologyDerivedIso
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max u v)} [AddCommGroup M] [Module A M]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega)
    (d : ℕ) (hcm : IsCohenMacaulayModuleOfDepth.{u, max u v} A d (ModuleCat.of A M))
    (hnt : Nontrivial M) :
    (dualizingDerivedHomFunctor A omega).obj
        (.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj
          (ModuleCat.of A M))) ≅
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).obj
        (ModuleCat.of A (dualModuleOf (M := M) omega d)) := by
  letI : Module.Finite A M := hcm.1
  exact isoSingleHomology
    (Classical.choice (Classical.choose_spec
      (exists_dualizing_homology_iso_single omega homega d hcm hnt)).2)

/-- The comparison `single ⋙ homology ≅ 𝟭` is the inverse of the map induced on degree `-d`
cohomology by `cmHomologyDerivedIso`. -/
private theorem cmHomologyDerivedIso_homology
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max u v)} [AddCommGroup M] [Module A M]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega)
    (d : ℕ) (hcm : IsCohenMacaulayModuleOfDepth.{u, max u v} A d (ModuleCat.of A M))
    (hnt : Nontrivial M) :
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
        (ModuleCat.{max u v} A) (-(d : ℤ))).hom.app
        (ModuleCat.of A (dualModuleOf (M := M) omega d)) =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).map
        (cmHomologyDerivedIso omega homega d hcm hnt).inv := by
  let : Module.Finite A M := hcm.1
  exact singleFunctorCompHomologyFunctorIso_hom_app_eq _

/-- Two morphisms between modules placed in degree `n` agree as soon as their degree `n`
cohomology maps agree, the placement functor being fully faithful. -/
private theorem homology_map_injective_single
    {A : Type u} [CommRing A] {X Y : ModuleCat.{max u v} A} (n : ℤ)
    (f g : ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) n).obj X ⟶
      (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) n).obj Y))
    (h : (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map f =
      (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n).map g) : f = g := by
  let S := DerivedCategory.singleFunctor (ModuleCat.{max u v} A) n
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) n
  let α := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{max u v} A) n
  let hFF := Functor.FullyFaithful.ofFullyFaithful S
  have hf := α.hom.naturality (hFF.preimage f)
  have hg := α.hom.naturality (hFF.preimage g)
  dsimp at hf hg
  have hpre : hFF.preimage f = hFF.preimage g := by
    apply (cancel_epi (α.hom.app X)).1
    calc
      α.hom.app X ≫ hFF.preimage f = H.map (S.map (hFF.preimage f)) ≫ α.hom.app Y := hf.symm
      _ = H.map (S.map (hFF.preimage g)) ≫ α.hom.app Y := by
        rw [hFF.map_preimage, hFF.map_preimage, h]
      _ = α.hom.app X ≫ hFF.preimage g := hg
  calc
    f = S.map (hFF.preimage f) := (hFF.map_preimage f).symm
    _ = S.map (hFF.preimage g) := congrArg S.map hpre
    _ = g := hFF.map_preimage g

/-- The isomorphisms `cmHomologyDerivedIso` are natural in the Cohen--Macaulay module. -/
private theorem cmHomologyDerivedIso_naturality
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega)
    (d : ℕ)
    (X Y : CohenMacaulayModulesOfDepth.{u, max u v} A d) (f : Y ⟶ X) :
    (cmHomologyDerivedIso omega homega d X.property
      (nontrivial_of_depth_eq_nat d X.property.2.2)).hom ≫
        (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).map
          ((cmHomologyFunctor omega homega d).map f.op).hom =
      (dualizingDerivedHomFunctor A omega).map
        ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map f.hom).op ≫
          (cmHomologyDerivedIso omega homega d Y.property
            (nontrivial_of_depth_eq_nat d Y.property.2.2)).hom := by
  let G := cmHomologyFunctor omega homega d
  let : Module.Finite A X.obj := X.property.1
  let : Module.Finite A Y.obj := Y.property.1
  let eM := cmHomologyDerivedIso omega homega d X.property
    (nontrivial_of_depth_eq_nat d X.property.2.2)
  let eN := cmHomologyDerivedIso omega homega d Y.property
    (nontrivial_of_depth_eq_nat d Y.property.2.2)
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (-(d : ℤ))
  let S := DerivedCategory.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))
  let D := dualizingDerivedHomFunctor A omega
  let X₀ := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj X.obj
  let Y₀ := (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj Y.obj
  let GM := H.obj (D.obj (.op X₀))
  let GN := H.obj (D.obj (.op Y₀))
  let fD := D.map ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map f.hom).op
  let fG := H.map fD
  let α := DerivedCategory.singleFunctorCompHomologyFunctorIso
    (ModuleCat.{max u v} A) (-(d : ℤ))
  have hαM : α.hom.app GM = H.map eM.inv := cmHomologyDerivedIso_homology omega homega d X.property
    (nontrivial_of_depth_eq_nat d X.property.2.2)
  have hαN : α.hom.app GN = H.map eN.inv := cmHomologyDerivedIso_homology omega homega d Y.property
    (nontrivial_of_depth_eq_nat d Y.property.2.2)
  have hαG : H.map (S.map fG) ≫ α.hom.app GN =
      α.hom.app GM ≫ fG := by
    simpa [H, S, α] using α.hom.naturality fG
  have hnat : H.map (S.map fG) ≫ H.map eN.inv =
      H.map eM.inv ≫ fG := by
    rwa [hαN, hαM] at hαG
  have hconj : S.map fG = eM.inv ≫ fD ≫ eN.hom := by
    apply homology_map_injective_single (A := A) (n := -(d : ℤ))
    apply (cancel_mono (H.map eN.inv)).1
    calc
      H.map (S.map fG) ≫ H.map eN.inv = H.map eM.inv ≫ fG := hnat
      _ = H.map eM.inv ≫ H.map fD := by rfl
      _ = H.map (eM.inv ≫ fD ≫ eN.hom) ≫ H.map eN.inv := by
        rw [← H.map_comp, ← H.map_comp]
        congr 1
        rw [Category.assoc eM.inv (fD ≫ eN.hom) eN.inv, Category.assoc fD eN.hom eN.inv,
          eN.hom_inv_id, Category.comp_id]
  show eM.hom ≫ S.map fG = fD ≫ eN.hom
  rw [hconj, Iso.hom_inv_id_assoc]

/-- The value of `cmHomologyFunctor` is the degree `-d` cohomology of `RHom_A(M, ω)` on the
nose. -/
private noncomputable def cmHomologyDerivedHomologyIso
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (_homega : IsNormalizedDualizingComplex omega)
    (d : ℕ) (X : CohenMacaulayModulesOfDepth.{u, max u v} A d) :
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).obj
        ((dualizingDerivedHomFunctor A omega).obj
          (.op ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).obj X.obj))) ≅
      ModuleCat.of A (dualModuleOf (M := X.obj) omega d) :=
  Iso.refl _

/-- The identifications `cmHomologyDerivedHomologyIso` are natural in the Cohen--Macaulay
module. -/
private theorem cmHomologyDerivedHomologyIso_naturality
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega)
    (d : ℕ) (X Y : CohenMacaulayModulesOfDepth.{u, max u v} A d) (f : Y ⟶ X) :
    (cmHomologyDerivedHomologyIso omega homega d X).hom ≫
        ((cmHomologyFunctor omega homega d).map f.op).hom =
    (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (-(d : ℤ))).map
          ((dualizingDerivedHomFunctor A omega).map
            ((DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).map f.hom).op) ≫
    (cmHomologyDerivedHomologyIso omega homega d Y).hom := by
  dsimp [cmHomologyDerivedHomologyIso, cmHomologyFunctor]
  simp

/-- Biduality: for a nonzero finite Cohen--Macaulay module `M` of depth `d`, the double dual
`Ext^{-d}_A(Ext^{-d}_A(M, ω), ω)` is `M`. -/
private noncomputable def cmHomologyDoubleIso
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    {M : Type (max u v)} [AddCommGroup M] [Module A M] [Module.Finite A M]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega)
    (d : ℕ) (hcm : IsCohenMacaulayModuleOfDepth.{u, max u v} A d (ModuleCat.of A M))
    (hnt : Nontrivial M) :
    ModuleCat.of A (dualModuleOf (M := dualModuleOf (M := M) omega d) omega d) ≅
      ModuleCat.of A M := by
  let eHom := (DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) 0).mapIso
      ((dualizingDerivedHomFunctor A omega).mapIso (cmHomologyDerivedIso omega homega d hcm hnt).op
        ≪≫ (singleBidualIso omega homega (ModuleCat.of A M)).symm) ≪≫
    (DerivedCategory.singleFunctorCompHomologyFunctorIso
      (ModuleCat.{max u v} A) 0).app (ModuleCat.of A M)
  exact (shiftedDualHomologyLinearEquiv omega
    (dualModuleOf (M := M) omega d) d).symm.trans eHom.toLinearEquiv |>.toModuleIso

/-- The duality functor is faithful, derived duality being an anti-equivalence on objects with
finite cohomology. -/
private theorem cmHomologyFunctor_faithful
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega) (d : ℕ) :
    (cmHomologyFunctor omega homega d).Faithful := by
  let G := cmHomologyFunctor omega homega d
  let S0 := DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0
  let D := dualizingDerivedHomFunctor A omega
  let F := coherentDualizingDerivedHomFunctor A omega homega.1
  let : F.IsEquivalence := coherentDualizingDerivedHom_isEquivalence A omega homega.1
  constructor
  intro X Y f g h
  let : Module.Finite A X.unop.obj := X.unop.property.1
  let : Module.Finite A Y.unop.obj := Y.unop.property.1
  let X₀ := S0.obj X.unop.obj
  let Y₀ := S0.obj Y.unop.obj
  let Xc : CoherentDerivedCategory A :=
    ⟨X₀, finiteCohomology_single A X.unop.obj⟩
  let Yc : CoherentDerivedCategory A :=
    ⟨Y₀, finiteCohomology_single A Y.unop.obj⟩
  let eM := cmHomologyDerivedIso omega homega d X.unop.property
    (nontrivial_of_depth_eq_nat d X.unop.property.2.2)
  let eN := cmHomologyDerivedIso omega homega d Y.unop.property
    (nontrivial_of_depth_eq_nat d Y.unop.property.2.2)
  let S := DerivedCategory.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))
  have hnat : ∀ k : X ⟶ Y, eM.hom ≫ S.map ((G.map k).hom) =
      D.map ((S0.map k.unop.hom).op) ≫ eN.hom := fun k => by
    simpa [G, S] using cmHomologyDerivedIso_naturality omega homega d X.unop Y.unop k.unop
  have hmap : (G.map f).hom = (G.map g).hom := congrArg (fun q => q.hom) h
  have hD : D.map ((S0.map f.unop.hom).op) = D.map ((S0.map g.unop.hom).op) := by
    apply (cancel_mono eN.hom).1
    rw [← hnat f, hmap, hnat g]
  let ι := ObjectProperty.ι (fun K : DerivedCategory (ModuleCat.{max u v} A) =>
    ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} A) i).obj K))
  let lift : (Y.unop ⟶ X.unop) → (Opposite.op Xc ⟶ Opposite.op Yc) := fun k =>
    ι.op.preimage (show Opposite.op (S0.obj X.unop.obj) ⟶ Opposite.op (S0.obj Y.unop.obj) from
      (S0.map k.hom).op)
  have hlift : ∀ k, ι.op.map (lift k) = (S0.map k.hom).op := fun k => ι.op.map_preimage _
  have hFc : F.map (lift f.unop) = F.map (lift g.unop) := by
    apply ι.map_injective
    change D.map (ι.op.map _) = D.map (ι.op.map _)
    rw [hlift, hlift]
    exact hD
  have hsingleOp := (hlift f.unop).symm.trans
    ((congrArg ι.op.map (F.map_injective hFc)).trans (hlift g.unop))
  have hlin : f.unop.hom = g.unop.hom := (Functor.FullyFaithful.ofFullyFaithful S0).map_injective
    (congrArg (fun q => q.unop) hsingleOp)
  apply Quiver.Hom.unop_inj
  apply ObjectProperty.hom_ext
  exact hlin

/-- The duality functor is full: a map of the `Ext` modules comes from a map of derived duals,
hence from a map of the modules themselves. -/
private theorem cmHomologyFunctor_full
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega) (d : ℕ) :
    (cmHomologyFunctor omega homega d).Full := by
  let G := cmHomologyFunctor omega homega d
  let S0 := DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0
  let S := DerivedCategory.singleFunctor (ModuleCat.{max u v} A) (-(d : ℤ))
  let D := dualizingDerivedHomFunctor A omega
  let F := coherentDualizingDerivedHomFunctor A omega homega.1
  let ι := ObjectProperty.ι (fun K : DerivedCategory (ModuleCat.{max u v} A) =>
    ∀ i : ℤ, Module.Finite A ((DerivedCategory.homologyFunctor
      (ModuleCat.{max u v} A) i).obj K))
  let : F.Full := by
    let : F.IsEquivalence :=
      coherentDualizingDerivedHom_isEquivalence A omega homega.1
    infer_instance
  constructor
  intro X Y k
  let : Module.Finite A X.unop.obj := X.unop.property.1
  let : Module.Finite A Y.unop.obj := Y.unop.property.1
  let Xc : CoherentDerivedCategory A :=
    ⟨S0.obj X.unop.obj, finiteCohomology_single A X.unop.obj⟩
  let Yc : CoherentDerivedCategory A :=
    ⟨S0.obj Y.unop.obj, finiteCohomology_single A Y.unop.obj⟩
  let eM : _ ≅ S.obj (G.obj X).obj := cmHomologyDerivedIso omega homega d X.unop.property
    (nontrivial_of_depth_eq_nat d X.unop.property.2.2)
  let eN : _ ≅ S.obj (G.obj Y).obj := cmHomologyDerivedIso omega homega d Y.unop.property
    (nontrivial_of_depth_eq_nat d Y.unop.property.2.2)
  let q := eM.hom ≫ S.map k.hom ≫ eN.inv
  let qC : ι.obj (F.obj (Opposite.op Xc)) ⟶ ι.obj (F.obj (Opposite.op Yc)) := q
  let fC : Opposite.op Xc ⟶ Opposite.op Yc := F.preimage (ι.preimage qC)
  let fD := (ι.op.map fC).unop
  let fBase : Y.unop.obj ⟶ X.unop.obj :=
    (Functor.FullyFaithful.ofFullyFaithful S0).preimage fD
  let fCM : Y.unop ⟶ X.unop := ⟨fBase⟩
  let f : X ⟶ Y := fCM.op
  have hFmap : F.map fC = ι.preimage qC := F.map_preimage (ι.preimage qC)
  have hDerived : D.map ((S0.map fBase).op) = q := by
    have hSingle : S0.map fBase = fD :=
      (Functor.FullyFaithful.ofFullyFaithful S0).map_preimage fD
    rw [congrArg (fun a => D.map a.op) hSingle]
    have htmp : ι.map (F.map fC) = q := by
      rw [hFmap, ι.map_preimage]
    show D.map (ι.op.map fC) = q
    simpa [F, ι, coherentDualizingDerivedHomFunctor] using htmp
  have hnat := cmHomologyDerivedIso_naturality omega homega d X.unop Y.unop fCM
  have hnat' : eM.hom ≫ S.map (G.map f).hom =
      D.map ((S0.map fBase).op) ≫ eN.hom := by
    simpa [G, S, f, fCM, eM, eN, cmHomologyFunctor] using hnat
  have hS : S.map (G.map f).hom = S.map k.hom := by
    apply (cancel_epi eM.hom).1
    rw [hnat', hDerived]
    simp [q]
  have hObjX : (G.obj X).obj = ModuleCat.of A
      (dualModuleOf (M := X.unop.obj) omega d) := rfl
  have hObjY : (G.obj Y).obj = ModuleCat.of A
      (dualModuleOf (M := Y.unop.obj) omega d) := rfl
  have hModule : (G.map f).hom = k.hom := by
    cases hObjX
    cases hObjY
    exact (Functor.FullyFaithful.ofFullyFaithful S).map_injective hS
  refine ⟨f, ?_⟩
  apply ObjectProperty.hom_ext
  exact hModule

/-- The duality functor is essentially surjective, every object being the dual of its own
dual. -/
private theorem cmHomologyFunctor_essSurj
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega) (d : ℕ) :
    (cmHomologyFunctor omega homega d).EssSurj := by
  let G := cmHomologyFunctor omega homega d
  constructor
  intro Y
  let : Module.Finite A Y.obj := Y.property.1
  have hnt := nontrivial_of_depth_eq_nat d Y.property.2.2
  let X := G.obj (Opposite.op Y)
  have e := cmHomologyDoubleIso omega homega d Y.property hnt
  exact ⟨Opposite.op X, ⟨ObjectProperty.isoMk _ e⟩⟩

/-- `Ext^{-d}_A(-, ω)` as an anti-autoequivalence of the Cohen--Macaulay modules of depth `d`
taken in the universe of the derived category. -/
private noncomputable def cmHomologyEquivalence
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega) (d : ℕ) :
    (CohenMacaulayModulesOfDepth.{u, max u v} A d)ᵒᵖ ≌
      CohenMacaulayModulesOfDepth.{u, max u v} A d := by
  let G := cmHomologyFunctor omega homega d
  letI : G.IsEquivalence := {
    full := cmHomologyFunctor_full omega homega d
    faithful := cmHomologyFunctor_faithful omega homega d
    essSurj := cmHomologyFunctor_essSurj omega homega d }
  exact Functor.asEquivalence G

/-- Universe lifting of the modules, as a functor between the two copies of the category of
Cohen--Macaulay modules of depth `d`. -/
private noncomputable def cmUniverseLiftFunctor
    {A : Type u} [CommRing A] [IsLocalRing A] (d : ℕ) :
    CohenMacaulayModulesOfDepth.{u, max u v} A d ⥤
      CohenMacaulayModulesOfDepth.{u, max (u + 1) (v + 1)} A d where
  obj X := by
    let M := (ModuleCat.uliftFunctor.{max (u + 1) (v + 1), max u v} A).obj X.obj
    let e : (↑M) ≃ₗ[A] X.obj := ULift.moduleEquiv
    exact ⟨M, finite_isCohenMacaulay_depth_of_linearEquiv e X.property⟩
  map f := ⟨(ModuleCat.uliftFunctor.{max (u + 1) (v + 1), max u v} A).map f.hom⟩
  map_id X := by
    apply ObjectProperty.hom_ext
    ext x
    simp [ModuleCat.uliftFunctor]
  map_comp f g := by
    apply ObjectProperty.hom_ext
    ext x
    simp [ModuleCat.uliftFunctor]

/-- Every finite module in the larger universe is, up to isomorphism, a lift: a finite module is
determined by a small model. -/
private theorem cmUniverseLiftFunctor_essSurj
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (d : ℕ) :
    (cmUniverseLiftFunctor.{u, v} (A := A) d).EssSurj := by
  let L := cmUniverseLiftFunctor.{u, v} (A := A) d
  constructor
  intro Y
  let : Module.Finite A (↑Y.obj) := Y.property.1
  let hsmall := exists_small_model_of_finite.{u, max (u + 1) (v + 1)}
    (A := A) (M := (↑Y.obj))
  let N : ModuleCat.{u} A := Classical.choose hsmall
  have hN := Classical.choose_spec hsmall
  let eSmall : (ModuleCat.uliftFunctor.{max (u + 1) (v + 1), u} A).obj N ≅
      ModuleCat.of A Y.obj := Classical.choice hN
  let Xmod := (ModuleCat.uliftFunctor.{max u v, u} A).obj N
  let eLow : (↑Xmod) ≃ₗ[A] N := ULift.moduleEquiv
  let eHigh : N ≃ₗ[A] (↑((ModuleCat.uliftFunctor.{max (u + 1) (v + 1), u} A).obj N)) :=
    ULift.moduleEquiv.symm
  let eXY : (↑Xmod) ≃ₗ[A] (↑Y.obj) := eLow.trans (eHigh.trans eSmall.toLinearEquiv)
  let X : CohenMacaulayModulesOfDepth.{u, max u v} A d :=
    ⟨Xmod, finite_isCohenMacaulay_depth_of_linearEquiv eXY Y.property⟩
  let eLift : (↑(L.obj X).obj) ≃ₗ[A] (↑Xmod) := ULift.moduleEquiv
  let eToY := eLift.trans eXY
  exact ⟨X, ⟨ObjectProperty.isoMk _ eToY.toModuleIso⟩⟩

/-- Universe lifting identifies the two copies of the category of Cohen--Macaulay modules of
depth `d`. -/
private noncomputable def cmUniverseLiftEquivalence
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A] (d : ℕ) :
    CohenMacaulayModulesOfDepth.{u, max u v} A d ≌
      CohenMacaulayModulesOfDepth.{u, max (u + 1) (v + 1)} A d := by
  let L := cmUniverseLiftFunctor.{u, v} (A := A) d
  let hFF : L.FullyFaithful := by
    let U := ModuleCat.uliftFunctor.{max (u + 1) (v + 1), max u v} A
    let J := IsCohenMacaulayModuleOfDepth.{u, max u v} A d
    let K := IsCohenMacaulayModuleOfDepth.{u, max (u + 1) (v + 1)} A d
    let F0 := J.ι ⋙ U
    let F1 := L ⋙ K.ι
    have hIso : F0 ≅ F1 := by
      refine NatIso.ofComponents (F := F0) (G := F1) (fun X => ?_) ?_
      · dsimp [F0, F1, J, K, L, cmUniverseLiftFunctor]
        exact Iso.refl (U.obj X.obj)
      intro X Y f
      dsimp [F0, F1, J, K, L, U, cmUniverseLiftFunctor]
      rfl
    let hF1 := Functor.FullyFaithful.ofIso
      ((Functor.FullyFaithful.ofFullyFaithful J.ι).comp
        (ModuleCat.fullyFaithfulUliftFunctor.{u, max u v, max (u + 1) (v + 1)} A)) hIso
    letI : K.ι.Faithful := (Functor.FullyFaithful.ofFullyFaithful K.ι).faithful
    exact Functor.FullyFaithful.ofCompFaithful hF1
  letI : L.IsEquivalence := {
    full := hFF.full
    faithful := hFF.faithful
    essSurj := cmUniverseLiftFunctor_essSurj.{u, v} (A := A) d }
  exact Functor.asEquivalence L

/-- The duality functor, followed by the universe lift, is the degree `-d` cohomology of
`RHom_A(-, ω)` lifted to the universe of `Ext`. -/
private noncomputable def cmHomologyLiftIso
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega) (d : ℕ) :
    ((IsCohenMacaulayModuleOfDepth.{u, max u v} A d).ι.op ⋙
        (DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0).op ⋙
          dualizingDerivedHomFunctor A omega ⋙
            DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (-(d : ℤ)) ⋙
              ModuleCat.uliftFunctor.{max (u + 1) (v + 1), max u v} A) ≅
      (cmHomologyFunctor omega homega d ⋙
        cmUniverseLiftFunctor.{u, v} (A := A) d ⋙
          (IsCohenMacaulayModuleOfDepth.{u, max (u + 1) (v + 1)} A d).ι) := by
  let I := IsCohenMacaulayModuleOfDepth.{u, max u v} A d
  let J := IsCohenMacaulayModuleOfDepth.{u, max (u + 1) (v + 1)} A d
  let G := cmHomologyFunctor omega homega d
  let L := cmUniverseLiftFunctor.{u, v} (A := A) d
  let S0 := DerivedCategory.singleFunctor (ModuleCat.{max u v} A) 0
  let D := dualizingDerivedHomFunctor A omega
  let H := DerivedCategory.homologyFunctor (ModuleCat.{max u v} A) (-(d : ℤ))
  let U := ModuleCat.uliftFunctor.{max (u + 1) (v + 1), max u v} A
  let C := I.ι.op ⋙ S0.op ⋙ D ⋙ H ⋙ U
  let B := G ⋙ L ⋙ J.ι
  refine NatIso.ofComponents (F := C) (G := B)
    (fun X => by
      simpa [C, B, I, J, G, L, U, cmHomologyFunctor, cmUniverseLiftFunctor] using
        U.mapIso (cmHomologyDerivedHomologyIso omega homega d X.unop)) ?_
  intro X Y f
  change U.map (H.map (D.map ((S0.map f.unop.hom).op)) ≫
        (cmHomologyDerivedHomologyIso omega homega d Y.unop).hom) =
      U.map ((cmHomologyDerivedHomologyIso omega homega d X.unop).hom ≫
        (G.map f).hom)
  simpa only [Functor.map_comp, ObjectProperty.ι_map, Quiver.Hom.unop_op,
    G, I, cmHomologyFunctor] using
    congrArg U.map
    (cmHomologyDerivedHomologyIso_naturality omega homega d X.unop Y.unop
      f.unop).symm

/-- The contravariant functor `M ↦ Ext^{-d}_A(M, ω)` on all `A`-modules. -/
public noncomputable def extIntoDualizingComplex
    {A : Type u} [CommRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A)) (d : ℕ) :
    (ModuleCat.{max u v} A)ᵒᵖ ⥤ ModuleCat.{max (u + 1) (v + 1)} A :=
  extIntoOmegaAt A omega (-(d : ℤ))

/-- **Cohen--Macaulay duality (Stacks Project, Tag 0B5A).** For a normalized dualizing complex,
`Ext` in degree minus the depth induces an anti-autoequivalence of the category of finite
Cohen--Macaulay modules of that depth. -/
@[stacks 0B5A "cm_duality, that CM_d is anti-autoequivalent to itself", no_expose]
public noncomputable def cohenMacaulayExtDuality
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega) (d : ℕ) :
    (CohenMacaulayModulesOfDepth.{u, max u v} A d)ᵒᵖ ≌
      CohenMacaulayModulesOfDepth.{u, max (u + 1) (v + 1)} A d :=
  (cmHomologyEquivalence omega homega d).trans (cmUniverseLiftEquivalence (A := A) d)

/-- The duality functor, after forgetting the Cohen--Macaulay condition, is naturally the
canonical contravariant `Ext^{-d}` functor. -/
@[stacks 0B5A "cm_duality, that the anti-autoequivalence is M ↦ Ext^{-d}(M, ω)"]
public theorem cohenMacaulayExtDuality_forget
    {A : Type u} [CommRing A] [IsNoetherianRing A] [IsLocalRing A]
    (omega : DerivedCategory (ModuleCat.{max u v} A))
    (homega : IsNormalizedDualizingComplex omega) (d : ℕ) :
    Nonempty
      ((cohenMacaulayExtDuality omega homega d).functor ⋙
          (IsCohenMacaulayModuleOfDepth.{u, max (u + 1) (v + 1)} A d).ι ≅
        (IsCohenMacaulayModuleOfDepth.{u, max u v} A d).ι.op ⋙
          extIntoDualizingComplex omega d) := by
  let I := IsCohenMacaulayModuleOfDepth.{u, max u v} A d
  let J := IsCohenMacaulayModuleOfDepth.{u, max (u + 1) (v + 1)} A d
  let G := cmHomologyFunctor omega homega d
  let L := cmUniverseLiftFunctor.{u, v} (A := A) d
  let α := Functor.isoWhiskerLeft I.ι.op
    (extIntoOmegaAtIso A omega (-(d : ℤ)))
  let β := cmHomologyLiftIso omega homega d
  let γ := Functor.associator G L J.ι
  refine ⟨?_⟩
  simpa [cohenMacaulayExtDuality, extIntoDualizingComplex,
    cmHomologyEquivalence, cmUniverseLiftEquivalence, Functor.asEquivalence] using
    γ ≪≫ β.symm ≪≫ α.symm

end Dualizing
