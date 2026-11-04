module

import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered

public import StacksFrontier.RingTheory.Flat.InjectiveModMaximalIdeal
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The residue fibre of a spreading-out system injects into the residue fibre of the colimit

Let `(A λ → B λ, N λ)` be a directed system with colimit `(R → S, M)` in which every `B μ` is a
localization at a prime of `B λ ⊗_{A λ} A μ`, every `N μ` is the base change of `N λ` along
`B λ → B μ`, and the maps `A λ → B λ`, `ρ_λ : A λ → R` and `σ_λ : B λ → S` are local homomorphisms
of local rings. Let `𝔪` be the maximal ideal of `R` and `𝔪_λ = ρ_λ^{-1}(𝔪)`. Then
`N λ / 𝔪_λ N λ → M / 𝔪 M` is injective for every `λ`.

## Main results

* `SpreadingOut.mem_smul_top_of_leg_mem_smul_top`: if the image of `x ∈ N λ` in `M` lies in `𝔪 M`,
  then `x` lies in `𝔪_λ N λ`.
* `SpreadingOut.flat_map_of_isLocalization_pushout`: in such a system, a flat transition map
  `A k → A l` gives a flat transition map `B k → B l`.
* `SpreadingOut.injective_of_isBaseChange_of_faithfullyFlat`: a base change along a faithfully
  flat algebra is injective.
* `SpreadingOut.comap_maximalIdeal_of_isLocalHom`: the contraction of the maximal ideal along a
  local homomorphism of local rings is the maximal ideal.

## Implementation notes

`𝔪_λ` is `Stacks.SpreadingOut.QuotientSystem.idealA ρ (maximalIdeal R) λ`, and `𝔪_λ N λ` is the
submodule `(𝔪_λ B λ) • ⊤` of the `B λ`-module `N λ`.
-/

@[expose] public section


universe u

open CategoryTheory Limits IsLocalRing
open scoped TensorProduct

namespace SpreadingOut

/-! ### Injectivity of a base change -/

/-- A base change along a faithfully flat algebra is injective. -/
public lemma injective_of_isBaseChange_of_faithfullyFlat
    {C C' P Q : Type*} [CommRing C] [CommRing C'] [Algebra C C'] [Module.FaithfullyFlat C C']
    [AddCommGroup P] [Module C P] [AddCommGroup Q] [Module C Q] [Module C' Q]
    [IsScalarTower C C' Q] {f : P →ₗ[C] Q} (h : IsBaseChange C' f) :
    Function.Injective f := by
  rw [injective_iff_map_eq_zero]
  intro p hp
  refine (Module.FaithfullyFlat.one_tmul_eq_zero_iff C P (A := C') p).1 (h.equiv.injective ?_)
  rwa [map_zero, h.equiv_tmul, one_smul]

/-! ### Flatness of the transition maps -/

/-- Let `φ : A ⟶ B` be a map of systems of commutative rings in which every `B l` is a
localization at a prime of the pushout of `B k ← A k → A l`. If the transition map `A k → A l` is
flat, then so is `B k → B l`. -/
public lemma flat_map_of_isLocalization_pushout
    {Λ : Type u} [Preorder Λ] {A B : Λ ⥤ CommRingCat.{u}} (φ : A ⟶ B)
    (hBloc : ∀ ⦃i j : Λ⦄ (h : i ⟶ j),
      letI := (pushout.desc (B.map h) (φ.app j) (φ.naturality h).symm).hom.toAlgebra
      ∃ (q : Ideal ↑(pushout (φ.app i) (A.map h))) (_ : q.IsPrime),
        IsLocalization q.primeCompl ↑(B.obj j))
    ⦃k l : Λ⦄ (h : k ⟶ l)
    (hflat : letI : Algebra ↑(A.obj k) ↑(A.obj l) := (A.map h).hom.toAlgebra
      Module.Flat ↑(A.obj k) ↑(A.obj l)) :
    letI : Algebra ↑(B.obj k) ↑(B.obj l) := (B.map h).hom.toAlgebra
    Module.Flat ↑(B.obj k) ↑(B.obj l) := by
  let algAkBk : Algebra ↑(A.obj k) ↑(B.obj k) := (φ.app k).hom.toAlgebra
  let algAkAl : Algebra ↑(A.obj k) ↑(A.obj l) := (A.map h).hom.toAlgebra
  let algBkBl : Algebra ↑(B.obj k) ↑(B.obj l) := (B.map h).hom.toAlgebra
  let algAlBl : Algebra ↑(A.obj l) ↑(B.obj l) := (φ.app l).hom.toAlgebra
  let algAkBl : Algebra ↑(A.obj k) ↑(B.obj l) := ((B.map h).hom.comp (φ.app k).hom).toAlgebra
  have towBk : IsScalarTower ↑(A.obj k) ↑(B.obj k) ↑(B.obj l) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have towAl : IsScalarTower ↑(A.obj k) ↑(A.obj l) ↑(B.obj l) :=
    IsScalarTower.of_algebraMap_eq fun x => (Stacks.SpreadingOut.QuotientSystem.phi_map φ h x).symm
  let algTensor : Algebra (↑(B.obj k) ⊗[↑(A.obj k)] ↑(A.obj l)) ↑(B.obj l) :=
    (Algebra.TensorProduct.productMap
      (IsScalarTower.toAlgHom ↑(A.obj k) ↑(B.obj k) ↑(B.obj l))
      (IsScalarTower.toAlgHom ↑(A.obj k) ↑(A.obj l) ↑(B.obj l))).toRingHom.toAlgebra
  obtain ⟨T, hT⟩ := CommRingCat.exists_isLocalization_tensorProduct_of_pushout
    (Ri := ↑(A.obj k)) (Si := ↑(B.obj k)) (Rj := ↑(A.obj l)) (Sj := ↑(B.obj l))
    (fun _ => rfl) (φ.naturality h).symm (hBloc h)
  have := hT
  have := hflat
  have h1 : Module.Flat ↑(B.obj k) (↑(B.obj k) ⊗[↑(A.obj k)] ↑(A.obj l)) :=
    Module.Flat.baseChange ↑(A.obj k) ↑(B.obj k) ↑(A.obj l)
  have h2 : Module.Flat (↑(B.obj k) ⊗[↑(A.obj k)] ↑(A.obj l)) ↑(B.obj l) :=
    IsLocalization.flat _ T
  have tow2 : IsScalarTower ↑(B.obj k) (↑(B.obj k) ⊗[↑(A.obj k)] ↑(A.obj l)) ↑(B.obj l) :=
    IsScalarTower.of_algebraMap_eq fun x =>
      (Algebra.TensorProduct.productMap_left_apply
        (IsScalarTower.toAlgHom ↑(A.obj k) ↑(B.obj k) ↑(B.obj l))
        (IsScalarTower.toAlgHom ↑(A.obj k) ↑(A.obj l) ↑(B.obj l)) x).symm
  exact Module.Flat.trans ↑(B.obj k) (↑(B.obj k) ⊗[↑(A.obj k)] ↑(A.obj l)) ↑(B.obj l)

/-! ### The residue fibre injects -/

/-- The contraction of the maximal ideal along a local homomorphism is the maximal ideal. -/
@[ega "0 1.0.7" "local implies φ⁻¹(n)=m"]
public lemma comap_maximalIdeal_of_isLocalHom {A₀ R₀ : Type*} [CommRing A₀] [CommRing R₀]
    [IsLocalRing A₀] [IsLocalRing R₀] (f : A₀ →+* R₀) [IsLocalHom f] :
    (maximalIdeal R₀).comap f = maximalIdeal A₀ := by
  ext x
  simp only [Ideal.mem_comap, mem_maximalIdeal, mem_nonunits_iff]
  exact ⟨fun h hu => h (hu.map f), fun h hu => h (IsLocalHom.map_nonunit x hu)⟩

/-- Let `(A λ → B λ, N λ)` be a directed system of local homomorphisms of local rings and modules
with colimits `R → S` and `M`, in which every `B μ` is a localization at a prime of
`B λ ⊗_{A λ} A μ` and every `N μ` is the base change of `N λ`, and all of whose structure maps
`ρ_λ : A λ → R` and `σ_λ : B λ → S` are local; let `𝔪` be the maximal ideal of `R`. If the image
of `x ∈ N λ` in `M` lies in `𝔪 M`, then `x` already lies in `𝔪_λ N λ`, where `𝔪_λ = ρ_λ^{-1}(𝔪)`.
Equivalently, `N λ/𝔪_λ N λ → M/𝔪M` is injective. -/
public theorem mem_smul_top_of_leg_mem_smul_top
    {R S M : Type u} [CommRing R] [CommRing S] [Algebra R S] [IsLocalRing R]
    [AddCommGroup M] [Module S M]
    {Λ : Type u} [Preorder Λ] [Nonempty Λ] [IsDirected Λ (· ≤ ·)]
    {A B : Λ ⥤ CommRingCat.{u}} {N : Λ ⥤ AddCommGrpCat.{u}} (φ : A ⟶ B)
    (ρ : A ⟶ (Functor.const Λ).obj (CommRingCat.of R))
    (σ : B ⟶ (Functor.const Λ).obj (CommRingCat.of S))
    (ν : N ⟶ (Functor.const Λ).obj (AddCommGrpCat.of M))
    (mod : ∀ i, Module ↑(B.obj i) ↑(N.obj i))
    (hsmul : ∀ ⦃i j : Λ⦄ (h : i ⟶ j) (b : ↑(B.obj i)) (m : ↑(N.obj i)),
      N.map h (b • m) = B.map h b • N.map h m)
    (hφ : ∀ i, φ.app i ≫ σ.app i = ρ.app i ≫ CommRingCat.ofHom (algebraMap R S))
    (hν : ∀ (i : Λ) (b : ↑(B.obj i)) (m : ↑(N.obj i)),
      (ν.app i (b • m) : M) = HSMul.hSMul (α := S) (β := M) (σ.app i b) (ν.app i m))
    (hR : IsColimit (Cocone.mk (CommRingCat.of R) ρ))
    (hS : IsColimit (Cocone.mk (CommRingCat.of S) σ))
    (hM : IsColimit (Cocone.mk (AddCommGrpCat.of M) ν))
    (hAlocal : ∀ i, IsLocalRing ↑(A.obj i)) (hBlocal : ∀ i, IsLocalRing ↑(B.obj i))
    (hφlocal : ∀ i, IsLocalHom (φ.app i).hom)
    (hρlocal : ∀ i, IsLocalHom (ρ.app i).hom)
    (hσlocal : ∀ i, IsLocalHom (σ.app i).hom)
    (hBloc : ∀ ⦃i j : Λ⦄ (h : i ⟶ j),
      letI := (pushout.desc (B.map h) (φ.app j) (φ.naturality h).symm).hom.toAlgebra
      ∃ (p : Ideal ↑(pushout (φ.app i) (A.map h))) (_ : p.IsPrime),
        IsLocalization p.primeCompl ↑(B.obj j))
    (hNbc : ∀ ⦃i j : Λ⦄ (h : i ⟶ j),
      letI : Algebra ↑(B.obj i) ↑(B.obj j) := (B.map h).hom.toAlgebra
      letI : Module ↑(B.obj i) ↑(N.obj j) := Module.compHom _ (B.map h).hom
      letI : IsScalarTower ↑(B.obj i) ↑(B.obj j) ↑(N.obj j) :=
        .of_algebraMap_smul fun _ _ => rfl
      IsBaseChange ↑(B.obj j)
        (⟨(N.map h).hom.toAddHom, hsmul h⟩ : ↑(N.obj i) →ₗ[↑(B.obj i)] ↑(N.obj j)))
    (k : Λ) (x : ↑(N.obj k))
    (hx : (ν.app k x : M) ∈ ((maximalIdeal R).map (algebraMap R S)) • (⊤ : Submodule S M)) :
    x ∈ (((maximalIdeal R).comap (ρ.app k).hom).map (φ.app k).hom)
      • (⊤ : Submodule ↑(B.obj k) ↑(N.obj k)) := by
  classical
  have : IsFiltered Λ := inferInstance
  have hI : (maximalIdeal R) ≠ ⊤ := (maximalIdeal.isMaximal R).ne_top
  have hmax : ∀ i : Λ,
      (Stacks.SpreadingOut.QuotientSystem.idealA ρ (maximalIdeal R) i).IsMaximal := by
    intro i
    have := hAlocal i
    have := hρlocal i
    have : IsLocalRing ↑(((Functor.const Λ).obj (CommRingCat.of R)).obj i) :=
      inferInstanceAs (IsLocalRing R)
    have heq : Stacks.SpreadingOut.QuotientSystem.idealA ρ (maximalIdeal R) i
        = maximalIdeal ↑(A.obj i) :=
      comap_maximalIdeal_of_isLocalHom (ρ.app i).hom
    rw [heq]
    exact maximalIdeal.isMaximal _
  have hinj : ∀ ⦃i j : Λ⦄ (h : i ⟶ j),
      Function.Injective
        ((Stacks.SpreadingOut.QuotientSystem.funN φ ρ (maximalIdeal R) mod hsmul).map h) := by
    intro i j h
    have := hAlocal i; have := hAlocal j; have := hBlocal i; have := hBlocal j
    have := hφlocal i; have := hφlocal j
    have hCloc : ∀ i : Λ, IsLocalRing
        (↑(B.obj i) ⧸ Stacks.SpreadingOut.QuotientSystem.idealB φ ρ (maximalIdeal R) i) :=
      Stacks.SpreadingOut.QuotientSystem.hBlocalQ φ ρ (maximalIdeal R) hI hAlocal hBlocal hφlocal
    have hCi := hCloc i
    have hCj := hCloc j
    have hne : ∀ i : Λ, Stacks.SpreadingOut.QuotientSystem.idealB φ ρ (maximalIdeal R) i ≠ ⊤ :=
      Stacks.SpreadingOut.QuotientSystem.idealB_ne_top φ ρ (maximalIdeal R) hI hAlocal hBlocal
        hφlocal
    have hBmap : IsLocalHom (B.map h).hom :=
      CategoryTheory.isLocalHom_map_of_isLocalHom_app σ hσlocal h
    have hqloc : IsLocalHom (Stacks.SpreadingOut.QuotientSystem.qmapB φ ρ (maximalIdeal R) h) :=
      Stacks.SpreadingOut.QuotientSystem.isLocalHom_quotientMap (B.map h).hom _
        (hne i) (hne j)
        (Stacks.SpreadingOut.QuotientSystem.idealB_le_comap φ ρ (maximalIdeal R) h)
    let algK : Algebra (↑(A.obj i) ⧸ Stacks.SpreadingOut.QuotientSystem.idealA ρ (maximalIdeal R) i)
        (↑(A.obj j) ⧸ Stacks.SpreadingOut.QuotientSystem.idealA ρ (maximalIdeal R) j) :=
      ((Stacks.SpreadingOut.QuotientSystem.funA ρ (maximalIdeal R)).map h).hom.toAlgebra
    have hfieldflat : Module.Flat
        (↑(A.obj i) ⧸ Stacks.SpreadingOut.QuotientSystem.idealA ρ (maximalIdeal R) i)
        (↑(A.obj j) ⧸ Stacks.SpreadingOut.QuotientSystem.idealA ρ (maximalIdeal R) j) := by
      have := hmax i
      let fld : Field
          (↑(A.obj i) ⧸ Stacks.SpreadingOut.QuotientSystem.idealA ρ (maximalIdeal R) i) :=
        Ideal.Quotient.field _
      exact Module.Flat.of_free
    have hflat := flat_map_of_isLocalization_pushout
      (Stacks.SpreadingOut.QuotientSystem.funPhi φ ρ (maximalIdeal R))
      (Stacks.SpreadingOut.QuotientSystem.hBlocQ φ ρ (maximalIdeal R) hI hAlocal hBlocal hφlocal
        hBloc) h hfieldflat
    let algC : Algebra
        (↑(B.obj i) ⧸ Stacks.SpreadingOut.QuotientSystem.idealB φ ρ (maximalIdeal R) i)
        (↑(B.obj j) ⧸ Stacks.SpreadingOut.QuotientSystem.idealB φ ρ (maximalIdeal R) j) :=
      (Stacks.SpreadingOut.QuotientSystem.qmapB φ ρ (maximalIdeal R) h).toAlgebra
    have hflat' : Module.Flat
        (↑(B.obj i) ⧸ Stacks.SpreadingOut.QuotientSystem.idealB φ ρ (maximalIdeal R) i)
        (↑(B.obj j) ⧸ Stacks.SpreadingOut.QuotientSystem.idealB φ ρ (maximalIdeal R) j) := hflat
    have hff : Module.FaithfullyFlat
        (↑(B.obj i) ⧸ Stacks.SpreadingOut.QuotientSystem.idealB φ ρ (maximalIdeal R) i)
        (↑(B.obj j) ⧸ Stacks.SpreadingOut.QuotientSystem.idealB φ ρ (maximalIdeal R) j) :=
      Module.FaithfullyFlat.of_flat_of_isLocalHom
    let modBN : Module
        (↑(B.obj i) ⧸ Stacks.SpreadingOut.QuotientSystem.idealB φ ρ (maximalIdeal R) i)
        (↑(N.obj j) ⧸ (Stacks.SpreadingOut.QuotientSystem.idealB φ ρ (maximalIdeal R) j)
          • (⊤ : Submodule ↑(B.obj j) ↑(N.obj j))) :=
      Module.compHom _ (Stacks.SpreadingOut.QuotientSystem.qmapB φ ρ (maximalIdeal R) h)
    let towBB := Stacks.SpreadingOut.QuotientSystem.tower_of_algebraMap_smul
      (R₀ := ↑(B.obj i) ⧸ Stacks.SpreadingOut.QuotientSystem.idealB φ ρ (maximalIdeal R) i)
      (S₀ := ↑(B.obj j) ⧸ Stacks.SpreadingOut.QuotientSystem.idealB φ ρ (maximalIdeal R) j)
      (M₀ := ↑(N.obj j) ⧸ (Stacks.SpreadingOut.QuotientSystem.idealB φ ρ (maximalIdeal R) j)
        • (⊤ : Submodule ↑(B.obj j) ↑(N.obj j))) (fun _ _ => rfl)
    exact injective_of_isBaseChange_of_faithfullyFlat
      (Stacks.SpreadingOut.QuotientSystem.hNbcQ φ ρ (maximalIdeal R) mod hsmul hNbc h)
  let modQinst := Stacks.SpreadingOut.QuotientSystem.modQ φ ρ (maximalIdeal R) mod hsmul
  have hcol := Stacks.SpreadingOut.QuotientSystem.legNIsColimit φ ρ σ ν (maximalIdeal R) mod hsmul
    hφ hν hR hS hM
  have hzero :
      (Stacks.SpreadingOut.QuotientSystem.legN φ ρ σ ν (maximalIdeal R) mod hsmul hφ hν).app k
        (Submodule.Quotient.mk x)
      = (Stacks.SpreadingOut.QuotientSystem.legN φ ρ σ ν (maximalIdeal R) mod hsmul hφ hν).app k
        0 := by
    rw [map_zero, Stacks.SpreadingOut.QuotientSystem.legN_app_mk]
    exact (Submodule.Quotient.mk_eq_zero _).2 hx
  obtain ⟨q, f, g, hfg⟩ :=
    (IsColimit.eq_iff (Stacks.SpreadingOut.QuotientSystem.funN φ ρ (maximalIdeal R) mod hsmul)
      hcol).1 hzero
  refine (Submodule.Quotient.mk_eq_zero _).1 (hinj f ?_)
  exact hfg.trans
    ((map_zero (ConcreteCategory.hom
        ((Stacks.SpreadingOut.QuotientSystem.funN φ ρ (maximalIdeal R) mod hsmul).map g))).trans
      (map_zero (ConcreteCategory.hom
        ((Stacks.SpreadingOut.QuotientSystem.funN φ ρ (maximalIdeal R) mod hsmul).map f))).symm)

end SpreadingOut
