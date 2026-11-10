module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.AlgebraicTopology.SimplexCategory.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Regular.RegularSequence
public import StacksFrontier.RingTheory.Koszul.Defs
import StacksCore.Tactic.EgaSgaAttribute

@[expose] public section

set_option backward.isDefEq.respectTransparency false

/-!
# Flat base change of Koszul regularity

Let `φ : R → S` be a flat ring map, let `f_1, ..., f_r ∈ R`, let `M` be an `R`-module and let
`N = S ⊗_R M`. If `f_1, ..., f_r` is `M`-`H_1`-regular, respectively `M`-Koszul-regular, then
`φ(f_1), ..., φ(f_r)` is `N`-`H_1`-regular, respectively `N`-Koszul-regular.

## Main definitions

* `KoszulC.koszulComplexBaseChange`: the termwise base change `S ⊗_R (K_•(f) ⊗_R M)` of the Koszul
  complex with coefficients in `M`.
* `KoszulC.extBaseChange`: the `R`-algebra map `⋀_R(R^r) → ⋀_S(S^r)` induced by `φ`.

## Main results

* `KoszulC.homology_baseChange_linearEquiv`: for `S` flat over `R`,
  `H_i(K_•(φ(f)) ⊗_S N) ≅ S ⊗_R H_i(K_•(f) ⊗_R M)`.
* `KoszulC.homology_isZero_baseChange`: flat base change preserves the vanishing of
  `H_i(K_•(f) ⊗_R M)`.
* `KoszulC.isH1Regular_baseChange`: flat base change of `H_1`-regular sequences.
* `KoszulC.isKoszulRegular_baseChange`: flat base change of Koszul-regular sequences.
* `Koszul.isWeaklyRegular_ringEquiv`: weak regularity is transported along a ring isomorphism.

## Implementation notes

`N` is `S ⊗[R] M` and `φ(f_i)` is `algebraMap R S (f i)`. Since `R`, `S` and `M` live in
independent universes, the homology of `K_•(φ(f)) ⊗_S N` and that of
`KoszulC.koszulComplexBaseChange f M` are objects of `ModuleCat S` in different universes; they
are compared through `S`-linear equivalences of the homology modules.
-/

open scoped ExteriorAlgebra TensorProduct
open CliffordAlgebra CategoryTheory

namespace KoszulC

open Koszul

variable {R : Type*} [CommRing R] {S : Type*} [CommRing S] [Algebra R S] {r : ℕ}

/-- The termwise base change of the Koszul complex along `R → S`: the chain complex of
`S`-modules with `n`-th term `S ⊗[R] (⋀[R]^n (Fin r → R) ⊗[R] M)` and differential the base change
`LinearMap.baseChange S` of `LinearMap.rTensor M (d (seqDual f) n)`. -/
@[ega "III 1.1.2" "more general", sga "6 VII 1.2"]
noncomputable def koszulComplexBaseChange (f : Fin r → R) (M : Type*) [AddCommGroup M]
    [Module R M] :
    ChainComplex (ModuleCat S) ℕ :=
  ChainComplex.of (fun n => ModuleCat.of S (S ⊗[R] ((⋀[R]^n (Fin r → R)) ⊗[R] M)))
    (fun n => ModuleCat.ofHom (R := S)
      (LinearMap.baseChange S (LinearMap.rTensor M (d (seqDual f) n))))
    (fun n => by
      apply ModuleCat.hom_ext
      rw [ModuleCat.hom_comp, ModuleCat.hom_ofHom, ModuleCat.hom_ofHom, ModuleCat.hom_zero,
        ← LinearMap.baseChange_comp, ← LinearMap.rTensor_comp, d_comp_d,
        LinearMap.rTensor_zero, LinearMap.baseChange_zero])

/-- The degree-`n` object of `koszulComplexBaseChange f M` is
`S ⊗[R] ((⋀[R]^n (Fin r → R)) ⊗[R] M)`. -/
@[simp]
lemma koszulComplexBaseChange_X (f : Fin r → R) (M : Type*) [AddCommGroup M] [Module R M] (n : ℕ) :
    (koszulComplexBaseChange (S := S) f M).X n
      = ModuleCat.of S (S ⊗[R] ((⋀[R]^n (Fin r → R)) ⊗[R] M)) := rfl

/-- If the `S`-linear equivalences `e₂`, `e₃` intertwine `g` with `g'`, then `e₂` carries
`ker g` onto `ker g'`. -/
lemma map_ker_of_comm {S A B A' B' : Type*} [CommRing S]
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup A'] [AddCommGroup B']
    [Module S A] [Module S B] [Module S A'] [Module S B']
    {g : A →ₗ[S] B} {g' : A' →ₗ[S] B'} (e₂ : A ≃ₗ[S] A') (e₃ : B ≃ₗ[S] B')
    (h : ∀ x, e₃ (g x) = g' (e₂ x)) :
    Submodule.map (e₂ : A →ₗ[S] A') (LinearMap.ker g) = LinearMap.ker g' := by
  apply le_antisymm
  · rintro _ ⟨y, hy, rfl⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker, LinearEquiv.coe_coe] at hy ⊢
    rw [← h y, hy, map_zero]
  · intro z hz
    rw [LinearMap.mem_ker] at hz
    refine ⟨e₂.symm z, ?_, by simp⟩
    simp only [SetLike.mem_coe, LinearMap.mem_ker]
    apply e₃.injective
    rw [h (e₂.symm z), LinearEquiv.apply_symm_apply, hz, map_zero]

/-- A degreewise family of `S`-linear equivalences between two complexes of `S`-modules of the
same shape, possibly in different universes, which commutes with the differentials induces an
`S`-linear equivalence of their homology modules. -/
lemma homologyTransport_of_degreewiseEquiv {S : Type*} [CommRing S] {ι : Type*}
    {c : ComplexShape ι}
    {C : HomologicalComplex (ModuleCat S) c} {D : HomologicalComplex (ModuleCat S) c}
    (e : ∀ n, (C.X n) ≃ₗ[S] (D.X n))
    (hcomm : ∀ n m, ∀ x : C.X n,
        (e m) ((C.d n m).hom x) = (D.d n m).hom ((e n) x))
    (i : ι) :
    Nonempty ((C.homology i) ≃ₗ[S] (D.homology i)) := by
  have scHelper : ∀ (sc₁ sc₂ : ShortComplex (ModuleCat S))
      (e₁ : (sc₁.X₁ : Type _) ≃ₗ[S] sc₂.X₁)
      (e₂ : (sc₁.X₂ : Type _) ≃ₗ[S] sc₂.X₂)
      (e₃ : (sc₁.X₃ : Type _) ≃ₗ[S] sc₂.X₃),
      (∀ x, e₂ (sc₁.f.hom x) = sc₂.f.hom (e₁ x)) →
      (∀ x, e₃ (sc₁.g.hom x) = sc₂.g.hom (e₂ x)) →
      Nonempty ((sc₁.homology : Type _) ≃ₗ[S] sc₂.homology) := by
    intro sc₁ sc₂ e₁ e₂ e₃ hf hg
    set R₁ := LinearMap.ker (sc₁.g).hom with hR₁
    set R₂ := LinearMap.ker (sc₂.g).hom with hR₂
    have hmap : Submodule.map (e₂ : sc₁.X₂ →ₗ[S] sc₂.X₂) R₁ = R₂ := by
      rw [hR₁, hR₂]; exact map_ker_of_comm e₂ e₃ hg
    let kE : (R₁ : Type _) ≃ₗ[S] R₂ := (e₂.submoduleMap R₁).trans (LinearEquiv.ofEq _ _ hmap)
    have hkE : ∀ x : sc₁.X₁,
        (kE (sc₁.moduleCatToCycles x) : sc₂.X₂) = sc₂.moduleCatToCycles (e₁ x) := by
      intro x
      simp only [kE, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
        LinearEquiv.submoduleMap_apply, ShortComplex.moduleCatToCycles, LinearMap.codRestrict_apply]
      exact hf x
    set P₁ := (sc₁.moduleCatToCycles).range
    set P₂ := (sc₂.moduleCatToCycles).range
    have hPmap : Submodule.map (kE : R₁ →ₗ[S] R₂) P₁ = P₂ := by
      apply le_antisymm
      · rintro _ ⟨z, ⟨x, rfl⟩, rfl⟩
        exact ⟨e₁ x, Subtype.ext (hkE x).symm⟩
      · rintro z ⟨x, rfl⟩
        refine ⟨sc₁.moduleCatToCycles (e₁.symm x), ⟨e₁.symm x, rfl⟩, ?_⟩
        apply Subtype.ext
        simp only [LinearEquiv.coe_coe, hkE, LinearEquiv.apply_symm_apply]
    exact ⟨(sc₁.moduleCatHomologyIso).toLinearEquiv.trans
      ((Submodule.Quotient.equiv P₁ P₂ kE hPmap).trans
        (sc₂.moduleCatHomologyIso).toLinearEquiv.symm)⟩
  exact scHelper (C.sc i) (D.sc i)
    (e (c.prev i)) (e i) (e (c.next i))
    (fun x => hcomm _ i x) (fun x => hcomm i _ x)

/-- The dual functional commutes with base change: `seqDual (φ ∘ f) (φ ∘ v) = φ (seqDual f v)`,
where `φ = algebraMap R S`. -/
lemma seqDual_baseChange_apply (f : Fin r → R) (v : Fin r → R) :
    seqDual (fun j => algebraMap R S (f j)) (fun j => algebraMap R S (v j))
      = algebraMap R S (seqDual f v) := by
  simp [seqDual_apply]

/-- The `R`-linear map `(Fin r → R) →ₗ[R] (Fin r → S)` given by `v ↦ algebraMap R S ∘ v`. -/
def algebraMapPi :
    (Fin r → R) →ₗ[R] (Fin r → S) :=
  (Algebra.linearMap R S).compLeft (Fin r)

/-- The `j`-th coordinate of `algebraMapPi m` is `algebraMap R S (m j)`. -/
@[simp]
lemma algebraMapPi_apply (m : Fin r → R) (j : Fin r) :
    algebraMapPi (S := S) m j = algebraMap R S (m j) := rfl

/-- There is an `S`-linear isomorphism `β : S ⊗[R] (⋀[R]^n (Fin r → R)) ≃ₗ[S] ⋀[S]^n (Fin r → S)`
with `β (1 ⊗ ιMulti R n v) = ιMulti S n (φ ∘ v)` for all `v`, where `φ = algebraMap R S`. -/
lemma extPow_baseChange_natEquiv (n : ℕ) :
    ∃ β : (S ⊗[R] (⋀[R]^n (Fin r → R))) ≃ₗ[S] (⋀[S]^n (Fin r → S)),
      ∀ (v : Fin n → (Fin r → R)),
        β (1 ⊗ₜ[R] (exteriorPower.ιMulti R n v))
          = exteriorPower.ιMulti S n (fun i => (fun j => algebraMap R S (v i j))) := by
  let gAlt : (Fin r → S) [⋀^Fin n]→ₗ[R] (⋀[S]^n (Fin r → S)) :=
    AlternatingMap.mk
      ((exteriorPower.ιMulti S n (M := Fin r → S)).toMultilinearMap.restrictScalars R)
      (fun v i j hv hij => (exteriorPower.ιMulti S n).map_eq_zero_of_eq v hv hij)
  let gNatMap : (⋀[R]^n (Fin r → R)) →ₗ[R] (⋀[S]^n (Fin r → S)) :=
    exteriorPower.alternatingMapLinearEquiv
      (gAlt.compLinearMap (algebraMapPi (S := S) (r := r)))
  let βMap : (S ⊗[R] (⋀[R]^n (Fin r → R))) →ₗ[S] (⋀[S]^n (Fin r → S)) :=
    LinearMap.liftBaseChange S gNatMap
  have βMap_gen : ∀ (v : Fin n → (Fin r → R)),
      βMap (1 ⊗ₜ[R] (exteriorPower.ιMulti R n v))
        = exteriorPower.ιMulti S n (fun i => (fun j => algebraMap R S (v i j))) := by
    intro v
    change (LinearMap.liftBaseChange S gNatMap) (1 ⊗ₜ[R] (exteriorPower.ιMulti R n v)) = _
    rw [LinearMap.liftBaseChange_tmul, one_smul]
    change exteriorPower.alternatingMapLinearEquiv
      (gAlt.compLinearMap (algebraMapPi (S := S) (r := r)))
      (exteriorPower.ιMulti R n v) = _
    rw [exteriorPower.alternatingMapLinearEquiv_apply_ιMulti]
    rfl
  let bR := Pi.basisFun R (Fin r)
  let bS := Pi.basisFun S (Fin r)
  let bLHS := (Module.Basis.exteriorPower n bR).baseChange S
  let bRHS := Module.Basis.exteriorPower n bS
  have key : ∀ s, βMap (bLHS s) = bRHS s := by
    intro s
    change βMap (((Module.Basis.exteriorPower n bR).baseChange S) s) = _
    rw [Module.Basis.baseChange_apply, exteriorPower.coe_basis]
    set σ := Set.powersetCard.ofFinEmbEquiv.symm s
    have hfam : exteriorPower.ιMulti_family R n (⇑bR) s
        = exteriorPower.ιMulti R n (fun i => bR (σ i)) := rfl
    rw [hfam, βMap_gen]
    change _ = bRHS s
    rw [show bRHS s = exteriorPower.ιMulti_family S n (⇑bS) s from
      congrFun (exteriorPower.coe_basis S n bS) s]
    have hfam2 : exteriorPower.ιMulti_family S n (⇑bS) s
        = exteriorPower.ιMulti S n (fun i => bS (σ i)) := rfl
    rw [hfam2]
    congr 1
    ext i j
    simp [bR, bS, Pi.basisFun_apply, Pi.single_apply]
  let β : (S ⊗[R] (⋀[R]^n (Fin r → R))) ≃ₗ[S] (⋀[S]^n (Fin r → S)) := bLHS.equiv bRHS (Equiv.refl _)
  have hβ : (β : (S ⊗[R] (⋀[R]^n (Fin r → R))) →ₗ[S] (⋀[S]^n (Fin r → S))) = βMap := by
    apply bLHS.ext
    intro s
    change β (bLHS s) = βMap (bLHS s)
    rw [key]
    change bLHS.equiv bRHS (Equiv.refl _) (bLHS s) = bRHS s
    rw [Module.Basis.equiv_apply]
    rfl
  refine ⟨β, fun v => ?_⟩
  have : β (1 ⊗ₜ[R] (exteriorPower.ιMulti R n v))
      = βMap (1 ⊗ₜ[R] (exteriorPower.ιMulti R n v)) := by
    rw [← LinearEquiv.coe_coe, hβ]
  rw [this, βMap_gen]

/-- The base-change `R`-algebra hom
`ExteriorAlgebra R (Fin r → R) →ₐ[R] ExteriorAlgebra S (Fin r → S)`,
sending `ι R m` to `ι S (φ ∘ m)`. -/
noncomputable def extBaseChange :
    ExteriorAlgebra R (Fin r → R) →ₐ[R] ExteriorAlgebra S (Fin r → S) :=
  ExteriorAlgebra.lift R ⟨(ExteriorAlgebra.ι S).restrictScalars R ∘ₗ algebraMapPi (S := S) (r := r),
    fun m => by simp⟩

/-- `extBaseChange` sends `ι R m` to `ι S (algebraMap R S ∘ m)`. -/
@[simp]
lemma extBaseChange_ι (m : Fin r → R) :
    extBaseChange (S := S) (r := r) (ExteriorAlgebra.ι R m)
      = ExteriorAlgebra.ι S (algebraMapPi (S := S) (r := r) m) := by
  simp [extBaseChange]

/-- `extBaseChange` carries `ιMulti R n v` to `ιMulti S n (φ ∘ v)`. -/
lemma extBaseChange_ιMulti (n : ℕ) (v : Fin n → (Fin r → R)) :
    extBaseChange (S := S) (r := r) (ExteriorAlgebra.ιMulti R n v)
      = ExteriorAlgebra.ιMulti S n (fun i => (fun j => algebraMap R S (v i j))) := by
  induction n with
  | zero => simp [ExteriorAlgebra.ιMulti]
  | succ k ih =>
    rw [ιMulti_succ_apply, map_mul, extBaseChange_ι, ih, ιMulti_succ_apply]
    congr 1

/-- If `β (1 ⊗ ιMulti R n v) = ιMulti S n (φ ∘ v)` for all `v`, then `β (1 ⊗ y)` is
`extBaseChange y` for every `y ∈ ⋀[R]^n (Fin r → R)`. -/
lemma coe_natEquiv_eq_extBaseChange {n : ℕ}
    (β : (S ⊗[R] (⋀[R]^n (Fin r → R))) ≃ₗ[S] (⋀[S]^n (Fin r → S)))
    (hβ : ∀ (v : Fin n → (Fin r → R)),
        β (1 ⊗ₜ[R] (exteriorPower.ιMulti R n v))
          = exteriorPower.ιMulti S n (fun i => (fun j => algebraMap R S (v i j))))
    (y : ExteriorAlgebra R (Fin r → R)) (hy : y ∈ ⋀[R]^n (Fin r → R)) :
    ((β (1 ⊗ₜ[R] (⟨y, hy⟩ : ⋀[R]^n (Fin r → R)))) : ExteriorAlgebra S (Fin r → S))
      = extBaseChange (S := S) (r := r) y := by
  have hmem : ∀ a ∈ Submodule.span R (Set.range ⇑(ExteriorAlgebra.ιMulti R n)),
      a ∈ ⋀[R]^n (Fin r → R) := by
    intro a ha
    rwa [exteriorPower.ιMulti_span_fixedDegree] at ha
  have hspan : y ∈ Submodule.span R (Set.range ⇑(ExteriorAlgebra.ιMulti R n)) := by
    rw [exteriorPower.ιMulti_span_fixedDegree]; exact hy
  induction hspan using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    have hcoe : ((⟨ExteriorAlgebra.ιMulti R n v, _⟩ : ⋀[R]^n (Fin r → R)))
        = exteriorPower.ιMulti R n v := rfl
    rw [hcoe, hβ, extBaseChange_ιMulti]; rfl
  | zero =>
    have h0 : (⟨(0 : ExteriorAlgebra R (Fin r → R)), hy⟩ : ⋀[R]^n (Fin r → R)) = 0 := rfl
    rw [h0, TensorProduct.tmul_zero, LinearEquiv.map_zero, Submodule.coe_zero, map_zero]
  | add a b ha hb iha ihb =>
    have ham := hmem a ha
    have hbm := hmem b hb
    have hsub : (⟨a + b, hy⟩ : ⋀[R]^n (Fin r → R))
        = (⟨a, ham⟩ : ⋀[R]^n (Fin r → R)) + ⟨b, hbm⟩ := rfl
    rw [hsub, TensorProduct.tmul_add, map_add, Submodule.coe_add, map_add, iha ham, ihb hbm]
  | smul c a ha iha =>
    have ham := hmem a ha
    have hsub : (⟨c • a, hy⟩ : ⋀[R]^n (Fin r → R)) = c • (⟨a, ham⟩ : ⋀[R]^n (Fin r → R)) := rfl
    rw [hsub, TensorProduct.tmul_smul,
      ← IsScalarTower.algebraMap_smul S c (1 ⊗ₜ[R] (⟨a, ham⟩ : ⋀[R]^n (Fin r → R))),
      map_smul, Submodule.coe_smul, iha ham, map_smul, IsScalarTower.algebraMap_smul]

/-- Contraction with `seqDual (φ ∘ f)` commutes with `extBaseChange` on the elements
`ιMulti R m w`. -/
lemma contractLeft_extBaseChange_ιMulti (f : Fin r → R) (m : ℕ) (w : Fin m → (Fin r → R)) :
    (CliffordAlgebra.contractLeft (seqDual (fun j => algebraMap R S (f j))))
        (extBaseChange (S := S) (r := r) (ExteriorAlgebra.ιMulti R m w))
      = extBaseChange (S := S) (r := r)
          ((CliffordAlgebra.contractLeft (seqDual f)) (ExteriorAlgebra.ιMulti R m w)) := by
  induction m with
  | zero =>
    have h0 : ExteriorAlgebra.ιMulti R 0 w = 1 := by simp [ExteriorAlgebra.ιMulti]
    rw [h0, map_one, contractLeft_one, contractLeft_one, map_zero]
  | succ k ih =>
    rw [ιMulti_succ_apply, map_mul, extBaseChange_ι, contractLeft_ι_mul, contractLeft_ι_mul,
      map_sub, map_smul, map_mul, extBaseChange_ι, ih]
    congr 1
    · have hscal : (seqDual (fun j => algebraMap R S (f j))) (algebraMapPi (S := S) (r := r) (w 0))
          = algebraMap R S (seqDual f (w 0)) :=
        seqDual_baseChange_apply f (w 0)
      rw [hscal, IsScalarTower.algebraMap_smul]

/-- Contraction with `seqDual (φ ∘ f)` commutes with `extBaseChange` on `⋀[R]^m (Fin r → R)`. -/
lemma contractLeft_extBaseChange_comm (f : Fin r → R) (m : ℕ) (x : ExteriorAlgebra R (Fin r → R))
    (hx : x ∈ ⋀[R]^m (Fin r → R)) :
    (CliffordAlgebra.contractLeft (seqDual (fun j => algebraMap R S (f j))))
        (extBaseChange (S := S) (r := r) x)
      = extBaseChange (S := S) (r := r)
          ((CliffordAlgebra.contractLeft (seqDual f)) x) := by
  rw [← exteriorPower.ιMulti_span_fixedDegree] at hx
  induction hx using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨v, rfl⟩ := hz
    exact contractLeft_extBaseChange_ιMulti f m v
  | zero => simp
  | add a b _ _ iha ihb => rw [map_add, map_add, map_add, iha, ihb, map_add]
  | smul c a _ iha =>
    rw [map_smul, ← IsScalarTower.algebraMap_smul S c (extBaseChange a),
      map_smul, iha, map_smul, map_smul, IsScalarTower.algebraMap_smul]

/-- If `β n (1 ⊗ ιMulti R n v) = ιMulti S n (φ ∘ v)` for all `n` and `v`, then
`β n (1 ⊗ d (seqDual f) n z) = d (seqDual (φ ∘ f)) n (β (n + 1) (1 ⊗ z))`. -/
lemma d_baseChange_comm (f : Fin r → R)
    (β : ∀ n, (S ⊗[R] (⋀[R]^n (Fin r → R))) ≃ₗ[S] (⋀[S]^n (Fin r → S)))
    (hβ : ∀ n, ∀ (v : Fin n → (Fin r → R)),
        β n (1 ⊗ₜ[R] (exteriorPower.ιMulti R n v))
          = exteriorPower.ιMulti S n (fun i => (fun j => algebraMap R S (v i j))))
    (n : ℕ) (z : (⋀[R]^(n + 1) (Fin r → R))) :
    β n (1 ⊗ₜ[R] (d (seqDual f) n z))
      = d (seqDual (fun j => algebraMap R S (f j))) n (β (n + 1) (1 ⊗ₜ[R] z)) := by
  apply Subtype.ext
  have hL : ((β n (1 ⊗ₜ[R] (d (seqDual f) n z))) : ExteriorAlgebra S (Fin r → S))
      = extBaseChange (S := S) (r := r)
          (CliffordAlgebra.contractLeft (seqDual f) (z : ExteriorAlgebra R (Fin r → R))) := by
    rw [coe_natEquiv_eq_extBaseChange (β n) (hβ n) _ (d (seqDual f) n z).2, ← d_apply_coe]
  have hβz : ((β (n + 1) (1 ⊗ₜ[R] z)) : ExteriorAlgebra S (Fin r → S))
      = extBaseChange (S := S) (r := r) (z : ExteriorAlgebra R (Fin r → R)) := by
    have h := coe_natEquiv_eq_extBaseChange (β (n + 1)) (hβ (n + 1))
      (z : ExteriorAlgebra R (Fin r → R)) z.2
    rwa [Subtype.coe_eta] at h
  rw [d_apply_coe, hβz, contractLeft_extBaseChange_comm f (n + 1)
    (z : ExteriorAlgebra R (Fin r → R)) z.2]
  exact hL

/-- There is a degreewise family of `S`-linear equivalences from the terms of
`seqComplexTensor (φ ∘ f) (S ⊗[R] M)` to those of `koszulComplexBaseChange f M` which commutes
with the differentials. -/
@[sga "6 VII 1.2" "partial"]
lemma koszulComplex_baseChange_chainComm (f : Fin r → R) (M : Type*) [AddCommGroup M] [Module R M] :
    ∃ e : ∀ n, (((seqComplexTensor (R := S) (fun j => algebraMap R S (f j)) (S ⊗[R] M)).X n))
          ≃ₗ[S] ((koszulComplexBaseChange (S := S) f M).X n),
      ∀ n m, ∀ x,
        (e m) (((seqComplexTensor (R := S) (fun j => algebraMap R S (f j)) (S ⊗[R] M)).d n m).hom x)
          = ((koszulComplexBaseChange (S := S) f M).d n m).hom ((e n) x) := by
  choose β hβ using fun n => extPow_baseChange_natEquiv (R := R) (S := S) (r := r) n
  let ePre : ∀ n, ((koszulComplexBaseChange (S := S) f M).X n)
      ≃ₗ[S] (((seqComplexTensor (R := S) (fun j => algebraMap R S (f j)) (S ⊗[R] M)).X n)) :=
    fun n => (TensorProduct.AlgebraTensorModule.distribBaseChange R S
        (⋀[R]^n (Fin r → R)) M).trans
        (TensorProduct.congr (β n) (LinearEquiv.refl S (S ⊗[R] M)))
  have hePre : ∀ (k : ℕ) (z : ⋀[R]^k (Fin r → R)) (mm : M),
      (ePre k) (1 ⊗ₜ[R] (z ⊗ₜ[R] mm)) = (β k (1 ⊗ₜ[R] z)) ⊗ₜ[S] (1 ⊗ₜ[R] mm) := by
    intro k z mm
    change (TensorProduct.congr (β k) (LinearEquiv.refl S (S ⊗[R] M)))
        ((TensorProduct.AlgebraTensorModule.distribBaseChange R S
          (⋀[R]^k (Fin r → R)) M) (1 ⊗ₜ[R] (z ⊗ₜ[R] mm))) = _
    rw [TensorProduct.AlgebraTensorModule.distribBaseChange_tmul, TensorProduct.congr_tmul,
      LinearEquiv.refl_apply]
  refine ⟨fun n => (ePre n).symm, ?_⟩
  intro n m x
  by_cases h : n = m + 1
  · subst h
    have square : ∀ w : (koszulComplexBaseChange (S := S) f M).X (m + 1),
        (LinearMap.rTensor (S ⊗[R] M) (d (seqDual fun j => algebraMap R S (f j)) m))
            ((ePre (m + 1)) w)
          = (ePre m)
              ((LinearMap.baseChange S (LinearMap.rTensor M (d (seqDual f) m))) w) := by
      have gen : ∀ (z : ⋀[R]^(m + 1) (Fin r → R)) (mm : M),
          (LinearMap.rTensor (S ⊗[R] M) (d (seqDual fun j => algebraMap R S (f j)) m))
              ((ePre (m + 1)) (1 ⊗ₜ[R] (z ⊗ₜ[R] mm)))
            = (ePre m) ((LinearMap.baseChange S (LinearMap.rTensor M (d (seqDual f) m)))
                (1 ⊗ₜ[R] (z ⊗ₜ[R] mm))) := by
        intro z mm
        rw [hePre, LinearMap.rTensor_tmul, LinearMap.baseChange_tmul, LinearMap.rTensor_tmul,
          hePre, d_baseChange_comm f β hβ m z]
      intro w
      induction w using TensorProduct.inductionOn with
      | tmul s t =>
        induction t using TensorProduct.inductionOn with
        | tmul z mm =>
          have hs : (s ⊗ₜ[R] (z ⊗ₜ[R] mm) : (koszulComplexBaseChange (S := S) f M).X (m + 1))
              = s • (1 ⊗ₜ[R] (z ⊗ₜ[R] mm)) := by
            rw [TensorProduct.smul_tmul', smul_eq_mul, mul_one]
          rw [hs, map_smul, map_smul, map_smul, map_smul, gen z mm]
        | add t1 t2 ht1 ht2 =>
          rw [TensorProduct.tmul_add, map_add, map_add, map_add, map_add, ht1, ht2]
      | add w1 w2 hw1 hw2 =>
        rw [map_add, map_add, map_add, map_add, hw1, hw2]
    change (ePre m).symm _ = _
    apply (ePre m).injective
    rw [LinearEquiv.apply_symm_apply]
    simp only [seqComplexTensor, koszulComplexBaseChange, ChainComplex.of_d, ModuleCat.hom_ofHom]
    have := square ((ePre (m+1)).symm x)
    rwa [LinearEquiv.apply_symm_apply] at this
  · have hC : ((seqComplexTensor (R := S) (fun j => algebraMap R S (f j)) (S ⊗[R] M)).d n m)
        = 0 := by
      apply HomologicalComplex.shape; simp only [ComplexShape.down_Rel]; omega
    have hD : ((koszulComplexBaseChange (S := S) f M).d n m) = 0 := by
      apply HomologicalComplex.shape; simp only [ComplexShape.down_Rel]; omega
    rw [hC, hD]; simp only [ModuleCat.hom_zero, LinearMap.zero_apply]; exact (ePre m).symm.map_zero

/-- The `i`-th homology of `seqComplexTensor (φ ∘ f) (S ⊗[R] M)` is `S`-linearly
isomorphic to the `i`-th homology of the termwise base change `koszulComplexBaseChange f M`. -/
@[sga "6 VII 1.2" "partial"]
lemma koszulComplex_baseChange_pillarA (f : Fin r → R) (M : Type*) [AddCommGroup M] [Module R M]
    (i : ℕ) :
    Nonempty
      (((seqComplexTensor (R := S) (fun j => algebraMap R S (f j)) (S ⊗[R] M)).homology i)
        ≃ₗ[S] ((koszulComplexBaseChange (S := S) f M).homology i)) := by
  obtain ⟨e, hcomm⟩ := koszulComplex_baseChange_chainComm (S := S) f M
  exact homologyTransport_of_degreewiseEquiv e hcomm i

/-- The differential of `koszulComplexBaseChange f M` is the `baseChange S` of the differential
of `seqComplexTensor f M`, in every (bi)degree. -/
lemma koszulComplexBaseChange_d_hom (f : Fin r → R) (M : Type*) [AddCommGroup M] [Module R M]
    (n m : ℕ) :
    ((koszulComplexBaseChange (S := S) f M).d n m).hom
      = LinearMap.baseChange S ((seqComplexTensor f M).d n m).hom := by
  by_cases h : (ComplexShape.down ℕ).Rel n m
  · obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨m, by simpa [ComplexShape.down_Rel] using h.symm⟩
    have hm : m = k := by simpa [ComplexShape.down_Rel] using h
    subst hm
    simp only [koszulComplexBaseChange, seqComplexTensor, ChainComplex.of_d, ModuleCat.hom_ofHom]
  · rw [HomologicalComplex.shape _ _ _ h, HomologicalComplex.shape _ _ _ h,
      ModuleCat.hom_zero, ModuleCat.hom_zero, LinearMap.baseChange_zero]

/-- Base change along a flat ring map `R → S` preserves exactness. -/
private theorem exact_baseChange_of_flat [Module.Flat R S] {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C] [Module R A] [Module R B] [Module R C]
    {f : A →ₗ[R] B} {g : B →ₗ[R] C} (h : Function.Exact f g) :
    Function.Exact (LinearMap.baseChange S f) (LinearMap.baseChange S g) := by
  simp only [LinearMap.baseChange_eq_lTensor]
  exact Module.Flat.lTensor_exact S h

/-- Let `S` be flat over `R`, let `f₁ : A → B` and `g₁ : B → C` be `R`-linear maps with
`g₁ ∘ f₁ = 0`, and let `f' : A' → B'` and `g' : B' → C'` be `S`-linear maps which `S`-linear
equivalences `A' ≃ S ⊗[R] A`, `B' ≃ S ⊗[R] B` and `C' ≃ S ⊗[R] C` identify with the base changes
of `f₁` and `g₁`. Then `ker g' / im f'` is `S`-linearly isomorphic to `S ⊗[R] (ker g₁ / im f₁)`. -/
lemma flat_homology_baseChange_of_linearEquiv [Module.Flat R S] {A B C : Type*}
    [AddCommGroup A] [AddCommGroup B] [AddCommGroup C]
    [Module R A] [Module R B] [Module R C]
    (f₁ : A →ₗ[R] B) (g₁ : B →ₗ[R] C)
    {A' B' C' : Type*} [AddCommGroup A'] [AddCommGroup B'] [AddCommGroup C']
    [Module S A'] [Module S B'] [Module S C']
    (f' : A' →ₗ[S] B') (g' : B' →ₗ[S] C')
    (e₁ : A' ≃ₗ[S] S ⊗[R] A) (e₂ : B' ≃ₗ[S] S ⊗[R] B) (e₃ : C' ≃ₗ[S] S ⊗[R] C)
    (hf : ∀ x, e₂ (f' x) = LinearMap.baseChange S f₁ (e₁ x))
    (hg : ∀ x, e₃ (g' x) = LinearMap.baseChange S g₁ (e₂ x))
    (memg' : ∀ a, f' a ∈ LinearMap.ker g')
    (memker : ∀ a, f₁ a ∈ LinearMap.ker g₁) :
    Nonempty (
      ( ↥(LinearMap.ker g') ⧸ (LinearMap.range
          (LinearMap.codRestrict (LinearMap.ker g') f' memg')) )
      ≃ₗ[S]
      S ⊗[R] ( ↥(LinearMap.ker g₁) ⧸ (LinearMap.range
          (LinearMap.codRestrict (LinearMap.ker g₁) f₁ memker))) ) := by
  set tc' := LinearMap.codRestrict (LinearMap.ker g') f' memg' with htc'
  set tc := LinearMap.codRestrict (LinearMap.ker g₁) f₁ memker with htc
  have hinj : Function.Injective (LinearMap.baseChange S (LinearMap.ker g₁).subtype) := by
    rw [LinearMap.baseChange_eq_lTensor]
    exact Module.Flat.lTensor_preserves_injective_linearMap _ Subtype.val_injective
  have hrange : LinearMap.range (LinearMap.baseChange S (LinearMap.ker g₁).subtype)
      = LinearMap.ker (LinearMap.baseChange S g₁) := by
    exact (exact_baseChange_of_flat (LinearMap.exact_subtype_ker_map g₁)).linearMap_ker_eq.symm
  have hmap : Submodule.map (e₂ : B' →ₗ[S] S ⊗[R] B) (LinearMap.ker g')
      = LinearMap.ker (LinearMap.baseChange S g₁) :=
    map_ker_of_comm e₂ e₃ hg
  let kerIso : (S ⊗[R] ↥(LinearMap.ker g₁)) ≃ₗ[S] ↥(LinearMap.ker (LinearMap.baseChange S g₁)) :=
    (LinearEquiv.ofInjective _ hinj).trans (LinearEquiv.ofEq _ _ hrange)
  let E : ↥(LinearMap.ker g') ≃ₗ[S] S ⊗[R] ↥(LinearMap.ker g₁) :=
    (e₂.submoduleMap (LinearMap.ker g')).trans
      ((LinearEquiv.ofEq _ _ hmap).trans kerIso.symm)
  let EL : ↥(LinearMap.ker g') →ₗ[S] S ⊗[R] ↥(LinearMap.ker g₁) := (E : _ →ₗ[S] _)
  have key : ∀ a', E (tc' a') = LinearMap.baseChange S tc (e₁ a') := by
    intro a'
    apply kerIso.injective
    have hL : (kerIso (E (tc' a')) : S ⊗[R] B) = e₂ (f' a') := by
      simp only [E, kerIso, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
        LinearEquiv.submoduleMap_apply, LinearEquiv.coe_ofEq_apply, htc',
        LinearMap.codRestrict_apply]
    have hR : (kerIso (LinearMap.baseChange S tc (e₁ a')) : S ⊗[R] B)
        = LinearMap.baseChange S f₁ (e₁ a') := by
      simp only [kerIso, LinearEquiv.trans_apply, LinearEquiv.coe_ofEq_apply,
        LinearEquiv.ofInjective_apply, htc]
      rw [← LinearMap.comp_apply, ← LinearMap.baseChange_comp]
      congr 1
    apply Subtype.ext
    rw [hL, hR, hf]
  have eq1 : Submodule.map EL (LinearMap.range tc')
      = LinearMap.range (LinearMap.baseChange S tc) := by
    rw [← LinearMap.range_comp]
    have hcomp : EL ∘ₗ tc' = (LinearMap.baseChange S tc) ∘ₗ (e₁ : A' →ₗ[S] S ⊗[R] A) := by
      ext a'; simp only [EL, LinearMap.comp_apply, LinearEquiv.coe_coe]; exact key a'
    rw [hcomp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr e₁.surjective, Submodule.map_top]
  have eq2 : LinearMap.range (LinearMap.baseChange S tc)
      = LinearMap.ker (LinearMap.baseChange S (LinearMap.range tc).mkQ) := by
    rw [(exact_baseChange_of_flat
      (LinearMap.exact_subtype_mkQ (LinearMap.range tc))).linearMap_ker_eq]
    conv_lhs => rw [show tc = (LinearMap.range tc).subtype ∘ₗ tc.rangeRestrict from rfl]
    rw [LinearMap.baseChange_comp, LinearMap.range_comp,
      LinearMap.range_eq_top.mpr (LinearMap.baseChange_surjective S
        (LinearMap.surjective_rangeRestrict tc)), Submodule.map_top]
  let stepA : (↥(LinearMap.ker g') ⧸ LinearMap.range tc') ≃ₗ[S]
      ((S ⊗[R] ↥(LinearMap.ker g₁)) ⧸ Submodule.map EL (LinearMap.range tc')) :=
    Submodule.Quotient.equiv (LinearMap.range tc')
      (Submodule.map EL (LinearMap.range tc')) E rfl
  let stepB : ((S ⊗[R] ↥(LinearMap.ker g₁)) ⧸ Submodule.map EL (LinearMap.range tc'))
      ≃ₗ[S] ((S ⊗[R] ↥(LinearMap.ker g₁)) ⧸ LinearMap.ker (LinearMap.baseChange S (LinearMap.range
          tc).mkQ)) :=
    Submodule.quotEquivOfEq _ _ (by rw [eq1, eq2])
  let stepC : ((S ⊗[R] ↥(LinearMap.ker g₁)) ⧸ LinearMap.ker (LinearMap.baseChange S
      (LinearMap.range tc).mkQ))
      ≃ₗ[S] (S ⊗[R] (↥(LinearMap.ker g₁) ⧸ LinearMap.range tc)) :=
    LinearMap.quotKerEquivOfSurjective _
      (LinearMap.baseChange_surjective S (Submodule.mkQ_surjective _))
  exact ⟨stepA.trans (stepB.trans stepC)⟩

/-- For `S` flat over `R`, the `i`-th homology of `koszulComplexBaseChange f M` is `S`-linearly
isomorphic to `S ⊗[R]` the `i`-th homology of `seqComplexTensor f M`. -/
lemma koszulComplex_baseChange_pillarB [Module.Flat R S] (f : Fin r → R) (M : Type*)
    [AddCommGroup M] [Module R M] (i : ℕ) :
    Nonempty
      (((koszulComplexBaseChange (S := S) f M).homology i)
        ≃ₗ[S] (S ⊗[R] ((seqComplexTensor f M).homology i))) := by
  set C := seqComplexTensor f M
  set C' := koszulComplexBaseChange (S := S) f M
  have hf : ((C'.sc i).f).hom = LinearMap.baseChange S ((C.sc i).f).hom :=
    koszulComplexBaseChange_d_hom f M _ i
  have hg : ((C'.sc i).g).hom = LinearMap.baseChange S ((C.sc i).g).hom :=
    koszulComplexBaseChange_d_hom f M i _
  have hz' : ∀ a, ((C'.sc i).f).hom a ∈ LinearMap.ker ((C'.sc i).g).hom :=
    fun a => LinearMap.mem_ker.mpr (ShortComplex.zero_apply (C'.sc i) a)
  have hzR : ∀ a, ((C.sc i).f).hom a ∈ LinearMap.ker ((C.sc i).g).hom :=
    fun a => LinearMap.mem_ker.mpr (ShortComplex.zero_apply (C.sc i) a)
  obtain ⟨eAbs⟩ := flat_homology_baseChange_of_linearEquiv (R := R) (S := S)
    ((C.sc i).f).hom ((C.sc i).g).hom
    ((C'.sc i).f).hom ((C'.sc i).g).hom
    (LinearEquiv.refl S (↑((C'.sc i).X₁))) (LinearEquiv.refl S (↑((C'.sc i).X₂)))
    (LinearEquiv.refl S (↑((C'.sc i).X₃)))
    (fun x => LinearMap.congr_fun hf x)
    (fun x => LinearMap.congr_fun hg x)
    hz' hzR
  refine ⟨((C'.sc i).moduleCatHomologyIso).toLinearEquiv.trans (eAbs.trans
    (TensorProduct.AlgebraTensorModule.congr (LinearEquiv.refl S S)
      ((C.sc i).moduleCatHomologyIso).toLinearEquiv.symm))⟩

/-- For `S` flat over `R`, the `i`-th homology of `seqComplexTensor (φ ∘ f) (S ⊗[R] M)` is
`S`-linearly isomorphic to `S ⊗[R]` the `i`-th homology of `seqComplexTensor f M`. -/
lemma homology_baseChange_linearEquiv [Module.Flat R S] (f : Fin r → R) (M : Type*) [AddCommGroup M]
    [Module R M] (i : ℕ) :
    Nonempty
      (((seqComplexTensor (R := S) (fun j => algebraMap R S (f j)) (S ⊗[R] M)).homology i)
        ≃ₗ[S] (S ⊗[R] ((seqComplexTensor f M).homology i))) := by
  obtain ⟨eA⟩ := koszulComplex_baseChange_pillarA (S := S) f M i
  obtain ⟨eB⟩ := koszulComplex_baseChange_pillarB (S := S) f M i
  exact ⟨eA.trans eB⟩

/-- If the `i`-th Koszul homology over `R` is a subsingleton, so is the `i`-th homology of the
base-changed complex over `S`. -/
lemma homology_baseChange_subsingleton [Module.Flat R S] (f : Fin r → R) (M : Type*)
    [AddCommGroup M] [Module R M] (i : ℕ)
    (hi : Subsingleton ((seqComplexTensor f M).homology i)) :
    Subsingleton
      ((seqComplexTensor (R := S) (fun j => algebraMap R S (f j)) (S ⊗[R] M)).homology i) := by
  obtain ⟨e⟩ := homology_baseChange_linearEquiv (S := S) f M i
  exact e.toEquiv.subsingleton

/-- Flat base change preserves the vanishing of Koszul homology: if `H_i(K_•(f) ⊗_R M)` is zero,
then so is `H_i(K_•(φ(f)) ⊗_S (S ⊗_R M))`. -/
theorem homology_isZero_baseChange [Module.Flat R S] (f : Fin r → R) (M : Type*)
    [AddCommGroup M] [Module R M]
    (i : ℕ) (hi : Limits.IsZero ((seqComplexTensor f M).homology i)) :
    Limits.IsZero
      ((seqComplexTensor (R := S) (fun j => algebraMap R S (f j)) (S ⊗[R] M)).homology i) := by
  rw [ModuleCat.isZero_iff_subsingleton] at hi ⊢
  exact homology_baseChange_subsingleton f M i hi

/-- For a flat ring map `φ : R → S`, if `f_1, ..., f_r` is `M`-`H_1`-regular over `R`, then
`φ(f_1), ..., φ(f_r)` is `(S ⊗_R M)`-`H_1`-regular over `S`. -/
@[stacks 062H "(1)"]
theorem isH1Regular_baseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] {r : ℕ} (f : Fin r → R) (M : Type*) [AddCommGroup M] [Module R M]
    (hf : IsH1RegularOn f M) :
    IsH1RegularOn (R := S) (fun i => algebraMap R S (f i)) (S ⊗[R] M) :=
  homology_isZero_baseChange f M 1 hf

/-- For a flat ring map `φ : R → S`, if `f_1, ..., f_r` is `M`-Koszul-regular over `R`, then
`φ(f_1), ..., φ(f_r)` is `(S ⊗_R M)`-Koszul-regular over `S`. -/
@[stacks 062H "(2)", sga "6 VII 1.5" "special case", sga "6 VIII 1.3" "VII 1.5, special case"]
theorem isKoszulRegular_baseChange {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Module.Flat R S] {r : ℕ} (f : Fin r → R) (M : Type*) [AddCommGroup M] [Module R M]
    (hf : IsKoszulRegularOn f M) :
    IsKoszulRegularOn (R := S) (fun i => algebraMap R S (f i)) (S ⊗[R] M) :=
  fun i hi => homology_isZero_baseChange f M i (hf i hi)

end KoszulC

namespace Koszul

/-- Weak regularity of a sequence is transported along a ring isomorphism. -/
public theorem isWeaklyRegular_ringEquiv {R S : Type*} [CommRing R] [CommRing S]
    (e : R ≃+* S) (l : List R) :
    RingTheory.Sequence.IsWeaklyRegular R l ↔
      RingTheory.Sequence.IsWeaklyRegular S (l.map e) := by
  apply e.toAddEquiv.isWeaklyRegular_congr
  apply List.forall₂_map_right_iff.mpr
  apply List.forall₂_same.mpr
  intro r _ x
  exact e.map_mul r x

end Koszul
