module

public import Mathlib.Algebra.Category.ModuleCat.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Monoidal.Basic
public import Mathlib.Algebra.Homology.Embedding.RestrictionHomology
public import Mathlib.Algebra.Homology.Monoidal
public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.AlgebraicTopology.AlternatingFaceMapComplex
public import Mathlib.CategoryTheory.Monoidal.FunctorCategory
public import Mathlib.LinearAlgebra.Alternating.Uncurry.Fin
public import Mathlib.LinearAlgebra.DirectSum.Finsupp
public import Mathlib.LinearAlgebra.ExteriorAlgebra.Basis
public import Mathlib.LinearAlgebra.SymmetricAlgebra.Basis
public import Mathlib.LinearAlgebra.TensorProduct.DirectLimit
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.Flat.Stability
public import Mathlib.RingTheory.MvPolynomial.Ideal
public import StacksFrontier.Algebra.Category.ModuleCat.Monoidal.LargeUniverse
public import StacksFrontier.Algebra.Homology.Resolution.ProjectiveResolution
public import StacksFrontier.Algebra.Homology.SpectralSequence.FilteredComplex.Basic
public import StacksFrontier.AlgebraicTopology.SimplicialTensorConnectivity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolutionOfModules
public import StacksFrontier.Homology.KFlat.Flat
public import StacksFrontier.Homology.Tor.DerivedTensor
public import StacksFrontier.Homology.Tor.DerivedTensorUniverse
public import StacksFrontier.LinearAlgebra.SymmetricPower.Free
public import StacksFrontier.LinearAlgebra.SymmetricPower.Presentation
public import StacksFrontier.RingTheory.Flat.Lazard
public import StacksFrontier.RingTheory.Koszul.DifferentialGradedAlgebra
public import StacksFrontier.RingTheory.Koszul.FlatBaseChange
public import StacksFrontier.RingTheory.Koszul.Regular
public import StacksFrontier.RingTheory.TensorAlgebra.Colimit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.SymmetricPowerVanishing.HomogeneousKoszulComplex
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of the Koszul complex of a flat module

Exterior powers, symmetric algebras and tensor products commute with direct limits; hence, by
Lazard's theorem, the Koszul complex `∧^• M ⊗ Sym(M)` of a flat module `M` is exact in every
positive degree.

This file is one part of `SymmetricPowerVanishing`, which imports all of them.
-/

@[expose] public noncomputable section

open scoped DirectSum TensorProduct

open CategoryTheory CategoryTheory.Limits AlgebraicTopology

namespace Stacks.ChaoticSite

universe u v w

attribute [local instance] HasDerivedCategory.standard

universe z

/-- The projection `∧_R(M) → ∧^p_R(M)` onto the homogeneous component of degree `p`. -/
def exteriorPowerProjection (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] (p : ℕ) :
    ExteriorAlgebra R M →ₗ[R] (⋀[R]^p M) where
  toFun x := ⟨(ExtPow.degreeMap x).coeff p, ExtPow.coeff_degreeMap_mem x p⟩
  map_add' x y := by apply Subtype.ext; simp
  map_smul' r x := by apply Subtype.ext; simp

/-- The projection onto `∧^p_R(M)` restricts to the identity on `∧^p_R(M)`. -/
lemma exteriorPowerProjection_subtype (R M : Type*) [CommRing R]
    [AddCommGroup M] [Module R M] (p : ℕ) :
    (exteriorPowerProjection R M p).comp (Submodule.subtype (⋀[R]^p M)) = LinearMap.id := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change (ExtPow.degreeMap (x : ExteriorAlgebra R M)).coeff p = x
  rw [ExtPow.degreeMap_eq_of_mem p _ x.property]
  simp

/-- The projection onto `∧^p` is natural in the module. -/
lemma exteriorPowerProjection_naturality {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (p : ℕ) (x : ExteriorAlgebra R M) :
    exteriorPowerProjection R N p (ExteriorAlgebra.map f x) =
      exteriorPower.map p f (exteriorPowerProjection R M p x) := by
  have hh : (ExtPow.degreeMap (R := R) (M := N)).comp (ExteriorAlgebra.map f) =
      (Polynomial.mapAlgHom (ExteriorAlgebra.map f)).comp ExtPow.degreeMap := by
    apply ExteriorAlgebra.hom_ext
    ext m
    simp [ExtPow.degreeMap_ι]
  apply Subtype.ext
  rw [exteriorPower.coe_map]
  change (ExtPow.degreeMap (ExteriorAlgebra.map f x)).coeff p =
    ExteriorAlgebra.map f ((ExtPow.degreeMap x).coeff p)
  have := congrArg (fun t => (t x).coeff p) hh
  simpa using this

section Colimit
variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι]
  [DecidableEq ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  {G : ι → Type w} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
  [DirectedSystem G (fun i j h => f i j h)]

/-- A compatible family `cᵢ : Gᵢ → L` that is jointly surjective, and whose kernels are killed by
the transition maps, identifies `L` with the direct limit of the `Gᵢ`. -/
def directLimitEquivOfRepresentation
    {L : Type*} [AddCommGroup L] [Module R L]
    (c : ∀ i, G i →ₗ[R] L)
    (hc : ∀ i j h x, c j (f i j h x) = c i x)
    (hsurj : ∀ x, ∃ i y, c i y = x)
    (hzero : ∀ i y, c i y = 0 → ∃ j, ∃ hij : i ≤ j, f i j hij y = 0) :
    Module.DirectLimit G f ≃ₗ[R] L :=
  LinearEquiv.ofBijective (Module.DirectLimit.lift R ι G f c hc) (by
    constructor
    · intro x y hxy
      obtain ⟨i, z, hz⟩ := Module.DirectLimit.exists_of (x - y)
      have hcz : c i z = 0 := by
        rw [← Module.DirectLimit.lift_of c hc z, hz, map_sub, hxy, sub_self]
      obtain ⟨j, hij, hj⟩ := hzero i z hcz
      apply sub_eq_zero.mp
      rw [← hz, ← Module.DirectLimit.of_f (f := f) (hij := hij) (x := z), hj, map_zero]
    · intro x
      obtain ⟨i, y, rfl⟩ := hsurj x
      exact ⟨Module.DirectLimit.of R ι G f i y, Module.DirectLimit.lift_of c hc y⟩)

omit [DirectedSystem G fun i j h ↦ ⇑(f i j h)] in
/-- `directLimitEquivOfRepresentation` sends the image of `x : Gᵢ` to `cᵢ x`. -/
lemma directLimitEquivOfRepresentation_of
    {L : Type*} [AddCommGroup L] [Module R L]
    (c : ∀ i, G i →ₗ[R] L)
    (hc : ∀ i j h x, c j (f i j h x) = c i x)
    (hsurj : ∀ x, ∃ i y, c i y = x)
    (hzero : ∀ i y, c i y = 0 → ∃ j, ∃ hij : i ≤ j, f i j hij y = 0)
    (i : ι) (x : G i) :
    directLimitEquivOfRepresentation f c hc hsurj hzero (Module.DirectLimit.of R ι G f i x) =
      c i x := by
  change (Module.DirectLimit.lift R ι G f c hc) (Module.DirectLimit.of R ι G f i x) = c i x
  exact Module.DirectLimit.lift_of c hc x

/-- Every element of `Sym_R(lim Gᵢ)` comes from `Sym_R(Gᵢ)` for some `i`. -/
lemma symmetricAlgebra_directLimit_exists
    (x : SymmetricAlgebra R (Module.DirectLimit G f)) :
    ∃ i y, symmetricAlgebraMap (Module.DirectLimit.of R ι G f i) y = x := by
  obtain ⟨⟨i, y⟩, hy⟩ := Quotient.exists_rep ((SymmetricAlgebra.equivDirectLimit f) x)
  refine ⟨i, y, ?_⟩
  have hh := congrArg (SymmetricAlgebra.equivDirectLimit f).symm hy
  simpa only [SymmetricAlgebra.equivDirectLimit, AlgEquiv.ofAlgHom_symm_apply,
    SymmetricAlgebra.ofDirectLimit_mk, AlgEquiv.symm_apply_apply] using hh

/-- An element of `Sym_R(Gᵢ)` vanishing in `Sym_R(lim Gᵢ)` already vanishes in `Sym_R(Gⱼ)` for
some `j ≥ i`. -/
lemma symmetricAlgebra_directLimit_zero (i : ι) (y : SymmetricAlgebra R (G i))
    (hy : symmetricAlgebraMap (Module.DirectLimit.of R ι G f i) y = 0) :
    ∃ j, ∃ hij : i ≤ j, symmetricAlgebraMap (f i j hij) y = 0 := by
  have hh : (⟦⟨i, y⟩⟧ : SymmetricColim f) = 0 := by
    apply (SymmetricAlgebra.ofDirectLimit_bijective f).injective
    simpa using hy
  exact (DirectLimit.exists_eq_zero (f := fun i j h => symmetricTrans f i j h) ⟨i, y⟩).mp hh

/-- Every element of `∧_R(lim Gᵢ)` comes from `∧_R(Gᵢ)` for some `i`. -/
lemma exteriorAlgebra_directLimit_exists (x : ExteriorAlgebra R (Module.DirectLimit G f)) :
    ∃ i y, ExteriorAlgebra.map (Module.DirectLimit.of R ι G f i) y = x := by
  obtain ⟨⟨i, y⟩, hy⟩ := Quotient.exists_rep ((ExteriorAlgebra.equivDirectLimit f) x)
  refine ⟨i, y, ?_⟩
  have hh := congrArg (ExteriorAlgebra.equivDirectLimit f).symm hy
  simpa only [ExteriorAlgebra.equivDirectLimit, AlgEquiv.ofAlgHom_symm_apply,
    ExteriorAlgebra.ofDirectLimit_mk, AlgEquiv.symm_apply_apply] using hh

/-- An element of `∧_R(Gᵢ)` vanishing in `∧_R(lim Gᵢ)` already vanishes in `∧_R(Gⱼ)` for some
`j ≥ i`. -/
lemma exteriorAlgebra_directLimit_zero (i : ι) (y : ExteriorAlgebra R (G i))
    (hy : ExteriorAlgebra.map (Module.DirectLimit.of R ι G f i) y = 0) :
    ∃ j, ∃ hij : i ≤ j, ExteriorAlgebra.map (f i j hij) y = 0 := by
  have hh : (⟦⟨i, y⟩⟧ : ExteriorColim f) = 0 := by
    apply (ExteriorAlgebra.ofDirectLimit_bijective f).injective
    simpa using hy
  exact (DirectLimit.exists_eq_zero (f := exteriorTrans f) ⟨i, y⟩).mp hh

/-- Every element of `∧^p_R(lim Gᵢ)` comes from `∧^p_R(Gᵢ)` for some `i`. -/
lemma exteriorPower_directLimit_exists (p : ℕ)
    (x : ⋀[R]^p (Module.DirectLimit G f)) :
    ∃ i y, exteriorPower.map p (Module.DirectLimit.of R ι G f i) y = x := by
  obtain ⟨i, y, hy⟩ := exteriorAlgebra_directLimit_exists f (x : ExteriorAlgebra R _)
  refine ⟨i, exteriorPowerProjection R (G i) p y, ?_⟩
  rw [← exteriorPowerProjection_naturality, hy]
  exact LinearMap.congr_fun (exteriorPowerProjection_subtype R _ p) x

/-- An element of `∧^p_R(Gᵢ)` vanishing in `∧^p_R(lim Gᵢ)` already vanishes in `∧^p_R(Gⱼ)` for
some `j ≥ i`. -/
lemma exteriorPower_directLimit_zero (p : ℕ) (i : ι) (y : ⋀[R]^p (G i))
    (hy : exteriorPower.map p (Module.DirectLimit.of R ι G f i) y = 0) :
    ∃ j, ∃ hij : i ≤ j, exteriorPower.map p (f i j hij) y = 0 := by
  obtain ⟨j, hij, hj⟩ := exteriorAlgebra_directLimit_zero f i y.val (by
    simpa using congrArg Subtype.val hy)
  refine ⟨j, hij, ?_⟩
  apply Subtype.ext
  simpa using hj

/-- The transition map of a directed system from an index to itself is the identity. -/
private theorem transition_self_eq_id {κ : Type*} [Preorder κ] {K : κ → Type*}
    [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] (F : (i j : κ) → i ≤ j → K i →ₗ[R] K j)
    [DirectedSystem K (fun i j h => F i j h)] (i : κ) : F i i le_rfl = LinearMap.id :=
  LinearMap.ext fun y => DirectedSystem.map_self (f := fun i j h => F i j h) y

/-- Transition maps of a directed system compose. -/
private theorem transition_comp_eq {κ : Type*} [Preorder κ] {K : κ → Type*}
    [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)] (F : (i j : κ) → i ≤ j → K i →ₗ[R] K j)
    [DirectedSystem K (fun i j h => F i j h)] {i j k : κ} (hij : i ≤ j) (hjk : j ≤ k) :
    (F j k hjk).comp (F i j hij) = F i k (hij.trans hjk) :=
  LinearMap.ext fun y => DirectedSystem.map_map (f := fun i j h => F i j h) hij hjk y

omit [DecidableEq ι] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- The `p`th exterior powers of a directed system of modules form a directed system. -/
lemma exteriorPower_directedSystem (p : ℕ) :
    DirectedSystem (fun i => ⋀[R]^p (G i))
      (fun i j h => exteriorPower.map p (f i j h)) := by
  constructor
  · intro i x
    rw [transition_self_eq_id f i, exteriorPower.map_id, LinearMap.id_apply]
  · intro k j i hij hjk x
    rw [← LinearMap.comp_apply, ← exteriorPower.map_comp, transition_comp_eq f hij hjk]

/-- Exterior powers commute with direct limits: `lim ∧^p_R(Gᵢ) ≃ ∧^p_R(lim Gᵢ)`. -/
def exteriorPowerDirectLimitEquiv (p : ℕ) :
    Module.DirectLimit (fun i => ⋀[R]^p (G i))
      (fun i j h => exteriorPower.map p (f i j h)) ≃ₗ[R]
        (⋀[R]^p (Module.DirectLimit G f)) := by
  have := exteriorPower_directedSystem f p
  refine directLimitEquivOfRepresentation _
    (fun i => exteriorPower.map p (Module.DirectLimit.of R ι G f i)) ?_
    (exteriorPower_directLimit_exists f p) (exteriorPower_directLimit_zero f p)
  intro i j h x
  rw [← LinearMap.comp_apply, ← exteriorPower.map_comp]
  have hh : (Module.DirectLimit.of R ι G f j).comp (f i j h) =
      Module.DirectLimit.of R ι G f i := LinearMap.ext fun y => Module.DirectLimit.of_f
  rw [hh]

/-- `exteriorPowerDirectLimitEquiv` sends the image of `x : ∧^p_R(Gᵢ)` to `∧^p` of the canonical
map `Gᵢ → lim Gᵢ` applied to `x`. -/
lemma exteriorPowerDirectLimitEquiv_of (p : ℕ) (i : ι) (x : ⋀[R]^p (G i)) :
    exteriorPowerDirectLimitEquiv f p
      (Module.DirectLimit.of R ι (fun i => ⋀[R]^p (G i))
        (fun i j h => exteriorPower.map p (f i j h)) i x) =
      exteriorPower.map p (Module.DirectLimit.of R ι G f i) x :=
  by
    have := exteriorPower_directedSystem f p
    simp only [exteriorPowerDirectLimitEquiv, directLimitEquivOfRepresentation_of]

omit [DecidableEq ι] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- The symmetric algebras of a directed system of modules form a directed system. -/
lemma symmetricAlgebra_directedSystem :
    DirectedSystem (fun i => SymmetricAlgebra R (G i))
      (fun i j h => (symmetricAlgebraMap (f i j h)).toLinearMap) :=
  { map_self := fun {_i} x =>
      DirectedSystem.map_self (f := fun i j h => symmetricTrans f i j h) x
    map_map := fun {_k _j _i} hij hjk x =>
      DirectedSystem.map_map (f := fun i j h => symmetricTrans f i j h) hij hjk x }

/-- Symmetric algebras commute with direct limits: `lim Sym_R(Gᵢ) ≃ Sym_R(lim Gᵢ)`. -/
def symmetricAlgebraDirectLimitEquiv :
    Module.DirectLimit (fun i => SymmetricAlgebra R (G i))
      (fun i j h => (symmetricAlgebraMap (f i j h)).toLinearMap) ≃ₗ[R]
        SymmetricAlgebra R (Module.DirectLimit G f) := by
  have := symmetricAlgebra_directedSystem f
  refine directLimitEquivOfRepresentation _
    (fun i => (symmetricAlgebraMap (Module.DirectLimit.of R ι G f i)).toLinearMap) ?_
    (symmetricAlgebra_directLimit_exists f) (symmetricAlgebra_directLimit_zero f)
  intro i j h x
  change symmetricAlgebraMap (Module.DirectLimit.of R ι G f j)
    (symmetricAlgebraMap (f i j h) x) = symmetricAlgebraMap (Module.DirectLimit.of R ι G f i) x
  rw [← AlgHom.comp_apply, symmetricAlgebraMap_comp]
  have hh : (Module.DirectLimit.of R ι G f j).comp (f i j h) =
      Module.DirectLimit.of R ι G f i := LinearMap.ext fun y => Module.DirectLimit.of_f
  rw [hh]

/-- `symmetricAlgebraDirectLimitEquiv` sends the image of `x : Sym_R(Gᵢ)` to `Sym` of the
canonical map `Gᵢ → lim Gᵢ` applied to `x`. -/
lemma symmetricAlgebraDirectLimitEquiv_of (i : ι) (x : SymmetricAlgebra R (G i)) :
    symmetricAlgebraDirectLimitEquiv f
      (Module.DirectLimit.of R ι (fun i => SymmetricAlgebra R (G i))
        (fun i j h => (symmetricAlgebraMap (f i j h)).toLinearMap) i x) =
      symmetricAlgebraMap (Module.DirectLimit.of R ι G f i) x :=
  by
    have := symmetricAlgebra_directedSystem f
    dsimp only [symmetricAlgebraDirectLimitEquiv]
    apply directLimitEquivOfRepresentation_of

end Colimit
section Colimit
variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι]
  [DecidableEq ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  {G : ι → Type w} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
  [DirectedSystem G (fun i j h => f i j h)]
  {H : ι → Type z} [∀ i, AddCommGroup (H i)] [∀ i, Module R (H i)]
  (g : (i j : ι) → i ≤ j → H i →ₗ[R] H j)
  [DirectedSystem H (fun i j h => g i j h)]

omit [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] [DirectedSystem G fun i j h ↦ ⇑(f i j h)] in
/-- The canonical maps into a direct limit are compatible with the transition maps. -/
lemma directLimit_of_comp {i j : ι} (h : i ≤ j) :
    (Module.DirectLimit.of R ι G f j).comp (f i j h) = Module.DirectLimit.of R ι G f i :=
  LinearMap.ext fun _x => Module.DirectLimit.of_f

/-- `directLimitRight` identifies `L ⊗ of` with the canonical map into the direct limit of the
`L ⊗ Hᵢ`. -/
private theorem directLimitRight_comp_lTensor {κ : Type*} [Preorder κ] [DecidableEq κ]
    {K : κ → Type*} [∀ i, AddCommGroup (K i)] [∀ i, Module R (K i)]
    (F : (i j : κ) → i ≤ j → K i →ₗ[R] K j) (L : Type*) [AddCommGroup L] [Module R L] (j : κ) :
    (TensorProduct.directLimitRight F L).toLinearMap.comp
        ((Module.DirectLimit.of R κ K F j).lTensor L) =
      Module.DirectLimit.of R κ (fun j => L ⊗[R] K j) (fun j k h => (F j k h).lTensor L) j := by
  apply TensorProduct.ext
  ext a b
  exact TensorProduct.directLimitRight_tmul_of F L a b

omit [DirectedSystem G fun i j h ↦ ⇑(f i j h)] [DirectedSystem H fun i j h ↦ ⇑(g i j h)] in
/-- Every element of `(lim Gᵢ) ⊗ (lim Hᵢ)` comes from `Gᵢ ⊗ Hᵢ` for some `i`. -/
lemma tensorDirectLimit_exists
    (x : Module.DirectLimit G f ⊗[R] Module.DirectLimit H g) :
    ∃ i y, TensorProduct.map (Module.DirectLimit.of R ι G f i)
      (Module.DirectLimit.of R ι H g i) y = x := by
  obtain ⟨i, a, ha⟩ := Module.DirectLimit.exists_of
    (TensorProduct.directLimitLeft f (Module.DirectLimit H g) x)
  have ha' : (Module.DirectLimit.of R ι G f i).rTensor (Module.DirectLimit H g) a = x := by
    apply (TensorProduct.directLimitLeft f _).injective
    rwa [TensorProduct.directLimitLeft_rTensor_of]
  obtain ⟨j, b, hb⟩ := Module.DirectLimit.exists_of (TensorProduct.directLimitRight g (G i) a)
  have hb' : (Module.DirectLimit.of R ι H g j).lTensor (G i) b = a := by
    apply (TensorProduct.directLimitRight g _).injective
    exact (LinearMap.congr_fun (directLimitRight_comp_lTensor g (G i) j) b).trans hb
  obtain ⟨k, hik, hjk⟩ := exists_ge_ge i j
  refine ⟨k, TensorProduct.map (f i k hik) (g j k hjk) b, ?_⟩
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp,
    directLimit_of_comp, directLimit_of_comp,
    ← LinearMap.rTensor_comp_lTensor, LinearMap.comp_apply, hb', ha']

omit [DecidableEq ι] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- Tensoring a directed system on the right with a fixed module gives a directed system. -/
lemma rTensor_directedSystem (L : Type*) [AddCommGroup L] [Module R L] :
    DirectedSystem (fun i => G i ⊗[R] L) (fun i j h => (f i j h).rTensor L) := by
  constructor
  · intro i x
    rw [transition_self_eq_id f i, LinearMap.rTensor_id_apply]
  · intro k j i hij hjk x
    rw [← LinearMap.rTensor_comp_apply, transition_comp_eq f hij hjk]

omit [DecidableEq ι] [IsDirected ι fun x1 x2 ↦ x1 ≤ x2] [Nonempty ι] in
/-- Tensoring a directed system on the left with a fixed module gives a directed system. -/
lemma lTensor_directedSystem (L : Type*) [AddCommGroup L] [Module R L] :
    DirectedSystem (fun i => L ⊗[R] G i) (fun i j h => (f i j h).lTensor L) := by
  constructor
  · intro i x
    rw [transition_self_eq_id f i, LinearMap.lTensor_id_apply]
  · intro k j i hij hjk x
    rw [← LinearMap.lTensor_comp_apply, transition_comp_eq f hij hjk]

omit [Nonempty ι] in
/-- An element of `Gᵢ ⊗ Hᵢ` vanishing in `(lim Gᵢ) ⊗ (lim Hᵢ)` already vanishes in `Gⱼ ⊗ Hⱼ` for
some `j ≥ i`. -/
lemma tensorDirectLimit_zero (i : ι) (x : G i ⊗[R] H i)
    (hx : TensorProduct.map (Module.DirectLimit.of R ι G f i)
      (Module.DirectLimit.of R ι H g i) x = 0) :
    ∃ j, ∃ hij : i ≤ j, TensorProduct.map (f i j hij) (g i j hij) x = 0 := by
  have := rTensor_directedSystem f (Module.DirectLimit H g)
  have hz : Module.DirectLimit.of R ι (fun j => G j ⊗[R] Module.DirectLimit H g)
      (fun j k h => (f j k h).rTensor (Module.DirectLimit H g)) i
      ((Module.DirectLimit.of R ι H g i).lTensor (G i) x) = 0 := by
    rw [← TensorProduct.directLimitLeft_rTensor_of, ← LinearMap.comp_apply,
      LinearMap.rTensor_comp_lTensor, hx, map_zero]
  obtain ⟨j, hij, hj⟩ := Module.DirectLimit.of.zero_exact hz
  have hj' : (Module.DirectLimit.of R ι H g i).lTensor (G j)
      ((f i j hij).rTensor (H i) x) = 0 := by
    rwa [← LinearMap.comp_apply, LinearMap.rTensor_comp_lTensor,
      ← LinearMap.lTensor_comp_rTensor, LinearMap.comp_apply] at hj
  have := lTensor_directedSystem g (G j)
  have hz' : Module.DirectLimit.of R ι (fun k => G j ⊗[R] H k)
      (fun k l h => (g k l h).lTensor (G j)) i ((f i j hij).rTensor (H i) x) = 0 := by
    rw [← directLimitRight_comp_lTensor g (G j) i, LinearMap.comp_apply, hj', map_zero]
  obtain ⟨k, hik, hk⟩ := Module.DirectLimit.of.zero_exact hz'
  obtain ⟨l, hjl, hkl⟩ := exists_ge_ge j k
  refine ⟨l, hij.trans hjl, ?_⟩
  rw [← LinearMap.comp_apply, LinearMap.lTensor_comp_rTensor] at hk
  have hh := congrArg (TensorProduct.map (f j l hjl) (g k l hkl)) hk
  rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, map_zero] at hh
  rwa [transition_comp_eq f hij hjl, transition_comp_eq g hik hkl] at hh

end Colimit

/-- The map `∧^p M ⊗ Sym_R(M) → ∧^p N ⊗ Sym_R(N)` induced by a linear map `f : M → N`. -/
abbrev symmetricKoszulMap {R M N : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (f : M →ₗ[R] N) (p : ℕ) :=
  TensorProduct.map (exteriorPower.map p f) (symmetricAlgebraMap f).toLinearMap

/-- `symmetricKoszulMap` is functorial. -/
lemma symmetricKoszulMap_comp {R M N P : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    [AddCommGroup P] [Module R P] (f : M →ₗ[R] N) (g : N →ₗ[R] P) (p : ℕ) :
    (symmetricKoszulMap g p).comp (symmetricKoszulMap f p) =
      symmetricKoszulMap (g.comp f) p := by
  unfold symmetricKoszulMap
  rw [← TensorProduct.map_comp, ← exteriorPower.map_comp]
  congr 1
  apply LinearMap.ext
  intro x
  exact congrArg (fun t : SymmetricAlgebra R M →ₐ[R] SymmetricAlgebra R P => t x)
    (symmetricAlgebraMap_comp f g)

section KoszulColimit
variable {R : Type u} [CommRing R] {ι : Type v} [Preorder ι]
  [DecidableEq ι] [IsDirected ι (· ≤ ·)] [Nonempty ι]
  {G : ι → Type w} [∀ i, AddCommGroup (G i)] [∀ i, Module R (G i)]
  (f : (i j : ι) → i ≤ j → G i →ₗ[R] G j)
  [DirectedSystem G (fun i j h => f i j h)]

/-- The identification `(lim ∧^p Gᵢ) ⊗ (lim Sym_R(Gᵢ)) ≃ ∧^p(lim Gᵢ) ⊗ Sym_R(lim Gᵢ)` sends
the image of an element of `∧^p Gᵢ ⊗ Sym_R(Gᵢ)` to its image under the canonical map
`Gᵢ → lim Gᵢ`. -/
lemma symmetricKoszulDirectLimitEquiv_map (p : ℕ) (i : ι)
    (x : (⋀[R]^p (G i)) ⊗[R] SymmetricAlgebra R (G i)) :
    (TensorProduct.congr (exteriorPowerDirectLimitEquiv f p)
      (symmetricAlgebraDirectLimitEquiv f))
      (TensorProduct.map
        (Module.DirectLimit.of R ι (fun i => ⋀[R]^p (G i))
          (fun i j h => exteriorPower.map p (f i j h)) i)
        (Module.DirectLimit.of R ι (fun i => SymmetricAlgebra R (G i))
          (fun i j h => (symmetricAlgebraMap (f i j h)).toLinearMap) i) x) =
      symmetricKoszulMap (Module.DirectLimit.of R ι G f i) p x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul a b => simp [exteriorPowerDirectLimitEquiv_of, symmetricAlgebraDirectLimitEquiv_of]
  | add a b ha hb => simp [ha, hb]

/-- Every element of `∧^p(lim Gᵢ) ⊗ Sym_R(lim Gᵢ)` comes from `∧^p Gᵢ ⊗ Sym_R(Gᵢ)` for some
`i`. -/
lemma symmetricKoszul_directLimit_exists (p : ℕ)
    (x : (⋀[R]^p (Module.DirectLimit G f)) ⊗[R]
      SymmetricAlgebra R (Module.DirectLimit G f)) :
    ∃ i y, symmetricKoszulMap (Module.DirectLimit.of R ι G f i) p y = x := by
  have := exteriorPower_directedSystem f p
  have := symmetricAlgebra_directedSystem f
  let e := TensorProduct.congr (exteriorPowerDirectLimitEquiv f p)
    (symmetricAlgebraDirectLimitEquiv f)
  obtain ⟨i, y, hy⟩ := tensorDirectLimit_exists
    (fun i j h => exteriorPower.map p (f i j h))
    (fun i j h => (symmetricAlgebraMap (f i j h)).toLinearMap) (e.symm x)
  refine ⟨i, y, ?_⟩
  rw [← symmetricKoszulDirectLimitEquiv_map]
  change e _ = x
  rw [hy, e.apply_symm_apply]

/-- An element of `∧^p Gᵢ ⊗ Sym_R(Gᵢ)` vanishing in `∧^p(lim Gᵢ) ⊗ Sym_R(lim Gᵢ)` already
vanishes in `∧^p Gⱼ ⊗ Sym_R(Gⱼ)` for some `j ≥ i`. -/
lemma symmetricKoszul_directLimit_zero (p : ℕ) (i : ι)
    (x : (⋀[R]^p (G i)) ⊗[R] SymmetricAlgebra R (G i))
    (hx : symmetricKoszulMap (Module.DirectLimit.of R ι G f i) p x = 0) :
    ∃ j, ∃ hij : i ≤ j, symmetricKoszulMap (f i j hij) p x = 0 := by
  have := exteriorPower_directedSystem f p
  have := symmetricAlgebra_directedSystem f
  let e := TensorProduct.congr (exteriorPowerDirectLimitEquiv f p)
    (symmetricAlgebraDirectLimitEquiv f)
  have hh : TensorProduct.map
      (Module.DirectLimit.of R ι (fun i => ⋀[R]^p (G i))
        (fun i j h => exteriorPower.map p (f i j h)) i)
      (Module.DirectLimit.of R ι (fun i => SymmetricAlgebra R (G i))
        (fun i j h => (symmetricAlgebraMap (f i j h)).toLinearMap) i) x = 0 := by
    apply e.injective
    rw [map_zero]
    exact (symmetricKoszulDirectLimitEquiv_map f p i x).trans hx
  exact tensorDirectLimit_zero
    (fun i j h => exteriorPower.map p (f i j h))
    (fun i j h => (symmetricAlgebraMap (f i j h)).toLinearMap) i x hh

/-- If each Koszul complex `∧^• Gᵢ ⊗ Sym_R(Gᵢ)` is exact at degree `p + 1`, then so is the Koszul
complex of the direct limit `lim Gᵢ`. -/
lemma symmetricKoszul_exact_directLimit (p : ℕ)
    (h : ∀ i, Function.Exact (symmetricKoszulDifferential R (G i) (p + 1))
      (symmetricKoszulDifferential R (G i) p)) :
    Function.Exact (symmetricKoszulDifferential R (Module.DirectLimit G f) (p + 1))
      (symmetricKoszulDifferential R (Module.DirectLimit G f) p) := by
  intro x
  constructor
  · intro hx
    obtain ⟨i, y, hy⟩ := symmetricKoszul_directLimit_exists f (p + 1) x
    have hz : symmetricKoszulMap (Module.DirectLimit.of R ι G f i) p
        (symmetricKoszulDifferential R (G i) p y) = 0 := by
      rw [← LinearMap.comp_apply, symmetricKoszulDifferential_naturality,
        LinearMap.comp_apply, hy, hx]
    obtain ⟨j, hij, hj⟩ := symmetricKoszul_directLimit_zero f p i _ hz
    have hj' : symmetricKoszulDifferential R (G j) p
        (symmetricKoszulMap (f i j hij) (p + 1) y) = 0 := by
      rwa [← LinearMap.comp_apply, symmetricKoszulDifferential_naturality,
        LinearMap.comp_apply] at hj
    obtain ⟨z, hz⟩ := (h j _).mp hj'
    refine ⟨symmetricKoszulMap (Module.DirectLimit.of R ι G f j) (p + 1 + 1) z, ?_⟩
    rw [← LinearMap.comp_apply, ← symmetricKoszulDifferential_naturality,
      LinearMap.comp_apply, hz, ← LinearMap.comp_apply, symmetricKoszulMap_comp,
      directLimit_of_comp, hy]
  · rintro ⟨z, rfl⟩
    apply LinearMap.congr_fun (koszulDifferential_comp
      (symmetricKoszulAction R (Module.DirectLimit G f))
      (symmetricKoszulAction R (Module.DirectLimit G f)) ?_ p) z
    intro x y z
    exact mul_left_comm _ _ _

end KoszulColimit
/-- For a flat module `M`, the Koszul complex `∧^• M ⊗ Sym_R(M)` is exact in every positive
degree. -/
lemma symmetricKoszul_exact_of_flat
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (p : ℕ) :
    Function.Exact (symmetricKoszulDifferential R M (p + 1))
      (symmetricKoszulDifferential R M p) := by
  obtain ⟨ι, hpre, hdir, hne, hdec, G, hag, hmod, f, hds, hfree, hfinite, ⟨e⟩⟩ :=
    flat_exists_directLimit_finiteFree R M
  apply symmetricKoszul_exact_of_equiv e.symm p
  apply symmetricKoszul_exact_directLimit f p
  intro i
  have := hfree i
  have := hfinite i
  exact symmetricKoszul_exact_of_finite_free R (G i) p

/-- For a flat module `M`, the homogeneous Koszul complex is exact at
`∧^{p+1} M ⊗ Sym^{q+1} M`. -/
lemma homogeneousKoszul_exact_of_flat
    (R M : Type*) [CommRing R] [AddCommGroup M] [Module R M]
    [Module.Flat R M] (p q : ℕ) :
    Function.Exact (homogeneousKoszulDifferential R M (p + 1) q)
      (homogeneousKoszulDifferential R M p (q + 1)) :=
  homogeneousKoszul_exact_of_symmetricKoszul_exact R M p q
    (symmetricKoszul_exact_of_flat R M p)

end Stacks.ChaoticSite

end
