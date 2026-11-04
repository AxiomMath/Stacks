module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.MatrixAlgebraSections
public import StacksFrontier.LinearAlgebra.Matrix.AlternatingProjectorImage

/-!
# The alternating projector as an endomorphism of a free sheaf of modules

Let `S` be a scheme and let `R₀ S = End (𝟙_ (ModuleSheaf S))` be the commutative ring of
endomorphisms of `𝒪_S` as a sheaf of `𝒪_S`-modules. Two matrix dictionaries for the
endomorphisms of a finite free sheaf of `𝒪_S`-modules are already available and were so far
unrelated. `Stacks.EtaleCohomology.BrauerScheme.freeDualMatrix` is the *dual basis* dictionary:
the `(a, b)` entry of the matrix of `f` is `freeInj a ≫ f ≫ freeProj b`, defined for an arbitrary
index type in the universe of the sheaf of modules.
`Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv` is the *biproduct* dictionary, defined
for an index type in `Type 0` by conjugating with the identification `freeBiproductIso` of the
free sheaf with a finite direct sum of copies of the unit and reading off biproduct components;
it is the dictionary the Kronecker law and the tensor-power computations are stated in.

The first half of this file shows the two dictionaries agree, after the universe lift: the
tautological point `freeInj (ULift.up i)` is carried by `freeBiproductIso` to the biproduct
inclusion `biproduct.ι i`, and dually the composite of `freeBiproductIso` with the biproduct
projection `biproduct.π j` is the tautological coordinate `freeProj (ULift.up j)`. Conjugating
the defining formula for a biproduct component by those two identities turns it into
`freeInj (ULift.up i) ≫ f ≫ freeProj (ULift.up j)`, which is the dual basis entry.

The second half uses the dual basis dictionary, where rank-one endomorphisms are easy, to produce
the projector of [Stacks, Tag 0A2L] on a free sheaf of modules. A vector `v : I → R₀ S` of
coefficients gives a point `vecPoint v = ∑ i, v i ≫ freeInj i` and a covector
`vecCovec v = ∑ i, freeProj i ≫ v i`, the pairing `vecPoint v ≫ vecCovec w` is the dot product
`∑ i, v i * w i`, and the matrix of the rank-one endomorphism `vecCovec w ≫ vecPoint v` is the
outer product `(a, b) ↦ w a * v b`. Taking for `v` and `w` the alternating vector
`Matrix.altVec (R₀ S)` on the index type `Fin d → Fin d` of the `d`-fold tensor power therefore
produces an endomorphism `altProjFree S d` of the free sheaf of modules of rank `d ^ d` whose
matrix is exactly `Matrix.altProj (R₀ S)` — in both dictionaries, by the bridge. The standard
basis covector `Matrix.altCoordVec` at the identity index pairs to `1` with the alternating
vector, so the two cross pairings of the alternating point and covector with their standard
basis partners are the identity of the unit; this is the splitting that makes the image of the
projector free.

## Main definitions

* `Stacks.EtaleCohomology.BrauerScheme.vecPoint` and
  `Stacks.EtaleCohomology.BrauerScheme.vecCovec`: the point and the covector of a finite free
  sheaf of `𝒪_S`-modules attached to a vector of coefficients in `R₀ S`.
* `Stacks.EtaleCohomology.BrauerScheme.altPointFree`,
  `Stacks.EtaleCohomology.BrauerScheme.altCovecFree`,
  `Stacks.EtaleCohomology.BrauerScheme.altCoordPointFree` and
  `Stacks.EtaleCohomology.BrauerScheme.altCoordCovecFree`: the alternating point and covector of
  the free sheaf of modules of rank `d ^ d`, and their standard basis partners.
* `Stacks.EtaleCohomology.BrauerScheme.altProjFree`: the projector of [Stacks, Tag 0A2L] as an
  endomorphism of the free sheaf of modules of rank `d ^ d`.

## Main results

* `Stacks.EtaleCohomology.BrauerScheme.freeDualMatrix_eq_freeEndMatrixEquiv`: **the two matrix
  dictionaries for endomorphisms of a finite free sheaf of modules agree.**
* `Stacks.EtaleCohomology.BrauerScheme.freeInj_comp_freeBiproductIso_hom` and
  `Stacks.EtaleCohomology.BrauerScheme.freeBiproductIso_hom_comp_biproduct_π`: the two halves of
  that agreement — `freeBiproductIso` matches the tautological points and coordinates with the
  biproduct inclusions and projections.
* `Stacks.EtaleCohomology.BrauerScheme.vecPoint_comp_vecCovec`: the pairing of a point and a
  covector is the dot product of their coefficient vectors.
* `Stacks.EtaleCohomology.BrauerScheme.freeDualMatrix_vecCovec_comp_vecPoint`: the matrix of a
  rank-one endomorphism is the outer product of its coefficient vectors.
* `Stacks.EtaleCohomology.BrauerScheme.altPointFree_comp_altCoordCovecFree` and
  `Stacks.EtaleCohomology.BrauerScheme.altCoordPointFree_comp_altCovecFree`: **the two cross
  pairings of the alternating pair are the identity of the unit.**
* `Stacks.EtaleCohomology.BrauerScheme.freeDualMatrix_altProjFree` and
  `Stacks.EtaleCohomology.BrauerScheme.freeEndMatrixEquiv_altProjFree`: **the matrix of
  `altProjFree` is `Matrix.altProj`**, in each of the two dictionaries.

## Implementation notes

**Why the first lemma is an application of an abstract one.** A goal mentioning
`freeModule S I` carries `Stacks.SheafOfModules.Tensor.ringSheaf S.sheaf`, whose argument fits
only after `TopCat.Sheaf` is unfolded; that unfolding is unavailable at the `implicit`
transparency `rw` and `simp` check their motives at, so once `freeBiproductIso` and
`SheafOfModules.ιFree` have been unfolded no further rewrite — not even `Iso.trans_hom` — is
accepted. `CategoryTheory.Limits.Sigma.ι_comp_whiskerEquiv_isoCoproduct` therefore states the
computation for an abstract category, where everything rewrites, and
`freeInj_comp_freeBiproductIso_hom` is an application of it elaborated at default transparency.
The same consideration turns the two pairing identities into `exact`s rather than `rw`s. This is
the convention of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.EndAlgebraFreePoints`.

**`HasFiniteBiproducts (ModuleSheaf S)` and `MonoidalPreadditive (ModuleSheaf S)`** are
re-enabled from `MatrixFreeSheaf` with `attribute [local instance]` rather than restated: the two
declarations there are `local instance`s, hence ordinary declarations downstream, and restating
them collides.

## References

* [Stacks Project, Tag 0A2L](https://stacks.math.columbia.edu/tag/0A2L)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory AlgebraicGeometry TopologicalSpace
open Stacks.SheafOfModules

universe u

noncomputable section

namespace CategoryTheory.Limits

/-- **The reindexing isomorphism of a coproduct, followed by the comparison with the biproduct,
carries the `j`-th coproduct inclusion to the `e j`-th biproduct inclusion**, up to the chosen
isomorphism of the factors. This is the shape
`Stacks.EtaleCohomology.BrauerScheme.freeBiproductIso` is built in; it is stated here, for an
abstract category, because the scheme-level statement cannot be rewritten in — see the
implementation notes of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BrauerGroupScheme.AltProjectorFreeSheaf`. -/
lemma Sigma.ι_comp_whiskerEquiv_isoCoproduct {C : Type*} [Category C] [HasZeroMorphisms C]
    {J K : Type*} (f : J → C) (g : K → C) [HasCoproduct f] [HasCoproduct g] [HasBiproduct g]
    (e : J ≃ K) (w : ∀ j, g (e j) ≅ f j) (j : J) :
    Sigma.ι f j ≫ (Sigma.whiskerEquiv e w ≪≫ (biproduct.isoCoproduct g).symm).hom
      = (w j).inv ≫ biproduct.ι g (e j) := by
  simp

end CategoryTheory.Limits

namespace Stacks.EtaleCohomology.BrauerScheme

attribute [local instance] hasFiniteBiproductsModuleSheaf monoidalPreadditiveModuleSheaf

/-! ### The dictionary bridge -/

/-- The identification of a finite free sheaf of modules with a direct sum of copies of `𝒪_S`
carries the `i`-th tautological point to the `i`-th biproduct inclusion. -/
theorem freeInj_comp_freeBiproductIso_hom (S : Scheme.{u}) (I : Type) [Finite I] (i : I) :
    freeInj (S := S) (ULift.up i) ≫ (freeBiproductIso S I).hom
      = Limits.biproduct.ι (fun _ : I => 𝟙_ (ModuleSheaf S)) i := by
  have h := Limits.Sigma.ι_comp_whiskerEquiv_isoCoproduct
    (fun _ : ULift.{u, 0} I => _root_.SheafOfModules.unit (Tensor.ringSheaf S.sheaf))
    (fun _ : I => 𝟙_ (ModuleSheaf S)) (Equiv.ulift (α := I))
    (fun _ => Iso.refl (𝟙_ (ModuleSheaf S))) (ULift.up i)
  exact h.trans (Category.id_comp _)

/-- The identification of a finite free sheaf of modules with a direct sum of copies of `𝒪_S`
carries the `i`-th biproduct inclusion back to the `i`-th tautological point. -/
@[reassoc]
theorem biproduct_ι_comp_freeBiproductIso_inv (S : Scheme.{u}) (I : Type) [Finite I] (i : I) :
    Limits.biproduct.ι (fun _ : I => 𝟙_ (ModuleSheaf S)) i ≫ (freeBiproductIso S I).inv
      = freeInj (S := S) (ULift.up i) := by
  rw [← freeInj_comp_freeBiproductIso_hom, Category.assoc, Iso.hom_inv_id, Category.comp_id]

/-- The identification of a finite free sheaf of modules with a direct sum of copies of `𝒪_S`
carries the `j`-th biproduct projection to the `j`-th tautological coordinate. -/
theorem freeBiproductIso_hom_comp_biproduct_π (S : Scheme.{u}) (I : Type) [Finite I]
    [DecidableEq I] (j : I) :
    (freeBiproductIso S I).hom ≫ Limits.biproduct.π (fun _ : I => 𝟙_ (ModuleSheaf S)) j
      = freeProj (S := S) (ULift.up j) := by
  refine freeModule_hom_ext_inj fun k => ?_
  obtain ⟨i⟩ := k
  rw [← Category.assoc, freeInj_comp_freeBiproductIso_hom, freeInj_comp_freeProj]
  rcases eq_or_ne i j with rfl | h
  · rw [Limits.biproduct.ι_π_self, ite_eq_left rfl]
  · rw [Limits.biproduct.ι_π_ne _ h,
      ite_eq_right (fun hh : ULift.up i = ULift.up j => h (congrArg ULift.down hh))]

/-- **The two matrix dictionaries for endomorphisms of a finite free sheaf of `𝒪_S`-modules
agree.** The dual basis entry `freeInj (ULift.up i) ≫ f ≫ freeProj (ULift.up j)` is the `(i, j)`
biproduct component of `f` read through `freeBiproductIso`. -/
theorem freeDualMatrix_eq_freeEndMatrixEquiv (S : Scheme.{u}) (I : Type) [Finite I]
    [DecidableEq I]
    (f : freeModule S (ULift.{u, 0} I) ⟶ freeModule S (ULift.{u, 0} I)) (i j : I) :
    freeDualMatrix f (ULift.up i) (ULift.up j) = freeEndMatrixEquiv S I f i j := by
  have := Fintype.ofFinite I
  rw [freeEndMatrixEquiv_apply, unitMatrixEquiv_apply, Limits.biproduct.components]
  simp only [freeDualMatrix, dualBasisMatrix_apply, Category.assoc]
  rw [biproduct_ι_comp_freeBiproductIso_inv_assoc, freeBiproductIso_hom_comp_biproduct_π]

/-! ### Points and covectors from vectors of coefficients -/

variable {S : Scheme.{u}}

/-- The point of the free sheaf of modules on `I` with coordinates `v`. -/
def vecPoint {I : Type u} [Fintype I] (v : I → R₀ S) :
    𝟙_ (ModuleSheaf S) ⟶ freeModule S I := ∑ i : I, v i ≫ freeInj i

/-- The covector of the free sheaf of modules on `I` with coordinates `w`. -/
def vecCovec {I : Type u} [Fintype I] [DecidableEq I] (w : I → R₀ S) :
    freeModule S I ⟶ 𝟙_ (ModuleSheaf S) := ∑ i : I, freeProj i ≫ w i

/-- A covector reads off the coefficient at a tautological point. -/
theorem freeInj_comp_vecCovec {I : Type u} [Fintype I] [DecidableEq I] (w : I → R₀ S) (a : I) :
    freeInj (S := S) a ≫ vecCovec w = w a := by
  rw [vecCovec, Preadditive.comp_sum,
    Finset.sum_eq_single_of_mem a (Finset.mem_univ a)
      (fun b _ hb => by
        rw [← Category.assoc, freeInj_comp_freeProj, ite_eq_right (Ne.symm hb), Limits.zero_comp]),
    ← Category.assoc, freeInj_comp_freeProj, ite_eq_left rfl, Category.id_comp]

/-- A tautological coordinate reads off the coefficient of a point. -/
theorem vecPoint_comp_freeProj {I : Type u} [Fintype I] [DecidableEq I] (v : I → R₀ S) (b : I) :
    vecPoint v ≫ freeProj b = v b := by
  rw [vecPoint, Preadditive.sum_comp,
    Finset.sum_eq_single_of_mem b (Finset.mem_univ b)
      (fun c _ hc => by
        rw [Category.assoc, freeInj_comp_freeProj, ite_eq_right hc, Limits.comp_zero]),
    Category.assoc, freeInj_comp_freeProj, ite_eq_left rfl, Category.comp_id]

/-- **The pairing of a point and a covector is the dot product of their coefficient vectors.** -/
theorem vecPoint_comp_vecCovec {I : Type u} [Fintype I] [DecidableEq I] (v w : I → R₀ S) :
    vecPoint v ≫ vecCovec w = ∑ i : I, v i * w i := by
  rw [vecPoint, Preadditive.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Category.assoc, freeInj_comp_vecCovec, unitEnd_mul_eq_comp]

/-- **The matrix of the rank-one endomorphism `vecCovec w ≫ vecPoint v` is the outer product of
the two coefficient vectors.** -/
theorem freeDualMatrix_vecCovec_comp_vecPoint {I : Type u} [Fintype I] [DecidableEq I]
    (v w : I → R₀ S) (a b : I) :
    freeDualMatrix (vecCovec w ≫ vecPoint v) a b = w a * v b := by
  simp only [freeDualMatrix, dualBasisMatrix_apply, Category.assoc]
  rw [vecPoint_comp_freeProj, ← Category.assoc, freeInj_comp_vecCovec, unitEnd_mul_eq_comp]

/-! ### The alternating projector on the free sheaf of modules of rank `d ^ d` -/

/-- The alternating point of the free sheaf of modules of rank `d ^ d`. -/
def altPointFree (S : Scheme.{u}) (d : ℕ) :
    𝟙_ (ModuleSheaf S) ⟶ freeModule S (ULift.{u, 0} (Fin d → Fin d)) :=
  vecPoint (fun k => Matrix.altVec (R₀ S) k.down)

/-- The alternating covector. -/
def altCovecFree (S : Scheme.{u}) (d : ℕ) :
    freeModule S (ULift.{u, 0} (Fin d → Fin d)) ⟶ 𝟙_ (ModuleSheaf S) :=
  vecCovec (fun k => Matrix.altVec (R₀ S) k.down)

/-- The standard-basis point at the identity index. -/
def altCoordPointFree (S : Scheme.{u}) (d : ℕ) :
    𝟙_ (ModuleSheaf S) ⟶ freeModule S (ULift.{u, 0} (Fin d → Fin d)) :=
  vecPoint (fun k => Matrix.altCoordVec (R₀ S) (Fin d) k.down)

/-- The standard-basis covector at the identity index. -/
def altCoordCovecFree (S : Scheme.{u}) (d : ℕ) :
    freeModule S (ULift.{u, 0} (Fin d → Fin d)) ⟶ 𝟙_ (ModuleSheaf S) :=
  vecCovec (fun k => Matrix.altCoordVec (R₀ S) (Fin d) k.down)

/-- The pairing of the point and the covector with coefficients `a ∘ down` and `b ∘ down` is
the identity of the unit when `∑ g, a g * b g = 1`. -/
private theorem vecPoint_comp_vecCovec_ulift_eq_id {J : Type} [Fintype J] [DecidableEq J]
    (a b : J → R₀ S) (h : ∑ g, a g * b g = 1) :
    vecPoint (fun k : ULift.{u, 0} J => a k.down) ≫ vecCovec (fun k : ULift.{u, 0} J => b k.down)
      = 𝟙 (𝟙_ (ModuleSheaf S)) := by
  rw [vecPoint_comp_vecCovec, ← End.one_def, ← h]
  exact Fintype.sum_equiv (Equiv.ulift (α := J)) _ _ fun _ => rfl

/-- **The alternating point pairs to the identity of the unit with the standard-basis
covector**, because the coordinate of the alternating vector at the identity index is `1`. -/
theorem altPointFree_comp_altCoordCovecFree (S : Scheme.{u}) (d : ℕ) :
    altPointFree S d ≫ altCoordCovecFree S d = 𝟙 (𝟙_ (ModuleSheaf S)) :=
  vecPoint_comp_vecCovec_ulift_eq_id _ _ Matrix.sum_altVec_mul_altCoordVec

/-- **The standard-basis point pairs to the identity of the unit with the alternating
covector.** -/
theorem altCoordPointFree_comp_altCovecFree (S : Scheme.{u}) (d : ℕ) :
    altCoordPointFree S d ≫ altCovecFree S d = 𝟙 (𝟙_ (ModuleSheaf S)) :=
  vecPoint_comp_vecCovec_ulift_eq_id _ _ Matrix.sum_altCoordVec_mul_altVec

/-- The alternating projector of [Stacks, Tag 0A2L] as an endomorphism of the free sheaf of
modules of rank `d ^ d`: the rank-one endomorphism built from the alternating covector and the
alternating point. -/
def altProjFree (S : Scheme.{u}) (d : ℕ) :
    freeModule S (ULift.{u, 0} (Fin d → Fin d)) ⟶ freeModule S (ULift.{u, 0} (Fin d → Fin d)) :=
  altCovecFree S d ≫ altPointFree S d

/-- **The matrix of the alternating projector is `Matrix.altProj`** — in the `freeDualMatrix`
dictionary. -/
theorem freeDualMatrix_altProjFree (S : Scheme.{u}) (d : ℕ) (k l : ULift.{u, 0} (Fin d → Fin d)) :
    freeDualMatrix (altProjFree S d) k l = Matrix.altProj (R₀ S) k.down l.down := by
  rw [Matrix.altProj_apply]
  simp only [altProjFree, altCovecFree, altPointFree]
  exact freeDualMatrix_vecCovec_comp_vecPoint _ _ k l

/-- **The matrix of the alternating projector is `Matrix.altProj`** — in the
`freeEndMatrixEquiv` dictionary. -/
theorem freeEndMatrixEquiv_altProjFree (S : Scheme.{u}) (d : ℕ) :
    freeEndMatrixEquiv S (Fin d → Fin d) (altProjFree S d) = Matrix.altProj (R₀ S) := by
  funext k l
  rw [← freeDualMatrix_eq_freeEndMatrixEquiv, freeDualMatrix_altProjFree]

end Stacks.EtaleCohomology.BrauerScheme

end

end
