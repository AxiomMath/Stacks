module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Euler characteristic of a complex is the Euler characteristic of its homology

Let `K` be a homological complex of vector spaces over a field `k`, of a complex shape `c` in
which every index has a successor given by a bijection `σ` of the index type (`c.Rel i (σ i)`
for all `i`), with signs alternating along `c`. If every term of `K` is finite-dimensional and
only finitely many terms are nonzero, then the alternating sum of the dimensions of the terms
agrees with the alternating sum of the dimensions of the homology:

`∑ᵢ χ(i) dim Hᵢ(K) = ∑ᵢ χ(i) dim Kᵢ`.

The shapes covered include `ComplexShape.up ℤ` and `ComplexShape.down ℤ`, with `σ = (· ± 1)`,
and the shapes `ComplexShape.up' v` of an additive group, with `σ = (· + v)`; the latter are the
shapes of the pages of a spectral sequence.

## Main results

* `HomologicalComplex.homologyEulerChar_eq_eulerChar_of_rel`: the identity above.

## Implementation notes

The pointwise input is the rank identity `dim Hᵢ + dim (im d_in) + dim (im d_out) = dim Kᵢ`,
from the quotient description `CategoryTheory.ShortComplex.moduleCatHomologyIso` of the homology
of a short complex of modules and rank-nullity. The image of the differential into `σ i` is the
image of the differential out of `i`, so after reindexing along `σ`, which flips the sign, the
image terms cancel.

The module universe is arbitrary: the homology of a complex of vector spaces over `k : Type u`
may live in `ModuleCat.{v} k` for any `v`, as it does for the cohomology of a sheaf on a site
whose objects lie in a larger universe than its sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u v

namespace HomologicalComplex

variable {k : Type u} [Field k]

/-- **The rank identity for a short complex of finite-dimensional vector spaces.** The
dimension of the middle term is the dimension of the homology plus the dimensions of the images
of the two maps. -/
theorem finrank_homology_add_finrank_range_f_add_finrank_range_g
    (S : ShortComplex (ModuleCat.{v} k)) [Module.Finite k S.X₂] :
    Module.finrank k S.homology + Module.finrank k S.f.hom.range +
      Module.finrank k S.g.hom.range = Module.finrank k S.X₂ := by
  let L := S.moduleCatToCycles
  have hq : Module.finrank k (LinearMap.ker S.g.hom ⧸ LinearMap.range L) +
      Module.finrank k (LinearMap.range L) = Module.finrank k (LinearMap.ker S.g.hom) :=
    (LinearMap.range L).finrank_quotient_add_finrank
  have hiso : Module.finrank k S.homology =
      Module.finrank k (LinearMap.ker S.g.hom ⧸ LinearMap.range L) :=
    S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  have hrange : Module.finrank k (LinearMap.range L) = Module.finrank k S.f.hom.range := by
    have hcomp : (LinearMap.ker S.g.hom).subtype ∘ₗ L = S.f.hom := rfl
    rw [← hcomp, LinearMap.range_comp, Submodule.finrank_map_subtype_eq]
  have hg := S.g.hom.finrank_range_add_finrank_ker
  omega

/-- A linear map out of a zero module has zero-dimensional image. -/
theorem finrank_range_eq_zero_of_isZero {M N : ModuleCat.{v} k} (f : M ⟶ N) (hM : IsZero M) :
    Module.finrank k f.hom.range = 0 := by
  have := ModuleCat.isZero_iff_subsingleton.mp hM
  exact Nat.le_zero.mp (f.hom.finrank_range_le.trans_eq Module.finrank_zero_of_subsingleton)

/-- A zero module has dimension zero. -/
theorem finrank_eq_zero_of_isZero {M : ModuleCat.{v} k} (hM : IsZero M) :
    Module.finrank k M = 0 :=
  have := ModuleCat.isZero_iff_subsingleton.mp hM
  Module.finrank_zero_of_subsingleton

variable {ι : Type*} {c : ComplexShape ι} [c.EulerCharSigns]

/-- **The Euler characteristic of a complex of finite-dimensional vector spaces with finitely
many nonzero terms is computed by its homology**, for a complex shape in which every index `i`
has the successor `σ i`, for a bijection `σ` of the indices. -/
@[ega "III 7.9.2" "Case where A is a field"]
theorem homologyEulerChar_eq_eulerChar_of_rel (σ : ι ≃ ι) (hσ : ∀ i, c.Rel i (σ i))
    (K : HomologicalComplex (ModuleCat.{v} k) c) (hfin : ∀ i, Module.Finite k (K.X i))
    (hsupp : {i | ¬ IsZero (K.X i)}.Finite) :
    K.homologyEulerChar = K.eulerChar := by
  classical
  have hnext (i : ι) : c.next i = σ i := c.next_eq' (hσ i)
  have hprev (i : ι) : c.prev (σ i) = i := c.prev_eq' (hσ i)
  let sg (i : ι) : ℤ := (c.χ i : ℤ)
  let cr (i : ι) : ℕ := Module.finrank k (K.X i)
  let hr (i : ι) : ℕ := Module.finrank k (K.sc i).homology
  let dr (i : ι) : ℕ := Module.finrank k (K.sc i).g.hom.range
  let dp (i : ι) : ℕ := Module.finrank k (K.sc i).f.hom.range
  have hsgσ (i : ι) : sg (σ i) = -sg i := by
    simpa [sg] using congrArg (fun x : ℤˣ => (x : ℤ)) (c.χ_next (hσ i))
  have hsub {r : ι → ℕ} (hr0 : ∀ i, IsZero (K.X i) → r i = 0) :
      (Function.support fun i => sg i * (r i : ℤ)).Finite :=
    hsupp.subset fun i hi hz => hi (by simp [hr0 i hz])
  have hwc := hsub (r := cr) fun i hz => finrank_eq_zero_of_isZero hz
  have hwh := hsub (r := hr) fun i hz =>
    finrank_eq_zero_of_isZero (ShortComplex.isZero_homology_of_isZero_X₂ (K.sc i) hz)
  have hwd := hsub (r := dr) fun i hz => finrank_range_eq_zero_of_isZero (K.sc i).g hz
  have hboundary (i : ι) : dp (σ i) = dr i := by
    dsimp only [dp, dr]
    let φ : (K.sc (σ i)).X₁ ≅ (K.sc i).X₂ := K.XIsoOfEq (hprev i)
    let ψ : (K.sc (σ i)).X₂ ≅ (K.sc i).X₃ := K.XIsoOfEq (hnext i).symm
    have hcomm : (K.sc (σ i)).f ≫ ψ.hom = φ.hom ≫ (K.sc i).g := by
      show K.d _ _ ≫ (K.XIsoOfEq _).hom = (K.XIsoOfEq _).hom ≫ K.d _ _
      rw [HomologicalComplex.d_comp_XIsoOfEq_hom, HomologicalComplex.XIsoOfEq_hom_comp_d]
    have hrange : (K.sc (σ i)).f.hom.range.map ψ.toLinearEquiv.toLinearMap =
        (K.sc i).g.hom.range := by
      rw [← LinearMap.range_comp, show ψ.toLinearEquiv.toLinearMap ∘ₗ (K.sc (σ i)).f.hom =
        (K.sc i).g.hom ∘ₗ φ.toLinearEquiv.toLinearMap from congrArg ModuleCat.Hom.hom hcomm]
      exact LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range φ.toLinearEquiv)
    rw [← hrange, LinearEquiv.finrank_map_eq]
  have hpoint (i : ι) : (hr i : ℤ) + dp i + dr i = cr i := by
    have : Module.Finite k (K.sc i).X₂ := hfin i
    exact_mod_cast finrank_homology_add_finrank_range_f_add_finrank_range_g (K.sc i)
  have hwdp : (Function.support fun i => sg i * (dp i : ℤ)).Finite := by
    refine (hwd.image σ).subset fun j hj => ⟨σ.symm j, fun hz => hj ?_, by simp⟩
    have hsg := hsgσ (σ.symm j)
    rw [σ.apply_symm_apply] at hsg
    simpa [← hboundary (σ.symm j), hsg] using hz
  have hshift : (∑ᶠ i, sg i * (dp i : ℤ)) = -∑ᶠ i, sg i * (dr i : ℤ) := by
    rw [← finsum_comp_equiv σ, ← finsum_neg_distrib]
    exact finsum_congr fun i => by rw [hboundary, hsgσ, neg_mul]
  have hsum : (∑ᶠ i, sg i * (hr i : ℤ)) + (∑ᶠ i, sg i * (dp i : ℤ)) +
      ∑ᶠ i, sg i * (dr i : ℤ) = ∑ᶠ i, sg i * (cr i : ℤ) := by
    rw [← finsum_add_distrib hwh hwdp, ← finsum_add_distrib ((hwh.union hwdp).subset
      (Function.support_add _ _)) hwd]
    exact finsum_congr fun i => by rw [← hpoint i]; ring
  show (∑ᶠ i, sg i * (hr i : ℤ)) = ∑ᶠ i, sg i * (cr i : ℤ)
  linarith

end HomologicalComplex

end
