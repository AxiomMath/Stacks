module

public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.Homology.EulerCharacteristic
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The Euler characteristic of a bounded complex of finite-dimensional vector spaces

For a cochain complex `C` of `k`-vector spaces, indexed by `ℤ`, whose terms are all
finite-dimensional and all but finitely many of which vanish, the alternating sum of the
dimensions of the cohomology groups agrees with the alternating sum of the dimensions of the
terms.

## Main results

* `StacksDraft.Perfect.homologyEulerChar_eq_eulerChar`: for such a complex,
  `∑ (-1)^i dim H^i(C) = ∑ (-1)^i dim C^i`.

## Implementation notes

Both sides are the `finsum` Euler characteristics of
`Mathlib/Algebra/Homology/EulerCharacteristic`, so the two sums are over all of `ℤ` and each is `0`
unless the relevant support is finite. The finiteness hypothesis is therefore used twice: once to
make the sums the finite sums they are meant to be, and once in the telescoping step.

The pointwise input is the rank identity
`dim H^i + dim (im d^{i-1}) + dim (im d^i) = dim C^i`, obtained from the quotient description
`ShortComplex.moduleCatHomologyIso` of the homology of a short complex of modules together with
the rank-nullity theorem.  Summing it with signs and using
`dim (im d^{i-1}) = dim (im d^{i-1})` read at the two short complexes `C.sc i` and `C.sc (i-1)`
makes the two image terms cancel after an index shift, which is the telescoping.

## References

* [Stacks Project, Tag 0BDJ](https://stacks.math.columbia.edu/tag/0BDJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace StacksDraft.Perfect

universe u

/-- The dimension of a linear map's image is unchanged by linear equivalences on its source and
target that commute with it. -/
private theorem finrank_range_eq_of_linearEquiv {k : Type*} [Field k]
    {M M' N N' : Type*} [AddCommGroup M] [Module k M]
    [AddCommGroup M'] [Module k M'] [AddCommGroup N] [Module k N]
    [AddCommGroup N'] [Module k N']
    (f : M →ₗ[k] N) (g : M' →ₗ[k] N')
    (eM : M ≃ₗ[k] M') (eN : N ≃ₗ[k] N')
    (hcomm : ∀ x, eN (f x) = g (eM x)) :
    Module.finrank k f.range = Module.finrank k g.range := by
  let L : f.range →ₗ[k] g.range :=
    { toFun := fun y => ⟨eN y, by
        rcases y.property with ⟨x, hx⟩
        exact ⟨eM x, by simpa [hx] using (hcomm x).symm⟩⟩
      map_add' x y := Subtype.ext (eN.map_add x y)
      map_smul' a x := Subtype.ext (eN.map_smul a x) }
  have hbij : Function.Bijective L := by
    refine ⟨fun x y h => Subtype.ext (eN.injective (congrArg Subtype.val h)), fun y => ?_⟩
    rcases y.property with ⟨z, hz⟩
    refine ⟨⟨f (eM.symm z), ⟨eM.symm z, rfl⟩⟩, Subtype.ext ?_⟩
    show eN (f (eM.symm z)) = (y : N')
    rw [hcomm]
    simpa using hz
  exact (LinearEquiv.ofBijective L hbij).finrank_eq

/-- The images of two morphisms of vector spaces have equal dimension when the morphisms are
intertwined by isomorphisms. -/
private theorem finrank_range_eq_of_iso_comm {k : Type*} [Field k] {A B A' B' : ModuleCat k}
    (f : A ⟶ B) (g : A' ⟶ B') (eA : A ≅ A') (eB : B ≅ B') (hcomm : f ≫ eB.hom = eA.hom ≫ g) :
    Module.finrank k f.hom.range = Module.finrank k g.hom.range :=
  finrank_range_eq_of_linearEquiv f.hom g.hom eA.toLinearEquiv eB.toLinearEquiv fun x => by
    simpa using congrArg (fun q => q.hom x) hcomm

/-- A linear map out of a zero module has zero-dimensional image. -/
private theorem finrank_range_zero_of_isZero_source {k : Type*} [Field k]
    {M N : ModuleCat k} (f : M ⟶ N) (hM : IsZero M) :
    Module.finrank k f.hom.range = 0 := by
  rw [hM.eq_of_src f 0, ModuleCat.hom_zero, LinearMap.range_zero]
  exact finrank_bot k N

/-- A zero module has dimension zero. -/
private theorem finrank_eq_zero_of_isZero {k : Type*} [Field k] {M : ModuleCat k}
    (hM : IsZero M) : Module.finrank k M = 0 := by
  have : Subsingleton M := ModuleCat.isZero_iff_subsingleton.mp hM
  exact Module.finrank_zero_of_subsingleton

/-- **The rank identity for a short complex of finite-dimensional vector spaces.**  The
dimension of the middle term is the dimension of the homology plus the dimensions of the images
of the two maps. -/
private theorem finrank_homology_add_finrank_ranges {k : Type*} [Field k]
    (S : ShortComplex (ModuleCat k)) [S.HasHomology]
    [Module.Finite k S.X₁] [Module.Finite k S.X₂] :
    Module.finrank k S.homology + Module.finrank k S.f.hom.range +
      Module.finrank k S.g.hom.range = Module.finrank k S.X₂ := by
  let L := S.moduleCatToCycles
  have hq : Module.finrank k (LinearMap.ker S.g.hom ⧸ LinearMap.range L) +
      Module.finrank k (LinearMap.range L) = Module.finrank k (LinearMap.ker S.g.hom) :=
    (LinearMap.range L).finrank_quotient_add_finrank
  have hiso : Module.finrank k S.homology =
      Module.finrank k (LinearMap.ker S.g.hom ⧸ LinearMap.range L) :=
    S.moduleCatHomologyIso.toLinearEquiv.finrank_eq
  have hker : L.ker = S.f.hom.ker := by
    ext x
    show (L x = 0) ↔ S.f.hom x = 0
    exact ⟨fun hx => congrArg Subtype.val hx, fun hx => Subtype.ext hx⟩
  have hL := L.finrank_range_add_finrank_ker
  have hf := S.f.hom.finrank_range_add_finrank_ker
  have hg := S.g.hom.finrank_range_add_finrank_ker
  rw [hker] at hL
  omega

/-- The rank identity `dim H^i + dim (im d^{i-1}) + dim (im d^i) = dim C^i` for a cochain complex
of finite-dimensional vector spaces. -/
private theorem finrank_sc_homology_add_finrank_ranges {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{u} k) ℤ) (hfin : ∀ i : ℤ, Module.Finite k (C.X i)) (i : ℤ) :
    Module.finrank k (C.sc i).homology + Module.finrank k (C.sc i).f.hom.range +
      Module.finrank k (C.sc i).g.hom.range = Module.finrank k (C.X i) := by
  let e₁ : (C.sc i).X₁ ≅ C.X (i - 1) := C.XIsoOfEq (by simp [CochainComplex.prev])
  let e₂ : (C.sc i).X₂ ≅ C.X i := C.XIsoOfEq rfl
  have : Module.Finite k (C.sc i).X₁ := LinearEquiv.finiteDimensional e₁.toLinearEquiv.symm
  have : Module.Finite k (C.sc i).X₂ := LinearEquiv.finiteDimensional e₂.toLinearEquiv.symm
  exact finrank_homology_add_finrank_ranges (C.sc i)

/-- The image of `d^{i-1}` has the same dimension whether read as the first map of `C.sc i` or as
the second map of `C.sc (i - 1)`. -/
private theorem finrank_range_sc_f_eq {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{u} k) ℤ) (i : ℤ) :
    Module.finrank k (C.sc i).f.hom.range = Module.finrank k (C.sc (i - 1)).g.hom.range := by
  let e₁ := C.isoSc' (i - 1) i (i + 1) (by simp [CochainComplex.prev])
    (by simp [CochainComplex.next])
  let e₂ := C.isoSc' (i - 2) (i - 1) i (by rw [CochainComplex.prev]; omega)
    (by simp [CochainComplex.next])
  exact (finrank_range_eq_of_iso_comm _ _ (asIso e₁.hom.τ₁) (asIso e₁.hom.τ₂)
    e₁.hom.comm₁₂.symm).trans
    (finrank_range_eq_of_iso_comm _ _ (asIso e₂.hom.τ₂) (asIso e₂.hom.τ₃) e₂.hom.comm₂₃.symm).symm

/-- Shifting the index of a signed sum by one changes its sign. -/
private theorem finsum_negOnePow_mul_sub_one (r : ℤ → ℤ) :
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * r (i - 1) = -∑ᶠ i : ℤ, (i.negOnePow : ℤ) * r i :=
  calc
    ∑ᶠ i : ℤ, (i.negOnePow : ℤ) * r (i - 1) =
        ∑ᶠ i : ℤ, ((i + 1).negOnePow : ℤ) * r (i + 1 - 1) :=
      (finsum_comp_equiv (Equiv.addRight (1 : ℤ))).symm
    _ = -∑ᶠ i : ℤ, (i.negOnePow : ℤ) * r i := by
      rw [← finsum_neg_distrib]
      exact finsum_congr fun i => by simp [Int.negOnePow_succ]

/-- **The Euler characteristic of a bounded complex of finite-dimensional vector spaces is
computed by its cohomology.**  If every term of the cochain complex `C` is finite-dimensional
over `k` and only finitely many terms are nonzero, then
`∑ (-1)^i dim H^i(C) = ∑ (-1)^i dim C^i`. -/
@[ega "0 11.10.2" "special case",
  ega "III 7.9.2" "Case where A is a field",
  ega "III 7.9.6" "special case"]
public theorem homologyEulerChar_eq_eulerChar {k : Type u} [Field k]
    (C : CochainComplex (ModuleCat.{u} k) ℤ)
    (hfin : ∀ i : ℤ, Module.Finite k (C.X i))
    (hsupp : {i : ℤ | ¬ IsZero (C.X i)}.Finite) :
    HomologicalComplex.homologyEulerChar C = HomologicalComplex.eulerChar C := by
  classical
  let cr (i : ℤ) : ℕ := Module.finrank k (C.X i)
  let hr (i : ℤ) : ℕ := Module.finrank k (C.sc i).homology
  let dr (i : ℤ) : ℕ := Module.finrank k ((C.sc i).g.hom.range)
  let dp (i : ℤ) : ℕ := Module.finrank k ((C.sc i).f.hom.range)
  let sg (i : ℤ) : ℤ := (i.negOnePow : ℤ)
  let wc (i : ℤ) : ℤ := sg i * (cr i : ℤ)
  let wh (i : ℤ) : ℤ := sg i * (hr i : ℤ)
  let wd (i : ℤ) : ℤ := sg i * (dr i : ℤ)
  let wdp (i : ℤ) : ℤ := sg i * (dp i : ℤ)
  have hfs {s : Set ℤ} (hs : s.Finite) (r : ℤ → ℕ) (h : ∀ i ∉ s, r i = 0) :
      Function.HasFiniteSupport r :=
    hs.subset (Function.support_subset_iff'.mpr h)
  have hsupp' {i : ℤ} (hi : i ∉ {i : ℤ | ¬ IsZero (C.X i)}) : IsZero (C.X i) := by
    simpa [Set.mem_ofPred_eq, not_not] using hi
  have hsigned {r : ℤ → ℕ} (hrfin : Function.HasFiniteSupport r) :
      Function.HasFiniteSupport (fun i : ℤ => sg i * (r i : ℤ)) := by
    apply hrfin.subset
    rw [Function.support_subset_iff']
    intro i hi
    simp [Function.notMem_support.mp hi]
  have hwh : Function.HasFiniteSupport wh := hsigned <| hfs hsupp hr fun i hi =>
    finrank_eq_zero_of_isZero (ShortComplex.isZero_homology_of_isZero_X₂ (C.sc i)
      ((hsupp' hi).of_iso (C.XIsoOfEq rfl)))
  have hwd : Function.HasFiniteSupport wd := hsigned <| hfs hsupp dr fun i hi =>
    finrank_range_zero_of_isZero_source (C.sc i).g ((hsupp' hi).of_iso (C.XIsoOfEq rfl))
  have hsuppPrev : {i : ℤ | ¬ IsZero (C.X (i - 1))}.Finite :=
    (hsupp.image (· + 1)).subset fun i hi => ⟨i - 1, hi, Int.sub_add_cancel i 1⟩
  have hwdp : Function.HasFiniteSupport wdp := hsigned <|
    hfs hsuppPrev dp fun i hi => finrank_range_zero_of_isZero_source (C.sc i).f
        ((hsupp' (i := i - 1) hi).of_iso (C.XIsoOfEq (by simp [CochainComplex.prev])))
  have hsignedpoint (i : ℤ) : wh i + wdp i + wd i = wc i := by
    have hz : (hr i : ℤ) + dp i + dr i = cr i := by
      exact_mod_cast finrank_sc_homology_add_finrank_ranges C hfin i
    simp only [wh, wdp, wd, wc, ← hz, mul_add]
  have hsum : (∑ᶠ i : ℤ, wh i) + (∑ᶠ i : ℤ, wdp i) + (∑ᶠ i : ℤ, wd i) = ∑ᶠ i : ℤ, wc i := by
    rw [← finsum_add_distrib hwh hwdp,
      ← finsum_add_distrib ((hwh.union hwdp).subset (Function.support_add _ _)) hwd]
    exact finsum_congr hsignedpoint
  have hshift : (∑ᶠ i : ℤ, wdp i) = -(∑ᶠ i : ℤ, wd i) :=
    (finsum_congr fun i => by simp [wdp, dp, dr, sg, finrank_range_sc_f_eq C i]).trans
      (finsum_negOnePow_mul_sub_one fun i => (dr i : ℤ))
  rw [hshift] at hsum
  have hEuler : (∑ᶠ i : ℤ, wh i) = ∑ᶠ i : ℤ, wc i := by omega
  have hhom (i : ℤ) :
      Module.finrank k (C.homology i) = Module.finrank k (C.sc i).homology := rfl
  simpa [HomologicalComplex.homologyEulerChar, HomologicalComplex.eulerChar,
    GradedObject.eulerChar, ComplexShape.χ, ComplexShape.eulerCharSignsUpInt,
    hhom, wh, wc, sg, hr, cr] using hEuler

end StacksDraft.Perfect

end
