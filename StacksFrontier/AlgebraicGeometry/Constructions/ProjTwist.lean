module

public import StacksFrontier.AlgebraicGeometry.Constructions.ProjStructureSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorSheafificationComparison
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Twists on the homogeneous spectrum

For a nonnegatively graded ring `A`, the `n`-th twist `𝒪_{Proj A}(n)` of the structure sheaf is
the sheaf associated to the graded module `A(n)`, the regular module `A` with its grading shifted
by `n`: the degree `i` piece of `A(n)` is `A_{i + n}`. The `n`-th twist of an arbitrary
`𝒪_{Proj A}`-module `ℱ` is `ℱ ⊗ 𝒪_{Proj A}(n)`.

Shifting an `ℕ`-grading by an integer leaves the nonnegative range, so the construction first
extends the grading to all of `ℤ` by zero and then shifts; the result is again a decomposition of
`A`, and the graded-multiplication compatibility that makes `A(n)` a graded module over `A`
survives the shift.

## Main definitions

* `AlgebraicGeometry.ProjectiveSpectrum.Proj.integerGrading`: an `ℕ`-grading extended to `ℤ`
  by zero.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistGrading`: the grading of `A(n)`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistingSheaf`: `𝒪_{Proj A}(n)`.
* `AlgebraicGeometry.ProjectiveSpectrum.Proj.twistSheafOfModules`: `ℱ(n)`.

## Implementation notes

The grading may have any `SetLike`/`AddSubgroupClass` representation. Its pieces are regarded as
`ℤ`-submodules of the underlying additive group, extended by zero to negative degrees, and then
shifted. The underlying module of every graded twist is the regular module `A`, so only the
grading changes from one twist to the next.

The structure-sheaf twist is an abbreviation for the associated-module sheaf of that grading, so
its section and standard-open module instances are inherited rather than restated. The tensor
product is the sheafification of the sectionwise tensor product,
`Stacks.SheafOfModules.Tensor.sheafTensor`.

## References

* [Stacks Project, Tag 01MN](https://stacks.math.columbia.edu/tag/01MN)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProjectiveSpectrum.Proj

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u w

variable {S : Type u} [CommRing S]

variable {σ : Type w} [SetLike σ S] [AddSubgroupClass σ S]

/-- The homogeneous component of an arbitrary additive-subgroup grading, regarded as a
`ℤ`-submodule of the underlying additive group. -/
public def homogeneousSubmodule (𝒜 : ℕ → σ) (i : ℕ) : Submodule ℤ S where
  carrier := 𝒜 i
  zero_mem' := zero_mem (𝒜 i)
  add_mem' := fun ha hb => add_mem ha hb
  smul_mem' := fun n _ ha => zsmul_mem ha n

/-- An element lies in `homogeneousSubmodule 𝒜 i` exactly when it lies in `𝒜 i`. -/
@[simp] public theorem mem_homogeneousSubmodule (𝒜 : ℕ → σ) (i : ℕ) (x : S) :
    x ∈ homogeneousSubmodule (S := S) 𝒜 i ↔ x ∈ 𝒜 i := Iff.rfl

/-- A nonnegative grading, extended by zero to all integer degrees. -/
public def integerGrading (𝒜 : ℕ → σ) (i : ℤ) : Submodule ℤ S :=
  if 0 ≤ i then homogeneousSubmodule (S := S) 𝒜 i.toNat else ⊥

/-- In a nonnegative degree `i`, the extended grading is the degree `i` component of `𝒜`. -/
@[simp] public theorem integerGrading_natCast (𝒜 : ℕ → σ) (i : ℕ) :
    integerGrading (S := S) 𝒜 i = homogeneousSubmodule (S := S) 𝒜 i := by
  simp [integerGrading]

/-- In a negative degree, the extended grading is zero. -/
@[simp] public theorem integerGrading_neg (𝒜 : ℕ → σ) (i : ℤ) (hi : i < 0) :
    integerGrading (S := S) 𝒜 i = ⊥ := by
  simp [integerGrading, not_le.mpr hi]

/-- The degree `i` part of the regular graded module shifted by `n` is `S_{i+n}`. -/
@[sga "6 VI 1.2" "special case"]
public abbrev twistGrading (𝒜 : ℕ → σ) (n : ℤ) :
    ℤ → Submodule ℤ S := fun i => integerGrading (S := S) 𝒜 (i + n)

/-- The degree `i` part of the twist by `n` is the degree `i + n` part of the extended grading. -/
@[simp] public theorem twistGrading_apply (𝒜 : ℕ → σ) (n i : ℤ) :
    twistGrading (S := S) 𝒜 n i = integerGrading (S := S) 𝒜 (i + n) := rfl

/-- The twist by `0` is the grading extended by zero, unshifted. -/
@[simp] public theorem twistGrading_zero (𝒜 : ℕ → σ) :
    twistGrading (S := S) 𝒜 0 = integerGrading (S := S) 𝒜 := by
  funext i
  simp

/-- The degree `i - n` part of the twist by `n` is the degree `i` component of `𝒜`. -/
@[simp] public theorem twistGrading_natCast (𝒜 : ℕ → σ) (n : ℤ) (i : ℕ) :
    twistGrading (S := S) 𝒜 n ((i : ℤ) - n) = homogeneousSubmodule (S := S) 𝒜 i := by
  simp

/-- Extending a grading to `ℤ` by zero again decomposes the ring. -/
public noncomputable instance integerGradingDecomposition
    (𝒜 : ℕ → σ) [GradedRing 𝒜] :
    DirectSum.Decomposition (integerGrading (S := S) 𝒜) := by
  let 𝒜' : ℤ → Submodule ℤ S := integerGrading (S := S) 𝒜
  have hnat (n : ℕ) : 𝒜' n = homogeneousSubmodule (S := S) 𝒜 n := by
    simp [𝒜']
  have hbase : DirectSum.IsInternal (homogeneousSubmodule (S := S) 𝒜) := by
    change DirectSum.IsInternal 𝒜
    exact DirectSum.Decomposition.isInternal 𝒜
  have hi' : iSupIndep 𝒜' := by
    intro d
    by_cases hd : 0 ≤ d
    · rw [show 𝒜' d = homogeneousSubmodule (S := S) 𝒜 d.toNat by
        simp [𝒜', integerGrading, hd]]
      apply (hbase.submodule_iSupIndep d.toNat).mono_right
      refine iSup₂_le fun e he ↦ ?_
      by_cases he' : 0 ≤ e
      · rw [show 𝒜' e = homogeneousSubmodule (S := S) 𝒜 e.toNat by
          simp [𝒜', integerGrading, he']]
        exact le_iSup_of_le e.toNat (le_iSup_of_le (by omega : e.toNat ≠ d.toNat) le_rfl)
      · simp [𝒜', integerGrading, he']
    · simp [𝒜', integerGrading, hd]
  have hs' : iSup 𝒜' = ⊤ := top_unique <| hbase.submodule_iSup_eq_top.ge.trans <|
    iSup_le fun n ↦ (hnat n).ge.trans (le_iSup 𝒜' (n : ℤ))
  exact (DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi' hs').chooseDecomposition

/-- Shifting a `ℤ`-grading by an integer again decomposes the ring. -/
public noncomputable instance twistGradingDecomposition
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (n : ℤ) :
    DirectSum.Decomposition (twistGrading (S := S) 𝒜 n) := by
  let e : ℤ ≃ ℤ := Equiv.addRight n
  have h : DirectSum.IsInternal ((integerGrading (S := S) 𝒜) ∘ e) := by
    have h0 := DirectSum.Decomposition.isInternal (integerGrading (S := S) 𝒜)
    rw [DirectSum.isInternal_submodule_iff_iSupIndep_and_iSup_eq_top] at h0 ⊢
    obtain ⟨hind, hsup⟩ := h0
    refine ⟨hind.comp e.injective, ?_⟩
    rw [← hsup]
    exact e.iSup_comp (g := integerGrading (S := S) 𝒜)
  exact (show DirectSum.IsInternal
    (fun i => integerGrading (S := S) 𝒜 (i + n)) from h).chooseDecomposition

/-- The action of `ℕ` on `ℤ` by addition of the cast. -/
local instance : VAdd ℕ ℤ where
  vadd i j := (i : ℤ) + j

/-- Multiplication by a homogeneous element of degree `i` carries the degree `j` part of `S(n)`
into its degree `i + j` part, so `S(n)` is a graded module over `S`. -/
public instance twistGradingGradedSMul
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (n : ℤ) :
    SetLike.GradedSMul 𝒜 (twistGrading (S := S) 𝒜 n) := by
  refine ⟨?_⟩
  intro i j a b ha hb
  change a * b ∈ integerGrading (S := S) 𝒜 ((i : ℤ) + j + n)
  by_cases hj : 0 ≤ j + n
  · have hb' : b ∈ 𝒜 (j + n).toNat := by simpa [twistGrading, integerGrading, hj] using hb
    have ht : 0 ≤ (i : ℤ) + j + n := by omega
    have heq : ((i : ℤ) + j + n).toNat = i + (j + n).toNat := by omega
    simpa [integerGrading, ht, heq, homogeneousSubmodule] using
      (SetLike.mul_mem_graded ha hb')
  · obtain rfl : b = 0 := by simpa [twistGrading, integerGrading, hj] using hb
    simp [integerGrading]

/-- The `n`-th twist of the structure sheaf on `Proj(S)`. -/
@[stacks 01MN "part (1), twist of the structure sheaf"]
public noncomputable abbrev twistingSheaf
    (𝒜 : ℕ → σ) [GradedRing 𝒜] (n : ℤ) :
    SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒜)) :=
  associatedModuleSheaf 𝒜 (twistGrading (S := S) 𝒜 n)

/-- Tensoring an `𝒪_Proj(S)`-module with the `n`-th twisting sheaf. -/
@[stacks 01MN "part (2), twist of a module sheaf"]
public noncomputable def twistSheafOfModules
    (𝒜 : ℕ → σ) [GradedRing 𝒜]
    (F : SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒜))) (n : ℤ) :
    SheafOfModules.{u}
      ((sheafCompose (Opens.grothendieckTopology (ProjectiveSpectrum.top 𝒜))
        (forget₂ CommRingCat.{u} RingCat.{u})).obj
        (ProjectiveSpectrum.Proj.structureSheaf 𝒜)) :=
  ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
    (ProjectiveSpectrum.Proj.structureSheaf 𝒜)).obj F).obj (twistingSheaf 𝒜 n)

end AlgebraicGeometry.ProjectiveSpectrum.Proj
