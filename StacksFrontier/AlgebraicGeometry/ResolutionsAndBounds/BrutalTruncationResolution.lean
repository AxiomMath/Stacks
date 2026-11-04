module

public import StacksFrontier.AlgebraicGeometry.ResolutionsAndBounds.DiagonalBoxGenerator

/-!
# The brutal truncation of an acyclic resolution

Let `C` be an acyclic `ℕ`-indexed chain complex of modules on a scheme, with coherent terms, and
let `0 < N`. The complex `C_{N + 1} → ⋯ → C_2 → C_1`, placed in degrees `[-N, 0]`, has `C_0` as
its zeroth cohomology, no cohomology strictly between `-N` and `0`, and coherent cohomology in
every degree. This is the homological algebra the proof of [Stacks, Tag 0FZ5] uses to cut the
resolution of [Stacks, Tag 0FZ2] down to a bounded complex.

## Main definitions

* `ComplexShape.finDown N`: the chain-complex shape on `Fin (N + 1)`, with differentials
  `i + 1 ⟶ i`.
* `HomologicalComplex.brutalTruncationSucc C N`: the complex `C_{N + 1} → ⋯ → C_1` in degrees
  `[-N, 0]`, the term `C_{j + 1}` sitting in degree `-j`.

## Main results

* `AlgebraicGeometry.brutalTruncationOfAcyclicResolution`: the proposition
  `AlgebraicGeometry.BrutalTruncationOfAcyclicResolution`, proved.

## Implementation notes

The truncation is built in two steps along embeddings of complex shapes: the restriction of `C`
along `j ↦ j + 1` from `ComplexShape.finDown N` to `ComplexShape.down ℕ`, then the extension
along `j ↦ -j` from `ComplexShape.finDown N` to `ComplexShape.up ℤ`. The interior homology is
then read off `HomologicalComplex.extendHomologyIso` and `HomologicalComplex.restriction.sc'Iso`,
the zeroth from the cokernel presentation `C_2 → C_1 → C_0 → 0` that acyclicity provides.

The Noetherian hypothesis of the proposition is not used: coherent modules on any scheme are
closed under kernels and cokernels ([Stacks, Tag 01BY]).

## References

* [Stacks Project, Tag 0FZ5](https://stacks.math.columbia.edu/tag/0FZ5)
* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

/-- The chain-complex shape on `Fin (N + 1)`: there is a differential `i ⟶ j` exactly when
`i = j + 1`. -/
def ComplexShape.finDown (N : ℕ) : ComplexShape (Fin (N + 1)) where
  Rel i j := (j : ℕ) + 1 = i
  next_eq h h' := Fin.ext (by omega)
  prev_eq h h' := Fin.ext (by omega)

namespace ComplexShape.finDown

variable (N : ℕ)

/-- The embedding `j ↦ j + 1` of `ComplexShape.finDown N` into `ComplexShape.down ℕ`. -/
def embeddingSucc : (ComplexShape.finDown N).Embedding (ComplexShape.down ℕ) :=
  Embedding.mk' _ _ (fun i => (i : ℕ) + 1) (fun i j h => Fin.ext (by simpa using h))
    (fun i j => by simp [ComplexShape.finDown])

/-- The embedding `j ↦ -j` of `ComplexShape.finDown N` into `ComplexShape.up ℤ`. -/
def embeddingNeg : (ComplexShape.finDown N).Embedding (ComplexShape.up ℤ) :=
  Embedding.mk' _ _ (fun i => -((i : ℕ) : ℤ)) (fun i j h => Fin.ext (by simpa using h))
    (fun i j => by simp only [ComplexShape.finDown, ComplexShape.up_Rel]; omega)

/-- The embedding `ComplexShape.finDown.embeddingSucc N` sends `i` to `i + 1`. -/
@[simp]
lemma embeddingSucc_f (i : Fin (N + 1)) : (embeddingSucc N).f i = (i : ℕ) + 1 := rfl

/-- The embedding `ComplexShape.finDown.embeddingNeg N` sends `i` to `-i`. -/
@[simp]
lemma embeddingNeg_f (i : Fin (N + 1)) : (embeddingNeg N).f i = -((i : ℕ) : ℤ) := rfl

/-- The embedding `ComplexShape.finDown.embeddingSucc N` reflects the relation of
`ComplexShape.down ℕ`. -/
instance : (embeddingSucc N).IsRelIff where
  rel' i j h := by
    change (j : ℕ) + 1 = i
    change (j : ℕ) + 1 + 1 = (i : ℕ) + 1 at h
    omega

/-- The embedding `ComplexShape.finDown.embeddingNeg N` reflects the relation of
`ComplexShape.up ℤ`. -/
instance : (embeddingNeg N).IsRelIff where
  rel' i j h := by
    change (j : ℕ) + 1 = i
    change -((i : ℕ) : ℤ) + 1 = -((j : ℕ) : ℤ) at h
    omega

end ComplexShape.finDown

namespace HomologicalComplex

variable {V : Type*} [Category* V] [HasZeroMorphisms V] [HasZeroObject V]

/-- **The brutal truncation `C_{N + 1} → ⋯ → C_1` of a chain complex**, as a cochain complex
with `C_{j + 1}` in degree `-j` for `j ≤ N` and zero elsewhere. -/
def brutalTruncationSucc (C : ChainComplex V ℕ) (N : ℕ) : CochainComplex V ℤ :=
  (C.restriction (ComplexShape.finDown.embeddingSucc N)).extend
    (ComplexShape.finDown.embeddingNeg N)

end HomologicalComplex

namespace AlgebraicGeometry

universe u

attribute [local instance] HasDerivedCategory.standard

open HomologicalComplex ComplexShape.finDown

/-- **The homology of a short complex of coherent modules is coherent**, coherent modules being
closed under kernels and cokernels ([Stacks, Tag 01BY]). -/
theorem isCoherent_homology_of_isCoherent {W : Scheme.{u}} (S : ShortComplex W.Modules)
    (h₁ : S.X₁.IsCoherent) (h₂ : S.X₂.IsCoherent) (h₃ : S.X₃.IsCoherent) :
    S.homology.IsCoherent := by
  have := CoherentAbelian.coherentModules_isClosedUnderKernels (R := W.ringCatSheaf)
  have := CoherentAbelian.coherentModules_isClosedUnderCokernels (R := W.ringCatSheaf)
  have hc : S.cycles.IsCoherent :=
    isCoherent_of_moduleIso (S.cyclesIsKernel.conePointUniqueUpToIso (limit.isLimit _)).symm
      (ObjectProperty.prop_kernel (P := fun M : SheafOfModules W.ringCatSheaf => M.IsCoherent)
        S.g h₂ h₃)
  exact isCoherent_of_moduleIso
    ((cokernelIsCokernel _).coconePointUniqueUpToIso S.homologyIsCokernel)
    (ObjectProperty.prop_cokernel (P := fun M : SheafOfModules W.ringCatSheaf => M.IsCoherent)
      S.toCycles h₁ hc)

/-- **[Stacks, Tag 0FZ5], the brutal truncation step:**
`AlgebraicGeometry.BrutalTruncationOfAcyclicResolution` holds. The complex
`C_{N + 1} → ⋯ → C_1` in degrees `[-N, 0]` has zeroth cohomology `C_0`, no cohomology strictly
between `-N` and `0`, and coherent cohomology throughout. -/
theorem brutalTruncationOfAcyclicResolution : BrutalTruncationOfAcyclicResolution.{u} := by
  intro W _ C hac hcoh N hN
  set L := C.brutalTruncationSucc N
  set D := C.restriction (embeddingSucc N)
  -- The terms.
  have hXzero : ∀ i : ℤ, (∀ j : Fin (N + 1), -((j : ℕ) : ℤ) ≠ i) → IsZero (L.X i) :=
    fun i hi => D.isZero_extend_X (embeddingNeg N) i hi
  have hXiso : ∀ j : Fin (N + 1), L.X (-((j : ℕ) : ℤ)) ≅ C.X ((j : ℕ) + 1) := fun j =>
    D.extendXIso (embeddingNeg N) (i := j) rfl ≪≫ C.restrictionXIso (embeddingSucc N) rfl
  have hLge : L.IsStrictlyGE (-(N : ℤ)) := by
    rw [CochainComplex.isStrictlyGE_iff]
    intro i hi
    exact hXzero i fun j hj => by have := j.isLt; omega
  have hLle : L.IsStrictlyLE 0 := by
    rw [CochainComplex.isStrictlyLE_iff]
    intro i hi
    exact hXzero i fun j hj => by omega
  have hXcoh : ∀ i : ℤ, (L.X i).IsCoherent := by
    intro i
    by_cases h : ∃ j : Fin (N + 1), -((j : ℕ) : ℤ) = i
    · obtain ⟨j, rfl⟩ := h
      exact isCoherent_of_moduleIso (hXiso j).symm (hcoh _)
    · have := CoherentAbelian.coherentModules_containsZero (R := W.ringCatSheaf)
      exact isCoherent_of_moduleIso (hXzero i fun j hj => h ⟨j, hj⟩).isoZero.symm
        (ObjectProperty.prop_zero (fun M : SheafOfModules W.ringCatSheaf => M.IsCoherent))
  have hH : ∀ i : ℤ, (DerivedCategory.homologyFunctor W.Modules i).obj (DerivedCategory.Q.obj L)
      ≅ L.homology i := fun i => (DerivedCategory.homologyFunctorFactors W.Modules i).app L
  refine ⟨L, hLge, hLle, fun j hj => ⟨hXiso ⟨j, by omega⟩⟩, ⟨?_⟩, ?_, ?_⟩
  · -- The zeroth cohomology is `C_0`.
    let i1 : Fin (N + 1) := ⟨1, by omega⟩
    have hprev : (ComplexShape.finDown N).prev 0 = i1 :=
      (ComplexShape.finDown N).prev_eq' (by simp [ComplexShape.finDown, i1])
    have hnext : (ComplexShape.finDown N).next 0 = 0 :=
      (ComplexShape.finDown N).next_eq_self' 0 (fun k hk => by
        simp [ComplexShape.finDown] at hk)
    have hS1 : (C.sc' 2 1 0).Exact :=
      (C.exactAt_iff' 2 1 0 (by simp) (by simp)).1 (hac 1)
    have : Epi (C.sc' 2 1 0).g :=
      ((C.exactAt_iff' 1 0 0 (by simp) (by simp)).1 (hac 0)).epi_f (C.shape 0 0 (by simp))
    have hg : (D.sc' i1 0 0).g = 0 := D.shape 0 0 (by simp [ComplexShape.finDown])
    let hd := ShortComplex.LeftHomologyData.ofIsColimitCokernelCofork (D.sc' i1 0 0) hg
      (CokernelCofork.ofπ (Z := C.X 0) (C.d 1 0) (C.d_comp_d 2 1 0)) hS1.gIsCokernel
    exact hH 0 ≪≫ D.extendHomologyIso (embeddingNeg N) (j := 0) (by simp) ≪≫
      D.homologyIsoSc' i1 0 0 hprev hnext ≪≫ hd.homologyIso
  · -- The gap.
    intro i hi1 hi2
    obtain ⟨j, rfl⟩ : ∃ j : ℕ, i = -(j : ℤ) := ⟨(-i).toNat, by omega⟩
    have hj1 : 0 < j := by omega
    have hjN : j < N := by omega
    let jj : Fin (N + 1) := ⟨j, by omega⟩
    let jp : Fin (N + 1) := ⟨j + 1, by omega⟩
    let jm : Fin (N + 1) := ⟨j - 1, by omega⟩
    have hprev : (ComplexShape.finDown N).prev jj = jp :=
      (ComplexShape.finDown N).prev_eq' (by simp [ComplexShape.finDown, jj, jp])
    have hnext : (ComplexShape.finDown N).next jj = jm :=
      (ComplexShape.finDown N).next_eq' (by simp [ComplexShape.finDown, jj, jm]; omega)
    have hCj : (C.sc' (j + 2) (j + 1) j).Exact :=
      (C.exactAt_iff' (j + 2) (j + 1) j (by simp) (by simp)).1 (hac (j + 1))
    have hDj : D.ExactAt jj := by
      rw [D.exactAt_iff' jp jj jm hprev hnext]
      exact (ShortComplex.exact_iff_of_iso (restriction.sc'Iso C (embeddingSucc N) jp jj jm
        (i' := j + 2) (j' := j + 1) (k' := j) (by simp [jp])
        (by simp [jj]) (by simp [jm]; omega)
        (by simp) (by simp))).2 hCj
    have hLj : L.ExactAt (-(j : ℤ)) :=
      (D.extend_exactAt_iff (embeddingNeg N) (j := jj) (by simp [jj])).2 hDj
    exact (L.exactAt_iff_isZero_homology _).1 hLj |>.of_iso (hH _)
  · -- Coherence of the cohomology.
    intro i
    exact isCoherent_of_moduleIso (hH i).symm
      (isCoherent_homology_of_isCoherent (L.sc i) (hXcoh _) (hXcoh _) (hXcoh _))

end AlgebraicGeometry
