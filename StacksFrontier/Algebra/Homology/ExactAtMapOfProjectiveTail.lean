module

public import Mathlib.Algebra.Homology.Additive
public import Mathlib.Algebra.Homology.ShortComplex.ShortExact
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Preadditive.Projective.Basic

/-!
# Right exact functors preserve exactness along a projective tail

Let `K` be a cochain complex in an abelian category which vanishes in high degrees, is exact in
every degree `≥ n` and has projective terms in every degree `> n`. Then every additive functor
which preserves epimorphisms carries `K` to a complex which is still exact in every degree `≥ n`.

## Main results

* `CochainComplex.projective_kernel_d_of_projective_tail`: the cycles are projective above `n`.
* `CochainComplex.exactAt_mapHomologicalComplex_of_projective_tail`: the statement above.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

variable {C D : Type*} [Category* C] [Abelian C] [Category* D] [Abelian D]

section

variable (K : CochainComplex C ℤ)

/-- The short complex `Z^j → K^j → Z^{j+1}` of the cycles of `K`, where `Z^j` is the kernel of the
differential leaving degree `j`. -/
noncomputable def cyclesShortComplex (j : ℤ) : ShortComplex C :=
  ShortComplex.mk (kernel.ι (K.d j (j + 1)))
    (kernel.lift (K.d (j + 1) (j + 1 + 1)) (K.d j (j + 1)) (K.d_comp_d _ _ _)) (by
      rw [← cancel_mono (kernel.ι (K.d (j + 1) (j + 1 + 1))), Category.assoc, kernel.lift_ι,
        kernel.condition, zero_comp])

/-- If `K` is exact in degree `j`, then the morphism `K^i → Z^j` induced by the differential is an
epimorphism. -/
private lemma epi_kernel_lift_of_exactAt_aux (i j k : ℤ) (hi : (ComplexShape.up ℤ).prev j = i)
    (hk : (ComplexShape.up ℤ).next j = k) (h : K.ExactAt j) :
    Epi (kernel.lift (K.d j k) (K.d i j) (K.d_comp_d _ _ _)) :=
  ((HomologicalComplex.exactAt_iff' K i j k hi hk).1 h).epi_kernelLift

/-- If `K` is exact in degree `j + 1`, then the morphism `K^j → Z^{j+1}` induced by the
differential is an epimorphism. -/
lemma epi_kernel_lift_of_exactAt (j : ℤ) (h : K.ExactAt (j + 1)) :
    Epi (kernel.lift (K.d (j + 1) (j + 1 + 1)) (K.d j (j + 1)) (K.d_comp_d _ _ _)) :=
  epi_kernel_lift_of_exactAt_aux K j (j + 1) (j + 1 + 1) (by simp) (by simp) h

/-- The short complex `Z^j → K^j → K^{j+1}`, where `Z^j` is the kernel of the differential. -/
private noncomputable def kernelShortComplex (j : ℤ) : ShortComplex C :=
  ShortComplex.mk (kernel.ι (K.d j (j + 1))) (K.d j (j + 1)) (kernel.condition _)

/-- The comparison of `Z^j → K^j → Z^{j+1}` with `Z^j → K^j → K^{j+1}`. -/
private noncomputable def cyclesToKernelShortComplex (j : ℤ) :
    K.cyclesShortComplex j ⟶ K.kernelShortComplex j :=
  { τ₁ := 𝟙 _
    τ₂ := 𝟙 _
    τ₃ := kernel.ι (K.d (j + 1) (j + 1 + 1))
    comm₁₂ := by simp [cyclesShortComplex, kernelShortComplex]
    comm₂₃ := by simp [cyclesShortComplex, kernelShortComplex] }

/-- If `K` is exact in degree `j + 1`, then `0 → Z^j → K^j → Z^{j+1} → 0` is short exact. -/
lemma cyclesShortComplex_shortExact (j : ℤ) (h : K.ExactAt (j + 1)) :
    (K.cyclesShortComplex j).ShortExact := by
  refine ShortComplex.ShortExact.mk' ?_
    (inferInstance : Mono (kernel.ι (K.d j (j + 1)))) (K.epi_kernel_lift_of_exactAt j h)
  have hS' : (K.kernelShortComplex j).Exact :=
    ShortComplex.exact_of_f_is_kernel _ (kernelIsKernel _)
  have : Epi (K.cyclesToKernelShortComplex j).τ₁ := (inferInstance : Epi (𝟙 _))
  have : IsIso (K.cyclesToKernelShortComplex j).τ₂ := (inferInstance : IsIso (𝟙 _))
  have : Mono (K.cyclesToKernelShortComplex j).τ₃ :=
    (inferInstance : Mono (kernel.ι (K.d (j + 1) (j + 1 + 1))))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono (K.cyclesToKernelShortComplex j)).2 hS'

variable {K}

/-- **The cycles are projective above `n`.** If `K` vanishes above `m`, is exact in every degree
`≥ n` and has projective terms in every degree `> n`, then the kernel of every differential
leaving a degree `> n` is projective. -/
theorem projective_kernel_d_of_projective_tail (n m : ℤ) (hK : ∀ i, m < i → IsZero (K.X i))
    (hex : ∀ i, n ≤ i → K.ExactAt i) (hproj : ∀ i, n < i → Projective (K.X i)) (j : ℤ)
    (hj : n < j) : Projective (kernel (K.d j (j + 1))) := by
  suffices H : ∀ k : ℕ, ∀ j : ℤ, n < j → m < j + k → Projective (kernel (K.d j (j + 1))) by
    exact H (m - j + 1).toNat j hj (by omega)
  intro k
  induction k with
  | zero =>
    intro j _ hjm
    exact (IsZero.of_mono (kernel.ι (K.d j (j + 1))) (hK j (by simpa using hjm))).projective
  | succ k ih =>
    intro j hj hjm
    have : Projective (K.cyclesShortComplex j).X₃ :=
      ih (j + 1) (by omega) (by push_cast at hjm ⊢; omega)
    have := hproj j hj
    let s := (K.cyclesShortComplex_shortExact j (hex (j + 1) (by omega))).splittingOfProjective
    exact Retract.projective (X := kernel (K.d j (j + 1))) (Y := K.X j)
      ⟨(K.cyclesShortComplex j).f, s.r, s.f_r⟩

end

/-- **Right exact functors preserve exactness along a projective tail.** Let `K` be a cochain
complex which vanishes above `m`, is exact in every degree `≥ n` and has projective terms in every
degree `> n`. Then for every additive functor `F` preserving epimorphisms, `F(K)` is exact in
every degree `≥ n`. -/
theorem exactAt_mapHomologicalComplex_of_projective_tail (F : C ⥤ D) [F.Additive]
    [F.PreservesEpimorphisms] {K : CochainComplex C ℤ} (n m : ℤ)
    (hK : ∀ i, m < i → IsZero (K.X i)) (hex : ∀ i, n ≤ i → K.ExactAt i)
    (hproj : ∀ i, n < i → Projective (K.X i)) (j : ℤ) (hj : n ≤ j) :
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj K).ExactAt j := by
  rw [HomologicalComplex.exactAt_iff' _ (j - 1) j (j + 1) (by simp) (by simp)]
  have : Projective (K.cyclesShortComplex j).X₃ :=
    projective_kernel_d_of_projective_tail n m hK hex hproj (j + 1) (by omega)
  let sj := (K.cyclesShortComplex_shortExact j (hex (j + 1) (by omega))).splittingOfProjective
  have : Projective (K.cyclesShortComplex (j + 1)).X₃ :=
    projective_kernel_d_of_projective_tail n m hK hex hproj (j + 1 + 1) (by omega)
  have : IsSplitMono (kernel.ι (K.d (j + 1) (j + 1 + 1))) :=
    let s := (K.cyclesShortComplex_shortExact (j + 1)
      (hex (j + 1 + 1) (by omega))).splittingOfProjective
    IsSplitMono.mk' ⟨s.r, s.f_r⟩
  have hepi := epi_kernel_lift_of_exactAt_aux K (j - 1) j (j + 1) (by simp) (by simp) (hex j hj)
  change ((K.sc' (j - 1) j (j + 1)).map F).Exact
  let φ : (K.sc' (j - 1) j (j + 1)).map F ⟶ (K.kernelShortComplex j).map F :=
    { τ₁ := F.map (kernel.lift (K.d j (j + 1)) (K.d (j - 1) j) (K.d_comp_d _ _ _))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := (F.map_comp _ _).symm.trans
        ((congrArg F.map (kernel.lift_ι (K.d j (j + 1)) (K.d (j - 1) j) (K.d_comp_d _ _ _))).trans
          (Category.comp_id _).symm)
      comm₂₃ := (Category.id_comp _).trans (Category.comp_id _).symm }
  have : Epi φ.τ₁ := (inferInstance : Epi (F.map (kernel.lift (K.d j (j + 1)) (K.d (j - 1) j)
    (K.d_comp_d _ _ _))))
  have : IsIso φ.τ₂ := (inferInstance : IsIso (𝟙 _))
  have : Mono φ.τ₃ := (inferInstance : Mono (𝟙 _))
  rw [ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ]
  have : Epi (F.mapShortComplex.map (K.cyclesToKernelShortComplex j)).τ₁ :=
    (inferInstance : Epi (F.map (𝟙 _)))
  have : IsIso (F.mapShortComplex.map (K.cyclesToKernelShortComplex j)).τ₂ :=
    (inferInstance : IsIso (F.map (𝟙 _)))
  have : Mono (F.mapShortComplex.map (K.cyclesToKernelShortComplex j)).τ₃ :=
    (inferInstance : Mono (F.map (kernel.ι (K.d (j + 1) (j + 1 + 1)))))
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono
    (F.mapShortComplex.map (K.cyclesToKernelShortComplex j))).1 (sj.map F).exact

end CochainComplex
