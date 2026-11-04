module

public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimitHomologySequence
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact

/-!
# The Milnor short exact sequence at a given derived-limit triangle

Let `A` be an abelian category with exact countable products and let `(Kₙ)` be an inverse system
in `D(A)` indexed by `ℕ`. A derived limit of the system is an object `K` fitting in a
distinguished triangle `K ⟶ ∏ Kₙ ⟶ ∏ Kₙ ⟶ K⟦1⟧` whose middle map is the difference map; taking
degree-`r` cohomology of that triangle yields the Milnor short exact sequence

`0 ⟶ R¹lim Hʳ⁻¹(Kₙ) ⟶ Hʳ(K) ⟶ lim Hʳ(Kₙ) ⟶ 0`,

with `R¹lim` presented as the cokernel of the difference map on the product.

`DerivedCategory.isDerivedLimit_homology_shortExact` (Tag 07KY) already states this, but it
takes the derived limit as a *property* and so re-quantifies the structural map `K ⟶ ∏ Kₙ`
existentially. A consumer that has obtained a particular structural map — for instance as the
image of one under a right derived functor, which is what Tag 08U1 produces — cannot then
identify it with the one 07KY returns, and the projection onto `lim Hʳ(Kₙ)` is characterized
only in terms of that map. This file states the same conclusion with the triangle, and hence the
structural map, supplied by the caller.

## Main results

* `DerivedCategory.exists_milnor_shortExact_of_distTriang`: the Milnor short exact sequence of a
  given derived-limit triangle, with its projection characterized by the supplied structural
  map.

## Implementation notes

The statement and proof are those of Tag 07KY with `a`, `b` and the distinguished-triangle
hypothesis moved from the conclusion into the parameters; 07KY is the existential form of this
lemma.

`R¹lim` is the cokernel of the difference map rather than a chosen right-derived-limit functor,
which is what keeps the inclusion characterizable by the connecting morphism without an
arbitrary identification. The limit `lim Hʳ(Kₙ)` is related to the kernel of the difference map
through `inverseSystemLimitKernelForkIsLimit`, so the projection is stated against the limit
itself and characterized by its composites with all limit projections.

## References

* [Stacks Project, Tag 07KY](https://stacks.math.columbia.edu/tag/07KY)
* [Stacks Project, Tag 07KZ](https://stacks.math.columbia.edu/tag/07KZ)
-/

@[expose] public noncomputable section

universe w v u

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

namespace DerivedCategory

variable {A : Type u} [Category.{v} A] [Abelian A]
  [HasProductsOfShape ℕ A] [HasExactLimitsOfShape (Discrete ℕ) A]
  [HasLimitsOfShape ℕᵒᵖ A] [HasDerivedCategory.{w} A]

/-- The Milnor short exact sequence attached to a *given* derived-limit triangle. The inclusion
descends the connecting morphism through the cokernel of `1 - shift` in degree `r - 1`, and the
projection to the inverse limit is characterized by its composites with the limit projections,
in terms of the supplied structural map `a`.

This is `DerivedCategory.isDerivedLimit_homology_shortExact` with the triangle supplied rather
than existentially quantified. -/
theorem exists_milnor_shortExact_of_distTriang
    (F : ℕᵒᵖ ⥤ DerivedCategory A) [HasProduct fun n : ℕ ↦ F.obj ⟨n⟩]
    (K : DerivedCategory A) (a : K ⟶ ∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩)
    (b : (∏ᶜ fun n : ℕ ↦ F.obj ⟨n⟩) ⟶ K⟦(1 : ℤ)⟧)
    (hT : Triangle.mk a (Pi.lift fun n : ℕ ↦
        Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) n -
          Pi.π (fun n : ℕ ↦ F.obj ⟨n⟩) (n + 1) ≫
            F.map (homOfLE (Nat.le_succ n)).op) b ∈ distTriang (DerivedCategory A))
    (r : ℤ) :
    let X : ℕ → DerivedCategory A := fun n ↦ F.obj (Opposite.op n)
    let d : (∏ᶜ X) ⟶ ∏ᶜ X := Pi.lift fun n : ℕ ↦
      Pi.π X n - Pi.π X (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
    let T := Triangle.mk a d b
    let H := DerivedCategory.homologyFunctor A r
    let H₁ := DerivedCategory.homologyFunctor A (r - 1)
    let homologySystem : ℕᵒᵖ ⥤ A := F ⋙ H
    let shiftedHomologySystem : ℕᵒᵖ ⥤ A := F ⋙ H₁
    let P : A := ∏ᶜ fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)
    let δ : P ⟶ P := Pi.lift fun n : ℕ ↦
      Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)) n -
        Pi.π (fun n : ℕ ↦ shiftedHomologySystem.obj (Opposite.op n)) (n + 1) ≫
          shiftedHomologySystem.map (homOfLE (Nat.le_succ n)).op
    ∃ (e : H₁.obj (∏ᶜ X) ≅ P)
      (i : cokernel δ ⟶ H.obj K) (q : H.obj K ⟶ limit homologySystem)
      (w : i ≫ q = 0),
      e.hom = piComparison H₁ X ∧
        cokernel.π δ ≫ i = e.inv ≫ DerivedCategory.HomologySequence.δ T (r - 1) r ∧
          (∀ n : ℕ, q ≫ limit.π homologySystem (Opposite.op n) =
            H.map a ≫ H.map (Pi.π X n)) ∧
            (ShortComplex.mk i q w).ShortExact := by
  let X : ℕ → DerivedCategory A := fun n => F.obj ⟨n⟩
  let d : (∏ᶜ X) ⟶ ∏ᶜ X := Pi.lift fun n =>
    Pi.π X n - Pi.π X (n + 1) ≫ F.map (homOfLE (Nat.le_succ n)).op
  let T := Triangle.mk a d b
  let H := homologyFunctor A r
  let H₁ := homologyFunctor A (r - 1)
  let δ₁ := Pi.lift fun n : ℕ =>
    Pi.π (fun n => H₁.obj (X n)) n - Pi.π (fun n => H₁.obj (X n)) (n + 1) ≫
      H₁.map (F.map (homOfLE (Nat.le_succ n)).op)
  let δ₀ := Pi.lift fun n : ℕ =>
    Pi.π (fun n => H.obj (X n)) n - Pi.π (fun n => H.obj (X n)) (n + 1) ≫
      H.map (F.map (homOfLE (Nat.le_succ n)).op)
  have := Stacks.DerivedProducts.hasProductsOfShape_derivedCategory (A := A) (I := ℕ)
  have := Stacks.DerivedProducts.isIso_piComparison_homologyFunctor X (r - 1)
  have := Stacks.DerivedProducts.isIso_piComparison_homologyFunctor X r
  let e₁ := asIso (piComparison H₁ X)
  let e₀ := asIso (piComparison H X)
  have hd₁ : H₁.map d ≫ e₁.hom = e₁.hom ≫ δ₁ :=
    Stacks.DerivedLimit.map_inverseSystemDifference_comp_piComparison H₁ F
  have hd₀ : H.map d ≫ e₀.hom = e₀.hom ≫ δ₀ :=
    Stacks.DerivedLimit.map_inverseSystemDifference_comp_piComparison H F
  let c := HomologySequence.δ T (r - 1) r
  have hc : δ₁ ≫ e₁.inv ≫ c = 0 := by
    rw [← cancel_epi e₁.hom, ← Category.assoc, ← hd₁]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_zero]
    exact HomologySequence.comp_δ T hT (r - 1) r
  have had : a ≫ d = 0 := comp_distTriang_mor_zero₁₂ T hT
  have hca : c ≫ H.map a = 0 := HomologySequence.δ_comp T hT (r - 1) r
  have ha : (H.map a ≫ e₀.hom) ≫ δ₀ = 0 := by
    rw [Category.assoc, ← hd₀, ← Category.assoc, ← H.map_comp, had, H.map_zero, zero_comp]
  let i := cokernel.desc δ₁ (e₁.inv ≫ c) hc
  let q₀ := kernel.lift δ₀ (H.map a ≫ e₀.hom) ha
  let eLim : limit (F ⋙ H) ≅ kernel δ₀ :=
    (inverseSystemLimitKernelForkIsLimit (F ⋙ H)).conePointUniqueUpToIso
      (limit.isLimit _)
  let q := q₀ ≫ eLim.inv
  have heLim : eLim.hom ≫ kernel.ι δ₀ = Pi.lift (fun n : ℕ => limit.π (F ⋙ H) ⟨n⟩) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  have hq : q ≫ Pi.lift (fun n : ℕ => limit.π (F ⋙ H) ⟨n⟩) = H.map a ≫ e₀.hom := by
    rw [← heLim]
    simp [q, q₀]
  have hqn : ∀ n : ℕ, q ≫ limit.π (F ⋙ H) ⟨n⟩ = H.map a ≫ H.map (Pi.π X n) := fun n => by
    simpa [e₀, X, Functor.comp_obj] using congrArg (· ≫ Pi.π (fun n => H.obj (X n)) n) hq
  have hi : cokernel.π δ₁ ≫ i = e₁.inv ≫ c := cokernel.π_desc _ _ _
  have hiq : i ≫ q = 0 := by
    rw [← cancel_epi (cokernel.π δ₁)]
    refine limit.hom_ext fun ⟨n⟩ => ?_
    simp only [Category.assoc, hqn, reassoc_of% hi, reassoc_of% hca, zero_comp, comp_zero]
  have hprev : (ShortComplex.mk δ₁ (e₁.inv ≫ c) hc).Exact := by
    apply ShortComplex.exact_of_iso _ (HomologySequence.exact₃ T hT (r - 1) r)
    exact ShortComplex.isoMk e₁ e₁ (Iso.refl _) (by simpa [T, H₁] using hd₁.symm) (by simp [c])
  have hcurr : (ShortComplex.mk (H.map a ≫ e₀.hom) δ₀ ha).Exact := by
    apply ShortComplex.exact_of_iso _ (HomologySequence.exact₂ T hT r)
    exact ShortComplex.isoMk (Iso.refl _) e₀ e₀ (by simp [T, H]) (by simpa [T, H] using hd₀.symm)
  have : Mono i := hprev.mono_cokernelDesc
  have : Epi q₀ := hcurr.epi_kernelLift
  have : Epi q := epi_comp q₀ eLim.inv
  refine ⟨e₁, i, q, hiq, rfl, hi, hqn, ?_⟩
  refine { exact := ?_, mono_f := inferInstance, epi_g := inferInstance }
  let S := ShortComplex.mk i (H.map a) (by
    rw [← cancel_epi (cokernel.π δ₁), ← Category.assoc, hi]
    simp only [Category.assoc, hca, comp_zero])
  let φ : ShortComplex.mk c (H.map a) (HomologySequence.δ_comp T hT (r - 1) r) ⟶ S :=
    { τ₁ := e₁.hom ≫ cokernel.π δ₁
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _
      comm₁₂ := by simp [S, i]
      comm₂₃ := by simp [S] }
  have hS : S.Exact :=
    (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp
      (HomologySequence.exact₁ T hT (r - 1) r)
  let ψ : ShortComplex.mk i q hiq ⟶ S :=
    { τ₁ := 𝟙 _
      τ₂ := 𝟙 _
      τ₃ := eLim.hom ≫ kernel.ι δ₀ ≫ e₀.inv
      comm₁₂ := by simp [S]
      comm₂₃ := by simp [S, q, q₀] }
  exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr hS

end DerivedCategory

end
