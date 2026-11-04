module

public import Mathlib.Algebra.Homology.DerivedCategory.ShortExact
public import StacksFrontier.Deformation.ToposThickening.ExtensionDifference

/-!
# The difference of two extensions with the same quotient, and its connecting morphism

Let `𝒜` be an abelian category and let `0 ⟶ A₁ ⟶ B₁ ⟶ C ⟶ 0` and `0 ⟶ A₂ ⟶ B₂ ⟶ C ⟶ 0` be two
short exact sequences of cochain complexes in `𝒜` with the same quotient `C`, together with a
morphism `φ : A₂ ⟶ A₁`. Dividing the fibre product `B₂ ×_C B₁` by the graph `{(i₂ a, i₁ φ a)}`
of `φ` gives a short exact sequence `0 ⟶ A₁ ⟶ E ⟶ C ⟶ 0`, the *difference* of the first
sequence and the pushout of the second along `φ` (Baer's difference). Its connecting morphism in
the derived category is the difference of the connecting morphisms:

`δ_E = δ₁ - δ₂ ≫ φ⟦1⟧`.

The proof compares the three sequences with the sequence `0 ⟶ A₁ ⊞ A₂ ⟶ B₂ ×_C B₁ ⟶ C ⟶ 0`,
which maps to each of them over the identity of `C`, by naturality of the connecting morphism.

## Main definitions

* `CochainComplex.baerDifference`: the difference sequence `0 ⟶ A₁ ⟶ E ⟶ C ⟶ 0`.

## Main results

* `CochainComplex.shortExact_baerDifference`: it is short exact.
* `CochainComplex.triangleOfSESδ_baerDifference`: `δ_E = δ₁ - δ₂ ≫ φ⟦1⟧`.

## References

* [Stacks Project, Tag 0DIZ](https://stacks.math.columbia.edu/tag/0DIZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace CochainComplex

universe w v u

attribute [-instance] CategoryTheory.catToReflQuiver

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {S₁ S₂ : ShortComplex (CochainComplex 𝒜 ℤ)} (hS₁ : S₁.ShortExact) (hS₂ : S₂.ShortExact)
  (e : S₂.X₃ ⟶ S₁.X₃) (φ : S₂.X₁ ⟶ S₁.X₁)

/-- The fibre product `B₂ ×_C B₁` of the two middle terms over the common quotient. -/
abbrev baerPullback : CochainComplex 𝒜 ℤ := pullback (S₂.g ≫ e) S₁.g

/-- The graph of `φ`, embedded in the fibre product. -/
abbrev baerGraph : S₂.X₁ ⟶ baerPullback e :=
  pullback.lift (f := S₂.g ≫ e) (g := S₁.g) S₂.f (φ ≫ S₁.f) (by simp)

/-- **The difference of two extensions with the same quotient**:
`0 ⟶ A₁ ⟶ (B₂ ×_C B₁)/graph(φ) ⟶ C ⟶ 0`. -/
abbrev baerDifference : ShortComplex (CochainComplex 𝒜 ℤ) :=
  ShortComplex.mk
    (pullback.lift (f := S₂.g ≫ e) (g := S₁.g) (0 : S₁.X₁ ⟶ S₂.X₂) S₁.f (by simp) ≫
      cokernel.π (baerGraph e φ))
    (cokernel.desc (baerGraph e φ) (pullback.fst (S₂.g ≫ e) S₁.g ≫ S₂.g) (by
      rw [← Category.assoc, pullback.lift_fst, S₂.zero]))
    (by rw [Category.assoc, cokernel.π_desc, ← Category.assoc, pullback.lift_fst, zero_comp])

include hS₁ hS₂ in
/-- The difference sequence is short exact. -/
theorem shortExact_baerDifference : (baerDifference e φ).ShortExact :=
  Deformation.ToposThickening.quotient_shortExact hS₂
    (Deformation.ToposThickening.differencePullback_shortExact (S₁ := S₂) hS₁ e)
    (baerGraph e φ) (pullback.lift_fst _ _ _)

/-- The comparison sequence `0 ⟶ A₁ ⊞ A₂ ⟶ B₂ ×_C B₁ ⟶ C ⟶ 0`. -/
abbrev baerTotal : ShortComplex (CochainComplex 𝒜 ℤ) :=
  ShortComplex.mk
    (pullback.lift (f := S₂.g ≫ e) (g := S₁.g) (biprod.snd ≫ S₂.f) (biprod.fst ≫ S₁.f)
      (by simp))
    (pullback.fst (S₂.g ≫ e) S₁.g ≫ S₂.g)
    (by rw [← Category.assoc, pullback.lift_fst, Category.assoc, S₂.zero, comp_zero])

include hS₁ hS₂ in
/-- The comparison sequence `0 ⟶ A₁ ⊞ A₂ ⟶ B₂ ×_C B₁ ⟶ C ⟶ 0` is short exact. -/
theorem shortExact_baerTotal : (baerTotal e).ShortExact := by
  have := hS₁.mono_f
  have := hS₂.mono_f
  have := hS₁.epi_g
  have := hS₂.epi_g
  refine ShortComplex.ShortExact.mk' ?_ ?_ (epi_comp _ _)
  · refine (ShortComplex.exact_iff_exact_up_to_refinements _).2 fun A z hz => ?_
    dsimp only at z hz
    obtain ⟨a₂, ha₂⟩ := hS₂.exact.lift' (z ≫ pullback.fst (S₂.g ≫ e) S₁.g) (by
      rw [Category.assoc, hz])
    obtain ⟨a₁, ha₁⟩ := hS₁.exact.lift' (z ≫ pullback.snd (S₂.g ≫ e) S₁.g) (by
      rw [Category.assoc, ← pullback.condition, ← Category.assoc, ← Category.assoc,
        Category.assoc z, hz, zero_comp])
    refine ⟨A, 𝟙 A, inferInstance, biprod.lift a₁ a₂, ?_⟩
    dsimp only
    rw [Category.id_comp]
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, biprod.lift_snd_assoc, ha₂]
    · rw [Category.assoc, pullback.lift_snd, biprod.lift_fst_assoc, ha₁]
  · refine (Preadditive.mono_iff_cancel_zero _).2 fun A z hz => ?_
    refine biprod.hom_ext _ _ ((cancel_mono S₁.f).1 ?_) ((cancel_mono S₂.f).1 ?_)
    · simpa only [Category.assoc, pullback.lift_snd, zero_comp] using
        congrArg (· ≫ pullback.snd (S₂.g ≫ e) S₁.g) hz
    · simpa only [Category.assoc, pullback.lift_fst, zero_comp] using
        congrArg (· ≫ pullback.fst (S₂.g ≫ e) S₁.g) hz

/-- The comparison sequence maps to the first sequence. -/
def baerTotalToFirst : baerTotal e ⟶ S₁ where
  τ₁ := biprod.fst
  τ₂ := pullback.snd _ _
  τ₃ := e
  comm₁₂ := (pullback.lift_snd _ _ _).symm
  comm₂₃ := by
    dsimp
    rw [Category.assoc, ← pullback.condition]

/-- The comparison sequence maps to the second sequence, through the identification `e` of the
quotients. -/
def baerTotalToSecond : baerTotal e ⟶ S₂ where
  τ₁ := biprod.snd
  τ₂ := pullback.fst _ _
  τ₃ := 𝟙 _
  comm₁₂ := (pullback.lift_fst _ _ _).symm
  comm₂₃ := by simp

/-- The comparison sequence maps to the difference sequence. -/
def baerTotalToDifference : baerTotal e ⟶ baerDifference e φ where
  τ₁ := biprod.fst - biprod.snd ≫ φ
  τ₂ := cokernel.π _
  τ₃ := 𝟙 _
  comm₁₂ := by
    dsimp
    have h : pullback.lift (f := S₂.g ≫ e) (g := S₁.g) (biprod.snd ≫ S₂.f) (biprod.fst ≫ S₁.f)
        (by simp) =
        (biprod.fst - biprod.snd ≫ φ) ≫
          pullback.lift (f := S₂.g ≫ e) (g := S₁.g) (0 : S₁.X₁ ⟶ S₂.X₂) S₁.f (by simp) +
        biprod.snd ≫ baerGraph e φ := by
      apply pullback.hom_ext
      · rw [pullback.lift_fst, Preadditive.add_comp, Category.assoc, Category.assoc,
          pullback.lift_fst, pullback.lift_fst, comp_zero, zero_add]
      · rw [pullback.lift_snd, Preadditive.add_comp, Category.assoc, Category.assoc,
          pullback.lift_snd, pullback.lift_snd, Preadditive.sub_comp, Category.assoc,
          sub_add_cancel]
    rw [h, Preadditive.add_comp, Category.assoc, Category.assoc, cokernel.condition, comp_zero,
      add_zero]
  comm₂₃ := by simp

variable [HasDerivedCategory.{w} 𝒜]

include hS₁ hS₂ in
/-- **The connecting morphism of the difference of two extensions** is the difference of their
connecting morphisms: `δ_E = e ≫ δ₁ - δ₂ ≫ φ⟦1⟧`, read on the quotient of the second sequence. -/
theorem triangleOfSESδ_baerDifference :
    DerivedCategory.triangleOfSESδ (shortExact_baerDifference hS₁ hS₂ e φ) =
      DerivedCategory.Q.map e ≫ DerivedCategory.triangleOfSESδ hS₁ -
        DerivedCategory.triangleOfSESδ hS₂ ≫ (DerivedCategory.Q.map φ)⟦(1 : ℤ)⟧' := by
  have hT := shortExact_baerTotal hS₁ hS₂ e
  have n₁ := DerivedCategory.triangleOfSESδ_naturality hT hS₁ (baerTotalToFirst e)
  have n₂ := DerivedCategory.triangleOfSESδ_naturality hT hS₂ (baerTotalToSecond e)
  have n₃ := DerivedCategory.triangleOfSESδ_naturality hT (shortExact_baerDifference hS₁ hS₂ e φ)
    (baerTotalToDifference e φ)
  simp only [baerTotalToFirst, baerTotalToSecond, baerTotalToDifference,
    CategoryTheory.Functor.map_id, Category.id_comp] at n₁ n₂ n₃
  rw [← n₃, ← n₁, ← n₂, Functor.map_sub, Functor.map_sub, Functor.map_comp,
    Functor.map_comp, Preadditive.comp_sub, Category.assoc]

end CochainComplex

end
