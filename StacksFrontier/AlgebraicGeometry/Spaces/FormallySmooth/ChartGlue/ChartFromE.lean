module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.AffineObj
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.ChartLemma
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.ChartGlue.ChartSmooth

/-!
# The chart of the gluing from an affine object étale over `U ×_Y T'`

Let `a : yoneda U ⟶ X` be étale (hence formally étale) with `a ≫ f` formally smooth, and let `E`
be an affine object with an étale morphism `E ⟶ U ×_Y T'`. Then `R = Γ(E, ⊤)` is a formally smooth
algebra over `A' = Γ(T', ⊤)`, and the section of `X` over `Spec R ≅ E` is formally étale relative
to `T'` and lies over `y`. These are the hypotheses of `AlgebraicGeometry.Space.ChartGlue.algChart`
and of the gluing.

## Main results

* `AlgebraicGeometry.Space.ChartGlue.relFormallyEtale_of_iso`: transport along an isomorphism.
* `AlgebraicGeometry.Space.ChartGlue.chart_of_etale`: the three properties of the chart.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space.ChartGlue

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T' : BigFppfOver B S hS}
  [IsAffine ((BigFppfOver.toScheme B S hS).obj T')]
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {f : X ⟶ Y} {y : Y.obj (op T')}

omit [IsAffine ((BigFppfOver.toScheme B S hS).obj T')] in
/-- **Relative formal étaleness transports along an isomorphism over `T'`.** -/
theorem relFormallyEtale_of_iso {E E' : BigFppfOver B S hS} (eT : E ⟶ T') (g₀ : X.obj (op E))
    (h : RelFormallyEtale B S hS T' f y eT g₀) (ι : E' ≅ E) :
    RelFormallyEtale B S hS T' f y (ι.hom ≫ eT) (X.map ι.hom.op g₀) := by
  intro C₀ D₀ hC hD j hj c g hg e₀ he₀ hge
  obtain ⟨e, ⟨he₁, he₂, he₃⟩, heu⟩ := h C₀ D₀ hC hD j hj c g hg (e₀ ≫ ι.hom)
    (by rw [Category.assoc, he₀]) (by rw [op_comp, Functor.map_comp_apply, hge])
  refine ⟨e ≫ ι.inv, ⟨?_, ?_, ?_⟩, fun e' ⟨he'₁, he'₂, he'₃⟩ ↦ ?_⟩
  · rw [← Category.assoc, he₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  · rw [Category.assoc, Iso.inv_hom_id_assoc, he₂]
  · rw [← Functor.map_comp_apply, ← op_comp, Category.assoc, Iso.inv_hom_id,
      Category.comp_id, he₃]
  · rw [Iso.eq_comp_inv]
    refine heu _ ⟨?_, ?_, ?_⟩
    · rw [← Category.assoc, he'₁]
    · rw [Category.assoc, he'₂]
    · rw [op_comp, Functor.map_comp_apply, he'₃]

variable (B S hS T' f y) {U : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X)
  (hrep : yoneda.relativelyRepresentable (a ≫ f))
  {E : BigFppfOver B S hS} [IsAffine ((BigFppfOver.toScheme B S hS).obj E)]
  (eZ : E ⟶ UZ B S hS T' f y a hrep)

/-- The section of `X` over `Spec Γ(E, ⊤)`. -/
def chartPoint : letI := ringAlg B S hS T' (eZ ≫ UZsnd B S hS T' f y a hrep)
    X.obj (op (specObj B S hS T' (ringE B S hS (E := E)) (contains_specRingE B S hS))) :=
  X.map (specIso B S hS T' (eZ ≫ UZsnd B S hS T' f y a hrep)).hom.op
    (aPt (a := a) (eZ ≫ UZfst B S hS T' f y a hrep))

variable {B S hS T' f y a hrep eZ}

/-- If `a` is formally étale, `a ≫ f` is formally smooth and `yoneda.map eZ` is formally étale,
then the section `chartPoint` of `X` over `Spec Γ(E, ⊤)` maps under `f` to the pullback of `y`, is
formally étale relative to `T'`, and `Γ(E, ⊤)` is a formally smooth algebra over `Γ(T', ⊤)`. -/
theorem chart_of_etale (hfa : FormallyEtale a) (hfs : FormallySmooth (a ≫ f))
    (hε : FormallyEtale (yoneda.map eZ)) :
    letI := ringAlg B S hS T' (eZ ≫ UZsnd B S hS T' f y a hrep)
    f.app _ (chartPoint B S hS T' f y a hrep eZ) =
        Y.map (specToT B S hS T' _ (contains_specRingE B S hS)).op y ∧
      RelFormallyEtale B S hS T' f y (specToT B S hS T' _ (contains_specRingE B S hS))
        (chartPoint B S hS T' f y a hrep eZ) ∧
      Algebra.FormallySmooth (ringOf B S hS T') (ringE B S hS (E := E)) := by
  let := ringAlg B S hS T' (eZ ≫ UZsnd B S hS T' f y a hrep)
  set ι := specIso B S hS T' (eZ ≫ UZsnd B S hS T' f y a hrep)
  have hιT := specIso_hom_comp B S hS T' (eZ ≫ UZsnd B S hS T' f y a hrep)
  have hyE : f.app _ (aPt (a := a) (eZ ≫ UZfst B S hS T' f y a hrep)) =
      Y.map (eZ ≫ UZsnd B S hS T' f y a hrep).op y := by
    rw [← aPt_comp, f.naturality_apply, UZ_compat, ← Functor.map_comp_apply, ← op_comp]
  have hpair := pairFormallyEtale_of_formallyEtale eZ hε
  refine ⟨?_, ?_, ?_⟩
  · rw [chartPoint, f.naturality_apply, hyE, ← Functor.map_comp_apply, ← op_comp, hιT]
  · have := relFormallyEtale_of_iso _ _ (relFormallyEtale_of_pair hfa hyE hpair) ι
    rw [hιT] at this
    exact this
  · refine formallySmooth_of_relLift B S hS T' _ (contains_specRingE B S hS) ?_
    intro C₀ D₀ hC hD j hj c e₀ he₀
    obtain ⟨e, he₁, he₂⟩ := exists_lift_of_pair hfs hyE hpair C₀ D₀ hC hD j hj c (e₀ ≫ ι.hom)
      (by rw [Category.assoc, hιT, he₀])
    refine ⟨e ≫ ι.inv, ?_, ?_⟩
    · rw [← Category.assoc, he₁, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    · rw [← hιT, Category.assoc, Iso.inv_hom_id_assoc, he₂]

end AlgebraicGeometry.Space.ChartGlue

end
