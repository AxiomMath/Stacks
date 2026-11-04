module

public import StacksFrontier.AlgebraicGeometry.Picard.DivisorsOnSmoothCurves
public import StacksFrontier.AlgebraicGeometry.Picard.DivisorSheafDegree
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.SmoothRelativeDimension
public import StacksFrontier.AlgebraicGeometry.Variety.NumericalIntersection
public import StacksFrontier.AlgebraicGeometry.GroupScheme.ZPowRank0BFG
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The graph of an endomorphism of a smooth curve as a divisor on `C × C`

Let `f : C ⟶ Spec k` be a smooth separated curve over a field and `φ : C ⟶ C` a morphism over
`k`. The graph `Γ_φ = (𝟙, φ) : C ⟶ C ×_k C` is a closed immersion, and its image is an effective
Cartier divisor on the surface `C ×_k C`: it is the image of a section of the first projection,
which is a smooth relative curve, and such an image is finite locally free of rank one over the
base, hence a relative effective Cartier divisor ([Stacks, Tag 0B9D]). For `φ = 𝟙` this is the
diagonal `Δ_C`.

The intersection number `V(φ) = Δ_C · Γ_φ` of [Stacks, Tag 03U1] is the intersection number
`(𝒪(Δ_C) · Γ_φ)` of [Stacks, Tag 0BEP] on the proper surface `C ×_k C`, of the invertible module
of the diagonal with the closed curve `Γ_φ`.

## Main definitions

* `AlgebraicGeometry.CurveGraph.graph`: the graph `(𝟙, φ) : C ⟶ C ×_k C`.
* `AlgebraicGeometry.CurveGraph.graphDivisor`: its image, as an ideal sheaf on `C ×_k C`.
* `AlgebraicGeometry.CurveGraph.diagonalDivisor`: the diagonal `Δ_C`.
* `AlgebraicGeometry.CurveGraph.fixedPointIntersection`: `V(φ) = (𝒪(Δ_C) · Γ_φ)`.

## Main results

* `AlgebraicGeometry.CurveGraph.isClosedImmersion_graph`: the graph of a morphism into a
  separated scheme is a closed immersion.
* `AlgebraicGeometry.CurveGraph.isEffectiveCartierDivisor_graphDivisor`: the graph of an
  endomorphism of a smooth separated curve is an effective Cartier divisor on `C ×_k C`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.Divisors

universe u

namespace AlgebraicGeometry.CurveGraph

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))

/-- **The graph** `Γ_φ = (𝟙, φ) : C ⟶ C ×_k C` of a morphism `φ : C ⟶ C` over `k`. -/
def graph (φ : C ⟶ C) (w : φ ≫ f = f) : C ⟶ pullback f f :=
  pullback.lift (𝟙 C) φ (by rw [Category.id_comp, w])

/-- The first coordinate of the graph is the identity. -/
@[reassoc (attr := simp)]
theorem graph_fst (φ : C ⟶ C) (w : φ ≫ f = f) : graph f φ w ≫ pullback.fst f f = 𝟙 C :=
  pullback.lift_fst _ _ _

/-- The second coordinate of the graph `Γ_φ` is `φ`. -/
@[reassoc (attr := simp)]
theorem graph_snd (φ : C ⟶ C) (w : φ ≫ f = f) : graph f φ w ≫ pullback.snd f f = φ :=
  pullback.lift_snd _ _ _

/-- **The graph of a morphism into a separated scheme is a closed immersion.** -/
@[ega "I 5.3.11" "special case"]
instance isClosedImmersion_graph [IsSeparated f] (φ : C ⟶ C) (w : φ ≫ f = f) :
    IsClosedImmersion (graph f φ w) := by
  have : IsClosedImmersion (graph f φ w ≫ pullback.fst f f) := by
    rw [graph_fst]
    infer_instance
  exact IsClosedImmersion.of_comp (graph f φ w) (pullback.fst f f)

/-- **The image of the graph**, as a closed subscheme of `C ×_k C`. -/
def graphDivisor (φ : C ⟶ C) (w : φ ≫ f = f) : (pullback f f).IdealSheafData :=
  (graph f φ w).ker

/-- The image of the graph maps isomorphically onto `C` by the first projection. -/
theorem isIso_graphDivisor_subschemeι_fst [IsSeparated f] (φ : C ⟶ C) (w : φ ≫ f = f) :
    IsIso ((graphDivisor f φ w).subschemeι ≫ pullback.fst f f) := by
  let g := graph f φ w
  have hiso : IsIso g.toImage :=
    IsClosedImmersion.isIso_of_ker_eq g g.imageι g.toImage g.toImage_imageι
      (Scheme.IdealSheafData.ker_subschemeι g.ker).symm
  have h : g.imageι ≫ pullback.fst f f = inv g.toImage := by
    rw [← cancel_epi g.toImage, IsIso.hom_inv_id, ← Category.assoc, g.toImage_imageι]
    exact graph_fst f φ w
  show IsIso (g.imageι ≫ pullback.fst f f)
  rw [h]
  infer_instance

/-- **The graph of an endomorphism of a smooth separated curve is an effective Cartier divisor
on `C ×_k C`.** -/
theorem isEffectiveCartierDivisor_graphDivisor [IsCurve k f] [Smooth f]
    (φ : C ⟶ C) (w : φ ≫ f = f) :
    Stacks.Divisors.IsEffectiveCartierDivisor (graphDivisor f φ w) := by
  have hf : SmoothOfRelativeDimension 1 f := smoothOfRelativeDimension_one_of_isCurve k f
  have : SmoothOfRelativeDimension 1 (pullback.fst f f) :=
    (smoothOfRelativeDimension_isStableUnderBaseChange 1).of_isPullback
      (IsPullback.of_hasPullback f f).flip hf
  have := isIso_graphDivisor_subschemeι_fst f φ w
  have := Stacks.Morphisms.isFiniteLocallyFree_of_isIso
    ((graphDivisor f φ w).subschemeι ≫ pullback.fst f f)
  exact (isRelativeEffectiveCartierDivisor_of_isFiniteLocallyFree (pullback.fst f f)
    (graphDivisor f φ w)).1

/-- **The diagonal** `Δ_C ⊆ C ×_k C`, the graph of the identity. -/
abbrev diagonalDivisor : (pullback f f).IdealSheafData :=
  graphDivisor f (𝟙 C) (Category.id_comp f)

/-- The diagonal of a smooth separated curve is an effective Cartier divisor on `C ×_k C`. -/
instance isEffectiveCartierDivisor_diagonalDivisor [IsCurve k f] [Smooth f] :
    Stacks.Divisors.IsEffectiveCartierDivisor (diagonalDivisor f) :=
  isEffectiveCartierDivisor_graphDivisor f (𝟙 C) (Category.id_comp f)

/-- The module `𝒪(Δ_C)` of the diagonal is invertible. -/
instance isInvertible_diagonalDivisorSheaf [IsCurve k f] [Smooth f] :
    SheafOfModules.IsInvertible (pullback f f).presheaf (pullback f f).ringCatSheaf.2
      (divisorSheaf (diagonalDivisor f)) :=
  Stacks.Divisors.isInvertible_divisorSheaf (diagonalDivisor f)

/-- **The intersection number `V(φ) = Δ_C · Γ_φ`** on `C ×_k C` ([Stacks, Tag 03U1]): the
intersection number `(𝒪(Δ_C) · Γ_φ)` of [Stacks, Tag 0BEP] of the invertible module of the
diagonal with the graph of `φ`, a closed curve on the proper surface `C ×_k C`. -/
@[sga "4½ Rapport 5.3"]
def fixedPointIntersection [IsCurve k f] [Smooth f] [IsProper f]
    (hdim : topologicalKrullDim C ≤ 1) (φ : C ⟶ C) (w : φ ≫ f = f) : ℤ :=
  intersectionNumber k (pullback.fst f f ≫ f) (graph f φ w) 1 (by simpa using hdim)
    (fun _ => divisorSheaf (diagonalDivisor f))

end AlgebraicGeometry.CurveGraph

end
