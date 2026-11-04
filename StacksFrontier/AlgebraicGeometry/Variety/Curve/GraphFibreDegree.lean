module

public import StacksFrontier.AlgebraicGeometry.Variety.Curve.GraphDivisor
public import StacksFrontier.AlgebraicGeometry.Variety.Curve.CurveMapDegree
public import StacksFrontier.AlgebraicGeometry.Divisors.DivisorPicardClass

/-!
# Intersection numbers with the graph of an endomorphism of a curve

Let `f : C ⟶ Spec k` be a smooth proper curve over a field and `φ : C ⟶ C` a morphism over `k`
with graph `Γ_φ = (𝟙, φ) : C ⟶ C ×_k C`. The intersection number of an invertible module on
`C ×_k C` with `Γ_φ` is the degree of its pullback along the graph ([Stacks, Tag 0BEY]). In
particular:

* `V(φ) = (𝒪(Δ_C) · Γ_φ)` is the degree of `Γ_φ^* 𝒪(Δ_C)` on `C`;
* a class `pr₁^* L` pulled back from the first factor meets `Γ_φ` in `deg L` points, since
  `pr₁ ∘ Γ_φ = 𝟙`;
* a class `pr₂^* L` from the second factor meets it in `deg φ · deg L` points, since
  `pr₂ ∘ Γ_φ = φ`.

With `L = 𝒪(c₀)` the last two give `Γ_φ · ({c₀} × C + C × {c₀}) = 1 + deg φ`, the identity used
in the proof of [Stacks, Tag 03U1].

## Main results

* `AlgebraicGeometry.CurveGraph.fixedPointIntersection_eq_picardDegree`.
* `AlgebraicGeometry.CurveGraph.picardDegree_graph_fst`,
  `AlgebraicGeometry.CurveGraph.picardDegree_graph_snd`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Stacks.PicardCurve Stacks.Divisors

universe u

namespace AlgebraicGeometry.CurveGraph

variable {k : Type u} [Field k] {C : Scheme.{u}} (f : C ⟶ Spec (.of k))

/-- The degree of an invertible module on a proper curve depends on the structure morphism only
through the morphism itself. -/
theorem invertibleCurveDegree_congr {g g' : C ⟶ Spec (.of k)} (h : g = g') [IsProper g]
    [IsProper g'] (hdim : topologicalKrullDim C ≤ 1) (L : C.Modules)
    [SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2 L] :
    invertibleCurveDegree k g hdim L = invertibleCurveDegree k g' hdim L := by
  subst h
  rfl

/-- **`V(φ) = deg Γ_φ^* 𝒪(Δ_C)`**: the intersection number of the diagonal with the graph is
the degree on `C` of the pullback along the graph of the class of `𝒪(Δ_C)`
([Stacks, Tag 0BEY]). -/
theorem fixedPointIntersection_eq_picardDegree [IsCurve k f] [Smooth f] [IsProper f]
    (hdim : topologicalKrullDim C ≤ 1) (φ : C ⟶ C) (w : φ ≫ f = f) :
    fixedPointIntersection f hdim φ w =
      picardDegree k f hdim (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace
        (Stacks.Picard.schemePullbackClass (graph f φ w) (picardClass (diagonalDivisor f)))) := by
  obtain ⟨e₁⟩ := nonempty_rep_schemePullbackClass_iso (graph f φ w)
    (picardClass (diagonalDivisor f))
  obtain ⟨e₂⟩ := nonempty_rep_picardClass_iso (invertibleSheaf' (diagonalDivisor f))
    (isInvertible_invertibleSheaf_picard (diagonalDivisor f))
  let e := e₁ ≪≫ (Scheme.Modules.pullback (graph f φ w)).mapIso e₂
  rw [picardDegree_eq_invertibleCurveDegree_rep]
  let : SheafOfModules.IsInvertible C.presheaf C.ringCatSheaf.2
      ((Scheme.Modules.pullback (graph f φ w)).obj (divisorSheaf (diagonalDivisor f))) :=
    inferInstance
  rw [invertibleCurveDegree_eq_of_iso k f hdim e, fixedPointIntersection]
  refine (intersectionNumber_one_eq_invertibleCurveDegree k (pullback.fst f f ≫ f) (graph f φ w)
    _ (divisorSheaf (diagonalDivisor f))).trans ?_
  exact invertibleCurveDegree_congr (by rw [graph_fst_assoc]) hdim _

/-- **A class pulled back from the first factor meets the graph in `deg L` points**:
`deg Γ_φ^* pr₁^* L = deg L`, since `pr₁ ∘ Γ_φ = 𝟙`. -/
theorem picardDegree_graph_fst [IsCurve k f] [IsProper f] (hdim : topologicalKrullDim C ≤ 1)
    (φ : C ⟶ C) (w : φ ≫ f = f) (L : Stacks.Picard.ofScheme C) :
    picardDegree k f hdim (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace
        (Stacks.Picard.schemePullbackClass (graph f φ w)
          (Stacks.Picard.schemePullbackClass (pullback.fst f f) L))) =
      picardDegree k f hdim (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace L) := by
  rw [Stacks.Picard.schemePullbackClass_comp, graph_fst, Stacks.Picard.schemePullbackClass_id]

/-- **A class pulled back from the second factor meets the graph in `deg φ · deg L` points**:
`deg Γ_φ^* pr₂^* L = deg φ · deg L`, since `pr₂ ∘ Γ_φ = φ`. -/
theorem picardDegree_graph_snd [IsCurve k f] [IsProper f] (hdim : topologicalKrullDim C ≤ 1)
    (φ : C ⟶ C) (w : φ ≫ f = f) (L : Stacks.Picard.ofScheme C) :
    picardDegree k f hdim (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace
        (Stacks.Picard.schemePullbackClass (graph f φ w)
          (Stacks.Picard.schemePullbackClass (pullback.snd f f) L))) =
      (curveMapDegree f φ w : ℤ) *
        picardDegree k f hdim (Stacks.GluePicard.picardModelAddEquiv C.toRingedSpace L) := by
  rw [Stacks.Picard.schemePullbackClass_comp, graph_snd]
  exact picardDegree_schemePullbackClass f hdim φ w L

end AlgebraicGeometry.CurveGraph

end
