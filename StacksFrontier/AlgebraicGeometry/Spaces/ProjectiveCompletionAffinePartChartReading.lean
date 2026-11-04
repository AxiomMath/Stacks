module

public import StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackAdjunctionReading
public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveCompletionAffinePart

/-!
# The chart reading of the morphism from the affine part of the projective completion

Let `ψ : U ⟶ E = \underline{Spec}_X(Sym(ℰ))` be the morphism from the affine part of the projective
completion to the vector bundle (`projectiveCompletionAffinePartToVectorBundle`), classified by the
algebra map `Sym(ℰ) ⟶ u_* 𝒪_U` extending the adjunct of `q : u^*ℰ ⟶ 𝒪_U`, `m ↦ (m, 0) / s`.  At
a point `t ∈ U(T)` factoring through an étale chart `W` of `U` along `w : T ⟶ W`, with `W` over an
étale chart `V` of `X`, the point `ψ(t)` read at `V` sends the generator of `Sym(ℰ)` given by a
section `e` of `ℰ` over `V` to `q(e|_W)` pulled back along `w`.

## Main results

* `chartEval_projectiveCompletionAffinePartAlgebraMap_gen`: the reading on generators.
* `relativeSpecPointsEquiv_projectiveCompletionAffinePartToVectorBundle_app`: the point `ψ(t)` is
  the point of the relative spectrum that the reading is about.

## Implementation notes

`chartEval_projectiveCompletionAffinePartAlgebraMap_gen` counts about 199% of the default
`maxHeartbeats` in `drake --heartbeats` units (statement, proof and kernel check together) and
passes at the default limit: the definitions of the algebra map and of the module map are unfolded
in the proof, so that the generic lemma of
`StacksFrontier.AlgebraicGeometry.Spaces.ModulePullbackAdjunctionReading` matches them by rewriting
rather than by conversion.

## References

* [Stacks Project, Tag 0ERW](https://stacks.math.columbia.edu/tag/0ERW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance] HasBinaryBiproducts.of_hasBinaryProducts

namespace AlgebraicGeometry.Space

/-- `SymAlgSheaf.algebraLift_ungradedIncl_gen` at a chart `V`, with the two sides indexed as
`chartEval_compPushforwardAlgebraMap_pointOverOfPoint_of_homEquiv` indexes them. -/
theorem algebraLift_right_app_ungradedIncl_gen (B : BigFppfSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (W : AlgebraicSpaces B S hS) (𝒜 : AlgebraSheaf.{u, u} B S hS W.1 W.2)
    (F : Modules.{u, u} B S hS W.1 W.2) (φ : F ⟶ AlgebraSheaf.underlyingModule 𝒜)
    (V : SmallEtale B S hS W.1) (s : F.val.obj (op V)) :
    (SymAlgSheaf.algebraLift B S hS W 𝒜 F φ).right.hom.app (op V)
        ((symmetricAlgebra B S hS W F).ungradedIncl 1
          ((symmetricAlgebraGen B S hS W F).val.app (op V) s)) =
      φ.val.app (op V) s :=
  SymAlgSheaf.algebraLift_ungradedIncl_gen B S hS W 𝒜 F φ (op V) s

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {X : AlgebraicSpaces B S hS}
    (E : Modules.{u, u} B S hS X.1 X.2) {r : ℕ}
    (hr : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS X.1 X.2) E r)
    (hs : IsIso ((modulePullback B S hS (projectiveCompletionAffinePartHom E hr)).map
      (projectiveCompletionSectionHom E hr)))
    [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
      (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)]

omit [AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree
  (show SheafOfModules.{u} (structureRingSheaf B S hS X) from E)] in
/-- **The point `ψ(t)` of the vector bundle, read at a chart on a generator of `Sym(ℰ)`.**  For
`t ∈ U(T)` factoring through an étale chart `W` of `U` along `w : T ⟶ W`, with `W` over an étale
chart `V` of `X` along `g`, the point of the relative spectrum given by `Sym(ℰ) ⟶ u_* 𝒪_U` at `t`,
read at `V` along `w ≫ g`, sends the generator given by a section `e` of `ℰ` over `V` to the
function `q(e|_W)` on `W`, `q : u^*ℰ ⟶ 𝒪_U` the map `m ↦ (m, 0) / s`, pulled back along `w`. -/
theorem chartEval_projectiveCompletionAffinePartAlgebraMap_gen
    {T : BigFppfOver B S hS} (t : (projectiveCompletionAffinePart E hr).1.obj (op T))
    {Uc : SmallEtale B S hS (projectiveCompletionAffinePart E hr).1} (u : T ⟶ Uc.obj.left)
    {V : SmallEtale B S hS X.1}
    (g : (SmallEtale.toOver B S hS (projectiveCompletionAffinePart E hr).1).obj Uc ⟶
      (SmallEtale.toOver B S hS X.1).obj V)
    (hu : yonedaEquiv.symm t = yoneda.map u ≫ Uc.obj.hom)
    (hg : Uc.1.hom ≫ (projectiveCompletionAffinePartProj E hr).hom = yoneda.map g ≫ V.1.hom)
    (e : E.val.obj (op V)) :
    chartEval B S hS (symmetricAlgebraSheaf B S hS X E) V (u ≫ g)
        ((projectiveCompletionAffinePartProj E hr).hom.app (op T) t)
        (yonedaEquiv_symm_app_eq_of_chart B S hS (projectiveCompletionAffinePartProj E hr) t u g
          hu hg)
        (compPushforwardAlgebraMap B S hS (projectiveCompletionAffinePartAlgebraMap E hr hs)
          (pointOverOfPoint B S hS (projectiveCompletionAffinePartProj E hr) T t))
        ((symmetricAlgebra B S hS X E).ungradedIncl 1
          ((symmetricAlgebraGen B S hS X E).val.app (op V) e)) =
      ((BigFppfOver.toScheme B S hS).map u).appTop
        ((projectiveCompletionAffinePartQuotient E hr hs).val.app (op Uc)
          (modulePullbackChartSection B S hS (projectiveCompletionAffinePartProj E hr) E
            ⟨Uc, V, g, hg⟩ e)) := by
  refine (chartEval_compPushforwardAlgebraMap_pointOverOfPoint_apply B S hS
      (projectiveCompletionAffinePartProj E hr) t u g
      (projectiveCompletionAffinePartAlgebraMap E hr hs) hu hg
      ((symmetricAlgebra B S hS X E).ungradedIncl 1
          ((symmetricAlgebraGen B S hS X E).val.app (op V) e))).trans ?_
  rw [show projectiveCompletionAffinePartAlgebraMap E hr hs = SymAlgSheaf.algebraLift B S hS X
      (pushforwardAlgebra B S hS (Over.mk (projectiveCompletionAffinePartProj E hr))) E
      (projectiveCompletionAffinePartModuleMap E hr hs) from rfl,
    algebraLift_right_app_ungradedIncl_gen]
  unfold projectiveCompletionAffinePartModuleMap
  have h := directImageChartProjection_homEquiv_comp_eqToHom B S hS
      (projectiveCompletionAffinePartProj E hr) E (projectiveCompletionAffinePartQuotient E hr hs)
      g hg e
  rw [h]

/-- The point of the vector bundle given by `ψ` at a point `t` of the affine part is the point of
the relative spectrum given by `Sym(ℰ) ⟶ u_* 𝒪_U` at `t`. -/
theorem relativeSpecPointsEquiv_projectiveCompletionAffinePartToVectorBundle_app
    {T : BigFppfOver B S hS} (t : (projectiveCompletionAffinePart E hr).1.obj (op T)) :
    relativeSpecPointsEquiv B S hS (symmetricAlgebraSheaf B S hS X E) T
        ((projectiveCompletionAffinePartToVectorBundle E hr hs).hom.app (op T) t) =
      relativeSpecLiftPoint B S hS (projectiveCompletionAffinePartProj E hr)
        (projectiveCompletionAffinePartAlgebraMap E hr hs) T t :=
  relativeSpecPointsEquiv_relativeSpecLift_app B S hS (projectiveCompletionAffinePartProj E hr)
    (projectiveCompletionAffinePartAlgebraMap E hr hs) T t

end AlgebraicGeometry.Space

end
