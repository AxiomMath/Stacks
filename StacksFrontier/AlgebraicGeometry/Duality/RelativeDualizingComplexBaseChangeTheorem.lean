module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexBaseChangeMain
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexGeneratorCriterion
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingComplexRestrictDiagonal

/-!
# Base change of relative dualizing complexes (Stacks 0E2Y)

Consider a cartesian square of schemes
```
X' --g'--> X
|          |
f'         f
v          v
S' --g---> S
```
with `f` flat and locally of finite presentation, and let `(K, ξ)` be a relative dualizing
complex for `f` relative to a diagonal open `W ⊆ X ×_S X`. Let `W' ⊆ X' ×_{S'} X'` be a diagonal
open of `f'` with `(g' × g')(W') ⊆ W`, and `w : W' ⟶ W` the induced morphism. Then
`K' = L(g')^*K` together with the derived base change `ξ'` of `ξ`, namely `Lw^*ξ` read through
`Lw^*Δ_*𝒪_X = Δ'_*𝒪_{X'}` (Stacks 0E23 at the Tor independent diagonal square, Stacks 0CTA)
and through transitivity of derived pullback, is a relative dualizing complex for `f'` relative
to `W'`.

## Proof

Relative perfectness of `K'` is Stacks 0DI5. For the diagonal condition, it suffices to check
that the derived pullbacks of the map defined by `ξ'` along the opens `W'_{U'}` of `W'` are
isomorphisms, for the charts `U' = g'⁻¹(U) ∩ f'⁻¹(V')` with `V ⊆ S`, `U ⊆ f⁻¹(V)`, `V' ⊆ g⁻¹(V)`
affine (the map lives on `Δ'(X')`, which they cover). By the transport of the diagonal condition
along open immersions this is the diagonal condition for the restriction of `(K', ξ')` to `U'`.
On the chart, the restriction of `ξ` to `U` is a generator (it defines an isomorphism), its base
change is a generator (the affine case, Stacks 0E2F), and `R ℰom(𝒪_{U'}, L pr₁^*K'|_{W'_{U'}})` is
`𝒪_{U'}[0]` (Stacks 0E2F (2) on sections); a generator then defines an isomorphism.

## Main results

* `AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex.baseChange`: Stacks 0E2Y.

## References

* [Stacks Project, Tag 0E2Y](https://stacks.math.columbia.edu/tag/0E2Y)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite StrictlyPerfect
open Stacks.Duality.TwistedInverseImageDuality
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces (derivedPullback)

universe u

attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.sheafTensorObjAdditive
  Stacks.Topology.SheafTensorAdditiveOnOpens.hasMapBifunctorSheafTensor

namespace AlgebraicGeometry.Scheme.Hom.DiagonalOpen

variable {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  (hpb : IsPullback g' f' f g) [Flat f] [LocallyOfFinitePresentation f]
  (D : DiagonalOpen f) (D' : DiagonalOpen f') (w : D'.W ⟶ D.W)
  (hw : w ≫ D.ι = D'.ι ≫ pullbackMapOfIsPullback hpb)

include hpb hw in
/-- **The diagonal condition for the base change, chart by chart.** For a relative dualizing
complex `(K, ξ)` for `f` on `W`, any identifications `φ`, `ψ`, and any chart
`U' = g'⁻¹(U) ∩ f'⁻¹(V')`, the derived pullback to `W'_{U'}` of the map defined by
`φ ≫ Lw^*ξ ≫ ψ` is an isomorphism. -/
theorem isIso_pull_diagonalAction_baseChange_chart (K : DerivedCategory X.Modules)
    (ξ : D.diagonalObject ⟶ D.derivedPullbackProj K)
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    (φ : D'.diagonalObject ≅ (pull w).obj D.diagonalObject)
    (ψ : (pull w).obj (D.derivedPullbackProj K) ≅ D'.derivedPullbackProj (baseChangeComplex g' K))
    (V : S.Opens) (hV : IsAffineOpen V) (U : X.Opens) (hU : IsAffineOpen U) (hUV : U ≤ f ⁻¹ᵁ V)
    (V' : S'.Opens) (hV' : IsAffineOpen V') (hV'V : V' ≤ g ⁻¹ᵁ V) :
    IsIso ((pull (D'.restrictInclusion
      (chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')).ι)).map
        (D'.diagonalAction (baseChangeComplex g' K) (φ.hom ≫ (pull w).map ξ ≫ ψ.hom))) := by
  let U' := chartBaseChange (g' := g') (f' := f') (U := U) (V' := V')
  let j' := D'.restrictInclusion U'.ι
  let eU := D.restrictDiagonalObjectIso U.ι
  let pU := D.projPullIso (D.restrict U.ι) U.ι (D.restrictInclusion U.ι)
    (D.restrictInclusion_proj U.ι) K
  have hKU := hK.transport_of (D.restrict U.ι) U.ι rfl (D.restrictInclusion U.ι)
    (D.restrictInclusion_proj U.ι) eU (D.restrictDiagonalObjectIso_mul U.ι)
  have hgU := (D.restrict U.ι).isPostcompGenerator_of_isIso_diagonalAction _ _
    hKU.isIso_diagonalAction
  let e' := D'.restrictDiagonalObjectIso U'.ι
  let p' := D'.projPullIso (D'.restrict U'.ι) U'.ι j' (D'.restrictInclusion_proj U'.ι)
    (baseChangeComplex g' K)
  have hGen := isPostcompGenerator_restrict_baseChange hpb D D' w hw hV hU hUV hV' hV'V K ξ eU pU
    hKU hgU φ ψ e' p'
  have hE := nonempty_diagonalExactSupport_restrict_baseChange hpb D D' hV hU hUV hV' hV'V K _ hKU
  have hIso := (D'.restrict U'.ι).isIso_diagonalAction_of_isPostcompGenerator _ hE _ hGen
  exact D'.isIso_pull_diagonalAction_of_transport (baseChangeComplex g' K) (D'.restrict U'.ι) _ j'
    (φ.hom ≫ (pull w).map ξ ≫ ψ.hom) e' p' (D'.restrictDiagonalObjectIso_mul U'.ι) hIso

end AlgebraicGeometry.Scheme.Hom.DiagonalOpen

namespace AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

variable {X S S' X' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {g' : X' ⟶ X} {f' : X' ⟶ S'}
  [Flat f] [LocallyOfFinitePresentation f]

/-- **Base change of a relative dualizing complex, through any identifications.** For a
relative dualizing complex `(K, ξ)` for `f` relative to `W`, a diagonal open `W'` of `f'` with
`w : W' ⟶ W` the restriction of `g' × g'`, and any identifications
`φ : Δ'_*𝒪_{X'} ≅ Lw^*Δ_*𝒪_X` and `ψ : Lw^*(L pr₁^*K|_W) ≅ L pr₁^*(L(g')^*K)|_{W'}`,
the pair `(L(g')^*K, φ ≫ Lw^*ξ ≫ ψ)` is a relative dualizing complex for `f'` relative to
`W'`. -/
theorem baseChange_of_iso (hpb : IsPullback g' f' f g) {D : DiagonalOpen f}
    {K : DerivedCategory X.Modules} {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    (D' : DiagonalOpen f') (w : D'.W ⟶ D.W)
    (hw : w ≫ D.ι = D'.ι ≫ pullbackMapOfIsPullback hpb)
    (φ : D'.diagonalObject ≅ (pull w).obj D.diagonalObject)
    (ψ : (pull w).obj (D.derivedPullbackProj K) ≅
      D'.derivedPullbackProj (DiagonalOpen.baseChangeComplex g' K)) :
    haveI : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hpb (inferInstance : Flat f)
    haveI : LocallyOfFinitePresentation f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb
        (inferInstance : LocallyOfFinitePresentation f)
    IsRelativeDualizingComplex f'
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S'.toRingedSpace f'.base)) D'
      (DiagonalOpen.baseChangeComplex g' K) (φ.hom ≫ (pull w).map ξ ≫ ψ.hom) := by
  have : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hpb (inferInstance : Flat f)
  have : LocallyOfFinitePresentation f' :=
    MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb
      (inferInstance : LocallyOfFinitePresentation f)
  constructor
  · exact isPerfectRelativeTo_derivedPullback hpb K hK.isPerfectRelativeTo
  · exact DiagonalOpen.isIso_diagonalAction_of_charts hpb D' _ _
      fun V hV U hU hUV V' hV' hV'V =>
        DiagonalOpen.isIso_pull_diagonalAction_baseChange_chart hpb D D' w hw K ξ hK φ ψ
          V hV U hU hUV V' hV' hV'V

/-- **Stacks 0E2Y: base change of a relative dualizing complex.** Let `X' = X ×_S S'` with
projections `g' : X' ⟶ X` and `f' : X' ⟶ S'`, `f` flat and locally of finite presentation, and
let `(K, ξ)` be a relative dualizing complex for `f` relative to a diagonal open `W`. For a
diagonal open `W'` of `f'` with `(g' × g')(W') ⊆ W` and `w : W' ⟶ W` the induced morphism, set
`K' = L(g')^*K` and let `ξ'` be the derived base change of `ξ`: `Lw^*ξ` read through
`Lw^*Δ_*𝒪_X = Δ'_*𝒪_{X'}` (the base change of `Δ_*` across the Tor independent diagonal square)
and transitivity of derived pullback. Then `(K', ξ')` is a relative dualizing complex for `f'`
relative to `W'`. -/
@[stacks 0E2Y "As in the source's proof, `W'` is any diagonal open of `f'` with
`(g' × g')(W') ⊆ W`, and `w : W' ⟶ W` is the induced morphism."]
theorem baseChange (hpb : IsPullback g' f' f g) {D : DiagonalOpen f}
    {K : DerivedCategory X.Modules} {ξ : D.diagonalObject ⟶ D.derivedPullbackProj K}
    (hK : IsRelativeDualizingComplex f
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S.toRingedSpace f.base)) D K ξ)
    (D' : DiagonalOpen f') (w : D'.W ⟶ D.W)
    (hw : w ≫ D.ι = D'.ι ≫ pullbackMapOfIsPullback hpb) :
    haveI : Flat f' := MorphismProperty.of_isPullback (P := @Flat) hpb (inferInstance : Flat f)
    haveI : LocallyOfFinitePresentation f' :=
      MorphismProperty.of_isPullback (P := @LocallyOfFinitePresentation) hpb
        (inferInstance : LocallyOfFinitePresentation f)
    IsRelativeDualizingComplex f'
      (RingedSpace.canonicalCertifiedDerivedSheafTensoringFamily
        (RingedSpace.inverseImage S'.toRingedSpace f'.base)) D'
      (DiagonalOpen.baseChangeComplex g' K)
      (D.baseChangeDiagonalMap D' g' w (DiagonalOpen.proj_baseChange hpb D D' w hw)
        (DiagonalOpen.baseChangeDiagonalIso hpb D D' w hw) K ξ) :=
  hK.baseChange_of_iso hpb D' w hw (DiagonalOpen.baseChangeDiagonalIso hpb D D' w hw).symm
    (DiagonalOpen.derivedPullbackProjBaseChangeIso D D' g' w
      (DiagonalOpen.proj_baseChange hpb D D' w hw) K)

end AlgebraicGeometry.Scheme.Hom.IsRelativeDualizingComplex

end
