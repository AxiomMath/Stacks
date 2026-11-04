module

public import StacksFrontier.AlgebraicGeometry.Size.Pullback
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleSourceModuleFMapCompDischarge
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionChartRealizedSchemeSizeBound
public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.SquareZeroExtensionQuotientRealization

/-!
# Realizing a square-zero extension whose ideal is pulled back from an affine scheme

Let `E` be a square-zero extension `0 → ℐ → 𝒜 → 𝒪_X → 0` on the small étale site of an algebraic
space `X` over `f : X ⟶ Y` (the data of Stacks 05ZT), and suppose that `ℐ ≅ g^*ℳ` for a morphism
`g : X ⟶ T` to an affine scheme `T` and a quasi-coherent `𝒪_T`-module `ℳ`. Over an affine open
`V` of an étale chart `U` of `X`, the sections of `g^*ℳ` are `𝒪_X(V) ⊗_{Γ(T, 𝒪_T)} ℳ(T)`
(the chart form of Stacks 083K), so `#ℐ(V) ≤ max ℵ₀ (max (size U) #ℳ(T))`, and
`#𝒜(V) ≤ #𝒪_X(V) · #ℐ(V)` is bounded by the same cardinal. When `#ℳ(T)` is below the cutoff of
the big fppf site, this cardinal is too, so the site contains every chart thickening `U'`, and the
thickened quotient `X' = U'/R'` of Stacks 05ZT is realized on the given site. In the proof of
Stacks 0D3X this is the step showing that the thickening `X₀ ⊂ X'` built from the solution `𝒪'`
lives on the original site, its ideal being `f^*𝒞_{Y₀/Y}`.

## Main definitions

* `AlgebraicGeometry.Space.chartOpensSelfChartDiagram`: an open of an étale chart of `X` over the
  identity chart of `T`, along `g : X ⟶ T`.

## Main results

* `AlgebraicGeometry.Space.mk_modulePullback_chartOpens_le`: the size bound on the sections of
  `g^*ℳ` over an affine open of a chart.
* `AlgebraicGeometry.Space.SquareZeroExtension.contains_chartRealizedScheme_of_iso_modulePullback`:
  the site contains every chart thickening.
* `AlgebraicGeometry.Space.SquareZeroExtension.nonempty_realization_of_iso_modulePullback`: the
  extension is realized on the given site.

## References

* [Stacks Project, Tag 05ZT](https://stacks.math.columbia.edu/tag/05ZT)
* [Stacks Project, Tag 083K](https://stacks.math.columbia.edu/tag/083K)
* [Stacks Project, Tag 0D3X](https://stacks.math.columbia.edu/tag/0D3X)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite Cardinal

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An open of an étale chart over the identity chart of a scheme**: for `g : X ⟶ T`, an open
`V` of an étale chart `U` of `X` and the identity chart of `T`, joined by the composite
`V ⟶ U ⟶ X ⟶ T`. -/
def chartOpensSelfChartDiagram {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (g : X ⟶ schemeSpace T) (U : SmallEtale B S hS X.1) (V : (chartScheme U).Opens) :
    ChartDiagram B S hS X.1 (schemeSpace T).1 g.hom where
  U := (chartOpens B S hS U).obj V
  V := selfChart B S hS T
  g := yoneda.preimage (((chartOpens B S hS U).obj V).obj.hom ≫ g.hom)
  comm := by
    rw [Functor.map_preimage]
    exact (Category.comp_id _).symm

/-- The sections of the structure sheaf over an affine open of a chart are bounded by its size. -/
private theorem mk_sections_chartOpens_le_size {X : AlgebraicSpaces B S hS}
    (U : SmallEtale B S hS X.1) (V : (chartScheme U).affineOpens) :
    #((smallEtaleRingedTopos B S hS X).O.obj.obj (op ((chartOpens B S hS U).obj V.1))) ≤
      (chartScheme U).size :=
  (Scheme.mk_sections_coe_opens (chartScheme U) V.1).trans_le
    (Scheme.mk_sections_le_size (chartScheme U) V)

/-- **The sections of a pulled-back quasi-coherent module over an affine open of a chart are
bounded.** For `g : X ⟶ T` with `T` affine and `ℳ` quasi-coherent on `T`, the sections of `g^*ℳ`
over an affine open `V` of an étale chart `U` are `𝒪_X(V) ⊗_{Γ(T)} ℳ(T)` (Stacks 083K), of
cardinality at most `max ℵ₀ (max (size U) #ℳ(T))`. -/
theorem mk_modulePullback_chartOpens_le {X : AlgebraicSpaces B S hS} {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (g : X ⟶ schemeSpace T)
    (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2)
    (hM : M.IsQuasicoherentOnSite) (U : SmallEtale B S hS X.1)
    (V : (chartScheme U).affineOpens) :
    #(((modulePullback B S hS g).obj M).val.obj (op ((chartOpens B S hS U).obj V.1))) ≤
      max ℵ₀ (max (chartScheme U).size #(M.val.obj (op (selfChart B S hS T)))) := by
  let d := chartOpensSelfChartDiagram g U V.1
  let := chartDiagramAlgebra B S hS g d
  have haU : IsAffine (V.1 : Scheme.{u}) := V.2
  refine (Cardinal.mk_congr (Equiv.ofBijective _
      (bijective_modulePullbackChartBaseChange_of_isQuasicoherentOnSite B S hS g M hM d haU
        hT))).symm.trans_le
    (Cardinal.mk_tensorProduct_le.trans (max_le_max le_rfl (max_le_max ?_ le_rfl)))
  exact mk_sections_chartOpens_le_size U V

namespace SquareZeroExtension

variable {X Y : AlgebraicSpaces B S hS} {f : X ⟶ Y} (E : SquareZeroExtension B S hS f)

/-- **A site contains the chart thickenings of an extension whose ideal is pulled back from an
affine scheme with small sections.** If `ℐ ≅ g^*ℳ` for `g : X ⟶ T`, `T` affine, `ℳ`
quasi-coherent with `#ℳ(T)` below the cutoff, every chart thickening `U'` lies in the site: the
sections of `𝒜` over the affine opens of `U` are bounded by `max ℵ₀ (max (size U) #ℳ(T))`. -/
theorem contains_chartRealizedScheme_of_iso_modulePullback {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (g : X ⟶ schemeSpace T)
    (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2)
    (hM : M.IsQuasicoherentOnSite) (hMB : #(M.val.obj (op (selfChart B S hS T))) < B.cutoff)
    (eI : E.I ≅ (modulePullback B S hS g).obj M) (U : SmallEtale B S hS X.1) :
    B.Contains (E.chartRealizedScheme U) := by
  have hκ : max ℵ₀ (max (chartScheme U).size #(M.val.obj (op (selfChart B S hS T)))) <
      B.cutoff :=
    max_lt B.aleph0_lt_cutoff (max_lt U.obj.left.left.2 hMB)
  refine E.contains_chartRealizedScheme_of_mk_le U hκ fun V => (E.mk_A_le_mk_mul _).trans ?_
  have hinj : Function.Injective (eI.hom.val.app (op ((chartOpens B S hS U).obj V.1))) :=
    Function.LeftInverse.injective (g := eI.inv.val.app (op ((chartOpens B S hS U).obj V.1)))
      fun x => congrArg (fun φ => (φ.val.app (op ((chartOpens B S hS U).obj V.1))).hom x)
        eI.hom_inv_id
  have hO : #((smallEtaleRingedTopos B S hS X).O.obj.obj (op ((chartOpens B S hS U).obj V.1))) ≤
      max ℵ₀ (max (chartScheme U).size #(M.val.obj (op (selfChart B S hS T)))) :=
    (mk_sections_chartOpens_le_size U V).trans ((le_max_left _ _).trans (le_max_right _ _))
  exact (mul_le_mul' hO ((Cardinal.mk_le_of_injective hinj).trans
    (mk_modulePullback_chartOpens_le hT g M hM U V))).trans
    (Cardinal.mul_eq_self (le_max_left _ _)).le

/-- **An extension whose ideal is pulled back from an affine scheme with small sections is
realized on the given site** (Stacks 05ZT): the site contains the chart thickenings of any
presentation, so the thickened quotient `X' = U'/R'` is an algebraic space of the site. -/
theorem nonempty_realization_of_iso_modulePullback {T : BigFppfOver B S hS}
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj T)) (g : X ⟶ schemeSpace T)
    (M : Modules.{u, u} B S hS (schemeSpace T).1 (schemeSpace T).2)
    (hM : M.IsQuasicoherentOnSite) (hMB : #(M.val.obj (op (selfChart B S hS T))) < B.cutoff)
    (eI : E.I ≅ (modulePullback B S hS g).obj M) :
    Nonempty (ToposRealization E) :=
  E.nonempty_realization_of_contains_chartRealizedScheme
    (presentationOfIsAlgebraicSpace B S hS X.1 X.2)
    (presentationOfIsAlgebraicSpace B S hS Y.1 Y.2)
    (E.contains_chartRealizedScheme_of_iso_modulePullback hT g M hM hMB eI _)
    (E.contains_chartRealizedScheme_of_iso_modulePullback hT g M hM hMB eI _)

end SquareZeroExtension

end AlgebraicGeometry.Space

end
