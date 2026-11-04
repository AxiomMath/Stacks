module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.FiniteLocallyFree
public import StacksFrontier.AlgebraicGeometry.Modules.FiniteLocallyFreeDescent.Fpqc
public import StacksFrontier.AlgebraicGeometry.Spaces.Coverings
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentEtaleChart
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
import StacksCore.Tactic.StacksAttribute

/-!
# Finite local freeness of a module on an algebraic space descends along fpqc coverings

Let `X` be an algebraic space over a scheme `S` and let `F` be an `𝒪_X`-module on the small
étale site of `X`. If `{f i : X i ⟶ X}` is an fpqc covering of `X` and every pullback `(f i)^*F`
is finite locally free, then `F` is finite locally free, provided the modules on the affine étale
charts of `X` are compared with Zariski modules on their schemes as recorded by the hypothesis
`hchart`.

## Main results

* `AlgebraicGeometry.Space.isFiniteLocallyFreeOnSite_of_pullback_isFpqcCovering`: if `F` has
  finite locally free pullbacks along an fpqc covering and satisfies the chart transport
  hypothesis `hchart`, then `F` is finite locally free.

## References

* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DN](https://stacks.math.columbia.edu/tag/03DN)
* [Stacks Project, Tag 03MQ](https://stacks.math.columbia.edu/tag/03MQ)
* [Stacks Project, Tag 05B2](https://stacks.math.columbia.edu/tag/05B2)
* [Stacks Project, Tag 060T](https://stacks.math.columbia.edu/tag/060T)
* [Stacks Project, Tag 060X](https://stacks.math.columbia.edu/tag/060X)
-/

@[expose] public section

open CategoryTheory

universe u v

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `F` be an `𝒪_X`-module on the small étale site of an algebraic space `X` over `S` and let
`{f i : X i ⟶ X}` be an fpqc covering such that every pullback `(f i)^*F` is finite locally free.
Suppose that over every affine étale chart `T` of `X` there is a quasi-coherent Zariski module `M`
on the scheme of `T` whose finite local freeness implies that of `F` over `T`, and whose pullbacks
along morphisms factoring through some `f i` are finite locally free whenever `(f i)^*F` is
(the hypothesis `hchart`). Then `F` is finite locally free. -/
theorem isFiniteLocallyFreeOnSite_of_pullback_isFpqcCovering
    {I : Type v} {X : AlgebraicSpaces B S hS} {Xi : I → AlgebraicSpaces B S hS}
    (f : ∀ i, Xi i ⟶ X) (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom)
    (F : Modules.{u, u} B S hS X.obj X.property)
    (hchart : ∀ (T : SmallEtale B S hS X.obj) (_ : IsAffine (chartScheme T)),
      ∃ (M : (chartScheme T).Modules) (_ : M.IsQuasicoherent),
        (SheafOfModules.IsFiniteLocallyFree.{u, u, u} M →
          SheafOfModules.IsFiniteLocallyFreeOnSite
            (R := (Stacks.SheafOfModules.Tensor.ringSheaf
              ((smallEtaleRingedSite B S hS X.obj X.property).over T).O))
            (F.over T)) ∧
        ∀ (T' : BigFppfOver B S hS) (g : T' ⟶ (SmallEtale.toOver B S hS X.obj).obj T)
          (i : I) (a : yoneda.obj T' ⟶ (Xi i).obj),
          a ≫ (f i).hom = yoneda.map g ≫ T.obj.hom →
          SheafOfModules.IsFiniteLocallyFreeOnSite ((modulePullback B S hS (f i)).obj F) →
          SheafOfModules.IsFiniteLocallyFree.{u, u, u}
            ((Scheme.Modules.pullback ((BigFppfOver.toScheme B S hS).map g)).obj M))
    (hF : ∀ i, SheafOfModules.IsFiniteLocallyFreeOnSite
      ((modulePullback B S hS (f i)).obj F)) :
    SheafOfModules.IsFiniteLocallyFreeOnSite F := by
  refine
    (Stacks.SheafOfModules.isFiniteLocallyFreeOnSite_iff_exists_cover_isFiniteLocallyFreeOnSite
      (smallEtaleRingedSite B S hS X.obj X.property) F).2
      ⟨{T : SmallEtale B S hS X.obj // IsAffine (chartScheme T)}, fun T ↦ T.1,
        SmallEtale.coversTop_affineCharts B S hS X.obj, ?_⟩
  rintro ⟨T, hT⟩
  obtain ⟨M, hMqc, hfree, htransport⟩ := hchart T hT
  obtain ⟨E, _, hmem, hfactor⟩ :=
    hf.2 (⟨(SmallEtale.toOver B S hS X.obj).obj T, hT⟩ : BigAffineFppf B S hS) T.obj.hom
  have hmem' : (E.map (BigAffineFppf.toScheme B S hS)).presieve₀ ∈
      Scheme.fpqcPrecoverage (chartScheme T) := by
    rwa [PreZeroHypercover.presieve₀_map]
  refine hfree ?_
  refine isFiniteLocallyFree_of_pullback_fpqcCover M (hqc := hMqc)
    { toPreZeroHypercover := E.map (BigAffineFppf.toScheme B S hS), mem₀ := hmem' } fun j ↦ ?_
  obtain ⟨i, a, ha⟩ := hfactor j
  exact htransport _ ((BigAffineFppf.inclusion B S hS).map (E.f j)) i a ha (hF i)

end AlgebraicGeometry.Space

end
