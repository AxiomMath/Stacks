module

public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.CokernelSupportImage
public import StacksFrontier.AlgebraicGeometry.Spaces.DescentLocus.EpiIsoOfEqualRank
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartSections

/-!
# The locus where a map of vector bundles of the same rank becomes an isomorphism

Let `f : X ⟶ Y` and `g : Y' ⟶ Y` be morphisms of algebraic spaces and `φ : E ⟶ F` a map of
quasi-coherent `𝒪_X`-modules with `F` of finite type. If the pullbacks of `E` and `F` to
`X ×_Y Y'` are finite locally free of the same rank, then the pullback of `φ` is an isomorphism
exactly when the image of `|Y'|` in `|Y|` misses `|f|(Supp(Coker φ))`. An epimorphism between
finite locally free modules of the same rank is an isomorphism (Stacks 089Q), so this is the
epimorphism criterion `AlgebraicGeometry.Space.epi_modulePullback_fst_map_iff_range_subset`.

This is the last step of the proof of Stacks 0D23: over the stratum on which `f_*E` is finite
locally free of the rank of `E` with formation commuting with base change, `E` descends along
`g` exactly when the counit `f^*f_*E ⟶ E` becomes an isomorphism after base change along `g`.

## Main results

* `AlgebraicGeometry.Space.isIso_modulePullback_fst_map_iff_range_subset`

## References

* [Stacks Project, Tag 0D23](https://stacks.math.columbia.edu/tag/0D23)
* [Stacks Project, Tag 089Q](https://stacks.math.columbia.edu/tag/089Q)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The isomorphism locus of a map of vector bundles of the same rank.** Let `φ : E ⟶ F` be a
map of quasi-coherent `𝒪_X`-modules with `F` of finite type, and let `g : Y' ⟶ Y` be such that the
pullbacks of `E` and `F` along the projection `X ×_Y Y' ⟶ X` are finite locally free of the same
rank `r`. Then the pullback of `φ` is an isomorphism exactly when the image of `|Y'|` in `|Y|`
misses `|f|(Supp(Coker φ))`. -/
theorem isIso_modulePullback_fst_map_iff_range_subset {X Y Y' : AlgebraicSpaces B S hS}
    (f : X ⟶ Y) (g : Y' ⟶ Y) {E F : Modules.{u, u} B S hS X.1 X.2}
    [E.IsQuasicoherentOnSite] [F.IsQuasicoherentOnSite]
    (hF : SheafOfModules.IsFiniteTypeOnSite F) (φ : E ⟶ F) {r : ℤ}
    (hE' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePullback B S hS (pullback.fst f g)).obj E) r)
    (hF' : AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfIntRank
      ((modulePullback B S hS (pullback.fst f g)).obj F) r) :
    IsIso ((modulePullback B S hS (pullback.fst f g)).map φ) ↔
      Set.range (pointsMap B S hS Y'.1 g.hom) ⊆
        (pointsMap B S hS X.1 f.hom ''
          supportOfSheaf B S hS X.1 ((SheafOfModules.toSheaf _).obj
            (cokernel φ : Modules.{u, u} B S hS X.1 X.2)))ᶜ := by
  rw [← epi_modulePullback_fst_map_iff_range_subset f g hF φ]
  refine ⟨fun h => @IsIso.epi_of_iso _ _ _ _ _ h, fun _ => ?_⟩
  exact @AlgebraicGeometry.SheafOfModules.isIso_of_epi_of_isFiniteLocallyFreeOfIntRank _ _ _ _
    (smallEtaleRingedSite_hasWeakSheafify_over B S hS _ (pullback f g).2)
    (smallEtaleRingedSite_wEqualsLocallyBijective_over B S hS _ (pullback f g).2) _ _
    (fun U a b => mul_comm (G := chartRing B S hS (pullback f g).1 (pullback f g).2 U.unop) a b)
    _ _ _ hE' hF' _ _

end AlgebraicGeometry.Space

end
