module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFreeRank.Field
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteLocallyFreeCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.LocallyPrincipalPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.CategoryTheory.Sites.Modules.FiniteLocallyFreeOfRank
public import StacksFrontier.RingTheory.Module.LocallyFree.SheafBridge

/-!
# The sections of a module of rank `r` over the affine charts of a covering

Let `F` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let `H` be
an `𝒪_F`-module which is finite locally free of rank `r` in the sense of the rank clause of
Stacks 0409, `AlgebraicGeometry.RingedSite.IsFiniteLocallyFreeOfRank`: over the members of a
covering of every étale chart, `H` is a coproduct of `r` copies of the structure sheaf.  This
file reads that condition on sections: the affine étale charts over which the sections of `H`
form a finite locally free module of rank `r` cover every étale chart.

This is the implication from Stacks 0409 to the *chartwise* reading of the rank, that is, the
forward direction of the rank form of Descent, Proposition 03DX (2); the converse, which needs
the module to be cartesian on affine charts, is
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_freeRankPresieve`.  The direction proved
here needs no hypothesis, because a *finite* coproduct in an abelian category is a biproduct and
taking sections is additive.

## Main results

* `AlgebraicGeometry.RingedSite.nonempty_basis_sections_of_isColimitCofanUnit`: if a module on a
  slice of a ringed site at an object is a coproduct of `r` copies of the structure sheaf, its
  sections over every object lying over that one form a free module with a basis indexed by
  `Fin r`.
* `AlgebraicGeometry.Space.freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank`: **the
  forward direction of the rank form of Descent, Proposition 03DX (2).**  For a module of
  rank `r`, the affine étale charts over which the sections form a finite locally free module of
  rank `r` generate a covering sieve of every étale chart.

## Implementation notes

The sections of the restriction `M.over A` of a module to the slice at a chart `A` over an
object `W` of that slice are the sections `M.val.obj (op W.left)` of `M` itself, and the
coefficient ring `((RingedSite.ringSheaf X).over A).obj.obj (op W)` is `chartRing` of `W.left`;
both identifications hold by `rfl`, since restriction to a slice is pushforward along
`CategoryTheory.Over.forget`.  The two spellings nevertheless produce different instance terms,
so the basis is transported with `Module.Basis.map` along an explicitly supplied linear
equivalence rather than by rewriting.

The covering obligation is discharged pointwise, through
`AlgebraicGeometry.Space.smallEtale_sieve_of_pointwise_covering`: a point of the chart is
lifted into a member of the trivialising covering by
`AlgebraicGeometry.Space.exists_mem_sieve_scheme_point`, and that member is replaced by an
affine open around the lifted point by `AlgebraicGeometry.Space.exists_affine_chart_at`.  The
affine chart so obtained still lies over the member of the covering, so the coproduct
decomposition is available on it.

## References

* [Stacks Project, Tag 0409](https://stacks.math.columbia.edu/tag/0409)
* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 00NW](https://stacks.math.columbia.edu/tag/00NW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.RingedSite

/-- **The sections of a coproduct of `r` copies of the structure sheaf on a slice are free of
rank `r`.**  If the restriction of a module `H` on a ringed site to the slice at an object `A` is
a colimit cofan of `r` copies of the structure sheaf of that slice, then for every object `V`
equipped with a morphism to `A` the sections of `H` over `V` form a free module over the sections
of the structure sheaf, with a basis indexed by `Fin r`.

Taking sections is additive and the cofan is finite, so it stays a colimit cofan after
evaluation; this is
`Stacks.SheafOfModules.exists_finsuppEquiv_of_isColimit_cofan` on the slice at `A`, read at the
object `V ⟶ A` of that slice. -/
theorem nonempty_basis_sections_of_isColimitCofanUnit (X : RingedSite.{u + 1, u, u})
    (H : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) (r : ℕ) (A : X.C)
    (ι : ∀ _ : Fin r,
      SheafOfModules.unit ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).over A) ⟶ H.over A)
    (hcofan : IsColimit (Cofan.mk (H.over A) ι)) {V : X.C} (m : V ⟶ A) :
    Nonempty (Module.Basis (Fin r) ((Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V))
      (H.val.obj (op V))) := by
  obtain ⟨θ, -⟩ := Stacks.SheafOfModules.exists_finsuppEquiv_of_isColimit_cofan ι hcofan
  exact ⟨(Finsupp.basisSingleOne (ι := Fin r)
    (R := (Stacks.SheafOfModules.Tensor.ringSheaf X.O).obj.obj (op V))).map
      (θ (op (Over.mk m))).symm⟩

end AlgebraicGeometry.RingedSite

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)

/-- **The forward direction of the rank form of Descent, Proposition 03DX (2).**  If an
`𝒪_F`-module `H` is finite locally free of rank `r` in the sense of the rank clause of
Stacks 0409, then the affine étale charts over which the sections of `H` form a finite locally
free module of rank `r` generate a covering sieve of every étale chart.

This is the implication `⇒` of the rank form of Descent, Proposition 03DX (2); the converse is
`AlgebraicGeometry.Space.isFiniteLocallyFreeOfRank_of_freeRankPresieve`.

The covering is produced pointwise.  A point of the chart lifts into a member `A` of the
covering trivialising `H`, and an affine open around the lift is again an étale chart lying
over `A`; the sections of `H` over it are free of rank `r` by
`AlgebraicGeometry.RingedSite.nonempty_basis_sections_of_isColimitCofanUnit`. -/
theorem freeRankPresieve_mem_topology_of_isFiniteLocallyFreeOfRank
    (H : Modules.{u, u} B S hS F hF) (r : ℕ)
    (h : RingedSite.IsFiniteLocallyFreeOfRank (smallEtaleRingedSite B S hS F hF) H r)
    (U : SmallEtale B S hS F) :
    Sieve.generate (fun (V : SmallEtale B S hS F) (_ : V ⟶ U) =>
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj V) ∧
        Module.IsFiniteLocallyFreeOfRank (chartRing B S hS F hF V)
          (H.val.obj (op V)) r) ∈ SmallEtale.topology B S hS F U := by
  refine smallEtale_sieve_of_pointwise_covering B S hS F U _ fun z => ?_
  obtain ⟨I, A, a, hcov, hfree⟩ := h U
  have hcov' : Sieve.ofArrows A a ∈ SmallEtale.topology B S hS F U := hcov
  obtain ⟨V₁, g₁, hg₁, z₁, hz₁⟩ := exists_mem_sieve_scheme_point B S hS F U hcov' z
  obtain ⟨Z, t, ff, ⟨i⟩, hfac⟩ := hg₁
  obtain ⟨T₀, j, hT₀aff, w₀, hw₀⟩ := exists_affine_chart_at B S hS F V₁ z₁
  obtain ⟨κ, ⟨hcofan⟩⟩ := hfree i
  refine ⟨T₀, j ≫ g₁, ⟨T₀, 𝟙 _, j ≫ g₁, ⟨hT₀aff, ?_⟩, Category.id_comp _⟩, w₀, ?_⟩
  · exact Module.isFiniteLocallyFreeOfRank_of_basis
      (RingedSite.nonempty_basis_sections_of_isColimitCofanUnit
        (smallEtaleRingedSite B S hS F hF) H r (A i) κ hcofan (j ≫ t)).some
  · rw [Functor.map_comp, Functor.map_comp]
    exact (congrArg _ hw₀).trans hz₁

end AlgebraicGeometry.Space

end
