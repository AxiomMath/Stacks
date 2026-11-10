module

public import StacksFrontier.Topology.Sheaves.Modules.ModuleGlueing.MatrixCocycleOfOverlap

/-!
# The charts of the module glued from a family of comparisons of free charts

`Stacks.SheafOfModules.matrixCocycleOfOverlap` reads a family of comparisons `φ k l` of free charts
over the overlaps as a matrix cocycle, and `Stacks.SheafOfModules.MatrixCocycle.glued` glues it.
This file records the chart isomorphisms of the glued module **as isomorphisms of sheaves of
modules on the slice sites**, and shows that they are related by the given comparisons. Having the
charts, rather than the bare existence of a glued module, is what makes morphisms out of and into
the glued module accessible afterwards.

## Main definitions

* `Stacks.SheafOfModules.MatrixCocycle.overChartIso`: **the chart isomorphism of the glued module
  over a member of the family**, `D.glued.over (V k) ≅ (chart k).over (V k)`, assembled from the
  sectionwise chart isomorphisms `Stacks.SheafOfModules.MatrixCocycle.chartIso`.

## Main results

* `Stacks.SheafOfModules.transEquiv_matrixCocycleOfOverlap`: the transition maps of the matrix
  cocycle of a family of comparisons are the components of the comparisons.
* `Stacks.SheafOfModules.exists_glued_iso_over_of_overlap`: **a family of comparisons of free
  charts over the overlaps, satisfying the identity and cocycle laws, glues to a finite locally
  free module together with chart isomorphisms related on components by the comparisons.**
* `Stacks.SheafOfModules.exists_glued_iso_over_of_overlap_of_eq`: the same, with the overlaps
  given as opens only propositionally equal to the intersections.

## References

* [Stacks Project, Tag 00AM](https://stacks.math.columbia.edu/tag/00AM)
* [Stacks Project, Tag 01C6](https://stacks.math.columbia.edu/tag/01C6)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace Stacks.SheafOfModules

namespace MatrixCocycle

variable {X : TopCat.{u}}
  {O : Sheaf (Opens.grothendieckTopology ((X : TopCat) : Type u)) RingCat.{u}}
  {K : Type u} {V : K → Opens X} {m : K → ℕ} (D : MatrixCocycle O V m)

/-- **The chart isomorphism of the glued module over a member of the family**, as an
isomorphism of sheaves of modules on the slice site `Opens(X)/V k`. Its component at an object
`W ⟶ V k` is the sectionwise chart isomorphism over `W`; naturality is
`Stacks.SheafOfModules.MatrixCocycle.chartIso_hom_res`. -/
noncomputable def overChartIso (k : K) :
    D.glued.over (V k) ≅ (chart (O := O) (m := m) k).over (V k) :=
  (_root_.SheafOfModules.fullyFaithfulForget _).preimageIso
    (PresheafOfModules.isoMk (fun W => D.chartIso k (leOfHom W.unop.hom)) (by
      intro W W' f
      ext s
      have h := D.chartIso_hom_res k (leOfHom W.unop.hom) (leOfHom f.unop.left) s
      have hf : f.unop.left = homOfLE (leOfHom f.unop.left) := Subsingleton.elim _ _
      change (D.chartIso k (leOfHom W'.unop.hom)).hom (res D.glued f.unop.left s)
        = res (chart (O := O) (m := m) k) f.unop.left
            ((D.chartIso k (leOfHom W.unop.hom)).hom s)
      rw [hf]
      exact h))

/-- The component at an object `W ⟶ V k` of the chart isomorphism `overChartIso k` is the
sectionwise chart isomorphism `chartIso k` over `W`. -/
@[simp]
lemma overChartIso_hom_val_app (k : K) (W : (Over (V k))ᵒᵖ) :
    (D.overChartIso k).hom.val.app W = (D.chartIso k (leOfHom W.unop.hom)).hom :=
  rfl

/-- The component at an object `W ⟶ V k` of the inverse of the chart isomorphism
`overChartIso k` is the inverse of the sectionwise chart isomorphism `chartIso k` over `W`. -/
@[simp]
lemma overChartIso_inv_val_app (k : K) (W : (Over (V k))ᵒᵖ) :
    (D.overChartIso k).inv.val.app W = (D.chartIso k (leOfHom W.unop.hom)).inv :=
  rfl

end MatrixCocycle

section Transition

variable {X : TopCat.{u}}
  {O : Sheaf (Opens.grothendieckTopology ((X : TopCat) : Type u)) RingCat.{u}}
  {K : Type u} (V : K → Opens X) (m : K → ℕ)
  (φ : ∀ k l : K, (MatrixCocycle.chart (O := O) (m := m) k).over (V k ⊓ V l) ⟶
    (MatrixCocycle.chart (O := O) (m := m) l).over (V k ⊓ V l))

/-- **The transition maps of the matrix cocycle of a family of comparisons are the components of
the comparisons**: both are multiplication by the matrix of the component, read in
coordinates. -/
theorem transEquiv_matrixCocycleOfOverlap
    (hid : ∀ k : K, φ k k = 𝟙 _)
    (hcomp : ∀ (k l j : K) ⦃W : Opens X⦄ (hk : W ≤ V k) (hl : W ≤ V l) (hj : W ≤ V j)
      (x : ToType ((MatrixCocycle.chart (O := O) (m := m) k).val.obj (op W))),
      overlapApp V m φ l j hl hj (overlapApp V m φ k l hk hl x)
        = overlapApp V m φ k j hk hj x)
    (k l : K) ⦃W : Opens X⦄ (hk : W ≤ V k) (hl : W ≤ V l)
    (e : ToType ((MatrixCocycle.chart (O := O) (m := m) k).val.obj (op W))) :
    (matrixCocycleOfOverlap V m φ hid hcomp).transEquiv k l hk hl e
      = overlapApp V m φ k l hk hl e := by
  refine (freeCoordEquiv (op W)).injective (funext fun b => ?_)
  rw [MatrixCocycle.freeCoordEquiv_transEquiv]
  conv_rhs => rw [← freeMk_freeCoord (S := O) (op W) e]
  change rowMul _ (freeCoord (op W) e) b
    = freeCoord (op W) (overlapApp V m φ k l hk hl (freeMk (op W) (freeCoord (op W) e))) b
  rw [freeCoord_overlapApp_freeMk]
  rfl

end Transition

/-- **A family of comparisons of free charts over the overlaps, satisfying the identity and
cocycle laws, glues to a finite locally free module together with chart isomorphisms related by
the comparisons.** The chart isomorphisms `ν k : N.over (V k) ≅ (chart k).over (V k)` are
recorded, and on the sections over every open `W` below two members `V k` and `V l` the `l`-th one
is the `k`-th one followed by the component of `φ k l`. The sheaf of rings is arbitrary.

This strengthens the existence statement of a glued module: the module is
`Stacks.SheafOfModules.MatrixCocycle.glued` of `Stacks.SheafOfModules.matrixCocycleOfOverlap`, and
the charts are `Stacks.SheafOfModules.MatrixCocycle.overChartIso`. -/
theorem exists_glued_iso_over_of_overlap {X : TopCat.{u}}
    {O : Sheaf (Opens.grothendieckTopology ((X : TopCat) : Type u)) RingCat.{u}}
    {K : Type u} (V : K → Opens X) (hV : ⨆ k, V k = ⊤) (m : K → ℕ)
    (φ : ∀ k l : K, (MatrixCocycle.chart (O := O) (m := m) k).over (V k ⊓ V l) ⟶
      (MatrixCocycle.chart (O := O) (m := m) l).over (V k ⊓ V l))
    (hid : ∀ k : K, φ k k = 𝟙 _)
    (hcomp : ∀ (k l j : K) ⦃W : Opens X⦄ (hk : W ≤ V k) (hl : W ≤ V l) (hj : W ≤ V j)
      (x : ToType ((MatrixCocycle.chart (O := O) (m := m) k).val.obj (op W))),
      overlapApp V m φ l j hl hj (overlapApp V m φ k l hk hl x)
        = overlapApp V m φ k j hk hj x) :
    ∃ (N : _root_.SheafOfModules.{u} O)
      (ν : ∀ k, N.over (V k) ≅ (MatrixCocycle.chart (O := O) (m := m) k).over (V k)),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N ∧
      ∀ (k l : K) ⦃W : Opens X⦄ (hk : W ≤ V k) (hl : W ≤ V l),
        (ν l).hom.val.app (op (Over.mk (homOfLE hl))) =
          (ν k).hom.val.app (op (Over.mk (homOfLE hk))) ≫
            (φ k l).val.app (op (Over.mk (homOfLE (le_inf hk hl)))) := by
  set D := matrixCocycleOfOverlap V m φ hid hcomp
  refine ⟨D.glued, D.overChartIso, D.isFiniteLocallyFree_glued hV, fun k l W hk hl => ?_⟩
  ext s
  exact (D.trans_chartIso_hom k l hk hl s).symm.trans
    (transEquiv_matrixCocycleOfOverlap V m φ hid hcomp k l hk hl _)

/-- **The glueing with recorded charts, over arbitrary opens equal to the overlaps.** The same as
`Stacks.SheafOfModules.exists_glued_iso_over_of_overlap`, with the overlap of `V k` and `V l`
given as an open `U k l` that is only *propositionally* `V k ⊓ V l`, so that a consumer whose
overlaps are not syntactically intersections need not transport slice morphisms along an equality
of opens. The identity and cocycle laws are stated on components. -/
theorem exists_glued_iso_over_of_overlap_of_eq {X : TopCat.{u}}
    {O : Sheaf (Opens.grothendieckTopology ((X : TopCat) : Type u)) RingCat.{u}}
    {K : Type u} (V : K → Opens X) (hV : ⨆ k, V k = ⊤) (m : K → ℕ) (U : K → K → Opens X)
    (hU : ∀ k l, U k l = V k ⊓ V l)
    (ψ : ∀ k l : K, (MatrixCocycle.chart (O := O) (m := m) k).over (U k l) ⟶
      (MatrixCocycle.chart (O := O) (m := m) l).over (U k l))
    (hid : ∀ (k : K) ⦃W : Opens X⦄ (hk : W ≤ U k k)
      (x : ToType ((MatrixCocycle.chart (O := O) (m := m) k).val.obj (op W))),
      (ψ k k).val.app (op (Over.mk (homOfLE hk))) x = x)
    (hcomp : ∀ (k l j : K) ⦃W : Opens X⦄ (hkl : W ≤ U k l) (hlj : W ≤ U l j)
      (hkj : W ≤ U k j)
      (x : ToType ((MatrixCocycle.chart (O := O) (m := m) k).val.obj (op W))),
      (ψ l j).val.app (op (Over.mk (homOfLE hlj)))
          ((ψ k l).val.app (op (Over.mk (homOfLE hkl))) x)
        = (ψ k j).val.app (op (Over.mk (homOfLE hkj))) x) :
    ∃ (N : _root_.SheafOfModules.{u} O)
      (ν : ∀ k, N.over (V k) ≅ (MatrixCocycle.chart (O := O) (m := m) k).over (V k)),
      AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFree.{u, u, u} N ∧
      ∀ (k l : K) ⦃W : Opens X⦄ (hk : W ≤ V k) (hl : W ≤ V l) (hkl : W ≤ U k l),
        (ν l).hom.val.app (op (Over.mk (homOfLE hl))) =
          (ν k).hom.val.app (op (Over.mk (homOfLE hk))) ≫
            (ψ k l).val.app (op (Over.mk (homOfLE hkl))) := by
  obtain rfl : U = fun k l => V k ⊓ V l := funext fun k => funext fun l => hU k l
  have hid' : ∀ k : K, ψ k k = 𝟙 _ := fun k =>
    _root_.SheafOfModules.hom_ext (PresheafOfModules.hom_ext fun W => by
      ext x
      exact hid k (leOfHom W.unop.hom) x)
  obtain ⟨N, ν, hN, hν⟩ := exists_glued_iso_over_of_overlap V hV m ψ hid'
    (fun k l j W hk hl hj x => hcomp k l j (le_inf hk hl) (le_inf hl hj) (le_inf hk hj) x)
  exact ⟨N, ν, hN, fun k l W hk hl _ => hν k l hk hl⟩

end Stacks.SheafOfModules

end
