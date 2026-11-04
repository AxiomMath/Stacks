module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.InvertibleSummandNoSliceSheafify
public import StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Stacks.FibreEssentialSmallness
public import StacksFrontier.AlgebraicGeometry.Stacks.SubcategoryModuleLowerShriek
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeRetract

/-!
# Invertible modules on a locally Noetherian algebraic stack are coherent (Stacks 0GR7)

Let `𝒳` be a locally Noetherian algebraic stack and let `M` be an invertible `𝒪_𝒳`-module
(`Stacks.SheafOfModules.IsInvertible`, Stacks 01CS): tensoring by `M` is an equivalence of the
category of `𝒪_𝒳`-modules on the big fppf site of `𝒳`.  Then `M` is coherent.

Coherence is read, as in `StacksFrontier.AlgebraicGeometry.Stacks.CoherentLocallyNoetherian`, as
Stacks 0GR5(2): finite presentation on the fppf site of `𝒳` in the sense of Stacks 03DL(7).

## Main results

* `SheafOfModules.hasFiniteGlobalPresentation_of_isSplitMono_cofan` and
  `SheafOfModules.hasFiniteGlobalPresentation_of_isSplitMono_pi`: a split direct summand of a
  finite free sheaf of modules has a finite global presentation, the second for a finite product
  of copies of the structure sheaf.
* `SheafOfModules.isFinitePresentationOnSite_of_cover_isSplitMono_pi`: a sheaf of modules which
  on a covering of every object is a split direct summand of a finite product of copies of the
  structure sheaf is of finite presentation on the site.
* `Stacks.SheafOfModules.isFinitePresentationOnSite_of_isInvertible`: an invertible sheaf of
  modules on a site with sheafification is of finite presentation on that site.
* `AlgebraicGeometry.Stack.isCoherentModule_of_isInvertible`: on a locally Noetherian algebraic
  stack every invertible module is coherent.

## Implementation notes

Finite presentation on the site is the predicate of
`StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite`, not Mathlib's
`SheafOfModules.IsFinitePresentation`: there is no implication from the latter back to the
former, so the presentation is built directly.

The fppf site of an algebraic stack has its objects one universe above its schemes; the
sheafification instances it needs at the universe of the structure sheaf come from its essential
smallness, `AlgebraicGeometry.Stack.essentiallySmall_obj_algebraicStack`.

## References

* [Stacks Project, Tag 0GR7](https://stacks.math.columbia.edu/tag/0GR7)
* [Stacks Project, Tag 0GR5](https://stacks.math.columbia.edu/tag/0GR5)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 01CS](https://stacks.math.columbia.edu/tag/01CS)
* [Stacks Project, Tag 0B8M](https://stacks.math.columbia.edu/tag/0B8M)
* [Stacks Project, Tag 0B8N](https://stacks.math.columbia.edu/tag/0B8N)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w t

namespace SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **A split direct summand of a finite free sheaf of modules has a finite global
presentation**, with as many relations as generators. -/
theorem hasFiniteGlobalPresentation_of_isSplitMono_cofan {n : ℕ} {M N : SheafOfModules.{w} R}
    (ι : ∀ _ : Fin n, SheafOfModules.unit R ⟶ N) (hN : IsColimit (Cofan.mk N ι))
    (s : M ⟶ N) (r : N ⟶ M) (hsr : s ≫ r = 𝟙 M) :
    M.HasFiniteGlobalPresentation := by
  let L : SheafOfModules.{w} R ⥤ SheafOfModules.{max u v w} R :=
    SheafOfModules.uliftForPresentationFunctor.{u, v, w, w, max u v w} (R := R)
  have hpb : PreservesBiproduct (fun _ : Fin n => SheafOfModules.unit R) L :=
    preservesBiproduct_of_preservesProduct L
  have hpc : PreservesColimit
      (Discrete.functor (fun _ : Fin n => SheafOfModules.unit R)) L :=
    preservesCoproduct_of_preservesBiproduct L
  have hcol : IsColimit (Cofan.mk (L.obj N) (fun i => L.map (ι i))) :=
    Cofan.isColimitMapCoconeEquiv _ _ (Cofan.mk N ι) (isColimitOfPreserves _ hN)
  have h : Retract (L.obj M) (L.obj N) :=
    ⟨L.map s, L.map r, by rw [← L.map_comp, hsr, L.map_id]⟩
  have hzero : (𝟙 (L.obj N) - h.r ≫ h.i) ≫ h.r = 0 := by simp [h.retract]
  exact ⟨n, n, L.obj N, L.obj N, fun i => L.map (ι i), fun i => L.map (ι i), ⟨hcol⟩, ⟨hcol⟩,
    𝟙 (L.obj N) - h.r ≫ h.i, h.r, hzero, ⟨h.isColimitCokernelCofork⟩⟩

/-- **A split subobject of a finite product of copies of the structure sheaf has a finite global
presentation.** -/
theorem hasFiniteGlobalPresentation_of_isSplitMono_pi
    [HasFiniteProducts (SheafOfModules.{w} R)] {M : SheafOfModules.{w} R} {n : ℕ}
    (s : M ⟶ ∏ᶜ (fun _ : Fin n => SheafOfModules.unit R)) (hs : IsSplitMono s) :
    M.HasFiniteGlobalPresentation := by
  have hbp : HasFiniteBiproducts (SheafOfModules.{w} R) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  let e : (∏ᶜ fun _ : Fin n => SheafOfModules.unit R) ≅
      (∐ fun _ : Fin n => SheafOfModules.unit R) :=
    (biproduct.isoProduct _).symm ≪≫ biproduct.isoCoproduct _
  refine hasFiniteGlobalPresentation_of_isSplitMono_cofan
    (Sigma.ι (fun _ : Fin n => SheafOfModules.unit R))
    (coproductIsCoproduct (fun _ : Fin n => SheafOfModules.unit R))
    (s ≫ e.hom) (e.inv ≫ retraction s) ?_
  rw [Category.assoc, ← Category.assoc e.hom, e.hom_inv_id, Category.id_comp]
  exact IsSplitMono.id s

/-- **A sheaf of modules which on a covering of every object is a split direct summand of a
finite product of copies of the structure sheaf is of finite presentation on the site**, in the
sense of Stacks 03DL(7). -/
theorem isFinitePresentationOnSite_of_cover_isSplitMono_pi
    [∀ V : C, HasFiniteProducts (SheafOfModules.{w} (R.over V))] (M : SheafOfModules.{w} R)
    (h : ∀ U : C, ∃ (I : Type (max u v)) (V : I → C) (f : ∀ i, V i ⟶ U),
      Sieve.ofArrows V f ∈ J U ∧
        ∀ i : I, ∃ n : ℕ,
          ∃ s : M.over (V i) ⟶ ∏ᶜ (fun _ : Fin n => SheafOfModules.unit (R.over (V i))),
            IsSplitMono s) :
    M.IsFinitePresentationOnSite where
  locally_hasFiniteGlobalPresentation U := by
    obtain ⟨I, V, f, hcov, hsplit⟩ := h U
    refine ⟨I, V, f, hcov, fun i => ?_⟩
    obtain ⟨n, s, hs⟩ := hsplit i
    exact hasFiniteGlobalPresentation_of_isSplitMono_pi s hs

end SheafOfModules

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- **An invertible sheaf of modules on a site with sheafification is of finite presentation on
that site**, in the sense of Stacks 03DL(7). -/
theorem isFinitePresentationOnSite_of_isInvertible
    (hO : Presheaf.IsSheaf J (TensorSheafification.structureRingPresheaf O))
    (L : _root_.SheafOfModules.{w} (TensorSheafification.structureSheaf O hO))
    (hL : IsInvertible O hO L) :
    L.IsFinitePresentationOnSite := by
  have := hL
  exact _root_.SheafOfModules.isFinitePresentationOnSite_of_cover_isSplitMono_pi L fun U =>
    exists_cover_isDirectSummand_finiteFree hO L U

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- On a locally Noetherian algebraic stack every invertible `𝒪_𝒳`-module is coherent. -/
@[stacks 0GR7 "invertible modules on the stack are coherent"]
theorem isCoherentModule_of_isInvertible (𝒳 : AlgebraicStacks.{u, t} B S hS)
    (_h𝒳 : HasPropertyOnSomeSchemeAtlas B S hS
      (fun T : Scheme.{u} ↦ IsLocallyNoetherian T) 𝒳)
    (M : SheafOfModules.{u} (ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids B.topology le_rfl))
    (hM : Stacks.SheafOfModules.IsInvertible
      (structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl).obj
      (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
        B.topology le_rfl).property M) :
    IsCoherentModule B S hS 𝒳 M :=
  Stacks.SheafOfModules.isFinitePresentationOnSite_of_isInvertible
    (O := (structureSheaf B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids B.topology le_rfl).obj)
    (ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids
      B.topology le_rfl).property M hM

end AlgebraicGeometry.Stack

end
