module

public import StacksFrontier.CategoryTheory.Sites.Simplicial.Cartesian
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalAugmentationComponents
public import StacksFrontier.CategoryTheory.Sites.Simplicial.TotalSiteCharts

/-!
# Cartesian sheaves in case (B) through the cross arrows

Let `C` be a simplicial family of sites with transitions `u_φ` which are continuous and
cocontinuous. The total category is the covariant Grothendieck construction, and a simplex map
`φ : [m] ⟶ [n]` and an object `V` of degree `n` give the cross arrow `(n, V) ⟶ (m, u_φ V)`. The
transition `f_φ⁻¹F_m ⟶ F_n` of Stacks 09WF of a sheaf of sets `F` on the total site is
invertible exactly when restriction of `F` along every cross arrow of `φ` is a bijection.

All names are in the namespace `CategoryTheory.CocontinuousSimplicialSite`.

## Main results

* `isIso_fiberTransition_app_iff_bijective_cartesianCrossCriterion`: the transition
  `f_φ⁻¹F_m ⟶ F_n` of a sheaf of sets `F` on the total site is invertible exactly when `F`
  inverts every cross arrow of `φ`.
* `isCartesianSheaf_iff_bijective_cartesianCrossCriterion`: a sheaf of sets on the total site is
  cartesian (Stacks 07TF) exactly when it inverts every cross arrow.

## References

* [Stacks Project, Tag 07TF](https://stacks.math.columbia.edu/tag/07TF)
* [Stacks Project, Tag 09WF](https://stacks.math.columbia.edu/tag/09WF)
-/

@[expose] public section

open CategoryTheory Opposite

universe u

namespace CategoryTheory.CocontinuousSimplicialSite

variable (C : CocontinuousSimplicialSite.{u})
  (hc : ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n), (C.underlying.map φ.op).toFunctor.IsContinuous
    ((situation C).componentTopology n) ((situation C).componentTopology m))

include hc

/-- **Stacks 09WF in case (B), on sections.** The transition `f_φ⁻¹F_m ⟶ F_n` of a sheaf of sets
on the total site is invertible exactly when restriction along every cross arrow of `φ` is a
bijection on sections. -/
theorem isIso_fiberTransition_app_iff_bijective_cartesianCrossCriterion
    {m n : SimplexCategory} (φ : m ⟶ n) (G : Sheaf (situation C).totalTopology (Type u)) :
    IsIso (((situation C).fiberTransition φ).app G) ↔
      ∀ U : C.underlying.obj (op n), Function.Bijective
        (G.obj.map ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app U).op) := by
  let u := (C.underlying.map φ.op).toFunctor
  have : u.IsCocontinuous ((situation C).componentTopology n)
      ((situation C).componentTopology m) := C.isCocontinuous φ.op
  have : u.IsContinuous ((situation C).componentTopology n)
      ((situation C).componentTopology m) := hc φ
  let adj₂ := u.sheafAdjunctionCocontinuous (Type u) ((situation C).componentTopology n)
    ((situation C).componentTopology m)
  let A := ((situation C).restrictTransition φ).app G
  have hfT : ((situation C).fiberTransition φ).app G =
      (((situation C).transitionMorphism φ).adj.homEquiv _ _).symm A :=
    (Equiv.eq_symm_apply _).2 (SimplicialSiteSituation.fiberTransition_adj _ φ G)
  have h₂ : ((adj₂.homEquiv _ _).symm A).hom =
      ((u.op.ranAdjunction (Type u)).homEquiv _ _).symm A.hom := by
    have h := u.sheafAdjunctionCocontinuous_homEquiv_apply_hom (Type u)
      ((situation C).componentTopology n) ((situation C).componentTopology m)
      ((adj₂.homEquiv _ _).symm A)
    have e₁ : adj₂.homEquiv _ _ ((adj₂.homEquiv _ _).symm A) = A := Equiv.apply_symm_apply _ _
    exact (Equiv.eq_symm_apply _).2 (h.symm.trans (congrArg (fun t => t.hom) e₁))
  rw [hfT, Adjunction.isIso_homEquiv_symm_iff ((situation C).transitionMorphism φ).adj adj₂ A]
  refine ((ObjectProperty.isIso_hom_iff _).symm.trans
    (Iff.of_eq (congrArg (fun f => IsIso f) h₂))).trans ((NatTrans.isIso_iff_isIso_app _).trans ?_)
  have key := fun U : C.underlying.obj (op n) =>
    (congrArg IsIso (SimplicialSiteSituation.restrictTransition_inr_app C φ G U)).to_iff.trans
      (isIso_iff_bijective _)
  exact ⟨fun h U => (key U).1 (h (op U)), fun h U => (key U.unop).2 (h U.unop)⟩

/-- **Stacks 07TF in case (B), on sections.** A sheaf of sets on the total site is cartesian
exactly when restriction along every cross arrow is a bijection on sections. -/
theorem isCartesianSheaf_iff_bijective_cartesianCrossCriterion
    (G : Sheaf (situation C).totalTopology (Type u)) :
    (situation C).IsCartesianSheaf G ↔
      ∀ ⦃m n : SimplexCategory⦄ (φ : m ⟶ n) (U : C.underlying.obj (op n)), Function.Bijective
        (G.obj.map ((Grothendieck.ιNatTrans (F := C.underlying) φ.op).app U).op) :=
  forall_congr' fun _ => forall_congr' fun _ => forall_congr' fun φ =>
    isIso_fiberTransition_app_iff_bijective_cartesianCrossCriterion C hc φ G

end CategoryTheory.CocontinuousSimplicialSite
