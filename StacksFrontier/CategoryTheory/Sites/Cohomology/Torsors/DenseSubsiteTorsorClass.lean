module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChangeOfTopology.DenseSubsiteCohomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Torsors.FirstCohomology
public import StacksFrontier.Cotangent.Spaces.ConstantBaseRingPresheaf

/-!
# Torsor classes under restriction to a dense subsite

Let `G : (C, J) ⥤ (D, K)` exhibit `(C, J)` as a dense subsite of `(D, K)` and let `H` be an
abelian sheaf on `D`. A torsor `P` under `H` restricts along `G` to a torsor under the
restriction of `H`. The isomorphism `H¹(D, H) ≅ H¹(C, H|_C)` of
`Stacks.Cohomology.DenseSubsite.hAddEquiv` carries the class of `P` (Tag 03AJ) to the class of
its restriction.

## Main definitions

* `Stacks.Cohomology.Torsors.AbelianTorsor.restrict`: the restriction of a torsor along a dense
  subsite.

## Main results

* `Stacks.Cohomology.DenseSubsite.hAddEquiv_torsorIsoClassesEquivH1`: the cohomology comparison
  of a dense subsite sends the class of a torsor to the class of its restriction.

## Implementation notes

The class of a torsor is the extension class of its pushout extension, whose quotient is the
constant sheaf; the comparison applies the exact restriction functor to that extension
(`Ext.mapExactFunctor_extClass`), and the restricted extension exhibits the restricted torsor
as the fibre over the restricted unit section, which is what
`Stacks.Cohomology.Torsors.torsorIsoClassesEquivH1_eq_boundary_iff` recognises. The one
computation is that the identification of the restricted constant sheaf with the constant sheaf
respects the sheafification maps, which is
`Functor.IsDenseSubsite.toSheafify_comp_sheafEquivSheafificationCompatibility_hom_app`.

## References

* [Stacks Project, Tag 03AJ](https://stacks.math.columbia.edu/tag/03AJ)
* [Stacks Project, Tag 00XU](https://stacks.math.columbia.edu/tag/00XU)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

universe a t u₁ v₁ u₂ v₂

namespace Stacks.Cohomology.Torsors

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K]

/-- **The restriction of a torsor to a dense subsite.** A torsor `P` under an abelian sheaf `H`
on `D` restricts along `G` to a torsor under the restriction of `H`: its sections over `U` are
the sections of `P` over `G U`. -/
def AbelianTorsor.restrict {H : Sheaf K AddCommGrpCat.{t}} (P : AbelianTorsor H) :
    AbelianTorsor ((G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).obj H) :=
  ⟨{ presheaf := G.op ⋙ P.1.presheaf
     isSheaf := G.op_comp_isSheaf_of_isSheaf J K P.1.presheaf P.1.isSheaf
     act := fun U g s => P.1.act (G.op.obj U) g s
     one_act := fun U s => P.1.one_act (G.op.obj U) s
     mul_act := fun U g h s => P.1.mul_act (G.op.obj U) g h s
     naturality := fun f g s => P.1.naturality (G.op.map f) g s
     simplyTransitive := fun U h s t => P.1.simplyTransitive (G.op.obj U) h s t },
    fun U => by
      obtain ⟨S, hS, hne⟩ := P.2 (G.obj U)
      exact ⟨S.functorPullback G, G.cover_lift J K hS, fun V f hf => hne hf⟩⟩

end Stacks.Cohomology.Torsors

namespace Stacks.Cohomology.DenseSubsite

open Stacks.Cohomology.Torsors

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D) (G : C ⥤ D)
  [G.IsDenseSubsite J K]
  [HasWeakSheafify J AddCommGrpCat.{t}] [HasWeakSheafify K AddCommGrpCat.{t}]
  [(G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).IsEquivalence]
  [HasSheafify J AddCommGrpCat.{t}] [HasSheafify K AddCommGrpCat.{t}]
  [HasExt.{a} (Sheaf J AddCommGrpCat.{t})] [HasExt.{a} (Sheaf K AddCommGrpCat.{t})]
  [EnoughInjectives (Sheaf J AddCommGrpCat.{t})]

omit [HasSheafify J AddCommGrpCat.{t}] [HasExt.{a} (Sheaf J AddCommGrpCat.{t})]
  [HasExt.{a} (Sheaf K AddCommGrpCat.{t})] [EnoughInjectives (Sheaf J AddCommGrpCat.{t})] in
/-- The identification of the restricted constant sheaf with the constant sheaf respects the unit
sections: as a map out of a sheafification it is adjoint to the restriction of the sheafification
map of the constant presheaf on `D`. -/
theorem constantSheafRestrictionIso_inv_app_eq :
    (constantSheafRestrictionIso J K G).inv.app (AddCommGrpCat.of (ULift.{t} ℤ)) =
      ((sheafificationAdjunction J AddCommGrpCat.{t}).homEquiv _ _).symm
        (Functor.whiskerLeft G.op (constantUnit (J := K))) := by
  have hc : constantUnit (J := K) =
      toSheafify K ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ))) := by
    rw [constantUnit, Adjunction.homEquiv_unit, sheafificationAdjunction_unit_app]
    simp
  refine (Equiv.eq_symm_apply _).mpr ((Adjunction.homEquiv_unit _ _ _ _).trans ?_)
  rw [sheafificationAdjunction_unit_app, hc]
  exact Functor.IsDenseSubsite.toSheafify_comp_sheafEquivSheafificationCompatibility_hom_app
    J K G AddCommGrpCat.{t} ((Functor.const Dᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)))

/-- **The cohomology comparison of a dense subsite respects torsor classes.** The isomorphism
`H¹(D, H) ≅ H¹(C, H|_C)` carries the class of a torsor `P` under `H` (Tag 03AJ) to the class of
the restriction of `P`. -/
theorem hAddEquiv_torsorIsoClassesEquivH1 (H : Sheaf K AddCommGrpCat.{t}) (P : AbelianTorsor H) :
    hAddEquiv J K G H 1 (torsorIsoClassesEquivH1 H (Quotient.mk (torsorSetoid H) P)) =
      torsorIsoClassesEquivH1 ((G.sheafPushforwardContinuous AddCommGrpCat.{t} J K).obj H)
        (Quotient.mk (torsorSetoid _) (P.restrict J K G)) := by
  let L := G.sheafPushforwardContinuous AddCommGrpCat.{t} J K
  let S := torsorPushoutComplex H P
  have hS : S.ShortExact := torsorPushoutComplex_shortExact H P
  obtain ⟨i0, e0, inj0, fib0⟩ :=
    (torsorIsoClassesEquivH1_eq_boundary_iff S hS (constantUnit (J := K)) P).mp (by
      rw [constantUnit_adj_inverse, Abelian.Ext.mk₀_id_comp]
      rfl)
  let q' : (Functor.const Cᵒᵖ).obj (AddCommGrpCat.of (ULift.{t} ℤ)) ⟶ (S.map L).X₃.obj :=
    Functor.whiskerLeft G.op (constantUnit (J := K))
  have hR := (torsorIsoClassesEquivH1_eq_boundary_iff (S.map L) (hS.map_of_exact L) q'
    (P.restrict J K G)).mpr
      ⟨Functor.whiskerLeft G.op i0, fun U h s => e0 _ h s, fun U => inj0 _, fun U x => fib0 _ x⟩
  refine Eq.trans ?_ hR.symm
  refine (Stacks.ExtAdjunction.hComparison_apply (constantSheafRestrictionIso J K G) 1 H
    hS.extClass).trans ?_
  refine (congrArg (fun e => (Abelian.Ext.mk₀ ((constantSheafRestrictionIso J K G).app
    (AddCommGrpCat.of (ULift.{t} ℤ))).inv).comp e (zero_add 1))
      (Abelian.Ext.mapExactFunctor_extClass L hS)).trans ?_
  congr 2
  exact constantSheafRestrictionIso_inv_app_eq J K G

end Stacks.Cohomology.DenseSubsite

end
