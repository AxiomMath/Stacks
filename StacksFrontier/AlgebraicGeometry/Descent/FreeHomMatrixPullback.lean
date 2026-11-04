module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeHomMatrix
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitFree

/-!
# Extension of scalars acts on the matrix of a morphism of free sheaves of modules entrywise

Let `φ : S ⟶ F_*R` be a morphism of sheaves of rings along a continuous functor `F : C ⥤ D` of
sites, with `F` final, and let `T` be a terminal object of `C` whose image `F T` is terminal in
`D`. A morphism `R^{⊕I} ⟶ R^{⊕L}` of free sheaves of modules with `L` finite is a matrix of
sections over the terminal object (`Stacks.SheafOfModules.freeHomMatrixEquiv`), and extension of
scalars along `φ` carries free sheaves of modules to free sheaves of modules by Mathlib's
`CategoryTheory.SheafOfModules.pullbackObjFreeIso`. This file proves that, conjugated by that
identification, **extension of scalars acts on the matrix entrywise by `φ` on sections over the
terminal object**.

This is the Hom-level compatibility the full faithfulness half of Stacks Tag 0EXD needs: the
transition functors of Stacks Tag 0EXE are extension of scalars along the canonical morphisms of
Frobenius-colimit structure sheaves, so with this lemma the square of Hom-sets of free modules
attached to an almost blowup square is the square of matrices over the four rings of global
sections, entry by entry.

## Main definitions

* `Stacks.SheafOfModules.pullbackFreeHom`: **extension of scalars on a morphism of free sheaves
  of modules**, conjugated by `CategoryTheory.SheafOfModules.pullbackObjFreeIso` so as to be
  again a morphism of free sheaves of modules on the same index types.

## Main results

* `Stacks.SheafOfModules.freeHomMatrixEquiv_pullbackFreeHom`: **the matrix of the extension of
  scalars is the matrix of the original morphism with `φ` applied to each entry.**

## Implementation notes

The proof is by transposition across the pullback–pushforward adjunction, and is arranged so
that no computation with elements of a tensor product occurs: extension of scalars is a left
adjoint, so a morphism out of its value is never computed, only transposed.

The transpose of `(pullbackObjFreeIso φ L).hom` is the morphism
`R^{⊕L} ⟶ (pushforward φ)(R^{⊕L})` whose restriction along the `l`-th tautological inclusion is
`φ` followed by the pushforward of that inclusion; that is Mathlib's
`CategoryTheory.SheafOfModules.ιFree_comp_unit_app_free_comp` in the shape proved in
`StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.UnitFree`, and it is spelled here as the
composite of the unit of the adjunction with the pushforward of the free identification rather
than as a definition of its own, so that that lemma applies on the nose.

Composing that transpose with the pushforward of the `k`-th coordinate projection gives the
`k`-th coordinate projection followed by `φ`
(`Stacks.SheafOfModules.unitFree_comp_pushforward_map_freeProj`): both sides are morphisms out of
a coproduct of copies of the unit sheaf, so it suffices to compare them on each tautological
inclusion, where `CategoryTheory.SheafOfModules.ιFree_comp_freeProj` leaves an identity or a
zero. That identity is the whole content; everything after it is an evaluation at the unit
section over the terminal object.

**Why the final step rewrites the goal rather than the hypothesis.** The two spellings of the
unit section over the terminal object — `unitOne` of `unit R` over `F T` and the image under `φ`
of `unitOne` of `unit S` over `T` — are definitionally equal but, a composite of morphisms of
sheaves of modules being evaluated on sections by `rfl` and not by a simp lemma, a `rw` inside
the hypothesis finds no occurrence of the first. Rewriting the *goal* backwards along
`Stacks.SheafOfModules.unitToPushforwardObjUnit_unitOne` puts it in the shape the evaluated
identity has, and the remaining identifications are then discharged by `exact`, which checks at
default transparency.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open SheafOfModules

universe v₁ v₂ u₁ u₂ u

namespace Stacks.SheafOfModules

variable {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
  {J : GrothendieckTopology C} {K : GrothendieckTopology D} {F : C ⥤ D}
  {S : Sheaf J RingCat.{u}} {R : Sheaf K RingCat.{u}}
  [Functor.IsContinuous F J K]
  (φ : S ⟶ (F.sheafPushforwardContinuous RingCat.{u} J K).obj R)

/-- The comparison `unit S ⟶ (pushforward φ)(unit R)` of unit sheaves takes the unit section over
an object to the unit section over its image, `φ` being a morphism of sheaves of rings. -/
lemma unitToPushforwardObjUnit_unitOne {T : C} :
    (unitToPushforwardObjUnit φ).val.app (op T) (unitOne (S := S) (op T)) =
      unitOne (S := R) (op (F.obj T)) := by
  have hone : φ.hom.app (op T) (unitOne (S := S) (op T)) =
      unitOne (S := R) (op (F.obj T)) := map_one _
  exact (unitToPushforwardObjUnit_val_app_apply φ (unitOne (S := S) (op T))).trans hone

section Pullback

variable [(_root_.SheafOfModules.pushforward.{u} φ).IsRightAdjoint]
  [HasWeakSheafify J AddCommGrpCat.{u}] [HasWeakSheafify K AddCommGrpCat.{u}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [K.WEqualsLocallyBijective AddCommGrpCat.{u}] [F.Final]

/-- **The transpose of the free identification, composed with a coordinate projection.** The
morphism `S^{⊕L} ⟶ (pushforward φ)(R^{⊕L})` transposing
`CategoryTheory.SheafOfModules.pullbackObjFreeIso`, followed by the pushforward of the `k`-th
coordinate projection of `R^{⊕L}`, is the `k`-th coordinate projection of `S^{⊕L}` followed by
`φ`.

Both sides are morphisms out of a coproduct of copies of `unit S`, so they agree as soon as they
agree after each tautological inclusion, where
`CategoryTheory.SheafOfModules.ιFree_comp_freeProj` leaves an identity or a zero. -/
lemma unitFree_comp_pushforward_map_freeProj (L : Type u) [DecidableEq L] (k : L) :
    ((pullbackPushforwardAdjunction.{u} φ).unit.app (free (R := S) L) ≫
          (_root_.SheafOfModules.pushforward.{u} φ).map (pullbackObjFreeIso φ L).hom) ≫
        (_root_.SheafOfModules.pushforward.{u} φ).map (freeProj (S := R) k) =
      freeProj (S := S) k ≫ unitToPushforwardObjUnit φ := by
  refine Cofan.IsColimit.hom_ext (isColimitFreeCofan (R := S) L) _ _ fun l => ?_
  have hc : ∀ N (m : free (R := S) L ⟶ N), (freeCofan (R := S) L).inj l ≫ m = ιFree l ≫ m :=
    fun _ _ => rfl
  rw [hc, hc, ← Category.assoc, ιFree_comp_unit_app_free_comp]
  simp only [Category.assoc, ← Functor.map_comp]
  rw [ιFree_comp_freeProj]
  conv_rhs => rw [← Category.assoc, ιFree_comp_freeProj]
  rcases eq_or_ne l k with rfl | h
  · simp
  · simp [h]

/-- **Extension of scalars on a morphism of free sheaves of modules.** Extension of scalars
along `φ` carries a free sheaf of modules to a free sheaf of modules on the same index type by
`CategoryTheory.SheafOfModules.pullbackObjFreeIso`; conjugating by that identification turns a
morphism `S^{⊕I} ⟶ S^{⊕L}` into a morphism `R^{⊕I} ⟶ R^{⊕L}`. -/
noncomputable def pullbackFreeHom (I L : Type u)
    (f : free (R := S) I ⟶ free (R := S) L) : free (R := R) I ⟶ free (R := R) L :=
  (pullbackObjFreeIso φ I).inv ≫ (_root_.SheafOfModules.pullback.{u} φ).map f ≫
    (pullbackObjFreeIso φ L).hom

/-- The `i`-th tautological inclusion followed by the extension of scalars of `f`, precomposed
with the identification of the extension of scalars of `unit S` with `unit R`, is the extension
of scalars of the `i`-th row of `f` followed by the free identification. This is the form in
which the row of the matrix can be transposed across the adjunction. -/
lemma pullbackObjUnitToUnit_comp_pullbackFreeHom (I L : Type u)
    (f : free (R := S) I ⟶ free (R := S) L) (i : I) :
    pullbackObjUnitToUnit φ ≫ ιFree (R := R) i ≫ pullbackFreeHom φ I L f =
      (_root_.SheafOfModules.pullback.{u} φ).map (ιFree (R := S) i ≫ f) ≫
        (pullbackObjFreeIso φ L).hom := by
  rw [pullbackFreeHom, ← pullback_map_ιFree_comp_pullbackObjFreeIso_hom_assoc]
  simp only [Functor.map_comp, Category.assoc, Iso.hom_inv_id_assoc]

/-- **The transpose of a row of the extension of scalars.** Transposing the previous identity
across the pullback–pushforward adjunction: `φ` followed by the pushforward of the `i`-th row of
the extension of scalars of `f` is the `i`-th row of `f` followed by the transpose of the free
identification. -/
lemma pushforward_map_pullbackFreeHom (I L : Type u)
    (f : free (R := S) I ⟶ free (R := S) L) (i : I) :
    unitToPushforwardObjUnit φ ≫
        (_root_.SheafOfModules.pushforward.{u} φ).map
          (ιFree (R := R) i ≫ pullbackFreeHom φ I L f) =
      (ιFree (R := S) i ≫ f) ≫
        ((pullbackPushforwardAdjunction.{u} φ).unit.app (free (R := S) L) ≫
          (_root_.SheafOfModules.pushforward.{u} φ).map (pullbackObjFreeIso φ L).hom) := by
  have e := congrArg ((pullbackPushforwardAdjunction.{u} φ).homEquiv (unit S) (free (R := R) L))
    (pullbackObjUnitToUnit_comp_pullbackFreeHom φ I L f i)
  rw [Adjunction.homEquiv_naturality_right, Adjunction.homEquiv_naturality_left,
    pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit,
    Adjunction.homEquiv_unit] at e
  exact e

/-- **The transpose of an entry of the extension of scalars.** Composing the previous identity
with the pushforward of the `k`-th coordinate projection and using
`Stacks.SheafOfModules.unitFree_comp_pushforward_map_freeProj`: `φ` followed by the pushforward
of the `(i, k)` entry of the extension of scalars of `f` is the `(i, k)` entry of `f` followed by
`φ`. Evaluating this at the unit section over a terminal object is the matrix statement. -/
lemma pushforward_map_pullbackFreeHom_comp_freeProj (I L : Type u) [DecidableEq L]
    (f : free (R := S) I ⟶ free (R := S) L) (i : I) (k : L) :
    unitToPushforwardObjUnit φ ≫
        (_root_.SheafOfModules.pushforward.{u} φ).map
          ((ιFree (R := R) i ≫ pullbackFreeHom φ I L f) ≫ freeProj (S := R) k) =
      ((ιFree (R := S) i ≫ f) ≫ freeProj (S := S) k) ≫ unitToPushforwardObjUnit φ := by
  rw [Functor.map_comp, ← Category.assoc, pushforward_map_pullbackFreeHom, Category.assoc,
    unitFree_comp_pushforward_map_freeProj]
  simp only [Category.assoc]

/-- **Extension of scalars acts entrywise on the coordinates of a morphism of free sheaves of
modules.** Over an arbitrary object `T` of the source site, the `k`-th coordinate of the image of
the `i`-th tautological section under the extension of scalars of `f`, taken over `F T`, is the
image under `φ` of the `k`-th coordinate of the image of the `i`-th tautological section under
`f`, taken over `T`.

No terminality is used: this is the whole content of the entrywise description, and
`Stacks.SheafOfModules.freeHomMatrixEquiv_pullbackFreeHom` is the reading of it at a terminal
object. Stating it here rather than only there is what lets a consumer at a concrete site, where
`F T` and the object it means to call it by are definitionally but not syntactically equal, avoid
forcing that identification underneath the composite equivalence `freeHomMatrixEquiv`. -/
theorem freeCoord_pullbackFreeHom (I L : Type u) [DecidableEq L]
    (f : free (R := S) I ⟶ free (R := S) L) (i : I) (k : L) (T : C) :
    freeCoord (S := R) (op (F.obj T))
        ((ιFree (R := R) i ≫ pullbackFreeHom φ I L f).val.app (op (F.obj T))
          (unitOne (S := R) (op (F.obj T)))) k =
      φ.hom.app (op T)
        (freeCoord (S := S) (op T)
          ((ιFree (R := S) i ≫ f).val.app (op T) (unitOne (S := S) (op T))) k) := by
  rw [← unitToPushforwardObjUnit_unitOne φ (T := T)]
  exact (congrArg (fun m : unit S ⟶ (_root_.SheafOfModules.pushforward.{u} φ).obj (unit R) =>
      (_root_.SheafOfModules.Hom.val m).app (op T) (unitOne (S := S) (op T)))
    (pushforward_map_pullbackFreeHom_comp_freeProj φ I L f i k)).trans
      (unitToPushforwardObjUnit_val_app_apply φ _)

/-- **Extension of scalars acts entrywise on the matrix of a morphism of free sheaves of
modules.** On a site with a terminal object `T` whose image `F T` is terminal too, the `(i, k)`
entry of the matrix of the extension of scalars of `f` is the image under `φ` of the `(i, k)`
entry of the matrix of `f`.

This is the compatibility of the matrix description of the Hom-sets of free modules with the
transition functors of Stacks Tag 0EXE, which Stacks Tag 0EXD needs in order to read a cartesian
square of rings of global sections as a cartesian square of Hom-sets of free modules. -/
theorem freeHomMatrixEquiv_pullbackFreeHom {T : C} (hT : IsTerminal T)
    (hFT : IsTerminal (F.obj T)) (I L : Type u) [Fintype L] [DecidableEq L]
    (f : free (R := S) I ⟶ free (R := S) L) (i : I) (k : L) :
    freeHomMatrixEquiv (R := R) hFT I L (pullbackFreeHom φ I L f) i k =
      φ.hom.app (op T) (freeHomMatrixEquiv (R := S) hT I L f i k) := by
  rw [freeHomMatrixEquiv_apply, freeHomMatrixEquiv_apply]
  exact freeCoord_pullbackFreeHom φ I L f i k T

end Pullback

end Stacks.SheafOfModules

end
