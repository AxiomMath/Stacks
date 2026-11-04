module

public import Mathlib.Algebra.Group.ULift
public import Mathlib.CategoryTheory.Subobject.Basic
public import Mathlib.GroupTheory.Archimedean
public import Mathlib.Topology.Irreducible
public import Mathlib.Topology.Sheaves.Abelian
public import StacksFrontier.Topology.Sheaves.Cohomology.Vanishing.IrreducibleSpaces
public import StacksFrontier.Topology.Sheaves.OpenImmersion.Restriction
public import StacksFrontier.Topology.Sheaves.Sheaf.Constant
import StacksCore.Tactic.StacksAttribute

/-!
# Subsheaves of the constant sheaf of integers on an irreducible space

Let `X` be an irreducible topological space and let `H` be an abelian subsheaf of the constant
sheaf of integers on `X`. Then there is a nonempty open `U ⊆ X` and an integer `d` such that
`H|_U` is the constant sheaf of the subgroup `dℤ`, compatibly with the inclusions of both into
the constant sheaf of integers restricted to `U`.

## Main definitions

None.

## Main results

* `Stacks.Sheaves.ConstantIntegerSubsheaves.exists_open_restrict_iso_constant_zmultiples`: on a
  nonempty open of an irreducible space an abelian subsheaf of the constant sheaf of integers is
  the constant sheaf of a subgroup `dℤ`.

## Implementation notes

*The explicit model.* On an irreducible space any two nonempty opens meet, so the constant
presheaf is already a sheaf away from the empty open and its sheafification is the presheaf
sending a nonempty open to the coefficient group and the empty open to zero. That presheaf is
`irreducibleConstantModel`, and `constantSheafIsoIrreducibleModel` is the identification;
`irreducibleConstantModelRestrictIso` identifies the model on an open subspace with the
restriction of the model on the ambient space, both being given by the same formula.

*Where the integer `d` comes from.* Through the model, a section of the subsheaf over a nonempty
open has a single well-defined value in `ℤ`, and that value is unchanged by restriction to a
smaller nonempty open. The values so obtained form a subgroup of `ℤ`, namely
`sectionValueSubgroup`; every subgroup of `ℤ` is `dℤ` for some `d`, and `d` itself is attained by
a section over some nonempty open `U`. Restricting to `U` makes every element of `dℤ` attained
over every nonempty open of `U`, which is exactly the bijectivity recorded in
`sectionValueFactor_restrict_bijective`, so the subsheaf restricted to `U` is the constant sheaf
of `dℤ`.

A subsheaf is a `CategoryTheory.Subobject` in the abelian category of sheaves of abelian groups,
and `dℤ` is `AddSubgroup.zmultiples d`. The coefficient category is `AddCommGrpCat.{v}` for a
universe `v` independent of the universe of `X`, so the integers appear as `ULift.{v} ℤ`.
Equality of the restricted subsheaf with the constant sheaf of `dℤ` is expressed by an
isomorphism of underlying presheaves commuting with the inclusions into the constant sheaf of
integers, whose own restriction to `U` is identified with the constant sheaf of integers on `U`
by the unique isomorphism preserving constant sections. The `HasSheafify` assumptions supply the
construction of those constant sheaves.

## References

* [Stacks Project, Tag 02UY](https://stacks.math.columbia.edu/tag/02UY)
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace TopCat Opposite
open CategoryTheory.Limits
open Stacks.CohomologyVanishing

namespace Stacks.Sheaves.ConstantIntegerSubsheaves

universe u v

/-- Every additive subgroup of a universe lift of the integers is the group of multiples of one
of its elements. -/
private lemma exists_zmultiples_eq (H : AddSubgroup (ULift.{v} ℤ)) :
    ∃ d : ULift.{v} ℤ, H = AddSubgroup.zmultiples d := by
  let e : ULift.{v} ℤ ≃+ ℤ := AddEquiv.ulift
  have hmem : ∀ z : ℤ, z ∈ H.map e.toAddMonoidHom ↔ (ULift.up z : ULift.{v} ℤ) ∈ H := by
    intro z
    refine ⟨?_, fun hz => ⟨ULift.up z, hz, rfl⟩⟩
    rintro ⟨x, hx, rfl⟩
    exact hx
  obtain ⟨n, hn⟩ := Int.subgroup_cyclic (H.map e.toAddMonoidHom)
  rw [← AddSubgroup.zmultiples_eq_closure] at hn
  refine ⟨ULift.up n, ?_⟩
  ext x
  refine ⟨fun hx => ?_, fun hx => ?_⟩
  · obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp (hn ▸ (hmem x.down).mpr hx)
    exact AddSubgroup.mem_zmultiples_iff.mpr ⟨k, ULift.ext _ _ hk⟩
  · obtain ⟨k, hk⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    exact (hmem x.down).mp (hn ▸ AddSubgroup.mem_zmultiples_iff.mpr ⟨k, congrArg ULift.down hk⟩)

private theorem sectionValue_restrict (X : TopCat.{u})
    (F : TopCat.Presheaf AddCommGrpCat.{v} X)
    (α : F ⟶ irreducibleConstantModel X (AddCommGrpCat.of (ULift.{v} ℤ)))
    {U V : Opens X} (i : V ⟶ U) (hU : (U : Set X).Nonempty)
    (hV : (V : Set X).Nonempty) (s : F.obj (op U)) :
    (irreducibleConstantModelEval X (AddCommGrpCat.of (ULift.{v} ℤ)) V hV).hom
        ((α.app (op V)).hom ((F.map i.op).hom s)) =
      (irreducibleConstantModelEval X (AddCommGrpCat.of (ULift.{v} ℤ)) U hU).hom
        ((α.app (op U)).hom s) := by
  rw [NatTrans.naturality_apply α i.op s]
  simpa only [ConcreteCategory.comp_apply] using congrArg
    (fun f : _ ⟶ AddCommGrpCat.of (ULift.{v} ℤ) => f.hom ((α.app (op U)).hom s))
    (irreducibleConstantModel_map_eval X (AddCommGrpCat.of (ULift.{v} ℤ)) i hV)

private noncomputable def irreducibleConstantModelRestrictIsoApp (X : TopCat.{u})
    (U : Opens X) (A : AddCommGrpCat.{v})
    (V : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ) :
    (irreducibleConstantModel ((Opens.toTopCat X).obj U) A).obj V ≅
      (restrictPresheaf (irreducibleConstantModel X A) U).obj V := by
  classical
  let O := U.isOpenEmbedding.functor.obj V.unop
  have qToP : PLift (∃ x : X, x ∈ O) →
      PLift (∃ x : ((Opens.toTopCat X).obj U), x ∈ V.unop) := fun q => ⟨by
    obtain ⟨_, y, hy, rfl⟩ := q.down
    exact ⟨y, hy⟩⟩
  have pToQ : PLift (∃ x : ((Opens.toTopCat X).obj U), x ∈ V.unop) →
      PLift (∃ x : X, x ∈ O) := fun p => ⟨by
    obtain ⟨x, hx⟩ := p.down
    exact ⟨x.1, Set.mem_image_of_mem _ hx⟩⟩
  let f : (irreducibleConstantModel ((Opens.toTopCat X).obj U) A).obj V ⟶
      (restrictPresheaf (irreducibleConstantModel X A) U).obj V := AddCommGrpCat.ofHom {
    toFun := fun s h => s (qToP h)
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  let g : (restrictPresheaf (irreducibleConstantModel X A) U).obj V ⟶
      (irreducibleConstantModel ((Opens.toTopCat X).obj U) A).obj V := AddCommGrpCat.ofHom {
    toFun := fun s h => s (pToQ h)
    map_zero' := rfl
    map_add' := fun _ _ => rfl }
  exact {
    hom := f
    inv := g
    hom_inv_id := by
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => funext fun h => ?_)
      change s (qToP (pToQ h)) = s h
      exact congrArg s (Subsingleton.elim _ _)
    inv_hom_id := by
      refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => funext fun h => ?_)
      change s (pToQ (qToP h)) = s h
      exact congrArg s (Subsingleton.elim _ _) }

private noncomputable def irreducibleConstantModelRestrictIso (X : TopCat.{u})
    (U : Opens X) (A : AddCommGrpCat.{v}) :
    irreducibleConstantModel ((Opens.toTopCat X).obj U) A ≅
      restrictPresheaf (irreducibleConstantModel X A) U := by
  classical
  refine NatIso.ofComponents (irreducibleConstantModelRestrictIsoApp X U A) ?_
  intro V W f
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => funext fun h => ?_)
  dsimp only [NatTrans.comp_app, Category.assoc,
    irreducibleConstantModelRestrictIsoApp, irreducibleConstantModel, restrictPresheaf]
  change s _ = s _
  exact congrArg s (Subsingleton.elim _ _)

private def sectionValueSubgroup (X : TopCat.{u}) [IrreducibleSpace X]
  (F : TopCat.Presheaf AddCommGrpCat.{v} X)
  (α : F ⟶ irreducibleConstantModel X (AddCommGrpCat.of (ULift.{v} ℤ))) :
    AddSubgroup (ULift.{v} ℤ) where
  carrier := {z | ∃ (U : Opens X) (hU : (U : Set X).Nonempty) (s : F.obj (op U)),
    (irreducibleConstantModelEval X (AddCommGrpCat.of (ULift.{v} ℤ)) U hU).hom
      ((α.app (op U)).hom s) = z}
  zero_mem' := by
    obtain ⟨x⟩ : Nonempty X := inferInstance
    refine ⟨⊤, ⟨x, trivial⟩, 0, ?_⟩
    simp
  add_mem' := by
    rintro a b ⟨U, hU, s, rfl⟩ ⟨V, hV, t, rfl⟩
    let W : Opens X := U ⊓ V
    have hW : (W : Set X).Nonempty := nonempty_preirreducible_inter U.2 V.2 hU hV
    let iU : W ⟶ U := homOfLE inf_le_left
    let iV : W ⟶ V := homOfLE inf_le_right
    refine ⟨W, hW, (F.map iU.op).hom s + (F.map iV.op).hom t, ?_⟩
    simp only [map_add]
    rw [sectionValue_restrict X F α iU hU hW s,
      sectionValue_restrict X F α iV hV hW t]
  neg_mem' := by
    rintro a ⟨U, hU, s, rfl⟩
    refine ⟨U, hU, -s, ?_⟩
    simp

private theorem sectionValueSubgroup_restrict_mem
    (X : TopCat.{u}) [IrreducibleSpace X]
    (F : TopCat.Presheaf AddCommGrpCat.{v} X)
    (α : F ⟶ irreducibleConstantModel X (AddCommGrpCat.of (ULift.{v} ℤ)))
    {U V : Opens X} (i : V ⟶ U) (hV : ∃ x : X, x ∈ V)
    (d : ULift.{v} ℤ) (hd : sectionValueSubgroup X F α = AddSubgroup.zmultiples d)
    (s : F.obj (op U))
    (hs : (irreducibleConstantModelEval X (AddCommGrpCat.of (ULift.{v} ℤ)) U
      ⟨hV.choose, i.le hV.choose_spec⟩).hom ((α.app (op U)).hom s) = d)
    (z : ULift.{v} ℤ) (hz : z ∈ sectionValueSubgroup X F α) :
    ∃ t : F.obj (op V),
      (irreducibleConstantModelEval X (AddCommGrpCat.of (ULift.{v} ℤ)) V hV).hom
        ((α.app (op V)).hom t) = z := by
  obtain ⟨n, hn⟩ := AddSubgroup.mem_zmultiples_iff.mp (hd ▸ hz)
  refine ⟨(F.map i.op).hom (n • s), ?_⟩
  rw [sectionValue_restrict X F α i
    ⟨hV.choose, i.le hV.choose_spec⟩ hV (n • s), map_zsmul, map_zsmul, hs, hn]

private def sectionValueFactor (X : TopCat.{u}) [IrreducibleSpace X]
    (F : TopCat.Presheaf AddCommGrpCat.{v} X)
    (α : F ⟶ irreducibleConstantModel X (AddCommGrpCat.of (ULift.{v} ℤ)))
    (d : ULift.{v} ℤ) (hd : sectionValueSubgroup X F α = AddSubgroup.zmultiples d) :
    F ⟶ irreducibleConstantModel X (AddCommGrpCat.of (AddSubgroup.zmultiples d)) where
  app V := AddCommGrpCat.ofHom {
    toFun := fun s q => ⟨α.app V s q, by
      rw [← hd]
      exact ⟨V.unop, q.down, s, rfl⟩⟩
    map_zero' := funext fun q => Subtype.ext (congrFun (map_zero (α.app V).hom) q)
    map_add' := fun s t => funext fun q => Subtype.ext (congrFun (map_add (α.app V).hom s t) q) }
  naturality := by
    intro V W f
    refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => funext fun q => Subtype.ext ?_)
    exact congrFun (NatTrans.naturality_apply α f s) q

private theorem sectionValueFactor_restrict_bijective
    (X : TopCat.{u}) [IrreducibleSpace X]
    (F : TopCat.Presheaf AddCommGrpCat.{v} X)
    (α : F ⟶ irreducibleConstantModel X (AddCommGrpCat.of (ULift.{v} ℤ)))
    (hα : ∀ V, Function.Injective ((α.app V).hom))
    (U : Opens X) (hU : (U : Set X).Nonempty) (d : ULift.{v} ℤ)
    (hd : sectionValueSubgroup X F α = AddSubgroup.zmultiples d)
    (s : F.obj (op U))
    (hs : (irreducibleConstantModelEval X (AddCommGrpCat.of (ULift.{v} ℤ)) U hU).hom
      ((α.app (op U)).hom s) = d)
    (V : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ) :
    Function.Bijective ((sectionValueFactor X F α d hd).app
      (op (U.isOpenEmbedding.functor.obj V.unop))).hom := by
  let O := U.isOpenEmbedding.functor.obj V.unop
  refine ⟨fun a b hab => hα (op O) (funext fun q => congrArg Subtype.val (congrFun hab q)),
    fun t => ?_⟩
  by_cases hO : (O : Set X).Nonempty
  · let i : O ⟶ U := homOfLE (by
      rintro x ⟨y, hy, rfl⟩
      exact y.property)
    obtain ⟨a, ha⟩ := sectionValueSubgroup_restrict_mem X F α i hO d hd s hs
      (t ⟨hO⟩).val (hd.symm ▸ (t ⟨hO⟩).property)
    refine ⟨a, funext fun q => ?_⟩
    obtain rfl : q = ⟨hO⟩ := Subsingleton.elim _ _
    exact Subtype.ext ha
  · exact ⟨0, funext fun q => (hO q.down).elim⟩

private def sectionValueFactorRestrictIso
    (X : TopCat.{u}) [IrreducibleSpace X]
    (F : TopCat.Presheaf AddCommGrpCat.{v} X)
    (α : F ⟶ irreducibleConstantModel X (AddCommGrpCat.of (ULift.{v} ℤ)))
    (hα : ∀ V, Function.Injective ((α.app V).hom))
    (U : Opens X) (hU : (U : Set X).Nonempty) (d : ULift.{v} ℤ)
    (hd : sectionValueSubgroup X F α = AddSubgroup.zmultiples d)
    (s : F.obj (op U))
    (hs : (irreducibleConstantModelEval X (AddCommGrpCat.of (ULift.{v} ℤ)) U hU).hom
      ((α.app (op U)).hom s) = d) :
    restrictPresheaf F U ≅ restrictPresheaf
      (irreducibleConstantModel X (AddCommGrpCat.of (AddSubgroup.zmultiples d))) U :=
  NatIso.ofComponents (fun V => (AddEquiv.ofBijective
    ((sectionValueFactor X F α d hd).app
      (op (U.isOpenEmbedding.functor.obj V.unop))).hom
    (sectionValueFactor_restrict_bijective X F α hα U hU d hd s hs V)).toAddCommGrpIso)
    (fun f => (sectionValueFactor X F α d hd).naturality
      (U.isOpenEmbedding.functor.op.map f))

/-- The underlying presheaf of the constant sheaf is isomorphic to the explicit model. -/
private def constantSheafModelIso (X : TopCat.{u})
    [PreirreducibleSpace X] [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (A : AddCommGrpCat.{v}) :
    ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj A).obj ≅
      irreducibleConstantModel X A :=
  (sheafToPresheaf (Opens.grothendieckTopology X) AddCommGrpCat).mapIso
    (constantSheafIsoIrreducibleModel X A)

/-- The unit of sheafification, as a map into the underlying presheaf of the constant sheaf. -/
private def constantSheafUnit (X : TopCat.{u})
    [PreirreducibleSpace X] [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (A : AddCommGrpCat.{v}) :
    (Functor.const (Opens X)ᵒᵖ).obj A ⟶
      ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj A).obj :=
  toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj A)

/-- The comparison with the model sends the unit of sheafification to the constant sections. -/
private theorem constantSheafModelIso_unit (X : TopCat.{u})
    [PreirreducibleSpace X] [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (A : AddCommGrpCat.{v}) (V : (Opens X)ᵒᵖ) :
    (constantSheafUnit X A).app V ≫ (constantSheafModelIso X A).hom.app V =
      (constantToIrreducibleModel X A).app V :=
  NatTrans.congr_app (toSheafify_sheafifyLift _ _ _) V

private theorem constantSheaf_unit_surjective (X : TopCat.{u})
    [PreirreducibleSpace X] [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (A : AddCommGrpCat.{v}) (V : (Opens X)ᵒᵖ) :
    Function.Surjective ((toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj A)).app V).hom := by
  let e := constantSheafModelIso X A
  have hi : Function.Injective (e.hom.app V).hom :=
    (AddCommGrpCat.mono_iff_injective _).mp inferInstance
  intro s
  by_cases hV : (V.unop : Set X).Nonempty
  · refine ⟨e.hom.app V s ⟨hV⟩, hi ?_⟩
    have h := congrArg (fun f => f (e.hom.app V s ⟨hV⟩))
      (constantSheafModelIso_unit X A V)
    change e.hom.app V ((toSheafify (Opens.grothendieckTopology X)
      ((Functor.const (Opens X)ᵒᵖ).obj A)).app V _) = _ at h
    rw [h]
    funext q
    exact congrArg (e.hom.app V s) (Subsingleton.elim _ _)
  · exact ⟨0, hi (funext fun q => (hV q.down).elim)⟩

private def irreducibleConstantModelMap (X : TopCat.{u})
    {A B : AddCommGrpCat.{v}} (f : A ⟶ B) :
    irreducibleConstantModel X A ⟶ irreducibleConstantModel X B where
  app _ := AddCommGrpCat.ofHom {
    toFun := fun s q => f (s q)
    map_zero' := funext fun _ => map_zero f.hom
    map_add' := fun _ _ => funext fun _ => map_add f.hom _ _ }
  naturality _ _ _ := rfl

private theorem irreducibleConstantModelRestrictIso_unit (X : TopCat.{u})
    (U : Opens X) (A : AddCommGrpCat.{v})
    (V : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ) :
    (constantToIrreducibleModel ((Opens.toTopCat X).obj U) A).app V ≫
      (irreducibleConstantModelRestrictIso X U A).hom.app V =
      (constantToIrreducibleModel X A).app (op (U.isOpenEmbedding.functor.obj V.unop)) :=
  AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ => funext fun _ => rfl)

private def constantSheafRestrictIso (X : TopCat.{u}) [PreirreducibleSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] (U : Opens X)
    [PreirreducibleSpace ((Opens.toTopCat X).obj U)]
    [HasSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{v}]
    (A : AddCommGrpCat.{v}) :
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      AddCommGrpCat.{v}).obj A).obj ≅
      restrictPresheaf ((constantSheaf (Opens.grothendieckTopology X)
        AddCommGrpCat.{v}).obj A).obj U := by
  let Y := (Opens.toTopCat X).obj U
  exact constantSheafModelIso Y A ≪≫ irreducibleConstantModelRestrictIso X U A ≪≫
    Functor.isoWhiskerLeft U.isOpenEmbedding.functor.op (constantSheafModelIso X A).symm

private theorem constantSheafRestrictIso_unit (X : TopCat.{u}) [PreirreducibleSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}] (U : Opens X)
    [PreirreducibleSpace ((Opens.toTopCat X).obj U)]
    [HasSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{v}]
    (A : AddCommGrpCat.{v}) (V : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ) :
    (toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      ((Functor.const (Opens ((Opens.toTopCat X).obj U))ᵒᵖ).obj A)).app V ≫
        (constantSheafRestrictIso X U A).hom.app V =
      (toSheafify (Opens.grothendieckTopology X) ((Functor.const (Opens X)ᵒᵖ).obj A)).app
        (op (U.isOpenEmbedding.functor.obj V.unop)) := by
  let Y := (Opens.toTopCat X).obj U
  let O := op (U.isOpenEmbedding.functor.obj V.unop)
  let r : irreducibleConstantModel Y A ≅
      U.isOpenEmbedding.functor.op ⋙ irreducibleConstantModel X A :=
    irreducibleConstantModelRestrictIso X U A
  change (constantSheafUnit Y A).app V ≫ (constantSheafModelIso Y A).hom.app V ≫
    r.hom.app V ≫ (constantSheafModelIso X A).inv.app O =
      (constantSheafUnit X A).app O
  have hr : (constantToIrreducibleModel Y A).app V ≫ r.hom.app V =
      (constantToIrreducibleModel X A).app O :=
    irreducibleConstantModelRestrictIso_unit X U A V
  rw [← Category.assoc, constantSheafModelIso_unit Y A V, ← Category.assoc, hr,
    ← constantSheafModelIso_unit X A O]
  simp only [Category.assoc, (constantSheafModelIso X A).hom_inv_id_app, Category.comp_id]

private def subsheafToModel (X : TopCat.{u}) [PreirreducibleSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (H : Subobject ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)))) :
    (Subobject.underlying.obj H).obj ⟶
      irreducibleConstantModel X (AddCommGrpCat.of (ULift.{v} ℤ)) :=
  H.arrow.hom ≫ (constantSheafModelIso X (AddCommGrpCat.of (ULift.{v} ℤ))).hom

private theorem subsheafToModel_injective (X : TopCat.{u}) [PreirreducibleSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (H : Subobject ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)))) (V : (Opens X)ᵒᵖ) :
    Function.Injective ((subsheafToModel X H).app V).hom :=
  ((AddCommGrpCat.mono_iff_injective
    ((constantSheafModelIso X (AddCommGrpCat.of (ULift.{v} ℤ))).hom.app V)).mp
        inferInstance).comp
    ((AddCommGrpCat.mono_iff_injective (H.arrow.hom.app V)).mp inferInstance)

private def subsheafRestrictIso (X : TopCat.{u}) [IrreducibleSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (H : Subobject ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))))
    (U : Opens X) (hU : (U : Set X).Nonempty)
    [PreirreducibleSpace ((Opens.toTopCat X).obj U)]
    [HasSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{v}]
    (d : ULift.{v} ℤ)
    (hd : sectionValueSubgroup X _ (subsheafToModel X H) = AddSubgroup.zmultiples d)
    (s : (Subobject.underlying.obj H).obj.obj (op U))
    (hs : (irreducibleConstantModelEval X (AddCommGrpCat.of (ULift.{v} ℤ)) U hU).hom
      (((subsheafToModel X H).app (op U)).hom s) = d) :
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      AddCommGrpCat.{v}).obj (AddCommGrpCat.of (AddSubgroup.zmultiples d))).obj ≅
      restrictPresheaf (Subobject.underlying.obj H).obj U := by
  let Y := (Opens.toTopCat X).obj U
  let D := AddCommGrpCat.of (AddSubgroup.zmultiples d)
  let eD := constantSheafModelIso Y D
  let rD : irreducibleConstantModel Y D ≅
      U.isOpenEmbedding.functor.op ⋙ irreducibleConstantModel X D :=
    irreducibleConstantModelRestrictIso X U D
  let eβ : U.isOpenEmbedding.functor.op ⋙ (Subobject.underlying.obj H).obj ≅
      U.isOpenEmbedding.functor.op ⋙ irreducibleConstantModel X D :=
    sectionValueFactorRestrictIso X _ _ (subsheafToModel_injective X H) U hU d hd s hs
  exact eD ≪≫ rD ≪≫ eβ.symm

private theorem subsheafRestrictIso_unit (X : TopCat.{u}) [IrreducibleSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (H : Subobject ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))))
    (U : Opens X) (hU : (U : Set X).Nonempty)
    [PreirreducibleSpace ((Opens.toTopCat X).obj U)]
    [HasSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{v}]
    (d : ULift.{v} ℤ)
    (hd : sectionValueSubgroup X _ (subsheafToModel X H) = AddSubgroup.zmultiples d)
    (s : (Subobject.underlying.obj H).obj.obj (op U))
    (hs : (irreducibleConstantModelEval X (AddCommGrpCat.of (ULift.{v} ℤ)) U hU).hom
      (((subsheafToModel X H).app (op U)).hom s) = d)
    (V : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ) :
    AddCommGrpCat.ofHom (AddSubgroup.zmultiples d).subtype ≫
      (constantToIrreducibleModel X (AddCommGrpCat.of (ULift.{v} ℤ))).app
        (op (U.isOpenEmbedding.functor.obj V.unop)) =
      ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
        ((Functor.const (Opens ((Opens.toTopCat X).obj U))ᵒᵖ).obj
          (AddCommGrpCat.of (AddSubgroup.zmultiples d)))).app V ≫
        (subsheafRestrictIso X H U hU d hd s hs).hom.app V) ≫
        (subsheafToModel X H).app (op (U.isOpenEmbedding.functor.obj V.unop)) := by
  let Y := (Opens.toTopCat X).obj U
  let Z := AddCommGrpCat.of (ULift.{v} ℤ)
  let D := AddCommGrpCat.of (AddSubgroup.zmultiples d)
  let ι : D ⟶ Z := AddCommGrpCat.ofHom (AddSubgroup.zmultiples d).subtype
  let O := op (U.isOpenEmbedding.functor.obj V.unop)
  let α := subsheafToModel X H
  let rD : irreducibleConstantModel Y D ≅
      U.isOpenEmbedding.functor.op ⋙ irreducibleConstantModel X D :=
    irreducibleConstantModelRestrictIso X U D
  let eβ : U.isOpenEmbedding.functor.op ⋙ (Subobject.underlying.obj H).obj ≅
      U.isOpenEmbedding.functor.op ⋙ irreducibleConstantModel X D :=
    sectionValueFactorRestrictIso X _ α (subsheafToModel_injective X H) U hU d hd s hs
  have hβ : eβ.hom.app V ≫ (irreducibleConstantModelMap X ι).app O = α.app O := rfl
  calc
    ι ≫ (constantToIrreducibleModel X Z).app O =
        (constantToIrreducibleModel Y D).app V ≫ rD.hom.app V ≫
          (irreducibleConstantModelMap X ι).app O :=
      AddCommGrpCat.hom_ext (AddMonoidHom.ext fun _ => funext fun _ => rfl)
    _ = ((constantSheafUnit Y D).app V ≫
        ((constantSheafModelIso Y D).hom.app V ≫ rD.hom.app V ≫ eβ.inv.app V)) ≫ α.app O := by
      rw [← hβ]
      simp only [Category.assoc, eβ.inv_hom_id_app_assoc]
      rw [← constantSheafModelIso_unit Y D V]
      simp only [Category.assoc]

private theorem subsheafRestrictIso_compat (X : TopCat.{u}) [IrreducibleSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    (H : Subobject ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))))
    (U : Opens X) (hU : (U : Set X).Nonempty)
    [PreirreducibleSpace ((Opens.toTopCat X).obj U)]
    [HasSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{v}]
    (d : ULift.{v} ℤ)
    (hd : sectionValueSubgroup X _ (subsheafToModel X H) = AddSubgroup.zmultiples d)
    (s : (Subobject.underlying.obj H).obj.obj (op U))
    (hs : (irreducibleConstantModelEval X (AddCommGrpCat.of (ULift.{v} ℤ)) U hU).hom
      (((subsheafToModel X H).app (op U)).hom s) = d)
    (V : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ) :
    ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
      AddCommGrpCat.{v}).map (AddCommGrpCat.ofHom (AddSubgroup.zmultiples d).subtype)).hom.app V ≫
      (constantSheafRestrictIso X U (AddCommGrpCat.of (ULift.{v} ℤ))).hom.app V =
      (subsheafRestrictIso X H U hU d hd s hs).hom.app V ≫
        H.arrow.hom.app (op (U.isOpenEmbedding.functor.obj V.unop)) := by
  let Y := (Opens.toTopCat X).obj U
  let Z := AddCommGrpCat.of (ULift.{v} ℤ)
  let D := AddCommGrpCat.of (AddSubgroup.zmultiples d)
  let ι : D ⟶ Z := AddCommGrpCat.ofHom (AddSubgroup.zmultiples d).subtype
  let O := op (U.isOpenEmbedding.functor.obj V.unop)
  have hZ : (constantSheafUnit Y Z).app V ≫ (constantSheafRestrictIso X U Z).hom.app V =
      (constantSheafUnit X Z).app O :=
    constantSheafRestrictIso_unit X U Z V
  have : Epi ((constantSheafUnit Y D).app V) := (AddCommGrpCat.epi_iff_surjective _).mpr
    (constantSheaf_unit_surjective Y D V)
  refine (cancel_epi ((constantSheafUnit Y D).app V)).mp ?_
  have hnat : (constantSheafUnit Y D).app V ≫
      ((constantSheaf (Opens.grothendieckTopology Y) AddCommGrpCat.{v}).map ι).hom.app V =
      ι ≫ (constantSheafUnit Y Z).app V :=
    (NatTrans.congr_app (toSheafify_naturality (Opens.grothendieckTopology Y)
      ((Functor.const (Opens Y)ᵒᵖ).map ι)) V).symm
  rw [← Category.assoc, hnat, Category.assoc, hZ]
  refine (cancel_mono ((constantSheafModelIso X Z).hom.app O)).mp ?_
  change (ι ≫ (constantSheafUnit X Z).app O) ≫ (constantSheafModelIso X Z).hom.app O =
    ((constantSheafUnit Y D).app V ≫ (subsheafRestrictIso X H U hU d hd s hs).hom.app V) ≫
      (subsheafToModel X H).app O
  rw [Category.assoc, constantSheafModelIso_unit X Z O]
  exact subsheafRestrictIso_unit X H U hU d hd s hs V

/-- An abelian subsheaf of the constant integer sheaf is, on some nonempty open of an
irreducible space, the constant sheaf of `dℤ`, compatibly with its inclusion into the
constant integer sheaf. -/
@[stacks 02UY]
theorem exists_open_restrict_iso_constant_zmultiples
    (X : TopCat.{u}) [IrreducibleSpace X]
    [HasSheafify (Opens.grothendieckTopology X) AddCommGrpCat.{v}]
    [∀ (U : Opens X), HasSheafify
      (Opens.grothendieckTopology ((Opens.toTopCat X).obj U)) AddCommGrpCat.{v}]
    (H : Subobject ((constantSheaf (Opens.grothendieckTopology X)
      AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ)))) :
    ∃ (U : Opens X), (U : Set X).Nonempty ∧
      ∃ (d : ULift.{v} ℤ)
        (eH : ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          AddCommGrpCat.{v}).obj
            (AddCommGrpCat.of (AddSubgroup.zmultiples d))).obj ≅
          restrictPresheaf (Subobject.underlying.obj H).obj U)
        (eZ : ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          AddCommGrpCat.{v}).obj (AddCommGrpCat.of (ULift.{v} ℤ))).obj ≅
          restrictPresheaf
            ((constantSheaf (Opens.grothendieckTopology X) AddCommGrpCat.{v}).obj
              (AddCommGrpCat.of (ULift.{v} ℤ))).obj U),
        (∀ (V : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ),
          ((toSheafify (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
            ((Functor.const (Opens ((Opens.toTopCat X).obj U))ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{v} ℤ)))).app V) ≫ eZ.hom.app V =
          (toSheafify (Opens.grothendieckTopology X)
            ((Functor.const (Opens X)ᵒᵖ).obj
              (AddCommGrpCat.of (ULift.{v} ℤ)))).app
                (op (U.isOpenEmbedding.functor.obj V.unop))) ∧
        (∀ (V : (Opens ((Opens.toTopCat X).obj U))ᵒᵖ),
          ((constantSheaf (Opens.grothendieckTopology ((Opens.toTopCat X).obj U))
          AddCommGrpCat.{v}).map
            (AddCommGrpCat.ofHom
              (AddSubgroup.zmultiples d).subtype)).hom.app V ≫
              eZ.hom.app V = eH.hom.app V ≫
              H.arrow.hom.app (op (U.isOpenEmbedding.functor.obj V.unop))) := by
  obtain ⟨d, hd⟩ := exists_zmultiples_eq (sectionValueSubgroup X _ (subsheafToModel X H))
  obtain ⟨U, hU, s, hs⟩ : d ∈ sectionValueSubgroup X _ (subsheafToModel X H) :=
    hd ▸ AddSubgroup.mem_zmultiples d
  have : IrreducibleSpace ((Opens.toTopCat X).obj U) :=
    Subtype.irreducibleSpace ⟨hU,
      PreirreducibleSpace.isPreirreducible_univ.open_subset U.2 (Set.subset_univ _)⟩
  exact ⟨U, hU, d, subsheafRestrictIso X H U hU d hd s hs, constantSheafRestrictIso X U _,
    constantSheafRestrictIso_unit X U _, subsheafRestrictIso_compat X H U hU d hd s hs⟩

end Stacks.Sheaves.ConstantIntegerSubsheaves

end
