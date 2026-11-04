module

public import Mathlib.Algebra.Category.Grp.Ulift
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.ProjectiveReplacementAcyclicity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CategoryHomology.SimplicialReplacementChainMap

/-!
# Acyclic covers of abelian presheaves with values in a larger universe

Let `C` be a small category, `C : Type u`.
`Stacks.CategoryHomology.freeRepresentablePresheaf_homology_isZero` computes the simplicial
replacement of the free abelian presheaf `V ↦ ℤ^{(V ⟶ U)}` on a representable, and
`Stacks.CategoryHomology.freeCover` covers every presheaf with values in `AddCommGrpCat.{u}`
by a direct sum of those. Both are stated at the value universe `u`, because the free abelian
group on `V ⟶ U` is a `u`-small group.

This file constructs the acyclic cover of a presheaf with values in `AddCommGrpCat.{max u v}`:
a direct sum, over all sections of all objects, of free abelian presheaves on representables,
each summand pushed into the larger universe by `AddCommGrpCat.uliftFunctor`.

## Main definitions

* `Stacks.CategoryHomology.replacementUliftFunctor`: the universe lift
  `AddCommGrpCat.{u} ⥤ AddCommGrpCat.{max u v}`.
* `Stacks.CategoryHomology.uliftReplacementGroupIso` and
  `Stacks.CategoryHomology.uliftSimplicialReplacementIso`: the simplicial replacement of a
  universe-lifted presheaf is the universe lift of its simplicial replacement.
* `Stacks.CategoryHomology.uliftFreeRepresentablePresheaf` and
  `Stacks.CategoryHomology.uliftFreeRepresentableHom`: the universe lift of the free abelian
  presheaf on a representable, and the morphism out of it determined by a section.
* `Stacks.CategoryHomology.uliftFreeCover` and `Stacks.CategoryHomology.uliftFreeCoverHom`: the
  canonical presentation of a presheaf with values in `AddCommGrpCat.{max u v}`.

## Main results

* `Stacks.CategoryHomology.uliftReplacementComplex_homology_isZero`: acyclicity of the
  replacement passes to a universe-lifted presheaf.
* `Stacks.CategoryHomology.uliftFreeCover_homology_isZero`: the canonical presentation has
  acyclic simplicial replacement in positive degrees.
* `Stacks.CategoryHomology.exists_acyclic_epi_of_presheaf`: every abelian presheaf with values
  in `AddCommGrpCat.{max u v}` admits an epimorphism onto it from a presheaf whose simplicial
  replacement is acyclic in positive degrees.

## Implementation notes

`DirectSum.of` carries a `DecidableEq` instance, and the definition and its computation rules
must use the same term, so it is bound to `Classical.decEq _` in every declaration that mentions
the cover.

## References

* [Stacks Project, Tag 08PG](https://stacks.math.columbia.edu/tag/08PG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open scoped DirectSum

universe u v

namespace Stacks.CategoryHomology

variable {C : Type u} [SmallCategory C]

/-- The universe lift of abelian groups, `AddCommGrpCat.{u} ⥤ AddCommGrpCat.{max u v}`. -/
abbrev replacementUliftFunctor : AddCommGrpCat.{u} ⥤ AddCommGrpCat.{max u v} :=
  AddCommGrpCat.uliftFunctor.{v, u}

/-! ### The replacement of a universe-lifted presheaf -/

/-- The degree-`p` replacement group of a universe-lifted presheaf is the universe lift of the
degree-`p` replacement group. -/
def uliftReplacementGroupIso (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (p : ℕ) :
    replacementGroup (F ⋙ replacementUliftFunctor.{u, v}) p ≅
      (replacementUliftFunctor.{u, v}).obj (replacementGroup F p) :=
  AddEquiv.toAddCommGrpIso
    ((DFinsupp.mapRange.addEquiv fun x : ComposableArrows C p =>
        (AddEquiv.ulift : ULift.{v} (F.obj (op x.right)) ≃+ _)).trans AddEquiv.ulift.symm)

/-- The value of `Stacks.CategoryHomology.uliftReplacementGroupIso` on a summand: it keeps the
index and strips the universe lift from the coefficient. -/
lemma uliftReplacementGroupIso_summand (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (p : ℕ)
    (y : ComposableArrows C p) (t : F.obj (op y.right)) :
    (uliftReplacementGroupIso.{u, v} F p).hom.hom
        (replacementSummand (F ⋙ replacementUliftFunctor.{u, v}) p y (ULift.up t)) =
      ULift.up (replacementSummand F p y t) := by
  classical
  show AddEquiv.ulift.symm (DFinsupp.mapRange.addEquiv (fun x : ComposableArrows C p =>
      (AddEquiv.ulift : ULift.{v} (F.obj (op x.right)) ≃+ _))
      (DirectSum.of (fun z : ComposableArrows C p => ULift.{v} (F.obj (op z.right))) y
        (ULift.up t))) = _
  rw [mapRangeAddEquiv_of]
  rfl

/-- The simplicial replacement of a universe-lifted presheaf is the universe lift of its
simplicial replacement. -/
def uliftSimplicialReplacementIso (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    simplicialReplacement (F ⋙ replacementUliftFunctor.{u, v}) ≅
      ((SimplicialObject.whiskering AddCommGrpCat.{u} AddCommGrpCat.{max u v}).obj
        replacementUliftFunctor.{u, v}).obj (simplicialReplacement F) :=
  NatIso.ofComponents (fun Δ => uliftReplacementGroupIso.{u, v} F Δ.unop.len) (by
    intro Δ Γ g
    refine replacementGroup_hom_ext (C' := C) Δ.unop.len fun x s => ?_
    have hL : ((simplicialReplacement (F ⋙ replacementUliftFunctor.{u, v})).map g ≫
          (uliftReplacementGroupIso.{u, v} F Γ.unop.len).hom).hom
        (replacementSummand (F ⋙ replacementUliftFunctor.{u, v}) Δ.unop.len x s) =
        ULift.up (replacementSummand F Γ.unop.len (x.whiskerLeft (simplexIndexMap g.unop))
          ((F.map (op (x.map (homOfLE (Fin.le_last _))))).hom s.down)) := by
      rw [AddCommGrpCat.comp_apply, simplicialReplacement_map,
        show (replacementMap (F ⋙ replacementUliftFunctor.{u, v}) g).hom
            (replacementSummand (F ⋙ replacementUliftFunctor.{u, v}) Δ.unop.len x s) =
          replacementSummand (F ⋙ replacementUliftFunctor.{u, v}) Γ.unop.len
            (x.whiskerLeft (simplexIndexMap g.unop))
            (ULift.up ((F.map (op (x.map (homOfLE (Fin.le_last _))))).hom s.down)) from
          replacementMap_on_generator (F ⋙ replacementUliftFunctor.{u, v}) g x s]
      exact uliftReplacementGroupIso_summand F _ _ _
    have hR : ((uliftReplacementGroupIso.{u, v} F Δ.unop.len).hom ≫
          (((SimplicialObject.whiskering AddCommGrpCat.{u} AddCommGrpCat.{max u v}).obj
            replacementUliftFunctor.{u, v}).obj (simplicialReplacement F)).map g).hom
        (replacementSummand (F ⋙ replacementUliftFunctor.{u, v}) Δ.unop.len x s) =
        ULift.up (replacementSummand F Γ.unop.len (x.whiskerLeft (simplexIndexMap g.unop))
          ((F.map (op (x.map (homOfLE (Fin.le_last _))))).hom s.down)) := by
      rw [AddCommGrpCat.comp_apply,
        show s = ULift.up s.down from rfl, uliftReplacementGroupIso_summand]
      change ULift.up ((replacementMap F g).hom (replacementSummand F Δ.unop.len x s.down)) = _
      rw [show (replacementMap F g).hom (replacementSummand F Δ.unop.len x s.down) =
          replacementSummand F Γ.unop.len (x.whiskerLeft (simplexIndexMap g.unop))
            ((F.map (op (x.map (homOfLE (Fin.le_last _))))).hom s.down) from
        replacementMap_on_generator F g x s.down]
    exact hL.trans hR.symm)

/-- The simplicial replacement *complex* of a universe-lifted presheaf is the universe lift of
its simplicial replacement complex. -/
def uliftReplacementComplexIso (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    simplicialReplacementComplex (F ⋙ replacementUliftFunctor.{u, v}) ≅
      ((replacementUliftFunctor.{u, v}).mapHomologicalComplex (ComplexShape.down ℕ)).obj
        (simplicialReplacementComplex F) :=
  (AlgebraicTopology.alternatingFaceMapComplex _).mapIso
      (uliftSimplicialReplacementIso.{u, v} F) ≪≫
    ((AlgebraicTopology.alternatingFaceMapComplexCompMapHomologicalComplexIso
      replacementUliftFunctor.{u, v}).app (simplicialReplacement F)).symm

/-- Vanishing of homology in a positive degree passes along the universe lift of complexes of
abelian groups. -/
theorem isZero_homology_mapHomologicalComplex_ulift
    {K : ChainComplex AddCommGrpCat.{u} ℕ} (n : ℕ) (h : IsZero (K.homology (n + 1))) :
    IsZero ((((replacementUliftFunctor.{u, v}).mapHomologicalComplex
      (ComplexShape.down ℕ)).obj K).homology (n + 1)) := by
  rw [← HomologicalComplex.exactAt_iff_isZero_homology] at h ⊢
  rw [HomologicalComplex.exactAt_iff' _ (n + 2) (n + 1) n (ChainComplex.prev ℕ (n + 1))
    (ChainComplex.next_nat_succ n)] at h ⊢
  exact h.map replacementUliftFunctor.{u, v}

/-- **Acyclicity of the simplicial replacement passes to a universe-lifted presheaf.** -/
theorem uliftReplacementComplex_homology_isZero (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ)
    (h : IsZero ((simplicialReplacementComplex F).homology (n + 1))) :
    IsZero ((simplicialReplacementComplex (F ⋙ replacementUliftFunctor.{u, v})).homology
      (n + 1)) :=
  IsZero.of_iso (isZero_homology_mapHomologicalComplex_ulift.{u, v} n h)
    ((HomologicalComplex.homologyFunctor AddCommGrpCat.{max u v} (ComplexShape.down ℕ)
      (n + 1)).mapIso (uliftReplacementComplexIso.{u, v} F))

/-! ### The cover -/

/-- The universe lift of the free abelian presheaf on a representable: `V ↦ ULift ℤ^{(V ⟶ U)}`,
with values in `AddCommGrpCat.{max u v}`. -/
abbrev uliftFreeRepresentablePresheaf (U : C) : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  freeRepresentablePresheaf U ⋙ replacementUliftFunctor.{u, v}

/-- The simplicial replacement of `Stacks.CategoryHomology.uliftFreeRepresentablePresheaf` is
acyclic in every positive degree. -/
theorem uliftFreeRepresentablePresheaf_homology_isZero (U : C) (n : ℕ) :
    IsZero ((simplicialReplacementComplex
      (uliftFreeRepresentablePresheaf.{u, v} U)).homology (n + 1)) :=
  uliftReplacementComplex_homology_isZero.{u, v} _ n
    (freeRepresentablePresheaf_homology_isZero U (n + 1) (Nat.succ_pos n))

/-- The morphism out of the universe-lifted free abelian presheaf on a representable determined
by a section over the representing object: the generator `h : V ⟶ U` is sent to the restriction
of the section along `h`. This is `Stacks.CategoryHomology.freeRepresentableHom` with the
universe lift stripped off the source. -/
def uliftFreeRepresentableHom {X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (U : C) (s : X.obj (op U)) :
    uliftFreeRepresentablePresheaf.{u, v} U ⟶ X where
  app Y := AddCommGrpCat.ofHom
    ((FreeAbelianGroup.lift fun h : Y.unop ⟶ U => (X.map h.op) s).comp
      (AddEquiv.ulift (α := FreeAbelianGroup (Y.unop ⟶ U))).toAddMonoidHom)
  naturality Y Z f := by
    apply AddCommGrpCat.hom_ext
    refine (AddMonoidHom.cancel_right
      (f := (AddEquiv.ulift (α := FreeAbelianGroup (Y.unop ⟶ U))).symm.toAddMonoidHom)
      (AddEquiv.ulift (α := FreeAbelianGroup (Y.unop ⟶ U))).symm.surjective).mp ?_
    apply FreeAbelianGroup.lift_ext
    intro g
    change (FreeAbelianGroup.lift fun h : Z.unop ⟶ U => (X.map h.op) s)
        ((AddCommGrpCat.free.map ((yoneda.obj U).map f)) (FreeAbelianGroup.of g))
      = (X.map f) ((FreeAbelianGroup.lift fun h : Y.unop ⟶ U => (X.map h.op) s)
          (FreeAbelianGroup.of g))
    rw [AddCommGrpCat.free_map_coe, FreeAbelianGroup.map_of, FreeAbelianGroup.lift_apply_of,
      FreeAbelianGroup.lift_apply_of]
    change (X.map (f.unop ≫ g).op) s = (X.map f) ((X.map g.op) s)
    rw [CategoryTheory.op_comp, X.map_comp, CategoryTheory.comp_apply]
    rfl

/-- The value of `Stacks.CategoryHomology.uliftFreeRepresentableHom` on the generator `𝟙 U`: it
is the given section. -/
lemma uliftFreeRepresentableHom_id {X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}} (U : C)
    (s : X.obj (op U)) :
    (uliftFreeRepresentableHom.{u, v} U s).app (op U)
        (ULift.up (FreeAbelianGroup.of (𝟙 U))) = s := by
  show (FreeAbelianGroup.lift fun h : U ⟶ U => (X.map h.op) s) (FreeAbelianGroup.of (𝟙 U)) = s
  rw [FreeAbelianGroup.lift_apply_of, op_id, X.map_id]
  rfl

/-- The index set of the canonical presentation of a presheaf with values in
`AddCommGrpCat.{max u v}`: a pair of an object of `C` and a section over it. -/
abbrev uliftFreeCoverIndex (X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) : Type (max u v) :=
  Σ U : C, (X.obj (op U) : Type (max u v))

/-- The canonical presentation of a presheaf with values in `AddCommGrpCat.{max u v}` by
universe-lifted free abelian presheaves on representables. -/
def uliftFreeCover (X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) : Cᵒᵖ ⥤ AddCommGrpCat.{max u v} :=
  directSumPresheaf fun i : uliftFreeCoverIndex.{u, v} X =>
    uliftFreeRepresentablePresheaf.{u, v} i.1

/-- The canonical presentation morphism, assembled from
`Stacks.CategoryHomology.uliftFreeRepresentableHom`. -/
def uliftFreeCoverHom (X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    uliftFreeCover.{u, v} X ⟶ X :=
  letI : DecidableEq (uliftFreeCoverIndex.{u, v} X) := Classical.decEq _
  directSumPresheafDesc _ fun i : uliftFreeCoverIndex.{u, v} X =>
    uliftFreeRepresentableHom.{u, v} i.1 i.2

/-- The canonical presentation morphism is an epimorphism. -/
instance uliftFreeCoverHom_epi (X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) :
    Epi (uliftFreeCoverHom.{u, v} X) :=
  letI : DecidableEq (uliftFreeCoverIndex.{u, v} X) := Classical.decEq _
  epi_directSumPresheafDesc _ _ fun Y s =>
    ⟨⟨Y.unop, s⟩, ULift.up (FreeAbelianGroup.of (𝟙 Y.unop)),
      uliftFreeRepresentableHom_id Y.unop s⟩

/-- The canonical presentation has acyclic simplicial replacement in every positive degree. -/
theorem uliftFreeCover_homology_isZero (X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    IsZero ((simplicialReplacementComplex (uliftFreeCover.{u, v} X)).homology (n + 1)) :=
  replacementComplex_homology_isZero_of_directSum _ n fun i =>
    uliftFreeRepresentablePresheaf_homology_isZero.{u, v} i.1 n

/-- **Every abelian presheaf with values in `AddCommGrpCat.{max u v}` admits an acyclic
epimorphic cover**: an epimorphism onto it from a presheaf whose simplicial replacement has
vanishing homology in degree `n + 1`. -/
theorem exists_acyclic_epi_of_presheaf (X : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (n : ℕ) :
    ∃ (P : Cᵒᵖ ⥤ AddCommGrpCat.{max u v}) (π : P ⟶ X), Epi π ∧
      IsZero ((simplicialReplacementComplex P).homology (n + 1)) :=
  ⟨uliftFreeCover.{u, v} X, uliftFreeCoverHom.{u, v} X, inferInstance,
    uliftFreeCover_homology_isZero.{u, v} X n⟩

end Stacks.CategoryHomology

end
