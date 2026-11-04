module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparisonIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorIso
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorAlgebraConstruction
public import StacksCore.Tactic.StacksAttribute

/-!
# The pullback-tensor comparison on a ringed space is the canonical one

Let `f : X ⟶ Y` be a morphism of ringed spaces and let `A`, `B` be sheaves of `𝒪_Y`-modules.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorComparison` constructs the canonical
comparison morphism `Stacks.RingedSpace.comparison f A B : f^*(A ⊗_{𝒪_Y} B) ⟶ f^*A ⊗_{𝒪_X} f^*B`
of Stacks 01CD, computes it on the images of pure tensors, and proves
(`Stacks.RingedSpace.comparison_unique`) that that computation determines it.
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackTensorIso` constructs an isomorphism
`Stacks.PullbackTensor.pullbackTensorSheafObjIso` of exactly that type, as a composite of four
links, but leaves open whether it is *the* comparison.

Here the composite is computed on the sheafification-unit image of a pure tensor of local
sections and identified with the comparison by `comparison_unique`. Consequently every component
of the comparison is an isomorphism, and `Stacks.RingedSpace.comparisonIso` applies with no
hypothesis.

## Main definitions

* `Stacks.PullbackTensor.shUnit`: a local section of a presheaf of `𝒪_X`-modules, read in its
  sheafification through the unit of the sheafification adjunction.
* `Stacks.PullbackTensor.preUnit`: a local section of a presheaf of `𝒪_Y`-modules, read in the
  presheaf-level pullback through the unit of
  `PresheafOfModules.pullbackPushforwardAdjunction`.
* `Stacks.PullbackTensor.unitArrow`: the index object `(U, 𝟙)` of the filtered colimit computing
  the pullback, at which that unit lives.

## Main results

* `Stacks.PullbackTensor.pullbackTensorIso_hom_preUnit_tmul`: **the presheaf-level comparison of
  Tag 01CD is canonical** — it carries the pullback-unit image of a pure tensor to the pure
  tensor of the two pullback-unit images.
* `Stacks.PullbackTensor.pullbackTensorSheafObjIso_hom_eq_comparison`: **the canonicality clause
  of Stacks 01CD** — `pullbackTensorSheafObjIso` *is* `Stacks.RingedSpace.comparison`.
* `Stacks.PullbackTensor.isIso_comparison`: **Stacks 01CD** — every component of the
  canonical comparison is an isomorphism.
* `Stacks.PullbackTensor.comparisonIso_hom_app`: the component of that isomorphism at `(A, B)`
  is `pullbackTensorSheafObjIso`.
* The links, each on a unit image: `sheafificationCompPullback_hom_pullbackUnit` (link 1),
  `pullbackIso_hom_preUnit` and `pullbackIso_inv_germ` (the model comparison inside link 2),
  `sheafificationTensorObjIso_hom_shUnit_tmul` (link 3, Tag 0GMW read on sections) and
  `sheafPullbackIso_inv_shUnit` (link 4).

## Implementation notes

Three of the four links, and `Stacks.PullbackColimit.pullbackIso` inside link 2, are
`CategoryTheory.Adjunction.leftAdjointUniq` isomorphisms, so each is computed from
`CategoryTheory.Adjunction.unit_leftAdjointUniq_hom_app`: the defining property of
`leftAdjointUniq` is exactly that it carries one unit to the other.  Read on sections by
`PresheafOfModules.hom_congr_apply'` (link 1 and the presheaf-level model) or by
`SheafOfModules.hom_congr_app_apply` (link 4), each of those becomes a one-line proof.  Link 1
is stated for the *composite* adjunctions whose left adjoints are `sheafification ⋙ f^*` and
`f^*_pre ⋙ sheafification`, which is the shape `SheafOfModules.sheafificationCompPullback` has;
link 4 compares `SheafOfModules.pullbackPushforwardAdjunction` with
`SheafOfModules.PullbackConstruction.adjunction`, whose unit on sections is definitionally
`shUnit` of `preUnit`.

`Stacks.RingedSpace.pullbackAdjunction` is used in place of
`SheafOfModules.pullbackPushforwardAdjunction (structureSheafHom f)` throughout, although the
two are definitionally equal.  The reason is instance resolution: the sheaf-level instance
`(SheafOfModules.pushforward φ).IsRightAdjoint` is not found for `φ = structureSheafHom f`, while
`RingedSpaceModuleAdjunction.modulePullbackPushforwardAdjunction` supplies it with a `letI`.
Since `CategoryTheory.Functor.IsRightAdjoint` is a `Prop`, proof irrelevance makes the two terms
interchangeable, so nothing is lost.

Every rewrite in `pullbackTensorIso_hom_preUnit_tmul` and in
`pullbackTensorSheafObjIso_hom_eq_comparison` carries its arguments explicitly, and the last two
steps use `congrArg` rather than `rw`.  That is forced, not stylistic.  The implicit arguments of
`PresheafOfModules.Hom.app` are the two presheaves of modules, and the same presheaf has several
spellings here — the uncurried native tensor after `Functor.prod` against
`PresheafOfModules.tensorObj _ _`, `pullbackFunctor f` against
`SheafOfModules.pullback (structureSheafHom f)`, `X.presheaf` against `X.sheaf.obj` — which agree
definitionally but not syntactically, so a `rw` whose pattern was generated from the other
spelling reports that it found no occurrence.  In the final step the goal is not even
type-correct at `implicit` transparency, because the `Module` instances on a pure tensor there
require unfolding `RingedSpaceModuleAdjunction.modulePullback`.  Explicit arguments and
`congrArg` elaborate at default transparency and are immune to all of this.

The three `change`s inside `pullbackTensorIso_hom_preUnit_tmul` replace a `germ` of a pure
tensor by `Stacks.PullbackTensor.germTmul`, and `Stacks.PullbackTensor.tmulGerm` by a pure
tensor of germs.  Both are definitional, and `PullbackTensorIso` records why they cannot be
rewrites: a rule whose left-hand side mentions `germ F R (tensorObj A B) T r (a ⊗ₜ b)` cannot be
applied, since building the motive needs that assignment to typecheck at `implicit`
transparency.

Universes are not narrowed: everything is stated for `RingedSpace.{u, u}` and
`SheafOfModules.{u}`, exactly as in the two imported files.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0GMW](https://stacks.math.columbia.edu/tag/0GMW)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace
open scoped TensorProduct

universe u

namespace Stacks.PullbackTensor

open _root_.PresheafOfModules Stacks.PullbackModel Stacks.RingedSpace Stacks.PullbackColimit
open RingedSpaceModuleAdjunction CategoryTheory.Sheaf

variable {X Y : RingedSpace.{u, u}} (f : X ⟶ Y)

section Sheafify

variable (X)

/-- A local section of a presheaf of `𝒪_X`-modules, carried into its sheafification by the
unit of the sheafification adjunction. -/
noncomputable def shUnit
    (P : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (V : (Opens X.carrier)ᵒᵖ) (p : P.obj V) :
    ((PresheafOfModules.sheafification (𝟙 (structureRingSheaf X).obj)).obj P).val.obj V :=
  Hom.app ((PresheafOfModules.sheafificationAdjunction
    (𝟙 (structureRingSheaf X).obj)).unit.app P) V p

/-- The comparison `sheafificationTensorObjIso` carries the unit image of a pure tensor to the
unit image of the pure tensor of the unit images. -/
lemma sheafificationTensorObjIso_hom_shUnit_tmul
    (P Q : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat))
    (V : (Opens X.carrier)ᵒᵖ) (p : P.obj V) (q : Q.obj V) :
    Hom.app (sheafificationTensorObjIso X P Q).hom.val V
        (shUnit X (tensorObj P Q) V (p ⊗ₜ q)) =
      Hom.app ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩)
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj)).unit.app
        (_root_.PresheafOfModules.tensorObj
          ((PresheafOfModules.sheafification (𝟙 (structureRingSheaf X).obj)).obj P).val
          ((PresheafOfModules.sheafification (𝟙 (structureRingSheaf X).obj)).obj Q).val)) V
        (shUnit X P V p ⊗ₜ shUnit X Q V q) :=
  PresheafOfModules.sheafificationTensorIso_inv_unit_tmul
    (Opens.grothendieckTopology X.carrier) (𝟙 X.sheaf.obj) P Q V p q

/-- Naturality of the sheafification unit, in the `shUnit` spelling. -/
lemma sheafification_map_shUnit
    {P Q : PresheafOfModules.{u} (X.presheaf ⋙ forget₂ CommRingCat RingCat)} (φ : P ⟶ Q)
    (V : (Opens X.carrier)ᵒᵖ) (p : P.obj V) :
    Hom.app ((PresheafOfModules.sheafification (𝟙 (structureRingSheaf X).obj)).map φ).val V
        (shUnit X P V p) = shUnit X Q V (Hom.app φ V p) :=
  PresheafOfModules.unit_naturality_apply (α := 𝟙 (structureRingSheaf X).obj) φ V p

end Sheafify

/-- A local section of a presheaf of `𝒪_Y`-modules, carried into the presheaf-level pullback
by the unit of the adjunction. -/
noncomputable def preUnit
    (M : PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens Y.carrier)ᵒᵖ) (m : M.obj U) :
    ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj M).obj
      ((opensMap f).op.obj U) :=
  Hom.app ((PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (structureSheafHom f).hom).unit.app M) U m

/-- The index object of the colimit computing the pullback at which the unit lives: the
identity arrow on `f⁻¹U`. -/
noncomputable abbrev unitArrow (U : (Opens Y.carrier)ᵒᵖ) :
    CostructuredArrow (opensMap f).op ((opensMap f).op.obj U) :=
  CostructuredArrow.mk (𝟙 ((opensMap f).op.obj U))

/-- The germ description of `preUnit` through the concrete model of the pullback. -/
lemma pullbackIso_hom_preUnit
    (M : PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens Y.carrier)ᵒᵖ) (m : M.obj U) :
    Hom.app ((PullbackColimit.pullbackIso f.hom.c).hom.app M)
        ((opensMap f).op.obj U) (preUnit f M U m) =
      germ (opensMap f) X.presheaf ((extendScalars f.hom.c).obj M) (unitArrow f U) 1
        (tmul (f.hom.c.app U).hom 1 m) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureSheafHom f).hom)
    (PullbackColimit.modelAdjunction f.hom.c) M
  exact PresheafOfModules.hom_congr_apply' h U m

/-- The inverse of the model comparison carries the model unit germ back to `preUnit`. -/
lemma pullbackIso_inv_germ
    (M : PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens Y.carrier)ᵒᵖ) (m : M.obj U) :
    Hom.app ((PullbackColimit.pullbackIso f.hom.c).inv.app M)
        ((opensMap f).op.obj U)
        (germ (opensMap f) X.presheaf ((extendScalars f.hom.c).obj M) (unitArrow f U) 1
          (tmul (f.hom.c.app U).hom 1 m)) =
      preUnit f M U m := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (PullbackColimit.modelAdjunction f.hom.c)
    (PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureSheafHom f).hom) M
  exact PresheafOfModules.hom_congr_apply' h U m

/-- The presheaf-level pullback comparison carries the unit image of a pure tensor to the pure
tensor of the unit images. -/
lemma pullbackTensorIso_hom_preUnit_tmul
    (M N : PresheafOfModules.{u} (Y.presheaf ⋙ forget₂ CommRingCat RingCat))
    (U : (Opens Y.carrier)ᵒᵖ) (x : M.obj U) (y : N.obj U) :
    Hom.app ((pullbackTensorIso f.hom.c).hom.app (M, N)) ((opensMap f).op.obj U)
        (preUnit f (tensorObj M N) U (x ⊗ₜ y)) =
      (preUnit f M U x ⊗ₜ preUnit f N U y :
        (tensorObj ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj M)
          ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj N)).obj
            ((opensMap f).op.obj U)) := by
  show Hom.app
    ((Functor.uncurry.obj (_root_.PresheafOfModules.tensorBifunctor.{u, u, u, u, u}
      X.presheaf)).map
        (X := ((colimitPullback (opensMap f) X.presheaf).obj ((extendScalars f.hom.c).obj M),
          (colimitPullback (opensMap f) X.presheaf).obj ((extendScalars f.hom.c).obj N)))
        (Y := ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj M,
          (PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj N))
        (((PullbackColimit.pullbackIso f.hom.c).inv.app M),
        ((PullbackColimit.pullbackIso f.hom.c).inv.app N))) ((opensMap f).op.obj U)
      (Hom.app (objTensorIso (opensMap f) X.presheaf ((extendScalars f.hom.c).obj M)
          ((extendScalars f.hom.c).obj N)).hom ((opensMap f).op.obj U)
        (Hom.app ((colimitPullback (opensMap f) X.presheaf).map
            (extendScalarsTensorObjIso f.hom.c M N).hom) ((opensMap f).op.obj U)
          (Hom.app ((PullbackColimit.pullbackIso f.hom.c).hom.app (tensorObj M N))
            ((opensMap f).op.obj U) (preUnit f (tensorObj M N) U (x ⊗ₜ y))))) = _
  refine (_root_.PresheafOfModules.hom_congr_apply'
    (_root_.PresheafOfModules.tensorBifunctor_uncurry_map (O := X.presheaf)
      ((PullbackColimit.pullbackIso f.hom.c).inv.app M)
      ((PullbackColimit.pullbackIso f.hom.c).inv.app N)) ((opensMap f).op.obj U) _).trans ?_
  rw [pullbackIso_hom_preUnit f (tensorObj M N) U (x ⊗ₜ y)]
  rw [colimitPullback_map_germ_one (opensMap f) X.presheaf
      (extendScalarsTensorObjIso f.hom.c M N).hom (unitArrow f U)
      (tmul (f.hom.c.app U).hom 1 (x ⊗ₜ y) :
        ((extendScalars f.hom.c).obj (tensorObj M N)).obj U)]
  show Hom.app (tensorHom ((PullbackColimit.pullbackIso f.hom.c).inv.app M)
        ((PullbackColimit.pullbackIso f.hom.c).inv.app N)) ((opensMap f).op.obj U)
      (Hom.app (objTensorIso (opensMap f) X.presheaf ((extendScalars f.hom.c).obj M)
          ((extendScalars f.hom.c).obj N)).hom ((opensMap f).op.obj U)
        (germTmul (opensMap f) X.presheaf ((extendScalars f.hom.c).obj M)
          ((extendScalars f.hom.c).obj N) ((opensMap f).op.obj U) (unitArrow f U) 1
          (tmul (f.hom.c.app U).hom 1 x) (tmul (f.hom.c.app U).hom 1 y))) = _
  rw [objTensorIso_hom_germTmul (opensMap f) X.presheaf ((extendScalars f.hom.c).obj M)
      ((extendScalars f.hom.c).obj N) ((opensMap f).op.obj U) (unitArrow f U) 1
      (tmul (f.hom.c.app U).hom 1 x) (tmul (f.hom.c.app U).hom 1 y)]
  show Hom.app (tensorHom ((PullbackColimit.pullbackIso f.hom.c).inv.app M)
        ((PullbackColimit.pullbackIso f.hom.c).inv.app N)) ((opensMap f).op.obj U)
      (germ (opensMap f) X.presheaf ((extendScalars f.hom.c).obj M) (unitArrow f U) 1
          (tmul (f.hom.c.app U).hom 1 x) ⊗ₜ
        germ (opensMap f) X.presheaf ((extendScalars f.hom.c).obj N) (unitArrow f U) 1
          (tmul (f.hom.c.app U).hom 1 y)) = _
  rw [tensorHom_tmul ((PullbackColimit.pullbackIso f.hom.c).inv.app M)
      ((PullbackColimit.pullbackIso f.hom.c).inv.app N) ((opensMap f).op.obj U)
      (germ (opensMap f) X.presheaf ((extendScalars f.hom.c).obj M) (unitArrow f U) 1
        (tmul (f.hom.c.app U).hom 1 x))
      (germ (opensMap f) X.presheaf ((extendScalars f.hom.c).obj N) (unitArrow f U) 1
        (tmul (f.hom.c.app U).hom 1 y)),
    pullbackIso_inv_germ f M U x, pullbackIso_inv_germ f N U y]
  rfl

/-- The isomorphism `SheafOfModules.sheafificationCompPullback` carries the pullback-unit image
of the sheafification-unit image of `x ⊗ y` to the sheafification-unit image of the presheaf
pullback-unit image of `x ⊗ y`. -/
lemma sheafificationCompPullback_hom_pullbackUnit
    (A B : SheafOfModules.{u} (structureRingSheaf Y))
    (U : (Opens Y.carrier)ᵒᵖ) (x : A.val.obj U) (y : B.val.obj U) :
    Hom.app ((SheafOfModules.sheafificationCompPullback.{u}
          (structureSheafHom f)).hom.app (tensorObj A.val B.val)).val
        ((opensMap f).op.obj U)
        (pullbackUnit f (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
          ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B) U
          (Hom.app ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).unit.app
        (_root_.PresheafOfModules.tensorObj A.val B.val)) U (x ⊗ₜ y))) =
      shUnit X ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj
          (tensorObj A.val B.val)) ((opensMap f).op.obj U)
        (preUnit f (tensorObj A.val B.val) U (x ⊗ₜ y)) := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    ((PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf Y).obj)).comp
      (pullbackAdjunction f))
    ((PresheafOfModules.pullbackPushforwardAdjunction.{u} (structureSheafHom f).hom).comp
      (PresheafOfModules.sheafificationAdjunction (𝟙 (structureRingSheaf X).obj)))
    (tensorObj A.val B.val)
  exact PresheafOfModules.hom_congr_apply' h U (x ⊗ₜ y)

/-- The inverse of `SheafOfModules.pullbackIso` carries the sheafification-unit image of the
presheaf pullback-unit image of a section `m` to its sheaf pullback-unit image. -/
lemma sheafPullbackIso_inv_shUnit (M : SheafOfModules.{u} (structureRingSheaf Y))
    (U : (Opens Y.carrier)ᵒᵖ) (m : M.val.obj U) :
    Hom.app ((SheafOfModules.pullbackIso.{u} (structureSheafHom f)).inv.app M).val
        ((opensMap f).op.obj U)
        (shUnit X ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj M.val)
          ((opensMap f).op.obj U) (preUnit f M.val U m)) =
      pullbackUnit f M U m := by
  have h := Adjunction.unit_leftAdjointUniq_hom_app
    (SheafOfModules.PullbackConstruction.adjunction.{u} (structureSheafHom f))
    (pullbackAdjunction f) M
  exact SheafOfModules.hom_congr_app_apply h U m

variable (A B : SheafOfModules.{u} (structureRingSheaf Y))

/-- The four links of `pullbackTensorSheafObjIso`, read on sections. -/
lemma pullbackTensorSheafObjIso_hom_apply (V : (Opens X.carrier)ᵒᵖ)
    (z : ((pullbackFunctor f).obj (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B)).val.obj V) :
    Hom.app (pullbackTensorSheafObjIso f A B).hom.val V z =
      Hom.app ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩)).map
          (((SheafOfModules.pullbackIso.{u} (structureSheafHom f)).inv.app A,
              (SheafOfModules.pullbackIso.{u} (structureSheafHom f)).inv.app B) :
            (((PresheafOfModules.sheafification (𝟙 (structureRingSheaf X).obj)).obj
                ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj A.val),
              (PresheafOfModules.sheafification (𝟙 (structureRingSheaf X).obj)).obj
                ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj B.val)) :
                _ × _) ⟶ ((pullbackFunctor f).obj A, (pullbackFunctor f).obj B))).val V
        (Hom.app (sheafificationTensorObjIso X
            ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj A.val)
            ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj B.val)).hom.val V
          (Hom.app ((PresheafOfModules.sheafification
                (𝟙 (structureRingSheaf X).obj)).map
              ((pullbackTensorIso f.hom.c).hom.app (A.val, B.val))).val V
            (Hom.app ((SheafOfModules.sheafificationCompPullback.{u}
                (structureSheafHom f)).hom.app (tensorObj A.val B.val)).val V z))) := rfl

/-- The isomorphism `Stacks.PullbackTensor.pullbackTensorSheafObjIso` *is* the canonical
comparison morphism `Stacks.RingedSpace.comparison`. -/
theorem pullbackTensorSheafObjIso_hom_eq_comparison :
    (pullbackTensorSheafObjIso f A B).hom = comparison f A B := by
  refine comparison_unique f A B _ fun U x y => ?_
  refine (homEquiv_val_app f (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
      ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B)
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩).obj ((pullbackFunctor f).obj A)).obj ((pullbackFunctor f).obj B))
      (pullbackTensorSheafObjIso f A B).hom U
      (Hom.app ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).unit.app
        (_root_.PresheafOfModules.tensorObj A.val B.val)) U (x ⊗ₜ y))).trans ?_
  rw [pullbackTensorSheafObjIso_hom_apply f A B ((opensMap f).op.obj U)
      (pullbackUnit f (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨Y.presheaf, Y.IsSheaf⟩).obj A).obj B) U
        (Hom.app ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨Y.presheaf, Y.IsSheaf⟩).obj)).unit.app
        (_root_.PresheafOfModules.tensorObj A.val B.val)) U (x ⊗ₜ y)))]
  rw [sheafificationCompPullback_hom_pullbackUnit f A B U x y]
  refine Eq.trans (congrArg (Hom.app ((Functor.uncurry.obj
      (Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
        ⟨X.presheaf, X.IsSheaf⟩)).map _).val _)
      ((congrArg (Hom.app (sheafificationTensorObjIso X _ _).hom.val _)
        ((sheafification_map_shUnit X ((pullbackTensorIso f.hom.c).hom.app (A.val, B.val))
          ((opensMap f).op.obj U) (preUnit f (tensorObj A.val B.val) U (x ⊗ₜ y))).trans
          (congrArg (shUnit X _ _)
            (pullbackTensorIso_hom_preUnit_tmul f A.val B.val U x y)))).trans
      (sheafificationTensorObjIso_hom_shUnit_tmul X
        ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj A.val)
        ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj B.val)
        ((opensMap f).op.obj U) (preUnit f A.val U x) (preUnit f B.val U y)))) ?_
  refine Eq.trans (tensorSheaf_map_unit_tmul X
      ((SheafOfModules.pullbackIso.{u} (structureSheafHom f)).inv.app A)
      ((SheafOfModules.pullbackIso.{u} (structureSheafHom f)).inv.app B)
      ((opensMap f).op.obj U)
      (shUnit X ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj A.val)
        ((opensMap f).op.obj U) (preUnit f A.val U x))
      (shUnit X ((PresheafOfModules.pullback.{u} (structureSheafHom f).hom).obj B.val)
        ((opensMap f).op.obj U) (preUnit f B.val U y))) ?_
  refine congrArg (Hom.app ((PresheafOfModules.sheafificationAdjunction.{u, u, u, u}
      (R := Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩)
      (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ⟨X.presheaf, X.IsSheaf⟩).obj)).unit.app
        (_root_.PresheafOfModules.tensorObj ((pullbackFunctor f).obj A).val
          ((pullbackFunctor f).obj B).val)) ((opensMap f).op.obj U)) ?_
  exact congrArg₂ _ (sheafPullbackIso_inv_shUnit f A U x)
    (sheafPullbackIso_inv_shUnit f B U y)

/-- Every component of the canonical comparison `f^*(A ⊗ B) ⟶ f^*A ⊗ f^*B` is an
isomorphism. -/
instance isIso_comparison : IsIso (comparison f A B) := by
  rw [← pullbackTensorSheafObjIso_hom_eq_comparison]
  exact ⟨⟨(pullbackTensorSheafObjIso f A B).inv,
    (pullbackTensorSheafObjIso f A B).hom_inv_id,
    (pullbackTensorSheafObjIso f A B).inv_hom_id⟩⟩

/-- The component of `Stacks.RingedSpace.comparisonIso` at `(A, B)` is the composite
isomorphism `pullbackTensorSheafObjIso`. -/
theorem comparisonIso_hom_app :
    (comparisonIso f).hom.app (A, B) = (pullbackTensorSheafObjIso f A B).hom :=
  (pullbackTensorSheafObjIso_hom_eq_comparison f A B).symm

end Stacks.PullbackTensor
