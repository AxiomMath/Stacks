module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriek
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuous
public import StacksFrontier.CategoryTheory.Sites.Localization.AndMorphisms
public import Mathlib.CategoryTheory.GuitartExact.KanExtension

/-!
# Exchange of the canonical direct image of modules and restriction over a square of sites

Let
```
  C' --v'--> C
  |          |
  u'         u
  v          v
  D' --v---> D
```
be a commutative square of functors of sites, `u' ⋙ v = v' ⋙ u`, with `u`, `u'` cocontinuous and
`v`, `v'` continuous and cocontinuous, and assume the comparison functors
`{}^{u'}_{V'} I ⥤ {}^u_{v(V')} I` of Stacks 0FN1 are all cofinal. Fix sheaves of rings `O_C` on
`C` and `O_D` on `D` and a structure map `f^♯ : O_D ⟶ {}_su O_C`, and let
`O_{C'} = (g')^{-1} O_C`, `O_{D'} = g^{-1} O_D` be the restrictions along `v'` and `v`.

For the canonical direct images of `Stacks.SheafOfModules.pushforwardCocontinuous`, the
base-change transformation of right Kan extensions is `O_{D'}`-linear and gives an isomorphism of
the two composites of functors on sheaves of modules: the first conclusion of Stacks 0FN3.

## Main definitions

* `Stacks.SheafOfModules.structureMapSquare`: the structure map
  `(f')^♯ : O_{D'} ⟶ {}_su' O_{C'}` obtained from `f^♯` by restricting along `v` and applying the
  base-change isomorphism of Stacks 0FN1 for sheaves of rings.
* `Stacks.SheafOfModules.squareComparison`: the comparison
  `f_* ∘ g^* ⟶ (g')^* ∘ f'_*` of functors on sheaves of modules, whose underlying map of sheaves
  of abelian groups is the base-change transformation of right Kan extensions.

## Main results

* `Stacks.SheafOfModules.ranBaseChange_π`: the base-change transformation of right Kan extensions
  attached to a `2`-square, read on the legs of the limit cones: the leg of the target at
  `(a, ψ)` pulls back to the leg of the source at the image of `(a, ψ)` under the comparison
  functor of the square.
* `Stacks.SheafOfModules.inverseImageCompPushforwardCocontinuousIso`: the first conclusion of
  Stacks 0FN3 for the canonical direct images, as the inverse of `squareComparison`, with no
  hypothesis beyond the square, the cofinality and the structure map;
  `Stacks.SheafOfModules.nonempty_inverseImage_comp_pushforwardCocontinuous_iso` is the same
  asserted through `Nonempty`.

## References

* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3); the sheaf-level
  statement is Stacks 0FN1.
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v r v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅

namespace Stacks.SheafOfModules

section BaseChange

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄} {A : Type u₅}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄] [Category.{v₅} A]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄} (w : TwoSquare T L R B)
  [∀ F : C₁ ⥤ A, T.HasRightKanExtension F] [∀ F : C₃ ⥤ A, B.HasRightKanExtension F]

/-- The defining property of the base-change transformation of right Kan extensions attached to a
`2`-square: whiskered with `T` and followed by the counit of the right Kan extension along `T`,
it is the transformation that the square and the counit of the right Kan extension along `B`
produce. -/
lemma ranBaseChange_fac (F : C₃ ⥤ A) (X₁ : C₁) :
    (w.ranBaseChange.app F).app (T.obj X₁) ≫ (T.ranCounit.app (L ⋙ F)).app X₁
      = (B.ran.obj F).map (w.app X₁) ≫ (B.ranCounit.app F).app (L.obj X₁) := by
  have h := ((T.ranAdjunction A).homEquiv
      ((B.ran ⋙ (Functor.whiskeringLeft C₂ C₄ A).obj R).obj F)
      (((Functor.whiskeringLeft C₁ C₃ A).obj L).obj F)).symm_apply_apply
    (CostructuredArrow.hom
      ((Functor.RightExtension.mk (B.ran.obj F) (B.ranCounit.app F)).compTwoSquare w))
  rw [Adjunction.homEquiv_counit, Functor.ranAdjunction_counit, ← w.ranBaseChange_app] at h
  have := congr_app h X₁
  simpa using this

/-- **Base change on the legs of the limit cones.** The leg at `(a, ψ)` of the limit cone
computing the right Kan extension along `T` of `L ⋙ F`, pulled back along the base-change
transformation, is the leg at the image of `(a, ψ)` under the comparison functor of the square of
the limit cone computing the right Kan extension of `F` along `B`. -/
lemma ranBaseChange_π (F : C₃ ⥤ A) (X₂ : C₂) (j : StructuredArrow X₂ T) :
    (w.ranBaseChange.app F).app X₂ ≫ ranπ T (L ⋙ F) X₂ j
      = ranπ B F (R.obj X₂) (StructuredArrow.mk (R.map j.hom ≫ w.app j.right)) := by
  have hnat := (w.ranBaseChange.app F).naturality j.hom
  dsimp only [ranπ, Functor.comp_obj, Functor.comp_map, Functor.whiskeringLeft_obj_obj,
    Functor.whiskeringLeft_obj_map, StructuredArrow.mk_right, StructuredArrow.mk_hom_eq_self]
    at hnat ⊢
  rw [← Category.assoc, ← hnat, Category.assoc, ranBaseChange_fac, ← Functor.map_comp_assoc]

end BaseChange

section Square

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] {J' : GrothendieckTopology C'}
  {J : GrothendieckTopology C} {K' : GrothendieckTopology D'} {K : GrothendieckTopology D}
  {u' : C' ⥤ D'} {u : C ⥤ D} {v' : C' ⥤ C} {v : D' ⥤ D} [u.IsCocontinuous J K]
  [u'.IsCocontinuous J' K'] [v.IsContinuous K' K] [v.IsCocontinuous K' K]
  [v'.IsContinuous J' J] [v'.IsCocontinuous J' J]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{v}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ AddCommGrpCat.{v}, u'.op.HasPointwiseRightKanExtension G]
  [∀ G : Cᵒᵖ ⥤ RingCat.{r}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ RingCat.{r}, u'.op.HasPointwiseRightKanExtension G]
  {OC : Sheaf J RingCat.{r}} {OD : Sheaf K RingCat.{r}}

/-- The base-change transformation of Stacks 0FN1 for the sheaves of rings of the square, as a
morphism of presheaves of rings `v^p({}_su O_C) ⟶ {}_su' O_{C'}`. -/
def structureBaseChange (hsq : u' ⋙ v = v' ⋙ u) :
    v.op ⋙ u.op.ran.obj OC.obj ⟶ u'.op.ran.obj (inverseImageRing J' J v' OC).obj :=
  ((Stacks.Sites.CocontinuousExchange.twoSquare hsq).op.ranBaseChange
    (D := RingCat.{r})).app OC.obj

/-- The image of `(U', ψ)` under the comparison functor of the square, as an object of the index
category of the right Kan extension along `u.op` at `v.op(V')`. -/
abbrev squareIndex (hsq : u' ⋙ v = v' ⋙ u) {V' : D'ᵒᵖ} (j : StructuredArrow V' u'.op) :
    StructuredArrow (v.op.obj V') u.op :=
  StructuredArrow.mk (v.op.map j.hom ≫
    (Stacks.Sites.CocontinuousExchange.twoSquare hsq).op.app j.right)

omit [v'.IsCocontinuous J' J]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{v}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ AddCommGrpCat.{v}, u'.op.HasPointwiseRightKanExtension G] in
/-- `Stacks.SheafOfModules.ranBaseChange_π` for the sheaves of rings of the square. -/
lemma structureBaseChange_π (hsq : u' ⋙ v = v' ⋙ u) (V' : D'ᵒᵖ)
    (j : StructuredArrow V' u'.op) :
    (structureBaseChange (OC := OC) hsq).app V' ≫
        ranπ u'.op (inverseImageRing J' J v' OC).obj V' j
      = ranπ u.op OC.obj (v.op.obj V') (squareIndex hsq j) :=
  ranBaseChange_π _ OC.obj V' j

variable (fSharp : OD ⟶ (u.sheafPushforwardCocontinuous RingCat.{r} J K).obj OC)
  (hsq : u' ⋙ v = v' ⋙ u)

/-- The structure map `(f')^♯ : O_{D'} ⟶ {}_su' O_{C'}` of the left-hand column: the restriction
along `v` of `f^♯ : O_D ⟶ {}_su O_C`, followed by the base-change transformation of Stacks 0FN1
for sheaves of rings. -/
def structureMapSquare :
    inverseImageRing K' K v OD ⟶
      (u'.sheafPushforwardCocontinuous RingCat.{r} J' K').obj (inverseImageRing J' J v' OC) :=
  ObjectProperty.homMk (Functor.whiskerLeft v.op fSharp.hom ≫
    structureBaseChange (J' := J') (J := J) (OC := OC) hsq)

omit [v.IsCocontinuous K' K] [v'.IsCocontinuous J' J]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{v}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ AddCommGrpCat.{v}, u'.op.HasPointwiseRightKanExtension G] in
/-- The two ring maps through which a section of `O_{D'}` acts on the leg at `(U', ψ)` agree: the
one coming from `(f')^♯` and the leg of the Kan extension along `u'`, and the one coming from
`f^♯` and the leg of the Kan extension along `u` at the image of `(U', ψ)` under the comparison
functor of the square. -/
lemma scalarπ_square_apply (V' : D'ᵒᵖ) (j : StructuredArrow V' u'.op)
    (r : (inverseImageRing K' K v OD).obj.obj V') :
    (scalarπ u'
        (structureMapPresheaf u'
          (structureMapSquare (J' := J') (K' := K') fSharp hsq)) V' j).hom r
      = (scalarπ u (structureMapPresheaf u fSharp) (v.op.obj V') (squareIndex hsq j)).hom r :=
  ConcreteCategory.congr_hom (structureBaseChange_π hsq V' j)
    ((fSharp.hom.app (v.op.obj V')).hom r)

variable (M : _root_.SheafOfModules.{v} OC)

/-- The base-change transformation of Stacks 0FN1 for the sheaves of modules of the square, as a
morphism of presheaves of abelian groups `v^p({}_su M) ⟶ {}_su' ((v')^p M)`. -/
def squareComparisonPresheaf :
    v.op ⋙ u.op.ran.obj M.val.presheaf ⟶
      u'.op.ran.obj ((inverseImage.{v} J' J v' OC).obj M).val.presheaf :=
  ((Stacks.Sites.CocontinuousExchange.twoSquare hsq).op.ranBaseChange
    (D := AddCommGrpCat.{v})).app M.val.presheaf

/-- `squareComparisonPresheaf` at an object of `D'`, with its source and target written as values
of the two right Kan extensions. -/
def squareComparisonApp (V' : D'ᵒᵖ) :
    (u.op.ran.obj M.val.presheaf).obj (v.op.obj V') ⟶
      (u'.op.ran.obj ((inverseImage.{v} J' J v' OC).obj M).val.presheaf).obj V' :=
  (squareComparisonPresheaf hsq M).app V'

omit [∀ G : Cᵒᵖ ⥤ RingCat.{r}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ RingCat.{r}, u'.op.HasPointwiseRightKanExtension G] in
/-- `Stacks.SheafOfModules.ranBaseChange_π` for the sheaves of modules of the square. -/
lemma squareComparisonApp_π (V' : D'ᵒᵖ) (j : StructuredArrow V' u'.op) :
    squareComparisonApp hsq M V' ≫
        ranπ u'.op ((inverseImage.{v} J' J v' OC).obj M).val.presheaf V' j
      = ranπ u.op M.val.presheaf (v.op.obj V') (squareIndex hsq j) :=
  ranBaseChange_π _ M.val.presheaf V' j

omit [v.IsCocontinuous K' K]
  [∀ G : C'ᵒᵖ ⥤ AddCommGrpCat.{v}, u'.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ RingCat.{r}, u'.op.HasPointwiseRightKanExtension G] in
/-- `Stacks.SheafOfModules.ranSMul_π` for the right-hand column of the square, at the image of
`(U', ψ)` under the comparison functor. -/
lemma ranSMul_π_square (V' : D'ᵒᵖ) (r : (inverseImageRing K' K v OD).obj.obj V')
    (j : StructuredArrow V' u'.op) :
    ranSMul u (structureMapPresheaf u fSharp) M.val (v.op.obj V') r ≫
        ranπ u.op M.val.presheaf (v.op.obj V') (squareIndex hsq j)
      = ranπ u.op M.val.presheaf (v.op.obj V') (squareIndex hsq j) ≫
        smulPresheaf M.val (v'.op.obj j.right)
          ((scalarπ u (structureMapPresheaf u fSharp) (v.op.obj V')
            (squareIndex hsq j)).hom r) :=
  ranSMul_π u _ M.val (v.op.obj V') r _

omit [v.IsCocontinuous K' K]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{v}, u.op.HasPointwiseRightKanExtension G] in
/-- `Stacks.SheafOfModules.ranSMul_π` for the left-hand column of the square, with the scalar
written through `f^♯` by `scalarπ_square_apply`. -/
lemma ranSMul_π_inverseImage (V' : D'ᵒᵖ) (r : (inverseImageRing K' K v OD).obj.obj V')
    (j : StructuredArrow V' u'.op) :
    ranSMul u' (structureMapPresheaf u' (structureMapSquare (J' := J') (K' := K') fSharp hsq))
          ((inverseImage.{v} J' J v' OC).obj M).val V' r ≫
        ranπ u'.op ((inverseImage.{v} J' J v' OC).obj M).val.presheaf V' j
      = ranπ u'.op ((inverseImage.{v} J' J v' OC).obj M).val.presheaf V' j ≫
        smulPresheaf M.val (v'.op.obj j.right)
          ((scalarπ u (structureMapPresheaf u fSharp) (v.op.obj V')
            (squareIndex hsq j)).hom r) := by
  rw [ranSMul_π u' _ _ V' r j]
  congr 2
  exact scalarπ_square_apply fSharp hsq V' j r

omit [v.IsCocontinuous K' K] in
/-- **Base change is `O_{D'}`-linear.** Scalar multiplication by a section of `O_{D'}` commutes
with the base-change transformation. -/
lemma ranSMul_squareComparison (V' : D'ᵒᵖ) (r : (inverseImageRing K' K v OD).obj.obj V') :
    ranSMul u (structureMapPresheaf u fSharp) M.val (v.op.obj V') r ≫
        squareComparisonApp hsq M V'
      = squareComparisonApp hsq M V' ≫
        ranSMul u' (structureMapPresheaf u' (structureMapSquare (J' := J') (K' := K') fSharp hsq))
          ((inverseImage.{v} J' J v' OC).obj M).val V' r := by
  refine ran_hom_ext u'.op ((inverseImage.{v} J' J v' OC).obj M).val.presheaf (fun j => ?_)
  simp only [Category.assoc, ranSMul_π_inverseImage, squareComparisonApp_π]
  refine (ranSMul_π_square fSharp hsq M V' r j).trans ?_
  rw [← squareComparisonApp_π (J' := J') hsq M V' j]
  exact Category.assoc _ _ _

/-- The comparison `f_* ∘ g^* ⟶ (g')^* ∘ f'_*` at `M`, on underlying presheaves of modules: the
base-change transformation. -/
def squareComparisonVal :
    ((pushforwardCocontinuous.{v} u fSharp ⋙ inverseImage.{v} K' K v OD).obj M).val ⟶
      ((inverseImage.{v} J' J v' OC ⋙ pushforwardCocontinuous.{v} u'
        (structureMapSquare (J' := J') (K' := K') fSharp hsq)).obj M).val :=
  PresheafOfModules.homMk (squareComparisonPresheaf hsq M)
    (fun V' r m => ConcreteCategory.congr_hom (ranSMul_squareComparison fSharp hsq M V' r) m)

/-- **The comparison of the two composites on sheaves of modules**,
`f_* ∘ g^* ⟶ (g')^* ∘ f'_*`, whose underlying map of sheaves of abelian groups is the
base-change transformation of right Kan extensions of Stacks 0FN1. -/
def squareComparison :
    pushforwardCocontinuous.{v} u fSharp ⋙ inverseImage.{v} K' K v OD ⟶
      inverseImage.{v} J' J v' OC ⋙ pushforwardCocontinuous.{v} u'
        (structureMapSquare (J' := J') (K' := K') fSharp hsq) where
  app N := ⟨squareComparisonVal fSharp hsq N⟩
  naturality N₁ N₂ φ := by
    refine _root_.SheafOfModules.hom_ext ?_
    refine (PresheafOfModules.toPresheaf _).map_injective ?_
    exact ((Stacks.Sites.CocontinuousExchange.twoSquare hsq).op.ranBaseChange
      (D := AddCommGrpCat.{v})).naturality (presheafMap φ.val)

end Square

section Iso

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] {J' : GrothendieckTopology C'}
  {J : GrothendieckTopology C} {K' : GrothendieckTopology D'} {K : GrothendieckTopology D}
  {u' : C' ⥤ D'} {u : C ⥤ D} {v' : C' ⥤ C} {v : D' ⥤ D} [u.IsCocontinuous J K]
  [u'.IsCocontinuous J' K'] [v.IsContinuous K' K] [v.IsCocontinuous K' K]
  [v'.IsContinuous J' J] [v'.IsCocontinuous J' J]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{v}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ AddCommGrpCat.{v}, u'.op.HasPointwiseRightKanExtension G]
  [∀ G : Cᵒᵖ ⥤ RingCat.{r}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ RingCat.{r}, u'.op.HasPointwiseRightKanExtension G]
  {OC : Sheaf J RingCat.{r}} {OD : Sheaf K RingCat.{r}}
  (fSharp : OD ⟶ (u.sheafPushforwardCocontinuous RingCat.{r} J K).obj OC)
  (hsq : u' ⋙ v = v' ⋙ u)
  (hfinal : ∀ V' : D',
    (CostructuredArrow.map₂ (S := u') (T := V') (U := u) (V := v.obj V') (F := v') (G := v)
      (eqToHom hsq.symm) (𝟙 (v.obj V'))).Final)

include hfinal in
/-- Every component of the comparison `Stacks.SheafOfModules.squareComparison` is an
isomorphism. -/
lemma isIso_squareComparison_app (M : _root_.SheafOfModules.{v} OC) :
    IsIso ((squareComparison (J' := J') (K' := K') fSharp hsq).app M) := by
  have hge := Stacks.Sites.CocontinuousExchange.guitartExact_twoSquare_mk hsq hfinal
  have h1 : IsIso (squareComparisonPresheaf (J' := J') hsq M) :=
    inferInstanceAs (IsIso (((Stacks.Sites.CocontinuousExchange.twoSquare hsq).op.ranBaseChange
      (D := AddCommGrpCat.{v})).app M.val.presheaf))
  have h2 : IsIso ((sheafToPresheaf K' AddCommGrpCat.{v}).map
      ((_root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD)).map
        ((squareComparison (J' := J') (K' := K') fSharp hsq).app M))) := h1
  have h3 : IsIso ((_root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD)).map
      ((squareComparison (J' := J') (K' := K') fSharp hsq).app M)) :=
    isIso_of_reflects_iso _ (sheafToPresheaf K' AddCommGrpCat.{v})
  exact isIso_of_reflects_iso _
    (_root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD))

include hfinal in
/-- **Exchange of direct image and restriction for the canonical direct images.** For a
commutative square of ringed topoi as in the module docstring, with the direct images of sheaves
of modules along the cocontinuous `u` and `u'` the canonical ones of
`Stacks.SheafOfModules.pushforwardCocontinuous`, the isomorphism
`f'_* ∘ (g')^* ≅ g^* ∘ f_*` on sheaves of modules, inverse to
`Stacks.SheafOfModules.squareComparison`. -/
def inverseImageCompPushforwardCocontinuousIso :
    inverseImage.{v} J' J v' OC ⋙ pushforwardCocontinuous.{v} u'
        (structureMapSquare (J' := J') (K' := K') fSharp hsq) ≅
      pushforwardCocontinuous.{v} u fSharp ⋙ inverseImage.{v} K' K v OD := by
  have h : ∀ M, IsIso ((squareComparison (J' := J') (K' := K') fSharp hsq).app M) :=
    fun M => isIso_squareComparison_app (J' := J') (K' := K') fSharp hsq hfinal M
  have : IsIso (squareComparison (J' := J') (K' := K') fSharp hsq) :=
    NatIso.isIso_of_isIso_app _
  exact (asIso (squareComparison (J' := J') (K' := K') fSharp hsq)).symm

include hfinal in
/-- `Stacks.SheafOfModules.inverseImageCompPushforwardCocontinuousIso` asserted through
`Nonempty`: the two composites are isomorphic. -/
theorem nonempty_inverseImage_comp_pushforwardCocontinuous_iso :
    Nonempty (inverseImage.{v} J' J v' OC ⋙ pushforwardCocontinuous.{v} u'
        (structureMapSquare (J' := J') (K' := K') fSharp hsq) ≅
      pushforwardCocontinuous.{v} u fSharp ⋙ inverseImage.{v} K' K v OD) :=
  ⟨inverseImageCompPushforwardCocontinuousIso fSharp hsq hfinal⟩

end Iso

end Stacks.SheafOfModules

end
