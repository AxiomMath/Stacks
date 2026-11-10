module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousSquare
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The module comparison of a square of sites, from objectwise bijectivity on sheaves of sets

Let
```
  C' --v'--> C
  |          |
  u'         u
  v          v
  D' --v---> D
```
be a commutative square of functors of sites, with `u`, `u'` cocontinuous and `v`, `v'`
continuous and cocontinuous, and let `f_*`, `f'_*` be the canonical direct images of sheaves of
modules along `u` and `u'` (`Stacks.SheafOfModules.pushforwardCocontinuous`).
`Stacks.SheafOfModules.squareComparison` is the comparison `f_* ∘ g^* ⟶ (g')^* ∘ f'_*` of the
two composites, linear over the structure sheaf; its underlying map of presheaves of abelian
groups is the base-change transformation of right Kan extensions of **Stacks 0FN1**.
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PushforwardCocontinuousSquare.lean` proves it
invertible when the square is Guitart exact, that is, when the comparison functors of the index
categories are cofinal.

That cofinality fails for the squares of **Stacks 07AT**: there the base change is invertible
only on *sheaves*, by a local-factorization argument which the library carries out on sheaves of
sets, objectwise (`CategoryTheory.SubsitePushforward.bijective_subsiteRanBaseChange_app_app`).
This file proves that such an objectwise statement on sheaves of sets suffices: if, for every
sheaf of modules `M`, the base-change transformation of right Kan extensions is invertible at
every object for the underlying presheaf of *sets* of `M`, then `squareComparison` is an
isomorphism.

## Main results

* `Stacks.SheafOfModules.ranCompIsoOfPreserves`: the value of a pointwise right Kan extension
  commutes with a functor that preserves the limit computing it, compatibly with the legs.
* `Stacks.SheafOfModules.isIso_map_ranBaseChange_app_app_iff`: the base-change transformation
  of right Kan extensions at an object is invertible after applying such a functor if and only if
  the base-change transformation of the composite is invertible there.
* `Stacks.SheafOfModules.isIso_squareComparison_of_forget`: `squareComparison` is an isomorphism
  as soon as its sets-level counterpart is invertible at every object, for every sheaf of
  modules.

## References

* [Stacks Project, Tag 0FN1](https://stacks.math.columbia.edu/tag/0FN1)
* [Stacks Project, Tag 0FN3](https://stacks.math.columbia.edu/tag/0FN3)
* [Stacks Project, Tag 07AT](https://stacks.math.columbia.edu/tag/07AT)
-/

@[expose] public noncomputable section

open CategoryTheory Limits Opposite

universe v r v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v₅ u₅ v₆ u₆

namespace Stacks.SheafOfModules

section Preserves

variable {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B] (L : A ⥤ B)
  {H : Type u₃} [Category.{v₃} H] {H' : Type u₄} [Category.{v₄} H'] (G : H ⥤ H')
  [∀ F : A ⥤ H, L.HasPointwiseRightKanExtension F]
  [∀ F : A ⥤ H', L.HasPointwiseRightKanExtension F]
  (N : A ⥤ H)

/-- **The value of a pointwise right Kan extension commutes with a functor preserving the limit
computing it**: `G((Ran_L N)(b)) ≅ (Ran_L (N ⋙ G))(b)`, the two being limits of the same
diagram. -/
def ranCompIsoOfPreserves (b : B) [PreservesLimit (StructuredArrow.proj b L ⋙ N) G] :
    G.obj ((L.ran.obj N).obj b) ≅ (L.ran.obj (N ⋙ G)).obj b :=
  letI : PreservesLimit (StructuredArrow.proj b L ⋙ (𝟭 (A ⥤ H)).obj N) G :=
    ‹PreservesLimit (StructuredArrow.proj b L ⋙ N) G›
  IsLimit.conePointUniqueUpToIso (isLimitOfPreserves G (ranIsLimit L N b))
    (ranIsLimit L (N ⋙ G) b)

/-- The comparison `ranCompIsoOfPreserves` carries `G` of a leg to the corresponding leg. -/
@[reassoc]
lemma ranCompIsoOfPreserves_hom_ranπ (b : B) [PreservesLimit (StructuredArrow.proj b L ⋙ N) G]
    (j : StructuredArrow b L) :
    (ranCompIsoOfPreserves L G N b).hom ≫ ranπ L (N ⋙ G) b j = G.map (ranπ L N b j) :=
  let : PreservesLimit (StructuredArrow.proj b L ⋙ (𝟭 (A ⥤ H)).obj N) G :=
    ‹PreservesLimit (StructuredArrow.proj b L ⋙ N) G›
  IsLimit.conePointUniqueUpToIso_hom_comp (isLimitOfPreserves G (ranIsLimit L N b))
    (ranIsLimit L (N ⋙ G) b) j

end Preserves

section BaseChange

variable {C₁ : Type u₁} {C₂ : Type u₂} {C₃ : Type u₃} {C₄ : Type u₄}
  [Category.{v₁} C₁] [Category.{v₂} C₂] [Category.{v₃} C₃] [Category.{v₄} C₄]
  {T : C₁ ⥤ C₂} {L : C₁ ⥤ C₃} {R : C₂ ⥤ C₄} {B : C₃ ⥤ C₄} (w : TwoSquare T L R B)
  {H : Type u₅} [Category.{v₅} H] {H' : Type u₆} [Category.{v₆} H'] (G : H ⥤ H')
  [∀ F : C₁ ⥤ H, T.HasPointwiseRightKanExtension F]
  [∀ F : C₃ ⥤ H, B.HasPointwiseRightKanExtension F]
  [∀ F : C₁ ⥤ H', T.HasPointwiseRightKanExtension F]
  [∀ F : C₃ ⥤ H', B.HasPointwiseRightKanExtension F]

/-- The base-change transformation of right Kan extensions commutes with a functor preserving
the limits computing the two Kan extensions, through `ranCompIsoOfPreserves`. -/
lemma map_ranBaseChange_app_app_comp (F : C₃ ⥤ H) (X₂ : C₂)
    [PreservesLimit (StructuredArrow.proj X₂ T ⋙ (L ⋙ F)) G]
    [PreservesLimit (StructuredArrow.proj (R.obj X₂) B ⋙ F) G] :
    G.map ((w.ranBaseChange.app F).app X₂) ≫ (ranCompIsoOfPreserves T G (L ⋙ F) X₂).hom =
      (ranCompIsoOfPreserves B G F (R.obj X₂)).hom ≫
        (w.ranBaseChange.app (F ⋙ G)).app X₂ := by
  refine ran_hom_ext T ((L ⋙ F) ⋙ G) (fun j => ?_)
  have e1 := ranCompIsoOfPreserves_hom_ranπ T G (L ⋙ F) X₂ j
  have e2 := ranBaseChange_π w F X₂ j
  have e3 : (w.ranBaseChange.app (F ⋙ G)).app X₂ ≫ ranπ T ((L ⋙ F) ⋙ G) X₂ j =
      ranπ B (F ⋙ G) (R.obj X₂)
        (StructuredArrow.mk (R.map j.hom ≫ w.app j.right)) :=
    ranBaseChange_π w (F ⋙ G) X₂ j
  have e4 := ranCompIsoOfPreserves_hom_ranπ B G F (R.obj X₂)
    (StructuredArrow.mk (R.map j.hom ≫ w.app j.right))
  simp only [Category.assoc, e1, e3, e4, ← G.map_comp, e2]

/-- **The base-change transformation of right Kan extensions is invertible after applying a
functor preserving the relevant limits exactly when the base-change transformation of the
composite is.** -/
theorem isIso_map_ranBaseChange_app_app_iff (F : C₃ ⥤ H) (X₂ : C₂)
    [PreservesLimit (StructuredArrow.proj X₂ T ⋙ (L ⋙ F)) G]
    [PreservesLimit (StructuredArrow.proj (R.obj X₂) B ⋙ F) G] :
    IsIso (G.map ((w.ranBaseChange.app F).app X₂)) ↔
      IsIso ((w.ranBaseChange.app (F ⋙ G)).app X₂) := by
  rw [← isIso_comp_left_iff (ranCompIsoOfPreserves B G F (R.obj X₂)).hom,
    ← map_ranBaseChange_app_app_comp w G F X₂, isIso_comp_right_iff]

end BaseChange

section Restriction

variable {X : Type u₁} [Category.{v₁} X] {Y : Type u₂} [Category.{v₂} Y]
  (JX : GrothendieckTopology X) (JY : GrothendieckTopology Y) (w : X ⥤ Y)
  [w.IsContinuous JX JY] [w.IsCocontinuous JX JY]
  [∀ F : Xᵒᵖ ⥤ AddCommGrpCat.{v}, w.op.HasPointwiseRightKanExtension F]
  [∀ F : Xᵒᵖ ⥤ RingCat.{r}, w.op.HasPointwiseRightKanExtension F]
  (O : Sheaf JY RingCat.{r})

/-- The **tautological structure map** `O_Y ⟶ {}_sw (w^{-1}O_Y)` of the morphism of ringed topoi
attached to a continuous and cocontinuous functor of sites `w`, when the source carries the
restricted sheaf of rings: the unit of the right Kan extension adjunction. -/
def ranUnitSheaf :
    O ⟶ (w.sheafPushforwardCocontinuous RingCat.{r} JX JY).obj (inverseImageRing JX JY w O) :=
  ObjectProperty.homMk (ranUnitRing w O.obj)

/-- **Restriction of sheaves of modules is left adjoint to the canonical direct image** along a
continuous and cocontinuous functor of sites, for the restricted sheaf of rings and the
tautological structure map: the adjunction of presheaves of modules
`Stacks.SheafOfModules.pushforward₀RanPushforwardAdjunction`, restricted to sheaves. -/
@[sga "4 III 2.4" "special case"]
def inverseImagePushforwardCocontinuousAdjunction :
    inverseImage.{v} JX JY w O ⊣ pushforwardCocontinuous.{v} w (ranUnitSheaf JX JY w O) :=
  (pushforward₀RanPushforwardAdjunction.{v} w O.obj).restrictFullyFaithful
    (_root_.SheafOfModules.fullyFaithfulForget O)
    (_root_.SheafOfModules.fullyFaithfulForget (inverseImageRing JX JY w O))
    (L := inverseImage.{v} JX JY w O)
    (R := pushforwardCocontinuous.{v} w (ranUnitSheaf JX JY w O))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))
    (NatIso.ofComponents (fun _ => Iso.refl _) (fun _ => rfl))

/-- The structure map `O_Y ⟶ {}_sw O_X` of the morphism of ringed topoi attached to a continuous
and cocontinuous functor of sites `w`, when `O_X` is *equal* to the restriction of `O_Y`: the unit
of the right Kan extension adjunction, transported along that equality. -/
def fSharpOfEq {OX : Sheaf JX RingCat.{r}} (h : OX.obj = w.op ⋙ O.obj) :
    O ⟶ (w.sheafPushforwardCocontinuous RingCat.{r} JX JY).obj OX :=
  ObjectProperty.homMk (ranUnitRing w O.obj ≫ w.op.ran.map (eqToHom h.symm))

/-- **Restriction of sheaves of modules is left adjoint to the canonical direct image**, for a
sheaf of rings on the source equal to the restriction of the one on the target: restriction is
`SheafOfModules.pushforward` along the identification, and the direct image is the canonical one
for the structure map `Stacks.SheafOfModules.fSharpOfEq`. -/
def pushforwardPushforwardCocontinuousAdjunction {OX : Sheaf JX RingCat.{r}}
    (h : OX.obj = w.op ⋙ O.obj) :
    _root_.SheafOfModules.pushforward.{v} (F := w)
        (ObjectProperty.homMk (eqToHom h) :
          OX ⟶ (w.sheafPushforwardContinuous RingCat.{r} JX JY).obj O) ⊣
      pushforwardCocontinuous.{v} w (fSharpOfEq JX JY w O h) := by
  obtain ⟨S, hS⟩ := OX
  change S = w.op ⋙ O.obj at h
  subst h
  have e : fSharpOfEq JX JY w O (OX := ⟨w.op ⋙ O.obj, hS⟩) rfl = ranUnitSheaf JX JY w O :=
    ObjectProperty.hom_ext _
      ((whisker_eq _ (w.op.ran.map_id (w.op ⋙ O.obj))).trans (Category.comp_id _))
  rw [e]
  exact inverseImagePushforwardCocontinuousAdjunction JX JY w O

end Restriction

/-- The structure map of the left-hand column induced by `fSharp` acts on the legs of the limit
cones through `fSharp` and the legs of the right-hand column, at the image of the leg under the
comparison functor of the square. -/
private lemma structureMapSquare_hom_app_ranπ {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂}
    [Category.{v₂} C] {D' : Type u₃} [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D]
    {J' : GrothendieckTopology C'} {J : GrothendieckTopology C} {K' : GrothendieckTopology D'}
    {K : GrothendieckTopology D} {u' : C' ⥤ D'} {u : C ⥤ D} {v' : C' ⥤ C} {v : D' ⥤ D}
    [u.IsCocontinuous J K] [u'.IsCocontinuous J' K'] [v.IsContinuous K' K]
    [v'.IsContinuous J' J] [u.IsContinuous J K]
    [∀ G : Cᵒᵖ ⥤ RingCat.{r}, u.op.HasPointwiseRightKanExtension G]
    [∀ G : C'ᵒᵖ ⥤ RingCat.{r}, u'.op.HasPointwiseRightKanExtension G]
    {OC : Sheaf J RingCat.{r}} {OD : Sheaf K RingCat.{r}}
    (fSharp : OD ⟶ (u.sheafPushforwardCocontinuous RingCat.{r} J K).obj OC)
    (hsq : u' ⋙ v = v' ⋙ u) (V' : D'ᵒᵖ) (j : StructuredArrow V' u'.op) :
    (structureMapSquare (J' := J') (K' := K') fSharp hsq).hom.app V' ≫
        ranπ u'.op (inverseImageRing J' J v' OC).obj V' j =
      fSharp.hom.app (v.op.obj V') ≫ ranπ u.op OC.obj (v.op.obj V') (squareIndex hsq j) :=
  (Category.assoc _ _ _).trans
    (whisker_eq _ (structureBaseChange_π (J' := J') (J := J) (OC := OC) hsq V' j))

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
  [∀ G : Cᵒᵖ ⥤ Type v, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ Type v, u'.op.HasPointwiseRightKanExtension G]
  [∀ V : Dᵒᵖ, PreservesLimitsOfShape (StructuredArrow V u.op) (forget AddCommGrpCat.{v})]
  [∀ V' : D'ᵒᵖ, PreservesLimitsOfShape (StructuredArrow V' u'.op) (forget AddCommGrpCat.{v})]
  {OC : Sheaf J RingCat.{r}} {OD : Sheaf K RingCat.{r}}
  (fSharp : OD ⟶ (u.sheafPushforwardCocontinuous RingCat.{r} J K).obj OC)
  (hsq : u' ⋙ v = v' ⋙ u)

omit [v.IsCocontinuous K' K] [v'.IsCocontinuous J' J]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{v}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ AddCommGrpCat.{v}, u'.op.HasPointwiseRightKanExtension G]
  [∀ G : Cᵒᵖ ⥤ Type v, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ Type v, u'.op.HasPointwiseRightKanExtension G]
  [∀ V : Dᵒᵖ, PreservesLimitsOfShape (StructuredArrow V u.op) (forget AddCommGrpCat.{v})]
  [∀ V' : D'ᵒᵖ, PreservesLimitsOfShape (StructuredArrow V' u'.op) (forget AddCommGrpCat.{v})] in
/-- The structure map of the left-hand column induced by the tautological structure map of the
right-hand column acts on the legs of the limit cones through the restriction maps of `O_D`,
at the image of the leg under the comparison functor of the square. -/
lemma structureMapSquare_ranUnitSheaf_ranπ [u.IsContinuous J K] (O : Sheaf K RingCat.{r})
    (V' : D'ᵒᵖ) (j : StructuredArrow V' u'.op) :
    (structureMapSquare (J' := J') (K' := K') (ranUnitSheaf J K u O) hsq).hom.app V' ≫
        ranπ u'.op (inverseImageRing J' J v' (inverseImageRing J K u O)).obj V' j =
      O.obj.map (squareIndex hsq j).hom := by
  refine (structureMapSquare_hom_app_ranπ (J' := J') (K' := K') (ranUnitSheaf J K u O) hsq
    V' j).trans ?_
  exact ranAdjunction_unit_app_ranπ u.op O.obj _ _

omit [v.IsCocontinuous K' K] [v'.IsCocontinuous J' J]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{v}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ AddCommGrpCat.{v}, u'.op.HasPointwiseRightKanExtension G]
  [∀ G : Cᵒᵖ ⥤ Type v, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ Type v, u'.op.HasPointwiseRightKanExtension G]
  [∀ V : Dᵒᵖ, PreservesLimitsOfShape (StructuredArrow V u.op) (forget AddCommGrpCat.{v})]
  [∀ V' : D'ᵒᵖ, PreservesLimitsOfShape (StructuredArrow V' u'.op) (forget AddCommGrpCat.{v})] in
/-- **The structure map induced on the left-hand column by a tautological one is tautological.**
If `O_C` is the restriction of `O_D` along `u` and the right-hand column carries the transported
unit `Stacks.SheafOfModules.fSharpOfEq`, then the structure map
`Stacks.SheafOfModules.structureMapSquare` it induces on the left-hand column is again the
transported unit, for the restrictions along `v'` and `v` of the two sheaves of rings. -/
lemma structureMapSquare_fSharpOfEq [u.IsContinuous J K] [u'.IsContinuous J' K']
    (hC : OC.obj = u.op ⋙ OD.obj)
    (h' : (inverseImageRing J' J v' OC).obj = u'.op ⋙ (inverseImageRing K' K v OD).obj) :
    structureMapSquare (J' := J') (K' := K') (fSharpOfEq J K u OD hC) hsq =
      fSharpOfEq J' K' u' (inverseImageRing K' K v OD) h' := by
  refine ObjectProperty.hom_ext _ (NatTrans.ext (funext fun V' => ?_))
  refine ran_hom_ext u'.op (inverseImageRing J' J v' OC).obj (fun j => ?_)
  have hL := structureMapSquare_hom_app_ranπ (J' := J') (K' := K') (fSharpOfEq J K u OD hC)
    hsq V' j
  have hR : (fSharpOfEq J' K' u' (inverseImageRing K' K v OD) h').hom.app V' ≫
        ranπ u'.op (inverseImageRing J' J v' OC).obj V' j =
      (ranUnitRing u' (inverseImageRing K' K v OD).obj).app V' ≫
        ((u'.op.ran.map (eqToHom h'.symm)).app V' ≫
          ranπ u'.op (inverseImageRing J' J v' OC).obj V' j) :=
    Category.assoc _ _ _
  refine hL.trans (Eq.trans ?_ hR.symm)
  change (ranUnitRing u OD.obj).app (v.op.obj V') ≫ ((u.op.ran.map (eqToHom hC.symm)).app
    (v.op.obj V') ≫ ranπ u.op OC.obj (v.op.obj V') (squareIndex hsq j)) = _
  rw [ranπ_map_functor, ranπ_map_functor, ← Category.assoc, ← Category.assoc]
  have a1 : (ranUnitRing u OD.obj).app (v.op.obj V') ≫
      ranπ u.op (u.op ⋙ OD.obj) (v.op.obj V') (squareIndex hsq j) =
        OD.obj.map (squareIndex hsq j).hom :=
    ranAdjunction_unit_app_ranπ u.op OD.obj _ _
  have a2 : (ranUnitRing u' (inverseImageRing K' K v OD).obj).app V' ≫
      ranπ u'.op (u'.op ⋙ (inverseImageRing K' K v OD).obj) V' j =
        (inverseImageRing K' K v OD).obj.map j.hom :=
    ranAdjunction_unit_app_ranπ u'.op _ _ _
  rw [a1, a2]
  simp only [eqToHom_app, squareIndex, StructuredArrow.mk_hom_eq_self, Functor.map_comp,
    Category.assoc, NatTrans.op_app, eqToHom_op, eqToHom_map,
    eqToHom_trans]
  rfl

/-- **The comparison of the two composites is invertible as soon as its sets-level counterpart
is invertible at every object.** If, for every sheaf of `O_C`-modules `M` and every object `V'`
of `D'`, the base-change transformation of right Kan extensions of the square is invertible at
`V'` for the underlying presheaf of sets of `M`, then
`f_* ∘ g^* ⟶ (g')^* ∘ f'_*` is an isomorphism of functors on sheaves of modules.

The underlying map of presheaves of abelian groups of the comparison is the base-change
transformation of right Kan extensions of abelian presheaves; the forgetful functor to sets
preserves the limits computing those Kan extensions, so by
`Stacks.SheafOfModules.isIso_map_ranBaseChange_app_app_iff` its underlying map of sets is the
sets-level base change, up to isomorphism; and the forgetful functors from abelian groups to
sets, from presheaves to sheaves and from modules to abelian sheaves reflect isomorphisms. -/
theorem isIso_squareComparison_of_forget
    (H : ∀ (M : _root_.SheafOfModules.{v} OC) (V' : D'ᵒᵖ),
      IsIso ((((Stacks.Sites.CocontinuousExchange.twoSquare hsq).op.ranBaseChange
        (D := Type v)).app (M.val.presheaf ⋙ forget AddCommGrpCat.{v})).app V')) :
    IsIso (squareComparison (J' := J') (K' := K') fSharp hsq) := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro M
  have h1 : IsIso (squareComparisonPresheaf (J' := J') hsq M) := by
    rw [NatTrans.isIso_iff_isIso_app]
    intro V'
    have : IsIso ((forget AddCommGrpCat.{v}).map
        ((squareComparisonPresheaf (J' := J') hsq M).app V')) :=
      (isIso_map_ranBaseChange_app_app_iff
        (Stacks.Sites.CocontinuousExchange.twoSquare hsq).op (forget AddCommGrpCat.{v})
        M.val.presheaf V').2 (H M V')
    exact isIso_of_reflects_iso _ (forget AddCommGrpCat.{v})
  have h2 : IsIso ((sheafToPresheaf K' AddCommGrpCat.{v}).map
      ((_root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD)).map
        ((squareComparison (J' := J') (K' := K') fSharp hsq).app M))) := h1
  have h3 : IsIso ((_root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD)).map
      ((squareComparison (J' := J') (K' := K') fSharp hsq).app M)) :=
    isIso_of_reflects_iso _ (sheafToPresheaf K' AddCommGrpCat.{v})
  exact isIso_of_reflects_iso _ (_root_.SheafOfModules.toSheaf.{v} (inverseImageRing K' K v OD))

/-- **`g'_! ∘ (f')^{-1} ≅ f^{-1} ∘ g_!` for restriction, from objectwise bijectivity on sheaves of
sets.** In a commutative square of sites as above in which `u` and `u'` are continuous as well,
with `O_C` the restriction of `O_D` along `u` and `O_{C'} = (v')^{-1}O_C` the restriction of
`O_{D'} = v^{-1}O_D` along `u'`, let `f^{-1}` and `(f')^{-1}` be restriction of sheaves of modules
along `u` and `u'`, and let `g_!`, `g'_!` be any left adjoints of the inverse images `g^*`,
`(g')^*` along `v` and `v'`. If the base-change transformation of right Kan extensions of the
square is invertible at every object for the underlying presheaf of sets of every sheaf of
`O_C`-modules, then `g'_! ∘ (f')^{-1} ≅ f^{-1} ∘ g_!`.

Both composites are left adjoints, of `f'_* ∘ (g')^*` and of `g^* ∘ f_*` for the canonical direct
images, which `Stacks.SheafOfModules.isIso_squareComparison_of_forget` identifies; the structure
map of `f'_*` is the one `Stacks.SheafOfModules.structureMapSquare` produces, by
`Stacks.SheafOfModules.structureMapSquare_fSharpOfEq`. -/
def restrictionCompLowerShriekIso [u.IsContinuous J K] [u'.IsContinuous J' K']
    (hC : OC.obj = u.op ⋙ OD.obj)
    (h' : (inverseImageRing J' J v' OC).obj = u'.op ⋙ (inverseImageRing K' K v OD).obj)
    {Lg : _root_.SheafOfModules.{v} (inverseImageRing K' K v OD) ⥤ _root_.SheafOfModules.{v} OD}
    {Lg' : _root_.SheafOfModules.{v} (inverseImageRing J' J v' OC) ⥤ _root_.SheafOfModules.{v} OC}
    (adj : Lg ⊣ inverseImage.{v} K' K v OD) (adj' : Lg' ⊣ inverseImage.{v} J' J v' OC)
    (H : ∀ (M : _root_.SheafOfModules.{v} OC) (V' : D'ᵒᵖ),
      IsIso ((((Stacks.Sites.CocontinuousExchange.twoSquare hsq).op.ranBaseChange
        (D := Type v)).app (M.val.presheaf ⋙ forget AddCommGrpCat.{v})).app V')) :
    _root_.SheafOfModules.pushforward.{v} (F := u')
        (ObjectProperty.homMk (eqToHom h') : inverseImageRing J' J v' OC ⟶
          (u'.sheafPushforwardContinuous RingCat.{r} J' K').obj (inverseImageRing K' K v OD)) ⋙
        Lg' ≅
      Lg ⋙ _root_.SheafOfModules.pushforward.{v} (F := u)
        (ObjectProperty.homMk (eqToHom hC) : OC ⟶
          (u.sheafPushforwardContinuous RingCat.{r} J K).obj OD) := by
  have hiso := isIso_squareComparison_of_forget (J' := J') (K' := K')
    (fSharpOfEq J K u OD hC) hsq H
  have e := congrArg (fun φ => pushforwardCocontinuous.{v} u' φ)
    (structureMapSquare_fSharpOfEq (J' := J') (K' := K') hsq hC h')
  let σ : pushforwardCocontinuous.{v} u (fSharpOfEq J K u OD hC) ⋙ inverseImage.{v} K' K v OD ≅
      inverseImage.{v} J' J v' OC ⋙
        pushforwardCocontinuous.{v} u' (fSharpOfEq J' K' u' (inverseImageRing K' K v OD) h') :=
    asIso (squareComparison (J' := J') (K' := K') (fSharpOfEq J K u OD hC) hsq) ≪≫
      Functor.isoWhiskerLeft _ (eqToIso e)
  exact ((pushforwardPushforwardCocontinuousAdjunction J' K' u'
      (inverseImageRing K' K v OD) h').comp adj').leftAdjointUniq
    ((adj.comp (pushforwardPushforwardCocontinuousAdjunction J K u OD hC)).ofNatIsoRight σ)

end Square

end Stacks.SheafOfModules

end
