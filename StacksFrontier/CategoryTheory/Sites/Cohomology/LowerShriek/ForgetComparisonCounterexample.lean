module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.LowerShriek.ForgetComparisonCriterionFromContinuity
public import StacksFrontier.CategoryTheory.Sites.Cohomology.CompactObjects.ExtensionByZeroUnitAtTerminal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LowerShriekForgetLocalized
public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal
import StacksCore.Tactic.StacksAttribute

/-!
# The derived lower shrieks need not commute with forgetting, even when `g_! = g_!^{Ab}`

Let `u : C ⥤ D` be a continuous and cocontinuous functor of sites, `g` the corresponding morphism
of topoi, `O_D` a sheaf of rings on `D` and `O_C = g^{-1} O_D`, as in Stacks 07AC. The warning of
Stacks 07AE says that in general the square

```
D(O_C) --Lg_!--> D(O_D)
  |                 |
forget            forget
  v                 v
D(C) --Lg_!^{Ab}--> D(D)
```

does not commute, and that this can happen even if `g_! = g_!^{Ab}`. The comparison
transformation of the warning and its criterion are
`Stacks.Cohomology.DerivedLowerShriek.existsUnique_derivedForgetComparison_of_continuous` and
`Stacks.Cohomology.DerivedLowerShriek.isIso_derivedForgetComparison_iff`; this file proves the
remaining claim, by an example.

## The example

`C` is the cospan category `left ⟶ one ⟵ right`, `D` is `Bool` ordered by `false ≤ true`, both
with the trivial topology, and `u` sends the two legs to `false ≤ true`. The sheaf of rings `O_D`
is `ℤ` at `true` and the zero ring at `false`, so `O_C` is `ℤ` at `one` and zero at `left` and
`right`.

* *`g_! = g_!^{Ab}`.* Every `O_C`-module vanishes at `left` and `right`, so `g_!^{Ab}` of its
  underlying abelian sheaf vanishes at `false` (the left Kan extension there is the pushout of
  `M(left) ← M(one) → M(right)`), and so does every `O_D`-module. At `true` the left Kan extension
  is `M(one)`, the index category having a terminal object, so the unit of `g_!^{Ab} ⊣ g^{-1}` is
  invertible at `one`. By the criterion of Stacks 0798 it suffices to check the comparison at the
  `j_{U!}O_U`: those for `U = left, right` vanish, and `j_{one!}O_one = O_C`, where the
  comparison followed by the canonical `g_! O_C ⟶ O_D` (invertible because `u` is final) is the
  counit of `g_!^{Ab} ⊣ g^{-1}` at `O_D`, which is invertible by the two computations above.
* *`Lg_! ≠ Lg_!^{Ab}`.* `Lg_!^{Ab}(O_C)` at `false` is the homotopy pushout of `0 ← ℤ → 0`, with
  `H^{-1} = ℤ`, while `Lg_!(O_C) = O_D` vanishes at `false`. In the form used here: if the two
  composites agreed at `j_{one!}O_one[0]`, then `Ext^1(O_C, g^{-1}I)` would vanish for every
  injective abelian sheaf `I` on `D` (the argument of
  `Stacks.Cohomology.DerivedLowerShriek.extAcyclic_forget_extensionByZeroUnit`). For `I` the
  right adjoint of evaluation at `false` applied to `ℚ`, the extension of `O_C` by `g^{-1}I`
  whose restriction along `one ⟶ right` is twisted by a nonzero map `ℤ ⟶ I(false)` does not
  split, so `Ext^1(O_C, g^{-1}I) ≠ 0`.

## Main results

* `DerivedLowerShriek.exists_isIso_forgetComparison_not_isIso_derivedForgetComparison`:
  **Stacks 07AE**, the warning.
* `DerivedLowerShriek.ForgetCounterexample.isIso_forgetComparison`: `g_! = g_!^{Ab}` in the
  example.
* `DerivedLowerShriek.ForgetCounterexample.not_isIso_derivedForgetComparison` and
  `DerivedLowerShriek.ForgetCounterexample.not_nonempty_iso`: the derived comparison is not
  invertible, and the two composites are not isomorphic at all.

## References

* [Stacks Project, Tag 07AE](https://stacks.math.columbia.edu/tag/07AE)
* [Stacks Project, Tag 07AC](https://stacks.math.columbia.edu/tag/07AC)
* [Stacks Project, Tag 0798](https://stacks.math.columbia.edu/tag/0798)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian Opposite

namespace Stacks.Cohomology.DerivedLowerShriek.ForgetCounterexample

/-- The functor of sites of the counterexample. -/
abbrev u : WalkingCospan ⥤ Bool :=
  cospan (homOfLE (show false ≤ true by decide)) (homOfLE (show false ≤ true by decide))

/-- The trivial topology on the cospan category. -/
abbrev J : GrothendieckTopology WalkingCospan := ⊥

/-- The trivial topology on `Bool`. -/
abbrev K : GrothendieckTopology Bool := ⊥

/-- `u` is continuous: every presheaf is a sheaf for the trivial topology. -/
instance u_isContinuous : u.IsContinuous J K := ⟨fun _ => Presieve.isSheaf_bot⟩

/-- `u` is cocontinuous: the only covering sieves are maximal. -/
instance u_isCocontinuous : u.IsCocontinuous J K := by
  refine ⟨fun hS => ?_⟩
  obtain rfl := GrothendieckTopology.bot_covering.mp hS
  exact GrothendieckTopology.bot_covering.mpr (Sieve.functorPullback_top u _)

/-- `one` is a terminal object of the cospan category. -/
def isTerminalOne : IsTerminal (WalkingCospan.one) :=
  IsTerminal.ofUniqueHom
    (fun j => match j with
      | none => 𝟙 _
      | some k => WidePullbackShape.Hom.term k)
    (fun _ _ => Subsingleton.elim _ _)

/-- `true` is a terminal object of `Bool`. -/
def isTerminalTrue : IsTerminal (true : Bool) :=
  IsTerminal.ofUniqueHom (fun b => homOfLE (by cases b <;> decide))
    (fun _ _ => Subsingleton.elim _ _)

/-- `u` is final: it sends the terminal object `one` to the terminal object `true`. -/
instance u_final : u.Final := by
  have := Functor.final_fromPUnit_of_isTerminal isTerminalOne
  have : (Functor.fromPUnit.{0} WalkingCospan.one ⋙ u).Final :=
    Functor.final_fromPUnit_of_isTerminal isTerminalTrue
  exact Functor.final_of_final_comp (Functor.fromPUnit.{0} WalkingCospan.one) u

/-- The opposite of the cospan category is thin. -/
lemma op_hom_ext {X Y : WalkingCospanᵒᵖ} (f g : X ⟶ Y) : f = g :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

/-- The opposite of `Bool` is thin. -/
lemma op_hom_ext' {X Y : Boolᵒᵖ} (f g : X ⟶ Y) : f = g :=
  Quiver.Hom.unop_inj (Subsingleton.elim _ _)

/-- Every object of the index category of the left Kan extension at `true` lies over `one`. -/
lemma trueIndex_left (Y : CostructuredArrow u.op (u.op.obj (op WalkingCospan.one))) :
    Y.left = op WalkingCospan.one := by
  rcases Y with ⟨⟨c⟩, _, f⟩
  rcases c with _ | ⟨_ | _⟩
  · rfl
  all_goals exact absurd (leOfHom f.unop : (true : Bool) ≤ false) (by decide)

/-- The index category of the left Kan extension at `true` has `(one, 𝟙)` as terminal object. -/
def trueIndexTerminal :
    IsTerminal (CostructuredArrow.mk (𝟙 (u.op.obj (op WalkingCospan.one)))) :=
  IsTerminal.ofUniqueHom
    (fun Y => CostructuredArrow.homMk (eqToHom (trueIndex_left Y)) (op_hom_ext' _ _))
    (fun _ _ => CostructuredArrow.hom_ext _ _ (op_hom_ext _ _))

variable (X : WalkingCospanᵒᵖ ⥤ AddCommGrpCat.{0})

/-- The unit of the left Kan extension along `u.op` is invertible at `one`. -/
instance isIso_lanUnit_app_one : IsIso ((u.op.lanUnit.app X).app (op WalkingCospan.one)) := by
  have := (Functor.isPointwiseLeftKanExtensionLeftKanExtensionUnit u.op X
    (u.op.obj (op WalkingCospan.one))).isIso_ι_app_of_isTerminal _ trueIndexTerminal
  change IsIso ((u.op.leftKanExtensionUnit X).app (op WalkingCospan.one))
  simpa using this

/-- A colimit all of whose injections vanish is zero. -/
lemma isZero_colimit_of_ι_eq_zero {I : Type*} [Category I] (G : I ⥤ AddCommGrpCat.{0})
    [HasColimit G] (h : ∀ i, colimit.ι G i = 0) : IsZero (colimit G) := by
  rw [IsZero.iff_id_eq_zero]
  exact colimit.hom_ext fun i => by simp [h i]

/-- The left Kan extension along `u.op` vanishes at `false` as soon as the presheaf vanishes at
`left` and `right`: the colimit computing it is the pushout of `X(left) ← X(one) → X(right)`. -/
lemma isZero_lan_obj_false (hl : IsZero (X.obj (op WalkingCospan.left)))
    (hr : IsZero (X.obj (op WalkingCospan.right))) :
    IsZero ((u.op.lan.obj X).obj (op false)) := by
  refine IsZero.of_iso ?_ (u.op.leftKanExtensionObjIsoColimit X (op false))
  apply isZero_colimit_of_ι_eq_zero
  rintro ⟨⟨c⟩, ⟨⟩, f⟩
  rcases c with _ | ⟨_ | _⟩
  · let j' : CostructuredArrow u.op (op false) :=
      CostructuredArrow.mk (Y := op WalkingCospan.left) (𝟙 (op false))
    let φ : (CostructuredArrow.mk (Y := op WalkingCospan.one) f) ⟶ j' :=
      CostructuredArrow.homMk WalkingCospan.Hom.inl.op (op_hom_ext' _ _)
    have : colimit.ι (CostructuredArrow.proj u.op (op false) ⋙ X) j' = 0 := hl.eq_of_src _ _
    refine (colimit.w (CostructuredArrow.proj u.op (op false) ⋙ X) φ).symm.trans ?_
    rw [this, comp_zero]
  · exact hl.eq_of_src _ _
  · exact hr.eq_of_src _ _

/-! ### The sheaf of rings -/

/-- `u` preserves the pullbacks of a cofinal family of coverings for the trivial topology `J`. -/
instance u_preservesCoveringPullbacks : Stacks.Sites.PreservesCoveringPullbacks J u where
  exists_cover U S hS := by
    refine ⟨Presieve.singleton (𝟙 U), ?_, ?_, ?_⟩
    · have : Sieve.generate (Presieve.singleton (𝟙 U)) = ⊤ :=
        Sieve.id_mem_iff_eq_top.mp
          (Sieve.le_generate (Presieve.singleton (𝟙 U)) U (𝟙 U) (Presieve.singleton_self _))
      rw [this]
      exact GrothendieckTopology.top_mem _ _
    · obtain rfl := GrothendieckTopology.bot_covering.mp hS
      intro _ _ _
      trivial
    · rintro V f ⟨⟩ W g
      exact ⟨hasPullback_of_left_iso _ _, inferInstance⟩

/-- The presheaf of rings `O_D` of the counterexample: `ℤ` at `true`, the zero ring at `false`. -/
def ringPresheaf : Boolᵒᵖ ⥤ CommRingCat.{0} where
  obj X := match X.unop with
    | false => CommRingCat.of PUnit
    | true => CommRingCat.of ℤ
  map := by
    intro X Y f
    cases X with
    | op x =>
      cases Y with
      | op y =>
        cases x <;> cases y
        · exact 𝟙 _
        · exact absurd (f.unop.down.down : (true : Bool) ≤ false) (by decide)
        · exact CommRingCat.ofHom (Int.castRingHom PUnit)
        · exact 𝟙 _
  map_id := by
    intro X
    cases X with
    | op x => cases x <;> rfl
  map_comp := by
    intro X Y Z f g
    cases X with
    | op x =>
      cases Y with
      | op y =>
        cases Z with
        | op z =>
          cases x <;> cases y <;> cases z
          case op.op.op.false.true.false =>
            exact absurd (f.unop.down.down : (true : Bool) ≤ false) (by decide)
          case op.op.op.true.false.true =>
            exact absurd (g.unop.down.down : (true : Bool) ≤ false) (by decide)
          all_goals first | rfl | (ext x; simp)

/-- The sheaf of commutative rings `O_D` of the counterexample. -/
def O : Sheaf K CommRingCat.{0} := ⟨ringPresheaf, Presheaf.isSheaf_bot _⟩

/-- `O_D`, as a sheaf of rings. -/
abbrev OD : Sheaf K RingCat.{0} := Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O

/-- `O_C = g^{-1} O_D`. -/
abbrev OC : Sheaf J RingCat.{0} := inverseImageRing J K u OD

/-- `O_D(false)` is the zero ring. -/
instance subsingleton_OD_false : Subsingleton (OD.obj.obj (op false)) := by
  change Subsingleton PUnit
  infer_instance

/-- Every `O_D`-module vanishes at `false`. -/
instance subsingleton_OD_module_false (N : SheafOfModules.{0} OD) :
    Subsingleton (N.val.obj (op false)) :=
  Module.subsingleton (OD.obj.obj (op false)) _

/-- `O_C(left)` is the zero ring. -/
instance subsingleton_OC_left : Subsingleton (OC.obj.obj (op WalkingCospan.left)) := by
  change Subsingleton PUnit
  infer_instance

/-- `O_C(right)` is the zero ring. -/
instance subsingleton_OC_right : Subsingleton (OC.obj.obj (op WalkingCospan.right)) := by
  change Subsingleton PUnit
  infer_instance

/-- Every `O_C`-module vanishes at `left`. -/
instance subsingleton_OC_module_left (N : SheafOfModules.{0} OC) :
    Subsingleton (N.val.obj (op WalkingCospan.left)) :=
  Module.subsingleton (OC.obj.obj (op WalkingCospan.left)) _

/-- Every `O_C`-module vanishes at `right`. -/
instance subsingleton_OC_module_right (N : SheafOfModules.{0} OC) :
    Subsingleton (N.val.obj (op WalkingCospan.right)) :=
  Module.subsingleton (OC.obj.obj (op WalkingCospan.right)) _

attribute [local instance] HasDerivedCategory.standard
  isRightAdjoint_sourceSliceRestriction isRightAdjoint_targetSliceRestriction
  isLeftDerivedFunctor_derivedLowerShriek_comp_forget_of_continuous

/-! ### Lower shriek of abelian sheaves at the two points of `Bool` -/

/-- The unit of Mathlib's construction of lower shriek of abelian sheaves (left Kan extension,
then sheafification), at `one`. -/
lemma constructionUnit_app_one (H : Sheaf J AddCommGrpCat.{0}) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u AddCommGrpCat.{0} J K).unit.app
        H).hom.app (op WalkingCospan.one) =
      (u.op.lanUnit.app H.obj).app (op WalkingCospan.one) ≫
        (toSheafify K (u.op.lan.obj H.obj)).app (op true) := by
  have h := Adjunction.map_restrictFullyFaithful_unit_app
    (L := Functor.sheafPullbackConstruction.sheafPullback u AddCommGrpCat.{0} J K)
    (R := u.sheafPushforwardContinuous AddCommGrpCat.{0} J K)
    ((u.op.lanAdjunction AddCommGrpCat.{0}).comp (sheafificationAdjunction K AddCommGrpCat.{0}))
    (fullyFaithfulSheafToPresheaf J AddCommGrpCat.{0}) (Functor.FullyFaithful.id _)
    (Iso.refl _) (Iso.refl _) H
  have h' := congrArg (fun f => NatTrans.app f (op WalkingCospan.one)) h
  refine h'.trans ?_
  simp only [Adjunction.comp_unit_app, Functor.lanAdjunction_unit,
    sheafificationAdjunction_unit_app, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app,
    Functor.comp_map, Functor.whiskeringLeft_obj_map, Functor.id_obj]
  rfl

/-- **The unit of `g_!^{Ab} ⊣ g^{-1}` is invertible at `one`**: the index category of the left
Kan extension at `true = u(one)` has `(one, 𝟙)` as a terminal object, and sheafification for the
trivial topology is invertible. -/
instance isIso_abelianUnit_app_one (H : Sheaf J AddCommGrpCat.{0}) :
    IsIso (((u.sheafAdjunctionContinuous AddCommGrpCat.{0} J K).unit.app H).hom.app
      (op WalkingCospan.one)) := by
  have h := congrArg (fun f => f.hom.app (op WalkingCospan.one))
    (Adjunction.unit_leftAdjointUniq_hom_app (u.sheafAdjunctionContinuous AddCommGrpCat.{0} J K)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u AddCommGrpCat.{0} J K) H)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app] at h
  have hs : IsIso (toSheafify K (u.op.lan.obj H.obj)) :=
    isIso_toSheafify K (Presheaf.isSheaf_bot _)
  have h1 : IsIso (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous u
      AddCommGrpCat.{0} J K).unit.app H).hom.app (op WalkingCospan.one)) := by
    rw [constructionUnit_app_one]
    have h3 := isIso_lanUnit_app_one H.obj
    have h4 : IsIso ((toSheafify K (u.op.lan.obj H.obj)).app (op true)) :=
      @NatIso.isIso_app_of_isIso _ _ _ _ _ _ (toSheafify K (u.op.lan.obj H.obj)) hs (op true)
    exact IsIso.comp_isIso' h3 h4
  have h2 : IsIso (((u.sheafPushforwardContinuous AddCommGrpCat.{0} J K).map
      ((Functor.sheafPullbackConstruction.sheafPullbackIso u AddCommGrpCat.{0} J K).hom.app
        H)).hom.app (op WalkingCospan.one)) := by
    have : IsIso ((sheafToPresheaf J AddCommGrpCat.{0}).map
        ((u.sheafPushforwardContinuous AddCommGrpCat.{0} J K).map
          ((Functor.sheafPullbackConstruction.sheafPullbackIso u AddCommGrpCat.{0} J K).hom.app
            H))) := inferInstance
    exact NatIso.isIso_app_of_isIso _ _
  exact IsIso.of_isIso_fac_right h

/-- **`g_!^{Ab} H` vanishes at `false` when `H` vanishes at `left` and `right`.** -/
lemma isZero_abelianLowerShriek_obj_false (H : Sheaf J AddCommGrpCat.{0})
    (hl : IsZero (H.obj.obj (op WalkingCospan.left)))
    (hr : IsZero (H.obj.obj (op WalkingCospan.right))) :
    IsZero (((u.sheafPullback AddCommGrpCat.{0} J K).obj H).obj.obj (op false)) := by
  have : IsIso (toSheafify K (u.op.lan.obj H.obj)) := isIso_toSheafify K (Presheaf.isSheaf_bot _)
  exact IsZero.of_iso (isZero_lan_obj_false H.obj hl hr)
    (((sheafToPresheaf K AddCommGrpCat.{0}).mapIso
      ((Functor.sheafPullbackConstruction.sheafPullbackIso u AddCommGrpCat.{0} J K).app H)).app
        (op false) ≪≫ (asIso ((toSheafify K (u.op.lan.obj H.obj)).app (op false))).symm)

/-- **The counit of `g_!^{Ab} ⊣ g^{-1}` is invertible at an abelian sheaf vanishing at
`false`.** At `true` it is inverse to the unit at `one` by the triangle identity; at `false`
both sides vanish. -/
lemma isIso_abelianCounit_app (A : Sheaf K AddCommGrpCat.{0})
    (hA : IsZero (A.obj.obj (op false))) :
    IsIso ((u.sheafAdjunctionContinuous AddCommGrpCat.{0} J K).counit.app A) := by
  let adj := u.sheafAdjunctionContinuous AddCommGrpCat.{0} J K
  rw [← isIso_iff_of_reflects_iso _ (sheafToPresheaf K AddCommGrpCat.{0}),
    NatTrans.isIso_iff_isIso_app]
  rintro ⟨b⟩
  cases b
  · have h1 : IsZero (((u.sheafPullback AddCommGrpCat.{0} J K).obj
        ((u.sheafPushforwardContinuous AddCommGrpCat.{0} J K).obj A)).obj.obj (op false)) :=
      isZero_abelianLowerShriek_obj_false _ hA hA
    exact ⟨⟨0, h1.eq_of_src _ _, hA.eq_of_src _ _⟩⟩
  · have h := congrArg (fun f => f.hom.app (op WalkingCospan.one))
      (adj.right_triangle_components A)
    simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
      ObjectProperty.FullSubcategory.id_hom, NatTrans.id_app] at h
    have e := IsIso.inv_eq_of_hom_inv_id h
    show IsIso (((u.sheafPushforwardContinuous AddCommGrpCat.{0} J K).map
      (adj.counit.app A)).hom.app (op WalkingCospan.one))
    rw [← e]
    infer_instance

/-! ### `g_! = g_!^{Ab}` -/

/-- A natural transformation is invertible at an object at which both functors vanish. -/
lemma isIso_app_of_isZero {A B : Type*} [Category A] [Category B] [HasZeroMorphisms B]
    {F G : A ⥤ B} (c : F ⟶ G) {X : A} (hF : IsZero (F.obj X)) (hG : IsZero (G.obj X)) :
    IsIso (c.app X) :=
  ⟨⟨0, hF.eq_of_src _ _, hG.eq_of_src _ _⟩⟩

/-- `j_{left!}O_left = 0`: its morphisms to `N` are the sections `N(left) = 0`. -/
lemma isZero_extensionByZeroUnit_left :
    IsZero (Stacks.SheafOfModules.extensionByZeroUnit.{0, 0, 0, 0} OC WalkingCospan.left) := by
  rw [IsZero.iff_id_eq_zero]
  exact (Stacks.SheafOfModules.extensionByZeroUnitHomEquiv.{0, 0, 0, 0} OC _ _).injective
    (Subsingleton.elim _ _)

/-- `j_{right!}O_right = 0`: its morphisms to `N` are the sections `N(right) = 0`. -/
lemma isZero_extensionByZeroUnit_right :
    IsZero (Stacks.SheafOfModules.extensionByZeroUnit.{0, 0, 0, 0} OC WalkingCospan.right) := by
  rw [IsZero.iff_id_eq_zero]
  exact (Stacks.SheafOfModules.extensionByZeroUnitHomEquiv.{0, 0, 0, 0} OC _ _).injective
    (Subsingleton.elim _ _)

/-- The comparison of Stacks 0798 is invertible at a zero module. -/
lemma isIso_forgetComparison_app_of_isZero {M : SheafOfModules.{0} OC} (hM : IsZero M) :
    IsIso ((forgetComparison J K u OD).app M) :=
  isIso_app_of_isZero _ (Functor.map_isZero _ hM) (Functor.map_isZero _ hM)

/-- The underlying abelian sheaf of an `O_D`-module vanishes at `false`. -/
lemma isZero_toSheaf_obj_false (N : SheafOfModules.{0} OD) :
    IsZero (((SheafOfModules.toSheaf OD).obj N).obj.obj (op false)) :=
  @AddCommGrpCat.isZero_of_subsingleton _ (subsingleton_OD_module_false N)

/-- The comparison of Stacks 0798 is invertible at `O_C`: followed by the canonical map
`g_! O_C ⟶ O_D` (invertible, `u` being final) it is the counit of `g_!^{Ab} ⊣ g^{-1}` at `O_D`
precomposed with the identification `O_C = g^{-1} O_D`. -/
instance isIso_forgetComparison_app_unit :
    IsIso ((forgetComparison J K u OD).app (SheafOfModules.unit OC)) := by
  let adj := u.sheafAdjunctionContinuous AddCommGrpCat.{0} J K
  let k := (forgetComparison J K u OD).app (SheafOfModules.unit OC) ≫
    (SheafOfModules.toSheaf OD).map (SheafOfModules.pullbackObjUnitToUnit (idRingMap J K u OD))
  let t : (forgetSourceModules J K u OD).obj (SheafOfModules.unit OC) ⟶
      (u.sheafPushforwardContinuous AddCommGrpCat.{0} J K).obj
        ((SheafOfModules.toSheaf OD).obj (SheafOfModules.unit OD)) :=
    (SheafOfModules.toSheaf OC).map
      (SheafOfModules.unitToPushforwardObjUnit (idRingMap J K u OD))
  have hk : adj.homEquiv _ _ k = t := by
    rw [Adjunction.homEquiv_naturality_right]
    refine (congrArg (· ≫ (u.sheafPushforwardContinuous AddCommGrpCat.{0} J K).map
      ((SheafOfModules.toSheaf OD).map
        (SheafOfModules.pullbackObjUnitToUnit (idRingMap J K u OD))))
      (Stacks.SheafOfModules.lowerShriekForgetComparison_homEquiv u (idRingMap J K u OD)
        (SheafOfModules.unit OC))).trans ?_
    change (SheafOfModules.toSheaf OC).map
        ((SheafOfModules.pullbackPushforwardAdjunction (idRingMap J K u OD)).unit.app
          (SheafOfModules.unit OC)) ≫
        (SheafOfModules.toSheaf OC).map ((SheafOfModules.pushforward (idRingMap J K u OD)).map
          (SheafOfModules.pullbackObjUnitToUnit (idRingMap J K u OD))) = _
    exact (Functor.map_comp _ _ _).symm.trans (congrArg (SheafOfModules.toSheaf OC).map
      (((SheafOfModules.pullbackPushforwardAdjunction (idRingMap J K u OD)).homEquiv_unit
        _ _ _).symm.trans
        (SheafOfModules.pullbackPushforwardAdjunction_homEquiv_pullbackObjUnitToUnit _)))
  have hk' : k = (u.sheafPullback AddCommGrpCat.{0} J K).map t ≫ adj.counit.app _ :=
    (((adj.homEquiv _ _).symm_apply_apply k).symm.trans
      (congrArg (adj.homEquiv _ _).symm hk)).trans (adj.homEquiv_counit _ _ _)
  have := isIso_abelianCounit_app _ (isZero_toSheaf_obj_false (SheafOfModules.unit OD))
  have : IsIso (SheafOfModules.unitToPushforwardObjUnit (idRingMap J K u OD)) :=
    Stacks.SheafOfModules.isIso_unitToPushforwardObjUnit _
  have ht : IsIso t := Functor.map_isIso (SheafOfModules.toSheaf OC) _
  have hkk : IsIso k := by
    rw [hk']
    infer_instance
  have : IsIso ((SheafOfModules.toSheaf OD).map
      (SheafOfModules.pullbackObjUnitToUnit (idRingMap J K u OD))) := inferInstance
  exact IsIso.of_isIso_comp_right _ ((SheafOfModules.toSheaf OD).map
      (SheafOfModules.pullbackObjUnitToUnit (idRingMap J K u OD)))

/-- `j_{one!} O_one ≅ O_C`, `one` being terminal. -/
def extensionByZeroUnitOneIso :
    Stacks.SheafOfModules.extensionByZeroUnit.{0, 0, 0, 0} OC WalkingCospan.one ≅
      SheafOfModules.unit OC :=
  Stacks.SheafOfModules.extensionByZeroUnitSpellingIso OC WalkingCospan.one ≪≫
    Stacks.Sites.ExtensionByZero.extensionByZeroUnitIsoUnitOfTerminal J OC WalkingCospan.one
      isTerminalOne

/-- **`g_! = g_!^{Ab}` in the counterexample**: the comparison of Stacks 0798 is an
isomorphism. -/
theorem isIso_forgetComparison : IsIso (forgetComparison J K u OD) := by
  rw [Stacks.SheafOfModules.isIso_lowerShriekForgetComparison_iff]
  rintro (_ | ⟨_ | _⟩)
  · exact (NatTrans.isIso_app_iff_of_iso _ extensionByZeroUnitOneIso).mpr inferInstance
  · exact isIso_forgetComparison_app_of_isZero isZero_extensionByZeroUnit_left
  · exact isIso_forgetComparison_app_of_isZero isZero_extensionByZeroUnit_right

/-! ### A non-split extension of presheaves on the cospan category -/

section Twisted

variable (A B : WalkingCospanᵒᵖ ⥤ AddCommGrpCat.{0})
  (φ : A.obj (op WalkingCospan.one) ⟶ B.obj (op WalkingCospan.right))

/-- The twisting cocycle: `φ` on the leg `one ⟶ right`, zero elsewhere. -/
def twist : (c d : WalkingCospanᵒᵖ) → (A.obj c →+ B.obj d)
  | ⟨none⟩, ⟨some WalkingPair.right⟩ => φ.hom
  | _, _ => 0

/-- The cocycle vanishes on identities. -/
lemma twist_self (c : WalkingCospanᵒᵖ) : twist A B φ c c = 0 := by
  rcases c with ⟨_ | ⟨_ | _⟩⟩ <;> rfl

/-- There is no morphism `one ⟶ left` in the cospan category. -/
lemma not_hom_left_one (f : op WalkingCospan.left ⟶ op WalkingCospan.one) : False := by
  nomatch f.unop

/-- There is no morphism `one ⟶ right` in the cospan category. -/
lemma not_hom_right_one (f : op WalkingCospan.right ⟶ op WalkingCospan.one) : False := by
  nomatch f.unop

/-- There is no morphism `right ⟶ left` in the cospan category. -/
lemma not_hom_left_right (f : op WalkingCospan.left ⟶ op WalkingCospan.right) : False := by
  nomatch f.unop

/-- There is no morphism `left ⟶ right` in the cospan category. -/
lemma not_hom_right_left (f : op WalkingCospan.right ⟶ op WalkingCospan.left) : False := by
  nomatch f.unop

/-- The extension `0 → B → E → A → 0` of presheaves on the cospan category whose restriction along
`one ⟶ right` is twisted by `φ`: `E(c) = A(c) × B(c)`, with restriction
`(x, q) ↦ (A(f) x, B(f) q + τ_f(x))`. -/
def twisted : WalkingCospanᵒᵖ ⥤ AddCommGrpCat.{0} where
  obj c := AddCommGrpCat.of (A.obj c × B.obj c)
  map {c d} f := AddCommGrpCat.ofHom (((A.map f).hom.comp (AddMonoidHom.fst _ _)).prod
    ((B.map f).hom.comp (AddMonoidHom.snd _ _) + (twist A B φ c d).comp (AddMonoidHom.fst _ _)))
  map_id c := by
    ext ⟨x, q⟩
    · simp
    · simp [twist_self]
  map_comp {c d e} f g := by
    ext ⟨x, q⟩
    · simp
    · rcases c with ⟨_ | ⟨_ | _⟩⟩ <;> rcases d with ⟨_ | ⟨_ | _⟩⟩ <;>
        rcases e with ⟨_ | ⟨_ | _⟩⟩ <;>
        first
        | exact (not_hom_left_one f).elim | exact (not_hom_right_one f).elim
        | exact (not_hom_left_right f).elim | exact (not_hom_right_left f).elim
        | exact (not_hom_left_one g).elim | exact (not_hom_right_one g).elim
        | exact (not_hom_left_right g).elim | exact (not_hom_right_left g).elim
        | (obtain rfl : f = 𝟙 _ := op_hom_ext _ _; simp [twist])
        | (obtain rfl : g = 𝟙 _ := op_hom_ext _ _; simp [twist])

/-- The restriction maps of the twisted extension. -/
lemma twisted_map_apply {c d : WalkingCospanᵒᵖ} (f : c ⟶ d) (w : (twisted A B φ).obj c) :
    (twisted A B φ).map f w = (A.map f w.1, B.map f w.2 + twist A B φ c d w.1) := rfl

/-- The inclusion `B ⟶ E`. -/
def twistedι : B ⟶ twisted A B φ where
  app c := AddCommGrpCat.ofHom (AddMonoidHom.inr _ _)
  naturality c d f := by
    ext q
    refine Prod.ext ?_ ?_
    · change (0 : A.obj d) = A.map f 0
      exact (map_zero _).symm
    · change B.map f q = B.map f q + twist A B φ c d 0
      rw [map_zero, add_zero]

/-- The projection `E ⟶ A`. -/
def twistedπ : twisted A B φ ⟶ A where
  app c := AddCommGrpCat.ofHom (AddMonoidHom.fst _ _)
  naturality c d f := by
    ext w
    rfl

/-- The short complex `0 → B → E → A → 0`. -/
@[simps]
def twistedSC : ShortComplex (WalkingCospanᵒᵖ ⥤ AddCommGrpCat.{0}) where
  f := twistedι A B φ
  g := twistedπ A B φ
  zero := by
    ext c q
    rfl

/-- Pointwise, the twisted extension splits. -/
def twistedSplitting (c : WalkingCospanᵒᵖ) :
    ((twistedSC A B φ).map ((evaluation _ _).obj c)).Splitting where
  r := AddCommGrpCat.ofHom (AddMonoidHom.snd _ _)
  s := AddCommGrpCat.ofHom (AddMonoidHom.inl _ _)
  f_r := by ext q; rfl
  s_g := by ext x; rfl
  id := by
    ext ⟨x, q⟩
    change ((0 : A.obj c), q) + (x, (0 : B.obj c)) = (x, q)
    simp

/-- The twisted extension is a short exact sequence: it is so pointwise, where it splits. -/
lemma twistedSC_shortExact : (twistedSC A B φ).ShortExact := by
  have h : ∀ c, ((twistedSC A B φ).map ((evaluation _ _).obj c)).ShortExact :=
    fun c => (twistedSplitting A B φ c).shortExact
  have : ∀ c, Mono ((twistedι A B φ).app c) := fun c => (h c).mono_f
  have : ∀ c, Epi ((twistedπ A B φ).app c) := fun c => (h c).epi_g
  have : Mono (twistedSC A B φ).f := NatTrans.mono_of_mono_app (twistedι A B φ)
  have : Epi (twistedSC A B φ).g := NatTrans.epi_of_epi_app (twistedπ A B φ)
  refine ⟨?_⟩
  rw [ShortComplex.exact_iff_isZero_homology]
  refine Functor.isZero _ fun c => ?_
  refine IsZero.of_iso ?_ (((twistedSC A B φ).mapHomologyIso
    ((evaluation _ _).obj c)).symm)
  exact (ShortComplex.exact_iff_isZero_homology _).1 (h c).exact

/-- **The twisted extension has no section** as soon as `A` vanishes at `left` and `right`, the
restrictions of `B` along the two legs have the same kernel, and `φ ≠ 0`. -/
lemma twisted_no_section [Subsingleton (A.obj (op WalkingCospan.left))]
    [Subsingleton (A.obj (op WalkingCospan.right))]
    (hB : ∀ q, B.map WalkingCospan.Hom.inl.op q = 0 → B.map WalkingCospan.Hom.inr.op q = 0)
    (s : A ⟶ twisted A B φ) (hs : s ≫ twistedπ A B φ = 𝟙 A) (ξ : A.obj (op WalkingCospan.one)) :
    φ ξ = 0 := by
  have h1 : (s.app (op WalkingCospan.one) ξ).1 = ξ :=
    ConcreteCategory.congr_hom (congrArg (fun t => t.app (op WalkingCospan.one)) hs) ξ
  have key : ∀ (c : WalkingCospanᵒᵖ) [Subsingleton (A.obj c)] (f : op WalkingCospan.one ⟶ c),
      (twisted A B φ).map f (s.app (op WalkingCospan.one) ξ) = 0 := fun c _ f => by
    simpa only [ConcreteCategory.comp_apply, Subsingleton.elim (A.map f ξ) 0, map_zero] using
      (ConcreteCategory.congr_hom (s.naturality f) ξ).symm
  have hl := congrArg Prod.snd (key _ WalkingCospan.Hom.inl.op)
  have hr := congrArg Prod.snd (key _ WalkingCospan.Hom.inr.op)
  rw [twisted_map_apply] at hl hr
  rwa [hB _ ((add_zero _).symm.trans hl), zero_add, h1] at hr

end Twisted

/-! ### An injective abelian sheaf on `Bool` not vanishing at `false` -/

/-- The presheaf `t ↦ ∏_{t ⟶ false} ℚ` on `Bool`: the right adjoint of evaluation at `false`,
applied to `ℚ`. -/
abbrev injPresheaf : Boolᵒᵖ ⥤ AddCommGrpCat.{0} :=
  (evaluationRightAdjoint AddCommGrpCat.{0} (op false)).obj (AddCommGrpCat.of ℚ)

/-- The right adjoint of evaluation, an exact functor, preserves injectives, and `ℚ` is
divisible. -/
instance injective_injPresheaf : Injective injPresheaf :=
  Injective.injective_of_adjoint (evaluationAdjunctionLeft AddCommGrpCat.{0} (op false)) _

/-- The injective abelian sheaf `I` on `Bool`. -/
abbrev injSheaf : Sheaf K AddCommGrpCat.{0} :=
  (sheafBotEquivalence AddCommGrpCat.{0}).inverse.obj injPresheaf

/-- `I` is injective, sheaves for the trivial topology being presheaves. -/
instance injective_injSheaf : Injective injSheaf :=
  ((sheafBotEquivalence AddCommGrpCat.{0}).symm.map_injective_iff injPresheaf).2 inferInstance

/-- A nonzero section of `I` over `false`. -/
def injSection : injPresheaf.obj (op false) :=
  (Pi.lift fun _ => 𝟙 (AddCommGrpCat.of ℚ)) (1 : ℚ)

/-- `injSection` is not zero: its component at `𝟙 false` is `1`. -/
lemma injSection_ne_zero : injSection ≠ 0 := by
  intro h
  have h1 : (Pi.π (fun _ : op false ⟶ op false => AddCommGrpCat.of ℚ) (𝟙 _)) injSection =
      (1 : ℚ) := by
    rw [injSection, ← ConcreteCategory.comp_apply, Pi.lift_π]
    rfl
  rw [h] at h1
  exact one_ne_zero (h1.symm.trans (map_zero _))

/-! ### `Ext^1(O_C, g^{-1} I) ≠ 0` -/

/-- The underlying abelian presheaf of `O_C`. -/
abbrev unitPresheaf : WalkingCospanᵒᵖ ⥤ AddCommGrpCat.{0} :=
  ((SheafOfModules.toSheaf OC).obj (SheafOfModules.unit OC)).obj

/-- The underlying presheaf of `g^{-1} I`. -/
abbrev restrictedInjPresheaf : WalkingCospanᵒᵖ ⥤ AddCommGrpCat.{0} :=
  ((abelianRestriction.{0} J K u).obj injSheaf).obj

/-- The cocycle `ℤ = O_C(one) ⟶ (g^{-1} I)(right) = I(false)`, `1 ↦ injSection`. -/
def cocycle : unitPresheaf.obj (op WalkingCospan.one) ⟶
    restrictedInjPresheaf.obj (op WalkingCospan.right) :=
  (AddCommGrpCat.ofHom (zmultiplesHom (injPresheaf.obj (op false)) injSection) :
    AddCommGrpCat.of ℤ ⟶ _)

/-- `O_C` vanishes at `left`. -/
instance subsingleton_unitPresheaf_left :
    Subsingleton (unitPresheaf.obj (op WalkingCospan.left)) :=
  subsingleton_OC_left

/-- `O_C` vanishes at `right`. -/
instance subsingleton_unitPresheaf_right :
    Subsingleton (unitPresheaf.obj (op WalkingCospan.right)) :=
  subsingleton_OC_right

/-- **`Ext^1(O_C, g^{-1} I)` is not zero**: the twisted extension of `O_C` by `g^{-1} I` along
`injSection` does not split. -/
theorem not_subsingleton_ext_unit :
    ¬ Subsingleton (Ext.{0} ((SheafOfModules.toSheaf OC).obj (SheafOfModules.unit OC))
      ((abelianRestriction.{0} J K u).obj injSheaf) 1) := by
  intro hsub
  have hS := (twistedSC_shortExact unitPresheaf restrictedInjPresheaf cocycle).map_of_exact
    (sheafBotEquivalence AddCommGrpCat.{0}).inverse
  obtain ⟨x₂, hx₂⟩ := Ext.covariant_sequence_exact₃ _ hS
    (Ext.mk₀ (𝟙 ((SheafOfModules.toSheaf OC).obj (SheafOfModules.unit OC)))) (zero_add 1)
    (@Subsingleton.elim _ hsub _ _)
  obtain ⟨σ, rfl⟩ := (Ext.mk₀_bijective _ _).2 x₂
  rw [Ext.mk₀_comp_mk₀] at hx₂
  have hσ := (Ext.mk₀_bijective _ _).1 hx₂
  have h' : σ.hom ≫ twistedπ unitPresheaf restrictedInjPresheaf cocycle = 𝟙 _ :=
    congrArg (fun t => t.hom) hσ
  have h0 := twisted_no_section unitPresheaf restrictedInjPresheaf cocycle (fun q hq => hq)
    σ.hom h' (1 : ℤ)
  apply injSection_ne_zero
  have h2 : cocycle (1 : ℤ) = injSection := by
    show zmultiplesHom (injPresheaf.obj (op false)) injSection (1 : ℤ) = injSection
    simp
  rw [← h2]
  exact h0

/-- `Ext^1(-, Y)` vanishes together at isomorphic objects. -/
lemma subsingleton_ext_of_iso {X X' Y : Sheaf J AddCommGrpCat.{0}} (e : X ≅ X')
    (h : Subsingleton (Ext.{0} X Y 1)) : Subsingleton (Ext.{0} X' Y 1) := by
  have key : ∀ γ : Ext.{0} X' Y 1,
      γ = (Ext.mk₀ e.inv).comp ((Ext.mk₀ e.hom).comp γ (zero_add 1)) (zero_add 1) := by
    intro γ
    rw [← Ext.comp_assoc _ _ _ (add_zero 0) (zero_add 1) (by omega), Ext.mk₀_comp_mk₀,
      e.inv_hom_id, Ext.mk₀_id_comp]
  refine ⟨fun α β => ?_⟩
  rw [key α, key β, Subsingleton.elim ((Ext.mk₀ e.hom).comp α (zero_add 1))]

/-! ### The derived comparison is not invertible -/

/-- **The comparison `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` of Stacks 07AE is not an isomorphism in
the counterexample.** If it were, `forget j_{one!}O_one ≅ O_C` would be `Ext`-acyclic for
`g_!^{Ab} ⊣ g^{-1}` (`extAcyclic_forget_extensionByZeroUnit`), but
`Ext^1(O_C, g^{-1} I) ≠ 0`. -/
theorem not_isIso_derivedForgetComparison : ¬ IsIso (derivedForgetComparison J K u OD) := by
  intro h
  have hU : IsIso ((derivedForgetComparison J K u OD).app
      ((DerivedCategory.singleFunctor _ 0).obj
        (extensionByZeroUnit OC WalkingCospan.one))) := inferInstance
  have hsub := extAcyclic_forget_extensionByZeroUnit J K u O WalkingCospan.one hU injSheaf 1
    le_rfl
  exact not_subsingleton_ext_unit (subsingleton_ext_of_iso ((SheafOfModules.toSheaf OC).mapIso
    (Stacks.Sites.ExtensionByZero.extensionByZeroUnitIsoUnitOfTerminal J OC _ isTerminalOne))
    hsub)


/-- **Any isomorphism `Lg_!^{Ab}(forget j_{one!}O_one) ≅ forget(Lg_! j_{one!}O_one)` makes
`forget j_{one!}O_one` `Ext`-acyclic for `g_!^{Ab} ⊣ g^{-1}`.** This is the argument of
`extAcyclic_forget_extensionByZeroUnit` with the canonical comparison replaced by an arbitrary
isomorphism: by the derived adjunction of `Lg_!^{Ab}`,
`Ext^n(forget j_{one!}O_one, g^{-1}I) = Hom(Lg_!^{Ab} forget j_{one!}O_one, I[n])`, and the
isomorphism together with Stacks 07AC identifies the source with `forget(g_! j_{one!}O_one)` in
degree zero. -/
theorem subsingleton_ext_of_iso_obj
    (α : (derivedLowerShriekAbelian J K u).obj
        ((forgetSourceModules J K u OD).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj (extensionByZeroUnit OC WalkingCospan.one))) ≅
      (forgetTargetModules K OD).mapDerivedCategory.obj ((derivedLowerShriek J K u OD).obj
        ((DerivedCategory.singleFunctor _ 0).obj (extensionByZeroUnit OC WalkingCospan.one))))
    (I : Sheaf K AddCommGrpCat.{0}) [Injective I] (n : ℕ) (hn : 1 ≤ n) :
    Subsingleton (Ext.{0} ((forgetSourceModules J K u OD).obj
      (extensionByZeroUnit OC WalkingCospan.one)) ((abelianRestriction.{0} J K u).obj I) n) := by
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by omega⟩
  let jU := extensionByZeroUnit OC WalkingCospan.one
  let X := (forgetSourceModules J K u OD).obj jU
  let W := (forgetTargetModules K OD).obj ((lowerShriekModules J K u OD).obj jU)
  let dR := derivedAbelianRestriction.{0} J K u
  let adj := derivedAbelianLowerShriekAdjunction.{0} J K u
  let E : (derivedLowerShriekAbelian J K u).obj ((DerivedCategory.singleFunctor _ 0).obj X) ≅
      (DerivedCategory.singleFunctor _ 0).obj W :=
    (derivedLowerShriekAbelian J K u).mapIso
        (((forgetSourceModules J K u OD).mapDerivedCategorySingleFunctor 0).app jU).symm ≪≫
      α ≪≫
      (forgetTargetModules K OD).mapDerivedCategory.mapIso
        (derivedLowerShriekSingleExtensionByZeroUnitIso J K u O WalkingCospan.one) ≪≫
      ((forgetTargetModules K OD).mapDerivedCategorySingleFunctor 0).app _
  let T := ((DerivedCategory.singleFunctor _ 0).obj I)⟦((m + 1 : ℕ) : ℤ)⟧
  let e1 : ((DerivedCategory.singleFunctor _ 0).obj
      ((abelianRestriction.{0} J K u).obj I))⟦((m + 1 : ℕ) : ℤ)⟧ ≅ dR.obj T :=
    (shiftFunctor _ ((m + 1 : ℕ) : ℤ)).mapIso
        (((abelianRestriction.{0} J K u).mapDerivedCategorySingleFunctor 0).app I).symm ≪≫
      ((dR.commShiftIso ((m + 1 : ℕ) : ℤ)).app _).symm
  let eq : Ext.{0} X ((abelianRestriction.{0} J K u).obj I) (m + 1) ≃ Ext.{0} W I (m + 1) :=
    Ext.homEquiv.trans (((Iso.refl _).homCongr e1).trans ((adj.homEquiv _ _).symm.trans
      ((E.homCongr (Iso.refl T)).trans Ext.homEquiv.symm)))
  have := Ext.subsingleton_of_injective W I m
  exact eq.subsingleton

/-- **The square of Stacks 07AE does not commute up to any isomorphism in the counterexample**:
there is no isomorphism at all between `Lg_!^{Ab}(forget j_{one!}O_one)` and
`forget(Lg_! j_{one!}O_one)`, let alone a natural one. -/
theorem not_nonempty_iso_obj :
    ¬ Nonempty ((derivedLowerShriekAbelian J K u).obj
        ((forgetSourceModules J K u OD).mapDerivedCategory.obj
          ((DerivedCategory.singleFunctor _ 0).obj (extensionByZeroUnit OC WalkingCospan.one))) ≅
      (forgetTargetModules K OD).mapDerivedCategory.obj ((derivedLowerShriek J K u OD).obj
        ((DerivedCategory.singleFunctor _ 0).obj (extensionByZeroUnit OC WalkingCospan.one)))) :=
  fun ⟨α⟩ => not_subsingleton_ext_unit (subsingleton_ext_of_iso ((SheafOfModules.toSheaf OC).mapIso
    (Stacks.Sites.ExtensionByZero.extensionByZeroUnitIsoUnitOfTerminal J OC _ isTerminalOne))
    (subsingleton_ext_of_iso_obj α injSheaf 1 le_rfl))

/-- The two composites `Lg_!^{Ab} ∘ forget` and `forget ∘ Lg_!` are not isomorphic. -/
theorem not_nonempty_iso :
    ¬ Nonempty ((forgetSourceModules J K u OD).mapDerivedCategory ⋙
        derivedLowerShriekAbelian J K u ≅
      derivedLowerShriek J K u OD ⋙ (forgetTargetModules K OD).mapDerivedCategory) :=
  fun ⟨α⟩ => not_nonempty_iso_obj ⟨α.app _⟩

/-! ### The warning of Stacks 07AE -/

end Stacks.Cohomology.DerivedLowerShriek.ForgetCounterexample

namespace Stacks.Cohomology.DerivedLowerShriek

open ForgetCounterexample

attribute [local instance] HasDerivedCategory.standard
  isRightAdjoint_sourceSliceRestriction isRightAdjoint_targetSliceRestriction
  isLeftDerivedFunctor_derivedLowerShriek_comp_forget_of_continuous

/-- **Stacks Project, Tag 07AE, the warning.** Let `u : C ⥤ D`, `g`, `O_D` and `O_C = g^{-1} O_D`
be as in Stacks 07AC. In general the square

```
D(O_C) --Lg_!--> D(O_D)
  |                 |
forget            forget
  v                 v
D(C) --Lg_!^{Ab}--> D(D)
```

does **not** commute, and this can happen even if `g_! = g_!^{Ab}`.

Stated as an existence: there are small sites `C`, `D`, a functor `u : C ⥤ D` satisfying the
hypotheses of Stacks 07AC (continuous in the sense of Stacks 00WV, which is
`Functor.IsContinuous` together with `Stacks.Sites.PreservesCoveringPullbacks`, and
cocontinuous) and a sheaf of rings `O_D` on `D` such that

* `g_! = g_!^{Ab}`: the canonical comparison `g_!^{Ab} ∘ forget ⟶ forget ∘ g_!` of Stacks 0798
  (`forgetComparison`) is an isomorphism, and yet
* the canonical comparison `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` of Stacks 07AE
  (`derivedForgetComparison`, characterised by
  `existsUnique_derivedForgetComparison_of_continuous`) is not an isomorphism, and indeed the
  two composites `Lg_!^{Ab} ∘ forget` and `forget ∘ Lg_!` are not isomorphic by any natural
  isomorphism whatsoever.

The example: `C` is the cospan category `left ⟶ one ⟵ right` and `D` is `Bool` ordered by
`false ≤ true`, both with the trivial topology, `u` sends the legs to `false ≤ true`, and `O_D`
is `ℤ` at `true` and the zero ring at `false`. Every `O_C`-module vanishes at `left` and `right`,
which forces `g_! = g_!^{Ab}` (`isIso_forgetComparison`); but the underlying abelian sheaf of
`j_{one!} O_one = O_C` has a nonzero `Ext^1` into the restriction of an injective abelian sheaf
of `D` (`not_subsingleton_ext_unit`), which is the homotopy pushout `0 ← ℤ → 0` computing
`Lg_!^{Ab}` at `false` having nonzero `H^{-1}`, so the comparison is not invertible
(`not_isIso_derivedForgetComparison`, via the criterion of this tag,
`extAcyclic_forget_extensionByZeroUnit`). -/
@[stacks 07AE "the warning: the square `forget ∘ Lg_!` vs `Lg_!^{Ab} ∘ forget` need not \
commute even when `g_! = g_!^{Ab}` -- an example of sites, a functor satisfying the hypotheses of \
Stacks 07AC and a sheaf of rings for which the comparison of Stacks 0798 is an isomorphism and \
the comparison `Lg_!^{Ab} ∘ forget ⟶ forget ∘ Lg_!` is not, nor are the two composites isomorphic \
by any natural isomorphism; the example lives in universe 0, an existence statement needing one"]
theorem exists_isIso_forgetComparison_not_isIso_derivedForgetComparison :
    ∃ (C D : Type) (_ : SmallCategory C) (_ : SmallCategory D)
      (J : GrothendieckTopology C) (K : GrothendieckTopology D) (f : C ⥤ D)
      (_ : f.IsContinuous J K) (_ : f.IsCocontinuous J K)
      (_ : Stacks.Sites.PreservesCoveringPullbacks J f) (O : Sheaf K CommRingCat.{0}),
      IsIso (forgetComparison J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) ∧
        ¬ IsIso (derivedForgetComparison J K f
          (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)) ∧
        ¬ Nonempty ((forgetSourceModules J K f
            (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O)).mapDerivedCategory ⋙
              derivedLowerShriekAbelian J K f ≅
          derivedLowerShriek J K f
              (Stacks.SheafOfModules.Tensor.ringSheaf (targetRingedSite K O).O) ⋙
            (forgetTargetModules K (Stacks.SheafOfModules.Tensor.ringSheaf
              (targetRingedSite K O).O)).mapDerivedCategory) :=
  ⟨WalkingCospan, Bool, inferInstance, inferInstance, ForgetCounterexample.J,
    ForgetCounterexample.K, u, inferInstance, inferInstance, inferInstance, O,
    isIso_forgetComparison, not_isIso_derivedForgetComparison, not_nonempty_iso⟩

end Stacks.Cohomology.DerivedLowerShriek
