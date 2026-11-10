module

public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.HigherDirectImageBaseChange
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardCocontinuousSquare
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedTransport
public import StacksFrontier.AlgebraicGeometry.Stacks.Sheaves.Injectives
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackEssentiallySmall
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.BaseChangeOverASquareOfSites

/-!
# Base change for the direct image of sheaves of modules (Stacks 075H)

Let `f : 𝒳 ⥤ 𝒴` and `g : 𝒴' ⥤ 𝒴` be 1-morphisms of categories fibred in groupoids over the big
fppf category of a scheme `S`, and let

```
𝒴' ×_𝒴 𝒳 --- g' ---> 𝒳
   |                 |
   f'                f
   v                 v
  𝒴' ------ g -----> 𝒴
```

be the canonical 2-cartesian square, `g' = fst`, `f' = snd`. For an arbitrary topology
`τ ≤ fppf` on the schemes and an arbitrary module universe, this file constructs the direct image
of sheaves of modules as the canonical direct image along a cocontinuous functor, proves that it
is right adjoint to the inverse image of Stacks 06WE, and proves **Stacks 075H for sheaves of
modules**: the base change map `g⁻¹ f_* ⟶ f'_* (g')⁻¹` is an isomorphism, and in every degree
`g⁻¹ Rⁿf_* ≅ Rⁿf'_* (g')⁻¹` as soon as `(g')⁻¹` preserves injective sheaves of modules (Stacks
06X2: `g'` faithful, the apex having equalizers).

## Main definitions

* `AlgebraicGeometry.Stack.moduleDirectImage`: the direct image `f_*` of sheaves of modules, at an
  arbitrary module universe.
* `AlgebraicGeometry.Stack.moduleDirectImageAdjunction`: `f^* ⊣ f_*`.
* `Stacks.SheafOfModules.twoSquareComparison`: the linear base change comparison of the canonical
  direct images over an arbitrary 2-commutative square of ringed sites whose ring maps are
  compatible with the legs of the Kan extensions.
* `AlgebraicGeometry.Stack.moduleDirectImageBaseChange`: the base change map of Stacks 075H.

## Main results

* `AlgebraicGeometry.Stack.isIso_moduleDirectImageBaseChange` and
  `AlgebraicGeometry.Stack.moduleDirectImageBaseChangeIso`: Stacks 075H in degree zero.
* `AlgebraicGeometry.Stack.moduleHigherDirectImageBaseChangeIso`: Stacks 075H in every degree.
* `AlgebraicGeometry.Stack.preservesInjectiveObjects_modulePullback`: Stacks 06X2 (2) for the
  inverse image of Stacks 06WE, with its size conditions read off essential smallness.
* `Stacks.SheafOfModules.pushforwardCocontinuousSectionsIsoOfIsTerminal`: sections of a direct
  image over an object `y` whose comma category `CostructuredArrow F y` has a terminal object.

## Implementation notes

The module direct image is `Stacks.SheafOfModules.pushforwardCocontinuous`, whose module
structure is characterised on the legs of the limit cones computing the right Kan extension. The
base change transformation of right Kan extensions is characterised on the same legs
(`Stacks.SheafOfModules.ranBaseChange_π`), which is what makes it linear; the 2-cell of the
2-fibre product enters only through the leg it moves, and the ring maps of the two columns agree
on legs because the comparison isomorphism of the 2-fibre product lies over an identity
(`scalarπ_baseChange`). Invertibility is Guitart exactness of the 2-fibre product square, which is
Stacks 075B, and the forgetful functors reflect isomorphisms.

No Stacks tag is registered here: the statements are the module clause of Stacks 075H in the
generality the consumers need, not the tag itself.

## References

* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
* [Stacks Project, Tag 075B](https://stacks.math.columbia.edu/tag/075B)
* [Stacks Project, Tag 06WE](https://stacks.math.columbia.edu/tag/06WE)
* [Stacks Project, Tag 06X2](https://stacks.math.columbia.edu/tag/06X2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u v w v' w' m r

namespace Stacks.SheafOfModules

variable {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y] (F : X ⥤ Y)
  [∀ G : Xᵒᵖ ⥤ RingCat.{r}, F.op.HasPointwiseRightKanExtension G]
  [∀ G : Xᵒᵖ ⥤ AddCommGrpCat.{m}, F.op.HasPointwiseRightKanExtension G]
  (T : Yᵒᵖ ⥤ RingCat.{r}) (R : Xᵒᵖ ⥤ RingCat.{r}) (h : R = F.op ⋙ T)

/-- Applying `eqToHom h` and then `eqToHom h.symm` to a ring element is the identity. -/
private theorem eqToHom_app_symm_apply {A B : Xᵒᵖ ⥤ RingCat.{r}} (h : A = B) (U : Xᵒᵖ)
    (s : B.obj U) : ((eqToHom h).app U).hom (((eqToHom h.symm).app U).hom s) = s := by
  subst h
  rfl

omit [∀ G : Xᵒᵖ ⥤ AddCommGrpCat.{m}, F.op.HasPointwiseRightKanExtension G] in
/-- The ring maps that the transported tautological structure map cuts out at the legs are the
restriction maps of `T` followed by the identification `F^{-1}T = R`. -/
theorem scalarπ_ranUnitRing_comp_map_eqToHom (V : Yᵒᵖ) (j : StructuredArrow V F.op) :
    scalarπ F (ranUnitRing F T ≫ F.op.ran.map (eqToHom h.symm)) V j =
      T.map j.hom ≫ (eqToHom h.symm).app j.right := by
  subst h
  rw [eqToHom_refl, CategoryTheory.Functor.map_id, Category.comp_id, scalarπ_ranUnitRing,
    NatTrans.id_app]
  exact (Category.comp_id _).symm

/-- The unit of the right Kan extension adjunction on underlying presheaves of abelian groups is
linear for the transported tautological structure map. -/
theorem ranSMul_ranUnitPresheaf_restrictScalars (N : PresheafOfModules.{m} T) (V : Yᵒᵖ)
    (s : T.obj V) :
    smulPresheaf N V s ≫ (ranUnitPresheaf F T N).app V =
      (ranUnitPresheaf F T N).app V ≫
        ranSMul F (ranUnitRing F T ≫ F.op.ran.map (eqToHom h.symm))
          ((PresheafOfModules.pushforward₀.{m} F T ⋙
            PresheafOfModules.restrictScalars (eqToHom h)).obj N) V s := by
  refine ran_hom_ext F.op ((PresheafOfModules.pushforward₀.{m} F T).obj N).presheaf (fun j => ?_)
  have h₁ : (ranUnitPresheaf F T N).app V ≫
      ranπ F.op ((PresheafOfModules.pushforward₀.{m} F T).obj N).presheaf V j =
        N.presheaf.map j.hom :=
    ranAdjunction_unit_app_ranπ F.op N.presheaf V j
  have h₂ := ranSMul_π F (ranUnitRing F T ≫ F.op.ran.map (eqToHom h.symm))
    ((PresheafOfModules.pushforward₀.{m} F T ⋙
      PresheafOfModules.restrictScalars (eqToHom h)).obj N) V s j
  rw [scalarπ_ranUnitRing_comp_map_eqToHom F T R h] at h₂
  refine (Category.assoc _ _ _).trans ?_
  refine (congrArg (smulPresheaf N V s ≫ ·) h₁).trans ?_
  refine (smulPresheaf_map N j.hom s).trans ?_
  refine Eq.trans ?_ (Category.assoc _ _ _).symm
  refine Eq.trans ?_ (congrArg ((ranUnitPresheaf F T N).app V ≫ ·) h₂).symm
  refine Eq.trans ?_ (Category.assoc _ _ _)
  refine Eq.trans ?_ (congrArg (· ≫ _) h₁).symm
  exact congrArg (N.presheaf.map j.hom ≫ smulPresheaf N _ ·)
    (eqToHom_app_symm_apply h j.right ((T.map j.hom).hom s)).symm

/-- The counit of the right Kan extension adjunction on underlying presheaves of abelian groups is
linear for the transported tautological structure map. -/
theorem ranSMul_ranCounit_restrictScalars (P : PresheafOfModules.{m} R) (U : Xᵒᵖ)
    (s : R.obj U) :
    ranSMul F (ranUnitRing F T ≫ F.op.ran.map (eqToHom h.symm)) P (F.op.obj U)
        (((eqToHom h).app U).hom s) ≫ (F.op.ranCounit.app P.presheaf).app U =
      (F.op.ranCounit.app P.presheaf).app U ≫ smulPresheaf P U s := by
  have hh := ranSMul_π F (ranUnitRing F T ≫ F.op.ran.map (eqToHom h.symm)) P (F.op.obj U)
    (((eqToHom h).app U).hom s) (StructuredArrow.mk (𝟙 (F.op.obj U)))
  rw [ranπ_mk_id, scalarπ_ranUnitRing_comp_map_eqToHom F T R h] at hh
  refine hh.trans ?_
  congr 2
  rw [show (StructuredArrow.mk (𝟙 (F.op.obj U)) : StructuredArrow (F.op.obj U) F.op).hom = 𝟙 _
    from rfl, CategoryTheory.Functor.map_id, Category.id_comp]
  exact eqToHom_app_symm_apply h.symm U s

/-- The unit of the adjunction between restriction along `F`, with scalars transported along
`R = F^{-1}T`, and the direct image: the unit of the right Kan extension adjunction on underlying
presheaves of abelian groups. -/
def ranPushforwardRestrictScalarsUnit :
    𝟭 (PresheafOfModules.{m} T) ⟶
      (PresheafOfModules.pushforward₀.{m} F T ⋙ PresheafOfModules.restrictScalars (eqToHom h)) ⋙
        ranPushforward.{m} F (ranUnitRing F T ≫ F.op.ran.map (eqToHom h.symm)) where
  app N := PresheafOfModules.homMk (ranUnitPresheaf F T N)
    (fun V r n => ConcreteCategory.congr_hom
      (ranSMul_ranUnitPresheaf_restrictScalars F T R h N V r) n)
  naturality _ _ g := (PresheafOfModules.toPresheaf T).map_injective
    ((F.op.ranAdjunction AddCommGrpCat.{m}).unit.naturality (presheafMap g))

/-- The counit of the adjunction between restriction along `F`, with scalars transported along
`R = F^{-1}T`, and the direct image: the counit of the right Kan extension adjunction on
underlying presheaves of abelian groups. -/
def ranPushforwardRestrictScalarsCounit :
    ranPushforward.{m} F (ranUnitRing F T ≫ F.op.ran.map (eqToHom h.symm)) ⋙
        PresheafOfModules.pushforward₀.{m} F T ⋙ PresheafOfModules.restrictScalars (eqToHom h) ⟶
      𝟭 (PresheafOfModules.{m} R) where
  app P := PresheafOfModules.homMk (F.op.ranCounit.app P.presheaf)
    (fun U s n => ConcreteCategory.congr_hom (ranSMul_ranCounit_restrictScalars F T R h P U s) n)
  naturality _ _ g := (PresheafOfModules.toPresheaf R).map_injective
    (F.op.ranCounit.naturality (presheafMap g))

/-- Restriction of presheaves of modules along `F`, with scalars transported along an
identification `R = F^{-1}T`, is left adjoint to the direct image of presheaves of modules for
the corresponding transport of the tautological structure map. The unit and counit are those of
the right Kan extension adjunction on underlying presheaves of abelian groups. -/
noncomputable def pushforward₀RestrictScalarsRanPushforwardAdjunction :
    PresheafOfModules.pushforward₀.{m} F T ⋙ PresheafOfModules.restrictScalars (eqToHom h) ⊣
      ranPushforward.{m} F (ranUnitRing F T ≫ F.op.ran.map (eqToHom h.symm)) where
  unit := ranPushforwardRestrictScalarsUnit F T R h
  counit := ranPushforwardRestrictScalarsCounit F T R h
  left_triangle_components N :=
    (PresheafOfModules.toPresheaf R).map_injective
      (F.op.ranCounit_app_whiskerLeft_ranAdjunction_unit_app N.presheaf)
  right_triangle_components P := by
    refine (PresheafOfModules.toPresheaf T).map_injective ?_
    have h := (F.op.ranAdjunction AddCommGrpCat.{m}).right_triangle_components P.presheaf
    rw [Functor.ranAdjunction_counit] at h
    exact h

/-- **The unit of the adjunction, followed by the leg at `(U, ψ)` of the right Kan extension, is
the restriction map along `ψ`.** -/
theorem pushforward₀RestrictScalarsRanPushforwardAdjunction_unit_app_ranπ
    (N : PresheafOfModules.{m} T) (V : Yᵒᵖ) (j : StructuredArrow V F.op) :
    (presheafMap ((pushforward₀RestrictScalarsRanPushforwardAdjunction F T R h).unit.app N)).app V ≫
      ranπ F.op ((PresheafOfModules.pushforward₀.{m} F T ⋙
        PresheafOfModules.restrictScalars (eqToHom h)).obj N).presheaf V j =
      N.presheaf.map j.hom :=
  ranAdjunction_unit_app_ranπ F.op N.presheaf V j

/-- Postcomposing a morphism into a direct image with the direct image of a morphism `φ`, and
then taking the leg at `(U, ψ)` of the right Kan extension, is taking the leg first and then
applying `φ` at `U`. -/
theorem ranπ_presheafMap_comp_ranPushforward_map_apply {S : Xᵒᵖ ⥤ RingCat.{r}}
    (ψ : T ⟶ F.op.ran.obj S) {N : PresheafOfModules.{m} T} {P₁ P₂ : PresheafOfModules.{m} S}
    (a : N ⟶ (ranPushforward.{m} F ψ).obj P₁) (φ : P₁ ⟶ P₂) (V : Yᵒᵖ)
    (j : StructuredArrow V F.op) (z : N.presheaf.obj V) :
    (ranπ F.op P₂.presheaf V j).hom
        (((presheafMap (a ≫ (ranPushforward.{m} F ψ).map φ)).app V).hom z) =
      ((presheafMap φ).app j.right).hom
        ((ranπ F.op P₁.presheaf V j).hom (((presheafMap a).app V).hom z)) :=
  ConcreteCategory.congr_hom (ranπ_map_functor F.op (presheafMap φ) V j)
    (((presheafMap a).app V).hom z)

section Sections

variable {X : Type v} [Category.{w} X] {Y : Type v'} [Category.{w'} Y] {F : X ⥤ Y}
  {JX : GrothendieckTopology X} {JY : GrothendieckTopology Y} [F.IsCocontinuous JX JY]
  [∀ G : Xᵒᵖ ⥤ RingCat.{r}, F.op.HasPointwiseRightKanExtension G]
  [∀ G : Xᵒᵖ ⥤ AddCommGrpCat.{m}, F.op.HasPointwiseRightKanExtension G]
  {OX : Sheaf JX RingCat.{r}} {OY : Sheaf JY RingCat.{r}}
  (fSharp : OY ⟶ (F.sheafPushforwardCocontinuous RingCat.{r} JX JY).obj OX)
  {y : Y} {t : CostructuredArrow F y} (ht : IsTerminal t)

/-- A terminal object of `CostructuredArrow F y` is an initial leg of the right Kan extension
along `F.op` at `op y`. -/
def isInitialStructuredArrowOfIsTerminal :
    IsInitial (StructuredArrow.mk (Y := op t.left) t.hom.op : StructuredArrow (op y) F.op) :=
  (initialOpOfTerminal ht).isInitialObj (costructuredArrowOpEquivalence F y).functor

/-- **Sections of a direct image over an object with a terminal arrow.** If `(x₀, F x₀ ⟶ y)` is
terminal in `CostructuredArrow F y`, the sections of the direct image of a sheaf of modules `M`
over `y` are the sections of `M` over `x₀`, through the leg of the right Kan extension at that
arrow, naturally in `M`. -/
def pushforwardCocontinuousSectionsIsoOfIsTerminal :
    pushforwardCocontinuous.{m} F fSharp ⋙ toAbelianPresheaf.{m} OY ⋙
        (evaluation Yᵒᵖ AddCommGrpCat.{m}).obj (op y) ≅
      toAbelianPresheaf.{m} OX ⋙ (evaluation Xᵒᵖ AddCommGrpCat.{m}).obj (op t.left) :=
  NatIso.ofComponents
    (fun M => by
      have : IsIso (ranπ F.op M.val.presheaf (op y)
          (StructuredArrow.mk (Y := op t.left) t.hom.op)) :=
        (ranIsLimit F.op M.val.presheaf (op y)).isIso_π_app_of_isInitial _
          (isInitialStructuredArrowOfIsTerminal ht)
      exact @asIso _ _ _ _ (ranπ F.op M.val.presheaf (op y)
        (StructuredArrow.mk (Y := op t.left) t.hom.op)) this)
    (fun {M N} φ => ranπ_map_functor F.op (presheafMap φ.val) (op y) _)

end Sections

section TwoSquare

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄

variable {C' : Type u₁} [Category.{v₁} C'] {C : Type u₂} [Category.{v₂} C] {D' : Type u₃}
  [Category.{v₃} D'] {D : Type u₄} [Category.{v₄} D] {J' : GrothendieckTopology C'}
  {J : GrothendieckTopology C} {K' : GrothendieckTopology D'} {K : GrothendieckTopology D}
  {u' : C' ⥤ D'} {u : C ⥤ D} {v' : C' ⥤ C} {v : D' ⥤ D} [u.IsCocontinuous J K]
  [u'.IsCocontinuous J' K'] [v.IsContinuous K' K] [v'.IsContinuous J' J]
  [∀ G : Cᵒᵖ ⥤ AddCommGrpCat.{m}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ AddCommGrpCat.{m}, u'.op.HasPointwiseRightKanExtension G]
  [∀ G : Cᵒᵖ ⥤ RingCat.{r}, u.op.HasPointwiseRightKanExtension G]
  [∀ G : C'ᵒᵖ ⥤ RingCat.{r}, u'.op.HasPointwiseRightKanExtension G]
  {OC : Sheaf J RingCat.{r}} {OD : Sheaf K RingCat.{r}} {OC' : Sheaf J' RingCat.{r}}
  {OD' : Sheaf K' RingCat.{r}} (w : TwoSquare v' u' u v)
  (φ : OC' ⟶ (v'.sheafPushforwardContinuous RingCat.{r} J' J).obj OC)
  (χ : OD' ⟶ (v.sheafPushforwardContinuous RingCat.{r} K' K).obj OD)
  (fSharp : OD ⟶ (u.sheafPushforwardCocontinuous RingCat.{r} J K).obj OC)
  (fSharp' : OD' ⟶ (u'.sheafPushforwardCocontinuous RingCat.{r} J' K').obj OC')

/-- The image of a leg `(U', ψ)` of the right Kan extension along `u'.op` at `V'` under the
comparison functor of the 2-square `w`, a leg of the right Kan extension along `u.op` at
`v.op(V')`. -/
abbrev twoSquareIndex {V' : D'ᵒᵖ} (j : StructuredArrow V' u'.op) :
    StructuredArrow (v.op.obj V') u.op :=
  StructuredArrow.mk (v.op.map j.hom ≫ w.op.app j.right)

/-- A morphism of sheaves of rings into a restriction, read at an object. -/
def restrictRingApp {E : Type u₁} [Category.{v₁} E] {G : Type u₂} [Category.{v₂} G]
    {JE : GrothendieckTopology E} {JG : GrothendieckTopology G} {a : E ⥤ G}
    [a.IsContinuous JE JG] {OE : Sheaf JE RingCat.{r}} {OG : Sheaf JG RingCat.{r}}
    (ψ : OE ⟶ (a.sheafPushforwardContinuous RingCat.{r} JE JG).obj OG) (U : Eᵒᵖ) :
    OE.obj.obj U ⟶ OG.obj.obj (a.op.obj U) :=
  ψ.hom.app U

/-- The compatibility of the four ring maps of a 2-square of ringed sites with the legs of the
right Kan extensions: a section of `O_{D'}` acts on the leg `(U', ψ)` of `u'_*` through the same
ring map as on the corresponding leg of `u_*`. -/
def TwoSquareRingCompatible : Prop :=
  ∀ (V' : D'ᵒᵖ) (j : StructuredArrow V' u'.op),
    restrictRingApp χ V' ≫
        scalarπ u (structureMapPresheaf u fSharp) (v.op.obj V') (twoSquareIndex w j) =
      scalarπ u' (structureMapPresheaf u' fSharp') V' j ≫ restrictRingApp φ j.right

variable (hring : TwoSquareRingCompatible w φ χ fSharp fSharp') (M : _root_.SheafOfModules.{m} OC)

include hring in
/-- **Base change of right Kan extensions is linear** over a 2-square of ringed sites whose ring
maps are compatible with the legs. -/
lemma ranSMul_twoSquareComparison (V' : D'ᵒᵖ) (t : OD'.obj.obj V') :
    ranSMul u (structureMapPresheaf u fSharp) M.val (v.op.obj V')
        ((restrictRingApp χ V').hom t) ≫
        (w.op.ranBaseChange.app M.val.presheaf).app V' =
      (w.op.ranBaseChange.app M.val.presheaf).app V' ≫
        ranSMul u' (structureMapPresheaf u' fSharp')
          ((_root_.SheafOfModules.pushforward.{m} φ).obj M).val V' t := by
  refine ran_hom_ext u'.op ((_root_.SheafOfModules.pushforward.{m} φ).obj M).val.presheaf
    (fun j => ?_)
  have e1 := ranSMul_π u (structureMapPresheaf u fSharp) M.val (v.op.obj V')
    ((restrictRingApp χ V').hom t) (twoSquareIndex w j)
  have e2 : (w.op.ranBaseChange.app M.val.presheaf).app V' ≫
      ranπ u'.op ((_root_.SheafOfModules.pushforward.{m} φ).obj M).val.presheaf V' j =
      ranπ u.op M.val.presheaf (v.op.obj V') (twoSquareIndex w j) :=
    ranBaseChange_π w.op M.val.presheaf V' j
  have e3 := ranSMul_π u' (structureMapPresheaf u' fSharp')
    ((_root_.SheafOfModules.pushforward.{m} φ).obj M).val V' t j
  have h := congrArg (fun k => RingCat.Hom.hom k t) (hring V' j)
  simp only [RingCat.comp_apply] at h
  exact ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) e2)).trans
    ((e1.trans (congrArg (fun x => _ ≫ smulPresheaf M.val _ x) h)).trans
      ((Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) e3).trans
        ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ _) e2)))).symm)

include hring in
/-- **The base change comparison of sheaves of modules over a 2-square**,
`g^* ∘ f_* ⟶ (g')^* ∘ f'_*`, whose underlying map of presheaves of abelian groups is the
base change of right Kan extensions. -/
def twoSquareComparison :
    pushforwardCocontinuous.{m} u fSharp ⋙ _root_.SheafOfModules.pushforward.{m} χ ⟶
      _root_.SheafOfModules.pushforward.{m} φ ⋙ pushforwardCocontinuous.{m} u' fSharp' where
  app N := ⟨PresheafOfModules.homMk (w.op.ranBaseChange.app N.val.presheaf)
    (fun V' t n => ConcreteCategory.congr_hom
      (ranSMul_twoSquareComparison w φ χ fSharp fSharp' hring N V' t) n)⟩
  naturality N₁ N₂ ψ := by
    refine _root_.SheafOfModules.hom_ext ?_
    refine (PresheafOfModules.toPresheaf _).map_injective ?_
    exact (w.op.ranBaseChange (D := AddCommGrpCat.{m})).naturality (presheafMap ψ.val)

end TwoSquare

end Stacks.SheafOfModules

namespace AlgebraicGeometry.Stack

/-- The inverse image of sheaves of modules of Stacks 06WE is additive, in every module universe:
it does not change the addition of morphisms. -/
instance additive_modulePullback_univ (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
    (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
    (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
    (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology) :
    (modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).Additive where
  map_add := by intros; rfl

section Injectives

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p) (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- The inverse image of sheaves of modules is the pushforward along the structure-sheaf
identification of `AlgebraicGeometry.Stack.ringStructureSheafCoreHom`. -/
theorem modulePullback_eq_pushforward_ringStructureSheafCoreHom :
    letI : p.IsFibered := hp.isFibered
    letI : q.IsFibered := hq.isFibered
    letI := ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
      (τ.over (B.obj hS))).1
    modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ =
      SheafOfModules.pushforward.{m} (ringStructureSheafCoreHom B S hS p q f τ hp hq hf hτ) := by
  subst hf
  rfl

/-- **Stacks 06X2 (2) for the inverse image of Stacks 06WE.** Along a faithful 1-morphism whose
source has equalizers, the inverse image of sheaves of modules carries injective sheaves of
modules to injective ones; the size conditions are essential smallness of the source and local
smallness of the target in the module universe. -/
theorem preservesInjectiveObjects_modulePullback [f.Faithful] [HasEqualizers 𝒳]
    [EssentiallySmall.{u} 𝒳] [LocallySmall.{u} 𝒴]
    [HasSheafify (associatedTopology B S hS q τ) AddCommGrpCat.{u}]
    [(associatedTopology B S hS q τ).WEqualsLocallyBijective AddCommGrpCat.{u}] :
    (modulePullback.{u, v, w, u, v', w'} B S hS p q hp hq f hf τ hτ).PreservesInjectiveObjects := by
  let : p.IsFibered := hp.isFibered
  let : q.IsFibered := hq.isFibered
  let := ((hq.isFibredOneMorphism hf).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  have hPre : (PresheafOfModules.pushforward.{u}
      (ringStructureSheafCoreHom B S hS p q f τ hp hq hf hτ).hom).IsRightAdjoint :=
    PresheafOfModules.isRightAdjoint_pushforward_of_essentiallySmall.{u} _
  have hK : ∀ G : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{u}, f.op.HasPointwiseLeftKanExtension G := fun _ Y => by
    have := hasColimitsOfShape_of_essentiallySmall.{u} (CostructuredArrow f.op Y)
      AddCommGrpCat.{u}
    infer_instance
  refine ⟨fun {I} _ => ?_⟩
  rw [modulePullback_eq_pushforward_ringStructureSheafCoreHom]
  exact injective_sheafOfModules_pushforward_obj B S hS p q f τ hp hq hf hτ hPre I

end Injectives

section DirectImage

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] {𝒴 : Type v'} [Category.{w'} 𝒴]
  (p : 𝒳 ⥤ BigFppfOver B S hS) (q : 𝒴 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)
  (f : 𝒳 ⥤ 𝒴) (hf : f ⋙ q = p)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  [f.IsCocontinuous (associatedTopology B S hS p τ) (associatedTopology B S hS q τ)]
  [∀ F : 𝒳ᵒᵖ ⥤ RingCat.{u}, f.op.HasPointwiseRightKanExtension F]

/-- The structure map `𝒪_𝒴 ⟶ f_*𝒪_𝒳` of a 1-morphism of categories fibred in groupoids: the
unit of the right Kan extension adjunction at the structure sheaf of the target, read through the
identification `𝒪_𝒳 = f⁻¹𝒪_𝒴` of Stacks 06TW. -/
noncomputable def moduleDirectImageStructureMap :
    ringStructureSheafCore B S hS q hq τ hτ ⟶
      (f.sheafPushforwardCocontinuous RingCat.{u} (associatedTopology B S hS p τ)
        (associatedTopology B S hS q τ)).obj (ringStructureSheafCore B S hS p hp τ hτ) :=
  ⟨Stacks.SheafOfModules.ranUnitRing f (ringStructureSheafCore B S hS q hq τ hτ).obj ≫
    f.op.ran.map (eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ).symm)⟩

/-- The ring map `𝒪_𝒴(V) ⟶ 𝒪_𝒳(U)` that the structure map cuts out at a leg `(U, ψ)` of the
right Kan extension is restriction of the structure sheaf of the base along `ψ`, read through
Stacks 06TW. -/
theorem scalarπ_moduleDirectImageStructureMap (V : 𝒴ᵒᵖ) (j : StructuredArrow V f.op) :
    Stacks.SheafOfModules.scalarπ f (moduleDirectImageStructureMap B S hS p q hp hq f hf τ hτ).hom
        V j =
      (ringStructureSheafCore B S hS q hq τ hτ).obj.map j.hom ≫
        (eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ).symm).app j.right := by
  subst hf
  have h1 : (moduleDirectImageStructureMap B S hS (f ⋙ q) q hp hq f rfl τ hτ).hom =
      Stacks.SheafOfModules.ranUnitRing f (ringStructureSheafCore B S hS q hq τ hτ).obj :=
    (congrArg (_ ≫ ·) ((congrArg f.op.ran.map (eqToHom_refl _ _)).trans
      (f.op.ran.map_id _))).trans (Category.comp_id _)
  rw [h1]
  refine (Stacks.SheafOfModules.scalarπ_ranUnitRing f _ V j).trans ?_
  rw [eqToHom_app]
  exact (Category.comp_id _).symm

variable [∀ F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{m}, f.op.HasPointwiseRightKanExtension F]

/-- The direct image `f_*` of sheaves of modules along a 1-morphism of categories fibred in
groupoids, at an arbitrary module universe: the canonical direct image
`Stacks.SheafOfModules.pushforwardCocontinuous` along the cocontinuous functor `f`, with the
structure map `moduleDirectImageStructureMap`. -/
noncomputable abbrev moduleDirectImage :
    SheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ) ⥤
      SheafOfModules.{m} (ringStructureSheafCore B S hS q hq τ hτ) :=
  Stacks.SheafOfModules.pushforwardCocontinuous.{m} f
    (moduleDirectImageStructureMap B S hS p q hp hq f hf τ hτ)

/-- **The direct image of sheaves of modules is right adjoint to the inverse image** of
Stacks 06WE, at an arbitrary module universe: `modulePullback ⊣ moduleDirectImage`.

On underlying presheaves of modules the inverse image is restriction along `f` with scalars
transported along Stacks 06TW, and the direct image is the right Kan extension with the module
structure cut out by the transported tautological structure map; the presheaf-level adjunction is
`Stacks.SheafOfModules.pushforward₀RestrictScalarsRanPushforwardAdjunction`, and it restricts to
sheaves along the fully faithful forgetful functors. -/
noncomputable def moduleDirectImageAdjunction :
    modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ ⊣
      moduleDirectImage.{u, v, w, v', w', m} B S hS p q hp hq f hf τ hτ :=
  Adjunction.restrictFullyFaithful
    (iC := SheafOfModules.forget (ringStructureSheafCore B S hS q hq τ hτ))
    (iD := SheafOfModules.forget (ringStructureSheafCore B S hS p hp τ hτ))
    (L := modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ)
    (R := moduleDirectImage.{u, v, w, v', w', m} B S hS p q hp hq f hf τ hτ)
    (Stacks.SheafOfModules.pushforward₀RestrictScalarsRanPushforwardAdjunction.{v, w, v', w', m}
      f (ringStructureSheafCore B S hS q hq τ hτ).obj
      (ringStructureSheafCore B S hS p hp τ hτ).obj
      (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ))
    (SheafOfModules.fullyFaithfulForget _) (SheafOfModules.fullyFaithfulForget _)
    (modulePullbackForgetIso.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).symm
    (Iso.refl _)

/-- **The unit of `f^* ⊣ f_*`, followed by the leg at `(U, ψ)` of the right Kan extension, is the
restriction map along `ψ`**: for a module `M` on `𝒴` and an arrow `ψ : V ⟶ f(U)`, the section of
`f_* f^* M` over `V` that the unit attaches to `m ∈ M(V)` has component `M(ψ)(m)` at `(U, ψ)`. -/
theorem moduleDirectImageAdjunction_unit_app_ranπ
    (M : SheafOfModules.{m} (ringStructureSheafCore B S hS q hq τ hτ)) (V : 𝒴ᵒᵖ)
    (j : StructuredArrow V f.op) :
    (Stacks.SheafOfModules.presheafMap ((moduleDirectImageAdjunction.{u, v, w, v', w', m}
      B S hS p q hp hq f hf τ hτ).unit.app M).val).app V ≫
      Stacks.SheafOfModules.ranπ f.op
        ((modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).obj M).val.presheaf V j =
      M.val.presheaf.map j.hom := by
  have key := Adjunction.map_restrictFullyFaithful_unit_app
    (iC := SheafOfModules.forget (ringStructureSheafCore B S hS q hq τ hτ))
    (iD := SheafOfModules.forget (ringStructureSheafCore B S hS p hp τ hτ))
    (L := modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ)
    (R := moduleDirectImage.{u, v, w, v', w', m} B S hS p q hp hq f hf τ hτ)
    (Stacks.SheafOfModules.pushforward₀RestrictScalarsRanPushforwardAdjunction.{v, w, v', w', m}
        f (ringStructureSheafCore B S hS q hq τ hτ).obj
        (ringStructureSheafCore B S hS p hp τ hτ).obj
        (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ))
    (SheafOfModules.fullyFaithfulForget _) (SheafOfModules.fullyFaithfulForget _)
    (modulePullbackForgetIso.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).symm
    (Iso.refl _) M
  have leg :=
    Stacks.SheafOfModules.pushforward₀RestrictScalarsRanPushforwardAdjunction_unit_app_ranπ f _ _
      (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ) M.val V j
  have aux := Stacks.SheafOfModules.ranπ_presheafMap_comp_ranPushforward_map_apply f _
    (Stacks.SheafOfModules.ranUnitRing f (ringStructureSheafCore B S hS q hq τ hτ).obj ≫
      f.op.ran.map (eqToHom (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ).symm))
    ((Stacks.SheafOfModules.pushforward₀RestrictScalarsRanPushforwardAdjunction.{v, w, v', w', m}
        f (ringStructureSheafCore B S hS q hq τ hτ).obj
        (ringStructureSheafCore B S hS p hp τ hτ).obj
        (ringStructureSheafCore_obj_eq B S hS p q hp hq f hf τ hτ)).unit.app M.val)
    ((modulePullbackForgetIso.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).symm.hom.app M) V j
  ext z
  specialize aux z
  have e1 := congrArg (fun φ => ((Stacks.SheafOfModules.presheafMap φ).app V).hom z) key
  refine (ConcreteCategory.comp_apply _ _ z).trans ?_
  refine (congrArg (Stacks.SheafOfModules.ranπ f.op
    ((modulePullback.{u, v, w, m, v', w'} B S hS p q hp hq f hf τ hτ).obj M).val.presheaf V j).hom
      e1).trans ?_
  refine aux.trans ?_
  exact ConcreteCategory.congr_hom leg z

end DirectImage

/-- An `eqToHom` from an object to itself, in front of a composite ending in an `eqToHom`, may be
dropped, and the trailing pair of `eqToHom`s may be replaced by any other pair with the same
endpoints. -/
theorem _root_.CategoryTheory.eqToHom_comp_comp_eqToHom_of_self {C : Type*} [Category C]
    {A B B₁ B₂ B₃ : C} (h : A = A) (k : A ⟶ B) (e₁ : B = B₁) (e₂ : B₁ = B₂) (e₃ : B = B₃)
    (e₄ : B₃ = B₂) :
    eqToHom h ≫ k ≫ eqToHom e₁ ≫ eqToHom e₂ = k ≫ eqToHom e₃ ≫ eqToHom e₄ := by
  simp

section BaseChange

universe v₁ w₁ v₂ w₂ v₃ w₃

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v₁} [Category.{w₁} 𝒳] {𝒴' : Type v₂} [Category.{w₂} 𝒴']
  {𝒴 : Type v₃} [Category.{w₃} 𝒴]
  (p𝒳 : 𝒳 ⥤ BigFppfOver B S hS) (p𝒴' : 𝒴' ⥤ BigFppfOver B S hS)
  (p𝒴 : 𝒴 ⥤ BigFppfOver B S hS) (f : 𝒳 ⥤ 𝒴) (g : 𝒴' ⥤ 𝒴)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)
  (h𝒳 : p𝒳.IsFiberedInGroupoids) (h𝒴' : p𝒴'.IsFiberedInGroupoids)
  (h𝒴 : p𝒴.IsFiberedInGroupoids) (hfc : f ⋙ p𝒴 = p𝒳) (hgc : g ⋙ p𝒴 = p𝒴')
  (P : TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g ⥤ BigFppfOver B S hS)
  (hP : P.IsFiberedInGroupoids)
  (hPf : TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g ⋙ p𝒳 = P)
  (hPs : TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g ⋙ p𝒴' = P)
  [f.IsCocontinuous (associatedTopology B S hS p𝒳 τ) (associatedTopology B S hS p𝒴 τ)]
  [(TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).IsCocontinuous (associatedTopology B S hS P τ)
    (associatedTopology B S hS p𝒴' τ)]
  [∀ F : 𝒳ᵒᵖ ⥤ RingCat.{u}, f.op.HasPointwiseRightKanExtension F]
  [∀ F : (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)ᵒᵖ ⥤ RingCat.{u},
    (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).op.HasPointwiseRightKanExtension F]
  [∀ F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{m}, f.op.HasPointwiseRightKanExtension F]
  [∀ F : (TwoFibreProductOver p𝒳 p𝒴' p𝒴 f g)ᵒᵖ ⥤ AddCommGrpCat.{m},
    (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).op.HasPointwiseRightKanExtension F]

omit [∀ F : 𝒳ᵒᵖ ⥤ AddCommGrpCat.{m}, f.op.HasPointwiseRightKanExtension F] in
/-- The two ring maps through which a section of `𝒪_{𝒴'}` acts on a leg of the right Kan
extension along the second projection agree with the ones acting on the corresponding leg of the
right Kan extension along `f`: both are restriction of the structure sheaf of the base, the
comparison isomorphism of the 2-fibre product lying over an identity. -/
theorem scalarπ_baseChange (V' : 𝒴'ᵒᵖ)
    (j : StructuredArrow V' (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g).op) :
    (eqToHom (ringStructureSheafCore_obj_eq B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ)).app V' ≫
        Stacks.SheafOfModules.scalarπ f
          (moduleDirectImageStructureMap B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ).hom (g.op.obj V')
          (StructuredArrow.mk (g.op.map j.hom ≫
            (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).op.app j.right)) =
      Stacks.SheafOfModules.scalarπ (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g)
          (moduleDirectImageStructureMap B S hS P p𝒴' hP h𝒴'
            (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) hPs τ hτ).hom V' j ≫
        (eqToHom (ringStructureSheafCore_obj_eq B S hS P p𝒳 hP h𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) hPf τ hτ)).app j.right := by
  rw [scalarπ_moduleDirectImageStructureMap, scalarπ_moduleDirectImageStructureMap]
  subst hfc hgc hPs
  have hv := TwoFibreProductOver.psiIso_hom_vertical (p𝒳 := f ⋙ p𝒴) (p𝒴 := g ⋙ p𝒴)
    (p𝒮 := p𝒴) (F := f) (G := g) j.right.unop
  have hfac := IsHomLift.fac' p𝒴 (𝟙 j.right.unop.base)
    ((TwoFibreProductOver.psiIso (f ⋙ p𝒴) (g ⋙ p𝒴) p𝒴 f g).hom.app j.right.unop)
  simp only [eqToHom_app]
  change eqToHom _ ≫ (BigFppfOver.structureSheaf B S hS).obj.map
      (p𝒴.map ((TwoFibreProductOver.psiIso (f ⋙ p𝒴) (g ⋙ p𝒴) p𝒴 f g).hom.app j.right.unop ≫
        g.map j.hom.unop)).op ≫ eqToHom _ =
    ((BigFppfOver.structureSheaf B S hS).obj.map (p𝒴.map (g.map j.hom.unop)).op ≫
      eqToHom _) ≫ eqToHom _
  rw [p𝒴.map_comp, hfac]
  simp only [op_comp, Functor.map_comp, eqToHom_op, eqToHom_map, Category.id_comp,
    Category.assoc, eqToHom_trans]
  exact eqToHom_comp_comp_eqToHom_of_self _ _ _ _ _ _


/-- **The base change map of Stacks 075H in degree zero, for sheaves of modules**:
`g⁻¹ f_* ⟶ f'_* (g')⁻¹` for the canonical 2-cartesian square, with `g' = fst` and `f' = snd`. -/
def moduleDirectImageBaseChange :
    moduleDirectImage.{u, v₁, w₁, v₃, w₃, m} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ ⋙
        modulePullback.{u, v₂, w₂, m, v₃, w₃} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ ⟶
      modulePullback.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂, m, v₁, w₁} B S hS P p𝒳 hP h𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) hPf τ hτ ⋙
        moduleDirectImage.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂, v₂, w₂, m} B S hS P p𝒴' hP h𝒴'
          (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) hPs τ hτ :=
  letI : p𝒳.IsFibered := h𝒳.isFibered
  letI : p𝒴.IsFibered := h𝒴.isFibered
  letI : p𝒴'.IsFibered := h𝒴'.isFibered
  letI : P.IsFibered := hP.isFibered
  letI := ((h𝒴.isFibredOneMorphism hgc).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  letI := ((h𝒳.isFibredOneMorphism hPf).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS))).1
  Stacks.SheafOfModules.twoSquareComparison (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g)
    ⟨eqToHom (ringStructureSheafCore_obj_eq B S hS P p𝒳 hP h𝒳
      (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) hPf τ hτ)⟩
    ⟨eqToHom (ringStructureSheafCore_obj_eq B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ)⟩
    (moduleDirectImageStructureMap B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ)
    (moduleDirectImageStructureMap B S hS P p𝒴' hP h𝒴'
      (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) hPs τ hτ)
    (scalarπ_baseChange B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴' h𝒴 hfc hgc P hP hPf hPs)

/-- **Stacks 075H in degree zero for sheaves of modules**: the base change map is invertible.
Its underlying map of presheaves of abelian groups is the base change of right Kan extensions along
the opposite of the 2-fibre product square, which is invertible because that square is Guitart
exact (Stacks 075B, `CategoryTheory.TwoFibreProductOver.guitartExact_twoFibreProductSquare`). -/
instance isIso_moduleDirectImageBaseChange :
    IsIso (moduleDirectImageBaseChange.{u, m} B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴' h𝒴 hfc hgc
      P hP hPf hPs) := by
  have : (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).GuitartExact :=
    TwoFibreProductOver.guitartExact_twoFibreProductSquare p𝒳 p𝒴' p𝒴 f g h𝒳 h𝒴' h𝒴 hfc hgc
  have : (baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).op.GuitartExact := inferInstance
  refine @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun M => ?_)
  have h1 : IsIso (((baseChangeTwoSquare p𝒳 p𝒴' p𝒴 f g).op.ranBaseChange
      (D := AddCommGrpCat.{m})).app M.val.presheaf) := inferInstance
  have h2 : IsIso ((sheafToPresheaf _ AddCommGrpCat.{m}).map
      ((SheafOfModules.toSheaf.{m} _).map
        ((moduleDirectImageBaseChange.{u, m} B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴' h𝒴 hfc hgc
          P hP hPf hPs).app M))) := h1
  have h3 := isIso_of_reflects_iso ((SheafOfModules.toSheaf.{m} _).map
        ((moduleDirectImageBaseChange.{u, m} B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴' h𝒴 hfc hgc
          P hP hPf hPs).app M)) (sheafToPresheaf (associatedTopology B S hS p𝒴' τ)
    AddCommGrpCat.{m})
  exact isIso_of_reflects_iso _ (SheafOfModules.toSheaf.{m} _)

/-- **Stacks 075H in degree zero for sheaves of modules**, as an isomorphism
`g⁻¹ f_* ≅ f'_* (g')⁻¹`. -/
def moduleDirectImageBaseChangeIso :
    moduleDirectImage.{u, v₁, w₁, v₃, w₃, m} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ ⋙
        modulePullback.{u, v₂, w₂, m, v₃, w₃} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ ≅
      modulePullback.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂, m, v₁, w₁} B S hS P p𝒳 hP h𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) hPf τ hτ ⋙
        moduleDirectImage.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂, v₂, w₂, m} B S hS P p𝒴' hP h𝒴'
          (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) hPs τ hτ :=
  asIso (moduleDirectImageBaseChange.{u, m} B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴' h𝒴 hfc hgc
    P hP hPf hPs)

section HigherDirectImages

variable [HasSheafify (associatedTopology B S hS p𝒳 τ) AddCommGrpCat.{m}]
  [(associatedTopology B S hS p𝒳 τ).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify (associatedTopology B S hS p𝒴 τ) AddCommGrpCat.{m}]
  [(associatedTopology B S hS p𝒴 τ).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify (associatedTopology B S hS p𝒴' τ) AddCommGrpCat.{m}]
  [(associatedTopology B S hS p𝒴' τ).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasSheafify (associatedTopology B S hS P τ) AddCommGrpCat.{m}]
  [(associatedTopology B S hS P τ).WEqualsLocallyBijective AddCommGrpCat.{m}]
  [HasInjectiveResolutions (SheafOfModules.{m} (ringStructureSheafCore B S hS p𝒳 h𝒳 τ hτ))]
  [HasInjectiveResolutions (SheafOfModules.{m} (ringStructureSheafCore B S hS P hP τ hτ))]
  [(modulePullback.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂, m, v₁, w₁} B S hS P p𝒳 hP h𝒳
    (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) hPf τ hτ).PreservesInjectiveObjects]

open Stacks.SheafOfModules in
/-- The inverse image of sheaves of modules along a 1-morphism of categories fibred in groupoids
is exact. -/
theorem preservesHomology_modulePullback {𝒜 : Type v} [Category.{w} 𝒜] {ℬ : Type v'}
    [Category.{w'} ℬ] (a : 𝒜 ⥤ BigFppfOver B S hS) (b : ℬ ⥤ BigFppfOver B S hS)
    (ha : a.IsFiberedInGroupoids) (hb : b.IsFiberedInGroupoids) (k : 𝒜 ⥤ ℬ) (hk : k ⋙ b = a)
    [HasSheafify (associatedTopology B S hS a τ) AddCommGrpCat.{m}]
    [(associatedTopology B S hS a τ).WEqualsLocallyBijective AddCommGrpCat.{m}]
    [HasSheafify (associatedTopology B S hS b τ) AddCommGrpCat.{m}]
    [(associatedTopology B S hS b τ).WEqualsLocallyBijective AddCommGrpCat.{m}] :
    (modulePullback.{u, v, w, m, v', w'} B S hS a b ha hb k hk τ hτ).PreservesHomology := by
  let : a.IsFibered := ha.isFibered
  let : b.IsFibered := hb.isFibered
  have hc := ((hb.isFibredOneMorphism hk).isContinuous_and_isCocontinuous_inheritedTopology
    (τ.over (B.obj hS)))
  let := hc.1
  let := hc.2
  have := preservesFiniteLimits_modulePullback'.{u, v, w, v', w', m} B S hS a b ha hb k hk τ hτ
  have : PreservesFiniteColimits
      (modulePullback.{u, v, w, m, v', w'} B S hS a b ha hb k hk τ hτ) :=
    PushforwardRightExact.preservesFiniteColimits_pushforward_of_isAlmostCocontinuous
      k (⟨eqToHom (ringStructureSheafCore_obj_eq B S hS a b ha hb k hk τ hτ)⟩ :
        ringStructureSheafCore B S hS a ha τ hτ ⟶ _)
      (isAlmostCocontinuous_of_isCocontinuous k _ _)
  infer_instance

/-- **Stacks 075H for sheaves of modules, in every degree**:
`g⁻¹ Rⁿf_* ≅ Rⁿf'_* (g')⁻¹` on sheaves of modules, naturally, for the canonical 2-cartesian
square, provided `(g')⁻¹` carries injective sheaves of modules to injective ones (which holds when
`g'` is faithful and the apex has equalizers, Stacks 06X2).

The exact `g⁻¹` is pulled out of the right derived functor (`rightDerivedCompIso`), the
degree-zero base change `moduleDirectImageBaseChangeIso` identifies the composites, and the exact,
injective-preserving `(g')⁻¹` is pulled out on the other side (`compRightDerivedIso`). -/
def moduleHigherDirectImageBaseChangeIso (n : ℕ) :
    (moduleDirectImage.{u, v₁, w₁, v₃, w₃, m} B S hS p𝒳 p𝒴 h𝒳 h𝒴 f hfc τ hτ).rightDerived n ⋙
        modulePullback.{u, v₂, w₂, m, v₃, w₃} B S hS p𝒴' p𝒴 h𝒴' h𝒴 g hgc τ hτ ≅
      modulePullback.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂, m, v₁, w₁} B S hS P p𝒳 hP h𝒳
          (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) hPf τ hτ ⋙
        (moduleDirectImage.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂, v₂, w₂, m} B S hS P p𝒴' hP
          h𝒴' (TwoFibreProductOver.snd p𝒳 p𝒴' p𝒴 f g) hPs τ hτ).rightDerived n :=
  haveI := preservesHomology_modulePullback.{u, v₂, w₂, v₃, w₃, m} B S hS τ hτ p𝒴' p𝒴 h𝒴' h𝒴
    g hgc
  haveI := preservesHomology_modulePullback.{u, max (u + 1) v₁ v₂ w₃, max u w₁ w₂, v₁, w₁, m}
    B S hS τ hτ P p𝒳 hP h𝒳 (TwoFibreProductOver.fst p𝒳 p𝒴' p𝒴 f g) hPf
  (Functor.rightDerivedCompIso _ _ n).symm ≪≫
    Functor.rightDerivedIsoOfNatIso
      (moduleDirectImageBaseChangeIso.{u, m} B S hS p𝒳 p𝒴' p𝒴 f g τ hτ h𝒳 h𝒴' h𝒴 hfc hgc
        P hP hPf hPs) n ≪≫
    Functor.compRightDerivedIso _ _ n

end HigherDirectImages

end BaseChange

end AlgebraicGeometry.Stack
