module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PullbackContinuous
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictRanAdjunction
public import StacksFrontier.CategoryTheory.Adjunction.ConjugateCoproduct
public import StacksFrontier.CategoryTheory.Sites.SheafPullbackSumFormula

/-!
# Lower shriek of modules restricted to another site is a direct sum: the ran criterion

Let `(C_n, J_n)`, `(C_m, J_m)` and `(E, L)` be sites, let `v_n : C_n ⥤ E` be continuous and
`v_m : C_m ⥤ E` continuous and cocontinuous, and let `O` be a sheaf of rings on `(E, L)`. Write
`O_n` and `O_m` for its restrictions. Restriction of sheaves of `O`-modules along `v_n` has a
left adjoint `g_{n!}`, and restriction along `v_m` has a right adjoint
(`Stacks.SheafOfModules.RestrictRan.sheafAdjunction`), so `g_{n!}` followed by restriction along
`v_m` is a left adjoint whose right adjoint is the direct image along `v_m` followed by
restriction along `v_n`.

This file gives the module-coefficient counterpart of the ran criterion
`CategoryTheory.Functor.sheafPullbackCompPushforwardIsoCoproductOfRan`: given a family of
continuous functors `t i : C_n ⥤ C_m` together with transformations `τ i : t i ⋙ v_m ⟶ v_n`, if
the right Kan extension along `v_m.op`, evaluated at `v_n U`, is the product over `i` of the
values at `t i U`, then `g_{n!}` followed by restriction along `v_m` is the direct sum over `i`
of the module pullbacks along the `t i`, for the ring maps `O(τ i)`.

The criterion is **not** a transport of the abelian one: its conclusion is about the categories of
modules, and the comparison transformations of right adjoints whose fan has to be a limit are
transformations of module-valued functors, so they have to be produced at the module level. What
is reused is the abelian comparison `CategoryTheory.Functor.ranRestrictComparison`, which is the
underlying transformation of presheaves of abelian groups; the content added is its linearity,
which is `Stacks.SheafOfModules.ranSMul_π` together with
`Stacks.SheafOfModules.RestrictRan.scalarπ_unitRingHom` — the ring map that scalar multiplication
on the right Kan extension acts through at the index `(t U, τ_U)` is exactly `O(τ_U)`, the ring
map along which the summand labelled by `τ` is taken.

## Main definitions

* `Stacks.SheafOfModules.RestrictRan.ringComparison`: the ring map `O_n ⟶ t_* O_m` attached to
  `τ`, the map `O(τ)` of the source, and `…ringComparisonSheaf` for sheaves of rings.
* `Stacks.SheafOfModules.RestrictRan.ranComparisonPresheaf`, `…ranComparisonSheaf`: the
  comparison of right adjoints attached to `τ`, on presheaves resp. sheaves of modules.

## Main results

* `Stacks.Limits.isLimitFanOfReflects`, `Stacks.Limits.isLimitFanOfEvaluation`: a fan is a limit
  as soon as its image under a functor reflecting products is, resp. as soon as it is one at
  every object of the source of a functor category.
* `Stacks.SheafOfModules.RestrictRan.isLimitFanOfModuleSections`: a fan of sheaves of modules is
  a limit as soon as the underlying fan of presheaves of abelian groups is one over every object.
* `Stacks.SheafOfModules.RestrictRan.pullbackCompRestrictIsoCoproductOfRan`: **the ran criterion
  for sheaves of modules.**

## Implementation notes

The limit hypothesis is phrased, exactly as in the abelian criterion, as
`CategoryTheory.Limits.IsLimit` of an explicit `Fan.mk` whose legs are written out in terms of
the Kan extension counit and the given transformations; that is the shape in which such a
decomposition arises from a comma category with a distinguished object in each piece, and it is
what `CategoryTheory.SimplicialSite.isLimitFanRanComponent` produces. It is a statement about
presheaves of abelian groups and about one object of `C_n` at a time, and it is promoted to the
module-level product formula by `…isLimitFanOfModuleSections`: the forgetful functor from sheaves
of modules to presheaves of abelian groups preserves products and reflects isomorphisms, hence
reflects products, and products of presheaves are objectwise.

Passing from the product formula for the right adjoints to the direct-sum formula for the left
adjoints is `CategoryTheory.Adjunction.coproductIsoOfIsLimitFan`, which is stated for an
arbitrary pair of categories and so applies to categories of sheaves of modules unchanged.

The abelian comparison is indexed by a family in
`CategoryTheory.Functor.ranRestrictComparison`, so it is read here at a one-element family;
`ranComparisonAb` hides that.

## References

* [Stacks Project, Tag 09WG](https://stacks.math.columbia.edu/tag/09WG)
* [Stacks Project, Tag 0797](https://stacks.math.columbia.edu/tag/0797)
* [Stacks Project, Tag 0D72](https://stacks.math.columbia.edu/tag/0D72)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor Opposite

namespace Stacks.Limits

universe w v₁ u₁ v₂ u₂ v₃ u₃

variable {I : Type w} {A : Type u₁} [Category.{v₁} A] {B : Type u₂} [Category.{v₂} B]

/-- A functor reflecting products of shape `I` reflects limit fans: if the image fan is a limit,
so was the fan. This is the reflecting counterpart of
`CategoryTheory.Limits.isColimitCofanMapOfPreserves`. -/
def isLimitFanOfReflects (G : A ⥤ B) [ReflectsLimitsOfShape (Discrete I) G] {f : I → A} {P : A}
    (p : ∀ i, P ⟶ f i) (h : IsLimit (Fan.mk (G.obj P) fun i => G.map (p i))) :
    IsLimit (Fan.mk P p) := by
  refine isLimitOfReflects G ?_
  refine (IsLimit.equivOfNatIsoOfIso
    ((Discrete.natIso fun _ => Iso.refl _ :
        Discrete.functor (fun i => G.obj (f i)) ≅ Discrete.functor f ⋙ G))
    (Fan.mk (G.obj P) fun i => G.map (p i))
    (G.mapCone (Fan.mk P p)) (Cone.ext (Iso.refl _) ?_)) h
  intro j
  obtain ⟨j⟩ := j
  simp

/-- A fan in a functor category is a limit as soon as it is one at every object of the source,
because limits in a functor category are computed pointwise. This is the limit counterpart of
`CategoryTheory.Limits.isColimitCofanOfEvaluation`. -/
def isLimitFanOfEvaluation {K : Type u₃} [Category.{v₃} K] {f : I → (K ⥤ B)} {P : K ⥤ B}
    (p : ∀ i, P ⟶ f i) (h : ∀ X : K, IsLimit (Fan.mk (P.obj X) fun i => (p i).app X)) :
    IsLimit (Fan.mk P p) := by
  refine evaluationJointlyReflectsLimits _ fun X => ?_
  refine (IsLimit.equivOfNatIsoOfIso
    ((Discrete.natIso fun _ => Iso.refl _ :
        Discrete.functor (fun i => (f i).obj X) ≅ Discrete.functor f ⋙ (evaluation K B).obj X))
    (Fan.mk (P.obj X) fun i => (p i).app X)
    (((evaluation K B).obj X).mapCone (Fan.mk P p))
    (Cone.ext (Iso.refl _) ?_)) (h X)
  intro j
  obtain ⟨j⟩ := j
  simp

end Stacks.Limits

namespace Stacks.SheafOfModules.RestrictRan

universe w v r v₁ u₁ v₂ u₂ v₃ u₃

section Detection

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C} {O : Sheaf J RingCat.{r}}
  {I : Type w} [Small.{v} I]

/-- A fan of sheaves of modules is a limit as soon as the underlying fan of presheaves of abelian
groups is a limit over every object of the site: the forgetful functor to presheaves of abelian
groups preserves products and reflects isomorphisms, hence reflects products, and products of
presheaves are objectwise. -/
def isLimitFanOfModuleSections {f : I → _root_.SheafOfModules.{v} O}
    {P : _root_.SheafOfModules.{v} O} (p : ∀ i, P ⟶ f i)
    (h : ∀ X : Cᵒᵖ, IsLimit (Fan.mk (P.val.presheaf.obj X)
      fun i => ((PresheafOfModules.toPresheaf O.obj).map (p i).val).app X)) :
    IsLimit (Fan.mk P p) := by
  haveI : ReflectsLimitsOfShape (Discrete I)
      (_root_.SheafOfModules.forget.{v} O ⋙ PresheafOfModules.toPresheaf O.obj) :=
    reflectsLimitsOfShape_of_reflectsIsomorphisms
  exact Stacks.Limits.isLimitFanOfReflects
    (_root_.SheafOfModules.forget.{v} O ⋙ PresheafOfModules.toPresheaf O.obj) p
    (Stacks.Limits.isLimitFanOfEvaluation _ h)

end Detection

section Comparison

variable {Cn : Type u₁} [Category.{v₁} Cn] {Cm : Type u₂} [Category.{v₂} Cm]
  {E : Type u₃} [Category.{v₃} E] (vn : Cn ⥤ E) (vm : Cm ⥤ E) (t : Cn ⥤ Cm) (τ : t ⋙ vm ⟶ vn)
  (O : Eᵒᵖ ⥤ RingCat.{r})

/-- The ring map `O_n ⟶ t_* O_m` attached to a transformation `τ : t ⋙ v_m ⟶ v_n`: restriction
of the presheaf of rings along `τ`. This is the map `O(τ)` of Stacks 0D72, the ring map along
which the summand labelled by `τ` is taken. -/
def ringComparison : vn.op ⋙ O ⟶ t.op ⋙ (vm.op ⋙ O) :=
  Functor.whiskerRight (NatTrans.op τ) O

variable [∀ F : Cmᵒᵖ ⥤ AddCommGrpCat.{v}, vm.op.HasPointwiseRightKanExtension F]

/-- The comparison of presheaves of abelian groups attached to `τ`: restrict the right Kan
extension along `v_m.op` to `C_n` along `v_n.op`, transport along `τ`, and apply the Kan
extension counit. This is `CategoryTheory.Functor.ranRestrictComparison` at a one-element
family. -/
def ranComparisonAb :
    vm.op.ran ⋙ (whiskeringLeft Cnᵒᵖ Eᵒᵖ AddCommGrpCat.{v}).obj vn.op ⟶
      (whiskeringLeft Cnᵒᵖ Cmᵒᵖ AddCommGrpCat.{v}).obj t.op :=
  Functor.ranRestrictComparison AddCommGrpCat.{v} vn vm (fun _ : Unit => t) (fun _ => τ) ()

/-- The index of the comma category attached to an object `U` of `C_n` and the transformation
`τ`: the object `t U` of `C_m` together with the arrow `τ_U : v_m (t U) ⟶ v_n U`. -/
def commaIndex (U : Cnᵒᵖ) : StructuredArrow (vn.op.obj U) vm.op :=
  StructuredArrow.mk (Y := t.op.obj U) ((NatTrans.op τ).app U)

/-- On sections, the abelian comparison is the leg, at the index attached to `τ`, of the limit
cone computing the right Kan extension. -/
lemma ranComparisonAb_app_app (P : Cmᵒᵖ ⥤ AddCommGrpCat.{v}) (U : Cnᵒᵖ) :
    ((ranComparisonAb.{v} vn vm t τ).app P).app U
      = ranπ vm.op P (vn.op.obj U) (commaIndex vn vm t τ U) :=
  rfl

variable [∀ F : Cmᵒᵖ ⥤ RingCat.{r}, vm.op.HasPointwiseRightKanExtension F]

/-- **The abelian comparison is linear.** Scalar multiplication on the direct image acts on the
leg at the index attached to `τ` through the ring map `O(τ)`, which is the ring map the target
restricts scalars along; this is `Stacks.SheafOfModules.ranSMul_π` read through
`scalarπ_unitRingHom`. -/
lemma ranComparisonAb_smul (N : PresheafOfModules.{v} (vm.op ⋙ O)) (U : Cnᵒᵖ)
    (s : O.obj (vn.op.obj U)) :
    smulPresheaf ((ranPushforward.{v} vm (unitRingHom vm (T := O))).obj N) (vn.op.obj U) s ≫
        ((ranComparisonAb.{v} vn vm t τ).app N.presheaf).app U
      = ((ranComparisonAb.{v} vn vm t τ).app N.presheaf).app U ≫
        smulPresheaf N (t.op.obj U) ((ringComparison vn vm t τ O).app U s) := by
  rw [ranComparisonAb_app_app]
  show ranSMul vm (unitRingHom vm (T := O)) N (vn.op.obj U) s ≫
      ranπ vm.op N.presheaf (vn.op.obj U) (commaIndex vn vm t τ U) = _
  rw [ranSMul_π, scalarπ_unitRingHom]
  rfl

/-- **The comparison of right adjoints on presheaves of modules.** The direct image along `v_m`
followed by restriction along `v_n` maps to restriction along `t` over the ring map `O(τ)`; on
underlying presheaves of abelian groups it is `ranComparisonAb`. -/
def ranComparisonPresheaf :
    ranPushforward.{v} vm (unitRingHom vm (T := O)) ⋙ PresheafOfModules.pushforward₀.{v} vn O ⟶
      PresheafOfModules.pushforward.{v} (ringComparison vn vm t τ O) where
  app N := PresheafOfModules.homMk ((ranComparisonAb.{v} vn vm t τ).app N.presheaf)
    (fun U s x => ConcreteCategory.congr_hom
      (ranComparisonAb_smul.{v} vn vm t τ O N U s) x)
  naturality _ _ f := (PresheafOfModules.toPresheaf _).map_injective
    ((ranComparisonAb.{v} vn vm t τ).naturality (presheafMap f))

end Comparison

section Sheaf

variable {Cn : Type u₁} [Category.{v₁} Cn] {Cm : Type u₂} [Category.{v₂} Cm]
  {E : Type u₃} [Category.{v₃} E] (vn : Cn ⥤ E) (vm : Cm ⥤ E)
  (Jn : GrothendieckTopology Cn) (Jm : GrothendieckTopology Cm) (L : GrothendieckTopology E)
  [vn.IsContinuous Jn L] [vm.IsContinuous Jm L] [vm.IsCocontinuous Jm L]
  (O : Sheaf L RingCat.{r}) (t : Cn ⥤ Cm) (τ : t ⋙ vm ⟶ vn) [t.IsContinuous Jn Jm]
  [∀ F : Cmᵒᵖ ⥤ RingCat.{r}, vm.op.HasPointwiseRightKanExtension F]
  [∀ F : Cmᵒᵖ ⥤ AddCommGrpCat.{v}, vm.op.HasPointwiseRightKanExtension F]

/-- The ring map `O_n ⟶ t_* O_m` of sheaves of rings attached to `τ`. -/
def ringComparisonSheaf :
    ringSheaf vn Jn L O ⟶
      (t.sheafPushforwardContinuous RingCat.{r} Jn Jm).obj (ringSheaf vm Jm L O) :=
  ⟨ringComparison vn vm t τ O.obj⟩

/-- **The comparison of right adjoints on sheaves of modules**: the direct image along `v_m`
followed by restriction along `v_n` maps to the direct image along `t` over `O(τ)`. -/
def ranComparisonSheaf :
    pushforwardCocontinuous.{v} vm (sheafUnit vm Jm L O) ⋙
        _root_.SheafOfModules.pushforward.{v} (F := vn) (𝟙 (ringSheaf vn Jn L O)) ⟶
      _root_.SheafOfModules.pushforward.{v} (ringComparisonSheaf vn vm Jn Jm L O t τ) where
  app M := ⟨(ranComparisonPresheaf.{v} vn vm t τ O.obj).app M.val⟩
  naturality _ _ f :=
    _root_.SheafOfModules.hom_ext ((ranComparisonPresheaf.{v} vn vm t τ O.obj).naturality f.val)

end Sheaf

section Criterion

variable {I : Type w} {Cn : Type u₁} [Category.{v₁} Cn] {Cm : Type u₂} [Category.{v₂} Cm]
  {E : Type u₃} [Category.{v₃} E] (vn : Cn ⥤ E) (vm : Cm ⥤ E)
  (Jn : GrothendieckTopology Cn) (Jm : GrothendieckTopology Cm) (L : GrothendieckTopology E)
  [vn.IsContinuous Jn L] [vm.IsContinuous Jm L] [vm.IsCocontinuous Jm L]
  (O : Sheaf L RingCat.{r}) (t : I → (Cn ⥤ Cm)) (τ : ∀ i, t i ⋙ vm ⟶ vn)
  [ht : ∀ i, (t i).IsContinuous Jn Jm]
  [∀ F : Cmᵒᵖ ⥤ RingCat.{r}, vm.op.HasPointwiseRightKanExtension F]
  [∀ F : Cmᵒᵖ ⥤ AddCommGrpCat.{v}, vm.op.HasPointwiseRightKanExtension F]
  [Small.{v} I]
  [(_root_.SheafOfModules.pushforward.{v} (F := vn) (𝟙 (ringSheaf vn Jn L O))).IsRightAdjoint]
  [∀ i, (_root_.SheafOfModules.pushforward.{v}
    (ringComparisonSheaf vn vm Jn Jm L O (t i) (τ i))).IsRightAdjoint]
  [HasCoproduct fun i => _root_.SheafOfModules.pullback.{v}
    (ringComparisonSheaf vn vm Jn Jm L O (t i) (τ i))]

/-- **The ran criterion for sheaves of modules.** If the right Kan extension along `v_m.op`,
evaluated at `v_n U` for an object `U` of `C_n`, is the product over `i` of the values at
`t i U`, with the transports along the `τ i` followed by the Kan extension counit as projections,
then lower shriek of modules along `v_n` followed by restriction along `v_m` is the direct sum
over `i` of the module pullbacks along the `t i`, for the ring maps `O(τ i)`.

This is the module counterpart of
`CategoryTheory.Functor.sheafPullbackCompPushforwardIsoCoproductOfRan`, and the hypothesis is the
same one: it speaks of presheaves of abelian groups and of one object of `C_n` at a time. -/
def pullbackCompRestrictIsoCoproductOfRan
    (hfan : ∀ (P : Cmᵒᵖ ⥤ AddCommGrpCat.{v}) (U : Cn),
      IsLimit (Fan.mk ((vm.op.ran.obj P).obj (op (vn.obj U)))
        fun i => (vm.op.ran.obj P).map ((τ i).app U).op ≫
          (vm.op.ranCounit.app P).app (op ((t i).obj U)))) :
    (∐ fun i => _root_.SheafOfModules.pullback.{v}
        (ringComparisonSheaf vn vm Jn Jm L O (t i) (τ i))) ≅
      _root_.SheafOfModules.pullback.{v} (F := vn) (𝟙 (ringSheaf vn Jn L O)) ⋙
        _root_.SheafOfModules.pushforward.{v} (F := vm) (𝟙 (ringSheaf vm Jm L O)) :=
  Adjunction.coproductIsoOfIsLimitFan
    ((_root_.SheafOfModules.pullbackPushforwardAdjunction.{v}
        (F := vn) (𝟙 (ringSheaf vn Jn L O))).comp
      (sheafAdjunction.{v} vm Jm L O))
    (fun i => _root_.SheafOfModules.pullbackPushforwardAdjunction.{v}
      (ringComparisonSheaf vn vm Jn Jm L O (t i) (τ i)))
    (fun i => ranComparisonSheaf.{v} vn vm Jn Jm L O (t i) (τ i))
    (fun M => isLimitFanOfModuleSections _ (fun U => by
      obtain ⟨U⟩ := U
      exact hfan M.val.presheaf U))

end Criterion

end Stacks.SheafOfModules.RestrictRan

end
