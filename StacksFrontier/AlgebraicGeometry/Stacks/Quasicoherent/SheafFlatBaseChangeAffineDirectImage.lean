module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.CartesianTransportAlongPushout
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ModuleDirectImageInitialChart
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.SheafFlatBaseChangeAffineChartLocality
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FppfHigherDirectImageVanishingOfTerminalFibres

/-!
# The direct image of the faithful `LQCoh^fbc` between affine-representable stacks

Let `f : 𝒳 ⟶ 𝒴` be a 1-morphism of algebraic stacks over `S`, both representable by affine
schemes, and `F` a module on the fppf site of `𝒳`, with sections in `Type (u + 1)`, in the
faithful `LQCoh^fbc(𝒪_𝒳)` (locally quasi-coherent with the flat base change property of
Stacks 0762 read with the pullback of sheaves). This file proves that `f_* F = R⁰f_* F` lies in
`LQCoh^fbc(𝒪_𝒴)`: the degree-zero half of the affine case (clause (4)) of Stacks 0770 for
`LQCoh^fbc`, which Stacks 0771 part (4)(b) consumes.

The class is detected on the affine charts `y : Sch/V ⟶ 𝒴`
(`AlgebraicGeometry.Stack.sheafFlatBaseChangeModuleRule_of_objectStackMap`), and the inverse
image of `f_* F` along a chart is the direct image of the base change (Stacks 075H in degree
zero). So everything comes down to a 1-morphism `q : 𝒵 ⥤ Sch/V`, `V` affine, from a category
fibred in groupoids with a terminal object `t` over an affine scheme `T`:

* the base change `x_w ⟶ t` of `t` to an object `w` of `Sch/V` (a cartesian arrow over
  `T ×_V w ⟶ T`) is an initial structured arrow, so `(q_* G)(w) = G(x_w)`
  (`AlgebraicGeometry.Stack.isInitialStructuredArrowOfIsPullback`,
  `AlgebraicGeometry.Stack.exists_isPullback_baseChangeChart`);
* this identification is semilinear and compatible with restriction
  (`AlgebraicGeometry.Stack.moduleSheafPushforwardEvaluation_smul`,
  `AlgebraicGeometry.Stack.moduleSheafPushforwardEvaluation_restriction_apply`);
* along a flat arrow `w₁ ⟶ w₂` of affine objects the base changes form a fibre product of
  affine schemes, so the arrow `x_{w₁} ⟶ x_{w₂}` is flat and the rings form a pushout square;
  cartesianness of `G` along it gives cartesianness of `q_* G` along `w₁ ⟶ w₂`
  (`Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_pushout_transport`).

## Main results

* `AlgebraicGeometry.Stack.isCartesianOnFlatAffineArrows_moduleSheafPushforward`: the direct image
  to `Sch/V` of a module cartesian on flat arrows between objects over affine schemes is again
  cartesian on such arrows.
* `Stack.AlgebraicStacks.sheafFlatBaseChangeModuleRule_fppfHigherDirectImage_zero`: **`R⁰f_*`
  carries `LQCoh^fbc` into `LQCoh^fbc`** for `f` between stacks representable by affine schemes,
  at module universe `u + 1`.

No `@[stacks]` attribute is claimed: this is an input of the proof of Stacks 0771 part (4)(b).

## References

* [Stacks Project, Tag 0770](https://stacks.math.columbia.edu/tag/0770)
* [Stacks Project, Tag 0771](https://stacks.math.columbia.edu/tag/0771)
* [Stacks Project, Tag 075H](https://stacks.math.columbia.edu/tag/075H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.PresheafOfModules

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck
  Stacks.Cohomology.SiteModules.moduleSheavesEnoughInjectives

namespace AlgebraicGeometry.Stack

universe u w

section BaseChangeChart

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒵 : Type (u + 1)} [Category.{u} 𝒵] {V : BigFppfOver B S hS} (q : 𝒵 ⥤ Over V)
  (hP : (q ⋙ Over.forget V).IsFiberedInGroupoids) {t : 𝒵} (ht : IsTerminal t)

/-- **The chart of a base change is initial.** Let `q : 𝒵 ⥤ Sch/V` be a 1-morphism from a category
fibred in groupoids with a terminal object `t`. For an arrow `c : x ⟶ t` and an arrow
`a : q(x) ⟶ w` of `Sch/V` such that the square of `c` and `a` over `q(t) ⟶ V ⟵ w` is a fibre
product, the structured arrow `w ⟶ q(x)` given by `a` is initial: `x` is the base change of `t`
to `w`. -/
def isInitialStructuredArrowOfIsPullback {x : 𝒵} (c : x ⟶ t) {w : Over V} (a : q.obj x ⟶ w)
    (hpb : IsPullback ((q ⋙ Over.forget V).map c) a.left (q.obj t).hom w.hom) :
    IsInitial (StructuredArrow.mk (Y := op x) a.op : StructuredArrow (op w) q.op) := by
  haveI hc : (q ⋙ Over.forget V).IsStronglyCartesian ((q ⋙ Over.forget V).map c) c :=
    hP.isStronglyCartesian_homLift _ _
  have hw : ∀ (x' : 𝒵) (b : q.obj x' ⟶ w),
      (q ⋙ Over.forget V).map (ht.from x') ≫ (q.obj t).hom = b.left ≫ w.hom :=
    fun x' b => (Over.w (q.map (ht.from x'))).trans (Over.w b).symm
  let u : ∀ (x' : 𝒵) (b : q.obj x' ⟶ w),
      (q ⋙ Over.forget V).obj x' ⟶ (q ⋙ Over.forget V).obj x :=
    fun x' b => hpb.lift _ _ (hw x' b)
  let m : ∀ (x' : 𝒵) (b : q.obj x' ⟶ w), x' ⟶ x := fun x' b =>
    Functor.IsStronglyCartesian.map (q ⋙ Over.forget V) ((q ⋙ Over.forget V).map c) c
      (hpb.lift_fst _ _ (hw x' b)).symm (ht.from x')
  have hmlift : ∀ (x' : 𝒵) (b : q.obj x' ⟶ w), (q ⋙ Over.forget V).map (m x' b) = u x' b :=
    fun x' b => (IsHomLift.eq_of_isHomLift (p := q ⋙ Over.forget V) (u x' b) (m x' b)).symm
  have hfac : ∀ (x' : 𝒵) (b : q.obj x' ⟶ w), q.map (m x' b) ≫ a = b := fun x' b => by
    apply Over.OverMorphism.ext
    change (q ⋙ Over.forget V).map (m x' b) ≫ a.left = b.left
    rw [hmlift]
    exact hpb.lift_snd _ _ _
  refine IsInitial.ofUniqueHom
    (fun Bo => StructuredArrow.homMk (m Bo.right.unop Bo.hom.unop).op
      (Quiver.Hom.unop_inj (hfac _ _))) ?_
  intro Bo k
  apply StructuredArrow.ext
  apply Quiver.Hom.unop_inj
  have hk : q.map k.right.unop ≫ a = Bo.hom.unop :=
    congrArg Quiver.Hom.unop (StructuredArrow.w k)
  have hu : (q ⋙ Over.forget V).map k.right.unop = u _ Bo.hom.unop := by
    apply hpb.hom_ext
    · rw [hpb.lift_fst, ← Functor.map_comp]
      exact congrArg _ (ht.hom_ext _ _)
    · rw [hpb.lift_snd]
      exact congrArg CommaMorphism.left hk
  have : (q ⋙ Over.forget V).IsHomLift (u _ Bo.hom.unop) k.right.unop := by
    rw [← hu]
    infer_instance
  exact Functor.IsStronglyCartesian.map_uniq (q ⋙ Over.forget V) ((q ⋙ Over.forget V).map c) c
    (hpb.lift_fst _ _ (hw _ Bo.hom.unop)).symm (ht.from _) k.right.unop (ht.hom_ext _ _)

include hP in
/-- **Every object of `Sch/V` has a base-change chart**: a cartesian arrow `c : x ⟶ t` over the
first projection of `q(t) ×_V w`, with the second projection as an arrow `q(x) ⟶ w` of `Sch/V`. -/
theorem exists_isPullback_baseChangeChart (w : Over V) :
    ∃ (x : 𝒵) (c : x ⟶ t) (a : q.obj x ⟶ w),
      IsPullback ((q ⋙ Over.forget V).map c) a.left (q.obj t).hom w.hom := by
  have : (q ⋙ Over.forget V).IsFibered := hP.isFibered
  obtain ⟨x, c, hc⟩ := Functor.IsPreFibered.exists_isCartesian' (p := q ⋙ Over.forget V) (a := t)
    (pullback.fst (q.obj t).hom w.hom)
  have e : (q ⋙ Over.forget V).obj x = pullback (q.obj t).hom w.hom :=
    IsHomLift.domain_eq (q ⋙ Over.forget V) (pullback.fst (q.obj t).hom w.hom) c
  have hfac : (q ⋙ Over.forget V).map c = eqToHom e ≫ pullback.fst (q.obj t).hom w.hom := by
    rw [IsHomLift.fac' (q ⋙ Over.forget V) (pullback.fst (q.obj t).hom w.hom) c]
    simp
  have hx : (eqToHom e ≫ pullback.snd (q.obj t).hom w.hom) ≫ w.hom = (q.obj x).hom := by
    rw [Category.assoc, ← pullback.condition, ← Category.assoc, ← hfac]
    exact Over.w (q.map c)
  refine ⟨x, c, Over.homMk (eqToHom e ≫ pullback.snd _ _) hx, ?_⟩
  refine IsPullback.of_iso_pullback ⟨?_⟩ (eqToIso e) hfac.symm rfl
  change (q ⋙ Over.forget V).map c ≫ (q.obj t).hom = (eqToHom e ≫ pullback.snd _ _) ≫ w.hom
  rw [hx]
  exact Over.w (q.map c)

end BaseChangeChart

section EvaluationRestriction

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒵 : Type (u + 1)} [Category.{u} 𝒵] {𝒲 : Type (u + 1)} [Category.{u} 𝒲]
  (p : 𝒵 ⥤ BigFppfOver B S hS) (q : 𝒲 ⥤ BigFppfOver B S hS)
  (hp : p.IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids) (F : 𝒵 ⥤ 𝒲) (hF : F ⋙ q = p)

attribute [local irreducible] ringStructureSheafCore moduleSheafPushforward

/-- **The evaluation of the direct image at structured arrows is compatible with restriction.**
For an arrow `φ : z ⟶ z'` of the target, structured arrows `A` at `z` and `A'` at `z'`, and an
arrow `ψ` between their sources over `φ`, restricting along `φ` and evaluating at `A` is evaluating
at `A'` and restricting along `ψ`. -/
theorem moduleSheafPushforwardEvaluation_restriction
    (N : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    {z z' : 𝒲} (φ : z ⟶ z') (A : StructuredArrow (op z) F.op) (A' : StructuredArrow (op z') F.op)
    (ψ : A.right.unop ⟶ A'.right.unop) (h : F.map ψ ≫ A'.hom.unop = A.hom.unop ≫ φ) :
    ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj
        ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
          B.topology le_rfl).obj N)).map φ.op ≫
      moduleSheafPushforwardEvaluation B S hS p q hp hq F hF N A =
    moduleSheafPushforwardEvaluation B S hS p q hp hq F hF N A' ≫
      ((SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj N).map ψ.op := by
  let P := (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).obj
    ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
      B.topology le_rfl).obj N)
  let ε := (modulePullbackCompToPresheafIso.{u, u + 1, u, u + 1, u, u} B S hS p q hp hq F hF
        B.topology le_rfl).inv.app
        ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
          B.topology le_rfl).obj N) ≫
      (SheafOfModules.forget _ ⋙ PresheafOfModules.toPresheaf _).map
        ((moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
          B.topology le_rfl).counit.app N)
  have h' : φ.op ≫ A.hom = A'.hom ≫ (F.map ψ).op := Quiver.Hom.unop_inj h.symm
  change P.map φ.op ≫ P.map A.hom ≫ ε.app A.right =
    (P.map A'.hom ≫ ε.app A'.right) ≫ _
  rw [← Category.assoc, ← Functor.map_comp, h', Functor.map_comp, Category.assoc,
    Category.assoc]
  exact congrArg (P.map A'.hom ≫ ·) (ε.naturality ψ.op)

/-- `AlgebraicGeometry.Stack.moduleSheafPushforwardEvaluation_restriction` on sections. -/
theorem moduleSheafPushforwardEvaluation_restriction_apply
    (N : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    {z z' : 𝒲} (φ : z ⟶ z') (A : StructuredArrow (op z) F.op) (A' : StructuredArrow (op z') F.op)
    (ψ : A.right.unop ⟶ A'.right.unop) (h : F.map ψ ≫ A'.hom.unop = A.hom.unop ≫ φ)
    (n : ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
      B.topology le_rfl).obj N).val.obj (op z')) :
    moduleSheafPushforwardEvaluation B S hS p q hp hq F hF N A
        (((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p q hp hq F hF
          B.topology le_rfl).obj N).val.map φ.op n) =
      N.val.map ψ.op (moduleSheafPushforwardEvaluation B S hS p q hp hq F hF N A' n) :=
  ConcreteCategory.congr_hom
    (moduleSheafPushforwardEvaluation_restriction B S hS p q hp hq F hF N φ A A' ψ h) n

end EvaluationRestriction

section EvaluationSmul

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒵 : Type (u + 1)} [Category.{u} 𝒵] {𝒲 : Type (u + 1)} [Category.{u} 𝒲]
  (q : 𝒲 ⥤ BigFppfOver B S hS) (F : 𝒵 ⥤ 𝒲)
  (hp : (F ⋙ q).IsFiberedInGroupoids) (hq : q.IsFiberedInGroupoids)

/-- **The evaluation of the direct image at a structured arrow is semilinear** along the
restriction of functions along the arrow. -/
theorem moduleSheafPushforwardEvaluation_smul
    (N : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS (F ⋙ q) hp B.topology le_rfl))
    {z : 𝒲} (A : StructuredArrow (op z) F.op)
    (r : (ringStructureSheafCore B S hS q hq B.topology le_rfl).obj.obj (op z))
    (n : ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS (F ⋙ q) q hp hq F rfl
      B.topology le_rfl).obj N).val.obj (op z)) :
    moduleSheafPushforwardEvaluation B S hS (F ⋙ q) q hp hq F rfl N A (r • n) =
      @id (N.val.obj A.right : Type (u + 1))
        (@id ((ringStructureSheafCore B S hS (F ⋙ q) hp B.topology le_rfl).obj.obj A.right :
            Type u)
          (((ringStructureSheafCore B S hS q hq B.topology le_rfl).obj.map A.hom).hom r) •
        @id (N.val.obj A.right : Type (u + 1))
          (moduleSheafPushforwardEvaluation B S hS (F ⋙ q) q hp hq F rfl N A n)) := by
  have h₁ := PresheafOfModules.map_smul ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS
    (F ⋙ q) q hp hq F rfl B.topology le_rfl).obj N).val A.hom r n
  have h₂ := (((moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS (F ⋙ q) q hp hq F rfl
      B.topology le_rfl).counit.app N).val.app A.right).hom.map_smul
      (((ringStructureSheafCore B S hS q hq B.topology le_rfl).obj.map A.hom).hom r)
      (((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS (F ⋙ q) q hp hq F rfl
        B.topology le_rfl).obj N).val.map A.hom n)
  exact (congrArg (((moduleSheafAdjunction.{u, u + 1, u, u, u + 1, u} B S hS (F ⋙ q) q hp hq F
      rfl B.topology le_rfl).counit.app N).val.app A.right).hom h₁).trans h₂

end EvaluationSmul

section DirectImageCartesian

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {𝒵 : Type (u + 1)} [Category.{u} 𝒵] {V : BigFppfOver B S hS} (q : 𝒵 ⥤ Over V)
  (hP : (q ⋙ Over.forget V).IsFiberedInGroupoids) (hV : (Over.forget V).IsFiberedInGroupoids)

/-- **The direct image to `Sch/V` from a category with a terminal object over an affine scheme
is cartesian on flat arrows between affine objects.** Let `q : 𝒵 ⥤ Sch/V` be a 1-morphism of
categories fibred in groupoids, `V` affine, and `t` a terminal object of `𝒵` over an affine
scheme `T`. If a module `G` on `𝒵` is cartesian on flat arrows between objects over affine
schemes, so is its direct image `q_* G`: its sections over `w` are those of `G` over the base
change of `t` to `w`, the base change of a flat arrow `w₁ ⟶ w₂` is flat, and the rings of the
base changes are the tensor products (Stacks 01I6 for affine schemes). -/
theorem isCartesianOnFlatAffineArrows_moduleSheafPushforward {t : 𝒵} (ht : IsTerminal t)
    (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj ((q ⋙ Over.forget V).obj t)))
    (hVa : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (G : SheafOfModules.{u + 1}
      (ringStructureSheafCore B S hS (q ⋙ Over.forget V) hP B.topology le_rfl))
    (hG : IsCartesianOnFlatAffineArrows.{u, u + 1, u, u} B S hS (q ⋙ Over.forget V) hP
      (etaleTopology B) (etaleTopology_le_topology B) G.val) :
    IsCartesianOnFlatAffineArrows.{u, u + 1, u, u} B S hS (Over.forget V) hV
      (etaleTopology B) (etaleTopology_le_topology B)
      ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS (q ⋙ Over.forget V)
        (Over.forget V) hP hV q rfl B.topology le_rfl).obj G).val := by
  intro w₁ w₂ φ hφ hw₁ hw₂
  obtain ⟨x₁, c₁, a₁, h₁⟩ := exists_isPullback_baseChangeChart B S hS q hP (t := t) w₁
  obtain ⟨x₂, c₂, a₂, h₂⟩ := exists_isPullback_baseChangeChart B S hS q hP (t := t) w₂
  let A₁ : StructuredArrow (op w₁) q.op := StructuredArrow.mk (Y := op x₁) a₁.op
  let A₂ : StructuredArrow (op w₂) q.op := StructuredArrow.mk (Y := op x₂) a₂.op
  let hA₁ := isInitialStructuredArrowOfIsPullback B S hS q hP ht c₁ a₁ h₁
  let hA₂ := isInitialStructuredArrowOfIsPullback B S hS q hP ht c₂ a₂ h₂
  let k := hA₂.to (StructuredArrow.mk (Y := op x₁) (a₁ ≫ φ).op)
  let ψ : x₁ ⟶ x₂ := k.right.unop
  have hk : q.map ψ ≫ a₂ = a₁ ≫ φ := congrArg Quiver.Hom.unop (StructuredArrow.w k)
  have hψc : ψ ≫ c₂ = c₁ := ht.hom_ext _ _
  have hsq : IsPullback ((q ⋙ Over.forget V).map ψ) a₁.left a₂.left φ.left := by
    refine IsPullback.of_right ?_ (congrArg CommaMorphism.left hk) h₂
    rw [← Functor.map_comp, hψc, Over.w φ]
    exact h₁
  have : PreservesLimitsOfShape WalkingCospan (BigFppfOver.toScheme B S hS) :=
    Space.preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hsqS := hsq.map (BigFppfOver.toScheme B S hS)
  have h₁S := h₁.map (BigFppfOver.toScheme B S hS)
  have h₂S := h₂.map (BigFppfOver.toScheme B S hS)
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj w₁.left) := hw₁
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj w₂.left) := hw₂
  have : IsAffine ((BigFppfOver.toScheme B S hS).obj (q.obj t).left) := hT
  have hx₁ : IsAffine ((BigFppfOver.toScheme B S hS).obj ((q ⋙ Over.forget V).obj x₁)) :=
    IsAffine.of_isPullback h₁S
  have hx₂ : IsAffine ((BigFppfOver.toScheme B S hS).obj ((q ⋙ Over.forget V).obj x₂)) :=
    IsAffine.of_isPullback h₂S
  have hψflat : Flat ((BigFppfOver.toScheme B S hS).map ((q ⋙ Over.forget V).map ψ)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (P := @Flat) hsqS.flip
      (show Flat ((BigFppfOver.toScheme B S hS).map φ.left) from hφ)
  have hGψ := hG ψ hψflat hx₁ hx₂
  have := hx₁
  have := hx₂
  have hpo := isPushout_appTop_of_isPullback hsqS.flip
  let R := (structureSheaf B S hS (Over.forget V) hV (etaleTopology B)
    (etaleTopology_le_topology B)).obj
  let R' := (structureSheaf B S hS (q ⋙ Over.forget V) hP (etaleTopology B)
    (etaleTopology_le_topology B)).obj
  let N := (moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS (q ⋙ Over.forget V)
    (Over.forget V) hP hV q rfl B.topology le_rfl).obj G
  have hi₁ := isIso_moduleSheafPushforwardEvaluation B S hS (q ⋙ Over.forget V) (Over.forget V)
    hP hV q rfl G A₁ hA₁
  have hi₂ := isIso_moduleSheafPushforwardEvaluation B S hS (q ⋙ Over.forget V) (Over.forget V)
    hP hV q rfl G A₂ hA₂
  let e₁ : (N.val.obj (op w₁)) ≃+ (G.val.obj (op x₁)) :=
    (@asIso _ _ _ _ (moduleSheafPushforwardEvaluation B S hS (q ⋙ Over.forget V) (Over.forget V)
      hP hV q rfl G A₁) hi₁).addCommGroupIsoToAddEquiv
  let e₂ : (N.val.obj (op w₂)) ≃+ (G.val.obj (op x₂)) :=
    (@asIso _ _ _ _ (moduleSheafPushforwardEvaluation B S hS (q ⋙ Over.forget V) (Over.forget V)
      hP hV q rfl G A₂) hi₂).addCommGroupIsoToAddEquiv
  refine Stacks.PresheafOfModules.bijective_restrictionBaseChange_of_pushout_transport.{u, u + 1, u,
    u + 1, u, u + 1}
    (R := R) (R' := R') N.val G.val φ ψ (R.map a₁.op) (R.map a₂.op) hpo e₁ e₂
    (moduleSheafPushforwardEvaluation_smul B S hS (Over.forget V) q hP hV G A₁)
    (moduleSheafPushforwardEvaluation_smul B S hS (Over.forget V) q hP hV G A₂)
    (moduleSheafPushforwardEvaluation_restriction_apply B S hS (q ⋙ Over.forget V)
      (Over.forget V) hP hV q rfl G φ A₁ A₂ ψ hk) hGψ

/-- `AlgebraicGeometry.Stack.isCartesianOnFlatAffineArrows_moduleSheafPushforward` for a source
whose structure functor is only propositionally `q ⋙ Over.forget V`. -/
theorem isCartesianOnFlatAffineArrows_moduleSheafPushforward_of_comp_eq
    (p : 𝒵 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids) (hqp : q ⋙ Over.forget V = p)
    {t : 𝒵} (ht : IsTerminal t) (hT : IsAffine ((BigFppfOver.toScheme B S hS).obj (p.obj t)))
    (hVa : IsAffine ((BigFppfOver.toScheme B S hS).obj V))
    (G : SheafOfModules.{u + 1} (ringStructureSheafCore B S hS p hp B.topology le_rfl))
    (hG : IsCartesianOnFlatAffineArrows.{u, u + 1, u, u} B S hS p hp
      (etaleTopology B) (etaleTopology_le_topology B) G.val) :
    IsCartesianOnFlatAffineArrows.{u, u + 1, u, u} B S hS (Over.forget V) hV
      (etaleTopology B) (etaleTopology_le_topology B)
      ((moduleSheafPushforward.{u, u + 1, u, u, u + 1, u} B S hS p (Over.forget V) hp hV q hqp
        B.topology le_rfl).obj G).val := by
  subst hqp
  exact isCartesianOnFlatAffineArrows_moduleSheafPushforward B S hS q hp hV ht hT hVa G hG

end DirectImageCartesian

section Transfer

universe m

variable {C : Type*} [Category C] {R : Cᵒᵖ ⥤ CommRingCat.{u}}

/-- Cartesianness along an arrow transfers along an isomorphism of presheaves of modules. -/
theorem bijective_restrictionBaseChange_of_iso
    {M N : PresheafOfModules.{max m u} (R ⋙ forget₂ CommRingCat RingCat)} (e : M ≅ N)
    {X Y : Cᵒᵖ} (f : X ⟶ Y) (hM : Function.Bijective (restrictionBaseChange M f)) :
    Function.Bijective (restrictionBaseChange N f) := by
  have : IsIso (restrictionBaseChange M f) := (ConcreteCategory.isIso_iff_bijective _).2 hM
  have := Stacks.PresheafOfModules.isIso_restrictionBaseChange_of_iso e f
  exact ConcreteCategory.bijective_of_isIso _

end Transfer

end AlgebraicGeometry.Stack

namespace AlgebraicGeometry.Stack.AlgebraicStacks

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)

attribute [local instance] hasSheafify_fppfAssociatedTopology
  wEqualsLocallyBijective_fppfAssociatedTopology

/-- **The affine case of Stacks 0770 in degree zero, for the faithful `LQCoh^fbc` at module
universe `u + 1`**: the direct image `R⁰f_* = f_*` along a 1-morphism between stacks
representable by affine schemes carries `LQCoh^fbc(𝒪_𝒳)` into `LQCoh^fbc(𝒪_𝒴)`. Over the
affine chart `y : Sch/V ⟶ 𝒴` the inverse image of `f_* F` is the direct image of the base change
(Stacks 075H in degree zero), whose source has a terminal object over an affine scheme. -/
theorem sheafFlatBaseChangeModuleRule_fppfHigherDirectImage_zero
    {𝒳 𝒴 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ 𝒴) (h𝒳 : IsAffineRepresentable B S hS 𝒳) (h𝒴 : IsAffineRepresentable B S hS 𝒴)
    (F : fppfModules B S hS 𝒳) (hF : sheafFlatBaseChangeModuleRule B S hS E h 𝒳 F) :
    sheafFlatBaseChangeModuleRule B S hS E h 𝒴 ((fppfHigherDirectImage B S hS f 0).obj F) := by
  refine sheafFlatBaseChangeModuleRule_of_objectStackMap _ fun y hy => ?_
  let g := objectStackMap B S hS 𝒴 y
  let V := 𝒴.val.val.p.obj y
  have : (schemeStack.{u, w} B S hS V).val.val.p.Faithful :=
    inferInstanceAs (Over.forget V).Faithful
  let Psq := twoFibreProductSquareAlgebraicStacks B S hS f g
  obtain ⟨t, ⟨ht⟩, htaff⟩ := exists_isTerminal_of_isAffineRepresentable B S hS (𝒳 := Psq.pt)
    (isAffineRepresentable_twoFibreProductAlgebraicStack B S hS f g h𝒳 h𝒴
      (isAffineRepresentable_schemeStack.{u, w} B S hS _ hy))
  let G := (fppfModulePullback B S hS Psq.fst).obj F
  have hG : sheafFlatBaseChangeModuleRule B S hS E h Psq.pt G :=
    sheafFlatBaseChange_fppfModulePullback B S hS E h Psq.fst F hF
  have hGc : IsCartesianOnFlatAffineArrows.{u, u + 1, u, u} B S hS Psq.pt.val.val.p
      Psq.pt.val.isFiberedInGroupoids (etaleTopology B) (etaleTopology_le_topology B) G.val :=
    fun _ _ φ hφ hx hy' => bijective_restrictionBaseChange_of_flat_freeModuleUniverse.{u, u + 1,
      u, u} B E h S hS Psq.pt.val.val.p Psq.pt.val.isFiberedInGroupoids G.val hG φ hφ hx hy'
  have hcart := isCartesianOnFlatAffineArrows_moduleSheafPushforward_of_comp_eq B S hS
    (CatFiberedInGroupoids.homFunctor Psq.snd.hom)
    (schemeStack.{u, w} B S hS V).val.isFiberedInGroupoids Psq.pt.val.val.p
    Psq.pt.val.isFiberedInGroupoids (CatFiberedInGroupoids.homFunctor_comp_p Psq.snd.hom) ht
    htaff hy G hGc
  let e₀ := (moduleSheafHigherDirectImageZeroIso.{u, u + 1, u, u + 1, u} B S hS Psq.pt.val.val.p
      (schemeStack.{u, w} B S hS V).val.val.p Psq.pt.val.isFiberedInGroupoids
      (schemeStack.{u, w} B S hS V).val.isFiberedInGroupoids
      (CatFiberedInGroupoids.homFunctor Psq.snd.hom)
      (CatFiberedInGroupoids.homFunctor_comp_p Psq.snd.hom) B.topology le_rfl).app G
  have h₀ := fun {a b} (φ : a ⟶ b) hφ ha hb =>
    AlgebraicGeometry.Stack.bijective_restrictionBaseChange_of_iso.{u, u + 1}
      ((SheafOfModules.forget _).mapIso e₀.symm) φ.op (hcart φ hφ ha hb)
  let e₁ := fppfHigherDirectImageBaseChangeIso B S hS f g 0 F
  let X := (fppfModulePullback B S hS g).obj ((fppfHigherDirectImage B S hS f 0).obj F)
  exact isLocallyQuasicoherentWithSheafFlatBaseChangeUnivLE_of_isCartesianOnFlatAffineArrows.{u,
    u + 1, u, u} B E h S hS _ (schemeStack.{u, w} B S hS V).val.isFiberedInGroupoids X.val
    (X.isSheaf.of_le (BigFppfOver.associatedTopology_le_fppf B S hS _ .etale))
    (fun _ _ φ hφ ha hb => AlgebraicGeometry.Stack.bijective_restrictionBaseChange_of_iso.{u, u + 1}
      ((SheafOfModules.forget _).mapIso e₁.symm) φ.op (h₀ φ hφ ha hb))

end AlgebraicGeometry.Stack.AlgebraicStacks
