module

public import StacksFrontier.CategoryTheory.Sites.RingedLocalization.RingedToposHomModules
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.CategoryTheory.Sites.Modules.FlatMorphisms.RingedSites
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedPointPushforward
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ToposInverseImageExact
public import StacksFrontier.CategoryTheory.Sites.UniverseLiftColimits
public import Mathlib.Algebra.Category.Grp.Ulift
public import Mathlib.LinearAlgebra.TensorProduct.Tower
import StacksCore.Tactic.StacksAttribute

/-!
# Exactness of pullback along a flat morphism of ringed topoi

Stacks 04JC. For a morphism of ringed topoi `(f, f♯) : (Sh(C), O_C) ⟶ (Sh(D), O_D)` that is
*flat* — meaning that the inverse-image form `f⁻¹O_D ⟶ O_C` of its structure map is a flat
morphism of sheaves of rings, in the sense of Stacks 04JB — the pullback functor
`f^* : Mod(O_D) ⟶ Mod(O_C)` on sheaves of modules is exact.

## Main results

* `Stacks.Sheaves.RingedToposModules.pullbackModules_exact_of_isFlatMap`: pullback along a flat
  morphism of ringed topoi preserves finite limits and finite colimits.
* `Stacks.Sheaves.RingedToposModules.extendScalars_preservesFiniteLimits`: extension of scalars
  along a flat morphism of sheaves of commutative rings is left exact. This is the
  change-of-rings half of the statement above, and it is what makes the same assertion available
  for the other pullback of sheaves of modules in this development, the abstract left adjoint
  `AlgebraicGeometry.RingedToposSiteHom.pullbackTopos`.

## Implementation notes

Pullback of sheaves of modules is `Stacks.Sheaves.RingedToposModules.pullbackModules`
of Stacks 03D6 part (2), namely the inverse image of Stacks 03D2 followed by extension of
scalars along the structure map. The two halves of exactness are proved separately.

*Finite colimits* are free: `pullbackModules` is a left adjoint, by the Stacks 03D7
adjunction `pullbackAdjPushforwardModules`.

*Finite limits* need the two factors separately. For the inverse image this is left exactness of
`f⁻¹` transported through the identification of the underlying sheaf of sets of an
inverse-image module with the inverse image of the underlying sheaf — the `moduleIso` field of
`Stacks.Sheaves.ToposPullback.pullbackModule`, which is `Iso.refl`. For extension of scalars it
is flatness, and that argument is the substance of the file: extension of scalars is the
sectionwise tensor product followed by sheafification, whereas flatness of a morphism of sheaves
of rings is asserted (necessarily, since sheafification of abelian presheaves is unavailable for
an arbitrary universe of sections) *after lifting the section rings into a universe containing
the site*. Comparing the two therefore needs the lift of a sheaf of modules
(`moduleULift`), the fact that the universe lift of abelian groups preserves sheafification
(`ulift_preservesSheafification`), and an identification of the sectionwise tensor product
before and after the lift (`tensorPresheafIso`, resting on
`TensorProduct.AlgebraTensorModule.uliftEquiv` and the symmetry of the tensor product). With
those, the two composites of functors to abelian sheaves are naturally isomorphic, and left
exactness transfers because the underlying-abelian-sheaf functor reflects finite limits.

The morphism of ringed topoi is the canonical two-field structure of Stacks 01D3 part (2),
`AlgebraicGeometry.RingedToposHom`; `pullbackModules` is built over the richer four-field
`Stacks.Sheaves.RingedToposModules.RingedToposHom`, and
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` passes between them.

The universe levels of `Stacks.Sheaves.RingedToposModules.extendScalars` are written out at
every use site. The argument below introduces auxiliary sheafification instances for
`AddCommGrpCat.{max w u v}` alongside the ones for `AddCommGrpCat.{w}` that the statement
needs, so naming the levels pins the target category of that functor before instance search
begins rather than leaving it to be chosen by whichever instance is solved first.

`AlgebraicGeometry.SheafOfModules.sheafULift`, `.commRingCatULift` and
`CategoryTheory.sheafCompose` are made `implicit_reducible` for this file: the lifted structure
sheaf's sections are `ULift` of the original sections only after those three unfold, so without
this the module structure on the lifted sections is not found.
  `Stacks.PresheafOfModules.ChangeOfRings.changeOfRings`,
`.changeOfRingsObj` and `.cofObj` are in the same list, for the tensor comparison.

## References

* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03ER](https://stacks.math.columbia.edu/tag/03ER)
* [Stacks Project, Tag 04JB](https://stacks.math.columbia.edu/tag/04JB)
* [Stacks Project, Tag 04JC](https://stacks.math.columbia.edu/tag/04JC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open AlgebraicGeometry.SheafOfModules (sheafULift IsFlatMapULift)

universe v u v' u' w z

namespace Stacks.Sheaves.RingedToposModules

attribute [local implicit_reducible]
  AlgebraicGeometry.SheafOfModules.sheafULift
  AlgebraicGeometry.SheafOfModules.commRingCatULift
  CategoryTheory.sheafCompose
  Stacks.PresheafOfModules.ChangeOfRings.changeOfRings
  Stacks.PresheafOfModules.ChangeOfRings.changeOfRingsObj
  Stacks.PresheafOfModules.ChangeOfRings.cofObj


/-- `comp_preservesFiniteLimits` with the two hypotheses as explicit arguments, so that it can
be applied where the composite is spelled through a definition that instance search will not
unfold. -/
public lemma preservesFiniteLimits_comp_of {C D E : Type*}
    [Category* C] [Category* D] [Category* E] (F : C ⥤ D) (G : D ⥤ E)
    (hF : PreservesFiniteLimits F) (hG : PreservesFiniteLimits G) :
    PreservesFiniteLimits (F ⋙ G) :=
  have := hF
  have := hG
  comp_preservesFiniteLimits F G

/-- Composing a sheaf with a left exact functor is left exact in the sheaf, provided the
forgetful functor to presheaves is: it is so on presheaves, where it acts pointwise, and
`sheafToPresheaf` reflects the limits it preserves. -/
private lemma sheafCompose_preservesFiniteLimits
    {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
    {A B : Type*} [Category* A] [Category* B] (F : A ⥤ B)
    [HasFiniteLimits A] [J.HasSheafCompose F] [PreservesFiniteLimits F]
    [PreservesFiniteLimits (sheafToPresheaf J A)] :
    PreservesFiniteLimits (sheafCompose J F) := by
  have : PreservesFiniteLimits ((Functor.whiskeringRight Cᵒᵖ A B).obj F) :=
    ⟨fun _ _ _ => inferInstance⟩
  have : PreservesFiniteLimits (sheafCompose J F ⋙ sheafToPresheaf J B) := by
    show PreservesFiniteLimits (sheafToPresheaf J A ⋙ (Functor.whiskeringRight _ _ _).obj F)
    exact comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_reflects_of_preserves _ (sheafToPresheaf J B)

section ULift

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

/-- Lift a sheaf of `O`-modules to a sheaf of modules over the universe lift of `O`: the
sections are lifted and the ring action is the lifted action. This is the comparison needed
because flatness of a morphism of sheaves of rings is asserted after lifting the section rings
into a universe containing the site. -/
private noncomputable def moduleULift (O : Sheaf J CommRingCat.{w}) :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⥤
      SheafOfModules.{max w u v}
        (Stacks.SheafOfModules.Tensor.ringSheaf ((sheafULift.{w, u, v} J).obj O)) where
  obj M := {
    val := {
      obj U := ModuleCat.of
        (ULift.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U))
        (ULift.{max u v} (M.val.obj U))
      map {U V} f := ModuleCat.ofHom
        (R := ULift.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U))
        (Y := (ModuleCat.restrictScalars
          (ULift.ringEquiv.symm.toRingHom.comp
            (((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.map f).hom.comp
              ULift.ringEquiv.toRingHom))).obj
            (ModuleCat.of
              (ULift.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj V))
              (ULift.{max u v} (M.val.obj V)))) {
          toFun x := ULift.up (M.val.map f x.down)
          map_add' x y := congrArg ULift.up (map_add (M.val.map f).hom x.down y.down)
          map_smul' a x := congrArg ULift.up (M.val.map_smul f a.down x.down) }
      map_id U := by ext x; apply congrArg ULift.up; rw [M.val.map_id]; rfl
      map_comp f g := by ext x; exact congrArg ULift.up (M.val.map_comp_apply f g x.down) }
    isSheaf := Presheaf.isSheaf_comp_of_isSheaf J M.val.presheaf
      AddCommGrpCat.uliftFunctor M.isSheaf }
  map {M N} φ := ⟨{
    app U := ModuleCat.ofHom
      (R := ULift.{max u v} ((Stacks.SheafOfModules.Tensor.ringSheaf O).obj.obj U)) {
      toFun x := ULift.up (φ.val.app U x.down)
      map_add' x y := congrArg ULift.up (map_add (φ.val.app U).hom x.down y.down)
      map_smul' a x := congrArg ULift.up (map_smul (φ.val.app U).hom a.down x.down) }
    naturality {U V} f := ModuleCat.hom_ext <| DFunLike.ext _ _ fun x =>
      congrArg ULift.up (PresheafOfModules.naturality_apply φ.val f x.down) }⟩

/-- Lifting sheaves of modules preserves finite limits: after passing to underlying abelian
sheaves it is composition with the universe lift of abelian groups, and the
underlying-abelian-sheaf functor reflects finite limits. -/
private lemma moduleULift_preservesFiniteLimits (O : Sheaf J CommRingCat.{w}) :
    PreservesFiniteLimits (moduleULift O) := by
  let V := SheafOfModules.toSheaf.{max w u v}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((sheafULift.{w, u, v} J).obj O))
  have : PreservesFiniteLimits (sheafCompose J AddCommGrpCat.uliftFunctor.{max u v, w}) :=
    sheafCompose_preservesFiniteLimits _ _
  have : PreservesFiniteLimits (moduleULift O ⋙ V) := by
    show PreservesFiniteLimits
      (SheafOfModules.toSheaf.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
        sheafCompose J AddCommGrpCat.uliftFunctor.{max u v, w})
    exact comp_preservesFiniteLimits _ _
  have : V.ReflectsIsomorphisms := by dsimp [V]; infer_instance
  have : PreservesFiniteLimits V := by dsimp [V]; infer_instance
  have : ReflectsFiniteLimits V := reflectsFiniteLimits_of_reflectsIsomorphisms V
  exact preservesFiniteLimits_of_reflects_of_preserves _ V

end ULift

section TensorComparison

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  {O₁ O₂ : Sheaf J CommRingCat.{w}} (θ : O₁ ⟶ O₂)

/-- The target structure sheaf of the lift, viewed as a module over the source one by
restriction of scalars. Flatness of the morphism is exactness of tensoring with this. -/
private noncomputable abbrev liftedRingModule :=
  (SheafOfModules.restrictScalars
    ((sheafCompose J (forget₂ CommRingCat.{max w u v} RingCat.{max w u v})).map
      ((sheafULift.{w, u, v} J).map θ))).obj
        (SheafOfModules.unit
          (Stacks.SheafOfModules.Tensor.ringSheaf ((sheafULift.{w, u, v} J).obj O₂)))

/-- Tensor the sections with the target ring and then lift: the sectionwise tensor product of
Stacks 03CU followed by the universe lift of abelian groups. -/
private noncomputable abbrev tensorPresheafLeft :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁) ⥤
      Cᵒᵖ ⥤ AddCommGrpCat.{max w u v} :=
  SheafOfModules.forget _ ⋙ Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ.hom ⋙
    PresheafOfModules.toPresheaf _ ⋙
      (Functor.whiskeringRight _ _ _).obj AddCommGrpCat.uliftFunctor.{max u v, w}

/-- Lift and then tensor the lifted sections with the lifted target ring. -/
private noncomputable abbrev tensorPresheafRight :
    SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁) ⥤
      Cᵒᵖ ⥤ AddCommGrpCat.{max w u v} :=
  moduleULift O₁ ⋙ SheafOfModules.forget _ ⋙
    (PresheafOfModules.tensorBifunctor ((sheafULift.{w, u, v} J).obj O₁).obj).flip.obj
        (liftedRingModule θ).val ⋙
      PresheafOfModules.toPresheaf _

/-- Lifting the sectionwise tensor product and tensoring the lifted sections agree over each
object of the site: both are the tensor product of the lifted modules, up to the symmetry of the
tensor product. -/
private noncomputable def tensorULiftIso
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁)) (U : Cᵒᵖ) :
    ((tensorPresheafLeft θ).obj M).obj U ≅ ((tensorPresheafRight θ).obj M).obj U := by
  letI : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := (θ.hom.app U).hom.toAlgebra
  exact AddEquiv.toAddCommGrpIso
    ((TensorProduct.AlgebraTensorModule.uliftEquiv (O₁.obj.obj U) (O₁.obj.obj U)
      (O₂.obj.obj U) (M.val.obj U)).toAddEquiv.trans
      (TensorProduct.comm (ULift.{max u v} (O₁.obj.obj U))
        (ULift.{max u v} (O₂.obj.obj U)) (ULift.{max u v} (M.val.obj U))).toAddEquiv)

/-- `tensorPresheafLeft` and `tensorPresheafRight` are naturally isomorphic: they agree over
each object by `tensorULiftIso`, and that identification is natural both in the site and in the
sheaf of modules, as both sides act on a pure tensor factorwise. -/
private noncomputable def tensorPresheafIso :
    tensorPresheafLeft θ ≅ tensorPresheafRight θ := by
  refine NatIso.ofComponents (fun M => NatIso.ofComponents (tensorULiftIso θ M) ?_) ?_
  · rename_i M
    intro U V f
    ext x
    obtain ⟨x⟩ := x
    let : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := (θ.hom.app U).hom.toAlgebra
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add x y hx hy =>
      exact ((map_add _ (ULift.up x) (ULift.up y)).trans (congrArg₂ (· + ·) hx hy)).trans
        (map_add _ _ _).symm
    | tmul a m =>
      change (tensorULiftIso θ M V).hom
        (ULift.up ((Stacks.PresheafOfModules.ChangeOfRings.cofMap θ.hom M.val f)
          (a ⊗ₜ[O₁.obj.obj U] m))) = _
      exact congrArg (fun z ↦ (ConcreteCategory.hom (tensorULiftIso θ M V).hom) (ULift.up z))
        (Stacks.PresheafOfModules.ChangeOfRings.cofMap_tmul θ.hom M.val f a m)
  · intro M N φ
    ext U x
    obtain ⟨x⟩ := x
    let : Algebra (O₁.obj.obj U) (O₂.obj.obj U) := (θ.hom.app U).hom.toAlgebra
    induction x using TensorProduct.induction_on with
    | zero => exact (map_zero _).trans (map_zero _).symm
    | add x y hx hy =>
      exact ((map_add _ (ULift.up x) (ULift.up y)).trans (congrArg₂ (· + ·) hx hy)).trans
        (map_add _ _ _).symm
    | tmul a m =>
      change (tensorULiftIso θ N U).hom
        (ULift.up ((Stacks.PresheafOfModules.ChangeOfRings.cofHomApp θ.hom φ.val U)
          (a ⊗ₜ[O₁.obj.obj U] m))) = _
      exact congrArg (fun z ↦ (ConcreteCategory.hom (tensorULiftIso θ N U).hom) (ULift.up z))
        (Stacks.PresheafOfModules.ChangeOfRings.cofHomApp_tmul θ.hom φ.val U a m)

end TensorComparison

section ChangeOfRings

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [HasWeakSheafify J AddCommGrpCat.{w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- Extension of scalars along a *flat* morphism of sheaves of commutative rings is left exact.
This is the substantive half of Stacks 04JC: after passing to underlying abelian sheaves,
extension of scalars becomes the lift of modules followed by tensoring with the lifted target
ring, which is left exact by flatness, and the underlying-abelian-sheaf functor reflects finite
limits. -/
@[sga "4 IV 13.7" "special case", sga "4 V 1.7.2" "(i) ⇒ (ii)"]
lemma extendScalars_preservesFiniteLimits
    {O₁ O₂ : Sheaf J CommRingCat.{w}} (θ : O₁ ⟶ O₂)
    (hθ : IsFlatMapULift.{w, u, v} θ) :
    PreservesFiniteLimits (extendScalars.{w, v, u} J θ.hom
      (Stacks.SheafOfModules.Tensor.ringSheaf O₁).property
      (Stacks.SheafOfModules.Tensor.ringSheaf O₂).property) := by
  let : HasSheafify J AddCommGrpCat.{max w u v} :=
    GrothendieckTopology.hasSheafify_addCommGrpCat.{max w u v, v, u} J
  let : J.WEqualsLocallyBijective AddCommGrpCat.{max w u v} :=
    AlgebraicGeometry.SheafOfModules.wEqualsLocallyBijective_addCommGrpCat.{max w u v, u, v} J
  let : J.PreservesSheafification AddCommGrpCat.uliftFunctor.{max u v, w} :=
    Stacks.Sheaves.UniverseLift.preservesSheafification_uliftFunctor.{u, v, w, max u v}
      (J := J)
  let O₁' := (sheafULift.{w, u, v} J).obj O₁
  let T := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, max w u v, max w u v, max w u v}
    O₁').flip.obj (liftedRingModule θ)
  have : PreservesFiniteLimits T := hθ.1
  let V := SheafOfModules.toSheaf.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₂) ⋙
    sheafCompose J AddCommGrpCat.uliftFunctor.{max u v, w}
  have : PreservesFiniteLimits (sheafCompose J AddCommGrpCat.uliftFunctor.{max u v, w}) :=
    sheafCompose_preservesFiniteLimits _ _
  have : PreservesFiniteLimits V := comp_preservesFiniteLimits _ _
  have : V.ReflectsIsomorphisms := by dsimp [V]; infer_instance
  have hV : ReflectsFiniteLimits V := reflectsFiniteLimits_of_reflectsIsomorphisms V
  have : PreservesFiniteLimits (moduleULift O₁) := moduleULift_preservesFiniteLimits O₁
  let L := SheafOfModules.forget.{w} (Stacks.SheafOfModules.Tensor.ringSheaf O₁) ⋙
    Stacks.PresheafOfModules.ChangeOfRings.changeOfRings θ.hom
  let U₂ := SheafOfModules.toSheaf.{max w u v} (Stacks.SheafOfModules.Tensor.ringSheaf O₁')
  have : PreservesFiniteLimits (T ⋙ U₂) := comp_preservesFiniteLimits _ _
  have hR : PreservesFiniteLimits (moduleULift O₁ ⋙ T ⋙ U₂) := comp_preservesFiniteLimits _ _
  let P₁ := PresheafOfModules.toPresheaf (Stacks.SheafOfModules.Tensor.ringSheaf O₂).obj
  let Ul := sheafCompose J AddCommGrpCat.uliftFunctor.{max u v, w}
  let e : extendScalars.{w, v, u} J θ.hom (Stacks.SheafOfModules.Tensor.ringSheaf O₁).property
        (Stacks.SheafOfModules.Tensor.ringSheaf O₂).property ⋙ V ≅
      moduleULift O₁ ⋙ T ⋙ U₂ := calc
    extendScalars.{w, v, u} J θ.hom (Stacks.SheafOfModules.Tensor.ringSheaf O₁).property
          (Stacks.SheafOfModules.Tensor.ringSheaf O₂).property ⋙ V ≅
        (L ⋙ P₁) ⋙ (presheafToSheaf J AddCommGrpCat.{w} ⋙ Ul) := Iso.refl _
    _ ≅ (L ⋙ P₁) ⋙ ((Functor.whiskeringRight Cᵒᵖ AddCommGrpCat.{w}
            AddCommGrpCat.{max w u v}).obj AddCommGrpCat.uliftFunctor.{max u v, w} ⋙
          presheafToSheaf J AddCommGrpCat.{max w u v}) :=
      Functor.isoWhiskerLeft (L ⋙ P₁)
        (sheafComposeNatIso J AddCommGrpCat.uliftFunctor.{max u v, w}
          (sheafificationAdjunction J AddCommGrpCat.{w})
          (sheafificationAdjunction J AddCommGrpCat.{max w u v})).symm
    _ ≅ tensorPresheafLeft θ ⋙ presheafToSheaf J AddCommGrpCat.{max w u v} := Iso.refl _
    _ ≅ tensorPresheafRight θ ⋙ presheafToSheaf J AddCommGrpCat.{max w u v} :=
      Functor.isoWhiskerRight (tensorPresheafIso θ) _
    _ ≅ moduleULift O₁ ⋙ T ⋙ U₂ := Iso.refl _
  have hE : PreservesFiniteLimits (extendScalars.{w, v, u} J θ.hom
      (Stacks.SheafOfModules.Tensor.ringSheaf O₁).property
      (Stacks.SheafOfModules.Tensor.ringSheaf O₂).property ⋙ V) :=
    @preservesFiniteLimits_of_natIso _ _ _ _ _ _ e.symm hR
  exact @preservesFiniteLimits_of_reflects_of_preserves _ _ _ _ _ _ _ V hE hV

end ChangeOfRings

section FlatPullback

open AlgebraicGeometry

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]

variable [HasWeakSheafify X.J AddCommGrpCat.{w}]
  [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]

/-- **Stacks 04JC**, second assertion. Pullback of sheaves of modules along a *flat* morphism
of ringed topoi is exact: it preserves finite limits and finite colimits. The first assertion,
exactness of the inverse image of abelian sheaves, is
`CategoryTheory.Sites.abelianInverseImage_exact`. -/
@[stacks 04JC "flat_pullback_exact"]
theorem pullbackModules_exact_of_isFlatMap (f : AlgebraicGeometry.RingedToposHom X Y)
    (hf : AlgebraicGeometry.SheafOfModules.IsFlatMapULift.{w, u, v} f.fSharpInverseImage) :
    exactFunctor (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
      (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O))
      (f.toRingedToposModulesHom.pullbackModules) := by
  let := (pullbackAdjPushforwardModules f.toRingedToposModulesHom).isLeftAdjoint
  rw [exactFunctor_iff]
  exact ⟨preservesFiniteLimits_comp_of _ _ (inverseImageModules_preservesFiniteLimits _ _)
    (extendScalars_preservesFiniteLimits X.J f.fSharpInverseImage hf), inferInstance⟩

end FlatPullback

end Stacks.Sheaves.RingedToposModules

end
