module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SheafificationTensor

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.ChangeOfRings
public import Mathlib.CategoryTheory.Sites.Abelian
public import Mathlib.CategoryTheory.Sites.EpiMono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposHom
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.CategoryTheory.Sites.Modules.Flat
public import StacksFrontier.CategoryTheory.Sites.Modules.Tensor

/-!
# Extensions of modules on a first order thickening of ringed topoi

A *first order thickening* of ringed topoi is a morphism `i : (Sh(C), O') → (Sh(D), O)` whose
underlying morphism of topoi is an equivalence and whose structure map `O ⟶ i_*O'` is locally
surjective with square-zero kernel ideal `I`. An *extension* over such a thickening is a short
exact sequence of `O`-modules whose outer terms are restricted from `O'`-modules along the
structure map. Multiplication by a section of `I` carries the middle term into the kernel term
and factors through the quotient term, which gives the canonical map `I ⊗_{O'} F ⟶ K` attached
to an extension of `F` by `K`.

The canonical map is constructed the way the source describes it: a local section of `F` lifts
to the middle term of the extension, multiplying the lift by a section of `I` lands in the
kernel term because the ideal is square zero, and the result does not depend on the lift. That
produces a bilinear pairing on sections, which descends through the sheafification unit of the
tensor product and is characterized by its value on pure tensors.

## Main definitions

* `Deformation.ToposThickening.FirstOrderThickening`: a first order thickening of ringed topoi,
  with its square-zero ideal presented as a module over the quotient structure sheaf.
* `Deformation.ToposThickening.extensionActionMap`: the canonical map `I ⊗_{O'} F ⟶ K` of an
  extension, together with the local-lift formula characterizing it.

## Implementation notes

`CategoryTheory.Abelian.YonedaExtension` in degree zero, with the outer terms restricted from
the quotient structure sheaf, is the sequence in the source's displayed equation; that is why
it carries the tag here as well.

The canonical map is specified by its value on pure tensors after a local lift of the quotient
section. The equality is stated after the injection of the kernel module, so no choice of a
local inverse is involved. The equivalence of the underlying topoi is recorded explicitly;
modules over the source structure sheaf are represented on the target by modules over the
direct image of that sheaf. The ideal is identified by its sectionwise kernel property, and its
square-zero property is sectionwise multiplication in `O`.

## References

* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits MonoidalCategory TensorProduct
open AlgebraicGeometry (RingedTopos RingedToposHom)
open Stacks.Sheaves.ToposPushforward (pushforwardCommRingFunctor)

universe v u w v' u' w'

attribute [local implicit_reducible] SheafOfModules.unit PresheafOfModules.unit
  CategoryTheory.ConcreteCategory.hom

namespace Deformation.ToposThickening

private lemma descentFiber_exists {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} {P Q H : Cᵒᵖ ⥤ Type w'}
    (f : P ⟶ Q) [Presheaf.IsLocallySurjective J f]
    (hH : Presheaf.IsSheaf J H) (b : P ⟶ H)
    (hfiber : ∀ (U : Cᵒᵖ) (x y : P.obj U), f.app U x = f.app U y →
      b.app U x = b.app U y)
    (U : Cᵒᵖ) (y : Q.obj U) :
    ∃ z : H.obj U, ∀ {V : Cᵒᵖ} (g : U ⟶ V) (x : P.obj V),
      f.app V x = Q.map g y → H.map g z = b.app V x := by
  let S := Presheaf.imageSieve f y
  have hS := Presheaf.imageSieve_mem J f y
  let t : Presieve.FamilyOfElements H S.arrows :=
    fun V g hg ↦ b.app _ (Presheaf.localPreimage f y g hg)
  have ht : t.Compatible := by
    intro V₁ V₂ W g₁ g₂ p₁ p₂ hp₁ hp₂ he
    dsimp [t]
    rw [← b.naturality_apply, ← b.naturality_apply]
    apply hfiber
    rw [f.naturality_apply, f.naturality_apply,
      Presheaf.app_localPreimage, Presheaf.app_localPreimage,
      ← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, he]
  let sh := (isSheaf_iff_isSheaf_of_type J H).mp hH S hS
  refine ⟨sh.amalgamate t ht, ?_⟩
  intro V g x hx
  have hg : S g.unop := ⟨x, hx⟩
  exact (sh.valid_glue ht g.unop hg).trans
    (hfiber _ _ _ ((Presheaf.app_localPreimage f y g.unop hg).trans hx.symm))

private noncomputable def descentFiberInvariant {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} {P Q H : Cᵒᵖ ⥤ Type w'}
    (f : P ⟶ Q) [Presheaf.IsLocallySurjective J f]
    (hH : Presheaf.IsSheaf J H) (b : P ⟶ H)
    (hfiber : ∀ (U : Cᵒᵖ) (x y : P.obj U), f.app U x = f.app U y →
      b.app U x = b.app U y) : Q ⟶ H where
  app U := ↾fun y ↦ (descentFiber_exists f hH b hfiber U y).choose
  naturality {U V} g := by
    ext y
    apply hH.isSeparated _ _ (Presheaf.imageSieve_mem J f (Q.map g y))
    intro W p hp
    change H.map p.op ((descentFiber_exists f hH b hfiber V (Q.map g y)).choose) =
      H.map p.op (H.map g ((descentFiber_exists f hH b hfiber U y).choose))
    obtain ⟨x, hx⟩ := hp
    rw [(descentFiber_exists f hH b hfiber V (Q.map g y)).choose_spec p.op x hx]
    rw [← Functor.map_comp_apply]
    exact ((descentFiber_exists f hH b hfiber U y).choose_spec (g ≫ p.op) x
      (by simpa using hx)).symm

private lemma descentFiberInvariant_app {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} {P Q H : Cᵒᵖ ⥤ Type w'}
    (f : P ⟶ Q) [Presheaf.IsLocallySurjective J f]
    (hH : Presheaf.IsSheaf J H) (b : P ⟶ H)
    (hfiber : ∀ (U : Cᵒᵖ) (x y : P.obj U), f.app U x = f.app U y →
      b.app U x = b.app U y)
    (U : Cᵒᵖ) (x : P.obj U) :
    (descentFiberInvariant f hH b hfiber).app U (f.app U x) = b.app U x := by
  have h := (descentFiber_exists f hH b hfiber U (f.app U x)).choose_spec (𝟙 U) x
    (by simp)
  simpa [descentFiberInvariant] using h

private def actionPairPresheaf {C : Type u'} [Category.{v'} C]
    (P Q : Cᵒᵖ ⥤ Type w') : Cᵒᵖ ⥤ Type w' where
  obj U := P.obj U × Q.obj U
  map f := ↾fun x ↦ (P.map f x.1, Q.map f x.2)
  map_id U := by ext x <;> simp
  map_comp f g := by ext x <;> simp

private noncomputable def actionPairMap {C : Type u'} [Category.{v'} C]
    {P P' Q Q' : Cᵒᵖ ⥤ Type w'} (f : P ⟶ Q) (g : P' ⟶ Q') :
    actionPairPresheaf P P' ⟶ actionPairPresheaf Q Q' where
  app U := ↾fun x ↦ (f.app U x.1, g.app U x.2)
  naturality {U V} k := by
    ext x
    change (f.app V (P.map k x.1), g.app V (P'.map k x.2)) =
      (Q.map k (f.app U x.1), Q'.map k (g.app U x.2))
    exact Prod.ext (NatTrans.naturality_apply f k x.1)
      (NatTrans.naturality_apply g k x.2)

private lemma actionPairMap_locallySurjective {C : Type u'} [Category.{v'} C]
    (J : GrothendieckTopology C) {P P' Q Q' : Cᵒᵖ ⥤ Type w'}
    (f : P ⟶ Q) (g : P' ⟶ Q')
    [Presheaf.IsLocallySurjective J f] [Presheaf.IsLocallySurjective J g] :
    Presheaf.IsLocallySurjective J (actionPairMap f g) where
  imageSieve_mem {U} x := by
    apply J.superset_covering
      (S := Presheaf.imageSieve f x.1 ⊓ Presheaf.imageSieve g x.2)
    · rintro V k ⟨⟨x₁, hx₁⟩, ⟨x₂, hx₂⟩⟩
      exact ⟨(x₁, x₂), Prod.ext hx₁ hx₂⟩
    · exact J.intersection_covering
        (Presheaf.imageSieve_mem J f _) (Presheaf.imageSieve_mem J g _)

private noncomputable abbrev actionModuleTypes {C : Type u'} [Category.{v'} C]
    {R : Cᵒᵖ ⥤ RingCat.{w'}} (M : PresheafOfModules.{w'} R) : Cᵒᵖ ⥤ Type w' :=
  M.presheaf ⋙ forget AddCommGrpCat.{w'}

private noncomputable abbrev actionModuleMap {C : Type u'} [Category.{v'} C]
    {R : Cᵒᵖ ⥤ RingCat.{w'}} {M N : PresheafOfModules.{w'} R} (f : M ⟶ N) :
    actionModuleTypes M ⟶ actionModuleTypes N :=
  Functor.whiskerRight ((PresheafOfModules.toPresheaf R).map f) (forget AddCommGrpCat.{w'})

private lemma exact_sections {C : Type u'} [Category.{v'} C]
    {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w'}}
    [J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify J AddCommGrpCat.{w'}]
    {A B D : SheafOfModules.{w'} R} (f : A ⟶ B) (g : B ⟶ D)
    (hfg : f ≫ g = 0) [Mono f]
    (hexact : (ShortComplex.mk f g hfg).Exact)
    (U : Cᵒᵖ) (x : B.val.obj U) (hx : g.val.app U x = 0) :
    ∃ y : A.val.obj U, f.val.app U y = x := by
  let S := ShortComplex.mk f g hfg
  have hfork : IsLimit (KernelFork.ofι f hfg) :=
    (S.exact_and_mono_f_iff_f_is_kernel.mp ⟨hexact, inferInstance⟩).some
  let e := SheafOfModules.evaluation R U
  have hEval := isLimitOfPreserves e hfork
  have hEval' : IsLimit ((KernelFork.ofι f hfg).map e) :=
    KernelFork.isLimitMapConeEquiv (KernelFork.ofι f hfg) e hEval
  let gU := e.map g
  let xmap : ModuleCat.of (R.obj.obj U) (R.obj.obj U) ⟶ e.obj B :=
    ModuleCat.ofHom (LinearMap.smulRight LinearMap.id x)
  have hx1 : xmap 1 = x := by
    change ((LinearMap.id : (R.obj.obj U) →ₗ[R.obj.obj U] (R.obj.obj U)) 1) • x = x
    simp
  have hxmap : xmap ≫ gU = 0 := by
    ext
    rw [ModuleCat.comp_apply, hx1]
    change g.val.app U x = 0
    exact hx
  obtain ⟨l, hl⟩ := KernelFork.IsLimit.lift' hEval' xmap hxmap
  refine ⟨l 1, ?_⟩
  have hl' := hl
  simp only [KernelFork.map_ι, KernelFork.ι_ofι] at hl'
  have h := congrArg (fun q => q 1) hl'
  rw [ModuleCat.comp_apply, hx1] at h
  change f.val.app U (l 1) = x at h
  exact h

/-- The two maps of a degree-zero Yoneda extension compose to zero. -/
public lemma yonedaExtension_comp_zero
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {B A : 𝒜}
    (E : Abelian.YonedaExtension B A 0) : E.f ≫ E.g = 0 := by
  have hz := E.exact_g.toIsComplex.zero 0
  simpa [ComposableArrows.Precomp.map, ComposableArrows.Mk₁.map] using hz

private lemma yonedaExtension_exactShortComplex
    {𝒜 : Type*} [Category 𝒜] [Abelian 𝒜] {B A : 𝒜}
    (E : Abelian.YonedaExtension B A 0) :
    (ShortComplex.mk E.f E.g (yonedaExtension_comp_zero E)).Exact := by
  apply (ShortComplex.exact_iff_exact_toComposableArrows _).2
  change (ComposableArrows.mk₂ E.f E.g).Exact
  exact E.exact_g


variable {X : RingedTopos.{v, u, w}}
  {Y : RingedTopos.{v', u', w'}}

/-- The forgetful functor from sheaves of modules over the structure sheaf of `Y` to
presheaves of modules preserves finite limits. -/
local instance :
    PreservesFiniteLimits
      (SheafOfModules.forget.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)) :=
  SheafOfModules.Finite.forgetPreservesFiniteLimits _

/-- A first-order thickening, with the kernel represented as a module over
the quotient structure sheaf on the target topos. -/
public structure FirstOrderThickening
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    (i : RingedToposHom X Y) where
  /-- The underlying geometric morphism identifies the topoi. -/
  equiv : i.toToposHom.pushforward.IsEquivalence
  /-- The structure map is locally surjective. -/
  surjective : Presheaf.IsLocallySurjective Y.J i.fSharp.hom
  /-- The square-zero ideal, viewed as a module over the quotient. -/
  I : SheafOfModules.{w'}
    (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))
  /-- Inclusion of the ideal in the structure sheaf. -/
  incl : (SheafOfModules.restrictScalars
      (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
          Stacks.SheafOfModules.Tensor.ringSheaf
            ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
        (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj I ⟶
    SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
  /-- The ideal is exactly the kernel of the structure map. -/
  kernel : ∀ (U : Y.Cᵒᵖ) (a : Y.O.obj.obj U),
    i.fSharp.hom.app U a = 0 ↔
      ∃ b : I.val.obj U, (show Y.O.obj.obj U from incl.val.app U b) = a
  /-- The ideal is a submodule, not merely a cover of the kernel. -/
  injective : ∀ U : Y.Cᵒᵖ, Function.Injective (incl.val.app U)
  /-- Every product of two ideal sections vanishes. -/
  square_zero : ∀ (U : Y.Cᵒᵖ) (a b : I.val.obj U),
      (show Y.O.obj.obj U from incl.val.app U a) *
        (show Y.O.obj.obj U from incl.val.app U b) = 0

/-- A local section of the structure sheaf killed by the structure map of a first order
thickening is the image of a section of the square-zero ideal. -/
public lemma FirstOrderThickening.exists_ideal_section
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y} (hi : FirstOrderThickening i) (U : Y.Cᵒᵖ)
    (a : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U)
    (ha : i.fSharp.hom.app U a = 0) :
    ∃ b : hi.I.val.obj U,
      (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from hi.incl.val.app U b) = a :=
  (hi.kernel U a).1 ha

/-- The structure map of a first order thickening kills the image of an ideal section. -/
private lemma incl_map_eq_zero
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y} (hi : FirstOrderThickening i) (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) :
    (((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp).hom.app U).hom
      (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from
        hi.incl.val.app U a) = 0 :=
  (hi.kernel U (hi.incl.val.app U a)).2 ⟨a, rfl⟩

/-- The forgetful functor to presheaves of modules preserves monomorphisms. -/
private lemma sheafModule_mono_val
    {A B : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)} (f : A ⟶ B)
    [Mono f] : Mono f.val :=
  (SheafOfModules.forget.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).map_mono f

private lemma extension_action_maps_to_zero
    {X : RingedTopos.{v, u, w}}
    {Y : RingedTopos.{v', u', w'}}
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : E.Z.left.val.obj U) :
    E.g.val.app U
        ((show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from
          hi.incl.val.app U a) • x) = 0 := by
  let α : Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) :=
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp
  let r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U :=
    show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from hi.incl.val.app U a
  have ha : (α.hom.app U).hom r = 0 := incl_map_eq_zero hi U a
  change E.g.val.app U (r • x) = 0
  rw [map_smul]
  change (α.hom.app U).hom r •
    (show F.val.obj U from E.g.val.app U x) = 0
  rw [ha]
  exact zero_smul _ _

private lemma extension_kernel_action_zero
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (k : K.val.obj U) :
    E.f.val.app U
      ((show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from hi.incl.val.app U a) •
        (show ((SheafOfModules.restrictScalars
          (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
              Stacks.SheafOfModules.Tensor.ringSheaf
                ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
            (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K).val.obj U
          from k)) = 0 := by
  let α : Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) :=
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp
  let r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U :=
    show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from hi.incl.val.app U a
  have ha : (α.hom.app U).hom r = 0 := incl_map_eq_zero hi U a
  change E.f.val.app U (r • (show ((SheafOfModules.restrictScalars α).obj K).val.obj U
    from k)) = 0
  change E.f.val.app U ((α.hom.app U).hom r •
    (show K.val.obj U from k)) = 0
  rw [ha, zero_smul]
  exact map_zero _

private noncomputable def extensionActionLift
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : E.Z.left.val.obj U) : K.val.obj U :=
  (exact_sections E.f E.g (yonedaExtension_comp_zero E)
    (yonedaExtension_exactShortComplex E) U
    ((show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from hi.incl.val.app U a) • x)
    (extension_action_maps_to_zero hi E U a x)).choose

private lemma extensionActionLift_spec
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : E.Z.left.val.obj U) :
    E.f.val.app U (extensionActionLift hi E U a x) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from
        hi.incl.val.app U a) • x :=
  (exact_sections E.f E.g (yonedaExtension_comp_zero E)
    (yonedaExtension_exactShortComplex E) U
    ((show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from hi.incl.val.app U a) • x)
    (extension_action_maps_to_zero hi E U a x)).choose_spec

private lemma extensionActionLift_eq_of_quotient_eq
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x y : E.Z.right.val.obj U)
    (hxy : E.g.val.app U x = E.g.val.app U y) :
    extensionActionLift hi E U a (show E.Z.left.val.obj U from x) =
      extensionActionLift hi E U a (show E.Z.left.val.obj U from y) := by
  have := sheafModule_mono_val E.f
  apply PresheafOfModules.injective_of_mono E.f.val U
  have hzero : E.g.val.app U (x - y) = 0 := by
    rw [map_sub, hxy, sub_self]
  obtain ⟨k, hk⟩ := exact_sections E.f E.g (yonedaExtension_comp_zero E)
    (yonedaExtension_exactShortComplex E) U
    (show E.Z.left.val.obj U from x - y) (by simpa using hzero)
  let r : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U :=
    show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from hi.incl.val.app U a
  have hkill : r • (show E.Z.left.val.obj U from x - y) = 0 := by
    calc
      r • (show E.Z.left.val.obj U from x - y) = r • E.f.val.app U k := by rw [hk]
      _ = E.f.val.app U
          (r • (show ((SheafOfModules.restrictScalars
            (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
                Stacks.SheafOfModules.Tensor.ringSheaf
                  ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
              (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K).val.obj U
            from k)) := (map_smul (E.f.val.app U).hom r
              (show ((SheafOfModules.restrictScalars
                (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
                    Stacks.SheafOfModules.Tensor.ringSheaf
                      ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
                  (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K).val.obj U
                from k)).symm
      _ = 0 := extension_kernel_action_zero hi E U a k
  have hact :
      r • x = r • y := by
    apply sub_eq_zero.mp
    simpa [smul_sub] using hkill
  rw [extensionActionLift_spec, extensionActionLift_spec]
  exact hact

private noncomputable def extensionActionOnMiddle
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0) :
    actionPairPresheaf (actionModuleTypes hi.I.val)
      (actionModuleTypes E.Z.right.val) ⟶ actionModuleTypes K.val where
  app U := ↾fun p => extensionActionLift hi E U p.1
    (show E.Z.left.val.obj U from p.2)
  naturality {U V} g := by
    ext p
    have := sheafModule_mono_val E.f
    let α : Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
        Stacks.SheafOfModules.Tensor.ringSheaf
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O) :=
      (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp
    change extensionActionLift hi E V (hi.I.val.map g p.1)
        (show E.Z.left.val.obj V from E.Z.right.val.map g p.2) =
      (((SheafOfModules.restrictScalars α).obj K).val.map g)
        (extensionActionLift hi E U p.1
        (show E.Z.left.val.obj U from p.2))
    apply PresheafOfModules.injective_of_mono E.f.val V
    rw [extensionActionLift_spec hi E V (hi.I.val.map g p.1)
      (show E.Z.left.val.obj V from E.Z.right.val.map g p.2)]
    rw [PresheafOfModules.naturality_apply E.f.val g
      (extensionActionLift hi E U p.1 (show E.Z.left.val.obj U from p.2))]
    rw [extensionActionLift_spec hi E U p.1 (show E.Z.left.val.obj U from p.2)]
    rw [map_smul]
    have hinc :
        (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map g (hi.incl.val.app U p.1) =
          hi.incl.val.app V (hi.I.val.map g p.1) := by
      have hinc' := (PresheafOfModules.naturality_apply hi.incl.val g p.1).symm
      change (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.map g (hi.incl.val.app U p.1) =
        hi.incl.val.app V
          ((((SheafOfModules.restrictScalars α).obj hi.I).val.map g) p.1) at hinc'
      have hmap : (((SheafOfModules.restrictScalars α).obj hi.I).val.map g) p.1 =
          hi.I.val.map g p.1 := rfl
      rw [hmap] at hinc'
      exact hinc'
    rw [← hinc]
    rfl

private lemma extensionActionOnMiddle_add_left
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (U : Y.Cᵒᵖ) (a a' : hi.I.val.obj U) (x : E.Z.left.val.obj U) :
    (extensionActionOnMiddle hi E).app U (a + a', x) =
      (extensionActionOnMiddle hi E).app U (a, x) +
        (extensionActionOnMiddle hi E).app U (a', x) := by
  have := sheafModule_mono_val E.f
  change extensionActionLift hi E U (a + a') x =
    extensionActionLift hi E U a x + extensionActionLift hi E U a' x
  apply PresheafOfModules.injective_of_mono E.f.val U
  have hincl :
      (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from
        hi.incl.val.app U (a + a')) =
      (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from hi.incl.val.app U a) +
        (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from
          hi.incl.val.app U a') :=
    (hi.incl.val.app U).hom.map_add a a'
  have hf : E.f.val.app U (extensionActionLift hi E U a x + extensionActionLift hi E U a' x) =
      E.f.val.app U (extensionActionLift hi E U a x) +
        E.f.val.app U (extensionActionLift hi E U a' x) :=
    (E.f.val.app U).hom.map_add _ _
  rw [hf, extensionActionLift_spec, extensionActionLift_spec, extensionActionLift_spec,
    hincl]
  exact add_smul _ _ _

private lemma extensionActionOnMiddle_add_right
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x x' : E.Z.left.val.obj U) :
    (extensionActionOnMiddle hi E).app U (a, x + x') =
      (extensionActionOnMiddle hi E).app U (a, x) +
        (extensionActionOnMiddle hi E).app U (a, x') := by
  have := sheafModule_mono_val E.f
  change extensionActionLift hi E U a (x + x') =
    extensionActionLift hi E U a x + extensionActionLift hi E U a x'
  apply PresheafOfModules.injective_of_mono E.f.val U
  have hf : E.f.val.app U (extensionActionLift hi E U a x + extensionActionLift hi E U a x') =
      E.f.val.app U (extensionActionLift hi E U a x) +
        E.f.val.app U (extensionActionLift hi E U a x') :=
    (E.f.val.app U).hom.map_add _ _
  rw [hf, extensionActionLift_spec, extensionActionLift_spec, extensionActionLift_spec]
  exact smul_add _ _ _

/-- An epimorphism of sheaves of modules is locally surjective on sections. -/
public lemma sheafModule_epi_locallySurjective
    {C : Type u'} [Category.{v'} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{w'}}
    [HasSheafify J AddCommGrpCat.{w'}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    {M N : SheafOfModules.{w'} R} (f : M ⟶ N) [Epi f] :
    Presheaf.IsLocallySurjective J
      ((PresheafOfModules.toPresheaf R.obj).map f.val) := by
  have hPres : PreservesColimit (span f f) (SheafOfModules.toSheaf R) := by
    let L := PresheafOfModules.sheafification (R := R) (𝟙 R.obj)
    let adj := PresheafOfModules.sheafificationAdjunction (R := R) (𝟙 R.obj)
    let Rt := SheafOfModules.forget.{w'} R ⋙ PresheafOfModules.restrictScalars (𝟙 R.obj)
    let K : WalkingSpan ⥤ PresheafOfModules R.obj := span f f ⋙ Rt
    have h₁ : PreservesColimit K (L ⋙ SheafOfModules.toSheaf R) :=
      preservesColimit_of_natIso K
        (PresheafOfModules.sheafificationCompToSheaf (R := R) (𝟙 R.obj)).symm
    let e : span f f ≅ K ⋙ L :=
      (Functor.rightUnitor (span f f)).symm ≪≫
        Functor.isoWhiskerLeft (span f f) (asIso adj.counit).symm ≪≫
        (Functor.associator (span f f) Rt L).symm
    have h₂ : PreservesColimit (K ⋙ L) (SheafOfModules.toSheaf R) :=
      preservesColimit_of_preserves_colimit_cocone
        (isColimitOfPreserves L (colimit.isColimit K))
        (isColimitOfPreserves (L ⋙ SheafOfModules.toSheaf R) (colimit.isColimit K))
    exact preservesColimit_of_iso_diagram (SheafOfModules.toSheaf R) e.symm
  have : Epi ((SheafOfModules.toSheaf R).map f) :=
    preserves_epi_of_preservesColimit (SheafOfModules.toSheaf R) f
  have hloc : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map f) :=
    (Sheaf.isLocallySurjective_iff_epi' AddCommGrpCat
      ((SheafOfModules.toSheaf R).map f)).mpr inferInstance
  change Presheaf.IsLocallySurjective J
    ((PresheafOfModules.toPresheaf R.obj).map f.val)
  exact hloc

private lemma actionModuleTypes_isSheaf
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))) :
    Presheaf.IsSheaf Y.J (actionModuleTypes K.val) := by
  change Presheaf.IsSheaf Y.J
    (((sheafCompose Y.J (forget AddCommGrpCat.{w'})).obj
      ((SheafOfModules.toSheaf
        (Stacks.SheafOfModules.Tensor.ringSheaf
          ((pushforwardCommRingFunctor i.toToposHom).obj X.O))).obj K)).obj)
  exact ((sheafCompose Y.J (forget AddCommGrpCat.{w'})).obj
    ((SheafOfModules.toSheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O))).obj K)).property

private lemma actionModuleMap_locallySurjective
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0) :
    Presheaf.IsLocallySurjective Y.J (actionModuleMap E.g.val) := by
  have hG0 := sheafModule_epi_locallySurjective E.g
  change Presheaf.IsLocallySurjective Y.J
    (Functor.whiskerRight ((PresheafOfModules.toPresheaf
      ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj)).map E.g.val)
      (forget AddCommGrpCat.{w'}))
  exact (Presheaf.isLocallySurjective_iff_whisker_forget
    (J := Y.J) ((PresheafOfModules.toPresheaf
      (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj).map E.g.val)).mp hG0

private lemma actionPairMap_quotient_locallySurjective
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0) :
    Presheaf.IsLocallySurjective Y.J
      (actionPairMap (𝟙 (actionModuleTypes hi.I.val)) (actionModuleMap E.g.val)) := by
  have hId : Presheaf.IsLocallySurjective Y.J (𝟙 (actionModuleTypes hi.I.val)) := by
    constructor
    intro U x
    apply Y.J.superset_covering (S := ⊤)
    · intro V g _
      exact ⟨(actionModuleTypes hi.I.val).map g.op x, rfl⟩
    · exact Y.J.top_mem U
  have hG : Presheaf.IsLocallySurjective Y.J (actionModuleMap E.g.val) :=
    actionModuleMap_locallySurjective E
  exact actionPairMap_locallySurjective Y.J (𝟙 (actionModuleTypes hi.I.val))
    (actionModuleMap E.g.val)

private lemma extensionActionOnMiddle_fiber
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0) :
    ∀ (U : Y.Cᵒᵖ) (x y : (actionPairPresheaf (actionModuleTypes hi.I.val)
      (actionModuleTypes E.Z.right.val)).obj U),
      (actionPairMap (𝟙 (actionModuleTypes hi.I.val))
          (actionModuleMap E.g.val)).app U x =
        (actionPairMap (𝟙 (actionModuleTypes hi.I.val))
          (actionModuleMap E.g.val)).app U y →
      (extensionActionOnMiddle hi E).app U x =
        (extensionActionOnMiddle hi E).app U y := by
  intro U x y hxy
  have ha := congrArg (fun z => z.1) hxy
  have hg := congrArg (fun z => z.2) hxy
  change x.1 = y.1 at ha
  change E.g.val.app U x.2 = E.g.val.app U y.2 at hg
  change extensionActionLift hi E U x.1 x.2 =
    extensionActionLift hi E U y.1 y.2
  rw [ha]
  exact extensionActionLift_eq_of_quotient_eq hi E U y.1 x.2 y.2 hg

private noncomputable def extensionActionPairing
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0) :
    actionPairPresheaf (actionModuleTypes hi.I.val) (actionModuleTypes F.val) ⟶
      actionModuleTypes K.val :=
  @descentFiberInvariant _ _ Y.J
    (actionPairPresheaf (actionModuleTypes hi.I.val) (actionModuleTypes E.Z.right.val))
    (actionPairPresheaf (actionModuleTypes hi.I.val) (actionModuleTypes F.val))
    (actionModuleTypes K.val)
    (actionPairMap (𝟙 (actionModuleTypes hi.I.val)) (actionModuleMap E.g.val))
    (actionPairMap_quotient_locallySurjective hi E)
    (actionModuleTypes_isSheaf K) (extensionActionOnMiddle hi E)
    (extensionActionOnMiddle_fiber hi E)

private lemma extensionActionPairing_lift
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (y : E.Z.left.val.obj U) :
    (extensionActionPairing hi E).app U (a, E.g.val.app U y) =
      extensionActionLift hi E U a y :=
  @descentFiberInvariant_app _ _ Y.J
    (actionPairPresheaf (actionModuleTypes hi.I.val) (actionModuleTypes E.Z.right.val))
    (actionPairPresheaf (actionModuleTypes hi.I.val) (actionModuleTypes F.val))
    (actionModuleTypes K.val)
    (actionPairMap (𝟙 (actionModuleTypes hi.I.val)) (actionModuleMap E.g.val))
    (actionPairMap_quotient_locallySurjective hi E)
    (actionModuleTypes_isSheaf K) (extensionActionOnMiddle hi E)
    (extensionActionOnMiddle_fiber hi E) U (a, y)


private lemma extensionActionPairing_naturality
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    {U V : Y.Cᵒᵖ} (g : U ⟶ V) (a : hi.I.val.obj U) (x : F.val.obj U) :
    (extensionActionPairing hi E).app V
        (hi.I.val.map g a, F.val.map g x) =
      K.val.map g ((extensionActionPairing hi E).app U (a, x)) :=
  congrArg (fun k ↦ k (a, x)) ((extensionActionPairing hi E).naturality g)

private lemma extensionActionPairing_add_left
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (U : Y.Cᵒᵖ) (a a' : hi.I.val.obj U) (x : F.val.obj U) :
    (extensionActionPairing hi E).app U (a + a', x) =
      (extensionActionPairing hi E).app U (a, x) +
        (extensionActionPairing hi E).app U (a', x) := by
  have hK : Presheaf.IsSheaf Y.J (actionModuleTypes K.val) := actionModuleTypes_isSheaf K
  have hG : Presheaf.IsLocallySurjective Y.J (actionModuleMap E.g.val) :=
    actionModuleMap_locallySurjective E
  have := hG
  apply hK.isSeparated _ _
    (Presheaf.imageSieve_mem (A := Type w') (U := U) (FA := TypeCat.Fun)
      (CA := fun T ↦ T) Y.J (actionModuleMap E.g.val) x)
  rintro V g ⟨y, hy⟩
  change E.Z.left.val.obj (Opposite.op V) at y
  change E.g.val.app (Opposite.op V) y = F.val.map g.op x at hy
  change K.val.map g.op _ = K.val.map g.op _
  have e1 : K.val.map g.op ((extensionActionPairing hi E).app U (a + a', x)) =
      (extensionActionPairing hi E).app (Opposite.op V)
        (hi.I.val.map g.op (a + a'), F.val.map g.op x) :=
    (extensionActionPairing_naturality hi E g.op (a + a') x).symm
  have e2 : K.val.map g.op ((extensionActionPairing hi E).app U (a, x) +
        (extensionActionPairing hi E).app U (a', x)) =
      (extensionActionPairing hi E).app (Opposite.op V)
          (hi.I.val.map g.op a, F.val.map g.op x) +
        (extensionActionPairing hi E).app (Opposite.op V)
          (hi.I.val.map g.op a', F.val.map g.op x) := by
    rw [extensionActionPairing_naturality hi E g.op a x,
      extensionActionPairing_naturality hi E g.op a' x]
    exact (K.val.map g.op).hom.map_add _ _
  have key : ∀ A A' : hi.I.val.obj (Opposite.op V),
      (extensionActionPairing hi E).app (Opposite.op V)
          (A + A', E.g.val.app (Opposite.op V) y) =
        (extensionActionPairing hi E).app (Opposite.op V)
            (A, E.g.val.app (Opposite.op V) y) +
          (extensionActionPairing hi E).app (Opposite.op V)
            (A', E.g.val.app (Opposite.op V) y) := by
    intro A A'
    rw [extensionActionPairing_lift, extensionActionPairing_lift,
      extensionActionPairing_lift]
    exact extensionActionOnMiddle_add_left hi E (Opposite.op V) A A' y
  have hIa : hi.I.val.map g.op (a + a') =
      hi.I.val.map g.op a + hi.I.val.map g.op a' :=
    (hi.I.val.map g.op).hom.map_add a a'
  rw [e1, e2, ← hy]
  exact (congrArg (fun z => (extensionActionPairing hi E).app (Opposite.op V)
    (z, E.g.val.app (Opposite.op V) y)) hIa).trans (key _ _)

private lemma extensionActionPairing_add_right
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x x' : F.val.obj U) :
    (extensionActionPairing hi E).app U (a, x + x') =
      (extensionActionPairing hi E).app U (a, x) +
        (extensionActionPairing hi E).app U (a, x') := by
  have hK : Presheaf.IsSheaf Y.J (actionModuleTypes K.val) := actionModuleTypes_isSheaf K
  have hG : Presheaf.IsLocallySurjective Y.J (actionModuleMap E.g.val) :=
    actionModuleMap_locallySurjective E
  let : Presheaf.IsLocallySurjective Y.J (actionModuleMap E.g.val) := hG
  let : Presheaf.IsLocallySurjective Y.J
      (actionPairMap (actionModuleMap E.g.val) (actionModuleMap E.g.val)) :=
    actionPairMap_locallySurjective Y.J (actionModuleMap E.g.val) (actionModuleMap E.g.val)
  apply hK.isSeparated _ _
    (Presheaf.imageSieve_mem (A := Type w') (U := U) (FA := TypeCat.Fun)
      (CA := fun T ↦ T) Y.J
      (actionPairMap (actionModuleMap E.g.val) (actionModuleMap E.g.val)) (x, x'))
  rintro V g ⟨⟨y, y'⟩, h⟩
  change E.Z.left.val.obj (Opposite.op V) at y y'
  have hx := congrArg Prod.fst h
  have hx' := congrArg Prod.snd h
  change E.g.val.app (Opposite.op V) y = F.val.map g.op x at hx
  change E.g.val.app (Opposite.op V) y' = F.val.map g.op x' at hx'
  change K.val.map g.op _ = K.val.map g.op _
  have hgadd : E.g.val.app (Opposite.op V) (y + y') =
      E.g.val.app (Opposite.op V) y + E.g.val.app (Opposite.op V) y' :=
    (E.g.val.app (Opposite.op V)).hom.map_add y y'
  have hFadd : F.val.map g.op (x + x') =
      F.val.map g.op x + F.val.map g.op x' :=
    (F.val.map g.op).hom.map_add x x'
  have hxx : F.val.map g.op (x + x') = E.g.val.app (Opposite.op V) (y + y') := by
    rw [hgadd, hx, hx']
    exact hFadd
  have e1 : K.val.map g.op ((extensionActionPairing hi E).app U (a, x + x')) =
      (extensionActionPairing hi E).app (Opposite.op V)
        (hi.I.val.map g.op a, F.val.map g.op (x + x')) :=
    (extensionActionPairing_naturality hi E g.op a (x + x')).symm
  have e2 : K.val.map g.op ((extensionActionPairing hi E).app U (a, x) +
        (extensionActionPairing hi E).app U (a, x')) =
      (extensionActionPairing hi E).app (Opposite.op V)
          (hi.I.val.map g.op a, F.val.map g.op x) +
        (extensionActionPairing hi E).app (Opposite.op V)
          (hi.I.val.map g.op a, F.val.map g.op x') := by
    rw [extensionActionPairing_naturality hi E g.op a x,
      extensionActionPairing_naturality hi E g.op a x']
    exact (K.val.map g.op).hom.map_add _ _
  have key : ∀ (A : hi.I.val.obj (Opposite.op V))
      (z z' : E.Z.left.val.obj (Opposite.op V)),
      (extensionActionPairing hi E).app (Opposite.op V)
          (A, E.g.val.app (Opposite.op V) (z + z')) =
        (extensionActionPairing hi E).app (Opposite.op V)
            (A, E.g.val.app (Opposite.op V) z) +
          (extensionActionPairing hi E).app (Opposite.op V)
            (A, E.g.val.app (Opposite.op V) z') := by
    intro A z z'
    rw [extensionActionPairing_lift, extensionActionPairing_lift,
      extensionActionPairing_lift]
    exact extensionActionOnMiddle_add_right hi E (Opposite.op V) A z z'
  rw [e1, e2, hxx, ← hx, ← hx']
  exact key _ y y'

private lemma extensionActionPairing_smul_left
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (U : Y.Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U)
    (a : hi.I.val.obj U) (x : F.val.obj U) :
    (extensionActionPairing hi E).app U (r • a, x) =
      r • (show K.val.obj U from (extensionActionPairing hi E).app U (a, x)) := by
  let α : Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) :=
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp
  let αT := Functor.whiskerRight α.hom (forget RingCat.{w'})
  let g := actionModuleMap E.g.val
  have hα : Presheaf.IsLocallySurjective Y.J αT :=
    (Presheaf.isLocallySurjective_iff_whisker_forget
      (J := Y.J) i.fSharp.hom).mp hi.surjective
  have hG : Presheaf.IsLocallySurjective Y.J g := actionModuleMap_locallySurjective E
  let f := actionPairMap αT g
  let : Presheaf.IsLocallySurjective Y.J f :=
    actionPairMap_locallySurjective Y.J αT g
  have hK : Presheaf.IsSheaf Y.J (actionModuleTypes K.val) := actionModuleTypes_isSheaf K
  apply hK.isSeparated _ _
    (Presheaf.imageSieve_mem (A := Type w') (U := U) (FA := TypeCat.Fun)
      (CA := fun T ↦ T) Y.J f (r, x))
  rintro V g' ⟨⟨r₀, y⟩, h⟩
  have hr := congrArg Prod.fst h
  have hx := congrArg Prod.snd h
  change (α.hom.app (Opposite.op V)).hom r₀ =
    (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.map g'.op r at hr
  change E.g.val.app (Opposite.op V) y = F.val.map g'.op x at hx
  change K.val.map g'.op _ = K.val.map g'.op _
  rw [K.val.map_smul, ← extensionActionPairing_naturality hi E g'.op,
    ← extensionActionPairing_naturality hi E g'.op,
    hi.I.val.map_smul, ← hr, ← hx]
  have := sheafModule_mono_val E.f
  let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (hi.I.val.obj (Opposite.op V)) :=
    (((SheafOfModules.restrictScalars α).obj hi.I).val.obj (Opposite.op V)).isModule
  let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (F.val.obj (Opposite.op V)) :=
    (((SheafOfModules.restrictScalars α).obj F).val.obj (Opposite.op V)).isModule
  let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (K.val.obj (Opposite.op V)) :=
    (((SheafOfModules.restrictScalars α).obj K).val.obj (Opposite.op V)).isModule
  let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj (Opposite.op V))
      (K.val.obj (Opposite.op V)) := (K.val.obj (Opposite.op V)).isModule
  let : SMul ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (hi.I.val.obj (Opposite.op V)) :=
    (inferInstance : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (hi.I.val.obj (Opposite.op V))).toDistribMulAction.toMulAction.toSMul
  let : SMul ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (F.val.obj (Opposite.op V)) :=
    (inferInstance : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (F.val.obj (Opposite.op V))).toDistribMulAction.toMulAction.toSMul
  let : SMul ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (K.val.obj (Opposite.op V)) :=
    (inferInstance : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (K.val.obj (Opposite.op V))).toDistribMulAction.toMulAction.toSMul
  let r₀R : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V) := r₀
  let q : (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj (Opposite.op V) :=
    (α.hom.app (Opposite.op V)).hom r₀
  let yV : E.Z.left.val.obj (Opposite.op V) := y
  let aV : hi.I.val.obj (Opposite.op V) := hi.I.val.map g'.op a
  let xV : F.val.obj (Opposite.op V) := F.val.map g'.op x
  have hqI : q • aV =
      (r₀R • aV :
        ((SheafOfModules.restrictScalars α).obj hi.I).val.obj (Opposite.op V)) := rfl
  have hqK (z : K.val.obj (Opposite.op V)) : q • z =
      (r₀R • z : ((SheafOfModules.restrictScalars α).obj K).val.obj
        (Opposite.op V)) := rfl
  change (extensionActionPairing hi E).app (Opposite.op V)
      (q • aV, E.g.val.app (Opposite.op V) yV) =
    q • (show K.val.obj (Opposite.op V) from
        (extensionActionPairing hi E).app (Opposite.op V)
          (aV, E.g.val.app (Opposite.op V) yV))
  let pV : K.val.obj (Opposite.op V) :=
    (extensionActionPairing hi E).app (Opposite.op V)
      (aV, E.g.val.app (Opposite.op V) yV)
  apply PresheafOfModules.injective_of_mono E.f.val (Opposite.op V)
  rw [hqK pV]
  calc
    E.f.val.app (Opposite.op V)
        ((extensionActionPairing hi E).app (Opposite.op V)
          (q • aV, E.g.val.app (Opposite.op V) yV)) =
        r₀R • ((show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V) from
          hi.incl.val.app (Opposite.op V) aV) • yV) := by
      rw [extensionActionPairing_lift, extensionActionLift_spec]
      rw [hqI]
      have hinc : (hi.incl.val.app (Opposite.op V)).hom (r₀R • aV) =
          r₀R • (hi.incl.val.app (Opposite.op V)).hom aV :=
        map_smul (hi.incl.val.app (Opposite.op V)).hom r₀R aV
      rw [hinc]
      simp [smul_smul]
      rfl
    _ = E.f.val.app (Opposite.op V) (r₀R • pV) := by
      have hsm : E.f.val.app (Opposite.op V) (r₀R • pV) =
          r₀R • E.f.val.app (Opposite.op V) pV :=
        map_smul (E.f.val.app (Opposite.op V)).hom r₀R pV
      rw [hsm]
      simp only [pV]
      rw [extensionActionPairing_lift, extensionActionLift_spec]

private lemma extensionActionPairing_smul_right
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (U : Y.Cᵒᵖ) (r : (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj U)
    (a : hi.I.val.obj U) (x : F.val.obj U) :
    (extensionActionPairing hi E).app U (a, r • x) =
      r • (show K.val.obj U from (extensionActionPairing hi E).app U (a, x)) := by
  let α : Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
      Stacks.SheafOfModules.Tensor.ringSheaf
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O) :=
    (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp
  let αT := Functor.whiskerRight α.hom (forget RingCat.{w'})
  let g := actionModuleMap E.g.val
  have hα : Presheaf.IsLocallySurjective Y.J αT :=
    (Presheaf.isLocallySurjective_iff_whisker_forget
      (J := Y.J) i.fSharp.hom).mp hi.surjective
  have hG : Presheaf.IsLocallySurjective Y.J g := actionModuleMap_locallySurjective E
  let f := actionPairMap αT g
  let : Presheaf.IsLocallySurjective Y.J f :=
    actionPairMap_locallySurjective Y.J αT g
  have hK : Presheaf.IsSheaf Y.J (actionModuleTypes K.val) := actionModuleTypes_isSheaf K
  apply hK.isSeparated _ _
    (Presheaf.imageSieve_mem (A := Type w') (U := U) (FA := TypeCat.Fun)
      (CA := fun T ↦ T) Y.J f (r, x))
  rintro V g' ⟨⟨r₀, y⟩, h⟩
  have hr := congrArg Prod.fst h
  have hx := congrArg Prod.snd h
  change (α.hom.app (Opposite.op V)).hom r₀ =
    (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.map g'.op r at hr
  change E.g.val.app (Opposite.op V) y = F.val.map g'.op x at hx
  change K.val.map g'.op _ = K.val.map g'.op _
  rw [K.val.map_smul, ← extensionActionPairing_naturality hi E g'.op,
    ← extensionActionPairing_naturality hi E g'.op,
    F.val.map_smul, ← hr, ← hx]
  have := sheafModule_mono_val E.f
  let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (hi.I.val.obj (Opposite.op V)) :=
    (((SheafOfModules.restrictScalars α).obj hi.I).val.obj (Opposite.op V)).isModule
  let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (F.val.obj (Opposite.op V)) :=
    (((SheafOfModules.restrictScalars α).obj F).val.obj (Opposite.op V)).isModule
  let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (K.val.obj (Opposite.op V)) :=
    (((SheafOfModules.restrictScalars α).obj K).val.obj (Opposite.op V)).isModule
  let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj (Opposite.op V))
      (K.val.obj (Opposite.op V)) := (K.val.obj (Opposite.op V)).isModule
  let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (E.Z.left.val.obj (Opposite.op V)) :=
    (E.Z.left.val.obj (Opposite.op V)).isModule
  let : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (E.Z.right.val.obj (Opposite.op V)) :=
    (E.Z.right.val.obj (Opposite.op V)).isModule
  let : SMul ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (E.Z.left.val.obj (Opposite.op V)) :=
    (inferInstance : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (E.Z.left.val.obj (Opposite.op V))).toDistribMulAction.toMulAction.toSMul
  let : SMul ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (E.Z.right.val.obj (Opposite.op V)) :=
    (inferInstance : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (E.Z.right.val.obj (Opposite.op V))).toDistribMulAction.toMulAction.toSMul
  let : SMul ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      ((actionModuleTypes E.Z.left.val).obj (Opposite.op V)) :=
    (inferInstance : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (E.Z.left.val.obj (Opposite.op V))).toDistribMulAction.toMulAction.toSMul
  let : SMul ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      ((actionModuleTypes E.Z.right.val).obj (Opposite.op V)) :=
    (inferInstance : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (E.Z.right.val.obj (Opposite.op V))).toDistribMulAction.toMulAction.toSMul
  let : SMul ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (hi.I.val.obj (Opposite.op V)) :=
    (inferInstance : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (hi.I.val.obj (Opposite.op V))).toDistribMulAction.toMulAction.toSMul
  let : SMul ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (F.val.obj (Opposite.op V)) :=
    (inferInstance : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (F.val.obj (Opposite.op V))).toDistribMulAction.toMulAction.toSMul
  let : SMul ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (K.val.obj (Opposite.op V)) :=
    (inferInstance : Module ((Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V))
      (K.val.obj (Opposite.op V))).toDistribMulAction.toMulAction.toSMul
  let r₀R : (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V) := r₀
  let q : (Stacks.SheafOfModules.Tensor.ringSheaf
      ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj.obj (Opposite.op V) :=
    (α.hom.app (Opposite.op V)).hom r₀
  let yV : E.Z.left.val.obj (Opposite.op V) := y
  let aV : hi.I.val.obj (Opposite.op V) := hi.I.val.map g'.op a
  let xV : F.val.obj (Opposite.op V) := E.g.val.app (Opposite.op V) yV
  have hqF (z : F.val.obj (Opposite.op V)) : q • z =
      (r₀R • z : ((SheafOfModules.restrictScalars α).obj F).val.obj
        (Opposite.op V)) := rfl
  have hqK (z : K.val.obj (Opposite.op V)) : q • z =
      (r₀R • z : ((SheafOfModules.restrictScalars α).obj K).val.obj
        (Opposite.op V)) := rfl
  change (extensionActionPairing hi E).app (Opposite.op V)
      (aV, q • xV) =
    q • (show K.val.obj (Opposite.op V) from
      (extensionActionPairing hi E).app (Opposite.op V)
        (aV, E.g.val.app (Opposite.op V) yV))
  rw [hqF]
  change (extensionActionPairing hi E).app (Opposite.op V)
      (aV, r₀R • E.g.val.app (Opposite.op V) yV) =
    r₀R • (show K.val.obj (Opposite.op V) from
      (extensionActionPairing hi E).app (Opposite.op V)
        (aV, E.g.val.app (Opposite.op V) yV))
  let pV : K.val.obj (Opposite.op V) :=
    (extensionActionPairing hi E).app (Opposite.op V)
      (aV, E.g.val.app (Opposite.op V) yV)
  rw [← map_smul (E.g.val.app (Opposite.op V)).hom r₀R yV]
  apply PresheafOfModules.injective_of_mono E.f.val (Opposite.op V)
  calc
    E.f.val.app (Opposite.op V)
        ((extensionActionPairing hi E).app (Opposite.op V)
          (aV, E.g.val.app (Opposite.op V) (r₀R • yV))) =
        (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj (Opposite.op V) from
          hi.incl.val.app (Opposite.op V) aV) • (r₀R • yV) := by
      rw [extensionActionPairing_lift, extensionActionLift_spec]
    _ = E.f.val.app (Opposite.op V) (r₀R • pV) := by
      have hsm : E.f.val.app (Opposite.op V) (r₀R • pV) =
          r₀R • E.f.val.app (Opposite.op V) pV :=
        map_smul (E.f.val.app (Opposite.op V)).hom r₀R pV
      rw [hsm]
      simp only [pV]
      rw [extensionActionPairing_lift, extensionActionLift_spec]
      exact smul_comm _ _ _

private noncomputable def extensionActionTensorDescPresheaf
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0) :
    PresheafOfModules.tensorObj hi.I.val F.val ⟶ K.val where
  app U := ModuleCat.MonoidalCategory.tensorLift
    (fun a x ↦ (extensionActionPairing hi E).app U (a, x))
    (extensionActionPairing_add_left hi E U)
    (extensionActionPairing_smul_left hi E U)
    (extensionActionPairing_add_right hi E U)
    (extensionActionPairing_smul_right hi E U)
  naturality {U V} g := by
    apply ModuleCat.MonoidalCategory.tensor_ext
    intro a x
    exact extensionActionPairing_naturality hi E g a x

private lemma extensionActionTensorDescPresheaf_tmul
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}] [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0)
    (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : F.val.obj U) :
    (extensionActionTensorDescPresheaf hi E).app U
        (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U] x) =
      (extensionActionPairing hi E).app U (a, x) := by
  rfl

add_to_stacks 08MB CategoryTheory.Abelian.YonedaExtension

/-- The canonical map `I ⊗[O] F → K`, characterized by multiplication by an
ideal section after lifting a section of `F` to the middle module. -/
@[stacks 08MB "canonical action map"]
public noncomputable def extensionActionMap
    [X.J.HasSheafCompose (forget RingCat.{w})]
    [Y.J.HasSheafCompose (forget RingCat.{w'})]
    [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
    {i : RingedToposHom X Y}
    [Y.J.WEqualsLocallyBijective AddCommGrpCat.{w'}]
    [HasSheafify Y.J AddCommGrpCat.{w'}]
    [HasWeakSheafify Y.J AddCommGrpCat.{w'}]
    (hi : FirstOrderThickening i)
    {F K : SheafOfModules.{w'}
      (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O))}
    (E : Abelian.YonedaExtension
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj F)
      ((SheafOfModules.restrictScalars
        (show Stacks.SheafOfModules.Tensor.ringSheaf Y.O ⟶
            Stacks.SheafOfModules.Tensor.ringSheaf
              ((pushforwardCommRingFunctor i.toToposHom).obj X.O) from
          (sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj K) 0) :
    { c : ((Stacks.SheafOfModules.Tensor.sheafTensor
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K //
      ∀ (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : E.Z.left.val.obj U),
        E.f.val.app U
            (c.val.app U
              (((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
                  i.toToposHom).obj X.O))
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
                  i.toToposHom).obj X.O)).obj)).unit.app
                (PresheafOfModules.tensorObj hi.I.val F.val)).app U
                (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U]
                  E.g.val.app U x))) =
          (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from
            hi.incl.val.app U a) • x } :=
  Classical.choice (show Nonempty { c :
      ((Stacks.SheafOfModules.Tensor.sheafTensor
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K //
      ∀ (U : Y.Cᵒᵖ) (a : hi.I.val.obj U) (x : E.Z.left.val.obj U),
        E.f.val.app U
            (c.val.app U
              (((PresheafOfModules.sheafificationAdjunction
                (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
                  i.toToposHom).obj X.O))
                (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
                  i.toToposHom).obj X.O)).obj)).unit.app
                (PresheafOfModules.tensorObj hi.I.val F.val)).app U
                (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U]
                  E.g.val.app U x))) =
          (show (Stacks.SheafOfModules.Tensor.ringSheaf Y.O).obj.obj U from
            hi.incl.val.app U a) • x } from by
    let R :=
      Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj X.O)
    let t := extensionActionTensorDescPresheaf hi E
    let c : ((Stacks.SheafOfModules.Tensor.sheafTensor
        ((pushforwardCommRingFunctor i.toToposHom).obj X.O)).obj hi.I).obj F ⟶ K := by
      change (PresheafOfModules.sheafification (R := R) (𝟙 R.obj)).obj
          (PresheafOfModules.tensorObj hi.I.val F.val) ⟶ K
      exact (PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm t
    refine ⟨⟨c, ?_⟩⟩
    intro U a x
    have hc : c.val.app U
        (((PresheafOfModules.sheafificationAdjunction
          (R := Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor
            i.toToposHom).obj X.O))
          (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf ((pushforwardCommRingFunctor i.toToposHom).obj
            X.O)).obj)).unit.app
          (PresheafOfModules.tensorObj hi.I.val F.val)).app U
          (a ⊗ₜ[((pushforwardCommRingFunctor i.toToposHom).obj X.O).obj.obj U]
            E.g.val.app U x)) =
        (extensionActionPairing hi E).app U (a, E.g.val.app U x) := by
      dsimp [c]
      change ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).symm t).val.app U
          (((PresheafOfModules.sheafificationAdjunction (𝟙 R.obj)).unit.app
            (PresheafOfModules.tensorObj hi.I.val F.val)).app U
            (a ⊗ₜ[R.obj.obj U] E.g.val.app U x)) = _
      exact (congrArg (fun q ↦ q.app U
          (a ⊗ₜ[R.obj.obj U] E.g.val.app U x))
          ((PresheafOfModules.sheafificationHomEquiv (𝟙 R.obj)).apply_symm_apply t)).trans
        (extensionActionTensorDescPresheaf_tmul hi E U a (E.g.val.app U x))
    rw [hc, extensionActionPairing_lift, extensionActionLift_spec])

end Deformation.ToposThickening

end
