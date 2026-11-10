module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.CategoryTheory.Sites.CoverLifting
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Direct image of (pre)sheaves of modules along a functor of sites

Let `f : C ⥤ D` be a functor and let `R : Dᵒᵖ ⥤ RingCat` be a presheaf of rings. Mathlib's
`PresheafOfModules.pushforward₀ f R` is the *inverse* image: it sends a presheaf of `R`-modules
to the presheaf of `f.op ⋙ R`-modules obtained by precomposition with `f.op`. This file
constructs its right adjoint, the direct image, as the pointwise right Kan extension along
`f.op`, computed by compatible families of sections indexed by `StructuredArrow x f.op`.

On the sheaf side, if `C` and `D` carry Grothendieck topologies `J` and `K` for which `f` is
both continuous and cocontinuous and `O` is a sheaf of rings on `D`, the direct image of a sheaf
of modules is again a sheaf: any pointwise right Kan extension along `f.op` of a sheaf is a
sheaf when `f` is cocontinuous. This yields the adjunction between the inverse image
`SheafOfModules.pushforward (𝟙 _)` and the direct image.

Over a terminal object the direct image computes the global sections of its argument: if `U` is
terminal in `C` and `X` is terminal in `D`, then the sections of the direct image over `X` are
the sections over `U`, as modules over the ring of global sections `R(X)`.

A functor `e : C₁ ⥤ C₂` over `D` induces a comparison `f_* f^{-1} ⟶ (e ∘ f)_* (e ∘ f)^{-1}`,
strictly functorial in `e`, obtained by restricting a compatible family of sections along the
functor of indexing categories; and the direct image along a composite of functors of sites is
the composite of the direct images.

## Main definitions

* `PresheafOfModules.directImageSections`: the compatible families of sections indexed by
  `StructuredArrow x f.op` which form the value of the direct image at `x`.
* `PresheafOfModules.directImageObj`: the direct image of a presheaf of modules.
* `PresheafOfModules.directImage`: the direct image functor on presheaves of modules.
* `PresheafOfModules.directImageCounit`: the counit of the right Kan extension, on underlying
  presheaves of abelian groups.
* `PresheafOfModules.restrictScalarsId`: restriction of scalars along an identity morphism of
  presheaves of rings is the identity functor.
* `PresheafOfModules.directImageReindex` and `SheafOfModules.directImageReindex`: the
  comparison `f_* f^{-1} ⟶ (e ∘ f)_* (e ∘ f)^{-1}` attached to a functor `e` over `D`.
* `SheafOfModules.directImage`: the direct image functor on sheaves of modules.
* `SheafOfModules.pushforward₀`: the inverse image of sheaves of modules in the strict form in
  which the structure sheaf of the source is the inverse image of that of the target on the
  nose, together with `SheafOfModules.pushforwardIdIsoPushforward₀` comparing it with
  `SheafOfModules.pushforward` along an identity.
* `SheafOfModules.directImageOfEq` and `SheafOfModules.pushforward₀OfEq`: the same two
  functors, for a structure sheaf identified with the inverse image of `O` by an equality.
* `SheafOfModules.directImageComp` and `SheafOfModules.directImageCompOfEq`: the direct image
  along a composite.

## Main results

* `PresheafOfModules.isPointwiseRightKanExtension_directImageCounit`: the direct image is the
  pointwise right Kan extension along `f.op`.
* `PresheafOfModules.directImageRanIso`: the underlying presheaf of abelian groups of the
  direct image is the right Kan extension along `f.op`.
* `PresheafOfModules.pushforward₀DirectImageAdjunction` and
  `PresheafOfModules.pushforwardDirectImageAdjunction`: the inverse image of presheaves of
  modules is left adjoint to the direct image, and
  `PresheafOfModules.directImageUnit_directImageCounit` is the triangle identity between them
  on underlying presheaves of abelian groups.
* `SheafOfModules.pushforwardDirectImageAdjunction`,
  `SheafOfModules.pushforward₀DirectImageAdjunction` and their `OfEq` variants: the inverse
  image of sheaves of modules is left adjoint to the direct image.
* `PresheafOfModules.directImageObjTerminalIso` and
  `SheafOfModules.directImageTerminalIso`: the direct image preserves global sections.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe r w vC vC₀ vC₁ vC₂ vD uC uC₂ uD

namespace PresheafOfModules

section RestrictScalarsId

variable {C : Type uC} [Category.{vC} C]

variable (R : Cᵒᵖ ⥤ RingCat.{r}) in
/-- Restriction of scalars along the identity morphism of a presheaf of rings is the identity
functor on presheaves of modules. -/
def restrictScalarsId :
    restrictScalars.{w} (𝟙 R) ≅ 𝟭 (PresheafOfModules.{w} R) :=
  NatIso.ofComponents
    (fun M ↦ isoMk (fun X ↦ ModuleCat.restrictScalarsId'App _ (by simp) (M.obj X))
      (fun {_ _} _ ↦ by ext x; rfl))
    (fun _ ↦ by ext X x; rfl)

variable {R : Cᵒᵖ ⥤ RingCat.{r}}

/-- The component of `PresheafOfModules.restrictScalarsId` at a section is the identity. -/
@[simp]
lemma restrictScalarsId_hom_app_apply (M : PresheafOfModules.{w} R) (X : Cᵒᵖ)
    (x : ((restrictScalars.{w} (𝟙 R)).obj M).obj X) :
    Hom.app ((restrictScalarsId.{r, w} R).hom.app M) X x = x :=
  rfl

/-- The component of the inverse of `PresheafOfModules.restrictScalarsId` at a section is the
identity. -/
@[simp]
lemma restrictScalarsId_inv_app_apply (M : PresheafOfModules.{w} R) (X : Cᵒᵖ) (x : M.obj X) :
    Hom.app ((restrictScalarsId.{r, w} R).inv.app M) X x = x :=
  rfl

/-- On underlying presheaves of abelian groups, `PresheafOfModules.restrictScalarsId` is the
identity: restriction of scalars along an identity does not touch the underlying presheaf, only
the scalar action, and the comparison of the two actions is the identity on sections. -/
@[simp]
lemma toPresheaf_map_restrictScalarsId_hom_app (M : PresheafOfModules.{w} R) :
    (toPresheaf.{w} R).map ((restrictScalarsId.{r, w} R).hom.app M) = 𝟙 _ :=
  rfl

/-- The inverse half of `PresheafOfModules.toPresheaf_map_restrictScalarsId_hom_app`. -/
@[simp]
lemma toPresheaf_map_restrictScalarsId_inv_app (M : PresheafOfModules.{w} R) :
    (toPresheaf.{w} R).map ((restrictScalarsId.{r, w} R).inv.app M) = 𝟙 _ :=
  rfl

/-- **Restriction of scalars along an identity is invisible on underlying presheaves of abelian
groups.** For a morphism `f` of presheaves of modules, `(restrictScalars (𝟙 R)).map f` and `f`
have the *same* underlying morphism of presheaves of abelian groups, on the nose.

This is the cheap way past `PresheafOfModules.restrictScalars (𝟙 R)`: it is an equality the
kernel accepts by `rfl` with no reduction of the `Module.compHom` instance, where the
corresponding comparison inside `PresheafOfModules` has to be made by the transport
`PresheafOfModules.restrictScalars_id_map`. Since `PresheafOfModules.toPresheaf` is faithful, an
equation between morphisms of presheaves of modules with `(restrictScalars (𝟙 R)).map f`
occurring inside it can be checked after applying `PresheafOfModules.toPresheaf`, and there the
occurrence simply disappears. -/
@[simp]
lemma toPresheaf_map_restrictScalars_id_map {M N : PresheafOfModules.{w} R} (f : M ⟶ N) :
    (toPresheaf.{w} R).map ((restrictScalars.{w} (𝟙 R)).map f) = (toPresheaf.{w} R).map f :=
  rfl

/-- Naturality of `PresheafOfModules.restrictScalarsId` in the presheaf of modules. -/
@[reassoc]
lemma restrictScalarsId_hom_naturality {M N : PresheafOfModules.{w} R} (f : M ⟶ N) :
    (restrictScalars.{w} (𝟙 R)).map f ≫ (restrictScalarsId.{r, w} R).hom.app N =
      (restrictScalarsId.{r, w} R).hom.app M ≫ f :=
  (restrictScalarsId.{r, w} R).hom.naturality f

/-- Naturality of the inverse of `PresheafOfModules.restrictScalarsId` in the presheaf of
modules. -/
@[reassoc]
lemma restrictScalarsId_inv_naturality {M N : PresheafOfModules.{w} R} (f : M ⟶ N) :
    f ≫ (restrictScalarsId.{r, w} R).inv.app N =
      (restrictScalarsId.{r, w} R).inv.app M ≫ (restrictScalars.{w} (𝟙 R)).map f :=
  (restrictScalarsId.{r, w} R).inv.naturality f

/-- **Restriction of scalars along an identity, applied to a morphism, is that morphism
conjugated by `PresheafOfModules.restrictScalarsId`.** This is the propositional substitute for
the definitional equality between `(restrictScalars (𝟙 R)).map f` and `f`, which a kernel asked
to check it directly has to reach through the `Module.compHom` instance on every module of
sections. -/
lemma restrictScalars_id_map {M N : PresheafOfModules.{w} R} (f : M ⟶ N) :
    (restrictScalars.{w} (𝟙 R)).map f =
      (restrictScalarsId.{r, w} R).hom.app M ≫ f ≫ (restrictScalarsId.{r, w} R).inv.app N :=
  (Iso.eq_comp_inv ((restrictScalarsId.{r, w} R).app N)).mpr
    ((restrictScalarsId.{r, w} R).hom.naturality f)

end RestrictScalarsId

section

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{r}) (N : PresheafOfModules.{max uC vD w} (f.op ⋙ R))

/-- The families of sections, indexed by the objects of `StructuredArrow x f.op`, that are
compatible with the morphisms of that category. This is the value at `x` of the direct image
along `f` of a presheaf of modules `N`, as a subgroup of the product of all its values. -/
def directImageSections (x : Dᵒᵖ) :
    AddSubgroup (∀ j : StructuredArrow x f.op, N.obj j.right) where
  carrier s := ∀ ⦃j k : StructuredArrow x f.op⦄ (g : j ⟶ k), N.map g.right (s j) = s k
  zero_mem' := by intro j k g; exact (N.map g.right).hom.map_zero
  add_mem' := by intro s t hs ht j k g; rw [Pi.add_apply, map_add, hs g, ht g]; rfl
  neg_mem' := by intro s hs j k g; rw [Pi.neg_apply, map_neg, hs g]; rfl

/-- A compatible family of sections of `N` over `StructuredArrow x f.op` can be multiplied by a
section of `R` over `x`, the scalar being transported to the index by the structural morphism. -/
instance directImageSectionsModule (x : Dᵒᵖ) :
    Module (R.obj x) (directImageSections f R N x) where
  smul a s := ⟨fun j ↦ R.map j.hom a • (show N.obj j.right from s.val j), by
    intro j k g
    change N.map g.right (R.map j.hom a • (show N.obj j.right from s.val j)) = _
    rw [N.map_smul]
    have hr : R.map (f.op.map g.right) (R.map j.hom a) = R.map k.hom a := by
      rw [← ConcreteCategory.comp_apply, ← R.map_comp, StructuredArrow.w g]
    change R.map (f.op.map g.right) (R.map j.hom a) • N.map g.right (s.val j) = _
    rw [hr]
    exact congrArg (fun z ↦ R.map k.hom a • z) (s.property g)⟩
  one_smul s := by
    apply Subtype.ext; funext j
    change (R.map j.hom).hom 1 • s.val j = s.val j
    rw [(R.map j.hom).hom.map_one, one_smul]
  mul_smul a b s := by
    apply Subtype.ext; funext j
    change (R.map j.hom).hom (a * b) • s.val j =
      (R.map j.hom).hom a • (R.map j.hom).hom b • s.val j
    rw [(R.map j.hom).hom.map_mul, mul_smul]
  smul_zero a := by
    apply Subtype.ext; funext j
    change (R.map j.hom).hom a • (0 : N.obj j.right) = 0
    simp
  smul_add a s t := by
    apply Subtype.ext; funext j
    change (R.map j.hom).hom a • (s.val j + t.val j) = _
    exact smul_add _ _ _
  add_smul a b s := by
    apply Subtype.ext; funext j
    change (R.map j.hom).hom (a + b) • s.val j =
      (R.map j.hom).hom a • s.val j + (R.map j.hom).hom b • s.val j
    rw [(R.map j.hom).hom.map_add, add_smul]
  zero_smul s := by
    apply Subtype.ext; funext j
    change (R.map j.hom).hom 0 • s.val j = 0
    rw [(R.map j.hom).hom.map_zero, zero_smul]

/-- The direct image along `f` of a presheaf of modules, on objects: its sections over `x` are
the compatible families of sections indexed by `StructuredArrow x f.op`. -/
def directImageObj : PresheafOfModules.{max uC vD w} R where
  obj x := ModuleCat.of (R.obj x) (directImageSections f R N x)
  map {x y} a := ModuleCat.ofHom
    (Y := (ModuleCat.restrictScalars (R.map a).hom).obj
      (ModuleCat.of (R.obj y) (directImageSections f R N y)))
    { toFun := fun s ↦ ⟨fun j ↦ s.val ((StructuredArrow.map a).obj j),
        fun {_ _} g ↦ s.property ((StructuredArrow.map a).map g)⟩
      map_add' := by intros; rfl
      map_smul' := by
        intro a' s
        apply Subtype.ext
        funext j
        change R.map (a ≫ j.hom) a' • _ = R.map j.hom (R.map a a') • _
        rw [R.map_comp]
        rfl }
  map_id x := by
    ext s
    apply Subtype.ext
    funext j
    change s.val ((StructuredArrow.map (𝟙 x)).obj j) = s.val j
    rcases j with ⟨⟨⟨⟩⟩, j, b⟩
    change s.val (StructuredArrow.mk (𝟙 x ≫ b)) = s.val (StructuredArrow.mk b)
    rw [Category.id_comp]
  map_comp a b := by
    ext s
    apply Subtype.ext
    funext j
    change s.val ((StructuredArrow.map (a ≫ b)).obj j) =
      s.val ((StructuredArrow.map a).obj ((StructuredArrow.map b).obj j))
    rcases j with ⟨⟨⟨⟩⟩, j, c⟩
    change s.val (StructuredArrow.mk ((a ≫ b) ≫ c)) =
      s.val (StructuredArrow.mk (a ≫ b ≫ c))
    rw [Category.assoc]

/-- The counit of the direct image, as a morphism of presheaves of abelian groups: a compatible
family indexed by `StructuredArrow (f.op.obj x) f.op` has a value at the identity index. -/
def directImageCounit : f.op ⋙ (directImageObj f R N).presheaf ⟶ N.presheaf where
  app x := AddCommGrpCat.ofHom
    { toFun := fun s ↦ s.val (StructuredArrow.mk (𝟙 (f.op.obj x)))
      map_zero' := rfl
      map_add' := by intros; rfl }
  naturality {x y} a := by
    ext s
    change s.val ((StructuredArrow.map (f.op.map a)).obj
      (StructuredArrow.mk (𝟙 (f.op.obj y)))) =
      N.map a (s.val (StructuredArrow.mk (𝟙 (f.op.obj x))))
    have h := s.property (StructuredArrow.homMk a :
      StructuredArrow.mk (𝟙 (f.op.obj x)) ⟶ StructuredArrow.mk (f.op.map a))
    change N.map a (s.val (StructuredArrow.mk (𝟙 (f.op.obj x)))) =
      s.val (StructuredArrow.mk (f.op.map a)) at h
    change s.val (StructuredArrow.mk (f.op.map a ≫ 𝟙 _)) = _
    rw [Category.comp_id]
    exact h.symm

/-- The counit of the direct image evaluates a compatible family, transported along the
structure arrow of an index `j`, at the identity index; the result is the value of the family
at `j`. -/
lemma directImageCounit_apply (x : Dᵒᵖ) (j : StructuredArrow x f.op)
    (s : directImageSections f R N x) :
    (directImageCounit.{r, w} f R N).app j.right ((directImageObj f R N).map j.hom s) =
      s.val j := by
  change s.val ((StructuredArrow.map j.hom).obj
    (StructuredArrow.mk (𝟙 (f.op.obj j.right)))) = _
  rcases j with ⟨⟨⟨⟩⟩, j, b⟩
  change s.val (StructuredArrow.mk (b ≫ 𝟙 _)) = s.val (StructuredArrow.mk b)
  rw [Category.comp_id]

/-- The direct image of a presheaf of modules is the pointwise right Kan extension of its
underlying presheaf of abelian groups along `f.op`. -/
def isPointwiseRightKanExtension_directImageCounit :
    (Functor.RightExtension.mk _
      (directImageCounit.{r, w} f R N)).IsPointwiseRightKanExtension := by
  intro x
  refine {
    lift := fun c ↦ AddCommGrpCat.ofHom
      { toFun := fun s ↦ ⟨fun j ↦ c.π.app j s, fun {_ _} g ↦ ?_⟩
        map_zero' := ?_
        map_add' := ?_ }
    fac := ?_
    uniq := ?_ }
  · exact congrFun (congrArg (fun k ↦ (k.hom : _ → _)) (c.w g)) s
  · apply Subtype.ext; funext j; exact map_zero _
  · intro s t; apply Subtype.ext; funext j; exact map_add _ _ _
  · intro c j
    ext s
    rcases j with ⟨⟨⟨⟩⟩, j, b⟩
    change c.π.app (StructuredArrow.mk (b ≫ 𝟙 _)) s = c.π.app (StructuredArrow.mk b) s
    rw [Category.comp_id]
  · intro c a ha
    ext s
    apply Subtype.ext
    funext j
    exact (directImageCounit_apply.{r, w} f R N x j _).symm.trans
      (ConcreteCategory.congr_hom (ha j) s)

end

section Adjunction

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{r})

/-- The direct image along `f` of a morphism of presheaves of modules. -/
def directImageMap {N N' : PresheafOfModules.{max uC vD w} (f.op ⋙ R)} (g : N ⟶ N') :
    directImageObj f R N ⟶ directImageObj f R N' where
  app x := ModuleCat.ofHom
    { toFun := fun s ↦ ⟨fun j ↦ g.app j.right (s.val j), by
        intro j k a
        dsimp
        change N'.map a.right (g.app j.right (s.val j)) = _
        rw [← PresheafOfModules.naturality_apply]
        exact congrArg (fun z ↦ g.app k.right z) (s.property a)⟩
      map_add' := by intros; apply Subtype.ext; funext j; exact map_add _ _ _
      map_smul' := by
        intro a s
        apply Subtype.ext
        funext j
        change g.app j.right (R.map j.hom a • (show N.obj j.right from s.val j)) =
          R.map j.hom a • (g.app j.right (s.val j))
        exact (g.app j.right).hom.map_smul _ _ }
  naturality := by intros; rfl

/-- The direct image functor on presheaves of modules along a functor `f : C ⥤ D`: it is right
adjoint to the inverse image `PresheafOfModules.pushforward₀ f R`. -/
def directImage : PresheafOfModules.{max uC vD w} (f.op ⋙ R) ⥤
    PresheafOfModules.{max uC vD w} R where
  obj := directImageObj f R
  map := directImageMap f R
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The unit of the adjunction between the inverse and direct images of presheaves of modules:
a section over `x` gives the compatible family of its restrictions. -/
def directImageUnit : 𝟭 (PresheafOfModules.{max uC vD w} R) ⟶
    pushforward₀ f R ⋙ directImage.{r, w} f R where
  app M :=
    { app x := ModuleCat.ofHom
        { toFun := fun t ↦ ⟨fun j ↦ M.map j.hom t, by
            intro j k g
            change M.map (f.op.map g.right) (M.map j.hom t) = M.map k.hom t
            rw [← M.map_comp_apply, StructuredArrow.w g]⟩
          map_add' := by intro t t'; apply Subtype.ext; funext j; exact map_add _ _ _
          map_smul' := by
            intro a t; apply Subtype.ext; funext j
            exact M.map_smul j.hom a t }
      naturality := by
        intro x y a
        ext t
        apply Subtype.ext
        funext j
        exact (M.map_comp_apply a j.hom t).symm }
  naturality := by
    intro M M' g
    ext x t
    apply Subtype.ext
    funext j
    exact (PresheafOfModules.naturality_apply g j.hom t).symm

/-- The counit of the adjunction between the inverse and direct images of presheaves of
modules: the morphism of presheaves of modules whose underlying morphism of presheaves of
abelian groups is `PresheafOfModules.directImageCounit`. -/
def directImageModuleCounit :
    directImage.{r, w} f R ⋙ pushforward₀ f R ⟶
      𝟭 (PresheafOfModules.{max uC vD w} (f.op ⋙ R)) where
  app N := PresheafOfModules.homMk (directImageCounit.{r, w} f R N) (by
    intro x a s
    change R.map (𝟙 (f.op.obj x)) a • s.val (StructuredArrow.mk (𝟙 _)) =
      a • s.val (StructuredArrow.mk (𝟙 _))
    rw [R.map_id]
    rfl)
  naturality := by intros; rfl

/-- The inverse image of presheaves of modules is left adjoint to the direct image. -/
def pushforward₀DirectImageAdjunction :
    pushforward₀.{max uC vD w} f R ⊣ directImage.{r, w} f R where
  unit := directImageUnit.{r, w} f R
  counit := directImageModuleCounit.{r, w} f R
  left_triangle_components M := by
    ext x t
    change M.map (𝟙 (f.op.obj x)) t = t
    rw [M.map_id]
    rfl
  right_triangle_components N := by
    ext x s
    apply Subtype.ext
    funext j
    exact directImageCounit_apply.{r, w} f R N x j s

/-- The unit and the counit of the direct image satisfy the triangle identity on underlying
presheaves of abelian groups: the family of restrictions of a section, evaluated at the
identity index, is that section. -/
lemma directImageUnit_directImageCounit (M : PresheafOfModules.{max uC vD w} R) :
    Functor.whiskerLeft f.op ((toPresheaf R).map ((directImageUnit.{r, w} f R).app M)) ≫
      directImageCounit.{r, w} f R ((pushforward₀ f R).obj M) = 𝟙 _ := by
  ext x t
  change M.map (𝟙 (f.op.obj x)) t = t
  rw [M.map_id]
  rfl

/-- The inverse image `PresheafOfModules.pushforward` for the identity morphism of
`f.op ⋙ R` agrees with `PresheafOfModules.pushforward₀`. -/
def pushforwardIdIsoPushforward₀ :
    pushforward.{max uC vD w} (F := f) (𝟙 (f.op ⋙ R)) ≅ pushforward₀.{max uC vD w} f R :=
  Functor.isoWhiskerLeft (pushforward₀.{max uC vD w} f R)
      (restrictScalarsId.{r, max uC vD w} (f.op ⋙ R)) ≪≫
    (pushforward₀.{max uC vD w} f R).rightUnitor

/-- The inverse image of presheaves of modules, in the form
`PresheafOfModules.pushforward (𝟙 _)` in which it appears on sheaves of modules, is left adjoint
to the direct image. -/
def pushforwardDirectImageAdjunction :
    pushforward.{max uC vD w} (F := f) (𝟙 (f.op ⋙ R)) ⊣ directImage.{r, w} f R :=
  Adjunction.ofNatIsoLeft (pushforward₀DirectImageAdjunction.{r, w} f R)
    (pushforwardIdIsoPushforward₀.{r, w} f R).symm

end Adjunction

section Terminal

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{r})

/-- The index of `StructuredArrow (op X) f.op` attached to an object `U` of `C` and a terminal
object `X` of `D`. When `U` is terminal it is initial in that category. -/
def terminalStructuredArrow (U : C) {X : D} (hX : IsTerminal X) :
    StructuredArrow (op X) f.op :=
  StructuredArrow.mk (hX.from (f.obj U)).op

/-- Every index of `StructuredArrow (op X) f.op` is reached from
`PresheafOfModules.terminalStructuredArrow` by the morphism coming from a terminal object `U`
of `C`. -/
def terminalStructuredArrowHom {U : C} (hU : IsTerminal U) {X : D} (hX : IsTerminal X)
    (j : StructuredArrow (op X) f.op) :
    terminalStructuredArrow f U hX ⟶ j :=
  StructuredArrow.homMk (hU.from j.right.unop).op (Quiver.Hom.unop_inj (hX.hom_ext _ _))

/-- Global sections of the direct image, as a map to the global sections of `N`: evaluation of a
compatible family at the index attached to the terminal objects. -/
def directImageObjTerminalHom (N : PresheafOfModules.{max uC vD w} (f.op ⋙ R))
    (U : C) {X : D} (hX : IsTerminal X) :
    (directImageObj f R N).obj (op X) ⟶
      (ModuleCat.restrictScalars (R.map (hX.from (f.obj U)).op).hom).obj (N.obj (op U)) :=
  ModuleCat.ofHom
    (X := (directImageObj f R N).obj (op X))
    (Y := (ModuleCat.restrictScalars (R.map (hX.from (f.obj U)).op).hom).obj (N.obj (op U)))
    { toFun := fun s ↦ s.val (terminalStructuredArrow f U hX)
      map_add' := fun _ _ ↦ rfl
      map_smul' := fun _ _ ↦ rfl }

/-- Global sections of `N`, as a map to the global sections of the direct image: a section over
a terminal object `U` of `C` restricts to a compatible family. -/
def directImageObjTerminalInv (N : PresheafOfModules.{max uC vD w} (f.op ⋙ R))
    {U : C} (hU : IsTerminal U) {X : D} (hX : IsTerminal X) :
    (ModuleCat.restrictScalars (R.map (hX.from (f.obj U)).op).hom).obj (N.obj (op U)) ⟶
      (directImageObj f R N).obj (op X) :=
  ModuleCat.ofHom
    (X := (ModuleCat.restrictScalars (R.map (hX.from (f.obj U)).op).hom).obj (N.obj (op U)))
    (Y := (directImageObj f R N).obj (op X))
    { toFun := fun t ↦ ⟨fun j ↦ N.map (hU.from j.right.unop).op t, by
        intro j k g
        refine (N.map_comp_apply ((hU.from j.right.unop).op) g.right t).symm.trans ?_
        exact N.congr_map_apply (Quiver.Hom.unop_inj (hU.hom_ext _ _)) t⟩
      map_add' := by intro t t'; apply Subtype.ext; funext j; exact map_add _ _ _
      map_smul' := fun a t ↦ Subtype.ext (funext fun j ↦ by
        have hs : R.map (f.op.map (hU.from j.right.unop).op)
            (R.map (hX.from (f.obj U)).op a) = R.map j.hom a := by
          rw [← ConcreteCategory.comp_apply, ← R.map_comp]
          exact congrArg (fun u ↦ R.map u a) (Quiver.Hom.unop_inj (hX.hom_ext _ _))
        exact (N.map_smul (hU.from j.right.unop).op (R.map (hX.from (f.obj U)).op a)
            (t : N.obj (op U))).trans
          (congrArg (fun z ↦ z • N.map (hU.from j.right.unop).op (t : N.obj (op U))) hs)) }

/-- The direct image preserves global sections: if `U` is terminal in `C` and `X` is terminal in
`D`, the sections of the direct image of `N` over `X` are the sections of `N` over `U`, as
modules over the ring `R(X)` of global sections of `R`. -/
def directImageObjTerminalIso (N : PresheafOfModules.{max uC vD w} (f.op ⋙ R))
    {U : C} (hU : IsTerminal U) {X : D} (hX : IsTerminal X) :
    (directImageObj f R N).obj (op X) ≅
      (ModuleCat.restrictScalars (R.map (hX.from (f.obj U)).op).hom).obj (N.obj (op U)) where
  hom := directImageObjTerminalHom.{r, w} f R N U hX
  inv := directImageObjTerminalInv.{r, w} f R N hU hX
  hom_inv_id := by
    refine ModuleCat.hom_ext (LinearMap.ext fun s ↦ Subtype.ext (funext fun j ↦ ?_))
    exact s.property (terminalStructuredArrowHom f hU hX j)
  inv_hom_id := by
    have hid : ∀ m : N.obj (op U), N.map (𝟙 (op U)) m = m := by
      intro m; rw [N.map_id]; rfl
    refine ModuleCat.hom_ext (@LinearMap.ext _ _ _ _ _ _ _ _ (_) (_) _ _ _ fun t ↦ ?_)
    exact (N.congr_map_apply
        (Quiver.Hom.unop_inj (hU.hom_ext _ _) : (hU.from U).op = 𝟙 (op U))
        (t : N.obj (op U))).trans (hid t)

end Terminal

section Reindex

variable {C₁ : Type uC} [Category.{vC₁} C₁] {C₂ : Type uC} [Category.{vC₂} C₂]
  {D : Type uD} [Category.{vD} D] (e : C₁ ⥤ C₂) (f : C₂ ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{r})

/-- Reindexing the direct image of an inverse image along a functor `e` over `D`: a compatible
family of sections indexed by `StructuredArrow x f.op` restricts to one indexed by
`StructuredArrow x (e ⋙ f).op`, because an index of the latter becomes one of the former by
applying `e`. This is the comparison `f_* f^{-1} ⟶ (e ∘ f)_* (e ∘ f)^{-1}`, on a presheaf of
modules. -/
def directImageReindexApp (M : PresheafOfModules.{max uC vD w} R) :
    (directImage.{r, w} f R).obj ((pushforward₀ f R).obj M) ⟶
      (directImage.{r, w} (e ⋙ f) R).obj ((pushforward₀ (e ⋙ f) R).obj M) where
  app x := ModuleCat.ofHom
    { toFun := fun s ↦ ⟨fun k ↦ s.val ((StructuredArrow.pre x e.op f.op).obj k),
        fun {_ _} g ↦ s.property ((StructuredArrow.pre x e.op f.op).map g)⟩
      map_add' := by intros; rfl
      map_smul' := by intros; rfl }
  naturality := by intros; rfl

/-- The comparison `f_* f^{-1} ⟶ (e ∘ f)_* (e ∘ f)^{-1}` of `directImageReindexApp`, as a
natural transformation of functors on presheaves of modules. -/
def directImageReindex :
    pushforward₀.{max uC vD w} f R ⋙ directImage.{r, w} f R ⟶
      pushforward₀.{max uC vD w} (e ⋙ f) R ⋙ directImage.{r, w} (e ⋙ f) R where
  app M := directImageReindexApp.{r, w} e f R M
  naturality := by intros; rfl

/-- Reindexing along the identity functor does nothing. -/
lemma directImageReindex_id : directImageReindex.{r, w} (𝟭 C₂) f R = 𝟙 _ := rfl

/-- Reindexing is compatible with composition of functors over `D`. -/
lemma directImageReindex_comp {C₀ : Type uC} [Category.{vC₀} C₀] (e' : C₀ ⥤ C₁) :
    directImageReindex.{r, w} (e' ⋙ e) f R =
      directImageReindex.{r, w} e f R ≫ directImageReindex.{r, w} e' (e ⋙ f) R := rfl

/-- The comparison map is the one determined by the counits: evaluating the reindexed family
at an identity index is evaluating the original family at the image index. -/
lemma directImageReindex_counit (M : PresheafOfModules.{max uC vD w} R) :
    Functor.whiskerLeft (e ⋙ f).op
        ((toPresheaf R).map (directImageReindexApp.{r, w} e f R M)) ≫
      directImageCounit.{r, w} (e ⋙ f) R ((pushforward₀ (e ⋙ f) R).obj M) =
      Functor.whiskerLeft e.op
        (directImageCounit.{r, w} f R ((pushforward₀ f R).obj M)) := rfl

end Reindex

section RanComparison

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) (R : Dᵒᵖ ⥤ RingCat.{r})
  (N : PresheafOfModules.{max uC vD w} (f.op ⋙ R))

/-- The underlying presheaf of abelian groups of the direct image of a presheaf of modules is
a right Kan extension along `f.op`, by
`PresheafOfModules.isPointwiseRightKanExtension_directImageCounit`. -/
instance isRightKanExtension_directImageCounit :
    (((directImage.{r, w} f R).obj N).presheaf).IsRightKanExtension
      (directImageCounit.{r, w} f R N) :=
  (isPointwiseRightKanExtension_directImageCounit.{r, w} f R N).isRightKanExtension

/-- The comparison from the underlying presheaf of abelian groups of the direct image to the
right Kan extension along `f.op`. -/
def directImageRanHom :
    ((directImage.{r, w} f R).obj N).presheaf ⟶ f.op.ran.obj N.presheaf :=
  Functor.liftOfIsRightKanExtension _ (f.op.ranCounit.app N.presheaf) _
    (directImageCounit.{r, w} f R N)

/-- The comparison map of `PresheafOfModules.directImageRanHom` is compatible with the two
counits. -/
@[reassoc]
lemma directImageRanHom_fac :
    Functor.whiskerLeft f.op (directImageRanHom.{r, w} f R N) ≫
        f.op.ranCounit.app N.presheaf =
      directImageCounit.{r, w} f R N :=
  Functor.liftOfIsRightKanExtension_fac _ _ _ _

/-- The comparison map with the right Kan extension is an isomorphism, since the direct image
is itself a right Kan extension of the same presheaf. -/
instance isIso_directImageRanHom : IsIso (directImageRanHom.{r, w} f R N) :=
  (Functor.isRightKanExtension_iff_isIso (directImageRanHom.{r, w} f R N)
    (f.op.ranCounit.app N.presheaf) (directImageCounit.{r, w} f R N)
    (directImageRanHom_fac.{r, w} f R N)).1 inferInstance

/-- The underlying presheaf of abelian groups of the direct image of a presheaf of modules is
the right Kan extension along `f.op` of the underlying presheaf of `N`: both are right Kan
extensions of the same presheaf. -/
def directImageRanIso :
    ((directImage.{r, w} f R).obj N).presheaf ≅ f.op.ran.obj N.presheaf :=
  asIso (directImageRanHom.{r, w} f R N)

/-- The comparison with the right Kan extension is compatible with the two counits. -/
@[reassoc]
lemma directImageRanIso_fac :
    Functor.whiskerLeft f.op (directImageRanIso.{r, w} f R N).hom ≫
        f.op.ranCounit.app N.presheaf =
      directImageCounit.{r, w} f R N :=
  directImageRanHom_fac.{r, w} f R N

end RanComparison

end PresheafOfModules

namespace SheafOfModules

variable {C : Type uC} [Category.{vC} C] {D : Type uD} [Category.{vD} D]
  (f : C ⥤ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [f.IsContinuous J K] [f.IsCocontinuous J K] (O : Sheaf K RingCat.{r})

/-- The inverse image of sheaves of modules along a continuous functor of sites, in the strict
form in which the structure sheaf of the source is the inverse image of that of the target on
the nose: restriction along `f.op`, with no restriction of scalars. -/
def pushforward₀ :
    SheafOfModules.{max uC vD w} O ⥤
      SheafOfModules.{max uC vD w}
        ((f.sheafPushforwardContinuous RingCat.{r} J K).obj O) where
  obj M :=
    { val := (PresheafOfModules.pushforward₀ f O.obj).obj M.val
      isSheaf := f.op_comp_isSheaf J K ⟨M.val.presheaf, M.isSheaf⟩ }
  map g := ⟨(PresheafOfModules.pushforward₀ f O.obj).map g.val⟩
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The strict inverse image agrees with `SheafOfModules.pushforward` along the identity
morphism of the inverse image of the structure sheaf: the two differ by restriction of scalars
along an identity. -/
def pushforwardIdIsoPushforward₀ :
    pushforward.{max uC vD w} (𝟙 ((f.sheafPushforwardContinuous RingCat.{r} J K).obj O)) ≅
      pushforward₀.{r, w} f J K O :=
  NatIso.ofComponents
    (fun M ↦
      { hom := ⟨((PresheafOfModules.pushforwardIdIsoPushforward₀.{r, w} f O.obj).app M.val).hom⟩
        inv := ⟨((PresheafOfModules.pushforwardIdIsoPushforward₀.{r, w} f O.obj).app M.val).inv⟩
        hom_inv_id := SheafOfModules.hom_ext
          ((PresheafOfModules.pushforwardIdIsoPushforward₀.{r, w} f O.obj).app M.val).hom_inv_id
        inv_hom_id := SheafOfModules.hom_ext
          ((PresheafOfModules.pushforwardIdIsoPushforward₀.{r, w} f O.obj).app M.val).inv_hom_id })
    (fun ψ ↦ SheafOfModules.hom_ext
      ((PresheafOfModules.pushforwardIdIsoPushforward₀.{r, w} f O.obj).hom.naturality ψ.val))

/-- The direct image functor on sheaves of modules along a functor of sites which is both
continuous and cocontinuous: the underlying presheaf of modules is the direct image of
presheaves of modules, which is a sheaf because it is a pointwise right Kan extension along
`f.op` of a sheaf and `f` is cocontinuous. -/
def directImage :
    SheafOfModules.{max uC vD w} ((f.sheafPushforwardContinuous RingCat.{r} J K).obj O) ⥤
      SheafOfModules.{max uC vD w} O where
  obj N :=
    { val := PresheafOfModules.directImageObj f O.obj N.val
      isSheaf := by
        rw [Presheaf.isSheaf_iff_multifork]
        intro X S
        exact ⟨RanIsSheafOfIsCocontinuous.isLimitMultifork N.isSheaf
          (PresheafOfModules.isPointwiseRightKanExtension_directImageCounit.{r, w}
            f O.obj N.val) S⟩ }
  map g := ⟨PresheafOfModules.directImageMap f O.obj g.val⟩
  map_id := by intros; rfl
  map_comp := by intros; rfl

/-- The inverse image of sheaves of modules is left adjoint to the direct image. -/
@[sga "4 Vbis 2.4.0" "partial"]
def pushforwardDirectImageAdjunction :
    pushforward.{max uC vD w} (𝟙 ((f.sheafPushforwardContinuous RingCat.{r} J K).obj O)) ⊣
      directImage.{r, w} f J K O :=
  Adjunction.restrictFullyFaithful
    (PresheafOfModules.pushforwardDirectImageAdjunction.{r, w} f O.obj)
    (fullyFaithfulForget _) (fullyFaithfulForget _)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

/-- The inverse image of sheaves of modules is a left adjoint. -/
instance :
    (pushforward.{max uC vD w}
      (𝟙 ((f.sheafPushforwardContinuous RingCat.{r} J K).obj O))).IsLeftAdjoint :=
  (pushforwardDirectImageAdjunction.{r, w} f J K O).isLeftAdjoint

/-- The strict inverse image of sheaves of modules is left adjoint to the direct image. -/
def pushforward₀DirectImageAdjunction :
    pushforward₀.{r, w} f J K O ⊣ directImage.{r, w} f J K O :=
  Adjunction.restrictFullyFaithful
    (PresheafOfModules.pushforward₀DirectImageAdjunction.{r, w} f O.obj)
    (fullyFaithfulForget _) (fullyFaithfulForget _)
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))
    (NatIso.ofComponents (fun _ ↦ Iso.refl _) (fun _ ↦ rfl))

/-- The direct image, for a sheaf of rings `T` on `C` which is *equal* to the inverse image of
`O` rather than being it on the nose. This is the shape in which the structure sheaf of the
source of a 1-morphism of fibred categories is identified with the restriction of the structure
sheaf of the target. -/
@[sga "4 Vbis 2.4.0" "partial"]
def directImageOfEq {T : Sheaf J RingCat.{r}}
    (hT : T = (f.sheafPushforwardContinuous RingCat.{r} J K).obj O) :
    SheafOfModules.{max uC vD w} T ⥤ SheafOfModules.{max uC vD w} O := by
  subst hT
  exact directImage.{r, w} f J K O

/-- The inverse image of sheaves of modules along an equality identification of the structure
sheaves is left adjoint to the direct image. -/
@[sga "4 Vbis 2.4.0" "partial"]
def pushforwardDirectImageAdjunctionOfEq {T : Sheaf J RingCat.{r}}
    (hT : T = (f.sheafPushforwardContinuous RingCat.{r} J K).obj O) :
    pushforward.{max uC vD w} (eqToHom hT) ⊣ directImageOfEq.{r, w} f J K O hT := by
  subst hT
  exact pushforwardDirectImageAdjunction.{r, w} f J K O

/-- The strict inverse image, for a sheaf of rings `T` on `C` which is *equal* to the inverse
image of `O` rather than being it on the nose. -/
def pushforward₀OfEq {T : Sheaf J RingCat.{r}}
    (hT : T = (f.sheafPushforwardContinuous RingCat.{r} J K).obj O) :
    SheafOfModules.{max uC vD w} O ⥤ SheafOfModules.{max uC vD w} T := by
  subst hT
  exact pushforward₀.{r, w} f J K O

/-- The strict inverse image along an equality identification of the structure sheaves agrees
with `SheafOfModules.pushforward` along the corresponding `eqToHom`. -/
def pushforwardOfEqIsoPushforward₀OfEq {T : Sheaf J RingCat.{r}}
    (hT : T = (f.sheafPushforwardContinuous RingCat.{r} J K).obj O) :
    pushforward.{max uC vD w} (eqToHom hT) ≅ pushforward₀OfEq.{r, w} f J K O hT := by
  subst hT
  exact pushforwardIdIsoPushforward₀.{r, w} f J K O

/-- The strict inverse image along an equality identification of the structure sheaves is left
adjoint to the direct image. -/
def pushforward₀DirectImageAdjunctionOfEq {T : Sheaf J RingCat.{r}}
    (hT : T = (f.sheafPushforwardContinuous RingCat.{r} J K).obj O) :
    pushforward₀OfEq.{r, w} f J K O hT ⊣ directImageOfEq.{r, w} f J K O hT := by
  subst hT
  exact pushforward₀DirectImageAdjunction.{r, w} f J K O

section Reindex

variable {C₁ : Type uC} [Category.{vC₁} C₁] {C₂ : Type uC} [Category.{vC₂} C₂]
  {D' : Type uD} [Category.{vD} D'] (e : C₁ ⥤ C₂) (g : C₂ ⥤ D')
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂) (K' : GrothendieckTopology D')
  [g.IsContinuous J₂ K'] [g.IsCocontinuous J₂ K']
  [(e ⋙ g).IsContinuous J₁ K'] [(e ⋙ g).IsCocontinuous J₁ K']
  (O : Sheaf K' RingCat.{r})

/-- Reindexing the direct image of an inverse image along a functor `e` over the target:
the comparison `g_* g^{-1} ⟶ (e ∘ g)_* (e ∘ g)^{-1}` on sheaves of modules. -/
def directImageReindex :
    pushforward₀.{r, w} g J₂ K' O ⋙ directImage.{r, w} g J₂ K' O ⟶
      pushforward₀.{r, w} (e ⋙ g) J₁ K' O ⋙ directImage.{r, w} (e ⋙ g) J₁ K' O where
  app M := ⟨PresheafOfModules.directImageReindexApp.{r, w} e g O.obj M.val⟩
  naturality := by intros; rfl

/-- Reindexing along the identity functor does nothing. -/
lemma directImageReindex_id [(𝟭 C₂ ⋙ g).IsContinuous J₂ K']
    [(𝟭 C₂ ⋙ g).IsCocontinuous J₂ K'] :
    directImageReindex.{r, w} (𝟭 C₂) g J₂ J₂ K' O = 𝟙 _ := rfl

/-- Reindexing is compatible with composition of functors over the target. -/
lemma directImageReindex_comp {C₀ : Type uC} [Category.{vC₀} C₀] (e' : C₀ ⥤ C₁)
    (J₀ : GrothendieckTopology C₀)
    [(e' ⋙ e ⋙ g).IsContinuous J₀ K'] [(e' ⋙ e ⋙ g).IsCocontinuous J₀ K']
    [((e' ⋙ e) ⋙ g).IsContinuous J₀ K'] [((e' ⋙ e) ⋙ g).IsCocontinuous J₀ K'] :
    directImageReindex.{r, w} (e' ⋙ e) g J₀ J₂ K' O =
      directImageReindex.{r, w} e g J₁ J₂ K' O ≫
        directImageReindex.{r, w} e' (e ⋙ g) J₀ J₁ K' O := rfl

end Reindex

section Comp

variable {C₁ : Type uC} [Category.{vC₁} C₁] {C₂ : Type uC₂} [Category.{vC₂} C₂]
  {D' : Type uD} [Category.{vD} D'] (e : C₁ ⥤ C₂) (g : C₂ ⥤ D')
  (J₁ : GrothendieckTopology C₁) (J₂ : GrothendieckTopology C₂) (K' : GrothendieckTopology D')
  [g.IsContinuous J₂ K'] [g.IsCocontinuous J₂ K']
  [e.IsContinuous J₁ J₂] [e.IsCocontinuous J₁ J₂]
  [(e ⋙ g).IsContinuous J₁ K'] [(e ⋙ g).IsCocontinuous J₁ K']
  (O : Sheaf K' RingCat.{r})

/-- The direct image along a composite is the composite of the direct images: both are right
adjoint to the inverse image along the composite, which is the composite of the inverse
images. -/
@[sga "4 Vbis 2.4.0" "partial"]
def directImageComp :
    directImage.{r, max uC uC₂ vC₂ vD w} e J₁ J₂
          ((g.sheafPushforwardContinuous RingCat.{r} J₂ K').obj O) ⋙
        directImage.{r, max uC uC₂ vC₂ vD w} g J₂ K' O ≅
      directImage.{r, max uC uC₂ vC₂ vD w} (e ⋙ g) J₁ K' O :=
  Adjunction.rightAdjointUniq
    (((pushforwardDirectImageAdjunction.{r, max uC uC₂ vC₂ vD w} g J₂ K' O).comp
      (pushforwardDirectImageAdjunction.{r, max uC uC₂ vC₂ vD w} e J₁ J₂
        ((g.sheafPushforwardContinuous RingCat.{r} J₂ K').obj O))).ofNatIsoLeft (Iso.refl _))
    (pushforwardDirectImageAdjunction.{r, max uC uC₂ vC₂ vD w} (e ⋙ g) J₁ K' O)

/-- The direct image along a composite, for structure sheaves identified with inverse images
by equalities rather than on the nose. -/
def directImageCompOfEq {T₁ : Sheaf J₂ RingCat.{r}}
    (hT₁ : T₁ = (g.sheafPushforwardContinuous RingCat.{r} J₂ K').obj O)
    {T₂ : Sheaf J₁ RingCat.{r}}
    (hT₂ : T₂ = (e.sheafPushforwardContinuous RingCat.{r} J₁ J₂).obj T₁)
    (hT₃ : T₂ = ((e ⋙ g).sheafPushforwardContinuous RingCat.{r} J₁ K').obj O) :
    directImageOfEq.{r, max uC uC₂ vC₂ vD w} e J₁ J₂ T₁ hT₂ ⋙
        directImageOfEq.{r, max uC uC₂ vC₂ vD w} g J₂ K' O hT₁ ≅
      directImageOfEq.{r, max uC uC₂ vC₂ vD w} (e ⋙ g) J₁ K' O hT₃ := by
  subst hT₁
  subst hT₂
  exact directImageComp.{r, w} e g J₁ J₂ K' O

end Comp

/-- The direct image preserves global sections: if `U` is terminal in `C` and `X` is terminal in
`D`, the sections of the direct image of `N` over `X` are the sections of `N` over `U`, as
modules over the ring `Γ(D, O)` of global sections of the structure sheaf. -/
def directImageTerminalIso
    (N : SheafOfModules.{max uC vD w}
      ((f.sheafPushforwardContinuous RingCat.{r} J K).obj O))
    {U : C} {X : D} (hU : IsTerminal U) (hX : IsTerminal X) :
    ((directImage.{r, w} f J K O).obj N).val.obj (op X) ≅
      (ModuleCat.restrictScalars (O.obj.map (hX.from (f.obj U)).op).hom).obj
        (N.val.obj (op U)) :=
  PresheafOfModules.directImageObjTerminalIso.{r, w} f O.obj N.val hU hX

end SheafOfModules

end
