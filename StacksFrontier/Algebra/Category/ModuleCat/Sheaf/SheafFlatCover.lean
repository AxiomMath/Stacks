module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Free
public import Mathlib.CategoryTheory.Abelian.Pseudoelements
public import Mathlib.RingTheory.Flat.CategoryTheory
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.TensorRightSplitExactness
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorExactness
public import StacksFrontier.CategoryTheory.Functor.Bifunctor
public import StacksCore.Tactic.StacksAttribute

/-!
# Flat covers of sheaves of modules, and exactness of the tensor product

Let `O` be a sheaf of commutative rings on a site `C`. This file develops the flatness theory
of sheaves of `O`-modules needed for Stacks 03EX: *tensoring a short exact sequence of sheaves
of modules whose third term is flat with an arbitrary sheaf of modules again gives a short
exact sequence.*

Three things are built, in dependency order.

**Right exactness of the tensor product.** Tensoring presheaves of modules on the right with a
fixed presheaf of modules preserves all colimits, because colimits of presheaves of modules are
computed sectionwise and tensoring in `ModuleCat` has a right adjoint. The sheaf-level tensor
product `Stacks.SheafOfModules.Tensor.sheafTensor` is "forget to presheaves, tensor, sheafify",
and the forgetful functor does **not** preserve colimits, so the sheaf-level statement is not
formal. It is proved by going through the presheaf-level colimit: the comparison morphism from
the colimit of the underlying presheaves to the underlying presheaf of the colimit sheaf becomes
an isomorphism after sheafification, hence is locally bijective, and
`Stacks.isIso_sheafification_map_tensorRight_map` says that tensoring followed by sheafification
does not see a locally bijective morphism.

**Flat covers (Stacks 03EW).** The free presheaf of modules on the underlying presheaf of sets
of a presheaf of modules `M` surjects onto `M` and is sectionwise free, hence sectionwise flat;
since limits of presheaves of modules are also computed sectionwise, tensoring with it is left
exact. Sheafifying gives an epimorphism onto any sheaf of modules from a **flat** sheaf of
modules: right exactness of its tensor functor is the result above, and left exactness is the
composite of three left exact functors once the free cover is substituted for its sheafification,
which is legitimate because the unit of sheafification is locally bijective.

**Stacks 03EX.** Right exactness already gives exactness in the middle and an epimorphism on the
right, so only injectivity on the left is at issue. Following the source, one resolves `G` by a
flat `G'`, forms the 3-by-3 diagram of the `S`-sequence tensored with `G'' → G' → G`, and chases
it; `Stacks.mono_of_threeByThree` isolates that chase as a statement about an arbitrary abelian
category, proved with `CategoryTheory.Abelian.Pseudoelement`. The symmetry of the tensor product
(`Stacks.tensorObjComm`) is what lets the rows of the diagram — where the morphism varies in the
*second* tensor variable — inherit exactness from the first-variable statements.

## Main definitions

* `Stacks.freeCover` is the free presheaf of modules on the sections of a presheaf of modules,
  and `Stacks.fromFreeCover` the canonical surjection from it, both at module universe equal to
  the ring universe. `Stacks.freeCoverSplit` and `Stacks.fromFreeCoverSplit` are the same two
  at split universes and are what the sheaf-level half uses.
* `Stacks.sheafFreeCover` is the free presheaf of modules on the sections of a sheaf of modules,
  `Stacks.flatCover` its sheafification, a flat sheaf of modules, and `Stacks.fromFlatCover`
  the canonical epimorphism onto the original sheaf of modules; `Stacks.flatResolution`
  packages the resulting short exact sequence.
* `Stacks.tensorObjComm` is the symmetry of the objectwise tensor product of presheaves of
  modules, and `Stacks.tensorRightNatTrans` the natural transformation obtained by tensoring a
  morphism in the second variable.
* `Stacks.tensorRightComplex` maps a short complex through the native tensor functor
  in its second variable.
* `Stacks.moduleSheafification` is the sheafification functor for presheaves of modules over the
  sheaf of rings underlying `O`, and `Stacks.tensorRightOf` is `Stacks.tensorRight` with both of
  its module universes set to the module universe of the sheaf-level statements.

## Main results

* `Stacks.preservesColimitsOfSize_tensorRight`: tensoring presheaves of modules on the right
  preserves colimits.
* `Stacks.preservesFiniteLimits_tensorRight_of_flat_obj`: tensoring on the right with a
  sectionwise flat presheaf of modules preserves finite limits.
* `Stacks.isColimitSheafTensorRightMapCocone` and
  `Stacks.preservesColimitsOfSize_sheafTensorRight`: the tensor product of sheaves of modules
  is right exact in the first variable.
* `Stacks.isFlat_flatCover`: **Stacks 03EW for sheaves of modules** — every sheaf of modules
  admits an epimorphism from a flat one.
* `Stacks.mono_of_threeByThree`: the 3-by-3 diagram lemma behind 03EX.
* `Stacks.tensorRightComplexIso`: the symmetry isomorphism identifying tensoring a short
  complex in the second variable with tensoring it in the first.
* `Stacks.sheafTensorRight_shortExact_of_flat`: **Stacks 03EX**, part (2).
* `Stacks.sheafTensorRight_shortExact_of_flat_of_univLE`: the same, with the sheafification
  hypotheses replaced by the universe inequality that produces them.

## Implementation notes

### The module universe

The sheaf-level statements are at module universe `max t w` over a sheaf of rings in
`CommRingCat.{w}`, with `t` free and the site universes `u` and `v` independent of both. The
inequality `w ≤ max t w` is forced, and `max t w` is its general solution; nothing else is
pinned.

What forces it is the **flat cover**, which is a free module. The free module on a set in
`Type z` over a ring in `Type w` has carrier in `Type (max z w)`, so it is an object of
`PresheafOfModules.{z}` only when `w ≤ z`. For a module universe `z` not dominating `w` the
category contains no nonzero free module over `Stacks.ringPresheaf O` at all, so no flat-cover
route to 03EX exists there; `Stacks.sheafTensorRight_shortExact_of_flat` is therefore stated at
the universes where its proof's one universe-sensitive ingredient exists, and not at a free `z`.

Two single-universe declarations of Mathlib would pin the module universe to `w` itself, and
split-universe versions of both are used instead. `PresheafOfModules.freeObj` is stated for a
presheaf of sets in `Type u` over a presheaf of rings in `RingCat.{u}`, one universe serving as
both; `StacksFrontier.Algebra.Category.ModuleCat.Presheaf.FreeSplitUniverse` reruns it as
`PresheafOfModules.freeSplitObj` with the two separated. `MonoidalCategory (ModuleCat.{u} R)` is
stated for a ring carrier in the module category's own `Type u`;
`StacksFrontier.Algebra.Category.ModuleCat.TensorRightSplitUniverse` reruns the tensor-hom
adjunction and flatness as `ModuleCat.tensorRightSplit`, and
`StacksFrontier.Algebra.Category.ModuleCat.Presheaf.TensorRightSplitExactness` reruns the
sectionwise colimit and limit arguments through it.

The presheaf-level helpers of this file about `Stacks.tensorObj` and `Stacks.tensorMapRight`
(`Stacks.tensorRightNatTrans`, `Stacks.tensorObjComm` and their lemmas) are at a free module
universe `z`: they mention no free module and no monoidal structure, and their proofs are
`TensorProduct.ext` followed by `rfl`.

### The sheafification hypotheses

`HasSheafify` — weak sheafification *together with* left exactness of it — rather than
`HasWeakSheafify` is required, and is what Stacks assumes by working on a site: `ShortExact`
typechecks without any instance, but every tool for proving one needs
`SheafOfModules (Stacks.SheafOfModules.Tensor.ringSheaf O)` to be abelian, and Mathlib's only
instance for that (`Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian`) is derived from the
sheafification adjunction and requires `HasSheafify`, not merely `HasWeakSheafify`.

At module universe `max t w` those binders are not an independent assumption:
`CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat` produce all three
from `UnivLE.{max u v, max t w}`, which at `t := max u v` holds unconditionally.
`Stacks.sheafTensorRight_shortExact_of_flat_of_univLE` records that.

### Other choices

The flat cover is built from `PresheafOfModules.freeSplitObj` applied to the presheaf of
sections rather than from `PresheafOfModules.fromFreeYonedaCoproduct`, which is the direct
analogue of the source's `⨁ j_{Uᵢ!} O_{Uᵢ}`: the latter is stated in Mathlib only for a small
category with all four universes equal. The two agree, since the free module on the sections of
`M` is exactly the direct sum over pairs `(U, s)` with `s ∈ M(U)`.

`Stacks.sheafTensorMapRight_eq_zero` names
`CategoryTheory.Functor.preservesZeroMorphisms_of_isLeftAdjoint` explicitly: it is the instance
that typeclass search finds for `(Stacks.moduleSheafification O).PreservesZeroMorphisms`, but
only after exhausting the `Additive` and `Full` routes, which at a split module universe costs
more than the synthesis budget.

## References

* [Stacks Project, Tag 03EW](https://stacks.math.columbia.edu/tag/03EW)
* [Stacks Project, Tag 03EX](https://stacks.math.columbia.edu/tag/03EX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open TensorProduct

universe v u w z t s s'

namespace Stacks

section General

variable {D A B : Type*} [Category D] [Category A] [Category B]

/-- The image under `G` of a leg of a colimit cocone `s`, followed by the image of the
comparison morphism `hs.desc t`, is the image of the corresponding leg of `t`. -/
lemma mapCocone_ι_app_comp_map_desc {K : D ⥤ A} {s : Cocone K} (hs : IsColimit s)
    (G : A ⥤ B) (t : Cocone K) (j : D) :
    (G.mapCocone s).ι.app j ≫ G.map (hs.desc t) = (G.mapCocone t).ι.app j := by
  simp only [Functor.mapCocone_ι_app, ← G.map_comp, hs.fac]

/-- A functor which preserves a colimit cocone turns the comparison morphism to another
colimit cocone into an isomorphism. -/
lemma isIso_map_desc {K : D ⥤ A} {s : Cocone K} (hs : IsColimit s) (G : A ⥤ B)
    [PreservesColimitsOfShape D G] {t : Cocone K} (ht : IsColimit (G.mapCocone t)) :
    IsIso (G.map (hs.desc t)) := by
  rw [(isColimitOfPreserves G hs).uniq (G.mapCocone t) _
    (mapCocone_ι_app_comp_map_desc hs G t)]
  exact ((isColimitOfPreserves G hs).nonempty_isColimit_iff_isIso_desc).1 ⟨ht⟩

/-- Conversely, a functor which preserves a colimit cocone and turns the comparison morphism
to another cocone into an isomorphism sends that cocone to a colimit cocone. -/
noncomputable def isColimitMapCocone {K : D ⥤ A} {s : Cocone K} (hs : IsColimit s)
    (G : A ⥤ B) [PreservesColimitsOfShape D G] (t : Cocone K)
    (h : IsIso (G.map (hs.desc t))) : IsColimit (G.mapCocone t) := by
  haveI : IsIso ((isColimitOfPreserves G hs).desc (G.mapCocone t)) := by
    rw [← (isColimitOfPreserves G hs).uniq (G.mapCocone t) _
      (mapCocone_ι_app_comp_map_desc hs G t)]
    exact h
  exact (isColimitOfPreserves G hs).ofPointIso

/-- A functor sends two equal composites to equal composites of the images. -/
lemma map_comp_eq_map_comp (F : A ⥤ B) {X Y Z X' : A} {f : X ⟶ Y} {g : Y ⟶ Z}
    {f' : X ⟶ X'} {g' : X' ⟶ Z} (h : f ≫ g = f' ≫ g') :
    F.map f ≫ F.map g = F.map f' ≫ F.map g' := by
  rw [← F.map_comp, ← F.map_comp, h]

end General

section ThreeByThree

open CategoryTheory.Abelian.Pseudoelement

attribute [local instance] CategoryTheory.Abelian.Pseudoelement.homToFun

variable {A : Type*} [Category A] [Abelian A]

/-- **A 3-by-3 diagram lemma.**

Consider a commutative diagram
```
M₁₁ --a₁--> M₁₂ --b₁--> M₁₃
 |           |           |
 u₁          u₂          u₃
 v           v           v
M₂₁ --a₂--> M₂₂ --b₂--> M₂₃
 |           |
 v₁          v₂
 v           v
M₃₁ --a₃--> M₃₂
```
in an abelian category in which the first column and the second row are exact, the first row
and the second column are complexes, `b₁` is an epimorphism and `u₂` and `a₃` are
monomorphisms. Then `u₃` is a monomorphism.

This is the diagram chase behind Stacks 03EX: with `Mᵢⱼ = Xᵢ ⊗ Gⱼ` for a short exact
sequence `X₁ → X₂ → X₃` and a flat resolution `G₁ → G₂ → G₃` of `G = G₃`, the hypotheses say
that tensoring is right exact in each variable, that `G₂` is flat (giving the second column
exact on the left) and that `X₃` is flat (giving the third row exact on the left). -/
lemma mono_of_threeByThree
    {M₁₁ M₁₂ M₁₃ M₂₁ M₂₂ M₂₃ M₃₁ M₃₂ : A}
    {a₁ : M₁₁ ⟶ M₁₂} {b₁ : M₁₂ ⟶ M₁₃}
    {a₂ : M₂₁ ⟶ M₂₂} {b₂ : M₂₂ ⟶ M₂₃}
    {a₃ : M₃₁ ⟶ M₃₂}
    {u₁ : M₁₁ ⟶ M₂₁} {v₁ : M₂₁ ⟶ M₃₁}
    {u₂ : M₁₂ ⟶ M₂₂} {v₂ : M₂₂ ⟶ M₃₂}
    {u₃ : M₁₃ ⟶ M₂₃}
    (hz₁ : u₁ ≫ v₁ = 0) (hcol₁ : (ShortComplex.mk u₁ v₁ hz₁).Exact)
    (hz₂ : a₂ ≫ b₂ = 0) (hrow₂ : (ShortComplex.mk a₂ b₂ hz₂).Exact)
    (hrow₁ : a₁ ≫ b₁ = 0) (hcol₂ : u₂ ≫ v₂ = 0)
    (sq₁ : a₁ ≫ u₂ = u₁ ≫ a₂) (sq₂ : b₁ ≫ u₃ = u₂ ≫ b₂)
    (sq₃ : a₂ ≫ v₂ = v₁ ≫ a₃)
    [Epi b₁] [Mono u₂] [Mono a₃] :
    Mono u₃ := by
  refine mono_of_zero_of_map_zero _ fun x hx ↦ ?_
  obtain ⟨y, rfl⟩ := pseudo_surjective_of_epi b₁ x
  have h1 : b₂ (u₂ y) = 0 := by
    rw [← Abelian.Pseudoelement.comp_apply, ← sq₂, Abelian.Pseudoelement.comp_apply]
    exact hx
  obtain ⟨z, hz⟩ := pseudo_exact_of_exact hrow₂ _ h1
  have hz' : a₂ z = u₂ y := hz
  have h2 : a₃ (v₁ z) = 0 := by
    rw [← Abelian.Pseudoelement.comp_apply, ← sq₃, Abelian.Pseudoelement.comp_apply, hz',
      ← Abelian.Pseudoelement.comp_apply, hcol₂, Abelian.Pseudoelement.zero_apply]
  have h3 : v₁ z = 0 :=
    zero_of_map_zero _ (pseudo_injective_of_mono a₃) _ h2
  obtain ⟨t, ht⟩ := pseudo_exact_of_exact hcol₁ _ h3
  have ht' : u₁ t = z := ht
  have h4 : u₂ (a₁ t) = u₂ y := by
    rw [← Abelian.Pseudoelement.comp_apply, sq₁, Abelian.Pseudoelement.comp_apply, ht', hz']
  have h5 : a₁ t = y := pseudo_injective_of_mono u₂ h4
  rw [← h5, ← Abelian.Pseudoelement.comp_apply, hrow₁, Abelian.Pseudoelement.zero_apply]

end ThreeByThree

variable {C : Type u} [Category.{v} C] {O : Cᵒᵖ ⥤ CommRingCat.{w}}

/-- Tensoring presheaves of modules on the right with `F` preserves colimits. -/
instance preservesColimitsOfSize_tensorRight (F : PresheafOfModules.{w} (ringPresheaf O)) :
    PreservesColimitsOfSize.{w, w}
      (tensorRight F : PresheafOfModules.{w} (ringPresheaf O) ⥤ _) where
  preservesColimitsOfShape := ⟨⟨fun hc ↦ ⟨by
    refine PresheafOfModules.evaluationJointlyReflectsColimits _ _ (fun X ↦ ?_)
    haveI : PreservesColimits (MonoidalCategory.tensorRight
        (show ModuleCat.{w} ((ringPresheaf O).obj X) from F.obj X)) :=
      preservesColimits_of_natIso (BraidedCategory.tensorLeftIsoTensorRight _)
    exact isColimitOfPreserves (MonoidalCategory.tensorRight
      (show ModuleCat.{w} ((ringPresheaf O).obj X) from F.obj X))
      (isColimitOfPreserves (PresheafOfModules.evaluation _ X) hc)⟩⟩⟩

/-- Tensoring presheaves of modules on the right with `F` preserves finite colimits. -/
instance preservesFiniteColimits_tensorRight (F : PresheafOfModules.{w} (ringPresheaf O)) :
    PreservesFiniteColimits
      (tensorRight F : PresheafOfModules.{w} (ringPresheaf O) ⥤ _) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Tensoring on the right, as a functor of the *second* variable: the natural
transformation `tensorRight N ⟶ tensorRight N'` induced by `α : N ⟶ N'`. -/
noncomputable def tensorRightNatTrans {N N' : PresheafOfModules.{z} (ringPresheaf O)}
    (α : N ⟶ N') :
    (tensorRight N : PresheafOfModules.{z} (ringPresheaf O) ⥤ _) ⟶ tensorRight N' where
  app M := tensorMapRight M α
  naturality _ _ _ := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

/-- The component of `Stacks.tensorRightNatTrans α` at `M` is `Stacks.tensorMapRight M α`. -/
@[simp]
lemma tensorRightNatTrans_app {N N' : PresheafOfModules.{z} (ringPresheaf O)} (α : N ⟶ N')
    (M : PresheafOfModules.{z} (ringPresheaf O)) :
    (tensorRightNatTrans α).app M = tensorMapRight M α := rfl

/-- **Tensoring on the right with an objectwise flat presheaf of modules is left exact.**
Limits of presheaves of modules are computed sectionwise, so this reduces to flatness of
each module of sections. -/
lemma preservesFiniteLimits_tensorRight_of_flat_obj
    (N : PresheafOfModules.{w} (ringPresheaf O))
    (hN : ∀ X : Cᵒᵖ, Module.Flat ((ringPresheaf O).obj X) (N.obj X)) :
    PreservesFiniteLimits (tensorRight N : PresheafOfModules.{w} (ringPresheaf O) ⥤ _) := by
  refine ⟨fun D _ _ ↦ ⟨⟨fun hc ↦ ⟨?_⟩⟩⟩⟩
  refine PresheafOfModules.evaluationJointlyReflectsLimits _ _ fun X ↦ ?_
  have := hN X
  exact isLimitOfPreserves (MonoidalCategory.tensorRight
    (show ModuleCat.{w} ((ringPresheaf O).obj X) from N.obj X))
    (isLimitOfPreserves (PresheafOfModules.evaluation _ X) hc)

/-- Tensoring with `M` in the second variable is compatible with composition. -/
lemma tensorMapRight_comp (M : PresheafOfModules.{z} (ringPresheaf O))
    {N N' N'' : PresheafOfModules.{z} (ringPresheaf O)} (α : N ⟶ N') (β : N' ⟶ N'') :
    tensorMapRight M α ≫ tensorMapRight M β = tensorMapRight M (α ≫ β) := by
  refine PresheafOfModules.tensorObj_hom_ext fun X x y ↦ rfl

/-- Tensoring the zero morphism with `M` in the second variable gives the zero morphism. -/
lemma tensorMapRight_eq_zero (M : PresheafOfModules.{z} (ringPresheaf O))
    {N N' : PresheafOfModules.{z} (ringPresheaf O)} (α : N ⟶ N') (hα : α = 0) :
    tensorMapRight M α = 0 := by
  subst hα
  refine PresheafOfModules.tensorObj_hom_ext fun X x y ↦ ?_
  show x ⊗ₜ[(ringPresheaf O).obj X] (0 : N'.obj X) = 0
  rw [TensorProduct.tmul_zero]

section Comm

variable (M N : PresheafOfModules.{z} (ringPresheaf O))

/-- The symmetry of the objectwise tensor product of presheaves of modules. -/
noncomputable def tensorCommHom : tensorObj M N ⟶ tensorObj N M where
  app X := ModuleCat.ofHom
    (TensorProduct.comm ((ringPresheaf O).obj X) (M.obj X) (N.obj X)).toLinearMap
  naturality := by
    intro X Y f
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

/-- The symmetry `Stacks.tensorCommHom M N` sends `x ⊗ y` to `y ⊗ x`. -/
@[simp]
lemma tensorCommHom_app_tmul (X : Cᵒᵖ) (x : M.obj X) (y : N.obj X) :
    (tensorCommHom M N).app X (show (tensorObj M N).obj X from
        x ⊗ₜ[(ringPresheaf O).obj X] y) =
      y ⊗ₜ[(ringPresheaf O).obj X] x := rfl

/-- **The objectwise tensor product of presheaves of modules is symmetric.** -/
@[simps]
noncomputable def tensorObjComm : tensorObj M N ≅ tensorObj N M where
  hom := tensorCommHom M N
  inv := tensorCommHom N M
  hom_inv_id := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl
  inv_hom_id := by
    apply PresheafOfModules.hom_ext
    intro X
    apply ModuleCat.hom_ext
    apply TensorProduct.ext
    ext x y
    rfl

end Comm

/-- Under the symmetry of the tensor product, tensoring a morphism in the second variable
becomes tensoring it in the first variable. -/
lemma tensorCommHom_comp_tensorRight_map (M : PresheafOfModules.{z} (ringPresheaf O))
    {N N' : PresheafOfModules.{z} (ringPresheaf O)} (α : N ⟶ N') :
    tensorMapRight M α ≫ tensorCommHom M N' =
      tensorCommHom M N ≫ (tensorRight M).map α := by
  refine PresheafOfModules.tensorObj_hom_ext fun X x y ↦ rfl

section FreeCover

variable (M : PresheafOfModules.{w} (ringPresheaf O))

/-- The free presheaf of modules on the underlying presheaf of sets of `M`. It is objectwise
free, hence objectwise flat, and it maps onto `M`. -/
noncomputable abbrev freeCover : PresheafOfModules.{w} (ringPresheaf O) :=
  PresheafOfModules.freeObj (M.presheaf ⋙ forget _)

/-- The canonical surjection from the free presheaf of modules on the sections of `M`. -/
noncomputable def fromFreeCover : freeCover M ⟶ M :=
  PresheafOfModules.freeObjDesc (𝟙 (M.presheaf ⋙ forget _))

/-- `Stacks.fromFreeCover M` sends the basis vector of a section `m` to `m`. -/
@[simp]
lemma fromFreeCover_app_freeMk (X : Cᵒᵖ) (m : M.obj X) :
    (fromFreeCover M).app X (ModuleCat.freeMk m) = m :=
  ModuleCat.freeDesc_apply _ m

/-- The canonical morphism from the free cover of `M` onto `M` is an epimorphism. -/
instance epi_fromFreeCover : Epi (fromFreeCover M) :=
  PresheafOfModules.epi_of_surjective fun _ m ↦
    ⟨ModuleCat.freeMk m, fromFreeCover_app_freeMk M _ m⟩

/-- Every module of sections of the free cover of `M` is flat. -/
lemma flat_freeCover_obj (X : Cᵒᵖ) :
    Module.Flat ((ringPresheaf O).obj X) ((freeCover M).obj X) := by
  show Module.Flat ((ringPresheaf O).obj X)
    ((M.presheaf ⋙ forget _).obj X →₀ (ringPresheaf O).obj X)
  infer_instance

/-- Tensoring on the right with the free cover of `M` preserves finite limits. -/
lemma preservesFiniteLimits_tensorRight_freeCover :
    PreservesFiniteLimits
      (tensorRight (freeCover M) : PresheafOfModules.{w} (ringPresheaf O) ⥤ _) :=
  preservesFiniteLimits_tensorRight_of_flat_obj _ (flat_freeCover_obj M)

end FreeCover

section Sheaf

variable {J : GrothendieckTopology C}
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max t w}]
  [HasWeakSheafify J AddCommGrpCat.{max t w}]

/-- Sheafification of presheaves of modules over the sheaf of rings underlying `O`. -/
noncomputable abbrev moduleSheafification
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (O : Sheaf J CommRingCat.{w}) :
    PresheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj ⥤
      SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  PresheafOfModules.sheafification (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)

variable (O : Sheaf J CommRingCat.{w})

/-- The identity of the presheaf of rings underlying `O`, viewed as the locally bijective
comparison morphism to the underlying presheaf of the associated sheaf of rings. This is the
form in which the sheafification functor for presheaves of modules consumes it. -/
noncomputable abbrev ringSheafCompare
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] :
    ringPresheaf O.obj ⟶ (Stacks.SheafOfModules.Tensor.ringSheaf O).obj :=
  𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj

-- The two sheafification binders of this section are omitted so that the universe `t`, which
-- occurs in them and nowhere in the conclusions, does not become an undeterminable parameter
-- of these two instances: with it present, typeclass synthesis cannot use them at all.
omit [J.WEqualsLocallyBijective AddCommGrpCat.{max t w}]
  [HasWeakSheafify J AddCommGrpCat.{max t w}] in
/-- The morphism `Stacks.ringSheafCompare O` is locally injective. -/
instance isLocallyInjective_ringSheafCompare :
    Presheaf.IsLocallyInjective J (ringSheafCompare O) :=
  Presheaf.isLocallyInjective_of_injective _ _ fun _ _ _ h ↦ h

omit [J.WEqualsLocallyBijective AddCommGrpCat.{max t w}]
  [HasWeakSheafify J AddCommGrpCat.{max t w}] in
/-- The morphism `Stacks.ringSheafCompare O` is locally surjective. -/
instance isLocallySurjective_ringSheafCompare :
    Presheaf.IsLocallySurjective J (ringSheafCompare O) :=
  Presheaf.isLocallySurjective_of_surjective _ _ fun _ b ↦ ⟨b, rfl⟩

/-- `Stacks.tensorRight` with both of its module universes set to `max t w`, which makes it an
endofunctor and is the shape in which the sheaf-level statements use it. -/
noncomputable abbrev tensorRightOf
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (N : PresheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :
    PresheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj ⥤
      PresheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj :=
  tensorRight N

/-- Tensoring presheaves of modules on the right with `N` preserves colimits. -/
instance preservesColimitsOfSize_tensorRightOf
    (N : PresheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :
    PreservesColimitsOfSize.{max t w, max t w} (tensorRightOf O N) :=
  preservesColimitsOfSize_tensorRight_split (O := O.obj) N

/-- Tensoring presheaves of modules on the right with `N` preserves finite colimits. -/
instance preservesFiniteColimits_tensorRightOf
    (N : PresheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj) :
    PreservesFiniteColimits (tensorRightOf O N) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

/-- Sheafifying the underlying presheaf of modules of a sheaf of modules gives it back:
the counit of the sheafification adjunction is an isomorphism. -/
noncomputable def forgetCompModuleSheafificationIso :
    SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙ moduleSheafification O ≅
      𝟭 _ := by
  have e := asIso ((PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).counit)
  exact e

/-- **The tensor product of sheaves of modules is right exact in the first variable.**

A colimit cocone of sheaves of modules stays a colimit after tensoring with a fixed sheaf of
modules. The forgetful functor to presheaves of modules does *not* preserve colimits, so the
proof goes through the presheaf-level colimit: the comparison morphism from it to the
underlying presheaf of the colimit sheaf is locally bijective, and
`Stacks.isIso_sheafification_map_tensorRight_map` says that tensoring and then sheafifying
does not see a locally bijective morphism in the first variable. -/
@[ega "0 4.1.5" "partial"]
noncomputable def isColimitSheafTensorRightMapCocone
    (F : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    {D : Type s} [Category.{s'} D]
    {K : D ⥤ SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)}
    [HasColimitsOfShape D
      (PresheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)]
    [PreservesColimitsOfShape D (tensorRightOf O F.val)]
    (c : Cocone K) (hc : IsColimit c) :
    IsColimit (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
      F).mapCocone c) := by
  have hP : IsColimit (colimit.cocone
      (K ⋙ SheafOfModules.forget.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :=
    colimit.isColimit _
  haveI : PreservesColimitsOfShape D
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙ moduleSheafification O) :=
    preservesColimitsOfShape_of_natIso (forgetCompModuleSheafificationIso O).symm
  haveI hu : IsIso ((moduleSheafification O).map
      (hP.desc ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O)).mapCocone c))) :=
    isIso_map_desc hP (moduleSheafification O) (isColimitOfPreserves
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
        moduleSheafification O) hc)
  have hW := W_toPresheaf_map_of_isIso (O := O.obj) (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
    (ringSheafCompare O) _ hu
  haveI := hW.isLocallyInjective
  haveI := hW.isLocallySurjective
  refine isColimitMapCocone hP (tensorRightOf O F.val ⋙ moduleSheafification O)
    ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O)).mapCocone c) ?_
  exact isIso_sheafification_map_tensorRight_map (O := O.obj)
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (N := F.val) (ringSheafCompare O)
    (hP.desc ((SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O)).mapCocone c))

/-- Tensoring sheaves of modules on the right with `F` preserves colimits. -/
instance preservesColimitsOfSize_sheafTensorRight
    (F : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    PreservesColimitsOfSize.{max t w, max t w}
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj F) where
  preservesColimitsOfShape :=
    ⟨⟨fun hc ↦ ⟨isColimitSheafTensorRightMapCocone O F _ hc⟩⟩⟩

/-- Tensoring sheaves of modules on the right with `F` preserves finite colimits. -/
instance preservesFiniteColimits_sheafTensorRight
    (F : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    PreservesFiniteColimits
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj F) :=
  PreservesColimitsOfSize.preservesFiniteColimits _

section FlatCover

variable [HasSheafify J AddCommGrpCat.{max t w}]
  (G : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O))

/-- The free presheaf of modules on the sections of a sheaf of modules. -/
noncomputable abbrev sheafFreeCover
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] :
    PresheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O).obj :=
  freeCoverSplit (O := O.obj) G.val

/-- **Stacks 03EW for sheaves of modules.** The flat cover of a sheaf of modules `G`: the
sheafification of the free presheaf of modules on the sections of `G`. -/
noncomputable def flatCover : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O) :=
  (moduleSheafification O).obj (sheafFreeCover O G)

/-- The canonical surjection from the free presheaf of modules on the sections of `G`,
viewed in the category of presheaves of modules over the ring sheaf of `O`. -/
noncomputable abbrev fromSheafFreeCover : sheafFreeCover O G ⟶ G.val :=
  fromFreeCoverSplit (O := O.obj) G.val

/-- The canonical morphism from the free cover of `G` onto `G.val` is an epimorphism. -/
instance : Epi (fromSheafFreeCover O G) := epi_fromFreeCoverSplit _

/-- Sheafifying the underlying presheaf of modules of a sheaf of modules returns it. -/
noncomputable def sheafifyValIso : (moduleSheafification O).obj G.val ≅ G :=
  (forgetCompModuleSheafificationIso O).app G

/-- The canonical epimorphism onto `G` from its flat cover. -/
noncomputable def fromFlatCover : flatCover O G ⟶ G :=
  (moduleSheafification O).map (fromSheafFreeCover O G) ≫ (sheafifyValIso O G).hom

/-- The canonical morphism from the flat cover of `G` onto `G` is an epimorphism. -/
instance : Epi (fromFlatCover O G) := by
  change Epi ((moduleSheafification O).map (fromSheafFreeCover O G) ≫ (sheafifyValIso O G).hom)
  infer_instance

/-- The unit of sheafification at the free cover: a locally bijective morphism from the free
presheaf of modules on the sections of `G` to the underlying presheaf of the flat cover. -/
noncomputable abbrev toFlatCoverVal : sheafFreeCover O G ⟶ (flatCover O G).val :=
  (PresheafOfModules.sheafificationAdjunction
    (R := Stacks.SheafOfModules.Tensor.ringSheaf O)
    (𝟙 (Stacks.SheafOfModules.Tensor.ringSheaf O).obj)).unit.app _

/-- The unit of sheafification at the free cover of `G` is locally injective. -/
instance : Presheaf.IsLocallyInjective J
    ((PresheafOfModules.toPresheaf (ringPresheaf O.obj)).map (toFlatCoverVal O G)) := by
  change Presheaf.IsLocallyInjective J
    (CategoryTheory.toSheafify J (sheafFreeCover O G).presheaf)
  infer_instance

/-- The unit of sheafification at the free cover of `G` is locally surjective. -/
instance : Presheaf.IsLocallySurjective J
    ((PresheafOfModules.toPresheaf (ringPresheaf O.obj)).map (toFlatCoverVal O G)) := by
  change Presheaf.IsLocallySurjective J
    (CategoryTheory.toSheafify J (sheafFreeCover O G).presheaf)
  infer_instance

/-- Tensoring and then sheafifying does not distinguish the free cover of `G` from its
sheafification, because the unit of sheafification is locally bijective and
`Stacks.isIso_sheafification_map_tensorMapRight` says the second tensor variable does not
see a local bijection. -/
noncomputable def tensorRightFlatCoverIso :
    tensorRightOf O (sheafFreeCover O G) ⋙ moduleSheafification O ≅
      tensorRightOf O (flatCover O G).val ⋙ moduleSheafification O := by
  haveI : ∀ M, IsIso ((Functor.whiskerRight
      (tensorRightNatTrans (O := O.obj) (toFlatCoverVal O G))
      (moduleSheafification O)).app M) := fun M ↦
    isIso_sheafification_map_tensorMapRight (O := O.obj)
      (R := Stacks.SheafOfModules.Tensor.ringSheaf O) (M := M) (ringSheafCompare O)
      (toFlatCoverVal O G)
  haveI := NatIso.isIso_of_isIso_app (Functor.whiskerRight
    (tensorRightNatTrans (O := O.obj) (toFlatCoverVal O G)) (moduleSheafification O))
  have e := asIso (Functor.whiskerRight
    (tensorRightNatTrans (O := O.obj) (toFlatCoverVal O G)) (moduleSheafification O))
  exact e

/-- **The flat cover of a sheaf of modules is flat.**

Left exactness comes from the free presheaf of modules being objectwise free, hence
objectwise flat: the forgetful functor to presheaves of modules preserves limits, tensoring
with an objectwise flat presheaf of modules preserves finite limits, and sheafification is
left exact once `HasSheafify` holds. Right exactness holds for every sheaf of modules. -/
theorem isFlat_flatCover : SheafOfModules.IsFlat (flatCover O G) := by
  refine (exactFunctor_iff _).2 ⟨?_, inferInstance⟩
  let : PreservesFiniteLimits (tensorRightOf O (sheafFreeCover O G)) :=
    preservesFiniteLimits_tensorRight_freeCoverSplit (O := O.obj) G.val
  let : PreservesFiniteLimits
      (tensorRightOf O (sheafFreeCover O G) ⋙ moduleSheafification O) :=
    comp_preservesFiniteLimits _ _
  let : PreservesFiniteLimits
      (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O) ⋙
        (tensorRightOf O (sheafFreeCover O G) ⋙ moduleSheafification O)) :=
    comp_preservesFiniteLimits _ _
  exact preservesFiniteLimits_of_natIso
    (Functor.isoWhiskerLeft (SheafOfModules.forget (Stacks.SheafOfModules.Tensor.ringSheaf O))
      (tensorRightFlatCoverIso O G))

end FlatCover

section TensorExactness

variable [HasSheafify J AddCommGrpCat.{max t w}]

/-- The short complex obtained from a short complex `E` of sheaves of modules by tensoring
it in the second variable with a fixed sheaf of modules `M`. -/
noncomputable def tensorRightComplex
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
    (M : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (E : ShortComplex (SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    ShortComplex (SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  letI : HasFiniteBiproducts
      (SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  E.map ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).obj M)

/-- **Symmetry of the tensor product of sheaves of modules.** Tensoring a short complex in
the second variable by `M` is isomorphic to tensoring it in the first variable by `M`. -/
noncomputable def tensorRightComplexIso
    (M : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (E : ShortComplex (SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O))) :
    tensorRightComplex O M E ≅
      E.map ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj M) :=
  ShortComplex.isoMk
    ((moduleSheafification O).mapIso (tensorObjComm (O := O.obj) M.val E.X₁.val))
    ((moduleSheafification O).mapIso (tensorObjComm (O := O.obj) M.val E.X₂.val))
    ((moduleSheafification O).mapIso (tensorObjComm (O := O.obj) M.val E.X₃.val))
    (map_comp_eq_map_comp (moduleSheafification O)
      (tensorCommHom_comp_tensorRight_map (O := O.obj) M.val E.f.val).symm)
    (map_comp_eq_map_comp (moduleSheafification O)
      (tensorCommHom_comp_tensorRight_map (O := O.obj) M.val E.g.val).symm)

/-- A short exact sequence of sheaves of modules stays exact on the right when tensored with
a fixed sheaf of modules `N` in the first variable. -/
private lemma exact_and_epi_sheafTensorRight
    (S : ShortComplex (SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (hS : S.ShortExact)
    (N : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
      N)).Exact ∧
    Epi (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
      N).map S.g) :=
  letI : HasFiniteBiproducts
      (SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
    HasFiniteBiproducts.of_hasFiniteProducts
  (Functor.preservesFiniteColimits_iff_forall_exact_map_and_epi
    (F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
      N)).1 inferInstance S hS

/-- **The key step of Stacks 03EX.** If `S` is a short exact sequence of sheaves of modules
whose third term is flat, and `E` is a short exact sequence whose middle term is flat, then
tensoring `S` with the third term of `E` keeps the first map a monomorphism.

Taking `E` to be the flat resolution `Stacks.fromFlatCover` of a sheaf of modules `G`, this
is exactly the injectivity half of Stacks 03EX. -/
lemma mono_sheafTensorRight_map_f
    (S E : ShortComplex (SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (hS : S.ShortExact) (hE : E.ShortExact)
    (hX₃ : SheafOfModules.IsFlat S.X₃) (hE₂ : SheafOfModules.IsFlat E.X₂) :
    Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
      E.X₃).map S.f) := by
  have hcol := exact_and_epi_sheafTensorRight O S hS
  have hrow : ∀ M : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O),
      (tensorRightComplex O M E).Exact ∧ Epi (tensorRightComplex O M E).g := fun M ↦
    (ShortComplex.exact_and_epi_g_iff_of_iso (tensorRightComplexIso O M E)).2
      (exact_and_epi_sheafTensorRight O E hE M)
  have hz₁ :
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj E.X₁).map
          S.f ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj E.X₁).map
          S.g = 0 :=
    (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
      E.X₁)).zero
  have hcol₂ :
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj E.X₂).map
          S.f ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj E.X₂).map
          S.g = 0 :=
    (S.map ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
      E.X₂)).zero
  have hz₂ :
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).obj S.X₂).map E.f ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).obj S.X₂).map
          E.g = 0 :=
    (tensorRightComplex O S.X₂ E).zero
  have hrow₁ :
      ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).obj S.X₁).map E.f ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).obj S.X₁).map
          E.g = 0 :=
    (tensorRightComplex O S.X₁ E).zero
  have : Epi (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).obj
      S.X₁).map E.g) := (hrow S.X₁).2
  have : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
      E.X₂).map S.f) := by
    exact ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
      (F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
        E.X₂)).1 hE₂.1 S hS).2
  have : Mono (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).obj
      S.X₃).map E.f) :=
    ((ShortComplex.exact_and_mono_f_iff_of_iso (tensorRightComplexIso O S.X₃ E)).2
      ((Functor.preservesFiniteLimits_iff_forall_exact_map_and_mono
        (F := (Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
          S.X₃)).1 hX₃.1 E hE)).2
  exact mono_of_threeByThree hz₁ (hcol E.X₁).1 hz₂ (hrow S.X₂).1 hrow₁ hcol₂
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).map S.f).naturality
      E.f)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).map S.f).naturality
      E.g)
    (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).map S.g).naturality
      E.f)

/-- **Stacks 03EW for sheaves of modules**, as a short exact sequence: every sheaf of modules
`G` is the third term of a short exact sequence whose middle term is flat. -/
noncomputable abbrev flatResolution
    (G : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    ShortComplex (SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :=
  ShortComplex.mk (kernel.ι (fromFlatCover O G)) (fromFlatCover O G) (kernel.condition _)

/-- The flat resolution of `G` is a short exact sequence. -/
lemma shortExact_flatResolution
    (G : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    (flatResolution O G).ShortExact :=
  ⟨ShortComplex.exact_kernel _⟩

/-- The middle term of the flat resolution of `G` is flat. -/
lemma isFlat_flatResolution_X₂
    (G : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)) :
    SheafOfModules.IsFlat (flatResolution O G).X₂ :=
  isFlat_flatCover O G

/-- **Stacks Project, Tag 03EX, sheaf case.** If the final term of a short exact sequence of
sheaves of modules is flat, then tensoring the sequence with any sheaf of modules gives a
short exact sequence of sheaves of modules. -/
@[stacks 03EX "sheaf_tensor_exactness", sga "1 IV 1.1" "(i)", sga "4 XVII 4.1.1" "(ii), f = id"]
theorem sheafTensorRight_shortExact_of_flat
    (S : ShortComplex (SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (G : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hS : S.ShortExact) (hflat : SheafOfModules.IsFlat S.X₃) :
    ∃ h : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
          G).map S.f ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
          G).map S.g = 0,
      (ShortComplex.mk
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
          G).map S.f)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
          G).map S.g) h).ShortExact := by
  have hcol := exact_and_epi_sheafTensorRight O S hS G
  have hmono : Mono
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
        (flatResolution O G).X₃).map S.f) :=
    mono_sheafTensorRight_map_f O S (flatResolution O G) hS (shortExact_flatResolution O G)
      hflat (isFlat_flatResolution_X₂ O G)
  exact ⟨(S.map ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
      G)).zero,
    { exact := hcol.1, mono_f := hmono, epi_g := hcol.2 }⟩

end TensorExactness

end Sheaf

/-! ### The sheafification hypotheses discharged by the universe inequality

The sheafification binders of the previous section are not an extra assumption on top of
`max u v ≤ max t w`: they follow from it. This section records that, so that `max t w` is
visibly a universe at which Stacks 03EX is available rather than one at which it might be
vacuous. -/

section SheafUnivLE

variable {J : GrothendieckTopology C} [UnivLE.{max u v, max t w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]

attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

/-- **Stacks Project, Tag 03EX, sheaf case, with the sheafification hypotheses discharged.**

The same statement as `Stacks.sheafTensorRight_shortExact_of_flat`, with its three
sheafification binders replaced by the single universe inequality `max u v ≤ max t w` that
produces them, through `CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat` and
`CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat`. At `t := max u v`
that inequality holds unconditionally, so the module universe `max u v w` is one at which
Stacks 03EX holds with no instance hypothesis beyond
`J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})`. -/
theorem sheafTensorRight_shortExact_of_flat_of_univLE (O : Sheaf J CommRingCat.{w})
    (S : ShortComplex (SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O)))
    (G : SheafOfModules.{max t w} (Stacks.SheafOfModules.Tensor.ringSheaf O))
    (hS : S.ShortExact) (hflat : SheafOfModules.IsFlat S.X₃) :
    ∃ h : ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
          G).map S.f ≫
        ((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
          G).map S.g = 0,
      (ShortComplex.mk
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
          G).map S.f)
        (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, v, w, max t w, max t w} O).flip.obj
          G).map S.g) h).ShortExact :=
  sheafTensorRight_shortExact_of_flat O S G hS hflat

end SheafUnivLE

end Stacks
