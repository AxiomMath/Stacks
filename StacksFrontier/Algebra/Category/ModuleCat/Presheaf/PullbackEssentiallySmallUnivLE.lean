module

public import Mathlib.CategoryTheory.EssentiallySmall
public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.PullbackUnivLE

/-!
# Pushforward of presheaves of modules over an essentially small site, at independent universes

Let `F : C ⥤ D` be a functor, let `R` and `S` be presheaves of rings on `D` and on `C` and let
`φ : S ⟶ F.op ⋙ R` be a morphism of presheaves of rings. The typeclass
`(PresheafOfModules.pushforward φ).IsRightAdjoint`, which is what makes
`PresheafOfModules.pullback φ` a left adjoint, is discharged in
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/PullbackUnivLE.lean` for a source site that is
`v`-**small**, `v` the module universe, and in
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/PullbackEssentiallySmall.lean` for a source site
that is only `v`-**essentially** small, but there with the ring universe tied to `v`.

This file discharges it for an essentially small source site with the ring universe independent
of the module universe. The canonical presentation of a presheaf of modules by free presheaves
of modules on representables is indexed, not by all objects of the site, but by the objects of a
family meeting every isomorphism class; such a family is `v`-small for an essentially small site
even though the type of objects need not be.

## Main definitions

* `PresheafOfModules.fromFreePresentation`: the canonical morphism onto a presheaf of modules
  from the coproduct of the free presheaves of modules on the representables at the objects of a
  family, indexed by the sections over those objects.
* `PresheafOfModules.freePresentationCokernelCofork`: the cofork presenting a presheaf of modules
  as a cokernel of a morphism between two such coproducts.

## Main results

* `PresheafOfModules.hom_ext_sections_of_family`: two morphisms of presheaves of modules agree as
  soon as they agree on the sections over the objects of a family meeting every isomorphism
  class.
* `PresheafOfModules.isColimitFreePresentationCokernelCofork`: that cofork is a colimit.
* `PresheafOfModules.pullbackObjIsDefined_eq_top_of_family`: the partial left adjoint of
  `pushforward φ` is defined on every object once such a `v`-small family exists.
* `CategoryTheory.locallySmall_trans_univLE` and
  `CategoryTheory.essentiallySmall_trans_univLE`: local and essential smallness transport up a
  universe inequality, which is how a site that is essentially small in the universe of its
  structure sheaf is seen to be essentially small in a larger module universe.

## Implementation notes

The index type of the presentation is `Σ i, M.obj (op (ι i))` for `ι : I → C` with `I : Type v`,
so it lies in `Type v` on the nose and the coproduct it indexes exists in
`PresheafOfModules.{v} R`. The hypothesis on `ι` is that every object of the site is isomorphic
to some `ι i`; sections transport along such an isomorphism, which is why the restricted index
set still presents every presheaf of modules.

Everything else is the argument of
`StacksFrontier/Algebra/Category/ModuleCat/Presheaf/PullbackUnivLE.lean`, whose ingredients
`PresheafOfModules.freeObjShrink`, `PresheafOfModules.fromFreeYonedaShrink` and
`PresheafOfModules.freeYonedaShrinkEquiv` already have the ring and module universes
independent, and whose `PresheafOfModules.pullbackObjIsDefined_freeObjShrink_yoneda` asks only
local smallness of the two sites.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

universe v w u w' u' r v'

open CategoryTheory CategoryTheory.Limits Opposite

/-- **Local smallness transports up a universe inequality**: a hom type that is `v`-small is
`v'`-small as soon as `v ≤ v'`. -/
theorem CategoryTheory.locallySmall_trans_univLE {C : Type u} [Category.{w} C]
    (h : LocallySmall.{v} C) [UnivLE.{v, v'}] : LocallySmall.{v'} C :=
  have := h
  { hom_small := fun X Y ↦ Small.trans_univLE.{v, v'} (X ⟶ Y) }

/-- **Essential smallness transports up a universe inequality**: by
`CategoryTheory.essentiallySmall_iff` it is smallness of the skeleton together with local
smallness, and both transport. -/
theorem CategoryTheory.essentiallySmall_trans_univLE {C : Type u} [Category.{w} C]
    (h : EssentiallySmall.{v} C) [UnivLE.{v, v'}] : EssentiallySmall.{v'} C :=
  have := h
  (essentiallySmall_iff C).2
    ⟨Small.trans_univLE.{v, v'} (Skeleton C), locallySmall_trans_univLE inferInstance⟩

namespace PresheafOfModules

section Presentation

variable {C : Type u} [Category.{w} C] (R : Cᵒᵖ ⥤ RingCat.{r})
  [∀ X, Small.{v} (R.obj X)] [LocallySmall.{v} C]

omit [∀ X, Small.{v} (R.obj X)] [LocallySmall.{v} C] in
/-- Restricting a section along an isomorphism of the site and back along its inverse recovers
it. Stated through `PresheafOfModules.restrictₛₗ`, whose target type is the module of sections
itself rather than a restriction of scalars of it. -/
lemma restrictₛₗ_inv_op_restrictₛₗ_hom_op {M : PresheafOfModules.{v} R} {U X : C} (e : U ≅ X)
    (x : M.obj (op X)) :
    M.restrictₛₗ e.inv.op (M.restrictₛₗ e.hom.op x) = x := by
  have h : (e.hom.op ≫ e.inv.op : op X ⟶ op X) = 𝟙 (op X) := by
    rw [← op_comp, e.inv_hom_id, op_id]
  have h₁ : M.map (e.hom.op ≫ e.inv.op) x = M.map e.inv.op (M.map e.hom.op x) :=
    M.map_comp_apply _ _ x
  have h₂ : M.map (𝟙 (op X)) x = x := by rw [M.map_id]; rfl
  exact h₁.symm.trans ((M.congr_map_apply h x).trans h₂)

variable {I : Type v} (ι : I → C)

/-- The index type of the presentation of a presheaf of modules attached to a family `ι` of
objects of the site: the pairs `(i, x)` with `x` a section over `ι i`. It lies in `Type v`
because `I` does, which is what makes the coproduct it indexes exist in
`PresheafOfModules.{v} R` without the site itself being `v`-small. -/
abbrev freePresentationIndex (M : PresheafOfModules.{v} R) : Type v :=
  Σ i : I, (M.obj (op (ι i)) : Type v)

/-- The family of free presheaves of modules on representables indexed by
`freePresentationIndex R ι M`: the index `(i, x)` contributes the free module on the
representable at `ι i`. -/
abbrev freePresentationDiagram (M : PresheafOfModules.{v} R) :
    freePresentationIndex R ι M → PresheafOfModules.{v} R := fun j ↦
  (freeObjShrink R (yoneda.obj (ι j.1)) : PresheafOfModules.{v} R)

/-- The canonical morphism onto `M` from the coproduct of the free presheaves of modules on the
representables at the objects of `ι`, indexed by the sections of `M` over them: on the summand
indexed by `(i, x)` it is the morphism naming `x`. -/
def fromFreePresentation (M : PresheafOfModules.{v} R) :
    ∐ freePresentationDiagram R ι M ⟶ M :=
  Sigma.desc fun j ↦ fromFreeYonedaShrink R j.2

/-- On the summand indexed by `(i, x)`, `fromFreePresentation R ι M` is the morphism naming the
section `x`. -/
@[reassoc]
lemma ι_fromFreePresentation (M : PresheafOfModules.{v} R) (i : I) (x : M.obj (op (ι i))) :
    Sigma.ι (freePresentationDiagram R ι M) (⟨i, x⟩ : freePresentationIndex R ι M) ≫
        fromFreePresentation R ι M =
      fromFreeYonedaShrink R x :=
  Sigma.ι_desc _ _

omit [∀ X, Small.{v} (R.obj X)] [LocallySmall.{v} C] in
/-- Two morphisms of presheaves of modules out of `M` agree as soon as they agree on the
sections of `M` over the objects of a family meeting every isomorphism class of the site: an
arbitrary section is the restriction, along such an isomorphism, of a section over a member of
the family. -/
theorem hom_ext_sections_of_family (hι : ∀ X : C, ∃ i, Nonempty (ι i ≅ X))
    {M N : PresheafOfModules.{v} R} {u u' : M ⟶ N}
    (h : ∀ (i : I) (x : M.obj (op (ι i))), u.app (op (ι i)) x = u'.app (op (ι i)) x) :
    u = u' := by
  refine hom_ext_sections R fun X x ↦ ?_
  obtain ⟨i, ⟨e⟩⟩ := hι X
  have key : ∀ w : M ⟶ N, w.app (op X) x =
      N.restrictₛₗ e.inv.op (w.app (op (ι i)) (M.restrictₛₗ e.hom.op x)) := fun w ↦
    (congrArg (fun z ↦ w.app (op X) z) (restrictₛₗ_inv_op_restrictₛₗ_hom_op R e x)).symm.trans
      (naturality_apply w e.inv.op (M.restrictₛₗ e.hom.op x))
  exact (key u).trans
    ((congrArg (fun z ↦ N.restrictₛₗ e.inv.op z) (h i (M.restrictₛₗ e.hom.op x))).trans
      (key u').symm)

/-- **Every presheaf of modules is a quotient of a coproduct of free presheaves of modules on
representables**, the representables being taken at the objects of a `v`-small family meeting
every isomorphism class of the site: the summand indexed by a section hits that section. -/
theorem epi_fromFreePresentation (hι : ∀ X : C, ∃ i, Nonempty (ι i ≅ X))
    (M : PresheafOfModules.{v} R) :
    Epi (fromFreePresentation R ι M) where
  left_cancellation u u' h :=
    hom_ext_sections_of_family R ι hι fun i x ↦
      app_eq_of_fromFreeYonedaShrink_comp_eq R x (by
        rw [← ι_fromFreePresentation R ι M i x, Category.assoc, Category.assoc, h])

/-- The morphism between coproducts of free presheaves of modules on representables whose
cokernel is `M`: present the kernel of `fromFreePresentation R ι M` in the same way, and compose
with its inclusion. -/
def toFreePresentation (M : PresheafOfModules.{v} R) :
    ∐ freePresentationDiagram R ι (kernel (fromFreePresentation R ι M)) ⟶
      ∐ freePresentationDiagram R ι M :=
  fromFreePresentation R ι (kernel (fromFreePresentation R ι M)) ≫ kernel.ι _

/-- The composite of `toFreePresentation R ι M` with `fromFreePresentation R ι M` is zero. -/
@[reassoc (attr := simp)]
lemma toFreePresentation_fromFreePresentation (M : PresheafOfModules.{v} R) :
    toFreePresentation R ι M ≫ fromFreePresentation R ι M = 0 :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun α ↦ fromFreePresentation R ι (kernel (fromFreePresentation R ι M)) ≫ α)
      (kernel.condition (fromFreePresentation R ι M))).trans comp_zero)

/-- The cokernel cofork presenting `M` as a cokernel of `toFreePresentation R ι M`. -/
abbrev freePresentationCokernelCofork (M : PresheafOfModules.{v} R) :
    CokernelCofork (toFreePresentation R ι M) :=
  CokernelCofork.ofπ _ (toFreePresentation_fromFreePresentation R ι M)

/-- **Every presheaf of modules is a cokernel of a morphism between coproducts of free presheaves
of modules on representables**, the representables being taken at the objects of a `v`-small
family meeting every isomorphism class of the site, and the universes of the site, of its
morphisms, of the rings and of the module sections independent. -/
def isColimitFreePresentationCokernelCofork (hι : ∀ X : C, ∃ i, Nonempty (ι i ≅ X))
    (M : PresheafOfModules.{v} R) :
    IsColimit (freePresentationCokernelCofork R ι M) := by
  have : Epi (fromFreePresentation R ι M) := epi_fromFreePresentation R ι hι M
  have : Epi (fromFreePresentation R ι (kernel (fromFreePresentation R ι M))) :=
    epi_fromFreePresentation R ι hι _
  let S₀ := ShortComplex.mk _ _ (toFreePresentation_fromFreePresentation R ι M)
  let T₀ := ShortComplex.mk _ _ (kernel.condition (fromFreePresentation R ι M))
  let ψ : S₀ ⟶ T₀ :=
    { τ₁ := fromFreePresentation R ι (kernel (fromFreePresentation R ι M))
      τ₂ := 𝟙 _
      τ₃ := 𝟙 _ }
  exact ((ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).2
    (T₀.exact_of_f_is_kernel (kernelIsKernel _))).gIsCokernel

end Presentation

section Pullback

variable {C : Type u} [Category.{w} C] {D : Type u'} [Category.{w'} D] {F : C ⥤ D}
  {R : Dᵒᵖ ⥤ RingCat.{r}} {S : Cᵒᵖ ⥤ RingCat.{r}} (φ : S ⟶ F.op ⋙ R)
  [∀ X, Small.{v} (R.obj X)] [∀ X, Small.{v} (S.obj X)]
  [LocallySmall.{v} C] [LocallySmall.{v} D]

/-- **The partial left adjoint of the pushforward of presheaves of modules is defined
everywhere** as soon as the source site has a `v`-small family of objects meeting every
isomorphism class, with the universes of the two sites, of their morphisms, of the presheaves of
rings and of the module sections independent. This is
`PresheafOfModules.pullbackObjIsDefined_eq_top_of_univLE` with `Small.{v} C` weakened to
essential smallness in the form in which it is used. -/
theorem pullbackObjIsDefined_eq_top_of_family {I : Type v} (ι : I → C)
    (hι : ∀ X : C, ∃ i, Nonempty (ι i ≅ X)) :
    pullbackObjIsDefined.{v} φ = ⊤ := by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  refine Functor.leftAdjointObjIsDefined_of_isColimit
    (isColimitFreePresentationCokernelCofork S ι hι M) ?_
  have (J : Type v) : HasColimitsOfShape (Discrete J) (PresheafOfModules.{v} R) :=
    have : HasColimitsOfShape (Discrete J) AddCommGrpCat.{v} := AddCommGrpCat.hasColimitsOfShape
    PresheafOfModules.hasColimitsOfShape R (Discrete J)
  rintro (_ | _) <;>
    exact Functor.leftAdjointObjIsDefined_colimit _
      (fun _ ↦ pullbackObjIsDefined_freeObjShrink_yoneda.{v} φ _)

end Pullback

end PresheafOfModules

end
