module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Pullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FreeYonedaUnivLE
import StacksCore.Tactic.StacksAttribute

/-!
# Pushforward of presheaves of modules has a left adjoint, at independent universes

Let `F : C ⥤ D` be a functor, let `R` and `S` be presheaves of rings on `D` and on `C`, and
let `φ : S ⟶ F.op ⋙ R` be a morphism of presheaves of rings. Mathlib defines the pullback
functor `PresheafOfModules.pullback φ` as a left adjoint of `PresheafOfModules.pushforward φ`
*when one exists*, the existence being carried by `(pushforward φ).IsRightAdjoint`, and
discharges that typeclass in `PresheafOfModules.pullbackObjIsDefined_eq_top` — but only for
`{C D : Type u}` with `[SmallCategory C]`, `[SmallCategory D]` and presheaves of rings in
`RingCat.{u}`, because the proof resolves a presheaf of modules into the free modules
`(free S).obj (yoneda.obj X)` on the representables, and `PresheafOfModules.free` has the
ring universe for its module universe while `yoneda.obj X` has the morphism universe for its
section universe.

This file discharges the same typeclass with the universes of the two sites, of their
morphisms, of the presheaves of rings and of the module sections **mutually independent**,
subject only to the smallness hypotheses the construction uses.

## Main results

* `PresheafOfModules.isColimitPresentationCokernelCofork`: every presheaf of modules is a
  cokernel of a morphism between coproducts of free presheaves of modules on representables,
  at independent universes.
* `PresheafOfModules.pullbackObjIsDefined_eq_top_of_univLE`: the partial left adjoint of
  `pushforward φ` is defined on every object.
* `PresheafOfModules.isRightAdjoint_pushforward_of_univLE`: hence `pushforward φ` is a right
  adjoint, so `PresheafOfModules.pullback φ` and
  `PresheafOfModules.pullbackPushforwardAdjunction φ` are available unconditionally.

## Implementation notes

The argument is Mathlib's, with its three universe-pinned ingredients replaced:

* the free presheaf of modules on a representable is
  `PresheafOfModules.freeObjShrink R (yoneda.obj U)` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/SeparatorUnivLE.lean`, whose sections are
  `Shrink.{v} ((Y.unop ⟶ U) →₀ R.obj Y)` rather than `(Y.unop ⟶ U) →₀ R.obj Y`, so that the
  module universe is prescribed instead of being the maximum of the morphism and ring
  universes;
* its corepresentation of sections, `PresheafOfModules.freeYonedaShrinkEquiv` of
  `StacksFrontier/Algebra/Category/ModuleCat/Sheaf/FreeYonedaUnivLE.lean`, replaces
  `PresheafOfModules.freeYonedaEquiv`;
* the index type of the presentation of `M` is the pairs `(U, x)` with `x` a section of `M`
  over `U`, **shrunk** into the module universe, where Mathlib uses `M.Elements` directly.
  Shrinking is what keeps the coproduct inside the colimits that `PresheafOfModules.{v} R`
  has: those are exactly the ones `AddCommGrpCat.{v}` has.

Nothing else in Mathlib's argument needs the two sites to be small. In particular
`PresheafOfModules.{v} R` is abelian and has `v`-small colimits for an arbitrary site and an
arbitrary presheaf of rings, and `CategoryTheory.Functor.leftAdjointObjIsDefined` is closed
under colimits at arbitrary universes.

The hypotheses are the smallness statements the construction uses — `Small.{v} C` for the
index type of the presentation, `LocallySmall.{v} C` and `LocallySmall.{v} D` for the
representables, and `Small.{v} (S.obj X)`, `Small.{v} (R.obj X)` for the coefficients — rather
than `UnivLE`, matching the convention of the two files above; `UnivLE.{u, v}`,
`UnivLE.{w, v}` and `UnivLE.{r, v}` supply them. Note that `Small.{v} D` is *not* needed: the
presentation is of an object of `PresheafOfModules.{v} S`, over `C`.

## References

* [Stacks Project, Tag 03D6](https://stacks.math.columbia.edu/tag/03D6)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
-/

@[expose] public noncomputable section

universe v w u w' u' r

open CategoryTheory CategoryTheory.Limits Opposite

namespace PresheafOfModules

section Presentation

variable {C : Type u} [Category.{w} C] (R : Cᵒᵖ ⥤ RingCat.{r})
  [∀ X, Small.{v} (R.obj X)] [LocallySmall.{v} C]

omit [∀ X, Small.{v} (R.obj X)] [LocallySmall.{v} C] in
/-- Two morphisms of presheaves of modules out of `M` agree as soon as they agree on every
section of `M` over every object of the site. Stated with the object taken in `C` rather than
in `Cᵒᵖ`, which is the form in which the generating sections of the presentation below come. -/
theorem hom_ext_sections {M N : PresheafOfModules.{v} R} {u u' : M ⟶ N}
    (h : ∀ (U : C) (x : M.obj (op U)), u.app (op U) x = u'.app (op U) x) : u = u' :=
  PresheafOfModules.hom_ext fun Y ↦ ModuleCat.hom_ext (LinearMap.ext fun x ↦ h Y.unop x)

/-- The tautological generating section of the free presheaf of modules on a representable
corepresents sections: reading it off the canonical morphism attached to `x` returns `x`. -/
theorem freeYonedaShrinkEquiv_fromFreeYonedaShrink {M : PresheafOfModules.{v} R} {U : C}
    (x : M.obj (op U)) :
    freeYonedaShrinkEquiv R (fromFreeYonedaShrink R x) = x :=
  (freeYonedaShrinkEquiv R).apply_symm_apply x

/-- A morphism out of the free presheaf of modules on the representable at `U` is determined
by the section it names, so a cancellation statement against the morphisms
`fromFreeYonedaShrink R x` is a statement about sections. -/
theorem app_eq_of_fromFreeYonedaShrink_comp_eq {M N : PresheafOfModules.{v} R} {u u' : M ⟶ N}
    {U : C} (x : M.obj (op U))
    (h : fromFreeYonedaShrink R x ≫ u = fromFreeYonedaShrink R x ≫ u') :
    u.app (op U) x = u'.app (op U) x := by
  have h₁ := congrArg (freeYonedaShrinkEquiv R) h
  rw [freeYonedaShrinkEquiv_comp, freeYonedaShrinkEquiv_comp,
    freeYonedaShrinkEquiv_fromFreeYonedaShrink] at h₁
  exact h₁

variable [Small.{v} C]

/-- The index type of the canonical presentation of a presheaf of modules: the pairs `(U, x)`
with `U` an object of the site and `x` a section of `M` over `U`. It lies in `max u v`, and is
`v`-small because the site is, which is what makes the coproduct it indexes exist in
`PresheafOfModules.{v} R`. -/
abbrev presentationIndex (M : PresheafOfModules.{v} R) : Type (max u v) :=
  Σ U : C, (M.obj (op U) : Type v)

/-- The family of free presheaves of modules on representables indexed by
`presentationIndex R M`: the index `(U, x)` contributes the free module on the representable
at `U`. -/
abbrev presentationFamily (M : PresheafOfModules.{v} R) :
    presentationIndex R M → PresheafOfModules.{v} R := fun i ↦
  (freeObjShrink R (yoneda.obj i.1) : PresheafOfModules.{v} R)

/-- The canonical morphism onto `M` from the coproduct of the free presheaves of modules on
the representables indexed by the sections of `M`: on the summand indexed by `(U, x)` it is
the morphism naming `x`. -/
def fromPresentation (M : PresheafOfModules.{v} R) : ∐ presentationFamily R M ⟶ M :=
  Sigma.desc fun i ↦ fromFreeYonedaShrink R i.2

@[reassoc]
lemma ι_fromPresentation (M : PresheafOfModules.{v} R) (U : C) (x : M.obj (op U)) :
    Sigma.ι (presentationFamily R M) (⟨U, x⟩ : presentationIndex R M) ≫
        fromPresentation R M =
      fromFreeYonedaShrink R x :=
  Sigma.ι_desc _ _

/-- **Every presheaf of modules is a quotient of a coproduct of free presheaves of modules on
representables**, with the universes of the site, of its morphisms, of the rings and of the
module sections independent: the summand indexed by a section hits that section. -/
instance epi_fromPresentation (M : PresheafOfModules.{v} R) :
    Epi (fromPresentation R M) where
  left_cancellation u u' h :=
    hom_ext_sections R fun U x ↦
      app_eq_of_fromFreeYonedaShrink_comp_eq R x (by
        rw [← ι_fromPresentation R M U x, Category.assoc, Category.assoc, h])

/-- The morphism between coproducts of free presheaves of modules on representables whose
cokernel is `M`: present the kernel of `fromPresentation R M` in the same way, and compose
with its inclusion. -/
def toPresentation (M : PresheafOfModules.{v} R) :
    ∐ presentationFamily R (kernel (fromPresentation R M)) ⟶ ∐ presentationFamily R M :=
  fromPresentation R (kernel (fromPresentation R M)) ≫ kernel.ι _

@[reassoc (attr := simp)]
lemma toPresentation_fromPresentation (M : PresheafOfModules.{v} R) :
    toPresentation R M ≫ fromPresentation R M = 0 :=
  (Category.assoc _ _ _).trans
    ((congrArg (fun α ↦ fromPresentation R (kernel (fromPresentation R M)) ≫ α)
      (kernel.condition (fromPresentation R M))).trans comp_zero)

/-- The cokernel cofork presenting `M` as a cokernel of `toPresentation R M`. -/
abbrev presentationCokernelCofork (M : PresheafOfModules.{v} R) :
    CokernelCofork (toPresentation R M) :=
  CokernelCofork.ofπ _ (toPresentation_fromPresentation R M)

/-- **Every presheaf of modules is a cokernel of a morphism between coproducts of free
presheaves of modules on representables**, with the universes of the site, of its morphisms,
of the rings and of the module sections independent. This is the colimit presentation that
Mathlib's `PresheafOfModules.isColimitFreeYonedaCoproductsCokernelCofork` provides for a small
site in a single universe. -/
def isColimitPresentationCokernelCofork (M : PresheafOfModules.{v} R) :
    IsColimit (presentationCokernelCofork R M) := by
  let S₀ := ShortComplex.mk _ _ (toPresentation_fromPresentation R M)
  let T₀ := ShortComplex.mk _ _ (kernel.condition (fromPresentation R M))
  let ψ : S₀ ⟶ T₀ :=
    { τ₁ := fromPresentation R (kernel (fromPresentation R M))
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

/-- The partial left adjoint of `pushforward φ` is defined on the free presheaf of modules on
the representable at `X`, and takes there the free presheaf of modules on the representable at
`F.obj X`. Both corepresentations of sections are the same evaluation, so the composite
bijection is natural in the target on the nose. -/
def pushforwardCompCoyonedaFreeYonedaShrinkCorepresentableBy (X : C) :
    (pushforward.{v} φ ⋙ coyoneda.obj
        (op (freeObjShrink S (yoneda.obj X) : PresheafOfModules.{v} S))).CorepresentableBy
      (freeObjShrink R (yoneda.obj (F.obj X)) : PresheafOfModules.{v} R) where
  homEquiv {M} := (freeYonedaShrinkEquiv R).trans
    (freeYonedaShrinkEquiv (M := (pushforward.{v} φ).obj M) S).symm
  homEquiv_comp {M N} g f := by
    refine (freeYonedaShrinkEquiv (M := (pushforward.{v} φ).obj N) S).injective ?_
    have h₁ : freeYonedaShrinkEquiv (M := (pushforward.{v} φ).obj N) S
          (((freeYonedaShrinkEquiv R).trans
            (freeYonedaShrinkEquiv (M := (pushforward.{v} φ).obj N) S).symm) (f ≫ g)) =
        freeYonedaShrinkEquiv R (f ≫ g) :=
      Equiv.apply_symm_apply _ _
    have h₂ : freeYonedaShrinkEquiv (M := (pushforward.{v} φ).obj M) S
          (((freeYonedaShrinkEquiv R).trans
            (freeYonedaShrinkEquiv (M := (pushforward.{v} φ).obj M) S).symm) f) =
        freeYonedaShrinkEquiv R f :=
      Equiv.apply_symm_apply _ _
    exact h₁.trans (congrArg (fun y ↦ g.app (op (F.obj X)) y) h₂.symm)

lemma pullbackObjIsDefined_freeObjShrink_yoneda (X : C) :
    pullbackObjIsDefined.{v} φ
      (freeObjShrink S (yoneda.obj X) : PresheafOfModules.{v} S) :=
  (pushforwardCompCoyonedaFreeYonedaShrinkCorepresentableBy.{v} φ X).isCorepresentable

variable [Small.{v} C]

/-- **The partial left adjoint of the pushforward of presheaves of modules is defined
everywhere**, with the universes of the two sites, of their morphisms, of the presheaves of
rings and of the module sections independent. This is
`PresheafOfModules.pullbackObjIsDefined_eq_top` off `SmallCategory`: every presheaf of modules
is a cokernel of a morphism between coproducts of free presheaves of modules on
representables, the partial left adjoint is defined on those, and the domain of definition is
closed under colimits. -/
theorem pullbackObjIsDefined_eq_top_of_univLE :
    pullbackObjIsDefined.{v} φ = ⊤ := by
  ext M
  simp only [Pi.top_apply, Prop.top_eq_true, iff_true]
  apply Functor.leftAdjointObjIsDefined_of_isColimit
    (isColimitPresentationCokernelCofork S M)
  rintro (_ | _)
  all_goals
    exact Functor.leftAdjointObjIsDefined_colimit _
      (fun _ ↦ pullbackObjIsDefined_freeObjShrink_yoneda.{v} φ _)

/-- **The pushforward of presheaves of modules is a right adjoint**, with the universes of the
two sites, of their morphisms, of the presheaves of rings and of the module sections
independent. Instance, so that `PresheafOfModules.pullback φ` and
`PresheafOfModules.pullbackPushforwardAdjunction φ` are available with no adjointness
hypothesis; this is what Mathlib supplies only for small sites in a single universe. -/
@[stacks 03D6 "part (2), presheaves of modules at independent universes"]
instance isRightAdjoint_pushforward_of_univLE :
    (pushforward.{v} φ).IsRightAdjoint :=
  Functor.isRightAdjoint_of_leftAdjointObjIsDefined_eq_top
    (pullbackObjIsDefined_eq_top_of_univLE.{v} φ)

end Pullback

end PresheafOfModules

end
