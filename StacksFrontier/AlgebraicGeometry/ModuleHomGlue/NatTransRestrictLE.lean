module

public import StacksFrontier.AlgebraicGeometry.ModuleHomGlue.NatTransRestrict
public import StacksFrontier.AlgebraicGeometry.ModuleLimits.MapDescentTransport

/-!
# Restricting an isomorphism of the restricted functors to a smaller open

`StacksFrontier/AlgebraicGeometry/ModuleHomGlue/NatTransRestrict.lean` glues a family of
isomorphisms `Θ i : G ⋙ (- |_{U i}) ≅ H ⋙ (- |_{U i})` into a natural isomorphism `G ≅ H`,
provided any two of them induce the same map on the sections over every affine open contained in
both of their domains.  The agreement hypothesis is stated on *sections*, through
`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp`.

A local-to-global argument, however, proves the agreement by a *rigidity* statement, which
returns an equality of natural isomorphisms of functors into the modules on the smaller open —
not an equality of maps on sections.  This file bridges the two: it restricts `Θ i` along the
inclusion of the smaller open and identifies the result's action on sections with that of `Θ i`.

## The bridge

`Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso` is the comparison between restricting to
`V` and then to `W ≤ V` and restricting to `W` directly; it is Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictFunctorComp` reindexed along
`AlgebraicGeometry.Scheme.homOfLE_ι`.  Conjugating by it sends `Θ` to a natural isomorphism of
the functors restricted to `W`, and `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_eq`
identifies each of its components with the *sectionwise* restriction
`Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE`, whose action on sections is that of the
original component by construction.

`Stacks.AlgebraicGeometry.ModuleHomGlue.localApp` and
`Stacks.AlgebraicGeometry.ModuleLimits.imageSections` are literally the same map — both are the
action of a morphism of restrictions on the sections over an open presented as an image,
transported along that presentation — so the two developments meet with nothing to prove beyond
substituting the presentation away.

## Main definitions

* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.restrictIsoOfLE`: the restriction to a smaller
  open of an isomorphism of the restricted functors.

## Main results

* `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_eq_imageSections`: the two names for the
  action on sections agree.
* `Stacks.AlgebraicGeometry.ModuleHomGlue.localApp_restrictHomOfLE`: restricting to a smaller
  open does not change the action on sections over an open seen by both.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.restrictIsoOfLE_hom_app`: the components of
  `restrictIsoOfLE` are the sectionwise restrictions of the components.
* `Stacks.AlgebraicGeometry.ModuleNatTransGlue.ofRestrict_app_eq_of_restrictIsoOfLE`: **the
  agreement hypothesis of the glueing follows from an equality of the two restricted natural
  isomorphisms at the object in question.**  This is the form a rigidity statement can discharge.
-/

@[expose] public noncomputable section

open CategoryTheory TopologicalSpace Opposite
open AlgebraicGeometry

universe u v w

namespace Stacks.AlgebraicGeometry.ModuleHomGlue

open Stacks.AlgebraicGeometry.ModuleLimits

variable {X : Scheme.{u}} {M N : X.Modules}

/-- **`localApp` and `imageSections` are the same map.**  Both are the action of a morphism of the
restrictions on the sections over an open presented as an image, transported along that
presentation, so substituting the presentation away leaves nothing to prove. -/
public theorem localApp_eq_imageSections {W : X.Opens}
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U : X.Opens} {P : W.toScheme.Opens} (hP : W.ι ''ᵁ P = U) (m : Γ(M, U)) :
    localApp W.ι χ hP m = imageSections χ hP m := by
  subst hP
  rfl

/-- **Restricting a morphism of restrictions to a smaller open does not change its `localApp`.**
For `V ≤ W` and `χ : M|_W ⟶ N|_W`, the sectionwise restriction of `χ` to `V` acts on the sections
over an open seen by both as `χ` does. -/
public theorem localApp_restrictHomOfLE {V W : X.Opens} (e : V ≤ W)
    (χ : Scheme.Modules.restrict M W.ι ⟶ Scheme.Modules.restrict N W.ι)
    {U : X.Opens} {P : V.toScheme.Opens} {Q : W.toScheme.Opens}
    (hP : V.ι ''ᵁ P = U) (hQ : W.ι ''ᵁ Q = U) :
    localApp V.ι (restrictHomOfLE e χ) hP = localApp W.ι χ hQ := by
  ext m
  rw [localApp_eq_imageSections, localApp_eq_imageSections]
  exact imageSections_restrictHomOfLE e χ hP hQ m

end Stacks.AlgebraicGeometry.ModuleHomGlue

namespace Stacks.AlgebraicGeometry.ModuleNatTransGlue

open Stacks.AlgebraicGeometry.ModuleLimits

variable {Y : Scheme.{u}} {C : Type v} [Category.{w} C] {G H : C ⥤ Y.Modules}

/-- **The restriction to a smaller open of an isomorphism of the restricted functors.**  For
`W ≤ V` and `Θ : G ⋙ (- |_V) ≅ H ⋙ (- |_V)`, restricting along `AlgebraicGeometry.Scheme.homOfLE`
and collapsing the iterated restriction with
`Stacks.AlgebraicGeometry.ModuleLimits.restrictLEIso` gives `G ⋙ (- |_W) ≅ H ⋙ (- |_W)`. -/
public def restrictIsoOfLE {V W : Y.Opens} (e : W ≤ V)
    (Θ : G ⋙ Scheme.Modules.restrictFunctor V.ι ≅ H ⋙ Scheme.Modules.restrictFunctor V.ι) :
    G ⋙ Scheme.Modules.restrictFunctor W.ι ≅ H ⋙ Scheme.Modules.restrictFunctor W.ι :=
  Functor.isoWhiskerLeft G (restrictLEIso e).symm ≪≫
    (Functor.associator G (Scheme.Modules.restrictFunctor V.ι)
      (Scheme.Modules.restrictFunctor (Y.homOfLE e))).symm ≪≫
    Functor.isoWhiskerRight Θ (Scheme.Modules.restrictFunctor (Y.homOfLE e)) ≪≫
    Functor.associator H (Scheme.Modules.restrictFunctor V.ι)
      (Scheme.Modules.restrictFunctor (Y.homOfLE e)) ≪≫
    Functor.isoWhiskerLeft H (restrictLEIso e)

/-- The components of `restrictIsoOfLE` are the sectionwise restrictions of the components of
`Θ`.  This is `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_eq`. -/
public theorem restrictIsoOfLE_hom_app {V W : Y.Opens} (e : W ≤ V)
    (Θ : G ⋙ Scheme.Modules.restrictFunctor V.ι ≅ H ⋙ Scheme.Modules.restrictFunctor V.ι)
    (A : C) :
    (restrictIsoOfLE e Θ).hom.app A = restrictHomOfLE e (Θ.hom.app A) := by
  rw [restrictHomOfLE_eq]
  simp [restrictIsoOfLE]

/-- **The agreement hypothesis of the glueing, reduced to an equality over the smaller open.**
If the restrictions to `W` of two isomorphisms of the restricted functors have the same component
at `A`, then the two local natural transformations they define have the same map on the sections
over `W`.

This is the step that lets a rigidity statement — which compares natural transformations of
functors into the modules on `W` — discharge the hypothesis of
`Stacks.AlgebraicGeometry.ModuleNatTransGlue.exists_natIso_of_restrictIso`, which is an equality
of maps on sections. -/
public theorem ofRestrict_app_eq_of_restrictIsoOfLE {V₁ V₂ W : Y.Opens}
    (h₁ : W ≤ V₁) (h₂ : W ≤ V₂)
    (Θ₁ : G ⋙ Scheme.Modules.restrictFunctor V₁.ι ≅ H ⋙ Scheme.Modules.restrictFunctor V₁.ι)
    (Θ₂ : G ⋙ Scheme.Modules.restrictFunctor V₂.ι ≅ H ⋙ Scheme.Modules.restrictFunctor V₂.ι)
    (A : C)
    (h : (restrictIsoOfLE h₁ Θ₁).hom.app A = (restrictIsoOfLE h₂ Θ₂).hom.app A) :
    (LocalNatTrans.ofRestrict V₁ Θ₁.hom).app A W h₁ =
      (LocalNatTrans.ofRestrict V₂ Θ₂.hom).app A W h₂ := by
  have key : ∀ (V : Y.Opens) (hV : W ≤ V)
      (Θ : G ⋙ Scheme.Modules.restrictFunctor V.ι ≅ H ⋙ Scheme.Modules.restrictFunctor V.ι),
      ModuleHomGlue.localApp W.ι ((restrictIsoOfLE hV Θ).hom.app A) (image_top_ι W) =
        (LocalNatTrans.ofRestrict V Θ.hom).app A W hV := by
    intro V hV Θ
    rw [LocalNatTrans.ofRestrict_app, restrictIsoOfLE_hom_app]
    exact ModuleHomGlue.localApp_restrictHomOfLE hV (Θ.hom.app A) (image_top_ι W)
      (ModuleHomGlue.image_preimage_eq_self V.ι (hV.trans (image_top_ι V).ge))
  rw [← key V₁ h₁ Θ₁, ← key V₂ h₂ Θ₂, h]

end Stacks.AlgebraicGeometry.ModuleNatTransGlue

end
