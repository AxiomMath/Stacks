module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsCorepresentable
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionLinear

/-!
# Global sections on a site with a terminal object

`Stacks.Cohomology.SiteModules.globalSectionsFunctor` sends a sheaf of `O`-modules on a site to
its module of *compatible families* of sections, over the ring `Γ(C, O)` of compatible families
of sections of the structure sheaf. When the site has a terminal object — equivalently, when
`Cᵒᵖ` has an initial object `X` — a compatible family is determined by, and may be prescribed
by, its single value at `X`. This file records that: evaluation at `X` is a ring isomorphism
`Γ(C, O) ≅ O(X)` and an isomorphism of modules `Γ(C, M) ≅ M(X)`, naturally in `M`.

That is what makes the global-sections functor of this development comparable with the
evaluation functor `SheafOfModules.evaluation O X` of Mathlib, which is the one used on a
scheme: on the site of opens of a space, `⊤` is terminal, and sections over `⊤` are the global
sections.

Both comparisons are stated after restriction of scalars along a ring map out of a base ring,
since that is the form in which they are consumed: an inverse system of sheaves of modules on a
scheme over `Spec A` has its global sections read as `A`-modules.

## Main definitions

* `Stacks.Cohomology.SiteModules.globalSectionRingEquivInitial` — `Γ(C, O) ≅ O(X)` as rings.
* `Stacks.Cohomology.SiteModules.globalSectionsLinearEquivInitial` — `Γ(C, M) ≅ M(X)` as modules
  over a base ring acting on both sides.
* `Stacks.Cohomology.SiteModules.globalSectionsFunctorIsoEvaluation` — the same, naturally in
  `M`: the global-sections functor and the evaluation functor at `X` agree as functors into
  modules over a base ring.

## Implementation notes

Everything here is at a single universe. `Stacks.Cohomology.SiteModules.globalSectionsFunctor`
lands in `ModuleCat.{max u w}` for modules in universe `w`, while
`SheafOfModules.evaluation` lands in `ModuleCat.{w}`, so the two are comparable only when
`u ≤ w`; and the left exactness of global sections available in `GlobalSectionsCorepresentable`
holds at module universe equal to the universe of the structure rings. Collapsing the site, the
structure rings, the modules and the base ring to one universe satisfies both at once, and that
is the situation on the site of opens of a scheme over an affine base, where every universe is
the universe of the scheme.

Evaluation at an initial object of `Cᵒᵖ` is injective because every component of a compatible
family is the restriction of the component at `X`, and surjective because prescribing those
restrictions defines a compatible family: the two composites `X ⟶ Y ⟶ Z` and `X ⟶ Z` agree by
initiality.

## References

* [Stacks Project, Tag 071H](https://stacks.math.columbia.edu/tag/071H)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks.Cohomology.SiteModules

variable {C : Type u} [Category.{u} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{u})

/-! ### Evaluation at an initial object -/

/-- At an initial object `X` of `Cᵒᵖ`, evaluation of a global scalar at `X` is a ring
isomorphism `Γ(C, O) ≅ O(X)`: a compatible family is the family of restrictions of its value at
`X`. -/
def globalSectionRingEquivInitial (X : Cᵒᵖ) (hX : IsInitial X) :
    ↥(GlobalSectionRing O) ≃+* O.obj.obj X :=
  RingEquiv.ofBijective (globalSectionEval O X) <| by
    constructor
    · intro s t hst
      refine Subtype.ext (funext fun Y => ?_)
      have hs := s.2 (hX.to Y)
      have ht := t.2 (hX.to Y)
      exact hs.symm.trans ((congrArg (O.obj.map (hX.to Y)).hom hst).trans ht)
    · intro a
      refine ⟨⟨fun Y => (O.obj.map (hX.to Y)).hom a, ?_⟩, ?_⟩
      · intro Y Z f
        change (O.obj.map f).hom ((O.obj.map (hX.to Y)).hom a) = _
        rw [← RingCat.comp_apply, ← O.obj.map_comp, hX.hom_ext (hX.to Y ≫ f) (hX.to Z)]
      · change (O.obj.map (hX.to X)).hom a = a
        rw [hX.hom_ext (hX.to X) (𝟙 X), O.obj.map_id]
        rfl

/-- The isomorphism `globalSectionRingEquivInitial` sends a compatible family to its section at
`X`. -/
@[simp]
theorem globalSectionRingEquivInitial_apply (X : Cᵒᵖ) (hX : IsInitial X)
    (a : ↥(GlobalSectionRing O)) :
    globalSectionRingEquivInitial O X hX a = a.val X := rfl

variable [∀ X : Cᵒᵖ, IsMulCommutative (O.obj.obj X)]

/-- Evaluation at an initial object `X` of `Cᵒᵖ` is a bijection from the compatible families of
sections of an `O`-module to its sections at `X`. -/
def globalSectionsEquivInitial (M : SheafOfModules.{u} O) (X : Cᵒᵖ) (hX : IsInitial X) :
    GlobalSections O M ≃ M.val.obj X := by
  refine Equiv.ofBijective (fun s => s.eval X) ?_
  constructor
  · intro s t hst
    refine Subtype.ext (funext fun Y => ?_)
    have hs := s.2 (hX.to Y)
    have ht := t.2 (hX.to Y)
    exact hs.symm.trans ((congrArg (M.val.map (hX.to Y)) hst).trans ht)
  · intro a
    refine ⟨⟨fun Y => M.val.map (hX.to Y) a, ?_⟩, ?_⟩
    · intro Y Z f
      change M.val.map f (M.val.map (hX.to Y) a) = _
      rw [← PresheafOfModules.map_comp_apply, hX.hom_ext (hX.to Y ≫ f) (hX.to Z)]
    · change M.val.map (hX.to X) a = a
      rw [hX.hom_ext (hX.to X) (𝟙 X)]
      simp only [PresheafOfModules.map_id]
      rfl

/-! ### The comparison with evaluation, over a base ring -/

variable {A : Type u} [CommRing A]

/-- Evaluation at an initial object `X` of `Cᵒᵖ`, as an isomorphism of `A`-modules, for a base
ring `A` acting on the compatible families through `ρ` and on the sections at `X` through the
composite of `ρ` with evaluation. -/
def globalSectionsLinearEquivInitial (M : SheafOfModules.{u} O) (X : Cᵒᵖ) (hX : IsInitial X)
    (ρ : A →+* ↥(GlobalSectionRing O)) (σ : A →+* O.obj.obj X)
    (hρσ : (globalSectionEval O X).comp ρ = σ) :
    letI := Module.compHom (GlobalSections O M) ρ
    letI := Module.compHom (M.val.obj X : Type _) σ
    GlobalSections O M ≃ₗ[A] (M.val.obj X : Type _) :=
  letI := Module.compHom (GlobalSections O M) ρ
  letI := Module.compHom (M.val.obj X : Type _) σ
  { globalSectionsEquivInitial O M X hX with
    map_add' := fun s t => rfl
    map_smul' := fun a s => by
      change (ρ a • s).eval X = σ a • s.eval X
      rw [globalSections_smul_apply, ← hρσ]
      rfl }

/-- Evaluation at an initial object `X` of `Cᵒᵖ`, naturally in the module: the global-sections
functor of this development, read over a base ring `A`, is the evaluation functor at `X` read
over `A`. -/
def globalSectionsFunctorIsoEvaluation (X : Cᵒᵖ) (hX : IsInitial X)
    (ρ : A →+* ↥(GlobalSectionRing O)) (σ : A →+* O.obj.obj X)
    (hρσ : (globalSectionEval O X).comp ρ = σ) :
    globalSectionsFunctor.{u, u, u, u} O ⋙ ModuleCat.restrictScalars ρ ≅
      SheafOfModules.evaluation O X ⋙ ModuleCat.restrictScalars σ :=
  NatIso.ofComponents
    (fun M => ((globalSectionsLinearEquivInitial O M X hX ρ σ hρσ).toModuleIso))
    (fun _ => rfl)

end Stacks.Cohomology.SiteModules

end
