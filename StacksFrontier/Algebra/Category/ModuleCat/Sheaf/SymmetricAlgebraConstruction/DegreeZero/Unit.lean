module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification

/-!
# The sheafification of the free rank-one presheaf of modules

Let `α : R₀ ⟶ R.obj` be a locally bijective morphism from a presheaf of rings to the underlying
presheaf of a sheaf of rings, so that `R` is the sheafification of `R₀` and
`PresheafOfModules.sheafification α : PresheafOfModules R₀ ⥤ SheafOfModules R` is the associated
sheaf of modules functor. This file identifies the sheafification of the free rank-one presheaf of
`R₀`-modules with the free rank-one sheaf of `R`-modules:

`(PresheafOfModules.sheafification α).obj (PresheafOfModules.unit R₀) ≅ SheafOfModules.unit R`.

The isomorphism is produced from the two universal properties rather than from local bijectivity
of `α`. Both sides corepresent sections: `unit R₀` corepresents sections of a presheaf of
`R₀`-modules and `sheafification α` is a left adjoint, so a morphism out of the left-hand side is
a section of the restriction of scalars of the target; `unit R` on the right corepresents sections
directly. Restriction of scalars does not change the underlying groups, so the two descriptions
agree, and the two mutually inverse maps are the ones named by the constant section `1` on each
side. Each triangle identity then reduces, by injectivity of the two hom-equivalences, to a single
computation at `1`.

## Main definitions

* `PresheafOfModules.unitRestrictScalarsHom`: the morphism `unit R₀ ⟶ unit R.obj` given by `α`,
  with the target read as a presheaf of `R₀`-modules by restriction of scalars.
* `PresheafOfModules.sheafificationObjUnitHom` and `sheafificationObjUnitInv`: the two directions
  of the identification.
* `PresheafOfModules.sheafificationObjUnitIso`: **the sheafification of the free rank-one
  presheaf of modules is the free rank-one sheaf of modules.**

## Main results

* `PresheafOfModules.sheafificationObjUnitIso_hom_one`: the identification carries the image of
  `1` under the sheafification unit to `1`.
* `PresheafOfModules.sheafificationHomEquiv_app` and
  `PresheafOfModules.sheafifyUnit_naturality_apply`: the sheafification hom-equivalence and the
  naturality of the sheafification unit, read on a local section.

## Implementation notes

**The module universe is the ring universe.** `PresheafOfModules.unit R₀` has
`obj X = ModuleCat.of _ (R₀.obj X)`, so its module universe is the universe of the rings. Hence
everything here is stated at a single universe `t` for both, unlike the sheafification
machinery of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GradedAlgebraSheafification`, which carries an
independent module universe.

**Why local bijectivity of `α` is not used.** It appears only as the instance hypothesis that
makes `PresheafOfModules.sheafification α` exist. The identification itself is formal: it would
hold for any left adjoint to `SheafOfModules.forget R ⋙ restrictScalars α`.

## References

* [Stacks Project, Section 17.21](https://stacks.math.columbia.edu/tag/01CF)
-/

@[expose] public section

open CategoryTheory Opposite

universe v u t

namespace PresheafOfModules

section RestrictScalars

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)

/-- The unit section of the free rank-one sheaf of `R`-modules, read as a section of the
presheaf of `R₀`-modules obtained from it by restriction of scalars. Restriction of scalars
changes neither the sections nor the restriction maps, so this is the constant section `1`. -/
noncomputable def unitRestrictScalarsOne :
    ((restrictScalars α).obj ((SheafOfModules.forget R).obj (SheafOfModules.unit R))).sections :=
  sectionsMk (fun X => (1 : R.obj.obj X)) (fun {_ _} f => unit_map_one R.obj f)

/-- **The morphism `unit R₀ ⟶ unit R.obj` given by `α`**, with the target read as a presheaf of
`R₀`-modules by restriction of scalars: it is the morphism out of the free rank-one presheaf of
modules named by the unit section of the target. -/
noncomputable def unitRestrictScalarsHom :
    unit R₀ ⟶ (restrictScalars α).obj ((SheafOfModules.forget R).obj (SheafOfModules.unit R)) :=
  (unitHomEquiv _).symm (unitRestrictScalarsOne α)

/-- The morphism `PresheafOfModules.unitRestrictScalarsHom α` sends the section `1` of `R₀` over
`X` to the section `1` of `R.obj` over `X`. -/
@[simp]
theorem unitRestrictScalarsHom_one (X : Cᵒᵖ) :
    Hom.app (unitRestrictScalarsHom α) X (1 : R₀.obj X) = (1 : R.obj.obj X) :=
  congrArg (fun s => s.val X) ((unitHomEquiv _).apply_symm_apply (unitRestrictScalarsOne α))

end RestrictScalars

section Sheafification

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {R₀ : Cᵒᵖ ⥤ RingCat.{t}} {R : Sheaf J RingCat.{t}} (α : R₀ ⟶ R.obj)
  [Presheaf.IsLocallyInjective J α] [Presheaf.IsLocallySurjective J α]
  [J.WEqualsLocallyBijective AddCommGrpCat.{t}] [HasWeakSheafify J AddCommGrpCat.{t}]

/-- **The sheafification hom-equivalence, read on a local section.** The morphism of presheaves
of modules corresponding to `f` is the sheafification unit followed by `f`, because the
equivalence is the hom-equivalence of `PresheafOfModules.sheafificationAdjunction`. -/
theorem sheafificationHomEquiv_app {P : PresheafOfModules.{t} R₀} {F : SheafOfModules.{t} R}
    (f : (sheafification α).obj P ⟶ F) (X : Cᵒᵖ) (m : P.obj X) :
    Hom.app (sheafificationHomEquiv α f) X m = f.val.app X (Hom.app (sheafifyUnit α P) X m) := by
  rw [← sheafificationAdjunction_homEquiv_apply, Adjunction.homEquiv_unit]
  rfl

/-- **Naturality of the sheafification unit, read on a local section.** -/
theorem sheafifyUnit_naturality_apply {M N : PresheafOfModules.{t} R₀} (g : M ⟶ N) (X : Cᵒᵖ)
    (m : M.obj X) :
    Hom.app (sheafifyUnit α N) X (Hom.app g X m) =
      ((sheafification α).map g).val.app X (Hom.app (sheafifyUnit α M) X m) :=
  congrArg (fun h : M ⟶ sheafifyRestrict α N => Hom.app h X m)
    ((sheafificationAdjunction α).unit.naturality g)

/-- The forward direction of the identification: the morphism adjoint to
`PresheafOfModules.unitRestrictScalarsHom`. -/
noncomputable def sheafificationObjUnitHom :
    (sheafification α).obj (unit R₀) ⟶ SheafOfModules.unit R :=
  (sheafificationHomEquiv α).symm (unitRestrictScalarsHom α)

/-- The morphism `PresheafOfModules.sheafificationObjUnitHom α` sends the image of `1` under the
sheafification unit to `1`. -/
theorem sheafificationObjUnitHom_app_one (X : Cᵒᵖ) :
    (sheafificationObjUnitHom α).val.app X (Hom.app (sheafifyUnit α (unit R₀)) X
      (1 : R₀.obj X)) = (1 : R.obj.obj X) := by
  have h := sheafificationHomEquiv_app α (sheafificationObjUnitHom α) X (1 : R₀.obj X)
  rw [show sheafificationHomEquiv α (sheafificationObjUnitHom α) = unitRestrictScalarsHom α from
    (sheafificationHomEquiv α).apply_symm_apply _] at h
  exact h.symm.trans (unitRestrictScalarsHom_one α X)

/-- The image of the unit section of `R₀` under the sheafification unit is a section of the
sheafification of the free rank-one presheaf of modules: the restriction maps of `unit R₀`
preserve `1`. -/
noncomputable def sheafificationObjUnitOneSection :
    ((sheafification α).obj (unit R₀)).sections :=
  sectionsMk (fun X => Hom.app (sheafifyUnit α (unit R₀)) X (1 : R₀.obj X))
    (fun {X Y} f => (naturality_apply (sheafifyUnit α (unit R₀)) f (1 : R₀.obj X)).symm.trans
      (congrArg (fun z => Hom.app (sheafifyUnit α (unit R₀)) Y z) (unit_map_one R₀ f)))

/-- The backward direction of the identification: the morphism out of the free rank-one sheaf of
modules named by `PresheafOfModules.sheafificationObjUnitOneSection`. -/
noncomputable def sheafificationObjUnitInv :
    SheafOfModules.unit R ⟶ (sheafification α).obj (unit R₀) :=
  (SheafOfModules.unitHomEquiv _).symm (sheafificationObjUnitOneSection α)

/-- The morphism `PresheafOfModules.sheafificationObjUnitInv α` sends `1` to the image of `1` under
the sheafification unit. -/
theorem sheafificationObjUnitInv_app_one (X : Cᵒᵖ) :
    (sheafificationObjUnitInv α).val.app X (1 : R.obj.obj X) =
      Hom.app (sheafifyUnit α (unit R₀)) X (1 : R₀.obj X) :=
  congrArg (fun s => s.val X)
    ((SheafOfModules.unitHomEquiv _).apply_symm_apply (sheafificationObjUnitOneSection α))

/-- `PresheafOfModules.sheafificationObjUnitInv α` followed by
`PresheafOfModules.sheafificationObjUnitHom α` is the identity of `SheafOfModules.unit R`. -/
theorem sheafificationObjUnitInv_comp_hom :
    sheafificationObjUnitInv α ≫ sheafificationObjUnitHom α = 𝟙 (SheafOfModules.unit R) := by
  refine (SheafOfModules.unitHomEquiv (SheafOfModules.unit R)).injective
    (sections_ext _ _ fun X => ?_)
  have e₁ : (SheafOfModules.unitHomEquiv (SheafOfModules.unit R)
        (sheafificationObjUnitInv α ≫ sheafificationObjUnitHom α)).val X =
      (sheafificationObjUnitHom α).val.app X
        ((sheafificationObjUnitInv α).val.app X (1 : R.obj.obj X)) := rfl
  have e₂ : (SheafOfModules.unitHomEquiv (SheafOfModules.unit R)
      (𝟙 (SheafOfModules.unit R))).val X = (1 : R.obj.obj X) := rfl
  rw [e₁, e₂, sheafificationObjUnitInv_app_one α X, sheafificationObjUnitHom_app_one α X]

/-- `PresheafOfModules.sheafificationObjUnitHom α` followed by
`PresheafOfModules.sheafificationObjUnitInv α` is the identity of the sheafification of
`PresheafOfModules.unit R₀`. -/
theorem sheafificationObjUnitHom_comp_inv :
    sheafificationObjUnitHom α ≫ sheafificationObjUnitInv α =
      𝟙 ((sheafification α).obj (unit R₀)) := by
  refine (sheafificationHomEquiv α).injective
    ((unitHomEquiv _).injective (sections_ext _ _ fun X => ?_))
  have e₁ : (unitHomEquiv _ (sheafificationHomEquiv α
        (sheafificationObjUnitHom α ≫ sheafificationObjUnitInv α))).val X =
      (sheafificationObjUnitInv α).val.app X ((sheafificationObjUnitHom α).val.app X
        (Hom.app (sheafifyUnit α (unit R₀)) X (1 : R₀.obj X))) :=
    sheafificationHomEquiv_app α
      (sheafificationObjUnitHom α ≫ sheafificationObjUnitInv α) X (1 : R₀.obj X)
  have e₂ : (unitHomEquiv _ (sheafificationHomEquiv α
        (𝟙 ((sheafification α).obj (unit R₀))))).val X =
      Hom.app (sheafifyUnit α (unit R₀)) X (1 : R₀.obj X) :=
    sheafificationHomEquiv_app α (𝟙 ((sheafification α).obj (unit R₀))) X (1 : R₀.obj X)
  rw [e₁, e₂, sheafificationObjUnitHom_app_one α X, sheafificationObjUnitInv_app_one α X]

/-- **The sheafification of the free rank-one presheaf of modules is the free rank-one sheaf of
modules.** -/
noncomputable def sheafificationObjUnitIso :
    (sheafification α).obj (unit R₀) ≅ SheafOfModules.unit R where
  hom := sheafificationObjUnitHom α
  inv := sheafificationObjUnitInv α
  hom_inv_id := sheafificationObjUnitHom_comp_inv α
  inv_hom_id := sheafificationObjUnitInv_comp_hom α

/-- **The identification carries the sheafified unit section to `1`.** -/
theorem sheafificationObjUnitIso_hom_one (X : Cᵒᵖ) :
    (sheafificationObjUnitIso α).hom.val.app X
        (Hom.app (sheafifyUnit α (unit R₀)) X (1 : R₀.obj X)) = (1 : R.obj.obj X) :=
  sheafificationObjUnitHom_app_one α X

end Sheafification

end PresheafOfModules

end
