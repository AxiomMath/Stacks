module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeProperty

/-!
# Functoriality of the comparison map in the module (Stacks 06WC)

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids and let `φ : x ⟶ y` be an arrow
of `𝒳` lying over a morphism of schemes `a : U ⟶ V`. Stacks 06WC attaches to a presheaf of
modules `F` over the structure sheaf of Stacks 06TV the comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}`, built in
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtaleModuleComparison.lean` as the mate
of the direct-image comparison of Stacks 06W2.

This file records that `c_φ` is natural in `F`. On underlying presheaves this is
`AlgebraicGeometry.Stack.restrictionPushforwardComparison_naturality`, the corresponding
statement for Stacks 06W2; what is added here is that the squares commute as squares of
presheaves of modules, and that the square for the mate `c_φ` follows from the square for the
direct-image comparison by the two naturality identities of the pullback–direct image
adjunction.

The restriction of Stacks 06WJ is packaged as a functor so that the squares can be stated: the
definition `AlgebraicGeometry.Stack.restrictModuleToSmallEtale` is already the action on objects
of a composite of two functors, and
`AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFunctor` is that composite, agreeing with it
on objects by `rfl`.

One consequence is recorded: the flat base change property of Stacks 0762 only depends on the
isomorphism class of the module.

## Main definitions

* `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFunctor`: the restriction of Stacks 06WJ to
  the small étale site of the scheme below an object, as a functor on presheaves of modules.
* `AlgebraicGeometry.Stack.restrictModulePullbackComparisonNatTrans`: **Stacks 06WC**, the
  comparison map `c_φ` as a natural transformation of functors of the module.

## Main results

* `AlgebraicGeometry.Stack.restrictModulePushforwardComparison_naturality`: the direct-image
  comparison of Stacks 06WC is natural in the presheaf of modules.
* `AlgebraicGeometry.Stack.restrictModulePullbackComparison_naturality`: the comparison map
  `c_φ` of Stacks 06WC is natural in the presheaf of modules.
* `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_of_iso`: the flat base change property of
  Stacks 0762 transports along an isomorphism of presheaves of modules.

## Implementation notes

The module universe is fixed to `u`, the universe of the schemes, wherever the pullback
`a_{small}^*` appears; that restriction comes from the comparison map itself and is explained in
the implementation notes of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/SmallEtaleModuleComparison.lean`. The
direct-image comparison needs no such restriction, but it is stated here at the same universe
because it is only used to produce the statement about `c_φ`.

`hasFlatBaseChangeProperty_of_iso` is not an assertion of the source. It is the transport
statement that the closure properties of Stacks 0764 use silently, and it is the first thing a
proof of any of them needs; it carries no tag for that reason.

What is *not* here: Stacks 0764(4), that the modules with the flat base change property have
colimits agreeing with those of `Mod(𝒳_étale, 𝒪_𝒳)`. The natural transformation of this file is
the input to that argument — the source's proof is that `a_{small}^*` commutes with colimits,
being a left adjoint, and that restriction to the small étale site does too — but the colimits
of the source are colimits of étale *sheaves* of modules, so the argument also needs that
restriction to the small étale site commutes with étale sheafification. That step is not
available here and no part of Stacks 0764 is claimed.

## References

* [Stacks Project, Tag 06W2](https://stacks.math.columbia.edu/tag/06W2)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
* [Stacks Project, Tag 06WJ](https://stacks.math.columbia.edu/tag/06WJ)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u v w m

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- The restriction of **Stacks 06WJ** at an object `x` of `𝒳`, as a functor from the presheaves
of modules on `𝒳` to the presheaves of modules on the small étale site of the scheme below `x`:
restriction of the underlying abelian presheaf, then transport of the scalars along
`AlgebraicGeometry.Stack.localStructurePresheafIso`.

This is the functor whose action on objects is
`AlgebraicGeometry.Stack.restrictModuleToSmallEtale`; the tag is on that definition. -/
noncomputable def restrictModuleToSmallEtaleFunctor (x : 𝒳) :
    PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj ⥤
      PresheafOfModules.{m}
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj :=
  letI := isEquivalence_overPost B S hS p hp x
  PresheafOfModules.pushforward₀
      (smallEtaleInclusion B E h (p.obj x).left.1 (contains_base B E h S hS p x) ⋙
        (Over.post (X := x) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget x)
      (ringStructureSheafCore B S hS p hp τ hτ).obj ⋙
    PresheafOfModules.restrictScalars
      (localStructurePresheafIso B E h S hS p hp x τ hτ).hom

/-- The functor of `AlgebraicGeometry.Stack.restrictModuleToSmallEtaleFunctor` agrees on objects
with the restriction of Stacks 06WJ. -/
theorem restrictModuleToSmallEtaleFunctor_obj (x : 𝒳)
    (F : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj) :
    (restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ x).obj F =
      restrictModuleToSmallEtale B E h S hS p hp x τ hτ F :=
  rfl

section

variable {x y : 𝒳} (φ : x ⟶ y)

/-- **Stacks 06WC.** The direct-image comparison of a presheaf of modules below an arrow of `𝒳`
is natural in the module, at an arbitrary universe for the sections of the module.

On underlying abelian presheaves this is the naturality of Stacks 06W2, which holds for
presheaves with values in any category, and putting the module structure on the comparison does
not change it on sections. No universe inequality is needed: the direct image of presheaves of
modules is restriction of scalars followed by reindexing, and exists at every module universe. -/
@[stacks 06WC "functoriality of the direct-image comparison in the module"]
theorem restrictModulePushforwardComparison_naturality
    {F F' : PresheafOfModules.{m} (ringStructureSheafCore B S hS p hp τ hτ).obj} (α : F ⟶ F') :
    (restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ y).map α ≫
        restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F' =
      restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F ≫
        (PresheafOfModules.pushforward.{m}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).map
          ((restrictModuleToSmallEtaleFunctor.{u, v, w, m} B E h S hS p hp τ hτ x).map α) := by
  refine PresheafOfModules.hom_ext fun W => ?_
  induction W with | op W => ?_
  ext a
  have hnat := ConcreteCategory.congr_hom
    (restrictionPushforwardComparison_naturality B E h S hS p hp φ
      (F := F.presheaf) (G := F'.presheaf)
      ((PresheafOfModules.toPresheaf _).map α) W) a
  simp only at hnat ⊢
  exact hnat.symm

/-- **Stacks 06WC.** The comparison map `c_φ` is natural in the module.

The square for `c_φ` is the square for the direct-image comparison carried across the
pullback–direct image adjunction along `a_{small}^♯`, using that `c_φ` is by definition the mate
of that comparison: naturality of the adjunction isomorphism on the left turns the left-hand
composite into a mate, naturality on the right does the same for the right-hand composite, and
the two mates agree by
`AlgebraicGeometry.Stack.restrictModulePushforwardComparison_naturality`. -/
@[stacks 06WC "functoriality of the comparison map in the module"]
theorem restrictModulePullbackComparison_naturality
    {F F' : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj} (α : F ⟶ F') :
    (PresheafOfModules.pullback.{u}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).map
        ((restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ y).map α) ≫
          restrictModulePullbackComparison B E h S hS p hp φ τ hτ F' =
      restrictModulePullbackComparison B E h S hS p hp φ τ hτ F ≫
        (restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ x).map α := by
  have hleft := (PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv_naturality_left_symm
    ((restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ y).map α)
    (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F')
  have hright := (PresheafOfModules.pullbackPushforwardAdjunction.{u}
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).homEquiv_naturality_right_symm
    (restrictModulePushforwardComparison B E h S hS p hp φ τ hτ F)
    ((restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ x).map α)
  rw [restrictModulePushforwardComparison_naturality B E h S hS p hp τ hτ φ α] at hleft
  exact hleft.symm.trans hright

/-- **Stacks 06WC.** The comparison map `c_φ` below an arrow `φ : x ⟶ y` of `𝒳`, as a natural
transformation from the restriction at `y` followed by `a_{small}^*` to the restriction at
`x`. -/
@[stacks 06WC "the comparison map as a natural transformation"]
noncomputable def restrictModulePullbackComparisonNatTrans :
    restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ y ⋙
        PresheafOfModules.pullback.{u}
          (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
          (smallEtaleStructureComparison B E h S hS p hp φ τ hτ) ⟶
      restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ x where
  app F := restrictModulePullbackComparison B E h S hS p hp φ τ hτ F
  naturality _ _ α := restrictModulePullbackComparison_naturality B E h S hS p hp τ hτ φ α

end

/-- The comparison map of **Stacks 06WC** below a fixed arrow is an isomorphism for one presheaf
of modules as soon as it is for an isomorphic one.

The two comparison maps sit in the commuting square of
`AlgebraicGeometry.Stack.restrictModulePullbackComparison_naturality`, whose other two sides are
the images of the isomorphism under the restriction at the target followed by `a_{small}^*` and
under the restriction at the source; both are isomorphisms. -/
theorem isIso_restrictModulePullbackComparison_of_iso
    {F F' : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj} (e : F ≅ F')
    {x y : 𝒳} (ψ : x ⟶ y)
    (hF : IsIso (restrictModulePullbackComparison B E h S hS p hp ψ τ hτ F)) :
    IsIso (restrictModulePullbackComparison B E h S hS p hp ψ τ hτ F') := by
  have h1 : IsIso ((restrictModuleToSmallEtaleFunctor.{u, v, w, u}
      B E h S hS p hp τ hτ x).map e.hom) :=
    (restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ x).map_isIso e.hom
  have hnat := restrictModulePullbackComparison_naturality B E h S hS p hp τ hτ ψ e.hom
  have hcomp : IsIso ((PresheafOfModules.pullback.{u}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ))
      (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).map
        ((restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ y).map e.hom) ≫
      restrictModulePullbackComparison B E h S hS p hp ψ τ hτ F') := by
    rw [hnat]
    exact IsIso.comp_isIso' hF h1
  exact IsIso.of_isIso_comp_left (f := (PresheafOfModules.pullback.{u}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p ψ))
      (smallEtaleStructureComparison B E h S hS p hp ψ τ hτ)).map
        ((restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ y).map e.hom))
    (g := restrictModulePullbackComparison B E h S hS p hp ψ τ hτ F')

/-- The flat base change property of **Stacks 0762** transports along an isomorphism of
presheaves of modules: at each flat arrow this is
`AlgebraicGeometry.Stack.isIso_restrictModulePullbackComparison_of_iso`. -/
theorem hasFlatBaseChangeProperty_of_iso
    {F F' : PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj} (e : F ≅ F')
    (hF : HasFlatBaseChangeProperty B E h S hS p hp τ hτ F) :
    HasFlatBaseChangeProperty B E h S hS p hp τ hτ F' := fun ψ hflat =>
  isIso_restrictModulePullbackComparison_of_iso B E h S hS p hp τ hτ e ψ (hF ψ hflat)

end AlgebraicGeometry.Stack

end
