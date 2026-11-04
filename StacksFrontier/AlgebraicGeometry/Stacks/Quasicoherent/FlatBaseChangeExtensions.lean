module

public import Mathlib.Algebra.Homology.ShortComplex.Abelian
public import Mathlib.CategoryTheory.Abelian.DiagramLemmas.Four
public import StacksFrontier.AlgebraicGeometry.RestrictionExact.OverExact
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatBaseChangeColimits

/-!
# Extensions of modules with the flat base change property (Stacks 0764, part (2))

Let `p : 𝒳 ⥤ (Sch/S)_{fppf}` be a category fibred in groupoids. **Stacks 0762** attaches to a
presheaf of `𝒪_𝒳`-modules the *flat base change property*: the comparison map
`c_φ : a_{small}^*(F|_{V_ét}) ⟶ F|_{U_ét}` of **Stacks 0761** is an isomorphism for every arrow
`φ : x ⟶ y` of `𝒳` lying over a flat morphism of schemes `a : U ⟶ V`. Part (2) of
**Stacks 0764** says that the modules with the property form a weak Serre subcategory, which by
**Stacks 0754** asks for a zero object, strict fullness, closure under kernels and cokernels and
closure under extensions. This file proves the **extension** clause, at the level of presheaves
of modules; `StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeColimits.lean` has
the zero object, the strict fullness and the cokernels there.

The source's argument for the extension clause is the 5 lemma against exactness of
`a_{small}^*` and of the restriction functors. Only *right* exactness of
`F ↦ a_{small}^*(F|_{V_ét})` is used here, and that is formal: restriction to a small étale site
is exact, being restriction along a functor followed by a change of scalars, and `a_{small}^*` is
a left adjoint. With `c_φ` an isomorphism at the outer terms of the short exact sequence, its
component at `F₁ ⟶ F₂` is a monomorphism because its composite with the isomorphism at `F₂` is
the isomorphism at `F₁` followed by a monomorphism; so both rows are short exact and the short
five lemma gives the middle component. That is
`CategoryTheory.ShortComplex.isIso_app_of_shortExact`, stated here for an arbitrary pair of
additive functors of abelian categories with the source right exact and the target exact.

## Main definitions

* `AlgebraicGeometry.Stack.smallEtaleRestrictionSiteFunctor`: the functor of sites underlying the
  restriction of **Stacks 06W1** at an object of `𝒳`.
* `AlgebraicGeometry.Stack.restrictModulePushforwardSpelling`: that restriction on presheaves of
  modules, spelled as `PresheafOfModules.pushforward` along it.
* `AlgebraicGeometry.Stack.flatBaseChangeComparisonSource`: the source
  `F ↦ a_{small}^*(F|_{V_ét})` of the comparison map of **Stacks 06WC** below an arrow, as a
  functor of the module.

## Main results

* `CategoryTheory.ShortComplex.isIso_app_of_shortExact`: the short five lemma for a natural
  transformation from a right exact functor to an exact functor.
* `AlgebraicGeometry.Stack.preservesFiniteLimits_restrictModuleToSmallEtaleFunctor'` and
  `AlgebraicGeometry.Stack.preservesFiniteColimits_restrictModuleToSmallEtaleFunctor'`:
  restriction to a small étale site is exact on presheaves of modules.
* `AlgebraicGeometry.Stack.hasFlatBaseChangeProperty_X₂_of_shortExact`: **the extension clause of
  Stacks 0764 part (2)**, for presheaves of modules.

## Implementation notes

No `@[stacks 0764]` attribute is carried. Part (2) of that tag asserts the weak Serre property,
which asks for four closure conditions, and this is one of them; the declarations in
`FlatBaseChangeColimits.lean` that carry a part-(2) key do so for the ambient category of
presheaves of modules, and the same reading applies here.

The kernel clause is the one condition of **Stacks 0754** for the flat base change property that
is neither here nor in `FlatBaseChangeColimits.lean`. It is the only condition whose proof in the
source consumes *left* exactness of `a_{small}^*`, and `a_{small}^*` is here the left adjoint
`PresheafOfModules.pullback` of the direct image of presheaves of modules along base change, so
its left exactness is not a formal consequence of anything above. Left exactness of that
presheaf-level pullback asks for the sections `𝒪_U(W')` to be flat over the sections at `W'` of
the presheaf-level inverse image of `𝒪_V`, objectwise on the small étale site; flatness of `a`
gives that at the stalks, not objectwise.

The comparison map the source reads **Stacks 0762** with is the one on *sheaves* of modules, in
which `a_{small}^*` is the pullback along the morphism of ringed sites `ε_a` of
**Stacks 070R (2)** — that is, the sheafification of the pullback above. That reading, with all
four conditions of Stacks 0754 for the locally quasi-coherent modules, is
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeSheafProperty.lean`; its kernel
clause runs on left exactness of `ε_a^*` on quasi-coherent modules, which is
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/FlatBaseChangeSheafKernels.lean`.

Exactness of the restriction functor is read off
`Stacks.AlgebraicGeometry.RestrictionExact.preservesFiniteLimits_presheafPushforward` and the
`AlgebraicGeometry.Stack.preservesColimitsOfShape_restrictModuleToSmallEtaleFunctor`.
Applying the former needs the two coefficient presheaves of rings and the functor of sites all
three supplied explicitly: `AlgebraicGeometry.Stack.ringStructureSheafCore` is built by a tactic
block, so leaving any of them to unification makes `whnf` unfold a tactic-generated term and
costs several times the default heartbeat budget.

## References

* [Stacks Project, Tag 0754](https://stacks.math.columbia.edu/tag/0754)
* [Stacks Project, Tag 0761](https://stacks.math.columbia.edu/tag/0761)
* [Stacks Project, Tag 0762](https://stacks.math.columbia.edu/tag/0762)
* [Stacks Project, Tag 0764](https://stacks.math.columbia.edu/tag/0764)
* [Stacks Project, Tag 06W1](https://stacks.math.columbia.edu/tag/06W1)
* [Stacks Project, Tag 06WC](https://stacks.math.columbia.edu/tag/06WC)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v w

namespace CategoryTheory.ShortComplex

universe uA vA uA' vA'

variable {A : Type uA} [Category.{vA} A] [Abelian A] {A' : Type uA'} [Category.{vA'} A']
  [Abelian A']

/-- **Short five lemma against a right exact functor.**  Let `η : Φ ⟶ Ψ` be a natural
transformation of additive functors of abelian categories with `Φ` right exact and `Ψ` exact.
If `η` is an isomorphism at the outer terms of a short exact sequence `T`, it is an isomorphism
at the middle term. -/
theorem isIso_app_of_shortExact (Φ Ψ : A ⥤ A') [Φ.Additive] [Ψ.Additive]
    [Limits.PreservesFiniteColimits Φ] [Limits.PreservesFiniteLimits Ψ]
    [Limits.PreservesFiniteColimits Ψ] (η : Φ ⟶ Ψ) {T : ShortComplex A} (hT : T.ShortExact)
    (h₁ : IsIso (η.app T.X₁)) (h₃ : IsIso (η.app T.X₃)) :
    IsIso (η.app T.X₂) := by
  have := hT.mono_f
  have := hT.epi_g
  have := h₁
  have := h₃
  have hcok : Limits.IsColimit
      (Limits.CokernelCofork.ofπ (Φ.map T.g) (by rw [← Φ.map_comp, T.zero, Φ.map_zero])) :=
    Limits.IsColimit.ofIsoColimit
      (Limits.CokernelCofork.mapIsColimit _ hT.gIsCokernel Φ) (Limits.Cofork.ext (Iso.refl _))
  have hmono : Mono (Φ.map T.f) := by
    have hnat := η.naturality T.f
    have : Mono (Φ.map T.f ≫ η.app T.X₂) := by
      rw [hnat]; infer_instance
    exact mono_of_mono _ (η.app T.X₂)
  have hΦ : (T.map Φ).ShortExact :=
    { exact := (T.map Φ).exact_of_g_is_cokernel hcok
      mono_f := hmono
      epi_g := Limits.epi_of_isColimit_cofork hcok }
  have hΨ : (T.map Ψ).ShortExact := hT.map Ψ
  exact isIso₂_of_shortExact_of_isIso₁₃' (mapNatTrans T η) hΦ hΨ h₁ h₃

end CategoryTheory.ShortComplex

namespace AlgebraicGeometry.Stack

variable (B : BigFppfSite.{u}) (E : BigEtaleSite.{u}) (h : E.cutoff = B.cutoff)
  (S : Scheme.{u}) (hS : B.Contains S)
  {𝒳 : Type v} [Category.{w} 𝒳] (p : 𝒳 ⥤ BigFppfOver B S hS) (hp : p.IsFiberedInGroupoids)
  (τ : GrothendieckTopology B.Schemes) (hτ : τ ≤ B.topology)

/-- The functor of sites underlying the restriction of **Stacks 06W1** at an object `z` of `𝒳`:
the small étale inclusion of **Stacks 06W1**, the inverse of the localization equivalence of
**Stacks 06W0**, and the forgetful functor of the slice at `z`. -/
noncomputable def smallEtaleRestrictionSiteFunctor (z : 𝒳) :
    SmallEtale E (p.obj z).left.1 (contains_base B E h S hS p z) ⥤ 𝒳 :=
  letI := isEquivalence_overPost B S hS p hp z
  smallEtaleInclusion B E h (p.obj z).left.1 (contains_base B E h S hS p z) ⋙
    (Over.post (X := z) (p ⋙ Over.forget (B.obj hS))).inv ⋙ Over.forget z

section

variable {x y : 𝒳} (φ : x ⟶ y)

/-- The restriction of **Stacks 06WJ** at an object, spelled as the direct image of presheaves of
modules along the morphism of ringed sites below the restriction functor. -/
noncomputable def restrictModulePushforwardSpelling (z : 𝒳) :
    PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj ⥤
      PresheafOfModules.{u}
        (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj :=
  PresheafOfModules.pushforward.{u} (F := smallEtaleRestrictionSiteFunctor B E h S hS p hp z)
    (localStructurePresheafIso B E h S hS p hp z τ hτ).hom

/-- The two spellings of the restriction agree. -/
theorem restrictModulePushforwardSpelling_eq (z : 𝒳) :
    restrictModulePushforwardSpelling B E h S hS p hp τ hτ z =
      restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ z :=
  rfl

/-- Restriction of presheaves of modules to the small étale site at `z` is additive. -/
noncomputable instance additive_restrictModuleToSmallEtaleFunctor' (z : 𝒳) :
    (restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ z).Additive :=
  restrictModulePushforwardSpelling_eq B E h S hS p hp τ hτ z ▸
    Stacks.AlgebraicGeometry.RestrictionExact.additive_presheafPushforward.{u}
      (F := smallEtaleRestrictionSiteFunctor B E h S hS p hp z)
      (R := (ringStructureSheafCore B S hS p hp τ hτ).obj)
      (S := (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj)
      (localStructurePresheafIso B E h S hS p hp z τ hτ).hom

/-- Restriction of presheaves of modules to the small étale site at `z` preserves finite limits. -/
noncomputable instance preservesFiniteLimits_restrictModuleToSmallEtaleFunctor' (z : 𝒳) :
    PreservesFiniteLimits
      (restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ z) :=
  cast (congrArg (fun G => PreservesFiniteLimits G)
      (restrictModulePushforwardSpelling_eq B E h S hS p hp τ hτ z))
    (Stacks.AlgebraicGeometry.RestrictionExact.preservesFiniteLimits_presheafPushforward.{u}
      (F := smallEtaleRestrictionSiteFunctor B E h S hS p hp z)
      (R := (ringStructureSheafCore B S hS p hp τ hτ).obj)
      (S := (SmallEtale.structureSheaf E (p.obj z).left.1 (contains_base B E h S hS p z)).obj)
      (localStructurePresheafIso B E h S hS p hp z τ hτ).hom)

/-- Restriction of presheaves of modules to the small étale site at `z` preserves finite
colimits. -/
noncomputable instance preservesFiniteColimits_restrictModuleToSmallEtaleFunctor' (z : 𝒳) :
    PreservesFiniteColimits
      (restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ z) :=
  ⟨fun _ _ _ =>
    preservesColimitsOfShape_restrictModuleToSmallEtaleFunctor B E h S hS p hp τ hτ z⟩

/-- The pullback `a_{small}^*` of presheaves of modules along the small étale base change below
`φ` preserves finite colimits. -/
noncomputable instance preservesFiniteColimits_pullback_smallEtaleStructureComparison :
    PreservesFiniteColimits (PresheafOfModules.pullback.{u}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)) :=
  ⟨fun _ _ _ => inferInstance⟩


/-- The direct image of presheaves of modules along the small étale base change below `φ` is
additive. -/
noncomputable instance additive_pushforward_smallEtaleStructureComparison :
    (PresheafOfModules.pushforward.{u}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).Additive :=
  Stacks.AlgebraicGeometry.RestrictionExact.additive_presheafPushforward.{u}
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)

/-- The pullback `a_{small}^*` of presheaves of modules along the small étale base change below
`φ` is additive. -/
noncomputable instance additive_pullback_smallEtaleStructureComparison :
    (PresheafOfModules.pullback.{u}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).Additive :=
  (PresheafOfModules.pullbackPushforwardAdjunction.{u}
    (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)).left_adjoint_additive

/-- The source of the comparison map of **Stacks 06WC** below an arrow `φ : x ⟶ y`, as a functor
of the presheaf of modules: restriction at `y` followed by `a_{small}^*`. -/
noncomputable abbrev flatBaseChangeComparisonSource :
    PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj ⥤
      PresheafOfModules.{u}
        (SmallEtale.structureSheaf E (p.obj x).left.1 (contains_base B E h S hS p x)).obj :=
  restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ y ⋙
    PresheafOfModules.pullback.{u}
      (F := smallEtaleBaseChange E (smallEtaleBaseMorphism B E h S hS p φ))
      (smallEtaleStructureComparison B E h S hS p hp φ τ hτ)

/-- The functor `F ↦ a_{small}^*(F|_{V_ét})` below `φ` preserves finite colimits. -/
noncomputable instance preservesFiniteColimits_flatBaseChangeComparisonSource :
    Limits.PreservesFiniteColimits
      (flatBaseChangeComparisonSource B E h S hS p hp τ hτ φ) :=
  Limits.comp_preservesFiniteColimits _ _

end

/-- **The extension clause of Stacks 0764 part (2), for presheaves of modules.**  In a short
exact sequence of presheaves of `𝒪_𝒳`-modules whose outer terms have the flat base change
property of **Stacks 0762**, the middle term has it too. -/
theorem hasFlatBaseChangeProperty_X₂_of_shortExact
    (T : ShortComplex (PresheafOfModules.{u} (ringStructureSheafCore B S hS p hp τ hτ).obj))
    (hT : T.ShortExact)
    (h₁ : HasFlatBaseChangeProperty B E h S hS p hp τ hτ T.X₁)
    (h₃ : HasFlatBaseChangeProperty B E h S hS p hp τ hτ T.X₃) :
    HasFlatBaseChangeProperty B E h S hS p hp τ hτ T.X₂ := fun {_ _} φ hflat =>
  ShortComplex.isIso_app_of_shortExact
    (flatBaseChangeComparisonSource B E h S hS p hp τ hτ φ)
    (restrictModuleToSmallEtaleFunctor.{u, v, w, u} B E h S hS p hp τ hτ _)
    (restrictModulePullbackComparisonNatTrans B E h S hS p hp τ hτ φ) hT
    (h₁ φ hflat) (h₃ φ hflat)

end AlgebraicGeometry.Stack

end
