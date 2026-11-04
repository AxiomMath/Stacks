module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Sheafification
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.FlatObjectRefinement
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticSerreSubcategory
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticSheafification

/-!
# Stacks 0774 (2) at every module universe

`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ParasiticSerreSubcategory.lean` and
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ParasiticSheafification.lean` prove part (2)
of **Stacks 0774** — the `τ`-sheafification of a parasitic presheaf of modules is parasitic, and
the parasitic modules form a Serre subcategory of `Mod(𝒳_τ, 𝒪_𝒳)` — under `UnivLE.{u + 1, t}`,
which fails at the module universe `t = u` of the schemes. This file proves the same statements
with that inequality replaced by what the arguments use:

* the two sheafification hypotheses `CategoryTheory.HasSheafify` and
  `CategoryTheory.GrothendieckTopology.WEqualsLocallyBijective` for `AddCommGrpCat`-valued
  presheaves, which the library meets at the module universe `u` through essential smallness of
  the site; and
* `CategoryTheory.Balanced` of the category of modules, for the closure under extensions.

## Main results

* `AlgebraicGeometry.Stack.containsZero_parasiticModules`: the parasitic modules contain a zero
  object, at any module universe.
* `AlgebraicGeometry.Stack.isParasitic_X₂_of_shortExact_of_balanced` and
  `AlgebraicGeometry.Stack.isClosedUnderExtensions_parasiticModules_of_balanced`: the closure
  under extensions in a balanced category of modules.
* `AlgebraicGeometry.Stack.isParasitic_sheafification'`: **Stacks 0774** (2)(a), under the
  sheafification hypotheses alone.
* `AlgebraicGeometry.Stack.isParasitic_of_epi'`: the closure under quotients, likewise.
* `AlgebraicGeometry.Stack.isSerreClass_parasiticModules'`: **Stacks 0774** (2)(b), likewise.

## Implementation notes

Both the sheafification and the quotient statements rest on
`CategoryTheory.Presheaf.subsingleton_obj_of_isLocallySurjective`: vanishing of sections at a
covering-refinable family of objects passes along a locally surjective morphism of presheaves
whose target is separated; for the flat objects of `𝒳` the refinement property is
`AlgebraicGeometry.Stack.isCoveringRefinable_flatObject`.

`CategoryTheory.Balanced` is assumed rather than `CategoryTheory.Abelian`, because
`Mod(𝒳_τ, 𝒪_𝒳)` already carries a `CategoryTheory.Preadditive` instance and a second one arriving
through an assumed `Abelian` leaves instance resolution unable to reach `Balanced`. Under the two
sheafification hypotheses `SheafOfModules.instAbelian` supplies it.

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w t v₁ u₁ u₂

section Sections

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

variable {R : Sheaf J RingCat.{u₂}}

/-- The middle term of a short exact sequence of sheaves of modules whose outer terms have
vanishing modules of sections at an object has a vanishing module of sections there, in a
balanced category of sheaves of modules. -/
private theorem subsingleton_obj_X₂_of_shortExact_of_balanced
    [Balanced (SheafOfModules.{t} R)]
    {Sq : ShortComplex (SheafOfModules.{t} R)} (hSq : Sq.ShortExact) (X : Cᵒᵖ)
    (h₁ : Subsingleton (Sq.X₁.val.obj X)) (h₃ : Subsingleton (Sq.X₃.val.obj X)) :
    Subsingleton (Sq.X₂.val.obj X) := by
  let E : SheafOfModules.{t} R ⥤ ModuleCat.{t} (R.obj.obj X) :=
    SheafOfModules.forget.{t} R ⋙ PresheafOfModules.evaluation R.obj X
  have hppl : PreservesLimit (parallelPair Sq.g 0) E :=
    ((inferInstance : PreservesFiniteLimits E).preservesFiniteLimits
        WalkingParallelPair).preservesLimit
  have hex : (Sq.map E).Exact := hSq.exact.map_of_mono_of_preservesKernel E hSq.mono_f hppl
  refine subsingleton_of_forall_eq 0 fun y => ?_
  obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 hex y (h₃.elim _ _)
  rw [← hz, h₁.elim z 0]
  exact map_zero _

end Sections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (τ : SiteKind)

section Balanced

/-- A zero module is parasitic, so the parasitic modules contain a zero object, at any module
universe. -/
instance containsZero_parasiticModules :
    (parasiticModules.{u, w, t} B S hS 𝒳 τ).ContainsZero := by
  obtain ⟨Z, hZ⟩ := (hasZeroObject_of_hasTerminal_object (C := SheafOfModules.{t}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ))).zero
  exact ⟨Z, hZ, fun x _ => ModuleCat.subsingleton_of_isZero (Functor.map_isZero
    (SheafOfModules.forget.{t} _ ⋙ PresheafOfModules.evaluation _ (op x)) hZ)⟩

/-- **Stacks 0774** (2)(b), the closure under extensions, in a balanced category of modules:
the middle term of a short exact sequence `0 → F₁ → F₂ → F₃ → 0` of modules on one of the sites
associated with an algebraic stack, with `F₁` and `F₃` parasitic, is parasitic. This is
`AlgebraicGeometry.Stack.isParasitic_X₂_of_shortExact` with its hypothesis `UnivLE.{u + 1, t}`
replaced by `CategoryTheory.Balanced` of the category of modules. -/
theorem isParasitic_X₂_of_shortExact_of_balanced
    [Balanced (SheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ))]
    {Sq : ShortComplex (SheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ))}
    (hSq : Sq.ShortExact)
    (h₁ : IsParasitic B S hS 𝒳 τ Sq.X₁.val) (h₃ : IsParasitic B S hS 𝒳 τ Sq.X₃.val) :
    IsParasitic B S hS 𝒳 τ Sq.X₂.val := fun x hx =>
  subsingleton_obj_X₂_of_shortExact_of_balanced.{t} hSq (op x) (h₁ x hx) (h₃ x hx)

/-- The parasitic modules are closed under extensions in a balanced category of modules, by
`AlgebraicGeometry.Stack.isParasitic_X₂_of_shortExact_of_balanced`. -/
instance isClosedUnderExtensions_parasiticModules_of_balanced
    [Balanced (SheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p 𝒳.val.isFiberedInGroupoids τ))] :
    (parasiticModules.{u, w, t} B S hS 𝒳 τ).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hSq h₁ h₃ :=
    isParasitic_X₂_of_shortExact_of_balanced.{u, w, t} B S hS 𝒳 τ hSq h₁ h₃

end Balanced

section Sheafify

variable [HasSheafify (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) AddCommGrpCat.{t}]
  [(BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ).WEqualsLocallyBijective
    AddCommGrpCat.{t}]

/-- Under the two sheafification hypotheses alone, the `τ`-sheafification of a parasitic presheaf
of `𝒪_𝒳`-modules on an algebraic stack is parasitic. -/
theorem isParasitic_sheafification'
    (M : PresheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ).obj)
    (hM : IsParasitic B S hS 𝒳 τ M) :
    IsParasitic B S hS 𝒳 τ
      ((PresheafOfModules.sheafification
        (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) (𝟙 _)).obj M).val := by
  have hls := (GrothendieckTopology.W_toSheafify
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) M.presheaf).isLocallySurjective
  exact fun x hx => Presheaf.subsingleton_obj_of_isLocallySurjective
    (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ)
    (CategoryTheory.toSheafify
      (BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) M.presheaf)
    ((PresheafOfModules.sheafification
      (J := BigFppfOver.associatedTopology B S hS 𝒳.val.val.p τ) (𝟙 _)).obj M).isSheaf.isSeparated
    (isCoveringRefinable_flatObject B S hS 𝒳 τ) hM hx

/-- Under the two sheafification hypotheses alone, the target of an epimorphism of sheaves of
`𝒪_𝒳`-modules with parasitic source is parasitic. -/
theorem isParasitic_of_epi'
    {F G : SheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ)}
    (f : F ⟶ G) [Epi f] (hF : IsParasitic B S hS 𝒳 τ F.val) :
    IsParasitic B S hS 𝒳 τ G.val := by
  have := Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi f
  exact fun x hx => Presheaf.subsingleton_obj_of_isLocallySurjective _
    ((PresheafOfModules.toPresheaf _).map f.val) G.isSheaf.isSeparated
    (isCoveringRefinable_flatObject B S hS 𝒳 τ) hF hx

/-- Under the two sheafification hypotheses alone, the parasitic modules are closed under
quotients. -/
instance isClosedUnderQuotients_parasiticModules' :
    (parasiticModules.{u, w, t} B S hS 𝒳 τ).IsClosedUnderQuotients where
  prop_of_epi f hf hF := by
    have := hf
    exact isParasitic_of_epi' B S hS 𝒳 τ f hF

/-- Under the two sheafification hypotheses alone, the parasitic modules form a Serre
subcategory of `Mod(𝒳_τ, 𝒪_𝒳)`. -/
instance isSerreClass_parasiticModules' :
    (parasiticModules.{u, w, t} B S hS 𝒳 τ).IsSerreClass where

end Sheafify

end AlgebraicGeometry.Stack

end
