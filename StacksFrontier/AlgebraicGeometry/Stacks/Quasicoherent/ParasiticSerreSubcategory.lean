module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Limits
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.CategoryTheory.Abelian.SerreClass.Basic
public import Mathlib.CategoryTheory.Limits.Constructions.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.ContainsZero
public import Mathlib.CategoryTheory.ObjectProperty.EpiMono
public import Mathlib.CategoryTheory.ObjectProperty.Extensions
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PushforwardExact
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticModules
public import StacksFrontier.AlgebraicGeometry.Stacks.Quasicoherent.ParasiticSheafification

/-!
# The parasitic modules are a Serre subcategory (Stacks 0774)

Let `𝒳` be an algebraic stack over a scheme `S` in a big fppf site `B`, and let `τ` be one of
the five topologies of **Stacks 06TP**. Clause (2)(b) of **Stacks 0774** says that the full
subcategory of `Mod(𝒳_τ, 𝒪_𝒳)` consisting of the parasitic modules (**Stacks 0773**) is a Serre
subcategory, that is: it contains a zero object and is closed under submodules, under quotients
and under extensions.

All four are proved here. The zero object, the closure under submodules and the closure under
extensions rest on the same fact, that taking sections of a sheaf of modules at an object is
*left* exact, being the composite of the forgetful functor to presheaves of modules with
evaluation and so preserving finite limits. A submodule of a module whose sections vanish at a
flat object has vanishing sections there because a monomorphism is injective on sections; and if
`0 → F₁ → F₂ → F₃ → 0` is short exact with `F₁` and `F₃` parasitic then, at a flat object `x`,
every section of `F₂` is killed by the map to `F₃` and is therefore the image of a section of
`F₁`, which vanishes. This is the source's "evaluate on `x` lying over a scheme flat over `𝒳`".

The closure under quotients is the one assertion that is *not* formal, because an epimorphism of
sheaves of modules is not surjective on sections: it is only locally surjective. That is exactly
the hypothesis of
`AlgebraicGeometry.Stack.isParasitic_of_isLocallySurjective` of
`StacksFrontier/AlgebraicGeometry/Stacks/Quasicoherent/ParasiticSheafification.lean`, which is the
same argument the source uses for clause (2)(a) — a section of the quotient at a flat object
comes, on a covering that may be taken to consist of flat objects again, from a section of the
parasitic module, hence vanishes locally, hence vanishes.

## Main definitions

* `AlgebraicGeometry.Stack.parasiticModules`: the full subcategory of `Mod(𝒳_τ, 𝒪_𝒳)` cut out by
  the parasitic condition, as a `CategoryTheory.ObjectProperty`.

## Main results

* `AlgebraicGeometry.Stack.isParasitic_of_mono`: **Stacks 0774** (2)(b), closure under
  submodules.
* `AlgebraicGeometry.Stack.isParasitic_X₂_of_shortExact`: **Stacks 0774** (2)(b), closure under
  extensions.
* `AlgebraicGeometry.Stack.isParasitic_of_epi`: **Stacks 0774** (2)(b), closure under quotients.
* `AlgebraicGeometry.Stack.isSerreClass_parasiticModules`: **Stacks 0774** (2)(b) itself — the
  parasitic modules are a Serre subcategory of `Mod(𝒳_τ, 𝒪_𝒳)`. The three closure properties and
  the zero object are also recorded as the instances
  `CategoryTheory.ObjectProperty.ContainsZero`,
  `CategoryTheory.ObjectProperty.IsClosedUnderSubobjects`,
  `CategoryTheory.ObjectProperty.IsClosedUnderQuotients` and
  `CategoryTheory.ObjectProperty.IsClosedUnderExtensions`, which is what
  `CategoryTheory.ObjectProperty.IsSerreClass` is assembled from.

## Implementation notes

`CategoryTheory.ObjectProperty.isSerreClass_iff_prop_X₂_of_exact` (**Stacks 02MP**) is not used:
its criterion quantifies over short complexes that are exact at the middle term only, and for
those the comparison object is the image sheaf, so it needs the same local surjectivity as the
closure under quotients does and offers no shorter route to it.

The closure under extensions, and the presence of a zero object, need `Mod(𝒳_τ, 𝒪_𝒳)` to be
abelian, which is no extra assumption on the mathematics: a Serre subcategory is by definition a
subcategory of an abelian category, and `CategoryTheory.ObjectProperty.IsSerreClass` asks for it
too. It is obtained from `SheafOfModules.instAbelian` together with the sheafification results
for `AddCommGrpCat`-valued presheaves, which hold once the universe of the module sections is at
least that of the site; that is the hypothesis `UnivLE.{u + 1, t}` those statements carry. It is
not assumed as an `Abelian` instance argument, because `Mod(𝒳_τ, 𝒪_𝒳)` already carries a
`CategoryTheory.Preadditive` instance and a second one arriving through an assumed `Abelian`
leaves instance resolution unable to reach `CategoryTheory.Balanced`.

Left exactness of sections is used through the explicit composite
`SheafOfModules.forget R ⋙ PresheafOfModules.evaluation R.obj X` rather than through
`SheafOfModules.evaluation`, because the composite is additive and preserves finite limits by
instance resolution alone, whereas for the packaged form both have to be re-established by hand.

Vanishing is expressed as `Subsingleton` of the module of sections, which is the form
**Stacks 0773** states the parasitic condition in, so no transport along an isomorphism of
module categories is needed anywhere below.

## References

* [Stacks Project, Tag 0773](https://stacks.math.columbia.edu/tag/0773)
* [Stacks Project, Tag 0774](https://stacks.math.columbia.edu/tag/0774)
* [Stacks Project, Tag 02MO](https://stacks.math.columbia.edu/tag/02MO)
* [Stacks Project, Tag 02MP](https://stacks.math.columbia.edu/tag/02MP)
* [Stacks Project, Tag 06TP](https://stacks.math.columbia.edu/tag/06TP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry.Stack

universe u w t v₁ u₁ u₂

attribute [local instance] CategoryTheory.GrothendieckTopology.hasSheafify_addCommGrpCat
  CategoryTheory.GrothendieckTopology.wEqualsLocallyBijective_addCommGrpCat

section Sections

variable {C : Type u₁} [Category.{v₁} C] {J : GrothendieckTopology C}

/-- Taking sections of a sheaf of modules at an object, as a functor to modules over the ring of
sections of the coefficient sheaf there: the forgetful functor to presheaves of modules followed
by evaluation. It is additive and preserves finite limits, which is all that is used below. -/
private abbrev sectionsFunctor (R : Sheaf J RingCat.{u₂}) (X : Cᵒᵖ) :
    SheafOfModules.{t} R ⥤ ModuleCat.{t} (R.obj.obj X) :=
  SheafOfModules.forget.{t} R ⋙ PresheafOfModules.evaluation R.obj X

variable {R : Sheaf J RingCat.{u₂}}

/-- A sheaf of modules which is a zero object has a vanishing module of sections at every
object. -/
private theorem subsingleton_obj_of_isZero {M : SheafOfModules.{t} R} (hM : IsZero M)
    (X : Cᵒᵖ) : Subsingleton (M.val.obj X) :=
  ModuleCat.subsingleton_of_isZero (Functor.map_isZero (sectionsFunctor.{t} R X) hM)

/-- A monomorphism of sheaves of modules is injective on the module of sections at every object,
because taking sections preserves finite limits and hence monomorphisms. So if the target has a
vanishing module of sections at an object, then so does the source. -/
private theorem subsingleton_obj_of_mono {M N : SheafOfModules.{t} R} (i : M ⟶ N) [Mono i]
    (X : Cᵒᵖ) (hN : Subsingleton (N.val.obj X)) : Subsingleton (M.val.obj X) := by
  have hmono : Mono ((sectionsFunctor.{t} R X).map i) := inferInstance
  exact ⟨fun a b => (ModuleCat.mono_iff_injective _).1 hmono (hN.elim _ _)⟩

/-- The middle term of a short exact sequence of sheaves of modules whose outer terms have
vanishing modules of sections at an object has a vanishing module of sections there.

Taking sections at the object preserves finite limits, so it carries the short exact sequence to
a sequence of modules exact at its middle term. A section of the middle sheaf is killed by the
map to the third, whose sections vanish, hence is the image of a section of the first, and those
vanish as well. -/
private theorem subsingleton_obj_X₂_of_shortExact [UnivLE.{max u₁ v₁, t}]
    {Sq : ShortComplex (SheafOfModules.{t} R)} (hSq : Sq.ShortExact) (X : Cᵒᵖ)
    (h₁ : Subsingleton (Sq.X₁.val.obj X)) (h₃ : Subsingleton (Sq.X₃.val.obj X)) :
    Subsingleton (Sq.X₂.val.obj X) := by
  have hmf := hSq.mono_f
  have hex : (Sq.map (sectionsFunctor.{t} R X)).Exact :=
    hSq.exact.map_of_mono_of_preservesKernel (sectionsFunctor.{t} R X) hmf inferInstance
  have key : ∀ y : Sq.X₂.val.obj X, y = 0 := by
    intro y
    obtain ⟨z, hz⟩ := (ShortComplex.moduleCat_exact_iff _).1 hex y (h₃.elim _ _)
    rw [← hz, h₁.elim z 0]
    exact map_zero _
  exact ⟨fun a b => (key a).trans (key b).symm⟩

end Sections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable (𝒳 : Stack.AlgebraicStacks.{u, w} B S hS) (τ : SiteKind)

/-- The full subcategory of `Mod(𝒳_τ, 𝒪_𝒳)` consisting of the parasitic modules of
**Stacks 0773**, as an object property: a sheaf of modules has the property exactly when its
underlying presheaf of modules is parasitic. -/
abbrev parasiticModules :
    ObjectProperty (SheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ)) :=
  fun F => IsParasitic B S hS 𝒳 τ F.val

/-- **Stacks 0774** (2)(b), the closure under submodules. A submodule of a parasitic module on
one of the sites associated with an algebraic stack is parasitic.

It is immediate from the definition, as the source says: a monomorphism of sheaves of modules is
injective on sections, so at a flat object the sections of the submodule inject into the
vanishing sections of the ambient module. -/
@[stacks 0774 "part (2)(b), the closure under submodules: a submodule of a parasitic module is
parasitic"]
theorem isParasitic_of_mono
    {F' F : SheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ)}
    (i : F' ⟶ F) [Mono i] (hF : IsParasitic B S hS 𝒳 τ F.val) :
    IsParasitic B S hS 𝒳 τ F'.val := fun x hx =>
  subsingleton_obj_of_mono.{t} i (op x) (hF x hx)

/-- The parasitic modules are closed under submodules, by
`AlgebraicGeometry.Stack.isParasitic_of_mono`. -/
instance : (parasiticModules.{u, w, t} B S hS 𝒳 τ).IsClosedUnderSubobjects where
  prop_of_mono i hi hF := @isParasitic_of_mono.{u, w, t} B S hS 𝒳 τ _ _ i hi hF

variable [UnivLE.{u + 1, t}]

/-- **Stacks 0774** (2)(b), the closure under extensions. Given a short exact sequence
`0 → F₁ → F₂ → F₃ → 0` of modules on one of the sites associated with an algebraic stack, with
`F₁` and `F₃` parasitic, the module `F₂` is parasitic.

This is the source's "evaluate on `x` lying over a scheme flat over `𝒳`": at a flat object the
sections of `F₁` and of `F₃` vanish, and taking sections is left exact, so the sections of `F₂`
vanish too. -/
@[stacks 0774 "part (2)(b), the closure under extensions: the middle term of a short exact
sequence of modules whose outer terms are parasitic is parasitic"]
theorem isParasitic_X₂_of_shortExact
    {Sq : ShortComplex (SheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ))}
    (hSq : Sq.ShortExact)
    (h₁ : IsParasitic B S hS 𝒳 τ Sq.X₁.val) (h₃ : IsParasitic B S hS 𝒳 τ Sq.X₃.val) :
    IsParasitic B S hS 𝒳 τ Sq.X₂.val := fun x hx =>
  subsingleton_obj_X₂_of_shortExact.{t} hSq (op x) (h₁ x hx) (h₃ x hx)

/-- A zero module is parasitic, so the parasitic modules contain a zero object. -/
instance : (parasiticModules.{u, w, t} B S hS 𝒳 τ).ContainsZero := by
  obtain ⟨Z, hZ⟩ := (inferInstance : HasZeroObject (SheafOfModules.{t}
    (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
      𝒳.val.isFiberedInGroupoids τ))).zero
  exact ⟨Z, hZ, fun x _ => subsingleton_obj_of_isZero.{t} hZ (op x)⟩

/-- The parasitic modules are closed under extensions, by
`AlgebraicGeometry.Stack.isParasitic_X₂_of_shortExact`. -/
instance : (parasiticModules.{u, w, t} B S hS 𝒳 τ).IsClosedUnderExtensions where
  prop_X₂_of_shortExact hSq h₁ h₃ :=
    isParasitic_X₂_of_shortExact.{u, w, t} B S hS 𝒳 τ hSq h₁ h₃

/-- **Stacks 0774** (2)(b), the closure under quotients. If `p : F ⟶ G` is an epimorphism of
modules on one of the sites associated with an algebraic stack and `F` is parasitic, then `G` is
parasitic.

An epimorphism of sheaves of modules is locally surjective, so this is
`AlgebraicGeometry.Stack.isParasitic_of_isLocallySurjective`: at a flat object every section of
`G` comes from a section of `F` on a covering, and that covering may be refined by one whose
sources are again flat objects, where `F` vanishes. -/
@[stacks 0774 "part (2)(b), the closure under quotients: a quotient of a parasitic module is
parasitic"]
theorem isParasitic_of_epi
    {F G : SheafOfModules.{t}
      (FibredSite.ringStructureSheafCore B S hS 𝒳.val.val.p
        𝒳.val.isFiberedInGroupoids τ)}
    (p : F ⟶ G) [Epi p] (hF : IsParasitic B S hS 𝒳 τ F.val) :
    IsParasitic B S hS 𝒳 τ G.val :=
  isParasitic_of_isLocallySurjective B S hS 𝒳 τ _
    (Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi p) hF

/-- The parasitic modules are closed under quotients, by
`AlgebraicGeometry.Stack.isParasitic_of_epi`. -/
instance : (parasiticModules.{u, w, t} B S hS 𝒳 τ).IsClosedUnderQuotients where
  prop_of_epi p hp hF := @isParasitic_of_epi.{u, w, t} B S hS 𝒳 τ _ _ _ p hp hF

/-- **Stacks 0774** (2)(b). The full subcategory of `Mod(𝒳_τ, 𝒪_𝒳)` consisting of the parasitic
modules is a Serre subcategory: it contains a zero object and is closed under submodules, under
quotients and under extensions, which are the four instances above. -/
@[stacks 0774 "part (2)(b): the parasitic modules are a Serre subcategory of Mod(𝒳_τ, 𝒪_𝒳)"]
instance isSerreClass_parasiticModules :
    (parasiticModules.{u, w, t} B S hS 𝒳 τ).IsSerreClass where

end AlgebraicGeometry.Stack

end
