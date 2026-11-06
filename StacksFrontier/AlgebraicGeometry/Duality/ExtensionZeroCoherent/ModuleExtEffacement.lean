module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.Basic
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.EnoughInjectives
public import Mathlib.CategoryTheory.Abelian.Injective.Ext
public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.Refinements

/-!
# Effacing a positive-degree `Ext`-class by an epimorphism

A class in `Ext^q(Y, Z)` with `q > 0` dies after restriction along some epimorphism `P ⟶ Y`.
Present the class by a map out of an injective resolution of `Z`, which
`CategoryTheory.InjectiveResolution.extMk_surjective` says is possible, and refine the presenting
map until it factors through the previous term of the resolution: the refinement exists because
an injective resolution is exact, and factoring through the previous term is exactly the
criterion `CategoryTheory.InjectiveResolution.extMk_eq_zero_iff` for the class to vanish.

This is the dimension-shifting step of a devissage in the first argument of `Ext`, and it is the
reason such a devissage terminates.

## The statement is general, and its instances for `𝒪_X`-modules

The effacement lemma is about an arbitrary abelian category with enough injective resolutions,
and nothing below is specific to a scheme. At `X.Modules`, the case the extension-by-zero
material consumes, the two instance arguments it takes stand as follows:

* `HasInjectiveResolutions X.Modules` is Mathlib's, reached by instance search alone.
  `𝒪_X`-modules are Grothendieck abelian in the scheme's own universe by Mathlib's
  `AlgebraicGeometry.Scheme.Modules.instIsGrothendieckAbelian`, a Grothendieck abelian category
  has enough injectives by `CategoryTheory.IsGrothendieckAbelian.enoughInjectives`, and enough
  injectives gives injective resolutions by
  `CategoryTheory.InjectiveResolution.instHasInjectiveResolutions`.
* `Stacks.ExtEffacement.hasExt_modules` needs a derived category, and which one is chosen
  changes the statement; see below.

## Which derived category this is about

`CategoryTheory.HasExt.{w} A` is the smallness of the derived morphism types, and it is obtained
from a derived category by `CategoryTheory.hasExt_of_hasDerivedCategory`. For `X.Modules` there
are two derived categories to obtain it from, and they are different categories:
`CategoryTheory.HasDerivedCategory.standard`, which the extension-by-zero material installs as a
local instance, and the global `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory`, whose own
documentation records that it and not the standard one is the model against which the direct-sum
and Brown-representability statements about `D(𝒪_X)` have content.

The two give `HasExt` at *different universes*: for `X : Scheme.{u}` the standard model yields
`HasExt.{u + 1}` and the global instance yields `HasExt.{u}`. So `hasExt_modules` below fixes
`u + 1` in its own statement, matching
`StacksFrontier.AlgebraicGeometry.Duality.ExtensionZeroCoherent.BoundedCoherentTStructure` and
everything else built on `DeligneSystemHom`. Pinning it in the statement rather than inheriting
it from an ambient instance is deliberate: this file imports nothing from this repository, so no
import can change what it says.

`hasExt_modules` is not an instance, following Mathlib's policy and this repository's, under
which a category has in general several reasonable `HasExt` universes and none of them is
canonical. A consumer activates it with
`attribute [local instance] Stacks.ExtEffacement.hasExt_modules`, or uses Mathlib's
`CategoryTheory.HasExt.standard`, which at `X.Modules` gives the same universe.

## Main results

* `Stacks.ExtEffacement.exists_epi_precomp_eq_zero`: **a positive-degree `Ext`-class is killed by
  restriction along some epimorphism onto its first argument**.
* `Stacks.ExtEffacement.hasExt_modules`: `𝒪_X`-modules have `Ext` in the standard model.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Abelian AlgebraicGeometry

universe w v u

namespace Stacks.ExtEffacement

/-- **A positive-degree `Ext`-class is killed by restriction along some epimorphism onto its
first argument.** Write the class as `R.extMk f`, for `f` a map from `Y` into the degree-`q - 1`
term of an injective resolution `R` of `Z` which is annihilated by the next differential; such an
`f` exists by `CategoryTheory.InjectiveResolution.extMk_surjective`. Exactness of `R` in positive
degrees refines `f` along an epimorphism `p : P ⟶ Y` to a map factoring through the degree-`q - 2`
term, and `CategoryTheory.InjectiveResolution.extMk_eq_zero_iff` says that such a factorization is
precisely the vanishing of `R.extMk (p ≫ f)`, which is the restricted class. -/
public theorem exists_epi_precomp_eq_zero {A : Type u} [Category.{v} A] [Abelian A]
    [HasExt.{w} A] [HasInjectiveResolutions A] {Y Z : A} {q : ℕ} (hq : 0 < q)
    (e : Ext.{w} Y Z q) :
    ∃ (P : A) (p : P ⟶ Y), Epi p ∧ (Ext.mk₀ p).comp e (zero_add q) = 0 := by
  obtain ⟨n, rfl⟩ : ∃ n, q = n + 1 := ⟨q - 1, by omega⟩
  let I := injectiveResolution Z
  obtain ⟨f, hf, rfl⟩ := I.extMk_surjective e (n + 2) rfl
  obtain ⟨P, p, hp, g, hg⟩ := (I.exact_succ n).exact_up_to_refinements f hf
  refine ⟨P, p, hp, ?_⟩
  rw [I.mk₀_comp_extMk, I.extMk_eq_zero_iff _ _ _ _ n rfl]
  exact ⟨g, hg.symm⟩

/-- **`𝒪_X`-modules have `Ext` in the standard derived category.** The universe is `u + 1`, which
is the one `CategoryTheory.HasDerivedCategory.standard` produces for `X.Modules`, and it is fixed
in the statement rather than taken from whatever `HasDerivedCategory` instance happens to be
ambient; the global `AlgebraicGeometry.Scheme.Modules.hasDerivedCategory` would give `HasExt.{u}`,
a different statement. See the module documentation.

Not an instance: a category has in general several reasonable `HasExt` universes. Activate it
with `attribute [local instance] Stacks.ExtEffacement.hasExt_modules`. -/
public theorem hasExt_modules (X : Scheme.{u}) : HasExt.{u + 1} X.Modules := by
  let : HasDerivedCategory.{u + 1} X.Modules := HasDerivedCategory.standard _
  exact hasExt_of_hasDerivedCategory _

end Stacks.ExtEffacement

end
