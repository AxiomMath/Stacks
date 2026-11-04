module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.PushforwardContinuous
public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Submodule
public import Mathlib.CategoryTheory.Preadditive.Injective.Basic
public import Mathlib.Topology.Sheaves.Flasque
public import StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Injective sheaves of modules on a ringed space are flasque

Let `(X, 𝒪_X)` be a ringed space, encoded by a sheaf of rings `R` on the open-cover site of a
topological space `X`. If `I` is an injective sheaf of `R`-modules and `U' ⊆ U` are opens of `X`,
then the restriction map `I(U) → I(U')` is surjective. Equivalently, every injective sheaf of
modules is flasque.

## Main definitions

No new definitions are introduced. The subsheaf of sections vanishing locally outside an open
subset, and the direct image of a restriction, are
`Stacks.Cohomology.InjectiveRestriction.supportedSubmodule` and
`directImageRestriction` of
`StacksFrontier.Topology.Sheaves.Cohomology.CechAcyclicity.InjectiveSheavesRestrictOnto`.

## Main results

* `Stacks.Cohomology.exists_map_eq_of_injective` (Stacks Tag 01EA): the restriction map of an
  injective sheaf of modules along an inclusion of opens is surjective. It is
  `InjectiveRestriction.injective_restriction_surjective` of the imported module.
* `Stacks.Cohomology.isFlasque_of_injective_module` (Stacks Tag 09SX): an injective sheaf of
  modules is flasque.

## Implementation notes

The extension argument is the one of the imported module. The source argues with the
extension-by-zero functors `j_!`, which corepresent sections over an open, and concludes by
Yoneda. Sheaves of modules in Mathlib do not come with a `j_!`, so the
argument is run with the equivalent construction `supportedSubmodule M U`: the subsheaf of
sections that vanish locally outside `U`. The injectivity of `j'_!𝒪_{U'} → j_!𝒪_U` in the source
appears there as `supportedSubmodule_toDirectImageRestriction_mono`, the statement that
`supportedSubmodule I U' ⟶ I ⟶ j_*(I|_{U'})` is a monomorphism; injectivity of `I` then splits
off a map `j_*(I|_{U'}) ⟶ I`, and evaluating it at `U` produces the required extension.

The pushforward used is the one of `SheafOfModules.overPushforwardOverAdj`, which needs binary
products on the site; the open-cover site `Opens X` has them.

Since `Opens X` is a partial order, any two parallel restriction maps of a presheaf of modules
agree. The three lemmas `map_eq_map_comp`, `map_comp_eq_map_comp` and `map_eq_zero_of_map_eq_zero`
package this together with functoriality, and every step below goes through them. Stating them as
structural lemmas, instead of unfolding restriction maps to the underlying presheaf of abelian
groups, is what keeps all intermediate terms type-correct, so no transparency option is needed.

The three universes are independent: the space, the sheaf of rings and the module carriers.

`supportedSubmodule` is pinned by `mem_supportedSubmodule_iff`, which spells out its sections and
is imported with it, and by `supportedSubmodule_ι_apply` below, which identifies its inclusion
into `M`.

## References

* [Stacks Project, Tag 01EA](https://stacks.math.columbia.edu/tag/01EA)
* [Stacks Project, Tag 09SX](https://stacks.math.columbia.edu/tag/09SX)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u v w

namespace Stacks.Cohomology

open Stacks.Cohomology.InjectiveRestriction (supportedSubmodule directImageRestriction
  toDirectImageRestriction mem_supportedSubmodule_iff eq_zero_of_locally_zero
  supportedSubmodule_toDirectImageRestriction_mono)

variable {X : Type u} [TopologicalSpace X]
variable {R : Sheaf (Opens.grothendieckTopology X) RingCat.{v}}

/-! ### Restriction maps on the open-cover site

The poset `Opens X` has at most one morphism between two objects, so a restriction map of a
presheaf of modules is determined by its source and target. These three lemmas are the only
form in which that fact is used below.
-/

/-- Restricting along `h : A ⟶ C` agrees with restricting along `f : A ⟶ B` and then
`g : B ⟶ C`, for any choice of the three maps. -/
theorem map_eq_map_comp (M : PresheafOfModules.{w} R.obj) {A B C : (Opens X)ᵒᵖ}
    (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) (s : M.obj A) :
    M.map h s = M.map g (M.map f s) := by
  rw [← M.map_comp_apply]
  exact M.congr_map_apply (Subsingleton.elim _ _) s

/-- Any two ways of restricting a section from `A` down to `C` through an intermediate object
agree. -/
theorem map_comp_eq_map_comp (M : PresheafOfModules.{w} R.obj) {A B B' C : (Opens X)ᵒᵖ}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A ⟶ B') (g' : B' ⟶ C) (s : M.obj A) :
    M.map g (M.map f s) = M.map g' (M.map f' s) := by
  rw [← M.map_comp_apply, ← M.map_comp_apply]
  exact M.congr_map_apply (Subsingleton.elim _ _) s

/-- A section that restricts to zero along `f : A ⟶ B` restricts to zero along any
`h : A ⟶ C` that factors through `B`. -/
theorem map_eq_zero_of_map_eq_zero (M : PresheafOfModules.{w} R.obj) {A B C : (Opens X)ᵒᵖ}
    (f : A ⟶ B) (g : B ⟶ C) (h : A ⟶ C) {s : M.obj A} (hs : M.map f s = 0) :
    M.map h s = 0 :=
  (map_eq_map_comp M f g h s).trans (by rw [hs]; exact map_zero _)

/-- If `s` restricts to zero along `f' : A ⟶ B'`, then any restriction of it through another
intermediate object `B` is zero. -/
theorem map_comp_eq_zero (M : PresheafOfModules.{w} R.obj) {A B B' C : (Opens X)ᵒᵖ}
    (f : A ⟶ B) (g : B ⟶ C) (f' : A ⟶ B') (g' : B' ⟶ C) {s : M.obj A} (hs : M.map f' s = 0) :
    M.map g (M.map f s) = 0 :=
  (map_comp_eq_map_comp M f g f' g' s).trans (by rw [hs]; exact map_zero _)

/-! ### The subsheaf of sections supported in an open -/

/-- The inclusion `supportedSubmodule M U ⟶ M` is, on sections, the inclusion of the underlying
submodule. This pins down `(supportedSubmodule M U).ι`. -/
theorem supportedSubmodule_ι_apply (M : SheafOfModules.{w} R) (U : Opens X) (V : (Opens X)ᵒᵖ)
    (s : (supportedSubmodule M U).toSheafOfModules.val.obj V) :
    (supportedSubmodule M U).ι.val.app V s = s.val :=
  rfl

/-- A section of `M` over `V` that vanishes locally outside `U` and whose restriction to the
categorical product `U ⨯ V` is zero is itself zero: outside `U` it vanishes locally by
assumption, and on `U ⊓ V` it vanishes because `U ⊓ V` maps to `U ⨯ V`. -/
theorem eq_zero_of_mem_supportedSubmodule (M : SheafOfModules.{w} R) (U : Opens X)
    {V : (Opens X)ᵒᵖ} (s : M.val.obj V) (hmem : s ∈ (supportedSubmodule M U).obj V)
    (hs : M.val.map (prod.snd : U ⨯ V.unop ⟶ V.unop).op s = 0) : s = 0 := by
  refine eq_zero_of_locally_zero M s fun x hx => ?_
  by_cases hxU : x ∈ U
  · exact ⟨U ⊓ V.unop, inf_le_right, ⟨hxU, hx⟩,
      map_eq_zero_of_map_eq_zero M.val (prod.snd : U ⨯ V.unop ⟶ V.unop).op
        (prod.lift (homOfLE inf_le_left) (homOfLE inf_le_right) :
          U ⊓ V.unop ⟶ U ⨯ V.unop).op _ hs⟩
  · exact (mem_supportedSubmodule_iff M U s).mp hmem x hx hxU

/-! ### Injective sheaves of modules are flasque -/

/-- The extension statement behind Stacks Tag 01EA, phrased with the restriction maps
`PresheafOfModules.map` of `I`: every section of an injective sheaf of modules over `U'` is the
restriction of a section over any larger open `U`. -/
theorem exists_map_eq_of_injective
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
    (I : SheafOfModules.{w} R) [Injective I]
    {U' U : Opens X} (h : U' ≤ U) (y : I.val.obj (op U')) :
    ∃ s : I.val.obj (op U), I.val.map (homOfLE h).op s = y :=
  InjectiveRestriction.injective_restriction_surjective R I h y

/-- **Stacks Project, Tag 09SX.** An injective sheaf of modules on a ringed space is flasque,
stated with Mathlib's `TopCat.Presheaf.IsFlasque` for the underlying sheaf of abelian groups.
This is the reformulation of Tag 01EA. -/
@[stacks 09SX, sga "4 V 4.10" "2), F=A, ringed space", ega "0 12.2.1" "partial"]
instance isFlasque_of_injective_module
    {X : Type u} [TopologicalSpace X]
    (R : Sheaf (Opens.grothendieckTopology X) RingCat.{v})
    (I : SheafOfModules.{w} R) [Injective I] :
    TopCat.Presheaf.IsFlasque (X := TopCat.of X) ((SheafOfModules.toSheaf R).obj I).obj where
  epi {V W} i := by
    have hle : W.unop ≤ V.unop := leOfHom i.unop
    rw [Subsingleton.elim i (homOfLE hle).op]
    exact ConcreteCategory.epi_of_surjective _
      (Stacks.Cohomology.InjectiveRestriction.injective_restriction_surjective R I hle)

end Stacks.Cohomology

end
