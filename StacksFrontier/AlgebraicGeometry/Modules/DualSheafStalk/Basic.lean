module

public import StacksFrontier.AlgebraicGeometry.ReflexiveHull.CoherentDual
public import StacksFrontier.AlgebraicGeometry.Reflexive.ExtensionChain.Depth
public import StacksFrontier.AlgebraicGeometry.ReflexiveStalk.Basic
/-!
# Reflexivity of a module on a scheme is reflexivity of all its stalks

Let `X` be a locally Noetherian scheme and let `F` be an `𝒪_X`-module such that `F` and its dual
`F^∨` are of finite presentation.  Then `F` is reflexive — the canonical map `F ⟶ F^∨∨` is an
isomorphism — exactly when every stalk `F_x` is a reflexive `𝒪_{X,x}`-module.  This is the
equivalence of conditions (1) and (2) of
[Stacks, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3).

## Main results

* `isReflexive_iff_forall_isReflexive_stalk`: the equivalence (1) ⟺ (2) of Tag 0AY3.
* `isReflexive_iff_forall_isReflexive_stalk_of_isCoherent`: the same for a coherent module on a
  locally Noetherian scheme.

## Implementation notes

`isReflexive_dualSheaf_of_isFinitePresentation` of
`StacksFrontier/AlgebraicGeometry/ReflexiveHull/DualStalk.lean` proves reflexivity of a *dual* by a
counting argument which deliberately avoids comparing the stalk of the canonical map with the
algebraic evaluation map.  That comparison is what Tag 0AY3 needs, and it is
`dualStalkEquiv_stalkHom_toDoubleDual`: both sides are computed on a germ of a local section
and a germ of a local functional brought onto a common open neighbourhood, where the left side is
the defining formula `toDoubleDual_val_app_apply` of the canonical map and the right side is the
germ formula of Tag 01CP.

The finite-presentation hypothesis on the dual is what Tag 01CP consumes at `F^∨`, and it is
needed for both directions: the equivalence is read off a single square, so neither half of it is
available without identifying the stalk of `F^∨∨`.  On a locally Noetherian scheme it follows from
coherence of `F` by way of the first assertion of
[Stacks, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ), which is
`hasLocalKernelPresentationDual`.

The stalkwise criterion for an isomorphism is `isIso_of_bijective_stalkHom`; the reflexivity
predicate is `IsReflexive`, that is `IsIso (toDoubleDual F)`, so the two sides of the equivalence
are bijectivity statements about the *same* map and no choice of isomorphism intervenes.

## References

* [Stacks Project, Tag 0AY3](https://stacks.math.columbia.edu/tag/0AY3)
* [Stacks Project, Tag 01CP](https://stacks.math.columbia.edu/tag/01CP)
* [Stacks Project, Tag 01CQ](https://stacks.math.columbia.edu/tag/01CQ)
-/

@[expose] public section

open CategoryTheory TopologicalSpace Opposite AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.ReflexiveModules

open Stacks.SheafOfModules.SheafHomStalk

variable {X : Scheme.{u}}

/-! ### The germ formula for the stalk of a dual -/

/-- A morphism of `𝒪_X`-modules which is an isomorphism is bijective on every stalk. -/
public theorem bijective_stalkHom_of_isIso {F G : X.Modules} (f : F ⟶ G) [IsIso f] (x : X) :
    Function.Bijective (stalkHom f x) := by
  have h1 : (stalkHom (inv f) x).comp (stalkHom f x) = LinearMap.id := by
    rw [← stalkHom_comp, IsIso.hom_inv_id, stalkHom_id]
  have h2 : (stalkHom f x).comp (stalkHom (inv f) x) = LinearMap.id := by
    rw [← stalkHom_comp, IsIso.inv_hom_id, stalkHom_id]
  refine ⟨fun a b hab => ?_, fun b => ⟨stalkHom (inv f) x b, ?_⟩⟩
  · have ha := LinearMap.congr_fun h1 a
    have hb := LinearMap.congr_fun h1 b
    simp only [LinearMap.comp_apply, LinearMap.id_apply] at ha hb
    rw [← ha, ← hb, hab]
  · simpa only [LinearMap.comp_apply, LinearMap.id_apply] using LinearMap.congr_fun h2 b

/-! ### Stacks 0AY3, conditions (1) and (2) -/

/-- **(1) ⟺ (2) of Stacks, Tag 0AY3 for a coherent module** on a locally Noetherian scheme.

A coherent module is of finite presentation by Tag 01BW (1), and its dual is of finite
presentation by `isFinitePresentation_dualSheaf`, which is the first assertion of Tag 01CQ at
`𝒢 = 𝒪_X` fed through Tag 01XZ. -/
public theorem isReflexive_iff_forall_isReflexive_stalk_of_isCoherent (X : Scheme.{u})
    [IsLocallyNoetherian X] (F : X.Modules)
    (hF : F.IsCoherent) :
    IsReflexive F ↔ ∀ x : X, Module.IsReflexive (ringStalk X.sheaf x) (modStalk F x) := by
  have hcoh : F.IsCoherent := hF
  have hFP : F.IsFinitePresentation := _root_.isFinitePresentation_of_isCoherent F
  have : F.IsCoherent := hF
  have hdual : (dualSheaf F).IsFinitePresentation := isFinitePresentation_dualSheaf F
  exact Stacks.AlgebraicGeometry.ReflexiveModules.isReflexive_iff_forall_modStalk F

end Stacks.AlgebraicGeometry.ReflexiveModules

end
