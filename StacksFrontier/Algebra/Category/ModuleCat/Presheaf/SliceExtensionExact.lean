module

public import StacksFrontier.Algebra.Category.ModuleCat.Presheaf.SliceAdjunctions
public import Mathlib.Algebra.Category.ModuleCat.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import Mathlib.Algebra.Category.ModuleCat.Products
public import Mathlib.Algebra.DirectSum.Module
public import Mathlib.Algebra.Homology.ShortComplex.ExactFunctor
public import Mathlib.CategoryTheory.Abelian.Exact
public import Mathlib.CategoryTheory.Adjunction.Additive
public import Mathlib.CategoryTheory.Adjunction.Unique
public import Mathlib.CategoryTheory.Limits.ExactFunctor
import StacksCore.Tactic.StacksAttribute

/-!
# Extension of presheaves of modules from a slice category is exact

Let `O` be a presheaf of rings on a category `C` and let `U` be an object of `C`. Stacks 03EJ,
following Sites, Remark 0494, records that restriction of presheaves of modules to the slice
category `C/U` has a left adjoint `j_{U!}` and a right adjoint `j_{U*}`, and that `j_{U!}` is
exact. This file proves the exactness.

Exactness of `j_{U!}` is not formal: a left adjoint always preserves colimits, so the only
content is that `j_{U!}` preserves finite *limits*. The argument used here is the standard one
for a functor between abelian categories: an additive functor that preserves monomorphisms and
cokernels preserves homology, and a functor that preserves homology preserves finite limits. All
three of additivity, preservation of cokernels and preservation of colimits come from the
adjunction; preservation of monomorphisms is where the explicit direct-sum formula for `j_{U!}`
is needed.

That formula is `Stacks.Sites.OverModules.extensionPresheaf`: the sections of
`j_{U!} M` over `X` are `∐_{p : X ⟶ U} M(X/p)`. On that description `j_{U!} f` is the coproduct
of the components of `f`, so it is a monomorphism as soon as each component is — a coproduct of
injective maps of modules is injective, which is Grothendieck's axiom AB4 for `ModuleCat` and is
proved here by transporting the coproduct to a `DirectSum`.

Finally the statement is about an *arbitrary* left adjoint of restriction, the one packaged in a
`PresheafModuleAdjunctionsOver`; uniqueness of left adjoints transports exactness from the
direct-sum model to it.

## Main results

* `Stacks.Sites.OverModules.mono_sigmaMap`: a coproduct of monomorphisms of modules is a
  monomorphism.
* `Stacks.Sites.OverModules.extensionFunctor_map_app_eq`: `j_{U!} f` is, on sections over `X`,
  the coproduct of the components of `f` at the objects of `C/U` over `X`.
* `Stacks.Sites.OverModules.extensionFunctor_preservesMonos`: `j_{U!}` preserves
  monomorphisms.
* `Stacks.Sites.OverModules.extension_exact`: extension from the slice category is exact.

## Implementation notes

`mono_sigmaMap` is stated with the module universe in the form `max v t` for an index type in
`Type v`, because `ModuleCat.coprodIsoDirectSum` is: the direct sum of a `v`-indexed family of
modules only lives in the same universe as the modules when that universe dominates `v`. The
repo already has `Stacks.Sites.ExtensionByZero.mono_sigmaMap`, which is the same statement with
every universe collapsed to one and is proved from the `AB4` instance of `ModuleCat`; that
instance needs the ring, the index type and the modules in a single universe, so it does not
apply here, where the ring universe `w` is independent of the others. The two should be merged
once a single statement covers both.

For the same reason `extensionFunctor_preservesMonos` is stated at module universe `max v t`
rather than at a universe variable constrained only by `UnivLE`: `UnivLE.{v, a}` makes the index
type `a`-small but does not make `a` dominate `v` as a level, which is what the direct-sum
comparison needs.

## References

* [Stacks Project, Tag 03EJ](https://stacks.math.columbia.edu/tag/03EJ)
* [Stacks Project, Tag 0494](https://stacks.math.columbia.edu/tag/0494)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Sites.OverModules

universe v u w m t a

section Coproducts

/-- A coproduct of monomorphisms of modules is a monomorphism: Grothendieck's axiom AB4 for
`ModuleCat`, in the form of the map of coproducts induced by a family of maps, and with the
ring, the index type and the modules in three independent universes. -/
lemma mono_sigmaMap {R : Type w} [Ring R] {ι : Type v}
    {A B : ι → ModuleCat.{max v t, w} R} [HasCoproduct A] [HasCoproduct B]
    (p : ∀ i, A i ⟶ B i) (hp : ∀ i, Mono (p i)) : Mono (Limits.Sigma.map p) := by
  classical
  let l : DirectSum ι (fun i => A i) →ₗ[R] DirectSum ι (fun i => B i) :=
    DirectSum.lmap (R := R) (M := fun i => A i) (N := fun i => B i) fun i => (p i).hom
  have hl : Function.Injective l :=
    (DirectSum.lmap_injective (R := R) (M := fun i => A i) (N := fun i => B i)
      (f := fun i => (p i).hom)).mpr fun i => (ModuleCat.mono_iff_injective (p i)).1 (hp i)
  have hdecomp : Limits.Sigma.map p =
      (ModuleCat.coprodIsoDirectSum A).hom ≫ ModuleCat.ofHom l ≫
        (ModuleCat.coprodIsoDirectSum B).inv := by
    apply Sigma.hom_ext
    intro i
    have hlof : ModuleCat.ofHom (DirectSum.lof R ι (fun i => A i) i) ≫ ModuleCat.ofHom l =
        p i ≫ ModuleCat.ofHom (DirectSum.lof R ι (fun i => B i) i) :=
      ModuleCat.hom_ext (LinearMap.ext fun x => DirectSum.lmap_lof _ _ _)
    rw [Limits.Sigma.ι_map, ← Category.assoc, ModuleCat.ι_coprodIsoDirectSum_hom,
      ← Category.assoc, hlof, Category.assoc, ModuleCat.lof_coprodIsoDirectSum_inv]
  have : Mono (ModuleCat.ofHom l) := (ModuleCat.mono_iff_injective _).2 hl
  rw [hdecomp]
  infer_instance

end Coproducts

section Construction

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C) [UnivLE.{v, a}]

/-- On the summand indexed by `p : X ⟶ U`, the morphism `j_{U!} f` is the component of `f` at
the object `p` of `C/U`, followed by the inclusion of the corresponding summand. -/
lemma ι_comp_extensionFunctor_map_app
    {M M' : PresheafOfModules.{a, v, max u v, w} (overRingPresheaf O U)}
    (f : M ⟶ M') (X : Cᵒᵖ) (p : X.unop ⟶ U) :
    Sigma.ι (extensionSummands O U M X) p ≫
        ((extensionFunctor.{v, u, w, a} O U).map f).app X =
      f.app (op (Over.mk p)) ≫ Sigma.ι (extensionSummands O U M' X) p :=
  (ι_comp_extensionHomBackward O U M
    (f ≫ extensionHomForward O U M' (𝟙 (extensionPresheaf O U M'))) X p).trans rfl

/-- On sections over `X`, `j_{U!} f` is the coproduct of the components of `f` at the objects
of `C/U` lying over `X`. -/
lemma extensionFunctor_map_app_eq
    {M M' : PresheafOfModules.{a, v, max u v, w} (overRingPresheaf O U)}
    (f : M ⟶ M') (X : Cᵒᵖ) :
    ((extensionFunctor.{v, u, w, a} O U).map f).app X =
      Limits.Sigma.map (f := extensionSummands O U M X)
        (g := extensionSummands O U M' X) fun p => f.app (op (Over.mk p)) :=
  Sigma.hom_ext _ _ fun p => (ι_comp_extensionFunctor_map_app O U f X p).trans
    (Limits.Sigma.ι_map (f := extensionSummands O U M X) (g := extensionSummands O U M' X)
      (fun q => f.app (op (Over.mk q))) p).symm

end Construction

section Exactness

variable {C : Type u} [Category.{v} C] (O : Cᵒᵖ ⥤ RingCat.{w}) (U : C)

/-- Extension from the slice category preserves monomorphisms: a monomorphism of presheaves of
modules is injective on sections, and a coproduct of injective maps of modules is injective. -/
lemma extensionFunctor_preservesMonos :
    (extensionFunctor.{v, u, w, max v t} O U).PreservesMonomorphisms where
  preserves {M M'} f hf := by
    apply PresheafOfModules.mono_of_injective
    intro X
    have hmono : Mono (Limits.Sigma.map (f := extensionSummands O U M X)
        (g := extensionSummands O U M' X) fun p => f.app (op (Over.mk p))) :=
      mono_sigmaMap _ fun p => (ModuleCat.mono_iff_injective _).2
        (PresheafOfModules.injective_of_mono f (op (Over.mk p)))
    exact (ModuleCat.mono_iff_injective _).1 (extensionFunctor_map_app_eq O U f X ▸ hmono)

/-- Restriction of presheaves of modules to the slice category is additive. -/
lemma restrictionFunctor_additive :
    (restrictionFunctor.{v, u, w, max u v m} O U).Additive where
  map_add := by
    intros
    ext _ _
    rfl

/-- **Stacks 03EJ.** Extension of presheaves of modules from a slice category is exact. -/
@[stacks 03EJ "`j_{U!}` is exact"]
theorem extension_exact (A : PresheafModuleAdjunctionsOver.{v, u, w, m} O U) :
    exactFunctor
      (PresheafOfModules.{max u v m} (overRingPresheaf O U))
      (PresheafOfModules.{max u v m} O) A.extension := by
  rw [exactFunctor_iff]
  refine ⟨?_, ?_⟩
  · have hadd := restrictionFunctor_additive.{v, u, w, m} O U
    have hE := extensionFunctorAdjunction.{v, u, w, max u v m} O U
    have : (extensionFunctor.{v, u, w, max u v m} O U).Additive := hE.left_adjoint_additive
    have : (extensionFunctor.{v, u, w, max u v m} O U).PreservesMonomorphisms :=
      extensionFunctor_preservesMonos.{v, u, w, max u m} O U
    have : PreservesColimits (extensionFunctor.{v, u, w, max u v m} O U) :=
      hE.leftAdjoint_preservesColimits
    have := Functor.preservesHomology_of_preservesMonos_and_cokernels
      (extensionFunctor.{v, u, w, max u v m} O U)
    have : PreservesFiniteLimits (extensionFunctor.{v, u, w, max u v m} O U) :=
      Functor.preservesFiniteLimits_of_preservesHomology _
    exact preservesFiniteLimits_of_natIso
      (Adjunction.leftAdjointUniq A.extensionRestriction hE).symm
  · have := A.extensionRestriction.leftAdjoint_preservesColimits
    infer_instance

end Exactness

end Stacks.Sites.OverModules
