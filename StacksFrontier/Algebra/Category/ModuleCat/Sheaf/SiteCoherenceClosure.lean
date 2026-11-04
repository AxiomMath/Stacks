module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.EpiMono
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.LocalOnCover.Coherence
public import StacksFrontier.AlgebraicGeometry.Topologies.CoherentKernelOnSite
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ULiftUnit

/-!
# Closure properties of coherence on a site

Stacks 01BY (1) says that a subsheaf of finite type of a coherent sheaf of modules is coherent.
This file proves it over a ringed site, for the predicate `SheafOfModules.IsCoherentOnSite` of
Stacks 03DL(8), together with its local forms.

## Main definitions

* `Stacks.SheafOfModules.presheafRelationsIsoOfInjective`: the presheaf of relations among a
  finite family of sections is unchanged by a map of presheaves of modules that is injective on
  sections.

## Main results

* `Stacks.SheafOfModules.isCoherentOnSite_of_mono`: a subsheaf of finite type of a coherent
  sheaf of modules on a site is coherent.
* `Stacks.SheafOfModules.isCoherentOnSite_of_coversTop_of_mono`: a sheaf of modules that is, on
  the members of a covering family, a subsheaf of finite type of a coherent sheaf, is coherent.
* `Stacks.SheafOfModules.isCoherentOnSite_of_coversTop_of_iso`: a sheaf of modules locally
  isomorphic to a coherent sheaf is coherent.

## Implementation notes

`SheafOfModules.IsCoherentOnSite` is defined over an arbitrary site, so coherence of the
restriction `M.over U` to a slice site is stated in the same vocabulary, and heredity is the
theorem `Stacks.SheafOfModules.isCoherentOnSite_over`.

For a map `ι : M ⟶ N` that is injective on sections, the relations among `s` and among `ι s`
are the same submodule of `R(V)^n` at every object `V`, so `presheafRelationsIsoOfInjective` is
the identity on elements.

## References

* [Stacks Project, Tag 01BY](https://stacks.math.columbia.edu/tag/01BY)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe u v w m

section Relations

variable {C : Type u} [Category.{v} C] {S : Cᵒᵖ ⥤ RingCat.{w}}

/-- The presheaf of relations among a finite family of sections `s` is isomorphic to the presheaf
of relations among `φ ∘ s`, for a map `φ` of presheaves of modules that is injective on sections:
at every object the two relation modules are the same submodule of the module of coefficient
tuples. -/
noncomputable def presheafRelationsIsoOfInjective {M N : PresheafOfModules.{m} S} (φ : M ⟶ N)
    (hφ : ∀ V : Cᵒᵖ, Function.Injective (φ.app V)) {U : C} {n : ℕ}
    (s : Fin n → M.obj (op U)) :
    PresheafOfModules.relations M s ≅
      PresheafOfModules.relations N (fun i ↦ φ.app (op U) (s i)) := by
  let e (V : (Over U)ᵒᵖ) :
      (PresheafOfModules.relations M s).obj V ≅
        (PresheafOfModules.relations N (fun i ↦ φ.app (op U) (s i))).obj V := by
    refine LinearEquiv.toModuleIso (LinearEquiv.ofEq _ _ (Submodule.ext fun a ↦ ?_))
    have key : Fintype.linearCombination (S.obj (op V.unop.left))
          (fun i ↦ N.restrictₛₗ V.unop.hom.op (φ.app (op U) (s i))) a =
        φ.app (op V.unop.left) (Fintype.linearCombination (S.obj (op V.unop.left))
          (fun i ↦ M.restrictₛₗ V.unop.hom.op (s i)) a) := by
      rw [Fintype.linearCombination_apply, Fintype.linearCombination_apply, map_sum]
      refine Finset.sum_congr rfl fun i _ ↦ ?_
      rw [map_smul]
      exact (congrArg (fun y ↦ a i • y)
        (PresheafOfModules.naturality_apply φ V.unop.hom.op (s i))).symm
    simp only [LinearMap.mem_ker, key]
    exact ⟨fun h ↦ by rw [h, map_zero], fun h ↦ hφ _ (by rw [h, map_zero])⟩
  refine PresheafOfModules.isoMk e ?_
  intro V W f
  ext a
  rfl

end Relations

section Subsheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- A subsheaf of finite type of a coherent sheaf of modules on a site is coherent. -/
theorem isCoherentOnSite_of_mono {M N : SheafOfModules.{m} R} (ι : M ⟶ N) [Mono ι]
    (hN : SheafOfModules.IsCoherentOnSite N)
    (hM : PresheafOfModules.IsFiniteType J M.val) :
    SheafOfModules.IsCoherentOnSite M :=
  ⟨hM, fun U n s ↦ isFiniteType_of_presheafIso
    (presheafRelationsIsoOfInjective ((SheafOfModules.forget R).map ι)
      (injective_app_of_mono ι) s).symm
    (hN.kernel_isFiniteType U n fun i ↦ ((SheafOfModules.forget R).map ι).app (op U) (s i))⟩

/-- A sheaf of modules whose restriction to each member of a family covering the final object
is a subsheaf of finite type of the restriction of a coherent sheaf is coherent. The coherent
sheaf `P i` and the monomorphism may depend on the member of the covering family. -/
theorem isCoherentOnSite_of_coversTop_of_mono (M : SheafOfModules.{m} R)
    {I : Type (max u v)} (U : I → C) (hU : J.CoversTop U)
    (P : I → SheafOfModules.{m} R) (hP : ∀ i, SheafOfModules.IsCoherentOnSite (P i))
    (hft : ∀ i, PresheafOfModules.IsFiniteType (J.over (U i)) (M.over (U i)).val)
    (ι : ∀ i, M.over (U i) ⟶ (P i).over (U i)) (hι : ∀ i, Mono (ι i)) :
    SheafOfModules.IsCoherentOnSite M :=
  isCoherentOnSite_of_coversTop M U hU fun i ↦
    have := hι i
    isCoherentOnSite_of_mono (ι i) (isCoherentOnSite_over (P i) (hP i) (U i)) (hft i)

/-- A sheaf of modules whose restriction to each member of a family covering the final object
is isomorphic to the restriction of a coherent sheaf is coherent. -/
theorem isCoherentOnSite_of_coversTop_of_iso (M : SheafOfModules.{m} R)
    {I : Type (max u v)} (U : I → C) (hU : J.CoversTop U)
    (P : I → SheafOfModules.{m} R) (hP : ∀ i, SheafOfModules.IsCoherentOnSite (P i))
    (e : ∀ i, (P i).over (U i) ≅ M.over (U i)) :
    SheafOfModules.IsCoherentOnSite M :=
  isCoherentOnSite_of_coversTop M U hU fun i ↦
    isCoherentOnSite_of_iso (e i) (isCoherentOnSite_over (P i) (hP i) (U i))

end Subsheaf

end Stacks.SheafOfModules

end
