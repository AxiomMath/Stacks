module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.CategoryTheory.Sites.LocallyBijective
public import StacksFrontier.Homology.KFlat.Bifunctor
public import Mathlib.Algebra.Homology.HomotopyCategory.MappingCone

/-!
# Quasi-isomorphy of complexes of sheaves of modules is tested on enough objects

Let `R` be a sheaf of rings on a site `(C, J)` and let `B` be a class of objects of `C` such that
every object is covered by members of `B`. A short complex of sheaves of `R`-modules is exact as
soon as its sequences of sections over the members of `B` are exact, and consequently a morphism
of complexes of sheaves of `R`-modules is a quasi-isomorphism as soon as its complexes of sections
over the members of `B` are quasi-isomorphic. The object, morphism, ring and module universes are
independent.

Exactness of a short complex is the epimorphy of the canonical map to the kernel of its second
map; an epimorphism of sheaves of modules is detected by local surjectivity of the underlying
presheaves, which is detected on the members of `B`; and sections preserve kernels. For complexes
one passes to the mapping cone, which is compatible with taking sections.

## Main results

* `Stacks.SheafOfModules.exact_of_hasEnoughObjects`.
* `Stacks.SheafOfModules.quasiIso_of_hasEnoughObjects`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.SheafOfModules

universe v u u' t

variable {C : Type u'} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{u}}
  [HasSheafify J AddCommGrpCat.{t}] [J.WEqualsLocallyBijective AddCommGrpCat.{t}]
  {B : ObjectProperty C}

/-- Evaluation of a sheaf of modules at an object of the site is additive, for modules in any
universe `t` independent of the universe of the ring sheaf.
(`Stacks.SheafOfModules.evaluation_additive` is the case of modules in the universe of the
ring.) -/
instance evaluation_additive_of_universe (X : Cᵒᵖ) :
    (_root_.SheafOfModules.evaluation.{t} R X).Additive where
  map_add := rfl

/-- **Exactness of a short complex of sheaves of modules is tested on enough objects.** -/
theorem exact_of_hasEnoughObjects (hB : J.HasEnoughObjects B)
    (S : ShortComplex (_root_.SheafOfModules.{t} R))
    (h : ∀ ⦃V : C⦄, B V → (S.map (_root_.SheafOfModules.evaluation R (op V))).Exact) :
    S.Exact := by
  rw [S.exact_iff_epi_kernel_lift]
  apply EpiMono.epi_of_isLocallySurjective
  apply Presheaf.isLocallySurjective_of_hasEnoughObjects_surjective J _ hB
  intro V hV y
  let ev := _root_.SheafOfModules.evaluation R (op V)
  let ι := kernel.ι S.g
  let y' : ev.obj (kernel S.g) := y
  have h0 : ev.map ι ≫ ev.map S.g = 0 := by
    rw [← Functor.map_comp, kernel.condition, Functor.map_zero]
  have hy : (ev.map S.g).hom ((ev.map ι).hom y') = 0 := congrArg (fun f => f.hom y') h0
  obtain ⟨x, hx⟩ := (ShortComplex.moduleCat_exact_iff (S.map ev)).1 (h hV) _ hy
  refine ⟨x, (ModuleCat.mono_iff_injective (ev.map ι)).1 (Functor.map_mono _ _) ?_⟩
  have h1 : ev.map (kernel.lift S.g S.f S.zero) ≫ ev.map ι = ev.map S.f := by
    rw [← Functor.map_comp, kernel.lift_ι]
  exact (congrArg (fun f => f.hom x) h1).trans hx

/-- **Quasi-isomorphy of a morphism of complexes of sheaves of modules is tested on enough
objects.** If the complexes of sections of `φ` over the members of a class `B` of objects
covering every object of the site are quasi-isomorphic, then `φ` is a quasi-isomorphism. -/
theorem quasiIso_of_hasEnoughObjects (hB : J.HasEnoughObjects B)
    {K L : CochainComplex (_root_.SheafOfModules.{t} R) ℤ} (φ : K ⟶ L)
    (h : ∀ ⦃V : C⦄, B V → QuasiIso
      (((_root_.SheafOfModules.evaluation R (op V)).mapHomologicalComplex
        (ComplexShape.up ℤ)).map φ)) :
    QuasiIso φ := by
  rw [CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone]
  intro n
  rw [HomologicalComplex.exactAt_iff]
  refine exact_of_hasEnoughObjects hB _ (fun V hV => ?_)
  let ev := _root_.SheafOfModules.evaluation R (op V)
  have h1 := (CochainComplex.KFlatBifunctor.quasiIso_iff_acyclic_mappingCone _).1 (h hV) n
  rw [HomologicalComplex.exactAt_iff] at h1
  exact (ShortComplex.exact_iff_of_iso
    ((HomologicalComplex.shortComplexFunctor _ (ComplexShape.up ℤ) n).mapIso
      (CochainComplex.mappingCone.mapHomologicalComplexIso φ ev))).2 h1

end Stacks.SheafOfModules

end
