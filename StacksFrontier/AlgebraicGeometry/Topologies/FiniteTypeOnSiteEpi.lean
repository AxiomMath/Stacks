module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.EpiLocallySurjective
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.GlobalPresentationOfPresentation
public import StacksFrontier.AlgebraicGeometry.Topologies.ModuleTypesOnSite

/-!
# Finite type on a site is inherited by quotients

A quotient of a sheaf of modules which is of finite type on a site is again of finite type on
that site: the clause 03DL(5) is stable under epimorphisms.  This is immediate from the shape in
which `SheafOfModules.IsFiniteTypeOnSite` records it, namely an epimorphism onto the module from
a finite coproduct of copies of the structure sheaf on each member of a covering.  Composing
such an epimorphism with the given one again gives an epimorphism from the same finite
coproduct.

Two facts make the composition legitimate.  Restriction to a slice of the site preserves
epimorphisms, because an epimorphism of sheaves of modules is a local surjection and local
surjectivity is preserved by the cocontinuous forgetful functor of the slice.  And raising the
universe of the sections preserves epimorphisms, because it preserves colimits, hence pushouts.

## Main results

* `Stacks.SheafOfModules.epi_over`: the restriction of an epimorphism of sheaves of modules to
  a slice of the site is an epimorphism.
* `Stacks.SheafOfModules.hasFiniteGlobalGenerators_of_epi`: generation by finitely many global
  sections, Stacks 03DE(5), passes to a quotient.
* `Stacks.SheafOfModules.isFiniteTypeOnSite_of_epi`: `SheafOfModules.IsFiniteTypeOnSite`,
  Stacks 03DL(5), passes to a quotient.

## References

* [Stacks Project, Tag 03DE](https://stacks.math.columbia.edu/tag/03DE)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite SheafOfModules

universe u v w

namespace Stacks.SheafOfModules

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C} {R : Sheaf J RingCat.{w}}

/-- **Local surjectivity of a morphism of sheaves of modules is inherited by its restriction to
a slice of the site.**  The forgetful functor of the slice is cocontinuous, and local
surjectivity is preserved by whiskering along a cocontinuous functor. -/
theorem isLocallySurjective_over {M N : SheafOfModules.{w} R} (q : M ⟶ N)
    [Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map q)] (U : C) :
    Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf (R.over U)).map (q.over U)) := by
  let _ : (Over.forget U).IsCocontinuous (J.over U) J :=
    ⟨fun hS => J.overEquiv_symm_mem_over _ _ hS⟩
  exact Presheaf.isLocallySurjective_whisker (J.over U) J (Over.forget U)
    ((SheafOfModules.toSheaf R).map q).hom

/-- **The restriction of an epimorphism of sheaves of modules to a slice of the site is an
epimorphism.**  An epimorphism is a local surjection, local surjectivity restricts to the
slice, and a local surjection is an epimorphism. -/
theorem epi_over [HasSheafify J AddCommGrpCat.{w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    {M N : SheafOfModules.{w} R} (q : M ⟶ N) [Epi q] (U : C) : Epi (q.over U) := by
  have h1 : Sheaf.IsLocallySurjective ((SheafOfModules.toSheaf R).map q) :=
    Stacks.SheafOfModules.EpiMono.isLocallySurjective_of_epi q
  exact Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective (q.over U)
    (isLocallySurjective_over q U)

/-- **Generation by finitely many global sections passes to a quotient.**  If `q : M ⟶ N` is an
epimorphism and `M` admits an epimorphism from a finite coproduct of copies of the structure
sheaf, then so does `N`: compose the two.  The universe of the sections is raised by a functor
which preserves colimits and therefore epimorphisms. -/
theorem hasFiniteGlobalGenerators_of_epi
    [HasWeakSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [HasWeakSheafify J AddCommGrpCat.{max u v w}]
    [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    {M N : SheafOfModules.{w} R} (q : M ⟶ N) [Epi q]
    (hM : M.HasFiniteGlobalGenerators) : N.HasFiniteGlobalGenerators := by
  have hpc : PreservesColimitsOfSize.{0, 0}
      (uliftForPresentationFunctor.{u, v, w, w, max u v w} (R := R)) :=
    have := uliftForPresentationFunctor_preservesColimits.{u, v, w, w, max u v w} (R := R)
    preservesColimitsOfSize_shrink _
  have hu : Epi ((uliftForPresentationFunctor.{u, v, w, w, max u v w} (R := R)).map q) :=
    inferInstance
  obtain ⟨n, P, ι, hP, π, hπ⟩ := hM
  exact ⟨n, P, ι, hP, _, @epi_comp _ _ _ _ _ π hπ _ hu⟩

/-- **A quotient of a sheaf of modules of finite type on a site is of finite type on the
site.**  This is the clause 03DL(5) of Stacks 03DL for an epimorphism: on each member of a
covering witnessing finite type for the source, the restricted epimorphism composes with the
finite presenting coproduct of the source to present the target. -/
theorem isFiniteTypeOnSite_of_epi
    [HasSheafify J AddCommGrpCat.{w}] [J.WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{w}]
    [∀ U : C, HasWeakSheafify (J.over U) AddCommGrpCat.{max u v w}]
    [∀ U : C, (J.over U).WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
    {M N : SheafOfModules.{w} R} (p : M ⟶ N) [Epi p]
    (hM : M.IsFiniteTypeOnSite) : N.IsFiniteTypeOnSite := by
  refine ⟨fun U => ?_⟩
  obtain ⟨I, V, f, hf, h⟩ := hM.locally_finitelyGenerated U
  refine ⟨I, V, f, hf, fun i => ?_⟩
  have := epi_over p (V i)
  exact hasFiniteGlobalGenerators_of_epi (p.over (V i)) (h i)

end Stacks.SheafOfModules

end
