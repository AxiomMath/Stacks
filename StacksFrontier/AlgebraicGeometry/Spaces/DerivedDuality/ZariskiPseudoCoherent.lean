module

public import StacksFrontier.AlgebraicGeometry.Spaces.DerivedDuality.LocalCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentStructureSheaf
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.CoherentOfFinitePresentationUnit
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.CohomologyBoundedAbove
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.CoherentModules
public import StacksFrontier.CategoryTheory.Sites.Cohomology.PseudoCoherent.Summands
public import StacksFrontier.AlgebraicGeometry.CoherentOfFiniteType

/-!
# Pseudo-coherence on the Zariski site of a Noetherian scheme

On a locally Noetherian scheme `T` the structure sheaf of the Zariski ringed site
`AlgebraicGeometry.Scheme.zariskiRingedSite` is coherent in the sense of Stacks 01BV, and on a
Noetherian scheme every bounded above object of `D(𝒪_T)` with coherent cohomology sheaves is
pseudo-coherent on that ringed site (Stacks 08E8, read on the site).

## Main results

* `AlgebraicGeometry.Scheme.zariskiRingedSite_isCoherentOnSite_unit`.
* `AlgebraicGeometry.Scheme.zariskiRingedSite_isPseudoCoherent_of_schemeCoherent`.

## References

* [Stacks Project, Tag 01XZ](https://stacks.math.columbia.edu/tag/01XZ)
* [Stacks Project, Tag 08E8](https://stacks.math.columbia.edu/tag/08E8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian

namespace AlgebraicGeometry.Scheme

variable (T : Scheme.{u})

/-- **The structure sheaf of the Zariski ringed site of a locally Noetherian scheme is
coherent.** The relations clause is `AlgebraicGeometry.RingedSite.isFiniteType_relations_unit`
at the covering by the affine opens, whose rings of sections are Noetherian and whose
restriction maps are flat. -/
theorem zariskiRingedSite_isCoherentOnSite_unit [IsLocallyNoetherian T] :
    SheafOfModules.IsCoherentOnSite
      (SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf T.zariskiRingedSite.O)) where
  isFiniteType := PresheafOfModules.isFiniteType_unit _
  kernel_isFiniteType U n s :=
    RingedSite.isFiniteType_relations_unit T.zariskiRingedSite (fun A => IsAffineOpen A)
      (fun W => by
        refine ⟨⟨fun Y _ => ∃ A : T.Opens, IsAffineOpen A ∧ Y ≤ A ∧ A ≤ W,
          fun {Y Z} f ⟨A, hA, hYA, hAW⟩ g => ⟨A, hA, (leOfHom g).trans hYA, hAW⟩⟩, ?_, ?_⟩
        · intro x hx
          obtain ⟨V, hV, hxV, hVW⟩ :=
            (Opens.isBasis_iff_nbhd.mp T.isBasis_affineOpens) hx
          exact ⟨V, homOfLE hVW, ⟨V, hV, le_rfl, hVW⟩, hxV⟩
        · rintro Y h ⟨A, hA, hYA, hAW⟩
          exact ⟨A, homOfLE hYA, homOfLE hAW, hA, Subsingleton.elim _ _⟩)
      (fun A hA => IsLocallyNoetherian.component_noetherian ⟨A, hA⟩)
      (fun {A A'} h hA hA' => by
        have := HasRingHomProperty.appLE (P := @AlgebraicGeometry.Flat) (𝟙 T)
          (inferInstance : AlgebraicGeometry.Flat (𝟙 T)) ⟨A, hA⟩ ⟨A', hA'⟩ (leOfHom h)
        simp only [Scheme.Hom.appLE, Scheme.Hom.id_app] at this
        exact this) U n s

/-- A module of finite presentation on the Zariski ringed site of a locally Noetherian scheme is
coherent on the site. -/
theorem zariskiRingedSite_isCoherentOnSite_of_isFinitePresentation [IsLocallyNoetherian T]
    (M : SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf T.zariskiRingedSite.O))
    (hM : M.IsFinitePresentation) : SheafOfModules.IsCoherentOnSite M :=
  Stacks.SheafOfModules.isCoherentOnSite_of_isFinitePresentation_of_unit T.zariskiRingedSite M
    (zariskiRingedSite_isCoherentOnSite_unit T)

/-- **Stacks 08E8 on the Zariski ringed site.** On a Noetherian scheme, a bounded above object of
`D(𝒪_T)` with coherent cohomology sheaves is pseudo-coherent on the Zariski ringed site: its
cohomology sheaves are coherent on the site, hence pseudo-coherent in every degree, and a bounded
above object with pseudo-coherent cohomology sheaves is pseudo-coherent. -/
theorem zariskiRingedSite_isPseudoCoherent [IsNoetherian T]
    (X : RingedSite.SchemeStdDerived T) (hX : RingedSite.SchemeCoherent T X) (b : ℤ)
    (hb : ∀ i : ℤ, b < i → IsZero ((RingedSite.schemeStdHomology T i).obj X)) :
    letI := HasDerivedCategory.standard
      (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf T.zariskiRingedSite.O))
    T.zariskiRingedSite.IsPseudoCoherent X := by
  let := HasDerivedCategory.standard
    (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf T.zariskiRingedSite.O))
  have hO := zariskiRingedSite_isCoherentOnSite_unit T
  refine (RingedSite.isPseudoCoherent_iff_forall_isPseudoCoherentFrom T.zariskiRingedSite X).2
    fun m => ?_
  refine RingedSite.isPseudoCoherentFrom_of_homology_of_boundedAbove_general
    T.zariskiRingedSite X m b hb ?_
  intro i _
  have hfp : ((RingedSite.schemeStdHomology T i).obj X).IsFinitePresentation :=
    (Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_iff_isFinitePresentation _).1
      (hX i)
  exact RingedSite.isPseudoCoherentFrom_singleFunctor_zero_of_isCoherentOnSite
    T.zariskiRingedSite hO _
    (zariskiRingedSite_isCoherentOnSite_of_isFinitePresentation T _ hfp) (m - i)

end AlgebraicGeometry.Scheme
