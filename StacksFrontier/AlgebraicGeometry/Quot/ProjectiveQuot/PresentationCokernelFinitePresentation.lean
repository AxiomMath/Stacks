module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.PresentationCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationCokernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.SliceRestrictionFiniteKernel
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FiniteLocallyFreeFinitePresentation
public import StacksFrontier.AlgebraicGeometry.FlatBaseChange.Descent
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentationGeneration.AssemblyOnSite
public import StacksFrontier.AlgebraicGeometry.Etale.ElementaryNeighborhood.StructureSheafProjectiveSections
public import StacksFrontier.AlgebraicGeometry.Modules.FinitePresentationPullbackScheme

/-!
# Finite presentation of the twisted family of a Grassmannian presentation

For a finite locally free quotient `q : 𝒪_T^{⊕ N} ⟶ ℰ` with `N = freeRank n r m`, the kernel
`ker(q)` is of finite type (Stacks 01BP, the target being of finite presentation), so is its
inverse image on `ℙⁿ_T`, and the cokernel `ℱ^{(m)}` of `u_m : π^* ker(q) ⟶ 𝒪^{⊕ r}(m)` is of finite
presentation (Stacks 0H96), hence quasi-coherent.

## Main results

* `AlgebraicGeometry.ProjectiveQuot.isFinitePresentation_freeModule`: `𝒪^{⊕ r}` on `ℙⁿ_T` is of
  finite presentation.
* `AlgebraicGeometry.ProjectiveQuot.isFinitePresentation_presentation_target`: the target `ℰ` of
  `q` is of finite presentation.
* `AlgebraicGeometry.ProjectiveQuot.isFiniteType_kernel_presentation`: `ker(q)` is of finite type.
* `AlgebraicGeometry.ProjectiveQuot.isFinitePresentation_presentationCokernel`: `ℱ^{(m)}` is of
  finite presentation, and `AlgebraicGeometry.ProjectiveQuot.isQuasicoherent_presentationCokernel`
  quasi-coherent.

## References

* [Stacks Project, Tag 0DPA](https://stacks.math.columbia.edu/tag/0DPA)
* [Stacks Project, Tag 05UH](https://stacks.math.columbia.edu/tag/05UH)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ProjectiveQuot

variable {n r : ℕ}

/-- The free module `𝒪^{⊕ r}` on `ℙⁿ_T` is of finite presentation. -/
instance isFinitePresentation_freeModule (T : Scheme.{u}) :
    (freeModule n r T).IsFinitePresentation :=
  Space.FpAssembly.isFinitePresentation_sigma
    (fun _ : Fin r => Scheme.unitModule (projectiveSpaceOver n T)) (fun _ => inferInstance)

/-- The target of a Grassmannian presentation is of finite presentation. -/
theorem isFinitePresentation_presentation_target {T : Scheme.{u}} {k N : ℕ}
    (q : Grassmannian.QuotientPresentation T k N) : q.target.IsFinitePresentation :=
  have := q.finiteLocallyFree
  have := AlgebraicGeometry.SheafOfModules.IsFiniteLocallyFreeOfRank.isFiniteLocallyFree
    q.target (N - k)
  Stacks.SheafOfModules.isFinitePresentation_of_isFiniteLocallyFree q.target

/-- **The kernel of a Grassmannian presentation is of finite type** (Stacks 01BP). -/
instance isFiniteType_kernel_presentation {T : Scheme.{u}} {k N : ℕ}
    (q : Grassmannian.QuotientPresentation T k N) : (kernel q.map).IsFiniteType :=
  haveI := isFinitePresentation_presentation_target q
  haveI := q.map_epi
  Stacks.SheafOfModules.SliceFinite.isFiniteType_kernel_of_epi_from_finite_free q.map

/-- **`ℱ^{(m)}` is of finite presentation** (Stacks 0H96), where `ℱ^{(m)}` is the cokernel of
`u_m : π^* ker(q) ⟶ 𝒪^{⊕ r}(m)`. -/
instance isFinitePresentation_presentationCokernel (m : ℕ) {T : Scheme.{u}} {k : ℕ}
    (q : Grassmannian.QuotientPresentation T k (freeRank.{u} n r m)) :
    (presentationCokernel m q).IsFinitePresentation :=
  haveI : ((Scheme.Modules.pullback (projectiveSpaceOver n T ↘ T)).obj
      (kernel q.map)).IsFiniteType :=
    @Stacks.AlgebraicGeometry.FlatBaseChange.isFiniteType_pullback _ _ _ _
      (isFiniteType_kernel_presentation q)
  haveI : (twist (m : ℤ) (freeModule n r T)).IsFinitePresentation :=
    isFinitePresentation_twist _ _ inferInstance
  Stacks.SheafOfModules.isFinitePresentation_cokernel (presentationTwistMap m q)

/-- `ℱ^{(m)}` is quasi-coherent. -/
instance isQuasicoherent_presentationCokernel (m : ℕ) {T : Scheme.{u}} {k : ℕ}
    (q : Grassmannian.QuotientPresentation T k (freeRank.{u} n r m)) :
    (presentationCokernel m q).IsQuasicoherent :=
  Stacks.Modules.isQuasicoherent_of_isFinitePresentation _

end AlgebraicGeometry.ProjectiveQuot

end
