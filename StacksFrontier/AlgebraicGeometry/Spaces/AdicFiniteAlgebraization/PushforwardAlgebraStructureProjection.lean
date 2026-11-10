module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.AlgebraUnitPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFiniteAlgebraization.ClosedSubspaceOfQuotient
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionStructureSheafCoherent
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom

/-!
# The structure map of a direct-image algebra along a closed immersion

For a closed immersion `i : Z ⟶ X` of algebraic spaces, the module underlying the direct-image
algebra `i_* 𝒪_Z` (`AlgebraicGeometry.Space.pushforwardAlgebra`) and the direct image
`AlgebraicGeometry.Space.structureSheafPushforward` of the structure sheaf are both quotients of
`𝒪_X` by the kernel ideal of `i`, through the structure map of the algebra and the structure
projection respectively. They are therefore isomorphic under `𝒪_X`.

## Main results

* `AlgebraicGeometry.Space.ker_unitToUnderlyingModule_pushforwardAlgebra`: the kernel of the
  structure map of `f_* 𝒪_Y` is the kernel ideal sheaf of `f`.
* `AlgebraicGeometry.Space.pushforwardAlgebraUnderlyingIso`: the isomorphism, for a closed
  immersion.
* `AlgebraicGeometry.Space.unitToUnderlyingModule_comp_pushforwardAlgebraUnderlyingIso`: its
  compatibility with the two maps out of `𝒪_X`.

## References

* [Stacks Project, Tag 03MB](https://stacks.math.columbia.edu/tag/03MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X Y : AlgebraicSpaces B S hS}

/-- On sections, the structure map of the direct-image algebra is the structure map of `f`. -/
theorem pushforwardAlgebra_algebraMap_eq_structureSharp_app (f : Y ⟶ X)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) (r : (structureSheaf B S hS X.1 X.2).obj.obj U) :
    (pushforwardAlgebra B S hS (Over.mk f)).algebraMap U r =
      (structureSharp B S hS f).hom.app U r :=
  congrArg (fun φ => (φ.hom.app U).hom r) (forgetCommRingSheaf_map_fSharp B S hS f)

/-- **The kernel of the structure map of `f_* 𝒪_Y` is the kernel ideal sheaf of `f`.** -/
theorem ker_unitToUnderlyingModule_pushforwardAlgebra (f : Y ⟶ X) :
    SheafOfModules.Submodule.ker
        (AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (Over.mk f))) =
      kernelIdealSheaf B S hS f := by
  refine SheafOfModules.Submodule.ext (PresheafOfModules.Submodule.ext fun U => ?_)
  ext a
  refine (SheafOfModules.Submodule.mem_ker
    (AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (Over.mk f))) U a).trans ?_
  change (pushforwardAlgebra B S hS (Over.mk f)).algebraMap U a = 0 ↔ _
  have h := pushforwardAlgebra_algebraMap_eq_structureSharp_app B S hS f U a
  exact ⟨fun ha => RingHom.mem_ker.2 (h.symm.trans ha), fun ha => h.trans (RingHom.mem_ker.1 ha)⟩

/-- For a closed immersion the structure map of the direct-image algebra is surjective. -/
theorem epi_unitToUnderlyingModule_pushforwardAlgebra (f : Y ⟶ X)
    (hf : IsClosedImmersion B S hS f.hom) :
    Epi (AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (Over.mk f))) := by
  have h : Presheaf.IsLocallySurjective (SmallEtale.topology B S hS X.1)
      (structureSharp B S hS f).hom :=
    isLocallySurjective_structureSharp B S hS f hf
  rw [Presheaf.isLocallySurjective_iff_whisker_forget] at h
  refine Stacks.SheafOfModules.EpiMono.epi_of_isLocallySurjective _ ⟨fun {U} s ↦ ?_⟩
  refine (SmallEtale.topology B S hS X.1).superset_covering ?_ (h.imageSieve_mem s)
  rintro V g ⟨t, ht⟩
  exact ⟨t, (pushforwardAlgebra_algebraMap_eq_structureSharp_app B S hS f _ t).trans ht⟩

/-- **For a closed immersion, the module underlying the direct-image algebra is the direct image of
the structure sheaf, under `𝒪_X`.** -/
def pushforwardAlgebraUnderlyingIso (f : Y ⟶ X) (hf : IsClosedImmersion B S hS f.hom) :
    (pushforwardAlgebra B S hS (Over.mk f)).underlyingModule ≅ structureSheafPushforward B S hS f :=
  isoOfEpiOfKerEq B S hS X _ (pushforwardStructureProjection B S hS f)
    (epi_unitToUnderlyingModule_pushforwardAlgebra B S hS f hf)
    (epi_pushforwardStructureProjection B S hS f hf)
    ((ker_unitToUnderlyingModule_pushforwardAlgebra B S hS f).trans
      (ker_pushforwardStructureProjection B S hS f).symm)

/-- The isomorphism carries the structure map of the algebra to the structure projection. -/
theorem unitToUnderlyingModule_comp_pushforwardAlgebraUnderlyingIso (f : Y ⟶ X)
    (hf : IsClosedImmersion B S hS f.hom) :
    AlgebraSheaf.unitToUnderlyingModule (pushforwardAlgebra B S hS (Over.mk f)) ≫
        (pushforwardAlgebraUnderlyingIso B S hS f hf).hom =
      pushforwardStructureProjection B S hS f :=
  comp_isoOfEpiOfKerEq_hom B S hS X _ _ _ _ _

end AlgebraicGeometry.Space

end
