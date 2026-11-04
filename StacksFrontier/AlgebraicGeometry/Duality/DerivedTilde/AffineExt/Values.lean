module

public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.QuasiIsoSections
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.ExtComparison
public import StacksFrontier.AlgebraicGeometry.DerivedGlobalSections
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedInternalHom

/-!
# The values of the `Ext` presheaf

Fix representatives of `K` and `L` by complexes of `R`-modules, and a K-injective resolution `I`
of the complex of sheaves associated to the representative of `L`. The internal Hom complex
from the sheafified representative of `K` into `I` computes `R𝓗om(K̃, L̃)`. Its complex of sections
over `D(f)` is the Hom complex of `R_f`-modules from the representative of `K ⊗ R_f` into the
sections of `I` over `D(f)`, which represent `L ⊗ R_f` and are K-injective; so its degree-`n`
cohomology is `Ext^n_{R_f}(K ⊗ R_f, L ⊗ R_f)`.

## Main definitions

* `AlgebraicGeometry.AffineExt.homModel`: the internal Hom complex.
* `AlgebraicGeometry.AffineExt.sectionHomologyEquiv`: the identification of the cohomology of its
  sections over `D(f)` with `Ext^n_{R_f}(K ⊗ R_f, L ⊗ R_f)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.AffineExt

attribute [local instance 10000] HasDerivedCategory.standard
    AlgebraicGeometry.tilde.preservesFiniteLimits
  Stacks.AffineTilde.preservesFiniteColimits_tildeFunctor

variable (R : CommRingCat.{u}) (K L : DerivedCategory (ModuleCat.{u} R))

/-- A complex of `R`-modules representing `K`. -/
def srcModel (R : CommRingCat.{u}) (K : DerivedCategory (ModuleCat.{u} R)) :
    CochainComplex (ModuleCat.{u} R) ℤ :=
  DerivedCategory.Q.objPreimage K

/-- The complex `srcModel R K` represents `K`. -/
def srcModelIso (R : CommRingCat.{u}) (K : DerivedCategory (ModuleCat.{u} R)) :
    DerivedCategory.Q.obj (srcModel R K) ≅ K :=
  DerivedCategory.Q.objObjPreimageIso K

/-- The complex of sheaves associated to `srcModel R L` admits a quasi-isomorphism into a
K-injective complex of sheaves. -/
lemma exists_resolution : ∃ (I : CochainComplex (Spec R).Modules ℤ)
    (s : ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj (srcModel R L) ⟶ I),
    I.IsKInjective ∧ QuasiIso s :=
  Scheme.Modules.exists_quasiIso_isKInjective (Spec R) _

/-- A K-injective resolution of the complex of sheaves associated to `srcModel R L`. -/
def resolution : CochainComplex (Spec R).Modules ℤ := (exists_resolution R L).choose

/-- The quasi-isomorphism from the complex of sheaves associated to `srcModel R L` into
`resolution R L`. -/
def resolutionMap :
    ((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj (srcModel R L) ⟶
      resolution R L :=
  (exists_resolution R L).choose_spec.choose

/-- The complex `resolution R L` is K-injective. -/
lemma isKInjective_resolution : (resolution R L).IsKInjective :=
  (exists_resolution R L).choose_spec.choose_spec.1

/-- The map `resolutionMap R L` is a quasi-isomorphism. -/
lemma quasiIso_resolutionMap : QuasiIso (resolutionMap R L) :=
  (exists_resolution R L).choose_spec.choose_spec.2

/-- Taking sections over `D(f)` sends `resolutionMap R L` to a quasi-isomorphism of complexes of
`Γ(Spec R, D(f))`-modules. -/
lemma quasiIsoSections (f : R) : QuasiIso (((sectionsS R (basicOpen R f)).mapHomologicalComplex
    (ComplexShape.up ℤ)).map (resolutionMap R L)) :=
  quasiIso_sectionsS_map R f (srcModel R L) (resolutionMap R L) (isKInjective_resolution R L)
    (quasiIso_resolutionMap R L)

/-- The internal Hom complex from the sheafified model of `K` into the resolution of `L̃`. -/
def homModel := RingedSite.sheafHomComplex (Stacks.SheafOfModules.ringedSite (Spec R).sheaf)
  (((tilde.functor R).mapHomologicalComplex (ComplexShape.up ℤ)).obj (srcModel R K))
  (resolution R L)

/-- The section complexes of the internal Hom complex over an open `U` are Hom complexes of
`R`-modules into the sections of the resolution. -/
def sectionComplexIso (U : (Spec R).Opens) :
    RingedSite.sectionComplex (Stacks.SheafOfModules.ringedSite (Spec R).sheaf) (homModel R K
        L).obj U ≅
      CochainComplex.HomComplex (srcModel R K)
        (((TildeSlice.sectionsR U).mapHomologicalComplex (ComplexShape.up ℤ)).obj (resolution R
            L)) :=
  (homModel R K L).sectionsIso U ≪≫ TildeSlice.homComplexTildeOverIso U (srcModel R K) (resolution
      R L)

/-- Over a principal open `D(f)` the section complexes of the internal Hom complex are Hom
complexes of `R_f`-modules. -/
def sectionComplexIsoS (f : R) :
    RingedSite.sectionComplex (Stacks.SheafOfModules.ringedSite (Spec R).sheaf) (homModel R K L).obj
        (basicOpen R f) ≅
      CochainComplex.HomComplex ((extC (locMap R f)).obj (srcModel R K))
        (((sectionsS R (basicOpen R f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (resolution R L)) :=
  sectionComplexIso R K L (basicOpen R f) ≪≫ adjHomComplexIso (locMap R f) (srcModel R K)
    (((sectionsS R (basicOpen R f)).mapHomologicalComplex (ComplexShape.up ℤ)).obj (resolution R L))

/-- The sheafified model of `K`, extended to `R_f`, represents `K ⊗ R_f`. -/
def srcExtIso (f : R) :
    DerivedCategory.Q.obj ((extC (locMap R f)).obj (srcModel R K)) ≅ (extD (locMap R f)).obj K :=
  ((ModuleCat.extendScalars.{u, u, u} (locMap R f).hom).mapDerivedCategoryFactors.app
    (srcModel R K)).symm ≪≫ (extD (locMap R f)).mapIso (srcModelIso R K)

/-- The sections over `D(f)` of the resolution of `L̃` represent `L ⊗ R_f`. -/
def tgtExtIso (f : R) :
    DerivedCategory.Q.obj (((sectionsS R (basicOpen R f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj (resolution R L)) ≅ (extD (locMap R f)).obj L :=
  haveI := quasiIsoSections R L f
  (asIso (DerivedCategory.Q.map (((sectionsS R (basicOpen R f)).mapHomologicalComplex
      (ComplexShape.up ℤ)).map (resolutionMap R L)))).symm ≪≫
    DerivedCategory.Q.mapIso ((NatIso.mapHomologicalComplex (tildeBasicOpenNatIso R f)
      (ComplexShape.up ℤ)).app (srcModel R L)).symm ≪≫
    ((ModuleCat.extendScalars.{u, u, u} (locMap R f).hom).mapDerivedCategoryFactors.app
      (srcModel R L)).symm ≪≫ (extD (locMap R f)).mapIso (srcModelIso R L)

/-- **The value of the `Ext` presheaf over `D(f)`.** The degree-`n` cohomology of the sections
over `D(f)` of the internal Hom complex is `Ext^n_{R_f}(K ⊗ R_f, L ⊗ R_f)`. -/
def sectionHomologyEquiv (f : R) (n : ℤ) :
    ((RingedSite.sectionComplex (Stacks.SheafOfModules.ringedSite (Spec R).sheaf)
      (homModel R K L).obj (basicOpen R f)).homology n : Type u) ≃+ localizedExt R K L f n :=
  haveI := isKInjective_sectionsS R f (resolution R L) (isKInjective_resolution R L)
  ((HomologicalComplex.homologyFunctor _ _ n).mapIso
      (sectionComplexIsoS R K L f)).addCommGroupIsoToAddEquiv.trans <|
    (CochainComplex.HomComplex.homologyAddEquivShiftedHom _ _ n).trans
      (Linear.homCongr ℤ (srcExtIso R K f) ((shiftFunctor _ n).mapIso (tgtExtIso R L f))).toAddEquiv

end AlgebraicGeometry.AffineExt
