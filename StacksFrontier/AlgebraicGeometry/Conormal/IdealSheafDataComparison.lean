module

public import StacksFrontier.AlgebraicGeometry.Conormal.QuotientFactorization
public import StacksFrontier.AlgebraicGeometry.ConormalUnitTransport.Basic
public import StacksFrontier.AlgebraicGeometry.Modules.ClosedSubschemeQuotient

/-!
# The sheaf of ideals of an `IdealSheafData` is the ideal sheaf of its closed immersion

Let `X` be a scheme and `I` a quasi-coherent sheaf of ideals on `X`, given as an
`AlgebraicGeometry.Scheme.IdealSheafData`. The submodule
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmodule` of the structure sheaf attached to `I` is
isomorphic to the ideal sheaf `Stacks.ClosedImmersion.idealSheaf` of the closed immersion
`I.subschemeι`, the kernel of `𝒪_X ⟶ ι_* 𝒪_{V(I)}`, compatibly with the inclusions of both into
the structure sheaf. The same holds for an arbitrary closed immersion of schemes `j : W ⟶ X` with
kernel `I`, and the inverse image along `j` of the submodule is the conormal sheaf of `j`.

## Main definitions

* `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmoduleIsoIdealSheaf`: the submodule of the
  structure sheaf attached to `I` is the ideal sheaf, in the sense of
  [Stacks Project, Tag 01C2], of the closed immersion `I.subschemeι`.
* `AlgebraicGeometry.Scheme.IdealSheafData.kerUnitSubmoduleIsoIdealSheaf`: the same for an
  arbitrary closed immersion of schemes: for `j : W ⟶ X` a closed immersion, the submodule
  attached to `j.ker` is the ideal sheaf of `j`.
* `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmoduleIsoIdealSheafOfKerEq`: the same with the
  sheaf of ideals given separately, through an equation `j.ker = I`.
* `AlgebraicGeometry.Scheme.IdealSheafData.modulePullbackUnitSubmoduleIsoConormalSheaf` and
  `AlgebraicGeometry.Scheme.IdealSheafData.modulePullbackKerUnitSubmoduleIsoConormalSheaf`: the
  inverse image of that submodule along the immersion is the conormal sheaf of
  [Stacks Project, Tag 01R2], in the spelling
  `Stacks.ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom` (with `j = I.subschemeι`
  for the first).
* `AlgebraicGeometry.Scheme.IdealSheafData.modulePullbackUnitSubmoduleIsoConormalSheafOfKerEq`:
  the last of those with the sheaf of ideals given separately, through an equation `j.ker = I`.

## Main results

* `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmoduleIsoIdealSheaf_hom_comp_idealSheafι` and
  `AlgebraicGeometry.Scheme.IdealSheafData.kerUnitSubmoduleIsoIdealSheaf_hom_comp_idealSheafι`:
  composed with the inclusion of the ideal sheaf into the structure sheaf, each identification is
  the inclusion of the submodule.
* `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmoduleIsoIdealSheafOfKerEq_hom_comp_idealSheafι`:
  the same with the sheaf of ideals given separately.

## References

* [Stacks Project, Tag 01C2](https://stacks.math.columbia.edu/tag/01C2), the ideal sheaf of a
  closed immersion of ringed spaces.
* [Stacks Project, Tag 01R2](https://stacks.math.columbia.edu/tag/01R2), the conormal sheaf.
* [Stacks Project, Tag 01R8](https://stacks.math.columbia.edu/tag/01R8), quasi-coherence of the
  ideal sheaf.
* [Stacks Project, Tag 01PQ](https://stacks.math.columbia.edu/tag/01PQ), the sectionwise kernel.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open RingedSpaceModuleAdjunction
open Stacks.Conormal.AffineCotangent.SourceTransport

universe u

namespace AlgebraicGeometry.Scheme.IdealSheafData

open _root_.AlgebraicGeometry.SheafOfModules.Submodule (asModules ιModules)

/-! ### The closed immersion the sheaf of ideals cuts out -/

variable {X : Scheme.{u}} (I : X.IdealSheafData)

/-- The submodule of the structure sheaf attached to a quasi-coherent sheaf of ideals `I` is
isomorphic to the ideal sheaf of the closed immersion `I.subschemeι` it cuts out. -/
def unitSubmoduleIsoIdealSheaf :
    asModules I.unitSubmodule ≅
      Stacks.ClosedImmersion.idealSheaf I.subschemeι.toLRSHom.toShHom :=
  Stacks.ClosedSubscheme.unitSubmoduleIsoKernel I

/-- Composed with the inclusion of the ideal sheaf into the structure sheaf of `X`,
`AlgebraicGeometry.Scheme.IdealSheafData.unitSubmoduleIsoIdealSheaf` is the inclusion of the
submodule. -/
theorem unitSubmoduleIsoIdealSheaf_hom_comp_idealSheafι :
    (unitSubmoduleIsoIdealSheaf I).hom ≫
        Stacks.ClosedImmersion.idealSheafι I.subschemeι.toLRSHom.toShHom =
      ιModules I.unitSubmodule :=
  SheafOfModules.Submodule.kernelIso_hom_comp_ι _

/-- The inverse image of the submodule attached to `I` along the closed immersion `I.subschemeι`
is the conormal sheaf of `I.subschemeι`, in the spelling
`Stacks.ClosedImmersion.conormalSheaf I.subschemeι.liftCoborder.toLRSHom.toShHom`. -/
def modulePullbackUnitSubmoduleIsoConormalSheaf :
    (modulePullback I.subschemeι.toLRSHom.toShHom).obj (asModules I.unitSubmodule) ≅
      Stacks.ClosedImmersion.conormalSheaf I.subschemeι.liftCoborder.toLRSHom.toShHom :=
  (modulePullback I.subschemeι.toLRSHom.toShHom).mapIso (unitSubmoduleIsoIdealSheaf I) ≪≫
    Stacks.Immersion.conormalSheafSelfIso I.subschemeι

/-! ### An arbitrary closed immersion of schemes -/

variable {W : Scheme.{u}} (j : W ⟶ X) [IsClosedImmersion j]

/-- For a closed immersion of schemes `j : W ⟶ X`, the submodule of the structure sheaf attached
to `j.ker` is isomorphic to the ideal sheaf of `j`. -/
def kerUnitSubmoduleIsoIdealSheaf :
    asModules j.ker.unitSubmodule ≅
      Stacks.ClosedImmersion.idealSheaf j.toLRSHom.toShHom :=
  unitSubmoduleIsoIdealSheaf j.ker ≪≫
    (idealSheafIsoOfIsoSourceOfCompEq (asIso j.toImage) j.ker.subschemeι j
      j.toImage_imageι).symm

/-- Composed with the inclusion of the ideal sheaf of `j` into the structure sheaf of `X`,
`AlgebraicGeometry.Scheme.IdealSheafData.kerUnitSubmoduleIsoIdealSheaf j` is the inclusion of the
submodule attached to `j.ker`. -/
theorem kerUnitSubmoduleIsoIdealSheaf_hom_comp_idealSheafι :
    (kerUnitSubmoduleIsoIdealSheaf j).hom ≫
        Stacks.ClosedImmersion.idealSheafι j.toLRSHom.toShHom =
      ιModules j.ker.unitSubmodule :=
  (Category.assoc _ _ _).trans
    ((congrArg ((unitSubmoduleIsoIdealSheaf j.ker).hom ≫ ·)
        (idealSheafIsoOfIsoSourceOfCompEq_inv_comp_ι (asIso j.toImage)
          j.ker.subschemeι j j.toImage_imageι)).trans
      (unitSubmoduleIsoIdealSheaf_hom_comp_idealSheafι j.ker))

/-- The inverse image along a closed immersion of schemes `j` of the submodule attached to `j.ker`
is the conormal sheaf of `j`, in the spelling
`Stacks.ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom`. -/
def modulePullbackKerUnitSubmoduleIsoConormalSheaf :
    (modulePullback j.toLRSHom.toShHom).obj (asModules j.ker.unitSubmodule) ≅
      Stacks.ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom :=
  (modulePullback j.toLRSHom.toShHom).mapIso (kerUnitSubmoduleIsoIdealSheaf j) ≪≫
    Stacks.Immersion.conormalSheafSelfIso j

/-- For a closed immersion of schemes `j : W ⟶ X` and a sheaf of ideals `I` with `j.ker = I`, the
submodule of the structure sheaf attached to `I` is isomorphic to the ideal sheaf of `j`. -/
def unitSubmoduleIsoIdealSheafOfKerEq (hj : j.ker = I) :
    asModules I.unitSubmodule ≅
      Stacks.ClosedImmersion.idealSheaf j.toLRSHom.toShHom := by
  subst hj
  exact kerUnitSubmoduleIsoIdealSheaf j

/-- For `j.ker = I`, composed with the inclusion of the ideal sheaf of `j` into the structure sheaf
of `X`, `AlgebraicGeometry.Scheme.IdealSheafData.unitSubmoduleIsoIdealSheafOfKerEq` is the
inclusion of the submodule attached to `I`. -/
theorem unitSubmoduleIsoIdealSheafOfKerEq_hom_comp_idealSheafι (hj : j.ker = I) :
    (unitSubmoduleIsoIdealSheafOfKerEq I j hj).hom ≫
        Stacks.ClosedImmersion.idealSheafι j.toLRSHom.toShHom =
      ιModules I.unitSubmodule := by
  subst hj
  exact kerUnitSubmoduleIsoIdealSheaf_hom_comp_idealSheafι j

/-- For a closed immersion of schemes `j : W ⟶ X` and a sheaf of ideals `I` with `j.ker = I`, the
inverse image along `j` of the submodule of the structure sheaf attached to `I` is the conormal
sheaf of `j`, in the spelling
`Stacks.ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom`. -/
def modulePullbackUnitSubmoduleIsoConormalSheafOfKerEq (hj : j.ker = I) :
    (modulePullback j.toLRSHom.toShHom).obj (asModules I.unitSubmodule) ≅
      Stacks.ClosedImmersion.conormalSheaf j.liftCoborder.toLRSHom.toShHom := by
  subst hj
  exact modulePullbackKerUnitSubmoduleIsoConormalSheaf j

end AlgebraicGeometry.Scheme.IdealSheafData

end
