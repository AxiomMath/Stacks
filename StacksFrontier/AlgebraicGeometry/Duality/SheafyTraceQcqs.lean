module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.AssociatedSheafComparison
public import StacksFrontier.AlgebraicGeometry.Duality.CompactGeneration.StandardModel
public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizingModule
public import StacksFrontier.AlgebraicGeometry.Duality.SheafyTrace
public import StacksFrontier.CategoryTheory.Sites.Cohomology.InternalHom.DerivedTensorHomBijectionNatural

/-!
# The sheafy trace map of a quasi-compact quasi-separated morphism

Let `f : X ⟶ Y` be a morphism of quasi-compact and quasi-separated schemes and let `a` be the right
adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of [Stacks, Tag 0A9E]. For `L` in `D_QCoh(𝒪_X)` and
`K` in `D_QCoh(𝒪_Y)` there is a canonical map, Equation 48.3.0.1 of [Stacks, Tag 0B6H],

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`,

the composition

`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, Rf_*a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`

of the map of [Stacks, Tag 0B69] and of `R𝓗om_{𝒪_Y}(Rf_*L, -)` applied to the counit
`Rf_*a(K) ⟶ K` of the adjunction.

## Main definitions

* `Stacks.Duality.qcqsSheafyTrace` — **Equation 48.3.0.1**: `Stacks.Duality.sheafyTrace` at the
  right adjoint `Stacks.Duality.twistedInverseImage` of [Stacks, Tag 0A9E], its adjunction
  `Stacks.Duality.twistedInverseImageAdjunction`, and the tensor–internal-Hom adjunction of
  [Stacks, Tag 08J8] on `D(𝒪_X)` and `D(𝒪_Y)`.

## Main results

* `Stacks.Duality.qcqsSheafyTrace_eq` — the trace map is the map of [Stacks, Tag 0B69] followed by
  the counit of `Rf_* ⊣ a`.

## Implementation notes

All derived categories are at `CategoryTheory.HasDerivedCategory.standard`, the model at which the
derived internal Hom of [Stacks, Tag 08DH], the map of [Stacks, Tag 0B69] and
`Stacks.Duality.sheafyTrace` are stated. At that model `Rf_*` carries `D_QCoh(𝒪_X)` into
`D_QCoh(𝒪_Y)` by `Stacks.Duality.StandardModel.isQuasicoherent_homology_derivedPushforward`
([Stacks, Tag 08D5]) and has a right adjoint by the instance
`Stacks.Duality.StandardModel.isLeftAdjoint_quasiCoherentDerivedPushforward`, which is
[Stacks, Tag 0A9E] transported from the locally small model.

## References

* [Stacks Project, Tag 0B6H](https://stacks.math.columbia.edu/tag/0B6H)
* [Stacks Project, Tag 0B69](https://stacks.math.columbia.edu/tag/0B69)
* [Stacks Project, Tag 0A9E](https://stacks.math.columbia.edu/tag/0A9E)
* [Stacks Project, Tag 08J8](https://stacks.math.columbia.edu/tag/08J8)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cohomology.ProjectionFormulaInternalHomOnRingedTopoi

universe u

namespace Stacks.Duality

-- `Stacks.Duality.sheafyTrace` is stated at the standard model.
attribute [local instance 10000] HasDerivedCategory.standard
attribute [local instance] Stacks.AssociatedSheaf.hasModuleSheafify
  Stacks.AssociatedSheaf.moduleSheafifyWEqualsLocallyBijective

variable {X Y : Scheme.{u}} (f : X ⟶ Y) [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace Y] [QuasiSeparatedSpace Y]

/-- **Equation 48.3.0.1 of [Stacks, Tag 0B6H].** Let `f : X ⟶ Y` be a morphism of quasi-compact
and quasi-separated schemes and `a` the right adjoint of `Rf_* : D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` of
[Stacks, Tag 0A9E]. For `L` in `D_QCoh(𝒪_X)` and `K` in `D_QCoh(𝒪_Y)`, the canonical map
`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, K)`: the map
`Rf_*R𝓗om_{𝒪_X}(L, a(K)) ⟶ R𝓗om_{𝒪_Y}(Rf_*L, Rf_*a(K))` of [Stacks, Tag 0B69], followed by
`R𝓗om_{𝒪_Y}(Rf_*L, -)` applied to the counit `Rf_*a(K) ⟶ K` of the adjunction. -/
@[stacks 0B6H]
def qcqsSheafyTrace (L : quasiCoherentDerivedCategory X) (K : quasiCoherentDerivedCategory Y) :
    (derivedPushforward f).obj
        (((Stacks.SheafOfModules.derivedSheafHom X.sheaf).obj (op L.obj)).obj
          ((twistedInverseImage f
            (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj K).obj) ⟶
      ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj
          (op ((derivedPushforward f).obj L.obj))).obj K.obj :=
  sheafyTrace f (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
    (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf))
    (StandardModel.isQuasicoherent_homology_derivedPushforward f)
    (twistedInverseImageAdjunction f (StandardModel.isQuasicoherent_homology_derivedPushforward f))
    L K

/-- **The trace map is that composition**: the map of [Stacks, Tag 0B69] at `L` and `a(K)`,
followed by `R𝓗om_{𝒪_Y}(Rf_*L, -)` of the counit `Rf_*a(K) ⟶ K` of `Rf_* ⊣ a`. -/
theorem qcqsSheafyTrace_eq (L : quasiCoherentDerivedCategory X)
    (K : quasiCoherentDerivedCategory Y) :
    qcqsSheafyTrace f L K =
      derivedSheafHomPushforward f
          (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite X.sheaf))
          (derivedTensorHomAdjunction (Stacks.SheafOfModules.ringedSite Y.sheaf)) L.obj
          ((twistedInverseImage f
            (StandardModel.isQuasicoherent_homology_derivedPushforward f)).obj K).obj ≫
        ((Stacks.SheafOfModules.derivedSheafHom Y.sheaf).obj
            (op ((derivedPushforward f).obj L.obj))).map
          ((ObjectProperty.ι _).map ((twistedInverseImageAdjunction f
            (StandardModel.isQuasicoherent_homology_derivedPushforward f)).counit.app K)) :=
  rfl

end Stacks.Duality

end
