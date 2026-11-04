module

public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentDerivedEtaleLocal
import StacksCore.Tactic.StacksAttribute

/-!
# Étale derived pullback preserves the quasi-coherent derived category of an algebraic space

Let `X` be an algebraic space over a scheme `S` contained in a big fppf site `B` and let
`f : Y ⟶ X` be an étale morphism of algebraic spaces over `S`.  Then `Lf^*` sends `D_QCoh(𝒪_X)`
into `D_QCoh(𝒪_Y)`, and so restricts to a functor `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`.

## Main results

* `AlgebraicGeometry.Space.derivedQuasicoherent_etaleModulePullback`: **Stacks 08F4 for étale
  morphisms of algebraic spaces**, on objects.
* `AlgebraicGeometry.Space.quasicoherentDerivedEtalePullback`: the resulting functor
  `D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)`, and
  `AlgebraicGeometry.Space.quasicoherentDerivedEtalePullbackCompιIso` its compatibility with the
  inclusions into the two unbounded derived categories.

## Implementation notes

An étale pullback of `𝒪`-modules is restriction of sections along
`AlgebraicGeometry.Space.smallEtalePostcomp` and so is exact, hence the functor it induces on
derived categories is already its total left derived functor; `Lf^*` is therefore
`CategoryTheory.Functor.mapDerivedCategory` of
`AlgebraicGeometry.Space.etaleModulePullback`, as in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasicoherentDerivedEtaleLocal.lean`.  Exactness is also
what makes the proof immediate from Stacks 03M0: `Hⁿ(Lf^*E) ≅ f^*(HⁿE)` by
`AlgebraicGeometry.Space.derivedQuasicoherentPullback_iff`, and `f^*` preserves quasi-coherence
of a single module by `AlgebraicGeometry.Space.isQuasicoherentOnSite_etaleModulePullback`.

**The restriction to étale morphisms is not an artefact of this proof.**  For a general morphism
`f : Y ⟶ X` of algebraic spaces the development has neither of the two inputs Stacks 08F4 needs.
First, there is no total left derived functor of
`AlgebraicGeometry.Space.modulePullback`: a left derived functor needs a resolving class, and the
K-flat complexes with flat terms of Stacks 06YS are supplied by
`Stacks.SheafOfModules.KFlatResolution.exists_kFlatResolution`, which asks for
`CategoryTheory.SmallCategory` of the site, whereas
`AlgebraicGeometry.Space.smallEtaleRingedSite` is an `AlgebraicGeometry.RingedSite.{u + 1, u, u}`.
Secondly, already on a single module, quasi-coherence is preserved by `f^*` only
conditionally here: `AlgebraicGeometry.Space.isQuasicoherentOnSite_modulePullback` carries
`AlgebraicGeometry.Space.HasLocalInverseImagePresentations`, the inverse-image factor of the
quasi-coherent clause of Stacks 03DO.  Both are available for an étale `f`, where the pullback is
a restriction and needs no resolving class and no comparison of structure sheaves.

No form of Stacks 08F5 is stated here.  The derived tensor product of `𝒪_X`-modules on an
algebraic space is not available: `Stacks.SheafOfModules.DerivedTensorProduct` is stated at the
universes of `AlgebraicGeometry.Space.smallEtaleRingedSite`, but every construction of an
inhabitant rests on the same Stacks 06YS resolutions, so none applies there.

## References

* [Stacks Project, Tag 08F4](https://stacks.math.columbia.edu/tag/08F4)
* [Stacks Project, Tag 08F5](https://stacks.math.columbia.edu/tag/08F5)
* [Stacks Project, Tag 08F2](https://stacks.math.columbia.edu/tag/08F2)
* [Stacks Project, Tag 08DW](https://stacks.math.columbia.edu/tag/08DW)
* [Stacks Project, Tag 03M0](https://stacks.math.columbia.edu/tag/03M0)
* [Stacks Project, Tag 071X](https://stacks.math.columbia.edu/tag/071X)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] HasDerivedCategory.standard

attribute [local instance] etaleModulePullback_additive
  preservesFiniteLimits_etaleModulePullback preservesFiniteColimits_etaleModulePullback

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : AlgebraicSpaces B S hS}

/-- **Stacks 08F4 for an étale morphism of algebraic spaces.**  If `E` is an object of `D(𝒪_X)`
all of whose cohomology sheaves are quasi-coherent and `f : Y ⟶ X` is étale, then every
cohomology sheaf of `Lf^*E` is quasi-coherent.

The étale pullback is exact, so `Hⁿ(Lf^*E) ≅ f^*(HⁿE)`, and `f^*` preserves quasi-coherence of a
module by the `(1) ⟹ (2)` direction of Stacks 03M0. -/
@[stacks 08F4 "for étale morphisms of algebraic spaces"]
theorem derivedQuasicoherent_etaleModulePullback (f : Y ⟶ X) (hf : IsEtale B S hS f.hom)
    (E : DerivedCategory (Modules.{u, u} B S hS X.1 X.2))
    (hE : DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))) E) :
    DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
        ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))
      ((etaleModulePullback B S hS f hf).mapDerivedCategory.obj E) :=
  (derivedQuasicoherentPullback_iff B S hS f hf E).2 fun n =>
    isQuasicoherentOnSite_etaleModulePullback B S hS f hf _ (hE n)

/-- **Stacks 08F4 for an étale morphism of algebraic spaces, as a functor.**  The derived
pullback along an étale morphism `f : Y ⟶ X` restricts to a functor
`D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)` between the derived categories of complexes with quasi-coherent
cohomology. -/
@[stacks 08F4 "for étale morphisms of algebraic spaces, the restriction D_QCoh(𝒪_X) ⥤ D_QCoh(𝒪_Y)"]
noncomputable def quasicoherentDerivedEtalePullback (f : Y ⟶ X) (hf : IsEtale B S hS f.hom) :
    QuasicoherentDerivedCategory.{u, u} B S hS X.1 X.2 ⥤
      QuasicoherentDerivedCategory.{u, u} B S hS Y.1 Y.2 :=
  ObjectProperty.lift _
    (ObjectProperty.ι _ ⋙ (etaleModulePullback B S hS f hf).mapDerivedCategory)
    fun K => derivedQuasicoherent_etaleModulePullback B S hS f hf K.obj K.property

/-- The restriction of `Lf^*` to the quasi-coherent derived categories is compatible with their
inclusions into the unbounded derived categories: `(restricted Lf^*) ⋙ ι ≅ ι ⋙ Lf^*`. -/
noncomputable def quasicoherentDerivedEtalePullbackCompιIso (f : Y ⟶ X)
    (hf : IsEtale B S hS f.hom) :
    quasicoherentDerivedEtalePullback B S hS f hf ⋙
        (DerivedCategoryB.derivedCategoryB
          (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
            ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O)))).ι ≅
      (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
          ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O)))).ι ⋙
        (etaleModulePullback B S hS f hf).mapDerivedCategory :=
  (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite.{u + 1, u, u, u}
      ((Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS Y.1 Y.2).O))))
    |>.liftCompιIso _ _

end AlgebraicGeometry.Space

end
