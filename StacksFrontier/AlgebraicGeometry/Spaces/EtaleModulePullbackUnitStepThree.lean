module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DirectImageRestrictScalars
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleModulePullbackUnitStepTwo

/-!
# The change-of-rings half of the unit, against the identification of Stacks 03LW

Let `f : X ⟶ Y` be an étale morphism of algebraic spaces over a scheme `S` contained in a big
fppf site `B`, and write `𝒱` for `CategoryTheory.Sheaf.moduleSheafFunctor`.  The pullback of
`𝒪_Y`-modules is `f^*M = 𝒪_X ⊗_{f⁻¹𝒪_Y} f⁻¹M`, and
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.pullbackScalarUnit` is its change-of-rings half
`x ↦ 1 ⊗ x`, a map `f⁻¹(𝒱M) ⟶ 𝒱(f^*M)` of sheaves of sets.  For an étale `f`, Stacks' Equation
03LW identifies `f^*M` with étale restriction, so composing with the underlying sheaf of sets of
that identification gives a map `f⁻¹(𝒱M) ⟶ M|_{X_étale}` — and it ought to be the comparison of
Stacks 03LQ, which is the canonical such map.

This file proves that.  It is **step 3** of the four-step comparison of the unit of étale
restriction of modules with the unit for sheaves of sets which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitComparison.lean` lay out; steps 1
and 4 are there, step 2 is in
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitStepTwo.lean`.

The obstruction that file records is precise: with the left-hand side already written as
`𝒱(unit ≫ (restrictScalars _).map _)` the statement *is* provable by
`CategoryTheory.Sheaf.hom_ext_sections` against
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app`; what is not affordable
is identifying that form with `pullbackScalarUnit _ _ ≫ 𝒱.map _`.  That identification is
nothing but `CategoryTheory.Functor.map_comp` together with the fact that restriction of scalars
does not change the underlying sheaf of sets, so it is proved below *at a general ringed topos*,
where no concrete sheaf has to be reduced, and instantiated afterwards.

## Main results

* `Stacks.Sheaves.GradedAlgebraEssentiallySmall.pullbackScalarUnit_comp_moduleSheafFunctor_map`:
  for a morphism of ringed topoi, the change-of-rings half of the unit followed by the
  underlying sheaf of sets of a morphism out of the pullback is the underlying sheaf of sets of
  the unit of extension of scalars followed by the restriction of scalars of that morphism.  It
  is `CategoryTheory.Functor.map_comp` and
  `Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_restrictScalars_map`, and it is the
  step the measurement above says has to happen at a general ringed topos.
* `moduleSheafFunctor_map_etaleModuleInverseImageIsoRestrictionTransport_hom_app`:
  the transport of modules of Stacks 03D2 along étale restriction is, on underlying sheaves of
  sets, the comparison of Stacks 03LQ.  It holds by `Eq.refl`, the transport being
  `Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso` at that comparison.
* `AlgebraicGeometry.Space.moduleSheafFunctor_map_extendScalarsFSharpAdjunction_unit_comp`: the
  unit of extension of scalars followed by the restriction of scalars of the identification of
  Stacks 03LW is that transport, on underlying sheaves of sets.  This is
  `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app` read off sections.
* `AlgebraicGeometry.Space.pullbackScalarUnit_comp_modulePullbackIsoEtaleModulePullback`:
  **step 3 — the change-of-rings half of the unit of Stacks 03LU, followed by the underlying
  sheaf of sets of the identification of Stacks 03LW, is the comparison of Stacks 03LQ.**

## Implementation notes

**Three spellings have to be kept apart, and each choice below is forced.**  The unit of
extension of scalars along the inverse-image form of the structure map has two names —
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.scalarAdjunction`, through which
`pullbackScalarUnit` is defined, and
`AlgebraicGeometry.Space.extendScalarsFSharpAdjunction`, through which
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app` is stated — and they are
definitionally equal but not interchangeable in a statement:
`AlgebraicGeometry.Space.moduleSheafFunctor_map_extendScalarsFSharpAdjunction_unit_comp` stated
with `scalarAdjunction` in place of `extendScalarsFSharpAdjunction` reports

`error: maximum recursion depth has been reached`

from `CategoryTheory.Sheaf.hom_ext_sections`, and raising that limit is not available here.  The
two are therefore bridged by
`AlgebraicGeometry.Space.scalarAdjunction_unit_app_eq_extendScalarsFSharpAdjunction_unit_app`, a
declaration whose whole content is `Eq.refl` and which has its own budget.  The same holds of
the inverse image of the structure sheaf: writing it as
`(smallEtaleRingedToposHom B S hS f).toRingedToposModulesHom.toToposHom` rather than as
`(smallEtaleRingedToposHom B S hS f).toToposHom` makes the same declaration reach `maxRecDepth`
as well.

The generic lemma is proved in term mode and not with `rw`: rewriting with
`CategoryTheory.Functor.map_comp` there leaves a goal the elaborator reports as *not type-correct
under the `implicit` transparency level*, because the rewrite unfolds
`AlgebraicGeometry.RingedToposHom.toRingedToposModulesHom` on one side of the composite and not
on the other.

Nothing here raises a compiler limit or disables a linter.

## What is not done

The four steps of the comparison are now all available, but **the comparison itself is not
assembled**, and what assembling it needs is two further identifications of vocabularies that
this file does not touch: that the direct image of sheaves of sets which step 1 produces,
`AlgebraicGeometry.Space.smallEtaleDirectImage`, is the direct image of the morphism of topoi
that `CategoryTheory.Adjunction.homEquiv_naturality_right` is stated for, and that the adjunction
`(smallEtaleRingedToposHom B S hS f).toToposHom.adj` of steps 2 and 3 is the adjunction
`(smallToposMorphismTypeU B S hS f).adj` of step 4.

## References

* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 03LV](https://stacks.math.columbia.edu/tag/03LV)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LQ](https://stacks.math.columbia.edu/tag/03LQ)
* [Stacks Project, Tag 03D2](https://stacks.math.columbia.edu/tag/03D2)
* [Stacks Project, Tag 03D7](https://stacks.math.columbia.edu/tag/03D7)
* [Stacks Project, Tag 03M8](https://stacks.math.columbia.edu/tag/03M8)
-/

@[expose] public section

open CategoryTheory Opposite
open Stacks.Sheaves.ToposPullback Stacks.Sheaves.ToposPushforward
open Stacks.Sheaves.RingedToposModules
open Stacks.Sheaves.GradedAlgebraEssentiallySmall

namespace Stacks.Sheaves.GradedAlgebraEssentiallySmall

universe w v u₁

variable {X Y : AlgebraicGeometry.RingedTopos.{v, u₁, w}}
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w})]
  [X.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [Y.J.HasSheafCompose (forget AddCommGrpCat.{w})]
  [HasWeakSheafify X.J AddCommGrpCat.{w}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{w}]
  (f : AlgebraicGeometry.RingedToposHom X Y)

/-- **The change-of-rings half of the unit, followed by a morphism out of the pullback.**  For a
morphism `f` of ringed topoi, a sheaf of modules `M` on the target and a morphism
`ψ : f^*M ⟶ N` of sheaves of modules on the source,
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.pullbackScalarUnit` followed by the underlying
sheaf of sets of `ψ` is the underlying sheaf of sets of the unit of extension of scalars followed
by the restriction of scalars of `ψ`.

It is `CategoryTheory.Functor.map_comp` together with
`Stacks.Sheaves.RingedToposModules.moduleSheafFunctor_map_restrictScalars_map`, which says that
restriction of scalars acts on a morphism by the very same morphism of underlying sheaves of
sets.  It is stated at a general ringed topos deliberately: at the small étale ringed topos of an
algebraic space this identification is exactly the one which the implementation notes of
`StacksFrontier/AlgebraicGeometry/Spaces/EtaleModulePullbackUnitComparison.lean` record as
unaffordable. -/
theorem pullbackScalarUnit_comp_moduleSheafFunctor_map
    (M : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))
    {N : SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
    (ψ : f.toRingedToposModulesHom.pullbackModules.obj M ⟶ N) :
    pullbackScalarUnit f M ≫
        (Sheaf.moduleSheafFunctor
          (Stacks.SheafOfModules.Tensor.ringSheaf X.O)).map ψ =
      (Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map
        ((scalarAdjunction f).unit.app
            ((inverseImageModules f.toToposHom
              (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)).obj M) ≫
          (SheafOfModules.restrictScalars
            f.toRingedToposModulesHom.fSharpInverseImage).map ψ) :=
  (((Sheaf.moduleSheafFunctor
          (inverseImageRingSheaf f.toToposHom
            (Stacks.SheafOfModules.Tensor.ringSheaf Y.O))).map_comp _ _).trans
      (congrArg (fun k ↦ pullbackScalarUnit f M ≫ k)
        (moduleSheafFunctor_map_restrictScalars_map
          f.toRingedToposModulesHom.fSharpInverseImage ψ))).symm

end Stacks.Sheaves.GradedAlgebraEssentiallySmall

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) (hf : IsEtale B S hS f.hom)

include hf

/-- **The transport of modules along étale restriction is the comparison of Stacks 03LQ on
underlying sheaves of sets.**
`AlgebraicGeometry.Space.etaleModuleInverseImageIsoRestrictionTransport` is
`Stacks.Sheaves.ToposPullback.pullbackModuleFunctorIsoOfNatIso` at the comparison
`AlgebraicGeometry.Space.smallToposMorphismTypeU_inverseImageIso` of Stacks 03LQ, and the
underlying morphism of sheaves of sets of the transport is that comparison by construction; so
this holds by `Eq.refl`. -/
theorem moduleSheafFunctor_map_etaleModuleInverseImageIsoRestrictionTransport_hom_app
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS Y))).map
        ((etaleModuleInverseImageIsoRestrictionTransport B S hS f hf).hom.app M) =
      (smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
        (moduleSetSheaf B S hS Y M) := rfl

omit hf in
/-- The two names of the unit of extension of scalars along the inverse-image form of the
structure map of Stacks 03G8 — `Stacks.Sheaves.GradedAlgebraEssentiallySmall.scalarAdjunction`,
through which `Stacks.Sheaves.GradedAlgebraEssentiallySmall.pullbackScalarUnit` is defined, and
`AlgebraicGeometry.Space.extendScalarsFSharpAdjunction`, through which
`AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app` is stated — agree at the
inverse image of a module.  It holds by `Eq.refl`.

It is a declaration of its own because the two are *not* interchangeable inside the statement of
`AlgebraicGeometry.Space.moduleSheafFunctor_map_extendScalarsFSharpAdjunction_unit_comp`; see
this file's implementation notes. -/
theorem scalarAdjunction_unit_app_eq_extendScalarsFSharpAdjunction_unit_app
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (scalarAdjunction (smallEtaleRingedToposHom B S hS f)).unit.app
        ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj M) =
      (extendScalarsFSharpAdjunction B S hS f).unit.app
        ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom
          (structureRingSheaf B S hS Y)).obj M) := rfl

/-- The unit of extension of scalars followed by the restriction of scalars of the
identification of Stacks 03LW is, on underlying sheaves of sets, the transport of modules along
étale restriction.

This is `AlgebraicGeometry.Space.modulePullbackIsoEtaleModulePullback_unit_app`, which is the
same statement on each section, read off sections by
`CategoryTheory.Sheaf.hom_ext_sections`. -/
theorem moduleSheafFunctor_map_extendScalarsFSharpAdjunction_unit_comp
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    (Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS Y))).map
        ((extendScalarsFSharpAdjunction B S hS f).unit.app
            ((inverseImageModules.{u, u, u, u + 1, u, u + 1}
              (smallEtaleRingedToposHom B S hS f).toToposHom
              (structureRingSheaf B S hS Y)).obj M) ≫
          (SheafOfModules.restrictScalars
            (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map
              ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M)) =
      (Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
          (smallEtaleRingedToposHom B S hS f).toToposHom (structureRingSheaf B S hS Y))).map
        ((etaleModuleInverseImageIsoRestrictionTransport B S hS f hf).hom.app M) :=
  CategoryTheory.Sheaf.hom_ext_sections (fun U s =>
    modulePullbackIsoEtaleModulePullback_unit_app B S hS f hf M U s)

/-- **Step 3 of the comparison of the two units: the change-of-rings half of the unit of
Stacks 03LU, followed by the underlying sheaf of sets of the identification of Stacks 03LW, is
the comparison of Stacks 03LQ.**  For an étale `f : X ⟶ Y` and an `𝒪_Y`-module `M`, the map
`x ↦ 1 ⊗ x` from the inverse image of `M` to the pullback `f^*M`, followed by the sheaf of sets
underlying the identification `f^*M = M|_{X_étale}` of Stacks' Equation 03LW, is the canonical
comparison `f⁻¹(𝒱M) ⟶ (𝒱M)|_{X_étale}` of Stacks 03LQ.

So the identification of Stacks 03LW introduces no twist on the change-of-rings half either:
together with
`AlgebraicGeometry.Space.moduleSheafFunctor_map_modulePullbackAdjunction_unit_app` it says that
the unit of étale restriction of modules is, on underlying sheaves of sets, the transpose of the
comparison of Stacks 03LQ.

It is the generic
`Stacks.Sheaves.GradedAlgebraEssentiallySmall.pullbackScalarUnit_comp_moduleSheafFunctor_map`,
followed by the two readings above; the bridge between the two names of the unit of extension of
scalars is
`AlgebraicGeometry.Space.scalarAdjunction_unit_app_eq_extendScalarsFSharpAdjunction_unit_app`. -/
theorem pullbackScalarUnit_comp_modulePullbackIsoEtaleModulePullback
    (M : Modules.{u, u} B S hS Y.1 Y.2) :
    pullbackScalarUnit (smallEtaleRingedToposHom B S hS f) M ≫
        (Sheaf.moduleSheafFunctor (structureRingSheaf B S hS X)).map
          ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M) =
      (smallToposMorphismTypeU_inverseImageIso B S hS f hf).hom.app
        (moduleSetSheaf B S hS Y M) :=
  (((pullbackScalarUnit_comp_moduleSheafFunctor_map (smallEtaleRingedToposHom B S hS f) M
        ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M)).trans
      (congrArg
        (fun a ↦ (Sheaf.moduleSheafFunctor (inverseImageRingSheaf.{u, u, u, u + 1, u, u + 1}
              (smallEtaleRingedToposHom B S hS f).toToposHom
              (structureRingSheaf B S hS Y))).map
            (a ≫ (SheafOfModules.restrictScalars
              (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage).map
                ((modulePullbackIsoEtaleModulePullback B S hS f hf).hom.app M)))
        (scalarAdjunction_unit_app_eq_extendScalarsFSharpAdjunction_unit_app B S hS f
          M))).trans
      (moduleSheafFunctor_map_extendScalarsFSharpAdjunction_unit_comp B S hS f hf M)).trans
    (moduleSheafFunctor_map_etaleModuleInverseImageIsoRestrictionTransport_hom_app B S hS f hf M)

end AlgebraicGeometry.Space

end
