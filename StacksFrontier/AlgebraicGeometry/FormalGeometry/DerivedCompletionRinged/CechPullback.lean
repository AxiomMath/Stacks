module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulCechColimit
public import StacksFrontier.AlgebraicGeometry.FormalGeometry.DerivedCompletionRinged.KoszulPullback
public import StacksFrontier.Homology.KFlat.Flat

/-!
# The inverse image of an extended alternating Čech complex

Let `f : (Sh(𝒟), 𝒪') ⟶ (Sh(𝒞), 𝒪)` be a morphism of ringed sites, let `t_1, …, t_r` be global
sections of `𝒪` and let `g_1, …, g_r` be global sections of `𝒪'` with `g_i = f^♯(t_i)`. This file
identifies the degreewise inverse image of the extended alternating Čech complex on the `t_i`
with the extended alternating Čech complex on the `g_i`:

`f^*Č(𝒪, t_1, …, t_r) ≅ Č(𝒪', g_1, …, g_r)`.

The module documentation of `KoszulDualPushforwardTower.lean` recorded that nothing in the
library computed `f^*` on an away or Čech complex along a morphism of ringed sites; this file is
that computation.

## The argument

No away localization is ever pulled back by hand. The extended alternating Čech complex *is* the
colimit of the Koszul complexes on the positive powers,
`AlgebraicGeometry.RingedSite.isColimitKoszulCechComplexCocone` ([Stacks, Tag 0913] for sheaves
of modules on a ringed site), and the inverse image of sheaves of modules is a left adjoint, so
it preserves that colimit — degreewise on complexes, colimits of complexes being computed
degreewise (`CochainComplex.KFlat.preservesColimit_mapHomologicalComplex`). The inverse image of
the Koszul tower is the Koszul tower on the pushed-forward sections, which is
`AlgebraicGeometry.RingedSite.pullbackKoszulPowerSystemIso` of `KoszulPullback.lean`. Two
colimits of isomorphic diagrams have isomorphic points.

## Main definitions

* `AlgebraicGeometry.RingedSite.pullbackExtendedAlternatingCechIso`:
  **`f^*Č(t) ≅ Č(g)`**, as complexes of sheaves of `𝒪'`-modules.

## Main results

* `AlgebraicGeometry.RingedSite.pullbackExtendedAlternatingCechIso_hom_comp`: the identification
  carries the inverse image of the comparison `K(𝒪, t^{n+1}) ⟶ Č(𝒪, t)` out of the `n`-th Koszul
  complex to the comparison `K(𝒪', g^{n+1}) ⟶ Č(𝒪', g)`, which is what pins it down: it is the
  map the two colimit presentations produce.

## Implementation notes

*Which preservation statement.*
`AlgebraicGeometry.RingedSite.preservesColimitsOfShape_nat_pullbackTopos` is the
sequential-colimit preservation of `f^*`, read off the adjunction `f^* ⊣ f_*` of
`AlgebraicGeometry.RingedToposSiteHom.pullbackPushforwardAdjunctionTopos`; it is the shape `ℕ`
instance that `CochainComplex.KFlat.preservesColimit_mapHomologicalComplex` consumes.
`KoszulPullback.lean` already records the finite-product preservation that the degreewise
identification of the Koszul complexes needs; this is the colimit counterpart.

*No invertibility hypothesis.* The comparison `f^*𝒪 ⟶ 𝒪'` is invertible at every morphism of
ringed sites, by `AlgebraicGeometry.RingedSite.isIso_pullbackObjUnitToUnit_fSharpRing`, so
nothing beyond `f` and the relation `g_i = f^♯(t_i)` is assumed.

## References

* [Stacks Project, Tag 0913](https://stacks.math.columbia.edu/tag/0913)
* [Stacks Project, Tag 099B](https://stacks.math.columbia.edu/tag/099B)
* [Stacks Project, Tag 0A0G](https://stacks.math.columbia.edu/tag/0A0G)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry

universe u

namespace AlgebraicGeometry.RingedSite

attribute [local instance] AlgebraicGeometry.RingedSite.hasSheafCompose_forget₂_ringCat
attribute [local instance] hasFiniteBiproducts_sheafOfModules

section Preserves

variable {X Y : RingedSite.{u, u, u}}
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  (f : RingedSite.Hom X Y)

/-- **The inverse image of sheaves of modules preserves sequential colimits**, being a left
adjoint. This is the colimit counterpart of
`AlgebraicGeometry.RingedSite.preservesFiniteProducts_pullbackTopos`. -/
instance preservesColimitsOfShape_nat_pullbackTopos :
    PreservesColimitsOfShape ℕ f.toRingedToposSiteHom.pullbackTopos :=
  f.toRingedToposSiteHom.pullbackPushforwardAdjunctionTopos.leftAdjoint_preservesColimits
    |>.preservesColimitsOfShape

end Preserves

section Cech

variable {X Y : RingedSite.{u, u, u}}
  [HasWeakSheafify X.J AddCommGrpCat.{u}] [X.J.WEqualsLocallyBijective AddCommGrpCat.{u}]
  [HasWeakSheafify Y.J CommRingCat.{u}] [HasWeakSheafify X.J CommRingCat.{u}]
  (f : RingedSite.Hom X Y) {r : ℕ}
  (t : Fin r → Presheaf.globalSections (Y.O.obj ⋙ forget CommRingCat.{u}))
  (g : Fin r → Presheaf.globalSections (X.O.obj ⋙ forget CommRingCat.{u}))
  (hg : PushGlobalSectionsCompatible f t g)

/-- The inverse image, applied degreewise to complexes, preserves the sequential colimit of the
Koszul tower: colimits of complexes are computed degreewise. -/
instance preservesColimit_koszulPowerSystem_pullbackTopos :
    PreservesColimit (koszulPowerSystem Y t)
      (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)) :=
  CochainComplex.KFlat.preservesColimit_mapHomologicalComplex (koszulPowerSystem Y t)
    f.toRingedToposSiteHom.pullbackTopos

include hg in
/-- **`f^*Č(𝒪, t_1, …, t_r) ≅ Č(𝒪', g_1, …, g_r)`.** Both sides are colimits of the Koszul tower
on the source site: the left because the extended alternating Čech complex on the `t_i` is the
colimit of the Koszul complexes on their positive powers
(`AlgebraicGeometry.RingedSite.isColimitKoszulCechComplexCocone`) and `f^*` preserves that
colimit, the two towers being identified by
`AlgebraicGeometry.RingedSite.pullbackKoszulPowerSystemIso`; the right by the same presentation
on the source site. -/
def pullbackExtendedAlternatingCechIso :
    (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (extendedAlternatingCech Y t) ≅
      extendedAlternatingCech X g :=
  IsColimit.coconePointsIsoOfNatIso
    (isColimitOfPreserves
      (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ))
      (isColimitKoszulCechComplexCocone Y t))
    (isColimitKoszulCechComplexCocone X g)
    (pullbackKoszulPowerSystemIso f t g hg)

include hg in
/-- **The identification is the map the two colimit presentations produce**: it carries the
inverse image of the comparison `K(𝒪, t^{n+1}) ⟶ Č(𝒪, t)` to the comparison
`K(𝒪', g^{n+1}) ⟶ Č(𝒪', g)`, for every `n`. -/
theorem pullbackExtendedAlternatingCechIso_hom_comp (n : ℕ) :
    (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).map
          (koszulCechComplexMap Y t n) ≫
        (pullbackExtendedAlternatingCechIso f t g hg).hom =
      (pullbackKoszulPowerSystemIso f t g hg).hom.app n ≫ koszulCechComplexMap X g n :=
  IsColimit.comp_coconePointsIsoOfNatIso_hom
    (isColimitOfPreserves
      (f.toRingedToposSiteHom.pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ))
      (isColimitKoszulCechComplexCocone Y t))
    (isColimitKoszulCechComplexCocone X g)
    (pullbackKoszulPowerSystemIso f t g hg) n

end Cech

end AlgebraicGeometry.RingedSite

end
