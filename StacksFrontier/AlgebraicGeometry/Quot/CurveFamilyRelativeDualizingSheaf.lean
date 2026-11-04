module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackInvertible.RingedTopos
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePullback
public import StacksFrontier.AlgebraicGeometry.Quot.CurvesStable
public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.DualizingSheafDuality
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeAmple

/-!
# The relative dualizing sheaf of a family of curves: the defining property (towards Stacks 0E6R)

For a family of curves `f : X → S` with Gorenstein fibres equidimensional of dimension one — in
particular for a prestable family — Stacks 0E6Q and 0E6R produce the *relative dualizing sheaf*
`ω_{X/S}`: an invertible `𝒪_X`-module whose formation commutes with arbitrary base change, so that
its restriction to the fibre `X_s` over a point `s` of the base is the dualizing sheaf `ω_{X_s}` of
the proper curve `X_s` over `κ(s)` (Stacks 0BS2).

This file records that defining property of `ω_{X/S}` for a family of curves of this library, and
proves that it is inherited along base change. It is the interface through which the openness of
the stable locus (Stacks 0E74, 0E76) and the quasi-separatedness of `𝓜̄_g` consume the relative
dualizing sheaf.

## Main definitions

* `AlgebraicGeometry.CurveFamily.IsRelativeDualizingSheaf`: a module `ω` on the total space of a
  family of curves is invertible and, on every fibre over a field-valued point of the base, its
  pullback is the dualizing sheaf `Stacks.Duality.dualizingSheafOverField` of that fibre.

## Main results

* `AlgebraicGeometry.CurveFamily.IsRelativeDualizingSheaf.of_hom`: for a morphism of families of
  curves `a : F ⟶ G` (a base change), the pullback along the morphism of total spaces of a
  relative dualizing sheaf of `G` is a relative dualizing sheaf of `F`.

## Implementation notes

The fibre over a field-valued point `p` of the base is presented, as in
`AlgebraicGeometry.IsStableCurveFamily`, by a scheme `V` of the site over `Spec p.carrier` and a
cartesian square exhibiting `V` as the fibre product; the pullback of `ω` to `V` is
`AlgebraicGeometry.Space.baseChangeModule`, the module of Stacks 03LU read on the Zariski site of
`V`, which is the convention of relative ampleness (Stacks 0D31,
`AlgebraicGeometry.Space.IsRelativelyAmple`). The dualizing sheaf of a scheme over a field is
only defined for a proper one, so properness of the presentation is asserted inside the clause,
as for the rational-bridge condition of Stacks 0E75; it follows from properness of the family.

Invertibility is `Stacks.SheafOfModules.IsInvertible` on the small étale ringed site of the total
space, the form in which the openness of the relatively ample locus (Stacks 0D3D) takes its
module.

The existence of a relative dualizing sheaf for every prestable family (Stacks 0E6P, 0E6Q, 0E6R)
is not proved here.

## References

* [Stacks Project, Tag 0E6R](https://stacks.math.columbia.edu/tag/0E6R)
* [Stacks Project, Tag 0E6Q](https://stacks.math.columbia.edu/tag/0E6Q)
* [Stacks Project, Tag 0E6P](https://stacks.math.columbia.edu/tag/0E6P)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0D31](https://stacks.math.columbia.edu/tag/0D31)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable (B : BigFppfSite.{u}) (hZ : B.Contains integerBase)

namespace CurveFamily

/-- **The defining property of the relative dualizing sheaf `ω_{X/S}`** (Stacks 0E6Q, 0E6R).
A module `ω` on the total space of a family of curves `f : X → S` is a relative dualizing sheaf
when it is an invertible module on the small étale ringed site of `X` and its
formation is compatible with passing to the fibres: for every field-valued point `p` of `S` and
every scheme `V` presenting the fibre `X ×_S Spec p.carrier`, the presentation is proper over
`p.carrier` and the pullback of `ω` to `V` is the dualizing sheaf `ω_V` of Stacks 0BS2. -/
def IsRelativeDualizingSheaf (X : CurveFamily B hZ)
    (ω : Space.Modules.{u, u} B integerBase hZ X.total.1 X.total.2) : Prop :=
  Stacks.SheafOfModules.IsInvertible (Space.structurePresheaf B integerBase hZ X.total.1)
      ((Stacks.SheafOfModules.Tensor.ringSheaf
        (Space.smallEtaleRingedSite B integerBase hZ X.total.1 X.total.2).O)).property ω ∧
    ∀ (p : Space.FieldValuedPoint B integerBase hZ (schemeSpace X.base).obj)
      (V : BigFppfOver B integerBase hZ) (v : V ⟶ p.siteObject)
      (q : yoneda.obj V ⟶ X.total.obj),
      IsPullback q (yoneda.map v) X.toBase.hom (yonedaEquiv.symm p.value) →
        ∃ hproper : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v),
          letI : IsProper ((BigFppfOver.toScheme B integerBase hZ).map v) := hproper
          Nonempty (Space.baseChangeModule B integerBase hZ ω V q ≅
            Stacks.Duality.dualizingSheafOverField
              ((BigFppfOver.toScheme B integerBase hZ).map v))

variable {B hZ}

/-- **The relative dualizing sheaf is compatible with base change.** For a morphism of families of
curves `a : F ⟶ G`, that is a base change of `G` along the morphism of bases, the pullback along
the morphism of total spaces of a relative dualizing sheaf of `G` is a relative dualizing sheaf
of `F`. A scheme over the total space of `F` is one over the total space of `G`, and a
presentation of the fibre of `F` over a field-valued point is a presentation of the fibre of `G`
over its image, the square of the morphism of families being cartesian. -/
theorem IsRelativeDualizingSheaf.of_hom {F G : CurveFamily B hZ} (a : F ⟶ G)
    {ω : Space.Modules.{u, u} B integerBase hZ G.total.1 G.total.2}
    (hω : G.IsRelativeDualizingSheaf B hZ ω) :
    F.IsRelativeDualizingSheaf B hZ ((Space.modulePullback B integerBase hZ a.totalMap).obj ω) := by
  refine ⟨?_, fun p V v q hq => ?_⟩
  · exact Stacks.SheafOfModules.isInvertible_pullbackModules_obj
      (f := Space.smallEtaleRingedToposModulesHom B integerBase hZ a.totalMap) (L := ω) (hL := hω.1)
  have hsq := AlgebraicSpaces.isPullback_hom B integerBase hZ a.cartesian
  have hval : yonedaEquiv.symm (Space.FieldValuedPoint.map B integerBase hZ _
      (schemeSpaceMap a.baseMap).hom p).value =
        yonedaEquiv.symm p.value ≫ (schemeSpaceMap a.baseMap).hom :=
    (yonedaEquiv_symm_naturality_right _ _ _).symm
  have hq' : IsPullback (q ≫ a.totalMap.hom) (yoneda.map v) G.toBase.hom
      (yonedaEquiv.symm (Space.FieldValuedPoint.map B integerBase hZ _
        (schemeSpaceMap a.baseMap).hom p).value) :=
    (congrArg (fun t => IsPullback (q ≫ a.totalMap.hom) (yoneda.map v) G.toBase.hom t) hval).mpr
      (hq.paste_horiz hsq)
  obtain ⟨hproper, ⟨e⟩⟩ := hω.2 (Space.FieldValuedPoint.map B integerBase hZ _
    (schemeSpaceMap a.baseMap).hom p) V v _ hq'
  exact ⟨hproper, ⟨(Space.baseChangeModuleCompIso B integerBase hZ a.totalMap ω V q).symm ≪≫ e⟩⟩

end CurveFamily

end AlgebraicGeometry

end
