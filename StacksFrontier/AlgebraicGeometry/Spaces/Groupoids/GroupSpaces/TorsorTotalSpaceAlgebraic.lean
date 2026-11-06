module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupSpaces.TorsorEffectiveDescentReduction
public import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.SeparatedQuasiFiniteDescent
import StacksFrontier.AlgebraicGeometry.Size.OpenCover
import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartFppfDescent
import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover
import StacksFrontier.AlgebraicGeometry.Spaces.FppfSectionOfLocallySurjective
import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.QuotientStackSquares.IsomorphismSheafAlgebraic
import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Properties
import StacksFrontier.AlgebraicGeometry.Spaces.Representable.Bootstrap.Stability
import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints

/-!
# The total space of a torsor of sheaves is an algebraic space, granted the bootstrap theorem

Granted Stacks 04S6 part (3), every `𝒢/ℬ`-torsor sheaf has an algebraic space as total space.
By `FppfTorsors.nonempty_isEquivalenceOver_comparison_iff_isAlgebraicSpace_total` this gives
Stacks 04UT, and it gives the effectivity of descent for `G`-torsors in Stacks 04US.

## Main results

* `AlgebraicGeometry.Space.isAlgebraicSpace_of_section_cover`: granted Stacks 04S6 part (3), a
  sheaf over `h_U` whose base change along a flat, locally finitely presented, surjective
  morphism `V ⟶ U` of the site is an algebraic space is an algebraic space.
* `AlgebraicGeometry.Space.FppfTorsors.isAlgebraicSpace_total_of_bootstrap`: granted Stacks 04S6
  part (3), every `𝒢/ℬ`-torsor sheaf has an algebraic space as total space.
* `AlgebraicGeometry.Space.FppfTorsors.nonempty_isEquivalenceOver_comparison_of_bootstrap`:
  granted Stacks 04S6 part (3), the comparison functor `G-Torsors ⥤ 𝒢/ℬ-Torsors` is an
  equivalence over the big fppf site (Stacks 04UT).
* `AlgebraicGeometry.Space.FppfTorsors.hasEffectiveDescent_projection_of_bootstrap`: granted
  Stacks 04S6 part (3) and effectivity of descent for `𝒢/ℬ`-torsors, condition (3) of Stacks
  02ZI for `p : G-Torsors ⥤ (Sch/S)_fppf`.

## References

* [Stacks Project, Tag 04UT](https://stacks.math.columbia.edu/tag/04UT)
* [Stacks Project, Tag 04US](https://stacks.math.columbia.edu/tag/04US)
* [Stacks Project, Tag 04U1](https://stacks.math.columbia.edu/tag/04U1)
* [Stacks Project, Tag 04S6](https://stacks.math.columbia.edu/tag/04S6)
* [Stacks Project, Tag 0499](https://stacks.math.columbia.edu/tag/0499)
* [Stacks Project, Tag 000X](https://stacks.math.columbia.edu/tag/000X)
* [Stacks Project, Tag 02ZI](https://stacks.math.columbia.edu/tag/02ZI)
* [Stacks Project, Tag 046F](https://stacks.math.columbia.edu/tag/046F)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {𝒞 : BigFppfSite.{u}} {S : Scheme.{u}} {hS : 𝒞.Contains S}

/-! ### Algebraicity along a flat, locally finitely presented surjection -/

/-- A morphism of algebraic spaces over `S` with a base-change-stable property `P` has `P` in
the sense of `AlgebraicGeometry.Space.HasProperty`: it has `P` after every base change along a
scheme-valued point of its target. -/
theorem hasProperty_of_space_hom' (P : MorphismProperty (AlgebraicSpaces 𝒞 S hS))
    [P.IsStableUnderBaseChange] {Y Z : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace 𝒞 S hS Y) (hZ : IsAlgebraicSpace 𝒞 S hS Z) (φ : Y ⟶ Z)
    (hφ : P (ObjectProperty.homMk φ :
      (⟨Y, hY⟩ : AlgebraicSpaces 𝒞 S hS) ⟶ (⟨Z, hZ⟩ : AlgebraicSpaces 𝒞 S hS))) :
    HasProperty 𝒞 S hS P φ
      (isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace 𝒞 S hS hY hZ φ) := fun U ξ ↦
  MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (AlgebraicSpaces.isPullback_fiberProduct 𝒞 S hS
      (ObjectProperty.homMk ξ : (⟨yoneda.obj U, isAlgebraicSpace_yoneda 𝒞 S hS U⟩ :
        AlgebraicSpaces 𝒞 S hS) ⟶ ⟨Z, hZ⟩)
      (ObjectProperty.homMk φ :
        (⟨Y, hY⟩ : AlgebraicSpaces 𝒞 S hS) ⟶ ⟨Z, hZ⟩)).flip hφ

/-- Granted Stacks 04S6 part (3), a sheaf `Y` over a representable `h_U` whose base change along
a flat, locally finitely presented, surjective morphism `k : V ⟶ U` of the site is an algebraic
space is itself an algebraic space. -/
theorem isAlgebraicSpace_of_section_cover
    (hbootstrap : IsBootstrapAlgebraicSpaceAlongFlatSurjection 𝒞 S hS)
    {Y Z : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {U V : BigFppfOver 𝒞 S hS} (k : V ⟶ U)
    {aY : Y ⟶ yoneda.obj U} {aZ : Z ⟶ yoneda.obj V} {g : Z ⟶ Y}
    (hsq : IsPullback g aZ aY (yoneda.map k))
    (hY : Presheaf.IsSheaf (BigFppfOver.topology 𝒞 S hS) Y)
    (hZ : IsAlgebraicSpace 𝒞 S hS Z)
    (hkFlat : Flat ((BigFppfOver.toScheme 𝒞 S hS).map k))
    (hkLfp : LocallyOfFinitePresentation ((BigFppfOver.toScheme 𝒞 S hS).map k))
    (hkSurj : Surjective ((BigFppfOver.toScheme 𝒞 S hS).map k)) :
    IsAlgebraicSpace 𝒞 S hS Y := by
  have hVa : IsAlgebraicSpace 𝒞 S hS (yoneda.obj V) := isAlgebraicSpace_yoneda 𝒞 S hS V
  have hUa : IsAlgebraicSpace 𝒞 S hS (yoneda.obj U) := isAlgebraicSpace_yoneda 𝒞 S hS U
  have hyFlat : IsFlat 𝒞 S hS (yoneda.map k) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff 𝒞 S hS
      AlgebraicGeometry.Flat.isEtaleLocalOnSourceAndTarget k).mpr hkFlat
  have hyLfp : IsLocallyOfFinitePresentation 𝒞 S hS (yoneda.map k) :=
    (holdsOnEveryEtaleChart_yoneda_map_iff 𝒞 S hS
      AlgebraicGeometry.LocallyOfFinitePresentation.isEtaleLocalOnSourceAndTarget k).mpr hkLfp
  have hySurj : IsSurjective 𝒞 S hS (yoneda.map k) :=
    isSurjective_of_presheafSurjective 𝒞 S hS _
      (presheaf_yoneda_map_of_inverseImage 𝒞 S hS
        (inferInstance : MorphismProperty.IsStableUnderBaseChange (@Surjective.{u}))
        k hkSurj)
  have hrepk : IsRepresentableByAlgebraicSpaces 𝒞 S hS (yoneda.map k) :=
    isRepresentableByAlgebraicSpaces_of_isAlgebraicSpace 𝒞 S hS hVa hUa (yoneda.map k)
  have hrepg : IsRepresentableByAlgebraicSpaces 𝒞 S hS g :=
    isRepresentableByAlgebraicSpaces_of_isPullback 𝒞 S hS aZ g (yoneda.map k) aY hsq.flip hrepk
  have key : ∀ (P : MorphismProperty (AlgebraicSpaces 𝒞 S hS)) [P.IsStableUnderBaseChange],
      P (ObjectProperty.homMk (yoneda.map k) : (⟨yoneda.obj V, hVa⟩ : AlgebraicSpaces 𝒞 S hS) ⟶
        (⟨yoneda.obj U, hUa⟩ : AlgebraicSpaces 𝒞 S hS)) → HasProperty 𝒞 S hS P g hrepg :=
    fun P _ h ↦ hasProperty_of_isPullback 𝒞 S hS P aZ g (yoneda.map k) aY hsq.flip hrepk
      (hasProperty_of_space_hom' P hVa hUa (yoneda.map k) h)
  exact hbootstrap g hY hZ hrepg (key _ hySurj) (key _ hyFlat) (key _ hyLfp)

/-! ### Algebraicity of the total space of a torsor of sheaves -/

namespace FppfTorsors

variable {B : (BigFppfOver 𝒞 S hS)ᵒᵖ ⥤ Type u} {hB : IsAlgebraicSpace 𝒞 S hS B}
  {G : GroupAlgebraicSpace 𝒞 S hS B hB}

/-- Granted Stacks 04S6 part (3), every `𝒢/ℬ`-torsor sheaf has an algebraic space as total
space. -/
theorem isAlgebraicSpace_total_of_bootstrap (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (hbootstrap : IsBootstrapAlgebraicSpaceAlongFlatSurjection 𝒞 S hS)
    (T : SheafTorsors G.obj) :
    IsAlgebraicSpace 𝒞 S hS T.total.left := by
  let : (SheafTorsors.projection G.obj).IsFibered :=
    (SheafTorsors.projection_isFiberedInGroupoids G.obj).isFibered
  obtain ⟨V, f, s, hsa, hfFlat, hfLfp, hfSurj⟩ :=
    AlgebraicGeometry.Space.exists_fppf_section T.isSheaf T.total.hom T.isLocallySurjective
  have hTb : (SheafTorsors.projection G.obj).obj T = T.base := rfl
  set Rpt := Functor.IsPreFibered.pullbackObj (p := SheafTorsors.projection G.obj) hTb f
    with hRptDef
  have hRb : Rpt.base = V := Functor.IsPreFibered.pullbackObj_proj hTb f
  set φ : Rpt ⟶ T := Functor.IsPreFibered.pullbackMap (p := SheafTorsors.projection G.obj) hTb f
    with hφ
  have hbase : SheafTorsors.Hom.base φ = eqToHom hRb ≫ f :=
    IsHomLift.fac' (SheafTorsors.projection G.obj) f φ
  have hsx : (yoneda.map (eqToHom hRb) ≫ s) ≫ T.total.hom =
      𝟙 (yoneda.obj Rpt.base) ≫ yoneda.map (SheafTorsors.Hom.base φ) := by
    rw [Category.assoc, hsa, ← Functor.map_comp, hbase, Category.id_comp]
  set sec : yoneda.obj Rpt.base ⟶ Rpt.total.left :=
    (SheafTorsors.Hom.isPullback φ).lift (yoneda.map (eqToHom hRb) ≫ s)
      (𝟙 (yoneda.obj Rpt.base)) hsx with hsecDef
  have hw : sec ≫ Rpt.total.hom = 𝟙 (yoneda.obj Rpt.base) :=
    (SheafTorsors.Hom.isPullback φ).lift_snd _ _ hsx
  have hRalg : IsAlgebraicSpace 𝒞 S hS Rpt.total.left :=
    isAlgebraicSpace_total_of_section (hB := hB) (G := G) Rpt
      (Over.homMk sec (by exact hw))
  have hiso : IsIso ((BigFppfOver.toScheme 𝒞 S hS).map (eqToHom hRb)) := by
    rw [eqToHom_map]; infer_instance
  have hcomp : (BigFppfOver.toScheme 𝒞 S hS).map (SheafTorsors.Hom.base φ) =
      (BigFppfOver.toScheme 𝒞 S hS).map (eqToHom hRb) ≫
        (BigFppfOver.toScheme 𝒞 S hS).map f := by
    rw [← Functor.map_comp, hbase]
  have key : ∀ {P : MorphismProperty Scheme.{u}}, P.RespectsIso →
      P ((BigFppfOver.toScheme 𝒞 S hS).map f) →
      P ((BigFppfOver.toScheme 𝒞 S hS).map (SheafTorsors.Hom.base φ)) := fun hP h ↦ by
    rw [hcomp]
    exact (MorphismProperty.cancel_left_of_respectsIso _ _ _).mpr h
  exact isAlgebraicSpace_of_section_cover hbootstrap (SheafTorsors.Hom.base φ)
    (SheafTorsors.Hom.isPullback φ) T.isSheaf hRalg
    (key Flat.isStableUnderBaseChange.respectsIso hfFlat)
    (key locallyOfFinitePresentation_isStableUnderBaseChange.respectsIso hfLfp)
    (key (inferInstance : MorphismProperty.IsStableUnderBaseChange (@Surjective.{u})).respectsIso
      hfSurj)

/-- Granted Stacks 04S6 part (3), the comparison functor `G-Torsors ⥤ 𝒢/ℬ-Torsors` is an
equivalence of stacks in groupoids over the big fppf site of `S`. -/
theorem nonempty_isEquivalenceOver_comparison_of_bootstrap (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (hbootstrap : IsBootstrapAlgebraicSpaceAlongFlatSurjection 𝒞 S hS) :
    Nonempty (Functor.IsEquivalenceOver (projection hB G) (SheafTorsors.projection G.obj)
      (comparison hB G)) :=
  (nonempty_isEquivalenceOver_comparison_iff_isAlgebraicSpace_total hB G).mpr
    (isAlgebraicSpace_total_of_bootstrap hB G hbootstrap)

/-- Granted Stacks 04S6 part (3) and effectivity of descent for `𝒢/ℬ`-torsors (`htarget`,
condition (3) of Stacks 04UM), descent data for `p : G-Torsors ⥤ (Sch/S)_fppf` are effective:
condition (3) of Stacks 02ZI. -/
theorem hasEffectiveDescent_projection_of_bootstrap (hB : IsAlgebraicSpace 𝒞 S hS B)
    (G : GroupAlgebraicSpace 𝒞 S hS B hB)
    (hbootstrap : IsBootstrapAlgebraicSpaceAlongFlatSurjection 𝒞 S hS)
    (htarget : letI : (SheafTorsors.projection G.obj).IsFibered :=
        (SheafTorsors.projection_isFiberedInGroupoids G.obj).isFibered
      Functor.HasEffectiveDescent (SheafTorsors.projection G.obj)
        (BigFppfOver.topology 𝒞 S hS)) :
    letI : (projection hB G).IsFibered :=
      (projection_isFiberedInGroupoids (hB := hB) (G := G)).isFibered
    Functor.HasEffectiveDescent (projection hB G) (BigFppfOver.topology 𝒞 S hS) :=
  hasEffectiveDescent_projection_of_isAlgebraicSpace_total hB G htarget
    (isAlgebraicSpace_total_of_bootstrap hB G hbootstrap)

end FppfTorsors

end AlgebraicGeometry.Space

end
