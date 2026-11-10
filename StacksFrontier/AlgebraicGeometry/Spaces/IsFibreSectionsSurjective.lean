module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Finite
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Flat
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Surjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SectionSpacesOverBase
public import StacksFrontier.AlgebraicGeometry.Stacks.Criteria.RestrictionOfScalarsEtale

/-!
# The restriction of scalars of a surjective étale morphism is surjective over the base

Let `U` be an object of the big fppf site of `S`, let `ζ : Z_U ⟶ h_U` be a finite morphism of
algebraic spaces over `S` and let `w : W ⟶ Z_U` be surjective and étale. The projection
`Res_{Z_U/U}(W) ⟶ h_U` of the restriction of scalars of Stacks 05YA is then surjective.

This is what Stacks 05XQ supplies to the last assertion of Stacks 05YD. Surjectivity of a
morphism of algebraic spaces may be tested after base change by an affine object of the site, by
Stacks 03MF; over an affine object the finite morphism `ζ` is represented by an object `V` of
the site, by the definition of a finite morphism, and Stacks 05XQ over a base object —
`AlgebraicGeometry.Space.exists_surjective_etale_sectionOverBase` — produces a surjective étale
`r : T ⟶ T₀` over the affine test object together with a section of the base change of `w`
along `r`. That section is the second component of a pair of Stacks 05Y9 whose first component
is `r` followed by the given point of `U`, hence a scheme-valued point of `Res_{Z_U/U}(W)`
living over a surjective morphism to the test object.

## Main results

* `AlgebraicGeometry.Space.RestrictionPair.point_comp_projection`: the projection of the
  scheme-valued point of `Res_{Z/Q}(X)` determined by a pair is the pair's first component.
* `AlgebraicGeometry.Space.isSurjective_projection_restrictionOfScalars`: the projection
  `Res_{Z_U/U}(W) ⟶ h_U` of the restriction of scalars of a surjective étale `w` along a finite
  `ζ` is surjective.

## References

* [Stacks Project, Tag 03MF](https://stacks.math.columbia.edu/tag/03MF)
* [Stacks Project, Tag 05XQ](https://stacks.math.columbia.edu/tag/05XQ)
* [Stacks Project, Tag 05Y9](https://stacks.math.columbia.edu/tag/05Y9)
* [Stacks Project, Tag 05YA](https://stacks.math.columbia.edu/tag/05YA)
* [Stacks Project, Tag 05YD](https://stacks.math.columbia.edu/tag/05YD)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for `HasPullbacks` of presheaves on the big fppf site times out by default
/-- Pullbacks of presheaves on the big fppf site over `S` (instance search times out without
this shortcut). -/
private instance hasPullbacks_presheaf_isFibreSectionsSurjective :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) := inferInstance

private instance (priority := high) hasPullback_presheaf_isFibreSectionsSurjective
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  HasLimitsOfShape.has_limit _

/-- **The projection of the scheme-valued point determined by a pair is the pair's first
component.** This is `AlgebraicGeometry.Space.RestrictionOfScalarsConstruction`'s description of
the projection, read through the Yoneda lemma. -/
theorem RestrictionPair.point_comp_projection {X Z Q : AlgebraicSpaces B S hS} {x : X ⟶ Z}
    {z : Z ⟶ Q} {T : BigFppfOver B S hS} (p : RestrictionPair B S hS x z (yoneda.obj T)) :
    p.point ≫ (restrictionOfScalars B S hS x z).projection = p.base := by
  refine yonedaEquiv.injective ?_
  rw [yonedaEquiv_comp, RestrictionPair.point, Equiv.apply_symm_apply,
    (restrictionOfScalars B S hS x z).projection_pairEquiv T _, Equiv.apply_symm_apply]

/-- **The restriction of scalars of a surjective étale morphism along a finite morphism to a
representable base is surjective over that base.** Let `U` be an object of the big fppf site of
`S`, let `ζ : Z_U ⟶ h_U` be finite and let `w : W ⟶ Z_U` be surjective and étale. Then the
projection `Res_{Z_U/U}(W) ⟶ h_U` of Stacks 05YA is surjective.

Surjectivity is tested on base changes by affine objects of the site, Stacks 03MF; over such an
object `ζ` is represented, and Stacks 05XQ over a base object supplies a section after a
surjective étale base change. -/
theorem isSurjective_projection_restrictionOfScalars {ZU W : AlgebraicSpaces B S hS}
    {U : BigFppfOver B S hS}
    {ζ : ZU ⟶ (schemeSpace U : AlgebraicSpaces B S hS)}
    {w : W ⟶ ZU} (hζ : IsFinite B S hS ζ.hom) (hw_surjective : IsSurjective B S hS w.hom)
    (hw_etale : IsEtale B S hS w.hom) :
    IsSurjective B S hS (restrictionOfScalars B S hS w ζ).projection := by
  classical
  refine isSurjective_of_isSurjective_affine_baseChange B S hS _ ?_
  intro T₀ hT₀ a
  -- Over the affine object `T₀` the finite morphism `ζ` is represented by an object `V`.
  obtain ⟨V, pV, i, -, hπ, hVpb⟩ := hζ T₀ hT₀ a
  -- The base change of `w` along that representative is again surjective étale.
  have hWV : IsAlgebraicSpace B S hS (pullback w.hom i) :=
    isAlgebraicSpace_pullback B S hS w.hom i W.property
      (isAlgebraicSpace_yoneda B S hS V) ZU.property
  have hwV_surjective : IsSurjective B S hS (pullback.snd w.hom i) :=
    isSurjective_pullback_snd B S hS W.property ZU.property
      (isAlgebraicSpace_yoneda B S hS V) w.hom i hw_surjective
  have hwV_etale : IsEtale B S hS (pullback.snd w.hom i) :=
    isEtale_pullback_snd B S hS (isAlgebraicSpace_yoneda B S hS V) ZU.property W.property
      w.hom i hw_etale
  -- Stacks 05XQ over the base object `T₀`.
  obtain ⟨T, r, hr_surjective, -, σ, hσ⟩ :=
    exists_surjective_etale_sectionOverBase B S hS T₀ V pV hπ (pullback w.hom i)
      (pullback.snd w.hom i) hWV hwV_surjective hwV_etale
  -- `T ×_{T₀} V` is a base change of `Z_U` along `r` followed by the given point of `U`.
  have hpaste : IsPullback (pullback.fst (yoneda.map r) (yoneda.map pV))
      (pullback.snd (yoneda.map r) (yoneda.map pV) ≫ i) (yoneda.map r ≫ a) ζ.hom :=
    (IsPullback.of_hasPullback (yoneda.map r) (yoneda.map pV)).paste_vert hVpb.flip
  -- The section is the second component of a pair of Stacks 05Y9 over `T`.
  obtain ⟨p, hpbase⟩ : ∃ p : RestrictionPair B S hS w ζ (yoneda.obj T),
      p.base = yoneda.map r ≫ a := by
    refine ⟨⟨yoneda.map r ≫ a,
      hpaste.lift (pullback.fst (yoneda.map r ≫ a) ζ.hom)
          (pullback.snd (yoneda.map r ≫ a) ζ.hom) pullback.condition ≫
        σ ≫ pullback.fst w.hom i, ?_⟩, rfl⟩
    simp only [Category.assoc]
    rw [pullback.condition (f := w.hom) (g := i),
      ← Category.assoc σ (pullback.snd w.hom i) i, hσ]
    exact hpaste.lift_snd _ _ _
  have hpt : p.point ≫ (restrictionOfScalars B S hS w ζ).projection = yoneda.map r ≫ a := by
    rw [RestrictionPair.point_comp_projection, hpbase]
  -- The pair gives a point of the base change of the projection over a surjective `r`.
  intro y
  obtain ⟨t, ht⟩ := isSurjective_yoneda_map B S hS r hr_surjective y
  refine ⟨pointsMap B S hS (yoneda.obj T)
    (pullback.lift p.point (yoneda.map r) hpt) t, ?_⟩
  have hcomp : pointsMap B S hS (pullback (restrictionOfScalars B S hS w ζ).projection a)
        (pullback.snd (restrictionOfScalars B S hS w ζ).projection a)
        (pointsMap B S hS (yoneda.obj T) (pullback.lift p.point (yoneda.map r) hpt) t) =
      pointsMap B S hS (yoneda.obj T)
        (pullback.lift p.point (yoneda.map r) hpt ≫
          pullback.snd (restrictionOfScalars B S hS w ζ).projection a) t := by
    rw [pointsMap_comp]; rfl
  rw [hcomp, pullback.lift_snd]
  exact ht

end AlgebraicGeometry.Space

end
