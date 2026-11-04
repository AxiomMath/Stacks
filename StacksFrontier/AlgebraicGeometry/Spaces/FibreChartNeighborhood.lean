module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsAndCoverings.RelativeProperties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# A small étale neighbourhood of a point of a fibre whose chart is a base-changed fibre

Let `X ⟶ Y` be a morphism of algebraic spaces over `S`, let `V ⟶ Y` be a surjective étale
scheme chart of the target and let `Spec k' ⟶ Y` be a point of the target which factors through
`V`, say as `ρ : Spec k' ⟶ V` followed by the chart. Let `F = X ×_Y Spec k'` be the fibre. For
an arbitrary geometric point `z` of `F` there are a surjective étale scheme chart `U` of `X` lying
over `V` and a small étale neighbourhood of `z` whose chart scheme is the base change along
`κ(v) ⊆ k'` of the scheme-theoretic fibre of `U ⟶ V` at the image point `v` of `ρ`:

`chartScheme N.chart ≅ U_v ×_{Spec κ(v)} Spec k' = pullback (g.fiberToSpecResidueField v)
(Spec.map φ)`.

## Main results

* `AlgebraicGeometry.exists_specResidueField_factorization`: a morphism from the spectrum of a
  field to a scheme factors through the residue field at its image point.
* `AlgebraicGeometry.isPullback_fiberBaseChange`: for `g : U ⟶ V` and a morphism
  `s : Spec K ⟶ V` factoring through the residue field at `v` by `φ`, the base change
  `U_v ×_{κ(v)} Spec K` of the fibre of `g` at `v` is the fibre product `U ×_V Spec K`.
* `AlgebraicGeometry.Space.exists_smallEtaleNeighborhood_fiberBaseChange`: for a cartesian square
  exhibiting `F` as `X ×_Y Spec k'` with the point of `Y` factored through the chart `V`, every
  geometric point of `F` has a small étale neighbourhood whose chart scheme is the base-changed
  fibre above, carried by a surjective étale scheme chart `U` of `X` which lies over `V`.

## References

* [Stacks Project, Tag 02X2](https://stacks.math.columbia.edu/tag/02X2)
* [Stacks Project, Tag 03EC](https://stacks.math.columbia.edu/tag/03EC)
* [Stacks Project, Tag 03FU](https://stacks.math.columbia.edu/tag/03FU)
* [Stacks Project, Tag 04JY](https://stacks.math.columbia.edu/tag/04JY)
* [Stacks Project, Tag 06LI](https://stacks.math.columbia.edu/tag/06LI)
* [Stacks Project, Lemma 06LW](https://stacks.math.columbia.edu/tag/06LW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Factoring a field-valued point through the residue field -/

/-- A morphism from the spectrum of a field factors through the residue field at its image
point. -/
theorem exists_specResidueField_factorization {V : Scheme.{u}} {K : Type u} [Field K]
    (s : Spec (.of K) ⟶ V) :
    ∃ (v : V) (φ : V.residueField v ⟶ CommRingCat.of K),
      Spec.map φ ≫ V.fromSpecResidueField v = s ∧ v = s (IsLocalRing.closedPoint K) :=
  ⟨(Scheme.SpecToEquivOfField K V s).1, (Scheme.SpecToEquivOfField K V s).2,
    (Scheme.SpecToEquivOfField K V).symm_apply_apply s,
    Scheme.SpecToEquivOfField_apply_fst K V s⟩

/-- Let `g : U ⟶ V` be a morphism of schemes and let `s : Spec K ⟶ V` be a point of the target
over a field, factored through the residue field at `v` as `Spec.map φ` followed by
`Spec κ(v) ⟶ V`. Then the base change `U_v ×_{Spec κ(v)} Spec K` of the fibre of `g` at `v`
along `φ` is the fibre product `U ×_V Spec K`. -/
@[ega "I 3.6.4" "special case"]
theorem isPullback_fiberBaseChange {U V : Scheme.{u}} (g : U ⟶ V) (v : V)
    {K : Type u} [Field K] (φ : V.residueField v ⟶ CommRingCat.of K)
    (s : Spec (.of K) ⟶ V) (hs : Spec.map φ ≫ V.fromSpecResidueField v = s) :
    IsPullback (pullback.fst (g.fiberToSpecResidueField v) (Spec.map φ) ≫ g.fiberι v)
      (pullback.snd (g.fiberToSpecResidueField v) (Spec.map φ)) g s := by
  rw [← hs]
  exact (IsPullback.of_hasPullback (g.fiberToSpecResidueField v) (Spec.map φ)).paste_horiz
    (IsPullback.of_hasPullback g (V.fromSpecResidueField v))

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Let `X ⟶ Y` be a morphism of presheaves on the big fppf site of `S` with `X` and `Y`
algebraic spaces, let `q : V ⟶ Y` be a scheme chart of the target which is surjective and étale
after every represented base change, let `k'` be a field in the site and let
`ρ : Spec k' ⟶ V` be a morphism of the site, so that `Spec k' ⟶ Y` factors through the chart.
Let `F` be the fibre `X ×_Y Spec k'`, presented by a cartesian square, and let `z` be any
geometric point of `F`.

Then there is a surjective étale scheme chart `U ⟶ X` lying over `V`, with `v` the image of the
closed point of `Spec k'` under `ρ` and `φ : κ(v) ⟶ k'` the induced extension of residue
fields, together with a small étale neighbourhood of `z` whose chart scheme is the base change
`U_v ×_{Spec κ(v)} Spec k'` of the scheme-theoretic fibre of `U ⟶ V` at `v`. -/
theorem exists_smallEtaleNeighborhood_fiberBaseChange
    {X Y F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hF : IsAlgebraicSpace B S hS F) (gXY : X ⟶ Y)
    (V : BigFppfOver B S hS) (q : yoneda.obj V ⟶ Y)
    (hqS : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    (hqE : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))) q)
    {k' : Type u} [Field k'] (hk' : B.Contains (Spec (.of k'))) (b' : Spec (.of k') ⟶ S)
    (ρ : (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS) : BigFppfOver B S hS) ⟶ V)
    {ξ : F ⟶ X} {π : F ⟶ yoneda.obj (Over.mk (⟨b'⟩ : B.obj hk' ⟶ B.obj hS))}
    (sq : IsPullback ξ π gXY (yoneda.map ρ ≫ q))
    (z : GeometricPoint B S hS F) :
    ∃ (U : BigFppfOver B S hS) (gUV : U ⟶ V) (aX : yoneda.obj U ⟶ X)
      (N : SmallEtaleNeighborhood z)
      (v : (BigFppfOver.toScheme B S hS).obj V)
      (φ : ((BigFppfOver.toScheme B S hS).obj V).residueField v ⟶ CommRingCat.of k'),
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) aX ∧
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) aX ∧
      yoneda.map gUV ≫ q = aX ≫ gXY ∧
      v = (BigFppfOver.toScheme B S hS).map ρ (IsLocalRing.closedPoint k') ∧
      Nonempty (chartScheme N.chart ≅
        pullback (((BigFppfOver.toScheme B S hS).map gUV).fiberToSpecResidueField v)
          (Spec.map φ)) := by
  have hP : IsAlgebraicSpace B S hS (pullback gXY q) :=
    isAlgebraicSpace_pullback B S hS gXY q hX (isAlgebraicSpace_yoneda B S hS V) hY
  obtain ⟨U, a, haSurj, haEtale⟩ := hP.exists_atlas
  let gUV : U ⟶ V := yoneda.preimage (a ≫ pullback.snd gXY q)
  have hgUV : yoneda.map gUV = a ≫ pullback.snd gXY q := yoneda.map_preimage _
  have sqP : IsPullback (pullback.fst gXY q) (pullback.snd gXY q) gXY q :=
    IsPullback.of_hasPullback gXY q
  have sq' := IsPullback.of_right' sq sqP
  have hW : IsPullback (yoneda.map (pullback.fst gUV ρ)) (yoneda.map (pullback.snd gUV ρ))
      (a ≫ pullback.snd gXY q) (yoneda.map ρ) := by
    rw [← hgUV]
    exact (IsPullback.of_hasPullback gUV ρ).map yoneda
  have sqchart := (IsPullback.of_right' hW.flip sq'.flip).flip
  have hchartEtale := (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback sqchart haEtale
  have hchartSurj := (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback sqchart haSurj
  obtain ⟨⟨N, hN⟩⟩ := exists_pointed_smallEtaleNeighborhood B S hS F hF z _ hchartSurj
    hchartEtale
  have hfstSurj := (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback sqP.flip hqS
  have hfstEtale := (MorphismProperty.relative_isStableUnderBaseChange
    (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS))).of_isPullback sqP.flip hqE
  have _ : MorphismProperty.IsStableUnderComposition
      (@Surjective.{u} : MorphismProperty Scheme.{u}) := surjective_isStableUnderComposition.{u}
  have _ : MorphismProperty.IsStableUnderComposition
      (@Etale.{u} : MorphismProperty Scheme.{u}) := etale_isStableUnderComposition.{u}
  have _ : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) :=
    MorphismProperty.IsStableUnderComposition.inverseImage _
  have _ : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Surjective.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) :=
    MorphismProperty.relative_isStableUnderComposition _
  have _ : MorphismProperty.IsStableUnderComposition
      (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@Etale.{u} : MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS))) :=
    MorphismProperty.relative_isStableUnderComposition _
  have hpres := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  let s : Spec (.of k') ⟶ (BigFppfOver.toScheme B S hS).obj V :=
    (BigFppfOver.toScheme B S hS).map ρ
  obtain ⟨v, φ, hs, hv⟩ := exists_specResidueField_factorization s
  exact ⟨U, gUV, a ≫ pullback.fst gXY q, N, v, φ,
    MorphismProperty.comp_mem _ _ _ haSurj hfstSurj,
    MorphismProperty.comp_mem _ _ _ haEtale hfstEtale,
    by rw [hgUV]; simp only [Category.assoc, ← pullback.condition], hv,
    ⟨eqToIso (congrArg (BigFppfOver.toScheme B S hS).obj hN) ≪≫
      PreservesPullback.iso (BigFppfOver.toScheme B S hS) gUV ρ ≪≫
      (isPullback_fiberBaseChange _ v φ s hs).isoPullback.symm⟩⟩

end Space

end AlgebraicGeometry

end
