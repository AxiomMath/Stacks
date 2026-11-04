module

public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.RelativeOverField
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkAsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness
public import StacksFrontier.AlgebraicGeometry.Spaces.GeometricPointEtaleLift
public import StacksFrontier.AlgebraicGeometry.Spaces.RecoveringMorphisms.Bijectivity

/-!
# Conservative families of points of a slice of the small étale site

For an étale chart `V` of an algebraic space `F`, the localizations at `V` of the geometric
points of `F` lifting to `V` are a conservative family of points of the slice of the small étale
site over `V` (`AlgebraicGeometry.Space.isConservativeFamilyOfPoints_etaleSitePointOver`).  This
file shows that a much smaller family suffices: any family of lifts whose images cover the
points of the scheme underlying `V`.  Such families arise when the geometric points are produced
by a construction, for instance as images of geometric points of the members of a flat
covering, and cannot be taken to be all geometric points.

## Main results

* `AlgebraicGeometry.Space.exists_geometricPoint_hom_of_point`: every point of an object of the
  big fppf site is hit by a geometric point.
* `AlgebraicGeometry.Space.exists_geometricFiber_lift_of_chartHom`: a lift of a geometric point
  to an étale chart lifts along any morphism of étale charts, through any prescribed point over
  its image.
* `AlgebraicGeometry.Space.isConservativeFamilyOfPoints_etaleSitePointOver_of_family`: a family
  of lifts covering the points of the chart is conservative on the slice.

## References

* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
* [Stacks Project, Tag 04H2](https://stacks.math.columbia.edu/tag/04H2)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Every point of the scheme underlying an object `T` of the big fppf site is hit by a geometric
point of `yoneda.obj T`; its image under any `η : yoneda.obj T ⟶ F` is a geometric point of `F`
whose section is the composite.  This is `AlgebraicGeometry.Space.exists_geo_lift_at_chart_point`
for the identity chart of `yoneda.obj T`. -/
theorem exists_geometricPoint_hom_of_point {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (T : BigFppfOver B S hS) (η : yoneda.obj T ⟶ F) (z : (BigFppfOver.toScheme B S hS).obj T) :
    ∃ (x : GeometricPoint B S hS F) (ξ : x.val.siteObject ⟶ T),
      η.app (Opposite.op x.val.siteObject) ξ = x.val.value ∧
        ∃ z' : (BigFppfOver.toScheme B S hS).obj x.val.siteObject,
          (BigFppfOver.toScheme B S hS).map ξ z' = z := by
  obtain ⟨x, p, z', hz⟩ :=
    exists_geo_lift_at_chart_point B S hS (yoneda.obj T) (idChart B S hS T) z
  exact ⟨geometricPointMap η x, p.1, congrArg (η.app _) p.2, z', hz⟩

/-- **Lifting a geometric point along a morphism of étale charts, through a prescribed point.**
Let `g : W ⟶ V` be a morphism of étale charts of `F`, let `p` lift a geometric point `x̄` of `F`
to `V`, and let `z` be a point of `W` lying over the image of `p`.  Then `p` lifts along `g` to a
lift of `x̄` to `W` passing through `z`.  The base change of the étale `g` along `p` is étale over
the spectrum of the algebraically closed field of `x̄`, and every point of such a scheme is the
image of a section (`AlgebraicGeometry.etale_field_map_factors`). -/
theorem exists_geometricFiber_lift_of_chartHom {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {W V : SmallEtale B S hS F} (g : W ⟶ V) (x : GeometricPoint B S hS F)
    (p : GeometricFiber B S hS F x V) (z : (BigFppfOver.toScheme B S hS).obj W.obj.left)
    (ζ : (BigFppfOver.toScheme B S hS).obj x.val.siteObject)
    (hz : (BigFppfOver.toScheme B S hS).map g.hom.left z =
      (BigFppfOver.toScheme B S hS).map p.1 ζ) :
    ∃ q : GeometricFiber B S hS F x W, q.1 ≫ g.hom.left = p.1 ∧
      ∃ ζ' : (BigFppfOver.toScheme B S hS).obj x.val.siteObject,
        (BigFppfOver.toScheme B S hS).map q.1 ζ' = z := by
  classical
  let G := BigFppfOver.toScheme B S hS
  let γ := G.map g.hom.left
  let P := G.map p.1
  obtain ⟨w, hw₁, hw₂⟩ := Scheme.Pullback.exists_preimage_pullback (f := γ) (g := P) z ζ hz
  have : IsAlgClosed x.val.carrier := x.property
  obtain ⟨l, hl, hq⟩ := etale_field_map_factors x.val.carrier (pullback.snd γ P) inferInstance
    ((pullback γ P).residueField w) ((pullback γ P).fromSpecResidueField w)
  let qs : G.obj x.val.siteObject ⟶ G.obj W.obj.left := l ≫ pullback.fst γ P
  have hqs : qs ≫ γ = P := by
    simp only [qs, Category.assoc, pullback.condition]
    rw [← Category.assoc, hl]
    exact Category.id_comp _
  let s₀ : Spec ((pullback γ P).residueField w) := default
  let ζ₀ : G.obj x.val.siteObject := ((pullback γ P).fromSpecResidueField w ≫ pullback.snd γ P) s₀
  have hls : l ζ₀ = w := by
    have h := congrArg (fun h : Spec ((pullback γ P).residueField w) ⟶ pullback γ P => h s₀) hq
    refine Eq.trans ?_ (h.symm.trans ((pullback γ P).fromSpecResidueField_apply w s₀))
    exact (Scheme.Hom.comp_apply _ _ _).symm
  have hbase : qs ≫ B.inclusion.map W.obj.left.hom =
      B.inclusion.map x.val.siteObject.hom := by
    calc qs ≫ B.inclusion.map W.obj.left.hom
        = qs ≫ B.inclusion.map (g.hom.left.left ≫ V.obj.left.hom) := by rw [Over.w g.hom.left]
      _ = (qs ≫ γ) ≫ B.inclusion.map V.obj.left.hom := by
          rw [Functor.map_comp, Category.assoc]; rfl
      _ = B.inclusion.map (p.1.left ≫ V.obj.left.hom) := by
          rw [hqs, Functor.map_comp]; rfl
      _ = B.inclusion.map x.val.siteObject.hom := by rw [Over.w p.1]
  let qBelow : B.inclusion.obj x.val.siteObject.left ⟶ B.inclusion.obj W.obj.left.left := qs
  let qSite : x.val.siteObject ⟶ W.obj.left := Over.homMk (B.inclusion.preimage qBelow)
    (B.inclusion.map_injective (by rw [Functor.map_comp, Functor.map_preimage]; exact hbase))
  have hqMap : G.map qSite = qs := B.inclusion.map_preimage qBelow
  have hqg : qSite ≫ g.hom.left = p.1 := G.map_injective (by rw [G.map_comp, hqMap]; exact hqs)
  refine ⟨⟨qSite, ?_⟩, hqg, ζ₀, ?_⟩
  · calc W.obj.hom.app (Opposite.op x.val.siteObject) qSite
        = (yoneda.map g.hom.left ≫ V.obj.hom).app (Opposite.op x.val.siteObject) qSite := by
          rw [CostructuredArrow.w g.hom]
      _ = V.obj.hom.app (Opposite.op x.val.siteObject) (qSite ≫ g.hom.left) := rfl
      _ = x.val.value := by rw [hqg]; exact p.2
  · show G.map qSite ζ₀ = z
    rw [hqMap]
    show (l ≫ pullback.fst γ P) ζ₀ = z
    rw [Scheme.Hom.comp_apply, hls]
    exact hw₁

/-- **A family of lifts of geometric points meeting every point of a chart is a conservative
family of points of the slice.**  Let `V` be an étale chart of an algebraic space `F` and `ψ` a
family of geometric points of `F` with lifts to `V` whose images cover the scheme underlying `V`.
Then the localizations of these points at their lifts form a conservative family of points of the
slice of the small étale site over `V`.  This sharpens
`AlgebraicGeometry.Space.isConservativeFamilyOfPoints_etaleSitePointOver`, where the family is
all lifts of all geometric points; the proof is the same sieve criterion, with
`AlgebraicGeometry.Space.exists_geometricFiber_lift_of_chartHom` producing the required lift. -/
theorem isConservativeFamilyOfPoints_etaleSitePointOver_of_family
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (V : SmallEtale B S hS F) {t : Type*}
    (ψ : t → Σ x : GeometricPoint B S hS F, (etaleSitePoint B S hS F x hF).fiber.obj V)
    (hψ : ∀ v : (BigFppfOver.toScheme B S hS).obj V.obj.left, ∃ k,
      ∃ ζ : (BigFppfOver.toScheme B S hS).obj (ψ k).1.val.siteObject,
        (BigFppfOver.toScheme B S hS).map (ψ k).2.1 ζ = v) :
    ObjectProperty.IsConservativeFamilyOfPoints
      (ObjectProperty.ofObj (fun k => (etaleSitePoint B S hS F (ψ k).1 hF).over (ψ k).2)) := by
  apply ObjectProperty.IsConservativeFamilyOfPoints.mk'
  intro Y T hT
  obtain ⟨Y, g, rfl⟩ := Over.mk_surjective Y
  obtain ⟨T, rfl⟩ := (Sieve.overEquiv (Over.mk g)).symm.surjective T
  rw [GrothendieckTopology.mem_over_iff, OrderIso.apply_symm_apply]
  refine smallEtale_sieve_of_pointwise_covering B S hS F Y T (fun z => ?_)
  obtain ⟨k, ζ, hζ⟩ := hψ ((BigFppfOver.toScheme B S hS).map g.hom.left z)
  obtain ⟨q, hq, ζ', hζ'⟩ := exists_geometricFiber_lift_of_chartHom B S hS g (ψ k).1 (ψ k).2 z ζ
    hζ.symm
  have hmem := ObjectProperty.ofObj_apply
    (fun k => (etaleSitePoint B S hS F (ψ k).1 hF).over (ψ k).2) k
  obtain ⟨W, h, hh, w, hw⟩ := hT ⟨_, hmem⟩
    ⟨q, (FunctorToTypes.mem_fromOverSubfunctor_iff _ _ _).mpr (Subtype.ext hq)⟩
  refine ⟨W.left, h.left, (Sieve.overEquiv_symm_iff T h).1 hh,
    (BigFppfOver.toScheme B S hS).map w.val.val ζ', ?_⟩
  have hm : w.val.val ≫ (SmallEtale.toOver B S hS F).map h.left = q.val :=
    congrArg Subtype.val (congrArg Subtype.val hw)
  rw [← Scheme.Hom.comp_apply, ← Functor.map_comp, hm]
  exact hζ'

end AlgebraicGeometry.Space

end
