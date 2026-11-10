module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.Zariski

/-!
# An open cover of an object of the site is a Zariski covering of its representable sheaf

Let `S` be a scheme contained in a big fppf site `B`. A family `{gᵢ : Xᵢ ⟶ T}` of morphisms of
the big fppf site of `S` whose underlying morphisms of schemes are open immersions covering the
underlying scheme of `T` induces a Zariski covering, hence an fppf covering, of the presheaf
represented by `T`.

This is the passage from a Zariski cover of a *scheme* of the site to a covering family in the
sense of **Stacks 041G**, whose joint surjectivity is a condition on field-valued points rather
than on scheme points: a field-valued point of `T` whose image lies in the image of an open
immersion lifts along it, by `AlgebraicGeometry.IsOpenImmersion.lift`.

## Main results

* `AlgebraicGeometry.Space.exists_fieldValuedPoint_of_mem_range`: a field-valued point of a
  represented presheaf whose scheme point lies in the image of an open immersion of the site is
  the image of a field-valued point of the smaller representable.
* `AlgebraicGeometry.Space.isZariskiCovering_yoneda_of_openCover`: **Stacks 041G** for an open
  cover of an object of the site.
* `AlgebraicGeometry.Space.isFppfCovering_yoneda_of_openCover`: the same family is an fppf
  covering, by **Stacks 0DFC**.

## References

* [Stacks Project, Tag 041G](https://stacks.math.columbia.edu/tag/041G)
* [Stacks Project, Tag 0DFC](https://stacks.math.columbia.edu/tag/0DFC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A field-valued point of a represented presheaf whose underlying scheme point lies in the
image of an open immersion of the site is the image of a field-valued point of the smaller
representable.** The spectrum of the point's field maps into the open, so the point lifts along
the open immersion by `AlgebraicGeometry.IsOpenImmersion.lift`, and the lift is a morphism of
the site because the inclusion of the site into schemes is fully faithful. -/
theorem exists_fieldValuedPoint_of_mem_range
    {T V : BigFppfOver B S hS} (j : V ⟶ T)
    [_root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map j)]
    (p : FieldValuedPoint B S hS (yoneda.obj T))
    (hp : schemePoint B S hS T p ∈
      Set.range ((BigFppfOver.toScheme B S hS).map j)) :
    ∃ q : FieldValuedPoint B S hS (yoneda.obj V),
      pointsMap B S hS (yoneda.obj V) (yoneda.map j) (q.class B S hS (yoneda.obj V)) =
        p.class B S hS (yoneda.obj T) := by
  classical
  let G := BigFppfOver.toScheme B S hS
  let A := FieldValuedPoint.siteObject B S hS (yoneda.obj T) p
  let _ : Field p.carrier := p.field
  have hrange : Set.range (G.map p.value) ⊆ Set.range (G.map j) := by
    rintro _ ⟨z, rfl⟩
    obtain rfl : z = IsLocalRing.closedPoint p.carrier :=
      (inferInstance : Subsingleton (PrimeSpectrum p.carrier)).elim _ _
    simpa [schemePoint, G] using hp
  let ψ : Spec (.of p.carrier) ⟶ G.obj V :=
    IsOpenImmersion.lift (G.map j) (G.map p.value) hrange
  have hψ : ψ ≫ G.map j = G.map p.value := IsOpenImmersion.lift_fac _ _ _
  let k : A.left ⟶ V.left :=
    B.inclusion.preimage
      (show B.inclusion.obj A.left ⟶ B.inclusion.obj V.left from ψ)
  have hk : B.inclusion.map k = ψ := B.inclusion.map_preimage _
  let g : A ⟶ V := Over.homMk k (by
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp]
    have hw : ∀ {W : BigFppfOver B S hS} (f : W ⟶ T),
        G.map f ≫ B.inclusion.map T.hom = B.inclusion.map W.hom := fun f => by
      change B.inclusion.map f.left ≫ B.inclusion.map T.hom = _
      rw [← B.inclusion.map_comp, f.w]
    rw [hk, ← hw j, ← Category.assoc, hψ]
    exact hw p.value)
  have hg : g ≫ j = p.value := by
    apply Over.OverMorphism.ext
    change k ≫ j.left = p.value.left
    apply B.inclusion.map_injective
    rw [B.inclusion.map_comp, hk]
    exact hψ
  refine ⟨⟨p.carrier, p.contained, p.toBase, g⟩, ?_⟩
  rw [pointsMap_class]
  refine congrArg (FieldValuedPoint.class B S hS (yoneda.obj T)) ?_
  cases p
  simp [FieldValuedPoint.map, hg]

/-- **Stacks 041G for an open cover of an object of the big fppf site of `S`.** A family of
morphisms of the site whose underlying morphisms of schemes are open immersions covering the
underlying scheme of the target induces a Zariski covering of the presheaf represented by the
target. -/
@[stacks 041G "an open cover of an object of the site"]
theorem isZariskiCovering_yoneda_of_openCover
    {I : Type v} {T : BigFppfOver B S hS} (X : I → BigFppfOver B S hS) (g : ∀ i, X i ⟶ T)
    (hopen : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (g i)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i))) :
    IsZariskiCovering B S hS I (fun i => yoneda.obj (X i)) (fun i => yoneda.map (g i)) := by
  refine ⟨fun i => ?_, fun x => ?_⟩
  · have _ := inverseImage_isStableUnderBaseChange B S hS
      (P := (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u}))
      inferInstance
    exact (MorphismProperty.relative_map_iff
      (P := MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))).2 (hopen i)
  · obtain ⟨p, rfl⟩ := Quot.exists_rep x
    obtain ⟨i, hi⟩ := hcov (schemePoint B S hS T p)
    have _ := hopen i
    obtain ⟨q, hq⟩ := exists_fieldValuedPoint_of_mem_range B S hS (g i) p hi
    exact ⟨i, q.class B S hS (yoneda.obj (X i)), hq⟩

/-- **Stacks 0DFC for an open cover of an object of the big fppf site of `S`.** The family of
representables of an open cover of an object of the site is an fppf covering of the
representable of that object: it is a Zariski covering by Stacks 041G. -/
@[stacks 0DFC "an open cover of an object of the site"]
theorem isFppfCovering_yoneda_of_openCover
    {I : Type v} {T : BigFppfOver B S hS} (X : I → BigFppfOver B S hS) (g : ∀ i, X i ⟶ T)
    (hopen : ∀ i, _root_.AlgebraicGeometry.IsOpenImmersion
      ((BigFppfOver.toScheme B S hS).map (g i)))
    (hcov : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, x ∈ Set.range ((BigFppfOver.toScheme B S hS).map (g i))) :
    IsFppfCovering B S hS (fun i => yoneda.obj (X i)) (fun i => yoneda.map (g i)) :=
  isFppfCovering_of_isZariskiCovering B S hS (isAlgebraicSpace_yoneda B S hS T)
    (fun i => isAlgebraicSpace_yoneda B S hS (X i))
    (isZariskiCovering_yoneda_of_openCover B S hS X g hopen hcov)

end AlgebraicGeometry.Space

end
