module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.StandardEtale
import all StacksFrontier.AlgebraicGeometry.Morphisms.Etale.StandardEtale
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Morphisms.FiniteTypePoint
public import Mathlib.AlgebraicGeometry.Pullbacks

/-!
# Pointwise étaleness and unramifiedness along an open immersion

This file collects the local facts about étaleness, unramifiedness and finite type at a point
that the comparison of a finite étale cover with its extension across a depth-two complement
needs.

Étaleness at a point (`AlgebraicGeometry.EtaleAt`) and unramifiedness at a point
(`AlgebraicGeometry.UnramifiedAt`) are defined by the existence of affine neighbourhoods on
which the map of sections has the corresponding ring-theoretic property, so composing with an
open immersion on the source transports them in both directions: the image of an affine open
under an open immersion is affine, and the two maps of sections agree up to the canonical
isomorphism `AlgebraicGeometry.arrowResLEAppIso`. For unramifiedness the transport is cleanest
through the stalkwise description, `AlgebraicGeometry.unramifiedAt_iff_morphisms_unramifiedAt`
(Stacks Tag 039J), since the stalk map of `j ≫ f` factors as the stalk map of `f` followed by an
isomorphism.

## Main results

* `Stacks.FundamentalGroup.ExtendedEtaleFold.etaleAt_of_etaleAt_isOpenImmersion_comp` — étaleness
  at a point descends along an open immersion of the source.
* `unramifiedAt_isOpenImmersion_comp` — unramifiedness at a point ascends along an open immersion
  of the source.
* `exists_preimage_of_mem_opensRange` — a point of the target of a base change whose image lies
  in the range of the base is hit by the base-changed cover.

## Implementation notes

No `@[stacks]` attribute is placed here: these are ingredients of the `etale_iff_flat` clause of
[Stacks, Tag 0EY6], and that clause itself is proved and tagged in
`StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.Purity`, as
`etaleAt_iff_isFlatAt_extendedEtale`. Its two inputs, Stacks Tag 0BJH and the openness of the
flat locus (Stacks Tag 05IM), are both available --- at
`PurityBranchLocus/UnramifiedCodimensionOne.lean` and `Flatness/FiniteTypeII/FlatLocus.lean`
respectively --- contrary to what this note previously recorded.

The private `etale_resLE_of_etale_appLE` of
`StacksFrontier/AlgebraicGeometry/Morphisms/Etale/StandardEtale.lean` is reached by `import all`
rather than re-proved. Two further ingredients of the same argument are already in the library
and are deliberately not restated here: that the local ring at a generic point has Krull
dimension zero is `Stacks.Chow.ringKrullDim_stalk_eq_zero_of_mem_genericPoints`
(`StacksFrontier/AlgebraicGeometry/Chow/FibreCycles/FibreDimension.lean`), alongside
`Stacks.Chow.isMax_of_mem_genericPoints`, which says that nothing specialises to a generic point
but itself; and that the depth of a local ring is at most its Krull dimension is available as a
private lemma in five separate files, among them
`StacksFrontier/RingTheory/ProjectiveDimension/KrullDimension.lean`.

## References

* [Stacks Project, Tag 0EY6](https://stacks.math.columbia.edu/tag/0EY6)
* [Stacks Project, Tag 02GI](https://stacks.math.columbia.edu/tag/02GI)
* [Stacks Project, Tag 039J](https://stacks.math.columbia.edu/tag/039J)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace Stacks.FundamentalGroup.ExtendedEtaleFold

/-! ### Transport along an open immersion of the source -/

/-- **Unramifiedness at a point ascends along an open immersion of the source.** The stalk map of
`j ≫ f` at `x` is the stalk map of `f` at `j x` followed by the isomorphism `j.stalkMap x`, so
the two are isomorphic as arrows and formal unramifiedness transports; the comparison with the
affine-neighbourhood definition is Stacks Tag 039J. -/
public theorem unramifiedAt_isOpenImmersion_comp {X X' S : Scheme.{u}} (j : X' ⟶ X)
    [IsOpenImmersion j] (f : X ⟶ S) [IsLocallyNoetherian S] [LocallyOfFiniteType f] (x : X')
    (h : UnramifiedAt f (j x)) : UnramifiedAt (j ≫ f) x := by
  have hFormal : StalkwiseUnramifiedAt f (j x) :=
    (unramifiedAt_iff_morphisms_unramifiedAt f (j x)).mpr h
  let φ := f.stalkMap (j x)
  let ψ := (j ≫ f).stalkMap x
  let : Algebra (S.presheaf.stalk (f (j x))) (X.presheaf.stalk (j x)) := φ.hom.toAlgebra
  let : Algebra (S.presheaf.stalk ((j ≫ f) x)) (X'.presheaf.stalk x) := ψ.hom.toAlgebra
  have hFormalφ : φ.hom.FormallyUnramified :=
    RingHom.formallyUnramified_algebraMap.mpr hFormal
  have he : Arrow.mk φ ≅ Arrow.mk ψ := by
    refine Arrow.isoMk' φ ψ (Iso.refl _) (asIso (j.stalkMap x)) ?_
    have hcomp : ψ = φ ≫ j.stalkMap x := by
      simpa [ψ, φ] using Scheme.Hom.stalkMap_comp j f x
    rw [hcomp]
    simp
  have hFormalψ : ψ.hom.FormallyUnramified :=
    (RingHom.FormallyUnramified.respectsIso.arrow_mk_iso_iff he).mp hFormalφ
  exact (unramifiedAt_iff_morphisms_unramifiedAt (j ≫ f) x).mp
    (RingHom.formallyUnramified_algebraMap.mp hFormalψ)

/-- **Étaleness at a point descends along an open immersion of the source.** If `j ≫ f` is étale
at `x` on an affine open `A` of `X'`, then `f` is étale at `j x` on the affine open `j ''ᵁ A`:
the two restricted morphisms agree up to the isomorphism `j.isoImage A`, and étaleness of a
morphism of affine schemes is étaleness of the map of global sections. -/
public theorem etaleAt_of_etaleAt_isOpenImmersion_comp {X' X S : Scheme.{u}} (j : X' ⟶ X)
    [IsOpenImmersion j] (f : X ⟶ S) (x : X') (h : EtaleAt (j ≫ f) x) : EtaleAt f (j x) := by
  obtain ⟨A, hA, hxA, V, hV, hAV, hEt⟩ := h
  let W : X.Opens := j ''ᵁ A
  have hW : IsAffineOpen W := j.isAffineOpen_iff_of_isOpenImmersion.mpr hA
  have hWV : W ≤ f ⁻¹ᵁ V := by
    rintro _ ⟨a, ha, rfl⟩
    exact hAV ha
  let e : A.toScheme ≅ W.toScheme := j.isoImage A
  have hresA : Etale ((j ≫ f).resLE V A hAV) :=
    etale_resLE_of_etale_appLE (j ≫ f) A hA V hV hAV hEt
  have heq : e.inv ≫ (j ≫ f).resLE V A hAV = f.resLE V W hWV := by
    apply (cancel_mono V.ι).1
    calc
      e.inv ≫ (j ≫ f).resLE V A hAV ≫ V.ι = (e.inv ≫ A.ι ≫ j) ≫ f := by simp
      _ = W.ι ≫ f := by
        rw [show e.inv ≫ A.ι ≫ j = W.ι by simp [W, e, Scheme.Hom.isoImage_inv_ι j A]]
      _ = f.resLE V W hWV ≫ V.ι := by simp [Scheme.Hom.resLE_comp_ι]
  have hresW : Etale (f.resLE V W hWV) := by
    rw [← heq]
    infer_instance
  have : IsAffine W.toScheme := hW
  have : IsAffine V.toScheme := hV
  have hRingTop : ((f.resLE V W hWV).appTop).hom.Etale :=
    (HasRingHomProperty.iff_of_isAffine (P := @Etale)).1 hresW
  have hRing : (f.appLE V W hWV).hom.Etale :=
    (RingHom.Etale.respectsIso.arrow_mk_iso_iff (arrowResLEAppIso f V W hWV)).1 hRingTop
  exact ⟨W, hW, ⟨x, hxA, rfl⟩, V, hV, hWV, hRing⟩

/-! ### Points of a base change over the range of the base -/

/-- **A point of a base change whose image lies in the range of the base is hit.** If `π` is the
base change of `f` along the open immersion `j`, then the range of the second leg `g` is the
preimage under `f` of the range of `j`. -/
public theorem exists_preimage_of_mem_opensRange {U X V Y : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (f : Y ⟶ X) (π : V ⟶ U) (g : V ⟶ Y) (hpb : IsPullback π g j f) (y : Y)
    (hy : f y ∈ (j.opensRange : Set X)) : ∃ v : V, g v = y := by
  have : IsOpenImmersion g := MorphismProperty.of_isPullback hpb inferInstance
  have himage : g.opensRange = f ⁻¹ᵁ j.opensRange := by
    simpa using IsOpenImmersion.image_preimage_eq_preimage_image_of_isPullback hpb ⊤
  change y ∈ g.opensRange
  rw [himage]
  exact hy

end Stacks.FundamentalGroup.ExtendedEtaleFold

end
