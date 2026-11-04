module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.FieldBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.Stacks.DecentStack
public import StacksFrontier.AlgebraicGeometry.Stacks.PointsTopologyRepresentable
public import StacksFrontier.AlgebraicGeometry.Stacks.QuasiSeparatedSecondDiagonal
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativeDimensionAtPoint
public import StacksFrontier.AlgebraicGeometry.Stacks.RelativePropertyRepresented

/-!
# A decent stack represented by an algebraic space

Let `𝒴` be a category fibred in groupoids over the big fppf site of `S` represented by an
algebraic space `F`. If `𝒴` is decent in the sense of **Stacks 0GW1**, then `F` is decent in the
sense of **Stacks 03I8**.

## Main results

* `AlgebraicGeometry.Stack.isDecentSpace_of_isDecent_representing`: decency of `𝒴` gives
  decency of `F`.

## Implementation notes

A point of `|F|` corresponds, through the homeomorphism of
`AlgebraicGeometry.Stack.isHomeomorph_spacePointMap_representing`, to a point of `|𝒴|`, which
decency of `𝒴` represents by a field-valued point `q` with quasi-compact 1-morphism. Read through
**Stacks 04SW** the 1-morphism is a quasi-compact morphism of algebraic spaces
`h_{q.base} ⟶ F` (`AlgebraicGeometry.Stack.hasRelativeProperty_iff_prop_representingMap`), and
restricting it to the field spectrum of `q` gives a quasi-compact field-valued representative of
the point, which is condition (5) of **Stacks 03JV**. Condition (5) implies condition (4), the
definition of decency.

## References

* [Stacks Project, Tag 03I8](https://stacks.math.columbia.edu/tag/03I8)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 04SW](https://stacks.math.columbia.edu/tag/04SW)
* [Stacks Project, Tag 0GW1](https://stacks.math.columbia.edu/tag/0GW1)
-/

@[expose] public section

open CategoryTheory Opposite

namespace AlgebraicGeometry.Stack

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A decent category fibred in groupoids represented by an algebraic space has decent
representing space.** If `𝒴` is decent (**Stacks 0GW1**) and represented by the algebraic space
`F`, then `F` is decent (**Stacks 03I8**). -/
theorem isDecentSpace_of_isDecent_representing
    (𝒴 : CatFiberedInGroupoids.{u, u, u + 1, u + 1} (BigFppfOver B S hS))
    (h𝒴 : IsDecent B S hS 𝒴)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    (e : StacksRepresentableCFG.EquivalenceOver 𝒴.val.p
      (presheafOfCategories (F ⋙ typeToCat)).p) :
    Space.IsDecentSpace B S hS F := by
  intro x
  refine Space.hasQuasiCompactMonomorphicFieldRepresentative_of_hasQuasiCompactFieldRepresentative
    B S hS F hF ?_
  let φ := spacePointMap B S hS F 𝒴 (representingEquivalence B S hS F 𝒴 e).functor
  have hφ : Function.Bijective φ := bijective_spacePointMap_representing B S hS F 𝒴 e
  obtain ⟨q, hq, hrep, hqc⟩ := h𝒴 (φ x)
  let eQ : StacksRepresentableCFG.EquivalenceOver (schemeFibredCategory B S hS q.base).val.p
      (presheafOfCategories (yoneda.obj q.base ⋙ typeToCat)).p :=
    PresheafOfCategories.sliceElementsEquivalenceOver q.base
  let a := fieldValuedPointMorphism B S hS 𝒴 q
  let : (Space.quasiCompactProperty B S hS).IsLocalAtTarget
      (Space.Topology.fppf.precoverage.{u, u} B S hS) :=
    Space.isQuasiCompact_isLocalAtTarget_fppf B S hS
  have hr : Space.IsQuasiCompact B S hS
      (representingMap B S hS (schemeFibredCategory B S hS q.base) 𝒴 (yoneda.obj q.base) F
        eQ e a) :=
    (hasRelativeProperty_iff_prop_representingMap B S hS (Space.quasiCompactProperty B S hS) a
      hrep (yoneda.obj q.base) F (isAlgebraicSpace_yoneda B S hS q.base) hF eQ e).1 hqc
  set r := representingMap B S hS (schemeFibredCategory B S hS q.base) 𝒴 (yoneda.obj q.base) F
    eQ e a with hrdef
  let p₀ := Space.FieldValuedPoint.map B S hS (yoneda.obj q.base) r (baseSpacePoint B S hS q)
  refine ⟨p₀, ?_, ?_⟩
  · apply hφ.1
    show spacePointMap B S hS F 𝒴 (representingEquivalence B S hS F 𝒴 e).functor
      (Space.pointsMap B S hS (yoneda.obj q.base) r
        ((baseSpacePoint B S hS q).class B S hS _)) = _
    refine (spacePointMap_representing_naturality B S hS (yoneda.obj q.base) F
      (schemeFibredCategory B S hS q.base) 𝒴 eQ e a _).trans ?_
    rw [spacePointMap_class, ← hq]
    show pointClass B S hS 𝒴.val 𝒴.property (fieldValuedPointMap B S hS _ a.hom
      (fieldValuedPointMap B S hS _ (representingEquivalence B S hS (yoneda.obj q.base)
        (schemeFibredCategory B S hS q.base) eQ).functor
        (spaceFieldValuedPoint B S hS _ (baseSpacePoint B S hS q)))) = _
    refine (class_eq_class_iff_hasCommonExtension B S hS 𝒴.val 𝒴.property _ _).2
      ⟨_, ⟨𝟙 _⟩, ⟨?_⟩⟩
    exact (Functor.TwoYoneda.chosenLift 𝒴.val.p 𝒴.property q.base ⟨q.obj, q.over⟩
      (Over.mk (spectrumSiteObjectIso B S hS q).hom)).φ
  · have hv : yonedaEquiv.symm (spectrumSiteObjectIso B S hS q).hom =
        yoneda.map (spectrumSiteObjectIso B S hS q).hom :=
      yonedaEquiv.symm_apply_eq.2 (yonedaEquiv_yoneda_map _).symm
    have hfm : Space.fieldMorphism B S hS F p₀ =
        yoneda.map (spectrumSiteObjectIso B S hS q).hom ≫ r := by
      have h1 : yonedaEquiv.symm (r.app (op (spectrumSiteObject B S hS q))
          (spectrumSiteObjectIso B S hS q).hom) =
          yonedaEquiv.symm (spectrumSiteObjectIso B S hS q).hom ≫ r :=
        (yonedaEquiv_symm_naturality_right (spectrumSiteObject B S hS q) r _).symm
      exact h1.trans (congrArg (· ≫ r) hv)
    rw [hfm]
    exact Space.isQuasiCompact_isIso_comp B S hS
      (yoneda.map (spectrumSiteObjectIso B S hS q).hom) hr

end AlgebraicGeometry.Stack

end
