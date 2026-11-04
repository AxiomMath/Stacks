module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProjectiveBundle.ZariskiReadingPullbackBaseChange

/-!
# Sections over a Zariski open of a direct image, read along any chart map

For a morphism `h : T' ⟶ T` of test objects and a Zariski open `O` of the scheme of `T`, the
identification `AlgebraicGeometry.Space.directImageSelfOpensSection` of the sections over `O` of
the direct image along `h` with sections over the chart of the preimage open restricts along the
inverse of `AlgebraicGeometry.Space.baseChangeSelfOpensIso`.  Morphisms from an étale chart into
the base change of the chart of `O` are unique, that base change being the chart of the preimage
open, so the identification is restriction along any such morphism.  This is the sections
comparison of the base change of the Zariski reading against the conjugate of
`AlgebraicGeometry.Space.representedSquareModulePullbackIso`: both sides restrict along a map into
the base change of the chart of `O`.

## Main results

* `AlgebraicGeometry.Space.subsingleton_hom_baseChangeSelfOpens`: morphisms into the base change
  of the chart of a Zariski open are unique.
* `AlgebraicGeometry.Space.directImageSelfOpensSection_eq_map`: the identification of sections is
  restriction along any morphism into that base change.
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {T T' : BigFppfOver B S hS}
  (h : T' ⟶ T)

/-- **Morphisms into the base change of the chart of a Zariski open are unique**: that base change
is the chart of the preimage open (`AlgebraicGeometry.Space.baseChangeSelfOpensIso`). -/
theorem subsingleton_hom_baseChangeSelfOpens (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (W : SmallEtale B S hS (yoneda.obj T')) :
    Subsingleton (W ⟶ (smallBaseChange B S hS (representedSpaceMap B S hS h)
        (relativelyRepresentable_yoneda_map B S hS h)).obj ((selfOpensFunctor B S hS T).obj O)) :=
  ⟨fun _ _ => (cancel_mono (baseChangeSelfOpensIso h O).hom).mp
    ((subsingleton_hom_selfOpensFunctor B S hS T' W (preimageOpens h O)).elim _ _)⟩

/-- **The identification of sections over a Zariski open of a direct image is restriction along
any morphism from the chart of the preimage open to the base change of the chart of the open.** -/
theorem directImageSelfOpensSection_eq_map (O : (chartScheme (idEtaleChart B S hS T)).Opens)
    (F : Sheaf (SmallEtale.topology B S hS (yoneda.obj T')) (Type u))
    (x : ((testToposHom h).toToposHom.pushforward.obj F).obj.obj
      (op ((selfOpensFunctor B S hS T).obj O)))
    (b : (selfOpensFunctor B S hS T').obj (preimageOpens h O) ⟶
      (smallBaseChange B S hS (representedSpaceMap B S hS h)
        (relativelyRepresentable_yoneda_map B S hS h)).obj ((selfOpensFunctor B S hS T).obj O)) :
    directImageSelfOpensSection h O F x =
      F.obj.map b.op (((smallEtaleDirectImageRanIso B S hS (representedSpaceMap B S hS h) ≪≫
        chartRanIso B S hS (representedSpaceMap B S hS h)
          (relativelyRepresentable_yoneda_map B S hS h)).hom.app F).hom.app _ x) :=
  congrArg (fun a : (selfOpensFunctor B S hS T').obj (preimageOpens h O) ⟶
      (smallBaseChange B S hS (representedSpaceMap B S hS h)
        (relativelyRepresentable_yoneda_map B S hS h)).obj ((selfOpensFunctor B S hS T).obj O) =>
      F.obj.map a.op (((smallEtaleDirectImageRanIso B S hS
      (representedSpaceMap B S hS h) ≪≫ chartRanIso B S hS (representedSpaceMap B S hS h)
        (relativelyRepresentable_yoneda_map B S hS h)).hom.app F).hom.app _ x))
    (@Subsingleton.elim _ (subsingleton_hom_baseChangeSelfOpens h O _)
      (baseChangeSelfOpensIso h O).inv b)

end AlgebraicGeometry.Space
