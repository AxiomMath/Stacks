module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GeometricallyReducedGenericFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.Fibres.Reduced
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Reduction
public import StacksCore.Tactic.StacksAttribute

/-!
# Geometrically nonreduced fibres near the generic point

Let `f : X ⟶ Y` be a finite type morphism of schemes with irreducible target. If the fibre over
a generic point of `Y` is not geometrically reduced, then the same is true of every fibre over
some nonempty open subset of `Y`.

## Main results

* `AlgebraicGeometry.exists_open_forall_not_geometricallyReduced_fiber` gives a nonempty open
  subset over which every fibre is not geometrically reduced.

## Implementation notes

A finite type morphism is expressed by Mathlib's predicates `LocallyOfFiniteType` and
`QuasiCompact`. Geometric reducedness of the fibre over `y` is expressed as
`GeometricallyReduced (f.fiberToSpecResidueField y)`.

## References

* [Stacks Project, Tag 0577](https://stacks.math.columbia.edu/tag/0577)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-- If the generic fibre of a finite type morphism to an irreducible scheme is not geometrically
reduced, then every fibre over a suitable nonempty open subset of the target is not geometrically
reduced. -/
@[stacks 0577]
theorem exists_open_forall_not_geometricallyReduced_fiber
    {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IrreducibleSpace Y] [LocallyOfFiniteType f]
    [QuasiCompact f] (η : Y) (hη : IsGenericPoint η Set.univ)
    (h : ¬ GeometricallyReduced (f.fiberToSpecResidueField η)) :
    ∃ V : Set Y, IsOpen V ∧ V.Nonempty ∧
      ∀ y ∈ V, ¬ GeometricallyReduced (f.fiberToSpecResidueField y) := by
  obtain ⟨V, hV, Y', g, hgfin, hguh, hYint, hYaff, hdata⟩ :=
    exists_finiteUniversalHomeomorphism_geometricallyReduced_genericFiber f
  let : IsIntegral Y' := hYint
  let η' : Y' := genericPoint Y'
  have hη' : IsGenericPoint η' Set.univ := genericPoint_spec Y'
  let q : Y' ⟶ Y := g ≫ V.ι
  have hηV : η ∈ (V : Set Y) := (hη.mem_open_set_iff V.2).2 (by simpa using hV)
  have hhomeo : IsHomeomorph g := hguh.universally_isHomeomorph _ _ _ IsPullback.of_id_snd
  have hηrange : η ∈ Set.range q := by
    obtain ⟨z, hz⟩ := hhomeo.surjective ⟨η, hηV⟩
    exact ⟨z, congrArg V.ι hz⟩
  have hqclosure : closure (Set.range q) = Set.univ := Set.eq_univ_of_univ_subset <|
    (hη.mem_closed_set_iff isClosed_closure).mp (subset_closure hηrange)
  have hqη : q η' = η := by
    have hqgen : IsGenericPoint (q η') Set.univ := by
      simpa [Set.image_univ, hqclosure] using hη'.image q.continuous
    exact (hη.eq hqgen).symm
  dsimp only at hdata
  let P := pullback q f
  let X' := P.nilradical.subscheme
  let r : X' ⟶ P := P.nilradical.subschemeι
  let p : P ⟶ Y' := pullback.fst q f
  let f' : X' ⟶ Y' := r ≫ p
  have hred : ∀ ξ : Y', IsGenericPoint ξ Set.univ →
      GeometricallyReduced (f'.fiberToSpecResidueField ξ) := by
    simpa [P, X', r, p, f'] using hdata.2.2.2.2
  have hpb : IsPullback (pullback.snd q f) p f q :=
    (IsPullback.of_hasPullback q f).flip
  have hiff (z : Y') : GeometricallyReduced (p.fiberToSpecResidueField z) ↔
      GeometricallyReduced (f.fiberToSpecResidueField (q z)) :=
    Set.ext_iff.1 (geometricallyReduced_fiber_set_eq_preimage_of_isPullback f p (pullback.snd q f)
      q hpb) z
  have hPnot : ¬ GeometricallyReduced (p.fiberToSpecResidueField η') :=
    fun hp => h (hqη ▸ (hiff η').1 hp)
  have hPnotRed : ¬ IsReduced (p.fiber η') := by
    intro hredP
    let : IsReduced (pullback p (Y'.fromSpecResidueField η')) := by
      simpa only [Scheme.Hom.fiber] using hredP
    let s := pullback.fst p (Y'.fromSpecResidueField η')
    let j := pullback.snd r s
    let : UniversalHomeomorphism r :=
      universalHomeomorphism_nilradical_subschemeι P
    have hpbRed : IsPullback (pullback.fst r s) j r s :=
      IsPullback.of_hasPullback r s
    have hjhomeo : IsHomeomorph j :=
      (inferInstance : UniversalHomeomorphism r).universally_isHomeomorph _ _ _ hpbRed.flip
    let : Surjective j := ⟨hjhomeo.surjective⟩
    let : IsClosedImmersion r := inferInstance
    let : IsClosedImmersion j :=
      MorphismProperty.of_isPullback hpbRed (inferInstance : IsClosedImmersion r)
    let : IsIso j := isIso_of_isClosedImmersion_of_surjective j
    let e₀ := pullbackRightPullbackFstIso p (Y'.fromSpecResidueField η') r
    let ej : pullback r (pullback.fst p (Y'.fromSpecResidueField η')) ≅
        pullback p (Y'.fromSpecResidueField η') :=
      asIso j
    let e : f'.fiber η' ≅ p.fiber η' := by
      dsimp only [Scheme.Hom.fiber]
      exact e₀.symm ≪≫ ej
    have hgeoF : GeometricallyReduced (f'.fiberToSpecResidueField η') := hred η' hη'
    have hcomm : e.hom ≫ p.fiberToSpecResidueField η' =
        f'.fiberToSpecResidueField η' := by
      dsimp only [e, Scheme.Hom.fiberToSpecResidueField]
      show e₀.inv ≫ pullback.snd r (pullback.fst p (Y'.fromSpecResidueField η')) ≫
        pullback.snd p (Y'.fromSpecResidueField η') = _
      calc
        _ = e₀.inv ≫ (pullback.snd r (pullback.fst p (Y'.fromSpecResidueField η')) ≫
            pullback.snd p (Y'.fromSpecResidueField η')) := by simp
        _ = e₀.inv ≫ (e₀.hom ≫ pullback.snd (r ≫ p) (Y'.fromSpecResidueField η')) := by
          rw [← pullbackRightPullbackFstIso_hom_snd p (Y'.fromSpecResidueField η') r]
        _ = pullback.snd (r ≫ p) (Y'.fromSpecResidueField η') := by simp
    have hArrow : Arrow.mk (f'.fiberToSpecResidueField η') ≅
        Arrow.mk (p.fiberToSpecResidueField η') := Arrow.isoMk e (Iso.refl _) hcomm
    have : MorphismProperty.RespectsIso (@GeometricallyReduced : MorphismProperty Scheme) := by
      rw [GeometricallyReduced.eq_geometrically]
      infer_instance
    have hgeoP : GeometricallyReduced (p.fiberToSpecResidueField η') :=
      (MorphismProperty.arrow_iso_iff (@GeometricallyReduced : MorphismProperty Scheme)
        hArrow).mp hgeoF
    exact hPnot hgeoP
  let : LocallyOfFiniteType p := MorphismProperty.of_isPullback hpb ‹LocallyOfFiniteType f›
  let : QuasiCompact p := MorphismProperty.of_isPullback hpb ‹QuasiCompact f›
  obtain ⟨W, hWopen, hWnonempty, hWnotReduced⟩ :=
    exists_open_forall_not_isReduced_fiber p η' hη' hPnotRed
  have hnotGeoAt (y' : Y') (hy' : y' ∈ W) :
      ¬ GeometricallyReduced (f.fiberToSpecResidueField (q y')) := by
    intro hgeo
    have : GeometricallyReduced (p.fiberToSpecResidueField y') := (hiff y').2 hgeo
    exact hWnotReduced y' hy' (self_of_isIntegral_of_geometrically
      (GeometricallyReduced.geometrically_isReduced (f := p.fiberToSpecResidueField y')))
  refine ⟨V.ι '' (g '' W), V.ι.isOpenEmbedding.isOpenMap _ (hhomeo.isOpenMap _ hWopen),
    (hWnonempty.image g).image V.ι, ?_⟩
  rintro _ ⟨_, ⟨y', hy', rfl⟩, rfl⟩
  exact hnotGeoAt y' hy'

end AlgebraicGeometry

end
