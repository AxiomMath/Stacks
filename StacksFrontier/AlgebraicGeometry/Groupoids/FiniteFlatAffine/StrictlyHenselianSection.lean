module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.StrictlyHenselianFibre
public import StacksFrontier.AlgebraicGeometry.Groupoids.InvariantOpenSpecialization

/-!
# The sheet of a section of `U' ⟶ U` is an invariant open

Let `F : G' ⟶ G` be a morphism of groupoid schemes satisfying the hypotheses of
[Stacks Project, Tag 0DT9], let `C` be strictly henselian, let `p'` be a point of `Spec C'` over
the closed point of `Spec C`, and let `σ : U ⟶ U'` be a **section** of `f : U' ⟶ U` whose range
is open and contains the fibre `U'_{p'}`. Then the range of `σ` is an **invariant** open of `U'`.

## Main results

* `AlgebraicGeometry.GroupoidScheme.isClosedMap_objectsToInvariantSpectrum`: the quotient
  morphism `U ⟶ Spec C` is a closed map.
* `AlgebraicGeometry.GroupoidScheme.mem_fibre_of_section_of_mem_closedFibre`: the range of a
  section meets the preimage of the closed fibre of `U` exactly in `U'_{p'}`.
* `AlgebraicGeometry.GroupoidScheme.isInvariantSet_range_of_section`: **the range of the section
  is invariant.**

## References

* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory Stacks.Groupoids Stacks.Morphisms

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)

/-- **The quotient morphism `U ⟶ Spec C` is a closed map.** -/
theorem isClosedMap_objectsToInvariantSpectrum (G : GroupoidScheme S) [IsAffine G.objects.left]
    [IsAffine G.arrows.left] [IsFiniteLocallyFree G.source.left]
    [IsFiniteLocallyFree G.target.left] :
    IsClosedMap (objectsToInvariantSpectrum G).base := by
  have hint : IsIntegralHom
      (Spec.map (CommRingCat.ofHom (Subring.subtype (invariantRing G)))) :=
    IsIntegralHom.SpecMap_iff.mpr (isIntegral_invariantRing G)
  have hclosed : UniversallyClosed (objectsToInvariantSpectrum G) := by
    change UniversallyClosed (G.objects.left.isoSpec.hom ≫
      Spec.map (CommRingCat.ofHom (Subring.subtype (invariantRing G))))
    infer_instance
  exact (objectsToInvariantSpectrum G).isClosedMap

/-- A section of `f : U' ⟶ U` is a section on underlying points. -/
theorem base_comp_base_of_section {σ : G.objects.left ⟶ G'.objects.left}
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left) (x : G.objects.left) :
    F.mapObjects.left.base (σ.base x) = x :=
  congrArg (fun k : G.objects.left ⟶ G.objects.left => k.base x) hσ

section StrictlyHenselian

variable [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]
  [StrictlyHenselianLocalRing (invariantRing G)]

/-- **A point of the range of a section lying over the closed fibre of `U` lies in `U'_{p'}`.** -/
theorem mem_fibre_of_section_of_mem_closedFibre
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    (p' : Spec (.of (invariantRing G')))
    (hp' : (Spec.map (CommRingCat.ofHom (invariantRingMap F))).base p' =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G))))
    {σ : G.objects.left ⟶ G'.objects.left}
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left)
    (hfib : ∀ u' : G'.objects.left, (objectsToInvariantSpectrum G').base u' = p' →
      u' ∈ Set.range σ.base)
    (u : G.objects.left)
    (hu : (objectsToInvariantSpectrum G).base u =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G)))) :
    (objectsToInvariantSpectrum G').base (σ.base u) = p' := by
  obtain ⟨ι, hι⟩ :=
    (bijective_invariantFibreMap_of_strictlyHenselian F hsource htarget hstab p' hp').surjective
      (⟨u, hu.trans hp'.symm⟩ :
        {v : G.objects.left // (objectsToInvariantSpectrum G).base v =
          (Spec.map (CommRingCat.ofHom (invariantRingMap F))).base p'})
  have hιf : F.mapObjects.left.base ι.1 = u := congrArg Subtype.val hι
  obtain ⟨a, ha⟩ := hfib ι.1 ι.2
  have hau : a = u := by rw [← hιf, ← ha, base_comp_base_of_section F hσ]
  rw [← hau, ha]
  exact ι.2

/-- **The range of a section of `f : U' ⟶ U` containing the fibre `U'_{p'}` is invariant.** -/
theorem isInvariantSet_range_of_section
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    (p' : Spec (.of (invariantRing G')))
    (hp' : (Spec.map (CommRingCat.ofHom (invariantRingMap F))).base p' =
      (IsLocalRing.closedPoint (invariantRing G) : Spec (.of (invariantRing G))))
    {σ : G.objects.left ⟶ G'.objects.left}
    (hσ : σ ≫ F.mapObjects.left = 𝟙 G.objects.left)
    (hopen : IsOpen (Set.range σ.base))
    (hfib : ∀ u' : G'.objects.left, (objectsToInvariantSpectrum G').base u' = p' →
      u' ∈ Set.range σ.base) :
    IsInvariantSet G' (Set.range σ.base) := by
  refine isInvariantSet_of_forall_exists_mem_closure G' (isClosedMap_source G') hopen
    (Z := {u' : G'.objects.left | (objectsToInvariantSpectrum G').base u' = p'})
    hfib
    (isInvariantSet_fibre_objectsToInvariantSpectrum G' p') ?_
  rintro v ⟨u, rfl⟩
  obtain ⟨w, hw, hwq⟩ := exists_mem_closure_fibre_closedPoint (objectsToInvariantSpectrum G)
    (isClosedMap_objectsToInvariantSpectrum G) u
  refine ⟨σ.base w, ?_, ?_⟩
  · exact mem_fibre_of_section_of_mem_closedFibre F hsource htarget hstab p' hp' hσ hfib w hwq
  · exact specializes_iff_mem_closure.mp
      ((specializes_iff_mem_closure.mpr hw).map σ.base.hom.continuous)

end StrictlyHenselian

end AlgebraicGeometry.GroupoidScheme

end

end
