module

public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.StabilizerBaseChangeMorphism
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.Morphisms.FieldPointPurelyInseparable

/-!
# The fibres of a morphism of affine groupoid schemes over the invariant spectra

Let `F : G' ⟶ G` be a morphism of groupoid schemes with `U`, `R`, `U'`, `R'` affine and `s`, `t`,
`s'`, `t'` finite locally free, and write `q : U ⟶ M` and `q' : U' ⟶ M'` for the two quotient
morphisms to the spectra of the invariant rings. Fix a point `p'` of `M'` and let `p` be its
image in `M`. This file compares the two fibres `U'_{p'}` and `U_p`:

* if the square formed by `F` and the two **source** maps is cartesian then
  `U'_{p'} ⟶ U_p` is **surjective**, with no further hypothesis;
* if the squares formed by `F` and the two **target** maps and by `F` and the two **stabilizer**
  group schemes are cartesian, and the residue field extension `κ(u)/κ(p)` is purely
  inseparable at the image point `u`, then `U'_{p'} ⟶ U_p` is **injective**.

Together these are the first half of the "Claim" in the proof of [Stacks Project, Tag 0DT9] —
that `U'_{p'} ⟶ U_p` is bijective — the half that does not mention the residue fields of `U'`.

## Main results

All names are in the namespace `AlgebraicGeometry`.

* `GroupoidScheme.exists_objectsToInvariantSpectrum_base_eq_of_base_eq`: **surjectivity.**
* `GroupoidScheme.eq_of_objectsToInvariantSpectrum_base_eq_of_isPurelyInseparable`:
  **injectivity.**
* `GroupoidScheme.invariantFibreMap`: the map of fibres itself.
* `GroupoidScheme.bijective_invariantFibreMap`: **the two together, as the bijection
  `U'_{p'} ⟶ U_p` of the source text's Claim.**

## Implementation notes

Surjectivity is cheaper than the source text's argument. The source text deduces it from the
hypothesis that the scheme-theoretic fibres of `s'` and `s` are isomorphic; what is actually
needed is only that a compatible pair of points of `R` and `U'` is in the image of `R'`, and for
a cartesian square of *schemes* that is unconditional
(`AlgebraicGeometry.Scheme.exists_preimage_of_isPullback`: the tensor product of the
two residue fields over the residue field of the common image is a nonzero ring, because it is a
tensor product of field extensions). So no hypothesis on `f : U' ⟶ U` is needed, and in
particular étaleness is not used. The orbit description of the fibres of `q`, which is where
`U_p = t(s^{-1}(u))` enters, is Tag 03BL in the form
`AlgebraicGeometry.GroupoidScheme.base_objectsToInvariantSpectrum_eq_iff`.

Injectivity is the source text's argument. Two points of `U'_{p'}` over the same `u` are joined
by an arrow `r'` of `R'`, again by Tag 03BL. Testing on the residue field of `r'`, the source
and the target of the image of `r'` in `R` are two field-valued points of `U` with the same
image point `u` and the same composite with `q`, because `q` coequalizes `s` and `t`; pure
inseparability of `κ(u)/κ(p)` forces them to be equal
(`AlgebraicGeometry.eq_of_comp_eq_of_isPurelyInseparable`, which is the source text's comparison
of the two towers of residue fields). The cartesian target and stabilizer squares then return
an arrow of `R'` with equal source and target, by
`AlgebraicGeometry.source_eq_target_of_mapArrows_source_eq_target`, so the two points agree.

Étaleness of `f : U' ⟶ U` is used by neither statement: it enters Tag 0DT9 only through the
*other* half of the Claim, the identification of the residue fields of the points of `U'_{p'}`
with those of `U_p`.

## References

* [Stacks Project, Tag 03BL](https://stacks.math.columbia.edu/tag/03BL)
* [Stacks Project, Tag 0DT9](https://stacks.math.columbia.edu/tag/0DT9)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Stacks.Groupoids
open Stacks.Morphisms

noncomputable section

universe u

namespace AlgebraicGeometry.GroupoidScheme

variable {S : Scheme.{u}} {G G' : GroupoidScheme S} (F : GroupoidScheme.Hom G' G)

/-- The image in `M` of the class of a point of `U'` is the class of its image in `U`, read on
underlying points. -/
theorem base_objectsToInvariantSpectrum_mapObjects (u' : G'.objects.left) :
    (objectsToInvariantSpectrum G).base (F.mapObjects.left.base u') =
      (Spec.map (CommRingCat.ofHom (invariantRingMap F))).base
        ((objectsToInvariantSpectrum G').base u') := by
  change (F.mapObjects.left ≫ objectsToInvariantSpectrum G).base u' =
    (objectsToInvariantSpectrum G' ≫ Spec.map (CommRingCat.ofHom (invariantRingMap F))).base u'
  rw [mapObjects_comp_objectsToInvariantSpectrum]

/-- **The map of fibres over the invariant spectra**: a point of `U'` lying over `p'` is carried
by `F` to a point of `U` lying over the image of `p'` in `M`. -/
def invariantFibreMap (p' : Spec (.of (invariantRing G'))) :
    {u' : G'.objects.left // (objectsToInvariantSpectrum G').base u' = p'} →
      {v : G.objects.left // (objectsToInvariantSpectrum G).base v =
        (Spec.map (CommRingCat.ofHom (invariantRingMap F))).base p'} :=
  fun u' => ⟨F.mapObjects.left.base u'.1, by
    rw [base_objectsToInvariantSpectrum_mapObjects, u'.2]⟩

/-! ### Surjectivity of the map of fibres -/

section Surjective

variable [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]

/-- **The fibre of `U'` over a point `p'` of `M'` surjects onto the fibre of `U` over the image
of `p'` in `M`**, as soon as the square formed by `F` and the two source maps is cartesian.

The fibre of `U'` over `p'` is nonempty because `U' ⟶ M'` is surjective; its image point in `U`
has the same class in `M` as the given point `u`, so an arrow `r` of `R` joins the two; the
cartesian source square lifts `r` to an arrow `r'` of `R'` out of the chosen point of the fibre,
and the target of `r'` is the point asked for, because `q'` coequalizes `s'` and `t'`. -/
theorem exists_objectsToInvariantSpectrum_base_eq_of_base_eq
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (p' : Spec (.of (invariantRing G'))) (u : G.objects.left)
    (hu : (objectsToInvariantSpectrum G).base u =
      (Spec.map (CommRingCat.ofHom (invariantRingMap F))).base p') :
    ∃ u' : G'.objects.left,
      (objectsToInvariantSpectrum G').base u' = p' ∧ F.mapObjects.left.base u' = u := by
  obtain ⟨w', hw'⟩ := surjective_objectsToInvariantSpectrum G' p'
  have hclass : (objectsToInvariantSpectrum G).base u =
      (objectsToInvariantSpectrum G).base (F.mapObjects.left.base w') := by
    rw [hu, base_objectsToInvariantSpectrum_mapObjects, hw']
  obtain ⟨r, hrt, hrs⟩ := (base_objectsToInvariantSpectrum_eq_iff G u
    (F.mapObjects.left.base w')).mp hclass
  obtain ⟨r', hr'arrows, hr'source⟩ :=
    Scheme.exists_preimage_of_isPullback hsource r w' hrs
  refine ⟨G'.target.left.base r', ?_, ?_⟩
  · have hst : (objectsToInvariantSpectrum G').base (G'.target.left.base r') =
        (objectsToInvariantSpectrum G').base (G'.source.left.base r') := by
      change (G'.target.left ≫ objectsToInvariantSpectrum G').base r' =
        (G'.source.left ≫ objectsToInvariantSpectrum G').base r'
      rw [source_comp_objectsToInvariantSpectrum]
    rw [hst, hr'source, hw']
  · have hmt : F.mapObjects.left.base (G'.target.left.base r') =
        G.target.left.base (F.mapArrows.left.base r') := by
      change (G'.target.left ≫ F.mapObjects.left).base r' =
        (F.mapArrows.left ≫ G.target.left).base r'
      rw [F.map_target_left]
    rw [hmt, hr'arrows, hrt]

end Surjective

/-! ### Injectivity of the map of fibres -/

section Injective

variable [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
  [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]

/-- **Two points of the fibre of `U'` over a point of `M'` with the same image `v` in `U` are
equal**, as soon as the squares formed by `F` and the two target maps and by `F` and the two
stabilizer group schemes are cartesian and a field-valued point of `U` at `v` is determined by
its composite with the quotient morphism `q : U ⟶ M`.

This is the injectivity half of the "Claim" of [Stacks Project, Tag 0DT9]. The two points are
joined by an arrow `r'` of `R'`; the source and the target of its image in `R`, tested on the
residue field of `r'`, are two field-valued points of `U` with the same image point `v` and the
same composite with `q`, so the separating hypothesis makes them equal. The cartesian stabilizer
square then makes `r'` itself an arrow with equal source and target.

The separating hypothesis holds whenever `κ(v)/κ(q v)` is purely inseparable, which is the form
the source text uses and which
`eq_of_objectsToInvariantSpectrum_base_eq_of_isPurelyInseparable` records. -/
theorem eq_of_objectsToInvariantSpectrum_base_eq_of_separating
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    {u'₁ u'₂ : G'.objects.left} {v : G.objects.left}
    (hu₁ : F.mapObjects.left.base u'₁ = v) (hu₂ : F.mapObjects.left.base u'₂ = v)
    (hq : (objectsToInvariantSpectrum G').base u'₁ = (objectsToInvariantSpectrum G').base u'₂)
    (hsep : ∀ (K : Type u) (_ : Field K) (α β : Spec (.of K) ⟶ G.objects.left),
      α.base (IsLocalRing.closedPoint K) = v → β.base (IsLocalRing.closedPoint K) = v →
      α ≫ objectsToInvariantSpectrum G = β ≫ objectsToInvariantSpectrum G → α = β) :
    u'₁ = u'₂ := by
  obtain ⟨r', hrt, hrs⟩ := (base_objectsToInvariantSpectrum_eq_iff G' u'₁ u'₂).mp hq
  let K : Type u := ↥(G'.arrows.left.residueField r')
  let _ : Field K := inferInstanceAs (Field ↥(G'.arrows.left.residueField r'))
  let ρ : Spec (.of K) ⟶ G'.arrows.left := G'.arrows.left.fromSpecResidueField r'
  have hρbase : ρ.base (IsLocalRing.closedPoint K) = r' :=
    G'.arrows.left.fromSpecResidueField_apply r' _
  -- the source and the target of the image of `r'` in `R`, as field-valued points of `U`
  have hsrc : (ρ ≫ F.mapArrows.left ≫ G.source.left).base (IsLocalRing.closedPoint K) = v := by
    rw [F.map_source_left]
    change F.mapObjects.left.base (G'.source.left.base (ρ.base _)) = v
    rw [hρbase, hrs, hu₂]
  have htgt : (ρ ≫ F.mapArrows.left ≫ G.target.left).base (IsLocalRing.closedPoint K) = v := by
    rw [F.map_target_left]
    change F.mapObjects.left.base (G'.target.left.base (ρ.base _)) = v
    rw [hρbase, hrt, hu₁]
  -- they have the same composite with the quotient morphism
  have hcomp : (ρ ≫ F.mapArrows.left ≫ G.source.left) ≫ objectsToInvariantSpectrum G =
      (ρ ≫ F.mapArrows.left ≫ G.target.left) ≫ objectsToInvariantSpectrum G := by
    simp only [Category.assoc, source_comp_objectsToInvariantSpectrum]
  -- hence the image of `r'` in `R` has equal source and target
  have harrow : (ρ ≫ F.mapArrows.left) ≫ G.source.left =
      (ρ ≫ F.mapArrows.left) ≫ G.target.left := by
    simpa only [Category.assoc] using hsep K inferInstance _ _ hsrc htgt hcomp
  have hr' := source_eq_target_of_mapArrows_source_eq_target F htarget hstab ρ harrow
  have := congrArg (fun m : Spec (.of K) ⟶ G'.objects.left =>
    m.base (IsLocalRing.closedPoint K)) hr'
  change G'.source.left.base (ρ.base _) = G'.target.left.base (ρ.base _) at this
  rw [hρbase, hrs, hrt] at this
  exact this.symm

/-- **Two points of the fibre of `U'` over a point of `M'` with the same image `u` in `U` are
equal**, as soon as the squares formed by `F` and the two target maps and by `F` and the two
stabilizer group schemes are cartesian and the residue field extension `κ(u)/κ(q u)` of the
quotient morphism `q : U ⟶ M` is purely inseparable.

This is the injectivity half of the "Claim" of [Stacks Project, Tag 0DT9] in the form the source
text has it: pure inseparability of `κ(u)/κ(p)` is exactly what makes the source text's two
towers of residue fields induce the same map `κ(u) ⟶ κ(r')`. -/
theorem eq_of_objectsToInvariantSpectrum_base_eq_of_isPurelyInseparable
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    {u'₁ u'₂ : G'.objects.left} {u : G.objects.left}
    (hu₁ : F.mapObjects.left.base u'₁ = u) (hu₂ : F.mapObjects.left.base u'₂ = u)
    (hq : (objectsToInvariantSpectrum G').base u'₁ = (objectsToInvariantSpectrum G').base u'₂)
    [Algebra ((Spec (.of (invariantRing G))).residueField
        ((objectsToInvariantSpectrum G).base u)) (G.objects.left.residueField u)]
    (hcompat : algebraMap ((Spec (.of (invariantRing G))).residueField
          ((objectsToInvariantSpectrum G).base u)) (G.objects.left.residueField u) =
      ((objectsToInvariantSpectrum G).residueFieldMap u).hom)
    [IsPurelyInseparable ((Spec (.of (invariantRing G))).residueField
        ((objectsToInvariantSpectrum G).base u)) (G.objects.left.residueField u)] :
    u'₁ = u'₂ :=
  eq_of_objectsToInvariantSpectrum_base_eq_of_separating F htarget hstab hu₁ hu₂ hq
    fun _ _ _ _ hα hβ h =>
      eq_of_comp_eq_of_isPurelyInseparable (objectsToInvariantSpectrum G) hα hβ h hcompat

end Injective

/-! ### The bijection of fibres -/

section Bijective

variable [IsAffine G.objects.left] [IsAffine G.arrows.left]
  [IsAffine G'.objects.left] [IsAffine G'.arrows.left]
  [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
  [IsFiniteLocallyFree G'.source.left] [IsFiniteLocallyFree G'.target.left]

/-- **The bijection of fibres of the "Claim" of [Stacks Project, Tag 0DT9]**: the map
`U'_{p'} ⟶ U_p` is bijective, as soon as the squares formed by `F` and the two source maps, the
two target maps and the two stabilizer group schemes are cartesian and a field-valued point of
`U` at a point of `U_p` is determined by its composite with the quotient morphism.

Surjectivity needs only the cartesian source square; injectivity is the stabilizer argument,
whose residue field input is the separating hypothesis. See
`eq_of_objectsToInvariantSpectrum_base_eq_of_isPurelyInseparable` for the pure-inseparability
form of that hypothesis, which is how the source text supplies it. -/
theorem bijective_invariantFibreMap
    (hsource : IsPullback F.mapArrows.left G'.source.left G.source.left F.mapObjects.left)
    (htarget : IsPullback F.mapArrows.left G'.target.left G.target.left F.mapObjects.left)
    (hstab : IsPullback (stabilizerMap F).left (stabilizer G').hom (stabilizer G).hom
      F.mapObjects.left)
    (p' : Spec (.of (invariantRing G')))
    (hsep : ∀ v : G.objects.left, (objectsToInvariantSpectrum G).base v =
        (Spec.map (CommRingCat.ofHom (invariantRingMap F))).base p' →
      ∀ (K : Type u) (_ : Field K) (α β : Spec (.of K) ⟶ G.objects.left),
        α.base (IsLocalRing.closedPoint K) = v → β.base (IsLocalRing.closedPoint K) = v →
        α ≫ objectsToInvariantSpectrum G = β ≫ objectsToInvariantSpectrum G → α = β) :
    Function.Bijective (invariantFibreMap F p') := by
  refine ⟨fun a b hab => ?_, fun v => ?_⟩
  · have hval : F.mapObjects.left.base a.1 = F.mapObjects.left.base b.1 :=
      congrArg Subtype.val hab
    exact Subtype.ext (eq_of_objectsToInvariantSpectrum_base_eq_of_separating F htarget hstab
      rfl hval.symm (a.2.trans b.2.symm) (hsep _ (invariantFibreMap F p' a).2))
  · obtain ⟨u', hu'q, hu'f⟩ :=
      exists_objectsToInvariantSpectrum_base_eq_of_base_eq F hsource p' v.1 v.2
    exact ⟨⟨u', hu'q⟩, Subtype.ext hu'f⟩

end Bijective

end AlgebraicGeometry.GroupoidScheme

end

end
