module

public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndZariski.Basic
public import StacksFrontier.RingTheory.IndZariski.Defs
public import StacksCore.Tactic.StacksAttribute

/-!
# A localization is ind-Zariski

The localization of a commutative ring at an arbitrary multiplicative subset is ind-Zariski
over that ring: it is the filtered colimit of the localizations away from the single elements
of the multiplicative subset, each of which is a standard open immersion and hence a local
isomorphism.

## Main results

* `AlgebraicGeometry.ProEtale.isIndZariski_localization`: `A → Localization M` is ind-Zariski
  for every submonoid `M` of `A`.

## Implementation notes

The index category is the elements of `M` ordered by divisibility in `A`, which is directed
because `M` is closed under multiplication, and the transition maps are the canonical maps
`A_s → A_t` available whenever `s ∣ t`. The colimit cocone is the family of canonical maps
`A_s → Localization M`, and the colimit property is the universal property of
`Localization M`: a cocone makes every element of `M` invertible in its tip, because it does so
already at the single stage indexed by that element.

The result is stated for `Algebra.IsIndZariski`, whose index universe is pinned; the
`AlgebraicGeometry.ProEtale.IsIndZariski` spelling of Stacks 096N, whose index universe is a
free parameter, agrees with it when all three universes coincide, which is the generality in
which the two are used together.

## References

* [Stacks Project, Tag 096N](https://stacks.math.columbia.edu/tag/096N)
* [Stacks Project, Tag 096V](https://stacks.math.columbia.edu/tag/096V)
-/

@[expose] public noncomputable section

namespace AlgebraicGeometry.ProEtale

open CategoryTheory CategoryTheory.Limits

universe u

variable {A : Type u} [CommRing A]

/-- The elements of a submonoid, to be ordered by divisibility in the ambient ring. -/
private structure AwayIndex (M : Submonoid A) where
  /-- The underlying element of the submonoid. -/
  val : M

private instance awayIndexPreorder (M : Submonoid A) : Preorder (AwayIndex (A := A) M) where
  le i j := (i.val : A) ∣ (j.val : A)
  le_refl _ := dvd_rfl
  le_trans _ _ _ := dvd_trans

private instance awayIndexDirected (M : Submonoid A) :
    IsDirectedOrder (AwayIndex (A := A) M) where
  directed i j := ⟨⟨i.val * j.val⟩, ⟨j.val, by simp⟩, ⟨i.val, by simp [mul_comm]⟩⟩

private instance awayIndexNonempty (M : Submonoid A) : Nonempty (AwayIndex (A := A) M) := ⟨⟨1⟩⟩

/-- Morphisms out of a localization of `A` are determined by their values on the image of `A`. -/
private theorem hom_ext_of_isLocalization (S : Submonoid A) {L : Type u} [CommRing L] [Algebra A L]
    [IsLocalization S L] {Y : CommAlgCat.{u} A} {f g : CommAlgCat.of A L ⟶ Y}
    (h : ∀ a, f.hom (algebraMap A L a) = g.hom (algebraMap A L a)) : f = g := by
  exact CommAlgCat.hom_ext (AlgHom.coe_ringHom_injective
    (IsLocalization.ringHom_ext S (RingHom.ext h)))

/-- The transition map `A_s → A_t` of the divisibility diagram, for `s ∣ t`. -/
private def awayTransition {M : Submonoid A} (i j : AwayIndex (A := A) M) (h : i ≤ j) :
    Localization.Away (i.val : A) →ₐ[A] Localization.Away (j.val : A) where
  toRingHom := IsLocalization.Away.lift (i.val : A)
    (IsLocalization.Away.isUnit_of_dvd (x := (j.val : A)) h)
  commutes' := fun a => by simp

/-- The diagram of the localizations away from the single elements of `M`, indexed by
divisibility. -/
private abbrev awayDiagram (M : Submonoid A) : AwayIndex (A := A) M ⥤ CommAlgCat.{u} A where
  obj i := CommAlgCat.of A (Localization.Away (i.val : A))
  map {i j} f := CommAlgCat.ofHom (awayTransition (A := A) i j f.le)
  map_id i := by
    refine hom_ext_of_isLocalization (Submonoid.powers (i.val : A)) fun a => ?_
    simp [awayTransition]
  map_comp {i j k} f g := by
    refine hom_ext_of_isLocalization (Submonoid.powers (i.val : A)) fun a => ?_
    simp [awayTransition]

/-- The canonical map from a single-element localization to the localization at `M`. -/
private def awayToLocalization (M : Submonoid A) (i : AwayIndex (A := A) M) :
    Localization.Away (i.val : A) →ₐ[A] Localization M where
  toRingHom := IsLocalization.map (Localization M) (RingHom.id A)
    (Submonoid.powers_le.mpr i.val.property)
  commutes' := fun a => by simp

/-- The cocone of the divisibility diagram with tip `Localization M`. -/
private abbrev awayCocone (M : Submonoid A) : Cocone (awayDiagram (A := A) M) where
  pt := CommAlgCat.of A (Localization M)
  ι.app i := CommAlgCat.ofHom (awayToLocalization (A := A) M i)
  ι.naturality i j f := by
    refine hom_ext_of_isLocalization (Submonoid.powers (i.val : A)) fun a => ?_
    simp [awayTransition, awayToLocalization]

/-- The localization at `M` is the colimit of the localizations away from the elements
of `M`. -/
private def awayCocone_isColimit (M : Submonoid A) : IsColimit (awayCocone (A := A) M) := by
  classical
  refine IsColimit.ofExistsUnique fun t => ?_
  have hunit : ∀ s : M, IsUnit (algebraMap A (t.pt : Type u) s) := by
    intro s
    have hs : IsUnit (algebraMap A (Localization.Away (s : A)) (s : A)) :=
      IsLocalization.map_units _ ⟨(s : A), Submonoid.mem_powers _⟩
    simpa using hs.map ((t.ι.app ⟨s⟩).hom.toRingHom)
  let desc : Localization M →ₐ[A] (t.pt : Type u) :=
    { toRingHom := IsLocalization.lift hunit
      commutes' := fun a => by simp }
  refine ⟨CommAlgCat.ofHom desc, ?_, ?_⟩
  · intro i
    refine hom_ext_of_isLocalization (Submonoid.powers (i.val : A)) fun a => ?_
    simp [desc, awayToLocalization]
  · intro m _
    refine hom_ext_of_isLocalization M fun a => ?_
    simp

/-- The localization at a submonoid is a filtered colimit of local isomorphisms. -/
private theorem localization_ind (M : Submonoid A) :
    ObjectProperty.ind.{u} (fun C : CommAlgCat.{u} A => Algebra.IsLocalIso A C)
      (CommAlgCat.of A (Localization M)) := by
  refine ⟨AwayIndex (A := A) M, inferInstance, inferInstance,
    ⟨awayDiagram (A := A) M, (awayCocone (A := A) M).ι,
      awayCocone_isColimit (A := A) M⟩, fun i => ?_⟩
  have : Algebra.IsStandardOpenImmersion A (Localization.Away (i.val : A)) := inferInstance
  infer_instance

/-- The localization of `A` at an arbitrary submonoid is ind-Zariski over `A`: it is the
filtered colimit, along divisibility, of the localizations away from the single elements of the
submonoid, and each of those is a standard open immersion. -/
theorem isIndZariski_localization (M : Submonoid A) :
    Algebra.IsIndZariski A (Localization M) :=
  Algebra.isIndZariski_iff.mpr (localization_ind (A := A) M)

end AlgebraicGeometry.ProEtale

end
