module

public import Mathlib.Algebra.Category.Ring.FilteredColimits
public import Mathlib.RingTheory.Localization.Away.Basic
public import StacksFrontier.RingTheory.Localization.AwayToAtPrime

/-!
# A localization as the filtered colimit of its principal localizations

Let `M` be a submonoid of a commutative ring `R`. The localization `R[M⁻¹]` is the filtered
colimit of the principal localizations `R[a⁻¹]` for `a` running through `M`, the index being
ordered by divisibility and the transition maps being the universal maps of the principal
localizations.

## Main definitions

* `Localization.AwayIndex` is the index: an element of `M`, ordered by divisibility.
* `Localization.awayDiagram` sends such an index `a` to `Localization.Away a`, in `CommRingCat`.
* `Localization.awayCocone` is the cocone with vertex `Localization M`.

## Main results

* `Localization.isColimitAwayCocone`: the cocone is a colimit.

## Implementation notes

The index is a one-field structure rather than the submonoid itself: the order is divisibility,
which is not the order a subtype of `R` would otherwise carry, so putting it on the submonoid
directly would clash with the subtype order whenever `R` is ordered.

A map out of `Localization.Away a` is determined by its restriction along `R`, so every
compatibility in sight is checked on the image of `R`, through `Localization.away_ringHom_ext`.
The structure map of an arbitrary cocone is read off its leg at the index `1`, which is the
bottom of the order.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Localization

variable {R : Type u} [CommRing R] (M : Submonoid R)

/-- An index for the principal localizations inside `Localization M`: an element of `M`. The
order is divisibility in `R`, so that `a ≤ b` exactly when `R[b⁻¹]` is a further localization
of `R[a⁻¹]`. -/
structure AwayIndex where
  /-- The element of `M` at which this index localizes. -/
  elem : M

variable {M}

/-- The divisibility preorder on `Localization.AwayIndex M`: `a ≤ b` when `a` divides `b` in
`R`. -/
instance : Preorder (AwayIndex M) where
  le a b := (a.elem : R) ∣ (b.elem : R)
  le_refl _ := dvd_rfl
  le_trans _ _ _ := dvd_trans

/-- The index is directed: `a` and `b` both lie below their product. -/
instance : IsDirected (AwayIndex M) (· ≤ ·) :=
  ⟨fun a b => ⟨⟨a.elem * b.elem⟩, dvd_mul_right _ _, dvd_mul_left _ _⟩⟩

/-- The index is nonempty: it contains `1`. -/
instance : Nonempty (AwayIndex M) := ⟨⟨1⟩⟩

/-- If `a ≤ b` then `a` becomes a unit in `R[b⁻¹]`, being a divisor of `b`. -/
theorem isUnit_algebraMap_away_of_le {a b : AwayIndex M} (h : a ≤ b) :
    IsUnit (algebraMap R (Localization.Away (b.elem : R)) (a.elem : R)) := by
  obtain ⟨c, hc⟩ := h
  refine isUnit_of_mul_isUnit_left (y := algebraMap R (Localization.Away (b.elem : R)) c) ?_
  rw [← map_mul, ← hc]
  exact IsLocalization.Away.algebraMap_isUnit (b.elem : R)

/-- The transition map `R[a⁻¹] → R[b⁻¹]` attached to `a ≤ b`. -/
def awayTransition {a b : AwayIndex M} (h : a ≤ b) :
    Localization.Away (a.elem : R) →+* Localization.Away (b.elem : R) :=
  IsLocalization.Away.lift (S := Localization.Away (a.elem : R)) (a.elem : R)
    (isUnit_algebraMap_away_of_le h)

/-- The transition map `R[a⁻¹] → R[b⁻¹]` commutes with the maps from `R`. -/
theorem awayTransition_algebraMap {a b : AwayIndex M} (h : a ≤ b) (r : R) :
    awayTransition h (algebraMap R (Localization.Away (a.elem : R)) r) =
      algebraMap R (Localization.Away (b.elem : R)) r := by
  unfold awayTransition
  rw [IsLocalization.Away.lift_eq]

/-- Two ring maps out of a principal localization whose restrictions along `R` both equal `f`
are equal. -/
theorem away_ringHom_ext {a : AwayIndex M} {A : Type*} [CommRing A] (f : R →+* A)
    (φ ψ : Localization.Away (a.elem : R) →+* A)
    (hφ : ∀ r, φ (algebraMap R (Localization.Away (a.elem : R)) r) = f r)
    (hψ : ∀ r, ψ (algebraMap R (Localization.Away (a.elem : R)) r) = f r) :
    φ = ψ := by
  refine IsLocalization.ringHom_ext (Submonoid.powers (a.elem : R)) ?_
  ext r
  exact (hφ r).trans (hψ r).symm

/-- Two ring maps out of `Localization M` whose restrictions along `R` both equal `f` are
equal. -/
theorem localization_ringHom_ext {A : Type*} [CommRing A] (f : R →+* A)
    (φ ψ : Localization M →+* A)
    (hφ : ∀ r, φ (algebraMap R (Localization M) r) = f r)
    (hψ : ∀ r, ψ (algebraMap R (Localization M) r) = f r) :
    φ = ψ := by
  refine IsLocalization.ringHom_ext M ?_
  ext r
  exact (hφ r).trans (hψ r).symm

/-- The diagram of principal localizations `a ↦ R[a⁻¹]` over the index. -/
def awayDiagram (M : Submonoid R) : AwayIndex M ⥤ CommRingCat.{u} where
  obj a := CommRingCat.of (Localization.Away (a.elem : R))
  map {_ _} h := CommRingCat.ofHom (awayTransition h.le)
  map_id a := by
    apply CommRingCat.hom_ext
    apply away_ringHom_ext (algebraMap R (Localization.Away (a.elem : R)))
    · exact awayTransition_algebraMap (le_refl a)
    · exact fun _ => rfl
  map_comp {a b c} f g := by
    apply CommRingCat.hom_ext
    apply away_ringHom_ext (algebraMap R (Localization.Away (c.elem : R)))
    · exact awayTransition_algebraMap (f.le.trans g.le)
    · intro r
      change (awayTransition g.le) ((awayTransition f.le) _) = _
      rw [awayTransition_algebraMap, awayTransition_algebraMap]

/-- The map `R[a⁻¹] → R[M⁻¹]`, an element of `M` being invertible in `R[M⁻¹]`. -/
def awayLeg (a : AwayIndex M) :
    Localization.Away (a.elem : R) →+* Localization M :=
  IsLocalization.Away.lift (S := Localization.Away (a.elem : R)) (a.elem : R)
    (IsLocalization.map_units (Localization M) a.elem)

/-- The leg `R[a⁻¹] → R[M⁻¹]` sends the image of `r : R` to the image of `r`. -/
theorem awayLeg_algebraMap (a : AwayIndex M) (r : R) :
    awayLeg a (algebraMap R (Localization.Away (a.elem : R)) r) =
      algebraMap R (Localization M) r := by
  unfold awayLeg
  rw [IsLocalization.Away.lift_eq]

/-- The leg `R[a⁻¹] → R[M⁻¹]` composed with `R → R[a⁻¹]` is the map `R → R[M⁻¹]`. -/
theorem awayLeg_comp_algebraMap (a : AwayIndex M) :
    (awayLeg a).comp (algebraMap R (Localization.Away (a.elem : R))) =
      algebraMap R (Localization M) :=
  RingHom.ext (awayLeg_algebraMap a)

/-- The cocone on `Localization.awayDiagram` with vertex `Localization M`. -/
def awayCocone (M : Submonoid R) : Cocone (awayDiagram M) where
  pt := CommRingCat.of (Localization M)
  ι :=
    { app a := CommRingCat.ofHom (awayLeg a)
      naturality := by
        intro a b h
        apply CommRingCat.hom_ext
        change (awayLeg b).comp (awayTransition h.le) =
          (RingHom.id (Localization M)).comp (awayLeg a)
        rw [RingHom.id_comp]
        apply away_ringHom_ext (algebraMap R (Localization M))
        · intro r
          change (awayLeg b) ((awayTransition h.le)
            (algebraMap R (Localization.Away (a.elem : R)) r)) = _
          rw [awayTransition_algebraMap, awayLeg_algebraMap]
        · exact awayLeg_algebraMap a }

/-- The structure map `R → s.pt` of a cocone `s` on `Localization.awayDiagram`, read off its leg
at the index `1`. -/
def awayCoconeStr {M : Submonoid R} {s : Cocone (awayDiagram M)} : R →+* s.pt :=
  (s.ι.app ⟨1⟩).hom.comp (algebraMap R (Localization.Away ((⟨1⟩ : AwayIndex M).elem : R)))

/-- For a cocone `s` on `Localization.awayDiagram`, the leg at any index `a`, restricted along
`R → R[a⁻¹]`, is the structure map `Localization.awayCoconeStr`. -/
theorem awayCoconeStr_eq {s : Cocone (awayDiagram M)} (a : AwayIndex M) (r : R) :
    (s.ι.app a).hom (algebraMap R (Localization.Away (a.elem : R)) r) =
      awayCoconeStr (s := s) r := by
  have hoa : (⟨1⟩ : AwayIndex M) ≤ a := one_dvd _
  have hnat : (s.ι.app a).hom.comp (awayTransition hoa) = (s.ι.app ⟨1⟩).hom := by
    have h := s.ι.naturality (homOfLE hoa)
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id] at h
    exact congrArg CommRingCat.Hom.hom h
  have hr := RingHom.congr_fun hnat
    (algebraMap R (Localization.Away ((⟨1⟩ : AwayIndex M).elem : R)) r)
  change (s.ι.app a).hom (algebraMap R (Localization.Away (a.elem : R)) r) =
    (s.ι.app ⟨1⟩).hom (algebraMap R (Localization.Away ((⟨1⟩ : AwayIndex M).elem : R)) r)
  rw [← awayTransition_algebraMap hoa r]
  exact hr

/-- The structure map `Localization.awayCoconeStr` of a cocone sends every element of `M` to a
unit. -/
theorem isUnit_awayCoconeStr {s : Cocone (awayDiagram M)} (y : M) :
    IsUnit (awayCoconeStr (s := s) (y : R)) := by
  rw [← awayCoconeStr_eq (s := s) ⟨y⟩ (y : R)]
  exact IsUnit.map (s.ι.app ⟨y⟩).hom
    (IsLocalization.Away.algebraMap_isUnit
      (S := Localization.Away ((⟨y⟩ : AwayIndex M).elem : R)) (y : R))

/-- The map `R[M⁻¹] → s.pt` descended from a cocone `s`. -/
def awayCoconeDesc (s : Cocone (awayDiagram M)) : Localization M →+* s.pt :=
  IsLocalization.lift (M := M) (g := awayCoconeStr (s := s)) isUnit_awayCoconeStr

/-- The descended map `R[M⁻¹] → s.pt` restricts along `R` to `Localization.awayCoconeStr`. -/
theorem awayCoconeDesc_algebraMap (s : Cocone (awayDiagram M)) (r : R) :
    awayCoconeDesc s (algebraMap R (Localization M) r) = awayCoconeStr (s := s) r := by
  unfold awayCoconeDesc
  rw [IsLocalization.lift_eq]

/-- `Localization M` is the filtered colimit of the principal localizations
`Localization.Away a` for `a` in `M`. -/
def isColimitAwayCocone (M : Submonoid R) : IsColimit (awayCocone M) :=
  IsColimit.mk (fun s => CommRingCat.ofHom (awayCoconeDesc s))
    (by
      intro s a
      apply CommRingCat.hom_ext
      change (awayCoconeDesc s).comp (awayLeg a) = (s.ι.app a).hom
      apply away_ringHom_ext (awayCoconeStr (s := s))
      · intro r
        change (awayCoconeDesc s) ((awayLeg a) (algebraMap R _ r)) = _
        rw [awayLeg_algebraMap, awayCoconeDesc_algebraMap]
      · exact awayCoconeStr_eq a)
    (by
      intro s m hm
      apply CommRingCat.hom_ext
      apply localization_ringHom_ext (awayCoconeStr (s := s))
      · intro r
        have hmr := RingHom.congr_fun (congrArg CommRingCat.Hom.hom (hm ⟨1⟩))
          (algebraMap R (Localization.Away ((⟨1⟩ : AwayIndex M).elem : R)) r)
        change m.hom ((awayLeg (⟨1⟩ : AwayIndex M))
          (algebraMap R (Localization.Away ((⟨1⟩ : AwayIndex M).elem : R)) r)) =
          awayCoconeStr (s := s) r at hmr
        rwa [awayLeg_algebraMap] at hmr
      · exact awayCoconeDesc_algebraMap s)

/-- At the submonoid `p.primeCompl` the cocone legs are the canonical maps
`R[a⁻¹] → R_p` of `localizationAwayToAtPrime`. -/
theorem awayLeg_eq_localizationAwayToAtPrime (p : Ideal R) [p.IsPrime]
    (a : AwayIndex p.primeCompl) :
    awayLeg a = localizationAwayToAtPrime (a.elem : R) p a.elem.property := by
  apply away_ringHom_ext (algebraMap R (Localization.AtPrime p))
  · exact awayLeg_algebraMap a
  · intro r
    simp only [localizationAwayToAtPrime, IsLocalization.map_eq, RingHom.id_apply]

/-- The forgetful functor from `CommRingCat` preserves the colimit of
`Localization.awayDiagram M`. -/
instance preservesColimit_awayDiagram_forget (M : Submonoid R) :
    PreservesColimit (awayDiagram M) (forget CommRingCat.{u}) := by
  have h : PreservesFilteredColimits (forget CommRingCat.{u}) := inferInstance
  exact (h.preserves_filtered_colimits (AwayIndex M)).preservesColimit

end Localization

end
