module

public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Defs
public import Mathlib.AlgebraicGeometry.Morphisms.RingHomProperties
public import Mathlib.RingTheory.RingHom.Locally
public import StacksFrontier.RingTheory.CompleteIntersection.RingMap.Criteria
public import StacksFrontier.RingTheory.RingHom.FinitePresentation
public import StacksFrontier.RingTheory.Smooth.Syntomic
public import StacksFrontier.RingTheory.Syntomic.BaseChange
public import StacksFrontier.RingTheory.Syntomic.Morphisms

/-!
# Syntomic ring maps, and the morphism property they define

A ring homomorphism is syntomic when it is syntomic as an algebra map for the induced algebra
structure. This property is local in Mathlib's sense, respects isomorphisms, is stable under
base change, and contains the identities; consequently syntomicity of a morphism of schemes is
`affineLocally` of syntomicity of ring maps, which is recorded as a `HasRingHomProperty`
instance.

## Main definitions

* `RingHom.Syntomic` is syntomicity of a ring homomorphism.

## Main results

* `RingHom.syntomic_propertyIsLocal`: syntomicity of ring maps is local.
* `RingHom.syntomic_isStableUnderBaseChange`: syntomicity of ring maps is stable under base
  change.
* `AlgebraicGeometry.Syntomic.hasRingHomProperty`: a morphism of schemes is syntomic exactly
  when it is affine-locally given by syntomic ring maps.

## Implementation notes

This is the single copy of the ring-map side of syntomicity. The characterizations,
composition, base change and open-immersion results for syntomic morphisms are all consequences
of the `HasRingHomProperty` instance proved here, together with Mathlib's general theory of
morphism properties defined by properties of ring maps.

The bridge is built by `HasRingHomProperty.locally_of_iff`, which matches the pointwise affine
definition of `AlgebraicGeometry.SyntomicAt` against `RingHom.Locally RingHom.Syntomic`, and
then transported by `HasRingHomProperty.copy` along
`RingHom.locally_iff_of_localizationSpanTarget`, so the recorded ring-map property is
`RingHom.Syntomic` itself rather than its local closure.

## References

* [Stacks Project, Tag 01UD](https://stacks.math.columbia.edu/tag/01UD)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

universe u

namespace RingHom

/-- A ring homomorphism is **syntomic** if it is syntomic as an algebra map for the algebra
structure it induces. -/
def Syntomic {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) : Prop :=
  letI := f.toAlgebra
  Algebra.Syntomic R S

/-- Unfolding of `RingHom.Syntomic`. -/
theorem syntomic_iff {R S : Type u} [CommRing R] [CommRing S] (f : R →+* S) :
    f.Syntomic ↔ letI := f.toAlgebra; Algebra.Syntomic R S := Iff.rfl

/-- A ring isomorphism is syntomic. -/
theorem Syntomic.of_ringEquiv {R S : Type u} [CommRing R] [CommRing S] (e : R ≃+* S) :
    e.toRingHom.Syntomic := by
  let : Algebra R S := e.toRingHom.toAlgebra
  have : Algebra.Smooth R S := Algebra.Smooth.of_equiv (R := R)
    (show R ≃ₐ[R] S from { e with commutes' := fun _ => rfl })
  exact Algebra.Smooth.syntomic R S

/-- The composition of syntomic ring maps is syntomic. -/
private theorem syntomic_comp {R S T : Type u} [CommRing R] [CommRing S] [CommRing T]
    {f : R →+* S} {g : S →+* T} (hf : f.Syntomic) (hg : g.Syntomic) : (g.comp f).Syntomic := by
  let : Algebra R S := f.toAlgebra
  let : Algebra S T := g.toAlgebra
  let : Algebra R T := (g.comp f).toAlgebra
  have : IsScalarTower R S T := .of_algebraMap_eq fun _ => rfl
  have : Algebra.Syntomic R S := hf
  have : Algebra.Syntomic S T := hg
  exact Algebra.Syntomic.comp R S T

/-- The structure map of a principal localization is syntomic. -/
private theorem syntomic_algebraMap_of_away {R S : Type u} [CommRing R] [CommRing S] [Algebra R S]
    (r : R) [IsLocalization.Away r S] : (algebraMap R S).Syntomic := by
  have : Algebra.Smooth R S := Algebra.Smooth.of_isLocalization_Away r
  unfold Syntomic
  rw [toAlgebra_algebraMap]
  exact Algebra.Smooth.syntomic R S

/-- Syntomicity of ring maps is invariant under pre- and post-composition with isomorphisms. -/
theorem syntomic_respectsIso : RingHom.RespectsIso (@Syntomic.{u}) :=
  ⟨fun _ e hφ => syntomic_comp hφ (Syntomic.of_ringEquiv e),
    fun _ e hφ => syntomic_comp (Syntomic.of_ringEquiv e) hφ⟩

/-- Simultaneous principal localization preserves syntomicity. -/
theorem syntomic_localizationAwayPreserves :
    RingHom.LocalizationAwayPreserves (@Syntomic.{u}) := by
  intro R S instR instS f r R' S' instR' instS' algRR' algSS' hlocR hlocS hf
  let : Algebra R S := f.toAlgebra
  let : Algebra R' S' := (IsLocalization.Away.map R' S' f r).toAlgebra
  let : Algebra R S' := ((algebraMap R' S').comp (algebraMap R R')).toAlgebra
  have hmap : ∀ x : R, (IsLocalization.Away.map R' S' f r) (algebraMap R R' x) =
      algebraMap S S' (f x) := fun x => by
    simp [IsLocalization.Away.map]
  have : IsScalarTower R S S' := IsScalarTower.of_algebraMap_eq hmap
  have : IsScalarTower R R' S' := IsScalarTower.of_algebraMap_eq fun x => rfl
  have hlocS' : IsLocalization (Algebra.algebraMapSubmonoid S (Submonoid.powers r)) S' := by
    rwa [Algebra.algebraMapSubmonoid, Submonoid.map_powers]
  have : Algebra.IsPushout R S R' S' :=
    (Algebra.isLocalization_iff_isPushout (Submonoid.powers r) R').mp hlocS'
  have : Algebra.Syntomic R S := (syntomic_iff f).mp hf
  exact Algebra.IsPushout.syntomic R S R' S'

/-- Syntomicity of ring maps is stable under composition with a principal localization on
either side. -/
theorem syntomic_stableUnderCompositionWithLocalizationAway :
    RingHom.StableUnderCompositionWithLocalizationAway (@Syntomic.{u}) := by
  constructor
  · intro R S T instR instS instT algRS r hlocRS f hf
    have := hlocRS
    exact syntomic_comp (syntomic_algebraMap_of_away (S := S) r) hf
  · intro R S T instR instS instT algST s hlocST f hf
    have := hlocST
    exact syntomic_comp hf (syntomic_algebraMap_of_away (S := T) s)

/-- Syntomicity of ring maps descends from a principal open cover of the target. -/
theorem syntomic_ofLocalizationSpanTarget :
    RingHom.OfLocalizationSpanTarget (@Syntomic.{u}) := by
  intro R S _ _ f s hs h
  have hflat : f.Flat :=
    RingHom.Flat.ofLocalizationSpanTarget f s hs (fun r =>
      ((syntomic_iff ((algebraMap S (Localization.Away (r : S))).comp f)).mp (h r)).flat)
  obtain ⟨t, hts, ht⟩ := (Ideal.span_eq_top_iff_finite s).mp hs
  let g : Fin t.card → S := fun i => (t.equivFin.symm i : S)
  have hgtop : Ideal.span (Set.range g) = ⊤ := by
    have hrange : Set.range g = (t : Set S) := by
      refine Set.eq_of_subset_of_subset ?_ fun x hx => ⟨t.equivFin ⟨x, hx⟩, by simp [g]⟩
      rintro _ ⟨i, rfl⟩
      exact (t.equivFin.symm i).property
    rwa [hrange]
  have hci : f.IsLocalCompleteIntersection :=
    RingHom.isLocalCompleteIntersection_of_localization_away f g hgtop (fun i =>
      ((RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection _).mp
        ((syntomic_iff _).mp (h ⟨g i, hts (t.equivFin.symm i).property⟩))).2)
  exact (RingHom.syntomic_iff_flat_and_isLocalCompleteIntersection f).mpr ⟨hflat, hci⟩

/-- Syntomicity of ring maps is a local property in Mathlib's sense. -/
theorem syntomic_propertyIsLocal :
    RingHom.PropertyIsLocal (@Syntomic.{u}) :=
  { localizationAwayPreserves := syntomic_localizationAwayPreserves
    ofLocalizationSpanTarget := syntomic_ofLocalizationSpanTarget
    ofLocalizationSpan := syntomic_ofLocalizationSpanTarget.ofLocalizationSpan
      syntomic_stableUnderCompositionWithLocalizationAway.1
    StableUnderCompositionWithLocalizationAwayTarget :=
      syntomic_stableUnderCompositionWithLocalizationAway.2 }

/-- Syntomicity of ring maps is stable under base change. -/
theorem syntomic_isStableUnderBaseChange :
    RingHom.IsStableUnderBaseChange (@Syntomic.{u}) := by
  intro R S R' S' _ _ _ _ _ _ _ _ _ _ _ _ hf
  unfold Syntomic at hf ⊢
  rw [toAlgebra_algebraMap] at hf ⊢
  exact Algebra.IsPushout.syntomic R S R' S'

/-- Identity ring maps are syntomic. -/
theorem syntomic_containsIdentities : RingHom.ContainsIdentities (@Syntomic.{u}) :=
  fun R _ => Syntomic.of_ringEquiv (RingEquiv.refl R)

end RingHom

namespace AlgebraicGeometry

/-- A morphism of schemes is syntomic exactly when it is affine-locally given by syntomic ring
maps. -/
instance Syntomic.hasRingHomProperty :
    HasRingHomProperty (@Syntomic.{u}) (@RingHom.Syntomic.{u}) := by
  have hlocal := RingHom.syntomic_propertyIsLocal
  have hbridge : HasRingHomProperty (@Syntomic.{u})
      (RingHom.Locally (@RingHom.Syntomic.{u})) :=
    HasRingHomProperty.locally_of_iff hlocal.localizationAwayPreserves
      RingHom.syntomic_stableUnderCompositionWithLocalizationAway (by
        intro X S f
        change (∀ x, SyntomicAt f x) ↔ _
        constructor
        · intro hf x
          obtain ⟨U, hxU, V, hUV, hsyn⟩ := hf x
          exact ⟨V, U, hxU, hUV, hsyn⟩
        · intro hf x
          obtain ⟨U, V, hxV, hUV, hsyn⟩ := hf x
          exact ⟨V, hxV, U, hUV, hsyn⟩)
  exact HasRingHomProperty.copy
    (P := @Syntomic.{u})
    (Q := RingHom.Locally (@RingHom.Syntomic.{u}))
    (P' := @Syntomic.{u})
    (Q' := @RingHom.Syntomic.{u}) rfl (fun {R S} _ _ f =>
      RingHom.locally_iff_of_localizationSpanTarget hlocal.respectsIso
        hlocal.ofLocalizationSpanTarget f)

/-- Syntomic morphisms are stable under composition with open immersions on either side. -/
instance : MorphismProperty.Respects (@Syntomic.{u}) @IsOpenImmersion :=
  HasRingHomProperty.respects_isOpenImmersion
    RingHom.syntomic_stableUnderCompositionWithLocalizationAway.1

/-- Syntomic morphisms are stable under postcomposition with open immersions. -/
instance : MorphismProperty.RespectsRight (@Syntomic.{u}) @IsOpenImmersion :=
  (HasRingHomProperty.respects_isOpenImmersion (P := @Syntomic)
    RingHom.syntomic_stableUnderCompositionWithLocalizationAway.1).toRespectsRight

/-- Being syntomic is local on the source in the Zariski topology. -/
instance : IsZariskiLocalAtSource (@Syntomic.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtSource

/-- Being syntomic is local on the target in the Zariski topology. -/
instance : IsZariskiLocalAtTarget (@Syntomic.{u}) :=
  HasRingHomProperty.instIsZariskiLocalAtTarget (@Syntomic.{u})

end AlgebraicGeometry
