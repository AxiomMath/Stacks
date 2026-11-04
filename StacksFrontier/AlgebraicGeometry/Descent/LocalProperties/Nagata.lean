module

public import StacksFrontier.AlgebraicGeometry.Descent.LocalProperties.Criterion
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.FiniteType
public import StacksFrontier.AlgebraicGeometry.NagataNormalization.LocalProperty
public import StacksFrontier.RingTheory.Nagata.SmoothDescent

/-!
# Being Nagata is local in the smooth topology

A scheme is Nagata if and only if the members of a jointly surjective family of smooth
morphisms onto it are Nagata.

## Main results

* `AlgebraicGeometry.isLocally_isLocal_zariski` records that a scheme locally satisfying a
  local property of rings is a Zariski-local condition.
* `AlgebraicGeometry.isNagataScheme_isLocal_smooth` states that being Nagata is local in
  the smooth topology.
* `AlgebraicGeometry.isNagataScheme_isLocal_etale` is the same for the étale precoverage,
  which follows because every étale morphism is smooth.

## Implementation notes

Ascent is the Nagata property of a scheme of locally finite type over a Nagata base, and
descent is the ring-theoretic descent of the Nagata property along a smooth ring map which
is surjective on spectra. Both halves are applied to the global sections of the affine
schemes involved, which are reached from the scheme-level condition through the
characterizations of `AlgebraicGeometry.isLocally_iff_forall_affineOpens`.

## References

* [Stacks Project, Tag 036E](https://stacks.math.columbia.edu/tag/036E)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry

variable {P : (R : Type u) → [CommRing R] → Prop}

/-- Locally satisfying a local property of rings is invariant under isomorphism. -/
theorem IsLocally.of_iso (hP : CommRing.PropertyIsLocal P) {X Y : Scheme.{u}} (e : X ≅ Y)
    (hX : IsLocally P X) : IsLocally P Y := by
  rw [isLocally_iff_forall_affineOpens hP]
  intro V
  exact hP.of_ringEquiv (e.inv.appIso V.1).commRingCatIsoToRingEquiv
    (hX.forall_affineOpens hP ⟨e.inv ''ᵁ V.1, V.2.image_of_isOpenImmersion e.inv⟩)

/-- Locally satisfying a local property of rings is a Zariski-local condition on
schemes. -/
theorem isLocally_isLocal_zariski (hP : CommRing.PropertyIsLocal P) :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsLocally P X)
      Scheme.zariskiPrecoverage :=
  have : ObjectProperty.IsClosedUnderIsomorphisms (fun X : Scheme.{u} => IsLocally P X) :=
    ⟨fun e hX => IsLocally.of_iso hP e hX⟩
  isLocal_zariskiPrecoverage_of_openCover _ (fun U hX => isLocally_open hP _ hX U)
    fun U hU h => (isLocally_iff_exists_openCover hP _).mpr ⟨_, U, hU, h⟩

/-- **Stacks Project, Tag 036E.** Being Nagata is local for the smooth precoverage on
schemes. -/
@[stacks 036E]
instance isNagataScheme_isLocal_smooth :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsNagataScheme X)
      (Scheme.precoverage @Smooth) := by
  have : ObjectProperty.IsLocal (fun X : Scheme.{u} => IsNagataScheme X)
      Scheme.zariskiPrecoverage := isLocally_isLocal_zariski CommRing.isNagataRing_propertyIsLocal
  refine isLocal_smoothPrecoverage_of_affine (fun X : Scheme.{u} => IsNagataScheme X) ?_ ?_
  · intro X S hX hS f hsm hSprop
    let : IsAffine X := hX
    let : IsAffine S := hS
    let : Smooth f := hsm
    exact isNagataScheme_of_locallyOfFiniteType f hSprop
  · intro X S hX hS f hsm hsurj hXprop
    let : IsAffine X := hX
    let : IsAffine S := hS
    let : Smooth f := hsm
    have hff : (f.appTop).hom.FaithfullyFlat :=
      (Flat.flat_and_surjective_iff_faithfullyFlat_of_isAffine f).mp ⟨inferInstance, hsurj⟩
    let : Algebra Γ(S, ⊤) Γ(X, ⊤) := (f.appTop).hom.toAlgebra
    have hmap : (f.appTop).hom.Smooth := by
      simpa [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE] using
        hsm.smooth_appLE (isAffineOpen_top S) (isAffineOpen_top X) le_rfl
    let : Algebra.Smooth Γ(S, ⊤) Γ(X, ⊤) := RingHom.smooth_algebraMap.mp hmap
    have hspec : Function.Surjective (PrimeSpectrum.comap (algebraMap Γ(S, ⊤) Γ(X, ⊤))) :=
      (RingHom.FaithfullyFlat.iff_flat_and_comap_surjective.mp hff).2
    have hTR : IsNagataRing Γ(X, ⊤) :=
      hXprop.isNagataRing_sections ⟨⊤, isAffineOpen_top X⟩
    exact fun s => ⟨⟨⊤, isAffineOpen_top S⟩, Set.mem_univ s,
      IsNagataRing.of_smooth_of_comap_surjective hspec hTR⟩

/-- Being Nagata is local for the étale precoverage on schemes: it is smooth local by
**Stacks 036E**, and every étale morphism is smooth. -/
instance isNagataScheme_isLocal_etale :
    ObjectProperty.IsLocal (fun X : Scheme.{u} => IsNagataScheme X) Scheme.etalePrecoverage :=
  ObjectProperty.IsLocal.of_le
    (Scheme.precoverage_mono (P := (@AlgebraicGeometry.Etale : MorphismProperty Scheme.{u}))
      (Q := (@AlgebraicGeometry.Smooth : MorphismProperty Scheme.{u}))
      fun _ _ f hf => by
        let _ : AlgebraicGeometry.Etale f := hf
        infer_instance)

end AlgebraicGeometry
