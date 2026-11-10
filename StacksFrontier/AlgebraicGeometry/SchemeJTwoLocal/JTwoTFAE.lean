module

public import Mathlib.Data.List.TFAE
public import StacksFrontier.AlgebraicGeometry.Morphisms.SingularLocus.JTwo
public import StacksFrontier.AlgebraicGeometry.NormalizationQuotientDirectSum.RegularLocusOpen
public import StacksFrontier.RingTheory.Regular.SingularLocus
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Local characterizations of J-2 schemes

The scheme-theoretic J-2 condition `AlgebraicGeometry.Scheme.IsJ2` is defined by a universal
property quantified over all schemes locally of finite type over the base.  This file reduces it
to the ring-theoretic condition `IsJ2` on sections: a locally Noetherian scheme is J-2 exactly
when the section ring of every affine open is J-2, and it is enough to test this on the members
of a single affine open covering.  The J-2 condition is also inherited by every scheme locally of
finite type over a J-2 base.

## Main results

* `AlgebraicGeometry.Scheme.isJ2_tfae` is the four-part equivalence: the scheme is J-2, some
  open covering has J-2 members, every affine open has J-2 section ring, some affine open
  covering has J-2 section rings.
* `AlgebraicGeometry.Scheme.isJ2_of_locallyOfFiniteType'` is the inheritance statement: a
  scheme locally of finite type over a J-2 scheme is J-2, with local Noetherianity of the source
  derived rather than assumed;
  `AlgebraicGeometry.Scheme.isJ2_of_locallyOfFiniteType_of_isLocallyNoetherian` assumes it.
* `AlgebraicGeometry.Scheme.isOpen_regularLocus_spec_iff`: the regular locus of `Spec R` is
  open exactly when `R` is J-1.

## Implementation notes

In `isJ2_of_locallyOfFiniteType'` local Noetherianity of the source is bound with `letI`, from
`AlgebraicGeometry.LocallyOfFiniteType.isLocallyNoetherian`.  The instance argument of `IsJ2`
does not occur in its body, so which `IsLocallyNoetherian` instance is in scope never affects
the proposition.

Open coverings are indexed families of opens whose supremum is `⊤`, matching the ambient
convention, and the ring-theoretic conditions are written `_root_.IsJ1` / `_root_.IsJ2` because
the scheme-theoretic `IsJ2` shares their leaf name inside this namespace.

## References

* [Stacks Project, Tag 07R4](https://stacks.math.columbia.edu/tag/07R4)
-/

@[expose] public section

open CategoryTheory TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme

/-- The regular locus of `Spec R` is open exactly when `R` is J-1. -/
public theorem isOpen_regularLocus_spec_iff (R : Type u) [CommRing R] :
    IsOpen (regularLocus (Spec (.of R))) ↔ _root_.IsJ1 R := by
  have h : regularLocus (Spec (.of R)) =
      {p : PrimeSpectrum R | IsRegularLocalRing (Localization.AtPrime p.asIdeal)} := by
    ext p
    let : p.asIdeal.IsPrime := p.2
    change IsRegularLocalRing ((Spec (.of R)).presheaf.stalk p) ↔
      IsRegularLocalRing (Localization.AtPrime p.asIdeal)
    let e := (Spec.stalkIso (.of R) p).commRingCatIsoToRingEquiv
    exact ⟨fun _ => .of_ringEquiv e, fun _ => .of_ringEquiv e.symm⟩
  rw [h]
  rfl

/-- A locally Noetherian scheme locally of finite type over a locally Noetherian J-2 scheme is
J-2. -/
public theorem isJ2_of_locallyOfFiniteType_of_isLocallyNoetherian {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (hX : IsJ2 X) (f : Y ⟶ X)
    [LocallyOfFiniteType f] : IsJ2 Y := by
  refine IsJ2.mk fun Z g hg => ?_
  let : LocallyOfFiniteType g := hg
  let : LocallyOfFiniteType (g ≫ f) := locallyOfFiniteType_comp g f
  exact hX.isOpen_regularLocus (g ≫ f)

/-- If an affine open of a locally Noetherian scheme is J-2 as a scheme, its section ring is J-2
as a ring. -/
public theorem isJ2_sectionRing_of_isJ2_affineOpen {X : Scheme.{u}} [IsLocallyNoetherian X]
    (U : X.affineOpens) (hU : IsJ2 U.1.toScheme) : _root_.IsJ2 Γ(X, U.1) := by
  intro A hA hAlg hFinite
  let : CommRing A := hA
  let : Algebra Γ(X, U.1) A := hAlg
  let : Algebra.FiniteType Γ(X, U.1) A := hFinite
  let φ : CommRingCat.of Γ(X, U.1) ⟶ CommRingCat.of A :=
    CommRingCat.ofHom (algebraMap Γ(X, U.1) A)
  have : LocallyOfFiniteType (Spec.map φ) := by
    rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
    exact RingHom.finiteType_algebraMap.mpr inferInstance
  let g : Spec (.of A) ⟶ U.1.toScheme := Spec.map φ ≫ U.2.isoSpec.inv
  have : IsOpenImmersion U.2.isoSpec.inv := by infer_instance
  have : LocallyOfFiniteType U.2.isoSpec.inv := inferInstance
  have : LocallyOfFiniteType g := locallyOfFiniteType_comp _ _
  exact (isOpen_regularLocus_spec_iff A).mp (hU.isOpen_regularLocus g)

/-- The section ring of every affine open of a J-2 scheme is J-2. -/
public theorem isJ2_sectionRing_of_isJ2 {X : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : IsJ2 X) (U : X.affineOpens) : _root_.IsJ2 Γ(X, U.1) :=
  isJ2_sectionRing_of_isJ2_affineOpen U
    (isJ2_of_locallyOfFiniteType_of_isLocallyNoetherian hX U.1.ι)

/-- If a locally Noetherian scheme `X` has an affine open covering whose section rings are J-2,
then the regular locus of any scheme locally of finite type over `X` is open. -/
@[ega "IV 7.8.6" "more general"]
public theorem isOpen_regularLocus_of_affineJ2_cover {X Y : Scheme.{u}}
    [IsLocallyNoetherian X] {ι : Type u} (U : ι → X.affineOpens)
    (hU : (⨆ i, (U i).1) = ⊤) (hJ2 : ∀ i, _root_.IsJ2 Γ(X, (U i).1))
    (f : Y ⟶ X) [LocallyOfFiniteType f] : IsOpen (regularLocus Y) := by
  have hJ1 : ∀ (i : ι) (W : Y.affineOpens), W.1 ≤ f ⁻¹ᵁ (U i).1 → _root_.IsJ1 Γ(Y, W.1) := by
    intro i W e
    let : Algebra Γ(X, (U i).1) Γ(Y, W.1) := (f.appLE (U i).1 W.1 e).hom.toAlgebra
    let : Algebra.FiniteType Γ(X, (U i).1) Γ(Y, W.1) := f.finiteType_appLE (U i).2 W.2 e
    exact hJ2 i Γ(Y, W.1)
  have hmem : ∀ y : Y, ∃ W : Y.affineOpens, y ∈ W.1 ∧ _root_.IsJ1 Γ(Y, W.1) := by
    intro y
    obtain ⟨i, hi⟩ := (IsOpenCover.mk hU).exists_mem (f.base y)
    obtain ⟨_, ⟨W : Y.Opens, hW, rfl⟩, hyW, hWf⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open hi (f ⁻¹ᵁ (U i).1).2
    exact ⟨⟨W, hW⟩, hyW, hJ1 i ⟨W, hW⟩ hWf⟩
  have hcover : regularLocus Y =
      ⋃ y : Y, regularLocus Y ∩ (((hmem y).choose.1 : Y.Opens) : Set Y) := by
    refine Set.eq_of_subset_of_subset (fun z hz => ?_)
      (Set.iUnion_subset fun _ => Set.inter_subset_left)
    exact Set.mem_iUnion.mpr ⟨z, hz, (hmem z).choose_spec.1⟩
  rw [hcover]
  exact isOpen_iUnion fun y =>
    Stacks.AlgebraicGeometry.NormalizationQuotientDirectSum.isOpen_regularLocus_inter_affineOpen
      Y (hmem y).choose (hmem y).choose_spec.2

/-- **Stacks Project, Tag 07R4.** For a locally Noetherian scheme, the J-2 condition is
equivalent to holding on the members of an open covering, to the section ring of every affine
open being J-2, and to that ring-theoretic condition holding on one affine open covering. -/
@[stacks 07R4 "equivalent conditions"]
public theorem isJ2_tfae (X : Scheme.{u}) [IsLocallyNoetherian X] :
    List.TFAE [
      IsJ2 X,
      ∃ (I : Type u) (U : I → X.Opens),
        (⨆ i, U i) = ⊤ ∧ ∀ i, IsJ2 (U i).toScheme,
      ∀ U : X.affineOpens, _root_.IsJ2 Γ(X, U.1),
      ∃ (I : Type u) (U : I → X.affineOpens),
        (⨆ i, (U i).1) = ⊤ ∧ ∀ i, _root_.IsJ2 Γ(X, (U i).1)] := by
  tfae_have 1 → 2 := fun hX => ⟨PUnit.{u + 1}, fun _ => ⊤, by simp,
    fun _ => isJ2_of_locallyOfFiniteType_of_isLocallyNoetherian hX (⊤ : X.Opens).ι⟩
  tfae_have 2 → 4 := by
    rintro ⟨I, U, hU, hJ⟩
    let J := Σ i : I, {V : X.affineOpens // V.1 ≤ U i}
    refine ⟨J, fun j => j.2.1, ?_, ?_⟩
    · apply Opens.ext
      ext x
      simp only [Opens.coe_iSup, Set.mem_iUnion]
      refine ⟨fun _ => trivial, fun _ => ?_⟩
      obtain ⟨i, hi⟩ := (IsOpenCover.mk hU).exists_mem x
      obtain ⟨_, ⟨W : X.Opens, hW, rfl⟩, hxW, hWU⟩ :=
        X.isBasis_affineOpens.exists_subset_of_mem_open hi (U i).2
      exact ⟨⟨i, ⟨⟨W, hW⟩, hWU⟩⟩, hxW⟩
    · intro j
      exact isJ2_sectionRing_of_isJ2_affineOpen j.2.1
        (isJ2_of_locallyOfFiniteType_of_isLocallyNoetherian (hJ j.1) (X.homOfLE j.2.2))
  tfae_have 4 → 1 := by
    rintro ⟨I, U, hU, hJ⟩
    refine IsJ2.mk fun Y f hf => ?_
    let : LocallyOfFiniteType f := hf
    exact isOpen_regularLocus_of_affineJ2_cover U hU hJ f
  tfae_have 1 → 3 := fun hX U => isJ2_sectionRing_of_isJ2 hX U
  tfae_have 3 → 4 := fun h => ⟨X.affineOpens, id, iSup_affineOpens_eq_top X, h⟩
  tfae_finish

/-- **Stacks Project, Tag 07R4.** A scheme locally of finite type over a J-2 scheme is J-2.
Local Noetherianity of the source is derived from that of the base rather than assumed. -/
@[stacks 07R4 "locally finite type schemes"]
public theorem isJ2_of_locallyOfFiniteType' {X Y : Scheme.{u}} [IsLocallyNoetherian X]
    (hX : IsJ2 X) (f : Y ⟶ X) [LocallyOfFiniteType f] :
    letI : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
    IsJ2 Y := by
  let : IsLocallyNoetherian Y := LocallyOfFiniteType.isLocallyNoetherian f
  exact isJ2_of_locallyOfFiniteType_of_isLocallyNoetherian hX f

end AlgebraicGeometry.Scheme

end
