module

public import Mathlib.Topology.Constructible
public import StacksFrontier.AlgebraicGeometry.Blowup.DominatedByBlowup
public import StacksFrontier.AlgebraicGeometry.Blowup.IsomorphismOffCenter.Basic
public import StacksFrontier.AlgebraicGeometry.Blowup.ReesAlgebra.Proper
public import StacksFrontier.AlgebraicGeometry.Flatness.BlowingUp.FiniteTypeIdealSheaf
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.AlmostBlowUp.IsomorphismAwayFromCenter
public import StacksFrontier.AlgebraicGeometry.Morphisms.ImmersionsAndAffine.SectionGraphClosure
public import StacksFrontier.AlgebraicGeometry.StrictTransform.Basic
public import StacksFrontier.AlgebraicGeometry.RestrictIso

/-!
# Inputs for the construction of compactifications

Small facts shared by the steps of Nagata's compactification theorem: that a morphism which is
an isomorphism over an open stays one after base change and over the inverse image of that
open, that an admissible blowup is proper and an isomorphism over the open it is admissible
for, and two separation statements in a spectral space.

## Main results

* `AlgebraicGeometry.isIso_morphismRestrict_pullback_snd_preimage`: base change preserves being
  an isomorphism over an open.
* `AlgebraicGeometry.isProper_of_isAdmissibleBlowup` and
  `AlgebraicGeometry.isIso_morphismRestrict_of_isAdmissibleBlowup`: an admissible blowup is
  proper, and an isomorphism over the open it is admissible for.
* `AlgebraicGeometry.isCompact_preimage_of_isIso_morphismRestrict`: the inverse image of a
  quasi-compact open under a morphism which is an isomorphism over it is quasi-compact.
* `AlgebraicGeometry.supportedSectionsIdeal_eq_ker` and
  `AlgebraicGeometry.strictTransform_ideal_eq_ker`: the ideal of sections supported on a closed
  set, and the defining ideal of a strict transform, as kernel ideals of open inclusions.
* `Stacks.Compactification.exists_isOpen_isCompact_between`: in a prespectral quasi-separated
  space a compact set inside an open set is inside a quasi-compact open subset of it.
* `Stacks.Compactification.exists_disjoint_isClosed_isConstructible_superset`: two disjoint
  closed subsets of a quasi-compact prespectral quasi-separated space are separated by disjoint
  closed constructible sets with quasi-compact open complements.

## Implementation notes

The properness of an admissible blowup goes through
`AlgebraicGeometry.isProper_blowUpToBase_of_fg`, which needs the centre to be of finite type;
the centre of an admissible blowup is finitely presented as a closed subscheme, and
`AlgebraicGeometry.finitePresentation_subschemeι_iff_isFiniteType` converts.

## References

* [Stacks Project, Tag 02OS](https://stacks.math.columbia.edu/tag/02OS)
* [Stacks Project, Tag 080K](https://stacks.math.columbia.edu/tag/080K)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-- The second projection of an iterated pullback is an isomorphism iff the second projection of
the pullback along the composite is. -/
private theorem isIso_pullback_snd_pullback_snd_iff {A T U Y : Scheme.{u}} (q : A ⟶ Y)
    (g : T ⟶ U) (h : U ⟶ Y) :
    IsIso (pullback.snd (pullback.snd q h) g) ↔ IsIso (pullback.snd q (g ≫ h)) := by
  rw [← isIso_comp_left_iff (pullbackLeftPullbackSndIso q h g).hom,
    pullbackLeftPullbackSndIso_hom_snd]

/-- The base change of a morphism which is an isomorphism over an open of its target is an
isomorphism over the inverse image of that open. -/
theorem isIso_morphismRestrict_pullback_snd_preimage {A T Y : Scheme.{u}} (q : A ⟶ Y)
    (b : T ⟶ Y) (W : Y.Opens) [IsIso (q ∣_ W)] :
    IsIso (pullback.snd q b ∣_ (b ⁻¹ᵁ W)) := by
  have hq : IsIso (pullback.snd q W.ι) :=
    (isIso_morphismRestrict_iff_isIso_pullback_snd q W).1 inferInstance
  have htarget := (isIso_pullback_snd_pullback_snd_iff q (b ∣_ W) W.ι).1 inferInstance
  rw [morphismRestrict_ι b W] at htarget
  exact (isIso_morphismRestrict_iff_isIso_pullback_snd (pullback.snd q b) (b ⁻¹ᵁ W)).2
    ((isIso_pullback_snd_pullback_snd_iff q (b ⁻¹ᵁ W).ι b).2 htarget)

/-- An admissible blowup is proper: its centre is finitely presented as a closed subscheme,
hence of finite type, and the blowup in a centre of finite type is proper. -/
theorem isProper_of_isAdmissibleBlowup {X X' : Scheme.{u}} (U : X.Opens) (b : X' ⟶ X)
    (hb : Stacks.Blowup.IsAdmissibleBlowup U b) : IsProper b := by
  obtain ⟨I, hI, -, e, he⟩ := hb
  exact Stacks.Blowup.IsAdmissibleBlowup.isProper_of_fg e he
    ((finitePresentation_subschemeι_iff_isFiniteType I).mp hI)

/-- An admissible blowup is an isomorphism over the open it is admissible for: its centre is
supported away from that open, and a blowup is an isomorphism off the support of its centre. -/
theorem isIso_morphismRestrict_of_isAdmissibleBlowup {X X' : Scheme.{u}} (U : X.Opens)
    (b : X' ⟶ X) (hb : Stacks.Blowup.IsAdmissibleBlowup U b) : IsIso (b ∣_ U) := by
  obtain ⟨I, -, hdisj, e, he⟩ := hb
  have h : IsIso (Stacks.Blowup.blowUpToBase I ∣_ U) :=
    Stacks.Blowup.isIso_blowUpToBase_restrict_of_subset_compl_support_reesData I U
      fun _ hz ↦ Set.disjoint_left.mp hdisj hz
  have h' : IsIso (e.hom ∣_ Stacks.Blowup.blowUpToBase I ⁻¹ᵁ U) := inferInstance
  rw [← he, morphismRestrict_comp]
  exact IsIso.comp_isIso' h' h

/-- The inverse image of a quasi-compact open under a morphism which is an isomorphism over it
is quasi-compact. -/
theorem isCompact_preimage_of_isIso_morphismRestrict {X Y : Scheme.{u}} (b : X ⟶ Y)
    (U : Y.Opens) (hU : IsCompact (U : Set Y)) [IsIso (b ∣_ U)] :
    IsCompact ((b ⁻¹ᵁ U : X.Opens) : Set X) := by
  have : CompactSpace U.toScheme := isCompact_iff_compactSpace.mp hU
  have : CompactSpace (b ⁻¹ᵁ U).toScheme := (b ∣_ U).homeomorph.symm.compactSpace
  exact isCompact_iff_compactSpace.mpr this

/-- The ideal of sections supported on a closed set is the kernel ideal of the inclusion of its
open complement. -/
theorem supportedSectionsIdeal_eq_ker {X : Scheme.{u}} (Z : Set X) (hZ : IsClosed Z) :
    supportedSectionsIdeal Z =
      (Scheme.Opens.ι (⟨Zᶜ, hZ.isOpen_compl⟩ : X.Opens)).ker := by
  refine le_antisymm ?_ ?_
  · rw [← Scheme.IdealSheafData.map_bot,
      Scheme.IdealSheafData.le_map_iff_comap_le, le_bot_iff,
      ← restrict_isIso_iff_comap_bot]
    exact (isIso_restrict_iff_le_supportedSectionsIdeal Z hZ _).2 le_rfl
  · refine (isIso_restrict_iff_le_supportedSectionsIdeal Z hZ _).1 ?_
    rw [restrict_isIso_iff_comap_bot, ← le_bot_iff,
      ← Scheme.IdealSheafData.le_map_iff_comap_le, Scheme.IdealSheafData.map_bot]

/-- The defining ideal of the strict transform is the kernel ideal of the inclusion of the
complement of the inverse image of the exceptional divisor. -/
theorem strictTransform_ideal_eq_ker {X S : Scheme.{u}} (f : X ⟶ S)
    (I : S.IdealSheafData) :
    Stacks.StrictTransform.ideal f (blowUpToBase I) (exceptionalIdeal I) =
      (Scheme.Opens.ι (⟨(Stacks.StrictTransform.exceptionalPreimage f (blowUpToBase I)
        (exceptionalIdeal I))ᶜ,
        ((exceptionalIdeal I).support.isClosed.preimage
          (pullback.snd f (blowUpToBase I)).continuous).isOpen_compl⟩ :
        (Stacks.StrictTransform.baseChange f (blowUpToBase I)).Opens)).ker :=
  supportedSectionsIdeal_eq_ker _
    ((exceptionalIdeal I).support.isClosed.preimage
      (pullback.snd f (blowUpToBase I)).continuous)

end AlgebraicGeometry

namespace Stacks.Compactification

/-- A quasi-compact open subset of a quasi-separated space is constructible. -/
theorem isConstructible_of_isOpen_of_isCompact {Z : Type u} [TopologicalSpace Z]
    [QuasiSeparatedSpace Z] {A : Set Z} (hAopen : IsOpen A) (hAcompact : IsCompact A) :
    Topology.IsConstructible A := by
  have hAretro : IsRetrocompact A :=
    fun _ hUcompact hUopen ↦ hAcompact.inter_of_isOpen hUcompact hAopen hUopen
  exact hAretro.isConstructible hAopen

/-- In a prespectral space a compact subset of an open subset is contained in a quasi-compact
open subset of it: cover the compact set by basic quasi-compact opens inside the open set and
take a finite subcover. -/
theorem exists_isOpen_isCompact_between {Z : Type u} [TopologicalSpace Z] [PrespectralSpace Z]
    {A O : Set Z} (hAcompact : IsCompact A) (hOopen : IsOpen O) (hAO : A ⊆ O) :
    ∃ K : Set Z, IsOpen K ∧ IsCompact K ∧ A ⊆ K ∧ K ⊆ O := by
  choose B hB hAB hBO using fun a : A ↦
    PrespectralSpace.isTopologicalBasis.exists_subset_of_mem_open (hAO a.2) hOopen
  obtain ⟨s, hs⟩ := hAcompact.elim_finite_subcover B (fun a ↦ (hB a).1)
    fun x hx ↦ Set.mem_iUnion.2 ⟨⟨x, hx⟩, hAB _⟩
  exact ⟨⋃ a ∈ s, B a, isOpen_biUnion fun a _ ↦ (hB a).1,
    s.isCompact_biUnion fun a _ ↦ (hB a).2, hs, Set.iUnion₂_subset fun a _ ↦ hBO a⟩

/-- Two disjoint closed subsets of a quasi-compact prespectral quasi-separated space are
contained in disjoint closed constructible subsets whose complements are quasi-compact open:
thicken the second to a quasi-compact open avoiding the first, and then the complement of that
open to a quasi-compact open avoiding the second. -/
theorem exists_disjoint_isClosed_isConstructible_superset {Z : Type u} [TopologicalSpace Z]
    [CompactSpace Z] [PrespectralSpace Z] [QuasiSeparatedSpace Z]
    (A B : Set Z) (hAclosed : IsClosed A) (hBclosed : IsClosed B) (hdisj : Disjoint A B) :
    ∃ A' B' : Set Z,
      A ⊆ A' ∧ B ⊆ B' ∧ IsClosed A' ∧ IsClosed B' ∧
        Topology.IsConstructible A' ∧ Topology.IsConstructible B' ∧ Disjoint A' B' := by
  have hBinAcomp : B ⊆ Aᶜ := fun x hxB hxA => Set.disjoint_left.mp hdisj hxA hxB
  obtain ⟨U, hUopen, hUcompact, hBU, hUB⟩ :=
    exists_isOpen_isCompact_between hBclosed.isCompact hAclosed.isOpen_compl hBinAcomp
  have hA'A : A ⊆ Uᶜ := fun x hx hxU => hUB hxU hx
  have hA'closed : IsClosed (Uᶜ : Set Z) := hUopen.isClosed_compl
  have hA'inBcomp : (Uᶜ : Set Z) ⊆ Bᶜ := fun _ hxA' hxB => hxA' (hBU hxB)
  obtain ⟨U', hU'open, hU'compact, hA'U', hU'Bcomp⟩ :=
    exists_isOpen_isCompact_between hA'closed.isCompact hBclosed.isOpen_compl hA'inBcomp
  exact ⟨Uᶜ, U'ᶜ, hA'A, fun x hxB hxU' => hU'Bcomp hxU' hxB, hA'closed,
    hU'open.isClosed_compl,
    (isConstructible_of_isOpen_of_isCompact hUopen hUcompact).compl,
    (isConstructible_of_isOpen_of_isCompact hU'open hU'compact).compl,
    Set.disjoint_left.mpr fun x hxA' hxB' => hxB' (hA'U' hxA')⟩

end Stacks.Compactification

end
