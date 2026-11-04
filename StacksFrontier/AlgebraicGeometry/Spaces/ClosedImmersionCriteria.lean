module

public import Mathlib.CategoryTheory.Limits.Shapes.Pullback.Mono
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Etale.UniversallyInjectiveUnramified.ClosedImmersion
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FiniteTypeLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.Defs
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.Diagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.UniversallyInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Unramified
import StacksFrontier.AlgebraicGeometry.Spaces.Basic
import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonoCriteria
import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism
import StacksFrontier.AlgebraicGeometry.Topologies.Fppf

/-!
# Characterizations of closed immersions of algebraic spaces

A morphism of algebraic spaces over a scheme is a closed immersion precisely
under four equivalent combinations of universal closedness, unramifiedness,
universal injectivity, local finite type, and formal unramifiedness.

## Main results

* `closedImmersion_conditions_tfae` gives the five equivalent
  characterizations of a closed immersion.

## Implementation notes

The five entries of `List.TFAE` follow the source's order. Algebraic spaces
are functors on the big fppf site of the fixed base scheme. Monomorphisms are
categorical monomorphisms of their natural transformations.

## References

* [Stacks Project, Tag 05W8](https://stacks.math.columbia.edu/tag/05W8)
-/

public section

open AlgebraicGeometry CategoryTheory
open CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Universal closedness of a representable morphism of algebraic spaces, in the sense of
Stacks 03HI, is universal closedness of each of its represented base changes. -/
private theorem universallyClosed_iff_schemeProperty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f) :
    UniversallyClosed B S hS f ↔
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  (presheaf_universallyClosed_iff B S hS hX hY hrep).symm

private theorem locallyOfFiniteType_iff_schemeProperty
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hrep : yoneda.relativelyRepresentable f) :
    IsLocallyOfFiniteType B S hS f ↔
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f := by
  let : MorphismProperty.IsLocalAtTarget
      (@_root_.AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u})
      Scheme.fppfPrecoverage :=
    Stacks.Descent.locallyOfFiniteType_isLocalAtTarget_fppf
  exact holdsOnEveryEtaleChart_iff_relative B S hS
    (@_root_.AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u})
    LocallyOfFiniteType.isEtaleLocalOnSourceAndTarget
    hX hY f hrep

private theorem closedImmersion_iff_universallyClosed_locallyFiniteType_mono
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsClosedImmersion B S hS f ↔
      (UniversallyClosed B S hS f ∧
        (IsLocallyOfFiniteType B S hS f ∧ Mono f)) := by
  let q := BigFppfOver.toScheme B S hS
  let Pci := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.IsClosedImmersion.{u} : MorphismProperty Scheme.{u}) q
  let Puc := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.UniversallyClosed.{u} : MorphismProperty Scheme.{u}) q
  let Plft := MorphismProperty.inverseImage
    (@_root_.AlgebraicGeometry.LocallyOfFiniteType : MorphismProperty Scheme.{u}) q
  constructor
  · intro hf
    change Pci.presheaf f at hf
    have hrep := hf.rep
    have key : ∀ P : MorphismProperty Scheme.{u},
        (∀ {X Y : Scheme.{u}} (g : X ⟶ Y), _root_.AlgebraicGeometry.IsClosedImmersion g → P g) →
          (MorphismProperty.inverseImage P q).presheaf f := fun P hP =>
      MorphismProperty.relative_monotone (P := Pci) (P' := MorphismProperty.inverseImage P q)
        (fun _ _ g hg => hP (q.map g) hg) _ hf
    have hucSch :=
      key (@_root_.AlgebraicGeometry.UniversallyClosed.{u}) fun _ _ => inferInstance
    have hlftSch :=
      key (@_root_.AlgebraicGeometry.LocallyOfFiniteType) fun _ _ => inferInstance
    have hmono : Mono f :=
      MorphismProperty.presheaf_monomorphisms_le_monomorphisms (C := BigFppfOver B S hS) f <|
        MorphismProperty.relative_monotone
          (P := Pci) (P' := MorphismProperty.monomorphisms _)
          (fun A C g (hg : _root_.AlgebraicGeometry.IsClosedImmersion (q.map g)) =>
            (Functor.reflectsMonomorphisms_of_faithful q).reflects g
              (IsClosedImmersion.iff_isProper_and_mono _ |>.mp hg).2)
          _ hf
    exact ⟨(universallyClosed_iff_schemeProperty B S hS hX hY f hrep).mpr hucSch,
      (locallyOfFiniteType_iff_schemeProperty B S hS hX hY f hrep).mpr hlftSch,
      hmono⟩
  · rintro ⟨huc, hlft, hm⟩
    have hrep := relativelyRepresentable_of_locallyOfFiniteType_mono
      B S hS hX hY f ⟨hlft, hm⟩
      (fun hX' hY' g hg hsg =>
        relativelyRepresentable_of_isLocallyQuasiFinite_isSeparated B S hS g hX' hY' hg hsg)
    have hucSch : Puc.presheaf f :=
      (universallyClosed_iff_schemeProperty B S hS hX hY f hrep).mp huc
    have hlftSch : Plft.presheaf f :=
      (locallyOfFiniteType_iff_schemeProperty B S hS hX hY f hrep).mp hlft
    show Pci.presheaf f
    refine ⟨hrep, ?_⟩
    intro U V g fst snd hpb
    have hu : _root_.AlgebraicGeometry.UniversallyClosed (q.map snd) :=
      hucSch.property g fst snd hpb
    have hl : LocallyOfFiniteType (q.map snd) := hlftSch.property g fst snd hpb
    have hm' : Mono (q.map snd) := by
      have : Mono snd :=
        (Functor.reflectsMonomorphisms_of_faithful yoneda).reflects snd hpb.mono_snd_of_mono
      have : PreservesLimitsOfShape WalkingCospan q := comp_preservesLimitsOfShape _ _
      exact Functor.map_mono q snd
    have h56 := (closedImmersion_conditions_tfae (q.map snd)).out 5 1
    exact (IsClosedImmersion.iff_isProper_and_mono _).2 (h56.mp ⟨hu, hl, hm'⟩)

/-- The five equivalent conditions characterizing closed immersions of algebraic spaces. -/
@[stacks 05W8, sga "3 V 4.1.3"]
public theorem closedImmersion_conditions_tfae
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X)
    (hY : IsAlgebraicSpace B S hS Y)
    (f : X ⟶ Y) :
    List.TFAE
      [IsClosedImmersion B S hS f,
       UniversallyClosed B S hS f ∧
         (IsUnramified B S hS f ∧ Mono f),
       UniversallyClosed B S hS f ∧
         (IsUnramified B S hS f ∧
           UniversallyInjective B S hS f),
       UniversallyClosed B S hS f ∧
         (IsLocallyOfFiniteType B S hS f ∧ Mono f),
       UniversallyClosed B S hS f ∧
         (UniversallyInjective B S hS f ∧
           (IsLocallyOfFiniteType B S hS f ∧
             FormallyUnramified f))] := by
  refine List.tfae_of_forall (b :=
    UniversallyClosed B S hS f ∧
      (IsUnramified B S hS f ∧ Mono f)) ?_
  intro p hp
  simp only [List.mem_cons] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | hnil
  · exact (closedImmersion_iff_universallyClosed_locallyFiniteType_mono
      B S hS hX hY f).trans
        (and_congr Iff.rfl
          (isUnramified_mono_iff_isLocallyOfFiniteType_mono
            B S hS hX hY f).symm)
  · exact Iff.rfl
  · exact and_congr Iff.rfl
      (isUnramified_mono_iff_isUnramified_universallyInjective
        B S hS hX hY f).symm
  · exact and_congr Iff.rfl
      (isUnramified_mono_iff_isLocallyOfFiniteType_mono
        B S hS hX hY f).symm
  · exact and_congr Iff.rfl
      (isUnramified_mono_iff_universallyInjective_locallyOfFiniteType_formallyUnramified
        B S hS hX hY f).symm
  · cases hnil

end AlgebraicGeometry.Space

end
