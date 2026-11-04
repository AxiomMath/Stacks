module

public import Mathlib.AlgebraicGeometry.Morphisms.FinitePresentation
public import StacksFrontier.RingTheory.PseudoCoherentMap.Locality

@[expose] public noncomputable section

/-!
# Pseudo-coherence of a morphism of schemes

A morphism of schemes is *pseudo-coherent* when the map on sections over every compatible pair
of affine opens is a pseudo-coherent ring map (Stacks 067Z). This can equivalently be checked on
suitable affine open coverings, which is the affine-local content of Stacks 067Y, and the whole
section is an instance of the general machinery for a property of ring maps that is local in the
sense of `RingHom.PropertyIsLocal`.

## Main definitions

* `AlgebraicGeometry.PseudoCoherent`: a morphism of schemes is pseudo-coherent if the map on
  sections over every compatible pair of affine opens is a pseudo-coherent ring map.

## Main results

* `AlgebraicGeometry.hasRingHomProperty_pseudoCoherent`: `AlgebraicGeometry.PseudoCoherent` is
  the morphism property attached to `RingHom.PseudoCoherent` by
  `AlgebraicGeometry.affineLocally`.
* `AlgebraicGeometry.pseudoCoherent_isZariskiLocalAtTarget`: pseudo-coherence is Zariski-local on
  the target (an instance).
* `AlgebraicGeometry.pseudoCoherent_tfae`: the first two equivalent characterizations of
  pseudo-coherence of a scheme morphism, namely the existence of affine open coverings on which
  the maps on sections are pseudo-coherent and the same condition for every compatible pair of
  affine opens.
* `AlgebraicGeometry.locallyOfFinitePresentation_of_pseudoCoherent`: **Stacks 0682**, a
  pseudo-coherent morphism of schemes is locally of finite presentation (an instance). With
  Mathlib's instance from `AlgebraicGeometry.LocallyOfFinitePresentation` to
  `AlgebraicGeometry.LocallyOfFiniteType` it also gives the clause of Stacks 067Y that a
  pseudo-coherent morphism is locally of finite type.

## Implementation notes

`AlgebraicGeometry.PseudoCoherent` is defined by condition (2) of Stacks 067Y, following the
shape of `AlgebraicGeometry.LocallyOfFiniteType`, so that
`AlgebraicGeometry.HasRingHomProperty` identifies it with
`AlgebraicGeometry.affineLocally RingHom.PseudoCoherent` and the affine-local API applies to it
verbatim. That identification is `AlgebraicGeometry.affineLocally_iff_forall_isAffineOpen`.

The third characterization of Stacks 067Y, that the morphism is locally of finite type and the
structure sheaf is pseudo-coherent relative to the base (Stacks 09UI), is not stated in this
module; see `AlgebraicGeometry.pseudoCoherent_tfae_three` in
`StacksFrontier.AlgebraicGeometry.PseudoCoherent.StructureSheafComparison`.

## References

* [The Stacks Project, Lemma 37.60.1 (067Y)](https://stacks.math.columbia.edu/tag/067Y)
* [The Stacks Project, Definition 37.60.2 (067Z)](https://stacks.math.columbia.edu/tag/067Z)
* [The Stacks Project, Lemma 37.60.5 (0682)](https://stacks.math.columbia.edu/tag/0682)
* [The Stacks Project, Definition 29.14.1 (01SR)](https://stacks.math.columbia.edu/tag/01SR)
-/

open CategoryTheory TopologicalSpace
open scoped AlgebraicGeometry

namespace AlgebraicGeometry

universe u

/-- A morphism of schemes `f : X ⟶ S` is pseudo-coherent if for every affine open `V ⊆ S` and every
affine open `U ⊆ X` with `U ⊆ f ⁻¹ᵁ V` the induced map on sections `Γ(S, V) ⟶ Γ(X, U)` is a
pseudo-coherent ring map. -/
@[mk_iff, stacks 067Z]
public class PseudoCoherent {X S : Scheme.{u}} (f : X ⟶ S) : Prop where
  pseudoCoherent_appLE (f) :
    ∀ {V : S.Opens} (_ : IsAffineOpen V) {U : X.Opens} (_ : IsAffineOpen U) (e : U ≤ f ⁻¹ᵁ V),
      (f.appLE V U e).hom.PseudoCoherent

/-- `AlgebraicGeometry.PseudoCoherent` is the morphism property induced by the local property
`RingHom.PseudoCoherent` of ring maps through `AlgebraicGeometry.affineLocally`. -/
public instance hasRingHomProperty_pseudoCoherent :
    HasRingHomProperty @PseudoCoherent @RingHom.PseudoCoherent where
  isLocal_ringHomProperty := RingHom.pseudoCoherent_isLocal
  eq_affineLocally' := by
    ext X S f
    rw [pseudoCoherent_iff, affineLocally_iff_forall_isAffineOpen]

/-- Pseudo-coherence is Zariski-local on the target, since it is affine-local.

Mathlib's `AlgebraicGeometry.HasRingHomProperty.instIsZariskiLocalAtTarget` is tried by type class
search but does not apply to `@PseudoCoherent`: assigning `@PseudoCoherent` to its argument of
type `CategoryTheory.MorphismProperty Scheme` would unfold `CategoryTheory.MorphismProperty`, which
the transparency of type class search does not do. This is not specific to pseudo-coherence: at
this Mathlib pin the same happens for Mathlib's own properties with
`AlgebraicGeometry.HasRingHomProperty`, such as `AlgebraicGeometry.LocallyOfFiniteType`,
`AlgebraicGeometry.LocallyOfFinitePresentation` and `AlgebraicGeometry.Smooth`, and Mathlib's
call sites switch the transparency check `backward.isDefEq.respectTransparency.types` off
locally; `AlgebraicGeometry.IsFinite.iff_isIntegralHom_and_locallyOfFiniteType`, for example,
does so and then uses Zariski locality on the target for `AlgebraicGeometry.LocallyOfFiniteType`.
This instance needs no such option, and can go once the generic instance applies again. -/
public instance pseudoCoherent_isZariskiLocalAtTarget :
    IsZariskiLocalAtTarget @PseudoCoherent :=
  HasRingHomProperty.instIsZariskiLocalAtTarget @PseudoCoherent

/-- The affine opens of a scheme contained in a given open `U` cover `U`. -/
public lemma iSup_affineOpens_subtype_eq {X : Scheme.{u}} (U : X.Opens) :
    (⨆ i : {V : X.affineOpens // V.1 ≤ U}, (i.1.1 : X.Opens)) = U := by
  refine le_antisymm (iSup_le fun i ↦ i.2) fun x hx ↦ ?_
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx U.2
  exact Opens.mem_iSup.mpr ⟨⟨⟨V, hV⟩, hVU⟩, hxV⟩

/-- For a morphism of schemes the following are equivalent: there is an affine open cover of the
base and, over each of its members, an affine open cover of its inverse image on which the maps on
sections are pseudo-coherent ring maps; and every compatible pair of affine opens has
pseudo-coherent map on sections. -/
@[stacks 067Y "the equivalence of (1) and (2)"]
public theorem pseudoCoherent_tfae {X S : Scheme.{u}} (f : X ⟶ S) :
    let pseudoCoherentOn := fun (V : S.Opens) (U : X.Opens)
        (h : U ≤ f ⁻¹ᵁ V) ↦
      letI : Algebra Γ(S, V) Γ(X, U) := (f.appLE V U h).hom.toAlgebra
      Algebra.PseudoCoherent Γ(S, V) Γ(X, U)
    List.TFAE [
      ∃ (J : Type u) (V : J → S.Opens),
        IsOpenCover V ∧
          (∀ j, IsAffineOpen (V j)) ∧
          ∀ j, ∃ (I : Type u) (U : I → X.Opens)
            (hU : (⨆ i, U i) = f ⁻¹ᵁ (V j)),
            (∀ i, IsAffineOpen (U i)) ∧
              ∀ i, pseudoCoherentOn (V j) (U i)
                ((le_iSup U i).trans hU.le),
      ∀ (U : X.Opens), IsAffineOpen U →
        ∀ (V : S.Opens), IsAffineOpen V →
          ∀ (h : U ≤ f ⁻¹ᵁ V), pseudoCoherentOn V U h] := by
  intro pseudoCoherentOn
  tfae_have 1 → 2 := by
    rintro ⟨J, V, hVcover, hVaff, hVpre⟩
    have hf : PseudoCoherent f := by
      refine (HasRingHomProperty.iff_exists_appLE (P := @PseudoCoherent)
        RingHom.pseudoCoherent_stableUnderCompositionWithLocalizationAway.left).mpr fun x ↦ ?_
      obtain ⟨j, hj⟩ := hVcover.exists_mem (f.base x)
      obtain ⟨I, U, hU, hUaff, hUpc⟩ := hVpre j
      obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hU ▸ hj : x ∈ ⨆ i, U i)
      exact ⟨⟨V j, hVaff j⟩, ⟨U i, hUaff i⟩, hi, (le_iSup U i).trans hU.le, hUpc i⟩
    intro U hU V hV h
    exact hf.pseudoCoherent_appLE hV hU h
  tfae_have 2 → 1 := by
    intro h
    refine ⟨S.affineOpens, fun V ↦ V.1, iSup_affineOpens_eq_top S, fun V ↦ V.2, fun V ↦ ?_⟩
    refine ⟨{U : X.affineOpens // U.1 ≤ f ⁻¹ᵁ (V : S.Opens)}, fun U ↦ U.1.1,
      iSup_affineOpens_subtype_eq _, fun U ↦ U.1.2, fun U ↦ ?_⟩
    exact h U.1.1 U.1.2 V.1 V.2 _
  tfae_finish

-- See note [lower instance priority]
/-- **Stacks 0682.** A pseudo-coherent morphism of schemes is locally of finite presentation.

On every compatible pair of affine opens the map on sections is a pseudo-coherent ring map,
hence of finite presentation by `RingHom.PseudoCoherent.finitePresentation`.

Followed by Mathlib's instance from `AlgebraicGeometry.LocallyOfFinitePresentation` to
`AlgebraicGeometry.LocallyOfFiniteType`, this is how type class search finds that a
pseudo-coherent morphism is locally of finite type, the clause of Stacks 067Y recorded by the
second tag. -/
@[stacks 0682, stacks 067Y "condition (2) implies the finite-type half of condition (3)"]
public instance (priority := 100) locallyOfFinitePresentation_of_pseudoCoherent {X S : Scheme.{u}}
    (f : X ⟶ S) [hf : PseudoCoherent f] : LocallyOfFinitePresentation f := by
  rw [HasRingHomProperty.eq_affineLocally @LocallyOfFinitePresentation]
  rw [HasRingHomProperty.eq_affineLocally @PseudoCoherent] at hf
  exact affineLocally_le (fun hf ↦ hf.finitePresentation) f hf

end AlgebraicGeometry
