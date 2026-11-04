module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Basic

/-!
# Characterizations of properties étale local on the source and target

For a property of morphisms of schemes that is étale local on both source and target,
membership can be tested on étale diagrams, on an étale cover of either scheme, or on
successive étale covers of both schemes.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.iff_forall_etale_diagrams`: testing every
  étale diagram.
* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.iff_exists_surjective_etale_diagram`:
  testing one diagram with a surjective source map.
* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.iff_exists_etale_target_cover`: testing
  base changes along a target cover.
* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.iff_exists_etale_source_cover`: testing
  composites from a source cover.
* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.iff_exists_bi_etale_covers`: testing after
  successive covers on both sides.

## Implementation notes

The neighbourhood characterization is already given by the field
`AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.iff_forall_exists_etale_neighborhood`, which
is registered below. The remaining characterizations are stated separately as equivalences
with the original property. An étale covering is represented by Mathlib's
`AlgebraicGeometry.Scheme.Cover AlgebraicGeometry.Scheme.etalePrecoverage`; the pullback is
oriented so that its first projection maps to the target cover member.

## References

* [Stacks Project, Tag 04R1](https://stacks.math.columbia.edu/tag/04R1)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits

universe u

namespace IsEtaleLocalOnSourceAndTarget

add_to_stacks 04R1 "part (b)"
  AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.iff_forall_exists_etale_neighborhood

variable {P : MorphismProperty Scheme.{u}} {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- A property étale local on source and target holds iff it holds in every commuting square
whose vertical maps are étale. -/
@[stacks 04R1 "part (c)"]
theorem iff_forall_etale_diagrams (hP : IsEtaleLocalOnSourceAndTarget P) :
    P f ↔
      ∀ {U V : Scheme.{u}} (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V),
        Etale a → Etale b → h ≫ b = a ≫ f → P h := by
  constructor
  · intro hf U V a b h ha hb hcomm
    apply of_comp_etale hP h b hb
    simpa [hcomm] using hP.precomp.precomp a ha f hf
  · exact fun h => h (𝟙 X) (𝟙 Y) f inferInstance inferInstance (by simp)

/-- It suffices to test one commuting étale square whose map to the source is surjective. -/
@[stacks 04R1 "part (d)"]
theorem iff_exists_surjective_etale_diagram (hP : IsEtaleLocalOnSourceAndTarget P) :
    P f ↔
      ∃ (U V : Scheme.{u}) (a : U ⟶ X) (b : V ⟶ Y) (h : U ⟶ V),
        Etale a ∧ Etale b ∧ Function.Surjective a.base ∧
          h ≫ b = a ≫ f ∧ P h := by
  constructor
  · intro hf
    exact ⟨X, Y, 𝟙 X, 𝟙 Y, f, inferInstance, inferInstance,
      fun y => ⟨y, rfl⟩, by simp, hf⟩
  · rintro ⟨U, V, a, b, h, ha, hb, hsurj, hcomm, hh⟩
    have hfa : P (a ≫ f) := by
      rw [← hcomm]
      exact postcomp_of_etale P hP h hh b hb
    let 𝒰 : X.Cover.{u} Scheme.etalePrecoverage :=
      Scheme.Cover.mkOfCovers PUnit.{u + 1} (fun _ => U) (fun _ => a)
        (fun x => ⟨PUnit.unit, hsurj x⟩)
    exact (isLocalAtSource_etalePrecoverage P hP).of_zeroHypercover 𝒰 fun _ => hfa

/-- For an isomorphism-invariant property, the two projections of a pullback satisfy it
simultaneously. -/
private theorem fst_iff_snd_pullback (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {X Y Z : Scheme.{u}} (f : X ⟶ Z) (g : Y ⟶ Z) :
    P (pullback.fst g f) ↔ P (pullback.snd f g) := by
  rw [← pullbackSymmetry_hom_comp_fst, P.cancel_left_of_respectsIso]

/-- An étale-local property can be tested after an étale covering of the target. -/
@[stacks 04R1 "part (e)"]
theorem iff_exists_etale_target_cover (hP : IsEtaleLocalOnSourceAndTarget P) :
    P f ↔
      ∃ 𝒰 : Y.Cover.{u} Scheme.etalePrecoverage,
      ∀ i : 𝒰.I₀, P (pullback.fst (𝒰.f i) f) := by
  let hlocal := isLocalAtTarget P hP
  let : P.IsLocalAtTarget Scheme.etalePrecoverage := hlocal
  constructor
  · intro hf
    let 𝒰 : Y.Cover.{u} Scheme.etalePrecoverage :=
      Scheme.Cover.mkOfCovers PUnit (fun _ => Y) (fun _ => 𝟙 Y)
        (fun y => ⟨PUnit.unit, y, rfl⟩)
    exact ⟨𝒰, fun i => (fst_iff_snd_pullback P f (𝒰.f i)).mpr (hlocal.pullbackSnd 𝒰.mem₀ ⟨i⟩ hf)⟩
  · rintro ⟨𝒰, h𝒰⟩
    exact hlocal.of_zeroHypercover 𝒰 fun i => (fst_iff_snd_pullback P f (𝒰.f i)).mp (h𝒰 i)

/-- An étale-local property can be tested after an étale covering of the source. -/
@[stacks 04R1 "part (f)"]
theorem iff_exists_etale_source_cover (hP : IsEtaleLocalOnSourceAndTarget P) :
    P f ↔
      ∃ 𝒰 : X.Cover.{u} Scheme.etalePrecoverage,
      ∀ i : 𝒰.I₀, P (𝒰.f i ≫ f) := by
  constructor
  · intro hf
    let 𝒰 : X.Cover.{u} Scheme.etalePrecoverage :=
      Scheme.Cover.mkOfCovers PUnit (fun _ => X) (fun _ => 𝟙 X)
        (fun x => ⟨PUnit.unit, x, rfl⟩)
    exact ⟨𝒰, fun _ => show P (𝟙 X ≫ f) by simpa using hf⟩
  · rintro ⟨𝒰, h𝒰⟩
    exact (isLocalAtSource_etalePrecoverage P hP).of_zeroHypercover 𝒰 h𝒰

/-- An étale-local property can be tested after covering the target and then the base-changed
source by étale morphisms. -/
@[stacks 04R1 "part (g)"]
theorem iff_exists_bi_etale_covers (hP : IsEtaleLocalOnSourceAndTarget P) :
    P f ↔
      ∃ 𝒰 : Y.Cover.{u} Scheme.etalePrecoverage,
        ∀ i : 𝒰.I₀,
          ∃ 𝒱 : (pullback (𝒰.f i) f).Cover.{u} Scheme.etalePrecoverage,
            ∀ j : 𝒱.I₀, P (𝒱.f j ≫ pullback.fst (𝒰.f i) f) :=
  (iff_exists_etale_target_cover f hP).trans <| exists_congr fun 𝒰 => forall_congr' fun i =>
    iff_exists_etale_source_cover (pullback.fst (𝒰.f i) f) hP

end IsEtaleLocalOnSourceAndTarget

end AlgebraicGeometry
