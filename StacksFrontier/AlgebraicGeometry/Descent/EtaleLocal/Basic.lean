module

public import Mathlib.AlgebraicGeometry.Sites.Etale
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.Defs

/-!
# Consequences of étale locality on the source and target

A property of morphisms of schemes which is étale local on the source and target is local on
the source and local on the target for the étale precoverage, is preserved by postcomposition
with an étale morphism, and can be cancelled across an étale morphism on the target.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.respectsIso`: such a property is invariant
  under isomorphisms.
* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.of_comp_etale`: an étale morphism can be
  cancelled on the right of a composite.
* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.postcomp_of_etale`: postcomposition with an
  étale morphism preserves the property.
* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.isLocalAtSource_etalePrecoverage`: locality
  on the source for the étale precoverage.
* `AlgebraicGeometry.IsEtaleLocalOnSourceAndTarget.isLocalAtTarget`: locality on the target
  for the étale precoverage.

## Implementation notes

Source and target locality are Mathlib's `CategoryTheory.MorphismProperty.IsLocalAtSource` and
`CategoryTheory.MorphismProperty.IsLocalAtTarget` for `AlgebraicGeometry.Scheme.etalePrecoverage`.
Isomorphism invariance is derived once, from the étale precomposition and neighbourhood fields,
and is then used by both locality results.

## References

* [Stacks Project, Tag 04R0](https://stacks.math.columbia.edu/tag/04R0)
-/

@[expose] public section

namespace AlgebraicGeometry

open CategoryTheory

universe u

namespace IsEtaleLocalOnSourceAndTarget

/-- A property of morphisms of schemes that is étale local on the source and target is
invariant under isomorphisms. -/
theorem respectsIso (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P) : P.RespectsIso := by
  let : P.RespectsLeft (MorphismProperty.isomorphisms Scheme) := ⟨by
    intro X Y Z e he f hf
    let : IsIso e := he
    exact hP.precomp.precomp e (by infer_instance) f hf⟩
  let : P.RespectsRight (MorphismProperty.isomorphisms Scheme) := ⟨by
    intro X Y Z e he f hf
    let : IsIso e := he
    apply (hP.iff_forall_exists_etale_neighborhood (f ≫ e)).2
    intro x
    obtain ⟨U, V, a, b, h, u, ha, hb, hx, hcomm, hh⟩ :=
      (hP.iff_forall_exists_etale_neighborhood f).1 hf x
    refine ⟨U, V, a, b ≫ e, h, u, ha, ?_, hx, ?_, hh⟩
    · infer_instance
    · simpa only [Category.assoc] using congrArg (· ≫ e) hcomm⟩
  infer_instance

/-- An étale morphism can be cancelled on the right of a composite for a property which is
étale local on the source and target. -/
@[stacks 04R0 "cancel_etale"]
lemma of_comp_etale {P : MorphismProperty Scheme.{u}}
    (hP : IsEtaleLocalOnSourceAndTarget P)
    {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    (hg : Etale g) (hfg : P (f ≫ g)) : P f :=
  let s : X ⟶ Limits.pullback (f ≫ g) g := Limits.pullback.lift (𝟙 X) f (by simp)
  have hs : Etale s := MorphismProperty.of_postcomp (@Etale : MorphismProperty Scheme) s
    (Limits.pullback.fst (f ≫ g) g)
    (show Etale (Limits.pullback.fst (f ≫ g) g) from inferInstance)
    (by simpa only [s, Limits.pullback.lift_fst] using (inferInstance : Etale (𝟙 X)))
  by simpa only [s, Limits.pullback.lift_snd] using
    hP.precomp.precomp s hs _ (hP.pullbackSnd_of_etale (f ≫ g) hfg g hg)

/-- A property that is étale local on the source and target is preserved by postcomposition
with an étale morphism. -/
@[stacks 04R0 "postcompose_etale"]
theorem postcomp_of_etale (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P) {X Y Z : Scheme.{u}} (f : X ⟶ Y) (hf : P f)
    (g : Y ⟶ Z) (hg : Etale g) : P (f ≫ g) :=
  (hP.iff_forall_exists_etale_neighborhood (f ≫ g)).2 fun x ↦
    ⟨X, Y, 𝟙 X, g, f, x, inferInstance, hg, by simp, by simp, hf⟩

/-- A point of `X` lies in the image of an étale morphism of a covering family of the étale
precoverage. -/
private theorem exists_etale_apply_eq_of_mem_etalePrecoverage {X : Scheme.{u}} {R : Presieve X}
    (hR : R ∈ Scheme.etalePrecoverage X) (x : X) :
    ∃ (Z : Scheme.{u}) (g : Z ⟶ X), R g ∧ Etale g ∧ ∃ z, g z = x := by
  obtain ⟨hcover, hEtale⟩ := hR
  obtain ⟨Z, g, hg, z, hz⟩ :=
    (Presieve.mem_comap_jointlySurjectivePrecoverage_iff (F := Scheme.forget)).mp hcover x
  exact ⟨Z, g, hg, hEtale hg, z, hz⟩

/-- A morphism property étale local on the source and target is étale local on the source. -/
@[stacks 04R0 "local_source"]
theorem isLocalAtSource_etalePrecoverage (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P) :
    P.IsLocalAtSource Scheme.etalePrecoverage :=
  let : P.RespectsIso := respectsIso P hP
  { precomp := by
      intro X Y Z g hg f hf
      let : IsIso g := hg
      exact MorphismProperty.RespectsIso.precomp P g f hf
    postcomp := by
      intro X Y Z g hg f hf
      let : IsIso g := hg
      exact MorphismProperty.RespectsIso.postcomp P g f hf
    comp := by
      intro X Y f R hR U g hg hf
      exact hP.precomp.precomp g (hR.2 hg) f hf
    of_forall_comp := by
      intro X Y f R hR h
      apply (hP.iff_forall_exists_etale_neighborhood f).2
      intro x
      obtain ⟨Z, g, hg, hgEtale, z, hz'⟩ := exists_etale_apply_eq_of_mem_etalePrecoverage hR x
      obtain ⟨U, V, a, b, k, u, ha, hb, hu, hcomm, hk⟩ :=
        (hP.iff_forall_exists_etale_neighborhood (g ≫ f)).1 (h hg) z
      refine ⟨U, V, a ≫ g, b, k, u, ?_, hb, ?_, ?_, hk⟩
      · let : Etale a := ha
        infer_instance
      · change g (a u) = x
        simpa only [hu] using hz'
      · simpa only [Category.assoc] using hcomm
  }

/-- A property of scheme morphisms that is étale local on the source and target is étale local
on the target. -/
@[stacks 04R0 "local_target"]
theorem isLocalAtTarget (P : MorphismProperty Scheme.{u})
    (hP : IsEtaleLocalOnSourceAndTarget P) :
    P.IsLocalAtTarget Scheme.etalePrecoverage :=
  let : P.RespectsIso := respectsIso P hP
  { pullbackSnd := by
      intro X Y f R Z g hR hg hf
      exact hP.pullbackSnd_of_etale f hf g (hR.2 hg)
    of_forall_pullbackSnd := by
      intro X Y f R hR h
      apply (hP.iff_forall_exists_etale_neighborhood f).2
      intro x
      obtain ⟨Z, g, hg, hgEtale, z, hz⟩ :=
        exists_etale_apply_eq_of_mem_etalePrecoverage hR (f.base x)
      let : Etale g := hgEtale
      obtain ⟨p, hp_fst, _⟩ :=
        Scheme.exists_preimage_of_isPullback (IsPullback.of_hasPullback f g) x z hz.symm
      obtain ⟨U, V, a, b, k, u, ha, hb, hu, hcomm, hk⟩ :=
        (hP.iff_forall_exists_etale_neighborhood (Limits.pullback.snd f g)).1 (h hg) p
      refine ⟨U, V, a ≫ Limits.pullback.fst f g, b ≫ g, k, u, ?_, ?_, ?_, ?_, hk⟩
      · let : Etale a := ha
        let : Etale (Limits.pullback.fst f g) := by infer_instance
        infer_instance
      · let : Etale b := hb
        infer_instance
      · change (Limits.pullback.fst f g).base (a.base u) = x
        rw [hu, hp_fst]
      · simpa only [Category.assoc, ← Limits.pullback.condition] using
          congrArg (· ≫ g) hcomm }

end IsEtaleLocalOnSourceAndTarget

end AlgebraicGeometry
