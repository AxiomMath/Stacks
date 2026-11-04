module

public import StacksFrontier.AlgebraicGeometry.InvertibleQuotient.EpiIso
public import StacksFrontier.AlgebraicGeometry.ProjectiveBundle.TautologicalInvertible

/-!
# Universal tautological data: an inhabitant, and the obstruction at rank one

`Stacks.RelativeProj.TautologicalDatum.IsUniversal` is the hypothesis under which
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/Sections.lean` builds Tag 0B3V's bijection
between the sections of `π : 𝐏(F) ⟶ X` and the invertible quotients of `F`. Six declarations
there are quantified over it. This file inhabits it, and measures exactly what inhabiting it
costs for the canonical datum of an invertible module.

**An inhabitant.** Over a scheme with no points every tautological datum is universal, with no
hypothesis on the datum or on the module: the projection `π` is an isomorphism because its
target is empty, so `π` has exactly one section, and sheaves of modules over a scheme with no
points have a single morphism between any two objects, so every invertible quotient is
classified by that section. Specialising to the structure sheaf of the empty scheme gives an
unconditional term, `Stacks.RelativeProj.isUniversal_tautologicalDatumUnit_empty`.

**What that inhabitant does not reach.** It is degenerate on purpose, and the degeneracy is
recorded rather than left for a reader to discover: over an empty scheme the sections of `π`
form a one-element type (`Stacks.RelativeProj.unique_sections_of_isEmpty`) and so do the
isomorphism classes of invertible quotients
(`Stacks.RelativeProj.subsingleton_invertibleQuotientClass_of_isEmpty`), so the bijection is
between two singletons and no projective-space content is exercised.

**The obstruction for a scheme with points.** For the canonical datum of an invertible module,
`Stacks.RelativeProj.TautologicalDatum.ofInvertible`, the universal surjection is the identity,
so the pulled-back tautological map is an isomorphism and the relation *`σ` classifies `Q`* does
not mention `σ` at all: it says exactly that `Q.q` is an isomorphism
(`Stacks.RelativeProj.TautologicalDatum.classifies_ofInvertible_iff`). Hence `IsUniversal` for
that datum is *equivalent* to the conjunction of three statements about `X` and `F` and nothing
else (`Stacks.RelativeProj.TautologicalDatum.isUniversal_ofInvertible_iff`):

1. every invertible quotient of `F` is an isomorphism;
2. `π` has a section;
3. `π` has at most one section.

Both directions are proved, so these are not sufficient conditions chosen for convenience:
nobody can inhabit `IsUniversal` at a canonical rank-one datum without them.

**And item 1 is a theorem**, `Stacks.Divisors.isIso_q_of_isInvertible`, so the obstruction is
items 2 and 3 alone: `Stacks.RelativeProj.TautologicalDatum.isUniversal_ofInvertible_iff_sections`
says that for the canonical datum of an invertible module, `IsUniversal` **is** the statement that
`π : 𝐏(F) ⟶ X` has exactly one section. That is the identification of `𝐏(F)` with `X` on
`X`-points, and it is the single thing a non-degenerate inhabitant needs.

## Main definitions

* `Stacks.Modules.isoOfIsEmpty`: any two sheaves of modules over a scheme with no points are
  isomorphic.

## Main results

* `Stacks.Modules.subsingleton_sections_of_isEmpty`: the sections of a sheaf of modules over a
  scheme with no points form a subsingleton, the ring of sections of the structure sheaf over
  the only open being the zero ring.
* `Stacks.Modules.subsingleton_hom_of_isEmpty`: there is at most one morphism between two
  sheaves of modules over a scheme with no points.
* `Stacks.RelativeProj.TautologicalDatum.isUniversal_of_isEmpty`: **every tautological datum
  over a scheme with no points is universal.** No hypothesis on the datum or the module.
* `Stacks.RelativeProj.isUniversal_tautologicalDatumUnit_empty`: **an unconditional inhabitant
  of `IsUniversal`**, at the structure sheaf of the empty scheme.
* `Stacks.RelativeProj.unique_sections_of_isEmpty` and
  `Stacks.RelativeProj.subsingleton_invertibleQuotientClass_of_isEmpty`: the two sides of Tag
  0B3V's bijection at that inhabitant are singletons, which is the reach of the witness.
* `Stacks.RelativeProj.TautologicalDatum.isIso_pullbackQuotientMap_ofInvertible`: the pulled-back
  tautological map of a canonical rank-one datum is an isomorphism, its universal surjection
  being the identity.
* `Stacks.RelativeProj.TautologicalDatum.classifies_ofInvertible_iff`: for such a datum the
  classifying relation is independent of the section and says that the quotient map is an
  isomorphism.
* `Stacks.RelativeProj.TautologicalDatum.isUniversal_ofInvertible_iff`: the equivalence above.
* `Stacks.RelativeProj.TautologicalDatum.isUniversal_ofInvertible_iff_sections`: **the precise
  obstruction to a non-degenerate inhabitant, with its first item discharged.** For the canonical
  datum of an invertible module `IsUniversal` is equivalent to `π` having exactly one section,
  and to nothing else.

## Implementation notes

**Why the empty scheme and not an invertible module over a scheme with points.** Items 2 and 3
of `isUniversal_ofInvertible_iff` together say that `π : 𝐏(F) ⟶ X` is a bijection on `X`-points,
which for invertible `F` is the identification of `𝐏(F)` with `X`. Nothing in this repository
constructs that identification or any consequence of it: of the occurrences of
`Stacks.RelativeProj.Situation.relativeProjToBase` in the two Lean trees, none asserts it to be
an isomorphism, a monomorphism or an epimorphism. Over a scheme with no points `π` is an
isomorphism because its target has no points, and that is the whole reason the inhabitant is
there.

**The degeneracy of the empty-scheme witness, and the two subsingleton statements.**
`subsingleton_invertibleQuotientClass_of_isEmpty` is for an *arbitrary* module over a scheme with
no points; `Stacks.Divisors.subsingleton_invertibleQuotientClass_of_isInvertible` is for an
*invertible* module over an arbitrary scheme. Neither implies the other, so they are not
duplicates, and the empty-scheme one is what records how little the witness reaches.

**The one wall crossed, and the shape of the cure.** `(ofInvertible X F hF).twist` and
`(Scheme.Modules.pullback π).obj F` are equal only by unfolding the structure instance, the
wall `TautologicalBaseChange.lean` records at three sites. So `rw [ofInvertible_univ]` inside
`IsIso ((ofInvertible X F hF).pullbackQuotientMap σ hσ)` fails — *"not type-correct under the
`implicit` transparency level"*, with the real error an application type mismatch between the
two spellings of the twist. The cure is the declared type: `isIso_univ_ofInvertible` is
`inferInstanceAs (IsIso (𝟙 _))` at the written-out spelling, and with it in context
`unfold pullbackQuotientMap; infer_instance` goes through, exactly as
`epi_pullbackQuotientMap` does in `Sections.lean`.

**Morphisms are compared on sections, not on stalks.** `Subsingleton Γ(X, ⊥)` is Mathlib's, the
structure sheaf of any scheme having the zero ring as its sections over the empty open; a scheme
with no points has `⊥` as its only open, and `Module.subsingleton` carries the triviality to the
sections of any module. `AlgebraicGeometry.Scheme.Modules.hom_ext` then compares two morphisms
open by open. No stalk, no sheaf condition and no local triviality enters.

**No `@[stacks 0B3V]` attribute is attached.** The tag's bijection is registered on
`Stacks.RelativeProj.projectiveBundleSectionsEquiv` of
`StacksFrontier/AlgebraicGeometry/ProjectiveBundle/ClassifiesDescent.lean`, the unconditional
bijection at the bundle's own tautological datum; what is proved here is a *degenerate*
inhabitant of `IsUniversal` for an arbitrary datum over a scheme with no points, and a
characterisation of that hypothesis at rank one. Both carry hypotheses the tag does not.

## References

* [Stacks Project, Tag 0B3V](https://stacks.math.columbia.edu/tag/0B3V)
* [Stacks Project, Tag 01NS](https://stacks.math.columbia.edu/tag/01NS)
* [Stacks Project, Tag 01OB](https://stacks.math.columbia.edu/tag/01OB)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits

universe u

namespace Stacks.Modules

/-- **The sections of a sheaf of modules over a scheme with no points are trivial.** The only
open of such a scheme is `⊥`, over which the structure sheaf has the zero ring as its sections,
and a module over the zero ring is trivial. -/
theorem subsingleton_sections_of_isEmpty (X : Scheme.{u}) [IsEmpty X] (M : X.Modules)
    (U : X.Opens) : Subsingleton Γ(M, U) := by
  obtain rfl : U = ⊥ := le_bot_iff.mp fun x _ => isEmptyElim (α := X) x
  exact Module.subsingleton Γ(X, ⊥) _

/-- **There is at most one morphism between two sheaves of modules over a scheme with no
points**, two morphisms agreeing on the sections over every open. -/
theorem subsingleton_hom_of_isEmpty (X : Scheme.{u}) [IsEmpty X] (M N : X.Modules) :
    Subsingleton (M ⟶ N) := by
  refine ⟨fun f g => Scheme.Modules.hom_ext f g fun U => ?_⟩
  ext x
  exact (subsingleton_sections_of_isEmpty X N U).elim _ _

/-- **Any two sheaves of modules over a scheme with no points are isomorphic**, the zero
morphisms being mutually inverse because there is no other morphism to be. -/
def isoOfIsEmpty (X : Scheme.{u}) [IsEmpty X] (M N : X.Modules) : M ≅ N :=
  letI := subsingleton_hom_of_isEmpty X M M
  letI := subsingleton_hom_of_isEmpty X N N
  { hom := 0
    inv := 0
    hom_inv_id := Subsingleton.elim _ _
    inv_hom_id := Subsingleton.elim _ _ }

end Stacks.Modules

namespace Stacks.RelativeProj

open Stacks.Divisors

variable {X : Scheme.{u}} {F : X.Modules} [F.IsQuasicoherent]

/-- **Every tautological datum over a scheme with no points is universal.** The projection
`π : 𝐏(F) ⟶ X` is an isomorphism, its target having no points, so it has exactly one section;
and any two sheaves of modules on such a scheme are isomorphic by a unique morphism, so that
section classifies every invertible quotient. -/
instance TautologicalDatum.isUniversal_of_isEmpty [IsEmpty X] (D : TautologicalDatum X F) :
    D.IsUniversal where
  exists_classifies Q := by
    refine ⟨inv (projectiveBundleToBase X F), IsIso.inv_hom_id _, ?_⟩
    refine (D.classifies_iff _ _ Q).mpr ⟨Stacks.Modules.isoOfIsEmpty X _ _, ?_⟩
    exact (Stacks.Modules.subsingleton_hom_of_isEmpty X F Q.L).elim _ _
  eq_of_classifies σ σ' hσ hσ' _ _ _ :=
    (cancel_mono (projectiveBundleToBase X F)).mp (by rw [hσ, hσ'])

/-- **An unconditional inhabitant of `TautologicalDatum.IsUniversal`**: the tautological datum
of the structure sheaf of the empty scheme. -/
theorem isUniversal_tautologicalDatumUnit_empty :
    (tautologicalDatumUnit (∅ : Scheme.{u})).IsUniversal :=
  TautologicalDatum.isUniversal_of_isEmpty _

/-- **The projection of a projective bundle over a scheme with no points has exactly one
section.** This is one side of Tag 0B3V's bijection at the inhabitant above, and it records how
little that inhabitant reaches. -/
@[instance_reducible] def unique_sections_of_isEmpty [IsEmpty X] :
    Unique { σ : X ⟶ projectiveBundle X F // σ ≫ projectiveBundleToBase X F = 𝟙 X } where
  default := ⟨inv (projectiveBundleToBase X F), IsIso.inv_hom_id _⟩
  uniq σ := Subtype.ext <|
    (cancel_mono (projectiveBundleToBase X F)).mp (by rw [σ.2, IsIso.inv_hom_id])

/-- **Over a scheme with no points all invertible quotients of a module are identified.** This
is the other side of Tag 0B3V's bijection at the inhabitant above. -/
theorem subsingleton_invertibleQuotientClass_of_isEmpty (X : Scheme.{u}) [IsEmpty X]
    (E : X.Modules) : Subsingleton (InvertibleQuotientClass X E) :=
  ⟨Quotient.ind₂ fun Q R => Quotient.sound
    ⟨Stacks.Modules.isoOfIsEmpty X Q.L R.L,
      (Stacks.Modules.subsingleton_hom_of_isEmpty X E R.L).elim _ _⟩⟩

/-- The universal surjection of the canonical datum of an invertible module is an isomorphism:
it is the identity. Stated with its type written out, because `ofInvertible_univ` cannot be
rewritten under the twist's two spellings. -/
theorem TautologicalDatum.isIso_univ_ofInvertible
    (hF : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F) :
    IsIso (TautologicalDatum.ofInvertible X F hF).univ :=
  inferInstanceAs (IsIso (𝟙 ((Scheme.Modules.pullback (projectiveBundleToBase X F)).obj F)))

/-- **The pulled-back tautological map of the canonical datum of an invertible module is an
isomorphism.** Its three comparisons are isomorphisms and its universal surjection is the
identity. -/
theorem TautologicalDatum.isIso_pullbackQuotientMap_ofInvertible
    (hF : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F)
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X) :
    IsIso ((TautologicalDatum.ofInvertible X F hF).pullbackQuotientMap σ hσ) := by
  have := TautologicalDatum.isIso_univ_ofInvertible hF
  unfold TautologicalDatum.pullbackQuotientMap
  infer_instance

/-- **For the canonical datum of an invertible module the classifying relation does not mention
the section**: it says exactly that the quotient map is an isomorphism. The pulled-back
tautological map is invertible, so an isomorphism carrying it to `Q.q` exists precisely when
`Q.q` is invertible. -/
theorem TautologicalDatum.classifies_ofInvertible_iff
    (hF : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F)
    (σ : X ⟶ projectiveBundle X F) (hσ : σ ≫ projectiveBundleToBase X F = 𝟙 X)
    (Q : InvertibleQuotient X F) :
    (TautologicalDatum.ofInvertible X F hF).Classifies σ hσ Q ↔ IsIso Q.q := by
  have hiso := TautologicalDatum.isIso_pullbackQuotientMap_ofInvertible hF σ hσ
  rw [TautologicalDatum.classifies_iff]
  constructor
  · rintro ⟨α, hα⟩
    rw [← hα]
    infer_instance
  · intro hq
    exact ⟨(asIso ((TautologicalDatum.ofInvertible X F hF).pullbackQuotientMap σ hσ)).symm ≪≫
      asIso Q.q, IsIso.hom_inv_id_assoc _ _⟩

/-- **The precise obstruction to a universal tautological datum at rank one.** For the canonical
datum of an invertible module, `IsUniversal` holds exactly when every invertible quotient of `F`
is an isomorphism and the projection has exactly one section. The equivalence is proved in both
directions, so neither item can be avoided: the two about sections together say that `𝐏(F)` has
the same `X`-points as `X`, which for an invertible module is the identification of `𝐏(F)` with
the base. -/
theorem TautologicalDatum.isUniversal_ofInvertible_iff
    (hF : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F) :
    (TautologicalDatum.ofInvertible X F hF).IsUniversal ↔
      ((∀ Q : InvertibleQuotient X F, IsIso Q.q) ∧
        Nonempty { σ : X ⟶ projectiveBundle X F // σ ≫ projectiveBundleToBase X F = 𝟙 X } ∧
        Subsingleton { σ : X ⟶ projectiveBundle X F //
          σ ≫ projectiveBundleToBase X F = 𝟙 X }) := by
  let Q₀ : InvertibleQuotient X F := ⟨F, hF, 𝟙 F, inferInstance⟩
  constructor
  · intro h
    refine ⟨fun Q => ?_, ?_, ?_⟩
    · obtain ⟨σ, hσ, hcl⟩ := h.exists_classifies Q
      exact (TautologicalDatum.classifies_ofInvertible_iff hF σ hσ Q).1 hcl
    · obtain ⟨σ, hσ, _⟩ := h.exists_classifies Q₀
      exact ⟨⟨σ, hσ⟩⟩
    · exact ⟨fun σ σ' => Subtype.ext <| h.eq_of_classifies σ.1 σ'.1 σ.2 σ'.2
        Q₀
        ((TautologicalDatum.classifies_ofInvertible_iff hF σ.1 σ.2 _).2 inferInstance)
        ((TautologicalDatum.classifies_ofInvertible_iff hF σ'.1 σ'.2 _).2 inferInstance)⟩
  · rintro ⟨hall, ⟨σ₀⟩, hsub⟩
    exact
      { exists_classifies := fun Q => ⟨σ₀.1, σ₀.2,
          (TautologicalDatum.classifies_ofInvertible_iff hF σ₀.1 σ₀.2 Q).2 (hall Q)⟩
        eq_of_classifies := fun σ σ' hσ hσ' _ _ _ =>
          congrArg Subtype.val (hsub.elim ⟨σ, hσ⟩ ⟨σ', hσ'⟩) }

/-- **The obstruction, with its module-theoretic item discharged: for the canonical datum of an
invertible module, `IsUniversal` is exactly the statement that the projection has one section.**
The first item of `isUniversal_ofInvertible_iff` is the theorem
`Stacks.Divisors.isIso_q_of_isInvertible`, so nothing about modules remains: what a
non-degenerate inhabitant needs, and all it needs, is that `𝐏(F) ⟶ X` be a bijection on
`X`-points. -/
theorem TautologicalDatum.isUniversal_ofInvertible_iff_sections
    (hF : AlgebraicGeometry.SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 F) :
    (TautologicalDatum.ofInvertible X F hF).IsUniversal ↔
      (Nonempty { σ : X ⟶ projectiveBundle X F // σ ≫ projectiveBundleToBase X F = 𝟙 X } ∧
        Subsingleton { σ : X ⟶ projectiveBundle X F //
          σ ≫ projectiveBundleToBase X F = 𝟙 X }) := by
  rw [TautologicalDatum.isUniversal_ofInvertible_iff hF]
  exact ⟨fun h => h.2, fun h => ⟨fun Q => isIso_q_of_isInvertible hF Q, h.1, h.2⟩⟩

end Stacks.RelativeProj

end
