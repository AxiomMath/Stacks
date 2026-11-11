module

public import StacksFrontier.AlgebraicGeometry.MeromorphicSectionsTensor.Basic
public import StacksFrontier.AlgebraicGeometry.MeromorphicQuasicoherent.Criteria

/-!
# Quasi-coherence of the sheaf of meromorphic sections on a reduced or locally Noetherian scheme

Part (2) of Stacks Tag 02OW and the corresponding clause of Tag 0EMH assert that the sheaf of
meromorphic sections of a quasi-coherent `𝒪_X`-module is quasi-coherent. Both follow from the
identification `𝒦_X(F) = 𝒦_X ⊗_{𝒪_X} F` of
`Stacks.AlgebraicGeometry.MeromorphicSectionsTensor.isQuasicoherent_meromorphicSections` together
with quasi-coherence of the sheaf of meromorphic functions, which is part (1) of the same tag.

## Main results

* `Stacks.AlgebraicGeometry.MeromorphicSectionsTensor.meromorphicSections_isQuasicoherent`: the
  statement for a reduced scheme whose quasi-compact opens have finitely many irreducible
  components.
* In the same namespace, `meromorphicSections_isQuasicoherent_of_noEmbeddedPoints` is the
  statement for a locally Noetherian scheme without embedded points.

## Implementation notes

Neither theorem carries any hypothesis beyond those of its Stacks statement: the hypotheses are
used only to produce quasi-coherence of the sheaf of meromorphic functions, which is proved for
both as part
(1) of Tag 02OW and the corresponding clause of Tag 0EMH.

The last three declarations of this file restate the two results above (the first tagged 02OW
part (2), the second one clause of Tag 0EMH) in the binder order of the reference statements,
with every reference constant replaced by its own defining expression. The six `card…`
abbreviations above them transcribe, one by one, the bodies of the reference constants the two
statements use — the sheaf of total quotient rings and its structure map (Tag 01X4, by
sheafifying `AlgebraicGeometry.TopCat.Presheaf.totalQuotientPresheaf` and its unit), the
`RingCat`-valued form of a sheaf of commutative rings (Tag 03ER/04BR), the extension-of-scalars
functor (Tag 03CZ, whose body is
`SheafOfModules.forget ⋙ Stacks.PresheafOfModules.ChangeOfRings.changeOfRings ⋙
  PresheafOfModules.sheafification`), and
finally the sheaf of meromorphic sections read back as an `𝒪_X`-module. They are transcribed as
separate abbreviations rather than as one inlined expression for a concrete reason: inside a
single term of that size the module universe of `PresheafOfModules.sheafification` is still
undetermined when its locally-bijective-morphism instances are searched for, and the search
fails, while the same instance is found at once when the sheafification functor's type is
written down. Each abbreviation is the reference statement's own text.

As for `Stacks.AlgebraicGeometry.GenericPointCoproduct`
`.meromorphicFunctions_iso_coproduct_of_noEmbeddedPoints`, the embedded-point
predicate is inlined down to `Stacks.Divisors.IsAssociatedPoint`, which is the
associated-point predicate of Tag 02OJ with the same module structure on the stalk; the
reference statement supplies that structure by a `letI` because typeclass resolution does not
find it for an `X.Modules`. The reference statement's `x' ⤳ x` is the specialization relation,
which is how `AlgebraicGeometry.IsEmbeddedAssociatedPoint` states it.

## References

* [Stacks Project, Tag 02OW](https://stacks.math.columbia.edu/tag/02OW)
* [Stacks Project, Tag 0EMH](https://stacks.math.columbia.edu/tag/0EMH)
* [Stacks Project, Tag 01X4](https://stacks.math.columbia.edu/tag/01X4)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ)
-/

@[expose] public noncomputable section

open CategoryTheory Limits TopologicalSpace
open AlgebraicGeometry
open scoped AlgebraicGeometry

universe u

namespace Stacks.AlgebraicGeometry.MeromorphicSectionsTensor

open Stacks.AlgebraicGeometry.GenericPointDecomposition

/-- **Stacks Project, Tag 02OW, part (2), quasi-coherence.** On a reduced scheme whose
quasi-compact opens have finitely many irreducible components, the sheaf of meromorphic sections
of a quasi-coherent `𝒪_X`-module is quasi-coherent. -/
@[stacks 02OW "part (2), quasi-coherence"]
theorem meromorphicSections_isQuasicoherent (X : Scheme.{u}) [IsReduced X]
    (hfinite : GenericPointProduct.FiniteComponentsOnCompactOpens X)
    (F : X.Modules) [F.IsQuasicoherent] :
    (meromorphicSections X F).IsQuasicoherent :=
  isQuasicoherent_meromorphicSections X F
    (MeromorphicQuasicoherent.meromorphicFunctions_isQuasicoherent X hfinite) inferInstance

/-- **Stacks Project, Tag 0EMH, quasi-coherence of meromorphic sections.** On a locally Noetherian
scheme without embedded points, the sheaf of meromorphic sections of a quasi-coherent
`𝒪_X`-module is quasi-coherent.
One clause of [Stacks, Tag 0EMH]; the complete statement is
`AlgebraicGeometry.genericPointDecomposition_of_hasNoEmbeddedPoints`. -/
theorem meromorphicSections_isQuasicoherent_of_noEmbeddedPoints (X : Scheme.{u})
    [IsLocallyNoetherian X] (hX : AlgebraicGeometry.HasNoEmbeddedPoints X) (F : X.Modules)
    (hF : F.IsQuasicoherent) :
    (meromorphicSections X F).IsQuasicoherent :=
  isQuasicoherent_meromorphicSections X F
    (MeromorphicQuasicoherent.meromorphicFunctions_isQuasicoherent_of_noEmbeddedPoints X hX) hF

/-! ### Faithfulness to the reference statements

The reference statements' own expressions, transcribed. -/

/-- The reference sheaf of total quotient rings: the sheafification of the total-quotient
presheaf. -/
abbrev cardTotalQuotientSheaf (X : Scheme.{u}) : TopCat.Sheaf CommRingCat.{u} X :=
  (presheafToSheaf (Opens.grothendieckTopology X) CommRingCat.{u}).obj
    X.presheaf.totalQuotientPresheaf

/-- The reference canonical morphism to the sheaf of total quotient rings. -/
abbrev cardToTotalQuotientSheaf (X : Scheme.{u}) : X.sheaf ⟶ cardTotalQuotientSheaf X :=
  ⟨X.presheaf.toTotalQuotientPresheaf ≫
    toSheafify (Opens.grothendieckTopology X) X.presheaf.totalQuotientPresheaf⟩

/-- The reference `RingCat`-valued form of the sheaf of total quotient rings. -/
abbrev cardRingSheaf (X : Scheme.{u}) : TopCat.Sheaf RingCat.{u} X :=
  (sheafCompose (Opens.grothendieckTopology X) (forget₂ CommRingCat RingCat.{u})).obj
    (cardTotalQuotientSheaf X)

/-- Sheafification of presheaves of modules over the reference sheaf of total quotient rings. -/
abbrev cardSheafify (X : Scheme.{u}) :
    PresheafOfModules.{u} (cardRingSheaf X).obj ⥤ SheafOfModules.{u} (cardRingSheaf X) :=
  PresheafOfModules.sheafification (𝟙 (cardRingSheaf X).obj)

/-- The reference sheaf of meromorphic sections: extension of scalars along the canonical morphism,
which is the sectionwise tensor product of Tag 03CU followed by sheafification. -/
abbrev cardMeromorphicSectionSheaf (X : Scheme.{u}) (F : X.Modules) :
    SheafOfModules.{u} (cardRingSheaf X) :=
  (SheafOfModules.forget
        ((sheafCompose (Opens.grothendieckTopology X)
          (forget₂ CommRingCat RingCat.{u})).obj X.sheaf) ⋙
      Stacks.PresheafOfModules.ChangeOfRings.changeOfRings (cardToTotalQuotientSheaf X).hom ⋙
      cardSheafify X).obj F

/-- The reference sheaf of meromorphic sections, read back as an `𝒪_X`-module by restriction of
scalars. -/
abbrev cardMeromorphicSections (X : Scheme.{u}) (F : X.Modules) : X.Modules :=
  (SheafOfModules.restrictScalars
      ((sheafCompose (Opens.grothendieckTopology X)
        (forget₂ CommRingCat RingCat.{u})).map (cardToTotalQuotientSheaf X))).obj
    (cardMeromorphicSectionSheaf X F)

/-- Stacks Tag 02OW, label `part (2), quasi-coherence`, in the reference binder order and with
every reference constant replaced by its own defining expression. -/
example (X : Scheme.{u}) [IsReduced X]
    (hfinite : ∀ U : X.Opens, IsCompact (U : Set X) → (irreducibleComponents U).Finite)
    (F : X.Modules) [F.IsQuasicoherent] :
    (cardMeromorphicSections X F).IsQuasicoherent :=
  meromorphicSections_isQuasicoherent X hfinite F

/-- The quasi-coherence clause of Stacks Tag 0EMH as stated above, in the reference binder
order and with every reference constant replaced by its own defining expression. -/
example (X : Scheme.{u}) [IsLocallyNoetherian X]
    (hX : ∀ x : X, ¬ (Stacks.Divisors.IsAssociatedPoint
        (SheafOfModules.unit X.ringCatSheaf) x ∧
      ∃ x' : X, Stacks.Divisors.IsAssociatedPoint
        (SheafOfModules.unit X.ringCatSheaf) x' ∧ x' ⤳ x ∧ x' ≠ x))
    (F : X.Modules) (hF : F.IsQuasicoherent) :
    (cardMeromorphicSections X F).IsQuasicoherent :=
  meromorphicSections_isQuasicoherent_of_noEmbeddedPoints X hX F hF

/-- The reference absence-of-embedded-points hypothesis, inlined, is the library's predicate. -/
example (X : Scheme.{u}) :
    (∀ x : X, ¬ (Stacks.Divisors.IsAssociatedPoint
        (SheafOfModules.unit X.ringCatSheaf) x ∧
      ∃ x' : X, Stacks.Divisors.IsAssociatedPoint
        (SheafOfModules.unit X.ringCatSheaf) x' ∧ x' ⤳ x ∧ x' ≠ x)) ↔
      AlgebraicGeometry.HasNoEmbeddedPoints X := Iff.rfl

end Stacks.AlgebraicGeometry.MeromorphicSectionsTensor

end
