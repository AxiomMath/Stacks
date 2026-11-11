module

public import Mathlib.AlgebraicGeometry.Morphisms.Proper
import StacksCore.Tactic.StacksAttribute

/-!
# Composition of proper morphisms, and properness of closed immersions

Properness and universal closedness of morphisms of schemes are stable under composition
(`AlgebraicGeometry.IsProper.stableUnderComposition` and
`AlgebraicGeometry.universallyClosed_isStableUnderComposition`). A closed immersion is
universally closed, and is moreover proper, being finite.

In a commutative triangle `X ⟶ Y ⟶ S` whose right leg is separated, universal closedness and
properness descend from the long side `X ⟶ S` to the short side `X ⟶ Y`, and the image of `X`
in `Y` is then closed.

In a commutative triangle `X ⟶ Y ⟶ S` whose left leg is *surjective*, universal closedness
travels the other way, from the long side `X ⟶ S` to the right leg `Y ⟶ S`; properness does too
as soon as `Y ⟶ S` is separated and locally of finite type. This is the scheme-level form of the
statement that the image of a proper scheme is proper.

## Main results

* `AlgebraicGeometry.isProper_of_isClosedImmersion`: a closed immersion of schemes is proper.
* `AlgebraicGeometry.universallyClosed_of_universallyClosed_of_isSeparated` and
  `AlgebraicGeometry.isProper_of_isProper_of_isSeparated`: universal closedness and properness
  over a separated base descend to the morphism into that base.
* `AlgebraicGeometry.isClosed_range_of_universallyClosed_of_isSeparated`: in that situation the
  image is closed.
* `AlgebraicGeometry.isProper_iff_exists_iSup_eq_top`: properness is local on the base, in the
  form of an equivalence with properness over the members of some open covering of the base.
* `AlgebraicGeometry.universallyClosed_of_universallyClosed_of_surjective` and
  `AlgebraicGeometry.isProper_of_isProper_of_surjective`: the image of a universally closed,
  respectively proper, scheme under a surjection is universally closed, respectively proper.
  The properness clause of Stacks 03GN, assuming universal closedness of the source, is
  `AlgebraicGeometry.isProper_of_comp_surjective`.

## References

* [Stacks Project, Tag 01W2](https://stacks.math.columbia.edu/tag/01W2)
* [Stacks Project, Tag 01W3](https://stacks.math.columbia.edu/tag/01W3)
* [Stacks Project, Tag 01W5](https://stacks.math.columbia.edu/tag/01W5)
* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 03GN](https://stacks.math.columbia.edu/tag/03GN)
-/

@[expose] public section

universe u

namespace AlgebraicGeometry

/-- A closed immersion of schemes is proper: it is a finite morphism, and a finite morphism is
separated, universally closed and locally of finite type. -/
@[stacks 01W5 "proper", ega "II 5.4.2", ega "II 5.4.9" "5.4.2(i)"]
lemma isProper_of_isClosedImmersion {X Y : Scheme.{u}} (f : X ⟶ Y) [IsClosedImmersion f] :
    IsProper f :=
  inferInstance

/-- **[Stacks, Tag 01W2].** A morphism of schemes `f : X ⟶ S` is proper if and only if there is
an open covering `S = ⋃ V j` such that every restriction `f⁻¹(V j) ⟶ V j` is proper. The index
type of the covering may live in any universe. -/
@[stacks 01W2]
theorem isProper_iff_exists_iSup_eq_top {X S : Scheme.{u}} (f : X ⟶ S) :
    IsProper f ↔ ∃ (ι : Type*) (V : ι → S.Opens), iSup V = ⊤ ∧ ∀ j, IsProper (f ∣_ V j) := by
  refine ⟨fun _ ↦ ⟨PUnit, fun _ ↦ ⊤, iSup_const, fun _ ↦ inferInstance⟩, ?_⟩
  rintro ⟨ι, V, hV, H⟩
  exact IsZariskiLocalAtTarget.of_iSup_eq_top (P := @IsProper) V hV H

section SeparatedTarget

open CategoryTheory

variable {X Y S : Scheme.{u}} (g : X ⟶ Y) (q : Y ⟶ S) (p : X ⟶ S)

/-- **[Stacks, Tag 01W6] part (1).** Let `X ⟶ Y ⟶ S` be a commutative triangle with `Y`
separated over `S`. If `X ⟶ S` is universally closed, then so is `X ⟶ Y`. -/
@[stacks 01W6 "(1), in the triangle form of the source"]
lemma universallyClosed_of_universallyClosed_of_isSeparated (h : g ≫ q = p) [IsSeparated q]
    [UniversallyClosed p] : UniversallyClosed g := by
  subst h
  exact UniversallyClosed.of_comp_of_isSeparated g q

/-- **[Stacks, Tag 01W6] part (2).** Let `X ⟶ Y ⟶ S` be a commutative triangle with `Y`
separated over `S`. If `X` is proper over `S`, then `X ⟶ Y` is proper. -/
@[stacks 01W6 "(2), in the triangle form of the source"]
lemma isProper_of_isProper_of_isSeparated (h : g ≫ q = p) [IsSeparated q] [IsProper p] :
    IsProper g := by
  subst h
  exact IsProper.of_comp g q

/-- **The final clause of [Stacks, Tag 01W6].** In a commutative triangle `X ⟶ Y ⟶ S` with `Y`
separated over `S` and `X` universally closed over `S`, the image of `X` in `Y` is closed: the
morphism `X ⟶ Y` is universally closed, hence a closed map, and its image is the image of the
whole space. -/
@[stacks 01W6 "the final clause: the image of X in Y is closed"]
lemma isClosed_range_of_universallyClosed_of_isSeparated (h : g ≫ q = p) [IsSeparated q]
    [UniversallyClosed p] : IsClosed (Set.range g.base) :=
  have : UniversallyClosed g :=
    universallyClosed_of_universallyClosed_of_isSeparated g q p h
  Set.image_univ ▸ g.isClosedMap _ isClosed_univ

end SeparatedTarget

section SurjectiveSource

open CategoryTheory

variable {X Y S : Scheme.{u}} (g : X ⟶ Y) (q : Y ⟶ S) (p : X ⟶ S)

/-- **[Stacks, Tag 03GN], the universally closed half.** Let `X ⟶ Y ⟶ S` be a commutative
triangle with `X ⟶ Y` surjective. If `X ⟶ S` is universally closed, then so is `Y ⟶ S`: a map is
closed as soon as its precomposition with a continuous surjection is, and surjectivity is stable
under base change. -/
@[stacks 03GN "the universally closed half, in the triangle form of the source"]
lemma universallyClosed_of_universallyClosed_of_surjective (h : g ≫ q = p) [Surjective g]
    [UniversallyClosed p] : UniversallyClosed q := by
  subst h
  exact UniversallyClosed.of_comp_surjective g q

/-- The image of a proper scheme is proper: in a commutative triangle `X ⟶ Y ⟶ S` with
`X ⟶ Y` surjective and `X` proper over `S`, the morphism `Y ⟶ S` is proper as soon as it is
separated and locally of finite type.

This is a special case of the properness clause of [Stacks, Tag 03GN], which assumes `X`
universally closed over `S` rather than proper; that clause, under exactly the source's
hypotheses, is `AlgebraicGeometry.isProper_of_comp_surjective`. -/
@[ega "II 5.4.3" "more general"]
lemma isProper_of_isProper_of_surjective (h : g ≫ q = p) [Surjective g] [IsProper p]
    [IsSeparated q] [LocallyOfFiniteType q] : IsProper q :=
  (isProper_iff q).2
    ⟨‹IsSeparated q›, universallyClosed_of_universallyClosed_of_surjective g q p h,
      ‹LocallyOfFiniteType q›⟩

end SurjectiveSource

end AlgebraicGeometry

add_to_stacks 01W3 "the composition of proper morphisms is proper"
  AlgebraicGeometry.IsProper.stableUnderComposition
add_to_ega "II 5.4.2" AlgebraicGeometry.IsProper.stableUnderComposition
add_to_stacks 01W3 "the composition of universally closed morphisms is universally closed"
  AlgebraicGeometry.universallyClosed_isStableUnderComposition
add_to_ega "II 5.4.9" "5.4.2(ii)" AlgebraicGeometry.universallyClosed_isStableUnderComposition
add_to_ega "IV 2.4.3" "(ii)" AlgebraicGeometry.universallyClosed_isStableUnderComposition
add_to_stacks 01W5 "a closed immersion is universally closed"
  AlgebraicGeometry.instUniversallyClosedOfIsClosedImmersion
add_to_ega "II 5.4.9" "5.4.2(i)" AlgebraicGeometry.instUniversallyClosedOfIsClosedImmersion
add_to_ega "II 6.1.10" "closed immersions"
  AlgebraicGeometry.instUniversallyClosedOfIsClosedImmersion
add_to_ega "IV 2.4.3" AlgebraicGeometry.instUniversallyClosedOfIsClosedImmersion
