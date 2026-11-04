module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedEtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceCorrespondence
public import StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedQuasiFinite

/-!
# The remaining characterisations of an unramified monomorphism of algebraic spaces

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S`. [Stacks Project, Tag 05W6]
lists four equivalent conditions on `f`:

1. `f` is unramified and a monomorphism,
2. `f` is unramified and universally injective,
3. `f` is locally of finite type and a monomorphism,
4. `f` is universally injective, locally of finite type and formally unramified,

and asserts that such an `f` is moreover representable, separated and locally quasi-finite.

`StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedMonomorphism` proves the equivalence of
conditions (1) and (3) and the implications from condition (1) to conditions (2) and (4). This
file adds the implication from condition (2) to condition (3) of
[Stacks Project, Tag 040X], the two clauses of the "moreover" part which are available —
separatedness and local quasi-finiteness — and the two equivalences (1) ⟺ (2) and (1) ⟺ (4),
both unconditional.  Only the representability clause is still modulo a named hypothesis.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.Space.isSurjective_diagonal_of_universallyInjective` is the implication
  (2) ⇒ (3) of [Stacks Project, Tag 040X]: a universally injective morphism of algebraic spaces
  has surjective relative diagonal.
* `AlgebraicGeometry.Space.universallyInjective_of_isSurjective_diagonal` is the converse
  implication (3) ⇒ (2) of [Stacks Project, Tag 040X], and
  `AlgebraicGeometry.Space.universallyInjective_iff_isSurjective_diagonal` is the resulting
  equivalence of conditions (2) and (3).
* `AlgebraicGeometry.Space.mono_of_isOpenImmersion_diagonal_of_universallyInjective`: a
  universally injective morphism whose relative diagonal is an open immersion is a
  monomorphism. This is the step (2) ⇒ (1) of [Stacks Project, Tag 05W6], with the
  open-immersion input left as a hypothesis.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isUnramified` is the global assertion of
  [Stacks Project, Tag 05W0]: an unramified morphism of algebraic spaces is locally
  quasi-finite.
* `AlgebraicGeometry.Space.isSeparated_isLocallyQuasiFinite_of_isLocallyOfFiniteType_mono` is
  [Stacks Project, Tag 0463], and is the separatedness and local quasi-finiteness part of the
  "moreover" clause of [Stacks Project, Tag 05W6].
* `AlgebraicGeometry.Space.isUnramified_mono_iff_isUnramified_universallyInjective` is the
  equivalence of conditions (1) and (2), and, in the same namespace,
  `isUnramified_mono_iff_universallyInjective_locallyOfFiniteType_formallyUnramified` is the
  equivalence of conditions (1) and (4).
* `AlgebraicGeometry.Space.relativelyRepresentable_of_locallyOfFiniteType_mono` is the
  representability clause of the "moreover" part.

## Implementation notes

The source proves (3) ⇒ (4) ⇒ (2) ⇒ (1) ⇒ (3); the three implications other than (2) ⇒ (1) are
already available, so what is added here is (2) ⇒ (1) and the "moreover" clauses.

The step (2) ⇒ (1) is the composite of three facts. The first is the implication (2) ⇒ (3) of
[Stacks Project, Tag 040X], which is proved here and needs nothing beyond the definitions:
universal injectivity applied to the base change of `f` along `f` itself says that
`|X ×_Y X| → |X|` is injective, and the relative diagonal is a section of that first
projection, so a point of `X ×_Y X` and the image under the diagonal of its first projection
have the same first projection and are therefore equal. The second is
`AlgebraicGeometry.Space.presheafSurjective_of_isSurjective`, the direction of
[Stacks Project, Tag 03MD] which turns surjectivity on points of the representable diagonal into
surjectivity of each of its represented base changes. The third is
`AlgebraicGeometry.Space.isIso_of_presheaf_isOpenImmersion_of_presheafSurjective`: an open
immersion which is surjective after every represented base change is an isomorphism; and a
morphism of presheaves whose relative diagonal is an isomorphism is a monomorphism, which is
`CategoryTheory.Limits.pullback.isIso_diagonal_iff`.

The input that the relative diagonal of an unramified morphism is an open immersion is part (1)
of [Stacks Project, Tag 05W1], and is supplied by
`AlgebraicGeometry.Space.isOpenImmersion_diagonal_of_isUnramified` of
`StacksFrontier.AlgebraicGeometry.Spaces.UnramifiedDiagonal`, so the equivalence of conditions (1)
and (2) is unconditional and carries the tag. The comparison of
`AlgebraicGeometry.Space.FormallyUnramified` with formal unramifiedness on étale charts,
condition (1) implies condition (2) of [Stacks Project, Tag 04G8], is likewise available, as
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_formallyUnramified` of
`StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedEtaleCharts`, so the equivalence with
condition (4) is unconditional and carries the tag too. What is *not* available is
representability of a separated locally quasi-finite morphism, [Stacks Project, Tag 0418],
which is the hypothesis `h0418` of the representability clause; that statement alone carries no
`@[stacks 05W6]` attribute.

The separatedness clause is [Stacks Project, Tag 042N] and holds for a monomorphism with no
further hypothesis; it is `AlgebraicGeometry.Space.isSeparated_of_mono` of
`StacksFrontier.AlgebraicGeometry.Spaces.SeparatedQuasiFiniteEtaleDescent`, untagged there, which
is used here rather than restated. The local quasi-finiteness clause goes through
unramifiedness: `AlgebraicGeometry.Space.isUnramified_of_isLocallyOfFiniteType_of_mono`
makes a monomorphism which is locally of finite type unramified, and an unramified morphism of
schemes is locally quasi-finite by
`AlgebraicGeometry.Unramified.locallyQuasiFinite_of_unramified`, so the two conditions, both
being tested on étale charts, pass into one another chart by chart. Together the two clauses are
[Stacks Project, Tag 0463].

## References

* [Stacks Project, Tag 03MD](https://stacks.math.columbia.edu/tag/03MD)
* [Stacks Project, Tag 040X](https://stacks.math.columbia.edu/tag/040X)
* [Stacks Project, Tag 0418](https://stacks.math.columbia.edu/tag/0418)
* [Stacks Project, Tag 042N](https://stacks.math.columbia.edu/tag/042N)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 04G8](https://stacks.math.columbia.edu/tag/04G8)
* [Stacks Project, Tag 04GA](https://stacks.math.columbia.edu/tag/04GA)
* [Stacks Project, Tag 05W0](https://stacks.math.columbia.edu/tag/05W0)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 05W6](https://stacks.math.columbia.edu/tag/05W6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
  {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-! ### The diagonal of a universally injective morphism is surjective -/

/-- **Stacks 040X, condition (2) implies condition (3).** The relative diagonal of a universally
injective morphism of algebraic spaces over `S` is surjective on points.

Universal injectivity applied to the base change of `f` along `f` itself says that the first
projection `|X ×_Y X| → |X|` is injective. The relative diagonal is a section of that
projection, so for a point `z` of `X ×_Y X` the point `x` it projects to has
`Δ(x)` and `z` with the same first projection, whence `Δ(x) = z`. -/
theorem isSurjective_diagonal_of_universallyInjective (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ Y) (hf : UniversallyInjective B S hS f) :
    IsSurjective B S hS (pullback.diagonal f) := by
  intro z
  refine ⟨pointsMap B S hS (pullback f f) (pullback.fst f f) z, hf X hX f ?_⟩
  rw [← pointsMap_comp_apply, pullback.diagonal_fst, pointsMap_id, id_eq]

/-! ### A morphism with surjective diagonal is universally injective -/

/-- A section of a fibre product of presheaves on the big fppf site of `S` over an object of
the site is the same thing as a pair of sections of the two factors with the same image in the
base. -/
private theorem exists_pullback_section {Z F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (g : Z ⟶ G) (f : F ⟶ G) {T : BigFppfOver B S hS}
    (x : Z.obj (Opposite.op T)) (y : F.obj (Opposite.op T))
    (h : g.app (Opposite.op T) x = f.app (Opposite.op T) y) :
    ∃ z : (pullback g f).obj (Opposite.op T),
      (pullback.fst g f).app (Opposite.op T) z = x ∧
        (pullback.snd g f).app (Opposite.op T) z = y := by
  refine ⟨yonedaEquiv (pullback.lift (yonedaEquiv.symm x) (yonedaEquiv.symm y) ?_), ?_, ?_⟩
  · rw [yonedaEquiv_symm_naturality_right, yonedaEquiv_symm_naturality_right, h]
  · rw [← yonedaEquiv_comp, pullback.lift_fst, Equiv.apply_symm_apply]
  · rw [← yonedaEquiv_comp, pullback.lift_snd, Equiv.apply_symm_apply]

/-- **Stacks 040X, condition (3) implies condition (2).** A morphism of algebraic spaces over
`S` whose relative diagonal is surjective on points is universally injective.

Two sections over a field spectrum with the same image assemble into a section of `X ×_Y X`;
surjectivity of the diagonal makes its class the class of a point of `X`, so over a common
field-valued extension that section is a restriction of the diagonal, where the two projections
agree. -/
theorem universallyInjective_of_isSurjective_diagonal (f : X ⟶ Y)
    (hf : IsSurjective B S hS (pullback.diagonal f)) :
    UniversallyInjective B S hS f := by
  refine universallyInjective_of_fieldPoints B S hS f fun p y hy ↦ ?_
  obtain ⟨z, hz₁, hz₂⟩ := exists_pullback_section B S hS f f p.value y hy
  obtain ⟨t, ht⟩ := hf (FieldValuedPoint.class B S hS (pullback f f) { p with value := z })
  obtain ⟨t₀, rfl⟩ := Quot.exists_rep t
  obtain ⟨w, ⟨δ, hδ⟩, ⟨ε, hε⟩⟩ :=
    (FieldValuedPoint.class_eq_class_iff B S hS (pullback f f) _ _).mp ht
  have hε' : (pullback f f).map ε.op z = w.value := hε
  have hproj : ∀ π : pullback f f ⟶ X, pullback.diagonal f ≫ π = 𝟙 X →
      π.app (Opposite.op w.siteObject) w.value = X.map δ.op t₀.value := fun π hπ ↦ by
    rw [← hδ, NatTrans.naturality_apply]
    exact congrArg (X.map δ.op)
      (congrArg (fun η : X ⟶ X ↦ η.app (Opposite.op t₀.siteObject) t₀.value) hπ)
  have hkey : X.map ε.op p.value = X.map ε.op y :=
    calc X.map ε.op p.value
        = (pullback.fst f f).app (Opposite.op w.siteObject)
            ((pullback f f).map ε.op z) := by
          rw [NatTrans.naturality_apply]
          exact congrArg (fun v ↦ X.map ε.op v) hz₁.symm
      _ = (pullback.snd f f).app (Opposite.op w.siteObject)
            ((pullback f f).map ε.op z) := by
          rw [hε', hproj _ (pullback.diagonal_fst f), hproj _ (pullback.diagonal_snd f)]
      _ = X.map ε.op y := by
          rw [NatTrans.naturality_apply]
          exact congrArg (fun v ↦ X.map ε.op v) hz₂
  exact ⟨{ w with value := X.map ε.op p.value }, ε, rfl, hkey.symm⟩

/-- **Stacks 040X, conditions (2) and (3).** A morphism of algebraic spaces over `S` is
universally injective if and only if its relative diagonal is surjective on points. -/
theorem universallyInjective_iff_isSurjective_diagonal (hX : IsAlgebraicSpace B S hS X)
    (f : X ⟶ Y) :
    UniversallyInjective B S hS f ↔ IsSurjective B S hS (pullback.diagonal f) :=
  ⟨isSurjective_diagonal_of_universallyInjective B S hS hX f,
    universallyInjective_of_isSurjective_diagonal B S hS f⟩

/-! ### A universally injective morphism with open diagonal is a monomorphism -/

/-- **A universally injective morphism of algebraic spaces over `S` whose relative diagonal is
an open immersion is a monomorphism.** The diagonal is surjective on points by
[Stacks Project, Tag 040X], hence surjective after every represented base change by
[Stacks Project, Tag 03MD], hence an isomorphism because it is an open immersion; and a
morphism of presheaves with invertible relative diagonal is a monomorphism.

This is the step (2) ⇒ (1) of [Stacks Project, Tag 05W6] with its one geometric input, part (1)
of [Stacks Project, Tag 05W1], left as the hypothesis `hoi`. -/
theorem mono_of_isOpenImmersion_diagonal_of_universallyInjective
    (hX : IsAlgebraicSpace B S hS X) (f : X ⟶ Y)
    (hoi : IsOpenImmersion B S hS (pullback.diagonal f))
    (hf : UniversallyInjective B S hS f) :
    Mono f := by
  have hsurj := presheafSurjective_of_isSurjective B S hS (pullback.diagonal f) hoi.rep
    (isSurjective_diagonal_of_universallyInjective B S hS hX f hf)
  have hiso : IsIso (pullback.diagonal f) :=
    isIso_of_presheaf_isOpenImmersion_of_presheafSurjective B S hS _ hoi hsurj
  exact (pullback.isIso_diagonal_iff f).mp hiso

/-! ### An unramified morphism is locally quasi-finite -/

/-- **Stacks 0463.** A monomorphism of algebraic spaces over `S` which is locally of finite type
is separated and locally quasi-finite.

Separatedness is [Stacks Project, Tag 042N], already available as
`AlgebraicGeometry.Space.isSeparated_of_mono`; local quasi-finiteness goes through
unramifiedness, which a monomorphism locally of finite type has by
`AlgebraicGeometry.Space.isUnramified_of_isLocallyOfFiniteType_of_mono`.

These are two of the three assertions of the "moreover" clause of
[Stacks Project, Tag 05W6], reached from its condition (3); the equivalence of conditions (1)
and (3) carries them over to condition (1), and the two unconditional equivalences below carry
them over to conditions (2) and (4). -/
@[stacks 0463, stacks 05W6 "separated and locally quasi-finite, from condition (3)"]
theorem isSeparated_isLocallyQuasiFinite_of_isLocallyOfFiniteType_mono (f : X ⟶ Y)
    (h : IsLocallyOfFiniteType B S hS f ∧ Mono f) :
    IsSeparated B S hS f ∧ IsLocallyQuasiFinite B S hS f :=
  ⟨isSeparated_of_mono f h.2,
    isLocallyQuasiFinite_of_isUnramified B S hS _
      (isUnramified_of_isLocallyOfFiniteType_of_mono B S hS f h.1 h.2)⟩

/-! ### The equivalences with conditions (2) and (4) -/

/-- **Stacks 05W6, conditions (1) and (2).** A morphism of algebraic spaces over `S` is
unramified and a monomorphism if and only if it is unramified and universally injective.

The forward implication is
`AlgebraicGeometry.Space.isUnramified_universallyInjective_of_isUnramified_mono`. The converse
is `AlgebraicGeometry.Space.mono_of_isOpenImmersion_diagonal_of_universallyInjective`, whose
open-immersion input is part (1) of [Stacks Project, Tag 05W1], specialised to `f`; that is
`AlgebraicGeometry.Space.isOpenImmersion_diagonal_of_isUnramified`. -/
@[stacks 05W6 "conditions (1) and (2)", ega "IV 17.2.6" "(b) => (a)"]
theorem isUnramified_mono_iff_isUnramified_universallyInjective
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (IsUnramified B S hS f ∧ Mono f) ↔
      (IsUnramified B S hS f ∧ UniversallyInjective B S hS f) :=
  ⟨fun h => isUnramified_universallyInjective_of_isUnramified_mono B S hS hX hY f h,
    fun ⟨hu, hui⟩ =>
      ⟨hu, mono_of_isOpenImmersion_diagonal_of_universallyInjective B S hS hX f
        (isOpenImmersion_diagonal_of_isUnramified B S hS hX hY f hu) hui⟩⟩

/-- **Stacks 05W6, conditions (1) and (4).** A morphism of algebraic spaces over `S` is
unramified and a monomorphism if and only if it is universally injective, locally of finite
type and formally unramified.

The forward implication is, in this namespace,
`universallyInjective_isLocallyOfFiniteType_formallyUnramified_of_isUnramified_mono`.
For the converse, local finite type together with formal unramifiedness on étale charts is
unramifiedness, which is the available half of [Stacks Project, Tag 04GA]; passing from
`AlgebraicGeometry.Space.FormallyUnramified` to the chart condition is condition (1) implies
condition (2) of [Stacks Project, Tag 04G8], supplied by
`AlgebraicGeometry.Space.holdsOnEveryEtaleChart_of_formallyUnramified` of
`StacksFrontier.AlgebraicGeometry.Spaces.FormallyUnramifiedEtaleCharts`. The monomorphism is then
obtained as in
`AlgebraicGeometry.Space.isUnramified_mono_iff_isUnramified_universallyInjective`, from part (1)
of [Stacks Project, Tag 05W1]. Both inputs being available, this equivalence is unconditional
and carries the tag. -/
@[stacks 05W6 "conditions (1) and (4)"]
theorem isUnramified_mono_iff_universallyInjective_locallyOfFiniteType_formallyUnramified
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    (IsUnramified B S hS f ∧ Mono f) ↔
      (UniversallyInjective B S hS f ∧ IsLocallyOfFiniteType B S hS f ∧
        FormallyUnramified (B := B) (S := S) (hS := hS) f) := by
  refine ⟨fun h =>
    universallyInjective_isLocallyOfFiniteType_formallyUnramified_of_isUnramified_mono
      B S hS hX hY f h, fun ⟨hui, hft, hfu⟩ => ?_⟩
  have hu : IsUnramified B S hS f :=
    (isUnramified_iff_isLocallyOfFiniteType_and_formallyUnramifiedCharts B S hS f).mpr
      ⟨hft, holdsOnEveryEtaleChart_of_formallyUnramified B S hS f hfu⟩
  exact ⟨hu, mono_of_isOpenImmersion_diagonal_of_universallyInjective B S hS hX f
    (isOpenImmersion_diagonal_of_isUnramified B S hS hX hY f hu) hui⟩

/-! ### The representability clause -/

/-- **Stacks 05W6, the representability clause, granted Stacks 0418.** A monomorphism of
algebraic spaces over `S` which is locally of finite type is representable.

By [Stacks Project, Tag 0463] such a morphism is separated and locally quasi-finite, and a
separated locally quasi-finite morphism of algebraic spaces is representable by
[Stacks Project, Tag 0418], which is the hypothesis `h0418`. That tag rests on
[Stacks Project, Tag 03XX], which is not available in this development, so this statement
carries no `@[stacks]` attribute. -/
theorem relativelyRepresentable_of_locallyOfFiniteType_mono
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (h : IsLocallyOfFiniteType B S hS f ∧ Mono f)
    (h0418 : ∀ {X' Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}, IsAlgebraicSpace B S hS X' →
      IsAlgebraicSpace B S hS Y' → ∀ g : X' ⟶ Y', IsLocallyQuasiFinite B S hS g →
      IsSeparated B S hS g → yoneda.relativelyRepresentable g) :
    yoneda.relativelyRepresentable f :=
  have hsep := isSeparated_isLocallyQuasiFinite_of_isLocallyOfFiniteType_mono B S hS f h
  h0418 hX hY f hsep.2 hsep.1

end AlgebraicGeometry.Space

end
