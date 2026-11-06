module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent
public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.ReducedSingleton
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange

/-!
# Residual spaces that are spectra of fields

A residual space of an algebraic space `X` over `S` at a point `x` of `|X|` is the spectrum of
a field exactly when `x` is represented by a monomorphism from the spectrum of a field, which
is condition (4) of Stacks 03JV. A decent algebraic space has such a representative at every
point, so every residual space of a decent algebraic space is the spectrum of a field.

## Main definitions

No new definitions are introduced.

## Main results

* `AlgebraicGeometry.Space.exists_isIso_fieldMorphism_iff_hasMonomorphicFieldRepresentative` is
  the equivalence of Stacks 0H1R at a point: a residual space of `X` at `x` is the spectrum of
  a field if and only if `x` has a monomorphic field-valued representative.
* `AlgebraicGeometry.Space.exists_isIso_fieldMorphism_of_isDecentSpace` is the second assertion
  of Stacks 0H1R: for a decent algebraic space this holds at every point.
* `AlgebraicGeometry.Space.exists_iso_yoneda_of_isIso_fieldMorphism` reads the conclusion as an
  isomorphism of `Z` with the functor of points of an object of the site whose underlying
  scheme is the spectrum of a field.

## Implementation notes

"`Z` is the spectrum of a field" is expressed as the existence of a field-valued point of `Z`
of Stacks 03BU whose morphism `yoneda.obj (Spec k over S) ⟶ Z` is an isomorphism; this is the
same shape as the rendering of "`x` is represented by a monomorphism from the spectrum of a
field" by `AlgebraicGeometry.Space.HasMonomorphicFieldRepresentative`, where that morphism is
asked to be a monomorphism instead.
`AlgebraicGeometry.Space.exists_iso_yoneda_of_isIso_fieldMorphism` spells the conclusion out as
an isomorphism with a represented presheaf whose representing object has the spectrum of a
field as its underlying scheme.

Stacks 06QZ — the existence and uniqueness of the residual space at a point — is not available
here, so the residual space is not a chosen subobject: as in
`AlgebraicGeometry.Space.isClosed_singleton_iff_isClosedImmersion_of_isResidualSpaceAt`, it is
an arbitrary monomorphism `f : Z ⟶ X` satisfying the predicate
`AlgebraicGeometry.Space.IsResidualSpaceAt` of Stacks 06R0. Both statements below therefore
quantify over such an `f`, and no uniqueness is used: the hard implication does not compare
`Z` with a chosen residual space but produces the isomorphism directly, from Stacks 06MG and
Stacks 06QY.

That implication runs as follows. If `g : yoneda.obj (Spec k over S) ⟶ X` is a monomorphism
representing `x`, then the fibre product `Z ×_X Spec k` has a point by Stacks 03H4, because the
only point of `|Z|` and the point of the field spectrum both map to `x`; its projection to the
field spectrum is a monomorphism, hence an isomorphism by Stacks 06MG. The resulting
monomorphism `Spec k ⟶ Z` has nonempty source, and `Z` is reduced, locally Noetherian with one
point, so it carries a flat, surjective, locally finitely presented cover by a field spectrum
by Stacks 06QX; Stacks 06QY then makes that monomorphism an isomorphism. The other implication
only composes an isomorphism with the monomorphism `f`.

## References

* [Stacks Project, Tag 0H1R](https://stacks.math.columbia.edu/tag/0H1R)
* [Stacks Project, Tag 03H4](https://stacks.math.columbia.edu/tag/03H4)
* [Stacks Project, Tag 06MG](https://stacks.math.columbia.edu/tag/06MG)
* [Stacks Project, Tag 06QX](https://stacks.math.columbia.edu/tag/06QX)
* [Stacks Project, Tag 06QY](https://stacks.math.columbia.edu/tag/06QY)
* [Stacks Project, Tag 06R0](https://stacks.math.columbia.edu/tag/06R0)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- A field-valued point of `Z` whose presenting morphism is an isomorphism exhibits `Z` as the
functor of points of an object of the site whose underlying scheme is the spectrum of a
field. -/
theorem exists_iso_yoneda_of_isIso_fieldMorphism (q : FieldValuedPoint B S hS Z)
    (hq : IsIso (fieldMorphism B S hS Z q)) :
    ∃ (T : BigFppfOver B S hS) (k : Type u) (_ : Field k),
      (BigFppfOver.toScheme B S hS).obj T = Spec (.of k) ∧ Nonempty (yoneda.obj T ≅ Z) :=
  ⟨q.siteObject B S hS Z, q.carrier, q.field, rfl, ⟨asIso (fieldMorphism B S hS Z q)⟩⟩

/-- **Stacks 0H1R**, the equivalence at a point. Let `X` be an algebraic space over `S`, let `x`
be a point of `|X|` and let `f : Z ⟶ X` be a residual space of `X` at `x`. Then `Z` is the
spectrum of a field if and only if `x` can be represented by a monomorphism from the spectrum
of a field.

For the easy implication, the presenting morphism of a field-valued point of `Z` which is an
isomorphism, composed with the monomorphism `f`, is a monomorphism representing `x`, since the
only point of `|Z|` maps to `x`.

Conversely, let `g : yoneda.obj (Spec k over S) ⟶ X` be a monomorphism representing `x`. The
only point of `|Z|` and the point of the field spectrum both map to `x`, so the fibre product
`Z ×_X Spec k` has a point by Stacks 03H4; its projection to the field spectrum is a
monomorphism, hence an isomorphism by Stacks 06MG. That produces a monomorphism
`Spec k ⟶ Z` with nonempty source, and `Z`, being reduced and locally Noetherian with exactly
one point, has a flat, surjective, locally finitely presented cover by the spectrum of a field
by Stacks 06QX, so the monomorphism is an isomorphism by Stacks 06QY. -/
@[stacks 0H1R "the equivalence at a point"]
theorem exists_isIso_fieldMorphism_iff_hasMonomorphicFieldRepresentative
    (hX : IsAlgebraicSpace B S hS X) (x : points B S hS X) (f : Z ⟶ X)
    (hf : IsResidualSpaceAt B S hS X x f) :
    (∃ q : FieldValuedPoint B S hS Z, IsIso (fieldMorphism B S hS Z q)) ↔
      HasMonomorphicFieldRepresentative B S hS X x := by
  obtain ⟨hZ, hmono, hred, hln, hne, hsub, hsupp⟩ := hf
  obtain ⟨z₀⟩ := hne
  constructor
  · rintro ⟨q, hq⟩
    refine ⟨FieldValuedPoint.map B S hS Z f q, ?_, ?_⟩
    · rw [← pointsMap_class]
      exact hsupp (q.class B S hS Z)
    · rw [fieldMorphism_map]
      exact @mono_comp _ _ _ _ _ _ (@IsIso.mono_of_iso _ _ _ _ _ hq) f hmono
  · rintro ⟨p, hpx, hpmono⟩
    have hTalg : IsAlgebraicSpace B S hS (yoneda.obj (p.siteObject B S hS X)) :=
      isAlgebraicSpace_yoneda B S hS _
    -- The tautological point of the field spectrum maps to `x`.
    have ht := (pointsMap_fieldMorphism_tautologicalPoint B S hS X p).trans hpx
    -- Hence the fibre product `Z ×_X Spec k` has a point.
    obtain ⟨w, -, -⟩ := exists_points_of_isPullback B S hS
      (IsPullback.of_hasPullback f (fieldMorphism B S hS X p)) z₀ _ ((hsupp z₀).trans ht.symm)
    -- Its projection to the field spectrum is a monomorphism, hence an isomorphism.
    have : IsIso (Limits.pullback.snd f (fieldMorphism B S hS X p)) :=
      (isEmpty_points_or_isIso_of_mono_to_fieldSpectrum B S hS (p.siteObject B S hS X)
        (eqToIso rfl) (isAlgebraicSpace_pullback B S hS f (fieldMorphism B S hS X p) hZ hTalg hX)
        (Limits.pullback.snd f (fieldMorphism B S hS X p))).resolve_left
        fun hempty => hempty.false w
    -- The monomorphism it produces out of the field spectrum is an isomorphism, because `Z`
    -- carries a flat, surjective, locally finitely presented cover by a field spectrum.
    have hcover : HasLocallyOfFinitePresentationFlatFieldCover B S hS Z :=
      (isReduced_locallyNoetherian_singleton_iff_hasFinitePresentationCover B S hS Z hZ).mp
        ⟨hred, hln, ⟨z₀⟩, hsub⟩
    set g := inv (Limits.pullback.snd f (fieldMorphism B S hS X p)) ≫
      Limits.pullback.fst f (fieldMorphism B S hS X p)
    refine ⟨{ carrier := p.carrier
              field := p.field
              contained := p.contained
              toBase := p.toBase
              value := yonedaEquiv g }, ?_⟩
    show IsIso (yonedaEquiv.symm (yonedaEquiv _))
    rw [Equiv.symm_apply_apply]
    exact (isEmpty_points_or_isIso_of_mono_of_hasFinitePresentationCover B S hS hTalg hZ g
      hcover).resolve_left
      fun hempty => hempty.false ((p.tautologicalPoint B S hS X).class B S hS
        (yoneda.obj (p.siteObject B S hS X)))

/-- **Stacks 0H1R**, the assertion for a decent algebraic space: every residual space of a
decent algebraic space over `S` is the spectrum of a field.

A decent algebraic space has a monomorphic field-valued representative at every point, which is
condition (4) of Stacks 03JV, so the equivalence
`AlgebraicGeometry.Space.exists_isIso_fieldMorphism_iff_hasMonomorphicFieldRepresentative`
applies at every point. -/
@[stacks 0H1R "the assertion for a decent algebraic space"]
theorem exists_isIso_fieldMorphism_of_isDecentSpace (hX : IsAlgebraicSpace B S hS X)
    (hdecent : IsDecentSpace B S hS X) (x : points B S hS X) (f : Z ⟶ X)
    (hf : IsResidualSpaceAt B S hS X x f) :
    ∃ q : FieldValuedPoint B S hS Z, IsIso (fieldMorphism B S hS Z q) :=
  (exists_isIso_fieldMorphism_iff_hasMonomorphicFieldRepresentative B S hS hX x f hf).2
    (IsDecentSpace.hasMonomorphicFieldRepresentative B S hS X hdecent x)

end AlgebraicGeometry.Space

end
