module

public import Mathlib.Algebra.Field.Equiv
public import Mathlib.RingTheory.IntegralClosure.IsIntegralClosure.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatAffine.IntegralInvariants
public import StacksFrontier.AlgebraicGeometry.Groupoids.FiniteFlatQuotient.SubgroupoidDivisionDescent
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleFieldAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFieldCover

/-!
# Dividing a groupoid scheme whose object scheme is the spectrum of a field

Let `(U, R, s, t, c)` be a groupoid scheme over `S` whose scheme of objects is the spectrum of a
field `k`, and let `(U, P, s|_P, t|_P, c|_P)` be a subgroupoid on the same object scheme whose
pre-relation is a monomorphism and whose source and target maps are merely *finite*. Then the
hypotheses of **Stacks 04S4** are met, so the groupoid can be divided by `P`; and the quotient
`Ū` is the spectrum of a field.

Both improvements over the general statement come from the object scheme being the spectrum of a
field. Finite local freeness of `s|_P` and `t|_P` is automatic: a module over a field is flat,
and a field is Noetherian, so a finite morphism to the spectrum of a field is flat and locally
of finite presentation, which is **Stacks 02KB**. And the quotient morphism `U ⟶ Ū` is finite
locally free and surjective, hence faithfully flat, so `Γ(Ū)` is a subring of `Γ(U) = k` over
which `k` is integral — and such a subring is a field.

This is the step of the proof of **Stacks 06N0** (a DM, locally Noetherian, reduced algebraic
stack with a one-point space has a surjective étale cover by the spectrum of a field) which
produces the field: the groupoid there is the one of a flat presentation `Spec k ⟶ 𝒵`, the
subgroupoid `P` is the open-and-closed piece of `R` through the identity, and the field of the
conclusion is the field `k₀` of invariants, so that `Ū = Spec k₀`.

## Main results

* `AlgebraicGeometry.isFiniteLocallyFree_of_isFinite_of_isoSpecField`: a finite morphism whose
  target is isomorphic to the spectrum of a field is finite locally free.
* `AlgebraicGeometry.isField_sections_of_isFiniteLocallyFree_of_surjective`: the global functions
  on the target of a finite locally free surjection are a field as soon as the global functions
  on its source are.
* `AlgebraicGeometry.GroupoidScheme.isField_invariantRing`: **Stacks 03BM** — the invariant ring
  of an affine groupoid scheme with finite locally free source and target is a field when the
  ring of the object scheme is.
* `AlgebraicGeometry.GroupoidScheme.exists_division_isField_quotient_of_isoSpecField`:
  **Stacks 04S4** at an object scheme which is the spectrum of a field, with the quotient
  exhibited as the spectrum of a field.

## Implementation notes

That the object scheme is the spectrum of a field is expressed by an isomorphism
`G.objects.left ≅ Spec k`, as elsewhere for groupoid schemes on a field, rather than by an
equality; the subgroupoid's object scheme is then the spectrum of a field through the equality
of object schemes the subgroupoid carries.

The field-ness of the quotient is stated for the global functions of the quotient scheme rather
than as an isomorphism onto the spectrum of a named field. That is the shape in which it is
produced: `AlgebraicGeometry.GroupoidScheme.Division` records the quotient as an affine scheme,
not as the spectrum of the invariant ring, and the global functions of an affine scheme together
with `AlgebraicGeometry.Scheme.isoSpec` recover the spectrum presentation. The clause about the
invariant ring is stated separately, since that is the ring the source's proof names.

Injectivity of `Γ(Ū) ⟶ Γ(U)` is not available from surjectivity of `U ⟶ Ū` alone — a surjection
of affine schemes can have a non-reduced target — and comes from faithful flatness, which is
flatness together with surjectivity on spectra. That step is not redone here: it is
`AlgebraicGeometry.Space.exists_algebra_isField_of_isFinite_flat_surjective`, and
`AlgebraicGeometry.isField_sections_of_isFiniteLocallyFree_of_surjective` only moves it from
morphisms of spectra of rings to morphisms of affine schemes. For the invariant ring the
injectivity is instead free: the map is the inclusion of a subring.

## References

* [Stacks Project, Tag 02KB](https://stacks.math.columbia.edu/tag/02KB)
* [Stacks Project, Tag 03BJ](https://stacks.math.columbia.edu/tag/03BJ)
* [Stacks Project, Tag 03BM](https://stacks.math.columbia.edu/tag/03BM)
* [Stacks Project, Tag 04S4](https://stacks.math.columbia.edu/tag/04S4)
* [Stacks Project, Tag 06N0](https://stacks.math.columbia.edu/tag/06N0)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

open Stacks.Groupoids Stacks.Morphisms

/-! ### Global functions on a scheme isomorphic to the spectrum of a field -/

/-- The ring of global functions on a scheme presented with an isomorphism onto the spectrum of
a field is that field. -/
def sectionsRingEquivOfIsoSpecField {X : Scheme.{u}} (k : Type u) [Field k]
    (e : X ≅ Spec (.of k)) : Γ(X, ⊤) ≃+* k :=
  (Scheme.Γ.mapIso e.symm.op).commRingCatIsoToRingEquiv.trans
    (Scheme.ΓSpecIso (.of k)).commRingCatIsoToRingEquiv

/-- The global functions on a scheme isomorphic to the spectrum of a field are a field. -/
theorem isField_sections_of_isoSpecField {X : Scheme.{u}} (k : Type u) [Field k]
    (e : X ≅ Spec (.of k)) : IsField Γ(X, ⊤) :=
  MulEquiv.isField (Field.toIsField k) (sectionsRingEquivOfIsoSpecField k e).toMulEquiv

/-! ### Finite morphisms to the spectrum of a field -/

/-- **A finite morphism whose target is isomorphic to the spectrum of a field is finite locally
free.**  By **Stacks 02KB** it suffices to add flatness and local finite presentation to
finiteness: the local rings of the spectrum of a field are fields, so every morphism to it is
flat, and a field is Noetherian, so a morphism locally of finite type to it is locally of finite
presentation. -/
theorem isFiniteLocallyFree_of_isFinite_of_isoSpecField {X Y : Scheme.{u}} (k : Type u) [Field k]
    (e : Y ≅ Spec (.of k)) (f : X ⟶ Y) [IsFinite f] : IsFiniteLocallyFree f := by
  have hflat : Flat (f ≫ e.hom) :=
    flat_of_isField_stalk _ fun _ => isField_stalk_Spec_field k _
  have h : IsFiniteLocallyFree (f ≫ e.hom) :=
    (isFiniteLocallyFree_iff_isFinite_flat_locallyOfFinitePresentation _).mpr
      ⟨inferInstance, hflat, inferInstance⟩
  exact (MorphismProperty.cancel_right_of_respectsIso
    (P := @IsFiniteLocallyFree) f e.hom).mp h

/-! ### The global functions on the target of a finite locally free surjection -/

/-- **The global functions on the target of a finite locally free surjection onto an affine
scheme are a field as soon as the global functions on its source are.**  This is
`AlgebraicGeometry.Space.exists_algebra_isField_of_isFinite_flat_surjective` — a ring whose
spectrum receives a finite, flat, surjective morphism from the spectrum of a field is a field —
read for a morphism of affine schemes rather than for a morphism of spectra of rings: the source
is affine because a finite morphism is affine, and both schemes are replaced by the spectra of
their global functions. -/
theorem isField_sections_of_isFiniteLocallyFree_of_surjective {X Y : Scheme.{u}} (p : X ⟶ Y)
    [IsAffine Y] [IsFiniteLocallyFree p] [Surjective p] (h : IsField Γ(X, ⊤)) :
    IsField Γ(Y, ⊤) := by
  have : IsAffine X := isAffine_of_isAffineHom p
  let : Field Γ(X, ⊤) := h.toField
  have hcancel : ∀ P : MorphismProperty Scheme.{u}, P.IsStableUnderBaseChange → P p →
      P (X.isoSpec.inv ≫ p ≫ Y.isoSpec.hom) := fun P hPb hP =>
    have := hPb.respectsIso
    by rwa [P.cancel_left_of_respectsIso, P.cancel_right_of_respectsIso]
  obtain ⟨_, _, hF, _⟩ := Space.exists_algebra_isField_of_isFinite_flat_surjective
    (A := Γ(Y, ⊤)) Γ(X, ⊤) (X.isoSpec.inv ≫ p ≫ Y.isoSpec.hom)
    (hcancel _ inferInstance (IsFiniteLocallyFree.isFinite p))
    (hcancel _ inferInstance (IsFiniteLocallyFree.flat p))
    (hcancel _ inferInstance inferInstance)
  exact hF

namespace GroupoidScheme

/-! ### The invariant ring of a groupoid scheme on a field -/

/-- **Stacks Project, Tag 03BM.** The ring of invariant functions of an affine groupoid scheme
with finite locally free source and target is a field as soon as the ring of functions on the
object scheme is one.  The ring of functions on the object scheme is integral over the invariant
ring by **Stacks 03BJ**, and the invariant ring is a subring, so the extension is injective; an
injective integral extension of a field comes from a field. -/
@[stacks 03BM "the ring of invariants of a groupoid on the spectrum of a field is a field"]
theorem isField_invariantRing {S : Scheme.{u}} (G : GroupoidScheme S)
    [IsAffine G.objects.left] [IsAffine G.arrows.left]
    [IsFiniteLocallyFree G.source.left] [IsFiniteLocallyFree G.target.left]
    (h : IsField Γ(G.objects.left, ⊤)) : IsField (invariantRing G) := by
  let : Algebra (invariantRing G) Γ(G.objects.left, ⊤) :=
    (Subring.subtype (invariantRing G)).toAlgebra
  have : Algebra.IsIntegral (invariantRing G) Γ(G.objects.left, ⊤) :=
    algebraMap_isIntegral_iff.mp (isIntegral_invariantRing G)
  exact isField_of_isIntegral_of_isField Subtype.val_injective h

/-! ### Division at an object scheme which is the spectrum of a field -/

/-- **Stacks Project, Tag 04S4, at an object scheme which is the spectrum of a field.**  A
subgroupoid on the same object scheme whose pre-relation is a monomorphism and whose source and
target maps are *finite* can be divided out, and the quotient is the spectrum of a field.

Over a field the two finite locally free hypotheses of
`AlgebraicGeometry.GroupoidScheme.exists_division` reduce to finiteness, by
`AlgebraicGeometry.isFiniteLocallyFree_of_isFinite_of_isoSpecField`, and affineness of the
object scheme is automatic.  The quotient morphism being finite locally free and surjective, its
global functions are a field by
`AlgebraicGeometry.isField_sections_of_isFiniteLocallyFree_of_surjective`. -/
@[stacks 04S4 "all four conclusions, at an object scheme which is the spectrum of a field and \
with only finiteness assumed of the source and target of the subgroupoid, together with the \
quotient being the spectrum of a field"]
theorem exists_division_isField_quotient_of_isoSpecField {S : Scheme.{u}} (G H : GroupoidScheme S)
    (i : GroupoidScheme.Hom H G) (hobj : H.objects = G.objects)
    (hiobj : i.mapObjects = eqToHom hobj) (k : Type u) [Field k]
    (e : G.objects.left ≅ Spec (.of k))
    [Mono i.mapArrows]
    [IsFinite H.source.left] [IsFinite H.target.left]
    [Mono (prod.lift H.target H.source)]
    [IsSeparated (prod.lift G.target G.source).left]
    [LocallyOfFiniteType (prod.lift G.target G.source).left]
    [LocallyQuasiFinite (prod.lift G.target G.source).left] :
    ∃ D : Division G H i hobj, IsField Γ(D.quotient.left, ⊤) := by
  have : IsAffine G.objects.left := IsAffine.of_isIso e.hom
  let e' : H.objects.left ≅ Spec (.of k) :=
    eqToIso (congrArg Over.left hobj) ≪≫ e
  have : IsFiniteLocallyFree H.source.left :=
    isFiniteLocallyFree_of_isFinite_of_isoSpecField k e' H.source.left
  have : IsFiniteLocallyFree H.target.left :=
    isFiniteLocallyFree_of_isFinite_of_isoSpecField k e' H.target.left
  obtain ⟨D⟩ := exists_division G H i hobj hiobj
  have := D.quotient_affine
  have := D.projection_finiteLocallyFree
  have := D.projection_surjective
  exact ⟨D, isField_sections_of_isFiniteLocallyFree_of_surjective D.projection.left
    (isField_sections_of_isoSpecField k e)⟩

end GroupoidScheme

end AlgebraicGeometry

end
