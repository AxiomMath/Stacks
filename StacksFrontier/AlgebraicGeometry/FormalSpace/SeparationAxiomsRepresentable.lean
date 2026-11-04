module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionQuasiSeparated
public import StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionSeparatedRepresentable
public import StacksFrontier.AlgebraicGeometry.FormalSpace.RepresentableLocalOnSourceAndTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms

/-!
# Separation axioms for formal algebraic spaces, through the genuine fibre product

Let `S` be a scheme contained in a big fppf site `B` and let `X` be a formal algebraic space
over `S`. **Stacks 0AJ7** calls `X` *quasi-separated* when the equivalent conditions of
**Stacks 0AJ5** hold, and *separated* when the equivalent conditions of **Stacks 0AJ6** hold.
Both lemmas are about the fibre product `U ×_X V` of two scheme-valued points of `X`, which for
a formal algebraic space is a scheme by **Stacks 0AIP**; the conditions then ask that scheme to
be quasi-compact, respectively affine with `𝒪(U) ⊗_ℤ 𝒪(V) ⟶ 𝒪(U ×_X V)` surjective.

This file records the two notions of Stacks 0AJ7 in that form:
`AlgebraicGeometry.FormalSpace.IsQuasiSeparatedFormalAlgebraicSpace` and
`AlgebraicGeometry.FormalSpace.IsSeparatedFormalAlgebraicSpace` apply to a formal algebraic
space, and they *assert* that for every pair of affine test objects `U`, `V` over `X` the fibre
product sheaf `U ×_X V` is represented by an object of the site, with quasi-compact,
respectively affine, underlying scheme (and the surjectivity on global sections). Nothing in
them is vacuous: a representing object always exists, by Stacks 0AIP for an arbitrary formal
algebraic space, and any two representing objects are isomorphic over `U` and `V`.

They are proved equivalent to each of the conditions of Stacks 0AJ5, respectively Stacks 0AJ6,
including quasi-separatedness, respectively separatedness, of the reduction of `X`; so they are
the notions of Stacks 0AJ7 under any choice of the defining condition.

The conditions `AlgebraicGeometry.FormalSpace.IsQuasiSeparated` and
`AlgebraicGeometry.FormalSpace.IsSeparated` of
`StacksFrontier.AlgebraicGeometry.FormalSpace.SeparationAxioms` and
`StacksFrontier.AlgebraicGeometry.FormalSpace.AffineFibreProduct` are stated for an arbitrary fppf
sheaf and quantify over the objects of the site representing the fibre product, so on a sheaf
whose fibre products are not representable they hold vacuously. On a formal algebraic space
they agree with the notions here, by
`AlgebraicGeometry.FormalSpace.isQuasiSeparatedFormalAlgebraicSpace_iff_isQuasiSeparated` and
`AlgebraicGeometry.FormalSpace.isSeparatedFormalAlgebraicSpace_iff_isSeparated`.

## Main definitions

* `AlgebraicGeometry.FormalSpace.HasRepresentableQuasiCompactIntersectionsULift`: the
  intersection condition of Stacks 0AJ5 asserting representability of the fibre product.
* `AlgebraicGeometry.FormalSpace.IsQuasiSeparatedFormalAlgebraicSpace`: **Stacks 0AJ7**,
  clause (1).
* `AlgebraicGeometry.FormalSpace.IsSeparatedFormalAlgebraicSpace`: **Stacks 0AJ7**, clause (2).

## Main results

* `AlgebraicGeometry.FormalSpace.isPullback_fppfYoneda_map_iff`: a square of represented fppf
  sheaves is cartesian exactly when the underlying square of presheaves is.
* `AlgebraicGeometry.FormalSpace.isQuasiSeparated_iff_hasQuasiCompactIntersectionsULift` and
  `AlgebraicGeometry.FormalSpace.isSeparated_iff_hasAffineIntersectionsULift`: the sheaf-level
  conditions of `SeparationAxioms` are the presheaf-level conditions read by Stacks 0AJ5 and
  Stacks 0AJ6.
* `AlgebraicGeometry.FormalSpace.isAbsolutelyQuasiSeparated_reduction_tfae_representable`:
  **Stacks 0AJ5** with clauses (2) and (3) asserting that `U ×_X V` is a scheme.
* `AlgebraicGeometry.FormalSpace.isQuasiSeparatedFormalAlgebraicSpace_tfae` and
  `AlgebraicGeometry.FormalSpace.isSeparatedFormalAlgebraicSpace_tfae`: the notions of
  Stacks 0AJ7 are equivalent to every condition of Stacks 0AJ5, respectively Stacks 0AJ6.
* `IsSeparatedFormalAlgebraicSpace.isQuasiSeparatedFormalAlgebraicSpace`: a separated formal
  algebraic space is quasi-separated.
* `AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace.isSeparatedFormalAlgebraicSpace`:
  an affine formal algebraic space is separated, hence quasi-separated.

## Implementation notes

A scheme-valued point `U ⟶ X` is a morphism `h_U ⟶ X` from the universe-lifted Yoneda presheaf
of an object `U` of the site to the presheaf underlying `X`, and the fibre product `U ×_X V` is
the fibre product of presheaves, which is the fibre product of fppf sheaves because the site is
subcanonical (`AlgebraicGeometry.FormalSpace.isPullback_fppfYoneda_map_iff`). That it is "a
scheme" is the existence of an object of the site with a cartesian square over the two points.
Clause (1) of Stacks 0AJ5 and of Stacks 0AJ6 is read against a reduction of `X` presented by a
presheaf of `Type u`, as in `StacksFrontier.AlgebraicGeometry.FormalSpace.ReductionQuasiSeparated`;
the reduction exists by Stacks 0AIN.

## References

* [Stacks Project, Tag 0AIN](https://stacks.math.columbia.edu/tag/0AIN)
* [Stacks Project, Tag 0AIP](https://stacks.math.columbia.edu/tag/0AIP)
* [Stacks Project, Tag 0AJ5](https://stacks.math.columbia.edu/tag/0AJ5)
* [Stacks Project, Tag 0AJ6](https://stacks.math.columbia.edu/tag/0AJ6)
* [Stacks Project, Tag 0AJ7](https://stacks.math.columbia.edu/tag/0AJ7)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Fibre products of sheaves and of presheaves -/

/-- **A square of represented fppf sheaves over an fppf sheaf is cartesian exactly when the
underlying square of presheaves is.** The square is read on presheaves through the
identification of the underlying presheaf of a sheafified representable with the
universe-lifted Yoneda presheaf; the forgetful functor from sheaves to presheaves preserves
and, being fully faithful, reflects fibre products. -/
theorem isPullback_fppfYoneda_map_iff {X : FppfSheaf B S hS} {U V P : BigFppfOver B S hS}
    (f : (fppfYoneda B S hS).obj U ⟶ X) (g : (fppfYoneda B S hS).obj V ⟶ X)
    (p : P ⟶ U) (q : P ⟶ V) :
    IsPullback ((fppfYoneda B S hS).map p) ((fppfYoneda B S hS).map q) f g ↔
      IsPullback ((uliftYoneda.{u + 1}).map p) ((uliftYoneda.{u + 1}).map q)
        ((fppfYonedaCompSheafToPresheaf' B S hS).inv.app U ≫ f.hom)
        ((fppfYonedaCompSheafToPresheaf' B S hS).inv.app V ≫ g.hom) := by
  let K := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  let e := fppfYonedaCompSheafToPresheaf' B S hS
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · refine (h.map K).of_iso (e.app P) (e.app U) (e.app V) (Iso.refl _)
      (e.hom.naturality p) (e.hom.naturality q) ?_ ?_ <;>
    · rw [Iso.app_hom, Iso.hom_inv_id_app_assoc, Iso.refl_hom, Category.comp_id]
      rfl
  · refine IsPullback.of_map_of_faithful K ?_
    refine h.of_iso (e.app P).symm (e.app U).symm (e.app V).symm (Iso.refl _)
      (e.inv.naturality p) (e.inv.naturality q) ?_ ?_ <;>
    · rw [Iso.symm_hom, Iso.app_inv, Iso.refl_hom, Category.comp_id]
      rfl

/-- A cartesian square of universe-lifted Yoneda presheaves over `X` gives a cartesian square of
represented fppf sheaves over `X`, through the preimages of the two points. -/
theorem isPullback_fppfYoneda_map_preimage {X : FppfSheaf B S hS} {U V P : BigFppfOver B S hS}
    (a : (uliftYoneda.{u + 1}).obj U ⟶ X.obj) (b : (uliftYoneda.{u + 1}).obj V ⟶ X.obj)
    (p : P ⟶ U) (q : P ⟶ V)
    (sq : IsPullback ((uliftYoneda.{u + 1}).map p) ((uliftYoneda.{u + 1}).map q) a b) :
    IsPullback ((fppfYoneda B S hS).map p) ((fppfYoneda B S hS).map q)
      ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).preimage
        ((fppfYonedaCompSheafToPresheaf' B S hS).hom.app U ≫ a))
      ((sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))).preimage
        ((fppfYonedaCompSheafToPresheaf' B S hS).hom.app V ≫ b)) := by
  let K := sheafToPresheaf (BigFppfOver.topology B S hS) (Type (u + 1))
  let e := fppfYonedaCompSheafToPresheaf' B S hS
  refine (isPullback_fppfYoneda_map_iff B S hS _ _ p q).mpr ?_
  show IsPullback _ _ (e.inv.app U ≫ K.map _) (e.inv.app V ≫ K.map _)
  rwa [K.map_preimage (e.hom.app U ≫ a), K.map_preimage (e.hom.app V ≫ b),
    Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app_assoc]

/-- A condition on the legs of a cartesian square over affine points of `X` reads the same
among fppf sheaves and among presheaves. -/
private theorem forall_isPullback_fppfYoneda_iff {X : FppfSheaf B S hS}
    (T : ∀ {U V P : BigFppfOver B S hS}, (P ⟶ U) → (P ⟶ V) → Prop) :
    (∀ U V P (f : (fppfYoneda B S hS).obj U ⟶ X) g (p : P ⟶ U) (q : P ⟶ V),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
        IsPullback ((fppfYoneda B S hS).map p) ((fppfYoneda B S hS).map q) f g → T p q) ↔
      ∀ U V Q (a : (uliftYoneda.{u + 1}).obj U ⟶ X.obj) b (p : Q ⟶ U) (q : Q ⟶ V),
      IsAffine ((BigFppfOver.toScheme B S hS).obj U) →
      IsAffine ((BigFppfOver.toScheme B S hS).obj V) →
        IsPullback ((uliftYoneda.{u + 1}).map p) ((uliftYoneda.{u + 1}).map q) a b → T p q :=
  ⟨fun h U V Q a b p q hU hV sq ↦
      h U V Q _ _ p q hU hV (isPullback_fppfYoneda_map_preimage B S hS a b p q sq),
    fun h U V P f g p q hU hV sq ↦
      h U V P _ _ p q hU hV ((isPullback_fppfYoneda_map_iff B S hS f g p q).mp sq)⟩

/-- **The quasi-separatedness condition of `SeparationAxioms` is the intersection condition of
Stacks 0AJ5 with affine test objects.** `AlgebraicGeometry.FormalSpace.IsQuasiSeparated` reads
the fibre product among fppf sheaves through the sheafified Yoneda embedding, and
`AlgebraicGeometry.FormalSpace.HasQuasiCompactIntersectionsULift` reads it among presheaves
through the universe-lifted Yoneda embedding; the two readings agree by
`AlgebraicGeometry.FormalSpace.isPullback_fppfYoneda_map_iff`. -/
theorem isQuasiSeparated_iff_hasQuasiCompactIntersectionsULift (X : FppfSheaf B S hS) :
    IsQuasiSeparated B S hS X ↔
      HasQuasiCompactIntersectionsULift B S hS (fun Z : Scheme.{u} ↦ IsAffine Z) X.obj :=
  forall_isPullback_fppfYoneda_iff B S hS _

/-- **The separatedness condition of `AffineFibreProduct` is clause (2) of Stacks 0AJ6 read on
presheaves.** `AlgebraicGeometry.FormalSpace.IsSeparated` reads the fibre product among fppf
sheaves through the sheafified Yoneda embedding, and
`AlgebraicGeometry.FormalSpace.HasAffineIntersectionsULift` reads it among presheaves through
the universe-lifted Yoneda embedding; the two readings agree by
`AlgebraicGeometry.FormalSpace.isPullback_fppfYoneda_map_iff`, and the two maps on global
sections are the same map. -/
theorem isSeparated_iff_hasAffineIntersectionsULift (X : FppfSheaf B S hS) :
    IsSeparated B S hS X ↔ HasAffineIntersectionsULift B S hS X.obj :=
  forall_isPullback_fppfYoneda_iff B S hS _

/-! ### The intersection condition of Stacks 0AJ5 asserting representability -/

/-- **The intersection condition of Stacks 0AJ5, asserting representability.** For every pair
of objects `U`, `V` of the big fppf site of `S` whose underlying schemes satisfy `P` and every
pair of morphisms `h_U ⟶ X`, `h_V ⟶ X` out of their universe-lifted Yoneda presheaves there is
an object of the site representing the fibre product `U ×_X V`, and its underlying scheme is
quasi-compact.

Clause (2) of Stacks 0AJ5 is this with `P` quasi-compactness of the underlying scheme and
clause (3) is this with `P` affineness of it, in the source's own reading, in which calling
`U ×_X V` quasi-compact presupposes that it is a scheme.
`AlgebraicGeometry.FormalSpace.HasQuasiCompactIntersectionsULift` is the weaker form which
quantifies over the representing objects instead; the two agree on a formal algebraic space,
by `AlgebraicGeometry.FormalSpace.hasRepresentableQuasiCompactIntersectionsULift_iff`. -/
abbrev HasRepresentableQuasiCompactIntersectionsULift (P : Scheme.{u} → Prop)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)) : Prop :=
  ∀ (U V : BigFppfOver B S hS)
    (a : (uliftYoneda.{u + 1}).obj U ⟶ X) (b : (uliftYoneda.{u + 1}).obj V ⟶ X),
    P ((BigFppfOver.toScheme B S hS).obj U) →
    P ((BigFppfOver.toScheme B S hS).obj V) →
    ∃ (Q : BigFppfOver B S hS) (p : Q ⟶ U) (q : Q ⟶ V),
      IsPullback ((uliftYoneda.{u + 1}).map p) ((uliftYoneda.{u + 1}).map q) a b ∧
        CompactSpace ((BigFppfOver.toScheme B S hS).obj Q)

/-- **The intersection condition asserting representability implies the one quantifying over
representing objects.** Two objects of the site representing one fibre product are isomorphic,
the universe-lifted Yoneda embedding being fully faithful, and quasi-compactness passes along an
isomorphism of schemes. -/
theorem hasQuasiCompactIntersectionsULift_of_hasRepresentableQuasiCompactIntersectionsULift
    (P : Scheme.{u} → Prop) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (u + 1)}
    (h : HasRepresentableQuasiCompactIntersectionsULift B S hS P X) :
    HasQuasiCompactIntersectionsULift B S hS P X := by
  intro U V Q a b p q hU hV sq
  obtain ⟨Q', p', q', sq', hQ'⟩ := h U V a b hU hV
  let ff : (uliftYoneda.{u + 1} (C := BigFppfOver B S hS)).FullyFaithful :=
    ULiftYoneda.fullyFaithful _
  exact QuasiCompact.compactSpace_of_compactSpace
    ((BigFppfOver.toScheme B S hS).mapIso (ff.preimageIso (sq.isoIsPullback _ _ sq'))).hom

/-- **The two forms of the intersection condition of Stacks 0AJ5 agree on a formal algebraic
space.** The stronger form implies the weaker one always; the converse needs a representing
object for the fibre product of two scheme-valued points, which is the representability
assertion of Stacks 0AIP for an arbitrary formal algebraic space. -/
theorem hasRepresentableQuasiCompactIntersectionsULift_iff (P : Scheme.{u} → Prop)
    {X : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X) :
    HasRepresentableQuasiCompactIntersectionsULift B S hS P X.obj ↔
      HasQuasiCompactIntersectionsULift B S hS P X.obj := by
  have : HasBinaryProducts (BigFppfOver B S hS) :=
    hasBinaryProducts_of_hasTerminal_and_pullbacks _
  refine ⟨hasQuasiCompactIntersectionsULift_of_hasRepresentableQuasiCompactIntersectionsULift
    B S hS P, fun h U V a b hU hV ↦ ?_⟩
  obtain ⟨Q, p, q, sq, -⟩ :=
    exists_isPullback_locallyOfFiniteType_of_isFormalAlgebraicSpace B S hS hX U V a b
  exact ⟨Q, p, q, sq, h U V Q a b p q hU hV sq⟩

variable (hZ : B.Contains (⊤_ Scheme.{u}))

/-- **Stacks 0AJ5, with clauses (2) and (3) asserting representability.** Let `X` be a formal
algebraic space over `S` and let `i : X_red ⟶ X` be a reduction of `X`, presented by a presheaf
`Xred` of `Type u` together with an isomorphism from its universe lift. The following are
equivalent: `Xred` is a quasi-separated algebraic space; for every pair of objects of the big
fppf site of `S` with quasi-compact underlying scheme and every pair of morphisms from their
universe-lifted Yoneda presheaves into `X`, the fibre product is represented by an object of
the site with quasi-compact underlying scheme; and the same for every pair of objects with
affine underlying scheme.

This is `AlgebraicGeometry.FormalSpace.isAbsolutelyQuasiSeparated_reduction_tfae` together with
`AlgebraicGeometry.FormalSpace.hasRepresentableQuasiCompactIntersectionsULift_iff`. -/
@[stacks 0AJ5 "with clauses (2) and (3) in the source's own form, asserting that the fibre \
product U ×_X V is representable by an object of the site with quasi-compact underlying \
scheme; read against a reduction of X, in the sense of AlgebraicGeometry.FormalSpace.\
IsReduction and supplied by Stacks 0AIN, presented by a presheaf of Type u together with an \
isomorphism from its universe lift"]
theorem isAbsolutelyQuasiSeparated_reduction_tfae_representable
    {X Xr : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    {i : Xr ⟶ X} (hi : IsReduction B S hS X Xr i)
    {Xred : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : Xred ⋙ uliftFunctor.{u + 1} ≅ Xr.obj) :
    List.TFAE
      [ Space.IsAbsolutelyQuasiSeparated B S hS hZ Xred,
        HasRepresentableQuasiCompactIntersectionsULift B S hS
          (fun Z : Scheme.{u} ↦ CompactSpace (Z : Type u)) X.obj,
        HasRepresentableQuasiCompactIntersectionsULift B S hS
          (fun Z : Scheme.{u} ↦ IsAffine Z) X.obj ] := by
  rw [hasRepresentableQuasiCompactIntersectionsULift_iff B S hS _ hX,
    hasRepresentableQuasiCompactIntersectionsULift_iff B S hS _ hX]
  exact isAbsolutelyQuasiSeparated_reduction_tfae B S hS hZ hX hi e

/-! ### Stacks 0AJ7 -/

/-- **Stacks 0AJ7, clause (1): quasi-separated formal algebraic spaces.** A formal algebraic
space `X` over `S` is *quasi-separated* when the equivalent conditions of Stacks 0AJ5 hold.
The condition recorded is clause (3) of Stacks 0AJ5: for every pair of objects `U`, `V` of the
big fppf site of `S` with affine underlying scheme and every pair of morphisms `U ⟶ X`,
`V ⟶ X` (morphisms `h_U ⟶ X`, `h_V ⟶ X` of presheaves out of the universe-lifted Yoneda
presheaves), the fibre product `U ×_X V` is a scheme — represented by an object of the site
with a cartesian square over the two morphisms — and that scheme is quasi-compact.

The fibre product is the genuine one, and it is always representable, by Stacks 0AIP; so the
condition is never vacuous. Its equivalence with the other conditions of Stacks 0AJ5 —
quasi-separatedness of the reduction of `X`, and clause (2) with quasi-compact test objects —
is `AlgebraicGeometry.FormalSpace.isQuasiSeparatedFormalAlgebraicSpace_tfae`. On a formal
algebraic space it agrees with `AlgebraicGeometry.FormalSpace.IsQuasiSeparated`, by
`AlgebraicGeometry.FormalSpace.isQuasiSeparatedFormalAlgebraicSpace_iff_isQuasiSeparated`. -/
@[stacks 0AJ7 "clause (1): a formal algebraic space is quasi-separated when the conditions of \
Stacks 0AJ5 hold, recorded as clause (3) of Stacks 0AJ5 with the fibre product asserted to be \
a scheme; equivalent to every condition of Stacks 0AJ5 by \
isQuasiSeparatedFormalAlgebraicSpace_tfae"]
def IsQuasiSeparatedFormalAlgebraicSpace (X : FppfSheaf B S hS) : Prop :=
  IsFormalAlgebraicSpace B S hS X ∧
    HasRepresentableQuasiCompactIntersectionsULift B S hS (fun Z : Scheme.{u} ↦ IsAffine Z) X.obj

/-- **Stacks 0AJ7, clause (2): separated formal algebraic spaces.** A formal algebraic space
`X` over `S` is *separated* when the equivalent conditions of Stacks 0AJ6 hold. The condition
recorded is clause (2) of Stacks 0AJ6: for every pair of objects `U`, `V` of the big fppf site
of `S` with affine underlying scheme and every pair of morphisms `U ⟶ X`, `V ⟶ X` (morphisms
`h_U ⟶ X`, `h_V ⟶ X` of presheaves out of the universe-lifted Yoneda presheaves), the fibre
product `U ×_X V` is a scheme — represented by an object of the site with a cartesian square
over the two morphisms — that scheme is affine, and the canonical map
`𝒪(U) ⊗_ℤ 𝒪(V) ⟶ 𝒪(U ×_X V)` is surjective.

The fibre product is the genuine one, and it is always representable, by Stacks 0AIP; so the
condition is never vacuous. Its equivalence with clause (1) of Stacks 0AJ6, separatedness of
the reduction of `X`, is `AlgebraicGeometry.FormalSpace.isSeparatedFormalAlgebraicSpace_tfae`.
On a formal algebraic space it agrees with `AlgebraicGeometry.FormalSpace.IsSeparated`, by
`AlgebraicGeometry.FormalSpace.isSeparatedFormalAlgebraicSpace_iff_isSeparated`. -/
@[stacks 0AJ7 "clause (2): a formal algebraic space is separated when the conditions of \
Stacks 0AJ6 hold, recorded as clause (2) of Stacks 0AJ6 with the fibre product asserted to be \
a scheme; equivalent to clause (1) of Stacks 0AJ6 by isSeparatedFormalAlgebraicSpace_tfae"]
def IsSeparatedFormalAlgebraicSpace (X : FppfSheaf B S hS) : Prop :=
  IsFormalAlgebraicSpace B S hS X ∧ HasRepresentableAffineIntersectionsULift B S hS X.obj

/-- A quasi-separated formal algebraic space is a formal algebraic space. -/
theorem IsQuasiSeparatedFormalAlgebraicSpace.isFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (h : IsQuasiSeparatedFormalAlgebraicSpace B S hS X) : IsFormalAlgebraicSpace B S hS X :=
  h.1

/-- A separated formal algebraic space is a formal algebraic space. -/
theorem IsSeparatedFormalAlgebraicSpace.isFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (h : IsSeparatedFormalAlgebraicSpace B S hS X) : IsFormalAlgebraicSpace B S hS X :=
  h.1

/-- **On a formal algebraic space, quasi-separatedness in the sense of Stacks 0AJ7 is the
condition `AlgebraicGeometry.FormalSpace.IsQuasiSeparated`.** That condition quantifies over the
objects of the site representing the fibre product, and the fibre product of two scheme-valued
points of a formal algebraic space is representable by Stacks 0AIP. -/
theorem isQuasiSeparatedFormalAlgebraicSpace_iff_isQuasiSeparated {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) :
    IsQuasiSeparatedFormalAlgebraicSpace B S hS X ↔ IsQuasiSeparated B S hS X := by
  rw [isQuasiSeparated_iff_hasQuasiCompactIntersectionsULift,
    ← hasRepresentableQuasiCompactIntersectionsULift_iff B S hS _ hX]
  exact and_iff_right hX

/-- **On a formal algebraic space, separatedness in the sense of Stacks 0AJ7 is the condition
`AlgebraicGeometry.FormalSpace.IsSeparated`.** That condition quantifies over the objects of the
site representing the fibre product, and the fibre product of two scheme-valued points of a
formal algebraic space is representable by Stacks 0AIP. -/
theorem isSeparatedFormalAlgebraicSpace_iff_isSeparated {X : FppfSheaf B S hS}
    (hX : IsFormalAlgebraicSpace B S hS X) :
    IsSeparatedFormalAlgebraicSpace B S hS X ↔ IsSeparated B S hS X := by
  rw [isSeparated_iff_hasAffineIntersectionsULift,
    ← hasRepresentableAffineIntersectionsULift_iff B S hS hX]
  exact and_iff_right hX

/-- **Stacks 0AJ7, clause (1), is the class of the conditions of Stacks 0AJ5.** Let `X` be a
formal algebraic space over `S` and let `i : X_red ⟶ X` be a reduction of `X`, presented by a
presheaf `Xred` of `Type u` together with an isomorphism from its universe lift. The following
are equivalent: `X` is quasi-separated in the sense of Stacks 0AJ7; `Xred` is a quasi-separated
algebraic space (clause (1) of Stacks 0AJ5); for every pair of quasi-compact test objects over
`X` the fibre product is a quasi-compact scheme (clause (2)); and the same for every pair of
affine test objects (clause (3)). -/
@[stacks 0AJ7 "clause (1): the definition is equivalent to each of the conditions of Stacks \
0AJ5, read against a reduction of X presented by a presheaf of Type u, which exists by \
Stacks 0AIN"]
theorem isQuasiSeparatedFormalAlgebraicSpace_tfae
    {X Xr : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    {i : Xr ⟶ X} (hi : IsReduction B S hS X Xr i)
    {Xred : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : Xred ⋙ uliftFunctor.{u + 1} ≅ Xr.obj) :
    List.TFAE
      [ IsQuasiSeparatedFormalAlgebraicSpace B S hS X,
        Space.IsAbsolutelyQuasiSeparated B S hS hZ Xred,
        HasRepresentableQuasiCompactIntersectionsULift B S hS
          (fun Z : Scheme.{u} ↦ CompactSpace (Z : Type u)) X.obj,
        HasRepresentableQuasiCompactIntersectionsULift B S hS
          (fun Z : Scheme.{u} ↦ IsAffine Z) X.obj ] := by
  have h := isAbsolutelyQuasiSeparated_reduction_tfae_representable B S hS hZ hX hi e
  tfae_have 1 ↔ 4 := and_iff_right hX
  tfae_have 2 ↔ 3 := h.out 1 2
  tfae_have 2 ↔ 4 := h.out 1 3
  tfae_finish

/-- **Stacks 0AJ7, clause (2), is the class of the conditions of Stacks 0AJ6.** Let `X` be a
formal algebraic space over `S` and let `i : X_red ⟶ X` be a reduction of `X`, presented by a
presheaf `Xred` of `Type u` together with an isomorphism from its universe lift. Then `X` is
separated in the sense of Stacks 0AJ7 if and only if `Xred` is a separated algebraic space
(clause (1) of Stacks 0AJ6). -/
@[stacks 0AJ7 "clause (2): the definition is equivalent to clause (1) of Stacks 0AJ6, read \
against a reduction of X presented by a presheaf of Type u, which exists by Stacks 0AIN"]
theorem isSeparatedFormalAlgebraicSpace_tfae
    {X Xr : FppfSheaf B S hS} (hX : IsFormalAlgebraicSpace B S hS X)
    {i : Xr ⟶ X} (hi : IsReduction B S hS X Xr i)
    {Xred : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : Xred ⋙ uliftFunctor.{u + 1} ≅ Xr.obj) :
    IsSeparatedFormalAlgebraicSpace B S hS X ↔ Space.IsAbsolutelySeparated B S hS hZ Xred :=
  (and_iff_right hX).trans
    (isAbsolutelySeparated_reduction_iff_hasRepresentableAffineIntersectionsULift
      B S hS hZ hX hi e).symm

/-- **A separated formal algebraic space is quasi-separated**: an affine scheme is
quasi-compact. -/
theorem IsSeparatedFormalAlgebraicSpace.isQuasiSeparatedFormalAlgebraicSpace
    {X : FppfSheaf B S hS} (h : IsSeparatedFormalAlgebraicSpace B S hS X) :
    IsQuasiSeparatedFormalAlgebraicSpace B S hS X := by
  refine ⟨h.1, fun U V a b hU hV ↦ ?_⟩
  obtain ⟨Q, p, q, sq, hQ, -⟩ := h.2 U V a b hU hV
  have _ := hQ
  exact ⟨Q, p, q, sq, inferInstance⟩

/-- **An affine formal algebraic space is separated** in the sense of Stacks 0AJ7. It is a
formal algebraic space, and it satisfies `AlgebraicGeometry.FormalSpace.IsSeparated` by
`AlgebraicGeometry.FormalSpace.IsAffineFormalAlgebraicSpace.isSeparated`. -/
theorem IsAffineFormalAlgebraicSpace.isSeparatedFormalAlgebraicSpace {X : FppfSheaf B S hS}
    (hX : IsAffineFormalAlgebraicSpace B S hS X) : IsSeparatedFormalAlgebraicSpace B S hS X :=
  (isSeparatedFormalAlgebraicSpace_iff_isSeparated B S hS
    (isFormalAlgebraicSpace_of_isAffineFormalAlgebraicSpace B S hS hX)).mpr
    (IsAffineFormalAlgebraicSpace.isSeparated B S hS hX)

/-- **An affine formal algebraic space is quasi-separated** in the sense of Stacks 0AJ7, being
separated. -/
theorem IsAffineFormalAlgebraicSpace.isQuasiSeparatedFormalAlgebraicSpace
    {X : FppfSheaf B S hS} (hX : IsAffineFormalAlgebraicSpace B S hS X) :
    IsQuasiSeparatedFormalAlgebraicSpace B S hS X :=
  IsSeparatedFormalAlgebraicSpace.isQuasiSeparatedFormalAlgebraicSpace B S hS
    (IsAffineFormalAlgebraicSpace.isSeparatedFormalAlgebraicSpace B S hS hX)

end AlgebraicGeometry.FormalSpace

end
