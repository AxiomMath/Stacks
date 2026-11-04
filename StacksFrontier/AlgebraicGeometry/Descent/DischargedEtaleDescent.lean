module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineHomEtaleDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubschemeGroupoid
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Discharging the effective-descent hypotheses that are now theorems

`AlgebraicGeometry.Space.IsEffectiveDescentAlongSurjectiveEtale B S hS P` is the one geometric
hypothesis of Stacks 03I2, and several statements in this library still carry it. For three
properties it is no longer a hypothesis but a theorem of this library:

* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isImmersion`, for immersions;
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom`, Stacks 0247,
  for quasi-affine morphisms;
* `AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom`, for affine
  morphisms.

This file restates, unconditionally, the statements which carried the hypothesis at one of those
three properties and had no unconditional form elsewhere. Each declaration here is its
conditional original with the hypothesis supplied; the conditional originals are kept, so no
existing consumer changes.

The hypothesis is **not** discharged everywhere, and must not be: it is **false** for
`P = AlgebraicGeometry.Etale` by Stacks 02Z0, and
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_of_le` transfers it only
*downwards* along `≤`, so a site at a property which contains none of the three above gets
nothing from this file. In particular the covering-sieve predicate
`AlgebraicGeometry.Space.IsEffectiveDescentAlongCoveringSieve` is a different predicate, monotone
in neither direction with respect to the one used here, and the statements carrying it are left
alone.

## Main results

Every name in this section is relative to the namespace `AlgebraicGeometry.Space`, in which the
whole file lives; the fully qualified forms are too long for one line.

* `isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_quasiFinite_unconditional`
  is the quasi-compact case of Stacks 02W8 outright: effective descent along a surjective étale
  chart of the site for the separated quasi-finite morphisms of schemes.
* `isRepresentable_openSubspaceOfPoints_unconditional` is the representability of a stable
  quasi-compact open subspace of a descended fibre product, outright.
* `presheaf_isAffineHom_of_surjectiveEtaleChart_unconditional` and
  `presheaf_isAffineHom_of_etaleChart_of_isAlgebraicSpace_unconditional`
  are the two implications of Stacks 03WG into condition (1), outright.
* `Presentation.invariantLocallyClosedSubschemeEquiv_unconditional`,
  `Presentation.closed_iff_unconditional` and `Presentation.open_iff_unconditional` are the three
  parts of Stacks 07TW against the canonical groupoid scheme of the presenting relation, with
  invariance taken in the groupoid sense of Stacks 03BC part (4).

## Implementation notes

The three parts of Stacks 07TW already carry their tag, unconditionally, on the chart-based forms
`AlgebraicGeometry.Space.invariantLocallyClosedSubschemeEquiv_of_isAlgebraicSpace`,
`AlgebraicGeometry.Space.closed_iff_of_isAlgebraicSpace` and
`AlgebraicGeometry.Space.open_iff_of_isAlgebraicSpace`, and on the groupoid forms of
`StacksFrontier/AlgebraicGeometry/Spaces/InvariantSubschemeGroupoid.lean`. The instantiations at the
canonical groupoid scheme below are those groupoid forms at one particular groupoid scheme, so
they are deliberately left untagged: the tag's covering set is already complete and a second site
for each part would double-count it. For the same reason Stacks 03WG keeps its single tag site on
`AlgebraicGeometry.Space.isAffineHom_tfae_of_isAlgebraicSpace`, which this file does not touch.

The hypothesis `hX : AlgebraicGeometry.Space.IsAlgebraicSpace B S hS X` is **not** discharged in
the Stacks 07TW statements and is not meant to be: in the groupoid forms it is the implicit
argument of the type `AlgebraicGeometry.Space.Presentation B S hS X hX`, so a presentation cannot
even be mentioned without it. It is a genuine hypothesis of the source statement, not a residue
of the descent hypothesis.

## References

* [Stacks Project, Tag 02W8](https://stacks.math.columbia.edu/tag/02W8)
* [Stacks Project, Tag 0247](https://stacks.math.columbia.edu/tag/0247)
* [Stacks Project, Tag 03BC](https://stacks.math.columbia.edu/tag/03BC)
* [Stacks Project, Tag 03I2](https://stacks.math.columbia.edu/tag/03I2)
* [Stacks Project, Tag 03WG](https://stacks.math.columbia.edu/tag/03WG)
* [Stacks Project, Tag 07TW](https://stacks.math.columbia.edu/tag/07TW)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Stacks.Groupoids

universe u

namespace AlgebraicGeometry.Space

/-! ### Descent at the separated quasi-finite morphisms -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **The quasi-compact case of Stacks 02W8, outright.** Morphisms of schemes which are
separated, locally quasi-finite, locally of finite type and quasi-compact descend effectively
along the surjective étale morphisms of the big fppf site of `S`.

This is the declaration
`isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_quasiFinite_of_isQuasiAffineHom` of this
namespace with its hypothesis `h0247` supplied by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom`. Its Stacks
02LR input, the containment of the separated quasi-finite morphisms in the quasi-affine ones, was
already discharged there by `AlgebraicGeometry.isSeparated_inf_quasiFinite_le_isQuasiAffineHom`. -/
@[sga "3 X 5.4" "special case"]
theorem isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_quasiFinite_unconditional
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    IsEffectiveDescentAlongSurjectiveEtale B S hS
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓
        @LocallyOfFiniteType ⊓ @QuasiCompact : MorphismProperty Scheme.{u}) :=
  isEffectiveDescentAlongSurjectiveEtale_isSeparated_inf_quasiFinite_of_isQuasiAffineHom
    (isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom B S hS)

/-! ### The stable quasi-compact open subspace -/

/-- **The third step of Stacks 02W8, outright.** A quasi-compact open subspace of a descended
fibre product which is cut out on points and is covered by one quasi-compact open of the chart's
presentation is representable.

This is `AlgebraicGeometry.Space.isRepresentable_openSubspaceOfPoints_of_isQuasiAffineHom` with
its hypothesis `h0247` supplied by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom`. -/
theorem isRepresentable_openSubspaceOfPoints_unconditional
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    {a c : BigFppfOver B S hS} (π : G ⟶ yoneda.obj a) (q : c ⟶ a)
    (hc : IsAffine ((BigFppfOver.toScheme B S hS).obj c))
    (hqs : Surjective ((BigFppfOver.toScheme B S hS).map q))
    (hqe : Etale ((BigFppfOver.toScheme B S hS).map q))
    {U : BigFppfOver B S hS} {g : yoneda.obj U ⟶ G} {ρ : yoneda.obj U ⟶ yoneda.obj c}
    (sqg : IsPullback g ρ π (yoneda.map q))
    (hρ : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsSeparated.{u} ⊓ @LocallyQuasiFinite ⊓ @LocallyOfFiniteType :
        MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf ρ)
    {W : Set (points B S hS G)} {b : BigFppfOver B S hS} {i : b ⟶ U}
    (hi : _root_.AlgebraicGeometry.IsOpenImmersion ((BigFppfOver.toScheme B S hS).map i))
    (hbqc : IsCompact (Set.range ((BigFppfOver.toScheme B S hS).map i)))
    {k : yoneda.obj b ⟶ (openSubspaceOfPoints B S hS G W).toFunctor}
    (hsqb : IsPullback k (yoneda.map i) (openSubspaceOfPoints B S hS G W).ι g) :
    (openSubspaceOfPoints B S hS G W).toFunctor.IsRepresentable :=
  isRepresentable_openSubspaceOfPoints_of_isQuasiAffineHom
    (isEffectiveDescentAlongSurjectiveEtale_isQuasiAffineHom B S hS)
    hG π q hc hqs hqe sqg hρ hi hbqc hsqb

/-! ### Stacks 03WG into condition (1) -/

variable {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- **Stacks 03WG, (4) implies (1)**, outright, with the base changes of `f` along *all*
morphisms from objects of the site assumed affine. If some surjective étale chart `g` of the
target of `f` makes that base change of `f` affine, then `f` is representable with affine
represented base changes.

This is `AlgebraicGeometry.Space.presheaf_isAffineHom_of_surjectiveEtaleChart` with its
hypothesis `hdesc` supplied by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom`. -/
theorem presheaf_isAffineHom_of_surjectiveEtaleChart_unconditional
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y}
    (hs : IsSurjective B S hS g) (he : IsEtale B S hS g)
    (hV : (MorphismProperty.inverseImage
      (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd f g)) :
    yoneda.relativelyRepresentable f ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  presheaf_isAffineHom_of_surjectiveEtaleChart
    (isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S hS) hX hY hs he hV

/-- **Stacks 03WG, (4) implies (1)**, outright, with condition (4) in the form of Stacks 03WF.
If some surjective étale chart `g` of the target of `f` makes the base change of `f` affine as a
morphism of algebraic spaces, then `f` is representable with affine represented base changes.

This is `AlgebraicGeometry.Space.presheaf_isAffineHom_of_etaleChart_of_isAlgebraicSpace` with its
hypothesis `hdesc` supplied by
`AlgebraicGeometry.Space.isEffectiveDescentAlongSurjectiveEtale_isAffineHom`. Unlike
`AlgebraicGeometry.Space.presheaf_isAffineHom_of_surjectiveEtaleChart_unconditional` it asks of
the base change only the affineness of Stacks 03WF, which tests the morphisms from the *affine*
objects of the site; relative Tag 03JH closes the gap inside the conditional original. -/
theorem presheaf_isAffineHom_of_etaleChart_of_isAlgebraicSpace_unconditional
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) {f : X ⟶ Y}
    {V : BigFppfOver B S hS} {g : yoneda.obj V ⟶ Y}
    (hs : IsSurjective B S hS g) (he : IsEtale B S hS g)
    (h₄ : IsAffineHom B S hS (pullback.snd f g)) :
    yoneda.relativelyRepresentable f ∧
      (MorphismProperty.inverseImage
        (@_root_.AlgebraicGeometry.IsAffineHom.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)).presheaf f :=
  presheaf_isAffineHom_of_etaleChart_of_isAlgebraicSpace B S hS
    (isEffectiveDescentAlongSurjectiveEtale_isAffineHom B S hS) hX hY hs he h₄

/-! ### Stacks 07TW in the groupoid sense -/

section Invariant

variable (B S hS) {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hX : IsAlgebraicSpace B S hS X}

/-- The pre-relation of a presentation: its two projections, as a morphism of the relation scheme
into the self-product of the presenting scheme over `S`. This is the pre-relation whose étale
equivalence-relation property is the field
`AlgebraicGeometry.Space.Presentation.isEtaleEquivalenceRelation`. -/
noncomputable abbrev Presentation.preRelation (P : Presentation B S hS X hX) :
    PreRelation ((Over.post B.inclusion).obj P.R) ((Over.post B.inclusion).obj P.U) :=
  prod.lift ((Over.post B.inclusion).map P.target) ((Over.post B.inclusion).map P.source)

/-- The two projections of a presentation are an equivalence relation. This is the
`AlgebraicGeometry.Space.Presentation.isEtaleEquivalenceRelation` field, stated against
`AlgebraicGeometry.Space.Presentation.preRelation`. -/
theorem Presentation.isEquivalenceRelation_preRelation (P : Presentation B S hS X hX) :
    IsEquivalenceRelation (P.preRelation B S hS).target (P.preRelation B S hS).source :=
  IsEtaleEquivalenceRelation.isEquivalenceRelation (self := P.isEtaleEquivalenceRelation)

/-- The canonical groupoid scheme of a presentation: the unique groupoid scheme extending its
presenting relation, by
`AlgebraicGeometry.existsUnique_groupoidScheme_of_isEquivalenceRelation`. -/
noncomputable def Presentation.relationGroupoid (P : Presentation B S hS X hX) :
    GroupoidScheme S :=
  have := P.isEquivalenceRelation_preRelation B S hS
  _root_.AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation (P.preRelation B S hS)

/-- The canonical groupoid scheme of a presentation extends its presenting relation. -/
theorem Presentation.extendsRelation_relationGroupoid (P : Presentation B S hS X hX) :
    _root_.AlgebraicGeometry.ExtendsRelation (P.preRelation B S hS)
      (P.relationGroupoid B S hS) :=
  have := P.isEquivalenceRelation_preRelation B S hS
  _root_.AlgebraicGeometry.groupoidSchemeOfIsEquivalenceRelation_extendsRelation
    (P.preRelation B S hS)

/-- The object scheme of the canonical groupoid scheme of a presentation is the presenting
scheme. This is the identification which the invariance condition of Stacks 03BC part (4) is
stated against. -/
theorem Presentation.relationGroupoid_objects_left (P : Presentation B S hS X hX) :
    (P.relationGroupoid B S hS).objects.left = (BigFppfOver.toScheme B S hS).obj P.U :=
  congrArg Over.left (P.extendsRelation_relationGroupoid B S hS).objects_eq

/-! #### Against the canonical groupoid of the presenting relation

The three parts of Stacks 07TW in
`StacksFrontier/AlgebraicGeometry/Spaces/InvariantSubschemeGroupoid.lean` quantify over any groupoid
scheme extending the presenting relation. Instantiating them at the canonical one,
`AlgebraicGeometry.Space.Presentation.relationGroupoid`, gives the three parts with no groupoid
scheme chosen by the user. -/

/-- **Stacks 07TW**, the canonical bijection, outright, against the canonical groupoid scheme of
the presenting relation: for an algebraic space `X` over `S` with a presentation `P`, the locally
closed subschemes of the presenting scheme which are invariant in the sense of Stacks 03BC part
(4) correspond bijectively to the locally closed subspaces of `X`, and the bijection is
characterised by pullback along the atlas.

This is
`AlgebraicGeometry.Space.Presentation.invariantLocallyClosedSubschemeEquivOfExtendsRelation` at
`AlgebraicGeometry.Space.Presentation.relationGroupoid`. -/
noncomputable def Presentation.invariantLocallyClosedSubschemeEquiv_unconditional
    (P : Presentation B S hS X hX) :
    {e : {Z : Subobject ((BigFppfOver.toScheme B S hS).obj P.U) //
            _root_.AlgebraicGeometry.IsImmersion Z.arrow ∧
              IsInvariantMonomorphism (P.relationGroupoid B S hS)
                (Z.arrow ≫ eqToHom (P.relationGroupoid_objects_left B S hS).symm)} ≃
          LocallyClosedQuotientSubspace B S hS (X := X) //
      ∀ Z, ((e Z).1.preimage P.toSpace) = subschemePoints B S hS Z.1} :=
  P.invariantLocallyClosedSubschemeEquivOfExtendsRelation B S hS
    (P.extendsRelation_relationGroupoid B S hS) (P.relationGroupoid_objects_left B S hS)

/-- **Stacks 07TW**, closedness, outright, against the canonical groupoid scheme of the presenting
relation: the subspace of `X` corresponding to an invariant subscheme of the presenting scheme is
closed exactly when that subscheme is closed. -/
theorem Presentation.closed_iff_unconditional (P : Presentation B S hS X hX)
    (Z : {Z : Subobject ((BigFppfOver.toScheme B S hS).obj P.U) //
      _root_.AlgebraicGeometry.IsImmersion Z.arrow ∧
        IsInvariantMonomorphism (P.relationGroupoid B S hS)
          (Z.arrow ≫ eqToHom (P.relationGroupoid_objects_left B S hS).symm)}) :
    IsClosedSubspace B S hS
        ((P.invariantLocallyClosedSubschemeEquiv_unconditional B S hS).1 Z).1 ↔
      _root_.AlgebraicGeometry.IsClosedImmersion Z.1.arrow :=
  P.closed_iff_of_extendsRelation B S hS
    (P.extendsRelation_relationGroupoid B S hS) (P.relationGroupoid_objects_left B S hS) Z

/-- **Stacks 07TW**, openness, outright, against the canonical groupoid scheme of the presenting
relation: the subspace of `X` corresponding to an invariant subscheme of the presenting scheme is
open exactly when that subscheme is open. -/
theorem Presentation.open_iff_unconditional (P : Presentation B S hS X hX)
    (Z : {Z : Subobject ((BigFppfOver.toScheme B S hS).obj P.U) //
      _root_.AlgebraicGeometry.IsImmersion Z.arrow ∧
        IsInvariantMonomorphism (P.relationGroupoid B S hS)
          (Z.arrow ≫ eqToHom (P.relationGroupoid_objects_left B S hS).symm)}) :
    IsOpenSubspace B S hS
        ((P.invariantLocallyClosedSubschemeEquiv_unconditional B S hS).1 Z).1 ↔
      _root_.AlgebraicGeometry.IsOpenImmersion Z.1.arrow :=
  P.open_iff_of_extendsRelation B S hS
    (P.extendsRelation_relationGroupoid B S hS) (P.relationGroupoid_objects_left B S hS) Z

end Invariant

end AlgebraicGeometry.Space

end
