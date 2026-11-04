module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.VTopologySheafCriterion
public import StacksFrontier.AlgebraicGeometry.ProEtale.IndEtale.VTopologySheafCriterionOver
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsCofilteredLimits
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsSubcategorySheaf
public import StacksFrontier.AlgebraicGeometry.Topologies.H.BigSite
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.ExtendingFunctors
public import StacksFrontier.AlgebraicGeometry.Topologies.V.PhVFlatteningModification

/-!
# The extension of an h sheaf from a big h site: its uniqueness, and the V sheaf property

Let `S` be a scheme contained in a big h site and let `F` be a sheaf of sets on the big h
category `(Sch/S)_h` which carries a directed inverse limit of affine objects to the filtered
colimit of its values, the hypothesis `F(T) = colim F(T_i)` of Stacks 0EVR.  The remark asserts
that `F` extends *uniquely* to a contravariant functor `F'` on all schemes over `S` which (a)
satisfies the sheaf property for the h topology and (b) is limit preserving in the sense of
Stacks 05LX, and then, by Stacks 0EVQ, that `F'` also satisfies the sheaf property for the V
topology.

The remark is approached here from three sides.

* `AlgebraicGeometry.ExtendingFunctors.exists_unique_isHSheaf_isVSheaf_extension` is the whole
  of the remark, the V sheaf property included, in the source's own shape: a functor on the
  schemes over `S`, with the uniqueness.  It carries the `@[stacks 0EVR]` registration.  The V
  clause is the only one that uses Stacks 0ETR, and that tag is a theorem of this development,
  `AlgebraicGeometry.isPHCovering_iff_isVCovering`; so nothing is granted.
* `AlgebraicGeometry.ExtendingFunctors.exists_unique_isHSheaf_extension` proves (a), (b) and the
  uniqueness the remark asserts, for a functor on `Sch/S`, out of Stacks 0EV3 and
  Stacks 0EUW alone — without Stacks 0ETR, and so without the V sheaf property.  It is
  kept as the record of how much of the remark is reached that way, and carries no tag, omitting
  an assertion of the remark.
* `AlgebraicGeometry.exists_isVSheaf_extension_of_isSheaf_of_preservesAffineLimits` composes the
  two results the remark cites.  It reaches all three of (a), (b) and the V sheaf property, but
  for a functor on `Scheme` rather than on the schemes over `S`, and only once the conclusion of
  Stacks 0EV3 is granted as `h0EV3`, in the shape the library's Stacks 0EVQ consumes.  It claims no
  uniqueness, and it carries no tag: a statement which assumes the conclusion of one of the two
  results the remark cites does not register the remark.  It is kept as the record of how far
  the composition the remark describes goes.

## Main results

* `AlgebraicGeometry.ExtendingFunctors.exists_unique_isHSheaf_isVSheaf_extension` — **every
  assertion of the remark at once**: an h sheaf on the big h category over `S` with the colimit
  property extends, uniquely up to isomorphism, to a functor on all schemes over `S` which is an
  h sheaf, is limit preserving and is a sheaf for the V topology.  Nothing is granted.
* `AlgebraicGeometry.ExtendingFunctors.exists_unique_isHSheaf_extension` — the same without the
  V clause, from Stacks 0EV3 and Stacks 0EUW alone.
* `AlgebraicGeometry.ExtendingFunctors.isZariskiSheaf_of_isHSheaf` — an h sheaf on `Sch/S` is a
  Zariski sheaf, since a covering by open subobjects is an fppf covering and an fppf covering is
  an h covering.
* `AlgebraicGeometry.ExtendingFunctors.isVSheafOver_of_isHSheaf_of_preservesAffineLimits` — the
  relative Stacks 0EVQ read through the ph form of an h covering: an h sheaf on `Sch/S` which is
  limit preserving is a sheaf for the V topology.  Stacks 0ETR,
  `AlgebraicGeometry.isPHCovering_iff_isVCovering`, is what converts the two readings.
* `AlgebraicGeometry.exists_isVSheaf_extension_of_isSheaf_of_preservesAffineLimits` — the three
  properties of the extension, for a functor on `Scheme`: it is an h sheaf, is limit preserving,
  and is a sheaf for the V topology.  The conclusion of Stacks 0EV3 is granted as `h0EV3` and no
  uniqueness is claimed, so this is not a registration of the remark.

## Implementation notes

### The composition on `Scheme`

The remark asserts no new proposition: it composes two cited results, and the composition is
written out here as the single existential statement they jointly give, in the style of
`StacksFrontier/AlgebraicGeometry/FundamentalGroup/GaloisCategories/FiniteGSetsForget.lean`.

Only one of the two cited results is available in the shape that composition needs.  Stacks 0EVQ
is proved, as `AlgebraicGeometry.isVSheaf_of_isSheafFor_vCovering_of_isLimitPreserving`, and
supplies the V sheaf property.  Stacks 0EV3 is proved too, but on `Sch/S` and in the ph reading
of an h covering — see `AlgebraicGeometry.ExtendingFunctors.isHSheaf_extension` and
`AlgebraicGeometry.ExtendingFunctors.isLimitPreserving_extension` — which is not what the library's
Stacks 0EVQ consumes, so for this composition the conclusion of Stacks 0EV3 is carried as the
granted `h0EV3`; that is why this statement is left unregistered.

Two readings in the granted hypothesis differ from the source, both forced by the library's form
of Stacks 0EVQ.  First, the extension is a functor on all schemes rather than on the schemes
over `S`: the library's Stacks 0EVQ is stated for a presheaf on `Scheme`, the base of the source
being absent there, and a presheaf on `Over S` does not induce one on `Scheme`.  Second, its h
sheaf condition is read through V coverings.  An h covering is a family of morphisms locally of
finite presentation satisfying one of the two equivalent conditions of Stacks 0ETR;
`AlgebraicGeometry.IsHCovering` fixes the ph reading, while the library's Stacks 0EVQ consumes the
V reading.  The granted hypothesis is stated in the V reading because that is what the library's
Stacks 0EVQ consumes, and since a ph covering is a V covering,
`AlgebraicGeometry.isVCovering_of_isPHCovering`, the V reading implies the ph one, which is why
the conclusion below can state (a) with `AlgebraicGeometry.IsHCovering` without appealing to
Stacks 0ETR at all.

Uniqueness of the extension is **not** claimed by that composition.  The source remark says that
`F` extends uniquely, but the statement of Stacks 0EV3 asserts only that the extension has
properties (a) and (b); uniqueness is the content of Stacks 0EUW, whose uniqueness
statements `AlgebraicGeometry.ExtendingFunctors.extension_hom_unique` and
`AlgebraicGeometry.ExtendingFunctors.extension_iso_unique` are about functors on `Over S` and
the Zariski sheaf condition there, and so do not apply to the functor on all schemes produced
here.  Claiming uniqueness there would need a second granted hypothesis; it is claimed instead,
unconditionally, on `Sch/S`, by `exists_unique_isHSheaf_extension` below.

The colimit condition on `F` is spelled out as
`AlgebraicGeometry.BigHOver.PreservesAffineLimits`, which transcribes condition (b) of
Stacks 0EUW for the big h category over `S`: it is the analogue, for that category, of
`AlgebraicGeometry.ExtendingFunctors.PreservesAffineLimitsOnSubcategory`, with the limit taken
in schemes, as in the source's `T = lim T_i`.

### The extension on `Sch/S`

Existence is Stacks 0EV3, proved as
`AlgebraicGeometry.ExtendingFunctors.isHSheaf_extension` and
`AlgebraicGeometry.ExtendingFunctors.isLimitPreserving_extension`, together with the
identification `AlgebraicGeometry.ExtendingFunctors.nonempty_restrictionIso` of the restriction
of the extension with `F`.  Uniqueness is Stacks 0EUW, proved as
`AlgebraicGeometry.ExtendingFunctors.exists_unique_extension`: two functors on `Sch/S` which are
Zariski sheaves, are limit preserving and restrict to `F` are isomorphic, and an h sheaf is a
Zariski sheaf.  Nothing is granted there; that statement has no hypothesis beyond the data of
the source.

The index universe of the coverings is `v` in the h sheaf property of the extension and `u` in
the h sheaf property assumed of a competing extension: the first is the conclusion, stated for
coverings indexed in an arbitrary universe, and the second is a hypothesis, assumed only for
coverings indexed in the universe of the schemes, which is all the uniqueness argument consumes.

The V sheaf property of the extension is stated for coverings indexed in the same arbitrary
universe `v`.  The relative Stacks 0EVQ delivers it for coverings indexed in `Type (max u v)`,
its proof reindexing a covering into the universe of the schemes;
`AlgebraicGeometry.ExtendingFunctors.IsVSheafOver.ulift` brings that back down, a family and its
universe lift generating the same presieve and the sheaf condition depending only on the
presieve.

`exists_unique_isHSheaf_isVSheaf_extension` carries the `@[stacks 0EVR]` registration.  It is
none of the results it assembles: Stacks 0EV3 asserts properties (a) and (b) of *the* extension
supplied by Stacks 0EUW and asserts no uniqueness, Stacks 0EUW is the Zariski statement of which
this is the h corollary, and Stacks 0EVQ is the V sheaf criterion.  Each of those is registered
on its own covering set — Stacks 0EV3 on the two results named above, Stacks 0EUW across
`StacksFrontier/AlgebraicGeometry/Topologies/ExtendingFunctors.lean`,
`StacksFrontier/AlgebraicGeometry/Topologies/ExtendingFunctorsSheaf.lean` and
`StacksFrontier/AlgebraicGeometry/Topologies/ExtendingFunctorsLimits.lean` — and what is left, the
assertion of this remark, is what that statement says: in the source's own shape and with no
further input, `F` extends to a functor on all schemes over `S` with properties (a) and (b)
which is also a sheaf for the V topology, and that functor is unique up to isomorphism.

## The V sheaf property

Stacks 0EVR closes by combining the extension with Stacks 0EVQ to conclude that `F'` also
satisfies the sheaf property for the V topology.  On `Sch/S` that step is
`AlgebraicGeometry.ExtendingFunctors.isVSheafOver_of_isHSheaf_of_preservesAffineLimits`, and it
needs three things, all of them theorems of this library.

* The relative form of Stacks 0EVQ, for a functor on the schemes over `S`, is proved as
  `AlgebraicGeometry.ExtendingFunctors.isVSheafOver_of_isSheafFor_vCovering_of_isLimitPreserving`
  in `StacksFrontier/AlgebraicGeometry/ProEtale/IndEtale/VTopologySheafCriterionOver.lean`, over the
  covering vocabulary `AlgebraicGeometry.ExtendingFunctors.IsVCoveringOver` and
  `AlgebraicGeometry.ExtendingFunctors.IsVSheafOver` of
  `StacksFrontier/AlgebraicGeometry/Topologies/V/CoveringsOver.lean`.  It is proved in the slice
  rather than transported from the absolute case
  `AlgebraicGeometry.isVSheaf_of_isSheafFor_vCovering_of_isLimitPreserving`, and that is not a
  matter of taste: a functor on `Sch/S` is not the restriction of a functor on `Scheme`, the
  forgetful functor `Over S ⥤ Scheme` being neither full nor faithful on the fibres, and
  transport would ask for `Hom(-, S)` to be a V sheaf, while already `Hom(-, 𝔸¹)` is the
  presheaf of global functions and is not even an h sheaf —
  `AlgebraicGeometry.not_isSheafFor_isHCovering_gamma` and
  `AlgebraicGeometry.BigHOver.not_subcanonical_topology` in
  `StacksFrontier/AlgebraicGeometry/Topologies/HTopology/StructureSheafFailure.lean`.
* The limit preserving condition is read in two shapes in this library, and they agree.  The
  extension satisfies `AlgebraicGeometry.ExtendingFunctors.PreservesAffineLimits`, which tests
  the inverse systems indexed by the opposite of a nonempty directed poset, while the relative
  Stacks 0EVQ consumes `AlgebraicGeometry.Scheme.IsLimitPreserving`, which tests every cofiltered
  inverse system — the systems Stacks 0EVP produces being presented as cofiltered categories.
  `AlgebraicGeometry.Scheme.isLimitPreserving_of_preservesAffineLimits` in
  `StacksFrontier/AlgebraicGeometry/Topologies/ExtendingFunctorsCofilteredLimits.lean` identifies the
  two, by the cofinality theorem of Stacks 0032: a cofiltered category receives an initial functor
  from the opposite of a nonempty directed poset, restriction along it preserves and reflects
  limit cones, and the corresponding functor into the opposite category is final, so the colimit
  over the restricted system computes the colimit over the original one.
* The two readings of an h covering agree.  Stacks 0ETS defines an h covering to be a family of
  morphisms locally of finite presentation satisfying either of the two equivalent conditions of
  Stacks 0ETR, being a ph covering or being a V covering.
  `AlgebraicGeometry.IsHCovering` fixes the ph reading, so conclusion (a) above is the sheaf
  condition for the families which are locally of finite presentation and ph coverings, while
  the relative Stacks 0EVQ consumes it for the families which are locally of finite presentation
  and V coverings.  A ph covering is a V covering,
  `AlgebraicGeometry.isVCovering_of_isPHCovering`, so the class consumed is the *larger* one and
  the implication needed is the converse, Stacks 0ETR, which this library proves as
  `AlgebraicGeometry.isPHCovering_iff_isVCovering` in
  `StacksFrontier/AlgebraicGeometry/Topologies/V/PhVFlatteningModification.lean`, through the
  Raynaud–Gruson flattening theorem of Stacks 0815 and, below it, Stacks 0811.

It is the third of those that carries the mathematical content, and it is not an artefact of the
reduction.  The argument for Stacks 0EVQ consumes the sheaf condition at exactly two kinds of
family: open coverings, which are h coverings, and the stages `{Spec A_i → Spec R}` of the
presentation of a standard V covering of affines as a directed limit, which is Stacks 0EVP.
Those stages are of finite presentation and are standard V coverings, and that is all; in the
source they are h coverings *by definition*, since Stacks 0ETS reads an h covering through V
coverings.  Under the ph reading they are coverings only by
`AlgebraicGeometry.standardVCoveringHasPHRefinement`, which refines a standard V covering of an
affine scheme by a standard ph covering; the singleton case of that statement is exactly what
this step needs, and refining the stage presieve by a ph covering instead asks for the same
thing, a ph covering of `Spec R` factoring through `Spec A_i`.

## References

* [Stacks Project, Tag 0EVR](https://stacks.math.columbia.edu/tag/0EVR)
* [Stacks Project, Tag 0EV3](https://stacks.math.columbia.edu/tag/0EV3)
* [Stacks Project, Tag 0EVQ](https://stacks.math.columbia.edu/tag/0EVQ)
* [Stacks Project, Tag 0EVP](https://stacks.math.columbia.edu/tag/0EVP)
* [Stacks Project, Tag 0EUW](https://stacks.math.columbia.edu/tag/0EUW)
* [Stacks Project, Tag 0ETS](https://stacks.math.columbia.edu/tag/0ETS)
* [Stacks Project, Tag 0ETR](https://stacks.math.columbia.edu/tag/0ETR)
* [Stacks Project, Tag 0ETM](https://stacks.math.columbia.edu/tag/0ETM)
* [Stacks Project, Tag 0815](https://stacks.math.columbia.edu/tag/0815)
* [Stacks Project, Tag 0811](https://stacks.math.columbia.edu/tag/0811)
* [Stacks Project, Tag 05LX](https://stacks.math.columbia.edu/tag/05LX)
* [Stacks Project, Tag 0032](https://stacks.math.columbia.edu/tag/0032)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

namespace AlgebraicGeometry

section Composition

universe u v w

namespace BigHOver

/-- **Condition (b) of Stacks 0EUW for the big h category over `S`.** A presheaf of sets on the
big h category over `S` *preserves affine limits* when, for every inverse system of objects
with affine underlying scheme indexed by the opposite of a nonempty directed poset whose
underlying system of schemes has a limit cone in the system's own cone, the values of the
presheaf form a filtered colimit.

This is the hypothesis `F(T) = colim F(T_i)`, for `T = lim T_i` a directed limit of affine
schemes in the big h category over `S`, of Stacks 0EVR. -/
def PreservesAffineLimits (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigHOver B S hS)ᵒᵖ ⥤ Type w) : Prop :=
  ∀ (Λ : Type u) [PartialOrder Λ] [Nonempty Λ] [IsDirectedOrder Λ]
    (D : Λᵒᵖ ⥤ BigHOver B S hS) (_ : ∀ l, IsAffine ((toScheme B S hS).obj (D.obj l)))
    (c : Cone D) (_ : IsLimit ((toScheme B S hS).mapCone c)),
    Nonempty (IsColimit (F.mapCocone c.op))

end BigHOver

/-- **The composition of Stacks 0EV3 with Stacks 0EVQ, on `Scheme`.** Let `S` be a scheme
contained in a big h site and let `F` be a sheaf of sets on the big h category `(Sch/S)_h` whose
values on a directed inverse limit of affine objects form the filtered colimit of its values on
the system.  Then, once the conclusion of Stacks 0EV3 is granted as `h0EV3`, `F` extends to a
contravariant functor `F'` on schemes which satisfies the sheaf property for the h topology, is
limit preserving in the sense of Stacks 05LX over every base, and satisfies the sheaf property
for the V topology.

The first two properties are `h0EV3`; the third is obtained from them by Stacks 0EVQ,
`AlgebraicGeometry.isVSheaf_of_isSheafFor_vCovering_of_isLimitPreserving`.  Uniqueness of the
extension, which the source remark also records, is not claimed.

This statement carries no Stacks tag: it assumes the conclusion of one of the two results
Stacks 0EVR cites, in a shape stronger than what the library's Stacks 0EV3 proves, so it does not
register that remark.  Stacks 0EVR is registered on
`AlgebraicGeometry.ExtendingFunctors.exists_unique_isHSheaf_isVSheaf_extension` below, which
proves every assertion of the remark with nothing granted; this statement is kept as the record
of how far the composition the remark describes goes.  See the implementation notes of this
file. -/
theorem exists_isVSheaf_extension_of_isSheaf_of_preservesAffineLimits
    (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigHOver B S hS)ᵒᵖ ⥤ Type w)
    (hF : Presieve.IsSheaf (BigHOver.topology B S hS) F)
    (hcolim : BigHOver.PreservesAffineLimits.{u, w} B S hS F)
    (h0EV3 : ∀ G : (BigHOver B S hS)ᵒᵖ ⥤ Type w,
      Presieve.IsSheaf (BigHOver.topology B S hS) G →
      BigHOver.PreservesAffineLimits.{u, w} B S hS G →
      ∃ G' : Scheme.{u}ᵒᵖ ⥤ Type w,
        Nonempty ((BigHOver.toScheme B S hS).op ⋙ G' ≅ G) ∧
        (∀ (T : Scheme.{u}) (I : Type (max u v)) (X : I → Scheme.{u}) (g : ∀ i, X i ⟶ T),
          (∀ i, LocallyOfFinitePresentation (g i)) → IsVCovering X g →
            (Presieve.ofArrows X g).IsSheafFor G') ∧
        ∀ Y : Scheme.{u}, Scheme.IsLimitPreserving Y ((Over.forget Y).op ⋙ G')) :
    ∃ F' : Scheme.{u}ᵒᵖ ⥤ Type w,
      Nonempty ((BigHOver.toScheme B S hS).op ⋙ F' ≅ F) ∧
      (∀ (T : Scheme.{u}) (I : Type (max u v)) (X : I → Scheme.{u}) (g : ∀ i, X i ⟶ T),
        IsHCovering X g → (Presieve.ofArrows X g).IsSheafFor F') ∧
      (∀ Y : Scheme.{u}, Scheme.IsLimitPreserving Y ((Over.forget Y).op ⋙ F')) ∧
      IsVSheaf.{u, max u v, w} F' := by
  obtain ⟨F', hiso, hV, hLP⟩ := h0EV3 F hF hcolim
  exact ⟨F', hiso,
    fun T I X g hg ↦ hV T I X g hg.1 (isVCovering_of_isPHCovering X g hg.2), hLP,
    isVSheaf_of_isSheafFor_vCovering_of_isLimitPreserving.{u, v, w} F' hV hLP⟩

end Composition

namespace ExtendingFunctors

section Unconditional

universe w u v

variable {S : Scheme.{u}}

/-- **An h sheaf on `Sch/S` is a Zariski sheaf.** A covering of an object of `Sch/S` by open
subobjects is an fppf covering, and an fppf covering is an h covering, so the Zariski sheaf
condition is the h sheaf condition read at those coverings. -/
theorem isZariskiSheaf_of_isHSheaf {G : (Over S)ᵒᵖ ⥤ Type w} (hG : IsHSheaf.{w, u, u} G) :
    IsZariskiSheaf G :=
  isZariskiSheaf_of_isCoveringSheaf .fppf fun X Y f hf ↦
    hG X Y f (isHCoveringOver_of_mem_coveringPrecoverage_fppf Y f hf)

/-- The extension of `F` is isomorphic to any h sheaf restricting to `F` which is limit
preserving. -/
private theorem extension_iso_of_isHSheaf {P : ObjectProperty (Over S)}
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    {F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1))}
    (hF : IsHCoveringSheafOnSubcategory.{max w (u + 1), u, u} P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F)
    (F'' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))) (hs'' : IsHSheaf.{max w (u + 1), u, u} F'')
    (hb'' : PreservesAffineLimits F'') (β : P.ι.op ⋙ F'' ≅ F) :
    Nonempty (extension P F ≅ F'') := by
  have haF : IsZariskiSheafOnSubcategory P F :=
    isZariskiSheafOnSubcategory_of_isHCoveringSheafOnSubcategory hP1 hF
  obtain ⟨F₀, -, -, -, huniq⟩ := exists_unique_extension hP1 hP2 haF hbF
  obtain ⟨e₁⟩ := huniq (extension P F) (isZariskiSheaf_extension P F hP1 hP2 haF)
    (preservesAffineLimits_extension F hP1 hP2 haF)
    (nonempty_restrictionIso F hP1 hP2 haF hbF).some
  obtain ⟨e₂⟩ := huniq F'' (isZariskiSheaf_of_isHSheaf hs'') hb'' β
  exact ⟨e₁.symm.trans e₂⟩

/-- **The extension of an h sheaf on `Sch/S`, with its uniqueness and without the V clause.**
Let `S` be a scheme, let `P` be a full subcategory of `Sch/S` satisfying conditions (1) and (2)
of Stacks 0EUW and let `F : Pᵒᵖ ⥤ Set` be an h sheaf whose values on a directed inverse limit of
affine objects form the filtered colimit of its values on the system. Then `F` extends to a
contravariant functor `F'` on all schemes over `S` which satisfies the sheaf property for the h
topology and is limit preserving in the sense of Stacks 05LX, and any functor on `Sch/S` with
those two properties restricting to `F` is isomorphic to `F'`.

Properties (a) and (b) of the extension are Stacks 0EV3, `isHSheaf_extension` and
`isLimitPreserving_extension`, and the uniqueness is Stacks 0EUW,
`exists_unique_extension`.

**No `@[stacks 0EVR]` attribute is attached.** This statement omits one assertion of that
remark, that `F'` is also a sheaf for the V topology.  The registration sits on
`exists_unique_isHSheaf_isVSheaf_extension` below, which proves every assertion of the remark
including that one.  This statement is kept as the record of how much of the remark is reached
without Stacks 0ETR. -/
theorem exists_unique_isHSheaf_extension (P : ObjectProperty (Over S))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hF : IsHCoveringSheafOnSubcategory.{max w (u + 1), u, u} P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F) :
    ∃ (F' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))) (_ : IsHSheaf.{max w (u + 1), u, v} F')
      (_ : PreservesAffineLimits F') (_ : P.ι.op ⋙ F' ≅ F),
      ∀ F'' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1)), IsHSheaf.{max w (u + 1), u, u} F'' →
        PreservesAffineLimits F'' → (P.ι.op ⋙ F'' ≅ F) → Nonempty (F' ≅ F'') := by
  have haF : IsZariskiSheafOnSubcategory P F :=
    isZariskiSheafOnSubcategory_of_isHCoveringSheafOnSubcategory hP1 hF
  refine ⟨extension P F, isHSheaf_extension P F hP1 hP2 hF hbF,
    isLimitPreserving_extension P F hP1 hP2 hF,
    (nonempty_restrictionIso F hP1 hP2 haF hbF).some, fun F'' hs'' hb'' β ↦
    extension_iso_of_isHSheaf hP1 hP2 hF hbF F'' hs'' hb'' β⟩

/-! ### The V sheaf property of an h sheaf on `Sch/S` -/

/-- **An h sheaf on `Sch/S` which is limit preserving is a V sheaf.** This is Stacks 0EVQ read
through the ph form of an h covering: the sheaf condition the relative Stacks 0EVQ consumes is
the one for the families locally of finite presentation which are V coverings, and
`AlgebraicGeometry.isHCovering_iff_isVCovering` identifies those with the h coverings in the ph
reading fixed by `AlgebraicGeometry.IsHCovering`.

That identification is Stacks 0ETR, which is a theorem of this development; nothing is granted
here.  Limit preservation is consumed by the relative Stacks 0EVQ in the cofiltered reading of
Remark 05LX and supplied here in the directed reading, the two being identified by
`AlgebraicGeometry.Scheme.isLimitPreserving_of_preservesAffineLimits`. -/
theorem isVSheafOver_of_isHSheaf_of_preservesAffineLimits
    (G : (Over S)ᵒᵖ ⥤ Type w)
    (hG : IsHSheaf.{w, u, max u v} G) (hbG : PreservesAffineLimits G) :
    IsVSheafOver.{w, u, v} G :=
  IsVSheafOver.ulift.{w, u, v}
    (isVSheafOver_of_isSheafFor_vCovering_of_isLimitPreserving.{w, u, v} G
      (fun T _ X g hlfp hV ↦ hG T X g ((isHCovering_iff_isVCovering _ _).2 ⟨hlfp, hV⟩))
      (Scheme.isLimitPreserving_of_preservesAffineLimits hbG))

/-- **Stacks 0EVR.** Let `S` be a scheme, let `P` be a full subcategory of `Sch/S` satisfying
conditions (1) and (2) of Stacks 0EUW and let `F : Pᵒᵖ ⥤ Set` be an h sheaf whose values on a
directed inverse limit of affine objects form the filtered colimit of its values on the system.
Then `F` extends to a contravariant functor `F'` on all schemes over `S` which satisfies the
sheaf property for the h topology, is limit preserving in the sense of Stacks 05LX and satisfies
the sheaf property for the V topology, and any functor on `Sch/S` which is an h sheaf, is limit
preserving and restricts to `F` is isomorphic to `F'`.

This is the whole of the remark, the V clause included.  Properties (a) and (b) of the extension
are Stacks 0EV3, `isHSheaf_extension` and `isLimitPreserving_extension`; the
uniqueness is Stacks 0EUW, `exists_unique_extension`; and the V sheaf property is
Stacks 0EVQ read through Stacks 0ETR, by
`isVSheafOver_of_isHSheaf_of_preservesAffineLimits`. -/
@[stacks 0EVR "the whole of the remark: the extension of an h sheaf on the big h category over \
`S` which carries a directed inverse limit of affine objects to a filtered colimit, together \
with its uniqueness and every property the remark asserts of it. The extension is an h sheaf on \
all schemes over `S`, is limit preserving in the sense of Stacks 05LX, satisfies the sheaf \
property for the V topology, restricts to the given functor, and is the only functor which is \
an h sheaf, is limit preserving and restricts to it, up to isomorphism"]
theorem exists_unique_isHSheaf_isVSheaf_extension
    (P : ObjectProperty (Over S))
    (hP1 : HasAffineOpens P) (hP2 : HasFinitePresentationAffines P)
    (F : P.FullSubcategoryᵒᵖ ⥤ Type (max w (u + 1)))
    (hF : IsHCoveringSheafOnSubcategory.{max w (u + 1), u, u} P F)
    (hbF : PreservesAffineLimitsOnSubcategory P F) :
    ∃ (F' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1))) (_ : IsHSheaf.{max w (u + 1), u, v} F')
      (_ : PreservesAffineLimits F') (_ : IsVSheafOver.{max w (u + 1), u, v} F')
      (_ : P.ι.op ⋙ F' ≅ F),
      ∀ F'' : (Over S)ᵒᵖ ⥤ Type (max w (u + 1)), IsHSheaf.{max w (u + 1), u, u} F'' →
        PreservesAffineLimits F'' → (P.ι.op ⋙ F'' ≅ F) → Nonempty (F' ≅ F'') := by
  have haF : IsZariskiSheafOnSubcategory P F :=
    isZariskiSheafOnSubcategory_of_isHCoveringSheafOnSubcategory hP1 hF
  refine ⟨extension P F, isHSheaf_extension.{w, u, v} P F hP1 hP2 hF hbF,
    isLimitPreserving_extension P F hP1 hP2 hF,
    isVSheafOver_of_isHSheaf_of_preservesAffineLimits.{max w (u + 1), u, v} (extension P F)
      (isHSheaf_extension.{w, u, max u v} P F hP1 hP2 hF hbF)
      (isLimitPreserving_extension P F hP1 hP2 hF),
    (nonempty_restrictionIso F hP1 hP2 haF hbF).some, fun F'' hs'' hb'' β ↦
    extension_iso_of_isHSheaf hP1 hP2 hF hbF F'' hs'' hb'' β⟩

end Unconditional

end ExtendingFunctors

end AlgebraicGeometry

end
