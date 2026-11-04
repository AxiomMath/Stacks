module

public import StacksFrontier.AlgebraicGeometry.Descent.AffineFpqcFamilyEffective
public import StacksFrontier.AlgebraicGeometry.Descent.DescendingTypesOfMorphisms
public import StacksFrontier.AlgebraicGeometry.Descent.FamilyEffectivityLargeIndex
public import StacksFrontier.AlgebraicGeometry.Topologies.ExtendingFunctorsStandardTopologies
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Descending types of morphisms over an arbitrary base

Let `P` be a property of morphisms of schemes over a base which is stable under any base change
and preserved by finite disjoint unions, and let `τ` be one of fpqc, fppf, étale, smooth and
syntomic. If every descent datum relative to a surjective morphism of affine schemes which is
flat, flat of finite presentation, étale, smooth or syntomic according to `τ`, and whose member
has `P`, is effective, then every descent datum relative to a `τ`-covering of *any* scheme whose
members have `P` is effective.

This is the general-base half of Stacks 02W3; the base is no longer assumed affine.

## Main results

* `AlgebraicGeometry.PreZeroHypercover.mem_precoverage_restrictBase`: the restriction of a
  covering family to an open of the base is a covering family of that open, for the precoverage
  attached to any morphism property stable under base change.
* `AlgebraicGeometry.Scheme.precoverage_coveringMorphismProperty_le_fpqcPrecoverage`: the
  coverings of any of the five standard topologies are fpqc coverings.
* `AlgebraicGeometry.DescentData.isFamilyEffective_of_affineSingleton` and
  `AlgebraicGeometry.DescentData.isFamilyEffective_of_affineSingleton_of_anyIndex`:
  **Stacks 02W3 over an arbitrary base, for the fppf, étale, smooth and syntomic coverings**,
  for a covering family indexed in the universe of the schemes and in an arbitrary universe.
* `AlgebraicGeometry.DescentData.isFamilyEffective_fpqc_of_affineSingleton` and
  `AlgebraicGeometry.DescentData.isFamilyEffective_fpqc_of_affineSingleton_of_anyIndex`:
  **Stacks 02W3 over an arbitrary base, for the fpqc coverings**, likewise.

## Implementation notes

The reduction to the affine base is the gluing argument of the source, which is already
available in the form the source uses it: the schemes charting the datum over the affine opens
of the base glue, and the glued scheme charts the datum, provided only that the datum restricted
to each affine open of the base is effective. That is
`AlgebraicGeometry.DescentData.nonempty_chart_of_restrictBase_isFamilyEffective`, whose proof
runs through the full faithfulness of Stacks 02W0 for the restriction morphisms and Stacks 01LH
for the gluing. So all that is done here is to supply its hypothesis from the affine-base case
of the tag, which applies because the restriction of a `τ`-covering family to an open of the
base is again a `τ`-covering family of that open and the components of the restricted datum are
base changes of the original ones.

The gluing argument is stated for an fpqc covering family, so for the four topologies other
than fpqc the given covering family has to be recognised as an fpqc covering family: every
covering morphism of the five topologies is flat and locally of finite presentation, so the
family is an fppf covering family, and fppf covering families are fpqc covering families.

Each statement is proved first for a covering family indexed in the universe of the schemes,
which is what the affine-base case is stated for: its refinement step and the pullback functor
of Stacks 02VS both pass through the disjoint union of the family, and a family indexed by a
type that is not `u`-small has no disjoint union in `Scheme.{u}`. The restriction is then removed
by `AlgebraicGeometry.DescentData.isFamilyEffective_of_forall_reindex`, which reduces effectivity
along an fpqc covering family in any index universe to effectivity along its `u`-small covering
subfamilies, so that the source's own convention — a covering indexed by a set — is met. For the
four topologies other than fpqc a subfamily has to be recognised as a `τ`-covering again, which
it is: it is jointly surjective because it is an fpqc covering, and its members are members of
the original family.

## References

* [Stacks Project, Tag 01LH](https://stacks.math.columbia.edu/tag/01LH)
* [Stacks Project, Tag 02W0](https://stacks.math.columbia.edu/tag/02W0)
* [Stacks Project, Tag 02W3](https://stacks.math.columbia.edu/tag/02W3)
-/

@[expose] public section

noncomputable section

universe u v

namespace AlgebraicGeometry

open CategoryTheory CategoryTheory.Limits MorphismOfSchemeFamilies

/-- **The restriction of a covering family to an open of the base is a covering family of that
open.** Each member of the restricted family is a base change of the corresponding member of the
original one, and the precoverage attached to a morphism property stable under base change is
stable under base change. -/
lemma PreZeroHypercover.mem_precoverage_restrictBase {S : Scheme.{u}}
    (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange]
    (𝒰 : PreZeroHypercover.{u} S) (U : S.Opens)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.precoverage P S) :
    (PreZeroHypercover.restrictBase 𝒰 U).presieve₀ ∈ Scheme.precoverage P U.toScheme :=
  Precoverage.mem_coverings_of_isPullback 𝒰.f h𝒰 U.ι _ (fun i ↦ (𝒰.f i ⁻¹ᵁ U).ι)
    fun i ↦ isPullback_morphismRestrict (𝒰.f i) U

/-- **The coverings of any of the five standard topologies are fpqc coverings.** Every covering
morphism is flat and locally of finite presentation, so such a covering family is an fppf
covering family. -/
@[sga "3 XI 6.8" "more general"]
theorem Scheme.precoverage_coveringMorphismProperty_le_fpqcPrecoverage (τ : CoveringTopology) :
    Scheme.precoverage (coveringMorphismProperty.{u} τ) ≤ Scheme.fpqcPrecoverage := by
  refine le_trans ?_ Scheme.fppfPrecoverage_le_fpqcPrecoverage
  cases τ with
  | fppf => exact le_rfl
  | syntomic => exact Scheme.syntomicPrecoverage_le_fppfPrecoverage
  | smooth => exact Scheme.smoothPrecoverage_le_fppfPrecoverage
  | etale => exact Scheme.etalePrecoverage_le_fppfPrecoverage
  | zariski => exact Scheme.zariskiPrecoverage_le_fppfPrecoverage

namespace DescentData

variable {P : MorphismProperty Scheme.{u}}

/-- **Stacks Project, Tag 02W3, for the fppf, étale, smooth and syntomic coverings.** Let `P` be
a property of morphisms of schemes over a base which is stable under any base change and such
that a nonempty finite disjoint union of morphisms with `P` again has `P`. Let `τ` be one of
fppf, étale, smooth and syntomic, and suppose that for every surjective morphism of affine
schemes which is flat of finite presentation, étale, smooth or syntomic according to `τ`, every
descent datum relative to it whose member has `P` is effective. Then every descent datum
relative to a `τ`-covering of an arbitrary scheme whose members have `P` is effective. -/
@[stacks 02W3 "for τ = fppf, étale, smooth and syntomic, over an arbitrary base, for a \
covering family indexed in the universe of the schemes"]
theorem isFamilyEffective_of_affineSingleton [P.IsStableUnderBaseChange]
    (τ : CoveringTopology) (hτ : τ ≠ .zariski)
    (hcoprod : ∀ {J : Type u} [Finite J] [Nonempty J] {Y Z : J → Scheme.{u}}
      (g : ∀ j, Y j ⟶ Z j), (∀ j, P (g j)) → P (Limits.Sigma.map g))
    (haffine : ∀ {A T : Scheme.{u}} [IsAffine A] [IsAffine T] (a : A ⟶ T),
      Surjective a → coveringMorphismProperty τ a →
      ∀ E : DescentDatum a, P (E.obj ()).hom → E.IsEffective)
    {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{u} S)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.precoverage (coveringMorphismProperty τ) S)
    (D : DescentData 𝒰.f) (hP : ∀ i, P (D.obj i).hom) :
    D.IsFamilyEffective := by
  have := ExtendingFunctors.isStableUnderBaseChange_coveringMorphismProperty.{u} τ
  refine (nonempty_chart_of_restrictBase_isFamilyEffective
    (Scheme.precoverage_coveringMorphismProperty_le_fpqcPrecoverage τ S h𝒰) D fun U ↦ ?_).elim
      fun C ↦ C.isFamilyEffective
  have : IsAffine U.1.toScheme := U.2
  exact isFamilyEffective_affineBase_of_affineSingleton τ hτ hcoprod haffine
    (PreZeroHypercover.restrictBase 𝒰 U.1)
    (PreZeroHypercover.mem_precoverage_restrictBase _ 𝒰 U.1 h𝒰) _
    fun i ↦ restrictBase_prop_obj 𝒰 U.1 D i (hP i)

/-- **Stacks Project, Tag 02W3, for the fpqc coverings.** Let `P` be a property of morphisms of
schemes over a base which is stable under any base change and such that a nonempty finite
disjoint union of morphisms with `P` again has `P`. Suppose that for every surjective flat
morphism of affine schemes, every descent datum relative to it whose member has `P` is
effective. Then every descent datum relative to an fpqc covering of an arbitrary scheme whose
members have `P` is effective. -/
@[stacks 02W3 "for τ = fpqc, over an arbitrary base, for a covering family indexed in the \
universe of the schemes"]
theorem isFamilyEffective_fpqc_of_affineSingleton [P.IsStableUnderBaseChange]
    (hcoprod : ∀ {J : Type u} [Finite J] [Nonempty J] {Y Z : J → Scheme.{u}}
      (g : ∀ j, Y j ⟶ Z j), (∀ j, P (g j)) → P (Limits.Sigma.map g))
    (haffine : ∀ {A T : Scheme.{u}} [IsAffine A] [IsAffine T] (a : A ⟶ T),
      Surjective a → Flat a → ∀ E : DescentDatum a, P (E.obj ()).hom → E.IsEffective)
    {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{u} S)
    (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData 𝒰.f) (hP : ∀ i, P (D.obj i).hom) :
    D.IsFamilyEffective := by
  refine (nonempty_chart_of_restrictBase_isFamilyEffective h𝒰 D fun U ↦ ?_).elim
    fun C ↦ C.isFamilyEffective
  have : IsAffine U.1.toScheme := U.2
  exact isFamilyEffective_affineBase_fpqc_of_affineSingleton hcoprod haffine
    (PreZeroHypercover.restrictBase 𝒰 U.1)
    (PreZeroHypercover.mem_fpqcPrecoverage_restrictBase 𝒰 U.1 h𝒰) _
    fun i ↦ restrictBase_prop_obj 𝒰 U.1 D i (hP i)

/-- **Stacks Project, Tag 02W3, for the fppf, étale, smooth and syntomic coverings, with no
restriction on the index type of the covering family.** Let `P` be a property of morphisms of
schemes over a base which is stable under any base change and such that a nonempty finite
disjoint union of morphisms with `P` again has `P`. Let `τ` be one of fppf, étale, smooth and
syntomic, and suppose that for every surjective morphism of affine schemes which is flat of
finite presentation, étale, smooth or syntomic according to `τ`, every descent datum relative to
it whose member has `P` is effective. Then every descent datum relative to a `τ`-covering of an
arbitrary scheme, indexed by a type in an arbitrary universe, whose members have `P` is
effective. -/
@[stacks 02W3 "for τ = fppf, étale, smooth and syntomic, over an arbitrary base, for a covering \
family indexed in an arbitrary universe"]
theorem isFamilyEffective_of_affineSingleton_of_anyIndex [P.IsStableUnderBaseChange]
    (τ : CoveringTopology) (hτ : τ ≠ .zariski)
    (hcoprod : ∀ {J : Type u} [Finite J] [Nonempty J] {Y Z : J → Scheme.{u}}
      (g : ∀ j, Y j ⟶ Z j), (∀ j, P (g j)) → P (Limits.Sigma.map g))
    (haffine : ∀ {A T : Scheme.{u}} [IsAffine A] [IsAffine T] (a : A ⟶ T),
      Surjective a → coveringMorphismProperty τ a →
      ∀ E : DescentDatum a, P (E.obj ()).hom → E.IsEffective)
    {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.precoverage (coveringMorphismProperty τ) S)
    (D : DescentData f) (hP : ∀ i, P (D.obj i).hom) :
    D.IsFamilyEffective := by
  refine isFamilyEffective_of_forall_reindex f
    (Scheme.precoverage_coveringMorphismProperty_le_fpqcPrecoverage τ S hf) D fun J m hm ↦ ?_
  -- A `u`-small covering subfamily is again a `τ`-covering: it is jointly surjective because it
  -- is an fpqc covering, and its members are members of the original family.
  have hmτ : Presieve.ofArrows (fun j ↦ X (m j)) (fun j ↦ f (m j)) ∈
      Scheme.precoverage (coveringMorphismProperty τ) S :=
    (Scheme.ofArrows_mem_precoverage_iff _).2
      ⟨((Scheme.ofArrows_mem_precoverage_iff _).1 hm.2).1,
        fun j ↦ ((Scheme.ofArrows_mem_precoverage_iff _).1 hf).2 (m j)⟩
  exact isFamilyEffective_of_affineSingleton τ hτ hcoprod haffine
    ⟨J, fun j ↦ X (m j), fun j ↦ f (m j)⟩ hmτ (D.reindex m) fun j ↦ hP (m j)

/-- **Stacks Project, Tag 02W3, for the fpqc coverings, with no restriction on the index type of
the covering family.** Let `P` be a property of morphisms of schemes over a base which is stable
under any base change and such that a nonempty finite disjoint union of morphisms with `P` again
has `P`. Suppose that for every surjective flat morphism of affine schemes, every descent datum
relative to it whose member has `P` is effective. Then every descent datum relative to an fpqc
covering of an arbitrary scheme, indexed by a type in an arbitrary universe, whose members have
`P` is effective. -/
@[stacks 02W3 "for τ = fpqc, over an arbitrary base, for a covering family indexed in an \
arbitrary universe"]
theorem isFamilyEffective_fpqc_of_affineSingleton_of_anyIndex [P.IsStableUnderBaseChange]
    (hcoprod : ∀ {J : Type u} [Finite J] [Nonempty J] {Y Z : J → Scheme.{u}}
      (g : ∀ j, Y j ⟶ Z j), (∀ j, P (g j)) → P (Limits.Sigma.map g))
    (haffine : ∀ {A T : Scheme.{u}} [IsAffine A] [IsAffine T] (a : A ⟶ T),
      Surjective a → Flat a → ∀ E : DescentDatum a, P (E.obj ()).hom → E.IsEffective)
    {I : Type v} {S : Scheme.{u}} {X : I → Scheme.{u}} (f : ∀ i, X i ⟶ S)
    (hf : Presieve.ofArrows X f ∈ Scheme.fpqcPrecoverage S)
    (D : DescentData f) (hP : ∀ i, P (D.obj i).hom) :
    D.IsFamilyEffective :=
  isFamilyEffective_of_forall_reindex f hf D fun J m hm ↦
    isFamilyEffective_fpqc_of_affineSingleton hcoprod haffine
      ⟨J, fun j ↦ X (m j), fun j ↦ f (m j)⟩ hm (D.reindex m) fun j ↦ hP (m j)

end DescentData

end AlgebraicGeometry

end

end
