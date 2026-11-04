module

public import Mathlib.AlgebraicGeometry.IdealSheaf.Functorial
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Fibre
public import StacksFrontier.AlgebraicGeometry.Curves.IsNode
public import StacksFrontier.AlgebraicGeometry.Curves.NodalLciUnramifiedCriterion
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.FittingIdealsDifferentials
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalRelativeDimensionOne
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.Equidimensional
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberCriterion
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.FiberDimension
public import StacksFrontier.AlgebraicGeometry.Morphisms.Syntomic.Properties
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.BaseChangeLocus
public import StacksFrontier.AlgebraicGeometry.Morphisms.Unramified.Properties
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Families of nodal curves

Tag 0C59 says that a morphism of schemes `f : X ⟶ S` is flat and locally of finite presentation
with every nonempty fibre equidimensional of dimension one and with at-worst-nodal singularities
exactly when it is syntomic of relative dimension one and the closed subscheme `Sing(f) ⊆ X` cut
out by the first Fitting ideal of `Ω_{X/S}` is unramified over `S`.  The second of those
conditions is `AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne`, the definition of Tag
0C5A; the first is `Stacks.Curves.HasAtWorstNodalFibresOfDimensionOne`, defined here.

The equivalence is proved by passing to the fibres: Tag 0C4E turns the nodal condition on a
fibre into the conjunction of its being a local complete intersection over the residue field
with the unramifiedness of its own singular subscheme, Tag 01UF recognises the resulting flat,
finitely presented morphism with local-complete-intersection fibres as syntomic, Tag 0C3I
identifies the singular subscheme of a fibre with the fibre of the singular subscheme, and Tag
02G8 detects unramifiedness of the latter on the fibres.

The last four steps are assembled into
`AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_iff_fibres`, which is the equivalence
with the nodal condition on the fibres read as condition (2) of Tag 0C4E; Tag 0C59 itself,
`Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff`, follows by applying Tag 0C4E
(`Stacks.Curves.hasAtWorstNodalSingularities_iff_lci_and_unramified_relativeSingularIdeal`) to
each fibre.

## Main definitions

* `Stacks.Curves.HasAtWorstNodalFibresOfDimensionOne` — condition (1) of Tag 0C59.

## Main results

* `AlgebraicGeometry.syntomic_iff_isLocalCompleteIntersection_fiber` — Tag 01UF as an
  equivalence: a flat morphism locally of finite presentation is syntomic exactly when its
  fibres are local complete intersections over their residue fields.
* `AlgebraicGeometry.relativeDimension_iff_forall_topologicalKrullDimAt` — having every nonempty
  fibre equidimensional of dimension `d` is the same as having local fibre dimension `d` at
  every point of the source.
* `AlgebraicGeometry.syntomicOfRelativeDimension_iff_flat_locallyOfFinitePresentation_lci_fibres`
  — syntomicity of relative dimension `d` read off the fibres.
* `AlgebraicGeometry.unramified_iff_unramified_fiberToSpecResidueField` — unramifiedness is
  detected on the fibres.
* `AlgebraicGeometry.relativeSingularIdeal_comap_fiberι` — Tag 0C3I on a fibre: the singular
  subscheme of a fibre is the fibre of the singular subscheme.
* `AlgebraicGeometry.unramified_relativeSingularIdeal_iff_fibres` — the singular subscheme is
  unramified over the base exactly when the singular subscheme of every fibre is unramified
  over its residue field.
* `AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_iff_fibres` — the equivalence with the
  nodal condition on the fibres read as condition (2) of Tag 0C4E.
* `Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff` — **Tag 0C59**.

## Implementation notes

`AlgebraicGeometry.relativeSingularIdeal` is the first Fitting ideal of `Ω_{X/S}` and
`Scheme.IdealSheafData.subschemeι` the inclusion of the closed subscheme it cuts out, so
`Sing(f) ⟶ S` is `(relativeSingularIdeal f).subschemeι ≫ f`.  A fibre is
`AlgebraicGeometry.Scheme.Hom.fiber` with its structure morphism
`AlgebraicGeometry.Scheme.Hom.fiberToSpecResidueField`, and the nodal condition on it is
`Stacks.Curves.HasAtWorstNodalSingularities` of Tag 0C47, which reads the structure morphism off
an `AlgebraicGeometry.Scheme.Over` instance; the instance supplied is always the fibre's own
structure morphism.

Equidimensionality of the fibres is phrased as in `AlgebraicGeometry.RelativeDimension` of Tag
02NJ — only nonempty fibres are constrained — while `SyntomicOfRelativeDimension` of Tag 02K2
constrains the local fibre dimension at every point of the *source*, which is vacuous over an
empty fibre. `AlgebraicGeometry.relativeDimension_iff_forall_topologicalKrullDimAt` is the
translation; it is `RelativeDimension` that is stated with the instance argument, so the
condition is spelled out in the main statements, which must not presuppose local finite type.

The fibre criteria for syntomicity and for unramifiedness are both read off base change of the
corresponding locus — `AlgebraicGeometry.syntomicLocus_eq_preimage` of Tag 02V3 and
`AlgebraicGeometry.unramifiedAt_iff_of_isPullback` of Tag 0475 — applied to the cartesian square
defining the fibre, so neither needs a local computation. In particular the unramified half is
obtained from Tag 0475 rather than from `AlgebraicGeometry.unramified_of_fibres`, whose
hypothesis is the explicit decomposition of the fibre of Tag 02G8.

Tag 0C4E is stated for a scheme carrying a `AlgebraicGeometry.Scheme.Over` instance over a base
field, equidimensional of dimension one and locally of finite type over that field.  Applying it
to a fibre therefore takes three inputs besides the fibre's structure morphism: the
equidimensionality and the dimension of the fibre, which clause (1) of Tag 0C59 provides for a
nonempty fibre and which clause (2) provides through
`AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_iff_fibres`, and local finite type of
the fibre's structure morphism, which comes from local finite presentation of `f` -- present in
both clauses -- through the instance
`AlgebraicGeometry.Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField`.  Over an empty fibre
condition (2) of Tag 0C4E holds vacuously, so no fibrewise input is needed there.

## References

* [Stacks Project, Tag 0C59](https://stacks.math.columbia.edu/tag/0C59)
* [Stacks Project, Tag 0C5A](https://stacks.math.columbia.edu/tag/0C5A)
* [Stacks Project, Tag 0C4E](https://stacks.math.columbia.edu/tag/0C4E)
* [Stacks Project, Tag 0C47](https://stacks.math.columbia.edu/tag/0C47)
* [Stacks Project, Tag 0C3I](https://stacks.math.columbia.edu/tag/0C3I)
* [Stacks Project, Tag 01UF](https://stacks.math.columbia.edu/tag/01UF)
* [Stacks Project, Tag 01UK](https://stacks.math.columbia.edu/tag/01UK)
* [Stacks Project, Tag 01UL](https://stacks.math.columbia.edu/tag/01UL)
* [Stacks Project, Tag 02G8](https://stacks.math.columbia.edu/tag/02G8)
* [Stacks Project, Tag 02K2](https://stacks.math.columbia.edu/tag/02K2)
* [Stacks Project, Tag 02NJ](https://stacks.math.columbia.edu/tag/02NJ)
* [Stacks Project, Tag 0475](https://stacks.math.columbia.edu/tag/0475)
* [Stacks Project, Tag 02V3](https://stacks.math.columbia.edu/tag/02V3)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The fibrewise criterion for syntomicity, in both directions -/

/-- A flat morphism locally of finite presentation is syntomic exactly when each of its fibres
is a local complete intersection over the residue field of its base point. -/
@[ega "IV 19.3.6"]
theorem syntomic_iff_isLocalCompleteIntersection_fiber {X S : Scheme.{u}} (f : X ⟶ S)
    [Flat f] [LocallyOfFinitePresentation f] :
    Syntomic f ↔
      ∀ s : S, IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField s) := by
  refine ⟨fun hf s y => ?_, syntomic_of_lci_fibers f⟩
  have hloc := syntomicLocus_eq_preimage (f.fiberι s) (f.fiberToSpecResidueField s) f
    (S.fromSpecResidueField s) (IsPullback.of_hasPullback ..)
  exact (Set.ext_iff.mp hloc y).mpr (hf (f.fiberι s y))

/-! ### Relative dimension read off the fibres pointwise -/

/-- Having every nonempty fibre equidimensional of dimension `d` is the same as having local
fibre dimension `d` at every point of the source. -/
theorem relativeDimension_iff_forall_topologicalKrullDimAt {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (d : ℕ) :
    RelativeDimension f d ↔
      ∀ x : X, topologicalKrullDimAt (f.fiber (f x)) (f.asFiber x) = (d : WithBot ℕ∞) := by
  constructor
  · intro hf x
    have := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f (f x)
    obtain ⟨heq, hdim⟩ := hf (f x) ⟨f.asFiber x⟩
    exact topologicalKrullDimAt_eq_of_equidimensional (S.residueField (f x))
      (f.fiber (f x)) (f.fiberToSpecResidueField (f x)) heq hdim (f.asFiber x)
  · intro hd s hs
    have := Scheme.Hom.locallyOfFiniteType_fiberToSpecResidueField f s
    have hlocal : ∀ w : f.fiber s, topologicalKrullDimAt (f.fiber s) w = (d : WithBot ℕ∞) := by
      intro w
      rw [← Scheme.Hom.topologicalKrullDimAt_fiber_fiberι f s w]
      exact hd (f.fiberι s w)
    refine ⟨equidimensional_of_topologicalKrullDimAt_eq (S.residueField s) (f.fiber s)
      (f.fiberToSpecResidueField s) hlocal, ?_⟩
    simp_rw [topologicalKrullDim_eq_iSup_localKrullDim, ← topologicalKrullDimAt_eq_localKrullDim,
      hlocal]
    have : Nonempty (f.fiber s) := hs
    exact iSup_const

/-! ### Syntomic of relative dimension one, read off the fibres -/

/-- The clauses of Tag 0C59 other than the nodal singularities of the fibres and the
unramifiedness of the singular subscheme. -/
theorem syntomicOfRelativeDimension_iff_flat_locallyOfFinitePresentation_lci_fibres
    {X S : Scheme.{u}} (f : X ⟶ S) (d : ℕ) :
    SyntomicOfRelativeDimension d f ↔
      (Flat f ∧ LocallyOfFinitePresentation f ∧
        (∀ s : S, Nonempty (f.fiber s) →
          Equidimensional (f.fiber s) ∧
            topologicalKrullDim (f.fiber s) = (d : WithBot ℕ∞)) ∧
        ∀ s : S, IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField s)) := by
  constructor
  · rintro ⟨hsyn, hdim⟩
    have hflat : Flat f := flat hsyn
    have hlfp : LocallyOfFinitePresentation f := locallyOfFinitePresentation hsyn
    exact ⟨hflat, hlfp, (relativeDimension_iff_forall_topologicalKrullDimAt f d).mpr hdim,
      (syntomic_iff_isLocalCompleteIntersection_fiber f).mp hsyn⟩
  · rintro ⟨hflat, hlfp, hrd, hlci⟩
    exact ⟨(syntomic_iff_isLocalCompleteIntersection_fiber f).mpr hlci,
      (relativeDimension_iff_forall_topologicalKrullDimAt f d).mp hrd⟩

/-! ### The fibrewise criterion for unramifiedness -/

/-- A composite of unramified morphisms is unramified: both halves of the characterization of
unramifiedness as local finite type together with formal unramifiedness are stable under
composition. -/
@[sga "1 I 3.5" "more general"]
theorem unramified_comp {A B C : Scheme.{u}} (i : A ⟶ B) (p : B ⟶ C) (hi : Unramified i)
    (hp : Unramified p) : Unramified (i ≫ p) := by
  rw [unramified_iff_locallyOfFiniteType_and_formallyUnramified]
  have hi' := (unramified_iff_locallyOfFiniteType_and_formallyUnramified i).mp hi
  have hp' := (unramified_iff_locallyOfFiniteType_and_formallyUnramified p).mp hp
  exact ⟨MorphismProperty.comp_mem @LocallyOfFiniteType _ _ hi'.1 hp'.1,
    MorphismProperty.comp_mem @FormallyUnramified _ _ hi'.2 hp'.2⟩

/-- An isomorphism is unramified. -/
theorem unramified_of_isIso {A B : Scheme.{u}} (e : A ⟶ B) [IsIso e] : Unramified e :=
  (unramified_iff_locallyOfFiniteType_and_formallyUnramified e).mpr ⟨inferInstance, inferInstance⟩

/-- Precomposition with an isomorphism does not affect unramifiedness. -/
theorem unramified_isoHom_comp_iff {A B C : Scheme.{u}} (e : A ≅ B) (p : B ⟶ C) :
    Unramified (e.hom ≫ p) ↔ Unramified p := by
  refine ⟨fun h => ?_, fun h => unramified_comp _ _ (unramified_of_isIso e.hom) h⟩
  simpa using unramified_comp e.inv (e.hom ≫ p) (unramified_of_isIso e.inv) h

/-- A morphism locally of finite type is unramified exactly when each of its fibres is
unramified over the residue field of its base point. -/
theorem unramified_iff_unramified_fiberToSpecResidueField {Z S : Scheme.{u}} (g : Z ⟶ S)
    [LocallyOfFiniteType g] :
    Unramified g ↔ ∀ s : S, Unramified (g.fiberToSpecResidueField s) := by
  constructor
  · exact fun hg s => ⟨fun y => (unramifiedAt_iff_of_isPullback
      (IsPullback.of_hasPullback g (S.fromSpecResidueField s)) y).mp (hg.unramifiedAt _)⟩
  · intro h
    exact ⟨fun z => Scheme.Hom.fiberι_asFiber g z ▸ (unramifiedAt_iff_of_isPullback
      (IsPullback.of_hasPullback g (S.fromSpecResidueField (g z))) (g.asFiber z)).mpr
        ((h (g z)).unramifiedAt (g.asFiber z))⟩

/-! ### The singular subscheme of a fibre -/

/-- The fibre of the closed subscheme cut out by an ideal sheaf is the closed subscheme cut out
by the inverse image of that ideal sheaf. -/
theorem isPullback_subschemeι_comap_fiberι {X S : Scheme.{u}} (f : X ⟶ S)
    (I : X.IdealSheafData) (s : S) :
    IsPullback ((I.comapIso (f.fiberι s)).hom ≫ pullback.snd _ _)
      ((I.comap (f.fiberι s)).subschemeι ≫ f.fiberToSpecResidueField s)
      (I.subschemeι ≫ f) (S.fromSpecResidueField s) := by
  have hp : IsPullback (f.fiberι s) (f.fiberToSpecResidueField s) f
      (S.fromSpecResidueField s) := IsPullback.of_hasPullback _ _
  have hz : ((I.comapIso (f.fiberι s)).hom ≫ pullback.snd _ _) ≫ I.subschemeι =
      (I.comap (f.fiberι s)).subschemeι ≫ f.fiberι s := by
    simp
  have hker : I.subschemeι.ker.comap (f.fiberι s) = (I.comap (f.fiberι s)).subschemeι.ker := by
    rw [I.ker_subschemeι]
    simp [Scheme.IdealSheafData.comap]
  have hp₁ : IsPullback (I.comap (f.fiberι s)).subschemeι
      ((I.comapIso (f.fiberι s)).hom ≫ pullback.snd _ _) (f.fiberι s) I.subschemeι :=
    isPullback_of_isClosedImmersion _ _ _ _ hz.symm hker
  simpa using (hp₁.paste_horiz hp.flip).flip

/-- **Stacks Project, Tag 0C3I, on a fibre.** The singular subscheme of a fibre is the fibre of
the singular subscheme: the first Fitting ideal of the relative differentials pulls back along
the fibre inclusion to the first Fitting ideal of the relative differentials of the fibre. -/
theorem relativeSingularIdeal_comap_fiberι {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] (s : S) :
    (relativeSingularIdeal f).comap (f.fiberι s) =
      relativeSingularIdeal (f.fiberToSpecResidueField s) :=
  fittingIdeal_relativeDifferentials_comap (f.fiberι s) (f.fiberToSpecResidueField s) f
    (S.fromSpecResidueField s) (IsPullback.of_hasPullback ..) 1

/-- The singular subscheme of a morphism is unramified over the base exactly when the singular
subscheme of every fibre is unramified over the residue field of its base point. -/
theorem unramified_relativeSingularIdeal_iff_fibres {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] :
    Unramified ((relativeSingularIdeal f).subschemeι ≫ f) ↔
      ∀ s : S, Unramified ((relativeSingularIdeal (f.fiberToSpecResidueField s)).subschemeι ≫
        f.fiberToSpecResidueField s) := by
  set I := relativeSingularIdeal f
  rw [unramified_iff_unramified_fiberToSpecResidueField (I.subschemeι ≫ f)]
  refine forall_congr' fun s => ?_
  have hp := isPullback_subschemeι_comap_fiberι f I s
  -- the two candidate fibres are isomorphic over `Spec κ(s)`
  have hsnd : hp.isoPullback.hom ≫ (I.subschemeι ≫ f).fiberToSpecResidueField s =
      (I.comap (f.fiberι s)).subschemeι ≫ f.fiberToSpecResidueField s :=
    hp.isoPullback_hom_snd
  rw [← relativeSingularIdeal_comap_fiberι f s, ← hsnd]
  exact (unramified_isoHom_comp_iff _ _).symm

/-! ### The fibrewise criterion with the nodal condition read through Tag 0C4E -/

/-- **The nodal criterion of Tag 0C59 with the nodal condition on the fibres read as condition
(2) of Tag 0C4E.**  A morphism of schemes is syntomic of relative dimension one with unramified
singular subscheme exactly when it is flat, locally of finite presentation, every nonempty fibre
is equidimensional of dimension one, and every fibre is a local complete intersection over the
residue field of its base point whose own singular subscheme is unramified over that field.

Tag 0C4E identifies the last condition on a fibre with its having at-worst-nodal singularities,
which turns this into Tag 0C59 itself:
`Stacks.Curves.hasAtWorstNodalFibresOfDimensionOne_iff`.

The syntomic half is Tag 01UF together with Tags 01UK and 01UL and the translation between the
two spellings of relative dimension one; the unramified half is Tag 0C3I together with the
fibrewise criterion for unramifiedness. -/
theorem isAtWorstNodalOfRelativeDimensionOne_iff_fibres {X S : Scheme.{u}} (f : X ⟶ S) :
    IsAtWorstNodalOfRelativeDimensionOne f ↔
      (Flat f ∧ LocallyOfFinitePresentation f ∧
        (∀ s : S, Nonempty (f.fiber s) →
          Equidimensional (f.fiber s) ∧
            topologicalKrullDim (f.fiber s) = (1 : WithBot ℕ∞)) ∧
        ∀ s : S, IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField s) ∧
          Unramified ((relativeSingularIdeal (f.fiberToSpecResidueField s)).subschemeι ≫
            f.fiberToSpecResidueField s)) := by
  constructor
  · rintro ⟨hsrd, hsing⟩
    obtain ⟨hflat, hlfp, hrd, hlci⟩ :=
      (syntomicOfRelativeDimension_iff_flat_locallyOfFinitePresentation_lci_fibres f 1).mp hsrd
    exact ⟨hflat, hlfp, hrd,
      fun s => ⟨hlci s, (unramified_relativeSingularIdeal_iff_fibres f).mp hsing s⟩⟩
  · rintro ⟨hflat, hlfp, hrd, hfib⟩
    exact ⟨(syntomicOfRelativeDimension_iff_flat_locallyOfFinitePresentation_lci_fibres f 1).mpr
        ⟨hflat, hlfp, hrd, fun s => (hfib s).1⟩,
      (unramified_relativeSingularIdeal_iff_fibres f).mpr fun s => (hfib s).2⟩

end AlgebraicGeometry

namespace Stacks.Curves

/-- **Condition (1) of Stacks Project, Tag 0C59.**  A morphism of schemes is flat, locally of
finite presentation, and every nonempty fibre is equidimensional of dimension one with
at-worst-nodal singularities.

The nodal condition on a fibre is `Stacks.Curves.HasAtWorstNodalSingularities` over the residue
field of the base point, taken with respect to the fibre's own structure morphism; the
equidimensionality and dimension conditions are those of `AlgebraicGeometry.RelativeDimension`
for the value one. -/
def HasAtWorstNodalFibresOfDimensionOne {X S : Scheme.{u}} (f : X ⟶ S) : Prop :=
  Flat f ∧ LocallyOfFinitePresentation f ∧
    ∀ s : S, Nonempty (f.fiber s) →
      letI : (f.fiber s).Over (Spec (.of (S.residueField s))) :=
        ⟨f.fiberToSpecResidueField s⟩
      TopologicalSpace.Equidimensional (f.fiber s) ∧
        topologicalKrullDim (f.fiber s) = (1 : WithBot ℕ∞) ∧
          HasAtWorstNodalSingularities (S.residueField s) (f.fiber s)

/-- **Stacks Project, Tag 0C59.**  A morphism of schemes is flat, locally of finite presentation
with every nonempty fibre equidimensional of dimension one and with at-worst-nodal singularities
exactly when it is syntomic of relative dimension one and the closed subscheme cut out by the
first Fitting ideal of its relative differentials is unramified over the base.

Everything except the nodal condition on the fibres is
`AlgebraicGeometry.isAtWorstNodalOfRelativeDimensionOne_iff_fibres`, which reads that condition
as condition (2) of Tag 0C4E; Tag 0C4E
(`Stacks.Curves.hasAtWorstNodalSingularities_iff_lci_and_unramified_relativeSingularIdeal`)
applied to a fibre trades the two.  Its hypotheses on the fibre are the equidimensionality and
the dimension, which both sides of the equivalence provide for a nonempty fibre, and local
finite type of the fibre's structure morphism, which follows from local finite presentation of
`f`; over an empty fibre condition (2) holds vacuously. -/
@[stacks 0C59 "condition (1) is `Stacks.Curves.HasAtWorstNodalFibresOfDimensionOne` and \
condition (2) is `AlgebraicGeometry.IsAtWorstNodalOfRelativeDimensionOne`"]
theorem hasAtWorstNodalFibresOfDimensionOne_iff {X S : Scheme.{u}} (f : X ⟶ S) :
    HasAtWorstNodalFibresOfDimensionOne f ↔ IsAtWorstNodalOfRelativeDimensionOne f := by
  have hfibre : LocallyOfFinitePresentation f → ∀ s : S,
      TopologicalSpace.Equidimensional (f.fiber s) →
      topologicalKrullDim (f.fiber s) = (1 : WithBot ℕ∞) →
      let : (f.fiber s).Over (Spec (.of (S.residueField s))) :=
        ⟨f.fiberToSpecResidueField s⟩
      (HasAtWorstNodalSingularities (S.residueField s) (f.fiber s) ↔
        IsLocalCompleteIntersectionOverField (f.fiberToSpecResidueField s) ∧
          Unramified ((relativeSingularIdeal (f.fiberToSpecResidueField s)).subschemeι ≫
            f.fiberToSpecResidueField s)) := by
    intro hlfp s hequi hdim
    let : (f.fiber s).Over (Spec (.of (S.residueField s))) := ⟨f.fiberToSpecResidueField s⟩
    have : LocallyOfFiniteType (f.fiber s ↘ Spec (.of (S.residueField s))) :=
      inferInstanceAs (LocallyOfFiniteType (f.fiberToSpecResidueField s))
    exact hasAtWorstNodalSingularities_iff_lci_and_unramified_relativeSingularIdeal
      (S.residueField s) (f.fiber s) hequi hdim
  rw [isAtWorstNodalOfRelativeDimensionOne_iff_fibres f]
  constructor
  · rintro ⟨hflat, hlfp, hfib⟩
    refine ⟨hflat, hlfp, fun s hs => ⟨(hfib s hs).1, (hfib s hs).2.1⟩, fun s => ?_⟩
    by_cases hs : Nonempty (f.fiber s)
    · obtain ⟨heq, hdim, hnodal⟩ := hfib s hs
      exact (hfibre hlfp s heq hdim).mp hnodal
    · exact ⟨fun y => absurd ⟨y⟩ hs,
        ⟨fun z => absurd ⟨(relativeSingularIdeal
          (f.fiberToSpecResidueField s)).subschemeι.base z⟩ hs⟩⟩
  · rintro ⟨hflat, hlfp, hrd, hfib⟩
    refine ⟨hflat, hlfp, fun s hs => ⟨(hrd s hs).1, (hrd s hs).2, ?_⟩⟩
    exact (hfibre hlfp s (hrd s hs).1 (hrd s hs).2).mpr (hfib s)

end Stacks.Curves

end
