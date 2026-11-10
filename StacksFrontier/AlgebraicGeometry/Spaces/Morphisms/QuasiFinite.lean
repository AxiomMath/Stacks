module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.FromLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Descent.EtaleLocal.QuasiFiniteLocalAtSource
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Criteria
public import StacksFrontier.AlgebraicGeometry.Spaces.AtlasCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleChartAtPointOpen
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Immersions
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescFiniteness
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.QuasiCompact
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.Unramified
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenCover
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenImmersionCriteria
public import StacksFrontier.AlgebraicGeometry.Spaces.OpenSubspaceImage
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsPullback
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteMorphismProperty
public import StacksFrontier.AlgebraicGeometry.Spaces.SmoothAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.ZariskiCoveringPoints
public import StacksFrontier.AlgebraicGeometry.Variety.Defs.Dimension.SpecializationTrdeg

/-!
# Quasi-finite morphisms of algebraic spaces

A morphism of algebraic spaces over a scheme `S` is locally quasi-finite when the scheme
morphism it induces in every commuting square of étale charts is locally of finite type and
locally quasi-finite, and quasi-finite when it is in addition quasi-compact
(`AlgebraicGeometry.Space.IsLocallyQuasiFinite` and `AlgebraicGeometry.Space.IsQuasiFinite`,
Stacks 03XJ). This file collects the permanence properties of those two conditions and the
local criteria which detect them: local quasi-finiteness is inherited by the first factor of a
locally quasi-finite composite, every étale morphism and every immersion is locally
quasi-finite, and local quasi-finiteness can be tested pointwise, after base change to a scheme
or an affine scheme, on one surjective étale chart of either side, on every commuting square of
étale charts, or over a pair of Zariski coverings.

Stability under composition (**Stacks 03XK**) and under arbitrary base change (**Stacks 03XL**)
are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/QuasiFiniteMorphismProperty.lean`, which this file
imports; the results are used here under the same names.

All of these except the statement about immersions are instances of the general
every-étale-chart machinery of Stacks 03MJ, 0AML and 0AMM, once local quasi-finiteness of
scheme morphisms is known to be étale local on the source and target. That input is the
locally-quasi-finite case of Stacks 04R3,
`AlgebraicGeometry.locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget`.

## Main definitions

There are no new definitions.

## Main results

* `AlgebraicGeometry.LocallyOfFiniteType.inf_locallyQuasiFinite_isLocalAtSource_etalePrecoverage`:
  local quasi-finiteness of a morphism of schemes in the sense of Stacks 03XJ is local on the
  source for the étale topology, which is the étale case of Stacks 036H.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_comp`: **Stacks 03XN**.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isImmersion`: **Stacks 03XM**.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_mono`: the local quasi-finiteness clause of
  **Stacks 0463**, whose separatedness clause is
  `AlgebraicGeometry.Space.isSeparated_of_mono` (Stacks 042N).
* `AlgebraicGeometry.Space.locallyQuasiFinite_tfae`: **Stacks 040Z**, the nine criteria, with
  the equivalence of its first two conditions also stated separately as
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt`.
* `AlgebraicGeometry.Space.isLocallyOfFiniteType_of_isEtale`: **Stacks 06LT**, and
  `AlgebraicGeometry.Space.isLocallyQuasiFinite_of_isEtale`: **Stacks 03XU** — an étale
  morphism is locally of finite type and locally quasi-finite.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_yoneda_map_iff`: for a morphism of the site,
  the chart condition is local quasi-finiteness of the underlying morphism of schemes.
* `AlgebraicGeometry.Space.isLocallyQuasiFinite_iff_forall_discreteTopology_fibre`:
  **Stacks 06RW**, local quasi-finiteness of a morphism locally of finite type against
  discreteness of all of its field-valued fibres.

## Implementation notes

As everywhere in this library, the Stacks Project's local quasi-finiteness of a morphism of
schemes is the conjunction of Mathlib's `AlgebraicGeometry.LocallyOfFiniteType` and
`AlgebraicGeometry.LocallyQuasiFinite`, so the tested property of scheme morphisms is the
infimum of those two morphism properties.

Locality on the source of that infimum for the étale topology goes through the étale case of
Stacks 036H, `AlgebraicGeometry.isLocalAtSource_etale_of_affine_descent`, exactly as for local
finite type and local finite presentation. Of its four hypotheses, three are already available:
étale precomposition is
`AlgebraicGeometry.LocallyOfFiniteType.inf_locallyQuasiFinite_respectsLeft_etale`,
and both Zariski localities come from the `AlgebraicGeometry.HasRingHomProperty` instances of
the two factors through `CategoryTheory.MorphismProperty.IsLocalAtSource.inf` and
`CategoryTheory.MorphismProperty.IsLocalAtTarget.inf`. The fourth, descent along a surjective
étale morphism of affine schemes, is elementary here: the finite-type factor descends because
it is étale local on the source already, and with it in hand both morphisms are of finite type
with affine — hence quasi-compact — source, so local quasi-finiteness is finiteness of every
fibre (`AlgebraicGeometry.locallyQuasiFinite_iff_finite_preimage_singleton`), and a fibre of
the quotient is the image of a fibre of the cover under a surjection.

Étale locality on the source and target itself is not reproved here: it is the
locally-quasi-finite case of Stacks 04R3, proved in
`StacksFrontier/AlgebraicGeometry/Descent/EtaleLocal/QuasiFiniteLocalAtSource.lean` alongside the
other cases of that tag.

Since the two Zariski localities of the factors are indexed by a ring-homomorphism property
which is not an output parameter, they are supplied by name rather than by synthesis, and the
two infima they feed are supplied by name for the same reason; this mirrors
`StacksFrontier/AlgebraicGeometry/Descent/EtaleLocal/FiniteTypeLocalAtSource.lean`.

The argument for an immersion does not go through the chart machinery and needs no hypothesis
of algebraicity: in a commuting square of étale charts of an immersion `f`, the chart of the
target pulls `f` back to an immersion `s` of schemes, the morphism of the square factors as an
étale morphism followed by `s`, and an immersion of schemes is both locally of finite type and
locally quasi-finite. Étaleness of the factor is read off from the cancellation property of
étale morphisms applied to a section of the base change of the source chart.

The monomorphism statement of Stacks 0463 is not a chart statement either: a monomorphism has
an isomorphism for its relative diagonal, hence an open immersion after every represented base
change, so Stacks 05W1 makes a locally-finite-type monomorphism unramified and Stacks 05W0
makes it locally quasi-finite. The separatedness clause of that tag needs no finite-type
hypothesis and is proved where the relative diagonal of a monomorphism is identified, namely in
`StacksFrontier/AlgebraicGeometry/Stacks/RelativeDiagonalMonomorphism.lean`; the tag's two clauses
are therefore carried by two declarations.

Stacks 06RW is the one statement here with genuine content beyond the chart machinery. Its
field-valued points are those of Stacks 03BU, `AlgebraicGeometry.Space.FieldValuedPoint`: a
field whose spectrum belongs to the chosen big fppf site, together with a section of the target
over it. That is the library's reading throughout of a morphism from the spectrum of a field,
and it is what the statement quantifies over; the converse direction uses only the canonical
representatives at residue fields, which do belong to the site. The fibre over such a point is
the presheaf fibre product with the field spectrum, and the topology on its points is the one
of Stacks 03BX, made a local instance for the final section.

In the direction from discreteness, a commuting
square of étale charts is first compared with the fibre product of the chart `b` of the target
along `f`: the comparison is étale after every represented base change, being a section of a
base change of the projection of that fibre product. Then each point `v` of the chart of the
target is handled through the canonical field-valued representative of Stacks 03BU at `v`: the
fibre of the morphism of the site over `v` is an étale chart of the fibre of `f` over the
corresponding field-valued point, and discreteness of the latter's point space forbids a
nontrivial specialization in that chart. The obstruction is transcendence degree: two points
of a chart with the same image in the point space are the two images of a single point of the
chart's self-fibre-product under a pair of étale morphisms over the base field, so their
residue fields have the same transcendence degree over it, whereas a nontrivial specialization
drops it strictly by Stacks 0A21. A fibre without nontrivial specializations is `T1`, which is
condition (3) of Stacks 01TH, so the morphism of the site is quasi-finite at each of its
points.

The scheme-level transcendence-degree bookkeeping is kept to the one lemma
`AlgebraicGeometry.trdeg_residueField_eq_of_etale`: the algebra structures on the residue
fields are the ones Stacks 0A21 uses, induced by the structure morphism to the field spectrum,
and the scalar tower along an étale morphism is the naturality of
`AlgebraicGeometry.Scheme.Γevaluation`. Nothing relative is needed, because the chart statement
is only ever applied with the base being the spectrum of a field, which is a one-point space.

Of the nine criteria of Stacks 040Z, seven are formal consequences of the chart machinery and
of the three permanence properties above; the two with content are the implication from base
change to *affine* schemes, which cuts each chart square down to the affine opens of the chart
of the target and reassembles the pieces with the étale-neighbourhood criterion of Stacks 04QZ,
and the implication from a pair of Zariski coverings, which produces for each point of the
source the open subspace of Stacks 02YU witnessing quasi-finiteness there as the image of the
member of the inner covering containing it.

## References

* [Stacks Project, Tag 01TH](https://stacks.math.columbia.edu/tag/01TH)
* [Stacks Project, Tag 036H](https://stacks.math.columbia.edu/tag/036H)
* [Stacks Project, Tag 03BU](https://stacks.math.columbia.edu/tag/03BU)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03HF](https://stacks.math.columbia.edu/tag/03HF)
* [Stacks Project, Tag 03XJ](https://stacks.math.columbia.edu/tag/03XJ)
* [Stacks Project, Tag 03XK](https://stacks.math.columbia.edu/tag/03XK)
* [Stacks Project, Tag 03XL](https://stacks.math.columbia.edu/tag/03XL)
* [Stacks Project, Tag 03XM](https://stacks.math.columbia.edu/tag/03XM)
* [Stacks Project, Tag 03XN](https://stacks.math.columbia.edu/tag/03XN)
* [Stacks Project, Tag 03XU](https://stacks.math.columbia.edu/tag/03XU)
* [Stacks Project, Tag 040Z](https://stacks.math.columbia.edu/tag/040Z)
* [Stacks Project, Tag 042N](https://stacks.math.columbia.edu/tag/042N)
* [Stacks Project, Tag 0463](https://stacks.math.columbia.edu/tag/0463)
* [Stacks Project, Tag 04QZ](https://stacks.math.columbia.edu/tag/04QZ)
* [Stacks Project, Tag 04R3](https://stacks.math.columbia.edu/tag/04R3)
* [Stacks Project, Tag 05W0](https://stacks.math.columbia.edu/tag/05W0)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
* [Stacks Project, Tag 06LT](https://stacks.math.columbia.edu/tag/06LT)
* [Stacks Project, Tag 06RW](https://stacks.math.columbia.edu/tag/06RW)
* [Stacks Project, Tag 0A21](https://stacks.math.columbia.edu/tag/0A21)
* [Stacks Project, Tag 0ABM](https://stacks.math.columbia.edu/tag/0ABM)
* [Stacks Project, Tag 0AML](https://stacks.math.columbia.edu/tag/0AML)
* [Stacks Project, Tag 0AMM](https://stacks.math.columbia.edu/tag/0AMM)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

/-! ### Local quasi-finiteness of scheme morphisms is étale local on the source and target -/

/-- Local quasi-finiteness of morphisms of schemes in the sense of Stacks 03XJ — local finite
type together with Mathlib's fibre condition — absorbs an étale morphism on the right. -/
theorem LocallyOfFiniteType.inf_locallyQuasiFinite_respectsRight_etale :
    MorphismProperty.RespectsRight
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      (@Etale.{u} : MorphismProperty Scheme.{u}) where
  postcomp i hi p hp :=
    have : Etale i := hi
    have hi' := locallyQuasiFinite_of_etale i
    have : LocallyOfFiniteType i := hi'.1
    have : LocallyQuasiFinite i := hi'.2
    have : LocallyOfFiniteType p := hp.1
    have : LocallyQuasiFinite p := hp.2
    ⟨inferInstance, inferInstance⟩

/-- Local quasi-finiteness of morphisms of schemes in the sense of Stacks 03XJ is stable under
composition, each of its two factors being so. -/
theorem LocallyOfFiniteType.inf_locallyQuasiFinite_isStableUnderComposition :
    MorphismProperty.IsStableUnderComposition
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) :=
  ⟨fun p q hp hq => ⟨MorphismProperty.comp_mem _ p q hp.1 hq.1,
    MorphismProperty.comp_mem _ p q hp.2 hq.2⟩⟩

/-- Local quasi-finiteness of morphisms of schemes in the sense of Stacks 03XJ is local on the
source for the étale topology.

This is the étale case of Stacks 036H. Its only input beyond the Zariski localities of the two
factors and the corresponding statement for local finite type is the elementary observation
that a fibre of a morphism of affine schemes is the image of a fibre of its base change along
a surjective étale morphism, hence finite as soon as that one is. -/
theorem LocallyOfFiniteType.inf_locallyQuasiFinite_isLocalAtSource_etalePrecoverage :
    MorphismProperty.IsLocalAtSource
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      Scheme.etalePrecoverage :=
  let := LocallyOfFiniteType.inf_locallyQuasiFinite_respectsLeft_etale.{u}
  let : IsZariskiLocalAtSource (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.FiniteType)
  let : IsZariskiLocalAtSource (@LocallyQuasiFinite.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.QuasiFinite)
  let : IsZariskiLocalAtTarget (@LocallyOfFiniteType.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @LocallyOfFiniteType.{u}) (Q := RingHom.FiniteType)
  let : IsZariskiLocalAtTarget (@LocallyQuasiFinite.{u}) :=
    HasRingHomProperty.instIsZariskiLocalAtTarget
      (P := @LocallyQuasiFinite.{u}) (Q := RingHom.QuasiFinite)
  let : IsZariskiLocalAtSource
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsLocalAtSource.inf _ _
  let : IsZariskiLocalAtTarget
      ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) :=
    MorphismProperty.IsLocalAtTarget.inf _ _
  isLocalAtSource_etale_of_affine_descent
    ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    fun {X' X _Y} _ _ _ g f hg hg' h => by
      have : Surjective g := hg
      have : Etale g := hg'
      have : LocallyOfFiniteType (g ≫ f) := h.1
      have : LocallyQuasiFinite (g ≫ f) := h.2
      have hcover : Presieve.ofArrows (fun _ : PUnit.{1} => X') (fun _ => g) ∈
          Scheme.etalePrecoverage.{u} X :=
        ofArrows_mem_etalePrecoverage_iff.mpr
          ⟨fun x => ⟨PUnit.unit, hg.1 x⟩, fun _ => hg'⟩
      have hft : LocallyOfFiniteType f :=
        MorphismProperty.IsLocalAtSource.of_forall_comp hcover (by
          rintro W k ⟨_⟩
          infer_instance)
      have : QuasiCompact f := quasiCompact_of_compactSpace f
      have : QuasiCompact (g ≫ f) := quasiCompact_of_compactSpace (g ≫ f)
      refine ⟨hft, ?_⟩
      rw [locallyQuasiFinite_iff_finite_preimage_singleton]
      intro y
      have hfibre : f ⁻¹' {y} = g.base '' ((g ≫ f) ⁻¹' {y}) := by
        ext x
        refine ⟨fun hx => ?_, ?_⟩
        · obtain ⟨x', rfl⟩ := hg.1 x
          exact ⟨x', by simpa [Scheme.Hom.comp_apply] using hx, rfl⟩
        · rintro ⟨x', hx', rfl⟩
          simpa [Scheme.Hom.comp_apply] using hx'
      rw [hfibre]
      exact ((g ≫ f).finite_preimage_singleton y).image _

/-! ### Specializations inside a fibre over a field -/

/-- Over a field, the transcendence degree of the residue field at a point of a scheme is
unchanged by pulling the point back along an étale morphism over the field. -/
private theorem trdeg_residueField_eq_of_etale {k : Type u} [Field k] {X R : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) (r : R ⟶ Spec (.of k)) (s : R ⟶ X) [Etale s] (hsr : s ≫ g = r)
    (z : R) :
    letI : Algebra k (X.residueField (s z)) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ X.Γevaluation (s z)).hom.toAlgebra
    letI : Algebra k (R.residueField z) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ r.appTop ≫ R.Γevaluation z).hom.toAlgebra
    Algebra.trdeg k (X.residueField (s z)) = Algebra.trdeg k (R.residueField z) := by
  dsimp only
  subst hsr
  let _ : Algebra k (X.residueField (s z)) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ g.appTop ≫ X.Γevaluation (s z)).hom.toAlgebra
  let _ : Algebra (X.residueField (s z)) (R.residueField z) :=
    (s.residueFieldMap z).hom.toAlgebra
  let _ : Algebra k (R.residueField z) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (s ≫ g).appTop ≫ R.Γevaluation z).hom.toAlgebra
  have htower : IsScalarTower k (X.residueField (s z)) (R.residueField z) :=
    .of_algebraMap_eq fun w => by
      change (R.Γevaluation z).hom ((s ≫ g).appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom w)) =
        (s.residueFieldMap z).hom ((X.Γevaluation (s z)).hom
          (g.appTop.hom ((Scheme.ΓSpecIso (.of k)).inv.hom w)))
      rw [Scheme.Γevaluation_naturality_apply s z (g.appTop.hom _)]
      rfl
  have halg : Algebra.IsAlgebraic (X.residueField (s z)) (R.residueField z) := inferInstance
  have hadd : Algebra.trdeg k (X.residueField (s z)) +
      Algebra.trdeg (X.residueField (s z)) (R.residueField z) =
      Algebra.trdeg k (R.residueField z) := trdeg_add_eq k (X.residueField (s z))
  rwa [trdeg_eq_zero_iff.mpr halg, add_zero] at hadd

/-- Two points of a scheme locally of finite type over a field which are the images of a single
point under a pair of étale morphisms over the field are incomparable: their residue fields have
the same transcendence degree over the base field, whereas a nontrivial specialization drops it
strictly. -/
private theorem eq_of_specializes_of_etale_pair {k : Type u} [Field k] {X R : Scheme.{u}}
    (g : X ⟶ Spec (.of k)) [LocallyOfFiniteType g] (s t : R ⟶ X) [Etale s] [Etale t]
    (hst : s ≫ g = t ≫ g) (z : R) (hsp : s z ⤳ t z) : s z = t z := by
  by_contra hne
  have hlt := trdeg_residueField_lt_of_specialization k X g hsp hne
  have hs := trdeg_residueField_eq_of_etale g (s ≫ g) s rfl z
  have ht := trdeg_residueField_eq_of_etale g (s ≫ g) t hst.symm z
  dsimp only at hlt hs ht
  rw [hs, ← ht] at hlt
  exact absurd rfl (ne_of_lt hlt)

/-- A morphism locally of finite type whose fibres contain no nontrivial specialization is
locally quasi-finite.

The hypothesis makes every scheme-theoretic fibre a `T1` space, so the point of the fibre
determined by a point of the source is closed in it and nothing specializes to it; that is
condition (3) of [Stacks Project, Tag 01TH]. -/
private theorem locallyQuasiFinite_of_eq_of_specializes {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyOfFiniteType f] (h : ∀ ⦃x x' : X⦄, x ⤳ x' → f x = f x' → x = x') :
    LocallyQuasiFinite f := by
  refine (locallyQuasiFinite_iff_isDiscrete_preimage_singleton (f := f)).mpr fun y => ?_
  rw [isDiscrete_iff_discreteTopology, discreteTopology_iff_isOpen_singleton]
  rintro ⟨x, rfl⟩
  have hmem (a : f.fiber (f x)) : f (f.fiberι (f x) a) = f x := by
    have hm : f.fiberι (f x) a ∈ f ⁻¹' {f x} := (f.range_fiberι (f x)).le ⟨a, rfl⟩
    simpa using hm
  have hT1 : T1Space (f.fiber (f x)) :=
    t1Space_iff_specializes_imp_eq.mpr fun {a b} hab =>
      (f.fiberι (f x)).injective
        (h (hab.map (f.fiberι (f x)).continuous) ((hmem a).trans (hmem b).symm))
  have hclosed : IsClosed ({f.asFiber x} : Set (f.fiber (f x))) :=
    have := hT1
    isClosed_singleton
  have hno : ¬ ∃ x' : f.fiber (f x), x' ≠ f.asFiber x ∧ x' ⤳ f.asFiber x := by
    rintro ⟨x', hne, hspec⟩
    have := hT1
    exact hne (specializes_iff_eq.mp hspec)
  have hthird : IsClosed ({f.asFiber x} : Set (f.fiber (f x))) ∧
      ¬ ∃ x' : f.fiber (f x), x' ≠ f.asFiber x ∧ x' ⤳ f.asFiber x := ⟨hclosed, hno⟩
  have hqf := ((quasiFiniteAt_tfae f x).out 3 1).mp hthird
  change IsOpen ({⟨x, by simp⟩} : Set (f ⁻¹' {f x}))
  simpa only [Set.image_singleton, Scheme.Hom.asFiber, Homeomorph.apply_symm_apply] using
    (f.fiberHomeo (f x)).isOpen_image.mpr
      (Scheme.Hom.quasiFiniteAt_iff_isOpen_singleton_asFiber.mp hqf.2)

/-- A morphism which is locally of finite type and locally quasi-finite with subsingleton
target has discrete source: its single nonempty fibre is the whole source. -/
@[ega "II 6.1.7" "special case"]
private theorem discreteTopology_of_locallyQuasiFinite_of_subsingleton {X Y : Scheme.{u}}
    (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f] (hY : Subsingleton Y) (y : Y) :
    DiscreteTopology X := by
  have hfibre := (locallyQuasiFinite_iff_isDiscrete_preimage_singleton (f := f)).mp
    inferInstance y
  have heq : f ⁻¹' ({y} : Set Y) = Set.univ := by
    ext z
    simp [Subsingleton.elim (f z) y]
  rw [heq, isDiscrete_iff_discreteTopology] at hfibre
  exact (Homeomorph.Set.univ X).discreteTopology_iff.mp hfibre

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_QuasiFinite :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_QuasiFinite
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) :
    HasLimit (cospan f g) :=
  (hasPullbacks_presheaf_QuasiFinite B S hS).has_limit _

set_option synthInstance.maxHeartbeats 400000 in
-- instance search for limits of presheaves on the big fppf site is slow (see the docstring)
/-- Discrete limits of presheaves on the big fppf site over `S` (instance search times out
without this shortcut under Lean v4.35.0). -/
local instance (priority := high) quasiFinite_hasLimitsOfShape_discrete (J : Type) :
    HasLimitsOfShape (Discrete J) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  inferInstance

/-! ### Cancellation -/

/-- **Stacks 03XN.** If a composite of morphisms of algebraic spaces over `S` is locally
quasi-finite, then so is its first factor.

Local quasi-finiteness of morphisms of schemes is étale local on the source and target
(Stacks 04R3) and is inherited by the first factor of a composite that has it, local finite
type by Stacks 01T8 and the fibre condition by `AlgebraicGeometry.LocallyQuasiFinite.of_comp`,
so this is an instance of the cancellation form of Stacks 03MJ.

This is also the locally-quasi-finite clause of part (1) of **Stacks 0AGC**, whose other
clauses are in `StacksFrontier/AlgebraicGeometry/Spaces/Morphisms/Immersions.lean`. -/
@[stacks 03XN, stacks 0AGC "part (1): locally quasi-finite"]
theorem isLocallyQuasiFinite_of_comp {F G H : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hF : IsAlgebraicSpace B S hS F) (hG : IsAlgebraicSpace B S hS G)
    (hH : IsAlgebraicSpace B S hS H)
    (f : F ⟶ G) (g : G ⟶ H)
    (hfg : IsLocallyQuasiFinite B S hS (f ≫ g)) :
    IsLocallyQuasiFinite B S hS f :=
  holdsOnEveryEtaleChart_of_comp B S hS
    ((@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
    (fun u v h =>
      let : LocallyOfFiniteType (u ≫ v) := h.1
      let : LocallyQuasiFinite (u ≫ v) := h.2
      ⟨LocallyOfFiniteType.of_comp (f := u) (g := v) h.1,
        LocallyQuasiFinite.of_comp u v⟩)
    hF hG hH f g hfg

/-! ### Étale morphisms -/

/-- **Stacks 06LT.** An étale morphism of algebraic spaces over `S` is locally of finite type:
an étale morphism of schemes is.

Only the target has to be an algebraic space, where the source requires both. -/
@[stacks 06LT]
theorem isLocallyOfFiniteType_of_isEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hf : IsEtale B S hS f) :
    IsLocallyOfFiniteType B S hS f :=
  holdsOnEveryEtaleChart_of_isEtale_hom B S hS
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
    (fun _ hg => have := hg; inferInstance) hY hf

/-- **Stacks 03XU.** An étale morphism of algebraic spaces over `S` is locally quasi-finite: an
étale morphism of schemes is locally of finite type and locally quasi-finite (Stacks 03II).

Only the target has to be an algebraic space, where the source requires both. -/
@[stacks 03XU]
theorem isLocallyQuasiFinite_of_isEtale
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {f : X ⟶ Y} (hf : IsEtale B S hS f) :
    IsLocallyQuasiFinite B S hS f :=
  holdsOnEveryEtaleChart_of_isEtale_hom B S hS
    ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    (fun g hg => have := hg; locallyQuasiFinite_of_etale g) hY hf

/-- A morphism from a representable presheaf to an algebraic space which is étale after every
represented base change is locally quasi-finite. -/
private theorem isLocallyQuasiFinite_of_presheaf_etale {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U : BigFppfOver B S hS} (hX : IsAlgebraicSpace B S hS X) (p : yoneda.obj U ⟶ X)
    (hp : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf p) :
    IsLocallyQuasiFinite B S hS p :=
  isLocallyQuasiFinite_of_isEtale B S hS hX ((isEtale_iff_presheaf_of_yoneda B S hS p).2 hp)

/-! ### Immersions -/

/-- Being étale after every represented base change is stable under base change. -/
private theorem presheaf_etale_isStableUnderBaseChange :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf.IsStableUnderBaseChange :=
  have := isMultiplicative_presheaf_etale B S hS
  MorphismProperty.relative_isStableUnderBaseChange _

/-- A morphism of the site which has an étale left inverse is étale. -/
private theorem etale_map_of_comp_eq_id {U W : BigFppfOver B S hS} (δ : U ⟶ W) (r : W ⟶ U)
    (hr : Etale ((BigFppfOver.toScheme B S hS).map r)) (h : δ ≫ r = 𝟙 U) :
    Etale ((BigFppfOver.toScheme B S hS).map δ) := by
  have : Etale ((BigFppfOver.toScheme B S hS).map δ ≫ (BigFppfOver.toScheme B S hS).map r) := by
    rw [← CategoryTheory.Functor.map_comp, h, CategoryTheory.Functor.map_id]
    infer_instance
  exact Etale.of_comp (f := (BigFppfOver.toScheme B S hS).map δ)
    ((BigFppfOver.toScheme B S hS).map r)

/-- **Stacks 03XM.** An immersion of algebraic spaces over `S` is locally quasi-finite.

Neither the source nor the target has to be an algebraic space: the immersion property is a
condition on the represented base changes of the morphism, and so is what the proof uses. -/
@[stacks 03XM]
theorem isLocallyQuasiFinite_of_isImmersion {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : X ⟶ Y) (hf : IsImmersion B S hS f) :
    IsLocallyQuasiFinite B S hS f := by
  intro U V a b h ha hb hab
  -- `s`, the base change of `f` along the chart `b` of the target, is an immersion of schemes
  set T := BigFppfOver.toScheme B S hS with hT
  let p := hf.rep.fst b
  let s := hf.rep.snd b
  have hsImm : AlgebraicGeometry.IsImmersion (T.map s) :=
    hf.property b p s (hf.rep.isPullback b)
  -- `q`, the comparison of the chart `a` of the source with that base change
  let q := hf.rep.lift a h hab.symm
  have hqp : yoneda.map q ≫ p = a := hf.rep.lift_fst (g := b) a h hab.symm
  have hqs : q ≫ s = h := hf.rep.lift_snd (g := b) a h hab.symm
  -- `q` is étale: the base change of `a` along `p` has a section over `U` given by `q`
  have hpEtale : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u}) T).presheaf p :=
    (presheaf_etale_isStableUnderBaseChange B S hS).of_isPullback
      (hf.rep.isPullback b).flip hb
  let r := hpEtale.rep.snd a
  let t := hpEtale.rep.fst' a
  have hrEtale : Etale (T.map r) := hpEtale.property a (hpEtale.rep.fst a) r
    (hpEtale.rep.isPullback a)
  have htEtale : Etale (T.map t) :=
    ha.property p (yoneda.map r) t (hpEtale.rep.isPullback' a).flip
  let δ := hpEtale.rep.lift' q (𝟙 U)
    (show yoneda.map q ≫ p = yoneda.map (𝟙 U) ≫ a by simp [hqp])
  have hδt : δ ≫ t = q := hpEtale.rep.lift'_fst _ _ _
  have hδr : δ ≫ r = 𝟙 U := hpEtale.rep.lift'_snd _ _ _
  have hδEtale : Etale (T.map δ) := etale_map_of_comp_eq_id B S hS δ r hrEtale hδr
  have hqEtale : Etale (T.map q) := by
    simpa only [← Functor.map_comp, hδt] using (inferInstance : Etale (T.map δ ≫ T.map t))
  -- an immersion of schemes is locally of finite type and locally quasi-finite, and so is `q`
  have hq' := locallyQuasiFinite_of_etale (T.map q)
  have : LocallyOfFiniteType (T.map q) := hq'.1
  have : LocallyQuasiFinite (T.map q) := hq'.2
  change LocallyOfFiniteType (T.map h) ∧ LocallyQuasiFinite (T.map h)
  rw [← hqs, Functor.map_comp]
  exact ⟨inferInstance, inferInstance⟩

/-! ### Monomorphisms -/

/-- **Stacks 0463**, the local quasi-finiteness clause: a monomorphism of algebraic spaces over
`S` which is locally of finite type is locally quasi-finite.

The relative diagonal of a monomorphism is an isomorphism, hence an open immersion after every
represented base change, so part (2) of [Stacks Project, Tag 05W1] makes the morphism
unramified and [Stacks Project, Tag 05W0] makes it locally quasi-finite.

The separatedness clause of the tag is `AlgebraicGeometry.Space.isSeparated_of_mono`, which is
[Stacks Project, Tag 042N] and needs no finite-type hypothesis. -/
@[stacks 0463 "local quasi-finiteness"]
theorem isLocallyQuasiFinite_of_mono {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hmono : Mono f) (hft : IsLocallyOfFiniteType B S hS f) :
    IsLocallyQuasiFinite B S hS f := by
  have hdiag : IsOpenImmersion B S hS (pullback.diagonal f) :=
    presheaf_of_isIso B S hS (MorphismProperty.RespectsIso.inverseImage _ _)
      (fun U => by
        have : _root_.AlgebraicGeometry.IsOpenImmersion
            ((BigFppfOver.toScheme B S hS).map (𝟙 U)) := by
          rw [CategoryTheory.Functor.map_id]; infer_instance
        exact this) _
  exact isLocallyQuasiFinite_of_isUnramified B S hS _
    (isUnramified_of_isOpenImmersion_pullbackDiagonal B S hS hX hY f hft hdiag)

/-! ### Base change in the shape of a fibre product of presheaves -/

/-- The base change of a locally quasi-finite morphism of algebraic spaces over `S`, along any
pullback square of algebraic spaces, is locally quasi-finite. -/
private theorem isLocallyQuasiFinite_snd_of_isPullback {X Y Z P : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (hP : IsAlgebraicSpace B S hS P) {f : X ⟶ Y} {g : Z ⟶ Y}
    {fst : P ⟶ X} {snd : P ⟶ Z} (hsq : IsPullback fst snd f g)
    (hf : IsLocallyQuasiFinite B S hS f) : IsLocallyQuasiFinite B S hS snd :=
  let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
  let Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩
  let Z' : AlgebraicSpaces B S hS := ⟨Z, hZ⟩
  let P' : AlgebraicSpaces B S hS := ⟨P, hP⟩
  (isLocallyQuasiFinite_isStableUnderBaseChange B S hS).of_isPullback
    (IsPullback.of_map_of_faithful (ObjectProperty.ι _) hsq :
      IsPullback (ObjectProperty.homMk fst : P' ⟶ X') (ObjectProperty.homMk snd : P' ⟶ Z')
        (ObjectProperty.homMk f : X' ⟶ Y') (ObjectProperty.homMk g : Z' ⟶ Y')) hf

/-- The base change of a locally quasi-finite morphism of algebraic spaces over `S` along an
arbitrary morphism of algebraic spaces, in the shape of a presheaf fibre product. -/
theorem isLocallyQuasiFinite_pullback_fst {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (g : Z ⟶ Y) (f : X ⟶ Y)
    (hf : IsLocallyQuasiFinite B S hS f) :
    IsLocallyQuasiFinite B S hS (pullback.fst g f) :=
  isLocallyQuasiFinite_snd_of_isPullback B S hS hX hY hZ
    (isAlgebraicSpace_pullback B S hS g f hZ hX hY) (IsPullback.of_hasPullback g f).flip hf

/-- The base change of a locally quasi-finite morphism of algebraic spaces over `S` along an
arbitrary morphism of algebraic spaces, in the shape of a presheaf fibre product taken on the
other side. -/
theorem isLocallyQuasiFinite_pullback_snd {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y)
    (hZ : IsAlgebraicSpace B S hS Z) (f : X ⟶ Y) (g : Z ⟶ Y)
    (hf : IsLocallyQuasiFinite B S hS f) :
    IsLocallyQuasiFinite B S hS (pullback.snd f g) :=
  isLocallyQuasiFinite_snd_of_isPullback B S hS hX hY hZ
    (isAlgebraicSpace_pullback B S hS f g hX hZ hY) (IsPullback.of_hasPullback f g) hf

/-! ### Local quasi-finiteness on a morphism of the site -/

/-- For a morphism of the big fppf site of `S`, local quasi-finiteness of the induced morphism
of representable presheaves is local quasi-finiteness of the underlying morphism of schemes. -/
theorem isLocallyQuasiFinite_yoneda_map_iff {U V : BigFppfOver B S hS} (a : U ⟶ V) :
    IsLocallyQuasiFinite B S hS (yoneda.map a) ↔
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
        ((BigFppfOver.toScheme B S hS).map a) := by
  have hstab := LocallyOfFiniteType.inf_locallyQuasiFinite_isStableUnderComposition.{u}
  have hiso : MorphismProperty.RespectsIso
      ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) := by
    apply MorphismProperty.RespectsIso.mk
    · intro A C D e g hg
      refine MorphismProperty.comp_mem _ e.hom g ?_ hg
      constructor <;> infer_instance
    · intro A C D e g hg
      refine MorphismProperty.comp_mem _ g e.hom hg ?_
      constructor <;> infer_instance
  change HoldsOnEveryEtaleChart B S hS
    ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    (yoneda.map a) ↔ _
  rw [holdsOnEveryEtaleChart_iff_representable B S hS
    ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget (yoneda.map a)]
  set l := yoneda.preimage (yoneda.obj U).reprW.hom with hl
  set r := yoneda.preimage (yoneda.obj V).reprW.inv with hr
  have hlIso : IsIso (yoneda.map l) := by
    simpa [hl] using (show IsIso ((yoneda.obj U).reprW.hom) from inferInstance)
  have : IsIso l := Yoneda.fullyFaithful.isIso_of_isIso_map l
  have hrIso : IsIso (yoneda.map r) := by
    simpa [hr] using (show IsIso ((yoneda.obj V).reprW.inv) from inferInstance)
  have : IsIso r := Yoneda.fullyFaithful.isIso_of_isIso_map r
  have hpre : yoneda.preimage
      ((yoneda.obj U).reprW.hom ≫ yoneda.map a ≫ (yoneda.obj V).reprW.inv) = l ≫ a ≫ r := by
    apply yoneda.map_injective
    simp [hl, hr]
  rw [hpre, Functor.map_comp, Functor.map_comp]
  exact (MorphismProperty.cancel_left_of_respectsIso
      (P := (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      ((BigFppfOver.toScheme B S hS).map l)
      ((BigFppfOver.toScheme B S hS).map a ≫ (BigFppfOver.toScheme B S hS).map r)).trans
    (MorphismProperty.cancel_right_of_respectsIso
      (P := (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
        (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
      ((BigFppfOver.toScheme B S hS).map a) ((BigFppfOver.toScheme B S hS).map r))

/-! ### The nine criteria of Stacks 040Z -/

/-- Quasi-finiteness of a morphism of algebraic spaces over `S` at a point of its source is
the pointed-chart condition of Stacks 04NC for the germ property induced by local
quasi-finiteness of morphisms of schemes.

The two sides are the same existential statement read with the point condition inside or
outside the witnessing open subspace: part (2) of Stacks 04RF turns the chart condition into
an open neighbourhood over which the morphism is locally quasi-finite, which is exactly
`AlgebraicGeometry.Space.IsQuasiFiniteAt`. -/
theorem isQuasiFiniteAt_iff_holdsOnEveryEtaleChartAtPoint
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (x : points B S hS X) :
    IsQuasiFiniteAt B S hS f x ↔
      HoldsOnEveryEtaleChartAtPoint B S hS
        (MorphismOfGerms.HasRepresentativeWithProperty
          ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
            (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))) f x := by
  rw [holdsOnEveryEtaleChartAtPoint_iff_exists_open B S hS
    ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget hX hY f x]
  exact ⟨fun ⟨U, hU, y, hy, hq⟩ => ⟨U, hU, ⟨y, hy⟩, hq⟩,
    fun ⟨U, hU, ⟨y, hy⟩, hq⟩ => ⟨U, hU, y, hy, hq⟩⟩

/-- **Stacks 040Z**, the equivalence of conditions (1) and (2): a morphism of algebraic spaces
over `S` is locally quasi-finite exactly when it is quasi-finite at every point of its
source. -/
theorem isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    IsLocallyQuasiFinite B S hS f ↔ ∀ x : points B S hS X, IsQuasiFiniteAt B S hS f x := by
  change HoldsOnEveryEtaleChart B S hS
    ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u})) f ↔ _
  rw [holdsOnEveryEtaleChart_iff_forall_atPoint B S hS
    ((@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}))
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget hX hY f]
  exact forall_congr' fun x =>
    (isQuasiFiniteAt_iff_holdsOnEveryEtaleChartAtPoint B S hS hX hY f x).symm

/-- **Stacks 040Z**, the implication (4) → (1): a morphism of algebraic spaces over `S` whose
base change to every affine scheme over its target is locally quasi-finite is itself locally
quasi-finite.

Fix a commuting square of étale charts `p` of the source over `q` of the target, with
underlying morphism of schemes `aS`. Each affine open `W` of the target chart cuts out a
commuting square of *affine* charts, whose base is admissible for the hypothesis; the morphism
of the site it produces factors through the fibre product over `W`, and both factors are
locally quasi-finite — one by the hypothesis, the other because the restriction of an étale
chart along an open immersion is still an étale chart. So `aS` is locally quasi-finite over
each member of an affine open cover of its target, which is the étale-neighbourhood criterion
of Stacks 04QZ. -/
private theorem isLocallyQuasiFinite_of_affine_baseChange
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hf : ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
      IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
        IsLocallyQuasiFinite B S hS (pullback.fst g f)) :
    IsLocallyQuasiFinite B S hS f := by
  intro U V p q a hp _hq ha
  set T := BigFppfOver.toScheme B S hS with hT
  set aS := T.map a with haSdef
  have hpqf := isLocallyQuasiFinite_of_presheaf_etale B S hS hX p hp
  have hrestrict : ∀ W : (T.obj V).affineOpens,
      LocallyOfFiniteType (aS ∣_ W.1) ∧ LocallyQuasiFinite (aS ∣_ W.1) := by
    intro W
    set Upre := aS ⁻¹ᵁ W.1 with hUpre
    let V' : BigFppfOver B S hS :=
      Over.mk (Y := B.obj (Scheme.size_lt_of_isOpenImmersion W.1.ι V.left.property))
        (ObjectProperty.homMk (W.1.ι ≫ V.hom.hom))
    let U' : BigFppfOver B S hS :=
      Over.mk (Y := B.obj (Scheme.size_lt_of_isOpenImmersion Upre.ι U.left.property))
        (ObjectProperty.homMk (Upre.ι ≫ U.hom.hom))
    let v : V' ⟶ V := Over.homMk (ObjectProperty.homMk W.1.ι)
    let i : U' ⟶ U := Over.homMk (ObjectProperty.homMk Upre.ι)
    have haS : aS ≫ V.hom.hom = U.hom.hom := congrArg (fun k => k.hom) a.w
    let a' : U' ⟶ V' := Over.homMk (ObjectProperty.homMk (aS ∣_ W.1)) (by
      apply ObjectProperty.hom_ext
      change (aS ∣_ W.1) ≫ W.1.ι ≫ V.hom.hom = Upre.ι ≫ U.hom.hom
      rw [morphismRestrict_ι_assoc, haS])
    have hav : a' ≫ v = i ≫ a := by
      apply Over.OverMorphism.ext
      apply ObjectProperty.hom_ext
      exact morphismRestrict_ι aS W.1
    set g := yoneda.map v ≫ q with hg
    set p' := yoneda.map i ≫ p with hp'def
    have hw : yoneda.map a' ≫ g = p' ≫ f := by
      rw [hg, hp'def, ← Category.assoc, ← yoneda.map_comp, hav, yoneda.map_comp]
      simpa only [Category.assoc] using congrArg (fun k => yoneda.map i ≫ k) ha
    set r : yoneda.obj U' ⟶ pullback g f := pullback.lift (yoneda.map a') p' hw with hr
    have hU' := isAlgebraicSpace_yoneda B S hS U'
    have hV' := isAlgebraicSpace_yoneda B S hS V'
    have hpb := isAlgebraicSpace_pullback B S hS g f hV' hX hY
    have hi : IsLocallyQuasiFinite B S hS (yoneda.map i) := by
      refine (isLocallyQuasiFinite_yoneda_map_iff B S hS i).mpr ?_
      change LocallyOfFiniteType Upre.ι ∧ LocallyQuasiFinite Upre.ι
      constructor <;> infer_instance
    have hp'qf : IsLocallyQuasiFinite B S hS p' :=
      isLocallyQuasiFinite_comp B S hS hU' (isAlgebraicSpace_yoneda B S hS U) hX
        (yoneda.map i) p hi hpqf
    have hrqf : IsLocallyQuasiFinite B S hS r := by
      refine isLocallyQuasiFinite_of_comp B S hS hU' hpb hX r (pullback.snd g f) ?_
      rwa [show r ≫ pullback.snd g f = p' from pullback.lift_snd _ _ _]
    have hgf : IsLocallyQuasiFinite B S hS (pullback.fst g f) :=
      hf V' g (by change IsAffine W.1.toScheme; exact W.2)
    have htop := isLocallyQuasiFinite_comp B S hS hU' hpb hV' r (pullback.fst g f) hrqf hgf
    rw [show r ≫ pullback.fst g f = yoneda.map a' from pullback.lift_fst _ _ _] at htop
    exact (isLocallyQuasiFinite_yoneda_map_iff B S hS a').mp htop
  have hP := locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget.{u}
  refine (hP.iff_forall_exists_etale_neighborhood aS).mpr fun x => ?_
  have hx : aS x ∈ (⨆ W : (T.obj V).affineOpens, W.1) := by
    rw [iSup_affineOpens_eq_top]
    trivial
  obtain ⟨W, hxW⟩ := TopologicalSpace.Opens.mem_iSup.mp hx
  exact ⟨_, _, (aS ⁻¹ᵁ W.1).ι, W.1.ι, aS ∣_ W.1, ⟨x, hxW⟩,
    inferInstance, inferInstance, rfl, morphismRestrict_ι aS W.1, hrestrict W⟩

/-- **Stacks 040Z.** Nine criteria for a morphism of algebraic spaces over `S` to be locally
quasi-finite: pointwise quasi-finiteness, local quasi-finiteness of every base change to a
scheme or to an affine scheme or to one surjective étale chart of the target, local
quasi-finiteness of the composite with one surjective étale chart of the source, and local
quasi-finiteness of the morphism of schemes in every — or in one surjective — commuting square
of étale charts, or over a pair of Zariski coverings. -/
@[stacks 040Z]
theorem locallyQuasiFinite_tfae {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y) :
    List.TFAE [
      IsLocallyQuasiFinite B S hS f,
      ∀ x : points B S hS X, IsQuasiFiniteAt B S hS f x,
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsLocallyQuasiFinite B S hS (pullback.fst g f),
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsAffine ((BigFppfOver.toScheme B S hS).obj Z) →
          IsLocallyQuasiFinite B S hS (pullback.fst g f),
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧
          IsLocallyQuasiFinite B S hS (pullback.fst g f),
      ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsSurjective B S hS p ∧ IsEtale B S hS p ∧ IsLocallyQuasiFinite B S hS (p ≫ f),
      ∀ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p → IsEtale B S hS q → p ≫ f = yoneda.map a ≫ q →
          IsLocallyQuasiFinite B S hS (yoneda.map a),
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧ IsLocallyQuasiFinite B S hS (yoneda.map a),
      ∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, IsLocallyQuasiFinite B S hS ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι)
    ] := by
  set P : MorphismProperty Scheme.{u} :=
    (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) ⊓
      (@AlgebraicGeometry.LocallyQuasiFinite.{u} : MorphismProperty Scheme.{u}) with hPdef
  have hP : IsEtaleLocalOnSourceAndTarget P :=
    locallyOfFiniteType_inf_locallyQuasiFinite_isEtaleLocalOnSourceAndTarget
  -- (1) ↔ (7): the chart condition, read off one square at a time
  have h1iff7 : IsLocallyQuasiFinite B S hS f ↔
      ∀ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p → IsEtale B S hS q → p ≫ f = yoneda.map a ≫ q →
          IsLocallyQuasiFinite B S hS (yoneda.map a) := by
    constructor
    · intro hf U V p q a hp hq hcomm
      refine (isLocallyQuasiFinite_yoneda_map_iff B S hS a).mpr ?_
      exact hf U V p q a ((isEtale_iff_presheaf_of_yoneda B S hS p).1 hp)
        ((isEtale_iff_presheaf_of_yoneda B S hS q).1 hq) hcomm.symm
    · intro h U V p q a hp hq hcomm
      exact (isLocallyQuasiFinite_yoneda_map_iff B S hS a).mp
        (h U V p q a ((isEtale_iff_presheaf_of_yoneda B S hS p).2 hp)
          ((isEtale_iff_presheaf_of_yoneda B S hS q).2 hq) hcomm.symm)
  -- (1) ↔ (8): one surjective square suffices, by Stacks 03MJ
  have h1iff8 : IsLocallyQuasiFinite B S hS f ↔
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧ IsLocallyQuasiFinite B S hS (yoneda.map a) := by
    constructor
    · intro hf
      obtain ⟨U, V, p, q, a, hp, hq, hs, hcomm, hPa⟩ :=
        (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hX hY f).mp hf
      exact ⟨U, V, p, q, a, (isEtale_iff_presheaf_of_yoneda B S hS p).2 hp,
        (isEtale_iff_presheaf_of_yoneda B S hS q).2 hq,
        (surjective_iff_surjective_pointsMap B S hS X hX U p).mp hs, hcomm.symm,
        (isLocallyQuasiFinite_yoneda_map_iff B S hS a).mpr hPa⟩
    · rintro ⟨U, V, p, q, a, hp, hq, hs, hcomm, hPa⟩
      refine (holdsOnEveryEtaleChart_iff_surjectiveChart B S hS P hP hX hY f).mpr
        ⟨U, V, p, q, a, (isEtale_iff_presheaf_of_yoneda B S hS p).1 hp,
          (isEtale_iff_presheaf_of_yoneda B S hS q).1 hq,
          (surjective_iff_surjective_pointsMap B S hS X hX U p).mpr hs, hcomm.symm,
          (isLocallyQuasiFinite_yoneda_map_iff B S hS a).mp hPa⟩
  -- (1) → (3): base change along an arbitrary morphism from a representable presheaf
  have h1to3 : IsLocallyQuasiFinite B S hS f →
      ∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsLocallyQuasiFinite B S hS (pullback.fst g f) := fun hf Z g =>
    isLocallyQuasiFinite_pullback_fst B S hS hX hY (isAlgebraicSpace_yoneda B S hS Z) g f hf
  -- (3) → (5): an atlas of the target is one admissible base
  have h3to5 : (∀ (Z : BigFppfOver B S hS) (g : yoneda.obj Z ⟶ Y),
        IsLocallyQuasiFinite B S hS (pullback.fst g f)) →
      ∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧
          IsLocallyQuasiFinite B S hS (pullback.fst g f) := by
    intro h
    obtain ⟨V, g, hs, he⟩ := hY.exists_atlas
    exact ⟨V, g, (surjective_iff_surjective_pointsMap B S hS Y hY V g).mp hs,
      (isEtale_iff_presheaf_of_yoneda B S hS g).2 he, h V g⟩
  -- (5) → (8): lift an atlas of the fibre product to a surjective étale square
  have h5to8 : (∃ (V : BigFppfOver B S hS) (g : yoneda.obj V ⟶ Y),
        IsSurjective B S hS g ∧ IsEtale B S hS g ∧
          IsLocallyQuasiFinite B S hS (pullback.fst g f)) →
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧ IsLocallyQuasiFinite B S hS (yoneda.map a) := by
    rintro ⟨V, q, hqSurj, hqEtale, hbase⟩
    let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let V' : AlgebraicSpaces B S hS := ⟨yoneda.obj V, isAlgebraicSpace_yoneda B S hS V⟩
    let q' : V' ⟶ Y' := ObjectProperty.homMk q
    let f' : X' ⟶ Y' := ObjectProperty.homMk f
    let W : AlgebraicSpaces B S hS := AlgebraicSpaces.fiberProduct B S hS q' f'
    let fst : W ⟶ V' := ObjectProperty.homMk (pullback.fst q f)
    let snd : W ⟶ X' := ObjectProperty.homMk (pullback.snd q f)
    have hsq : IsPullback fst snd q' f' :=
      AlgebraicSpaces.isPullback_fiberProduct B S hS q' f'
    obtain ⟨U, t, htSurj, htEtale⟩ := W.property.exists_atlas
    have htqf := isLocallyQuasiFinite_of_presheaf_etale B S hS W.property t htEtale
    have hsndEtale : IsEtale B S hS snd.hom :=
      isEtale_of_isPullback B S hS fst snd q' f' hsq hqEtale
    set a : U ⟶ V := yoneda.preimage (t ≫ fst.hom) with hadef
    have ha : yoneda.map a = t ≫ fst.hom := yoneda.map_preimage _
    have htop : IsLocallyQuasiFinite B S hS (yoneda.map a) := by
      have hcomp := isLocallyQuasiFinite_comp B S hS (isAlgebraicSpace_yoneda B S hS U)
        W.property (isAlgebraicSpace_yoneda B S hS V) t fst.hom htqf hbase
      rw [ha]
      exact hcomp
    have hQsurj := MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
    have hsndSurj : (MorphismProperty.presheaf (MorphismProperty.inverseImage
        (@AlgebraicGeometry.Surjective.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS))) snd.hom := by
      refine hQsurj.of_isPullback (IsPullback.of_hasPullback q f) ?_
      exact (surjective_iff_surjective_pointsMap B S hS Y hY V q).mpr hqSurj
    let _ : (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)).IsStableUnderComposition :=
      inverseImage_isStableUnderComposition B S hS surjective_isStableUnderComposition.{u}
    have hQsurjcomp := MorphismProperty.relative_isStableUnderComposition
      (MorphismProperty.inverseImage (@AlgebraicGeometry.Surjective.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
    have hsourceSurj : IsSurjective B S hS (t ≫ snd.hom) := by
      refine (surjective_iff_surjective_pointsMap B S hS X hX U (t ≫ snd.hom)).mp ?_
      exact MorphismProperty.comp_mem _ t snd.hom htSurj hsndSurj
    have hsourceEtale : IsEtale B S hS (t ≫ snd.hom) :=
      isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS t).2 htEtale) hsndEtale
    refine ⟨U, V, t ≫ snd.hom, q, a, hsourceEtale, hqEtale, hsourceSurj, ?_, htop⟩
    have hw : snd.hom ≫ f = fst.hom ≫ q := by
      simpa [q', f', Y'] using congrArg (fun k => k.hom) hsq.w.symm
    rw [ha, Category.assoc, hw, Category.assoc]
  -- (1) → (6): an atlas of the source, composed with `f`
  have h1to6 : IsLocallyQuasiFinite B S hS f →
      ∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsSurjective B S hS p ∧ IsEtale B S hS p ∧
          IsLocallyQuasiFinite B S hS (p ≫ f) := by
    intro hf
    obtain ⟨U, p, hpSurj, hpEtale⟩ := hX.exists_atlas
    have hpqf := isLocallyQuasiFinite_of_presheaf_etale B S hS hX p hpEtale
    exact ⟨U, p, (surjective_iff_surjective_pointsMap B S hS X hX U p).mp hpSurj,
      (isEtale_iff_presheaf_of_yoneda B S hS p).2 hpEtale,
      isLocallyQuasiFinite_comp B S hS (isAlgebraicSpace_yoneda B S hS U) hX hY p f hpqf hf⟩
  -- (6) → (8): lift an atlas of the target through the composite
  have h6to8 : (∃ (U : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X),
        IsSurjective B S hS p ∧ IsEtale B S hS p ∧
          IsLocallyQuasiFinite B S hS (p ≫ f)) →
      ∃ (U V : BigFppfOver B S hS) (p : yoneda.obj U ⟶ X) (q : yoneda.obj V ⟶ Y) (a : U ⟶ V),
        IsEtale B S hS p ∧ IsEtale B S hS q ∧ IsSurjective B S hS p ∧
          p ≫ f = yoneda.map a ≫ q ∧ IsLocallyQuasiFinite B S hS (yoneda.map a) := by
    rintro ⟨U, p, hpSurj, hpEtale, hpf⟩
    obtain ⟨V, q, hqSurj, hqEtale⟩ := hY.exists_atlas
    obtain ⟨W, r, a, hcomm, hrSurj, hrEtale⟩ :=
      exists_surjective_etale_presentation_lift B S hS
        (isAlgebraicSpace_yoneda B S hS U) hY (p ≫ f) V q hqSurj hqEtale
    have hrqf := isLocallyQuasiFinite_of_presheaf_etale B S hS
      (isAlgebraicSpace_yoneda B S hS U) r hrEtale
    have hcompqf := isLocallyQuasiFinite_comp B S hS (isAlgebraicSpace_yoneda B S hS W)
      (isAlgebraicSpace_yoneda B S hS U) hY r (p ≫ f) hrqf hpf
    rw [hcomm] at hcompqf
    have htop : IsLocallyQuasiFinite B S hS (yoneda.map a) :=
      isLocallyQuasiFinite_of_comp B S hS (isAlgebraicSpace_yoneda B S hS W)
        (isAlgebraicSpace_yoneda B S hS V) hY (yoneda.map a) q hcompqf
    have hrpSurj : IsSurjective B S hS (r ≫ p) := by
      change Function.Surjective (pointsMap B S hS (yoneda.obj W) (r ≫ p))
      rw [pointsMap_comp]
      exact hpSurj.comp ((surjective_iff_surjective_pointsMap B S hS (yoneda.obj U)
        (isAlgebraicSpace_yoneda B S hS U) W r).mp hrSurj)
    have hrpEtale : IsEtale B S hS (r ≫ p) :=
      isEtale_comp B S hS ((isEtale_iff_presheaf_of_yoneda B S hS r).2 hrEtale) hpEtale
    exact ⟨W, V, r ≫ p, q, a, hrpEtale, (isEtale_iff_presheaf_of_yoneda B S hS q).2 hqEtale,
      hrpSurj, by simpa only [Category.assoc] using hcomm, htop⟩
  -- (1) → (9): the trivial Zariski coverings
  have h1to9 : IsLocallyQuasiFinite B S hS f →
      ∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, IsLocallyQuasiFinite B S hS
            ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι) := by
    intro hf
    have hYtop := isOpenSubspace_top (B := B) (S := S) (hS := hS) (F := Y) hY
    have hPpull : IsAlgebraicSpace B S hS (pullback f (⊤ : Subfunctor Y).ι) :=
      isAlgebraicSpace_pullback B S hS f (⊤ : Subfunctor Y).ι hX hYtop.1 hY
    have hPtop := isOpenSubspace_top (B := B) (S := S) (hS := hS)
      (F := pullback f (⊤ : Subfunctor Y).ι) hPpull
    have hbase := isLocallyQuasiFinite_pullback_snd B S hS hX hY hYtop.1 f
      (⊤ : Subfunctor Y).ι hf
    have hPtopQf : IsLocallyQuasiFinite B S hS (⊤ : Subfunctor
        (pullback f (⊤ : Subfunctor Y).ι)).ι :=
      isLocallyQuasiFinite_of_isEtale B S hS hPpull
        (isEtale_of_isIso B S hS (⊤ : Subfunctor (pullback f (⊤ : Subfunctor Y).ι)).ι)
    exact ⟨PUnit.{u + 1}, fun _ => ⊤, fun _ => PUnit.{u + 1}, fun _ _ => ⊤,
      isZariskiCover_top hY, fun _ => isZariskiCover_top hPpull, fun _ _ =>
        isLocallyQuasiFinite_comp B S hS hPtop.1 hPpull hYtop.1 _ _ hPtopQf hbase⟩
  -- (9) → (2): a point of the source lies in one member of the inner covering
  have h9to2 : (∃ (I : Type u) (Yopen : I → Subfunctor Y) (J : I → Type u)
        (Xopen : ∀ i, J i → Subfunctor (pullback f (Yopen i).ι)),
        IsZariskiCover B S hS I Yopen ∧ (∀ i, IsZariskiCover B S hS (J i) (Xopen i)) ∧
          ∀ i j, IsLocallyQuasiFinite B S hS
            ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι)) →
      ∀ x : points B S hS X, IsQuasiFiniteAt B S hS f x := by
    rintro ⟨I, Yopen, J, Xopen, hYcover, hXcover, hlocal⟩ x
    have hYopens : ∀ i, IsOpenSubspace B S hS (Yopen i) := hYcover.1
    have hYpoints :=
      (isZariskiCover_iff_iUnion_points B S hS Y hY I Yopen hYopens).mp hYcover
    have hyCover : pointsMap B S hS X f x ∈
        ⋃ i, Set.range (pointsMap B S hS (Yopen i).toFunctor (Yopen i).ι) := by
      rw [hYpoints]; trivial
    obtain ⟨i, yi, hyi⟩ := Set.mem_iUnion.mp hyCover
    have hPi : IsAlgebraicSpace B S hS (pullback f (Yopen i).ι) :=
      isAlgebraicSpace_pullback B S hS f (Yopen i).ι hX (hYopens i).1 hY
    let X' : AlgebraicSpaces B S hS := ⟨X, hX⟩
    let Y' : AlgebraicSpaces B S hS := ⟨Y, hY⟩
    let Yi' : AlgebraicSpaces B S hS := ⟨(Yopen i).toFunctor, (hYopens i).1⟩
    let W' : AlgebraicSpaces B S hS := ⟨pullback f (Yopen i).ι, hPi⟩
    let f₀ : X' ⟶ Y' := ObjectProperty.homMk f
    let g₀ : Yi' ⟶ Y' := ObjectProperty.homMk (Yopen i).ι
    have hpb : IsPullback (ObjectProperty.homMk (pullback.fst f (Yopen i).ι) : W' ⟶ X')
        (ObjectProperty.homMk (pullback.snd f (Yopen i).ι) : W' ⟶ Yi') f₀ g₀ :=
      AlgebraicSpaces.isPullback_fiberProduct B S hS f₀ g₀
    obtain ⟨w, hwp, -⟩ := exists_point_of_isPullback B S hS hpb x yi hyi.symm
    have hXicover := hXcover i
    have hXipoints := (isZariskiCover_iff_iUnion_points B S hS
      (pullback f (Yopen i).ι) hPi (J i) (Xopen i) hXicover.1).mp hXicover
    have hwCover : w ∈ ⋃ j, Set.range
        (pointsMap B S hS (Xopen i j).toFunctor (Xopen i j).ι) := by
      rw [hXipoints]; trivial
    obtain ⟨j, w', hwj⟩ := Set.mem_iUnion.mp hwCover
    have hXi : IsOpenSubspace B S hS (Xopen i j) := hXicover.1 j
    set r : (Xopen i j).toFunctor ⟶ X := (Xopen i j).ι ≫ pullback.fst f (Yopen i).ι with hrdef
    have hQbc := MorphismProperty.relative_isStableUnderBaseChange
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
    have hQcomp := MorphismProperty.relative_isStableUnderComposition
      (MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
        MorphismProperty Scheme.{u}) (BigFppfOver.toScheme B S hS)) (F := yoneda)
    have hfstOpen : IsOpenImmersion B S hS (pullback.fst f (Yopen i).ι) :=
      hQbc.of_isPullback (IsPullback.of_hasPullback f (Yopen i).ι).flip (hYopens i).2
    have hrOpen : IsOpenImmersion B S hS r :=
      MorphismProperty.comp_mem _ (Xopen i j).ι (pullback.fst f (Yopen i).ι) hXi.2 hfstOpen
    have _ : Mono r := mono_of_presheaf_isOpenImmersion hrOpen
    have hROpen : IsOpenSubspace B S hS (Subfunctor.range r) :=
      isOpenSubspace_range_of_open B S hS r hXi.1 hrOpen
    have hYiQf : IsLocallyQuasiFinite B S hS (Yopen i).ι :=
      isLocallyQuasiFinite_of_isEtale B S hS hY
        (isEtale_ι_of_isOpenSubspace (hYopens i))
    have hXiTarget : IsLocallyQuasiFinite B S hS
        ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι ≫ (Yopen i).ι) := by
      have hcomp := isLocallyQuasiFinite_comp B S hS hXi.1 (hYopens i).1 hY
        ((Xopen i j).ι ≫ pullback.snd f (Yopen i).ι) (Yopen i).ι (hlocal i j) hYiQf
      simpa only [Category.assoc] using hcomp
    have hrTarget : r ≫ f =
        (Xopen i j).ι ≫ pullback.snd f (Yopen i).ι ≫ (Yopen i).ι := by
      rw [hrdef, Category.assoc, pullback.condition]
    have hmono : Mono r := mono_of_presheaf_isOpenImmersion hrOpen
    have : Mono r := hmono
    have hgR : Subfunctor.toRange r ≫ (Subfunctor.range r).ι = r := Subfunctor.toRange_ι r
    have hinvR : (asIso (Subfunctor.toRange r)).inv ≫ r = (Subfunctor.range r).ι :=
      calc (asIso (Subfunctor.toRange r)).inv ≫ r
          = (asIso (Subfunctor.toRange r)).inv ≫ Subfunctor.toRange r ≫
              (Subfunctor.range r).ι := by rw [hgR]
        _ = (Subfunctor.range r).ι := by simp
    have heQf : IsLocallyQuasiFinite B S hS (asIso (Subfunctor.toRange r)).inv :=
      isLocallyQuasiFinite_of_isEtale B S hS hXi.1
        (isEtale_of_isIso B S hS (asIso (Subfunctor.toRange r)).inv)
    have hRlocal : IsLocallyQuasiFinite B S hS ((Subfunctor.range r).ι ≫ f) := by
      have hcomp := isLocallyQuasiFinite_comp B S hS hROpen.1 hXi.1 hY
        (asIso (Subfunctor.toRange r)).inv (r ≫ f) heQf (hrTarget ▸ hXiTarget)
      simpa only [← Category.assoc, hinvR] using hcomp
    refine ⟨Subfunctor.range r, hROpen,
      pointsMap B S hS (Xopen i j).toFunctor (Subfunctor.toRange r) w', ?_, hRlocal⟩
    calc pointsMap B S hS (Subfunctor.range r).toFunctor (Subfunctor.range r).ι
          (pointsMap B S hS (Xopen i j).toFunctor (Subfunctor.toRange r) w')
        = pointsMap B S hS (Xopen i j).toFunctor
            (Subfunctor.toRange r ≫ (Subfunctor.range r).ι) w' := by
          rw [pointsMap_comp]; rfl
      _ = pointsMap B S hS (Xopen i j).toFunctor r w' := by rw [hgR]
      _ = pointsMap B S hS (pullback f (Yopen i).ι) (pullback.fst f (Yopen i).ι)
            (pointsMap B S hS (Xopen i j).toFunctor (Xopen i j).ι w') := by
          rw [hrdef, pointsMap_comp]; rfl
      _ = pointsMap B S hS (pullback f (Yopen i).ι) (pullback.fst f (Yopen i).ι) w := by
          rw [hwj]
      _ = x := hwp
  have h1iff2 := isLocallyQuasiFinite_iff_forall_isQuasiFiniteAt B S hS hX hY f
  tfae_have 1 ↔ 2 := h1iff2
  tfae_have 1 → 3 := h1to3
  tfae_have 3 → 4 := fun h Z g _ => h Z g
  tfae_have 4 → 1 := isLocallyQuasiFinite_of_affine_baseChange B S hS hX hY f
  tfae_have 3 → 5 := h3to5
  tfae_have 5 → 8 := h5to8
  tfae_have 8 → 1 := h1iff8.mpr
  tfae_have 1 → 6 := h1to6
  tfae_have 6 → 8 := h6to8
  tfae_have 1 ↔ 7 := h1iff7
  tfae_have 1 → 8 := h1iff8.mp
  tfae_have 1 → 9 := h1to9
  tfae_have 9 → 2 := h9to2
  tfae_finish

/-! ### Discrete fibres over field-valued points -/

attribute [local instance] pointTopology

/-- An open continuous surjection out of a discrete space has discrete target. -/
private theorem discreteTopology_of_isOpenMap_surjective {A C : Type*} [TopologicalSpace A]
    [TopologicalSpace C] [DiscreteTopology A] (φ : A → C) (hopen : IsOpenMap φ)
    (hsurj : Function.Surjective φ) : DiscreteTopology C := by
  rw [discreteTopology_iff_isOpen_singleton]
  intro y
  have himage : φ '' (φ ⁻¹' {y}) = {y} :=
    Set.image_preimage_eq_inter_range.trans (by simp [hsurj.range_eq])
  simpa only [himage] using hopen (φ ⁻¹' {y}) (isOpen_discrete _)

private theorem pointsToScheme_schemePointsHomeomorph_symm (U : BigFppfOver B S hS)
    (x : (BigFppfOver.toScheme B S hS).obj U) :
    pointsToScheme B S hS U ((schemePointsHomeomorph B S hS U).symm x) = x :=
  (schemePointsHomeomorph B S hS U).apply_symm_apply x

/-- The chart lemma for Stacks 06RW: a morphism of the site into the field spectrum of a
field-valued point whose source carries an étale chart of an algebraic space with discrete
point space is locally quasi-finite.

Two points of the chart with the same image in the point space are the two images of a point
of the chart's self-fibre-product, which maps to the chart by two étale morphisms over the
field; so no nontrivial specialization of the chart can survive in the point space, which is
discrete. -/
private theorem locallyQuasiFinite_map_of_discrete_points
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (p : FieldValuedPoint B S hS G) {U : BigFppfOver B S hS}
    (j : yoneda.obj U ⟶ F) (q : F ⟶ yoneda.obj p.siteObject) (g : U ⟶ p.siteObject)
    (hcomm : j ≫ q = yoneda.map g)
    (hj : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf j)
    (hdisc : DiscreteTopology (points B S hS F))
    (hft : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g)) :
    LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map g) := by
  have hrep : yoneda.relativelyRepresentable j := hj.1
  have hsq : IsPullback (yoneda.map (hrep.fst' j)) (yoneda.map (hrep.snd j)) j j :=
    hrep.isPullback' j
  have hsEtale : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (hrep.fst' j)) :=
    hj.property j (yoneda.map (hrep.snd j)) (hrep.fst' j) hsq.flip
  have htEtale : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (hrep.snd j)) :=
    hj.property j (yoneda.map (hrep.fst' j)) (hrep.snd j) hsq
  have hcompeq : hrep.fst' j ≫ g = hrep.snd j ≫ g := by
    apply yoneda.map_injective
    rw [Functor.map_comp, Functor.map_comp, ← hcomm, ← Category.assoc, ← Category.assoc, hsq.w]
  refine locallyQuasiFinite_of_eq_of_specializes ((BigFppfOver.toScheme B S hS).map g)
    (fun {x x'} hsp _ => ?_)
  have hcont : Continuous (fun y : (BigFppfOver.toScheme B S hS).obj U =>
      pointsMap B S hS (yoneda.obj U) j ((schemePointsHomeomorph B S hS U).symm y)) :=
    (continuous_pointsMap B S hS j).comp (schemePointsHomeomorph B S hS U).symm.continuous
  have heq : pointsMap B S hS (yoneda.obj U) j ((schemePointsHomeomorph B S hS U).symm x) =
      pointsMap B S hS (yoneda.obj U) j ((schemePointsHomeomorph B S hS U).symm x') :=
    specializes_iff_eq.mp (hsp.map hcont)
  have hsqs : IsPullback
      (ObjectProperty.homMk (yoneda.map (hrep.fst' j)) :
        (⟨yoneda.obj (hrep.pullback j),
            isAlgebraicSpace_yoneda B S hS (hrep.pullback j)⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (ObjectProperty.homMk (yoneda.map (hrep.snd j)) :
        (⟨yoneda.obj (hrep.pullback j),
            isAlgebraicSpace_yoneda B S hS (hrep.pullback j)⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩)
      (ObjectProperty.homMk j :
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶ ⟨F, hF⟩)
      (ObjectProperty.homMk j :
        (⟨yoneda.obj U, isAlgebraicSpace_yoneda B S hS U⟩ : AlgebraicSpaces B S hS) ⟶
          ⟨F, hF⟩) :=
    IsPullback.of_map_of_faithful (ObjectProperty.ι _) hsq
  obtain ⟨w, hw₁, hw₂⟩ := exists_point_of_isPullback B S hS hsqs
    ((schemePointsHomeomorph B S hS U).symm x) ((schemePointsHomeomorph B S hS U).symm x') heq
  have hproj (π : hrep.pullback j ⟶ U) (y : (BigFppfOver.toScheme B S hS).obj U)
      (hw : pointsMap B S hS (yoneda.obj (hrep.pullback j)) (yoneda.map π) w =
        (schemePointsHomeomorph B S hS U).symm y) :
      (BigFppfOver.toScheme B S hS).map π (pointsToScheme B S hS (hrep.pullback j) w) = y := by
    have hnat := pointsToScheme_pointsMap_yoneda B S hS π w
    rw [hw, pointsToScheme_schemePointsHomeomorph_symm] at hnat
    exact hnat.symm
  have hx := hproj _ _ hw₁
  have hx' := hproj _ _ hw₂
  calc x = (BigFppfOver.toScheme B S hS).map (hrep.fst' j)
            (pointsToScheme B S hS (hrep.pullback j) w) := hx.symm
    _ = (BigFppfOver.toScheme B S hS).map (hrep.snd j)
            (pointsToScheme B S hS (hrep.pullback j) w) :=
        eq_of_specializes_of_etale_pair (k := p.carrier)
          ((BigFppfOver.toScheme B S hS).map g)
          ((BigFppfOver.toScheme B S hS).map (hrep.fst' j))
          ((BigFppfOver.toScheme B S hS).map (hrep.snd j))
          (by rw [← Functor.map_comp, ← Functor.map_comp, hcompeq]) _
          (by rw [hx, hx']; exact hsp)
    _ = x' := hx'

/-- The comparison of a commuting square of étale charts with the fibre product of the chart of
the target along the morphism is étale after every represented base change.

The projection of that fibre product to the source of the morphism is étale after every
represented base change, being a base change of the chart of the target; the comparison
morphism is a section of the base change of that projection along the chart of the source, and
a section of an étale morphism is étale. -/
private theorem presheaf_etale_chartLift {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {U V : BigFppfOver B S hS} (a : yoneda.obj U ⟶ X) (b : yoneda.obj V ⟶ Y) (f : X ⟶ Y)
    (h : U ⟶ V) (hcomm : yoneda.map h ≫ b = a ≫ f)
    (ha : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b) :
    (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf
        (pullback.lift (yoneda.map h) a hcomm) := by
  have _ := isMultiplicative_presheaf_etale B S hS
  have _ : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).IsStableUnderBaseChange :=
    inverseImage_isStableUnderBaseChange B S hS
      AlgebraicGeometry.Etale.etale_isStableUnderBaseChange
  have _ := presheaf_etale_isStableUnderBaseChange B S hS
  have hsnd : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf (pullback.snd b f) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback (IsPullback.of_hasPullback b f) hb
  have hrel : yoneda.relativelyRepresentable (pullback.snd b f) := hsnd.1
  have hw : pullback.lift (yoneda.map h) a hcomm ≫ pullback.snd b f =
      yoneda.map (𝟙 U) ≫ a := by
    rw [pullback.lift_snd, CategoryTheory.Functor.map_id, Category.id_comp]
  have hrs := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf) (hrel.isPullback a) hsnd
  have hrp := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf) (hrel.isPullback a).flip ha
  have hsEtale : AlgebraicGeometry.Etale
      ((BigFppfOver.toScheme B S hS).map (hrel.snd a)) :=
    MorphismProperty.of_relative_map
      (P := MorphismProperty.inverseImage
        (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
        (BigFppfOver.toScheme B S hS)) hrs
  have hsecEtale := etale_map_of_comp_eq_id B S hS
    (hrel.lift (pullback.lift (yoneda.map h) a hcomm) (𝟙 U) hw) (hrel.snd a) hsEtale
    (hrel.lift_snd _ _ hw)
  rw [← hrel.lift_fst (pullback.lift (yoneda.map h) a hcomm) (𝟙 U) hw]
  exact MorphismProperty.comp_mem _ _ _
    (MorphismProperty.relative_map (F := yoneda) hsecEtale) hrp

/-- The fibre of a morphism of the site over a point `v` of its target is discrete, given a
field-valued point `q` of the target of `f` represented by the residue field at `v` and a
discrete fibre of `f` over `q`.

The fibre product `W` of the morphism of the site with the field spectrum of `q` carries an
étale chart `j` of the fibre `D` of `f` over `q`, obtained by base change from the étale chart
`c`; so `W ⟶ Spec κ(v)` is locally quasi-finite by
`AlgebraicGeometry.Space.locallyQuasiFinite_map_of_discrete_points`, hence `W` is discrete, and
`W` is the fibre in question. -/
private theorem discreteTopology_sitePullback_of_discrete_fibre
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    {U V : BigFppfOver B S hS} (b : yoneda.obj V ⟶ Y)
    (c : yoneda.obj U ⟶ pullback b f)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (g : U ⟶ V) (hg : yoneda.map g = c ≫ pullback.fst b f)
    (hftg : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g))
    (q : FieldValuedPoint B S hS Y) (lam : q.siteObject ⟶ V)
    (hlam : yoneda.map lam ≫ b = yonedaEquiv.symm q.value)
    (hdiscD : DiscreteTopology (points B S hS (pullback (yonedaEquiv.symm q.value) f))) :
    DiscreteTopology ((BigFppfOver.toScheme B S hS).obj (Limits.pullback g lam)) := by
  have _ := presheaf_etale_isStableUnderBaseChange B S hS
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hDalg : IsAlgebraicSpace B S hS (pullback (yonedaEquiv.symm q.value) f) :=
    isAlgebraicSpace_pullback B S hS _ f (isAlgebraicSpace_yoneda B S hS q.siteObject) hX hY
  -- the fibre product of `g` with the field spectrum of `q`, inside the site
  have hWsq : IsPullback (Limits.pullback.fst g lam) (Limits.pullback.snd g lam) g lam :=
    IsPullback.of_hasPullback g lam
  have hWyon := hWsq.map yoneda
  have hWscheme := hWsq.map (BigFppfOver.toScheme B S hS)
  -- the comparison `d` of the fibre of `f` over `q` with the fibre product of `b` along `f`
  have hdcomm : (pullback.fst (yonedaEquiv.symm q.value) f ≫ yoneda.map lam) ≫ b =
      pullback.snd (yonedaEquiv.symm q.value) f ≫ f := by
    rw [Category.assoc, hlam]
    exact pullback.condition
  have hdfst := pullback.lift_fst (f := b) (g := f)
    (pullback.fst (yonedaEquiv.symm q.value) f ≫ yoneda.map lam)
    (pullback.snd (yonedaEquiv.symm q.value) f) hdcomm
  have hdsnd := pullback.lift_snd (f := b) (g := f)
    (pullback.fst (yonedaEquiv.symm q.value) f ≫ yoneda.map lam)
    (pullback.snd (yonedaEquiv.symm q.value) f) hdcomm
  have hbase : IsPullback
      (pullback.lift (pullback.fst (yonedaEquiv.symm q.value) f ≫ yoneda.map lam)
        (pullback.snd (yonedaEquiv.symm q.value) f) hdcomm)
      (pullback.fst (yonedaEquiv.symm q.value) f) (pullback.fst b f) (yoneda.map lam) := by
    apply IsPullback.of_right (t := (IsPullback.of_hasPullback b f).flip)
    · rw [hdsnd, ← hlam]
      exact (IsPullback.of_hasPullback (yoneda.map lam ≫ b) f).flip
    · exact hdfst
  -- the chart `j` of the fibre of `f` over `q`
  have hjcomm : yoneda.map (Limits.pullback.snd g lam) ≫ yonedaEquiv.symm q.value =
      (yoneda.map (Limits.pullback.fst g lam) ≫ c ≫ pullback.snd b f) ≫ f := by
    rw [← hlam, ← Category.assoc, ← hWyon.w, hg]
    simp only [Category.assoc]
    rw [pullback.condition]
  have hjfst := pullback.lift_fst (f := yonedaEquiv.symm q.value) (g := f)
    (yoneda.map (Limits.pullback.snd g lam))
    (yoneda.map (Limits.pullback.fst g lam) ≫ c ≫ pullback.snd b f) hjcomm
  have hjsnd := pullback.lift_snd (f := yonedaEquiv.symm q.value) (g := f)
    (yoneda.map (Limits.pullback.snd g lam))
    (yoneda.map (Limits.pullback.fst g lam) ≫ c ≫ pullback.snd b f) hjcomm
  have hjd : pullback.lift (yoneda.map (Limits.pullback.snd g lam))
        (yoneda.map (Limits.pullback.fst g lam) ≫ c ≫ pullback.snd b f) hjcomm ≫
      pullback.lift (pullback.fst (yonedaEquiv.symm q.value) f ≫ yoneda.map lam)
        (pullback.snd (yonedaEquiv.symm q.value) f) hdcomm =
      yoneda.map (Limits.pullback.fst g lam) ≫ c := by
    apply pullback.hom_ext
    · simp only [Category.assoc, hdfst]
      rw [← Category.assoc, hjfst, ← hg]
      exact hWyon.w.symm
    · simp only [Category.assoc, hdsnd]
      exact hjsnd
  have hpbW : IsPullback (yoneda.map (Limits.pullback.fst g lam))
      (pullback.lift (yoneda.map (Limits.pullback.snd g lam))
        (yoneda.map (Limits.pullback.fst g lam) ≫ c ≫ pullback.snd b f) hjcomm) c
      (pullback.lift (pullback.fst (yonedaEquiv.symm q.value) f ≫ yoneda.map lam)
        (pullback.snd (yonedaEquiv.symm q.value) f) hdcomm) := by
    apply IsPullback.of_bot (t := hbase)
    · simpa only [hjfst, hg] using hWyon
    · exact hjd.symm
  have hjEtale := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf) hpbW hc
  -- the fibre product is locally quasi-finite over the field spectrum, hence discrete
  have hftW : LocallyOfFiniteType
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd g lam)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (P := (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}))
      hWscheme hftg
  have hqfW : LocallyQuasiFinite
      ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd g lam)) :=
    locallyQuasiFinite_map_of_discrete_points B S hS hDalg q _
      (pullback.fst (yonedaEquiv.symm q.value) f) (Limits.pullback.snd g lam) hjfst
      hjEtale hdiscD hftW
  have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj q.siteObject) := by
    change Subsingleton (PrimeSpectrum q.carrier)
    infer_instance
  exact discreteTopology_of_locallyQuasiFinite_of_subsingleton
    ((BigFppfOver.toScheme B S hS).map (Limits.pullback.snd g lam)) hsub
    (IsLocalRing.closedPoint q.carrier)

/-- The chart step of Stacks 06RW: if every fibre of `f` over a field-valued point of its
target has discrete point space, then the morphism of the site in any commuting square of
étale charts of `f`, read through the fibre product of the chart of the target along `f`, is
locally quasi-finite.

Each point `v` of the chart of the target has a canonical field-valued representative, giving a
field-valued point of the target whose fibre is discrete; the fibre product of the morphism of
the site with its field spectrum is then discrete, and it is the fibre over `v`. -/
private theorem locallyQuasiFinite_map_of_discrete_fibres
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hft : HoldsOnEveryEtaleChart B S hS
      (@AlgebraicGeometry.LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u}) f)
    (hdisc : ∀ p : FieldValuedPoint B S hS Y,
      DiscreteTopology (points B S hS (pullback (yonedaEquiv.symm p.value) f)))
    {U V : BigFppfOver B S hS} (b : yoneda.obj V ⟶ Y)
    (hb : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf b)
    (c : yoneda.obj U ⟶ pullback b f)
    (hc : (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf c)
    (g : U ⟶ V) (hg : yoneda.map g = c ≫ pullback.fst b f) :
    LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map g) := by
  have _ := presheaf_etale_isStableUnderBaseChange B S hS
  have _ := preservesLimitsOfShape_walkingCospan_toScheme B S hS
  have hπX := MorphismProperty.IsStableUnderBaseChange.of_isPullback
    (P := (MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf) (IsPullback.of_hasPullback b f) hb
  have haX := MorphismProperty.comp_mem
    ((MorphismProperty.inverseImage
      (@AlgebraicGeometry.Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf) c (pullback.snd b f) hc hπX
  have hsqcomm : yoneda.map g ≫ b = (c ≫ pullback.snd b f) ≫ f := by
    rw [hg]
    simp only [Category.assoc]
    rw [pullback.condition]
  have hftg : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map g) :=
    hft U V (c ≫ pullback.snd b f) b g haX hb hsqcomm
  refine (locallyQuasiFinite_iff_isDiscrete_preimage_singleton
    (f := (BigFppfOver.toScheme B S hS).map g)).2 fun v => ?_
  have hlamY : yonedaEquiv.symm (schemePointRepresentative B S hS V v).value =
      yoneda.map (schemePointRepresentative B S hS V v).value :=
    yonedaEquiv.symm_apply_eq.mpr (yonedaEquiv_yoneda_map _).symm
  have hlamb : yoneda.map (schemePointRepresentative B S hS V v).value ≫ b =
      yonedaEquiv.symm (FieldValuedPoint.map B S hS (yoneda.obj V) b
        (schemePointRepresentative B S hS V v)).value := by
    rw [← hlamY]
    exact yonedaEquiv_symm_naturality_right _ b _
  have hlamScheme : (BigFppfOver.toScheme B S hS).map
      (schemePointRepresentative B S hS V v).value =
      ((BigFppfOver.toScheme B S hS).obj V).fromSpecResidueField v := by
    change B.inclusion.map (B.inclusion.preimage
      (X := B.obj (B.residueField_spec_contains V.left.property v)) (Y := V.left)
      (((BigFppfOver.toScheme B S hS).obj V).fromSpecResidueField v)) = _
    rw [B.inclusion.map_preimage]
  have hdiscW := discreteTopology_sitePullback_of_discrete_fibre B S hS hX hY f b c hc g hg hftg
    (FieldValuedPoint.map B S hS (yoneda.obj V) b (schemePointRepresentative B S hS V v))
    (schemePointRepresentative B S hS V v).value hlamb
    (hdisc (FieldValuedPoint.map B S hS (yoneda.obj V) b
      (schemePointRepresentative B S hS V v)))
  have hWscheme := (IsPullback.of_hasPullback g
    (schemePointRepresentative B S hS V v).value).map (BigFppfOver.toScheme B S hS)
  have hpbFiber : IsPullback
      ((BigFppfOver.toScheme B S hS).map
        (Limits.pullback.fst g (schemePointRepresentative B S hS V v).value))
      ((BigFppfOver.toScheme B S hS).map
        (Limits.pullback.snd g (schemePointRepresentative B S hS V v).value))
      ((BigFppfOver.toScheme B S hS).map g)
      (((BigFppfOver.toScheme B S hS).obj V).fromSpecResidueField v) := hlamScheme ▸ hWscheme
  exact isDiscrete_iff_discreteTopology.mpr
    ((((BigFppfOver.toScheme B S hS).map g).fiberHomeo v).discreteTopology_iff.mp
      ((Scheme.homeoOfIso hpbFiber.isoPullback).discreteTopology_iff.mp hdiscW))

/-- **Stacks 06RW.** A morphism of algebraic spaces over `S` which is locally of finite type is
locally quasi-finite exactly when, for every field-valued point of its target, the point space
of the fibre over that point is discrete.

For the forward implication the fibre over a field-valued point is locally quasi-finite over
the field spectrum by Stacks 03XL, so its étale charts are discrete schemes; an étale chart is
open and surjective on points, hence the point space of the fibre is discrete.

For the converse a commuting square of étale charts of `f` is compared with the fibre product
of the chart of the target along `f`, and each point of the chart of the target is handled
through its canonical residue-field representative: the fibre of the morphism of the site over
that point is a chart of the corresponding fibre of `f`, which is discrete, so the morphism of
the site has no nontrivial specialization in that fibre and is therefore locally quasi-finite
by [Stacks Project, Tag 01TH]. -/
@[stacks 06RW]
theorem isLocallyQuasiFinite_iff_forall_discreteTopology_fibre
    {X Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B S hS X) (hY : IsAlgebraicSpace B S hS Y) (f : X ⟶ Y)
    (hft : IsLocallyOfFiniteType B S hS f) :
    IsLocallyQuasiFinite B S hS f ↔
      ∀ p : FieldValuedPoint B S hS Y,
        DiscreteTopology (points B S hS (pullback (yonedaEquiv.symm p.value) f)) := by
  have _ := isMultiplicative_presheaf_etale B S hS
  constructor
  · intro hqf p
    have hDalg := isAlgebraicSpace_pullback B S hS (yonedaEquiv.symm p.value) f
      (isAlgebraicSpace_yoneda B S hS p.siteObject) hX hY
    have hfst : IsLocallyQuasiFinite B S hS
        (pullback.fst (yonedaEquiv.symm p.value) f) :=
      isLocallyQuasiFinite_pullback_fst B S hS hX hY
        (isAlgebraicSpace_yoneda B S hS p.siteObject) (yonedaEquiv.symm p.value) f hqf
    obtain ⟨U, a, haSurj, haEtale⟩ := hDalg.exists_atlas
    have hm : yoneda.map
        (yonedaEquiv (a ≫ pullback.fst (yonedaEquiv.symm p.value) f)) =
        a ≫ pullback.fst (yonedaEquiv.symm p.value) f :=
      yonedaEquiv.injective (yonedaEquiv_yoneda_map _)
    have hchart := hfst U p.siteObject a (𝟙 (yoneda.obj p.siteObject))
      (yonedaEquiv (a ≫ pullback.fst (yonedaEquiv.symm p.value) f)) haEtale
      (MorphismProperty.id_mem _ _) (by rw [hm, Category.comp_id])
    have _ : LocallyOfFiniteType ((BigFppfOver.toScheme B S hS).map
      (yonedaEquiv (a ≫ pullback.fst (yonedaEquiv.symm p.value) f))) := hchart.1
    have _ : LocallyQuasiFinite ((BigFppfOver.toScheme B S hS).map
      (yonedaEquiv (a ≫ pullback.fst (yonedaEquiv.symm p.value) f))) := hchart.2
    have hsub : Subsingleton ((BigFppfOver.toScheme B S hS).obj p.siteObject) := by
      change Subsingleton (PrimeSpectrum p.carrier)
      infer_instance
    have hdiscU : DiscreteTopology ((BigFppfOver.toScheme B S hS).obj U) :=
      discreteTopology_of_locallyQuasiFinite_of_subsingleton
        ((BigFppfOver.toScheme B S hS).map
          (yonedaEquiv (a ≫ pullback.fst (yonedaEquiv.symm p.value) f))) hsub
        (IsLocalRing.closedPoint p.carrier)
    have _ : DiscreteTopology (points B S hS (yoneda.obj U)) :=
      (schemePointsHomeomorph B S hS U).symm.discreteTopology_iff.mp hdiscU
    exact discreteTopology_of_isOpenMap_surjective
      (pointsMap B S hS (yoneda.obj U) a)
      (isOpenMap_pointsMap_of_etale B S hS hDalg U a haEtale)
      ((surjective_iff_surjective_pointsMap B S hS _ hDalg U a).mp haSurj)
  · intro hdisc U V a b g ha hb hcomm
    exact ⟨hft U V a b g ha hb hcomm,
      locallyQuasiFinite_map_of_discrete_fibres B S hS hX hY f hft hdisc b hb
        (pullback.lift (yoneda.map g) a hcomm)
        (presheaf_etale_chartLift B S hS a b f g hcomm ha hb) g (pullback.lift_fst _ _ _).symm⟩

end Space

end AlgebraicGeometry

end
