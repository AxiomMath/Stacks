module

public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.EtaleLocalizationSplittingExistence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.FunctorialitySourceTargetCartesian
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupoidRestrictionProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.SectionOpenImmersion
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiFiniteLocusOnCharts
public import StacksFrontier.AlgebraicGeometry.Stacks.SmoothMonomorphismOpenImmersion

/-!
# The finite part as an open finite subgroupoid of the restriction

Let `(U, R, s, t, c)` be a groupoid in algebraic spaces over `B` and let
`(U', Z_univ, s', t', c')` be its finite part, with its étale projection `g : U' ⟶ U` and its
canonical morphism of groupoids to `(U, R, s, t, c)` (Stacks 04RU, in the form
`AlgebraicGeometry.Space.FinitePartUniversalOpen`).  Write `R' = R|_{U'}` for the restriction of
`R` to `U'` along `g`, whose arrow space is the iterated fibre product
`(U' ×_{g, U, t} R) ×_R (R ×_{s, U, g} U')`.

The proof of Stacks 03FM turns the finite part into a *splitting* of `R'` in four steps: the
morphism `(f, t', s') : Z_univ ⟶ R'` is an open immersion; `s'` and `t'` are finite; the set
`{r' ∈ |R'| : s'(r') = u', t'(r') = u'}` is contained in `|Z_univ|`; and the three together
present `Z_univ` as a strong splitting of `R'` at `u'` in the sense of Stacks 04RK.

**This file carries out the first, the second and the fourth of those steps**, the fourth in the
form it takes once the third is removed: `Z_univ` is exhibited as an
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid` of `R'`, which is conditions
(a) and (b) of Stacks 04RK.  **The third step is not carried out**, so no strong splitting is
produced and the conclusion of Stacks 03FM is not reached; see the implementation notes.

The geometric content is the open immersion.  `Z_univ` is by construction an open subspace of
the ambient fibre product `U' ×_{g, U, s} R`, which is `R ×_{s, U, g} U'` up to the symmetry of
a fibre product, and the projection `R' ⟶ R ×_{s, U, g} U'` is étale, being a base change of a
base change of `g`.  The morphism `Z_univ ⟶ R'` is the graph of `t' : Z_univ ⟶ U'` over that
projection: it is a *section* of the base change of `R' ⟶ R ×_{s, U, g} U'` to `Z_univ`, hence an
open immersion by Stacks 05W1 and Stacks 03KP, and composing it with the base change of the open
immersion `Z_univ ⟶ R ×_{s, U, g} U'` gives `Z_univ ⟶ R'`.

## Main definitions

* `AlgebraicGeometry.Space.FinitePartUniversalOpen.toRestriction`: the morphism
  `(f, t', s') : Z_univ ⟶ R'` of the Stacks proof.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.subgroupoidComp`: the composition law carried
  by `Z_univ` read inside `R'`.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.restrictedSubgroupoid`: **`Z_univ` as an open
  finite subgroupoid of `R|_{U'}`**, which is conditions (a) and (b) of Stacks 04RK.

## Main results

* `AlgebraicGeometry.Space.FinitePartUniversalOpen.isOpenImmersion_toRestriction`: **the first
  step of the Stacks 03FM proof** — `Z_univ ⟶ R'` is an open immersion.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.target_finite`: **the second step** on the
  target side — `t' : Z_univ ⟶ U'` is finite.  (The source side is
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.source_finite`, which is already available.)
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.isOpenSubspace_range_toRestriction`,
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.range_source_finite` and
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.range_target_finite`: `Z_univ` as an open
  subspace of the arrow space of `R'`, with both restricted structure morphisms finite.
* `AlgebraicGeometry.Space.FinitePartUniversalOpen.toRestriction_app_compAt` and
  `AlgebraicGeometry.Space.FinitePartUniversalOpen.subgroupoidComp_restricts`:
  `Z_univ ⟶ R'` carries the composition of the finite part to the composition of `R'`.
* `AlgebraicGeometry.Space.exists_openFiniteSubgroupoid_of_strongSplittingSituation`: in
  Situation 04RL there are an algebraic space `U'`, an étale `g : U' ⟶ U` and an open finite
  subgroupoid of `R|_{U'}`.

## Implementation notes

### Carried hypotheses

Everything about the finite part is carried by the datum `F : FinitePartUniversalOpen G`; no
separatedness, finite type, flatness or étaleness hypothesis is imposed beyond the fields of that
structure.  Of those fields the open immersion uses `objectProjection_etale` (through the two
base changes), `universalOpen`, `universalOpen_base` and the open half of
`universalOpen.isOpen`; the finiteness of `t'` uses `universalOpen.finite_projection` through
`source_finite`; and the subgroupoid additionally uses the composition, unit and inverse of the
finite part and its pointwise groupoid structure.  `universalOpen_closed` and
`universalOpen_containsUnit` are not used here.

The final statement carries only the four hypotheses that the big fppf site contains the base
scheme, the object scheme, the arrow scheme and the scheme of composable pairs — exactly the
four `Stacks.Groupoids.GroupoidScheme.realization` needs in order to exist — together with the
fields of `AlgebraicGeometry.Space.StrongSplittingSituation`.  Of the latter only separatedness
and local finite type of the source and target are consumed, through
`AlgebraicGeometry.Space.realizationFinitePart`: the finiteness of the set of arrows from `u` to
itself and the quasi-finiteness of `s` along it are *not* used, because no statement of this file
mentions `u`.

### Why no étale cancellation is needed

The natural argument for the open immersion is that `Z_univ ⟶ R'` is a monomorphism and étale,
and that an étale monomorphism of algebraic spaces is an open immersion
(`AlgebraicGeometry.Space.isOpenImmersion_of_isEtale_of_mono`).  That argument is not available:
étaleness of `Z_univ ⟶ R'` would have to be deduced from étaleness of `R' ⟶ R ×_{s, U, g} U'`
and of the open immersion `Z_univ ⟶ R ×_{s, U, g} U'` by cancelling on the right, and the
cancellation law for étale morphisms of *algebraic spaces* is in neither Mathlib nor this
library — only the scheme-level `AlgebraicGeometry.Etale.of_comp_right`.  The route taken here
replaces the cancellation by the section criterion
`AlgebraicGeometry.Space.isOpenImmersion_of_isEtale_of_section`, which is available.

### What is not reached

*The containment* `{r' ∈ |R'| : s'(r') = u', t'(r') = u'} ⊆ |Z_univ|`, which is the third step of
the Stacks 03FM proof and the `contains_arrows` field of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.StrongSplitting`.  Stacks proves it by exhibiting,
for a `Spec k`-valued point `z'` of `R'` with both endpoints `u'`, the triple
`(s ∘ z, Z_u ×_{Spec κ(u), s ∘ z} Spec k, z)` as a `Spec k`-valued point of `Z_univ` over `r'`.
Carrying that out needs the description of membership in `Z_univ` on sections together with the
restriction of the point `u' = (u, Z_u)` of
`AlgebraicGeometry.Space.etaleLocalFibrePoint` along `Spec k ⟶ Spec κ(u)`, and neither is developed
here.
Consequently **no `AlgebraicGeometry.GroupoidInAlgebraicSpaces.StrongSplitting` is built and
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.IsStronglySplitAt` is not proved**: what is produced
is an open finite subgroupoid, which is conditions (a) and (b) of Stacks 04RK and not the
splitting condition (1).

*No attribute is attached.*  The conclusion of Stacks 03FM is a single existential assertion
whose substance is that `R|_{U'}` is strongly split over `u'`.  That is not proved, here or in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/EtaleLocalizationSplittingExistence.lean`, so for
the reason recorded in that file's implementation notes no Stacks 03FM attribute is carried here
either.
The same holds for Stacks 04RU: its clauses are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/Groupoids/More/FinitePart/`, and the statements here are
consequences of them rather than clauses of the tag.

*Stacks 0DTC* is untouched; the `Splitting` structure would need the same missing containment for
the stabilizer.

### Restated private declarations

None.  Every input is a public declaration of this library.

### Shape of the proofs

Two tactic idioms are avoided throughout.  Rewriting with `CategoryTheory.Category.assoc` is
unreliable in the presheaf categories used here, so reassociation is done in term mode with
`Category.assoc` and `congrArg`; and the compatibility lemmas of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionCompositionData` are instantiated at
their explicit argument before being rewritten with, because the implicit type of that argument
is the fibre product of the category of algebraic spaces while the term supplied is a fibre
product of presheaves, and the two are equal only up to unfolding.  In
`AlgebraicGeometry.Space.FinitePartUniversalOpen.toRestriction_app_compAt` and
`AlgebraicGeometry.Space.FinitePartUniversalOpen.subgroupoidComp_restricts` the last step is a
`congrArg` over a `Subtype.ext`, not a rewrite, because the composable-pair subtype carries a
proof field that mentions the component being changed.

## References

* [Stacks Project, Tag 03FM](https://stacks.math.columbia.edu/tag/03FM)
* [Stacks Project, Tag 044B](https://stacks.math.columbia.edu/tag/044B)
* [Stacks Project, Tag 02YW](https://stacks.math.columbia.edu/tag/02YW)
* [Stacks Project, Tag 03KP](https://stacks.math.columbia.edu/tag/03KP)
* [Stacks Project, Tag 04RK](https://stacks.math.columbia.edu/tag/04RK)
* [Stacks Project, Tag 04RL](https://stacks.math.columbia.edu/tag/04RL)
* [Stacks Project, Tag 04RT](https://stacks.math.columbia.edu/tag/04RT)
* [Stacks Project, Tag 04RU](https://stacks.math.columbia.edu/tag/04RU)
* [Stacks Project, Tag 05W1](https://stacks.math.columbia.edu/tag/05W1)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open GroupoidInAlgebraicSpaces

variable {C : BigFppfSite.{u}} {S : Scheme.{u}} {hS : C.Contains S}
  {B : AlgebraicSpaces C S hS} {G : GroupoidInAlgebraicSpaces C S hS B}

namespace FinitePartUniversalOpen

/-- The lift of `(t', f) : Z_univ ⟶ U' × R` to the fibre product `U' ×_{g, U, t} R`, which is
the first of the two factors of the arrow space of the restriction `R|_{U'}`. -/
def toTargetFibre (F : FinitePartUniversalOpen G) :
    F.arrows ⟶ AlgebraicSpaces.fiberProduct C S hS F.objectProjection G.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS F.objectProjection G.target).lift
    F.target F.arrowMap F.arrowMap_comp_target.symm

/-- The lift of `(f, s') : Z_univ ⟶ R × U'` to the fibre product `R ×_{s, U, g} U'`, which is
the second of the two factors of the arrow space of the restriction `R|_{U'}`. -/
def toSourceFibre (F : FinitePartUniversalOpen G) :
    F.arrows ⟶ AlgebraicSpaces.fiberProduct C S hS G.source F.objectProjection :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source F.objectProjection).lift
    F.arrowMap F.source F.arrowMap_comp_source

/-- **The morphism `(f, t', s') : Z_univ ⟶ R'` of the proof of Stacks 03FM**, where
`R' = R|_{U'}` is the restriction of `R` to the object space of the finite part along the étale
projection `g`.  Its arrow space is the fibre product over `R` of `U' ×_{g, U, t} R` and
`R ×_{s, U, g} U'`, so the morphism is the lift of the pair
`AlgebraicGeometry.Space.FinitePartUniversalOpen.toTargetFibre` and
`AlgebraicGeometry.Space.FinitePartUniversalOpen.toSourceFibre`, both of which have the arrow
`f : Z_univ ⟶ R` of the finite part as their `R`-component. -/
def toRestriction (F : FinitePartUniversalOpen G) :
    F.arrows ⟶ GroupoidInAlgebraicSpaces.restrictionArrows G F.objectProjection :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS
      (fiberProductSnd F.objectProjection G.target)
      (fiberProductFst G.source F.objectProjection)).lift
    F.toTargetFibre F.toSourceFibre
    (((AlgebraicSpaces.isPullback_fiberProduct C S hS F.objectProjection G.target).lift_snd
        F.target F.arrowMap F.arrowMap_comp_target.symm).trans
      ((AlgebraicSpaces.isPullback_fiberProduct C S hS G.source F.objectProjection).lift_fst
        F.arrowMap F.source F.arrowMap_comp_source).symm)

/-- The first component of `Z_univ ⟶ R'` is the lift into `U' ×_{g, U, t} R`. -/
theorem toRestriction_comp_fst (F : FinitePartUniversalOpen G) :
    F.toRestriction ≫ fiberProductFst (fiberProductSnd F.objectProjection G.target)
        (fiberProductFst G.source F.objectProjection) = F.toTargetFibre :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS
    (fiberProductSnd F.objectProjection G.target)
    (fiberProductFst G.source F.objectProjection)).lift_fst _ _ _

/-- The second component of `Z_univ ⟶ R'` is the lift into `R ×_{s, U, g} U'`. -/
theorem toRestriction_comp_snd (F : FinitePartUniversalOpen G) :
    F.toRestriction ≫ fiberProductSnd (fiberProductSnd F.objectProjection G.target)
        (fiberProductFst G.source F.objectProjection) = F.toSourceFibre :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS
    (fiberProductSnd F.objectProjection G.target)
    (fiberProductFst G.source F.objectProjection)).lift_snd _ _ _

/-- The `U'`-component of the lift into `U' ×_{g, U, t} R` is the target `t'`. -/
theorem toTargetFibre_comp_fst (F : FinitePartUniversalOpen G) :
    F.toTargetFibre ≫ fiberProductFst F.objectProjection G.target = F.target :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS F.objectProjection G.target).lift_fst _ _ _

/-- The `R`-component of the lift into `U' ×_{g, U, t} R` is the arrow `f : Z_univ ⟶ R`. -/
theorem toTargetFibre_comp_snd (F : FinitePartUniversalOpen G) :
    F.toTargetFibre ≫ fiberProductSnd F.objectProjection G.target = F.arrowMap :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS F.objectProjection G.target).lift_snd _ _ _

/-- The `R`-component of the lift into `R ×_{s, U, g} U'` is the arrow `f : Z_univ ⟶ R`. -/
theorem toSourceFibre_comp_fst (F : FinitePartUniversalOpen G) :
    F.toSourceFibre ≫ fiberProductFst G.source F.objectProjection = F.arrowMap :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source F.objectProjection).lift_fst _ _ _

/-- The `U'`-component of the lift into `R ×_{s, U, g} U'` is the source `s'`. -/
theorem toSourceFibre_comp_snd (F : FinitePartUniversalOpen G) :
    F.toSourceFibre ≫ fiberProductSnd G.source F.objectProjection = F.source :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS G.source F.objectProjection).lift_snd _ _ _

/-- `Z_univ ⟶ R'` lies over the arrow `f : Z_univ ⟶ R` of the finite part. -/
theorem toRestriction_comp_arrowsToArrows (F : FinitePartUniversalOpen G) :
    F.toRestriction ≫
        GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G F.objectProjection =
      F.arrowMap :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ fiberProductSnd F.objectProjection G.target)
      F.toRestriction_comp_fst).trans F.toTargetFibre_comp_snd)

/-- `Z_univ ⟶ R'` carries the source of the restriction to the source `s'` of the finite
part. -/
theorem toRestriction_comp_restrictionSource (F : FinitePartUniversalOpen G) :
    F.toRestriction ≫ GroupoidInAlgebraicSpaces.restrictionSource G F.objectProjection =
      F.source :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ fiberProductSnd G.source F.objectProjection)
      F.toRestriction_comp_snd).trans F.toSourceFibre_comp_snd)

/-- `Z_univ ⟶ R'` carries the target of the restriction to the target `t'` of the finite
part. -/
theorem toRestriction_comp_restrictionTarget (F : FinitePartUniversalOpen G) :
    F.toRestriction ≫ GroupoidInAlgebraicSpaces.restrictionTarget G F.objectProjection =
      F.target :=
  (Category.assoc _ _ _).symm.trans
    ((congrArg (fun k => k ≫ fiberProductFst F.objectProjection G.target)
      F.toRestriction_comp_fst).trans F.toTargetFibre_comp_fst)

/-- The commuting square making the exchanged pair of projections of `U' ×_{g, U, s} R` a cone
over the cospan defining `R ×_{s, U, g} U'`. -/
theorem ambientSwap_cond (F : FinitePartUniversalOpen G) :
    pullback.snd F.universalOpen.toBase.hom G.source.hom ≫ G.source.hom =
      pullback.fst F.universalOpen.toBase.hom G.source.hom ≫ F.objectProjection.hom :=
  pullback.condition.symm.trans
    (congrArg (fun k => pullback.fst F.universalOpen.toBase.hom G.source.hom ≫ k)
      F.universalOpen_toBase_hom)

/-- The commuting square for the exchange in the other direction. -/
theorem ambientSwapInv_cond (F : FinitePartUniversalOpen G) :
    pullback.snd G.source.hom F.objectProjection.hom ≫ F.universalOpen.toBase.hom =
      pullback.fst G.source.hom F.objectProjection.hom ≫ G.source.hom :=
  (congrArg (fun k => pullback.snd G.source.hom F.objectProjection.hom ≫ k)
    F.universalOpen_toBase_hom).trans pullback.condition.symm

/-- The symmetry comparing the ambient fibre product `U' ×_{g, U, s} R` of the universal open
subspace with the fibre product `R ×_{s, U, g} U'` which is a factor of the arrow space of the
restriction.  It exchanges the two projections, and it is formed along the base of the universal
pair rather than along `g`, the two being equal by
`AlgebraicGeometry.Space.FinitePartUniversalOpen.universalOpen_toBase_hom`. -/
def ambientSwap (F : FinitePartUniversalOpen G) :
    pullback F.universalOpen.toBase.hom G.source.hom ⟶
      pullback G.source.hom F.objectProjection.hom :=
  (IsPullback.of_hasPullback G.source.hom F.objectProjection.hom).lift
    (pullback.snd F.universalOpen.toBase.hom G.source.hom)
    (pullback.fst F.universalOpen.toBase.hom G.source.hom) F.ambientSwap_cond

/-- The symmetry carries the projection to `R` to the projection to `R`. -/
theorem ambientSwap_comp_fst (F : FinitePartUniversalOpen G) :
    F.ambientSwap ≫ pullback.fst G.source.hom F.objectProjection.hom =
      pullback.snd F.universalOpen.toBase.hom G.source.hom :=
  (IsPullback.of_hasPullback G.source.hom F.objectProjection.hom).lift_fst _ _ _

/-- The symmetry carries the projection to `U'` to the projection to `U'`. -/
theorem ambientSwap_comp_snd (F : FinitePartUniversalOpen G) :
    F.ambientSwap ≫ pullback.snd G.source.hom F.objectProjection.hom =
      pullback.fst F.universalOpen.toBase.hom G.source.hom :=
  (IsPullback.of_hasPullback G.source.hom F.objectProjection.hom).lift_snd _ _ _

/-- The inverse symmetry, exchanging the two projections in the other direction. -/
def ambientSwapInv (F : FinitePartUniversalOpen G) :
    pullback G.source.hom F.objectProjection.hom ⟶
      pullback F.universalOpen.toBase.hom G.source.hom :=
  (IsPullback.of_hasPullback F.universalOpen.toBase.hom G.source.hom).lift
    (pullback.snd G.source.hom F.objectProjection.hom)
    (pullback.fst G.source.hom F.objectProjection.hom) F.ambientSwapInv_cond

/-- The inverse symmetry carries the projection to `U'` to the projection to `U'`. -/
theorem ambientSwapInv_comp_fst (F : FinitePartUniversalOpen G) :
    F.ambientSwapInv ≫ pullback.fst F.universalOpen.toBase.hom G.source.hom =
      pullback.snd G.source.hom F.objectProjection.hom :=
  (IsPullback.of_hasPullback F.universalOpen.toBase.hom G.source.hom).lift_fst _ _ _

/-- The inverse symmetry carries the projection to `R` to the projection to `R`. -/
theorem ambientSwapInv_comp_snd (F : FinitePartUniversalOpen G) :
    F.ambientSwapInv ≫ pullback.snd F.universalOpen.toBase.hom G.source.hom =
      pullback.fst G.source.hom F.objectProjection.hom :=
  (IsPullback.of_hasPullback F.universalOpen.toBase.hom G.source.hom).lift_snd _ _ _

/-- The symmetry is an isomorphism, the two exchanges being mutually inverse. -/
instance isIso_ambientSwap (F : FinitePartUniversalOpen G) : IsIso F.ambientSwap :=
  ⟨F.ambientSwapInv,
    (IsPullback.of_hasPullback F.universalOpen.toBase.hom G.source.hom).hom_ext
      (((Category.assoc _ _ _).trans
        ((congrArg (fun k => F.ambientSwap ≫ k) F.ambientSwapInv_comp_fst).trans
          F.ambientSwap_comp_snd)).trans (Category.id_comp _).symm)
      (((Category.assoc _ _ _).trans
        ((congrArg (fun k => F.ambientSwap ≫ k) F.ambientSwapInv_comp_snd).trans
          F.ambientSwap_comp_fst)).trans (Category.id_comp _).symm),
    (IsPullback.of_hasPullback G.source.hom F.objectProjection.hom).hom_ext
      (((Category.assoc _ _ _).trans
        ((congrArg (fun k => F.ambientSwapInv ≫ k) F.ambientSwap_comp_fst).trans
          F.ambientSwapInv_comp_snd)).trans (Category.id_comp _).symm)
      (((Category.assoc _ _ _).trans
        ((congrArg (fun k => F.ambientSwapInv ≫ k) F.ambientSwap_comp_snd).trans
          F.ambientSwapInv_comp_fst)).trans (Category.id_comp _).symm)⟩

/-- The lift of `Z_univ` into `R ×_{s, U, g} U'` is the inclusion of the universal open
subspace into its ambient fibre product followed by the symmetry: both have the arrow
`f : Z_univ ⟶ R` as `R`-component and the source `s'` as `U'`-component. -/
theorem toSourceFibre_hom (F : FinitePartUniversalOpen G) :
    F.toSourceFibre.hom = F.universalOpen.subspace.ι ≫ F.ambientSwap :=
  (IsPullback.of_hasPullback G.source.hom F.objectProjection.hom).hom_ext
    ((congrArg (fun k => k.hom) F.toSourceFibre_comp_fst).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k => F.universalOpen.subspace.ι ≫ k)
          F.ambientSwap_comp_fst)).symm)
    ((congrArg (fun k => k.hom) F.toSourceFibre_comp_snd).trans
      ((Category.assoc _ _ _).trans
        (congrArg (fun k => F.universalOpen.subspace.ι ≫ k)
          F.ambientSwap_comp_snd)).symm)

/-- **`Z_univ ⟶ R ×_{s, U, g} U'` is an open immersion**: it is the inclusion of the universal
open subspace followed by an isomorphism. -/
theorem isOpenImmersion_toSourceFibre (F : FinitePartUniversalOpen G) :
    IsOpenImmersion C S hS F.toSourceFibre.hom := by
  rw [F.toSourceFibre_hom]
  exact MorphismProperty.RespectsIso.postcomp _ _ _ F.universalOpen.isOpen.2

/-- The projection `U' ×_{g, U, t} R ⟶ R` is étale, being a base change of the étale
`g : U' ⟶ U` along the target `t : R ⟶ U`. -/
theorem isEtale_targetFibreToArrows (F : FinitePartUniversalOpen G) :
    IsEtale C S hS (fiberProductSnd F.objectProjection G.target).hom :=
  isEtale_of_isPullback C S hS _ _ _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS F.objectProjection G.target)
    F.objectProjection_etale

/-- **The projection `R' ⟶ R ×_{s, U, g} U'` is étale**, being a base change of the étale
`U' ×_{g, U, t} R ⟶ R`, itself a base change of `g`.  This is the étaleness the Stacks proof
quotes as "a base change of `U' ⟶ U`". -/
theorem isEtale_restrictionToSourceFibre (F : FinitePartUniversalOpen G) :
    IsEtale C S hS (fiberProductSnd (fiberProductSnd F.objectProjection G.target)
      (fiberProductFst G.source F.objectProjection)).hom :=
  isEtale_of_isPullback C S hS _ _ _ _
    (AlgebraicSpaces.isPullback_fiberProduct C S hS
      (fiberProductSnd F.objectProjection G.target)
      (fiberProductFst G.source F.objectProjection))
    F.isEtale_targetFibreToArrows

/-- The graph of `t' : Z_univ ⟶ U'` over the projection `R' ⟶ R ×_{s, U, g} U'`: the section of
the base change of that projection to `Z_univ` determined by
`AlgebraicGeometry.Space.FinitePartUniversalOpen.toRestriction`. -/
def restrictionGraph (F : FinitePartUniversalOpen G) :
    F.arrows ⟶ AlgebraicSpaces.fiberProduct C S hS F.toSourceFibre
      (fiberProductSnd (fiberProductSnd F.objectProjection G.target)
        (fiberProductFst G.source F.objectProjection)) :=
  (AlgebraicSpaces.isPullback_fiberProduct C S hS F.toSourceFibre
    (fiberProductSnd (fiberProductSnd F.objectProjection G.target)
      (fiberProductFst G.source F.objectProjection))).lift
    (𝟙 F.arrows) F.toRestriction
    ((Category.id_comp _).trans F.toRestriction_comp_snd.symm)

/-- **The first step of the proof of Stacks 03FM: `Z_univ ⟶ R'` is an open immersion.**

Write `A' = R ×_{s, U, g} U'` and `p : R' ⟶ A'` for the projection, which is étale.  Base
changing `p` along the open immersion `Z_univ ⟶ A'` gives an étale morphism
`Z_univ ×_{A'} R' ⟶ Z_univ` and an open immersion `Z_univ ×_{A'} R' ⟶ R'`.  The morphism
`Z_univ ⟶ R'` lifts to a section of the former, which is therefore an open immersion by
Stacks 05W1 and Stacks 03KP, and `Z_univ ⟶ R'` is that section followed by the latter. -/
theorem isOpenImmersion_toRestriction (F : FinitePartUniversalOpen G) :
    IsOpenImmersion C S hS F.toRestriction.hom := by
  set p := fiberProductSnd (fiberProductSnd F.objectProjection G.target)
    (fiberProductFst G.source F.objectProjection) with hp
  have hsq := AlgebraicSpaces.isPullback_fiberProduct C S hS F.toSourceFibre p
  have hetale : IsEtale C S hS (fiberProductFst F.toSourceFibre p).hom :=
    isEtale_of_isPullback C S hS _ _ _ _ hsq.flip F.isEtale_restrictionToSourceFibre
  have hsnd : IsOpenImmersion C S hS (fiberProductSnd F.toSourceFibre p).hom :=
    isOpenImmersion_of_isPullback C S hS hsq F.isOpenImmersion_toSourceFibre
  have hsec : F.restrictionGraph.hom ≫ (fiberProductFst F.toSourceFibre p).hom =
      𝟙 F.arrows.obj :=
    congrArg (fun k => k.hom) (hsq.lift_fst (𝟙 F.arrows) F.toRestriction
      ((Category.id_comp _).trans F.toRestriction_comp_snd.symm))
  have hgraph : IsOpenImmersion C S hS F.restrictionGraph.hom :=
    isOpenImmersion_of_isEtale_of_section C S hS
      (AlgebraicSpaces.fiberProduct C S hS F.toSourceFibre p).property
      F.arrows.property _ hetale _ hsec
  have hfac : F.toRestriction.hom =
      F.restrictionGraph.hom ≫ (fiberProductSnd F.toSourceFibre p).hom :=
    (congrArg (fun k => k.hom) (hsq.lift_snd (𝟙 F.arrows) F.toRestriction
      ((Category.id_comp _).trans F.toRestriction_comp_snd.symm))).symm
  rw [hfac]
  exact isOpenImmersion_comp C S hS _ _ hgraph hsnd

/-- The inverse morphism of the finite part is involutive: a section of `Z_univ` is determined
by its source and its arrow, and inverting twice fixes both, the arrow by involutivity of the
inverse of a groupoid in presheaves. -/
theorem inverseMap_comp_inverseMap (F : FinitePartUniversalOpen G) :
    F.inverseMap.hom ≫ F.inverseMap.hom = 𝟙 F.arrows.obj := by
  ext T a
  refine F.arrows_ext T _ _ ?_ ?_
  · exact (F.inverseMap_source_app T (F.inverseMap.hom.app T a)).trans
      (F.inverseMap_target_app T a)
  · refine (F.inverseMap_arrowMap_app T (F.inverseMap.hom.app T a)).trans ?_
    refine (congrArg (fun z => Deformation.inverseArrow G.toGroupoidInFunctors T z)
      (F.inverseMap_arrowMap_app T a)).trans ?_
    exact Deformation.inverseArrow_inverseArrow G.toGroupoidInFunctors T
      (F.arrowMap.hom.app T a)

/-- The inverse morphism of the finite part is an isomorphism, being its own inverse. -/
instance isIso_inverseMap_hom (F : FinitePartUniversalOpen G) : IsIso F.inverseMap.hom :=
  ⟨F.inverseMap.hom, F.inverseMap_comp_inverseMap, F.inverseMap_comp_inverseMap⟩

/-- **The target morphism `t' : Z_univ ⟶ U'` of the finite part is finite**, which is the
target half of the second step of the proof of Stacks 03FM.  The inverse of the finite part is an
isomorphism carrying `s'` to `t'`, so `t'` is an isomorphism followed by the finite `s'`. -/
theorem target_finite (F : FinitePartUniversalOpen G) :
    IsFinite C S hS F.target.hom := by
  rw [← congrArg (fun k : F.arrows ⟶ F.objects => k.hom) F.inverseMap_comp_source]
  exact isFinite_isIso_comp F.inverseMap.hom F.source_finite

/-- `Z_univ ⟶ R'` is a monomorphism, being an open immersion of algebraic spaces. -/
instance mono_toRestriction (F : FinitePartUniversalOpen G) : Mono F.toRestriction.hom :=
  mono_of_presheaf_isOpenImmersion F.isOpenImmersion_toRestriction

/-- `Z_univ ⟶ R'` followed by the source of the restriction is the source `s'`, stated for the
underlying morphisms of presheaves. -/
theorem toRestriction_hom_comp_source (F : FinitePartUniversalOpen G) :
    F.toRestriction.hom ≫
        (G.restrict F.objectProjection).groupoid.source.hom =
      F.source.hom :=
  congrArg (fun k : F.arrows ⟶ F.objects => k.hom) F.toRestriction_comp_restrictionSource

/-- `Z_univ ⟶ R'` followed by the target of the restriction is the target `t'`, stated for the
underlying morphisms of presheaves. -/
theorem toRestriction_hom_comp_target (F : FinitePartUniversalOpen G) :
    F.toRestriction.hom ≫
        (G.restrict F.objectProjection).groupoid.target.hom =
      F.target.hom :=
  congrArg (fun k : F.arrows ⟶ F.objects => k.hom) F.toRestriction_comp_restrictionTarget

/-- **`Z_univ`, read inside the arrow space of `R|_{U'}`, is an open subspace**: its image
subfunctor is an open subspace because `Z_univ ⟶ R'` is an open immersion of algebraic
spaces. -/
theorem isOpenSubspace_range_toRestriction (F : FinitePartUniversalOpen G) :
    IsOpenSubspace C S hS (Subfunctor.range F.toRestriction.hom) :=
  isOpenSubspace_range_of_isAlgebraicSpace C S hS F.arrows.property _
    F.isOpenImmersion_toRestriction

/-- Evaluating a commuting triangle `f ≫ g = h` of presheaves at a section. -/
private theorem app_comp_eq_of_comp_eq {A B D : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {f : A ⟶ B} {g : B ⟶ D} {h : A ⟶ D} (e : f ≫ g = h) (T : (BigFppfOver C S hS)ᵒᵖ) (x : A.obj T) :
    g.app T (f.app T x) = h.app T x :=
  congrArg (fun k => k.app T x) e

/-- A morphism out of the arrow space of `R|_{U'}` which restricts along `Z_univ ⟶ R'` to `m`
restricts along the inclusion of the image of `Z_univ` to the inverse of the isomorphism of
`Z_univ` with its image followed by `m`. -/
private theorem range_ι_comp_eq_inv_comp (F : FinitePartUniversalOpen G)
    {X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u}
    {k : (GroupoidInAlgebraicSpaces.restrictionArrows G F.objectProjection).obj ⟶ X}
    {m : F.arrows.obj ⟶ X}
    (h : F.toRestriction.hom ≫ k = m) :
    (Subfunctor.range F.toRestriction.hom).ι ≫ k =
      (rangeIsoOfMono C S hS F.toRestriction.hom).inv ≫ m :=
  by rw [← h, ← Category.assoc, rangeIsoOfMono_inv_comp]

/-- The inclusion of the image of `Z_univ` followed by the source of `R|_{U'}` is the source
`s'` of the finite part, read through the isomorphism of `Z_univ` with its image. -/
theorem range_ι_comp_source (F : FinitePartUniversalOpen G) :
    (Subfunctor.range F.toRestriction.hom).ι ≫
        (G.restrict F.objectProjection).groupoid.source.hom =
      (rangeIsoOfMono C S hS F.toRestriction.hom).inv ≫ F.source.hom :=
  F.range_ι_comp_eq_inv_comp F.toRestriction_hom_comp_source

/-- The inclusion of the image of `Z_univ` followed by the target of `R|_{U'}` is the target
`t'` of the finite part, read through the isomorphism of `Z_univ` with its image. -/
theorem range_ι_comp_target (F : FinitePartUniversalOpen G) :
    (Subfunctor.range F.toRestriction.hom).ι ≫
        (G.restrict F.objectProjection).groupoid.target.hom =
      (rangeIsoOfMono C S hS F.toRestriction.hom).inv ≫ F.target.hom :=
  F.range_ι_comp_eq_inv_comp F.toRestriction_hom_comp_target

/-- **The restricted source of the image of `Z_univ` in `R|_{U'}` is finite**, which is the
`source_finite` condition of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid`. -/
theorem range_source_finite (F : FinitePartUniversalOpen G) :
    IsFinite C S hS ((Subfunctor.range F.toRestriction.hom).ι ≫
      (G.restrict F.objectProjection).groupoid.source.hom) := by
  rw [F.range_ι_comp_source]
  exact isFinite_isIso_comp _ F.source_finite

/-- **The restricted target of the image of `Z_univ` in `R|_{U'}` is finite**, which is the
`target_finite` condition of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid`. -/
theorem range_target_finite (F : FinitePartUniversalOpen G) :
    IsFinite C S hS ((Subfunctor.range F.toRestriction.hom).ι ≫
      (G.restrict F.objectProjection).groupoid.target.hom) := by
  rw [F.range_ι_comp_target]
  exact isFinite_isIso_comp _ F.target_finite

/-! ### Composition -/

/-- The first projection of the fibre product reads off the first entry of a composable
pair. -/
theorem composableToPullback_app_fst {U R : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (s t : R ⟶ U)
    (T : (BigFppfOver C S hS)ᵒᵖ) (p : (Deformation.composableArrows U R s t).obj T) :
    (pullback.fst s t).app T ((AlgebraicGeometry.composableToPullback s t).app T p) =
      p.1.1 :=
  congrArg (fun k : Deformation.composableArrows U R s t ⟶ R => k.app T p)
    (pullback.lift_fst _ _ _)

/-- The second projection of the fibre product reads off the second entry of a composable
pair. -/
theorem composableToPullback_app_snd {U R : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} (s t : R ⟶ U)
    (T : (BigFppfOver C S hS)ᵒᵖ) (p : (Deformation.composableArrows U R s t).obj T) :
    (pullback.snd s t).app T ((AlgebraicGeometry.composableToPullback s t).app T p) =
      p.1.2 :=
  congrArg (fun k : Deformation.composableArrows U R s t ⟶ R => k.app T p)
    (pullback.lift_snd _ _ _)

/-- The first projection of the fibre product of algebraic spaces reads off the first entry of
a composable pair. -/
theorem composableToPullback_app_fiberProductFst {X Y : AlgebraicSpaces C S hS} (s t : Y ⟶ X)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows X.obj Y.obj s.hom t.hom).obj T) :
    (fiberProductFst s t).hom.app T
        ((AlgebraicGeometry.composableToPullback s.hom t.hom).app T p) = p.1.1 :=
  congrArg (fun k : Deformation.composableArrows X.obj Y.obj s.hom t.hom ⟶ Y.obj => k.app T p)
    (pullback.lift_fst _ _ _)

/-- The second projection of the fibre product of algebraic spaces reads off the second entry
of a composable pair. -/
theorem composableToPullback_app_fiberProductSnd {X Y : AlgebraicSpaces C S hS} (s t : Y ⟶ X)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows X.obj Y.obj s.hom t.hom).obj T) :
    (fiberProductSnd s t).hom.app T
        ((AlgebraicGeometry.composableToPullback s.hom t.hom).app T p) = p.1.2 :=
  congrArg (fun k : Deformation.composableArrows X.obj Y.obj s.hom t.hom ⟶ Y.obj => k.app T p)
    (pullback.lift_snd _ _ _)

/-- Two sections of the arrow space of a restriction which have the same source lift, the same
underlying arrow of the ambient groupoid and the same target lift are equal: those three are the
components of the bijection of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.restrictionArrowDataEquiv`. -/
theorem restrictionArrows_ext {U' : AlgebraicSpaces C S hS} (g : U' ⟶ G.objects)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (z₁ z₂ : (GroupoidInAlgebraicSpaces.restrictionArrows G g).obj.obj T)
    (hs : (GroupoidInAlgebraicSpaces.restrictionSource G g).hom.app T z₁ =
      (GroupoidInAlgebraicSpaces.restrictionSource G g).hom.app T z₂)
    (ha : (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G g).hom.app T z₁ =
      (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G g).hom.app T z₂)
    (ht : (GroupoidInAlgebraicSpaces.restrictionTarget G g).hom.app T z₁ =
      (GroupoidInAlgebraicSpaces.restrictionTarget G g).hom.app T z₂) :
    z₁ = z₂ := by
  refine (GroupoidInAlgebraicSpaces.restrictionArrowDataEquiv G g T).injective
    (GroupoidInAlgebraicSpaces.RestrictionArrowData.ext ?_ ?_ ?_)
  · rw [GroupoidInAlgebraicSpaces.restrictionArrowDataEquiv_source,
      GroupoidInAlgebraicSpaces.restrictionArrowDataEquiv_source]
    exact hs
  · rw [GroupoidInAlgebraicSpaces.restrictionArrowDataEquiv_arrow,
      GroupoidInAlgebraicSpaces.restrictionArrowDataEquiv_arrow]
    exact ha
  · rw [GroupoidInAlgebraicSpaces.restrictionArrowDataEquiv_target,
      GroupoidInAlgebraicSpaces.restrictionArrowDataEquiv_target]
    exact ht

/-- Composable pairs of sections of `Z_univ` read inside `R|_{U'}` are the same as composable
pairs of sections of `Z_univ`: the comparison transports each component back along the
isomorphism of `Z_univ` with its image, and composability is preserved because the restricted
source and target of the image are the source and target of the finite part. -/
def composableTransport (F : FinitePartUniversalOpen G) :
    Deformation.composableArrows F.objects.obj
        (Subfunctor.range F.toRestriction.hom).toFunctor
        ((Subfunctor.range F.toRestriction.hom).ι ≫
          (G.restrict F.objectProjection).groupoid.source.hom)
        ((Subfunctor.range F.toRestriction.hom).ι ≫
          (G.restrict F.objectProjection).groupoid.target.hom) ⟶
      Deformation.composableArrows F.objects.obj F.arrows.obj F.source.hom F.target.hom where
  app T := ↾ fun p =>
    ⟨((rangeIsoOfMono C S hS F.toRestriction.hom).inv.app T p.1.1,
      (rangeIsoOfMono C S hS F.toRestriction.hom).inv.app T p.1.2),
      (congrArg (fun k => k.app T p.1.1) F.range_ι_comp_source).symm.trans
        (p.2.trans (congrArg (fun k => k.app T p.1.2) F.range_ι_comp_target))⟩
  naturality := by
    intro T T' f
    ext p
    refine Subtype.ext (Prod.ext ?_ ?_)
    · exact congrArg (fun k => k p.1.1)
        ((rangeIsoOfMono C S hS F.toRestriction.hom).inv.naturality f)
    · exact congrArg (fun k => k p.1.2)
        ((rangeIsoOfMono C S hS F.toRestriction.hom).inv.naturality f)

/-- The composition law carried by the image of `Z_univ` in the arrow space of `R|_{U'}`: a
composable pair is transported back to `Z_univ`, composed there, and its composite transported
forward again. -/
def subgroupoidComp (F : FinitePartUniversalOpen G) :
    Deformation.composableArrows F.objects.obj
        (Subfunctor.range F.toRestriction.hom).toFunctor
        ((Subfunctor.range F.toRestriction.hom).ι ≫
          (G.restrict F.objectProjection).groupoid.source.hom)
        ((Subfunctor.range F.toRestriction.hom).ι ≫
          (G.restrict F.objectProjection).groupoid.target.hom) ⟶
      (Subfunctor.range F.toRestriction.hom).toFunctor :=
  F.composableTransport ≫
    (AlgebraicGeometry.composableToPullback F.source.hom F.target.hom ≫ F.comp.hom) ≫
    Subfunctor.toRange F.toRestriction.hom

/-- **`Z_univ ⟶ R'` carries the composition of the finite part to the composition of
`R|_{U'}`.**  Both sides are sections of the arrow space of a restriction, so it is enough to
compare their three components: the source of a composite in `R|_{U'}` is the source of the
second factor and the source of a composite in the finite part is the source of the second
factor, dually for the target, and the underlying arrow of a composite in `R|_{U'}` is the
composite in `R` of the two underlying arrows, which is what the arrow of a composite in the
finite part is. -/
theorem toRestriction_app_compAt (F : FinitePartUniversalOpen G)
    (T : (BigFppfOver C S hS)ᵒᵖ) (a b : F.arrows.obj.obj T)
    (h : F.source.hom.app T a = F.target.hom.app T b)
    (h' : (G.restrict F.objectProjection).groupoid.source.hom.app T
        (F.toRestriction.hom.app T a) =
      (G.restrict F.objectProjection).groupoid.target.hom.app T
        (F.toRestriction.hom.app T b)) :
    F.toRestriction.hom.app T (F.compAt T a b h) =
      (G.restrict F.objectProjection).groupoid.toGroupoidInFunctors.comp.app T
        ⟨(F.toRestriction.hom.app T a, F.toRestriction.hom.app T b), h'⟩ := by
  have es : ∀ x : F.arrows.obj.obj T,
      (GroupoidInAlgebraicSpaces.restrictionSource G F.objectProjection).hom.app T
        (F.toRestriction.hom.app T x) = F.source.hom.app T x :=
    app_comp_eq_of_comp_eq F.toRestriction_hom_comp_source T
  have et : ∀ x : F.arrows.obj.obj T,
      (GroupoidInAlgebraicSpaces.restrictionTarget G F.objectProjection).hom.app T
        (F.toRestriction.hom.app T x) = F.target.hom.app T x :=
    app_comp_eq_of_comp_eq F.toRestriction_hom_comp_target T
  have ea : ∀ x : F.arrows.obj.obj T,
      (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G F.objectProjection).hom.app T
        (F.toRestriction.hom.app T x) = F.arrowMap.hom.app T x :=
    app_comp_eq_of_comp_eq
      (congrArg (fun k : F.arrows ⟶ G.arrows => k.hom) F.toRestriction_comp_arrowsToArrows) T
  have ecomp :
      (G.restrict F.objectProjection).groupoid.toGroupoidInFunctors.comp.app T
        ⟨(F.toRestriction.hom.app T a, F.toRestriction.hom.app T b), h'⟩ =
      (GroupoidInAlgebraicSpaces.restrictionCompositionData G F.objectProjection).hom.hom.app T
        ((AlgebraicGeometry.composableToPullback
            (GroupoidInAlgebraicSpaces.restrictionSource G F.objectProjection).hom
            (GroupoidInAlgebraicSpaces.restrictionTarget G F.objectProjection).hom).app T
          ⟨(F.toRestriction.hom.app T a, F.toRestriction.hom.app T b), h'⟩) := rfl
  have hc : G.source.hom.app T (F.arrowMap.hom.app T a) =
      G.target.hom.app T (F.arrowMap.hom.app T b) :=
    (F.objectProjection_source_app T a).symm.trans
      (((congrArg (F.objectProjection.hom.app T) h).trans
        (F.objectProjection_target_app T b)))
  have hzsrc := GroupoidInAlgebraicSpaces.restrictionCompositionData_hom_source_app G
    F.objectProjection T ((AlgebraicGeometry.composableToPullback
        (GroupoidInAlgebraicSpaces.restrictionSource G F.objectProjection).hom
        (GroupoidInAlgebraicSpaces.restrictionTarget G F.objectProjection).hom).app T
      ⟨(F.toRestriction.hom.app T a, F.toRestriction.hom.app T b), h'⟩)
  have hztgt := GroupoidInAlgebraicSpaces.restrictionCompositionData_hom_target_app G
    F.objectProjection T ((AlgebraicGeometry.composableToPullback
        (GroupoidInAlgebraicSpaces.restrictionSource G F.objectProjection).hom
        (GroupoidInAlgebraicSpaces.restrictionTarget G F.objectProjection).hom).app T
      ⟨(F.toRestriction.hom.app T a, F.toRestriction.hom.app T b), h'⟩)
  have hzarr := GroupoidInAlgebraicSpaces.restrictionCompositionData_hom_arrow_app G
    F.objectProjection T ((AlgebraicGeometry.composableToPullback
        (GroupoidInAlgebraicSpaces.restrictionSource G F.objectProjection).hom
        (GroupoidInAlgebraicSpaces.restrictionTarget G F.objectProjection).hom).app T
      ⟨(F.toRestriction.hom.app T a, F.toRestriction.hom.app T b), h'⟩)
  have hzund := GroupoidInAlgebraicSpaces.restrictionCompositionData_underlying_comp_app G
    F.objectProjection T ((AlgebraicGeometry.composableToPullback
        (GroupoidInAlgebraicSpaces.restrictionSource G F.objectProjection).hom
        (GroupoidInAlgebraicSpaces.restrictionTarget G F.objectProjection).hom).app T
      ⟨(F.toRestriction.hom.app T a, F.toRestriction.hom.app T b), h'⟩)
  refine restrictionArrows_ext F.objectProjection T _ _ ?_ ?_ ?_
  · rw [es, F.compAt_source, ecomp, hzsrc, composableToPullback_app_fiberProductSnd, es]
  · rw [ea, F.compAt_arrowMap T a b h hc, ecomp, hzarr, hzund]
    refine congrArg (fun q => G.toGroupoidInFunctors.comp.app T q)
      (Subtype.ext (Prod.ext ?_ ?_))
    · exact ((congrArg (fun x => (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G
        F.objectProjection).hom.app T x)
        (composableToPullback_app_fiberProductFst _ _ T _)).trans (ea a)).symm
    · exact ((congrArg (fun x => (GroupoidInAlgebraicSpaces.restrictionArrowsToArrows G
        F.objectProjection).hom.app T x)
        (composableToPullback_app_fiberProductSnd _ _ T _)).trans (ea b)).symm
  · rw [et, F.compAt_target, ecomp, hztgt, composableToPullback_app_fiberProductFst, et]

/-- **The composition carried by the image of `Z_univ` is the restriction of the composition of
`R|_{U'}`**, which is the `comp_restricts` condition of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid`.  This is
`AlgebraicGeometry.Space.FinitePartUniversalOpen.toRestriction_app_compAt` read through the
isomorphism of `Z_univ` with its image. -/
theorem subgroupoidComp_restricts (F : FinitePartUniversalOpen G)
    (T : (BigFppfOver C S hS)ᵒᵖ)
    (p : (Deformation.composableArrows F.objects.obj
      (Subfunctor.range F.toRestriction.hom).toFunctor
      ((Subfunctor.range F.toRestriction.hom).ι ≫
        (G.restrict F.objectProjection).groupoid.source.hom)
      ((Subfunctor.range F.toRestriction.hom).ι ≫
        (G.restrict F.objectProjection).groupoid.target.hom)).obj T) :
    (Subfunctor.range F.toRestriction.hom).ι.app T (F.subgroupoidComp.app T p) =
      (G.restrict F.objectProjection).groupoid.toGroupoidInFunctors.comp.app T
        ⟨((Subfunctor.range F.toRestriction.hom).ι.app T p.1.1,
          (Subfunctor.range F.toRestriction.hom).ι.app T p.1.2), p.2⟩ := by
  have hι : ∀ x : (Subfunctor.range F.toRestriction.hom).toFunctor.obj T,
      (Subfunctor.range F.toRestriction.hom).ι.app T x =
        F.toRestriction.hom.app T ((rangeIsoOfMono C S hS F.toRestriction.hom).inv.app T x) :=
    fun x => (app_comp_eq_of_comp_eq (rangeIsoOfMono_inv_comp C S hS F.toRestriction.hom) T x).symm
  have hab := (F.composableTransport.app T p).2
  have hab' : (G.restrict F.objectProjection).groupoid.source.hom.app T
        (F.toRestriction.hom.app T
          ((rangeIsoOfMono C S hS F.toRestriction.hom).inv.app T p.1.1)) =
      (G.restrict F.objectProjection).groupoid.target.hom.app T
        (F.toRestriction.hom.app T
          ((rangeIsoOfMono C S hS F.toRestriction.hom).inv.app T p.1.2)) :=
    (congrArg ((GroupoidInAlgebraicSpaces.restrict G
        F.objectProjection).groupoid.source.hom.app T) (hι p.1.1).symm).trans
      (p.2.trans (congrArg ((GroupoidInAlgebraicSpaces.restrict G
        F.objectProjection).groupoid.target.hom.app T) (hι p.1.2)))
  refine Eq.trans ?_ (Eq.trans (F.toRestriction_app_compAt T _ _ hab hab') ?_)
  · exact congrArg (fun k : F.arrows.obj ⟶ _ => k.app T
      (F.compAt T ((rangeIsoOfMono C S hS F.toRestriction.hom).inv.app T p.1.1)
        ((rangeIsoOfMono C S hS F.toRestriction.hom).inv.app T p.1.2) hab))
      (Subfunctor.toRange_ι F.toRestriction.hom)
  · exact congrArg (fun q => (GroupoidInAlgebraicSpaces.restrict G
        F.objectProjection).groupoid.toGroupoidInFunctors.comp.app T q)
      (Subtype.ext (Prod.ext (hι p.1.1).symm (hι p.1.2).symm))

/-- **The image of `Z_univ` in `R|_{U'}` evaluates to a groupoid at every test scheme**, which
is the `pointwiseGroupoid` condition of
`AlgebraicGeometry.GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid`.  The groupoid is the one the
finite part already carries, transported along the bijection of the sections of `Z_univ` with the
sections of its image; the objects are literally the same, and the composition agrees because the
transported composition is the composition of the finite part conjugated by that bijection. -/
theorem subgroupoid_pointwiseGroupoid (F : FinitePartUniversalOpen G)
    (T : (BigFppfOver C S hS)ᵒᵖ) :
    Nonempty (Deformation.PointwiseGroupoid
      (((Subfunctor.range F.toRestriction.hom).ι ≫
        (G.restrict F.objectProjection).groupoid.source.hom).app T)
      (((Subfunctor.range F.toRestriction.hom).ι ≫
        (G.restrict F.objectProjection).groupoid.target.hom).app T)
      (fun q => F.subgroupoidComp.app T q)) := by
  obtain ⟨P⟩ := F.pointwiseGroupoid T
  have hpt : ∀ {X : (BigFppfOver C S hS)ᵒᵖ ⥤ Type u} {k : _ ⟶ X} {m : F.arrows.obj ⟶ X},
      F.toRestriction.hom ≫ k = m → ∀ a : F.arrows.obj.obj T,
        (Subfunctor.toRange F.toRestriction.hom ≫ (Subfunctor.range F.toRestriction.hom).ι ≫
          k).app T a = m.app T a :=
    fun h a => app_comp_eq_of_comp_eq
      ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) (Subfunctor.toRange_ι F.toRestriction.hom)).trans h)) T a
  have hsrc := hpt F.toRestriction_hom_comp_source
  have htgt := hpt F.toRestriction_hom_comp_target
  have hinv : ∀ u : F.arrows.obj.obj T,
      (rangeIsoOfMono C S hS F.toRestriction.hom).inv.app T
        ((Subfunctor.toRange F.toRestriction.hom).app T u) = u :=
    app_comp_eq_of_comp_eq (rangeIsoOfMono C S hS F.toRestriction.hom).hom_inv_id T
  have hhom : ∀ b : (Subfunctor.range F.toRestriction.hom).toFunctor.obj T,
      (Subfunctor.toRange F.toRestriction.hom).app T
        ((rangeIsoOfMono C S hS F.toRestriction.hom).inv.app T b) = b :=
    app_comp_eq_of_comp_eq (rangeIsoOfMono C S hS F.toRestriction.hom).inv_hom_id T
  refine ⟨{ groupoid := P.groupoid
            arrowEquiv := fun x y => (P.arrowEquiv x y).trans
              { toFun := fun a => ⟨(Subfunctor.toRange F.toRestriction.hom).app T a.1,
                  (hsrc a.1).trans a.2.1, (htgt a.1).trans a.2.2⟩
                invFun := fun b => ⟨(rangeIsoOfMono C S hS F.toRestriction.hom).inv.app T b.1,
                  (hsrc _).symm.trans ((congrArg (fun z => ((Subfunctor.range
                      F.toRestriction.hom).ι ≫ (GroupoidInAlgebraicSpaces.restrict G
                      F.objectProjection).groupoid.source.hom).app T z)
                    (hhom b.1)).trans b.2.1),
                  (htgt _).symm.trans ((congrArg (fun z => ((Subfunctor.range
                      F.toRestriction.hom).ι ≫ (GroupoidInAlgebraicSpaces.restrict G
                      F.objectProjection).groupoid.target.hom).app T z)
                    (hhom b.1)).trans b.2.2)⟩
                left_inv := fun a => Subtype.ext (hinv a.1)
                right_inv := fun b => Subtype.ext (hhom b.1) }
            comp_eq := ?_ }⟩
  intro x y z g f
  refine Eq.trans (congrArg
    (fun u => (Subfunctor.toRange F.toRestriction.hom).app T u) (P.comp_eq g f)) ?_
  exact congrArg (fun q => (Subfunctor.toRange F.toRestriction.hom).app T
      ((AlgebraicGeometry.composableToPullback F.source.hom F.target.hom ≫ F.comp.hom).app T q))
    (Subtype.ext (Prod.ext (hinv _).symm (hinv _).symm))

/-- **`Z_univ` as an open finite subgroupoid of the restriction `R|_{U'}`.**  This is conditions
(a) and (b) of Stacks 04RK for the restriction of a groupoid in algebraic spaces to the object
space of its finite part: the image of `Z_univ` in the arrow space of `R|_{U'}` is an open
subspace, its restricted source and target are finite, it is closed under the composition of
`R|_{U'}`, and it evaluates to a groupoid at every test scheme.

It is **not** a splitting of `R|_{U'}` at any point: the containment of the arrows over a point
in `Z_univ`, which is the splitting condition proper, is not proved — see the implementation
notes of this file. -/
def restrictedSubgroupoid (F : FinitePartUniversalOpen G) :
    GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
      (G.restrict F.objectProjection).groupoid where
  arrows := Subfunctor.range F.toRestriction.hom
  arrows_open := F.isOpenSubspace_range_toRestriction
  source_finite := F.range_source_finite
  target_finite := F.range_target_finite
  comp := F.subgroupoidComp
  comp_restricts := F.subgroupoidComp_restricts
  pointwiseGroupoid := F.subgroupoid_pointwiseGroupoid

end FinitePartUniversalOpen

/-- **In the strong splitting situation of Stacks 04RL there are an algebraic space `U'`, an
étale morphism `g : U' ⟶ U` and an open finite subgroupoid of the restriction `R|_{U'}`.**

`U'` is the object space of the finite part of Stacks 04RU, `g` its étale projection, and the
subgroupoid is the universal open `Z_univ` read inside `R|_{U'}`.

This is **weaker than Stacks 03FM**, whose assertion is that `R|_{U'}` is *strongly split* over a
point `u'` over `u`: an open finite subgroupoid is conditions (a) and (b) of Stacks 04RK, and the
splitting condition — that every arrow of `R|_{U'}` with both endpoints `u'` lies in the
subgroupoid — is not proved.  The point `u'` itself is produced by
`AlgebraicGeometry.Space.etaleLocalFibrePoint` and
`AlgebraicGeometry.Space.lies_over_fibrePoint`, and is not mentioned here, which is why the
finiteness and quasi-finiteness hypotheses of Situation 04RL are unused. -/
theorem exists_openFiniteSubgroupoid_of_strongSplittingSituation
    (D : StrongSplittingSituation.{u})
    (C : BigFppfSite.{u}) (hS : C.Contains D.S)
    (hU : C.Contains D.groupoid.objects.left)
    (hR : C.Contains D.groupoid.arrows.left)
    (hP : C.Contains (pullback D.groupoid.source D.groupoid.target).left) :
    ∃ (U' : AlgebraicSpaces C D.S hS)
      (g : U' ⟶ (D.groupoid.realization C hS hU hR hP).objects),
      IsEtale C D.S hS g.hom ∧
      Nonempty (GroupoidInAlgebraicSpaces.OpenFiniteSubgroupoid
        (GroupoidInAlgebraicSpaces.restrict
          (D.groupoid.realization C hS hU hR hP) g).groupoid) :=
  ⟨(realizationFinitePart D.groupoid C hS hU hR hP).objects,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection,
    (realizationFinitePart D.groupoid C hS hU hR hP).objectProjection_etale,
    ⟨(realizationFinitePart D.groupoid C hS hU hR hP).restrictedSubgroupoid⟩⟩

end AlgebraicGeometry.Space

end
