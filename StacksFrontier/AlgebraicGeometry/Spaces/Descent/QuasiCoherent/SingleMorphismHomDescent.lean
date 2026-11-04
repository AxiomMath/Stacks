module

public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.EtaleComparisonRepresentable
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.PairChartNaturality
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.SingleMemberFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.FibreDegreeStratification
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedZariskiRestriction

/-!
# Descent of morphisms of modules along one surjective étale morphism

Let `X` be an algebraic space over a scheme `S` and let `g : Y ⟶ X` be a relatively
representable surjective étale morphism of algebraic spaces.  This file proves descent of
morphisms of `𝒪_X`-modules along `g`: a morphism `ψ : g^*M ⟶ g^*N` of the inverse images which is
compatible with the canonical comparison of Stacks 04W5 at *every* pair of morphisms into `Y`
with equal composites to `X` is the inverse image of a morphism `M ⟶ N`.

This is the fullness half of Stacks 04W6 for the one-member covering `{g}`, and it carries
nothing: relative representability of `g` gives the compatibility of the comparison of
Stacks 03LU with étale restriction at the pairs the proof reads the condition at, by
`AlgebraicGeometry.Space.QuasiCoherentDescent.etaleRestrictionComp_of_representable`.

## The test space is the chart, not a fibre product

`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_single` asks for the
naturality of the étale form of `ψ` on sections, in an arbitrary morphism `k` of the induced
charts of `X`.  For a *family* of étale morphisms that naturality is extracted from the pairwise
condition of Stacks 04W3 on the fibre products `Y i ×_X Y j`, which is what
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/PairChartNaturality.lean` does: a
chart of `Y i ×_X Y j` factoring `k` has to be built, as the universal morphism into a fibre
product of presheaves.

Here the hypothesis is available at *every* pair of morphisms into `Y` with equal composites to
`X`, and then no fibre product is needed: the two morphisms can be taken out of the chart `V`
itself.  Writing `k : V ≫ g ⟶ V' ≫ g`, the two legs out of the algebraic space represented by
the source of `V` are its own structure morphism `V.1.hom` and the composite
`yoneda.map k.hom.left ≫ V'.1.hom`; their composites with `g` agree because `k` is a morphism
over `X`; and the chart of the test space at which the compatibility is read is the identity
chart, whose comparison with `V` is invertible on the nose rather than a projection of a fibre
product.  Both legs have a represented source, so both are relatively representable, and the
coherence of Stacks 03LU with Stacks 03LW is a theorem at the two pairs the proof uses.

## Main definitions

* `AlgebraicGeometry.Space.QuasiCoherentDescent.chartTestSpace`: the algebraic space represented
  by the source of an étale chart, the test space the compatibility is read at.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.chartLegFst` and `…chartLegSnd`: the two
  morphisms from it to `Y` attached to a morphism of the induced charts of `X`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.LegChartData` bundles the geometry of a test
  space factoring a given morphism of charts of `X`.

## Main results

* `AlgebraicGeometry.Space.QuasiCoherentDescent.chartLeg_condition`: the two legs have equal
  composites to `X`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.nonempty_legChartData`: every morphism of the
  charts of `X` induced by two charts of `Y` is factored by the chart itself.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.etaleForm_naturality_of_dominated`: **the
  compatibility with the canonical comparison of Stacks 04W5 at every pair of morphisms into `Y`
  with equal composites to `X` is the naturality of the étale form on sections**, in an
  arbitrary morphism of the induced charts of `X`.
* `AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_of_dominated`:
  **descent of morphisms of `𝒪_X`-modules along a relatively representable surjective étale
  morphism.**

## Implementation notes

The arrangement is the one of
`StacksFrontier/AlgebraicGeometry/Spaces/Descent/QuasiCoherent/PairChartNaturality.lean`, and for
the same reasons.

Every statement of the transfer mentions only a variable of
`AlgebraicGeometry.Space.QuasiCoherentDescent.LegChartData` and its fields; the concrete test
space, its identity chart and the two legs appear only inside the proof of
`AlgebraicGeometry.Space.QuasiCoherentDescent.nonempty_legChartData`.  Naming them in a statement
instead makes the elaborator rebuild the étaleness of the second leg, which is obtained by
cancellation, inside each `whnf`, and that does not terminate.

The identification of the two charts of `X` that a factoring chart induces is carried by the
structure as a *morphism* `mid` together with the two ways it inverts the transport of sections,
rather than as an equality of charts: the equality holds in two definitionally equal shapes, at
the composite morphisms `a ≫ g` and `b ≫ g` and at the iterated postcompositions, and the two
consumers of it need different ones.

## References

* [Stacks Project, Tag 04W6](https://stacks.math.columbia.edu/tag/04W6)
* [Stacks Project, Tag 04W5](https://stacks.math.columbia.edu/tag/04W5)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 03LW](https://stacks.math.columbia.edu/tag/03LW)
* [Stacks Project, Tag 041E](https://stacks.math.columbia.edu/tag/041E)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space.QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
variable {X Y : AlgebraicSpaces B S hS}

/-! ### The chart of the source as a test space -/

/-- The algebraic space represented by the source of an étale chart of `Y`.  This is the test
space at which the compatibility of a morphism of inverse images with the canonical comparison
of Stacks 04W5 is read; see the module documentation. -/
abbrev chartTestSpace (V : SmallEtale B S hS Y.1) : AlgebraicSpaces B S hS :=
  ⟨yoneda.obj V.1.left, isAlgebraicSpace_yoneda B S hS V.1.left⟩

/-- The first leg: the structure morphism of the chart, as a morphism of algebraic spaces. -/
def chartLegFst (V : SmallEtale B S hS Y.1) : chartTestSpace B S hS V ⟶ Y :=
  ObjectProperty.homMk V.1.hom

/-- The first leg is étale: it is the structure morphism of an étale chart. -/
theorem isEtale_chartLegFst (V : SmallEtale B S hS Y.1) :
    IsEtale B S hS (chartLegFst B S hS V).hom :=
  (isEtale_iff_presheaf_of_yoneda B S hS V.1.hom).2 V.2

variable (g : Y ⟶ X) (hg : IsEtale B S hS g.hom)

/-- The second leg: the morphism of the two chart sources underlying a morphism of the induced
charts of `X`, followed by the structure morphism of the second chart. -/
def chartLegSnd {V V' : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V') :
    chartTestSpace B S hS V ⟶ Y :=
  ObjectProperty.homMk (yoneda.map k.hom.left ≫ V'.1.hom)

/-- **The two legs have equal composites to `X`**: that is the triangle over `X` of the given
morphism of the induced charts. -/
theorem chartLeg_condition {V V' : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V') :
    chartLegFst B S hS V ≫ g = chartLegSnd B S hS g hg k ≫ g := by
  apply ObjectProperty.hom_ext
  exact (CostructuredArrow.w k.hom).symm.trans (Category.assoc _ _ _).symm

/-- The second leg is étale, by cancellation: its composite with `g` is the composite of the
first leg with `g`, which is the structure morphism of an étale chart of `X`. -/
theorem isEtale_chartLegSnd {V V' : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V') :
    IsEtale B S hS (chartLegSnd B S hS g hg k).hom := by
  refine isEtale_of_isEtale_over B S hS (isAlgebraicSpace_yoneda B S hS V.1.left) Y.2 X.2
    (chartLegSnd B S hS g hg k).hom ((chartLegSnd B S hS g hg k).hom ≫ g.hom) g.hom ?_ hg rfl
  exact congrArg (fun m : chartTestSpace B S hS V ⟶ X => IsEtale B S hS m.hom)
      (chartLeg_condition B S hS g hg k) ▸
    isEtale_comp B S hS (isEtale_chartLegFst B S hS V) hg

/-- The identity chart of the test space. -/
abbrev chartTestUnit (V : SmallEtale B S hS Y.1) :
    SmallEtale B S hS (chartTestSpace B S hS V).1 :=
  selfChart B S hS V.1.left

/-! ### Relative representability of a leg -/

/-- A morphism to `Y` out of the space represented by the source of a chart is relatively
representable: its source is a represented presheaf. -/
theorem relativelyRepresentable_legToY (V : SmallEtale B S hS Y.1)
    (a : chartTestSpace B S hS V ⟶ Y) : yoneda.relativelyRepresentable a.hom :=
  relativelyRepresentable_of_isAlgebraicSpace B S hS Y.2 a.hom

/-- A morphism to `X` out of the space represented by the source of a chart is relatively
representable. -/
theorem relativelyRepresentable_legToX (V : SmallEtale B S hS Y.1)
    (a : chartTestSpace B S hS V ⟶ X) : yoneda.relativelyRepresentable a.hom :=
  relativelyRepresentable_of_isAlgebraicSpace B S hS X.2 a.hom

/-! ### The two charts of `X` induced by a chart of a test space -/

/-- The two charts of `X` obtained from a chart of a test space by two legs with equal composites
to `X` are equal. -/
theorem postcomp_leg_eq {P : AlgebraicSpaces B S hS} {a b : P ⟶ Y}
    (ha : IsEtale B S hS a.hom) (hb : IsEtale B S hS b.hom) (hab : a ≫ g = b ≫ g)
    (Z : SmallEtale B S hS P.1) :
    (smallEtalePostcomp B S hS (a ≫ g) (isEtale_comp B S hS ha hg)).obj Z =
      (smallEtalePostcomp B S hS (b ≫ g) (isEtale_comp B S hS hb hg)).obj Z :=
  smallEtalePostcomp_obj_congr B S hS (isEtale_comp B S hS ha hg)
    (isEtale_comp B S hS hb hg) hab Z

/-! ### The identity chart of the chart as a factoring chart -/

/-- The equality of the two charts of `X` that the identity chart of the test space induces along
the two legs attached to `k`. -/
theorem postcomp_chartUnit_eq {V V' : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V') :
    (smallEtalePostcomp B S hS (chartLegFst B S hS V ≫ g)
        (isEtale_comp B S hS (isEtale_chartLegFst B S hS V) hg)).obj
          (chartTestUnit B S hS V) =
      (smallEtalePostcomp B S hS (chartLegSnd B S hS g hg k ≫ g)
        (isEtale_comp B S hS (isEtale_chartLegSnd B S hS g hg k) hg)).obj
          (chartTestUnit B S hS V) :=
  postcomp_leg_eq B S hS g hg (isEtale_chartLegFst B S hS V)
    (isEtale_chartLegSnd B S hS g hg k) (chartLeg_condition B S hS g hg k)
    (chartTestUnit B S hS V)

/-- The same equality, written at the iterated postcompositions rather than at the composite
morphisms.  The two shapes are definitionally equal and both are needed; see the implementation
notes. -/
theorem postcomp_chartUnitIter_eq {V V' : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V') :
    (smallEtalePostcomp B S hS g hg).obj
        ((smallEtalePostcomp B S hS (chartLegFst B S hS V)
          (isEtale_chartLegFst B S hS V)).obj (chartTestUnit B S hS V)) =
      (smallEtalePostcomp B S hS g hg).obj
        ((smallEtalePostcomp B S hS (chartLegSnd B S hS g hg k)
          (isEtale_chartLegSnd B S hS g hg k)).obj (chartTestUnit B S hS V)) :=
  postcomp_chartUnit_eq B S hS g hg k

/-- The chart of `Y` that the identity chart of the test space induces along the first leg maps
to the chart `V` it was built from, by the identity on underlying objects. -/
def chartUnitFst (V : SmallEtale B S hS Y.1) :
    (smallEtalePostcomp B S hS (chartLegFst B S hS V)
        (isEtale_chartLegFst B S hS V)).obj (chartTestUnit B S hS V) ⟶ V :=
  ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 V.1.left)
    (congrArg (fun t => t ≫ V.1.hom) (yoneda.map_id V.1.left)))

/-- That comparison is invertible, by the identity on underlying objects. -/
instance isIso_chartUnitFst (V : SmallEtale B S hS Y.1) :
    IsIso (chartUnitFst B S hS V) := by
  refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk (𝟙 V.1.left)
    (((congrArg (fun t => t ≫ 𝟙 (yoneda.obj V.1.left) ≫ V.1.hom)
          (yoneda.map_id V.1.left)).trans (Category.id_comp _)).trans
      (Category.id_comp V.1.hom))), ?_, ?_⟩ <;>
    apply ObjectProperty.hom_ext <;> apply CostructuredArrow.hom_ext <;>
    exact Category.id_comp _

/-- The chart of `Y` that the identity chart of the test space induces along the second leg maps
to the chart `V'`, by the morphism of chart sources underlying `k`. -/
def chartUnitSnd {V V' : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V') :
    (smallEtalePostcomp B S hS (chartLegSnd B S hS g hg k)
        (isEtale_chartLegSnd B S hS g hg k)).obj (chartTestUnit B S hS V) ⟶ V' :=
  ObjectProperty.homMk (CostructuredArrow.homMk k.hom.left
    (Category.id_comp (yoneda.map k.hom.left ≫ V'.1.hom)).symm)

/-- The identification of the two charts of `X` induced by the identity chart of the test space,
as a *morphism* of charts. -/
def chartMid {V V' : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V') :
    (smallEtalePostcomp B S hS g hg).obj
        ((smallEtalePostcomp B S hS (chartLegFst B S hS V)
          (isEtale_chartLegFst B S hS V)).obj (chartTestUnit B S hS V)) ⟶
      (smallEtalePostcomp B S hS g hg).obj
        ((smallEtalePostcomp B S hS (chartLegSnd B S hS g hg k)
          (isEtale_chartLegSnd B S hS g hg k)).obj (chartTestUnit B S hS V)) :=
  eqToHom (postcomp_chartUnitIter_eq B S hS g hg k)

/-- The two comparisons factor the given morphism `k` of charts of `X` through the identification
of the two induced charts. -/
theorem postcomp_chartUnitFst_comp {V V' : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V') :
    (smallEtalePostcomp B S hS g hg).map (chartUnitFst B S hS V) ≫ k =
      chartMid B S hS g hg k ≫
        (smallEtalePostcomp B S hS g hg).map (chartUnitSnd B S hS g hg k) := by
  apply ObjectProperty.hom_ext
  apply CostructuredArrow.hom_ext
  rw [chartMid, eqToHom_comp_hom_left]
  rfl

/-- Transport along the equality of the two induced charts of `X` undoes restriction along
`AlgebraicGeometry.Space.QuasiCoherentDescent.chartMid`. -/
theorem eqToHom_val_map_chartMid {V V' : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V')
    (M : Modules.{u, u} B S hS X.1 X.2)
    (z : M.val.obj (.op ((smallEtalePostcomp B S hS (chartLegSnd B S hS g hg k ≫ g)
      (isEtale_comp B S hS (isEtale_chartLegSnd B S hS g hg k) hg)).obj
        (chartTestUnit B S hS V)))) :
    eqToHom (congrArg (fun W : SmallEtale B S hS X.1 => M.val.presheaf.obj (.op W))
        (postcomp_chartUnit_eq B S hS g hg k))
      (M.val.map (chartMid B S hS g hg k).op z) = z :=
  eqToHom_val_map_eqToHom_of_eq B S hS (postcomp_chartUnitIter_eq B S hS g hg k)
    (postcomp_chartUnit_eq B S hS g hg k) M z

/-- Restriction along `AlgebraicGeometry.Space.QuasiCoherentDescent.chartMid` undoes the
transport along the equality of the two induced charts of `X`. -/
theorem val_map_chartMid_eqToHom {V V' : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V')
    (M : Modules.{u, u} B S hS X.1 X.2)
    (t : M.val.obj (.op ((smallEtalePostcomp B S hS (chartLegFst B S hS V ≫ g)
      (isEtale_comp B S hS (isEtale_chartLegFst B S hS V) hg)).obj
        (chartTestUnit B S hS V)))) :
    M.val.map (chartMid B S hS g hg k).op
      (eqToHom (congrArg (fun W : SmallEtale B S hS X.1 => M.val.presheaf.obj (.op W))
        (postcomp_chartUnit_eq B S hS g hg k)) t) = t :=
  val_map_eqToHom_eqToHom_of_eq B S hS (postcomp_chartUnitIter_eq B S hS g hg k)
    (postcomp_chartUnit_eq B S hS g hg k) M t

/-! ### The factoring datum -/

/-- The geometry of a test space and a chart of it factoring a morphism `k` of the charts of `X`
induced by two charts `V`, `V'` of `Y`: the space, the two legs to `Y` with their étaleness,
their equal composites to `X` and the coherence of Stacks 03LU at each of them, the chart, its
two comparisons with `V` and `V'`, the invertibility of the first one, the identification `mid`
of the two charts of `X` that the chart induces, and the factorization of `k`.

The declarations below mention only a variable of this structure and its fields; see the
implementation notes. -/
structure LegChartData (V V' : SmallEtale B S hS Y.1)
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V') where
  /-- The test space. -/
  space : AlgebraicSpaces B S hS
  /-- The first leg. -/
  legFst : space ⟶ Y
  /-- The second leg. -/
  legSnd : space ⟶ Y
  /-- Étaleness of the first leg. -/
  isEtale_legFst : IsEtale B S hS legFst.hom
  /-- Étaleness of the second leg. -/
  isEtale_legSnd : IsEtale B S hS legSnd.hom
  /-- The two legs have equal composites to `X`. -/
  leg_condition : legFst ≫ g = legSnd ≫ g
  /-- The coherence of Stacks 03LU with étale restriction at the first leg and `g`. -/
  restrictionComp_legFst : EtaleRestrictionComp B S hS legFst g isEtale_legFst hg
    (isEtale_comp B S hS isEtale_legFst hg)
  /-- The coherence of Stacks 03LU with étale restriction at the second leg and `g`. -/
  restrictionComp_legSnd : EtaleRestrictionComp B S hS legSnd g isEtale_legSnd hg
    (isEtale_comp B S hS isEtale_legSnd hg)
  /-- The chart of the test space. -/
  obj : SmallEtale B S hS space.1
  /-- Its comparison, through the first leg, with the given chart `V`. -/
  fst : (smallEtalePostcomp B S hS legFst isEtale_legFst).obj obj ⟶ V
  /-- Its comparison, through the second leg, with the given chart `V'`. -/
  snd : (smallEtalePostcomp B S hS legSnd isEtale_legSnd).obj obj ⟶ V'
  /-- The first comparison is invertible. -/
  isIso_fst : IsIso fst
  /-- The identification of the chart of `X` under the first leg with the one under the
  second. -/
  mid : (smallEtalePostcomp B S hS g hg).obj
        ((smallEtalePostcomp B S hS legFst isEtale_legFst).obj obj) ⟶
      (smallEtalePostcomp B S hS g hg).obj
        ((smallEtalePostcomp B S hS legSnd isEtale_legSnd).obj obj)
  /-- The two comparisons factor `k` through the identification. -/
  postcomp_comp : (smallEtalePostcomp B S hS g hg).map fst ≫ k =
      mid ≫ (smallEtalePostcomp B S hS g hg).map snd
  /-- Transport along the equality of the two charts of `X` undoes restriction along `mid`. -/
  eqToHom_val_map_mid : ∀ (M : Modules.{u, u} B S hS X.1 X.2)
      (z : M.val.obj (.op ((smallEtalePostcomp B S hS (legSnd ≫ g)
        (isEtale_comp B S hS isEtale_legSnd hg)).obj obj))),
    eqToHom (congrArg (fun W : SmallEtale B S hS X.1 => M.val.presheaf.obj (.op W))
        (postcomp_leg_eq B S hS g hg isEtale_legFst isEtale_legSnd leg_condition obj))
      (M.val.map mid.op z) = z
  /-- Restriction along `mid` undoes the transport along the equality of the two charts. -/
  val_map_mid_eqToHom : ∀ (M : Modules.{u, u} B S hS X.1 X.2)
      (t : M.val.obj (.op ((smallEtalePostcomp B S hS (legFst ≫ g)
        (isEtale_comp B S hS isEtale_legFst hg)).obj obj))),
    M.val.map mid.op (eqToHom (congrArg (fun W : SmallEtale B S hS X.1 =>
      M.val.presheaf.obj (.op W))
        (postcomp_leg_eq B S hS g hg isEtale_legFst isEtale_legSnd leg_condition obj)) t) = t

variable (hrep : yoneda.relativelyRepresentable g.hom)

include hrep in
/-- **Every morphism of the charts of `X` induced by two charts of `Y` is factored by the first
chart itself.**  The test space is the algebraic space represented by the source of `V`, the two
legs are `AlgebraicGeometry.Space.QuasiCoherentDescent.chartLegFst` and `…chartLegSnd`, and the
chart is the identity chart; the comparison with `V` is the identity on underlying objects, hence
invertible. -/
theorem nonempty_legChartData {V V' : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V') :
    Nonempty (LegChartData B S hS g hg V V' k) :=
  have restrictionComp (a : chartTestSpace B S hS V ⟶ Y) (ha : IsEtale B S hS a.hom) :
      EtaleRestrictionComp B S hS a g ha hg (isEtale_comp B S hS ha hg) :=
    etaleRestrictionComp_of_representable B S hS a g ha hg _
      (relativelyRepresentable_legToY B S hS V a) hrep
      (relativelyRepresentable_legToX B S hS V (a ≫ g))
  ⟨{ space := chartTestSpace B S hS V
     legFst := chartLegFst B S hS V
     legSnd := chartLegSnd B S hS g hg k
     isEtale_legFst := isEtale_chartLegFst B S hS V
     isEtale_legSnd := isEtale_chartLegSnd B S hS g hg k
     leg_condition := chartLeg_condition B S hS g hg k
     restrictionComp_legFst := restrictionComp _ (isEtale_chartLegFst B S hS V)
     restrictionComp_legSnd := restrictionComp _ (isEtale_chartLegSnd B S hS g hg k)
     obj := chartTestUnit B S hS V
     fst := chartUnitFst B S hS V
     snd := chartUnitSnd B S hS g hg k
     isIso_fst := isIso_chartUnitFst B S hS V
     mid := chartMid B S hS g hg k
     postcomp_comp := postcomp_chartUnitFst_comp B S hS g hg k
     eqToHom_val_map_mid := eqToHom_val_map_chartMid B S hS g hg k
     val_map_mid_eqToHom := val_map_chartMid_eqToHom B S hS g hg k }⟩

/-! ### Naturality of the étale form -/

variable {M N : Modules.{u, u} B S hS X.1 X.2}

/-- **The compatibility with the canonical comparison of Stacks 04W5 at the two legs, read on
sections over the factoring chart.**  The two readings of the étale form of `ψ` agree, once the
two charts of `X` that the factoring chart induces are identified. -/
theorem etaleForm_compat_legChartData
    (ψ : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    {V V' : SmallEtale B S hS Y.1}
    {k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V'}
    (cd : LegChartData B S hS g hg V V' k)
    (hψ : ∀ x : ((modulePullback B S hS cd.legFst).obj
        ((modulePullback B S hS g).obj M)).val.obj (.op cd.obj),
      (canonicalComparison cd.legFst cd.legSnd g g cd.leg_condition N).hom.val.app (.op cd.obj)
          (((modulePullback B S hS cd.legFst).map ψ).val.app (.op cd.obj) x) =
        ((modulePullback B S hS cd.legSnd).map ψ).val.app (.op cd.obj)
          ((canonicalComparison cd.legFst cd.legSnd g g cd.leg_condition M).hom.val.app
            (.op cd.obj) x))
    (t : M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj
      ((smallEtalePostcomp B S hS cd.legFst cd.isEtale_legFst).obj cd.obj)))) :
    eqToHom (congrArg (fun W : SmallEtale B S hS X.1 => N.val.presheaf.obj (.op W))
          (postcomp_leg_eq B S hS g hg cd.isEtale_legFst cd.isEtale_legSnd cd.leg_condition
            cd.obj))
        ((etaleForm B S hS g hg ψ).val.app
          (.op ((smallEtalePostcomp B S hS cd.legFst cd.isEtale_legFst).obj cd.obj)) t) =
      (etaleForm B S hS g hg ψ).val.app
        (.op ((smallEtalePostcomp B S hS cd.legSnd cd.isEtale_legSnd).obj cd.obj))
        (eqToHom (congrArg (fun W : SmallEtale B S hS X.1 => M.val.presheaf.obj (.op W))
          (postcomp_leg_eq B S hS g hg cd.isEtale_legFst cd.isEtale_legSnd cd.leg_condition
            cd.obj)) t) := by
  obtain ⟨x, rfl⟩ : ∃ x, etaleSect₂ B S hS cd.legFst cd.isEtale_legFst g hg M cd.obj x = t :=
    ⟨etaleSect₂Inv B S hS cd.legFst cd.isEtale_legFst g hg M cd.obj t,
      etaleSect₂_etaleSect₂Inv B S hS cd.legFst cd.isEtale_legFst g hg M cd.obj t⟩
  convert etaleForm_compat_of_comparison B S hS cd.legFst cd.legSnd g g cd.leg_condition
    cd.isEtale_legFst cd.isEtale_legSnd hg hg
    (isEtale_comp B S hS cd.isEtale_legFst hg) (isEtale_comp B S hS cd.isEtale_legSnd hg)
    cd.restrictionComp_legFst cd.restrictionComp_legSnd ψ ψ cd.obj x (hψ x)
    using 2

/-- Restricting a section first along the morphism `k` of charts of `X` and then along the
comparison with `V` is restricting it along the comparison with `V'` and then along the
identification of the two induced charts. -/
theorem val_map_fst_comp_of_legChartData (M' : Modules.{u, u} B S hS X.1 X.2)
    {V V' : SmallEtale B S hS Y.1}
    {k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V'}
    (cd : LegChartData B S hS g hg V V' k)
    (t : M'.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj V'))) :
    M'.val.map ((smallEtalePostcomp B S hS g hg).map cd.fst).op (M'.val.map k.op t) =
      M'.val.map cd.mid.op
        (M'.val.map ((smallEtalePostcomp B S hS g hg).map cd.snd).op t) :=
  ((val_map_comp B S hS ((smallEtalePostcomp B S hS g hg).map cd.fst) k t).trans
      (val_map_congr_of_eq B S hS X M' cd.postcomp_comp t)).trans
    (val_map_comp B S hS cd.mid ((smallEtalePostcomp B S hS g hg).map cd.snd) t).symm

/-- The étale form read over the chart `V` and restricted along the comparison with `V` is that
form read over the chart of `Y` the factoring chart induces along the first leg. -/
theorem etaleForm_restrict_fst_of_legChartData
    (ψ : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    {V V' : SmallEtale B S hS Y.1}
    {k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V'}
    (cd : LegChartData B S hS g hg V V' k)
    (s : M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj V'))) :
    N.val.map ((smallEtalePostcomp B S hS g hg).map cd.fst).op
        ((etaleForm B S hS g hg ψ).val.app (.op V) (M.val.map k.op s)) =
      (etaleForm B S hS g hg ψ).val.app
        (.op ((smallEtalePostcomp B S hS cd.legFst cd.isEtale_legFst).obj cd.obj))
        (M.val.map cd.mid.op
          (M.val.map ((smallEtalePostcomp B S hS g hg).map cd.snd).op s)) :=
  (etaleForm_val_app_restrict B S hS g hg ψ cd.fst (M.val.map k.op s)).symm.trans
    (congrArg (fun z => (etaleForm B S hS g hg ψ).val.app
        (.op ((smallEtalePostcomp B S hS cd.legFst cd.isEtale_legFst).obj cd.obj)) z)
      (val_map_fst_comp_of_legChartData B S hS g hg M cd s))

/-- The étale form read over the chart of `Y` the factoring chart induces along the second leg,
restricted along the identification of the two induced charts of `X`, is that form read over the
chart `V'` and restricted along `k` and the comparison with `V`. -/
theorem etaleForm_restrict_snd_of_legChartData
    (ψ : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    {V V' : SmallEtale B S hS Y.1}
    {k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V'}
    (cd : LegChartData B S hS g hg V V' k)
    (s : M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj V'))) :
    N.val.map cd.mid.op ((etaleForm B S hS g hg ψ).val.app
        (.op ((smallEtalePostcomp B S hS cd.legSnd cd.isEtale_legSnd).obj cd.obj))
        (M.val.map ((smallEtalePostcomp B S hS g hg).map cd.snd).op s)) =
      N.val.map ((smallEtalePostcomp B S hS g hg).map cd.fst).op
        (N.val.map k.op ((etaleForm B S hS g hg ψ).val.app (.op V') s)) :=
  (congrArg (fun z => N.val.map cd.mid.op z)
      (etaleForm_val_app_restrict B S hS g hg ψ cd.snd s)).trans
    (val_map_fst_comp_of_legChartData B S hS g hg N cd
      ((etaleForm B S hS g hg ψ).val.app (.op V') s)).symm

/-- **The compatibility read along the identification of the two induced charts of `X`.** -/
theorem etaleForm_compat_mid_of_legChartData
    (ψ : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    {V V' : SmallEtale B S hS Y.1}
    {k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V'}
    (cd : LegChartData B S hS g hg V V' k)
    (hψ : ∀ x : ((modulePullback B S hS cd.legFst).obj
        ((modulePullback B S hS g).obj M)).val.obj (.op cd.obj),
      (canonicalComparison cd.legFst cd.legSnd g g cd.leg_condition N).hom.val.app (.op cd.obj)
          (((modulePullback B S hS cd.legFst).map ψ).val.app (.op cd.obj) x) =
        ((modulePullback B S hS cd.legSnd).map ψ).val.app (.op cd.obj)
          ((canonicalComparison cd.legFst cd.legSnd g g cd.leg_condition M).hom.val.app
            (.op cd.obj) x))
    (u : M.val.obj (.op ((smallEtalePostcomp B S hS (cd.legSnd ≫ g)
      (isEtale_comp B S hS cd.isEtale_legSnd hg)).obj cd.obj))) :
    (etaleForm B S hS g hg ψ).val.app
        (.op ((smallEtalePostcomp B S hS cd.legFst cd.isEtale_legFst).obj cd.obj))
        (M.val.map cd.mid.op u) =
      N.val.map cd.mid.op ((etaleForm B S hS g hg ψ).val.app
        (.op ((smallEtalePostcomp B S hS cd.legSnd cd.isEtale_legSnd).obj cd.obj)) u) := by
  have h1 := etaleForm_compat_legChartData B S hS g hg ψ cd hψ (M.val.map cd.mid.op u)
  rw [cd.eqToHom_val_map_mid M u] at h1
  rw [← h1]
  exact (cd.val_map_mid_eqToHom N _).symm

/-- **The compatibility, transferred along a factoring chart.** -/
theorem etaleForm_naturality_of_legChartData
    (ψ : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    {V V' : SmallEtale B S hS Y.1}
    {k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V'}
    (cd : LegChartData B S hS g hg V V' k)
    (hψ : ∀ x : ((modulePullback B S hS cd.legFst).obj
        ((modulePullback B S hS g).obj M)).val.obj (.op cd.obj),
      (canonicalComparison cd.legFst cd.legSnd g g cd.leg_condition N).hom.val.app (.op cd.obj)
          (((modulePullback B S hS cd.legFst).map ψ).val.app (.op cd.obj) x) =
        ((modulePullback B S hS cd.legSnd).map ψ).val.app (.op cd.obj)
          ((canonicalComparison cd.legFst cd.legSnd g g cd.leg_condition M).hom.val.app
            (.op cd.obj) x))
    (s : M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj V'))) :
    (etaleForm B S hS g hg ψ).val.app (.op V) (M.val.map k.op s) =
      N.val.map k.op ((etaleForm B S hS g hg ψ).val.app (.op V') s) := by
  have := cd.isIso_fst
  exact val_map_injective_of_isIso B S hS X N ((smallEtalePostcomp B S hS g hg).map cd.fst)
    ((etaleForm_restrict_fst_of_legChartData B S hS g hg ψ cd s).trans
      ((etaleForm_compat_mid_of_legChartData B S hS g hg ψ cd hψ
          (M.val.map ((smallEtalePostcomp B S hS g hg).map cd.snd).op s)).trans
        (etaleForm_restrict_snd_of_legChartData B S hS g hg ψ cd s)))

include hrep in
/-- **The compatibility with the canonical comparison of Stacks 04W5 at every pair of morphisms
into `Y` with equal composites to `X` is the naturality of the étale form on sections**, in an
arbitrary morphism of the induced charts of `X`.

This is the hypothesis that
`AlgebraicGeometry.Space.QuasiCoherentDescent.exists_modulePullback_map_eq_single` asks for.
Nothing is carried: the coherence of the comparison of Stacks 03LU with étale restriction is a
theorem at the two legs, both having a represented source and so being relatively
representable. -/
theorem etaleForm_naturality_of_dominated
    (ψ : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    (hcompat : ∀ (P : AlgebraicSpaces B S hS) (a b : P ⟶ Y) (hab : a ≫ g = b ≫ g),
      (modulePullback B S hS a).map ψ ≫ (canonicalComparison a b g g hab N).hom =
        (canonicalComparison a b g g hab M).hom ≫ (modulePullback B S hS b).map ψ)
    {V V' : SmallEtale B S hS Y.1}
    (k : (smallEtalePostcomp B S hS g hg).obj V ⟶ (smallEtalePostcomp B S hS g hg).obj V')
    (s : M.val.obj (.op ((smallEtalePostcomp B S hS g hg).obj V'))) :
    (etaleForm B S hS g hg ψ).val.app (.op V) (M.val.map k.op s) =
      N.val.map k.op ((etaleForm B S hS g hg ψ).val.app (.op V') s) := by
  obtain ⟨cd⟩ := nonempty_legChartData B S hS g hg hrep k
  exact etaleForm_naturality_of_legChartData B S hS g hg ψ cd (fun x =>
    comparison_val_app_of_naturality B S hS cd.legFst cd.legSnd g g cd.leg_condition
      ψ ψ (hcompat cd.space cd.legFst cd.legSnd cd.leg_condition) cd.obj x) s

include hg hrep in
/-- **Descent of morphisms of `𝒪_X`-modules along a relatively representable surjective étale
morphism.**  A morphism of the two inverse images along `g` which is compatible with the
canonical comparison of Stacks 04W5 at every pair of morphisms into `Y` with equal composites to
`X` is the inverse image along `g` of a morphism of `𝒪_X`-modules.

This is the fullness half of Stacks 04W6 for the one-member covering `{g}`, with **nothing
carried**: the coherence of the comparison of Stacks 03LU with étale restriction, which the
general statement of that half takes as a hypothesis, is a theorem at the pairs this proof reads
the condition at, because relative representability of `g` makes both legs out of a chart
relatively representable. -/
theorem exists_modulePullback_map_eq_of_dominated
    (hcov : IsEtaleCovering B S hS (fun _ : Unit => Y.1) (fun _ => g.hom))
    (ψ : (modulePullback B S hS g).obj M ⟶ (modulePullback B S hS g).obj N)
    (hcompat : ∀ (P : AlgebraicSpaces B S hS) (a b : P ⟶ Y) (hab : a ≫ g = b ≫ g),
      (modulePullback B S hS a).map ψ ≫ (canonicalComparison a b g g hab N).hom =
        (canonicalComparison a b g g hab M).hom ≫ (modulePullback B S hS b).map ψ) :
    ∃ χ : M ⟶ N, (modulePullback B S hS g).map χ = ψ :=
  exists_modulePullback_map_eq_single B S hS g hg hcov ψ
    fun _ _ k t => etaleForm_naturality_of_dominated B S hS g hg hrep ψ hcompat k t

end AlgebraicGeometry.Space.QuasiCoherentDescent

end
