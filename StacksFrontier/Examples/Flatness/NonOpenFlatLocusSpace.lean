module

public import Mathlib.Algebra.MvPolynomial.Cardinal
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Affine
public import StacksFrontier.AlgebraicGeometry.FiberRank.FlatFibreFiniteFree
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.AffineComparison
public import StacksFrontier.AlgebraicGeometry.Morphisms.Flat.IsoTransport
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineTranslation
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineLineTranslation.GenericPoint
public import StacksFrontier.AlgebraicGeometry.Spaces.Category
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatFiniteTypeModuleLocus
public import StacksFrontier.AlgebraicGeometry.Spaces.FlatModulePointChartIndependence
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionQuotientComparison
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.GroupActionRelationSummands
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.AlgebraicGeometry.Spaces.QuotientSheafPresentationUnconditional
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedFiniteTypeOnCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.RepresentedQuasicoherentSelfChart
public import StacksFrontier.AlgebraicGeometry.Topologies.Fppf.ContainingSet
public import StacksFrontier.Examples.Flatness.NonOpenFlatLocus

/-!
# An algebraic space and a point at which Stacks 0CWK fails

**Stacks 0CWK** asserts, for a morphism `f : X ⟶ Y` of algebraic spaces locally of finite type,
a quasi-coherent `𝒪_X`-module `F` of finite type and *an arbitrary* point `y` of `|Y|`, that the
points of the set-theoretic fibre `f^{-1}({y})` at which `F` is flat over `Y` form an open
subset of that fibre.  That is false.  This file exhibits a big fppf site, a morphism of
algebraic spaces over `Spec ℚ`, a module and a point satisfying every hypothesis of
`AlgebraicGeometry.Space.isOpen_flatLocus_setFibre` *except* the condition on `y`, at which the
conclusion fails.  So the condition on `y` carried by that theorem — condition (5) of
Stacks 03JV — cannot be dropped, and the source's statement is an error.

Let `A = ℚ[t, u_i : i ∈ ℤ]/((t - i) u_i : i ∈ ℤ)`, let `X = Spec A` and let
`I = (u_i : i ≥ 1)`.  The integers act on `X` over `Spec ℚ` by `t ↦ t - n`, `u_i ↦ u_{i + n}`.
No nonzero element of the action fixes a point of `X` together with its residue field, because
it translates the global section `t` by `n ∈ ℚ^×`; so the graph relation of the action is an
étale equivalence relation (**Stacks 02Z2**), the quotient `Y = X/ℤ` is an algebraic space
(**Stacks 02WW**) and the quotient map `f : X ⟶ Y` is surjective étale, in particular locally of
finite type.  The maximal ideals `p_m = (t - m) + (u_i : i ∈ ℤ)`, which have residue field `ℚ`,
form a single orbit, so they are one set-theoretic fibre of `f` (**Stacks 03BW**).  The module
`F = A ⧸ I` is quasi-coherent and cyclic, hence of finite type — but not of finite presentation,
which is why **Stacks 05WV** does not apply to it.  Finally the commutative algebra of
`Stacks.Examples.NonOpenFlatLocus` shows that `F` is flat over `Y` exactly at the `p_m` with
`m ≤ 0`, and that `p_0` lies in the closure of `{p_m : m ≥ 1}`, so that locus is
not open in the fibre.

## Main definitions

* `Stacks.Examples.NonOpenFlatLocusSpace.shiftAut` and
  `Stacks.Examples.NonOpenFlatLocusSpace.shiftAction`: the shift automorphism of `Spec A` over
  `Spec ℚ` and the integer action it generates.
* `Stacks.Examples.NonOpenFlatLocusSpace.chart`: `Spec A` as an object of a big fppf site over
  `Spec ℚ`, and `Stacks.Examples.NonOpenFlatLocusSpace.Xsp`,
  `Stacks.Examples.NonOpenFlatLocusSpace.Ysp`,
  `Stacks.Examples.NonOpenFlatLocusSpace.fmap`: the algebraic spaces `X = Spec A` and
  `Y = Spec A / ℤ` and the quotient morphism between them.
* `Stacks.Examples.NonOpenFlatLocusSpace.Fm`: the module `F = A ⧸ I` on the small étale site
  of `X`, and `Stacks.Examples.NonOpenFlatLocusSpace.diag` the square of étale scheme charts
  of `f` whose vertical map is the identity of `Spec A`.
* `Stacks.Examples.NonOpenFlatLocusSpace.ybase`: the point `y` of `|Y|`, the image of the
  `ℚ`-point `p_0`, and `Stacks.Examples.NonOpenFlatLocusSpace.fibreSet` the set-theoretic fibre
  of `f` over it.

## Main results

* `Stacks.Examples.NonOpenFlatLocusSpace.shiftAction_residueFieldFaithful` is condition (*) of
  Stacks 02Z2 for the action, which makes the graph relation an étale equivalence relation
  (`Stacks.Examples.NonOpenFlatLocusSpace.isEtaleEquivalenceRelation_rel`) and the quotient an
  algebraic space (`Stacks.Examples.NonOpenFlatLocusSpace.isAlgebraicSpace_quot`).
* `Stacks.Examples.NonOpenFlatLocusSpace.isLocallyOfFiniteType_fmap` and
  `Stacks.Examples.NonOpenFlatLocusSpace.isFiniteTypeOnCharts_Fm` are the hypotheses Stacks 0CWK
  asks of the morphism and of the module.
* `Stacks.Examples.NonOpenFlatLocusSpace.fibre_eq_range_ptPoint`: **the set-theoretic fibre of
  `f` over `y` is the single orbit `{p_m : m ∈ ℤ}`**, by Stacks 03BW for a group action.
* `Stacks.Examples.NonOpenFlatLocusSpace.mem_flatLocus_iff_isFlatAt`: **membership of the
  relative flat locus is flatness of `F` at the corresponding prime of `A`**, by Stacks 05VU
  read at the square `diag`.
* `Stacks.Examples.NonOpenFlatLocusSpace.not_isOpen_flatLocus_setFibre_of_free_shift` is **the
  refutation**: there is a morphism of algebraic spaces locally of finite type, a quasi-coherent
  module of finite type on its source and a point of its target for which the conclusion of
  Stacks 0CWK fails.  The hypothesis-carrying form is
  `Stacks.Examples.NonOpenFlatLocusSpace.not_isOpen_setOf_mem_flatLocus`.
* `Stacks.Examples.NonOpenFlatLocusSpace.not_hasQuasiCompactFieldRepresentative_ybase`: the
  hypothesis of `AlgebraicGeometry.Space.isOpen_flatLocus_setFibre` that fails at `y` is exactly
  the one that theorem carries — `y` has no quasi-compact field-valued representative.

## References

* [Stacks Project, Tag 0CWK](https://stacks.math.columbia.edu/tag/0CWK)
* [Stacks Project, Tag 02Z2](https://stacks.math.columbia.edu/tag/02Z2)
* [Stacks Project, Tag 02Z3](https://stacks.math.columbia.edu/tag/02Z3)
* [Stacks Project, Tag 02WW](https://stacks.math.columbia.edu/tag/02WW)
* [Stacks Project, Tag 03BW](https://stacks.math.columbia.edu/tag/03BW)
* [Stacks Project, Tag 03BX](https://stacks.math.columbia.edu/tag/03BX)
* [Stacks Project, Tag 03JV](https://stacks.math.columbia.edu/tag/03JV)
* [Stacks Project, Tag 05VU](https://stacks.math.columbia.edu/tag/05VU)
* [Stacks Project, Tag 05WV](https://stacks.math.columbia.edu/tag/05WV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Cardinal AlgebraicGeometry Multiplicative
open Stacks.Groupoids
open Stacks.Examples.NonOpenFlatLocus

namespace Stacks.Examples.NonOpenFlatLocusSpace

attribute [local instance] AlgebraicGeometry.Space.pointTopology

/-! ### `Spec A` over `Spec ℚ` -/

/-- `X = Spec A`, viewed over `Spec ℚ`. -/
abbrev src : Over (Spec (.of ℚ)) :=
  Over.mk (Spec.map (CommRingCat.ofHom (algebraMap ℚ A)))

/-- `A` is countable, being a quotient of a polynomial ring on countably many variables over
`ℚ`. -/
theorem mk_A_le : Cardinal.mk A ≤ ℵ₀ := by
  refine (Cardinal.mk_le_of_surjective (f := Ideal.Quotient.mk rel)
    Ideal.Quotient.mk_surjective).trans ?_
  refine (MvPolynomial.cardinalMk_le_max (σ := Option ℤ) (R := ℚ)).trans ?_
  simp

/-- `Spec A` lies in every big fppf site containing `Spec ℚ`. -/
theorem contains_src (B : BigFppfSite.{0}) (hS : B.Contains (Spec (.of ℚ))) :
    B.Contains (src).left := by
  change (Spec (CommRingCat.of A)).size < B.cutoff
  refine Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hS ?_
  exact mk_A_le.trans (le_max_left _ _)

/-! ### The shift as an automorphism -/

/-- The shifts compose. -/
private theorem ofHom_shift_comp (m n : ℤ) :
    CommRingCat.ofHom (shift m).toRingHom ≫ CommRingCat.ofHom (shift n).toRingHom =
      CommRingCat.ofHom (shift (n + m)).toRingHom :=
  CommRingCat.hom_ext (RingHom.ext fun x ↦ congrArg (fun f : A →ₐ[ℚ] A ↦ f x) (shift_comp n m))

/-- The shift by zero is the identity. -/
private theorem ofHom_shift_zero :
    CommRingCat.ofHom (shift 0).toRingHom = 𝟙 (CommRingCat.of A) := by
  rw [shift_zero]
  rfl

/-- The shifts are `ℚ`-algebra maps, so they are morphisms over `Spec ℚ`. -/
private theorem ofHom_algebraMap_comp_shift (n : ℤ) :
    CommRingCat.ofHom (algebraMap ℚ A) ≫ CommRingCat.ofHom (shift n).toRingHom =
      CommRingCat.ofHom (algebraMap ℚ A) :=
  CommRingCat.hom_ext (RingHom.ext (shift n).commutes)

/-- The automorphism of `Spec A` induced by the shift by `n`. -/
def shiftSpecIso (n : ℤ) : Spec (CommRingCat.of A) ≅ Spec (CommRingCat.of A) where
  hom := Spec.map (CommRingCat.ofHom (shift n).toRingHom)
  inv := Spec.map (CommRingCat.ofHom (shift (-n)).toRingHom)
  hom_inv_id := by
    rw [← Spec.map_comp, ofHom_shift_comp, add_neg_cancel, ofHom_shift_zero, Spec.map_id]
  inv_hom_id := by
    rw [← Spec.map_comp, ofHom_shift_comp, neg_add_cancel, ofHom_shift_zero, Spec.map_id]

/-- The automorphism of `Spec A` over `Spec ℚ` induced by the shift by `n`. -/
def shiftAut (n : ℤ) : Aut (src) :=
  Over.isoMk (shiftSpecIso n) (by
    change Spec.map (CommRingCat.ofHom (shift n).toRingHom) ≫
        Spec.map (CommRingCat.ofHom (algebraMap ℚ A)) =
      Spec.map (CommRingCat.ofHom (algebraMap ℚ A))
    rw [← Spec.map_comp, ofHom_algebraMap_comp_shift])

/-- The underlying morphism of schemes of the shift by `n`. -/
@[simp]
theorem shiftAut_hom_left (n : ℤ) :
    (shiftAut n).hom.left = Spec.map (CommRingCat.ofHom (shift n).toRingHom) := rfl

/-- The shift by zero is the identity automorphism. -/
theorem shiftAut_zero : shiftAut 0 = 1 := by
  refine Iso.ext (Over.OverMorphism.ext ?_)
  change Spec.map (CommRingCat.ofHom (shift 0).toRingHom) = 𝟙 (src).left
  rw [ofHom_shift_zero, Spec.map_id]
  rfl

/-- The shifts add. -/
theorem shiftAut_add (m n : ℤ) : shiftAut (m + n) = shiftAut m * shiftAut n := by
  refine Iso.ext (Over.OverMorphism.ext ?_)
  rw [Aut.Aut_mul_def]
  change Spec.map (CommRingCat.ofHom (shift (m + n)).toRingHom) =
    (shiftAut n).hom.left ≫ (shiftAut m).hom.left
  rw [shiftAut_hom_left, shiftAut_hom_left, ← Spec.map_comp, ofHom_shift_comp, add_comm n m]

/-- **The integer action on `Spec A`** generated by the shift. -/
def shiftAction : Multiplicative ℤ →* Aut (src) where
  toFun g := shiftAut (Multiplicative.toAdd g)
  map_one' := shiftAut_zero
  map_mul' _g _h := shiftAut_add _ _

/-- The integer `n` acts by the shift by `n`. -/
@[simp]
theorem shiftAction_ofAdd (n : ℤ) : shiftAction (Multiplicative.ofAdd n) = shiftAut n := rfl

/-! ### The translated coordinate and freeness -/

/-- The global section `t` of `Spec A`. -/
def coord : Γ((src).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of A)).inv t

/-- **The shift by `n` translates `t` by `n`.** -/
theorem shiftAut_appTop_coord (n : ℤ) :
    (shiftAut n).hom.left.appTop (coord) = coord - (n : Γ((src).left, ⊤)) := by
  simp only [coord, shiftAut_hom_left]
  rw [Scheme.specMap_appTop_ΓSpecIso_inv]
  change (Scheme.ΓSpecIso (CommRingCat.of A)).inv (shift n t) = _
  rw [shift_t, map_sub, map_intCast]

/-- **The action is free on residue fields.** No nonzero shift fixes a point of `Spec A`
together with its residue field. -/
theorem shiftAction_residueFieldFaithful :
    Space.ActsNontriviallyOnFixedResidueFields (src) (Multiplicative ℤ) (shiftAction) := by
  intro g x hx hne hres
  have hn : g.toAdd ≠ 0 := fun hzero ↦ hne (by simpa [hzero] using (ofAdd_toAdd g).symm)
  have hnat := (Scheme.Γevaluation_naturality_apply
    (shiftAction g).hom.left x (coord)).symm
  rw [hres, Scheme.residueFieldCongr_Γevaluation_apply hx] at hnat
  rw [show (shiftAction g) = shiftAut g.toAdd from rfl, shiftAut_appTop_coord, map_sub,
    map_intCast] at hnat
  have hzero : ((g.toAdd : ℤ) : (src).left.residueField x) = 0 := sub_eq_self.mp hnat
  have hunit : IsUnit ((g.toAdd : ℤ) : Γ((src).left, ⊤)) := by
    simpa using IsUnit.map
      (((Scheme.ΓSpecIso (CommRingCat.of ℚ)).inv ≫ (src).hom.appTop).hom :
        ℚ →+* Γ((src).left, ⊤))
      (isUnit_iff_ne_zero.mpr (Int.cast_ne_zero.mpr hn : ((g.toAdd : ℤ) : ℚ) ≠ 0))
  exact (IsUnit.map ((src).left.Γevaluation x).hom hunit).ne_zero (by simpa using hzero)

/-! ### The quotient algebraic space -/

section Site

variable (B : BigFppfSite.{0}) (hS : B.Contains (Spec (.of ℚ)))

/-- `Spec A` as an object of a big fppf site over `Spec ℚ`. -/
def chart : BigFppfOver B (Spec (.of ℚ)) hS :=
  Over.mk (ObjectProperty.homMk (src).hom : B.obj (contains_src B hS) ⟶ B.obj hS)

/-- The object of the site underlies `Spec A` over `Spec ℚ`, definitionally. -/
@[simp]
theorem chart_post : (Over.post B.inclusion).obj (chart B hS) = src := rfl

/-- The integer action, read at the underlying object of the site. -/
abbrev chartAction : Multiplicative ℤ →* Aut (Space.underlyingOver B hS (chart B hS)) :=
  shiftAction

/-- The freeness of the action, read at the object of the site. -/
theorem chartAction_residueFieldFaithful :
    Space.ActsNontriviallyOnFixedResidueFields (Space.underlyingOver B hS (chart B hS))
      (Multiplicative ℤ) (chartAction B hS) :=
  shiftAction_residueFieldFaithful

/-- **The relation scheme `∐_{n ∈ ℤ} Spec A` lies in the site**, by Stacks 02Z3. -/
theorem contains_relationScheme :
    B.Contains (Space.actionRelationScheme
      (Space.underlyingOver B hS (chart B hS)) (Multiplicative ℤ)).left :=
  Space.contains_actionRelationScheme (Multiplicative ℤ) B hS (chart B hS)
    (chartAction B hS) (chartAction_residueFieldFaithful B hS)

/-- The source map of the graph relation of the action: the identity on each copy. -/
abbrev relSource :
    Space.siteActionRelationScheme (Multiplicative ℤ) B hS (chart B hS)
      (contains_relationScheme B hS) ⟶ chart B hS :=
  Space.siteActionRelationSource (Multiplicative ℤ) B hS (chart B hS)
    (contains_relationScheme B hS)

/-- The target map of the graph relation of the action: the shift by the indexing integer. -/
abbrev relTarget :
    Space.siteActionRelationScheme (Multiplicative ℤ) B hS (chart B hS)
      (contains_relationScheme B hS) ⟶ chart B hS :=
  Space.siteActionRelationTarget (Multiplicative ℤ) B hS (chart B hS)
    (contains_relationScheme B hS) (chartAction B hS)

/-- The relation of the two maps is the graph relation of the action, definitionally. -/
theorem relation_eq :
    Space.relation B (Spec (.of ℚ)) hS (relSource B hS) (relTarget B hS) =
      Space.actionRelation (Space.underlyingOver B hS (chart B hS))
        (Multiplicative ℤ) (chartAction B hS) := rfl

/-- **Stacks 02Z2.** The graph relation of the shift is an étale equivalence relation. -/
instance isEtaleEquivalenceRelation_rel :
    Stacks.Groupoids.IsEtaleEquivalenceRelation
      (Space.relation B (Spec (.of ℚ)) hS (relSource B hS) (relTarget B hS)) := by
  rw [relation_eq]
  exact Space.actionRelation_isEtaleEquivalenceRelation _ (Multiplicative ℤ)
    (chartAction B hS) (chartAction_residueFieldFaithful B hS)

/-- **The quotient `Y = Spec A / ℤ` is an algebraic space**, by Stacks 02WW. -/
theorem isAlgebraicSpace_quot :
    IsAlgebraicSpace B (Spec (.of ℚ)) hS
      (Space.actionQuotient (Multiplicative ℤ) B hS (chart B hS) (chartAction B hS)) :=
  Space.isAlgebraicSpace_quotient_unconditional B (Spec (.of ℚ)) hS
    (relSource B hS) (relTarget B hS)

/-- The source algebraic space `X = Spec A`. -/
abbrev Xsp : AlgebraicSpaces B (Spec (.of ℚ)) hS :=
  ⟨yoneda.obj (chart B hS), isAlgebraicSpace_yoneda B (Spec (.of ℚ)) hS (chart B hS)⟩

/-- The target algebraic space `Y = Spec A / ℤ`. -/
abbrev Ysp : AlgebraicSpaces B (Spec (.of ℚ)) hS :=
  ⟨Space.actionQuotient (Multiplicative ℤ) B hS (chart B hS) (chartAction B hS),
    isAlgebraicSpace_quot B hS⟩

/-- The quotient morphism `f : X ⟶ Y`, surjective and étale. -/
abbrev fmap : Xsp B hS ⟶ Ysp B hS :=
  ObjectProperty.homMk
    (Space.actionProjection (Multiplicative ℤ) B hS (chart B hS) (chartAction B hS))

/-- `f` is the projection onto the quotient. -/
theorem fmap_hom :
    (fmap B hS).hom =
      Space.actionProjection (Multiplicative ℤ) B hS (chart B hS) (chartAction B hS) := rfl

/-- The quotient morphism `f` is étale as a morphism of presheaves on the site. -/
private theorem presheaf_etale_fmap :
    (MorphismProperty.inverseImage (@Etale.{0} : MorphismProperty Scheme.{0})
      (BigFppfOver.toScheme B (Spec (.of ℚ)) hS)).presheaf (fmap B hS).hom := by
  rw [fmap_hom, ← Space.quotientMap_eq_actionProjection (Multiplicative ℤ) B hS (chart B hS)
    (chartAction B hS) (contains_relationScheme B hS)]
  exact Space.quotientMap_etale_unconditional B (Spec (.of ℚ)) hS
    (relSource B hS) (relTarget B hS)

/-- **`f` is locally of finite type**, being étale. -/
theorem isLocallyOfFiniteType_fmap :
    Space.IsLocallyOfFiniteType B (Spec (.of ℚ)) hS (fmap B hS).hom :=
  Space.isLocallyOfFiniteType_of_isEtale' B (Spec (.of ℚ)) hS _
    (Space.isEtale_of_presheaf_etale B (Spec (.of ℚ)) hS (presheaf_etale_fmap B hS))

/-! ### The fibre over the image of `p_0` is the orbit `{p_m}` -/

/-- The point of the chart cut out by `p_m`. -/
def ptPoint (m : ℤ) : Space.points B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS)) :=
  (Space.pointsEquivScheme B (Spec (.of ℚ)) hS (chart B hS)).symm (pt m)

/-- The point `p_m` of the chart lies over the prime `p_m` of `A`. -/
@[simp]
theorem pointsToScheme_ptPoint (m : ℤ) :
    Space.pointsToScheme B (Spec (.of ℚ)) hS (chart B hS) (ptPoint B hS m) = pt m :=
  (Space.pointsEquivScheme B (Spec (.of ℚ)) hS (chart B hS)).apply_symm_apply _

/-- Distinct integers give distinct points of the chart. -/
theorem ptPoint_injective : Function.Injective (ptPoint B hS) := fun a b h ↦
  pt_injective (by rw [← pointsToScheme_ptPoint B hS a, ← pointsToScheme_ptPoint B hS b, h])

/-- The morphism of schemes realizing the action of `n` on the chart. -/
theorem toScheme_map_siteActionHom_eq (n : ℤ) :
    (BigFppfOver.toScheme B (Spec (.of ℚ)) hS).map
        (Space.siteActionHom (Multiplicative ℤ) B hS (chart B hS) (chartAction B hS)
          (Multiplicative.ofAdd n)) =
      (shiftAut n).hom.left :=
  congrArg Over.Hom.left (Space.post_map_siteActionHom (Multiplicative ℤ) B hS (chart B hS)
    (chartAction B hS) (Multiplicative.ofAdd n))

/-- **The `n`-th shift carries `p_m` to `p_{m - n}`** on the points of the chart. -/
theorem pointsMap_siteActionHom_ptPoint (n m : ℤ) :
    Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))
        (yoneda.map (Space.siteActionHom (Multiplicative ℤ) B hS (chart B hS)
          (chartAction B hS) (Multiplicative.ofAdd n))) (ptPoint B hS m) =
      ptPoint B hS (m - n) := by
  refine Space.injective_pointsToScheme B (Spec (.of ℚ)) hS (chart B hS) ?_
  rw [Space.pointsToScheme_pointsMap_yoneda, pointsToScheme_ptPoint,
    pointsToScheme_ptPoint, toScheme_map_siteActionHom_eq, shiftAut_hom_left]
  change (Spec.map (CommRingCat.ofHom (shift n).toRingHom)).base (pt m) = _
  rw [Spec.map_base]
  exact comap_shift_pt m n

/-- The chosen point `y` of the quotient: the image of `p_0`. -/
def ybase : Space.points B (Spec (.of ℚ)) hS
    (Space.actionQuotient (Multiplicative ℤ) B hS (chart B hS) (chartAction B hS)) :=
  Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))
    (Space.actionProjection (Multiplicative ℤ) B hS (chart B hS) (chartAction B hS))
    (ptPoint B hS 0)

/-- Every `p_m` lies in the fibre over `y`. -/
theorem pointsMap_proj_ptPoint (m : ℤ) :
    Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))
        (Space.actionProjection (Multiplicative ℤ) B hS (chart B hS) (chartAction B hS))
        (ptPoint B hS m) = ybase B hS := by
  have hm : ptPoint B hS m =
      Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))
        (yoneda.map (Space.siteActionHom (Multiplicative ℤ) B hS (chart B hS)
          (chartAction B hS) (Multiplicative.ofAdd (-m)))) (ptPoint B hS 0) := by
    rw [pointsMap_siteActionHom_ptPoint]
    congr 1
    omega
  have hcomp := Space.pointsMap_comp_apply B (Spec (.of ℚ)) hS
    (yoneda.map (Space.siteActionHom (Multiplicative ℤ) B hS (chart B hS) (chartAction B hS)
      (Multiplicative.ofAdd (-m))))
    (Space.actionProjection (Multiplicative ℤ) B hS (chart B hS) (chartAction B hS))
    (ptPoint B hS 0)
  rw [Space.siteActionHom_comp_actionProjection] at hcomp
  rw [ybase, hm, ← hcomp]

/-- Conversely every point of the fibre over `y` is one of the `p_m`. -/
theorem exists_eq_ptPoint_of_pointsMap_proj_eq
    (x : Space.points B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS)))
    (hx : Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))
      (Space.actionProjection (Multiplicative ℤ) B hS (chart B hS) (chartAction B hS)) x =
        ybase B hS) :
    ∃ m : ℤ, x = ptPoint B hS m := by
  obtain ⟨g, hg⟩ := Space.exists_smul_of_pointsMap_actionProjection_eq (Multiplicative ℤ) B hS
    (chart B hS) (chartAction B hS) (chartAction_residueFieldFaithful B hS) x (ptPoint B hS 0)
    (by rw [hx, ybase])
  refine ⟨-g.toAdd, ?_⟩
  rw [hg, show g = Multiplicative.ofAdd g.toAdd from rfl, pointsMap_siteActionHom_ptPoint]
  congr 1
  simp

/-- **The set-theoretic fibre of `f` over `y` is the orbit `{p_m : m : ℤ}`.** -/
theorem fibre_eq_range_ptPoint :
    Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))
        (Space.actionProjection (Multiplicative ℤ) B hS (chart B hS)
          (chartAction B hS)) ⁻¹' {ybase B hS} = Set.range (ptPoint B hS) := by
  refine Set.Subset.antisymm (fun x hx ↦ ?_) (fun x hx ↦ ?_)
  · obtain ⟨m, hm⟩ := exists_eq_ptPoint_of_pointsMap_proj_eq B hS x hx
    exact ⟨m, hm.symm⟩
  · obtain ⟨m, rfl⟩ := hx
    exact pointsMap_proj_ptPoint B hS m

/-- The fibre, read as a set of primes of `A`, is exactly `ptSet`. -/
theorem image_fibre_eq_ptSet :
    Space.pointsToScheme B (Spec (.of ℚ)) hS (chart B hS) ''
        (Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))
          (Space.actionProjection (Multiplicative ℤ) B hS (chart B hS)
            (chartAction B hS)) ⁻¹' {ybase B hS}) = ptSet := by
  rw [fibre_eq_range_ptPoint, ← Set.range_comp]
  exact congrArg Set.range (funext fun m ↦ pointsToScheme_ptPoint B hS m)

/-! ### Transporting non-openness along the comparison homeomorphism -/

/-- The set-theoretic fibre of `f` over `y`. -/
abbrev fibreSet : Set (Space.points B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))) :=
  Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS)) (fmap B hS).hom ⁻¹'
    {ybase B hS}

/-- A point of the chart lies in the fibre over `y` exactly when its prime of `A` is one of
the `p_m`. -/
theorem mem_fibreSet_iff (x : Space.points B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))) :
    x ∈ fibreSet B hS ↔
      Space.pointsToScheme B (Spec (.of ℚ)) hS (chart B hS) x ∈ ptSet := by
  have hfib : x ∈ fibreSet B hS ↔ ∃ m : ℤ, x = ptPoint B hS m := by
    change x ∈ Space.pointsMap B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))
      (Space.actionProjection (Multiplicative ℤ) B hS (chart B hS)
        (chartAction B hS)) ⁻¹' {ybase B hS} ↔ _
    rw [fibre_eq_range_ptPoint]
    exact ⟨fun ⟨m, hm⟩ ↦ ⟨m, hm.symm⟩, fun ⟨m, hm⟩ ↦ ⟨m, hm.symm⟩⟩
  rw [hfib]
  refine ⟨fun ⟨m, hm⟩ ↦ ⟨m, by rw [hm, pointsToScheme_ptPoint]⟩, fun ⟨m, hm⟩ ↦ ⟨m, ?_⟩⟩
  refine Space.injective_pointsToScheme B (Spec (.of ℚ)) hS (chart B hS) ?_
  rw [pointsToScheme_ptPoint, hm]

/-- **The fibre of `f` over `y` is homeomorphic to the subspace `{p_m : m : ℤ}` of
`Spec A`**, by the comparison homeomorphism of Stacks 03BX for the represented chart. -/
def fibreHomeo : (fibreSet B hS) ≃ₜ ptSet :=
  (Space.schemePointsHomeomorph B (Spec (.of ℚ)) hS (chart B hS)).subtype
    (mem_fibreSet_iff B hS)

/-- The comparison homeomorphism of the fibre is the comparison map on points. -/
@[simp]
theorem fibreHomeo_coe (x : fibreSet B hS) :
    ((fibreHomeo B hS x : ptSet) : PrimeSpectrum A) =
      Space.pointsToScheme B (Spec (.of ℚ)) hS (chart B hS) (x : _) := rfl

/-- If membership of the flat locus on the fibre is flatness of `F` at the corresponding prime of
`A`, then the flat locus is not open in the fibre. -/
theorem not_isOpen_setOf_mem_of_bridge
    (Fm : Space.Modules.{0, 0} B (Spec (.of ℚ)) hS (Xsp B hS).1 (Xsp B hS).2)
    (hbridge : ∀ x : fibreSet B hS,
      ((x : Space.points B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))) ∈
          Space.flatLocus B (Spec (.of ℚ)) hS (Xsp B hS).2 (fmap B hS).hom Fm) ↔
        IsFlatAt (Space.pointsToScheme B (Spec (.of ℚ)) hS (chart B hS) (x : _))) :
    ¬ IsOpen {x : fibreSet B hS |
      (x : Space.points B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))) ∈
        Space.flatLocus B (Spec (.of ℚ)) hS (Xsp B hS).2 (fmap B hS).hom Fm} := by
  intro hopen
  refine not_isOpen_flatLocus ?_
  have hset : {x : fibreSet B hS |
      (x : Space.points B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))) ∈
        Space.flatLocus B (Spec (.of ℚ)) hS (Xsp B hS).2 (fmap B hS).hom Fm} =
      (fibreHomeo B hS) ⁻¹' {z : ptSet | IsFlatAt z.1} := by
    ext x
    exact (hbridge x).trans (by rw [← fibreHomeo_coe B hS x]; exact Iff.rfl)
  exact (fibreHomeo B hS).isOpen_preimage.mp (hset ▸ hopen)


/-- `f : X ⟶ Y` is an étale chart of `Y`. -/
theorem isEtaleChart_fmap :
    Space.IsEtaleChart B (Spec (.of ℚ)) hS (Ysp B hS).1
      (CostructuredArrow.mk (fmap B hS).hom) :=
  presheaf_etale_fmap B hS

/-- `Spec A ⟶ Y` as an object of the small étale site of `Y`. -/
abbrev targetChart : Space.SmallEtale B (Spec (.of ℚ)) hS (Ysp B hS).1 :=
  ⟨CostructuredArrow.mk (fmap B hS).hom, isEtaleChart_fmap B hS⟩

/-- The commuting square of étale scheme charts with both charts `Spec A` and the identity
as its vertical map. -/
def diag : Space.ChartDiagram B (Spec (.of ℚ)) hS (Xsp B hS).1 (Ysp B hS).1 (fmap B hS).hom where
  U := Space.selfChart B (Spec (.of ℚ)) hS (chart B hS)
  V := targetChart B hS
  g := 𝟙 (chart B hS)
  comm := by simp only; rfl

/-- `F = A ⧸ I` is a finite `A`-module, being cyclic. -/
instance moduleFinite_F : Module.Finite A F := inferInstance

/-- `F^~`, the quasi-coherent module on `Spec A` associated with `F = A ⧸ I`. -/
abbrev Mt : SheafOfModules.{0} (Spec (CommRingCat.of A)).ringCatSheaf :=
  AlgebraicGeometry.tilde (R := CommRingCat.of A) (ModuleCat.of A F)

/-- `F = A ⧸ I` as a quasi-coherent module of finite type on the small étale site of `X`. -/
def Fm : Space.Modules.{0, 0} B (Spec (.of ℚ)) hS (Xsp B hS).1 (Xsp B hS).2 :=
  ((Space.representedQuasicoherentSchemeEquivalence B (Spec (.of ℚ)) hS (chart B hS)).functor.obj
    ⟨Mt, inferInstanceAs (SheafOfModules.IsQuasicoherent Mt)⟩).obj

/-- `Fm` is quasi-coherent on the small étale site. -/
instance isQuasicoherentOnSite_Fm : (Fm B hS).IsQuasicoherentOnSite :=
  ((Space.representedQuasicoherentSchemeEquivalence B (Spec (.of ℚ)) hS
    (chart B hS)).functor.obj ⟨Mt, inferInstanceAs (SheafOfModules.IsQuasicoherent Mt)⟩).property

/-- **`Fm` is of finite type on charts.** -/
theorem isFiniteTypeOnCharts_Fm :
    Space.IsFiniteTypeOnCharts B (Spec (.of ℚ)) hS (Xsp B hS).2 (Fm B hS) :=
  Space.isFiniteTypeOnCharts_representedQuasicoherentSchemeEquivalence B (Spec (.of ℚ)) hS
    (chart B hS) Mt (inferInstanceAs (SheafOfModules.IsQuasicoherent Mt))
    (inferInstanceAs (SheafOfModules.IsFiniteType Mt))

/-- The vertical map of the square of charts is the identity of `Spec A`. -/
theorem toScheme_map_diag_g :
    (BigFppfOver.toScheme B (Spec (.of ℚ)) hS).map (diag B hS).g =
      Spec.map (𝟙 (CommRingCat.of A)) := by
  change (BigFppfOver.toScheme B (Spec (.of ℚ)) hS).map (𝟙 (chart B hS)) = _
  rw [CategoryTheory.Functor.map_id, AlgebraicGeometry.Spec.map_id]
  rfl

/-- **Membership of the flat locus, at a point of the chart, is flatness of `F` at that prime
of `A`.** -/
theorem mem_flatLocus_iff_isFlatAt (u : PrimeSpectrum A) :
    Space.pointOfEtaleChart B (Spec (.of ℚ)) hS
        (Space.selfChart B (Spec (.of ℚ)) hS (chart B hS)) u ∈
      Space.flatLocus B (Spec (.of ℚ)) hS (Xsp B hS).2 (fmap B hS).hom (Fm B hS) ↔
    IsFlatAt u := by
  refine (Space.isFlatOverAtOnChartDiagram_iff_mem_flatLocus B (Spec (.of ℚ)) hS
    (fmap B hS) (Fm B hS) (diag B hS) u).symm.trans ?_
  have h1 : Space.IsFlatOverAtOnChartDiagram B (Spec (.of ℚ)) hS (Xsp B hS).2 (Fm B hS)
      (diag B hS) u ↔
      AlgebraicGeometry.IsFlatOverAt
        (LocallyRingedSpace.forgetToSheafedSpace.map
          ((BigFppfOver.toScheme B (Spec (.of ℚ)) hS).map (diag B hS).g).toLRSHom)
        Mt u :=
    AlgebraicGeometry.isFlatOverAt_iff_of_moduleIso _
      (Space.restrictToChart_selfChart_representedQuasicoherentIso B (Spec (.of ℚ)) hS
        (chart B hS) Mt (inferInstanceAs (SheafOfModules.IsQuasicoherent Mt))) u
  rw [h1, toScheme_map_diag_g]
  refine (AlgebraicGeometry.isFlatOverAt_spec_tilde_iff_flat_localizedModule
    (𝟙 (CommRingCat.of A)) (ModuleCat.of A F) rfl u).trans ?_
  exact (Module.flat_iff_of_isLocalization (Localization.AtPrime u.asIdeal)
    u.asIdeal.primeCompl (LocalizedModule u.asIdeal.primeCompl F)).symm

/-- A point of the represented algebraic space `X = Spec A` lies in the relative flat locus of `Fm`
over `Y` exactly when `F` is flat at the corresponding prime of `A`. -/
theorem mem_flatLocus_iff_isFlatAt_pointsToScheme
    (x : Space.points B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))) :
    x ∈ Space.flatLocus B (Spec (.of ℚ)) hS (Xsp B hS).2 (fmap B hS).hom (Fm B hS) ↔
      IsFlatAt (Space.pointsToScheme B (Spec (.of ℚ)) hS (chart B hS) x) := by
  have hx : Space.pointOfEtaleChart B (Spec (.of ℚ)) hS
      (Space.selfChart B (Spec (.of ℚ)) hS (chart B hS))
      (Space.pointsToScheme B (Spec (.of ℚ)) hS (chart B hS) x) = x := by
    rw [Space.pointOfEtaleChart_selfChart]
    exact (Space.pointsEquivScheme B (Spec (.of ℚ)) hS (chart B hS)).symm_apply_apply x
  refine Iff.trans ?_ (mem_flatLocus_iff_isFlatAt B hS
    (Space.pointsToScheme B (Spec (.of ℚ)) hS (chart B hS) x))
  rw [hx]

/-- The point `p_m` lies in the relative flat locus of `Fm` over `Y` exactly when `F` is flat at
the prime `p_m` of `A`. -/
theorem mem_flatLocus_ptPoint_iff (m : ℤ) :
    ptPoint B hS m ∈
        Space.flatLocus B (Spec (.of ℚ)) hS (Xsp B hS).2 (fmap B hS).hom (Fm B hS) ↔
      IsFlatAt (pt m) := by
  rw [mem_flatLocus_iff_isFlatAt_pointsToScheme, pointsToScheme_ptPoint]

/-- **The relative flat locus of `Fm` is not open in the fibre of `f` over `y`.** -/
theorem not_isOpen_setOf_mem_flatLocus :
    ¬ IsOpen {x : fibreSet B hS |
      (x : Space.points B (Spec (.of ℚ)) hS (yoneda.obj (chart B hS))) ∈
        Space.flatLocus B (Spec (.of ℚ)) hS (Xsp B hS).2 (fmap B hS).hom (Fm B hS)} :=
  not_isOpen_setOf_mem_of_bridge B hS (Fm B hS) fun x ↦
    mem_flatLocus_iff_isFlatAt_pointsToScheme B hS (x : _)

/-- **The point `y` has no quasi-compact field-valued representative**, which is the hypothesis
of `AlgebraicGeometry.Space.isOpen_flatLocus_setFibre` that the counterexample violates. -/
theorem not_hasQuasiCompactFieldRepresentative_ybase :
    ¬ Space.HasQuasiCompactFieldRepresentative B (Spec (.of ℚ)) hS (Ysp B hS).1
      (ybase B hS) := fun hy ↦
  not_isOpen_setOf_mem_flatLocus B hS
    (Space.isOpen_flatLocus_setFibre B (Spec (.of ℚ)) hS (fmap B hS) (Fm B hS)
      (isLocallyOfFiniteType_fmap B hS) (isFiniteTypeOnCharts_Fm B hS) (ybase B hS) hy)

/-- **Stacks 0CWK is false as stated.** -/
theorem not_isOpen_flatLocus_setFibre_of_free_shift :
    ∃ (B : BigFppfSite.{0}) (S : Scheme.{0}) (hS : B.Contains S)
      (X Y : AlgebraicSpaces B S hS) (f : X ⟶ Y)
      (Fm : Space.Modules.{0, 0} B S hS X.1 X.2) (_ : Fm.IsQuasicoherentOnSite)
      (_ : Space.IsLocallyOfFiniteType B S hS f.hom)
      (_ : Space.IsFiniteTypeOnCharts B S hS X.2 Fm)
      (y : Space.points B S hS Y.1),
      ¬ IsOpen {x : (Space.pointsMap B S hS X.1 f.hom ⁻¹' {y} :
          Set (Space.points B S hS X.1)) |
        (x : Space.points B S hS X.1) ∈ Space.flatLocus B S hS X.2 f.hom Fm} := by
  obtain ⟨B, hB⟩ := BigFppfSite.exists_containing ({Spec (CommRingCat.of ℚ)} : Set Scheme.{0})
  have hS : B.Contains (Spec (.of ℚ)) := hB _ (by simp)
  exact ⟨B, Spec (.of ℚ), hS, Xsp B hS, Ysp B hS, fmap B hS, Fm B hS, inferInstance,
    isLocallyOfFiniteType_fmap B hS, isFiniteTypeOnCharts_Fm B hS, ybase B hS,
    not_isOpen_setOf_mem_flatLocus B hS⟩

end Site

end Stacks.Examples.NonOpenFlatLocusSpace

end
