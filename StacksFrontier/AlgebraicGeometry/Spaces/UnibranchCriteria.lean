module

public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure
public import Mathlib.RingTheory.Algebraic.Cardinality
public import Mathlib.Topology.Irreducible
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Flatness.EtaleNeighborhood
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.Branches
public import StacksFrontier.AlgebraicGeometry.Properties.Unibranch
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleLocalRingNoetherian
public import StacksFrontier.AlgebraicGeometry.Spaces.SurjectiveOnPoints
public import StacksFrontier.AlgebraicGeometry.Spaces.Unibranch
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.EtaleSiteOfFppfSite
public import StacksFrontier.RingTheory.Branches.Henselization
public import StacksFrontier.RingTheory.Branches.MinimalPrimes
public import StacksFrontier.RingTheory.Spectrum.Prime.IrreducibleComponents

/-!
# Criteria for one branch at a point of an algebraic space

Five conditions on a point `x` of an algebraic space `F` are equivalent: the local ring of
every étale scheme chart at every point above `x` has a unique minimal prime; every such
chart has a unique irreducible component through every such point; those local rings are
unibranch; they are geometrically unibranch; and the étale local ring of `F` at every
geometric point above `x` has a unique minimal prime.

The fourth condition is `AlgebraicGeometry.Space.IsGeometricallyUnibranchAt`, which is the
definition of geometric unibranchness at a point of an algebraic space, so the equivalence is
what makes that definition agree with the other four branch criteria.

## Main definitions

* `AlgebraicGeometry.Space.HasUniqueMinimalPrimeOnEtaleCharts`,
  `AlgebraicGeometry.Space.HasUniqueIrreducibleComponentOnEtaleCharts`,
  `AlgebraicGeometry.Space.IsUnibranchOnEtaleCharts` and
  `AlgebraicGeometry.Space.HasUniqueMinimalPrimeAtGeometricPoints` are conditions (1), (2),
  (3) and (5).

## Main results

* `AlgebraicGeometry.Space.uniqueBranch_tfae`: the five conditions are equivalent for an
  algebraic space.

## Implementation notes

The chosen big fppf site presents the points of a scheme chart by the field-valued points of
its represented presheaf, so the two quantifiers of each condition — over étale charts of `F`,
and over the field-valued points of a chart lying over `x` — express the source's quantifiers
over schemes étale over the algebraic space and over their points above `x`.

The cycle of implications is (1) ↔ (2) → (4) → (3) → (1) together with (4) ↔ (5). The first
equivalence is the correspondence between the irreducible components of a scheme through a
point and the minimal primes of its local ring there, which on an affine chart is Tag 00ET.
The implication (2) → (4) is the étale-neighbourhood criterion for geometric unibranchness of
a scheme (Tag 0CB4): an étale neighbourhood of a point of a chart of `F` is refined by an
open subscheme of a smaller chart of `F`, and condition (2) for that chart bounds the branches
of the neighbourhood. The equivalence (4) ↔ (5) is Tag 06DM applied through Tag 04KF, which
identifies the étale local ring of `F` at a geometric point with a strict henselization of the
local ring of a chart.

## References

* [Stacks Project, Tag 06DK](https://stacks.math.columbia.edu/tag/06DK)
-/

@[expose] public noncomputable section

open CategoryTheory IsLocalRing

universe u

namespace AlgebraicGeometry.Space

/-! ### Uniqueness statements and bijections -/

/-- A unique-existence statement says exactly that the type of witnesses is nonempty and has
at most one element. -/
private theorem existsUnique_iff_nonempty_subsingleton {α : Type*} (p : α → Prop) :
    (∃! a, p a) ↔ Nonempty {a // p a} ∧ Subsingleton {a // p a} := by
  constructor
  · rintro ⟨c, hc, hu⟩
    exact ⟨⟨c, hc⟩, ⟨fun d d' => Subtype.ext ((hu d.1 d.2).trans (hu d'.1 d'.2).symm)⟩⟩
  · rintro ⟨⟨c, hc⟩, hsub⟩
    exact ⟨c, hc, fun d hd => congrArg Subtype.val (Subsingleton.elim ⟨d, hd⟩ ⟨c, hc⟩)⟩

/-- Two unique-existence statements agree once their types of witnesses are identified. -/
private theorem existsUnique_congr_equiv {α β : Type*} {p : α → Prop} {q : β → Prop}
    (e : {a // p a} ≃ {b // q b}) : (∃! a, p a) ↔ ∃! b, q b := by
  rw [existsUnique_iff_nonempty_subsingleton, existsUnique_iff_nonempty_subsingleton]
  exact and_congr e.nonempty_congr
    ⟨fun _ => e.symm.injective.subsingleton, fun _ => e.injective.subsingleton⟩

/-! ### Irreducible components through a point -/

/-- The irreducible components of a space through a point, packaged as subsets carrying both
their maximality and their incidence with the point. -/
def componentsThroughPack {X : Type*} [TopologicalSpace X] (x : X) :
    {Z : irreducibleComponents X // x ∈ (Z : Set X)} ≃
      {C : Set X // C ∈ irreducibleComponents X ∧ x ∈ C} where
  toFun Z := ⟨Z.1.1, Z.1.2, Z.2⟩
  invFun C := ⟨⟨C.1, C.2.1⟩, C.2.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The closure of the image of an irreducible component under an open embedding is an
irreducible component of the target, as soon as the component is nonempty. -/
theorem closure_image_mem_irreducibleComponents {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsOpenEmbedding f) {x : X} {C : Set X}
    (hC : C ∈ irreducibleComponents X) (hx : x ∈ C) :
    closure (f '' C) ∈ irreducibleComponents Y := by
  have hI : IsIrreducible (closure (f '' C)) :=
    (hC.1.image f hf.continuous.continuousOn).closure
  refine ⟨hI, fun D hD hDC => ?_⟩
  have hne : (D ∩ Set.range f).Nonempty :=
    ⟨f x, hDC (subset_closure ⟨x, hx, rfl⟩), ⟨x, rfl⟩⟩
  have hpre : IsIrreducible (f ⁻¹' D) := hD.preimage hf hne
  have hpreC : f ⁻¹' D ⊆ C :=
    hC.2 hpre fun z hz => hDC (subset_closure ⟨z, hz, rfl⟩)
  have hDcl : D ⊆ closure (D ∩ Set.range f) :=
    subset_closure_inter_of_isPreirreducible_of_isOpen hD.2 hf.isOpen_range hne
  rw [← Set.image_preimage_eq_inter_range] at hDcl
  exact hDcl.trans (closure_mono (Set.image_mono hpreC))

/-- An open embedding matches the irreducible components through a point with the irreducible
components through its image: a component of the source goes to the closure of its image, and
a component of the target is pulled back. -/
def componentsThroughEquivOfIsOpenEmbedding {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsOpenEmbedding f) (x : X) :
    {C : Set X // C ∈ irreducibleComponents X ∧ x ∈ C} ≃
      {D : Set Y // D ∈ irreducibleComponents Y ∧ f x ∈ D} where
  toFun C := ⟨closure (f '' C.1), closure_image_mem_irreducibleComponents hf C.2.1 C.2.2,
    subset_closure ⟨x, C.2.2, rfl⟩⟩
  invFun D := ⟨f ⁻¹' D.1,
    preimage_mem_irreducibleComponents D.2.1 hf ⟨f x, D.2.2, ⟨x, rfl⟩⟩, D.2.2⟩
  left_inv C := by
    apply Subtype.ext
    have hpre : f ⁻¹' closure (f '' C.1) ∈ irreducibleComponents X :=
      preimage_mem_irreducibleComponents
        (closure_image_mem_irreducibleComponents hf C.2.1 C.2.2) hf
        ⟨f x, subset_closure ⟨x, C.2.2, rfl⟩, ⟨x, rfl⟩⟩
    exact Set.Subset.antisymm
      (C.2.1.2 hpre.1 fun z hz => subset_closure ⟨z, hz, rfl⟩)
      fun z hz => subset_closure ⟨z, hz, rfl⟩
  right_inv D := Subtype.ext <|
    closure_image_preimage_of_isPreirreducible f hf.isOpenMap D.1 ⟨x, D.2.2⟩
      D.2.1.1.2 (isClosed_of_mem_irreducibleComponents _ D.2.1)

/-- Uniqueness of the irreducible component through a point is invariant under an open
embedding. -/
private theorem existsUnique_irreducibleComponent_congr {X Y : Type*} [TopologicalSpace X]
    [TopologicalSpace Y] {f : X → Y} (hf : Topology.IsOpenEmbedding f) (x : X) :
    (∃! C : irreducibleComponents X, x ∈ (C : Set X)) ↔
      ∃! D : irreducibleComponents Y, f x ∈ (D : Set Y) :=
  existsUnique_congr_equiv ((componentsThroughPack x).trans
    ((componentsThroughEquivOfIsOpenEmbedding hf x).trans (componentsThroughPack (f x)).symm))

/-- A scheme has a unique irreducible component through a point exactly when its local ring
there has a unique minimal prime: on an affine chart this is the correspondence of Tag 00ET
between the irreducible components through a prime and the minimal primes of the
localization. -/
private theorem existsUnique_irreducibleComponent_iff_existsUnique_minimalPrimes_stalk
    (X : Scheme.{u}) (x : X) :
    (∃! Z : irreducibleComponents X, x ∈ (Z : Set X)) ↔
      ∃! q : Ideal (X.presheaf.stalk x), q ∈ minimalPrimes (X.presheaf.stalk x) := by
  classical
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
  have : _root_.AlgebraicGeometry.IsOpenImmersion hU.fromSpec := hU.isOpenImmersion_fromSpec
  let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  have hp : hU.fromSpec p = x := hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have : p.asIdeal.IsPrime := p.isPrime
  let : Algebra Γ(X, U) (X.presheaf.stalk x) := (X.presheaf.germ U x hxU).hom.toAlgebra
  have : IsLocalization.AtPrime (X.presheaf.stalk x) p.asIdeal :=
    hU.isLocalization_stalk ⟨x, hxU⟩
  have h := existsUnique_irreducibleComponent_congr hU.fromSpec.isOpenEmbedding p
  rw [hp] at h
  exact h.symm.trans <| existsUnique_congr_equiv ((componentsThroughPack p).trans
    (PrimeSpectrum.irreducibleComponentsThroughEquiv Γ(X, U) p.asIdeal (X.presheaf.stalk x)))

/-! ### Local rings with a single minimal prime -/

/-- A unibranch local ring has a unique minimal prime: its reduction is a domain. -/
private theorem existsUnique_minimalPrimes_of_isUnibranch (R : Type*) [CommRing R]
    [IsLocalRing R] (hR : _root_.IsUnibranch R) : ∃! p : Ideal R, p ∈ minimalPrimes R := by
  have : IsDomain (R ⧸ nilradical R) := hR.1
  exact unique_minimalPrimes_of_isDomain_reduction

/-- A set with a unique member of extended cardinality one, and conversely. -/
public theorem existsUnique_mem_iff_encard_eq_one {α : Type*} (s : Set α) :
    (∃! a, a ∈ s) ↔ s.encard = 1 := by
  rw [Set.encard_eq_one]
  constructor
  · rintro ⟨a, ha, hu⟩
    exact ⟨a, Set.eq_singleton_iff_unique_mem.mpr ⟨ha, hu⟩⟩
  · rintro ⟨a, rfl⟩
    exact ⟨a, rfl, fun b hb => hb⟩

/-- **Stacks 0CB4.** A scheme is geometrically unibranch at a point as soon as every étale
neighbourhood of that point has a unique irreducible component through its distinguished
point: the number of geometric branches is the supremum of those counts. -/
@[ega "IV 18.8.15" "Implication b) ⇒ a)"]
private theorem isGeometricallyUnibranch_stalk_of_forall_etaleNeighborhood (X : Scheme.{u})
    (y : X) (h : ∀ N : _root_.AlgebraicGeometry.EtaleNeighborhood X y,
      ∃! Z : irreducibleComponents N.scheme, N.point ∈ (Z : Set N.scheme)) :
    _root_.IsGeometricallyUnibranch (X.presheaf.stalk y) := by
  have : Nonempty (_root_.AlgebraicGeometry.EtaleNeighborhood X y) :=
    ⟨{ scheme := X, point := y, toBase := 𝟙 X, map_point := by simp }⟩
  have hone : ∀ N : _root_.AlgebraicGeometry.EtaleNeighborhood X y,
      Set.encard {Z ∈ irreducibleComponents N.scheme | N.point ∈ Z} = 1 := by
    intro N
    rw [← existsUnique_mem_iff_encard_eq_one]
    exact existsUnique_congr_equiv (componentsThroughPack N.point) |>.mp (h N)
  have hsup : _root_.AlgebraicGeometry.numberOfGeometricBranches X y = 1 := by
    rw [_root_.AlgebraicGeometry.numberOfGeometricBranches_eq_iSup_encard]
    simp only [hone, iSup_const]
  rw [_root_.isGeometricallyUnibranch_iff_strictHenselization_has_unique_minimalPrime
    (X.presheaf.stalk y) (strictHenselizationData (X.presheaf.stalk y)).carrier
    (SeparableClosure (ResidueField (X.presheaf.stalk y)))]
  exact (existsUnique_mem_iff_encard_eq_one _).mpr hsup

/-- Geometric unibranchness of the local ring of a scheme at a point depends only on the
point. -/
private theorem isGeometricallyUnibranch_stalk_congr {X : Scheme.{u}} {x y : X} (h : x = y)
    (hx : _root_.IsGeometricallyUnibranch (X.presheaf.stalk x)) :
    _root_.IsGeometricallyUnibranch (X.presheaf.stalk y) :=
  h ▸ hx

/-! ### Chart points of a geometric point -/

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}

/-- Field-valued points of a represented presheaf with the same underlying scheme point
define the same point of that presheaf. -/
theorem class_eq_class_of_schemePoint_eq (U : BigFppfOver B S hS)
    (p q : FieldValuedPoint B S hS (yoneda.obj U))
    (h : schemePoint B S hS U p = schemePoint B S hS U q) :
    p.class B S hS (yoneda.obj U) = q.class B S hS (yoneda.obj U) :=
  injective_pointsToScheme B S hS U h

/-- The spectrum of an algebraic closure of a field whose spectrum lies in the chosen big
fppf site lies in that site again: an algebraic extension does not increase cardinality past
the cutoff. -/
theorem contains_specAlgebraicClosure (B : BigFppfSite.{u}) (K : Type u) [Field K]
    (hK : B.Contains (Spec (.of K))) : B.Contains (Spec (.of (AlgebraicClosure K))) :=
  Scheme.size_Spec_lt_of_mk_le_max B.aleph0_lt_cutoff B.cutoff_isStrongPrelimit hK
    ((Algebra.IsAlgebraic.cardinalMk_le_max K (AlgebraicClosure K)).trans_eq (max_comm _ _))

/-! ### Refining an étale neighbourhood of a chart point by a chart -/

/-- An étale neighbourhood of a point of an étale chart of `F` is refined by an open
subscheme of a smaller étale chart of `F`: an affine open of the neighbourhood around the
distinguished point is small enough for the chosen big fppf site and is étale over `F`. -/
theorem exists_smallEtale_refinement_of_etaleNeighborhood
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (U : SmallEtale B S hS F)
    (p : FieldValuedPoint B S hS (yoneda.obj U.1.left))
    (N : _root_.AlgebraicGeometry.EtaleNeighborhood
      ((BigFppfOver.toScheme B S hS).obj U.1.left) (schemePoint B S hS U.1.left p)) :
    ∃ (V : SmallEtale B S hS F) (q : FieldValuedPoint B S hS (yoneda.obj V.1.left))
      (j : (BigFppfOver.toScheme B S hS).obj V.1.left ⟶ N.scheme),
      _root_.AlgebraicGeometry.IsOpenImmersion j ∧
      j.base (schemePoint B S hS V.1.left q) = N.point ∧
      pointsMap B S hS (yoneda.obj V.1.left) V.1.hom (q.class B S hS (yoneda.obj V.1.left)) =
        pointsMap B S hS (yoneda.obj U.1.left) U.1.hom
          (p.class B S hS (yoneda.obj U.1.left)) := by
  classical
  let X := (BigFppfOver.toScheme B S hS).obj U.1.left
  obtain ⟨_, ⟨A, hA, rfl⟩, hpoint, -⟩ :=
    N.scheme.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ N.point) isOpen_univ
  let A' : N.scheme.affineOpens := ⟨A, hA⟩
  have : IsAffine A'.1.toScheme := A'.2
  let y : A'.1.toScheme := ⟨N.point, hpoint⟩
  let w : Scheme.Hom A'.1.toScheme X := A'.1.ι ≫ N.toBase
  have hwpoint : w.base y = N.toBase.base N.point := by
    show (A'.1.ι ≫ N.toBase).base y = N.toBase.base N.point
    rw [Scheme.Hom.comp_apply]
    rfl
  let hsize : B.Contains A'.1.toScheme :=
    (Scheme.size_le_of_locallyOfFiniteType w).trans_lt U.1.left.left.property
  let Wobj : B.Schemes := B.obj hsize
  let wB : B.inclusion.obj Wobj ⟶ B.inclusion.obj U.1.left.left := w
  let a₀ : Wobj ⟶ U.1.left.left := B.inclusion.preimage wB
  let Wover : BigFppfOver B S hS := Over.mk (a₀ ≫ U.1.left.hom)
  let a : Wover ⟶ U.1.left := Over.homMk a₀
  have haMap : (BigFppfOver.toScheme B S hS).map a = w := B.inclusion.map_preimage wB
  have haEt : Etale ((BigFppfOver.toScheme B S hS).map a) := by
    rw [haMap]
    infer_instance
  let V : SmallEtale B S hS F :=
    ⟨CostructuredArrow.mk (yoneda.map a ≫ U.1.hom),
      etale_comp_of_scheme B S hS a U.1.hom haEt U.2⟩
  let q := schemePointRepresentative B S hS V.1.left y
  let qU := FieldValuedPoint.map B S hS (yoneda.obj V.1.left) (yoneda.map a) q
  have hpointMap : schemePoint B S hS U.1.left qU = schemePoint B S hS U.1.left p := by
    rw [schemePoint_map_yoneda, schemePointRepresentative_point]
    calc ((BigFppfOver.toScheme B S hS).map a).base y = w.base y := by rw [haMap]
      _ = N.toBase.base N.point := hwpoint
      _ = schemePoint B S hS U.1.left p := N.map_point
  refine ⟨V, q, A'.1.ι, inferInstance, ?_, ?_⟩
  · show A'.1.ι.base (schemePoint B S hS V.1.left q) = N.point
    rw [schemePointRepresentative_point]
    rfl
  · show pointsMap B S hS (yoneda.obj V.1.left) (yoneda.map a ≫ U.1.hom)
      (q.class B S hS (yoneda.obj V.1.left)) = _
    rw [pointsMap_comp, Function.comp_apply, pointsMap_class,
      class_eq_class_of_schemePoint_eq U.1.left qU p hpointMap, pointsMap_class]

/-! ### The five criteria -/

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **Stacks 06DK, condition (1).** The local ring of every étale chart of `F` at every point
above `x` has a unique minimal prime. -/
def HasUniqueMinimalPrimeOnEtaleCharts (x : points B S hS F) : Prop :=
  ∀ (U : SmallEtale B S hS F) (p : FieldValuedPoint B S hS (yoneda.obj U.1.left)),
    pointsMap B S hS (yoneda.obj U.1.left) U.1.hom
        (p.class B S hS (yoneda.obj U.1.left)) = x →
      ∃! q : Ideal (((BigFppfOver.toScheme B S hS).obj U.1.left).presheaf.stalk
        (schemePoint B S hS U.1.left p)), q ∈ minimalPrimes _

/-- **Stacks 06DK, condition (2).** Every étale chart of `F` has a unique irreducible
component through every point above `x`. -/
def HasUniqueIrreducibleComponentOnEtaleCharts (x : points B S hS F) : Prop :=
  ∀ (U : SmallEtale B S hS F) (p : FieldValuedPoint B S hS (yoneda.obj U.1.left)),
    pointsMap B S hS (yoneda.obj U.1.left) U.1.hom
        (p.class B S hS (yoneda.obj U.1.left)) = x →
      ∃! Z : irreducibleComponents ((BigFppfOver.toScheme B S hS).obj U.1.left),
        schemePoint B S hS U.1.left p ∈ (Z : Set _)

/-- **Stacks 06DK, condition (3).** The local ring of every étale chart of `F` at every point
above `x` is unibranch. -/
def IsUnibranchOnEtaleCharts (x : points B S hS F) : Prop :=
  ∀ (U : SmallEtale B S hS F) (p : FieldValuedPoint B S hS (yoneda.obj U.1.left)),
    pointsMap B S hS (yoneda.obj U.1.left) U.1.hom
        (p.class B S hS (yoneda.obj U.1.left)) = x →
      _root_.IsUnibranch (((BigFppfOver.toScheme B S hS).obj U.1.left).presheaf.stalk
        (schemePoint B S hS U.1.left p))

/-- **Stacks 06DK, condition (5).** The étale local ring of `F` at every geometric point above
`x` has a unique minimal prime. -/
def HasUniqueMinimalPrimeAtGeometricPoints (x : points B S hS F) : Prop :=
  ∀ p : GeometricPoint B S hS F, GeometricPoint.LiesOver p x →
    ∃! q : Ideal (etaleLocalRing B S hS F p), q ∈ minimalPrimes _

/-! ### The implications -/

/-- Conditions (1) and (2) are equivalent: the irreducible components of a scheme through a
point correspond to the minimal primes of its local ring there. -/
private theorem hasUniqueMinimalPrimeOnEtaleCharts_iff_hasUniqueIrreducibleComponent
    (x : points B S hS F) :
    HasUniqueMinimalPrimeOnEtaleCharts B S hS F x ↔
      HasUniqueIrreducibleComponentOnEtaleCharts B S hS F x :=
  forall₃_congr fun U p _ =>
    (existsUnique_irreducibleComponent_iff_existsUnique_minimalPrimes_stalk
      ((BigFppfOver.toScheme B S hS).obj U.1.left) (schemePoint B S hS U.1.left p)).symm

/-- Condition (2) implies condition (4): an étale neighbourhood of a point of a chart is
refined by an open subscheme of a smaller chart, whose branches condition (2) controls. -/
private theorem isGeometricallyUnibranchAt_of_hasUniqueIrreducibleComponent
    (x : points B S hS F) (h : HasUniqueIrreducibleComponentOnEtaleCharts B S hS F x) :
    IsGeometricallyUnibranchAt B S hS F x := by
  intro U p hp
  apply isGeometricallyUnibranch_stalk_of_forall_etaleNeighborhood
  intro N
  obtain ⟨V, q, j, hj, hjq, hclass⟩ :=
    exists_smallEtale_refinement_of_etaleNeighborhood B S hS F U p N
  have : _root_.AlgebraicGeometry.IsOpenImmersion j := hj
  simpa only [hjq] using (existsUnique_irreducibleComponent_congr j.isOpenEmbedding
    (schemePoint B S hS V.1.left q)).mp (h V q (hclass.trans hp))

/-- Condition (4) implies condition (3): a geometrically unibranch local ring is unibranch. -/
private theorem isUnibranchOnEtaleCharts_of_isGeometricallyUnibranchAt (x : points B S hS F)
    (h : IsGeometricallyUnibranchAt B S hS F x) : IsUnibranchOnEtaleCharts B S hS F x :=
  fun U p hp => (h U p hp).1

/-- Condition (3) implies condition (1): a unibranch local ring has a unique minimal
prime. -/
private theorem hasUniqueMinimalPrimeOnEtaleCharts_of_isUnibranchOnEtaleCharts
    (x : points B S hS F) (h : IsUnibranchOnEtaleCharts B S hS F x) :
    HasUniqueMinimalPrimeOnEtaleCharts B S hS F x :=
  fun U p hp => existsUnique_minimalPrimes_of_isUnibranch _ (h U p hp)

/-- **Stacks 06DM through 04KF.** The local ring of a chart at the point selected by a small
étale neighbourhood of a geometric point is geometrically unibranch exactly when the étale
local ring there has a unique minimal prime: the latter is a strict henselization of the
former. -/
@[ega "IV 18.8.15" "special case"]
private theorem isGeometricallyUnibranch_chart_iff_existsUnique_minimalPrimes
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hF : IsAlgebraicSpace B S hS F)
    (x : GeometricPoint B S hS F) (V : SmallEtaleNeighborhood x) :
    _root_.IsGeometricallyUnibranch ((chartScheme V.chart).presheaf.stalk
        ((chartGeometricPoint V).hom
          (closedPoint (chartGeometricPoint V).residueField))) ↔
      ∃! q : Ideal (etaleLocalRing B S hS F x), q ∈ minimalPrimes _ := by
  let R := (chartScheme V.chart).presheaf.stalk
    ((chartGeometricPoint V).hom (closedPoint (chartGeometricPoint V).residueField))
  let κ := separableClosure (ResidueField R) (chartGeometricPoint V).residueField
  let T := IsLocalRing.henselizationTower R κ
  let e : T.strictHenselization ≃+* etaleLocalRing B S hS F x :=
    strictHenselizationEquivEtaleLocalRing hF V (bigEtaleSiteOfFppfSite B)
      V.chart.obj.left.left.property T
  exact (_root_.isGeometricallyUnibranch_iff_strictHenselization_has_unique_minimalPrime
    R T.strictHenselization κ).trans
      (existsUnique_congr_equiv (bijOn_minimalPrimes_ringEquiv e).equiv).symm

/-- Condition (4) implies condition (5): a geometric point above `x` has a small étale
neighbourhood, and the étale local ring there is a strict henselization of the chart's local
ring. -/
private theorem hasUniqueMinimalPrimeAtGeometricPoints_of_isGeometricallyUnibranchAt
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F)
    (h : IsGeometricallyUnibranchAt B S hS F x) :
    HasUniqueMinimalPrimeAtGeometricPoints B S hS F x := by
  intro g hg
  obtain ⟨U, f, hSurj, hEtale⟩ := hF.exists_atlas
  obtain ⟨⟨V, -⟩⟩ := exists_pointed_smallEtaleNeighborhood B S hS F hF g f hSurj hEtale
  exact (isGeometricallyUnibranch_chart_iff_existsUnique_minimalPrimes hF g V).mp
    (h V.chart (chartFieldValuedPoint V) ((chartFieldValuedPoint_pointsMap V).trans hg))

/-- Condition (5) implies condition (4): an algebraic closure of the field of a chart point
turns it into a geometric point above `x`, and the chart is a small étale neighbourhood of
it. -/
private theorem isGeometricallyUnibranchAt_of_hasUniqueMinimalPrimeAtGeometricPoints
    (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F)
    (h : HasUniqueMinimalPrimeAtGeometricPoints B S hS F x) :
    IsGeometricallyUnibranchAt B S hS F x := by
  intro U p hp
  let K := p.carrier
  let Ω := AlgebraicClosure K
  let hΩ := contains_specAlgebraicClosure B K p.contained
  let kobj : B.Schemes := B.obj hΩ
  let σ : Spec (.of Ω) ⟶ Spec (.of K) := Spec.map (CommRingCat.ofHom (algebraMap K Ω))
  let f₀ : B.inclusion.obj kobj ⟶ B.inclusion.obj p.siteObject.left := σ
  let f : kobj ⟶ p.siteObject.left := B.inclusion.preimage f₀
  let W : BigFppfOver B S hS := Over.mk (f ≫ p.siteObject.hom)
  let a : W ⟶ p.siteObject := Over.homMk f
  let r : FieldValuedPoint B S hS (yoneda.obj p.siteObject) :=
    { carrier := Ω
      contained := hΩ
      toBase := B.inclusion.map (f ≫ p.siteObject.hom)
      value := a }
  let q : FieldValuedPoint B S hS (yoneda.obj U.1.left) :=
    FieldValuedPoint.map B S hS (yoneda.obj p.siteObject) (yoneda.map p.value) r
  have hqclass : pointsMap B S hS (yoneda.obj U.1.left) U.1.hom
      (q.class B S hS (yoneda.obj U.1.left)) = x := by
    calc pointsMap B S hS (yoneda.obj U.1.left) U.1.hom
          (q.class B S hS (yoneda.obj U.1.left))
        = (FieldValuedPoint.map B S hS (yoneda.obj U.1.left) U.1.hom q).class B S hS F :=
          (pointsMap_class _ _ _ _ _ _).symm
      _ = (FieldValuedPoint.map B S hS (yoneda.obj U.1.left) U.1.hom p).class B S hS F :=
          FieldValuedPoint.class_eq_class_of_hasCommonExtension B S hS F
            (FieldValuedPoint.hasCommonExtension_map B S hS (yoneda.obj U.1.left) U.1.hom
              ⟨q, FieldValuedPoint.dominates_refl B S hS (yoneda.obj U.1.left) q, ⟨a, rfl⟩⟩)
      _ = x := (pointsMap_class B S hS (yoneda.obj U.1.left) U.1.hom p).trans hp
  let g : GeometricPoint B S hS F :=
    ⟨FieldValuedPoint.map B S hS (yoneda.obj U.1.left) U.1.hom q, AlgebraicClosure.isAlgClosed K⟩
  let V : SmallEtaleNeighborhood g := { chart := U, point := q.value, point_comp := rfl }
  have hrpoint : schemePoint B S hS p.siteObject r = closedPoint K := by
    show (B.inclusion.map f) (closedPoint Ω) = _
    rw [B.inclusion.map_preimage f₀]
    show PrimeSpectrum.comap (algebraMap K Ω) (closedPoint Ω) = closedPoint K
    simp
  have hpoint : schemePoint B S hS U.1.left q = schemePoint B S hS U.1.left p := by
    rw [schemePoint_map_yoneda, hrpoint]
    rfl
  exact isGeometricallyUnibranch_stalk_congr hpoint
    ((isGeometricallyUnibranch_chart_iff_existsUnique_minimalPrimes hF g V).2 (h g hqclass))

/-- **Stacks 06DK.** For a point `x` of an algebraic space `F` the five branch criteria are
equivalent: a unique minimal prime in the local rings of the étale charts above `x`, a unique
irreducible component of those charts through those points, unibranchness and geometric
unibranchness of those local rings, and a unique minimal prime in the étale local ring at
every geometric point above `x`. -/
@[stacks 06DK]
theorem uniqueBranch_tfae (hF : IsAlgebraicSpace B S hS F) (x : points B S hS F) :
    List.TFAE [HasUniqueMinimalPrimeOnEtaleCharts B S hS F x,
      HasUniqueIrreducibleComponentOnEtaleCharts B S hS F x,
      IsUnibranchOnEtaleCharts B S hS F x,
      IsGeometricallyUnibranchAt B S hS F x,
      HasUniqueMinimalPrimeAtGeometricPoints B S hS F x] := by
  tfae_have 1 ↔ 2 :=
    hasUniqueMinimalPrimeOnEtaleCharts_iff_hasUniqueIrreducibleComponent B S hS F x
  tfae_have 2 → 4 := isGeometricallyUnibranchAt_of_hasUniqueIrreducibleComponent B S hS F x
  tfae_have 4 → 3 := isUnibranchOnEtaleCharts_of_isGeometricallyUnibranchAt B S hS F x
  tfae_have 3 → 1 := hasUniqueMinimalPrimeOnEtaleCharts_of_isUnibranchOnEtaleCharts B S hS F x
  tfae_have 4 → 5 :=
    hasUniqueMinimalPrimeAtGeometricPoints_of_isGeometricallyUnibranchAt B S hS F hF x
  tfae_have 5 → 4 :=
    isGeometricallyUnibranchAt_of_hasUniqueMinimalPrimeAtGeometricPoints B S hS F hF x
  tfae_finish

end AlgebraicGeometry.Space

end
