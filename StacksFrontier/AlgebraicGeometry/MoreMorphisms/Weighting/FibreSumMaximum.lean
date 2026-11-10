module

public import Mathlib.Topology.Spectral.ConstructibleTopology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.WeightingInverse
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FibreCardinality
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumTerm
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.LevelSetConstructible
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFiniteUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ResidueDegreeBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.Properties.Constructible
public import StacksFrontier.Topology.Spectral.AsDirectedInverseLimit

/-!
# The maximum of a weighted fibre sum over a quasi-compact source

Let `f : X ⟶ Y` be a locally quasi-finite morphism with `X` quasi-compact and let `w : X → ℤ`
be a weighting of `f`. Then the weighted fibre sum of `w` along `f` is bounded above, and it
attains a greatest value on a nonempty target.

## Main results

* `AlgebraicGeometry.bddAbove_range_separableDegreeWeightedFiberSum`: the weighted fibre sum of a
  weighting along a locally quasi-finite morphism with quasi-compact source is bounded above.
* `AlgebraicGeometry.exists_isGreatest_range_separableDegreeWeightedFiberSum`: on a nonempty
  target that bound is achieved, so the weighted fibre sum has a greatest value.

## Implementation notes

Local quasi-finiteness is `AlgebraicGeometry.LocallyQuasiFinite` together with
`AlgebraicGeometry.LocallyOfFiniteType`, which is Tag 01TD's characterization, and
quasi-compactness of the source is `CompactSpace`.

Two finiteness statements combine into the bound. The level sets of a weighting are locally
constructible, so on an affine open they are constructible; an affine open of a scheme is a
spectral space and a partition of a spectral space into constructible parts has finitely many
nonempty parts, because the parts are open for the compact constructible topology. Finitely many
affine opens cover a quasi-compact source, so the weighting takes finitely many values and is
bounded above by some natural number `M`. Independently, a locally quasi-finite morphism with
quasi-compact source has universally bounded fibres, say of degree at most `N`; the sum of the
residue degrees at the points of a fibre is then at most `N`, and each term of the weighted fibre
sum is at most `M` times the residue degree at its point, since the separable degree of a finite
field extension is at most its dimension. So the weighted fibre sum never exceeds `M * N`.

Comparing the residue degree at a point of the source with the one appearing in the bound for a
field-valued base change takes two transports: the residue field of the scheme-theoretic fibre at
the image of a point is the residue field of the source at that point, and the two orders of the
fibre product have isomorphic residue fields over the base field.

A greatest value exists because a nonempty set of integers that is bounded above has a greatest
element; nonemptiness of the range of the weighted fibre sum is nonemptiness of the target.

## References

* [Stacks Project, Tag 0F3K](https://stacks.math.columbia.edu/tag/0F3K)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

open scoped Set.Notation

universe u

namespace AlgebraicGeometry

/-- A partition of a spectral space into constructible sets has only finitely many nonempty
parts: the parts are open for the constructible topology, which is compact. -/
private lemma finite_nonempty_of_constructible_partition
    {Z I : Type*} [TopologicalSpace Z] [SpectralSpace Z]
    (E : I → Set Z) (hE : ∀ i, Topology.IsConstructible (E i))
    (hcover : ∀ z, ∃ i, z ∈ E i)
    (hdisjoint : ∀ i j z, z ∈ E i → z ∈ E j → i = j) :
    {i | (E i).Nonempty}.Finite := by
  let O : I → Set (WithConstructibleTopology Z) := fun i ↦ WithTopology.ofTopology ⁻¹' E i
  have hO : ∀ i, IsOpen (O i) := by
    intro i
    apply WithConstructibleTopology.isOpen_iff.mpr
    change @IsOpen Z (constructibleTopology Z) (E i)
    rw [constructibleTopology_eq_generateFrom_isConstructible]
    exact TopologicalSpace.isOpen_generateFrom_of_mem (hE i)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover O hO (by
    intro z _
    obtain ⟨i, hi⟩ := hcover (WithTopology.ofTopology z)
    exact Set.mem_iUnion.mpr ⟨i, hi⟩)
  refine t.finite_toSet.subset ?_
  rintro i ⟨z, hz⟩
  obtain ⟨j, hjt, hzj⟩ := Set.mem_iUnion₂.mp
    (ht (Set.mem_univ (WithTopology.toTopology (constructibleTopology Z) z)))
  have hij : i = j := hdisjoint i j z hz hzj
  simpa [hij] using hjt

/-- A function on a quasi-compact scheme all of whose level sets are locally constructible takes
only finitely many values. -/
public lemma finite_range_of_isLocallyConstructible_levelSet
    {X : Scheme.{u}} [CompactSpace X] (w : X → ℤ)
    (hlevel : ∀ n : ℤ, Topology.IsLocallyConstructible {x : X | w x = n}) :
    (Set.range w).Finite := by
  classical
  obtain ⟨s, hs⟩ := isCompact_univ.elim_finite_subcover
      (fun U : X.affineOpens ↦ (U.1 : Set X)) (fun U ↦ U.1.2) (by
    intro x _
    obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    exact Set.mem_iUnion.mpr ⟨⟨V, hV⟩, hxV⟩)
  have hfinite (U : X.affineOpens) :
      {n : ℤ | ((U.1 : Set X) ↓∩ {x : X | w x = n}).Nonempty}.Finite := by
    let E : ℤ → Set (U.1 : Set X) := fun n ↦ (U.1 : Set X) ↓∩ {x : X | w x = n}
    let : SpectralSpace (U.1 : Set X) := spectralSpace_affineOpen U
    have hE : ∀ n, Topology.IsConstructible (E n) := fun n ↦
      (isLocallyConstructible_iff_forall_affineOpens {x : X | w x = n}).mp (hlevel n) U
    exact finite_nonempty_of_constructible_partition E hE (fun z ↦ ⟨w z.1, rfl⟩)
      (fun n m z hn hm ↦ hn.symm.trans hm)
  refine (Set.Finite.biUnion s.finite_toSet fun U _ ↦ hfinite U).subset ?_
  rintro n ⟨x, rfl⟩
  obtain ⟨U, hUs, hx⟩ := Set.mem_iUnion₂.mp (hs (Set.mem_univ x))
  exact Set.mem_iUnion₂.mpr ⟨U, hUs, ⟨⟨x, hx⟩, rfl⟩⟩

/-- The residue degree of `f` at a point of its source: the dimension of the residue field there
over the residue field of its image. -/
private noncomputable def residueDegree {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : ℕ :=
  letI : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  Module.finrank (Y.residueField (f x)) (X.residueField x)

/-- The term of a weighted fibre sum at a point of the fibre is at most any upper bound for the
weight times the residue degree at that point. -/
private lemma separableDegreeWeightedFiberTerm_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyQuasiFinite f] (w : X → ℤ) (M : ℕ)
    (hw : ∀ x : X, w x ≤ (M : ℤ)) (x : X) :
    letI : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    w x * (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ) ≤
      (M : ℤ) * (residueDegree f x : ℤ) := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  let : Module.Finite (Y.residueField (f x)) (X.residueField x) :=
    module_finite_residueFieldMap f x
  have hdeg : (0 : ℤ) ≤ (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ) :=
    Int.natCast_nonneg _
  calc
    w x * (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ) ≤
        (M : ℤ) * (Field.finSepDegree (Y.residueField (f x)) (X.residueField x) : ℤ) :=
      mul_le_mul_of_nonneg_right (hw x) hdeg
    _ ≤ (M : ℤ) * (residueDegree f x : ℤ) := by
      refine mul_le_mul_of_nonneg_left ?_ (Int.natCast_nonneg M)
      exact_mod_cast Field.finSepDegree_le_finrank (Y.residueField (f x)) (X.residueField x)

/-- Transport of a residue field along an isomorphism of schemes over the spectrum of a field:
the two residue fields are isomorphic as algebras over that field. -/
private noncomputable def residueFieldAlgEquivOfIsoOverSpec
    {K : Type u} [Field K] {Z W : Scheme.{u}}
    (p : Z ⟶ Spec (.of K)) (q : W ⟶ Spec (.of K)) (e : Z ≅ W)
    (h : e.hom ≫ q = p) (z : Z) :
    letI : Algebra K (Z.residueField z) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop ≫ Z.Γevaluation z).hom.toAlgebra
    letI : Algebra K (W.residueField (e.hom z)) :=
      ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫ W.Γevaluation (e.hom z)).hom.toAlgebra
    (W.residueField (e.hom z) : Type u) ≃ₐ[K] (Z.residueField z : Type u) := by
  letI : Algebra K (Z.residueField z) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop ≫ Z.Γevaluation z).hom.toAlgebra
  letI : Algebra K (W.residueField (e.hom z)) :=
    ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫ W.Γevaluation (e.hom z)).hom.toAlgebra
  let r : (W.residueField (e.hom z) : Type u) ≃+* (Z.residueField z : Type u) :=
    (asIso (e.hom.residueFieldMap z)).commRingCatIsoToRingEquiv
  have hsource : CommRingCat.ofHom (algebraMap K (Z.residueField z)) =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop ≫ Z.Γevaluation z) := rfl
  have htarget : CommRingCat.ofHom (algebraMap K (W.residueField (e.hom z))) =
      ((Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫ W.Γevaluation (e.hom z)) := rfl
  have hmap : (Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫
      W.Γevaluation (e.hom z) ≫ e.hom.residueFieldMap z =
      (Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop ≫ Z.Γevaluation z := by
    calc
      _ = (Scheme.ΓSpecIso (.of K)).inv ≫ q.appTop ≫
          (e.hom.appTop ≫ Z.Γevaluation z) := by
        rw [Scheme.Γevaluation_naturality]
      _ = (Scheme.ΓSpecIso (.of K)).inv ≫ p.appTop ≫ Z.Γevaluation z := by
        have happ := congrArg (fun m : Z ⟶ Spec (.of K) ↦ m.appTop) h
        have happ' : q.appTop ≫ e.hom.appTop = p.appTop := by
          simpa only [Scheme.Hom.comp_appTop] using happ
        simpa only [Category.assoc] using
          congrArg (fun a ↦ (Scheme.ΓSpecIso (.of K)).inv ≫ a ≫ Z.Γevaluation z) happ'
  have hr : CommRingCat.ofHom (r.toRingHom.comp
      (algebraMap K (W.residueField (e.hom z)))) =
      CommRingCat.ofHom (algebraMap K (Z.residueField z)) := by
    rw [CommRingCat.ofHom_comp, htarget, hsource]
    change _ ≫ e.hom.residueFieldMap z = _
    exact hmap
  exact AlgEquiv.ofRingEquiv (f := r) fun a ↦
    DFunLike.congr_fun (congrArg CommRingCat.Hom.hom hr) a

/-- The isomorphism exchanging the two orders of the fibre product defining a fibre, read as an
isomorphism over the spectrum of the residue field of the point. -/
private alias pullbackSymmetry_hom_comp_fst_fiber :=
  AlgebraicGeometry.pullbackSymmetry_hom_comp_fst_fiberToSpec

/-- The residue degree of `f` at a point of the fibre over `y` is the dimension over `κ(y)` of
the residue field of the base change of `f` to `Spec κ(y)` at the corresponding point. -/
private lemma residueDegree_fiberι_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y) (z : f.fiber y) :
    letI : Algebra (Y.residueField y)
        ((pullback (Y.fromSpecResidueField y) f).residueField
          ((pullbackSymmetry f (Y.fromSpecResidueField y)).hom z)) :=
      ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
        (pullback.fst (Y.fromSpecResidueField y) f).appTop ≫
        (pullback (Y.fromSpecResidueField y) f).Γevaluation
          ((pullbackSymmetry f (Y.fromSpecResidueField y)).hom z)).hom.toAlgebra
    residueDegree f (f.fiberι y z) =
      Module.finrank (Y.residueField y)
        ((pullback (Y.fromSpecResidueField y) f).residueField
          ((pullbackSymmetry f (Y.fromSpecResidueField y)).hom z)) := by
  have hz : f (f.fiberι y z) = y := (f.fiberHomeo y z).property
  -- First compare the residue field of the source with the one of the fibre.
  have hfiber : residueDegree f (f.fiberι y z) =
      let : Algebra (Y.residueField y) ((f.fiber y).residueField z) :=
        ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
          (f.fiberToSpecResidueField y).appTop ≫ (f.fiber y).Γevaluation z).hom.toAlgebra
      Module.finrank (Y.residueField y) ((f.fiber y).residueField z) := by
    set x : X := f.fiberι y z with hxdef
    clear_value x
    cases hz
    have hzx : z = f.asFiber x := by
      apply (f.fiberHomeo (f x)).injective
      apply Subtype.ext
      simpa only [Scheme.Hom.fiberHomeo_apply, Scheme.Hom.fiberι_asFiber] using hxdef.symm
    cases hzx
    let : Algebra (Y.residueField (f x)) (X.residueField x) :=
      (f.residueFieldMap x).hom.toAlgebra
    let : Algebra (Y.residueField (f x))
        ((f.fiber (f x)).residueField (f.asFiber x)) :=
      ((Scheme.ΓSpecIso (Y.residueField (f x))).inv ≫
        (f.fiberToSpecResidueField (f x)).appTop ≫
        (f.fiber (f x)).Γevaluation (f.asFiber x)).hom.toAlgebra
    let a : (X.residueField x : Type u) ≃ₐ[Y.residueField (f x)]
        ((f.fiber (f x)).residueField (f.asFiber x) : Type u) :=
      AlgEquiv.ofRingEquiv
        (f := RingEquiv.ofBijective (f.fiberResidueFieldHom x).hom
          (f.bijective_fiberResidueFieldHom x)) fun b ↦ by
        have hb := DFunLike.congr_fun
          (congrArg CommRingCat.Hom.hom (f.fiberResidueFieldHom_algebraMap x)) b
        simp only [CommRingCat.hom_ofHom, CommRingCat.hom_comp, RingHom.coe_comp,
          Function.comp_apply] at hb
        exact hb.symm
    exact a.toLinearEquiv.finrank_eq
  -- Then transport along the symmetry of the fibre product.
  rw [hfiber]
  let : Algebra (Y.residueField y) ((f.fiber y).residueField z) :=
    ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
      (f.fiberToSpecResidueField y).appTop ≫ (f.fiber y).Γevaluation z).hom.toAlgebra
  let : Algebra (Y.residueField y)
      ((pullback (Y.fromSpecResidueField y) f).residueField
        ((pullbackSymmetry f (Y.fromSpecResidueField y)).hom z)) :=
    ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
      (pullback.fst (Y.fromSpecResidueField y) f).appTop ≫
      (pullback (Y.fromSpecResidueField y) f).Γevaluation
        ((pullbackSymmetry f (Y.fromSpecResidueField y)).hom z)).hom.toAlgebra
  exact ((residueFieldAlgEquivOfIsoOverSpec (K := Y.residueField y)
    (f.fiberToSpecResidueField y) (pullback.fst (Y.fromSpecResidueField y) f)
    (pullbackSymmetry f (Y.fromSpecResidueField y))
    (pullbackSymmetry_hom_comp_fst_fiber f y) z).toLinearEquiv.finrank_eq).symm

/-- A degree bound for all field-valued base changes of `f` bounds the number of points of every
fibre. -/
private alias finite_fiber_of_degree_le := AlgebraicGeometry.finite_fiber_of_bounded_degree

/-- A degree bound for all field-valued base changes of `f` bounds the sum of the residue degrees
at the points of a fibre. -/
private lemma sum_residueDegree_fiber_le
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (N : ℕ)
    (hN : ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ Y),
      ∃ r ≤ N, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g f) r)
    (y : Y) [Fintype (f.fiber y)] :
    (∑ z : f.fiber y, residueDegree f (f.fiberι y z)) ≤ N := by
  classical
  let P : Scheme.{u} := pullback (Y.fromSpecResidueField y) f
  let e : f.fiber y ≅ P := pullbackSymmetry f (Y.fromSpecResidueField y)
  let ePts : f.fiber y ≃ P := e.hom.homeomorph.toEquiv
  let t : ℕ := Fintype.card (f.fiber y)
  let eFin : Fin t ≃ P := (Fintype.equivFin (f.fiber y)).symm.trans ePts
  let ψ : P → ℕ := fun z ↦
    let : Algebra (Y.residueField y) (P.residueField z) :=
      ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
        (pullback.fst (Y.fromSpecResidueField y) f).appTop ≫
        P.Γevaluation z).hom.toAlgebra
    Module.finrank (Y.residueField y) (P.residueField z)
  calc
    (∑ z : f.fiber y, residueDegree f (f.fiberι y z)) = ∑ z : f.fiber y, ψ (ePts z) :=
      Finset.sum_congr rfl fun z _ ↦ residueDegree_fiberι_eq f y z
    _ = ∑ i, ψ (eFin i) :=
      Fintype.sum_equiv (Fintype.equivFin (f.fiber y)) (fun z ↦ ψ (ePts z))
        (fun i ↦ ψ (eFin i)) fun z ↦ by
          simp only [eFin, Equiv.trans_apply, Equiv.symm_apply_apply]
    _ ≤ N := sum_finrank_residueField_le_of_degree_le f N hN (Y.residueField y)
      (Y.fromSpecResidueField y) eFin eFin.injective

/-- The weighted fibre sum of a weight bounded above by `M` along a morphism all of whose
field-valued base changes have degree at most `N` is at most `M * N`. -/
private lemma separableDegreeWeightedFiberSum_le_mul
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    (w : X → ℤ) (M N : ℕ) (hw : ∀ x : X, w x ≤ (M : ℤ))
    (hN : ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ Y),
      ∃ r ≤ N, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g f) r)
    (y : Y) :
    separableDegreeWeightedFiberSum f w y ≤ (M : ℤ) * (N : ℤ) := by
  classical
  let : Finite (f.fiber y) := finite_fiber_of_degree_le f N hN y
  let : Fintype (f.fiber y) := Fintype.ofFinite _
  let eFib : f.fiber y ≃ {x : X // f x = y} :=
    (f.fiberHomeo y).toEquiv.trans (Equiv.subtypeEquivRight fun _ ↦ Iff.rfl)
  let : Fintype {x : X // f x = y} := Fintype.ofEquiv _ eFib
  let term : {x : X // f x = y} → ℤ := fun x ↦
    let : Algebra (Y.residueField (f x.1)) (X.residueField x.1) :=
      (f.residueFieldMap x.1).hom.toAlgebra
    w x.1 * (Field.finSepDegree (Y.residueField (f x.1)) (X.residueField x.1) : ℤ)
  have hsumFib : (∑ x : {x : X // f x = y}, (residueDegree f x.1 : ℤ)) ≤ (N : ℤ) := by
    have hnat : (∑ x : {x : X // f x = y}, residueDegree f x.1) ≤ N :=
      (Fintype.sum_equiv eFib (fun z ↦ residueDegree f (f.fiberι y z))
        (fun x ↦ residueDegree f x.1) fun _ ↦ rfl).symm.trans_le
        (sum_residueDegree_fiber_le f N hN y)
    exact_mod_cast hnat
  calc
    separableDegreeWeightedFiberSum f w y = ∑ᶠ x : {x : X // f x = y}, term x :=
      separableDegreeWeightedFiberSum_eq_finsum_fiber f w y
    _ = ∑ x : {x : X // f x = y}, term x := finsum_eq_sum_of_fintype term
    _ ≤ ∑ x : {x : X // f x = y}, (M : ℤ) * (residueDegree f x.1 : ℤ) :=
      Finset.sum_le_sum fun x _ ↦ separableDegreeWeightedFiberTerm_le f w M hw x.1
    _ = (M : ℤ) * ∑ x : {x : X // f x = y}, (residueDegree f x.1 : ℤ) := by
      rw [← Finset.mul_sum]
    _ ≤ (M : ℤ) * (N : ℤ) := mul_le_mul_of_nonneg_left hsumFib (Int.natCast_nonneg M)

/-- **Stacks Project, Tag 0F3K.** The weighted fibre sum of a weighting of a locally quasi-finite
morphism with quasi-compact source is bounded above.

This is the bound from which the maximum of
`AlgebraicGeometry.exists_isGreatest_range_separableDegreeWeightedFiberSum` is obtained. -/
public theorem bddAbove_range_separableDegreeWeightedFiberSum
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] {w : X → ℤ} (hw : IsWeighting f w) :
    BddAbove (Set.range (separableDegreeWeightedFiberSum f w)) := by
  classical
  -- An upper bound `M` for the weight, from the finiteness of its set of values.
  have hrange : (Set.range w).Finite :=
    finite_range_of_isLocallyConstructible_levelSet w fun n ↦
      isLocallyConstructible_weighting_levelSet hw n
  have habs : (Int.natAbs '' Set.range w).Finite := hrange.image Int.natAbs
  let M : ℕ := habs.toFinset.sup id
  have hwM : ∀ x : X, w x ≤ (M : ℤ) := by
    intro x
    have hle : (w x).natAbs ≤ M :=
      Finset.le_sup (s := habs.toFinset) (f := id) (b := (w x).natAbs)
        (habs.mem_toFinset.mpr (Set.mem_image_of_mem Int.natAbs (Set.mem_range_self x)))
    have habsle : |w x| ≤ (M : ℤ) := by
      rw [← Int.natCast_natAbs]
      exact_mod_cast hle
    exact (abs_le.mp habsle).2
  -- A degree bound `N` for the fibres, from universal boundedness.
  obtain ⟨n, hn⟩ := hasUniversallyBoundedFibers_of_locallyQuasiFinite f
  let N : ℕ := n.toNat
  have hfield : ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ Y),
      ∃ r ≤ N, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g f) r := by
    intro k _ g
    obtain ⟨r, hr, hrank⟩ := (boundsFiberDegrees_iff_field_baseChange f n).mp hn k g
    exact ⟨r, by exact_mod_cast hr.trans (Int.self_le_toNat n), hrank⟩
  exact ⟨(M : ℤ) * (N : ℤ), Set.forall_mem_range.2 fun y ↦
    separableDegreeWeightedFiberSum_le_mul f w M N hwM hfield y⟩

/-- **Stacks Project, Tag 0F3K.** The weighted fibre sum of a weighting of a locally quasi-finite
morphism with quasi-compact source attains its maximum: its set of values has a greatest
element.

The target is assumed nonempty, which the source does not say and without which the set of
values is empty and has no greatest element. -/
@[stacks 0F3K "the target is assumed nonempty"]
public theorem exists_isGreatest_range_separableDegreeWeightedFiberSum
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] [LocallyQuasiFinite f]
    [CompactSpace X] [Nonempty Y] {w : X → ℤ} (hw : IsWeighting f w) :
    ∃ d : ℤ, IsGreatest (Set.range (separableDegreeWeightedFiberSum f w)) d :=
  (bddAbove_range_separableDegreeWeightedFiberSum f hw).exists_isGreatest_of_nonempty
    (Set.range_nonempty _)

end AlgebraicGeometry

end
