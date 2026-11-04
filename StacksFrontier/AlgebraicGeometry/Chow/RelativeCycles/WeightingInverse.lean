module

public import Mathlib.Algebra.CharP.Algebra
public import Mathlib.Algebra.Ring.ULift
public import Mathlib.Data.ZMod.Basic
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.FamilyCoeff
public import StacksFrontier.AlgebraicGeometry.Chow.RelativeCycles.Weighting
public import StacksFrontier.AlgebraicGeometry.F6Rank128.FiberResidueField
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.FibreCardinality
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.QuasiFiniteUniversallyBounded
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.ResidueDegreeBound
public import StacksFrontier.AlgebraicGeometry.Morphisms.FibreDimension.UniversallyBoundedBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumTerm
public import StacksCore.Tactic.StacksAttribute

/-!
# Reconstructing a family of zero-cycles from a weighting

Let `f : X ⟶ S` be locally quasi-finite and locally of finite type, so that every fibre of `f`
is a finite discrete set of points whose residue fields are finite extensions of the residue
field of the base point. Given an integer-valued function `w` on `X` and a natural number `n`
divisible by all the inseparable degrees `[κ(x) : κ(f x)]_i`, the recipe
`α_s = ∑_{f x = s} (n · w x / [κ(x) : κ(f x)]_i) [x]` defines a family of `0`-cycles on the
fibres of `f` whose attached weighting `Stacks.Chow.relativeCycleWeight` is `n · w`. This is the
inverse construction of the converse direction of the source.

Such an `n` exists whenever the source is quasi-compact: a locally quasi-finite morphism locally
of finite type with quasi-compact source has universally bounded fibres (Tag 03JA), so the
residue-field degrees along `f` admit a uniform bound `N`, and `N !` is divisible by every
inseparable degree. Over a base all of whose residue fields have exponential characteristic `p`
the inseparable degrees are powers of `p`, so `n` may be taken to be a power of `p`.

## Main definitions

* `AlgebraicGeometry.residueFinInsepDegree` — the inseparable degree `[κ(x) : κ(f x)]_i` of the
  residue-field extension of a morphism at a point, as a natural number.
* `Stacks.Chow.weightingQuotient` — the integer `n · w x / [κ(x) : κ(f x)]_i`.
* `Stacks.Chow.cycleOfWeighting` — the family of `0`-cycles on the fibres of `f` built from a
  function on `X` and a multiplier `n`.

## Main results

* `Stacks.Chow.mem_cyclesOfDimension_zero_of_locallyQuasiFinite` — for a locally quasi-finite
  morphism every cycle on a fibre is a `0`-cycle, the residue-field extensions being finite.
* `Stacks.Chow.relativeCycleWeight_cycleOfWeighting` — the weighting attached to
  `Stacks.Chow.cycleOfWeighting` is `n · w`, provided every inseparable degree divides `n`.
* `AlgebraicGeometry.exists_pos_forall_finInsepDegree_dvd` — for a quasi-compact source there is
  a positive `n` divisible by every inseparable degree, and every fibre is finite.
* `AlgebraicGeometry.exists_primePow_forall_finInsepDegree_dvd` — over a base of exponential
  characteristic `p` that `n` can be taken to be a power of `p`.
* `AlgebraicGeometry.expChar_residueField_of_over_zmod` — the residue fields of a scheme over
  `Spec (ZMod p)` have exponential characteristic `p`.

## Implementation notes

The coefficient of `Stacks.Chow.cycleOfWeighting` at a point `y` of the fibre over `s` is read
off at the point `f.fiberι s y` of `X`, so no transport between `S.residueField s` and
`S.residueField (f (f.fiberι s y))` is ever needed; the comparison with
`Stacks.Chow.relativeCycleWeight` is then a single rewrite along
`AlgebraicGeometry.Scheme.Hom.fiberι_asFiber`. For this the coefficient is packaged as the
function `Stacks.Chow.weightingQuotient` on `X`, which depends on the point only through a
non-dependent argument; writing the inseparable degree inline would put the point inside the
`Algebra` instance of `Field.finInsepDegree` and make that rewrite ill-typed.

Local finiteness of the support is free because the fibre is a finite set, which is part of the
hypothesis, and membership in the degree-zero part holds for every cycle on a fibre because the
residue-field extensions of a locally quasi-finite morphism are finite, hence of transcendence
degree zero, while the dimension function of `Stacks.Chow.fieldChowSituation` vanishes.

The bound on the residue-field degrees is extracted from `HasUniversallyBoundedFibers` through
`AlgebraicGeometry.sum_finrank_residueField_le_of_degree_le` applied to a one-element family of
points, and transported to the residue field of the source at the point by two isomorphisms: the
residue field of the fibre at `f.asFiber x` is `κ(x)`, and the two orders of the fibre product
defining the fibre have isomorphic residue fields over the base field. These transports repeat,
under fresh names, private material of
`StacksFrontier.AlgebraicGeometry.MoreMorphisms.Weighting.FibreSumMaximum`.

## References

* [Stacks Project, Tag 0H5P](https://stacks.math.columbia.edu/tag/0H5P)
* [Stacks Project, Tag 03JA](https://stacks.math.columbia.edu/tag/03JA)
* [Stacks Project, Tag 03J5](https://stacks.math.columbia.edu/tag/03J5)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u

namespace AlgebraicGeometry

/-! ### The inseparable degree of a residue-field extension -/

/-- The inseparable degree `[κ(x) : κ(f x)]_i` of the residue-field extension of a morphism of
schemes at a point of its source. -/
def residueFinInsepDegree {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : ℕ :=
  letI : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  Field.finInsepDegree (Y.residueField (f x)) (X.residueField x)

/-- The degree `[κ(x) : κ(f x)]` of the residue-field extension of a morphism of schemes at a
point of its source. -/
@[ega "IV 21.10.10" "partial"]
private def fiberResidueFinrank {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X) : ℕ :=
  letI : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  Module.finrank (Y.residueField (f x)) (X.residueField x)

/-- The inseparable degree of a finite residue-field extension is positive and at most the full
degree, because the separable degree is positive and the two degrees multiply to the full
degree. -/
private lemma residueFinInsepDegree_pos_le {X Y : Scheme.{u}} (f : X ⟶ Y)
    [LocallyQuasiFinite f] (x : X) :
    0 < residueFinInsepDegree f x ∧ residueFinInsepDegree f x ≤ fiberResidueFinrank f x := by
  let : Algebra (Y.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  let : Module.Finite (Y.residueField (f x)) (X.residueField x) :=
    module_finite_residueFieldMap f x
  have hmul : Field.finSepDegree (Y.residueField (f x)) (X.residueField x) *
      Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) =
      Module.finrank (Y.residueField (f x)) (X.residueField x) :=
    Field.finSepDegree_mul_finInsepDegree _ _
  have hprod : 0 < Field.finSepDegree (Y.residueField (f x)) (X.residueField x) *
      Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) := by
    rw [hmul]; exact Module.finrank_pos
  obtain ⟨hsep, hins⟩ := CanonicallyOrderedAdd.mul_pos.mp hprod
  refine ⟨hins, ?_⟩
  show Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) ≤
    Module.finrank (Y.residueField (f x)) (X.residueField x)
  calc Field.finInsepDegree (Y.residueField (f x)) (X.residueField x)
      ≤ Field.finSepDegree (Y.residueField (f x)) (X.residueField x) *
        Field.finInsepDegree (Y.residueField (f x)) (X.residueField x) :=
        Nat.le_mul_of_pos_left _ hsep
    _ = Module.finrank (Y.residueField (f x)) (X.residueField x) := hmul

/-! ### Transport of residue fields over the spectrum of a field -/

/-- Transport of a residue field along an isomorphism of schemes over the spectrum of a field:
the two residue fields are isomorphic as algebras over that field. -/
private def residueFieldAlgEquivOverSpecIso
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
lemma pullbackSymmetry_hom_comp_fst_fiberToSpec {X Y : Scheme.{u}} (f : X ⟶ Y) (y : Y) :
    (pullbackSymmetry f (Y.fromSpecResidueField y)).hom ≫
        pullback.fst (Y.fromSpecResidueField y) f = f.fiberToSpecResidueField y :=
  pullbackSymmetry_hom_comp_fst f (Y.fromSpecResidueField y)

/-- The residue degree of `f` at a point of the fibre over `y` is the dimension over `κ(y)` of
the residue field of the base change of `f` to `Spec κ(y)` at the corresponding point. -/
private lemma fiberResidueFinrank_fiberι_eq
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (y : Y) (z : f.fiber y) :
    letI : Algebra (Y.residueField y)
        ((pullback (Y.fromSpecResidueField y) f).residueField
          ((pullbackSymmetry f (Y.fromSpecResidueField y)).hom z)) :=
      ((Scheme.ΓSpecIso (Y.residueField y)).inv ≫
        (pullback.fst (Y.fromSpecResidueField y) f).appTop ≫
        (pullback (Y.fromSpecResidueField y) f).Γevaluation
          ((pullbackSymmetry f (Y.fromSpecResidueField y)).hom z)).hom.toAlgebra
    fiberResidueFinrank f (f.fiberι y z) =
      Module.finrank (Y.residueField y)
        ((pullback (Y.fromSpecResidueField y) f).residueField
          ((pullbackSymmetry f (Y.fromSpecResidueField y)).hom z)) := by
  have hz : f (f.fiberι y z) = y := (f.fiberHomeo y z).property
  -- First compare the residue field of the source with the one of the fibre.
  have hfiber : fiberResidueFinrank f (f.fiberι y z) =
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
  exact ((residueFieldAlgEquivOverSpecIso (K := Y.residueField y)
    (f.fiberToSpecResidueField y) (pullback.fst (Y.fromSpecResidueField y) f)
    (pullbackSymmetry f (Y.fromSpecResidueField y))
    (pullbackSymmetry_hom_comp_fst_fiberToSpec f y) z).toLinearEquiv.finrank_eq).symm

/-! ### A uniform bound on the residue degrees -/

/-- A degree bound for all field-valued base changes of `f` bounds the number of points of every
fibre. -/
lemma finite_fiber_of_bounded_degree
    {X Y : Scheme.{u}} (f : X ⟶ Y) (N : ℕ)
    (hN : ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ Y),
      ∃ r ≤ N, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g f) r)
    (y : Y) : Finite (f.fiber y) := by
  have hcard := cardinalMk_pullback_le_of_degree_le f N hN (Y.residueField y)
    (Y.fromSpecResidueField y)
  have hlt : Cardinal.mk
      (pullback (C := Scheme.{u}) (Y.fromSpecResidueField y) f : Scheme.{u}) <
      Cardinal.aleph0 := lt_of_le_of_lt hcard Cardinal.natCast_lt_aleph0
  have hfinite : Finite (pullback (C := Scheme.{u}) (Y.fromSpecResidueField y) f) :=
    Cardinal.lt_aleph0_iff_finite.mp hlt
  exact Finite.of_injective
    ((pullbackSymmetry f (Y.fromSpecResidueField y)).hom.homeomorph.toEquiv)
    ((pullbackSymmetry f (Y.fromSpecResidueField y)).hom.homeomorph.toEquiv).injective

/-- A degree bound for all field-valued base changes of `f` bounds the degree of the
residue-field extension at every point of the source. -/
private lemma fiberResidueFinrank_le_of_bounded_degree
    {X Y : Scheme.{u}} (f : X ⟶ Y) [LocallyOfFiniteType f] (N : ℕ)
    (hN : ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ Y),
      ∃ r ≤ N, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g f) r)
    (x : X) : fiberResidueFinrank f x ≤ N := by
  have hsum := sum_finrank_residueField_le_of_degree_le f N hN (Y.residueField (f x))
    (Y.fromSpecResidueField (f x)) (t := 1)
    (fun _ ↦ (pullbackSymmetry f (Y.fromSpecResidueField (f x))).hom (f.asFiber x))
    (fun a b _ ↦ Subsingleton.elim a b)
  simp only [Fin.sum_univ_one] at hsum
  have heq := fiberResidueFinrank_fiberι_eq f (f x) (f.asFiber x)
  rw [Scheme.Hom.fiberι_asFiber] at heq
  rw [heq]
  exact hsum

/-- For a locally quasi-finite morphism locally of finite type with quasi-compact source the
inseparable degrees of the residue-field extensions are positive and uniformly bounded, and
every fibre is finite. -/
private lemma exists_bound_residueFinInsepDegree {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [CompactSpace X] :
    ∃ N : ℕ, (∀ s : S, Finite (f.fiber s)) ∧
      ∀ x : X, 0 < residueFinInsepDegree f x ∧ residueFinInsepDegree f x ≤ N := by
  obtain ⟨N, hN⟩ := hasUniversallyBoundedFibers_of_locallyQuasiFinite f
  have hbase : ∀ (k : Type u) [Field k] (g : Spec (.of k) ⟶ S),
      ∃ r ≤ N.toNat, Stacks.Morphisms.IsFiniteLocallyFreeOfRank (pullback.fst g f) r := by
    intro k _ g
    obtain ⟨r, hr, hrank⟩ := (boundsFiberDegrees_iff_field_baseChange f N).mp hN k g
    exact ⟨r, by simpa using Int.toNat_le_toNat hr, hrank⟩
  refine ⟨N.toNat, fun s ↦ finite_fiber_of_bounded_degree f N.toNat hbase s, fun x ↦
    ⟨(residueFinInsepDegree_pos_le f x).1,
      (residueFinInsepDegree_pos_le f x).2.trans
        (fiberResidueFinrank_le_of_bounded_degree f N.toNat hbase x)⟩⟩

/-! ### Sufficiently divisible multipliers -/

/-- For a locally quasi-finite morphism locally of finite type with quasi-compact source, the
inseparable degrees of the residue-field extensions are bounded, so there is a positive integer
divisible by all of them, and every fibre is finite. -/
theorem exists_pos_forall_finInsepDegree_dvd {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] [CompactSpace X] :
    ∃ n : ℕ, 0 < n ∧ (∀ s : S, Finite (f.fiber s)) ∧
      ∀ x : X, letI := (f.residueFieldMap x).hom.toAlgebra
        (Field.finInsepDegree (S.residueField (f x)) (X.residueField x)) ∣ n := by
  obtain ⟨N, hfin, hbound⟩ := exists_bound_residueFinInsepDegree f
  refine ⟨N.factorial, Nat.factorial_pos N, hfin, fun x ↦ ?_⟩
  exact Nat.dvd_factorial (hbound x).1 (hbound x).2

/-- Over a scheme of characteristic `p`, the integer of
`AlgebraicGeometry.exists_pos_forall_finInsepDegree_dvd` can be taken to be a power of `p`. -/
theorem exists_primePow_forall_finInsepDegree_dvd {X S : Scheme.{u}}
    (f : X ⟶ S) [LocallyOfFiniteType f] [LocallyQuasiFinite f] [CompactSpace X]
    (p : ℕ) [hp : Fact p.Prime]
    (hchar : ∀ s : S, ExpChar (S.residueField s) p) :
    ∃ e : ℕ, (∀ s : S, Finite (f.fiber s)) ∧
      ∀ x : X, letI := (f.residueFieldMap x).hom.toAlgebra
        (Field.finInsepDegree (S.residueField (f x)) (X.residueField x)) ∣ p ^ e := by
  obtain ⟨N, hfin, hbound⟩ := exists_bound_residueFinInsepDegree f
  refine ⟨N, hfin, fun x ↦ ?_⟩
  let : Algebra (S.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  let : Module.Finite (S.residueField (f x)) (X.residueField x) :=
    module_finite_residueFieldMap f x
  let : ExpChar (S.residueField (f x)) p := hchar (f x)
  obtain ⟨m, hm⟩ := finInsepDegree_eq_pow (S.residueField (f x) : Type u)
    (X.residueField x : Type u) p
  have hmdeg : residueFinInsepDegree f x = p ^ m := hm
  have hle : p ^ m ≤ N := hmdeg ▸ (hbound x).2
  have hmle : m ≤ N := le_of_lt (lt_of_lt_of_le (Nat.lt_pow_self hp.out.one_lt) hle)
  show residueFinInsepDegree f x ∣ p ^ N
  rw [hmdeg]
  exact pow_dvd_pow p hmle

/-- The residue fields of a scheme over `Spec (ZMod p)` have exponential characteristic `p`: the
structure morphism induces a ring map from `ZMod p` to every residue field, and a ring map out of
a field is injective. -/
theorem expChar_residueField_of_over_zmod {S : Scheme.{u}} (p : ℕ)
    [Fact p.Prime] (σ : S ⟶ Spec (CommRingCat.of (ULift.{u} (ZMod p)))) (s : S) :
    ExpChar (S.residueField s) p := by
  let : ExpChar (ZMod p) p := ExpChar.prime Fact.out
  let φ : ULift.{u} (ZMod p) →+* (S.residueField s : Type u) :=
    ((Scheme.ΓSpecIso (CommRingCat.of (ULift.{u} (ZMod p)))).inv ≫ σ.appTop ≫
      S.Γevaluation s).hom
  let ψ : ZMod p →+* (S.residueField s : Type u) :=
    φ.comp (ULift.ringEquiv (R := ZMod p)).symm.toRingHom
  exact expChar_of_injective_ringHom (f := ψ) ψ.injective p

end AlgebraicGeometry

namespace Stacks.Chow

/-! ### Every cycle on a fibre of a locally quasi-finite morphism is a zero-cycle -/

/-- The residue-field extension of a locally quasi-finite morphism at a point is finite, hence
of transcendence degree zero. -/
theorem residueTrdeg_eq_zero_of_locallyQuasiFinite {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyQuasiFinite f] (x : X) : residueTrdeg f x = 0 := by
  let : Algebra (S.residueField (f x)) (X.residueField x) := (f.residueFieldMap x).hom.toAlgebra
  let : Module.Finite (S.residueField (f x)) (X.residueField x) :=
    module_finite_residueFieldMap f x
  show Algebra.trdeg (S.residueField (f x)) (X.residueField x) = 0
  exact trdeg_eq_zero_iff.mpr (Algebra.IsAlgebraic.of_finite _ _)

/-- Every point of a scheme-theoretic fibre of a locally quasi-finite morphism has relative
dimension zero over the residue field of the base point. -/
theorem relativeDimension_fiber_eq_zero_of_locallyQuasiFinite {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (s : S) (y : f.fiber s) :
    relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) y = 0 := by
  have htr : Cardinal.toNat (residueTrdeg (f.fiberToSpecResidueField s) y) = 0 := by
    rw [residueTrdeg_fiberToSpecResidueField,
      residueTrdeg_eq_zero_of_locallyQuasiFinite f (f.fiberι s y)]
    simp
  have hrel : relativeDimension (fieldChowSituation (S.residueField s)).dimensionFunction
      (f.fiberToSpecResidueField s) y =
      (fieldChowSituation (S.residueField s)).dimensionFunction
          (f.fiberToSpecResidueField s y) +
        (Cardinal.toNat (residueTrdeg (f.fiberToSpecResidueField s) y) : ℤ) := rfl
  rw [hrel, htr, Nat.cast_zero, add_zero]
  exact fieldChowSituation_dimensionFunction_eq_zero _ _

/-- For a locally quasi-finite morphism every algebraic cycle on a scheme-theoretic fibre is a
`0`-cycle, since every point of the fibre has relative dimension zero. -/
theorem mem_cyclesOfDimension_zero_of_locallyQuasiFinite {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (s : S)
    (c : AlgebraicCycle (f.fiber s) ℤ) :
    letI : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
      change LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s))
      infer_instance
    c ∈ cyclesOfDimension (fieldChowSituation (S.residueField s))
      (f.fiberToSpecResidueField s) ((0 : ℕ) : ℤ) := by
  have : LocallyOfFiniteType (f.fiberToSpecResidueField s) := by
    show LocallyOfFiniteType (pullback.snd f (S.fromSpecResidueField s))
    infer_instance
  rw [mem_cyclesOfDimension_iff_forall_point]
  intro y _
  simpa using relativeDimension_fiber_eq_zero_of_locallyQuasiFinite f s y

/-! ### The inverse construction -/

/-- The integer `n · w x / [κ(x) : κ(f x)]_i` attached to a function `w` on the source of `f`, a
multiplier `n` and a point `x`. The division is integer division; it is exact as soon as the
inseparable degree divides `n`. -/
def weightingQuotient {X S : Scheme.{u}} (f : X ⟶ S) (w : X → ℤ) (n : ℕ) (x : X) : ℤ :=
  (n : ℤ) * w x / (residueFinInsepDegree f x : ℤ)

/-- The family of `0`-cycles on the fibres of `f` with
`α_s = ∑_{f x = s} (n · w x / [κ(x) : κ(f x)]_i) [x]`. -/
def cycleOfWeighting {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (w : X → ℤ) (n : ℕ)
    (hfin : ∀ s : S, Finite (f.fiber s)) : FamilyOfCycles f 0 := fun s ↦
  ⟨({ toFun := fun y ↦ weightingQuotient f w n (f.fiberι s y)
      supportWithinDomain' := Set.subset_univ _
      supportLocallyFiniteWithinDomain' := fun _ _ ↦
        ⟨Set.univ, Filter.univ_mem, by
          have := hfin s
          exact Set.finite_univ.subset (Set.subset_univ _)⟩ } :
      AlgebraicCycle (f.fiber s) ℤ),
    mem_cyclesOfDimension_zero_of_locallyQuasiFinite f s _⟩

/-- The coefficients of `Stacks.Chow.cycleOfWeighting`, read at a point of a fibre. -/
theorem coe_cycleOfWeighting_apply {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (w : X → ℤ) (n : ℕ)
    (hfin : ∀ s : S, Finite (f.fiber s)) (s : S) (y : f.fiber s) :
    (cycleOfWeighting f w n hfin s : AlgebraicCycle (f.fiber s) ℤ) y =
      weightingQuotient f w n (f.fiberι s y) :=
  rfl

/-- Under the divisibility hypothesis, `w_α = n·w`. -/
theorem relativeCycleWeight_cycleOfWeighting {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFiniteType f] [LocallyQuasiFinite f] (w : X → ℤ) (n : ℕ)
    (hfin : ∀ s : S, Finite (f.fiber s))
    (hdvd : ∀ x : X, letI := (f.residueFieldMap x).hom.toAlgebra
      (Field.finInsepDegree (S.residueField (f x)) (X.residueField x)) ∣ n) (x : X) :
    relativeCycleWeight f (cycleOfWeighting f w n hfin) x = (n : ℤ) * w x := by
  have hd : residueFinInsepDegree f x ∣ n := hdvd x
  have hdZ : ((residueFinInsepDegree f x : ℤ)) ∣ (n : ℤ) * w x :=
    Dvd.dvd.mul_right (Int.natCast_dvd_natCast.mpr hd) _
  rw [relativeCycleWeight_apply, coe_cycleOfWeighting_apply, Scheme.Hom.fiberι_asFiber]
  show weightingQuotient f w n x * (residueFinInsepDegree f x : ℤ) = (n : ℤ) * w x
  exact Int.ediv_mul_cancel hdZ

end Stacks.Chow

end
