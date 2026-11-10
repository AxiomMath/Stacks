module

public import Mathlib.AlgebraicGeometry.Geometrically.Reduced
public import Mathlib.AlgebraicGeometry.Stalk
public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.PurelyInseparable.AdjoinPthRoots
public import Mathlib.FieldTheory.SeparablyGenerated
public import Mathlib.RingTheory.LocalProperties.Reduced
public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.PullbackStalk
public import StacksFrontier.FieldTheory.PerfectClosure
public import StacksFrontier.RingTheory.GeometricallyReduced.TFAE
public import StacksFrontier.RingTheory.GeometricallyReduced.TensorProduct

/-!
# Geometrically reduced schemes

A scheme over a field is geometrically reduced at a point if every point above it after an
arbitrary field extension has a reduced local ring. It is geometrically reduced over the field
if this holds at every point. Geometric reducedness at a point is detected by the local ring at
that point, and over a perfect field it is implied by plain reducedness.

## Main definitions

* `AlgebraicGeometry.IsGeometricallyReducedAt` expresses geometric reducedness at a point.
* `AlgebraicGeometry.IsGeometricallyReducedOver` expresses geometric reducedness over the
  ground field, as geometric reducedness at every point.

## Main results

* `AlgebraicGeometry.geometricallyReduced_iff_forall_isGeometricallyReducedAt` identifies
  Mathlib's global notion with geometric reducedness at every point.
* `AlgebraicGeometry.isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk` characterizes
  geometric reducedness at a point by geometric reducedness of the corresponding local ring.
* `AlgebraicGeometry.isGeometricallyReducedAt_of_isReduced` and
  `AlgebraicGeometry.geometricallyReduced_of_isReduced` treat a perfect ground field.

## Implementation notes

[Stacks, Tag 035V] defines geometric reducedness at a point and over the field;
`AlgebraicGeometry.IsGeometricallyReducedOver` states both of its parts — the pointwise
condition of part (1) under a quantifier over every point, which is part (2) — and carries the
tag. Mathlib's more general predicate `AlgebraicGeometry.GeometricallyReduced` on a morphism of
schemes is the notion of part (2) for an arbitrary base: over the spectrum of a field, its
definition by reducedness after every field-valued base change is equivalent to the pointwise
formulation, and that is what
`AlgebraicGeometry.geometricallyReduced_iff_forall_isGeometricallyReducedAt` says. The
algebra structure on a local ring is the
composite of the canonical map from the ground field to the stalk of its spectrum and the stalk
map of the structure morphism. For a purely inseparable extension the point above a given point
is unique; the local-ring conditions are therefore stated invariantly for every point mapping to
it, without making a noncanonical choice.

## References

* [Stacks Project, Tag 020I](https://stacks.math.columbia.edu/tag/020I)
* [Stacks Project, Tag 035V](https://stacks.math.columbia.edu/tag/035V)
* [Stacks Project, Tag 035W](https://stacks.math.columbia.edu/tag/035W)
-/

@[expose] public section

open CategoryTheory Limits CommRingCat

namespace AlgebraicGeometry

open scoped TensorProduct

universe u

/-- A scheme `X` over a field `k` is geometrically reduced at `x` if, after every field
extension of `k`, every point above `x` has a reduced local ring.

This is the condition of part (1) of [Stacks, Tag 035V] at a fixed point; the tag itself is
carried by `AlgebraicGeometry.IsGeometricallyReducedOver`, which asks for it at every point
of `X`. -/
@[ega "IV 4.6.12"]
public abbrev IsGeometricallyReducedAt {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) : Prop :=
  ∀ (k' : Type u) [Field k'] [Algebra k k'],
    let g : Spec (.of k') ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k k'))
    ∀ x' : (pullback f g : Scheme),
      pullback.fst f g x' = x →
        _root_.IsReduced ((pullback f g).presheaf.stalk x')

/-- **[Stacks, Tag 035V].** Let `k` be a field and let `X` be a scheme over `k`, given by its
structure morphism `f : X ⟶ Spec k`.

1. `X` is *geometrically reduced at* a point `x ∈ X` if for any field extension `k'/k` and any
   point `x'` of `X_{k'}` lying over `x` the local ring `𝒪_{X_{k'}, x'}` is reduced. That
   pointwise condition is `AlgebraicGeometry.IsGeometricallyReducedAt f x`, the body of this
   definition under its quantifier: the base change `X_{k'}` is the pullback of `f` along
   `Spec k' ⟶ Spec k`, and `x'` lies over `x` when the first projection sends it to `x`.
2. `X` is *geometrically reduced over `k`* if it is geometrically reduced at every point of
   `X`, which is exactly what this definition says.

Mathlib's `AlgebraicGeometry.GeometricallyReduced` is the notion of part (2) for an arbitrary
base, defined by reducedness of every field-valued base change rather than pointwise; over a
field the two agree by
`AlgebraicGeometry.geometricallyReduced_iff_forall_isGeometricallyReducedAt`, so the results
stated for it — such as `AlgebraicGeometry.geometricallyReduced_of_isReduced` over a perfect
field — apply to this predicate as well. -/
@[stacks 035V]
public abbrev IsGeometricallyReducedOver {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Prop :=
  ∀ x : X, IsGeometricallyReducedAt f x

/-- A scheme over a field is geometrically reduced exactly when it is geometrically reduced at
every point.

The right-hand side is `AlgebraicGeometry.IsGeometricallyReducedOver f`, which carries
[Stacks, Tag 035V]; this identifies it with Mathlib's predicate
`AlgebraicGeometry.GeometricallyReduced`, the notion of the tag's part (2) for an arbitrary
base. -/
public theorem geometricallyReduced_iff_forall_isGeometricallyReducedAt
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) :
    GeometricallyReduced f ↔ ∀ x : X, IsGeometricallyReducedAt f x := by
  rw [geometricallyReduced_iff, geometrically_iff_of_commRing_of_isClosedUnderIsomorphisms]
  exact ⟨fun h x K _ _ x' _ ↦ @AlgebraicGeometry.isReduced_stalk_of_isReduced _ (h K) x',
    fun h K _ _ ↦ @AlgebraicGeometry.isReduced_of_isReduced_stalk _ fun x' ↦
      h ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))) x') K x' rfl⟩

/-- A localization detects reducedness if the original ring is radical over a ring on which
the localization map reflects units. -/
private lemma isReduced_of_localization_of_exists_pow
    {A T C : Type*} [CommRing A] [CommRing T] [CommRing C]
    (i : A →+* T) (φ : T →+* C) [IsLocalHom (φ.comp i)]
    (hpow : ∀ t : T, ∃ n > 0, t ^ n ∈ i.range)
    (hlocal : let := φ.toAlgebra; ∃ M : Submonoid T, IsLocalization M C)
    [_root_.IsReduced C] : _root_.IsReduced T := by
  let algebraTC := φ.toAlgebra
  obtain ⟨M, hM⟩ := hlocal
  have hunit : M ≤ IsUnit.submonoid T := by
    intro t ht
    obtain ⟨n, hn, a, ha⟩ := hpow t
    have hu : IsUnit (φ (i a)) := by
      rw [ha, map_pow]
      exact (IsLocalization.map_units C (⟨t, ht⟩ : M)).pow n
    exact (isUnit_pow_iff hn.ne').mp (ha ▸ i.isUnit_map ((isUnit_map_iff (φ.comp i) a).mp hu))
  exact isReduced_of_injective φ (IsLocalization.atUnits T M (S := C) hunit).injective

/-- Comparison of reducedness of a stalk after base change with reducedness of the tensor product
of the field extension with the original local ring: the first part holds for any extension, the
second for purely inseparable ones. -/
private lemma isReduced_stalk_iff_aux
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k))
    (t : (pullback f (Spec.map (ofHom (algebraMap k K))) : Scheme)) :
    let x := pullback.fst f (Spec.map (ofHom (algebraMap k K))) t
    let : Algebra k (X.presheaf.stalk x) :=
      let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
        StructureSheaf.stalkAlgebra k (f.base x)
      ((f.stalkMap x).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
    (_root_.IsReduced (K ⊗[k] X.presheaf.stalk x) →
      _root_.IsReduced ((pullback f (Spec.map (ofHom (algebraMap k K)))).presheaf.stalk t)) ∧
    (IsPurelyInseparable k K →
      _root_.IsReduced ((pullback f (Spec.map (ofHom (algebraMap k K)))).presheaf.stalk t) →
      _root_.IsReduced (K ⊗[k] X.presheaf.stalk x)) := by
  intro _ _
  let g := Spec.map (ofHom (algebraMap k K))
  let pX := pullback.fst f g
  let pY := pullback.snd f g
  let x := pX t
  let y : PrimeSpectrum K := pY t
  let h : f x = g y := congrArg (fun j : pullback f g ⟶ Spec (.of k) => j t) pullback.condition
  let z : PrimeSpectrum k := f x
  let R := (Spec (.of k)).presheaf.stalk (f x)
  let A := X.presheaf.stalk x
  let B := (Spec (.of K)).presheaf.stalk y
  let algebraKR : Algebra k R := StructureSheaf.stalkAlgebra k (f x)
  let algebraRA : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let algebraKA : Algebra k A := ((f.stalkMap x).hom.comp (algebraMap k R)).toAlgebra
  let algebraKB : Algebra K B := StructureSheaf.stalkAlgebra K y
  let algebraBaseB : Algebra k B := ((algebraMap K B).comp (algebraMap k K)).toAlgebra
  let algebraRB : Algebra R B :=
    ((eqToHom (congrArg (Spec (.of k)).presheaf.stalk h)) ≫ g.stalkMap y).hom.toAlgebra
  have towerKRA : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq' rfl
  have towerKKB : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
  have towerKRB : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq'
    (stalkMap_spec_comp_algebraMap y (f x) h).symm
  have locR : IsLocalization.AtPrime R z.asIdeal := by
    change IsLocalization.AtPrime ((structurePresheafInCommRingCat k).stalk z) z.asIdeal
    infer_instance
  have locB : IsLocalization.AtPrime B y.asIdeal := by
    change IsLocalization.AtPrime ((structurePresheafInCommRingCat K).stalk y) y.asIdeal
    infer_instance
  have hr : Function.Bijective (algebraMap k R) :=
    Field.localization_map_bijective (M := z.asIdeal.primeCompl) (by simp)
  have hb : Function.Bijective (algebraMap K B) :=
    Field.localization_map_bijective (M := y.asIdeal.primeCompl) (by simp)
  let eB : K ≃ₐ[k] B := AlgEquiv.ofBijective (IsScalarTower.toAlgHom k K B) hb
  have compatible : TensorProduct.CompatibleSMul k R A B :=
    TensorProduct.CompatibleSMul.of_algebraMap_surjective A B hr.surjective
  let e : A ⊗[k] K ≃ₐ[A] A ⊗[R] B :=
    (Algebra.TensorProduct.congr (AlgEquiv.refl : A ≃ₐ[A] A) eB).trans
      (Algebra.TensorProduct.equivOfCompatibleSMul k R A A B).symm
  have haux := BaseChangeStalk.pullback_stalk_isLocalization f g t
  change ∃ φ : A ⊗[R] B →+* (pullback f g).presheaf.stalk t, _ ∧ _ ∧
    let : Algebra (A ⊗[R] B) ((pullback f g).presheaf.stalk t) := φ.toAlgebra
    ∃ M : Submonoid (A ⊗[R] B), IsLocalization M ((pullback f g).presheaf.stalk t) at haux
  obtain ⟨φ, hleft, -, hlocal⟩ := haux
  refine ⟨fun hred ↦ ?_, fun hinsep hC ↦ ?_⟩
  · have : _root_.IsReduced (A ⊗[k] K) := isReduced_of_injective
      (Algebra.TensorProduct.comm k K A).symm.toRingHom
      (Algebra.TensorProduct.comm k K A).symm.injective
    have hring : _root_.IsReduced (A ⊗[R] B) :=
      isReduced_of_injective e.symm.toRingHom e.symm.injective
    let : Algebra (A ⊗[R] B) ((pullback f g).presheaf.stalk t) := φ.toAlgebra
    obtain ⟨M, hM⟩ := hlocal
    let : IsLocalization M ((pullback f g).presheaf.stalk t) := hM
    exact isReduced_localizationPreserves M ((pullback f g).presheaf.stalk t) hring
  · have hleft' : φ.comp (algebraMap A (A ⊗[R] B)) = (pX.stalkMap t).hom := hleft
    have : IsLocalHom (φ.comp (algebraMap A (A ⊗[R] B))) := by
      rw [hleft']
      infer_instance
    have hpow : ∀ s : A ⊗[R] B, ∃ n > 0, s ^ n ∈ (algebraMap A (A ⊗[R] B)).range := by
      intro s
      obtain ⟨v, rfl⟩ := e.surjective s
      obtain ⟨n, hn, a, ha⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct v
      refine ⟨n, hn, a, ?_⟩
      rw [← map_pow, ← ha, e.commutes]
    have : _root_.IsReduced (A ⊗[R] B) :=
      isReduced_of_localization_of_exists_pow (algebraMap A (A ⊗[R] B)) φ hpow hlocal
    exact isReduced_of_injective
      (e.toRingHom.comp (Algebra.TensorProduct.comm k K A).toRingHom)
      (e.injective.comp (Algebra.TensorProduct.comm k K A).injective)

/-- Reducedness of every stalk above a point after a purely inseparable base change implies
reducedness of the tensor product with the local ring at that point. -/
public lemma isReduced_tensorProduct_of_forall_isReduced_stalk
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (hred : ∀ t : (pullback f (Spec.map (ofHom (algebraMap k K))) : Scheme),
      pullback.fst f (Spec.map (ofHom (algebraMap k K))) t = x →
      _root_.IsReduced ((pullback f (Spec.map (ofHom (algebraMap k K)))).presheaf.stalk t)) :
    let : Algebra k (X.presheaf.stalk x) :=
      let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
        StructureSheaf.stalkAlgebra k (f.base x)
      ((f.stalkMap x).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
    _root_.IsReduced (K ⊗[k] X.presheaf.stalk x) := by
  obtain ⟨t, rfl⟩ :=
    (pullback.fst f (Spec.map (ofHom (algebraMap k K)))).surjective x
  have := hred t rfl
  exact (isReduced_stalk_iff_aux f t).2 inferInstance this


/-- A scheme over a field is geometrically reduced at a point if and only if its local ring at
that point is geometrically reduced over the field. -/
@[stacks 035W]
public lemma isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk
    {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X) :
    IsGeometricallyReducedAt f x ↔
      let : Algebra k (X.presheaf.stalk x) :=
        let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
          StructureSheaf.stalkAlgebra k (f.base x)
        ((f.stalkMap x).hom.comp
          (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
      Algebra.IsGeometricallyReduced k (X.presheaf.stalk x) := by
  let A := X.presheaf.stalk x
  let : Algebra k A :=
    let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
      StructureSheaf.stalkAlgebra k (f.base x)
    ((f.stalkMap x).hom.comp
      (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
  have hring := Algebra.isGeometricallyReduced_tfae k (ringExpChar k) A
    (perfectClosure k (AlgebraicClosure k)) (AlgebraicClosure k)
  constructor
  · intro hpoint
    apply (hring.out 1 6).mp
    intro K _ _ _ _
    exact isReduced_tensorProduct_of_forall_isReduced_stalk f x (hpoint K)
  · intro hgeom
    change ∀ (K : Type u) [Field K] [Algebra k K]
      (t : (pullback f (Spec.map (ofHom (algebraMap k K))) : Scheme)),
      pullback.fst f (Spec.map (ofHom (algebraMap k K))) t = x →
        _root_.IsReduced ((pullback f (Spec.map (ofHom (algebraMap k K)))).presheaf.stalk t)
    have hAll : ∀ (K : Type u) [Field K] [Algebra k K], _root_.IsReduced (K ⊗[k] A) :=
      (hring.out 6 5).mp hgeom
    intro K _ _ t ht
    subst ht
    exact (isReduced_stalk_iff_aux f t).1 (hAll K)

/-- A reduced local ring of a scheme over a perfect field is geometrically reduced at the
corresponding point. -/
@[stacks 020I "part (1)", ega "IV 4.6.11" "partial", ega "IV 4.6.12" "special case"]
public theorem isGeometricallyReducedAt_of_isReduced
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) [_root_.IsReduced (X.presheaf.stalk x)] :
    IsGeometricallyReducedAt f x := by
  let : Algebra k (X.presheaf.stalk x) :=
    let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
      StructureSheaf.stalkAlgebra k (f.base x)
    ((f.stalkMap x).hom.comp (algebraMap k _)).toAlgebra
  rw [isGeometricallyReducedAt_iff_isGeometricallyReduced_stalk,
    Algebra.isGeometricallyReduced_field_iff]
  exact Algebra.isReduced_tensorProduct_of_isSeparableExtension_or_isSeparablyGenerated
    (.inl ⟨fun K' _ =>
      let ⟨s, hs, hsep⟩ := exists_isTranscendenceBasis_and_isSeparable_of_perfectField k K'
      ⟨(s : Set K'), hs, hsep⟩⟩)

/-- A reduced scheme over a perfect field is geometrically reduced over that field. -/
@[stacks 020I "part (2)",
  instance,
  ega "IV 4.6.1" "(c) ⇒ (b), special case",
  ega "IV 4.6.12" "(b) ⇒ (a), special case"]
public theorem geometricallyReduced_of_isReduced
    {k : Type u} [Field k] [PerfectField k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) [IsReduced X] :
    GeometricallyReduced f :=
  (geometricallyReduced_iff_forall_isGeometricallyReducedAt f).mpr
    (fun x => isGeometricallyReducedAt_of_isReduced f x)

end AlgebraicGeometry
