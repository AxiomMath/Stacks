module

public import Mathlib.AlgebraicGeometry.Noetherian
public import Mathlib.Data.List.TFAE
public import Mathlib.FieldTheory.PurelyInseparable.Basic
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Perfect.BaseChangeStalk
public import StacksFrontier.AlgebraicGeometry.Variety.Geometrically.PullbackStalk
public import StacksFrontier.RingTheory.GeometricallyRegular.Defs
public import StacksFrontier.RingTheory.GeometricallyRegular.FieldExtension
public import StacksFrontier.RingTheory.GeometricallyRegular.PurelyInseparableCriterion
public import StacksFrontier.RingTheory.RegularRing.Defs

/-!
# Geometrically regular schemes over a field

For a scheme over a field, geometric regularity at a point requires regularity of the local
rings at all points above it after every finitely generated extension of the base field. The
scheme is geometrically regular when this holds at every point. For a locally Noetherian scheme
this can be tested after finite purely inseparable extensions, or on the local ring at the
point.

## Main definitions

* `AlgebraicGeometry.IsGeometricallyRegularAt` is geometric regularity at a point.
* `AlgebraicGeometry.IsGeometricallyRegular` is geometric regularity at every point.

## Main results

* `AlgebraicGeometry.geometricallyRegularAt_tfae` gives the three equivalent characterizations
  of geometric regularity at a point.

## Implementation notes

The base change of `f : X ⟶ Spec k` to a field extension `K/k` is the pullback of `f` along
`Spec K ⟶ Spec k`; lying over `x` means equality after the first pullback projection. A
finitely generated field extension is expressed by `Algebra.EssFiniteType`. The predicates are
stated without a locally Noetherian typeclass hypothesis, since their defining conditions make
sense for every scheme; the source and its immediate applications impose that hypothesis.

The three entries of `AlgebraicGeometry.geometricallyRegularAt_tfae` are respectively items
(1), (2) and (3) of Tag 038U. In item (3), the `k`-algebra structure on the local ring is the
composite of the canonical map from `k` to the stalk of `Spec k` and the stalk map of the
structure morphism.

## References

* [Stacks Project, Tag 038T](https://stacks.math.columbia.edu/tag/038T)
* [Stacks Project, Tag 038U](https://stacks.math.columbia.edu/tag/038U)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

open scoped TensorProduct

universe u

/-- **Stacks Project, Tag 038T, part (1).** A scheme `X` over a field `k` is geometrically
regular at `x` if, after every finitely generated field extension `K/k`, every point above `x`
has a regular local ring. -/
@[stacks 038T "part (1)", ega "IV 6.7.6" "geom. regular at x", ega "IV 6.7.8"]
public abbrev IsGeometricallyRegularAt {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) (x : X) : Prop :=
  ∀ (K : Type u) [Field K] [Algebra k K] [Algebra.EssFiniteType k K],
    let g : Spec (.of K) ⟶ Spec (.of k) :=
      Spec.map (CommRingCat.ofHom (algebraMap k K))
    ∀ (x' : (pullback f g : Scheme.{u})), pullback.fst f g x' = x →
      IsRegularLocalRing ((pullback f g : Scheme.{u}).presheaf.stalk x')

/- `AlgebraicGeometry.IsGeometricallyReducedAt` has the same signature and a weaker conclusion
on a wider range of extensions: it asks the stalks to be reduced, not regular local, and does so
after *every* field extension of `k`, not only the finitely generated ones. -/

/-- **Stacks Project, Tag 038T, part (2).** A scheme over a field is geometrically regular if it
is geometrically regular at every point. -/
@[stacks 038T "part (2)", ega "IV 6.7.6" "geometrically regular"]
public abbrev IsGeometricallyRegular {k : Type u} [Field k] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of k)) : Prop :=
  ∀ x : X, IsGeometricallyRegularAt f x

/- `AlgebraicGeometry.IsLocalCompleteIntersectionOverField` has the same signature and the
unrelated body `Syntomic f`: `f` is presented on affine opens by syntomic ring maps, a condition
on the local presentations of `f` and not on its stalks after a base field extension. -/

/-- If a ring map reflects units after restriction along a radical subring, it reflects them. -/
private theorem isLocalHom_of_comp_of_exists_pow
    {A T C : Type*} [CommSemiring A] [CommSemiring T] [CommSemiring C]
    (i : A →+* T) (φ : T →+* C)
    (hcomp : IsLocalHom (φ.comp i))
    (hpow : ∀ t : T, ∃ n > 0, ∃ a : A, t ^ n = i a) : IsLocalHom φ := by
  refine ⟨fun t hunit => ?_⟩
  obtain ⟨n, hn, a, ha⟩ := hpow t
  apply (isUnit_pow_iff hn.ne').mp
  rw [ha]
  exact i.isUnit_map ((isUnit_map_iff (φ.comp i) a).mp (by
    show IsUnit (φ (i a))
    rw [← ha, map_pow]
    exact hunit.pow n))

/-- The stalk of a base change along a field extension is a localization of the tensor product
of the stalk of `X` with `K` over the base field. -/
private lemma exists_tensorProduct_equiv_isLocalization_pullbackStalk
    {k K : Type u} [Field k] [Field K] [Algebra k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (t : (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})) :
    let x := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) t
    let : Algebra k (X.presheaf.stalk x) :=
      let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
        StructureSheaf.stalkAlgebra k (f.base x)
      ((f.stalkMap x).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
    ∃ (T : Type u) (_ : CommRing T) (_ : Algebra (X.presheaf.stalk x) T)
      (_ : X.presheaf.stalk x ⊗[k] K ≃ₐ[X.presheaf.stalk x] T)
      (φ : T →+* (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk t)
      (M : Submonoid T),
      φ.comp (algebraMap (X.presheaf.stalk x) T) =
        ((pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).stalkMap t).hom ∧
      @IsLocalization T _ M ((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk t) _
        φ.toAlgebra := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  let pX := pullback.fst f g
  let pY := pullback.snd f g
  let x := pX t
  let y : PrimeSpectrum K := pY t
  have h : f x = g y := congrArg (fun j : pullback f g ⟶ Spec (.of k) => j t)
    pullback.condition
  let R := (Spec (.of k)).presheaf.stalk (f x)
  let A := X.presheaf.stalk x
  let B := (Spec (.of K)).presheaf.stalk y
  let algebraKR : Algebra k R := StructureSheaf.stalkAlgebra k (f x)
  let algebraRA : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let : Algebra R A := algebraRA
  let algebraKA : Algebra k A := ((f.stalkMap x).hom.comp
    (algebraMap k R)).toAlgebra
  let : Algebra k A := algebraKA
  have towerKRA : IsScalarTower k R A := IsScalarTower.of_algebraMap_eq' rfl
  let algebraKB : Algebra K B := StructureSheaf.stalkAlgebra K y
  let algebraBaseB : Algebra k B := ((algebraMap K B).comp (algebraMap k K)).toAlgebra
  have towerKKB : IsScalarTower k K B := IsScalarTower.of_algebraMap_eq' rfl
  let algebraRB : Algebra R B := ((eqToHom
    (congrArg (Spec (.of k)).presheaf.stalk h)) ≫ g.stalkMap y).hom.toAlgebra
  let : Algebra R B := algebraRB
  have towerKRB : IsScalarTower k R B := IsScalarTower.of_algebraMap_eq'
    (stalkMap_spec_comp_algebraMap y (f x) h).symm
  let z : PrimeSpectrum k := f x
  have locR : IsLocalization.AtPrime R z.asIdeal := by
    show IsLocalization.AtPrime ((structurePresheafInCommRingCat k).stalk z) z.asIdeal
    infer_instance
  have locB : IsLocalization.AtPrime B y.asIdeal := by
    show IsLocalization.AtPrime ((structurePresheafInCommRingCat K).stalk y) y.asIdeal
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
  obtain ⟨φ, hleft, -, hlocal⟩ := BaseChangeStalk.pullback_stalk_isLocalization f g t
  change (A ⊗[R] B) →+* (pullback f g : Scheme.{u}).presheaf.stalk t at φ
  obtain ⟨M, hM⟩ := hlocal
  change Submonoid (A ⊗[R] B) at M
  exact ⟨A ⊗[R] B, inferInstance, inferInstance, e, φ, M, hleft, hM⟩

/-- Regularity of the local ring above a point after a purely inseparable base change gives
regularity of the tensor product with the local ring below. -/
private lemma isRegularRing_tensorProduct_of_regularPullbackStalk
    {k K : Type u} [Field k] [Field K] [Algebra k K] [IsPurelyInseparable k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (t : (pullback f
      (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hreg : IsRegularLocalRing
      ((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk t)) :
    let x := pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) t
    let : Algebra k (X.presheaf.stalk x) :=
      let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
        StructureSheaf.stalkAlgebra k (f.base x)
      ((f.stalkMap x).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
    IsRegularRing (K ⊗[k] X.presheaf.stalk x) := by
  intro x _
  have := hreg
  obtain ⟨T, _, _, e, φ, M, hleft, hM⟩ :=
    exists_tensorProduct_equiv_isLocalization_pullbackStalk f t
  have hφlocal : IsLocalHom φ := isLocalHom_of_comp_of_exists_pow (algebraMap _ T) φ
    (by rw [hleft]; infer_instance) fun s => by
    obtain ⟨v, rfl⟩ := e.surjective s
    obtain ⟨n, hn, a, ha⟩ := IsPurelyInseparable.exists_pow_mem_range_tensorProduct v
    exact ⟨n, hn, a, by rw [← map_pow, ← ha, e.commutes]⟩
  let := φ.toAlgebra
  have : IsLocalization M ((pullback f
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk t) := hM
  have hMunit : M ≤ IsUnit.submonoid T := fun m hm =>
    hφlocal.map_nonunit m (IsLocalization.map_units _ ⟨m, hm⟩)
  have : IsLocalRing (X.presheaf.stalk x ⊗[k] K) :=
    _root_.isLocalRing_tensorProduct_of_isPurelyInseparable k _ K
  have : IsLocalRing T := e.toRingEquiv.isLocalRing
  let eC : T ≃ₐ[T] ((pullback f
    (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk t) :=
    IsLocalization.atUnits T M hMunit
  have hT : IsRegularLocalRing T := IsRegularLocalRing.of_ringEquiv eC.symm.toRingEquiv
  have : IsRegularRing T := ((IsLocalRing.isRegularRing_tfae (R := T)).out 1 3).mp hT
  exact IsRegularRing.of_ringEquiv
    ((Algebra.TensorProduct.comm k K _).toRingEquiv.trans e.toRingEquiv).symm

/-- Regularity of the local rings at every point above `x` after a finite purely inseparable
base change gives regularity of the tensor product with the local ring at `x`. -/
private lemma isRegularRing_tensorProduct_of_regularPullbackStalks
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Module.Finite k K]
    [IsPurelyInseparable k K] {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (hreg : ∀ t : (pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}),
      pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) t = x →
      IsRegularLocalRing
        ((pullback f
          (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk t)) :
    let : Algebra k (X.presheaf.stalk x) :=
      let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
        StructureSheaf.stalkAlgebra k (f.base x)
      ((f.stalkMap x).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
    IsRegularRing (K ⊗[k] X.presheaf.stalk x) := by
  obtain ⟨t, rfl⟩ :=
    (pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K)))).surjective x
  exact isRegularRing_tensorProduct_of_regularPullbackStalk f t (hreg t rfl)

/-- Geometric regularity of the local ring at `x` gives regularity of the local ring at any
point above `x` after a finitely generated base change. -/
private lemma isRegularLocalRing_pullbackStalk_of_isGeometricallyRegular
    {k K : Type u} [Field k] [Field K] [Algebra k K] [Algebra.EssFiniteType k K]
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) (x : X)
    (t : (pullback f (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}))
    (hxt : pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) t = x)
    (hgeo : let : Algebra k (X.presheaf.stalk x) :=
      let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
        StructureSheaf.stalkAlgebra k (f.base x)
      ((f.stalkMap x).hom.comp
        (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
      Algebra.IsGeometricallyRegular k (X.presheaf.stalk x)) :
    IsRegularLocalRing
      ((pullback f
        (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk t) := by
  let g := Spec.map (CommRingCat.ofHom (algebraMap k K))
  subst hxt
  let : Algebra k (X.presheaf.stalk (pullback.fst f g t)) :=
    let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base (pullback.fst f g t))) :=
      StructureSheaf.stalkAlgebra k (f.base (pullback.fst f g t))
    ((f.stalkMap (pullback.fst f g t)).hom.comp (algebraMap k _)).toAlgebra
  obtain ⟨T, _, _, e, φ, M, -, hM⟩ :=
    exists_tensorProduct_equiv_isLocalization_pullbackStalk f t
  have : IsRegularRing (K ⊗[k] X.presheaf.stalk (pullback.fst f g t)) :=
    hgeo.isRegularRing_tensorProduct K
  have : IsRegularRing T :=
    IsRegularRing.of_ringEquiv ((Algebra.TensorProduct.comm k K _).toRingEquiv.trans e.toRingEquiv)
  let := φ.toAlgebra
  have : IsLocalization M ((pullback f g : Scheme.{u}).presheaf.stalk t) := hM
  have : IsRegularRing ((pullback f g : Scheme.{u}).presheaf.stalk t) :=
    isRegularRing_of_isLocalization M
  exact IsRegularLocalRing.of_isRegularRing_of_isLocalRing _

/-- For a locally Noetherian scheme over a field, geometric regularity at a point is equivalent
both to regularity at every point above it after every finite purely inseparable field extension,
and to geometric regularity of its local ring over the ground field. -/
@[stacks 038U]
public lemma geometricallyRegularAt_tfae
    (k : Type u) [Field k] (X : Scheme.{u}) (f : X ⟶ Spec (.of k))
    [IsLocallyNoetherian X] (x : X) :
    List.TFAE [
      IsGeometricallyRegularAt f x,
      ∀ (K : Type u) [Field K] [Algebra k K] [Module.Finite k K]
        [IsPurelyInseparable k K],
        ∀ (x' : (pullback f
            (Spec.map (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u})),
          pullback.fst f (Spec.map (CommRingCat.ofHom (algebraMap k K))) x' = x →
            IsRegularLocalRing
              ((pullback f
                (Spec.map
                  (CommRingCat.ofHom (algebraMap k K))) : Scheme.{u}).presheaf.stalk x'),
      let : Algebra k (X.presheaf.stalk x) :=
        let : Algebra k ((Spec (.of k)).presheaf.stalk (f.base x)) :=
          StructureSheaf.stalkAlgebra k (f.base x)
        ((f.stalkMap x).hom.comp
          (algebraMap k ((Spec (.of k)).presheaf.stalk (f.base x)))).toAlgebra
      Algebra.IsGeometricallyRegular k (X.presheaf.stalk x)] := by
  let R := (Spec (.of k)).presheaf.stalk (f.base x)
  let A := X.presheaf.stalk x
  let : Algebra k R := StructureSheaf.stalkAlgebra k (f.base x)
  let : Algebra R A := (f.stalkMap x).hom.toAlgebra
  let : Algebra k A := ((f.stalkMap x).hom.comp (algebraMap k R)).toAlgebra
  tfae_have 1 → 2 := fun h K _ _ _ _ x' hx => h K x' hx
  tfae_have 2 → 3 := by
    intro h
    show Algebra.IsGeometricallyRegular k A
    exact ⟨(Algebra.forall_isRegularRing_tensorProduct_essFiniteType_iff_finite_isPurelyInseparable
      k A).mpr fun K _ _ _ _ => isRegularRing_tensorProduct_of_regularPullbackStalks f x (h K)⟩
  tfae_have 3 → 1 := by
    intro h K _ _ _ _ x' hx
    exact isRegularLocalRing_pullbackStalk_of_isGeometricallyRegular f x x' hx h
  tfae_finish

end AlgebraicGeometry
