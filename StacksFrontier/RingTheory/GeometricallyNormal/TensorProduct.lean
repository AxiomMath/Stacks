module

public import Mathlib.RingTheory.Nilpotent.GeometricallyReduced
public import StacksFrontier.RingTheory.GeometricallyNormal.Localization

import Mathlib.Algebra.Field.Shrink

import Mathlib.RingTheory.Localization.BaseChange
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.FieldTheory.Separable.TFAE
import StacksFrontier.RingTheory.Nagata.Examples
import StacksFrontier.RingTheory.Nagata.FiniteType
import StacksFrontier.RingTheory.Smooth.Field
import StacksFrontier.RingTheory.Smooth.Normal

/-!
# Tensor products with a geometrically normal algebra are normal

Proof of `Algebra.IsGeometricallyNormal.isNormalRing_tensorProduct_of_isNormalRing` (Stacks 06DF):
for a field `k`, a geometrically normal `k`-algebra `A` and a normal `k`-algebra `B`, the ring
`A ⊗[k] B` is normal.

The argument is the source's. Normality is local, and localizations of `A` stay geometrically
normal (Lemma 06DE), so `A` and `B` may be assumed to be normal domains. A normal domain `B` over
`k` is the directed union of its finitely generated normal `k`-subalgebras — the integral closure
of a finitely generated subalgebra `C` in its fraction field is finite over `C`, fields being
Nagata — and the maps `A ⊗[k] B' → A ⊗[k] B` are injective, so by Lemma 037D `B` may be assumed of
finite type over `k`. Then `A ⊗[k] B` embeds into `K ⊗[k] B` and `A ⊗[k] L`, where `K` and `L` are
the fraction fields: `K ⊗[k] B` is normal because `K/k` is separable, so `K` is a localization of
a smooth `k`-algebra and normality ascends along smooth maps (Lemma 033C); and `A ⊗[k] L` is normal
by geometric normality of `A`. An element of `K ⊗[k] L` lying in both subrings lies in `A ⊗[k] B`
(linear algebra over `k`), which gives that `A ⊗[k] B` is integrally closed. It is reduced with
finitely many minimal primes, since `K ⊗[k] B` is a reduced Noetherian localization of it into
which it embeds, and Lemma 030C concludes.

## Main results

* `Algebra.IsGeometricallyNormal.isNormalRing_tensorProduct_of_field`: the base change of a
  geometrically normal algebra to a field extension in any universe is normal.
* `Algebra.IsGeometricallyNormal.isNormalRing_tensorProduct_of_isNormalRing`: Stacks 06DF.

## Implementation notes

Geometric normality is `Algebra.IsGeometricallyNormal` (Definition 0380), which quantifies over
field extensions in the universe of `k`; the extension to all universes goes through the finitely
generated subextensions, each of which is small over `k`. Normality is the library's `IsNormalRing`
(Definition 00GV); neither algebra is assumed to be a domain or Noetherian, and `k`, `A`, `B` live
in independent universes.

## References

* [Stacks Project, Tag 06DF](https://stacks.math.columbia.edu/tag/06DF)
-/

@[expose] public section

open scoped TensorProduct

universe u v w

/-- The image of `f ⊗ g` is the intersection of the images of `f ⊗ id` and `id ⊗ g`, when `f` is
an injective linear map of vector spaces. -/
@[ega "0 6.1.4" "special case", sga "3 VIB 11.8" "special case"]
theorem TensorProduct.range_map_eq_inf_of_injective {K U V W X : Type*} [Field K]
    [AddCommGroup U] [Module K U] [AddCommGroup V] [Module K V] [AddCommGroup W] [Module K W]
    [AddCommGroup X] [Module K X] (f : U →ₗ[K] V) (g : W →ₗ[K] X) (hf : Function.Injective f) :
    LinearMap.range (TensorProduct.map f g) =
      LinearMap.range (TensorProduct.map f (LinearMap.id : X →ₗ[K] X)) ⊓
      LinearMap.range (TensorProduct.map (LinearMap.id : V →ₗ[K] V) g) := by
  obtain ⟨r, hr⟩ := f.exists_leftInverse_of_injective (LinearMap.ker_eq_bot.mpr hf)
  ext z
  constructor
  · rintro ⟨x, rfl⟩
    refine ⟨⟨TensorProduct.map LinearMap.id g x, ?_⟩, ⟨TensorProduct.map f LinearMap.id x, ?_⟩⟩ <;>
      rw [← LinearMap.comp_apply, ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp]
  · rintro ⟨⟨x, hx⟩, ⟨y, hy⟩⟩
    refine ⟨TensorProduct.map r LinearMap.id y, ?_⟩
    have hcomm : (TensorProduct.map f g).comp (TensorProduct.map r (LinearMap.id : W →ₗ[K] W)) =
        (TensorProduct.map (f.comp r) LinearMap.id).comp
          (TensorProduct.map (LinearMap.id : V →ₗ[K] V) g) := by
      rw [← TensorProduct.map_comp, ← TensorProduct.map_comp, LinearMap.comp_id, LinearMap.id_comp,
        LinearMap.comp_id]
    rw [← LinearMap.comp_apply, hcomm, LinearMap.comp_apply, hy, ← hx, ← LinearMap.comp_apply,
      ← TensorProduct.map_comp, LinearMap.comp_assoc, hr, LinearMap.comp_id, LinearMap.id_comp]

/-- The image of `f ⊗ g` is the intersection of the images of `f ⊗ id` and `id ⊗ g`, when `f` is
an injective map of algebras over a field. -/
@[ega "0 6.1.4" "special case"]
theorem Algebra.TensorProduct.range_map_eq_inf_of_injective {k A B C D : Type*} [Field k]
    [CommRing A] [CommRing B] [CommRing C] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k C]
    [Algebra k D] (f : A →ₐ[k] B) (g : C →ₐ[k] D) (hf : Function.Injective f) :
    (Algebra.TensorProduct.map f g).range =
      (Algebra.TensorProduct.map f (AlgHom.id k D)).range ⊓
      (Algebra.TensorProduct.map (AlgHom.id k B) g).range :=
  Subalgebra.toSubmodule_injective <|
    _root_.TensorProduct.range_map_eq_inf_of_injective f.toLinearMap g.toLinearMap hf

/-- When `f` is injective, an element in the images of both `id ⊗ g` and `f ⊗ id` lies in the image
of `f ⊗ g`. -/
theorem Algebra.TensorProduct.exists_map_eq_of_map_eq_of_injective {k A B C D : Type*} [Field k]
    [CommRing A] [CommRing B] [CommRing C] [CommRing D] [Algebra k A] [Algebra k B] [Algebra k C]
    [Algebra k D] (f : A →ₐ[k] B) (g : C →ₐ[k] D) (hf : Function.Injective f) (s : B ⊗[k] C)
    (t : A ⊗[k] D)
    (hst : Algebra.TensorProduct.map (AlgHom.id k B) g s =
      Algebra.TensorProduct.map f (AlgHom.id k D) t) :
    ∃ r, Algebra.TensorProduct.map f g r = Algebra.TensorProduct.map (AlgHom.id k B) g s := by
  obtain ⟨r, hr⟩ : Algebra.TensorProduct.map f (AlgHom.id k D) t ∈
      (Algebra.TensorProduct.map f g).range := by
    rw [Algebra.TensorProduct.range_map_eq_inf_of_injective f g hf]
    exact Algebra.mem_inf.mpr ⟨AlgHom.mem_range_self _ t, (AlgHom.mem_range _).mpr ⟨s, hst⟩⟩
  exact ⟨r, hr.trans hst.symm⟩

/-- A field extension which is essentially of finite type over `k` is small over `k`. -/
theorem Algebra.EssFiniteType.small_of_field (k : Type u) (K : Type v) [Field k] [Field K]
    [Algebra k K] [Algebra.EssFiniteType k K] : Small.{u} K := by
  have : Small.{u} (Algebra.EssFiniteType.subalgebra k K) := Algebra.FiniteType.small (R := k)
  exact small_of_surjective (IsLocalization.mk'_surjective (S := K)
    (Algebra.EssFiniteType.submonoid k K))

namespace Algebra.IsGeometricallyNormal

variable {k : Type u} {A : Type v} [Field k] [CommRing A] [Algebra k A]

/-- A geometrically normal algebra is geometrically reduced, a normal ring being reduced. -/
theorem isGeometricallyReduced [Algebra.IsGeometricallyNormal k A] :
    Algebra.IsGeometricallyReduced k A :=
  (Algebra.isGeometricallyReduced_field_iff k A).mpr
    (isNormalRing_tensorProduct (A := A) (AlgebraicClosure k)).isReduced

/-- The base change of a geometrically normal algebra to a field extension of `k` in an arbitrary
universe is normal: it is the directed union of the base changes to the finitely generated
subextensions, each of which is isomorphic to a field in the universe of `k`. -/
theorem isNormalRing_tensorProduct_of_field [Algebra.IsGeometricallyNormal k A] (L : Type w)
    [Field L] [Algebra k L] : IsNormalRing (L ⊗[k] A) := by
  refine isNormalRing_tensorProduct_of_forall_fg_intermediateField fun F hF ↦ ?_
  have : Algebra.EssFiniteType k F := IntermediateField.essFiniteType_iff.mpr hF
  have : Small.{u} F := Algebra.EssFiniteType.small_of_field k F
  exact IsNormalRing.congr (Algebra.TensorProduct.congr (Shrink.algEquiv k F) .refl).toRingEquiv
    (isNormalRing_tensorProduct (A := A) (Shrink.{u} F))

end Algebra.IsGeometricallyNormal

namespace Algebra.IsGeometricallyNormal.TensorProductOfNormal

/-- The base change of a normal ring to a geometrically reduced field extension is normal: over a
finitely generated subextension `F/k`, separable by Lemma 030W, `F` is the fraction field of a
smooth `k`-algebra (Lemma 0CBM's source, `Algebra.IsSeparableExtension.tfae_exists_smooth`). -/
@[ega "0 23.1.7" "partial", ega "IV 21.14.4" "special case", ega "IV 6.7.6" "partial"]
private theorem isNormalRing_tensorProduct_of_isGeometricallyReduced (k K B : Type*) [Field k]
    [Field K] [CommRing B] [Algebra k K] [Algebra k B] [Algebra.IsGeometricallyReduced k K]
    (hB : IsNormalRing B) : IsNormalRing (K ⊗[k] B) := by
  refine isNormalRing_tensorProduct_of_forall_fg_intermediateField fun F hF ↦ ?_
  have : Algebra.EssFiniteType k F := IntermediateField.essFiniteType_iff.mpr hF
  have : Algebra.IsGeometricallyReduced k F :=
    Algebra.IsGeometricallyReduced.of_injective F.val F.val.injective
  obtain ⟨p, hp⟩ := ExpChar.exists k
  have : Algebra.IsSeparableExtension k F :=
    ((Algebra.isSeparableExtension_tfae k F p).out 1 4).mpr ‹_›
  obtain ⟨R, _, _⟩ := ((Algebra.IsSeparableExtension.tfae_exists_smooth k F).out 1 2).mp ‹_›
  exact IsNormalRing.congr (Algebra.TensorProduct.comm k B F).toRingEquiv
    (Algebra.isNormalRing_tensorProduct_of_smooth_of_isLocalization k B R F hB
      (nonZeroDivisors R))

/-- Normality of `A ⊗[k] B` is local on `A`. -/
private theorem isNormalRing_tensorProduct_of_localizations {k A B : Type*} [CommRing k]
    [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    (h : ∀ (p : Ideal A) [p.IsPrime], IsNormalRing (Localization.AtPrime p ⊗[k] B)) :
    IsNormalRing (A ⊗[k] B) :=
  IsNormalRing.of_localization_atPrime_tensorProduct fun p _ ↦
    IsNormalRing.congr (Algebra.TensorProduct.cancelBaseChange k A (Localization.AtPrime p)
      (Localization.AtPrime p) B).symm.toRingEquiv (h p)

/-- A localization `S` of `R` at nonzerodivisors of a ring with fraction field `Q` is a subring of
`Q` which is again a ring with fraction field `Q`. -/
private theorem exists_algebra_isFractionRing_of_isLocalization {R : Type*} (S Q : Type*)
    [CommRing R] [CommRing S] [CommRing Q] [Algebra R S] [Algebra R Q] [IsFractionRing R Q]
    (M : Submonoid R) [IsLocalization M S] (hM : M ≤ nonZeroDivisors R) :
    ∃ _ : Algebra S Q, IsScalarTower R S Q ∧ IsFractionRing S Q := by
  let _ := IsLocalization.localizationAlgebraOfSubmonoidLe S Q M _ hM
  have : IsScalarTower R S Q := IsLocalization.localization_isScalarTower_of_submonoid_le S Q M _ hM
  exact ⟨‹_›, ‹_›, IsFractionRing.isFractionRing_of_isLocalization M S Q hM⟩

/-- A ring `R` is integrally closed when it has two localizations `S = M⁻¹R`, `T = N⁻¹R` at
nonzerodivisors which are integrally closed and whose "intersection" inside the common localization
`U = N⁻¹S` is `R`. -/
private theorem isIntegrallyClosed_of_localization_intersection {R S T U : Type*} [CommRing R]
    [CommRing S] [CommRing T] [CommRing U] [Algebra R S] [Algebra R T] [Algebra R U] [Algebra S U]
    [Algebra T U] [IsScalarTower R S U] [IsScalarTower R T U] (M N : Submonoid R)
    [IsLocalization M S] [IsLocalization N T] [IsLocalization (N.map (algebraMap R S)) U]
    (hM : M ≤ nonZeroDivisors R) (hN : N ≤ nonZeroDivisors R) [IsIntegrallyClosed S]
    [IsIntegrallyClosed T]
    (hinter : ∀ s : S, ∀ t : T, algebraMap S U s = algebraMap T U t →
      ∃ r : R, algebraMap R U r = algebraMap S U s) : IsIntegrallyClosed R := by
  let Q := FractionRing R
  obtain ⟨_, _, _⟩ := exists_algebra_isFractionRing_of_isLocalization S Q M hM
  obtain ⟨_, _, _⟩ := exists_algebra_isFractionRing_of_isLocalization T Q N hN
  have hP : N.map (algebraMap R S) ≤ nonZeroDivisors S := by
    rintro _ ⟨r, hr, rfl⟩
    exact IsLocalization.map_nonZeroDivisors_le M S (Submonoid.mem_map_of_mem _ (hN hr))
  obtain ⟨_, _, _⟩ := exists_algebra_isFractionRing_of_isLocalization U Q
    (N.map (algebraMap R S)) hP
  have : IsScalarTower R U Q := IsScalarTower.to₁₃₄ R S U Q
  have : IsScalarTower T U Q := by
    refine IsScalarTower.of_algebraMap_eq' (IsLocalization.ringHom_ext N ?_)
    ext r
    simp only [RingHom.comp_apply]
    rw [← IsScalarTower.algebraMap_apply R T U, ← IsScalarTower.algebraMap_apply R U Q,
      ← IsScalarTower.algebraMap_apply R T Q]
  refine (isIntegrallyClosed_iff Q).mpr fun {x} hx ↦ ?_
  obtain ⟨s, hs⟩ := (isIntegrallyClosed_iff Q).mp ‹IsIntegrallyClosed S› hx.tower_top
  obtain ⟨t, ht⟩ := (isIntegrallyClosed_iff Q).mp ‹IsIntegrallyClosed T› hx.tower_top
  have heq : algebraMap S U s = algebraMap T U t := IsFractionRing.injective U Q <| by
    simpa only [← IsScalarTower.algebraMap_apply] using hs.trans ht.symm
  obtain ⟨r, hr⟩ := hinter s t heq
  exact ⟨r, by simpa only [← IsScalarTower.algebraMap_apply, hs] using congrArg (algebraMap U Q) hr⟩

/-- A flat algebra carries nonzerodivisors of the base to nonzerodivisors. -/
private theorem algebraMapSubmonoid_le_nonZeroDivisors_of_flat (R S : Type*) [CommRing R]
    [CommRing S] [Algebra R S] [Module.Flat R S] :
    Algebra.algebraMapSubmonoid S (nonZeroDivisors R) ≤ nonZeroDivisors S := by
  rintro _ ⟨r, hr, rfl⟩
  refine mem_nonZeroDivisors_iff_right.mpr fun x hx ↦ ?_
  apply Module.Flat.isSMulRegular_of_nonZeroDivisors (M := S) hr
  simpa only [Algebra.smul_def, mul_zero, zero_mul, mul_comm] using hx

section FractionBaseChange

variable {k A B : Type*} [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]

/-- The image of the nonzerodivisors of `B` in `A ⊗[k] B` consists of nonzerodivisors. -/
private theorem map_includeRight_nonZeroDivisors_le :
    (nonZeroDivisors B).map (Algebra.TensorProduct.includeRight (R := k) (A := A)) ≤
      nonZeroDivisors (A ⊗[k] B) := by
  let _ : Algebra B (A ⊗[k] B) := Algebra.TensorProduct.rightAlgebra
  have : Module.Flat B (A ⊗[k] B) := Module.Flat.of_linearEquiv
    (Algebra.TensorProduct.commRight k B A).symm.toLinearEquiv
  rintro _ ⟨b, hb, rfl⟩
  have h := algebraMapSubmonoid_le_nonZeroDivisors_of_flat B (A ⊗[k] B)
    (Submonoid.mem_map_of_mem (algebraMap B (A ⊗[k] B)) hb)
  rwa [Algebra.TensorProduct.algebraMap_eq_includeRight] at h

/-- The map `A ⊗[k] B → Frac(A) ⊗[k] B`. -/
private noncomputable abbrev mapLeft : A ⊗[k] B →ₐ[k] FractionRing A ⊗[k] B :=
  Algebra.TensorProduct.map (IsScalarTower.toAlgHom k A (FractionRing A)) (AlgHom.id k B)

/-- `Frac(A) ⊗[k] B` is the localization of `A ⊗[k] B` at the nonzerodivisors of `A`. -/
private theorem isLocalization_mapLeft :
    let _ := (mapLeft (k := k) (A := A) (B := B)).toAlgebra
    IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] B) (nonZeroDivisors A))
      (FractionRing A ⊗[k] B) := by
  let _ := (mapLeft (k := k) (A := A) (B := B)).toAlgebra
  have : IsScalarTower A (A ⊗[k] B) (FractionRing A ⊗[k] B) :=
    IsScalarTower.of_algebraMap_eq fun a ↦ by
      rw [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.algebraMap_apply]
      simp
  exact IsLocalization.tensorProduct_tensorProduct k B (nonZeroDivisors A) (FractionRing A)
    (by ext b; simp [RingHom.algebraMap_toAlgebra])

/-- The map `A ⊗[k] B → Frac(A) ⊗[k] B` is injective. -/
private theorem mapLeft_injective : Function.Injective (mapLeft (k := k) (A := A) (B := B)) := by
  let _ := (mapLeft (k := k) (A := A) (B := B)).toAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] B) (nonZeroDivisors A))
      (FractionRing A ⊗[k] B) := isLocalization_mapLeft
  exact IsLocalization.injective _ (algebraMapSubmonoid_le_nonZeroDivisors_of_flat A (A ⊗[k] B))

private theorem map_map_includeRight_mapLeft :
    ((nonZeroDivisors B).map (Algebra.TensorProduct.includeRight (R := k) (A := A))).map
        (mapLeft (k := k) (A := A) (B := B)) =
      (nonZeroDivisors B).map
        (Algebra.TensorProduct.includeRight (R := k) (A := FractionRing A)) := by
  ext z
  constructor
  · rintro ⟨x, ⟨b, hb, rfl⟩, rfl⟩
    exact ⟨b, hb, by simp⟩
  · rintro ⟨b, hb, rfl⟩
    exact ⟨Algebra.TensorProduct.includeRight b, Submonoid.mem_map_of_mem _ hb, by simp⟩

/-- `A ⊗[k] B` is integrally closed as soon as `Frac(A) ⊗[k] B` and `A ⊗[k] Frac(B)` are normal:
it is the intersection of these two localizations inside `Frac(A) ⊗[k] Frac(B)`. -/
private theorem isIntegrallyClosed_tensorProduct_of_fraction_baseChange
    (hS : IsNormalRing (FractionRing A ⊗[k] B)) (hT : IsNormalRing (A ⊗[k] FractionRing B)) :
    IsIntegrallyClosed (A ⊗[k] B) := by
  let K := FractionRing A
  let L := FractionRing B
  let R := A ⊗[k] B
  let S := K ⊗[k] B
  let T := A ⊗[k] L
  let U := K ⊗[k] L
  let f := IsScalarTower.toAlgHom k A K
  let g := IsScalarTower.toAlgHom k B L
  let _ : Algebra R S := (mapLeft (k := k) (A := A) (B := B)).toAlgebra
  let _ : Algebra R T := (Algebra.TensorProduct.map (AlgHom.id k A) g).toAlgebra
  let _ : Algebra R U := (Algebra.TensorProduct.map f g).toAlgebra
  let _ : Algebra S U := (Algebra.TensorProduct.map (AlgHom.id k K) g).toAlgebra
  let _ : Algebra T U := (Algebra.TensorProduct.map f (AlgHom.id k L)).toAlgebra
  have : IsScalarTower A R T := IsScalarTower.of_algebraMap_eq fun a ↦ by
    rw [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply,
      Algebra.TensorProduct.algebraMap_apply]
    simp [R, T, L, g]
  have : IsScalarTower K S U := IsScalarTower.of_algebraMap_eq (R := K) (S := S) (A := U)
    fun a ↦ by
      rw [RingHom.algebraMap_toAlgebra, Algebra.TensorProduct.algebraMap_apply,
        Algebra.TensorProduct.algebraMap_apply]
      simp [S, U, K, L, g]
  have : IsScalarTower R S U := IsScalarTower.of_algebraMap_eq' <| by
    ext a <;> simp [RingHom.algebraMap_toAlgebra, R, S, U, K, L, f]
  have : IsScalarTower R T U := IsScalarTower.of_algebraMap_eq' <| by
    ext a <;> simp [RingHom.algebraMap_toAlgebra, R, T, U, K, L, f, g]
  let M := Algebra.algebraMapSubmonoid R (nonZeroDivisors A)
  let N := (nonZeroDivisors B).map (Algebra.TensorProduct.includeRight (R := k) (A := A))
  have : IsLocalization M S := isLocalization_mapLeft
  have : IsLocalization N T := IsLocalization.tensorProduct_tensorProduct_right k A
    (nonZeroDivisors B) L (by ext b; simp [RingHom.algebraMap_toAlgebra, g])
  have : IsLocalization (N.map (algebraMap R S)) U := by
    rw [show N.map (algebraMap R S) = _ from map_map_includeRight_mapLeft]
    exact IsLocalization.tensorProduct_tensorProduct_right k K (nonZeroDivisors B) L
      (by ext b; simp [RingHom.algebraMap_toAlgebra, g])
  have : IsIntegrallyClosed S := hS.isIntegrallyClosed
  have : IsIntegrallyClosed T := hT.isIntegrallyClosed
  exact isIntegrallyClosed_of_localization_intersection (S := S) (T := T) (U := U) M N
    (algebraMapSubmonoid_le_nonZeroDivisors_of_flat A R) map_includeRight_nonZeroDivisors_le
    fun s t hst ↦ Algebra.TensorProduct.exists_map_eq_of_map_eq_of_injective f g
      (IsFractionRing.injective A K) s t (by simpa [RingHom.algebraMap_toAlgebra] using hst)

/-- `A ⊗[k] B` has finitely many minimal primes: its localization `Frac(A) ⊗[k] B` is Noetherian
and `A ⊗[k] B` embeds into it. -/
private theorem finite_minimalPrimes_tensorProduct [IsDomain A] [Algebra.FiniteType k B] :
    (minimalPrimes (A ⊗[k] B)).Finite := by
  let _ := (mapLeft (k := k) (A := A) (B := B)).toAlgebra
  have : IsLocalization (Algebra.algebraMapSubmonoid (A ⊗[k] B) (nonZeroDivisors A))
      (FractionRing A ⊗[k] B) := isLocalization_mapLeft
  have hi : Function.Injective (algebraMap (A ⊗[k] B) (FractionRing A ⊗[k] B)) :=
    mapLeft_injective
  have : IsNoetherianRing (FractionRing A ⊗[k] B) :=
    Algebra.FiniteType.isNoetherianRing (FractionRing A) _
  have hker : Ideal.comap (algebraMap (A ⊗[k] B) (FractionRing A ⊗[k] B)) ⊥ = ⊥ :=
    (RingHom.injective_iff_ker_eq_bot _).mp hi
  have h := (minimalPrimes.finite_of_isNoetherianRing (FractionRing A ⊗[k] B)).image
    (Ideal.comap (algebraMap (A ⊗[k] B) (FractionRing A ⊗[k] B)))
  rwa [← IsLocalization.minimalPrimes_comap
    (Algebra.algebraMapSubmonoid (A ⊗[k] B) (nonZeroDivisors A)), hker] at h

/-- **06DF for domains, with `B` of finite type.** -/
@[ega "IV 21.14.4" "special case"]
private theorem isNormalRing_tensorProduct_of_isDomain_of_finiteType [IsDomain A] [IsDomain B]
    [Algebra.FiniteType k B] [Algebra.IsGeometricallyNormal k A] (hB : IsNormalRing B) :
    IsNormalRing (A ⊗[k] B) := by
  have : Algebra.IsGeometricallyNormal k (FractionRing A) :=
    Algebra.IsGeometricallyNormal.of_isLocalization (A := A) (nonZeroDivisors A)
  have : Algebra.IsGeometricallyReduced k (FractionRing A) := isGeometricallyReduced
  have hS := isNormalRing_tensorProduct_of_isGeometricallyReduced k (FractionRing A) B hB
  have hT : IsNormalRing (A ⊗[k] FractionRing B) :=
    IsNormalRing.congr (Algebra.TensorProduct.comm k (FractionRing B) A).toRingEquiv
      (isNormalRing_tensorProduct_of_field (FractionRing B))
  have : IsReduced (FractionRing A ⊗[k] B) := hS.isReduced
  have : IsReduced (A ⊗[k] B) :=
    isReduced_of_injective (mapLeft (k := k) (A := A) (B := B)).toRingHom mapLeft_injective
  exact ((isIntegrallyClosed_tfae_of_finite_minimalPrimes
    finite_minimalPrimes_tensorProduct).out 1 2).mpr
    (isIntegrallyClosed_tensorProduct_of_fraction_baseChange hS hT)

end FractionBaseChange

/-- In a normal domain `B` over a field `k`, the image of a finitely generated domain `C` lies in
a finitely generated normal subalgebra: the image of the integral closure of `C` in its fraction
field, which is finite over `C` because fields are Nagata. -/
private theorem exists_fg_normal_subalgebra_of_finiteType {k C : Type u} {B : Type v} [Field k]
    [CommRing C] [IsDomain C] [CommRing B] [IsDomain B] [IsIntegrallyClosed B] [Algebra k C]
    [Algebra k B] [Algebra.FiniteType k C] (f : C →ₐ[k] B) (hf : Function.Injective f) :
    ∃ S : Subalgebra k B, S.FG ∧ IsNormalRing S ∧ f.range ≤ S := by
  have hjn : IsUniversallyJapaneseRing k ∧ IsNoetherianRing k :=
    ((isNagataRing_tfae (R := k)).out 1 3).mp (IsNagataRing.of_field (K := k))
  let N := integralClosure C (FractionRing C)
  have : Module.Finite C N := (hjn.1.japanese C).finite (FractionRing C)
  have : Algebra.FiniteType k N := .trans (inferInstance : Algebra.FiniteType k C)
    (Module.Finite.finiteType N)
  have : IsIntegrallyClosed N := integralClosure.isIntegrallyClosedOfFiniteExtension
    (FractionRing C)
  let i := IsScalarTower.toAlgHom k B (FractionRing B)
  have hfi : Function.Injective (i.comp f) :=
    (IsFractionRing.injective B (FractionRing B)).comp hf
  let g : FractionRing C →ₐ[k] FractionRing B :=
    IsFractionRing.liftAlgHom (K := FractionRing C) (g := i.comp f) hfi
  have hg (c : C) : g (algebraMap C (FractionRing C) c) = i (f c) :=
    IsFractionRing.lift_algebraMap (K := FractionRing C) (g := (i.comp f).toRingHom) hfi c
  let j : N →ₐ[k] FractionRing B := g.comp (N.val.restrictScalars k)
  have hjmem (z : N) : j z ∈ i.range :=
    (isIntegrallyClosed_iff (FractionRing B)).mp ‹IsIntegrallyClosed B›
      (IsIntegral.map_of_comp_eq f.toRingHom g.toRingHom (by ext c; exact (hg c).symm) z.2)
  let e := AlgEquiv.ofInjective i (IsFractionRing.injective B (FractionRing B))
  let l : N →ₐ[k] B := e.symm.toAlgHom.comp (j.codRestrict i.range hjmem)
  have hl (z : N) : i (l z) = j z :=
    congrArg Subtype.val (e.apply_symm_apply (j.codRestrict i.range hjmem z))
  have hli : Function.Injective l := fun x y hxy ↦
    Subtype.ext (g.injective ((hl x).symm.trans ((congrArg i hxy).trans (hl y))))
  refine ⟨l.range, (Subalgebra.fg_iff_finiteType _).mpr
      (Algebra.FiniteType.of_surjective l.rangeRestrict l.rangeRestrict_surjective),
    IsNormalRing.congr (AlgEquiv.ofInjective l hli).toRingEquiv
      (IsNormalRing.of_isIntegrallyClosed N), ?_⟩
  rintro _ ⟨c, rfl⟩
  have hjc : j (algebraMap C N c) = i (f c) := by simpa [j] using hg c
  exact ⟨algebraMap C N c, IsFractionRing.injective B (FractionRing B)
    (by simpa [i] using (hl _).trans hjc)⟩

/-- In a normal domain `B` over a field `k`, every finitely generated subalgebra lies in a
finitely generated normal subalgebra. -/
private theorem exists_fg_normal_subalgebra {k : Type u} {B : Type v} [Field k] [CommRing B]
    [IsDomain B] [IsIntegrallyClosed B] [Algebra k B] (S : Subalgebra k B) (hS : S.FG) :
    ∃ T : Subalgebra k B, T.FG ∧ IsNormalRing T ∧ S ≤ T := by
  have : Algebra.FiniteType k S := (Subalgebra.fg_iff_finiteType S).mp hS
  have : Small.{u} S := Algebra.FiniteType.small (R := k)
  let e := Shrink.algEquiv k S
  have : Algebra.FiniteType k (Shrink.{u} S) :=
    Algebra.FiniteType.of_surjective e.symm.toAlgHom e.symm.surjective
  obtain ⟨T, hT, hn, hle⟩ := exists_fg_normal_subalgebra_of_finiteType
    (S.val.comp e.toAlgHom) (Subtype.val_injective.comp e.injective)
  exact ⟨T, hT, hn, fun b hb ↦
    hle ⟨e.symm ⟨b, hb⟩, congrArg Subtype.val (e.apply_symm_apply ⟨b, hb⟩)⟩⟩

/-- **06DF for domains.** `B` is the directed union of its finitely generated normal subalgebras.
-/
@[ega "IV 21.14.4" "special case"]
private theorem isNormalRing_tensorProduct_of_isDomain {k : Type u} {A : Type v} {B : Type w}
    [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B] [IsDomain A] [IsDomain B]
    [Algebra.IsGeometricallyNormal k A] (hB : IsNormalRing B) : IsNormalRing (A ⊗[k] B) := by
  have : IsIntegrallyClosed B := hB.isIntegrallyClosed
  let I := {S : Subalgebra k B // S.FG ∧ IsNormalRing S}
  have : Nonempty I := by
    obtain ⟨S, hS, hN, _⟩ := exists_fg_normal_subalgebra (⊥ : Subalgebra k B) Subalgebra.fg_bot
    exact ⟨⟨S, hS, hN⟩⟩
  have : IsDirectedOrder I := ⟨fun S T ↦ by
    obtain ⟨U, hU, hN, hle⟩ := exists_fg_normal_subalgebra (S.1 ⊔ T.1) (S.2.1.sup T.2.1)
    exact ⟨⟨U, hU, hN⟩, le_sup_left.trans hle, le_sup_right.trans hle⟩⟩
  let f (S : Subalgebra k B) : A ⊗[k] S →ₐ[k] A ⊗[k] B :=
    Algebra.TensorProduct.map (AlgHom.id k A) S.val
  have hmono {S T : Subalgebra k B} (h : S ≤ T) : (f S).range ≤ (f T).range := by
    have heq : (f T).comp (Algebra.TensorProduct.map (AlgHom.id k A)
        (Subalgebra.inclusion h)) = f S := by
      ext a <;> simp [f]
    rw [← heq]
    exact AlgHom.range_comp_le_range _ _
  refine isNormalRing_of_directedUnion (ι := I) (fun S ↦ (f S.1).range.toSubring)
    (fun _ _ h ↦ hmono h) (fun x ↦ ?_) (fun S ↦ ?_)
  · induction x with
    | tmul a b =>
      obtain ⟨S, hS, hN, hle⟩ := exists_fg_normal_subalgebra (Algebra.adjoin k {b})
        ⟨{b}, by rw [Finset.coe_singleton]⟩
      exact ⟨⟨S, hS, hN⟩, Subalgebra.mem_toSubring.mpr
        ⟨a ⊗ₜ[k] ⟨b, hle (Algebra.self_mem_adjoin_singleton k b)⟩, by simp [f]⟩⟩
    | add x y hx hy =>
      obtain ⟨S, hS⟩ := hx
      obtain ⟨T, hT⟩ := hy
      obtain ⟨U, hSU, hTU⟩ := exists_ge_ge S T
      exact ⟨U, add_mem (hmono hSU hS) (hmono hTU hT)⟩
  · have : Algebra.FiniteType k S.1 := (Subalgebra.fg_iff_finiteType _).mp S.2.1
    have hi : Function.Injective (f S.1) := TensorProduct.map_injective_of_flat_flat
      (LinearMap.id : A →ₗ[k] A) S.1.val.toLinearMap Function.injective_id Subtype.val_injective
    exact IsNormalRing.congr (AlgEquiv.ofInjective (f S.1) hi).toRingEquiv
      (isNormalRing_tensorProduct_of_isDomain_of_finiteType S.2.2)

end Algebra.IsGeometricallyNormal.TensorProductOfNormal

open Algebra.IsGeometricallyNormal.TensorProductOfNormal in
/-- **Stacks 06DF.** The tensor product over a field `k` of a geometrically normal `k`-algebra and
a normal `k`-algebra is a normal ring. -/
@[stacks 06DF, ega "IV 21.14.4" "special case"]
theorem Algebra.IsGeometricallyNormal.isNormalRing_tensorProduct_of_isNormalRing (k : Type u)
    (A : Type v) (B : Type w) [Field k] [CommRing A] [CommRing B] [Algebra k A] [Algebra k B]
    [Algebra.IsGeometricallyNormal k A] (hB : IsNormalRing B) : IsNormalRing (A ⊗[k] B) := by
  refine isNormalRing_tensorProduct_of_localizations fun p _ ↦ ?_
  have hA : IsNormalRing A := IsNormalRing.congr (Algebra.TensorProduct.lid k A).toRingEquiv
    (isNormalRing_tensorProduct (A := A) k)
  have : IsDomain (Localization.AtPrime p) := (hA p).1
  have : Algebra.IsGeometricallyNormal k (Localization.AtPrime p) :=
    Algebra.IsGeometricallyNormal.of_isLocalization (A := A) p.primeCompl
  refine IsNormalRing.congr (Algebra.TensorProduct.comm k B (Localization.AtPrime p)).toRingEquiv
    (isNormalRing_tensorProduct_of_localizations fun q _ ↦ ?_)
  have : IsDomain (Localization.AtPrime q) := (hB q).1
  exact IsNormalRing.congr
    (Algebra.TensorProduct.comm k (Localization.AtPrime p) (Localization.AtPrime q)).toRingEquiv
    (isNormalRing_tensorProduct_of_isDomain
      (hB.isLocalization q.primeCompl (Localization.AtPrime q)))
