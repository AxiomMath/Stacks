module

public import Mathlib.Algebra.Lie.OfAssociative
public import Mathlib.Algebra.Order.Floor.Extended
public import Mathlib.Algebra.Order.Interval.Basic
public import Mathlib.Analysis.Complex.UpperHalfPlane.Basic
public import Mathlib.Analysis.SpecialFunctions.Bernstein
public import Mathlib.Analysis.SpecialFunctions.Gamma.Basic
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
public import Mathlib.Combinatorics.Enumerative.DyckWord
public import Mathlib.Combinatorics.SimpleGraph.Triangle.Removal
public import Mathlib.Data.NNRat.Floor
public import Mathlib.Data.Nat.Choose.Multinomial
public import Mathlib.Geometry.Euclidean.Altitude
public import Mathlib.NumberTheory.Chebyshev
public import Mathlib.NumberTheory.Height.NumberField
public import Mathlib.NumberTheory.Height.Projectivization
public import Mathlib.NumberTheory.LucasLehmer
public import Mathlib.NumberTheory.SelbergSieve
public import Mathlib.Order.CompletePartialOrder
public import Mathlib.RingTheory.Henselian
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
public import Mathlib.RingTheory.PicardGroup
public import Mathlib.RingTheory.Radical.NatInt
public import Mathlib.RingTheory.RegularLocalRing.Defs
public import Mathlib.RingTheory.RingHom.QuasiFinite
public import Mathlib.RingTheory.SimpleRing.Principal
public import Mathlib.RingTheory.TotallySplit
public import Mathlib.RingTheory.Unramified.LocalRing
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.RingTheory.ZariskisMainTheorem
public import Mathlib.Tactic.Echelon.Zsqrtd
public import Mathlib.Tactic.NormNum.Irrational
public import Mathlib.Tactic.NormNum.IsCoprime
public import Mathlib.Tactic.NormNum.IsSquare
public import Mathlib.Tactic.NormNum.LegendreSymbol
public import Mathlib.Tactic.NormNum.ModEq
public import Mathlib.Tactic.NormNum.NatFib
public import Mathlib.Tactic.NormNum.NatLog
public import Mathlib.Tactic.NormNum.NatSqrt
public import Mathlib.Tactic.NormNum.Ordinal
public import Mathlib.Tactic.NormNum.Parity
public import Mathlib.Tactic.NormNum.Prime
public import Mathlib.Tactic.NormNum.RealSqrt
import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Topology.Sheaves.Init
import Mathlib.Topology.Sheaves.Presheaf
import StacksCore.Tactic.StacksAttribute
import StacksFrontier.RingTheory.Artinian.FiniteType
public import StacksFrontier.Topology.Dimension.Krull

@[expose] public section

/-!
# Isolated points in the fibres of a ring map of finite type

Let `R → S` be of finite type, let `𝔮` be a prime of `S` lying over `𝔭 ⊂ R`, let
`F = Spec (κ(𝔭) ⊗_R S)` be the fibre over `𝔭` and let `q̄ ∈ F` be the point corresponding to
`𝔮`.  This file proves Stacks 00PK: the six conditions "`q̄` is isolated in `F`",
"`S_𝔮/𝔭S_𝔮` is finite over `κ(𝔭)`", "some `g ∉ 𝔮` has `𝔮` as the only prime of `D(g)` over `𝔭`",
"`dim_q̄ F = 0`", "`q̄` is closed in `F` and `dim S_𝔮/𝔭S_𝔮 = 0`" and "`κ(𝔮)/κ(𝔭)` is finite and
`dim S_𝔮/𝔭S_𝔮 = 0`" are equivalent.

## Main results

* `Stacks.QuasiFinite.IsolatedFibrePoint.solution`: the equivalence of the conditions above.

## Implementation notes

The route is the source's: everything is transported to Lemma 00PJ for the `κ(𝔭)`-algebra
`κ(𝔭) ⊗_R S`, which is of finite type over the field `κ(𝔭)`, at the prime `q̄`.

The lemma that carries the transport is `isLocalization_atPrime_qbar`: the ring `S_𝔮/𝔭S_𝔮`, in
the form `κ(𝔭) ⊗_R S_𝔮`, *is* a localization of `κ(𝔭) ⊗_R S` at `q̄`.  It is a localization at
the image of `S ∖ 𝔮`, because localization commutes with the base change `R → κ(𝔭)`
(`IsLocalization.tensorProduct_tensorProduct_right`), and that image already inverts everything
outside `q̄`, because every element of `κ(𝔭) ⊗_R S` is `1 ⊗ s` up to a unit
(`isUnit_algebraMap_of_notMem_qbar`).  Feeding it to Lemma 00PJ as the model `Sq` of the local
ring makes condition (2) of the two lemmas literally the same statement, and
`ringKrullDim_eq_zero_iff_height_eq_zero` turns `dim S_𝔮/𝔭S_𝔮` into the height of `q̄`.

The point `q̄` is spelled as the kernel of the `κ(𝔭)`-algebra map
`toResidueField : κ(𝔭) ⊗_R S →ₐ[κ(𝔭)] κ(𝔮)`.  That is the same prime as the one
`PrimeSpectrum.preimageEquivFiber` attaches to `𝔮` (`preimageEquivFiber_fiberPoint`), which is
what makes the fibre subspace of `Spec S` and `Spec (κ(𝔭) ⊗_R S)` interchangeable, by the
homeomorphism `PrimeSpectrum.preimageHomeomorphFiber`; conditions (1), (4) and the first half of
(5) are read across it.

Condition (6) is *not* transported through condition (6) of Lemma 00PJ, which is about `κ(q̄)`:
instead `toResidueField` is used twice, once for `κ(𝔭) ⊗_R S_𝔮 ↠ κ(𝔮)`, which gives (2) → (6),
and once for `(κ(𝔭) ⊗_R S)/q̄ ↪ κ(𝔮)`, which gives (6) → (5) since a finite-dimensional domain
over a field is a field.  This avoids identifying `κ(q̄)` with `κ(𝔮)`.

Condition (3) is compared with condition (1) inside `Spec S` rather than through condition (3)
of Lemma 00PJ, whose `g` is an element of the fibre ring: producing a `g` in `S` instead is
Mathlib's `Ideal.exists_notMem_forall_mem_of_ne_of_liesOver`, for a ring map quasi-finite at
`𝔮`, and `Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber` is condition (1), read in the fibre
over the image of `𝔮` rather than over `𝔭` (`isOpen_singleton_fiber_congr`).

The `κ(𝔭) ⊗_R S`-algebra structure on `κ(𝔭) ⊗_R S_𝔮` is the one induced by the localization map
`S → S_𝔮`, and it is taken as the `toAlgebra` of `toFiberLocalization`, a map of
`κ(𝔭)`-algebras: the scalar tower `κ(𝔭) → κ(𝔭) ⊗_R S → κ(𝔭) ⊗_R S_𝔮` that Lemma 00PJ asks for
is then `IsScalarTower.of_algHom` rather than a computation.

## References

* [StacksProject 00PK](https://stacks.math.columbia.edu/tag/00PK)
-/

@[expose] public section

namespace Stacks.QuasiFinite.IsolatedFibrePoint

open TensorProduct PrimeSpectrum

section KrullDimAt

variable {X Y : Type*} [TopologicalSpace X] [TopologicalSpace Y]

/-- The Krull dimension at a point depends only on a neighbourhood of that point: along an
open embedding `f`, the dimensions at `x` and at `f x` agree. The two infima are cofinal in
each other, since `f '' U` is an open neighbourhood of `f x` homeomorphic to `U`, and `f ⁻¹' V`
is an open neighbourhood of `x` whose image `f '' (f ⁻¹' V)` is a subspace of `V`. -/
private lemma krullDimAt_eq_of_isOpenEmbedding {f : X → Y} (hf : Topology.IsOpenEmbedding f)
    (x : X) : topologicalKrullDimAt Y (f x) = topologicalKrullDimAt X x := by
  refine le_antisymm
    (le_iInf fun U ↦ iInf_le_of_le ⟨f '' U.1, ⟨x, U.2.1, rfl⟩, hf.isOpenMap _ U.2.2⟩ ?_)
    (le_iInf fun V ↦ iInf_le_of_le ⟨f ⁻¹' V.1, V.2.1, V.2.2.preimage hf.continuous⟩ ?_)
  · exact (IsHomeomorph.topologicalKrullDim_eq _
      (hf.isEmbedding.homeomorphImage U.1).isHomeomorph).ge
  · refine (IsHomeomorph.topologicalKrullDim_eq _
      (hf.isEmbedding.homeomorphImage (f ⁻¹' V.1)).isHomeomorph).trans_le ?_
    exact Topology.IsInducing.topologicalKrullDim_le
      (Topology.IsEmbedding.inclusion (Set.image_preimage_subset f V.1)).isInducing

/-- The Krull dimension at a point is a homeomorphism invariant: the pointwise form of
`IsHomeomorph.topologicalKrullDim_eq`. -/
private lemma krullDimAt_eq_of_homeomorph (e : X ≃ₜ Y) (x : X) :
    topologicalKrullDimAt X x = topologicalKrullDimAt Y (e x) :=
  (krullDimAt_eq_of_isOpenEmbedding e.isOpenEmbedding x).symm

end KrullDimAt

section

variable {S : Type*} [CommRing S] (q : Ideal S) [q.IsPrime] (Sq : Type*) [CommRing Sq]
  [Algebra S Sq] [IsLocalization.AtPrime Sq q]

/-- A local ring of `S` at a prime `q` has dimension `0` exactly when `q` has height `0`. -/
private lemma ringKrullDim_eq_zero_iff_height_eq_zero : ringKrullDim Sq = 0 ↔ q.height = 0 := by
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height q Sq]
  exact WithBot.coe_eq_zero

end

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (𝔭 : Ideal R) [𝔭.IsPrime] (𝔮 : Ideal S) [𝔮.IsPrime]

/-- The map of `κ(𝔭)`-algebras `κ(𝔭) ⊗_R S → κ(𝔭) ⊗_R S_𝔮` induced by the localization map
`S → S_𝔮`. -/
private noncomputable abbrev toFiberLocalization :
    𝔭.Fiber S →ₐ[𝔭.ResidueField] 𝔭.Fiber (Localization.AtPrime 𝔮) :=
  Algebra.TensorProduct.lTensor _ (IsScalarTower.toAlgHom R S (Localization.AtPrime 𝔮))

/-- `κ(𝔭) ⊗_R S_𝔮` as an algebra over the fibre `κ(𝔭) ⊗_R S`, along `toFiberLocalization`. -/
@[instance_reducible]
private noncomputable def fiberLocalizationAlgebra :
    Algebra (𝔭.Fiber S) (𝔭.Fiber (Localization.AtPrime 𝔮)) :=
  (toFiberLocalization 𝔭 𝔮).toRingHom.toAlgebra

attribute [local instance] fiberLocalizationAlgebra

private lemma algebraMap_fiberLocalization_apply (x : 𝔭.Fiber S) :
    algebraMap (𝔭.Fiber S) (𝔭.Fiber (Localization.AtPrime 𝔮)) x = toFiberLocalization 𝔭 𝔮 x :=
  rfl

/-- The scalar tower `κ(𝔭) → κ(𝔭) ⊗_R S → κ(𝔭) ⊗_R S_𝔮`. -/
private lemma isScalarTower_fiberLocalization :
    IsScalarTower 𝔭.ResidueField (𝔭.Fiber S) (𝔭.Fiber (Localization.AtPrime 𝔮)) :=
  IsScalarTower.of_algHom (toFiberLocalization 𝔭 𝔮)

end

attribute [local instance] fiberLocalizationAlgebra isScalarTower_fiberLocalization

section

variable {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
  (𝔭 : Ideal R) [𝔭.IsPrime] (𝔮 : Ideal S) [𝔮.IsPrime] [𝔮.LiesOver 𝔭]
  [Algebra (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)]
  [IsScalarTower R (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)]

/-- The point of the fibre of `Spec S → Spec R` over `𝔭` given by a prime `𝔮` lying over `𝔭`. -/
private abbrev fiberPoint :
    ↥(comap (algebraMap R S) ⁻¹' {(⟨𝔭, ‹_›⟩ : PrimeSpectrum R)}) :=
  ⟨⟨𝔮, ‹_›⟩, PrimeSpectrum.ext (𝔮.over_def 𝔭).symm⟩

/-- The canonical `κ(𝔭)`-algebra map from the fibre `κ(𝔭) ⊗_R S` to the residue field `κ(𝔮)`:
on the left factor it is the residue field extension `κ(𝔭) → κ(𝔮)`, on the right factor the
canonical map `S → κ(𝔮)`.  Its kernel is the point `q̄` of the fibre. -/
private noncomputable abbrev toResidueField : 𝔭.Fiber S →ₐ[𝔭.ResidueField] 𝔮.ResidueField :=
  Algebra.TensorProduct.lift (Algebra.ofId 𝔭.ResidueField 𝔮.ResidueField)
    (IsScalarTower.toAlgHom R S 𝔮.ResidueField) fun _ _ ↦ .all _ _

/-- The point `q̄` of the fibre `Spec (κ(𝔭) ⊗_R S)` corresponding to `𝔮`, as the kernel of
`toResidueField`. -/
private noncomputable abbrev qbar : Ideal (𝔭.Fiber S) :=
  RingHom.ker (toResidueField 𝔭 𝔮)

private instance isPrime_qbar : (qbar 𝔭 𝔮).IsPrime := RingHom.ker_isPrime _

/-- `q̄` is the point that `PrimeSpectrum.preimageEquivFiber` attaches to `𝔮`. -/
private lemma preimageEquivFiber_fiberPoint :
    PrimeSpectrum.preimageEquivFiber R S (⟨𝔭, ‹_›⟩ : PrimeSpectrum R) (fiberPoint 𝔭 𝔮)
      = ⟨qbar 𝔭 𝔮, inferInstance⟩ := by
  refine PrimeSpectrum.ext ?_
  rw [PrimeSpectrum.preimageEquivFiber_apply_asIdeal]
  congr 1
  ext x
  · simp
  · simp

/-- An element of `S` lies in `𝔮` exactly when `1 ⊗ s` lies in `q̄`: the map `toResidueField`
sends `1 ⊗ s` to the image of `s` in `κ(𝔮)`. -/
private lemma one_tmul_mem_qbar_iff (s : S) :
    (1 : 𝔭.ResidueField) ⊗ₜ[R] s ∈ qbar 𝔭 𝔮 ↔ s ∈ 𝔮 := by
  simp [RingHom.mem_ker, Ideal.algebraMap_residueField_eq_zero]

omit [𝔮.IsPrime] [𝔮.LiesOver 𝔭] [Algebra (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)]
  [IsScalarTower R (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)] in
/-- An element of `R ∖ 𝔭` is invertible in the fibre `κ(𝔭) ⊗_R T`, being invertible already in
the field `κ(𝔭)`. -/
private lemma isUnit_algebraMap_of_notMem (T : Type*) [CommRing T] [Algebra R T] {r : R}
    (hr : r ∉ 𝔭) : IsUnit (algebraMap R (𝔭.Fiber T) r) := by
  rw [IsScalarTower.algebraMap_apply R 𝔭.ResidueField (𝔭.Fiber T)]
  exact (isUnit_iff_ne_zero.mpr
    fun h ↦ hr (Ideal.algebraMap_residueField_eq_zero.mp h)).map _

/-- **Everything outside `q̄` is inverted in `κ(𝔭) ⊗_R S_𝔮`.**  Some `r ∈ R ∖ 𝔭` takes `x` to a
pure tensor `1 ⊗ s` (`Ideal.Fiber.exists_smul_eq_one_tmul`), and `r` is a unit, so `x ∉ q̄`
forces `s ∉ 𝔮`; and `s` is inverted in `S_𝔮`. -/
private lemma isUnit_algebraMap_of_notMem_qbar {x : 𝔭.Fiber S} (hx : x ∉ qbar 𝔭 𝔮) :
    IsUnit (algebraMap (𝔭.Fiber S) (𝔭.Fiber (Localization.AtPrime 𝔮)) x) := by
  obtain ⟨r, hr, s, e⟩ := Ideal.Fiber.exists_smul_eq_one_tmul (S := S) 𝔭 x
  have hru : IsUnit (algebraMap R (𝔭.Fiber S) r) := isUnit_algebraMap_of_notMem 𝔭 S hr
  have hsq : s ∉ 𝔮 := by
    rw [← one_tmul_mem_qbar_iff 𝔭 𝔮, ← e, Algebra.smul_def, mul_comm,
      Ideal.mul_unit_mem_iff_mem _ hru]
    exact hx
  refine isUnit_of_mul_isUnit_right (x := algebraMap (𝔭.Fiber S)
    (𝔭.Fiber (Localization.AtPrime 𝔮)) (algebraMap R (𝔭.Fiber S) r)) ?_
  have key : algebraMap (𝔭.Fiber S) (𝔭.Fiber (Localization.AtPrime 𝔮))
        (algebraMap R (𝔭.Fiber S) r)
      * algebraMap (𝔭.Fiber S) (𝔭.Fiber (Localization.AtPrime 𝔮)) x
      = (1 : 𝔭.ResidueField) ⊗ₜ[R] algebraMap S (Localization.AtPrime 𝔮) s := by
    rw [← map_mul, ← Algebra.smul_def, e]
    simp [algebraMap_fiberLocalization_apply]
  rw [key]
  simpa using (IsLocalization.map_units (M := 𝔮.primeCompl) (Localization.AtPrime 𝔮)
    ⟨s, hsq⟩).map (Algebra.TensorProduct.includeRight (R := R) (A := 𝔭.ResidueField)
      (B := Localization.AtPrime 𝔮))

/-- **The local ring of the fibre at `q̄` is the fibre ring `S_𝔮/𝔭S_𝔮`.**  `κ(𝔭) ⊗_R S_𝔮` is a
localization of `κ(𝔭) ⊗_R S` at the image of `S ∖ 𝔮`, because localization commutes with the
base change along `R → κ(𝔭)`; and that image is enough, everything outside `q̄` being inverted
there. -/
private lemma isLocalization_atPrime_qbar :
    IsLocalization.AtPrime (𝔭.Fiber (Localization.AtPrime 𝔮)) (qbar 𝔭 𝔮) := by
  set M := 𝔮.primeCompl.map (Algebra.TensorProduct.includeRight
    (R := R) (A := 𝔭.ResidueField) (B := S)) with hM
  have hL : IsLocalization M (𝔭.Fiber (Localization.AtPrime 𝔮)) :=
    IsLocalization.tensorProduct_tensorProduct_right R 𝔭.ResidueField 𝔮.primeCompl
      (Localization.AtPrime 𝔮) (by ext x; simp [algebraMap_fiberLocalization_apply])
  refine IsLocalization.of_le (M := M) _ ?_ fun x hx ↦ isUnit_algebraMap_of_notMem_qbar 𝔭 𝔮 hx
  rintro x ⟨s, hs, rfl⟩
  simpa [hM, Ideal.primeCompl, one_tmul_mem_qbar_iff] using hs

/-- Condition (2) implies the first half of condition (6): `S_𝔮/𝔭S_𝔮 = κ(𝔭) ⊗_R S_𝔮` maps onto
`κ(𝔮)`, because `S_𝔮 → κ(𝔮)` is surjective. -/
private lemma finite_residueField_of_finite_fiber
    (h : Module.Finite 𝔭.ResidueField (𝔭.Fiber (Localization.AtPrime 𝔮))) :
    Module.Finite 𝔭.ResidueField 𝔮.ResidueField := by
  refine Module.Finite.of_surjective (Algebra.TensorProduct.lift
    (Algebra.ofId 𝔭.ResidueField 𝔮.ResidueField)
    (IsScalarTower.toAlgHom R (Localization.AtPrime 𝔮) 𝔮.ResidueField)
    (fun _ _ ↦ .all _ _)).toLinearMap fun y ↦ ?_
  obtain ⟨t, rfl⟩ := IsLocalRing.residue_surjective (R := Localization.AtPrime 𝔮) y
  exact ⟨1 ⊗ₜ t, by simp [IsLocalRing.ResidueField.algebraMap_eq]⟩

/-- The first half of condition (6) implies that `q̄` is a closed point: `(κ(𝔭) ⊗_R S)/q̄`
embeds in `κ(𝔮)` by construction of `q̄`, so it is a finite-dimensional domain over `κ(𝔭)`,
hence a field. -/
private lemma isMaximal_qbar_of_finite_residueField
    (h : Module.Finite 𝔭.ResidueField 𝔮.ResidueField) : (qbar 𝔭 𝔮).IsMaximal := by
  have : Module.Finite 𝔭.ResidueField (𝔭.Fiber S ⧸ qbar 𝔭 𝔮) :=
    Module.Finite.of_injective (Ideal.kerLiftAlg (toResidueField 𝔭 𝔮)).toLinearMap
      (by simpa using Ideal.kerLiftAlg_injective (toResidueField 𝔭 𝔮))
  have : IsArtinianRing (𝔭.Fiber S ⧸ qbar 𝔭 𝔮) := .of_finite 𝔭.ResidueField _
  exact Ideal.Quotient.maximal_of_isField _ (IsArtinianRing.isField_of_isDomain _)

/-- Renaming the point of `Spec R` under `𝔮` does not change the fibre subspace or its
distinguished point. -/
private lemma isOpen_singleton_fiber_congr {P P' : PrimeSpectrum R} (h : P = P')
    (q : PrimeSpectrum S) (hq : comap (algebraMap R S) q = P) :
    IsOpen (X := comap (algebraMap R S) ⁻¹' {P}) {⟨q, hq⟩} ↔
      IsOpen (X := comap (algebraMap R S) ⁻¹' {P'}) {⟨q, hq.trans h⟩} := by
  subst h; rfl

omit [Algebra (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)]
  [IsScalarTower R (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)] in
/-- Conditions (1) and (3) of the source, compared inside `Spec S`: `𝔮` is isolated in its
fibre exactly when some basic open `D(g)` meets the fibre in `𝔮` alone. -/
private lemma isOpen_singleton_fiberPoint_iff [Algebra.FiniteType R S] :
    IsOpen {fiberPoint 𝔭 𝔮} ↔ ∃ g ∉ 𝔮, {q ∈ 𝔭.primesOver S | g ∉ q} = {𝔮} := by
  constructor
  · intro hopen
    have : Algebra.QuasiFiniteAt R 𝔮 :=
      Algebra.QuasiFiniteAt.of_isOpen_singleton_fiber (R := R) ⟨𝔮, ‹_›⟩
        ((isOpen_singleton_fiber_congr (P := (⟨𝔭, ‹_›⟩ : PrimeSpectrum R))
          (P' := PrimeSpectrum.comap (algebraMap R S) ⟨𝔮, ‹_›⟩)
          (PrimeSpectrum.ext (𝔮.over_def 𝔭)) ⟨𝔮, ‹_›⟩
          (PrimeSpectrum.ext (𝔮.over_def 𝔭).symm)).mp hopen)
    obtain ⟨g, hg, H⟩ := Ideal.exists_notMem_forall_mem_of_ne_of_liesOver 𝔭 𝔮
    refine ⟨g, hg, Set.eq_singleton_iff_unique_mem.mpr
      ⟨⟨⟨inferInstance, inferInstance⟩, hg⟩, ?_⟩⟩
    rintro q' ⟨⟨hq'p, hq'o⟩, hgq'⟩
    by_contra hne
    exact hgq' (H q' hq'p hne hq'o)
  · rintro ⟨g, hg, hgs⟩
    have hset : {fiberPoint 𝔭 𝔮}
        = Subtype.val ⁻¹' (PrimeSpectrum.basicOpen g : Set (PrimeSpectrum S)) := by
      ext y
      have hy : y.1.asIdeal ∈ 𝔭.primesOver S := ⟨y.1.2, ⟨congr($(y.2).asIdeal).symm⟩⟩
      simp only [Set.mem_singleton_iff, Set.mem_preimage, SetLike.mem_coe,
        PrimeSpectrum.mem_basicOpen]
      exact ⟨fun hyq ↦ hyq ▸ hg,
        fun hgy ↦ Subtype.ext (PrimeSpectrum.ext (hgs.subset ⟨hy, hgy⟩))⟩
    rw [hset]
    exact (PrimeSpectrum.basicOpen g).isOpen.preimage continuous_subtype_val

end

attribute [local instance] isLocalization_atPrime_qbar

/-- **Stacks 00PK.** Let `R → S` be of finite type, let `𝔮` be a prime of `S` lying over `𝔭`,
let `F = Spec (κ(𝔭) ⊗_R S)` be the fibre over `𝔭` and let `q̄ ∈ F` be the point corresponding to
`𝔮`.  Then `q̄` is isolated in `F` iff `S_𝔮/𝔭S_𝔮` is finite over `κ(𝔭)` iff some `g ∉ 𝔮` has
`𝔮` as the only prime of `D(g)` over `𝔭` iff `dim_q̄ F = 0` iff `q̄` is closed in `F` and
`dim S_𝔮/𝔭S_𝔮 = 0` iff `κ(𝔮)/κ(𝔭)` is finite and `dim S_𝔮/𝔭S_𝔮 = 0`. -/
public theorem solution {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (𝔭 : Ideal R) [𝔭.IsPrime] (𝔮 : Ideal S) [𝔮.IsPrime]
    [𝔮.LiesOver 𝔭] [Algebra (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)]
    [IsScalarTower R (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)] :
    List.TFAE
      [IsOpen (X := PrimeSpectrum.comap (algebraMap R S) ⁻¹' {(⟨𝔭, ‹_›⟩ : PrimeSpectrum R)})
          {⟨⟨𝔮, ‹_›⟩, PrimeSpectrum.ext (𝔮.over_def 𝔭).symm⟩},
        Module.Finite 𝔭.ResidueField (𝔭.Fiber (Localization.AtPrime 𝔮)),
        ∃ g ∉ 𝔮, {q ∈ 𝔭.primesOver S | g ∉ q} = {𝔮},
        topologicalKrullDimAt
            ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {(⟨𝔭, ‹_›⟩ : PrimeSpectrum R)})
            ⟨⟨𝔮, ‹_›⟩, PrimeSpectrum.ext (𝔮.over_def 𝔭).symm⟩ = 0,
        IsClosed (X := PrimeSpectrum.comap (algebraMap R S) ⁻¹' {(⟨𝔭, ‹_›⟩ : PrimeSpectrum R)})
            {⟨⟨𝔮, ‹_›⟩, PrimeSpectrum.ext (𝔮.over_def 𝔭).symm⟩} ∧
          ringKrullDim (𝔭.Fiber (Localization.AtPrime 𝔮)) = 0,
        Module.Finite 𝔭.ResidueField 𝔮.ResidueField ∧
          ringKrullDim (𝔭.Fiber (Localization.AtPrime 𝔮)) = 0] := by
  -- Lemma 00PJ for the `κ(𝔭)`-algebra `κ(𝔭) ⊗_R S` at `q̄`, with `κ(𝔭) ⊗_R S_𝔮` as the model
  -- of the local ring there.
  have H := (PrimeSpectrum.isOpen_singleton_tfae_and_exists_algEquiv_prod_of_finiteType
    𝔭.ResidueField (qbar 𝔭 𝔮) (𝔭.Fiber (Localization.AtPrime 𝔮))).1
  have hdim := ringKrullDim_eq_zero_iff_height_eq_zero (qbar 𝔭 𝔮)
    (𝔭.Fiber (Localization.AtPrime 𝔮))
  -- The fibre subspace of `Spec S` and `Spec (κ(𝔭) ⊗_R S)` are homeomorphic, and the
  -- homeomorphism carries the point `𝔮` to `q̄`.
  set e := PrimeSpectrum.preimageHomeomorphFiber R S (⟨𝔭, ‹_›⟩ : PrimeSpectrum R)
  have hept : e (fiberPoint 𝔭 𝔮) = ⟨qbar 𝔭 𝔮, inferInstance⟩ := preimageEquivFiber_fiberPoint 𝔭 𝔮
  have h1 : IsOpen {fiberPoint 𝔭 𝔮}
      ↔ IsOpen {(⟨qbar 𝔭 𝔮, inferInstance⟩ : PrimeSpectrum (𝔭.Fiber S))} := by
    rw [← hept, ← Set.image_singleton (f := e), e.isOpen_image]
  have h5 : IsClosed {fiberPoint 𝔭 𝔮}
      ↔ IsClosed {(⟨qbar 𝔭 𝔮, inferInstance⟩ : PrimeSpectrum (𝔭.Fiber S))} := by
    rw [← hept, ← Set.image_singleton (f := e), e.isClosed_image]
  have h4 : topologicalKrullDimAt _ (fiberPoint 𝔭 𝔮)
      = topologicalKrullDimAt (PrimeSpectrum (𝔭.Fiber S)) ⟨qbar 𝔭 𝔮, inferInstance⟩ := by
    rw [krullDimAt_eq_of_homeomorph e, hept]
  tfae_have 1 ↔ 2 := h1.trans (H.out 1 2)
  tfae_have 1 ↔ 3 := isOpen_singleton_fiberPoint_iff 𝔭 𝔮
  tfae_have 1 ↔ 4 := by rw [h4]; exact h1.trans (H.out 1 4)
  tfae_have 1 ↔ 5 := h1.trans ((H.out 1 5).trans (and_congr h5.symm hdim.symm))
  tfae_have 2 → 6 := fun h ↦ by
    have h25 := (H.out 2 5).mp h
    exact ⟨finite_residueField_of_finite_fiber 𝔭 𝔮 h, hdim.mpr h25.2⟩
  tfae_have 6 → 5 := fun h ↦ ⟨h5.mpr ((PrimeSpectrum.isClosed_singleton_iff_isMaximal _).mpr
      (isMaximal_qbar_of_finite_residueField 𝔭 𝔮 h.1)), h.2⟩
  tfae_finish

end Stacks.QuasiFinite.IsolatedFibrePoint

end

/-!
# Isolated points in the fibres of a ring map of finite type

Let `R → S` be a ring map of finite type, let `𝔮` be a prime of `S` lying over a prime `𝔭` of
`R`, let `F = Spec (S ⊗_R κ(𝔭))` be the fibre of `Spec S → Spec R` over `𝔭` and let `q̄ ∈ F` be
the point corresponding to `𝔮`. The following are equivalent: `q̄` is an isolated point of `F`;
the local ring `S_𝔮/𝔭S_𝔮` of `F` at `q̄` is finite over `κ(𝔭)`; there is a `g ∈ S`, `g ∉ 𝔮`,
such that `𝔮` is the only prime of `D(g)` lying over `𝔭`; `F` has dimension `0` at `q̄`; `q̄` is
a closed point of `F` and `dim S_𝔮/𝔭S_𝔮 = 0`; the residue field extension `κ(𝔮)/κ(𝔭)` is
finite and `dim S_𝔮/𝔭S_𝔮 = 0`. These are the conditions under which `R → S` is called
quasi-finite at `𝔮`.

## Main results

* `Algebra.isOpen_singleton_fiber_tfae_of_finiteType`: the six equivalent conditions.

## Implementation notes

The fibre is the subspace `comap (algebraMap R S) ⁻¹' {𝔭}` of `Spec S`, not the space
`Spec (S ⊗_R κ(𝔭))`; the two are homeomorphic, by `PrimeSpectrum.preimageHomeomorphFiber`, and
the subspace carries the point `q̄` as `𝔮` itself, so the conditions read as conditions on `𝔮`
and need no transported point. It is also the form in which quasi-finiteness is phrased in
`Algebra.quasiFiniteAt_iff_isOpen_singleton_fiber`, by which condition (1) is
`Algebra.QuasiFiniteAt R 𝔮`, the property named in Definition 00PL.

The ring `S_𝔮/𝔭S_𝔮` is `κ(𝔭) ⊗_R S_𝔮`, written `𝔭.Fiber (Localization.AtPrime 𝔮)`: this is
the source's own identification of `S_𝔮/𝔭S_𝔮` with the local ring of `F` at `q̄`, it is the
spelling in which `Algebra.QuasiFinite` is stated, and it is a `κ(𝔭)`-algebra by construction,
where the quotient `S_𝔮/𝔭S_𝔮` is one only after inverting `R ∖ 𝔭`. The dimension `dim_q̄ F` of a
space at a point is `topologicalKrullDimAt`, the project's form of Stacks 0055 (4), and the
dimension of a ring is `ringKrullDim`. The extension `κ(𝔮)/κ(𝔭)` is between Mathlib's
`Ideal.ResidueField`s, whose `κ(𝔭)`-algebra structure is the canonical one by
the `IsScalarTower R (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)` hypothesis.

The localization at `𝔮` is the concrete `Localization.AtPrime 𝔮` rather than an abstract
`Sq` with `IsLocalization.AtPrime Sq 𝔮`, as Lemma 00PJ's form has it. Nothing is lost: the two
conditions naming `S_𝔮` are invariant under the canonical isomorphism, `Ideal.ResidueField 𝔮`
in condition (6) is *defined* as the residue field of `Localization.AtPrime 𝔮`, and
`Algebra.QuasiFiniteAt`, the property this lemma characterises, is likewise stated over it, so
an abstract `Sq` would buy generality in condition (2) alone at the price of a scalar tower in
every application.

Condition (3) is stated at the level of primes of `S`, as the source states it: the primes of
`D(g)` lying over `𝔭` are the members of `𝔭.primesOver S` avoiding `g`, and the condition is
that this set is `{𝔮}`.

Conditions (5) and (6) read `dim S_𝔮/𝔭S_𝔮 = 0` as the vanishing of `ringKrullDim` of the
ring the source names in condition (2), rather than as the height of `q̄` in the fibre ring
`S ⊗_R κ(𝔭)`. The two are the same number: `𝔭.Fiber (Localization.AtPrime 𝔮)` is the local
ring of `S ⊗_R κ(𝔭)` at `q̄`, which is `Ideal.Fiber.localizationAlgEquivQuotient` read through
`κ(𝔭) ⊗_R S_𝔮 = S_𝔮/𝔭S_𝔮`, and `ringKrullDim` of a localization at a prime is that
prime's height, by `IsLocalization.AtPrime.ringKrullDim_eq_height`. Lemma 00PJ, over the base
`κ(𝔭)`, states these two conditions with `height`.

Faithfulness. (1) No hypothesis is idle: `Algebra.FiniteType R S` is needed already for
(1) → (2) (for `R = k` a field and `S = k(x)` the unique point of the fibre over `𝔭 = 0` is
isolated while `S_𝔮/𝔭S_𝔮 = k(x)` is not finite over `k`), and `𝔮.LiesOver 𝔭` is what places
`q̄` in `F` and makes `κ(𝔮)` an extension of `κ(𝔭)`. (2) The scalars and base are the source's:
finiteness in (2) and (6) is over `κ(𝔭)`, the localization is at `𝔮` over `S`, and the fibre is
taken over `𝔭` along `R → κ(𝔭)`. (3) The canonical maps are pinned: `q̄` is `𝔮` in the fibre,
`𝔭.Fiber` pins the base change along `R → κ(𝔭)`, and the `IsScalarTower R R_𝔭 S_𝔮` hypothesis
pins the inclusion `κ(𝔭) → κ(𝔮)` as `Localization.localRingHom` of `algebraMap R S`. (4) The
instantiation is not degenerate: for `R = ℤ`, `S = ℤ[x]/(x² - 2)`, `𝔭 = (5)` and `𝔮` the prime
over `5` all six hold, with `g = 1`, `S_𝔮/𝔭S_𝔮 = κ(𝔮) = 𝔽₂₅` and `F` a point; for `R = ℤ`,
`S = ℤ[x]`, `𝔭 = (5)` and `𝔮 = (5, x)` all six fail, `F = Spec 𝔽₅[x]` having no isolated point
and `S_𝔮/𝔭S_𝔮 = 𝔽₅[x]_{(x)}` having dimension `1`.

## References

* [StacksProject 00PK](https://stacks.math.columbia.edu/tag/00PK)
-/

@[expose] public section

namespace Algebra

/-- **Stacks 00PK.** Let `R → S` be of finite type, let `𝔮` be a prime of `S` lying over a prime
`𝔭` of `R`, let `F = Spec (S ⊗_R κ(𝔭))` be the fibre of `Spec S → Spec R` over `𝔭` and let `q̄`
be the point of `F` corresponding to `𝔮`. The following are equivalent: `q̄` is an isolated
point of `F`; `S_𝔮/𝔭S_𝔮` is finite over `κ(𝔭)`; some `g ∉ 𝔮` has `𝔮` as the only prime of
`D(g)` lying over `𝔭`; `dim_q̄ F = 0`; `q̄` is a closed point of `F` and `dim S_𝔮/𝔭S_𝔮 = 0`;
`κ(𝔮)/κ(𝔭)` is finite and `dim S_𝔮/𝔭S_𝔮 = 0`. -/
@[stacks 00PK "The fibre is the subspace `comap (algebraMap R S) ⁻¹' {𝔭}` of `Spec S` and `q̄`
is `𝔮` itself; `S_𝔮/𝔭S_𝔮` is `κ(𝔭) ⊗_R S_𝔮`, i.e. `𝔭.Fiber (Localization.AtPrime 𝔮)`;
`dim_q̄ F` is `topologicalKrullDimAt`. See the module docstring.",
  ega "0 14.1.10" "(1)⇔(4) for fibres",
  ega "II 6.2.1" "affine case",
  ega "II 6.2.2" "affine case, one prime"]
public theorem isOpen_singleton_fiber_tfae_of_finiteType {R S : Type*} [CommRing R] [CommRing S]
    [Algebra R S] [Algebra.FiniteType R S] (𝔭 : Ideal R) [𝔭.IsPrime] (𝔮 : Ideal S) [𝔮.IsPrime]
    [𝔮.LiesOver 𝔭] [Algebra (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)]
    [IsScalarTower R (Localization.AtPrime 𝔭) (Localization.AtPrime 𝔮)] :
    List.TFAE
      [IsOpen (X := PrimeSpectrum.comap (algebraMap R S) ⁻¹' {(⟨𝔭, ‹_›⟩ : PrimeSpectrum R)})
          {⟨⟨𝔮, ‹_›⟩, PrimeSpectrum.ext (𝔮.over_def 𝔭).symm⟩},
        Module.Finite 𝔭.ResidueField (𝔭.Fiber (Localization.AtPrime 𝔮)),
        ∃ g ∉ 𝔮, {q ∈ 𝔭.primesOver S | g ∉ q} = {𝔮},
        topologicalKrullDimAt
            ↥(PrimeSpectrum.comap (algebraMap R S) ⁻¹' {(⟨𝔭, ‹_›⟩ : PrimeSpectrum R)})
            ⟨⟨𝔮, ‹_›⟩, PrimeSpectrum.ext (𝔮.over_def 𝔭).symm⟩ = 0,
        IsClosed (X := PrimeSpectrum.comap (algebraMap R S) ⁻¹' {(⟨𝔭, ‹_›⟩ : PrimeSpectrum R)})
            {⟨⟨𝔮, ‹_›⟩, PrimeSpectrum.ext (𝔮.over_def 𝔭).symm⟩} ∧
          ringKrullDim (𝔭.Fiber (Localization.AtPrime 𝔮)) = 0,
        Module.Finite 𝔭.ResidueField 𝔮.ResidueField ∧
          ringKrullDim (𝔭.Fiber (Localization.AtPrime 𝔮)) = 0] :=
            by apply Stacks.QuasiFinite.IsolatedFibrePoint.solution

end Algebra

end

end

/-! ### Stacks 00PM

Stacks 00PM — a finite type ring map `R → S` is quasi-finite (00PL: quasi-finite at every prime
of `S`) iff every residue-field fibre `S ⊗_R κ(p)` is finite over `κ(p)` — is
`forall_quasiFiniteAt_iff_forall_finite_fiber` below, at the end of this file. Mathlib's tag on
`Algebra.quasiFinite_iff` only unfolds the definition of `Algebra.QuasiFinite`. -/

@[expose] public section
set_option linter.unusedVariables false
set_option linter.style.show false


open scoped TensorProduct

/-- **Four rings lemma.** Given a commutative square of rings
`R → S`, `R → R'`, `R' → S'`, `S → S'` (encoded by `Algebra` instances and the
appropriate `IsScalarTower` data) such that `R → S` is of finite type and the
canonical map `S ⊗_R R' → S'` is surjective, if `R → S` is quasi-finite at the
prime `q := q'.under S` of `S`, then `R' → S'` is quasi-finite at `q'`.

Proof sketch: base change `R → S` quasi-finite at `q'.under S` along
`R → R'`, using `Algebra.QuasiFiniteAt.baseChange` with the tensor product
`R' ⊗[R] S`, to obtain quasi-finiteness of `R' → R' ⊗[R] S` at a suitable
prime `P` lying over `q'.under S` and below `q'`. Then push along the
surjective `R'`-algebra map `R' ⊗[R] S →ₐ[R'] S'` using
`Algebra.QuasiFiniteAt.of_surjectiveOnStalks`. -/
@[stacks 00PN]
theorem four_rings_quasiFiniteAt
    (R S R' S' : Type*)
    [CommRing R] [CommRing S] [CommRing R'] [CommRing S']
    [Algebra R S] [Algebra R R'] [Algebra R' S'] [Algebra R S'] [Algebra S S']
    [IsScalarTower R R' S']
    [IsScalarTower R S S']
    [Algebra.FiniteType R S]
    (hsurj : Function.Surjective
      (Algebra.TensorProduct.productMap
        (IsScalarTower.toAlgHom R S S')
        (IsScalarTower.toAlgHom R R' S')))
    (q' : Ideal S') [q'.IsPrime]
    [Algebra.QuasiFiniteAt R (q'.under S)] :
    Algebra.QuasiFiniteAt R' q' := by
  -- The natural `R'`-algebra map `R' ⊗[R] S →ₐ[R'] S'`.
  set f' : R' ⊗[R] S →ₐ[R'] S' :=
    Algebra.TensorProduct.lift (Algebra.ofId R' S')
      (IsScalarTower.toAlgHom R S S') (fun _ _ => Commute.all _ _) with hf'_def
  -- `f'` is surjective.  We obtain this by transporting `hsurj` along the
  -- commutativity isomorphism `S ⊗[R] R' ≃ₐ[R] R' ⊗[R] S`.
  have hf'surj : Function.Surjective f' := by
    have h1 : (f'.restrictScalars R).comp
        (Algebra.TensorProduct.comm R S R').toAlgHom =
        Algebra.TensorProduct.productMap
          (IsScalarTower.toAlgHom R S S')
          (IsScalarTower.toAlgHom R R' S') := by
      refine Algebra.TensorProduct.ext' (fun s r' => ?_)
      simp [f', Algebra.ofId_apply, mul_comm]
    have hcomp : Function.Surjective
        ((f'.restrictScalars R).comp
          (Algebra.TensorProduct.comm R S R').toAlgHom) := by
      rw [h1]; exact hsurj
    have hcomm_surj : Function.Surjective
        (Algebra.TensorProduct.comm R S R') :=
      (Algebra.TensorProduct.comm R S R').surjective
    exact Function.Surjective.of_comp hcomp
  -- Let `P := q'.comap f'` be the corresponding prime of `R' ⊗[R] S`.
  let P : Ideal (R' ⊗[R] S) := q'.comap f'.toRingHom
  have hP : P.IsPrime := Ideal.comap_isPrime f'.toRingHom q'
  -- Step 1: `Algebra.QuasiFiniteAt R' P` follows from base change.
  -- We need `(q'.under S) = P.comap (Algebra.TensorProduct.includeRight : S →ₐ[R] R' ⊗[R] S)`.
  have hPunder : (q'.under S) =
      P.comap (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := S)).toRingHom := by
    -- Both sides equal `q'.comap (algebraMap S S')`.
    -- `P.comap includeRight = q'.comap (f' ∘ includeRight) = q'.comap (algebraMap S S')`.
    show q'.comap (algebraMap S S') =
      (q'.comap f'.toRingHom).comap
        (Algebra.TensorProduct.includeRight (R := R) (A := R') (B := S)).toRingHom
    rw [Ideal.comap_comap]
    congr 1
    ext s
    simp [f', Algebra.TensorProduct.includeRight_apply,
      IsScalarTower.toAlgHom_apply]
  have : Algebra.QuasiFiniteAt R' P :=
    Algebra.QuasiFiniteAt.baseChange (R := R) (S := S) (A := R')
      (p := q'.under S) (q := P) hPunder
  -- Step 2: Push along the surjective `R'`-algebra map `f' : R' ⊗[R] S →ₐ[R'] S'`
  -- using `of_surjectiveOnStalks`.
  have hf'_stalks : (f' : R' ⊗[R] S →ₐ[R'] S').SurjectiveOnStalks :=
    RingHom.surjectiveOnStalks_of_surjective hf'surj
  have hP_eq : P = q'.comap f'.toRingHom := rfl
  exact Algebra.QuasiFiniteAt.of_surjectiveOnStalks (R := R') (S := R' ⊗[R] S) (T := S')
    (p := P) f' hf'_stalks q' hP_eq

end

/-! ### Stacks 00PO

Stacks 00PO — a composition of quasi-finite ring maps is quasi-finite — is Mathlib's
`RingHom.QuasiFinite.comp`; Mathlib also carries the tag on the algebra-level
`Algebra.QuasiFinite.trans`. -/

@[expose] public section

-- The former @[stacks 00PO] theorem is the Mathlib theorem.
add_to_stacks 00PO RingHom.QuasiFinite.comp

end

/-!
# Quasi-finiteness is local

Stacks tag 077H (Lemma 10.122.6).

Let `R → S` be a finite type ring map, let `𝔮 ⊂ S` be a prime lying over
`𝔭 ⊂ R`, and let `f ∈ R` with `f ∉ 𝔭` and `g ∈ S` with `g ∉ 𝔮`. Form the
localization `R_f` of `R` away from `f` and the localization `S_{fg}` of `S` away
from `(algebraMap R S) f * g`, with the induced `R_f`-algebra structure on
`S_{fg}`. Writing `Q := 𝔮 S_{fg}` for the prime obtained by extending `𝔮` along
`S → S_{fg}`, the statement is that `R → S` is quasi-finite at `𝔮` if and only
if `R_f → S_{fg}` is quasi-finite at `Q`.

All rings here are commutative with unit, `κ(𝔭)` denotes the residue field of a
prime `𝔭`, and the *fibre ring* over `𝔭` is `κ(𝔭) ⊗_R S`. An `R`-algebra `S` is
quasi-finite when every fibre ring `κ(𝔭) ⊗_R S` is a finite-dimensional
`κ(𝔭)`-vector space, which is `Algebra.QuasiFinite R S`, whose field
`finite_fiber` asserts `Module.Finite (κ(𝔭)) (𝔭.Fiber S)` for every prime `𝔭`.
The class carries no finite-type hypothesis, so `Algebra.FiniteType R S` is
supplied separately below. For a prime `𝔮 ⊂ S`, the map `R → S` is quasi-finite
at `𝔮` when the localization `S_𝔮 = Localization.AtPrime 𝔮` is a quasi-finite
`R`-algebra, i.e. `Algebra.QuasiFiniteAt R 𝔮`.

Since `f` maps to a unit in `S_{fg}`, the universal property of `R_f` gives a
unique `R`-algebra map `R_f → S_{fg}` compatible with the maps from `R`; this is
encoded by the `Algebra Rf Sfg` and scalar-tower instances. The extended prime is
`𝔮 S_{fg} = Ideal.map (algebraMap S Sfg) 𝔮`; from `g ∉ 𝔮` and, via lying over,
`f ∉ 𝔮`, we get `f · g ∉ 𝔮`, so `𝔮` survives in `S_{fg}` and `𝔮 S_{fg}` is a
genuine prime. That consequence is taken below as the hypothesis `[Q.IsPrime]`.

The definitions `Algebra.QuasiFinite`, `Algebra.QuasiFiniteAt` and
`RingHom.QuasiFiniteAt` already exist in Mathlib and match these conventions, so
no new definitions are introduced here.
-/

@[expose] public section

/-- Stacks tag 077H (Lemma 10.122.6). For a finite type ring map `R → S`, a prime
`𝔮 ⊂ S` lying over `𝔭 ⊂ R`, an element `f ∈ R` with `f ∉ 𝔭` and an element
`g ∈ S` with `g ∉ 𝔮`, with `R_f = Localization.Away f` and
`S_{fg} = Localization.Away ((algebraMap R S f) * g)` and the induced
`R_f`-algebra structure on `S_{fg}`, the map `R → S` is quasi-finite at `𝔮` iff
`R_f → S_{fg}` is quasi-finite at `Q = 𝔮 S_{fg}`. -/
@[stacks 077H]
theorem quasiFiniteAt_localization_away_iff
    {R S Rf Sfg : Type*}
    [CommRing R] [CommRing S] [CommRing Rf] [CommRing Sfg]
    [Algebra R S] [Algebra R Rf] [Algebra R Sfg] [Algebra S Sfg] [Algebra Rf Sfg]
    [IsScalarTower R S Sfg] [IsScalarTower R Rf Sfg]
    (f : R) (g : S)
    [IsLocalization.Away f Rf]
    [IsLocalization.Away (algebraMap R S f * g) Sfg]
    [Algebra.FiniteType R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (hf : f ∉ p) (hg : g ∉ q)
    (Q : Ideal Sfg) (hQ : Q = Ideal.map (algebraMap S Sfg) q) [Q.IsPrime] :
    Algebra.QuasiFiniteAt R q ↔ Algebra.QuasiFiniteAt Rf Q := by
  have hfS : (algebraMap R S) f ∉ q := by
    intro h
    apply hf
    have : f ∈ Ideal.comap (algebraMap R S) q := h
    rwa [← Ideal.under_def, ← q.over_def p] at this
  have hprod : (algebraMap R S f * g) ∉ q := by
    intro h
    rcases (Ideal.IsPrime.mul_mem_iff_mem_or_mem ‹q.IsPrime›).mp h with h1 | h1
    · exact hfS h1
    · exact hg h1
  have hdisj : Disjoint ↑(Submonoid.powers (algebraMap R S f * g)) (↑q : Set S) := by
    rw [Set.disjoint_left]
    rintro a ⟨n, rfl⟩ ha
    exact hprod (‹q.IsPrime›.mem_of_pow_mem n ha)
  -- comap Q = q
  have hcomap : Ideal.comap (algebraMap S Sfg) Q = q := by
    rw [hQ]
    exact IsLocalization.under_map_of_isPrime_disjoint
      (Submonoid.powers (algebraMap R S f * g)) Sfg ‹q.IsPrime› hdisj
  -- Localization.AtPrime Q is a localization of S at q
  have hLoc : IsLocalization q.primeCompl (Localization.AtPrime Q) := by
    have h := IsLocalization.isLocalization_isLocalization_atPrime_isLocalization
      (Submonoid.powers (algebraMap R S f * g)) (S := Sfg) (Localization.AtPrime Q) Q
    have hsub : (Ideal.comap (algebraMap S Sfg) Q).primeCompl = q.primeCompl := by
      simp only [Ideal.primeCompl, hcomap]
    have h2 : IsLocalization (Ideal.comap (algebraMap S Sfg) Q).primeCompl
        (Localization.AtPrime Q) := h
    rw [hsub] at h2
    exact h2
  -- S-algebra equiv between the two localizations
  let : IsLocalization q.primeCompl (Localization.AtPrime Q) := hLoc
  have eS : Localization.AtPrime q ≃ₐ[S] Localization.AtPrime Q :=
    IsLocalization.algEquiv q.primeCompl _ _
  -- as R-algebra equiv
  have eR : Localization.AtPrime q ≃ₐ[R] Localization.AtPrime Q :=
    AlgEquiv.restrictScalars R eS
  -- QuasiFinite R Rf
  have hRf : Algebra.QuasiFinite R Rf := by
    have e : Localization.Away f ≃ₐ[R] Rf :=
      IsLocalization.algEquiv (Submonoid.powers f) _ _
    have hft0 : Algebra.FiniteType R (Localization.Away f) := inferInstance
    have : Algebra.FiniteType R Rf := Algebra.FiniteType.equiv hft0 e
    exact Algebra.QuasiFinite.of_isIntegral_of_finiteType (S := R) f
  -- now the chain
  unfold Algebra.QuasiFiniteAt
  rw [Algebra.QuasiFinite.iff_of_algEquiv eR]
  constructor
  · intro h
    exact Algebra.QuasiFinite.of_restrictScalars R Rf (Localization.AtPrime Q)
  · intro h
    exact Algebra.QuasiFinite.trans R Rf (Localization.AtPrime Q)

/-- Restatement of the theorem in terms of `RingHom.QuasiFiniteAt`, using the
ring homomorphisms `algebraMap R S` and `algebraMap Rf Sfg` directly. This is the
`(algebraMap R S).QuasiFiniteAt 𝔮 ↔ (algebraMap Rf Sfg).QuasiFiniteAt Q` form
mentioned in the problem statement. -/
theorem quasiFiniteAt_localization_away_iff'
    {R S Rf Sfg : Type*}
    [CommRing R] [CommRing S] [CommRing Rf] [CommRing Sfg]
    [Algebra R S] [Algebra R Rf] [Algebra R Sfg] [Algebra S Sfg] [Algebra Rf Sfg]
    [IsScalarTower R S Sfg] [IsScalarTower R Rf Sfg]
    (f : R) (g : S)
    [IsLocalization.Away f Rf]
    [IsLocalization.Away (algebraMap R S f * g) Sfg]
    [Algebra.FiniteType R S]
    (p : Ideal R) (q : Ideal S) [p.IsPrime] [q.IsPrime] [q.LiesOver p]
    (hf : f ∉ p) (hg : g ∉ q)
    (Q : Ideal Sfg) (hQ : Q = Ideal.map (algebraMap S Sfg) q) [Q.IsPrime] :
    (algebraMap R S).QuasiFiniteAt q ↔ (algebraMap Rf Sfg).QuasiFiniteAt Q := by
  have hRS : (algebraMap R S).toAlgebra = (inferInstance : Algebra R S) :=
    Algebra.algebra_ext _ _ (fun _ => rfl)
  have hRfSfg : (algebraMap Rf Sfg).toAlgebra = (inferInstance : Algebra Rf Sfg) :=
    Algebra.algebra_ext _ _ (fun _ => rfl)
  unfold RingHom.QuasiFiniteAt
  rw [hRS, hRfSfg]
  exact quasiFiniteAt_localization_away_iff (R := R) (S := S) (Rf := Rf) (Sfg := Sfg)
    f g p q hf hg Q hQ

end

/-!
# Permanence of quasi-finiteness

Stacks tag 0C6H (Lemma 10.122.10).

Let `A → B` and `B → C` be ring homomorphisms, giving a composite `A → C`, and
suppose that `A → C` is of finite type. Let `r` be a prime ideal of `C`, lying
over a prime `q` of `B` and over a prime `p` of `A`. If `A → C` is quasi-finite
at `r`, then `B → C` is quasi-finite at `r`.

The lying-over data does not appear explicitly below: `q` and `p` are determined
as the contractions of `r` along `B → C` and `A → C`, so the conclusion depends
only on the ring maps `A → B → C` and the prime `r`.

The three notions involved already exist in Mathlib. A ring homomorphism `R → S`
is of *finite type* when `S` is a finitely generated `R`-algebra, which is
`RingHom.FiniteType`. An `R`-algebra `S` is *quasi-finite* when for every prime
`P` of `R` the residue-field fibre `κ(P) ⊗_R S` is a finite `κ(P)`-module, which
is `Algebra.QuasiFinite R S`. For a ring map `R → S` and a prime `q` of `S`, the
map is *quasi-finite at* `q` when the localization `S_q` is a quasi-finite
`R`-algebra, i.e. `Algebra.QuasiFiniteAt R q`; the ring-map flavoured version
`RingHom.QuasiFiniteAt f q` equips `S` with the `R`-algebra structure coming from
`f` and then asks for `Algebra.QuasiFiniteAt R q`.
-/

@[expose] public section

open TensorProduct in
/-- The canonical `D`-linear "change of base ring" map
`D ⊗[A] N → D ⊗[B] N` coming from a scalar tower `A → B`. -/
@[ega "0 20.5.3" "partial"]
noncomputable def changeBaseTensorMap (A B D N : Type*)
    [CommRing A] [CommRing B] [Algebra A B]
    [CommRing D] [Algebra A D] [Algebra B D] [IsScalarTower A B D]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] :
    D ⊗[A] N →ₗ[D] D ⊗[B] N :=
  TensorProduct.AlgebraTensorModule.lift
    { toFun := fun d =>
        { toFun := fun n => d ⊗ₜ[B] n
          map_add' := by intro x y; simp [tmul_add]
          map_smul' := by intro a n; simp }
      map_add' := by intro x y; ext n; simp [add_tmul]
      map_smul' := by intro d x; ext n; simp [smul_tmul', smul_eq_mul] }

open TensorProduct in
/-- The change-of-base-ring map is surjective. -/
theorem changeBaseTensorMap_surjective (A B D N : Type*)
    [CommRing A] [CommRing B] [Algebra A B]
    [CommRing D] [Algebra A D] [Algebra B D] [IsScalarTower A B D]
    [AddCommGroup N] [Module A N] [Module B N] [IsScalarTower A B N] :
    Function.Surjective (changeBaseTensorMap A B D N) := by
  rw [← LinearMap.range_eq_top, eq_top_iff]
  rintro x -
  induction x using TensorProduct.inductionOn with
  | tmul m n => exact ⟨m ⊗ₜ n, by simp [changeBaseTensorMap]⟩
  | add x y hx hy => exact add_mem hx hy

open scoped TensorProduct
/-- Permanence of quasi-finiteness (Stacks tag 0C6H): if the composite of
`f : A →+* B` and `g : B →+* C` is quasi-finite at a prime `r` of `C`, then `g`
itself is quasi-finite at `r`. -/
@[stacks 0C6H]
theorem quasiFiniteAt_of_comp_quasiFiniteAt
    {A B C : Type*} [CommRing A] [CommRing B] [CommRing C]
    (f : A →+* B) (g : B →+* C)
    (r : Ideal C) [r.IsPrime]
    (h : (g.comp f).QuasiFiniteAt r) :
    g.QuasiFiniteAt r := by
  -- Set up the three algebra structures coming from the ring maps, and the
  -- scalar tower `A → B → C`.
  let algB : Algebra B C := g.toAlgebra
  let algA : Algebra A C := (g.comp f).toAlgebra
  let algAB : Algebra A B := f.toAlgebra
  have : IsScalarTower A B C := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  -- `g.QuasiFiniteAt r` unfolds to `Algebra.QuasiFinite B (Localization.AtPrime r)`.
  refine { finite_fiber := ?_ }
  intro Q hQ
  set S := Localization.AtPrime r with hS
  -- the prime `P` of `A` lying under `Q`.
  set P : Ideal A := Q.comap (algebraMap A B) with hP
  have : P.IsPrime := hP ▸ Ideal.IsPrime.comap _
  -- the induced residue-field algebra `κ(P) → κ(Q)`, and its scalar tower.
  let : Algebra P.ResidueField Q.ResidueField :=
    (Ideal.ResidueField.map P Q (algebraMap A B) hP).toAlgebra
  have : IsScalarTower A P.ResidueField Q.ResidueField := by
    apply IsScalarTower.of_algebraMap_eq
    intro x
    change algebraMap A Q.ResidueField x
      = (Ideal.ResidueField.map P Q (algebraMap A B) hP) (algebraMap A P.ResidueField x)
    rw [Ideal.ResidueField.map_algebraMap,
      IsScalarTower.algebraMap_apply A B Q.ResidueField]
  -- From the hypothesis, the fibre `κ(P) ⊗[A] S` is a finite `κ(P)`-module.
  have hfin : Module.Finite P.ResidueField (P.Fiber S) := h.finite_fiber P
  -- Base change to `κ(Q)`: `κ(Q) ⊗[κ(P)] (κ(P) ⊗[A] S)` is finite over `κ(Q)`.
  have : Module.Finite Q.ResidueField
      (Q.ResidueField ⊗[P.ResidueField] (P.ResidueField ⊗[A] S)) :=
    Module.Finite.base_change P.ResidueField Q.ResidueField (P.ResidueField ⊗[A] S)
  -- Cancel the base change: `κ(Q) ⊗[κ(P)] (κ(P) ⊗[A] S) ≃ₗ[κ(Q)] κ(Q) ⊗[A] S`.
  have e := TensorProduct.AlgebraTensorModule.cancelBaseChange
    A P.ResidueField Q.ResidueField Q.ResidueField S
  have : Module.Finite Q.ResidueField (Q.ResidueField ⊗[A] S) :=
    Module.Finite.equiv e
  -- The fibre `κ(Q) ⊗[B] S = Q.Fiber S` is a `κ(Q)`-linear quotient of
  -- `κ(Q) ⊗[A] S`, hence finite over `κ(Q)`.
  exact Module.Finite.of_surjective (changeBaseTensorMap A B Q.ResidueField S)
    (changeBaseTensorMap_surjective A B Q.ResidueField S)

end

/-!
# Quasi-finiteness above a prime

Stacks tag 0H8X (Lemma 10.122.4), Section 10.122 "Quasi-finite maps".

Let `R → S` be a finite type ring map and let `p` be a prime ideal of `R`. Then
the following three conditions are equivalent:

1. `R → S` is quasi-finite at every prime `q` of `S` lying over `p`, i.e. with
   `q ∩ R = p`.
2. `S ⊗_R κ(p)` is a finite `κ(p)`-algebra, equivalently a finite-dimensional
   `κ(p)`-vector space.
3. `Spec(S ⊗_R κ(p))` is a finite set.

## Background

For a prime ideal `p ⊂ R`, the residue field is
`κ(p) := Frac(R/p) = R_p / p R_p`, the residue field of the local ring
`R_p = Localization.AtPrime p`; in Mathlib this is `Ideal.ResidueField p`, defined
as `IsLocalRing.ResidueField (Localization.AtPrime p)`. The fibre of
`Spec(S) → Spec(R)` over `p` is the `κ(p)`-algebra `S ⊗_R κ(p)`; in Mathlib this
is `Ideal.Fiber p S`, defined as `p.ResidueField ⊗[R] S`, whose prime spectrum is
the underlying topological fibre. A ring map `R → S` is of finite type when `S` is
a finitely generated `R`-algebra, i.e. `Algebra.FiniteType R S`.

For `R → S` of finite type and `q ⊂ S` prime lying over `p := q ∩ R`, the map is
quasi-finite at `q` when the corresponding point of the fibre is isolated,
equivalently when `S_q / p S_q` is a finite `κ(p)`-module (Stacks tag 00PK). In
Mathlib this is `Algebra.QuasiFiniteAt R q`, defined as
`Algebra.QuasiFinite R (Localization.AtPrime q)`: for every prime `P ⊂ R` the
`κ(P)`-module `κ(P) ⊗_R (S_q)` is finite. For a prime `q` over `p` the only
nonzero fibre is at `P = p`, which recovers the classical condition that
`S_q / p S_q` is finite over `κ(p)`.

The finite type hypothesis is essential: it makes `S ⊗_R κ(p)` a finite type
`κ(p)`-algebra, so that the equivalence reduces to the corresponding statement for
finite type algebras over a field (Stacks tag 0ALW, Lemma 10.61.3). Without it the
three conditions can fail to be equivalent.

The full equivalence `(1) ↔ (2) ↔ (3)` follows from the two biconditionals proved
below, since any two of the three biconditionals determine the third. The proof
reduces to Stacks tag 0ALW for finite type algebras over a field, with the
equivalent characterisations of quasi-finiteness at a prime from tags 00PL and
00PK.
-/

@[expose] public section

open scoped TensorProduct

/-- Transport `Algebra.QuasiFiniteAt` along an equality of primes. Pure plumbing:
`QuasiFiniteAt R q` is by definition `QuasiFinite R (Localization.AtPrime q)`, a function
of the ideal `q`, so equal primes carry the property between each other. -/
private lemma quasiFiniteAt_congr {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    {q q' : Ideal S} [q.IsPrime] [q'.IsPrime] (h : q = q')
    (H : Algebra.QuasiFiniteAt R q') : Algebra.QuasiFiniteAt R q := by
  subst h
  exact H

/-- The fibre `p.Fiber S` of a finite type ring map is of finite type over `κ(p)`, by base
change. -/
private instance finiteType_fiber {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] :
    Algebra.FiniteType p.ResidueField (p.Fiber S) := by
  unfold Ideal.Fiber
  infer_instance

/-- The contraction to `S` of a prime of the fibre `p.Fiber S` lies over `p`. -/
private lemma liesOver_comap_includeRight {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    (p : Ideal R) [p.IsPrime] (q : Ideal (p.Fiber S)) [q.IsPrime] :
    (q.comap Algebra.TensorProduct.includeRight.toRingHom).LiesOver p :=
  ((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm ⟨q, ‹_›⟩).property.right

/-- The backward direction of Stacks tag 00PK: for a finite type ring map
`R → S`, a prime `p ⊂ R`, and a prime `q` of the fibre algebra
`A = p.Fiber S = κ(p) ⊗_R S`, if the point `q` is *isolated*, i.e. open, in
`Spec A`, then `R → S` is quasi-finite at the contracted prime `r = q ∩ S`. This
is the nontrivial local content of the equivalence between the two definitions of
quasi-finiteness at a prime: isolated in the fibre versus `S_r / p S_r` finite.

Openness of `{q}` in `Spec A` over the field `κ(p)`, which is Artinian, with `A`
of finite type over `κ(p)` by base change, is exactly `QuasiFiniteAt κ(p) q`, i.e.
`QuasiFinite κ(p) (A_q)` for `A_q = Localization.AtPrime q`. Over an Artinian base
that is in turn equivalent to `Module.Finite κ(p) (A_q)`.

To deduce `QuasiFiniteAt R r = QuasiFinite R (S_r)` one checks that
`κ(P) ⊗_R S_r = P.Fiber (S_r)` is a finite `κ(P)`-module for every prime `P ⊂ R`.
If `P ≠ p` then, since `r` lies over `p`, the ring `S_r` is a module over the
local ring `R_p` and `P.Fiber (S_r) = 0`, because `R → R_P` factors through `R_p`
and `p ⊄ P` forces a unit of `R_P` into `P·R_P`; a zero module is finite. If
`P = p` then `p.Fiber (S_r) = S_r / p S_r`, and there is a
`κ(p) = R_p/pR_p`-algebra isomorphism `Localization.AtPrime q ≃ S_r / p S_r`,
along which `Module.Finite κ(p) (A_q)` transports to
`Module.Finite κ(p) (p.Fiber S_r)`. -/
@[ega "II 6.2.1" "(a) ⇒ (b), affine case"]
private lemma quasiFiniteAt_of_fiber_isOpen_singleton
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber S)) (hq : q.IsPrime)
    (H : IsOpen ({⟨q, hq⟩} : Set (PrimeSpectrum (p.Fiber S)))) :
    Algebra.QuasiFiniteAt R (q.comap Algebra.TensorProduct.includeRight.toRingHom) := by
  have := hq
  -- Openness of `{q}` in `Spec A` over the Artinian base `κ(p)` (with `A` finite-type) is
  -- exactly `QuasiFiniteAt κ(p) q` by the local characterisation.
  have hk : Algebra.QuasiFiniteAt p.ResidueField q :=
    Algebra.QuasiFiniteAt.of_isOpen_singleton ⟨q, hq⟩ H
  set r : Ideal S := q.comap Algebra.TensorProduct.includeRight.toRingHom with hr
  have : r.IsPrime := Ideal.comap_isPrime _ _
  -- `r = q ∩ S` lies over `p` (its image in `Spec R` is `p`).
  have : r.LiesOver p := liesOver_comap_includeRight p q
  -- Descent: quasi-finiteness at `q` over the residue field `κ(p)` descends to
  -- quasi-finiteness at `r` over `R`.
  exact Algebra.QuasiFiniteAt.of_quasiFiniteAt_residueField p r q rfl

/-- Field case of Stacks tag 0ALW: a finite type algebra `A` over a field `k` is a finite
`k`-module if and only if `Spec A` is discrete. Both sides are equivalent to `A` having
Krull dimension zero. -/
theorem Algebra.FiniteType.module_finite_iff_discreteTopology {k A : Type*} [Field k]
    [CommRing A] [Algebra k A] [Algebra.FiniteType k A] :
    Module.Finite k A ↔ DiscreteTopology (PrimeSpectrum A) := by
  rw [Module.finite_iff_krullDimLE_zero k,
    PrimeSpectrum.discreteTopology_iff_finite_and_krullDimLE_zero]
  refine ⟨fun h => ?_, fun h => h.right⟩
  have : IsNoetherianRing A := Algebra.FiniteType.isNoetherianRing k _
  have : IsArtinianRing A := isArtinianRing_iff_isNoetherianRing_krullDimLE_zero.mpr ⟨‹_›, h⟩
  exact ⟨inferInstance, h⟩

/-- Pointwise form of Stacks tag 00PK: for a finite type ring map `R → S`, a prime `p ⊂ R`
and a prime `q` of the fibre `p.Fiber S`, `R → S` is quasi-finite at `q ∩ S` if and only if
`q` is an isolated point of `Spec (p.Fiber S)`. -/
theorem quasiFiniteAt_comap_includeRight_iff_isOpen_singleton
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime]
    (q : Ideal (p.Fiber S)) (hq : q.IsPrime) :
    Algebra.QuasiFiniteAt R (q.comap Algebra.TensorProduct.includeRight.toRingHom)
      ↔ IsOpen ({⟨q, hq⟩} : Set (PrimeSpectrum (p.Fiber S))) := by
  have := hq
  set r : Ideal S := q.comap Algebra.TensorProduct.includeRight.toRingHom with hr
  have : r.IsPrime := Ideal.comap_isPrime _ _
  -- forward: `QuasiFiniteAt R r` base-changes to `QuasiFiniteAt κ(p) q`, and over the
  -- Artinian base `κ(p)` (with `A` finite-type) the point `q` is then clopen, hence open.
  -- backward: the analytic kernel, isolated point ⟹ quasi-finite at `r = q ∩ S`.
  refine ⟨fun Hqf => ?_, quasiFiniteAt_of_fiber_isOpen_singleton p q hq⟩
  have : Algebra.QuasiFiniteAt R r := Hqf
  have : Algebra.QuasiFiniteAt p.ResidueField q := Algebra.QuasiFiniteAt.baseChange r q hr
  exact (Algebra.QuasiFiniteAt.isClopen_singleton (R := p.ResidueField) ⟨q, hq⟩).isOpen

/-- Stacks tag 0H8X, the equivalence of conditions (1) and (2): a finite type ring
map `R → S` is quasi-finite at every prime of `S` lying over a prime `p` of `R` if
and only if the fibre `S ⊗_R κ(p)` is a finite `κ(p)`-module. -/
@[stacks 0H8X, ega "II 6.2.2" "affine case, b)⇔c)"]
theorem quasiFiniteAt_forall_iff_finite_fiber
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] :
    -- (1) quasi-finite at every prime of S lying over p
    (∀ (q : Ideal S) [q.IsPrime], q.comap (algebraMap R S) = p →
        Algebra.QuasiFiniteAt R q)
    -- (2) the fibre S ⊗_R κ(p) is a finite κ(p)-module
    ↔ Module.Finite p.ResidueField (p.Fiber S) := by
  -- Identify primes of `S` over `p` with points of `Spec A` via the order iso
  -- `primesOverOrderIsoFiber`, then combine the pointwise bridge (Stacks 00PK) with the
  -- field case (Stacks 0ALW, `discrete ⟺ every point open`).
  rw [Algebra.FiniteType.module_finite_iff_discreteTopology,
    discreteTopology_iff_isOpen_singleton]
  constructor
  · -- (1) ⇒ every fibre point is open: each fibre point `q` contracts to a prime `q ∩ S`
    -- over `p`, where condition (1) gives quasi-finiteness; transport via the bridge.
    rintro H ⟨q, hq⟩
    have := hq
    exact (quasiFiniteAt_comap_includeRight_iff_isOpen_singleton p q hq).mp (H _
      (liesOver_comap_includeRight p q).over.symm)
  · -- every fibre point open ⇒ (1): a prime `q` over `p` is the contraction of its fibre
    -- point `q̄ = primesOverOrderIsoFiber ⟨q,…⟩`; openness of `{q̄}` plus the bridge gives
    -- quasi-finiteness at `q̄ ∩ S`, which equals `q`.
    intro H q hq hcomap
    have := hq
    have : q.LiesOver p := ⟨hcomap.symm⟩
    have hq'p : (((PrimeSpectrum.primesOverOrderIsoFiber R S p) ⟨q, ‹_›, ‹_›⟩).asIdeal).IsPrime :=
      ((PrimeSpectrum.primesOverOrderIsoFiber R S p) ⟨q, ‹_›, ‹_›⟩).isPrime
    have := hq'p
    have hqeq : q = (((PrimeSpectrum.primesOverOrderIsoFiber R S p) ⟨q, ‹_›, ‹_›⟩).asIdeal).comap
        Algebra.TensorProduct.includeRight.toRingHom :=
      congr($((PrimeSpectrum.primesOverOrderIsoFiber R S p).symm_apply_apply
        ⟨q, ‹_›, ‹_›⟩).val).symm
    exact quasiFiniteAt_congr hqeq
      ((quasiFiniteAt_comap_includeRight_iff_isOpen_singleton p _ hq'p).mpr (H ⟨_, hq'p⟩))

/-- Stacks tag 0H8X, the equivalence of conditions (2) and (3): for a finite type
ring map `R → S` and a prime `p` of `R`, the fibre `S ⊗_R κ(p)` is a finite
`κ(p)`-module if and only if its prime spectrum `Spec(S ⊗_R κ(p))` is finite. -/
@[stacks 0H8X, ega "II 6.2.2" "affine, one fibre a)⇔b)"]
theorem moduleFinite_fiber_iff_finite_primeSpectrum
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] (p : Ideal R) [p.IsPrime] :
    -- (2) the fibre S ⊗_R κ(p) is a finite κ(p)-module
    Module.Finite p.ResidueField (p.Fiber S)
    -- (3) Spec(S ⊗_R κ(p)) is a finite set
    ↔ Finite (PrimeSpectrum (p.Fiber S)) := by
  constructor
  · -- (2) ⇒ (3): a finite module over the field `κ(p)` is an Artinian ring, and an
    -- Artinian ring has a finite prime spectrum.
    intro h
    have : IsArtinianRing (p.Fiber S) := by
      rwa [← Module.finite_iff_isArtinianRing p.ResidueField]
    infer_instance
  · -- (3) ⇒ (2): finite spectrum means the fibre over the (unique) point of `Spec κ(p)`
    -- is finite, i.e. `QuasiFinite κ(p) A`; over the Artinian base `κ(p)` this is exactly
    -- `Module.Finite κ(p) A`.
    intro _
    rw [← Algebra.QuasiFinite.iff_of_isArtinianRing (R := p.ResidueField),
        Algebra.QuasiFinite.iff_finite_comap_preimage_singleton]
    exact fun _ => Set.toFinite _

/-- **Stacks 00PM.** Let `R → S` be a finite type ring map. Then `R → S` is quasi-finite, i.e.
quasi-finite at every prime `q` of `S` (Stacks 00PL), if and only if for every prime `p` of `R`
the fibre ring `S ⊗_R κ(p)` is finite over `κ(p)`. -/
@[stacks 00PM "Quasi-finiteness at `q` is `Algebra.QuasiFiniteAt R q`, which for a finite type
map is the 00PK condition `q̄` isolated in its fibre
(`quasiFiniteAt_comap_includeRight_iff_isOpen_singleton`); `S ⊗_R κ(p)` is `p.Fiber S`.
The source's finite type ring map is `[Algebra.FiniteType R S]`, which is also the finite type
part of 00PL's definition. Proved from 0H8X fibre by fibre."]
theorem forall_quasiFiniteAt_iff_forall_finite_fiber
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    (∀ (q : Ideal S) [q.IsPrime], Algebra.QuasiFiniteAt R q) ↔
      ∀ (p : Ideal R) [p.IsPrime], Module.Finite p.ResidueField (p.Fiber S) := by
  refine ⟨fun H p _ ↦ (quasiFiniteAt_forall_iff_finite_fiber p).mp fun q _ _ ↦ H q,
    fun H q _ ↦ (quasiFiniteAt_forall_iff_finite_fiber (q.comap (algebraMap R S))).mpr
      (H _) q rfl⟩

/-- For a finite type ring map `R → S`, being quasi-finite at every prime of `S` is Mathlib's
`Algebra.QuasiFinite R S` (Stacks 00PM together with `Algebra.quasiFinite_iff`). -/
theorem forall_quasiFiniteAt_iff_quasiFinite
    {R S : Type*} [CommRing R] [CommRing S] [Algebra R S] [Algebra.FiniteType R S] :
    (∀ (q : Ideal S) [q.IsPrime], Algebra.QuasiFiniteAt R q) ↔ Algebra.QuasiFinite R S :=
  forall_quasiFiniteAt_iff_forall_finite_fiber.trans (Algebra.quasiFinite_iff R S).symm

end

/-! ### Stacks 00PL

Definition 00PL: let `R → S` be of finite type and `𝔮` a prime of `S`. (1) `R → S` is
*quasi-finite at `𝔮`* when the equivalent conditions of Lemma 00PK hold, the first of which is
that `𝔮` is an isolated point of its fibre. (2) A ring map `A → B` is *quasi-finite* when it is
of finite type and quasi-finite at every prime of `B`.

Mathlib's `Algebra.QuasiFinite R S`, which carries the tag upstream, asks instead that every
fibre `κ(𝔭) ⊗_R S` be finite over `κ(𝔭)` and does not ask that `S` be of finite type over `R`;
Mathlib's `Algebra.QuasiFiniteAt R 𝔮` asks that `S_𝔮` be quasi-finite over `R`, which is the
source's notion (1) only for `S` of finite type. Here are the source's two notions,
`Algebra.StacksQuasiFiniteAt` and `Algebra.StacksQuasiFinite`, and the bridges:
`Algebra.stacksQuasiFiniteAt_iff_quasiFiniteAt` (for `S` of finite type, (1) is
`Algebra.QuasiFiniteAt`), `Algebra.stacksQuasiFinite_iff` ((2) is finite type together with
Mathlib's `Algebra.QuasiFinite`) and `Algebra.stacksQuasiFinite_iff_forall_finite_fiber`
(Lemma 00PM in the source's own terms: for `S` of finite type, (2) holds iff every fibre
`S ⊗_R κ(𝔭)` is finite over `κ(𝔭)`).

The fibre is the subspace `comap (algebraMap R S) ⁻¹' {𝔭}` of `Spec S`, homeomorphic to
`Spec (κ(𝔭) ⊗_R S)` by `PrimeSpectrum.preimageHomeomorphFiber`, as in
`Algebra.isOpen_singleton_fiber_tfae_of_finiteType` (Lemma 00PK), whose condition (1) is the
defining condition of `Algebra.StacksQuasiFiniteAt`; the other five conditions of 00PK are
equivalent to it by that lemma.
-/

@[expose] public section

namespace Algebra

variable (R : Type*) {S : Type*} [CommRing R] [CommRing S] [Algebra R S]

/-- **Stacks 00PL (1).** For a ring map `R → S` (of finite type, in the source) and a prime `𝔮`
of `S`, `R → S` is quasi-finite at `𝔮` when `𝔮` is an isolated point of its fibre, the subspace
of `Spec S` of the primes lying over `𝔮 ∩ R`: this is condition (1) of Lemma 00PK, equivalent to
the other five by `Algebra.isOpen_singleton_fiber_tfae_of_finiteType`. -/
@[stacks 00PL "(1). The fibre is the subspace `comap (algebraMap R S) ⁻¹' {𝔮 ∩ R}` of `Spec S`
and the condition is 00PK (1), `𝔮` isolated in it. For `S` of finite type over `R` this is
Mathlib's `Algebra.QuasiFiniteAt R 𝔮`, by `Algebra.stacksQuasiFiniteAt_iff_quasiFiniteAt`."]
def StacksQuasiFiniteAt (q : PrimeSpectrum S) : Prop :=
  IsOpen (X := PrimeSpectrum.comap (algebraMap R S) ⁻¹' {q.comap (algebraMap R S)}) {⟨q, rfl⟩}

variable (S) in
/-- **Stacks 00PL (2).** A ring map `R → S` is quasi-finite when it is of finite type and
quasi-finite at every prime of `S` in the sense of (1), `Algebra.StacksQuasiFiniteAt`. -/
@[stacks 00PL "(2). Equivalent to finite type together with Mathlib's `Algebra.QuasiFinite R S`
(which does not include finite type), by `Algebra.stacksQuasiFinite_iff`."]
def StacksQuasiFinite : Prop :=
  Algebra.FiniteType R S ∧ ∀ q : PrimeSpectrum S, StacksQuasiFiniteAt R q

/-- **Stacks 00PL (1), bridge.** For `R → S` of finite type, `R → S` is quasi-finite at `𝔮` in
the source's sense (`𝔮` isolated in its fibre) iff it is in Mathlib's sense
(`Algebra.QuasiFiniteAt`: `S_𝔮` is quasi-finite over `R`). -/
@[stacks 00PL "(1), for `R → S` of finite type, in Mathlib's language."]
theorem stacksQuasiFiniteAt_iff_quasiFiniteAt [Algebra.FiniteType R S] (q : PrimeSpectrum S) :
    StacksQuasiFiniteAt R q ↔ Algebra.QuasiFiniteAt R q.asIdeal :=
  (quasiFiniteAt_iff_isOpen_singleton_fiber q).symm

/-- **Stacks 00PL (2), bridge.** A ring map `R → S` is quasi-finite in the source's sense (of
finite type and quasi-finite at every prime) iff it is of finite type and quasi-finite in
Mathlib's sense (every fibre `κ(𝔭) ⊗_R S` finite over `κ(𝔭)`). -/
@[stacks 00PL "(2), in Mathlib's language: `Algebra.QuasiFinite` together with finite type."]
theorem stacksQuasiFinite_iff :
    StacksQuasiFinite R S ↔ Algebra.FiniteType R S ∧ Algebra.QuasiFinite R S := by
  refine ⟨fun ⟨hft, h⟩ ↦ ⟨hft, ?_⟩, fun ⟨hft, _⟩ ↦ ⟨hft, fun q ↦ ?_⟩⟩
  · -- Every point of each fibre is isolated, so each fibre is discrete; it is quasi-compact,
    -- being homeomorphic to the spectrum of `κ(𝔭) ⊗_R S`; hence each fibre is finite.
    rw [QuasiFinite.iff_finite_comap_preimage_singleton]
    intro x
    have : DiscreteTopology (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {x}) := by
      refine discreteTopology_iff_isOpen_singleton.mpr ?_
      rintro ⟨q, hq⟩
      obtain rfl : q.comap (algebraMap R S) = x := hq
      exact h q
    have : CompactSpace (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {x}) :=
      (PrimeSpectrum.preimageHomeomorphFiber R S x).symm.compactSpace
    have : Finite (PrimeSpectrum.comap (algebraMap R S) ⁻¹' {x}) := finite_of_compact_of_discrete
    exact Set.toFinite _
  · -- Quasi-finiteness passes to the localization `S_𝔮`, which is `Algebra.QuasiFiniteAt`.
    exact (stacksQuasiFiniteAt_iff_quasiFiniteAt R q).mpr inferInstance

variable (S) in
/-- **Stacks 00PM.** Let `R → S` be a ring map of finite type. Then `R → S` is quasi-finite (in
the source's sense, Definition 00PL (2)) iff for every prime `𝔭` of `R` the ring `S ⊗_R κ(𝔭)` is
finite over `κ(𝔭)`. -/
@[stacks 00PM "Stated for the source's notion `Algebra.StacksQuasiFinite`; the fibre
`S ⊗_R κ(𝔭)` is `𝔭.Fiber S = κ(𝔭) ⊗_R S`."]
theorem stacksQuasiFinite_iff_forall_finite_fiber [Algebra.FiniteType R S] :
    StacksQuasiFinite R S ↔
      ∀ (𝔭 : Ideal R) [𝔭.IsPrime], Module.Finite 𝔭.ResidueField (𝔭.Fiber S) := by
  rw [stacksQuasiFinite_iff, and_iff_right ‹_›, quasiFinite_iff]

end Algebra

end
