module

public import StacksFrontier.RingTheory.KrullDimension.BaseChange
public import StacksFrontier.RingTheory.RelativeDimension.Defs

@[expose] public section

/-!
# Relative dimension of a finite type ring map is invariant under base change

Let `R → S` be a ring map of finite type, let `R → R'` be any ring map, let `S' = R' ⊗_R S` and
let `f : Spec S' → Spec S` be the induced map on spectra. Then for every prime `𝔮'` of `S'`, the
relative dimension of `S'/R'` at `𝔮'` equals the relative dimension of `S/R` at `f(𝔮') = 𝔮' ∩ S`:

`dim_{𝔮'}(S'/R') = dim_{f(𝔮')}(S/R)`.

Hence `f⁻¹({𝔮 | dim_𝔮(S/R) ≤ n}) = {𝔮' | dim_{𝔮'}(S'/R') ≤ n}` for every `n`. The base change
is given by a commutative square of rings with `Algebra.IsPushout R S R' S'`, and `f` is
`PrimeSpectrum.comap (algebraMap S S')`.

## Main results

* `Stacks.RelativeDimension.BaseChange.solution` and
  `Algebra.IsPushout.relativeDimensionAt_comap_eq`: for every prime `𝔮'` of `S'`,
  `Algebra.relativeDimensionAt R (PrimeSpectrum.comap (algebraMap S S') 𝔮').asIdeal` equals
  `Algebra.relativeDimensionAt R' 𝔮'.asIdeal`.

## References

* [StacksProject 00QI](https://stacks.math.columbia.edu/tag/00QI)
* [StacksProject 00P4](https://stacks.math.columbia.edu/tag/00P4)
* [StacksProject 00QD](https://stacks.math.columbia.edu/tag/00QD)

## Tags

relative dimension, fibre, dimension of fibres, base change, finite type ring map
-/

@[expose] public section

namespace Stacks.RelativeDimension.BaseChange

attribute [local instance] Algebra.TensorProduct.rightAlgebra

section Fibre

variable (R S : Type*) [CommRing R] [CommRing S] [Algebra R S] (𝔭 : PrimeSpectrum R)

/-- The prime of `S` that `PrimeSpectrum.preimageHomeomorphFiber` places below a prime `q` of the
fibre ring `κ(𝔭) ⊗_R S` is the contraction of `q` along `S → κ(𝔭) ⊗_R S`. -/
private theorem coe_preimageHomeomorphFiber_symm_apply
    (q : PrimeSpectrum (𝔭.asIdeal.Fiber S)) :
    ((PrimeSpectrum.preimageHomeomorphFiber R S 𝔭).symm q : PrimeSpectrum S) =
      PrimeSpectrum.comap (algebraMap S (𝔭.asIdeal.Fiber S)) q :=
  rfl

/-- Every prime `𝔮` of `S` lying over `𝔭` is the contraction of a prime of the fibre ring
`κ(𝔭) ⊗_R S` along `S → κ(𝔭) ⊗_R S`. -/
private theorem exists_fiber_point (𝔮 : PrimeSpectrum S)
    (h : PrimeSpectrum.comap (algebraMap R S) 𝔮 = 𝔭) :
    ∃ q : PrimeSpectrum (𝔭.asIdeal.Fiber S),
      PrimeSpectrum.comap (algebraMap S (𝔭.asIdeal.Fiber S)) q = 𝔮 := by
  subst h
  refine ⟨PrimeSpectrum.preimageHomeomorphFiber R S _ ⟨𝔮, rfl⟩, ?_⟩
  rw [← coe_preimageHomeomorphFiber_symm_apply, Homeomorph.symm_apply_apply]

/-- The relative dimension `dim_𝔮(S/R)` is the local dimension of `Spec (κ(𝔭) ⊗_R S)` at any
prime of the fibre ring contracting to `𝔮`, where `𝔭 = 𝔮 ∩ R`. -/
private theorem relativeDimensionAt_eq_localKrullDim (𝔮 : PrimeSpectrum S)
    (h : PrimeSpectrum.comap (algebraMap R S) 𝔮 = 𝔭)
    (q : PrimeSpectrum (𝔭.asIdeal.Fiber S))
    (hq : PrimeSpectrum.comap (algebraMap S (𝔭.asIdeal.Fiber S)) q = 𝔮) :
    Algebra.relativeDimensionAt R 𝔮.asIdeal =
      TopologicalSpace.localKrullDim (PrimeSpectrum (𝔭.asIdeal.Fiber S)) q := by
  subst h
  have key : q = PrimeSpectrum.preimageHomeomorphFiber R S _ ⟨𝔮, rfl⟩ :=
    (Homeomorph.symm_apply_eq _).mp
      (Subtype.ext ((coe_preimageHomeomorphFiber_symm_apply R S _ q).trans hq))
  rw [Algebra.relativeDimensionAt,
    ← TopologicalSpace.topologicalKrullDimAt_eq_localKrullDim, key,
    ← topologicalKrullDimAt_eq_of_homeomorph]

end Fibre

/-- Let `S' = R' ⊗_R S` be a base change of a finite type `R`-algebra `S`, let `𝔭'` be a prime
of `R'` and let `𝔭 = 𝔭' ∩ R`. A prime `q'` of the fibre ring `κ(𝔭') ⊗_{R'} S'` lying over the
prime `𝔮'` of `S'` lies above a prime `q` of the fibre ring `κ(𝔭) ⊗_R S` which lies over
`𝔮' ∩ S`, and `Spec (κ(𝔭) ⊗_R S)` has the same dimension at `q` as `Spec (κ(𝔭') ⊗_{R'} S')`
has at `q'`. -/
private theorem exists_fiber_point_localKrullDim_eq (R S R' S' : Type*) [CommRing R]
    [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R']
    [Algebra R' S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S']
    [IsScalarTower R S S'] [Algebra.IsPushout R S R' S'] [Algebra.FiniteType R S]
    (𝔭 : PrimeSpectrum R) (𝔭' : PrimeSpectrum R')
    (h𝔭 : 𝔭.asIdeal = 𝔭'.asIdeal.comap (algebraMap R R'))
    (𝔮' : PrimeSpectrum S') (q' : PrimeSpectrum (𝔭'.asIdeal.Fiber S'))
    (hq' : PrimeSpectrum.comap (algebraMap S' (𝔭'.asIdeal.Fiber S')) q' = 𝔮') :
    ∃ q : PrimeSpectrum (𝔭.asIdeal.Fiber S),
      PrimeSpectrum.comap (algebraMap S (𝔭.asIdeal.Fiber S)) q =
          PrimeSpectrum.comap (algebraMap S S') 𝔮' ∧
        TopologicalSpace.localKrullDim (PrimeSpectrum (𝔭.asIdeal.Fiber S)) q =
          TopologicalSpace.localKrullDim (PrimeSpectrum (𝔭'.asIdeal.Fiber S')) q' := by
  let _ : Algebra 𝔭.asIdeal.ResidueField 𝔭'.asIdeal.ResidueField :=
    (Ideal.ResidueField.map 𝔭.asIdeal 𝔭'.asIdeal (algebraMap R R') h𝔭).toAlgebra
  have : IsScalarTower R 𝔭.asIdeal.ResidueField 𝔭'.asIdeal.ResidueField :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [RingHom.algebraMap_toAlgebra, Ideal.ResidueField.map_algebraMap,
        ← IsScalarTower.algebraMap_apply]
  have : IsScalarTower R S' (𝔭'.asIdeal.Fiber S') :=
    IsScalarTower.of_algebraMap_eq fun r ↦ by
      rw [IsScalarTower.algebraMap_apply R R' (𝔭'.asIdeal.Fiber S'),
        IsScalarTower.algebraMap_apply R' S' (𝔭'.asIdeal.Fiber S'),
        ← IsScalarTower.algebraMap_apply R R' S']
  let _ : Algebra S (𝔭'.asIdeal.Fiber S') :=
    ((algebraMap S' (𝔭'.asIdeal.Fiber S')).comp (algebraMap S S')).toAlgebra
  have : IsScalarTower S S' (𝔭'.asIdeal.Fiber S') := IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower R S (𝔭'.asIdeal.Fiber S') :=
    IsScalarTower.of_algebraMap_eq fun x ↦ by
      rw [RingHom.algebraMap_toAlgebra, RingHom.comp_apply,
        ← IsScalarTower.algebraMap_apply R S S',
        ← IsScalarTower.algebraMap_apply R S' (𝔭'.asIdeal.Fiber S')]
  let ψ : 𝔭.asIdeal.Fiber S →ₐ[R] 𝔭'.asIdeal.Fiber S' :=
    Algebra.pushoutDesc (R := R) (S := 𝔭.asIdeal.ResidueField) (R' := S)
      (𝔭.asIdeal.Fiber S)
      (IsScalarTower.toAlgHom R 𝔭.asIdeal.ResidueField (𝔭'.asIdeal.Fiber S'))
      (IsScalarTower.toAlgHom R S (𝔭'.asIdeal.Fiber S')) fun _ _ ↦ mul_comm _ _
  have hψk : ∀ x, ψ (algebraMap 𝔭.asIdeal.ResidueField (𝔭.asIdeal.Fiber S) x) =
      algebraMap 𝔭.asIdeal.ResidueField (𝔭'.asIdeal.Fiber S') x :=
    fun x ↦ Algebra.pushoutDesc_left (𝔭.asIdeal.Fiber S) _ _ _ x
  have hψS : ∀ x, ψ (algebraMap S (𝔭.asIdeal.Fiber S) x) =
      algebraMap S (𝔭'.asIdeal.Fiber S') x :=
    fun x ↦ Algebra.pushoutDesc_right (𝔭.asIdeal.Fiber S) _ _ _ x
  let _ : Algebra (𝔭.asIdeal.Fiber S) (𝔭'.asIdeal.Fiber S') := ψ.toRingHom.toAlgebra
  have : IsScalarTower R (𝔭.asIdeal.Fiber S) (𝔭'.asIdeal.Fiber S') :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (ψ.commutes x).symm
  have : IsScalarTower 𝔭.asIdeal.ResidueField (𝔭.asIdeal.Fiber S) (𝔭'.asIdeal.Fiber S') :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (hψk x).symm
  have : IsScalarTower S (𝔭.asIdeal.Fiber S) (𝔭'.asIdeal.Fiber S') :=
    IsScalarTower.of_algebraMap_eq fun x ↦ (hψS x).symm
  have : Algebra.IsPushout R R' S S' := Algebra.IsPushout.symm inferInstance
  have hRK : Algebra.IsPushout R 𝔭'.asIdeal.ResidueField S (𝔭'.asIdeal.Fiber S') :=
    (Algebra.IsPushout.comp_iff R R' (T := 𝔭'.asIdeal.ResidueField) S S'
      (T' := 𝔭'.asIdeal.Fiber S')).mpr inferInstance
  have : Algebra.IsPushout 𝔭.asIdeal.ResidueField 𝔭'.asIdeal.ResidueField
      (𝔭.asIdeal.Fiber S) (𝔭'.asIdeal.Fiber S') :=
    (Algebra.IsPushout.comp_iff R 𝔭.asIdeal.ResidueField (T := 𝔭'.asIdeal.ResidueField) S
      (𝔭.asIdeal.Fiber S) (T' := 𝔭'.asIdeal.Fiber S')).mp hRK
  refine ⟨PrimeSpectrum.comap (algebraMap (𝔭.asIdeal.Fiber S) (𝔭'.asIdeal.Fiber S')) q', ?_,
    Algebra.IsPushout.localKrullDim_comap_eq 𝔭.asIdeal.ResidueField 𝔭'.asIdeal.ResidueField
      (𝔭.asIdeal.Fiber S) (𝔭'.asIdeal.Fiber S') q'⟩
  rw [← PrimeSpectrum.comap_comp_apply,
    ← IsScalarTower.algebraMap_eq S (𝔭.asIdeal.Fiber S) (𝔭'.asIdeal.Fiber S'),
    RingHom.algebraMap_toAlgebra, PrimeSpectrum.comap_comp_apply, hq']

/-- Let `R → S` be a finite type ring map, let `R → R'` be any ring map, let `S' = R' ⊗_R S` and
let `f : Spec S' → Spec S` be the induced map on spectra. Then relative dimension is invariant
under this base change: `dim_{𝔮'}(S'/R') = dim_{f(𝔮')}(S/R)` for every prime `𝔮'` of `S'`. -/
public theorem solution (R S R' S' : Type*) [CommRing R]
    [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R']
    [Algebra R' S'] [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S']
    [IsScalarTower R S S'] [Algebra.IsPushout R S R' S'] [Algebra.FiniteType R S]
    (𝔮' : PrimeSpectrum S') :
    Algebra.relativeDimensionAt R (PrimeSpectrum.comap (algebraMap S S') 𝔮').asIdeal =
      Algebra.relativeDimensionAt R' 𝔮'.asIdeal := by
  generalize h𝔭' : PrimeSpectrum.comap (algebraMap R' S') 𝔮' = 𝔭'
  have h𝔭 : PrimeSpectrum.comap (algebraMap R S) (PrimeSpectrum.comap (algebraMap S S') 𝔮') =
      PrimeSpectrum.comap (algebraMap R R') 𝔭' := by
    rw [← h𝔭', ← PrimeSpectrum.comap_comp_apply, ← PrimeSpectrum.comap_comp_apply,
      ← IsScalarTower.algebraMap_eq, ← IsScalarTower.algebraMap_eq]
  obtain ⟨q', hq'⟩ := exists_fiber_point R' S' 𝔭' 𝔮' h𝔭'
  obtain ⟨q, hq, hdim⟩ := exists_fiber_point_localKrullDim_eq R S R' S'
    (PrimeSpectrum.comap (algebraMap R R') 𝔭') 𝔭' rfl 𝔮' q' hq'
  rw [relativeDimensionAt_eq_localKrullDim R S _ _ h𝔭 q hq,
    relativeDimensionAt_eq_localKrullDim R' S' 𝔭' 𝔮' h𝔭' q' hq', hdim]

end Stacks.RelativeDimension.BaseChange

end

/-! ### Relative dimension under base change, for a pushout square -/

@[expose] public section

namespace Algebra.IsPushout

/-- Let `R → S` be a finite type ring map, let `R → R'` be any ring map, let `S' = R' ⊗_R S` and
let `f : Spec S' → Spec S` be the induced map on spectra. Then relative dimension is invariant
under this base change: `dim_{𝔮'}(S'/R') = dim_{f(𝔮')}(S/R)` for every prime `𝔮'` of `S'`. In
particular, for `n : ℕ`, the inverse image `f⁻¹({𝔮 | dim_𝔮(S/R) ≤ n})` is
`{𝔮' | dim_{𝔮'}(S'/R') ≤ n}`. -/
@[stacks 00QI "The source's equality of sublevel sets, for a bound `n ≥ 0`, is stated as the
pointwise equality `dim_{𝔮'}(S'/R') = dim_{f(𝔮')}(S/R)` of relative dimensions, to which it is
equivalent for all `n` at once; `S' = R' ⊗_R S` is the abstract `Algebra.IsPushout R S R' S'`
and `f` is `PrimeSpectrum.comap (algebraMap S S')`. See the module docstring."]
public theorem relativeDimensionAt_comap_eq (R S R' S' : Type*) [CommRing R]
    [CommRing S] [CommRing R'] [CommRing S'] [Algebra R S] [Algebra R R'] [Algebra R' S']
    [Algebra S S'] [Algebra R S'] [IsScalarTower R R' S'] [IsScalarTower R S S']
    [Algebra.IsPushout R S R' S'] [Algebra.FiniteType R S] (𝔮' : PrimeSpectrum S') :
    Algebra.relativeDimensionAt R (PrimeSpectrum.comap (algebraMap S S') 𝔮').asIdeal =
      Algebra.relativeDimensionAt R' 𝔮'.asIdeal :=
  Stacks.RelativeDimension.BaseChange.solution R S R' S' 𝔮'

end Algebra.IsPushout

end
