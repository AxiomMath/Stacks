module

public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackNecessity
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreSetInclusion

/-!
# The fibre clause of tag 05IH under the hypotheses of the tag

Let `f : X ⟶ S` be a morphism of schemes locally of finite type, let `F` be a finite-type
quasi-coherent `𝒪_X`-module flat over `S` at a point `x`, and let `G` be an `𝒪_S`-module. Stacks
tag 05IH asserts

`x ∈ WeakAss_X(F ⊗_{𝒪_X} f^*G) ↔ f x ∈ WeakAss_S(G) ∧ x ∈ Ass_{X_{f x}}(F_{f x})`.

The second clause of the forward implication is already proved, in
`StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackNecessity`, but under
finite *presentation* of `f` and of `F`: the algebra it rests on is the local closed-fibre clause
`isAssociatedPrimeStacks_maximalIdeal_quotient_of_isWeaklyAssociatedPrime_tensorProduct`, in
`Stacks.WeaklyAssociatedPrimes`, whose proof runs the universal injectivity of tag 05DF and so
needs a finitely presented
module over an essentially-finitely-presented map. This file removes that restriction: the fibre
clause holds under the tag's own hypotheses.

What removes it is the chain of reductions of
`StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreSetInclusion`, which carries the
fibre clause of tag 05IG from the finite presentation case to a *finite* module over a ring map
*essentially of finite type*. Those are exactly the hypotheses the stalks of `f` and `F`
satisfy: the stalk map of a morphism locally of finite type is essentially of finite type, and
the stalk of a finite-type quasi-coherent module is finite over the local ring.

The one reformulation needed is of the conclusion. The chain produces weak association of the
maximal ideal of `𝒪_{X, x}` to `F_x ⊗_{𝒪_{S, f x}} κ(𝔪)`, and the fibre dictionary
`Stacks.Divisors.isAssociatedPoint_pullback_fiberι_iff` asks instead for *association* to the
closed fibre `F_x / 𝔪 F_x`. The two modules are identified by
`Stacks.WeaklyAssociatedPrimes.closedFibreTensorResidueFieldLinearEquiv`, and over the closed
fibre ring, which is Noetherian, weak association is association.

## Main results

* `isAssociatedPrimeStacks_closedFibre_of_isWeaklyAssociatedPrime_tensorProduct_of_finite`, in
  `Stacks.WeaklyAssociatedPrimes`, is the local closed-fibre clause for a finite module over a
  local homomorphism essentially of finite type.
* `Stacks.Divisors.mem_relativeAssassin_of_isWeaklyAssociatedPoint_tensorPullback_of_finiteType`
  is the fibre clause of the forward implication of tag 05IH, under the hypotheses of the tag.
  The tag in full is `Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finiteType`, in
  `StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackIff`.
* `Stacks.Divisors.mem_relativeAssassin_of_isWeaklyAssociatedPoint_of_finiteType` is that clause
  at `G = 𝒪_S`, stated with no tensor factor: a weakly associated point of a flat finite-type
  module lies in the relative assassin. It carries no tag, being a specialization of the clause
  above; it is stated separately because the identification of `F ⊗_{𝒪_X} f^*𝒪_S` with `F` is
  exactly what is unavailable on an algebraic space, so the tensor-free form is the one that
  transports to a chart diagram.

## Implementation notes

The geometric instantiation is the one of
`Stacks.Divisors.mem_relativeAssassin_of_isWeaklyAssociatedPoint_tensorPullback`, with the two
finite-presentation inputs replaced: `Module.Finite` of the stalk in place of
`Module.FinitePresentation`, and `IsEssentiallyOfFiniteType` of the stalk map in place of
`RingHom.EssentiallyOfFinitePresentation`. The finiteness of the closed fibre module over the
closed fibre ring, which that clause also asks for, is not needed here.

## References

* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct

universe u

namespace Stacks.WeaklyAssociatedPrimes

/-- **The fibre clause of [Stacks, Tag 05IG] in the local situation, for a finite module.** Let
`R → B` be a local homomorphism of local rings which is essentially of finite type, let `N` be a
`B`-module finite over `B` and flat over `R`, and let `M` be an `R`-module. If the maximal ideal
of `B` is weakly associated to `N ⊗_R M`, then it is an associated prime — in the strict sense of
[Stacks, Tag 00LA] — of the closed fibre `N / 𝔪_R N`.

This is the conclusion of
`isAssociatedPrimeStacks_maximalIdeal_quotient_of_isWeaklyAssociatedPrime_tensorProduct` of this
namespace with its finite presentation hypotheses weakened to finiteness and essential finite
type. The closed fibre module is `N ⊗_R κ(𝔪_R)` by
`closedFibreTensorResidueFieldLinearEquiv`, weak association of the maximal ideal of `B` to it is
`isWeaklyAssociatedPrime_tensorResidueField_of_finiteModule`, and over the closed fibre ring,
which is Noetherian, weak association is association. -/
theorem isAssociatedPrimeStacks_closedFibre_of_isWeaklyAssociatedPrime_tensorProduct_of_finite
    {R B : Type u} [CommRing R] [CommRing B] [IsLocalRing R] [IsLocalRing B]
    [Algebra R B] [IsLocalHom (algebraMap R B)]
    {N : Type u} [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]
    [Module.Finite B N] [Module.Flat R N]
    {M : Type u} [AddCommGroup M] [Module R M]
    [IsNoetherianRing (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R))]
    (hess : IsEssentiallyOfFiniteType R B (algebraMap R B))
    (hq : IsWeaklyAssociatedPrime B (N ⊗[R] M) (IsLocalRing.maximalIdeal B)) :
    IsAssociatedPrimeStacks B
      (N ⧸ (Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) • (⊤ : Submodule B N)))
      (IsLocalRing.maximalIdeal B) := by
  classical
  have hw0 := isWeaklyAssociatedPrime_tensorResidueField_of_finiteModule R B M N hess
    (IsLocalRing.maximalIdeal B) hq
  have hmc : (IsLocalRing.maximalIdeal B).comap (algebraMap R B) = IsLocalRing.maximalIdeal R :=
    IsLocalRing.maximalIdeal_comap (algebraMap R B)
  have : (IsLocalRing.maximalIdeal R).IsPrime := (IsLocalRing.maximalIdeal.isMaximal R).isPrime
  have : ((IsLocalRing.maximalIdeal B).comap (algebraMap R B)).IsPrime := Ideal.IsPrime.comap _
  have hw1 : IsWeaklyAssociatedPrime B
      (N ⊗[R] (IsLocalRing.maximalIdeal R).ResidueField) (IsLocalRing.maximalIdeal B) :=
    (isWeaklyAssociatedPrime_tensorResidueField_congr (N := N) hmc
      (IsLocalRing.maximalIdeal B)).mp hw0
  have hw : IsWeaklyAssociatedPrime B
      (N ⧸ (Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) • (⊤ : Submodule B N)))
      (IsLocalRing.maximalIdeal B) :=
    isWeaklyAssociatedPrime_of_linearEquiv' (closedFibreTensorResidueFieldLinearEquiv N) hw1
  have hle : Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) ≤
      IsLocalRing.maximalIdeal B := by
    rw [Ideal.map_le_iff_le_comap, IsLocalRing.maximalIdeal_comap]
  have hsurj : Function.Surjective (algebraMap B
      (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R))) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.Quotient.mk_surjective
  have hker : Ideal.comap (algebraMap B
        (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)))
      (⊥ : Ideal (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R))) =
        Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) := by
    rw [Ideal.Quotient.algebraMap_eq]
    exact Ideal.mk_ker
  have hcomap : (Ideal.map (algebraMap B
        (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)))
      (IsLocalRing.maximalIdeal B)).comap (algebraMap B
        (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R))) =
      IsLocalRing.maximalIdeal B := by
    rw [Ideal.comap_map_of_surjective _ hsurj, hker]
    exact sup_eq_left.mpr hle
  have h1 := (isWeaklyAssociatedPrime_comap_iff_of_surjective hsurj
    (Ideal.map (algebraMap B
      (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)))
      (IsLocalRing.maximalIdeal B))).mpr (hcomap ▸ hw)
  have h3 := (Stacks.Divisors.isAssociatedPrimeStacks_comap_iff hsurj _).mp
    ((isWeaklyAssociatedPrime_iff_isAssociatedPrimeStacks _).mp h1)
  rwa [hcomap] at h3

end Stacks.WeaklyAssociatedPrimes

namespace Stacks.Divisors

open Stacks.WeaklyAssociatedPrimes

/-- The fibre clause for a point whose stalk is weakly associated to `N ⊗ M`, for any module `M`
over the stalk of the base. -/
private theorem mem_relativeAssassin_of_isWeaklyAssociatedPrime_tensor_stalk
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (M : Type u) [AddCommGroup M] [Module (S.presheaf.stalk (f x)) M]
    (hT : letI : Algebra (S.presheaf.stalk (f x)) (X.presheaf.stalk x) :=
        (f.stalkMap x).hom.toAlgebra
      letI : Module (S.presheaf.stalk (f x))
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        Module.compHom _ (f.stalkMap x).hom
      haveI : IsScalarTower (S.presheaf.stalk (f x)) (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x) :=
        IsScalarTower.of_algebraMap_smul fun _ _ => rfl
      IsWeaklyAssociatedPrime (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x ⊗[S.presheaf.stalk (f x)] M)
        (IsLocalRing.maximalIdeal (X.presheaf.stalk x))) :
    x ∈ relativeAssassin f F := by
  classical
  let R := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : R →+* B := (f.stalkMap x).hom
  let : Algebra R B := φ.toAlgebra
  let : IsLocalHom φ := f.toLRSHom.prop x
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R N := hF
  have : Module.Finite B N := SheafOfModules.finite_stalk X.sheaf F x
  -- the stalk map is essentially of finite type
  have : Algebra.EssFiniteType R B := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have hess : IsEssentiallyOfFiniteType R B (algebraMap R B) := by
    obtain ⟨T, T', hT, hLoc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra R B).mp inferInstance
    exact ⟨T, inferInstance, (algebraMap R T).toAlgebra, hT, T',
      (algebraMap T B).toAlgebra, ⟨IsScalarTower.of_algebraMap_eq' rfl, hLoc⟩⟩
  -- the closed fibre ring is the local ring of the scheme-theoretic fibre, hence Noetherian
  have : IsNoetherianRing
      (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) := by
    have : IsLocallyNoetherian (f.fiber (f x)) := by
      have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
        change LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField (f x)))
        infer_instance
      exact LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
    rw [RingHom.algebraMap_toAlgebra]
    exact isNoetherianRing_of_ringEquiv _ (quotientStalkEquivFiberStalk f x).symm
  have key :=
    isAssociatedPrimeStacks_closedFibre_of_isWeaklyAssociatedPrime_tensorProduct_of_finite
      (R := R) (B := B) (N := N) (M := M) hess hT
  rw [mem_relativeAssassin_iff_isAssociatedPoint_asFiber, isAssociatedPoint_pullback_fiberι_iff]
  rwa [RingHom.algebraMap_toAlgebra] at key

/-- **Stacks Project, Tag 05IH, the fibre clause of the forward implication.** Let `f : X ⟶ S`
be locally of finite type, let `F` be a quasi-coherent `𝒪_X`-module of finite type which is flat
over `S` at `x`, and let `G` be an `𝒪_S`-module. If `x` is weakly associated to
`F ⊗_{𝒪_X} f^*G`, then `x` lies in the relative assassin `Ass_{X/S}(F)`, that is, the point `x`
determines on the fibre `X_{f x}` is associated to the restriction of `F` to that fibre.

No hypothesis beyond the tag's own is used. The variant
`Stacks.Divisors.mem_relativeAssassin_of_isWeaklyAssociatedPoint_tensorPullback` asks instead for
finite presentation of `f` and of `F`, which is what the universal injectivity of Stacks 05DF
needs; it is removed here by the reductions of
`StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.TensorFibreSetInclusion`, which carry the
fibre clause of Stacks 05IG from a finitely presented module to a finite one.

This is one clause of one direction. The full tag, both directions and all three conditions, is
`Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finiteType` in
`StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackIff`, which carries the
`@[stacks 05IH]` attribute. -/
theorem mem_relativeAssassin_of_isWeaklyAssociatedPoint_tensorPullback_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (G : S.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hx : IsWeaklyAssociatedPoint
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
          ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
            (((Scheme.Modules.pullback f).obj G)))) x) :
    x ∈ relativeAssassin f F := by
  let R := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : R →+* B := (f.stalkMap x).hom
  let : Algebra R B := φ.toAlgebra
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x)
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hT : IsWeaklyAssociatedPrime B (N ⊗[R] M) (IsLocalRing.maximalIdeal B) := by
    let P := (Scheme.Modules.pullback f).obj G
    let tens := ((Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toLocallyRingedSpace.toRingedSpace.presheaf,
        X.toLocallyRingedSpace.toRingedSpace.IsSheaf⟩).obj F).obj P
    obtain ⟨eTensor⟩ := exists_tensorStalkLinearEquiv F P x
    let ePull : TopCat.Presheaf.stalk (C := Ab.{u}) P.val.presheaf x ≃ₗ[B]
        TensorProduct R B M := Classical.choose
      (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
        f.toLRSHom.toShHom G x)
    let : Module B (TopCat.Presheaf.stalk (C := Ab.{u}) tens.val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) tens.val x
    exact (LinearEquiv.isWeaklyAssociatedPrime_iff (eTensor.trans ((ePull.lTensor N).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B N M))) _).mp hx
  exact mem_relativeAssassin_of_isWeaklyAssociatedPrime_tensor_stalk f F x hF M hT

/-- **Stacks Project, Tag 05IH, the forward implication.** Let `f : X ⟶ S` be locally of finite
type, let `F` be a quasi-coherent `𝒪_X`-module of finite type which is flat over `S` at `x`, and
let `G` be an `𝒪_S`-module. If `x` is weakly associated to `F ⊗_{𝒪_X} f^*G` and the maximal ideal
of `𝒪_{S, f x}` is finitely generated, then `f x` is weakly associated to `G` and `x` lies in the
relative assassin `Ass_{X/S}(F)`.

Only the base clause carries a hypothesis the tag does not have, namely finite generation of the
maximal ideal at `f x`; it replaces the prime avoidance the source runs after making the stalk
of `F` projective over the base by the étale-local structure theorem of Stacks 05ID.

The tag itself, both directions and with no such hypothesis, is
`Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finiteType` in
`StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackIff`, which carries the
`@[stacks 05IH]` attribute. This version is kept for the consumers that already have the finite
generation to hand. -/
theorem isWeaklyAssociatedPoint_and_mem_relativeAssassin_of_tensorPullback_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (G : S.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hfg : (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))).FG)
    (hx : IsWeaklyAssociatedPoint
      ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
          ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
            (((Scheme.Modules.pullback f).obj G)))) x) :
    IsWeaklyAssociatedPoint G (f x) ∧ x ∈ relativeAssassin f F :=
  ⟨isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_tensorPullback f F G x hF hfg hx,
    mem_relativeAssassin_of_isWeaklyAssociatedPoint_tensorPullback_of_finiteType f F G x hF hx⟩

/-- **A weakly associated point of a flat finite type module lies in the relative assassin.**
Let `f : X ⟶ S` be locally of finite type and let `F` be a quasi-coherent `𝒪_X`-module of finite
type which is flat over `S` at `x`. If `x` is weakly associated to `F` then `x` lies in
`Ass_{X/S}(F)`. -/
theorem mem_relativeAssassin_of_isWeaklyAssociatedPoint_of_finiteType
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) [F.IsQuasicoherent] [F.IsFiniteType] (x : X)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hx : IsWeaklyAssociatedPoint F x) :
    x ∈ relativeAssassin f F := by
  let R := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : R →+* B := (f.stalkMap x).hom
  let : Algebra R B := φ.toAlgebra
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have hT : IsWeaklyAssociatedPrime B (N ⊗[R] R) (IsLocalRing.maximalIdeal B) :=
    (LinearEquiv.isWeaklyAssociatedPrime_iff
      (TensorProduct.AlgebraTensorModule.rid R B N).symm _).mp hx
  exact mem_relativeAssassin_of_isWeaklyAssociatedPrime_tensor_stalk f F x hF R hT

end Stacks.Divisors

end
