module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.FinitePresentationStalk
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociated
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.FibreStalk
public import StacksFrontier.AlgebraicGeometry.Morphisms.Support.FiniteType
public import StacksFrontier.AlgebraicGeometry.RingedSpace.Flat
public import StacksFrontier.RingTheory.EssentialFiniteness.Defs
public import StacksFrontier.RingTheory.Ideal.AssociatedPrime.Defs
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.LinearEquiv
public import StacksFrontier.Topology.Sheaves.Functors.Module.RingedSpace
public import StacksFrontier.Topology.Sheaves.RingedSpace.ModulePullbackStalkAdjunction
public import Mathlib.AlgebraicGeometry.Morphisms.FiniteType
public import Mathlib.RingTheory.TensorProduct.Quotient

/-!
# Weakly associated points of a flat tensor product over a general base

Let `f : X ⟶ S` be a morphism of schemes locally of finite type, let `F` be a finite-type
quasi-coherent `𝒪_X`-module which is flat over `S` at a point `x`, and let `G` be a
quasi-coherent `𝒪_S`-module. The point `x` is weakly associated to `F ⊗_{𝒪_X} f^*G` exactly
when `f x` is weakly associated to `G` and `x` lies in the relative assassin `Ass_{X/S}(F)`.

This file reduces that statement, at the level of the local rings at `x` and `f x`, to the
purely algebraic fibrewise description of the weakly associated primes of a flat tensor
product, which is Stacks tag 05II. That description is taken as an explicit hypothesis;
everything else is proved.

## Main definitions

* `Stacks.Divisors.WeaklyAssociatedPrimesTensorFormula` is the algebraic input: for an
  essentially-finite-type ring map `R → B` and a `B`-module `N` finite over `B` and flat over
  `R`, the weakly associated primes of `N ⊗_R M` are the contractions of the associated
  primes in the fibres over the weakly associated primes of `M`. This is Stacks tag 05II.
* `Stacks.Divisors.LocalWeaklyAssociatedTensorFormula` is the single-prime consequence of it
  that the proof actually uses, for a local homomorphism of local rings. It is the whole
  remaining obligation of the file.

## Main results

* `Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_localFormula` is the
  characterization, under the local hypothesis, and
  `Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_formula` is the same under
  the tag 05II hypothesis.
* `Stacks.Divisors.isWeaklyAssociatedPrime_iff_isAssociatedPrime_fiber_of_formula` is the
  local algebraic form it is reduced to, stated entirely in terms of opaque rings and
  modules so that no scheme instance takes part in its elaboration.
* `Stacks.Divisors.fiberFormula_iff` collapses the fibrewise description at the closed point:
  only the maximal ideal of the base can occur there.
* `Stacks.Divisors.mem_relativeAssassin_iff_isAssociatedPoint_asFiber` describes membership
  in the relative assassin by association on the one fibre through the point.
* `Stacks.Divisors.exists_tensorStalkLinearEquiv` and
  `Stacks.Divisors.exists_modulePullbackStalkLinearEquiv_of_eq` are the two stalk
  computations used: the stalk of a tensor product, and the stalk of a pullback at a point
  presented as an image.

## Implementation notes

The reduction is organized so that the mathematics happens in
`isWeaklyAssociatedPrime_iff_isAssociatedPrime_fiber_of_formula`, whose hypotheses are a
local homomorphism of local rings, a finite flat module, and three comparison equivalences.
Instantiating it is then pure bookkeeping, and no competing typeclass instance on a stalk can
interfere with the algebra, which is what goes wrong when such an assembly is carried out
directly on the scheme-level objects.

Both stalk computations are stated as `Nonempty` of a type of linear equivalences rather than
as data. This matters for the second one: the point `x` of `X` is the image `i z` of a point
of the fibre, and the comparison must be transported along that equality of points. Inside a
proof of a proposition the transport is a `subst` followed by the reduction of
`TopCat.Presheaf.stalkCongr` at a reflexivity witness; produced as data the same transport
does not typecheck at the ambient reducibility setting.

The module structure on a stalk that the associated- and weakly-associated-point predicates
are stated over is `AlgebraicGeometry.Scheme.Modules.moduleStalk`; the Tag 01CB stalk
isomorphism is stated over `Stacks.SheafOfModules.TensorStalkRingedSpace.stalkModule`, and the two
  are identified by
`Stacks.SheafOfModules.stalkModule_eq`.

## References

* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
* [Stacks Project, Tag 05II](https://stacks.math.columbia.edu/tag/05II)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct Opposite

universe u

namespace Stacks.Divisors

/-! ### Transport of the two prime conditions along a linear equivalence

The weakly associated case is `LinearEquiv.isWeaklyAssociatedPrime_iff`. -/

/-- Association of an ideal to a module only depends on the module up to a linear
equivalence. -/
alias isAssociatedPrimeStacks_congr := isAssociatedPrimeStacks_of_linearEquiv_iff

/-- Along a surjective ring map `R → S` association of an ideal of `S` to an `S`-module is
association of its contraction to the same module read over `R`: the two colon ideals
correspond under contraction, and a prime of `S` is recovered from its contraction. -/
alias isAssociatedPrimeStacks_comap_iff := isAssociatedPrimeStacks_comap_surjective_iff

/-! ### The fibre ring over a prime of the base -/

/-- A prime of the fibre ring `B ⊗[R] κ(𝔭)` contracts, through `B`, to `𝔭` itself. -/
theorem comap_comap_eq_of_tensorResidueField {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] (p : Ideal R) [p.IsPrime]
    (q : Ideal (B ⊗[R] p.ResidueField)) [q.IsPrime] :
    (q.comap (algebraMap B (B ⊗[R] p.ResidueField))).comap (algebraMap R B) = p := by
  let j : p.ResidueField →+* B ⊗[R] p.ResidueField :=
    Algebra.TensorProduct.includeRight.toRingHom
  have hj : q.comap j = ⊥ := Ideal.eq_bot_of_prime _
  have hc : (algebraMap B (B ⊗[R] p.ResidueField)).comp (algebraMap R B) =
      j.comp (algebraMap R p.ResidueField) := by
    ext r
    simp [j, Algebra.TensorProduct.tmul_one_eq_one_tmul]
  rw [Ideal.comap_comap, hc, ← Ideal.comap_comap, hj]
  exact p.ker_algebraMap_residueField

/-- For a maximal ideal `𝔭` of `R` the fibre ring `B ⊗[R] κ(𝔭)` is the quotient of `B` by the
ideal generated by `𝔭`. -/
theorem nonempty_quotientMapAlgEquivTensorResidueField {R B : Type*} [CommRing R] [CommRing B]
    [Algebra R B] (p : Ideal R) [p.IsMaximal] :
    Nonempty ((B ⧸ p.map (algebraMap R B)) ≃ₐ[B] (B ⊗[R] p.ResidueField)) :=
  ⟨(Algebra.TensorProduct.quotIdealMapEquivTensorQuot B p).trans
    (Algebra.TensorProduct.congr (AlgEquiv.refl : B ≃ₐ[B] B)
      (AlgEquiv.ofBijective (IsScalarTower.toAlgHom R (R ⧸ p) p.ResidueField)
        p.bijective_algebraMap_quotient_residueField))⟩

/-- For a maximal ideal `𝔭` of `R` the map `B → B ⊗[R] κ(𝔭)` is surjective. -/
private theorem surjective_algebraMap_tensorResidueField {R : Type*} (B : Type*) [CommRing R]
    [CommRing B] [Algebra R B] (p : Ideal R) [p.IsMaximal] :
    Function.Surjective (algebraMap B (B ⊗[R] p.ResidueField)) :=
  Algebra.TensorProduct.includeLeft_surjective B B p.algebraMap_residueField_surjective

/-- **The local form of the fibrewise formula.** For a local homomorphism of local rings
`R → B`, the fibrewise description of the weakly associated primes of `N ⊗[R] M`, evaluated
at the maximal ideal of `B`, collapses to the conjunction of weak association of the maximal
ideal of `R` to `M` and association of the maximal ideal of `B` to the fibre module over the
closed point of `R`.

Only one prime of `R` can occur: a prime of a fibre ring contracting to the maximal ideal of
`B` contracts to the maximal ideal of `R`. -/
theorem fiberFormula_iff {R B : Type*} [CommRing R] [CommRing B]
    [IsLocalRing R] [IsLocalRing B] [Algebra R B] [IsLocalHom (algebraMap R B)]
    {M N : Type*} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module B N] :
    (∃ p ∈ weaklyAssociatedPrimes R M, ∃ hp : p.IsPrime,
      letI : p.IsPrime := hp
      ∃ q ∈ assStacks (B ⊗[R] p.ResidueField)
        ((B ⊗[R] p.ResidueField) ⊗[B] N),
        IsLocalRing.maximalIdeal B = q.comap (algebraMap B (B ⊗[R] p.ResidueField))) ↔
    IsWeaklyAssociatedPrime R M (IsLocalRing.maximalIdeal R) ∧
      IsAssociatedPrimeStacks B
        ((B ⊗[R] (IsLocalRing.maximalIdeal R).ResidueField) ⊗[B] N)
        (IsLocalRing.maximalIdeal B) := by
  set p₀ := IsLocalRing.maximalIdeal R with hp₀
  have hs := surjective_algebraMap_tensorResidueField B p₀
  constructor
  · rintro ⟨p, hp, hp', q, hq, heq⟩
    have := hp'
    have := hq.1
    have hpp : p = p₀ := by
      rw [← comap_comap_eq_of_tensorResidueField p q, ← heq, IsLocalRing.maximalIdeal_comap]
    subst hpp
    exact ⟨hp, heq ▸ (isAssociatedPrimeStacks_comap_iff hs q).mp hq⟩
  · rintro ⟨hp, hq⟩
    set q := (IsLocalRing.maximalIdeal B).map (algebraMap B (B ⊗[R] p₀.ResidueField)) with hq'
    obtain ⟨e⟩ := nonempty_quotientMapAlgEquivTensorResidueField (B := B) p₀
    have hk : RingHom.ker (algebraMap B (B ⊗[R] p₀.ResidueField)) ≤
        IsLocalRing.maximalIdeal B := by
      intro b hb
      have hz : Ideal.Quotient.mk (p₀.map (algebraMap R B)) b = 0 := by
        refine e.injective ?_
        change e (algebraMap B _ b) = e 0
        rw [e.commutes, map_zero]
        exact hb
      exact Ideal.map_le_iff_le_comap.mpr (IsLocalRing.maximalIdeal_comap (algebraMap R B)).ge
        (Ideal.Quotient.eq_zero_iff_mem.mp hz)
    have heq : q.comap (algebraMap B (B ⊗[R] p₀.ResidueField)) =
        IsLocalRing.maximalIdeal B := by
      rw [hq', Ideal.comap_map_of_surjective _ hs]
      exact sup_eq_left.mpr hk
    exact ⟨p₀, hp, inferInstance, q,
      (isAssociatedPrimeStacks_comap_iff hs q).mpr (heq.symm ▸ hq), heq.symm⟩

/-! ### The algebraic input: Stacks tag 05II -/

/-- **Stacks tag 05II**, at one universe and for a module that is finite rather than a
localization of a finite one: for an essentially-finite-type ring map `R → B` and a
`B`-module `N` which is finite over `B` and flat over `R`, the weakly associated primes of
`N ⊗[R] M` are exactly the contractions to `B` of the associated primes of the fibre modules
`(B ⊗[R] κ(𝔭)) ⊗[B] N` over the weakly associated primes `𝔭` of `M`.

This is the one statement this file does not prove. The Stacks project proves tag 05II by
translating the scheme-level tag 05IH into algebra, so it is not available as an input there;
its own proof of 05IH reduces to the finite-presentation case (tag 05IG) using the
étale-neighbourhood spreading-out of tag 05I5.

This library takes the other order, proving tag 05II in algebra first: it is
`weaklyAssociatedPrimes_tensorProduct_eq_fibrewise_assStacks_of_small'` of the namespace
`Stacks.WeaklyAssociatedPrimes`, and `Stacks.Divisors.weaklyAssociatedPrimesTensorFormula` in
`StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackFormula` is this
hypothesis deduced from it. So nothing downstream need assume it. -/
def WeaklyAssociatedPrimesTensorFormula : Prop :=
  ∀ (R B M N : Type u) [CommRing R] [CommRing B] [Algebra R B]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]
    [Module.Finite B N] [Module.Flat R N],
    IsEssentiallyOfFiniteType R B (algebraMap R B) →
    weaklyAssociatedPrimes B (N ⊗[R] M) =
      {q : Ideal B | ∃ p ∈ weaklyAssociatedPrimes R M, ∃ hp : p.IsPrime,
        letI : p.IsPrime := hp
        ∃ q' ∈ assStacks (B ⊗[R] p.ResidueField) ((B ⊗[R] p.ResidueField) ⊗[B] N),
          q = Ideal.comap (algebraMap B (B ⊗[R] p.ResidueField)) q'}

/-- The single prime of the formula of tag 05II that this file consumes: for a local
homomorphism of local rings `R → B` essentially of finite type and a `B`-module `N` finite
over `B` and flat over `R`, the maximal ideal of `B` is weakly associated to `N ⊗[R] M`
exactly when the maximal ideal of `R` is weakly associated to `M` and the maximal ideal of
`B` is associated to the fibre module over the closed point of `R`.

This is weaker than `Stacks.Divisors.WeaklyAssociatedPrimesTensorFormula`, which implies it
by `Stacks.Divisors.localWeaklyAssociatedTensorFormula_of_formula`, and it is the whole
remaining obligation of the file. -/
def LocalWeaklyAssociatedTensorFormula : Prop :=
  ∀ (R B M N : Type u) [CommRing R] [CommRing B] [IsLocalRing R] [IsLocalRing B]
    [Algebra R B] [IsLocalHom (algebraMap R B)]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]
    [Module.Finite B N] [Module.Flat R N],
    IsEssentiallyOfFiniteType R B (algebraMap R B) →
    (IsWeaklyAssociatedPrime B (N ⊗[R] M) (IsLocalRing.maximalIdeal B) ↔
      IsWeaklyAssociatedPrime R M (IsLocalRing.maximalIdeal R) ∧
        IsAssociatedPrimeStacks B
          ((B ⊗[R] (IsLocalRing.maximalIdeal R).ResidueField) ⊗[B] N)
          (IsLocalRing.maximalIdeal B))

/-- The formula of tag 05II implies its local form: read the set equality at the maximal
ideal of `B` and collapse the fibrewise description with
`Stacks.Divisors.fiberFormula_iff`. -/
theorem localWeaklyAssociatedTensorFormula_of_formula
    (h : WeaklyAssociatedPrimesTensorFormula.{u}) :
    LocalWeaklyAssociatedTensorFormula.{u} := by
  intro R B M N _ _ _ _ _ _ _ _ _ _ _ _ _ _ hess
  exact (Set.ext_iff.mp (h R B M N hess) (IsLocalRing.maximalIdeal B)).trans fiberFormula_iff

/-- **The whole mathematical content, over opaque rings and modules.** Let `R → B` be a local
homomorphism of local rings which is essentially of finite type, let `N` be a `B`-module
finite over `B` and flat over `R`, and let `M` be an `R`-module. Let `D` be a `B`-algebra
identified with the fibre ring `B ⊗[R] κ(𝔪_R)`, and let `T` and `FN` be modules identified
with `N ⊗[R] M` over `B` and with `D ⊗[B] N` over `D`. Then the maximal ideal of `B` is
weakly associated to `T` exactly when the maximal ideal of `R` is weakly associated to `M`
and the maximal ideal of `D` is associated to `FN`.

This is tag 05IH at a point, with the geometry stripped away: instantiating it at the local
rings and stalks of a morphism of schemes involves no further mathematics. -/
theorem isWeaklyAssociatedPrime_iff_isAssociatedPrime_fiber_of_formula
    (hformula : LocalWeaklyAssociatedTensorFormula.{u})
    {R B D M N T FN : Type u}
    [CommRing R] [CommRing B] [CommRing D]
    [IsLocalRing R] [IsLocalRing B] [IsLocalRing D]
    [Algebra R B] [IsLocalHom (algebraMap R B)] [Algebra B D]
    [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module B N] [Module R N] [IsScalarTower R B N]
    [Module.Finite B N] [Module.Flat R N]
    [AddCommGroup T] [Module B T]
    [AddCommGroup FN] [Module D FN] [Module B FN] [IsScalarTower B D FN]
    (hess : IsEssentiallyOfFiniteType R B (algebraMap R B))
    (eT : T ≃ₗ[B] N ⊗[R] M)
    (eD : (B ⊗[R] (IsLocalRing.maximalIdeal R).ResidueField) ≃ₐ[B] D)
    (eFN : FN ≃ₗ[D] D ⊗[B] N) :
    IsWeaklyAssociatedPrime B T (IsLocalRing.maximalIdeal B) ↔
      IsWeaklyAssociatedPrime R M (IsLocalRing.maximalIdeal R) ∧
        IsAssociatedPrimeStacks D FN (IsLocalRing.maximalIdeal D) := by
  have hsurj : Function.Surjective (algebraMap B D) := by
    intro d
    obtain ⟨c, hc⟩ := eD.surjective d
    obtain ⟨b, hb⟩ := surjective_algebraMap_tensorResidueField B _ c
    exact ⟨b, by rw [← eD.commutes b, hb, hc]⟩
  have : IsLocalHom (algebraMap B D) := IsLocalHom.of_surjective _ hsurj
  have hfiber : IsAssociatedPrimeStacks B
      ((B ⊗[R] (IsLocalRing.maximalIdeal R).ResidueField) ⊗[B] N)
      (IsLocalRing.maximalIdeal B) ↔
        IsAssociatedPrimeStacks D FN (IsLocalRing.maximalIdeal D) := by
    rw [isAssociatedPrimeStacks_comap_iff hsurj (IsLocalRing.maximalIdeal D),
      IsLocalRing.maximalIdeal_comap]
    exact isAssociatedPrimeStacks_congr
      ((eD.toLinearEquiv.rTensor N).trans (eFN.restrictScalars B).symm) _
  rw [LinearEquiv.isWeaklyAssociatedPrime_iff eT]
  exact (hformula R B M N hess).trans (and_congr Iff.rfl hfiber)

/-! ### The two stalk computations -/

/-- **Stacks 01CB at Mathlib's stalk module structures.** The stalk of a tensor product of
two `𝒪_X`-modules is the tensor product of their stalks over the local ring. -/
theorem exists_tensorStalkLinearEquiv {X : Scheme.{u}} (F P : X.Modules) (x : X) :
    letI : Module (X.presheaf.stalk x)
        (TopCat.Presheaf.stalk (C := Ab.{u})
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (P))).val.presheaf x) :=
      PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
        (R := X.presheaf) ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (P))).val x
    Nonempty (
      (TopCat.Presheaf.stalk (C := Ab.{u})
          ((((Stacks.SheafOfModules.Tensor.sheafTensor ⟨((X.toRingedSpace)).presheaf,
            ((X.toRingedSpace)).IsSheaf⟩).obj (F)).obj (P))).val.presheaf x)
        ≃ₗ[X.presheaf.stalk x]
        TensorProduct (X.presheaf.stalk x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)
          (TopCat.Presheaf.stalk (C := Ab.{u}) P.val.presheaf x)) := by
  have e := Stacks.SheafOfModules.TensorStalkRingedSpace.tensorStalkIso X.toRingedSpace x F P
  -- The first two rewrites land on `F.val` and `P.val`. The third one, on the stalk of the
  -- tensor product, has to be instantiated by hand: that object's type names its sheaf of
  -- rings as `Stacks.SheafOfModules.Tensor.ringSheaf`, a semireducible definition, so the
  -- implicit ringed space of `stalkModule` cannot be read off it while matching. Naming the
  -- same object over `structureSheafRing`, which is `instance_reducible`, supplies it.
  rw [Stacks.SheafOfModules.stalkModule_eq, Stacks.SheafOfModules.stalkModule_eq,
    Stacks.SheafOfModules.stalkModule_eq (X := X.toRingedSpace)
      (F := ((((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj F).obj P) :
          _root_.SheafOfModules.{u} (structureSheafRing X.toRingedSpace)).val) (x := x)] at e
  exact ⟨e⟩

/-- **Stacks 0098 at a point presented as an image.** For `i : Y ⟶ X` and `z : Y` with
`i z = x`, the stalk at `z` of the pullback of an `𝒪_X`-module `F` is the base change of the
stalk of `F` at `x` along the stalk map composed with the comparison of the stalks at `x` and
at `i z`. -/
theorem exists_modulePullbackStalkLinearEquiv_of_eq {Y X : Scheme.{u}} (i : Y ⟶ X)
    (F : X.Modules) (z : Y) (x : X) (hx : i z = x) :
    letI : Algebra (X.presheaf.stalk x) (Y.presheaf.stalk z) :=
      ((i.stalkMap z).hom.comp
        (X.presheaf.stalkCongr (.of_eq hx.symm)).hom.hom).toAlgebra
    Nonempty (
      (TopCat.Presheaf.stalk (C := Ab.{u})
          ((Scheme.Modules.pullback i).obj F).val.presheaf z)
        ≃ₗ[Y.presheaf.stalk z]
        TensorProduct (X.presheaf.stalk x) (Y.presheaf.stalk z)
          (TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x)) := by
  subst hx
  dsimp only
  rw [TopCat.Presheaf.stalkCongr_hom, TopCat.Presheaf.stalkSpecializes_refl]
  exact ⟨Classical.choose
    (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      i.toLRSHom.toShHom F z)⟩

/-! ### The relative assassin at one point -/

/-- A point of `X` lies in the relative assassin `Ass_{X/S}(F)` exactly when the point it
determines on its own fibre is associated to the restriction of `F` to that fibre: a point of
`X` lies over only one point of `S`. -/
theorem mem_relativeAssassin_iff_isAssociatedPoint_asFiber {X S : Scheme.{u}} (f : X ⟶ S)
    (F : X.Modules) (x : X) :
    x ∈ relativeAssassin f F ↔
      IsAssociatedPoint ((Scheme.Modules.pullback (f.fiberι (f x))).obj F) (f.asFiber x) := by
  rw [mem_relativeAssassin]
  refine ⟨?_, fun h => ⟨f x, f.asFiber x, h, f.fiberι_asFiber x⟩⟩
  rintro ⟨s, w, hw, hx⟩
  obtain rfl : f x = s := by
    rw [← hx]
    exact Set.mem_preimage.mp ((f.range_fiberι s) ▸ Set.mem_range_self w)
  obtain rfl : w = f.asFiber x :=
    (f.fiberι (f x)).isEmbedding.injective (hx.trans (f.fiberι_asFiber x).symm)
  simpa only [mem_associatedPoints_iff] using hw

/-! ### Stacks tag 05IH -/

/-- **Stacks Project, Tag 05IH**, from the local form of the algebraic formula of tag 05II.
For `f : X ⟶ S` locally of finite type, `F` a finite-type quasi-coherent `𝒪_X`-module flat
over `S` at `x`, and `G` a quasi-coherent `𝒪_S`-module, the point `x` is weakly associated to
`F ⊗_{𝒪_X} f^*G` exactly when `f x` is weakly associated to `G` and `x` lies in the relative
assassin `Ass_{X/S}(F)`. -/
theorem isWeaklyAssociatedPoint_tensorPullback_iff_of_localFormula
    (hformula : LocalWeaklyAssociatedTensorFormula.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (G : S.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent]
    (x : X) (hF : IsFlatOverAt f.toLRSHom.toShHom F x) :
    IsWeaklyAssociatedPoint
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
            ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
          (((Scheme.Modules.pullback f).obj G)))) x ↔
      (IsWeaklyAssociatedPoint G (f x) ∧ x ∈ relativeAssassin f F) := by
  classical
  -- the two local rings and the local homomorphism between them
  let R := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : R →+* B := (f.stalkMap x).hom
  let : Algebra R B := φ.toAlgebra
  let : IsLocalHom φ := f.toLRSHom.prop x
  have : (IsLocalRing.maximalIdeal R).IsMaximal := IsLocalRing.maximalIdeal.isMaximal R
  -- the two stalks of the modules, and the module structures on them
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x)
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Finite B N := SheafOfModules.finite_stalk X.sheaf F x
  have hflat : Module.Flat R N := hF
  -- the stalk map is essentially of finite type
  have : Algebra.EssFiniteType R B := by
    rw [← RingHom.essFiniteType_algebraMap, RingHom.algebraMap_toAlgebra]
    exact LocallyOfFiniteType.stalkMap f x
  have hess : IsEssentiallyOfFiniteType R B (algebraMap R B) := by
    obtain ⟨T, T', hT, hLoc⟩ := (Algebra.essFiniteType_iff_exists_subalgebra R B).mp inferInstance
    exact ⟨T, inferInstance, (algebraMap R T).toAlgebra, hT, T',
      (algebraMap T B).toAlgebra, ⟨IsScalarTower.of_algebraMap_eq' rfl, hLoc⟩⟩
  -- the stalk of the tensor product is `N ⊗[R] M`
  let P := (Scheme.Modules.pullback f).obj G
  let tens := ((Stacks.SheafOfModules.Tensor.sheafTensor
    ⟨X.toLocallyRingedSpace.toRingedSpace.presheaf,
      X.toLocallyRingedSpace.toRingedSpace.IsSheaf⟩).obj F).obj P
  let T := TopCat.Presheaf.stalk (C := Ab.{u}) tens.val.presheaf x
  obtain ⟨eTensor⟩ := exists_tensorStalkLinearEquiv F P x
  let ePull : TopCat.Presheaf.stalk (C := Ab.{u}) P.val.presheaf x ≃ₗ[B]
      TensorProduct R B M := Classical.choose
    (RingedSpaceModuleAdjunction.exists_modulePullbackStalkLinearEquiv
      f.toLRSHom.toShHom G x)
  let : Module B T :=
    PresheafOfModules.instModuleCarrierStalkCommRingCatCarrierAbPresheafOpensCarrier
      (R := X.presheaf) tens.val x
  let eT : T ≃ₗ[B] N ⊗[R] M :=
    eTensor.trans ((ePull.lTensor N).trans
      (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B N M))
  -- the fibre through `x`, its local ring, and the identification with the fibre ring
  let i := f.fiberι (f x)
  let z := f.asFiber x
  let D := (f.fiber (f x)).presheaf.stalk z
  let ψ : B →+* D := (i.stalkMap z).hom.comp
    (X.presheaf.stalkCongr (.of_eq (f.fiberι_asFiber x).symm)).hom.hom
  let : Algebra B D := ψ.toAlgebra
  let eQ : (B ⧸ Ideal.map φ (IsLocalRing.maximalIdeal R)) ≃ₐ[B] D :=
    { __ := quotientStalkEquivFiberStalk f x
      commutes' := quotientStalkEquivFiberStalk_mk f x }
  obtain ⟨eK⟩ := nonempty_quotientMapAlgEquivTensorResidueField (B := B)
    (IsLocalRing.maximalIdeal R)
  let eD : (B ⊗[R] (IsLocalRing.maximalIdeal R).ResidueField) ≃ₐ[B] D := eK.symm.trans eQ
  -- the stalk of the restriction of `F` to that fibre is `D ⊗[B] N`
  let FN := TopCat.Presheaf.stalk (C := Ab.{u})
    ((Scheme.Modules.pullback i).obj F).val.presheaf z
  let : Module B FN := Module.compHom FN ψ
  have : IsScalarTower B D FN := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  obtain ⟨eFN⟩ :=
    exists_modulePullbackStalkLinearEquiv_of_eq i F z x (f.fiberι_asFiber x)
  -- assemble
  rw [mem_relativeAssassin_iff_isAssociatedPoint_asFiber]
  exact isWeaklyAssociatedPrime_iff_isAssociatedPrime_fiber_of_formula hformula
    (R := R) (B := B) (D := D) (M := M) (N := N) (T := T) (FN := FN) hess eT eD eFN

/-- **Stacks Project, Tag 05IH**, from the algebraic formula of tag 05II itself. -/
theorem isWeaklyAssociatedPoint_tensorPullback_iff_of_formula
    (hformula : WeaklyAssociatedPrimesTensorFormula.{u})
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFiniteType f]
    (F : X.Modules) (G : S.Modules)
    [F.IsQuasicoherent] [F.IsFiniteType] [G.IsQuasicoherent]
    (x : X) (hF : IsFlatOverAt f.toLRSHom.toShHom F x) :
    IsWeaklyAssociatedPoint
        ((((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X.toLocallyRingedSpace.toRingedSpace)).presheaf,
            ((X.toLocallyRingedSpace.toRingedSpace)).IsSheaf⟩).obj (F)).obj
          (((Scheme.Modules.pullback f).obj G)))) x ↔
      (IsWeaklyAssociatedPoint G (f x) ∧ x ∈ relativeAssassin f F) :=
  isWeaklyAssociatedPoint_tensorPullback_iff_of_localFormula
    (localWeaklyAssociatedTensorFormula_of_formula hformula) f F G x hF

end Stacks.Divisors

end
