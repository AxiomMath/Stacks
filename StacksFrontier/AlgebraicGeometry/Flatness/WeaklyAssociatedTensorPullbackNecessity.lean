module

public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.PullbackStalk
public import StacksFrontier.AlgebraicGeometry.Flatness.EssentialFinitePresentation
public import StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullback
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.FlatTensorProduct
public import StacksFrontier.RingTheory.Ideal.WeaklyAssociatedPrime.ProjectiveClosedFibre
public import StacksFrontier.Topology.Sheaves.RingedSpace.StalkFinitePresentation

/-!
# Necessity of the base and fibre conditions at a weakly associated point of a flat tensor
product

Let `f : X ⟶ S` be a morphism of schemes, let `F` be an `𝒪_X`-module flat over `S` at a point
`x`, and let `G` be an `𝒪_S`-module. Stacks tag 05IH asserts, for `f` locally of finite type
and `F` quasi-coherent of finite type, that

`x ∈ WeakAss_X(F ⊗_{𝒪_X} f^*G) ↔ f x ∈ WeakAss_S(G) ∧ x ∈ Ass_{X_{f x}}(F_{f x})`.

This file proves the implication from left to right, in two separate clauses, each under the
hypotheses that the algebra behind it needs.

It also proves the implication from right to left, and hence the biconditional, under one further
hypothesis: that the stalk `F_x` be projective as an `𝒪_{S, f x}`-module. That hypothesis is not
removable *on this route*, the one that goes through the stalk: the source removes it by passing
to an elementary étale neighbourhood square given by the structure theorem of Stacks 05ID, over
which the *global sections* of the pullback of `F` are projective, and transporting the three
conditions of the tag back along the étale maps by Stacks 05FP; an étale morphism does not
induce an isomorphism of Zariski stalks, so 05ID says nothing about `F_x` itself. The
projectivity is automatic when `F_x` is a finite module over `𝒪_{S, f x}`, since it is flat
there.

None of the results here is the tag. Tag 05IH in full — both directions, under the tag's own
hypotheses and no others — is
`Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finiteType` in
`StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackIff`, and that is
where the `@[stacks 05IH]` attribute lives. It takes the other route: the geometric reduction
`Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_localFormula` asks for the whole
algebraic equivalence at once, and that equivalence is now proved, being Stacks 05II. The
clauses below remain useful where their hypotheses are already present — the base clause in
particular asks no finiteness of `f` or of `F` at all, which the tag does.

What is added here, relative to that reduction, is that two halves of the algebraic equivalence
need not be assumed: they are
`Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_tensorProduct_of_fg` and the
closed-fibre clause
`isAssociatedPrimeStacks_maximalIdeal_quotient_of_isWeaklyAssociatedPrime_tensorProduct`
of the same namespace. Instantiating them at the stalks of `f` gives the two clauses below.

## Main results

* `Stacks.Divisors.isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_tensorPullback`: the base
  clause `x ∈ WeakAss_X(F ⊗ f^*G) → f x ∈ WeakAss_S(G)`, for a maximal ideal of `𝒪_{S, f x}`
  which is finitely generated.
* `Stacks.Divisors.mem_relativeAssassin_of_isWeaklyAssociatedPoint_tensorPullback`: the fibre
  clause `x ∈ WeakAss_X(F ⊗ f^*G) → x ∈ Ass_{X/S}(F)`, for `f` locally of finite presentation
  and `F` of finite presentation.
* `Stacks.Divisors.isWeaklyAssociatedPoint_and_mem_relativeAssassin_of_tensorPullback`: the two
  together, that is the forward implication of the tag under both restrictions.
* `Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_of_mem_relativeAssassin`: the converse
  implication `f x ∈ WeakAss_S(G) → x ∈ Ass_{X/S}(F) → x ∈ WeakAss_X(F ⊗ f^*G)`, for `f` locally
  of finite presentation, `F` of finite presentation, and `F_x` projective over `𝒪_{S, f x}`.
* `Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_projective_stalk`: the
  biconditional of the tag under the union of the hypotheses of the two directions.
* `Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finite_stalk`: the same with the
  projectivity discharged from finiteness of `F_x` over `𝒪_{S, f x}` by Stacks 00NZ.

## Implementation notes

The fibre condition `x ∈ Ass_{X_s}(F_s)` is spelled as membership in the relative assassin
`Stacks.Divisors.relativeAssassin` of tag 05AT, which at the fixed point `x` says exactly that
the point `x` determines on its own fibre is associated to the restriction of `F` to that fibre:
this is `Stacks.Divisors.mem_relativeAssassin_iff_isAssociatedPoint_asFiber`, and a
point of `X` lies over only one point of `S`.

Two restrictions of the hypotheses of the source appear, and both come from the algebra, not from
the reduction. The fibre clause rests on the universal injectivity of Stacks 05DF, which is
proved by a limit argument requiring finite *presentation* of both the stalk map and the stalk;
the source reaches the finite type case from it through the étale-local structure theorem of
Stacks 05I5, which is not available here. The base clause needs either finitely many weakly
associated primes of `G_{f x}` or a finitely generated maximal ideal of `𝒪_{S, f x}`, the latter
being taken here: without one of them the prime avoidance in the proof of the contraction
statement has nothing finite to run over.

The two restrictions are independent and the clauses are therefore stated separately, each
asking only for what it uses; in particular the base clause asks for no finiteness of `F` or `f`
at all, only flatness at the point.

## References

* [Stacks Project, Tag 05IH](https://stacks.math.columbia.edu/tag/05IH)
* [Stacks Project, Tag 05IG](https://stacks.math.columbia.edu/tag/05IG)
* [Stacks Project, Tag 05AT](https://stacks.math.columbia.edu/tag/05AT)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TensorProduct
open Stacks.WeaklyAssociatedPrimes

universe u

namespace Stacks.Divisors

/-- Weak association of the tensor with a pullback is weak association of the maximal ideal on
the tensor product of the stalks. -/
private theorem isWeaklyAssociatedPoint_tensorPullback_iff_tensorProduct
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (G : S.Modules) (x : X) :
    let R := S.presheaf.stalk (f x)
    let B := X.presheaf.stalk x
    let : Algebra R B := (f.stalkMap x).hom.toAlgebra
    let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
    let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x)
    let : Module R N := Module.compHom N (f.stalkMap x).hom
    have : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
    IsWeaklyAssociatedPoint
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toLocallyRingedSpace.toRingedSpace.presheaf,
            X.toLocallyRingedSpace.toRingedSpace.IsSheaf⟩).obj F).obj
          ((Scheme.Modules.pullback f).obj G)) x ↔
      IsWeaklyAssociatedPrime B (N ⊗[R] M) (IsLocalRing.maximalIdeal B) := by
  intro R B _ N M _ _
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
  exact LinearEquiv.isWeaklyAssociatedPrime_iff (eTensor.trans ((ePull.lTensor N).trans
    (TensorProduct.AlgebraTensorModule.cancelBaseChange R B B N M))) _

/-- The closed fibre ring `𝒪_{X, x} / 𝔪_{S, f x} 𝒪_{X, x}` of a morphism locally of finite
presentation is Noetherian, being the local ring of the locally Noetherian fibre `X_{f x}`. -/
private theorem isNoetherianRing_quotient_map_stalkMap {X S : Scheme.{u}} (f : X ⟶ S)
    [LocallyOfFinitePresentation f] (x : X) :
    IsNoetherianRing (X.presheaf.stalk x ⧸
      Ideal.map (f.stalkMap x).hom (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x)))) := by
  have : IsLocallyNoetherian (f.fiber (f x)) := by
    have : LocallyOfFiniteType (f.fiberToSpecResidueField (f x)) := by
      change LocallyOfFiniteType (Limits.pullback.snd f (S.fromSpecResidueField (f x)))
      infer_instance
    exact LocallyOfFiniteType.isLocallyNoetherian (f.fiberToSpecResidueField (f x))
  exact isNoetherianRing_of_ringEquiv _ (quotientStalkEquivFiberStalk f x).symm

/-- **Stacks Project, Tag 05IH, the base clause of the forward implication.** Let `f : X ⟶ S`
be a morphism of schemes, let `F` be an `𝒪_X`-module flat over `S` at `x` and let `G` be an
`𝒪_S`-module. If `x` is weakly associated to `F ⊗_{𝒪_X} f^*G` and the maximal ideal of
`𝒪_{S, f x}` is finitely generated, then `f x` is weakly associated to `G`.

The finite generation replaces the finiteness of `WeakAss(G_{f x})` in the prime avoidance of
the underlying contraction statement
`Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_tensorProduct_of_fg`; no finiteness
hypothesis on `f` or on `F` is used.

This asks nothing of `f` or `F`, and so is not comparable with the tag, which assumes both and
concludes more. Tag 05IH itself is
`Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finiteType` in
`StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackIff`. -/
theorem isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_tensorPullback
    {X S : Scheme.{u}} (f : X ⟶ S) (F : X.Modules) (G : S.Modules) (x : X)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hfg : (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))).FG)
    (hx : IsWeaklyAssociatedPoint
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toLocallyRingedSpace.toRingedSpace.presheaf,
          X.toLocallyRingedSpace.toRingedSpace.IsSheaf⟩).obj F).obj
        ((Scheme.Modules.pullback f).obj G)) x) :
    IsWeaklyAssociatedPoint G (f x) := by
  let R := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : R →+* B := (f.stalkMap x).hom
  let : Algebra R B := φ.toAlgebra
  let : IsLocalHom φ := f.toLRSHom.prop x
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x)
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R N := hF
  have hcomap : Ideal.comap (algebraMap R B) (IsLocalRing.maximalIdeal B) =
      IsLocalRing.maximalIdeal R := by
    rw [RingHom.algebraMap_toAlgebra]
    exact IsLocalRing.maximalIdeal_comap φ
  have hT : IsWeaklyAssociatedPrime B (N ⊗[R] M) (IsLocalRing.maximalIdeal B) :=
    (isWeaklyAssociatedPoint_tensorPullback_iff_tensorProduct f F G x).mp hx
  simpa only [hcomap] using
    Stacks.WeaklyAssociatedPrimes.isWeaklyAssociatedPrime_comap_tensorProduct_of_fg
      (R := R) (S := B) (N := N) (M := M) hT (hcomap ▸ hfg)

/-- **Stacks Project, Tag 05IH, the fibre clause of the forward implication.** Let `f : X ⟶ S`
be locally of finite presentation, let `F` be an `𝒪_X`-module of finite presentation which is
flat over `S` at `x`, and let `G` be an `𝒪_S`-module. If `x` is weakly associated to
`F ⊗_{𝒪_X} f^*G`, then `x` lies in the relative assassin `Ass_{X/S}(F)`, that is, the point `x`
determines on the fibre `X_{f x}` is associated to the restriction of `F` to that fibre.

Finite presentation of `f` and of `F` is what the underlying closed-fibre clause
`isAssociatedPrimeStacks_maximalIdeal_quotient_of_isWeaklyAssociatedPrime_tensorProduct`
asks for, through the universal injectivity of Stacks 05DF. The remaining hypotheses of that
clause are discharged here: the closed fibre ring `𝒪_{X, x} / 𝔪_{S, f x} 𝒪_{X, x}` is the local
ring of the scheme-theoretic fibre `X_{f x}`, which is locally Noetherian because it is locally
of finite type over the residue field at `f x`, and the closed fibre module is a quotient of the
stalk `F_x`, hence finite over it. -/
theorem mem_relativeAssassin_of_isWeaklyAssociatedPoint_tensorPullback
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) (G : S.Modules) [hFfp : F.IsFinitePresentation] (x : X)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hx : IsWeaklyAssociatedPoint
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toLocallyRingedSpace.toRingedSpace.presheaf,
          X.toLocallyRingedSpace.toRingedSpace.IsSheaf⟩).obj F).obj
        ((Scheme.Modules.pullback f).obj G)) x) :
    x ∈ relativeAssassin f F := by
  let R := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : R →+* B := (f.stalkMap x).hom
  let : Algebra R B := φ.toAlgebra
  let : IsLocalHom φ := f.toLRSHom.prop x
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x)
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R N := hF
  have : Module.FinitePresentation B N :=
    @Stacks.SheafOfModules.finitePresentation_stalk X.toRingedSpace F hFfp x
  have hess : (algebraMap R B).EssentiallyOfFinitePresentation := by
    rw [RingHom.algebraMap_toAlgebra]
    exact LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap f x
  have : IsNoetherianRing
      (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) :=
    isNoetherianRing_quotient_map_stalkMap f x
  have : Module.Finite (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R))
      (N ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) •
        (⊤ : Submodule B N)) := by
    have : Module.Finite B
        (N ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) •
          (⊤ : Submodule B N)) :=
      Module.Finite.of_surjective (Submodule.mkQ _) (Submodule.mkQ_surjective _)
    exact Module.Finite.of_restrictScalars_finite B _ _
  have hT : IsWeaklyAssociatedPrime B (N ⊗[R] M) (IsLocalRing.maximalIdeal B) :=
    (isWeaklyAssociatedPoint_tensorPullback_iff_tensorProduct f F G x).mp hx
  have key :=
    isAssociatedPrimeStacks_maximalIdeal_quotient_of_isWeaklyAssociatedPrime_tensorProduct
      (R := R) (S := B) (N := N) (M := M) hess hT
  rw [mem_relativeAssassin_iff_isAssociatedPoint_asFiber,
    isAssociatedPoint_pullback_fiberι_iff]
  rwa [RingHom.algebraMap_toAlgebra] at key

/-- **Stacks Project, Tag 05IH, the forward implication.** Let `f : X ⟶ S` be locally of finite
presentation, let `F` be an `𝒪_X`-module of finite presentation which is flat over `S` at `x`,
and let `G` be an `𝒪_S`-module. If `x` is weakly associated to `F ⊗_{𝒪_X} f^*G` and the maximal
ideal of `𝒪_{S, f x}` is finitely generated, then `f x` is weakly associated to `G` and `x` lies
in the relative assassin `Ass_{X/S}(F)`.

This is the conjunction of the two clauses above, under the union of their hypotheses. The
converse implication, granted that the stalk `F_x` is projective over `𝒪_{S, f x}`, is
`Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_of_mem_relativeAssassin` below. -/
theorem isWeaklyAssociatedPoint_and_mem_relativeAssassin_of_tensorPullback
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) (G : S.Modules) [F.IsFinitePresentation] (x : X)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hfg : (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))).FG)
    (hx : IsWeaklyAssociatedPoint
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toLocallyRingedSpace.toRingedSpace.presheaf,
          X.toLocallyRingedSpace.toRingedSpace.IsSheaf⟩).obj F).obj
        ((Scheme.Modules.pullback f).obj G)) x) :
    IsWeaklyAssociatedPoint G (f x) ∧ x ∈ relativeAssassin f F :=
  ⟨isWeaklyAssociatedPoint_of_isWeaklyAssociatedPoint_tensorPullback f F G x hF hfg hx,
    mem_relativeAssassin_of_isWeaklyAssociatedPoint_tensorPullback f F G x hF hx⟩

/-- **Stacks Project, Tag 05IH, the converse implication, granted projectivity of the stalk.**
Let `f : X ⟶ S` be locally of finite presentation, let `F` be an `𝒪_X`-module of finite
presentation which is flat over `S` at `x`, and let `G` be an `𝒪_S`-module. Assume the stalk
`F_x` is projective as an `𝒪_{S, f x}`-module. If `f x` is weakly associated to `G` and `x` lies
in the relative assassin `Ass_{X/S}(F)`, then `x` is weakly associated to `F ⊗_{𝒪_X} f^*G`.

Projectivity of the stalk is the hypothesis of the underlying algebraic converse
`isWeaklyAssociatedPrime_tensorProduct_of_isAssociatedPrimeStacks_closedFibre` of the namespace
`Stacks.WeaklyAssociatedPrimes`, and it is irreducible there: the argument of Stacks 05GP over an
auto-associated ring which produces the witness runs on a map of projective modules over the
quotient of the base by the annihilator of the witness downstairs. The source does not prove it
for the stalk; it installs projectivity by replacing `f`, `F`, `G` by their pullbacks along an
elementary étale neighbourhood square supplied by Stacks 05ID, over which the *global sections*
of the pullback of `F` are projective, and then transports all three conditions back along the
étale maps using Stacks 05FP. An étale morphism does not induce an isomorphism of Zariski stalks,
so 05ID gives no information about `F_x` itself.

Everything else that the algebraic converse asks for is discharged here. The maximality of the
fibre prime among the primes associated to the closed fibre module is automatic at a point: the
prime in question is the maximal ideal of the local ring `𝒪_{X, x}`, and a prime above it is
proper, hence equal to it. The remaining hypotheses — the closed fibre ring being Noetherian and
the stalk map being essentially of finite presentation — are discharged exactly as in
`Stacks.Divisors.mem_relativeAssassin_of_isWeaklyAssociatedPoint_tensorPullback`.

The converse implication with no projectivity hypothesis, as part of the full tag, is
`Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finiteType` in
`StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackIff`: it reaches the
tag through the algebraic formula of Stacks 05II rather than through the stalk, so the
projectivity that is irreducible on this route never arises. -/
theorem isWeaklyAssociatedPoint_tensorPullback_of_mem_relativeAssassin
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) (G : S.Modules) [hFfp : F.IsFinitePresentation] (x : X)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hproj : let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
      letI : Module (S.presheaf.stalk (f x)) N := Module.compHom N (f.stalkMap x).hom
      Module.Projective (S.presheaf.stalk (f x)) N)
    (hG : IsWeaklyAssociatedPoint G (f x))
    (hx : x ∈ relativeAssassin f F) :
    IsWeaklyAssociatedPoint
      (((Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨X.toLocallyRingedSpace.toRingedSpace.presheaf,
          X.toLocallyRingedSpace.toRingedSpace.IsSheaf⟩).obj F).obj
        ((Scheme.Modules.pullback f).obj G)) x := by
  let R := S.presheaf.stalk (f x)
  let B := X.presheaf.stalk x
  let φ : R →+* B := (f.stalkMap x).hom
  let : Algebra R B := φ.toAlgebra
  let : IsLocalHom φ := f.toLRSHom.prop x
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
  let M := TopCat.Presheaf.stalk (C := Ab.{u}) G.val.presheaf (f x)
  let : Module R N := Module.compHom N φ
  have : IsScalarTower R B N := IsScalarTower.of_algebraMap_smul fun _ _ => rfl
  have : Module.Flat R N := hF
  have : Module.Projective R N := hproj
  have : Module.FinitePresentation B N :=
    @Stacks.SheafOfModules.finitePresentation_stalk X.toRingedSpace F hFfp x
  have hess : (algebraMap R B).EssentiallyOfFinitePresentation := by
    rw [RingHom.algebraMap_toAlgebra]
    exact LocallyOfFinitePresentation.essentiallyOfFinitePresentation_stalkMap f x
  have : IsNoetherianRing
      (B ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R)) :=
    isNoetherianRing_quotient_map_stalkMap f x
  rw [mem_relativeAssassin_iff_isAssociatedPoint_asFiber,
    isAssociatedPoint_pullback_fiberι_iff] at hx
  have hq : IsAssociatedPrimeStacks B
      (N ⧸ Ideal.map (algebraMap R B) (IsLocalRing.maximalIdeal R) • (⊤ : Submodule B N))
      (IsLocalRing.maximalIdeal B) := by
    rwa [RingHom.algebraMap_toAlgebra]
  have hT : IsWeaklyAssociatedPrime B (N ⊗[R] M) (IsLocalRing.maximalIdeal B) :=
    isWeaklyAssociatedPrime_tensorProduct_of_isAssociatedPrimeStacks_closedFibre
      (R := R) (S := B) (N := N) (M := M) hess hG hq
      fun s hs hle => le_antisymm hle (IsLocalRing.le_maximalIdeal hs.1.ne_top)
  exact (isWeaklyAssociatedPoint_tensorPullback_iff_tensorProduct f F G x).mpr hT

/-- **Stacks Project, Tag 05IH, granted projectivity of the stalk.** Let `f : X ⟶ S` be locally
of finite presentation, let `F` be an `𝒪_X`-module of finite presentation which is flat over `S`
at `x`, and let `G` be an `𝒪_S`-module. If the maximal ideal of `𝒪_{S, f x}` is finitely
generated and the stalk `F_x` is projective as an `𝒪_{S, f x}`-module, then `x` is weakly
associated to `F ⊗_{𝒪_X} f^*G` exactly when `f x` is weakly associated to `G` and `x` lies in
the relative assassin `Ass_{X/S}(F)`.

This is the biconditional of the tag under the restrictions of the two directions taken
together. The forward implication needs the finite generation of the maximal ideal and nothing
about projectivity; the converse needs projectivity and nothing about the maximal ideal.

The biconditional under the tag's own hypotheses alone is
`Stacks.Divisors.isWeaklyAssociatedPoint_tensorPullback_iff_of_finiteType` in
`StacksFrontier.AlgebraicGeometry.Flatness.WeaklyAssociatedTensorPullbackIff`. This version is
kept for the consumers that already have both extra hypotheses to hand. -/
theorem isWeaklyAssociatedPoint_tensorPullback_iff_of_projective_stalk
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) (G : S.Modules) [F.IsFinitePresentation] (x : X)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hfg : (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))).FG)
    (hproj : let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
      letI : Module (S.presheaf.stalk (f x)) N := Module.compHom N (f.stalkMap x).hom
      Module.Projective (S.presheaf.stalk (f x)) N) :
    IsWeaklyAssociatedPoint
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toLocallyRingedSpace.toRingedSpace.presheaf,
            X.toLocallyRingedSpace.toRingedSpace.IsSheaf⟩).obj F).obj
          ((Scheme.Modules.pullback f).obj G)) x ↔
      (IsWeaklyAssociatedPoint G (f x) ∧ x ∈ relativeAssassin f F) :=
  ⟨isWeaklyAssociatedPoint_and_mem_relativeAssassin_of_tensorPullback f F G x hF hfg,
    fun h => isWeaklyAssociatedPoint_tensorPullback_of_mem_relativeAssassin f F G x hF hproj
      h.1 h.2⟩

/-- **Stacks Project, Tag 05IH, for a stalk finite over the base local ring.** If the stalk `F_x`
is a finite `𝒪_{S, f x}`-module — as it is when `f` is finite — then flatness over `S` at `x`
already makes it free over `𝒪_{S, f x}` by Stacks 00NZ, so no projectivity hypothesis is needed
and the biconditional of the tag holds under the finite generation of the maximal ideal alone. -/
theorem isWeaklyAssociatedPoint_tensorPullback_iff_of_finite_stalk
    {X S : Scheme.{u}} (f : X ⟶ S) [LocallyOfFinitePresentation f]
    (F : X.Modules) (G : S.Modules) [F.IsFinitePresentation] (x : X)
    (hF : IsFlatOverAt f.toLRSHom.toShHom F x)
    (hfg : (IsLocalRing.maximalIdeal (S.presheaf.stalk (f x))).FG)
    (hfin : let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
      letI : Module (S.presheaf.stalk (f x)) N := Module.compHom N (f.stalkMap x).hom
      Module.Finite (S.presheaf.stalk (f x)) N) :
    IsWeaklyAssociatedPoint
        (((Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toLocallyRingedSpace.toRingedSpace.presheaf,
            X.toLocallyRingedSpace.toRingedSpace.IsSheaf⟩).obj F).obj
          ((Scheme.Modules.pullback f).obj G)) x ↔
      (IsWeaklyAssociatedPoint G (f x) ∧ x ∈ relativeAssassin f F) := by
  refine isWeaklyAssociatedPoint_tensorPullback_iff_of_projective_stalk f F G x hF hfg ?_
  let R := S.presheaf.stalk (f x)
  let N := TopCat.Presheaf.stalk (C := Ab.{u}) F.val.presheaf x
  let : Module R N := Module.compHom N (f.stalkMap x).hom
  have : Module.Flat R N := hF
  have : Module.Finite R N := hfin
  have : Module.Free R N := Module.free_of_flat_of_isLocalRing
  exact Module.Projective.of_free

end Stacks.Divisors

end
