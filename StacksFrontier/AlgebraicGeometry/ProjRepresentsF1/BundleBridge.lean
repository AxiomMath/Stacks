module

public import StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.UniversalBundle
public import StacksFrontier.AlgebraicGeometry.RelativeProjQcohSheaf.QuadrupleChartGlue

/-!
# The pullback clause of Tag 01O4, reduced to the two comparisons of the tensor powers

`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.UniversalBundle` reduced
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle` to one equation in each nonnegative degree,
relating the adjoint transpose of a pair's graded map to that of the pullback pair. That equation
still mentions the pair, the pullback–pushforward adjunction and the degree bookkeeping of
Section 01NS. This file removes all three: it shows the equation follows from a statement about
*nothing but the two comparisons of the tensor powers themselves*,
`Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorLaurentBridge`.

## Main definitions

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorLaurentBridge`: **the bridge**. In each
  nonnegative degree, the degreewise comparison
  `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorAlgebraPullbackIsos` of the pullback of a
  tensor algebra agrees, through the comparison
  `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorToLaurent` of a tensor algebra with the
  Laurent algebra, with the comparison
  `Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.laurentPullback` of the integral tensor powers
  of Tag 01CU.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorPowerToLaurent`: the comparison of the
  `m`-fold tensor power of `L` with the degree-`m` piece of its Laurent algebra.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.TensorPowerBridge`: **the bridge again, indexed by
  the natural numbers and with the tensor algebra gone.** This is the statement that is actually
  owed: it mentions only `pullbackTensorPowerIso`, `tensorPowerToLaurent` and `laurentPullback`.

## Main results

* `Stacks.AlgebraicGeometry.ProjRepresentsF1.isPullbackPair_pullbackPair_of_bridge`: **the
  pullback property of `pullbackPair` follows from the bridge**, at the canonical comparison
  `tensorAlgebraPullbackIsos TA` and with no other hypothesis.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorLaurentBridge_of_tensorPowerBridge`: **the
  bridge follows from its natural-number form** — the integer grading, the case split on the
  sign of the degree and the two degree transports of `tensorAlgebraPullbackIsos` are all
  discharged.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.bundleOfBridge` and
  `Stacks.AlgebraicGeometry.ProjRepresentsF1.bundleOfPowerBridge`: and hence so does the bundle
  of Tag 01O4, again at that canonical comparison.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.tensorPowerToLaurent_one`: **in degree one the
  comparison of the tensor powers with the Laurent algebra is the Laurent generator.** This is
  what reduces the degree-one case of the bridge to a lemma the repository already has; see the
  implementation notes for why that composition is not carried out here.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.eqToHom_comp_pullbackComp_inv`: the contraction of
  an iterated pullback absorbs the degree identification `n * 1 = n`.
* `Stacks.AlgebraicGeometry.ProjRepresentsF1.bridge_rearrange` and `bridge_power_rearrange`: the
  two rearrangements of the reduction, with every object and morphism free.

## Implementation notes

**The reduction is a cancellation on each side and one rearrangement.** On the right, the
comparison `tensorToLaurent` is an isomorphism in a nonnegative degree
(`isIso_tensorToLaurent_app`), so it may be cancelled; after it is, the pullback pair's transpose
becomes its family `laurentApp`, which `laurentApp_quadruplePair` identifies with the twisting of
the pulled-back quadruple — and that is `Twisting.pullbackApp`, built from `laurentPullback`, by
`rfl`. On the left, the bridge replaces the comparison of the tensor algebras by the comparison
of the Laurent algebras. What is left over is the degree identification `n * 1 = n`, cancelled on
the left, and pure associativity.

**The rearrangement is done with free variables.** `bridge_rearrange` takes every object and
morphism as a variable, so it is elaborated once against a goal in an abstract category; stated
at the sheaf-of-modules spelling the same chase meets two spellings of the pullback functor and
runs out of heartbeats in `whnf`. The two spellings — `AlgebraicGeometry.Scheme.Modules.pullback`
and `Stacks.RingedSpace.pullbackFunctor` of the underlying morphism of ringed spaces — are equal
by `rfl`, which is what lets one instantiation serve both sides.

## Not done here

**No project tag is attached here.** `TensorPowerBridge` is proved, in
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorPowerBridgeProof`
(`...ProjRepresentsF1.tensorPowerBridge`), so `bundleOfPowerBridge` does assemble an
`Stacks.AlgebraicGeometry.ProjRepresentsF1.F1Bundle` at the canonical comparison, as
`...ProjRepresentsF1.f1Bundle`; the tag sits there and not on this file's reduction. The notes
below describe what that proof had to supply, and are kept because they say where each piece is.

**Degree one is closed**, in
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorPowerBridgeSteps`:
`tensorPowerToLaurent_one` identifies the comparison with the Laurent generator and
`pullbackTensorPowerIso` is `Iso.refl` there, so that case asks exactly that the Laurent
generator commute with the pullback, which is
`...RelativeProjQcohSheaf.laurentPullback_tensorPowerOneIso` with both sides inverted
(`...ProjRepresentsF1.laurentGenerator_pullback`). What blocked the composition was the
invertibility instance
`(SheafOfModules.TensorPower.tensorRightFunctor T.toRingedSpace.presheaf _ L).IsEquivalence`
that `tensorPowerOneIso` takes, which neither spelling of invertibility carried here yielded;
`...ProjRepresentsF1.isEquivalence_tensorRightFunctor_scheme` supplies it.

**Degree zero is the degree-zero value of `tensorPowerToLaurent`, and nothing else.** The two
structure-sheaf comparisons are *not* two: `(Scheme.Modules.pullbackUnitIso g).hom` and
`Stacks.PullbackTensorCoherence.pullbackUnitComparison (ringedSpaceHom g)` are the same
morphism by `rfl` (`...ProjRepresentsF1.pullbackTensorPowerIso_zero_hom`), and
`...RelativeProjQcohSheaf.laurentPullback_zero` is the second. So the case reduces to
`tensorPowerToLaurent TA L 0 = 𝟙`, which is not reflexive: it is the degree-zero identification
`tensorPieceIso_zero` of the bundle together with the `map_one` field of `tensorToLaurent` and
`...RelativeProjQcohSheaf.oneHom_laurent`. It is `...ProjRepresentsF1.tensorPowerToLaurent_zero`.
The `map_one` field in its morphism form was already in the library, as
`...RelativeProjQcohSheaf.oneHom_comp_app_zero`.

**The inductive step is where it stops.** `pullbackTensorPowerIso` recurses on the *left* —
`SheafOfModules.tensorPower J F (n + 2)` is `F ⊗ tensorPower J F (n + 1)`, so the new copy of
`F` is the left factor — while `...RelativeProjQcohSheaf.laurentPullback_succIso` has its
successor law on the *right*, whiskering by one more copy of `g^*L`. No braiding is needed:
`...RelativeProjQcohSheaf.laurentPullback_mulSheaf` is stated for an arbitrary bidegree, so
bidegree `(1, n + 1)` gives the left-handed law directly.

The matching left-handed law for `tensorPowerToLaurent` is now available, as
`...ProjRepresentsF1.tensorPowerToLaurent_add_two` in
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorPowerBridgeSteps`. It did not need a new
lift of the sectionwise field
`SheafOfModules.TensorExteriorSymmetricAlgebras.tensorPieceIso_mul_left`: that lift already
existed, as `...ProjRepresentsF1.generatorMul_comp_eq_id` of
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorAlgebraMul`, which was private there and
is now public.

The pair of successor laws for the two sides of the square is now available too, as
`...ProjRepresentsF1.pullbackTensorPowerIso_comp_tensorPowerToLaurent_add_two` and
`...ProjRepresentsF1.map_tensorPowerToLaurent_comp_laurentPullback_add_two`. Joining them needed
the comparison of Tag 01CD in its two spellings — `pullbackTensorSchemeIso`, built from
`Stacks.PullbackTensorIso.pullbackTensorIso`, against the
`Stacks.PullbackTensorCoherence.pullbackTensorComparison` that `laurentPullback_mulSheaf` is
stated with, which the kernel identifies — together with its naturality in both variables
(`...ProjRepresentsF1.pullbackTensorSchemeIso_naturality`, one line off that same isomorphism of
bifunctors) and the conversion
`Stacks.PullbackTensorCoherence.tensorSheaf_map_eq_tensorHom` between
`Stacks.SheafOfModules.Tensor.sheafTensor`'s functorial action and the monoidal `⊗ₘ`.

The two identifications of this kind the repository already had,
`...RelativeProjQcohSheaf.pieceIso_hom_eq_laurentPullback` and
`...RelativeProjQcohSheaf.pullPowCompare_eq_powComparePull`, relate families that recurse on the
same side, so neither their method nor the reusable induction
`...RelativeProjQcohSheaf.eq_of_whiskerRight_rec` applies here: that induction is stated for a
right-handed whiskering recursion. The induction used instead is a two-step recursion on `ℕ` with
two base cases, `rec_two` of
`StacksFrontier.AlgebraicGeometry.ProjRepresentsF1.TensorPowerBridgeProof`.

## References

* [Stacks Project, Tag 01O4](https://stacks.math.columbia.edu/tag/01O4)
* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 01CU](https://stacks.math.columbia.edu/tag/01CU)
* [Stacks Project, Section 01NS](https://stacks.math.columbia.edu/tag/01NS)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.RingedSpace

namespace Stacks.AlgebraicGeometry.ProjRepresentsF1

universe u

variable {S : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (TA : TensorAlgebras.{u})

/-- The bridge hypothesis: the degreewise comparison of the pullback of a tensor algebra agrees
with the comparison of the integral tensor powers that the Laurent algebra is graded by. -/
public def TensorLaurentBridge {T T' : Scheme.{u}} (g : T' ⟶ T) (L : T.Modules)
    [Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L] : Prop :=
  ∀ n : ℤ, 0 ≤ n →
    (tensorAlgebraPullbackIsos TA g L n).hom ≫
        (tensorToLaurent ((Scheme.Modules.pullback g).obj L)
          (TA T' ((Scheme.Modules.pullback g).obj L))).app n =
      (Scheme.Modules.pullback g).map ((tensorToLaurent L (TA T L)).app n) ≫
        laurentPullback g L n

/-- A pair's adjoint transpose followed by the comparison of its tensor algebra with its Laurent
algebra is the family `laurentApp`, up to the degree identification `n * 1 = n`. -/
public theorem pullbackMap_comp_tensorToLaurent {T : Scheme.{u}} {h : T ⟶ S}
    (R : F1Pair A TA h) (n : ℤ) :
    letI := R.invertible
    R.pullbackMap A TA n ≫ (tensorToLaurent R.L (TA T R.L)).app n =
      eqToHom (congrArg (fun k : ℤ =>
          (pullbackFunctor (ringedSpaceHom h)).obj ((situationAlgebra A).piece k))
          (mul_one n).symm) ≫
        R.laurentApp A TA h n := by
  let := R.invertible
  change R.pullbackMap A TA n ≫ (tensorToLaurent R.L (TA T R.L)).app n =
    eqToHom _ ≫ eqToHom _ ≫ R.pullbackMap A TA n ≫ (tensorToLaurent R.L (TA T R.L)).app n
  exact Eq.symm (Eq.trans (Category.assoc _ _ _).symm
    (Eq.trans
      (congrArg (fun z => z ≫ R.pullbackMap A TA n ≫ (tensorToLaurent R.L (TA T R.L)).app n)
        (Eq.trans (eqToHom_trans _ _) (eqToHom_refl _ _)))
      (Category.id_comp _)))

section PowerBridge

variable {T T' : Scheme.{u}} (g : T' ⟶ T) (L : T.Modules)
  [Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L]

/-- **The comparison of the `m`-fold tensor power of `L` with the degree-`m` piece of its
Laurent algebra**: the identification of the tensor power with the degree-`m` piece of the tensor
algebra, followed by the comparison of the tensor algebra with the Laurent algebra. It is an
isomorphism, both factors being ones. -/
public def tensorPowerToLaurent (m : ℕ) :
    SheafOfModules.tensorPower (Opens.grothendieckTopology ↥T) L m ⟶
      (laurent L).piece (m : ℤ) :=
  ((TA T L).tensorPieceIso m).inv ≫ (tensorToLaurent L (TA T L)).app (m : ℤ)

/-- **In degree one the comparison is the Laurent generator.** The degree-one identification of
the tensor algebra is inverse to its generator (`tensorGenerator_eq`), and the generator composed
with the comparison of the two graded algebras of `L` is the Laurent generator
(`tensorGenerator_comp_tensorToLaurent`), which is what pins `tensorToLaurent` down. -/
public theorem tensorPowerToLaurent_one :
    tensorPowerToLaurent TA L 1 = laurentGenerator L :=
  Eq.trans
    (congrArg (fun z => z ≫ (tensorToLaurent L (TA T L)).app 1)
      ((TA T L).tensorGenerator_eq).symm)
    (tensorGenerator_comp_tensorToLaurent L (TA T L))

/-- **The bridge, indexed by the natural numbers and with the tensor algebra gone.** The
comparison `pullbackTensorPowerIso` of the `m`-fold tensor powers agrees, through
`tensorPowerToLaurent`, with the comparison `laurentPullback` of the integral tensor powers.

This is `TensorLaurentBridge` with the integer grading, the case split on the sign of the degree
and the two degree transports of `tensorAlgebraPullbackIsos` all discharged; see
`tensorLaurentBridge_of_tensorPowerBridge`. -/
public def TensorPowerBridge : Prop :=
  ∀ m : ℕ, (pullbackTensorPowerIso g L m).hom ≫
      tensorPowerToLaurent TA ((Scheme.Modules.pullback g).obj L) m =
    (Scheme.Modules.pullback g).map (tensorPowerToLaurent TA L m) ≫
      laurentPullback g L (m : ℤ)

end PowerBridge

section Degree

variable {T T' : Scheme.{u}} (g : T' ⟶ T) (f : T ⟶ S)

/-- **The contraction of an iterated pullback absorbs the degree identification `n * 1 = n`.**
On the left the identification is applied to the pullback along the composite, on the right to
the inner pullback; the contraction carries one to the other. This is
`Stacks.AlgebraicGeometry.RelativeProjQcohSheaf.Quadruple.compComparison_comp_eqToHom` with the
contraction spelled as the component of Mathlib's composition isomorphism, by
`compComparison_eq_pullbackComp_inv`. -/
public theorem eqToHom_comp_pullbackComp_inv (n : ℤ) :
    eqToHom (congrArg (fun k : ℤ =>
        (pullbackFunctor (ringedSpaceHom (g ≫ f))).obj ((situationAlgebra A).piece k))
        (mul_one n)) ≫ (Scheme.Modules.pullbackComp g f).inv.app (A.piece n) =
      compComparison g f ((situationAlgebra A).piece (n * 1)) ≫
        (pullbackFunctor (ringedSpaceHom g)).map (eqToHom (congrArg (fun k : ℤ =>
          (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A).piece k))
          (mul_one n))) :=
  Eq.trans
    (congrArg (fun z => eqToHom (congrArg (fun k : ℤ =>
        (pullbackFunctor (ringedSpaceHom (g ≫ f))).obj ((situationAlgebra A).piece k))
        (mul_one n)) ≫ z)
      (compComparison_eq_pullbackComp_inv g f ((situationAlgebra A).piece n)).symm)
    (Eq.trans
      (congrArg (fun z => z ≫ compComparison g f ((situationAlgebra A).piece n))
        (eqToHom_map (pullbackFunctor (ringedSpaceHom (g ≫ f)))
          (congrArg (situationAlgebra A).piece (mul_one n))).symm)
      (Quadruple.compComparison_comp_eqToHom (g := f) (f' := g) (A := situationAlgebra A)
        (mul_one n)).symm)

end Degree

/-! ### The rearrangement, with every object and morphism free -/

/-- The one rearrangement the reduction needs, stated with every object and morphism a free
variable so that it is checked once, away from any goal mentioning two spellings of the pullback
functor or of the tensor product. -/
public theorem bridge_rearrange {C : Type*} [Category C] {W₀ W₁ V V₁ V₂ V₀ Z Y : C}
    (e : W₀ ⟶ W₁) (pc : W₁ ⟶ V) (u : V ⟶ V₁) (iota : V₁ ⟶ V₂) (tp : V₂ ⟶ Y)
    (cc : W₀ ⟶ V₀) (me : V₀ ⟶ V) (mt : V₁ ⟶ Z) (lam : Z ⟶ Y) (mc : V₀ ⟶ Z)
    (hd : e ≫ pc = cc ≫ me) (hu : iota ≫ tp = mt ≫ lam) (hm : me ≫ u ≫ mt = mc) :
    e ≫ (pc ≫ u ≫ iota) ≫ tp = cc ≫ mc ≫ lam := by
  calc e ≫ (pc ≫ u ≫ iota) ≫ tp
      = (e ≫ pc) ≫ u ≫ iota ≫ tp := by simp only [Category.assoc]
    _ = (cc ≫ me) ≫ u ≫ mt ≫ lam := by rw [hd, hu]
    _ = cc ≫ (me ≫ u ≫ mt) ≫ lam := by simp only [Category.assoc]
    _ = cc ≫ mc ≫ lam := by rw [hm]

/-- The rearrangement of the degree reduction, with every object and morphism free. -/
public theorem bridge_power_rearrange {C : Type*} [Category C] {W V₀ V₁ V₂ Z Y : C}
    (mh : W ⟶ V₀) (pt : V₀ ⟶ V₁) (wi : V₁ ⟶ V₂) (tp : V₂ ⟶ Y) (mw : V₀ ⟶ Z) (lam : Z ⟶ Y)
    (mt : W ⟶ Z) (h1 : pt ≫ wi ≫ tp = mw ≫ lam) (h2 : mh ≫ mw = mt) :
    mh ≫ pt ≫ wi ≫ tp = mt ≫ lam := by
  rw [h1, ← h2, Category.assoc]

/-- The three factors of `pullbackTensorPieceIso`, by definition. -/
public theorem pullbackTensorPieceIso_hom {T T' : Scheme.{u}} (g : T' ⟶ T) (L : T.Modules)
    (m : ℕ) :
    (pullbackTensorPieceIso g TA L m).hom =
      (Scheme.Modules.pullback g).map ((TA T L).tensorPieceIso m).hom ≫
        (pullbackTensorPowerIso g L m).hom ≫
          ((TA T' ((Scheme.Modules.pullback g).obj L)).tensorPieceIso m).inv := rfl

/-- **The bridge follows from its natural-number form.** The integer grading, the case split on
the sign of the degree and the two degree transports of `tensorAlgebraPullbackIsos` are all
discharged here: a nonnegative integer is a natural number, at which `Int.toNat_of_nonneg` is
reflexive and both transports are identities. -/
public theorem tensorLaurentBridge_of_tensorPowerBridge {T T' : Scheme.{u}} (g : T' ⟶ T)
    (L : T.Modules) [Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L]
    (h : TensorPowerBridge TA g L) : TensorLaurentBridge TA g L := by
  intro n hn
  obtain ⟨m, rfl⟩ := Int.eq_ofNat_of_zero_le hn
  have hdef : tensorAlgebraPullbackIsos TA g L (m : ℤ) =
      eqToIso (congrArg
          (fun k : ℤ => (Scheme.Modules.pullback g).obj ((TA T L).tensor.piece k))
          (Int.toNat_of_nonneg hn).symm) ≪≫
        pullbackTensorPieceIso g TA L ((m : ℤ)).toNat ≪≫
        eqToIso (congrArg
          (fun k : ℤ =>
            (TA T' ((Scheme.Modules.pullback g).obj L)).tensor.piece k)
          (Int.toNat_of_nonneg hn)) :=
    dite_eq_left hn
  rw [hdef]
  simp only [Int.toNat_natCast]
  exact bridge_power_rearrange
    ((Scheme.Modules.pullback g).map ((TA T L).tensorPieceIso m).hom)
    ((pullbackTensorPowerIso g L m).hom)
    (((TA T' ((Scheme.Modules.pullback g).obj L)).tensorPieceIso m).inv)
    ((tensorToLaurent ((Scheme.Modules.pullback g).obj L)
      (TA T' ((Scheme.Modules.pullback g).obj L))).app (m : ℤ))
    ((Scheme.Modules.pullback g).map (tensorPowerToLaurent TA L m))
    (laurentPullback g L (m : ℤ))
    ((Scheme.Modules.pullback g).map ((tensorToLaurent L (TA T L)).app (m : ℤ)))
    (h m)
    (Eq.trans (Functor.map_comp (Scheme.Modules.pullback g) _ _).symm
      (congrArg (Scheme.Modules.pullback g).map
        (Iso.hom_inv_id_assoc ((TA T L).tensorPieceIso m)
          ((tensorToLaurent L (TA T L)).app (m : ℤ)))))

/-! ### The reduction -/

/-- **The pullback clause of Tag 01O4 follows from the agreement of the two comparisons of the
tensor powers.** -/
public theorem isPullbackPair_pullbackPair_of_bridge {T T' : Scheme.{u}} {f : T ⟶ S}
    (g : T' ⟶ T) (P : F1Pair A TA f)
    (hbr : letI := P.invertible; TensorLaurentBridge TA g P.L) :
    IsPullbackPair A TA (tensorAlgebraPullbackIsos TA) g P (pullbackPair A TA g P) := by
  let := P.invertible
  refine isPullbackPair_pullbackPair_of_degreewise A TA g P fun n hn => ?_
  have hiso : IsIso ((tensorToLaurent ((Scheme.Modules.pullback g).obj P.L)
      (TA T' ((Scheme.Modules.pullback g).obj P.L))).app n) :=
    isIso_tensorToLaurent_app _ _ n hn
  refine (Iso.cancel_iso_hom_right _ _ (@asIso _ _ _ _ _ hiso)).mp ?_
  refine (Iso.cancel_iso_hom_left (eqToIso (congrArg (fun k : ℤ =>
      (pullbackFunctor (ringedSpaceHom (g ≫ f))).obj ((situationAlgebra A).piece k))
      (mul_one n))) _ _).mp ?_
  refine Eq.trans ?_ (laurentApp_quadruplePair A TA (g ≫ f)
    ((P.quadruple A TA f).pullback g) n).symm
  exact bridge_rearrange
    (eqToHom (congrArg (fun k : ℤ =>
      (pullbackFunctor (ringedSpaceHom (g ≫ f))).obj ((situationAlgebra A).piece k))
      (mul_one n)))
    ((Scheme.Modules.pullbackComp g f).inv.app (A.piece n))
    ((Scheme.Modules.pullback g).map (P.pullbackMap A TA n))
    ((tensorAlgebraPullbackIsos TA g P.L n).hom)
    ((tensorToLaurent ((Scheme.Modules.pullback g).obj P.L)
      (TA T' ((Scheme.Modules.pullback g).obj P.L))).app n)
    (compComparison g f ((situationAlgebra A).piece (n * 1)))
    ((pullbackFunctor (ringedSpaceHom g)).map (eqToHom (congrArg (fun k : ℤ =>
      (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A).piece k)) (mul_one n))))
    ((Scheme.Modules.pullback g).map ((tensorToLaurent P.L (TA T P.L)).app n))
    (laurentPullback g P.L n)
    ((pullbackFunctor (ringedSpaceHom g)).map (P.laurentApp A TA f n))
    (eqToHom_comp_pullbackComp_inv A g f n)
    (hbr n hn)
    (Eq.trans
      (congrArg (fun z => (pullbackFunctor (ringedSpaceHom g)).map (eqToHom (congrArg
        (fun k : ℤ => (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A).piece k))
        (mul_one n))) ≫ z)
        (Functor.map_comp (Scheme.Modules.pullback g) (P.pullbackMap A TA n)
          ((tensorToLaurent P.L (TA T P.L)).app n)).symm)
      (Functor.map_comp (Scheme.Modules.pullback g)
        (eqToHom (congrArg (fun k : ℤ =>
          (pullbackFunctor (ringedSpaceHom f)).obj ((situationAlgebra A).piece k)) (mul_one n)))
        (P.pullbackMap A TA n ≫ (tensorToLaurent P.L (TA T P.L)).app n)).symm)

/-- **The bundle of Tag 01O4 from the bridge**, at the canonical comparison
`tensorAlgebraPullbackIsos TA`: the universal pair, the representing bijections and their
normalisation come from `bundleOfIsPullbackPair`, and the pullback clause from
`isPullbackPair_pullbackPair_of_bridge`. -/
public def bundleOfBridge (hgen : IsGeneratedInDegreeOne A)
    (hbr : ∀ {T T' : Scheme.{u}} {f : T ⟶ S} (g : T' ⟶ T) (P : F1Pair A TA f),
      letI := P.invertible; TensorLaurentBridge TA g P.L) :
    F1Bundle A TA (tensorAlgebraPullbackIsos TA) :=
  bundleOfIsPullbackPair A TA hgen
    (fun g P => isPullbackPair_pullbackPair_of_bridge A TA g P (hbr g P))

/-- **The bundle of Tag 01O4 from the natural-number form of the bridge**: what Tag 01O4's
bundle costs, at the canonical comparison `tensorAlgebraPullbackIsos TA`, is the agreement of
`pullbackTensorPowerIso` with `laurentPullback` through `tensorPowerToLaurent`, in each
nonnegative degree, and nothing else. -/
public def bundleOfPowerBridge (hgen : IsGeneratedInDegreeOne A)
    (hbr : ∀ {T T' : Scheme.{u}} (g : T' ⟶ T) (L : T.Modules)
      (hL : Stacks.SheafOfModules.IsInvertible T.presheaf T.ringCatSheaf.2 L),
      letI := hL; TensorPowerBridge TA g L) :
    F1Bundle A TA (tensorAlgebraPullbackIsos TA) :=
  bundleOfBridge A TA hgen fun g P =>
    letI := P.invertible
    tensorLaurentBridge_of_tensorPowerBridge TA g P.L (hbr g P.L P.invertible)

end Stacks.AlgebraicGeometry.ProjRepresentsF1

end
