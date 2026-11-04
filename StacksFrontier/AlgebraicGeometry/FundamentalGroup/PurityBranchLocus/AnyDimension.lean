module

public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.EtaleAt
public import StacksFrontier.AlgebraicGeometry.Etale.Morphisms.Permanence
public import StacksFrontier.AlgebraicGeometry.Flatness.FiniteNeighborhood
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.ExtendedEtale.PointwiseEtale
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.DimensionAtMostTwo
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.PurityLocalizedFinite
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityBranchLocus.PurityRegularLocal
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.EtaleLocus
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.PurityRamificationLocus.Generizations
public import StacksFrontier.AlgebraicGeometry.Morphisms.CohenMacaulay.LocalRing
public import StacksFrontier.AlgebraicGeometry.Morphisms.Etale.LocusBaseChange
public import StacksFrontier.AlgebraicGeometry.Morphisms.EtaleNeighbourhood.FiniteSingletonFibre
public import StacksFrontier.AlgebraicGeometry.Morphisms.FinitePresentation.LocallyNoetherian
public import StacksFrontier.AlgebraicGeometry.Morphisms.QuasiFinite.Locus
public import StacksFrontier.AlgebraicGeometry.Spaces.RegularLocalRings
public import StacksFrontier.RingTheory.Etale.Height
public import StacksFrontier.RingTheory.IntegrallyClosed.Stability
public import StacksFrontier.RingTheory.QuasiFinite.Dimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Purity of the branch locus in any dimension

Let `f : X ⟶ Y` be a morphism of locally Noetherian schemes, let `x` be a point of `X` and let
`y = f x`. Assume the local ring of `X` at `x` is normal, the local ring of `Y` at `y` is regular,
`f` is quasi-finite at `x`, the two local rings have the same dimension `d ≥ 1`, and `f` is
unramified at every point specializing to `x` whose local ring has dimension one. Purity of the
branch locus, [Stacks, Tag 0BMB], asserts that `f` is then étale at `x`.

This file carries out the two steps of the source's proof that
`AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_dim_le_two` leaves
open above dimension two: the passage from the quasi-finite morphism of schemes to a *finite*
algebra, and the induction on `d` which upgrades the hypothesis on one-dimensional generizations
to étaleness at *every* generization. Its input from the other side of the source's argument is
[Stacks, Tag 0BMA] clause (2) in every dimension `d ≥ 2`, in the predicate shape
`Stacks.PurityBranchLocus.PurityFiniteNormal`; `Stacks.PurityBranchLocus.purityFiniteNormal`
below supplies it from `Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_two_le_ringKrullDim`,
so the tag is proved here in every dimension.

## The shape of the argument

Étaleness at `x` is, in any dimension, a consequence of Cohen–Macaulayness of `𝒪_{X,x}`: the
theorem `etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_isMaximalCohenMacaulay`
derives flatness of the stalk map from miracle flatness and then applies [Stacks, Tag 0BJH]. So
the whole residual content of the tag is that `𝒪_{X,x}` be Cohen–Macaulay, and that is what the
étale-local reduction supplies.

By [Stacks, Tag 02LK] an elementary étale change of the base makes `f` finite near `x`, with a
single point `v` over the distinguished point `b` of the neighbourhood: concretely, writing
`g : V' ⟶ U'` for the restriction of `f` to a pair of affine opens and `q : Bs ⟶ U'` for the
elementary étale neighbourhood of `g z`, there is an open `W` of `V' ×_{U'} Bs` such that
`p = W.ι ≫ pullback.snd g q` is finite and `v` is the only point of `W` over `b`, while
`r = W.ι ≫ pullback.fst g q` is étale with `r v = z`. The local ring `𝒪_{W,v}` is then a *finite*
algebra over `𝒪_{Bs,b}` ([Stacks, Tag 05B8]), and the permanence of properties along an étale
morphism ([Stacks, Tags 025N, 025P, 025Q, 039S, 04N8]) carries normality, regularity, dimension
and Cohen–Macaulayness between the two sides of the square.

Two conclusions are drawn in that model.

* **Going down.** `𝒪_{Bs,b}` is a regular, hence normal, local ring, `𝒪_{W,v}` is a normal local
  domain of the same dimension, and the finite map between them is injective, so going down holds
  ([Stacks, Tag 00H8], Mathlib's instance for an integral extension of a normal domain). Height is
  therefore preserved, which is exactly the statement that `dim 𝒪_{X,x'} = dim 𝒪_{Y,f x'}` at
  every point `x'` specializing to `x`: the generizations of `x` are the primes of `𝒪_{X,x}`
  ([Stacks, Tag 01J7]), they lift to generizations of `v` because the étale map `r` is flat, and
  the dimension of a local ring at a generization is the height of the corresponding prime.
* **Cohen–Macaulayness.** `PurityFiniteNormal` applies to the finite algebra
  `𝒪_{Bs,b} → 𝒪_{W,v}` once `Spec 𝒪_{W,v}` is étale over the punctured spectrum of `𝒪_{Bs,b}`,
  which is étaleness of `p` at every point of `W` strictly generizing `v`. Then `𝒪_{W,v}` is
  regular, hence Cohen–Macaulay, and Cohen–Macaulayness descends to `𝒪_{X,x}` along `r`.

The induction on `d` is then the source's. For `d ≤ 2` the conclusion is already available. For
`d ≥ 3` every proper generization `x'` of `x` is treated first: its local ring is normal and the
local ring at `f x'` is regular, both being generizations; `f` is quasi-finite at `x'` because the
quasi-finite locus is open and a generization lies in every open neighbourhood; the two dimensions
agree there by the going-down step; and `dim 𝒪_{X,x'} < d`. If that dimension is positive the
induction hypothesis applies at `x'`, and if it is zero then `x'` is a generization of a
one-dimensional generization of `x`, where the induction hypothesis applies and étaleness spreads
to generizations.

## Main results

* `Stacks.PurityBranchLocus.height_eq_height_of_finite_of_isRegularLocalRing` — going down for a
  finite local homomorphism from a regular local ring to a normal local ring of the same
  dimension, in the form of equality of heights.
* `Stacks.PurityBranchLocus.purityFiniteNormal` — [Stacks, Tag 0BMA] clause (2) in every
  dimension `d ≥ 2`, in the predicate shape the results below consume.
* `AlgebraicGeometry.ringKrullDim_stalk_eq_of_specializes_of_quasiFiniteAt` — the dimensions of
  the two local rings agree at every generization of `x`.
* `AlgebraicGeometry.isMaximalCohenMacaulay_stalk_of_etaleAt_generizations` — `𝒪_{X,x}` is
  Cohen–Macaulay, from `PurityFiniteNormal`.
* `AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne` — the whole of
  [Stacks, Tag 0BMB], at the tag's own hypotheses and in every dimension.

## The other registrations of the tag

[Stacks, Tag 0BMB] is also registered on
`AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_dim_eq_one`
(`PurityBranchLocus.DimensionOne`) and on
`AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_dim_le_two`
(`PurityBranchLocus.DimensionAtMostTwo`), which are the cases `d = 1` and `1 ≤ d ≤ 2` of the
source's induction; the latter is the base case of the induction below. Both are subsumed by the
theorem here, and both are kept: they are the statements the dimension-restricted arguments
prove, and the dimension-at-most-two case needs none of this file's étale-local reduction.

## References

* [Stacks Project, Tag 0BMB](https://stacks.math.columbia.edu/tag/0BMB)
* [Stacks Project, Tag 0BMA](https://stacks.math.columbia.edu/tag/0BMA)
* [Stacks Project, Tag 02LK](https://stacks.math.columbia.edu/tag/02LK)
* [Stacks Project, Tag 00H8](https://stacks.math.columbia.edu/tag/00H8)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing TopologicalSpace

universe u

namespace Stacks.PurityBranchLocus

/-! ### Going down for a finite local homomorphism out of a regular local ring -/

/-- **Going down for a finite local homomorphism from a regular local ring to a normal local ring
of the same dimension**, in the form of equality of heights: if `A → B` is a finite homomorphism
of local rings with `A` regular, `B` a normal ring and `dim B = dim A`, then a prime of `B` and
the prime of `A` it lies over have the same height.

The structure map is injective by equality of dimensions
(`Stacks.PurityBranchLocus.injective_algebraMap_of_finite_of_ringKrullDim_eq`), so `B` is an
integral extension of the normal domain `A` ([Stacks, Tag 0567] makes a regular ring normal) and
going down holds, [Stacks, Tag 00H8]. The opposite inequality is quasi-finiteness,
[Stacks, Tag 00QF]. -/
public lemma height_eq_height_of_finite_of_isRegularLocalRing
    {A B : Type u} [CommRing A] [CommRing B] [Algebra A B] [Module.Finite A B]
    [IsLocalRing A] [IsLocalRing B]
    (hA : IsRegularLocalRing A) (hB : IsNormalRing B)
    (hdim : ringKrullDim B = ringKrullDim A)
    (P : Ideal A) (Q : Ideal B) [P.IsPrime] [Q.IsPrime] [Q.LiesOver P] :
    Q.height = P.height := by
  have _ : IsRegularLocalRing A := hA
  have _ : IsRegularRing A :=
    ((IsLocalRing.isRegularRing_tfae (R := A)).out 1 3).mp (inferInstance : IsRegularLocalRing A)
  obtain ⟨hdomA, hicA⟩ := (main_theorem0567 A).of_isLocalRing
  have _ : IsDomain A := hdomA
  have _ : IsIntegrallyClosed A := hicA
  obtain ⟨hdomB, -⟩ := hB.of_isLocalRing
  have _ : IsDomain B := hdomB
  have _ : FaithfulSMul A B := (faithfulSMul_iff_algebraMap_injective A B).2
    (injective_algebraMap_of_finite_of_ringKrullDim_eq hdim)
  have _ : Algebra.HasGoingDown A B := inferInstance
  exact le_antisymm (Ideal.height_le_height_of_liesOver_of_quasiFiniteAt P Q)
    (Ideal.height_le_height_of_liesOver_of_hasGoingDown P Q)

/-- **Going down along a local homomorphism of local rings**: every prime of the source lies under
a prime of the target. The maximal ideal lies under the maximal ideal, and a prime strictly below
it is reached by going down from the maximal ideal, [Stacks, Tag 00H8]. -/
private lemma exists_isPrime_liesOver_of_hasGoingDown {A B : Type u} [CommRing A] [CommRing B]
    [IsLocalRing A] [IsLocalRing B] [Algebra A B] [Algebra.HasGoingDown A B]
    (hunder : Ideal.under A (maximalIdeal B) = maximalIdeal A) (P : Ideal A) [P.IsPrime] :
    ∃ Q : PrimeSpectrum B, Q.asIdeal.LiesOver P := by
  rcases eq_or_lt_of_le (IsLocalRing.le_maximalIdeal_of_isPrime P) with heq | hlt
  · exact ⟨⟨maximalIdeal B, (maximalIdeal.isMaximal B).isPrime⟩, ⟨by rw [hunder, heq]⟩⟩
  · obtain ⟨Q, -, hQprime, hQover⟩ :=
      Algebra.HasGoingDown.exists_ideal_le_liesOver_of_lt (maximalIdeal B)
        (by rwa [hunder])
    exact ⟨⟨Q, hQprime⟩, hQover⟩

/-! ### The input from the branch locus in a general dimension -/

/-- **[Stacks, Tag 0BMA] clause (2) in every dimension `d ≥ 2`**, in the predicate shape
`Stacks.PurityBranchLocus.PurityFiniteNormal` that the results below consume. It is the statement
of `Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_two_le_ringKrullDim`, where the tag is
proved by the source's induction on `d`. -/
@[ega "IV 21.12.14" "special case"]
public lemma purityFiniteNormal : PurityFiniteNormal.{u} :=
  fun A B _ _ _ _ _ _ hB hdim hetale =>
    Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_two_le_ringKrullDim A B hB hdim hetale

end Stacks.PurityBranchLocus

namespace AlgebraicGeometry

/-! ### The finite model -/

/-- The two projections of a fibre product agree in the base: a point of an open `W` of
`V' ×_{U'} Bs` has the same image in `U'` whether it is taken through `g` or through `q`. -/
private lemma apply_comp_fst_eq_apply_comp_snd {V' U' : Scheme.{u}} (g : V' ⟶ U')
    {Bs : Scheme.{u}} (q : Bs ⟶ U') (W : (pullback g q).Opens) (y : W.toScheme) :
    g ((W.ι ≫ pullback.fst g q) y) = q ((W.ι ≫ pullback.snd g q) y) := by
  have h := congrArg (fun m : (pullback g q : Scheme.{u}) ⟶ U' => m (W.ι y))
    (pullback.condition (f := g) (g := q))
  simpa only [Scheme.Hom.comp_apply] using h

/-- In the situation of [Stacks, Tag 02LK], the structure of the finite model: the projection
`W.ι ≫ pullback.fst g q` is étale, `W` and `Bs` are locally Noetherian, the local ring of the new
base `Bs` at the distinguished point is regular, the local ring of `W` at `v` is normal, and the
two have the same dimension.

Regularity and dimension are read off the étale morphisms `q` and `W.ι ≫ pullback.fst g q`
([Stacks, Tags 025P, 04N8]) and normality off the latter ([Stacks, Tag 025N]). -/
private lemma etale_isLocallyNoetherian_isRegularLocalRing_isNormalRing_of_etale
    {V' U' : Scheme.{u}} (g : V' ⟶ U') [IsLocallyNoetherian V'] [IsLocallyNoetherian U']
    [LocallyOfFiniteType g] {Bs : Scheme.{u}} (q : Bs ⟶ U') [Etale q]
    (W : (pullback g q).Opens) (v : W.toScheme)
    (hX : IsNormalRing (V'.presheaf.stalk ((W.ι ≫ pullback.fst g q) v)))
    (hY : IsRegularLocalRing (U'.presheaf.stalk (g ((W.ι ≫ pullback.fst g q) v))))
    (hdim : ringKrullDim (V'.presheaf.stalk ((W.ι ≫ pullback.fst g q) v)) =
      ringKrullDim (U'.presheaf.stalk (g ((W.ι ≫ pullback.fst g q) v)))) :
    Etale (W.ι ≫ pullback.fst g q) ∧ IsLocallyNoetherian W.toScheme ∧ IsLocallyNoetherian Bs ∧
      IsRegularLocalRing (Bs.presheaf.stalk ((W.ι ≫ pullback.snd g q) v)) ∧
      IsNormalRing (W.toScheme.presheaf.stalk v) ∧
        ringKrullDim (W.toScheme.presheaf.stalk v) =
          ringKrullDim (Bs.presheaf.stalk ((W.ι ≫ pullback.snd g q) v)) := by
  have _ : Etale (pullback.fst g q) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback g q).flip inferInstance
  have _ : Etale (W.ι ≫ pullback.fst g q) := inferInstance
  have _ : IsLocallyNoetherian W.toScheme :=
    LocallyOfFiniteType.isLocallyNoetherian (W.ι ≫ pullback.fst g q)
  have _ : IsLocallyNoetherian Bs := LocallyOfFiniteType.isLocallyNoetherian q
  have hsq := apply_comp_fst_eq_apply_comp_snd g q W v
  have hrEt : RingHom.IsEtaleLocalHom ((W.ι ≫ pullback.fst g q).stalkMap v).hom :=
    (etale_iff_forall_isEtaleAt (W.ι ≫ pullback.fst g q)).mp inferInstance v
  refine ⟨inferInstance, inferInstance, inferInstance,
    (isRegularLocalRing_stalk_iff_of_etale q _).mpr (hsq ▸ hY), ?_, ?_⟩
  · obtain ⟨hd, hic⟩ := hX.of_isLocalRing
    have hnd : IsNormalDomain (W.toScheme.presheaf.stalk v) :=
      (RingHom.isNormalDomain_iff_of_isEtaleLocalHom
        ((W.ι ≫ pullback.fst g q).stalkMap v).hom hrEt).mp ⟨hd, hic⟩
    have _ : IsDomain (W.toScheme.presheaf.stalk v) := hnd.isDomain
    have _ : IsIntegrallyClosed (W.toScheme.presheaf.stalk v) := hnd.isIntegrallyClosed
    exact IsNormalRing.of_isIntegrallyClosed _
  · rw [ringKrullDim_stalk_eq_of_etale (W.ι ≫ pullback.fst g q) v, hdim, hsq]
    exact (ringKrullDim_stalk_eq_of_etale q _).symm

/-- A morphism sends the point of `X` cut out by a prime `Q` of `𝒪_{X,x}` to the point of `Y` cut
out by the contraction of `Q` to `𝒪_{Y,f x}`. -/
private lemma apply_fromSpecStalk_eq {X Y : Scheme.{u}} (f : X ⟶ Y) (x : X)
    (Q : (Spec (X.presheaf.stalk x) : Scheme.{u})) :
    f (X.fromSpecStalk x Q) = Y.fromSpecStalk (f x) (Spec.map (f.stalkMap x) Q) := by
  rw [← Scheme.Hom.comp_apply, ← Scheme.SpecMap_stalkMap_fromSpecStalk f, Scheme.Hom.comp_apply]

/-- **An étale morphism lifts generizations.** A point `z'` specializing to `r v` is the image
under `r` of the point of `W` cut out by a prime of `𝒪_{W,v}`.

The generizations of `r v` are the primes of `𝒪_{V', r v}` ([Stacks, Tag 01J7]); the stalk map of
`r` is flat, so it has going down and such a prime is the contraction of a prime `Q` of `𝒪_{W,v}`;
and `r` carries the point cut out by `Q` to the point cut out by its contraction. -/
private lemma exists_apply_fromSpecStalk_eq_of_specializes_of_etale {W V' : Scheme.{u}}
    [IsLocallyNoetherian W] [IsLocallyNoetherian V']
    (r : W ⟶ V') [Etale r] (v : W) (z' : V') (hz' : z' ⤳ r v) :
    ∃ Q : (Spec (W.presheaf.stalk v) : Scheme.{u}), r (W.fromSpecStalk v Q) = z' := by
  obtain ⟨P, hP⟩ := (show z' ∈ Set.range (V'.fromSpecStalk (r v)) by
    simpa only [Scheme.range_fromSpecStalk, Set.mem_ofPred_eq] using hz')
  have hrEt : RingHom.IsEtaleLocalHom (r.stalkMap v).hom :=
    (etale_iff_forall_isEtaleAt r).mp inferInstance v
  let : Algebra (V'.presheaf.stalk (r v)) (W.presheaf.stalk v) := (r.stalkMap v).hom.toAlgebra
  have halgr : algebraMap (V'.presheaf.stalk (r v)) (W.presheaf.stalk v) =
      (r.stalkMap v).hom := RingHom.algebraMap_toAlgebra _
  have _ : Module.Flat (V'.presheaf.stalk (r v)) (W.presheaf.stalk v) :=
    RingHom.flat_algebraMap_iff.mp (halgr ▸ hrEt.1)
  have _ : Algebra.HasGoingDown (V'.presheaf.stalk (r v)) (W.presheaf.stalk v) :=
    Algebra.HasGoingDown.of_flat
  have _ : P.asIdeal.IsPrime := P.isPrime
  have hunder : Ideal.under (V'.presheaf.stalk (r v)) (maximalIdeal (W.presheaf.stalk v)) =
      maximalIdeal (V'.presheaf.stalk (r v)) := by
    rw [Ideal.under, halgr]
    exact IsLocalRing.maximalIdeal_comap (r.stalkMap v).hom
  obtain ⟨Q, hQover⟩ :
      ∃ Q : (Spec (W.presheaf.stalk v) : Scheme.{u}), Q.asIdeal.LiesOver P.asIdeal :=
    Stacks.PurityBranchLocus.exists_isPrime_liesOver_of_hasGoingDown hunder P.asIdeal
  have hmapQ : (Spec.map (r.stalkMap v)) Q = P := by
    refine PrimeSpectrum.ext ?_
    show Ideal.comap (r.stalkMap v).hom Q.asIdeal = P.asIdeal
    rw [← halgr]
    exact (hQover.over).symm
  exact ⟨Q, by rw [apply_fromSpecStalk_eq, hmapQ, hP]⟩

/-- **Going down for the finite morphism of the model**, in the form of equality of dimensions:
if `p : W ⟶ Bs` is finite with `v` the only point over `p v`, `𝒪_{Bs, p v}` is regular, `𝒪_{W,v}`
is normal and the two have the same dimension, then the dimensions of the local rings of `W` and
of `Bs` agree at the point cut out by any prime `Q` of `𝒪_{W,v}`.

Both sides are heights of corresponding primes ([Stacks, Tag 01J7]) — the local ring of `W` at `v`
is a finite algebra over that of `Bs` at `p v` ([Stacks, Tag 05B8]) — and those heights agree by
`Stacks.PurityBranchLocus.height_eq_height_of_finite_of_isRegularLocalRing`. -/
private lemma ringKrullDim_stalk_fromSpecStalk_eq_of_isFinite {W Bs : Scheme.{u}} (p : W ⟶ Bs)
    [IsFinite p] [IsLocallyNoetherian W] [IsLocallyNoetherian Bs] (v : W)
    (hvuniq : ∀ y : W, p y = p v → y = v)
    (hAreg : IsRegularLocalRing (Bs.presheaf.stalk (p v)))
    (hBnormal : IsNormalRing (W.presheaf.stalk v))
    (hdimAB : ringKrullDim (W.presheaf.stalk v) = ringKrullDim (Bs.presheaf.stalk (p v)))
    (Q : (Spec (W.presheaf.stalk v) : Scheme.{u})) :
    ringKrullDim (W.presheaf.stalk (W.fromSpecStalk v Q)) =
      ringKrullDim (Bs.presheaf.stalk (p (W.fromSpecStalk v Q))) := by
  have hfinstalk : (p.stalkMap v).hom.Finite :=
    finite_stalkMap_of_preimage_singleton p v
      (Set.eq_singleton_iff_unique_mem.mpr ⟨rfl, fun y hy => hvuniq y hy⟩)
  let : Algebra (Bs.presheaf.stalk (p v)) (W.presheaf.stalk v) := (p.stalkMap v).hom.toAlgebra
  have halgp : algebraMap (Bs.presheaf.stalk (p v)) (W.presheaf.stalk v) =
      (p.stalkMap v).hom := RingHom.algebraMap_toAlgebra _
  have _ : Module.Finite (Bs.presheaf.stalk (p v)) (W.presheaf.stalk v) :=
    RingHom.finite_algebraMap.mp (halgp ▸ hfinstalk)
  have hPprime : (Ideal.under (Bs.presheaf.stalk (p v)) Q.asIdeal).IsPrime :=
    Q.isPrime.comap (algebraMap (Bs.presheaf.stalk (p v)) (W.presheaf.stalk v))
  have hQP : Q.asIdeal.height = (Ideal.under (Bs.presheaf.stalk (p v)) Q.asIdeal).height := by
    have _ : Q.asIdeal.LiesOver (Ideal.under (Bs.presheaf.stalk (p v)) Q.asIdeal) := ⟨rfl⟩
    exact Stacks.PurityBranchLocus.height_eq_height_of_finite_of_isRegularLocalRing
      hAreg hBnormal hdimAB _ Q.asIdeal
  have hpw : p (W.fromSpecStalk v Q) = Bs.fromSpecStalk (p v)
      (⟨Ideal.under (Bs.presheaf.stalk (p v)) Q.asIdeal, hPprime⟩ : PrimeSpectrum _) := by
    rw [apply_fromSpecStalk_eq]
    congr 1
  calc ringKrullDim (W.presheaf.stalk (W.fromSpecStalk v Q))
      = (Q.asIdeal.height : WithBot ℕ∞) := ringKrullDim_stalk_fromSpecStalk W v Q
    _ = ((Ideal.under (Bs.presheaf.stalk (p v)) Q.asIdeal).height : WithBot ℕ∞) := by rw [hQP]
    _ = ringKrullDim (Bs.presheaf.stalk (p (W.fromSpecStalk v Q))) := by
        rw [hpw]
        exact (ringKrullDim_stalk_fromSpecStalk Bs (p v)
          (⟨Ideal.under (Bs.presheaf.stalk (p v)) Q.asIdeal, hPprime⟩ : PrimeSpectrum _)).symm

/-- In the situation of [Stacks, Tag 02LK] — a morphism `g` made finite near `z` by an elementary
étale change `q` of the base, with `v` the only point of the finite open `W` over the
distinguished point — the dimensions of the local rings of source and target agree at every point
specializing to `z`.

The generizations of `z` lift to generizations of `v` along the flat étale projection
(`AlgebraicGeometry.exists_apply_fromSpecStalk_eq_of_specializes_of_etale`), and there the two
dimensions agree because the finite local homomorphism `𝒪_{Bs,b} → 𝒪_{W,v}` has going down
(`AlgebraicGeometry.ringKrullDim_stalk_fromSpecStalk_eq_of_isFinite`). -/
private lemma ringKrullDim_stalk_eq_of_isFiniteNeighborhoodAt
    {V' U' : Scheme.{u}} (g : V' ⟶ U') [IsLocallyNoetherian V'] [IsLocallyNoetherian U']
    [LocallyOfFiniteType g] (z : V')
    {Bs : Scheme.{u}} (q : Bs ⟶ U') [Etale q] (b : Bs) (W : (pullback g q).Opens)
    (hfin : IsFinite (W.ι ≫ pullback.snd g q)) (v : W.toScheme)
    (hv : (W.ι ≫ pullback.snd g q) v = b)
    (hvuniq : ∀ y : W.toScheme, (W.ι ≫ pullback.snd g q) y = b → y = v)
    (hrv : (W.ι ≫ pullback.fst g q) v = z)
    (hX : IsNormalRing (V'.presheaf.stalk z))
    (hY : IsRegularLocalRing (U'.presheaf.stalk (g z)))
    (hdim : ringKrullDim (V'.presheaf.stalk z) = ringKrullDim (U'.presheaf.stalk (g z)))
    (z' : V') (hz' : z' ⤳ z) :
    ringKrullDim (V'.presheaf.stalk z') = ringKrullDim (U'.presheaf.stalk (g z')) := by
  subst hv
  subst hrv
  obtain ⟨_, _, _, hAreg, hBnormal, hdimAB⟩ :=
    etale_isLocallyNoetherian_isRegularLocalRing_isNormalRing_of_etale g q W v hX hY hdim
  set p := W.ι ≫ pullback.snd g q
  set r := W.ι ≫ pullback.fst g q
  -- The commuting square of the four points.
  have hsq : ∀ y : W.toScheme, g (r y) = q (p y) := apply_comp_fst_eq_apply_comp_snd g q W
  -- The generization `z'` of `z = r v` comes from a prime `Q` of `𝒪_{W,v}`.
  obtain ⟨Q, hQ⟩ := exists_apply_fromSpecStalk_eq_of_specializes_of_etale r v z' hz'
  calc ringKrullDim (V'.presheaf.stalk z')
      = ringKrullDim (W.toScheme.presheaf.stalk (W.toScheme.fromSpecStalk v Q)) := by
        rw [← hQ, ringKrullDim_stalk_eq_of_etale r (W.toScheme.fromSpecStalk v Q)]
    _ = ringKrullDim (Bs.presheaf.stalk (p (W.toScheme.fromSpecStalk v Q))) :=
        ringKrullDim_stalk_fromSpecStalk_eq_of_isFinite p v hvuniq hAreg hBnormal hdimAB Q
    _ = ringKrullDim (U'.presheaf.stalk (g z')) := by
        rw [ringKrullDim_stalk_eq_of_etale q (p (W.toScheme.fromSpecStalk v Q)),
          ← hsq (W.toScheme.fromSpecStalk v Q), hQ]

/-- A prime of the sections over an affine open `V` cut out by a point equal to `v` is the prime
cut out by `v`. -/
private lemma eq_primeIdealOf_of_fromSpec_eq {W : Scheme.{u}} {V : W.Opens} (hV : IsAffineOpen V)
    (J : PrimeSpectrum Γ(W, V)) {v : W} (hv : v ∈ V) (h : hV.fromSpec J = v) :
    J = hV.primeIdealOf ⟨v, hv⟩ := by
  rw [← hV.primeIdealOf_fromSpec J (hV.range_fromSpec.le ⟨_, rfl⟩)]
  congr 1
  exact Subtype.ext h

/-- **The prime cut out by `v` is the only one over the prime cut out by `p v`**, in the rings of
sections over an affine open `Ua` of `Bs` and its preimage in `W`, when `v` is the only point of
`W` over `p v`: a prime of `Γ(W, p ⁻¹ᵁ Ua)` lying over the prime of `Γ(Bs, Ua)` cut out by `p v`
is cut out by a point of `W` over `p v`, hence by `v`. -/
private lemma primesOver_eq_singleton_primeIdealOf_of_unique_preimage {W Bs : Scheme.{u}}
    (p : W ⟶ Bs) (v : W) (hvuniq : ∀ y : W, p y = p v → y = v)
    {Ua : Bs.Opens} (hUa : IsAffineOpen Ua) (hvUa : v ∈ p ⁻¹ᵁ Ua)
    (hVa : IsAffineOpen (p ⁻¹ᵁ Ua)) [Algebra Γ(Bs, Ua) Γ(W, p ⁻¹ᵁ Ua)]
    (halgTC : algebraMap Γ(Bs, Ua) Γ(W, p ⁻¹ᵁ Ua) = (p.appLE Ua (p ⁻¹ᵁ Ua) le_rfl).hom) :
    (hUa.primeIdealOf ⟨p v, hvUa⟩).asIdeal.primesOver Γ(W, p ⁻¹ᵁ Ua) =
      {(hVa.primeIdealOf ⟨v, hvUa⟩).asIdeal} := by
  have hcomapv : ∀ (y : W) (hy : y ∈ p ⁻¹ᵁ Ua),
      PrimeSpectrum.comap (p.appLE Ua (p ⁻¹ᵁ Ua) le_rfl).hom (hVa.primeIdealOf ⟨y, hy⟩) =
        hUa.primeIdealOf ⟨p y, hy⟩ := fun y hy =>
    IsAffineOpen.comap_primeIdealOf_appLE Ua hUa (p ⁻¹ᵁ Ua) hVa le_rfl hy
  have hliesOver : ∀ (y : W) (hy : y ∈ p ⁻¹ᵁ Ua),
      (hVa.primeIdealOf ⟨y, hy⟩).asIdeal.LiesOver (hUa.primeIdealOf ⟨p y, hy⟩).asIdeal :=
    fun y hy => ⟨by rw [Ideal.under, halgTC, ← hcomapv y hy]; rfl⟩
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨⟨inferInstance, hliesOver v hvUa⟩, fun J hJ => ?_⟩
  have _ : J.IsPrime := hJ.1
  set y := hVa.fromSpec (⟨J, hJ.1⟩ : PrimeSpectrum _)
  have hyVa : y ∈ p ⁻¹ᵁ Ua := hVa.range_fromSpec.le ⟨_, rfl⟩
  have hyJ : hVa.primeIdealOf ⟨y, hyVa⟩ = (⟨J, hJ.1⟩ : PrimeSpectrum _) :=
    hVa.primeIdealOf_fromSpec _ hyVa
  have hunder : (hUa.primeIdealOf ⟨p y, hyVa⟩) = (hUa.primeIdealOf ⟨p v, hvUa⟩) := by
    rw [← hcomapv y hyVa, ← hcomapv v hvUa, hyJ]
    refine PrimeSpectrum.ext ?_
    show Ideal.comap (p.appLE Ua (p ⁻¹ᵁ Ua) le_rfl).hom J = _
    rw [← halgTC, ← Ideal.under, ← (hJ.2).over, halgTC]
    exact (congrArg PrimeSpectrum.asIdeal (hcomapv v hvUa)).symm
  have hpy : p y = p v := by
    have h1 := hUa.fromSpec_primeIdealOf (⟨p y, hyVa⟩ : Ua)
    rw [hunder] at h1
    exact h1.symm.trans (hUa.fromSpec_primeIdealOf (⟨p v, hvUa⟩ : Ua))
  exact congrArg PrimeSpectrum.asIdeal
    (eq_primeIdealOf_of_fromSpec_eq hVa ⟨J, hJ.1⟩ hvUa (hvuniq y hpy))

/-- **Étaleness below the prime cut out by `v`.** A prime of `Γ(W, p ⁻¹ᵁ Ua)` strictly below the
one cut out by `v` is cut out by a proper generization of `v`, so `p` is étale there by
hypothesis, and étaleness of the stalk map is étaleness of the algebra of sections at that prime,
[Stacks, Tag 039N]. -/
private lemma isEtaleAt_of_lt_primeIdealOf {W Bs : Scheme.{u}} [IsLocallyNoetherian W]
    [IsLocallyNoetherian Bs] (p : W ⟶ Bs) [IsFinite p] (v : W)
    (haway : ∀ y : W, y ⤳ v → y ≠ v → EtaleAt p y)
    {Ua : Bs.Opens} (hUa : IsAffineOpen Ua) (hvUa : v ∈ p ⁻¹ᵁ Ua)
    (hVa : IsAffineOpen (p ⁻¹ᵁ Ua)) (J : Ideal Γ(W, p ⁻¹ᵁ Ua)) (hJ : J.IsPrime)
    (hJle : J ≤ (hVa.primeIdealOf ⟨v, hvUa⟩).asIdeal)
    (hJne : J ≠ (hVa.primeIdealOf ⟨v, hvUa⟩).asIdeal) :
    letI : Algebra Γ(Bs, Ua) Γ(W, p ⁻¹ᵁ Ua) := (p.appLE Ua (p ⁻¹ᵁ Ua) le_rfl).hom.toAlgebra
    Algebra.IsEtaleAt Γ(Bs, Ua) J := by
  set y := hVa.fromSpec (⟨J, hJ⟩ : PrimeSpectrum _)
  have hyVa : y ∈ p ⁻¹ᵁ Ua := hVa.range_fromSpec.le ⟨_, rfl⟩
  have hyJ : hVa.primeIdealOf ⟨y, hyVa⟩ = (⟨J, hJ⟩ : PrimeSpectrum _) :=
    hVa.primeIdealOf_fromSpec _ hyVa
  -- `y` is a proper generization of `v`.
  have hyv : y ⤳ v := by
    have hsp : (⟨J, hJ⟩ : PrimeSpectrum _) ⤳ (hVa.primeIdealOf ⟨v, hvUa⟩) :=
      (PrimeSpectrum.le_iff_specializes _ _).mp hJle
    have := hVa.fromSpec.base.hom.map_specializes hsp
    rwa [hVa.fromSpec_primeIdealOf (⟨v, hvUa⟩ : _)] at this
  have hyne : y ≠ v := by
    intro hcon
    refine hJne ?_
    exact congrArg PrimeSpectrum.asIdeal
      (eq_primeIdealOf_of_fromSpec_eq hVa ⟨J, hJ⟩ hvUa hcon)
  have hstalkEt : RingHom.IsEtaleLocalHom (p.stalkMap y).hom :=
    (isEtaleAt_iff_etaleAt p y).mpr (haway y hyv hyne)
  have := (isEtaleLocalHom_iff_isEtaleAt_affine p y (p ⁻¹ᵁ Ua) hVa hyVa Ua hUa le_rfl).mp
    hstalkEt
  rwa [hyJ] at this

/-- **Cohen–Macaulayness of the local ring at `v` for a finite morphism**, granted
[Stacks, Tag 0BMA] clause (2) in the shape `Stacks.PurityBranchLocus.PurityFiniteNormal`: if
`p : W ⟶ Bs` is finite with `v` the only point over `p v`, if `𝒪_{Bs, p v}` is regular of
dimension at least two and `𝒪_{W,v}` is normal of the same dimension, and if `p` is étale at
every point strictly specializing to `v`, then `𝒪_{W,v}` is Cohen–Macaulay.

The two local rings are the localizations of the rings of sections over an affine open `Ua` of
`Bs` and its preimage in `W`, at the primes cut out by `p v` and by `v`, and the one is a finite
algebra over the other ([Stacks, Tag 05B8]). That is precisely the situation of
`Stacks.PurityBranchLocus.isCohenMacaulayLocalRing_of_purityFiniteNormal`. -/
private lemma isCohenMacaulayLocalRing_stalk_of_purityFiniteNormal
    (hPurity : Stacks.PurityBranchLocus.PurityFiniteNormal.{u})
    {W Bs : Scheme.{u}} [IsLocallyNoetherian W] [IsLocallyNoetherian Bs] (p : W ⟶ Bs)
    [IsFinite p] (v : W) (hvuniq : ∀ y : W, p y = p v → y = v)
    (hAreg : IsRegularLocalRing (Bs.presheaf.stalk (p v)))
    (hBnormal : IsNormalRing (W.presheaf.stalk v))
    (hdimAB : ringKrullDim (W.presheaf.stalk v) = ringKrullDim (Bs.presheaf.stalk (p v)))
    (hdim2 : (2 : WithBot ℕ∞) ≤ ringKrullDim (Bs.presheaf.stalk (p v)))
    (haway : ∀ y : W, y ⤳ v → y ≠ v → EtaleAt p y) :
    IsCohenMacaulayLocalRing (W.presheaf.stalk v) := by
  -- An affine open of the base and its preimage, over which `p` is a finite ring map.
  obtain ⟨Ua, hUa, hbUa, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show p v ∈ (⊤ : Bs.Opens) by simp)
  have hVa : IsAffineOpen (p ⁻¹ᵁ Ua) := hUa.preimage p
  have hvVa : v ∈ p ⁻¹ᵁ Ua := hbUa
  let : Algebra Γ(Bs, Ua) Γ(W, p ⁻¹ᵁ Ua) := (p.appLE Ua (p ⁻¹ᵁ Ua) le_rfl).hom.toAlgebra
  have halgTC : algebraMap Γ(Bs, Ua) Γ(W, p ⁻¹ᵁ Ua) =
      (p.appLE Ua (p ⁻¹ᵁ Ua) le_rfl).hom := RingHom.algebraMap_toAlgebra _
  have _ : Module.Finite Γ(Bs, Ua) Γ(W, p ⁻¹ᵁ Ua) := by
    refine RingHom.finite_algebraMap.mp (halgTC ▸ ?_)
    rw [Scheme.Hom.appLE_eq_app]
    exact p.finite_app Ua hUa
  set 𝔭 : Ideal Γ(Bs, Ua) := (hUa.primeIdealOf ⟨p v, hbUa⟩).asIdeal
  set 𝔮 : Ideal Γ(W, p ⁻¹ᵁ Ua) := (hVa.primeIdealOf ⟨v, hvVa⟩).asIdeal
  have _ : 𝔭.IsPrime := (hUa.primeIdealOf ⟨p v, hbUa⟩).isPrime
  have _ : 𝔮.IsPrime := (hVa.primeIdealOf ⟨v, hvVa⟩).isPrime
  let : Algebra Γ(Bs, Ua) (Bs.presheaf.stalk (p v)) :=
    TopCat.Presheaf.algebra_section_stalk Bs.presheaf (⟨p v, hbUa⟩ : Ua)
  let : Algebra Γ(W, p ⁻¹ᵁ Ua) (W.presheaf.stalk v) :=
    TopCat.Presheaf.algebra_section_stalk W.presheaf (⟨v, hvVa⟩ : (p ⁻¹ᵁ Ua))
  have _ : IsLocalization.AtPrime (Bs.presheaf.stalk (p v)) 𝔭 :=
    hUa.isLocalization_stalk ⟨p v, hbUa⟩
  have _ : IsLocalization.AtPrime (W.presheaf.stalk v) 𝔮 :=
    hVa.isLocalization_stalk ⟨v, hvVa⟩
  let : Algebra (Bs.presheaf.stalk (p v)) (W.presheaf.stalk v) := (p.stalkMap v).hom.toAlgebra
  let : Algebra Γ(Bs, Ua) (W.presheaf.stalk v) :=
    ((W.presheaf.germ (p ⁻¹ᵁ Ua) v hvVa).hom.comp
      (p.appLE Ua (p ⁻¹ᵁ Ua) le_rfl).hom).toAlgebra
  have _ : IsScalarTower Γ(Bs, Ua) Γ(W, p ⁻¹ᵁ Ua) (W.presheaf.stalk v) :=
    IsScalarTower.of_algebraMap_eq fun _ => rfl
  have _ : IsScalarTower Γ(Bs, Ua) (Bs.presheaf.stalk (p v)) (W.presheaf.stalk v) :=
    IsScalarTower.of_algebraMap_eq fun y => by
      show (W.presheaf.germ (p ⁻¹ᵁ Ua) v hvVa).hom ((p.appLE Ua (p ⁻¹ᵁ Ua) le_rfl).hom y) =
        (p.stalkMap v).hom ((Bs.presheaf.germ Ua (p v) hbUa).hom y)
      rw [Scheme.Hom.appLE_eq_app, Scheme.Hom.germ_stalkMap_apply]
  have huniq : 𝔭.primesOver Γ(W, p ⁻¹ᵁ Ua) = {𝔮} :=
    primesOver_eq_singleton_primeIdealOf_of_unique_preimage p v hvuniq hUa hvVa hVa halgTC
  exact Stacks.PurityBranchLocus.isCohenMacaulayLocalRing_of_purityFiniteNormal hPurity 𝔭 𝔮
    huniq hAreg hBnormal hdimAB hdim2
    fun J hJ hJle hJne => isEtaleAt_of_lt_primeIdealOf p v haway hUa hvVa hVa J hJ hJle hJne

/-- In the situation of [Stacks, Tag 02LK] — a morphism `g` made finite near `z` by an elementary
étale change `q` of the base, with `v` the only point of the finite open `W` over the
distinguished point — the local ring at `z` is Cohen–Macaulay as soon as `g` is étale at every
point strictly specializing to `z`, granted [Stacks, Tag 0BMA] clause (2) in the shape
`Stacks.PurityBranchLocus.PurityFiniteNormal`.

Cohen–Macaulayness of `𝒪_{W,v}` is
`AlgebraicGeometry.isCohenMacaulayLocalRing_stalk_of_purityFiniteNormal`, applied to the finite
morphism `W ⟶ Bs`; its hypothesis of étaleness at the points strictly generizing `v` is what
[Stacks, Tag 039N] reads off the hypothesis on `g`. Cohen–Macaulayness then descends to
`𝒪_{V',z}` along the étale projection, [Stacks, Tag 025Q]. -/
private lemma isCohenMacaulayLocalRing_stalk_of_isFiniteNeighborhoodAt
    (hPurity : Stacks.PurityBranchLocus.PurityFiniteNormal.{u})
    {V' U' : Scheme.{u}} (g : V' ⟶ U') [IsLocallyNoetherian V'] [IsLocallyNoetherian U']
    [LocallyOfFiniteType g] (z : V')
    {Bs : Scheme.{u}} (q : Bs ⟶ U') [Etale q] (b : Bs) (W : (pullback g q).Opens)
    (hfin : IsFinite (W.ι ≫ pullback.snd g q)) (v : W.toScheme)
    (hv : (W.ι ≫ pullback.snd g q) v = b)
    (hvuniq : ∀ y : W.toScheme, (W.ι ≫ pullback.snd g q) y = b → y = v)
    (hrv : (W.ι ≫ pullback.fst g q) v = z)
    (hX : IsNormalRing (V'.presheaf.stalk z))
    (hY : IsRegularLocalRing (U'.presheaf.stalk (g z)))
    (hdim : ringKrullDim (V'.presheaf.stalk z) = ringKrullDim (U'.presheaf.stalk (g z)))
    (hdim2 : (2 : WithBot ℕ∞) ≤ ringKrullDim (V'.presheaf.stalk z))
    (haway : ∀ z' : V', z' ⤳ z → z' ≠ z → EtaleAt g z') :
    IsCohenMacaulayLocalRing (V'.presheaf.stalk z) := by
  subst hv
  subst hrv
  obtain ⟨_, _, _, hAreg, hBnormal, hdimAB⟩ :=
    etale_isLocallyNoetherian_isRegularLocalRing_isNormalRing_of_etale g q W v hX hY hdim
  set p := W.ι ≫ pullback.snd g q with hp
  set r := W.ι ≫ pullback.fst g q with hr
  have hrEt : RingHom.IsEtaleLocalHom (r.stalkMap v).hom :=
    (etale_iff_forall_isEtaleAt r).mp inferInstance v
  -- Étaleness of `p` at the proper generizations of `v`, from that of `g` at those of `z = r v`.
  have hawayp : ∀ y : W.toScheme, y ⤳ v → y ≠ v → EtaleAt p y := by
    intro y hyv hyne
    have hrne : r y ≠ r v := by
      intro hcon
      have hlt := ringKrullDim_stalk_lt_of_specializes hyv hyne
      rw [ringKrullDim_stalk_eq_of_etale r y, ringKrullDim_stalk_eq_of_etale r v, hcon] at hlt
      exact lt_irrefl _ hlt
    have hEtsnd : EtaleAt (pullback.snd g q) (W.ι y) := by
      refine (etaleAt_iff_of_isPullback (IsPullback.of_hasPullback g q)
        (Or.inr (inferInstance : Flat q)) (W.ι y)).mp ?_
      have hr' : pullback.fst g q (W.ι y) = r y := by rw [hr, Scheme.Hom.comp_apply]
      rw [hr']
      exact haway (r y) (r.base.hom.map_specializes hyv) hrne
    rw [hp]
    exact etaleAt_comp W.ι (pullback.snd g q) (x := y)
      ((etale_iff_forall_etaleAt W.ι).mp inferInstance y) hEtsnd
  have hCM : IsCohenMacaulayLocalRing (W.toScheme.presheaf.stalk v) :=
    isCohenMacaulayLocalRing_stalk_of_purityFiniteNormal hPurity p v hvuniq hAreg hBnormal hdimAB
      (by rwa [← hdimAB, ringKrullDim_stalk_eq_of_etale r v]) hawayp
  exact (RingHom.isCohenMacaulayLocalRing_iff_of_isEtaleLocalHom (r.stalkMap v).hom hrEt).mpr hCM

/-- **Restriction to the quasi-finite locus.** If `f` is quasi-finite at `x` and `𝒪_{X,x}` is
normal, the point `x` lifts to a point `x₁` of the quasi-finite locus, which is locally Noetherian,
at which `ι ≫ f` is quasi-finite and whose local ring is normal of the same dimension as `𝒪_{X,x}`
(an open immersion changes neither). -/
private lemma exists_quasiFiniteAt_restrict_quasiFiniteLocus {X Y : Scheme.{u}} (f : X ⟶ Y)
    [IsLocallyNoetherian X] (x : X) (hX : IsNormalRing (X.presheaf.stalk x))
    (hqf : quasiFiniteAt f x) :
    ∃ x₁ : (quasiFiniteLocus f).toScheme, (quasiFiniteLocus f).ι x₁ = x ∧
      IsLocallyNoetherian (quasiFiniteLocus f).toScheme ∧
      ringKrullDim ((quasiFiniteLocus f).toScheme.presheaf.stalk x₁) =
        ringKrullDim (X.presheaf.stalk x) ∧
      IsNormalRing ((quasiFiniteLocus f).toScheme.presheaf.stalk x₁) ∧
      quasiFiniteAt ((quasiFiniteLocus f).ι ≫ f) x₁ := by
  let x₁ : (quasiFiniteLocus f).toScheme := ⟨x, (mem_quasiFiniteLocus_iff f x).mpr hqf⟩
  exact ⟨x₁, rfl, LocallyOfFiniteType.isLocallyNoetherian (quasiFiniteLocus f).ι,
    ringKrullDim_stalk_eq_of_etale (quasiFiniteLocus f).ι x₁,
    IsNormalRing.congr (asIso ((quasiFiniteLocus f).ι.stalkMap x₁)).commRingCatIsoToRingEquiv hX,
    ⟨finiteTypeAt_of_locallyOfFiniteType ((quasiFiniteLocus f).ι ≫ f) x₁,
      Scheme.Hom.quasiFiniteAt_comp_iff_of_isOpenImmersion.mpr hqf.2⟩⟩

/-! ### Equality of dimensions at the generizations -/

/-- **The dimensions of the two local rings agree at every generization of a quasi-finite point.**
Let `f : X ⟶ Y` be a morphism of locally Noetherian schemes which is quasi-finite at `x`, with
`𝒪_{X,x}` normal, `𝒪_{Y,f x}` regular and the two of the same dimension. Then
`dim 𝒪_{X,x'} = dim 𝒪_{Y,f x'}` for every point `x'` specializing to `x`.

This is the going-down step of the proof of [Stacks, Tag 0BMB]. After an elementary étale change
of the base, [Stacks, Tag 02LK], the morphism is finite near `x`, and there going down is
available: see `AlgebraicGeometry.ringKrullDim_stalk_eq_of_isFiniteNeighborhoodAt`. The passage to
that model is harmless because the quasi-finite locus is open, so it contains every generization
of `x`, and because an open immersion changes neither the dimension nor the normality of a local
ring. -/
public theorem ringKrullDim_stalk_eq_of_specializes_of_quasiFiniteAt
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : X)
    (hX : IsNormalRing (X.presheaf.stalk x))
    (hY : IsRegularLocalRing (Y.presheaf.stalk (f x)))
    (hqf : quasiFiniteAt f x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (x' : X) (hx' : x' ⤳ x) :
    ringKrullDim (X.presheaf.stalk x') = ringKrullDim (Y.presheaf.stalk (f x')) := by
  classical
  obtain ⟨x₁, rfl, _, hdimZ, hXZ, hqfZ⟩ :=
    exists_quasiFiniteAt_restrict_quasiFiniteLocus f x hX hqf
  set x'₁ : (quasiFiniteLocus f).toScheme := ⟨x', hx'.mem_open (quasiFiniteLocus f).2 x₁.2⟩
  have hspec : x'₁ ⤳ x₁ :=
    ((quasiFiniteLocus f).ι.isEmbedding.isInducing).specializes_iff.mp hx'
  -- Make the morphism finite near the point and run the going-down step there.
  obtain ⟨N⟩ := Stacks.Flatness.exists_etaleNeighborhood_finiteAt
    ((quasiFiniteLocus f).ι ≫ f) x₁
    (((quasiFiniteAt_tfae ((quasiFiniteLocus f).ι ≫ f) x₁).out 1 2).mp hqfZ)
  obtain ⟨hfin, ⟨v, hv, hvuniq⟩, hvspec⟩ := N.spec
  exact (ringKrullDim_stalk_eq_of_etale (quasiFiniteLocus f).ι x'₁).symm.trans <|
    ringKrullDim_stalk_eq_of_isFiniteNeighborhoodAt
    ((quasiFiniteLocus f).ι ≫ f) x₁ N.neighborhood.toBase N.neighborhood.point N.openSubscheme
    hfin v hv hvuniq (hvspec v hv).1 hXZ hY (by rwa [hdimZ]) x'₁ hspec

/-! ### Cohen–Macaulayness of the local ring at the point -/

/-- **The local ring at a quasi-finite point is Cohen–Macaulay**, granted [Stacks, Tag 0BMA]
clause (2) in the shape `Stacks.PurityBranchLocus.PurityFiniteNormal`. Let `f : X ⟶ Y` be a
morphism of locally Noetherian schemes which is quasi-finite at `x`, with `𝒪_{X,x}` normal,
`𝒪_{Y,f x}` regular and the two of the same dimension, at least two, and assume `f` is étale at
every point strictly specializing to `x`. Then `𝒪_{X,x}` is Cohen–Macaulay.

This is the étale-local reduction of [Stacks, Tag 0BMB] to [Stacks, Tag 0BMA]; see
`AlgebraicGeometry.isCohenMacaulayLocalRing_stalk_of_isFiniteNeighborhoodAt` for the step carried
out in the finite model. -/
public theorem isMaximalCohenMacaulay_stalk_of_etaleAt_generizations
    (hPurity : Stacks.PurityBranchLocus.PurityFiniteNormal.{u})
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : X)
    (hX : IsNormalRing (X.presheaf.stalk x))
    (hY : IsRegularLocalRing (Y.presheaf.stalk (f x)))
    (hqf : quasiFiniteAt f x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (hdim2 : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x))
    (haway : ∀ x' : X, x' ⤳ x → x' ≠ x → EtaleAt f x') :
    Module.IsMaximalCohenMacaulay (X.presheaf.stalk x) (X.presheaf.stalk x) := by
  classical
  obtain ⟨x₁, rfl, _, hdimZ, hXZ, hqfZ⟩ :=
    exists_quasiFiniteAt_restrict_quasiFiniteLocus f x hX hqf
  -- Étaleness at the proper generizations transfers to the restriction.
  have hawayZ : ∀ z : (quasiFiniteLocus f).toScheme, z ⤳ x₁ → z ≠ x₁ →
      EtaleAt ((quasiFiniteLocus f).ι ≫ f) z := by
    intro z hz hne
    refine etaleAt_comp (quasiFiniteLocus f).ι f (x := z)
      ((etale_iff_forall_etaleAt (quasiFiniteLocus f).ι).mp inferInstance z) ?_
    exact haway ((quasiFiniteLocus f).ι z) ((quasiFiniteLocus f).ι.base.hom.map_specializes hz)
      fun hcon => hne (Subtype.ext hcon)
  -- Make the morphism finite near the point and run the Cohen–Macaulay step there.
  obtain ⟨N⟩ := Stacks.Flatness.exists_etaleNeighborhood_finiteAt
    ((quasiFiniteLocus f).ι ≫ f) x₁
    (((quasiFiniteAt_tfae ((quasiFiniteLocus f).ι ≫ f) x₁).out 1 2).mp hqfZ)
  obtain ⟨hfin, ⟨v, hv, hvuniq⟩, hvspec⟩ := N.spec
  have hCMZ : IsCohenMacaulayLocalRing
      ((quasiFiniteLocus f).toScheme.presheaf.stalk x₁) :=
    isCohenMacaulayLocalRing_stalk_of_isFiniteNeighborhoodAt hPurity
      ((quasiFiniteLocus f).ι ≫ f) x₁ N.neighborhood.toBase N.neighborhood.point
      N.openSubscheme hfin v hv hvuniq (hvspec v hv).1 hXZ hY
      (by rwa [hdimZ]) (by rwa [hdimZ]) hawayZ
  refine (isCohenMacaulayLocalRing_iff_isMaximalCohenMacaulay _).mp ?_
  exact (isCohenMacaulayLocalRing_iff_of_ringEquiv
    (asIso ((quasiFiniteLocus f).ι.stalkMap x₁)).commRingCatIsoToRingEquiv).mpr hCMZ

/-! ### The induction on the dimension -/

/-- **Purity of the branch locus, [Stacks, Tag 0BMB], in any dimension.** Let `f : X ⟶ Y` be a
morphism of locally Noetherian schemes and let `x : X` be a point whose local ring is normal,
with regular local ring at `f x`, at which `f` is quasi-finite, and such that the two local rings
have the same dimension, which is at least one. If `f` is unramified at every point specializing
to `x` whose local ring has dimension one, then `f` is étale at `x`.

The hypotheses are exactly the tag's own.

The proof is the source's induction on `d = dim 𝒪_{X,x}`. For `d ≤ 2` the conclusion is
`AlgebraicGeometry.etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_dim_le_two`. For
`d ≥ 3` the induction hypothesis gives étaleness at every proper generization of `x` — their local
rings are normal, the local rings below them regular, `f` is quasi-finite there because the
quasi-finite locus is open, and the two dimensions agree there by
`AlgebraicGeometry.ringKrullDim_stalk_eq_of_specializes_of_quasiFiniteAt` — and that is what makes
`𝒪_{X,x}` Cohen–Macaulay, whence the conclusion. The Cohen–Macaulay step is where
[Stacks, Tag 0BMA] clause (2) enters, through
`Stacks.PurityBranchLocus.purityFiniteNormal`. -/
@[stacks 0BMB "the whole tag, in every dimension: hypotheses (1) `𝒪_{X,x}` normal, (2) \
`𝒪_{Y,f x}` regular, (3) `f` quasi-finite at `x`, (4) \
`dim 𝒪_{X,x} = dim 𝒪_{Y,f x}` and `1 ≤ dim 𝒪_{X,x}`, and (5) `f` unramified at every point \
specializing to `x` whose local ring has dimension one; the conclusion is `EtaleAt f x`. The \
proof is the source's induction on `dim 𝒪_{X,x}`, with the case `dim 𝒪_{X,x} ≤ 2` as its base \
case and tag 0BMA clause (2) in every dimension, \
`Stacks.PurityDimensionTwo.etale_of_isNormalRing_of_two_le_ringKrullDim`, supplying \
Cohen–Macaulayness of `𝒪_{X,x}` above it.",
  ega "IV 21.12.14" "(v), (v), special case",
  sga "1 X 3.1" "more general",
  sga "1 X 3.2" "more general"]
public theorem etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne
    {X Y : Scheme.{u}} (f : X ⟶ Y) [IsLocallyNoetherian X] [IsLocallyNoetherian Y] (x : X)
    (hX : IsNormalRing (X.presheaf.stalk x))
    (hY : IsRegularLocalRing (Y.presheaf.stalk (f x)))
    (hqf : quasiFiniteAt f x)
    (hdim : ringKrullDim (X.presheaf.stalk x) = ringKrullDim (Y.presheaf.stalk (f x)))
    (hone : 1 ≤ ringKrullDim (X.presheaf.stalk x))
    (hunr : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 → UnramifiedAt f x') :
    EtaleAt f x := by
  obtain ⟨d, hd⟩ :=
    Stacks.ApproximationProperty.exists_natCast_eq_ringKrullDim (X.presheaf.stalk x)
  induction d using Nat.strong_induction_on generalizing X Y with
  | h d ih =>
    by_cases hle2 : ringKrullDim (X.presheaf.stalk x) ≤ 2
    · exact etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_dim_le_two f x hX hY
        hqf hdim hone hle2 hunr
    have h2 : (2 : WithBot ℕ∞) ≤ ringKrullDim (X.presheaf.stalk x) := (not_le.mp hle2).le
    -- Étaleness at a proper generization of positive local dimension, by induction.
    have hgen : ∀ x' : X, x' ⤳ x → x' ≠ x → 1 ≤ ringKrullDim (X.presheaf.stalk x') →
        EtaleAt f x' := by
      intro x' hx' hne hpos
      obtain ⟨e, he⟩ :=
        Stacks.ApproximationProperty.exists_natCast_eq_ringKrullDim (X.presheaf.stalk x')
      have hlt : e < d := by
        have hh := ringKrullDim_stalk_lt_of_specializes hx' hne
        rw [hd, he] at hh
        exact_mod_cast hh
      have hqf' : quasiFiniteAt f x' := (mem_quasiFiniteLocus_iff f x').mp
        (hx'.mem_open (quasiFiniteLocus f).2 ((mem_quasiFiniteLocus_iff f x).mpr hqf))
      exact ih e hlt f x' (isNormalRing_stalk_of_specializes hx' hX)
        (isRegularLocalRing_stalk_of_specializes (f.base.hom.map_specializes hx') hY) hqf'
        (ringKrullDim_stalk_eq_of_specializes_of_quasiFiniteAt f x hX hY hqf hdim x' hx')
        hpos (fun w hw hdw => hunr w (hw.trans hx') hdw) he
    -- Étaleness at the one-dimensional generizations, and then at every proper generization.
    have hetale1 : ∀ x' : X, x' ⤳ x → ringKrullDim (X.presheaf.stalk x') = 1 →
        EtaleAt f x' := by
      intro x' hx' hd1
      rcases eq_or_ne x' x with rfl | hne
      · exact absurd (hd1 ▸ h2) (by norm_num)
      · exact hgen x' hx' hne (le_of_eq hd1.symm)
    have haway : ∀ x' : X, x' ⤳ x → x' ≠ x → EtaleAt f x' := by
      intro x' hx' hne
      by_cases hzero : ringKrullDim (X.presheaf.stalk x') = 0
      · exact etaleAt_generization_of_ringKrullDim_stalk_eq_zero f hX.of_isLocalRing.1
          hone hetale1 hx' hzero
      obtain ⟨e, he⟩ :=
        Stacks.ApproximationProperty.exists_natCast_eq_ringKrullDim (X.presheaf.stalk x')
      refine hgen x' hx' hne ?_
      rw [he]
      exact_mod_cast Nat.one_le_iff_ne_zero.mpr
        (fun hh => hzero (by simp only [he, hh, Nat.cast_zero]))
    exact etaleAt_of_quasiFiniteAt_of_unramifiedAt_codimensionOne_of_isMaximalCohenMacaulay f x
      (isMaximalCohenMacaulay_stalk_of_etaleAt_generizations
        Stacks.PurityBranchLocus.purityFiniteNormal f x hX hY hqf hdim h2 haway)
      hY hqf hdim hone hunr

end AlgebraicGeometry

end
