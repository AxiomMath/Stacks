module

public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.BoundedCoherentConditions
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.PerfectPreservation
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedTensorTorAmplitudeOver
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibres
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectObjectCanonical
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectPerfectObjectsCanonical
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectProperPushforwardBaseChange
public import StacksFrontier.AlgebraicGeometry.Perfect.TensorFinitelyPresentedPerfect
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.TorDimensionDirectImage
import StacksCore.Tactic.StacksAttribute

/-!
# Six criteria for a Fourier-Mukai functor to preserve perfect objects

Let `S` be a scheme, let `X` and `Y` be schemes over `S` and let `K ∈ D(𝒪_{X ×_S Y})`.
[Stacks, Tag 0FYT] asserts that the Fourier-Mukai functor

`Φ_K : D(𝒪_X) ⟶ D(𝒪_Y)`,  `M ⟼ R pr_{2,*}(L pr_1^* M ⊗^𝐋_{𝒪_{X ×_S Y}} K)`

of [Stacks, Tag 0FYQ] sends `D_perf(𝒪_X)` into `D_perf(𝒪_Y)` as soon as one of six conditions
holds. This file proves each of the six clauses under exactly the hypotheses of the source, one
theorem per clause. Nothing is assumed about `Y` beyond what the clause states.

Throughout, `T = L pr_1^* M ⊗^𝐋 K` (`AlgebraicGeometry.fourierMukaiKernelTensor`), so that
`Φ_K(M) = R pr_{2,*} T`. If `M` is perfect then so is `L pr_1^* M` ([Stacks, Tag 09UA],
`AlgebraicGeometry.isPerfect_fourierMukaiPullback`), and the properties of `X ⟶ S` used below
pass to `pr_2 : X ×_S Y ⟶ Y` by base change ([Stacks, Tag 01T4], [Stacks, Tag 01W4],
[Stacks, Tag 01U9], [Stacks, Tag 01TS]); the latter are Mathlib's base-change instances and are
found by instance search.

## Main results

* `exists_hasTorAmplitudeOver_derivedTensor_of_compactSpace`: on a quasi-compact scheme, tensoring
  with a perfect object preserves finite Tor dimension over the base.
* `isPerfect_fourierMukai_of_boundedCoherent_kernel`: clause (1).
* `isPerfect_fourierMukai_of_flatProperSupportFinitelyPresented_kernel`: clause (2).
* `isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation`: clause (3).
* `isPerfect_fourierMukai_of_isPerfect_kernel_of_noetherian_properFlat`: clause (4).
* `isPerfect_fourierMukai_of_isRelativelyPerfect_kernel_of_properFlatFinitePresentation`:
  clause (5).
* `isPerfect_fourierMukai_of_isRelativelyPerfect_kernel_of_noetherian_properFlat`: clause (6).

## Implementation notes

*Clause (1)* follows the source: [Stacks, Tag 08EV] for `pr_2` applied to `T`. Its four
hypotheses on `T` are derived from the source's hypotheses on `K`: the cohomology sheaves of `T`
are coherent (`AlgebraicGeometry.isCoherent_homology_fourierMukaiTensor`, which uses
[Stacks, Tag 0FXU] for `M`); their supports lie in the union of the supports of the finitely many
nonzero `H^j(K)` and so are proper over `Y`
(`AlgebraicGeometry.isProperOver_supp_homology_fourierMukaiTensor`); `T` has finite Tor dimension
over `pr_2^{-1}𝒪_Y` because `K` does and `L pr_1^* M` is perfect on the quasi-compact scheme
`X ×_S Y` (`AlgebraicGeometry.exists_hasTorAmplitudeOver_derivedTensor_of_compactSpace`); and an
object of Tor amplitude in `[a, b]` over the base has its cohomology in `[a, b]`
(`AlgebraicGeometry.isZero_homology_of_hasTorAmplitudeOver`), which bounds `T` on both sides.

*Clause (2)* is [Stacks, Tag 0A1H] for `pr_2`, with `E = L pr_1^* M` and `𝒢^• = 𝒦^•`, as in the
source.

*Clause (3).* The source cites [Stacks, Tag 0B91]. The route taken is the one of clause (5),
which contains it: `T` is perfect ([Stacks, Tag 09UA] and [Stacks, Tag 09J5],
`AlgebraicGeometry.isPerfect_fourierMukaiTensor`), hence `Y`-perfect by the first assertion of
[Stacks, Tag 0DI4], and [Stacks, Tag 0DJT] makes `R pr_{2,*} T` perfect.

*Clause (5)* is the source's: the second assertion of [Stacks, Tag 0DI4] makes `T` `Y`-perfect and
[Stacks, Tag 0DJT] concludes. `Y`-perfectness is [Stacks, Tag 0DI0],
`AlgebraicGeometry.Scheme.Hom.IsRelativelyPerfect`.

*Clauses (4) and (6)* reduce to (3) and (5) through [Stacks, Tag 01TX]: a proper morphism to a
Noetherian scheme is of finite type, hence locally of finite presentation, and that instance is
found by instance search.

The six theorems are new declarations; the conditional forms of the same clauses in
`StacksFrontier/AlgebraicGeometry/DerivedVarieties/FourierMukai/PerfectPreservation.lean` are left
unchanged.

## References

* [Stacks Project, Tag 0FYT](https://stacks.math.columbia.edu/tag/0FYT)
* [Stacks Project, Tag 0FYQ](https://stacks.math.columbia.edu/tag/0FYQ)
* [Stacks Project, Tag 08EV](https://stacks.math.columbia.edu/tag/08EV)
* [Stacks Project, Tag 0FXU](https://stacks.math.columbia.edu/tag/0FXU)
* [Stacks Project, Tag 0A1H](https://stacks.math.columbia.edu/tag/0A1H)
* [Stacks Project, Tag 0B91](https://stacks.math.columbia.edu/tag/0B91)
* [Stacks Project, Tag 0DI0](https://stacks.math.columbia.edu/tag/0DI0)
* [Stacks Project, Tag 0DI4](https://stacks.math.columbia.edu/tag/0DI4)
* [Stacks Project, Tag 0DJT](https://stacks.math.columbia.edu/tag/0DJT)
* [Stacks Project, Tag 01TX](https://stacks.math.columbia.edu/tag/01TX)
* [Stacks Project, Tag 09UA](https://stacks.math.columbia.edu/tag/09UA)
* [Stacks Project, Tag 0B66](https://stacks.math.columbia.edu/tag/0B66)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open Stacks.Cohomology.PerfectComplexes (IsPerfect)
open StacksDraft.TorAmplitude

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {S X Y : Scheme.{u}} (f : X ⟶ S) (g : Y ⟶ S)

/-! ### Tor amplitude over the base of `L pr_1^* M ⊗^𝐋 K` -/

section TorAmplitude

variable {Z W : Scheme.{u}} (p : Z ⟶ W)
  [(Stacks.SheafOfModules.Tensor.sheafTensor Z.toRingedSpace.sheaf).Additive]
  [∀ M, ((Stacks.SheafOfModules.Tensor.sheafTensor Z.toRingedSpace.sheaf).obj M).Additive]
  [∀ K L : CochainComplex (Stacks.DerivedTensor.RingedSite.Modules Z.toRingedSpace.sheaf) ℤ,
    HomologicalComplex.HasMapBifunctor K L
      (Stacks.SheafOfModules.Tensor.sheafTensor Z.toRingedSpace.sheaf) (ComplexShape.up ℤ)]

/-- **Tensoring with a perfect object on a quasi-compact scheme preserves finite Tor dimension
over the base.** Let `p : Z ⟶ W` be a morphism of schemes with `Z` quasi-compact, let `E` be a
perfect object of `D(𝒪_Z)` and let `F ∈ D(𝒪_Z)` have Tor amplitude in `[c, d]` over `W`. Then
`E ⊗^𝐋 F` has finite Tor dimension over `W`.

Perfectness gives an open covering of `Z` on each member of which `E` has Tor amplitude in an
interval ([Stacks, Tag 08CS]), hence so does each of its stalks ([Stacks, Tag 09U9]); finitely
many members cover `Z`, so one interval `[a, b]` bounds every stalk of `E`. At every point the
derived stalk of `E ⊗^𝐋 F` is the derived tensor product of the stalks, and [Stacks, Tag 0B66]
bounds it, read over the local ring of `W`, by `[a + c, b + d]`. -/
theorem exists_hasTorAmplitudeOver_derivedTensor_of_compactSpace [CompactSpace Z]
    (T : Stacks.DerivedTensor.RingedSite.DerivedTensorProduct Z.toRingedSpace.sheaf)
    (E : DerivedCategory Z.Modules) (hE : IsPerfect (X := Z.toRingedSpace) E)
    (F : DerivedCategory Z.Modules) (c d : ℤ) (hF : HasTorAmplitudeOver p F c d) :
    ∃ a b : ℤ, HasTorAmplitudeOver p ((T.tensor.obj E).obj F) a b := by
  obtain ⟨I, U, hU, hfin⟩ :=
    Stacks.Cohomology.TorAmplitude.locallyHasFiniteTorDimension_of_isPerfect
      (X := Z.toRingedSpace) E hE
  choose α β hαβ using hfin
  have hstalk : ∀ (i : I) (y : Z), y ∈ U i → HasTorAmplitudeCanonical
      (ToType (TopCat.Presheaf.stalk (C := RingCat.{u})
        (StrictlyPerfect.structureSheafOfRings.{u} Z.toRingedSpace).obj y))
      ((AlgebraicGeometry.SheafOfModules.stalkFunctor
        (StrictlyPerfect.structureSheafOfRings.{u} Z.toRingedSpace) y).mapDerivedCategory.obj E)
        (α i) (β i) :=
    fun i => (Stacks.Thickenings.hasTorAmplitude_restrictModules_iff_forall_stalk
      Z.toRingedSpace (U i) E (α i) (β i)).1 (hαβ i)
  have hmem : ∀ y : Z, ∃ i, y ∈ U i := fun y => Opens.mem_iSup.1 (hU ▸ trivial)
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover
    (fun i => ((U i : Opens Z.carrier) : Set Z)) (fun i => (U i).isOpen)
    fun y _ => Set.mem_iUnion.2 (hmem y)
  obtain ⟨a₀, ha₀⟩ := (t.finite_toSet.image α).bddBelow
  obtain ⟨b₀, hb₀⟩ := (t.finite_toSet.image β).bddAbove
  refine ⟨a₀ + c, b₀ + d, (hasTorAmplitudeOver_iff_forall_derivedStalk p _ _ _).2 fun x => ?_⟩
  obtain ⟨i, hit, hxi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ x))
  exact hasTorAmplitudeCanonical_derivedStalk_derivedTensor p T E F x a₀ b₀ c d
    (Scheme.Hom.hasTorAmplitudeCanonical_mono (ha₀ ⟨i, hit, rfl⟩) (hb₀ ⟨i, hit, rfl⟩)
      (hstalk i x hxi))
    ((hasTorAmplitudeOver_iff_forall_derivedStalk p F c d).1 hF x)

end TorAmplitude

/-! ### Clause (1) -/

section ClauseOne

variable [IsNoetherian S] [LocallyOfFiniteType f] [QuasiCompact f]
  [LocallyOfFiniteType g] [QuasiCompact g]

/-- **[Stacks, Tag 0FYT], clause (1).** Let `S` be Noetherian, let `X ⟶ S` and `Y ⟶ S` be of
finite type and let `K ∈ D^b_{Coh}(𝒪_{X ×_S Y})` be such that the support of every `H^i(K)` is
proper over `Y` and `K` has finite Tor dimension as an object of `D(pr_2^{-1}𝒪_Y)`. Then `Φ_K`
sends `D_perf(𝒪_X)` into `D_perf(𝒪_Y)`.

The support of a coherent `H^i(K)` is closed, and `hsupp` asks that this closed subset be proper
over `Y`. The proof is [Stacks, Tag 08EV] for `pr_2` applied to `T = L pr_1^* M ⊗^𝐋 K`, with each
of its hypotheses on `T` derived from those on `K`; see the module documentation. -/
@[stacks 0FYT "part (1)"]
theorem isPerfect_fourierMukai_of_boundedCoherent_kernel
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : DerivedCategoryB.derivedCategoryBBounded
      (fun F : (Limits.pullback f g).Modules => F.IsCoherent) K)
    (hsupp : ∀ (j : ℤ) (hcl : IsClosed (SheafOfModules.supp
      ((DerivedCategory.homologyFunctor (Limits.pullback f g).Modules j).obj K))),
      IsProperOver (Limits.pullback.snd f g) ⟨_, hcl⟩)
    (hTor : Stacks.Cohomology.TorAmplitude.HasFiniteTorDimension
      (RingedSpace.inverseImage Y.toRingedSpace (Limits.pullback.snd f g).base)
      ((Scheme.Hom.derivedScalarRestriction (Limits.pullback.snd f g)).obj K))
    (M : DerivedCategory X.Modules) (hM : IsPerfect (X := X.toRingedSpace) M) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M) := by
  have hXN : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have hYN : IsNoetherian Y := isNoetherian_of_locallyOfFiniteType g
  have hPN : IsNoetherian (Limits.pullback f g) :=
    isNoetherian_of_locallyOfFiniteType (Limits.pullback.snd f g)
  obtain ⟨c, d, hcd⟩ :=
    (hasFiniteTorDimension_derivedScalarRestriction_iff (Limits.pullback.snd f g) K).1 hTor
  obtain ⟨a, b, hab⟩ := exists_hasTorAmplitudeOver_derivedTensor_of_compactSpace
    (Limits.pullback.snd f g)
    (Stacks.DerivedTensor.RingedSite.canonicalDerivedTensorProduct _)
    ((fourierMukaiPullback f g).obj M) (isPerfect_fourierMukaiPullback f g M hM) K c d hcd
  have hT : HasTorAmplitudeOver (Limits.pullback.snd f g) (fourierMukaiKernelTensor f g K M) a b :=
    hab
  obtain ⟨⟨-, kb, hKhi⟩, hKc⟩ := id hK
  obtain ⟨⟨-, mb, hMhi⟩, hMc⟩ :=
    Stacks.AlgebraicGeometry.PerfectCohomology.isBoundedCoherent_of_isPerfect X M hM
  have hcoh := isCoherent_homology_fourierMukaiTensor f g K ⟨⟨kb, hKhi⟩, hKc⟩ M ⟨⟨mb, hMhi⟩, hMc⟩
  refine
    Stacks.AlgebraicGeometry.ProperSupportCoherent.isPerfect_derivedPushforward_of_isProperOver_supp
      (Limits.pullback.snd f g) (fourierMukaiKernelTensor f g K M) a b ?_ ?_ hcoh
      (fun j => isProperOver_supp_homology_fourierMukaiTensor f g K hK hsupp M j _)
      ((hasFiniteTorDimension_derivedScalarRestriction_iff _ _).2 ⟨a, b, hT⟩)
  · exact (DerivedCategory.isGE_iff _ a).2 fun j hj =>
      isZero_homology_of_hasTorAmplitudeOver _ _ a b hT j fun h => by have := h.1; omega
  · exact (DerivedCategory.isLE_iff _ b).2 fun j hj =>
      isZero_homology_of_hasTorAmplitudeOver _ _ a b hT j fun h => by have := h.2; omega

end ClauseOne

/-! ### Clause (2) -/

/-- **[Stacks, Tag 0FYT], clause (2).** Let `X ⟶ S` be of finite presentation and let `K` be
represented by a bounded complex `𝒦^•` of finitely presented `𝒪_{X ×_S Y}`-modules, flat over
`Y`, with support proper over `Y`. Then `Φ_K` sends `D_perf(𝒪_X)` into `D_perf(𝒪_Y)`.

This is [Stacks, Tag 0A1H] for `pr_2 : X ×_S Y ⟶ Y`, which is of finite presentation by base
change, with `E = L pr_1^* M`, perfect by [Stacks, Tag 09UA]. -/
@[stacks 0FYT "part (2)"]
theorem isPerfect_fourierMukai_of_flatProperSupportFinitelyPresented_kernel
    [LocallyOfFinitePresentation f] [QuasiCompact f] [QuasiSeparated f]
    (G : CochainComplex (Limits.pullback f g).Modules ℤ)
    (hG : FlatProperSupportFinitelyPresented (Limits.pullback.snd f g) G)
    (K : DerivedCategory (Limits.pullback f g).Modules) (e : DerivedCategory.Q.obj G ≅ K)
    (M : DerivedCategory X.Modules) (hM : IsPerfect (X := X.toRingedSpace) M) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M) := by
  have hfp : FinitePresentation (Limits.pullback.snd f g) :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  have key : IsPerfect (X := Y.toRingedSpace)
      ((fourierMukai f g (DerivedCategory.Q.obj G)).obj M) :=
    isPerfect_derivedPushforward_tensor (Limits.pullback.snd f g) hfp
      ((fourierMukaiPullback f g).obj M) (isPerfect_fourierMukaiPullback f g M hM) G hG
  have e' : (fourierMukai f g (DerivedCategory.Q.obj G)).obj M ≅ (fourierMukai f g K).obj M :=
    (fourierMukaiPushforward f g).mapIso
      (((Stacks.DerivedTensor.RingedSite.derivedTensorProductFunctor
        (Limits.pullback f g).toRingedSpace.sheaf).flip.mapIso e).app
          ((fourierMukaiPullback f g).obj M))
  exact Stacks.Cohomology.PerfectComplexTriangles.isPerfect_of_iso.{u, u + 1} e' key

/-! ### Clauses (3) and (4) -/

/-- **[Stacks, Tag 0FYT], clause (3).** Let `X ⟶ S` be a proper flat morphism of finite
presentation and let `K` be perfect. Then `Φ_K` sends `D_perf(𝒪_X)` into `D_perf(𝒪_Y)`.

`T = L pr_1^* M ⊗^𝐋 K` is perfect, hence `Y`-perfect by the first assertion of
[Stacks, Tag 0DI4], and [Stacks, Tag 0DJT] for the proper, flat, finitely presented `pr_2` makes
`R pr_{2,*} T` perfect. -/
@[stacks 0FYT "part (3)"]
theorem isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : IsPerfect (X := (Limits.pullback f g).toRingedSpace) K)
    (M : DerivedCategory X.Modules) (hM : IsPerfect (X := X.toRingedSpace) M) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M) :=
  open Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward in
  isPerfect_derivedPushforward_of_isPerfectRelativeTo_of_flat
    (Limits.pullback.snd f g) (fourierMukaiKernelTensor f g K M)
    (Scheme.Hom.isPerfectRelativeTo_canonical_of_isPerfect (Limits.pullback.snd f g) _
      (isPerfect_fourierMukaiTensor f g K M hK hM))

/-- **[Stacks, Tag 0FYT], clause (4).** Let `S` be Noetherian, let `X ⟶ S` be flat and proper and
let `K` be perfect. Then `Φ_K` sends `D_perf(𝒪_X)` into `D_perf(𝒪_Y)`.

As in the source this is clause (3): `X ⟶ S` is of finite type over a Noetherian scheme, hence
locally of finite presentation by [Stacks, Tag 01TX], an instance found by instance search. -/
@[stacks 0FYT "part (4)"]
theorem isPerfect_fourierMukai_of_isPerfect_kernel_of_noetherian_properFlat [IsNoetherian S]
    [IsProper f] [Flat f]
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : IsPerfect (X := (Limits.pullback f g).toRingedSpace) K)
    (M : DerivedCategory X.Modules) (hM : IsPerfect (X := X.toRingedSpace) M) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M) :=
  isPerfect_fourierMukai_of_isPerfect_kernel_of_properFlatFinitePresentation f g K hK M hM

/-! ### Clauses (5) and (6) -/

/-- **[Stacks, Tag 0FYT], clause (5).** Let `X ⟶ S` be a proper flat morphism of finite
presentation and let `K` be `Y`-perfect ([Stacks, Tag 0DI0]). Then `Φ_K` sends `D_perf(𝒪_X)`
into `D_perf(𝒪_Y)`.

The second assertion of [Stacks, Tag 0DI4] makes `T = L pr_1^* M ⊗^𝐋 K` `Y`-perfect, and
[Stacks, Tag 0DJT] for `pr_2` makes `R pr_{2,*} T` perfect. -/
@[stacks 0FYT "part (5)"]
theorem isPerfect_fourierMukai_of_isRelativelyPerfect_kernel_of_properFlatFinitePresentation
    [IsProper f] [Flat f] [LocallyOfFinitePresentation f]
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : (Limits.pullback.snd f g).IsRelativelyPerfect K)
    (M : DerivedCategory X.Modules) (hM : IsPerfect (X := X.toRingedSpace) M) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M) :=
  open Stacks.AlgebraicGeometry.RelativelyPerfectProperPushforward in
  isPerfect_derivedPushforward_of_isPerfectRelativeTo_of_flat
    (Limits.pullback.snd f g) (fourierMukaiKernelTensor f g K M)
    (Scheme.Hom.isPerfectRelativeTo_canonical_derivedTensor (Limits.pullback.snd f g)
      ((fourierMukaiPullback f g).obj M) K (isPerfect_fourierMukaiPullback f g M hM)
      ((Scheme.Hom.isPerfectRelativeTo_canonicalFamily_iff _ K).2 hK))

/-- **[Stacks, Tag 0FYT], clause (6).** Let `S` be Noetherian, let `X ⟶ S` be flat and proper and
let `K` be `Y`-perfect. Then `Φ_K` sends `D_perf(𝒪_X)` into `D_perf(𝒪_Y)`.

This is clause (5), `X ⟶ S` being locally of finite presentation by [Stacks, Tag 01TX]. -/
@[stacks 0FYT "part (6)"]
theorem isPerfect_fourierMukai_of_isRelativelyPerfect_kernel_of_noetherian_properFlat
    [IsNoetherian S] [IsProper f] [Flat f]
    (K : DerivedCategory (Limits.pullback f g).Modules)
    (hK : (Limits.pullback.snd f g).IsRelativelyPerfect K)
    (M : DerivedCategory X.Modules) (hM : IsPerfect (X := X.toRingedSpace) M) :
    IsPerfect (X := Y.toRingedSpace) ((fourierMukai f g K).obj M) :=
  isPerfect_fourierMukai_of_isRelativelyPerfect_kernel_of_properFlatFinitePresentation f g K hK
    M hM

end AlgebraicGeometry

end
