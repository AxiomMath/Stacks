module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeUnitSingle
public import StacksFrontier.AlgebraicGeometry.Cohomology.LocallyNoetherian.Coherent
public import StacksFrontier.AlgebraicGeometry.DerivedAffineMorphism.PullbackPushforwardDerivedTensor
public import StacksFrontier.AlgebraicGeometry.DerivedCategoryOverField.Decomposition
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.BoundedCoherent
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.BoxDisplay
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.ClosedImmersionKernel
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.FlatSingleTensorHomology
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.FourierMukai.KernelVariable
public import StacksFrontier.AlgebraicGeometry.FiberRank.Basic
public import StacksFrontier.AlgebraicGeometry.Intersection.TorFormula.CoherentTorSheaves
public import StacksFrontier.AlgebraicGeometry.InvertibleClasses.Basic
public import StacksFrontier.AlgebraicGeometry.Perfect.RelativelyPerfectFibres
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImageUnconditional
public import StacksFrontier.CategoryTheory.Triangulated.ExactFunctorBoundedOperations

/-!
# The Fourier-Mukai functor of the kernel variable at an external tensor product

Let `k` be a field, let `f : X ⟶ Spec k` be proper and flat, let `ℰ` and `𝒢` be finite locally
free `𝒪_X`-modules and let `M ∈ D^b_Coh(𝒪_X)`. The second computation of the proof of
[Stacks, Tag 0FZ6] is

`Ψ_M(ℰ ⊠ 𝒢) = R pr_{2,*}(L pr_1^* M ⊗^𝐋 (ℰ ⊠ 𝒢)) = RΓ(X, ℰ ⊗^𝐋 M) ⊗_k 𝒢`,

where `Ψ_M` is `AlgebraicGeometry.fourierMukaiKernelFunctor`, and its consequence that `Ψ_M(ℰ ⊠ 𝒢)`
is a finite direct sum of shifts of `𝒢`. This file proves both, the latter with the shifts
confined to any window `[a, b]` outside which `H^i(X, ℰ ⊗^𝐋 M)` vanishes:

`Ψ_M(ℰ ⊠ 𝒢) ∈ smd(add(𝒢[a, b]))`.

## The argument

The chain of isomorphisms is the source's, read in the derived category of `X`:

1. the display of [Stacks, Tag 0G0E], `AlgebraicGeometry.fourierMukaiDisplayIso`, rewrites
   `R pr_{2,*}(L pr_1^* M ⊗^𝐋 (ℰ ⊠ 𝒢))` as `R pr_{2,*}(L pr_1^* ℰ ⊗^𝐋 L pr_1^* M) ⊗^𝐋 𝒢`;
   it is the box comparison of [Stacks, Tag 0G0A] followed by the projection formula of
   [Stacks, Tag 0B54] at `pr₂`, which is [Stacks, Tag 08EU] in the case at hand;
2. the monoidality of derived pullback, [Stacks, Tag 079U], gives
   `L pr_1^* ℰ ⊗^𝐋 L pr_1^* M ≅ L pr_1^*(ℰ ⊗^𝐋 M)`;
3. derived base change, [Stacks, Tag 08IB], for the cartesian square
   `X ×_k X ⟶ X` over `X ⟶ Spec k`, which is Tor independent because `X` is flat over `k`,
   gives `R pr_{2,*} L pr_1^*(ℰ ⊗^𝐋 M) ≅ L f^* R f_*(ℰ ⊗^𝐋 M)`.

So `Ψ_M(ℰ ⊠ 𝒢) ≅ Θ(Rf_*(ℰ ⊗^𝐋 M))` for the exact functor `Θ = L f^*(-) ⊗^𝐋 𝒢 : D(𝒪_{Spec k}) ⥤
D(𝒪_X)`, which carries `𝒪_{Spec k}` to `𝒢`. Properness enters through [Stacks, Tag 08E2]: since
`ℰ ⊗^𝐋 M` is in `D^b_Coh(𝒪_X)`, the object `Rf_*(ℰ ⊗^𝐋 M)` has coherent, that is finite
dimensional, cohomology, so it lies in `smd(add(𝒪_{Spec k}[a, b]))`
(`AlgebraicGeometry.SpecFieldDerived.mem_window_of_isCoherent_homology`), and the exact functor
`Θ` carries that into `smd(add(𝒢[a, b]))` ([Stacks, Tag 0FX5]).

## Main definitions

* `AlgebraicGeometry.fourierMukaiBoxTwist` — the exact functor `Θ = L f^*(-) ⊗^𝐋 𝒢`.
* `AlgebraicGeometry.fourierMukaiKernelFunctorBoxIso` — `Ψ_M(ℰ ⊠ 𝒢) ≅ Θ(Rf_*(ℰ ⊗^𝐋 M))`.

## Main results

* `AlgebraicGeometry.fourierMukaiKernelFunctor_box_mem_window` — the membership
  `Ψ_M(ℰ ⊠ 𝒢) ∈ smd(add(𝒢[a, b]))` for every window `[a, b]` of `H^*(X, ℰ ⊗^𝐋 M)`.
* `AlgebraicGeometry.exists_window_fourierMukaiKernelFunctor_box` — such a window exists.
* `AlgebraicGeometry.fourierMukaiKernelFunctor_box_mem_triangEnvelopeIter_zero` — hence
  `Ψ_M(ℰ ⊠ 𝒢) ∈ ⟨𝒢⟩₀`.

## References

* [Stacks Project, Tag 0FZ6](https://stacks.math.columbia.edu/tag/0FZ6)
* [Stacks Project, Tag 08IB](https://stacks.math.columbia.edu/tag/08IB)
* [Stacks Project, Tag 08EU](https://stacks.math.columbia.edu/tag/08EU)
* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
* [Stacks Project, Tag 0FX5](https://stacks.math.columbia.edu/tag/0FX5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open Stacks.Cohomology.DerivedAdjunctionOnRingedSpaces
open Stacks.DerivedTensor.RingedSite

universe u

namespace AlgebraicGeometry

attribute [local instance 100000] HasDerivedCategory.standard

variable {k : Type u} [Field k] {X : Scheme.{u}} (f : X ⟶ Spec (.of k))

/-! ### The functor `Θ = L f^*(-) ⊗^𝐋 𝒢` -/

/-- **The functor `Θ = L f^*(-) ⊗^𝐋 𝒢 : D(𝒪_{Spec k}) ⥤ D(𝒪_X)`**, the derived pullback along
`f` followed by the derived tensor product with `𝒢` placed in degree zero. On a complex of
vector spaces `V` it is `V ⊗_k 𝒢`. -/
def fourierMukaiBoxTwist (G : X.Modules) :
    DerivedCategory (Spec (.of k)).Modules ⥤ DerivedCategory X.Modules :=
  dpull f ⋙ dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj G)

/-- `L f^*` commutes with the shift, by [Stacks, Tag 06YJ]. -/
local instance commShift_boxTwistPullback : (dpull f).CommShift ℤ :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_commShift (f := f.toLRSHom.toShHom)

/-- `L f^*` is exact, by [Stacks, Tag 06YJ]. -/
local instance isTriangulated_boxTwistPullback : (dpull f).IsTriangulated :=
  Stacks.Cohomology.KFlatDerivedPullback.derivedPullback_isTriangulated (f := f.toLRSHom.toShHom)

/-- `- ⊗^𝐋 A` commutes with the shift, by [Stacks, Tag 06YU]. -/
local instance commShift_boxTwistTensor (A : DerivedCategory X.Modules) :
    (dtenR X A).CommShift ℤ :=
  (canonicalDerivedTensorProduct X.toRingedSpace.sheaf).commShift_left A

/-- `- ⊗^𝐋 A` is exact, by [Stacks, Tag 06YU]. -/
local instance isTriangulated_boxTwistTensor (A : DerivedCategory X.Modules) :
    (dtenR X A).IsTriangulated :=
  (canonicalDerivedTensorProduct X.toRingedSpace.sheaf).exact_left A

/-- `Θ` commutes with the shift. -/
instance commShift_fourierMukaiBoxTwist (G : X.Modules) :
    (fourierMukaiBoxTwist f G).CommShift ℤ :=
  Functor.CommShift.comp (F := dpull f)
    (G := dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj G))

/-- **`Θ` is exact.** -/
instance isTriangulated_fourierMukaiBoxTwist (G : X.Modules) :
    (fourierMukaiBoxTwist f G).IsTriangulated :=
  Functor.IsTriangulated.instComp (F := dpull f)
    (G := dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj G))

/-- **`Θ(𝒪_{Spec k}) ≅ 𝒢`**: the derived pullback of the structure sheaf is the structure
sheaf, and `𝒪_X` is the unit of the derived tensor product. -/
def fourierMukaiBoxTwistUnitIso (G : X.Modules) :
    (fourierMukaiBoxTwist f G).obj ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        (SheafOfModules.unit (Spec (.of k)).ringCatSheaf)) ≅
      (DerivedCategory.singleFunctor X.Modules 0).obj G :=
  (dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj G)).mapIso
      (dpullStructureSheafIso f) ≪≫
    (dtenLeftUnitIso X).app ((DerivedCategory.singleFunctor X.Modules 0).obj G)

/-- **`Θ` carries `smd(add(𝒪_{Spec k}[a, b]))` into `smd(add(𝒢[a, b]))`**, by the
functoriality of these subcategories along an exact functor, [Stacks, Tag 0FX5], and
`Θ(𝒪_{Spec k}) ≅ 𝒢`. -/
theorem fourierMukaiBoxTwist_mem_window (G : X.Modules) (a b : ℤ)
    {V : DerivedCategory (Spec (.of k)).Modules}
    (hV : ((⨆ i ∈ Set.Icc a b, (ObjectProperty.singleton
        ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
          (SheafOfModules.unit (Spec (.of k)).ringCatSheaf))).isoClosure.shift
            i).binaryProductsClosure).retractClosure V) :
    ((⨆ i ∈ Set.Icc a b, (ObjectProperty.singleton
        ((DerivedCategory.singleFunctor X.Modules 0).obj G)).isoClosure.shift i
      ).binaryProductsClosure).retractClosure ((fourierMukaiBoxTwist f G).obj V) := by
  have h :=
    Stacks.TriangulatedGenerators.retractClosure_extensionProductIter_biSup_shift_inverseImage_of_le
      (fourierMukaiBoxTwist f G)
      (P := ObjectProperty.singleton ((DerivedCategory.singleFunctor (Spec (.of k)).Modules 0).obj
        (SheafOfModules.unit (Spec (.of k)).ringCatSheaf)))
      (Q := (ObjectProperty.singleton
        ((DerivedCategory.singleFunctor X.Modules 0).obj G)).isoClosure)
      (fun Y hY => by
        obtain rfl := (ObjectProperty.singleton_iff _ _).1 hY
        exact ⟨_, (ObjectProperty.singleton_iff _ _).2 rfl, ⟨fourierMukaiBoxTwistUnitIso f G⟩⟩)
      a b 0 V hV
  rw [ObjectProperty.isoClosure_eq_self
    (ObjectProperty.singleton ((DerivedCategory.singleFunctor X.Modules 0).obj G)).isoClosure] at h
  exact h

/-! ### The computation `Ψ_M(ℰ ⊠ 𝒢) ≅ Θ(Rf_*(ℰ ⊗^𝐋 M))` -/

/-- The square `X ×_k X ⟶ X` over `X ⟶ Spec k`, read on the underlying morphisms of ringed
spaces. -/
theorem fourierMukaiBox_sq :
    (pullback.fst f f).toLRSHom.toShHom ≫ f.toLRSHom.toShHom =
      (pullback.snd f f).toLRSHom.toShHom ≫ f.toLRSHom.toShHom :=
  shHom_comp_eq pullback.condition

/-- **Derived base change for `X ×_k X ⟶ X` over `X ⟶ Spec k`**, [Stacks, Tag 08IB]:
`L f^* R f_* N ≅ R pr_{2,*} L pr_1^* N` for `N` with quasi-coherent cohomology. The square is
Tor independent because `f` is flat. -/
def fourierMukaiBoxBaseChangeIso [QuasiCompact f] [QuasiSeparated f] [Flat f]
    (N : DerivedCategory X.Modules) (hN : IsQCohAll N) :
    (dpull f).obj ((dpush f).obj N) ≅ (dpush (pullback.snd f f)).obj
      ((dpull (pullback.fst f f)).obj N) :=
  have hiso := derivedBaseChangeIsIsoOnQuasicoherent (pullback.fst f f) (pullback.snd f f) f f
    (IsPullback.of_hasPullback f f) inferInstance inferInstance (torIndependent_of_flat f f)
    (fourierMukaiBox_sq f) N hN
  @asIso _ _ _ _ ((dbaseChange (pullback.fst f f) (pullback.snd f f) f f
    (fourierMukaiBox_sq f)).app N) hiso

/-- **`Ψ_M(ℰ ⊠ 𝒢) ≅ Θ(Rf_*(ℰ ⊗^𝐋 M))`**, i.e.
`R pr_{2,*}(L pr_1^* M ⊗^𝐋 (ℰ ⊠ 𝒢)) ≅ L f^* RΓ(X, ℰ ⊗^𝐋 M) ⊗^𝐋 𝒢`, for `f` flat,
quasi-compact and quasi-separated, `𝒢` finite locally free and `M` with quasi-coherent
cohomology: the display of [Stacks, Tag 0G0E], the monoidality of derived pullback
([Stacks, Tag 079U]) and derived base change ([Stacks, Tag 08IB]). -/
def fourierMukaiKernelFunctorBoxIso [QuasiCompact f] [QuasiSeparated f] [Flat f]
    (E G : X.Modules) (hE : E.IsQuasicoherent)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (M : DerivedCategory X.Modules) (hM : IsQCohAll M) :
    (fourierMukaiKernelFunctor f f M).obj
        ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
          (externalTensorProduct f f E G)) ≅
      (fourierMukaiBoxTwist f G).obj
        ((dpush f).obj ((dtenR X M).obj ((DerivedCategory.singleFunctor X.Modules 0).obj E))) :=
  have hEM : IsQCohAll ((dtenR X M).obj ((DerivedCategory.singleFunctor X.Modules 0).obj E)) :=
    isQCohAll_dtenR (fun j =>
      open Stacks.AlgebraicGeometry.AffinePushforwardTExactness in
      isQuasicoherent_homology_singleFunctor_obj (X := X) 0 E hE j) hM
  fourierMukaiDisplayIso k f f ((dpull (pullback.fst f f)).obj M) E G hG ≪≫
    ((TorFormula.derivedTensor X).mapIso
      ((dpush (pullback.snd f f)).mapIso
          ((dpullTensorIso (pullback.fst f f) M).app
            ((DerivedCategory.singleFunctor X.Modules 0).obj E)).symm ≪≫
        (fourierMukaiBoxBaseChangeIso f _ hEM).symm)).app
      ((DerivedCategory.singleFunctor X.Modules 0).obj G)

/-! ### Finite dimensionality, from properness -/

/-- **`ℰ ⊗^𝐋 M` is in `D^b_Coh(𝒪_X)`** for `ℰ` finite locally free and `M` in `D^b_Coh(𝒪_X)`,
`X` being of finite type over `k`: the cohomology sheaves are coherent by [Stacks, Tag 0AZS],
the bound above is the right t-exactness of the derived tensor product, and the bound below
holds because `ℰ` is flat, so that `H^i(M ⊗^𝐋 ℰ) = H^i(M) ⊗ ℰ`. -/
theorem bounded_and_isCoherent_homology_tensorSingle [LocallyOfFiniteType f] (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (M : DerivedCategory X.Modules) (hMb : DerivedCategory.TStructure.t.bounded M)
    (hMcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj M).IsCoherent) :
    (∃ m : ℤ, ((dtenR X M).obj ((DerivedCategory.singleFunctor X.Modules 0).obj E)).IsGE m) ∧
      (∃ n : ℤ, ((dtenR X M).obj ((DerivedCategory.singleFunctor X.Modules 0).obj E)).IsLE n) ∧
      ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj
        ((dtenR X M).obj ((DerivedCategory.singleFunctor X.Modules 0).obj E))).IsCoherent := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have := hE
  have hEcoh : E.IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentTFAE.isCoherent_of_isFiniteLocallyFree X E
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩⟩ := hMb
  have hMLE : M.IsLE n := hn
  have hMGE : M.IsGE m := hm
  have hMm : DerivedCategoryB.derivedCategoryBMinus (fun F : X.Modules => F.IsCoherent) M :=
    ⟨⟨n, fun j hj => DerivedCategory.isZero_of_isLE M n j hj⟩, hMcoh⟩
  have hEm : DerivedCategoryB.derivedCategoryBMinus (fun F : X.Modules => F.IsCoherent)
      ((DerivedCategory.singleFunctor X.Modules 0).obj E) :=
    ⟨TorFormula.isBoundedAbove_singleFunctor_obj X E,
      TorFormula.isCoherent_homology_singleFunctor_obj X E hEcoh⟩
  obtain ⟨⟨b, hb⟩, hc⟩ := TorFormula.derivedCategoryBMinus_derivedTensor X _ _ hEm hMm
  have : Stacks.FiniteLocallyFree.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E :=
    (Stacks.FiniteLocallyFree.isFiniteLocallyFree_iff_algebraicGeometry E).2 hE
  have hflat := Scheme.Modules.isFlat_of_isFiniteLocallyFree E
  have : DerivedCategory.TStructure.t.IsGE
      ((dtenR X ((DerivedCategory.singleFunctor X.Modules 0).obj E)).obj M) m :=
    isGE_tensorSingleFlat X M E hflat m
  refine ⟨⟨m, ?_⟩, ⟨b, (DerivedCategory.isLE_iff _ b).2 fun j hj => hb j hj⟩, hc⟩
  exact DerivedCategory.TStructure.t.isGE_of_iso
    ((dtenRSwapIso X ((DerivedCategory.singleFunctor X.Modules 0).obj E)).app M) m

/-- **The cohomology of `RΓ(X, ℰ ⊗^𝐋 M)` is finite dimensional and bounded**, for `f` proper,
`ℰ` finite locally free and `M ∈ D^b_Coh(𝒪_X)`: this is [Stacks, Tag 08E2] for
`f : X ⟶ Spec k`, applied to `ℰ ⊗^𝐋 M ∈ D^b_Coh(𝒪_X)`, every closed subset of `X` being
proper over `k`. -/
theorem derivedCategoryBBounded_dpush_tensorSingle [IsProper f] (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (M : DerivedCategory X.Modules) (hMb : DerivedCategory.TStructure.t.bounded M)
    (hMcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj M).IsCoherent) :
    DerivedCategoryB.derivedCategoryBBounded
      (fun N : (Spec (.of k)).Modules => N.IsCoherent)
      ((dpush f).obj ((dtenR X M).obj ((DerivedCategory.singleFunctor X.Modules 0).obj E))) := by
  obtain ⟨⟨m, hm⟩, ⟨n, hn⟩, hc⟩ := bounded_and_isCoherent_homology_tensorSingle f E hE M hMb hMcoh
  open Stacks.AlgebraicGeometry.ProperSupportCoherent in
  exact derivedCategoryBBounded_derivedPushforward_of_properSupp
    f _ hc (fun j => isProperOver_of_isProper f _) m n hm hn

/-! ### The membership `Ψ_M(ℰ ⊠ 𝒢) ∈ smd(add(𝒢[a, b]))` -/

/-- **`Ψ_M(ℰ ⊠ 𝒢) ∈ smd(add(𝒢[a, b]))`.** Let `k` be a field, `f : X ⟶ Spec k` proper and
flat, `ℰ`, `𝒢` finite locally free `𝒪_X`-modules and `M ∈ D^b_Coh(𝒪_X)`. If
`H^i(X, ℰ ⊗^𝐋 M) = 0` for `i ∉ [a, b]` (and `a ≤ b`), then
`R pr_{2,*}(L pr_1^* M ⊗^𝐋 (ℰ ⊠ 𝒢))` lies in `smd(add(𝒢[a, b]))`, the shifts being those of
the cohomological degrees `a, …, b`. This is the computation
`R pr_{2,*}((K ⊗^𝐋 ℰ) ⊠ 𝒢) = RΓ(X, K ⊗^𝐋 ℰ) ⊗_k 𝒢` of the proof of [Stacks, Tag 0FZ6],
together with "since `X` is proper, each `H^i(X, K)` is finite dimensional": by
`fourierMukaiKernelFunctorBoxIso` the object is `Θ(RΓ(X, ℰ ⊗^𝐋 M))`, the complex
`RΓ(X, ℰ ⊗^𝐋 M)` of `k`-vector spaces has finite dimensional cohomology by [Stacks, Tag 08E2]
and so is a finite sum of shifts of `k`, and `Θ(k) = 𝒢`. -/
theorem fourierMukaiKernelFunctor_box_mem_window [IsProper f] [Flat f] (E G : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (M : DerivedCategory X.Modules) (hMb : DerivedCategory.TStructure.t.bounded M)
    (hMcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj M).IsCoherent)
    (a b : ℤ) (hle : a ≤ b)
    (hab : ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules i).obj
        ((dpush f).obj ((dtenR X M).obj ((DerivedCategory.singleFunctor X.Modules 0).obj E))))) :
    ((⨆ i ∈ Set.Icc a b, (ObjectProperty.singleton
        ((DerivedCategory.singleFunctor X.Modules 0).obj G)).isoClosure.shift i
      ).binaryProductsClosure).retractClosure
      ((fourierMukaiKernelFunctor f f M).obj
        ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
          (externalTensorProduct f f E G))) := by
  have := hE
  have hEq : E.IsQuasicoherent :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isQuasicoherent_of_isFiniteLocallyFree E
  have hMq : IsQCohAll M := fun j => have := hMcoh j; _root_.isQuasicoherent_of_isCoherent _
  have hV := SpecFieldDerived.mem_window_of_isCoherent_homology k _ a b hle
    (derivedCategoryBBounded_dpush_tensorSingle f E hE M hMb hMcoh).2 hab
  exact ObjectProperty.prop_of_iso _ (fourierMukaiKernelFunctorBoxIso f E G hEq hG M hMq).symm
    (fourierMukaiBoxTwist_mem_window f G a b hV)

/-- **A window exists**: for `f` proper, `ℰ` finite locally free and `M ∈ D^b_Coh(𝒪_X)`, the
cohomology of `RΓ(X, ℰ ⊗^𝐋 M)` vanishes outside some `[a, b]` with `a ≤ b`, by
[Stacks, Tag 08E2]. -/
theorem exists_window_fourierMukaiKernelFunctor_box [IsProper f] (E : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (M : DerivedCategory X.Modules) (hMb : DerivedCategory.TStructure.t.bounded M)
    (hMcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj M).IsCoherent) :
    ∃ a b : ℤ, a ≤ b ∧ ∀ i : ℤ, i < a ∨ b < i →
      IsZero ((DerivedCategory.homologyFunctor (Spec (.of k)).Modules i).obj
        ((dpush f).obj ((dtenR X M).obj ((DerivedCategory.singleFunctor X.Modules 0).obj E)))) := by
  obtain ⟨⟨⟨a, ha⟩, ⟨b, hb⟩⟩, -⟩ := derivedCategoryBBounded_dpush_tensorSingle f E hE M hMb hMcoh
  refine ⟨a, max a b, le_max_left _ _, fun i hi => ?_⟩
  rcases hi with hi | hi
  · exact ha i hi
  · exact hb i (lt_of_le_of_lt (le_max_right _ _) hi)

/-- **`Ψ_M(ℰ ⊠ 𝒢) ∈ ⟨𝒢⟩₀`** for `f` proper and flat, `ℰ`, `𝒢` finite locally free and
`M ∈ D^b_Coh(𝒪_X)`: the per-object form of `fourierMukaiKernelFunctor_box_mem_window`, with the
window of `exists_window_fourierMukaiKernelFunctor_box`. This is the membership the proof of
[Stacks, Tag 0FZ6] feeds into the functoriality of `⟨−⟩ₙ`. -/
theorem fourierMukaiKernelFunctor_box_mem_triangEnvelopeIter_zero [IsProper f] [Flat f]
    (E G : X.Modules)
    (hE : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) E)
    (hG : SheafOfModules.IsFiniteLocallyFree.{u, u, u} (R := X.ringCatSheaf) G)
    (M : DerivedCategory X.Modules) (hMb : DerivedCategory.TStructure.t.bounded M)
    (hMcoh : ∀ i : ℤ, ((DerivedCategory.homologyFunctor X.Modules i).obj M).IsCoherent) :
    (ObjectProperty.singleton ((DerivedCategory.singleFunctor X.Modules 0).obj G)
      ).triangEnvelopeIter 0
      ((fourierMukaiKernelFunctor f f M).obj
        ((DerivedCategory.singleFunctor (pullback f f).Modules 0).obj
          (externalTensorProduct f f E G))) := by
  obtain ⟨a, b, hle, hab⟩ := exists_window_fourierMukaiKernelFunctor_box f E hE M hMb hMcoh
  have h := fourierMukaiKernelFunctor_box_mem_window f E G hE hG M hMb hMcoh a b hle hab
  rw [ObjectProperty.triangEnvelopeIter_zero]
  refine ObjectProperty.monotone_retractClosure (ObjectProperty.limitsClosure_monotone _ ?_) _ h
  refine iSup₂_le fun i _ Y hY => ?_
  obtain ⟨Z, hZ, ⟨e⟩⟩ := hY
  exact ⟨Z, -i, (shiftEquiv (DerivedCategory X.Modules) i).unitIso.app Y ≪≫
    (shiftFunctor _ (-i)).mapIso e, (ObjectProperty.singleton_iff _ _).1 hZ ▸
      (ObjectProperty.singleton_iff _ _).2 rfl⟩

end AlgebraicGeometry

end
