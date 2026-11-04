module

public import StacksFrontier.AlgebraicGeometry.Perfect.ProjectionFormulaKZero.PerfectTensor
public import StacksFrontier.AlgebraicGeometry.Perfect.DerivedPushforwardOpenBase
public import StacksFrontier.AlgebraicGeometry.Perfect.GrothendieckGroupProperPushforwardDerived
public import StacksFrontier.AlgebraicGeometry.ProperSupportCoherent.DerivedDirectImageUnconditional
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedPushforward.QuasiCoherentDirectSums

/-!
# The proper pushforward `K'₀(X) ⟶ K'₀(Y)` and the parity Euler class

Let `f : X ⟶ Y` be a proper morphism of locally Noetherian schemes. The total derived direct
image `Rf_*` carries objects with locally bounded coherent cohomology to such objects: over an
affine open `V` of `Y` the preimage `f⁻¹V` is quasi-compact, so the restriction of the object to
it is bounded, and `Rf_*` of a bounded object with coherent cohomology along the proper morphism
`f⁻¹V ⟶ V` to a Noetherian scheme is in `D^b_Coh` by [Stacks, Tag 08E2]. Together with the
dévissage of the parity Euler class this gives

  `f_* χ(K) = χ(Rf_* K)`

for every `K` with locally bounded coherent cohomology, `f_* : K'₀(X) ⟶ K'₀(Y)` being the
pushforward of [Stacks, Tag 0FDL].

## Main results

* `AlgebraicGeometry.ParityEulerClass.IsLocallyBoundedCoherent.derivedPushforward`: the closure.
* `AlgebraicGeometry.ParityEulerClass.properPushforward_mk_eq`:
  `f_*[ℱ] = χ(Rf_* ℱ)` for a coherent module `ℱ`.
* `AlgebraicGeometry.ParityEulerClass.properPushforward_parityEulerClass`:
  `f_* χ(K) = χ(Rf_* K)`.

## References

* [Stacks Project, Tag 0FDL](https://stacks.math.columbia.edu/tag/0FDL)
* [Stacks Project, Tag 08E2](https://stacks.math.columbia.edu/tag/08E2)
* [Stacks Project, Tag 08FE](https://stacks.math.columbia.edu/tag/08FE)
* [Stacks Project, Tag 08DZ](https://stacks.math.columbia.edu/tag/08DZ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated Topology

universe u

namespace AlgebraicGeometry.ParityEulerClass

attribute [local instance 100000] HasDerivedCategory.standard

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **`Rf_*` preserves locally bounded coherent cohomology along a proper morphism to a locally
Noetherian scheme.** -/
theorem IsLocallyBoundedCoherent.derivedPushforward [IsLocallyNoetherian Y] [IsProper f]
    {K : DerivedCategory X.Modules} (hK : IsLocallyBoundedCoherent K) :
    IsLocallyBoundedCoherent ((derivedPushforwardModules f).obj K) := by
  refine isLocallyBoundedCoherent_of_local _ fun y => ?_
  obtain ⟨_, ⟨V₀, hV, rfl⟩, hyV, -⟩ :=
    Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
  let V : Y.Opens := V₀
  have : IsAffine V.toScheme := hV
  have : IsNoetherian V.toScheme := IsNoetherian.mk
  have hcpt : IsCompact ((f ⁻¹ᵁ V : X.Opens) : Set X) :=
    f.isCompact_preimage (IsAffineOpen.isCompact hV)
  have hfin := hK.2.finite_nonempty_inter_compact hcpt
  obtain ⟨a, ha⟩ := hfin.bddBelow
  obtain ⟨b, hb⟩ := hfin.bddAbove
  let RK := (Scheme.Modules.restrictFunctor (f ⁻¹ᵁ V).ι).mapDerivedCategory.obj K
  have hz : ∀ q : ℤ, (q < a ∨ b < q) →
      IsZero ((DerivedCategory.homologyFunctor _ q).obj RK) := by
    intro q hq
    refine IsZero.of_iso (isZero_restrict_of_disjoint _ _ (Set.disjoint_left.2 fun x hx hxV => ?_))
      (restrictHomologyIso (f ⁻¹ᵁ V) K q).symm
    have hmem : q ∈ {q | (SheafOfModules.supp ((DerivedCategory.homologyFunctor X.Modules q).obj K)
        ∩ ((f ⁻¹ᵁ V : X.Opens) : Set X)).Nonempty} := ⟨x, hx, hxV⟩
    have := ha hmem
    have := hb hmem
    omega
  have hcoh : ∀ q : ℤ, ((DerivedCategory.homologyFunctor _ q).obj RK).IsCoherent := fun q =>
    ObjectProperty.prop_of_iso (P := SheafOfModules.IsCoherent)
      (restrictHomologyIso (f ⁻¹ᵁ V) K q) (Modules.isCoherent_restrict (hM := hK.1 q) _ _)
  have hGE : RK.IsGE a := (DerivedCategory.isGE_iff RK a).2 fun q hq => hz q (Or.inl hq)
  have hLE : RK.IsLE b := (DerivedCategory.isLE_iff RK b).2 fun q hq => hz q (Or.inr hq)
  open Stacks.AlgebraicGeometry.ProperSupportCoherent in
  refine ⟨V, hyV, _, derivedCategoryBBounded_derivedPushforward_of_properSupp
      (f ∣_ V) RK hcoh (fun j => ?_) a b hGE hLE, fun q =>
      ⟨restrictHomologyIso V _ q ≪≫ (DerivedCategory.homologyFunctor _ q).mapIso
        (schemeDerivedPushforwardRestrictOpensIso f V K)⟩⟩
  show IsProper ((Scheme.IdealSheafData.vanishingIdeal _).subschemeι ≫ (f ∣_ V))
  infer_instance

/-- **`Rf_*` commutes with direct sums of objects with locally bounded coherent cohomology**,
which have quasi-coherent cohomology: [Stacks, Tag 08DZ]. -/
theorem isIso_sigmaComparison_derivedPushforward [QuasiCompact f] [QuasiSeparated f]
    {α : Type u} (K : α → DerivedCategory X.Modules) (hK : ∀ k, IsLocallyBoundedCoherent (K k)) :
    IsIso (sigmaComparison (derivedPushforwardModules f) K) :=
  Stacks.Duality.DerivedPushforward.isIso_sigmaComparison_of_isQuasicoherent f K fun k i =>
    have := (hK k).1 i
    _root_.isQuasicoherent_of_isCoherent _

/-- **The parity sums of `Rf_*(ℱ[0])` are the parity sums of the higher direct images.** The
cohomology of `Rf_*(ℱ[0])` in degree `n` is `R ⁿ f_* ℱ`, which vanishes for `n < 0`. -/
def paritySumDerivedPushforwardIso (F : X.Modules) (r : ℕ) (hr : r ≤ 1) :
    paritySum ((derivedPushforwardModules f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F)) (r : ℤ) ≅
      ProperPushforwardKZero.parityDirectImageSum f F r := by
  let K := (derivedPushforwardModules f).obj ((DerivedCategory.singleFunctor X.Modules 0).obj F)
  have e : ∀ n : ℤ, (DerivedCategory.homologyFunctor Y.Modules n).obj K ≅
      ((Scheme.Modules.pushforward f).rightDerivedPlus n).obj F := fun n =>
    (Stacks.AlgebraicGeometry.ProperSupportCoherent.nonempty_homology_derivedPushforward_single_zero
      f F n).some
  have hz : IsZero (∐ fun k : ULift.{u} ℕ =>
      (DerivedCategory.homologyFunctor Y.Modules (2 * (-((k.down + 1 : ℕ) : ℤ)) + r)).obj K) :=
    isZero_sigma _ fun k => IsZero.of_iso
      (Stacks.AlgebraicGeometry.HigherDirectImage.isZero_higherDirectImage_of_neg f F _
        (by push_cast; omega)) (e _)
  exact paritySumSplit K r ≪≫ (isoBiprodZero hz).symm ≪≫
    Limits.Sigma.reindex (Equiv.ulift : ULift.{u} ℕ ≃ ℕ)
      (fun i : ℕ => (DerivedCategory.homologyFunctor Y.Modules (2 * (i : ℤ) + r)).obj K) ≪≫
    Limits.Sigma.mapIso fun i => e _ ≪≫ eqToIso (congrArg
      (fun n : ℤ => ((Scheme.Modules.pushforward f).rightDerivedPlus n).obj F) (by push_cast; ring))

/-- **[Stacks, Tag 0FDL] read through the parity Euler class**: `f_*[ℱ] = χ(Rf_*(ℱ[0]))` for a
coherent `𝒪_X`-module `ℱ`. -/
theorem properPushforward_mk_eq [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsProper f]
    (F : Stacks.SheafOfModules.CoherentModules X.ringCatSheaf) :
    ProperPushforwardKZero.properPushforward f (KZero.mk _ F) =
      parityEulerClass ((derivedPushforwardModules f).obj
        ((DerivedCategory.singleFunctor X.Modules 0).obj F.obj)) := by
  have hF : F.obj.IsCoherent := CoherentAbelian.isCoherent_of_stacksIsCoherent F.property
  have hK := (isLocallyBoundedCoherent_single F.obj hF).derivedPushforward f
  rw [parityEulerClass_eq hK]
  exact ProperPushforwardKZero.properPushforward_mk f F _ _
    (paritySumDerivedPushforwardIso f F.obj 0 zero_le_one)
    (paritySumDerivedPushforwardIso f F.obj 1 le_rfl)

/-- **The proper pushforward of the parity Euler class is the parity Euler class of `Rf_*`.**
For `K` with locally bounded coherent cohomology, `f_* χ(K) = χ(Rf_* K)`: the dévissage of
`χ ∘ Rf_*` reduces it to the parity sums of `K`, placed in degree `0`, where it is
`properPushforward_mk_eq`. -/
theorem properPushforward_parityEulerClass [IsLocallyNoetherian X] [IsLocallyNoetherian Y]
    [IsProper f] (K : DerivedCategory X.Modules) (hK : IsLocallyBoundedCoherent K) :
    ProperPushforwardKZero.properPushforward f (parityEulerClass K) =
      parityEulerClass ((derivedPushforwardModules f).obj K) := by
  rw [parityEulerClass_map_eq (derivedPushforwardModules f)
    (fun L hL => hL.derivedPushforward f)
    (fun L hL => isIso_sigmaComparison_derivedPushforward f L hL) K hK,
    parityEulerClass_eq hK, map_sub, properPushforward_mk_eq f (parityObject K hK 0),
    properPushforward_mk_eq f (parityObject K hK 1)]
  rfl

end AlgebraicGeometry.ParityEulerClass
