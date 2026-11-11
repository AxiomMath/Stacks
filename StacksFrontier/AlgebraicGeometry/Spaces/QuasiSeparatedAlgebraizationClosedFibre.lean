module

public import StacksFrontier.AlgebraicGeometry.Spaces.FormalAlgebraization
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosedPermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionPointEmbedding
public import StacksFrontier.AlgebraicGeometry.Spaces.PointsRepresented
public import StacksFrontier.Topology.Algebra.AdicTopology.FaithfullyFlatModWeakIdeal

/-!
# Open sets containing the closed fibre of a universally closed space

Let `A` be a ring complete with respect to an ideal `I`, so that `I` lies in the Jacobson
radical of `A`, and let `X` be an algebraic space universally closed over `S = Spec A`. An open
subset of `|X|` containing the points of the closed fibre `X_0 = X ×_S Spec (A / I)` is all of
`|X|`: the image in `Spec A` of its closed complement is closed and misses `V(I)`, and a nonempty
closed subset of `Spec A` contains a maximal ideal, which contains `I`.

## Main results

* `AlgebraicGeometry.Space.eq_univ_of_isOpen_of_range_adicFibre_subset`: the statement above.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_QuasiSeparatedAlgebraizationClosedFibre
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_QuasiSeparatedAlgebraizationClosedFibre
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  hasPullbacks_presheaf_QuasiSeparatedAlgebraizationClosedFibre.has_limit _

attribute [local instance] pointTopology

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))} {hSn : ∀ n, B.Contains (adicThickening A I n)}

/-- **An open set of points containing the closed fibre of a universally closed space is
everything.** Let `I` lie in the Jacobson radical of `A` and `X ⟶ Spec A` be universally closed.
An open subset of `|X|` containing the image of `|X_0|` is all of `|X|`. -/
theorem eq_univ_of_isOpen_of_range_adicFibre_subset (hI : I ≤ Ideal.jacobson ⊥)
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (fX : X ⟶ yoneda.obj (baseObject A B hS)) (huc : UniversallyClosed B _ hS fX)
    {U : Set (points B _ hS X)} (hU : IsOpen U)
    (h0 : Set.range (pointsMap B _ hS _
      (pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn 0)))) ⊆ U) :
    U = Set.univ := by
  have hbase := isAlgebraicSpace_yoneda B _ hS (baseObject A B hS)
  set D := pointsMap B _ hS X fX '' Uᶜ
  have hD : IsClosed D := isClosed_of_universallyClosed B _ hS hbase fX huc _ hU.isClosed_compl
  have hdisj : ∀ x ∈ D, x ∉ Set.range (pointsMap B _ hS _
      (yoneda.map (adicThickeningMap A I B hS hSn 0))) := by
    rintro _ ⟨x, hx, rfl⟩ ⟨t, ht⟩
    obtain ⟨w, hw, -⟩ := exists_points_of_isPullback B _ hS
      (IsPullback.of_hasPullback fX (yoneda.map (adicThickeningMap A I B hS hSn 0))) x t ht.symm
    exact hx (h0 ⟨w, hw⟩)
  -- read the image on `Spec A`
  let e := schemePointsHomeomorph B _ hS (baseObject A B hS)
  have hC : IsClosed (e '' D) := e.isClosedMap _ hD
  by_contra hne
  obtain ⟨x, hx⟩ : (Uᶜ).Nonempty := by
    rw [Set.nonempty_compl]
    exact hne
  have hCne : (e '' D).Nonempty := ⟨_, ⟨_, ⟨x, hx, rfl⟩, rfl⟩⟩
  let C : Set (PrimeSpectrum A) := e '' D
  obtain ⟨K, hK⟩ := (PrimeSpectrum.isClosed_iff_zeroLocus_ideal C).1 hC
  have hKtop : K ≠ ⊤ := by
    rintro rfl
    obtain ⟨y, hy⟩ := hCne
    have : y ∈ PrimeSpectrum.zeroLocus ((⊤ : Ideal A) : Set A) := by
      rw [← hK]
      exact hy
    rw [Submodule.top_coe, PrimeSpectrum.zeroLocus_univ] at this
    exact this
  obtain ⟨m, hm, hKm⟩ := Ideal.exists_le_maximal K hKtop
  let y : PrimeSpectrum A := ⟨m, hm.isPrime⟩
  have hyC : y ∈ C := by
    rw [hK]
    exact hKm
  obtain ⟨d, hd, hde⟩ := hyC
  refine hdisj d hd ?_
  rw [range_pointsMap_yoneda_eq_preimage, Set.mem_preimage]
  have hIm : I ^ (0 + 1) ≤ y.asIdeal := by
    rw [zero_add, pow_one]
    exact hI.trans (sInf_le ⟨bot_le, hm⟩)
  have := PrimeSpectrum.mem_range_comap_quotientMk hIm
  rw [← schemePointsHomeomorph_apply, show e d = y from hde]
  exact this

end AlgebraicGeometry.Space

end
