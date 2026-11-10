module

public import StacksFrontier.AlgebraicGeometry.FormalGeometry.AlgebraizationCoherentFormal.ImprovingFormalModulesDepthThree
public import StacksFrontier.AlgebraicGeometry.LocalCohomology.ImprovingCoherentModules.DepthTwoExtensionConstruction
public import StacksFrontier.AlgebraicGeometry.Algebraization.DistanceSpecialization
public import StacksFrontier.RingTheory.Catenary.Formal
public import StacksFrontier.RingTheory.Dualizing.Complex
public import StacksFrontier.RingTheory.Dualizing.UniversallyCatenary

/-!
# The inputs of the depth-two improvement on the open `U` of an algebraization situation

Fix an algebraization situation: a Noetherian ring `A` with ideals `I ⊆ 𝔞`, with `X = Spec(A)`,
`Y = V(I)`, `Z = V(𝔞)` and `U = X ∖ Z`, and let `δ^Y_Z` be the distance of a point of `Y` from
`Z`. The proof of [Stacks, Tag 0EJG] applies [Stacks, Tag 0EJF] on the Noetherian scheme `U`, to
the closed subscheme `U ∩ Y` cut out by `I𝒪_U`, with `T = {δ^Y_Z ≤ 2}` and `T' = {δ^Y_Z ≤ 1}`.
This file proves the hypotheses of that application which do not involve the formal module.

## Main results

* `Stacks.Algebraization.AlgebraizationSituation.hasDualizingComplexOnAffineCover_U`: if `A` has
  a dualizing complex then `U` locally has one: every point of `U` lies in a basic open
  `D(f) ⊆ U`, whose ring of sections `A_f` carries the localized dualizing complex
  ([Stacks, Tag 0A7G]).
* `Stacks.Algebraization.AlgebraizationSituation.mem_support_idealOnOpen_iff`: the points of the
  support of `I𝒪_U` are the points of `U` lying over a point of `Y`.
* `Stacks.Algebraization.AlgebraizationSituation.distanceToZSublevel_subset_support`: the loci
  `{δ^Y_Z ≤ k}` lie in `U ∩ Y`.
* `Stacks.Algebraization.AlgebraizationSituation.`
  `mem_distanceToZSublevel_two_of_isImmediateSpecialization`:
  condition (e) of [Stacks, Tag 0EJF]: if `y ⇝ y'` is an immediate specialization of points of
  `U ∩ Y` with `y' ∈ T'`, then `y ∈ T`. This uses that `δ^Y_Z` grows by at most one along an
  immediate specialization ([Stacks, Tag 0EIY]), which needs `Y` catenary; a ring with a
  dualizing complex is universally catenary ([Stacks, Tag 0A80]).

## References

* [Stacks Project, Tag 0EJG](https://stacks.math.columbia.edu/tag/0EJG)
* [Stacks Project, Tag 0EJF](https://stacks.math.columbia.edu/tag/0EJF)
* [Stacks Project, Tag 0EIY](https://stacks.math.columbia.edu/tag/0EIY)
* [Stacks Project, Tag 0A7G](https://stacks.math.columbia.edu/tag/0A7G)
* [Stacks Project, Tag 0A80](https://stacks.math.columbia.edu/tag/0A80)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace

universe u

namespace Stacks.Algebraization

namespace AlgebraizationSituation

variable (S : AlgebraizationSituation.{u})

/-! ### A dualizing complex on the affine opens of a basic open cover of `U` -/

/-- **`U` locally has a dualizing complex.** If `A` has a dualizing complex, then every point
of `U = Spec(A) ∖ V(𝔞)` has an affine open neighbourhood in `U` whose ring of sections has a
dualizing complex: a basic open `D(f) ⊆ U` with `f ∈ 𝔞`, whose ring of sections is `A_f`. -/
public theorem hasDualizingComplexOnAffineCover_U
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K) :
    HasDualizingComplexOnAffineCover S.U.toScheme := by
  obtain ⟨K, hK⟩ := hdual
  intro y
  set x : PrimeSpectrum S.A := S.U.ι.base y with hx
  have hxU : ¬ S.a ≤ x.asIdeal := by
    have hmem : S.U.ι.base y ∈ (S.U : Set S.X) := by
      rw [← Scheme.Opens.range_ι S.U]
      exact Set.mem_range_self y
    intro hle
    exact hmem ((PrimeSpectrum.mem_zeroLocus x (S.a : Set S.A)).mpr hle)
  obtain ⟨f, hfa, hfx⟩ := Set.not_subset.mp hxU
  let W : S.X.Opens := PrimeSpectrum.basicOpen (R := S.A) f
  have hW : IsAffineOpen W := IsAffineOpen.Spec_basicOpen (R := CommRingCat.of S.A) f
  have hWU : W ≤ S.U.ι.opensRange := by
    rw [Scheme.Opens.opensRange_ι]
    intro p hp hpa
    exact hp ((PrimeSpectrum.mem_zeroLocus (p : PrimeSpectrum S.A) (S.a : Set S.A)).mp hpa hfa)
  let V : S.U.toScheme.Opens := S.U.ι ⁻¹ᵁ W
  refine ⟨⟨V, hW.preimage_of_isOpenImmersion S.U.ι hWU⟩, hfx, ?_⟩
  -- the ring of sections of `V` is that of `W`, a localization of `A` away from `f`
  have himg : S.U.ι ''ᵁ V = W := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, inf_eq_right.mpr hWU]
  let e : Γ(S.X, W) ≃+* Γ(S.U.toScheme, V) :=
    ((S.X.presheaf.mapIso (eqToIso himg).op) ≪≫ S.U.ι.appIso V).commRingCatIsoToRingEquiv
  let : Algebra S.A Γ(S.X, W) :=
    inferInstanceAs (Algebra S.A ((Spec.structureSheaf S.A).obj.obj (op W)))
  have hloc : IsLocalization.Away f Γ(S.X, W) :=
    StructureSheaf.IsLocalization.to_basicOpen S.A f
  let : Algebra S.A Γ(S.U.toScheme, V) := ((e : _ →+* _).comp (algebraMap S.A Γ(S.X, W))).toAlgebra
  let eA : Γ(S.X, W) ≃ₐ[S.A] Γ(S.U.toScheme, V) :=
    AlgEquiv.ofRingEquiv (f := e) fun _ => rfl
  have : IsLocalization (Submonoid.powers f) Γ(S.U.toScheme, V) :=
    IsLocalization.isLocalization_of_algEquiv (Submonoid.powers f) eA
  exact ⟨_, Dualizing.isDualizingComplex_localization (Submonoid.powers f) K hK⟩

/-! ### The support of `I𝒪_U` -/

/-- The points of the support of `I𝒪_U` are the points of `U` whose image in `X` lies in
`Y = V(I)`, that is, which lie over a point of `Y`. -/
public theorem mem_support_idealOnOpen_iff (y : S.U.toScheme) :
    y ∈ (idealOnOpen S).support ↔ ∃ z : S.Y, S.U.ι.base y = S.Yι.base z := by
  have hsupp : y ∈ (idealOnOpen S).support ↔ S.I ≤ (S.U.ι.base y : PrimeSpectrum S.A).asIdeal := by
    change y ∈ (((Scheme.IdealSheafData.ofIdealTop
      (S.I.map (Scheme.ΓSpecIso (.of S.A)).inv.hom)).comap S.U.ι).support : Set _) ↔ _
    rw [Scheme.IdealSheafData.support_comap, Closeds.coe_preimage, Set.mem_preimage,
      Scheme.IdealSheafData.coe_support_ofIdealTop, Ideal.map, Scheme.zeroLocus_span,
      Spec_zeroLocus_eq_zeroLocus]
    exact (PrimeSpectrum.mem_zeroLocus (S.U.ι.base y : PrimeSpectrum S.A) (S.I : Set S.A)).trans
      SetLike.coe_subset_coe
  rw [hsupp]
  constructor
  · intro hI
    have := (S.U.ι.base y : PrimeSpectrum S.A).isPrime
    let z : PrimeSpectrum (S.A ⧸ S.I) :=
      ⟨(S.U.ι.base y : PrimeSpectrum S.A).asIdeal.map (Ideal.Quotient.mk S.I),
        Ideal.isPrime_map_quotientMk_of_isPrime hI⟩
    exact ⟨z, PrimeSpectrum.ext (Ideal.comap_map_mk hI).symm⟩
  · rintro ⟨z, hz⟩
    rw [hz]
    intro a ha
    change Ideal.Quotient.mk S.I a ∈ (z : PrimeSpectrum (S.A ⧸ S.I)).asIdeal
    rw [Ideal.Quotient.eq_zero_iff_mem.mpr ha]
    exact Ideal.zero_mem _

/-- The loci `{y ∈ U ∩ Y : δ^Y_Z(y) ≤ k}` lie in the support of `I𝒪_U`. -/
public theorem distanceToZSublevel_subset_support (k : ℕ∞) :
    S.distanceToZSublevel k ⊆ ((idealOnOpen S).support : Set S.U.toScheme) := by
  rintro y ⟨z, hyz, -⟩
  exact (S.mem_support_idealOnOpen_iff y).mpr ⟨z, hyz⟩

/-! ### Condition (e): immediate specializations into `T'` start in `T` -/

/-- If `A` is universally catenary, then `Y = Spec(A ⧸ I)` is a catenary space. -/
public theorem isCatenarySpace_Y (hcat : Ring.IsUniversallyCatenary S.A) :
    IrreducibleClosedsCodim.IsCatenarySpace S.Y :=
  isCatenarySpace_of_isCatenary (hcat (S.A ⧸ S.I))

/-- An immediate specialization inside `U` between points of `U ∩ Y` is an immediate
specialization inside `Y`: a point of `Y` between them is a generization of a point of the open
`U`, hence lies in `U`. -/
public theorem isImmediateSpecialization_Y {y y' : S.U.toScheme} {z z' : S.Y}
    (hyz : S.U.ι.base y = S.Yι.base z) (hyz' : S.U.ι.base y' = S.Yι.base z')
    (h : IsImmediateSpecialization y y') : IsImmediateSpecialization z z' := by
  have hY : Topology.IsClosedEmbedding S.Yι.base := S.Yι.isClosedEmbedding
  have hU : Topology.IsOpenEmbedding S.U.ι.base := S.U.ι.isOpenEmbedding
  obtain ⟨hspec, hne, hbetween⟩ := h
  refine ⟨?_, ?_, ?_⟩
  · refine hY.isInducing.specializes_iff.mp ?_
    rw [← hyz, ← hyz']
    exact hspec.map S.U.ι.continuous
  · intro hzz
    apply hne
    apply hU.injective
    rw [hyz, hyz', hzz]
  · intro w hzw hwz'
    have hXw' : S.Yι.base w ⤳ S.U.ι.base y' := by
      rw [hyz']
      exact hwz'.map S.Yι.continuous
    obtain ⟨v, hv⟩ := hXw'.mem_open hU.isOpen_range ⟨y', rfl⟩
    have hyv : y ⤳ v := by
      refine hU.isInducing.specializes_iff.mp ?_
      rw [hv, hyz]
      exact hzw.map S.Yι.continuous
    have hvy' : v ⤳ y' := by
      refine hU.isInducing.specializes_iff.mp ?_
      rw [hv]
      exact hXw'
    rcases hbetween v hyv hvy' with rfl | rfl
    · left
      exact hY.injective (hv.symm.trans hyz)
    · right
      exact hY.injective (hv.symm.trans hyz')

/-- **Condition (e) of [Stacks, Tag 0EJF] for `T = {δ ≤ 2}` and `T' = {δ ≤ 1}`.** If `A` is
universally catenary, `y` is a point of `U ∩ Y` and `y ⇝ y'` is an immediate specialization in
`U` with `δ^Y_Z(y') ≤ 1`, then `δ^Y_Z(y) ≤ 2`. -/
public theorem mem_distanceToZSublevel_two_of_isImmediateSpecialization
    (hcat : Ring.IsUniversallyCatenary S.A) (y y' : S.U.toScheme)
    (hy : y ∈ (idealOnOpen S).support) (h : IsImmediateSpecialization y y')
    (hy' : y' ∈ S.distanceToZSublevel 1) : y ∈ S.distanceToZSublevel 2 := by
  obtain ⟨z, hyz⟩ := (S.mem_support_idealOnOpen_iff y).mp hy
  obtain ⟨z', hyz', hz'⟩ := hy'
  have himm := S.isImmediateSpecialization_Y hyz hyz' h
  have hle := distanceFunction_le_add_one_of_isImmediateSpecialization S.Y S.closedSubsetZ
    (S.isCatenarySpace_Y hcat) himm
  refine ⟨z, hyz, hle.trans ?_⟩
  calc distanceFunction S.Y S.closedSubsetZ z' + 1 ≤ 1 + 1 := add_le_add hz' le_rfl
    _ = 2 := by norm_num

/-- Condition (e) of [Stacks, Tag 0EJF] for `T = {δ ≤ 2}` and `T' = {δ ≤ 1}`, in the form the
construction of the improved system takes it, when `A` has a dualizing complex. -/
public theorem forall_mem_distanceToZSublevel_two_of_isImmediateSpecialization
    (hdual : ∃ K : DerivedCategory (ModuleCat.{u} S.A), Dualizing.IsDualizingComplex K) :
    ∀ y y' : S.U.toScheme, y ∈ (idealOnOpen S).support → IsImmediateSpecialization y y' →
      y' ∈ S.distanceToZSublevel 1 → y ∈ S.distanceToZSublevel 2 := by
  obtain ⟨K, hK⟩ := hdual
  exact S.mem_distanceToZSublevel_two_of_isImmediateSpecialization
    (Dualizing.isUniversallyCatenary_of_isDualizingComplex hK)

end AlgebraizationSituation

end Stacks.Algebraization

end
