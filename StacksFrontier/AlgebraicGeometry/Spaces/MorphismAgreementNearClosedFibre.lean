module

public import StacksFrontier.AlgebraicGeometry.Spaces.AdicFibreFlatAtClosedFibre
public import StacksFrontier.AlgebraicGeometry.Spaces.DiagonalProperties
public import StacksFrontier.AlgebraicGeometry.Spaces.EtalePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.MapDescent
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeDiagonal
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.OpenSubspaceCoveringLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.SteinConnectedFibreCore
public import StacksFrontier.AlgebraicGeometry.Spaces.UniversallyClosed

/-!
# Morphisms agreeing on the adic fibres agree near the closed fibre

Let `A` be a Noetherian ring, `I ⊆ A` an ideal, and `φ, φ' : U ⟶ Y` two morphisms of algebraic
spaces over `S = Spec A`, with `U` locally of finite type over `S`. If `φ` and `φ'` have the
same adic fibres `U_n ⟶ Y_n`, they agree on an open subspace of `U` containing the closed fibre.

Their equalizer `K = U ×_{Y ×_S Y} Y ⟶ U` is a monomorphism locally of finite type (the
relative diagonal of `Y ⟶ S` is), and every `U_n ⟶ U` factors through it, so the adic fibres
`K_n ⟶ U_n` are isomorphisms. By the étale form of the local criterion of flatness along the
closed fibre,
`AlgebraicGeometry.Space.exists_isOpenSubspace_isEtale_of_forall_isEtale_adicFibreMap`,
`K ⟶ U` is étale on an open subspace `W'` of `K` containing the closed fibre; an étale
monomorphism is an open immersion, and its image is the open subspace sought.

## Main results

* `AlgebraicGeometry.Space.exists_isOpenSubspace_comp_eq_of_forall_adicFibreMap_eq`: the
  statement above.
* `AlgebraicGeometry.Space.eq_top_of_isOpenSubspace_of_forall_range_adicFibre_le`: over a ring
  complete with respect to `I`, an open subspace of a proper algebraic space containing an adic
  fibre is everything.
* `AlgebraicGeometry.Space.eq_of_forall_adicFibreMap_eq_of_isQuasiSeparated`: for a proper
  source over a complete Noetherian base, a morphism into a quasi-separated space locally of
  finite type is determined by its adic fibres (the uniqueness half of Stacks 0GHK).

## References

* [Stacks Project, Tag 0GHK](https://stacks.math.columbia.edu/tag/0GHK)
* [Stacks Project, Tag 05W5](https://stacks.math.columbia.edu/tag/05W5)
-/

@[expose] public noncomputable section

attribute [local instance] AlgebraicGeometry.Space.pointTopology

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

/-- Pullbacks of presheaves on `BigFppfOver B S hS`, given directly: instance search for them
times out under Lean v4.35.0. -/
local instance (priority := high) hasPullbacks_presheaf_MorphismAgreementNearClosedFibre
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} :
    HasPullbacks ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
  Limits.functorCategoryHasLimitsOfShape

local instance (priority := high) hasPullback_presheaf_MorphismAgreementNearClosedFibre
    {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {X Y Z : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (f : X ⟶ Z) (g : Y ⟶ Z) : HasLimit (cospan f g) :=
  hasPullbacks_presheaf_MorphismAgreementNearClosedFibre.has_limit _

variable {A : Type u} [CommRing A] {I : Ideal A} {B : BigFppfSite.{u}}
  {hS : B.Contains (Spec (.of A))} {hSn : ∀ n, B.Contains (adicThickening A I n)}

/-- **Morphisms with the same adic fibres agree near the closed fibre.** Let `A` be Noetherian
and `φ, φ' : U ⟶ Y` morphisms of algebraic spaces over `Spec A`, with `U` locally of finite type
over `Spec A`. If `φ` and `φ'` have the same adic fibres, they agree on an open subspace of `U`
containing every adic fibre `U_n`. -/
theorem exists_isOpenSubspace_comp_eq_of_forall_adicFibreMap_eq [IsNoetherianRing A]
    {U Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hU : IsAlgebraicSpace B _ hS U) (hY : IsAlgebraicSpace B _ hS Y)
    {fU : U ⟶ yoneda.obj (baseObject A B hS)} {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (hlU : IsLocallyOfFiniteType B _ hS fU) (_hqY : IsQuasiSeparated B _ hS fY)
    (_hlY : IsLocallyOfFiniteType B _ hS fY) {φ φ' : U ⟶ Y} (hφ : φ ≫ fY = fU)
    (hφ' : φ' ≫ fY = fU)
    (h : ∀ n, adicFibreMap A I B hS hSn φ hφ n = adicFibreMap A I B hS hSn φ' hφ' n) :
    ∃ W : Subfunctor U, IsOpenSubspace B _ hS W ∧
      (∀ n, Subfunctor.range (pullback.fst fU (yoneda.map (adicThickeningMap A I B hS hSn n))) ≤
        W) ∧
      W.ι ≫ φ = W.ι ≫ φ' := by
  -- the equalizer `K ⟶ U`
  let ψ : U ⟶ pullback fY fY := pullback.lift φ φ' (by rw [hφ, hφ'])
  let Δ := pullback.diagonal fY
  let k : pullback ψ Δ ⟶ U := pullback.fst ψ Δ
  have hΔ : (MorphismProperty.presheaf (MorphismProperty.inverseImage
      (@LocallyOfFiniteType.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B _ hS))) Δ :=
    presheaf_of_isPullback B _ hS (isPullback_pullbackDiagonal_diag B _ hS fY)
      (presheaf_locallyOfFiniteType_diag B _ hS Y hY)
  have hlk : IsLocallyOfFiniteType B _ hS k :=
    presheafImpliesHoldsOnEveryEtaleChart_locallyOfFiniteType B _ hS k
      (presheaf_of_isPullback B _ hS (IsPullback.of_hasPullback ψ Δ).flip hΔ)
  have hK : IsAlgebraicSpace B _ hS (pullback ψ Δ) :=
    isAlgebraicSpace_pullback B _ hS ψ Δ hU hY
      (isAlgebraicSpace_pullback B _ hS fY fY hY hY
        (isAlgebraicSpace_yoneda B _ hS (baseObject A B hS)))
  have hΔmono : Mono Δ := IsSplitMono.mono _
  have hkmono : Mono k := pullback.fst_of_mono
  have e := pullback.condition (f := ψ) (g := Δ)
  have h1 : k ≫ φ = pullback.snd ψ Δ :=
    calc k ≫ φ = k ≫ ψ ≫ pullback.fst fY fY := by rw [pullback.lift_fst]
      _ = pullback.snd ψ Δ ≫ Δ ≫ pullback.fst fY fY := by rw [← Category.assoc, e, Category.assoc]
      _ = _ := by rw [pullback.diagonal_fst, Category.comp_id]
  have h2 : k ≫ φ' = pullback.snd ψ Δ :=
    calc k ≫ φ' = k ≫ ψ ≫ pullback.snd fY fY := by rw [pullback.lift_snd]
      _ = pullback.snd ψ Δ ≫ Δ ≫ pullback.snd fY fY := by rw [← Category.assoc, e, Category.assoc]
      _ = _ := by rw [pullback.diagonal_snd, Category.comp_id]
  have hkφ : k ≫ φ = k ≫ φ' := h1.trans h2.symm
  -- the adic fibres of `K ⟶ U` are isomorphisms
  have hiso : ∀ n, IsIso (adicFibreMap A I B hS hSn (fG := fU) k rfl n) := by
    intro n
    have hfst : pullback.fst fU (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫ φ =
        pullback.fst fU (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫ φ' := by
      have := congrArg (· ≫ pullback.fst fY (yoneda.map (adicThickeningMap A I B hS hSn n)))
        (h n)
      simpa only [adicFibreMap_fst] using this
    have hψ1 : ψ ≫ pullback.fst fY fY = φ := pullback.lift_fst _ _ _
    have hψ2 : ψ ≫ pullback.snd fY fY = φ' := pullback.lift_snd _ _ _
    let t : adicFibre A I B hS hSn fU n ⟶ pullback ψ Δ :=
      pullback.lift (pullback.fst fU (yoneda.map (adicThickeningMap A I B hS hSn n)))
        (pullback.fst fU (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫ φ) (by
        apply pullback.hom_ext
        · rw [Category.assoc, Category.assoc, hψ1, pullback.diagonal_fst, Category.comp_id]
        · rw [Category.assoc, Category.assoc, hψ2, pullback.diagonal_snd, Category.comp_id,
            hfst])
    have htk : t ≫ k = pullback.fst fU (yoneda.map (adicThickeningMap A I B hS hSn n)) :=
      pullback.lift_fst _ _ _
    have hts : t ≫ pullback.snd ψ Δ =
        pullback.fst fU (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫ φ :=
      pullback.lift_snd _ _ _
    let s : adicFibre A I B hS hSn fU n ⟶ adicFibre A I B hS hSn (k ≫ fU) n :=
      pullback.lift t (pullback.snd fU (yoneda.map (adicThickeningMap A I B hS hSn n))) (by
        rw [← Category.assoc, htk, pullback.condition])
    have hsf : s ≫ pullback.fst (k ≫ fU) (yoneda.map (adicThickeningMap A I B hS hSn n)) = t :=
      pullback.lift_fst _ _ _
    have hss : s ≫ pullback.snd (k ≫ fU) (yoneda.map (adicThickeningMap A I B hS hSn n)) =
        pullback.snd fU (yoneda.map (adicThickeningMap A I B hS hSn n)) := pullback.lift_snd _ _ _
    refine ⟨s, ?_, ?_⟩
    · apply pullback.hom_ext
      · rw [Category.assoc, hsf, Category.id_comp]
        apply pullback.hom_ext
        · rw [Category.assoc, htk, adicFibreMap_fst]
        · rw [Category.assoc, hts, ← Category.assoc, adicFibreMap_fst, Category.assoc, h1]
      · rw [Category.assoc, hss, adicFibreMap_snd, Category.id_comp]
    · apply pullback.hom_ext
      · rw [Category.assoc, adicFibreMap_fst, ← Category.assoc, hsf, htk, Category.id_comp]
      · rw [Category.assoc, adicFibreMap_snd, hss, Category.id_comp]
  -- étale along the closed fibre, hence an open immersion there
  obtain ⟨W', hW', hfib', hWE'⟩ :=
    exists_isOpenSubspace_isEtale_of_forall_isEtale_adicFibreMap (I := I) (hSn := hSn) hK hU hlU
      k rfl hlk fun n => isEtale_of_isIso B _ hS _
  have hoi : IsOpenImmersion B _ hS (W'.ι ≫ k) :=
    isOpenImmersion_of_isEtale_of_mono B _ hS (W'.ι ≫ k) hW'.1 hU hWE' inferInstance
  refine ⟨Subfunctor.range (W'.ι ≫ k), isOpenSubspace_subfunctorRange B _ hS hW'.1 hoi,
    fun n => ?_, ?_⟩
  · rintro V _ ⟨y, rfl⟩
    have hsec : pullback.fst fU (yoneda.map (adicThickeningMap A I B hS hSn n)) =
        inv (adicFibreMap A I B hS hSn (fG := fU) k rfl n) ≫
          pullback.fst (k ≫ fU) (yoneda.map (adicThickeningMap A I B hS hSn n)) ≫ k := by
      rw [IsIso.eq_inv_comp, adicFibreMap_fst]
    have hmem := hfib' n V ⟨(inv (adicFibreMap A I B hS hSn (fG := fU) k rfl n)).app V y, rfl⟩
    refine ⟨⟨_, hmem⟩, ?_⟩
    rw [hsec]
    rfl
  · ext V ⟨x, w, rfl⟩
    exact congrArg (fun g => g.app V w.1) hkφ

/-- **An open subspace containing an adic fibre of a proper space is everything.** Let `A` be
complete with respect to `I` and `X` proper over `Spec A`. An open subspace `W ⊆ X` containing
an adic fibre `X_n` is all of `X`: the image in `Spec A` of the closed complement of `W` is
closed, so if it were nonempty it would contain a closed point, which lies in `V(I)` because `I`
is contained in the Jacobson radical; a point of `X` over it lies in `X_n`, hence in `W`. -/
theorem eq_top_of_isOpenSubspace_of_forall_range_adicFibre_le [IsAdicComplete I A]
    {X : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B _ hS X)
    {fX : X ⟶ yoneda.obj (baseObject A B hS)} (hpX : IsProper B _ hS fX) (W : Subfunctor X)
    (hW : IsOpenSubspace B _ hS W) (n : ℕ)
    (hle : Subfunctor.range (pullback.fst fX (yoneda.map (adicThickeningMap A I B hS hSn n))) ≤
      W) : W = ⊤ := by
  refine eq_top_of_range_pointsMap_eq_univ B _ hS hX W hW ?_
  by_contra hne
  obtain ⟨z, hz⟩ := (Set.ne_univ_iff_exists_notMem _).mp hne
  set Z : Set (points B _ hS X) := (Set.range (pointsMap B _ hS _ W.ι))ᶜ
  have hZ : IsClosed Z := (isOpen_range_pointsMap_of_isOpenImmersion B _ hS W.ι hW.2).isClosed_compl
  have hcm : IsClosedMap (pointsMap B _ hS X fX) :=
    isClosedMap_pointsMap_of_pullback_fst_id B _ hS fX
      (hpX.2.2 _ (isAlgebraicSpace_yoneda B _ hS (baseObject A B hS)) (𝟙 _))
  let C : Set (PrimeSpectrum A) :=
    (schemePointsHomeomorph B _ hS (baseObject A B hS)) '' (pointsMap B _ hS X fX '' Z)
  have hC : IsClosed C := (schemePointsHomeomorph B _ hS (baseObject A B hS)).isClosedMap _
    (hcm _ hZ)
  -- a closed point of `C`
  have hJ : PrimeSpectrum.vanishingIdeal C ≠ ⊤ := by
    intro htop
    have h1 : (1 : A) ∈ PrimeSpectrum.vanishingIdeal C := htop ▸ Submodule.mem_top
    have hc : schemePointsHomeomorph B _ hS (baseObject A B hS) (pointsMap B _ hS X fX z) ∈ C :=
      ⟨_, ⟨z, hz, rfl⟩, rfl⟩
    exact ((schemePointsHomeomorph B _ hS (baseObject A B hS)
      (pointsMap B _ hS X fX z) : PrimeSpectrum A).isPrime.ne_top
      ((Ideal.eq_top_iff_one _).mpr ((PrimeSpectrum.mem_vanishingIdeal _ _).mp h1 _ hc)))
  obtain ⟨M, hM, hJM⟩ := Ideal.exists_le_maximal _ hJ
  have hmC : (⟨M, hM.isPrime⟩ : PrimeSpectrum A) ∈ C := by
    rw [← hC.closure_eq, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    exact hJM
  obtain ⟨_, ⟨z', hz', rfl⟩, hm⟩ := hmC
  -- the closed point lies in `V(I)`
  have hIM : I ^ (n + 1) ≤ M := (Ideal.pow_le_self (Nat.succ_ne_zero n)).trans
    ((IsAdicComplete.le_jacobson_bot I).trans (sInf_le ⟨bot_le, hM⟩))
  let t : PrimeSpectrum (A ⧸ I ^ (n + 1)) :=
    ⟨M.map (Ideal.Quotient.mk _), Ideal.map_isPrime_of_surjective Ideal.Quotient.mk_surjective
      (by rwa [Ideal.mk_ker])⟩
  have ht : (BigFppfOver.toScheme B _ hS).map (adicThickeningMap A I B hS hSn n) t =
      ⟨M, hM.isPrime⟩ := by
    refine PrimeSpectrum.ext ?_
    change Ideal.comap (Ideal.Quotient.mk _) (M.map (Ideal.Quotient.mk _)) = M
    rw [Ideal.comap_map_of_surjective _ Ideal.Quotient.mk_surjective, ← RingHom.ker_eq_comap_bot,
      Ideal.mk_ker, sup_eq_left.mpr hIM]
  obtain ⟨x', hx', -⟩ := exists_points_of_isPullback_yoneda_map
    (IsPullback.of_hasPullback fX (yoneda.map (adicThickeningMap A I B hS hSn n))) z' t
    (hm.trans ht.symm)
  apply hz'
  rw [← hx', ← Subfunctor.lift_ι _ hle, pointsMap_comp_apply]
  exact ⟨_, rfl⟩

/-- **Uniqueness of algebraization into a quasi-separated space (Stacks 0GHK, uniqueness).** Let
`A` be a Noetherian ring complete with respect to `I`, `X` proper over `Spec A` and `Y`
quasi-separated and locally of finite type over `Spec A`. Two morphisms `X ⟶ Y` over `Spec A`
with the same adic fibres are equal. -/
theorem eq_of_forall_adicFibreMap_eq_of_isQuasiSeparated [IsNoetherianRing A] [IsAdicComplete I A]
    {X Y : (BigFppfOver B (Spec (.of A)) hS)ᵒᵖ ⥤ Type u}
    (hX : IsAlgebraicSpace B _ hS X) (hY : IsAlgebraicSpace B _ hS Y)
    {fX : X ⟶ yoneda.obj (baseObject A B hS)} {fY : Y ⟶ yoneda.obj (baseObject A B hS)}
    (hpX : IsProper B _ hS fX) (hqY : IsQuasiSeparated B _ hS fY)
    (hlY : IsLocallyOfFiniteType B _ hS fY)
    {φ φ' : X ⟶ Y} (hφ : φ ≫ fY = fX) (hφ' : φ' ≫ fY = fX)
    (h : ∀ n, adicFibreMap A I B hS hSn φ hφ n = adicFibreMap A I B hS hSn φ' hφ' n) :
    φ = φ' := by
  obtain ⟨W, hW, hfib, hWeq⟩ := exists_isOpenSubspace_comp_eq_of_forall_adicFibreMap_eq hX hY
    hpX.2.1.1 hqY hlY hφ hφ' h
  have hWtop := eq_top_of_isOpenSubspace_of_forall_range_adicFibre_le hX hpX W hW 0 (hfib 0)
  ext V x
  have hx : x ∈ W.obj V := by
    rw [hWtop]
    trivial
  exact congrArg (fun g => g.app V ⟨x, hx⟩) hWeq

end AlgebraicGeometry.Space

end
