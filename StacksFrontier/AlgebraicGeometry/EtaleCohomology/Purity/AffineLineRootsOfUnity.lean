module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineSupport
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RootsOfUnityGlobalSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Restriction.DegreeZeroSurjectivity
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Curves.GenericFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeGroupEtaleOverField
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.CohomologyPullbackMap

/-!
# The direct image of `μ_ℓ` along `𝐆_m ⟶ 𝐀¹`

Let `k` be an algebraically closed field, `ℓ` invertible in `k` and `j : 𝐆_m ⟶ 𝐀¹_k` the
inclusion of the punctured affine line. The unit `μ_ℓ ⟶ j_* j⁻¹ μ_ℓ` on `(𝐀¹)_étale` is an
isomorphism.

## Main results

* `Stacks.EtaleCohomology.Purity.mono_unit_multiplicative_punctured`: the unit
  `𝐆_m ⟶ j_* j⁻¹ 𝐆_m` on `(𝐀¹)_étale` is a monomorphism.
* `Stacks.EtaleCohomology.Purity.isIso_rootsOfUnityUnit`: the unit `μ_ℓ ⟶ j_* j⁻¹ μ_ℓ` on
  `(𝐀¹)_étale` is an isomorphism.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

namespace Stacks.EtaleCohomology.Purity

variable (k : Type u) [Field k]

/-- The punctured affine line `𝐆_m = D(T) ⊆ 𝐀¹_k` is affine. -/
instance isAffine_punctured : IsAffine (punctured k).toScheme :=
  (isAffineOpen_top (affineLine k)).basicOpen (coordinate k)

/-- The open immersion `𝐆_m ⟶ 𝐀¹_k` is quasi-compact. -/
instance quasiCompact_punctured_ι : QuasiCompact (punctured k).ι :=
  @AlgebraicGeometry.instQuasiCompactOfIsAffineHom _ _ _ (isAffineHom_of_isAffine _)

/-- The punctured affine line `𝐆_m ⊆ 𝐀¹_k` is nonempty. -/
theorem nonempty_punctured : Nonempty (punctured k) := by
  by_contra h
  rw [not_nonempty_iff] at h
  have hbot : punctured k = ⊥ := by
    ext x
    exact ⟨fun hx => (h.false ⟨x, hx⟩).elim, fun hx => hx.elim⟩
  have h2 := preimage_punctured_specIso_inv k
  rw [hbot] at h2
  have h3 : PrimeSpectrum.basicOpen (MvPolynomial.X ⟨0⟩ : MvPolynomial (ULift.{u} (Fin 1)) k) = ⊥ :=
    h2.symm.trans (by ext x; exact Iff.rfl)
  rw [PrimeSpectrum.basicOpen_eq_bot_iff] at h3
  exact MvPolynomial.X_ne_zero _ (h3.eq_zero)

/-- The open immersion `𝐆_m ⟶ 𝐀¹_k` is scheme-theoretically dominant. -/
instance isSchemeTheoreticallyDominant_punctured_ι :
    IsSchemeTheoreticallyDominant (punctured k).ι := by
  rw [isSchemeTheoreticallyDominant_iff_isDominant]
  refine ⟨?_⟩
  change Dense (Set.range (punctured k).ι.base)
  rw [Scheme.Opens.range_ι]
  obtain ⟨⟨x, hx⟩⟩ := nonempty_punctured k
  exact (punctured k).isOpen.dense ⟨x, hx⟩

/-- **Restricting units of an étale `𝐀¹`-scheme to its part over `𝐆_m` is injective**: the unit
`𝐆_m ⟶ j_* j⁻¹ 𝐆_m` of restriction to `𝐆_m` is a monomorphism. -/
theorem mono_unit_multiplicative_punctured :
    Mono ((etaleRestrictionAbelianDirectImageAdj.{u, 0} (punctured k).ι).unit.app
      (Stacks.Kummer.multiplicativeSheaf.{u, 0} (affineLine k))) := by
  have happ : ∀ W, Mono (((etaleRestrictionAbelianDirectImageAdj.{u, 0} (punctured k).ι).unit.app
      (Stacks.Kummer.multiplicativeSheaf.{u, 0} (affineLine k))).hom.app W) := by
    rintro ⟨V⟩
    rw [AddCommGrpCat.mono_iff_injective]
    intro a b hab
    obtain ⟨x, rfl⟩ := Stacks.Kummer.ofUnit_surjective.{u, 0} a
    obtain ⟨y, rfl⟩ := Stacks.Kummer.ofUnit_surjective.{u, 0} b
    change (Stacks.Kummer.multiplicativeSheaf.{u, 0} (affineLine k)).obj.map
        ((Scheme.Etale.smallEtaleComposeBaseChangeAdj (punctured k).ι).counit.app V).op
          (Stacks.Kummer.ofUnit x) =
      (Stacks.Kummer.multiplicativeSheaf.{u, 0} (affineLine k)).obj.map
        ((Scheme.Etale.smallEtaleComposeBaseChangeAdj (punctured k).ι).counit.app V).op
          (Stacks.Kummer.ofUnit y) at hab
    rw [Stacks.Kummer.map_ofUnit, Stacks.Kummer.map_ofUnit] at hab
    refine congrArg _ (Units.ext ?_)
    exact appTop_pullback_fst_injective (punctured k).ι V.hom
      (congrArg Units.val (Stacks.Kummer.ofUnit_injective.{u, 0} hab))
  exact Sheaf.Hom.mono_of_presheaf_mono _ _ _ (h := NatTrans.mono_of_mono_app _)

/-- A primitive `ℓ`-th root of unity of `k` in the global functions of a scheme over `k`. -/
theorem exists_isPrimitiveRoot_globalSections [IsSepClosed k] {ℓ : ℕ} (hℓ : IsUnit (ℓ : k))
    {X : Scheme.{u}} (f : X ⟶ Spec (.of k)) [Nontrivial Γ(X, ⊤)] :
    ∃ ζ : Γ(X, ⊤), IsPrimitiveRoot ζ ℓ := by
  have : NeZero (ℓ : k) := ⟨hℓ.ne_zero⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot k ℓ
  exact ⟨_, hζ.map_of_injective (f := ((Scheme.ΓSpecIso (.of k)).inv ≫ f.appTop).hom)
    (RingHom.injective _)⟩

variable [IsAlgClosed k] {ℓ : ℕ} (hℓ0 : 0 < ℓ) (hℓ : IsUnit (ℓ : k))

/-- The unit `μ_ℓ ⟶ j_* j⁻¹ μ_ℓ` of restriction to `𝐆_m`. -/
abbrev rootsOfUnityUnit :
    Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ ⟶
      (etaleAbelianDirectImage.{u, 0} (punctured k).ι).obj
        ((etaleRestriction.{u, 0} (punctured k).ι).obj
          (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ)) :=
  (etaleRestrictionAbelianDirectImageAdj.{u, 0} (punctured k).ι).unit.app _

omit [IsAlgClosed k] in
/-- The unit `μ_ℓ ⟶ j_* j⁻¹ μ_ℓ` of restriction to `𝐆_m` is a monomorphism. -/
theorem mono_rootsOfUnityUnit : Mono (rootsOfUnityUnit k (ℓ := ℓ)) := by
  have hnat := (etaleRestrictionAbelianDirectImageAdj.{u, 0} (punctured k).ι).unit.naturality
    (Stacks.Kummer.rootsOfUnityι.{u, 0} (affineLine k) ℓ)
  have := mono_unit_multiplicative_punctured k
  have hm : Mono ((Stacks.Kummer.rootsOfUnityι.{u, 0} (affineLine k) ℓ) ≫
      (etaleRestrictionAbelianDirectImageAdj.{u, 0} (punctured k).ι).unit.app
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} (affineLine k))) := mono_comp _ _
  rw [show (Stacks.Kummer.rootsOfUnityι.{u, 0} (affineLine k) ℓ) ≫
      (etaleRestrictionAbelianDirectImageAdj.{u, 0} (punctured k).ι).unit.app
        (Stacks.Kummer.multiplicativeSheaf.{u, 0} (affineLine k)) = _ from hnat] at hm
  exact @mono_of_mono _ _ _ _ _ _ _ hm

omit [IsAlgClosed k] in
/-- The restriction of the unit to `𝐆_m` is invertible. -/
theorem isIso_restriction_rootsOfUnityUnit :
    IsIso ((etaleRestriction.{u, 0} (punctured k).ι).map (rootsOfUnityUnit k (ℓ := ℓ))) := by
  let adj := etaleRestrictionAbelianDirectImageAdj.{u, 0} (punctured k).ι
  have := (etaleAbelianDirectImageFullyFaithfulOfIsOpenImmersion.{u, 0} (punctured k).ι).full
  have := (etaleAbelianDirectImageFullyFaithfulOfIsOpenImmersion.{u, 0} (punctured k).ι).faithful
  have htri :=
    adj.left_triangle_components (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ)
  have : IsIso (adj.counit.app ((etaleRestriction.{u, 0} (punctured k).ι).obj
      (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ))) := inferInstance
  exact IsIso.of_isIso_fac_right htri

omit [IsAlgClosed k] in
/-- `H⁰(X, j_* F) = H⁰(U, F)`, in cardinality. -/
theorem natCard_sheafH_zero_directImage {U X : Scheme.{u}} (j : U ⟶ X)
    (F : Sheaf U.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    Nat.card (Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, 0} j).obj F) 0) =
      Nat.card (Sheaf.H.{u + 1} F 0) := by
  let : MorphismProperty.ContainsIdentities (@Etale.{u}) := ⟨fun _ => inferInstance⟩
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 X)) := MorphismProperty.Over.mkIdTerminal _ _
  exact Nat.card_congr
    ((Sheaf.H.equiv₀ ((etaleAbelianDirectImage.{u, 0} j).obj F) hT).toEquiv.trans
      (Sheaf.H.equiv₀ F (smallEtaleBaseChangeFinalIsTerminal j)).toEquiv.symm)

omit [IsAlgClosed k] in
/-- Isomorphic sheaves have isomorphic cohomology, in cardinality. -/
theorem natCard_sheafH_congr {X : Scheme.{u}}
    {F G : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}} (e : F ≅ G) (n : ℕ) :
    Nat.card (Sheaf.H.{u + 1} F n) = Nat.card (Sheaf.H.{u + 1} G n) :=
  Nat.card_congr ⟨Sheaf.H.map e.hom n, Sheaf.H.map e.inv n,
    fun x => by rw [← Sheaf.H.map_comp_apply, e.hom_inv_id, Sheaf.H.map_id_apply],
    fun x => by rw [← Sheaf.H.map_comp_apply, e.inv_hom_id, Sheaf.H.map_id_apply]⟩

omit [IsAlgClosed k] in
/-- The restriction of `μ_ℓ` along an étale `j : U ⟶ X` is `μ_ℓ` on `U`. -/
def restrictionRootsOfUnityIso {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (n : ℕ) :
    (etaleRestriction.{u, 0} j).obj (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} X n) ≅
      Stacks.Kummer.rootsOfUnitySheaf.{u, 0} U n :=
  have := (extensionByZeroAdj.{u, 0} j).rightAdjoint_preservesLimits.{0, 0}
  PreservesKernel.iso (etaleRestriction.{u, 0} j) (Stacks.Kummer.powMap.{u, 0} X n) ≪≫
    kernelIsoOfEq (by
      change (etaleRestriction.{u, 0} j).map (n • 𝟙 _) = n • 𝟙 _
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
      rfl)

include hℓ0 hℓ in
/-- `H⁰(𝐀¹, μ_ℓ)` has `ℓ` elements. -/
theorem natCard_sheafH_zero_rootsOfUnity_affineLine :
    Nat.card (Sheaf.H.{u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ) 0) = ℓ := by
  have : Nontrivial Γ(affineLine k, ⊤) := (isDomain_globalSections k).toNontrivial
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_globalSections k hℓ (affineLine k ↘ Spec (.of k))
  exact natCard_sheafH_zero_rootsOfUnity (affineLine k) hℓ0.ne'
    (isUnit_natCast_globalSections_of_over (affineLine k ↘ Spec (.of k)) hℓ) hζ

include hℓ0 hℓ in
/-- `H⁰(𝐆_m, μ_ℓ)` has `ℓ` elements. -/
theorem natCard_sheafH_zero_rootsOfUnity_punctured :
    Nat.card (Sheaf.H.{u + 1} (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (punctured k).toScheme ℓ) 0) =
      ℓ := by
  let : Algebra Γ(affineLine k, ⊤) Γ((punctured k).toScheme, ⊤) :=
    (punctured k).ι.appTop.hom.toAlgebra
  have : IsLocalization.Away (coordinate k) Γ((punctured k).toScheme, ⊤) :=
    Γ_restrict_isLocalization (affineLine k) (coordinate k)
  have hdom : IsDomain Γ((punctured k).toScheme, ⊤) :=
    IsLocalization.isDomain_of_le_nonZeroDivisors _
      (powers_le_nonZeroDivisors_of_noZeroDivisors (prime_coordinate k).ne_zero)
  have : Nontrivial Γ((punctured k).toScheme, ⊤) := hdom.toNontrivial
  obtain ⟨ζ, hζ⟩ := exists_isPrimitiveRoot_globalSections k hℓ
    ((punctured k).ι ≫ (affineLine k ↘ Spec (.of k)))
  exact natCard_sheafH_zero_rootsOfUnity (punctured k).toScheme hℓ0.ne'
    (isUnit_natCast_globalSections_of_over ((punctured k).ι ≫ (affineLine k ↘ Spec (.of k))) hℓ) hζ

include hℓ0 hℓ in
/-- **The unit `μ_ℓ ⟶ j_* j⁻¹ μ_ℓ` along `j : 𝐆_m ⟶ 𝐀¹` is an isomorphism.** -/
theorem isIso_rootsOfUnityUnit : IsIso (rootsOfUnityUnit k (ℓ := ℓ)) := by
  have hmono := mono_rootsOfUnityUnit k (ℓ := ℓ)
  set θ := rootsOfUnityUnit k (ℓ := ℓ)
  have hinj : Function.Injective (Sheaf.H.map.{u + 1} θ 0) :=
    fun a b h => Abelian.Ext.postcomp_mk₀_injective_of_mono _ θ h
  have hcard : Nat.card (Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, 0} (punctured k).ι).obj
      ((etaleRestriction.{u, 0} (punctured k).ι).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ))) 0) = ℓ := by
    rw [natCard_sheafH_zero_directImage, natCard_sheafH_congr (restrictionRootsOfUnityIso _ ℓ),
      natCard_sheafH_zero_rootsOfUnity_punctured k hℓ0 hℓ]
  have hfin : Finite (Sheaf.H.{u + 1} ((etaleAbelianDirectImage.{u, 0} (punctured k).ι).obj
      ((etaleRestriction.{u, 0} (punctured k).ι).obj
        (Stacks.Kummer.rootsOfUnitySheaf.{u, 0} (affineLine k) ℓ))) 0) :=
    Nat.finite_of_card_ne_zero (by rw [hcard]; exact hℓ0.ne')
  have hsurj : Function.Surjective (Sheaf.H.map.{u + 1} θ 0) :=
    (hinj.bijective_of_nat_card_le (by
      rw [hcard, natCard_sheafH_zero_rootsOfUnity_affineLine k hℓ0 hℓ])).2
  let S := ShortComplex.mk θ (cokernel.π θ) (cokernel.condition θ)
  have hS : S.ShortExact :=
    { exact := ShortComplex.exact_of_g_is_cokernel _ (cokernelIsCokernel θ) }
  have h1 := subsingleton_sheafH_one_rootsOfUnity_affineLine k hℓ0 hℓ
  have hQ : Subsingleton (Sheaf.H.{u + 1} (cokernel θ) 0) := by
    refine subsingleton_of_forall_eq 0 fun y => ?_
    obtain ⟨z, hz⟩ := Abelian.Ext.covariant_sequence_exact₃ _ hS y (rfl : 0 + 1 = 1)
      (Subsingleton.elim _ _)
    obtain ⟨x, rfl⟩ := hsurj z
    rw [← hz]
    show (x.comp (Abelian.Ext.mk₀ θ) (add_zero 0)).comp (Abelian.Ext.mk₀ (cokernel.π θ))
      (add_zero 0) = 0
    rw [Abelian.Ext.comp_assoc_of_third_deg_zero, Abelian.Ext.mk₀_comp_mk₀, cokernel.condition,
      Abelian.Ext.mk₀_zero, Abelian.Ext.comp_zero]
  have hres : IsZero ((etaleRestriction.{u, 0} (punctured k).ι).obj (cokernel θ)) := by
    have := isIso_restriction_rootsOfUnityUnit k (ℓ := ℓ)
    have : (etaleRestriction.{u, 0} (punctured k).ι).IsLeftAdjoint :=
      (etaleRestrictionAbelianDirectImageAdj.{u, 0} (punctured k).ι).isLeftAdjoint
    exact (isZero_cokernel_of_epi ((etaleRestriction.{u, 0} (punctured k).ι).map θ)).of_iso
      (PreservesCokernel.iso _ θ)
  let : MorphismProperty.ContainsIdentities (@Etale.{u}) := ⟨fun _ => inferInstance⟩
  have hT : IsTerminal (Scheme.Etale.mk (𝟙 (affineLine k))) :=
    MorphismProperty.Over.mkIdTerminal _ _
  have hΓ : IsZero ((Sheaf.Γ (affineLine k).smallEtaleTopology AddCommGrpCat.{u + 1}).obj
      (cokernel θ)) := by
    refine IsZero.of_iso ?_ ((Sheaf.ΓNatIsoSheafSections _ _ hT).app (cokernel θ))
    rw [AddCommGrpCat.isZero_iff_subsingleton]
    exact (Sheaf.H.equiv₀ (cokernel θ) hT).symm.toEquiv.subsingleton
  have hzero := isZero_of_isZero_restriction_of_isZero_sections k (cokernel θ) hres hΓ
  have : Epi θ := Preadditive.epi_of_isZero_cokernel' _ (cokernelIsCokernel θ) hzero
  exact isIso_of_mono_of_epi θ

end Stacks.EtaleCohomology.Purity

end
