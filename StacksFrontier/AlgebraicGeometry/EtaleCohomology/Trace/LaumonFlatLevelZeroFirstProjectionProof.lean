module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFirstProjectionFibreCharacter
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFlatLevelZeroFirstProjection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFirstProjectionFibreVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationFlatModelLevelZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.RepresentationBasePoint
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformDegreeZero
public import StacksFrontier.AlgebraicGeometry.Size.AlgebraicExtension
public import StacksFrontier.AlgebraicGeometry.Size.ArtinianLocal

/-!
# `R¹pr₁! K'₀ = 0` for the family sheaf of Laumon's argument, `ℓ ≠ char k'`

Let `K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t h(x))` be the family sheaf on `𝔸² = Spec k'[x][t]` of Laumon's
argument ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)), `h = xⁿ⁰ + c x`, `ψ' ≠ 1`, and
`K'₀` the bottom level of its flat model. This proves
`Stacks.EtaleCohomology.LaumonFamilyFirstProjectionVanishingInput'`: `R¹pr₁! K'₀ = 0` for
`ℓ ≠ char k'` (`Stacks.EtaleCohomology.laumonFamilyFirstProjectionVanishingInput'`), and hence the
primed (H2) of the chain, `Stacks.EtaleCohomology.LaumonFamilyNoPunctualSectionsInput'`
(`Stacks.EtaleCohomology.laumonFamilyNoPunctualSectionsInput'`).

The sheaf `K` is `ℱ_{ρ₀}` for the integral model `ρ₀ = P⁻¹ ρ P` of `ρ = Res_b(pr₁^*σ₁ ⊗ ψ'(-χ))`,
whose levels are flat; so `K'₀` is the lisse sheaf of `(ℤ/ℓ)^r` with `π₁` acting through
`ρ₀` modulo `ℓ` (`Stacks.EtaleCohomology.representationLAdicSheafFlatModelLevelZeroIso`), and by
restriction of scalars it suffices to show `R¹pr₁! = 0` with coefficients `ℤ/ℓ`. This is checked
on the geometric fibres `Spec Ω[t]` of `pr₁` over `x̄` (proper base change, Tag 0F7L): after a
change of base point, `π₁` of the fibre acts through `ρ₀`, on which `pr₁^*σ₁` becomes trivial
and the character becomes the Artin–Schreier character of `h(x̄) t`
(`Stacks.EtaleCohomology.etaleFundamentalGroupMap_laumonFamilyPr₁_fibre_eq_one`,
`Stacks.EtaleCohomology.torsorCover_character_laumonFamily_fibre`); so the rational matrices are
`N(χ)`, `N(c) = P⁻¹ Res_b(ψ'(-c)) P`, with `∑_c N(c) = 0` since `ψ' ≠ 1`, and `H¹_c` of the fibre
vanishes (`Stacks.EtaleCohomology.isZero_homology_one_derivedLowerShriek_levelModule_scaledLine`).

## Main results

* `Stacks.EtaleCohomology.isZero_homology_one_derivedLowerShriek_lisseEtaleSheaf_laumonFamilyPr₁`.
* `Stacks.EtaleCohomology.laumonFamilyFirstProjectionVanishingInput'`.
* `Stacks.EtaleCohomology.laumonFamilyNoPunctualSectionsInput'`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard`, and so do the statements here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.LAdicTower AlgebraicGeometry
  AlgebraicGeometry.SmallEtale Polynomial Stacks.ArtinSchreier Stacks.ConstantSheaf
  Stacks.GroupCohomology

universe u

attribute [local instance] discreteForget₂AddCommGrpCat
  Stacks.EtaleCohomology.moduleCat_hasLimitsOfSize

namespace Stacks.EtaleCohomology

/-- **The affine line over the residue field of a geometric point of a scheme of a big étale site
is in the site**: the residue field is algebraic over a residue field of the scheme, which is no
larger than the scheme. -/
theorem schemeSizeBelow_spec_polynomial_residueField_ofPoint (B : BigEtaleSite.{u})
    {S : Scheme.{u}} (hS : schemeSizeBelow B.cutoff S) (s : S) :
    schemeSizeBelow B.cutoff
      (Spec (.of (Polynomial (GeometricPoint.ofPoint S s).residueField))) :=
  (schemeSizeBelow_spec_iff B.aleph0_lt_cutoff _).2 (Polynomial.cardinalMk_le_max.trans_lt
    (max_lt ((Cardinal.mk_le_max_of_isAlgebraic (S.residueField s)
      (AlgebraicClosure (S.residueField s))).trans_lt
        (max_lt ((Scheme.mk_residueField_le_size S s).trans_lt hS) B.aleph0_lt_cutoff))
      B.aleph0_lt_cutoff))

/-- **`#k'` is invertible in `ℤ/ℓ` for `ℓ ≠ char k'`.** -/
theorem isUnit_card_zmod_pow_of_ringChar_ne (k' : Type u) [Field k'] [Fintype k'] {ℓ : ℕ}
    [Fact ℓ.Prime] (hℓ : ringChar k' ≠ ℓ) : IsUnit (Fintype.card k' : ZMod (ℓ ^ (0 + 1))) := by
  have : Fact (ℓ ^ (0 + 1)).Prime := ⟨by rw [zero_add, pow_one]; exact Fact.out⟩
  obtain ⟨n, hp, hn⟩ := FiniteField.card k' (ringChar k')
  refine isUnit_iff_ne_zero.2 fun h0 => hℓ ?_
  rw [ZMod.natCast_eq_zero_iff, zero_add, pow_one, hn] at h0
  exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : ℓ.Prime) hp).1
    ((Fact.out : ℓ.Prime).dvd_of_dvd_pow h0)).symm

/-! ### The fibrewise vanishing -/

section Fibrewise

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

variable (k' : Type u) [Field k'] [Fintype k'] (B : BigEtaleSite.{u})
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k')))) {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]

/-- **`R¹pr₁! ℱ_{ρ₀ mod ℓ} = 0`** on `𝔸² = Spec k'[x][t]`, `ℓ ∤ #k'`, for a continuous
`ρ₀ : π₁(𝔸², z̄) → GL_r(ℤ_ℓ)` whose rational matrices on the kernel of `pr₁_*` are `N(χ)`, `χ` the
character of the Artin–Schreier cover of `h(x) t` and `N : k' → M_r(ℚ_ℓ)` with `N(0) = 1` and
`∑_c N(c) = 0`: on the geometric fibre `Spec Ω[t]` over `x̄`, after a change of base point, `π₁`
acts through `N` of the Artin–Schreier character of `h(x̄) t`, and `H¹_c` of the fibre vanishes
(`Stacks.EtaleCohomology.isZero_homology_one_derivedLowerShriek_levelModule_scaledLine`); proper
base change (Tag 0F7L) concludes. -/
theorem isZero_homology_one_derivedLowerShriek_lisseEtaleSheaf_laumonFamilyPr₁
    (hℓ : IsUnit (Fintype.card k' : ZMod (ℓ ^ (0 + 1)))) (h : Polynomial k')
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (cover k' (Polynomial (Polynomial k')) (C h * Polynomial.X))) {r : ℕ}
    (ρ₀ : EtaleFundamentalGroup (Spec (.of (Polynomial (Polynomial k')))) z →* GL (Fin r) ℤ_[ℓ])
    (hρ₀ : Continuous ρ₀) (N : k' → Matrix (Fin r) (Fin r) ℚ_[ℓ]) (hN0 : N 0 = 1)
    (hN : ∑ c : k', N c = 0)
    (hρ₀N : ∀ δ, etaleFundamentalGroupMap (laumonFamilyPr₁ k') z δ = 1 →
      (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (ρ₀ δ).val =
        N (Multiplicative.toAdd ((torsorCover k' (Polynomial (Polynomial k'))
          (C h * Polynomial.X)).character z p₀ δ)))
    (jg₁ : CompactificationOf
      (Over.mk (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL)))) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ 1).obj
      ((derivedLowerShriek.{u, 0} (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL)) jg₁
        (ZMod (ℓ ^ (0 + 1)))).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj
          ((lisseEtaleSheaf B (specObject (Polynomial (Polynomial k')) B hS) z
            (ZMod (ℓ ^ (0 + 1)))).obj (levelModule.{u + 1, u + 1} ρ₀ hρ₀ (0 + 1)))))) := by
  have : NeZero (ℓ ^ (0 + 1)) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let X := specObject (Polynomial (Polynomial k')) B hS
  have : IsNoetherian X.1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  let G :=
    (lisseEtaleSheaf B X z (ZMod (ℓ ^ (0 + 1)))).obj (levelModule.{u + 1, u + 1} ρ₀ hρ₀ (0 + 1))
  let K :=
    (DerivedCategory.Plus.singleFunctor (EtaleModules.{u, 0} (ZMod (ℓ ^ (0 + 1))) X.1) 0).obj G
  have hK : Nat.card (ZMod (ℓ ^ (0 + 1))) • 𝟙 K = 0 := by
    rw [← CategoryTheory.Functor.map_id, ← Functor.map_nsmul, natCard_nsmul_id_etaleModules,
      Functor.map_zero]
  refine isZero_homology_derivedLowerShriek_of_isPullback_geometricFibres (ZMod (ℓ ^ (0 + 1))) _
    jg₁ K (Nat.card (ZMod (ℓ ^ (0 + 1)))) Nat.card_pos hK 1 fun y => ?_
  let s := GeometricPoint.ofPoint (Spec (.of (Polynomial k'))) y
  let φ : Polynomial k' →+* s.residueField := (Spec.preimage s.hom).hom
  have hs : Spec.map (CommRingCat.ofHom φ) = s.hom := by
    rw [CommRingCat.ofHom_hom, Spec.map_preimage]
  have sq := isPullback_laumonFamilyPr₁_fibre k' φ
  rw [hs] at sq
  refine ⟨_, _, _, sq, ?_⟩
  let : Algebra k' s.residueField := (φ.comp C).toAlgebra
  have hφ : ∀ a : k', φ (C a) = algebraMap k' s.residueField a := fun a => rfl
  have hP := schemeSizeBelow_spec_polynomial_residueField_ofPoint B hL y
  let P := specObject (Polynomial s.residueField) B hP
  let u := Spec.map (CommRingCat.ofHom (mapRingHom φ))
  let uB : P ⟶ X := ObjectProperty.homMk u
  let y' : GeometricPoint (Spec (.of (Polynomial s.residueField))) :=
    GeometricPoint.ofPoint _ (Classical.arbitrary _)
  obtain ⟨t⟩ := nonempty_finiteEtaleFiberFunctorIso (x := z) (x' := y'.map u)
  let eB := representationLAdicSheafBasePointIso B X t hρ₀
  let e₁ := (SmallEtale.sheafEquiv B X.1 X.property
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (0 + 1))))).functor.mapIso
    { hom := eB.hom.app 0
      inv := eB.inv.app 0
      hom_inv_id := congrArg (fun φ => LAdicSheaf.Hom.app φ 0) eB.hom_inv_id
      inv_hom_id := congrArg (fun φ => LAdicSheaf.Hom.app φ 0) eB.inv_hom_id }
  let ρt := ρ₀.comp (etaleFundamentalGroupBasePointHom t).toMonoidHom
  have hρt : Continuous ρt := hρ₀.comp (etaleFundamentalGroupBasePointHom t).continuous
  obtain ⟨e₂⟩ := nonempty_etaleModuleInverseImage_lisseEtaleSheaf_iso B uB y' (ZMod (ℓ ^ (0 + 1)))
    (levelModule.{u + 1, u + 1} ρt hρt (0 + 1))
  let τ := ρt.comp (etaleFundamentalGroupMap u y').toMonoidHom
  have hτ : Continuous τ := hρt.comp (etaleFundamentalGroupMap u y').continuous
  let e₃ : (finiteTypeContinuousModuleRes (ZMod (ℓ ^ (0 + 1)))
      (etaleFundamentalGroupMap uB.hom y')).obj (levelModule.{u + 1, u + 1} ρt hρt (0 + 1)) ≅
      levelModule.{u + 1, u + 1} τ hτ (0 + 1) :=
    finiteTypeContinuousModuleIsoOfLinearEquiv (ZMod (ℓ ^ (0 + 1))) (LinearEquiv.refl _ _)
      fun σ v => rfl
  let eK : (etaleModuleDerivedInverseImagePlus.{u, 0} (ZMod (ℓ ^ (0 + 1))) u).obj K ≅
      (DerivedCategory.Plus.singleFunctor _ 0).obj
        ((lisseEtaleSheaf B P y' (ZMod (ℓ ^ (0 + 1)))).obj
          (levelModule.{u + 1, u + 1} τ hτ (0 + 1))) :=
    (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
      (etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (0 + 1))) u) 0).app G ≪≫
      (DerivedCategory.Plus.singleFunctor _ 0).mapIso
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (0 + 1))) u).mapIso e₁ ≪≫ e₂ ≪≫
          (lisseEtaleSheaf B P y' (ZMod (ℓ ^ (0 + 1)))).mapIso e₃)
  have hg : mapRingHom φ (C h * Polynomial.X) = C (φ h) * Polynomial.X := by simp
  obtain ⟨q⟩ :=
    nonempty_finiteEtaleFiber_cover k' (C (φ h) * Polynomial.X : Polynomial s.residueField) y'
  refine (isZero_homology_one_derivedLowerShriek_levelModule_scaledLine k' B hP hℓ y' (φ h) q τ hτ
    N (fun γ => ?_) hN0 hN (jg₁.baseChange sq)).of_iso
      ((DerivedCategory.Plus.homologyFunctor _ 1).mapIso
        ((derivedLowerShriek.{u, 0} _ (jg₁.baseChange sq) (ZMod (ℓ ^ (0 + 1)))).mapIso eK))
  have h1 := etaleFundamentalGroupMap_laumonFamilyPr₁_fibre_eq_one k' φ y' t γ
  show (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (ρ₀ (etaleFundamentalGroupBasePointHom t
    (etaleFundamentalGroupMap u y' γ))).val = _
  rw [hρ₀N _ h1, torsorCover_character_laumonFamily_fibre φ hφ (C h * Polynomial.X)
    (C (φ h) * Polynomial.X) hg y' t p₀ q γ]

end Fibrewise

/-! ### The vanishing of `R¹pr₁! K'₀` -/

section Vanishing

attribute [local instance] HasDerivedCategory.standard

/-- **`R¹pr₁! K'₀ = 0` for `ℓ ≠ char k'`** ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)):
for the bottom level `K'₀` of the flat model of the family sheaf
`K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t h(x))` on `Spec k'[x][t]`. `K = ℱ_{ρ₀}` for the integral model
`ρ₀ = P⁻¹ ρ P` of `ρ = Res_b(pr₁^*σ₁ ⊗ ψ'(-χ))`, so `K'₀` is the lisse sheaf of `(ℤ/ℓ)^r` with
`π₁` acting through `ρ₀` modulo `ℓ`
(`Stacks.EtaleCohomology.representationLAdicSheafFlatModelLevelZeroIso`); `R¹pr₁!` commutes with
restriction of scalars to `ℤ_ℓ`, and on the kernel of `pr₁_*` the rational matrices of `ρ₀` are
`N(χ)`, `N(c) = P⁻¹ Res_b(ψ'(-c)) P`, with `∑_c N(c) = 0` because `ψ' ≠ 1`
(`Stacks.EtaleCohomology.isZero_homology_one_derivedLowerShriek_lisseEtaleSheaf_laumonFamilyPr₁`).
-/
public theorem laumonFamilyFirstProjectionVanishingInput' :
    LaumonFamilyFirstProjectionVanishingInput'.{u} := by
  intro B ℓ _ _ _ _ k' _ _ hℓ hS hL E _ _ _ d b ψ' hψ' n₀ c hh z p₀ m σ₁ hσ₁ jg₁
  have : IsNoetherian (specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  let X := specObject (Polynomial (Polynomial k')) B hS
  have := compactSpace_etaleFundamentalGroup X.1 z
  let ρ := restrictScalarsRep b (laumonFamilyRep k' ψ' n₀ c z p₀ σ₁)
  have hρ : Continuous ρ := continuous_restrictScalarsRep_laumonFamilyRep k' b ψ' n₀ c z p₀ σ₁ hσ₁
  let ρ₀ := integralModel ρ hρ
  have hρ₀ : Continuous ρ₀ := continuous_integralModel ρ hρ
  let P := (exists_conj_integral ρ hρ).choose
  let N : k' → Matrix (Fin (m * d)) (Fin (m * d)) ℚ_[ℓ] := fun a =>
    (P⁻¹ : GL (Fin (m * d)) ℚ_[ℓ]).val * restrictScalarsScalarAlgHom b m (ψ' (-a)) * P.val
  have hN0 : N 0 = 1 := by
    change
      (P⁻¹ : GL (Fin (m * d)) ℚ_[ℓ]).val * restrictScalarsScalarAlgHom b m (ψ' (-0)) * P.val = 1
    rw [neg_zero, AddChar.map_zero_eq_one, map_one, Matrix.mul_one, ← Units.val_mul, inv_mul_cancel,
      Units.val_one]
  have hN : ∑ a : k', N a = 0 := by
    show ∑ a : k',
      (P⁻¹ : GL (Fin (m * d)) ℚ_[ℓ]).val * restrictScalarsScalarAlgHom b m (ψ' (-a)) * P.val = 0
    rw [← Finset.sum_mul, ← Finset.mul_sum, ← map_sum,
      show ∑ a : k', ψ' (-a) = 0 from (Fintype.sum_equiv (Equiv.neg k') _ ψ' fun _ => rfl).trans
        (AddChar.sum_eq_zero_of_ne_one hψ'), map_zero, Matrix.mul_zero, Matrix.zero_mul]
  have hρ₀N : ∀ δ, etaleFundamentalGroupMap (laumonFamilyPr₁ k') z δ = 1 →
      (PadicInt.Coe.ringHom (p := ℓ)).mapMatrix (ρ₀ δ).val =
        N (Multiplicative.toAdd ((torsorCover k' (Polynomial (Polynomial k'))
          (laumonKernel k' n₀ c)).character z p₀ δ)) := by
    intro δ hδ
    have hσ : (σ₁.comp (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom) δ = 1 :=
      (congrArg σ₁ hδ).trans (map_one σ₁)
    refine (congrArg Units.val (map_integralModel ρ hρ δ)).trans ?_
    rw [Units.val_mul, Units.val_mul, restrictScalarsRep_val]
    show (P⁻¹ : GL (Fin (m * d)) ℚ_[ℓ]).val * restrictScalarsMatrix b
      ((characterTwist (σ₁.comp (etaleFundamentalGroupMap (laumonFamilyPr₁ k') z).toMonoidHom)
        (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial (Polynomial k'))
          (laumonKernel k' n₀ c) ψ' z p₀) δ).val) * P.val = _
    rw [characterTwist_val, hσ, Units.val_one, Matrix.smul_one_eq_diagonal, ← Matrix.scalar_apply,
      Stacks.ArtinSchreier.artinSchreierCharacter_apply]
    rfl
  have hG1 := isZero_homology_one_derivedLowerShriek_lisseEtaleSheaf_laumonFamilyPr₁ k' B hS hL
    (isUnit_card_zmod_pow_of_ringChar_ne k' hℓ) (Polynomial.X ^ n₀ + Polynomial.C c * Polynomial.X)
    z p₀ ρ₀ hρ₀ N hN0 hN hρ₀N jg₁
  obtain ⟨eC⟩ := nonempty_homology_derivedLowerShriek_restrictScalars_iso
    (PadicInt.toZModPow (p := ℓ) (0 + 1))
    (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL)) jg₁
    ((lisseEtaleSheaf B X z (ZMod (ℓ ^ (0 + 1)))).obj (levelModule.{u + 1, u + 1} ρ₀ hρ₀ (0 + 1))) 1
  have hres := Functor.map_isZero (etaleModuleRestrictScalars (PadicInt.toZModPow (p := ℓ) (0 + 1))
    (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1) hG1
  let e0 := representationLAdicSheafFlatModelLevelZeroIso B X z ρ₀ hρ₀
  exact (hres.of_iso eC).of_iso ((DerivedCategory.Plus.homologyFunctor _ 1).mapIso
    ((derivedLowerShriek.{u, 0} (B.inclusion.map (laumonFamilyFirstProjection k' B hS hL)) jg₁
      ℤ_[ℓ]).mapIso (((StacksDraft.DerivedSectionsComparison.singlePlusQIso
        (EtaleModules.{u, 0} ℤ_[ℓ] X.1)).app _) ≪≫
          (DerivedCategory.Plus.singleFunctor _ 0).mapIso e0)))

/-- **(H2) for `ℓ ≠ char k'`** ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the primed
no-punctual-sections input of Laumon's family, with no remaining input. -/
public theorem laumonFamilyNoPunctualSectionsInput' : LaumonFamilyNoPunctualSectionsInput'.{u} :=
  laumonFamilyNoPunctualSectionsInput'_of_firstProjection laumonFamilyFirstProjectionVanishingInput'

end Vanishing

end Stacks.EtaleCohomology

end
