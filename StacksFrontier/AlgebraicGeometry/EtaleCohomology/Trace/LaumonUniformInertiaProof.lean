module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonUniformInertia
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonUniformInertiaFinale
public import
  StacksFrontier.AlgebraicGeometry.FundamentalGroup.GaloisCategory.GaloisFixedPointsTransport
public import StacksFrontier.AlgebraicGeometry.FundamentalGroup.EtaleFundamental.InducedHomBasePoint
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.GenericFibre.GenericResidueFieldOfSpec
public import StacksFrontier.RingTheory.DiscreteValuationRing.PolynomialAtXInfinityMap

/-!
# The inertia at `∞` of the fibres of the Fourier family, uniformly in the constant field

This file proves `Stacks.EtaleCohomology.LaumonUniformInertiaInput`
(`Stacks.EtaleCohomology.laumonUniformInertiaInput`): for `σ` continuous on `U ≅ 𝔸¹_k` and an
additive character `ψ ≠ 1` of `k` there is one `N`, independent of the finite extension `k'` of
`k`, such that for `n > N` prime to `p` the inertia group at every place at infinity of `𝔸¹_{k'}`
fixes no nonzero vector of the fibre `σ' ⊗ L_ψ(a xⁿ + c x)` of the Fourier family or of its
contragredient, and has no coinvariants on them. This is the uniform bound on the inertia at `∞`
in the purity half of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main results

* `Stacks.EtaleCohomology.exists_mem_curvePointInertia_isUnit_restrictScalarsMatrix_sub_one`:
  one element `γ` of the inertia at `∞` with `Res_b(τ(γ)) - 1` invertible, uniformly in `k'`.
* `Stacks.EtaleCohomology.laumonUniformInertiaInput`.
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry Matrix Stacks.FundamentalGroup

universe u

namespace Stacks.EtaleCohomology

/-- **One inertia element at `∞` with `Res_b(τ(γ)) - 1` invertible, uniformly in the constant
field**: for `σ` continuous on `U ≅ 𝔸¹_k` and `ψ ≠ 1` there is `N` such that for every `n > N`
prime to `p` and every choice of `k'`, `x̄'`, `a ≠ 0`, `c`, `p₀`, `L`, `Ω`, `t`, `A` and `P` as in
`LaumonUniformInertiaInput`, with `A` a place at `∞`, some `γ` in the inertia group of `P` makes
`Res_b(τ(γ)) - 1` invertible, where `τ = (σ' ⊗ χ) ∘ φ_t` is the twist of the restriction `σ'` of
`σ` by the Artin–Schreier character `χ` of `a xⁿ + c x` for `ψ ∘ Tr_{k'/k}`. -/
theorem exists_mem_curvePointInertia_isUnit_restrictScalarsMatrix_sub_one :
    ∀ (ℓ : ℕ) [Fact ℓ.Prime] (k : Type u) [Field k] [Finite k] (U : Scheme.{u}) [ConnectedSpace U]
    (e : U ⟶ Spec (.of (Polynomial k))) [IsIso e] (p : ℕ) [Fact p.Prime] [CharP k p]
    (x : GeometricPoint U) (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E]
    {d : ℕ} (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ}
    (σ : EtaleFundamentalGroup U x →* GL (Fin m) E)
    (_ : Continuous (restrictScalarsRep b σ)) (ψ : AddChar k E), ψ ≠ 1 →
    ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
    ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k']
      [ConnectedSpace (Spec (.of (Polynomial k')))] [IrreducibleSpace (Spec (.of (Polynomial k')))]
      (x' : GeometricPoint (Spec (.of (Polynomial k'))))
      (hx' : x'.map (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫
        inv e) = x)
      (a c : k'), a ≠ 0 →
      ∀ (p₀ : (finiteEtaleFiberFunctor x').obj (Stacks.ArtinSchreier.cover k' (Polynomial k')
          (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X)))
        (L Ω : Type u) [Field L] [Field Ω]
        [Algebra ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k'))))) L]
        [IsSepClosure ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k'))))) L]
        [Algebra L Ω] [Algebra ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k'))))) Ω]
        [IsScalarTower ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k'))))) L Ω] [IsAlgClosed Ω]
        [Algebra.IsAlgebraic ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k'))))) Ω]
        (t : finiteEtaleFiberFunctor x' ≅ finiteEtaleFiberFunctor ((algebraicClosureGeometricPoint
          ((Spec (.of (Polynomial k'))).residueField (genericPoint (Spec (.of (Polynomial k')))))
          Ω).map ((Spec (.of (Polynomial k'))).fromSpecResidueField
            (genericPoint (Spec (.of (Polynomial k')))))))
        (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
        [Algebra A ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k')))))]
        [IsFractionRing A ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k')))))] [Algebra A L]
        [IsScalarTower A ((Spec (.of (Polynomial k'))).residueField
          (genericPoint (Spec (.of (Polynomial k'))))) L]
        (P : Ideal (integralClosure A L)) [P.IsMaximal],
        (∃ g : Γ(Spec (.of (Polynomial k')), ⊤),
          ((Spec (.of (Polynomial k'))).evaluation ⊤ (genericPoint (Spec (.of (Polynomial k'))))
            trivial).hom g ∉ Set.range (algebraMap A ((Spec (.of (Polynomial k'))).residueField
              (genericPoint (Spec (.of (Polynomial k'))))))) →
        ∃ γ ∈ curvePointInertia (Spec (.of (Polynomial k'))) L Ω A P,
          IsUnit (restrictScalarsMatrix b ((characterTwist
            (σ.comp (hx' ▸ (etaleFundamentalGroupMap (Spec.map (CommRingCat.ofHom
              (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) x').toMonoidHom))
            (Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k')
              (Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X)
              (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) x' p₀)
            (etaleFundamentalGroupBasePointHom t γ) : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) - 1)
 := by
  intro ℓ _ k _ _ U _ e _ p _ _ x E _ _ _ d b m σ hσ ψ hψ
  classical
  have := Fintype.ofFinite k
  obtain ⟨c₁, hc₁⟩ := AddChar.ne_one_iff.1 hψ
  let T : Matrix (Fin (m * d)) (Fin (m * d)) ℚ_[ℓ] :=
    restrictScalarsMatrix b (Matrix.scalar (Fin m) (ψ c₁))
  let O : Set (GL (Fin (m * d)) ℚ_[ℓ]) := {g | (T * (g : Matrix _ _ ℚ_[ℓ]) - 1).det ≠ 0}
  have hO : IsOpen O :=
    isOpen_ne_fun (((continuous_const.matrix_mul Units.continuous_val).sub continuous_const :
      Continuous fun g : GL (Fin (m * d)) ℚ_[ℓ] => T * (g : Matrix _ _ ℚ_[ℓ]) - 1).matrix_det)
      continuous_const
  have h1O : (1 : GL (Fin (m * d)) ℚ_[ℓ]) ∈ O := by
    show (T * ((1 : GL (Fin (m * d)) ℚ_[ℓ]) : Matrix _ _ ℚ_[ℓ]) - 1).det ≠ 0
    rw [Units.val_one, Matrix.mul_one]
    have hT : T - 1 = restrictScalarsMatrix b (Matrix.scalar (Fin m) (ψ c₁ - 1)) := by
      simp only [T, map_sub, map_one, restrictScalarsMatrix_sub, restrictScalarsMatrix_one]
    rw [hT]
    exact ((Matrix.isUnit_iff_isUnit_det _).1 ((((Ne.isUnit (sub_ne_zero.2 hc₁)).map
      (Matrix.scalar (Fin m))).map (restrictScalarsMonoidHom b m)))).ne_zero
  obtain ⟨H, ⟨Y, y, rfl⟩, hHO⟩ :=
    (EtaleFundamentalGroup.nhds_one_hasBasis_isOpenSubgroup U x).mem_iff.1
      ((hO.preimage hσ).mem_nhds (by rw [Set.mem_preimage, map_one]; exact h1O))
  have hkK : ∀ a : k, algebraMap k (FractionRing (Polynomial k)) a =
      algebraMap (Polynomial k) (FractionRing (Polynomial k)) (Polynomial.C a) := fun a =>
    IsScalarTower.algebraMap_apply k (Polynomial k) (FractionRing (Polynomial k)) a
  have := Polynomial.isDiscreteValuationRing_localizationAtX k
  have := Polynomial.isFractionRing_localizationAtX k
  let : Algebra (Polynomial.LocalizationAtX k) (SeparableClosure (FractionRing (Polynomial k))) :=
    ((algebraMap (FractionRing (Polynomial k))
      (SeparableClosure (FractionRing (Polynomial k)))).comp
      (algebraMap (Polynomial.LocalizationAtX k) (FractionRing (Polynomial k)))).toAlgebra
  have : IsScalarTower (Polynomial.LocalizationAtX k) (FractionRing (Polynomial k))
      (SeparableClosure (FractionRing (Polynomial k))) := IsScalarTower.of_algebraMap_eq' rfl
  let : Algebra k (SeparableClosure (FractionRing (Polynomial k))) :=
    ((algebraMap (FractionRing (Polynomial k))
      (SeparableClosure (FractionRing (Polynomial k)))).comp
      (algebraMap k (FractionRing (Polynomial k)))).toAlgebra
  have : IsScalarTower k (FractionRing (Polynomial k))
      (SeparableClosure (FractionRing (Polynomial k))) :=
    IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : Algebra.IsAlgebraic (FractionRing (Polynomial k))
      (AlgebraicClosure (SeparableClosure (FractionRing (Polynomial k)))) :=
    Algebra.IsAlgebraic.trans _ (SeparableClosure (FractionRing (Polynomial k))) _
  have : CharP (FractionRing (Polynomial k)) p :=
    charP_of_injective_algebraMap (algebraMap k (FractionRing (Polynomial k))).injective p
  have : Finite (IsLocalRing.ResidueField (Polynomial.LocalizationAtX k)) :=
    Nat.finite_of_card_ne_zero (by
      rw [Polynomial.natCard_residueField_localizationAtX]; exact Nat.card_pos.ne')
  let ψ₀ : Polynomial k →+* FractionRing (Polynomial k) :=
    Polynomial.eval₂RingHom ((algebraMap (Polynomial k) (FractionRing (Polynomial k))).comp
      Polynomial.C) (algebraMap (Polynomial k) (FractionRing (Polynomial k)) Polynomial.X)⁻¹
  let J₀ : Spec (.of (FractionRing (Polynomial k))) ⟶ U :=
    Spec.map (CommRingCat.ofHom ψ₀) ≫ inv e
  obtain ⟨E₀, hE₀, hfix₀⟩ := exists_finiteDimensional_forall_mem_fixingSubgroup_spec_comp_eq
    (FractionRing (Polynomial k)) (SeparableClosure (FractionRing (Polynomial k)))
    (AlgebraicClosure (SeparableClosure (FractionRing (Polynomial k)))) J₀ Y
  obtain ⟨P₀, hP₀⟩ := Ideal.exists_maximal (integralClosure (Polynomial.LocalizationAtX k)
    (SeparableClosure (FractionRing (Polynomial k))))
  obtain ⟨N, hN⟩ :=
    IsDiscreteValuationRing.exists_forall_exists_mem_inertia_sub_eq_of_constantExtension
      (Polynomial.LocalizationAtX k) (FractionRing (Polynomial k)) k
      (SeparableClosure (FractionRing (Polynomial k))) p
      (Polynomial.natCard_residueField_localizationAtX k).le
      (Polynomial.irreducible_algebraMap_X_localizationAtX k) P₀ E₀
  refine ⟨N, fun n hn hpn k' _ _ _ _ _ x' hx' a c ha p₀ L Ω _ _ _ _ _ _ _ _ _ t A _ _ _ _ _ _ _
    P _ hA => ?_⟩
  subst hx'
  set K' := (Spec (.of (Polynomial k'))).residueField (genericPoint (Spec (.of (Polynomial k'))))
    with hK'def
  let alg₁ : Algebra (Polynomial k') K' :=
    specResidueFieldAlgebra (.of (Polynomial k')) (genericPoint (Spec (.of (Polynomial k'))))
  have : IsFractionRing (Polynomial k') K' :=
    isFractionRing_specResidueField_genericPoint (.of (Polynomial k'))
  have hA' :
      ∃ g : Polynomial k', algebraMap (Polynomial k') K' g ∉ Set.range (algebraMap A K') := by
    obtain ⟨g, hg⟩ := hA
    refine ⟨(Scheme.ΓSpecIso (.of (Polynomial k'))).hom g, ?_⟩
    have h := congrArg (fun φ => φ.hom g) (Iso.hom_inv_id (Scheme.ΓSpecIso (.of (Polynomial k'))))
    simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_id, RingHom.id_apply] at h
    show ((Scheme.ΓSpecIso _).inv ≫ (Spec _).Γevaluation _).hom
      ((Scheme.ΓSpecIso (.of (Polynomial k'))).hom g) ∉ _
    rw [CommRingCat.hom_comp, RingHom.comp_apply, h]
    exact hg
  let alg₂ : Algebra (FractionRing (Polynomial k)) K' := (Polynomial.liftInvX k k' K').toAlgebra
  let alg₃ : Algebra k' K' := ((algebraMap (Polynomial k') K').comp Polynomial.C).toAlgebra
  let alg₄ : Algebra k K' := ((algebraMap k' K').comp (algebraMap k k')).toAlgebra
  have : IsScalarTower k k' K' := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  have : IsScalarTower k (FractionRing (Polynomial k)) K' :=
    IsScalarTower.of_algebraMap_eq (fun a => by
      show algebraMap (Polynomial k') K' (Polynomial.C (algebraMap k k' a)) =
        Polynomial.liftInvX k k' K' (algebraMap k _ a)
      rw [hkK, Polynomial.liftInvX_algebraMap, Polynomial.evalInvX_C])
  have hK'top := Polynomial.adjoin_range_eq_top_of_liftInvX k (K' := K') rfl rfl
  have hA₀ := Polynomial.liftInvX_algebraMap_mem_range k hA'
  have hπA := Polynomial.liftInvX_algebraMap_X_mem_maximalIdeal k hA'
  let alg₅ : Algebra (FractionRing (Polynomial k)) L :=
    ((algebraMap K' L).comp (algebraMap (FractionRing (Polynomial k)) K')).toAlgebra
  have : IsScalarTower (FractionRing (Polynomial k)) K' L := IsScalarTower.of_algebraMap_eq' rfl
  obtain ⟨ι, hι⟩ := hN k' K' hK'top A hA₀ hπA L P
  obtain ⟨c₀, hc₀⟩ := Algebra.trace_surjective k k' (-c₁)
  let g : Polynomial k' := Polynomial.C a * Polynomial.X ^ n + Polynomial.C c * Polynomial.X
  let q := t.hom.app (Stacks.ArtinSchreier.cover k' (Polynomial k') g) p₀
  obtain ⟨t₀, ht₀, hσt₀⟩ :=
    Stacks.ArtinSchreier.exists_algebraMap_eq_fiberRoot_galoisToFundamentalGroup k'
      (Polynomial k') g L Ω q
  have hx : algebraMap (FractionRing (Polynomial k)) K'
      (algebraMap (Polynomial.LocalizationAtX k) (FractionRing (Polynomial k))
        (algebraMap (Polynomial k) (Polynomial.LocalizationAtX k) Polynomial.X)) =
      (algebraMap (Polynomial k') K' Polynomial.X)⁻¹ := by
    rw [← IsScalarTower.algebraMap_apply (Polynomial k) (Polynomial.LocalizationAtX k)
      (FractionRing (Polynomial k))]
    exact (Polynomial.liftInvX_algebraMap k k' K' _).trans (Polynomial.evalInvX_X k k' K')
  have hroot : t₀ ^ Fintype.card k' - t₀ = algebraMap K' L (algebraMap k' K' a *
      (algebraMap (FractionRing (Polynomial k)) K'
        (algebraMap (Polynomial.LocalizationAtX k) (FractionRing (Polynomial k))
          (algebraMap (Polynomial k) (Polynomial.LocalizationAtX k) Polynomial.X)))⁻¹ ^ n +
      algebraMap k' K' c * (algebraMap (FractionRing (Polynomial k)) K'
        (algebraMap (Polynomial.LocalizationAtX k) (FractionRing (Polynomial k))
          (algebraMap (Polynomial k) (Polynomial.LocalizationAtX k) Polynomial.X)))⁻¹) := by
    rw [hx, inv_inv]
    apply (algebraMap L Ω).injective
    let r : Ω := Stacks.ArtinSchreier.fiberRoot q
    let γ₀ : Ω := (Stacks.ArtinSchreier.fiberRingHom q).hom
      (algebraMap (Polynomial k') (Stacks.ArtinSchreier.Ring k' g) g)
    have e1 : r ^ Fintype.card k' = r + γ₀ := Stacks.ArtinSchreier.fiberRoot_pow_card q
    have ht' : algebraMap L Ω t₀ = r := ht₀
    have e2 : γ₀ = algebraMap K' Ω (algebraMap (Polynomial k') K' g) :=
      Stacks.ArtinSchreier.fiberRingHom_algebraMap_genericPoint q g
    rw [map_sub, map_pow, ht', e1, e2, add_sub_cancel_left,
      ← IsScalarTower.algebraMap_apply K' L Ω]
    congr 1
    simp only [g, map_add, map_mul, map_pow]
    rfl
  obtain ⟨σL, hσI, hσE, hσt⟩ := hι n hn hpn a c ha t₀ hroot c₀
  let γ := galoisToFundamentalGroup (Spec (.of (Polynomial k'))) L Ω σL
  have hγ : γ ∈ curvePointInertia (Spec (.of (Polynomial k'))) L Ω A P :=
    Subgroup.mem_map_of_mem _ hσI
  have hchar :
      Multiplicative.toAdd ((Stacks.ArtinSchreier.torsorCover k' (Polynomial k') g).character
        x' p₀ (etaleFundamentalGroupBasePointHom t γ)) = c₀ := by
    have hce := IsEtaleFundamentalGroupHomInducedBy.character_eq (Φ := MonoidHom.id _)
      (Stacks.ArtinSchreier.torsorCover k' (Polynomial k') g)
      ⟨Functor.leftUnitor _, fun _ _ _ => rfl⟩ (isEtaleFundamentalGroupHomInducedBy_basePointHom t)
      q p₀ γ
    show Multiplicative.toAdd ((Stacks.ArtinSchreier.torsorCover k' (Polynomial k') g).character
      x' p₀ ((etaleFundamentalGroupBasePointHom t).toMonoidHom γ)) = c₀
    rw [hce]
    have h1 := hσt₀ σL
    rw [hσt, ← IsScalarTower.algebraMap_apply K' L Ω,
      IsScalarTower.algebraMap_apply k' (Polynomial k') (Stacks.ArtinSchreier.Ring k' g)] at h1
    have h2 : (Stacks.ArtinSchreier.fiberRingHom q).hom (algebraMap (Polynomial k')
        (Stacks.ArtinSchreier.Ring k' g) (algebraMap k' (Polynomial k')
          (Multiplicative.toAdd
            ((Stacks.ArtinSchreier.torsorCover k' (Polynomial k') g).character _ q γ)))) =
          algebraMap K' Ω (algebraMap k' K' (Multiplicative.toAdd
            ((Stacks.ArtinSchreier.torsorCover k' (Polynomial k') g).character _ q γ))) :=
      Stacks.ArtinSchreier.fiberRingHom_algebraMap_genericPoint q _
    rw [h2] at h1
    exact ((algebraMap k' K').injective ((algebraMap K' Ω).injective h1)).symm
  let f : Spec (.of (Polynomial k')) ⟶ U :=
    Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e
  let j' := (Spec (.of (Polynomial k'))).fromSpecResidueField
    (genericPoint (Spec (.of (Polynomial k'))))
  have hind := ((isEtaleFundamentalGroupHomInducedBy_map j'
    (algebraicClosureGeometricPoint K' Ω)).comp_baseChange
      (isEtaleFundamentalGroupHomInducedBy_basePointHom_id t)).comp_baseChange
        (isEtaleFundamentalGroupHomInducedBy_map f x')
  have hJ : (j' ≫ 𝟙 _) ≫ f =
      Spec.map (CommRingCat.ofHom (algebraMap (FractionRing (Polynomial k)) K')) ≫ J₀ := by
    rw [Category.comp_id]
    show (Spec (.of (Polynomial k'))).fromSpecResidueField _ ≫ _ = _
    rw [fromSpecResidueField_eq_specMap]
    simp only [f, J₀, ← Category.assoc, ← Spec.map_comp]
    congr 2
    ext1
    apply Polynomial.ringHom_ext
    · intro z
      show algebraMap (Polynomial k') K' (Polynomial.map (algebraMap k k') (Polynomial.C z)) =
        Polynomial.liftInvX k k' K' (ψ₀ (Polynomial.C z))
      rw [Polynomial.map_C]
      show _ = Polynomial.liftInvX k k' K' (Polynomial.eval₂ _ _ (Polynomial.C z))
      rw [Polynomial.eval₂_C, RingHom.comp_apply, Polynomial.liftInvX_algebraMap,
        Polynomial.evalInvX_C]
    · show algebraMap (Polynomial k') K' (Polynomial.map (algebraMap k k') Polynomial.X) =
        Polynomial.liftInvX k k' K' (Polynomial.eval₂ _ _ Polynomial.X)
      rw [Polynomial.map_X, Polynomial.eval₂_X, map_inv₀, Polynomial.liftInvX_algebraMap,
        Polynomial.evalInvX_X, inv_inv]
  have hfixL : ∀ g' : Spec (.of L) ⟶ Y.left,
      g' ≫ Y.hom = Spec.map (CommRingCat.ofHom (algebraMap K' L)) ≫ ((j' ≫ 𝟙 _) ≫ f) →
        Spec.map (CommRingCat.ofHom σL.toAlgHom.toRingHom) ≫ g' = g' := by
    intro g' hg'
    let σ₀ : Gal(SeparableClosure (FractionRing (Polynomial k)) / FractionRing (Polynomial k)) :=
      (ι.symm.trans (σL.restrictScalars (FractionRing (Polynomial k)))).trans ι
    refine spec_comp_eq_of_algEquiv ι J₀ Y σL σ₀ (fun z => ?_) (hfix₀ σ₀ ?_) g'
      (hg'.trans (by rw [hJ]))
    · show ι (σL (ι.symm (ι z))) = ι (σL z)
      rw [AlgEquiv.symm_apply_apply]
    · rw [IntermediateField.mem_fixingSubgroup_iff]
      intro z hz
      show ι (σL (ι.symm z)) = z
      rw [hσE z hz, AlgEquiv.apply_symm_apply]
  have hstab := forall_apply_eq_of_forall_spec_comp_eq K' L Ω _ hind Y σL hfixL y
  have hdet := hHO (show (etaleFundamentalGroupMap f x') (etaleFundamentalGroupBasePointHom t γ) ∈
    MulAction.stabilizer _ y from MulAction.mem_stabilizer_iff.2 hstab)
  let χ := Stacks.ArtinSchreier.artinSchreierCharacter k' (Polynomial k') g
    (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) x' p₀
  have hχ : (χ (etaleFundamentalGroupBasePointHom t γ) : E) = ψ c₁ := by
    rw [Stacks.ArtinSchreier.artinSchreierCharacter_apply, hchar, AddChar.compAddMonoidHom_apply]
    show ψ (Algebra.trace k k' (-c₀)) = ψ c₁
    rw [map_neg, hc₀, neg_neg]
  have hunit : IsUnit (restrictScalarsMatrix b ((characterTwist
      (σ.comp (etaleFundamentalGroupMap f x').toMonoidHom) χ
        (etaleFundamentalGroupBasePointHom t γ) : GL (Fin m) E) : Matrix (Fin m) (Fin m) E) -
          1) := by
    rw [characterTwist_val, hχ, Matrix.smul_eq_diagonal_mul, restrictScalarsMatrix_mul]
    exact (Matrix.isUnit_iff_isUnit_det _).2 (Ne.isUnit hdet)
  exact ⟨γ, hγ, hunit⟩

/-- **The uniform inertia input holds**: `Stacks.EtaleCohomology.LaumonUniformInertiaInput`. -/
theorem laumonUniformInertiaInput : LaumonUniformInertiaInput.{u} := by
  intro ℓ _ k _ _ U _ e _ p _ _ x E _ _ _ d b m σ hσ ψ hψ
  obtain ⟨N, hN⟩ := exists_mem_curvePointInertia_isUnit_restrictScalarsMatrix_sub_one ℓ k U e p x
    E b σ hσ ψ hψ
  refine ⟨N, fun n hn hpn k' _ _ _ _ _ x' hx' a c ha p₀ L Ω _ _ _ _ _ _ _ _ _ t A _ _ _ _ _ _ _
    P _ hA => ?_⟩
  obtain ⟨γ, hγ, hunit⟩ := hN n hn hpn k' x' hx' a c ha p₀ L Ω t A P hA
  have hmain := invariants_eq_bot_and_subsingleton_coinvariants_of_isUnit
    ((restrictScalarsRep b (characterTwist _ _)).comp
      (etaleFundamentalGroupBasePointHom t).toMonoidHom)
    (curvePointInertia (Spec (.of (Polynomial k'))) L Ω A P) ⟨γ, hγ⟩ hunit
  have hdual := invariants_eq_bot_and_subsingleton_coinvariants_of_isUnit
    ((restrictScalarsRep b (contragredient (characterTwist _ _))).comp
        (etaleFundamentalGroupBasePointHom t).toMonoidHom)
    (curvePointInertia (Spec (.of (Polynomial k'))) L Ω A P) ⟨γ, hγ⟩
    (isUnit_restrictScalarsMatrix_contragredient_sub_one b _ _ hunit)
  exact ⟨hmain.1, hmain.2, hdual.1, hdual.2⟩

end Stacks.EtaleCohomology

end
