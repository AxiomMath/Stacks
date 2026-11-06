module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CurvePointInertiaStalk

/-!
# The stalk at a missing point of a curve lies in the inertia invariants

`Stacks.EtaleCohomology.CurvePointInertiaStalkInput` embeds the stalk at `ȳ` of `j_*` of the
levels of `ℱ_{ρ₀}` into `(ℤ/ℓⁿ⁺¹)^r` and says that the reductions of the inertia invariants lie
in the image. `Stacks.EtaleCohomology.CurvePointInertiaStalkRangeInput` keeps the properties of
these embeddings (injectivity, semilinearity, compatibility with the transitions, the intertwiners
and the Frobenius) and records the other inclusion: every vector of the image is fixed by
`ρ₀ mod ℓⁿ⁺¹` of the inertia `curvePointInertia`. Indeed a section over `Spec K^{sh}` is fixed by
the automorphisms of `t̄` over `K^{sh}`
(`Stacks.EtaleCohomology.mem_range_padicLevelDirectImageStalkHom_iff`), and every element `g` of
the inertia group at `P` extends to an automorphism `G̃` of `Ω` fixing `K^{sh}`, the inertia fixed
field (`AlgEquiv.liftNormal`), whose image in `π₁(V, η̄)` is that of `g`. This is the form in which
the specialization map of Laumon's degeneration lands in the inertia invariants
(`Stacks.EtaleCohomology.CurveSpecializationInput`,
[Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

The construction of the maps `εₙ` is that of `Stacks.EtaleCohomology.curvePointInertiaStalkInput`.

The standard model `HasDerivedCategory.standard` is used as in
`Stacks.EtaleCohomology.CurvePointInertiaStalkInput`.

## Main definitions

* `Stacks.EtaleCohomology.CurvePointInertiaStalkRangeInput`

## Main results

* `Stacks.EtaleCohomology.curvePointInertiaStalkRangeInput`
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open AlgebraicGeometry.Scheme IsLocalRing
open scoped Pointwise Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard moduleCat_hasLimitsOfSize
  GeometricPoint.residueFieldAlgebra

/-- **The stalk at a missing point of `j_*` of the levels of `ℱ_{ρ₀}` lies in the inertia
invariants**: in the setting of `Stacks.EtaleCohomology.CurvePointInertiaStalkInput` there are
injective additive maps `εₙ : (j_* ℱₙ)_ȳ → (ℤ/ℓⁿ⁺¹)^r`, `ℤ_ℓ`-semilinear, compatible with the
transition maps, with the morphisms induced by the intertwiners of `ρ₀` and with the geometric
Frobenius `ρ₀(φ Fr⁻¹)`, whose images are fixed by `ρ₀ mod ℓⁿ⁺¹` of the inertia
`curvePointInertia`. -/
public def CurvePointInertiaStalkRangeInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (V : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B V.1 V.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian V.1] [Fact ℓ.Prime] [ConnectedSpace V.1] [IrreducibleSpace V.1] [IsAffine V.1]
    (k : Type u) [Field k] [Fintype k] (f : V.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (_j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_hcard : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    -- the curve `W ⊇ V` and the missing point `y`
    (W : B.Scheme) (fW : W.1 ⟶ Spec (.of k)) [LocallyOfFiniteType fW] [QuasiCompact fW]
    [IsSeparated fW] [SmoothOfRelativeDimension 1 fW]
    (eW : W.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion eW]
    (_ : eW ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = fW)
    (jW : V.1 ⟶ W.1) [IsOpenImmersion jW]
    (_ : jW ≫ fW = f) (y : W.1) (_ : IsClosed ({y} : Set W.1)) (_ : y ∉ Set.range jW.base)
    (hy : jW.base (genericPoint V.1) ⤳ y)
    -- the local field at `y`
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (V.1.residueField (genericPoint V.1)) L]
    [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
    [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
    [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω]
    (A : Type u) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A]
    [Algebra A (V.1.residueField (genericPoint V.1))]
    [IsFractionRing A (V.1.residueField (genericPoint V.1))] [Algebra A L]
    [IsScalarTower A (V.1.residueField (genericPoint V.1)) L]
    [Finite (IsLocalRing.ResidueField A)]
    (eA : A ≃+* W.1.presheaf.stalk y)
    (_ : ∀ a : A, algebraMap A (V.1.residueField (genericPoint V.1)) a =
      (curveLocalRingToFunctionField jW hy).hom (eA a))
    (P : Ideal (integralClosure A L)) [P.IsMaximal]
    (Fr : Gal(L / V.1.residueField (genericPoint V.1)))
    (_hFrD :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      Fr ∈ MulAction.stabilizer Gal(L / V.1.residueField (genericPoint V.1)) P)
    (_ :
      letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
        (integralClosure A L)
      ∀ b : integralClosure A L, Fr • b - b ^ Nat.card (IsLocalRing.ResidueField A) ∈ P)
    (r : ℕ) (ρ₀ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀) [Finite (W.1.residueField y)],
    letI := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
      (integralClosure A L)
    let x : GeometricPoint V.1 := (algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1))
    let ℱ : LAdicSheaf.{u, u + 1} B V ℓ := representationLAdicSheaf B V x
      (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V x) ρ₀ hρ₀
    let stalk : Sheaf W.1.smallEtaleTopology (ModuleCat.{u + 1} ℤ_[ℓ]) ⥤ ModuleCat.{u + 1} ℤ_[ℓ] :=
      (Scheme.pointSmallEtale (Stacks.Frobenius.geometricPointAt W.1 y).hom).sheafFiber
    let D : Sheaf (SmallEtale.topology B V.1 V.2) (ModuleCat.{u + 1} ℤ_[ℓ]) ⥤
        Sheaf W.1.smallEtaleTopology (ModuleCat.{u + 1} ℤ_[ℓ]) :=
      (SmallEtale.sheafEquiv B V.1 V.2 (ModuleCat.{u + 1} ℤ_[ℓ])).functor ⋙
        etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jW
    ∃ ε : ∀ n : ℕ, (stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))) →+
        (Fin r → ZMod (ℓ ^ (n + 1))),
      (∀ n, Function.Injective (ε n)) ∧
      (∀ n (c : ℤ_[ℓ]) (w : stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))),
        ε n (c • w) = PadicInt.toZModPow (n + 1) c • ε n w) ∧
      (∀ n (w : stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ (n + 1)))),
        ε n ((stalk.map (D.map (LAdicSheaf.padicTransition B V ℓ ℱ n))).hom w) = fun i =>
          ZMod.castHom (pow_dvd_pow ℓ (Nat.le_succ (n + 1))) (ZMod (ℓ ^ (n + 1)))
            (ε (n + 1) w i)) ∧
      (∀ (M : Matrix (Fin r) (Fin r) ℤ_[ℓ]) (hM : ∀ g, M * (ρ₀ g).val = (ρ₀ g).val * M) n
        (w : stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))),
        ε n ((stalk.map (D.map (LAdicSheaf.padicLevelMap
            (representationLAdicSheafMap B V x
              (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V x) hρ₀ hρ₀ M hM)
              n))).hom w) =
          (M.map (PadicInt.toZModPow (n + 1))) *ᵥ ε n w) ∧
      (∀ n (w : stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))),
        ε n ((Stacks.Frobenius.frobeniusStalk (ModuleCat.{u + 1} ℤ_[ℓ]) W.1 y
            (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))).hom w) =
          ((ρ₀ ((galoisToFundamentalGroup V.1 L Ω).toMonoidHom Fr⁻¹)).val.map
            (PadicInt.toZModPow (n + 1))) *ᵥ ε n w) ∧
      ∀ n (w : stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))),
        ∀ σ ∈ Stacks.FundamentalGroup.curvePointInertia V.1 L Ω A P,
          ((ρ₀ σ).val.map (PadicInt.toZModPow (n + 1))) *ᵥ ε n w = ε n w

/-- On a `ℤ_ℓ`-module killed by `ℓⁿ⁺¹`, the action of `c` is that of `(c mod ℓⁿ⁺¹).val`. -/
private theorem smul_eq_toZModPow_val_smul_of_pow_smul_eq_zero {ℓ : ℕ} [Fact ℓ.Prime]
    {M : Type*} [AddCommGroup M] [Module ℤ_[ℓ] M] {n : ℕ} {w : M} (hw : (ℓ ^ (n + 1)) • w = 0)
    (c : ℤ_[ℓ]) :
    c • w = (PadicInt.toZModPow (n + 1) c).val • w := by
  have hker : c - ((PadicInt.toZModPow (n + 1) c).val : ℤ_[ℓ]) ∈
      Ideal.span {(ℓ : ℤ_[ℓ]) ^ (n + 1)} := by
    rw [← PadicInt.ker_toZModPow, RingHom.mem_ker, map_sub, map_natCast, ZMod.natCast_zmod_val,
      sub_self]
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.mp hker
  have hc : c = ((PadicInt.toZModPow (n + 1) c).val : ℤ_[ℓ]) + d * (ℓ : ℤ_[ℓ]) ^ (n + 1) := by
    rw [hd]
    ring
  have hℓw : ((ℓ : ℤ_[ℓ]) ^ (n + 1)) • w = 0 := by
    rwa [← Nat.cast_pow, Nat.cast_smul_eq_nsmul]
  calc c • w = (((PadicInt.toZModPow (n + 1) c).val : ℤ_[ℓ]) + d * (ℓ : ℤ_[ℓ]) ^ (n + 1)) • w := by
        rw [← hc]
    _ = ((PadicInt.toZModPow (n + 1) c).val : ℤ_[ℓ]) • w := by
        rw [add_smul, mul_smul, hℓw, smul_zero, add_zero]
    _ = (PadicInt.toZModPow (n + 1) c).val • w := Nat.cast_smul_eq_nsmul ℤ_[ℓ] _ w

/-- An endomorphism of the source of `t̄` over `t̄` is also one over its image `f(t̄)`. -/
private theorem comp_map_hom_of_comp_hom {S T : Scheme.{u}} (t : GeometricPoint S) (f : S ⟶ T)
    {α : t.source ⟶ t.source} (h : α ≫ t.hom = t.hom) :
    α ≫ (t.map f).hom = (t.map f).hom := by
  show α ≫ t.hom ≫ f = t.hom ≫ f
  rw [← Category.assoc, h]

/-- A `κ(η)`-automorphism of `Ω` fixes the geometric point `Spec Ω → Spec κ(η) → X` at `η`. -/
private theorem specMap_algEquiv_comp_geometricPoint_hom {X : Scheme.{u}} (η : X) (Ω : Type u)
    [Field Ω] [Algebra (X.residueField η) Ω] [IsAlgClosed Ω] (G : Ω ≃ₐ[X.residueField η] Ω) :
    Spec.map (CommRingCat.ofHom (G.toRingEquiv : Ω →+* Ω)) ≫
        ((algebraicClosureGeometricPoint (X.residueField η) Ω).map
          (X.fromSpecResidueField η)).hom =
      ((algebraicClosureGeometricPoint (X.residueField η) Ω).map
        (X.fromSpecResidueField η)).hom := by
  show Spec.map (CommRingCat.ofHom (G.toRingEquiv : Ω →+* Ω)) ≫
    Spec.map (CommRingCat.ofHom (algebraMap (X.residueField η) Ω)) ≫ X.fromSpecResidueField η = _
  rw [← Category.assoc, ← Spec.map_comp]
  congr 2
  ext z
  exact G.commutes z

/-- A ring automorphism `φ` of `Ω` fixing the image of `ι : R → Ω` satisfies
`Spec φ ≫ Spec ι = Spec ι`. -/
private theorem specMap_ringEquiv_comp_specMap_of_comp {R Ω : Type u} [CommRing R] [CommRing Ω]
    (ι : R →+* Ω) (φ : Ω ≃+* Ω) (h : ∀ k, φ (ι k) = ι k) :
    Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω)) ≫ Spec.map (CommRingCat.ofHom ι) =
      Spec.map (CommRingCat.ofHom ι) := by
  rw [← Spec.map_comp]
  congr 1
  ext k
  exact h k

/-- **`Stacks.EtaleCohomology.CurvePointInertiaStalkRangeInput` holds**: the maps `εₙ` of
`Stacks.EtaleCohomology.curvePointInertiaStalkInput`, whose images consist of sections over
`Spec K^{sh}`, hence are fixed by the inertia. -/
theorem curvePointInertiaStalkRangeInput : CurvePointInertiaStalkRangeInput.{u} := by
  intro B V ℓ i1 i2 i3 i4 i5 i6 i7 i8 k i9 i10 f i11 i12 i13 i14 j kbar i15 i16 i17 i18 p n i19
    i20 hcard hℓp W fW i21 i22 i23 i24 eW i25 heW jW i26 hjW y hyc hyV hy L Ω i27 i28 i29 i30 i31
    i32 i33 i34 i35 A i36 i37 i38 i39 i40 i41 i42 i43 eA hA P i44 Fr hFrD hFr r ρ₀ hρ₀ i45
  intro x ℱ stalk D
  -- the geometric point at `y`, and the local ring there
  let s : GeometricPoint W.1 := Stacks.Frobenius.geometricPointAt W.1 y
  have hcy : s.hom (closedPoint s.residueField) = y :=
    (congrArg (fun z => s.hom z) (Subsingleton.elim (closedPoint s.residueField) _)).trans
      (Stacks.Frobenius.geometricPointAt_liesOver W.1 y)
  let eAc : A ≃+* W.1.presheaf.stalk (s.hom (closedPoint s.residueField)) :=
    eA.trans (W.1.presheaf.stalkCongr (Inseparable.of_eq hcy.symm)).commRingCatIsoToRingEquiv
  have : IsDomain (W.1.presheaf.stalk (s.hom (closedPoint s.residueField))) :=
    Function.Injective.isDomain (eAc.symm : _ →+* A) eAc.symm.injective
  have : IsDiscreteValuationRing (W.1.presheaf.stalk (s.hom (closedPoint s.residueField))) :=
    IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing eAc
  have : Nonempty W.1 := ⟨y⟩
  have : IrreducibleSpace W.1 := irreducibleSpace_of_isOpenImmersion_affineLine eW
  have hcV : s.hom (closedPoint s.residueField) ∉ Set.range jW.base := by rwa [hcy]
  -- the strict henselization `H = 𝒪^{sh}_{W,ȳ}` and `V ×_W Spec H = Spec K^{sh}`
  have : IsNoetherianRing (W.1.presheaf.stalk (s.hom (closedPoint s.residueField))) :=
    PrincipalIdealRing.isNoetherianRing
  have : QuasiCompact jW := quasiCompact_of_noetherianSpace_source jW
  obtain ⟨hHdom, hHdvr⟩ := @isDomain_and_isDiscreteValuationRing_etaleLocalRing B W.1 W.2 s
    inferInstance inferInstance inferInstance
  have : Nonempty V.1 := ⟨genericPoint V.1⟩
  obtain ⟨ϖ, hϖ, e, he, -⟩ := exists_directImageStalkIso_localizationAway B W.1 W.2 s jW hcV
    ((sheafCompose _ (forget (ModuleCat.{u + 1} ℤ_[ℓ]))).obj
      (padicLevelMathlib B V x ρ₀ hρ₀ 0))
  have hfr : IsFractionRing (etaleLocalRing B W.1 W.2 s) (Localization.Away ϖ) :=
    isFractionRing_localizationAway_of_irreducible (etaleLocalRing B W.1 W.2 s) hϖ
  let : Field (Localization.Away ϖ) := IsFractionRing.toField (etaleLocalRing B W.1 W.2 s)
  have hKc : B.Contains (Spec (.of (Localization.Away ϖ))) :=
    (Scheme.size_congr e).symm.trans_lt (Scheme.size_pullback_lt jW
      (strictHenselizationToBase B W.1 W.2 s) V.2 (contains_strictHenselization B W.1 W.2 s))
  let g : B.obj (Spec (.of (Localization.Away ϖ))) hKc ⟶ V :=
    ObjectProperty.homMk (e.inv ≫ pullback.fst jW (strictHenselizationToBase B W.1 W.2 s))
  have hg : B.inclusion.map g = e.inv ≫ pullback.fst jW (strictHenselizationToBase B W.1 W.2 s) :=
    rfl
  -- the étale local ring as a strict henselization of `A`
  let : Algebra (W.1.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (etaleLocalRing B W.1 W.2 s) := etaleLocalRingAlgebra B W.1 W.2 s
  have : IsLocalHom (algebraMap (W.1.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (etaleLocalRing B W.1 W.2 s)) := isLocalHom_algebraMap_etaleLocalRing B W.1 W.2 s
  let : Algebra A (etaleLocalRing B W.1 W.2 s) :=
    ((algebraMap (W.1.presheaf.stalk (s.hom (closedPoint s.residueField)))
      (etaleLocalRing B W.1 W.2 s)).comp eAc.toRingHom).toAlgebra
  have halgH : ∀ a : A, algebraMap A (etaleLocalRing B W.1 W.2 s) a =
      algebraMap (W.1.presheaf.stalk (s.hom (closedPoint s.residueField)))
        (etaleLocalRing B W.1 W.2 s) (eAc a) := fun _ => rfl
  have : IsLocalHom (algebraMap A (etaleLocalRing B W.1 W.2 s)) := ⟨fun a ha => by
    rw [halgH] at ha
    exact (isUnit_map_iff eAc a).mp (isUnit_of_map_unit _ _ ha)⟩
  have hInd : StacksDraft.IndEtale A (etaleLocalRing B W.1 W.2 s) :=
    StacksDraft.indEtale_of_equiv eAc.symm (RingEquiv.refl (etaleLocalRing B W.1 W.2 s))
      (fun a => by
        rw [halgH, RingEquiv.apply_symm_apply]
        rfl)
      (indEtale_etaleLocalRing B W.1 W.2 s)
  have : IsSepClosure (ResidueField A) (ResidueField (etaleLocalRing B W.1 W.2 s)) := by
    have hsc := isSepClosure_residueField_etaleLocalRing B W.1 W.2 s
    have he1 : (algebraMap (ResidueField A) (ResidueField (etaleLocalRing B W.1 W.2 s))).comp
        ((ResidueField.mapEquiv eAc).symm : ResidueField (W.1.presheaf.stalk
          (s.hom (closedPoint s.residueField))) →+* ResidueField A) =
        ((RingEquiv.refl (ResidueField (etaleLocalRing B W.1 W.2 s))) :
          ResidueField (etaleLocalRing B W.1 W.2 s) →+* _).comp
          (algebraMap (ResidueField (W.1.presheaf.stalk (s.hom (closedPoint s.residueField))))
            (ResidueField (etaleLocalRing B W.1 W.2 s))) := by
      refine RingHom.ext fun z => ?_
      obtain ⟨a, rfl⟩ := residue_surjective z
      have h1 : (ResidueField.mapEquiv eAc).symm (residue _ a) = residue A (eAc.symm a) :=
        ResidueField.map_residue _ _
      simp only [RingHom.comp_apply, RingHom.coe_coe, h1, ResidueField.algebraMap_residue,
        RingEquiv.refl_apply, halgH, RingEquiv.apply_symm_apply]
    exact ⟨hsc.sep_closed, @Algebra.IsSeparable.of_equiv_equiv _ _ _ _ _ _ _ _ _ _
      (ResidueField.mapEquiv eAc).symm (RingEquiv.refl _) he1 hsc.separable⟩
  -- the place `P` and the inertia field
  have : IsSepClosed L := IsSepClosure.sep_closed (V.1.residueField (genericPoint V.1))
  have hGal : IsGalois (V.1.residueField (genericPoint V.1)) L := IsSepClosure.isGalois
  have hNor : Normal (V.1.residueField (genericPoint V.1)) L := hGal.to_normal
  have : IsAlgClosure (V.1.residueField (genericPoint V.1)) Ω := ⟨inferInstance, inferInstance⟩
  have : Normal (V.1.residueField (genericPoint V.1)) Ω := IsAlgClosure.normal _ _
  have : P.LiesOver (maximalIdeal A) :=
    ⟨(IsLocalRing.eq_maximalIdeal (Ideal.IsMaximal.under A P)).symm⟩
  let Φ : (etaleLocalRing B W.1 W.2 s) ≃ₐ[A]
      IsIntegralClosure.inertiaInvariants A (V.1.residueField (genericPoint V.1)) L P :=
    Classical.choice (IsIntegralClosure.nonempty_algEquiv_inertiaInvariants_of_indEtale A
      (V.1.residueField (genericPoint V.1)) L P (etaleLocalRing B W.1 W.2 s) hInd)
  obtain ⟨ι, hιH, hιrange⟩ :=
    IsIntegralClosure.exists_ringHom_fractionRing_range_eq_inertiaFixedField A
      (V.1.residueField (genericPoint V.1)) L P (etaleLocalRing B W.1 W.2 s) Φ
      (Localization.Away ϖ)
  -- the embedding `ι' : K^{sh} → L → Ω` and the geometric point `t̄`
  let ι' : Localization.Away ϖ →+* Ω := (algebraMap L Ω).comp ι
  have hΦA : ∀ a : A, ((Φ (algebraMap A (etaleLocalRing B W.1 W.2 s) a) :
      IsIntegralClosure.localizedSubring P) : L) = algebraMap A L a := fun a => by
    rw [Φ.commutes]
    exact IsIntegralClosure.coe_algebraMap_inertiaInvariants A
      (V.1.residueField (genericPoint V.1)) L P a
  have hι'A : ∀ a : A, ι' (algebraMap (etaleLocalRing B W.1 W.2 s) (Localization.Away ϖ)
      (algebraMap A (etaleLocalRing B W.1 W.2 s) a)) =
      algebraMap (V.1.residueField (genericPoint V.1)) Ω
        (algebraMap A (V.1.residueField (genericPoint V.1)) a) := fun a => by
    simp only [ι', RingHom.comp_apply, hιH, hΦA]
    rw [IsScalarTower.algebraMap_apply A (V.1.residueField (genericPoint V.1)) L,
      ← IsScalarTower.algebraMap_apply (V.1.residueField (genericPoint V.1)) L Ω]
  let gA : A →+* Localization.Away ϖ := (algebraMap (etaleLocalRing B W.1 W.2 s)
    (Localization.Away ϖ)).comp (algebraMap A (etaleLocalRing B W.1 W.2 s))
  have hgA : Function.Injective gA := by
    intro a b hab
    have h := congrArg ι' hab
    simp only [gA, RingHom.comp_apply, hι'A] at h
    exact IsFractionRing.injective A (V.1.residueField (genericPoint V.1))
      ((algebraMap (V.1.residueField (genericPoint V.1)) Ω).injective h)
  let γ : V.1.residueField (genericPoint V.1) →+* Localization.Away ϖ :=
    IsFractionRing.lift (A := A) hgA
  have hγ : ι'.comp γ = algebraMap (V.1.residueField (genericPoint V.1)) Ω := by
    refine IsLocalization.ringHom_ext (nonZeroDivisors A) (RingHom.ext fun a => ?_)
    simp only [RingHom.comp_apply, γ, IsFractionRing.lift_algebraMap, gA]
    exact hι'A a
  have halg : letI := ι'.toAlgebra; Algebra.IsAlgebraic (Localization.Away ϖ) Ω := by
    let : Algebra (Localization.Away ϖ) Ω := ι'.toAlgebra
    let : Algebra (V.1.residueField (genericPoint V.1)) (Localization.Away ϖ) := γ.toAlgebra
    have : IsScalarTower (V.1.residueField (genericPoint V.1)) (Localization.Away ϖ) Ω :=
      IsScalarTower.of_algebraMap_eq fun z => (RingHom.congr_fun hγ z).symm
    exact Algebra.IsAlgebraic.tower_top (K := V.1.residueField (genericPoint V.1))
      (L := Localization.Away ϖ)
  let t : GeometricPoint (Spec (.of (Localization.Away ϖ))) :=
    ⟨Ω, Spec.map (CommRingCat.ofHom ι')⟩
  have ht : t.IsAlgebraic := isAlgebraic_specMap_geometricPoint ι' halg
  -- `g(t̄)` is the geometric generic point `x̄`
  have hc' : jW.base (genericPoint V.1) ⤳ s.hom (closedPoint s.residueField) := by
    rwa [hcy]
  have hcomp : (W.1.presheaf.stalkCongr (Inseparable.of_eq hcy.symm)).hom ≫
      curveLocalRingToFunctionField jW hc' = curveLocalRingToFunctionField jW hy := by
    simp only [curveLocalRingToFunctionField, TopCat.Presheaf.stalkCongr_hom]
    exact TopCat.Presheaf.stalkSpecializes_comp_assoc _ _ _ _
  have hring : ∀ r, ι' (algebraMap (etaleLocalRing B W.1 W.2 s) (Localization.Away ϖ)
      (structureSheafStalkFromLocalRing B W.1 W.2 s r)) =
      (CommRingCat.ofHom (algebraMap (V.1.residueField (genericPoint V.1)) Ω)).hom
        ((curveLocalRingToFunctionField jW hc').hom r) := by
    intro r
    obtain ⟨a, rfl⟩ := eAc.surjective r
    have h1 := congrArg (fun φ => φ.hom (eA a)) hcomp
    simp only [CommRingCat.hom_comp, RingHom.comp_apply] at h1
    show ι' (algebraMap (etaleLocalRing B W.1 W.2 s) (Localization.Away ϖ)
      (algebraMap A (etaleLocalRing B W.1 W.2 s) a)) = _
    rw [hι'A, hA a]
    exact congrArg _ h1.symm
  have hxg : t.hom ≫ B.inclusion.map g = x.hom := by
    rw [hg]
    exact specMap_comp_inv_fst_eq_of_ringHom jW hc' (structureSheafStalkFromLocalRing B W.1 W.2 s)
      (strictHenselizationToBase B W.1 W.2 s) rfl e he ι'
      (CommRingCat.ofHom (algebraMap (V.1.residueField (genericPoint V.1)) Ω)) hring
  have : ConnectedSpace (B.inclusion.obj V) := i6
  let : Algebra ((Spec (.of (Localization.Away ϖ))).residueField (t.hom default)) t.residueField :=
    GeometricPoint.residueFieldAlgebra t
  let pth : finiteEtaleFiberFunctor (t.map (B.inclusion.map g)) ≅ finiteEtaleFiberFunctor x :=
    eqToIso (congrArg (fun f => finiteEtaleFiberFunctor (⟨Ω, f⟩ : GeometricPoint V.1)) hxg)
  -- the maps `εₙ`
  let H' : ∀ n : ℕ, _ := fun n => padicLevelDirectImageStalkHom B W.1 W.2 s B V x jW
    (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth n
  let ε : ∀ n : ℕ, stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n)) →+
      (Fin r → ZMod (ℓ ^ (n + 1))) := fun n =>
    (AddEquiv.ulift (α := Fin r → ZMod (ℓ ^ (n + 1)))).toAddMonoidHom.comp
      (ConcreteCategory.hom (H' n))
  have hε : ∀ n (z : stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))),
      ε n z = (ConcreteCategory.hom (H' n) z).down := fun _ _ => rfl
  have hinj : ∀ n, Function.Injective (ε n) := fun n => AddEquiv.ulift.injective.comp
    (padicLevelDirectImageStalkHom_injective B W.1 W.2 s B V x jW (Localization.Away ϖ) e hKc g
      hg t ρ₀ hρ₀ pth n)
  have : IsAlgClosure ((Spec (.of (Localization.Away ϖ))).residueField (t.hom default))
      t.residueField := ht
  have : Normal ((Spec (.of (Localization.Away ϖ))).residueField (t.hom default))
      t.residueField := IsAlgClosure.normal _ _
  let := IsIntegralClosure.MulSemiringAction A (V.1.residueField (genericPoint V.1)) L
    (integralClosure A L)
  -- the automorphism of `t.source` induced by a ring automorphism of `Ω`
  let αR : (Ω ≃+* Ω) → (t.source ≅ t.source) := fun φ =>
    Scheme.Spec.mapIso (RingEquiv.toCommRingCatIso φ).op
  have hGx : ∀ G : Ω ≃ₐ[V.1.residueField (genericPoint V.1)] Ω,
      (αR G.toRingEquiv).hom ≫ x.hom = x.hom := fun G =>
    specMap_algEquiv_comp_geometricPoint_hom (genericPoint V.1) Ω G
  have hGt : ∀ G : Ω ≃ₐ[V.1.residueField (genericPoint V.1)] Ω,
      (αR G.toRingEquiv).hom ≫ (t.map (B.inclusion.map g)).hom =
        (t.map (B.inclusion.map g)).hom := fun G => by
    show (αR G.toRingEquiv).hom ≫ t.hom ≫ B.inclusion.map g = t.hom ≫ B.inclusion.map g
    rw [hxg]
    exact hGx G
  -- the image in `π₁(V, x̄)` of `G̃` is that of its restriction to `L`
  have hGφ : ∀ G : Ω ≃ₐ[V.1.residueField (genericPoint V.1)] Ω, etaleFundamentalGroupMulEquiv pth
      (GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g))
        (αR G.toRingEquiv) (hGt G)) =
      galoisToFundamentalGroup V.1 L Ω (G.restrictNormal L) := fun G => by
    rw [galoisToFundamentalGroup_restrictNormal_eq_sourceAutElement V.1 L Ω G (hGx G)]
    exact (etaleFundamentalGroupMulEquiv_eqToIso_sourceAutElement (S := V.1) hxg
      (αR G.toRingEquiv) (hGt G)).trans rfl
  -- sections over `K^{sh}` are fixed by the automorphisms of `t̄` over `K^{sh}`
  have hfix : ∀ n (w : stalk.obj (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n))) (φ : Ω ≃+* Ω)
      (hφ : ∀ k, φ (ι' k) = ι' k),
      levelRepresentation ρ₀ (n + 1) (etaleFundamentalGroupMulEquiv pth
        (GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g)) (αR φ)
          (comp_map_hom_of_comp_hom t _ (specMap_ringEquiv_comp_specMap_of_comp ι' φ hφ))))
        (ConcreteCategory.hom (H' n) w).down = (ConcreteCategory.hom (H' n) w).down := by
    intro n w φ hφ
    have hφt := specMap_ringEquiv_comp_specMap_of_comp ι' φ hφ
    obtain ⟨τ0, hτ0⟩ := GeometricPoint.exists_algEquiv_of_specMap_comp_hom t φ hφt
    have hmem := (mem_range_padicLevelDirectImageStalkHom_iff B W.1 W.2 s B V x jW
      (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth ht n
      (ULift.up (ConcreteCategory.hom (H' n) w).down)).mp ⟨w, rfl⟩
    have hα : (αR φ).hom = Spec.map (CommRingCat.ofHom τ0.toRingHom) := by
      show Spec.map (CommRingCat.ofHom (φ : Ω →+* Ω)) = _
      congr 2
      exact RingHom.ext fun z => (RingEquiv.congr_fun hτ0 z).symm
    exact hmem (τ0.restrictNormal _) τ0 (fun z => AlgEquiv.restrictNormal_commutes τ0 _ z)
      (αR φ) hα hφt
  refine ⟨ε, hinj, ?_, ?_, ?_, ?_, ?_⟩
  · -- (ii) the `ℤ_ℓ`-action factors through `ℤ/ℓⁿ⁺¹`
    intro n c w
    have htors : (ℓ ^ (n + 1)) • w = 0 := by
      apply hinj n
      rw [map_nsmul, map_zero]
      funext i
      simp
    rw [smul_eq_toZModPow_val_smul_of_pow_smul_eq_zero htors c, map_nsmul,
      ← Nat.cast_smul_eq_nsmul (ZMod (ℓ ^ (n + 1))), ZMod.natCast_zmod_val]
  · -- (iii) transitions
    intro n w
    have h := padicLevelDirectImageStalkHom_sheafFiber_padicTransition B W.1 W.2 s B V x jW
      (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth n w
    have t1 : stalk.map (D.map (LAdicSheaf.padicTransition B V ℓ ℱ n)) =
        ((pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])).map
          ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jW).map
            (padicLevelMathlibTransition B V x ρ₀ hρ₀ n)) := rfl
    rw [t1, hε, hε]
    funext i
    have hi := congrFun h i
    rw [levelReduction_apply] at hi
    show (ConcreteCategory.hom (padicLevelDirectImageStalkHom B W.1 W.2 s B V x jW
      (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth n) _).down i =
      (levelRingHom (n + 1)) ((ConcreteCategory.hom (padicLevelDirectImageStalkHom B W.1 W.2 s B V x
        jW (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth (n + 1)) w).down i)
    convert hi using 4
  · -- (iv) intertwiners
    intro M hM n w
    have h := padicLevelDirectImageStalkHom_sheafFiber_padicLevelMap B W.1 W.2 s B V x jW
      (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth M hM n w
    have t1 : stalk.map (D.map (LAdicSheaf.padicLevelMap (representationLAdicSheafMap B V x
        (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V x) hρ₀ hρ₀ M hM) n)) =
        ((pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} ℤ_[ℓ])).map
          ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jW).map
            (padicLevelMathlibMap B V x ρ₀ hρ₀ M hM n)) := rfl
    rw [t1, hε, hε]
    convert h using 3
  · -- (v) the geometric Frobenius
    intro n w
    let a : GeometricPoint.Hom s s := Stacks.Frobenius.frobeniusPointHom W.1 y
    obtain ⟨ã, hã⟩ := exists_iso_comp_hom_eq_baseChangeStrictHenselizationEndomorphism B W.1 W.2 s
      B V jW (Localization.Away ϖ) e t ht a
    have hãg := comp_inclusion_map_of_comp_baseChangeStrictHenselizationEndomorphism B W.1 W.2 s B
      V jW (Localization.Away ϖ) e hKc g hg t a ã.hom hã
    have hF := padicLevelDirectImageStalkHom_sheafFiber_pointSmallEtaleHom B W.1 W.2 s B V x jW
      (Localization.Away ϖ) e hKc g hg t ρ₀ hρ₀ pth a ã.hom hã hãg
      (GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g)) ã hãg)
      (GeometricPoint.sourceAutElement_hom_eq_finiteEtaleFiberMap (S := V.1)
        (t.map (B.inclusion.map g)) ã hãg _ rfl) n w
    have t1 : Stacks.Frobenius.frobeniusStalk (ModuleCat.{u + 1} ℤ_[ℓ]) W.1 y
        (D.obj (LAdicSheaf.padicLevel B V ℓ ℱ n)) =
        (pointSmallEtaleHom s.hom s.hom a.hom a.comm).sheafFiber.app
          ((etaleModuleDirectImage.{u, 0} ℤ_[ℓ] jW).obj (padicLevelMathlib B V x ρ₀ hρ₀ n)) := rfl
    rw [t1, hε, hε]
    -- the ring automorphism `τ` of `Ω` underlying `ã`
    let τ : Ω →+* Ω := (Spec.preimage ã.hom).hom
    let τi : Ω →+* Ω := (Spec.preimage ã.inv).hom
    have hτ : Spec.map (CommRingCat.ofHom τ) = ã.hom := Spec.map_preimage _
    have hτi : Spec.map (CommRingCat.ofHom τi) = ã.inv := Spec.map_preimage _
    have hτ1 : ∀ z, τi (τ z) = z := by
      have h : CommRingCat.ofHom τ ≫ CommRingCat.ofHom τi = 𝟙 _ := Spec.map_injective (by
        rw [Spec.map_comp, hτ, hτi, ã.inv_hom_id, Spec.map_id])
      exact fun z => congrArg (fun φ => φ.hom z) h
    have hτ2 : ∀ z, τ (τi z) = z := by
      have h : CommRingCat.ofHom τi ≫ CommRingCat.ofHom τ = 𝟙 _ := Spec.map_injective (by
        rw [Spec.map_comp, hτ, hτi, ã.hom_inv_id, Spec.map_id])
      exact fun z => congrArg (fun φ => φ.hom z) h
    let τe : Ω ≃+* Ω := RingEquiv.ofRingHom τ τi (RingHom.ext hτ2) (RingHom.ext hτ1)
    -- the endomorphism of `K^{sh}` induced by the Frobenius of the strict henselization
    obtain ⟨c, hc1, hc2⟩ := exists_ringHom_specMap_eq_conj
      (pullback.snd jW (strictHenselizationToBase B W.1 W.2 s)) e he
      (baseChangeStrictHenselizationEndomorphism B W.1 W.2 s B V jW a)
      (etaleLocalRingEndomorphism B W.1 W.2 a).hom (pullback.lift_snd _ _ _)
    have hτc : ∀ k, τ (ι' k) = ι' (c k) := by
      have h : CommRingCat.ofHom ι' ≫ CommRingCat.ofHom τ = CommRingCat.ofHom c ≫
          CommRingCat.ofHom ι' := Spec.map_injective (by
        rw [Spec.map_comp, Spec.map_comp, hτ, hc1]
        exact hã)
      exact fun k => congrArg (fun φ => φ.hom k) h
    -- the Frobenius of `H` read in `(B_q)^I`
    let θA : etaleLocalRing B W.1 W.2 s →ₐ[A] etaleLocalRing B W.1 W.2 s :=
      { (etaleLocalRingEndomorphism B W.1 W.2 a).hom with
        commutes' := fun z => by
          show (etaleLocalRingEndomorphism B W.1 W.2 a).hom
            (structureSheafStalkFromLocalRing B W.1 W.2 s (eAc z)) =
            structureSheafStalkFromLocalRing B W.1 W.2 s (eAc z)
          exact RingHom.congr_fun
            (etaleLocalRingEndomorphism_comp_structureSheafStalkFromLocalRing B W.1 W.2 a) _ }
    have hθiso : IsIso (etaleLocalRingEndomorphism B W.1 W.2 a) := by
      have := geometricPointStalkMap_isIso B W.1 W.2 a RingCat.{u}
      exact NatIso.isIso_app_of_isIso _ _
    have : IsLocalHom θA := ⟨fun z hz => (isUnit_map_iff
      (asIso (etaleLocalRingEndomorphism B W.1 W.2 a)).ringCatIsoToRingEquiv z).mp hz⟩
    have hcardA : Nat.card (ResidueField A) = Nat.card (W.1.residueField y) :=
      Nat.card_congr (ResidueField.mapEquiv eA).toEquiv
    have hθres : ∀ h, residue _ (θA h) ^ Nat.card (ResidueField A) = residue _ h := fun h => by
      rw [hcardA]
      exact residue_etaleLocalRingEndomorphism_pow B W.1 W.2 a _
        (frobeniusPointHom_preimage_pow W.1 y) h
    have hFrq : Fr • P = P := MulAction.mem_stabilizer_iff.mp hFrD
    have hFrΦ := IsIntegralClosure.galAction_algEquiv_comp_eq_of_residue_pow A
      (V.1.residueField (genericPoint V.1)) L P (etaleLocalRing B W.1 W.2 s) hInd Φ θA Fr hFrq _
      hFr hθres
    -- a lift `G̃` of `Fr⁻¹` to `Ω`, and `β = G̃⁻¹ ∘ τ` fixes `K^{sh}`
    let G : Ω ≃ₐ[V.1.residueField (genericPoint V.1)] Ω := AlgEquiv.liftNormal Fr⁻¹ Ω
    have hG : ∀ l : L, G (algebraMap L Ω l) = algebraMap L Ω (Fr⁻¹ l) :=
      AlgEquiv.liftNormal_commutes Fr⁻¹ Ω
    let β : Ω ≃+* Ω := τe.trans G.symm.toRingEquiv
    have hβι : ∀ k, β (ι' k) = ι' k := by
      have hext : (β.toRingHom).comp ι' = ι' := by
        refine IsLocalization.ringHom_ext (nonZeroDivisors (etaleLocalRing B W.1 W.2 s))
          (RingHom.ext fun h => ?_)
        show G.symm (τ (ι' (algebraMap _ _ h))) = ι' (algebraMap _ _ h)
        rw [hτc, hc2]
        show G.symm (algebraMap L Ω (ι (algebraMap _ _ (θA h)))) =
          algebraMap L Ω (ι (algebraMap _ _ h))
        rw [hιH, hιH]
        have h1 : ((Φ (θA h) : IsIntegralClosure.localizedSubring P) : L) =
            Fr⁻¹ ((Φ h : IsIntegralClosure.localizedSubring P) : L) := by
          rw [← hFrΦ h]
          exact (Fr.symm_apply_apply _).symm
        rw [h1, ← hG, AlgEquiv.symm_apply_apply]
      exact fun k => RingHom.congr_fun hext k
    -- decompose `ã = Spec G̃ ≫ Spec β`
    have hdec : ã.hom = (αR G.toRingEquiv ≪≫ αR β).hom := by
      rw [← hτ]
      show Spec.map (CommRingCat.ofHom τ) =
        Spec.map (CommRingCat.ofHom (G.toRingEquiv : Ω →+* Ω)) ≫
          Spec.map (CommRingCat.ofHom (β : Ω →+* Ω))
      rw [← Spec.map_comp]
      congr 1
      ext z
      show τ z = G (G.symm (τ z))
      rw [AlgEquiv.apply_symm_apply]
    have hβtg : (αR β).hom ≫ (t.map (B.inclusion.map g)).hom = (t.map (B.inclusion.map g)).hom :=
      comp_map_hom_of_comp_hom t _ (specMap_ringEquiv_comp_specMap_of_comp ι' β hβι)
    have hσdec : GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g)) ã hãg =
        GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g))
            (αR G.toRingEquiv) (hGt G) *
          GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g))
            (αR β) hβtg := by
      rw [← GeometricPoint.sourceAutElement_trans]
      exact GeometricPoint.sourceAutElement_congr (S := V.1) _ hdec _
    have hGφ' := hGφ G
    rw [AlgEquiv.restrict_liftNormal Ω Fr⁻¹] at hGφ'
    have hlev : levelRepresentation ρ₀ (n + 1) (etaleFundamentalGroupMulEquiv pth
        (GeometricPoint.sourceAutElement (S := V.1) (t.map (B.inclusion.map g)) ã hãg))
        (ConcreteCategory.hom (H' n) w).down =
        levelRepresentation ρ₀ (n + 1) (galoisToFundamentalGroup V.1 L Ω Fr⁻¹)
          (ConcreteCategory.hom (H' n) w).down := by
      rw [hσdec, map_mul, map_mul, Module.End.mul_apply, hfix n w β hβι, hGφ']
    convert hF.trans (hlev.trans (levelRepresentation_apply ρ₀ (n + 1) _ _)) using 3
  · -- (vii) the image is fixed by the inertia
    intro n w σ hσ
    obtain ⟨γ₀, hγ₀, rfl⟩ := Subgroup.mem_map.mp hσ
    rw [hε, ← levelRepresentation_apply]
    -- the extension `G̃` of `γ₀` to `Ω` fixes `K^{sh}`
    let G : Ω ≃ₐ[V.1.residueField (genericPoint V.1)] Ω := AlgEquiv.liftNormal γ₀ Ω
    have hG : ∀ l : L, G (algebraMap L Ω l) = algebraMap L Ω (γ₀ l) :=
      AlgEquiv.liftNormal_commutes γ₀ Ω
    have hγfix : ∀ k, γ₀ (ι k) = ι k := by
      rw [← IsIntegralClosure.fixingSubgroup_inertiaFixedField A
        (V.1.residueField (genericPoint V.1)) L P] at hγ₀
      intro k
      have hk : ι k ∈ (IsIntegralClosure.inertiaFixedField A
          (V.1.residueField (genericPoint V.1)) L P : Set L) := by
        rw [← hιrange]
        exact ⟨k, rfl⟩
      exact hγ₀ ⟨ι k, hk⟩
    have hGι : ∀ k, G (ι' k) = ι' k := fun k => by
      show G (algebraMap L Ω (ι k)) = algebraMap L Ω (ι k)
      rw [hG, hγfix]
    have hGφ' := hGφ G
    rw [AlgEquiv.restrict_liftNormal Ω γ₀] at hGφ'
    rw [show (galoisToFundamentalGroup V.1 L Ω).toMonoidHom γ₀ = _ from hGφ'.symm]
    exact hfix n w G.toRingEquiv hGι

end Stacks.EtaleCohomology

end
