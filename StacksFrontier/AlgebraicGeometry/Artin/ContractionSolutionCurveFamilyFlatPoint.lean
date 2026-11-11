module

public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilyFlatLift
public import StacksFrontier.AlgebraicGeometry.Artin.ContractionSolutionCurveFamilyFlatTorsion
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleChartLifts

/-!
# Flatness of the contraction at a point of an étale chart over the contracted locus

Let `s` be a solution of Artin's contraction problem of Stacks 0GH8 with target `X` over an
affine Dedekind base `S`, with `W` identified with the completion of `Spec A` at its closed
point, `A` an adically complete local `Γ(S)`-algebra with algebraically closed residue field on
which no nonzero element of `Γ(S)` is a zero divisor. Let `a : V ⟶ X` be an étale chart and
`v ∈ V` a point over the contracted locus `T`, with `R = 𝒪_{V,v}` Noetherian.

The maps `θₙ : A ⧸ 𝔪_Aⁿ⁺¹ → R ⧸ 𝔪ⁿ⁺¹` read off from `X_{/T} ≅ W` have sections: `θ₀` is an
isomorphism of residue fields, because the residue field of the fibre `V ×_X Spec κ_A` at the
point given by the chart is a separable algebraic extension of the algebraically closed `κ_A`;
the sections of `X` over `Spec (A ⧸ 𝔪_Aⁿ⁺¹)` corresponding to `Spec (A ⧸ 𝔪_Aⁿ⁺¹) ⟶ Spec A` then
lift uniquely through the formally étale chart, compatibly with `θ₀⁻¹`, and the lifts are local
maps `ρₙ : R → A ⧸ 𝔪_Aⁿ⁺¹` with `θₙ ∘ ρₙ` the truncation. The `ρₙ` are compatible, so `R` is
torsion free, hence flat, over `Γ(S)`
(`AlgebraicGeometry.Artin.flat_of_algHom_quotient_pow`).

## Main results

* `AlgebraicGeometry.Artin.ContractionSituation.Solution.bijective_truncTheta_zero`.
* `AlgebraicGeometry.Artin.ContractionSituation.Solution.flat_stalkMap_of_mem_T`: the structure
  morphism `V ⟶ S` is flat at `v`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite IsLocalRing

universe u

namespace AlgebraicGeometry.Artin.ContractionSituation.Solution

attribute [local instance] Space.pointTopology

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} [IsAffine S]
    {c : ContractionSituation B S hS} {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (s : Solution c X) {A : Type u} [CommRing A] [IsLocalRing A] [Algebra Γ(S, ⊤) A]
    {hA : B.Contains (Spec (.of A))}
    (eW : c.W ≅ Space.completionSheaf B S hS
      (yoneda.obj (Space.specOver B S hS S.isoSpec.inv A hA))
      {(Space.schemePointsHomeomorph B S hS (Space.specOver B S hS S.isoSpec.inv A hA)).symm
        (IsLocalRing.closedPoint A)})
    {V : BigFppfOver B S hS} (a : yoneda.obj V ⟶ X)
    {v : (BigFppfOver.toScheme B S hS).obj V}
    [Algebra Γ(S, ⊤) (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v)]
    (hR : algebraMap Γ(S, ⊤) (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) =
      (Space.chartStalkStructureMap V v).hom)
    (hv : Space.pointsMap B S hS (yoneda.obj V) a
      ((Space.schemePointsHomeomorph B S hS V).symm v) ∈ s.T)

/-- `𝔪¹` is a maximal ideal of a local ring. -/
theorem isMaximal_maximalIdeal_pow_zero_add_one (L : Type*) [CommRing L] [IsLocalRing L] :
    (maximalIdeal L ^ (0 + 1)).IsMaximal := by
  rw [zero_add, pow_one]
  infer_instance

/-- The truncations of the chart are compatible with the restrictions. -/
theorem truncRes_comp_truncCan {m n : ℕ} (h : m ≤ n) :
    Space.truncRes (Space.contains_spec_stalk_toScheme V v) _ h ≫ truncCan v hR n =
      truncCan v hR m := by
  apply (BigFppfOver.toScheme B S hS).map_injective
  rw [Functor.map_comp, truncCan, truncCan, Space.toScheme_map_homOfSpec,
    Space.toScheme_map_homOfSpec, Space.truncRes, Space.toScheme_map_specOverHom,
    ← Category.assoc, ← Spec.map_comp]
  congr 2

/-- The truncation of the chart at level `m` is the restriction of the one at level `n`. -/
theorem app_truncCan_eq_map {m n : ℕ} (h : m ≤ n) :
    a.app _ (truncCan v hR m) = X.map (Space.truncRes
      (Space.contains_spec_stalk_toScheme V v) _ h).op (a.app _ (truncCan v hR n)) := by
  have hn := NatTrans.naturality_apply a (Space.truncRes
    (Space.contains_spec_stalk_toScheme V v) _ h).op (truncCan v hR n)
  refine Eq.trans ?_ hn
  exact congrArg (a.app _) (truncRes_comp_truncCan hR h).symm

/-- The maps `A → 𝒪_{V,v} ⧸ 𝔪ⁿ⁺¹` are compatible with the truncations. -/
theorem factorₐ_comp_thetaHom {m n : ℕ} (h : m ≤ n) :
    (Ideal.Quotient.factorₐ Γ(S, ⊤) (Ideal.pow_le_pow_right (Nat.succ_le_succ h))).comp
      (s.thetaHom eW a hR hv n) = s.thetaHom eW a hR hv m := by
  have hn' := (Space.completionSubfunctor B S hS X s.T).map
    (Space.truncRes (Space.contains_spec_stalk_toScheme V v) _ h).op
    (s.hasImageIn_truncCan a hR hv n)
  have h1 := s.completionEquiv_map eW (Space.truncRes (Space.contains_spec_stalk_toScheme V v) _ h)
    ⟨a.app _ (truncCan v hR n), s.hasImageIn_truncCan a hR hv n⟩ hn'
  have h2 : (s.completionEquiv eW _ ⟨a.app _ (truncCan v hR m), s.hasImageIn_truncCan a hR hv m⟩) =
      (s.completionEquiv eW _ ⟨X.map (Space.truncRes
        (Space.contains_spec_stalk_toScheme V v) _ h).op (a.app _ (truncCan v hR n)), hn'⟩) :=
    congrArg (s.completionEquiv eW _) (Subtype.ext (app_truncCan_eq_map a hR h))
  have h3 := (s.specOverHom_thetaHom eW a hR hv m).trans ((congrArg Subtype.val h2).trans (h1.trans
    (congrArg (fun g => Space.truncRes (Space.contains_spec_stalk_toScheme V v) _ h ≫ g)
      (s.specOverHom_thetaHom eW a hR hv n).symm)))
  rw [Space.truncRes, Space.specOverHom_comp] at h3
  exact (Space.specOverHom_injective h3).symm

include hR in
/-- The maps `θₙ` are compatible with the restrictions. -/
theorem truncRes_comp_truncTau {m n : ℕ} (h : m ≤ n) :
    Space.truncRes (Space.contains_spec_stalk_toScheme V v) _ h ≫ s.truncTau eW a hR hv n =
      s.truncTau eW a hR hv m ≫ Space.truncRes hA (maximalIdeal A) h := by
  rw [truncTau, truncTau, Space.truncRes, Space.truncRes, Space.specOverHom_comp,
    Space.specOverHom_comp]
  apply Space.specOverHom_congr
  ext x
  obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
  exact DFunLike.congr_fun (s.factorₐ_comp_thetaHom eW a hR hv h) x

variable (ha : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
  (BigFppfOver.toScheme B S hS)).presheaf a)

include ha in
/-- **`θ₀` is an isomorphism of residue fields.** The truncations at level `0` of the chart and
of `Spec A` give a point of the fibre `E = V ×_X Spec κ_A`, a scheme étale over `Spec κ_A`; its
residue field is `κ_A`, which is algebraically closed, and it surjects onto `κ(v)`. -/
theorem bijective_truncTheta_zero [IsAlgClosed (ResidueField A)] :
    Function.Bijective (s.truncTheta eW a hR hv 0) := by
  let b1 : yoneda.obj (Space.truncSpec hA (maximalIdeal A) 0) ⟶ X :=
    yonedaEquiv.symm (s.betaSection eW 0)
  have hi : yoneda.map (truncCan v hR 0) ≫ a = yoneda.map (s.truncTau eW a hR hv 0) ≫ b1 := by
    apply yonedaEquiv.injective
    rw [yonedaEquiv_comp, yonedaEquiv_yoneda_map, yonedaEquiv_comp, yonedaEquiv_yoneda_map]
    exact (s.map_truncTau_betaSection eW a hR hv 0).symm
  let ℓ := ha.rep.lift' (truncCan v hR 0) (s.truncTau eW a hR hv 0) hi
  have h1 : ℓ ≫ ha.rep.fst' b1 = truncCan v hR 0 := ha.rep.lift'_fst _ _ _
  have h2 : ℓ ≫ ha.rep.snd b1 = s.truncTau eW a hR hv 0 := ha.rep.lift'_snd _ _ _
  have hq : Etale ((BigFppfOver.toScheme B S hS).map (ha.rep.snd b1)) := ha.property_snd b1
  have hsurjℓ : Function.Surjective
      (Scheme.stalkClosedPointTo ((BigFppfOver.toScheme B S hS).map ℓ)) := by
    have hc : ∀ f, f = (BigFppfOver.toScheme B S hS).map (truncCan v hR 0) →
        Function.Surjective (Scheme.stalkClosedPointTo f) := by
      rintro f rfl
      have : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal
          (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) ^ (0 + 1)))).hom :=
        IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
      exact surjective_stalkClosedPointTo_SpecMap_comp _ Ideal.Quotient.mk_surjective
    have hcomp := hc ((BigFppfOver.toScheme B S hS).map ℓ ≫
      (BigFppfOver.toScheme B S hS).map (ha.rep.fst' b1)) (by rw [← Functor.map_comp, h1])
    have e := Scheme.stalkClosedPointTo_comp ((BigFppfOver.toScheme B S hS).map ℓ)
      ((BigFppfOver.toScheme B S hS).map (ha.rep.fst' b1))
    intro y
    obtain ⟨x, hx⟩ := hcomp y
    rw [e] at hx
    exact ⟨_, hx⟩
  have := isMaximal_maximalIdeal_pow_zero_add_one A
  have := isMaximal_maximalIdeal_pow_zero_add_one
    (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v)
  let : Field (A ⧸ maximalIdeal A ^ (0 + 1)) := Ideal.Quotient.field _
  let : Field (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v ⧸
      maximalIdeal (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) ^ (0 + 1)) :=
    Ideal.Quotient.field _
  have : IsAlgClosed (A ⧸ maximalIdeal A ^ (0 + 1)) :=
    IsAlgClosed.of_ringEquiv (ResidueField A) _
      (Ideal.quotEquivOfEq (by rw [zero_add, pow_one]))
  refine ⟨RingHom.injective (s.truncTheta eW a hR hv 0).toRingHom, ?_⟩
  exact surjective_of_etale_of_isAlgClosed (s.truncTheta eW a hR hv 0).toRingHom
    ((BigFppfOver.toScheme B S hS).map (ha.rep.snd b1)) ((BigFppfOver.toScheme B S hS).map ℓ)
    (by rw [← Functor.map_comp, h2]; rfl) hsurjℓ

/-- `θ₀`, as an isomorphism of `Γ(S)`-algebras. -/
def truncThetaZeroEquiv [IsAlgClosed (ResidueField A)] :
    (A ⧸ maximalIdeal A ^ (0 + 1)) ≃ₐ[Γ(S, ⊤)]
      (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v ⧸
        maximalIdeal (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) ^ (0 + 1)) :=
  AlgEquiv.ofBijective _ (s.bijective_truncTheta_zero eW a hR hv ha)

/-- `Spec θ₀⁻¹ : Spec κ_A ⟶ Spec κ(v)`, as a morphism of the site. -/
def sigmaZeroSpec [IsAlgClosed (ResidueField A)] :
    Space.truncSpec hA (maximalIdeal A) 0 ⟶ truncY v 0 :=
  Space.specOverHom B S hS S.isoSpec.inv _ _ (s.truncThetaZeroEquiv eW a hR hv ha).symm.toAlgHom

/-- The morphism `σ₀ : Spec κ_A ⟶ V` through `Spec κ(v)`, given by `θ₀⁻¹`. -/
def sigmaZero [IsAlgClosed (ResidueField A)] : Space.truncSpec hA (maximalIdeal A) 0 ⟶ V :=
  s.sigmaZeroSpec eW a hR hv ha ≫ truncCan v hR 0

/-- `Spec θ₀` followed by `σ₀` is the truncation of the chart at level `0`. -/
theorem truncTau_comp_sigmaZero [IsAlgClosed (ResidueField A)] :
    s.truncTau eW a hR hv 0 ≫ s.sigmaZero eW a hR hv ha = truncCan v hR 0 := by
  have h : s.truncTau eW a hR hv 0 ≫ s.sigmaZeroSpec eW a hR hv ha = 𝟙 _ := by
    rw [truncTau, sigmaZeroSpec, Space.specOverHom_comp, ← Space.specOverHom_id]
    exact Space.specOverHom_congr (AlgHom.ext fun x =>
      (s.truncThetaZeroEquiv eW a hR hv ha).apply_symm_apply x)
  rw [sigmaZero, ← Category.assoc, h, Category.id_comp]

/-- `σ₀` lifts `β₀` through the chart. -/
theorem app_sigmaZero [IsAlgClosed (ResidueField A)] :
    a.app _ (s.sigmaZero eW a hR hv ha) = s.betaSection eW 0 := by
  have h : s.sigmaZeroSpec eW a hR hv ha ≫ s.truncTau eW a hR hv 0 = 𝟙 _ := by
    rw [truncTau, sigmaZeroSpec, Space.specOverHom_comp, ← Space.specOverHom_id]
    exact Space.specOverHom_congr (AlgHom.ext fun x =>
      (s.truncThetaZeroEquiv eW a hR hv ha).symm_apply_apply x)
  have hn := NatTrans.naturality_apply a (s.sigmaZeroSpec eW a hR hv ha).op (truncCan v hR 0)
  refine hn.trans ((congrArg (fun z => X.map (s.sigmaZeroSpec eW a hR hv ha).op z)
    (s.map_truncTau_betaSection eW a hR hv 0).symm).trans ?_)
  rw [← Functor.map_comp_apply, ← op_comp, h, op_id, Functor.map_id_apply]

/-- The lift `σₙ : Spec (A ⧸ 𝔪_Aⁿ⁺¹) ⟶ V` of `βₙ` through the formally étale chart, restricting
to `σ₀`. -/
def sigma [IsAlgClosed (ResidueField A)] (n : ℕ) : Space.truncSpec hA (maximalIdeal A) n ⟶ V :=
  (Space.existsUnique_lift_truncSpec a (Space.formallyEtale_of_etale B S hS a ha) hA
    (maximalIdeal A) n (s.sigmaZero eW a hR hv ha) (s.betaSection eW n)
    ((s.map_truncRes_betaSection eW _).trans (s.app_sigmaZero eW a hR hv ha).symm)).exists.choose

/-- `σₙ` restricts to `σ₀` and lifts `βₙ`. -/
theorem sigma_spec [IsAlgClosed (ResidueField A)] (n : ℕ) :
    Space.truncRes hA (maximalIdeal A) (Nat.zero_le n) ≫ s.sigma eW a hR hv ha n =
      s.sigmaZero eW a hR hv ha ∧ a.app _ (s.sigma eW a hR hv ha n) = s.betaSection eW n :=
  (Space.existsUnique_lift_truncSpec a (Space.formallyEtale_of_etale B S hS a ha) hA
    (maximalIdeal A) n (s.sigmaZero eW a hR hv ha) (s.betaSection eW n)
    ((s.map_truncRes_betaSection eW _).trans
      (s.app_sigmaZero eW a hR hv ha).symm)).exists.choose_spec

/-- The lifts `σₙ` are compatible with the restrictions. -/
theorem truncRes_comp_sigma [IsAlgClosed (ResidueField A)] {m n : ℕ} (h : m ≤ n) :
    Space.truncRes hA (maximalIdeal A) h ≫ s.sigma eW a hR hv ha n = s.sigma eW a hR hv ha m := by
  refine (Space.existsUnique_lift_truncSpec a (Space.formallyEtale_of_etale B S hS a ha) hA
    (maximalIdeal A) m (s.sigmaZero eW a hR hv ha) (s.betaSection eW m)
    ((s.map_truncRes_betaSection eW _).trans (s.app_sigmaZero eW a hR hv ha).symm)).unique ⟨?_, ?_⟩
    (s.sigma_spec eW a hR hv ha m)
  · change Space.truncRes hA (maximalIdeal A) (Nat.zero_le m) ≫
      Space.truncRes hA (maximalIdeal A) h ≫ s.sigma eW a hR hv ha n = _
    rw [← Category.assoc, Space.truncRes_comp]
    exact (s.sigma_spec eW a hR hv ha n).1
  · exact (NatTrans.naturality_apply a (Space.truncRes hA (maximalIdeal A) h).op
      (s.sigma eW a hR hv ha n)).trans ((congrArg
        (fun z => X.map (Space.truncRes hA (maximalIdeal A) h).op z)
        (s.sigma_spec eW a hR hv ha n).2).trans (s.map_truncRes_betaSection eW h))

/-- **`Spec θₙ` followed by `σₙ` is the truncation of the chart.** Both lift the truncation of
the chart through the formally étale chart and restrict to the truncation at level `0`. -/
theorem truncTau_comp_sigma [IsAlgClosed (ResidueField A)] (n : ℕ) :
    s.truncTau eW a hR hv n ≫ s.sigma eW a hR hv ha n = truncCan v hR n := by
  have hy : X.map (Space.truncRes (Space.contains_spec_stalk_toScheme V v) _ (Nat.zero_le n)).op
      (a.app _ (truncCan v hR n)) = a.app _ (truncCan v hR 0) :=
    (app_truncCan_eq_map a hR (Nat.zero_le n)).symm
  refine (Space.existsUnique_lift_truncSpec a (Space.formallyEtale_of_etale B S hS a ha)
    (Space.contains_spec_stalk_toScheme V v) _ n (truncCan v hR 0) (a.app _ (truncCan v hR n))
    hy).unique ⟨?_, ?_⟩ ⟨truncRes_comp_truncCan hR (Nat.zero_le n), rfl⟩
  · change Space.truncRes (Space.contains_spec_stalk_toScheme V v) _ (Nat.zero_le n) ≫
      s.truncTau eW a hR hv n ≫ s.sigma eW a hR hv ha n = _
    rw [← Category.assoc, s.truncRes_comp_truncTau eW a hR hv (Nat.zero_le n), Category.assoc,
      (s.sigma_spec eW a hR hv ha n).1, s.truncTau_comp_sigmaZero eW a hR hv ha]
  · exact (NatTrans.naturality_apply a (s.truncTau eW a hR hv n).op
      (s.sigma eW a hR hv ha n)).trans ((congrArg
        (fun z => X.map (s.truncTau eW a hR hv n).op z)
        (s.sigma_spec eW a hR hv ha n).2).trans (s.map_truncTau_betaSection eW a hR hv n))

/-- `σₙ` sends the point of `Spec (A ⧸ 𝔪_Aⁿ⁺¹)` to `v`. -/
theorem toScheme_map_sigma_closedPoint [IsAlgClosed (ResidueField A)] (n : ℕ) :
    (BigFppfOver.toScheme B S hS).map (s.sigma eW a hR hv ha n)
      (closedPoint (A ⧸ maximalIdeal A ^ (n + 1))) = v := by
  have hy := eq_of_mem_Spec_quotient_pow n (closedPoint (A ⧸ maximalIdeal A ^ (n + 1)))
    ((BigFppfOver.toScheme B S hS).map (s.truncTau eW a hR hv n)
      (closedPoint (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v ⧸
        maximalIdeal (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) ^ (n + 1))))
  have h := toScheme_map_truncCan_apply v hR n
    (closedPoint (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v ⧸
      maximalIdeal (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) ^ (n + 1)))
  rw [← s.truncTau_comp_sigma eW a hR hv ha n, Functor.map_comp] at h
  rw [hy]
  exact h

/-- The local map `𝒪_{V,v} ⟶ A ⧸ 𝔪_Aⁿ⁺¹` whose spectrum, followed by `Spec 𝒪_{V,v} ⟶ V`, is
`σₙ`. -/
def rhoHom [IsAlgClosed (ResidueField A)] (n : ℕ) :
    ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v ⟶
      CommRingCat.of (A ⧸ maximalIdeal A ^ (n + 1)) :=
  (exists_eq_SpecMap_comp_fromSpecStalk (L := .of (A ⧸ maximalIdeal A ^ (n + 1)))
    ((BigFppfOver.toScheme B S hS).map (s.sigma eW a hR hv ha n))
    (s.toScheme_map_sigma_closedPoint eW a hR hv ha n)).choose

/-- `rhoHom` is a local map. -/
theorem isLocalHom_rhoHom [IsAlgClosed (ResidueField A)] (n : ℕ) :
    IsLocalHom (s.rhoHom eW a hR hv ha n).hom :=
  (exists_eq_SpecMap_comp_fromSpecStalk (L := .of (A ⧸ maximalIdeal A ^ (n + 1)))
    ((BigFppfOver.toScheme B S hS).map (s.sigma eW a hR hv ha n))
    (s.toScheme_map_sigma_closedPoint eW a hR hv ha n)).choose_spec.1

/-- `Spec` of `rhoHom`, followed by `Spec 𝒪_{V,v} ⟶ V`, is `σₙ`. -/
theorem SpecMap_rhoHom_comp [IsAlgClosed (ResidueField A)] (n : ℕ) :
    Spec.map (s.rhoHom eW a hR hv ha n) ≫ ((BigFppfOver.toScheme B S hS).obj V).fromSpecStalk v =
      (BigFppfOver.toScheme B S hS).map (s.sigma eW a hR hv ha n) :=
  (exists_eq_SpecMap_comp_fromSpecStalk (L := .of (A ⧸ maximalIdeal A ^ (n + 1)))
    ((BigFppfOver.toScheme B S hS).map (s.sigma eW a hR hv ha n))
    (s.toScheme_map_sigma_closedPoint eW a hR hv ha n)).choose_spec.2

/-- The map of `Γ(S)`-algebras `ρₙ : 𝒪_{V,v} → A ⧸ 𝔪_Aⁿ⁺¹`. -/
def rho [IsAlgClosed (ResidueField A)] (n : ℕ) :
    ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v →ₐ[Γ(S, ⊤)]
      A ⧸ maximalIdeal A ^ (n + 1) :=
  { (s.rhoHom eW a hR hv ha n).hom with
    commutes' := fun r => by
      have h := Space.chartStalkStructureMap_comp_eq (s.rhoHom eW a hR hv ha n) (by
        rw [← Category.assoc, s.SpecMap_rhoHom_comp eW a hR hv ha n]
        exact Space.toScheme_map_comp_str (s.sigma eW a hR hv ha n))
      change (s.rhoHom eW a hR hv ha n).hom (algebraMap _ _ r) = _
      rw [hR]
      exact congrArg (fun g => g.hom r) h }

/-- **`θₙ ∘ ρₙ` is the truncation `𝒪_{V,v} → 𝒪_{V,v} ⧸ 𝔪ⁿ⁺¹`.** Both are local maps out of
`𝒪_{V,v}` inducing the truncation of the chart. -/
theorem truncTheta_rho [IsAlgClosed (ResidueField A)] (n : ℕ)
    (y : ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) :
    s.truncTheta eW a hR hv n (s.rho eW a hR hv ha n y) = Ideal.Quotient.mk _ y := by
  have := s.isLocalHom_rhoHom eW a hR hv ha n
  have : IsLocalHom (s.truncTheta eW a hR hv n).toRingHom := isLocalHom_of_quotient_pow n _
  have : IsLocalHom (s.rhoHom eW a hR hv ha n ≫
      CommRingCat.ofHom (s.truncTheta eW a hR hv n).toRingHom).hom :=
    RingHom.isLocalHom_comp _ _
  have : IsLocalHom (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal
      (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) ^ (n + 1)))).hom :=
    IsLocalHom.of_surjective _ Ideal.Quotient.mk_surjective
  have h := SpecMap_comp_fromSpecStalk_injective
    (s.rhoHom eW a hR hv ha n ≫ CommRingCat.ofHom (s.truncTheta eW a hR hv n).toRingHom)
    (CommRingCat.ofHom (Ideal.Quotient.mk (maximalIdeal
      (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) ^ (n + 1)))) (by
      rw [Spec.map_comp, Category.assoc, s.SpecMap_rhoHom_comp eW a hR hv ha n]
      change (BigFppfOver.toScheme B S hS).map (s.truncTau eW a hR hv n) ≫ _ = _
      rw [← Functor.map_comp, s.truncTau_comp_sigma eW a hR hv ha n]
      rfl)
  exact congrArg (fun g => g.hom y) h

/-- The maps `ρₙ` are compatible with the truncations. -/
theorem factor_rho [IsAlgClosed (ResidueField A)] {m n : ℕ} (h : m ≤ n)
    (y : ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) :
    Ideal.Quotient.factor (Ideal.pow_le_pow_right (Nat.succ_le_succ h))
      (s.rho eW a hR hv ha n y) = s.rho eW a hR hv ha m y := by
  have := s.isLocalHom_rhoHom eW a hR hv ha n
  have := s.isLocalHom_rhoHom eW a hR hv ha m
  have : IsLocalHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.succ_le_succ h) : maximalIdeal A ^ (n + 1) ≤ _)) :=
    IsLocalHom.of_surjective _ (Ideal.Quotient.factor_surjective _)
  have : IsLocalHom (s.rhoHom eW a hR hv ha n ≫ CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.succ_le_succ h) : maximalIdeal A ^ (n + 1) ≤ _))).hom :=
    RingHom.isLocalHom_comp _ _
  have h' := SpecMap_comp_fromSpecStalk_injective
    (s.rhoHom eW a hR hv ha n ≫ CommRingCat.ofHom (Ideal.Quotient.factor
      (Ideal.pow_le_pow_right (Nat.succ_le_succ h) : maximalIdeal A ^ (n + 1) ≤ _)))
    (s.rhoHom eW a hR hv ha m) (by
      rw [Spec.map_comp, Category.assoc, s.SpecMap_rhoHom_comp eW a hR hv ha n,
        s.SpecMap_rhoHom_comp eW a hR hv ha m]
      change (BigFppfOver.toScheme B S hS).map (Space.truncRes hA (maximalIdeal A) h) ≫ _ = _
      rw [← Functor.map_comp, s.truncRes_comp_sigma eW a hR hv ha h])
  exact congrArg (fun g => g.hom y) h'

/-- The kernel of `ρₙ` lies in `𝔪ⁿ⁺¹`. -/
theorem mem_of_rho_eq_zero [IsAlgClosed (ResidueField A)] (n : ℕ)
    (y : ((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v)
    (hy : s.rho eW a hR hv ha n y = 0) :
    y ∈ maximalIdeal (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) ^ (n + 1) := by
  rw [← Ideal.Quotient.eq_zero_iff_mem, ← s.truncTheta_rho eW a hR hv ha n y, hy, map_zero]

include s eW hR hv ha in
/-- **Flatness at a point over the contracted locus.** Let `a : V ⟶ X` be an étale chart and
`v ∈ V` a point over `T` whose local ring is Noetherian. Then the structure morphism `V ⟶ S` is
flat at `v`: the maps `ρₙ : 𝒪_{V,v} → A ⧸ 𝔪_Aⁿ⁺¹` are compatible `Γ(S)`-algebra maps with kernels
in `𝔪ⁿ⁺¹`, so `𝒪_{V,v}` is torsion free, hence flat, over the Dedekind domain `Γ(S)`, and so
over its localization `𝒪_{S,s}`. -/
theorem flat_stalkMap_of_mem_T [IsDomain Γ(S, ⊤)] [IsDedekindDomain Γ(S, ⊤)]
    [IsAlgClosed (ResidueField A)]
    [IsNoetherianRing (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v)]
    (hAc : IsAdicComplete (maximalIdeal A) A)
    (hAt : ∀ r : Γ(S, ⊤), r ≠ 0 → IsSMulRegular A r) :
    ((B.inclusion.map V.hom).stalkMap v).hom.Flat := by
  have := hAc
  let f : (BigFppfOver.toScheme B S hS).obj V ⟶ S := B.inclusion.map V.hom
  change (f.stalkMap v).hom.Flat
  let : Algebra Γ(S, ⊤) (S.presheaf.stalk (f v)) :=
    (S.presheaf.germ ⊤ (f v) trivial).hom.toAlgebra
  have : IsLocalization.AtPrime (S.presheaf.stalk (f v))
      ((isAffineOpen_top S).primeIdealOf ⟨f v, trivial⟩).asIdeal :=
    (isAffineOpen_top S).isLocalization_stalk ⟨f v, trivial⟩
  let : Algebra (S.presheaf.stalk (f v))
      (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) := (f.stalkMap v).hom.toAlgebra
  have : IsScalarTower Γ(S, ⊤) (S.presheaf.stalk (f v))
      (((BigFppfOver.toScheme B S hS).obj V).presheaf.stalk v) :=
    IsScalarTower.of_algebraMap_eq fun r => by
      rw [hR]
      exact (congrArg (fun g => g.hom r) (Scheme.Hom.germ_stalkMap f ⊤ v trivial)).symm
  exact flat_of_algHom_quotient_pow
    ((isAffineOpen_top S).primeIdealOf ⟨f v, trivial⟩).asIdeal.primeCompl
    hAt (s.rho eW a hR hv ha) (fun _ _ h y => s.factor_rho eW a hR hv ha h y)
    (s.mem_of_rho_eq_zero eW a hR hv ha)

end AlgebraicGeometry.Artin.ContractionSituation.Solution

end
