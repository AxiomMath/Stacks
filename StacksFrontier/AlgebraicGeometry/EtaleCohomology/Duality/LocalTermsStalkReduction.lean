module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Duality.LocalTermsInertia
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModuleBalancedTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.RelativeCurveHigherVanishing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Purity.AffineLineHigherDirectImage
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ExtensionByZero.ModuleRestrictionInverseImage

/-!
# The local terms at the boundary from the stalks at the boundary

Let `j : U ⟶ Y` be a quasi-compact open immersion, `N > 0` invertible on `Y` and `G` a sheaf of
`ℤ/N`-modules on `U_étale`. The local terms of `G` at the boundary are the cokernel of
`j_! G ⟶ j_* G` and `R¹j_* G`. Over `U` both vanish (`j_! ⟶ j_*` is invertible there, and the
higher direct images along `j` vanish on `U`), at a geometric point outside `U` the stalk of the
cokernel is a quotient of the stalk of `j_* G`, and stalks detect `c • 𝟙 = 0`. So `c` kills both
local terms as soon as it kills the stalks of `j_* G` and `R¹j_* G` at the geometric points of
`Y` outside `U` (`Stacks.EtaleCohomology.localTerms_nsmul_id_eq_zero_of_boundaryStalksKilledBy`).

For the ℓ-adic sheaf `ℱ_{ρ₀}` of a representation of `π₁` of a smooth affine curve `V` over a
finite field, this reduces `Stacks.EtaleCohomology.LAdicSheaf.LocalTermsStalkInput` to a
statement about the stalks at the boundary geometric points of `X̄_k̄` alone:
`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsBoundaryStalkInput` says that finitely many inertia
groups at places at infinity govern them. The per-place bounds of the hypothesis of
`LocalTermsStalkInput` are made uniform by taking the largest of finitely many exponents
(`Stacks.EtaleCohomology.InertiaLevelsKilledBy.mono`).

## Main definitions

* `Stacks.EtaleCohomology.BoundaryStalksKilledBy`.
* `Stacks.EtaleCohomology.LAdicSheaf.IsBoundaryInertia`.
* `Stacks.EtaleCohomology.LAdicSheaf.LocalTermsBoundaryStalkInput`.

## Main results

* `Stacks.EtaleCohomology.nsmul_id_eq_zero_of_forall_sheafFiber`.
* `Stacks.EtaleCohomology.localTerms_nsmul_id_eq_zero_of_boundaryStalksKilledBy`.
* `Stacks.EtaleCohomology.LAdicSheaf.localTermsStalkInput_of_localTermsBoundaryStalkInput`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale
open Stacks.Frobenius Matrix

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] moduleCat_hasLimitsOfSize

/-- **`InertiaLevelsKilledBy` is monotone in the exponent.** -/
theorem InertiaLevelsKilledBy.mono {ℓ r : ℕ} [Fact ℓ.Prime] {G : Type*} [Group G]
    [TopologicalSpace G]
    {I : Subgroup G} {ρ : G →* GL (Fin r) ℤ_[ℓ]} {e e' : ℕ} (h : InertiaLevelsKilledBy I ρ e)
    (hee' : e ≤ e') : InertiaLevelsKilledBy I ρ e' := by
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hee'
  intro n
  refine ⟨fun v hv => ?_, fun c hc hcoc => ?_⟩
  · rw [add_comm e d, pow_add ℓ d e, mul_smul, (h n).1 v hv, smul_zero]
  · obtain ⟨m, hm⟩ := (h n).2 c hc hcoc
    refine ⟨ℓ ^ d • m, fun σ => ?_⟩
    rw [add_comm e d, pow_add ℓ d e, mul_smul, hm σ, mulVec_smul, smul_sub]

section Stalks

variable {Λ : Type} [CommRing Λ]

/-- **Stalks detect `c • 𝟙 = 0`.** A sheaf of `Λ`-modules on Mathlib's small étale site whose
stalks at all geometric points are killed by `c` is killed by `c`: the cokernel of `c • 𝟙` is
computed stalkwise, so its projection is invertible on every stalk, hence invertible. -/
theorem nsmul_id_eq_zero_of_forall_sheafFiber {X : Scheme.{u}} (F : EtaleModules.{u, 0} Λ X)
    (c : ℕ) (h : ∀ s : GeometricPoint X,
      c • 𝟙 (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj F) = 0) :
    c • 𝟙 F = 0 := by
  have hπ : IsIso (cokernel.π (c • 𝟙 F)) := by
    refine isIso_of_forall_isIso_etaleModuleSheafFiber_map _ fun s => ?_
    let Φ := (Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)
    have h0 : Φ.map (c • 𝟙 F) = 0 := by
      rw [Functor.map_nsmul, CategoryTheory.Functor.map_id]
      exact h s
    have : IsIso (Φ.map (cokernel.π (c • 𝟙 F)) ≫ (PreservesCokernel.iso Φ (c • 𝟙 F)).hom) := by
      rw [PreservesCokernel.π_iso_hom Φ (c • 𝟙 F)]
      exact cokernel.π_of_zero h0
    exact IsIso.of_isIso_comp_right _ (PreservesCokernel.iso Φ (c • 𝟙 F)).hom
  rw [← cancel_mono (cokernel.π (c • 𝟙 F)), cokernel.condition, zero_comp]

/-- If `c` kills the stalk of `G` at a geometric point, it kills the stalk there of the cokernel
of any morphism to `G`. -/
theorem nsmul_id_sheafFiber_cokernel_eq_zero {X : Scheme.{u}} {F G : EtaleModules.{u, 0} Λ X}
    (ψ : F ⟶ G) (c : ℕ) (s : GeometricPoint X)
    (h : c • 𝟙 (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj G) = 0) :
    c • 𝟙 (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      (cokernel ψ)) = 0 := by
  let Φ := (Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)
  have h1 : Φ.map (cokernel.π ψ) ≫ (c • 𝟙 (Φ.obj (cokernel ψ))) =
      Φ.map (cokernel.π ψ) ≫ (0 : Φ.obj (cokernel ψ) ⟶ Φ.obj (cokernel ψ)) := by
    rw [Preadditive.comp_nsmul, Category.comp_id, comp_zero,
      ← Category.id_comp (Φ.map (cokernel.π ψ)), ← Preadditive.nsmul_comp]
    show (c • 𝟙 (Φ.obj G)) ≫ _ = 0
    rw [h, zero_comp]
  exact (cancel_epi _).1 h1

/-- **Stalks over an open subscheme.** The stalk of a sheaf `Q` on `X` at a geometric point lying
in the image of an open immersion `j : U ⟶ X` is a stalk of `j⁻¹ Q`; so it vanishes when `j⁻¹ Q`
does. -/
theorem isZero_sheafFiber_of_isZero_inverseImage {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (Q : EtaleModules.{u, 0} Λ X)
    (hQ : IsZero ((etaleModuleInverseImage.{u, 0} Λ j).obj Q)) (s : GeometricPoint X)
    (hs : s.hom.base default ∈ Set.range j.base) :
    IsZero (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj Q) := by
  have hsub : Set.range s.hom.base ⊆ Set.range j.base := by
    rintro _ ⟨y, rfl⟩
    rwa [Subsingleton.elim y default]
  rw [← IsOpenImmersion.lift_fac j s.hom hsub]
  let t := IsOpenImmersion.lift j s.hom hsub
  let e := (etaleModuleInverseImageSheafFiberIso.{u, 0} (Λ := Λ) j t).app Q
  refine (Functor.map_isZero ((Scheme.pointSmallEtale t).sheafFiber (A := ModuleCat.{u + 1} Λ))
    hQ).of_iso ?_
  let i₁ : ((Scheme.pointSmallEtale (t ≫ j)).ulift.{u + 1}).sheafFiber
      (A := ModuleCat.{u + 1} Λ) ≅ (Scheme.pointSmallEtale (t ≫ j)).sheafFiber :=
    GrothendieckTopology.Point.sheafFiberUliftNatIso _ _
  let i₂ : ((Scheme.pointSmallEtale t).ulift.{u + 1}).sheafFiber
      (A := ModuleCat.{u + 1} Λ) ≅ (Scheme.pointSmallEtale t).sheafFiber :=
    GrothendieckTopology.Point.sheafFiberUliftNatIso _ _
  exact (i₁.app Q).symm ≪≫ e.symm ≪≫ i₂.app _

/-- Over the open `U`, the cokernel of `j_! G ⟶ j_* G` vanishes. -/
theorem isZero_inverseImage_cokernel_extensionByZeroToDirectImage {U X : Scheme.{u}} (j : U ⟶ X)
    [IsOpenImmersion j] (G : EtaleModules.{u, 0} Λ U) :
    IsZero ((etaleModuleInverseImage.{u, 0} Λ j).obj
      (cokernel ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ j).app G))) := by
  let R := etaleModuleRestriction.{u, 0} Λ j
  have : R.IsLeftAdjoint := (etaleModuleRestrictionDirectImageAdj.{u, 0} Λ j).isLeftAdjoint
  have := isIso_etaleModuleRestriction_map_extensionByZeroToDirectImage Λ j G
  refine (isZero_cokernel_of_epi (R.map ((etaleModuleExtensionByZeroToDirectImage.{u, 0} Λ j).app
    G))).of_iso ?_
  exact (etaleModuleInverseImageRestrictionIso.{u, 0} Λ j).app _ ≪≫ PreservesCokernel.iso R _

end Stalks

/-- **`c` kills the stalks of `j_* G` and `R¹j_* G` outside `U`.** For an open immersion
`j : U ⟶ Y` and a sheaf `G` of `Λ`-modules on `U_étale`: at every geometric point of `Y` not
lying over a point of `U`, `c` kills the stalks of `j_* G` and of `R¹j_* G`. -/
public def BoundaryStalksKilledBy {Λ : Type} [CommRing Λ] {U Y : Scheme.{u}} (j : U ⟶ Y)
    (G : EtaleModules.{u, 0} Λ U) (c : ℕ) : Prop :=
  ∀ s : GeometricPoint Y, s.hom.base default ∉ Set.range j.base →
    c • 𝟙 (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      ((etaleModuleDirectImage.{u, 0} Λ j).obj G)) = 0 ∧
    c • 𝟙 (((Scheme.pointSmallEtale s.hom).sheafFiber (A := ModuleCat.{u + 1} Λ)).obj
      (((etaleModuleDirectImage.{u, 0} Λ j).rightDerived 1).obj G)) = 0

/-- **The local terms from the stalks at the boundary.** Let `j : U ⟶ Y` be a quasi-compact
open immersion, `N > 0` invertible on `Y` and `G` a sheaf of `ℤ/N`-modules on `U_étale`. If `c`
kills the stalks of `j_* G` and `R¹j_* G` at the geometric points of `Y` outside `U`, then `c`
kills the cokernel of `j_! G ⟶ j_* G` and `R¹j_* G`. -/
theorem localTerms_nsmul_id_eq_zero_of_boundaryStalksKilledBy {N : ℕ} {U Y : Scheme.{u}}
    (j : U ⟶ Y) [IsOpenImmersion j] [QuasiCompact j] (hN0 : 0 < N)
    (hN : IsUnit ((N : ℤ) : Γ(Y, ⊤))) (G : EtaleModules.{u, 0} (ZMod N) U) (c : ℕ)
    (h : BoundaryStalksKilledBy j G c) :
    c • 𝟙 (cokernel ((etaleModuleExtensionByZeroToDirectImage.{u, 0} (ZMod N) j).app G)) = 0 ∧
      c • 𝟙 (((etaleModuleDirectImage.{u, 0} (ZMod N) j).rightDerived 1).obj G) = 0 := by
  constructor
  · refine nsmul_id_eq_zero_of_forall_sheafFiber _ c fun s => ?_
    by_cases hs : s.hom.base default ∈ Set.range j.base
    · exact (isZero_sheafFiber_of_isZero_inverseImage j _
        (isZero_inverseImage_cokernel_extensionByZeroToDirectImage j G) s hs).eq_of_src _ _
    · exact nsmul_id_sheafFiber_cokernel_eq_zero _ c s (h s hs).1
  · refine nsmul_id_eq_zero_of_forall_sheafFiber _ c fun s => ?_
    by_cases hs : s.hom.base default ∈ Set.range j.base
    · have hFa : N • 𝟙 ((etaleModuleForgetAb.{u, 0} (ZMod N) U).obj G) = 0 :=
        Purity.nsmul_id_etaleModuleForgetUniv_zmod G
      have hz : IsZero ((etaleModuleInverseImage.{u, 0} (ZMod N) j).obj
          (((etaleModuleDirectImage.{u, 0} (ZMod N) j).rightDerived 1).obj G)) := by
        refine Purity.isZero_etaleModuleInverseImage_rightDerived_of_ab _ j j G 1 ?_
        exact (Purity.isZero_restriction_rightDerived_of_isOpenImmersion j _
          (fun t a => ⟨N, hN0, hN, Purity.nsmul_eq_zero_stalk_of_nsmul_id hFa t a⟩) 1
          Nat.one_pos).of_iso ((smallEtalePullbackAbIsoEtaleRestriction j).app _)
      exact (isZero_sheafFiber_of_isZero_inverseImage j _ hz s hs).eq_of_src _ _
    · exact (h s hs).2

/-- **`I` is the inertia group of a place at infinity.** For an irreducible scheme `V` with
function field `K`, a separable closure `L` of `K` and a prime `ℓ`: `I` is the inertia group
`P.inertia` of a place `(A, P)` of `K` at infinity — a discrete valuation ring `A` with fraction
field `K` that some global function on `V` is not in, with finite residue field of characteristic
`≠ ℓ`, and a maximal ideal `P` of the integral closure of `A` in `L`. These are the places of
the hypothesis of `Stacks.EtaleCohomology.LAdicSheaf.LocalTermsStalkInput`. -/
public def LAdicSheaf.IsBoundaryInertia (V : Scheme.{u}) [IrreducibleSpace V] (ℓ : ℕ) (L : Type u)
    [Field L] [Algebra (V.residueField (genericPoint V)) L]
    [IsSepClosure (V.residueField (genericPoint V)) L]
    (I : Subgroup Gal(L / V.residueField (genericPoint V))) : Prop :=
  ∃ (A : Type u) (_ : CommRing A) (_ : IsDomain A) (_ : IsDiscreteValuationRing A)
    (_ : Algebra A (V.residueField (genericPoint V)))
    (_ : IsFractionRing A (V.residueField (genericPoint V))) (_ : Algebra A L)
    (_ : IsScalarTower A (V.residueField (genericPoint V)) L)
    (P : Ideal (integralClosure A L)) (_ : P.IsMaximal) (_ : Finite (IsLocalRing.ResidueField A)),
    ℓ ≠ ringChar (IsLocalRing.ResidueField A) ∧
    (∃ a : Γ(V, ⊤), (V.evaluation ⊤ (genericPoint V) trivial).hom a ∉
      Set.range (algebraMap A (V.residueField (genericPoint V)))) ∧
    (letI := IsIntegralClosure.MulSemiringAction A (V.residueField (genericPoint V)) L
      (integralClosure A L)
    P.inertia Gal(L / V.residueField (genericPoint V)) = I)

/-- **The boundary stalks of `ℱ_{ρ₀}` are governed by finitely many inertia groups at infinity**
(the geometric input of `Stacks.EtaleCohomology.LAdicSheaf.LocalTermsStalkInput`, at the
boundary). In the setting of `LocalTermsStalkInput` (a smooth affine curve `V` over a finite
field `k`, a compactification `j : V ⟶ X̄`, `j' : V_k̄ ⟶ X̄_k̄` its base change, a continuous
`ρ₀ : π₁(V, η̄) → GL_r(ℤ_ℓ)`), there are finitely many inertia groups `I₁, …, I_m` of places at
infinity such that, whenever `ℓ ^ e` kills `H⁰(I_i, Mₙ)` and `H¹(I_i, Mₙ)` for all `i` and `n`
(`Stacks.EtaleCohomology.InertiaLevelsKilledBy`), `ℓ ^ e` kills the stalks of `j'_* Gₙ` and of
`R¹j'_* Gₙ` at every geometric point of `X̄_k̄` outside `V_k̄`, for `Gₙ` the levels of `ℱ_{ρ₀}`
on `V_k̄`.

Mathematically: at a geometric point `s̄` of `X̄_k̄ ∖ V_k̄` these stalks are `H⁰` and `H¹` of
`V_k̄ ×_{X̄_k̄} Spec 𝒪^{sh}_{X̄_k̄, s̄} = ∐ Spec K^{sh}_i` (Stacks 03Q9), one field for each branch
of `X̄` at the image of `s̄`, each the fraction field of a strict henselization of a place of `K`
at infinity, with absolute Galois group an inertia group of that place; so they are
`⊕ H⁰(I_P, Mₙ)` and `⊕ H¹(I_P, Mₙ)` (Stacks 03QU). The places at infinity are finitely many, and
the inertia groups of the places over one of them are conjugate. This proposition is not
registered and is not a hypothesis of any registered statement. -/
public def LAdicSheaf.LocalTermsBoundaryStalkInput : Prop :=
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
    (k : Type u) [Field k] [Finite k] (f : V.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar] (p : ℕ) [Fact p.Prime] [CharP k p] (_ : ℓ ≠ p)
    (L Ω : Type u) [Field L] [Field Ω]
    [Algebra (V.1.residueField (genericPoint V.1)) L]
    [IsSepClosure (V.1.residueField (genericPoint V.1)) L]
    [Algebra L Ω] [Algebra (V.1.residueField (genericPoint V.1)) Ω]
    [IsScalarTower (V.1.residueField (genericPoint V.1)) L Ω] [IsAlgClosed Ω]
    [Algebra.IsAlgebraic (V.1.residueField (genericPoint V.1)) Ω]
    (r : ℕ) (ρ₀ : EtaleFundamentalGroup V.1 ((algebraicClosureGeometricPoint
      (V.1.residueField (genericPoint V.1)) Ω).map (V.1.fromSpecResidueField (genericPoint V.1)))
        →* GL (Fin r) ℤ_[ℓ]) (hρ₀ : Continuous ρ₀),
    ∃ (m : ℕ) (I : Fin m → Subgroup Gal(L / V.1.residueField (genericPoint V.1))),
      (∀ i, LAdicSheaf.IsBoundaryInertia V.1 ℓ L (I i)) ∧
      ∀ e : ℕ, (∀ i, InertiaLevelsKilledBy (I i)
          (ρ₀.comp (galoisToFundamentalGroup V.1 L Ω).toMonoidHom) e) →
        ∀ n : ℕ, BoundaryStalksKilledBy (fieldBaseChangeMap j.obj.hom kbar)
          ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (n + 1)))
            (fieldBaseChangeProj (Over.mk f) kbar)).obj
              (LAdicSheaf.etaleLevel B V ℓ (representationLAdicSheaf B V
                ((algebraicClosureGeometricPoint (V.1.residueField (genericPoint V.1)) Ω).map
                  (V.1.fromSpecResidueField (genericPoint V.1)))
                (canonicalFiniteLocallyConstantAbelianSheafEquivalence B V _) ρ₀ hρ₀) n))
          (ℓ ^ e)

/-- **`LocalTermsStalkInput` from the boundary stalks.** The per-place bounds of the hypothesis
give one exponent for each of the finitely many inertia groups of
`Stacks.EtaleCohomology.LAdicSheaf.LocalTermsBoundaryStalkInput`; their maximum `E` works for
all of them (`Stacks.EtaleCohomology.InertiaLevelsKilledBy.mono`), so `ℓ ^ E` kills the boundary
stalks of `j'_* Gₙ` and `R¹j'_* Gₙ` for every `n`, hence the local terms
(`Stacks.EtaleCohomology.localTerms_nsmul_id_eq_zero_of_boundaryStalksKilledBy`, `ℓ` being
invertible on `X̄_k̄`). -/
theorem LAdicSheaf.localTermsStalkInput_of_localTermsBoundaryStalkInput
    (h : LAdicSheaf.LocalTermsBoundaryStalkInput.{u}) : LAdicSheaf.LocalTermsStalkInput.{u} := by
  intro B V ℓ i1 i2 i3 i4 i5 i6 i7 i8 k i9 i10 f i11 i12 i13 i14 j kbar i15 i16 i17 p i18 i19 hℓp
    L Ω i20 i21 i22 i23 i24 i25 i26 i27 i28 r ρ₀ hρ₀ hplace
  obtain ⟨m, I, hI, hbd⟩ := h B V ℓ k f j kbar p hℓp L Ω r ρ₀ hρ₀
  have hex : ∀ i, ∃ e : ℕ, InertiaLevelsKilledBy (I i)
      (ρ₀.comp (galoisToFundamentalGroup V.1 L Ω).toMonoidHom) e := by
    intro i
    obtain ⟨A, _, _, _, _, _, _, _, P, _, _, hℓA, hA, hIP⟩ := hI i
    obtain ⟨e, he⟩ := hplace A P hℓA hA
    exact ⟨e, hIP ▸ he⟩
  choose e he using hex
  refine ⟨Finset.univ.sup e, fun n => ?_⟩
  have hb := hbd (Finset.univ.sup e)
    (fun i => (he i).mono (Finset.le_sup (Finset.mem_univ i))) n
  have := Fintype.ofFinite k
  have : IsOpenImmersion j.obj.hom.left := j.property.1
  have : IsOpenImmersion (fieldBaseChangeMap j.obj.hom kbar) :=
    have : MorphismProperty.IsStableUnderComposition @IsOpenImmersion.{u} :=
      MorphismProperty.IsMultiplicative.toIsStableUnderComposition
    MorphismProperty.pullbackMap (P := @IsOpenImmersion)
      (inferInstanceAs (IsOpenImmersion j.obj.hom.left))
      (inferInstanceAs (IsOpenImmersion (𝟙 _))) (Over.w j.obj.hom).symm (Category.id_comp _).symm
  have : TopologicalSpace.NoetherianSpace (Over.mk f).left :=
    inferInstanceAs (TopologicalSpace.NoetherianSpace V.1)
  have : QuasiCompact j.obj.hom.left := quasiCompact_of_noetherianSpace_source _
  have : QuasiCompact (fieldBaseChangeMap j.obj.hom kbar) :=
    MorphismProperty.of_isPullback (isPullback_fieldBaseChangeMap j.obj.hom kbar).flip ‹_›
  have : CharP kbar p := charP_of_injective_algebraMap (algebraMap k kbar).injective p
  have hℓk : IsUnit ((ℓ ^ (n + 1) : ℕ) : kbar) := by
    refine isUnit_iff_ne_zero.2 ?_
    rw [Nat.cast_pow]
    refine pow_ne_zero _ fun h0 => hℓp ?_
    have hdvd := (CharP.cast_eq_zero_iff kbar p ℓ).1 h0
    exact ((Nat.prime_dvd_prime_iff_eq (Fact.out : p.Prime) (Fact.out : ℓ.Prime)).1 hdvd).symm
  have hN : IsUnit (((ℓ ^ (n + 1) : ℕ) : ℤ) : Γ(fieldBaseChange j.obj.right kbar, ⊤)) := by
    exact_mod_cast Purity.isUnit_natCast_globalSections_of_over
      (pullback.snd j.obj.right.hom (specAlgebraMap k kbar)) hℓk
  exact localTerms_nsmul_id_eq_zero_of_boundaryStalksKilledBy
    (fieldBaseChangeMap j.obj.hom kbar) (pow_pos (Fact.out : ℓ.Prime).pos _) hN _ _ hb

end Stacks.EtaleCohomology

end
