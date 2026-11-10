module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineAwayFibre
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonOriginFibreScheme
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LAdicFiniteEtaleDirectImageRealizable
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageTopGysinMorphismShriek
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.RepresentationCommutantCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.CompactSupportDegreeZeroLisse
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformAmplitude
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierTransformDegreeZero
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.LocallyConstantTensor
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedLowerShriek.ChangeOfRings
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleSheaves.RestrictionOfScalarsNoncomm
public import StacksFrontier.AlgebraicGeometry.ProjectiveCurve.Basic

/-!
# The fibres of the Fourier family away from `a = 0`, off the top degree

Let `K₀` be the level zero of the flat model of the Fourier family
`pr₁^*ℱ_σ ⊗ L_ψ'(a xⁿ + x t)` on `Spec k'[x][t]`, `U' = pr₂⁻¹(V')` for an open `V'` of the
`t`-line, and `ȳ` the geometric point at an algebraic closure `Ω` of the residue field of a point
`y` of `V'`. The fibre of `U' → V'` at `ȳ` is the affine line `𝔸¹_Ω`
(`Stacks.EtaleCohomology.exists_laumonFamilyFibre_affineSpace_iso`), and `K₀` restricts to a
locally constant sheaf on it. Hence `H^q_c(𝔸¹_Ω, K₀) = 0`

* for `q < 0`, `Rf_!` having amplitude `≥ 0`;
* for `q = 0`, a locally constant sheaf on a connected non-proper curve having no compactly
  supported sections
  (`Stacks.EtaleCohomology.isZero_homology_zero_derivedLowerShriek_of_isLocallyConstantWith`);
* for `q ≥ 3`, `K₀` being killed by `ℓ` and `𝔸¹_Ω` a curve
  (`Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_two_mul_lt_of_pow_nsmul_eq_zero`,
  the absolute case of [Stacks, Tag 095U] after restricting the scalars to `ℤ/ℓᴺ`).

So `Stacks.EtaleCohomology.LaumonFourierLineAwayFibreVanishing` reduces to the degree two
(`Stacks.EtaleCohomology.LaumonFourierLineAwayFibreTopVanishing`,
`Stacks.EtaleCohomology.laumonFourierLineAwayFibreVanishing_of_top`), in Laumon's local theory of
the Fourier transform in the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.LaumonFourierLineAwayFibreTopVanishing`.

## Main results

* `Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_two_mul_lt_of_pow_nsmul_eq_zero`.
* `Stacks.EtaleCohomology.exists_laumonFamilyFibre_affineSpace_iso`.
* `Stacks.EtaleCohomology.LAdicSheaf.isFiniteTypeLocallyConstant_padicTower_obj`.
* `Stacks.EtaleCohomology.laumonFourierLineAwayFibreVanishing_of_top`.

## Implementation notes

`Stacks.EtaleCohomology.derivedLowerShriek` lives in the standard model
`HasDerivedCategory.standard` of the derived category, hence so do the statements here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
open CategoryTheory.LAdicTower

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-! ### `H^q_c` above twice the dimension, for `ℤ_ℓ`-coefficients -/

section PadicCoefficients

attribute [local instance] moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

/-- **`Hⁱ(Rf_!(G[0])) = 0` for `i > 2 dim X` over a separably closed field**, for a sheaf `G` of
`ℤ_ℓ`-modules killed by `ℓᴺ`: `G` is the restriction of scalars of a sheaf of
`ℤ/ℓᴺ`-modules (its coextension of scalars), `Rf_!` commutes with restriction of scalars, and over
the finite ring `ℤ/ℓᴺ` this is
`Stacks.EtaleCohomology.isZero_homology_derivedLowerShriek_of_two_mul_lt`. -/
theorem isZero_homology_derivedLowerShriek_of_two_mul_lt_of_pow_nsmul_eq_zero (ℓ : ℕ)
    [Fact ℓ.Prime] (N : ℕ) (Ω : Type u) [Field Ω] [IsSepClosed Ω] {X : Scheme.{u}}
    (f : X ⟶ Spec (.of Ω)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
    (j : CompactificationOf (Over.mk f)) (n : ℕ) (hX : topologicalKrullDim X ≤ n)
    (G : EtaleModules.{u, 0} ℤ_[ℓ] X) (hG : ℓ ^ N • 𝟙 G = 0) (i : ℤ) (hi : 2 * (n : ℤ) < i) :
    IsZero ((DerivedCategory.Plus.homologyFunctor _ i).obj
      ((derivedLowerShriek.{u, 0} f j ℤ_[ℓ]).obj
        ((DerivedCategory.Plus.singleFunctor _ 0).obj G))) := by
  obtain ⟨p, rfl⟩ : ∃ p : ℕ, i = p := ⟨i.toNat, by omega⟩
  have : NeZero (ℓ ^ N) := ⟨pow_ne_zero _ (Fact.out : ℓ.Prime).ne_zero⟩
  let ρ : ℤ_[ℓ] →+* ZMod (ℓ ^ N) := PadicInt.toZModPow N
  have hρ : Function.Surjective ρ := ZMod.ringHom_surjective ρ
  have hker : ∀ (V : X.Etaleᵒᵖ), ∀ a ∈ RingHom.ker ρ, ∀ x : G.obj.obj V, a • x = 0 := by
    intro V a ha x
    rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at ha
    obtain ⟨c, rfl⟩ := ha
    have hx : (ℓ ^ N) • x = 0 := by
      rw [← etaleModules_map_nsmul_id_apply ℤ_[ℓ] G (ℓ ^ N) V x, hG, Functor.map_zero]
      rfl
    rw [mul_comm, mul_smul, show ((ℓ : ℤ_[ℓ]) ^ N) = ((ℓ ^ N : ℕ) : ℤ_[ℓ]) by push_cast; rfl,
      Nat.cast_smul_eq_nsmul, hx, smul_zero]
  let G' := (etaleModuleCoextendScalars ρ X).obj G
  let ε : (etaleModuleRestrictScalars ρ X).obj G' ≅ G :=
    etaleModuleRestrictCoextendScalarsIso ρ hρ G hker
  obtain ⟨e⟩ := nonempty_homology_derivedLowerShriek_restrictScalars_iso ρ f j G' p
  have h0 := isZero_homology_derivedLowerShriek_of_two_mul_lt (ZMod (ℓ ^ N)) Ω f j n hX G' p hi
  exact ((etaleModuleRestrictScalars ρ (Spec (.of Ω))).map_isZero h0).of_iso
    ((DerivedCategory.Plus.homologyFunctor _ (p : ℤ)).mapIso
      ((derivedLowerShriek.{u, 0} f j ℤ_[ℓ]).mapIso
        ((DerivedCategory.Plus.singleFunctor _ 0).mapIso ε.symm)) ≪≫ e)

end PadicCoefficients

/-! ### The geometric fibres of `pr₂` over an open of the `t`-line -/

section Geometry

variable {k' : Type u} [Field k'] {B : BigEtaleSite.{u}}
  {hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k'))))}
  {hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k')))} {V' U' : B.Scheme}
  {jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL}
  {jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS} {g' : U' ⟶ V'}

/-- **The fibre of `U' = pr₂⁻¹(V') ⟶ V'` along any `s : T ⟶ V'` is `𝔸¹_T`**, over `T`: `pr₂` is
the base change of `𝔸¹_{k'} ⟶ Spec k'` along the `t`-line. -/
theorem exists_laumonFamilyFibre_affineSpace_iso
    (hU : IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV'))
    {T : Scheme.{u}} (s : T ⟶ V'.1) :
    ∃ e : pullback (B.inclusion.map g') s ≅ AffineSpace (ULift.{u} (Fin 1)) T,
      e.hom ≫ (AffineSpace (ULift.{u} (Fin 1)) T ↘ T) = pullback.snd (B.inclusion.map g') s := by
  have P := isPullback_SpecMap_of_isPushout _ _ _ _ (isPushout_C_mapRingHom_C k')
  have S := ((IsPullback.of_hasPullback (B.inclusion.map g') s).paste_horiz hU).paste_horiz P
  exact ⟨S.isoIsPullback _ _ (isPullback_affineLineBaseChange_of_hom k' _),
    IsPullback.isoIsPullback_hom_snd _ _ _ _⟩

/-- **The geometric fibres of `U' ⟶ V'` are connected, not proper, and of dimension at most one**:
they are affine lines. -/
theorem laumonFamilyFibre_connectedSpace_not_isProper_dim
    (hU : IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV'))
    (Ω : Type u) [Field Ω] (s : Spec (.of Ω) ⟶ V'.1) :
    ConnectedSpace ↥(pullback (B.inclusion.map g') s) ∧
      ¬ IsProper (pullback.snd (B.inclusion.map g') s) ∧
      topologicalKrullDim ↥(pullback (B.inclusion.map g') s) ≤ ((1 : ℕ) : WithBot ℕ∞) := by
  obtain ⟨e, he⟩ := exists_laumonFamilyFibre_affineSpace_iso hU s
  have : IrreducibleSpace (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω))) := inferInstance
  refine ⟨?_, fun hP => ?_, ?_⟩
  · let h := Scheme.homeoOfIso e.symm
    exact h.surjective.connectedSpace h.continuous
  · have := hP
    refine not_isProper_affineSpace Ω (ULift.{u} (Fin 1)) ?_
    rw [← (Iso.inv_comp_eq e).2 he.symm]
    infer_instance
  · rw [IsHomeomorph.topologicalKrullDim_eq _ (Scheme.homeoOfIso e).isHomeomorph]
    calc topologicalKrullDim (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω)))
        = topologicalKrullDim (PrimeSpectrum (MvPolynomial (ULift.{u} (Fin 1)) Ω)) :=
          IsHomeomorph.topologicalKrullDim_eq _
            (TopCat.homeoOfIso (Scheme.forgetToTop.mapIso
              (AffineSpace.SpecIso (ULift.{u} (Fin 1)) (CommRingCat.of Ω)))).isHomeomorph
      _ = ringKrullDim (MvPolynomial (ULift.{u} (Fin 1)) Ω) :=
          PrimeSpectrum.topologicalKrullDim_eq_ringKrullDim _
      _ = ringKrullDim Ω + Nat.card (ULift.{u} (Fin 1)) :=
          MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite
      _ ≤ ((1 : ℕ) : WithBot ℕ∞) := by simp

end Geometry

/-! ### The levels of a lisse sheaf as sheaves of `ℤ_ℓ`-modules -/

section Levels

variable {B : BigEtaleSite.{u}} {ℓ : ℕ} [Fact ℓ.Prime]
  [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.obj T.property),
    HasWeakSheafify ((SmallEtale.topology B T.obj T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.obj T.property)
    (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]

/-- **The levels of a lisse ℓ-adic sheaf, as sheaves of `ℤ_ℓ`-modules on Mathlib's small étale
site, are locally constant of finite type**: restriction of scalars along the surjection
`ℤ_ℓ ⟶ ℤ/ℓⁿ⁺¹` keeps a level locally constant of finite type, and the comparison of the two
small étale sites preserves the condition. -/
theorem LAdicSheaf.isFiniteTypeLocallyConstant_padicTower_obj {X : B.Scheme} [IsNoetherian X.1]
    (G : LAdicSheaf.{u, u + 1} B X ℓ) (hG : G.IsLisse) (n : ℕ) :
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ] X.1.smallEtaleTopology
      (towerObj (LAdicSheaf.padicTower B X ℓ G) n) := by
  let f : ℤ_[ℓ] →+* ZMod (ℓ ^ (n + 1)) := PadicInt.toZModPow (n + 1)
  have hf : Function.Surjective f := ZMod.ringHom_surjective f
  have h2 := isFiniteTypeLocallyConstant_restrictScalarsSheafNoncomm.{u + 1} f
    (SmallEtale.topology B X.1 X.property) (fun E hE => by
      rw [ModuleCat.isFG_iff] at hE ⊢
      let _ : Algebra ℤ_[ℓ] (ZMod (ℓ ^ (n + 1))) := f.toAlgebra
      let _ : Module ℤ_[ℓ] E := ((ModuleCat.restrictScalars.{u + 1} f).obj E).isModule
      have : IsScalarTower ℤ_[ℓ] (ZMod (ℓ ^ (n + 1))) E := .of_algebraMap_smul fun _ _ => rfl
      have : Module.Finite ℤ_[ℓ] (ZMod (ℓ ^ (n + 1))) :=
        Module.Finite.of_surjective (Algebra.linearMap ℤ_[ℓ] (ZMod (ℓ ^ (n + 1)))) hf
      exact Module.Finite.trans (ZMod (ℓ ^ (n + 1))) E) (G.level n)
    (LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse G hG n)
  exact (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B X ℤ_[ℓ] _).2 h2

end Levels

/-- **The Fourier family sheaf is lisse**: it is the sheaf of a continuous representation. -/
theorem isLisse_laumonFourierFamilySheaf (k' : Type u) [Field k'] [Fintype k']
    (B : BigEtaleSite.{u}) (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    {ℓ : ℕ} [Fact ℓ.Prime] {E : Type} [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E) (n : ℕ) (a : k')
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
    {m : ℕ}
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁)) :
    (laumonFourierFamilySheaf k' B hS b ψ' n a z p₀ σ₁ hσ₁).toLAdicSheaf.IsLisse := by
  unfold laumonFourierFamilySheaf restrictScalarsRepCoefficientSheaf
  rw [representationSheafCommutantCoefficientSheaf_toLAdicSheaf]
  exact LAdicSheaf.representationSheaf_isLisse _ _ _ _ _

/-! ### The fibres of the Fourier family off the top degree -/

section Family

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits

variable (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
  [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
    ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
      (SmallEtale.topology B S.1 S.property)
      (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
  [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
    HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
  [Fact ℓ.Prime] [ConnectedSpace U.1]
  (k : Type u) [Field k] [Fintype k] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsIso e]
  (x : GeometricPoint U.1) (E : Type) [Field E] [Algebra ℚ_[ℓ] E] {d : ℕ}
  (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
  (ψ : AddChar k E) (n : ℕ)

/-- **The top degree of the fibres of the level zero of the Fourier family, for `a ≠ 0`**: with
the data of `Stacks.EtaleCohomology.LaumonFourierLineAwayFibreVanishing`, `H²_c` of the
restriction of `K₀` to the geometric fibre of `g'` at every point `y` of `V'` vanishes (no
coinvariants of the inertia at `∞`, where all the slopes equal `n > 1`). -/
public def LaumonFourierLineAwayFibreTopVanishing : Prop :=
  ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k'] (a : k'), a ≠ 0 →
    ∀ (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
      (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
    (pz : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonFourierKernel k' n a)))
    (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
      (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
        (z.map (laumonFamilyPr₁ k'))).toMonoidHom))))
    (V' U' : B.Scheme) [IsNoetherian V'.1] [IsNoetherian U'.1]
    (jV' : V' ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
    (jU : U' ⟶ Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) (g' : U' ⟶ V')
    [LocallyOfFiniteType (B.inclusion.map g')] [QuasiCompact (B.inclusion.map g')]
    [IsSeparated (B.inclusion.map g')] (jg' : CompactificationOf (Over.mk (B.inclusion.map g'))),
    IsOpenImmersion (B.inclusion.map jV') →
    IsPullback (B.inclusion.map jU) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k' B hS hL)) (B.inclusion.map jV') →
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
    ∀ (y : V'.1), IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0}
        (pullback.snd (B.inclusion.map g') (GeometricPoint.ofPoint V'.1 y).hom)
        (jg'.baseChange (IsPullback.of_hasPullback (B.inclusion.map g')
          (GeometricPoint.ofPoint V'.1 y).hom)) ℤ_[ℓ]).obj
        ((etaleModuleDerivedInverseImagePlus.{u, 0} ℤ_[ℓ]
          (pullback.fst (B.inclusion.map g') (GeometricPoint.ofPoint V'.1 y).hom)).obj
          ((DerivedCategory.Plus.singleFunctor _ 0).obj
            ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)).obj
              (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
            (laumonFourierFamilySheaf k' B hS b
              (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _
                hσ₁).toLAdicSheaf)) 0))))))

omit [Fintype k] in
/-- **The fibres of the level zero of the Fourier family have no `H^q_c`, `q ≠ 1`, as soon as
they have no `H²_c`**: the geometric fibre of `g'` at `y` is the affine line `𝔸¹_Ω`, connected,
not proper and of dimension one, on which the restriction of `K₀` is locally constant and killed
by `ℓ`. -/
theorem laumonFourierLineAwayFibreVanishing_of_top
    (H : LaumonFourierLineAwayFibreTopVanishing B U ℓ k e x E b σ ψ n) :
    LaumonFourierLineAwayFibreVanishing B U ℓ k e x E b σ ψ n := by
  intro k' _ _ _ a ha hS hL z hz pz hσ₁ V' U' _ _ jV' jU g' _ _ _ jg' hopen hpb
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  intro y q hq
  obtain rfl | h2 := eq_or_ne q 2
  · exact H k' a ha hS hL z hz pz hσ₁ V' U' jV' jU g' jg' hopen hpb y
  let s := (GeometricPoint.ofPoint V'.1 y).hom
  let Ω := (GeometricPoint.ofPoint V'.1 y).residueField
  let G' := B.inclusion.map g'
  let f' := pullback.snd G' s
  let u' := pullback.fst G' s
  let L := (laumonFourierFamilySheaf k' B hS b
    (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _ hσ₁).toLAdicSheaf
  let K₀ := towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ L)) 0
  let A := (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)).obj K₀
  let F := (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] u').obj A
  let j' := jg'.baseChange (IsPullback.of_hasPullback G' s)
  have hK₀ := LAdicSheaf.isFiniteTypeLocallyConstant_padicTower_obj (LAdicSheaf.flatModel B ℓ L)
    (LAdicSheaf.isLisse_flatModel B ℓ L
      (isLisse_laumonFourierFamilySheaf k' B hS b _ n a z pz _ hσ₁)) 0
  have hF : Stacks.ConstantSheaf.IsLocallyConstantWith ℤ_[ℓ] (pullback G' s).smallEtaleTopology
      (ModuleCat.isFG ℤ_[ℓ]) F :=
    isLocallyConstantWith_inverseImage ℤ_[ℓ] _ u'
      (isLocallyConstantWith_inverseImage ℤ_[ℓ] _ (B.inclusion.map jU) hK₀)
  have hF1 : ℓ ^ 1 • 𝟙 F = 0 := by
    have hK : ℓ ^ (0 + 1) • 𝟙 K₀ = 0 := LAdicSheaf.pow_nsmul_id_padicTower_obj B ℓ _ 0
    change ℓ ^ 1 • 𝟙 ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] u').obj
      ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)).obj K₀)) = 0
    rw [← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_nsmul,
      ← CategoryTheory.Functor.map_id, ← CategoryTheory.Functor.map_nsmul, hK,
      CategoryTheory.Functor.map_zero, CategoryTheory.Functor.map_zero]
  let eS := (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] u') 0).app A
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ q).mapIso
    ((derivedLowerShriek.{u, 0} f' j' ℤ_[ℓ]).mapIso eS))
  change IsZero ((DerivedCategory.Plus.homologyFunctor _ q).obj
    ((derivedLowerShriek.{u, 0} f' j' ℤ_[ℓ]).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj F)))
  obtain ⟨hconn, hnp, hdim⟩ := laumonFamilyFibre_connectedSpace_not_isProper_dim hpb Ω s
  rcases lt_trichotomy q 0 with hq0 | rfl | hq0
  · have := isGE_derivedLowerShriek_obj ℤ_[ℓ] f' j'
      ((DerivedCategory.Plus.singleFunctor _ 0).obj F) 0
    exact DerivedCategory.Plus.isZero_homology_of_isGE _ 0 q hq0
  · have := hconn
    exact isZero_homology_zero_derivedLowerShriek_of_isLocallyConstantWith ℤ_[ℓ] _ Ω f' j'
      (j'.not_isClosed_range_immersion_of_not_isProper hnp) F hF
  · exact isZero_homology_derivedLowerShriek_of_two_mul_lt_of_pow_nsmul_eq_zero ℓ 1 Ω f' j' 1
      hdim F hF1 q (by omega)

end Family

end Stacks.EtaleCohomology

end
