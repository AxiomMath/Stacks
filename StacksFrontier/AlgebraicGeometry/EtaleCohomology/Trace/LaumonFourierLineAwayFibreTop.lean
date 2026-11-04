module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineAwayFibreOffTop
public import
  StacksFrontier.AlgebraicGeometry.EtaleCohomology.FourierDeligne.FourierGenericCoinvariantFibreSplit

/-!
# The top degree of the fibres of the Fourier family away from `a = 0`

With the notation of `Stacks.EtaleCohomology.LaumonFourierLineAwayFibreVanishing`, the vanishing of
`H²_c` of the level zero `K₀` of the Fourier family on the geometric fibres `𝔸¹_Ω` of
`U' ⟶ V'` (`Stacks.EtaleCohomology.LaumonFourierLineAwayFibreTopVanishing`) splits into

* **the curve half** `Stacks.EtaleCohomology.AffineLineOpenTopCohomologyVanishingInput`, shared with
  the generic coinvariant vanishing (L2) of the Fourier transform: on an open of `𝔸¹_Ω`, `H²_c` of a
  locally constant sheaf with finite values and no constant simple quotient vanishes, `H²_c` being
  the Tate twisted coinvariants of the monodromy;
* **the inertia half** `Stacks.EtaleCohomology.LaumonFourierLineAwayFibreNoConstantQuotient`: the
  restriction to `𝔸¹_Ω` of the level zero of the flat model, a locally constant sheaf of
  `ℤ/ℓ`-modules, has no constant simple quotient; for `a ≠ 0` and `n` large prime to `p`, the
  inertia at `∞` acts on it without coinvariants, all the slopes being `n`.

`K₀` is the restriction of scalars along `ℤ_ℓ ⟶ ℤ/ℓ` of the level zero read on Mathlib's small
étale site, `Rf_!` commutes with restriction of scalars, and the fibre is `𝔸¹_Ω`
(`Stacks.EtaleCohomology.laumonFourierLineAwayFibreTopVanishing_of_halves`). With
`Stacks.EtaleCohomology.laumonFourierLineAwayFibreVanishing_of_top` this proves
`Stacks.EtaleCohomology.LaumonFourierLineAwayFibreVanishing`, in Laumon's local theory of the
Fourier transform in the proof of [Tag 03VH](https://stacks.math.columbia.edu/tag/03VH).

## Main definitions

* `Stacks.EtaleCohomology.LaumonFourierLineAwayFibreNoConstantQuotient`.

## Main results

* `Stacks.EtaleCohomology.isZero_of_forall_compactificationOf_of_eq`.
* `Stacks.EtaleCohomology.laumonFourierLineAwayFibreTopVanishing_of_halves`.
* `Stacks.EtaleCohomology.laumonFourierLineAwayFibreVanishing_of_halves`.

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

/-- A property of all compactifications of `g` holds for every compactification of `f = g`. -/
theorem isZero_of_forall_compactificationOf_of_eq {X Y : Scheme.{u}} {f g : X ⟶ Y}
    (P : ∀ h : X ⟶ Y, CompactificationOf (Over.mk h) → Prop) (hgf : g = f)
    (h : ∀ jc : CompactificationOf (Over.mk g), P g jc) (j : CompactificationOf (Over.mk f)) :
    P f j := by
  subst hgf
  exact h j

section Family

attribute [local instance] etaleModuleInverseImage_preservesFiniteLimits
  etaleModuleInverseImage_preservesFiniteColimits moduleCat_hasLimitsOfSize
  SmallEtale.hasWeakSheafify_over_moduleCat_ring
  SmallEtale.isRightAdjoint_smallEtalePushforward_moduleCat_ring

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

/-- **The inertia half of the top degree of the fibres of the Fourier family, for `a ≠ 0`**: with
the data of `Stacks.EtaleCohomology.LaumonFourierLineAwayFibreVanishing`, the restriction to the
geometric fibre of `g'` at every point `y` of `V'` of the level zero of the flat model of the
Fourier family, as a sheaf of `ℤ/ℓ`-modules on Mathlib's small étale site, has no constant
simple quotient. -/
public def LaumonFourierLineAwayFibreNoConstantQuotient : Prop :=
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
    ∀ (y : V'.1), HasNoConstantSimpleQuotient (ZMod (ℓ ^ (0 + 1)))
      ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (0 + 1)))
        (pullback.fst (B.inclusion.map g') (GeometricPoint.ofPoint V'.1 y).hom)).obj
        ((etaleModuleInverseImage.{u, 0} (ZMod (ℓ ^ (0 + 1))) (B.inclusion.map jU)).obj
          (LAdicSheaf.etaleLevel B _ ℓ (LAdicSheaf.flatModel B ℓ
            (laumonFourierFamilySheaf k' B hS b
              (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _
                hσ₁).toLAdicSheaf) 0)))

omit [Fintype k] in
/-- **`H²_c` of the fibres of the Fourier family vanishes, from the curve half and the inertia
half**: `K₀` restricted to the fibre `𝔸¹_Ω` is the restriction of scalars along `ℤ_ℓ ⟶ ℤ/ℓ` of
a locally constant sheaf of `ℤ/ℓ`-modules with finite values and no constant simple quotient,
whose `H²_c` vanishes by the curve half. -/
theorem laumonFourierLineAwayFibreTopVanishing_of_halves
    (hC : AffineLineOpenTopCohomologyVanishingInput.{u})
    (hN : LaumonFourierLineAwayFibreNoConstantQuotient B U ℓ k e x E b σ ψ n) :
    LaumonFourierLineAwayFibreTopVanishing B U ℓ k e x E b σ ψ n := by
  intro k' _ _ _ a ha hS hL z hz pz hσ₁ V' U' _ _ jV' jU g' _ _ _ jg' hopen hpb
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  intro y
  have hNy := hN k' a ha hS hL z hz pz hσ₁ V' U' jV' jU g' jg' hopen hpb y
  let s := (GeometricPoint.ofPoint V'.1 y).hom
  let Ω := (GeometricPoint.ofPoint V'.1 y).residueField
  let G' := B.inclusion.map g'
  let f' := pullback.snd G' s
  let u' := pullback.fst G' s
  let Λ₀ := ZMod (ℓ ^ (0 + 1))
  let ρ : ℤ_[ℓ] →+* Λ₀ := PadicInt.toZModPow (0 + 1)
  let L := (laumonFourierFamilySheaf k' B hS b
    (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _ hσ₁).toLAdicSheaf
  let L' := LAdicSheaf.flatModel B ℓ L
  let X₂ := Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS
  let K₀ := towerObj (LAdicSheaf.padicTower B X₂ ℓ L') 0
  let A := (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)).obj K₀
  let F := (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] u').obj A
  let N₀ := LAdicSheaf.etaleLevel B X₂ ℓ L' 0
  let N := (etaleModuleInverseImage.{u, 0} Λ₀ u').obj
    ((etaleModuleInverseImage.{u, 0} Λ₀ (B.inclusion.map jU)).obj N₀)
  let j' := jg'.baseChange (IsPullback.of_hasPullback G' s)
  have hL : L.IsLisse := isLisse_laumonFourierFamilySheaf k' B hS b _ n a z pz _ hσ₁
  have hL' : L'.IsLisse := LAdicSheaf.isLisse_flatModel B ℓ L hL
  -- `F` is the restriction of scalars of `N`
  let eK : K₀ ≅ (etaleModuleRestrictScalars ρ X₂.1).obj N₀ :=
    ((sheafEquivRestrictScalarsIso B X₂.1 X₂.property ρ).app (L'.level 0)).symm
  let eF : F ≅ (etaleModuleRestrictScalars ρ _).obj N :=
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] u').mapIso
      ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)).mapIso eK ≪≫
        (etaleModuleInverseImageRestrictScalars ρ (B.inclusion.map jU)).app N₀) ≪≫
      (etaleModuleInverseImageRestrictScalars ρ u').app _
  let eS := (Stacks.DerivedFunctor.exactMapDerivedCategoryPlusSingle
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] u') 0).app A
  obtain ⟨eR⟩ := nonempty_homology_derivedLowerShriek_restrictScalars_iso ρ f' j' N 2
  refine IsZero.of_iso ?_ ((DerivedCategory.Plus.homologyFunctor _ 2).mapIso
    ((derivedLowerShriek.{u, 0} f' j' ℤ_[ℓ]).mapIso
      (eS ≪≫ (DerivedCategory.Plus.singleFunctor _ 0).mapIso eF)) ≪≫ eR)
  refine Functor.map_isZero _ ?_
  -- the curve half on the fibre `𝔸¹_Ω`
  obtain ⟨eA, heA⟩ := exists_laumonFamilyFibre_affineSpace_iso hpb s
  have : IrreducibleSpace (AffineSpace (ULift.{u} (Fin 1)) (Spec (.of Ω))) := inferInstance
  have : Nonempty ↥(pullback G' s) := ⟨eA.inv.base (Classical.arbitrary _)⟩
  have hN₀ := (SmallEtale.isFiniteTypeLocallyConstant_sheafEquiv_functor_iff B X₂ Λ₀
    (L'.level 0)).2 (LAdicSheaf.isFiniteTypeLocallyConstant_level_of_isLisse L' hL' 0)
  have hNlc : Stacks.ConstantSheaf.IsLocallyConstantWith Λ₀ (pullback G' s).smallEtaleTopology
      (fun E => Module.Finite Λ₀ E) N :=
    isLocallyConstantWith_of_imp Λ₀ (fun E hE => (ModuleCat.isFG_iff E).1 hE)
      (isLocallyConstantWith_inverseImage Λ₀ _ u'
        (isLocallyConstantWith_inverseImage Λ₀ _ (B.inclusion.map jU) hN₀))
  exact isZero_of_forall_compactificationOf_of_eq
    (fun h jc => IsZero ((DerivedCategory.Plus.homologyFunctor _ 2).obj
      ((derivedLowerShriek.{u, 0} h jc Λ₀).obj ((DerivedCategory.Plus.singleFunctor _ 0).obj N))))
    (Category.id_comp f') (hC Ω Λ₀ f' ⟨eA, heA⟩ (𝟙 _) N hNlc hNy) j'

/-- **The fibres of the Fourier family have no `H^q_c`, `q ≠ 1`, from the curve half and the
inertia half.** -/
theorem laumonFourierLineAwayFibreVanishing_of_halves
    (hC : AffineLineOpenTopCohomologyVanishingInput.{u})
    (hN : LaumonFourierLineAwayFibreNoConstantQuotient B U ℓ k e x E b σ ψ n) :
    LaumonFourierLineAwayFibreVanishing B U ℓ k e x E b σ ψ n :=
  laumonFourierLineAwayFibreVanishing_of_top B U ℓ k e x E b σ ψ n
    (laumonFourierLineAwayFibreTopVanishing_of_halves B U ℓ k e x E b σ ψ n hC hN)

end Family

end Stacks.EtaleCohomology

end
