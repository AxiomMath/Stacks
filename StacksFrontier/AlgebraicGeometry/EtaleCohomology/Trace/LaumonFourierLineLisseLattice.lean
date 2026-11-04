module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFourierLineLisseLocalTheory
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LowerShriekLocallyConstantClosure
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonPlaneFieldExtension

/-!
# Laumon's local theory of the Fourier family, with the lattices handled explicitly

The two inputs of `Stacks.EtaleCohomology.laumonFourierLineLisseInput_of_away_zero`
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) ask that `G_V = R¹g'_!(K|_{U'})` be lisse,
`K = pr₁^*ℱ_σ ⊗ L_ψ'(a xⁿ + x t)` the Fourier family over a finite extension `k'` of `k`.
The lattice of `K` is the one chosen for the representation over `k'`
(`Stacks.EtaleCohomology.exists_conj_integral`), only isogenous to the pullback of a lattice over
`k`, and lisseness of an ℓ-adic sheaf is not invariant under isogeny. This file isolates exactly
where the lattice enters: `Rʳ g'_! G` is lisse as soon as all the `Rˢ g'_!` of the level zero `K₀`
of the flat model of `K` (a sheaf killed by `ℓ`) are locally constant of finite type
(`Stacks.EtaleCohomology.LAdicSheaf.isLisse_higherDirectImageShriek_of_levelZero`), and these form
a class closed under extensions and summands.

* **`a = 0`** (`Stacks.EtaleCohomology.laumonFourierLineLisseZeroInput_of_lattice`): it suffices
  that finitely many constructible sheaves `Qᵢ` on `Spec k[x][t]` killed by `ℓ` generate, under
  extensions and summands, the level zero `K₀` of every `k'`-family on the line `a = 0` from their
  pullbacks to `Spec k'[x][t]` (`Stacks.EtaleCohomology.LaumonFourierZeroLatticeInput`: the `Qᵢ`
  are the simple constituents of the reduction of a lattice of the family over `k`; the
  constituents of `K₀` are those of the pullback by Brauer–Nesbitt, and the pullback of a simple
  constituent is semisimple by Clifford's theorem, `π₁(𝔸²_{k'})` being normal of finite index in
  `π₁(𝔸²_k)`). Then the generic local constancy over `k` of the `Rˢ pr₂! Qᵢ`
  (`Stacks.EtaleCohomology.exists_ne_zero_forall_isFiniteTypeLocallyConstant_lowerShriekHomology`,
  Tag 0GL0) gives one `D₀ ∈ k[t]`, and proper base change along `Spec k'[t] → Spec k[t]`
  (`Stacks.EtaleCohomology.isPullback_laumonPlaneFieldExtension`, Tag 0F7L) makes it work over
  every `k'` and for every lattice.
* **`a ≠ 0`** (`Stacks.EtaleCohomology.laumonFourierLineLisseAwayInput_of_levelZero`): it suffices
  that the `Rˢ g'_!` of the level zero be locally constant
  (`Stacks.EtaleCohomology.LaumonFourierLineAwayLevelZeroInput`): Laumon's local theory with
  coefficients killed by `ℓ`, for which the slopes at `∞` are those of the ℓ-adic sheaf (the wild
  inertia is pro-`p`), so that the statement concerns every lattice at once.

## Main definitions

* `Stacks.EtaleCohomology.laumonPlaneFieldExtensionHom`,
  `Stacks.EtaleCohomology.laumonLineFieldExtensionHom`.
* `Stacks.EtaleCohomology.LaumonFourierZeroLatticeInput`.
* `Stacks.EtaleCohomology.LaumonFourierLineAwayLevelZero`,
  `Stacks.EtaleCohomology.LaumonFourierLineAwayLevelZeroInput`.

## Main results

* `Stacks.EtaleCohomology.laumonFourierLineLisseZeroInput_of_lattice`.
* `Stacks.EtaleCohomology.laumonFourierLineLisseAwayInput_of_levelZero`.

## Implementation notes

`Stacks.EtaleCohomology.lowerShriekHomology` lives in the standard model
`HasDerivedCategory.standard` of the derived category, hence so do the statements here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry AlgebraicGeometry.SmallEtale Matrix
open CategoryTheory.LAdicTower

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard
  etaleModuleInverseImage_preservesFiniteLimits etaleModuleInverseImage_preservesFiniteColimits

section FieldExtension

variable (k k' : Type u) [Field k] [Field k'] [Algebra k k'] (B : BigEtaleSite.{u})
  (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
  (hS₀ : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k)))))
  (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
  (hL₀ : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k))))

/-- **`Spec k'[x][t] → Spec k[x][t]`**, as a morphism of the big étale site. -/
public abbrev laumonPlaneFieldExtensionHom :
    Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS ⟶
      Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k)) B hS₀ :=
  ObjectProperty.homMk (Spec.map (CommRingCat.ofHom
    (Polynomial.mapRingHom (Polynomial.mapRingHom (algebraMap k k')))))

/-- **`Spec k'[t] → Spec k[t]`**, as a morphism of the big étale site. -/
public abbrev laumonLineFieldExtensionHom :
    Stacks.ArtinSchreier.specObject (Polynomial k') B hL ⟶
      Stacks.ArtinSchreier.specObject (Polynomial k) B hL₀ :=
  ObjectProperty.homMk (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))))

end FieldExtension

section Family

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

/-- **The level zero of the Fourier family has locally constant `Rˢ g'_!`, for `a ≠ 0`**: for
every finite extension `k'` of `k`, `a ∈ k'ˣ`, all the data of the family, every open `V'` of the
`t`-line, `U' = pr₂⁻¹(V')` and any compactification of `g' : U' → V'`, all the `Rˢ g'_!` of the
restriction to `U'` of the level zero `K₀` of the flat model of the Fourier family `K` are locally
constant of finite type. -/
public def LaumonFourierLineAwayLevelZero : Prop :=
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
    ∀ s : ℤ, Stacks.ConstantSheaf.IsFiniteTypeLocallyConstant.{u + 1} ℤ_[ℓ] V'.1.smallEtaleTopology
      ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' s).obj
        ((etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)).obj
          (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
            (laumonFourierFamilySheaf k' B hS b
              (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n a z pz _
                hσ₁).toLAdicSheaf)) 0)))

end Family

/-- **Laumon's local theory away from `a = 0`, with coefficients killed by `ℓ`**: under the
hypotheses of `Stacks.EtaleCohomology.LaumonFourierLineLisseInput` there is `N` such that for
`n > N` prime to `p` and every `a ≠ 0`, all the `Rˢ g'_!` of the level zero of the Fourier family
are locally constant over every open of the `t`-line
(`Stacks.EtaleCohomology.LaumonFourierLineAwayLevelZero`). The level zero is a lisse sheaf killed
by `ℓ` all of whose slopes at `∞` equal `n > 1`, and Laumon's local theory of the Fourier transform
holds for such coefficients. -/
public def LaumonFourierLineAwayLevelZeroInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_ : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    LaumonStablyAbsIrr k e x σ → (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∃ N : ℕ, ∀ n : ℕ, N < n → ¬ p ∣ n →
      LaumonFourierLineAwayLevelZero B U ℓ k e x E b σ ψ n

/-- **The lisse transform away from `a = 0`, from its level zero**:
`Stacks.EtaleCohomology.LaumonFourierLineAwayLevelZeroInput` implies
`Stacks.EtaleCohomology.LaumonFourierLineLisseAwayInput`, by
`Stacks.EtaleCohomology.LAdicSheaf.isLisse_higherDirectImageShriek_of_levelZero` and the
restriction of the level zero of the flat model
(`Stacks.EtaleCohomology.LAdicSheaf.flatModelLevelZeroInverseImageIso`). -/
public theorem laumonFourierLineLisseAwayInput_of_levelZero
    (H : LaumonFourierLineAwayLevelZeroInput.{u}) : LaumonFourierLineLisseAwayInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ hef j kbar _ _ _ _ p q _ _ hcard hℓp x E _ _ _
    d b m σ hσ K _ _ _ hirr hstab hζ ι' β hV hpure ψ hψ
  obtain ⟨N, hN⟩ :=
    H B U ℓ k f e hef j kbar p q hcard hℓp x E b σ hσ K hirr hstab hζ ι' β hpure ψ hψ
  refine ⟨N, fun n hn hpn => ?_⟩
  intro k' _ _ _ a ha hS hL z hz pz hσ₁ V' U' _ _ jV' jU g' _ _ _ jg' hopen hpb
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  refine LAdicSheaf.isLisse_higherDirectImageShriek_of_levelZero B ℓ g' jg' _ (fun s => ?_) 1
  exact ObjectProperty.prop_of_iso
    (Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      V'.1.smallEtaleTopology ℤ_[ℓ])
      ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' s).mapIso
        (LAdicSheaf.flatModelLevelZeroInverseImageIso B ℓ jU _).symm)
      (hN n hn hpn k' a ha hS hL z hz pz hσ₁ V' U' jV' jU g' jg' hopen hpb s)

/-- **The lattice comparison on the line `a = 0`**: under the hypotheses of
`Stacks.EtaleCohomology.LaumonFourierLineLisseInput`, for every `n` (and when the plane over `k`
is below the cutoff of the site) there are finitely many constructible sheaves `Qᵢ` on
`Spec k[x][t]` killed by `ℓ` such that, for every finite extension `k'` of `k` and all the data
of the Fourier family `K` on the line `a = 0` over `k'`, the level zero of the flat model of `K`
lies in the closure under extensions and summands
(`Stacks.EtaleCohomology.IsExtensionSummandClosure`) of the pullbacks of the `Qᵢ` to
`Spec k'[x][t]`. (Take for the `Qᵢ` the simple constituents of the reduction modulo `ℓ` of a
lattice of the family over `k`: the family over `k'` is its pullback, `ψ' = ψ ∘ Tr_{k'/k}`
(`Stacks.EtaleCohomology.artinSchreierCharacter_trace_baseChange_eq`), any two stable lattices
have the same constituents modulo `ℓ` (Brauer–Nesbitt), and the pullback of a simple constituent
is semisimple (Clifford).) -/
public def LaumonFourierZeroLatticeInput : Prop :=
  ∀ (B : BigEtaleSite.{u}) (U : B.Scheme) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (g : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B g).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ n : ℕ, HasWeakSheafify (SmallEtale.topology B U.1 U.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [IsNoetherian U.1] [Fact ℓ.Prime] [ConnectedSpace U.1]
    (k : Type u) [Field k] [Fintype k] (f : U.1 ⟶ Spec (.of k))
    [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f] [SmoothOfRelativeDimension 1 f]
    [IsAffine U.1] (e : U.1 ⟶ Spec (.of (Polynomial k))) [IsOpenImmersion e] [IsIso e]
    (_ : e ≫ Spec.map (CommRingCat.ofHom (algebraMap k (Polynomial k))) = f)
    (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [Algebra k kbar]
    [IsAlgClosure k kbar]
    [ConnectedSpace ↥(Limits.pullback f (Spec.map (CommRingCat.ofHom (algebraMap k kbar))))]
    (p n : ℕ) [Fact p.Prime] [CharP k p] (_ : Fintype.card k = p ^ n) (_ : ℓ ≠ p)
    (x : GeometricPoint U.1)
    (E : Type) [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) {m : ℕ} (σ : EtaleFundamentalGroup U.1 x →* GL (Fin m) E)
    (hσ : Continuous (restrictScalarsRep b σ)) (K : Type) [Field K] [IsAlgClosed K] [Algebra E K],
    (∀ W : Submodule K (Fin m → K),
      (∀ g, ∀ v ∈ W, (σ g).val.map (algebraMap E K) *ᵥ v ∈ W) → W = ⊥ ∨ W = ⊤) →
    LaumonStablyAbsIrr k e x σ → (∃ ζ : E, IsPrimitiveRoot ζ p) →
    ∀ (ι' : E →+* ℂ) (β : ℤ)
    [FiniteDimensional ℚ_[ℓ]
        (LAdicSheaf.rationalGeometricCompactlySupportedCohomology B U ℓ f j kbar
          (LAdicSheaf.representationSheaf B U x (restrictScalarsRep b σ) hσ) 1)],
    (∀ (y : closedPoints U.1) (z : ℂ),
        ((σ (geometricFrobeniusFamily f x y)).val.charpoly.map ι').IsRoot z →
        ‖z‖ = ((p ^ n : ℕ) : ℝ) ^ (((residueDegree f y.1 : ℤ) * β : ℝ) / 2)) →
    ∀ ψ : AddChar k E, ψ ≠ 1 → ∀ n : ℕ,
    ∀ hS₀ : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k)))),
    ∃ (ι : Type) (_ : Fintype ι)
      (Q : ι → EtaleModules.{u, 0} ℤ_[ℓ]
        (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k)) B hS₀).1),
      (∀ i, IsBigSiteConstructibleEtaleModule B _ ℤ_[ℓ] (Q i)) ∧ (∀ i, ℓ • 𝟙 (Q i) = 0) ∧
      ∀ (k' : Type u) [Field k'] [Fintype k'] [Algebra k k']
        (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
        (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
        (hz : (z.map (laumonFamilyPr₁ k')).map (Spec.map (CommRingCat.ofHom
          (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e) = x)
        (pz : (finiteEtaleFiberFunctor z).obj
          (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k'))
            (laumonFourierKernel k' n 0)))
        (hσ₁ : Continuous (restrictScalarsRep b (σ.comp (hz ▸ (etaleFundamentalGroupMap
          (Spec.map (CommRingCat.ofHom (Polynomial.mapRingHom (algebraMap k k'))) ≫ inv e)
            (z.map (laumonFamilyPr₁ k'))).toMonoidHom)))),
        haveI : IsNoetherian
            (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
          inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
        IsExtensionSummandClosure (fun A => ∃ i, Nonempty (A ≅
            (etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
              (B.inclusion.map (laumonPlaneFieldExtensionHom k k' B hS hS₀))).obj (Q i)))
          (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
            (laumonFourierFamilySheaf k' B hS b
              (ψ.compAddMonoidHom (Algebra.trace k k').toAddMonoidHom) n 0 z pz _
                hσ₁).toLAdicSheaf)) 0)

/-- **Laumon's local theory on the line `a = 0`, from the lattice comparison**:
`Stacks.EtaleCohomology.LaumonFourierZeroLatticeInput` implies
`Stacks.EtaleCohomology.LaumonFourierLineLisseZeroInput`. The `Rˢ pr₂!` of the finitely many `Qᵢ`
are locally constant over `D(D₀)` for one nonzero `D₀ ∈ k[t]`, after every base change
(`Stacks.EtaleCohomology.exists_ne_zero_forall_isFiniteTypeLocallyConstant_lowerShriekHomology`);
an open `V'` of the `t`-line over `k'` inside `D(D₀ ⊗ k')` maps to `D(D₀)`, and
`U' → Spec k'[x][t] → Spec k[x][t]` over `V' → Spec k'[t] → Spec k[t]` is cartesian
(`Stacks.EtaleCohomology.isPullback_laumonPlaneFieldExtension`). So the `Rˢ g'_!` of the
restriction of every sheaf of the closure, in particular of the level zero of the family, are
locally constant
(`Stacks.EtaleCohomology.forall_isFiniteTypeLocallyConstant_lowerShriekHomology_of_closure`), and
`G_V` is lisse (`Stacks.EtaleCohomology.LAdicSheaf.isLisse_higherDirectImageShriek_of_levelZero`).
When the plane over `k` is not below the cutoff, neither is the plane over any `k'`, and `D₀ = 1`
does. -/
public theorem laumonFourierLineLisseZeroInput_of_lattice
    (H : LaumonFourierZeroLatticeInput.{u}) : LaumonFourierLineLisseZeroInput.{u} := by
  intro B U ℓ _ _ _ _ _ _ k _ _ f _ _ _ _ _ e _ _ hef j kbar _ _ _ _ p q _ _ hcard hℓp x E _ _ _
    d b m σ hσ K _ _ _ hirr hstab hζ ι' β hV hpure ψ hψ n
  by_cases hS₀ : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k))))
  swap
  · refine ⟨1, one_ne_zero, ?_⟩
    intro k' _ _ _ a _ hS
    exact absurd (schemeSizeBelow_laumonPlane_of_fieldExtension k k' hS) hS₀
  have hL₀ := schemeSizeBelow_laumonLine_of_laumonPlane k hS₀
  obtain ⟨ι, _, Q, hQc, hQ, hcl⟩ :=
    H B U ℓ k f e hef j kbar p q hcard hℓp x E b σ hσ K hirr hstab hζ ι' β hpure ψ hψ n hS₀
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k)) B hS₀).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k)))))
  obtain ⟨D₀, hD₀, hD⟩ := exists_ne_zero_forall_isFiniteTypeLocallyConstant_lowerShriekHomology B
    hL₀ (laumonFamilyProjection k B hS₀ hL₀) Q hQc ℓ (Fact.out : ℓ.Prime).pos hQ
  refine ⟨D₀, hD₀, ?_⟩
  intro k' _ _ _ a ha hS hL z hz pz hσ₁ V' U' _ _ jV' jU g' _ _ _ jg' hopen hrange hpb
  have ha0 : a = 0 := by simpa using ha
  subst ha0
  rw [eval₂_laumonLine_aeval_X_one] at hrange
  have : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
    inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
  let π := laumonPlaneFieldExtensionHom k k' B hS hS₀
  let πt := laumonLineFieldExtensionHom k k' B hL hL₀
  let Pr : ObjectProperty (EtaleModules.{u, 0} ℤ_[ℓ] V'.1) :=
    Stacks.ConstantSheaf.IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, 0}
      V'.1.smallEtaleTopology ℤ_[ℓ]
  have hpb' : IsPullback (B.inclusion.map (jU ≫ π)) (B.inclusion.map g')
      (B.inclusion.map (laumonFamilyProjection k B hS₀ hL₀)) (B.inclusion.map (jV' ≫ πt)) :=
    hpb.paste_horiz (isPullback_laumonPlaneFieldExtension k k')
  have hrange' : Set.range (B.inclusion.map (jV' ≫ πt)) ⊆
      (PrimeSpectrum.basicOpen D₀ : Set (PrimeSpectrum (Polynomial k))) :=
    range_comp_laumonLineFieldExtension_subset k k' (B.inclusion.map jV') D₀ hrange
  let S' : ObjectProperty (EtaleModules.{u, 0} ℤ_[ℓ] U'.1) := fun A =>
    ∃ i, Nonempty (A ≅ (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map (jU ≫ π))).obj (Q i))
  have hS' : ∀ A, S' A → ∀ s : ℤ,
      Pr ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' s).obj A) := by
    rintro A ⟨i, ⟨eA⟩⟩ s
    exact Pr.prop_of_iso ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' s).mapIso eA).symm
      (hD V' U' (jV' ≫ πt) (jU ≫ π) g' jg' hrange' hpb' i s)
  have hcl' := IsExtensionSummandClosure.map
    (etaleModuleInverseImage.{u, 0} ℤ_[ℓ] (B.inclusion.map jU)) (S' := S')
    (fun A ⟨i, ⟨eA⟩⟩ => .of_mem ⟨i, ⟨(etaleModuleInverseImage.{u, 0} ℤ_[ℓ]
      (B.inclusion.map jU)).mapIso eA ≪≫ ((etaleModuleInverseImageCompIso ℤ_[ℓ]
        (B.inclusion.map jU) (B.inclusion.map π)).app (Q i)).symm⟩⟩)
    (hcl k' hS z hz pz hσ₁)
  refine LAdicSheaf.isLisse_higherDirectImageShriek_of_levelZero B ℓ g' jg' _ (fun s => ?_) 1
  exact Pr.prop_of_iso
    ((lowerShriekHomology ℤ_[ℓ] (B.inclusion.map g') jg' s).mapIso
      (LAdicSheaf.flatModelLevelZeroInverseImageIso B ℓ jU _).symm)
    (forall_isFiniteTypeLocallyConstant_lowerShriekHomology_of_closure (B.inclusion.map g') jg'
      ℤ_[ℓ] hS' hcl' s)

end Stacks.EtaleCohomology

end
