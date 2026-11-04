module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonFlatLevelZeroReduction

/-!
# The no-punctual-sections input of Laumon's degeneration for `ℓ ≠ char k'`

The input (H2) of the specialization injection of Laumon's degeneration argument
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)),
`Stacks.EtaleCohomology.LaumonFamilyNoPunctualSectionsInput`, and its reductions
`Stacks.EtaleCohomology.LaumonFamilyFlatLevelVanishingInput` and
`Stacks.EtaleCohomology.LaumonFamilyFlatLevelZeroVanishingInput`, quantify over all primes `ℓ`,
including the characteristic `p` of the finite field `k'`. Tag 03VH works with `ℓ ≠ p` throughout,
and the vanishing `H¹_c(𝔸²_k̄, K'₀) = 0` uses it: on the lines `h(x) ≠ 0` the Artin–Schreier sheaf
`L_ψ'(t h(x))` has no cohomology with compact supports because `p` is invertible in the
coefficients. This file states the three propositions with the hypothesis `ringChar k' ≠ ℓ`
(`Stacks.EtaleCohomology.LaumonFamilyNoPunctualSectionsInput'`,
`Stacks.EtaleCohomology.LaumonFamilyFlatLevelVanishingInput'`,
`Stacks.EtaleCohomology.LaumonFamilyFlatLevelZeroVanishingInput'`) and the same two reductions
between them, which are those of the unrestricted statements at each `ℓ`.

## Main definitions

* `Stacks.EtaleCohomology.LaumonFamilyNoPunctualSectionsInput'`.
* `Stacks.EtaleCohomology.LaumonFamilyFlatLevelVanishingInput'`.
* `Stacks.EtaleCohomology.LaumonFamilyFlatLevelZeroVanishingInput'`.

## Main results

* `Stacks.EtaleCohomology.laumonFamilyNoPunctualSectionsInput'_of_flatLevelVanishing'`.
* `Stacks.EtaleCohomology.laumonFamilyFlatLevelVanishingInput'_of_levelZero'`.
* `Stacks.EtaleCohomology.laumonFamilyNoPunctualSectionsInput'_of_levelZero'`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.LAdicTower AlgebraicGeometry
open AlgebraicGeometry.SmallEtale CategoryTheory.Abelian Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- **(H2) `G = R¹pr₂! K` has no punctual sections, for `ℓ ≠ char k'`**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): for the family sheaf
`K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t h(x))`, `h = xⁿ⁰ + c x ≠ 0`, `ψ'` nontrivial, a nonempty open `j : V ⟶ W`
of the `t`-line `W` and a point `y ∉ V`, the kernels of the stalks at `ȳ` of the units
`Gₙ → j_* j⁻¹ Gₙ` are killed by a fixed power of `ℓ`. (Since `R⁰pr₂! K = 0`, the Leray edge map
identifies `H⁰_c(W_k̄, Gₙ)` with `H¹_c(𝔸²_k̄, Kₙ)`, which vanishes because `R pr₁! L_ψ'(t h(x))` is
supported on `h = 0`, where `L_ψ'` is trivial along the `t`-line; a section of `Gₙ` supported at
`ȳ` is a compactly supported section.) -/
public def LaumonFamilyNoPunctualSectionsInput' : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k' : Type u) [Field k'] [Fintype k']
    (_ : ringChar k' ≠ ℓ)
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E) (_ : ψ' ≠ 1) (n₀ : ℕ) (c : k')
    (_ : (Polynomial.X ^ n₀ + Polynomial.C c * Polynomial.X : Polynomial k') ≠ 0)
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c))) {m : ℕ}
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁))
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL))))
    (V : B.Scheme) [IsNoetherian V.1] [Nonempty V.1]
    (jW : V.1 ⟶ (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1) [IsOpenImmersion jW]
    (y : (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1) (_ : y ∉ Set.range jW.base),
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial k'))))
    ∃ M : ℕ, ∀ (n : ℕ)
      (w : finiteLevelStalk B (Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
        ℓ (laumonFamilyHigherDirectImage k' B hS hL b ψ' n₀ c z p₀ σ₁ hσ₁ jg).toLAdicSheaf
        (geometricPointAt _ y) n),
      (levelUnitStalkMap (ObjectProperty.homMk jW :
          V ⟶ Stacks.ArtinSchreier.specObject (Polynomial k') B hL)
        (laumonFamilyHigherDirectImage k' B hS hL b ψ' n₀ c z p₀ σ₁ hσ₁ jg).toLAdicSheaf
        (geometricPointAt _ y) n).hom w = 0 → (ℓ ^ M) • w = 0

/-- **The vanishing on the flat levels of Laumon's family sheaf, for `ℓ ≠ char k'`**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): for the family sheaf
`K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t h(x))` on `Spec k'[x][t]` (`h = xⁿ⁰ + c x ≠ 0`, `ψ'` nontrivial) and the
levels `K'ₙ` of its flat model (`Stacks.EtaleCohomology.LAdicSheaf.flatModel`), read as sheaves of
`ℤ_ℓ`-modules on Mathlib's small étale site:

* `R⁰pr₂! K'ₙ = 0`: the fibres of `pr₂` are affine lines over fields, carrying a locally constant
  sheaf, which has no compactly supported sections;
* `H¹_c(𝔸²_k̄, K'ₙ) = 0`: along `pr₁ : 𝔸² → 𝔸¹_x`, the fibre over `x̄` is the `t`-line with
  `K'ₙ| = M ⊗ L_ψ'(h(x̄) t)`, so `R^q pr₁! K'ₙ = 0` for `q ≤ 1` (constant for `h(x̄) = 0`, a
  nontrivial Artin–Schreier sheaf otherwise), and the Leray spectral sequence gives `H¹_c = 0`. -/
public def LaumonFamilyFlatLevelVanishingInput' : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k' : Type u) [Field k'] [Fintype k']
    (_ : ringChar k' ≠ ℓ)
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E) (_ : ψ' ≠ 1) (n₀ : ℕ) (c : k')
    (_ : (Polynomial.X ^ n₀ + Polynomial.C c * Polynomial.X : Polynomial k') ≠ 0)
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c))) {m : ℕ}
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁))
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL))))
    (n : ℕ),
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
    IsZero ((lowerShriekHomology ℤ_[ℓ]
        (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg 0).obj
        (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
          (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf)) n)) ∧
      ∀ (kbar : Type u) [Field kbar] [Algebra k' kbar] [IsAlgClosure k' kbar]
        (jU : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL) ≫
          laumonLineStructure k' B hL))),
        IsZero ((compactSupportSheafCohomology ℤ_[ℓ]
          (B.inclusion.map (laumonFamilyProjection k' B hS hL) ≫ laumonLineStructure k' B hL) jU
            kbar 1).obj
          (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
            (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf)) n))

private instance isNoetherian_specObject_polynomial (k' : Type u) [Field k'] (B : BigEtaleSite.{u})
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k')))) :
    IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 :=
  inferInstanceAs (IsNoetherian (Spec (.of (Polynomial k'))))

private instance isNoetherian_specObject_polynomial_polynomial (k' : Type u) [Field k']
    (B : BigEtaleSite.{u})
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k'))))) :
    IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
  inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))

/-- **(H2) from the vanishing on the flat levels, for `ℓ ≠ char k'`**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)):
`Stacks.EtaleCohomology.LaumonFamilyNoPunctualSectionsInput'` holds with `M = 0` once
`R⁰pr₂! K'ₙ = 0` and `H¹_c(𝔸²_k̄, K'ₙ) = 0` on the flat levels `K'ₙ` of the family sheaf: the Leray
edge gives `H⁰_c(W_k̄, R¹pr₂! K'ₙ) = 0`, and a sheaf without compactly supported sections has no
sections supported at the points of the finite complement of `V`. -/
public theorem laumonFamilyNoPunctualSectionsInput'_of_flatLevelVanishing'
    (h : LaumonFamilyFlatLevelVanishingInput'.{u}) : LaumonFamilyNoPunctualSectionsInput'.{u} := by
  intro B ℓ _ _ _ _ k' _ _ hℓ hS hL E _ _ _ d b ψ' hψ' n₀ c hh z p₀ m σ₁ hσ₁ jg V _ _ jW _ y hyV
  refine ⟨0, fun n w hw => ?_⟩
  rw [pow_zero, one_smul]
  let W := Stacks.ArtinSchreier.specObject (Polynomial k') B hL
  let fW := laumonLineStructure k' B hL
  let kbar := AlgebraicClosure k'
  obtain ⟨jW'⟩ : Nonempty (CompactificationOf (Over.mk fW)) := IsCofiltered.nonempty
  have : LocallyOfFiniteType (B.inclusion.map (laumonFamilyProjection k' B hS hL) ≫ fW) :=
    inferInstance
  have : QuasiCompact fW := inferInstanceAs (QuasiCompact
    (Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))))
  have : QuasiCompact (B.inclusion.map (laumonFamilyProjection k' B hS hL) ≫ fW) := inferInstance
  have : IsSeparated (B.inclusion.map (laumonFamilyProjection k' B hS hL) ≫ fW) := inferInstance
  obtain ⟨jU⟩ : Nonempty (CompactificationOf (Over.mk
      (B.inclusion.map (laumonFamilyProjection k' B hS hL) ≫ fW))) := IsCofiltered.nonempty
  obtain ⟨Z, iZ, _, _, _, hij⟩ := exists_closedImmersion_compl_range_affineLine k' jW
  have hy : y ∈ Set.range iZ.base := by
    by_contra hc
    have : y ∈ Set.range jW.base := by
      rw [hij]
      exact hc
    exact hyV this
  have : Finite (W.1.residueField y) := finite_residueField fW y
    (isClosed_singleton_of_notMem_range_affineLine k' jW y hyV)
  have : IsOpenImmersion (B.inclusion.map (ObjectProperty.homMk jW : V ⟶ W)) :=
    inferInstanceAs (IsOpenImmersion jW)
  refine LAdicSheaf.levelUnitStalkMap_higherDirectImageShriek_eq_zero B ℓ
    (laumonFamilyProjection k' B hS hL) jg fW jW' kbar iZ (ObjectProperty.homMk jW : V ⟶ W)
    (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf 1 hij y hy (fun n' => ?_) n w hw
  obtain ⟨h0, h1⟩ := h B ℓ k' hℓ hS hL b ψ' hψ' n₀ c hh z p₀ σ₁ hσ₁ jg n'
  let K : (IsLPowerTorsion ℓ
      (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1).FullSubcategory :=
    ⟨towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
      (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf)) n',
      ⟨n' + 1, LAdicSheaf.padicTower_annihilated B _ ℓ _ n'⟩⟩
  exact LAdicSheaf.isZero_compactSupportSheafCohomology_lowerShriekHomology_one B ℓ
    (laumonFamilyProjection k' B hS hL) jg fW jW' kbar K h0 jU (h1 kbar jU)

/-- **The vanishing on the bottom flat level of Laumon's family sheaf, for `ℓ ≠ char k'`**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)):
`Stacks.EtaleCohomology.LaumonFamilyFlatLevelVanishingInput'` at the level `n = 0` only, for the
bottom level `K'₀` of the flat model of the family sheaf, a sheaf killed by `ℓ`: `R⁰pr₂! K'₀ = 0`
and `H¹_c(𝔸²_k̄, K'₀) = 0`. -/
public def LaumonFamilyFlatLevelZeroVanishingInput' : Prop :=
  ∀ (B : BigEtaleSite.{u}) (ℓ : ℕ)
    [∀ (n : ℕ) (S T : B.Scheme) (f : T ⟶ S),
      ((AlgebraicGeometry.smallEtaleBaseChange B f).sheafPushforwardContinuous
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))
        (SmallEtale.topology B S.1 S.property)
        (SmallEtale.topology B T.1 T.property)).IsRightAdjoint]
    [∀ (n : ℕ) (T : B.Scheme) (V : SmallEtale B T.1 T.property),
      HasWeakSheafify ((SmallEtale.topology B T.1 T.property).over V)
        (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))]
    [∀ (n : ℕ) (T : B.Scheme), HasWeakSheafify (SmallEtale.topology B T.1 T.property)
      (ModuleCat.{u + 1} (ZMod (ℓ ^ (n + 1))))] [Fact ℓ.Prime]
    (k' : Type u) [Field k'] [Fintype k']
    (_ : ringChar k' ≠ ℓ)
    (hS : schemeSizeBelow B.cutoff (Spec (.of (Polynomial (Polynomial k')))))
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k'))))
    {E : Type} [Field E] [Algebra ℚ_[ℓ] E] [FiniteDimensional ℚ_[ℓ] E] {d : ℕ}
    (b : Module.Basis (Fin d) ℚ_[ℓ] E) (ψ' : AddChar k' E) (_ : ψ' ≠ 1) (n₀ : ℕ) (c : k')
    (_ : (Polynomial.X ^ n₀ + Polynomial.C c * Polynomial.X : Polynomial k') ≠ 0)
    (z : GeometricPoint (Spec (.of (Polynomial (Polynomial k')))))
    (p₀ : (finiteEtaleFiberFunctor z).obj
      (Stacks.ArtinSchreier.cover k' (Polynomial (Polynomial k')) (laumonKernel k' n₀ c))) {m : ℕ}
    (σ₁ : EtaleFundamentalGroup (Spec (.of (Polynomial k'))) (z.map (laumonFamilyPr₁ k')) →*
      GL (Fin m) E) (hσ₁ : Continuous (restrictScalarsRep b σ₁))
    (jg : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL)))),
    haveI : IsNoetherian (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1 :=
      inferInstanceAs (IsNoetherian (Spec (.of (Polynomial (Polynomial k')))))
    IsZero ((lowerShriekHomology ℤ_[ℓ]
        (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg 0).obj
        (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
          (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf)) 0)) ∧
      ∀ (kbar : Type u) [Field kbar] [Algebra k' kbar] [IsAlgClosure k' kbar]
        (jU : CompactificationOf (Over.mk (B.inclusion.map (laumonFamilyProjection k' B hS hL) ≫
          laumonLineStructure k' B hL))),
        IsZero ((compactSupportSheafCohomology ℤ_[ℓ]
          (B.inclusion.map (laumonFamilyProjection k' B hS hL) ≫ laumonLineStructure k' B hL) jU
            kbar 1).obj
          (towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
            (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf)) 0))

/-- **The vanishing on the flat levels from the bottom level, for `ℓ ≠ char k'`**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): the levels of the flat model are flat, so
`R⁰pr₂!` and `H¹_c(𝔸²_k̄, -)` vanish on every `K'ₙ` once they vanish on `K'₀`. -/
public theorem laumonFamilyFlatLevelVanishingInput'_of_levelZero'
    (h : LaumonFamilyFlatLevelZeroVanishingInput'.{u}) :
    LaumonFamilyFlatLevelVanishingInput'.{u} := by
  intro B ℓ _ _ _ _ k' _ _ hℓ hS hL E _ _ _ d b ψ' hψ' n₀ c hh z p₀ m σ₁ hσ₁ jg n
  obtain ⟨h0, h1⟩ := h B ℓ k' hℓ hS hL b ψ' hψ' n₀ c hh z p₀ σ₁ hσ₁ jg
  let K := (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf
  have hK := LAdicSheaf.powExact_etaleLevel_flatModel B ℓ K
  refine ⟨?_, fun kbar _ _ _ jU => ?_⟩
  · exact LAdicSheaf.isZero_lowerShriekHomology_padicTower B
      (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) ℓ
      (LAdicSheaf.flatModel B ℓ K) hK (B.inclusion.map (laumonFamilyProjection k' B hS hL)) jg 0
      h0 n
  · exact LAdicSheaf.isZero_compactSupportSheafCohomology_padicTower B
      (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS) ℓ
      (LAdicSheaf.flatModel B ℓ K) hK
      (B.inclusion.map (laumonFamilyProjection k' B hS hL) ≫ laumonLineStructure k' B hL) jU
      kbar 1 (h1 kbar jU) n

/-- **(H2) from the vanishing on the bottom flat level, for `ℓ ≠ char k'`**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)). -/
public theorem laumonFamilyNoPunctualSectionsInput'_of_levelZero'
    (h : LaumonFamilyFlatLevelZeroVanishingInput'.{u}) : LaumonFamilyNoPunctualSectionsInput'.{u} :=
  laumonFamilyNoPunctualSectionsInput'_of_flatLevelVanishing'
    (laumonFamilyFlatLevelVanishingInput'_of_levelZero' h)

end Stacks.EtaleCohomology

end
