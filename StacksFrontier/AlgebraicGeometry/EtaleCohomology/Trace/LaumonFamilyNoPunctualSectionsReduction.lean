module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.HigherDirectImageShriekPunctualSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportLerayEdge
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.AffineLineOpenComplement
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.LaumonSpecializationInjection
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactificationIndependence.Independence

/-!
# `R¹pr₂! K` has no punctual sections, from the vanishing on the flat levels

In Laumon's degeneration argument ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)) the
family sheaf `K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t (xⁿ⁰ + c x))` on `𝔸² = Spec k'[x][t]` has
`G = R¹pr₂! K` on the `t`-line `W` (`Stacks.EtaleCohomology.laumonFamilyHigherDirectImage`).
The proposition `Stacks.EtaleCohomology.LaumonFamilyNoPunctualSectionsInput` (H2) asks that the
kernels of the stalks at `ȳ`, `y ∉ V`, of the units `Gₙ → j_* j⁻¹ Gₙ` be killed by a fixed power
of `ℓ`. This file reduces it, with `M = 0`, to the vanishing on the levels `K'ₙ` of the flat model
`K'` of `K` (`Stacks.EtaleCohomology.LaumonFamilyFlatLevelVanishingInput`):

* `R⁰pr₂! K'ₙ = 0` (the fibres of `pr₂` are affine lines carrying a locally constant sheaf);
* `H¹_c(𝔸²_k̄, K'ₙ) = 0` (by Leray along `pr₁`, `R pr₁! K'ₙ` lives in degree `2`).

Then the Leray edge
(`Stacks.EtaleCohomology.LAdicSheaf.isZero_compactSupportSheafCohomology_lowerShriekHomology_one`)
gives `H⁰_c(W_k̄, R¹pr₂! K'ₙ) = 0`, and
`Stacks.EtaleCohomology.LAdicSheaf.levelUnitStalkMap_higherDirectImageShriek_eq_zero` (for the
closed complement `Z` of `V`, `AlgebraicGeometry.exists_closedImmersion_compl_range_affineLine`)
gives the injectivity of the stalks of the units.

## Main definitions

* `Stacks.EtaleCohomology.LaumonFamilyFlatLevelVanishingInput`.

## Main results

* `AlgebraicGeometry.isClosed_singleton_of_notMem_range_affineLine`.
* `Stacks.EtaleCohomology.laumonFamilyNoPunctualSectionsInput_of_flatLevelVanishing`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.LAdicTower AlgebraicGeometry
open AlgebraicGeometry.SmallEtale Stacks.Frobenius

universe u

namespace AlgebraicGeometry

/-- **A point of `𝔸¹_K` outside a nonempty open is closed**: it is not the generic point, so its
prime is nonzero, hence maximal in the principal ideal domain `K[X]`. -/
theorem isClosed_singleton_of_notMem_range_affineLine (K : Type u) [Field K] {V : Scheme.{u}}
    [Nonempty V] (jV : V ⟶ Spec (.of (Polynomial K))) [IsOpenImmersion jV]
    (y : Spec (.of (Polynomial K))) (hy : y ∉ Set.range jV.base) : IsClosed ({y} : Set _) := by
  have hy0 : y.asIdeal ≠ ⊥ := by
    intro h
    obtain ⟨v⟩ := ‹Nonempty V›
    have hle : y.asIdeal ≤ (jV.base v).asIdeal := by
      rw [h]
      exact bot_le
    have hsp : y ⤳ jV.base v := (PrimeSpectrum.le_iff_specializes y (jV.base v)).1 hle
    exact hy (hsp.mem_open jV.isOpenEmbedding.isOpen_range ⟨v, rfl⟩)
  have : y.asIdeal.IsMaximal := y.isPrime.isMaximal hy0
  exact (PrimeSpectrum.isClosed_singleton_iff_isMaximal y).2 this

end AlgebraicGeometry

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

/-- The structure morphism `Spec k'[t] ⟶ Spec k'` of the `t`-line. -/
abbrev laumonLineStructure (k' : Type u) [Field k'] (B : BigEtaleSite.{u})
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k')))) :
    (Stacks.ArtinSchreier.specObject (Polynomial k') B hL).1 ⟶ Spec (.of k') :=
  Spec.map (CommRingCat.ofHom (algebraMap k' (Polynomial k')))

/-- The structure morphism `Spec k'[t] ⟶ Spec k'` of the `t`-line is locally of finite type. -/
instance locallyOfFiniteType_laumonLineStructure (k' : Type u) [Field k'] (B : BigEtaleSite.{u})
    (hL : schemeSizeBelow B.cutoff (Spec (.of (Polynomial k')))) :
    LocallyOfFiniteType (laumonLineStructure k' B hL) := by
  rw [HasRingHomProperty.Spec_iff (P := @LocallyOfFiniteType)]
  exact RingHom.finiteType_algebraMap.2 inferInstance

/-- **The vanishing on the flat levels of Laumon's family sheaf**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)): for the family sheaf
`K = pr₁^*ℱ_{σ₁} ⊗ L_ψ'(t h(x))` on `Spec k'[x][t]` (`h = xⁿ⁰ + c x ≠ 0`, `ψ'` nontrivial) and the
levels `K'ₙ` of its flat model (`Stacks.EtaleCohomology.LAdicSheaf.flatModel`), read as sheaves of
`ℤ_ℓ`-modules on Mathlib's small étale site:

* `R⁰pr₂! K'ₙ = 0`: the fibres of `pr₂` are affine lines over fields, carrying a locally constant
  sheaf, which has no compactly supported sections;
* `H¹_c(𝔸²_k̄, K'ₙ) = 0`: along `pr₁ : 𝔸² → 𝔸¹_x`, the fibre over `x̄` is the `t`-line with
  `K'ₙ| = M ⊗ L_ψ'(h(x̄) t)`, so `R^q pr₁! K'ₙ = 0` for `q ≤ 1` (constant for `h(x̄) = 0`, a
  nontrivial Artin–Schreier sheaf otherwise), and the Leray spectral sequence gives `H¹_c = 0`. -/
public def LaumonFamilyFlatLevelVanishingInput : Prop :=
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

/-- **(H2) from the vanishing on the flat levels**
([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)):
`Stacks.EtaleCohomology.LaumonFamilyNoPunctualSectionsInput` holds with `M = 0` once
`R⁰pr₂! K'ₙ = 0` and `H¹_c(𝔸²_k̄, K'ₙ) = 0` on the flat levels `K'ₙ` of the family sheaf: the
Leray edge gives `H⁰_c(W_k̄, R¹pr₂! K'ₙ) = 0`, and a sheaf without compactly supported sections
has no sections supported at the points of the finite complement of `V`. -/
public theorem laumonFamilyNoPunctualSectionsInput_of_flatLevelVanishing
    (h : LaumonFamilyFlatLevelVanishingInput.{u}) : LaumonFamilyNoPunctualSectionsInput.{u} := by
  intro B ℓ _ _ _ _ k' _ _ hS hL E _ _ _ d b ψ' hψ' n₀ c hh z p₀ m σ₁ hσ₁ jg V _ _ jW _ y hyV
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
  obtain ⟨h0, h1⟩ := h B ℓ k' hS hL b ψ' hψ' n₀ c hh z p₀ σ₁ hσ₁ jg n'
  let K : (IsLPowerTorsion ℓ
      (Stacks.ArtinSchreier.specObject (Polynomial (Polynomial k')) B hS).1).FullSubcategory :=
    ⟨towerObj (LAdicSheaf.padicTower B _ ℓ (LAdicSheaf.flatModel B ℓ
      (laumonFamilySheaf k' B hS b ψ' n₀ c z p₀ σ₁ hσ₁).toLAdicSheaf)) n',
      ⟨n' + 1, LAdicSheaf.padicTower_annihilated B _ ℓ _ n'⟩⟩
  exact LAdicSheaf.isZero_compactSupportSheafCohomology_lowerShriekHomology_one B ℓ
    (laumonFamilyProjection k' B hS hL) jg fW jW' kbar K h0 jU (h1 kbar jU)

end Stacks.EtaleCohomology

end
