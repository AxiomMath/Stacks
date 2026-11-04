module

public import
  StacksFrontier.AlgebraicGeometry.DeRham.RelativePoincareDuality.TopDifferentialEtaleSection
public import StacksFrontier.AlgebraicGeometry.DeRham.PoincareDuality.TopDifferentialSpreadOut
public import StacksFrontier.Algebra.Homology.FlatComplexTopDegreeBaseChange

/-!
# The top de Rham differential: reduction to bases of finite type over `ℤ`

Let `f : X ⟶ Spec A` be proper and smooth of relative dimension `n`. Then `f` is the base change
of a proper morphism `Y ⟶ Spec R₀` smooth of relative dimension `n`, with `R₀ ⊆ A` of finite type
over `ℤ` (`AlgebraicGeometry.exists_isPullback_specAdjoin_smoothOfRelativeDimension`). On the
alternating Čech complexes of a finite affine covering of `Y` the de Rham differential of `X/A`
is the base change of that of `Y/R₀`; these are complexes of flat `R₀`-modules with no cohomology
above `n` ([Stacks, Tag 02V7]), so vanishing on `Hⁿ` passes from `Y/R₀` to `X/A`
(`Stacks.FlatComplexTopDegree.homologyMap_extendScalars_eq_zero_of_homologyMap_eq_zero`).

Consequently the vanishing of `d : Hⁿ(Y, Ω^{n-1}) ⟶ Hⁿ(Y, Ω^n)` in [Stacks, Tag 0G8J] only has to
be shown over bases of finite type over `ℤ`, which are Noetherian and Jacobson, and, by the
Stein factorization and étale-local sections, only for morphisms with a section whose ring of
global functions is the base ring.

## Main results

* `AlgebraicGeometry.TopDegreeDifferential.topDifferentialVanishes_of_finiteType`.
* `AlgebraicGeometry.TopDegreeDifferential.topDifferentialVanishes_of_section_of_finiteType`.
* `AlgebraicGeometry.RelativeDualitySituation.higherDirectImage_map_deRham_d_eq_zero_of_section`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace ModuleCat
open Stacks.Cech

universe u

namespace AlgebraicGeometry.TopDegreeDifferential

/-- **Reduction of the top de Rham differential to bases of finite type over `ℤ`.** If
`d : Hⁿ(Y, Ω^{n-1}_{Y/R}) ⟶ Hⁿ(Y, Ω^n_{Y/R})` vanishes for every proper `Y ⟶ Spec R` smooth of
relative dimension `n` with `R` of finite type over `ℤ`, then it vanishes for every proper
`X ⟶ Spec A` smooth of relative dimension `n`. -/
theorem topDifferentialVanishes_of_finiteType (n : ℕ)
    (h : ∀ (R : CommRingCat.{u}), Algebra.FiniteType ℤ R → ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec R)
      [IsProper g] [SmoothOfRelativeDimension n g], TopDifferentialVanishes g n)
    {A : CommRingCat.{u}} {X : Scheme.{u}} (f : X ⟶ Spec A) [IsProper f]
    [SmoothOfRelativeDimension n f] : TopDifferentialVanishes f n := by
  cases n with
  | zero => exact topDifferentialVanishes_zero f
  | succ e =>
  classical
  obtain ⟨⟨t⟩, Y, h₁, q', hprop, hsm, hpb⟩ :=
    exists_isPullback_specAdjoin_smoothOfRelativeDimension A f (e + 1)
  let R₀ : Subalgebra ℤ A := Algebra.adjoin ℤ (t : Set A)
  have : Algebra.FiniteType ℤ R₀ := finiteType_adjoinFinset_int A t
  let h₀ : Y ⟶ Spec (.of R₀) := h₁
  have : IsProper h₀ := hprop
  have : SmoothOfRelativeDimension (e + 1) h₀ := hsm
  have : Smooth h₀ := SmoothOfRelativeDimension.smooth (e + 1) h₀
  have : IsNoetherianRing R₀ := Algebra.FiniteType.isNoetherianRing ℤ R₀
  let ι : R₀ →+* A := R₀.val.toRingHom
  have hsq : IsPullback q' f h₀ (Spec.map (CommRingCat.ofHom ι)) := hpb
  have : IsAffineHom q' := MorphismProperty.of_isPullback hsq.flip inferInstance
  have : CompactSpace Y := QuasiCompact.compactSpace_of_compactSpace h₀
  obtain ⟨s, hs⟩ :=
    Stacks.AlgebraicGeometry.Tag01PFAffineExtend.exists_finset_affineOpens_iSup_eq_top (X := Y)
  let : LinearOrder s := linearOrderOfSTO WellOrderingRel
  let U : s → Y.Opens := fun i => i.1.1
  have hU : (⊤ : Y.Opens) = ⨆ i, U i := hs.symm.trans iSup_subtype'
  have hUaff : ∀ i, IsAffineOpen (U i) := fun i => i.1.2
  -- the vanishing over `R₀`, on Čech complexes
  have hvan : HomologicalComplex.homologyMap
      (alternatingCechModulePush h₀ U (Scheme.Hom.deRhamPresheafD h₀ e)
        (Scheme.Hom.deRhamPresheafD_app_smul h₀ e)) (e + 1) = 0 :=
    (rightDerived_map_deRham_d_eq_zero_iff_homologyMap h₀ U hU hUaff e e).1
      (h (.of R₀) inferInstance Y h₀)
  -- the Čech complexes of `Ω^e_{Y/R₀}` are flat, bounded, with no cohomology above `e + 1`
  have := Scheme.Hom.isQuasicoherent_relativeDifferentialForms h₀ e
  have hflat : IsFlatOver h₀.toLRSHom.toShHom (h₀.relativeDifferentialForms (e : ℤ)) :=
    have := ProperSmoothDeRham.isFiniteLocallyFree_relativeDifferentialForms h₀ e
    VectorBundleCodimensionOne.isFlatOver_of_isFiniteLocallyFree h₀ _
  have := Scheme.Hom.isCoherent_relativeDifferentialForms h₀ e
  have : ∀ i, Module.Flat R₀
      ((alternatingCechModuleComplex h₀ U (h₀.relativeDifferentialForms (e : ℤ))).X i) :=
    alternatingCechModuleComplex_flat h₀ U _ hUaff hflat
  have hfib : ∀ t : Spec (.of R₀),
      topologicalKrullDim (h₀.fiber t) ≤ ((e + 1 : ℕ) : WithBot ℕ∞) := by
    intro t
    have hsmt := smoothOfRelativeDimension_fiberToSpecResidueField h₀ (e + 1) t
    rcases isEmpty_or_nonempty (h₀.fiber t) with hE | hN
    · rw [(topologicalKrullDim_eq_bot_iff_isEmpty _).2 hE]
      exact bot_le
    · exact (@topologicalKrullDim_eq_of_smoothOfRelativeDimension_over_field _ _ _ hN (e + 1) _
        hsmt).le
  have hmain := Stacks.FlatComplexTopDegree.homologyMap_extendScalars_eq_zero_of_homologyMap_eq_zero
    (alternatingCechModulePush h₀ U (Scheme.Hom.deRhamPresheafD h₀ e)
      (Scheme.Hom.deRhamPresheafD_app_smul h₀ e)) e (Fintype.card s)
    (fun i hi => subsingleton_alternatingSubmodule h₀ U _ hi)
    (fun i hi => isZero_homology_alternatingCechModuleComplex h₀ U hU _ hUaff hfib hi) hvan ι
  -- read back on `X`
  have hU' : (⊤ : X.Opens) = ⨆ i, q' ⁻¹ᵁ U i := by
    rw [← Scheme.Hom.preimage_iSup, ← hU, Scheme.Hom.preimage_top]
  have : IsSeparated f := inferInstance
  exact (rightDerived_map_deRham_d_eq_zero_iff_homologyMap f (fun i => q' ⁻¹ᵁ U i) hU'
    (fun i => (hUaff i).preimage q') e e).2
    ((homologyMap_extendScalars_deRham_eq_zero_iff ι h₀ f q' hsq U hUaff e (e + 1)).1 hmain)

/-- Rings of finite type over `ℤ` are stable under ring maps of finite type. -/
theorem finiteType_int_of_finiteType {A B : CommRingCat.{u}} (φ : A ⟶ B)
    (hA : Algebra.FiniteType ℤ A) (hφ : φ.hom.FiniteType) : Algebra.FiniteType ℤ B := by
  algebraize [φ.hom]
  exact Algebra.FiniteType.trans (S := A) hA inferInstance

/-- **The top de Rham differential vanishes on `Hⁿ` over affine bases, from the case of a section
over a base of finite type over `ℤ`**: if `d : Hⁿ(Y, Ω^{n-1}_{Y/B}) ⟶ Hⁿ(Y, Ω^n_{Y/B})` vanishes
for every proper `Y ⟶ Spec B` smooth of relative dimension `n` with `B` of finite type over `ℤ`,
with a section and with `B ⟶ Γ(Y, 𝒪_Y)` bijective, then it vanishes for every proper `Y ⟶ Spec A`
smooth of relative dimension `n`. -/
theorem topDifferentialVanishes_of_section_of_finiteType (n : ℕ)
    (h : ∀ (B : CommRingCat.{u}), Algebra.FiniteType ℤ B → ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec B)
      [IsProper g] [SmoothOfRelativeDimension n g] [IsIso g.appTop] (σ : Spec B ⟶ Y),
      σ ≫ g = 𝟙 _ → TopDifferentialVanishes g n)
    {A : CommRingCat.{u}} {Y : Scheme.{u}} (g : Y ⟶ Spec A) [IsProper g]
    [SmoothOfRelativeDimension n g] : TopDifferentialVanishes g n :=
  topDifferentialVanishes_of_finiteType n
    (fun _ hR _ g' _ _ => topDifferentialVanishes_of_section_of_affine_of_mem
      (fun B => Algebra.FiniteType ℤ B) (fun φ hA hφ => finiteType_int_of_finiteType φ hA hφ) n
      h hR g') g

end AlgebraicGeometry.TopDegreeDifferential

namespace AlgebraicGeometry.RelativeDualitySituation

open TopDegreeDifferential in
/-- **Reduction of [Stacks, Tag 0G8J] to proper smooth schemes with a section over an affine
base of finite type over `ℤ` whose ring of global functions is the base ring.** In the relative
duality situation the map `d : R^n f_*Ω^{n-1}_{X/S} ⟶ R^n f_*Ω^n_{X/S}` is zero as soon as the top
de Rham differential vanishes on `H^n(Y, -)` for every proper `Y ⟶ Spec B` smooth of relative
dimension `n` with `B` of finite type over `ℤ`, with a section and with `B ⟶ Γ(Y, 𝒪_Y)`
bijective. -/
theorem higherDirectImage_map_deRham_d_eq_zero_of_section (D : RelativeDualitySituation.{u})
    (h : ∀ (B : CommRingCat.{u}), Algebra.FiniteType ℤ B → ∀ (Y : Scheme.{u}) (g : Y ⟶ Spec B)
      [IsProper g] [SmoothOfRelativeDimension D.n g] [IsIso g.appTop] (σ : Spec B ⟶ Y),
      σ ≫ g = 𝟙 _ → TopDifferentialVanishes g D.n) :
    (Stacks.Cohomology.AbelianSheaf.higherDirectImage D.f.base D.n).map
      ((SheafOfModules.toSheaf _).map (D.f.deRhamComplex.d (D.n - 1) D.n)) = 0 :=
  D.higherDirectImage_map_deRham_d_eq_zero_of_affine fun _ _ _ g _ _ _ =>
    topDifferentialVanishes_of_section_of_finiteType D.n h g

end AlgebraicGeometry.RelativeDualitySituation
