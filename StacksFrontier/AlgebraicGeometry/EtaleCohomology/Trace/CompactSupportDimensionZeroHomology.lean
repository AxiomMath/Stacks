module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTruncation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Trace.CompactSupportTorsionVanishing

/-!
# `Hʳ_c(X_k̄, K) = H⁰_c(X_k̄, Hʳ(K))` in dimension zero, with Frobenius

Let `k` be a finite field, `X` a scheme of dimension zero, separated of finite type over `k`, with
a compactification `j`, and `k̄` an algebraically closed extension of `k`. For a bounded below
complex `K` of sheaves of `Λ`-modules on `X_étale` with `Hⁿ(K) = 0` for `n < 0` and every `Hⁿ(K)`
killed by a positive integer, the canonical truncations give

`Hʳ_c(X_k̄, K) ≅ Hʳ_c(X_k̄, τ_{≥ 0} K) ≅ Hʳ_c(X_k̄, τ_{≥ 1} K) ≅ ⋯ ≅ Hʳ_c(X_k̄, τ_{≥ r} K)
  ≅ Hʳ_c(X_k̄, τ_{≤ r} τ_{≥ r} K) ≅ H⁰_c(X_k̄, Hʳ(K))`,

naturally in `K` and compatibly with the geometric Frobenius `π_X^*`
(`Stacks.EtaleCohomology.compactSupportDimensionZeroHomologyIso`): the graded pieces
`τ_{≤ n} τ_{≥ n} K = Hⁿ(K)[-n]` have `Hⁱ_c = H^{i-n}_c(X_k̄, Hⁿ(K))`, which vanishes for
`i ≠ n` since `X` has dimension zero
(`Stacks.EtaleCohomology.isZero_compactSupportFrobeniusCohomologyGroup_single_of_nsmul_eq_zero`),
and the long exact sequences of the truncation triangles
(`Stacks.EtaleCohomology.compactSupportFrobeniusTriangle_distinguished`) conclude.

For `X = Spec κ`, `κ` a finite field, this computes the stalk side of the Leray comparison
`Hʳ_c(U_{κ̄}, K) ≅ H⁰_c(Spec κ̄, Rʳ g_! K)` at a closed point, in the reduction of the weight bound
of Weil II to curves ([Tag 03VH](https://stacks.math.columbia.edu/tag/03VH)).

## Main results

* `Stacks.EtaleCohomology.isIso_homology_compactSupportFrobeniusFunctor_map_g_of_isZero` and
  `isIso_homology_compactSupportFrobeniusFunctor_map_f_of_isZero`: the long exact sequence of a
  short exact sequence of complexes.
* `Stacks.EtaleCohomology.compactSupportDimensionZeroHomologyIso` and
  `Stacks.EtaleCohomology.compactSupportDimensionZeroHomologyIso_hom_frobenius`.

## Implementation notes

`compactSupportFrobeniusFunctor` lives in the standard model `HasDerivedCategory.standard`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.Frobenius

universe u

namespace Stacks.EtaleCohomology

attribute [local instance] HasDerivedCategory.standard

section General

variable (Λ : Type) [Ring Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) (j : CompactificationOf (Over.mk f))
  (kbar : Type u) [Field kbar] [Algebra k kbar]

section Triangle

variable {S : ShortComplex (CochainComplex (EtaleModules.{u, 0} Λ X) ℤ)} (hS : S.ShortExact)
  (h₁ : CochainComplex.plus _ S.X₁) (h₂ : CochainComplex.plus _ S.X₂)
  (h₃ : CochainComplex.plus _ S.X₃)

/-- Some Frobenius datum on the finite field `k`, to build the triangle. -/
private theorem exists_frobeniusDatum :
    ∃ (p n : ℕ) (_ : Fact p.Prime) (_ : CharP k p), Fintype.card k = p ^ n := by
  obtain ⟨p, hp⟩ := CharP.exists k
  obtain ⟨n, hpr, hn⟩ := FiniteField.card k p
  exact ⟨p, n, ⟨hpr⟩, hp, hn⟩

include hS in
/-- **`Hⁱ_c(X_k̄, K₂) ⟶ Hⁱ_c(X_k̄, K₃)` is an isomorphism when `Hⁱ_c` and `Hⁱ⁺¹_c` of `K₁`
vanish**, for a short exact sequence `0 → K₁ → K₂ → K₃ → 0` of bounded below complexes. -/
theorem isIso_homology_compactSupportFrobeniusFunctor_map_g_of_isZero (i : ℤ)
    (h0 : IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj ⟨S.X₁, h₁⟩)))
    (h1 : IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) (i + 1)).obj
      ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj ⟨S.X₁, h₁⟩))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
      ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
        (ObjectProperty.homMk S.g : (⟨S.X₂, h₂⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₃, h₃⟩))) := by
  obtain ⟨p, n, _, _, hn⟩ := exists_frobeniusDatum (k := k)
  have hT := compactSupportFrobeniusTriangle_distinguished.{u, 0} Λ f j kbar p n hn hS h₁ h₂ h₃
  refine @isIso_of_mono_of_epi _ _ _ _ _ _ ?_ ?_
  · exact (DerivedCategory.HomologySequence.mono_homologyMap_mor₂_iff _ hT i).2 (h0.eq_of_src _ _)
  · exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₂_iff _ hT i (i + 1) rfl).2
      (h1.eq_of_tgt _ _)

include hS in
/-- **`Hⁱ_c(X_k̄, K₁) ⟶ Hⁱ_c(X_k̄, K₂)` is an isomorphism when `Hⁱ⁻¹_c` and `Hⁱ_c` of `K₃`
vanish**, for a short exact sequence `0 → K₁ → K₂ → K₃ → 0` of bounded below complexes. -/
theorem isIso_homology_compactSupportFrobeniusFunctor_map_f_of_isZero (i : ℤ)
    (h0 : IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) (i - 1)).obj
      ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj ⟨S.X₃, h₃⟩)))
    (h1 : IsZero ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
      ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj ⟨S.X₃, h₃⟩))) :
    IsIso ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
      ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
        (ObjectProperty.homMk S.f : (⟨S.X₁, h₁⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₂, h₂⟩))) := by
  obtain ⟨p, n, _, _, hn⟩ := exists_frobeniusDatum (k := k)
  have hT := compactSupportFrobeniusTriangle_distinguished.{u, 0} Λ f j kbar p n hn hS h₁ h₂ h₃
  refine @isIso_of_mono_of_epi _ _ _ _ _ _ ?_ ?_
  · exact (DerivedCategory.HomologySequence.mono_homologyMap_mor₁_iff _ hT (i - 1) i
      (by omega)).2 (h0.eq_of_src _ _)
  · exact (DerivedCategory.HomologySequence.epi_homologyMap_mor₁_iff _ hT i).2 (h1.eq_of_tgt _ _)

end Triangle

/-! ### The truncation maps -/

/-- The cokernel `τ_{≥ n} K / τ_{≤ n} τ_{≥ n} K` of a bounded below complex is bounded below. -/
theorem plus_shortComplexTruncLE_X₃ (n : ℤ) (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    CochainComplex.plus _ ((K.obj.truncGE n).shortComplexTruncLE n).X₃ := by
  refine ⟨n, ?_⟩
  rw [CochainComplex.isStrictlyGE_iff]
  intro i' hi'
  have hS := ((K.obj.truncGE n).shortComplexTruncLE_shortExact n).map_of_exact
    (HomologicalComplex.eval _ (ComplexShape.up ℤ) i')
  have := hS.epi_g
  exact IsZero.of_epi (((K.obj.truncGE n).shortComplexTruncLE n).g.f i')
    ((K.obj.truncGE n).isZero_of_isStrictlyGE n i' hi')

omit [Fintype k] in
/-- The quasi-isomorphism `τ_{≥ n} K / τ_{≤ n} τ_{≥ n} K ⟶ τ_{≥ n+1} τ_{≥ n} K` becomes an
isomorphism under `compactSupportFrobeniusFunctor`. -/
theorem isIso_compactSupportFrobeniusFunctor_map_shortComplexTruncLEX₃ToTruncGE (n : ℤ)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    IsIso ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
      (ObjectProperty.homMk ((K.obj.truncGE n).shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl) :
        (⟨_, plus_shortComplexTruncLE_X₃ Λ n K⟩ : CochainComplex.Plus _) ⟶
          (CochainComplex.Plus.truncGEFunctor (n + 1)).obj
            ((CochainComplex.Plus.truncGEFunctor n).obj K))) := by
  have : QuasiIso (ObjectProperty.homMk
      ((K.obj.truncGE n).shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl) :
        (⟨_, plus_shortComplexTruncLE_X₃ Λ n K⟩ : CochainComplex.Plus _) ⟶
          (CochainComplex.Plus.truncGEFunctor (n + 1)).obj
            ((CochainComplex.Plus.truncGEFunctor n).obj K)).hom :=
    inferInstanceAs (QuasiIso ((K.obj.truncGE n).shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl))
  exact isIso_compactSupportFrobeniusFunctor_map_of_quasiIso Λ f j kbar _

/-- **`Hⁱ_c(X_k̄, τ_{≥ n} K) ⟶ Hⁱ_c(X_k̄, τ_{≥ n+1} K)` is an isomorphism** when `Hⁱ_c` and
`Hⁱ⁺¹_c` of the graded piece `τ_{≤ n} τ_{≥ n} K` vanish. -/
theorem isIso_compactSupportTruncToTrunc_app (n i : ℤ)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (h0 : IsZero ((compactSupportGradedHomology Λ f j kbar n i).obj K))
    (h1 : IsZero ((compactSupportGradedHomology Λ f j kbar n (i + 1)).obj K)) :
    IsIso ((compactSupportTruncToTrunc Λ f j kbar n i).app K) := by
  let M := K.obj.truncGE n
  let S := M.shortComplexTruncLE n
  have hS : S.ShortExact := M.shortComplexTruncLE_shortExact n
  have h₁ : CochainComplex.plus _ S.X₁ := ((CochainComplex.Plus.gradedFunctor n).obj K).property
  have h₂ : CochainComplex.plus _ S.X₂ := ((CochainComplex.Plus.truncGEFunctor n).obj K).property
  have h₃ : CochainComplex.plus _ S.X₃ := plus_shortComplexTruncLE_X₃ Λ n K
  have hg := isIso_homology_compactSupportFrobeniusFunctor_map_g_of_isZero Λ f j kbar hS h₁ h₂ h₃ i
    h0 h1
  let e := (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
    ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
      (ObjectProperty.homMk (M.shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl) :
        (⟨S.X₃, h₃⟩ : CochainComplex.Plus _) ⟶ (CochainComplex.Plus.truncGEFunctor (n + 1)).obj
          ((CochainComplex.Plus.truncGEFunctor n).obj K))) ≫
    inv ((Functor.whiskerRight (CochainComplex.Plus.truncGEπTruncGE n (n + 1))
      (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i)).app K)
  have he : IsIso e := by
    have := isIso_compactSupportFrobeniusFunctor_map_shortComplexTruncLEX₃ToTruncGE Λ f j kbar n K
    infer_instance
  have hk : (CochainComplex.Plus.πTruncGEComp n (n + 1)).app K =
      (ObjectProperty.homMk S.g : (⟨S.X₂, h₂⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₃, h₃⟩) ≫
        (ObjectProperty.homMk (M.shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl) :
          (⟨S.X₃, h₃⟩ : CochainComplex.Plus _) ⟶ (CochainComplex.Plus.truncGEFunctor (n + 1)).obj
            ((CochainComplex.Plus.truncGEFunctor n).obj K)) :=
    ObjectProperty.hom_ext _ (M.g_shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl).symm
  have heq : (compactSupportTruncToTrunc Λ f j kbar n i).app K =
      (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
          (ObjectProperty.homMk S.g : (⟨S.X₂, h₂⟩ : CochainComplex.Plus _) ⟶ ⟨S.X₃, h₃⟩)) ≫ e := by
    show (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
        ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
          ((CochainComplex.Plus.πTruncGEComp n (n + 1)).app K)) ≫ _ = _
    rw [NatIso.isIso_inv_app, hk]
    have hmc : ∀ {x y z : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)} {w : ModuleCat.{u + 1} Λ}
        (a : x ⟶ y) (b : y ⟶ z)
        (c : (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).obj
          ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj z) ⟶ w),
        (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
            ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map (a ≫ b)) ≫ c =
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
            ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map a) ≫
            ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).map
              ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map b) ≫ c) := fun a b c => by
      simp
    exact hmc _ _ _
  rw [heq]
  exact @IsIso.comp_isIso _ _ _ _ _ _ _ hg he

/-- **`Hⁿ_c(X_k̄, τ_{≤ n} τ_{≥ n} K) ⟶ Hⁿ_c(X_k̄, τ_{≥ n} K)` is an isomorphism**: the cokernel
`τ_{≥ n+1} K` has no `Hⁱ_c` for `i ≤ n`. -/
theorem isIso_compactSupportGradedToTrunc_app_self (n : ℤ)
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) :
    IsIso ((compactSupportGradedToTrunc Λ f j kbar n n).app K) := by
  let M := K.obj.truncGE n
  let S := M.shortComplexTruncLE n
  have hS : S.ShortExact := M.shortComplexTruncLE_shortExact n
  have h₁ : CochainComplex.plus _ S.X₁ := ((CochainComplex.Plus.gradedFunctor n).obj K).property
  have h₂ : CochainComplex.plus _ S.X₂ := ((CochainComplex.Plus.truncGEFunctor n).obj K).property
  have h₃ : CochainComplex.plus _ S.X₃ := plus_shortComplexTruncLE_X₃ Λ n K
  -- `S.X₃` is quasi-isomorphic to `τ_{≥ n+1} τ_{≥ n} K`, which has no `Hⁱ_c` for `i < n + 1`
  have hz : ∀ i : ℤ, i < n + 1 → IsZero ((DerivedCategory.Plus.homologyFunctor
      (ModuleCat.{u + 1} Λ) i).obj ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).obj
        ⟨S.X₃, h₃⟩)) := fun i hi => by
    have := isIso_compactSupportFrobeniusFunctor_map_shortComplexTruncLEX₃ToTruncGE Λ f j kbar n K
    exact (isZero_compactSupportTruncHomology Λ f j kbar (n + 1) i hi
      ((CochainComplex.Plus.truncGEFunctor n).obj K)).of_iso
      ((DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) i).mapIso
        (asIso ((compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar).map
          (ObjectProperty.homMk (M.shortComplexTruncLEX₃ToTruncGE n (n + 1) rfl) :
            (⟨S.X₃, h₃⟩ : CochainComplex.Plus _) ⟶ (CochainComplex.Plus.truncGEFunctor (n + 1)).obj
              ((CochainComplex.Plus.truncGEFunctor n).obj K)))))
  exact isIso_homology_compactSupportFrobeniusFunctor_map_f_of_isZero Λ f j kbar hS h₁ h₂ h₃ n
    (hz _ (by omega)) (hz _ (by omega))

end General

/-! ### Dimension zero -/

/-- The bounded below complexes `K` of sheaves of `Λ`-modules on `X_étale` with `Hⁿ(K) = 0` for
`n < 0` and every `Hⁿ(K)` killed by a positive integer. -/
def torsionHomologyNonneg (Λ : Type) [Ring Λ] (X : Scheme.{u}) :
    ObjectProperty (CochainComplex.Plus (EtaleModules.{u, 0} Λ X)) := fun K =>
  K.obj.IsGE 0 ∧ ∀ n : ℤ, ∃ m : ℕ, 0 < m ∧
    m • 𝟙 ((HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) n).obj K.obj) = 0

section DimensionZero

variable (Λ : Type) [CommRing Λ] {k : Type u} [Field k] [Fintype k] {X : Scheme.{u}}
  (f : X ⟶ Spec (.of k)) [LocallyOfFiniteType f] [QuasiCompact f] [IsSeparated f]
  (j : CompactificationOf (Over.mk f)) (kbar : Type u) [Field kbar] [IsAlgClosed kbar]
  [Algebra k kbar] (hdim : topologicalKrullDim X ≤ 0)

include hdim in
/-- In dimension zero the graded piece `τ_{≤ n} τ_{≥ n} K` of a complex with torsion cohomology
has no `Hⁱ_c` for `i > n`: it is `H^{i-n}_c(X_k̄, Hⁿ(K))`. -/
theorem isZero_compactSupportGradedHomology_of_lt
    (K : CochainComplex.Plus (EtaleModules.{u, 0} Λ X))
    (hK : torsionHomologyNonneg Λ X K) (n i : ℤ) (h : n < i) :
    IsZero ((compactSupportGradedHomology Λ f j kbar n i).obj K) := by
  obtain ⟨m, hm, hG⟩ := hK.2 n
  exact (isZero_compactSupportFrobeniusCohomologyGroup_single_of_nsmul_eq_zero f j kbar Λ _ m hm hG
    0 (by simpa using hdim) (-n + i) (by omega)).of_iso
    ((compactSupportGradedHomologyIso Λ f j kbar n i (-n + i) rfl).app K)

include hdim in
/-- The truncation maps `Hʳ_c(X_k̄, τ_{≥ 0} K) ⟶ ⋯ ⟶ Hʳ_c(X_k̄, τ_{≥ n} K)`, `n ≤ r`, on complexes
with torsion cohomology in degrees `≥ 0`, in dimension zero: isomorphisms. -/
def compactSupportTruncChainIso (r : ℕ) : (n : ℕ) → n ≤ r →
    ((torsionHomologyNonneg Λ X).ι ⋙ compactSupportTruncHomology Λ f j kbar 0 r ≅
      (torsionHomologyNonneg Λ X).ι ⋙ compactSupportTruncHomology Λ f j kbar n r)
  | 0, _ => Iso.refl _
  | n + 1, h =>
    haveI : IsIso (Functor.whiskerLeft (torsionHomologyNonneg Λ X).ι
        (compactSupportTruncToTrunc Λ f j kbar n r)) :=
      @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
        (fun K => isIso_compactSupportTruncToTrunc_app Λ f j kbar n r K.1
          (isZero_compactSupportGradedHomology_of_lt Λ f j kbar hdim K.1 K.2 n r (by omega))
          (isZero_compactSupportGradedHomology_of_lt Λ f j kbar hdim K.1 K.2 n (r + 1)
            (by omega)))
    compactSupportTruncChainIso r n (by omega) ≪≫
      asIso (Functor.whiskerLeft (torsionHomologyNonneg Λ X).ι
        (compactSupportTruncToTrunc Λ f j kbar n r))

include hdim in
/-- **`Hʳ_c(X_k̄, K) ≅ H⁰_c(X_k̄, Hʳ(K))` in dimension zero**, naturally in a bounded below complex
`K` with `Hⁿ(K) = 0` for `n < 0` and torsion cohomology sheaves: through the truncations
`τ_{≥ 0} K, …, τ_{≥ r} K` and the graded piece `τ_{≤ r} τ_{≥ r} K = Hʳ(K)[-r]`. -/
def compactSupportDimensionZeroHomologyIso (r : ℕ) :
    (torsionHomologyNonneg Λ X).ι ⋙ compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) r ≅
      (torsionHomologyNonneg Λ X).ι ⋙ (CochainComplex.Plus.ι (EtaleModules.{u, 0} Λ X) ⋙
        HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) r) ⋙
        (Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, 0} Λ X)).functor 0 ⋙
        compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
        DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) 0 :=
  haveI : IsIso (Functor.whiskerLeft (torsionHomologyNonneg Λ X).ι
      (Functor.whiskerRight (CochainComplex.Plus.πTruncGE 0)
        (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) r))) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _ (fun K => by
      have := K.2.1
      exact isIso_compactSupport_πTruncGE_zero Λ f j kbar r K.1)
  haveI : IsIso (Functor.whiskerLeft (torsionHomologyNonneg Λ X).ι
      (compactSupportGradedToTrunc Λ f j kbar r r)) :=
    @NatIso.isIso_of_isIso_app _ _ _ _ _ _ _
      (fun K => isIso_compactSupportGradedToTrunc_app_self Λ f j kbar r K.1)
  asIso (Functor.whiskerLeft (torsionHomologyNonneg Λ X).ι
      (Functor.whiskerRight (CochainComplex.Plus.πTruncGE 0)
        (compactSupportFrobeniusFunctor.{u, 0} Λ f j kbar ⋙
          DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) r))) ≪≫
    compactSupportTruncChainIso Λ f j kbar hdim r r le_rfl ≪≫
    (asIso (Functor.whiskerLeft (torsionHomologyNonneg Λ X).ι
      (compactSupportGradedToTrunc Λ f j kbar r r))).symm ≪≫
    Functor.isoWhiskerLeft (torsionHomologyNonneg Λ X).ι
      (compactSupportGradedHomologyIso Λ f j kbar r r 0 (by omega))

section Frobenius

variable (p q : ℕ) [Fact p.Prime] [CharP k p] (hcard : Fintype.card k = p ^ q)

/-- **Pasting two intertwining squares along a composite of isomorphisms.** -/
alias comp_trans_hom_eq_of_comm := Stacks.EtaleCohomology.comp_trans_hom

/-- **An intertwining square for an isomorphism gives one for its inverse.** -/
theorem comp_symm_hom_eq_of_comm {𝒞 : Type*} [Category* 𝒞] {A₁ A₂ : 𝒞} (e : A₁ ≅ A₂)
    (a₁ : A₁ ⟶ A₁) (a₂ : A₂ ⟶ A₂) (h : a₁ ≫ e.hom = e.hom ≫ a₂) :
    a₂ ≫ e.symm.hom = e.symm.hom ≫ a₁ := by
  rw [Iso.symm_hom, Iso.eq_inv_comp, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id,
    Category.comp_id]

/-- The chain of truncation isomorphisms commutes with the geometric Frobenius. -/
theorem compactSupportTruncChainIso_hom_frobenius (r : ℕ) (n : ℕ) (h : n ≤ r) :
    Functor.whiskerLeft (torsionHomologyNonneg Λ X).ι
        (compactSupportFrobeniusAlong Λ f j kbar p q hcard
          (CochainComplex.Plus.truncGEFunctor 0) r) ≫
      (compactSupportTruncChainIso Λ f j kbar hdim r n h).hom =
    (compactSupportTruncChainIso Λ f j kbar hdim r n h).hom ≫
      Functor.whiskerLeft (torsionHomologyNonneg Λ X).ι
        (compactSupportFrobeniusAlong Λ f j kbar p q hcard
          (CochainComplex.Plus.truncGEFunctor n) r) := by
  induction n with
  | zero =>
    show _ ≫ 𝟙 _ = 𝟙 _ ≫ _
    rw [Category.comp_id, Category.id_comp]
    rfl
  | succ n ih =>
    refine comp_trans_hom_eq_of_comm _ _ _ _ _ (ih (by omega)) ?_
    exact NatTrans.ext (funext fun K =>
      NatTrans.congr_app (compactSupportTruncToTrunc_frobenius Λ f j kbar p q hcard n r) K.1)

/-- **The isomorphism `Hʳ_c(X_k̄, K) ≅ H⁰_c(X_k̄, Hʳ(K))` commutes with the geometric
Frobenius** `π_X^*`. -/
theorem compactSupportDimensionZeroHomologyIso_hom_frobenius (r : ℕ) :
    Functor.whiskerLeft (torsionHomologyNonneg Λ X).ι
        (Functor.whiskerRight (canonicalCompactSupportFrobeniusNatTrans.{u, 0} Λ f j kbar p q hcard)
          (DerivedCategory.Plus.homologyFunctor (ModuleCat.{u + 1} Λ) r)) ≫
      (compactSupportDimensionZeroHomologyIso Λ f j kbar hdim r).hom =
    (compactSupportDimensionZeroHomologyIso Λ f j kbar hdim r).hom ≫
      Functor.whiskerLeft (torsionHomologyNonneg Λ X).ι
        (Functor.whiskerLeft (CochainComplex.Plus.ι (EtaleModules.{u, 0} Λ X) ⋙
          HomologicalComplex.homologyFunctor _ (ComplexShape.up ℤ) r)
          (compactSupportFrobeniusAlong Λ f j kbar p q hcard
            ((Stacks.DerivedIndexing.cplusSingleFunctors (EtaleModules.{u, 0} Λ X)).functor 0)
            0)) := by
  refine comp_trans_hom_eq_of_comm _ _ _ (Functor.whiskerLeft (torsionHomologyNonneg Λ X).ι
      (compactSupportFrobeniusAlong Λ f j kbar p q hcard
        (CochainComplex.Plus.truncGEFunctor 0) r)) _ ?_ ?_
  · exact NatTrans.ext (funext fun K => NatTrans.congr_app
      (compactSupportFrobeniusAlong_whiskerRight Λ f j kbar p q hcard
        (CochainComplex.Plus.πTruncGE 0) r) K.1)
  refine comp_trans_hom_eq_of_comm _ _ _ (Functor.whiskerLeft (torsionHomologyNonneg Λ X).ι
      (compactSupportFrobeniusAlong Λ f j kbar p q hcard
        (CochainComplex.Plus.truncGEFunctor r) r)) _
    (compactSupportTruncChainIso_hom_frobenius Λ f j kbar hdim p q hcard r r le_rfl) ?_
  refine comp_trans_hom_eq_of_comm _ _ _ (Functor.whiskerLeft (torsionHomologyNonneg Λ X).ι
      (compactSupportFrobeniusAlong Λ f j kbar p q hcard
        (CochainComplex.Plus.gradedFunctor r) r)) _ ?_ ?_
  · exact comp_symm_hom_eq_of_comm _ _ _ (NatTrans.ext (funext fun K => NatTrans.congr_app
      (compactSupportGradedToTrunc_frobenius Λ f j kbar p q hcard r r) K.1))
  · exact NatTrans.ext (funext fun K => NatTrans.congr_app
      (compactSupportGradedHomologyIso_hom_frobenius Λ f j kbar p q hcard r r 0 (by omega)) K.1)

end Frobenius

end DimensionZero

end Stacks.EtaleCohomology
