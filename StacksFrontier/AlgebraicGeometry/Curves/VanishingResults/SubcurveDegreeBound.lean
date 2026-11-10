module

public import StacksFrontier.AlgebraicGeometry.Curves.VanishingResults.SubcurveSelection

/-!
# A degree bound on a subcurve

Let `k` be a field and `X` a proper reduced scheme of dimension one over `k`. For an invertible
`𝒪_X`-module `ℒ` and a zero-dimensional closed subscheme `Z ⊆ X` with ideal `ℐ`, [Stacks, Tag
0E3E] asserts that if `H¹(X, ℐℒ) ≠ 0` then some reduced connected one-dimensional closed
subscheme `Y ⊆ X` satisfies

  `deg(ℒ|_Y) ≤ -2 χ(Y, 𝒪_Y) + deg(Z ∩ Y)`.

## Main results

* `AlgebraicGeometry.eulerCharacteristic_tensorLeft_coimage_idealToClosedSubscheme`:
  `χ(ℒ ⊗ ℐ𝒪_Y) = χ(Y, ℒ|_Y) - deg(Z ∩ Y)`.
* `AlgebraicGeometry.finrank_cohomologyOverField_zero_le_of_mono_dualizingSheaf`: a module
  annihilated by `ℐ_Y` embedded in `ω_X` has at most `h¹(Y, 𝒪_Y)` independent sections.
* `AlgebraicGeometry.finrank_globalSections_le_finrank_cohomologyOverField_one`: one with a
  nonzero map to `ω_X` on a reduced connected `Y` has `h¹ ≥ [Γ(Y, 𝒪_Y) : k] = h⁰(Y, 𝒪_Y)`.
* `AlgebraicGeometry.exists_subcurve_invertibleCurveDegree_le_of_not_isZero_cohomology_idealTwist`:
  **[Stacks, Tag 0E3E]**.

## Implementation notes

The subcurve is produced by
`AlgebraicGeometry.Scheme.IdealSheafData.exists_isPreconnected_mono`, with an injection
`ℒ ⊗ ℐ𝒪_Y ⟶ ω_X`. The source concludes from the exact sequence `0 ⟶ ℐ'ℒ|_Y ⟶ ω_Y ⟶ 𝒬 ⟶ 0` and
`χ(ω_Y) = -χ(𝒪_Y)` ([Stacks, Tag 0BS5]); here the two halves of that equality that are needed
are proved directly for the module `ℳ = ℒ ⊗ ℐ𝒪_Y`: `h⁰(ℳ) ≤ h¹(Y, 𝒪_Y)` by duality on `X`, and
`h¹(ℳ) ≥ h⁰(Y, 𝒪_Y)` because `H¹(ℳ)` is a nonzero vector space over the field `Γ(Y, 𝒪_Y)`. So
`χ(ℳ) ≤ -χ(Y, 𝒪_Y)`, and `χ(ℳ) = χ(Y, ℒ|_Y) - deg(Z ∩ Y)`.

The scheme-theoretic intersection `Z ∩ Y` is the closed subscheme `Z ⊔ Y` cut out by the sum of
the two ideal sheaves, and its degree is `dim_k Γ(Z ∩ Y, 𝒪)`, as for `deg(Z)` in
[Stacks, Tag 0E3A]. The ideal twist `ℐℒ` is `ℒ ⊗ ℐ`, as in
`AlgebraicGeometry.CohenMacaulayCurveSituation.idealTwist`. The hypothesis of the source that `X`
is connected is not used.

## References

* [Stacks Project, Tag 0E3E](https://stacks.math.columbia.edu/tag/0E3E)
* [Stacks Project, Tag 0BS2](https://stacks.math.columbia.edu/tag/0BS2)
* [Stacks Project, Tag 0BS5](https://stacks.math.columbia.edu/tag/0BS5)
* [Stacks Project, Tag 0C6P](https://stacks.math.columbia.edu/tag/0C6P)
* [Stacks Project, Tag 0AYT](https://stacks.math.columbia.edu/tag/0AYT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry

variable {X : Scheme.{u}}

/-! ### Bounds for a module on a closed subscheme embedded in the dualizing sheaf -/

/-- A closed subscheme has the same dimension as its support. -/
alias Scheme.IdealSheafData.topologicalKrullDim_support := topologicalKrullDim_support_eq

/-- The scheme-theoretic intersection with a zero-dimensional closed subscheme is
zero-dimensional. -/
theorem Scheme.IdealSheafData.topologicalKrullDim_sup_le_zero {Z : X.IdealSheafData}
    (hZ : topologicalKrullDim Z.subscheme ≤ 0) (Y : X.IdealSheafData) :
    topologicalKrullDim (Z ⊔ Y).subscheme ≤ 0 :=
  (Scheme.IdealSheafData.inclusion (le_sup_left : Z ≤ Z ⊔ Y)).isClosedEmbedding.isInducing
    |>.topologicalKrullDim_le.trans hZ

/-- **The sequence `0 ⟶ ℐ_Z 𝒪_Y ⟶ 𝒪_Y ⟶ 𝒪_{Z ∩ Y} ⟶ 0` is short exact**, where `ℐ_Z 𝒪_Y` is the
image of `ℐ_Z ⟶ 𝒪_Y`, its coimage, and `Z ∩ Y` the scheme-theoretic intersection `Z ⊔ Y`
(`AlgebraicGeometry.Scheme.IdealSheafData.nonempty_isColimitRestrictionSup`). -/
theorem Scheme.IdealSheafData.shortExact_coimage_restriction (Z Y : X.IdealSheafData) :
    ∃ h : Abelian.factorThruCoimage (idealToClosedSubscheme Z Y) ≫
        closedSubschemeRestriction (le_sup_right : Y ≤ Z ⊔ Y) = 0,
      (ShortComplex.mk _ _ h).ShortExact := by
  have h : Abelian.factorThruCoimage (idealToClosedSubscheme Z Y) ≫
      closedSubschemeRestriction (le_sup_right : Y ≤ Z ⊔ Y) = 0 := by
    apply (cancel_epi (Abelian.coimage.π (idealToClosedSubscheme Z Y))).mp
    rw [← Category.assoc, Abelian.coimage.fac, comp_zero]
    exact kernel_ι_comp_ambientToClosedSubscheme_comp_restriction Z Y
  obtain ⟨hc⟩ := nonempty_isColimitRestrictionSup Z Y
  have := ambientToClosedSubscheme_epi (Z ⊔ Y)
  have : Epi (closedSubschemeRestriction (le_sup_right : Y ≤ Z ⊔ Y)) :=
    epi_of_epi_fac
      (ambientToClosedSubscheme_comp_closedSubschemeRestriction (le_sup_right : Y ≤ Z ⊔ Y))
  refine ⟨h, ShortComplex.ShortExact.mk' ?_ inferInstance this⟩
  apply ShortComplex.exact_of_g_is_cokernel
  refine CokernelCofork.IsColimit.ofπ' _ _ fun {W} k hk => ?_
  have hk' : idealToClosedSubscheme Z Y ≫ k = 0 := by
    rw [← Abelian.coimage.fac (idealToClosedSubscheme Z Y), Category.assoc]
    exact (congrArg (fun t => Abelian.coimage.π (idealToClosedSubscheme Z Y) ≫ t) hk).trans
      comp_zero
  exact CokernelCofork.IsColimit.desc' hc k hk'

/-- Tensoring with an invertible module is an equivalence. -/
private theorem isEquivalence_tensorLeft_of_isInvertible (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] :
    (Scheme.Modules.tensorLeft L).IsEquivalence :=
  (Stacks.SheafOfModules.isInvertible_iff_tensorLeftFunctor_isEquivalence _ _ L).mp hL

/-- Tensoring a coherent module with an invertible module gives a coherent module. -/
private theorem isCoherent_tensorLeft_obj_of_isInvertible [IsLocallyNoetherian X] (L : X.Modules)
    [SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] {M : X.Modules}
    (hM : M.IsCoherent) : ((Scheme.Modules.tensorLeft L).obj M).IsCoherent :=
  @SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace L M
    (Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L) hM

/-- **`χ(ℒ ⊗ ℐ_Z 𝒪_Y) = χ(Y, ℒ|_Y) - deg(Z ∩ Y)`** for a zero-dimensional `Z`: tensoring the
short exact sequence `0 ⟶ ℐ_Z 𝒪_Y ⟶ 𝒪_Y ⟶ 𝒪_{Z ∩ Y} ⟶ 0` with `ℒ`, the middle term has the Euler
characteristic of `ℒ|_Y` by the projection formula, and the last one that of `𝒪_{Z ∩ Y}`,
whose global sections have dimension `deg(Z ∩ Y)` ([Stacks, Tag 0AYT]). -/
theorem eulerCharacteristic_tensorLeft_coimage_idealToClosedSubscheme {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L] (Z Y : X.IdealSheafData)
    (hZ : topologicalKrullDim Z.subscheme ≤ 0)
    (hC : ((Scheme.Modules.tensorLeft L).obj
      (Abelian.coimage (Scheme.IdealSheafData.idealToClosedSubscheme Z Y))).IsCoherent) :
    letI : Algebra k Γ((Z ⊔ Y).subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ ((Z ⊔ Y).subschemeι ≫ f).appTop).hom.toAlgebra
    @eulerCharacteristic k _ X f _ _ hC =
      (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
          ((Scheme.Modules.pullback Y.subschemeι).obj L) n) : ℤ)) -
        (Module.finrank k Γ((Z ⊔ Y).subscheme, ⊤) : ℤ) := by
  let : Algebra k Γ((Z ⊔ Y).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ ((Z ⊔ Y).subschemeι ≫ f).appTop).hom.toAlgebra
  have := isEquivalence_tensorLeft_of_isInvertible L
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hLc : L.IsCoherent := Stacks.AlgebraicGeometry.CoherentKernel.isCoherent_of_isInvertible X L
  obtain ⟨h0, hS⟩ := Scheme.IdealSheafData.shortExact_coimage_restriction Z Y
  have hOY := Scheme.IdealSheafData.isCoherent_closedSubschemeStructureSheaf Y
  have hOW := Scheme.IdealSheafData.isCoherent_closedSubschemeStructureSheaf (Z ⊔ Y)
  have h1 : (ShortComplex.map (ShortComplex.mk _ _ h0)
      (Scheme.Modules.tensorLeft L)).X₁.IsCoherent :=
    hC
  have h2 : (ShortComplex.map (ShortComplex.mk _ _ h0)
      (Scheme.Modules.tensorLeft L)).X₂.IsCoherent :=
    isCoherent_tensorLeft_obj_of_isInvertible L hOY
  have h3 : (ShortComplex.map (ShortComplex.mk _ _ h0)
      (Scheme.Modules.tensorLeft L)).X₃.IsCoherent :=
    isCoherent_tensorLeft_obj_of_isInvertible L hOW
  have hadd := eulerCharacteristic_add_of_shortExact k f
    (hS.map_of_exact (Scheme.Modules.tensorLeft L))
  -- The middle term.
  have hYloc : IsLocallyNoetherian Y.subscheme :=
    isLocallyNoetherian_of_isClosedImmersion Y.subschemeι
  have hunitY : (SheafOfModules.unit Y.subscheme.ringCatSheaf).IsCoherent :=
    Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit
  have hpull : ((Scheme.Modules.pullback Y.subschemeι).obj L).IsCoherent :=
    isCoherent_pullback Y.subschemeι L
  have hmid : @eulerCharacteristic k _ X f _ _ h2 =
      ∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
          ((Scheme.Modules.pullback Y.subschemeι).obj L) n) : ℤ) := by
    rw [@eulerCharacteristic_eq_of_iso k _ X f _ _ _ h2
      (@SheafOfModules.tensorSheaf_isCoherent X.toRingedSpace _ L hOY hLc)
      (Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap X.toRingedSpace L
        (Scheme.IdealSheafData.closedSubschemeStructureSheaf Y)),
      eulerCharacteristic_tensorSheaf_pushforward_unit_of_isClosedImmersion k Y.subschemeι f L
        hLc hunitY hOY hpull, eulerCharacteristic_eq_finsum]
  -- The last term.
  have hWdim := Scheme.IdealSheafData.topologicalKrullDim_sup_le_zero hZ Y
  have hsuppW : topologicalKrullDim (_root_.SheafOfModules.supp
      (Scheme.IdealSheafData.closedSubschemeStructureSheaf (Z ⊔ Y))) ≤ 0 := by
    rw [Scheme.IdealSheafData.supp_closedSubschemeStructureSheaf,
      Scheme.IdealSheafData.topologicalKrullDim_support]
    exact hWdim
  have : SheafOfModules.IsFiniteLocallyFreeOfRank.{u, u, u} L 1 :=
    Stacks.SheafRankOne.isFiniteLocallyFreeOfRank_one_of_isInvertible_scheme X L
  obtain ⟨hT, hχ⟩ := @exists_eulerCharacteristic_tensorSheaf_eq_mul_of_isFiniteLocallyFreeOfRank
    X k _ f _ L _ 1 _ hOW hsuppW
  have : IsFinite ((Z ⊔ Y).subschemeι ≫ f) :=
    isFinite_of_isProper_of_topologicalKrullDim_le_zero _ hWdim
  have : IsAffine (Z ⊔ Y).subscheme := isAffine_of_isAffineHom ((Z ⊔ Y).subschemeι ≫ f)
  have : IsLocallyNoetherian (Z ⊔ Y).subscheme :=
    isLocallyNoetherian_of_isClosedImmersion (Z ⊔ Y).subschemeι
  have hlast : @eulerCharacteristic k _ X f _ _ h3 =
      (Module.finrank k Γ((Z ⊔ Y).subscheme, ⊤) : ℤ) := by
    refine hχ.trans ?_
    rw [Nat.cast_one, one_mul, eulerCharacteristic_pushforward_of_isClosedImmersion k
      (Z ⊔ Y).subschemeι f _ Stacks.AlgebraicGeometry.CoherentOfFiniteType.isCoherent_unit hOW]
    exact (eulerCharacteristic_eq_finsum _ _ _).trans
      (finsum_alternating_finrank_unit_eq_finrank_of_isAffine _)
  change @eulerCharacteristic k _ X f _ _ h2 =
    @eulerCharacteristic k _ X f _ _ h1 + @eulerCharacteristic k _ X f _ _ h3 at hadd
  change @eulerCharacteristic k _ X f _ _ h1 = _
  rw [← hmid, hadd, hlast]
  ring

section Bounds

variable {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [IsProper f]

/-- **`h⁰(X, ℳ) ≤ h¹(Y, 𝒪_Y)` for a module `ℳ` annihilated by `ℐ_Y` embedded in `ω_X`.** Global
sections of `ℳ` are maps `𝒪_X ⟶ ℳ`, which factor through `𝒪_Y`; composing with the embedding into
`ω_X` is injective, and maps `𝒪_Y ⟶ ω_X` are linear forms on `H¹(X, 𝒪_Y) = H¹(Y, 𝒪_Y)` by clause
(5) of [Stacks, Tag 0BS2]. -/
theorem finrank_cohomologyOverField_zero_le_of_mono_dualizingSheaf
    (hdim : topologicalKrullDim X ≤ 1) (Y : X.IdealSheafData) {M : X.Modules}
    (hM : (Scheme.Modules.pushforward Y.subschemeι).essImage M)
    (ψ : M ⟶ Stacks.Duality.dualizingSheafOverField f) [Mono ψ] :
    Module.finrank k (cohomologyOverField k f M 0) ≤
      Module.finrank k (cohomologyOverField k (Y.subschemeι ≫ f)
        (SheafOfModules.unit Y.subscheme.ringCatSheaf) 1) := by
  let := modulesLinearOverField k f
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hOc := Scheme.IdealSheafData.isCoherent_closedSubschemeStructureSheaf Y
  have hOq : (Scheme.IdealSheafData.closedSubschemeStructureSheaf Y).IsQuasicoherent :=
    isQuasicoherent_of_isCoherent _
  have := @finiteDimensional_cohomologyOverField_of_isProper k _ X f _
    (Scheme.IdealSheafData.closedSubschemeStructureSheaf Y) hOc 1
  let D := Stacks.Duality.homDualizingSheafLinearEquiv f hdim
    (Scheme.IdealSheafData.closedSubschemeStructureSheaf Y) hOq
  have : FiniteDimensional k
      (Scheme.IdealSheafData.closedSubschemeStructureSheaf Y ⟶
        Stacks.Duality.dualizingSheafOverField f) :=
    LinearEquiv.finiteDimensional D.symm
  let R := Linear.rightComp k (Scheme.IdealSheafData.closedSubschemeStructureSheaf Y) ψ
  have hR : Function.Injective R := fun _ _ => (cancel_mono ψ).mp
  have : FiniteDimensional k (Scheme.IdealSheafData.closedSubschemeStructureSheaf Y ⟶ M) :=
    FiniteDimensional.of_injective R hR
  let P := Linear.leftComp k M (Scheme.IdealSheafData.ambientToClosedSubscheme Y)
  have hP : Function.Surjective P := fun g => by
    have := Scheme.IdealSheafData.ambientToClosedSubscheme_epi Y
    exact ⟨Abelian.epiDesc _ g (Scheme.IdealSheafData.kernel_ι_comp_eq_zero_of_essImage Y hM g),
      Abelian.comp_epiDesc (Scheme.IdealSheafData.ambientToClosedSubscheme Y) g _⟩
  calc Module.finrank k (cohomologyOverField k f M 0)
      = Module.finrank k (structureSheafModule X ⟶ M) :=
        (unitHomLinearEquivCohomologyZero k f M).finrank_eq.symm
    _ ≤ Module.finrank k (Scheme.IdealSheafData.closedSubschemeStructureSheaf Y ⟶ M) := by
        have h := LinearMap.finrank_range_le P
        rwa [LinearMap.range_eq_top.mpr hP, finrank_top] at h
    _ ≤ Module.finrank k (Scheme.IdealSheafData.closedSubschemeStructureSheaf Y ⟶
          Stacks.Duality.dualizingSheafOverField f) :=
        LinearMap.finrank_le_finrank_of_injective hR
    _ = Module.finrank k (cohomologyOverField k f
          (Scheme.IdealSheafData.closedSubschemeStructureSheaf Y) 1) := by
        rw [D.finrank_eq, Subspace.dual_finrank_eq]
    _ = _ :=
        (finrank_cohomologyOverField_pushforward_of_isClosedImmersion k Y.subschemeι f _ 1).symm

/-- **`h¹(X, ℳ) ≥ [Γ(Y, 𝒪_Y) : k]` for a module `ℳ = i_* 𝒩` on a reduced connected closed subscheme
`Y` with a nonzero map to `ω_X`.** By clause (5) of [Stacks, Tag 0BS2] the map is a nonzero linear
form on `H¹(X, ℳ) = H¹(Y, 𝒩)`, which is a vector space over the field `Γ(Y, 𝒪_Y)`. -/
theorem finrank_globalSections_le_finrank_cohomologyOverField_one
    (hdim : topologicalKrullDim X ≤ 1) (Y : X.IdealSheafData) [IsReduced Y.subscheme]
    [ConnectedSpace Y.subscheme] {M : X.Modules} (hMc : M.IsCoherent)
    (hM : (Scheme.Modules.pushforward Y.subschemeι).essImage M)
    (ψ : M ⟶ Stacks.Duality.dualizingSheafOverField f) (hψ : ψ ≠ 0) :
    letI : Algebra k Γ(Y.subscheme, ⊤) :=
      ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y.subschemeι ≫ f).appTop).hom.toAlgebra
    Module.finrank k Γ(Y.subscheme, ⊤) ≤ Module.finrank k (cohomologyOverField k f M 1) := by
  let : Algebra k Γ(Y.subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ (Y.subschemeι ≫ f).appTop).hom.toAlgebra
  obtain ⟨N, ⟨e⟩⟩ := hM
  have hne : Nontrivial (cohomologyOverField k f M 1) := by
    by_contra h
    rw [not_nontrivial_iff_subsingleton] at h
    apply hψ
    refine (Stacks.Duality.homDualizingSheafAddEquiv f hdim M
      (isQuasicoherent_of_isCoherent M)).injective ?_
    rw [map_zero]
    exact ModuleCat.hom_ext
      (LinearMap.ext fun v => by rw [Subsingleton.elim v 0, map_zero, map_zero])
  have := @finiteDimensional_cohomologyOverField_of_isProper k _ X f _ M hMc 1
  have hdvd := finrank_globalSections_dvd_finrank_cohomologyOverField k (Y.subschemeι ≫ f)
    (isField_globalSections_of_isReduced_of_connectedSpace k (Y.subschemeι ≫ f)) N 1
  rw [finrank_cohomologyOverField_pushforward_of_isClosedImmersion k Y.subschemeι f N 1,
    finrank_cohomologyOverField_eq_of_iso k f e 1] at hdvd
  exact Nat.le_of_dvd Module.finrank_pos hdvd

end Bounds

/-- A dimension at most one which is not at most zero is one. -/
theorem _root_.WithBot.eq_one_of_le_one_of_not_le_zero {x : WithBot ℕ∞} (h1 : x ≤ 1)
    (h0 : ¬ x ≤ 0) : x = 1 := by
  induction x using WithBot.recBotCoe with
  | bot => exact absurd bot_le h0
  | coe n =>
    have h1' : n ≤ 1 := by exact_mod_cast h1
    have h0' : ¬ n ≤ 0 := fun h => h0 (by exact_mod_cast h)
    obtain rfl : n = 1 := le_antisymm h1' (Order.one_le_iff_ne_zero.mpr fun h => h0' h.le)
    rfl

/-! ### Tag 0E3E -/

/-- **The degree bound on a subcurve, relative to a closed set `T₀`.** Let `X` be proper of
dimension at most one over a field `k`, `ℒ` invertible, `Z` a zero-dimensional closed subscheme
and `φ : ℒ ⊗ ℐ_Z ⟶ ω_X` nonzero, killing `ℒ ⊗ (ℐ_Z ∩ ℐ_{T₀})` for a closed set `T₀`. Then there is
a connected closed set `T ⊆ T₀` of dimension one whose reduced structure `Y` satisfies
`deg(ℒ|_Y) ≤ -2 χ(Y, 𝒪_Y) + deg(Z ∩ Y)`.

The twist `ℐ_Z ⟶ ℒ^{-1} ⊗ ω_X` of `φ` gives `T`
(`AlgebraicGeometry.Scheme.IdealSheafData.exists_isPreconnected_mono`) with an injection
`ℒ ⊗ ℐ𝒪_Y ⟶ ω_X`, whence `χ(ℒ ⊗ ℐ𝒪_Y) ≤ -χ(Y, 𝒪_Y)`; and
`χ(ℒ ⊗ ℐ𝒪_Y) = χ(Y, ℒ|_Y) - deg(Z ∩ Y)`. -/
theorem exists_le_invertibleCurveDegree_le_of_ne_zero {k : Type u} [Field k]
    (f : X ⟶ Spec (.of k)) [IsProper f] (hdim : topologicalKrullDim X ≤ 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (Z : X.IdealSheafData) (hZ : topologicalKrullDim Z.subscheme ≤ 0)
    (T₀ : TopologicalSpace.Closeds X)
    (φ : (Scheme.Modules.tensorLeft L).obj
        (kernel (Scheme.IdealSheafData.ambientToClosedSubscheme Z)) ⟶
      Stacks.Duality.dualizingSheafOverField f) (hφ : φ ≠ 0)
    (hφ₀ : (Scheme.Modules.tensorLeft L).map (kernel.ι
      (Scheme.IdealSheafData.idealToClosedSubscheme Z
        (Scheme.IdealSheafData.vanishingIdeal T₀))) ≫ φ = 0) :
    ∃ T : TopologicalSpace.Closeds X, T ≤ T₀ ∧ _root_.IsPreconnected (T : Set X) ∧
      ∃ (hY : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal T).subscheme = 1),
      ConnectedSpace (Scheme.IdealSheafData.vanishingIdeal T).subscheme ∧
      letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback
        (Scheme.IdealSheafData.vanishingIdeal T).subschemeι L hL
      letI : Algebra k Γ((Z ⊔ Scheme.IdealSheafData.vanishingIdeal T).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫
          ((Z ⊔ Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f).appTop).hom.toAlgebra
      invertibleCurveDegree k ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f) hY.le
          ((Scheme.Modules.pullback (Scheme.IdealSheafData.vanishingIdeal T).subschemeι).obj L) ≤
        -2 * (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
          ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f)
          (SheafOfModules.unit
            (Scheme.IdealSheafData.vanishingIdeal T).subscheme.ringCatSheaf) n) : ℤ)) +
          (Module.finrank k Γ((Z ⊔ Scheme.IdealSheafData.vanishingIdeal T).subscheme, ⊤) : ℤ) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have : IsNoetherian X := isNoetherian_of_locallyOfFiniteType f
  have := isEquivalence_tensorLeft_of_isInvertible L
  let E := (Scheme.Modules.tensorLeft L).asEquivalence
  let ω := Stacks.Duality.dualizingSheafOverField f
  -- The twist `ℐ ⟶ ℒ^{-1} ⊗ ω_X` of `φ`.
  have hφ' : (E.toAdjunction.homEquiv _ _) φ ≠ 0 := fun h0 => hφ (by
    rw [← (E.toAdjunction.homEquiv _ _).symm_apply_apply φ, h0, Adjunction.homEquiv_counit,
      Functor.map_zero, zero_comp])
  have hφ₀' : kernel.ι (Scheme.IdealSheafData.idealToClosedSubscheme Z
      (Scheme.IdealSheafData.vanishingIdeal T₀)) ≫ (E.toAdjunction.homEquiv _ _) φ = 0 := by
    have h1 := E.toAdjunction.homEquiv_naturality_left (kernel.ι
      (Scheme.IdealSheafData.idealToClosedSubscheme Z (Scheme.IdealSheafData.vanishingIdeal T₀))) φ
    refine h1.symm.trans ((congrArg (E.toAdjunction.homEquiv _ _) hφ₀).trans ?_)
    exact (E.toAdjunction.homEquiv_unit _ _ _).trans
      (by convert comp_zero using 2; exact E.inverse.map_zero _ _)
  have hω' := Scheme.Modules.noZeroDimensionalImages_inverse_tensorLeft L
    (Stacks.Duality.noZeroDimensionalImages_dualizingSheafOverField f hdim)
  obtain ⟨T, hTT₀, hTconn, hTdim, ψ', hmono, hψ'⟩ :=
    Scheme.IdealSheafData.exists_isPreconnected_mono hdim Z hω' T₀ _ hφ' hφ₀'
  let β := Scheme.IdealSheafData.idealToClosedSubscheme Z (Scheme.IdealSheafData.vanishingIdeal T)
  -- The injection `ℒ ⊗ ℐ𝒪_Y ⟶ ω_X`.
  have : Mono (E.functor.map ψ') := E.functor.map_mono ψ'
  have hcm : Mono (E.counit.app ω) := inferInstanceAs (Mono (E.counitIso.app ω).hom)
  have hmψ : Mono (E.functor.map ψ' ≫ E.counit.app ω) := mono_comp _ _
  have hψ : E.functor.map ψ' ≫ E.counit.app ω ≠ 0 := fun h0 => hψ' (E.functor.map_injective (by
    rw [Functor.map_zero]
    exact (cancel_mono (E.counit.app ω)).mp (by rwa [zero_comp])))
  -- `(Scheme.IdealSheafData.vanishingIdeal T)` is reduced, connected and of dimension one.
  have hsT : ((Scheme.IdealSheafData.vanishingIdeal T).support : Set X) = T :=
    Scheme.IdealSheafData.coe_support_vanishingIdeal T
  have hY1 : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal T).subscheme = 1 := by
    rw [← Scheme.IdealSheafData.topologicalKrullDim_support, hsT]
    exact WithBot.eq_one_of_le_one_of_not_le_zero
      ((topologicalKrullDim_subspace_le X T).trans hdim) hTdim
  have hYne : Nonempty (Scheme.IdealSheafData.vanishingIdeal T).subscheme := by
    by_contra hne
    rw [not_nonempty_iff] at hne
    have : IsEmpty (TopologicalSpace.IrreducibleCloseds
        (Scheme.IdealSheafData.vanishingIdeal T).subscheme) :=
      ⟨fun c => hne.elim c.isIrreducible.nonempty.some⟩
    have h1 : topologicalKrullDim (Scheme.IdealSheafData.vanishingIdeal T).subscheme = ⊥ :=
      Order.krullDim_eq_bot
    rw [h1] at hY1
    exact absurd hY1 (by decide)
  have hYconn : ConnectedSpace (Scheme.IdealSheafData.vanishingIdeal T).subscheme := by
    have hrange : Set.range (Scheme.IdealSheafData.vanishingIdeal T).subschemeι.base = T := by
      rw [(Scheme.IdealSheafData.vanishingIdeal T).range_subschemeι, hsT]
    have hpre : _root_.IsPreconnected
        (Set.range (Scheme.IdealSheafData.vanishingIdeal T).subschemeι.base) :=
      hrange ▸ hTconn
    rw [← Set.image_univ] at hpre
    have hu := ((Scheme.IdealSheafData.vanishingIdeal
      T).subschemeι.isClosedEmbedding.isInducing.isPreconnected_image).mp hpre
    exact { toPreconnectedSpace := ⟨hu⟩, toNonempty := hYne }
  refine ⟨T, hTT₀, hTconn, hY1, hYconn, ?_⟩
  -- The numerical bound.
  have := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback
    (Scheme.IdealSheafData.vanishingIdeal T).subschemeι L hL
  let : Algebra k Γ((Z ⊔ (Scheme.IdealSheafData.vanishingIdeal T)).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((Z ⊔ (Scheme.IdealSheafData.vanishingIdeal T)).subschemeι ≫ f).appTop).hom.toAlgebra
  let : Algebra k Γ((Scheme.IdealSheafData.vanishingIdeal T).subscheme, ⊤) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫
      ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f).appTop).hom.toAlgebra
  have hC : ((Scheme.Modules.tensorLeft L).obj (Abelian.coimage β)).IsCoherent :=
    isCoherent_tensorLeft_obj_of_isInvertible L
      (Scheme.IdealSheafData.isCoherent_coimage_idealToClosedSubscheme Z
        (Scheme.IdealSheafData.vanishingIdeal T))
  have hχ := eulerCharacteristic_tensorLeft_coimage_idealToClosedSubscheme f L Z
    (Scheme.IdealSheafData.vanishingIdeal T) hZ hC
  have hOYess : (Scheme.Modules.pushforward
      (Scheme.IdealSheafData.vanishingIdeal T).subschemeι).essImage
      ((Scheme.Modules.tensorLeft L).obj
        (Scheme.IdealSheafData.closedSubschemeStructureSheaf
          (Scheme.IdealSheafData.vanishingIdeal T))) :=
    ⟨_, ⟨(Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso
      (Scheme.IdealSheafData.vanishingIdeal T).subschemeι
      (SheafOfModules.unit (Scheme.IdealSheafData.vanishingIdeal T).subscheme.ringCatSheaf)
      L).symm ≪≫ Stacks.SheafOfModules.TensorPresentations.tensorSheafSwap X.toRingedSpace _ L⟩⟩
  have hMess : (Scheme.Modules.pushforward
      (Scheme.IdealSheafData.vanishingIdeal T).subschemeι).essImage
      ((Scheme.Modules.tensorLeft L).obj (Abelian.coimage β)) :=
    essImage_pushforward_of_mono (Scheme.IdealSheafData.vanishingIdeal T)
      ((Scheme.Modules.tensorLeft L).map (Abelian.factorThruCoimage β)) hOYess
  have hb0 := @finrank_cohomologyOverField_zero_le_of_mono_dualizingSheaf X k _ f _ hdim
    (Scheme.IdealSheafData.vanishingIdeal T) _
    hMess (E.functor.map ψ' ≫ E.counit.app ω) hmψ
  have hb1 := finrank_globalSections_le_finrank_cohomologyOverField_one f hdim
    (Scheme.IdealSheafData.vanishingIdeal T) hC hMess _ hψ
  have hχM : @eulerCharacteristic k _ X f _ _ hC =
      (Module.finrank k (cohomologyOverField k f
        ((Scheme.Modules.tensorLeft L).obj (Abelian.coimage β)) 0) : ℤ) -
      (Module.finrank k (cohomologyOverField k f
        ((Scheme.Modules.tensorLeft L).obj (Abelian.coimage β)) 1) : ℤ) :=
    (eulerCharacteristic_eq_finsum _ _ _).trans
      (finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero _ _ _
        (isZero_cohomologyOverField_two_le k f hdim _))
  have hχY := finsum_alternating_finrank_cohomologyOverField_eq_sub_of_isZero k
    ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f)
    (SheafOfModules.unit (Scheme.IdealSheafData.vanishingIdeal T).subscheme.ringCatSheaf)
    (isZero_cohomologyOverField_two_le k
      ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f) hY1.le _)
  have hΓY := finrank_cohomologyOverField_zero_unit_eq_finrank_globalSections k
    ((Scheme.IdealSheafData.vanishingIdeal T).subschemeι ≫ f)
  unfold invertibleCurveDegree
  rw [hχY]
  rw [hχM] at hχ
  rw [hΓY]
  omega

/-- **Stacks Project, Tag 0E3E.** Let `k` be a field and `X` a proper scheme over `k` which is
reduced and of dimension `1`. Let `ℒ` be an invertible `𝒪_X`-module and `Z ⊆ X` a closed subscheme
of dimension at most zero with ideal sheaf `ℐ`. If `H¹(X, ℐℒ) ≠ 0`, then there is a reduced
connected closed subscheme `Y ⊆ X` of dimension `1` with

  `deg(ℒ|_Y) ≤ -2 χ(Y, 𝒪_Y) + deg(Z ∩ Y)`,

where `Z ∩ Y` is the scheme-theoretic intersection `Z ⊔ Y` and `deg(Z ∩ Y) = dim_k Γ(Z ∩ Y, 𝒪)`.
Here `ℐℒ` is `ℒ ⊗ ℐ`, as in [Stacks, Tag 0E3A]; the source's hypothesis that `X` is connected is
not needed.

A nonzero map `ℐℒ ⟶ ω_X` from duality ([Stacks, Tag 0BS2]) kills nothing more than the zero
module, `X` being reduced, and
`AlgebraicGeometry.exists_le_invertibleCurveDegree_le_of_ne_zero` applies with `T₀ = X`. -/
@[stacks 0E3E]
theorem exists_subcurve_invertibleCurveDegree_le_of_not_isZero_cohomology_idealTwist
    {k : Type u} [Field k] (f : X ⟶ Spec (.of k)) [IsProper f] [IsReduced X]
    (hdim : topologicalKrullDim X = 1) (L : X.Modules)
    [hL : SheafOfModules.IsInvertible X.presheaf X.ringCatSheaf.2 L]
    (Z : X.IdealSheafData) (hZ : topologicalKrullDim Z.subscheme ≤ 0)
    (h : ¬ IsZero (cohomologyOverField k f
      ((((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u}
            ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩).obj L).obj
          (Stacks.ClosedImmersion.idealSheaf Z.subschemeι.toLRSHom.toShHom))) 1)) :
    ∃ (Y : X.IdealSheafData) (_ : IsReduced Y.subscheme) (_ : ConnectedSpace Y.subscheme)
      (hY : topologicalKrullDim Y.subscheme = 1),
      letI := Stacks.AlgebraicGeometry.Tag09NY.isInvertible_modulePullback Y.subschemeι L hL
      letI : Algebra k Γ((Z ⊔ Y).subscheme, ⊤) :=
        ((Scheme.ΓSpecIso (.of k)).inv ≫ ((Z ⊔ Y).subschemeι ≫ f).appTop).hom.toAlgebra
      invertibleCurveDegree k (Y.subschemeι ≫ f) hY.le
          ((Scheme.Modules.pullback Y.subschemeι).obj L) ≤
        -2 * (∑ᶠ n : ℕ, (-1 : ℤ) ^ n * (Module.finrank k (cohomologyOverField k
          (Y.subschemeι ≫ f) (SheafOfModules.unit Y.subscheme.ringCatSheaf) n) : ℤ)) +
          (Module.finrank k Γ((Z ⊔ Y).subscheme, ⊤) : ℤ) := by
  have : IsLocallyNoetherian X := LocallyOfFiniteType.isLocallyNoetherian f
  have hIc := Scheme.IdealSheafData.isCoherent_kernel_ambientToClosedSubscheme Z
  have h' : ¬ IsZero (cohomologyOverField k f ((Scheme.Modules.tensorLeft L).obj
      (kernel (Scheme.IdealSheafData.ambientToClosedSubscheme Z))) 1) := h
  have hq : ((Scheme.Modules.tensorLeft L).obj
      (kernel (Scheme.IdealSheafData.ambientToClosedSubscheme Z))).IsQuasicoherent :=
    @isQuasicoherent_of_isCoherent _ _ _ _
      (isCoherent_tensorLeft_obj_of_isInvertible L hIc)
  obtain ⟨φ, hφ⟩ := Stacks.Duality.exists_ne_zero_hom_dualizingSheaf f hdim.le _ hq h'
  have := isEquivalence_tensorLeft_of_isInvertible L
  obtain ⟨T, -, -, hY1, hYconn, hdeg⟩ :=
    exists_le_invertibleCurveDegree_le_of_ne_zero f hdim.le L Z hZ ⊤ φ hφ (by
      rw [Scheme.IdealSheafData.kernel_ι_idealToClosedSubscheme_vanishingIdeal_top,
        Functor.map_zero, zero_comp])
  exact ⟨_, inferInstance, hYconn, hY1, hdeg⟩

end AlgebraicGeometry

end
