module

public import StacksFrontier.AlgebraicGeometry.Spaces.ProperSupportExtFiniteSiteChange
public import StacksFrontier.AlgebraicGeometry.Spaces.CoherentFinitePresentation

/-!
# Morphisms into a coherent module with proper support over a field

Let `k` be a field, `X` an algebraic space locally of finite type over `Spec k`, `𝒦` a coherent
`𝒪_X`-module and `𝒢` a coherent `𝒪_X`-module whose support is proper over `Spec k`. Then
`Hom(𝒦, 𝒢)` is finite-dimensional over `k`.

As in `StacksFrontier/AlgebraicGeometry/Spaces/ProperSupportExtFinite.lean`, `𝒢` is the direct image
`i_*𝒢'` of a coherent module on a closed subspace `i : Z ⟶ X` proper over `Spec k`, so
`Hom(𝒦, 𝒢) = Hom_Z(i^*𝒦, 𝒢')` by adjunction, finite-dimensional by Stacks 0D0T.

This is the finiteness input of the tangent spaces of `Quot_{F/X/S}` (Remark 0CZW, axiom [3]):
there `𝒦` is the kernel and `𝒢` the quotient of a point of `Quot` over a field.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Abelian

universe u

attribute [local instance 5000] SheafOfModules.instAbelian
attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

/-- If a closed subspace is cut out by the annihilator ideal of `G`, its defining ideal
annihilates `G`. -/
private theorem isPowAnnihilated_one_of_definingIdealSheaf_eq_annihilatorIdealSheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) {X : AlgebraicSpaces B S hS}
    (G : Modules.{u, u} B S hS X.1 X.2) (Z : ClosedSubspaces B S hS X.1)
    (hZ : definingIdealSheaf B S hS X Z = annihilatorIdealSheaf B S hS X G) :
    IsPowAnnihilated B S hS X.1 X.2 (definingIdealSheaf B S hS X Z) 1 G := by
  intro U r hr x
  rw [pow_one] at hr
  have hd : definingIdealAt B S hS X Z (op U) = annihilatorIdealAt B S hS X G (op U) := by
    rw [← definingIdealSheaf_obj B S hS X, ← annihilatorIdealSheaf_obj B S hS X, hZ]
  exact smul_eq_zero_of_mem_annihilatorIdealAt B S hS X G (op U) r (hd ▸ hr) x

section Field

attribute [local instance] modulesLinear

variable (k : Type u) [Field k] (B : BigFppfSite.{u}) (hk : B.Contains (Spec (.of k)))
  {X : AlgebraicSpaces B (Spec (.of k)) hk} (f : X ⟶ schemeSpace (baseObject k B hk))
  (hf : IsLocallyOfFiniteType B (Spec (.of k)) hk f.hom)

/-- Finite-dimensionality of `Hom(i^*K, G')` passes along the adjunction `i^* ⊣ i_*` to
`Hom(K, G)` for `G ≅ i_*G'`. -/
private theorem finiteDimensional_hom_of_moduleFinite_modulePullback
    {Z : AlgebraicSpaces B (Spec (.of k)) hk} (i : Z ⟶ X)
    (K G : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (G' : Modules.{u, u} B (Spec (.of k)) hk Z.1 Z.2)
    (eG : (modulePushforward B (Spec (.of k)) hk i).obj G' ≅ G)
    [Module.Finite k ((modulePullback B (Spec (.of k)) hk i).obj K ⟶ G')] :
    FiniteDimensional k (K ⟶ G) := by
  let L := modulePushforward B (Spec (.of k)) hk i
  have : PreservesFiniteLimits L := preservesFiniteLimits_modulePushforward B (Spec (.of k)) hk i
  have : L.Additive := Functor.additive_of_preserves_binary_products L
  have : L.Linear k := Stacks.SheafOfModules.linear_of_map_globalSmul _ _ L
    fun a M => modulePushforward_map_globalSmul_baseRingHom k B hk i M a
  let adj := modulePullbackAdjunction B (Spec (.of k)) hk i
  let φ : ((modulePullback B (Spec (.of k)) hk i).obj K ⟶ G') →ₗ[k] (K ⟶ L.obj G') :=
    { toFun := fun a => adj.homEquiv _ _ a
      map_add' := fun a b => by
        simp only [Adjunction.homEquiv_unit, Functor.map_add, Preadditive.comp_add]
      map_smul' := fun c a => by
        simp only [Adjunction.homEquiv_unit, RingHom.id_apply]
        rw [Functor.map_smul, Linear.comp_smul] }
  have : FiniteDimensional k (K ⟶ L.obj G') :=
    Module.Finite.of_surjective φ (adj.homEquiv _ _).surjective
  let ψ : (K ⟶ L.obj G') →ₗ[k] (K ⟶ G) :=
    { toFun := fun a => a ≫ eG.hom
      map_add' := fun a b => Preadditive.add_comp _ _ _ _ _ _
      map_smul' := fun c a => Linear.smul_comp _ _ _ _ _ _ }
  exact Module.Finite.of_surjective ψ fun a => ⟨a ≫ eG.inv, by simp [ψ]⟩

/-- **Morphisms from a coherent module into a coherent module with proper support over a field
form a finite-dimensional vector space.** -/
theorem finiteDimensional_hom_of_hasProperSupport
    (K G : Modules.{u, u} B (Spec (.of k)) hk X.1 X.2)
    (hK : IsCoherent B (Spec (.of k)) hk X.1 X.2 K) (hG : IsCoherent B (Spec (.of k)) hk X.1 X.2 G)
    (hsupp : HasProperSupport B (Spec (.of k)) hk X.2 (schemeSpace (baseObject k B hk)).2 f.hom hf
      ((SheafOfModules.toSheaf _).obj G)) :
    FiniteDimensional k (K ⟶ G) := by
  let := C1573.fact_isLocallyNoetherian_of_baseObject X f hf
  have hGqc : G.IsQuasicoherentOnSite := hG.toIsQuasicoherentOnSite
  have := hG.toIsCoherentOnSite
  have hft := isFiniteTypeOnSite_of_isCoherentOnSite B (Spec (.of k)) hk X G
  obtain ⟨hZ₁, hid⟩ := exists_isClosedSubspace_schemeTheoreticSupport B (Spec (.of k)) hk X G hGqc
    (Stacks.SheafOfModules.presheaf_isFiniteType_of_isFiniteTypeOnSite G hft)
  let Z₁ : ClosedSubspaces B (Spec (.of k)) hk X.1 :=
    ⟨schemeTheoreticSupport B (Spec (.of k)) hk X G, hZ₁⟩
  let 𝓚 := definingIdealSheaf B (Spec (.of k)) hk X Z₁
  have hKqc := isQuasicoherentOnSite_definingIdealSheaf B (Spec (.of k)) hk X Z₁
  obtain ⟨Z₂, hZ₂⟩ := exists_definingIdealSheaf_eq_of_isQuasicoherentOnSite B (Spec (.of k)) hk X
    _ (isQuasicoherentOnSite_idealPowerMultiple B (Spec (.of k)) hk X.1 X.2 𝓚
      (SheafOfModules.unit _) (SheafOfModules.isQuasicoherentOnSite_unit _) hKqc 2)
  let i := closedSubspaceInclusion B (Spec (.of k)) hk X Z₂
  have hi : IsClosedImmersion B (Spec (.of k)) hk i.hom := Z₂.2.2
  have hker : SheafOfModules.kerIdeal (structureSharp B (Spec (.of k)) hk i) =
      idealPowerMultiple B (Spec (.of k)) hk X.1 X.2 𝓚 2 (SheafOfModules.unit _) :=
    (C1573.kerIdeal_structureSharp_ι B (Spec (.of k)) hk X Z₂).trans hZ₂
  -- the closed subspace `Z₂` is proper over the field
  have hpts := C1573.range_pointsMap_ι_subset_of_definingIdealSheaf_eq_idealPowerMultiple B
    (Spec (.of k)) hk X Z₁ Z₂ 2 hZ₂
  have hsuppeq := supportOfSheaf_eq_range_pointsMap_schemeTheoreticSupport B (Spec (.of k)) hk X G
    hGqc hft
  obtain ⟨hcl, hprop⟩ := hsupp
  have hZ₂cl := isClosed_range_pointsMap_of_isClosedImmersion B (Spec (.of k)) hk X.2 Z₂.1.ι hi
  have hprop₂ := isProperOver_of_subset B (Spec (.of k)) hk X.2 (schemeSpace (baseObject k B hk)).2
    f.hom hf _ _ hZ₂cl hcl (hpts.trans (by rw [hsuppeq])) hprop
  have hproper : IsProper B (Spec (.of k)) hk (Z₂.1.ι ≫ f.hom) :=
    (exists_isProper_closedSubspace_iff_forall B (Spec (.of k)) hk X.2
      (schemeSpace (baseObject k B hk)).2 f.hom hf _ hZ₂cl).1
      ((isProper_reducedClosedSubspace_iff_exists B (Spec (.of k)) hk X.2
        (schemeSpace (baseObject k B hk)).2 f.hom hf _ hZ₂cl).1 hprop₂) Z₂.1 Z₂.2 rfl
  have hG₂ : IsPowAnnihilated B (Spec (.of k)) hk X.1 X.2 𝓚 2 G := fun U r hr x =>
    isPowAnnihilated_one_of_definingIdealSheaf_eq_annihilatorIdealSheaf B (Spec (.of k)) hk G Z₁
      hid U r (Ideal.pow_le_pow_right (by norm_num) hr) x
  obtain ⟨G', hG'qc, ⟨eG⟩⟩ := isQuasicoherentEssImagePushforward_of_isClosedImmersion B
    (Spec (.of k)) hk X i hi G hGqc
      (C1573.annihilatedByKerIdeal_of_isPowAnnihilated i 𝓚 2 hker hKqc G hG₂)
  have hG' := isCoherent_of_modulePushforward_closedSubspace B (Spec (.of k)) hk X
    (Fact.out) G Z₂ G' hG'qc eG
  -- the inverse image of `K` to `Z₂` is coherent
  have : Fact (HasEtaleLocalProperty B (Spec (.of k)) hk
      (closedSubspaceToSpace B (Spec (.of k)) hk X Z₂).1
      (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_isLocallyOfFiniteType B (Spec (.of k)) hk
      Z₂.2.1 X.2 Z₂.1.ι (isLocallyOfFiniteType_of_isClosedImmersion B (Spec (.of k)) hk Z₂.1.ι
        Z₂.2.2) Fact.out⟩
  have hK' : IsCoherent B (Spec (.of k)) hk Z₂.1.toFunctor Z₂.2.1
      ((modulePullback B (Spec (.of k)) hk i).obj K) :=
    (isCoherent_iff_isFinitePresentationOnSite B (Spec (.of k)) hk _ _ _).2
      (isFinitePresentationOnSite_modulePullback B (Spec (.of k)) hk i K
        ((isCoherent_iff_isFinitePresentationOnSite B (Spec (.of k)) hk X.1 X.2 K).1 hK))
  -- Stacks 0D0T on `Z₂`
  let : HasExt.{u + 1} (Modules.{u, u} B (Spec (.of k)) hk Z₂.1.toFunctor Z₂.2.1) :=
    HasExt.standard _
  have hfin₀ := moduleFinite_ext_of_isProper k B hk Z₂.1.toFunctor Z₂.2.1 (Z₂.1.ι ≫ f.hom) hproper
    _ G' hK' hG' 0
  have : Module.Finite k ((modulePullback B (Spec (.of k)) hk i).obj K ⟶ G') :=
    Module.Finite.equiv (Ext.linearEquiv₀ (R := k))
  exact finiteDimensional_hom_of_moduleFinite_modulePullback k B hk i K G G' eG

end Field

section SiteChange

attribute [local instance] modulesLinear

variable {k : Type u} [Field k] {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Morphisms from a coherent module into a coherent module with support proper over a test
scheme which is the spectrum of a field form a finite-dimensional vector space**, for the
`k`-linear structure given by `ψ`, the pullback of functions along `p`. This is
`AlgebraicGeometry.Space.finiteDimensional_hom_of_hasProperSupport` read through the change of
base site of Stacks 04SG, as in
`AlgebraicGeometry.Space.finiteDimensional_ext_one_and_hom_of_hasProperSupport_of_toScheme_eq`. -/
theorem finiteDimensional_hom_of_hasProperSupport_of_toScheme_eq
    (X : AlgebraicSpaces B S hS) {T : BigFppfOver B S hS} (p : X ⟶ schemeSpace T)
    (hp : IsLocallyOfFiniteType B S hS p.hom)
    (e : (BigFppfOver.toScheme B S hS).obj T = Spec (.of k))
    (ψ : k →+* Stacks.Cohomology.SiteModules.GlobalSectionRing
      (Stacks.SheafOfModules.Tensor.ringSheaf (smallEtaleRingedSite B S hS X.1 X.2).O))
    (hψ : ∀ c, ψ c = targetScalars B S hS p (((Scheme.ΓSpecIso (.of k)).inv ≫
      (eqToHom e).appTop).hom c))
    (K G : Modules.{u, u} B S hS X.1 X.2) (hK : IsCoherent B S hS X.1 X.2 K)
    (hG : IsCoherent B S hS X.1 X.2 G)
    (hsupp : HasProperSupport B S hS X.2 (schemeSpace T).2 p.hom hp
      ((SheafOfModules.toSheaf _).obj G)) :
    letI := Stacks.SheafOfModules.linearOver _ ψ
    FiniteDimensional k (K ⟶ G) := by
  obtain ⟨⟨Tk, hTk⟩, ⟨⟨⟩⟩, h⟩ := T
  change Tk = Spec (.of k) at e
  subst e
  have hψ' : ∀ c, ψ c = targetScalars B S hS p ((Scheme.ΓSpecIso (.of k)).inv c) := fun c =>
    (hψ c).trans <| by
      rw [eqToHom_refl]
      rfl
  let π : X ⟶ schemeSpace (Over.mk (show B.obj hTk ⟶ B.obj hS from h)) := p
  have : Fact (HasEtaleLocalProperty B S hS X.1 (fun V : Scheme.{u} => IsLocallyNoetherian V)) :=
    ⟨hasEtaleLocalProperty_isLocallyNoetherian_of_toScheme_eq X p hp rfl⟩
  let f' := siteChangeStructure X π
  have hf' := (isLocallyOfFiniteType_siteChangeStructure_iff X π).2 hp
  let Ψ := siteChangeModules B X π
  have hKc' := (isCoherent_siteChangeModules_iff X π K).2 hK
  have hGc' := (isCoherent_siteChangeModules_iff X π G).2 hG
  have hqc : G.IsQuasicoherentOnSite := hG.toIsQuasicoherentOnSite
  have := hG.toIsCoherentOnSite
  have hft := isFiniteTypeOnSite_of_isCoherentOnSite B S hS X G
  have hsupp' := (hasProperSupport_siteChangeModules_iff X π hp G hqc hft).2 hsupp
  have := finiteDimensional_hom_of_hasProperSupport k B hTk f' hf' (Ψ.obj K) (Ψ.obj G) hKc'
    hGc' hsupp'
  let := Stacks.SheafOfModules.linearOver _ ψ
  have : Ψ.Additive := Functor.additive_of_preserves_binary_products Ψ
  have : Ψ.Linear k := Stacks.SheafOfModules.linear_of_map_globalSmul ψ
    (baseRingHom k B hTk (siteChangeSpace B X π).1 (siteChangeSpace B X π).2) Ψ fun c M => by
      rw [show ψ c = targetScalars B S hS π ((Scheme.ΓSpecIso (.of k)).inv c) from hψ' c,
        baseRingHom_eq_targetScalars k B hTk (siteChangeSpace B X π) f' c]
      exact siteChangeModules_map_globalSmul B X π f' _ M
  exact FiniteDimensional.of_injective (Ψ.mapLinearMap k (X := K) (Y := G))
    Ψ.map_injective

end SiteChange

end AlgebraicGeometry.Space

end
