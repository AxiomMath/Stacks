module

public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreePullbackChartGlue
public import StacksFrontier.AlgebraicGeometry.FiniteLocallyFree.BlowUpFreePullbackSectionShrink

/-!
# The inverse image of the descended bundle is the bundle

Let `b : X' ⟶ X` be a morphism of schemes, let `U` and `V` cover `X`, let `b` be an isomorphism
over `V`, and let `𝒢` be a finite locally free module on `X'` trivialised over `b ⁻¹ᵁ U` by
`α : 𝒪_{X'}^{⊕I} ⟶ 𝒢`. Then `𝒢` is the inverse image of a finite locally free module on `X`:
the essential surjectivity half of [Stacks, Tag 0EXD] for the almost blowup square of
[Stacks, Example 0EVH] with a free module on the centre.

## Main results

* `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_restrictHomOfLE`: restricting a
  morphism of restrictions twice is restricting it once.
* `Stacks.AlgebraicGeometry.ModuleLimits.trivTail_cancel`: two composites with a common head
  `H ≫ F.map s` agree when their tails do.
* `AlgebraicGeometry.sectionFreeIso_eq`: `AlgebraicGeometry.sectionFreeIso` computed through any
  morphism equal to the section of `b` it is defined along.
* `AlgebraicGeometry.pullbackFreeChartCompIso_eq_pullbackSectionChartIso`: over an open carrying a
  section of `b` the free chart and the section chart agree, provided the trivialisation of `N`
  there is the one `α` gives along the section.
* `AlgebraicGeometry.restrictHomOfLE_pullbackFreeChartCompIso_eq`: the two chart comparisons
  agree over an open contained in `U` and `V`.
* `AlgebraicGeometry.nonempty_pullback_iso_of_restrictChartIso_compat`: the inverse image of a
  module with compatible trivialisations over `U` and `V` is the given module.
* `AlgebraicGeometry.exists_isFiniteLocallyFree_pullback_iso_of_isIso_restrict_free`: a finite
  locally free module on `X'`, free over the preimage of `U`, is the inverse image of a finite
  locally free module on `X`.

## References

* [Stacks Project, Tag 0EXD](https://stacks.math.columbia.edu/tag/0EXD)
* [Stacks Project, Tag 0EVH](https://stacks.math.columbia.edu/tag/0EVH)
* [Stacks Project, Tag 01ZR](https://stacks.math.columbia.edu/tag/01ZR)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace AlgebraicGeometry

universe u v₁ v₂ w₁ w₂

namespace Stacks.AlgebraicGeometry.ModuleLimits

variable {X : Scheme.{u}} {M N : X.Modules}

/-- Restricting a morphism of restrictions to a smaller open twice is restricting it once. -/
theorem restrictHomOfLE_restrictHomOfLE {V W Z : X.Opens} (e : V ≤ W) (e' : W ≤ Z)
    (χ : Scheme.Modules.restrict M Z.ι ⟶ Scheme.Modules.restrict N Z.ι) :
    restrictHomOfLE e (restrictHomOfLE e' χ) = restrictHomOfLE (e.trans e') χ := by
  have hc := X.homOfLE_homOfLE e e'
  have hassocM := restrictCompIso_assoc (X.homOfLE e) (X.homOfLE e') Z.ι
    (Scheme.homOfLE_ι X e') (Scheme.homOfLE_ι X e) hc M
  have hisoN : (restrictCompIso (X.homOfLE e) W.ι (Scheme.homOfLE_ι X e) N ≪≫
        (Scheme.Modules.restrictFunctor (X.homOfLE e)).mapIso
          (restrictCompIso (X.homOfLE e') Z.ι (Scheme.homOfLE_ι X e') N)) =
      (restrictCompIso (X.homOfLE (e.trans e')) Z.ι (Scheme.homOfLE_ι X (e.trans e')) N ≪≫
        restrictCompIso (X.homOfLE e) (X.homOfLE e') hc
          (Scheme.Modules.restrict N Z.ι)) :=
    Iso.ext (restrictCompIso_assoc (X.homOfLE e) (X.homOfLE e') Z.ι
      (Scheme.homOfLE_ι X e') (Scheme.homOfLE_ι X e) hc N)
  have hnat := restrictCompIso_naturality (X.homOfLE e) (X.homOfLE e') hc χ
  have h2 := congrArg Iso.inv hisoN
  simp only [Iso.trans_inv, Functor.mapIso_inv] at h2
  simp only [restrictHomOfLE_eq_restrictLocal, restrictLocal_eq,
    CategoryTheory.Functor.map_comp, Category.assoc]
  rw [reassoc_of% hassocM, ← reassoc_of% hnat, h2, Iso.hom_inv_id_assoc]

/-- If `t = s ≫ a₁ ≫ a₂` and `F.map a₁ ≫ F.map a₂ ≫ f₁ ≫ f₂ ≫ f₃ = R`, then
`(H ≫ F.map t ≫ f₁ ≫ f₂) ≫ f₃ = H ≫ F.map s ≫ R`. -/
theorem trivTail_cancel {𝒞 : Type w₁} {𝒟 : Type w₂} [Category.{v₁} 𝒞] [Category.{v₂} 𝒟]
    (F : 𝒞 ⥤ 𝒟) {Mp Gp Q Fr : 𝒞} {W Y₁ Y₂ Z : 𝒟} (H : W ⟶ F.obj Mp) (s : Mp ⟶ Gp)
    (a₁ : Gp ⟶ Q) (a₂ : Q ⟶ Fr) (t : Mp ⟶ Fr) (f₁ : F.obj Fr ⟶ Y₁) (f₂ : Y₁ ⟶ Y₂)
    (f₃ : Y₂ ⟶ Z) (R : F.obj Gp ⟶ Z) (ht : t = s ≫ a₁ ≫ a₂)
    (hR : F.map a₁ ≫ F.map a₂ ≫ f₁ ≫ f₂ ≫ f₃ = R) :
    (H ≫ F.map t ≫ f₁ ≫ f₂) ≫ f₃ = H ≫ F.map s ≫ R := by
  subst ht hR
  simp only [CategoryTheory.Functor.map_comp, Category.assoc]

end Stacks.AlgebraicGeometry.ModuleLimits

namespace AlgebraicGeometry

/-! ### The comparison along the section, with the section a variable -/

/-- For any `sP` equal to `k ≫ freeChartBaseSection b V`, `AlgebraicGeometry.sectionFreeIso` is
the inverse of `AlgebraicGeometry.restrictCompIso`, followed by the inverse of the restriction of
`α` along `sP`, followed by `Stacks.Modules.restrictFreeIso sP I`. -/
theorem sectionFreeIso_eq {X X' T : Scheme.{u}} (b : X' ⟶ X) {U V : X.Opens} [IsIso (b ∣_ V)]
    (k : T ⟶ V.toScheme) (hkU : Set.range (k ≫ V.ι).base ⊆ (U : Set X)) [IsOpenImmersion k]
    {I : Type u} {G : X'.Modules} (α : _root_.SheafOfModules.free.{u} I ⟶ G)
    (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ U).ι).map α))
    {sP : T ⟶ X'} [IsOpenImmersion sP] (hsP : k ≫ freeChartBaseSection b V = sP)
    (hp : IsIso ((Scheme.Modules.restrictFunctor sP).map α)) :
    sectionFreeIso b k hkU α hα =
      (restrictCompIso k (freeChartBaseSection b V) hsP G).symm ≪≫
        (asIso ((Scheme.Modules.restrictFunctor sP).map α)).symm ≪≫
          Stacks.Modules.restrictFreeIso sP I := by
  subst hsP
  rfl

variable {X X' : Scheme.{u}} (b : X' ⟶ X) {I : Type u} {G : X'.Modules}
  (α : _root_.SheafOfModules.free.{u} I ⟶ G)

/-! ### The two charts agree over an open carrying a section -/

/-- Over an open `Ω` on which `b` is invertible the free chart comparison and the section chart
comparison agree, provided the trivialisation `τ'` of `N` over `Ω` is the identification `σ'` of
`N` with the inverse image of `𝒢` along the section followed by the trivialisation of `𝒢` that `α`
gives there. -/
theorem pullbackFreeChartCompIso_eq_pullbackSectionChartIso {Ω : X.Opens} [IsIso (b ∣_ Ω)]
    (N : X.Modules)
    (hα' : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ Ω).ι).map α))
    (hp : IsIso ((Scheme.Modules.restrictFunctor (freeChartBaseSection b Ω)).map α))
    (σ' : Scheme.Modules.restrict N Ω.ι ≅
      Scheme.Modules.restrict G (freeChartBaseSection b Ω))
    (τ' : Scheme.Modules.restrict N Ω.ι ≅
      _root_.SheafOfModules.free (R := Ω.toScheme.ringCatSheaf) I)
    (hτσ : τ' = σ' ≪≫
      (asIso ((Scheme.Modules.restrictFunctor (freeChartBaseSection b Ω)).map α)).symm ≪≫
        Stacks.Modules.restrictFreeIso (freeChartBaseSection b Ω) I) :
    pullbackFreeChartCompIso b α Ω N τ' hα' = pullbackSectionChartIso b N σ' :=
  have := hp
  Iso.ext (Stacks.AlgebraicGeometry.ModuleLimits.trivTail_cancel
    (Scheme.Modules.pullback (b ∣_ Ω))
    (restrictPullbackPreimageIso b Ω N).hom σ'.hom
    (inv ((Scheme.Modules.restrictFunctor (freeChartBaseSection b Ω)).map α))
    (Stacks.Modules.restrictFreeIso (freeChartBaseSection b Ω) I).hom τ'.hom
    (Scheme.Modules.pullbackFreeIso (b ∣_ Ω) I).hom
    (Stacks.Modules.restrictFreeIso (b ⁻¹ᵁ Ω).ι I).inv
    ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ Ω).ι).map α)
    (pullbackRestrictObjIso (b ∣_ Ω) (freeChartBaseSection b Ω)
      (morphismRestrict_comp_freeChartBaseSection b) G).hom
    (congrArg Iso.hom hτσ)
    (pullbackRestrictObjIso_hom_eq_of_isIso α (b ∣_ Ω) (freeChartBaseSection b Ω)
      (morphismRestrict_comp_freeChartBaseSection b) hp))

/-! ### The agreement of the two charts over the overlap -/

/-- The free chart comparison over `b ⁻¹ᵁ U` and the section chart comparison over `b ⁻¹ᵁ V`
have the same restriction `Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE` to `b ⁻¹ᵁ Ω`,
for an open `Ω` inside both `U` and `V`, with inclusions `cf` and `ct` into the two and `sP` the
section of `b` over `V` restricted to it, provided the two trivialisations of `N` agree over `Ω`
(`hcompat`). -/
theorem restrictHomOfLE_pullbackFreeChartCompIso_eq {U V Ω : X.Opens} (hΩU : Ω ≤ U)
    (hΩV : Ω ≤ V) [IsIso (b ∣_ V)] [IsIso (b ∣_ Ω)] (N : X.Modules)
    (τ : Scheme.Modules.restrict N U.ι ≅
      _root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
    (σ : Scheme.Modules.restrict N V.ι ≅
      Scheme.Modules.restrict G (freeChartBaseSection b V))
    (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ U).ι).map α))
    (cf : Ω.toScheme ⟶ U.toScheme) [IsOpenImmersion cf] (hcf : cf ≫ U.ι = Ω.ι)
    (ct : Ω.toScheme ⟶ V.toScheme) [IsOpenImmersion ct] (hct : ct ≫ V.ι = Ω.ι)
    (hkU : Set.range (ct ≫ V.ι).base ⊆ (U : Set X))
    {sP : Ω.toScheme ⟶ X'} [IsOpenImmersion sP]
    (hsP : ct ≫ freeChartBaseSection b V = sP)
    (hp : IsIso ((Scheme.Modules.restrictFunctor sP).map α))
    (hcompat : restrictChartIso U.ι τ cf hcf ≪≫ Stacks.Modules.restrictFreeIso cf I =
      restrictChartIso V.ι σ ct hct ≪≫ sectionFreeIso b ct hkU α hα) :
    Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE (b.preimage_mono hΩU)
        (pullbackFreeChartCompIso b α U N τ hα).hom =
      Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE (b.preimage_mono hΩV)
        (pullbackSectionChartIso b N σ).hom := by
  obtain rfl : cf = X.homOfLE hΩU := by rw [← cancel_mono U.ι, hcf, Scheme.homOfLE_ι]
  obtain rfl : ct = X.homOfLE hΩV := by rw [← cancel_mono V.ι, hct, Scheme.homOfLE_ι]
  obtain rfl : sP = freeChartBaseSection b Ω :=
    eq_freeChartBaseSection b Ω sP <| by
      rw [← hsP, Category.assoc, freeChartBaseSection_comp, Scheme.homOfLE_ι]
  have hα' : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ Ω).ι).map α) :=
    isIso_restrictFunctor_map_preimage_of_le b α hΩU hα
  have hL := restrictChartIso_pullbackFreeChartCompIso b α hΩU N τ
    (restrictChartIso U.ι τ (X.homOfLE hΩU) (Scheme.homOfLE_ι X hΩU) ≪≫
      Stacks.Modules.restrictFreeIso (X.homOfLE hΩU) I) hα hα'
    ((iso_trans_eq_iff _ _ _).1 rfl)
  have hR := restrictChartIso_pullbackSectionChartIso b hΩV N σ
    (restrictChartIso V.ι σ (X.homOfLE hΩV) (Scheme.homOfLE_ι X hΩV) ≪≫
      (restrictCompIso (X.homOfLE hΩV) (freeChartBaseSection b V) hsP G).symm) rfl
  have hτσ : (restrictChartIso U.ι τ (X.homOfLE hΩU) (Scheme.homOfLE_ι X hΩU) ≪≫
        Stacks.Modules.restrictFreeIso (X.homOfLE hΩU) I) =
      (restrictChartIso V.ι σ (X.homOfLE hΩV) (Scheme.homOfLE_ι X hΩV) ≪≫
          (restrictCompIso (X.homOfLE hΩV) (freeChartBaseSection b V) hsP G).symm) ≪≫
        (asIso ((Scheme.Modules.restrictFunctor (freeChartBaseSection b Ω)).map α)).symm ≪≫
          Stacks.Modules.restrictFreeIso (freeChartBaseSection b Ω) I :=
    hcompat.trans
      ((congrArg (restrictChartIso V.ι σ (X.homOfLE hΩV) (Scheme.homOfLE_ι X hΩV) ≪≫ ·)
        (sectionFreeIso_eq b (X.homOfLE hΩV) hkU α hα hsP hp)).trans
        (Iso.trans_assoc _ _ _).symm)
  refine ((restrictHomOfLE_iso_hom (b.preimage_mono hΩU) _).trans
    (congrArg Iso.hom hL)).trans ?_
  refine Eq.trans ?_ ((restrictHomOfLE_iso_hom (b.preimage_mono hΩV) _).trans
    (congrArg Iso.hom hR)).symm
  exact congrArg Iso.hom
    (pullbackFreeChartCompIso_eq_pullbackSectionChartIso b α N hα' hp _ _ hτσ)

/-! ### The glueing -/

/-- If `N` has trivialisations `κ` over `U` and `V` whose agreement over `U ⊓ V` is `hcompat`,
then the inverse image of `N` along `b` is isomorphic to `G`. -/
theorem nonempty_pullback_iso_of_restrictChartIso_compat {U V : X.Opens} [IsIso (b ∣_ V)]
    (hUV : U ⊔ V = ⊤) (N : X.Modules)
    (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ U).ι).map α))
    (κ : ∀ i, Scheme.Modules.restrict N (TwoOpensGlue.opn U V i).ι ≅
      TwoOpensGlue.mdl U V (_root_.SheafOfModules.free (R := U.toScheme.ringCatSheaf) I)
        (Scheme.Modules.restrict G (freeChartBaseSection b V)) i)
    (hcompat : restrictChartIso (TwoOpensGlue.opn U V ⟨false⟩).ι (κ ⟨false⟩)
            (TwoOpensGlue.mid U V ⟨false⟩) (TwoOpensGlue.mid_comp U V ⟨false⟩) ≪≫
          overlapIsoFamily b α hα ⟨false⟩ =
        restrictChartIso (TwoOpensGlue.opn U V ⟨true⟩).ι (κ ⟨true⟩)
            (TwoOpensGlue.mid U V ⟨true⟩) (TwoOpensGlue.mid_comp U V ⟨true⟩) ≪≫
          overlapIsoFamily b α hα ⟨true⟩) :
    Nonempty ((Scheme.Modules.pullback b).obj N ≅ G) := by
  have : IsIso (b ∣_ (U ⊓ V)) :=
    Stacks.RestrictIso.isIso_morphismRestrict_of_le b inf_le_right ‹IsIso (b ∣_ V)›
  have hmf : IsOpenImmersion
      (show (U ⊓ V).toScheme ⟶ U.toScheme from TwoOpensGlue.mid U V ⟨false⟩) :=
    TwoOpensGlue.isOpenImmersion_mid U V ⟨false⟩
  have hft : Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE
        (inf_le_left : b ⁻¹ᵁ U ⊓ b ⁻¹ᵁ V ≤ b ⁻¹ᵁ U)
        (preimageChartIso b α hα κ ⟨false⟩).hom =
      Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE
        (inf_le_right : b ⁻¹ᵁ U ⊓ b ⁻¹ᵁ V ≤ b ⁻¹ᵁ V)
        (preimageChartIso b α hα κ ⟨true⟩).hom :=
    restrictHomOfLE_pullbackFreeChartCompIso_eq b α
      (inf_le_left : U ⊓ V ≤ U) (inf_le_right : U ⊓ V ≤ V) N (κ ⟨false⟩) (κ ⟨true⟩) hα
      (TwoOpensGlue.mid U V ⟨false⟩) (TwoOpensGlue.mid_comp U V ⟨false⟩)
      (overlapToRight (U := U) (V := V)) (overlapToRight_comp (U := U) (V := V))
      (range_overlapToRight_comp_subset (U := U) (V := V))
      (sP := sectionComp b (overlapToRight (U := U) (V := V))) rfl
      (isIso_restrictFunctor_map_sectionComp b (overlapToRight (U := U) (V := V))
        (range_overlapToRight_comp_subset (U := U) (V := V)) α hα) hcompat
  have hd : b ⁻¹ᵁ V ⊓ b ⁻¹ᵁ U ≤ b ⁻¹ᵁ U ⊓ b ⁻¹ᵁ V := le_inf inf_le_right inf_le_left
  refine Stacks.AlgebraicGeometry.ModuleLimits.nonempty_iso_of_cover_of_inf
    (fun i => b ⁻¹ᵁ TwoOpensGlue.opn U V i) (fun x => ?_) (preimageChartIso b α hα κ)
    (fun i j => ?_)
  · have hx : b.base x ∈ U ⊔ V := hUV ▸ trivial
    rcases (by simpa using hx : b.base x ∈ U ∨ b.base x ∈ V) with h | h
    · exact ⟨⟨false⟩, h⟩
    · exact ⟨⟨true⟩, h⟩
  · match i, j with
    | ⟨false⟩, ⟨false⟩ => rfl
    | ⟨true⟩, ⟨true⟩ => rfl
    | ⟨false⟩, ⟨true⟩ => exact hft
    | ⟨true⟩, ⟨false⟩ =>
        refine Eq.trans (Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_restrictHomOfLE
          hd inf_le_right (preimageChartIso b α hα κ ⟨true⟩).hom).symm ?_
        refine Eq.trans ?_ (Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE_restrictHomOfLE
          hd inf_le_left (preimageChartIso b α hα κ ⟨false⟩).hom)
        exact congrArg (Stacks.AlgebraicGeometry.ModuleLimits.restrictHomOfLE hd) hft.symm

/-- A finite locally free module on `X'`, free over the preimage of `U` and with `b` invertible
over `V`, is the inverse image of a finite locally free module on `X`. -/
theorem exists_isFiniteLocallyFree_pullback_iso_of_isIso_restrict_free {U V : X.Opens}
    [IsIso (b ∣_ V)] (hUV : U ⊔ V = ⊤) [Finite I]
    (hG : Scheme.Modules.IsFiniteLocallyFree G)
    (hα : IsIso ((Scheme.Modules.restrictFunctor (b ⁻¹ᵁ U).ι).map α)) :
    ∃ N : X.Modules, Scheme.Modules.IsFiniteLocallyFree N ∧
      Nonempty ((Scheme.Modules.pullback b).obj N ≅ G) := by
  obtain ⟨N, κ, hN, hcompat⟩ :=
    exists_isFiniteLocallyFree_restrict_iso_compat_of_isIso_restrict_free b α hUV hG hα
  exact ⟨N, hN, nonempty_pullback_iso_of_restrictChartIso_compat b α hUV N hα κ hcompat⟩

end AlgebraicGeometry

end
