module

public import StacksFrontier.AlgebraicGeometry.Duality.RelativeDualizing.DualizingComplexNegativeExt
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.NormalizedDualizing
public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.OpenImmersionComposition
public import StacksFrontier.Topology.Sheaves.Cohomology.GlueingComplexes.SchemeFiniteCoverLocallySmall

/-!
# Uniqueness of normalized dualizing complexes

Let `S` be Noetherian with a dualizing complex `ω_S^•`, `X` of finite type over `S`, and
`𝒰 : X = ⋃ U_i` a finite open covering by schemes separated over `S`. For the upper shriek
formalism of a choice of compactifications, a dualizing complex normalized relative to `ω_S^•`
and `𝒰` is unique up to unique isomorphism ([Stacks, Tag 0AU7]).

Given two, `(K, α_i)` and `(K', α'_i)`, the isomorphisms `α'^{-1}_i ∘ α_i : K|_{U_i} ≅ K'|_{U_i}`
agree on the overlaps, because both normalizations restrict to the canonical ones there. They
glue to a unique morphism `K ⟶ K'` (`Stacks.Cohomology.GlueingComplexes`), because negative
self-Ext of the dualizing complex `K` vanishes on every open
(`Stacks.Duality.eq_zero_of_isDualizingComplex`), and the glued morphism is invertible, its
inverse being glued from the inverses. The source argues instead with the invertible object
`R𝓗om(K, K')` of [Stacks, Tag 0ATP]; the glueing of morphisms used here is the same sheaf
property of `Hom` in negative degrees.

## Main results

* `Stacks.Duality.Normalized.existsUnique_iso_ofCompactifications`: **[Stacks, Tag 0AU7]** for
  the upper shriek functors of compactifications.

## References

* [Stacks Project, Tag 0AU7](https://stacks.math.columbia.edu/tag/0AU7)
* [Stacks Project, Tag 0ATP](https://stacks.math.columbia.edu/tag/0ATP)
* [Stacks Project, Tag 08DG](https://stacks.math.columbia.edu/tag/08DG)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u w

namespace Stacks.Duality

/-- The restriction of the conjugate of `δ` by the identifications `j^! = Lj^*` is the conjugate
of the restriction of `δ`, given the factorisation of the identification for the composite. -/
private theorem restrict_conj_chase {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {a a' b b' : C} {p p' q q' w w' : D} (ρU : a ≅ b) (ρU' : a' ≅ b') (δ : a ⟶ a')
    (cc : L.obj b ≅ w) (cc' : L.obj b' ≅ w') (ρh : p ≅ L.obj a) (ρh' : p' ≅ L.obj a')
    (F : q ≅ p) (F' : q' ≅ p') (ρW : q ≅ w) (ρW' : q' ≅ w') (σ : p ⟶ p')
    (hρ : ρW.hom = F.hom ≫ ρh.hom ≫ L.map ρU.hom ≫ cc.hom)
    (hρ' : ρW'.hom = F'.hom ≫ ρh'.hom ≫ L.map ρU'.hom ≫ cc'.hom)
    (hσ : ρh.hom ≫ L.map δ = σ ≫ ρh'.hom) :
    cc.inv ≫ L.map (ρU.inv ≫ δ ≫ ρU'.hom) ≫ cc'.hom =
      ρW.inv ≫ (F.hom ≫ σ ≫ F'.inv) ≫ ρW'.hom := by
  have hρi : ρW.inv = cc.inv ≫ L.map ρU.inv ≫ ρh.inv ≫ F.inv := by
    rw [← cancel_epi ρW.hom, Iso.hom_inv_id, hρ]
    simp [← L.map_comp_assoc]
  have hσ' : ρh.inv ≫ σ ≫ ρh'.hom = L.map δ := by
    rw [← hσ, Iso.inv_hom_id_assoc]
  rw [hρi, hρ']
  simp only [Category.assoc, Iso.inv_hom_id_assoc, Functor.map_comp]
  rw [← reassoc_of% hσ']

namespace UpperShriek

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))

/-- For a shriekable open immersion `j`, the identification `j^! K ≅ Lj^* K`, read in the ambient
derived category. -/
abbrev pullbackOpenIso {X Y : Scheme.{u}} (j : X ⟶ Y) (hj : IsShriekable j) [IsOpenImmersion j]
    (K : quasiCoherentDerivedCategoryPlusOfModel Y) :
    ((shriekOf c j hj).obj K).obj.obj ≅ (derivedPullback j).obj K.obj.obj :=
  (ObjectProperty.ι _).mapIso ((shriekOfIsoPullbackOfIsOpenImmersion c j hj).app K)

/-- **Restriction commutes with the identifications `j^! = Lj^*`.** For opens `W ≤ U` of `X` and
`δ : U^! K ⟶ U^! K'`, restricting to `W` the morphism `Lι_U^*K ⟶ Lι_U^*K'` corresponding to `δ`
gives the morphism corresponding to the restriction `W^! K ≅ h^! U^! K ⟶ h^! U^! K' ≅ W^! K'` of
`δ`, where `h : W ⟶ U`. -/
theorem restrictHomLocallySmall_pullbackOpenIso {X : Scheme.{u}} {W U : X.Opens} (h : W ≤ U)
    (hh : IsShriekable (X.homOfLE h)) (hU : IsShriekable U.ι) (hW : IsShriekable W.ι)
    {K K' : quasiCoherentDerivedCategoryPlusOfModel X}
    (δ : (shriekOf c U.ι hU).obj K ⟶ (shriekOf c U.ι hU).obj K') :
    Stacks.Cohomology.GlueingComplexes.restrictHomLocallySmall h K.obj.obj K'.obj.obj
        ((pullbackOpenIso c U.ι hU K).inv ≫ δ.hom.hom ≫ (pullbackOpenIso c U.ι hU K').hom) =
      (pullbackOpenIso c W.ι hW K).inv ≫
        ((factorIsoOf c (X.homOfLE_ι h) hh hU hW).hom.app K ≫ (shriekOf c (X.homOfLE h) hh).map δ ≫
          (factorIsoOf c (X.homOfLE_ι h) hh hU hW).inv.app K').hom.hom ≫
        (pullbackOpenIso c W.ι hW K').hom := by
  let cc := fun M : DerivedCategory X.Modules =>
    (Stacks.DerivedPullback.Composition.derivedPullbackCompIsoCanonical
        (X.homOfLE h).toLRSHom.toShHom U.ι.toLRSHom.toShHom ≪≫
      StacksDraft.DerivedModel.derivedPullbackCongr
        (congrArg (fun m : W.toScheme ⟶ X ↦ m.toLRSHom.toShHom) (X.homOfLE_ι h))).app M
  have fac : ∀ M : quasiCoherentDerivedCategoryPlusOfModel X,
      (pullbackOpenIso c W.ι hW M).hom =
      ((factorIsoOf c (X.homOfLE_ι h) hh hU hW).hom.app M).hom.hom ≫
        (pullbackOpenIso c (X.homOfLE h) hh ((shriekOf c U.ι hU).obj M)).hom ≫
        (derivedPullback (X.homOfLE h)).map (pullbackOpenIso c U.ι hU M).hom ≫
        (cc M.obj.obj).hom := fun M =>
    congrArg (fun f => f.hom)
      (shriekOfIsoPullbackOfIsOpenImmersion_factorIso c (X.homOfLE_ι h) hh hU hW M)
  have nat : (pullbackOpenIso c (X.homOfLE h) hh ((shriekOf c U.ι hU).obj K)).hom ≫
      (derivedPullback (X.homOfLE h)).map δ.hom.hom =
      ((shriekOf c (X.homOfLE h) hh).map δ).hom.hom ≫
        (pullbackOpenIso c (X.homOfLE h) hh ((shriekOf c U.ι hU).obj K')).hom :=
    (congrArg (fun f => f.hom)
      ((shriekOfIsoPullbackOfIsOpenImmersion c (X.homOfLE h) hh).hom.naturality δ)).symm
  exact restrict_conj_chase (derivedPullback (X.homOfLE h)) (pullbackOpenIso c U.ι hU K)
    (pullbackOpenIso c U.ι hU K') δ.hom.hom (cc K.obj.obj) (cc K'.obj.obj)
    (pullbackOpenIso c (X.homOfLE h) hh ((shriekOf c U.ι hU).obj K))
    (pullbackOpenIso c (X.homOfLE h) hh ((shriekOf c U.ι hU).obj K'))
    ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso
      ((factorIsoOf c (X.homOfLE_ι h) hh hU hW).app K))
    ((ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso
      ((factorIsoOf c (X.homOfLE_ι h) hh hU hW).app K'))
    (pullbackOpenIso c W.ι hW K) (pullbackOpenIso c W.ι hW K')
    ((shriekOf c (X.homOfLE h) hh).map δ).hom.hom (fac K) (fac K') nat

/-- The identification `j^! = Lj^*` is natural: `Lj^*` of a morphism is the conjugate of `j^!` of
it. -/
theorem map_eq_pullbackOpenIso {X Y : Scheme.{u}} (j : X ⟶ Y) (hj : IsShriekable j)
    [IsOpenImmersion j] {K K' : quasiCoherentDerivedCategoryPlusOfModel Y} (f : K ⟶ K') :
    (derivedPullback j).map f.hom.hom = (pullbackOpenIso c j hj K).inv ≫
      ((shriekOf c j hj).map f).hom.hom ≫ (pullbackOpenIso c j hj K').hom := by
  have nat : ((shriekOf c j hj).map f).hom.hom ≫ (pullbackOpenIso c j hj K').hom =
      (pullbackOpenIso c j hj K).hom ≫ (derivedPullback j).map f.hom.hom :=
    congrArg (fun g => g.hom) ((shriekOfIsoPullbackOfIsOpenImmersion c j hj).hom.naturality f)
  exact (Iso.eq_inv_comp _).mpr nat.symm

end UpperShriek

namespace Normalized

variable (c : ∀ {X Y : Scheme.{u}} (f : X ⟶ Y), IsShriekable f → CompactificationOf (Over.mk f))
  {X S : Scheme.{u}} {p : X ⟶ S} {hp : IsFiniteTypeOverNoetherian p}
  {ωS : quasiCoherentDerivedCategoryPlusOfModel S} {ι : Type w} {𝒰 : SeparatedCovering p ι}

/-- The comparison `K|_{U_i} ≅ K'|_{U_i}` of two normalized complexes on a member of the covering,
`α'^{-1}_i ∘ α_i`, read as a morphism between derived restrictions. -/
def compareHom (𝒩₁ 𝒩₂ : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰) (i : ι) :
    (derivedPullback (𝒰.U i).ι).obj 𝒩₁.complex.obj.obj ⟶
      (derivedPullback (𝒰.U i).ι).obj 𝒩₂.complex.obj.obj :=
  (UpperShriek.pullbackOpenIso c (𝒰.U i).ι (hp.isShriekable_ι _) 𝒩₁.complex).inv ≫
    ((𝒩₁.localIso i).hom ≫ (𝒩₂.localIso i).inv).hom.hom ≫
    (UpperShriek.pullbackOpenIso c (𝒰.U i).ι (hp.isShriekable_ι _) 𝒩₂.complex).hom

/-- The restriction to `W ≤ U_i` of the comparison of two normalizations is the comparison of
their restrictions, which by the compatibility of normalizations does not depend on `i`. -/
theorem restrictLocalIso_comp (𝒩₁ 𝒩₂ : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰)
    {W : X.Opens} (i : ι) (h : W ≤ 𝒰.U i) :
    (UpperShriek.factorIsoOf c (X.homOfLE_ι h) (hp.isShriekable_homOfLE h)
        (hp.isShriekable_ι _) (hp.isShriekable_ι W)).hom.app 𝒩₁.complex ≫
      (UpperShriek.shriekOf c (X.homOfLE h) (hp.isShriekable_homOfLE h)).map
        ((𝒩₁.localIso i).hom ≫ (𝒩₂.localIso i).inv) ≫
      (UpperShriek.factorIsoOf c (X.homOfLE_ι h) (hp.isShriekable_homOfLE h)
        (hp.isShriekable_ι _) (hp.isShriekable_ι W)).inv.app 𝒩₂.complex =
      ((UpperShriek.ofCompactifications c).restrictLocalIso hp ωS 𝒩₁.complex h
          (𝒰.shriekable i) (𝒩₁.localIso i)).hom ≫
        ((UpperShriek.ofCompactifications c).restrictLocalIso hp ωS 𝒩₂.complex h
          (𝒰.shriekable i) (𝒩₂.localIso i)).inv := by
  refine (congrArg (fun t => _ ≫ t ≫ _)
    ((UpperShriek.shriekOf c (X.homOfLE h) (hp.isShriekable_homOfLE h)).map_comp _ _)).trans ?_
  simp only [UpperShriek.restrictLocalIso, Iso.trans_hom, Iso.trans_inv, Iso.symm_hom,
    Iso.symm_inv, Iso.app_hom, Iso.app_inv, Functor.mapIso_hom, Functor.mapIso_inv,
    Category.assoc, Iso.inv_hom_id_app_assoc]
  exact congrArg (_ ≫ ·) (Category.assoc _ _ _)

/-- The comparisons of two normalized complexes on the members of the covering agree on the
overlaps. -/
theorem compareHom_compat (𝒩₁ 𝒩₂ : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰)
    (i j : ι) :
    Stacks.Cohomology.GlueingComplexes.restrictHomLocallySmall
        (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U i) 𝒩₁.complex.obj.obj 𝒩₂.complex.obj.obj
        (compareHom c 𝒩₁ 𝒩₂ i) =
      Stacks.Cohomology.GlueingComplexes.restrictHomLocallySmall
        (inf_le_right : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U j) 𝒩₁.complex.obj.obj 𝒩₂.complex.obj.obj
        (compareHom c 𝒩₁ 𝒩₂ j) := by
  have e₁ := UpperShriek.restrictHomLocallySmall_pullbackOpenIso c
    (inf_le_left : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U i) (hp.isShriekable_homOfLE _) (hp.isShriekable_ι _)
    (hp.isShriekable_ι _) ((𝒩₁.localIso i).hom ≫ (𝒩₂.localIso i).inv)
  have e₂ := UpperShriek.restrictHomLocallySmall_pullbackOpenIso c
    (inf_le_right : 𝒰.U i ⊓ 𝒰.U j ≤ 𝒰.U j) (hp.isShriekable_homOfLE _) (hp.isShriekable_ι _)
    (hp.isShriekable_ι _) ((𝒩₁.localIso j).hom ≫ (𝒩₂.localIso j).inv)
  refine e₁.trans (Eq.trans ?_ e₂.symm)
  refine (congrArg (fun t => _ ≫ t.hom.hom ≫ _)
    (restrictLocalIso_comp c 𝒩₁ 𝒩₂ i inf_le_left)).trans (Eq.trans ?_ (congrArg
      (fun t => _ ≫ t.hom.hom ≫ _) (restrictLocalIso_comp c 𝒩₁ 𝒩₂ j inf_le_right)).symm)
  exact congrArg₂ (fun (A : (UpperShriek.ofCompactifications c).restrictTo hp (𝒰.U i ⊓ 𝒰.U j)
        𝒩₁.complex ≅ (UpperShriek.ofCompactifications c).localModel
          (hp.isShriekable_le inf_le_left (𝒰.shriekable i)) ωS)
      (B : (UpperShriek.ofCompactifications c).restrictTo hp (𝒰.U i ⊓ 𝒰.U j)
        𝒩₂.complex ≅ (UpperShriek.ofCompactifications c).localModel
          (hp.isShriekable_le inf_le_left (𝒰.shriekable i)) ωS) =>
      (UpperShriek.pullbackOpenIso c (𝒰.U i ⊓ 𝒰.U j).ι (hp.isShriekable_ι _) 𝒩₁.complex).inv ≫
        (A.hom ≫ B.inv).hom.hom ≫
        (UpperShriek.pullbackOpenIso c (𝒰.U i ⊓ 𝒰.U j).ι (hp.isShriekable_ι _) 𝒩₂.complex).hom)
    (𝒩₁.compat i j) (𝒩₂.compat i j)

/-- **The comparisons of two normalized complexes glue.** For two dualizing complexes normalized
relative to `ω_S^•` and `𝒰`, there is a unique morphism `K ⟶ K'` restricting on each `U_i` to
`α'^{-1}_i ∘ α_i`. -/
theorem existsUnique_map_eq_compareHom
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒩₁ 𝒩₂ : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰) :
    ∃! φ : 𝒩₁.complex.obj.obj ⟶ 𝒩₂.complex.obj.obj,
      ∀ i, (derivedPullback (𝒰.U i).ι).map φ = compareHom c 𝒩₁ 𝒩₂ i := by
  have := hp.source_noetherian
  have := 𝒰.finite
  have hd₀ := isDualizingComplex_standard_of_isDualizingComplex
    (𝒩₂.isDualizingComplex_ofCompactifications c hωS)
  refine Stacks.Cohomology.GlueingComplexes.existsUnique_map_eq_of_iSup_eq_top_locallySmall
    𝒰.U 𝒰.covers _ _ (fun W ⟨i, hWi⟩ g => ?_) _ (compareHom_compat c 𝒩₁ 𝒩₂)
  let R := fun 𝒩 : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰 =>
    (UpperShriek.ofCompactifications c).restrictLocalIso hp ωS 𝒩.complex hWi (𝒰.shriekable i)
      (𝒩.localIso i)
  let θ : (derivedPullback W.ι).obj 𝒩₁.complex.obj.obj ≅
      (derivedPullback W.ι).obj 𝒩₂.complex.obj.obj :=
    (UpperShriek.pullbackOpenIso c W.ι (hp.isShriekable_ι W) 𝒩₁.complex).symm ≪≫
      (ObjectProperty.ι _ ⋙ ObjectProperty.ι _).mapIso (R 𝒩₁ ≪≫ (R 𝒩₂).symm) ≪≫
      UpperShriek.pullbackOpenIso c W.ι (hp.isShriekable_ι W) 𝒩₂.complex
  let τ := (Stacks.Injectives.grothendieckModelEquiv (SheafOfModules.{u}
      (structureSheafRing W.toScheme.toRingedSpace))).fullyFaithfulFunctor.preimageIso
    ((StacksDraft.DerivedModel.derivedPullbackModelIso W.ι.toLRSHom.toShHom).app
        ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj 𝒩₁.complex.obj.obj) ≪≫ θ ≪≫
      ((StacksDraft.DerivedModel.derivedPullbackModelIso W.ι.toLRSHom.toShHom).app
        ((Stacks.Injectives.grothendieckModelEquiv _).inverse.obj 𝒩₂.complex.obj.obj)).symm)
  let Sh := shiftFunctor (@DerivedCategory _ _ _ (HasDerivedCategory.standard
    (SheafOfModules.{u} (structureSheafRing W.toScheme.toRingedSpace)))) (1 : ℤ)
  exact (cancel_epi (Sh.mapIso τ.symm).hom).mp
    ((eq_zero_of_isDualizingComplex _ hd₀ W (Sh.map τ.inv ≫ g)).trans comp_zero.symm)

/-- A morphism of normalized complexes restricts on `U_i` to the comparison exactly when it
carries one normalization on `U_i` to the other. -/
theorem map_eq_compareHom_iff (𝒩₁ 𝒩₂ : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰)
    (i : ι) (f : 𝒩₁.complex ⟶ 𝒩₂.complex) :
    (derivedPullback (𝒰.U i).ι).map f.hom.hom = compareHom c 𝒩₁ 𝒩₂ i ↔
      (UpperShriek.shriekOf c (𝒰.U i).ι (hp.isShriekable_ι _)).map f ≫ (𝒩₂.localIso i).hom =
        (𝒩₁.localIso i).hom := by
  have key := UpperShriek.map_eq_pullbackOpenIso c (𝒰.U i).ι (hp.isShriekable_ι _) f
  refine ⟨fun h => ?_, fun h => ?_⟩
  · have h' := (cancel_mono _).mp ((cancel_epi _).mp (key.symm.trans h))
    exact (Iso.eq_comp_inv _).mp (ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ h'))
  · have hf : (UpperShriek.shriekOf c (𝒰.U i).ι (hp.isShriekable_ι _)).map f =
        (𝒩₁.localIso i).hom ≫ (𝒩₂.localIso i).inv := (Iso.eq_comp_inv _).mpr h
    exact key.trans (congrArg (fun t => _ ≫ t.hom.hom ≫ _) hf)

private theorem conj_comp_conj {C : Type*} [Category C] {a b c a' b' c' : C} (r₁ : a ≅ a')
    (r₂ : b ≅ b') (r₃ : c ≅ c') (x : a ⟶ b) (y : b ⟶ c) (z : a ⟶ c) (h : x ≫ y = z) :
    (r₁.inv ≫ x ≫ r₂.hom) ≫ (r₂.inv ≫ y ≫ r₃.hom) = r₁.inv ≫ z ≫ r₃.hom := by
  simp [← h]

/-- The comparisons of normalized complexes on `U_i` compose: the comparison of `𝒩₁` with `𝒩₂`
followed by that of `𝒩₂` with `𝒩₃` is the comparison of `𝒩₁` with `𝒩₃`. -/
theorem compareHom_comp (𝒩₁ 𝒩₂ 𝒩₃ : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰)
    (i : ι) : compareHom c 𝒩₁ 𝒩₂ i ≫ compareHom c 𝒩₂ 𝒩₃ i = compareHom c 𝒩₁ 𝒩₃ i := by
  have e₀ : ((𝒩₁.localIso i).hom ≫ (𝒩₂.localIso i).inv) ≫
      ((𝒩₂.localIso i).hom ≫ (𝒩₃.localIso i).inv) =
      (𝒩₁.localIso i).hom ≫ (𝒩₃.localIso i).inv := by simp
  have e : ((𝒩₁.localIso i).hom ≫ (𝒩₂.localIso i).inv).hom.hom ≫
      ((𝒩₂.localIso i).hom ≫ (𝒩₃.localIso i).inv).hom.hom =
      ((𝒩₁.localIso i).hom ≫ (𝒩₃.localIso i).inv).hom.hom := congrArg (fun t => t.hom.hom) e₀
  exact conj_comp_conj _ _ _ _ _ _ e

/-- The comparison on `U_i` of a normalized complex with itself is the identity. -/
theorem compareHom_self (𝒩 : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰) (i : ι) :
    compareHom c 𝒩 𝒩 i = 𝟙 _ := by
  simp only [compareHom, Iso.hom_inv_id]
  exact (congrArg (_ ≫ ·) (Category.id_comp _)).trans (Iso.inv_hom_id _)

/-- Morphisms inducing the comparisons `𝒩₁ → 𝒩₂` and `𝒩₂ → 𝒩₁` on every member compose to the
identity of `𝒩₁`. -/
private theorem comp_eq_id_of_map_eq_compareHom
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒩₁ 𝒩₂ : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰)
    {φ : 𝒩₁.complex.obj.obj ⟶ 𝒩₂.complex.obj.obj} {ψ : 𝒩₂.complex.obj.obj ⟶ 𝒩₁.complex.obj.obj}
    (hφ : ∀ i, (derivedPullback (𝒰.U i).ι).map φ = compareHom c 𝒩₁ 𝒩₂ i)
    (hψ : ∀ i, (derivedPullback (𝒰.U i).ι).map ψ = compareHom c 𝒩₂ 𝒩₁ i) :
    φ ≫ ψ = 𝟙 _ := by
  obtain ⟨_, _, hu⟩ := existsUnique_map_eq_compareHom c hωS 𝒩₁ 𝒩₁
  exact (hu _ fun i => (Functor.map_comp _ _ _).trans
      ((congrArg₂ (· ≫ ·) (hφ i) (hψ i)).trans (compareHom_comp c 𝒩₁ 𝒩₂ 𝒩₁ i))).trans
    (hu _ fun i => (CategoryTheory.Functor.map_id _ _).trans (compareHom_self c 𝒩₁ i).symm).symm

/-- **[Stacks, Tag 0AU7]** for the upper shriek functors of compactifications. In Situation 0AU4,
let `X` be of finite type over `S` and `𝒰` a finite open covering of `X` by schemes separated over
`S`. A dualizing complex normalized relative to `ω_S^•` and `𝒰` is unique up to unique
isomorphism: for two of them, `(K, α_i)` and `(K', α'_i)`, there is exactly one isomorphism
`K ≅ K'` carrying `α_i` to `α'_i` on every member. -/
theorem existsUnique_iso_ofCompactifications
    (hωS : haveI := hp.base_noetherian; IsDualizingComplex ωS.obj.obj)
    (𝒩 𝒩' : Normalized (UpperShriek.ofCompactifications c) hp ωS 𝒰) :
    ∃! e : 𝒩.complex ≅ 𝒩'.complex, ∀ i,
      ((UpperShriek.ofCompactifications c).shriek (𝒰.U i).ι (hp.isShriekable_ι _)).mapIso e ≪≫
        𝒩'.localIso i = 𝒩.localIso i := by
  obtain ⟨φ, hφ, huφ⟩ := existsUnique_map_eq_compareHom c hωS 𝒩 𝒩'
  obtain ⟨ψ, hψ, -⟩ := existsUnique_map_eq_compareHom c hωS 𝒩' 𝒩
  let Φ : 𝒩.complex ⟶ 𝒩'.complex := ObjectProperty.homMk (ObjectProperty.homMk φ)
  let e : 𝒩.complex ≅ 𝒩'.complex :=
    { hom := Φ, inv := ObjectProperty.homMk (ObjectProperty.homMk ψ)
      hom_inv_id := ObjectProperty.hom_ext _
        (ObjectProperty.hom_ext _ (comp_eq_id_of_map_eq_compareHom c hωS 𝒩 𝒩' hφ hψ))
      inv_hom_id := ObjectProperty.hom_ext _
        (ObjectProperty.hom_ext _ (comp_eq_id_of_map_eq_compareHom c hωS 𝒩' 𝒩 hψ hφ)) }
  refine ⟨e, fun i => Iso.ext ((map_eq_compareHom_iff c 𝒩 𝒩' i Φ).mp (hφ i)), fun e' he' => ?_⟩
  have h₁ : e'.hom.hom.hom = φ := huφ _ fun i =>
    (map_eq_compareHom_iff c 𝒩 𝒩' i e'.hom).mpr (congrArg Iso.hom (he' i))
  exact Iso.ext (ObjectProperty.hom_ext _ (ObjectProperty.hom_ext _ h₁))

end Normalized

end Stacks.Duality

end
