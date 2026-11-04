module

public import StacksFrontier.AlgebraicGeometry.Quot.CurveFamilyFibreBaseChange
public import StacksFrontier.AlgebraicGeometry.Quot.CompletionSubalgebraLimit
public import StacksFrontier.RingTheory.LocalRing.ResidueFieldAdjoinColimit
public import StacksFrontier.AlgebraicGeometry.Descent.FaithfullyFlatPushforwardUnit
public import StacksFrontier.AlgebraicGeometry.LimitDescentGlueing.Glueing
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Relative
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.RingTheory.GRing.EssFiniteType

/-!
# Étale contractions of a family of curves over an affine base

Let `F` be a family of curves over `Spec A` for an arbitrary ring `A`, `𝔭 ⊂ A` a prime, `X₀` the
fibre of `F` over `𝔭` and `h₀ : X₀ ⟶ Y₀` a morphism over `κ(𝔭)` to a proper scheme with
`𝒪_{Y₀} = h₀,*𝒪_{X₀}` and `R¹h₀,*𝒪_{X₀} = 0`. This file proves the conclusion of Stacks 0E7C,
`AlgebraicGeometry.CurveFamily.HasEtaleContraction`, for these data.

## Main results

* `AlgebraicGeometry.CurveFamily.hasEtaleContraction_of_affine`: the étale contraction of `h₀`
  exists for a family of curves over `Spec A`.

## References

* [Stacks Project, Tag 0E7C](https://stacks.math.columbia.edu/tag/0E7C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u

namespace AlgebraicGeometry

namespace CurveFamily

variable {B : BigFppfSite.{u}} {hZ : B.Contains integerBase}

section Stages

open CompletionSubalgebra

variable (B hZ) {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
  (hA : B.Contains (Spec (.of A)))

/-- The stage `Spec ℤ[s] ⊆ Spec A`, as an object of the site over the integers. -/
abbrev stageObj (i : (Finset A)ᵒᵖ) : BigFppfOver B integerBase hZ :=
  (BigAffineFppf.inclusion B integerBase hZ).obj ((diagram A ℤ B hZ hA).obj i)

/-- The transition maps between the stages. -/
abbrev stageMap {i j : (Finset A)ᵒᵖ} (e : i ⟶ j) : stageObj B hZ hA i ⟶ stageObj B hZ hA j :=
  (BigAffineFppf.inclusion B integerBase hZ).map ((diagram A ℤ B hZ hA).map e)

/-- The map `Spec A ⟶ Spec ℤ[s]`. -/
abbrev legMap (i : (Finset A)ᵒᵖ) : integerSiteObject B hZ hA ⟶ stageObj B hZ hA i :=
  (BigAffineFppf.inclusion B integerBase hZ).map ((cone A ℤ B hZ hA).π.app i)

/-- The maps `Spec A ⟶ Spec ℤ[s]` are compatible with the transition maps between the stages. -/
theorem legMap_stageMap {i j : (Finset A)ᵒᵖ} (e : i ⟶ j) :
    legMap B hZ hA i ≫ stageMap B hZ hA e = legMap B hZ hA j :=
  ((BigAffineFppf.inclusion B integerBase hZ).map_comp _ _).symm.trans
    (congrArg _ ((cone A ℤ B hZ hA).w e))

/-- The residue field `κ(𝔭 ∩ ℤ[s])`. -/
abbrev stageField (i : (Finset A)ᵒᵖ) : Type u :=
  (AdjoinResidueField.prime ℤ p i.unop).ResidueField

include hA in
/-- If the site contains `Spec κ(𝔭)`, then it contains `Spec κ(𝔭 ∩ ℤ[s])` for every stage. -/
theorem contains_stageField (hκ : B.Contains (Spec (.of p.ResidueField))) (i : (Finset A)ᵒᵖ) :
    B.Contains (Spec (.of (stageField p i))) :=
  BigFppfSite.contains_spec_of_mk_lt_cutoff B
    ((Cardinal.mk_le_of_injective (Ideal.ResidueField.map _ p _
      (AdjoinResidueField.prime_eq ℤ p i.unop)).injective).trans_lt
      (BigFppfSite.mk_lt_cutoff_of_contains_spec B hκ))

/-- The point `Spec κ(𝔭 ∩ ℤ[s]) ⟶ Spec ℤ[s]`. -/
abbrev stagePoint (hκ : B.Contains (Spec (.of p.ResidueField))) (i : (Finset A)ᵒᵖ) :
    integerSiteObject B hZ (contains_stageField B p hA hκ i) ⟶ stageObj B hZ hA i :=
  integerSiteMap B hZ _ (contains_sub A ℤ B hA i.unop)
    (Spec.map (CommRingCat.ofHom (algebraMap (sub A ℤ i.unop) (stageField p i))))

/-- The transition maps `Spec κ(𝔭 ∩ ℤ[t]) ⟶ Spec κ(𝔭 ∩ ℤ[s])`. -/
abbrev stageResidueMap {k m : (Finset A)ᵒᵖ} (e : k ⟶ m) :
    Spec (.of (stageField p k)) ⟶ Spec (.of (stageField p m)) :=
  (AdjoinResidueField.diagram ℤ p).map e

/-- The maps `Spec κ(𝔭) ⟶ Spec κ(𝔭 ∩ ℤ[s])`. -/
abbrev residueLeg (k : (Finset A)ᵒᵖ) : Spec (.of p.ResidueField) ⟶ Spec (.of (stageField p k)) :=
  (AdjoinResidueField.cone ℤ p).π.app k

/-- The stage points are compatible with the transition maps. -/
theorem stagePoint_comp (hκ : B.Contains (Spec (.of p.ResidueField))) {k m : (Finset A)ᵒᵖ}
    (e : k ⟶ m) :
    integerSiteMap B hZ (contains_stageField B p hA hκ k) (contains_stageField B p hA hκ m)
        (stageResidueMap p e) ≫ stagePoint B hZ p hA hκ m =
      stagePoint B hZ p hA hκ k ≫ stageMap B hZ hA e := by
  show integerSiteMap B hZ _ _ (Spec.map (CommRingCat.ofHom (Ideal.ResidueField.map
      (AdjoinResidueField.prime ℤ p m.unop) (AdjoinResidueField.prime ℤ p k.unop)
      (AdjoinResidueField.incl ℤ e.unop) (AdjoinResidueField.prime_comap ℤ p e.unop)))) ≫
      integerSiteMap B hZ _ (contains_sub A ℤ B hA m.unop)
        (Spec.map (CommRingCat.ofHom (algebraMap (sub A ℤ m.unop) (stageField p m)))) =
    integerSiteMap B hZ _ (contains_sub A ℤ B hA k.unop)
        (Spec.map (CommRingCat.ofHom (algebraMap (sub A ℤ k.unop) (stageField p k)))) ≫
      integerSiteMap B hZ _ _ (Spec.map (CommRingCat.ofHom (AdjoinResidueField.incl ℤ e.unop)))
  rw [integerSiteMap_comp, integerSiteMap_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext x
  exact Ideal.ResidueField.map_algebraMap _ _ _ _ x

/-- The stage points are compatible with the point of `Spec A`. -/
theorem stagePoint_leg (hκ : B.Contains (Spec (.of p.ResidueField))) (k : (Finset A)ᵒᵖ) :
    integerSiteMap B hZ hκ hA (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) ≫
        legMap B hZ hA k =
      integerSiteMap B hZ hκ (contains_stageField B p hA hκ k) (residueLeg p k) ≫
        stagePoint B hZ p hA hκ k := by
  show integerSiteMap B hZ _ _ (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))) ≫
      integerSiteMap B hZ _ (contains_sub A ℤ B hA k.unop)
        (Spec.map (CommRingCat.ofHom (sub A ℤ k.unop).val.toRingHom)) =
    integerSiteMap B hZ _ _ (Spec.map (CommRingCat.ofHom (Ideal.ResidueField.map
      (AdjoinResidueField.prime ℤ p k.unop) p (sub A ℤ k.unop).val.toRingHom
      (AdjoinResidueField.prime_eq ℤ p k.unop)))) ≫
      integerSiteMap B hZ _ (contains_sub A ℤ B hA k.unop)
        (Spec.map (CommRingCat.ofHom (algebraMap (sub A ℤ k.unop) (stageField p k))))
  rw [integerSiteMap_comp, integerSiteMap_comp, ← Spec.map_comp, ← Spec.map_comp]
  congr 2
  ext x
  exact (Ideal.ResidueField.map_algebraMap _ _ _ _ x).symm

/-- The stage points are compatible with the point of `Spec A`, on schemes. -/
theorem stagePoint_leg_scheme (k : (Finset A)ᵒᵖ) :
    Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)) ≫
        Spec.map (CommRingCat.ofHom (sub A ℤ k.unop).val.toRingHom) =
      residueLeg p k ≫
        Spec.map (CommRingCat.ofHom (algebraMap (sub A ℤ k.unop) (stageField p k))) := by
  show _ = Spec.map (CommRingCat.ofHom (Ideal.ResidueField.map
      (AdjoinResidueField.prime ℤ p k.unop) p (sub A ℤ k.unop).val.toRingHom
      (AdjoinResidueField.prime_eq ℤ p k.unop))) ≫ _
  rw [← Spec.map_comp, ← Spec.map_comp]
  congr 1
  ext x
  exact (Ideal.ResidueField.map_algebraMap _ _ _ _ x).symm

/-- A homomorphism of fields induces a flat surjective morphism of spectra. -/
theorem flat_surjective_specMap_of_field {K L : Type u} [Field K] [Field L] (f : K →+* L) :
    Flat (Spec.map (CommRingCat.ofHom f)) ∧ Surjective (Spec.map (CommRingCat.ofHom f)) :=
  (flat_and_surjective_SpecMap_iff _).mpr (by
    let := f.toAlgebra
    exact (inferInstance : Module.FaithfullyFlat K L))

end Stages

/-- An isomorphism over `S` with a base change along `π` gives a cartesian square. -/
theorem isPullback_of_overIso {S T : Scheme.{u}} (π : S ⟶ T) {U : Over S} {W : Over T}
    (φ : U ≅ (Over.pullback π).obj W) :
    IsPullback (φ.hom.left ≫ Limits.pullback.fst W.hom π) U.hom W.hom π := by
  refine (IsPullback.of_hasPullback W.hom π).of_iso ((Over.forget S).mapIso φ).symm (Iso.refl _)
    (Iso.refl _) (Iso.refl _) (by simp) ?_ (by simp) (by simp)
  have := Over.w φ.inv
  simp only [Over.pullback_obj_hom] at this
  simp [this]

open CompletionSubalgebra in
/-- **Étale contractions over an affine base.** Let `F` be a family of curves over `Spec A`,
`𝔭 ⊂ A` a prime with fibre `X₀`, and `h₀ : X₀ ⟶ Y₀` a morphism over `κ(𝔭)` to a proper scheme with
`𝒪_{Y₀} = h₀,*𝒪_{X₀}` (`h0`) and `R¹h₀,*𝒪_{X₀} = 0` (`hR1`). Then there are an étale
`U ⟶ Spec A` with a lift of the point `𝔭`, a family of curves `G` over `U` and a morphism from the
base change of `F` to `G` restricting to `h₀` on the fibres over that lift
(`AlgebraicGeometry.CurveFamily.HasEtaleContraction`). -/
theorem hasEtaleContraction_of_affine
    {A : Type u} [CommRing A] (p : Ideal A) [p.IsPrime]
    (hA : B.Contains (Spec (.of A))) (hκ : B.Contains (Spec (.of p.ResidueField)))
    (F : CurveFamily B hZ) (hF : F.base = integerSiteObject B hZ hA)
    {X₀ : Scheme.{u}} (hX₀ : B.Contains X₀) (pX₀ : X₀ ⟶ Spec (.of p.ResidueField))
    (ι : yoneda.obj (integerSiteObject B hZ hX₀) ⟶ F.total.obj)
    (hι : IsPullback ι (yoneda.map (integerSiteMap B hZ hX₀ hκ pX₀)) (F.toBaseYonedaOfEq hF)
      (yoneda.map (integerSiteMap B hZ hκ hA
        (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField))))))
    {Y₀ : Scheme.{u}} (hY₀ : B.Contains Y₀) (pY₀ : Y₀ ⟶ Spec (.of p.ResidueField))
    [IsProper pY₀] (h₀ : X₀ ⟶ Y₀) (hh₀ : h₀ ≫ pY₀ = pX₀)
    (h0 : IsIso (C := Y₀.Modules) (Scheme.Modules.unitToPushforwardUnit h₀))
    (hR1 : IsZero (((Scheme.Modules.pushforward h₀).rightDerived 1).obj
      (SheafOfModules.unit X₀.ringCatSheaf))) :
    HasEtaleContraction hA F hF hκ (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))
      hX₀ pX₀ ι hY₀ pY₀ h₀ := by
  classical
  have hof : ∀ {P X Y Z : (BigFppfOver B integerBase hZ)ᵒᵖ ⥤ Type u} {fst fst' : P ⟶ X}
      {snd snd' : P ⟶ Y} {f f' : X ⟶ Z} {g g' : Y ⟶ Z}, IsPullback fst snd f g → fst = fst' →
        snd = snd' → f = f' → g = g' → IsPullback fst' snd' f' g' := by
    rintro _ _ _ _ _ _ _ _ _ _ _ _ h rfl rfl rfl rfl
    exact h
  obtain ⟨i, Fi, hFi, δ, hδ⟩ :=
    exists_hom_to_stage_of_isLimit (cone A ℤ B hZ hA) (isLimit A ℤ B hZ hA) F hF
  obtain ⟨iF, hiF1, -⟩ := exists_iso_pullback_of_hom hF hFi (legMap B hZ hA i) δ hδ
  have sqi0 := Fi.isPullback_pullbackHom_yoneda hFi (legMap B hZ hA i)
  have sqi : IsPullback
      (iF.hom ≫ ((Fi.ofBaseEq hFi).pullbackHom (legMap B hZ hA i)).totalMap.hom)
      (F.toBaseYonedaOfEq hF) (Fi.toBaseYonedaOfEq hFi) (yoneda.map (legMap B hZ hA i)) :=
    sqi0.of_iso iF.symm (Iso.refl _) (Iso.refl _) (Iso.refl _) (by simp)
      ((Category.comp_id _).trans ((Iso.inv_comp_eq _).mpr hiF1.symm).symm) (by simp) (by simp)
  have stage : ∀ (k : (Finset A)ᵒᵖ) (e : k ⟶ i),
      ∃ φk : F.total.obj ⟶ ((Fi.ofBaseEq hFi).pullback (stageMap B hZ hA e)).total.obj,
        φk ≫ ((Fi.ofBaseEq hFi).pullbackHom (stageMap B hZ hA e)).totalMap.hom =
          iF.hom ≫ ((Fi.ofBaseEq hFi).pullbackHom (legMap B hZ hA i)).totalMap.hom ∧
        IsPullback φk (F.toBaseYonedaOfEq hF)
          ((Fi.ofBaseEq hFi).pullback (stageMap B hZ hA e)).toBaseYoneda
          (yoneda.map (legMap B hZ hA k)) := by
    intro k e
    have sqk := Fi.isPullback_pullbackHom_yoneda hFi (stageMap B hZ hA e)
    have h1 := hof sqi rfl rfl rfl ((congrArg yoneda.map (legMap_stageMap B hZ hA e).symm).trans
      (yoneda.map_comp _ _))
    exact ⟨_, sqk.lift_fst _ _ _, IsPullback.of_right' h1 sqk⟩
  have hcκ := AdjoinResidueField.isLimit ℤ p
  have : ∀ {k m : (Finset A)ᵒᵖ} (e : k ⟶ m), IsAffineHom ((AdjoinResidueField.diagram ℤ p).map e) :=
    fun _ => inferInstance
  have : ∀ k : (Finset A)ᵒᵖ, CompactSpace ((AdjoinResidueField.diagram ℤ p).obj k) := fun k =>
    inferInstanceAs (CompactSpace (Spec (.of (stageField p k))))
  have : ∀ k : (Finset A)ᵒᵖ, QuasiSeparatedSpace ((AdjoinResidueField.diagram ℤ p).obj k) :=
    fun k => inferInstanceAs (QuasiSeparatedSpace (Spec (.of (stageField p k))))
  have hYfp : FinitePresentation pY₀ := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨j, Yj, pj, gj, hpj, hpbj⟩ :=
    LimitDescent.exists_isPullback_of_finitePresentation_of_essentiallySmall
      (AdjoinResidueField.diagram ℤ p) (AdjoinResidueField.cone ℤ p) hcκ (X := Y₀) pY₀ hYfp
  let m := IsCofiltered.min i j
  let em : m ⟶ i := IsCofiltered.minToLeft i j
  let emj : m ⟶ j := IsCofiltered.minToRight i j
  obtain ⟨φm, hφm1, sqm⟩ := stage m em
  let Fm := (Fi.ofBaseEq hFi).pullback (stageMap B hZ hA em)
  obtain ⟨Xm, hXmp, hXm, ιm, -, hιm⟩ := exists_fibre Fm (rfl : Fm.base = stageObj B hZ hA m)
    (contains_stageField B p hA hκ m) (stagePoint B hZ p hA hκ m)
  have := hXmp
  have eFm : Fm.toBaseYonedaOfEq (rfl : Fm.base = stageObj B hZ hA m) = Fm.toBaseYoneda :=
    toBaseYonedaOfEq_rfl' Fm
  rw [eFm] at hιm
  have hXmP : B.Contains (Limits.pullback Xm.hom (residueLeg p m)) :=
    Scheme.size_pullback_lt _ _ hXm hκ
  obtain ⟨ι', hι'e, hι'⟩ := exists_fibre_baseChange sqm (residueLeg p m)
    (stagePoint_leg B hZ p hA hκ m) hιm hXmP (IsPullback.of_hasPullback Xm.hom (residueLeg p m))
  obtain ⟨eX, heX1, heX2⟩ := fibreIso (F.toBaseYonedaOfEq hF) hι hι'
  have hY1 : IsPullback gj pY₀ pj (residueLeg p m ≫ (AdjoinResidueField.diagram ℤ p).map emj) := by
    have e1 : (AdjoinResidueField.cone ℤ p).π.app j =
        residueLeg p m ≫ (AdjoinResidueField.diagram ℤ p).map emj :=
      ((AdjoinResidueField.cone ℤ p).w emj).symm
    rw [← e1]
    exact hpbj
  have sqYm := IsPullback.of_right' hY1
    (IsPullback.of_hasPullback pj ((AdjoinResidueField.diagram ℤ p).map emj))
  let Ym : Over ((AdjoinResidueField.diagram ℤ p).obj m) :=
    Over.mk (Limits.pullback.snd pj ((AdjoinResidueField.diagram ℤ p).map emj))
  let XO : Over (AdjoinResidueField.cone ℤ p).pt := Over.mk pX₀
  let YO : Over (AdjoinResidueField.cone ℤ p).pt := Over.mk pY₀
  let isoXO : XO ≅ (Over.pullback ((AdjoinResidueField.cone ℤ p).π.app m)).obj Xm :=
    Over.isoMk eX heX1
  let isoYO : YO ≅ (Over.pullback ((AdjoinResidueField.cone ℤ p).π.app m)).obj Ym :=
    Over.isoMk sqYm.isoPullback (sqYm.isoPullback_hom_snd)
  let h₀O : XO ⟶ YO := Over.homMk h₀ hh₀
  have hXmfp : FinitePresentation Xm.hom := ⟨inferInstanceAs (LocallyOfFinitePresentation Xm.hom),
    inferInstanceAs (QuasiCompact Xm.hom), inferInstanceAs (QuasiSeparated Xm.hom)⟩
  have hYmfp : FinitePresentation Ym.hom := by
    obtain ⟨h1, h2, h3⟩ := hpj
    show FinitePresentation (Limits.pullback.snd pj ((AdjoinResidueField.diagram ℤ p).map emj))
    exact ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨n, en, g, α, β, hα, hβ, hαβ⟩ :=
    exists_morphism_after_baseChange (AdjoinResidueField.diagram ℤ p) (AdjoinResidueField.cone ℤ p)
      hcκ m Xm Ym hXmfp hYmfp (isoXO.inv ≫ h₀O ≫ isoYO.hom)
  let Xn := (Over.pullback ((AdjoinResidueField.diagram ℤ p).map en)).obj Xm
  let Yn := (Over.pullback ((AdjoinResidueField.diagram ℤ p).map en)).obj Ym
  let ψX : XO ≅ (Over.pullback ((AdjoinResidueField.cone ℤ p).π.app n)).obj Xn := isoXO ≪≫ α.symm
  let ψY : YO ≅ (Over.pullback ((AdjoinResidueField.cone ℤ p).π.app n)).obj Yn := isoYO ≪≫ β.symm
  have sqXn := isPullback_of_overIso ((AdjoinResidueField.cone ℤ p).π.app n) ψX
  have sqYn := isPullback_of_overIso ((AdjoinResidueField.cone ℤ p).π.app n) ψY
  have hEqO : ψX.hom ≫ (Over.pullback ((AdjoinResidueField.cone ℤ p).π.app n)).map g =
      h₀O ≫ ψY.hom := by
    have h1 : (Over.pullback ((AdjoinResidueField.cone ℤ p).π.app n)).map g =
        α.hom ≫ (isoXO.inv ≫ h₀O ≫ isoYO.hom) ≫ β.inv := by
      rw [← Category.assoc α.hom, hαβ, Category.assoc, Iso.hom_inv_id, Category.comp_id]
    rw [h1]
    simp [ψX, ψY]
  have hcompn : (ψX.hom.left ≫ Limits.pullback.fst Xn.hom
      ((AdjoinResidueField.cone ℤ p).π.app n)) ≫ g.left =
      h₀ ≫ ψY.hom.left ≫ Limits.pullback.fst Yn.hom ((AdjoinResidueField.cone ℤ p).π.app n) := by
    calc (ψX.hom.left ≫ Limits.pullback.fst Xn.hom ((AdjoinResidueField.cone ℤ p).π.app n)) ≫
          g.left
        = ψX.hom.left ≫ (((Over.pullback ((AdjoinResidueField.cone ℤ p).π.app n)).map g).left ≫
            Limits.pullback.fst Yn.hom ((AdjoinResidueField.cone ℤ p).π.app n)) := by
          rw [overPullback_map_left_fst, Category.assoc]
      _ = (ψX.hom ≫ (Over.pullback ((AdjoinResidueField.cone ℤ p).π.app n)).map g).left ≫
            Limits.pullback.fst Yn.hom ((AdjoinResidueField.cone ℤ p).π.app n) := by
          rw [Over.comp_left, Category.assoc]
      _ = (h₀O ≫ ψY.hom).left ≫
            Limits.pullback.fst Yn.hom ((AdjoinResidueField.cone ℤ p).π.app n) := by
          rw [hEqO]
      _ = h₀ ≫ ψY.hom.left ≫
            Limits.pullback.fst Yn.hom ((AdjoinResidueField.cone ℤ p).π.app n) := by
          rw [Over.comp_left, Category.assoc]
          rfl
  have := hpj.1
  have := hpj.2.1
  have := hpj.2.2
  have : LocallyOfFinitePresentation Ym.hom :=
    inferInstanceAs (LocallyOfFinitePresentation
      (Limits.pullback.snd pj ((AdjoinResidueField.diagram ℤ p).map emj)))
  have : QuasiCompact Ym.hom :=
    inferInstanceAs
      (QuasiCompact (Limits.pullback.snd pj ((AdjoinResidueField.diagram ℤ p).map emj)))
  have : QuasiSeparated Ym.hom :=
    inferInstanceAs
      (QuasiSeparated (Limits.pullback.snd pj ((AdjoinResidueField.diagram ℤ p).map emj)))
  have : CompactSpace Yn.left :=
    QuasiCompact.compactSpace_of_compactSpace
      (Limits.pullback.snd Ym.hom ((AdjoinResidueField.diagram ℤ p).map en))
  have : QuasiSeparatedSpace Yn.left :=
    quasiSeparatedSpace_of_quasiSeparated
      (Limits.pullback.snd Ym.hom ((AdjoinResidueField.diagram ℤ p).map en))
  have : CompactSpace (Over.mk (𝟙 ((AdjoinResidueField.diagram ℤ p).obj n))).left :=
    inferInstanceAs (CompactSpace ((AdjoinResidueField.diagram ℤ p).obj n))
  have : QuasiSeparatedSpace (Over.mk (𝟙 ((AdjoinResidueField.diagram ℤ p).obj n))).left :=
    inferInstanceAs (QuasiSeparatedSpace ((AdjoinResidueField.diagram ℤ p).obj n))
  let f₀ : Yn ⟶ Over.mk (𝟙 ((AdjoinResidueField.diagram ℤ p).obj n)) :=
    Over.homMk Yn.hom (Category.comp_id _)
  have : LocallyOfFiniteType f₀.left :=
    inferInstanceAs (LocallyOfFiniteType
      (Limits.pullback.snd Ym.hom ((AdjoinResidueField.diagram ℤ p).map en)))
  have : IsProper ((Over.pullback ((AdjoinResidueField.cone ℤ p).π.app n)).map f₀).left := by
    have : IsIso ψY.inv.left := inferInstanceAs (IsIso ((Over.forget _).map ψY.inv))
    have hP : IsProper ((Over.pullback ((AdjoinResidueField.cone ℤ p).π.app n)).obj Yn).hom := by
      rw [← Over.w ψY.inv]
      show IsProper (ψY.inv.left ≫ pY₀)
      infer_instance
    have hw2 := Over.w ((Over.pullback ((AdjoinResidueField.cone ℤ p).π.app n)).map f₀)
    have : IsIso ((Over.pullback ((AdjoinResidueField.cone ℤ p).π.app n)).obj
        (Over.mk (𝟙 ((AdjoinResidueField.diagram ℤ p).obj n)))).hom :=
      inferInstanceAs (IsIso (Limits.pullback.snd
        (𝟙 ((AdjoinResidueField.diagram ℤ p).obj n)) ((AdjoinResidueField.cone ℤ p).π.app n)))
    have e2 : ((Over.pullback ((AdjoinResidueField.cone ℤ p).π.app n)).map f₀).left =
        ((Over.pullback ((AdjoinResidueField.cone ℤ p).π.app n)).obj Yn).hom ≫
          inv ((Over.pullback ((AdjoinResidueField.cone ℤ p).π.app n)).obj
            (Over.mk (𝟙 ((AdjoinResidueField.diagram ℤ p).obj n)))).hom := by
      rw [← hw2, Category.assoc, IsIso.hom_inv_id, Category.comp_id]
    rw [e2]
    infer_instance
  obtain ⟨q, eq', hpropq⟩ := exists_isProper_baseChange_of_isLimit (AdjoinResidueField.diagram ℤ p)
    (AdjoinResidueField.cone ℤ p) n hcκ Yn (Over.mk (𝟙 ((AdjoinResidueField.diagram ℤ p).obj n))) f₀
  let Xq := (Over.pullback ((AdjoinResidueField.diagram ℤ p).map eq')).obj Xn
  let Yq := (Over.pullback ((AdjoinResidueField.diagram ℤ p).map eq')).obj Yn
  let hq : Xq ⟶ Yq := (Over.pullback ((AdjoinResidueField.diagram ℤ p).map eq')).map g
  have hYq : IsProper Yq.hom := by
    have hw2 := Over.w ((Over.pullback ((AdjoinResidueField.diagram ℤ p).map eq')).map f₀)
    have := hpropq
    have : IsIso ((Over.pullback ((AdjoinResidueField.diagram ℤ p).map eq')).obj
        (Over.mk (𝟙 ((AdjoinResidueField.diagram ℤ p).obj n)))).hom :=
      inferInstanceAs (IsIso (Limits.pullback.snd (𝟙 ((AdjoinResidueField.diagram ℤ p).obj n))
        ((AdjoinResidueField.diagram ℤ p).map eq')))
    rw [← hw2]
    infer_instance
  have ecq : (AdjoinResidueField.cone ℤ p).π.app n =
      residueLeg p q ≫ (AdjoinResidueField.diagram ℤ p).map eq' :=
    ((AdjoinResidueField.cone ℤ p).w eq').symm
  have fibreLift : ∀ {W : Scheme.{u}} {Z : Over ((AdjoinResidueField.diagram ℤ p).obj n)}
      {pW : W ⟶ Spec (.of p.ResidueField)} {w : W ⟶ Z.left},
      IsPullback w pW Z.hom ((AdjoinResidueField.cone ℤ p).π.app n) →
      ∃ zq : W ⟶ ((Over.pullback ((AdjoinResidueField.diagram ℤ p).map eq')).obj Z).left,
        zq ≫ Limits.pullback.fst Z.hom ((AdjoinResidueField.diagram ℤ p).map eq') = w ∧
        IsPullback zq pW ((Over.pullback ((AdjoinResidueField.diagram ℤ p).map eq')).obj Z).hom
          (residueLeg p q) := by
    intro W Z pW w h
    have pb := IsPullback.of_hasPullback Z.hom ((AdjoinResidueField.diagram ℤ p).map eq')
    rw [ecq] at h
    exact ⟨_, pb.lift_fst _ _ _, IsPullback.of_right' h pb⟩
  have pbY := IsPullback.of_hasPullback Yn.hom ((AdjoinResidueField.diagram ℤ p).map eq')
  obtain ⟨xq, hxq1, sqXq⟩ := fibreLift (pW := pX₀) sqXn
  obtain ⟨yq, hyq1, sqYq⟩ := fibreLift (pW := pY₀) sqYn
  have hqcomp : xq ≫ hq.left = h₀ ≫ yq := by
    apply pbY.hom_ext
    · rw [Category.assoc, overPullback_map_left_fst, ← Category.assoc, hxq1, hcompn,
        Category.assoc, hyq1]
    · rw [Category.assoc, overPullback_map_left_snd,
        show xq ≫ Limits.pullback.snd Xn.hom ((AdjoinResidueField.diagram ℤ p).map eq') =
          pX₀ ≫ residueLeg p q from sqXq.w,
        Category.assoc,
        show yq ≫ Limits.pullback.snd Yn.hom ((AdjoinResidueField.diagram ℤ p).map eq') =
          pY₀ ≫ residueLeg p q from sqYq.w]
      exact (congrArg (· ≫ residueLeg p q) hh₀.symm).trans (Category.assoc _ _ _)
  have hsqh : IsPullback xq h₀ hq.left yq :=
    IsPullback.of_bot (by rw [hh₀, Over.w hq]; exact sqXq) hqcomp sqYq
  have hfs := flat_surjective_specMap_of_field (Ideal.ResidueField.map
    (AdjoinResidueField.prime ℤ p q.unop) p (sub A ℤ q.unop).val.toRingHom
    (AdjoinResidueField.prime_eq ℤ p q.unop))
  have : Flat (residueLeg p q) := hfs.1
  have : Surjective (residueLeg p q) := hfs.2
  have : Flat yq := MorphismProperty.of_isPullback (P := @Flat) sqYq.flip hfs.1
  have hyqs : Function.Surjective yq.base :=
    (MorphismProperty.of_isPullback (P := @Surjective) sqYq.flip hfs.2).surj
  have isProper_pullback : ∀ {a b : (Finset A)ᵒᵖ} (e : a ⟶ b) (Z : Over ((AdjoinResidueField.diagram
      ℤ p).obj b)), IsProper Z.hom → IsProper ((Over.pullback ((AdjoinResidueField.diagram ℤ p).map
        e)).obj Z).hom := fun e Z hZ => MorphismProperty.of_isPullback (P := @IsProper)
    (IsPullback.of_hasPullback Z.hom ((AdjoinResidueField.diagram ℤ p).map e)) hZ
  have : IsProper Xn.hom := isProper_pullback en Xm hXmp
  have : IsProper Xq.hom := isProper_pullback eq' Xn inferInstance
  have := hYq
  have : IsProper hq.left := by
    have : IsProper (hq.left ≫ Yq.hom) := by rw [Over.w hq]; infer_instance
    exact IsProper.of_comp hq.left Yq.hom
  have h0q := Scheme.Modules.isIso_unitToPushforwardUnit_of_isPullback hsqh hyqs h0
  have hR1q := Scheme.Modules.isZero_rightDerived_unit_of_isPullback hsqh hyqs 1 hR1
  have stageComp : ∀ {a b c : (Finset A)ᵒᵖ} (e₁ : a ⟶ b) (e₂ : b ⟶ c),
      yoneda.map (stageMap B hZ hA (e₁ ≫ e₂)) =
        yoneda.map (stageMap B hZ hA e₁) ≫ yoneda.map (stageMap B hZ hA e₂) := fun e₁ e₂ =>
    (congrArg yoneda.map ((congrArg (BigAffineFppf.inclusion B integerBase hZ).map
      ((diagram A ℤ B hZ hA).map_comp e₁ e₂)).trans
        ((BigAffineFppf.inclusion B integerBase hZ).map_comp _ _))).trans (yoneda.map_comp _ _)
  have famSq : ∀ {a b : (Finset A)ᵒᵖ} (e₁ : a ⟶ b) (e₂ : b ⟶ i),
      ∃ ψ : ((Fi.ofBaseEq hFi).pullback (stageMap B hZ hA (e₁ ≫ e₂))).total.obj ⟶
          ((Fi.ofBaseEq hFi).pullback (stageMap B hZ hA e₂)).total.obj,
        ψ ≫ ((Fi.ofBaseEq hFi).pullbackHom (stageMap B hZ hA e₂)).totalMap.hom =
          ((Fi.ofBaseEq hFi).pullbackHom (stageMap B hZ hA (e₁ ≫ e₂))).totalMap.hom ∧
        IsPullback ψ ((Fi.ofBaseEq hFi).pullback (stageMap B hZ hA (e₁ ≫ e₂))).toBaseYoneda
          ((Fi.ofBaseEq hFi).pullback (stageMap B hZ hA e₂)).toBaseYoneda
          (yoneda.map (stageMap B hZ hA e₁)) := by
    intro a b e₁ e₂
    have s1 := Fi.isPullback_pullbackHom_yoneda hFi (stageMap B hZ hA (e₁ ≫ e₂))
    have s2 := Fi.isPullback_pullbackHom_yoneda hFi (stageMap B hZ hA e₂)
    exact ⟨_, s2.lift_fst _ _ _, IsPullback.of_right' (hof s1 rfl rfl rfl (stageComp e₁ e₂)) s2⟩
  obtain ⟨ψnm, hψnm1, sqnm⟩ := famSq en em
  have hXnC : B.Contains Xn.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact Xn.hom (contains_stageField B p hA hκ n)
  obtain ⟨ιn, hιn1, hιn⟩ := exists_fibre_baseChange sqnm (stageResidueMap p en)
    (stagePoint_comp B hZ p hA hκ en).symm hιm hXnC
    (IsPullback.of_hasPullback Xm.hom ((AdjoinResidueField.diagram ℤ p).map en))
  obtain ⟨ψqn, hψqn1, sqqn⟩ := famSq eq' (en ≫ em)
  have hXqC : B.Contains Xq.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact Xq.hom (contains_stageField B p hA hκ q)
  obtain ⟨ιq, hιq1, hιq⟩ := exists_fibre_baseChange sqqn (stageResidueMap p eq')
    (stagePoint_comp B hZ p hA hκ eq').symm hιn hXqC
    (IsPullback.of_hasPullback Xn.hom ((AdjoinResidueField.diagram ℤ p).map eq'))
  have : Algebra.FiniteType ℤ (sub A ℤ q.unop) :=
    (Subalgebra.fg_iff_finiteType _).mp (Subalgebra.fg_adjoin_finset _)
  have : IsNoetherianRing (sub A ℤ q.unop) := Algebra.FiniteType.isNoetherianRing ℤ _
  have hGRq : IsGRing (Localization.AtPrime (AdjoinResidueField.prime ℤ p q.unop)) :=
    isGRing_of_essFiniteType (R := ℤ) isGRing_basic_examples.{0, 0}.2.2.1
  let Fq := (Fi.ofBaseEq hFi).pullback (stageMap B hZ hA (eq' ≫ en ≫ em))
  have hFq : Fq.base = integerSiteObject B hZ (contains_sub A ℤ B hA q.unop) := rfl
  have hιq' : IsPullback ιq (yoneda.map (integerSiteMap B hZ hXqC
        (contains_stageField B p hA hκ q) Xq.hom)) (Fq.toBaseYonedaOfEq hFq)
      (yoneda.map (integerSiteMap B hZ (contains_stageField B p hA hκ q)
        (contains_sub A ℤ B hA q.unop) (Spec.map (CommRingCat.ofHom
          (algebraMap (sub A ℤ q.unop) (AdjoinResidueField.prime ℤ p q.unop).ResidueField))))) :=
    hof hιq rfl rfl (toBaseYonedaOfEq_rfl' Fq).symm rfl
  have hYqC : B.Contains Yq.left :=
    Scheme.size_lt_of_locallyOfFiniteType_of_quasiCompact Yq.hom (contains_stageField B p hA hκ q)
  have : IsProper (Y := Spec (.of (stageField p q))) Yq.hom := hYq
  have H := hasEtaleContraction_of_isGRing_localization (AdjoinResidueField.prime ℤ p q.unop)
    hGRq (contains_sub A ℤ B hA q.unop) (contains_stageField B p hA hκ q) Fq hFq hXqC Xq.hom ιq
    hιq' hYqC Yq.hom hq.left (Over.w hq) h0q hR1q
  obtain ⟨φq, hφq1, sqq⟩ := stage q (eq' ≫ en ≫ em)
  have hφ : φq ≫ Fq.toBaseYonedaOfEq hFq = F.toBaseYonedaOfEq hF ≫
      yoneda.map (integerSiteMap B hZ hA (contains_sub A ℤ B hA q.unop)
        (Spec.map (CommRingCat.ofHom (sub A ℤ q.unop).val.toRingHom))) :=
    (congrArg (φq ≫ ·) (toBaseYonedaOfEq_rfl' Fq)).trans sqq.w
  have hαinv : α.inv.left ≫ α.hom.left = 𝟙 _ := by
    rw [← Over.comp_left, α.inv_hom_id, Over.id_left]
  have S1 : eX.hom ≫ Limits.pullback.fst Xm.hom (residueLeg p m) =
      xq ≫ Limits.pullback.fst Xn.hom ((AdjoinResidueField.diagram ℤ p).map eq') ≫
        Limits.pullback.fst Xm.hom ((AdjoinResidueField.diagram ℤ p).map en) :=
    (congrArg (eX.hom ≫ ·) (((Category.id_comp _).symm.trans
      (congrArg (· ≫ Limits.pullback.fst Xm.hom (residueLeg p m)) hαinv.symm)).trans
        ((Category.assoc _ _ _).trans (congrArg (α.inv.left ≫ ·) hα)))).trans
      (((Category.assoc _ _ _).symm.trans (Category.assoc _ _ _).symm).trans
        ((congrArg (· ≫ Limits.pullback.fst Xm.hom ((AdjoinResidueField.diagram ℤ p).map en))
          hxq1.symm).trans (Category.assoc _ _ _)))
  have Y1 : yoneda.map (integerSiteMap B hZ hX₀ hXmP eX.hom) ≫
      yoneda.map (integerSiteMap B hZ hXmP hXm (Limits.pullback.fst Xm.hom (residueLeg p m))) =
      yoneda.map (integerSiteMap B hZ hX₀ hXqC xq) ≫
        yoneda.map (integerSiteMap B hZ hXqC hXnC
          (Limits.pullback.fst Xn.hom ((AdjoinResidueField.diagram ℤ p).map eq'))) ≫
        yoneda.map (integerSiteMap B hZ hXnC hXm
          (Limits.pullback.fst Xm.hom ((AdjoinResidueField.diagram ℤ p).map en))) :=
    (yoneda_map_integerSiteMap_comp _ _).trans
      ((congrArg (fun f => yoneda.map (integerSiteMap B hZ hX₀ hXm f)) S1).trans
        ((yoneda_map_integerSiteMap_comp _ _).symm.trans
          (congrArg (yoneda.map (integerSiteMap B hZ hX₀ hXqC xq) ≫ ·)
            (yoneda_map_integerSiteMap_comp _ _).symm)))
  have e1 : yoneda.map (integerSiteMap B hZ hκ hA
      (Spec.map (CommRingCat.ofHom (algebraMap A p.ResidueField)))) ≫
        yoneda.map (legMap B hZ hA q) =
      yoneda.map (integerSiteMap B hZ hκ (contains_stageField B p hA hκ q) (residueLeg p q)) ≫
        yoneda.map (stagePoint B hZ p hA hκ q) := by
    rw [← yoneda.map_comp, ← yoneda.map_comp, stagePoint_leg]
  have e2 : yoneda.map (integerSiteMap B hZ hX₀ hκ pX₀) ≫
      yoneda.map (integerSiteMap B hZ hκ (contains_stageField B p hA hκ q) (residueLeg p q)) =
      yoneda.map (integerSiteMap B hZ hX₀ hXqC xq) ≫
        yoneda.map (integerSiteMap B hZ hXqC (contains_stageField B p hA hκ q)
          (Limits.pullback.snd Xn.hom ((AdjoinResidueField.diagram ℤ p).map eq'))) :=
    (yoneda_map_integerSiteMap_comp _ _).trans
      ((congrArg (fun f => yoneda.map (integerSiteMap B hZ hX₀ (contains_stageField B p hA hκ q) f))
        sqXq.w.symm).trans (yoneda_map_integerSiteMap_comp _ _).symm)
  have sqFq := Fi.isPullback_pullbackHom_yoneda hFi (stageMap B hZ hA (eq' ≫ en ≫ em))
  have hιx : ι ≫ φq = yoneda.map (integerSiteMap B hZ hX₀ hXqC xq) ≫ ιq := by
    apply sqFq.hom_ext
    · rw [Category.assoc, hφq1, ← hφm1, ← heX2, Category.assoc, reassoc_of% hι'e, Category.assoc,
        ← hψqn1, reassoc_of% hιq1, ← hψnm1, reassoc_of% hιn1]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ (ιm ≫
        ((Fi.ofBaseEq hFi).pullbackHom (stageMap B hZ hA em)).totalMap.hom)) Y1).trans
          ((Category.assoc _ _ _).trans (congrArg (_ ≫ ·) (Category.assoc _ _ _))))
    · rw [Category.assoc, sqq.w, reassoc_of% hι.w, Category.assoc, hιq.w, e1]
      exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫
        yoneda.map (stagePoint B hZ p hA hκ q)) e2).trans (Category.assoc _ _ _))
  exact HasEtaleContraction.baseChange
    (Spec.map (CommRingCat.ofHom (sub A ℤ q.unop).val.toRingHom)) φq hφ (residueLeg p q)
    (stagePoint_leg_scheme p q) H hX₀ pX₀ ι hι xq sqXq.w hιx hY₀ pY₀ yq sqYq h₀ hh₀
    hqcomp.symm

end CurveFamily

end AlgebraicGeometry

end
