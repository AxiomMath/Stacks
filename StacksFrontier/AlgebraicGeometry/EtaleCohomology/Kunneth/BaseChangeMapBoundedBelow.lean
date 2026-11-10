module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Kunneth.EtaleCoefficientsAbelianBaseChange
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.BaseChangeMatePasting
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedPushforward.OrdinaryAndDerivedCounit
public import Mathlib.Algebra.Homology.DerivedCategory.DerivabilityStructureInjectives
public import StacksFrontier.CategoryTheory.Adjunction.Mates
public import StacksFrontier.CategoryTheory.Localization.MapHomotopyCategoryAdjunctionCounit
public import StacksFrontier.Topology.Sheaves.Cohomology.HigherDirectImage.AbelianDerivedBaseChangeCriteria

/-!
# The base change map of `D(-_étale, Λ)` on bounded below objects

Let

```
X' <-h-- Y
|f'      |e
S  <-g-- T
```

be a commutative square of schemes, `h ≫ f' = e ≫ g`. The base change map
`Stacks.EtaleCohomology.EtaleCoefficients.baseChangeMap` of the unbounded derived categories
`D(-_étale, Λ)` is the mate, under the derived adjunctions, of the composite of the
pullback-composition isomorphisms of [Stacks, Tag 0D6D]. On bounded below objects there is a
second base change map, `Stacks.EtaleCohomology.EtaleCoefficients.derivedBaseChangePlus`, the
descent to `D⁺` of the underived base change map. This file proves that **they are invertible
together** (`isIso_baseChangeMap_app_iff_isIso_derivedBaseChangePlus_app`), and therefore that for
`ℤ/mℤ`-coefficients **`baseChangeMap` is invertible at a bounded below object exactly when the
abelian base change map `Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` is invertible at
its underlying complex of abelian sheaves** (`isIso_baseChangeMap_app_iff`).

## The proof

Both maps are computed on a bounded below complex `I` of injectives. The unbounded map, preceded
by `(f')⁻¹` of the unit `g_*I ⟶ Rg_*I` and followed by `Rh_*` of the comparison `e⁻¹I ⟶ e⁻¹I`
of the derived with the degreewise inverse image, is the degreewise base change map followed by
the unit of `Rh_*` (`baseChangeMap_fac`); this is checked on adjuncts under `h⁻¹ ⊣ Rh_*`, from
the counit factorizations of [Stacks, Tag 0FPI], the characterization of the composite of
`pullbackCompIso` by the underived composition isomorphisms, and the mate description of the
underived base change map. The descended map has the same description with the bounded below
derived functors (`Stacks.Cohomology.BaseChange.derived_fac_app`), and the two are compared by
the identification of `Rh_*` on `D⁺` with its bounded below right derived functor.

## Main results

* `Stacks.Cohomology.BaseChange.mateEquiv_app_fac` — the computation of a derived mate on a
  complex, for variables.
* `baseChangeMap_fac` — the unbounded base change map on a complex.
* `isIso_baseChangeMap_app_iff_isIso_derivedBaseChangePlus_app` — the two base change maps are
  invertible together on `D⁺`.
* `isIso_baseChangeMap_app_iff` — **for `ℤ/mℤ`-coefficients, `baseChangeMap` is invertible at a
  bounded below object exactly when `smallEtaleDerivedBaseChangeAb` is invertible at its
  underlying complex of abelian sheaves.**

## Implementation notes

`baseChangeMap` and `pullback` of `D(-_étale, Λ)` are built on the standard model of the derived
category (`AdjunctionForRingedTopoi.lean:394` in
`StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/`), and so are
`Stacks.Cohomology.BaseChange.derived` and
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb`; that fixes the model here.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.BaseChange

section Chase

variable {𝒞 : Type*} [Category* 𝒞]

/-- The rearrangement behind `mateEquiv_app_fac_of_three`, for morphisms of an arbitrary
category: a composite `a₁ ≫ a₂ ≫ e₁'` of three comparisons, each read
through comparison maps `c` as in `hA`, `hB`, `hE`, is read through them by the composite of the
three readings. -/
theorem threeComparison_chase {P₀ P₁ P₂ P₃ Q₀ Q₁ R₀ R₁ R₂ R₃ : 𝒞}
    (a₁ : P₀ ⟶ P₁) (a₂ : P₁ ⟶ P₂) (e₁ : P₃ ⟶ P₂) (e₁' : P₂ ⟶ P₃) (c₁ : P₁ ⟶ R₀) (c₂ : P₂ ⟶ R₁)
    (x₁ : P₀ ⟶ Q₀) (y₁ : Q₀ ⟶ R₂) (m₁ : R₂ ⟶ R₀) (m₂ : R₀ ⟶ R₁) (x₂ : P₃ ⟶ Q₁) (y₂ : Q₁ ⟶ R₃)
    (m₃ : R₃ ⟶ R₁) (m₃' : R₁ ⟶ R₃) (m : R₂ ⟶ R₃)
    (hA : a₁ ≫ c₁ = x₁ ≫ y₁ ≫ m₁) (hB : a₂ ≫ c₂ = c₁ ≫ m₂) (hE : e₁ ≫ c₂ = x₂ ≫ y₂ ≫ m₃)
    (he : e₁' ≫ e₁ = 𝟙 P₂) (hm : m₃ ≫ m₃' = 𝟙 R₃) (hM : m₁ ≫ m₂ ≫ m₃' = m) :
    (a₁ ≫ a₂ ≫ e₁') ≫ x₂ ≫ y₂ = x₁ ≫ y₁ ≫ m := by
  have hE' : x₂ ≫ y₂ = e₁ ≫ c₂ ≫ m₃' := by
    rw [reassoc_of% hE, hm, Category.comp_id]
  rw [hE', Category.assoc, Category.assoc, reassoc_of% he, reassoc_of% hB, reassoc_of% hA, hM]

end Chase

section MateFac

variable {KS KT KX KY DS DT DX DY : Type*} [Category* KS] [Category* KT] [Category* KX]
  [Category* KY] [Category* DS] [Category* DT] [Category* DX] [Category* DY]
  {QS : KS ⥤ DS} {QT : KT ⥤ DT} {QX : KX ⥤ DX} {QY : KY ⥤ DY}
  {gK : KS ⥤ KT} {gKp : KT ⥤ KS} (aG : gK ⊣ gKp) {hK : KX ⥤ KY} {hKp : KY ⥤ KX} (aH : hK ⊣ hKp)
  {fK : KS ⥤ KX} {eK : KT ⥤ KY}
  {gD : DS ⥤ DT} {gDp : DT ⥤ DS} (AG : gD ⊣ gDp) {hD : DX ⥤ DY} {hDp : DY ⥤ DX} (AH : hD ⊣ hDp)
  {fD : DS ⥤ DX} {eD : DT ⥤ DY}
  {cg : QS ⋙ gD ⟶ gK ⋙ QT} {ch : QX ⋙ hD ⟶ hK ⋙ QY} {cf : QS ⋙ fD ⟶ fK ⋙ QX}
  {ce : QT ⋙ eD ⟶ eK ⋙ QY} {ug : gKp ⋙ QS ⟶ QT ⋙ gDp} {uh : hKp ⋙ QX ⟶ QY ⋙ hDp}
  (β : fD ⋙ hD ≅ gD ⋙ eD)

/-- **A derived mate computed on an object of the homotopy category.** Let `β` compare the two
composite derived inverse images of a square, and let it be read at the images `Q K` through
the comparisons `c` of the derived inverse images with the underived ones by morphisms
`b K`. Let `τ K` be morphisms of the underived composites satisfying the defining property of the
underived mate of `b`. If the derived counits are induced by the underived ones through the
units `u` of the derived direct images ([Stacks, Tag 0FPI]), then the mate of `β`, preceded by
`f⁻¹` of the unit of `g_*` and followed by `h_*` of the comparison of `e⁻¹`, is the comparison of
`f⁻¹`, followed by `τ K` and the unit of `h_*`. -/
theorem mateEquiv_app_fac
    (hFPIg : ∀ K, gD.map (ug.app K) ≫ AG.counit.app (QT.obj K) =
      cg.app (gKp.obj K) ≫ QT.map (aG.counit.app K))
    (hFPIh : ∀ K, hD.map (uh.app K) ≫ AH.counit.app (QY.obj K) =
      ch.app (hKp.obj K) ≫ QY.map (aH.counit.app K))
    (b : ∀ K, hK.obj (fK.obj K) ⟶ eK.obj (gK.obj K))
    (hβ : ∀ K, β.hom.app (QS.obj K) ≫ eD.map (cg.app K) ≫ ce.app (gK.obj K) =
      hD.map (cf.app K) ≫ ch.app (fK.obj K) ≫ QY.map (b K))
    (τ : ∀ K, fK.obj (gKp.obj K) ⟶ hKp.obj (eK.obj K))
    (hτ : ∀ K, hK.map (τ K) ≫ aH.counit.app (eK.obj K) =
      b (gKp.obj K) ≫ eK.map (aG.counit.app K))
    (K : KT) :
    fD.map (ug.app K) ≫ (AbstractKunnethMap.baseChangeMap AG AH fD eD β).app (QT.obj K) ≫
        hDp.map (ce.app K) =
      cf.app (gKp.obj K) ≫ QX.map (τ K) ≫ uh.app (eK.obj K) := by
  apply (AH.homEquiv _ _).symm.injective
  rw [Adjunction.homEquiv_counit, Adjunction.homEquiv_counit]
  have hc := AH.counit.naturality (ce.app K)
  have hm := AbstractKunnethMap.baseChangeMap_counit AG AH fD eD β (QT.obj K)
  have hn := β.hom.naturality (ug.app K)
  have hce := ce.naturality (aG.counit.app K)
  have hch := ch.naturality (τ K)
  simp only [Functor.comp_map, Functor.id_map, Functor.comp_obj, Functor.id_obj] at hc hn hce hch
  simp only [Functor.map_comp, Category.assoc, Functor.comp_obj]
  rw [hc, reassoc_of% hm, reassoc_of% hn, ← Functor.map_comp_assoc, hFPIg K, Functor.map_comp,
    Category.assoc, hce, reassoc_of% (hβ (gKp.obj K)), hFPIh, reassoc_of% hch,
    ← QY.map_comp (hK.map (τ K)), hτ, QY.map_comp]

variable {P P' : DS ⥤ DY} {PK PK' : KS ⥤ KY} {cP : QS ⋙ P ⟶ PK ⋙ QY}
  {cP' : QS ⋙ P' ⟶ PK' ⋙ QY}

variable (QT QX) in
/-- **A transformation `bc : g_* ⋙ f⁻¹ ⟶ e⁻¹ ⋙ h_*` computed at an object `K` of the homotopy
category**: preceded by `f⁻¹` of the unit `u_g` and followed by `h_*` of the comparison `c_e`, it
is the comparison `c_f`, followed by `τ K` and the unit `u_h`. -/
def UnitFac (bc : gDp ⋙ fD ⟶ eD ⋙ hDp) (ug : gKp ⋙ QS ⟶ QT ⋙ gDp) (uh : hKp ⋙ QX ⟶ QY ⋙ hDp)
    (cf : QS ⋙ fD ⟶ fK ⋙ QX) (ce : QT ⋙ eD ⟶ eK ⋙ QY)
    (τ : ∀ K, fK.obj (gKp.obj K) ⟶ hKp.obj (eK.obj K)) (K : KT) : Prop :=
  fD.map (ug.app K) ≫ bc.app (QT.obj K) ≫ hDp.map (ce.app K) =
    cf.app (gKp.obj K) ≫ QX.map (τ K) ≫ uh.app (eK.obj K)

variable (QS QY) in
/-- **A comparison `β : P ≅ P'` of two functors read through comparisons `c`, `c'` with functors
on the homotopy category by morphisms `b K`.** A named proposition, so that a hypothesis of this
shape is compared argument by argument. -/
def ReadThrough (β : P ≅ P') (c : QS ⋙ P ⟶ PK ⋙ QY) (c' : QS ⋙ P' ⟶ PK' ⋙ QY)
    (b : ∀ K, PK.obj K ⟶ PK'.obj K) : Prop :=
  ∀ K, β.hom.app (QS.obj K) ≫ c'.app K = c.app K ≫ QY.map (b K)

/-- **Morphisms `τ K` satisfy the defining property of the underived mate of the composite
`b₁ ≫ b₂ ≫ b₃'`**, through the counits of `aG` and `aH`. A named proposition, so that a hypothesis
of this shape is compared argument by argument. -/
def CounitCompat (b₁ : ∀ K, hK.obj (fK.obj K) ⟶ PK.obj K) (b₂ : ∀ K, PK.obj K ⟶ PK'.obj K)
    (b₃' : ∀ K, PK'.obj K ⟶ eK.obj (gK.obj K)) (τ : ∀ K, fK.obj (gKp.obj K) ⟶ hKp.obj (eK.obj K)) :
    Prop :=
  ∀ K, hK.map (τ K) ≫ aH.counit.app (eK.obj K) =
    (b₁ (gKp.obj K) ≫ b₂ (gKp.obj K) ≫ b₃' (gKp.obj K)) ≫ eK.map (aG.counit.app K)

/-- `mateEquiv_app_fac` for a comparison `β₁ ≫ β₂ ≫ β₃⁻¹` of the composite derived inverse images
through two intermediate functors `P`, `P'`, each piece read on objects of the homotopy category
through the comparisons `c`. -/
theorem mateEquiv_app_fac_of_three
    (hFPIg : ∀ K, gD.map (ug.app K) ≫ AG.counit.app (QT.obj K) =
      cg.app (gKp.obj K) ≫ QT.map (aG.counit.app K))
    (hFPIh : ∀ K, hD.map (uh.app K) ≫ AH.counit.app (QY.obj K) =
      ch.app (hKp.obj K) ≫ QY.map (aH.counit.app K))
    (β₁ : fD ⋙ hD ≅ P) (β₂ : P ≅ P') (β₃ : gD ⋙ eD ≅ P')
    (b₁ : ∀ K, hK.obj (fK.obj K) ⟶ PK.obj K) (b₂ : ∀ K, PK.obj K ⟶ PK'.obj K)
    (b₃ : ∀ K, eK.obj (gK.obj K) ⟶ PK'.obj K) (b₃' : ∀ K, PK'.obj K ⟶ eK.obj (gK.obj K))
    (hA : ∀ K, β₁.hom.app (QS.obj K) ≫ cP.app K = hD.map (cf.app K) ≫ ch.app (fK.obj K) ≫
      QY.map (b₁ K))
    (hB : ReadThrough QS QY β₂ cP cP' b₂)
    (hE : ∀ K, β₃.hom.app (QS.obj K) ≫ cP'.app K = eD.map (cg.app K) ≫ ce.app (gK.obj K) ≫
      QY.map (b₃ K))
    (hb : ∀ K, b₃ K ≫ b₃' K = 𝟙 _)
    (τ : ∀ K, fK.obj (gKp.obj K) ⟶ hKp.obj (eK.obj K))
    (hτ : CounitCompat aG aH b₁ b₂ b₃' τ)
    (K : KT) :
    UnitFac QT QX (AbstractKunnethMap.baseChangeMap AG AH fD eD (β₁ ≪≫ β₂ ≪≫ β₃.symm)) ug uh cf ce
      τ K := by
  refine mateEquiv_app_fac aG aH AG AH (β₁ ≪≫ β₂ ≪≫ β₃.symm) hFPIg hFPIh
    (fun K => b₁ K ≫ b₂ K ≫ b₃' K) (fun K => ?_) τ hτ K
  have hm : QY.map (b₃ K) ≫ QY.map (b₃' K) = 𝟙 _ := by
    rw [← QY.map_comp, hb, QY.map_id]
  simpa using threeComparison_chase _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (QY.map (b₁ K ≫ b₂ K ≫ b₃' K)) (hA K) (hB K) (hE K) (β₃.inv_hom_id_app (QS.obj K)) hm
    (by simp)

/-- **A transformation computed at `K` through invertible units and comparisons is invertible at
`Q K` exactly when the degreewise transformation followed by the unit of `h_*` is.** -/
theorem isIso_app_iff_of_unitFac {bc : gDp ⋙ fD ⟶ eD ⋙ hDp} {τ : ∀ K, fK.obj (gKp.obj K) ⟶
      hKp.obj (eK.obj K)} {K : KT} (h : UnitFac QT QX bc ug uh cf ce τ K) [IsIso (ug.app K)]
    [IsIso (cf.app (gKp.obj K))] [IsIso (ce.app K)] :
    IsIso (bc.app (QT.obj K)) ↔ IsIso (QX.map (τ K) ≫ uh.app (eK.obj K)) := by
  unfold UnitFac at h
  rw [← isIso_comp_left_iff (fD.map (ug.app K)), ← isIso_comp_right_iff _ (hDp.map (ce.app K)),
    Category.assoc, h, isIso_comp_left_iff]

section HomotopyCounit

variable {S T X Y : Type*} [Category* S] [Category* T] [Category* X] [Category* Y]
  [Preadditive S] [Preadditive T] [Preadditive X] [Preadditive Y]
  {gL : S ⥤ T} {gR : T ⥤ S} (adjG : gL ⊣ gR) {hL : X ⥤ Y} {hR : Y ⥤ X} (adjH : hL ⊣ hR)
  {fL : S ⥤ X} {eL : T ⥤ Y} {PL PL' : S ⥤ Y}
  [gL.Additive] [gR.Additive] [hL.Additive] [hR.Additive] [fL.Additive] [eL.Additive]
  [PL.Additive] [PL'.Additive]
  (α₁ : fL ⋙ hL ≅ PL) (α₂ : PL ≅ PL') (α₃ : gL ⋙ eL ≅ PL') (τ : gR ⋙ fL ⟶ eL ⋙ hR)

/-- **`CounitCompat` for transformations applied degreewise on homotopy categories**, from the
defining property of `τ` as the underived mate of `α₁ ≫ α₂ ≫ α₃⁻¹`. -/
theorem counitCompat_mapHomotopyCategory
    (β : fL ⋙ hL ≅ gL ⋙ eL) (hβ : β = α₁ ≪≫ α₂ ≪≫ α₃.symm)
    (hτ : ∀ M, hL.map (τ.app M) ≫ adjH.counit.app (eL.obj M) =
      β.hom.app (gR.obj M) ≫ eL.map (adjG.counit.app M)) :
    CounitCompat (Adjunction.mapHomotopyCategoryAdjunction adjG (ComplexShape.up ℤ))
      (Adjunction.mapHomotopyCategoryAdjunction adjH (ComplexShape.up ℤ))
      (fK := fL.mapHomotopyCategory (ComplexShape.up ℤ))
      (eK := eL.mapHomotopyCategory (ComplexShape.up ℤ))
      (PK := PL.mapHomotopyCategory (ComplexShape.up ℤ))
      (PK' := PL'.mapHomotopyCategory (ComplexShape.up ℤ))
      (fun K => (NatTrans.mapHomotopyCategory α₁.hom (ComplexShape.up ℤ)).app K)
      (fun K => (NatTrans.mapHomotopyCategory α₂.hom (ComplexShape.up ℤ)).app K)
      (fun K => (NatTrans.mapHomotopyCategory α₃.inv (ComplexShape.up ℤ)).app K)
      (fun K => (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K) := by
  subst hβ
  intro K
  obtain ⟨I, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  have hc : (hL.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex τ (ComplexShape.up ℤ)).app I) ≫
      (Adjunction.mapHomologicalComplexAdjunction adjH (ComplexShape.up ℤ)).counit.app
        ((eL.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) =
      ((NatTrans.mapHomologicalComplex α₁.hom (ComplexShape.up ℤ)).app
          ((gR.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        (NatTrans.mapHomologicalComplex α₂.hom (ComplexShape.up ℤ)).app
          ((gR.mapHomologicalComplex (ComplexShape.up ℤ)).obj I) ≫
        (NatTrans.mapHomologicalComplex α₃.inv (ComplexShape.up ℤ)).app
          ((gR.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
      (eL.mapHomologicalComplex (ComplexShape.up ℤ)).map
        ((Adjunction.mapHomologicalComplexAdjunction adjG (ComplexShape.up ℤ)).counit.app I) := by
    ext n : 1
    exact (hτ (I.X n)).trans (by simp only [Iso.trans_hom, Iso.symm_hom, NatTrans.comp_app]; rfl)
  have := congrArg (HomotopyCategory.quotient Y (ComplexShape.up ℤ)).map hc
  simp only [Functor.map_comp] at this
  exact this

end HomotopyCounit

end MateFac

section DerivedIsIso

-- `Stacks.Cohomology.BaseChange.derived` (`StacksFrontier/Topology/Sheaves/Cohomology/
-- StacksFrontier/Topology/Sheaves/Cohomology/HigherDirectImage/AbelianBaseChangeMap.lean:204`) is
-- built under the standard model.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

variable {A B C D : Type*} [Category* A] [Category* B] [Category* C] [Category* D]
  [Abelian A] [Abelian B] [Abelian C] [Abelian D]
  [EnoughInjectives A] [EnoughInjectives B] [EnoughInjectives C]
  (F : A ⥤ B) (F' : C ⥤ D) (G : B ⥤ D) (G' : A ⥤ C)
  [F.Additive] [F'.Additive] [G.Additive] [G'.Additive]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

variable {RF' : DerivedCategory C ⥤ DerivedCategory D}
  (α : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
    DerivedCategory.Qh ⋙ RF')
  [RF'.IsRightDerivedFunctor α (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]

/-- **The unit of the bounded below right derived functor against that of the unbounded one**: a
morphism followed by the unit of `RF'⁺` is invertible exactly when, in `D(D)`, it is followed by
the unit of `RF'`. -/
theorem isIso_comp_rightDerivedFunctorPlusUnit_iff
    (hres : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    {P : HomotopyCategory.Plus D} (M : HomotopyCategory.Plus C)
    (x : P ⟶ F'.mapHomotopyCategoryPlus.obj M) :
    IsIso (DerivedCategory.Plus.Qh.map x ≫ F'.rightDerivedFunctorPlusUnith.app M) ↔
      IsIso (DerivedCategory.Qh.map x.hom ≫
        α.app ((HomotopyCategory.Plus.ι C).obj M)) := by
  have e : DerivedCategory.Plus.ι.map
      (DerivedCategory.Plus.Qh.map x ≫ F'.rightDerivedFunctorPlusUnith.app M) ≫
        (Functor.boundedDerivedIso F' RF' α hres).hom.app (DerivedCategory.Plus.Qh.obj M) =
      DerivedCategory.Qh.map x.hom ≫ α.app ((HomotopyCategory.Plus.ι C).obj M) := by
    rw [Functor.map_comp, Category.assoc, Functor.boundedDerivedIso_hom_app F' RF' α hres M]
    rfl
  refine (isIso_iff_of_reflects_iso _ DerivedCategory.Plus.ι).symm.trans
    ((isIso_comp_right_iff _ ((Functor.boundedDerivedIso F' RF' α hres).hom.app
      (DerivedCategory.Plus.Qh.obj M))).symm.trans ?_)
  exact Iff.of_eq (congrArg IsIso e)

/-- **A transformation of unbounded derived functors and the descent of its degreewise version are
invertible together on `D⁺`.** Let `bc : Rg_* ⋙ f⁻¹ ⟶ e⁻¹ ⋙ Rh_*` be computed at every object of
the homotopy category, through the units `u` of `Rg_*` and `Rh_*` and comparisons `c` of `f⁻¹` and
`e⁻¹` with degreewise functors, by a degreewise transformation `τ`; let the comparisons be
invertible, the unit of `Rg_*` invertible on bounded below complexes of injectives, and `Rh_*` a
right derived functor computed by K-injective resolutions. Then at a bounded below object `K`, `bc`
is invertible exactly when the descent `Stacks.Cohomology.BaseChange.derived` of `τ` is. -/
theorem isIso_app_ι_iff_isIso_derived_app
    {gDp : DerivedCategory A ⥤ DerivedCategory B} {fD : DerivedCategory B ⥤ DerivedCategory D}
    {eD : DerivedCategory A ⥤ DerivedCategory C} {hDp : DerivedCategory C ⥤ DerivedCategory D}
    (bc : gDp ⋙ fD ⟶ eD ⋙ hDp)
    (ug : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ gDp)
    (uh : F'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
      DerivedCategory.Qh ⋙ hDp)
    [hDp.IsRightDerivedFunctor uh (HomotopyCategory.quasiIso C (ComplexShape.up ℤ))]
    (cf : DerivedCategory.Qh ⋙ fD ⟶ G.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (ce : DerivedCategory.Qh ⋙ eD ⟶
      G'.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    (τ : F ⋙ G ⟶ G' ⋙ F')
    (hfac : ∀ K, UnitFac DerivedCategory.Qh DerivedCategory.Qh bc ug uh cf ce
      (fun K => (NatTrans.mapHomotopyCategory τ (ComplexShape.up ℤ)).app K) K)
    (hug : ∀ L : CochainComplex.Plus (InjectiveObject A), IsIso (ug.app
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj
        (((InjectiveObject.ι A).mapHomologicalComplex (ComplexShape.up ℤ)).obj L.obj))))
    (hcf : ∀ K, IsIso (cf.app K)) (hce : ∀ K, IsIso (ce.app K))
    (hres : ∀ K : CochainComplex C ℤ, ∃ (I : CochainComplex C ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f)
    [PreservesFiniteLimits G'] [PreservesFiniteColimits G']
    (K : DerivedCategory.Plus A) :
    IsIso (bc.app (DerivedCategory.Plus.ι.obj K)) ↔
      IsIso ((derived F F' G G' τ (asIso G.rightDerivedFunctorPlusUnith)).app K) := by
  obtain ⟨n, hn⟩ := K.property
  have : K.IsGE n := (DerivedCategory.Plus.isGE_ι_obj_iff K n).1 hn
  obtain ⟨L, _, ⟨i⟩⟩ := DerivedCategory.Plus.exists_injective_nonempty_iso K n
  let Kh := (HomotopyCategory.Plus.quotient A).obj
    ((InjectiveObject.ι A).mapCochainComplexPlus.obj L)
  let j : DerivedCategory.Plus.Qh.obj Kh ≅ K :=
    (ObjectProperty.isoMk _ ((DerivedCategory.quotientCompQhIso A).app
        ((InjectiveObject.ι A).mapCochainComplexPlus.obj L).obj) :
      DerivedCategory.Plus.Qh.obj Kh ≅
        DerivedCategory.Plus.Q.obj ((InjectiveObject.ι A).mapCochainComplexPlus.obj L)) ≪≫ i
  let j' : DerivedCategory.Plus.ι.obj K ≅
      DerivedCategory.Qh.obj ((HomotopyCategory.Plus.ι A).obj Kh) :=
    (DerivedCategory.Plus.ι.mapIso j).symm
  have : IsIso (ug.app ((HomotopyCategory.Plus.ι A).obj Kh)) := hug L
  have := hcf
    ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj ((HomotopyCategory.Plus.ι A).obj Kh))
  have := hce ((HomotopyCategory.Plus.ι A).obj Kh)
  have hu := isIso_app_iff_of_unitFac (hfac ((HomotopyCategory.Plus.ι A).obj Kh))
  have hd := isIso_derived_app_Qh_iff F F' G G' τ (asIso G.rightDerivedFunctorPlusUnith) Kh
    inferInstance inferInstance
  have hl := isIso_comp_rightDerivedFunctorPlusUnit_iff F' uh hres
    (G'.mapHomotopyCategoryPlus.obj Kh) ((mapPlus τ).app Kh)
  exact (NatTrans.isIso_app_iff_of_iso bc j').trans
    (hu.trans (hl.symm.trans (hd.symm.trans (NatTrans.isIso_app_iff_of_iso _ j))))

end DerivedIsIso

end Stacks.Cohomology.BaseChange

open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology.ProjectionFormulaConstant (etaleRing)

universe u

namespace Stacks.EtaleCohomology.EtaleCoefficients

/-- An isomorphism of additive functors, applied degreewise on the homotopy category: its
inverse undoes it. -/
theorem mapHomotopyCategory_hom_app_comp_inv_app {C D : Type*} [Category* C] [Category* D]
    [Preadditive C] [Preadditive D] {F G : C ⥤ D} [F.Additive] [G.Additive] (α : F ≅ G)
    (K : HomotopyCategory C (ComplexShape.up ℤ)) :
    (NatTrans.mapHomotopyCategory α.hom (ComplexShape.up ℤ)).app K ≫
        (NatTrans.mapHomotopyCategory α.inv (ComplexShape.up ℤ)).app K =
      𝟙 ((F.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) := by
  rw [← NatTrans.comp_app, ← NatTrans.mapHomotopyCategory_comp, Iso.hom_inv_id,
    NatTrans.mapHomotopyCategory_id, NatTrans.id_app]

/-! ### The composite inverse images of sheaves of modules -/

section Conjugate

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The inverse image along a composite is the composite of the inverse images**, on sheaves of
`Λ̲`-modules on the small models: Stacks 0D6D for the composite morphism of ringed topoi, followed
by its comparison with the morphism of ringed topoi of `p ≫ f`. It is the left adjoint companion
of `pushforwardCompIso` (`conjugateEquiv_pullbackCompModulesIso_hom`). -/
def pullbackCompModulesIso {W X S : Scheme.{u}} (p : W ⟶ X) (f : X ⟶ S) :
    (ringedToposHom Λ f).pullbackTopos ⋙ (ringedToposHom Λ p).pullbackTopos ≅
      (ringedToposHom Λ (p ≫ f)).pullbackTopos :=
  RingedToposSiteHom.pullbackToposCompIso (ringedToposHom Λ p) (ringedToposHom Λ f) ≪≫
    RingedToposSiteHom.pullbackToposIsoOfIso (fSharpCompatible_comp Λ p f)

/-- `pullbackCompModulesIso` is the conjugate of `pushforwardCompIso`. -/
theorem conjugateEquiv_pullbackCompModulesIso_hom {W X S : Scheme.{u}} (p : W ⟶ X)
    (f : X ⟶ S) :
    conjugateEquiv (ringedToposHom Λ (p ≫ f)).pullbackPushforwardAdjunctionTopos
        ((ringedToposHom Λ f).pullbackPushforwardAdjunctionTopos.comp
          (ringedToposHom Λ p).pullbackPushforwardAdjunctionTopos)
        (pullbackCompModulesIso Λ p f).hom = (pushforwardCompIso Λ p f).hom := by
  have h₁ : conjugateEquiv (ringedToposHom Λ (p ≫ f)).pullbackPushforwardAdjunctionTopos
      ((ringedToposHom Λ f).comp (ringedToposHom Λ p)).pullbackPushforwardAdjunctionTopos
      (RingedToposSiteHom.pullbackToposIsoOfIso (fSharpCompatible_comp Λ p f)).hom =
        (RingedToposSiteHom.pushforwardToposIsoOfIso (fSharpCompatible_comp Λ p f)).inv :=
    Stacks.CategoryTheory.conjugateEquiv_leftAdjointUniq_ofNatIsoRight_hom _ _ _
  have h₂ : conjugateEquiv
      ((ringedToposHom Λ f).comp (ringedToposHom Λ p)).pullbackPushforwardAdjunctionTopos
      ((ringedToposHom Λ f).pullbackPushforwardAdjunctionTopos.comp
        (ringedToposHom Λ p).pullbackPushforwardAdjunctionTopos)
      (RingedToposSiteHom.pullbackToposCompIso (ringedToposHom Λ p) (ringedToposHom Λ f)).hom =
        (RingedToposSiteHom.pushforwardToposCompIso (ringedToposHom Λ p)
          (ringedToposHom Λ f)).hom :=
    Equiv.apply_symm_apply _ _
  rw [pullbackCompModulesIso, Iso.trans_hom, ← conjugateEquiv_comp
    (adj₂ := ((ringedToposHom Λ f).comp (ringedToposHom Λ p)).pullbackPushforwardAdjunctionTopos),
    h₁, h₂]
  rfl

/-- `pullbackCompModulesIso` inverted is the conjugate of `pushforwardCompIso` inverted. -/
theorem conjugateEquiv_pullbackCompModulesIso_inv {W X S : Scheme.{u}} (p : W ⟶ X)
    (f : X ⟶ S) :
    conjugateEquiv ((ringedToposHom Λ f).pullbackPushforwardAdjunctionTopos.comp
          (ringedToposHom Λ p).pullbackPushforwardAdjunctionTopos)
        (ringedToposHom Λ (p ≫ f)).pullbackPushforwardAdjunctionTopos
        (pullbackCompModulesIso Λ p f).inv = (pushforwardCompIso Λ p f).inv := by
  have h := conjugateEquiv_comp
    (adj₁ := (ringedToposHom Λ f).pullbackPushforwardAdjunctionTopos.comp
      (ringedToposHom Λ p).pullbackPushforwardAdjunctionTopos)
    (adj₂ := (ringedToposHom Λ (p ≫ f)).pullbackPushforwardAdjunctionTopos)
    (adj₃ := (ringedToposHom Λ f).pullbackPushforwardAdjunctionTopos.comp
      (ringedToposHom Λ p).pullbackPushforwardAdjunctionTopos)
    (pullbackCompModulesIso Λ p f).inv (pullbackCompModulesIso Λ p f).hom
  rw [Iso.hom_inv_id, conjugateEquiv_id, conjugateEquiv_pullbackCompModulesIso_hom] at h
  exact (Iso.comp_hom_eq_id (pushforwardCompIso Λ p f)).1 h

/-- The direct images of sheaves of `Λ̲`-modules along equal morphisms are isomorphic. -/
def pushforwardCongrIso {Y S : Scheme.{u}} {a b : Y ⟶ S} (hab : a = b) :
    (ringedToposHom Λ a).pushforwardTopos ≅ (ringedToposHom Λ b).pushforwardTopos :=
  eqToIso (congrArg (fun k => (ringedToposHom Λ k).pushforwardTopos) hab)

/-- The inverse images of sheaves of `Λ̲`-modules along equal morphisms are isomorphic. -/
def pullbackCongrModulesIso {Y S : Scheme.{u}} {a b : Y ⟶ S} (hab : a = b) :
    (ringedToposHom Λ a).pullbackTopos ≅ (ringedToposHom Λ b).pullbackTopos :=
  eqToIso (congrArg (fun k => (ringedToposHom Λ k).pullbackTopos) hab)

/-- `pullbackCongrModulesIso` is the conjugate of `pushforwardCongrIso`. -/
theorem conjugateEquiv_pullbackCongrModulesIso_hom {Y S : Scheme.{u}} {a b : Y ⟶ S}
    (hab : a = b) :
    conjugateEquiv (ringedToposHom Λ b).pullbackPushforwardAdjunctionTopos
        (ringedToposHom Λ a).pullbackPushforwardAdjunctionTopos
        (pullbackCongrModulesIso Λ hab).hom = (pushforwardCongrIso Λ hab.symm).hom := by
  subst hab
  simp [pullbackCongrModulesIso, pushforwardCongrIso, conjugateEquiv_id]

/-- `pushforwardCompIsoOfEq` is `pushforwardCompIso` followed by the identification of the direct
images along equal morphisms. -/
theorem pushforwardCompIsoOfEq_inv {W X S : Scheme.{u}} (p : W ⟶ X) (f : X ⟶ S) (c : W ⟶ S)
    (hc : p ≫ f = c) :
    (pushforwardCompIsoOfEq Λ p f c hc).inv =
      (pushforwardCompIso Λ p f).inv ≫ (pushforwardCongrIso Λ hc).hom := by
  subst hc
  simp [pushforwardCompIsoOfEq_rfl, pushforwardCongrIso]

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **The identification `(f')⁻¹ ⋙ h⁻¹ ≅ g⁻¹ ⋙ e⁻¹` of the two composite inverse images of a
commutative square**, on sheaves of `Λ̲`-modules: both are the inverse image along
`h ≫ f' = e ≫ g`. -/
def pullbackSquareModulesIso :
    (ringedToposHom Λ f').pullbackTopos ⋙ (ringedToposHom Λ h).pullbackTopos ≅
      (ringedToposHom Λ g).pullbackTopos ⋙ (ringedToposHom Λ e).pullbackTopos :=
  pullbackCompModulesIso Λ h f' ≪≫ pullbackCongrModulesIso Λ w ≪≫
    (pullbackCompModulesIso Λ e g).symm

/-- **`pullbackSquareModulesIso` is the conjugate of `pushforwardSquareIso`.** -/
theorem conjugateEquiv_pullbackSquareModulesIso_hom :
    conjugateEquiv ((ringedToposHom Λ g).pullbackPushforwardAdjunctionTopos.comp
          (ringedToposHom Λ e).pullbackPushforwardAdjunctionTopos)
        ((ringedToposHom Λ f').pullbackPushforwardAdjunctionTopos.comp
          (ringedToposHom Λ h).pullbackPushforwardAdjunctionTopos)
        (pullbackSquareModulesIso Λ f' g h e w).hom = (pushforwardSquareIso Λ f' g h e w).hom := by
  rw [pullbackSquareModulesIso, Iso.trans_hom, Iso.trans_hom, Iso.symm_hom,
    ← conjugateEquiv_comp (adj₂ := (ringedToposHom Λ (h ≫ f')).pullbackPushforwardAdjunctionTopos),
    ← conjugateEquiv_comp (adj₂ := (ringedToposHom Λ (e ≫ g)).pullbackPushforwardAdjunctionTopos),
    conjugateEquiv_pullbackCompModulesIso_inv, conjugateEquiv_pullbackCongrModulesIso_hom,
    conjugateEquiv_pullbackCompModulesIso_hom, Iso.trans_hom, Iso.symm_hom,
    pushforwardCompIsoOfEq_inv, Category.assoc]

end Conjugate

/-! ### The underived base change map as a mate of the inverse images -/

section ModuleCounit

variable (Λ : Type (u + 1)) [CommRing Λ] {X' Y S T : Scheme.{u}}
  (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T) (w : h ≫ f' = e ≫ g)

/-- **The defining property of `moduleBaseChange` through the inverse images**: `h⁻¹` of it,
followed by the counit of `h⁻¹ ⊣ h_*`, is `pullbackSquareModulesIso` followed by `e⁻¹` of the
counit of `g⁻¹ ⊣ g_*`. -/
theorem moduleBaseChange_counit
    (M : SheafOfModules.{u + 1} (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ T).O)) :
    (ringedToposHom Λ h).pullbackTopos.map ((moduleBaseChange Λ f' g h e w).app M) ≫
        (ringedToposHom Λ h).pullbackPushforwardAdjunctionTopos.counit.app
          ((ringedToposHom Λ e).pullbackTopos.obj M) =
      (pullbackSquareModulesIso Λ f' g h e w).hom.app
          ((ringedToposHom Λ g).pushforwardTopos.obj M) ≫
        (ringedToposHom Λ e).pullbackTopos.map
          ((ringedToposHom Λ g).pullbackPushforwardAdjunctionTopos.counit.app M) := by
  have h₁ := Stacks.Cohomology.BaseChange.homEquiv_symm_mate_app
    (ringedToposHom Λ f').pullbackPushforwardAdjunctionTopos
    (ringedToposHom Λ e).pullbackPushforwardAdjunctionTopos (pushforwardSquareIso Λ f' g h e w)
    (ringedToposHom Λ g).pullbackPushforwardAdjunctionTopos
    (ringedToposHom Λ h).pullbackPushforwardAdjunctionTopos
    (pullbackSquareModulesIso Λ f' g h e w).hom
    (conjugateEquiv_pullbackSquareModulesIso_hom Λ f' g h e w) M
  rwa [Adjunction.homEquiv_counit] at h₁

end ModuleCounit

/-! ### The composite derived inverse images on complexes -/

section DerivedPullback

-- `pullback` of `D(-_étale, Λ)`
-- (`AdjunctionForRingedTopoi.lean:394` in
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/`)
-- is built under the standard model of the derived category.
attribute [local instance] HasDerivedCategory.standard

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction
open Stacks.Cohomology.DerivedPullbackCompositionOnTopoi
open Stacks.SheafOfModules.Tensor (ringSheaf)

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **`pullbackCompIso` on a complex**: followed by the comparison of the derived with the
degreewise inverse image along `p ≫ f`, it is the comparisons along `f` and `p` followed by
`pullbackCompModulesIso` applied degreewise. -/
theorem pullbackCompIso_hom_app_comp_comparison {W X S : Scheme.{u}} (p : W ⟶ X) (f : X ⟶ S)
    (I : CochainComplex (SheafOfModules.{u + 1}
      (ringSheaf (ringedTopos Λ S).O)) ℤ) :
    (pullbackCompIso Λ p f).hom.app
        (DerivedCategory.Qh.obj ((HomotopyCategory.quotient (SheafOfModules.{u + 1}
          (ringSheaf (ringedTopos Λ S).O)) (ComplexShape.up ℤ)).obj I)) ≫
      (derivedPullbackComparison (ringedToposHom Λ (p ≫ f))).app
        ((HomotopyCategory.quotient (SheafOfModules.{u + 1}
          (ringSheaf (ringedTopos Λ S).O)) (ComplexShape.up ℤ)).obj I) =
    (pullback Λ p).map ((derivedPullbackComparison (ringedToposHom Λ f)).app
        ((HomotopyCategory.quotient (SheafOfModules.{u + 1}
          (ringSheaf (ringedTopos Λ S).O)) (ComplexShape.up ℤ)).obj I)) ≫
      (derivedPullbackComparison (ringedToposHom Λ p)).app
        ((HomotopyCategory.quotient (SheafOfModules.{u + 1}
          (ringSheaf (ringedTopos Λ X).O)) (ComplexShape.up ℤ)).obj
          (((ringedToposHom Λ f).pullbackTopos.mapHomologicalComplex (ComplexShape.up ℤ)).obj I)) ≫
      DerivedCategory.Qh.map ((HomotopyCategory.quotient (SheafOfModules.{u + 1}
          (ringSheaf (ringedTopos Λ W).O)) (ComplexShape.up ℤ)).map
        ((NatTrans.mapHomologicalComplex (pullbackCompModulesIso Λ p f).hom
          (ComplexShape.up ℤ)).app I)) := by
  set J := (HomotopyCategory.quotient (SheafOfModules.{u + 1}
    (ringSheaf (ringedTopos Λ S).O)) (ComplexShape.up ℤ)).obj I with hJ
  set qW := HomotopyCategory.quotient (SheafOfModules.{u + 1}
    (ringSheaf (ringedTopos Λ W).O)) (ComplexShape.up ℤ) with hqW
  let := Stacks.Cohomology.DerivedPullbackOnRingedTopoi.hasLeftDerivedFunctor_pullbackOnHomotopy
    (X := ringedTopos Λ W) (Y := ringedTopos Λ S) ((ringedToposHom Λ f).comp (ringedToposHom Λ p))
    (RingedToposSiteHom.isMorphismOfSites_comp_u _ _ (isMorphismOfSites_ringedToposHom Λ p)
      (isMorphismOfSites_ringedToposHom Λ f))
  have : ((ringedToposHom Λ f).comp (ringedToposHom Λ p)).pushforwardTopos.Additive :=
    have := ((ringedToposHom Λ f).comp
      (ringedToposHom Λ p)).pullbackPushforwardAdjunctionTopos.rightAdjoint_preservesLimits
    Functor.additive_of_preserves_binary_products _
  have : ((ringedToposHom Λ f).comp (ringedToposHom Λ p)).pullbackTopos.Additive :=
    Adjunction.left_adjoint_additive
      ((ringedToposHom Λ f).comp (ringedToposHom Λ p)).pullbackPushforwardAdjunctionTopos
  have h₁ := derivedPullbackCompComparison_app_comp_derivedPullbackComparison_app
    (ringedToposHom Λ p) (ringedToposHom Λ f) J
  have h₂ : (derivedPullbackIsoOfIso (fSharpCompatible_comp Λ p f)).hom.app
        (DerivedCategory.Qh.obj J) ≫
      (derivedPullbackComparison (ringedToposHom Λ (p ≫ f))).app J =
      (derivedPullbackComparison ((ringedToposHom Λ f).comp (ringedToposHom Λ p))).app J ≫
        (pullbackOnHomotopyIsoOfIso (fSharpCompatible_comp Λ p f)).hom.app J :=
    Functor.leftDerivedNatTrans_app _ _ _ _
      (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
        (ringSheaf (ringedTopos Λ S).O)) (ComplexShape.up ℤ)) _ _
  have h₃ : DerivedCategory.Qh.map
      ((pullbackOnHomotopyCompIso
        (ringedToposHom Λ p) (ringedToposHom Λ f)).hom.app J) ≫
      (pullbackOnHomotopyIsoOfIso (fSharpCompatible_comp Λ p f)).hom.app J =
      DerivedCategory.Qh.map (qW.map
        ((NatTrans.mapHomologicalComplex (pullbackCompModulesIso Λ p f).hom
          (ComplexShape.up ℤ)).app I)) := by
    have e₁ : (pullbackOnHomotopyIsoOfIso (fSharpCompatible_comp Λ p f)).hom.app J =
        DerivedCategory.Qh.map (qW.map
          ((NatTrans.mapHomologicalComplex
            (RingedToposSiteHom.pullbackToposIsoOfIso (fSharpCompatible_comp Λ p f)).hom
              (ComplexShape.up ℤ)).app I)) := rfl
    have e₂ : (pullbackOnHomotopyCompIso
        (ringedToposHom Λ p) (ringedToposHom Λ f)).hom.app J =
        qW.map ((Functor.mapHomologicalComplexCompIso
          (RingedToposSiteHom.pullbackToposCompIso (ringedToposHom Λ p) (ringedToposHom Λ f))
            (ComplexShape.up ℤ)).hom.app I) := rfl
    rw [e₁, e₂]
    erw [← Functor.map_comp, ← Functor.map_comp]
    congr 2
  have h₀ : (pullbackCompIso Λ p f).hom.app (DerivedCategory.Qh.obj J) =
      (derivedPullbackCompComparison (ringedToposHom Λ p) (ringedToposHom Λ f)).app
          (DerivedCategory.Qh.obj J) ≫
      (derivedPullbackIsoOfIso (fSharpCompatible_comp Λ p f)).hom.app
        (DerivedCategory.Qh.obj J) := rfl
  rw [h₀, Category.assoc, h₂, reassoc_of% h₁, h₃]
  rfl

/-- `pullbackCompIso_hom_app_comp_comparison` at an object of the homotopy category. -/
theorem pullbackCompIso_hom_app_comp_comparison_homotopy {W X S : Scheme.{u}} (p : W ⟶ X)
    (f : X ⟶ S)
    (K : (HomotopyCategory (SheafOfModules.{u + 1}
      (ringSheaf (ringedTopos Λ S).O)) (ComplexShape.up ℤ))) :
    (pullbackCompIso Λ p f).hom.app (DerivedCategory.Qh.obj K) ≫
      (derivedPullbackComparison (ringedToposHom Λ (p ≫ f))).app K =
    (pullback Λ p).map ((derivedPullbackComparison (ringedToposHom Λ f)).app K) ≫
      (derivedPullbackComparison (ringedToposHom Λ p)).app
        (((ringedToposHom Λ f).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ)).obj K) ≫
      DerivedCategory.Qh.map ((NatTrans.mapHomotopyCategory (pullbackCompModulesIso Λ p f).hom
        (ComplexShape.up ℤ)).app K) := by
  obtain ⟨I, rfl⟩ := HomotopyCategory.quotient_obj_surjective K
  exact pullbackCompIso_hom_app_comp_comparison Λ p f I

/-- **`pullbackCongr` on objects of the homotopy category**: followed by the comparison of the
derived with the degreewise inverse image, it is the comparison followed by
`pullbackCongrModulesIso` applied degreewise. -/
theorem pullbackCongr_readThrough {Y S : Scheme.{u}} {a b : Y ⟶ S} (hab : a = b) :
    Stacks.Cohomology.BaseChange.ReadThrough DerivedCategory.Qh DerivedCategory.Qh
      (pullbackCongr Λ hab) (derivedPullbackComparison (ringedToposHom Λ a))
      (derivedPullbackComparison (ringedToposHom Λ b))
      (fun K => (NatTrans.mapHomotopyCategory (pullbackCongrModulesIso Λ hab).hom
        (ComplexShape.up ℤ)).app K) := by
  subst hab
  intro K
  simp only [pullbackCongr, pullbackCongrModulesIso, eqToIso_refl, Iso.refl_hom, NatTrans.id_app,
    Category.id_comp, NatTrans.mapHomotopyCategory_id, CategoryTheory.Functor.map_id]
  exact (Category.comp_id _).symm

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **`moduleBaseChange` applied degreewise is the underived mate on homotopy categories** of
`pullbackSquareModulesIso` applied degreewise. -/
theorem moduleBaseChange_counitCompat :
    Stacks.Cohomology.BaseChange.CounitCompat
      (homotopyPullbackPushforwardAdjunction (ringedToposHom Λ g))
      (homotopyPullbackPushforwardAdjunction (ringedToposHom Λ h))
      (fK := (ringedToposHom Λ f').pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
      (eK := (ringedToposHom Λ e).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
      (PK := (ringedToposHom Λ (h ≫ f')).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
      (PK' := (ringedToposHom Λ (e ≫ g)).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
      (fun K => (NatTrans.mapHomotopyCategory (pullbackCompModulesIso Λ h f').hom
        (ComplexShape.up ℤ)).app K)
      (fun K => (NatTrans.mapHomotopyCategory (pullbackCongrModulesIso Λ w).hom
        (ComplexShape.up ℤ)).app K)
      (fun K => (NatTrans.mapHomotopyCategory (pullbackCompModulesIso Λ e g).inv
        (ComplexShape.up ℤ)).app K)
      (fun K => (NatTrans.mapHomotopyCategory (moduleBaseChange Λ f' g h e w)
        (ComplexShape.up ℤ)).app K) :=
  Stacks.Cohomology.BaseChange.counitCompat_mapHomotopyCategory _ _
    (pullbackCompModulesIso Λ h f') (pullbackCongrModulesIso Λ w) (pullbackCompModulesIso Λ e g) _
    (pullbackSquareModulesIso Λ f' g h e w) rfl (moduleBaseChange_counit Λ f' g h e w)

/-- **The unbounded base change map on an object of the homotopy category.** `baseChangeMap` at
`K`, preceded by `(f')⁻¹` of the unit `g_*K ⟶ Rg_*K` and followed by `Rh_*` of the comparison
`e⁻¹K ⟶ e⁻¹K` of the derived with the degreewise inverse image, is the comparison of `(f')⁻¹`,
followed by `moduleBaseChange` applied degreewise and by the unit of `Rh_*`. -/
theorem baseChangeMap_fac (K : HomotopyCategory (SheafOfModules.{u + 1}
      (ringSheaf (ringedTopos Λ T).O)) (ComplexShape.up ℤ)) :
    Stacks.Cohomology.BaseChange.UnitFac DerivedCategory.Qh DerivedCategory.Qh
      (baseChangeMap Λ f' g h e w) (derivedPushforwardUnit (ringedToposHom Λ g))
      (derivedPushforwardUnit (ringedToposHom Λ h))
      (derivedPullbackComparison (ringedToposHom Λ f'))
      (derivedPullbackComparison (ringedToposHom Λ e))
      (fun K => (NatTrans.mapHomotopyCategory (moduleBaseChange Λ f' g h e w)
        (ComplexShape.up ℤ)).app K) K :=
  Stacks.Cohomology.BaseChange.mateEquiv_app_fac_of_three
    (fK := (ringedToposHom Λ f').pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
    (eK := (ringedToposHom Λ e).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
    (PK := (ringedToposHom Λ (h ≫ f')).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
    (PK' := (ringedToposHom Λ (e ≫ g)).pullbackTopos.mapHomotopyCategory (ComplexShape.up ℤ))
    (cf := derivedPullbackComparison (ringedToposHom Λ f'))
    (ce := derivedPullbackComparison (ringedToposHom Λ e))
    (cP := derivedPullbackComparison (ringedToposHom Λ (h ≫ f')))
    (cP' := derivedPullbackComparison (ringedToposHom Λ (e ≫ g)))
    (homotopyPullbackPushforwardAdjunction (ringedToposHom Λ g))
    (homotopyPullbackPushforwardAdjunction (ringedToposHom Λ h)) (adjunction Λ g) (adjunction Λ h)
    (Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction_counit_fac _
      (isMorphismOfSites_ringedToposHom Λ g))
    (Stacks.Cohomology.DerivedPullbackOnRingedTopoi.derivedAdjunction_counit_fac _
      (isMorphismOfSites_ringedToposHom Λ h))
    (pullbackCompIso Λ h f') (pullbackCongr Λ w) (pullbackCompIso Λ e g)
    (fun K => (NatTrans.mapHomotopyCategory (pullbackCompModulesIso Λ h f').hom
      (ComplexShape.up ℤ)).app K)
    (fun K => (NatTrans.mapHomotopyCategory (pullbackCongrModulesIso Λ w).hom
      (ComplexShape.up ℤ)).app K)
    (fun K => (NatTrans.mapHomotopyCategory (pullbackCompModulesIso Λ e g).hom
      (ComplexShape.up ℤ)).app K)
    (fun K => (NatTrans.mapHomotopyCategory (pullbackCompModulesIso Λ e g).inv
      (ComplexShape.up ℤ)).app K)
    (pullbackCompIso_hom_app_comp_comparison_homotopy Λ h f')
    (pullbackCongr_readThrough Λ w)
    (pullbackCompIso_hom_app_comp_comparison_homotopy Λ e g)
    (fun K => mapHomotopyCategory_hom_app_comp_inv_app (pullbackCompModulesIso Λ e g) K)
    (fun K => (NatTrans.mapHomotopyCategory (moduleBaseChange Λ f' g h e w)
      (ComplexShape.up ℤ)).app K)
    (moduleBaseChange_counitCompat Λ f' g h e w)
    K

end DerivedPullback

/-! ### The two base change maps on bounded below objects -/

section BoundedBelow

-- `pullback`, `pushforward` and `baseChangeMap` of `D(-_étale, Λ)`
-- (`AdjunctionForRingedTopoi.lean:394` in
-- `StacksFrontier/CategoryTheory/Sites/Cohomology/DerivedPushforward/`) and
-- `Stacks.Cohomology.BaseChange.derived` are built under the standard model.
attribute [local instance] HasDerivedCategory.standard
attribute [local instance 2000] HomotopyCategory.Plus.instHasPointwiseRightDerivedFunctorQuasiIso

open Stacks.Cohomology.DerivedPullbackPushforwardAdjunction

variable (Λ : Type (u + 1)) [CommRing Λ]

/-- **The derived inverse image of `D(-_étale, Λ)` is computed degreewise on every complex**, the
inverse image of sheaves of `Λ̲`-modules being exact. -/
theorem isIso_derivedPullbackComparison_app_ringedToposHom {X Y : Scheme.{u}} (f : X ⟶ Y)
    (K : HomotopyCategory (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ Y).O)) (ComplexShape.up ℤ)) :
    IsIso ((derivedPullbackComparison (ringedToposHom Λ f)).app K) := by
  have hfac : (Stacks.Sheaves.DerivedPullback.derivedPullbackIsoMapDerived
      (ringedToposHom Λ f)).inv.app (DerivedCategory.Qh.obj K) ≫
        (derivedPullbackComparison (ringedToposHom Λ f)).app K =
      (ringedToposHom Λ f).pullbackTopos.mapDerivedCategoryFactorsh.hom.app K :=
    Functor.leftDerived_fac_app _ _ (HomotopyCategory.quasiIso (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ Y).O)) (ComplexShape.up ℤ)) _ _ K
  exact IsIso.of_isIso_fac_left hfac

variable {X' Y S T : Scheme.{u}} (f' : X' ⟶ S) (g : T ⟶ S) (h : Y ⟶ X') (e : Y ⟶ T)
  (w : h ≫ f' = e ≫ g)

/-- **The two base change maps are invertible together on `D⁺`**: for `K` bounded below,
`baseChangeMap` of `D(-_étale, Λ)` is invertible at `K` exactly when `derivedBaseChangePlus` is.
Both are computed on a bounded below complex of injectives representing `K`, by
`baseChangeMap_fac` and `Stacks.Cohomology.BaseChange.derived_fac_app`, as the degreewise base
change map followed by the unit of `Rh_*` and of its bounded below version. -/
theorem isIso_baseChangeMap_app_iff_isIso_derivedBaseChangePlus_app
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ T).O))) :
    IsIso ((baseChangeMap Λ f' g h e w).app (DerivedCategory.Plus.ι.obj K)) ↔
      IsIso ((derivedBaseChangePlus Λ f' g h e w).app K) :=
  Stacks.Cohomology.BaseChange.isIso_app_ι_iff_isIso_derived_app
    (ringedToposHom Λ g).pushforwardTopos (ringedToposHom Λ h).pushforwardTopos
    (ringedToposHom Λ f').pullbackTopos (ringedToposHom Λ e).pullbackTopos
    (baseChangeMap Λ f' g h e w) (derivedPushforwardUnit (ringedToposHom Λ g))
    (derivedPushforwardUnit (ringedToposHom Λ h)) (derivedPullbackComparison (ringedToposHom Λ f'))
    (derivedPullbackComparison (ringedToposHom Λ e)) (moduleBaseChange Λ f' g h e w)
    (baseChangeMap_fac Λ f' g h e w)
    (fun L => isIso_derivedPushforwardUnit_app_of_isKInjective (ringedToposHom Λ g)
      (((InjectiveObject.ι (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ T).O))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj)
      (inferInstanceAs (CochainComplex.IsKInjective (((InjectiveObject.ι (SheafOfModules.{u + 1}
        (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos Λ T).O))).mapHomologicalComplex
          (ComplexShape.up ℤ)).obj L.obj))))
    (isIso_derivedPullbackComparison_app_ringedToposHom Λ f')
    (isIso_derivedPullbackComparison_app_ringedToposHom Λ e)
    (exists_quasiIso_isKInjective (ringedTopos Λ Y)) K

/-- **For `ℤ/mℤ`-coefficients, the base change map of `D(-_étale, ℤ/m)` is invertible at a bounded
below object exactly when the abelian base change map is invertible at its underlying complex of
abelian sheaves**: `baseChangeMap` at `K` is invertible if and only if
`Stacks.EtaleCohomology.smallEtaleDerivedBaseChangeAb` is at the underlying complex of abelian
sheaves of `K`. This is how a base change theorem proved for abelian sheaves annihilated by `m`
is read on `D(-_étale, ℤ/m)`. -/
theorem isIso_baseChangeMap_app_iff (m : ℕ)
    (K : DerivedCategory.Plus (SheafOfModules.{u + 1}
      (Stacks.SheafOfModules.Tensor.ringSheaf (ringedTopos (ULift.{u + 1} (ZMod m)) T).O))) :
    IsIso ((baseChangeMap (ULift.{u + 1} (ZMod m)) f' g h e w).app
        (DerivedCategory.Plus.ι.obj K)) ↔
      IsIso ((smallEtaleDerivedBaseChangeAb f' g h e w).app
        ((forgetDerivedPlus (ULift.{u + 1} (ZMod m)) T).obj K)) :=
  (isIso_baseChangeMap_app_iff_isIso_derivedBaseChangePlus_app _ f' g h e w K).trans
    (isIso_derivedBaseChangePlus_app_iff f' g h e w m K)

end BoundedBelow

end Stacks.EtaleCohomology.EtaleCoefficients

end
