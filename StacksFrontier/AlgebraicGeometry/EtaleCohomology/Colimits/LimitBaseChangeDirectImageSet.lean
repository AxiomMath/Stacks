module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.LimitBaseChangeSetInverseImage

/-!
# Base change for direct images of sheaves of sets passes to the limit

Let `I` be a directed set and consider an inverse system of cartesian diagrams of schemes

```
X_i  ←-h_i-  Y_i
|f_i         |e_i
S_i  ←-g_i-  T_i
```

with affine transition morphisms and with every `g_i` quasi-compact and quasi-separated, with
limit the cartesian square `X ← Y, S ← T` with morphisms `f, g, h, e`. Let `(ℱ_i, φ_{i'i})` be a
system of sheaves of sets on `(T_i)` as in [Stacks, Tag 0EZL] and let `ℱ = colim p_i^{-1}ℱ_i` on
`T`. [Stacks, Tag 0EZT] (1) asserts: if `f_i^{-1}g_{i,*}ℱ_i = h_{i,*}e_i^{-1}ℱ_i` for all `i`, then
`f^{-1}g_*ℱ = h_*e^{-1}ℱ`. This file proves it
(`Stacks.EtaleCohomology.LimitSetBaseChange.isIso_smallEtaleSetBaseChange_of_isLimit`), by the
argument the source gives for (2):

* `e^{-1}ℱ = colim q_i^{-1}e_i^{-1}ℱ_i`
  (`Stacks.EtaleCohomology.LimitSetBaseChange.isDirPresentation_inverseImageSystem`);
* [Stacks, Tag 0EYM] in degree zero for sheaves of sets, twice:
  `g_*ℱ = colim s_i^{-1}g_{i,*}ℱ_i` and `h_*e^{-1}ℱ = colim r_i^{-1}h_{i,*}e_i^{-1}ℱ_i`
  (`Stacks.EtaleCohomology.LimitSetDirectImage.existsUnique_setDirectImage_desc`, fed with
  [Stacks, Tag 09YQ] in degree zero over quasi-compact quasi-separated objects,
  `Stacks.EtaleCohomology.SetLinearization.isSectionsColimitAt_of_presentation`);
* inverse image along `f` is a left adjoint, and the base change map of the limit square is
  compatible with those of the levels (`Stacks.EtaleCohomology.LimitSetBaseChange.cube_limit`,
  `Stacks.EtaleCohomology.LimitSetBaseChange.cube_transition`, both instances of the cube of
  square comparisons
  `Stacks.EtaleCohomology.LimitSetBaseChangeCube.squarePushforwardIso_cube_app`);
  so it is the colimit of the base change maps of the levels, which are isomorphisms.

The argument is run on hom-sets: a map is invertible when composing with it is a bijection of
hom-sets (`CategoryTheory.isIso_of_coyoneda_map_bijective`), and through the adjunction along
`f` and the two colimit descriptions that bijection is the family of the bijections the levels
supply.

## Main results

* `Stacks.EtaleCohomology.LimitSetBaseChange.isIso_smallEtaleSetBaseChange_of_isLimit` —
  **[Stacks, Tag 0EZT] (1).**

## References

* [Stacks Project, Tag 0EZT](https://stacks.math.columbia.edu/tag/0EZT)
* [Stacks Project, Tag 0EYM](https://stacks.math.columbia.edu/tag/0EYM)
* [Stacks Project, Tag 0EZL](https://stacks.math.columbia.edu/tag/0EZL)

Tags covered: 0EZT (conclusion (1)).
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry AlgebraicGeometry.Scheme
open Stacks.EtaleCohomology.LimitDirectImage Stacks.EtaleCohomology.SetLinearization
open Stacks.EtaleCohomology.LimitHigherDirectImage (limitMorphism limitMorphism_comp_π)

universe u

namespace Stacks.EtaleCohomology.LimitSetBaseChange

/-! ### Two rearrangements in an arbitrary category -/

/-- The rearrangement behind `cube_limit`. -/
theorem cube_limit_algebra {𝒜 : Type*} [Category* 𝒜]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ : 𝒜}
    {πg : O₀ ⟶ O₂} {gx : O₀ ⟶ O₁} {psg : O₁ ⟶ O₂} {sβ : O₂ ⟶ O₄} {sη : O₂ ⟶ O₃}
    {sSq : O₃ ⟶ O₄} {gpη : O₁ ⟶ O₅} {psgN : O₅ ⟶ O₃} {βi : O₀ ⟶ O₇} {gηi : O₀ ⟶ O₆}
    {sqG : O₆ ⟶ O₇} {fπ : O₇ ⟶ O₉} {fhx : O₇ ⟶ O₈} {fpsh : O₈ ⟶ O₉} {gex : O₆ ⟶ O₁₀}
    {sqq : O₁₀ ⟶ O₈} {gpse : O₅ ⟶ O₁₀} {psf : O₉ ⟶ O₄}
    (hπg : πg = gx ≫ psg) (hsβ : sβ = sη ≫ sSq) (n₁ : psg ≫ sη = gpη ≫ psgN)
    (hβi : βi = gηi ≫ sqG) (hfπ : fπ = fhx ≫ fpsh) (n₂ : sqG ≫ fhx = gex ≫ sqq)
    (e₃ : gηi ≫ gex = gx ≫ gpη ≫ gpse) (K : gpse ≫ sqq ≫ fpsh ≫ psf = psgN ≫ sSq) :
    πg ≫ sβ = βi ≫ fπ ≫ psf := by
  rw [hπg, hsβ, hβi, hfπ]
  simp only [Category.assoc]
  rw [reassoc_of% n₁, reassoc_of% n₂, reassoc_of% e₃, K]

/-- The rearrangement behind `cube_transition`. -/
theorem cube_transition_algebra {𝒜 : Type*} [Category* 𝒜]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ O₁₀ : 𝒜}
    {βj : O₀ ⟶ O₂} {gηj : O₀ ⟶ O₁} {sqjG : O₁ ⟶ O₂} {fd : O₂ ⟶ O₄} {fhm : O₂ ⟶ O₃}
    {ftsqh : O₃ ⟶ O₄} {gem : O₁ ⟶ O₅} {sqjT : O₅ ⟶ O₃} {gmt : O₀ ⟶ O₆} {gtη : O₆ ⟶ O₇}
    {gtsqe : O₇ ⟶ O₅} {dg : O₀ ⟶ O₈} {tsqg : O₆ ⟶ O₈} {tβ : O₈ ⟶ O₁₀} {tgη : O₈ ⟶ O₉}
    {tsqi : O₉ ⟶ O₁₀} {tsqgN : O₇ ⟶ O₉} {tsqfinv : O₁₀ ⟶ O₄} {tsqf : O₄ ⟶ O₁₀}
    (hβj : βj = gηj ≫ sqjG) (hfd : fd = fhm ≫ ftsqh) (n₂ : sqjG ≫ fhm = gem ≫ sqjT)
    (e₃ : gηj ≫ gem = gmt ≫ gtη ≫ gtsqe) (hdg : dg = gmt ≫ tsqg) (htβ : tβ = tgη ≫ tsqi)
    (n₄ : tsqg ≫ tgη = gtη ≫ tsqgN) (K : gtsqe ≫ sqjT ≫ ftsqh ≫ tsqf = tsqgN ≫ tsqi)
    (hinv : tsqf ≫ tsqfinv = 𝟙 _) :
    βj ≫ fd = dg ≫ tβ ≫ tsqfinv := by
  have K' : gtsqe ≫ sqjT ≫ ftsqh = tsqgN ≫ tsqi ≫ tsqfinv := by
    rw [← reassoc_of% K]
    simp only [hinv, Category.comp_id]
  rw [hβj, hfd, hdg, htβ]
  simp only [Category.assoc]
  rw [reassoc_of% n₂, reassoc_of% e₃, K', reassoc_of% n₄]

/-- The rearrangement behind `stage_transition`. -/
theorem stage_transition_algebra {𝒜 : Type*} [Category* 𝒜]
    {O₀ O₁ O₂ O₃ O₄ O₅ O₆ O₇ O₈ O₉ : 𝒜}
    {βj : O₀ ⟶ O₁} {fd : O₁ ⟶ O₂} {ftτ : O₂ ⟶ O₃} {fcx : O₃ ⟶ O₄} {psfj : O₄ ⟶ O₅}
    {dg : O₀ ⟶ O₆} {tβ : O₆ ⟶ O₇} {tsqfinv : O₇ ⟶ O₂} {tfτ : O₇ ⟶ O₈} {tsqfinv' : O₈ ⟶ O₃}
    {tsqf' : O₃ ⟶ O₈} {tps : O₈ ⟶ O₉} {cs : O₉ ⟶ O₅}
    (c₂ : βj ≫ fd = dg ≫ tβ ≫ tsqfinv) (n : tsqfinv ≫ ftτ = tfτ ≫ tsqfinv')
    (p : fcx ≫ psfj = tsqf' ≫ tps ≫ cs) (hinv : tsqfinv' ≫ tsqf' = 𝟙 _) :
    βj ≫ fd ≫ ftτ ≫ fcx ≫ psfj = dg ≫ tβ ≫ tfτ ≫ tps ≫ cs := by
  rw [← Category.assoc βj, c₂]
  simp only [Category.assoc]
  rw [reassoc_of% n, p, reassoc_of% hinv]

/-- The rearrangement behind `stage_comp`. -/
theorem stage_comp_algebra {𝒜 : Type*} [Category* 𝒜] {O₀ O₁ O₂ O₃ O₄ O₅ O₆ : 𝒜}
    {π : O₀ ⟶ O₁} {sβ : O₁ ⟶ O₂} {sfχ : O₂ ⟶ O₃} {βi : O₀ ⟶ O₄} {fπ : O₄ ⟶ O₅}
    {psf : O₅ ⟶ O₂} {frχ : O₅ ⟶ O₆} {psf' : O₆ ⟶ O₃}
    (c₁ : π ≫ sβ = βi ≫ fπ ≫ psf) (n : psf ≫ sfχ = frχ ≫ psf') :
    βi ≫ fπ ≫ frχ ≫ psf' = π ≫ sβ ≫ sfχ := by
  rw [← Category.assoc π, c₁]
  simp only [Category.assoc]
  rw [n]

/-! ### The presentation, read through the adjunctions -/

section Presentation

variable {I : Type u} [Preorder I] {D : Iᵒᵖ ⥤ Scheme.{u}} (c : Cone D)
  (F : EtaleSheafSystem D (Type (u + 1)))

/-- **`𝓕 = colim f_i^{-1}F_i` for sheaves of sets**: every family of maps
`τ_i : f_i^{-1}F_i ⟶ 𝒢` compatible with the transition maps of the system factors uniquely through
the legs `ι_i : f_i^{-1}F_i ⟶ 𝓕`. The inverse images along the projections are those of
`Stacks.EtaleCohomology.LimitDirectImage.etalePullback`, and the compatibility is read through the
comparison of the inverse images along `f_i = f_{i'} ≫ f_{i'i}`, as in
`Stacks.EtaleCohomology.LimitDirectImage.coneTranspose_comp`. -/
def IsSetPullbackColimitPresentation (𝓕 : Sheaf (smallEtaleTopology c.pt) (Type (u + 1)))
    (ι : ∀ i : Iᵒᵖ, (etalePullback (c.π.app i) (Type (u + 1))).obj (F.obj i) ⟶ 𝓕) : Prop :=
  ∀ (𝒢 : Sheaf (smallEtaleTopology c.pt) (Type (u + 1)))
    (τ : ∀ i : Iᵒᵖ, (etalePullback (c.π.app i) (Type (u + 1))).obj (F.obj i) ⟶ 𝒢),
    (∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j),
      (Adjunction.leftAdjointCompIso (systemAdjunction D (Type (u + 1)) a)
          (etaleAdjunction (c.π.app i) (Type (u + 1))) (etaleAdjunction (c.π.app j) (Type (u + 1)))
          (coneProjectionComp (Type (u + 1)) c a)).inv.app (F.obj j) ≫
        (etalePullback (c.π.app i) (Type (u + 1))).map (F.map a) ≫ τ i = τ j) →
      ∃! χ : 𝓕 ⟶ 𝒢, ∀ i : Iᵒᵖ, ι i ≫ χ = τ i

/-- A presentation by its inverse-image universal property is a presentation in adjoint form, with
the transposed legs. -/
theorem isDirPresentation_of_isSetPullbackColimitPresentation
    {𝓕 : Sheaf (smallEtaleTopology c.pt) (Type (u + 1))}
    (ι : ∀ i : Iᵒᵖ, (etalePullback (c.π.app i) (Type (u + 1))).obj (F.obj i) ⟶ 𝓕)
    (hι : ∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j),
      (Adjunction.leftAdjointCompIso (systemAdjunction D (Type (u + 1)) a)
          (etaleAdjunction (c.π.app i) (Type (u + 1))) (etaleAdjunction (c.π.app j) (Type (u + 1)))
          (coneProjectionComp (Type (u + 1)) c a)).inv.app (F.obj j) ≫
        (etalePullback (c.π.app i) (Type (u + 1))).map (F.map a) ≫ ι i = ι j)
    (hpres : IsSetPullbackColimitPresentation c F 𝓕 ι) :
    IsDirPresentation (Type (u + 1)) c F 𝓕 (coneTranspose (Type (u + 1)) c ι) := by
  refine ⟨fun i j a => coneTranspose_comp (Type (u + 1)) c F ι (fun a => hι a) a,
    fun 𝒦 τ hτ => ?_⟩
  obtain ⟨χ, hχ, hu⟩ := hpres 𝒦
    (fun i => ((etaleAdjunction (c.π.app i) (Type (u + 1))).homEquiv _ _).symm (τ i))
    (fun i j a => by
      rw [← F.homEquiv_symm_mapTranspose a]
      exact (leftAdjointCompIso_inv_homEquiv_symm (systemAdjunction D (Type (u + 1)) a)
        (etaleAdjunction (c.π.app i) (Type (u + 1))) (etaleAdjunction (c.π.app j) (Type (u + 1)))
        (coneProjectionComp (Type (u + 1)) c a) (F.mapTranspose a) (τ i)).trans
          (congrArg _ (hτ a).symm))
  refine ⟨χ, fun i => ?_, fun y hy => hu y fun i => ?_⟩
  · refine (Adjunction.homEquiv_naturality_right _ _ _).symm.trans ?_
    rw [hχ i, Equiv.apply_symm_apply]
  · rw [← hy i]
    exact ((Equiv.symm_apply_eq _).mpr (Adjunction.homEquiv_naturality_right
      (etaleAdjunction (c.π.app i) (Type (u + 1))) (ι i) y)).symm

end Presentation

/-! ### The base change maps of the levels and of the limit, transposed, and the two cubes -/

section Cubes

variable {I : Type u} [Preorder I] {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}} (f : DX ⟶ DS)
  (g : DT ⟶ DS) (h : DY ⟶ DX) (e : DY ⟶ DT)
  (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i)
  {cX : Cone DX} {cS : Cone DS} {cT : Cone DT} {cY : Cone DY} (hcX : IsLimit cX)
  (hcS : IsLimit cS) (hcT : IsLimit cT)
  (F : EtaleSheafSystem DT (Type (u + 1)))
  {𝓕 : Sheaf (smallEtaleTopology cT.pt) (Type (u + 1))}
  (x : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (cT.π.app i) (Type (u + 1))).obj 𝓕)

include w in
/-- The square on the limits commutes, with the limit morphisms of the cones. -/
theorem limit_comm :
    limitMorphism e cY cT hcT ≫ limitMorphism g cT cS hcS =
      limitMorphism h cY cX hcX ≫ limitMorphism f cX cS hcS :=
  (LimitBaseChange.limitSquare_comm f g h e cX cS cT cY _ _ _ _ hcS
    (limitMorphism_comp_π f cX cS hcS) (limitMorphism_comp_π g cT cS hcS)
    (limitMorphism_comp_π h cY cX hcX) (limitMorphism_comp_π e cY cT hcT) w).symm

/-- **The base change map of the `i`-th square, transposed**: `g_{i, *}` of the unit
`F_i ⟶ e_{i, *}e_i^{-1}F_i` followed by the identification
`g_{i, *}e_{i, *} ≅ f_{i, *}h_{i, *}`. -/
def levelTranspose (i : Iᵒᵖ) :
    (smallEtalePushforward (g.app i) (Type (u + 1))).obj (F.obj i) ⟶
      (smallEtalePushforward (f.app i) (Type (u + 1))).obj
        ((smallEtalePushforward (h.app i) (Type (u + 1))).obj (inverseImageObj e F i)) :=
  (smallEtalePushforward (g.app i) (Type (u + 1))).map ((setAdj (e.app i)).unit.app (F.obj i)) ≫
    (squarePushforwardIso (h.app i) (g.app i) (f.app i) (e.app i) (e.app i ≫ g.app i) (w i).symm
      rfl (Type (u + 1))).hom.app (inverseImageObj e F i)

/-- **The base change map of the limit square, transposed.** -/
def limitTranspose :
    (smallEtalePushforward (limitMorphism g cT cS hcS) (Type (u + 1))).obj 𝓕 ⟶
      (smallEtalePushforward (limitMorphism f cX cS hcS) (Type (u + 1))).obj
        ((smallEtalePushforward (limitMorphism h cY cX hcX) (Type (u + 1))).obj
          (inverseImageSheaf e cY cT hcT 𝓕)) :=
  (smallEtalePushforward (limitMorphism g cT cS hcS) (Type (u + 1))).map
      ((setAdj (limitMorphism e cY cT hcT)).unit.app 𝓕) ≫
    (squarePushforwardIso (limitMorphism h cY cX hcX) (limitMorphism g cT cS hcS)
      (limitMorphism f cX cS hcS) (limitMorphism e cY cT hcT)
      (limitMorphism e cY cT hcT ≫ limitMorphism g cT cS hcS)
      (limit_comm f g h e w hcX hcS hcT) rfl (Type (u + 1))).hom.app
        (inverseImageSheaf e cY cT hcT 𝓕)

/-- **The cube of the projections**: the transposed base change map of the limit square is
compatible with those of the levels through the transposed cocone maps of [Stacks, Tag 0EYM] for
`g` and for `h`. -/
theorem cube_limit (i : Iᵒᵖ) :
    projectionTranspose g (Type (u + 1)) cT cS hcS F x i ≫
        (smallEtalePushforward (cS.π.app i) (Type (u + 1))).map
          (limitTranspose f g h e w hcX hcS hcT (𝓕 := 𝓕)) =
      levelTranspose f g h e w F i ≫
        (smallEtalePushforward (f.app i) (Type (u + 1))).map
          (projectionTranspose h (Type (u + 1)) cY cX hcX (inverseImageSystem e F)
            (inverseImageLeg e F cY cT hcT x) i) ≫
          (projectionSquareIso f (Type (u + 1)) cX cS hcS i).hom.app
            ((smallEtalePushforward (limitMorphism h cY cX hcX) (Type (u + 1))).obj
              (inverseImageSheaf e cY cT hcT 𝓕)) := by
  have n₁ := (projectionSquareIso g (Type (u + 1)) cT cS hcS i).hom.naturality
    ((setAdj (limitMorphism e cY cT hcT)).unit.app 𝓕)
  dsimp only [Functor.comp_map] at n₁
  have n₂ := (squarePushforwardIso (h.app i) (g.app i) (f.app i) (e.app i)
    (e.app i ≫ g.app i) (w i).symm rfl (Type (u + 1))).hom.naturality
      (inverseImageLeg e F cY cT hcT x i)
  dsimp only [Functor.comp_map] at n₂
  have e₃ : (smallEtalePushforward (g.app i) (Type (u + 1))).map
        ((setAdj (e.app i)).unit.app (F.obj i)) ≫
      (smallEtalePushforward (g.app i) (Type (u + 1))).map
        ((smallEtalePushforward (e.app i) (Type (u + 1))).map
          (inverseImageLeg e F cY cT hcT x i)) =
      (smallEtalePushforward (g.app i) (Type (u + 1))).map (x i) ≫
        (smallEtalePushforward (g.app i) (Type (u + 1))).map
          ((smallEtalePushforward (cT.π.app i) (Type (u + 1))).map
            ((setAdj (limitMorphism e cY cT hcT)).unit.app 𝓕)) ≫
        (smallEtalePushforward (g.app i) (Type (u + 1))).map
          ((projectionSquareIso e (Type (u + 1)) cY cT hcT i).inv.app
            (inverseImageSheaf e cY cT hcT 𝓕)) :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg (smallEtalePushforward (g.app i)
      (Type (u + 1))).map ((Adjunction.homEquiv_unit _ _ _
        (inverseImageLeg e F cY cT hcT x i)).symm.trans
          (homEquiv_inverseImageLeg e F cY cT hcT x i))).trans
      ((Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _))))
  have K := LimitSetBaseChangeCube.squarePushforwardIso_cube_app
    (limitMorphism e cY cT hcT) (limitMorphism g cT cS hcS) (limitMorphism h cY cX hcX)
    (limitMorphism f cX cS hcS) (e.app i) (g.app i) (h.app i) (f.app i)
    (cY.π.app i) (cT.π.app i) (cX.π.app i) (cS.π.app i)
    (limitMorphism e cY cT hcT ≫ limitMorphism g cT cS hcS) rfl
    (limit_comm f g h e w hcX hcS hcT)
    (e.app i ≫ g.app i) rfl (w i).symm
    (limitMorphism e cY cT hcT ≫ cT.π.app i) rfl (limitMorphism_comp_π e cY cT hcT i)
    (limitMorphism g cT cS hcS ≫ cS.π.app i) rfl (limitMorphism_comp_π g cT cS hcS i)
    (limitMorphism h cY cX hcX ≫ cX.π.app i) rfl (limitMorphism_comp_π h cY cX hcX i)
    (limitMorphism f cX cS hcS ≫ cS.π.app i) rfl (limitMorphism_comp_π f cX cS hcS i)
    (limitMorphism e cY cT hcT ≫ limitMorphism g cT cS hcS ≫ cS.π.app i)
    (by rw [Category.assoc, limitMorphism_comp_π g cT cS hcS i])
    rfl
    (by rw [limitMorphism_comp_π g cT cS hcS i, ← Category.assoc,
      limitMorphism_comp_π e cY cT hcT i, Category.assoc])
    (by rw [← Category.assoc, limit_comm f g h e w hcX hcS hcT, Category.assoc,
      limitMorphism_comp_π f cX cS hcS i, ← Category.assoc, limitMorphism_comp_π h cY cX hcX i,
      Category.assoc])
    (by rw [← Category.assoc, limit_comm f g h e w hcX hcS hcT, Category.assoc])
    (Category.assoc _ _ _).symm
    (Type (u + 1)) (inverseImageSheaf e cY cT hcT 𝓕)
  exact cube_limit_algebra rfl (Functor.map_comp _ _ _) n₁.symm rfl (Functor.map_comp _ _ _)
    n₂.symm e₃ K

/-- **The cube of the transitions**: the transposed base change maps of the levels are compatible
with the transposed transition maps of [Stacks, Tag 0EYM] for `g` and for `h`. -/
theorem cube_transition {i j : Iᵒᵖ} (a : i ⟶ j) :
    levelTranspose f g h e w F j ≫
        (smallEtalePushforward (f.app j) (Type (u + 1))).map
          (directTransition h (Type (u + 1)) (inverseImageSystem e F) a) =
      directTransition g (Type (u + 1)) F a ≫
        (systemPushforward DS (Type (u + 1)) a).map (levelTranspose f g h e w F i) ≫
          (transitionSquareIso f (Type (u + 1)) a).inv.app
            ((smallEtalePushforward (h.app i) (Type (u + 1))).obj (inverseImageObj e F i)) := by
  have n₂ := (squarePushforwardIso (h.app j) (g.app j) (f.app j) (e.app j)
    (e.app j ≫ g.app j) (w j).symm rfl (Type (u + 1))).hom.naturality
      ((inverseImageSystem e F).mapTranspose a)
  dsimp only [Functor.comp_map] at n₂
  have e₃ : (smallEtalePushforward (g.app j) (Type (u + 1))).map
        ((setAdj (e.app j)).unit.app (F.obj j)) ≫
      (smallEtalePushforward (g.app j) (Type (u + 1))).map
        ((smallEtalePushforward (e.app j) (Type (u + 1))).map
          ((inverseImageSystem e F).mapTranspose a)) =
      (smallEtalePushforward (g.app j) (Type (u + 1))).map (F.mapTranspose a) ≫
        (smallEtalePushforward (g.app j) (Type (u + 1))).map
          ((systemPushforward DT (Type (u + 1)) a).map ((setAdj (e.app i)).unit.app (F.obj i))) ≫
        (smallEtalePushforward (g.app j) (Type (u + 1))).map
          ((transitionSquareIso e (Type (u + 1)) a).inv.app (inverseImageObj e F i)) :=
    (Functor.map_comp _ _ _).symm.trans ((congrArg (smallEtalePushforward (g.app j)
      (Type (u + 1))).map ((Adjunction.homEquiv_unit (setAdj (e.app j)) _ _
        ((inverseImageSystem e F).mapTranspose a)).symm.trans
          ((congrArg ((setAdj (e.app j)).homEquiv _ _)
            (inverseImageSystem_mapTranspose e F a)).trans
            (homEquiv_inverseImageTransition e F a)))).trans
      ((Functor.map_comp _ _ _).trans (congrArg (_ ≫ ·) (Functor.map_comp _ _ _))))
  have n₄ := (transitionSquareIso g (Type (u + 1)) a).hom.naturality
    ((setAdj (e.app i)).unit.app (F.obj i))
  dsimp only [Functor.comp_map] at n₄
  have K := LimitSetBaseChangeCube.squarePushforwardIso_cube_app
    (e.app i) (g.app i) (h.app i) (f.app i) (e.app j) (g.app j) (h.app j) (f.app j)
    (DY.map a) (DT.map a) (DX.map a) (DS.map a)
    (e.app i ≫ g.app i) rfl (w i).symm (e.app j ≫ g.app j) rfl (w j).symm
    (e.app i ≫ DT.map a) rfl (LimitHigherDirectImage.transition_comm e a)
    (g.app i ≫ DS.map a) rfl (LimitHigherDirectImage.transition_comm g a)
    (h.app i ≫ DX.map a) rfl (LimitHigherDirectImage.transition_comm h a)
    (f.app i ≫ DS.map a) rfl (LimitHigherDirectImage.transition_comm f a)
    (e.app i ≫ g.app i ≫ DS.map a)
    (by rw [LimitHigherDirectImage.transition_comm g a, Category.assoc])
    rfl
    (by rw [LimitHigherDirectImage.transition_comm g a, ← Category.assoc,
      LimitHigherDirectImage.transition_comm e a, Category.assoc])
    (by rw [← Category.assoc, ← w i, Category.assoc, LimitHigherDirectImage.transition_comm f a,
      ← Category.assoc])
    (by rw [← Category.assoc, ← w i, Category.assoc])
    (Category.assoc _ _ _).symm
    (Type (u + 1)) (inverseImageObj e F i)
  exact cube_transition_algebra rfl (Functor.map_comp _ _ _) n₂.symm e₃ rfl
    (Functor.map_comp _ _ _) n₄.symm K (Iso.hom_inv_id_app _ _)

end Cubes

/-! ### The stage maps -/

section Stage

variable {I : Type u} [Preorder I] {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}} (f : DX ⟶ DS)
  (g : DT ⟶ DS) (h : DY ⟶ DX) (e : DY ⟶ DT)
  (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i)
  {cX : Cone DX} {cS : Cone DS} {cT : Cone DT} {cY : Cone DY} (hcX : IsLimit cX)
  (hcS : IsLimit cS) (hcT : IsLimit cT)
  (F : EtaleSheafSystem DT (Type (u + 1)))
  {𝓕 : Sheaf (smallEtaleTopology cT.pt) (Type (u + 1))}
  (x : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (cT.π.app i) (Type (u + 1))).obj 𝓕)
  (𝒢 : Sheaf (smallEtaleTopology cX.pt) (Type (u + 1)))

/-- **The stage map**: a map `h_{i, *}e_i^{-1}F_i ⟶ r_{i, *}𝒢` goes to the map
`g_{i, *}F_i ⟶ s_{i, *}f_*𝒢` obtained by composing with the transposed base change map of the
`i`-th square and the identification of the projection square for `f`. -/
def stageMap (i : Iᵒᵖ)
    (τ : (smallEtalePushforward (h.app i) (Type (u + 1))).obj (inverseImageObj e F i) ⟶
      (smallEtalePushforward (cX.π.app i) (Type (u + 1))).obj 𝒢) :
    (smallEtalePushforward (g.app i) (Type (u + 1))).obj (F.obj i) ⟶
      (smallEtalePushforward (cS.π.app i) (Type (u + 1))).obj
        ((smallEtalePushforward (limitMorphism f cX cS hcS) (Type (u + 1))).obj 𝒢) :=
  levelTranspose f g h e w F i ≫ (smallEtalePushforward (f.app i) (Type (u + 1))).map τ ≫
    (projectionSquareIso f (Type (u + 1)) cX cS hcS i).hom.app 𝒢

/-- **The stage maps are bijective** when the base change maps of the levels are invertible. -/
theorem bijective_stageMap (i : Iᵒᵖ)
    (hst : IsIso ((smallEtaleSetBaseChange.{u, 0} (e.app i) (h.app i) (g.app i) (f.app i)
      (w i).symm).app (F.obj i))) :
    Function.Bijective (stageMap f g h e w hcS F 𝒢 i) := by
  have hb := LimitSetBaseChangeCube.bijective_homEquiv_comp_map_of_isIso (setAdj (f.app i))
    ((smallEtaleSetBaseChange.{u, 0} (e.app i) (h.app i) (g.app i) (f.app i) (w i).symm).app
      (F.obj i)) ((smallEtalePushforward (cX.π.app i) (Type (u + 1))).obj 𝒢)
  rw [LimitSetBaseChangeCube.homEquiv_smallEtaleSetBaseChange_app (e.app i) (h.app i) (g.app i)
    (f.app i) (w i).symm (e.app i ≫ g.app i) rfl (w i).symm] at hb
  have hc : Function.Bijective (fun m : (smallEtalePushforward (g.app i) (Type (u + 1))).obj
      (F.obj i) ⟶ (smallEtalePushforward (f.app i) (Type (u + 1))).obj
        ((smallEtalePushforward (cX.π.app i) (Type (u + 1))).obj 𝒢) =>
      m ≫ (projectionSquareIso f (Type (u + 1)) cX cS hcS i).hom.app 𝒢) :=
    ⟨fun a b hab => by
        simpa using congrArg (· ≫ (projectionSquareIso f (Type (u + 1)) cX cS hcS i).inv.app 𝒢) hab,
      fun m =>
      ⟨m ≫ (projectionSquareIso f (Type (u + 1)) cX cS hcS i).inv.app 𝒢, by simp⟩⟩
  have e₀ : stageMap f g h e w hcS F 𝒢 i =
      (fun m => m ≫ (projectionSquareIso f (Type (u + 1)) cX cS hcS i).hom.app 𝒢) ∘
        (fun τ => levelTranspose f g h e w F i ≫
          (smallEtalePushforward (f.app i) (Type (u + 1))).map τ) :=
    funext fun τ => by simp only [stageMap, Function.comp_apply, Category.assoc]
  rw [e₀]
  exact hc.comp hb

/-- **The stage maps commute with the transposed transition maps.** -/
theorem stageMap_transition {i j : Iᵒᵖ} (a : i ⟶ j)
    (τ : (smallEtalePushforward (h.app i) (Type (u + 1))).obj (inverseImageObj e F i) ⟶
      (smallEtalePushforward (cX.π.app i) (Type (u + 1))).obj 𝒢) :
    stageMap f g h e w hcS F 𝒢 j
        (directTransition h (Type (u + 1)) (inverseImageSystem e F) a ≫
          (systemPushforward DX (Type (u + 1)) a).map τ ≫
            (coneProjectionComp (Type (u + 1)) cX a).hom.app 𝒢) =
      directTransition g (Type (u + 1)) F a ≫
        (systemPushforward DS (Type (u + 1)) a).map (stageMap f g h e w hcS F 𝒢 i τ) ≫
          (coneProjectionComp (Type (u + 1)) cS a).hom.app
            ((smallEtalePushforward (limitMorphism f cX cS hcS) (Type (u + 1))).obj 𝒢) := by
  have n := (transitionSquareIso f (Type (u + 1)) a).inv.naturality τ
  dsimp only [Functor.comp_map] at n
  have p := projectionSquareIso_paste_app f (Type (u + 1)) cX cS hcS a 𝒢
  simp only [stageMap, Functor.map_comp, Category.assoc]
  exact stage_transition_algebra (cube_transition f g h e w F a) n.symm p
    (Iso.inv_hom_id_app _ _)

/-- **The stage map of a map out of the limit**: for `χ : h_*e^{-1}𝓕 ⟶ 𝒢`, the stage map of the
transposed cocone map of `h` followed by `r_{i, *}χ` is the transposed cocone map of `g` followed
by `s_{i, *}` of the transposed base change map of the limit square and `f_*χ`. -/
theorem stageMap_comp
    (χ : (smallEtalePushforward (limitMorphism h cY cX hcX) (Type (u + 1))).obj
      (inverseImageSheaf e cY cT hcT 𝓕) ⟶ 𝒢) (i : Iᵒᵖ) :
    stageMap f g h e w hcS F 𝒢 i
        (projectionTranspose h (Type (u + 1)) cY cX hcX (inverseImageSystem e F)
            (inverseImageLeg e F cY cT hcT x) i ≫
          (smallEtalePushforward (cX.π.app i) (Type (u + 1))).map χ) =
      projectionTranspose g (Type (u + 1)) cT cS hcS F x i ≫
        (smallEtalePushforward (cS.π.app i) (Type (u + 1))).map
          (limitTranspose f g h e w hcX hcS hcT (𝓕 := 𝓕) ≫
            (smallEtalePushforward (limitMorphism f cX cS hcS) (Type (u + 1))).map χ) := by
  have n := (projectionSquareIso f (Type (u + 1)) cX cS hcS i).hom.naturality χ
  dsimp only [Functor.comp_map] at n
  simp only [stageMap, Functor.map_comp, Category.assoc]
  exact stage_comp_algebra (cube_limit f g h e w hcX hcS hcT F x i) n.symm

end Stage

/-! ### The theorem -/

section Core

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}} (f : DX ⟶ DS) (g : DT ⟶ DS) (h : DY ⟶ DX)
  (e : DY ⟶ DT) (w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
  {cX : Cone DX} {cS : Cone DS} {cT : Cone DT} {cY : Cone DY}
  (hcX : IsLimit cX) (hcS : IsLimit cS) (hcT : IsLimit cT)
  (F : EtaleSheafSystem DT (Type (u + 1)))
  {𝓕 : Sheaf (smallEtaleTopology cT.pt) (Type (u + 1))}
  (x : ∀ i : Iᵒᵖ, F.obj i ⟶ (smallEtalePushforward (cT.π.app i) (Type (u + 1))).obj 𝓕)

/-- **The transposed base change map of the limit square has the universal property of the
colimit of those of the levels**: for every sheaf `𝒢` on `X`, composing with it is a bijection
`(h_*e^{-1}ℱ ⟶ 𝒢) ≃ (g_*ℱ ⟶ f_*𝒢)`, as soon as the base change maps of the levels are
invertible. -/
theorem existsUnique_limitTranspose_comp
    (hdir : IsDirPresentation (Type (u + 1)) cT F 𝓕 x)
    (hsecg : ∀ (i₀ : I) (V : (DS.obj (Opposite.op i₀)).AffineEtale),
      LimitSetDirectImage.IsSectionsColimitAt F x i₀
        ((smallEtaleBaseChange (g.app (Opposite.op i₀))).obj ((AffineEtale.Spec _).obj V)))
    (hsech : ∀ (i₀ : I) (V : (DX.obj (Opposite.op i₀)).AffineEtale),
      LimitSetDirectImage.IsSectionsColimitAt (inverseImageSystem e F)
        (inverseImageLeg e F cY cT hcT x) i₀
        ((smallEtaleBaseChange (h.app (Opposite.op i₀))).obj ((AffineEtale.Spec _).obj V)))
    (hstage : ∀ i : Iᵒᵖ,
      IsIso ((smallEtaleSetBaseChange.{u, 0} (e.app i) (h.app i) (g.app i) (f.app i)
        (w i).symm).app (F.obj i)))
    (𝒢 : Sheaf (smallEtaleTopology cX.pt) (Type (u + 1)))
    (ψ : (smallEtalePushforward (limitMorphism g cT cS hcS) (Type (u + 1))).obj 𝓕 ⟶
      (smallEtalePushforward (limitMorphism f cX cS hcS) (Type (u + 1))).obj 𝒢) :
    ∃! χ : (smallEtalePushforward (limitMorphism h cY cX hcX) (Type (u + 1))).obj
        (inverseImageSheaf e cY cT hcT 𝓕) ⟶ 𝒢,
      limitTranspose f g h e w hcX hcS hcT (𝓕 := 𝓕) ≫
        (smallEtalePushforward (limitMorphism f cX cS hcS) (Type (u + 1))).map χ = ψ := by
  have hG := isDirPresentation_inverseImageSystem e F cY cT hcT x hdir
  have hσ : LimitSetDirectImage.IsSetDirectImageFamily g cS F
      (fun i => projectionTranspose g (Type (u + 1)) cT cS hcS F x i ≫
        (smallEtalePushforward (cS.π.app i) (Type (u + 1))).map ψ) := by
    intro i j a
    have hn := (coneProjectionComp (Type (u + 1)) cS a).hom.naturality ψ
    dsimp only [Functor.comp_map] at hn
    dsimp only
    rw [projectionTranspose_compat g (Type (u + 1)) cT cS hcS F x (fun a => hdir.1 a) a,
      Functor.map_comp]
    simp only [Category.assoc]
    rw [hn]
  have hbij := fun i => bijective_stageMap f g h e w hcS F 𝒢 i (hstage i)
  choose τ hτ using fun i => (hbij i).2
    (projectionTranspose g (Type (u + 1)) cT cS hcS F x i ≫
      (smallEtalePushforward (cS.π.app i) (Type (u + 1))).map ψ)
  have hτc : LimitSetDirectImage.IsSetDirectImageFamily h cX (inverseImageSystem e F) τ := by
    intro i j a
    refine (hbij j).1 ?_
    rw [stageMap_transition f g h e w hcS F 𝒢 a, hτ i, hτ j]
    exact hσ a
  obtain ⟨χ, hχ, hχu⟩ := LimitSetDirectImage.existsUnique_setDirectImage_desc.{u, u} h cX hcX
    (inverseImageSystem e F) (inverseImageLeg e F cY cT hcT x) (fun a => hG.1 a) hsech hτc
  obtain ⟨_, _, hu⟩ := LimitSetDirectImage.existsUnique_setDirectImage_desc.{u, u} g cS hcS F x
    (fun a => hdir.1 a) hsecg hσ
  refine ⟨χ, (hu _ fun i => ?_).trans (hu _ fun i => rfl).symm, fun χ' hχ' =>
    hχu χ' fun i => (hbij i).1 ?_⟩
  · rw [← stageMap_comp f g h e w hcX hcS hcT F x 𝒢 χ i]
    exact (congrArg _ (hχ i)).trans (hτ i)
  · refine (stageMap_comp f g h e w hcX hcS hcT F x 𝒢 χ' i).trans ?_
    rw [hχ', hτ i]

/-- **The base change map of the limit square is invertible**, in terms of the limit morphisms of
the cones, as soon as those of the levels are and the colimit descriptions of
[Stacks, Tag 0EYM] hold. The commutativity `wL` of the limit square is a free argument, so that a
caller passes the proof its own statement carries. -/
theorem isIso_smallEtaleSetBaseChange_limitMorphism
    (hdir : IsDirPresentation (Type (u + 1)) cT F 𝓕 x)
    (hsecg : ∀ (i₀ : I) (V : (DS.obj (Opposite.op i₀)).AffineEtale),
      LimitSetDirectImage.IsSectionsColimitAt F x i₀
        ((smallEtaleBaseChange (g.app (Opposite.op i₀))).obj ((AffineEtale.Spec _).obj V)))
    (hsech : ∀ (i₀ : I) (V : (DX.obj (Opposite.op i₀)).AffineEtale),
      LimitSetDirectImage.IsSectionsColimitAt (inverseImageSystem e F)
        (inverseImageLeg e F cY cT hcT x) i₀
        ((smallEtaleBaseChange (h.app (Opposite.op i₀))).obj ((AffineEtale.Spec _).obj V)))
    (hstage : ∀ i : Iᵒᵖ,
      IsIso ((smallEtaleSetBaseChange.{u, 0} (e.app i) (h.app i) (g.app i) (f.app i)
        (w i).symm).app (F.obj i)))
    (wL : limitMorphism e cY cT hcT ≫ limitMorphism g cT cS hcS =
      limitMorphism h cY cX hcX ≫ limitMorphism f cX cS hcS) :
    IsIso ((smallEtaleSetBaseChange.{u, 0} (limitMorphism e cY cT hcT)
      (limitMorphism h cY cX hcX) (limitMorphism g cT cS hcS) (limitMorphism f cX cS hcS)
      wL).app 𝓕) := by
  have hβ := LimitSetBaseChangeCube.homEquiv_smallEtaleSetBaseChange_app
    (limitMorphism e cY cT hcT) (limitMorphism h cY cX hcX) (limitMorphism g cT cS hcS)
    (limitMorphism f cX cS hcS) wL
    (limitMorphism e cY cT hcT ≫ limitMorphism g cT cS hcS) rfl
    (limit_comm f g h e w hcX hcS hcT) 𝓕
  refine isIso_of_coyoneda_map_bijective _ fun 𝒢 => ?_
  have key := existsUnique_limitTranspose_comp f g h e w hcX hcS hcT F x hdir hsecg hsech
    hstage 𝒢
  refine ⟨fun χ₁ χ₂ h₁₂ => ?_, fun φ => ?_⟩
  · have h' := congrArg ((setAdj (limitMorphism f cX cS hcS)).homEquiv _ _) h₁₂
    simp only [Adjunction.homEquiv_naturality_right, hβ] at h'
    exact (key _).unique rfl h'.symm
  · obtain ⟨χ, hχ, -⟩ := key ((setAdj (limitMorphism f cX cS hcS)).homEquiv _ _ φ)
    refine ⟨χ, ((setAdj (limitMorphism f cX cS hcS)).homEquiv _ _).injective ?_⟩
    simp only [Adjunction.homEquiv_naturality_right, hβ]
    exact hχ

end Core

section Main

variable {I : Type u} [Preorder I] [IsDirected I (· ≤ ·)] [Nonempty I]
  {DX DS DT DY : Iᵒᵖ ⥤ Scheme.{u}} (f : DX ⟶ DS) (g : DT ⟶ DS) (h : DY ⟶ DX)
  (e : DY ⟶ DT)
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DX.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DS.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DT.map a)]
  [∀ {i j : Iᵒᵖ} (a : i ⟶ j), IsAffineHom (DY.map a)]
  [∀ i : Iᵒᵖ, QuasiCompact (g.app i)] [∀ i : Iᵒᵖ, QuasiSeparated (g.app i)]
  {cX : Cone DX} {cS : Cone DS} {cT : Cone DT} {cY : Cone DY}
  (fL : cX.pt ⟶ cS.pt) (gL : cT.pt ⟶ cS.pt) (hL : cY.pt ⟶ cX.pt) (eL : cY.pt ⟶ cT.pt)

/-- **[Stacks, Tag 0EZT] (1): base change for the direct images of sheaves of sets passes to the
limit.** Let `I` be a directed set and let `(X_i ← Y_i, S_i ← T_i)` be an inverse system over `I`
of cartesian squares of schemes `h_i ≫ f_i = e_i ≫ g_i`, with affine transition morphisms and with
every `g_i` quasi-compact and quasi-separated. Let `X, S, T, Y` be the limits, with the limit
morphisms `f, g, h, e` characterised by `f ≫ s_i = r_i ≫ f_i`, `g ≫ s_i = p_i ≫ g_i`,
`h ≫ r_i = q_i ≫ h_i` and `e ≫ p_i = q_i ≫ e_i`. Let `(ℱ_i, φ_{i'i})` be a system of sheaves of
sets on `(T_i)` (Stacks 0EZL) and let `ℱ = colim p_i^{-1}ℱ_i` on `T`, presented by legs
`ι_i : p_i^{-1}ℱ_i ⟶ ℱ`. If for every `i` the base change map
`f_i^{-1}g_{i,*}ℱ_i ⟶ h_{i,*}e_i^{-1}ℱ_i` of sheaves of sets is an isomorphism, then so is the base
change map `f^{-1}g_*ℱ ⟶ h_*e^{-1}ℱ` of the limit square. -/
@[stacks 0EZT "conclusion (1), at the source's hypotheses: for an inverse system over a directed \
set of cartesian squares of schemes with affine transition morphisms and quasi-compact \
quasi-separated `g_i`, with limit square `(f, g, h, e)`, and a system of sheaves of sets `ℱ_i` on \
the `T_i` (Tag 0EZL) with `ℱ = colim p_i^{-1}ℱ_i`, if every base change map \
`f_i^{-1}g_{i,*}ℱ_i ⟶ h_{i,*}e_i^{-1}ℱ_i` of sheaves of sets \
(`Stacks.EtaleCohomology.smallEtaleSetBaseChange`) is an isomorphism then so is \
`f^{-1}g_*ℱ ⟶ h_*e^{-1}ℱ`. Together with \
`Stacks.EtaleCohomology.LimitBaseChange.isIso_higherBaseChangeMapAb_of_isLimit`, conclusion (2), \
this covers the tag."]
theorem isIso_smallEtaleSetBaseChange_of_isLimit
    (hsq : ∀ i : Iᵒᵖ, IsPullback (h.app i) (e.app i) (f.app i) (g.app i))
    (hcX : IsLimit cX) (hcS : IsLimit cS) (hcT : IsLimit cT) (hcY : IsLimit cY)
    (hfL : ∀ i : Iᵒᵖ, fL ≫ cS.π.app i = cX.π.app i ≫ f.app i)
    (hgL : ∀ i : Iᵒᵖ, gL ≫ cS.π.app i = cT.π.app i ≫ g.app i)
    (hhL : ∀ i : Iᵒᵖ, hL ≫ cX.π.app i = cY.π.app i ≫ h.app i)
    (heL : ∀ i : Iᵒᵖ, eL ≫ cT.π.app i = cY.π.app i ≫ e.app i)
    (𝓕 : Sheaf (smallEtaleTopology cT.pt) (Type (u + 1)))
    (F : EtaleSheafSystem DT (Type (u + 1)))
    (ι : ∀ i : Iᵒᵖ, (etalePullback (cT.π.app i) (Type (u + 1))).obj (F.obj i) ⟶ 𝓕)
    (hι : ∀ ⦃i j : Iᵒᵖ⦄ (a : i ⟶ j),
      (Adjunction.leftAdjointCompIso (systemAdjunction DT (Type (u + 1)) a)
          (etaleAdjunction (cT.π.app i) (Type (u + 1)))
          (etaleAdjunction (cT.π.app j) (Type (u + 1)))
          (coneProjectionComp (Type (u + 1)) cT a)).inv.app (F.obj j) ≫
        (etalePullback (cT.π.app i) (Type (u + 1))).map (F.map a) ≫ ι i = ι j)
    (hpres : IsSetPullbackColimitPresentation cT F 𝓕 ι)
    (hstage : ∀ i : Iᵒᵖ,
      IsIso ((smallEtaleSetBaseChange.{u, 0} (e.app i) (h.app i) (g.app i) (f.app i)
        (hsq i).w.symm).app (F.obj i))) :
    IsIso ((smallEtaleSetBaseChange.{u, 0} eL hL gL fL
      (LimitBaseChange.limitSquare_comm f g h e cX cS cT cY fL gL hL eL hcS hfL hgL hhL heL
        fun i => (hsq i).w).symm).app 𝓕) := by
  have uniq : ∀ {D₁ D₂ : Iᵒᵖ ⥤ Scheme.{u}} {c₁ : Cone D₁} {c₂ : Cone D₂} (hc : IsLimit c₂)
      (γ : D₁ ⟶ D₂) (L : c₁.pt ⟶ c₂.pt), (∀ i, L ≫ c₂.π.app i = c₁.π.app i ≫ γ.app i) →
      L = limitMorphism γ c₁ c₂ hc := fun hc γ L hL =>
    hc.hom_ext fun i => (hL i).trans (limitMorphism_comp_π γ _ _ hc i).symm
  obtain rfl := uniq hcS g gL hgL
  obtain rfl := uniq hcX h hL hhL
  obtain rfl := uniq hcS f fL hfL
  obtain rfl := uniq hcT e eL heL
  have : ∀ i : Iᵒᵖ, QuasiCompact (h.app i) := fun i =>
    MorphismProperty.of_isPullback (P := @QuasiCompact) (hsq i).flip inferInstance
  have : ∀ i : Iᵒᵖ, QuasiSeparated (h.app i) := fun i =>
    MorphismProperty.of_isPullback (P := @QuasiSeparated) (hsq i).flip inferInstance
  -- the commutativity of the levels, kept opaque: instantiating the core with a `fun` term
  -- makes the kernel unfold the base change maps when it compares the two statements
  have w : ∀ i : Iᵒᵖ, h.app i ≫ f.app i = e.app i ≫ g.app i := fun i => (hsq i).w
  -- the hypothesis on the levels, moved to the proof `w` by proof irrelevance through `Eq.mp`,
  -- so that the kernel never compares the two base change maps
  have hstage' : ∀ i : Iᵒᵖ, IsIso ((smallEtaleSetBaseChange.{u, 0} (e.app i) (h.app i) (g.app i)
      (f.app i) (w i).symm).app (F.obj i)) := fun i =>
    Eq.mp (congrArg (fun p : e.app i ≫ g.app i = h.app i ≫ f.app i =>
      IsIso ((smallEtaleSetBaseChange.{u, 0} (e.app i) (h.app i) (g.app i) (f.app i) p).app
        (F.obj i))) (rfl : (hsq i).w.symm = (w i).symm)) (hstage i)
  have hdir := isDirPresentation_of_isSetPullbackColimitPresentation cT F ι hι hpres
  generalize coneTranspose (Type (u + 1)) cT ι = x at hdir
  have hG := isDirPresentation_inverseImageSystem e F cY cT hcT x hdir
  exact isIso_smallEtaleSetBaseChange_limitMorphism f g h e w hcX hcS hcT F x hdir
    (fun i₀ V => by
      obtain ⟨h₁, h₂⟩ := LimitHigherDirectImage.qcqs_baseChange_affineEtale.{u, u} g i₀ V
      exact isSectionsColimitAt_of_presentation.{u, u} hcT F x hdir i₀ _)
    (fun i₀ V => by
      obtain ⟨h₁, h₂⟩ := LimitHigherDirectImage.qcqs_baseChange_affineEtale.{u, u} h i₀ V
      exact isSectionsColimitAt_of_presentation.{u, u} hcY (inverseImageSystem e F) _ hG i₀ _)
    hstage' _

end Main

end Stacks.EtaleCohomology.LimitSetBaseChange

end
