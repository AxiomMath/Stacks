module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.CompIsoIndependence

/-!
# Associativity of the composition isomorphisms of upper shriek functors

For morphisms `f : W ⟶ X`, `g : X ⟶ Y`, `h : Y ⟶ Z` of `FTS_S` over a Noetherian base and
arbitrary compactifications of the six morphisms involved, the two isomorphisms
`(h ∘ g ∘ f)^! ≅ f^! ∘ g^! ∘ h^!` on `D⁺_QCoh` built from the composition isomorphisms of
[Stacks, Tag 0ATX] agree ([Stacks, Tag 0ATY]).

Following the source, the compactifications are replaced, through
`Stacks.Duality.NestedCompactification.upperShriekCompIso_eq_compIsoVia`, by a tower
`X̄ ⊇ V ⊇ U ⊇ W` over `Ȳ ⊇ W' ⊇ X` over `Z̄ ⊇ Y`, built here from the given compactifications of
`h`, `g ≫ h` and `f ≫ g ≫ h` by scheme-theoretic closures of graphs. The comparison maps of the
rectangles `A + B`, `B + C`, `A` and `C` are pasted from the base change maps of the squares `A`,
`B`, `C`, and the associativity becomes the pasting identity `Stacks.Duality.upperShriek_tower`.

## Main results

* `Stacks.Duality.upperShriekFactorIso`: `k^! ≅ f^! ∘ g^!` for a factorization `f ≫ g = k`.
* `Stacks.Duality.upperShriekFactorIso_assoc`: the associativity of [Stacks, Tag 0ATY].
* `Stacks.Duality.upperShriekPlusIdIso`: the unit `(𝟙_X)^! ≅ 𝟭` at any compactification of `𝟙_X`.
* `Stacks.Duality.upperShriekCompIso_id_comp`, `Stacks.Duality.upperShriekCompIso_comp_id` and
  their factored forms `Stacks.Duality.upperShriekFactorIso_id_comp`,
  `Stacks.Duality.upperShriekFactorIso_comp_id`: the unit laws of [Stacks, Tag 0ATY]. The left
  one is computed through the nested compactification `Ȳ ⊇ X ⊇ X` of `𝟙_X` and `g`; the right one
  follows formally from the left one at `𝟙_X` and associativity.

## References

* [Stacks Project, Tag 0ATY](https://stacks.math.columbia.edu/tag/0ATY)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Duality

private lemma inv_comp_inv_of_hom_comp_hom {C : Type*} [Category C] {P Q R T : C} (a : P ≅ Q)
    (b : Q ≅ T) (c : P ≅ R) (d : R ≅ T) (h : a.hom ≫ b.hom = c.hom ≫ d.hom) :
    (𝟙 _ ≫ d.inv) ≫ c.inv = b.inv ≫ a.inv := by
  have h' : (a ≪≫ b).symm = (c ≪≫ d).symm := by
    rw [show a ≪≫ b = c ≪≫ d from Iso.ext h]
  simpa using congrArg Iso.hom h'.symm

section TowerPullback

variable {X U V Xb : Scheme.{u}} (uU : X ⟶ U) (vUV : U ⟶ V) (vV : V ⟶ Xb) {u : X ⟶ Xb}
  {vU : U ⟶ Xb} {uV : X ⟶ V} (hU : uU ≫ vU = u) (hV : uV ≫ vV = u) (hUV : uU ≫ vUV = uV)
  (hp : vUV ≫ vV = vU)

/-- The two identifications of `Lu^*` with `L(vV)^* ⋙ L(vUV)^* ⋙ L(uU)^*` for
`X ⊆ U ⊆ V ⊆ X̄` agree. -/
theorem quasiCoherentDerivedPullback_tower_coherence (K : quasiCoherentDerivedCategory Xb) :
    (quasiCoherentDerivedPullbackCongr hV.symm ≪≫
        (quasiCoherentDerivedPullbackCompIso uV vV).symm).hom.app K ≫
      (quasiCoherentDerivedPullbackCongr hUV.symm ≪≫
        (quasiCoherentDerivedPullbackCompIso uU vUV).symm).hom.app
        ((quasiCoherentDerivedPullback' vV).obj K) =
    (quasiCoherentDerivedPullbackCongr hU.symm ≪≫
        (quasiCoherentDerivedPullbackCompIso uU vU).symm).hom.app K ≫
      (quasiCoherentDerivedPullback' uU).map
        ((quasiCoherentDerivedPullbackCompIso vUV vV ≪≫
          quasiCoherentDerivedPullbackCongr hp).inv.app K) := by
  subst hp hUV hU
  have hA := quasiCoherentDerivedPullbackCompIso_assoc uU vUV vV K
  have e₁ : (quasiCoherentDerivedPullbackCongr hV.symm).hom.app K = 𝟙 _ := by
    apply ObjectProperty.hom_ext; rfl
  have e₂ : (quasiCoherentDerivedPullbackCongr (rfl : uU ≫ vUV = uU ≫ vUV).symm).hom.app
      ((quasiCoherentDerivedPullback' vV).obj K) = 𝟙 _ := by
    apply ObjectProperty.hom_ext; rfl
  have e₃ : (quasiCoherentDerivedPullbackCongr (rfl : uU ≫ vUV ≫ vV = uU ≫ vUV ≫ vV).symm).hom.app
      K = 𝟙 _ := by
    apply ObjectProperty.hom_ext; rfl
  have e₄ : (quasiCoherentDerivedPullbackCongr (rfl : vUV ≫ vV = vUV ≫ vV)).inv.app K = 𝟙 _ := by
    apply ObjectProperty.hom_ext; rfl
  simp only [Iso.trans_hom, Iso.trans_inv, Iso.symm_hom, NatTrans.comp_app, e₁, e₂, e₃, e₄,
    Category.id_comp]
  exact inv_comp_inv_of_hom_comp_hom ((quasiCoherentDerivedPullback' uU).mapIso
    ((quasiCoherentDerivedPullbackCompIso vUV vV).app K))
    ((quasiCoherentDerivedPullbackCompIso uU (vUV ≫ vV)).app K)
    ((quasiCoherentDerivedPullbackCompIso uU vUV).app _)
    ((quasiCoherentDerivedPullbackCompIso (uU ≫ vUV) vV).app K) hA

end TowerPullback

section TowerChase

private lemma comp_inv_hom_cancel {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ : C} (x : P₀ ⟶ P₁)
    (y : P₁ ⟶ P₂) (z : P₂ ⟶ P₃) (i : P₄ ≅ P₃) : (x ≫ y ≫ z ≫ i.inv) ≫ i.hom = x ≫ y ≫ z := by
  simp

private lemma reassoc_six_four {C : Type*} [Category C] {P₀ P₁ P₂ P₃ P₄ P₅ P₆ Q₁ Q₂ Q₃ : C}
    {a₁ : P₀ ⟶ P₁} {a₂ : P₁ ⟶ P₂} {a₃ : P₂ ⟶ P₃} {a₄ : P₃ ⟶ P₄} {a₅ : P₄ ⟶ P₅} {a₆ : P₅ ⟶ P₆}
    {b₁ : P₀ ⟶ Q₁} {b₂ : Q₁ ⟶ Q₂} {b₃ : Q₂ ⟶ Q₃} {b₄ : Q₃ ⟶ P₆}
    (H : a₁ ≫ a₂ ≫ a₃ ≫ a₄ ≫ a₅ ≫ a₆ = b₁ ≫ b₂ ≫ b₃ ≫ b₄) :
    (b₁ ≫ b₂ ≫ b₃) ≫ b₄ = (a₁ ≫ a₂ ≫ a₃) ≫ (a₄ ≫ a₅ ≫ a₆) := by
  simpa only [Category.assoc] using H.symm

private lemma tower_inner_chase {E EU EY EYb EV EW : Type*} [Category E] [Category EU]
    [Category EY] [Category EYb] [Category EV] [Category EW]
    (LvU : E ⥤ EU) (arU : EY ⥤ EU) (Lι : EYb ⥤ EY) (ap : EYb ⥤ E) (βAB : ap ⋙ LvU ⟶ Lι ⋙ arU)
    (LvV : E ⥤ EV) (LvA : EV ⥤ EU) (P' : LvU ≅ LvV ⋙ LvA) (LvW : EYb ⥤ EW) (arA : EW ⥤ EV)
    (βB : ap ⋙ LvV ⟶ LvW ⋙ arA) (LjW : EW ⥤ EY) (βA : arA ⋙ LvA ⟶ LjW ⋙ arU)
    (PC : Lι ≅ LvW ⋙ LjW) {x M : EYb} {N : EW} (a : x ⟶ M) (c : LvW.obj M ⟶ N)
    (HP : βAB.app M = P'.hom.app (ap.obj M) ≫ LvA.map (βB.app M) ≫ βA.app (LvW.obj M) ≫
      arU.map (PC.inv.app M)) :
    βAB.app x ≫ arU.map (Lι.map a ≫ PC.hom.app M ≫ LjW.map c) =
      LvU.map (ap.map a) ≫ P'.hom.app (ap.obj M) ≫ LvA.map (βB.app M) ≫ LvA.map (arA.map c) ≫
        βA.app N := by
  have n1 := βAB.naturality a
  have n2 := βA.naturality c
  simp only [Functor.comp_map] at n1 n2
  rw [Functor.map_comp, ← reassoc_of% n1, HP]
  simp only [Category.assoc]
  rw [← arU.map_comp, Iso.inv_hom_id_app_assoc, ← n2]

private lemma tower_outer_chase {C E EV EU : Type*} [Category C] [Category E] [Category EV]
    [Category EU] (Lu : E ⥤ C) (LvV : E ⥤ EV) (LuV : EV ⥤ C) (LvA : EV ⥤ EU) (LuU : EU ⥤ C)
    (LvU : E ⥤ EU) (PBC : Lu ≅ LvV ⋙ LuV) (PA : LuV ≅ LvA ⋙ LuU) (PAB : Lu ≅ LvU ⋙ LuU)
    (P' : LvU ≅ LvV ⋙ LvA)
    (Hcoh : ∀ x, PBC.hom.app x ≫ PA.hom.app (LvV.obj x) = PAB.hom.app x ≫ LuU.map (P'.hom.app x))
    {x₀ x₁ x₂ x₃ : E} {m₀ m : EV} {n : EV} {e e₃ : EU}
    {a₁ : x₀ ⟶ x₁} {a₂ : x₁ ⟶ x₂} {b₁ : x₀ ⟶ x₃} {b₂ : x₃ ⟶ x₂}
    {βBC : LvV.obj x₁ ⟶ m₀} {Am : m₀ ⟶ m} {βB : LvV.obj x₂ ⟶ n} {y : n ⟶ m}
    {βAz : LvA.obj m ⟶ e} {βAB : LvU.obj x₃ ⟶ e₃} {z : e₃ ⟶ e}
    (HV : βBC ≫ Am = LvV.map a₂ ≫ βB ≫ y)
    (Hz : βAB ≫ z = LvU.map b₂ ≫ P'.hom.app x₂ ≫ LvA.map βB ≫ LvA.map y ≫ βAz)
    (Hassoc : a₁ ≫ a₂ = b₁ ≫ b₂) :
    Lu.map a₁ ≫ PBC.hom.app x₁ ≫ LuV.map βBC ≫ LuV.map Am ≫ PA.hom.app m ≫ LuU.map βAz =
      Lu.map b₁ ≫ PAB.hom.app x₃ ≫ LuU.map βAB ≫ LuU.map z := by
  have n1 := PA.hom.naturality (βB ≫ y)
  have n4 := PAB.hom.naturality b₂
  have n5 := PBC.hom.naturality a₂
  have H := congrArg Lu.map Hassoc
  have Hc := Hcoh x₂
  simp only [Functor.comp_map, Functor.map_comp, Category.assoc] at n1 n4 n5 H Hc
  rw [← LuV.map_comp_assoc, HV, ← LuU.map_comp, Hz]
  simp only [Functor.map_comp, Category.assoc]
  rw [reassoc_of% n1, ← reassoc_of% n5, reassoc_of% Hc, ← reassoc_of% n4, reassoc_of% H]

end TowerChase

section TowerRaw

variable {X U V Xb Y W Yb Z Zb T : Scheme.{u}} [CompactSpace X] [QuasiSeparatedSpace X]
  [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace V] [QuasiSeparatedSpace V]
  [CompactSpace Xb] [QuasiSeparatedSpace Xb] [CompactSpace Y] [QuasiSeparatedSpace Y]
  [CompactSpace W] [QuasiSeparatedSpace W] [CompactSpace Yb] [QuasiSeparatedSpace Yb]
  [CompactSpace Z] [QuasiSeparatedSpace Z] [CompactSpace Zb] [QuasiSeparatedSpace Zb]
  [CompactSpace T] [QuasiSeparatedSpace T]
  {u : X ⟶ Xb} (uU : X ⟶ U) {vU : U ⟶ Xb} {uV : X ⟶ V} (vV : V ⟶ Xb) (vUV : U ⟶ V)
  (r : Xb ⟶ Yb) (rU : U ⟶ Y) (pV : V ⟶ W) {w : Y ⟶ Yb} (uW : Y ⟶ W) (vW : W ⟶ Yb)
  (rW : W ⟶ Z) (s : Yb ⟶ Zb) (j : Z ⟶ Zb) (q : Zb ⟶ T)
  [IsOpenImmersion w] [IsOpenImmersion vW] [IsOpenImmersion uW] [IsOpenImmersion j]
  (hU : uU ≫ vU = u) (hV : uV ≫ vV = u) (hUV : uU ≫ vUV = uV) (hp : vUV ≫ vV = vU)
  (hw : uW ≫ vW = w) (sqAB : IsPullback vU rU r w) (sqB : IsPullback vV pV r vW)
  (sqA : IsPullback vUV rU pV uW) (sqC : IsPullback vW rW s j)
  (sqBC : IsPullback vV (pV ≫ rW) (r ≫ s) j)

omit [CompactSpace X] [QuasiSeparatedSpace X] in
include hp sqB in
/-- **The tower identity behind [Stacks, Tag 0ATY]**, for `X ⊆ U ⊆ V ⊆ X̄` over
`Y ⊆ W ⊆ Ȳ` over `Z ⊆ Z̄` over `T`: the comparison of the rectangle `A + B` followed by that of
`C` is the comparison of `B + C` followed by that of `A`. -/
theorem upperShriek_tower (K : quasiCoherentDerivedCategory T) :
    ((quasiCoherentDerivedPullback' u).map
        ((twistedInverseImageCompIso r (s ≫ q)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
      (quasiCoherentDerivedPullbackCongr hU.symm ≪≫
        (quasiCoherentDerivedPullbackCompIso uU vU).symm).hom.app
        ((twistedInverseImage r (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          ((twistedInverseImage (s ≫ q)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) ≫
      (quasiCoherentDerivedPullback' uU).map
        ((openBaseChange vU rU r w sqAB).app ((twistedInverseImage (s ≫ q)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K))) ≫
    (quasiCoherentDerivedPullback' uU).map ((twistedInverseImage rU
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
      ((quasiCoherentDerivedPullback' w).map
          ((twistedInverseImageCompIso s q (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
        (quasiCoherentDerivedPullbackCongr hw.symm ≪≫
          (quasiCoherentDerivedPullbackCompIso uW vW).symm).hom.app
          ((twistedInverseImage s (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            ((twistedInverseImage q
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) ≫
        (quasiCoherentDerivedPullback' uW).map
          ((openBaseChange vW rW s j sqC).app ((twistedInverseImage q
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)))) =
    ((quasiCoherentDerivedPullback' u).map
        ((twistedInverseImageCompIso (r ≫ s) q
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K) ≫
      (quasiCoherentDerivedPullbackCongr hV.symm ≪≫
        (quasiCoherentDerivedPullbackCompIso uV vV).symm).hom.app
        ((twistedInverseImage (r ≫ s) (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          ((twistedInverseImage q (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) ≫
      (quasiCoherentDerivedPullback' uV).map
        ((openBaseChange vV (pV ≫ rW) (r ≫ s) j sqBC).app ((twistedInverseImage q
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K))) ≫
    ((quasiCoherentDerivedPullback' uV).map
        ((twistedInverseImageCompIso pV rW (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app
          ((quasiCoherentDerivedPullback' j).obj ((twistedInverseImage q
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K))) ≫
      (quasiCoherentDerivedPullbackCongr hUV.symm ≪≫
        (quasiCoherentDerivedPullbackCompIso uU vUV).symm).hom.app
        ((twistedInverseImage pV (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          ((twistedInverseImage rW (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            ((quasiCoherentDerivedPullback' j).obj ((twistedInverseImage q
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)))) ≫
      (quasiCoherentDerivedPullback' uU).map
        ((openBaseChange vUV rU pV uW sqA).app
          ((twistedInverseImage rW (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            ((quasiCoherentDerivedPullback' j).obj ((twistedInverseImage q
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K))))) := by
  have HP := openBaseChange_app_hpaste vV pV r vW vUV rU uW vU w sqB sqA sqAB hp hw
    ((twistedInverseImage s (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
      ((twistedInverseImage q (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K))
  have HV := openBaseChange_app_vpaste vV vW j r s pV rW sqB sqC sqBC
    ((twistedInverseImage q (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)
  have Hz := tower_inner_chase (quasiCoherentDerivedPullback' vU)
    (twistedInverseImage rU (isQuasicoherent_homology_derivedPushforward_of_qcqs _))
    (quasiCoherentDerivedPullback' w) (twistedInverseImage r
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)) (openBaseChange vU rU r w sqAB)
    (quasiCoherentDerivedPullback' vV) (quasiCoherentDerivedPullback' vUV)
    (quasiCoherentDerivedPullbackCompIso vUV vV ≪≫ quasiCoherentDerivedPullbackCongr hp).symm
    (quasiCoherentDerivedPullback' vW) (twistedInverseImage pV
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)) (openBaseChange vV pV r vW sqB)
    (quasiCoherentDerivedPullback' uW) (openBaseChange vUV rU pV uW sqA)
    (quasiCoherentDerivedPullbackCongr hw.symm ≪≫ (quasiCoherentDerivedPullbackCompIso uW vW).symm)
    ((twistedInverseImageCompIso s q (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K)
    ((openBaseChange vW rW s j sqC).app ((twistedInverseImage q
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) HP
  have HV' : (openBaseChange vV (pV ≫ rW) (r ≫ s) j sqBC).app
        ((twistedInverseImage q (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) ≫
      (twistedInverseImageCompIso pV rW (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app
        ((quasiCoherentDerivedPullback' j).obj ((twistedInverseImage q
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) =
      (quasiCoherentDerivedPullback' vV).map
          ((twistedInverseImageCompIso r s (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app ((twistedInverseImage q
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) ≫
        (openBaseChange vV pV r vW sqB).app
          ((twistedInverseImage s (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
            ((twistedInverseImage q
              (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) ≫
        (twistedInverseImage pV (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map
          ((openBaseChange vW rW s j sqC).app ((twistedInverseImage q
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)) := by
    rw [HV]
    exact comp_inv_hom_cancel _ _ _ ((twistedInverseImageCompIso pV rW
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).app
      ((quasiCoherentDerivedPullback' j).obj ((twistedInverseImage q
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K)))
  have H := tower_outer_chase (quasiCoherentDerivedPullback' u) (quasiCoherentDerivedPullback' vV)
    (quasiCoherentDerivedPullback' uV) (quasiCoherentDerivedPullback' vUV)
    (quasiCoherentDerivedPullback' uU) (quasiCoherentDerivedPullback' vU)
    (quasiCoherentDerivedPullbackCongr hV.symm ≪≫ (quasiCoherentDerivedPullbackCompIso uV vV).symm)
    (quasiCoherentDerivedPullbackCongr hUV.symm ≪≫
      (quasiCoherentDerivedPullbackCompIso uU vUV).symm)
    (quasiCoherentDerivedPullbackCongr hU.symm ≪≫ (quasiCoherentDerivedPullbackCompIso uU vU).symm)
    (quasiCoherentDerivedPullbackCompIso vUV vV ≪≫ quasiCoherentDerivedPullbackCongr hp).symm
    (fun x => quasiCoherentDerivedPullback_tower_coherence uU vUV vV hU hV hUV hp x)
    HV' Hz (twistedInverseImageCompIso_assoc_hom r s q K)
  exact reassoc_six_four H

end TowerRaw

namespace NestedCompactification

section TowerConstruction

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {X Y Z T : FTS S} (f : X ⟶ Y)
  (g : Y ⟶ Z) (h : Z ⟶ T) (ch : CompactificationOf (Over.mk h.left))
  (cgh : CompactificationOf (Over.mk (g ≫ h).left))
  (cfgh : CompactificationOf (Over.mk (f ≫ g ≫ h).left))

/-- The nested compactification `Ȳ ⊇ W ⊇ Y` over `Z̄` of the tower (the square `C`). -/
noncomputable abbrev towerC : NestedCompactification g h ch := ofCompCompactification g h ch cgh

/-- The nested compactification `X̄ ⊇ U ⊇ X` over `Ȳ` of the tower (the rectangle `A + B`). -/
noncomputable abbrev towerAB : NestedCompactification f (g ≫ h) (towerC g h ch cgh).compFG :=
  ofCompCompactification f (g ≫ h) (towerC g h ch cgh).compFG cfgh

/-- `W ⟶ Ȳ`, with `Ȳ` read as the compactification of `g ≫ h`. -/
noncomputable abbrev towerVW : (towerC g h ch cgh).Q ⟶ (towerC g h ch cgh).compFG.space :=
  (towerC g h ch cgh).v

/-- `Ȳ ⟶ Z̄`, with `Ȳ` read as the compactification of `g ≫ h`. -/
noncomputable abbrev towerRC : (towerC g h ch cgh).compFG.space ⟶ ch.space := (towerC g h ch cgh).r

/-- The morphism `W ⟶ Ȳ` of the tower is an open immersion. -/
instance : IsOpenImmersion (towerVW g h ch cgh) := (towerC g h ch cgh).isOpenImmersion_v

/-- The morphism `Ȳ ⟶ Z̄` of the tower is proper. -/
instance : IsProper (towerRC g h ch cgh) := (towerC g h ch cgh).isProper_r

/-- The square `C` of the tower, with `W` the inverse image of `Z` in `Ȳ`, is a pullback. -/
theorem isPullback_towerC :
    IsPullback (towerVW g h ch cgh) (towerC g h ch cgh).rQ (towerRC g h ch cgh) ch.immersion :=
  (towerC g h ch cgh).isPullback

/-- The composite `Y ⟶ W ⟶ Ȳ` is the open immersion of `Y` into the compactification `Ȳ` of
`g ≫ h`. -/
theorem towerC_uQ_v : (towerC g h ch cgh).uQ ≫ towerVW g h ch cgh =
    (towerC g h ch cgh).compFG.immersion := (towerC g h ch cgh).uQ_v

/-- The composite `X ⟶ X̄ ⟶ Ȳ ⟶ Z̄` is `X ⟶ Z ⟶ Z̄`, the composite of `f ≫ g` with the open
immersion of `Z`. -/
theorem towerBC_u_r : (towerAB f g h ch cgh cfgh).u ≫ (towerAB f g h ch cgh cfgh).r ≫
    towerRC g h ch cgh = (f ≫ g).left ≫ ch.immersion :=
  (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ towerRC g h ch cgh)
    (towerAB f g h ch cgh cfgh).u_r).trans ((Category.assoc _ _ _).trans
      (congrArg (f.left ≫ ·) (towerC g h ch cgh).u_r)))

/-- The composite `X ⟶ X̄ ⟶ Ȳ` agrees with `X ⟶ Y ⟶ W ⟶ Ȳ`. -/
theorem towerBC_lift_cond : (towerAB f g h ch cgh cfgh).u ≫ (towerAB f g h ch cgh cfgh).r =
    (f.left ≫ (towerC g h ch cgh).uQ) ≫ towerVW g h ch cgh := by
  rw [(towerAB f g h ch cgh cfgh).u_r, Category.assoc, towerC_uQ_v]

/-- The nested compactification `X̄ ⊇ V ⊇ X` over `Z̄` of the tower (the rectangle `B + C`):
`V` is the inverse image of `Z`. -/
noncomputable def towerBC : NestedCompactification (f ≫ g) h ch where
  R := (towerAB f g h ch cgh cfgh).R
  r := (towerAB f g h ch cgh cfgh).r ≫ towerRC g h ch cgh
  u := (towerAB f g h ch cgh cfgh).u
  u_r := towerBC_u_r f g h ch cgh cfgh
  Q := pullback (towerAB f g h ch cgh cfgh).r (towerVW g h ch cgh)
  v := pullback.fst _ _
  rQ := pullback.snd _ _ ≫ (towerC g h ch cgh).rQ
  isPullback := (IsPullback.of_hasPullback _ _).paste_vert (isPullback_towerC g h ch cgh)
  uQ := pullback.lift _ _ (towerBC_lift_cond f g h ch cgh cfgh)
  uQ_v := pullback.lift_fst _ _ _
  uQ_rQ := by
    rw [pullback.lift_snd_assoc, Category.assoc, (towerC g h ch cgh).uQ_rQ]; rfl

/-- The composite `U ⟶ X̄ ⟶ Ȳ` agrees with `U ⟶ Y ⟶ W ⟶ Ȳ`. -/
theorem towerA_lift_cond : (towerAB f g h ch cgh cfgh).v ≫ (towerAB f g h ch cgh cfgh).r =
    ((towerAB f g h ch cgh cfgh).rQ ≫ (towerC g h ch cgh).uQ) ≫ towerVW g h ch cgh := by
  rw [(towerAB f g h ch cgh cfgh).isPullback.w, Category.assoc, towerC_uQ_v]

/-- The open immersion `U ⟶ V` of the tower. -/
noncomputable abbrev towerUV : (towerAB f g h ch cgh cfgh).Q ⟶
    pullback (towerAB f g h ch cgh cfgh).r (towerVW g h ch cgh) :=
  pullback.lift _ _ (towerA_lift_cond f g h ch cgh cfgh)

/-- The composite `U ⟶ V ⟶ X̄` is the open immersion `U ⟶ X̄`. -/
theorem towerUV_v : towerUV f g h ch cgh cfgh ≫ pullback.fst _ _ =
    (towerAB f g h ch cgh cfgh).v := pullback.lift_fst _ _ _

/-- The square `A` of the tower, with `U` the inverse image of `Y` in `V`, is a pullback. -/
theorem isPullback_towerA : IsPullback (towerUV f g h ch cgh cfgh) (towerAB f g h ch cgh cfgh).rQ
    (pullback.snd (towerAB f g h ch cgh cfgh).r (towerVW g h ch cgh)) (towerC g h ch cgh).uQ := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback _ _)
  rw [pullback.lift_fst, towerC_uQ_v]
  exact (towerAB f g h ch cgh cfgh).isPullback

/-- The composite `X ⟶ U ⟶ V` is the open immersion of `X` into `V`. -/
theorem towerA_uQ_v : (towerAB f g h ch cgh cfgh).uQ ≫ towerUV f g h ch cgh cfgh =
    pullback.lift _ _ (towerBC_lift_cond f g h ch cgh cfgh) := by
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, (towerAB f g h ch cgh cfgh).uQ_v]
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, ← Category.assoc,
      (towerAB f g h ch cgh cfgh).uQ_rQ]

/-- The nested compactification `V ⊇ U ⊇ X` over `W` of the tower (the square `A`). -/
noncomputable def towerA : NestedCompactification f g (towerC g h ch cgh).compF where
  R := pullback (towerAB f g h ch cgh cfgh).r (towerVW g h ch cgh)
  r := pullback.snd _ _
  isProper_r :=
    haveI : IsProper (X := (towerAB f g h ch cgh cfgh).R)
      (Y := (towerC g h ch cgh).compFG.space) (towerAB f g h ch cgh cfgh).r :=
      (towerAB f g h ch cgh cfgh).isProper_r
    (inferInstance : IsProper (pullback.snd (towerAB f g h ch cgh cfgh).r (towerVW g h ch cgh)))
  u := pullback.lift _ _ (towerBC_lift_cond f g h ch cgh cfgh)
  isOpenImmersion_u := by
    have : IsOpenImmersion (pullback.lift _ _ (towerBC_lift_cond f g h ch cgh cfgh) ≫
        pullback.fst (towerAB f g h ch cgh cfgh).r (towerVW g h ch cgh)) := by
      rw [pullback.lift_fst]; infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.fst (towerAB f g h ch cgh cfgh).r
      (towerVW g h ch cgh))
  u_r := pullback.lift_snd _ _ _
  Q := (towerAB f g h ch cgh cfgh).Q
  v := towerUV f g h ch cgh cfgh
  isOpenImmersion_v := by
    have : IsOpenImmersion (towerUV f g h ch cgh cfgh ≫
        pullback.fst (towerAB f g h ch cgh cfgh).r (towerVW g h ch cgh)) := by
      rw [towerUV_v]; infer_instance
    exact IsOpenImmersion.of_comp _ (pullback.fst (towerAB f g h ch cgh cfgh).r
      (towerVW g h ch cgh))
  rQ := (towerAB f g h ch cgh cfgh).rQ
  isPullback := isPullback_towerA f g h ch cgh cfgh
  uQ := (towerAB f g h ch cgh cfgh).uQ
  uQ_v := towerA_uQ_v f g h ch cgh cfgh
  uQ_rQ := (towerAB f g h ch cgh cfgh).uQ_rQ

/-- **The comparisons of the tower satisfy the associativity of [Stacks, Tag 0ATY]**: for the
compactifications `X̄ ⊇ V ⊇ U ⊇ X` over `Ȳ ⊇ W ⊇ Y` over `Z̄ ⊇ Z`, the comparison of `B + C`
followed by that of `A` is the comparison of `A + B` followed by `f^!` of that of `C`. -/
theorem compHom_tower (K : quasiCoherentDerivedCategory T.left) :
    (towerBC f g h ch cgh cfgh).compHom.app K ≫
        (towerA f g h ch cgh cfgh).compHom.app ((upperShriek h ch).obj K) =
      (towerAB f g h ch cgh cfgh).compHom.app K ≫
        (upperShriek f (towerAB f g h ch cgh cfgh).compF).map
          ((towerC g h ch cgh).compHom.app K) := by
  rw [compHom_app, compHom_app, compHom_app, compHom_app]
  have : CompactSpace ↥(pullback (towerAB f g h ch cgh cfgh).r (towerVW g h ch cgh) : Scheme.{u}) :=
    (inferInstance : CompactSpace (towerA f g h ch cgh cfgh).R)
  have : QuasiSeparatedSpace
      ↥(pullback (towerAB f g h ch cgh cfgh).r (towerVW g h ch cgh) : Scheme.{u}) :=
    (inferInstance : QuasiSeparatedSpace (towerA f g h ch cgh cfgh).R)
  exact (upperShriek_tower (towerAB f g h ch cgh cfgh).uQ (pullback.fst _ _)
    (towerUV f g h ch cgh cfgh) (towerAB f g h ch cgh cfgh).r (towerAB f g h ch cgh cfgh).rQ
    (pullback.snd _ _) (towerC g h ch cgh).uQ (towerVW g h ch cgh) (towerC g h ch cgh).rQ
    (towerRC g h ch cgh) ch.immersion ch.toBase (towerAB f g h ch cgh cfgh).uQ_v
    (pullback.lift_fst _ _ _) (towerA_uQ_v f g h ch cgh cfgh) (towerUV_v f g h ch cgh cfgh)
    (towerC_uQ_v g h ch cgh) (towerAB f g h ch cgh cfgh).isPullback (IsPullback.of_hasPullback _ _)
    (isPullback_towerA f g h ch cgh cfgh) (isPullback_towerC g h ch cgh)
    (towerBC f g h ch cgh cfgh).isPullback K).symm

section Assoc

variable [IsNoetherian S]

/-- The component at `K` of `compIsoVia cf cg cfg N` is the composite of the comparisons of
`cfg` with `N.compFG`, the comparison `N.compHom` of `N`, the comparison of `N.compF` with `cf`,
and `f^!` of the comparison of `c` with `cg`. -/
theorem compIsoVia_hom_app_hom {X Y Z : FTS S} {f : X ⟶ Y} {g : Y ⟶ Z}
    (cf : CompactificationOf (Over.mk f.left)) (cg : CompactificationOf (Over.mk g.left))
    (cfg : CompactificationOf (Over.mk (f ≫ g).left)) {c : CompactificationOf (Over.mk g.left)}
    (N : NestedCompactification f g c) (K : quasiCoherentDerivedCategoryPlusOfModel Z.left) :
    ((compIsoVia cf cg cfg N).hom.app K).hom =
      ((DominatingCompactification.upperShriekPlusIso (f ≫ g) cfg N.compFG).hom.app K).hom ≫
        N.compHom.app K.obj ≫
        ((DominatingCompactification.upperShriekPlusIso f N.compF cf).hom.app
          ((upperShriekPlus g c).obj K)).hom ≫
        (upperShriek f cf).map
          ((DominatingCompactification.upperShriekPlusIso g c cg).hom.app K).hom :=
  rfl

omit [CompactSpace S] [QuasiSeparatedSpace S] [AlgebraicGeometry.IsNoetherian S] in
private lemma assoc_chase {C D D₁ E : Type*} [Category C] [Category D] [Category D₁] [Category E]
    (F : D ⥤ C) (G₁ : D₁ ⥤ C) (G₂ : E ⥤ D)
    {P₀ P₁ P₂ P₄ Q₂ : C} {M₀ M₁ M₂ : D} {N₁ : D₁} {N₂ : E}
    {d₀ d₀' : P₀ ⟶ P₁} {bc : P₁ ⟶ P₂} {dV : P₂ ⟶ G₁.obj N₁} {dV' : G₁.obj N₁ ⟶ P₂}
    {a : P₂ ⟶ P₄} {dU : P₄ ⟶ F.obj M₂} {dW : M₂ ⟶ G₂.obj N₂} {ab : P₁ ⟶ Q₂}
    {dU' : Q₂ ⟶ F.obj M₀} {dY : M₀ ⟶ M₁} {dY' : M₁ ⟶ M₀} {cm : M₀ ⟶ M₂} {fc : Q₂ ⟶ P₄}
    (hV : dV ≫ dV' = 𝟙 _) (hY : dY ≫ dY' = 𝟙 _)
    (hN : fc ≫ dU = dU' ≫ F.map cm) (hT : bc ≫ a = ab ≫ fc) (hd : d₀' = d₀) :
    (d₀ ≫ bc ≫ dV ≫ G₁.map (𝟙 N₁)) ≫ (dV' ≫ a ≫ dU ≫ F.map dW) =
      (d₀' ≫ ab ≫ dU' ≫ F.map dY) ≫ F.map (dY' ≫ cm ≫ dW ≫ G₂.map (𝟙 N₂)) := by
  subst hd
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc, Functor.map_comp]
  rw [reassoc_of% hV, ← F.map_comp_assoc, hY, CategoryTheory.Functor.map_id, Category.id_comp,
    reassoc_of% hT, reassoc_of% hN]

end Assoc

end TowerConstruction

end NestedCompactification

section UpperShriekAssoc

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] [IsNoetherian S]

/-- **The composition isomorphism `k^! ≅ f^! ∘ g^!` of a factorization `k = g ∘ f`** on
`D⁺_QCoh`, for arbitrary compactifications of `f`, `g` and `k` (the isomorphism of
[Stacks, Tag 0ATX] read through `e : f ≫ g = k`). -/
noncomputable def upperShriekFactorIso {X Y Z : FTS S} {f : X ⟶ Y} {g : Y ⟶ Z} {k : X ⟶ Z}
    (e : f ≫ g = k) (cf : CompactificationOf (Over.mk f.left))
    (cg : CompactificationOf (Over.mk g.left)) (ck : CompactificationOf (Over.mk k.left)) :
    upperShriekPlus k ck ≅ upperShriekPlus g cg ⋙ upperShriekPlus f cf := by
  subst e
  exact upperShriekCompIso f g cf cg ck

/-- For the factorization `f ≫ g = f ≫ g` by `rfl`, `upperShriekFactorIso` is
`upperShriekCompIso f g cf cg ck`. -/
theorem upperShriekFactorIso_rfl {X Y Z : FTS S} (f : X ⟶ Y) (g : Y ⟶ Z)
    (cf : CompactificationOf (Over.mk f.left)) (cg : CompactificationOf (Over.mk g.left))
    (ck : CompactificationOf (Over.mk (f ≫ g).left)) :
    upperShriekFactorIso rfl cf cg ck = upperShriekCompIso f g cf cg ck := rfl

omit [CompactSpace S] [QuasiSeparatedSpace S] [AlgebraicGeometry.IsNoetherian S] in
private lemma hom_comp_hom_eq_id {C D : Type*} [Category C] [Category D] {P : ObjectProperty D}
    {A B : C ⥤ P.FullSubcategory} (α : A ≅ B) (β : B ≅ A) (h : α ≪≫ β = Iso.refl _)
    (K : C) : (α.hom.app K).hom ≫ (β.hom.app K).hom = 𝟙 _ := by
  simpa using congrArg (fun i => (i.hom.app K).hom) h

/-- **[Stacks, Tag 0ATY]: the upper shriek functors form a pseudofunctor**, the associativity:
for `k = h ∘ g ∘ f` in `FTS_S` over a Noetherian base and arbitrary compactifications of the six
morphisms, splitting off `f` first and splitting off `h` first give the same isomorphism
`k^! ≅ f^! ∘ g^! ∘ h^!` on `D⁺_QCoh`. -/
theorem upperShriekFactorIso_assoc {W X Y Z : FTS S} {f : W ⟶ X} {g : X ⟶ Y} {h : Y ⟶ Z}
    {fg : W ⟶ Y} {gh : X ⟶ Z} {k : W ⟶ Z} (efg : f ≫ g = fg) (egh : g ≫ h = gh)
    (ek : fg ≫ h = k) (ek' : f ≫ gh = k) (cf : CompactificationOf (Over.mk f.left))
    (cg : CompactificationOf (Over.mk g.left)) (ch : CompactificationOf (Over.mk h.left))
    (cfg : CompactificationOf (Over.mk fg.left)) (cgh : CompactificationOf (Over.mk gh.left))
    (ck : CompactificationOf (Over.mk k.left))
    (K : quasiCoherentDerivedCategoryPlusOfModel Z.left) :
    (upperShriekFactorIso ek' cf cgh ck).hom.app K ≫
        (upperShriekPlus f cf).map ((upperShriekFactorIso egh cg ch cgh).hom.app K) =
      (upperShriekFactorIso ek cfg ch ck).hom.app K ≫
        (upperShriekFactorIso efg cf cg cfg).hom.app ((upperShriekPlus h ch).obj K) := by
  subst efg egh ek
  apply ObjectProperty.hom_ext
  show ((upperShriekCompIso f (g ≫ h) cf cgh ck).hom.app K).hom ≫
      (upperShriek f cf).map ((upperShriekCompIso g h cg ch cgh).hom.app K).hom =
    ((upperShriekCompIso (f ≫ g) h cfg ch ck).hom.app K).hom ≫
      ((upperShriekCompIso f g cf cg cfg).hom.app ((upperShriekPlus h ch).obj K)).hom
  rw [NestedCompactification.upperShriekCompIso_eq_compIsoVia cf cgh ck
      (NestedCompactification.towerAB f g h ch cgh ck),
    NestedCompactification.upperShriekCompIso_eq_compIsoVia cg ch cgh
      (NestedCompactification.towerC g h ch cgh),
    NestedCompactification.upperShriekCompIso_eq_compIsoVia cfg ch ck
      (NestedCompactification.towerBC f g h ch cgh ck),
    NestedCompactification.upperShriekCompIso_eq_compIsoVia cf cg cfg
      (NestedCompactification.towerA f g h ch cgh ck),
    NestedCompactification.compIsoVia_hom_app_hom cf cgh ck
      (NestedCompactification.towerAB f g h ch cgh ck) K,
    NestedCompactification.compIsoVia_hom_app_hom, NestedCompactification.compIsoVia_hom_app_hom,
    NestedCompactification.compIsoVia_hom_app_hom, upperShriekPlusIso_refl]
  simp only [Iso.refl_hom, NatTrans.id_app, ObjectProperty.FullSubcategory.id_hom]
  have hdi : DominatingCompactification.upperShriekPlusIso (f ≫ g ≫ h) ck
      (NestedCompactification.towerAB f g h ch cgh ck).compFG =
    DominatingCompactification.upperShriekPlusIso ((f ≫ g) ≫ h) ck
      (NestedCompactification.towerBC f g h ch cgh ck).compFG := rfl
  have hT := NestedCompactification.compHom_tower f g h ch cgh ck K.obj
  have hN := (DominatingCompactification.upperShriekPlusIso f
    (NestedCompactification.towerAB f g h ch cgh ck).compF cf).hom.naturality
      ((NestedCompactification.towerC g h ch cgh).compPlusIso.hom.app K)
  have hN' := congrArg (fun x => x.hom) hN
  simp only [ObjectProperty.FullSubcategory.comp_hom] at hN'
  have eV : DominatingCompactification.upperShriekPlusIso (f ≫ g)
      (NestedCompactification.towerBC f g h ch cgh ck).compF cfg ≪≫
      DominatingCompactification.upperShriekPlusIso (f ≫ g) cfg
        (NestedCompactification.towerA f g h ch cgh ck).compFG = Iso.refl _ :=
    (upperShriekPlusIso_trans _ _ _ _).trans (upperShriekPlusIso_refl _ _)
  have hV := hom_comp_hom_eq_id _ _ eV ((upperShriekPlus h ch).obj K)
  have eY : DominatingCompactification.upperShriekPlusIso (g ≫ h)
      (NestedCompactification.towerC g h ch cgh).compFG cgh ≪≫
      DominatingCompactification.upperShriekPlusIso (g ≫ h) cgh
        (NestedCompactification.towerC g h ch cgh).compFG = Iso.refl _ :=
    (upperShriekPlusIso_trans _ _ _ _).trans (upperShriekPlusIso_refl _ _)
  have hY := hom_comp_hom_eq_id _ _ eY K
  have hd := congrArg (fun i => (i.hom.app K).hom) hdi
  have hN'' : (upperShriek f (NestedCompactification.towerAB f g h ch cgh ck).compF).map
        ((NestedCompactification.towerC g h ch cgh).compHom.app K.obj) ≫
      ((DominatingCompactification.upperShriekPlusIso f
        (NestedCompactification.towerAB f g h ch cgh ck).compF cf).hom.app
          ((upperShriekPlus h ch ⋙ upperShriekPlus g
            (NestedCompactification.towerC g h ch cgh).compF).obj K)).hom =
      ((DominatingCompactification.upperShriekPlusIso f
        (NestedCompactification.towerAB f g h ch cgh ck).compF cf).hom.app
          ((upperShriekPlus (g ≫ h) (NestedCompactification.towerC g h ch cgh).compFG).obj K)).hom ≫
        (upperShriek f cf).map ((NestedCompactification.towerC g h ch cgh).compHom.app K.obj) :=
    hN'
  exact (NestedCompactification.assoc_chase (upperShriek f cf) (upperShriek (f ≫ g) cfg)
    (upperShriek g cg) hV hY hN'' hT hd).symm

end UpperShriekAssoc

/-! ### The unit coherence -/

section Unit

private lemma comp_eq_id_of_eqToHom {C : Type*} [Category C] {P : ObjectProperty C}
    {x y z : P.FullSubcategory} (c : x ⟶ y) (i : y ⟶ z) (ι : z ⟶ x) {p₁ : x.obj = y.obj}
    {p₂ : y.obj = x.obj} (h₁ : c.hom = eqToHom p₁) (h₂ : (i ≫ ι).hom = eqToHom p₂) :
    (c ≫ i) ≫ ι = 𝟙 x := by
  apply ObjectProperty.hom_ext
  rw [Category.assoc, ObjectProperty.FullSubcategory.comp_hom, h₁, h₂]
  simp

private lemma unit_chase {C D : Type*} [Category C] [Category D] (L : D ⥤ C) {d₀ d₁ : D}
    {O₂ O₃ O₄ O₅ : C} {a : d₀ ⟶ d₁} {c : d₀ ⟶ d₀} {P : L.obj d₁ ⟶ O₂} {Lb : O₂ ⟶ O₃}
    {ιL' : O₃ ⟶ O₄} {ιL : O₂ ⟶ L.obj d₁} {β : L.obj d₁ ⟶ O₄} {ιa : O₄ ⟶ O₅}
    (hn : Lb ≫ ιL' = ιL ≫ β) (hp : P ≫ ιL = 𝟙 _) (hc : c = 𝟙 _) :
    (L.map a ≫ P ≫ Lb) ≫ ιL' ≫ ιa = L.map (c ≫ a) ≫ β ≫ ιa := by
  subst hc
  simp only [Category.id_comp, Category.assoc]
  rw [reassoc_of% hn, reassoc_of% hp]

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S]

/-- `(𝟙_X)^! = a_{𝟙} ⋙ L𝟙^* ≅ 𝟭` at the identity compactification. -/
noncomputable def upperShriekIdIsoProper (X : FTS S) :
    upperShriek (𝟙 X) (properCompactification (𝟙 X)) ≅ 𝟭 _ :=
  NatIso.ofComponents
    (fun K => (quasiCoherentDerivedPullbackIdIsoOfComp X.left).app
        ((twistedInverseImage (𝟙 X.left)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) ≪≫
      (twistedInverseImageIdIsoOfComp X.left).app K)
    (fun {K L} φ => by
      have h₁ := (quasiCoherentDerivedPullbackIdIsoOfComp X.left).hom.naturality
        ((twistedInverseImage (𝟙 X.left)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map φ)
      have h₂ := (twistedInverseImageIdIsoOfComp X.left).hom.naturality φ
      change (quasiCoherentDerivedPullback' (𝟙 X.left)).map ((twistedInverseImage (𝟙 X.left)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).map φ) ≫
          ((quasiCoherentDerivedPullbackIdIsoOfComp X.left).hom.app _ ≫
            (twistedInverseImageIdIsoOfComp X.left).hom.app L) =
        ((quasiCoherentDerivedPullbackIdIsoOfComp X.left).hom.app _ ≫
            (twistedInverseImageIdIsoOfComp X.left).hom.app K) ≫ φ
      rw [← Category.assoc, h₁, Category.assoc, Category.assoc]
      exact congrArg (_ ≫ ·) h₂)

/-- The component at `K` of `upperShriekIdIsoProper X` is the composite of
`L𝟙^* ≅ 𝟭` at `a_{𝟙} K` with `a_{𝟙} ≅ 𝟭` at `K`. -/
theorem upperShriekIdIsoProper_hom_app (X : FTS S) (K : quasiCoherentDerivedCategory X.left) :
    (upperShriekIdIsoProper X).hom.app K =
      (quasiCoherentDerivedPullbackIdIsoOfComp X.left).hom.app
          ((twistedInverseImage (𝟙 X.left)
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K) ≫
        (twistedInverseImageIdIsoOfComp X.left).hom.app K :=
  rfl

namespace NestedCompactification

variable {X Y : FTS S}

/-- The nested compactification of `𝟙_X` and `g` over a compactification `Ȳ` of `g`:
`R = Ȳ` over itself and `Q = X`. -/
noncomputable def idComp (g : X ⟶ Y) (cg : CompactificationOf (Over.mk g.left)) :
    NestedCompactification (𝟙 X) g cg where
  R := cg.space
  r := 𝟙 _
  u := cg.immersion
  u_r := by simp
  Q := X.left
  v := cg.immersion
  rQ := 𝟙 _
  isPullback := IsPullback.id_vert cg.immersion
  uQ := 𝟙 _
  uQ_v := Category.id_comp _
  uQ_rQ := rfl

end NestedCompactification

/-- The comparison of the nested compactification `NestedCompactification.idComp`, followed by
`(𝟙_X)^! ≅ 𝟭`, is the map `α_{𝟙}` of the identity of `Ȳ`. -/
theorem compHom_idComp_app {X Y : FTS S} (g : X ⟶ Y) (cg : CompactificationOf (Over.mk g.left))
    (K : quasiCoherentDerivedCategory Y.left) :
    (NestedCompactification.idComp g cg).compHom.app K ≫
        (upperShriekIdIsoProper X).hom.app ((upperShriek g cg).obj K) =
      (upperShriekCompactificationMap g (NestedCompactification.idComp g cg).compFG cg (𝟙 _)
        (Category.id_comp _) (IsPullback.id_vert cg.immersion)).app K := by
  have F1 := NestedCompactification.compHom_app (NestedCompactification.idComp g cg) K
  have F2 := upperShriekCompactificationMap_app_eq_openBaseChange g
    (NestedCompactification.idComp g cg).compFG cg (𝟙 _) (Category.id_comp _)
    (IsPullback.id_vert cg.immersion) K
  have F3 := upperShriekIdIsoProper_hom_app X ((upperShriek g cg).obj K)
  have F4 := (quasiCoherentDerivedPullbackIdIsoOfComp X.left).hom.naturality
    ((openBaseChange cg.immersion (𝟙 X.left) (𝟙 cg.space) cg.immersion
      (IsPullback.id_vert cg.immersion)).app
        ((twistedInverseImage cg.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          K))
  have F5 := comp_eq_id_of_eqToHom
    ((quasiCoherentDerivedPullbackCongr (NestedCompactification.idComp g cg).uQ_v.symm).hom.app
      ((twistedInverseImage (𝟙 cg.space)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
        ((twistedInverseImage cg.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          K)))
    ((quasiCoherentDerivedPullbackCompIso (𝟙 X.left) cg.immersion).inv.app
      ((twistedInverseImage (𝟙 cg.space)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
        ((twistedInverseImage cg.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          K)))
    ((quasiCoherentDerivedPullbackIdIsoOfComp X.left).hom.app
      ((quasiCoherentDerivedPullback' cg.immersion).obj
        ((twistedInverseImage (𝟙 cg.space)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj
          ((twistedInverseImage cg.toBase
            (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K))))
    (p₁ := rfl) rfl (quasiCoherentDerivedPullbackCompIso_inv_app_comp_idIsoOfComp cg.immersion _)
  have F6 : (twistedInverseImageCongr (Category.id_comp cg.toBase).symm
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).hom.app K = 𝟙 _ := rfl
  refine (congrArg₂ (· ≫ ·) F1 F3).trans (Eq.trans ?_ F2.symm)
  exact unit_chase _ F4 F5 F6

private lemma left_unit_chase {C : Type*} [Category C] (F : C ⥤ C) {O₀ O₁ O₂ O₄ O₅ : C}
    {d₁ : O₀ ⟶ O₁} {c : O₁ ⟶ O₂} {d₂ : O₂ ⟶ F.obj O₅} {m : O₅ ⟶ O₅} {d₃ : F.obj O₅ ⟶ O₄}
    {e : O₄ ⟶ O₅} {α : O₁ ⟶ O₅} {t : O₂ ⟶ O₄} (hm : m = 𝟙 _) (h₂₃ : d₂ ≫ d₃ = t)
    (h : c ≫ t ≫ e = α) :
    (d₁ ≫ c ≫ d₂ ≫ F.map m) ≫ d₃ ≫ e = d₁ ≫ α := by
  subst hm h
  simp only [CategoryTheory.Functor.map_id, Category.comp_id, Category.assoc]
  rw [reassoc_of% h₂₃]

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The right unit law of a pseudofunctor follows from the left unit law at the identity and
associativity: if `F ≅ E ⋙ F` and `E ≅ E ⋙ E` are compatible as below and `E ≅ 𝟭` splits the
latter, it also splits the former. -/
private lemma right_unit_formal {C D : Type*} [Category C] [Category D] (F : C ⥤ D) (E : C ⥤ C)
    (ε : E ≅ 𝟭 C) (γ : F ≅ E ⋙ F) (δ : E ≅ E ⋙ E)
    (hA : ∀ K, F.map (δ.hom.app K) = γ.hom.app (E.obj K))
    (hL : ∀ K, δ.hom.app K ≫ ε.hom.app (E.obj K) = 𝟙 _) (K : C) :
    γ.hom.app K ≫ F.map (ε.hom.app K) = 𝟙 _ := by
  have h₁ : ε.hom.app (E.obj K) = E.map (ε.hom.app K) := by
    have h := ε.hom.naturality (ε.hom.app K)
    simp only [Functor.id_obj, Functor.id_map] at h
    exact ((cancel_mono (ε.hom.app K)).1 h).symm
  have h₂ : γ.hom.app (E.obj K) ≫ F.map (ε.hom.app (E.obj K)) = 𝟙 _ := by
    rw [← hA, ← F.map_comp, hL, F.map_id]
  have h₃ := γ.hom.naturality (ε.hom.app K)
  simp only [Functor.comp_map, Functor.id_obj] at h₃
  rw [← cancel_epi (F.map (ε.hom.app K)), ← Category.assoc, h₃, Category.assoc, ← F.map_comp,
    ← h₁, F.map_comp, ← Category.assoc, h₂, Category.id_comp]
  exact (Category.comp_id _).symm

variable [AlgebraicGeometry.IsNoetherian S]

/-- `(𝟙_X)^! ≅ 𝟭` on `D⁺_QCoh` at the identity compactification. -/
noncomputable def upperShriekPlusIdIsoProper (X : FTS S) :
    upperShriekPlus (𝟙 X) (properCompactification (𝟙 X)) ≅ 𝟭 _ :=
  @isoOfNatTransι _ _ _ _ _ (upperShriekPlus (𝟙 X) (properCompactification (𝟙 X))) (𝟭 _)
    (Functor.whiskerLeft (ObjectProperty.ι _) (upperShriekIdIsoProper X).hom)
    (fun K => inferInstanceAs (IsIso ((upperShriekIdIsoProper X).hom.app K.obj)))

omit [AlgebraicGeometry.IsNoetherian S] in
/-- The underlying morphism of the component at `K` of `upperShriekPlusIdIsoProper X` is the
component of `upperShriekIdIsoProper X` at the underlying complex of `K`. -/
theorem upperShriekPlusIdIsoProper_hom_app_hom (X : FTS S)
    (K : quasiCoherentDerivedCategoryPlusOfModel X.left) :
    ((upperShriekPlusIdIsoProper X).hom.app K).hom = (upperShriekIdIsoProper X).hom.app K.obj :=
  rfl

/-- **The unit `(𝟙_X)^! ≅ 𝟭` on `D⁺_QCoh`** at an arbitrary compactification `c` of `𝟙_X`:
`(𝟙_X)^!_c ≅ (𝟙_X)^!_X` ([Stacks, Tag 0AA0]) followed by `a_{𝟙} ⋙ L𝟙^* ≅ 𝟭`. -/
noncomputable def upperShriekPlusIdIso (X : FTS S)
    (c : CompactificationOf (Over.mk (𝟙 X : X ⟶ X).left)) :
    upperShriekPlus (𝟙 X) c ≅ 𝟭 _ :=
  DominatingCompactification.upperShriekPlusIso (𝟙 X) c (properCompactification (𝟙 X)) ≪≫
    upperShriekPlusIdIsoProper X

/-- **The left unit law of [Stacks, Tag 0ATY]**: for `g : X ⟶ Y` and arbitrary compactifications
of `𝟙_X`, `g` and `𝟙_X ≫ g = g`, the composition isomorphism `(𝟙 ≫ g)^! ≅ 𝟙^! ∘ g^!` followed by
the unit `𝟙^! ≅ 𝟭` is the isomorphism of [Stacks, Tag 0AA0] between the two compactifications
of `g`. -/
theorem upperShriekCompIso_id_comp {X Y : FTS S} (g : X ⟶ Y)
    (c₁ : CompactificationOf (Over.mk (𝟙 X : X ⟶ X).left))
    (cg : CompactificationOf (Over.mk g.left)) (ck : CompactificationOf (Over.mk (𝟙 X ≫ g).left))
    (K : quasiCoherentDerivedCategoryPlusOfModel Y.left) :
    (upperShriekCompIso (𝟙 X) g c₁ cg ck).hom.app K ≫
        (upperShriekPlusIdIso X c₁).hom.app ((upperShriekPlus g cg).obj K) =
      (DominatingCompactification.upperShriekPlusIso g ck cg).hom.app K := by
  have : IsProper (X := (NestedCompactification.idComp g cg).compFG.space) (𝟙 cg.space) :=
    inferInstanceAs (IsProper (𝟙 cg.space))
  have e₁ : DominatingCompactification.upperShriekPlusIso g ck cg =
      DominatingCompactification.upperShriekPlusIso g ck
        (NestedCompactification.idComp g cg).compFG ≪≫
        upperShriekCompactificationIso g (NestedCompactification.idComp g cg).compFG cg (𝟙 cg.space)
          (Category.id_comp _) (IsPullback.id_vert cg.immersion) :=
    (upperShriekPlusIso_trans g ck (NestedCompactification.idComp g cg).compFG cg).symm.trans
      (congrArg (DominatingCompactification.upperShriekPlusIso g ck
          (NestedCompactification.idComp g cg).compFG ≪≫ ·)
        (upperShriekPlusIso_eq_upperShriekCompactificationIso g
          (NestedCompactification.idComp g cg).compFG cg (𝟙 cg.space)
          (Category.id_comp _) (IsPullback.id_vert cg.immersion)))
  have e₂ : DominatingCompactification.upperShriekPlusIso (𝟙 X)
        (NestedCompactification.idComp g cg).compF c₁ ≪≫
      DominatingCompactification.upperShriekPlusIso (𝟙 X) c₁ (properCompactification (𝟙 X)) =
        Iso.refl _ :=
    (upperShriekPlusIso_trans _ _ _ _).trans (upperShriekPlusIso_refl _ _)
  have A₁ := congrArg (fun i => i.hom.app K)
    (NestedCompactification.upperShriekCompIso_eq_compIsoVia c₁ cg ck
      (NestedCompactification.idComp g cg))
  have A₂ : (DominatingCompactification.upperShriekPlusIso g cg cg).hom.app K = 𝟙 _ := by
    rw [upperShriekPlusIso_refl]; rfl
  have A₃ := congrArg (fun i => i.hom.app ((upperShriekPlus g cg).obj K)) e₂
  have A₅ := congrArg (fun i => i.hom.app K) e₁
  have A₆ : (NestedCompactification.idComp g cg).compPlusIso.hom.app K ≫
      (upperShriekPlusIdIsoProper X).hom.app ((upperShriekPlus g cg).obj K) =
      (upperShriekCompactificationIso g (NestedCompactification.idComp g cg).compFG cg (𝟙 cg.space)
        (Category.id_comp _) (IsPullback.id_vert cg.immersion)).hom.app K :=
    ObjectProperty.hom_ext _ (compHom_idComp_app g cg K.obj)
  simp only [Iso.trans_hom, NatTrans.comp_app, Iso.refl_hom, NatTrans.id_app] at A₁ A₃ A₅
  refine (congrArg (· ≫ _) A₁).trans (Eq.trans ?_ A₅.symm)
  exact left_unit_chase (upperShriekPlus (𝟙 X) c₁) A₂ A₃
    ((congrArg (_ ≫ ·) (Category.id_comp _)).trans A₆)

/-- **The right unit law of [Stacks, Tag 0ATY]**: for `f : W ⟶ X` and arbitrary compactifications
of `f`, `𝟙_X` and `f ≫ 𝟙_X = f`, the composition isomorphism `(f ≫ 𝟙)^! ≅ 𝟙^! ⋙ f^!` followed by
`f^!` of the unit `𝟙^! ≅ 𝟭` is the isomorphism of [Stacks, Tag 0AA0] between the two
compactifications of `f`. It follows from the left unit law at `𝟙_X` and the associativity
`Stacks.Duality.upperShriekFactorIso_assoc` for `f, 𝟙_X, 𝟙_X`. -/
theorem upperShriekCompIso_comp_id {W X : FTS S} (f : W ⟶ X)
    (cf : CompactificationOf (Over.mk f.left))
    (c₁ : CompactificationOf (Over.mk (𝟙 X : X ⟶ X).left))
    (ck : CompactificationOf (Over.mk (f ≫ 𝟙 X).left))
    (K : quasiCoherentDerivedCategoryPlusOfModel X.left) :
    (upperShriekCompIso f (𝟙 X) cf c₁ ck).hom.app K ≫
        (upperShriekPlus f cf).map ((upperShriekPlusIdIso X c₁).hom.app K) =
      (DominatingCompactification.upperShriekPlusIso f ck cf).hom.app K := by
  have hA := upperShriekFactorIso_assoc (Category.comp_id f) (Category.id_comp (𝟙 X))
    (Category.comp_id f) (Category.comp_id f) cf c₁ c₁ cf c₁ cf
  have hL := upperShriekCompIso_id_comp (𝟙 X) c₁ c₁ c₁
  have hρ := right_unit_formal (upperShriekPlus f cf) (upperShriekPlus (𝟙 X) c₁)
    (upperShriekPlusIdIso X c₁) (upperShriekCompIso f (𝟙 X) cf c₁ cf)
    (upperShriekCompIso (𝟙 X) (𝟙 X) c₁ c₁ c₁)
    (fun K => (cancel_epi ((upperShriekCompIso f (𝟙 X) cf c₁ cf).hom.app K)).1 (hA K))
    (fun K => (hL K).trans (by rw [upperShriekPlusIso_refl]; rfl)) K
  have hc := congrArg (fun i => i.hom.app K)
    (NestedCompactification.upperShriekCompIso_eq_conj cf c₁ cf cf c₁ ck)
  simp only [upperShriekPlusIso_refl, Functor.isoWhiskerLeft_refl, Functor.isoWhiskerRight_refl,
    Iso.trans_refl, Iso.trans_hom, NatTrans.comp_app] at hc
  rw [hc, Category.assoc]
  exact (congrArg (_ ≫ ·) hρ).trans (Category.comp_id _)

/-- **The left unit law of [Stacks, Tag 0ATY] in factored form**: for `e : 𝟙_X ≫ g = g` and any
compactifications of `𝟙_X` and `g`, `g^! ≅ g^! ∘ 𝟙^!` followed by `𝟙^! ≅ 𝟭` is the identity. -/
theorem upperShriekFactorIso_id_comp {X Y : FTS S} {g : X ⟶ Y} (e : 𝟙 X ≫ g = g)
    (c₁ : CompactificationOf (Over.mk (𝟙 X : X ⟶ X).left))
    (cg : CompactificationOf (Over.mk g.left))
    (K : quasiCoherentDerivedCategoryPlusOfModel Y.left) :
    (upperShriekFactorIso e c₁ cg cg).hom.app K ≫
        (upperShriekPlusIdIso X c₁).hom.app ((upperShriekPlus g cg).obj K) = 𝟙 _ := by
  have h := upperShriekCompIso_id_comp g c₁ cg cg K
  rw [upperShriekPlusIso_refl] at h
  exact h

/-- **The right unit law of [Stacks, Tag 0ATY] in factored form**: for `e : f ≫ 𝟙_X = f` and any
compactifications of `f` and `𝟙_X`, `f^! ≅ 𝟙^! ⋙ f^!` followed by `f^!` of `𝟙^! ≅ 𝟭` is the
identity. -/
theorem upperShriekFactorIso_comp_id {W X : FTS S} {f : W ⟶ X} (e : f ≫ 𝟙 X = f)
    (cf : CompactificationOf (Over.mk f.left))
    (c₁ : CompactificationOf (Over.mk (𝟙 X : X ⟶ X).left))
    (K : quasiCoherentDerivedCategoryPlusOfModel X.left) :
    (upperShriekFactorIso e cf c₁ cf).hom.app K ≫
        (upperShriekPlus f cf).map ((upperShriekPlusIdIso X c₁).hom.app K) = 𝟙 _ := by
  have h := upperShriekCompIso_comp_id f cf c₁ cf K
  rw [upperShriekPlusIso_refl] at h
  exact h

end Unit

end Stacks.Duality

end
