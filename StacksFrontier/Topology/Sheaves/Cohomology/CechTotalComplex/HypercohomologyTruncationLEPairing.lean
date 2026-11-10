module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyTruncationLE
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyPairingPrecomp

/-!
# Pairings of the two brutal truncations of a complex concentrated in `[0, d]`

Let `K` be a bounded below complex of `𝒪_X`-modules whose terms vanish above degree `d`, and
`γ : K^a ⊗ K^b ⟶ K^{a+b}` a pairing of `K` with itself. For `p + e ≥ d` the pairing `γ` restricted
to `K ⊗ σ^{≥e}K` annihilates `σ^{>p}K ⊗ σ^{≥e}K` for degree reasons, so it descends to a pairing

`γ_{p,e} : σ^{≤p}K ⊗ σ^{≥e}K ⟶ K`.

On the graded pieces `Kᵃ[-a]` and `Kᵇ[-b]`, `a + b = d`, the pairing `γ` in bidegree `(a, b)` is
a pairing `Kᵃ[-a] ⊗ Kᵇ[-b] ⟶ K` with values in the top degree. These are the pairings of the
proof of [Stacks, Tag 0FW7] (there for the de Rham complex, `σ^{≤p}` and `σ^{≥d-p}`), and this
file proves the two compatibilities with the short exact sequences

`0 ⟶ K^{p+1}[-p-1] ⟶ σ^{≤p+1}K ⟶ σ^{≤p}K ⟶ 0`  and
`0 ⟶ σ^{≥q+1}K ⟶ σ^{≥q}K ⟶ K^q[-q] ⟶ 0`, `p + 1 + q = d`,

which are the hypotheses of [Stacks, Tag 07MC]
(`Stacks.Cech.Hypercohomology.cup_boundary_of_pairing`).

## Main definitions

* `Stacks.Cech.Hypercohomology.Pairing.descLE`: a pairing descended along `K ⟶ σ^{≤p}K`.
* `Stacks.Cech.Hypercohomology.truncLEGEPairing`: `γ_{p,e}`.
* `Stacks.Cech.Hypercohomology.gradedPairing`: the pairing of the graded pieces.

## Main results

* `Stacks.Cech.Hypercohomology.gradedPairing_compat`,
  `Stacks.Cech.Hypercohomology.truncLEGEPairing_compat`: the two compatibilities.

## References

* [Stacks Project, Tag 0FW7](https://stacks.math.columbia.edu/tag/0FW7)
* [Stacks Project, Tag 07MC](https://stacks.math.columbia.edu/tag/07MC)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing sectionsPresheafFunctor)
open Stacks.Cech.LinearCupProduct (ComplexPairing tensorPresheafModules)
open StacksDraft.StupidTruncation

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}

local notation "secC" => Stacks.Cech.Refinement.sectionsComplex O
local notation "tens" => tensorPresheafModules (SectionRing (ringSheaf O) ⊤)

/-- Sections of a zero sheaf vanish. -/
theorem isZero_sections {F : SheafOfModules.{u} (ringSheaf O)} (hF : IsZero F) :
    IsZero ((sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).obj F) :=
  (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map_isZero hF

section TruncLE

variable (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))

/-- In a retained degree `a ≤ p` the sections of `σ^{≤p}K` are those of `K`. -/
def truncLESectionsXIso (p a : ℤ) (h : a ≤ p) :
    ((secC).obj (truncLEPlus O K p).obj).X a ≅ ((secC).obj K.obj).X a :=
  (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).mapIso (stupidTruncLEXIso K.obj p a h)

/-- In a retained degree the projection `K ⟶ σ^{≤p}K` is the inverse identification, on
sections. -/
theorem sectionsComplex_truncLEπ_f (p a : ℤ) (h : a ≤ p) :
    ((secC).map (truncLEπ O K p).hom).f a = (truncLESectionsXIso K p a h).inv :=
  congrArg (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map
    (πStupidTrunc_f K.obj (embeddingUpIntLE p) (i := (p - a).toNat)
      (by change p - ((p - a).toNat : ℤ) = a; omega))

/-- The differentials of `σ^{≤p}K` in retained degrees are those of `K`, on sections. -/
theorem truncLESectionsXIso_comm (p a : ℤ) (h : a + 1 ≤ p) :
    (truncLESectionsXIso K p a (by omega)).hom ≫ ((secC).obj K.obj).d a (a + 1) =
      ((secC).obj (truncLEPlus O K p).obj).d a (a + 1) ≫
        (truncLESectionsXIso K p (a + 1) h).hom := by
  have := ((secC).map (truncLEπ O K p).hom).comm a (a + 1)
  rw [sectionsComplex_truncLEπ_f K p a (by omega), sectionsComplex_truncLEπ_f K p (a + 1) h] at this
  rw [← cancel_epi (truncLESectionsXIso K p a (by omega)).inv, Iso.inv_hom_id_assoc,
    reassoc_of% this, Iso.inv_hom_id, Category.comp_id]

/-- Sections of `σ^{≤p}K` vanish above `p`. -/
theorem isZero_truncLESections_X {p a : ℤ} (h : p < a) :
    IsZero (((secC).obj (truncLEPlus O K p).obj).X a) :=
  isZero_sections (isZero_truncLEPlus_X O K h)

/-- The comparison `σ^{≤p+1}K ⟶ σ^{≤p}K` in a degree retained by both, on sections. -/
theorem sectionsComplex_truncLEMap_f {p p' : ℤ} (h : p ≤ p') (a : ℤ) (ha : a ≤ p) :
    ((secC).map (truncLEMap O K h).hom).f a ≫ (truncLESectionsXIso K p a ha).hom =
      (truncLESectionsXIso K p' a (ha.trans h)).hom := by
  have e := congrArg (fun φ => ((secC).map φ.hom).f a) (truncLEπ_truncLEMap O K h)
  simp only [Functor.map_comp, HomologicalComplex.comp_f, ObjectProperty.FullSubcategory.comp_hom,
    sectionsComplex_truncLEπ_f K _ a ha, sectionsComplex_truncLEπ_f K _ a (ha.trans h)] at e
  rw [← cancel_epi (truncLESectionsXIso K p' a (ha.trans h)).inv, reassoc_of% e,
    Iso.inv_hom_id, Iso.inv_hom_id]

/-- The inclusion of the top term `Kᵖ[-p] ⟶ σ^{≤p}K` followed by the identification of terms is
the identification of the single term, on sections. -/
theorem sectionsComplex_truncLEι_f (p : ℤ) :
    ((secC).map (truncLEι O K p).hom).f p ≫ (truncLESectionsXIso K p p le_rfl).hom =
      (singleXIsoAt O (K.obj.X p) p p rfl).hom := by
  have key : (stupidTruncLEι K.obj p).f p ≫ (stupidTruncLEXIso K.obj p p le_rfl).hom =
      (HomologicalComplex.singleObjXSelf (up ℤ) p (K.obj.X p)).hom := by
    rw [stupidTruncLEι_f, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  exact ((sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map_comp _ _).symm.trans
    (congrArg (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map key)

end TruncLE

/-! ### Descending a pairing along `K ⟶ σ^{≤p}K` -/

section Desc

variable {K L M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}

/-- **A pairing descended along the projection `K ⟶ σ^{≤p}K`**, for a pairing which vanishes on
the terms of `K` above `p`. -/
def Pairing.descLE (D : Pairing O K L M) (p : ℤ)
    (hD : ∀ a b n h, p < a → D.μ a b n h = 0) : Pairing O (truncLEPlus O K p) L M where
  μ a b n h := if ha : a ≤ p then
      ((tens).map (truncLESectionsXIso K p a ha).hom).app (((secC).obj L.obj).X b) ≫ D.μ a b n h
    else 0
  μ_d a b n h := by
    by_cases ha : a ≤ p
    · rw [dite_eq_left ha, dite_eq_left ha, Category.assoc, D.μ_d a b n h]
      simp only [Preadditive.comp_add, Units.smul_def, Preadditive.comp_zsmul]
      congr 1
      · by_cases ha' : a + 1 ≤ p
        · rw [dite_eq_left ha', ← Category.assoc, ← Category.assoc, ← NatTrans.comp_app,
            ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp,
            truncLESectionsXIso_comm K p a ha']
        · rw [dite_eq_right ha', Limits.comp_zero, hD (a + 1) b (n + 1) (by omega) (by omega),
            Limits.comp_zero, Limits.comp_zero]
      · rw [← Category.assoc, ← Category.assoc, NatTrans.naturality]
    · have ha' : ¬ a + 1 ≤ p := by omega
      simp only [ha, ha', dite_false, Limits.zero_comp, Limits.comp_zero, smul_zero, add_zero]

/-- In a degree `a ≤ p` the descended pairing is the original pairing after the identification
of the terms of `σ^{≤p}K` with those of `K`. -/
theorem Pairing.descLE_μ_of_le (D : Pairing O K L M) (p : ℤ)
    (hD : ∀ a b n h, p < a → D.μ a b n h = 0) (a b n : ℤ) (h : a + b = n) (ha : a ≤ p) :
    (D.descLE p hD).μ a b n h =
      ((tens).map (truncLESectionsXIso K p a ha).hom).app (((secC).obj L.obj).X b) ≫
        D.μ a b n h :=
  dite_eq_left ha

/-- In a degree `a > p` the descended pairing vanishes. -/
theorem Pairing.descLE_μ_of_lt (D : Pairing O K L M) (p : ℤ)
    (hD : ∀ a b n h, p < a → D.μ a b n h = 0) (a b n : ℤ) (h : a + b = n) (ha : p < a) :
    (D.descLE p hD).μ a b n h = 0 :=
  dite_eq_right (by omega)

/-- The projection `K ⟶ σ^{≤p}K` carries the pairing to its descent. -/
theorem pairingHom_descLE (D : Pairing O K L M) (p : ℤ)
    (hD : ∀ a b n h, p < a → D.μ a b n h = 0) :
    PairingHom O (truncLEπ O K p) (𝟙 L) (𝟙 M) D (D.descLE p hD) := fun a b n h => by
  simp only [CategoryTheory.Functor.map_id, HomologicalComplex.id_f,
    ObjectProperty.FullSubcategory.id_hom, Category.id_comp, Category.comp_id]
  by_cases ha : a ≤ p
  · rw [Pairing.descLE_μ_of_le D p hD a b n h ha, sectionsComplex_truncLEπ_f K p a ha,
      ← Category.assoc, ← NatTrans.comp_app, ← Functor.map_comp, Iso.inv_hom_id,
      CategoryTheory.Functor.map_id, NatTrans.id_app, Category.id_comp]
  · rw [Pairing.descLE_μ_of_lt D p hD a b n h (by omega), Limits.comp_zero,
      hD a b n h (by omega)]

end Desc

/-! ### The pairings of the truncations and of the graded pieces -/

section TopVanishing

variable (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (γ : Pairing O K K K)
  (d : ℤ) (hd : ∀ n, d < n → IsZero (K.obj.X n))

/-- The inclusion `σ^{≥e}K ⟶ K` vanishes on sections in degrees below `e`. -/
private theorem sectionsComplex_ιTruncPlus_f_of_lt (e b : ℤ) (hb : b < e) :
    ((secC).map (ιTruncPlus O K e).hom).f b = 0 :=
  (isZero_sections (CochainComplex.isZero_of_isStrictlyGE
    (K.obj.stupidTrunc (embeddingUpIntGE e)) e b hb)).eq_of_src _ _

include hd in
/-- For `p + e ≥ d` the pairing `γ` restricted to `K ⊗ σ^{≥e}K` vanishes on the terms of `K`
above `p`, for degree reasons. -/
theorem precompRight_ιTruncPlus_vanish (p e : ℤ) (hpe : d ≤ p + e) (a b n : ℤ) (h : a + b = n)
    (ha : p < a) : (γ.precompRight (ιTruncPlus O K e)).μ a b n h = 0 := by
  rw [ComplexPairing.precompRight_μ]
  by_cases hb : e ≤ b
  · exact (isZero_sections (hd n (by omega))).eq_of_tgt _ _
  · rw [sectionsComplex_ιTruncPlus_f_of_lt K e b (by omega), tensorPresheafModules_obj_map_zero,
      Limits.zero_comp]

/-- **The pairing `σ^{≤p}K ⊗ σ^{≥e}K ⟶ K`** induced by `γ`, for `p + e ≥ d`. -/
def truncLEGEPairing (p e : ℤ) (hpe : d ≤ p + e) :
    Pairing O (truncLEPlus O K p) (truncPlus O K.obj e) K :=
  (γ.precompRight (ιTruncPlus O K e)).descLE p
    (fun a b n h ha => precompRight_ιTruncPlus_vanish K γ d hd p e hpe a b n h ha)

/-- In a degree `a ≤ p` the pairing `σ^{≤p}K ⊗ σ^{≥e}K ⟶ K` is `γ` after the identification of
the terms of `σ^{≤p}K` and the inclusion `σ^{≥e}K ⟶ K`. -/
theorem truncLEGEPairing_μ (p e : ℤ) (hpe : d ≤ p + e) (a b n : ℤ) (h : a + b = n) (ha : a ≤ p) :
    (truncLEGEPairing K γ d hd p e hpe).μ a b n h =
      ((tens).map (truncLESectionsXIso K p a ha).hom).app
          (((secC).obj (truncPlus O K.obj e).obj).X b) ≫
        ((tens).obj (((secC).obj K.obj).X a)).map (((secC).map (ιTruncPlus O K e).hom).f b) ≫
          γ.μ a b n h :=
  Pairing.descLE_μ_of_le _ p _ a b n h ha

/-- In a degree `a > p` the pairing `σ^{≤p}K ⊗ σ^{≥e}K ⟶ K` vanishes. -/
theorem truncLEGEPairing_μ_of_lt (p e : ℤ) (hpe : d ≤ p + e) (a b n : ℤ) (h : a + b = n)
    (ha : p < a) : (truncLEGEPairing K γ d hd p e hpe).μ a b n h = 0 :=
  Pairing.descLE_μ_of_lt _ p _ a b n h ha

/-- **The pairing of the graded pieces** `Kᵃ[-a] ⊗ Kᵇ[-b] ⟶ K` for `a + b = d`: `γ` in bidegree
`(a, b)`, with values in the top degree of `K`. -/
def gradedPairing (a b : ℤ) (hab : a + b = d) :
    Pairing O (singlePlus O (K.obj.X a) a) (singlePlus O (K.obj.X b) b) K where
  μ a' b' n h := if hab' : a' = a ∧ b' = b then
      ((tens).map (singleXIsoAt O (K.obj.X a) a a' hab'.1).hom).app _ ≫
        ((tens).obj (sectionsP O (K.obj.X a))).map (singleXIsoAt O (K.obj.X b) b b' hab'.2).hom ≫
          γ.μ a b n (by omega)
    else 0
  μ_d a' b' n h := by
    rw [sectionsComplex_singlePlus_d_at, sectionsComplex_singlePlus_d_at,
      tensorPresheafModules_map_zero, tensorPresheafModules_obj_map_zero, Limits.zero_comp,
      Limits.zero_comp, smul_zero, add_zero]
    by_cases hab' : a' = a ∧ b' = b
    · exact (isZero_sections (hd (n + 1) (by omega))).eq_of_tgt _ _
    · rw [dite_eq_right hab', Limits.zero_comp]

/-- In bidegree `(a, b)` the pairing of the graded pieces is `γ` after the identifications of the
single terms. -/
theorem gradedPairing_μ (a b : ℤ) (hab : a + b = d) :
    (gradedPairing K γ d hd a b hab).μ a b (a + b) rfl =
      ((tens).map (singleXIsoAt O (K.obj.X a) a a rfl).hom).app _ ≫
        ((tens).obj (sectionsP O (K.obj.X a))).map (singleXIsoAt O (K.obj.X b) b b rfl).hom ≫
          γ.μ a b (a + b) rfl :=
  dite_eq_left ⟨rfl, rfl⟩

/-- Outside bidegree `(a, b)` the pairing of the graded pieces vanishes. -/
theorem gradedPairing_μ_of_ne (a b : ℤ) (hab : a + b = d) (a' b' n : ℤ) (h : a' + b' = n)
    (hab' : ¬ (a' = a ∧ b' = b)) : (gradedPairing K γ d hd a b hab).μ a' b' n h = 0 :=
  dite_eq_right hab'

include hd in
/-- **The first compatibility of [Stacks, Tag 07MC]** for the sequences
`0 ⟶ K^{p+1}[-p-1] ⟶ σ^{≤p+1}K ⟶ σ^{≤p}K ⟶ 0` and `0 ⟶ σ^{≥q+1}K ⟶ σ^{≥q}K ⟶ K^q[-q] ⟶ 0`,
`p + 1 + q = d`: the pairing of the graded pieces after the projection `σ^{≥q}K ⟶ K^q[-q]` is the
pairing of the truncations after the inclusion `K^{p+1}[-p-1] ⟶ σ^{≤p+1}K`. -/
theorem gradedPairing_compat (p q : ℤ) (hpq : p + 1 + q = d) (a b n : ℤ) (hn : a + b = n) :
    ((tens).obj (((secC).obj (singlePlus O (K.obj.X (p + 1)) (p + 1)).obj).X a)).map
        (((secC).map (truncPlusπ K.obj q).hom).f b) ≫
      (gradedPairing K γ d hd (p + 1) q hpq).μ a b n hn =
    ((tens).map (((secC).map (truncLEι O K (p + 1)).hom).f a)).app
        (((secC).obj (truncPlus O K.obj q).obj).X b) ≫
      (truncLEGEPairing K γ d hd (p + 1) q hpq.ge).μ a b n hn := by
  by_cases ha : a = p + 1
  · subst ha
    by_cases hb : b = q
    · subst hb hn
      rw [gradedPairing_μ, truncLEGEPairing_μ K γ d hd (p + 1) b hpq.ge _ _ _ rfl le_rfl,
        ← NatTrans.comp_app_assoc, ← Functor.map_comp, sectionsComplex_truncLEι_f K (p + 1),
        NatTrans.naturality_assoc, ← Functor.map_comp_assoc,
        sectionsComplex_truncSC_g_singleXIsoAt]
      rfl
    · rw [gradedPairing_μ_of_ne K γ d hd _ _ hpq _ _ n hn (fun h => hb h.2), Limits.comp_zero,
        truncLEGEPairing_μ K γ d hd (p + 1) q hpq.ge _ _ _ hn le_rfl]
      by_cases hqb : q ≤ b
      · exact ((isZero_sections (hd n (by omega))).eq_of_tgt _ _).symm
      · rw [sectionsComplex_ιTruncPlus_f_of_lt K q b (by omega),
          tensorPresheafModules_obj_map_zero, Limits.zero_comp, Limits.comp_zero, Limits.comp_zero]
  · rw [gradedPairing_μ_of_ne K γ d hd _ _ hpq _ _ n hn (fun h => ha h.1), Limits.comp_zero]
    have h0 : ((secC).map (truncLEι O K (p + 1)).hom).f a = 0 :=
      (isZero_sections (HomologicalComplex.isZero_single_obj_X (up ℤ) (p + 1) (K.obj.X (p + 1)) a
        ha)).eq_of_src _ _
    rw [h0, tensorPresheafModules_map_zero, Limits.zero_comp]

include hd in
/-- **The second compatibility of [Stacks, Tag 07MC]** for the same sequences: the pairing of
`σ^{≤p+1}K` and `σ^{≥q}K` after the comparison `σ^{≥q+1}K ⟶ σ^{≥q}K` is the pairing of `σ^{≤p}K`
and `σ^{≥q+1}K` after the comparison `σ^{≤p+1}K ⟶ σ^{≤p}K`. -/
theorem truncLEGEPairing_compat (p q : ℤ) (hpq : p + 1 + q = d) (a b n : ℤ) (hn : a + b = n) :
    ((tens).obj (((secC).obj (truncLEPlus O K (p + 1)).obj).X a)).map
        (((secC).map (truncPlusMap O K.obj (show q ≤ q + 1 by omega)).hom).f b) ≫
      (truncLEGEPairing K γ d hd (p + 1) q hpq.ge).μ a b n hn =
    ((tens).map (((secC).map (truncLEMap O K (show p ≤ p + 1 by omega)).hom).f a)).app
        (((secC).obj (truncPlus O K.obj (q + 1)).obj).X b) ≫
      (truncLEGEPairing K γ d hd p (q + 1) (by omega)).μ a b n hn := by
  have hι : ((secC).map (truncPlusMap O K.obj (show q ≤ q + 1 by omega)).hom).f b ≫
      ((secC).map (ιTruncPlus O K q).hom).f b = ((secC).map (ιTruncPlus O K (q + 1)).hom).f b := by
    rw [← HomologicalComplex.comp_f, ← Functor.map_comp, ← ObjectProperty.FullSubcategory.comp_hom,
      truncPlusMap_ιTruncPlus]
  by_cases ha : a ≤ p
  · rw [truncLEGEPairing_μ K γ d hd (p + 1) q hpq.ge _ _ _ hn (by omega),
      truncLEGEPairing_μ K γ d hd p (q + 1) (by omega) _ _ _ hn ha,
      NatTrans.naturality_assoc, ← Functor.map_comp_assoc, hι, ← NatTrans.comp_app_assoc,
      ← Functor.map_comp, sectionsComplex_truncLEMap_f K (show p ≤ p + 1 by omega) a ha]
  · rw [truncLEGEPairing_μ_of_lt K γ d hd p (q + 1) (by omega) _ _ _ hn (by omega),
      Limits.comp_zero]
    by_cases ha' : a ≤ p + 1
    · rw [truncLEGEPairing_μ K γ d hd (p + 1) q hpq.ge _ _ _ hn ha',
        NatTrans.naturality_assoc, ← Functor.map_comp_assoc, hι]
      by_cases hb : q + 1 ≤ b
      · exact (isZero_sections (hd n (by omega))).eq_of_tgt _ _
      · rw [sectionsComplex_ιTruncPlus_f_of_lt K (q + 1) b (by omega),
          tensorPresheafModules_obj_map_zero, Limits.zero_comp, Limits.comp_zero]
    · rw [truncLEGEPairing_μ_of_lt K γ d hd (p + 1) q hpq.ge _ _ _ hn (by omega),
        Limits.comp_zero]

end TopVanishing

end Stacks.Cech.Hypercohomology

end
