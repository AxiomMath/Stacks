module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyBrutalCollapse
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologySinglePairing

/-!
# Pairings on brutal truncations and on single complexes

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings and let `γ` be a pairing
`K^p ⊗ L^q ⟶ M^{p+q}` of bounded below complexes of `𝒪_X`-modules, in the sense of
`Stacks.Cech.Hypercohomology.Pairing`. Since `γ` carries `K^{≥a} ⊗ L^{≥b}` into `M^{≥a+b}`, it
restricts to a pairing of the brutal truncations

`σ^{≥a}K ⊗ σ^{≥b}L ⟶ σ^{≥a+b}M`,

which is the multiplicativity of the filtration by brutal truncations (Stacks Section 0FM7 for
the de Rham complex). On the graded pieces `Kᵃ[-a] ⊗ Lᵇ[-b] ⟶ M^{a+b}[-a-b]` it induces the
pairing given in bidegree `(a, b)` by `γ` itself. This file constructs both pairings and proves
that the inclusions `σ^{≥a}K ⟶ K` and the projections `σ^{≥a}K ⟶ Kᵃ[-a]` are compatible with
them, so that by `Stacks.Cech.Hypercohomology.cup_natural` they are multiplicative on
hypercohomology.

## Main definitions

* `Stacks.Cech.Hypercohomology.singlePairingAt`: the pairing of sheaves placed in degrees `a`,
  `b` and `a + b` attached to a pairing on sections.
* `Stacks.Cech.Hypercohomology.truncPairing`: the pairing of brutal truncations.

## Main results

* `Stacks.Cech.Hypercohomology.pairingHom_ιTruncPlus`: the inclusions of the truncations carry
  the truncated pairing to the given one.
* `Stacks.Cech.Hypercohomology.pairingHom_truncSC_g`: the projections to the bottom terms carry
  the truncated pairing to the pairing of the bottom terms.

## References

* [Stacks Project, Section 0FM7](https://stacks.math.columbia.edu/tag/0FM7)
* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
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

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})

/-! ### Sheaves placed in an arbitrary degree -/

/-- The term in degree `i = a` of the sections of a sheaf placed in degree `a`. -/
def singleXIsoAt (F : SheafOfModules.{u} (ringSheaf O)) (a i : ℤ) (h : i = a) :
    ((Stacks.Cech.Refinement.sectionsComplex O).obj (singlePlus O F a).obj).X i ≅ sectionsP O F :=
  (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).mapIso
    (HomologicalComplex.singleObjXIsoOfEq (up ℤ) a F i h)

/-- The differentials of the sections of a sheaf placed in a single degree vanish. -/
theorem sectionsComplex_singlePlus_d_at (F : SheafOfModules.{u} (ringSheaf O)) (a i j : ℤ) :
    ((Stacks.Cech.Refinement.sectionsComplex O).obj (singlePlus O F a).obj).d i j = 0 := by
  change (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map
    (((HomologicalComplex.single _ (up ℤ) a).obj F).d i j) = 0
  rw [HomologicalComplex.single_obj_d, Functor.map_zero]

variable {O} in
/-- **The pairing of sheaves placed in degrees `a`, `b` and `a + b` attached to a pairing on
sections**: the given pairing in bidegree `(a, b)` and zero in every other bidegree. -/
def singlePairingAt {F G H : SheafOfModules.{u} (ringSheaf O)} (a b : ℤ)
    (μ₀ : Stacks.Cech.LinearCupProduct.Pairing (SectionRing (ringSheaf O) ⊤) (sectionsP O F)
      (sectionsP O G) (sectionsP O H)) :
    Pairing O (singlePlus O F a) (singlePlus O G b) (singlePlus O H (a + b)) where
  μ p q n h := if hpq : p = a ∧ q = b then
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
          (singleXIsoAt O F a p hpq.1).hom).app _ ≫
        ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj (sectionsP O F)).map
          (singleXIsoAt O G b q hpq.2).hom ≫ μ₀ ≫ (singleXIsoAt O H (a + b) n (by omega)).inv
    else 0
  μ_d p q n h := by
    rw [sectionsComplex_singlePlus_d_at, sectionsComplex_singlePlus_d_at,
      sectionsComplex_singlePlus_d_at, Limits.comp_zero, tensorPresheafModules_map_zero,
      tensorPresheafModules_obj_map_zero, Limits.zero_comp, Limits.zero_comp, smul_zero,
      add_zero]

variable {O} in
/-- The pairing of sheaves placed in degrees `a` and `b`, in bidegree `(a, b)`. -/
theorem singlePairingAt_μ {F G H : SheafOfModules.{u} (ringSheaf O)} (a b : ℤ)
    (μ₀ : Stacks.Cech.LinearCupProduct.Pairing (SectionRing (ringSheaf O) ⊤) (sectionsP O F)
      (sectionsP O G) (sectionsP O H)) :
    (singlePairingAt a b μ₀).μ a b (a + b) rfl =
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
          (singleXIsoAt O F a a rfl).hom).app _ ≫
        ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj (sectionsP O F)).map
          (singleXIsoAt O G b b rfl).hom ≫ μ₀ ≫ (singleXIsoAt O H (a + b) (a + b) rfl).inv :=
  dite_eq_left ⟨rfl, rfl⟩

variable {O} in
/-- The pairing of sheaves placed in degrees `a` and `b` vanishes outside bidegree `(a, b)`. -/
theorem singlePairingAt_μ_of_ne {F G H : SheafOfModules.{u} (ringSheaf O)} (a b : ℤ)
    (μ₀ : Stacks.Cech.LinearCupProduct.Pairing (SectionRing (ringSheaf O) ⊤) (sectionsP O F)
      (sectionsP O G) (sectionsP O H)) (p q n : ℤ) (h : p + q = n) (hpq : ¬(p = a ∧ q = b)) :
    (singlePairingAt a b μ₀).μ p q n h = 0 :=
  dite_eq_right hpq

/-! ### The pairing of brutal truncations -/

/-- The term in a retained degree `n ≥ a` of the sections of a brutal truncation `σ^{≥a}L` is the
sections of `Lⁿ`. -/
def truncSectionsXIso (L : CochainComplex (SheafOfModules.{u} (ringSheaf O)) ℤ) (a n : ℤ)
    (h : a ≤ n) :
    ((Stacks.Cech.Refinement.sectionsComplex O).obj (truncPlus O L a).obj).X n ≅
      ((Stacks.Cech.Refinement.sectionsComplex O).obj L).X n :=
  (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).mapIso (stupidTruncGEXIso L a n h)

/-- In a retained degree the inclusion of a brutal truncation is the identification of terms, on
sections. -/
theorem sectionsComplex_ιTruncPlus_f (K : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O)))
    (a n : ℤ) (h : a ≤ n) :
    ((Stacks.Cech.Refinement.sectionsComplex O).map (ιTruncPlus O K a).hom).f n =
      (truncSectionsXIso O K.obj a n h).hom :=
  congrArg (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map
    (ιStupidTruncGE_f K.obj a n h)


section Truncation

variable {O} {K L M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))} (γ : Pairing O K L M)

/-- The pairing `γ` read on `σ^{≥a}K ⊗ σ^{≥b}L` through the two inclusions, with values in `M`. -/
def truncRestrictμ (a b p q n : ℤ) (h : p + q = n) :
    ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
        (((Stacks.Cech.Refinement.sectionsComplex O).obj (truncPlus O K.obj a).obj).X p)).obj
        (((Stacks.Cech.Refinement.sectionsComplex O).obj (truncPlus O L.obj b).obj).X q) ⟶
      ((Stacks.Cech.Refinement.sectionsComplex O).obj M.obj).X n :=
  ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
      (((Stacks.Cech.Refinement.sectionsComplex O).map (ιTruncPlus O K a).hom).f p)).app _ ≫
    ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
        (((Stacks.Cech.Refinement.sectionsComplex O).obj K.obj).X p)).map
      (((Stacks.Cech.Refinement.sectionsComplex O).map (ιTruncPlus O L b).hom).f q) ≫
    γ.μ p q n h

/-- Below the truncation degree the inclusion of a brutal truncation is zero, on sections. -/
private theorem sectionsComplex_ιTruncPlus_f_eq_zero
    (N : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) (a p : ℤ) (hp : p < a) :
    ((Stacks.Cech.Refinement.sectionsComplex O).map (ιTruncPlus O N a).hom).f p = 0 := by
  change (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map
    ((HomologicalComplex.ιStupidTrunc N.obj (embeddingUpIntGE a)).f p) = 0
  rw [(CochainComplex.isZero_of_isStrictlyGE (N.obj.stupidTrunc (embeddingUpIntGE a)) a p
    hp).eq_of_src ((HomologicalComplex.ιStupidTrunc N.obj (embeddingUpIntGE a)).f p) 0,
    Functor.map_zero]

/-- Below the truncation degrees the restricted pairing vanishes, its source being zero. -/
theorem truncRestrictμ_eq_zero (a b p q n : ℤ) (h : p + q = n) (hpq : p < a ∨ q < b) :
    truncRestrictμ γ a b p q n h = 0 := by
  rcases hpq with hp | hq
  · rw [truncRestrictμ, sectionsComplex_ιTruncPlus_f_eq_zero K a p hp,
      tensorPresheafModules_map_zero, Limits.zero_comp]
  · rw [truncRestrictμ, sectionsComplex_ιTruncPlus_f_eq_zero L b q hq,
      tensorPresheafModules_obj_map_zero, Limits.zero_comp, Limits.comp_zero]

/-- The components of the pairing of brutal truncations: the restricted pairing, read in the
truncation `σ^{≥a+b}M` where it lands. -/
def truncPairingμ (a b p q n : ℤ) (h : p + q = n) :
    ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
        (((Stacks.Cech.Refinement.sectionsComplex O).obj (truncPlus O K.obj a).obj).X p)).obj
        (((Stacks.Cech.Refinement.sectionsComplex O).obj (truncPlus O L.obj b).obj).X q) ⟶
      ((Stacks.Cech.Refinement.sectionsComplex O).obj (truncPlus O M.obj (a + b)).obj).X n :=
  if hn : a + b ≤ n then
    truncRestrictμ γ a b p q n h ≫ (truncSectionsXIso O M.obj (a + b) n hn).inv
  else 0

/-- **The pairing of brutal truncations followed by the inclusion of `σ^{≥a+b}M` is the given
pairing read through the inclusions of `σ^{≥a}K` and `σ^{≥b}L`.** -/
theorem truncPairingμ_comp_ι (a b p q n : ℤ) (h : p + q = n) :
    truncPairingμ γ a b p q n h ≫
        ((Stacks.Cech.Refinement.sectionsComplex O).map (ιTruncPlus O M (a + b)).hom).f n =
      truncRestrictμ γ a b p q n h := by
  by_cases hn : a + b ≤ n
  · rw [truncPairingμ, dite_eq_left hn, Category.assoc,
      sectionsComplex_ιTruncPlus_f O M (a + b) n hn, Iso.inv_hom_id, Category.comp_id]
  · rw [truncPairingμ, dite_eq_right hn, Limits.zero_comp,
      truncRestrictμ_eq_zero γ a b p q n h (by omega)]

/-- The restricted pairing satisfies the Leibniz rule relative to the differentials of the
truncations and of `M`, because the inclusions of the truncations are morphisms of complexes. -/
theorem truncRestrictμ_d (a b p q n : ℤ) (h : p + q = n) :
    truncRestrictμ γ a b p q n h ≫
        ((Stacks.Cech.Refinement.sectionsComplex O).obj M.obj).d n (n + 1) =
      ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).obj (truncPlus O K.obj a).obj).d p
            (p + 1))).app
          (((Stacks.Cech.Refinement.sectionsComplex O).obj (truncPlus O L.obj b).obj).X q) ≫
        truncRestrictμ γ a b (p + 1) q (n + 1) (by omega) +
      p.negOnePow • (((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
          (((Stacks.Cech.Refinement.sectionsComplex O).obj (truncPlus O K.obj a).obj).X p)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).obj (truncPlus O L.obj b).obj).d q
            (q + 1)) ≫ truncRestrictμ γ a b p (q + 1) (n + 1) (by omega)) := by
  have hK := ((Stacks.Cech.Refinement.sectionsComplex O).map (ιTruncPlus O K a).hom).comm p (p + 1)
  have hL := ((Stacks.Cech.Refinement.sectionsComplex O).map (ιTruncPlus O L b).hom).comm q (q + 1)
  have e1 := congrArg (fun φ => ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
    φ).app (((Stacks.Cech.Refinement.sectionsComplex O).obj (truncPlus O L.obj b).obj).X q)) hK
  have e2 := congrArg (fun φ => ((tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
    (((Stacks.Cech.Refinement.sectionsComplex O).obj K.obj).X p)).map φ) hL
  simp only [Functor.map_comp, NatTrans.comp_app] at e1 e2
  dsimp only [truncRestrictμ]
  simp only [Category.assoc]
  rw [γ.μ_d p q n h, Preadditive.comp_add, Preadditive.comp_add, Units.smul_def, Units.smul_def,
    Preadditive.comp_zsmul, Preadditive.comp_zsmul]
  congr 1
  · rw [NatTrans.naturality_assoc, reassoc_of% e1]
  · congr 1
    rw [reassoc_of% e2, ← NatTrans.naturality_assoc]

/-- **The pairing of brutal truncations** `σ^{≥a}K ⊗ σ^{≥b}L ⟶ σ^{≥a+b}M` induced by a pairing
`K ⊗ L ⟶ M`. -/
def truncPairing (a b : ℤ) :
    Pairing O (truncPlus O K.obj a) (truncPlus O L.obj b) (truncPlus O M.obj (a + b)) where
  μ := truncPairingμ γ a b
  μ_d p q n h := by
    by_cases hn : a + b ≤ n + 1
    · have hiso : IsIso (((Stacks.Cech.Refinement.sectionsComplex O).map
          (ιTruncPlus O M (a + b)).hom).f (n + 1)) := by
        change IsIso ((sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map
          ((HomologicalComplex.ιStupidTrunc M.obj (embeddingUpIntGE (a + b))).f (n + 1)))
        rw [ιStupidTruncGE_f M.obj (a + b) (n + 1) hn]
        infer_instance
      rw [← cancel_mono (((Stacks.Cech.Refinement.sectionsComplex O).map
        (ιTruncPlus O M (a + b)).hom).f (n + 1)), Preadditive.add_comp, Units.smul_def,
        Preadditive.zsmul_comp,
        Category.assoc, Category.assoc, Category.assoc, truncPairingμ_comp_ι,
        truncPairingμ_comp_ι, ← HomologicalComplex.Hom.comm, ← Category.assoc,
        truncPairingμ_comp_ι]
      exact truncRestrictμ_d γ a b p q n h
    · exact ((sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map_isZero
        (CochainComplex.isZero_of_isStrictlyGE (M.obj.stupidTrunc (embeddingUpIntGE (a + b)))
          (a + b) (n + 1) (by omega))).eq_of_tgt _ _

/-- **The inclusions of the brutal truncations carry the pairing of truncations to the given
pairing.** -/
theorem pairingHom_ιTruncPlus (a b : ℤ) :
    PairingHom O (ιTruncPlus O K a) (ιTruncPlus O L b) (ιTruncPlus O M (a + b))
      (truncPairing γ a b) γ := fun p q n h =>
  (truncPairingμ_comp_ι γ a b p q n h).symm

/-- The projection of a brutal truncation onto its bottom term, followed by the identification of
that term, is the identification of the bottom term of the truncation, read on sections. -/
theorem sectionsComplex_truncSC_g_singleXIsoAt (N : CochainComplex.Plus
    (SheafOfModules.{u} (ringSheaf O))) (a : ℤ) :
    ((Stacks.Cech.Refinement.sectionsComplex O).map (truncPlusπ N.obj a).hom).f a ≫
        (singleXIsoAt O (N.obj.X a) a a rfl).hom =
      ((Stacks.Cech.Refinement.sectionsComplex O).map (ιTruncPlus O N a).hom).f a := by
  have key : (stupidTruncGEπ N.obj a).f a ≫
      (HomologicalComplex.singleObjXSelf (up ℤ) a (N.obj.X a)).hom =
      (HomologicalComplex.ιStupidTrunc N.obj (embeddingUpIntGE a)).f a := by
    rw [stupidTruncGEπ_f, Category.assoc, Iso.inv_hom_id, Category.comp_id,
      ← ιStupidTruncGE_f N.obj a a le_rfl]
  exact ((sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map_comp _ _).symm.trans
    (congrArg (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map key)

/-- **The projections of the brutal truncations onto their bottom terms carry the pairing of
truncations to the pairing of the bottom terms**, given in bidegree `(a, b)` by `γ` itself. -/
theorem pairingHom_truncSC_g (a b : ℤ) :
    PairingHom O (truncPlusπ K.obj a) (truncPlusπ L.obj b) (truncPlusπ M.obj (a + b))
      (truncPairing γ a b) (singlePairingAt a b (γ.μ a b (a + b) rfl)) := by
  intro p q n h
  by_cases hpq : p = a ∧ q = b
  · obtain ⟨rfl, rfl⟩ := hpq
    subst h
    have hM : (truncSectionsXIso O M.obj (p + q) (p + q) le_rfl).inv ≫
        ((Stacks.Cech.Refinement.sectionsComplex O).map (truncPlusπ M.obj (p + q)).hom).f
          (p + q) = (singleXIsoAt O (M.obj.X (p + q)) (p + q) (p + q) rfl).inv := by
      have key : (stupidTruncGEXIso M.obj (p + q) (p + q) le_rfl).inv ≫
          (stupidTruncGEπ M.obj (p + q)).f (p + q) =
          (HomologicalComplex.singleObjXSelf (up ℤ) (p + q) (M.obj.X (p + q))).inv := by
        rw [stupidTruncGEπ_f, Iso.inv_hom_id_assoc]
      exact ((sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map_comp _ _).symm.trans
        (congrArg (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map key)
    have e : (truncPairing γ p q).μ p q (p + q) rfl =
        truncRestrictμ γ p q p q (p + q) rfl ≫
          (truncSectionsXIso O M.obj (p + q) (p + q) le_rfl).inv :=
      dite_eq_left le_rfl
    rw [singlePairingAt_μ, e, Category.assoc, hM, truncRestrictμ,
      ← sectionsComplex_truncSC_g_singleXIsoAt K p,
      ← sectionsComplex_truncSC_g_singleXIsoAt L q, Functor.map_comp, NatTrans.comp_app,
      Functor.map_comp]
    simp only [Category.assoc]
    rw [NatTrans.naturality_assoc]
    rfl
  · rw [singlePairingAt_μ_of_ne _ _ _ p q n h hpq, Limits.comp_zero]
    by_cases hn : n = a + b
    · subst hn
      change 0 = truncPairingμ γ a b p q (a + b) h ≫ _
      rw [truncPairingμ, dite_eq_left le_rfl, truncRestrictμ_eq_zero γ a b p q (a + b) h (by omega),
        Limits.zero_comp, Limits.zero_comp]
    · exact ((sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map_isZero
        (HomologicalComplex.isZero_single_obj_X (up ℤ) (a + b) _ n hn)).eq_of_tgt _ _

end Truncation

end Stacks.Cech.Hypercohomology

end
