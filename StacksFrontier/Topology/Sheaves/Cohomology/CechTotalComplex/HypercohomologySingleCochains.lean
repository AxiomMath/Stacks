module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.RefinementOfACovering
public import StacksFrontier.Topology.Sheaves.Cohomology.CechOfSheavesOfModules.SliceSiteComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechToCohomology.DegreeOneComparison
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CechCupProductNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupUnit

/-!
# Čech cochains of a sheaf placed in degree zero

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings, `ℱ` a sheaf of
`𝒪_X`-modules and `𝒰 = (Uᵢ)` an open covering of `X`. A Čech `p`-cochain of `ℱ` in the explicit
model of [Stacks, Tag 01FJ] — a family of sections `s_{i₀…i_p} ∈ ℱ(U_{i₀} ∩ ⋯ ∩ U_{i_p})` — is a
cochain of degree `p` of the total Čech complex of `ℱ` placed in degree zero. This file records
that inclusion and its compatibility with the differential, with morphisms of sheaves and with
refinement.

## Main definitions

* `Stacks.Cech.Hypercohomology.cochainOf`: the cochain of the total Čech complex attached to an
  explicit Čech cochain.

## Main results

* `Stacks.Cech.Hypercohomology.cochainOf_d`: it commutes with the Čech differentials.
* `Stacks.Cech.Hypercohomology.cochainOf_map`: it is natural in the sheaf.
* `Stacks.Cech.Hypercohomology.cochainOf_refinement`: it commutes with refinement.

## References

* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing sectionsPresheafFunctor sectionsPresheaf coverObject
  abSections mmk mcomp md rawcomp mcomp_mmk mcech_ext mcomp_add mcomp_zero res_mcomp
  toCochainFun toCochainFun_apply toCochainFun_injective toCochainFun_md res_ge_res_le)
open Stacks.Cohomology.Basis (res res_res res_id res_add res_zero res_app)
open Stacks.Cech.LinearCupProduct (cechCochainsMap ιTotalCechTo)
open Stacks.Cohomology.RightDerivedBoundary (toSC)

universe u

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing
attribute [local implicit_reducible] CechCochains.Cochain

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) (F : SheafOfModules.{u} (ringSheaf O))

/-- The cochain of the module-valued Čech complex with the components of an explicit Čech
cochain. -/
def sliceCochain {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    ToType (((CategoryTheory.cechComplexFunctor (coverObject U hU)).obj
      (sectionsPresheaf ⊤ F)).X p) :=
  mmk ⊤ U hU F fun x => res (abSections F) (Stacks.Cech.cechComplexInter_eq U x).le (c x)

/-- The components of the cochain attached to an explicit Čech cochain are its values. -/
theorem toCochainFun_sliceCochain {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    toCochainFun ⊤ U hU F (sliceCochain U hU F c) = c :=
  funext fun x =>
    (congrArg (res (abSections F) (Stacks.Cech.cechComplexInter_eq U x).ge)
        (mcomp_mmk ⊤ U hU F _ x)).trans
      (res_ge_res_le (abSections F) (Stacks.Cech.cechComplexInter_eq U x) (c x))

/-- The components of the cochain attached to an explicit Čech cochain. -/
theorem mcomp_sliceCochain {p : ℕ} (c : CechCochains.Cochain U (abSections F) p)
    (x : Fin (p + 1) → I) :
    mcomp ⊤ U hU F (sliceCochain U hU F c) x =
      res (abSections F) (Stacks.Cech.cechComplexInter_eq U x).le (c x) :=
  mcomp_mmk ⊤ U hU F _ x

/-- The cochain attached to an explicit Čech cochain is additive. -/
theorem sliceCochain_add {p : ℕ} (c c' : CechCochains.Cochain U (abSections F) p) :
    sliceCochain U hU F (c + c') = sliceCochain U hU F c + sliceCochain U hU F c' :=
  mcech_ext ⊤ U hU F _ _ fun x => by
    rw [mcomp_add, mcomp_sliceCochain, mcomp_sliceCochain, mcomp_sliceCochain]
    exact res_add _ _ _ _

/-- The cochain attached to the zero Čech cochain is zero. -/
theorem sliceCochain_zero {p : ℕ} :
    sliceCochain U hU F (0 : CechCochains.Cochain U (abSections F) p) = 0 :=
  mcech_ext ⊤ U hU F _ _ fun x => by
    rw [mcomp_sliceCochain]
    exact (res_zero _ _).trans (mcomp_zero ⊤ U hU F x).symm

/-- The cochains attached to explicit Čech cochains commute with the Čech differentials. -/
theorem md_sliceCochain {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    md ⊤ U hU F (sliceCochain U hU F c) =
      sliceCochain U hU F (CechCochains.cechD U (abSections F) p c) := by
  refine toCochainFun_injective ⊤ U hU F (funext fun y => ?_)
  rw [toCochainFun_md, toCochainFun_sliceCochain, toCochainFun_sliceCochain]

/-- The cochain of the module-valued Čech complex attached to an explicit Čech cochain, as a
morphism out of the ring. -/
def sliceMor {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶ Stacks.Cech.LinearCupProduct.cechCochains
      (coverObject U hU) (SectionRing (ringSheaf O) ⊤) (sectionsP O F) p :=
  toMor (M := Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (sectionsP O F) p) (sliceCochain U hU F c)

/-- Composing `toMor x` with `f` gives `toMor y` as soon as `f x = y`. -/
private theorem toMor_comp_eq_of_apply_eq {R : Type u} [Ring R] {M N : ModuleCat.{u} R}
    (x : M) (f : M ⟶ N) (y : N) (h : f x = y) : toMor x ≫ f = toMor y :=
  (toMor_comp x f).trans (congrArg toMor h)

/-- The cochains attached to explicit Čech cochains commute with the Čech differentials, as
morphisms out of the ring. -/
theorem sliceMor_cechD {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    sliceMor U hU F c ≫ Stacks.Cech.LinearCupProduct.cechD (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (sectionsP O F) p =
      sliceMor U hU F (CechCochains.cechD U (abSections F) p c) :=
  toMor_comp_eq_of_apply_eq _ _ _ (md_sliceCochain U hU F c)

/-- `sliceMor` is additive. -/
theorem sliceMor_add {p : ℕ} (c c' : CechCochains.Cochain U (abSections F) p) :
    sliceMor U hU F (c + c') = sliceMor U hU F c + sliceMor U hU F c' := by
  unfold sliceMor
  rw [sliceCochain_add]
  exact toMor_add (M := Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (sectionsP O F) p) _ _

/-- `sliceMor` of the zero cochain is zero. -/
theorem sliceMor_zero {p : ℕ} :
    sliceMor U hU F (0 : CechCochains.Cochain U (abSections F) p) = 0 := by
  unfold sliceMor
  rw [sliceCochain_zero]
  have h := toMor_add (M := Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (sectionsP O F) p) 0 0
  rw [add_zero] at h
  exact add_eq_left.mp h.symm

/-! ### Naturality in the sheaf -/

section Naturality

variable {F} {G : SheafOfModules.{u} (ringSheaf O)} (f : F ⟶ G)

/-- A morphism of sheaves acts on the components of a cochain. -/
theorem mcomp_cechCochainsMap {p : ℕ}
    (t : ToType (((CategoryTheory.cechComplexFunctor (coverObject U hU)).obj
      (sectionsPresheaf ⊤ F)).X p)) (x : Fin (p + 1) → I) :
    mcomp ⊤ U hU G (ConcreteCategory.hom (cechCochainsMap (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) ((sectionsPresheafFunctor ⊤).map f) p) t) x =
      ConcreteCategory.hom (((SheafOfModules.toSheaf _).map f).hom.app _)
        (mcomp ⊤ U hU F t x) := by
  have h1 : rawcomp ⊤ U hU G (ConcreteCategory.hom (cechCochainsMap (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) ((sectionsPresheafFunctor ⊤).map f) p) t) x =
      ConcreteCategory.hom (((SheafOfModules.toSheaf _).map f).hom.app _)
        (rawcomp ⊤ U hU F t x) := by
    have := ConcreteCategory.congr_hom (Stacks.Cech.LinearCupProduct.cechCochainsMap_comp_π
      (coverObject U hU) (SectionRing (ringSheaf O) ⊤) ((sectionsPresheafFunctor ⊤).map f) p x) t
    exact this
  unfold mcomp
  rw [h1]
  exact res_app _ _ _ _

/-- A morphism of sheaves acts componentwise on the attached cochains. -/
theorem sliceCochain_map {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    ConcreteCategory.hom (cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
      ((sectionsPresheafFunctor ⊤).map f) p) (sliceCochain U hU F c) =
      sliceCochain U hU G (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map f).hom p c) :=
  mcech_ext ⊤ U hU G _ _ fun x => by
    rw [mcomp_cechCochainsMap, mcomp_sliceCochain, mcomp_sliceCochain]
    exact (res_app _ _ _ _).symm

end Naturality

/-- **The cochain of the total Čech complex attached to an explicit Čech cochain**, in the total
Čech complex of the sections presheaves and at a total degree `n = p + 0`. -/
def cochainOfTo {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) (n : ℤ)
    (h : (p : ℤ) + 0 = n) :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤)).obj (sectionsK O F)).X n :=
  sliceMor U hU F c ≫
    cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
      (singleXIso O F 0 rfl).inv p ≫
    ιTotalCechTo (coverObject U hU) (SectionRing (ringSheaf O) ⊤) (sectionsK O F) p 0 n h

/-- The attached cochains commute with the differentials, at an arbitrary total degree. -/
theorem cochainOfTo_d {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) (n : ℤ)
    (h : (p : ℤ) + 0 = n) :
    cochainOfTo U hU F c n h ≫ ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor
      (coverObject U hU) (SectionRing (ringSheaf O) ⊤)).obj (sectionsK O F)).d n (n + 1) =
      cochainOfTo U hU F (CechCochains.cechD U (abSections F) p c) (n + 1)
        (by push_cast; omega) := by
  have h0 : cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
      ((sectionsK O F).d 0 (0 + 1)) p = 0 := by
    rw [sectionsComplex_singlePlus_d]
    change ((CategoryTheory.cechComplexFunctor (coverObject U hU)).map (0 : _ ⟶ _)).f p = 0
    rw [Functor.map_zero]
    rfl
  have hd := Stacks.Cech.LinearCupProduct.ιTotalCechTo_d (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤) (sectionsK O F) p 0 n h
  have hm := Stacks.Cech.LinearCupProduct.cechCochainsMap_d (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤) (singleXIso O F 0 rfl).inv p
  unfold cochainOfTo
  rw [Category.assoc, Category.assoc, hd, h0,
    Limits.zero_comp, smul_zero, add_zero, reassoc_of% hm, ← Category.assoc, sliceMor_cechD]

/-- **The cochain of the total Čech complex attached to an explicit Čech cochain**: a family of
sections over the `(p+1)`-fold intersections, placed in Čech degree `p` and coefficient degree
`0` of the total Čech complex of `ℱ` placed in degree zero. -/
def cochainOf {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶ ((cech O U hU).obj (singlePlus O F 0).obj).X p :=
  cochainOfTo U hU F c p (add_zero _)

/-- **The attached cochains commute with the differentials.** -/
theorem cochainOf_d {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    cochainOf U hU F c ≫ ((cech O U hU).obj (singlePlus O F 0).obj).d p (p + 1) =
      cochainOf U hU F (CechCochains.cechD U (abSections F) p c) :=
  cochainOfTo_d U hU F c p (add_zero _)

/-- The attached cochain is additive. -/
theorem cochainOfTo_add {p : ℕ} (c c' : CechCochains.Cochain U (abSections F) p) (n : ℤ)
    (h : (p : ℤ) + 0 = n) :
    cochainOfTo U hU F (c + c') n h = cochainOfTo U hU F c n h + cochainOfTo U hU F c' n h := by
  unfold cochainOfTo
  rw [sliceMor_add, Preadditive.add_comp]

/-- The cochain attached to zero is zero. -/
theorem cochainOfTo_zero {p : ℕ} (n : ℤ) (h : (p : ℤ) + 0 = n) :
    cochainOfTo U hU F (0 : CechCochains.Cochain U (abSections F) p) n h = 0 := by
  unfold cochainOfTo
  rw [sliceMor_zero, Limits.zero_comp]

/-- The cochain attached to zero is zero. -/
theorem cochainOf_zero {p : ℕ} :
    cochainOf U hU F (0 : CechCochains.Cochain U (abSections F) p) = 0 :=
  cochainOfTo_zero U hU F p (add_zero _)

/-- The attached cochain is additive. -/
theorem cochainOf_add {p : ℕ} (c c' : CechCochains.Cochain U (abSections F) p) :
    cochainOf U hU F (c + c') = cochainOf U hU F c + cochainOf U hU F c' :=
  cochainOfTo_add U hU F c c' p (add_zero _)

/-- The cochain attached to a Čech cocycle is a cocycle. -/
theorem cochainOf_d_eq_zero {p : ℕ} (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    cochainOf U hU F c ≫ ((cech O U hU).obj (singlePlus O F 0).obj).d p (p + 1) = 0 := by
  rw [cochainOf_d, hc, cochainOf_zero]

/-! ### Naturality of the attached cochains -/

section NaturalityTotal

variable {F} {G : SheafOfModules.{u} (ringSheaf O)} (f : F ⟶ G)

/-- The identification of degree zero of a sheaf placed in degree zero is natural. -/
theorem singleXIso_inv_naturality :
    (singleXIso O F 0 rfl).inv ≫ ((Stacks.Cech.Refinement.sectionsComplex O).map
      (singlePlusMap O f).hom).f 0 =
      (sectionsPresheafFunctor ⊤).map f ≫ (singleXIso O G 0 rfl).inv := by
  change (sectionsPresheafFunctor ⊤).map _ ≫ (sectionsPresheafFunctor ⊤).map _ =
    (sectionsPresheafFunctor ⊤).map _ ≫ (sectionsPresheafFunctor ⊤).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1

/-- A morphism of sheaves acts on the attached cochains componentwise. -/
theorem sliceMor_map {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    sliceMor U hU F c ≫ cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
      ((sectionsPresheafFunctor ⊤).map f) p =
      sliceMor U hU G (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map f).hom p c) :=
  toMor_comp_eq_of_apply_eq _ _ _ (sliceCochain_map U hU f c)

/-- The attached cochains are natural in the sheaf, at an arbitrary total degree. -/
theorem cochainOfTo_map {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) (n : ℤ)
    (h : (p : ℤ) + 0 = n) :
    cochainOfTo U hU F c n h ≫ ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor
      (coverObject U hU) (SectionRing (ringSheaf O) ⊤)).map
        ((Stacks.Cech.Refinement.sectionsComplex O).map (singlePlusMap O f).hom)).f n =
      cochainOfTo U hU G (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map f).hom p c) n h := by
  have hι := Stacks.Cech.LinearCupProduct.ιTotalCechTo_totalCechComplexFunctor_map
    (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
    ((Stacks.Cech.Refinement.sectionsComplex O).map (singlePlusMap O f).hom) p 0 n h
  have hc := congrArg (fun φ => cechCochainsMap (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤) φ p) (singleXIso_inv_naturality f)
  simp only [Stacks.Cech.LinearCupProduct.cechCochainsMap_comp] at hc
  unfold cochainOfTo
  rw [Category.assoc, Category.assoc, hι, reassoc_of% hc, ← Category.assoc, sliceMor_map]

end NaturalityTotal

/-! ### Refinement -/

section Refinement

variable {J : Type u} (V : J → Opens X) (hV : ⊤ = ⨆ j, V j) (r : J → I)
  (hr : ∀ j, V j ≤ U (r j))

include hr in
/-- A refinement carries the intersections of the refining covering into those of the refined
one. -/
theorem inter_le_inter_refinement {p : ℕ} (x : Fin (p + 1) → J) :
    Stacks.CategoryTheory.CechComplex.inter V x ≤
      Stacks.CategoryTheory.CechComplex.inter U (r ∘ x) :=
  (Stacks.Cech.cechComplexInter_eq V x).le.trans
    ((CechCochains.inter_le_inter_comp U V r hr x).trans
      (Stacks.Cech.cechComplexInter_eq U (r ∘ x)).ge)

/-- The components of a refined cochain are restrictions of the components of the cochain. -/
theorem mcomp_cechRefinement {p : ℕ}
    (t : ToType (((CategoryTheory.cechComplexFunctor (coverObject U hU)).obj
      (sectionsPresheaf ⊤ F)).X p)) (x : Fin (p + 1) → J) :
    mcomp ⊤ V hV F (ConcreteCategory.hom ((Stacks.Cech.LinearCupProduct.cechRefinement
      (coverObject U hU) (coverObject V hV) (SectionRing (ringSheaf O) ⊤) r
      (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr) (sectionsPresheaf ⊤ F)).f p) t)
        x =
      res (abSections F) (inter_le_inter_refinement U V r hr x) (mcomp ⊤ U hU F t (r ∘ x)) := by
  have h1 : rawcomp ⊤ V hV F (ConcreteCategory.hom ((Stacks.Cech.LinearCupProduct.cechRefinement
      (coverObject U hU) (coverObject V hV) (SectionRing (ringSheaf O) ⊤) r
      (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr) (sectionsPresheaf ⊤ F)).f p) t)
        x =
      res (abSections F) (leOfHom (Stacks.Cech.LinearCupProduct.refinementInter
        (coverObject U hU) (coverObject V hV) r
        (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr) p x).left)
        (rawcomp ⊤ U hU F t (r ∘ x)) :=
    ConcreteCategory.congr_hom (Stacks.Cech.LinearCupProduct.cechRefinement_f_comp_π
      (coverObject U hU) (coverObject V hV) (SectionRing (ringSheaf O) ⊤) r
      (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr) (sectionsPresheaf ⊤ F) p x) t
  unfold mcomp
  rw [h1, res_res, res_res]

/-- The attached cochains commute with refinement, componentwise. -/
theorem sliceCochain_refinement {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    sliceCochain V hV F (CechCochains.refinementMap U V r hr (abSections F) p c) =
      ConcreteCategory.hom ((Stacks.Cech.LinearCupProduct.cechRefinement
        (coverObject U hU) (coverObject V hV) (SectionRing (ringSheaf O) ⊤) r
        (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr) (sectionsPresheaf ⊤ F)).f p)
          (sliceCochain U hU F c) :=
  mcech_ext ⊤ V hV F _ _ fun x => by
    rw [mcomp_cechRefinement, mcomp_sliceCochain, mcomp_sliceCochain,
      CechCochains.refinementMap_apply]
    change res _ _ (res _ _ _) = res _ _ (res _ _ _)
    rw [res_res, res_res]

private theorem paste_inv_hom {C : Type*} [Category* C] {a b c d e : C} (i : b ⟶ a) (j : a ⟶ b)
    (hij : i ≫ j = 𝟙 b) (x : b ⟶ c) (y : c ⟶ d) (z : d ⟶ e) :
    i ≫ ((j ≫ x ≫ y) ≫ z) = x ≫ y ≫ z := by
  rw [Category.assoc, ← Category.assoc i, hij, Category.id_comp, Category.assoc]

/-- The refinement map of total Čech complexes on a homogeneous summand, at an arbitrary total
degree. -/
theorem ιTotalCechTo_totalCechRefinement
    (K : CochainComplex (Stacks.Cech.LinearCupProduct.PresheafModules.{u} (Over (⊤ : Opens X))
      (SectionRing (ringSheaf O) ⊤)) ℤ) (p : ℕ) (a n : ℤ) (h : (p : ℤ) + a = n) :
    ιTotalCechTo (coverObject U hU) (SectionRing (ringSheaf O) ⊤) K p a n h ≫
      ((Stacks.Cech.LinearCupProduct.totalCechRefinement (coverObject U hU) (coverObject V hV)
        (SectionRing (ringSheaf O) ⊤) r
        (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr)).app K).f n =
      (Stacks.Cech.LinearCupProduct.cechRefinement (coverObject U hU) (coverObject V hV)
        (SectionRing (ringSheaf O) ⊤) r
        (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr) (K.X a)).f p ≫
      ιTotalCechTo (coverObject V hV) (SectionRing (ringSheaf O) ⊤) K p a n h := by
  unfold ιTotalCechTo
  refine (Category.assoc _ _ _).trans ?_
  refine (whisker_eq _ (Stacks.Cech.LinearCupProduct.ιTotal_totalCechRefinement _ _ _ _ _ K
    (p : ℤ) a n h)).trans ?_
  refine (whisker_eq _ (eq_whisker (Stacks.Cech.LinearCupProduct.cechIntRefinement_app_f _ _ _ _ _
    (K.X a) p) _)).trans ?_
  exact paste_inv_hom _ _ (Iso.inv_hom_id _) _ _ _

/-- The attached cochains commute with refinement, as morphisms out of the ring. -/
theorem sliceMor_refinement {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    sliceMor U hU F c ≫ (Stacks.Cech.LinearCupProduct.cechRefinement (coverObject U hU)
      (coverObject V hV) (SectionRing (ringSheaf O) ⊤) r
      (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr) (sectionsP O F)).f p =
      sliceMor V hV F (CechCochains.refinementMap U V r hr (abSections F) p c) :=
  toMor_comp_eq_of_apply_eq _ _ _ (sliceCochain_refinement U hU F V hV r hr c).symm

/-- **The attached cochains commute with refinement.** -/
theorem cochainOfTo_refinement {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) (n : ℤ)
    (h : (p : ℤ) + 0 = n) :
    cochainOfTo U hU F c n h ≫
      ((Stacks.Cech.LinearCupProduct.totalCechRefinement (coverObject U hU) (coverObject V hV)
        (SectionRing (ringSheaf O) ⊤) r
        (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr)).app (sectionsK O F)).f n =
      cochainOfTo V hV F (CechCochains.refinementMap U V r hr (abSections F) p c) n h := by
  have hn : cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
      (singleXIso O F 0 rfl).inv p ≫ (Stacks.Cech.LinearCupProduct.cechRefinement
        (coverObject U hU) (coverObject V hV) (SectionRing (ringSheaf O) ⊤) r
        (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr) ((sectionsK O F).X 0)).f p =
      (Stacks.Cech.LinearCupProduct.cechRefinement (coverObject U hU) (coverObject V hV)
        (SectionRing (ringSheaf O) ⊤) r
        (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr) (sectionsP O F)).f p ≫
      cechCochainsMap (coverObject V hV) (SectionRing (ringSheaf O) ⊤)
        (singleXIso O F 0 rfl).inv p :=
    (HomologicalComplex.comp_f _ _ p).symm.trans ((congrArg (fun φ => HomologicalComplex.Hom.f φ p)
      (Stacks.Cech.LinearCupProduct.cechRefinement_naturality (coverObject U hU)
        (coverObject V hV) (SectionRing (ringSheaf O) ⊤) r
        (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr)
        (singleXIso O F 0 rfl).inv)).trans (HomologicalComplex.comp_f _ _ p))
  unfold cochainOfTo
  rw [Category.assoc, Category.assoc, ιTotalCechTo_totalCechRefinement U hU V hV r hr,
    reassoc_of% hn, ← Category.assoc, sliceMor_refinement]

/-- **The attached cochains commute with refinement**, in the total Čech complex of the
sheaf placed in degree zero. -/
theorem cochainOf_refinement {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    cochainOf U hU F c ≫
      ((Stacks.Cech.Refinement.cechRefinement O U hU V hV r hr).app (singlePlus O F 0).obj).f p =
      cochainOf V hV F (CechCochains.refinementMap U V r hr (abSections F) p c) :=
  cochainOfTo_refinement U hU F V hV r hr c p (add_zero _)

end Refinement

/-! ### The classes of Čech cocycles -/

/-- **The class in `Hᵖ(X, ℱ)` of a Čech `p`-cocycle** of an open covering, through the
comparison of the total Čech complex with derived global sections. -/
def cechCocycleClass {p : ℕ} (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    hypercohomology O (singlePlus O F 0) p :=
  cechClass O U hU (singlePlus O F 0) p
    (cocycleClass (p : ℤ) (cochainOf U hU F c) (cochainOf_d_eq_zero U hU F c hc)
      (1 : SectionRing (ringSheaf O) ⊤))

/-- The class of a Čech cocycle does not depend on the proof that it is a cocycle, and only on
the cocycle. -/
theorem cechCocycleClass_congr {p : ℕ} {c c' : CechCochains.Cochain U (abSections F) p}
    (h : c = c') (hc : CechCochains.cechD U (abSections F) p c = 0)
    (hc' : CechCochains.cechD U (abSections F) p c' = 0) :
    cechCocycleClass U hU F c hc = cechCocycleClass U hU F c' hc' := by
  subst h
  rfl

/-- **A Čech coboundary has class zero.** -/
theorem cechCocycleClass_eq_zero {q : ℕ} (t : CechCochains.Cochain U (abSections F) q)
    (c : CechCochains.Cochain U (abSections F) (q + 1))
    (hc : CechCochains.cechD U (abSections F) (q + 1) c = 0)
    (ht : CechCochains.cechD U (abSections F) q t = c) :
    cechCocycleClass U hU F c hc = 0 := by
  have hx : cochainOf U hU F c = cochainOf U hU F t ≫
      ((cech O U hU).obj (singlePlus O F 0).obj).d q (q + 1) := by
    rw [cochainOf_d, ht]
  have h0 : cocycleClass ((q + 1 : ℕ) : ℤ) (cochainOf U hU F c)
      (cochainOf_d_eq_zero U hU F c hc) = 0 :=
    HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ _ _ hx
  unfold cechCocycleClass
  rw [h0]
  exact map_zero _

/-- **Čech cocycles differing by a coboundary have the same class.** -/
theorem cechCocycleClass_eq_of_eq_add {q : ℕ} (c c' : CechCochains.Cochain U (abSections F) (q + 1))
    (hc : CechCochains.cechD U (abSections F) (q + 1) c = 0)
    (hc' : CechCochains.cechD U (abSections F) (q + 1) c' = 0)
    (t : CechCochains.Cochain U (abSections F) q)
    (ht : c = c' + CechCochains.cechD U (abSections F) q t) :
    cechCocycleClass U hU F c hc = cechCocycleClass U hU F c' hc' := by
  have hx : cochainOf U hU F c = cochainOf U hU F c' + cochainOf U hU F t ≫
      ((cech O U hU).obj (singlePlus O F 0).obj).d (q : ℤ) ((q + 1 : ℕ) : ℤ) := by
    rw [ht, cochainOf_add]
    exact congrArg _ (cochainOf_d U hU F t).symm
  unfold cechCocycleClass cocycleClass
  rw [Stacks.CupProduct.liftCycles_homologyπ_eq_of_eq_add_comp_d _ (q : ℤ) _ _
    (by simp) (CochainComplex.next ℤ _) _ _ _ _ _ hx]

/-- **The class of a Čech cocycle is unchanged by refinement.** -/
theorem cechCocycleClass_refinement {J : Type u} (V : J → Opens X) (hV : ⊤ = ⨆ j, V j)
    (r : J → I) (hr : ∀ j, V j ≤ U (r j)) {p : ℕ}
    (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    cechCocycleClass V hV F (CechCochains.refinementMap U V r hr (abSections F) p c)
        (by rw [← CechCochains.refinementMap_cechD, hc, map_zero]) =
      cechCocycleClass U hU F c hc := by
  have href := cechClass_refinement O U hU V hV r hr (singlePlus O F 0) p
  symm
  unfold cechCocycleClass
  rw [← href, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply (cocycleClass _ _ _),
    cocycleClass_comp_homologyMap]
  congr 2
  exact congrArg ConcreteCategory.hom (cocycleClass_congr _
    (cochainOf_refinement U hU F V hV r hr c) _ _)

variable {F} in
/-- The attached cochains are natural in the sheaf. -/
theorem cochainOf_map {G : SheafOfModules.{u} (ringSheaf O)} (f : F ⟶ G) {p : ℕ}
    (c : CechCochains.Cochain U (abSections F) p) :
    cochainOf U hU F c ≫ ((cech O U hU).map (singlePlusMap O f).hom).f p =
      cochainOf U hU G (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map f).hom p c) :=
  cochainOfTo_map U hU f c p (add_zero _)

variable {F} in
/-- **The class of a Čech cocycle is natural in the sheaf.** -/
theorem hypercohomologyMap_cechCocycleClass {G : SheafOfModules.{u} (ringSheaf O)} (f : F ⟶ G)
    {p : ℕ} (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    hypercohomologyMap O (singlePlusMap O f) p (cechCocycleClass U hU F c hc) =
      cechCocycleClass U hU G (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map f).hom p c)
        (by rw [← Stacks.Cohomology.CechOne.push_cechD, hc, map_zero]) := by
  unfold cechCocycleClass
  rw [← ConcreteCategory.comp_apply, ← cechClass_naturality, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply (cocycleClass _ _ _), cocycleClass_comp_homologyMap]
  congr 2
  exact congrArg ConcreteCategory.hom (cocycleClass_congr _ (cochainOf_map U hU f c) _ _)

/-! ### Global sections -/

/-- The Čech `0`-cochain of the restrictions of a global section to the members of a
covering. -/
def restrictionCochain (t : F.val.obj (op ⊤)) : CechCochains.Cochain U (abSections F) 0 :=
  fun _ => res (abSections F) le_top (show ToType ((abSections F).obj (op ⊤)) from t)

/-- The restrictions of a global section form a Čech cocycle. -/
theorem cechD_restrictionCochain (t : F.val.obj (op ⊤)) :
    CechCochains.cechD U (abSections F) 0 (restrictionCochain U F t) = 0 := by
  funext y
  rw [CechCochains.cechD_apply, Fin.sum_univ_two]
  change (-1 : ℤ) ^ 0 • res (abSections F) _ (res (abSections F) le_top
      (show ToType ((abSections F).obj (op ⊤)) from t)) + (-1 : ℤ) ^ 1 • res (abSections F) _
      (res (abSections F) le_top (show ToType ((abSections F).obj (op ⊤)) from t)) = 0
  rw [res_res, res_res, pow_zero, pow_one, one_smul, neg_one_smul, add_neg_cancel]

/-- The cochain of the restrictions of a global section is its augmentation. -/
theorem sliceCochain_restrictionCochain (t : F.val.obj (op ⊤)) :
    sliceCochain U hU F (restrictionCochain U F t) =
      ConcreteCategory.hom (Stacks.Cech.LinearCupProduct.cechAugmentationCochains
        (coverObject U hU) (SectionRing (ringSheaf O) ⊤) (isTerminalTopOver (X := X))
        (sectionsP O F)) (show (sectionsP O F).obj (op (topOver (X := X))) from t) :=
  mcech_ext ⊤ U hU F _ _ fun x => by
    have h := ConcreteCategory.congr_hom
      (Stacks.Cech.LinearCupProduct.cechAugmentationCochains_comp_π (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤) (isTerminalTopOver (X := X)) (sectionsP O F) x)
      (show (sectionsP O F).obj (op (topOver (X := X))) from t)
    rw [ConcreteCategory.comp_apply] at h
    rw [mcomp_sliceCochain]
    unfold mcomp rawcomp
    rw [show ConcreteCategory.hom (Stacks.CategoryTheory.CechComplex.π (coverObject U hU)
        (sectionsPresheaf ⊤ F) 0 x) (ConcreteCategory.hom
          (Stacks.Cech.LinearCupProduct.cechAugmentationCochains (coverObject U hU)
            (SectionRing (ringSheaf O) ⊤) (isTerminalTopOver (X := X)) (sectionsP O F))
          (show (sectionsP O F).obj (op (topOver (X := X))) from t)) = _ from h]
    change res (abSections F) _ (res (abSections F) _
        (show ToType ((abSections F).obj (op ⊤)) from t)) =
      res (abSections F) _ (res (abSections F) _
        (show ToType ((abSections F).obj (op ⊤)) from t))
    rw [res_res, res_res]

/-- The cochain of the restrictions of a global section is its augmentation, as morphisms out of
the ring. -/
theorem sliceMor_restrictionCochain (t : F.val.obj (op ⊤)) :
    sliceMor U hU F (restrictionCochain U F t) =
      toMor (show (sectionsP O F).obj (op (topOver (X := X))) from t) ≫
        Stacks.Cech.LinearCupProduct.cechAugmentationCochains
          (coverObject U hU) (SectionRing (ringSheaf O) ⊤) (isTerminalTopOver (X := X))
          (sectionsP O F) :=
  (toMor_comp_eq_of_apply_eq _ _ _ (sliceCochain_restrictionCochain U hU F t).symm).symm

/-- **The cochain of the restrictions of a global section is its augmentation cocycle.** -/
theorem cochainOf_restrictionCochain (t : F.val.obj (op ⊤)) :
    cochainOf U hU F (restrictionCochain U F t) = sectionCochain U hU F t := by
  have hn := Stacks.Cech.LinearCupProduct.cechAugmentationCochains_naturality (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤) (isTerminalTopOver (X := X)) (singleXIso O F 0 rfl).inv
  change sliceMor U hU F (restrictionCochain U F t) ≫ _ ≫ _ = globalSection F t ≫ _ ≫ _
  rw [sliceMor_restrictionCochain, Category.assoc, reassoc_of% hn,
    Stacks.Cech.LinearCupProduct.ιTotalCechTo_eq (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (sectionsK O F) 0 0 _ (add_zero _)]
  rfl

/-- **The class of a global section is the class of its restrictions.** -/
theorem cechCocycleClass_restrictionCochain (t : F.val.obj (op ⊤)) :
    cechCocycleClass U hU F (restrictionCochain U F t) (cechD_restrictionCochain U F t) =
      sectionClass F t := by
  rw [sectionClass_eq_cechClass U hU F t]
  unfold cechCocycleClass
  congr 2
  exact congrArg ConcreteCategory.hom (cocycleClass_congr _
    (cochainOf_restrictionCochain U hU F t) _ _)

/-- **The class of a global section is natural in the sheaf.** -/
theorem hypercohomologyMap_sectionClass {F G : SheafOfModules.{u} (ringSheaf O)} (f : F ⟶ G)
    (t : F.val.obj (op ⊤)) :
    hypercohomologyMap O (singlePlusMap O f) 0 (sectionClass F t) =
      sectionClass G (f.val.app (op ⊤) t) := by
  rw [← cechCocycleClass_restrictionCochain (fun _ : PUnit.{u + 1} => (⊤ : Opens X))
      top_eq_iSup_top F t,
    ← cechCocycleClass_restrictionCochain (fun _ : PUnit.{u + 1} => (⊤ : Opens X))
      top_eq_iSup_top G (f.val.app (op ⊤) t)]
  refine (hypercohomologyMap_cechCocycleClass _ top_eq_iSup_top f _ _).trans
    (cechCocycleClass_congr _ _ _ (funext fun x => ?_) _ _)
  exact (res_app (X := ↑X) (abSections F) ((SheafOfModules.toSheaf _).map f).hom le_top
    (show ToType ((abSections F).obj (op ⊤)) from t)).symm

section SingleIso

attribute [local instance] HasDerivedCategory.standard

variable (O) in
/-- **The hypercohomology of isomorphic sheaves placed in degree zero.** -/
def hypercohomologySingleIso {F G : SheafOfModules.{u} (ringSheaf O)} (e : F ≅ G) (n : ℤ) :
    hypercohomology O (singlePlus O F 0) n ≅ hypercohomology O (singlePlus O G 0) n :=
  (Stacks.Cech.Linear.derivedSectionsFunctor X (ringSheaf O) ⊤ ⋙
    DerivedCategory.homologyFunctor _ n).mapIso
      (ObjectProperty.isoMk _ ((HomologicalComplex.single _ (up ℤ) 0).mapIso e))

/-- The isomorphism of hypercohomologies induced by an isomorphism of sheaves. -/
theorem hypercohomologySingleIso_hom_apply {F G : SheafOfModules.{u} (ringSheaf O)} (e : F ≅ G)
    (n : ℤ) (x : hypercohomology O (singlePlus O F 0) n) :
    (hypercohomologySingleIso O e n).hom x = hypercohomologyMap O (singlePlusMap O e.hom) n x :=
  rfl

end SingleIso

/-! ### The boundary of a global section -/

variable (O) in
/-- A short complex of sheaves of modules, placed in degree zero. -/
def singlePlusSC (S : ShortComplex (SheafOfModules.{u} (ringSheaf O))) :
    ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))) :=
  ShortComplex.mk (singlePlusMap O S.f) (singlePlusMap O S.g) (by
    apply ObjectProperty.hom_ext
    change (HomologicalComplex.single _ (up ℤ) 0).map S.f ≫
      (HomologicalComplex.single _ (up ℤ) 0).map S.g = 0
    rw [← Functor.map_comp, S.zero, Functor.map_zero])

variable (O) in
/-- A short exact sequence of sheaves of modules placed in degree zero is short exact. -/
theorem shortExact_singlePlusSC {S : ShortComplex (SheafOfModules.{u} (ringSheaf O))}
    (hS : S.ShortExact) : (toSC (singlePlusSC O S)).ShortExact :=
  hS.map_of_exact (HomologicalComplex.single _ (up ℤ) 0)

section Boundary

variable {S : ShortComplex (SheafOfModules.{u} (ringSheaf O))}

/-- The Čech cochain of a family of sections, in the total Čech complex of the first term of a
short complex placed in degree zero, in degree `0 + 1`. -/
abbrev cochainOne₁ (ω : CechCochains.Cochain U (abSections S.X₁) 1) :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      ((cech O U hU).obj (singlePlusSC O S).X₁.obj).X (0 + 1) :=
  cochainOf U hU S.X₁ ω

/-- The Čech cochain of a family of sections, in the total Čech complex of the third term of a
short complex placed in degree zero, in degree `0`. -/
abbrev cochainZero₃ (c : CechCochains.Cochain U (abSections S.X₃) 0) :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      ((cech O U hU).obj (singlePlusSC O S).X₃.obj).X 0 :=
  cochainOf U hU S.X₃ c

/-- The cochain of a Čech `1`-cocycle of the first term is a cocycle. -/
theorem cochainOne₁_d (ω : CechCochains.Cochain U (abSections S.X₁) 1)
    (hω : CechCochains.cechD U (abSections S.X₁) 1 ω = 0) :
    cochainOne₁ U hU ω ≫ ((cech O U hU).obj (singlePlusSC O S).X₁.obj).d (0 + 1) (0 + 1 + 1) =
      0 :=
  cochainOf_d_eq_zero U hU S.X₁ ω hω

/-- The cochain of a Čech `0`-cocycle of the third term is a cocycle. -/
theorem cochainZero₃_d (c : CechCochains.Cochain U (abSections S.X₃) 0)
    (hc : CechCochains.cechD U (abSections S.X₃) 0 c = 0) :
    cochainZero₃ U hU c ≫ ((cech O U hU).obj (singlePlusSC O S).X₃.obj).d 0 (0 + 1) = 0 :=
  cochainOf_d_eq_zero U hU S.X₃ c hc

/-- The equation of `boundary_sectionClass` between morphisms out of the ring. -/
theorem boundary_sectionClass_aux (hS : S.ShortExact) (t : S.X₃.val.obj (op ⊤))
    (s : CechCochains.Cochain U (abSections S.X₂) 0)
    (hs : Stacks.Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map S.g).hom 0 s =
      restrictionCochain U S.X₃ t)
    (ω : CechCochains.Cochain U (abSections S.X₁) 1)
    (hω : CechCochains.cechD U (abSections S.X₁) 1 ω = 0)
    (hωs : Stacks.Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map S.f).hom 1 ω =
      CechCochains.cechD U (abSections S.X₂) 0 s) :
    cocycleClass (0 + 1) (cochainOne₁ U hU ω) (cochainOne₁_d U hU ω hω) ≫
        cechClass O U hU (singlePlusSC O S).X₁ (0 + 1) =
      cocycleClass 0 (cochainZero₃ U hU (restrictionCochain U S.X₃ t))
          (cochainZero₃_d U hU _ (cechD_restrictionCochain U S.X₃ t)) ≫
        cechClass O U hU (singlePlusSC O S).X₃ 0 ≫
          boundary O (singlePlusSC O S) (shortExact_singlePlusSC O hS) 0 (0 + 1) rfl := by
  have h₃ : cochainOf U hU S.X₂ s ≫ ((cech O U hU).map (singlePlusSC O S).g.hom).f 0 =
      cochainZero₃ U hU (restrictionCochain U S.X₃ t) := by
    rw [← hs]
    exact cochainOf_map U hU S.g s
  have hα₃ : (cochainOf U hU S.X₂ s ≫ ((cech O U hU).map (singlePlusSC O S).g.hom).f 0) ≫
      ((cech O U hU).obj (singlePlusSC O S).X₃.obj).d 0 (0 + 1) = 0 := by
    rw [h₃]
    exact cochainZero₃_d U hU _ (cechD_restrictionCochain U S.X₃ t)
  have hα : cochainOne₁ U hU ω ≫ ((cech O U hU).map (singlePlusSC O S).f.hom).f (0 + 1) =
      cochainOf U hU S.X₂ s ≫ ((cech O U hU).obj (singlePlusSC O S).X₂.obj).d 0 (0 + 1) := by
    refine (cochainOf_map U hU S.f ω).trans ?_
    rw [hωs]
    exact (cochainOf_d U hU S.X₂ s).symm
  rw [cechClass_boundary O U hU (singlePlusSC O S) (shortExact_singlePlusSC O hS) 0
    (cochainOf U hU S.X₂ s) (cochainOne₁ U hU ω) hα₃ (cochainOne₁_d U hU ω hω) hα]
  exact congrArg (fun z => z ≫ cechClass O U hU (singlePlusSC O S).X₃ 0 ≫
    boundary O (singlePlusSC O S) (shortExact_singlePlusSC O hS) 0 (0 + 1) rfl)
    (cocycleClass_congr 0 h₃ hα₃ _)

/-- **The boundary of the class of a global section, on Čech cocycles.**  Let
`0 ⟶ ℱ₁ ⟶ ℱ₂ ⟶ ℱ₃ ⟶ 0` be a short exact sequence of sheaves of modules and `t` a global section
of `ℱ₃`. If `sᵢ ∈ ℱ₂(Uᵢ)` lift the restrictions of `t` and `ω` is a Čech `1`-cocycle of `ℱ₁`
mapping to the Čech coboundary `s_{i₁} - s_{i₀}` of `s`, then `∂[t] = [ω]` in `H¹(X, ℱ₁)`. -/
theorem boundary_sectionClass (hS : S.ShortExact) (t : S.X₃.val.obj (op ⊤))
    (s : CechCochains.Cochain U (abSections S.X₂) 0)
    (hs : Stacks.Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map S.g).hom 0 s =
      restrictionCochain U S.X₃ t)
    (ω : CechCochains.Cochain U (abSections S.X₁) 1)
    (hω : CechCochains.cechD U (abSections S.X₁) 1 ω = 0)
    (hωs : Stacks.Cohomology.CechOne.push U ((SheafOfModules.toSheaf _).map S.f).hom 1 ω =
      CechCochains.cechD U (abSections S.X₂) 0 s) :
    boundary O (singlePlusSC O S) (shortExact_singlePlusSC O hS) 0 (0 + 1) rfl
        (sectionClass S.X₃ t) = cechCocycleClass U hU S.X₁ ω hω := by
  have key := ConcreteCategory.congr_hom
    (boundary_sectionClass_aux U hU hS t s hs ω hω hωs) (1 : SectionRing (ringSheaf O) ⊤)
  have e3 : sectionClass S.X₃ t = (cocycleClass 0 (cochainZero₃ U hU (restrictionCochain U S.X₃ t))
        (cochainZero₃_d U hU _ (cechD_restrictionCochain U S.X₃ t)) ≫
      cechClass O U hU (singlePlusSC O S).X₃ 0) (1 : SectionRing (ringSheaf O) ⊤) :=
    (cechCocycleClass_restrictionCochain U hU S.X₃ t).symm
  rw [e3]
  exact key.symm

end Boundary

/-! ### The boundary map when the middle term is acyclic -/

section BoundaryBijective

attribute [local instance] HasDerivedCategory.standard
attribute [local instance] CategoryTheory.Functor.commShiftRightDerivedFunctorPlus

variable (O) in
/-- **Exactness of `Hⁿ(X, K₃) ⟶ Hⁿ⁺¹(X, K₁) ⟶ Hⁿ⁺¹(X, K₂)`.** -/
theorem exists_boundary_eq
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n : ℤ) (y : hypercohomology O S.X₁ (n + 1))
    (hy : hypercohomologyMap O S.f (n + 1) y = 0) :
    ∃ a : hypercohomology O S.X₃ n, boundary O S hS n (n + 1) rfl a = y := by
  have hex := DerivedCategory.HomologySequence.exact₁ _ (derivedTriangle_distinguished O S hS)
    n (n + 1) rfl
  rw [ShortComplex.moduleCat_exact_iff] at hex
  obtain ⟨a, ha⟩ := hex y hy
  exact ⟨a, by rw [boundary_eq]; exact ha⟩

variable (O) in
/-- **The boundary map is bijective when the middle term has no cohomology in the two degrees
involved.** -/
theorem bijective_boundary_of_isZero
    (S : ShortComplex (CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))))
    (hS : (toSC S).ShortExact) (n : ℤ) (h₀ : IsZero (hypercohomology O S.X₂ n))
    (h₁ : IsZero (hypercohomology O S.X₂ (n + 1))) :
    Function.Bijective (boundary O S hS n (n + 1) rfl) := by
  refine ⟨(injective_iff_map_eq_zero _).2 fun b hb => ?_, fun y => ?_⟩
  · obtain ⟨x, rfl⟩ := exact_boundary O S hS n b hb
    have := ModuleCat.subsingleton_of_isZero h₀
    rw [Subsingleton.elim x 0, map_zero]
  · have := ModuleCat.subsingleton_of_isZero h₁
    exact exists_boundary_eq O S hS n y (Subsingleton.elim _ _)

end BoundaryBijective

/-! ### Čech cohomology computing cohomology for the terms of a sheaf placed in degree zero -/

section CechComputesTerms

variable (O) in
/-- Čech cohomology computing cohomology is invariant under isomorphism of sheaves. -/
theorem cechComputesSheaf_of_iso {F G : SheafOfModules.{u} (ringSheaf O)} (e : F ≅ G)
    (h : CechComputesSheaf O F) : CechComputesSheaf O G := fun n =>
  cechSurjAt_cechInjAt_of_iso O
    (ObjectProperty.isoMk _ ((HomologicalComplex.single _ (up ℤ) 0).mapIso e)) n (h n)

variable (O) in
/-- **Čech cohomology computes the cohomology of a zero sheaf**: both vanish. -/
theorem cechComputesSheaf_of_isZero {F : SheafOfModules.{u} (ringSheaf O)} (hF : IsZero F) :
    CechComputesSheaf O F := fun n => by
  have : (singlePlus O F 0).obj.IsStrictlyGE (n + 1) := ⟨fun i _ => by
    by_cases hi : i = 0
    · subst hi
      exact IsZero.of_iso hF (HomologicalComplex.singleObjXSelf (up ℤ) 0 F)
    · exact HomologicalComplex.isZero_single_obj_X (up ℤ) 0 F i hi⟩
  exact cechSurjAt_cechInjAt_of_lt O (singlePlus O F 0) (n + 1) n (by omega)

variable (O) in
/-- Čech cohomology computes the cohomology of every term of a sheaf placed in degree zero, as
soon as it computes the cohomology of the sheaf. -/
theorem cechComputesSheaf_singlePlus_X {F : SheafOfModules.{u} (ringSheaf O)}
    (hF : CechComputesSheaf O F) (p : ℤ) : CechComputesSheaf O ((singlePlus O F 0).obj.X p) := by
  by_cases hp : p = 0
  · subst hp
    exact cechComputesSheaf_of_iso O (HomologicalComplex.singleObjXSelf (up ℤ) 0 F).symm hF
  · exact cechComputesSheaf_of_isZero O (HomologicalComplex.isZero_single_obj_X (up ℤ) 0 F p hp)

end CechComputesTerms

end Stacks.Cech.Hypercohomology
