module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologySingleCochains
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyTruncationPairing

/-!
# Čech cochains of a sheaf placed in an arbitrary degree

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings, `ℱ` a sheaf of
`𝒪_X`-modules, `a` an integer and `𝒰 = (Uᵢ)` an open covering of `X`. A Čech `p`-cochain of `ℱ`
in the explicit model of [Stacks, Tag 01FJ] is a cochain of degree `p + a` of the total Čech
complex of `ℱ` placed in degree `a`: the total complex of a single complex has a single summand
in each degree, and its differential there is the Čech differential. This file records that
inclusion, its compatibility with differentials, morphisms of sheaves and refinement, and the
resulting classes of Čech cocycles in `H^{p+a}(X, ℱ[-a])`. In degree `a = 0` these are the
classes `Stacks.Cech.Hypercohomology.cechCocycleClass`.

## Main definitions

* `Stacks.Cech.Hypercohomology.cochainOfAt`: the cochain of the total Čech complex of `ℱ[-a]`
  attached to an explicit Čech cochain.
* `Stacks.Cech.Hypercohomology.cechCocycleClassAt`: the class in `H^{p+a}(X, ℱ[-a])` of an
  explicit Čech `p`-cocycle.

## References

* [Stacks Project, Tag 01FJ](https://stacks.math.columbia.edu/tag/01FJ)
* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing sectionsPresheafFunctor sectionsPresheaf coverObject
  abSections)
open Stacks.Cech.LinearCupProduct (cechCochainsMap ιTotalCechTo)

universe u w uC vC

namespace Stacks.Cech.LinearCupProduct

open Stacks.Cech.CupProduct (tensorModules tensorModulesMap)

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

variable {C : Type uC} [Category.{vC} C] {_ : HasFiniteProducts C} {ι : Type w} [UnivLE.{w, u}]
  (W : ι → C) (R : Type u) {_ : CommRing R} {K L M : CochainComplex (PresheafModules.{u} C R) ℤ}

/-- **The Čech cup product on two homogeneous summands**, precomposed with arbitrary maps into the
Čech cochains: `(-1)^{as}` times the Alexander–Whitney map of the pairing in bidegree `(a, b)`. -/
@[reassoc]
theorem tensorModulesMap_ιTotalCechTo_cechCupProduct (D : ComplexPairing R K L M)
    {P Q : ModuleCat.{u} R} {r s : ℕ} {a b : ℤ} (z : P ⟶ cechCochains W R (K.X a) r)
    (w : Q ⟶ cechCochains W R (L.X b) s) (p q n : ℤ) (hp : (r : ℤ) + a = p)
    (hq : (s : ℤ) + b = q) (hn : p + q = n) :
    tensorModulesMap R (z ≫ ιTotalCechTo W R K r a p hp) (w ≫ ιTotalCechTo W R L s b q hq) ≫
        HomologicalComplex.ιMapBifunctor ((totalCechComplexFunctor W R).obj K)
          ((totalCechComplexFunctor W R).obj L) (tensorModules R) (up ℤ) p q n hn ≫
        (cechCupProduct W R D).f n =
      (((a * s).negOnePow : ℤ)) • (tensorModulesMap R z w ≫
        cechAlexanderWhitney W R (D.μ a b (a + b) rfl) r s ≫
        ιTotalCechTo W R M (r + s) (a + b) n (by push_cast; omega)) := by
  have h1 := ιTensorSource_eq W R K L r s a b p q n hp hq hn
  have h2 := ιTensorSource_cechCupProductDegree W R D r s a b n (by omega)
  rw [cechCupProductSummand_eq] at h2
  rw [← Stacks.Cech.CupProduct.tensorModulesMap_comp R z _ w _, Category.assoc, reassoc_of% h1]
  refine (congrArg (fun φ => tensorModulesMap R z w ≫ φ) h2).trans ?_
  rw [Preadditive.comp_zsmul]
  rfl

/-- **The Čech cup product of two homogeneous cochains**, written with `cupPair`: `(-1)^{as}` times
the Alexander–Whitney map of the pairing in bidegree `(a, b)`. -/
theorem cupPair_ιTotalCechTo_cechCupProduct (D : ComplexPairing R K L M)
    {P Q : ModuleCat.{u} R} {r s : ℕ} {a b : ℤ} (z : P ⟶ cechCochains W R (K.X a) r)
    (w : Q ⟶ cechCochains W R (L.X b) s) (p q n : ℤ) (hp : (r : ℤ) + a = p)
    (hq : (s : ℤ) + b = q) (hn : p + q = n) :
    Stacks.CupProduct.cupPair (tensorModules R) ((totalCechComplexFunctor W R).obj K)
        ((totalCechComplexFunctor W R).obj L) p q n hn (z ≫ ιTotalCechTo W R K r a p hp)
        (w ≫ ιTotalCechTo W R L s b q hq) ≫ (cechCupProduct W R D).f n =
      (((a * s).negOnePow : ℤ)) • (tensorModulesMap R z w ≫
        cechAlexanderWhitney W R (D.μ a b (a + b) rfl) r s ≫
        ιTotalCechTo W R M (r + s) (a + b) n (by push_cast; omega)) := by
  rw [Stacks.CupProduct.cupPair]
  simp only [Category.assoc]
  rw [tensorModules_map_app_comp_map_assoc]
  exact tensorModulesMap_ιTotalCechTo_cechCupProduct W R D z w p q n hp hq hn

end Stacks.Cech.LinearCupProduct

namespace Stacks.Cech.Hypercohomology

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize
attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing
attribute [local implicit_reducible] CechCochains.Cochain

variable {X : TopCat.{u}} {O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u}}
  {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i) (F : SheafOfModules.{u} (ringSheaf O))
  (a : ℤ)

/-- The sections of a sheaf placed in degree `a`, as a complex of presheaves of modules. -/
abbrev sectionsKAt : CochainComplex (Stacks.Cech.LinearCupProduct.PresheafModules.{u}
    (Over (⊤ : Opens X)) (SectionRing (ringSheaf O) ⊤)) ℤ :=
  (Stacks.Cech.Refinement.sectionsComplex O).obj (singlePlus O F a).obj

/-- **The cochain of the total Čech complex attached to an explicit Čech cochain**, placed in
Čech degree `p` and coefficient degree `a` of the total Čech complex of the sections of `ℱ`
placed in degree `a`, at a total degree `n = p + a`. -/
def cochainOfAtTo {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) (n : ℤ)
    (h : (p : ℤ) + a = n) :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤)).obj (sectionsKAt F a)).X n :=
  sliceMor U hU F c ≫
    cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
      (singleXIsoAt O F a a rfl).inv p ≫
    ιTotalCechTo (coverObject U hU) (SectionRing (ringSheaf O) ⊤) (sectionsKAt F a) p a n h

theorem cochainOfAtTo_d {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) (n : ℤ)
    (h : (p : ℤ) + a = n) :
    cochainOfAtTo U hU F a c n h ≫ ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor
      (coverObject U hU) (SectionRing (ringSheaf O) ⊤)).obj (sectionsKAt F a)).d n (n + 1) =
      cochainOfAtTo U hU F a (CechCochains.cechD U (abSections F) p c) (n + 1)
        (by push_cast; omega) := by
  have h0 : cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
      ((sectionsKAt F a).d a (a + 1)) p = 0 := by
    rw [sectionsComplex_singlePlus_d_at]
    change ((CategoryTheory.cechComplexFunctor (coverObject U hU)).map (0 : _ ⟶ _)).f p = 0
    rw [Functor.map_zero]
    rfl
  have hd := Stacks.Cech.LinearCupProduct.ιTotalCechTo_d (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤) (sectionsKAt F a) p a n h
  have hm := Stacks.Cech.LinearCupProduct.cechCochainsMap_d (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤) (singleXIsoAt O F a a rfl).inv p
  unfold cochainOfAtTo
  rw [Category.assoc, Category.assoc, hd, h0,
    Limits.zero_comp, smul_zero, add_zero, reassoc_of% hm, ← Category.assoc, sliceMor_cechD]

/-- The attached cochains commute with the differentials, at arbitrary total degrees. -/
theorem cochainOfAtTo_d' {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) (n n' : ℤ)
    (h : (p : ℤ) + a = n) (h' : ((p + 1 : ℕ) : ℤ) + a = n') :
    cochainOfAtTo U hU F a c n h ≫ ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor
      (coverObject U hU) (SectionRing (ringSheaf O) ⊤)).obj (sectionsKAt F a)).d n n' =
      cochainOfAtTo U hU F a (CechCochains.cechD U (abSections F) p c) n' h' := by
  obtain rfl : n' = n + 1 := by push_cast at h'; omega
  exact cochainOfAtTo_d U hU F a c n h

theorem cochainOfAtTo_add {p : ℕ} (c c' : CechCochains.Cochain U (abSections F) p) (n : ℤ)
    (h : (p : ℤ) + a = n) :
    cochainOfAtTo U hU F a (c + c') n h =
      cochainOfAtTo U hU F a c n h + cochainOfAtTo U hU F a c' n h := by
  unfold cochainOfAtTo
  rw [sliceMor_add, Preadditive.add_comp]

theorem cochainOfAtTo_zero {p : ℕ} (n : ℤ) (h : (p : ℤ) + a = n) :
    cochainOfAtTo U hU F a (0 : CechCochains.Cochain U (abSections F) p) n h = 0 := by
  unfold cochainOfAtTo
  rw [sliceMor_zero, Limits.zero_comp]

/-- **The cochain of the total Čech complex of `ℱ[-a]` attached to an explicit Čech
`p`-cochain**, in total degree `p + a`. -/
def cochainOfAt {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      ((cech O U hU).obj (singlePlus O F a).obj).X ((p : ℤ) + a) :=
  cochainOfAtTo U hU F a c ((p : ℤ) + a) rfl

/-- **The attached cochains commute with the differentials.** -/
theorem cochainOfAt_d {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    cochainOfAt U hU F a c ≫ ((cech O U hU).obj (singlePlus O F a).obj).d ((p : ℤ) + a)
        (((p + 1 : ℕ) : ℤ) + a) =
      cochainOfAt U hU F a (CechCochains.cechD U (abSections F) p c) :=
  cochainOfAtTo_d' U hU F a c _ _ rfl rfl

theorem cochainOfAt_add {p : ℕ} (c c' : CechCochains.Cochain U (abSections F) p) :
    cochainOfAt U hU F a (c + c') = cochainOfAt U hU F a c + cochainOfAt U hU F a c' :=
  cochainOfAtTo_add U hU F a c c' _ rfl

theorem cochainOfAt_zero {p : ℕ} :
    cochainOfAt U hU F a (0 : CechCochains.Cochain U (abSections F) p) = 0 :=
  cochainOfAtTo_zero U hU F a _ rfl

/-- The cochain attached to a Čech cocycle is a cocycle. -/
theorem cochainOfAt_d_eq_zero {p : ℕ} (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    cochainOfAt U hU F a c ≫ ((cech O U hU).obj (singlePlus O F a).obj).d ((p : ℤ) + a)
      ((p : ℤ) + a + 1) = 0 := by
  have hd := cochainOfAtTo_d U hU F a c ((p : ℤ) + a) rfl
  rw [hc, cochainOfAtTo_zero] at hd
  exact hd

/-! ### Naturality in the sheaf -/

section Naturality

variable (O) in
/-- A morphism of sheaves of modules placed in degree `a`. -/
def singlePlusMapAt {F G : SheafOfModules.{u} (ringSheaf O)} (f : F ⟶ G) (a : ℤ) :
    singlePlus O F a ⟶ singlePlus O G a :=
  ObjectProperty.homMk ((HomologicalComplex.single _ (up ℤ) a).map f)

/-- In degree zero, a morphism placed in degree `a` is the morphism placed in degree zero. -/
theorem singlePlusMapAt_zero {F G : SheafOfModules.{u} (ringSheaf O)} (f : F ⟶ G) :
    singlePlusMapAt O f 0 = singlePlusMap O f :=
  rfl

/-- Placing the identification of two equal sheaves in a degree gives the identification of the
two shifted sheaves. -/
theorem singlePlusMapAt_eqToHom {F G : SheafOfModules.{u} (ringSheaf O)} (h : F = G) :
    singlePlusMapAt O (eqToHom h) a = eqToHom (congrArg (fun F => singlePlus O F a) h) := by
  subst h
  exact ObjectProperty.hom_ext _ ((HomologicalComplex.single _ (up ℤ) a).map_id F)

variable {F} {G : SheafOfModules.{u} (ringSheaf O)} (f : F ⟶ G)

theorem singleXIsoAt_inv_naturality :
    (singleXIsoAt O F a a rfl).inv ≫ ((Stacks.Cech.Refinement.sectionsComplex O).map
      (singlePlusMapAt O f a).hom).f a =
      (sectionsPresheafFunctor ⊤).map f ≫ (singleXIsoAt O G a a rfl).inv := by
  change (sectionsPresheafFunctor ⊤).map _ ≫ (sectionsPresheafFunctor ⊤).map _ =
    (sectionsPresheafFunctor ⊤).map _ ≫ (sectionsPresheafFunctor ⊤).map _
  rw [← Functor.map_comp, ← Functor.map_comp]
  congr 1
  change (HomologicalComplex.singleObjXSelf (up ℤ) a F).inv ≫
    ((HomologicalComplex.single _ (up ℤ) a).map f).f a =
      f ≫ (HomologicalComplex.singleObjXSelf (up ℤ) a G).inv
  rw [HomologicalComplex.single_map_f_self, Iso.inv_hom_id_assoc]

theorem cochainOfAtTo_map {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) (n : ℤ)
    (h : (p : ℤ) + a = n) :
    cochainOfAtTo U hU F a c n h ≫ ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor
      (coverObject U hU) (SectionRing (ringSheaf O) ⊤)).map
        ((Stacks.Cech.Refinement.sectionsComplex O).map (singlePlusMapAt O f a).hom)).f n =
      cochainOfAtTo U hU G a (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map f).hom p c) n h := by
  have hι := Stacks.Cech.LinearCupProduct.ιTotalCechTo_totalCechComplexFunctor_map
    (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
    ((Stacks.Cech.Refinement.sectionsComplex O).map (singlePlusMapAt O f a).hom) p a n h
  have hc := congrArg (fun φ => cechCochainsMap (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤) φ p) (singleXIsoAt_inv_naturality a f)
  simp only [Stacks.Cech.LinearCupProduct.cechCochainsMap_comp] at hc
  unfold cochainOfAtTo
  rw [Category.assoc, Category.assoc, hι, reassoc_of% hc, ← Category.assoc, sliceMor_map]

/-- The attached cochains are natural in the sheaf. -/
theorem cochainOfAt_map {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    cochainOfAt U hU F a c ≫ ((cech O U hU).map (singlePlusMapAt O f a).hom).f ((p : ℤ) + a) =
      cochainOfAt U hU G a (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map f).hom p c) :=
  cochainOfAtTo_map U hU a f c _ rfl

end Naturality

/-! ### Refinement -/

section Refinement

variable {J : Type u} (V : J → Opens X) (hV : ⊤ = ⨆ j, V j) (r : J → I)
  (hr : ∀ j, V j ≤ U (r j))

/-- **The attached cochains commute with refinement.** -/
theorem cochainOfAtTo_refinement {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) (n : ℤ)
    (h : (p : ℤ) + a = n) :
    cochainOfAtTo U hU F a c n h ≫
      ((Stacks.Cech.LinearCupProduct.totalCechRefinement (coverObject U hU) (coverObject V hV)
        (SectionRing (ringSheaf O) ⊤) r
        (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr)).app (sectionsKAt F a)).f n =
      cochainOfAtTo V hV F a (CechCochains.refinementMap U V r hr (abSections F) p c) n h := by
  have hn : cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
      (singleXIsoAt O F a a rfl).inv p ≫ (Stacks.Cech.LinearCupProduct.cechRefinement
        (coverObject U hU) (coverObject V hV) (SectionRing (ringSheaf O) ⊤) r
        (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr) ((sectionsKAt F a).X a)).f p =
      (Stacks.Cech.LinearCupProduct.cechRefinement (coverObject U hU) (coverObject V hV)
        (SectionRing (ringSheaf O) ⊤) r
        (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr) (sectionsP O F)).f p ≫
      cechCochainsMap (coverObject V hV) (SectionRing (ringSheaf O) ⊤)
        (singleXIsoAt O F a a rfl).inv p :=
    (HomologicalComplex.comp_f _ _ p).symm.trans ((congrArg (fun φ => HomologicalComplex.Hom.f φ p)
      (Stacks.Cech.LinearCupProduct.cechRefinement_naturality (coverObject U hU)
        (coverObject V hV) (SectionRing (ringSheaf O) ⊤) r
        (Stacks.Cech.Refinement.coverRefinementHom U hU V hV r hr)
        (singleXIsoAt O F a a rfl).inv)).trans (HomologicalComplex.comp_f _ _ p))
  unfold cochainOfAtTo
  rw [Category.assoc, Category.assoc, ιTotalCechTo_totalCechRefinement U hU V hV r hr,
    reassoc_of% hn, ← Category.assoc, sliceMor_refinement]

/-- **The attached cochains commute with refinement**, in the total Čech complex of `ℱ[-a]`. -/
theorem cochainOfAt_refinement {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    cochainOfAt U hU F a c ≫
      ((Stacks.Cech.Refinement.cechRefinement O U hU V hV r hr).app
        (singlePlus O F a).obj).f ((p : ℤ) + a) =
      cochainOfAt V hV F a (CechCochains.refinementMap U V r hr (abSections F) p c) :=
  cochainOfAtTo_refinement U hU F a V hV r hr c _ rfl

end Refinement

/-! ### The classes of Čech cocycles -/

/-- **The class in `H^{p+a}(X, ℱ[-a])` of a Čech `p`-cocycle** of an open covering, through the
comparison of the total Čech complex with derived global sections. -/
def cechCocycleClassAt {p : ℕ} (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    hypercohomology O (singlePlus O F a) ((p : ℤ) + a) :=
  cechClass O U hU (singlePlus O F a) ((p : ℤ) + a)
    (cocycleClass ((p : ℤ) + a) (cochainOfAt U hU F a c) (cochainOfAt_d_eq_zero U hU F a c hc)
      (1 : SectionRing (ringSheaf O) ⊤))

/-- The class of a Čech cocycle depends only on the cocycle. -/
theorem cechCocycleClassAt_congr {p : ℕ} {c c' : CechCochains.Cochain U (abSections F) p}
    (h : c = c') (hc : CechCochains.cechD U (abSections F) p c = 0)
    (hc' : CechCochains.cechD U (abSections F) p c' = 0) :
    cechCocycleClassAt U hU F a c hc = cechCocycleClassAt U hU F a c' hc' := by
  subst h
  rfl

/-- **In degree zero the classes are those of `Stacks.Cech.Hypercohomology.cechCocycleClass`.** -/
theorem cechCocycleClassAt_zero {p : ℕ} (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    cechCocycleClassAt U hU F 0 c hc = cechCocycleClass U hU F c hc :=
  rfl

/-- **Čech cocycles differing by a coboundary have the same class.** -/
theorem cechCocycleClassAt_eq_of_eq_add {q : ℕ}
    (c c' : CechCochains.Cochain U (abSections F) (q + 1))
    (hc : CechCochains.cechD U (abSections F) (q + 1) c = 0)
    (hc' : CechCochains.cechD U (abSections F) (q + 1) c' = 0)
    (t : CechCochains.Cochain U (abSections F) q)
    (ht : c = c' + CechCochains.cechD U (abSections F) q t) :
    cechCocycleClassAt U hU F a c hc = cechCocycleClassAt U hU F a c' hc' := by
  have hx : cochainOfAt U hU F a c = cochainOfAt U hU F a c' + cochainOfAt U hU F a t ≫
      ((cech O U hU).obj (singlePlus O F a).obj).d ((q : ℤ) + a) (((q + 1 : ℕ) : ℤ) + a) := by
    rw [ht, cochainOfAt_add]
    exact congrArg _ (cochainOfAt_d U hU F a t).symm
  have hi : (up ℤ).prev (((q + 1 : ℕ) : ℤ) + a) = (q : ℤ) + a := by
    rw [CochainComplex.prev]; push_cast; ring
  unfold cechCocycleClassAt cocycleClass
  rw [Stacks.CupProduct.liftCycles_homologyπ_eq_of_eq_add_comp_d _ ((q : ℤ) + a) _ _
    hi (CochainComplex.next ℤ _) _ _ _ _ _ hx]

/-- **A Čech coboundary has class zero.** -/
theorem cechCocycleClassAt_eq_zero {q : ℕ} (t : CechCochains.Cochain U (abSections F) q)
    (c : CechCochains.Cochain U (abSections F) (q + 1))
    (hc : CechCochains.cechD U (abSections F) (q + 1) c = 0)
    (ht : CechCochains.cechD U (abSections F) q t = c) :
    cechCocycleClassAt U hU F a c hc = 0 := by
  have hx : cochainOfAt U hU F a c = cochainOfAt U hU F a t ≫
      ((cech O U hU).obj (singlePlus O F a).obj).d ((q : ℤ) + a) (((q + 1 : ℕ) : ℤ) + a) := by
    rw [cochainOfAt_d, ht]
  have h0 : cocycleClass (((q + 1 : ℕ) : ℤ) + a) (cochainOfAt U hU F a c)
      (cochainOfAt_d_eq_zero U hU F a c hc) = 0 :=
    HomologicalComplex.liftCycles_homologyπ_eq_zero_of_boundary _ _ _ _ _ hx
  unfold cechCocycleClassAt
  rw [h0]
  exact map_zero _

/-- **The class of a Čech cocycle is additive in the cocycle.** -/
theorem cechCocycleClassAt_add {p : ℕ} (c c' : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0)
    (hc' : CechCochains.cechD U (abSections F) p c' = 0) :
    cechCocycleClassAt U hU F a (c + c') (by rw [map_add, hc, hc', add_zero]) =
      cechCocycleClassAt U hU F a c hc + cechCocycleClassAt U hU F a c' hc' := by
  unfold cechCocycleClassAt
  rw [cocycleClass_congr _ (cochainOfAt_add U hU F a c c') _
    (by rw [Preadditive.add_comp, cochainOfAt_d_eq_zero U hU F a c hc,
      cochainOfAt_d_eq_zero U hU F a c' hc', add_zero]),
    cocycleClass_add _ _ _ (cochainOfAt_d_eq_zero U hU F a c hc)
      (cochainOfAt_d_eq_zero U hU F a c' hc')]
  simp only [ModuleCat.hom_add, LinearMap.add_apply, map_add]

/-- **The class of a Čech cocycle is unchanged by refinement.** -/
theorem cechCocycleClassAt_refinement {J : Type u} (V : J → Opens X) (hV : ⊤ = ⨆ j, V j)
    (r : J → I) (hr : ∀ j, V j ≤ U (r j)) {p : ℕ}
    (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    cechCocycleClassAt V hV F a (CechCochains.refinementMap U V r hr (abSections F) p c)
        (by rw [← CechCochains.refinementMap_cechD, hc, map_zero]) =
      cechCocycleClassAt U hU F a c hc := by
  have href := cechClass_refinement O U hU V hV r hr (singlePlus O F a) ((p : ℤ) + a)
  symm
  unfold cechCocycleClassAt
  rw [← href, ConcreteCategory.comp_apply, ← ConcreteCategory.comp_apply (cocycleClass _ _ _),
    cocycleClass_comp_homologyMap]
  congr 2
  exact congrArg ConcreteCategory.hom (cocycleClass_congr _
    (cochainOfAt_refinement U hU F a V hV r hr c) _ _)

variable {F} in
/-- **The class of a Čech cocycle is natural in the sheaf.** -/
theorem hypercohomologyMap_cechCocycleClassAt {G : SheafOfModules.{u} (ringSheaf O)}
    (f : F ⟶ G) {p : ℕ} (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0) :
    hypercohomologyMap O (singlePlusMapAt O f a) ((p : ℤ) + a) (cechCocycleClassAt U hU F a c hc) =
      cechCocycleClassAt U hU G a (Stacks.Cohomology.CechOne.push U
        ((SheafOfModules.toSheaf _).map f).hom p c)
        (by rw [← Stacks.Cohomology.CechOne.push_cechD, hc, map_zero]) := by
  unfold cechCocycleClassAt
  rw [← ConcreteCategory.comp_apply, ← cechClass_naturality, ConcreteCategory.comp_apply,
    ← ConcreteCategory.comp_apply (cocycleClass _ _ _), cocycleClass_comp_homologyMap]
  congr 2
  exact congrArg ConcreteCategory.hom (cocycleClass_congr _ (cochainOfAt_map U hU a f c) _ _)

/-! ### Every cocycle of the total Čech complex of a single complex is explicit -/

section Representability

/-- **A bicomplex concentrated in second degree `a`**: the inclusion of the summand `(p, a)` into
the total complex in degree `n = p + a` is an isomorphism. -/
theorem isIso_ιTotal_of_isZero_ne {A : Type*} [Category* A] [Preadditive A]
    (B : HomologicalComplex₂ A (up ℤ) (up ℤ)) [B.HasTotal (up ℤ)] (a : ℤ)
    (hB : ∀ p q : ℤ, q ≠ a → IsZero ((B.X p).X q)) (p n : ℤ) (h : p + a = n) :
    IsIso (B.ιTotal (up ℤ) p a n h) := by
  refine ⟨B.totalDesc (fun p' q h' => if hq : q = a then
    eqToHom (by
      obtain rfl := hq
      obtain rfl : p' = p := by change p' + q = n at h'; omega
      rfl) else 0), ?_, ?_⟩
  · rw [HomologicalComplex₂.ι_totalDesc, dif_pos rfl, eqToHom_refl]
  · refine HomologicalComplex₂.total.hom_ext (up ℤ) (fun p' q h' => ?_)
    rw [HomologicalComplex₂.ι_totalDesc_assoc, Category.comp_id]
    by_cases hq : q = a
    · subst hq
      obtain rfl : p' = p := by change p' + q = n at h'; omega
      rw [dif_pos rfl, eqToHom_refl, Category.id_comp]
    · exact (hB p' q hq).eq_of_src _ _

/-- The inclusion of the Čech cochains of `ℱ` into the total Čech complex of `ℱ[-a]` in total
degree `p + a` is an isomorphism. -/
theorem isIso_ιTotalCechTo_sectionsKAt {p : ℕ} (n : ℤ) (h : (p : ℤ) + a = n) :
    IsIso (ιTotalCechTo (coverObject U hU) (SectionRing (ringSheaf O) ⊤) (sectionsKAt F a)
      p a n h) := by
  have : IsIso ((Stacks.Cech.LinearCupProduct.totalCechBicomplex (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (sectionsKAt F a)).ιTotal (up ℤ) p a n h) :=
    isIso_ιTotal_of_isZero_ne _ a (fun p' q hq => by
      have hz : IsZero ((sectionsKAt F a).X q) :=
        (sectionsPresheafFunctor (R := ringSheaf O) (⊤ : Opens X)).map_isZero
          (HomologicalComplex.isZero_single_obj_X (up ℤ) a F q hq)
      exact (HomologicalComplex.eval _ _ p').map_isZero
        ((Stacks.Cech.LinearCupProduct.cechComplexFunctorInt (coverObject U hU)
          (SectionRing (ringSheaf O) ⊤)).map_isZero hz)) p n h
  unfold ιTotalCechTo
  exact IsIso.comp_isIso' inferInstance this

/-- The cochain of `sliceCochain` of the explicit cochain of a cochain is that cochain. -/
theorem sliceCochain_toCochainFun {p : ℕ}
    (s : ToType (((CategoryTheory.cechComplexFunctor (coverObject U hU)).obj
      (sectionsPresheaf ⊤ F)).X p)) :
    sliceCochain U hU F (Stacks.Cohomology.CechSheaf.toCochainFun ⊤ U hU F s) = s :=
  Stacks.Cohomology.CechSheaf.toCochainFun_injective ⊤ U hU F
    (toCochainFun_sliceCochain U hU F _)

/-- **Every morphism out of the ring into the total Čech complex of `ℱ[-a]` in degree `p + a`
is the cochain attached to an explicit Čech cochain.** -/
theorem exists_cochainOfAtTo_eq {p : ℕ} (n : ℤ) (h : (p : ℤ) + a = n)
    (z : unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤)).obj (sectionsKAt F a)).X n) :
    ∃ c : CechCochains.Cochain U (abSections F) p, cochainOfAtTo U hU F a c n h = z := by
  have := isIso_ιTotalCechTo_sectionsKAt U hU F a n h
  let w := z ≫ inv (ιTotalCechTo (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
    (sectionsKAt F a) p a n h) ≫ cechCochainsMap (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (singleXIsoAt O F a a rfl).hom p
  refine ⟨Stacks.Cohomology.CechSheaf.toCochainFun ⊤ U hU F (w (1 : SectionRing _ ⊤)), ?_⟩
  have hw : sliceMor U hU F (Stacks.Cohomology.CechSheaf.toCochainFun ⊤ U hU F
      (w (1 : SectionRing _ ⊤))) = w := by
    unfold sliceMor
    refine Eq.trans ?_ (toMor_apply w)
    exact congrArg (toMor (M := Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (sectionsP O F) p)) (sliceCochain_toCochainFun U hU F _)
  have hiso : cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
        (singleXIsoAt O F a a rfl).hom p ≫ cechCochainsMap (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤) (singleXIsoAt O F a a rfl).inv p = 𝟙 _ := by
    exact ((HomologicalComplex.eval _ _ p).mapIso ((CategoryTheory.cechComplexFunctor
      (coverObject U hU)).mapIso (singleXIsoAt O F a a rfl))).hom_inv_id
  unfold cochainOfAtTo
  rw [hw]
  simp only [w, Category.assoc, reassoc_of% hiso, IsIso.inv_hom_id, Category.comp_id]

/-- The two maps of Čech cochains induced by the identification of the term of `ℱ[-a]` in degree
`a` are inverse to each other. -/
theorem cechCochainsMap_singleXIsoAt_inv_hom (p : ℕ) :
    cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
        (singleXIsoAt O F a a rfl).inv p ≫ cechCochainsMap (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤) (singleXIsoAt O F a a rfl).hom p = 𝟙 _ :=
  ((HomologicalComplex.eval _ _ p).mapIso ((CategoryTheory.cechComplexFunctor
    (coverObject U hU)).mapIso (singleXIsoAt O F a a rfl))).inv_hom_id

/-- **The attached cochains determine the explicit cochain.** -/
theorem cochainOfAtTo_injective {p : ℕ} (n : ℤ) (h : (p : ℤ) + a = n)
    {c c' : CechCochains.Cochain U (abSections F) p}
    (hcc : cochainOfAtTo U hU F a c n h = cochainOfAtTo U hU F a c' n h) : c = c' := by
  have := isIso_ιTotalCechTo_sectionsKAt U hU F a n h
  unfold cochainOfAtTo at hcc
  rw [cancel_mono] at hcc
  have h3 : sliceCochain U hU F c = sliceCochain U hU F c' := by
    have h4 := congrArg (fun f : unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤) (sectionsP O F) p => f (1 : SectionRing (ringSheaf O) ⊤)) hcc
    exact ((toMor_apply_one (M := Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (sectionsP O F) p) _).symm.trans h4).trans
      (toMor_apply_one (M := Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (sectionsP O F) p) _)
  rw [← toCochainFun_sliceCochain U hU F c, ← toCochainFun_sliceCochain U hU F c', h3]

/-- The cochain attached to an explicit Čech cochain is a cocycle exactly when the explicit
cochain is a Čech cocycle. -/
theorem cechD_eq_zero_of_cochainOfAtTo {p : ℕ} (n : ℤ) (h : (p : ℤ) + a = n)
    (c : CechCochains.Cochain U (abSections F) p)
    (hz : cochainOfAtTo U hU F a c n h ≫ ((Stacks.Cech.LinearCupProduct.totalCechComplexFunctor
      (coverObject U hU) (SectionRing (ringSheaf O) ⊤)).obj (sectionsKAt F a)).d n (n + 1) = 0) :
    CechCochains.cechD U (abSections F) p c = 0 := by
  rw [cochainOfAtTo_d] at hz
  exact cochainOfAtTo_injective U hU F a (n + 1) (by push_cast; omega)
    (hz.trans (cochainOfAtTo_zero U hU F a _ _).symm)

/-- **When Čech cohomology computes the cohomology of `ℱ[-a]`, every class of `H^{p+a}(X, ℱ[-a])`
is the class of an explicit Čech cocycle on some open covering.** -/
theorem exists_cechCocycleClassAt_eq (hF : CechComputes O (singlePlus O F a)) (p : ℕ)
    (x : hypercohomology O (singlePlus O F a) ((p : ℤ) + a)) :
    ∃ (J : Type u) (V : J → Opens X) (hV : ⊤ = ⨆ j, V j)
      (c : CechCochains.Cochain V (abSections F) p)
      (hc : CechCochains.cechD V (abSections F) p c = 0),
      cechCocycleClassAt V hV F a c hc = x := by
  obtain ⟨J, V, hV, z, rfl⟩ := (hF ((p : ℤ) + a)).1 x
  obtain ⟨zz, hzz, hz⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq
    ((cech O V hV).obj (singlePlus O F a).obj) ((p : ℤ) + a) _
    (CochainComplex.next ℤ _) (toMor z)
  obtain ⟨c, hc⟩ := exists_cochainOfAtTo_eq V hV F a (p := p) ((p : ℤ) + a) rfl zz
  have hc' : cochainOfAt V hV F a c = zz := hc
  have hcd : CechCochains.cechD V (abSections F) p c = 0 :=
    cechD_eq_zero_of_cochainOfAtTo V hV F a _ rfl c (by rw [hc]; exact hzz)
  refine ⟨J, V, hV, c, hcd, ?_⟩
  have e : cocycleClass ((p : ℤ) + a) (cochainOfAt V hV F a c)
      (cochainOfAt_d_eq_zero V hV F a c hcd) = toMor z :=
    (cocycleClass_congr _ hc' _ _).trans hz
  have e' : (cocycleClass ((p : ℤ) + a) (cochainOfAt V hV F a c)
      (cochainOfAt_d_eq_zero V hV F a c hcd)) (1 : SectionRing (ringSheaf O) ⊤) = z := by
    rw [e]
    exact toMor_apply_one z
  exact congrArg (cechClass O V hV (singlePlus O F a) ((p : ℤ) + a)) e'

/-- If a Čech cocycle has vanishing class, its refinement, as a cochain of the total Čech complex
of `ℱ[-a]`, becomes a coboundary after an epimorphism. -/
private theorem exists_refinement_comp_eq_of_cechCocycleClassAt_eq_zero
    (hF : CechComputes O (singlePlus O F a)) {p : ℕ} (i : ℤ)
    (hi : (up ℤ).prev ((p : ℤ) + a) = i) (c : CechCochains.Cochain U (abSections F) p)
    (hc : CechCochains.cechD U (abSections F) p c = 0)
    (h0 : cechCocycleClassAt U hU F a c hc = 0) :
    ∃ (J : Type u) (V : J → Opens X) (hV : ⊤ = ⨆ j, V j) (r : J → I) (hr : ∀ j, V j ≤ U (r j))
      (A' : ModuleCat.{u} (SectionRing (ringSheaf O) ⊤))
      (π : A' ⟶ unitModule (SectionRing (ringSheaf O) ⊤)) (_ : Epi π)
      (x₁ : A' ⟶ ((cech O V hV).obj (singlePlus O F a).obj).X i),
      π ≫ cochainOfAt V hV F a (CechCochains.refinementMap U V r hr (abSections F) p c) =
        x₁ ≫ ((cech O V hV).obj (singlePlus O F a).obj).d i ((p : ℤ) + a) := by
  obtain ⟨J, V, hV, r, hr, hρ⟩ := (hF ((p : ℤ) + a)).2 I U hU _ h0
  have hc' : CechCochains.cechD V (abSections F) p
      (CechCochains.refinementMap U V r hr (abSections F) p c) = 0 := by
    rw [← CechCochains.refinementMap_cechD, hc, map_zero]
  have hcl : cocycleClass ((p : ℤ) + a)
      (cochainOfAt V hV F a (CechCochains.refinementMap U V r hr (abSections F) p c))
      (cochainOfAt_d_eq_zero V hV F a _ hc') = 0 := by
    have e := cocycleClass_comp_homologyMap
      ((Stacks.Cech.Refinement.cechRefinement O U hU V hV r hr).app (singlePlus O F a).obj)
      ((p : ℤ) + a) (cochainOfAt U hU F a c) (cochainOfAt_d_eq_zero U hU F a c hc)
    rw [cocycleClass_congr _ (cochainOfAt_refinement U hU F a V hV r hr c) _
      (cochainOfAt_d_eq_zero V hV F a _ hc')] at e
    rw [← e]
    refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
    exact hρ
  obtain ⟨A', π, hπ, x₁, hx₁⟩ :=
    (HomologicalComplex.liftCycles_comp_homologyπ_eq_zero_iff_up_to_refinements _ _ _ _ hi
      (CochainComplex.next ℤ _) _ _).1 hcl
  exact ⟨J, V, hV, r, hr, A', π, hπ, x₁, hx₁⟩

/-- **A Čech cocycle of positive degree with vanishing class becomes an explicit Čech coboundary
on a refinement**, when Čech cohomology computes the cohomology of `ℱ[-a]`. -/
theorem exists_refinement_cechD_eq_of_cechCocycleClassAt_eq_zero
    (hF : CechComputes O (singlePlus O F a)) {q : ℕ}
    (c : CechCochains.Cochain U (abSections F) (q + 1))
    (hc : CechCochains.cechD U (abSections F) (q + 1) c = 0)
    (h0 : cechCocycleClassAt U hU F a c hc = 0) :
    ∃ (J : Type u) (V : J → Opens X) (hV : ⊤ = ⨆ j, V j) (r : J → I) (hr : ∀ j, V j ≤ U (r j))
      (t : CechCochains.Cochain V (abSections F) q),
      CechCochains.refinementMap U V r hr (abSections F) (q + 1) c =
        CechCochains.cechD V (abSections F) q t := by
  have hi : (up ℤ).prev (((q + 1 : ℕ) : ℤ) + a) = (q : ℤ) + a := by
    rw [CochainComplex.prev]; push_cast; ring
  obtain ⟨J, V, hV, r, hr, A', π, hπ, x₁, hx₁⟩ :=
    exists_refinement_comp_eq_of_cechCocycleClassAt_eq_zero U hU F a hF _ hi c hc h0
  refine ⟨J, V, hV, r, hr, ?_⟩
  obtain ⟨t, ht⟩ := exists_cochainOfAtTo_eq V hV F a (p := q) ((q : ℤ) + a) rfl
    (Projective.factorThru (𝟙 _) π ≫ x₁)
  have ht' : cochainOfAt V hV F a t = Projective.factorThru (𝟙 _) π ≫ x₁ := ht
  refine ⟨t, (cochainOfAtTo_injective V hV F a (((q + 1 : ℕ) : ℤ) + a) rfl ?_).symm⟩
  change cochainOfAt V hV F a _ = cochainOfAt V hV F a _
  rw [← cochainOfAt_d, ht', Category.assoc, ← hx₁, ← Category.assoc,
    Projective.factorThru_comp, Category.id_comp]

/-- **A Čech `0`-cocycle with vanishing class vanishes on a refinement**, when Čech cohomology
computes the cohomology of `ℱ[-a]`. -/
theorem exists_refinement_eq_zero_of_cechCocycleClassAt_eq_zero
    (hF : CechComputes O (singlePlus O F a))
    (c : CechCochains.Cochain U (abSections F) 0)
    (hc : CechCochains.cechD U (abSections F) 0 c = 0)
    (h0 : cechCocycleClassAt U hU F a c hc = 0) :
    ∃ (J : Type u) (V : J → Opens X) (hV : ⊤ = ⨆ j, V j) (r : J → I) (hr : ∀ j, V j ≤ U (r j)),
      CechCochains.refinementMap U V r hr (abSections F) 0 c = 0 := by
  have hi : (up ℤ).prev (((0 : ℕ) : ℤ) + a) = a - 1 := by
    rw [CochainComplex.prev]; push_cast; ring
  obtain ⟨J, V, hV, r, hr, A', π, hπ, x₁, hx₁⟩ :=
    exists_refinement_comp_eq_of_cechCocycleClassAt_eq_zero U hU F a hF _ hi c hc h0
  refine ⟨J, V, hV, r, hr, ?_⟩
  have hz : x₁ = 0 := (isZero_cech_X O V hV (singlePlus O F a).obj a (a - 1)
    (by omega)).eq_of_tgt _ _
  rw [hz, Limits.zero_comp] at hx₁
  have hπ0 : cochainOfAt V hV F a _ = 0 := (cancel_epi π).1 (hx₁.trans (comp_zero).symm)
  refine cochainOfAtTo_injective V hV F a (((0 : ℕ) : ℤ) + a) rfl ?_
  exact hπ0.trans (cochainOfAt_zero V hV F a).symm

end Representability

/-! ### The cup product of explicit Čech cochains -/

section Cup

variable {F} {G H : SheafOfModules.{u} (ringSheaf O)}

omit hU in
/-- Reindexing a tuple enlarges the intersection it selects. -/
theorem cechInter_le_reindex {m m' : ℕ} (x : Fin m → I) (θ : Fin m' → Fin m) :
    CechCochains.inter U x ≤ CechCochains.inter U (x ∘ θ) :=
  le_iInf fun k => iInf_le (fun k => U (x k)) (θ k)

/-- **The Alexander–Whitney cup product of explicit Čech cochains along a bilinear map**:
`(c ∪ d)_{i₀…i_{r+s}} = β(c_{i₀…i_r}, d_{i_r…i_{r+s}})`, the two factors restricted to
`U_{i₀…i_{r+s}}`. -/
def cechAWCochain (β : Stacks.BilinearMap F.val G.val H.val) {r s : ℕ}
    (c : CechCochains.Cochain U (abSections F) r) (d : CechCochains.Cochain U (abSections G) s) :
    CechCochains.Cochain U (abSections H) (r + s) := fun x =>
  β.app (op (CechCochains.inter U x))
    (Stacks.Cohomology.Basis.res (abSections F) (cechInter_le_reindex U x _)
      (c (x ∘ Stacks.Cech.LinearCupProduct.frontIdx r (r + s) (by omega))))
    (Stacks.Cohomology.Basis.res (abSections G) (cechInter_le_reindex U x _)
      (d (x ∘ Stacks.Cech.LinearCupProduct.backIdx r s (r + s) le_rfl)))

/-- The unit `1 ⊗ 1` pushed along two morphisms out of the ring is the tensor product of their
values at `1`. -/
theorem unitTensor_tensorModulesMap {M N : ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)}
    (f : unitModule (SectionRing (ringSheaf O) ⊤) ⟶ M)
    (g : unitModule (SectionRing (ringSheaf O) ⊤) ⟶ N) :
    unitTensor O ≫ Stacks.Cech.CupProduct.tensorModulesMap (SectionRing (ringSheaf O) ⊤) f g =
      toMor
        (M := ((Stacks.Cech.CupProduct.tensorModules (SectionRing (ringSheaf O) ⊤)).obj M).obj N)
        (f (1 : SectionRing (ringSheaf O) ⊤) ⊗ₜ[SectionRing (ringSheaf O) ⊤]
          g (1 : SectionRing (ringSheaf O) ⊤)) := by
  refine ModuleCat.hom_ext (LinearMap.ext_ring ?_)
  simp [unitTensor, toMor, Stacks.Cech.CupProduct.tensorModulesMap, TensorProduct.map_tmul]
  rfl

/-- A bilinear map of presheaves of modules commutes with restriction, written with `res`. -/
theorem res_bilinearMap_app (β : Stacks.BilinearMap F.val G.val H.val) {V W : Opens X}
    (h : V ≤ W) (x : F.val.obj (op W)) (y : G.val.obj (op W)) :
    Stacks.Cohomology.Basis.res (abSections H) h (β.app (op W) x y) =
      β.app (op V) (Stacks.Cohomology.Basis.res (abSections F) h x)
        (Stacks.Cohomology.Basis.res (abSections G) h y) :=
  β.naturality (homOfLE h).op x y

/-- The restriction maps of the sections presheaf on the slice over `X` are the restrictions of
sections. -/
theorem sectionsP_map_apply {Z Z' : Over (⊤ : Opens X)} (f : Z ⟶ Z')
    (y : F.val.obj (op Z'.left)) :
    ConcreteCategory.hom ((sectionsP O F).map f.op) y =
      Stacks.Cohomology.Basis.res (abSections F) (leOfHom f.left) y :=
  rfl

/-- The face restriction of an explicit cochain. -/
theorem cechFaceRestriction_sliceCochain {p q : ℕ} (c : CechCochains.Cochain U (abSections F) p)
    (θ : Fin (p + 1) → Fin (q + 1)) (t : Fin (q + 1) → I) :
    ConcreteCategory.hom (Stacks.Cech.LinearCupProduct.cechFaceRestriction (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (sectionsP O F) θ t) (sliceCochain U hU F c) =
      Stacks.Cohomology.Basis.res (abSections F)
        ((leOfHom (Stacks.CategoryTheory.CechComplex.interMap (coverObject U hU) t θ).left).trans
          ((Stacks.Cohomology.CechSheaf.inter_coverObject_left ⊤ U hU (t ∘ θ)).le.trans
            (Stacks.Cech.cechComplexInter_eq U (t ∘ θ)).le)) (c (t ∘ θ)) := by
  change Stacks.Cohomology.Basis.res _ _ (Stacks.Cohomology.CechSheaf.rawcomp ⊤ U hU F
    (sliceCochain U hU F c) (t ∘ θ)) = _
  refine (congrArg (Stacks.Cohomology.Basis.res (abSections F) _)
    (Stacks.Cohomology.CechSheaf.rawcomp_mmk ⊤ U hU F _ (t ∘ θ))).trans ?_
  rw [Stacks.Cohomology.Basis.res_res, Stacks.Cohomology.Basis.res_res]

/-- The Alexander–Whitney product of two explicit cochains, on a component. -/
theorem π_cechAlexanderWhitney_sliceCochain (β : Stacks.BilinearMap F.val G.val H.val)
    {r s : ℕ} (c : CechCochains.Cochain U (abSections F) r)
    (d : CechCochains.Cochain U (abSections G) s) (t : Fin (r + s + 1) → I) :
    ConcreteCategory.hom (Stacks.CategoryTheory.CechComplex.π (coverObject U hU) (sectionsP O H)
      (r + s) t) (Stacks.Cech.LinearCupProduct.cechAlexanderWhitney (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤) (bilinearPairing β) r s
        (sliceCochain U hU F c ⊗ₜ[SectionRing (ringSheaf O) ⊤] sliceCochain U hU G d)) =
      β.app (op (Stacks.CategoryTheory.CechComplex.inter (coverObject U hU) t).left)
        (Stacks.Cohomology.Basis.res (abSections F)
          ((leOfHom (Stacks.CategoryTheory.CechComplex.interMap (coverObject U hU) t
            (Stacks.Cech.LinearCupProduct.frontIdx r (r + s) (by omega))).left).trans
            ((Stacks.Cohomology.CechSheaf.inter_coverObject_left ⊤ U hU _).le.trans
              (Stacks.Cech.cechComplexInter_eq U _).le))
          (c (t ∘ Stacks.Cech.LinearCupProduct.frontIdx r (r + s) (by omega))))
        (Stacks.Cohomology.Basis.res (abSections G)
          ((leOfHom (Stacks.CategoryTheory.CechComplex.interMap (coverObject U hU) t
            (Stacks.Cech.LinearCupProduct.backIdx r s (r + s) le_rfl)).left).trans
            ((Stacks.Cohomology.CechSheaf.inter_coverObject_left ⊤ U hU _).le.trans
              (Stacks.Cech.cechComplexInter_eq U _).le))
          (d (t ∘ Stacks.Cech.LinearCupProduct.backIdx r s (r + s) le_rfl))) := by
  refine (ConcreteCategory.congr_hom
    (Stacks.Cech.LinearCupProduct.cechAlexanderWhitney_comp_π (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (bilinearPairing β) r s t)
    (sliceCochain U hU F c ⊗ₜ[SectionRing (ringSheaf O) ⊤] sliceCochain U hU G d)).trans ?_
  rw [← cechFaceRestriction_sliceCochain U hU c, ← cechFaceRestriction_sliceCochain U hU d]
  rfl

/-- **The Alexander–Whitney map on the tensor product of two explicit cochains is the explicit
Alexander–Whitney product.** -/
theorem cechAlexanderWhitney_sliceCochain (β : Stacks.BilinearMap F.val G.val H.val) {r s : ℕ}
    (c : CechCochains.Cochain U (abSections F) r) (d : CechCochains.Cochain U (abSections G) s) :
    Stacks.Cech.LinearCupProduct.cechAlexanderWhitney (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤) (bilinearPairing β) r s
        (sliceCochain U hU F c ⊗ₜ[SectionRing (ringSheaf O) ⊤] sliceCochain U hU G d) =
      sliceCochain U hU H (cechAWCochain U β c d) := by
  refine Stacks.Cohomology.CechSheaf.mcech_ext ⊤ U hU H _ _ fun t => ?_
  rw [mcomp_sliceCochain]
  unfold Stacks.Cohomology.CechSheaf.mcomp Stacks.Cohomology.CechSheaf.rawcomp
  refine (congrArg (Stacks.Cohomology.Basis.res (abSections H)
    (Stacks.Cohomology.CechSheaf.inter_coverObject_left ⊤ U hU t).ge)
      (π_cechAlexanderWhitney_sliceCochain U hU β c d t)).trans ?_
  refine (res_bilinearMap_app β _ _ _).trans (Eq.trans ?_ (res_bilinearMap_app β _ _ _).symm)
  rw [Stacks.Cohomology.Basis.res_res, Stacks.Cohomology.Basis.res_res,
    Stacks.Cohomology.Basis.res_res, Stacks.Cohomology.Basis.res_res]

/-- **The tensor product of two explicit cochains followed by the Alexander–Whitney map is the
explicit Alexander–Whitney product.** -/
theorem unitTensor_tensorModulesMap_sliceMor_cechAlexanderWhitney
    (β : Stacks.BilinearMap F.val G.val H.val) {r s : ℕ}
    (c : CechCochains.Cochain U (abSections F) r) (d : CechCochains.Cochain U (abSections G) s) :
    unitTensor O ≫ Stacks.Cech.CupProduct.tensorModulesMap (SectionRing (ringSheaf O) ⊤)
        (sliceMor U hU F c) (sliceMor U hU G d) ≫
      Stacks.Cech.LinearCupProduct.cechAlexanderWhitney (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤) (bilinearPairing β) r s =
      sliceMor U hU H (cechAWCochain U β c d) := by
  rw [← Category.assoc, unitTensor_tensorModulesMap, toMor_comp]
  refine Eq.trans ?_ (toMor_apply (sliceMor U hU H (cechAWCochain U β c d)))
  have e1 : sliceMor U hU F c (1 : SectionRing (ringSheaf O) ⊤) = sliceCochain U hU F c :=
    toMor_apply_one _
  have e2 : sliceMor U hU G d (1 : SectionRing (ringSheaf O) ⊤) = sliceCochain U hU G d :=
    toMor_apply_one _
  have e3 : sliceMor U hU H (cechAWCochain U β c d) (1 : SectionRing (ringSheaf O) ⊤) =
      sliceCochain U hU H (cechAWCochain U β c d) := toMor_apply_one _
  rw [e1, e2, e3]
  exact congrArg _ (cechAlexanderWhitney_sliceCochain U hU β c d)

/-- The Alexander–Whitney map of the pairing of sheaves placed in degrees `a` and `b`, on the
cochains attached to two explicit cochains. -/
theorem unitTensor_cechAlexanderWhitney_singlePairingAt (b : ℤ)
    (β : Stacks.BilinearMap F.val G.val H.val) {r s : ℕ}
    (c : CechCochains.Cochain U (abSections F) r) (d : CechCochains.Cochain U (abSections G) s) :
    unitTensor O ≫ Stacks.Cech.CupProduct.tensorModulesMap (SectionRing (ringSheaf O) ⊤)
        (sliceMor U hU F c ≫ cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
          (singleXIsoAt O F a a rfl).inv r)
        (sliceMor U hU G d ≫ cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
          (singleXIsoAt O G b b rfl).inv s) ≫
      Stacks.Cech.LinearCupProduct.cechAlexanderWhitney (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤)
        ((singlePairingAt a b (bilinearPairing β)).μ a b (a + b) rfl) r s =
      sliceMor U hU H (cechAWCochain U β c d) ≫ cechCochainsMap (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤) (singleXIsoAt O H (a + b) (a + b) rfl).inv (r + s) := by
  rw [singlePairingAt_μ]
  unfold Stacks.Cech.LinearCupProduct.cechAlexanderWhitney
  rw [Stacks.Cech.LinearCupProduct.cechAlexanderWhitneyTo_naturality_left (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (singleXIsoAt O F a a rfl).hom,
    Stacks.Cech.LinearCupProduct.cechAlexanderWhitneyTo_naturality_right (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (singleXIsoAt O G b b rfl).hom,
    ← Stacks.Cech.LinearCupProduct.cechAlexanderWhitneyTo_comp_cechCochainsMap (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (bilinearPairing β) (singleXIsoAt O H (a + b) (a + b) rfl).inv,
    Stacks.Cech.LinearCupProduct.tensorModulesMap_comp_assoc,
    Stacks.Cech.LinearCupProduct.tensorModulesMap_comp_assoc]
  simp only [Category.assoc, Category.comp_id, Category.id_comp,
    cechCochainsMap_singleXIsoAt_inv_hom]
  rw [← Category.assoc, ← Category.assoc,
    ← unitTensor_tensorModulesMap_sliceMor_cechAlexanderWhitney U hU β c d]
  simp only [Category.assoc]
  rfl

open Stacks.Cech.CupProduct (tensorModules tensorModulesMap)

/-- **The Čech cup product of two homogeneous cochains of the total Čech complexes of the sections
presheaves**: `(-1)^{as}` times the Alexander–Whitney map of the pairing in bidegree `(a, b)`. -/
@[reassoc]
theorem cupPair_ιTotalCechTo_cechCupS
    {K L M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))} (γ : Pairing O K L M)
    {P Q : ModuleCat.{u} (SectionRing (ringSheaf O) ⊤)} {r s : ℕ} {a b : ℤ}
    (z : P ⟶ Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (((Stacks.Cech.Refinement.sectionsComplex O).obj K.obj).X a) r)
    (w : Q ⟶ Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) (((Stacks.Cech.Refinement.sectionsComplex O).obj L.obj).X b) s)
    (p q n : ℤ) (hp : (r : ℤ) + a = p) (hq : (s : ℤ) + b = q) (hn : p + q = n) :
    Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
        ((cechSections O U hU).obj K.obj) ((cechSections O U hU).obj L.obj) p q n hn
        (z ≫ ιTotalCechTo (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
          ((Stacks.Cech.Refinement.sectionsComplex O).obj K.obj) r a p hp)
        (w ≫ ιTotalCechTo (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
          ((Stacks.Cech.Refinement.sectionsComplex O).obj L.obj) s b q hq) ≫
        (cechCupS O U hU γ).f n =
      (((a * s).negOnePow : ℤ)) • (tensorModulesMap (SectionRing (ringSheaf O) ⊤) z w ≫
        Stacks.Cech.LinearCupProduct.cechAlexanderWhitney (coverObject U hU)
          (SectionRing (ringSheaf O) ⊤) (γ.μ a b (a + b) rfl) r s ≫
        ιTotalCechTo (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
          ((Stacks.Cech.Refinement.sectionsComplex O).obj M.obj) (r + s) (a + b) n
          (by push_cast; omega)) := by
  unfold cechCupS cechCupRaw
  exact Stacks.Cech.LinearCupProduct.cupPair_ιTotalCechTo_cechCupProduct (coverObject U hU)
    (SectionRing (ringSheaf O) ⊤) γ z w p q n hp hq hn

/-- **The cup product of two cochains of the total Čech complexes that are homogeneous
cochains**, of Čech degrees `r`, `s` and coefficient degrees `a`, `b`, is `(-1)^{as}` times their
Alexander–Whitney product. -/
theorem unitTensor_cupPair_cechCup_eq_zsmul
    {K L M : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))} (γ : Pairing O K L M)
    {r s : ℕ} {a b p q n : ℤ} (hp : (r : ℤ) + a = p) (hq : (s : ℤ) + b = q) (hn : p + q = n)
    (z : unitModule (SectionRing (ringSheaf O) ⊤) ⟶ ((cech O U hU).obj K.obj).X p)
    (w : unitModule (SectionRing (ringSheaf O) ⊤) ⟶ ((cech O U hU).obj L.obj).X q)
    (z' : unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤)
        (((Stacks.Cech.Refinement.sectionsComplex O).obj K.obj).X a) r)
    (w' : unitModule (SectionRing (ringSheaf O) ⊤) ⟶
      Stacks.Cech.LinearCupProduct.cechCochains (coverObject U hU)
        (SectionRing (ringSheaf O) ⊤)
        (((Stacks.Cech.Refinement.sectionsComplex O).obj L.obj).X b) s)
    (hz : z ≫ (eqToHom (cech_obj_eq O U hU K)).f p = z' ≫ ιTotalCechTo (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) ((Stacks.Cech.Refinement.sectionsComplex O).obj K.obj) r a p hp)
    (hw : w ≫ (eqToHom (cech_obj_eq O U hU L)).f q = w' ≫ ιTotalCechTo (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) ((Stacks.Cech.Refinement.sectionsComplex O).obj L.obj) s b q
        hq) :
    unitTensor O ≫ Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
        ((cech O U hU).obj K.obj) ((cech O U hU).obj L.obj) p q n hn z w ≫ (cechCup O U hU γ).f n =
      (((a * s).negOnePow : ℤ)) • ((unitTensor O ≫
        tensorModulesMap (SectionRing (ringSheaf O) ⊤) z' w' ≫
        Stacks.Cech.LinearCupProduct.cechAlexanderWhitney (coverObject U hU)
          (SectionRing (ringSheaf O) ⊤) (γ.μ a b (a + b) rfl) r s ≫
        ιTotalCechTo (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
          ((Stacks.Cech.Refinement.sectionsComplex O).obj M.obj) (r + s) (a + b) n
          (by push_cast; omega)) ≫ (eqToHom (cech_obj_eq O U hU M).symm).f n) := by
  have key := cupPair_comp_mapBifunctorMap O (eqToHom (cech_obj_eq O U hU K))
    (eqToHom (cech_obj_eq O U hU L)) p q n hn z w
  rw [hz, hw] at key
  rw [cechCup, HomologicalComplex.comp_f, HomologicalComplex.comp_f, reassoc_of% key,
    cupPair_ιTotalCechTo_cechCupS_assoc, Preadditive.zsmul_comp, Preadditive.comp_zsmul]
  simp only [Category.assoc]

/-- The cochain attached to an explicit Čech cochain, read in the total Čech complex of the
sections presheaves. -/
theorem cochainOfAt_comp_eqToHom_f {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    cochainOfAt U hU F a c ≫ (eqToHom (cech_obj_eq O U hU (singlePlus O F a))).f ((p : ℤ) + a) =
      (sliceMor U hU F c ≫ cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
        (singleXIsoAt O F a a rfl).inv p) ≫
        ιTotalCechTo (coverObject U hU) (SectionRing (ringSheaf O) ⊤) (sectionsKAt F a) p a
          ((p : ℤ) + a) rfl := by
  rw [eqToHom_cech_obj_eq, Category.assoc]
  exact Category.comp_id _

/-- The cochain attached to an explicit Čech cochain, through the total Čech complex of the
sections presheaves. -/
theorem cochainOfAt_eq_comp_eqToHom_f {p : ℕ} (c : CechCochains.Cochain U (abSections F) p) :
    cochainOfAt U hU F a c =
      ((sliceMor U hU F c ≫ cechCochainsMap (coverObject U hU) (SectionRing (ringSheaf O) ⊤)
        (singleXIsoAt O F a a rfl).inv p) ≫
        ιTotalCechTo (coverObject U hU) (SectionRing (ringSheaf O) ⊤) (sectionsKAt F a) p a
          ((p : ℤ) + a) rfl) ≫
        (eqToHom (cech_obj_eq O U hU (singlePlus O F a)).symm).f ((p : ℤ) + a) := by
  rw [← cochainOfAt_comp_eqToHom_f, Category.assoc, ← HomologicalComplex.comp_f, eqToHom_trans,
    eqToHom_refl, HomologicalComplex.id_f, Category.comp_id]

/-- **The cup product of the cochains attached to two explicit Čech cochains**, for the pairing
of sheaves placed in degrees `a` and `b` attached to a bilinear map `β`, is `(-1)^{as}` times the
cochain attached to their explicit Alexander–Whitney product. -/
theorem unitTensor_cupPair_cochainOfAt_cechCup (b : ℤ)
    (β : Stacks.BilinearMap F.val G.val H.val) {r s : ℕ}
    (c : CechCochains.Cochain U (abSections F) r) (d : CechCochains.Cochain U (abSections G) s) :
    unitTensor O ≫ Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
        ((cech O U hU).obj (singlePlus O F a).obj) ((cech O U hU).obj (singlePlus O G b).obj)
        ((r : ℤ) + a) ((s : ℤ) + b) (((r + s : ℕ) : ℤ) + (a + b)) (by push_cast; ring)
        (cochainOfAt U hU F a c) (cochainOfAt U hU G b d) ≫
      (cechCup O U hU (singlePairingAt a b (bilinearPairing β))).f (((r + s : ℕ) : ℤ) + (a + b)) =
      (((a * s).negOnePow : ℤ)) • cochainOfAt U hU H (a + b) (cechAWCochain U β c d) := by
  rw [cochainOfAt_eq_comp_eqToHom_f U hU (a + b) (cechAWCochain U β c d),
    unitTensor_cupPair_cechCup_eq_zsmul U hU _ rfl rfl _ _ _ _ _
      (cochainOfAt_comp_eqToHom_f U hU a c) (cochainOfAt_comp_eqToHom_f U hU b d),
    ← unitTensor_cechAlexanderWhitney_singlePairingAt]
  simp only [Category.assoc]

/-- A cochain attached to an explicit Čech cochain is a cocycle only if the explicit cochain is a
Čech cocycle. -/
theorem cechD_eq_zero_of_cochainOfAt_d {p : ℕ} (c : CechCochains.Cochain U (abSections F) p)
    (h : cochainOfAt U hU F a c ≫
      ((cech O U hU).obj (singlePlus O F a).obj).d ((p : ℤ) + a) ((p : ℤ) + a + 1) = 0) :
    CechCochains.cechD U (abSections F) p c = 0 :=
  cechD_eq_zero_of_cochainOfAtTo U hU F a _ rfl c h

include hU in
/-- **The Alexander–Whitney product of two Čech cocycles along a bilinear map is a Čech
cocycle.** -/
theorem cechD_cechAWCochain (β : Stacks.BilinearMap F.val G.val H.val) {r s : ℕ}
    (c : CechCochains.Cochain U (abSections F) r) (d : CechCochains.Cochain U (abSections G) s)
    (hc : CechCochains.cechD U (abSections F) r c = 0)
    (hd : CechCochains.cechD U (abSections G) s d = 0) :
    CechCochains.cechD U (abSections H) (r + s) (cechAWCochain U β c d) = 0 := by
  have h := unitTensor_cupPair_cochainOfAt_cechCup U hU 0 0 β c d
  have h0 := Stacks.CupProduct.cupPair_comp_gamma_comp_d_eq_zero
    (tensorModules (SectionRing (ringSheaf O) ⊤)) ((cech O U hU).obj (singlePlus O F 0).obj)
    ((cech O U hU).obj (singlePlus O G 0).obj)
    (cechCup O U hU (singlePairingAt 0 0 (bilinearPairing β))) ((r : ℤ) + 0) ((s : ℤ) + 0)
    (((r + s : ℕ) : ℤ) + (0 + 0)) (by push_cast; ring) (cochainOfAt U hU F 0 c)
    (cochainOfAt U hU G 0 d) (cochainOfAt_d_eq_zero U hU F 0 c hc)
    (cochainOfAt_d_eq_zero U hU G 0 d hd)
  rw [zero_mul, Int.negOnePow_zero, Units.val_one, one_smul] at h
  refine cechD_eq_zero_of_cochainOfAt_d U hU (0 + 0) _ ?_
  rw [← h, Category.assoc, Category.assoc, ← Category.assoc _ _ (HomologicalComplex.d _ _ _), h0,
    comp_zero]

/-- The class of an integer multiple of a cocycle. -/
theorem cocycleClass_zsmul {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ} {P : C}
    (k n : ℤ) (x : P ⟶ K.X n) (hx : x ≫ K.d n (n + 1) = 0)
    (hkx : (k • x) ≫ K.d n (n + 1) = 0) :
    cocycleClass n (k • x) hkx = k • cocycleClass n x hx := by
  have h : K.liftCycles (k • x) (n + 1) (CochainComplex.next ℤ n) hkx =
      k • K.liftCycles x (n + 1) (CochainComplex.next ℤ n) hx := by
    rw [← cancel_mono (K.iCycles n), HomologicalComplex.liftCycles_i, Preadditive.zsmul_comp,
      HomologicalComplex.liftCycles_i]
  dsimp only [cocycleClass]
  rw [h, Preadditive.zsmul_comp]

/-- The class of a cocycle precomposed with a morphism. -/
theorem comp_cocycleClass {C : Type*} [Category* C] [Abelian C] {K : CochainComplex C ℤ}
    {P P' : C} (f : P' ⟶ P) (n : ℤ) (x : P ⟶ K.X n) (hx : x ≫ K.d n (n + 1) = 0) :
    f ≫ cocycleClass n x hx = cocycleClass n (f ≫ x) (by rw [Category.assoc, hx, comp_zero]) := by
  dsimp only [cocycleClass]
  rw [← Category.assoc, HomologicalComplex.comp_liftCycles]

/-- **The cup product of the classes of two explicit Čech cocycles** of sheaves placed in degrees
`a` and `b`, for the pairing attached to a bilinear map `β`, is `(-1)^{as}` times the class of
their explicit Alexander–Whitney product. -/
theorem cup_cechCocycleClassAt (b : ℤ) (hF : CechComputes O (singlePlus O F a))
    (hG : CechComputes O (singlePlus O G b)) (β : Stacks.BilinearMap F.val G.val H.val)
    {r s : ℕ} (c : CechCochains.Cochain U (abSections F) r)
    (hc : CechCochains.cechD U (abSections F) r c = 0)
    (d : CechCochains.Cochain U (abSections G) s)
    (hd : CechCochains.cechD U (abSections G) s d = 0) :
    cup O hF hG (singlePairingAt a b (bilinearPairing β)) ((r : ℤ) + a) ((s : ℤ) + b)
        (((r + s : ℕ) : ℤ) + (a + b)) (by push_cast; ring) (cechCocycleClassAt U hU F a c hc)
        (cechCocycleClassAt U hU G b d hd) =
      ((a * s).negOnePow : ℤ) • cechCocycleClassAt U hU H (a + b) (cechAWCochain U β c d)
        (cechD_cechAWCochain U hU β c d hc hd) := by
  unfold cechCocycleClassAt
  rw [cup_eq, toMor_apply, toMor_apply,
    cechCupClass_eq O U hU _ _ _ _ _ _ (cochainOfAt_d_eq_zero U hU F a c hc) _
      (cochainOfAt_d_eq_zero U hU G b d hd), comp_cocycleClass,
    cocycleClass_congr _ (unitTensor_cupPair_cochainOfAt_cechCup U hU a b β c d) _
      (by rw [Preadditive.zsmul_comp, cochainOfAt_d_eq_zero U hU H (a + b) _
        (cechD_cechAWCochain U hU β c d hc hd), smul_zero]),
    cocycleClass_zsmul _ _ _ (cochainOfAt_d_eq_zero U hU H (a + b) _
      (cechD_cechAWCochain U hU β c d hc hd)), Preadditive.zsmul_comp]
  rfl

/-- **The cup product of the classes of two explicit Čech cocycles** of sheaves in degree zero,
for the pairing attached to a bilinear map `β`, is the class of their explicit Alexander–Whitney
product. -/
theorem cup_cechCocycleClass (hF : CechComputes O (singlePlus O F 0))
    (hG : CechComputes O (singlePlus O G 0)) (β : Stacks.BilinearMap F.val G.val H.val)
    {r s : ℕ} (c : CechCochains.Cochain U (abSections F) r)
    (hc : CechCochains.cechD U (abSections F) r c = 0)
    (d : CechCochains.Cochain U (abSections G) s)
    (hd : CechCochains.cechD U (abSections G) s d = 0) :
    cup O hF hG (singlePairing (bilinearPairing β)) r s ((r + s : ℕ) : ℤ) (by push_cast; rfl)
        (cechCocycleClass U hU F c hc) (cechCocycleClass U hU G d hd) =
      cechCocycleClass U hU H (cechAWCochain U β c d) (cechD_cechAWCochain U hU β c d hc hd) := by
  have h := cup_cechCocycleClassAt U hU 0 0 hF hG β c hc d hd
  rw [zero_mul, Int.negOnePow_zero, Units.val_one, one_smul] at h
  exact h

end Cup

end Stacks.Cech.Hypercohomology

end
