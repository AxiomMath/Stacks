module

public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotal
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.LinearCupProduct
public import Mathlib.Algebra.Category.ModuleCat.Products

/-!
# The elementwise total Čech complex is the total complex of the Čech bicomplex

Let `C` be a category with finite products, `W : ι → C` a family of objects and `R` a
commutative ring. The total Čech complex of a complex of presheaves of `R`-modules on `C` has two
descriptions in the library:

* `Stacks.Cech.LinearCupProduct.totalCechComplexFunctor`, the totalization (by direct sums) of
  the Čech bicomplex built from Mathlib's `CategoryTheory.cechComplexFunctor`, for a complex `K`
  indexed by `ℤ`;
* `Stacks.CategoryTheory.CechComplex.cechTot`, whose degree-`n` term is the type of dependent
  functions on the pairs `(p, a)` with `p + a = n` and the tuples of indices, for a complex `P`
  indexed by `ℕ`.

Both use the differential `δ + (-1)^p d` on the summand of Čech degree `p`. This file identifies
them whenever `K` vanishes in negative degrees and agrees with `P` in nonnegative degrees,
compatibly with the differentials (`Stacks.CategoryTheory.CechComplex.totalCechIso`).

## Main definitions

* `Stacks.CategoryTheory.CechComplex.cochainsIso`: the Čech cochains of Mathlib's Čech complex
  as dependent functions.
* `Stacks.CategoryTheory.CechComplex.totalCechIso`: the isomorphism of total complexes.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Cech.LinearCupProduct (PresheafModules cechCochains cechCochainsMap
  totalCechComplexFunctor ιTotalCech ιTotalCechTo totalCechDesc ιTotalCech_desc ιTotalCechTo_eq
  ιTotalCechTo_d totalCech_hom_ext cechCochainsMap_comp_π cechCochainsMap_comp cechCochainsMap_id)

universe u uC vC uR

namespace Stacks.CategoryTheory.CechComplex

noncomputable section

attribute [local instance] ModuleCat.hasLimitsOfSize ModuleCat.hasColimitsOfSize

variable {C : Type uC} [Category.{vC} C] [HasFiniteProducts C] {ι : Type u} (W : ι → C)
  {R : Type uR} [CommRing R]

/-! ### Čech cochains as dependent functions -/

/-- **The Čech cochains of Mathlib's Čech complex are dependent functions** on the tuples of
indices: the degree-`p` term is the product of the sections over the intersections. -/
def cochainsIso (F : Cᵒᵖ ⥤ ModuleCat.{u} R) (p : ℕ) :
    ((cechComplexFunctor W).obj F).X p ≅ ModuleCat.of R (Cochain W F p) :=
  (isLimitFan W F p).conePointUniqueUpToIso
    (ModuleCat.productConeIsLimit fun t : Fin (p + 1) → ι => F.obj (op (inter W t)))

/-- The component at a tuple `t` of the dependent function attached to a cochain is the
projection of the cochain to the factor `t`. -/
theorem cochainsIso_hom_apply (F : Cᵒᵖ ⥤ ModuleCat.{u} R) (p : ℕ)
    (z : ((cechComplexFunctor W).obj F).X p) (t : Fin (p + 1) → ι) :
    (cochainsIso W F p).hom z t = (π W F p t) z :=
  ConcreteCategory.congr_hom ((isLimitFan W F p).conePointUniqueUpToIso_hom_comp
    (ModuleCat.productConeIsLimit fun t : Fin (p + 1) → ι => F.obj (op (inter W t)))
    ⟨t⟩) z

/-- The projection to the factor `t` of the cochain attached to a dependent function `c` is
`c t`. -/
theorem π_cochainsIso_inv_apply (F : Cᵒᵖ ⥤ ModuleCat.{u} R) (p : ℕ) (c : Cochain W F p)
    (t : Fin (p + 1) → ι) : (π W F p t) ((cochainsIso W F p).inv c) = c t := by
  have h := cochainsIso_hom_apply W F p ((cochainsIso W F p).inv c) t
  rw [← ConcreteCategory.comp_apply, Iso.inv_hom_id, ConcreteCategory.id_apply] at h
  exact h.symm

/-- The Čech differential of Mathlib's Čech complex, on dependent functions. -/
theorem cochainsIso_hom_d (F : Cᵒᵖ ⥤ ModuleCat.{u} R) (p : ℕ)
    (z : ((cechComplexFunctor W).obj F).X p) :
    (cochainsIso W F (p + 1)).hom (((cechComplexFunctor W).obj F).d p (p + 1) z) =
      cechD W F p ((cochainsIso W F p).hom z) := by
  funext t
  rw [cochainsIso_hom_apply, ← ConcreteCategory.comp_apply, d_comp_π, cechD_apply]
  simp only [ModuleCat.hom_sum, ModuleCat.hom_zsmul, LinearMap.sum_apply,
    LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [cochainsIso_hom_apply]

/-- A morphism of presheaves acts componentwise on the cochains of Mathlib's Čech complex. -/
theorem cochainsIso_hom_map {F G : Cᵒᵖ ⥤ ModuleCat.{u} R} (f : F ⟶ G) (p : ℕ)
    (z : ((cechComplexFunctor W).obj F).X p) :
    (cochainsIso W G p).hom (cechCochainsMap W R f p z) =
      cochainMap W f p ((cochainsIso W F p).hom z) := by
  funext t
  rw [cochainsIso_hom_apply, ← ConcreteCategory.comp_apply, cechCochainsMap_comp_π W R f p t,
    ConcreteCategory.comp_apply, cochainMap_apply, cochainsIso_hom_apply]

/-! ### The total complexes -/

/-- A choice of enumeration of the summands of `Tot^n`, to sum over them. -/
@[instance_reducible]
def totIndexFintype (n : ℤ) : Fintype (TotIndex n) :=
  have := finite_totIndex n
  Fintype.ofFinite _

attribute [local instance] totIndexFintype

variable (K : CochainComplex (PresheafModules.{u} C R) ℤ)
  (P : CochainComplex (Cᵒᵖ ⥤ ModuleCat.{u} R) ℕ) (e : ∀ b : ℕ, K.X (b : ℤ) ≅ P.X b)

/-- The inclusion of the cochains of `P^b` of Čech degree `p` as a summand of `Tot^n`. -/
def totSingle (n : ℤ) (p b : ℕ) (h : (p : ℤ) + b = n) :
    Cochain W (P.X b) p →ₗ[R] TotX W P n :=
  LinearMap.single R (fun i : TotIndex n => Cochain W (P.X i.1.2) i.1.1) ⟨(p, b), h⟩

/-- `totSingle` places its argument in its own summand. -/
theorem totSingle_apply_self (n : ℤ) (p b : ℕ) (h : (p : ℤ) + b = n) (y : Cochain W (P.X b) p) :
    totSingle W P n p b h y ⟨(p, b), h⟩ = y :=
  Pi.single_eq_same (M := fun i : TotIndex n => Cochain W (P.X i.1.2) i.1.1) _ _

/-- `totSingle` vanishes on every other summand. -/
theorem totSingle_apply_ne (n : ℤ) (p b : ℕ) (h : (p : ℤ) + b = n) (y : Cochain W (P.X b) p)
    (i : TotIndex n) (hi : i ≠ ⟨(p, b), h⟩) : totSingle W P n p b h y i = 0 :=
  Pi.single_eq_of_ne (M := fun i : TotIndex n => Cochain W (P.X i.1.2) i.1.1) hi _

/-- `totSingle` vanishes on a summand of different Čech or coefficient degree. -/
theorem totSingle_apply_of_ne (n : ℤ) (p b : ℕ) (h : (p : ℤ) + b = n) (y : Cochain W (P.X b) p)
    (p' a' : ℕ) (h' : (p' : ℤ) + a' = n) (hne : ¬ (p' = p ∧ a' = b)) :
    totSingle W P n p b h y ⟨(p', a'), h'⟩ = 0 :=
  totSingle_apply_ne W P n p b h y _ fun he => hne ⟨congrArg (·.1.1) he, congrArg (·.1.2) he⟩

/-- **The total differential of a single summand**: `δ` lands in Čech degree `p + 1` and
`(-1)^p d_P` in coefficient degree `b + 1`. -/
theorem totDTo_totSingle (n m : ℤ) (hm : n + 1 = m) (p b : ℕ) (h : (p : ℤ) + b = n)
    (y : Cochain W (P.X b) p) :
    totDTo W P n m hm (totSingle W P n p b h y) =
      totSingle W P m (p + 1) b (by push_cast; omega) (cechD W (P.X b) p y) +
        ((-1 : ℤ) ^ p) • totSingle W P m p (b + 1) (by push_cast; omega)
          (cochainMap W (P.d b (b + 1)) p y) := by
  funext ⟨⟨p', a'⟩, hj⟩
  simp only [totDTo_apply, Pi.add_apply, Pi.smul_apply]
  congr 1
  · rcases p' with _ | q
    · rw [totDCech_zero, totSingle_apply_of_ne W P m _ _ _ _ _ _ _ (by omega)]
    · rw [totDCech_succ]
      by_cases hq : q = p ∧ a' = b
      · obtain ⟨rfl, rfl⟩ := hq
        rw [totSingle_apply_self, totSingle_apply_self]
      · rw [totSingle_apply_of_ne W P n _ _ _ _ _ _ _ hq, map_zero,
          totSingle_apply_of_ne W P m _ _ _ _ _ _ _ (by omega)]
  · rcases a' with _ | c
    · rw [totDCoef_zero, totSingle_apply_of_ne W P m _ _ _ _ _ _ _ (by omega), smul_zero]
    · rw [totDCoef_succ]
      by_cases hc : p' = p ∧ c = b
      · obtain ⟨rfl, rfl⟩ := hc
        rw [totSingle_apply_self, totSingle_apply_self]
      · rw [totSingle_apply_of_ne W P n _ _ _ _ _ _ _ hc, map_zero, smul_zero,
          totSingle_apply_of_ne W P m _ _ _ _ _ _ _ (by omega), smul_zero]

/-- The comparison on the summand of Čech degree `p` and coefficient degree `a`: zero when
`a < 0`, and the identification of `K^a` with `P^a` followed by the inclusion otherwise. -/
def summandTo (n : ℤ) (p : ℕ) : ∀ (a : ℤ), (p : ℤ) + a = n →
    (cechCochains W R (K.X a) p ⟶ ModuleCat.of R (TotX W P n))
  | (b : ℕ), h => cechCochainsMap W R (e b).hom p ≫ (cochainsIso W (P.X b) p).hom ≫
      ModuleCat.ofHom (totSingle W P n p b h)
  | .negSucc _, _ => 0

/-- **The comparison map** `Tot(Č(W, K))^n ⟶ Tot(Č(W, P))^n`, summand by summand. -/
def totalTo (n : ℤ) :
    ((totalCechComplexFunctor W R).obj K).X n ⟶ ModuleCat.of R (TotX W P n) :=
  totalCechDesc W R K fun p a h => summandTo W K P e n p a h

/-- On the summand of Čech degree `p` and coefficient degree `a`, the comparison map is
`summandTo`. -/
theorem ιTotalCechTo_totalTo (n : ℤ) (p : ℕ) (a : ℤ) (h : (p : ℤ) + a = n) :
    ιTotalCechTo W R K p a n h ≫ totalTo W K P e n = summandTo W K P e n p a h :=
  (congrArg (· ≫ totalTo W K P e n) (ιTotalCechTo_eq W R K p a n h)).trans
    ((Category.assoc _ _ _).trans (ιTotalCech_desc W R K _ p a h))

/-- The inverse comparison `Tot(Č(W, P))^n ⟶ Tot(Č(W, K))^n`. -/
def totalFrom (n : ℤ) :
    ModuleCat.of R (TotX W P n) ⟶ ((totalCechComplexFunctor W R).obj K).X n :=
  ModuleCat.ofHom
    { toFun := fun x => ∑ i : TotIndex n,
        (ιTotalCechTo W R K i.1.1 (i.1.2 : ℤ) n i.2).hom
          ((cechCochainsMap W R (e i.1.2).inv i.1.1).hom
            ((cochainsIso W (P.X i.1.2) i.1.1).inv.hom (x i)))
      map_add' := fun x y => by
        simp only [Pi.add_apply, map_add]
        exact Finset.sum_add_distrib
      map_smul' := fun c x => by
        simp only [Pi.smul_apply, map_smul, RingHom.id_apply]
        exact Finset.smul_sum.symm }

/-- The inverse comparison sums, over the summands of `Tot^n`, the inclusions of the components
transported along `e` and `cochainsIso`. -/
theorem totalFrom_apply (n : ℤ) (x : TotX W P n) :
    (totalFrom W K P e n).hom x = ∑ i : TotIndex n,
      (ιTotalCechTo W R K i.1.1 (i.1.2 : ℤ) n i.2).hom
        ((cechCochainsMap W R (e i.1.2).inv i.1.1).hom
          ((cochainsIso W (P.X i.1.2) i.1.1).inv.hom (x i))) :=
  rfl

/-- The Čech cochain map of `φ.hom` followed by that of `φ.inv` is the identity. -/
theorem cechCochainsMap_hom_inv_apply {F G : Cᵒᵖ ⥤ ModuleCat.{u} R} (φ : F ≅ G) (p : ℕ)
    (z : cechCochains W R F p) :
    (cechCochainsMap W R φ.inv p).hom ((cechCochainsMap W R φ.hom p).hom z) = z :=
  ((cechComplexFunctor W ⋙ HomologicalComplex.eval _ _ p).mapIso φ).hom_inv_id_apply z

/-- The Čech cochain map of `φ.inv` followed by that of `φ.hom` is the identity. -/
theorem cechCochainsMap_inv_hom_apply {F G : Cᵒᵖ ⥤ ModuleCat.{u} R} (φ : F ≅ G) (p : ℕ)
    (z : cechCochains W R G p) :
    (cechCochainsMap W R φ.hom p).hom ((cechCochainsMap W R φ.inv p).hom z) = z :=
  ((cechComplexFunctor W ⋙ HomologicalComplex.eval _ _ p).mapIso φ).inv_hom_id_apply z

/-- In a nonnegative coefficient degree `b`, the comparison on a summand is the identification
of `K^b` with `P^b` followed by the inclusion of the summand. -/
theorem summandTo_natCast (n : ℤ) (p b : ℕ) (h : (p : ℤ) + b = n) :
    summandTo W K P e n p (b : ℤ) h = cechCochainsMap W R (e b).hom p ≫
      (cochainsIso W (P.X b) p).hom ≫ ModuleCat.ofHom (totSingle W P n p b h) :=
  rfl

variable (hz : ∀ a : ℤ, a < 0 → IsZero (K.X a))
  (he : ∀ b : ℕ, K.d b (b + 1) ≫ (e (b + 1)).hom = (e b).hom ≫ P.d b (b + 1))

include hz in
/-- The Čech cochains of `K^a` vanish in negative degrees `a`. -/
theorem isZero_cechCochains_of_neg (a : ℤ) (ha : a < 0) (p : ℕ) :
    IsZero (cechCochains W R (K.X a) p) :=
  (cechComplexFunctor W ⋙ HomologicalComplex.eval _ _ p).map_isZero (hz a ha)

/-- Two maps out of a degree of the total Čech complex agree as soon as they agree on every
summand of nonnegative coefficient degree, when `K` vanishes in negative degrees. -/
private theorem totalCechTo_hom_ext (hz : ∀ a : ℤ, a < 0 → IsZero (K.X a)) {n : ℤ}
    {A : ModuleCat.{u} R}
    {f g : ((totalCechComplexFunctor W R).obj K).X n ⟶ A}
    (h : ∀ (p b : ℕ) (hpa : (p : ℤ) + b = n),
      ιTotalCechTo W R K p (b : ℤ) n hpa ≫ f = ιTotalCechTo W R K p (b : ℤ) n hpa ≫ g) :
    f = g := by
  refine totalCech_hom_ext W R K fun p a hpa => ?_
  simp only [← Category.assoc]
  rw [← ιTotalCechTo_eq W R K p a n hpa]
  rcases a with b | b
  · exact h p b hpa
  · exact (isZero_cechCochains_of_neg W K hz _ (Int.negSucc_lt_zero b) p).eq_of_src _ _

/-- The inverse comparison followed by the comparison is the identity. -/
theorem totalFrom_totalTo (n : ℤ) : totalFrom W K P e n ≫ totalTo W K P e n = 𝟙 _ := by
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro (x : TotX W P n)
  change (totalTo W K P e n).hom ((totalFrom W K P e n).hom x) = x
  rw [totalFrom_apply, map_sum]
  conv_rhs => rw [← Finset.univ_sum_single x]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := ConcreteCategory.congr_hom (ιTotalCechTo_totalTo W K P e n i.1.1 (i.1.2 : ℤ) i.2)
    ((cechCochainsMap W R (e i.1.2).inv i.1.1).hom ((cochainsIso W (P.X i.1.2) i.1.1).inv.hom
      (x i)))
  rw [ConcreteCategory.comp_apply] at h
  refine h.trans ?_
  change totSingle W P n i.1.1 i.1.2 i.2 ((cochainsIso W (P.X i.1.2) i.1.1).hom
    ((cechCochainsMap W R (e i.1.2).hom i.1.1).hom ((cechCochainsMap W R (e i.1.2).inv i.1.1).hom
      ((cochainsIso W (P.X i.1.2) i.1.1).inv (x i))))) = _
  rw [cechCochainsMap_inv_hom_apply, Iso.inv_hom_id_apply]
  rfl

include hz in
/-- The comparison followed by the inverse comparison is the identity, when `K` vanishes in
negative degrees. -/
theorem totalTo_totalFrom (n : ℤ) : totalTo W K P e n ≫ totalFrom W K P e n = 𝟙 _ := by
  refine totalCechTo_hom_ext W K hz fun p b hpa => ?_
  rw [Category.comp_id, ← Category.assoc, ιTotalCechTo_totalTo]
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  change (totalFrom W K P e n).hom ((summandTo W K P e n p (b : ℤ) hpa).hom z) = _
  rw [totalFrom_apply, Finset.sum_eq_single (⟨(p, b), hpa⟩ : TotIndex n)]
  · rw [summandTo_natCast]
    change (ιTotalCechTo W R K p b n hpa).hom ((cechCochainsMap W R (e b).inv p).hom
      ((cochainsIso W (P.X b) p).inv.hom (totSingle W P n p b hpa _ ⟨(p, b), hpa⟩))) = _
    rw [totSingle_apply_self]
    change (ιTotalCechTo W R K p b n hpa).hom ((cechCochainsMap W R (e b).inv p).hom
      ((cochainsIso W (P.X b) p).inv ((cochainsIso W (P.X b) p).hom
        ((cechCochainsMap W R (e b).hom p).hom z)))) = _
    rw [Iso.hom_inv_id_apply, cechCochainsMap_hom_inv_apply]
  · intro i _ hi
    rw [summandTo_natCast]
    change (ιTotalCechTo W R K i.1.1 (i.1.2 : ℤ) n i.2).hom
      ((cechCochainsMap W R (e i.1.2).inv i.1.1).hom
        ((cochainsIso W (P.X i.1.2) i.1.1).inv.hom (totSingle W P n p b hpa _ i))) = 0
    rw [totSingle_apply_ne W P n p b hpa _ i hi]
    simp
  · exact fun h => absurd (Finset.mem_univ _) h

include hz in
/-- The comparison followed by the inverse comparison fixes every element, when `K` vanishes
in negative degrees. -/
theorem totalFrom_totalTo_apply (n : ℤ) (x : ((totalCechComplexFunctor W R).obj K).X n) :
    (totalFrom W K P e n).hom ((totalTo W K P e n).hom x) = x :=
  (ConcreteCategory.congr_hom (totalTo_totalFrom W K P e hz n) x).trans
    (ConcreteCategory.id_apply x)

include hz he in
/-- **The comparison commutes with the differentials.** -/
theorem totalTo_comm (n : ℤ) :
    ((totalCechComplexFunctor W R).obj K).d n (n + 1) ≫ totalTo W K P e (n + 1) =
      totalTo W K P e n ≫ (cechTot W P).d n (n + 1) := by
  refine totalCechTo_hom_ext W K hz fun p b hpa => ?_
  apply ModuleCat.hom_ext
  apply LinearMap.ext
  intro z
  have hd := ConcreteCategory.congr_hom (ιTotalCechTo_d W R K p (b : ℤ) n hpa) z
  have h1 := ConcreteCategory.congr_hom
    (ιTotalCechTo_totalTo W K P e (n + 1) (p + 1) (b : ℤ) (by push_cast; omega))
    ((Stacks.Cech.LinearCupProduct.cechD W R (K.X b) p).hom z)
  have h2 := ConcreteCategory.congr_hom
    (ιTotalCechTo_totalTo W K P e (n + 1) p ((b : ℤ) + 1) (by omega))
    ((cechCochainsMap W R (K.d b (b + 1)) p).hom z)
  have h3 := ConcreteCategory.congr_hom (ιTotalCechTo_totalTo W K P e n p (b : ℤ) hpa) z
  simp only [ConcreteCategory.comp_apply] at hd h1 h2 h3
  change (totalTo W K P e (n + 1)).hom
      ((((totalCechComplexFunctor W R).obj K).d n (n + 1)).hom
        ((ιTotalCechTo W R K p (b : ℤ) n hpa).hom z)) =
    ((cechTot W P).d n (n + 1)).hom ((totalTo W K P e n).hom
      ((ιTotalCechTo W R K p (b : ℤ) n hpa).hom z))
  rw [h3, hd]
  simp only [ModuleCat.hom_add, ModuleCat.hom_zsmul, LinearMap.add_apply,
    LinearMap.smul_apply, ModuleCat.hom_comp, LinearMap.comp_apply, Units.smul_def,
    map_add, map_zsmul]
  rw [h1, h2]
  change (summandTo W K P e (n + 1) (p + 1) (b : ℤ) _).hom _ +
      _ • (summandTo W K P e (n + 1) p ((b + 1 : ℕ) : ℤ) _).hom _ =
    ((cechTot W P).d n (n + 1)).hom ((summandTo W K P e n p (b : ℤ) hpa).hom z)
  rw [summandTo_natCast, summandTo_natCast, summandTo_natCast, cechTot_d_apply]
  simp only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_ofHom]
  rw [totD, totDTo_totSingle]
  congr 2
  · have hcd := ConcreteCategory.congr_hom
      (Stacks.Cech.LinearCupProduct.cechCochainsMap_d W R (e b).hom p) z
    simp only [ConcreteCategory.comp_apply] at hcd
    rw [← hcd]
    exact cochainsIso_hom_d W (P.X b) p _
  · have hcm := ConcreteCategory.congr_hom
      (Stacks.Cech.LinearCupProduct.cechCochainsMap_comp W R (K.d (b : ℤ) ((b : ℤ) + 1))
        (e (b + 1)).hom p) z
    have hcm' := ConcreteCategory.congr_hom
      (Stacks.Cech.LinearCupProduct.cechCochainsMap_comp W R (e b).hom (P.d b (b + 1)) p) z
    simp only [ConcreteCategory.comp_apply] at hcm hcm'
    rw [← hcm, he, hcm']
    exact congrArg _ (cochainsIso_hom_map W (P.d b (b + 1)) p _)

/-- **The elementwise total Čech complex is the total complex of the Čech bicomplex**, for a
complex `K` indexed by `ℤ` which vanishes in negative degrees and is identified with `P` in
nonnegative degrees compatibly with the differentials. -/
def totalCechIso : (totalCechComplexFunctor W R).obj K ≅ cechTot W P :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => (show ((totalCechComplexFunctor W R).obj K).X n ≅ ModuleCat.of R (TotX W P n) from
      { hom := totalTo W K P e n
        inv := totalFrom W K P e n
        hom_inv_id := totalTo_totalFrom W K P e hz n
        inv_hom_id := totalFrom_totalTo W K P e n }))
    (by
      rintro n _ rfl
      exact (totalTo_comm W K P e hz he n).symm)

/-- The components of `totalCechIso` are the comparison maps. -/
@[simp]
theorem totalCechIso_hom_f (n : ℤ) : (totalCechIso W K P e hz he).hom.f n = totalTo W K P e n :=
  rfl

end

end Stacks.CategoryTheory.CechComplex

end
