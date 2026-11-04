module

public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.CechCupProductNaturality
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupProduct
public import StacksFrontier.Topology.Sheaves.Cohomology.CechTotalComplex.HypercohomologyCupUnit

/-!
# Naturality of the cup product on hypercohomology

Let `X` be a topological space with a sheaf `𝒪_X` of commutative rings. The cup product
`γ(a ∪ b)` of [Stacks, Section 01FP] on the hypercohomology of bounded below complexes of
`𝒪_X`-modules, computed by Čech cocycles (`Stacks.Cech.Hypercohomology.cup`), is natural in the
three complexes: for morphisms `f : K ⟶ K'`, `g : L ⟶ L'` and `h : M ⟶ M'` carrying a pairing
`D` of `(K, L)` into `M` to a pairing `D'` of `(K', L')` into `M'`,

`h(D(a ∪ b)) = D'(f(a) ∪ g(b))`.

## Main results

* `Stacks.Cech.Hypercohomology.cechCup_natural`: the naturality of the Čech cup product on total
  Čech complexes.
* `Stacks.Cech.Hypercohomology.cechCupClass_natural`: on Čech cohomology classes.
* `Stacks.Cech.Hypercohomology.cup_natural`: on hypercohomology.
* `Stacks.Cech.Hypercohomology.cup_smul_left`: the cup product is linear in the first factor.
* `Stacks.Cech.Hypercohomology.cup_eqToHom`: it does not depend on how its degrees are written.

## References

* [Stacks Project, Section 01FP](https://stacks.math.columbia.edu/tag/01FP)
* [Stacks Project, Tag 07MB](https://stacks.math.columbia.edu/tag/07MB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits ComplexShape Opposite TopologicalSpace
open Stacks.SheafOfModules.Tensor (ringSheaf)
open Stacks.Cohomology.CechSheaf (SectionRing coverObject)
open Stacks.Cech.CupProduct (tensorModules)

universe u

namespace Stacks.Cech.Hypercohomology

variable {X : TopCat.{u}} (O : Sheaf (Opens.grothendieckTopology X) CommRingCat.{u})
  {I : Type u} (U : I → Opens X) (hU : ⊤ = ⨆ i, U i)

/-- The compatibility of two pairings along three morphisms of complexes that the naturality of
the cup product consumes: pairing after the two morphisms is the third morphism after pairing. -/
def PairingHom {K L M K' L' M' : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') (D : Pairing O K L M) (D' : Pairing O K' L' M') :
    Prop :=
  ∀ (a b n : ℤ) (hab : a + b = n),
    ((Stacks.Cech.LinearCupProduct.tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).map
        (((Stacks.Cech.Refinement.sectionsComplex O).map f.hom).f a)).app
          (((Stacks.Cech.Refinement.sectionsComplex O).obj L.obj).X b) ≫
      ((Stacks.Cech.LinearCupProduct.tensorPresheafModules.{u} (SectionRing (ringSheaf O) ⊤)).obj
          (((Stacks.Cech.Refinement.sectionsComplex O).obj K'.obj).X a)).map
          (((Stacks.Cech.Refinement.sectionsComplex O).map g.hom).f b) ≫ D'.μ a b n hab =
      D.μ a b n hab ≫ ((Stacks.Cech.Refinement.sectionsComplex O).map h.hom).f n

/-- **The Čech cup product is natural in the three complexes**, on total Čech complexes. -/
theorem cechCup_natural {K L M K' L' M' : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') (D : Pairing O K L M) (D' : Pairing O K' L' M')
    (hD : PairingHom O f g h D D') :
    HomologicalComplex.mapBifunctorMap ((cech O U hU).map f.hom) ((cech O U hU).map g.hom)
        (tensorModules (SectionRing (ringSheaf O) ⊤)) (up ℤ) ≫ cechCup O U hU D' =
      cechCup O U hU D ≫ (cech O U hU).map h.hom := by
  rw [cech_map_eq, cech_map_eq, cech_map_eq]
  exact conj_cup_aux O (cech_obj_eq O U hU K) (cech_obj_eq O U hU K') (cech_obj_eq O U hU L)
    (cech_obj_eq O U hU L') (cech_obj_eq O U hU M) (cech_obj_eq O U hU M') _ _ _ _ _
    (Stacks.Cech.LinearCupProduct.cechCupProduct_natural_of_pairing_hom (coverObject U hU)
      (SectionRing (ringSheaf O) ⊤) D D' ((Stacks.Cech.Refinement.sectionsComplex O).map f.hom)
      ((Stacks.Cech.Refinement.sectionsComplex O).map g.hom)
      ((Stacks.Cech.Refinement.sectionsComplex O).map h.hom) hD)

/-- A class valued in a projective object is the class of a cocycle. -/
private theorem exists_eq_cocycleClass {C : Type*} [Category* C] [Abelian C]
    {K : CochainComplex C ℤ} {P : C} [Projective P] (n : ℤ) (x : P ⟶ K.homology n) :
    ∃ (z : P ⟶ K.X n) (hz : z ≫ K.d n (n + 1) = 0), x = cocycleClass n z hz := by
  obtain ⟨z, hz, h⟩ := Stacks.CupProduct.exists_liftCycles_homologyπ_eq K n (n + 1)
    (CochainComplex.next ℤ n) x
  exact ⟨z, hz, h.symm⟩

/-- **The cup product of Čech classes is natural in the three complexes.** -/
theorem cechCupClass_natural
    {K L M K' L' M' : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') (D : Pairing O K L M) (D' : Pairing O K' L' M')
    (hD : PairingHom O f g h D D') (p q t : ℤ) (ht : p + q = t)
    (x : unitModule _ ⟶ ((cech O U hU).obj K.obj).homology p)
    (y : unitModule _ ⟶ ((cech O U hU).obj L.obj).homology q) :
    cechCupClass O U hU D p q t ht x y ≫
        HomologicalComplex.homologyMap ((cech O U hU).map h.hom) t =
      cechCupClass O U hU D' p q t ht
        (x ≫ HomologicalComplex.homologyMap ((cech O U hU).map f.hom) p)
        (y ≫ HomologicalComplex.homologyMap ((cech O U hU).map g.hom) q) := by
  obtain ⟨z, hz, rfl⟩ := exists_eq_cocycleClass p x
  obtain ⟨w, hw, rfl⟩ := exists_eq_cocycleClass q y
  rw [cocycleClass_comp_homologyMap, cocycleClass_comp_homologyMap, cechCupClass_eq,
    cechCupClass_eq, Category.assoc, cocycleClass_comp_homologyMap]
  congr 1
  refine cocycleClass_congr t ?_ _ _
  rw [Category.assoc, ← HomologicalComplex.comp_f, ← cechCup_natural O U hU f g h D D' hD,
    HomologicalComplex.comp_f, ← Category.assoc, cupPair_comp_mapBifunctorMap]

/-- Two hypercohomology classes computed by Čech cocycles are computed on a common cover. -/
private theorem exists_cechClass_eq_cechClass
    {K L : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hK : CechComputes O K) (hL : CechComputes O L) (p q : ℤ) (a : hypercohomology O K p)
    (b : hypercohomology O L q) :
    ∃ (I : Type u) (W : I → Opens X) (hW : ⊤ = ⨆ i, W i)
      (x : ((cech O W hW).obj K.obj).homology p) (y : ((cech O W hW).obj L.obj).homology q),
      cechClass O W hW K p x = a ∧ cechClass O W hW L q y = b := by
  obtain ⟨I, U, hU, x, rfl⟩ := (hK p).1 a
  obtain ⟨J, V, hV, y, rfl⟩ := (hL q).1 b
  have hW := iSup_inf_eq_top U hU V hV
  exact ⟨_, _, hW, _, _,
    ConcreteCategory.congr_hom
      (cechClass_refinement O U hU _ hW Prod.fst (fun _ => inf_le_left) K p) x,
    ConcreteCategory.congr_hom
      (cechClass_refinement O V hV _ hW Prod.snd (fun _ => inf_le_right) L q) y⟩

/-- **The cup product on hypercohomology is natural in the three complexes**: for morphisms
`f`, `g`, `h` carrying the pairing `D` to the pairing `D'`, `h(D(a ∪ b)) = D'(f(a) ∪ g(b))`. -/
theorem cup_natural {K L M K' L' M' : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hK : CechComputes O K) (hL : CechComputes O L) (hK' : CechComputes O K')
    (hL' : CechComputes O L') (f : K ⟶ K') (g : L ⟶ L') (h : M ⟶ M') (D : Pairing O K L M)
    (D' : Pairing O K' L' M') (hD : PairingHom O f g h D D') (p q t : ℤ) (ht : p + q = t)
    (a : hypercohomology O K p) (b : hypercohomology O L q) :
    hypercohomologyMap O h t (cup O hK hL D p q t ht a b) =
      cup O hK' hL' D' p q t ht (hypercohomologyMap O f p a) (hypercohomologyMap O g q b) := by
  obtain ⟨I, W, hW, x, y, rfl, rfl⟩ := exists_cechClass_eq_cechClass O hK hL p q a b
  have hf := ConcreteCategory.congr_hom (cechClass_naturality O _ hW f p) x
  have hg := ConcreteCategory.congr_hom (cechClass_naturality O _ hW g q) y
  have hh := cechClass_naturality O _ hW h t
  simp only [ConcreteCategory.comp_apply] at hf hg
  rw [← hf, ← hg, cup_eq O _ hW hK hL, cup_eq O _ hW hK' hL', ← ConcreteCategory.comp_apply,
    Category.assoc, ← hh, ← Category.assoc, cechCupClass_natural O _ hW f g h D D' hD,
    toMor_comp, toMor_comp]

/-! ### Linearity of the cup product in the first factor -/

section Linearity

/-- The cup product of cochains is linear in its first factor. -/
theorem cupPair_smul_left {R : Type u} [CommRing R] (K L : CochainComplex (ModuleCat.{u} R) ℤ)
    {P Q : ModuleCat.{u} R} (p q t : ℤ) (ht : p + q = t) (α : P ⟶ K.X p) (β : Q ⟶ L.X q)
    (r : R) :
    Stacks.CupProduct.cupPair (tensorModules R) K L p q t ht (r • α) β =
      r • Stacks.CupProduct.cupPair (tensorModules R) K L p q t ht α β := by
  have h : ((tensorModules R).map (r • α)).app Q = r • ((tensorModules R).map α).app Q :=
    ModuleCat.hom_ext (TensorProduct.map_smul_left _ _ _)
  dsimp only [Stacks.CupProduct.cupPair]
  rw [h, Linear.smul_comp]

attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing in
/-- **The cup product of Čech classes is linear in the first factor** over the global sections
of `𝒪_X`. -/
theorem cechCupClass_smul_left {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (γ : Pairing O F G H) (p q t : ℤ) (ht : p + q = t)
    (x : ((cech O U hU).obj F.obj).homology p)
    (y : unitModule _ ⟶ ((cech O U hU).obj G.obj).homology q) (r : SectionRing (ringSheaf O) ⊤) :
    cechCupClass O U hU γ p q t ht (toMor (r • x)) y =
      r • cechCupClass O U hU γ p q t ht (toMor x) y := by
  obtain ⟨zx, hzx, hx'⟩ := exists_eq_cocycleClass p (toMor x)
  obtain ⟨zy, hzy, rfl⟩ := exists_eq_cocycleClass q y
  have hrzx : (r • zx) ≫ ((cech O U hU).obj F.obj).d p (p + 1) = 0 := by
    rw [Linear.smul_comp, hzx, smul_zero]
  have hrx : toMor (r • x) = cocycleClass p (r • zx) hrzx := by
    rw [toMor_smul, hx', cocycleClass_smul r p zx hzx hrzx]
  rw [hx', hrx, cechCupClass_eq, cechCupClass_eq, ← Linear.comp_smul]
  congr 1
  have hX := Stacks.CupProduct.cupPair_comp_gamma_comp_d_eq_zero
    (tensorModules (SectionRing (ringSheaf O) ⊤)) ((cech O U hU).obj F.obj)
    ((cech O U hU).obj G.obj) (cechCup O U hU γ) p q t ht zx zy hzx hzy
  have hrX : (r • (Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
      ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj) p q t ht zx zy ≫
        (cechCup O U hU γ).f t)) ≫ ((cech O U hU).obj H.obj).d t (t + 1) = 0 := by
    rw [Linear.smul_comp, hX, smul_zero]
  have e : Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
      ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj) p q t ht (r • zx) zy ≫
        (cechCup O U hU γ).f t =
      r • (Stacks.CupProduct.cupPair (tensorModules (SectionRing (ringSheaf O) ⊤))
      ((cech O U hU).obj F.obj) ((cech O U hU).obj G.obj) p q t ht zx zy ≫
        (cechCup O U hU γ).f t) := by
    rw [cupPair_smul_left, Linear.smul_comp]
  exact (cocycleClass_congr t e _ hrX).trans (cocycleClass_smul r t _ hX hrX)

attribute [local instance high] Stacks.Cech.Refinement.sectionCommRing in
/-- **The cup product is linear in the first factor** over the global sections of `𝒪_X`. -/
theorem cup_smul_left {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (γ : Pairing O F G H) (p q t : ℤ)
    (ht : p + q = t) (a : hypercohomology O F p) (b : hypercohomology O G q)
    (r : SectionRing (ringSheaf O) ⊤) :
    cup O hF hG γ p q t ht (r • a) b = r • cup O hF hG γ p q t ht a b := by
  obtain ⟨I, W, hW, x, y, rfl, rfl⟩ := exists_cechClass_eq_cechClass O hF hG p q a b
  rw [← map_smul, cup_eq O _ hW hF hG, cup_eq O _ hW hF hG, cechCupClass_smul_left,
    Linear.smul_comp]
  rfl

end Linearity

/-- **The cup product does not depend on how its degrees are written**: transporting the factors
along equalities of degrees transports the cup product. -/
theorem cup_eqToHom {F G H : CochainComplex.Plus (SheafOfModules.{u} (ringSheaf O))}
    (hF : CechComputes O F) (hG : CechComputes O G) (γ : Pairing O F G H) {p p' q q' t t' : ℤ}
    (hp : p = p') (hq : q = q') (ht' : t = t') (ht : p + q = t) (h : p' + q' = t')
    (a : hypercohomology O F p) (b : hypercohomology O G q) :
    cup O hF hG γ p' q' t' h ((eqToHom (congrArg (hypercohomology O F) hp)).hom a)
        ((eqToHom (congrArg (hypercohomology O G) hq)).hom b) =
      (eqToHom (congrArg (hypercohomology O H) ht')).hom (cup O hF hG γ p q t ht a b) := by
  subst hp hq ht'
  rfl

end Stacks.Cech.Hypercohomology
