module

public import StacksFrontier.Topology.Sheaves.Cohomology.Cech.ConcreteTotalKFlat
public import StacksFrontier.CategoryTheory.Sites.CechComplexConcreteTotalComparison
public import StacksFrontier.Algebra.Homology.Embedding.DescExtend

/-!
# The total Čech complex of the cover by the whole space

Let `X` be a topological space and `P` a complex of presheaves of `R`-modules on `X`. For the
cover of `X` by the single open `X`, the total Čech complex `Tot(Č({X}, P))` is homotopy
equivalent to the complex `P(X)` of global sections, extended by zero to negative degrees: the
projection to the Čech-degree-`0` summand and the inclusion of global sections as constant
`0`-cochains are inverse to each other up to homotopy. The homotopy is the sorting homotopy of
`Stacks.CategoryTheory.CechComplex.CochainSorting`, since for a single index the sorting
projection kills every cochain of positive Čech degree.

## Main definitions

* `Stacks.CategoryTheory.CechComplex.TopCover.cover`: the cover of `X` by `X`.
* `Stacks.CategoryTheory.CechComplex.TopCover.globalComplex`: the complex `P(X)`.
* `Stacks.CategoryTheory.CechComplex.TopCover.proj` and `incl`: the projection
  `Tot(Č({X}, P)) ⟶ P(X)` and the inclusion `P(X) ⟶ Tot(Č({X}, P))`.
* `Stacks.CategoryTheory.CechComplex.TopCover.homotopyEquiv`: **the homotopy equivalence**.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace

universe w u r

namespace Stacks.CategoryTheory.CechComplex.TopCover

noncomputable section

open CochainSorting

variable {X : TopCat.{u}} {R : Type r} [CommRing R]

/-- The cover of `X` by the single open `X`. -/
abbrev cover : PUnit.{w + 1} → Opens X := fun _ => ⊤

/-- Every finite intersection of members of the cover by `X` is all of `X`. -/
theorem top_le_inter {m : ℕ} (t : Fin m → PUnit.{w + 1}) :
    (⊤ : Opens X) ≤ inter (cover (X := X)) t := by
  rw [inter_eq_iInf]
  exact le_iInf fun _ => le_rfl

/-- The constant tuple. -/
abbrev unitTuple (m : ℕ) : Fin m → PUnit.{w + 1} := fun _ => PUnit.unit

variable (P : CochainComplex ((Opens X)ᵒᵖ ⥤ ModuleCat.{w} R) ℕ)

/-- **The complex `P(X)` of global sections**, with `P(X)^a = P^a(X)` and differential the value
at `X` of the differential of `P`. -/
abbrev globalComplex : CochainComplex (ModuleCat.{w} R) ℕ where
  X a := (P.X a).obj (op ⊤)
  d a b := (P.d a b).app (op ⊤)
  shape a b h := by rw [P.shape a b h]; rfl
  d_comp_d' a b c _ _ := by rw [← NatTrans.comp_app, P.d_comp_d]; rfl

/-- The projection of `Tot^a(Č({X}, P))` to global sections: the Čech-degree-`0` component. -/
def projX (a : ℕ) : TotX cover P (a : ℤ) →ₗ[R] (P.X a).obj (op ⊤) where
  toFun x := restrict (P.X a) (top_le_inter (unitTuple 1))
    (x ⟨(0, a), by simp⟩ (unitTuple 1))
  map_add' _ _ := map_add _ _ _
  map_smul' _ _ := map_smul _ _ _

/-- The inclusion of global sections into `Tot^a(Č({X}, P))` as constant `0`-cochains. -/
def inclX (a : ℕ) : (P.X a).obj (op ⊤) →ₗ[R] TotX cover P (a : ℤ) :=
  totSingle cover P a 0 a (by simp) ∘ₗ
    LinearMap.pi (fun t => restrict (P.X a) (le_top : inter cover t ≤ ⊤))

/-- `projX P a x` is the restriction to `X` of the Čech-degree-`0` component of `x`. -/
theorem projX_apply (a : ℕ) (x : TotX cover P (a : ℤ)) :
    projX P a x = restrict (P.X a) (top_le_inter (unitTuple 1))
      (x ⟨(0, a), by simp⟩ (unitTuple 1)) :=
  rfl

/-- `inclX P a s` is the Čech-degree-`0` cochain whose value at each tuple is the restriction of
`s`. -/
theorem inclX_apply (a : ℕ) (s : (P.X a).obj (op ⊤)) :
    inclX P a s = totSingle cover P a 0 a (by simp)
      (fun t => restrict (P.X a) (le_top : inter cover t ≤ ⊤) s) :=
  rfl

/-- `projX` is a left inverse of `inclX`. -/
theorem projX_inclX (a : ℕ) (s : (P.X a).obj (op ⊤)) : projX P a (inclX P a s) = s := by
  rw [inclX_apply, projX_apply, totSingle_apply_self, restrict_restrict, restrict_self]

/-- A morphism of presheaves commutes with restriction of sections. -/
private theorem app_restrict {F G : (Opens X)ᵒᵖ ⥤ ModuleCat.{w} R} (f : F ⟶ G) {V W : Opens X}
    (h : V ≤ W) (x : F.obj (op W)) : (f.app (op V)).hom (restrict F h x) =
      restrict G h ((f.app (op W)).hom x) :=
  ConcreteCategory.congr_hom (f.naturality (homOfLE h).op) x

/-- `projX` commutes with the total differential and the differential of `P(X)`. -/
theorem projX_totDTo (a : ℕ) (x : TotX cover P (a : ℤ)) :
    projX P (a + 1) (totDTo cover P a ((a + 1 : ℕ) : ℤ) (by push_cast; rfl) x) =
      ((P.d a (a + 1)).app (op ⊤)).hom (projX P a x) := by
  rw [projX_apply, projX_apply, totDTo_apply, totDCech_zero, zero_add, totDCoef_succ, pow_zero,
    one_smul, cochainMap_apply]
  exact (app_restrict (P.d a (a + 1)) _ _).symm

/-- The Čech differential of the constant `0`-cochain of a global section vanishes. -/
theorem cechD_restrict_top (b : ℕ) (s : (P.X b).obj (op ⊤)) :
    cechD cover (P.X b) 0 (fun t => restrict (P.X b) (le_top : inter cover t ≤ ⊤) s) = 0 := by
  have hc : ∀ (t : Fin 2 → PUnit.{w + 1}) (φ : Fin 1 → Fin 2),
      cres cover (P.X b) φ t (restrict (P.X b) (le_top : inter cover (t ∘ φ) ≤ ⊤) s) =
        restrict (P.X b) (le_top : inter cover t ≤ ⊤) s := by
    intro t φ
    exact restrict_restrict (P.X b) _ (leOfHom (interMap cover t φ)) s
  funext t
  rw [cechD_apply, Fin.sum_univ_two, hc, hc]
  simp

/-- `inclX` commutes with the differential of `P(X)` and the total differential. -/
theorem totDTo_inclX (a : ℕ) (s : (P.X a).obj (op ⊤)) :
    totDTo cover P a ((a + 1 : ℕ) : ℤ) (by push_cast; rfl) (inclX P a s) =
      inclX P (a + 1) (((P.d a (a + 1)).app (op ⊤)).hom s) := by
  rw [inclX_apply, totDTo_totSingle, cechD_restrict_top, map_zero, zero_add, pow_zero, one_smul,
    inclX_apply]
  congr 1
  funext t
  rw [cochainMap_apply]
  exact app_restrict (P.d a (a + 1)) _ _

/-- `inclX P a ∘ projX P a` is the sorting projection `totSort cover P a`. -/
theorem inclX_projX (a : ℕ) (x : TotX cover P (a : ℤ)) :
    inclX P a (projX P a x) = totSort cover P a x := by
  funext ⟨⟨p, b⟩, h⟩
  rcases p with _ | q
  · obtain rfl : b = a := by push_cast at h; omega
    rw [totSort_apply, sort_zero, inclX_apply, totSingle_apply_self]
    funext t
    obtain rfl : t = unitTuple 1 := Subsingleton.elim _ _
    rw [projX_apply, restrict_restrict, restrict_self]
  · rw [totSort_apply, sort_eq_zero cover _ (q + 1) (by simp), inclX_apply,
      totSingle_apply_of_ne _ _ _ _ _ _ _ _ _ _ (by omega)]

/-- `Tot^n(Č({X}, P))` vanishes in negative degrees. -/
theorem isZero_cechTot_X {n : ℤ} (hn : n < 0) : IsZero ((cechTot cover P).X n) := by
  have : IsEmpty (TotIndex n) := ⟨fun ⟨⟨p, a⟩, h⟩ => by omega⟩
  exact ModuleCat.isZero_of_subsingleton _

/-- The projection `Tot(Č({X}, P)) ⟶ P(X)`, on the `ℕ`-indexed restriction of the total
complex. -/
def proj₀ : (cechTot cover P).restriction ComplexShape.embeddingUpNat ⟶ globalComplex P where
  f a := ModuleCat.ofHom (projX P a)
  comm' := by
    rintro a _ rfl
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    revert x
    intro (x : TotX cover P (a : ℤ))
    change ((P.d a (a + 1)).app (op ⊤)).hom (projX P a x) =
      projX P (a + 1) (((cechTot cover P).d a ((a + 1 : ℕ) : ℤ)).hom x)
    rw [cechTot_d_apply' cover P (by push_cast; rfl)]
    exact (projX_totDTo P a x).symm

/-- The inclusion `P(X) ⟶ Tot(Č({X}, P))`, into the `ℕ`-indexed restriction of the total
complex. -/
def incl₀ : globalComplex P ⟶ (cechTot cover P).restriction ComplexShape.embeddingUpNat where
  f a := ModuleCat.ofHom (inclX P a)
  comm' := by
    rintro a _ rfl
    refine ModuleCat.hom_ext (LinearMap.ext fun s => ?_)
    change ((cechTot cover P).d a ((a + 1 : ℕ) : ℤ)).hom (inclX P a s) =
      inclX P (a + 1) (((P.d a (a + 1)).app (op ⊤)).hom s)
    rw [cechTot_d_apply' cover P (by push_cast; rfl)]
    exact totDTo_inclX P a s

/-- The morphism `proj₀ P` lifts along the embedding `ℕ → ℤ`: it vanishes on the components of
`Tot(Č({X}, P))` in negative degrees, which are zero. -/
theorem hasLift_proj₀ : ComplexShape.embeddingUpNat.HasLift (proj₀ P) := by
  intro j hj i' hij
  obtain rfl : j = 0 := by
    rcases j with _ | k
    · rfl
    · exact (hj.2 k (show (k : ℤ) + 1 = ((k + 1 : ℕ) : ℤ) by push_cast; rfl)).elim
  exact (isZero_cechTot_X P (by simp at hij; omega)).eq_of_src _ _

/-- **The projection `Tot(Č({X}, P)) ⟶ P(X)`** to the Čech-degree-`0` component, `P(X)`
extended by zero to negative degrees. -/
def proj : cechTot cover P ⟶ (globalComplex P).extend ComplexShape.embeddingUpNat :=
  ComplexShape.embeddingUpNat.liftExtend (proj₀ P) (hasLift_proj₀ P)

/-- **The inclusion `P(X) ⟶ Tot(Č({X}, P))`** of global sections as constant `0`-cochains. -/
def incl : (globalComplex P).extend ComplexShape.embeddingUpNat ⟶ cechTot cover P :=
  ComplexShape.embeddingUpNat.descExtend (incl₀ P)

/-- The inclusion followed by the projection is the identity of `P(X)`. -/
theorem incl_proj : incl P ≫ proj P = 𝟙 _ := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases hi : 0 ≤ i
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    have h : ComplexShape.embeddingUpNat.f a = (a : ℤ) := rfl
    rw [HomologicalComplex.comp_f, incl, proj, ComplexShape.Embedding.descExtend_f _ h,
      ComplexShape.Embedding.liftExtend_f _ _ _ h]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, HomologicalComplex.id_f]
    have h₁ : (incl₀ P).f a ≫ (proj₀ P).f a = 𝟙 _ :=
      ModuleCat.hom_ext (LinearMap.ext fun s => projX_inclX P a s)
    rw [reassoc_of% h₁, Iso.hom_inv_id]
  · exact ((globalComplex P).isZero_extend_X _ i
      (fun a ha => hi (ha ▸ Int.natCast_nonneg a))).eq_of_src _ _

/-- The projection followed by the inclusion is the sorting endomorphism `totSortHom cover P` of
`Tot(Č({X}, P))`. -/
theorem proj_incl : proj P ≫ incl P = totSortHom cover P := by
  refine HomologicalComplex.hom_ext _ _ fun i => ?_
  by_cases hi : 0 ≤ i
  · obtain ⟨a, rfl⟩ := Int.eq_ofNat_of_zero_le hi
    have h : ComplexShape.embeddingUpNat.f a = (a : ℤ) := rfl
    rw [HomologicalComplex.comp_f, incl, proj, ComplexShape.Embedding.descExtend_f _ h,
      ComplexShape.Embedding.liftExtend_f _ _ _ h]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    refine ModuleCat.hom_ext (LinearMap.ext fun x => ?_)
    revert x
    intro (x : TotX cover P (a : ℤ))
    exact inclX_projX P a x
  · exact (isZero_cechTot_X P (by omega)).eq_of_tgt _ _

/-- **The total Čech complex of the cover by the whole space is homotopy equivalent to the
complex of global sections**, by the projection to the Čech-degree-`0` component and the
inclusion of global sections as constant cochains. -/
def homotopyEquiv :
    HomotopyEquiv (cechTot cover P) ((globalComplex P).extend ComplexShape.embeddingUpNat) where
  hom := proj P
  inv := incl P
  homotopyHomInvId := (Homotopy.ofEq (proj_incl P)).trans (totHomotopy cover P).symm
  homotopyInvHomId := Homotopy.ofEq (incl_proj P)

end

end Stacks.CategoryTheory.CechComplex.TopCover

end
