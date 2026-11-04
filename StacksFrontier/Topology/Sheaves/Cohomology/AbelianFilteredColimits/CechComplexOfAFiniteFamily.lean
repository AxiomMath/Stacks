module

public import Mathlib.Algebra.Homology.HomologicalComplexLimits
public import Mathlib.Algebra.Homology.ShortComplex.Ab
public import Mathlib.Algebra.Homology.ShortComplex.HomologicalComplex
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Basic
public import Mathlib.CategoryTheory.Limits.ConcreteCategory.Filtered
public import Mathlib.CategoryTheory.Preadditive.Biproducts
public import StacksFrontier.CategoryTheory.Sites.CechComplex

/-!
# The Čech complex of a finite family commutes with colimits

For a finite family `U : ι → C` and a preadditive category `A` with products and coproducts, the
Čech complex functor `CategoryTheory.cechComplexFunctor U : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ`
preserves colimits of any shape:
$$
\check{\mathcal{C}}^\bullet(\mathcal{U}, \operatorname{colim} \mathcal{G}_j) =
\operatorname{colim} \check{\mathcal{C}}^\bullet(\mathcal{U}, \mathcal{G}_j).
$$
Together with the exactness of filtered colimits of abelian groups, it follows that exactness of
Čech complexes in a positive degree passes to filtered colimits of presheaves of abelian groups.

## Main definitions

* `Stacks.Cohomology.CechColimit.cechComplexObjColimitIso`: the isomorphism between the Čech
  complex of a colimit of presheaves and the colimit of their Čech complexes.

## Main results

* `Stacks.Cohomology.CechColimit.preservesColimitsOfShape_cechComplexFunctor`: for a finite
  family `U`, `cechComplexFunctor U` preserves colimits of any shape.
* `Stacks.Cohomology.CechColimit.exactAt_succ_of_isColimit`: a filtered colimit of cochain
  complexes of abelian groups which are exact in a positive degree is exact in that degree.
* `Stacks.Cohomology.CechColimit.exactAt_cechComplex_of_isColimit`: for a finite family `U`, if
  the Čech complex of each presheaf in a filtered system is exact in degree `n + 1`, then so is
  the Čech complex of the colimit presheaf.
* `Stacks.Cohomology.CechColimit.isZero_homology_cechComplex_of_isColimit`: the same statement,
  with exactness phrased as the vanishing of homology in a positive degree.

## References

* [Stacks Project, Tag 0A37](https://stacks.math.columbia.edu/tag/0A37)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Simplicial
open Stacks.CategoryTheory.CechComplex

universe w j j' v v' u u'

namespace Stacks.Cohomology.CechColimit

variable {C : Type u} [Category.{v} C] {A : Type u'} [Category.{v'} A]
  [HasProducts.{w} A] [HasCoproducts.{w} A] [Preadditive A] [HasFiniteProducts C]

omit [HasCoproducts.{w} A] [HasFiniteProducts C] in
/-- In a preadditive category, a finite family with a product has a biproduct. -/
theorem hasBiproduct_of_finite {T : Type w} [Finite T] (f : T → A) : HasBiproduct f :=
  HasBiproduct.of_hasProduct f

attribute [local instance] hasBiproduct_of_finite

variable (T : Type w) (V : T → C)

/-! ### Three descriptions of the degreewise terms -/

/-- The functor sending a presheaf `P` to the product of its values on a family `V : T → C`. -/
def piEval : (Cᵒᵖ ⥤ A) ⥤ A where
  obj P := ∏ᶜ fun t ↦ P.obj (op (V t))
  map α := Limits.Pi.map fun t ↦ α.app _

omit [HasCoproducts.{w} A] in
/-- The Čech complex functor of `U` followed by evaluation in degree `n` is the functor `piEval`
for the family of intersections `inter U x` indexed by the tuples `x : Fin (n + 1) → ι`. -/
theorem cechComplexFunctor_comp_eval {ι : Type w} (U : ι → C) (n : ℕ) :
    cechComplexFunctor U ⋙ HomologicalComplex.eval A (ComplexShape.up ℕ) n =
      piEval (A := A) (Fin (n + 1) → ι) (inter U) :=
  rfl

/-- The functor sending a presheaf `P` to the coproduct of its values on the family `V`, as the
composite of precomposition with the discrete diagram of the `op (V t)` and the colimit functor. -/
def sigmaEval : (Cᵒᵖ ⥤ A) ⥤ A :=
  (Functor.whiskeringLeft (Discrete T) Cᵒᵖ A).obj (Discrete.functor fun t ↦ op (V t)) ⋙ colim

variable [Finite T]

/-- The functor sending a presheaf `P` to the biproduct of its values on the finite family `V`. -/
def biprodEval : (Cᵒᵖ ⥤ A) ⥤ A where
  obj P := ⨁ fun t ↦ P.obj (op (V t))
  map α := biproduct.map fun t ↦ α.app _
  map_id _ := by ext; simp
  map_comp _ _ := by ext; simp

/-- The functor `biprodEval T V` is isomorphic to `piEval T V`. -/
def biprodEvalIsoPiEval : biprodEval (A := A) T V ≅ piEval (A := A) T V :=
  NatIso.ofComponents (fun _ ↦ biproduct.isoProduct _) (by
    intro P Q α
    dsimp [biprodEval, piEval]
    ext t
    simp)

/-- The discrete diagram of the values `P.obj (op (V t))` agrees with the composite of the
discrete diagram of the `op (V t)` with `P`. -/
def discreteDiagIso (P : Cᵒᵖ ⥤ A) :
    Discrete.functor (fun t ↦ P.obj (op (V t))) ≅
      Discrete.functor (fun t ↦ op (V t)) ⋙ P :=
  Discrete.natIso fun _ ↦ Iso.refl _

/-- The functor `biprodEval T V` is isomorphic to `sigmaEval T V`. -/
def biprodEvalIsoSigmaEval : biprodEval (A := A) T V ≅ sigmaEval (A := A) T V :=
  NatIso.ofComponents
    (fun P ↦ biproduct.isoCoproduct _ ≪≫ HasColimit.isoOfNatIso (discreteDiagIso T V P))
    (by
      intro P Q α
      dsimp [biprodEval, sigmaEval]
      refine biproduct.hom_ext' _ _ fun t ↦ ?_
      simp [discreteDiagIso])

/-- For a finite family `V`, the functor `piEval T V` is isomorphic to `sigmaEval T V`. -/
def piEvalIsoSigmaEval : piEval (A := A) T V ≅ sigmaEval (A := A) T V :=
  (biprodEvalIsoPiEval T V).symm ≪≫ biprodEvalIsoSigmaEval T V

/-! ### Preservation of colimits -/

section Preserves

variable {J : Type j} [Category.{j'} J] [HasColimitsOfShape J A]

omit [HasProducts.{w} A] [HasCoproducts.{w} A] [Preadditive A] [HasFiniteProducts C] in
/-- Precomposition with a functor `K : D ⥤ Cᵒᵖ` preserves colimits of shape `J`. -/
theorem preservesColimitsOfShape_whiskeringLeft {D : Type*} [Category.{w} D] (K : D ⥤ Cᵒᵖ) :
    PreservesColimitsOfShape J ((Functor.whiskeringLeft D Cᵒᵖ A).obj K) :=
  preservesColimitsOfShape_of_evaluation _ J fun d ↦
    (inferInstance : PreservesColimitsOfShape J ((evaluation Cᵒᵖ A).obj (K.obj d)))

omit [HasProducts.{w} A] [Preadditive A] [HasFiniteProducts C] [Finite T] in
/-- The functor `sigmaEval T V` preserves colimits of shape `J`. -/
theorem preservesColimitsOfShape_sigmaEval :
    PreservesColimitsOfShape J (sigmaEval (A := A) T V) := by
  have := preservesColimitsOfShape_whiskeringLeft (A := A) (J := J)
    (Discrete.functor fun t ↦ op (V t))
  show PreservesColimitsOfShape J
    ((Functor.whiskeringLeft (Discrete T) Cᵒᵖ A).obj (Discrete.functor fun t ↦ op (V t)) ⋙
      (colim : (Discrete T ⥤ A) ⥤ A))
  infer_instance

omit [HasFiniteProducts C] in
/-- For a finite family `V`, the functor `piEval T V`, sending `P` to `∏ t, P (V t)`, preserves
colimits of shape `J`. -/
theorem preservesColimitsOfShape_piEval :
    PreservesColimitsOfShape J (piEval (A := A) T V) :=
  have := preservesColimitsOfShape_sigmaEval (A := A) (J := J) T V
  preservesColimitsOfShape_of_natIso (piEvalIsoSigmaEval T V).symm

variable {ι : Type w} [Finite ι] (U : ι → C)

/-- For a finite family `U : ι → C`, the Čech complex functor
`cechComplexFunctor U : (Cᵒᵖ ⥤ A) ⥤ CochainComplex A ℕ` preserves colimits of shape `J`. -/
theorem preservesColimitsOfShape_cechComplexFunctor :
    PreservesColimitsOfShape J (cechComplexFunctor (A := A) U) :=
  HomologicalComplex.preservesColimitsOfShape_of_eval _ fun n ↦ by
    rw [cechComplexFunctor_comp_eval]
    exact preservesColimitsOfShape_piEval (J := J) _ _

/-- For a finite family `U`, the Čech complex of a colimit of presheaves is the colimit of their
Čech complexes, as cochain complexes. -/
def cechComplexObjColimitIso (D : J ⥤ (Cᵒᵖ ⥤ A)) [HasColimit D] :
    (cechComplexFunctor (A := A) U).obj (colimit D) ≅
      colimit (D ⋙ cechComplexFunctor (A := A) U) :=
  have := preservesColimitsOfShape_cechComplexFunctor (A := A) (J := J) U
  preservesColimitIso _ _

end Preserves

/-! ### Exactness passes to filtered colimits -/

section Exact

variable {J : Type j} [Category.{j'} J] [IsFilteredOrEmpty J]
  [HasColimitsOfShape J AddCommGrpCat.{u'}]
  [PreservesColimitsOfShape J (forget AddCommGrpCat.{u'})]

/-- Let `c` be a colimit cocone over a filtered diagram `K` of cochain complexes of abelian groups.
If every complex `K.obj i` is exact in degree `n + 1`, then so is `c.pt`. -/
theorem exactAt_succ_of_isColimit {K : J ⥤ CochainComplex AddCommGrpCat.{u'} ℕ}
    {c : Cocone K} (hc : IsColimit c) (n : ℕ)
    (h : ∀ i, (K.obj i).ExactAt (n + 1)) : c.pt.ExactAt (n + 1) := by
  have key : ∀ (m : ℕ), IsColimit ((HomologicalComplex.eval _ _ m).mapCocone c) :=
    fun m ↦ isColimitOfPreserves _ hc
  have hcomm : ∀ (m m' : ℕ) (i : J),
      (K.obj i).d m m' ≫ (c.ι.app i).f m' = (c.ι.app i).f m ≫ c.pt.d m m' :=
    fun m m' i ↦ ((c.ι.app i).comm m m').symm
  have hcommE : ∀ (m m' : ℕ) (i : J) (z : (K.obj i).X m),
      (c.ι.app i).f m' ((K.obj i).d m m' z) = c.pt.d m m' ((c.ι.app i).f m z) := fun m m' i z ↦ by
    simpa only [ConcreteCategory.comp_apply] using ConcreteCategory.congr_hom (hcomm m m' i) z
  have hleg : ∀ (m : ℕ) {a b : J} (g : a ⟶ b),
      (K.map g).f m ≫ (c.ι.app b).f m = (c.ι.app a).f m := fun m a b g ↦ by
    rw [← HomologicalComplex.comp_f, c.w g]
  have hex : ∀ L : CochainComplex AddCommGrpCat.{u'} ℕ, L.ExactAt (n + 1) ↔
      ∀ z : L.X (n + 1), L.d (n + 1) (n + 2) z = 0 → ∃ w : L.X n, L.d n (n + 1) w = z :=
    fun L ↦ by
      rw [HomologicalComplex.exactAt_iff' _ n (n + 1) (n + 2) (CochainComplex.prev_nat_succ n)
        (by simp), ShortComplex.ab_exact_iff]
      exact Iff.rfl
  rw [hex]
  intro x hx
  obtain ⟨i, y, hy⟩ := Concrete.isColimit_exists_rep _ (key (n + 1)) x
  simp only [Functor.mapCocone_ι_app, HomologicalComplex.eval_map] at hy
  have h2 : ((HomologicalComplex.eval _ _ (n + 2)).mapCocone c).ι.app i
        ((K.obj i).d (n + 1) (n + 2) y) =
      ((HomologicalComplex.eval _ _ (n + 2)).mapCocone c).ι.app i 0 := by
    simp only [Functor.mapCocone_ι_app, HomologicalComplex.eval_map, map_zero]
    rw [hcommE, hy]
    exact hx
  obtain ⟨i', f, hf⟩ := (IsColimit.eq_iff' (key (n + 2)) _ _).mp h2
  simp only [Functor.comp_map, HomologicalComplex.eval_map, map_zero] at hf
  have hcyc : (K.obj i').d (n + 1) (n + 2) ((K.map f).f (n + 1) y) = 0 := by
    rw [← ConcreteCategory.comp_apply, (K.map f).comm, ConcreteCategory.comp_apply]
    exact hf
  obtain ⟨w, hw⟩ := (hex _).1 (h i') _ hcyc
  refine ⟨(c.ι.app i').f n w, ?_⟩
  show c.pt.d n (n + 1) ((c.ι.app i').f n w) = x
  rw [← hcommE, hw, ← hy, ← ConcreteCategory.comp_apply, hleg]

variable {ι : Type u'} [Finite ι] (U : ι → C)

/-- Let `U` be a finite family in `C` and let `D` be a filtered system of presheaves of abelian
groups on `C` whose Čech complexes are all exact in degree `n + 1`. Then the Čech complex of the
colimit presheaf is exact in degree `n + 1`. -/
theorem exactAt_cechComplex_of_isColimit {D : J ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u'})} {c : Cocone D}
    (hc : IsColimit c) (n : ℕ)
    (h : ∀ i, ((cechComplexFunctor (A := AddCommGrpCat.{u'}) U).obj (D.obj i)).ExactAt (n + 1)) :
    ((cechComplexFunctor (A := AddCommGrpCat.{u'}) U).obj c.pt).ExactAt (n + 1) :=
  have := preservesColimitsOfShape_cechComplexFunctor (A := AddCommGrpCat.{u'}) (J := J) U
  exactAt_succ_of_isColimit
    (isColimitOfPreserves (cechComplexFunctor (A := AddCommGrpCat.{u'}) U) hc) n h

/-- Let `U` be a finite family in `C`, let `D` be a filtered system of presheaves of abelian groups
on `C` and let `0 < p`. If the degree-`p` homology of the Čech complex of every presheaf in the
system vanishes, then so does that of the Čech complex of the colimit presheaf. -/
theorem isZero_homology_cechComplex_of_isColimit {D : J ⥤ (Cᵒᵖ ⥤ AddCommGrpCat.{u'})}
    {c : Cocone D} (hc : IsColimit c) (p : ℕ) (hp : 0 < p)
    (h : ∀ i, IsZero
      (((cechComplexFunctor (A := AddCommGrpCat.{u'}) U).obj (D.obj i)).homology p)) :
    IsZero (((cechComplexFunctor (A := AddCommGrpCat.{u'}) U).obj c.pt).homology p) := by
  obtain ⟨n, rfl⟩ : ∃ n, p = n + 1 := ⟨p - 1, (Nat.succ_pred_eq_of_pos hp).symm⟩
  rw [← HomologicalComplex.exactAt_iff_isZero_homology]
  exact exactAt_cechComplex_of_isColimit U hc n fun i ↦
    (HomologicalComplex.exactAt_iff_isZero_homology _ _).2 (h i)

end Exact

end Stacks.Cohomology.CechColimit

end
