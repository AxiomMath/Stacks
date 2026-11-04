module

public import Mathlib.CategoryTheory.Preadditive.Basic
public import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
public import Mathlib.CategoryTheory.Limits.Shapes.Products
public import Mathlib.CategoryTheory.Limits.Shapes.ZeroMorphisms
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Kernels

/-!
# Matrices of morphisms between finite coproducts of copies of one object

Let `O` be an object of a preadditive category and let `P`, `Q` be finite coproducts of copies of
`O`, presented by colimit cofans. A morphism `a : Q ⟶ P` has a matrix of endomorphisms of `O`: the
entry at `(j, i)` is the `j`-th inclusion into `Q`, followed by `a` and by the `i`-th projection out
of `P`, the projections being the ones the coproduct has in a preadditive category. The matrix
determines `a`, and a cokernel of `a` is determined up to isomorphism by the matrix alone: two
objects presented as cokernels of morphisms with the same matrix are isomorphic. This is the
counting device behind bounds on the number of isomorphism classes of finitely presented objects.

## Main definitions

* `CategoryTheory.Limits.cofanProj`: the projections of a coproduct of copies of `O`.
* `CategoryTheory.Limits.cofanMatrix`: the matrix of a morphism between two such coproducts.
* `CategoryTheory.Limits.isoOfCofanMatrixEq`: cokernels of morphisms with equal matrices are
  isomorphic.
-/

@[expose] public noncomputable section

open CategoryTheory

namespace CategoryTheory.Limits

variable {D : Type*} [Category* D] [Preadditive D] {O : D}

section Proj

variable {n : ℕ} {P : D} {ι : Fin n → (O ⟶ P)} (hP : IsColimit (Cofan.mk P ι))

open Classical in
/-- The `i`-th projection out of a finite coproduct of copies of `O`: the identity on the `i`-th
summand and zero on the others. -/
def cofanProj (i : Fin n) : P ⟶ O :=
  Cofan.IsColimit.desc hP fun i' => if i' = i then 𝟙 O else 0

open Classical in
/-- The `l`-th inclusion followed by the `i`-th projection is the identity if `l = i` and zero
otherwise. -/
@[reassoc]
theorem ι_cofanProj (l i : Fin n) : ι l ≫ cofanProj hP i = if l = i then 𝟙 O else 0 :=
  Cofan.IsColimit.fac hP _ l

/-- The projections and the inclusions of a finite coproduct of copies of `O` decompose the
identity: `∑ i, cofanProj hP i ≫ ι i = 𝟙 P`. -/
theorem sum_cofanProj_ι : ∑ i, cofanProj hP i ≫ ι i = 𝟙 P := by
  refine Cofan.IsColimit.hom_ext hP _ _ fun l => ?_
  simp only [cofan_mk_inj, Preadditive.comp_sum]
  simp only [← Category.assoc, ι_cofanProj]
  simp only [ite_comp, Category.id_comp, zero_comp]
  rw [Finset.sum_ite_eq Finset.univ l ι]
  simp

/-- A morphism into a finite coproduct of copies of `O` is determined by its components. -/
theorem hom_ext_of_cofanProj {X : D} {f g : X ⟶ P}
    (h : ∀ i, f ≫ cofanProj hP i = g ≫ cofanProj hP i) : f = g := by
  rw [← Category.comp_id f, ← Category.comp_id g, ← sum_cofanProj_ι hP]
  simp only [Preadditive.comp_sum, ← Category.assoc, h]

end Proj

section Matrix

variable {n k : ℕ} {P Q : D} {ι : Fin n → (O ⟶ P)} {κ : Fin k → (O ⟶ Q)}

/-- **The matrix of a morphism between finite coproducts of copies of `O`.** -/
def cofanMatrix (hP : IsColimit (Cofan.mk P ι)) (κ : Fin k → (O ⟶ Q)) (a : Q ⟶ P) :
    Fin k → Fin n → (O ⟶ O) :=
  fun j i => κ j ≫ a ≫ cofanProj hP i

variable {P' Q' : D} {ι' : Fin n → (O ⟶ P')} {κ' : Fin k → (O ⟶ Q')}
  (hP : IsColimit (Cofan.mk P ι)) (hQ : IsColimit (Cofan.mk Q κ))
  (hP' : IsColimit (Cofan.mk P' ι')) (hQ' : IsColimit (Cofan.mk Q' κ'))

/-- The comparison of two coproducts of the same copies of `O`. -/
def cofanIso : P ≅ P' :=
  hP.coconePointUniqueUpToIso hP'

omit [Preadditive D] in
/-- The comparison `cofanIso hP hP'` sends the `l`-th inclusion into `P` to the `l`-th inclusion
into `P'`. -/
@[reassoc (attr := simp)]
theorem ι_cofanIso_hom (l : Fin n) : ι l ≫ (cofanIso hP hP').hom = ι' l :=
  hP.comp_coconePointUniqueUpToIso_hom hP' ⟨l⟩

/-- The comparison `cofanIso hP hP'` is compatible with the projections. -/
theorem cofanIso_hom_cofanProj (i : Fin n) :
    (cofanIso hP hP').hom ≫ cofanProj hP' i = cofanProj hP i := by
  refine Cofan.IsColimit.hom_ext hP _ _ fun l => ?_
  simp only [cofan_mk_inj, ι_cofanIso_hom_assoc, ι_cofanProj]

/-- Morphisms with equal matrices correspond under the comparisons of the coproducts. -/
theorem comp_cofanIso_eq_of_cofanMatrix_eq {a : Q ⟶ P} {a' : Q' ⟶ P'}
    (hm : cofanMatrix hP κ a = cofanMatrix hP' κ' a') :
    a ≫ (cofanIso hP hP').hom = (cofanIso hQ hQ').hom ≫ a' := by
  refine Cofan.IsColimit.hom_ext hQ _ _ fun j => ?_
  simp only [cofan_mk_inj, ι_cofanIso_hom_assoc]
  refine hom_ext_of_cofanProj hP' fun i => ?_
  rw [Category.assoc, Category.assoc, cofanIso_hom_cofanProj, Category.assoc]
  exact congrFun (congrFun hm j) i

variable {M M' : D} {a : Q ⟶ P} {b : P ⟶ M} {hab : a ≫ b = 0}
  {a' : Q' ⟶ P'} {b' : P' ⟶ M'} {hab' : a' ≫ b' = 0}

/-- The form of `comp_cofanIso_eq_of_cofanMatrix_eq` with the inverses of the comparisons. -/
theorem cofanIso_comp_eq_of_cofanMatrix_eq (hm : cofanMatrix hP κ a = cofanMatrix hP' κ' a') :
    a' ≫ (cofanIso hP hP').inv = (cofanIso hQ hQ').inv ≫ a := by
  rw [Iso.comp_inv_eq, Category.assoc, comp_cofanIso_eq_of_cofanMatrix_eq hP hQ hP' hQ' hm,
    Iso.inv_hom_id_assoc]

/-- **Cokernels of morphisms with equal matrices are isomorphic.** -/
def isoOfCofanMatrixEq (hc : IsColimit (CokernelCofork.ofπ b hab))
    (hc' : IsColimit (CokernelCofork.ofπ b' hab'))
    (hm : cofanMatrix hP κ a = cofanMatrix hP' κ' a') : M ≅ M' :=
  let f := CokernelCofork.IsColimit.desc' hc ((cofanIso hP hP').hom ≫ b') (by
    rw [← Category.assoc, comp_cofanIso_eq_of_cofanMatrix_eq hP hQ hP' hQ' hm, Category.assoc,
      hab', comp_zero])
  let g := CokernelCofork.IsColimit.desc' hc' ((cofanIso hP hP').inv ≫ b) (by
    rw [← Category.assoc, cofanIso_comp_eq_of_cofanMatrix_eq hP hQ hP' hQ' hm, Category.assoc,
      hab, comp_zero])
  { hom := f.1
    inv := g.1
    hom_inv_id := by
      refine Cofork.IsColimit.hom_ext hc ?_
      have hf : b ≫ f.1 = (cofanIso hP hP').hom ≫ b' := f.2
      have hg : b' ≫ g.1 = (cofanIso hP hP').inv ≫ b := g.2
      change b ≫ f.1 ≫ g.1 = b ≫ 𝟙 M
      rw [← Category.assoc, hf, Category.assoc, hg, Iso.hom_inv_id_assoc, Category.comp_id]
    inv_hom_id := by
      refine Cofork.IsColimit.hom_ext hc' ?_
      have hf : b ≫ f.1 = (cofanIso hP hP').hom ≫ b' := f.2
      have hg : b' ≫ g.1 = (cofanIso hP hP').inv ≫ b := g.2
      change b' ≫ g.1 ≫ f.1 = b' ≫ 𝟙 M'
      rw [← Category.assoc, hg, Category.assoc, hf, Iso.inv_hom_id_assoc, Category.comp_id] }

end Matrix

end CategoryTheory.Limits

end
