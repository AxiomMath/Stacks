module

public import StacksCore.Algebra.Homology.HomologicalBicomplex
public import Mathlib.Algebra.Category.Grp.Preadditive
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.Support.HomDoubleComplex
public import StacksCore.Tactic.StacksAttribute

/-!
# The Hom groups of two triangles form a double complex

The morphism groups between the two bi-infinite three-periodic sequences attached to a pair of
distinguished triangles, with differentials given by pre- and postcomposition, form a double
complex of abelian groups. The two differentials square to zero because three consecutive
transition maps of a periodic sequence are the three maps of a distinguished triangle, and they
commute because pre- and postcomposition always do.

## Main definitions

* `AlgebraicGeometry.HomDoubleComplexSetup.homDoubleComplex` is the resulting double complex.

## Main results

* `AlgebraicGeometry.HomDoubleComplexSetup.d₁_comp_d₁` and
  `AlgebraicGeometry.HomDoubleComplexSetup.d₂_comp_d₂`: the two differentials square to zero.
* `AlgebraicGeometry.HomDoubleComplexSetup.d₂_comp_d₁`: the two differentials commute.

## Implementation notes

The three axioms of a double complex are stated separately, and `homDoubleComplex` packages
them with the groups and maps of the underlying setup. Vanishing of two consecutive transition
maps of the periodic sequence is proved case by case on the residue of the degree modulo three;
in the third case the identification `(X⟦n⟧)⟦1⟧ ≅ X⟦n+1⟧` intervenes, and the composite of the
reindexing isomorphisms involved is recorded as its own equation rather than left to the
elaborator.

## References

* [Stacks Project, Tag 0H8B](https://stacks.math.columbia.edu/tag/0H8B)
-/

@[expose] public section

open CategoryTheory
open CategoryTheory.Pretriangulated

namespace AlgebraicGeometry.HomDoubleComplexSetup

universe v u

variable {C : Type u} [Category.{v} C] [Preadditive C] [Limits.HasZeroObject C]
  [HasShift C ℤ] [∀ n : ℤ, (shiftFunctor C n).Additive] [Pretriangulated C]

omit [Limits.HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
private lemma triangleShift_obj₁_comp_obj (T : Triangle C) (a b : ℤ) :
    ((Triangle.shiftFunctor C a ⋙ Triangle.shiftFunctor C b).obj T).obj₁ =
      (shiftFunctor C b).obj ((Triangle.shiftFunctor C a).obj T).obj₁ := rfl

omit [Preadditive C] [Limits.HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
private lemma shiftFunctor_comp_obj (X : C) (a b : ℤ) :
    (shiftFunctor C b).obj ((shiftFunctor C a).obj X) =
      (shiftFunctor C a ⋙ shiftFunctor C b).obj X := rfl

omit [Limits.HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
private lemma triangleShift_obj₁ (T : Triangle C) (n : ℤ) :
    ((Triangle.shiftFunctor C n).obj T).obj₁ = (shiftFunctor C n).obj T.obj₁ := rfl

/-- Two consecutive transition maps of the periodic sequence of a distinguished triangle
compose to zero: the case where the degree is divisible by three. -/
private lemma triangleMap_comp_zero_of_mod_eq_zero (T : Triangle C) (hT : T ∈ distTriang C)
    (p : ℤ) (h0 : p % 3 = 0) :
    triangleMap T p ≫ triangleMap T (p + 1) = 0 := by
  have h1 : (p + 1) % 3 = 1 := by omega
  have h2 : (p + 1 + 1) % 3 = 2 := by omega
  have hn : (p + 1) / 3 = p / 3 := by omega
  have hn₂ : (p + 1 + 1) / 3 = (p + 1) / 3 := by omega
  let S₀ := (Triangle.shiftFunctor C (p / 3)).obj T
  let S₁ := (Triangle.shiftFunctor C ((p + 1) / 3)).obj T
  have heq : S₀ = S₁ := congrArg (fun n : ℤ => (Triangle.shiftFunctor C n).obj T) hn.symm
  let e : S₀ ≅ S₁ := eqToIso heq
  have hA : triangleObject T p = S₀.obj₁ := by
    simp [triangleObject, h0, S₀]
  have hB₀ : triangleObject T (p + 1) = S₀.obj₂ := by
    simp [triangleObject, h1, hn, S₀]
  have hB₁ : triangleObject T (p + 1) = S₁.obj₂ := by
    simp [triangleObject, h1, S₁]
  have hC : triangleObject T (p + 1 + 1) = S₁.obj₃ := by
    simp [triangleObject, h2, hn₂, S₁]
  have hm₀ : triangleMap T p = eqToHom hA ≫ S₀.mor₁ ≫ eqToHom hB₀.symm := by
    unfold triangleMap
    simp [h0, S₀]
  have hm₁ : triangleMap T (p + 1) = eqToHom hB₁ ≫ S₁.mor₂ ≫ eqToHom hC.symm := by
    unfold triangleMap
    simp [h1, S₁]
  have hmid : eqToHom hB₀.symm ≫ eqToHom hB₁ = e.hom.hom₂ := by
    rw [eqToHom_trans]
    change eqToHom (hB₀.symm.trans hB₁) = (eqToHom heq).hom₂
    rw [Triangle.eqToHom_hom₂]
  have hzero : S₀.mor₁ ≫ e.hom.hom₂ ≫ S₁.mor₂ = 0 := by
    rw [← e.hom.comm₂, ← Category.assoc,
      comp_distTriang_mor_zero₁₂ S₀ (Triangle.shift_distinguished T hT (p / 3))]
    simp
  rw [hm₀, hm₁]
  simp only [Category.assoc]
  rw [reassoc_of% hmid, reassoc_of% hzero]
  simp

/-- Two consecutive transition maps of the periodic sequence of a distinguished triangle
compose to zero: the case where the degree is one modulo three. -/
private lemma triangleMap_comp_zero_of_mod_eq_one (T : Triangle C) (hT : T ∈ distTriang C)
    (p : ℤ) (_h0 : ¬ p % 3 = 0) (h1 : p % 3 = 1) :
    triangleMap T p ≫ triangleMap T (p + 1) = 0 := by
  have h2 : (p + 1) % 3 = 2 := by omega
  have h3 : (p + 1 + 1) % 3 = 0 := by omega
  have hn : (p + 1) / 3 = p / 3 := by omega
  have hn₂ : (p + 1 + 1) / 3 = (p + 1) / 3 + 1 := by omega
  let S₀ := (Triangle.shiftFunctor C (p / 3)).obj T
  let S₁ := (Triangle.shiftFunctor C ((p + 1) / 3)).obj T
  let S₂ := (Triangle.shiftFunctor C ((p + 1) / 3 + 1)).obj T
  have heq : S₀ = S₁ :=
    congrArg (fun n : ℤ => (Triangle.shiftFunctor C n).obj T) hn.symm
  let e : S₀ ≅ S₁ := eqToIso heq
  let b := shiftFunctorAdd' C ((p + 1) / 3) 1 ((p + 1) / 3 + 1) rfl
  have hA : triangleObject T p = S₀.obj₂ := by
    simp [triangleObject, h1, S₀]
  have hB₀ : triangleObject T (p + 1) = S₀.obj₃ := by
    simp [triangleObject, h2, hn, S₀]
  have hB₁ : triangleObject T (p + 1) = S₁.obj₃ := by
    simp [triangleObject, h2, S₁]
  have hC : triangleObject T (p + 1 + 1) = S₂.obj₁ := by
    simp [triangleObject, h3, hn₂, S₂]
  have hm₀ : triangleMap T p = eqToHom hA ≫ S₀.mor₂ ≫ eqToHom hB₀.symm := by
    unfold triangleMap
    simp [h1, S₀]
  have hm₁ : triangleMap T (p + 1) =
      eqToHom hB₁ ≫ S₁.mor₃ ≫ b.inv.app T.obj₁ ≫ eqToHom hC.symm := by
    unfold triangleMap
    simp [h2, S₁, b]
  have hmid : eqToHom hB₀.symm ≫ eqToHom hB₁ = e.hom.hom₃ := by
    rw [eqToHom_trans]
    change eqToHom (hB₀.symm.trans hB₁) = (eqToHom heq).hom₃
    rw [Triangle.eqToHom_hom₃]
  have hzero : S₀.mor₂ ≫ e.hom.hom₃ ≫ S₁.mor₃ = 0 := by
    rw [← e.hom.comm₃, ← Category.assoc,
      comp_distTriang_mor_zero₂₃ S₀ (Triangle.shift_distinguished T hT (p / 3))]
    simp
  rw [hm₀, hm₁]
  simp only [Category.assoc]
  rw [reassoc_of% hmid, reassoc_of% hzero]
  simp

/-- For a distinguished triangle `S` and a morphism of triangles `F : S⟦1⟧ ⟶ S'`, the composite
`S.mor₃ ≫ F.hom₁ ≫ S'.mor₁` vanishes. -/
private lemma mor₃_comp_hom₁_comp_mor₁ (S : Triangle C) (hS : S ∈ distTriang C) {S' : Triangle C}
    (F : (Triangle.shiftFunctor C (1 : ℤ)).obj S ⟶ S') : S.mor₃ ≫ F.hom₁ ≫ S'.mor₁ = 0 := by
  have h : S.mor₃ ≫ ((Triangle.shiftFunctor C (1 : ℤ)).obj S).mor₁ = 0 := by
    simp [Triangle.shiftFunctor, Int.negOnePow_one, comp_distTriang_mor_zero₃₁ S hS]
    rfl
  exact (congrArg (fun z => S.mor₃ ≫ z) F.comm₁.symm).trans
    (((Category.assoc _ _ _).symm.trans (congrArg (· ≫ F.hom₂) h)).trans Limits.zero_comp)

/-- Two consecutive transition maps of the periodic sequence of a distinguished triangle
compose to zero: the case where the degree is two modulo three, in which the identification
`(X⟦n⟧)⟦1⟧ ≅ X⟦n+1⟧` intervenes. -/
private lemma triangleMap_comp_zero_of_mod_eq_two (T : Triangle C) (hT : T ∈ distTriang C)
    (p : ℤ) (h0 : ¬ p % 3 = 0) (h1 : ¬ p % 3 = 1) :
    triangleMap T p ≫ triangleMap T (p + 1) = 0 := by
  have h2 : p % 3 = 2 := by omega
  have h3 : (p + 1) % 3 = 0 := by omega
  have h4 : (p + 1 + 1) % 3 = 1 := by omega
  have hn₁ : (p + 1) / 3 = p / 3 + 1 := by omega
  have hn₂ : (p + 1 + 1) / 3 = (p + 1) / 3 := by omega
  let S := (Triangle.shiftFunctor C (p / 3)).obj T
  let S₁ := (Triangle.shiftFunctor C ((p + 1) / 3)).obj T
  let Snext := (Triangle.shiftFunctor C (p / 3 + 1)).obj T
  let R := (Triangle.shiftFunctor C (1 : ℤ)).obj S
  let adj := CategoryTheory.shiftFunctorAdd' C (p / 3) 1 (p / 3 + 1) rfl
  let eTri := Triangle.shiftFunctorAdd' C (p / 3) 1 (p / 3 + 1) rfl
  have heq : Snext = S₁ :=
    congrArg (fun n : ℤ => (Triangle.shiftFunctor C n).obj T) hn₁.symm
  let j : Snext ≅ S₁ := eqToIso heq
  -- `F` is the triangle morphism `R ⟶ S₁` whose first component is the object-level shift
  -- comparison `adj`; its first commuting square is what makes the composite vanish.
  let F : R ⟶ S₁ := eTri.inv.app T ≫ j.hom
  have hA : triangleObject T p = S.obj₃ := by
    simp [triangleObject, h2, S]
  have hEnd : triangleObject T (p + 1) = Snext.obj₁ := by
    simp [triangleObject, h3, hn₁, Snext]
  have hB : triangleObject T (p + 1) = S₁.obj₁ := by
    simp [triangleObject, h3, S₁]
  have hC : triangleObject T (p + 1 + 1) = S₁.obj₂ := by
    simp [triangleObject, h4, hn₂, S₁]
  have hm₀ : triangleMap T p =
      eqToHom hA ≫ S.mor₃ ≫ adj.inv.app T.obj₁ ≫ eqToHom hEnd.symm := by
    unfold triangleMap
    simp [h2, S, adj]
  have hm₁ : triangleMap T (p + 1) = eqToHom hB ≫ S₁.mor₁ ≫ eqToHom hC.symm := by
    unfold triangleMap
    simp [h3, S₁]
  have hmid : eqToHom hEnd.symm ≫ eqToHom hB = j.hom.hom₁ := by
    rw [eqToHom_trans]
    change eqToHom (hEnd.symm.trans hB) = (eqToHom heq).hom₁
    rw [Triangle.eqToHom_hom₁]
  -- The remaining identities are assembled as terms rather than by `rewrite`: each of them
  -- composes across the definitional identification of `R.obj₁` with `S.obj₁⟦1⟧`, which
  -- `rewrite` cannot abstract over, while `congrArg` with an explicit function can.
  have e1 : (adj.inv.app T.obj₁ ≫ eqToHom hEnd.symm) ≫ eqToHom hB = F.hom₁ :=
    (Category.assoc _ _ _).trans
      (congrArg (fun z : Snext.obj₁ ⟶ S₁.obj₁ => adj.inv.app T.obj₁ ≫ z) hmid)
  have hfinal : S.mor₃ ≫
      ((adj.inv.app T.obj₁ ≫ eqToHom hEnd.symm) ≫ eqToHom hB) ≫ S₁.mor₁ = 0 :=
    (congrArg (fun z : R.obj₁ ⟶ S₁.obj₁ => S.mor₃ ≫ z ≫ S₁.mor₁) e1).trans
      (mor₃_comp_hom₁_comp_mor₁ S (Triangle.shift_distinguished T hT (p / 3)) F)
  have hassoc : eqToHom hA ≫
      (S.mor₃ ≫ ((adj.inv.app T.obj₁ ≫ eqToHom hEnd.symm) ≫ eqToHom hB) ≫ S₁.mor₁) ≫
        eqToHom hC.symm = 0 :=
    (congrArg (fun z : S.obj₃ ⟶ S₁.obj₂ => eqToHom hA ≫ z ≫ eqToHom hC.symm) hfinal).trans
      (by simp)
  rw [hm₀, hm₁]
  simpa only [Category.assoc] using hassoc

private lemma triangleMap_comp_zero (T : Triangle C) (hT : T ∈ distTriang C) (p : ℤ) :
    triangleMap T p ≫ triangleMap T (p + 1) = 0 := by
  by_cases h0 : p % 3 = 0
  · exact triangleMap_comp_zero_of_mod_eq_zero T hT p h0
  · by_cases h1 : p % 3 = 1
    · exact triangleMap_comp_zero_of_mod_eq_one T hT p h0 h1
    · exact triangleMap_comp_zero_of_mod_eq_two T hT p h0 h1

omit [Limits.HasZeroObject C] [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C] in
private lemma triangleMap_transport (T : Triangle C) {i j k : ℤ}
    (h : i + 1 = j) (h' : j + 1 = k) :
    eqToHom (congrArg (triangleObject T) h) ≫
        triangleMap T j ≫
        eqToHom (congrArg (triangleObject T) h') =
      triangleMap T (i + 1) ≫
        eqToHom (congrArg (triangleObject T)
          (show (i + 1) + 1 = k by omega)) := by
  cases h
  cases h'
  simp

/-- Consecutive horizontal differentials in the Hom double complex compose to zero. -/
@[stacks 0H8B "hom_double_complex: the horizontal differential squares to zero"]
lemma d₁_comp_d₁ (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) :
    AddCommGrpCat.ofHom (K.d₁ p q) ≫ AddCommGrpCat.ofHom (K.d₁ (p + 1) q) = 0 := by
  ext f
  change K.d₁ (p + 1) q (K.d₁ p q f) = 0
  simp only [HomDoubleComplexSetup.d₁, Preadditive.leftComp,
    AddMonoidHom.mk'_apply]
  have hidx : -(p + 1 + 1) + 1 = -(p + 1) := by omega
  have hidx' : -(p + 1) + 1 = -p := by omega
  have htrans := congrArg (fun g => triangleMap K.X (-(p + 1 + 1)) ≫ g ≫ f)
    (triangleMap_transport K.X hidx hidx')
  simp only [Category.assoc] at htrans ⊢
  rw [htrans]
  simp only [← Category.assoc]
  simp [triangleMap_comp_zero K.X K.X_distinguished (-(p + 1 + 1))]

/-- Consecutive vertical differentials in the Hom double complex compose to zero. -/
@[stacks 0H8B "hom_double_complex: the vertical differential squares to zero"]
lemma d₂_comp_d₂ (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) :
    AddCommGrpCat.ofHom (K.d₂ p q) ≫ AddCommGrpCat.ofHom (K.d₂ p (q + 1)) = 0 := by
  ext f
  change K.d₂ p (q + 1) (K.d₂ p q f) = 0
  simp only [HomDoubleComplexSetup.d₂, Preadditive.rightComp,
    AddMonoidHom.mk'_apply, Category.assoc]
  simpa using congrArg (fun g => f ≫ g) (triangleMap_comp_zero K.Y K.Y_distinguished q)

/-- The horizontal and vertical differentials in the Hom double complex commute. -/
@[stacks 0H8B "hom_double_complex: the two differentials commute"]
lemma d₂_comp_d₁ (K : HomDoubleComplexSetup (C := C)) (p q : ℤ) :
    AddCommGrpCat.ofHom (K.d₂ p q) ≫ AddCommGrpCat.ofHom (K.d₁ p (q + 1)) =
      AddCommGrpCat.ofHom (K.d₁ p q) ≫ AddCommGrpCat.ofHom (K.d₂ (p + 1) q) := by
  ext f
  change K.d₁ p (q + 1) (K.d₂ p q f) = K.d₂ (p + 1) q (K.d₁ p q f)
  simp only [HomDoubleComplexSetup.d₁, HomDoubleComplexSetup.d₂,
    Preadditive.leftComp, Preadditive.rightComp,
    AddMonoidHom.mk'_apply, Category.assoc]

/-- The double complex of abelian groups obtained from a pair of distinguished triangles. -/
@[stacks 0H8B "hom_double_complex"]
noncomputable def homDoubleComplex (K : HomDoubleComplexSetup (C := C)) :
    HomologicalComplex₂.DoubleComplex AddCommGrpCat where
  X p q := AddCommGrpCat.of (K.term p q)
  d₁ p q := AddCommGrpCat.ofHom (K.d₁ p q)
  d₂ p q := AddCommGrpCat.ofHom (K.d₂ p q)
  d₁_comp_d₁ := d₁_comp_d₁ K
  d₂_comp_d₂ := d₂_comp_d₂ K
  comm := d₂_comp_d₁ K

end AlgebraicGeometry.HomDoubleComplexSetup
