module

public import Mathlib.Algebra.Homology.DerivedCategory.Ext.EnoughProjectives
public import Mathlib.Algebra.Homology.DerivedCategory.FullyFaithful
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Basic

/-!
# Sibling functors out of the bounded derived category of a semisimple abelian category

Let `A` be an abelian category in which every object is projective. Two additive functors
`F G : D^b(A) ⥤ 𝒟` commuting with the shift whose restrictions to `A` are naturally isomorphic
are naturally isomorphic. This is the zero-dimensional case of the proof of
[Stacks, Tag 0G0C]: there `A` is the category of finite dimensional vector spaces over a finite
extension `k'` of `k`, and the source observes that the isomorphism on `𝒪_X` "extends canonically
to an isomorphism on any graded `k'`-vector space". No full faithfulness is needed.

## The proof

Every object of `A` being projective, `Hom(P[-b], L) = 0` whenever `P` is an object of `A` and
`L` has cohomology in degrees `< b`
(`DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective`). Together with the vanishing of
negative `Ext`s this shows that there are no nonzero morphisms between objects concentrated in two
different degrees, and that the truncation triangle `τ_{≤ b} X → X → τ_{≥ b + 1} X →` of an object
concentrated in degrees `[a, b + 1]` splits, its third morphism being such a positive `Ext`. So
every bounded object is, step by step, a binary biproduct of objects of smaller width.

A comparison of `F` and `G` on objects concentrated in one degree is the shift of the given
isomorphism on `A`, and it is natural on these objects because the only morphisms between them
live in a single degree. A comparison natural on a class of objects extends, naturally, to the
class of objects isomorphic to a binary biproduct of two of them
(`AlgebraicGeometry.PartialComparison.exists_extension`): the comparison at `Y ⊞ Z` is the
diagonal one, and naturality is checked one matrix entry at a time. Induction on the width
gives compatible comparisons on all bounded objects.

## Main definitions

* `AlgebraicGeometry.PartialComparison`: a natural comparison of two functors on the objects
  satisfying a property.

## Main results

* `AlgebraicGeometry.PartialComparison.exists_extension`: extension of a comparison along
  binary biproduct decompositions.
* `AlgebraicGeometry.nonempty_iso_of_restrictionIso_of_projective`: two additive functors out of
  `D^b(A)`, commuting with the shift and agreeing on `A`, are isomorphic when every object of `A`
  is projective.

## References

* [Stacks Project, Tag 0G0C](https://stacks.math.columbia.edu/tag/0G0C)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w v v' u u'

namespace AlgebraicGeometry

/-! ### Extending a comparison along binary biproduct decompositions -/

section Extension

variable {C E : Type*} [Category* C] [Category* E] [Preadditive C] [Preadditive E]
  [HasBinaryBiproducts C] (F G : C ⥤ E) [F.Additive] [G.Additive]

/-- A comparison of two functors on the objects satisfying a property `P`, natural with respect
to all morphisms between such objects. -/
structure PartialComparison (P : ObjectProperty C) where
  /-- The comparison at an object satisfying `P`. -/
  app (X : C) : P X → (F.obj X ≅ G.obj X)
  /-- Naturality with respect to every morphism between objects satisfying `P`. -/
  naturality (X Y : C) (hX : P X) (hY : P Y) (f : X ⟶ Y) :
    F.map f ≫ (app Y hY).hom = (app X hX).hom ≫ G.map f

namespace PartialComparison

variable {F G} {P : ObjectProperty C} (c : PartialComparison F G P)

/-- The identity of an object presented as a binary biproduct, split along the two summands. -/
lemma biprod_decomposition {X Y Z : C} (s : X ≅ Y ⊞ Z) :
    s.hom ≫ biprod.fst ≫ biprod.inl ≫ s.inv + s.hom ≫ biprod.snd ≫ biprod.inr ≫ s.inv =
      𝟙 X := by
  rw [← Preadditive.comp_add, ← Category.assoc biprod.fst, ← Category.assoc biprod.snd,
    ← Preadditive.add_comp, biprod.total, Category.id_comp, Iso.hom_inv_id]

private lemma map_biprod_decomposition (H : C ⥤ E) [H.Additive] {X Y Z : C} (s : X ≅ Y ⊞ Z) :
    H.map (s.hom ≫ biprod.fst) ≫ H.map (biprod.inl ≫ s.inv) +
      H.map (s.hom ≫ biprod.snd) ≫ H.map (biprod.inr ≫ s.inv) = 𝟙 _ := by
  rw [← H.map_comp, ← H.map_comp, ← H.map_add, Category.assoc, Category.assoc,
    biprod_decomposition, H.map_id]

private lemma map_inl_comp_map_fst (H : C ⥤ E) [H.Additive] {X Y Z : C} (s : X ≅ Y ⊞ Z) :
    H.map (biprod.inl ≫ s.inv) ≫ H.map (s.hom ≫ biprod.fst) = 𝟙 _ := by
  rw [← H.map_comp]; simp

private lemma map_inl_comp_map_snd (H : C ⥤ E) [H.Additive] {X Y Z : C} (s : X ≅ Y ⊞ Z) :
    H.map (biprod.inl ≫ s.inv) ≫ H.map (s.hom ≫ biprod.snd) = 0 := by
  rw [← H.map_comp]; simp

private lemma map_inr_comp_map_fst (H : C ⥤ E) [H.Additive] {X Y Z : C} (s : X ≅ Y ⊞ Z) :
    H.map (biprod.inr ≫ s.inv) ≫ H.map (s.hom ≫ biprod.fst) = 0 := by
  rw [← H.map_comp]; simp

private lemma map_inr_comp_map_snd (H : C ⥤ E) [H.Additive] {X Y Z : C} (s : X ≅ Y ⊞ Z) :
    H.map (biprod.inr ≫ s.inv) ≫ H.map (s.hom ≫ biprod.snd) = 𝟙 _ := by
  rw [← H.map_comp]; simp

/-- The comparison at an object presented as the biproduct of two objects of `P`: the diagonal
comparison, transported along the presentation. -/
def biprodApp {X Y Z : C} (hY : P Y) (hZ : P Z) (s : X ≅ Y ⊞ Z) : F.obj X ≅ G.obj X where
  hom := F.map (s.hom ≫ biprod.fst) ≫ (c.app Y hY).hom ≫ G.map (biprod.inl ≫ s.inv) +
    F.map (s.hom ≫ biprod.snd) ≫ (c.app Z hZ).hom ≫ G.map (biprod.inr ≫ s.inv)
  inv := G.map (s.hom ≫ biprod.fst) ≫ (c.app Y hY).inv ≫ F.map (biprod.inl ≫ s.inv) +
    G.map (s.hom ≫ biprod.snd) ≫ (c.app Z hZ).inv ≫ F.map (biprod.inr ≫ s.inv)
  hom_inv_id := by
    have h₁ : G.map (biprod.inl ≫ s.inv) ≫ G.map (s.hom ≫ biprod.fst) = 𝟙 _ := by
      rw [← G.map_comp]; simp
    have h₂ : G.map (biprod.inl ≫ s.inv) ≫ G.map (s.hom ≫ biprod.snd) = 0 := by
      rw [← G.map_comp]; simp
    have h₃ : G.map (biprod.inr ≫ s.inv) ≫ G.map (s.hom ≫ biprod.fst) = 0 := by
      rw [← G.map_comp]; simp
    have h₄ : G.map (biprod.inr ≫ s.inv) ≫ G.map (s.hom ≫ biprod.snd) = 𝟙 _ := by
      rw [← G.map_comp]; simp
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, zero_comp, comp_zero,
      add_zero, zero_add, Iso.hom_inv_id_assoc]
    rw [← F.map_comp, ← F.map_comp, ← F.map_add, Category.assoc, Category.assoc,
      biprod_decomposition, F.map_id]
  inv_hom_id := by
    have h₁ : F.map (biprod.inl ≫ s.inv) ≫ F.map (s.hom ≫ biprod.fst) = 𝟙 _ := by
      rw [← F.map_comp]; simp
    have h₂ : F.map (biprod.inl ≫ s.inv) ≫ F.map (s.hom ≫ biprod.snd) = 0 := by
      rw [← F.map_comp]; simp
    have h₃ : F.map (biprod.inr ≫ s.inv) ≫ F.map (s.hom ≫ biprod.fst) = 0 := by
      rw [← F.map_comp]; simp
    have h₄ : F.map (biprod.inr ≫ s.inv) ≫ F.map (s.hom ≫ biprod.snd) = 𝟙 _ := by
      rw [← F.map_comp]; simp
    simp only [Preadditive.add_comp, Preadditive.comp_add, Category.assoc,
      reassoc_of% h₁, reassoc_of% h₂, reassoc_of% h₃, reassoc_of% h₄, zero_comp, comp_zero,
      add_zero, zero_add, Iso.inv_hom_id_assoc]
    rw [← G.map_comp, ← G.map_comp, ← G.map_add, Category.assoc, Category.assoc,
      biprod_decomposition, G.map_id]

/-- Preceded by the inclusion of the first summand, the diagonal comparison is the comparison
at `Y` followed by that inclusion. -/
lemma map_inl_biprodApp_hom {X Y Z : C} (hY : P Y) (hZ : P Z) (s : X ≅ Y ⊞ Z) :
    F.map (biprod.inl ≫ s.inv) ≫ (c.biprodApp hY hZ s).hom =
      (c.app Y hY).hom ≫ G.map (biprod.inl ≫ s.inv) := by
  simp only [biprodApp, Preadditive.comp_add, reassoc_of% (map_inl_comp_map_fst F s),
    reassoc_of% (map_inl_comp_map_snd F s), zero_comp, add_zero]

/-- Preceded by the inclusion of the second summand, the diagonal comparison is the comparison
at `Z` followed by that inclusion. -/
lemma map_inr_biprodApp_hom {X Y Z : C} (hY : P Y) (hZ : P Z) (s : X ≅ Y ⊞ Z) :
    F.map (biprod.inr ≫ s.inv) ≫ (c.biprodApp hY hZ s).hom =
      (c.app Z hZ).hom ≫ G.map (biprod.inr ≫ s.inv) := by
  simp only [biprodApp, Preadditive.comp_add, reassoc_of% (map_inr_comp_map_fst F s),
    reassoc_of% (map_inr_comp_map_snd F s), zero_comp, zero_add]

/-- Followed by the projection to the first summand, the diagonal comparison is the comparison
at `Y` preceded by that projection. -/
lemma biprodApp_hom_map_fst {X Y Z : C} (hY : P Y) (hZ : P Z) (s : X ≅ Y ⊞ Z) :
    (c.biprodApp hY hZ s).hom ≫ G.map (s.hom ≫ biprod.fst) =
      F.map (s.hom ≫ biprod.fst) ≫ (c.app Y hY).hom := by
  simp only [biprodApp, Preadditive.add_comp, Category.assoc, map_inl_comp_map_fst G s,
    map_inr_comp_map_fst G s, comp_zero, add_zero, Category.comp_id]

/-- Followed by the projection to the second summand, the diagonal comparison is the comparison
at `Z` preceded by that projection. -/
lemma biprodApp_hom_map_snd {X Y Z : C} (hY : P Y) (hZ : P Z) (s : X ≅ Y ⊞ Z) :
    (c.biprodApp hY hZ s).hom ≫ G.map (s.hom ≫ biprod.snd) =
      F.map (s.hom ≫ biprod.snd) ≫ (c.app Z hZ).hom := by
  simp only [biprodApp, Preadditive.add_comp, Category.assoc, map_inl_comp_map_snd G s,
    map_inr_comp_map_snd G s, comp_zero, zero_add, Category.comp_id]

omit [G.Additive] in
/-- Two morphisms out of `F X`, for `X` presented as a binary biproduct, agree as soon as they
agree on the two summands. -/
lemma ext_of_biprod {X Y Z : C} (s : X ≅ Y ⊞ Z) {W : E} {φ ψ : F.obj X ⟶ W}
    (h₁ : F.map (biprod.inl ≫ s.inv) ≫ φ = F.map (biprod.inl ≫ s.inv) ≫ ψ)
    (h₂ : F.map (biprod.inr ≫ s.inv) ≫ φ = F.map (biprod.inr ≫ s.inv) ≫ ψ) : φ = ψ := by
  rw [← Category.id_comp φ, ← Category.id_comp ψ, ← map_biprod_decomposition F s,
    Preadditive.add_comp,
    Preadditive.add_comp, Category.assoc, Category.assoc, Category.assoc, Category.assoc, h₁, h₂]

omit [F.Additive] in
/-- Two morphisms into `G X`, for `X` presented as a binary biproduct, agree as soon as they
agree after projecting to the two summands. -/
lemma ext_of_biprod' {X Y Z : C} (s : X ≅ Y ⊞ Z) {W : E} {φ ψ : W ⟶ G.obj X}
    (h₁ : φ ≫ G.map (s.hom ≫ biprod.fst) = ψ ≫ G.map (s.hom ≫ biprod.fst))
    (h₂ : φ ≫ G.map (s.hom ≫ biprod.snd) = ψ ≫ G.map (s.hom ≫ biprod.snd)) : φ = ψ := by
  rw [← Category.comp_id φ, ← Category.comp_id ψ, ← map_biprod_decomposition G s,
    Preadditive.comp_add,
    Preadditive.comp_add, ← Category.assoc, ← Category.assoc φ, h₁, h₂, Category.assoc,
    Category.assoc]

/-- The diagonal comparisons at two biproduct presentations are natural with respect to every
morphism between the two objects: entry by entry, this is the naturality of `c`. -/
lemma biprodApp_naturality {X Y Z X' Y' Z' : C} (hY : P Y) (hZ : P Z) (s : X ≅ Y ⊞ Z)
    (hY' : P Y') (hZ' : P Z') (s' : X' ≅ Y' ⊞ Z') (f : X ⟶ X') :
    F.map f ≫ (c.biprodApp hY' hZ' s').hom = (c.biprodApp hY hZ s).hom ≫ G.map f := by
  have key : ∀ {T T' : C} (hT : P T) (hT' : P T') (i : T ⟶ X) (p : X' ⟶ T')
      (hi : F.map i ≫ (c.biprodApp hY hZ s).hom = (c.app T hT).hom ≫ G.map i)
      (hp : (c.biprodApp hY' hZ' s').hom ≫ G.map p = F.map p ≫ (c.app T' hT').hom),
      F.map i ≫ (F.map f ≫ (c.biprodApp hY' hZ' s').hom) ≫ G.map p =
        F.map i ≫ ((c.biprodApp hY hZ s).hom ≫ G.map f) ≫ G.map p := by
    intro T T' hT hT' i p hi hp
    calc F.map i ≫ (F.map f ≫ (c.biprodApp hY' hZ' s').hom) ≫ G.map p
        = (F.map i ≫ F.map f) ≫ ((c.biprodApp hY' hZ' s').hom ≫ G.map p) := by
          simp only [Category.assoc]
      _ = F.map (i ≫ f ≫ p) ≫ (c.app T' hT').hom := by
          rw [hp]; simp only [Functor.map_comp, Category.assoc]
      _ = (c.app T hT).hom ≫ G.map (i ≫ f ≫ p) := c.naturality T T' hT hT' _
      _ = (F.map i ≫ (c.biprodApp hY hZ s).hom) ≫ G.map f ≫ G.map p := by
          rw [hi]; simp only [Functor.map_comp, Category.assoc]
      _ = F.map i ≫ ((c.biprodApp hY hZ s).hom ≫ G.map f) ≫ G.map p := by
          simp only [Category.assoc]
  apply ext_of_biprod s
  · apply ext_of_biprod' s'
    · simpa only [Category.assoc] using key hY hY' _ _ (c.map_inl_biprodApp_hom hY hZ s)
        (c.biprodApp_hom_map_fst hY' hZ' s')
    · simpa only [Category.assoc] using key hY hZ' _ _ (c.map_inl_biprodApp_hom hY hZ s)
        (c.biprodApp_hom_map_snd hY' hZ' s')
  · apply ext_of_biprod' s'
    · simpa only [Category.assoc] using key hZ hY' _ _ (c.map_inr_biprodApp_hom hY hZ s)
        (c.biprodApp_hom_map_fst hY' hZ' s')
    · simpa only [Category.assoc] using key hZ hZ' _ _ (c.map_inr_biprodApp_hom hY hZ s)
        (c.biprodApp_hom_map_snd hY' hZ' s')

/-- At an object which itself satisfies `P`, the diagonal comparison is the given one. -/
lemma biprodApp_eq {X Y Z : C} (hX : P X) (hY : P Y) (hZ : P Z) (s : X ≅ Y ⊞ Z) :
    c.biprodApp hY hZ s = c.app X hX := by
  ext
  apply ext_of_biprod s
  · rw [c.map_inl_biprodApp_hom, c.naturality]
  · rw [c.map_inr_biprodApp_hom, c.naturality]

/-- **A comparison natural on `P` extends to the objects which are binary biproducts of two
objects of `P`.** The extension is natural with respect to all morphisms between such objects
and agrees with the given comparison on `P`. -/
theorem exists_extension {Q : ObjectProperty C} (hPQ : P ≤ Q)
    (hsplit : ∀ X, Q X → ∃ (Y Z : C) (_ : P Y) (_ : P Z), Nonempty (X ≅ Y ⊞ Z)) :
    ∃ d : PartialComparison F G Q, ∀ X (hX : P X), d.app X (hPQ X hX) = c.app X hX := by
  choose Y Z hY hZ s using hsplit
  refine ⟨{ app := fun X hX => c.biprodApp (hY X hX) (hZ X hX) (s X hX).some
            naturality := fun X X' hX hX' f => c.biprodApp_naturality _ _ _ _ _ _ f }, ?_⟩
  intro X hX
  exact c.biprodApp_eq hX _ _ _

end PartialComparison

end Extension

/-! ### Objects of `D^b(A)` of bounded width -/

section Semisimple

variable {A : Type u} [Category.{v} A] [Abelian A] [HasDerivedCategory.{w} A]

/-- The objects of `D^b(A)` with cohomology in degrees `a, …, a + n` for some `a`. -/
def boundedWidthLE (n : ℕ) : ObjectProperty (DerivedCategory.Bounded A) :=
  fun X => ∃ a : ℤ, X.obj.IsGE a ∧ X.obj.IsLE (a + n)

/-- An object of width at most `m` has width at most `n` for every `n ≥ m`. -/
lemma boundedWidthLE_mono {m n : ℕ} (h : m ≤ n) :
    boundedWidthLE (A := A) m ≤ boundedWidthLE n := by
  rintro X ⟨a, hGE, hLE⟩
  exact ⟨a, hGE, (DerivedCategory.TStructure.t (C := A)).isLE_of_le X.obj (a + m) (a + n)
    (by omega)⟩

/-- Every object of `D^b(A)` has bounded width. -/
lemma exists_boundedWidthLE (X : DerivedCategory.Bounded A) : ∃ n, boundedWidthLE n X := by
  obtain ⟨⟨a, ha⟩, ⟨b, hb⟩⟩ := X.property
  have : X.obj.IsGE a := ha
  have : X.obj.IsLE b := hb
  refine ⟨(b - a).toNat, a, ha, ?_⟩
  exact (DerivedCategory.TStructure.t (C := A)).isLE_of_le X.obj b _ (by omega)

/-- **No positive `Ext` out of a projective object**: a morphism from an object concentrated in
degree `b` whose cohomology is projective to an object with cohomology in degrees `< b` is zero. -/
lemma hom_eq_zero_of_isLE_of_projective {X Y : DerivedCategory A} {b b' : ℤ} (hb : b' < b)
    [X.IsGE b] [X.IsLE b] [Y.IsLE b'] (hproj : ∀ P : A, Projective P) (f : X ⟶ Y) : f = 0 := by
  obtain ⟨N, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X b
  obtain ⟨K, hK, ⟨e'⟩⟩ := Y.exists_iso_Q_obj_of_isLE b'
  have := hproj N
  let i := (DerivedCategory.singleFunctorIsoCompQ A b).app N
  have h := DerivedCategory.from_singleFunctor_obj_eq_zero_of_projective (P := N) (L := K)
    (i.inv ≫ e.inv ≫ f ≫ e'.hom) b' hb
  have hf : f = e.hom ≫ i.hom ≫ (i.inv ≫ e.inv ≫ f ≫ e'.hom) ≫ e'.inv := by simp
  rw [hf, h]
  simp

/-- **Morphisms between objects concentrated in two different degrees vanish**, when every object
of `A` is projective: one direction is a negative `Ext`, the other a positive `Ext` out of a
projective object. -/
lemma hom_eq_zero_of_ne (hproj : ∀ P : A, Projective P) {X Y : DerivedCategory.Bounded A}
    {a b : ℤ} (hab : a ≠ b) (hX : X.obj.IsGE a ∧ X.obj.IsLE a)
    (hY : Y.obj.IsGE b ∧ Y.obj.IsLE b) (f : X ⟶ Y) : f = 0 := by
  have := hX.1
  have := hX.2
  have := hY.1
  have := hY.2
  have hf : (DerivedCategory.Bounded.ι.map f : X.obj ⟶ Y.obj) = 0 := by
    rcases lt_or_gt_of_ne hab with h | h
    · exact (DerivedCategory.TStructure.t (C := A)).zero (X := X.obj) (Y := Y.obj) _ a b h
    · exact hom_eq_zero_of_isLE_of_projective (X := X.obj) (Y := Y.obj) h hproj _
  exact DerivedCategory.Bounded.ι.map_injective (by rw [hf, Functor.map_zero])

/-- An object of `D^b(A)` concentrated in degree `b` is the shift by `-b` of an object of `A`
placed in degree zero. -/
lemma exists_iso_boundedSingle_shift (X : DerivedCategory.Bounded A) (b : ℤ)
    (hX : X.obj.IsGE b ∧ X.obj.IsLE b) :
    ∃ N : A, Nonempty (X ≅ ((boundedSingleFunctor A).obj N)⟦-b⟧) := by
  have := hX.1
  have := hX.2
  obtain ⟨N, ⟨e⟩⟩ := DerivedCategory.exists_iso_singleFunctor_obj_of_isGE_of_isLE X.obj b
  refine ⟨N, ⟨ObjectProperty.isoMk _ (e ≪≫ ?_)⟩⟩
  exact (((DerivedCategory.Bounded.ι.commShiftIso (-b)).app
        ((boundedSingleFunctor A).obj N) ≪≫
      (shiftFunctor (DerivedCategory A) (-b)).mapIso
        ((boundedSingleFunctorCompιIso A).app N) ≪≫
      ((DerivedCategory.singleFunctors A).shiftIso (-b) b 0 (by omega)).app N)).symm

/-- **A bounded object of width `n + 2` is a biproduct of objects of widths `n + 1` and `1`**,
when every object of `A` is projective: the third morphism of the truncation triangle at the top
degree is a positive `Ext` out of a projective object. -/
lemma exists_iso_biprod_of_boundedWidthLE_succ (hproj : ∀ P : A, Projective P) (n : ℕ)
    (X : DerivedCategory.Bounded A) (hX : boundedWidthLE (n + 1) X) :
    ∃ (Y Z : DerivedCategory.Bounded A) (_ : boundedWidthLE n Y) (_ : boundedWidthLE 0 Z),
      Nonempty (X ≅ Y ⊞ Z) := by
  obtain ⟨a, hGE, hLE⟩ := hX
  let b : ℤ := a + n
  have : X.obj.IsGE a := hGE
  have : X.obj.IsLE (a + (n + 1 : ℕ)) := hLE
  have : X.obj.IsLE (b + 1) :=
    (DerivedCategory.TStructure.t (C := A)).isLE_of_le X.obj (a + (n + 1 : ℕ)) (b + 1)
      (by simp [b]; omega)
  have hT := (DerivedCategory.TStructure.t (C := A)).triangleLEGE_distinguished b (b + 1) rfl
    X.obj
  have h₁GE : ((DerivedCategory.TStructure.t (C := A)).truncLE b).obj X.obj |>.IsGE a := by
    infer_instance
  have h₁LE : ((DerivedCategory.TStructure.t (C := A)).truncLE b).obj X.obj |>.IsLE b := by
    infer_instance
  have h₃GE : ((DerivedCategory.TStructure.t (C := A)).truncGE (b + 1)).obj X.obj |>.IsGE
      (b + 1) := by
    infer_instance
  have h₃LE : ((DerivedCategory.TStructure.t (C := A)).truncGE (b + 1)).obj X.obj |>.IsLE
      (b + 1) := by
    infer_instance
  have h₁shift : (((DerivedCategory.TStructure.t (C := A)).truncLE b).obj X.obj⟦(1 : ℤ)⟧).IsLE
      (b - 1) :=
    (DerivedCategory.TStructure.t (C := A)).isLE_shift _ b 1 (b - 1) (by omega)
  have hmor₃ : ((DerivedCategory.TStructure.t (C := A)).triangleLEGE b (b + 1) rfl
      |>.obj X.obj).mor₃ = 0 := by
    have : (((DerivedCategory.TStructure.t (C := A)).triangleLEGE b (b + 1) rfl).obj
      X.obj).obj₃.IsGE (b + 1) := h₃GE
    have : (((DerivedCategory.TStructure.t (C := A)).triangleLEGE b (b + 1) rfl).obj
      X.obj).obj₃.IsLE (b + 1) := h₃LE
    have : ((((DerivedCategory.TStructure.t (C := A)).triangleLEGE b (b + 1) rfl).obj
      X.obj).obj₁⟦(1 : ℤ)⟧).IsLE (b - 1) := h₁shift
    exact hom_eq_zero_of_isLE_of_projective (b := b + 1) (b' := b - 1) (by omega) hproj _
  obtain ⟨e, -, -⟩ := exists_iso_binaryBiproduct_of_distTriang _ hT hmor₃
  let Y : DerivedCategory.Bounded A :=
    ⟨((DerivedCategory.TStructure.t (C := A)).truncLE b).obj X.obj, ⟨⟨a, h₁GE⟩, ⟨b, h₁LE⟩⟩⟩
  let Z : DerivedCategory.Bounded A :=
    ⟨((DerivedCategory.TStructure.t (C := A)).truncGE (b + 1)).obj X.obj,
      ⟨⟨b + 1, h₃GE⟩, ⟨b + 1, h₃LE⟩⟩⟩
  have : PreservesBinaryBiproducts (DerivedCategory.Bounded.ι (C := A)) :=
    preservesBinaryBiproducts_of_preservesBinaryProducts _
  refine ⟨Y, Z, ⟨a, h₁GE, h₁LE⟩, ⟨b + 1, h₃GE, by simpa using h₃LE⟩, ⟨?_⟩⟩
  exact (ObjectProperty.fullyFaithfulι _).preimageIso
    (e ≪≫ (DerivedCategory.Bounded.ι.mapBiprod Y Z).symm)

variable {D : Type u'} [Category.{v'} D] [Preadditive D] [HasShift D ℤ]
  {F G : DerivedCategory.Bounded A ⥤ D} [F.CommShift ℤ] [G.CommShift ℤ]

/-- The isomorphism on `A`, shifted by `n`, as a natural isomorphism of functors on `A`. -/
def shiftedSiblingRestrictionIso (α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G)
    (n : ℤ) :
    boundedSingleFunctor A ⋙ shiftFunctor _ n ⋙ F ≅
      boundedSingleFunctor A ⋙ shiftFunctor _ n ⋙ G :=
  Functor.isoWhiskerLeft _ (F.commShiftIso n) ≪≫ (Functor.associator _ _ _).symm ≪≫
    Functor.isoWhiskerRight α _ ≪≫ Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ (G.commShiftIso n).symm

omit [Preadditive D] in
/-- The shifted isomorphism is natural with respect to all morphisms between shifted objects of
`A`, not only the shifts of morphisms of `A`: the inclusion of `A` and the shift are full. -/
lemma shiftedSiblingRestrictionIso_naturality
    (α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G) (n : ℤ) (N N' : A)
    (f : ((boundedSingleFunctor A).obj N)⟦n⟧ ⟶ ((boundedSingleFunctor A).obj N')⟦n⟧) :
    F.map f ≫ ((shiftedSiblingRestrictionIso α n).app N').hom =
      ((shiftedSiblingRestrictionIso α n).app N).hom ≫ G.map f := by
  let B := boundedSingleFunctor A
  let hB : B.FullyFaithful := Functor.FullyFaithful.ofCompFaithful
    ((Functor.FullyFaithful.ofFullyFaithful (DerivedCategory.singleFunctor A 0)).ofIso
      (boundedSingleFunctorCompιIso A).symm)
  have : B.Full := hB.full
  obtain ⟨g, rfl⟩ := (shiftFunctor (DerivedCategory.Bounded A) n).map_surjective f
  obtain ⟨g₀, rfl⟩ := B.map_surjective g
  exact (shiftedSiblingRestrictionIso α n).hom.naturality g₀

variable [F.Additive] [G.Additive]

/-- The comparison at an object concentrated in degree `-n`, transported from the shifted
isomorphism on `A` along a presentation of the object. -/
def pureComparisonOf (α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G)
    {X : DerivedCategory.Bounded A} (n : ℤ) (N : A)
    (e : X ≅ ((boundedSingleFunctor A).obj N)⟦n⟧) : F.obj X ≅ G.obj X :=
  F.mapIso e ≪≫ (shiftedSiblingRestrictionIso α n).app N ≪≫ G.mapIso e.symm

omit [Preadditive D] [F.Additive] [G.Additive] in
/-- The comparisons at two objects concentrated in the same degree, transported along any
presentations, are natural with respect to every morphism between the two objects. -/
lemma pureComparisonOf_naturality
    (α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G)
    {X X' : DerivedCategory.Bounded A} (n n' : ℤ) (hn : n = n') (N N' : A)
    (e : X ≅ ((boundedSingleFunctor A).obj N)⟦n⟧)
    (e' : X' ≅ ((boundedSingleFunctor A).obj N')⟦n'⟧) (f : X ⟶ X') :
    F.map f ≫ (pureComparisonOf α n' N' e').hom = (pureComparisonOf α n N e).hom ≫ G.map f := by
  subst hn
  let g := e.inv ≫ f ≫ e'.hom
  have h₂ : F.map f ≫ F.map e'.hom = F.map e.hom ≫ F.map g := by
    simp only [g, ← F.map_comp, Iso.hom_inv_id_assoc]
  have h₃ : G.map g ≫ G.map e'.inv = G.map e.inv ≫ G.map f := by
    simp only [g, ← G.map_comp, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  simp only [pureComparisonOf, Iso.trans_hom, Functor.mapIso_hom, Iso.symm_hom, Category.assoc]
  rw [reassoc_of% h₂, reassoc_of% (shiftedSiblingRestrictionIso_naturality α n N N' g), h₃]

variable (F G) in
/-- **The comparison on objects concentrated in a single degree**, natural with respect to all
morphisms between such objects when every object of `A` is projective. -/
def pureComparison (α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G)
    (hproj : ∀ P : A, Projective P) : PartialComparison F G (boundedWidthLE 0) where
  app X hX :=
    pureComparisonOf α (-hX.choose) (exists_iso_boundedSingle_shift X hX.choose
      ⟨hX.choose_spec.1, by simpa using hX.choose_spec.2⟩).choose
      (exists_iso_boundedSingle_shift X hX.choose
        ⟨hX.choose_spec.1, by simpa using hX.choose_spec.2⟩).choose_spec.some
  naturality X Y hX hY f := by
    by_cases h : hX.choose = hY.choose
    · exact pureComparisonOf_naturality α _ _ (by rw [h]) _ _ _ _ f
    · rw [hom_eq_zero_of_ne hproj h ⟨hX.choose_spec.1, by simpa using hX.choose_spec.2⟩
        ⟨hY.choose_spec.1, by simpa using hY.choose_spec.2⟩ f, F.map_zero, G.map_zero,
        zero_comp, comp_zero]

/-- Compatible comparisons on the objects of every bounded width. -/
lemma exists_widthComparisons (α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G)
    (hproj : ∀ P : A, Projective P) :
    ∃ c : ∀ n : ℕ, PartialComparison F G (boundedWidthLE n),
      ∀ n X (hX : boundedWidthLE n X),
        (c (n + 1)).app X (boundedWidthLE_mono (Nat.le_succ n) X hX) = (c n).app X hX := by
  have hext : ∀ n (c : PartialComparison F G (boundedWidthLE (A := A) n)),
      ∃ d : PartialComparison F G (boundedWidthLE (n + 1)),
        ∀ X (hX : boundedWidthLE n X),
          d.app X (boundedWidthLE_mono (Nat.le_succ n) X hX) = c.app X hX := fun n c =>
    c.exists_extension (boundedWidthLE_mono (Nat.le_succ n)) fun X hX => by
      obtain ⟨Y, Z, hY, hZ, e⟩ := exists_iso_biprod_of_boundedWidthLE_succ hproj n X hX
      exact ⟨Y, Z, hY, boundedWidthLE_mono (Nat.zero_le n) Z hZ, e⟩
  choose ext hext using hext
  let c : ∀ n : ℕ, PartialComparison F G (boundedWidthLE (A := A) n) := fun n =>
    Nat.rec (pureComparison F G α hproj) (fun n c => ext n c) n
  exact ⟨c, fun n X hX => hext n (c n) X hX⟩

/-- **[Stacks, Tag 0G0C], the zero-dimensional case.** Let `A` be an abelian category in which
every object is projective. Two additive functors out of `D^b(A)` which commute with the shift
and whose restrictions to `A` are naturally isomorphic are naturally isomorphic. -/
theorem nonempty_iso_of_restrictionIso_of_projective
    (α : boundedSingleFunctor A ⋙ F ≅ boundedSingleFunctor A ⋙ G)
    (hproj : ∀ P : A, Projective P) : Nonempty (F ≅ G) := by
  classical
  obtain ⟨c, hc⟩ := exists_widthComparisons α hproj
  have hc' : ∀ m n (h : m ≤ n) X (hX : boundedWidthLE m X),
      (c n).app X (boundedWidthLE_mono h X hX) = (c m).app X hX := by
    intro m n h
    induction n, h using Nat.le_induction with
    | base => intro X hX; rfl
    | succ n hmn ih =>
      intro X hX
      rw [← ih X hX]
      exact hc n X (boundedWidthLE_mono hmn X hX)
  choose k hk using fun X : DerivedCategory.Bounded A => exists_boundedWidthLE X
  refine ⟨NatIso.ofComponents (fun X => (c (k X)).app X (hk X)) ?_⟩
  intro X Y f
  let n := max (k X) (k Y)
  rw [← hc' (k X) n (le_max_left _ _) X (hk X), ← hc' (k Y) n (le_max_right _ _) Y (hk Y)]
  exact (c n).naturality X Y _ _ f

end Semisimple

end AlgebraicGeometry

end
