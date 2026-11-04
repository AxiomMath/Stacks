module

public import Mathlib.CategoryTheory.Abelian.Subcategory
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Isomorphism
public import StacksFrontier.AlgebraicGeometry.DerivedVarieties.SiblingFunctors.Semisimple
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategoryBounded
public import StacksFrontier.CategoryTheory.Localization.NatTransMapDerivedCategory
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedTensor.ExtensionByZeroDerivedAdjunction

/-!
# Sibling functors and orthogonal decompositions of an abelian category

Let `A` be an abelian category which is the orthogonal sum of finitely many full subcategories
`A_i`: every object is a finite biproduct of objects of the pieces, and there are no nonzero
morphisms between objects of two different pieces. If each piece either has enough negative
objects or has all its objects projective, then sibling exact functors out of `D^b(A)`, the
first fully faithful, are isomorphic.

This is the reduction step of the proof of [Stacks, Tag 0G0C], which decomposes `X` into its
connected components and treats the components of dimension zero and of positive dimension
separately ("Details omitted" in the source). The positive-dimensional pieces are handled by
[Stacks, Tag 0FZW] (`AlgebraicGeometry.iso_of_areSiblings_of_fullyFaithful`), the
zero-dimensional ones by `AlgebraicGeometry.nonempty_iso_of_restrictionIso_of_projective`.

## The construction

Each piece `A_i` is closed under subobjects, quotients and finite products, so it is an abelian
category, and the projection `r_i : A ⥤ A_i` onto the `i`-th summand is both left and right
adjoint to the inclusion `ι_i`, with `r_i ι_i ≅ 𝟭`. Hence `ι_i` and `r_i` are exact, the derived
functor of `ι_i` is fully faithful (its derived adjunction has invertible unit), and the derived
functors of the projections `𝟭 ⟶ ι_i r_i` and inclusions `ι_i r_i ⟶ 𝟭` satisfy on `D^b(A)` the
same relations as on `A`: they sum to the identity and are orthogonal idempotents. The two
siblings, restricted along `D^b(A_i) ⥤ D^b(A)`, are siblings out of `D^b(A_i)`, so they are
isomorphic there; and isomorphisms on the images of the `ι_i r_i` glue, along the relations, to
an isomorphism `F ≅ F'` (`AlgebraicGeometry.nonempty_iso_of_sum_eq_id`).

## Main definitions

* `AlgebraicGeometry.OrthogonalDecomposition`: a decomposition of an abelian category into
  finitely many mutually orthogonal pieces.
* `AlgebraicGeometry.OrthogonalDecomposition.projFunctor`: the projection onto a piece.

## Main results

* `AlgebraicGeometry.nonempty_iso_of_sum_eq_id`: gluing isomorphisms along a decomposition of
  the identity into orthogonal idempotents.
* `AlgebraicGeometry.OrthogonalDecomposition.nonempty_iso_of_areSiblings`: sibling functors out of
  the bounded derived category of an orthogonal sum of pieces which have enough negative objects
  or are semisimple are isomorphic when the first is fully faithful.

## References

* [Stacks Project, Tag 0G0C](https://stacks.math.columbia.edu/tag/0G0C)
* [Stacks Project, Tag 0FZW](https://stacks.math.columbia.edu/tag/0FZW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Pretriangulated

universe w w' v v' u u'

/-! ### Additivity of the derived form of a natural transformation -/

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  {F G : C ⥤ D} [F.Additive] [G.Additive]
  [PreservesFiniteLimits F] [PreservesFiniteColimits F]
  [PreservesFiniteLimits G] [PreservesFiniteColimits G]

/-- The derived form of a sum of natural transformations is the sum of their derived forms. -/
theorem NatTrans.mapDerivedCategory_add (η η' : F ⟶ G) :
    NatTrans.mapDerivedCategory (η + η') =
      NatTrans.mapDerivedCategory η + NatTrans.mapDerivedCategory η' :=
  Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) fun K => by
      have h : (NatTrans.mapHomologicalComplex (η + η') (ComplexShape.up ℤ)).app K =
          (NatTrans.mapHomologicalComplex η (ComplexShape.up ℤ)).app K +
            (NatTrans.mapHomologicalComplex η' (ComplexShape.up ℤ)).app K := by
        ext n
        simp
      rw [NatTrans.app_add, NatTrans.mapDerivedCategory_app_Q,
        NatTrans.mapDerivedCategory_app_Q, NatTrans.mapDerivedCategory_app_Q, h,
        Functor.map_add, Preadditive.add_comp, Preadditive.comp_add]

/-- The derived form of the zero natural transformation is zero. -/
theorem NatTrans.mapDerivedCategory_zero :
    NatTrans.mapDerivedCategory (0 : F ⟶ G) = 0 :=
  Localization.natTrans_ext DerivedCategory.Q
    (HomologicalComplex.quasiIso C (ComplexShape.up ℤ)) fun K => by
      have h : (NatTrans.mapHomologicalComplex (0 : F ⟶ G) (ComplexShape.up ℤ)).app K = 0 := by
        ext n
        simp
      rw [NatTrans.mapDerivedCategory_app_Q, h, Functor.map_zero, zero_comp, comp_zero,
        NatTrans.app_zero]

/-- The derived form of a finite sum of natural transformations is the sum of their derived
forms. -/
theorem NatTrans.mapDerivedCategory_sum {ι : Type*} (s : Finset ι) (η : ι → (F ⟶ G)) :
    NatTrans.mapDerivedCategory (∑ i ∈ s, η i) = ∑ i ∈ s, NatTrans.mapDerivedCategory (η i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using NatTrans.mapDerivedCategory_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, NatTrans.mapDerivedCategory_add, ih]

end CategoryTheory

namespace CategoryTheory.Functor

variable {C : Type u} [Category.{v} C] [Abelian C] [HasDerivedCategory.{w} C]
  {D : Type u'} [Category.{v'} D] [Abelian D] [HasDerivedCategory.{w'} D]
  (F : C ⥤ D) [F.Additive] [PreservesFiniteLimits F] [PreservesFiniteColimits F]

/-- The action of an exact functor on bounded derived categories, followed by the inclusion of
`D^b`, is the inclusion of `D^b` followed by the action on unbounded derived categories. -/
def mapDerivedCategoryBoundedCompιIso :
    F.mapDerivedCategoryBounded ⋙ DerivedCategory.Bounded.ι ≅
      DerivedCategory.Bounded.ι ⋙ F.mapDerivedCategory :=
  Iso.refl _

/-- The action of an exact functor on bounded derived categories commutes with the shift: it does
so after composition with the fully faithful inclusion of `D^b`, where it becomes the action on
unbounded derived categories. -/
noncomputable instance commShift_mapDerivedCategoryBounded :
    F.mapDerivedCategoryBounded.CommShift ℤ :=
  Functor.CommShift.ofComp F.mapDerivedCategoryBoundedCompιIso ℤ

/-- The isomorphism `mapDerivedCategoryBoundedCompιIso` commutes with the shifts. -/
instance natTransCommShift_mapDerivedCategoryBoundedCompιIso :
    NatTrans.CommShift F.mapDerivedCategoryBoundedCompιIso.hom ℤ :=
  Functor.CommShift.ofComp_compatibility _ _

/-- The action of an exact functor on bounded derived categories is a triangulated functor. -/
instance isTriangulated_mapDerivedCategoryBounded : F.mapDerivedCategoryBounded.IsTriangulated :=
  (Functor.isTriangulated_iff_comp_right F.mapDerivedCategoryBoundedCompιIso).2 inferInstance

/-- The action on bounded derived categories is fully faithful as soon as the action on
unbounded derived categories is. -/
def fullyFaithfulMapDerivedCategoryBounded (hF : F.mapDerivedCategory.FullyFaithful) :
    F.mapDerivedCategoryBounded.FullyFaithful :=
  Functor.FullyFaithful.ofCompFaithful (G := DerivedCategory.Bounded.ι)
    ((ObjectProperty.fullyFaithfulι _).comp hF)

end CategoryTheory.Functor

namespace AlgebraicGeometry

/-! ### Gluing isomorphisms along a decomposition of the identity -/

section Gluing

variable {C E : Type*} [Category* C] [Category* E] [Preadditive C] [Preadditive E]
  {I : Type*} [Fintype I] [DecidableEq I] {F G : C ⥤ E} [F.Additive] [G.Additive]

omit [Preadditive C] [Preadditive E] [F.Additive] [G.Additive] in
/-- For `p : 𝟭 ⟶ R`, `q : R ⟶ 𝟭` and `θ : R ⋙ F ≅ R ⋙ G`, the composites
`F.map (p.app X) ≫ θ.hom.app X ≫ G.map (q.app X)` are natural in `X`. -/
private theorem naturality_map_app_hom_app_map_app {R : C ⥤ C} (p : 𝟭 C ⟶ R) (q : R ⟶ 𝟭 C)
    (θ : R ⋙ F ≅ R ⋙ G) {X Y : C} (f : X ⟶ Y) :
    F.map f ≫ F.map (p.app Y) ≫ θ.hom.app Y ≫ G.map (q.app Y) =
      (F.map (p.app X) ≫ θ.hom.app X ≫ G.map (q.app X)) ≫ G.map f := by
  have h₁ : f ≫ p.app Y = p.app X ≫ R.map f := p.naturality f
  have h₂ : R.map f ≫ q.app Y = q.app X ≫ f := q.naturality f
  have h₃ : F.map (R.map f) ≫ θ.hom.app Y = θ.hom.app X ≫ G.map (R.map f) :=
    θ.hom.naturality f
  calc F.map f ≫ F.map (p.app Y) ≫ θ.hom.app Y ≫ G.map (q.app Y)
      = F.map (p.app X) ≫ (F.map (R.map f) ≫ θ.hom.app Y) ≫ G.map (q.app Y) := by
        rw [← F.map_comp_assoc, h₁, F.map_comp]
        simp only [Category.assoc]
    _ = F.map (p.app X) ≫ θ.hom.app X ≫ G.map (R.map f ≫ q.app Y) := by
        rw [h₃, G.map_comp]
        simp only [Category.assoc]
    _ = (F.map (p.app X) ≫ θ.hom.app X ≫ G.map (q.app X)) ≫ G.map f := by
        rw [h₂, G.map_comp]
        simp only [Category.assoc]

/-- The sum of the "forward" composites through `θ` is a left inverse of the sum of the "backward"
ones; applied to `θ.symm` and with `F`, `G` swapped, it also gives the other inverse law. -/
private theorem sum_comp_sum_eq_id {J : Type*} [Fintype J] (R : J → C ⥤ C)
    (p : ∀ i, 𝟭 C ⟶ R i) (q : ∀ i, R i ⟶ 𝟭 C) (hsum : ∀ X : C, ∑ i, (p i).app X ≫ (q i).app X = 𝟙 X)
    (hqp : ∀ i (X : C), (q i).app X ≫ (p i).app X = 𝟙 _)
    (hqp' : ∀ i k, i ≠ k → ∀ X : C, (q i).app X ≫ (p k).app X = 0)
    (θ : ∀ i, R i ⋙ F ≅ R i ⋙ G) (X : C) :
    (∑ i, F.map ((p i).app X) ≫ (θ i).hom.app X ≫ G.map ((q i).app X)) ≫
      ∑ i, G.map ((p i).app X) ≫ (θ i).inv.app X ≫ F.map ((q i).app X) = 𝟙 _ := by
  classical
  have key : ∀ i k : J,
      (F.map ((p i).app X) ≫ (θ i).hom.app X ≫ G.map ((q i).app X)) ≫
        (G.map ((p k).app X) ≫ (θ k).inv.app X ≫ F.map ((q k).app X)) =
        if i = k then F.map ((p i).app X ≫ (q i).app X) else 0 := by
    intro i k
    split_ifs with h
    · subst h
      simp only [Category.assoc, ← G.map_comp_assoc, hqp, G.map_id, Category.id_comp,
        Iso.hom_inv_id_app_assoc, F.map_comp]
    · simp only [Category.assoc, ← G.map_comp_assoc, hqp' i k h, G.map_zero, zero_comp,
        comp_zero]
  simp only [Preadditive.sum_comp, Preadditive.comp_sum, key,
    Finset.sum_ite_eq', Finset.mem_univ, ite_true]
  rw [← F.map_sum, hsum]
  exact F.map_id X

omit [DecidableEq I] in
/-- **Isomorphisms on the summands of a decomposition of the identity glue.** If
`𝟙 = ∑ᵢ pᵢ ≫ qᵢ` with `pᵢ : 𝟭 ⟶ Rᵢ`, `qᵢ : Rᵢ ⟶ 𝟭`, `qᵢ ≫ pᵢ = 𝟙` and `qᵢ ≫ pₖ = 0` for
`i ≠ k`, then additive functors `F` and `G` with `Rᵢ ⋙ F ≅ Rᵢ ⋙ G` for every `i` are
isomorphic. -/
theorem nonempty_iso_of_sum_eq_id (R : I → C ⥤ C) (p : ∀ i, 𝟭 C ⟶ R i)
    (q : ∀ i, R i ⟶ 𝟭 C) (hsum : ∀ X : C, ∑ i, (p i).app X ≫ (q i).app X = 𝟙 X)
    (hqp : ∀ i (X : C), (q i).app X ≫ (p i).app X = 𝟙 _)
    (hqp' : ∀ i k, i ≠ k → ∀ X : C, (q i).app X ≫ (p k).app X = 0)
    (θ : ∀ i, R i ⋙ F ≅ R i ⋙ G) : Nonempty (F ≅ G) := by
  classical
  refine ⟨NatIso.ofComponents (fun X =>
    { hom := ∑ i, F.map ((p i).app X) ≫ (θ i).hom.app X ≫ G.map ((q i).app X)
      inv := ∑ i, G.map ((p i).app X) ≫ (θ i).inv.app X ≫ F.map ((q i).app X)
      hom_inv_id := ?_
      inv_hom_id := ?_ }) ?_⟩
  · exact sum_comp_sum_eq_id R p q hsum hqp hqp' θ X
  · exact sum_comp_sum_eq_id (F := G) (G := F) R p q hsum hqp hqp' (fun i => (θ i).symm) X
  · intro X Y f
    simp only [Preadditive.comp_sum, Preadditive.sum_comp]
    exact Finset.sum_congr rfl fun i _ =>
      naturality_map_app_hom_app_map_app (p i) (q i) (θ i) f

end Gluing

/-! ### Orthogonal decompositions of an abelian category -/

open scoped ZeroObject

attribute [local instance] Abelian.hasFiniteBiproducts

-- `CategoryTheory.catToReflQuiver` is a second instance path from `Category` to `Quiver`; when it
-- is the one chosen for the `⟶` in the types of `proj` and `incl`, rewriting with them fails.
attribute [-instance] CategoryTheory.catToReflQuiver

/-- **An orthogonal decomposition of an abelian category into finitely many pieces**: every
object is a finite biproduct of objects of the pieces, and there are no nonzero morphisms
between objects of two different pieces. -/
structure OrthogonalDecomposition (A : Type u) [Category.{v} A] [Abelian A] (I : Type)
    [Fintype I] where
  /-- The pieces. -/
  piece : I → ObjectProperty A
  /-- Each piece is closed under isomorphisms. -/
  isClosedUnderIsomorphisms_piece (i : I) : (piece i).IsClosedUnderIsomorphisms
  /-- There are no nonzero morphisms between objects of two different pieces. -/
  hom_eq_zero (i j : I) (hij : i ≠ j) {X Y : A} (hX : piece i X) (hY : piece j Y)
    (f : X ⟶ Y) : f = 0
  /-- Every object is a biproduct of objects of the pieces. -/
  exists_iso_biproduct (X : A) : ∃ Y : I → A, (∀ i, piece i (Y i)) ∧ Nonempty (X ≅ ⨁ Y)

namespace OrthogonalDecomposition

variable {A : Type u} [Category.{v} A] [Abelian A] {I : Type} [Fintype I] [DecidableEq I]
  (d : OrthogonalDecomposition A I)

/-- The `i`-th summand of a chosen decomposition of `X`. -/
def summand (X : A) (i : I) : A := (d.exists_iso_biproduct X).choose i

omit [DecidableEq I] in
/-- The `i`-th summand of `X` lies in the `i`-th piece. -/
lemma summand_mem (X : A) (i : I) : d.piece i (d.summand X i) :=
  (d.exists_iso_biproduct X).choose_spec.1 i

/-- The chosen decomposition of `X` as a biproduct of objects of the pieces. -/
def isoBiproduct (X : A) : X ≅ ⨁ d.summand X := (d.exists_iso_biproduct X).choose_spec.2.some

/-- The projection of `X` onto its `i`-th summand. -/
def proj (X : A) (i : I) : X ⟶ d.summand X i := (d.isoBiproduct X).hom ≫ biproduct.π _ i

/-- The inclusion of the `i`-th summand of `X`. -/
def incl (X : A) (i : I) : d.summand X i ⟶ X := biproduct.ι _ i ≫ (d.isoBiproduct X).inv

omit [DecidableEq I] in
/-- The inclusion of the `i`-th summand followed by the projection onto it is the identity. -/
@[reassoc (attr := simp)]
lemma incl_proj (X : A) (i : I) : d.incl X i ≫ d.proj X i = 𝟙 _ := by
  simp [incl, proj]

omit [DecidableEq I] in
/-- The inclusion of the `i`-th summand followed by the projection onto the `k`-th summand is
zero for `i ≠ k`. -/
@[reassoc]
lemma incl_proj_of_ne (X : A) {i k : I} (h : i ≠ k) : d.incl X i ≫ d.proj X k = 0 := by
  simp [incl, proj, biproduct.ι_π_ne _ h]

omit [DecidableEq I] in
/-- The composites of the projections onto the summands of `X` with the inclusions sum to the
identity of `X`. -/
lemma sum_proj_incl (X : A) : ∑ i, d.proj X i ≫ d.incl X i = 𝟙 X := by
  have h : ∑ i, d.proj X i ≫ d.incl X i = (d.isoBiproduct X).hom ≫
      (∑ i, biproduct.π (d.summand X) i ≫ biproduct.ι (d.summand X) i) ≫
        (d.isoBiproduct X).inv := by
    simp only [Preadditive.comp_sum, Preadditive.sum_comp, proj, incl, Category.assoc]
  rw [h, biproduct.total, Category.id_comp, Iso.hom_inv_id]

omit [DecidableEq I] in
/-- A morphism from an object of the `i`-th piece to `X` factors through the `i`-th summand. -/
@[reassoc]
lemma comp_proj_incl {Z X : A} {i : I} (hZ : d.piece i Z) (h : Z ⟶ X) :
    h ≫ d.proj X i ≫ d.incl X i = h := by
  conv_rhs => rw [← Category.comp_id h, ← d.sum_proj_incl X, Preadditive.comp_sum]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · intro k _ hk
    rw [← Category.assoc, d.hom_eq_zero i k (Ne.symm hk) hZ (d.summand_mem X k) (h ≫ _),
      zero_comp]

omit [DecidableEq I] in
/-- A morphism from `X` to an object of the `i`-th piece factors through the `i`-th summand. -/
@[reassoc]
lemma proj_incl_comp {Z X : A} {i : I} (hZ : d.piece i Z) (h : X ⟶ Z) :
    d.proj X i ≫ d.incl X i ≫ h = h := by
  conv_rhs => rw [← Category.id_comp h, ← d.sum_proj_incl X, Preadditive.sum_comp]
  rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
  · simp only [Category.assoc]
  · intro k _ hk
    rw [Category.assoc, d.hom_eq_zero k i hk (d.summand_mem X k) hZ (_ ≫ h), comp_zero]

/-- **The summands of a decomposition are unique up to isomorphism**: in any presentation of `X`
as a biproduct of objects of the pieces, the `i`-th factor is isomorphic to the chosen `i`-th
summand. -/
def summandIsoOfIsoBiproduct {X : A} {Y : I → A} (hY : ∀ i, d.piece i (Y i)) (e : X ≅ ⨁ Y)
    (i : I) : d.summand X i ≅ Y i where
  hom := d.incl X i ≫ e.hom ≫ biproduct.π Y i
  inv := biproduct.ι Y i ≫ e.inv ≫ d.proj X i
  hom_inv_id := by
    have h : d.incl X i ≫ e.hom ≫ biproduct.π Y i ≫ biproduct.ι Y i = d.incl X i ≫ e.hom := by
      conv_rhs => rw [← Category.comp_id (d.incl X i ≫ e.hom), ← biproduct.total,
        Preadditive.comp_sum]
      rw [Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
      · simp only [Category.assoc]
      · intro k _ hk
        simp only [← Category.assoc]
        rw [d.hom_eq_zero i k (Ne.symm hk) (d.summand_mem X i) (hY k)
          ((d.incl X i ≫ e.hom) ≫ biproduct.π Y k), zero_comp]
    simp only [Category.assoc]
    rw [reassoc_of% h, Iso.hom_inv_id_assoc, incl_proj]
  inv_hom_id := by
    have h := d.comp_proj_incl (hY i) (biproduct.ι Y i ≫ e.inv)
    simp only [Category.assoc] at h ⊢
    rw [reassoc_of% h, Iso.inv_hom_id_assoc, biproduct.ι_π_self]

/-- An object `X` lies in the `i`-th piece if the composites `proj X k ≫ incl X k` vanish for
`k ≠ i`, since then `X` is a retract of its `i`-th summand. -/
private lemma mem_of_proj_incl_eq_zero_of_ne {J : Type} [Fintype J]
    (e : OrthogonalDecomposition A J) {X : A} {i : J}
    (h : ∀ k, k ≠ i → e.proj X k ≫ e.incl X k = 0) : e.piece i X := by
  have hid : e.proj X i ≫ e.incl X i = 𝟙 X := by
    rw [← e.sum_proj_incl X, Finset.sum_eq_single_of_mem i (Finset.mem_univ i)]
    · intro k _ hk
      exact h k hk
  have := e.isClosedUnderIsomorphisms_piece i
  exact (e.piece i).prop_of_iso ⟨e.incl X i, e.proj X i, by simp, hid⟩ (e.summand_mem X i)

omit [DecidableEq I] in
/-- An object which receives no nonzero morphism from the other pieces lies in the `i`-th
piece. -/
lemma mem_of_forall_hom_to_eq_zero {X : A} {i : I}
    (h : ∀ k, k ≠ i → ∀ {Z : A}, d.piece k Z → ∀ f : Z ⟶ X, f = 0) : d.piece i X :=
  d.mem_of_proj_incl_eq_zero_of_ne fun k hk => by
    rw [h k hk (d.summand_mem X k) (d.incl X k), comp_zero]

omit [DecidableEq I] in
/-- An object which sends no nonzero morphism to the other pieces lies in the `i`-th piece. -/
lemma mem_of_forall_hom_from_eq_zero {X : A} {i : I}
    (h : ∀ k, k ≠ i → ∀ {Z : A}, d.piece k Z → ∀ f : X ⟶ Z, f = 0) : d.piece i X :=
  d.mem_of_proj_incl_eq_zero_of_ne fun k hk => by
    rw [h k hk (d.summand_mem X k) (d.proj X k), zero_comp]

/-- Each piece is closed under subobjects. -/
instance isClosedUnderSubobjects_piece (i : I) : (d.piece i).IsClosedUnderSubobjects where
  prop_of_mono {X Y} f _ hY := d.mem_of_forall_hom_to_eq_zero fun k hk Z hZ g =>
    (cancel_mono f).1 (by rw [d.hom_eq_zero k i hk hZ hY (g ≫ f), zero_comp])

/-- Each piece is closed under quotients. -/
instance isClosedUnderQuotients_piece (i : I) : (d.piece i).IsClosedUnderQuotients where
  prop_of_epi {X Y} f _ hX := d.mem_of_forall_hom_from_eq_zero fun k hk Z hZ g =>
    (cancel_epi f).1 (by rw [d.hom_eq_zero i k (Ne.symm hk) hX hZ (f ≫ g), comp_zero])

/-- Each piece contains a zero object. -/
instance containsZero_piece (i : I) : (d.piece i).ContainsZero where
  exists_zero := ⟨0, isZero_zero A, d.mem_of_forall_hom_to_eq_zero fun _ _ _ _ _ =>
    (isZero_zero A).eq_of_tgt _ _⟩

/-- Each piece is closed under binary products. -/
instance isClosedUnderBinaryProducts_piece (i : I) :
    (d.piece i).IsClosedUnderBinaryProducts where
  limitsOfShape_le := by
    rintro X ⟨p⟩
    refine d.mem_of_forall_hom_to_eq_zero fun k hk Z hZ g => ?_
    refine p.isLimit.hom_ext fun j => ?_
    rw [zero_comp]
    exact d.hom_eq_zero k i hk hZ (p.prop_diag_obj j) _

/-- Each piece is closed under finite products. -/
instance isClosedUnderFiniteProducts_piece (i : I) :
    (d.piece i).IsClosedUnderFiniteProducts :=
  ObjectProperty.IsClosedUnderFiniteProducts.mk'

/-- The endofunctor of `A` sending an object to its `i`-th summand. -/
def summandFunctor (i : I) : A ⥤ A where
  obj X := d.summand X i
  map {X Y} f := d.incl X i ≫ f ≫ d.proj Y i
  map_id X := by simp
  map_comp {X Y Z} f g := by
    have h := d.comp_proj_incl (d.summand_mem X i) (d.incl X i ≫ f)
    simp only [Category.assoc] at h ⊢
    rw [reassoc_of% h]

/-- **The projection onto the `i`-th piece.** -/
abbrev projFunctor (i : I) : A ⥤ (d.piece i).FullSubcategory where
  obj X := ⟨d.summand X i, d.summand_mem X i⟩
  map {X Y} f := ObjectProperty.homMk (d.incl X i ≫ f ≫ d.proj Y i)
  map_id X := ObjectProperty.hom_ext _ ((d.summandFunctor i).map_id X)
  map_comp f g := ObjectProperty.hom_ext _ ((d.summandFunctor i).map_comp f g)

omit [DecidableEq I] in
/-- The projection onto the `i`-th piece sends `f : X ⟶ Y` to the composite of the inclusion of
the `i`-th summand of `X`, `f`, and the projection onto the `i`-th summand of `Y`. -/
lemma projFunctor_map_hom (i : I) {X Y : A} (f : X ⟶ Y) :
    ((d.projFunctor i).map f).hom = d.incl X i ≫ f ≫ d.proj Y i := rfl

/-- The `i`-th summand functor is additive. -/
instance additive_summandFunctor (i : I) : (d.summandFunctor i).Additive where
  map_add {X Y f g} := by
    change d.incl X i ≫ (f + g) ≫ d.proj Y i =
      d.incl X i ≫ f ≫ d.proj Y i + d.incl X i ≫ g ≫ d.proj Y i
    rw [Preadditive.add_comp, Preadditive.comp_add]

/-- The projection onto a piece is additive. -/
instance additive_projFunctor (i : I) : (d.projFunctor i).Additive :=
  have : (d.projFunctor i ⋙ (d.piece i).ι).Additive := d.additive_summandFunctor i
  Functor.additive_of_comp_faithful _ (d.piece i).ι

/-- The inclusion of a piece is left adjoint to the projection onto it. -/
def inclAdjunction (i : I) : (d.piece i).ι ⊣ d.projFunctor i :=
  Adjunction.mkOfHomEquiv
    { homEquiv Z X :=
        { toFun h := ObjectProperty.homMk (h ≫ d.proj X i)
          invFun g := g.hom ≫ d.incl X i
          left_inv h := (Category.assoc _ _ _).trans (d.comp_proj_incl Z.property h)
          right_inv g := ObjectProperty.hom_ext _ ((Category.assoc _ _ _).trans
            ((congrArg (fun t => g.hom ≫ t) (d.incl_proj X i)).trans (Category.comp_id _))) }
      homEquiv_naturality_left_symm {Z' Z X} f g := by
        dsimp only [Equiv.coe_fn_symm_mk]
        rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc, ObjectProperty.ι_map]
      homEquiv_naturality_right {Z X X'} f g := by
        apply ObjectProperty.hom_ext
        dsimp only [Equiv.coe_fn_mk]
        rw [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
          ObjectProperty.homMk_hom, projFunctor_map_hom, Category.assoc, Category.assoc,
          d.comp_proj_incl_assoc Z.property] }

/-- The projection onto a piece is left adjoint to the inclusion of the piece. -/
def projAdjunction (i : I) : d.projFunctor i ⊣ (d.piece i).ι :=
  Adjunction.mkOfHomEquiv
    { homEquiv X Z :=
        { toFun g := d.proj X i ≫ g.hom
          invFun h := ObjectProperty.homMk (d.incl X i ≫ h)
          left_inv g := ObjectProperty.hom_ext _ (d.incl_proj_assoc X i g.hom)
          right_inv h := d.proj_incl_comp Z.property h }
      homEquiv_naturality_left_symm {X' X Z} f g := by
        apply ObjectProperty.hom_ext
        dsimp only [Equiv.coe_fn_symm_mk]
        simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
          Category.assoc]
        rw [d.proj_incl_comp Z.property]
      homEquiv_naturality_right {X Z Z'} f g := by
        dsimp only [Equiv.coe_fn_mk]
        rw [ObjectProperty.FullSubcategory.comp_hom, Category.assoc, ObjectProperty.ι_map] }

/-- The unit of the adjunction `inclAdjunction` is an isomorphism. -/
instance isIso_inclAdjunction_unit (i : I) : IsIso (d.inclAdjunction i).unit := by
  rw [NatTrans.isIso_iff_isIso_app]
  intro Z
  refine ⟨ObjectProperty.homMk (d.incl Z.obj i), ?_, ?_⟩
  · apply ObjectProperty.hom_ext
    simp only [inclAdjunction, Adjunction.mkOfHomEquiv_unit_app, Equiv.coe_fn_mk,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ObjectProperty.FullSubcategory.id_hom, Functor.id_obj]
    simpa using d.proj_incl_comp Z.property (𝟙 _)
  · apply ObjectProperty.hom_ext
    simp only [inclAdjunction, Adjunction.mkOfHomEquiv_unit_app, Equiv.coe_fn_mk,
      ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      ObjectProperty.FullSubcategory.id_hom, Functor.comp_obj]
    simp

/-- The projection onto a piece preserves finite limits. -/
instance preservesFiniteLimits_projFunctor (i : I) : PreservesFiniteLimits (d.projFunctor i) :=
  have := (d.inclAdjunction i).rightAdjoint_preservesLimits
  inferInstance

/-- The projection onto a piece preserves finite colimits. -/
instance preservesFiniteColimits_projFunctor (i : I) :
    PreservesFiniteColimits (d.projFunctor i) :=
  have := (d.projAdjunction i).leftAdjoint_preservesColimits
  inferInstance

/-- The inclusion of a piece preserves finite limits. -/
instance preservesFiniteLimits_ι (i : I) : PreservesFiniteLimits (d.piece i).ι :=
  have := (d.projAdjunction i).rightAdjoint_preservesLimits
  inferInstance

/-- The inclusion of a piece preserves finite colimits. -/
instance preservesFiniteColimits_ι (i : I) : PreservesFiniteColimits (d.piece i).ι :=
  have := (d.inclAdjunction i).leftAdjoint_preservesColimits
  inferInstance

/-! ### The projections and inclusions, on `A` -/

/-- The projections onto the `i`-th summands, as a natural transformation. -/
def projNat (i : I) : 𝟭 A ⟶ d.projFunctor i ⋙ (d.piece i).ι where
  app X := d.proj X i
  naturality {_ X'} f := (d.proj_incl_comp (d.summand_mem X' i) (f ≫ d.proj X' i)).symm

/-- The inclusions of the `i`-th summands, as a natural transformation. -/
def inclNat (i : I) : d.projFunctor i ⋙ (d.piece i).ι ⟶ 𝟭 A where
  app X := d.incl X i
  naturality {X X'} f := by
    change (d.incl X i ≫ f ≫ d.proj X' i) ≫ d.incl X' i = d.incl X i ≫ f
    simpa only [Category.assoc] using d.comp_proj_incl (d.summand_mem X i) (d.incl X i ≫ f)

omit [DecidableEq I] in
/-- The composites `projNat i ≫ inclNat i` sum to the identity of `𝟭 A`. -/
lemma sum_projNat_inclNat : ∑ i, d.projNat i ≫ d.inclNat i = 𝟙 (𝟭 A) := by
  ext X
  rw [NatTrans.app_sum]
  exact d.sum_proj_incl X

omit [DecidableEq I] in
/-- `inclNat i ≫ projNat i` is the identity. -/
lemma inclNat_projNat (i : I) : d.inclNat i ≫ d.projNat i = 𝟙 _ := by
  ext X
  exact d.incl_proj X i

omit [DecidableEq I] in
/-- `inclNat i ≫ projNat k` is zero for `i ≠ k`. -/
lemma inclNat_projNat_of_ne {i k : I} (h : i ≠ k) : d.inclNat i ≫ d.projNat k = 0 := by
  ext X
  exact d.incl_proj_of_ne X h

/-! ### The projections and inclusions, on derived categories -/

section Derived

variable [HasDerivedCategory.{w} A]

/-- The inclusion `D^b(A_i) ⥤ D^b(A)` of the bounded derived category of a piece. -/
abbrev derivedIncl (i : I) [HasDerivedCategory.{w'} (d.piece i).FullSubcategory] :
    DerivedCategory.Bounded (d.piece i).FullSubcategory ⥤ DerivedCategory.Bounded A :=
  (d.piece i).ι.mapDerivedCategoryBounded

/-- The projection `D^b(A) ⥤ D^b(A_i)` onto the bounded derived category of a piece. -/
abbrev derivedProj (i : I) [HasDerivedCategory.{w'} (d.piece i).FullSubcategory] :
    DerivedCategory.Bounded A ⥤ DerivedCategory.Bounded (d.piece i).FullSubcategory :=
  (d.projFunctor i).mapDerivedCategoryBounded

/-- **The inclusion of the bounded derived category of a piece is fully faithful**: the
derived adjunction of `ι_i ⊣ r_i` has invertible unit, the abelian one having. -/
def fullyFaithfulDerivedIncl (i : I) [HasDerivedCategory.{w'} (d.piece i).FullSubcategory] :
    (d.derivedIncl i).FullyFaithful :=
  (d.piece i).ι.fullyFaithfulMapDerivedCategoryBounded <|
    have := StacksDraft.DerivedRingIso.isIso_mapDerivedCategoryAdjunction_unit
      (d.inclAdjunction i) inferInstance
    (StacksDraft.DerivedRingIso.mapDerivedCategoryAdjunction
      (d.inclAdjunction i)).fullyFaithfulLOfIsIsoUnit

/-- The derived projection onto the `i`-th summands. -/
def derivedProjNat (i : I) [HasDerivedCategory.{w'} (d.piece i).FullSubcategory] :
    𝟭 (DerivedCategory A) ⟶ (d.projFunctor i).mapDerivedCategory ⋙
      (d.piece i).ι.mapDerivedCategory :=
  Functor.mapDerivedCategoryIdIso.inv ≫ NatTrans.mapDerivedCategory (d.projNat i) ≫
    (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso _ _).hom

/-- The derived inclusion of the `i`-th summands. -/
def derivedInclNat (i : I) [HasDerivedCategory.{w'} (d.piece i).FullSubcategory] :
    (d.projFunctor i).mapDerivedCategory ⋙ (d.piece i).ι.mapDerivedCategory ⟶
      𝟭 (DerivedCategory A) :=
  (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso _ _).inv ≫
    NatTrans.mapDerivedCategory (d.inclNat i) ≫ Functor.mapDerivedCategoryIdIso.hom

omit [DecidableEq I] in
/-- `derivedProjNat i ≫ derivedInclNat i` is the derived form of `projNat i ≫ inclNat i`,
conjugated by `Functor.mapDerivedCategoryIdIso`. -/
lemma derivedProjNat_derivedInclNat (i : I)
    [HasDerivedCategory.{w'} (d.piece i).FullSubcategory] :
    d.derivedProjNat i ≫ d.derivedInclNat i =
      Functor.mapDerivedCategoryIdIso.inv ≫
        NatTrans.mapDerivedCategory (d.projNat i ≫ d.inclNat i) ≫
          Functor.mapDerivedCategoryIdIso.hom := by
  simp only [derivedProjNat, derivedInclNat, Category.assoc, Iso.hom_inv_id_assoc,
    NatTrans.mapDerivedCategory_comp]

omit [DecidableEq I] in
/-- `derivedInclNat i ≫ derivedProjNat k` is the derived form of `inclNat i ≫ projNat k`,
conjugated by the isomorphism `mapDerivedCategoryCompIso`. -/
lemma derivedInclNat_derivedProjNat (i k : I)
    [HasDerivedCategory.{w'} (d.piece i).FullSubcategory]
    [HasDerivedCategory.{w'} (d.piece k).FullSubcategory] :
    d.derivedInclNat i ≫ d.derivedProjNat k =
      (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso _ _).inv ≫
        NatTrans.mapDerivedCategory (d.inclNat i ≫ d.projNat k) ≫
          (Stacks.Cohomology.PerfectComplexTriangles.mapDerivedCategoryCompIso _ _).hom := by
  simp only [derivedProjNat, derivedInclNat, Category.assoc, Iso.hom_inv_id_assoc,
    NatTrans.mapDerivedCategory_comp]

omit [DecidableEq I] in
/-- The composites `derivedProjNat i ≫ derivedInclNat i` sum to the identity. -/
lemma sum_derivedProjNat_derivedInclNat
    [∀ i, HasDerivedCategory.{w'} (d.piece i).FullSubcategory] :
    ∑ i, d.derivedProjNat i ≫ d.derivedInclNat i = 𝟙 _ := by
  simp only [derivedProjNat_derivedInclNat, ← Preadditive.comp_sum, ← Preadditive.sum_comp,
    ← NatTrans.mapDerivedCategory_sum, sum_projNat_inclNat, NatTrans.mapDerivedCategory_id]
  simp

omit [DecidableEq I] in
/-- `derivedInclNat i ≫ derivedProjNat i` is the identity. -/
lemma derivedInclNat_derivedProjNat_self (i : I)
    [HasDerivedCategory.{w'} (d.piece i).FullSubcategory] :
    d.derivedInclNat i ≫ d.derivedProjNat i = 𝟙 _ := by
  rw [derivedInclNat_derivedProjNat, inclNat_projNat, NatTrans.mapDerivedCategory_id]
  simp

omit [DecidableEq I] in
/-- `derivedInclNat i ≫ derivedProjNat k` is zero for `i ≠ k`. -/
lemma derivedInclNat_derivedProjNat_of_ne {i k : I} (h : i ≠ k)
    [HasDerivedCategory.{w'} (d.piece i).FullSubcategory]
    [HasDerivedCategory.{w'} (d.piece k).FullSubcategory] :
    d.derivedInclNat i ≫ d.derivedProjNat k = 0 := by
  rw [derivedInclNat_derivedProjNat, inclNat_projNat_of_ne d h, NatTrans.mapDerivedCategory_zero]
  simp

/-- The derived projection onto the `i`-th summands, on bounded derived categories. -/
def boundedProjNat (i : I) [HasDerivedCategory.{w'} (d.piece i).FullSubcategory] :
    𝟭 (DerivedCategory.Bounded A) ⟶ d.derivedProj i ⋙ d.derivedIncl i where
  app X := ObjectProperty.homMk ((d.derivedProjNat i).app X.obj)
  naturality {_ _} f := ObjectProperty.hom_ext _ ((d.derivedProjNat i).naturality f.hom)

/-- The derived inclusion of the `i`-th summands, on bounded derived categories. -/
def boundedInclNat (i : I) [HasDerivedCategory.{w'} (d.piece i).FullSubcategory] :
    d.derivedProj i ⋙ d.derivedIncl i ⟶ 𝟭 (DerivedCategory.Bounded A) where
  app X := ObjectProperty.homMk ((d.derivedInclNat i).app X.obj)
  naturality {_ _} f := ObjectProperty.hom_ext _ ((d.derivedInclNat i).naturality f.hom)

omit [DecidableEq I] in
/-- On every object `X` of `D^b(A)`, the composites `boundedProjNat i ≫ boundedInclNat i` sum to
the identity of `X`. -/
lemma sum_boundedProjNat_boundedInclNat
    [∀ i, HasDerivedCategory.{w'} (d.piece i).FullSubcategory] (X : DerivedCategory.Bounded A) :
    ∑ i, (d.boundedProjNat i).app X ≫ (d.boundedInclNat i).app X = 𝟙 X := by
  have h := congrArg (fun τ => τ.app X.obj) d.sum_derivedProjNat_derivedInclNat
  simp only [NatTrans.app_sum, NatTrans.comp_app, NatTrans.id_app] at h
  apply DerivedCategory.Bounded.ι.map_injective
  rw [Functor.map_sum]
  exact h

omit [DecidableEq I] in
/-- `boundedInclNat i ≫ boundedProjNat i` is the identity on every object of `D^b(A)`. -/
lemma boundedInclNat_boundedProjNat_self (i : I)
    [HasDerivedCategory.{w'} (d.piece i).FullSubcategory] (X : DerivedCategory.Bounded A) :
    (d.boundedInclNat i).app X ≫ (d.boundedProjNat i).app X = 𝟙 _ :=
  ObjectProperty.hom_ext _
    (congrArg (fun τ => τ.app X.obj) (d.derivedInclNat_derivedProjNat_self i))

omit [DecidableEq I] in
/-- `boundedInclNat i ≫ boundedProjNat k` is zero on every object of `D^b(A)` for `i ≠ k`. -/
lemma boundedInclNat_boundedProjNat_of_ne {i k : I} (h : i ≠ k)
    [HasDerivedCategory.{w'} (d.piece i).FullSubcategory]
    [HasDerivedCategory.{w'} (d.piece k).FullSubcategory] (X : DerivedCategory.Bounded A) :
    (d.boundedInclNat i).app X ≫ (d.boundedProjNat k).app X = 0 := by
  apply DerivedCategory.Bounded.ι.map_injective
  rw [Functor.map_zero]
  exact congrArg (fun τ => τ.app X.obj) (d.derivedInclNat_derivedProjNat_of_ne h)

end Derived

/-! ### Sibling functors -/

section Siblings

variable [HasDerivedCategory.{w} A]
  {D : Type u'} [Category.{v'} D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
  [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D] [IsTriangulated D]
  (F F' : DerivedCategory.Bounded A ⥤ D)
  [F.CommShift ℤ] [F.IsTriangulated] [F'.CommShift ℤ] [F'.IsTriangulated]

/-- The inclusion of the bounded derived category of a piece, restricted to the piece itself, is
the inclusion of the piece followed by the inclusion of `A`. -/
def boundedSingleFunctorCompDerivedInclIso (i : I)
    [HasDerivedCategory.{w'} (d.piece i).FullSubcategory] :
    boundedSingleFunctor (d.piece i).FullSubcategory ⋙ d.derivedIncl i ≅
      (d.piece i).ι ⋙ boundedSingleFunctor A :=
  ((ObjectProperty.fullyFaithfulι _).whiskeringRight _).preimageIso
    (Functor.associator _ _ _ ≪≫
      Functor.isoWhiskerLeft _ ((d.piece i).ι.mapDerivedCategoryBoundedCompιIso) ≪≫
      (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (boundedSingleFunctorCompιIso _) _ ≪≫
      (d.piece i).ι.mapDerivedCategorySingleFunctor 0 ≪≫
      Functor.isoWhiskerLeft _ (boundedSingleFunctorCompιIso A).symm ≪≫
      (Functor.associator _ _ _).symm)

omit [DecidableEq I] in
variable {F F'} in
/-- **Siblings restrict to siblings on the bounded derived category of a piece.** -/
lemma areSiblings_derivedIncl (h : AreSiblings F F') (i : I)
    [HasDerivedCategory.{w'} (d.piece i).FullSubcategory] :
    AreSiblings (d.derivedIncl i ⋙ F) (d.derivedIncl i ⋙ F') where
  restrictionIso := by
    obtain ⟨α⟩ := h.restrictionIso
    exact ⟨(Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (d.boundedSingleFunctorCompDerivedInclIso i) F ≪≫
      Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ α ≪≫ (Functor.associator _ _ _).symm ≪≫
      Functor.isoWhiskerRight (d.boundedSingleFunctorCompDerivedInclIso i).symm F' ≪≫
      Functor.associator _ _ _⟩
  objIso _ := h.objIso _

omit [HasDerivedCategory A] [DecidableEq I] in
/-- **A piece has enough negative objects** as soon as every object `X` of it receives an
epimorphism from some object `N` of `A`, not necessarily of the piece, to which it has no nonzero
morphism: the `i`-th summand of `N` then does, since `X` sees only that summand. -/
lemma hasEnoughNegativeObjects_piece {i : I}
    (hneg : ∀ X, d.piece i X → ∃ (N : A) (p : N ⟶ X), Epi p ∧ Subsingleton (X ⟶ N)) :
    HasEnoughNegativeObjects (d.piece i).FullSubcategory := by
  intro X
  obtain ⟨N, p, hp, hs⟩ := hneg X.obj X.property
  refine ⟨⟨d.summand N i, d.summand_mem N i⟩, ObjectProperty.homMk (d.incl N i ≫ p), ?_,
    ⟨fun a b => ObjectProperty.hom_ext _ ?_⟩⟩
  · apply (d.piece i).ι.epi_of_epi_map
    show Epi (d.incl N i ≫ p)
    rw [← d.proj_incl_comp X.property p] at hp
    exact epi_of_epi (d.proj N i) _
  · have h := hs.elim (a.hom ≫ d.incl N i) (b.hom ≫ d.incl N i)
    simpa only [Category.assoc, d.incl_proj, Category.comp_id] using congrArg (· ≫ d.proj N i) h

omit [HasDerivedCategory A] [DecidableEq I] in
/-- In a piece in which every epimorphism splits, every object is projective. -/
lemma projective_piece {i : I}
    (hss : ∀ {X Y : A}, d.piece i X → d.piece i Y → ∀ p : X ⟶ Y, Epi p → IsSplitEpi p)
    (P : (d.piece i).FullSubcategory) : Projective P where
  factors {E X} f e he := by
    have : (d.piece i).ι.IsLeftAdjoint := (d.inclAdjunction i).isLeftAdjoint
    have he' : Epi e.hom := (d.piece i).ι.map_epi e
    obtain ⟨⟨s, hs⟩⟩ := (hss E.property X.property e.hom he').exists_splitEpi
    refine ⟨f ≫ ObjectProperty.homMk s, ObjectProperty.hom_ext _ ?_⟩
    simp only [ObjectProperty.FullSubcategory.comp_hom, ObjectProperty.homMk_hom,
      Category.assoc, hs, Category.comp_id]

omit [DecidableEq I] in
/-- **Sibling functors out of the bounded derived category of an orthogonal sum are isomorphic**,
when the first is fully faithful and each piece either has enough negative objects or has all
its epimorphisms split. The siblings are isomorphic on each piece, by [Stacks, Tag 0FZW] or by
`AlgebraicGeometry.nonempty_iso_of_restrictionIso_of_projective`, and these isomorphisms glue
along the decomposition of the identity of `D^b(A)` into the derived projections. -/
theorem nonempty_iso_of_areSiblings (h : AreSiblings F F') (hF : Nonempty F.FullyFaithful)
    (hpiece : ∀ i, (∀ X, d.piece i X → ∃ (N : A) (p : N ⟶ X), Epi p ∧ Subsingleton (X ⟶ N)) ∨
      (∀ {X Y : A}, d.piece i X → d.piece i Y → ∀ p : X ⟶ Y, Epi p → IsSplitEpi p)) :
    Nonempty (F ≅ F') := by
  let : ∀ i, HasDerivedCategory (d.piece i).FullSubcategory :=
    fun i => HasDerivedCategory.standard _
  have hθ : ∀ i, Nonempty (d.derivedIncl i ⋙ F ≅ d.derivedIncl i ⋙ F') := by
    intro i
    rcases hpiece i with hneg | hss
    · obtain ⟨hF⟩ := hF
      exact iso_of_areSiblings_of_fullyFaithful _ _ (d.areSiblings_derivedIncl h i)
        ⟨(d.fullyFaithfulDerivedIncl i).comp hF⟩ (d.hasEnoughNegativeObjects_piece hneg)
    · obtain ⟨α⟩ := (d.areSiblings_derivedIncl h i).restrictionIso
      exact nonempty_iso_of_restrictionIso_of_projective α (d.projective_piece hss)
  exact nonempty_iso_of_sum_eq_id (fun i => d.derivedProj i ⋙ d.derivedIncl i)
    (fun i => d.boundedProjNat i) (fun i => d.boundedInclNat i)
    d.sum_boundedProjNat_boundedInclNat (fun i => d.boundedInclNat_boundedProjNat_self i)
    (fun _ _ hik => d.boundedInclNat_boundedProjNat_of_ne hik)
    (fun i => Functor.associator _ _ _ ≪≫ Functor.isoWhiskerLeft _ (hθ i).some ≪≫
      (Functor.associator _ _ _).symm)

end Siblings

end OrthogonalDecomposition

end AlgebraicGeometry

end
