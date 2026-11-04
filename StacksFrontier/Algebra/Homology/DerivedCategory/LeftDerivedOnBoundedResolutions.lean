module

public import StacksFrontier.Algebra.Homology.DerivedCategory.UnboundedComplexes

/-!
# A bounded above complex with terms in a resolving class computes the derived functor of 0794

Let `A` be an abelian category, let `P` be a class of objects of `A` which contains a zero
object, is closed under finite direct sums, and is such that every object of `A` is a quotient
of an object satisfying `P`, and let `F : A ⥤ B` be a right exact functor satisfying the
remaining hypotheses of [Stacks, Tag 0794]. That tag produces a total left derived functor of
`K(A) ⥤ D(B)`, `K ↦ F(K)`, and this file identifies it on the complexes for which the classical
computation should hold: a complex `S` which is bounded above and all of whose terms satisfy `P`
is sent to `F(S)`, the complex obtained by applying `F` degreewise.

The mechanism is that such an `S` is `P`-cellular in the sense of
`StacksDraft.UnboundedLeftDerivedFunctor.IsPCellular`, by the constant cellular presentation
`Q n := S`: a complex bounded above by `0` is bounded above by `n` for every `n : ℕ`, and the
structural map of the constant system is the identity, hence a quasi-isomorphism in every
degree. The `P`-cellular complexes resolve every object of `K(A)` and `F` inverts the
quasi-isomorphisms between them, so the comparison of the derived functor is invertible on that
class by `CategoryTheory.LeftDerivedByResolutions.isIso_app_of_resolutions`.

This is the analogue, for the resolving class of Stacks 0794, of
`Stacks.Homology.isIso_leftDerivedCounit_app_of_isKProjective` and
`Stacks.CategoryHomology.leftDerivedObjIsoOfIsKProjective`, which make the same computation at a
K-projective complex. Neither statement implies the other: a bounded above complex with terms in
`P` need not be K-projective unless the objects of `P` are projective.

## Main definitions

* `StacksDraft.UnboundedLeftDerivedFunctor.constSequenceCocone` and
  `isColimitConstSequenceCocone`: the constant `ℕ`-indexed system on an object has that object
  as its colimit.
* `StacksDraft.UnboundedLeftDerivedFunctor.leftDerivedObjIsoOfBoundedProp`: **the total left
  derived functor of Stacks 0794 at a bounded above complex with terms satisfying `P` is `F`
  applied degreewise.**

## Main results

* `StacksDraft.UnboundedLeftDerivedFunctor.isPCellular_of_isStrictlyLE`: a complex bounded above
  by some `a ≤ 0` all of whose terms satisfy `P` is `P`-cellular.
* `StacksDraft.UnboundedLeftDerivedFunctor.cellular_quotient_of_isStrictlyLE`: the same
  statement for its image in the homotopy category.
* `StacksDraft.UnboundedLeftDerivedFunctor.isIso_app_of_isStrictlyLE_of_prop`: the comparison of
  the left derived functor of Stacks 0794 is invertible at such a complex.
* `StacksDraft.UnboundedLeftDerivedFunctor.leftDerivedObjIsoOfBoundedProp_naturality`: the
  resulting computation is natural in the complex.

## References

* [Stacks Project, Tag 0794](https://stacks.math.columbia.edu/tag/0794)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Functor

namespace StacksDraft.UnboundedLeftDerivedFunctor

section ConstantSequence

variable {C : Type*} [Category* C]

/-- **Composing with a transition map of the constant `ℕ`-indexed system changes nothing.**
This is the statement that the system `Functor.ofSequence` builds from the identities of `X` is
constant on morphisms, in the form in which its transition maps are used.

It is stated for the underlying recursive construction `Functor.OfSequence.map` rather than for
the functor, and proved by induction on `j` from `i`, because that recursion reduces only at
literal numerals: at a variable index the equation has to be proved, and this is the form of it
whose source and target are the object `X` itself. -/
lemma ofSequence_id_rawmap_comp (X : C) {Z : C} (u : X ⟶ Z) (i j : ℕ) (hij : i ≤ j) :
    Functor.OfSequence.map (X := fun _ : ℕ => X) (fun _ => 𝟙 X) i j hij ≫ u = u := by
  induction j, hij using Nat.le_induction with
  | base => rw [Functor.OfSequence.map_id, Category.id_comp]
  | succ j hij ih =>
      rw [Functor.OfSequence.map_comp (X := fun _ : ℕ => X) (fun _ => 𝟙 X) i j (j + 1) hij
        (Nat.le_succ j), Functor.OfSequence.map_le_succ, Category.comp_id]
      exact ih

/-- **Composing with a map of the constant `ℕ`-indexed system changes nothing**, stated for the
functor which `Functor.ofSequence` builds from the identities of `X`. -/
lemma ofSequence_id_map_comp (X : C) {Z : C} (u : X ⟶ Z) {i j : ℕ} (φ : i ⟶ j) :
    (Functor.ofSequence (X := fun _ : ℕ => X) (fun _ => 𝟙 X)).map φ ≫ u = u :=
  ofSequence_id_rawmap_comp X u i j (leOfHom φ)

/-- The cocone on the `ℕ`-indexed system of identities of `X` with summit `X` and all legs the
identity. -/
def constSequenceCocone (X : C) :
    Cocone (Functor.ofSequence (X := fun _ : ℕ => X) (fun _ => 𝟙 X)) where
  pt := X
  ι := NatTrans.ofSequence (fun _ => 𝟙 X)
    (fun _ => (ofSequence_id_map_comp X (𝟙 X) _).trans (Category.id_comp (𝟙 X)).symm)

/-- **An object is the colimit of the constant `ℕ`-indexed system on itself.** All legs of a
cocone on that system are equal, because composing with a map of the system changes nothing, so
such a cocone is determined by its leg at `0`, and that leg is the unique factorisation. -/
def isColimitConstSequenceCocone (X : C) : IsColimit (constSequenceCocone X) where
  desc s := s.ι.app 0
  fac s n := (Category.id_comp (s.ι.app 0)).trans
    (((ofSequence_id_map_comp X (s.ι.app n) (homOfLE (Nat.zero_le n))).symm.trans
      (s.w (homOfLE (Nat.zero_le n)))).symm)
  uniq _ m hm := (Category.id_comp m).symm.trans (hm 0)

end ConstantSequence

section Cellular

variable {A : Type*} [Category* A] [Abelian A]

/-- **A complex bounded above by some `a ≤ 0` with all terms satisfying `P` is `P`-cellular.**
The cellular presentation is the constant one, `Q n := S` with all transition maps the identity:
a complex which is strictly bounded above by `a` is strictly bounded above by `n` for every
`n : ℕ` as soon as `a ≤ 0`, the colimit of the constant system is `S` itself, and the structural
map `Q n ⟶ S` is the identity, hence a quasi-isomorphism in every degree.

The bound `a ≤ 0` is what the indexing of `IsPCellular` requires: the `n`-th stage of a cellular
presentation is asked to be bounded above by `n`, and the stages are indexed by `ℕ`, so the
constant presentation of `S` is available exactly when `S` is bounded above by `0`. For a
complex bounded above by a positive `a` the statement still holds after shifting the indexing of
the presentation, but it is not this constant one. -/
theorem isPCellular_of_isStrictlyLE (P : ObjectProperty A) (S : CochainComplex A ℤ) (a : ℤ)
    [S.IsStrictlyLE a] (ha : a ≤ 0) (hS : ∀ i, P (S.X i)) : IsPCellular P S :=
  ⟨fun _ => S, fun _ => 𝟙 S, constSequenceCocone S, isColimitConstSequenceCocone S,
    Iso.refl S, fun n => S.isStrictlyLE_of_le a (n : ℤ) (by omega), fun _ i => hS i,
    fun n i _ =>
      have hid : (constSequenceCocone S).ι.app n ≫ (Iso.refl S).hom = 𝟙 S :=
        Category.comp_id _
      have : IsIso ((constSequenceCocone S).ι.app n ≫ (Iso.refl S).hom) :=
        ⟨⟨𝟙 S, (Category.comp_id _).trans hid, (Category.id_comp _).trans hid⟩⟩
      quasiIsoAt_of_isIso _ i⟩

/-- **A complex bounded above by `0` with all terms satisfying `P` is `P`-cellular.** This is
`isPCellular_of_isStrictlyLE` at the bound the indexing of a cellular presentation allows. -/
theorem isPCellular_of_isStrictlyLE_zero (P : ObjectProperty A) (S : CochainComplex A ℤ)
    [S.IsStrictlyLE 0] (hS : ∀ i, P (S.X i)) : IsPCellular P S :=
  isPCellular_of_isStrictlyLE P S 0 le_rfl hS

/-- **The homotopy class of a complex bounded above by `0` with all terms satisfying `P` is a
`P`-cellular object of `K(A)`.** -/
theorem cellular_quotient_of_isStrictlyLE (P : ObjectProperty A) (S : CochainComplex A ℤ)
    [S.IsStrictlyLE 0] (hS : ∀ i, P (S.X i)) :
    cellular P ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj S) :=
  ⟨S, isPCellular_of_isStrictlyLE_zero P S hS, ⟨Iso.refl _⟩⟩

end Cellular

section Derived

variable {A : Type*} [Category* A] [Abelian A] {B : Type*} [Category* B] [Abelian B]
  [HasDerivedCategory A] [HasDerivedCategory B]

/-- **The comparison of the left derived functor of Stacks 0794 is invertible at a bounded above
complex with terms satisfying `P`.** Under the hypotheses of
`CategoryTheory.Functor.hasPointwiseLeftDerivedFunctor_of_acyclic_mapHomologicalComplex`, if `α`
exhibits `LF` as the left derived functor of `K ↦ F(K)` along a localization `L` of `K(A)` at
the quasi-isomorphisms, then `α` is invertible at the homotopy class of a complex which is
bounded above by `0` and all of whose terms satisfy `P`.

The `P`-cellular objects of `K(A)` resolve every object
(`hasLeftResolutions_cellularLocalizerMorphism`) and `K ↦ F(K)` inverts the quasi-isomorphisms
between them (`derives_cellularLocalizerMorphism`), so this is the instance of
`CategoryTheory.LeftDerivedByResolutions.isIso_app_of_resolutions` at that resolving class and
at the `P`-cellular object provided by `cellular_quotient_of_isStrictlyLE`. -/
theorem isIso_app_of_isStrictlyLE_of_prop
    (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
    (P : ObjectProperty A) [P.ContainsZero]
    (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
    (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
    (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
      L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
    [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
    [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
    [PreservesColimitsOfShape ℕ F]
    {D : Type*} [Category D] (L : HomotopyCategory A (ComplexShape.up ℤ) ⥤ D)
    [L.IsLocalization (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (LF : D ⥤ DerivedCategory B)
    (α : L ⋙ LF ⟶ F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
    [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (S : CochainComplex A ℤ) [S.IsStrictlyLE 0] (hS : ∀ i, P (S.X i)) :
    IsIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj S)) := by
  have hres := hasLeftResolutions_cellularLocalizerMorphism P hsum hP
  have hder := derives_cellularLocalizerMorphism F P hsum hP hFP
  refine CategoryTheory.LeftDerivedByResolutions.isIso_app_of_resolutions
    (HomotopyCategory.quasiIso A (ComplexShape.up ℤ)) (cellular P) (fun X => ?_) _
    (fun s hs hX hY => ?_) L LF α _ (cellular_quotient_of_isStrictlyLE P S hS)
  · obtain ⟨R⟩ := hres X
    exact ⟨R.X₁.obj, R.X₁.property, R.w, R.hw⟩
  · exact hder (ObjectProperty.homMk (P := cellular P) (X := ⟨_, hX⟩) (Y := ⟨_, hY⟩) s) hs

variable (F : A ⥤ B) [F.Additive] [PreservesFiniteColimits F]
  (P : ObjectProperty A) [P.ContainsZero]
  (hsum : ∀ X Y : A, P X → P Y → P (X ⊞ Y))
  (hP : ∀ X : A, ∃ (Y : A) (_ : P Y) (p : Y ⟶ X), Epi p)
  (hFP : ∀ (a : ℤ) (L : CochainComplex A ℤ), L.IsStrictlyLE a → (∀ n, P (L.X n)) →
    L.Acyclic → ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj L).Acyclic)
  [HasColimitsOfShape ℕ A] [HasColimitsOfShape ℕ B]
  [HasExactColimitsOfShape ℕ A] [HasExactColimitsOfShape ℕ B]
  [PreservesColimitsOfShape ℕ F]
  (LF : DerivedCategory A ⥤ DerivedCategory B)
  (α : DerivedCategory.Qh ⋙ LF ⟶
    F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh)
  [LF.IsLeftDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]

/-- **The total left derived functor of Stacks 0794 at a bounded above complex with terms
satisfying `P` is the underived functor applied degreewise.** The comparison is invertible there
by `isIso_app_of_isStrictlyLE_of_prop`, and the remaining identifications are the canonical
comparisons of the homotopy category with the derived category.

This is the classical computation of a left derived functor by a resolution: for `F` right exact
and `P` the projective objects it says that the derived functor of a bounded above complex of
projectives is the complex obtained by applying `F` degreewise. The point of stating it for a
general resolving class `P` is that `F` is only assumed to turn bounded above acyclic complexes
with terms in `P` into acyclic complexes, which is weaker than exactness of `F` on `P` and is
the hypothesis of Stacks 0794. -/
def leftDerivedObjIsoOfBoundedProp (S : CochainComplex A ℤ) [S.IsStrictlyLE 0]
    (hS : ∀ i, P (S.X i)) :
    LF.obj (DerivedCategory.Q.obj S) ≅
      DerivedCategory.Q.obj ((F.mapHomologicalComplex (ComplexShape.up ℤ)).obj S) :=
  have := isIso_app_of_isStrictlyLE_of_prop F P hsum hP hFP DerivedCategory.Qh LF α S hS
  LF.mapIso ((DerivedCategory.quotientCompQhIso A).app S).symm ≪≫
    asIso (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj S)) ≪≫
    DerivedCategory.Qh.mapIso ((F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).app S) ≪≫
    (DerivedCategory.quotientCompQhIso B).app ((F.mapHomologicalComplex _).obj S)

/-- **The computation of the left derived functor of Stacks 0794 at a bounded above complex with
terms satisfying `P` is natural in the complex.** For a morphism `f : S ⟶ S'` of such complexes
the square relating `LF(f)` with `F(f)` applied degreewise commutes: each of the four
identifications composing `leftDerivedObjIsoOfBoundedProp` is a component of a natural
transformation — the comparison of the homotopy category with the derived category, the
comparison `α` exhibiting `LF` as a left derived functor, and the factorisation of
`F.mapHomotopyCategory` through the quotient — so the square is the composite of their four
naturality squares. -/
lemma leftDerivedObjIsoOfBoundedProp_naturality {S S' : CochainComplex A ℤ}
    [S.IsStrictlyLE 0] [S'.IsStrictlyLE 0] (hS : ∀ i, P (S.X i)) (hS' : ∀ i, P (S'.X i))
    (f : S ⟶ S') :
    LF.map (DerivedCategory.Q.map f) ≫
        (leftDerivedObjIsoOfBoundedProp F P hsum hP hFP LF α S' hS').hom =
      (leftDerivedObjIsoOfBoundedProp F P hsum hP hFP LF α S hS).hom ≫
        DerivedCategory.Q.map ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f) := by
  have h1 := (DerivedCategory.quotientCompQhIso A).inv.naturality f
  have h2 := α.naturality ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).map f)
  have h3 := (F.mapHomotopyCategoryFactors (ComplexShape.up ℤ)).hom.naturality f
  have h4 := (DerivedCategory.quotientCompQhIso B).hom.naturality
    ((F.mapHomologicalComplex (ComplexShape.up ℤ)).map f)
  simp only [Functor.comp_map, Functor.comp_obj] at h1 h2 h3 h4
  dsimp only [leftDerivedObjIsoOfBoundedProp, Iso.trans_hom, Iso.symm_hom,
    Functor.mapIso_inv, Functor.mapIso_hom, asIso_hom]
  simp only [Iso.app_inv, Iso.app_hom]
  slice_lhs 1 2 => rw [← LF.map_comp, h1, LF.map_comp]
  simp only [Category.assoc]
  slice_lhs 2 3 => rw [h2]
  slice_lhs 3 4 => rw [← DerivedCategory.Qh.map_comp, h3, DerivedCategory.Qh.map_comp]
  slice_lhs 4 5 => rw [h4]

end Derived

end StacksDraft.UnboundedLeftDerivedFunctor

end
