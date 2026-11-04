module

public import StacksFrontier.CategoryTheory.ObjectProperty.CoyonedaFullSubcategory
public import StacksFrontier.CategoryTheory.Triangulated.AdmissibleSubcategories
public import StacksFrontier.CategoryTheory.Triangulated.BrownRepresentability
public import StacksFrontier.CategoryTheory.Triangulated.LocalObjects

/-!
# A compactly generated localizing subcategory is right admissible

Let `C` be a triangulated category with coproducts indexed by its morphism universe, and let
`G : ι → C` be a family of objects indexed by a type of that universe. Write
`N = (ofObj G).localizingClosure` for the localizing subcategory it generates
(`StacksFrontier/CategoryTheory/Triangulated/LocalizingClosure.lean`). This file proves that if
each `G i` is *compact* in `C`, then `N` is right admissible: the inclusion
`N.ι : N.FullSubcategory ⥤ C` has a right adjoint.

This is the hypothesis that the step-1 sentence of [Stacks, Tag 09LK] — "DG localization
supplies an exact localization functor `L` with unit `M ⟶ L M`, whose local objects form
`N^⊥`" — leaves implicit. Nothing about a triangulated category produces such a reflector: its
existence is equivalent to `N ⋆ N^⊥ = ⊤`, i.e. to left admissibility of `N^⊥`, which is one of
the equivalent conditions of [Stacks, Tag 0H0P]
(`ObjectProperty.tfae_isRightAdmissible_isLeftAdmissible_extensionProduct_and_isEquivalence_ι_comp`
in `StacksFrontier/CategoryTheory/Triangulated/AdmissibleSubcategories.lean`). What supplies it is
Brown representability, [Stacks, Tag 0A8G], proved in this repository as
`CategoryTheory.Pretriangulated.exists_isTriangulated_rightAdjoint_of_compactlyGenerated`.

The consequences drawn from [Stacks, Tag 0H0P] are collected here: `N^⊥` is left admissible,
`N` is the left orthogonal of `N^⊥`, every object of `C` is an extension of an object of `N^⊥`
by an object of `N`, and `N^⊥` is equivalent to the Verdier quotient `C/N`. The reflector
itself — the endofunctor of `C` with its unit — is built in
`StacksFrontier/CategoryTheory/Triangulated/LocalizingReflector.lean`.

## The three inputs, and where each comes from

Brown representability is applied to `F = N.ι`, so its hypotheses are hypotheses about
`N.FullSubcategory`, not about `C`.

* *Coproducts.* `N` is closed under the coproducts of shape `Discrete α`, `α : Type v`, that `C`
  has, so `N.FullSubcategory` has them and `N.ι` creates — hence preserves — them. This is why
  the universe parameter of the localizing closure is pinned to the morphism universe `v` of
  `C`: that is the universe in which [Stacks, Tag 0A8G] indexes its direct sums.
* *Generation.* The family `G`, read inside `N`, generates `N`: an object of `N` right
  orthogonal to all shifts of all `G i` lies in `N^⊥` by
  `ObjectProperty.rightOrthogonal_localizingClosure_iff`, and an object lying in both `N` and
  `N^⊥` has `𝟙 = 0`. So this input costs nothing beyond the generation criterion already
  proved in full generality in
  `StacksFrontier/CategoryTheory/Triangulated/LocalObjects.lean`.
* *Compactness.* This is the one real hypothesis, and it is imposed explicitly, in the form in
  which [Stacks, Tag 0A8G] states it: each `preadditiveCoyoneda.obj (op (G i))` preserves
  coproducts of shape `Discrete α` for every `α : Type v`. Compactness of `G i` as an object of
  `C` gives compactness as an object of `N.FullSubcategory`, by
  `ObjectProperty.preservesColimitsOfShape_discrete_preadditiveCoyoneda_op`.

## Does [Stacks, Tag 09LK] satisfy the compactness hypothesis?

In the intended application `C` is the derived category of right DG modules over a DG category
`A` and the generators are the representable modules `h_B` for `B` an acyclic object of `A`.
Those are compact: `Hom_{D(A)}(h_B, M)` is `H^0(M(B))`, and taking `H^0` of a direct sum of
complexes of abelian groups commutes with the sum. So the hypothesis is the right one and the
application will meet it — but that identification is a statement about DG modules and is *not*
proved here; see the boundary described below. What the application must supply is a family
indexed by a type in the morphism universe of `D(A)`, which the acyclic objects of a (small) DG
category are.

## Boundary

Nothing about DG categories, DG modules, the DG Yoneda embedding `h_X` or the full faithfulness
of `D(A)`-restricted Yoneda appears here or is used here. This file is about an arbitrary
triangulated category with a compactly generated localizing subcategory.

## Main results

* `CategoryTheory.ObjectProperty.isRightAdmissible_localizingClosure`.
* `CategoryTheory.ObjectProperty.isLeftAdmissible_rightOrthogonal_localizingClosure`.
* `CategoryTheory.ObjectProperty.localizingClosure_eq_leftOrthogonal_rightOrthogonal`.
* `CategoryTheory.ObjectProperty.extensionProduct_localizingClosure_rightOrthogonal_eq_top`.
* `CategoryTheory.ObjectProperty.isEquivalence_rightOrthogonal_localizingClosure_ι_comp`.
-/

@[expose] public section

universe w' w v u

namespace CategoryTheory.ObjectProperty

open Category Limits Opposite Pretriangulated

variable {C : Type u} [Category.{v} C] [HasZeroObject C] [HasShift C ℤ] [Preadditive C]
  [∀ (n : ℤ), (shiftFunctor C n).Additive] [Pretriangulated C]

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- An object which satisfies a property and is right orthogonal to it is a zero object: its
identity is a morphism from an object of the property, hence vanishes. -/
lemma isZero_of_prop_of_rightOrthogonal (P : ObjectProperty C) {X : C} (hX : P X)
    (hX' : P.rightOrthogonal X) : IsZero X :=
  (IsZero.iff_id_eq_zero X).2 (hX' (𝟙 X) hX)

omit [HasZeroObject C] [HasShift C ℤ] [∀ (n : ℤ), (shiftFunctor C n).Additive]
  [Pretriangulated C] in
/-- An object of a full subcategory is a zero object as soon as the object of the ambient
category underlying it is. -/
lemma isZero_fullSubcategory_of_isZero_obj {P : ObjectProperty C}
    {Y : P.FullSubcategory} (hY : IsZero Y.obj) : IsZero Y := by
  rw [IsZero.iff_id_eq_zero]
  exact ObjectProperty.hom_ext _ (hY.eq_of_src _ _)

variable [IsTriangulated C] [HasCoproducts.{v} C] {ι : Type v} (G : ι → C)

/-- A generator, read as an object of the localizing subcategory it helps generate. -/
def localizingClosureGen (i : ι) : (ofObj G).localizingClosure.{v}.FullSubcategory :=
  ⟨G i, le_localizingClosure _ _ (ofObj_apply G i)⟩

omit [IsTriangulated C] [HasCoproducts C] in
/-- The object of `C` underlying `localizingClosureGen G i` is `G i`. -/
@[simp]
lemma localizingClosureGen_obj (i : ι) : (localizingClosureGen G i).obj = G i := rfl

section

variable [∀ (i : ι) (α : Type v),
  PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (G i)))]

omit [IsTriangulated C] [HasCoproducts C]
  [∀ (i : ι) (α : Type v),
    PreservesColimitsOfShape (Discrete α) (preadditiveCoyoneda.obj (op (G i)))] in
/-- Inside the localizing subcategory it generates, the family `G` is a generating family: an
object `Y` of `N` receiving only zero morphisms from the shifts of the `G i` lies in `N^⊥` by
`ObjectProperty.rightOrthogonal_localizingClosure_iff`, and an object of `N ⊓ N^⊥` is zero. -/
lemma isZero_of_rightOrthogonal_shiftClosure_localizingClosureGen
    (Y : (ofObj G).localizingClosure.{v}.FullSubcategory)
    (hY : ((ofObj (localizingClosureGen G)).shiftClosure ℤ).rightOrthogonal Y) :
    IsZero Y := by
  rw [rightOrthogonal_shiftClosure_ofObj_iff] at hY
  refine isZero_fullSubcategory_of_isZero_obj
    (isZero_of_prop_of_rightOrthogonal _ Y.property ?_)
  rw [rightOrthogonal_localizingClosure_iff]
  rintro _ ⟨i⟩ n f
  have e := ((ofObj G).localizingClosure.{v}.ι.commShiftIso (A := ℤ) n).app
    (localizingClosureGen G i)
  have h0 : e.hom ≫ f = 0 := by
    have h := hY i n ((ofObj G).localizingClosure.{v}.fullyFaithfulι.preimage (e.hom ≫ f))
    rw [← (ofObj G).localizingClosure.{v}.fullyFaithfulι.map_preimage (e.hom ≫ f), h]
    exact (ofObj G).localizingClosure.{v}.ι.map_zero _ _
  refine (cancel_epi e.hom).1 ?_
  simpa using h0

/-- **A localizing subcategory generated by a set of compact objects is right admissible.**
Brown representability [Stacks, Tag 0A8G] applied to the inclusion
`N.ι : N.FullSubcategory ⥤ C`, which is exact and preserves coproducts, and whose source is
triangulated, has coproducts, and is compactly generated by the family `G` read inside `N`. -/
theorem isRightAdmissible_localizingClosure :
    (ofObj G).localizingClosure.{v}.IsRightAdmissible := by
  have hcop : HasCoproducts.{v} (ofObj G).localizingClosure.{v}.FullSubcategory :=
    fun α ↦ inferInstance
  have hpres : ∀ α : Type v,
      PreservesColimitsOfShape (Discrete α) (ofObj G).localizingClosure.{v}.ι :=
    fun α ↦ inferInstance
  have hcompact : ∀ (i : ι) (α : Type v), PreservesColimitsOfShape (Discrete α)
      (preadditiveCoyoneda.obj (op (localizingClosureGen G i))) := by
    intro i α
    have : PreservesColimitsOfShape (Discrete α)
        (preadditiveCoyoneda.obj (op (localizingClosureGen G i).obj)) :=
      inferInstanceAs (PreservesColimitsOfShape (Discrete α)
        (preadditiveCoyoneda.obj (op (G i))))
    exact preservesColimitsOfShape_discrete_preadditiveCoyoneda_op _ _ α
  obtain ⟨R, adj, _, _⟩ :=
    Pretriangulated.exists_isTriangulated_rightAdjoint_of_compactlyGenerated
      (ofObj G).localizingClosure.{v}.ι
      (localizingClosureGen G) (isZero_of_rightOrthogonal_shiftClosure_localizingClosureGen G)
  have : (ofObj G).localizingClosure.{v}.ι.IsLeftAdjoint := ⟨R, ⟨adj⟩⟩
  exact ⟨⟩

/-- The [Stacks, Tag 0H0P] package for the pair `(N, N^⊥)`, with the first of its equivalent
conditions discharged by `ObjectProperty.isRightAdmissible_localizingClosure`. -/
private lemma tfae_localizingClosure_rightOrthogonal :
    ((ofObj G).localizingClosure.{v}.rightOrthogonal.IsLeftAdmissible ∧
        (ofObj G).localizingClosure.{v} =
          (ofObj G).localizingClosure.{v}.rightOrthogonal.leftOrthogonal) ∧
      (ofObj G).localizingClosure.{v} ≤
          (ofObj G).localizingClosure.{v}.rightOrthogonal.leftOrthogonal ∧
        (ofObj G).localizingClosure.{v}.extensionProduct
          (ofObj G).localizingClosure.{v}.rightOrthogonal = ⊤ := by
  have h := (tfae_isRightAdmissible_isLeftAdmissible_extensionProduct_and_isEquivalence_ι_comp.{0,
    0, v, u} (ofObj G).localizingClosure.{v}
    (ofObj G).localizingClosure.{v}.rightOrthogonal).1
  have h1 : (ofObj G).localizingClosure.{v}.IsRightAdmissible ∧
      (ofObj G).localizingClosure.{v}.rightOrthogonal =
        (ofObj G).localizingClosure.{v}.rightOrthogonal :=
    ⟨isRightAdmissible_localizingClosure G, rfl⟩
  exact ⟨(h.out 1 2).1 h1, (h.out 1 3).1 h1⟩

/-- **The local objects form a left admissible subcategory**, so the inclusion
`N^⊥.ι` has a left adjoint: the reflector of [Stacks, Tag 09LK], step 1. -/
theorem isLeftAdmissible_rightOrthogonal_localizingClosure :
    (ofObj G).localizingClosure.{v}.rightOrthogonal.IsLeftAdmissible :=
  (tfae_localizingClosure_rightOrthogonal G).1.1

/-- The localizing subcategory is recovered as the left orthogonal of its right orthogonal. -/
theorem localizingClosure_eq_leftOrthogonal_rightOrthogonal :
    (ofObj G).localizingClosure.{v} =
      (ofObj G).localizingClosure.{v}.rightOrthogonal.leftOrthogonal :=
  (tfae_localizingClosure_rightOrthogonal G).1.2

/-- **Every object is an extension of a local object by an object of `N`**: this is the
hypothesis `N ⋆ N^⊥ = ⊤` that the existence of the reflector is equivalent to. Unfolded, it
says that every `X` fits in a distinguished triangle `X' ⟶ X ⟶ Y ⟶ X'⟦1⟧` with `X'` in `N`
and `Y` in `N^⊥`. -/
theorem extensionProduct_localizingClosure_rightOrthogonal_eq_top :
    (ofObj G).localizingClosure.{v}.extensionProduct
      (ofObj G).localizingClosure.{v}.rightOrthogonal = ⊤ :=
  (tfae_localizingClosure_rightOrthogonal G).2.2

/-- **The local objects are the Verdier quotient `C/N`.** For any localization `L` of `C` at
the class of morphisms whose cone lies in `N`, the composite `N^⊥.ι ⋙ L` is an equivalence,
and a left adjoint of `N^⊥.ι` is obtained by factoring through `L`. -/
theorem isEquivalence_rightOrthogonal_localizingClosure_ι_comp
    {Q : Type w} [Category.{w'} Q] (L : C ⥤ Q)
    [L.IsLocalization (ofObj G).localizingClosure.{v}.trW] :
    ((ofObj G).localizingClosure.{v}.rightOrthogonal.ι ⋙ L).IsEquivalence ∧
      ∃ F : Q ⥤ (ofObj G).localizingClosure.{v}.rightOrthogonal.FullSubcategory,
        Nonempty (L ⋙ F ⊣ (ofObj G).localizingClosure.{v}.rightOrthogonal.ι) :=
  ((tfae_isRightAdmissible_isLeftAdmissible_extensionProduct_and_isEquivalence_ι_comp.{w', w, v, u}
      (ofObj G).localizingClosure.{v}
      (ofObj G).localizingClosure.{v}.rightOrthogonal).2
    (tfae_localizingClosure_rightOrthogonal G).2.1
    (extensionProduct_localizingClosure_rightOrthogonal_eq_top G)).2 L

end

end CategoryTheory.ObjectProperty

end
