module

public import Mathlib.Algebra.Homology.HomotopyCategory.HomComplexCohomology
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.CategoryTheory.DifferentialGraded.CochainComplexDGCategory

/-!
# Comparing the differential graded category of complexes with the ordinary ones

For a preadditive category `B`, the category of complexes and the homotopy category of the
differential graded category `CochainComplex.dgCategory B` are the ordinary category of cochain
complexes in `B` and the ordinary homotopy category `K(B)`. This file proves the two
comparisons, both as equivalences specified on objects and on morphisms, together with the
characterization of the coboundaries of the Hom complex as the closed homogeneous morphisms
whose associated maps into shifts are null-homotopic.

## Main results

* `CochainComplex.homotopicToZero_iff_eq_d`: a closed homogeneous morphism is a coboundary
  exactly when the corresponding morphism to the shifted target is homotopic to zero.
* `CochainComplex.complexesCategoryEquivalence`: the category of complexes of
  `CochainComplex.dgCategory B` is the ordinary category of cochain complexes in `B`.
* `CochainComplex.homotopyCategoryHomologyAddEquiv` and
  `CochainComplex.homotopyCategoryHomologyAddEquiv_map`: morphisms of the usual homotopy
  category are the degree-zero cohomology of the differential graded Hom.
* `CochainComplex.homotopyCategoryEquivalence`,
  `CochainComplex.homotopyCategoryEquivalence_obj` and
  `CochainComplex.homotopyCategoryEquivalence_map`: the homotopy category of
  `CochainComplex.dgCategory B` is the usual homotopy category of complexes.

## Implementation notes

Morphisms in the category of complexes of `CochainComplex.dgCategory B` are closed degree-zero
cochains, whereas morphisms of cochain complexes are chain maps. Both comparisons are stated as
equivalences bundled with their action: the identity on objects, and on morphisms the passage
between a closed degree-zero cochain and the corresponding chain map, component by component.

In `homotopicToZero_iff_eq_d` the degree `m` of a primitive is named together with the equality
`m + 1 = n`.

## References

* [Stacks Project, Tag 09L9](https://stacks.math.columbia.edu/tag/09L9)
-/

@[expose] public section

open CategoryTheory
open CochainComplex.HomComplex

universe v u

namespace CochainComplex

variable {B : Type u} [Category.{v} B] [Preadditive B]

/-- A closed homogeneous morphism is a boundary if and only if the associated morphism to the
shifted target is homotopic to zero. -/
@[stacks 09L9 "boundaries_homotopies"]
public theorem homotopicToZero_iff_eq_d {A C : CochainComplex B ℤ} {n : ℤ}
    (f : Cocycle A C n) :
    Nonempty (Homotopy (Cocycle.equivHomShift.symm f) 0) ↔
      ∃ (m : ℤ) (hm : m + 1 = n) (g : (dgCategory B).Hom A C m),
        hm ▸ (dgCategory B).d g = f.1 := by
  rw [← HomotopyCategory.quotient_map_eq_zero_iff, ← CohomologyClass.toHom_mk f,
    CohomologyClass.toHom_mk_eq_zero_iff]
  simp only [coboundaries, AddSubgroup.mem_mk, AddSubmonoid.mem_mk,
    AddSubsemigroup.mem_mk, Set.mem_ofPred_eq]
  constructor <;> rintro ⟨m, hm, g, hg⟩ <;> exact ⟨m, hm, g, by cases hm; exact hg⟩


section Comparison

variable (B)

/-- The functor from the category of complexes of `CochainComplex.dgCategory B` to the ordinary
category of cochain complexes: the identity on objects, and on morphisms the chain map
underlying a closed degree-zero cochain. -/
public def complexesToCochainFunctor :
    (dgCategory B).Comp ⥤ CochainComplex B ℤ where
  obj X := X
  map f := Cocycle.homOf f
  map_id X := by
    let X' : CochainComplex B ℤ := cast (dgCategory_obj B) X
    change Cocycle.homOf (Cocycle.ofHom (𝟙 X')) = 𝟙 X'
    exact Cocycle.homOf_ofHom_eq_self _
  map_comp f g := by
    ext i
    change (DGCategory.compCocycle (dgCategory B) g f).1.v i i
        (add_zero i) = f.1.v i i (add_zero i) ≫ g.1.v i i (add_zero i)
    unfold DGCategory.compCocycle
    change ((dgCategory B).comp (show (0 : ℤ) + 0 = 0 by lia)
      g.1 f.1).v i i (add_zero i) = _
    rw [dgCategory_comp_v (B := B) (h := by lia)
      (g := g.1) (f := f.1) i i i (add_zero i) (add_zero i)]

/-- The functor from the ordinary category of cochain complexes to the category of complexes of
`CochainComplex.dgCategory B`: the identity on objects, and on morphisms the closed degree-zero
cochain underlying a chain map. -/
public def cochainToComplexFunctor :
    CochainComplex B ℤ ⥤ (dgCategory B).Comp where
  obj X := X
  map f := Cocycle.ofHom f
  map_id X := by
    apply Subtype.ext; ext i
    change (Cochain.ofHom (𝟙 X)).v i i (add_zero i) =
      ((dgCategory B).id X).v i i (add_zero i)
    simp [Cochain.ofHom_v, dgCategory_id_v]
  map_comp f g := Subtype.ext (Cochain.ofHom_comp f g)

/-- The canonical equivalence from the category of complexes of `CochainComplex.dgCategory B`
to the ordinary category of cochain complexes in `B`. It fixes objects and acts on morphisms by
taking the component of a cochain in each degree. -/
@[stacks 09L9 "complexes_category"]
public noncomputable def complexesCategoryEquivalence :
    { E : (dgCategory B).Comp ≌ CochainComplex B ℤ //
      (∀ X : (dgCategory B).Comp, E.functor.obj X = X) ∧
      (∀ (X Y : (dgCategory B).Comp) (f : X ⟶ Y) (i : ℤ),
        HEq ((E.functor.map f).f i) (f.1.v i i (add_zero i))) } := by
  letI : (complexesToCochainFunctor B).Full :=
    ⟨fun {_ _} f => ⟨Cocycle.ofHom f, Cocycle.homOf_ofHom_eq_self f⟩⟩
  letI : (complexesToCochainFunctor B).Faithful :=
    ⟨fun {_ _ f g} h => by
      rw [← Cocycle.ofHom_homOf_eq_self f, ← Cocycle.ofHom_homOf_eq_self g]
      exact congrArg Cocycle.ofHom h⟩
  letI : (complexesToCochainFunctor B).EssSurj := ⟨fun X => ⟨X, ⟨Iso.refl X⟩⟩⟩
  letI : (complexesToCochainFunctor B).IsEquivalence :=
    ⟨inferInstance, inferInstance, inferInstance⟩
  exact ⟨(complexesToCochainFunctor B).asEquivalence,
    ⟨fun _ => rfl, fun _ _ _ _ => HEq.rfl⟩⟩

/-- The canonical identification of homotopy classes of maps of complexes with
degree-zero cohomology of the differential graded Hom. -/
@[stacks 09L9 "homotopy_category", sga "2 V 1.1" "more general", sga "4½ Etat_0 1.3.3" "H⁰(Hom•(A"]
public noncomputable def homotopyCategoryHomologyAddEquiv
    (A C : CochainComplex B ℤ) :
    (((HomotopyCategory.quotient B (.up ℤ)).obj A) ⟶
      ((HomotopyCategory.quotient B (.up ℤ)).obj C)) ≃+
      (CochainComplex.HomComplex A C).homology 0 :=
  ((CategoryTheory.Linear.homCongr ℤ
    (Iso.refl ((HomotopyCategory.quotient B (.up ℤ)).obj A))
    (((HomotopyCategory.quotient B (.up ℤ)).mapIso
      ((CategoryTheory.shiftFunctorZero (CochainComplex B ℤ) ℤ).app C)).symm)).toAddEquiv).trans
    ((CohomologyClass.homAddEquiv (K := A) (L := C) (n := 0)).symm.trans
      (homologyAddEquiv A C 0).symm)

/-- The canonical comparison carries a chain map to the cohomology class of its
degree-zero cochain. -/
@[stacks 09L9 "homotopy_category"]
public theorem homotopyCategoryHomologyAddEquiv_map
    {A C : CochainComplex B ℤ} (f : A ⟶ C) :
    homotopyCategoryHomologyAddEquiv B A C
        ((HomotopyCategory.quotient B (.up ℤ)).map f) =
      (homologyAddEquiv A C 0).symm (CohomologyClass.mk (Cocycle.ofHom f)) := by
  dsimp [homotopyCategoryHomologyAddEquiv]
  simp only [AddEquiv.symm_apply_eq, AddEquiv.apply_symm_apply]
  rw [CohomologyClass.homAddEquiv_apply, CohomologyClass.toHom_mk,
    Cocycle.equivHomShift_symm_apply, CategoryTheory.Linear.homCongr_apply]
  simp only [Iso.refl_inv, Category.id_comp, Iso.symm_hom, Functor.mapIso_inv]
  rw [← (HomotopyCategory.quotient B (.up ℤ)).map_comp]
  apply congrArg (HomotopyCategory.quotient B (.up ℤ)).map
  ext p
  simp [Cochain.rightShift_v, CochainComplex.shiftFunctorZero_inv_app_f,
    HomologicalComplex.XIsoOfEq]

/-- The comparison functor from the usual homotopy category to the homotopy category of
`CochainComplex.dgCategory B`: the descent of
`CochainComplex.cochainToComplexFunctor B ⋙ DGCategory.compToK (dgCategory B)` along the homotopy
quotient. -/
public noncomputable def homotopyCategoryComparisonFunctor :
    HomotopyCategory B (.up ℤ) ⥤ (dgCategory B).K :=
  CategoryTheory.Quotient.lift (homotopic B (.up ℤ))
    (cochainToComplexFunctor B ⋙ DGCategory.compToK (dgCategory B))
    (by
      rintro X Y f g ⟨h⟩
      change (Quotient.mk _ (Cocycle.ofHom f) : (dgCategory B).HomotopyClass X Y) =
        Quotient.mk _ (Cocycle.ofHom g)
      obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g h
      exact Quotient.sound ⟨z, sub_eq_iff_eq_add.2 hz⟩)

/-- The homotopy category of the differential graded category of complexes is
equivalent to the usual homotopy category of complexes. -/
@[stacks 09L9 "homotopy_category"]
public noncomputable def homotopyCategoryEquivalence :
    HomotopyCategory B (.up ℤ) ≌ (dgCategory B).K := by
  let F₀ : CochainComplex B ℤ ⥤ (dgCategory B).K := {
    obj := id
    map f := Quotient.mk _ (Cocycle.ofHom f)
    map_id _ := rfl
    map_comp := by
      intro X Y Z f g
      change Quotient.mk _ (Cocycle.ofHom (f ≫ g)) =
        Quotient.mk _ ((dgCategory B).compCocycle
          (Cocycle.ofHom g) (Cocycle.ofHom f))
      exact congrArg (Quotient.mk _) <| Subtype.ext <| by
        simp [DGCategory.compCocycle, CochainComplex.dgCategory]
  }
  let F := CategoryTheory.Quotient.lift (homotopic B (.up ℤ)) F₀
    (by
      rintro X Y f g ⟨h⟩
      change Quotient.mk _ (Cocycle.ofHom f) = Quotient.mk _ (Cocycle.ofHom g)
      obtain ⟨z, hz⟩ := Cochain.equivHomotopy f g h
      exact Quotient.sound ⟨z, sub_eq_iff_eq_add.2 hz⟩)
  letI : F.Full := by
    refine ⟨?_⟩
    intro X Y f
    obtain ⟨c, rfl⟩ := Quotient.exists_rep f
    refine ⟨(HomotopyCategory.quotient B (.up ℤ)).map (Cocycle.homOf c), ?_⟩
    change Quotient.mk _ (Cocycle.ofHom (Cocycle.homOf c)) = Quotient.mk _ c
    exact congrArg (Quotient.mk _) (Cocycle.ofHom_homOf_eq_self c)
  letI : F.Faithful := by
    refine ⟨?_⟩
    intro X Y f g h
    have hm : F.map ((HomotopyCategory.quotient B (.up ℤ)).map f.out) =
        F.map ((HomotopyCategory.quotient B (.up ℤ)).map g.out) := by
      rwa [HomotopyCategory.quotient_map_out f, HomotopyCategory.quotient_map_out g]
    let s := (dgCategory B).homotopySetoid X.as Y.as
    have hclass : Quotient.mk s (Cocycle.ofHom f.out) =
        Quotient.mk s (Cocycle.ofHom g.out) := by
      dsimp [F, F₀, CategoryTheory.Quotient.lift, HomotopyCategory.quotient,
        CategoryTheory.Quotient.functor] at hm ⊢
      exact hm
    rcases Quotient.exact hclass with ⟨z, hz⟩
    have hz' : Cochain.ofHom f.out = δ (-1) 0 z + Cochain.ofHom g.out := by
      ext p
      have hv := congrArg (fun w : Cochain X.as Y.as 0 => w.v p p (add_zero p)) hz
      have hv' := (sub_eq_iff_eq_add.mp hv)
      simp only [dgCategory, Int.reduceAdd, Cocycle.ofHom_coe, DGCategory.d',
        Int.reduceNeg] at hv'
      change (Cochain.ofHom f.out).v p p (add_zero p) =
        (δ (-1) 0 z).v p p (add_zero p) +
          (Cochain.ofHom g.out).v p p (add_zero p) at hv'
      rw [Cochain.ofHom_v f.out p, Cochain.ofHom_v g.out p] at hv'
      simpa only [Cochain.add_v, Cochain.ofHom_v] using hv'
    have hq := HomotopyCategory.eq_of_homotopy f.out g.out
      ((Cochain.equivHomotopy f.out g.out).symm ⟨z, hz'⟩)
    rwa [HomotopyCategory.quotient_map_out f, HomotopyCategory.quotient_map_out g] at hq
  letI : F.EssSurj := ⟨fun X => ⟨{ as := X }, ⟨Iso.refl X⟩⟩⟩
  letI : F.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact F.asEquivalence

/-- The functor of the comparison equivalence is
`CochainComplex.homotopyCategoryComparisonFunctor`. -/
public theorem homotopyCategoryEquivalence_functor :
    (homotopyCategoryEquivalence B).functor = homotopyCategoryComparisonFunctor B := rfl

/-- The comparison equivalence is the identity on complexes. -/
@[stacks 09L9 "homotopy_category"]
public theorem homotopyCategoryEquivalence_obj (A : CochainComplex B ℤ) :
    (homotopyCategoryEquivalence B).functor.obj
      ((HomotopyCategory.quotient B (.up ℤ)).obj A) = A := by
  show ((HomotopyCategory.quotient B (.up ℤ)).obj A).as = A
  exact HomotopyCategory.quotient_obj_as A

/-- On morphisms, the comparison sends the homotopy class of a chain map to
the corresponding degree-zero cocycle modulo boundaries. -/
@[stacks 09L9 "homotopy_category"]
public theorem homotopyCategoryEquivalence_map {A C : CochainComplex B ℤ}
    (f : A ⟶ C) :
    HEq ((homotopyCategoryEquivalence B).functor.map
      ((HomotopyCategory.quotient B (.up ℤ)).map f))
      (Quotient.mk _
        (show (dgCategory B).Cocycle A C from
          ⟨Cochain.ofHom f, by
            change δ 0 1 (Cochain.ofHom f) = 0
            simp⟩) :
        (dgCategory B).HomotopyClass A C) := by
  dsimp [homotopyCategoryEquivalence, CategoryTheory.Functor.asEquivalence,
    CategoryTheory.Quotient.lift, HomotopyCategory.quotient,
    CategoryTheory.Quotient.functor]
  rfl


end Comparison

end CochainComplex
