module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.DifferentialGraded.Module.DGCategoryComp
public import StacksFrontier.Algebra.DifferentialGraded.Module.HomotopyCategory

/-!
# The homotopy category of the differential graded category of differential graded modules

The homotopy category of a differential graded category has the same objects and, as morphisms,
the degree-zero cohomology classes of its Hom complexes: closed degree-zero morphisms modulo
boundaries. For the differential graded category of right differential graded `A`-modules a
closed degree-zero homogeneous map is a homomorphism of differential graded modules and a
boundary is a null-homotopic one, so those cohomology classes are the homotopy classes of
homomorphisms. Hence the homotopy category of differential graded modules is the homotopy
category of their differential graded category.

## Main definitions

* `DifferentialGradedModule.homotopyCategoryHomEquiv`: the bijection between homotopy classes of
  homomorphisms and degree-zero cohomology classes of the differential graded Hom module.
* `DifferentialGradedModule.homotopyCategoryEquivalence`: the resulting equivalence of the two
  homotopy categories.

## Main results

* `DifferentialGradedModule.homotopyCategoryHomEquiv_map`: the bijection sends a homomorphism to
  the class of the closed homogeneous map with the same underlying linear map.
* `DifferentialGradedModule.homotopyCategoryEquivalence_obj` and
  `DifferentialGradedModule.homotopyCategoryEquivalence_map`: the equivalence is the identity on
  objects and induces the above bijection on morphisms.

## Implementation notes

The degree-zero cohomology is `DGCategory.HomotopyClass`, the quotient of closed degree-zero
morphisms by the homotopy relation, and the usual homotopy category is the quotient of the
category of differential graded modules by homotopy. The two formulas fixing the action of the
equivalence are part of the statement, so it is a specific equivalence rather than an arbitrary
one; the morphism formula has to be stated as a heterogeneous equality because the two morphism
types are different types.

## References

* [Stacks Project, Tag 09LC](https://stacks.math.columbia.edu/tag/09LC)
-/

@[expose] public section

open CategoryTheory

universe u

namespace DifferentialGradedModule

variable {R : Type u} [CommRing R] (A : DifferentialGradedAlgebra R)

/-- A homotopy between homomorphisms of differential graded modules, read as a homogeneous map
of degree `-1`. -/
def homotopyToHomogeneousMap {L M : DifferentialGradedModule A} {f g : Hom L M}
    (H : Homotopy f g) : HomogeneousMap A L M (-1) := by
  refine ⟨H.toLinearMap.restrictScalars R, ?_, ?_⟩
  · intro i x hx
    simpa [sub_eq_add_neg] using H.map_grading i x hx
  · intro a x
    exact H.toLinearMap.map_smul (MulOpposite.op a) x

/-- Homotopic homomorphisms of differential graded modules have homotopic associated
cocycles. -/
theorem cocycleOfHom_homotopic {L M : DifferentialGradedModule A} {f g : Hom L M}
    (h : Homotopic f g) :
    (dgCategory A).Homotopic (cocycleOfHom A f) (cocycleOfHom A g) := by
  rcases h with ⟨H⟩
  refine ⟨homotopyToHomogeneousMap A H, ?_⟩
  apply Subtype.ext
  ext x
  change f.toFun x - g.toFun x = (homogeneousMapDifferential A (homotopyToHomogeneousMap A H)).1 x
  simpa [homogeneousMapDifferential_val, DifferentialGraded.gradedSign,
    homotopyToHomogeneousMap] using H.homotopy_eq x

/-- Homotopic cocycles of the differential graded category have homotopic associated
homomorphisms. -/
theorem homOfCocycle_homotopic {L M : DifferentialGradedModule A}
    {c d : (dgCategoryData A).category.Cocycle L M}
    (h : (dgCategory A).Homotopic c d) :
    Homotopic (homOfCocycle A c) (homOfCocycle A d) := by
  rcases h with ⟨k, hk⟩
  refine ⟨{
    toLinearMap :=
      { toFun := k.1
        map_add' := k.1.map_add
        map_smul' := by
          intro a x
          simpa using k.2.2 (MulOpposite.unop a) x }
    map_grading := ?_
    homotopy_eq := ?_ }⟩
  · intro i x hx
    simpa [sub_eq_add_neg] using k.2.1 i x hx
  · intro x
    have heq := LinearMap.congr_fun (congrArg Subtype.val hk) x
    change c.1.1 x - d.1.1 x =
      ((dgCategory A).d' (show (-1 : ℤ) + 1 = 0 by omega) k).1 x at heq
    simp only [DGCategory.d', dgCategory_d_val, DifferentialGraded.gradedSign,
      LinearMap.sub_apply, LinearMap.comp_apply] at heq
    simpa [homOfCocycle, sub_eq_add_neg, add_comm, add_left_comm, add_assoc] using heq

/-- Homotopy classes of homomorphisms of differential graded modules are canonically the
degree-zero cohomology classes of their differential graded Hom module. -/
@[stacks 09LC "homotopy_category"]
noncomputable def homotopyCategoryHomEquiv (L M : DifferentialGradedModule A) :
    ((((toHomotopyCategory A).obj L) ⟶ ((toHomotopyCategory A).obj M)) ≃
      (dgCategory A).HomotopyClass L M) where
  toFun := Quot.lift (fun f : L ⟶ M => Quotient.mk _ (cocycleOfHom A f)) fun f g h =>
    Quotient.sound <| cocycleOfHom_homotopic A <|
      (HomRel.compClosure_iff_self (homotopyRel A) f g).mp h
  invFun := Quotient.lift
    (fun c : (dgCategoryData A).category.Cocycle L M =>
      (toHomotopyCategory A).map (homOfCocycle A c))
    fun _ _ h => CategoryTheory.Quotient.sound _ (homOfCocycle_homotopic A h)
  left_inv f := Quot.inductionOn f fun _ => congrArg (Quot.mk _) (Hom.ext rfl)
  right_inv c := Quotient.inductionOn c fun _ =>
    congrArg (Quotient.mk _) (Subtype.ext (Subtype.ext rfl))

/-- The canonical bijection sends a homomorphism to the cohomology class of the closed
homogeneous map with the same underlying linear map. -/
@[stacks 09LC "homotopy_category"]
theorem homotopyCategoryHomEquiv_map (L M : DifferentialGradedModule A) (f : Hom L M) :
    ∃ c : (dgCategory A).Cocycle L M, c.1.1 = f.toFun ∧
      homotopyCategoryHomEquiv A L M ((toHomotopyCategory A).map f) = Quotient.mk _ c :=
  ⟨cocycleOfHom A f, rfl, rfl⟩

/-- The homotopy category of the differential graded category of differential graded modules is
canonically equivalent to the homotopy category of differential graded modules. -/
@[stacks 09LC "homotopy_category"]
noncomputable def homotopyCategoryEquivalence :
    HomotopyCategory A ≌ (dgCategory A).K :=
  let G : DifferentialGradedModule A ⥤ (dgCategory A).K :=
    { obj := id
      map := fun f => Quotient.mk _ (cocycleOfHom A f)
      map_id _ := congrArg (Quotient.mk _) (Subtype.ext (Subtype.ext rfl))
      map_comp _ _ :=
        congrArg (Quotient.mk _) (Subtype.ext (Subtype.ext (LinearMap.ext fun _ => rfl))) }
  let F : HomotopyCategory A ⥤ (dgCategory A).K :=
    CategoryTheory.Quotient.lift (homotopyRel A) G fun _ _ _ _ h =>
      Quotient.sound (cocycleOfHom_homotopic A h)
  have hMap : ∀ {X Y : HomotopyCategory A} (f : X ⟶ Y),
      F.map f = homotopyCategoryHomEquiv A X.as Y.as f := by
    intro X Y f; induction f using Quot.inductionOn; rfl
  let _ : F.Full := ⟨fun {X Y} f =>
    ⟨(homotopyCategoryHomEquiv A X.as Y.as).symm f, by rw [hMap, Equiv.apply_symm_apply]⟩⟩
  let _ : F.Faithful := ⟨fun {X Y} _ _ h =>
    (homotopyCategoryHomEquiv A X.as Y.as).injective (by rwa [← hMap, ← hMap])⟩
  let _ : F.EssSurj := ⟨fun X => ⟨(toHomotopyCategory A).obj X, ⟨Iso.refl X⟩⟩⟩
  let _ : F.IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  F.asEquivalence

/-- The canonical equivalence of homotopy categories is the identity on differential graded
modules. -/
@[stacks 09LC "homotopy_category"]
theorem homotopyCategoryEquivalence_obj (L : DifferentialGradedModule A) :
    (homotopyCategoryEquivalence A).functor.obj ((toHomotopyCategory A).obj L) = L :=
  rfl

/-- The functor of the canonical equivalence acts on every morphism by the canonical
identification with degree-zero Hom cohomology. -/
@[stacks 09LC "homotopy_category"]
theorem homotopyCategoryEquivalence_map (L M : DifferentialGradedModule A)
    (f : ((toHomotopyCategory A).obj L) ⟶ ((toHomotopyCategory A).obj M)) :
    HEq ((homotopyCategoryEquivalence A).functor.map f) (homotopyCategoryHomEquiv A L M f) := by
  dsimp [homotopyCategoryEquivalence, CategoryTheory.Functor.asEquivalence]
  exact Quot.inductionOn f fun _ => HEq.rfl

end DifferentialGradedModule
