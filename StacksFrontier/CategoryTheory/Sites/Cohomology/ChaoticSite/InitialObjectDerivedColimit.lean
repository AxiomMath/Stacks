module

public import StacksFrontier.CategoryTheory.Sites.Cohomology.ChaoticSite.CosimplicialResolution
import StacksCore.Tactic.StacksAttribute

/-!
# `Lπ_!` on a chaotic site with an initial object is underived

Let `C` be a small category with an initial object `I`, carrying the chaotic topology. The
lower shriek `π_!` of Tag 08PF is the colimit over `Cᵒᵖ`, and `Cᵒᵖ` has a terminal object, so
`π_!` is evaluation at `I` and is therefore exact: its left derived functors vanish in positive
degrees and are the colimit itself in degree zero.

The proof given here is the criterion of Tag 08Q9 applied to the *constant* cosimplicial object
with value `I`. That cosimplicial object is a point resolution — `Mor_C(I, W)` is a singleton,
so `Mor_C(U_•, W)` is isomorphic, not merely homotopy equivalent, to the constant simplicial set
on a singleton — and the Moore complex of `ℱ(U_•)` is the alternating constant complex on `ℱ(I)`,
whose homology is `ℱ(I)` in degree zero and zero elsewhere.

## Main results

* `Stacks.ChaoticSite.isPointResolution_const_of_isInitial`: the constant cosimplicial object at
  an initial object is a point resolution in the sense of Tag 08Q9.
* `Stacks.ChaoticSite.cosimplicialMooreComplexConstIso`: the Moore complex of the evaluation of
  a presheaf on a constant cosimplicial object is the alternating constant complex on the
  sections at its value.
* `Stacks.ChaoticSite.quasiIso_mooreCochainAugmentationConst`: the augmentation
  `ℱ(U_•) ⟶ (π_!ℱ)[0]` of the extended Moore complex is a quasi-isomorphism for the constant
  cosimplicial object at an initial object, with no hypothesis on the coefficient presheaf.
* `Stacks.ChaoticSite.leftDerivedColimitZeroIsoColimit`: `L_0π_! = π_!`, with no hypothesis on
  `C`, the colimit functor being right exact.
* `Stacks.ChaoticSite.isZero_leftDerivedColimit_succ_of_isInitial`: `L_nπ_! = 0` for `n > 0` when
  `C` has an initial object.

## Implementation notes

Degree zero needs no initial object: `CategoryTheory.Functor.leftDerivedZeroIsoSelf` applies to
any right exact additive functor, and `colim` preserves all colimits. The initial object is what
makes the positive degrees vanish.

**Smallness.** Everything up to and including the quasi-isomorphism of the augmentation is proved
for a category whose objects and morphisms live in unrelated universes: the point-resolution
condition speaks only of the simplicial sets of morphisms, and the Moore complex and its
augmentation are formed presheafwise. Only the two degreewise statements at the end are stated
for a small `C`, because they route through `Stacks.ChaoticSite.leftDerivedColimitNatIso`, the
degreewise form of the criterion of Tag 08Q9, which asks for a small site. For a site that is not
small the derived-category form is
`Stacks.ChaoticSite.AbelianValued.totalDerivedColimitSingleIsoOfIsInitial`.

## References

* [Stacks Project, Tag 08Q9](https://stacks.math.columbia.edu/tag/08Q9)
* [Stacks Project, Tag 08PF](https://stacks.math.columbia.edu/tag/08PF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicTopology

namespace Stacks.ChaoticSite


universe v u

/-! ### The constant cosimplicial object at an initial object -/

section General

variable {C : Type u} [Category.{v} C]

/-- An isomorphism of simplicial objects is a homotopy equivalence: its inverse is a homotopy
inverse on the nose, no homotopy being needed. -/
lemma homotopyEquivalences_of_iso {X Y : SimplicialObject (Type v)} (e : X ≅ Y) :
    SimplicialObject.homotopyEquivalences (Type v) e.hom :=
  ⟨e.inv, by rw [e.hom_inv_id]; exact Relation.EqvGen.refl _,
    by rw [e.inv_hom_id]; exact Relation.EqvGen.refl _⟩

/-- **`Mor_C(I, W)` is a singleton for `I` initial**: the simplicial set of morphisms from the
constant cosimplicial object with value `I` into an object `W` is the constant simplicial set on
a singleton. -/
def constInitialYonedaIso {I : C} (hI : IsInitial I) (W : C) :
    ((Functor.const SimplexCategory).obj I).op ⋙ yoneda.obj W ≅
      (Functor.const SimplexCategoryᵒᵖ).obj PUnit.{v + 1} :=
  NatIso.ofComponents
    (fun _ => Equiv.toIso
      { toFun := fun _ => PUnit.unit
        invFun := fun _ => hI.to W
        left_inv := fun _ => hI.hom_ext _ _
        right_inv := fun _ => rfl })
    (by intro _ _ _; rfl)

/-- **The constant cosimplicial object at an initial object is a point resolution.** Every
simplicial set `Mor_C(U_•, W)` is isomorphic to the constant simplicial set on a singleton, hence
homotopy equivalent to it; this is the hypothesis of the criterion of Tag 08Q9. -/
theorem isPointResolution_const_of_isInitial {I : C} (hI : IsInitial I) :
    IsPointResolution ((Functor.const SimplexCategory).obj I) :=
  fun W => ⟨(constInitialYonedaIso hI W).hom,
    homotopyEquivalences_of_iso (constInitialYonedaIso hI W)⟩

/-! ### The Moore complex of a constant cosimplicial object -/

section Coefficients

variable {A : Type*} [Category* A] [Abelian A]

/-- **The Moore complex of `ℱ(U_•)` for a constant cosimplicial object is the alternating
constant complex on `ℱ(I)`**: the simplicial object `ℱ(U_•)` is constant. -/
def cosimplicialMooreComplexConstIso (I : C) (F : Cᵒᵖ ⥤ A) :
    (GeneralValued.cosimplicialMooreComplex' A ((Functor.const SimplexCategory).obj I)).obj F ≅
      ChainComplex.alternatingConst.obj (F.obj (op I)) :=
  (alternatingFaceMapComplex A).mapIso
      (Functor.constComp SimplexCategoryᵒᵖ (op I) F) ≪≫
    AlgebraicTopology.alternatingFaceMapComplexConst.app (F.obj (op I))

/-- **The Moore complex of `ℱ(U_•)` for a constant cosimplicial object has no homology in
positive degrees**: it is the alternating constant complex on `ℱ(I)`, which is exact away from
degree zero. -/
theorem isZero_cosimplicialMooreComplexConst_homology_succ (I : C) (F : Cᵒᵖ ⥤ A) (n : ℕ) :
    IsZero (((GeneralValued.cosimplicialMooreComplex' A
      ((Functor.const SimplexCategory).obj I)).obj F).homology (n + 1)) :=
  IsZero.of_iso
    ((ChainComplex.alternatingConst_exactAt (F.obj (op I)) (n + 1)
      (Nat.succ_ne_zero n)).isZero_homology)
    ((HomologicalComplex.homologyFunctor A (ComplexShape.down ℕ) (n + 1)).mapIso
      (cosimplicialMooreComplexConstIso I F))

variable [HasColimitsOfShape Cᵒᵖ A]

omit [Abelian A] in
/-- **The colimit injection at an initial object is an isomorphism**: `I` initial in `C` makes
`op I` terminal in `Cᵒᵖ`, and the colimit of a diagram with a terminal object is its value
there. -/
theorem isIso_colimitι_of_isInitial {I : C} (hI : IsInitial I) (F : Cᵒᵖ ⥤ A) :
    IsIso (colimit.ι F (op I)) :=
  (colimit.isColimit F).isIso_ι_app_of_isTerminal (op I) (terminalOpOfInitial hI)

/-- **The colimit injection at an initial object is a cokernel of the degree-one differential of
the Moore complex.** The injection is an isomorphism, and an isomorphism out of `Y` is a cokernel
of every morphism into `Y` that it kills. This is the second input of
`Stacks.ChaoticSite.GeneralValued.quasiIso_mooreCochainAugmentation'`. -/
def colimitιConstIsColimit {I : C} (hI : IsInitial I) (F : Cᵒᵖ ⥤ A) :
    IsColimit (CokernelCofork.ofπ
      (colimit.ι F (op (((Functor.const SimplexCategory).obj I).obj (SimplexCategory.mk 0))))
      (GeneralValued.d_one_zero_comp_colimitι' ((Functor.const SimplexCategory).obj I) F)) :=
  haveI : IsIso (colimit.ι F
      (op (((Functor.const SimplexCategory).obj I).obj (SimplexCategory.mk 0)))) :=
    isIso_colimitι_of_isInitial hI F
  CokernelCofork.IsColimit.ofπ _ _
    (fun g _ => inv (colimit.ι F
      (op (((Functor.const SimplexCategory).obj I).obj (SimplexCategory.mk 0)))) ≫ g)
    (fun g _ => by rw [← Category.assoc, IsIso.hom_inv_id, Category.id_comp])
    (fun g _ m hm => by rw [← hm, ← Category.assoc, IsIso.inv_hom_id, Category.id_comp])

/-- **The augmentation of the extended Moore complex is a quasi-isomorphism at a chaotic site
with an initial object**, for *every* coefficient presheaf `ℱ` -- not only a projective one. The
two inputs of `Stacks.ChaoticSite.GeneralValued.quasiIso_mooreCochainAugmentation'` are both
supplied by the initial object: the positive homology vanishes because `ℱ(U_•)` is constant, and
the colimit injection at `U_0 = I` is an isomorphism, hence a cokernel.

This says that `ℱ(U_•) ⟶ (π_!ℱ)[0]` is a resolution, which is the underivedness of `π_!` asserted
by Tag 08QG for such a site. -/
theorem quasiIso_mooreCochainAugmentationConst {I : C} (hI : IsInitial I) (F : Cᵒᵖ ⥤ A) :
    QuasiIso ((GeneralValued.mooreCochainAugmentation'
      ((Functor.const SimplexCategory).obj I)).app F) :=
  GeneralValued.quasiIso_mooreCochainAugmentation' _ F
    (isZero_cosimplicialMooreComplexConst_homology_succ I F)
    (colimitιConstIsColimit hI F)

end Coefficients

end General

/-! ### The degreewise left derived functors of `π_!` -/

section Small

variable {C : Type u} [SmallCategory C]

/-- **`L_0π_! = π_!`**, for the `π_!` of Tag 08PF at abelian coefficients on any small category:
the colimit over `Cᵒᵖ` is right exact, so its zeroth left derived functor is itself. -/
def leftDerivedColimitZeroIsoColimit (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) :
    ((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived 0).obj F ≅ colimit F :=
  (colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerivedZeroIsoSelf.app F

/-- **`L_nπ_! = 0` for `n > 0` on a chaotic site with an initial object.** The constant
cosimplicial object at the initial object is a point resolution, so Tag 08Q9 computes `L_nπ_!(ℱ)`
as the degree `n` homology of the alternating constant complex on `ℱ(I)`, which vanishes for
`n > 0`. -/
theorem isZero_leftDerivedColimit_succ_of_isInitial {I : C} (hI : IsInitial I)
    (F : Cᵒᵖ ⥤ AddCommGrpCat.{u}) (n : ℕ) :
    IsZero (((colim : (Cᵒᵖ ⥤ AddCommGrpCat.{u}) ⥤ AddCommGrpCat.{u}).leftDerived (n + 1)).obj
      F) := by
  exact IsZero.of_iso (isZero_cosimplicialMooreComplexConst_homology_succ I F n)
    ((leftDerivedColimitNatIso ((Functor.const SimplexCategory).obj I)
      (isPointResolution_const_of_isInitial hI) (n + 1)).app F)

end Small

end Stacks.ChaoticSite

end
