module

public import StacksFrontier.AlgebraicGeometry.ProjectionFormulaInvertible.Abstract
public import Mathlib.CategoryTheory.Shift.CommShiftTwo

/-!
# Tensoring by a shift of a unit object

Let `T : C ⥤ C ⥤ C` be a bifunctor on a category with a shift by `ℤ`, commuting with the shifts
in both variables, and let `U : C` be an object for which `T.flip.obj U` — that is `- ⊗ U` — is
isomorphic to the identity.  Then `- ⊗ U⟦m⟧` is isomorphic to the shift by `m`, hence an
equivalence.

Both statements are proved here for an arbitrary bifunctor, with every category, functor and
object a variable; in the intended application `T` is a derived tensor product on a derived
category of sheaves of modules, and the two spellings of its sheaf of rings that meet there make
a goal mentioning it not type-correct at `implicit` transparency, so no rewrite can be performed
on such a goal.  Applying a lemma stated over variables runs the conversion at default
transparency instead.

## Main results

* `CategoryTheory.Functor.tensorRightOfUncurryIso`: tensoring on the right by a fixed object in
  the uncurried bifunctor, `Stacks.ProjectionFormula.tensorRightOf (Functor.uncurry.obj T) H`, is
  `T.flip.obj H`.  The two agree on objects, and on morphisms they differ by the identity
  `T (g ⊗ 𝟙) = (T g) H`.
* `CategoryTheory.Functor.flipObjShiftIsoOfUnitor`: `- ⊗ U⟦m⟧ ≅ ⟦m⟧`, from the commutation of
  `M ⊗ -` with the shift and the right unit isomorphism, whose naturality in `M` is the
  `commShift_map` field of `CategoryTheory.Functor.CommShift₂`.
* `CategoryTheory.Functor.isEquivalence_tensorRightOf_shiftedUnit`: tensoring on the right by
  `U⟦m⟧` is an equivalence.
-/

@[expose] public noncomputable section

open scoped CategoryTheory.Prod

namespace CategoryTheory.Functor

universe v u

variable {C : Type u} [Category.{v} C] (T : C ⥤ C ⥤ C)

/-- **Tensoring on the right by a fixed object is the flip of the bifunctor at that object.**
`Stacks.ProjectionFormula.tensorRightOf` is stated for a bifunctor on a product, as the
projection-formula map is; `Functor.flip` is the curried form of the same functor.  They agree on
objects, and on morphisms the uncurried bifunctor at `g ×ₘ 𝟙 H` is `(T.map g).app H` followed by
the identity. -/
def tensorRightOfUncurryIso (H : C) :
    Stacks.ProjectionFormula.tensorRightOf (Functor.uncurry.obj T) H ≅ T.flip.obj H :=
  NatIso.ofComponents (fun _ => Iso.refl _) (by
    intro M M' g
    dsimp
    rw [CategoryTheory.Functor.map_id, Category.comp_id, Category.comp_id, Category.id_comp])

/-- **Tensoring on the right by isomorphic objects gives isomorphic functors.**  Through
`tensorRightOfUncurryIso` this is the image of the isomorphism under `T.flip`. -/
def tensorRightOfCongr {H H' : C} (i : H ≅ H') :
    Stacks.ProjectionFormula.tensorRightOf (Functor.uncurry.obj T) H ≅
      Stacks.ProjectionFormula.tensorRightOf (Functor.uncurry.obj T) H' :=
  tensorRightOfUncurryIso T H ≪≫ T.flip.mapIso i ≪≫ (tensorRightOfUncurryIso T H').symm

/-- **Tensoring on the right by an object isomorphic to one by which it is an equivalence is an
equivalence.** -/
theorem isEquivalence_tensorRightOf_of_iso {H H' : C} (i : H ≅ H')
    (h : (Stacks.ProjectionFormula.tensorRightOf (Functor.uncurry.obj T) H').IsEquivalence) :
    (Stacks.ProjectionFormula.tensorRightOf (Functor.uncurry.obj T) H).IsEquivalence :=
  @Functor.isEquivalence_of_iso _ _ _ _ _ _ (tensorRightOfCongr T i).symm h

variable [HasShift C ℤ] [Preadditive C] [∀ n : ℤ, (shiftFunctor C n).Additive]
  [T.CommShift₂Int]

/-- **Tensoring on the right by a shift of a unit object is that shift.**  If `- ⊗ U` is
isomorphic to the identity by `ρ`, then `- ⊗ U⟦m⟧ ≅ ⟦m⟧`: the component at `M` is the
commutation of `M ⊗ -` with the shift by `m`, read at `U`, followed by the shift of `ρ` at `M`.

Naturality in `M` is exactly `CategoryTheory.Functor.CommShift₂.commShift_map`, the statement
that `T.map g` is compatible with the commutations of `M ⊗ -` and `M' ⊗ -` with the shift,
together with the naturality of `ρ`. -/
def flipObjShiftIsoOfUnitor (U : C) (ρ : T.flip.obj U ≅ 𝟭 C) (m : ℤ) :
    T.flip.obj (U⟦m⟧) ≅ shiftFunctor C m :=
  NatIso.ofComponents
    (fun M => ((T.obj M).commShiftIso m).app U ≪≫ (shiftFunctor C m).mapIso (ρ.app M))
    (fun {M M'} g => by
      dsimp
      simp only [Category.assoc]
      rw [← NatTrans.shift_app_comm_assoc, ← Functor.map_comp, ← Functor.map_comp]
      congr 2
      simpa using ρ.hom.naturality g)

/-- **Tensoring on the right by a shift of a unit object is an equivalence.**  It is isomorphic to
a shift functor, which is one. -/
theorem isEquivalence_tensorRightOf_shiftedUnit (U : C) (ρ : T.flip.obj U ≅ 𝟭 C) (m : ℤ) :
    (Stacks.ProjectionFormula.tensorRightOf (Functor.uncurry.obj T) (U⟦m⟧)).IsEquivalence :=
  Functor.isEquivalence_of_iso
    ((tensorRightOfUncurryIso T (U⟦m⟧)).trans (flipObjShiftIsoOfUnitor T U ρ m)).symm

end CategoryTheory.Functor

end
