module

public import Mathlib.CategoryTheory.Sites.ConstantSheaf
public import Mathlib.CategoryTheory.Sites.Over
import StacksCore.Tactic.StacksAttribute

/-!
# Constant, locally constant and finite locally constant sheaves

Let `J` be a Grothendieck topology on a category `C`. A sheaf is *constant* when it lies in
the essential image of the constant sheaf functor, i.e. when it is isomorphic to the
sheafification of a constant presheaf. It is *locally constant* when every object of `C`
admits a covering family on each member of which the restricted sheaf is constant. For
sheaves with values in a concrete category, *finite* local constancy additionally requires the
underlying types of the local constant values to be finite. These are the three notions of
Tag 18.43.1.

## Main definitions

* `CategoryTheory.Sheaf.IsConstant` (Mathlib): part (1), a constant sheaf.
* `Stacks.ConstantSheaf.IsLocallyConstant`: part (2), sheaves which become constant on a
  covering of every object.
* `Stacks.ConstantSheaf.IsFiniteLocallyConstant`: part (3), sheaves which become constant with
  finite values on such coverings.

## Main results

* every finite locally constant sheaf is locally constant, recorded as an instance.

## Implementation notes

Restriction of a sheaf to an object `U` is Mathlib's pullback to the localized site `C/U`,
namely `GrothendieckTopology.overPullback`. Coverings are represented by families of morphisms
whose generated sieve belongs to `J`, which is the form the source's coverings take.

The finite notion is stated for an arbitrary concrete target category; this simultaneously
covers sheaves of sets and sheaves of groups, which are the two cases of the source, and gives
the same notion for any other concrete algebraic target.

Mathlib's `CategoryTheory.Sheaf.IsConstant` is already exactly part (1), so it is adopted
directly rather than wrapped in a new name.

## References

* [Stacks Project, Tag 093Q](https://stacks.math.columbia.edu/tag/093Q)
-/

@[expose] public section

open CategoryTheory

namespace Stacks.ConstantSheaf

universe w v v' u u'

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
variable {D : Type u'} [Category.{v'} D]

add_to_stacks 093Q "part (1): a constant sheaf is an object in the essential image of the \
  constant sheaf functor" CategoryTheory.Sheaf.IsConstant
add_to_stacks 03RU "constant sheaves of sets, of abelian groups and of Lambda-modules"
  CategoryTheory.Sheaf.IsConstant
add_to_sga "4 IV 2.7.5" CategoryTheory.Sheaf.IsConstant
add_to_sga "4 IV 4.3.4" CategoryTheory.Sheaf.IsConstant
add_to_sga "4 IX 2.0" CategoryTheory.Sheaf.IsConstant
add_to_ega "0 3.6.1" CategoryTheory.Sheaf.IsConstant

/-- **Stacks 093Q (2).** A sheaf is locally constant if every object of the site has a covering
on each member of which its restriction is a constant sheaf. -/
@[stacks_fixed 093Q "part (2)",
  stacks_fixed 03RU "finite locally constant sheaves of sets and of abelian groups",
  ega "0 3.6.1" "locally simple", sga "3 X 9.2.1" "(2), (4)", sga "4 IX 2.0" "locally constant"]
class IsLocallyConstant [∀ U : C, HasWeakSheafify (J.over U) D] (F : Sheaf J D) : Prop where
  /-- A covering on which the restricted sheaf is constant. -/
  exists_cover : ∀ U : C,
    ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧
        ∀ i, Sheaf.IsConstant (J.over (X i)) ((J.overPullback D (X i)).obj F)

/-- **Stacks 093Q (3).** A sheaf with values in a concrete category is finite locally constant
if every object of the site has a covering on each member of which it is a constant sheaf with
finite underlying value. For `Type` and `Grp`, this is respectively the source's notion for
sheaves of sets and sheaves of groups. -/
@[stacks_fixed 093Q "part (3)",
  stacks_fixed 03RU "finite locally constant sheaves of sets and of abelian groups"]
class IsFiniteLocallyConstant {FD : D → D → Type*} {CD : D → Type w}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
    [∀ U : C, HasWeakSheafify (J.over U) D] (F : Sheaf J D) : Prop where
  /-- A covering on which the restricted sheaf has finite constant values. -/
  exists_finite_cover : ∀ U : C,
    ∃ (I : Type (max u v)) (X : I → C) (f : ∀ i, X i ⟶ U),
      Sieve.ofArrows X f ∈ J U ∧ ∀ i,
        ∃ E : D, Finite (CD E) ∧ Nonempty
          ((constantSheaf (J.over (X i)) D).obj E ≅ (J.overPullback D (X i)).obj F)

/-- A finite locally constant sheaf is locally constant. -/
instance {FD : D → D → Type*} {CD : D → Type w}
    [∀ X Y, FunLike (FD X Y) (CD X) (CD Y)] [ConcreteCategory.{w} D FD]
    [∀ U : C, HasWeakSheafify (J.over U) D] (F : Sheaf J D)
    [hF : IsFiniteLocallyConstant J F] : IsLocallyConstant J F where
  exists_cover U := by
    obtain ⟨I, X, f, hf, h⟩ := hF.exists_finite_cover U
    exact ⟨I, X, f, hf, fun i ↦ (h i).elim fun E ⟨_, e⟩ ↦ ⟨E, e⟩⟩

end Stacks.ConstantSheaf
