module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Abelian
public import Mathlib.Algebra.Category.Grp.FilteredColimits
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RingedToposModules
public import StacksFrontier.CategoryTheory.Sites.Modules.InternalHomAndFlatness.NaiveCotangentTower

/-!
# The base change of a naive cotangent complex along a morphism of sheaves of rings

Let `a : A ⟶ B` and `b : B ⟶ C` be morphisms of sheaves of commutative rings on a site.  The
naive cotangent complex `NL_{B/A}` is a complex of sheaves of `B`-modules; extending scalars
along `b` gives the complex `NL_{B/A} ⊗_B C` of sheaves of `C`-modules.  This file constructs

* extension of scalars along `b` and its adjunction with restriction of scalars, together with
  the counit of that adjunction read on complexes;
* the complex `NL_{B/A} ⊗_B C`;
* the canonical chain map `NL_{B/A} ⊗_B C ⟶ NL_{C/A}`, the adjoint of the map of Stacks 08TX
  attached to the square with vertical morphisms `𝟙 A` and `b`;
* the canonical chain map `NL_{C/A} ⟶ NL_{C/B}` attached to the square with vertical morphisms
  `a` and `𝟙 C`.

These are the first two maps of the six-term exact sequence of **Stacks 0E1Y**.

## Main definitions

* `Stacks.SheafOfModules.towerExtendScalars` and
  `Stacks.SheafOfModules.towerExtendRestrictAdjunction`: extension of scalars along `b` and
  its adjunction with restriction of scalars.
* `Stacks.SheafOfModules.towerCounit`: the counit of that adjunction, read on complexes.
* `Stacks.SheafOfModules.baseChangeNaiveCotangentComplex`: the complex `NL_{B/A} ⊗_B C`.
* `Stacks.SheafOfModules.baseChangeNaiveCotangentMap`: the chain map
  `NL_{B/A} ⊗_B C ⟶ NL_{C/A}`.
* `Stacks.SheafOfModules.relativeNaiveCotangentComplexMap`: the chain map
  `NL_{C/A} ⟶ NL_{C/B}`.

## Main results

* `Stacks.SheafOfModules.towerCounit_naturality`: the counit on complexes is natural; this is
  what expresses the canonical map `NL_{B/A} ⊗_B C ⟶ NL_{C/A}` as an adjoint.
* `Stacks.SheafOfModules.towerLeftSquare` and `Stacks.SheafOfModules.towerRightSquare`: the two
  commutative squares whose composite is the square from `a` to `b`.

## Implementation notes

Extension of scalars is the sheafified sectionwise tensor product, which is available when the
universe of sections of the modules agrees with the universe of sections of the rings; this
file therefore fixes the module universe to be the ring universe `max u v w`, `u` and `v` being
the universes of the objects and of the morphisms of the site.

The counit of the adjunction is transported to complexes by hand: the terms and the
differentials of the image of a complex under a functor are the images of the terms and the
differentials, so the degreewise counit is already a chain map.

## References

* [Stacks Project, Tag 0E1Y](https://stacks.math.columbia.edu/tag/0E1Y)
* [Stacks Project, Tag 08TX](https://stacks.math.columbia.edu/tag/08TX)
* [Stacks Project, Tag 03CZ](https://stacks.math.columbia.edu/tag/03CZ), extension and
  restriction of scalars for sheaves of modules.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u w

namespace Stacks.SheafOfModules

open AlgebraicGeometry.SheafOfModules (underlyingRingHomOfSite)

variable {S : Type u} [Category.{v} S] (J : GrothendieckTopology S)
  [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}]
variable (A B C : Sheaf J CommRingCat.{max u v w}) (a : A ⟶ B) (b : B ⟶ C)

/-! ### Extension of scalars -/

/-- Extension of scalars along `b : B ⟶ C`: the sheafified sectionwise tensor product
`C ⊗_B -`. -/
noncomputable def towerExtendScalars :
    _root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf B) ⥤
      _root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf C) :=
  Stacks.Sheaves.RingedToposModules.extendScalars J b.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf B).property
    (Stacks.SheafOfModules.Tensor.ringSheaf C).property

/-- **Stacks 03CZ.** Extension of scalars along `b` is left adjoint to restriction of scalars
along `b`. -/
noncomputable def towerExtendRestrictAdjunction :
    towerExtendScalars J B C b ⊣
      _root_.SheafOfModules.restrictScalars.{max u v w} (underlyingRingHomOfSite b) :=
  Stacks.Sheaves.RingedToposModules.extendRestrictScalarsAdjunction J b.hom
    (Stacks.SheafOfModules.Tensor.ringSheaf B).property
    (Stacks.SheafOfModules.Tensor.ringSheaf C).property

/-- Extension of scalars along `b` is an additive functor. -/
noncomputable instance towerExtendScalars_additive :
    (towerExtendScalars J B C b).Additive :=
  (towerExtendRestrictAdjunction J B C b).left_adjoint_additive

/-- Extension of scalars along `b`, applied termwise to complexes. -/
noncomputable abbrev towerExtendScalarsComplexes :
    CochainComplex
        (_root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf B)) ℤ ⥤
      CochainComplex
        (_root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf C)) ℤ :=
  (towerExtendScalars J B C b).mapHomologicalComplex (ComplexShape.up ℤ)

/-- Restriction of scalars along `b`, applied termwise to complexes. -/
noncomputable abbrev towerRestrictScalarsComplexes :
    CochainComplex
        (_root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf C)) ℤ ⥤
      CochainComplex
        (_root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf B)) ℤ :=
  (_root_.SheafOfModules.restrictScalars.{max u v w}
    (underlyingRingHomOfSite b)).mapHomologicalComplex (ComplexShape.up ℤ)

omit [HasWeakSheafify J CommRingCat.{max u v w}] in
/-- The counit of extension and restriction of scalars is natural. -/
theorem towerCounit_app_naturality
    {M N : _root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf C)}
    (h : M ⟶ N) :
    (towerExtendScalars J B C b).map
          ((_root_.SheafOfModules.restrictScalars.{max u v w}
            (underlyingRingHomOfSite b)).map h) ≫
        (towerExtendRestrictAdjunction J B C b).counit.app N =
      (towerExtendRestrictAdjunction J B C b).counit.app M ≫ h := by
  simp

/-- The counit of extension and restriction of scalars, read on complexes: in each degree it
is the counit of the adjunction. -/
noncomputable def towerCounit
    (K : CochainComplex
      (_root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf C)) ℤ) :
    (towerExtendScalarsComplexes J B C b).obj
        ((towerRestrictScalarsComplexes J B C b).obj K) ⟶ K where
  f i := (towerExtendRestrictAdjunction J B C b).counit.app (K.X i)
  comm' i j _ := by
    simp only [Functor.mapHomologicalComplex_obj_d]
    exact (towerCounit_app_naturality J B C b (K.d i j)).symm

omit [HasWeakSheafify J CommRingCat.{max u v w}] in
/-- In degree `i`, the counit on a complex `K` is the counit of the adjunction at `K.X i`. -/
@[simp] theorem towerCounit_f
    (K : CochainComplex
      (_root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf C)) ℤ)
    (i : ℤ) :
    (towerCounit J B C b K).f i =
      (towerExtendRestrictAdjunction J B C b).counit.app (K.X i) := rfl

omit [HasWeakSheafify J CommRingCat.{max u v w}] in
/-- The counit on complexes is natural. -/
theorem towerCounit_naturality
    {K L : CochainComplex
      (_root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf C)) ℤ}
    (g : K ⟶ L) :
    (towerExtendScalarsComplexes J B C b).map
          ((towerRestrictScalarsComplexes J B C b).map g) ≫ towerCounit J B C b L =
      towerCounit J B C b K ≫ g := by
  apply HomologicalComplex.hom_ext
  intro i
  simp

/-! ### The base change of the naive cotangent complex -/

/-- The base change `NL_{B/A} ⊗_B C` of the naive cotangent complex of `B` over `A`: the
termwise extension of scalars along `b`. -/
noncomputable abbrev baseChangeNaiveCotangentComplex :
    CochainComplex
      (_root_.SheafOfModules.{max u v w} (Stacks.SheafOfModules.Tensor.ringSheaf C)) ℤ :=
  (towerExtendScalarsComplexes J B C b).obj
    (naiveCotangentComplex.{v, u, max u v w, max u v w} J A B a)

/-- The map of Stacks 08TX for the square with vertical morphisms `𝟙 A` and `b`, which
compares `NL_{B/A}` with `NL_{C/A}` read as a complex of sheaves of `B`-modules. -/
noncomputable abbrev baseChangeSquareMap :
    naiveCotangentComplex.{v, u, max u v w, max u v w} J A B a ⟶
      (towerRestrictScalarsComplexes J B C b).obj
        (naiveCotangentComplex.{v, u, max u v w, max u v w} J A C (a ≫ b)) :=
  naiveCotangentComplexMapOfSquare.{v, u, max u v w, max u v w} J A B a A C (a ≫ b) (𝟙 A) b
    (Category.id_comp (a ≫ b)).symm

/-- **The canonical map `NL_{B/A} ⊗_B C ⟶ NL_{C/A}`**: the adjoint of the map of Stacks 08TX
attached to the square with vertical morphisms `𝟙 A` and `b`. -/
noncomputable def baseChangeNaiveCotangentMap :
    baseChangeNaiveCotangentComplex J A B C a b ⟶
      naiveCotangentComplex.{v, u, max u v w, max u v w} J A C (a ≫ b) :=
  (towerExtendScalarsComplexes J B C b).map (baseChangeSquareMap J A B C a b) ≫
    towerCounit J B C b _

/-- **The canonical map `NL_{C/A} ⟶ NL_{C/B}`** attached to the factorisation `A ⟶ B ⟶ C` of
the structure morphism of `C`: the map of Stacks 08TX for the square with vertical morphisms
`a` and `𝟙 C`. -/
noncomputable def relativeNaiveCotangentComplexMap :
    naiveCotangentComplex.{v, u, max u v w, max u v w} J A C (a ≫ b) ⟶
      naiveCotangentComplex.{v, u, max u v w, max u v w} J B C b :=
  naiveCotangentComplexMapOfSquare.{v, u, max u v w, max u v w} J A C (a ≫ b) B C b a (𝟙 C)
    (comp_id_eq_comp_of_fac J A C (a ≫ b) B b a rfl)

/-! ### The null homotopy -/

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The left-hand square of the tower, with vertical morphisms `𝟙 B` and `b ≫ 𝟙 C`. -/
theorem towerLeftSquare : 𝟙 B ≫ b = b ≫ 𝟙 C := by
  rw [Category.id_comp, Category.comp_id]

omit [HasWeakSheafify J CommRingCat.{max u v w}]
  [J.HasSheafCompose (forget₂ CommRingCat.{max u v w} RingCat.{max u v w})]
  [HasSheafify J AddCommGrpCat.{max u v w}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{max u v w}] in
/-- The right-hand square of the tower, with vertical morphisms `𝟙 A ≫ a` and `𝟙 B`. -/
theorem towerRightSquare : a ≫ 𝟙 B = 𝟙 A ≫ a := by
  rw [Category.id_comp, Category.comp_id]

end Stacks.SheafOfModules

end
