module

public import Mathlib.CategoryTheory.Abelian.Injective.Resolution
public import Mathlib.CategoryTheory.Abelian.RightDerived
public import Mathlib.CategoryTheory.Linear.LinearFunctor
public import Mathlib.Algebra.Homology.Linear
public import Mathlib.Algebra.Homology.ShortComplex.Linear

/-!
# Right derived functors are additive, and linear when the functor is

Mathlib builds `CategoryTheory.Functor.rightDerived` as the composite

`injectiveResolutions C ⋙ F.mapHomotopyCategory _ ⋙ HomotopyCategory.homologyFunctor D _ n`

and records neither that it is additive nor that it is `R`-linear. The second and third factors
carry both properties already; the first factor carries neither, and that single missing link is
what makes `(F.rightDerived n).Additive` unavailable. This file supplies it.

Taking injective resolutions is additive and linear for one reason: `map f` is the homotopy class
of `CategoryTheory.InjectiveResolution.desc f`, and `CategoryTheory.InjectiveResolution.desc`
is only determined up to homotopy, so any two lifts of one morphism become equal in the homotopy
category. `desc f + desc g` and `r • desc f` lift `f + g` and `r • f`, so they *are* the images
of those morphisms.

## Main results

* `CategoryTheory.additive_injectiveResolutions` and
  `CategoryTheory.linear_injectiveResolutions`: taking injective resolutions is additive, and
  `R`-linear over an `R`-linear abelian category.
* `CategoryTheory.Functor.additive_rightDerived`: **every right derived functor of an additive
  functor is additive.**
* `CategoryTheory.Functor.linear_rightDerived`: **the right derived functors of an `R`-linear
  functor are `R`-linear.**
* `HomologicalComplex.linear_homologyFunctor` and `HomotopyCategory.linear_homologyFunctor`:
  homology is `R`-linear. The first of these is a `TODO` of
  `Mathlib/Algebra/Homology/Linear.lean`; the short complex half it asks for is already present
  as `CategoryTheory.ShortComplex.homologyFunctor_linear`.

## Implementation notes

`CategoryTheory.Functor.linear_iff` reduces linearity of a functor to its value on `r • 𝟙 X`,
which is how `linear_injectiveResolutions` could also be read; the direct proof of `map_smul` is
used instead because it is the same three lines as `additive_injectiveResolutions`.

Additivity of these functors is elsewhere obtained by reading it off a `δ`-functor structure, as
in `Stacks.Cohomology.DirectSum.additive_Hfunctor`. That route needs a `δ`-functor to exist, so
it does not reach a right derived functor presented on its own; the proofs here need nothing but
the functor.
-/

@[expose] public section

universe v u

open CategoryTheory

namespace CategoryTheory

variable {C : Type u} [Category.{v} C] [Abelian C] [HasInjectiveResolutions C]
  {D : Type*} [Category* D] [Abelian D]

/-- **Taking injective resolutions is additive.** `desc f + desc g` lifts `f + g`, and two lifts
of one morphism are homotopic, hence equal in the homotopy category. -/
instance additive_injectiveResolutions : (injectiveResolutions C).Additive where
  map_add {X Y} f g := by
    have h : (injectiveResolutions C).map f + (injectiveResolutions C).map g =
        (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
          (InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X) +
            InjectiveResolution.desc g (injectiveResolution Y) (injectiveResolution X)) := by
      rw [CategoryTheory.Functor.map_add]; rfl
    rw [h]
    exact HomotopyCategory.eq_of_homotopy _ _ <| InjectiveResolution.descHomotopy (f + g) _ _
      (InjectiveResolution.desc_commutes _ _ _)
      (by rw [Preadditive.comp_add, InjectiveResolution.desc_commutes,
            InjectiveResolution.desc_commutes, CategoryTheory.Functor.map_add,
            Preadditive.add_comp])

/-- The homotopy-category-valued right derived functor of an additive functor is additive. -/
instance Functor.additive_rightDerivedToHomotopyCategory (F : C ⥤ D) [F.Additive] :
    F.rightDerivedToHomotopyCategory.Additive := by
  dsimp [Functor.rightDerivedToHomotopyCategory]
  infer_instance

/-- **Every right derived functor of an additive functor is additive.** All three factors of
`CategoryTheory.Functor.rightDerived` are additive, the first by
`CategoryTheory.additive_injectiveResolutions`. -/
instance Functor.additive_rightDerived (F : C ⥤ D) [F.Additive] (n : ℕ) :
    (F.rightDerived n).Additive := by
  dsimp [Functor.rightDerived, Functor.rightDerivedToHomotopyCategory]
  infer_instance

end CategoryTheory

section Linear

variable {R : Type*} [Semiring R]
  {C : Type u} [Category.{v} C] [Abelian C] [CategoryTheory.Linear R C]
  {D : Type*} [Category* D] [Abelian D] [CategoryTheory.Linear R D]

namespace HomologicalComplex

variable {ι : Type*} {c : ComplexShape ι}

/-- The short complex in degree `i` of a homological complex is `R`-linear in the complex: the
scalar action on a chain map is degreewise. -/
instance linear_shortComplexFunctor (i : ι) :
    Functor.Linear R (HomologicalComplex.shortComplexFunctor C c i) where
  map_smul f r := by ext <;> rfl

/-- **Homology of a homological complex is `R`-linear.** This is the `TODO` of
`Mathlib/Algebra/Homology/Linear.lean`; its short complex half,
`CategoryTheory.ShortComplex.homologyFunctor_linear`, is already present, and
`HomologicalComplex.homologyFunctorIso` factors this one through it. -/
instance linear_homologyFunctor [CategoryWithHomology C] (i : ι) :
    Functor.Linear R (HomologicalComplex.homologyFunctor C c i) :=
  Functor.linear_of_iso R (HomologicalComplex.homologyFunctorIso C c i).symm

/-- The functor placing an object in a single degree is `R`-linear. -/
instance linear_single (j : ℕ) :
    Functor.Linear R (HomologicalComplex.single C (ComplexShape.up ℕ) j) where
  map_smul f r := by ext; simp [HomologicalComplex.single_map_f_self]

end HomologicalComplex

namespace HomotopyCategory

/-- **Homology on the homotopy category is `R`-linear.** The quotient functor is full and
essentially surjective and `HomotopyCategory.homologyFunctorFactors` identifies the composite,
so linearity descends along it. -/
instance linear_homologyFunctor {ι : Type*} {c : ComplexShape ι} [CategoryWithHomology C]
    (i : ι) : Functor.Linear R (HomotopyCategory.homologyFunctor C c i) := by
  have := Functor.linear_of_iso R (HomotopyCategory.homologyFunctorFactors C c i).symm
  exact Functor.linear_of_full_essSurj_comp (HomotopyCategory.quotient C c) _

end HomotopyCategory

namespace CategoryTheory

variable [HasInjectiveResolutions C]

/-- **Taking injective resolutions is `R`-linear.** As for additivity: `r • desc f` lifts
`r • f`, and two lifts of one morphism agree in the homotopy category. -/
instance linear_injectiveResolutions : Functor.Linear R (injectiveResolutions C) where
  map_smul {X Y} f r := by
    have h : r • (injectiveResolutions C).map f =
        (HomotopyCategory.quotient C (ComplexShape.up ℕ)).map
          (r • InjectiveResolution.desc f (injectiveResolution Y) (injectiveResolution X)) := by
      rw [CategoryTheory.Functor.map_smul]; rfl
    rw [h]
    exact HomotopyCategory.eq_of_homotopy _ _ <| InjectiveResolution.descHomotopy (r • f) _ _
      (InjectiveResolution.desc_commutes _ _ _)
      (by rw [Linear.comp_smul, InjectiveResolution.desc_commutes,
            CategoryTheory.Functor.map_smul, Linear.smul_comp])

/-- The homotopy-category-valued right derived functor of an `R`-linear functor is
`R`-linear. -/
instance Functor.linear_rightDerivedToHomotopyCategory (F : C ⥤ D) [F.Additive]
    [Functor.Linear R F] : Functor.Linear R F.rightDerivedToHomotopyCategory := by
  dsimp [Functor.rightDerivedToHomotopyCategory]
  infer_instance

/-- **The right derived functors of an `R`-linear functor are `R`-linear.** This is the
hypothesis that lets `Stacks.EilenbergWatts.iso` run on a cohomology functor: linearity, not
additivity, is what makes the Eilenberg-Watts comparison factor through a tensor product. -/
instance Functor.linear_rightDerived (F : C ⥤ D) [F.Additive] [Functor.Linear R F] (n : ℕ) :
    Functor.Linear R (F.rightDerived n) := by
  dsimp [Functor.rightDerived, Functor.rightDerivedToHomotopyCategory]
  infer_instance

end CategoryTheory

end Linear

end
