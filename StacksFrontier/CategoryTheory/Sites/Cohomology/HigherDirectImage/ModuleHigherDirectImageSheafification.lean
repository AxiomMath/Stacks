module

public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Abelian
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Colimits
public import Mathlib.Algebra.Category.ModuleCat.Presheaf.Limits
public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedFunctorSingleRightDerived
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCoarsening
public import StacksFrontier.CategoryTheory.Abelian.RightDerivedPostcompose
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedLimit.OlssonLaszloSituation
public import StacksFrontier.CategoryTheory.Sites.Cohomology.LocallyQuasiCompact.HigherDirectImageLocalVanishing
public import StacksFrontier.Homology.Injectives.KInjective.FunctorialResolution
import StacksCore.Tactic.StacksAttribute

/-!
# The higher direct image of a sheaf of modules for a coarser topology

Let `C` be a category carrying two Grothendieck topologies `J' ≤ J` and let `R` be a sheaf of
rings for the finer topology `J`, so that the identity functor of `C` is the comparison morphism
of ringed sites `ε : (C_J, R) ⟶ (C_{J'}, R)`. Its direct image `ε_*` is `SheafOfModules.ofLE`,
which changes neither the underlying presheaf of modules nor the morphisms. This file proves

`R^pε_* M = a'(U ↦ H^p_J(U, M))`,

where `a'` is `J'`-sheafification of presheaves of `R`-modules, and deduces that `R^pε_*M = 0` as
soon as `H^p_J(U, M)` vanishes for the members `U` of a family of objects which `J'`-covers every
object of `C`.

## Main definitions

* `Stacks.Cohomology.ModuleHigherDirectImage.forgetOfLE`: the underlying presheaf of modules of a
  sheaf of modules for `J`, read over the sheaf of rings for the coarser topology.
* `Stacks.Cohomology.ModuleHigherDirectImage.sheafificationOfLE`: `a'`, the `J'`-sheafification
  of a presheaf of `R`-modules, as a sheaf of modules for the coarser topology.

## Main results

* `Stacks.Cohomology.ModuleHigherDirectImage.rightDerivedOfLEIso`: **Stacks 072W** for `ε` and
  sheaves of modules — `R^pε_*` is `a'` applied to the cohomology presheaf, the latter being the
  `p`-th right derived functor of the forgetful functor `Mod(R) ⥤ PMod(R)`.
* `Stacks.Cohomology.ModuleHigherDirectImage.moduleCohomologyIso`: the cohomology presheaf,
  evaluated at `U`, is `H^p_J(U, -)`.
* `Stacks.Cohomology.ModuleHigherDirectImage.isZero_rightDerived_ofLE_obj`: `R^pε_*M = 0` when
  the cohomology of `M` vanishes in degree `p` over a `J'`-covering family of objects.
* `Stacks.Cohomology.ModuleHigherDirectImage.isZero_rightDerived_ofLE_obj_of_weakSerre`: the same
  conclusion from assumptions (2) and (3) of Stacks 07A8, in the shape they are stated there.
* `Stacks.Cohomology.ModuleHigherDirectImage.isZero_homology_derivedPushforward_singleFunctor_obj`:
  the same vanishing read in the unbounded derived category, as `Hᵖ(Rε_*(M[0])) = 0` for any right
  derived functor `Rε_*` of `ε_*`.

## The argument

The direct image `ε_*` does not change the underlying presheaf of modules, so `ε_*` is the
forgetful functor `Mod(R) ⥤ PMod(R)` followed by `J'`-sheafification: the counit of
`a' ⊣ forget` is invertible because the forgetful functor is fully faithful. Sheafification of
presheaves of modules is exact — it preserves finite limits, and all colimits because it is a
left adjoint — so it can be pulled out of a right derived functor, which identifies `R^pε_*` with
`a'` applied to the `p`-th right derived functor of the forgetful functor. Evaluation of
presheaves of modules at an object is exact as well, so the value of that derived presheaf at `U`
is `H^p_J(U, -)`.

For the vanishing, each section of the cohomology presheaf over an object `U` restricts to zero
along the members of a `J'`-covering of `U` by objects on which the cohomology vanishes, so the
presheaf of abelian groups underlying the cohomology presheaf has zero `J'`-sheafification. Since
sheafification of presheaves of modules commutes with forgetting the module structures and the
functor to abelian sheaves is faithful, `a'` of the cohomology presheaf is a zero sheaf of
modules.

## Implementation notes

Both the forgetful functor and `J'`-sheafification are written over the sheaf of rings
`R.ofLE h` for the coarser topology rather than over `R`. The two presheaves of rings are equal,
but the restriction-of-scalars functor along `𝟙 (R.ofLE h).obj` is only *definitionally* the
identity, and the fullness of the right adjoint of `PresheafOfModules.sheafification` — which is
what makes the counit invertible — is an instance stated for the identity of one and the same
presheaf of rings. Spelling the source of the sheafification as `PresheafOfModules R.obj` makes
that instance, and with it the invertibility of the counit, unavailable.

## References

* [Stacks Project, Tag 072W](https://stacks.math.columbia.edu/tag/072W)
* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
* [Stacks Project, Tag 01FW](https://stacks.math.columbia.edu/tag/01FW)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

namespace Stacks.Cohomology.ModuleHigherDirectImage

universe u v r m w dJ dJ'

variable {C : Type u} [Category.{v} C] {J J' : GrothendieckTopology C}
  (h : J' ≤ J) (R : Sheaf J RingCat.{r})

/-- A faithful functor which preserves zero morphisms reflects zero objects. -/
private theorem isZero_of_isZero_map {A B : Type*} [Category* A] [Category* B]
    [HasZeroMorphisms A] [HasZeroMorphisms B] (F : A ⥤ B) [F.Faithful]
    [F.PreservesZeroMorphisms] {X : A} (hX : IsZero (F.obj X)) : IsZero X := by
  rw [IsZero.iff_id_eq_zero]
  refine F.map_injective ?_
  rw [F.map_id, F.map_zero]
  exact (IsZero.iff_id_eq_zero _).1 hX

/-- Every element of a zero object of `AddCommGrpCat` is zero. -/
private theorem eq_zero_of_isZero {A : AddCommGrpCat.{m}} (hA : IsZero A) (a : ToType A) :
    a = 0 := by
  simpa using ConcreteCategory.congr_hom ((IsZero.iff_id_eq_zero A).1 hA) a

/-- The underlying presheaf of modules of a sheaf of modules for the finer topology `J`, taken
over the sheaf of rings for the coarser topology `J'`. The two presheaves of rings are equal; this
is `SheafOfModules.forget` with its target written in the form to which `J'`-sheafification of
presheaves of modules applies. -/
abbrev forgetOfLE : SheafOfModules.{m} R ⥤ PresheafOfModules.{m} (R.ofLE h).obj :=
  SheafOfModules.forget R

/-- The functor `forgetOfLE h R` is additive. -/
instance additive_forgetOfLE : (forgetOfLE.{u, v, r, m} h R).Additive where
  map_add := rfl

/-- `ε_*` is additive: it changes neither the underlying presheaves of modules nor the morphisms
between them. -/
instance additive_ofLE : (SheafOfModules.ofLE.{u, v, r, m} h R).Additive where
  map_add := rfl

section Sheafification

variable [HasSheafify J' AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **The `J'`-sheafification of a presheaf of `R`-modules**, as a sheaf of modules for the
coarser topology `J'`. This is the functor `a'` of Stacks 072W for the comparison morphism `ε`. -/
abbrev sheafificationOfLE :
    PresheafOfModules.{m} (R.ofLE h).obj ⥤ SheafOfModules.{m} (R.ofLE h) :=
  PresheafOfModules.sheafification (𝟙 (R.ofLE h).obj)

/-- The sheafification functor `sheafificationOfLE h R` is additive, being a left adjoint. -/
instance additive_sheafificationOfLE : (sheafificationOfLE.{u, v, r, m} h R).Additive :=
  (PresheafOfModules.sheafificationAdjunction (𝟙 (R.ofLE h).obj)).left_adjoint_additive

/-- `a'` preserves finite colimits, being a left adjoint. -/
instance preservesFiniteColimits_sheafificationOfLE :
    PreservesFiniteColimits (sheafificationOfLE.{u, v, r, m} h R) :=
  have : PreservesColimitsOfSize.{0, 0} (sheafificationOfLE.{u, v, r, m} h R) :=
    (PresheafOfModules.sheafificationAdjunction
      (𝟙 (R.ofLE h).obj)).leftAdjoint_preservesColimits
  inferInstance

/-- **`a'` is exact, hence preserves homology.** It preserves finite limits because
sheafification is left exact, and finite colimits because it is a left adjoint. -/
instance preservesHomology_sheafificationOfLE :
    (sheafificationOfLE.{u, v, r, m} h R).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- **`ε_*` is the forgetful functor to presheaves of modules followed by `J'`-sheafification.**
The underlying presheaf of modules of `ε_*M` is that of `M`, and it is already a `J'`-sheaf, so
the counit of `a' ⊣ forget` is invertible there. -/
def forgetCompSheafificationOfLEIso :
    forgetOfLE.{u, v, r, m} h R ⋙ sheafificationOfLE.{u, v, r, m} h R ≅
      SheafOfModules.ofLE.{u, v, r, m} h R :=
  Functor.isoWhiskerLeft (SheafOfModules.ofLE.{u, v, r, m} h R)
      (asIso (PresheafOfModules.sheafificationAdjunction (𝟙 (R.ofLE h).obj)).counit) ≪≫
    (SheafOfModules.ofLE.{u, v, r, m} h R).rightUnitor

end Sheafification

section Derived

variable [HasSheafify J AddCommGrpCat.{m}] [J.WEqualsLocallyBijective AddCommGrpCat.{m}]
  [EnoughInjectives (SheafOfModules.{m} R)]

/-- Evaluation of presheaves of modules at an object is exact, hence preserves homology. -/
instance preservesHomology_evaluation (U : Cᵒᵖ) :
    (PresheafOfModules.evaluation.{m} (R.ofLE h).obj U).PreservesHomology :=
  Functor.preservesHomologyOfExact _

/-- **The cohomology presheaf computes cohomology over an object.** The value at `U` of the `p`-th
right derived functor of the forgetful functor to presheaves of modules is the cohomology
`H^p_J(U, M)` of `Stacks.Cohomology.moduleCohomology`, because evaluation of presheaves of modules
at `U` is exact. -/
def moduleCohomologyIso (p : ℕ) (M : SheafOfModules.{m} R) (U : C) :
    moduleCohomology R U p M ≅
      (PresheafOfModules.evaluation.{m} (R.ofLE h).obj (op U)).obj
        (((forgetOfLE.{u, v, r, m} h R).rightDerived p).obj M) :=
  (Functor.rightDerivedCompIso (forgetOfLE.{u, v, r, m} h R)
    (PresheafOfModules.evaluation.{m} (R.ofLE h).obj (op U)) p).app M

/-- The sections of the cohomology presheaf over an object with vanishing cohomology form a zero
group. -/
theorem isZero_cohomologyPresheaf_obj (p : ℕ) (M : SheafOfModules.{m} R) (U : C)
    (hU : IsZero (moduleCohomology R U p M)) :
    IsZero (((PresheafOfModules.toPresheaf.{m} (R.ofLE h).obj).obj
      (((forgetOfLE.{u, v, r, m} h R).rightDerived p).obj M)).obj (op U)) :=
  (forget₂ (ModuleCat.{m} ((R.ofLE h).obj.obj (op U))) AddCommGrpCat.{m}).map_isZero
    (IsZero.of_iso hU (moduleCohomologyIso.{u, v, r, m} h R p M U).symm)

variable [HasSheafify J' AddCommGrpCat.{m}] [J'.WEqualsLocallyBijective AddCommGrpCat.{m}]

/-- **Stacks 072W for the comparison of two topologies, on sheaves of modules.** The `p`-th higher
direct image `R^pε_*` of the comparison `ε : (C_J, R) ⟶ (C_{J'}, R)` of a topology and a coarser
one is the `J'`-sheafification of the cohomology presheaf `U ↦ H^p_J(U, -)`, the latter being the
`p`-th right derived functor of the forgetful functor from sheaves of `R`-modules to presheaves of
`R`-modules. -/
@[stacks 072W "sheaves of modules, for a topology and a coarser one"]
def rightDerivedOfLEIso (p : ℕ) :
    (SheafOfModules.ofLE.{u, v, r, m} h R).rightDerived p ≅
      (forgetOfLE.{u, v, r, m} h R).rightDerived p ⋙ sheafificationOfLE.{u, v, r, m} h R :=
  (Functor.rightDerivedIsoOfNatIso (forgetCompSheafificationOfLEIso.{u, v, r, m} h R) p).symm ≪≫
    Functor.rightDerivedCompIso (forgetOfLE.{u, v, r, m} h R)
      (sheafificationOfLE.{u, v, r, m} h R) p

variable [J'.HasSheafCompose (forget AddCommGrpCat.{m})]

/-- **The higher direct image of a sheaf of modules for a coarser topology vanishes when its
cohomology does on a covering family of objects.** If every object of `C` has a `J'`-covering by
members of a family `B` of objects of `C`, and `H^p_J(U, M)` is zero for every `U` in `B`, then
`R^pε_*M = 0`.

By Stacks 072W the sheaf `R^pε_*M` is the `J'`-sheafification of the presheaf `U ↦ H^p_J(U, M)`,
and a section of that presheaf over any object dies on a `J'`-covering, namely on one by members
of `B`. No positivity of `p` is needed. -/
theorem isZero_rightDerived_ofLE_obj (p : ℕ) (M : SheafOfModules.{m} R) (B : Set C)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ U : C, B U → IsZero (moduleCohomology R U p M)) :
    IsZero (((SheafOfModules.ofLE.{u, v, r, m} h R).rightDerived p).obj M) := by
  have hloc : ∀ (U : C) (x : ToType (((PresheafOfModules.toPresheaf.{m} (R.ofLE h).obj).obj
      (((forgetOfLE.{u, v, r, m} h R).rightDerived p).obj M)).obj (op U))),
      Presheaf.equalizerSieve (X := op U) x 0 ∈ J' U := by
    intro U x
    obtain ⟨𝒰, hcov, hmem⟩ := hB U
    refine J'.superset_covering ?_ hcov
    rw [Sieve.generate_le_iff]
    rintro V g ⟨i⟩
    have hz := isZero_cohomologyPresheaf_obj.{u, v, r, m} h R p M (𝒰.X i) (hvan _ (hmem i))
    exact (eq_zero_of_isZero hz _).trans (eq_zero_of_isZero hz _).symm
  refine IsZero.of_iso ?_ ((rightDerivedOfLEIso.{u, v, r, m} h R p).app M)
  refine isZero_of_isZero_map (SheafOfModules.toSheaf.{m} (R.ofLE h)) ?_
  refine IsZero.of_iso
    (SheafifiedHigherDirectImage.isZero_presheafToSheaf_of_locallyZero J' _ hloc) ?_
  exact (PresheafOfModules.sheafificationCompToSheaf (𝟙 (R.ofLE h).obj)).app
    (((forgetOfLE.{u, v, r, m} h R).rightDerived p).obj M)

/-- **`R^pε_*F = 0` for `p > 0` and `F` in `A`, from assumptions (2) and (3) of Stacks 07A8.**
The hypotheses are stated exactly as in
`Stacks.Cohomology.CompareTopologies.isWeakSerre_imageOfLE`: every object of `C` has a
`J'`-covering by members of `B`, and the cohomology `H^p_J(U, F)` vanishes for `p > 0`, for `U` in
`B` and for `F` in `A`. -/
theorem isZero_rightDerived_ofLE_obj_of_weakSerre
    (A : ObjectProperty (SheafOfModules.{m} R)) (B : Set C)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ U : C, B U → ∀ p : ℕ, 0 < p → ∀ F : SheafOfModules.{m} R, A F →
      IsZero (moduleCohomology R U p F))
    (p : ℕ) (hp : 0 < p) (F : SheafOfModules.{m} R) (hF : A F) :
    IsZero (((SheafOfModules.ofLE.{u, v, r, m} h R).rightDerived p).obj F) :=
  isZero_rightDerived_ofLE_obj.{u, v, r, m} h R p F B hB fun U hU => hvan U hU p hp F hF

section DerivedCategory

variable [IsGrothendieckAbelian.{w} (SheafOfModules.{m} R)]
  [HasDerivedCategory.{dJ} (SheafOfModules.{m} R)]
  [HasDerivedCategory.{dJ'} (SheafOfModules.{m} (R.ofLE h))]
  (Rε : DerivedCategory (SheafOfModules.{m} R) ⥤
    DerivedCategory (SheafOfModules.{m} (R.ofLE h)))
  (ε : (SheafOfModules.ofLE.{u, v, r, m} h R).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh ⟶ DerivedCategory.Qh ⋙ Rε)
  [Rε.IsRightDerivedFunctor ε
    (HomotopyCategory.quasiIso (SheafOfModules.{m} R) (ComplexShape.up ℤ))]

include ε in
/-- **`Hᵖ(Rε_*(M[0])) = 0`, the vanishing read in the derived category.** For any right derived
functor `Rε_*` of `ε_*` on the unbounded derived category, the degree-`p` cohomology of
`Rε_*` applied to `M` placed in degree `0` vanishes under the hypotheses of
`isZero_rightDerived_ofLE_obj`. This is that statement transported along
`Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived`, which identifies
`Hᵖ(Rε_*(M[0]))` with the classical `R^pε_*M`. -/
theorem isZero_homology_derivedPushforward_singleFunctor_obj (p : ℕ) (M : SheafOfModules.{m} R)
    (B : Set C)
    (hB : ∀ U : C, ∃ 𝒰 : PreZeroHypercover.{max u v} U, 𝒰.sieve₀ ∈ J' U ∧ ∀ i, B (𝒰.X i))
    (hvan : ∀ U : C, B U → IsZero (moduleCohomology R U p M)) :
    IsZero ((DerivedCategory.homologyFunctor (SheafOfModules.{m} (R.ofLE h)) (p : ℤ)).obj
      (Rε.obj ((DerivedCategory.singleFunctor (SheafOfModules.{m} R) 0).obj M))) :=
  IsZero.of_iso (isZero_rightDerived_ofLE_obj.{u, v, r, m} h R p M B hB hvan)
    ((Stacks.DerivedFunctor.singleCompDerivedCompHomologyIsoRightDerived
      (SheafOfModules.ofLE.{u, v, r, m} h R) Rε ε
      (fun K => ⟨_, (Stacks.Injectives.kInjectiveResolutionInclusion _).app K,
        inferInstance, inferInstance⟩) p).app M)

end DerivedCategory

end Derived

end Stacks.Cohomology.ModuleHigherDirectImage

end
