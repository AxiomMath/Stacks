module

public import StacksFrontier.Algebra.Homology.HomotopyCategory.ExactFunctorHomology
public import StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.EdgeMorphism

/-! # Restriction in the object of the site, on derived sections

Let `(C, O)` be a ringed site and `g : U' ⟶ U` a morphism of `C`.  Derived sections over `U`,
`Stacks.Cohomology.HypercohomologyEdge.derivedSections O U`, take values in
`DerivedCategory (ModuleCat (O(U)))` — a category which **depends on the object of the site**.
So "restriction along `g`" is *not* a natural transformation between two functors with a common
target: the target of derived sections over `U'` is a category of modules over a different ring.
It becomes one after composing with restriction of scalars along `ρ := O(U) ⟶ O(U')`, and that
is the shape this file provides.

`Stacks.Cohomology.HypercohomologyEdge.sectionsRestrict` is the restriction map of the sheaf of
modules itself, read as a morphism into restriction of scalars; it is nothing but
`CategoryTheory.PresheafOfModules.restriction` on the underlying presheaf of modules.  Its
derived companion `derivedSectionsRestrict` is obtained from the universal property of the total
right derived functor, exactly as the Leray comparison of [Stacks, Tag 0D5W] is: a transformation
out of `RΓ(U, -)` is determined by, and may be prescribed by, its composite with the unit of that
derived functor.  Finally `derivedSectionsRestrictHomology` is the same comparison on degree-`q`
cohomology, obtained by composing with the commutation of an exact functor with homology,
`Stacks.Homology.derivedHomologyIso`.

## Main definitions

* `Stacks.Cohomology.HypercohomologyEdge.sectionsRestrict`: restriction of sections along
  `g : U' ⟶ U`, as a transformation `Γ(U, -) ⟶ Γ(U', -) ⋙ Res_ρ`.
* `Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrict`: the same on unbounded derived
  sections, `RΓ(U, -) ⟶ RΓ(U', -) ⋙ R Res_ρ`.
* `Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrictHomology`: the same on degree-`q`
  hypercohomology, `H^q(U, -) ⟶ H^q(U', -) ⋙ Res_ρ`.

## Main results

* `Stacks.Cohomology.HypercohomologyEdge.derivedSectionsRestrict_fac` and
  `derivedSectionsRestrict_ext`: the equation characterizing `derivedSectionsRestrict`, and the
  uniqueness it gives.  This is the form in which a statement about the derived restriction is
  checked: a transformation out of a right derived functor is pinned down by its restriction
  along the unit, on the homotopy category, where restriction of sections is termwise.

*The unit is written out rather than named.*  `Stacks.Cohomology.HypercohomologyEdge` already has
a name for it, `derivedSectionsUnit` of
`StacksFrontier.CategoryTheory.Sites.Cohomology.HypercohomologyEdge.TruncationTowerConstancy`, but
that one is declared under a standing `EnoughInjectives` hypothesis which it does not need and
which nothing here has; a second abbreviation for the same transformation would be a duplicate,
so the unit is spelled out instead.

## Implementation notes

*Restriction of scalars along a homomorphism of possibly noncommutative rings is exact.*  The
structure ring of a ringed site is an object of `RingCat`, so Mathlib's exactness instances for
`CategoryTheory.ModuleCat.restrictScalars` — stated for commutative rings — do not apply.  The
general statement is proved here as `restrictScalars_shortComplex_exact` and its two corollaries,
which are kept as *theorems* and installed with `attribute [local instance]`: a global instance
would duplicate, at greater generality, the one Mathlib already has for commutative rings, and
two instances of one class differ as terms even where they agree as propositions.  A file which
needs to write `(ModuleCat.restrictScalars ρ).mapDerivedCategory` in a *new* statement should
install them the same way; a file which only applies the results below needs nothing, since the
instances are already resolved inside their types.

*Degree-`q` cohomology is not derived separately.*  `derivedSectionsRestrictHomology` is built
from `derivedSectionsRestrict` by composing with `Stacks.Homology.derivedHomologyIso`, rather
than by a second appeal to the universal property at the composite
`Γ(U, -) ⋙ H^q`.  The two agree — both are transformations out of a right derived functor of the
same functor, and `derivedSectionsRestrict_ext` identifies them — but the present route needs no
further unit.

## References

* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
* [Stacks Project, Tag 0BKV](https://stacks.math.columbia.edu/tag/0BKV)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace Stacks.Cohomology.HypercohomologyEdge

universe u v wRing wModule g

attribute [local instance] HasDerivedCategory.standard

/-! ### Exactness of restriction of scalars over a possibly noncommutative ring -/

/-- **Restriction of scalars carries exact short complexes to exact short complexes.**  On
underlying functions nothing changes, so exactness is unaffected.  Mathlib carries this only for
commutative rings, while the structure ring of a ringed site is an object of `RingCat`. -/
theorem restrictScalars_shortComplex_exact {A : Type*} {B : Type*} [Ring A] [Ring B]
    (φ : A →+* B) (S : ShortComplex (ModuleCat.{wModule} B)) (hS : S.Exact) :
    (S.map (ModuleCat.restrictScalars.{wModule} φ)).Exact := by
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hS ⊢
  exact hS

/-- Restriction of scalars preserves both finite limits and finite colimits, being exact. -/
private theorem restrictScalars_preservesFiniteLimits_and_colimits {A : Type*} {B : Type*}
    [Ring A] [Ring B] (φ : A →+* B) :
    PreservesFiniteLimits (ModuleCat.restrictScalars.{wModule} φ) ∧
      PreservesFiniteColimits (ModuleCat.restrictScalars.{wModule} φ) :=
  ((Functor.exact_tfae (ModuleCat.restrictScalars.{wModule} φ)).out 2 4).mp
    (restrictScalars_shortComplex_exact φ)

/-- Restriction of scalars along a homomorphism of possibly noncommutative rings preserves finite
limits.  Kept as a theorem, not an instance: see the implementation notes. -/
theorem restrictScalars_preservesFiniteLimits {A : Type*} {B : Type*} [Ring A] [Ring B]
    (φ : A →+* B) : PreservesFiniteLimits (ModuleCat.restrictScalars.{wModule} φ) :=
  (restrictScalars_preservesFiniteLimits_and_colimits φ).1

/-- Restriction of scalars along a homomorphism of possibly noncommutative rings preserves finite
colimits.  Kept as a theorem, not an instance: see the implementation notes. -/
theorem restrictScalars_preservesFiniteColimits {A : Type*} {B : Type*} [Ring A] [Ring B]
    (φ : A →+* B) : PreservesFiniteColimits (ModuleCat.restrictScalars.{wModule} φ) :=
  (restrictScalars_preservesFiniteLimits_and_colimits φ).2

attribute [local instance] restrictScalars_preservesFiniteLimits
  restrictScalars_preservesFiniteColimits evaluation_additive

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (O : Sheaf J RingCat.{wRing})

/-! ### Restriction of sections -/

/-- **Restriction of sections along a morphism of the site.**  For `g : U' ⟶ U`, the restriction
map `M(U) ⟶ M(U')` of a sheaf of `O`-modules is semilinear over `ρ : O(U) ⟶ O(U')`, so it is a
morphism of `O(U)`-modules into restriction of scalars along `ρ`.  This is the restriction map of
the sheaf of modules itself, and nothing more. -/
def sectionsRestrict {U U' : C} (g : U' ⟶ U) :
    SheafOfModules.evaluation O (.op U) ⟶
      SheafOfModules.evaluation O (.op U') ⋙
        ModuleCat.restrictScalars (O.obj.map g.op).hom :=
  Functor.whiskerLeft (SheafOfModules.forget O) (PresheafOfModules.restriction O.obj g.op)

variable [HasSheafify J AddCommGrpCat.{wModule}]
  [J.WEqualsLocallyBijective AddCommGrpCat.{wModule}]

/-- **Restriction of scalars along `ρ : O(U) ⟶ O(U')`, on unbounded derived categories.**
Restriction of scalars is exact, so it induces a functor on derived categories; this is the
functor through which restriction in the object of the site becomes a natural transformation. -/
def restrictScalarsDerived {U U' : C} (g : U' ⟶ U) :
    DerivedCategory (ModuleCat.{wModule} (O.obj.obj (.op U'))) ⥤
      DerivedCategory (ModuleCat.{wModule} (O.obj.obj (.op U))) :=
  (ModuleCat.restrictScalars (O.obj.map g.op).hom).mapDerivedCategory

variable [IsGrothendieckAbelian.{g} (SheafOfModules.{wModule} O)]

/-- The transformation prescribing `derivedSectionsRestrict` through the universal property of
`RΓ(U, -)`: on the homotopy category, restrict the complex of sections termwise, then compare
the termwise image with the value of `RΓ(U', -)` there. -/
def sectionsRestrictUnit {U U' : C} (g : U' ⟶ U) :
    homotopySections O U ⟶
      DerivedCategory.Qh ⋙ (derivedSections O U' ⋙ restrictScalarsDerived O g) :=
  Functor.whiskerRight (NatTrans.mapHomotopyCategory (sectionsRestrict O g)
      (ComplexShape.up ℤ)) DerivedCategory.Qh ≫
    Functor.whiskerRight (Functor.mapHomotopyCategoryCompIso
      (Iso.refl (SheafOfModules.evaluation O (.op U') ⋙
        ModuleCat.restrictScalars (O.obj.map g.op).hom))
        (ComplexShape.up ℤ)).inv DerivedCategory.Qh ≫
    Functor.whiskerLeft ((SheafOfModules.evaluation O (.op U')).mapHomotopyCategory
        (ComplexShape.up ℤ))
      (ModuleCat.restrictScalars (O.obj.map g.op).hom).mapDerivedCategoryFactorsh.inv ≫
    Functor.whiskerRight ((homotopySections O U').totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)))
      (restrictScalarsDerived O g)

/-- **Restriction in the object of the site, on unbounded derived sections.**
`RΓ(U, -) ⟶ RΓ(U', -) ⋙ R Res_ρ`, the transformation induced by `sectionsRestrictUnit` through
the universal property of the right derived functor of sections over `U`.  By
`derivedSectionsRestrict_fac` its composite with the unit of `RΓ(U, -)` is that transformation,
and by `derivedSectionsRestrict_ext` that equation determines it. -/
def derivedSectionsRestrict {U U' : C} (g : U' ⟶ U) :
    derivedSections O U ⟶ derivedSections O U' ⋙ restrictScalarsDerived O g :=
  (derivedSections O U).rightDerivedDesc
      ((homotopySections O U).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) _
    (sectionsRestrictUnit O g)

/-- The equation characterizing the derived restriction: composing it with the unit of
`RΓ(U, -)` recovers the termwise restriction of sections. -/
theorem derivedSectionsRestrict_fac {U U' : C} (g : U' ⟶ U) :
    (homotopySections O U).totalRightDerivedUnit DerivedCategory.Qh
          (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) ≫
        Functor.whiskerLeft DerivedCategory.Qh (derivedSectionsRestrict O g) =
      sectionsRestrictUnit O g :=
  (derivedSections O U).rightDerived_fac
      ((homotopySections O U).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) _
    (sectionsRestrictUnit O g)

/-- The equation of `derivedSectionsRestrict_fac` determines the derived restriction: two
transformations out of `RΓ(U, -)` that agree after composition with the unit are equal.  This is
how a square involving `derivedSectionsRestrict` is proved — on the homotopy category, where
restriction of sections is termwise. -/
theorem derivedSectionsRestrict_ext {U : C}
    {G : DerivedCategory (SheafOfModules.{wModule} O) ⥤
      DerivedCategory (ModuleCat.{wModule} (O.obj.obj (.op U)))}
    (τ₁ τ₂ : derivedSections O U ⟶ G)
    (h : (homotopySections O U).totalRightDerivedUnit DerivedCategory.Qh
            (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) ≫
          Functor.whiskerLeft DerivedCategory.Qh τ₁ =
        (homotopySections O U).totalRightDerivedUnit DerivedCategory.Qh
            (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) ≫
          Functor.whiskerLeft DerivedCategory.Qh τ₂) :
    τ₁ = τ₂ :=
  (derivedSections O U).rightDerived_ext
      ((homotopySections O U).totalRightDerivedUnit DerivedCategory.Qh
        (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)))
    (HomotopyCategory.quasiIso (SheafOfModules.{wModule} O) (ComplexShape.up ℤ)) _ _ _ h

/-- **Restriction in the object of the site, on degree-`q` hypercohomology.**
`H^q(U, -) ⟶ H^q(U', -) ⋙ Res_ρ`: the derived restriction, read on homology through the
commutation of the exact functor `Res_ρ` with homology. -/
def derivedSectionsRestrictHomology {U U' : C} (g : U' ⟶ U) (q : ℤ) :
    derivedSections O U ⋙
        DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q ⟶
      (derivedSections O U' ⋙
          DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U'))) q) ⋙
        ModuleCat.restrictScalars (O.obj.map g.op).hom :=
  Functor.whiskerRight (derivedSectionsRestrict O g)
      (DerivedCategory.homologyFunctor (ModuleCat.{wModule} (O.obj.obj (.op U))) q) ≫
    Functor.whiskerLeft (derivedSections O U')
      (Stacks.Homology.derivedHomologyIso
        (ModuleCat.restrictScalars (O.obj.map g.op).hom) q).hom

end Stacks.Cohomology.HypercohomologyEdge

end
