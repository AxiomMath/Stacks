module

public import StacksFrontier.AlgebraicGeometry.DerivedTildeEquivalence.AbsoluteRightDerived
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleDerivedGlobalSectionsExistence

/-!
# Additivity of an unbounded right derived functor computed by K-injectives

Let `A` be an abelian category in which every cochain complex admits a quasi-isomorphism into a
K-injective complex, let `F : K(A) ⥤ H` be an additive functor into a preadditive category and
let `RF : D(A) ⥤ H`, with unit `α : F ⟶ Qh ⋙ RF`, be a right derived functor of `F` along the
quasi-isomorphisms. Then `RF` is additive.

The unit `α` is invertible at a K-injective complex ([Stacks, Tag 070K]), and for a K-injective
`J` the localization map `Hom_{K(A)}(I, J) ⟶ Hom_{D(A)}(I, J)` is bijective ([Stacks, Tag 070I]).
So on morphisms between images of K-injective complexes `RF` is conjugate to `F`, which is
additive; and every object of `D(A)` is the image of a K-injective complex, so an arbitrary pair
of parallel morphisms is carried to such a pair by isomorphisms at both ends.

This discharges the additivity of unbounded derived global sections on a small étale site, which
is the shape in which the dévissage of [Stacks, Tag 0GJR] consumes it: `Functor.Additive` is not
an available instance for `CategoryTheory.Functor.totalRightDerived`.

## Main results

* `Stacks.SmallDerivedCategory.additive_of_exists_quasiIso_isKInjective` — an unbounded right
  derived functor of an additive functor is additive, when K-injective resolutions exist.
* `Stacks.EtaleCohomology.smallEtaleDerivedGlobalSections_additive` — unbounded derived global
  sections on the small étale site of a scheme form an additive functor.

## References

* [Stacks Project, Tag 070I](https://stacks.math.columbia.edu/tag/070I)
* [Stacks Project, Tag 070K](https://stacks.math.columbia.edu/tag/070K)
* [Stacks Project, Tag 079P](https://stacks.math.columbia.edu/tag/079P)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Functor
open AlgebraicGeometry AlgebraicGeometry.Scheme

namespace Stacks.SmallDerivedCategory

variable {A : Type*} [Category* A] [Abelian A] [HasDerivedCategory A]
  {H : Type*} [Category* H] [Preadditive H]

/-- **An unbounded right derived functor of an additive functor is additive.** Let `A` be an
abelian category in which every cochain complex admits a quasi-isomorphism into a K-injective
complex, let `F : K(A) ⥤ H` be additive and let `RF : D(A) ⥤ H` be a right derived functor of
`F` along the quasi-isomorphisms, with unit `α`. Then `RF` is additive.

On morphisms between the images of K-injective complexes `RF` is `F` conjugated by the unit,
which is invertible there; and every object of `D(A)` is the image of a K-injective complex. -/
theorem additive_of_exists_quasiIso_isKInjective
    (F : HomotopyCategory A (ComplexShape.up ℤ) ⥤ H) [F.Additive]
    (RF : DerivedCategory A ⥤ H) (α : F ⟶ DerivedCategory.Qh ⋙ RF)
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso A (ComplexShape.up ℤ))]
    (hA : ∀ K : CochainComplex A ℤ, ∃ (I : CochainComplex A ℤ) (f : K ⟶ I),
      I.IsKInjective ∧ QuasiIso f) :
    RF.Additive := by
  obtain ⟨-, hiso⟩ :=
    Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective F hA
  have key : ∀ {I J : CochainComplex A ℤ}, I.IsKInjective → J.IsKInjective →
      ∀ u v : DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) ⟶
        DerivedCategory.Qh.obj ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J),
      RF.map (u + v) = RF.map u + RF.map v := by
    intro I J hI hJ u v
    have hnat : ∀ w : (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I ⟶
        (HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J,
        α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) ≫
            RF.map (DerivedCategory.Qh.map w) =
          F.map w ≫ α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj J) :=
      fun w => (α.naturality w).symm
    have hsurj := (CochainComplex.IsKInjective.Qh_map_bijective
      ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I) J).surjective
    obtain ⟨u', rfl⟩ := hsurj u
    obtain ⟨v', rfl⟩ := hsurj v
    have := hiso DerivedCategory.Qh RF α I hI
    rw [← DerivedCategory.Qh.map_add,
      ← cancel_epi (α.app ((HomotopyCategory.quotient A (ComplexShape.up ℤ)).obj I)),
      hnat, Preadditive.comp_add, hnat, hnat, F.map_add, Preadditive.add_comp]
  constructor
  intro X Y u v
  obtain ⟨I, hI, ⟨a⟩⟩ := exists_isKInjective_iso_of_exists_quasiIso_isKInjective hA X
  obtain ⟨J, hJ, ⟨b⟩⟩ := exists_isKInjective_iso_of_exists_quasiIso_isKInjective hA Y
  have hrep : ∀ w : X ⟶ Y,
      RF.map a.inv ≫ RF.map (a.hom ≫ w ≫ b.inv) ≫ RF.map b.hom = RF.map w := by
    intro w
    rw [← RF.map_comp, ← RF.map_comp]
    simp
  rw [← hrep (u + v), ← hrep u, ← hrep v]
  simp only [Preadditive.add_comp, Preadditive.comp_add, key hI hJ]

end Stacks.SmallDerivedCategory

namespace Stacks.EtaleCohomology

universe u

attribute [local instance] HasDerivedCategory.standard

/-- **Unbounded derived global sections on a small étale site form an additive functor.** Global
sections of abelian étale sheaves are additive, and abelian sheaves on a small étale site are a
Grothendieck abelian category, so every complex of them has a K-injective resolution; the right
derived functor of an additive functor is then additive. -/
public instance smallEtaleDerivedGlobalSections_additive (X : Scheme.{u}) :
    (smallEtaleDerivedGlobalSections X).Additive :=
  haveI := isGrothendieckAbelian_sheaf_smallEtale_objectUniverse X
  Stacks.SmallDerivedCategory.additive_of_exists_quasiIso_isKInjective
    ((Sheaf.Γ (smallEtaleTopology X) Ab.{u + 1}).mapHomotopyCategory (ComplexShape.up ℤ) ⋙
      DerivedCategory.Qh)
    (smallEtaleDerivedGlobalSections X) (smallEtaleDerivedGlobalSectionsUnit X)
    (Stacks.Injectives.exists_quasiIso_isKInjective_of_isGrothendieckAbelian _)

end Stacks.EtaleCohomology

end
