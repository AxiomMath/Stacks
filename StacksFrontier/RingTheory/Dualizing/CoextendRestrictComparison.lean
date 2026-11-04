module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.Ext.Basic
public import StacksFrontier.RingTheory.Dualizing.DerivedHomFinite
public import StacksFrontier.RingTheory.Dualizing.TrivialDuality
public import StacksFrontier.RingTheory.Dualizing.TrivialDualityRing.Basic

/-!
# Derived Hom along a ring map, after restriction of scalars

Let `f : A →+* B` be a homomorphism of commutative rings.  Coextension of scalars
`Hom_A(B, -) : Mod(A) ⥤ Mod(B)` has a total right derived functor `RHom(B, -) : D(A) ⥤ D(B)`,
and composing it with restriction of scalars `D(B) ⥤ D(A)` computes the `A`-valued derived Hom
functor `RHom_A(B, -) : D(A) ⥤ D(A)`.  This is the first half of Tag 0A71.

The comparison is not merely an isomorphism of functors: it is *the* isomorphism compatible with
the two structural natural transformations exhibiting the two sides as right derived functors,
and as such it is unique.  The proof is the uniqueness of left Kan extensions along the
localization `K(A) ⥤ D(A)`: the natural transformation descending the restricted unit is an
isomorphism because at a K-injective complex `I` both units are isomorphisms — both sides are
then computed by the complex `Hom_A(B, I)` — and every object of `D(A)` is the image of a
K-injective complex.  In particular the composite agrees with the identity of `Hom_A(B, I)` on
K-injective complexes, which is the content of the source's proof.

Everything is stated for an arbitrary model of the two derived categories, that is for arbitrary
`HasDerivedCategory` instances with independent morphism universes, and for an arbitrary right
derived functor presented by its universal property rather than for a chosen construction.

The two functors out of `K(Mod A)` whose right derived functors are compared
(`Dualizing.coextendScalarsToDerivedCategory`, `Dualizing.homAlongToDerivedCategory`), the
structural transformation `Dualizing.restrictedDerivedUnit`, the single-complex unit
`Dualizing.coextendSingleUnit`, the interface `Dualizing.HomologyExtComparison` for the second
half of Tag 0A71, and the comparison
`Dualizing.derivedCoextendScalarsCompDerivedRestrictScalarsIso` itself — Tag 0A71 — are in
`StacksFrontier/RingTheory/Dualizing/TrivialDualityRing/Basic.lean`, which this module imports.

The remaining assumed functor, derived coextension itself, is discharged in
`StacksFrontier/RingTheory/Dualizing/CoextendRestrictComparison/Constructed.lean`: instantiating
`Dualizing.restrictDerivedCoextendIsoDerivedHomAlong` at `Dualizing.AnyModel.derivedHom` with
its total-derived unit gives Tag 0A71 with nothing assumed.

## Main definitions

* `Dualizing.derivedHomAlong` — the canonical total right derived functor of
  `homAlongToDerivedCategory f`, i.e. `RHom_A(B, -) : D(A) ⥤ D(A)`, with its structural
  transformation `Dualizing.derivedHomAlongUnit`.

## Main results

* `Dualizing.restrictDerivedCoextendIsoDerivedHomAlong` — Tag 0A71's comparison against the
  canonical derived functor `Dualizing.derivedHomAlong`.
* `Dualizing.isIso_rightDerivedUnit_app_of_isKInjective` — a K-injective complex computes any
  right derived functor out of `K(Mod A)`, in any model of `D(Mod A)`.

## References

* [Stacks Project, Tag 0A70](https://stacks.math.columbia.edu/tag/0A70)
* [Stacks Project, Tag 0A71](https://stacks.math.columbia.edu/tag/0A71)
-/

@[expose] public section

open CategoryTheory

universe u v wA wB

namespace Dualizing

noncomputable section

section Resolutions

variable {A : Type u} [CommRing A]

/-- Every cochain complex of `A`-modules admits a quasi-isomorphism towards a K-injective
complex: the category of `A`-modules has enough injectives. -/
theorem exists_quasiIso_isKInjective_moduleCat
    (K : CochainComplex (ModuleCat.{max v u} A) ℤ) :
    ∃ (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (g : K ⟶ I), I.IsKInjective ∧ QuasiIso g := by
  let : EnoughInjectives (ModuleCat.{max v u} A) := ModuleCat.enoughInjectives A
  obtain ⟨I, g, hg, hI⟩ := CochainComplex.exists_quasiIso_isKInjective K
  exact ⟨I, g, hI, hg⟩

end Resolutions

variable {A B : Type u} [CommRing A] [CommRing B]
  [HasDerivedCategory.{wA} (ModuleCat.{max v u} A)]
  [HasDerivedCategory.{wB} (ModuleCat.{max v u} B)]

/-- **Stacks 070Y** for complexes of modules: a K-injective complex computes any right derived
functor out of the homotopy category of `A`-modules, so the structural map is an isomorphism
there. This is the form of the statement used below for both the derived coextension functor
and the derived `A`-valued Hom functor.  Unlike `Dualizing.isIso_app_of_isKInjective` it is
stated for an arbitrary model of the derived category of `A`-modules and for an arbitrary
functor out of the homotopy category, not only for coextension of scalars. -/
theorem isIso_rightDerivedUnit_app_of_isKInjective {H : Type*} [Category H]
    (F : HomotopyCategory (ModuleCat.{max v u} A) (.up ℤ) ⥤ H)
    (RG : DerivedCategory (ModuleCat.{max v u} A) ⥤ H)
    (γ : F ⟶ DerivedCategory.Qh ⋙ RG)
    [RG.IsRightDerivedFunctor γ (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))]
    (I : CochainComplex (ModuleCat.{max v u} A) ℤ) (hI : I.IsKInjective) :
    IsIso (γ.app ((HomotopyCategory.quotient _ _).obj I)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective F
    (exists_quasiIso_isKInjective_moduleCat.{u, v})).2 DerivedCategory.Qh RG γ I hI

/-- Module complexes admit K-injective resolutions, so the derived `A`-valued Hom functor
exists in any chosen model of the derived category of `A`-modules. -/
instance homAlongToDerivedCategory_hasPointwiseRightDerivedFunctor (f : A →+* B) :
    (homAlongToDerivedCategory.{u, v, wA} f).HasPointwiseRightDerivedFunctor
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ)) :=
  (Functor.hasPointwiseRightDerivedFunctor_and_isIso_app_of_exists_quasiIso_isKInjective.{
      max v u, wA, max v u, max (u + 1) (v + 1), max (u + 1) (v + 1),
      max (u + 1) (v + 1)}
    (homAlongToDerivedCategory.{u, v, wA} f) (exists_quasiIso_isKInjective_moduleCat.{u, v})).1

/-- The derived `A`-valued Hom functor `RHom_A(B, -) : D(A) ⥤ D(A)` along a ring homomorphism
`f : A →+* B`, as the total right derived functor of `Hom_A(B, -)` viewed as a functor to
`A`-modules.  It is the target of the comparison of Tag 0A71. -/
def derivedHomAlong (f : A →+* B) :
    DerivedCategory (ModuleCat.{max v u} A) ⥤ DerivedCategory (ModuleCat.{max v u} A) :=
  (homAlongToDerivedCategory.{u, v, wA} f).totalRightDerived DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))

/-- The structural transformation exhibiting `Dualizing.derivedHomAlong f` as a right derived
functor of `Hom_A(B, -)`. -/
def derivedHomAlongUnit (f : A →+* B) :
    homAlongToDerivedCategory.{u, v, wA} f ⟶
      DerivedCategory.Qh ⋙ derivedHomAlong.{u, v, wA} f :=
  (homAlongToDerivedCategory.{u, v, wA} f).totalRightDerivedUnit DerivedCategory.Qh
    (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))

/-- `Dualizing.derivedHomAlong f` is a right derived functor of `Hom_A(B, -)` for the
transformation `Dualizing.derivedHomAlongUnit f`, by construction as a total right derived
functor. -/
instance derivedHomAlong_isRightDerivedFunctor (f : A →+* B) :
    (derivedHomAlong.{u, v, wA} f).IsRightDerivedFunctor (derivedHomAlongUnit.{u, v, wA} f)
      (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ)) := by
  dsimp [derivedHomAlong, derivedHomAlongUnit]
  infer_instance

variable (f : A →+* B)
  (RF : DerivedCategory (ModuleCat.{max v u} A) ⥤
    DerivedCategory (ModuleCat.{max v u} B))
  (α : coextendScalarsToDerivedCategory f ⟶ DerivedCategory.Qh ⋙ RF)

/-- Tag 0A71 against the canonical derived functor: restricting any right derived functor of
coextension of scalars to `D(A)` is `Dualizing.derivedHomAlong f`, by the unique isomorphism
compatible with the derived units.  This is the form in which the comparison is used from
outside. -/
def restrictDerivedCoextendIsoDerivedHomAlong
    [RF.IsRightDerivedFunctor α (HomotopyCategory.quasiIso (ModuleCat.{max v u} A) (.up ℤ))] :
    { e : RF ⋙ (ModuleCat.restrictScalars.{max v u} f).mapDerivedCategory ≅
        derivedHomAlong.{u, v, wA} f //
      restrictedDerivedUnit f RF α ≫ Functor.whiskerLeft DerivedCategory.Qh e.hom =
        derivedHomAlongUnit.{u, v, wA} f } :=
  derivedCoextendScalarsCompDerivedRestrictScalarsIso f RF α _ (derivedHomAlongUnit f)

end

end Dualizing

end
