module

public import Mathlib.CategoryTheory.Adjunction.Additive
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor

/-!
# Additivity of the stalk functor at a point of a site

The stalk at a point of a site, of a presheaf or sheaf of modules over the stalk of the
sheaf of rings, is an additive functor.

This is the one instance that stands between the functors of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor` and the *stalk complex* of
a complex of sheaves of modules: `HomologicalComplex.mapHomologicalComplex` needs
`PreservesZeroMorphisms`, and without it the degreewise stalk of a cochain complex cannot be
formed, so neither side of the stalk criterion for K-flatness (Stacks 0DEN) can be written
down at all. `Additive` is the stronger statement and is what is proved here;
`PreservesZeroMorphisms` follows from it by `Functor.additive_preservesZeroMorphisms`.

## Main results

* `Stacks.additive_presheafModuleFiber`, `Stacks.additive_sheafModuleFiber`,
  `Stacks.additive_sheafModuleFiberOfCommRing`: the three stalk functors are additive.

## Implementation notes

**Neither Mathlib route from exactness applies, and this is not a near miss.**
`Stacks.instPreservesFiniteLimitsPresheafModuleFiber` is already available, and preserving
finite limits is morally much stronger than additivity, so the expected proof is
`Functor.additive_of_preserves_binary_products`. That does not work: both it and
`Functor.additive_of_preservesBinaryBiproducts` take `[F.PreservesZeroMorphisms]` as a
*hypothesis*, so each would need the very thing being proved. Preservation of finite limits
therefore does not give additivity here, and no amount of exactness in that file does.

The proof instead goes through the definition. `presheafModuleFiber` is
`PresheafOfModules.pushforward (𝟙 _) ⋙ PresheafOfModules.colimitFunctor …`, and each factor
is additive for a different reason:

* the pushforward along `CategoryOfElements.π Φ.fiber` is precomposition with that functor's
  opposite on underlying presheaves, so `map_add` holds by `rfl`;
* `colimitFunctor` is a left adjoint, by `PresheafOfModules.colimitAdjunction`, so it is
  additive as soon as its right adjoint `PresheafOfModules.constFunctor` is — and that one is
  restriction of scalars into a constant presheaf, whose `map_add` is again `rfl`.

`constFunctor`'s additivity is supplied with `haveI` rather than as a global instance: it is
needed only to run `Adjunction.left_adjoint_additive`, and seating it globally would put an
instance keyed on `constFunctor` into search for every client of this file.

The commutative-ring form composes the `RingCat` one with `ModuleCat.restrictScalars` along
`commRingSheafFiberIso`, which is additive already.

## References

* [Stacks Project, Tag 04EQ](https://stacks.math.columbia.edu/tag/04EQ)
* [Stacks Project, Tag 0DEN](https://stacks.math.columbia.edu/tag/0DEN)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe w v u

namespace Stacks

variable {C : Type u} [Category.{v} C] [LocallySmall.{w} C]
  {J : GrothendieckTopology C}

/-- Pushforward of presheaves of modules along the projection from the category of
neighbourhoods of a point is additive: on underlying presheaves it is precomposition. -/
instance additive_pushforward_pi (Φ : J.Point.{w}) (R : Cᵒᵖ ⥤ RingCat.{w}) :
    (PresheafOfModules.pushforward.{w}
      (F := CategoryOfElements.π Φ.fiber) (R := R) (𝟙 _)).Additive where
  map_add := by intros; rfl

/-- The colimit-module functor is additive, being a left adjoint of the constant-presheaf
functor. -/
instance additive_colimitFunctor (Φ : J.Point.{w}) (R : Cᵒᵖ ⥤ RingCat.{w}) :
    (PresheafOfModules.colimitFunctor
      (Φ.isColimitPresheafFiberCocone (A := RingCat.{w}) R)).Additive :=
  haveI : (PresheafOfModules.constFunctor.{w}
      (Φ.presheafFiberCocone (A := RingCat.{w}) R)).Additive := ⟨by intros; rfl⟩
  Adjunction.left_adjoint_additive (PresheafOfModules.colimitAdjunction _)

/-- A composite of additive functors is additive. `Mathlib/CategoryTheory/Preadditive/
StacksCore/CategoryTheory/Preadditive/AdditiveFunctor.lean` carries the converse directions — additivity of a factor deduced from
additivity of the composite — but not this one, in any form, so the composites below cannot
be closed by `infer_instance` without it. -/
instance additive_comp {C₁ C₂ C₃ : Type*} [Category C₁] [Category C₂] [Category C₃]
    [Preadditive C₁] [Preadditive C₂] [Preadditive C₃]
    (F : C₁ ⥤ C₂) (G : C₂ ⥤ C₃) [F.Additive] [G.Additive] : (F ⋙ G).Additive where
  map_add := by
    intros
    dsimp only [Functor.comp_map]
    rw [F.map_add, G.map_add]

/-- The stalk of a presheaf of modules at a point of a site is an additive functor. -/
instance additive_presheafModuleFiber (Φ : J.Point.{w}) (R : Cᵒᵖ ⥤ RingCat.{w}) :
    (presheafModuleFiber Φ R).Additive :=
  inferInstanceAs (PresheafOfModules.pushforward.{w}
      (F := CategoryOfElements.π Φ.fiber) (R := R) (𝟙 _) ⋙
    PresheafOfModules.colimitFunctor
      (Φ.isColimitPresheafFiberCocone (A := RingCat.{w}) R)).Additive

/-- The stalk of a sheaf of modules at a point of a site is an additive functor. -/
instance additive_sheafModuleFiber (Φ : J.Point.{w}) (R : Sheaf J RingCat.{w}) :
    (sheafModuleFiber Φ R).Additive :=
  inferInstanceAs (SheafOfModules.forget R ⋙ presheafModuleFiber Φ R.obj).Additive

/-- The stalk of a sheaf of modules over the ring sheaf of a sheaf of commutative rings,
read over the `CommRingCat`-valued stalk, is an additive functor. This is the form the stalk
criterion for K-flatness is stated in, `CochainComplex.KFlat` requiring a commutative base
ring. -/
instance additive_sheafModuleFiberOfCommRing (Φ : J.Point.{w}) (O : Sheaf J CommRingCat.{w})
    [J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})] :
    (sheafModuleFiberOfCommRing Φ O).Additive :=
  inferInstanceAs (sheafModuleFiber Φ (commRingSheafToRingSheaf O) ⋙
    ModuleCat.restrictScalars.{w} (commRingSheafFiberIso Φ O).inv.hom).Additive

end Stacks

end
