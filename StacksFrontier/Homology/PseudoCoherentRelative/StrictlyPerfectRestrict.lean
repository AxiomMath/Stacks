module

public import StacksFrontier.Algebra.Homology.StrictlyPerfectApproximationLocal
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.StructureSheafSpelling
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentIso
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.PseudoCoherentTriangle
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.RestrictExact
public import StacksFrontier.AlgebraicGeometry.PseudoCoherent.TriangleLemmas
public import StacksFrontier.Homology.PseudoCoherentRelative.TildeOpenImmersion
public import StacksCore.Tactic.StacksAttribute

/-!
# Strict perfection travels along restriction to an open subscheme

`StrictlyPerfect.isStrictlyPerfect_map` says that an additive functor `OXMod X ⥤ OXMod Y`
matching the structure modules carries strictly perfect complexes (Stacks 08C4) to strictly
perfect complexes. This file specializes it to
`AlgebraicGeometry.Scheme.Modules.restrictFunctor` of an open immersion of schemes — in
particular of an *isomorphism* of schemes, which is the case needed to move a strictly perfect
approximation living on an open subscheme `D(g) ⊆ Spec R` over to one living on `Spec R_g`.

The two cohomological halves of a strictly perfect approximation travel the same way, and the
same spelling obstruction has to be cleared for them, so they are recorded here too.

## Main results

* `AlgebraicGeometry.Scheme.Modules.isStrictlyPerfect_restrictFunctor`: restriction along an
  open immersion of schemes preserves strict perfection.
* `AlgebraicGeometry.Scheme.Modules.isIso_homologyMap_restrictFunctor` and
  `AlgebraicGeometry.Scheme.Modules.epi_homologyMap_restrictFunctor`: restriction along an open
  immersion preserves being an isomorphism, resp. an epimorphism, on cohomology.

## Implementation notes

**No preservation of biproducts is needed**, and `StrictlyPerfect.isStrictlyPerfect_map` asks
only for additivity. This matters because it is exactly the biproduct instances that the
`AlgebraicGeometry.Scheme.Modules` / `AlgebraicGeometry.SheafOfModules` wall obstructs:
`CategoryTheory.Limits.HasFiniteBiproducts` of a category of sheaves of modules is available in
this development only for the two *concrete* spellings `Stacks.StrictlyPerfect.OXMod X` and
`AlgebraicGeometry.Scheme.Modules X`, never for a variable sheaf of rings, so a version of this
transport stated for a functor between variable `AlgebraicGeometry.SheafOfModules` categories
would have to carry the two `HasFiniteBiproducts` instances as hypotheses. Stating it for
`Stacks.StrictlyPerfect.OXMod` of two ringed spaces keeps every instance synthesis inside the
proof, where it succeeds.

The specialization to `AlgebraicGeometry.Scheme.Modules.restrictFunctor` is the crossing point
between the two spellings. `Stacks.StrictlyPerfect.OXMod X.toRingedSpace` and
`AlgebraicGeometry.Scheme.Modules X` are the same type with the same instances
(`Stacks.DerivedQCoh.oxMod_eq_sheafOfModules` is `rfl`), but
`Stacks.StrictlyPerfect.structureSheafOfRings` is a semireducible `def` while
`AlgebraicGeometry.Scheme.ringCatSheaf` is an `abbrev`, so typeclass synthesis does not make the
step and `(AlgebraicGeometry.Scheme.Modules.restrictFunctor f).Additive` is not found once the
functor is retyped. The two instance arguments are therefore supplied as *terms*, through an
explicit `@`-application: a type ascription is checked at default transparency, where the two
spellings are interchangeable. Writing the functor as
`show OXMod Y.toRingedSpace ⥤ OXMod X.toRingedSpace from _` instead does *not* work, because the
resulting `have`-bound functor defeats the search for its own `Additive` instance.

That the restriction of the structure sheaf is the structure sheaf is Mathlib's
`AlgebraicGeometry.Scheme.Modules.restrictUnitIso`.

The same `@`-application is what the two cohomological transports need, and there the obstructed
instances are the `CategoryTheory.Preadditive` arguments buried in
`CategoryTheory.Functor.Additive`: an instance declared for
`AlgebraicGeometry.Scheme.Modules X` carries that spelling's `Preadditive` instance in its own
statement, so matching it against a goal phrased with the `Stacks.StrictlyPerfect.OXMod` one
compares two instance arguments at reducible transparency and fails, even though the functor
itself is spelled identically on both sides. Exactness of the restriction is
`AlgebraicGeometry.Scheme.Modules.restrictFunctor_preservesFiniteLimits` together with
left-adjointness.

## References

* [Stacks Project, Tag 08C4](https://stacks.math.columbia.edu/tag/08C4)
* [Stacks Project, Tag 08E7](https://stacks.math.columbia.edu/tag/08E7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Modules

open StrictlyPerfect

/-- **Strict perfection travels along restriction to an open subscheme.** If a complex of
`𝒪_Y`-modules is strictly perfect (Stacks 08C4) and `f : X ⟶ Y` is an open immersion of schemes,
then its restriction along `f` is a strictly perfect complex of `𝒪_X`-modules.

The case `f` an *isomorphism* is what identifies a strictly perfect approximation living on a
standard open `D(g)` of `Spec R` with one living on `Spec R_g`.

The additivity of the restriction is supplied as a *term*, because typeclass synthesis does not
cross between the `Stacks.StrictlyPerfect.OXMod` and `AlgebraicGeometry.Scheme.Modules` spellings
of the category of `𝒪`-modules. -/
theorem isStrictlyPerfect_restrictFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {E : CochainComplex (OXMod.{u, u} Y.toRingedSpace) ℤ} (hE : IsStrictlyPerfect E) :
    IsStrictlyPerfect (X := X.toRingedSpace)
      (((restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).obj E) :=
  @isStrictlyPerfect_map Y.toRingedSpace X.toRingedSpace (restrictFunctor f)
    (additive_restrictFunctor f) (restrictUnitIso f) E hE

/-- Restriction along an open immersion of schemes preserves being an isomorphism on cohomology
in a given degree, because it is exact. Stated at the `Stacks.StrictlyPerfect.OXMod` spelling of
the category of `𝒪`-modules, where a strictly perfect approximation lives. -/
theorem isIso_homologyMap_restrictFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {P Q : CochainComplex (OXMod.{u, u} Y.toRingedSpace) ℤ} (β : P ⟶ Q) (j : ℤ)
    (h : IsIso (HomologicalComplex.homologyMap β j)) :
    IsIso (HomologicalComplex.homologyMap
      (((restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map β) j) :=
  @isIso_homologyMap_mapHomologicalComplex _ _ _ _ _ _ (restrictFunctor f)
    (additive_restrictFunctor f) (restrictFunctor_preservesFiniteLimits f)
    (inferInstance : PreservesFiniteColimits (restrictFunctor f)) P Q β j h

/-- Restriction along an open immersion of schemes preserves being an epimorphism on cohomology
in a given degree, because it is exact. -/
theorem epi_homologyMap_restrictFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {P Q : CochainComplex (OXMod.{u, u} Y.toRingedSpace) ℤ} (β : P ⟶ Q) (j : ℤ)
    (h : Epi (HomologicalComplex.homologyMap β j)) :
    Epi (HomologicalComplex.homologyMap
      (((restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map β) j) :=
  @epi_homologyMap_mapHomologicalComplex _ _ _ _ _ _ (restrictFunctor f)
    (additive_restrictFunctor f) (restrictFunctor_preservesFiniteLimits f)
    (inferInstance : PreservesFiniteColimits (restrictFunctor f)) P Q β j h

/-- **A strictly perfect approximation travels along restriction to an open subscheme.** If a
complex `A` of `𝒪_Y`-modules receives a morphism from a strictly perfect complex which is an
isomorphism on cohomology above `m` and an epimorphism in degree `m`, and the restriction of `A`
along an open immersion `f : X ⟶ Y` is identified with a complex `B` of `𝒪_X`-modules, then `B`
receives such a morphism from a strictly perfect complex of `𝒪_X`-modules.

The identification `e` is a hypothesis rather than something computed here, so that the complex
`B` stays an opaque variable: at the call site it is a complex built out of `Spec`, and matching
a written-out conclusion mentioning such a complex is what exhausts the elaboration budget in
this area. -/
theorem exists_approximation_restrictFunctor {X Y : Scheme.{u}} (f : X ⟶ Y) [IsOpenImmersion f]
    {A : CochainComplex (OXMod.{u, u} Y.toRingedSpace) ℤ}
    {B : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ}
    (e : ((restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).obj A ≅ B) (m : ℤ)
    {P : CochainComplex (OXMod.{u, u} Y.toRingedSpace) ℤ} (hP : IsStrictlyPerfect P) (α : P ⟶ A)
    (hα : ∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap α j))
    (hα₀ : Epi (HomologicalComplex.homologyMap α m)) :
    ∃ Q : CochainComplex (OXMod.{u, u} X.toRingedSpace) ℤ, IsStrictlyPerfect Q ∧
      ∃ β : Q ⟶ B, (∀ j : ℤ, m < j → IsIso (HomologicalComplex.homologyMap β j)) ∧
        Epi (HomologicalComplex.homologyMap β m) :=
  ⟨((restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).obj P,
    isStrictlyPerfect_restrictFunctor f hP,
    ((restrictFunctor f).mapHomologicalComplex (ComplexShape.up ℤ)).map α ≫ e.hom,
    fun j hj => isIso_homologyMap_comp _ _ j
      (isIso_homologyMap_restrictFunctor f α j (hα j hj)) (isIso_homologyMap_iso_hom e j),
    epi_homologyMap_comp _ _ m
      (epi_homologyMap_restrictFunctor f α m hα₀) (epi_homologyMap_iso_hom e m)⟩

end AlgebraicGeometry.Scheme.Modules

end
