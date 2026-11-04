module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ModuleStalkFunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleStalkExactness

/-!
# Geometric stalks of sheaves of modules on the small étale site detect isomorphisms

Let `X` be an algebraic space over a scheme `S` and let `R` be an arbitrary sheaf of rings on
`X_étale`. Every geometric point `x` of `X` is a point of the small étale site (Stacks 04K0),
so it has a stalk functor on sheaves of `R`-modules; this file names that functor and proves
that the family of them, over all geometric points of `X`, detects isomorphisms,
monomorphisms and epimorphisms of sheaves of `R`-modules.

## Main definitions

* `AlgebraicGeometry.Space.geometricModuleStalkFunctor`: the stalk functor at a geometric
  point on sheaves of modules over an arbitrary sheaf of rings on the small étale site.

## Main results

* `AlgebraicGeometry.Space.isIso_of_isIso_geometricModuleStalk`,
  `AlgebraicGeometry.Space.mono_of_mono_geometricModuleStalk` and
  `AlgebraicGeometry.Space.epi_of_epi_geometricModuleStalk`: a map of sheaves of `R`-modules
  which is invertible, a monomorphism, respectively an epimorphism on the stalk at every
  geometric point is invertible, a monomorphism, respectively an epimorphism.

## Implementation notes

`AlgebraicGeometry.Space.geometricModuleStalk` is the stalk of a sheaf of modules over the
*structure* sheaf of an algebraic space, read as a module over the étale local ring, and it is
an object map only. What is needed to check a map of sheaves of modules on stalks is a functor,
and over an arbitrary sheaf of rings rather than the structure sheaf — Stacks 04G0 and 0DK4
quantify over two arbitrary sheaves of rings. Both are supplied by `Stacks.sheafModuleFiber` at
the point of the site attached to the geometric point, which is what is named here; nothing is
constructed in this file.

The three results are `Stacks.isIso_of_isIso_sheafModuleFiber` and its two relatives fed with
`AlgebraicGeometry.Space.isConservativeFamilyOfPoints_etaleSitePoint`, the conservativity of the
family of geometric points. That conservativity is the "`X_étale` has enough points" consequence
of Stacks 04K5; passing from it to sheaves of modules is the content of
`Stacks.isIso_of_isIso_sheafModuleFiber`, which reduces an isomorphism of sheaves of modules to
one of the underlying sheaves of abelian groups.

The sheaf of rings and the sheaves of modules are at universe `u`, that of the sections of the
structure sheaf of the small étale ringed topos of Stacks 03G8, while the objects of the site
are in `Type (u + 1)`; the points of Stacks 04K0 are points relative to `Type u`, so the three
universes match without a lift. This is the universe at which the module development of this
tree runs.

Deliberately untagged. The source does not state these separately: they are the module-sheaf
form of the "enough points" consequence of Theorem 04K5, exactly as
`AlgebraicGeometry.Space.hasConservativeFamily_smallEtale` is its sheaf-of-sets form, and the
theorem's own clauses are proved in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleStalkExactness.lean`.

## References

* [Stacks Project, Tag 04K0](https://stacks.math.columbia.edu/tag/04K0)
* [Stacks Project, Tag 04K5](https://stacks.math.columbia.edu/tag/04K5)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hX : IsAlgebraicSpace B S hS X)
    (R : Sheaf (SmallEtale.topology B S hS X) RingCat.{u})

/-- **The stalk functor at a geometric point on sheaves of modules.** For an arbitrary sheaf of
rings `R` on the small étale site of an algebraic space `X` and a geometric point `x` of `X`,
the stalk at the point of the site of Stacks 04K0 determined by `x`, as a functor from sheaves
of `R`-modules to modules over the stalk of `R`.

`AlgebraicGeometry.Space.geometricModuleStalk` is the same construction for the structure sheaf
in place of `R`, read as a module over the étale local ring, and only objectwise. -/
noncomputable abbrev geometricModuleStalkFunctor (x : GeometricPoint B S hS X) :
    SheafOfModules.{u} R ⥤
      ModuleCat.{u} (((etaleSitePoint B S hS X x hX).presheafFiber
        (A := RingCat.{u})).obj R.obj) :=
  Stacks.sheafModuleFiber (etaleSitePoint B S hS X x hX) R

/-- **Geometric stalks detect isomorphisms of sheaves of modules.** A map of sheaves of modules
over an arbitrary sheaf of rings on the small étale site of an algebraic space which is
invertible on the stalk at every geometric point is invertible.

This is the module-sheaf form of the "enough points" consequence of Stacks 04K5, which for
sheaves of sets is `AlgebraicGeometry.Space.hasConservativeFamily_smallEtale`. It is the step
with which the source's stalkwise proofs of Stacks 04G0 and 0DK4 begin. -/
theorem isIso_of_isIso_geometricModuleStalk {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (hf : ∀ x : GeometricPoint B S hS X,
      IsIso ((geometricModuleStalkFunctor B S hS X hX R x).map f)) :
    IsIso f := by
  refine Stacks.isIso_of_isIso_sheafModuleFiber R
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS X hX) f ?_
  rintro ⟨Φ, hΦ⟩
  obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
  exact hf x

/-- **Geometric stalks detect monomorphisms of sheaves of modules.** -/
theorem mono_of_mono_geometricModuleStalk {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (hf : ∀ x : GeometricPoint B S hS X,
      Mono ((geometricModuleStalkFunctor B S hS X hX R x).map f)) :
    Mono f := by
  refine Stacks.mono_of_mono_sheafModuleFiber R
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS X hX) f ?_
  rintro ⟨Φ, hΦ⟩
  obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
  exact hf x

/-- **Geometric stalks detect epimorphisms of sheaves of modules.** -/
theorem epi_of_epi_geometricModuleStalk {M N : SheafOfModules.{u} R} (f : M ⟶ N)
    (hf : ∀ x : GeometricPoint B S hS X,
      Epi ((geometricModuleStalkFunctor B S hS X hX R x).map f)) :
    Epi f := by
  refine Stacks.epi_of_epi_sheafModuleFiber R
    (isConservativeFamilyOfPoints_etaleSitePoint B S hS X hX) f ?_
  rintro ⟨Φ, hΦ⟩
  obtain ⟨x, rfl⟩ := (ObjectProperty.ofObj_iff _ Φ).1 hΦ
  exact hf x

end AlgebraicGeometry.Space

end
