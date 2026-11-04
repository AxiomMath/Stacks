module

public import StacksFrontier.AlgebraicGeometry.Spaces.Decent.PrimeDivisorHenselianSpecMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.MeromorphicSectionCanonicalValue

/-!
# The meromorphic sections of `ℒ_ξ` at the generic point of a prime divisor

Let `X` be a decent algebraic space over `S` and let `Z ⊆ X` be a prime divisor with generic
point `ξ`.  The canonical morphism `c_ξ : Spec(𝒪^h_{X, ξ}) ⟶ X` of Stacks 0ENK pulls an
`𝒪_X`-module `ℒ` back to `ℒ_ξ = c_ξ^*ℒ`, whose module of sections
`AlgebraicGeometry.Space.PrimeDivisor.genericModuleStalk` is an `𝒪^h_{X, ξ}`-module.  Section
72.7 of the source reads the ratio `s / s_ξ` of a meromorphic section `s` of `ℒ` against a
generator `s_ξ` of `ℒ_ξ` inside the *meromorphic* sections of `ℒ_ξ` on `Spec(𝒪^h_{X, ξ})`, and
the first of the two collections of Stacks 0EPS is the set of prime divisors at whose generic
point `s` fails to lie in `ℒ_ξ` — that is, outside the image of the canonical map

`ℒ_ξ ⟶ 𝒦_X(ℒ)_ξ`.

This file builds that map.  Its target is the first `|X|`-indexed, *module*-valued meromorphic
stalk in the library: `AlgebraicGeometry.Space.meromorphicStalk` is indexed by a geometric point
and valued in rings, and the étale local ring at a geometric point above `ξ` is a *strict*
henselization of `𝒪^h_{X, ξ}` rather than `𝒪^h_{X, ξ}` itself, so it answers a different
question.  Here the point is `ξ ∈ |X|` throughout, carried by the prime divisor, and the module
is read on `Spec(𝒪^h_{X, ξ})` itself, exactly as the source reads it.

## Main definitions

* `AlgebraicGeometry.Space.PrimeDivisor.genericToMeromorphicFunctions` is the structure map
  `𝒪^h_{X, ξ} ⟶ 𝒦(Spec(𝒪^h_{X, ξ}))` into the meromorphic functions, read over the identity
  étale chart of `Spec(𝒪^h_{X, ξ})`.
* `AlgebraicGeometry.Space.PrimeDivisor.genericMeromorphicModuleStalk` is `𝒦_X(ℒ)_ξ`, the
  meromorphic sections of `ℒ_ξ` on `Spec(𝒪^h_{X, ξ})`, as an `𝒪^h_{X, ξ}`-module.
* `AlgebraicGeometry.Space.PrimeDivisor.genericModuleStalkToMeromorphic` is the comparison
  `ℒ_ξ ⟶ 𝒦_X(ℒ)_ξ`, as a map of `𝒪^h_{X, ξ}`-modules.

## Main results

* `AlgebraicGeometry.Space.PrimeDivisor.genericModuleStalkToMeromorphic_apply` reads the
  comparison off as the canonical map of
  `AlgebraicGeometry.Space.toMeromorphicSectionValue` over the identity étale chart.

## Implementation notes

As in `AlgebraicGeometry.Space.PrimeDivisor.genericHenselianPullback`, the henselian local ring
is carried as an abstract henselization `R` in `Type u` of the Zariski local ring of the generic
chart at its distinguished point, together with its containment `hR` in the chosen big site:
`AlgebraicGeometry.Space.henselianLocalRing` is a `CommRingCat.{u + 1}` and its spectrum is not
an object of the site.

The module `ℒ` ranges over `Modules.{u, u}`, not over the `Modules.{u, max u z}` of the order of
vanishing and of the Weil divisor of a meromorphic section: the pullback of modules
`AlgebraicGeometry.Space.modulePullback` of Stacks 03LU exists only at the module universe of
the structure rings, for the reason recorded in
`StacksFrontier/AlgebraicGeometry/Spaces/SmallEtaleModulePullback.lean`, and so therefore does
`c_ξ^*ℒ`.  The two generalities agree at `z := u`, which is where this comparison and the
carriers of Stacks 0EPR meet.

The two sides live in different universes — `ℒ_ξ` has its sections in `Type u` and `𝒦_X(ℒ)_ξ`
in `Type (u + 1)`, sheafification on the small étale site raising the universe — so the
comparison is a bundled `LinearMap` rather than a morphism of `ModuleCat R`.

## References

* [Stacks Project, Tag 0ENK](https://stacks.math.columbia.edu/tag/0ENK)
* [Stacks Project, Tag 0ENV](https://stacks.math.columbia.edu/tag/0ENV)
* [Stacks Project, Tag 0EPR](https://stacks.math.columbia.edu/tag/0EPR)
* [Stacks Project, Tag 0EPS](https://stacks.math.columbia.edu/tag/0EPS)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] pointTopology

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hX : IsAlgebraicSpace B S hS X)
    (hdec : IsDecentSpace B S hS X) (Z : PrimeDivisor B S hS X)

section Generic

variable (R : Type u) [CommRing R] [IsLocalRing R]
  [Algebra ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
    (Z.genericChart B S hS hX hdec).point) R]
  [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R]
  (hR : B.Contains (Spec (.of R)))

/-- The identity étale chart of `Spec(𝒪^h_{X, ξ})`, over which the sections of `ℒ_ξ` and of its
sheaf of meromorphic sections are read. -/
abbrev PrimeDivisor.genericHenselianChart :
    SmallEtale B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj :=
  idEtaleChart B S hS ((Z.genericChart B S hS hX hdec).henselianObj R hR)

/-- **The structure map `𝒪^h_{X, ξ} ⟶ 𝒦(Spec(𝒪^h_{X, ξ}))`** into the meromorphic functions of
`Spec(𝒪^h_{X, ξ})`, read over the identity étale chart: the sections of the structure sheaf
there are `Γ(Spec(𝒪^h_{X, ξ})) ≅ 𝒪^h_{X, ξ}`, and the map is the canonical `𝒪 ⟶ 𝒦` of Stacks
0EN3 after that isomorphism. -/
def PrimeDivisor.genericToMeromorphicFunctions : R →+*
    ((Stacks.SheafOfModules.Tensor.ringSheaf
        (meromorphicRingedSite B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj
          (Z.genericHenselianSpace B S hS hX hdec R hR).property).O).obj.obj
      (op (Z.genericHenselianChart B S hS hX hdec R hR))) :=
  ((toMeromorphicFunctionSheaf B S hS (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property).hom.app
      (op (Z.genericHenselianChart B S hS hX hdec R hR))).hom.comp
    (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom

/-- **`𝒦_X(ℒ)_ξ`, the meromorphic sections of `ℒ_ξ` at the generic point of a prime divisor**:
the sections of the sheaf `𝒦(ℒ_ξ)` of meromorphic sections of Stacks 0EN5 over the identity
étale chart of `Spec(𝒪^h_{X, ξ})`, as an `𝒪^h_{X, ξ}`-module by restriction of scalars along
`AlgebraicGeometry.Space.PrimeDivisor.genericToMeromorphicFunctions`.

This is the module in which Section 72.7 of the source reads the ratio `s / s_ξ`, and inside
which the first collection of Stacks 0EPS asks whether `s` lies in `ℒ_ξ`. -/
def PrimeDivisor.genericMeromorphicModuleStalk (L : Modules.{u, u} B S hS X hX) :
    ModuleCat.{u + 1} R :=
  (ModuleCat.restrictScalars (Z.genericToMeromorphicFunctions B S hS hX hdec R hR)).obj
    ((meromorphicSectionSheaf.{u, u} B S hS
        (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property
        (Z.genericHenselianPullback B S hS hX hdec R hR L)).val.obj
      (op (Z.genericHenselianChart B S hS hX hdec R hR)))

/-- **The comparison `ℒ_ξ ⟶ 𝒦_X(ℒ)_ξ`** at the generic point of a prime divisor: a section of
`ℒ_ξ = c_ξ^*ℒ` on `Spec(𝒪^h_{X, ξ})` is a meromorphic section of `ℒ_ξ` there, by the canonical
map `ℒ_ξ ⟶ 𝒦(ℒ_ξ)` of `AlgebraicGeometry.Space.toMeromorphicSectionValue` over the identity
étale chart.

Its image is `ℒ_ξ` as a submodule of the meromorphic sections, which is what the first
collection of Stacks 0EPS asks a meromorphic section to lie outside of. -/
def PrimeDivisor.genericModuleStalkToMeromorphic (L : Modules.{u, u} B S hS X hX) :
    Z.genericModuleStalk B S hS hX hdec R hR L →ₗ[R]
      Z.genericMeromorphicModuleStalk B S hS hX hdec R hR L where
  toFun m := toMeromorphicSectionValue B S hS
    (Z.genericHenselianSpace B S hS hX hdec R hR).obj
    (Z.genericHenselianSpace B S hS hX hdec R hR).property
    (Z.genericHenselianPullback B S hS hX hdec R hR L)
    (Z.genericHenselianChart B S hS hX hdec R hR) m
  map_add' m m' := toMeromorphicSectionValue_add B S hS
    (Z.genericHenselianSpace B S hS hX hdec R hR).obj
    (Z.genericHenselianSpace B S hS hX hdec R hR).property
    (Z.genericHenselianPullback B S hS hX hdec R hR L)
    (Z.genericHenselianChart B S hS hX hdec R hR) m m'
  map_smul' r m := toMeromorphicSectionValue_smul B S hS
    (Z.genericHenselianSpace B S hS hX hdec R hR).obj
    (Z.genericHenselianSpace B S hS hX hdec R hR).property
    (Z.genericHenselianPullback B S hS hX hdec R hR L)
    (Z.genericHenselianChart B S hS hX hdec R hR)
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom r) m
    (Z.genericToMeromorphicFunctions B S hS hX hdec R hR r) rfl

omit [IsLocalRing R]
  [IsLocalRing.IsHenselization
    ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
      (Z.genericChart B S hS hX hdec).point)
    (IsLocalRing.ResidueField
      ((Z.genericChart B S hS hX hdec).scheme.left.1.presheaf.stalk
        (Z.genericChart B S hS hX hdec).point)) R] in
/-- The comparison `ℒ_ξ ⟶ 𝒦_X(ℒ)_ξ` is the canonical map `ℒ_ξ ⟶ 𝒦(ℒ_ξ)` over the identity
étale chart of `Spec(𝒪^h_{X, ξ})`. -/
@[simp]
theorem PrimeDivisor.genericModuleStalkToMeromorphic_apply (L : Modules.{u, u} B S hS X hX)
    (m : Z.genericModuleStalk B S hS hX hdec R hR L) :
    Z.genericModuleStalkToMeromorphic B S hS hX hdec R hR L m =
      toMeromorphicSectionValue B S hS
        (Z.genericHenselianSpace B S hS hX hdec R hR).obj
        (Z.genericHenselianSpace B S hS hX hdec R hR).property
        (Z.genericHenselianPullback B S hS hX hdec R hR L)
        (Z.genericHenselianChart B S hS hX hdec R hR) m :=
  rfl

end Generic

end AlgebraicGeometry.Space

end
