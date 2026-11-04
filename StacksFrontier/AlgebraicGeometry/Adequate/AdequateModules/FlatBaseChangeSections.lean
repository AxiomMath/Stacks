module

public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateFunctors.BaseChange
public import StacksFrontier.AlgebraicGeometry.Adequate.AdequateModules.AffineLocal
public import StacksFrontier.AlgebraicGeometry.Descent.Module.AmitsurAcyclic

/-!
# The extended Čech complex of a flat surjection of affines, for an adequate module

Let `F` be an adequate sheaf of modules on the big `τ`-site over `S`. For a flat surjective
morphism `Spec A' → Spec A` of affines of the site over `S`, [Stacks, Tag 06VL] asserts that the
extended Čech complex
`0 → F(Spec A) → F(Spec A') → F(Spec (A' ⊗_A A')) → ⋯`
is exact. This module carries out the two steps of the source's proof.

## Main definitions

* `Stacks.Adequate.baseAlgebra` is `R` itself, viewed as an object of the category of
  `R`-algebras whose spectra have a given property `P`, and `Stacks.Adequate.baseAlgebraHom` is
  the structure morphism from it to an arbitrary such `R`-algebra.
  `Stacks.Adequate.baseAlgebraInSite` and `Stacks.Adequate.baseAlgebraInSiteHom` are the two of
  them for the source's category `Alg_A` of `A`-algebras whose spectra lie in the site, that is
  for the size condition of the site.
* `Stacks.Adequate.baseSections` is `F(Spec A)`, as an `A`-module.

## Main results

* `Stacks.Adequate.faithfullyFlat_of_flat_of_surjective_spec`: a flat ring map whose morphism of
  spectra is surjective is faithfully flat.
* `Stacks.Adequate.acyclic_amitsurExtendedCochainComplex_baseSections` is the second step: that
  extended Amitsur complex is exact, by [Stacks, Tag 023M].

The first step is
`Stacks.Adequate.bijective_affineSectionBaseChangeMap`, that the affine-section functor of an
adequate `F` commutes with flat base change along any morphism of `Alg_A`, together with its
specialization `Stacks.Adequate.bijective_affineSectionBaseChangeMap_base` to the structure
morphism of a flat `A`-algebra `C` of the site, `F(Spec C) = C ⊗_A F(Spec A)`; applied to
`C = A'`, `A' ⊗_A A'`, … the latter identifies every term of the extended Čech complex with
the corresponding term of the extended Amitsur complex of `A → A'` with coefficients
`F(Spec A)`. Both are stated in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/AffineLocalUnconditional.lean`, since
they are [Stacks, Tag 06VI] followed by [Stacks, Tag 06UW] and Tag 06VI lies above this module;
the definitions they are phrased with are the ones given here.

## Implementation notes

The scalars of a value of the affine-section functor are the ring supplied by
`AdequateFunctor.algebraRingDiagramOn`, whose carrier is that of `A` but which is not
syntactically `A`; `Stacks.Adequate.baseSections` is the value at the base algebra carrying the
`A`-module structure instead, and `Stacks.Adequate.baseSections_eq` records that the two have
the same carrier.

Likewise the source scalars of `AdequateFunctor.moduleValuedFunctorBaseChangeMap` come from the
`Algebra` structure induced by the morphism of `Alg_A` rather than from an ambient instance;
`Stacks.Adequate.algebraMap_baseAlgebraInSiteHom` records that for the structure morphism out of
`Stacks.Adequate.baseAlgebraInSite` that induced structure is the canonical one, which is what
lets flatness of `A → C` be hypothesized with the canonical instance.

The tag is split over a covering set of two declarations, one for each step of the source's
proof. Neither of them asserts the agreement of the Čech differentials with the differentials of
the Amitsur complex — the verification which the source of [Stacks, Tag 03FJ] omits and which
`Stacks.CechSite.conerveSectionsMap_naturality` carries out abstractly. That agreement is
supplied for the base-change maps used here by
`Stacks.Adequate.affineSectionBaseChangeMap_naturality`, in
`StacksFrontier/AlgebraicGeometry/Adequate/AdequateModules/CechAmitsurDifferentials.lean`: the
identifications of the terms commute with every transition map of the site algebras, hence carry
each coface map of the extended Čech complex to the corresponding coface map of the extended
Amitsur complex and each alternating sum to the other. What is still **not** asserted is the
source's final paragraph, deducing the fpqc sheaf condition from the exactness, for which the
source itself says "details omitted"; see the implementation notes of that module for the one
input it needs.

## References

* [Stacks Project, Tag 06VL](https://stacks.math.columbia.edu/tag/06VL)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory AdequateFunctor
open scoped TensorProduct

universe u m

namespace Stacks.Adequate

variable {τ : CoveringTopology} {S : Scheme.{u}}

/-! ### The base algebra as an object of `Alg_R` -/

/-- The ring `R` itself, as an object of the category of `R`-algebras whose spectra have the
property `P`. -/
public abbrev baseAlgebra {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R))) :
    AdequateFunctor.AlgebrasInSite R P :=
  ⟨CommAlgCat.of R R, hR⟩

/-- The structure morphism from `R` to an `R`-algebra whose spectrum has the property `P`. -/
public abbrev baseAlgebraHom {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    (Y : AdequateFunctor.AlgebrasInSite R P) :
    baseAlgebra P hR ⟶ Y :=
  ObjectProperty.homMk (CommAlgCat.ofHom (Algebra.ofId R Y.obj))

/-- The ring map underlying the structure morphism out of `R` is the algebra map of `Y`. -/
public theorem algebraMap_baseAlgebraHom {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    (Y : AdequateFunctor.AlgebrasInSite R P) :
    ((AdequateFunctor.siteAlgebraInclusion R P).map
        (baseAlgebraHom P hR Y)).hom.toRingHom = algebraMap R Y.obj :=
  rfl

/-- The structure morphism out of the base algebra is the only morphism out of it: composing it
with any morphism of the algebras of the property gives the structure morphism of the target. -/
public theorem baseAlgebraHom_comp {R : Type*} [CommRing R]
    (P : ObjectProperty Scheme) (hR : P (Spec (CommRingCat.of R)))
    {Y Z : AdequateFunctor.AlgebrasInSite R P} (f : Y ⟶ Z) :
    baseAlgebraHom P hR Y ≫ f = baseAlgebraHom P hR Z :=
  ObjectProperty.hom_ext _ (CommAlgCat.isInitialSelf.hom_ext _ _)

/-- The ring `A` itself, as an object of the category of `A`-algebras whose spectra belong to
the site: `Stacks.Adequate.baseAlgebra` for the size condition of the site. -/
public abbrev baseAlgebraInSite (B : BigSite τ S) (A : CommRingCat.{u})
    (hA : schemeSizeBelow B.cutoff (Spec A)) :
    AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff) :=
  baseAlgebra (schemeSizeBelow B.cutoff) hA

/-- The structure morphism from `A` to an `A`-algebra whose spectrum belongs to the site:
`Stacks.Adequate.baseAlgebraHom` for the size condition of the site. -/
public abbrev baseAlgebraInSiteHom (B : BigSite τ S) (A : CommRingCat.{u})
    (hA : schemeSizeBelow B.cutoff (Spec A))
    (C : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    baseAlgebraInSite B A hA ⟶ C :=
  baseAlgebraHom (schemeSizeBelow B.cutoff) hA C

/-- The ring map underlying the structure morphism out of `A` is the algebra map of `C`. -/
public theorem algebraMap_baseAlgebraInSiteHom (B : BigSite τ S) (A : CommRingCat.{u})
    (hA : schemeSizeBelow B.cutoff (Spec A))
    (C : AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff)) :
    ((AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff)).map
        (baseAlgebraInSiteHom B A hA C)).hom.toRingHom = algebraMap A C.obj :=
  algebraMap_baseAlgebraHom (schemeSizeBelow B.cutoff) hA C

/-- The sections of `F` over `Spec A`, as an `A`-module. -/
public noncomputable def baseSections (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (hA : schemeSizeBelow B.cutoff (Spec A)) :
    ModuleCat.{max u m} A :=
  letI X : (AdequateFunctor.AlgebrasInSite A (schemeSizeBelow B.cutoff))ᵒᵖᵒᵖ :=
    Opposite.op (Opposite.op (baseAlgebraInSite B A hA))
  letI : Module A ((affineSectionFunctor B F A f).obj X) :=
    inferInstanceAs (Module ((AdequateFunctor.algebraRingDiagramOn
      (AdequateFunctor.siteAlgebraInclusion A (schemeSizeBelow B.cutoff))).obj X)
      ((affineSectionFunctor B F A f).obj X))
  ModuleCat.of A ((affineSectionFunctor B F A f).obj X)

/-- `Stacks.Adequate.baseSections` is the value of the affine-section functor at the base
algebra. -/
public theorem baseSections_eq (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf)
    (A : CommRingCat.{u}) (f : Spec A ⟶ S)
    (hA : schemeSizeBelow B.cutoff (Spec A)) :
    (baseSections B F A f hA : Type (max u m)) =
      ((affineSectionFunctor B F A f).obj
        (Opposite.op (Opposite.op (baseAlgebraInSite B A hA))) : Type (max u m)) :=
  rfl

/-! ### Exactness of the extended Amitsur complex of the covering -/

/-- A flat ring map whose induced morphism of spectra is surjective is faithfully flat. -/
public theorem faithfullyFlat_of_flat_of_surjective_spec {A A' : CommRingCat.{u}} (φ : A ⟶ A')
    (hflat : RingHom.Flat φ.hom) (hsurj : Function.Surjective (Spec.map φ).base) :
    letI : Algebra A A' := φ.hom.toAlgebra
    Module.FaithfullyFlat A A' := by
  let : Algebra A A' := φ.hom.toAlgebra
  have : Module.Flat A A' := hflat
  exact Module.FaithfullyFlat.of_comap_surjective (A := A) (B := A') hsurj

/-- **[Stacks, Tag 06VL].** For a sheaf of modules `F` on the big `τ`-site over `S` and a flat
morphism `Spec A' → Spec A` of affines of the site over `S` which is surjective, the extended
Amitsur complex of `A → A'` with coefficients `F(Spec A)` is exact. For adequate `F` this is the
extended Čech complex of the covering, by
`Stacks.Adequate.bijective_affineSectionBaseChangeMap_base`. -/
public theorem acyclic_amitsurExtendedCochainComplex_baseSections (B : BigSite τ S)
    (F : SheafOfModules.{max u m} B.structureSheaf)
    (A A' : CommRingCat.{u}) (φ : A ⟶ A') (f : Spec A ⟶ S)
    (hA : schemeSizeBelow B.cutoff (Spec A))
    (hflat : RingHom.Flat φ.hom) (hsurj : Function.Surjective (Spec.map φ).base) :
    letI : Algebra A A' := φ.hom.toAlgebra
    (AlgebraicTopology.amitsurExtendedCochainComplex A A'
      (baseSections B F A f hA)).Acyclic := by
  let : Algebra A A' := φ.hom.toAlgebra
  have : Module.FaithfullyFlat A A' :=
    faithfullyFlat_of_flat_of_surjective_spec φ hflat hsurj
  exact Stacks.Descent.amitsurExtendedCochainComplex_acyclic_of_faithfullyFlat _ _ _

end Stacks.Adequate

end
