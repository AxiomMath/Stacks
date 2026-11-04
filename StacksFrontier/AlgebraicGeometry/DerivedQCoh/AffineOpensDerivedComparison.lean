module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.Algebra.Homology.DerivedCategory.SerreSubcategory
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineOpensQuasiCoherentReflection
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.DerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentCokernels
public import StacksFrontier.AlgebraicGeometry.Topologies.QuasicoherentOnSiteOfPresentation
import StacksCore.Tactic.StacksAttribute

/-!
# `D_QCoh(𝒪_X) ≌ D_QCoh(X_{affine, Zar}, 𝒪)` for a scheme

Let `X` be a scheme. [Stacks, Tag 0GZZ] lists five triangulated categories attached to it and
asserts that they are canonically exactly equivalent:

1. `D_QCoh(𝒪_X)`, on the ringed space `(X, 𝒪_X)`;
2. `D_QCoh(X_Zar, 𝒪)`, on the small Zariski site;
3. `D_QCoh(X_{affine, Zar}, 𝒪)`, on the affine opens with the Zariski topology;
4. `D_QCoh(X_affine, 𝒪)`, on the affine opens with the **chaotic** topology;
5. `QC(X_affine, 𝒪)`, the cartesian objects of [Stacks, Tag 0GYU] on the chaotic site.

This file proves the comparison of (1) with (3). Categories (1) and (2) are the *same* category
here — `AlgebraicGeometry.Scheme.Modules` is by definition the sheaves of modules over
`X.ringCatSheaf` on the site `X.Opens`, which is the small Zariski site of `X` — so the two
Stacks steps (1) ≃ (2) ≃ (3) collapse to the single step along
`AlgebraicGeometry.Scheme.affineOpensToOpens`.

The module-level comparison is available:
`AlgebraicGeometry.Scheme.affineOpensModuleRestrictionEquivalence` is the equivalence of abelian
categories of modules, and
`AlgebraicGeometry.Scheme.isQuasicoherentOnSite_affineOpensModuleRestriction_iff` matches up the
quasi-coherent modules under it, in both directions and with no hypothesis. What this file adds
is the passage to the unbounded derived categories and the identification of the subcategories
of complexes with quasi-coherent *cohomology*.

## Main definitions

* `AlgebraicGeometry.Scheme.affineOpensDerivedRestrictionEquivalence`: **restriction to the
  affine opens is an equivalence of the unbounded derived categories** of `𝒪_X`-modules, with its
  `CommShift` and `IsTriangulated` instances, so it is an exact equivalence of triangulated
  categories.
* `AlgebraicGeometry.Scheme.affineOpensQuasicoherentDerivedCategory`: category (3) of
  [Stacks, Tag 0GZZ], `D_QCoh(X_{affine, Zar}, 𝒪)`.
* `AlgebraicGeometry.Scheme.quasicoherentDerivedAffineOpensEquivalence`: **the equivalence
  (1) ≃ (3) of [Stacks, Tag 0GZZ]**, induced by derived restriction.
* `AlgebraicGeometry.Scheme.quasicoherentDerivedAffineOpensEquivalenceOfIsQuasicoherent`: the
  same equivalence with the source read over Mathlib's quasi-coherence predicate, which is the
  spelling of `Stacks.Duality.quasiCoherentDerivedCategory`.

## Main results

* `AlgebraicGeometry.Scheme.derivedCategoryB_isQuasicoherentOnSite_affineOpensRestriction_iff`:
  **a complex of `𝒪_X`-modules has quasi-coherent cohomology if and only if its restriction to
  the affine opens does.** No hypothesis: both directions of the module-level statement are
  available, so unlike the étale analogue
  `AlgebraicGeometry.Space.derivedCategoryB_isQuasicoherentOnSite_affineEtaleRestriction_iff`
  nothing is carried.
* `AlgebraicGeometry.Scheme.isQuasicoherent_eq_isQuasicoherentOnSite_ringCatSheaf`: on the
  Zariski site of a scheme Mathlib's quasi-coherence and the quasi-coherence of
  [Stacks, Tag 03DL] (6) are the same object property.
* `AlgebraicGeometry.Scheme.isClosedUnderIsomorphisms_derivedCategoryB_affineOpens`: category
  (3) is closed under isomorphisms in `D(X_{affine, Zar}, 𝒪)`.

## What is **not** proved here

The comparison of (3) with (4), the change of topology on the affine opens. That is the morphism
of ringed sites `ε` of [Stacks, Tag 0EWK], and the input it needs is the second conclusion of
[Stacks, Tag 07A8] — the equivalence `D_𝒜(R_τ) = D_𝒜(R_{τ'})` induced by `ε^*` and `Rε_*`. Only
the first conclusion of 07A8 exists in this library, as
`Stacks.Cohomology.CompareTopologies.isWeakSerreClass_imageOfLE`; the second needs the total
right derived functor of `ε_*` on an unbounded derived category, which does not exist anywhere
here. No statement about (3) versus (4) is made below, not even a hypothetical one.

In particular this file does **not** discharge the hypothesis of
`AlgebraicGeometry.isLeftAdjoint_qcqsQuasiCoherentDerivedPushforward_of_affineSiteAdjunction`.
That consumer needs a generating family in the sense of [Stacks, Tag 0GYG] on `D_QCoh(𝒪_X)`
indexed by a `Type u`, and the only such family in the library,
`AlgebraicGeometry.exists_generating_family_qcohCohomology_affineChaotic`, lives on the
**chaotic** affine site: the machinery producing it,
`Stacks.ModulesOnACategory.QuasiCoherentEquivalence.exists_qc_generating_family`, is stated
for modules over a presheaf of rings on a bare category, i.e. for the chaotic topology, and the
identification of `QC` with `D_QCoh` that carries it to
`AlgebraicGeometry.qcohCohomologyProperty` requires `J = ⊥`. So no family on the Zariski affine
site is available, and the equivalence below cannot replace the hypothesised adjunction with the
chaotic site. What it does do is reduce that hypothesis to a statement about the affine site
alone: a comparison of (3) with (4) now suffices, with (1) ≃ (3) no longer assumed.

The triangulated structure on the two subcategories is also not established here. For category
(1) it is proved, as
`Stacks.AlgebraicGeometry.QuasicoherentWeakSerre.derivedQuasicoherent_isTriangulated`, which
would give the same for (3) across the comparison; that file is not imported, to keep this one
free of a global choice of derived-category model. What is proved below is that the ambient
equivalence `AlgebraicGeometry.Scheme.affineOpensDerivedRestrictionEquivalence` is exact and
triangulated, so the comparison of the subcategories is the restriction of an exact equivalence
and not merely some equivalence of categories.

## Implementation notes

The derived-category model is a parameter: the statements carry
`[HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]` and the same for the affine site,
rather than fixing `CategoryTheory.HasDerivedCategory.standard`, so that a consumer working at
the locally small model can use them unchanged.

Additivity of restriction has to be given by hand, as in
`AlgebraicGeometry.Space.additive_affineEtaleModuleRestriction`: restriction is
`SheafOfModules.pushforward` along the identity, computed objectwise on sections, so addition of
morphisms is preserved on the nose. Exactness is then formal, restriction being an equivalence.

The passage from modules to complexes is
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, which identifies `Hⁿ` of the restricted
complex with the restriction of `Hⁿ`; with it the degree-zero statement
`AlgebraicGeometry.Scheme.isQuasicoherentOnSite_affineOpensModuleRestriction_iff` gives the
statement about complexes degree by degree.

## References

* [Stacks Project, Tag 0GZZ](https://stacks.math.columbia.edu/tag/0GZZ)
* [Stacks Project, Tag 0GZX](https://stacks.math.columbia.edu/tag/0GZX)
* [Stacks Project, Tag 03DL](https://stacks.math.columbia.edu/tag/03DL)
* [Stacks Project, Tag 03DM](https://stacks.math.columbia.edu/tag/03DM)
* [Stacks Project, Tag 07A8](https://stacks.math.columbia.edu/tag/07A8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe w u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-! ### Exactness of restriction to the affine opens -/

/-- **Restriction of sheaves of modules to the affine opens is additive.** It is
`SheafOfModules.pushforward` along the identity of the restricted structure sheaf, which is
computed objectwise on sections, so it preserves addition of morphisms on the nose. -/
instance Scheme.additive_affineOpensModuleRestriction :
    X.affineOpensModuleRestriction.Additive where
  map_add := rfl

/-- **Restriction of sheaves of modules to the affine opens is an equivalence**, the underlying
functor of `AlgebraicGeometry.Scheme.affineOpensModuleRestrictionEquivalence`. -/
theorem Scheme.isEquivalence_affineOpensModuleRestriction :
    X.affineOpensModuleRestriction.IsEquivalence :=
  X.affineOpensModuleRestrictionEquivalence.isEquivalence_functor

/-- Restriction to the affine opens is left exact, being an equivalence. -/
instance Scheme.preservesFiniteLimits_affineOpensModuleRestriction :
    PreservesFiniteLimits X.affineOpensModuleRestriction :=
  have := X.isEquivalence_affineOpensModuleRestriction
  inferInstance

/-- Restriction to the affine opens is right exact, being an equivalence. -/
instance Scheme.preservesFiniteColimits_affineOpensModuleRestriction :
    PreservesFiniteColimits X.affineOpensModuleRestriction :=
  have := X.isEquivalence_affineOpensModuleRestriction
  inferInstance

/-! ### The two quasi-coherence predicates on the Zariski site of a scheme -/

/-- **On the Zariski site of a scheme the two quasi-coherence predicates agree.** Mathlib's
`SheafOfModules.isQuasicoherent` and the quasi-coherence of [Stacks, Tag 03DL] (6),
`SheafOfModules.isQuasicoherentOnSite`, are the same object property on `𝒪_X`-modules.

This is `SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite`, whose size hypothesis
`UnivLE.{max u v r, r}` reads `UnivLE.{u, u}` here: the opens of `X` form a `Type u` whose order
category has morphisms in `Type u`, and the sections of `𝒪_X` live in `Type u` as well. -/
theorem Scheme.isQuasicoherent_eq_isQuasicoherentOnSite_ringCatSheaf :
    SheafOfModules.isQuasicoherent X.ringCatSheaf =
      SheafOfModules.isQuasicoherentOnSite.{u, u, u, u} X.ringCatSheaf :=
  funext fun M ↦ propext (SheafOfModules.isQuasicoherent_iff_isQuasicoherentOnSite M)

section Derived

variable [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)]
  [HasDerivedCategory.{w} (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
      X.affineZariskiRingedSite.O))]

/-! ### The equivalence of the ambient derived categories -/

/-- **Restriction to the affine opens induces an equivalence of the unbounded derived
categories** of `𝒪_X`-modules,

`D(𝒪_X) ≌ D(X_{affine, Zar}, 𝒪)`.

The equivalence of abelian categories
`AlgebraicGeometry.Scheme.affineOpensModuleRestrictionEquivalence` is exact, both directions of
an equivalence preserving all limits and colimits, so
`Stacks.DerivedQCoh.Equivalence.mapDerivedCategory` applies. -/
def Scheme.affineOpensDerivedRestrictionEquivalence :
    DerivedCategory (SheafOfModules.{u} X.ringCatSheaf) ≌
      DerivedCategory (SheafOfModules.{u} (Stacks.SheafOfModules.Tensor.ringSheaf
          X.affineZariskiRingedSite.O)) :=
  have : X.affineOpensModuleRestrictionEquivalence.functor.Additive :=
    inferInstanceAs X.affineOpensModuleRestriction.Additive
  Stacks.DerivedQCoh.Equivalence.mapDerivedCategory
    X.affineOpensModuleRestrictionEquivalence

/-- The functor of `AlgebraicGeometry.Scheme.affineOpensDerivedRestrictionEquivalence` is the
one induced on derived categories by restriction to the affine opens. In particular the
comparison below is derived restriction, not merely some equivalence. -/
@[simp]
theorem Scheme.affineOpensDerivedRestrictionEquivalence_functor :
    X.affineOpensDerivedRestrictionEquivalence.functor =
      X.affineOpensModuleRestriction.mapDerivedCategory :=
  rfl

/-- Derived restriction to the affine opens commutes with the shift. -/
instance Scheme.commShift_affineOpensDerivedRestrictionEquivalence_functor :
    X.affineOpensDerivedRestrictionEquivalence.functor.CommShift ℤ :=
  inferInstanceAs (X.affineOpensModuleRestriction.mapDerivedCategory.CommShift ℤ)

/-- Derived restriction to the affine opens is a triangulated functor, so
`AlgebraicGeometry.Scheme.affineOpensDerivedRestrictionEquivalence` is an exact equivalence of
triangulated categories. -/
instance Scheme.isTriangulated_affineOpensDerivedRestrictionEquivalence_functor :
    X.affineOpensDerivedRestrictionEquivalence.functor.IsTriangulated :=
  inferInstanceAs X.affineOpensModuleRestriction.mapDerivedCategory.IsTriangulated

/-! ### Matching up the quasi-coherent cohomology -/

/-- **Quasi-coherence of the cohomology of a complex of `𝒪_X`-modules is detected on the affine
opens of `X`.** A complex has quasi-coherent cohomology sheaves in every degree if and only if
its derived restriction to the affine opens does.

Both directions of the degree-zero statement are available with no hypothesis — preservation is
`AlgebraicGeometry.Scheme.isQuasicoherentOnSite_affineOpensModuleRestriction` and reflection is
`AlgebraicGeometry.Scheme.isQuasicoherentOnSite_of_affineOpensModuleRestriction` — so, unlike
the étale analogue
`AlgebraicGeometry.Space.derivedCategoryB_isQuasicoherentOnSite_affineEtaleRestriction_iff`,
nothing is carried here. The passage from modules to complexes is
`CategoryTheory.Functor.mapDerivedCategoryHomologyIso`, which identifies the cohomology sheaves
of the restricted complex with the restrictions of its cohomology sheaves. -/
theorem Scheme.derivedCategoryB_isQuasicoherentOnSite_affineOpensRestriction_iff
    (K : DerivedCategory (SheafOfModules.{u} X.ringCatSheaf)) :
    DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite (Stacks.SheafOfModules.Tensor.ringSheaf
            X.affineZariskiRingedSite.O))
        (X.affineOpensDerivedRestrictionEquivalence.functor.obj K) ↔
      DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite X.ringCatSheaf) K := by
  have hcomp := fun n : ℤ ↦
    (CategoryTheory.Functor.mapDerivedCategoryHomologyIso
      X.affineOpensModuleRestriction n).app K
  have hiso : (SheafOfModules.isQuasicoherentOnSite
      (Stacks.SheafOfModules.Tensor.ringSheaf
          X.affineZariskiRingedSite.O)).IsClosedUnderIsomorphisms :=
    inferInstance
  exact ⟨fun h n ↦ X.isQuasicoherentOnSite_of_affineOpensModuleRestriction _
      (hiso.of_iso (hcomp n) (h n)),
    fun h n ↦ hiso.of_iso (hcomp n).symm
      (X.isQuasicoherentOnSite_affineOpensModuleRestriction _ (h n))⟩

/-- **Category (3) of [Stacks, Tag 0GZZ]**: `D_QCoh(X_{affine, Zar}, 𝒪)`, the full subcategory
of the unbounded derived category of modules on the affine Zariski site of `X` all of whose
cohomology sheaves are quasi-coherent. -/
abbrev Scheme.affineOpensQuasicoherentDerivedCategory :=
  (DerivedCategoryB.derivedCategoryB
    (SheafOfModules.isQuasicoherentOnSite
      (Stacks.SheafOfModules.Tensor.ringSheaf X.affineZariskiRingedSite.O))).FullSubcategory

omit [HasDerivedCategory.{w} (SheafOfModules.{u} X.ringCatSheaf)] in
/-- `D_QCoh(X_{affine, Zar}, 𝒪)` is closed under isomorphisms in `D(X_{affine, Zar}, 𝒪)`: a
cohomology sheaf of an object isomorphic to a given one is isomorphic to the corresponding
cohomology sheaf, and quasi-coherence is closed under isomorphisms. -/
theorem Scheme.isClosedUnderIsomorphisms_derivedCategoryB_affineOpens :
    (DerivedCategoryB.derivedCategoryB
      (SheafOfModules.isQuasicoherentOnSite
        (Stacks.SheafOfModules.Tensor.ringSheaf
            X.affineZariskiRingedSite.O))).IsClosedUnderIsomorphisms :=
  ⟨fun {_ _} e hK n ↦
    (inferInstance : (SheafOfModules.isQuasicoherentOnSite
        (Stacks.SheafOfModules.Tensor.ringSheaf
            X.affineZariskiRingedSite.O)).IsClosedUnderIsomorphisms).of_iso
      ((DerivedCategory.homologyFunctor _ n).mapIso e) (hK n)⟩

/-- **The equivalence (1) ≃ (3) of [Stacks, Tag 0GZZ] for a scheme**: derived restriction to the
affine opens is an equivalence

`D_QCoh(𝒪_X) ≌ D_QCoh(X_{affine, Zar}, 𝒪)`.

It is the exact equivalence of the ambient unbounded derived categories
`AlgebraicGeometry.Scheme.affineOpensDerivedRestrictionEquivalence`, cut down to the two full
subcategories by
`AlgebraicGeometry.Scheme.derivedCategoryB_isQuasicoherentOnSite_affineOpensRestriction_iff`; so
the comparison is the canonical one, being the restriction of the derived restriction functor.
No hypothesis is carried. Categories (1) and (2) of 0GZZ are the same category of modules here,
so this single step is the Stacks chain (1) ≃ (2) ≃ (3).

[Stacks, Tag 0GZZ] (not registered here: this is not the whole statement of the tag): the
equivalence of (1) D_QCoh(O_X) and (3) D_QCoh(X_affine_Zar, O) for a scheme, as an equivalence of
categories induced by derived restriction to the affine opens, with no hypothesis; (1) and (2) are
the same category of modules here, so this is the chain (1) = (2) ≃ (3)
-/
def Scheme.quasicoherentDerivedAffineOpensEquivalence :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherentOnSite X.ringCatSheaf)).FullSubcategory ≌
      X.affineOpensQuasicoherentDerivedCategory :=
  have := X.isClosedUnderIsomorphisms_derivedCategoryB_affineOpens
  X.affineOpensDerivedRestrictionEquivalence.congrFullSubcategory
    (funext fun K ↦ propext
      (X.derivedCategoryB_isQuasicoherentOnSite_affineOpensRestriction_iff K))

/-- **The equivalence (1) ≃ (3) of [Stacks, Tag 0GZZ], with (1) read over Mathlib's
quasi-coherence.** The same statement as
`AlgebraicGeometry.Scheme.quasicoherentDerivedAffineOpensEquivalence` with the source written in
the spelling of `Stacks.Duality.quasiCoherentDerivedCategory`, the two predicates being the same
object property on the Zariski site of a scheme by
`AlgebraicGeometry.Scheme.isQuasicoherent_eq_isQuasicoherentOnSite_ringCatSheaf`.

[Stacks, Tag 0GZZ] (not registered here: this is not the whole statement of the tag): the
equivalence of (1) D_QCoh(O_X) and (3) D_QCoh(X_affine_Zar, O) for a scheme, with (1) read over
Mathlib's quasi-coherence predicate
-/
def Scheme.quasicoherentDerivedAffineOpensEquivalenceOfIsQuasicoherent :
    (DerivedCategoryB.derivedCategoryB
        (SheafOfModules.isQuasicoherent X.ringCatSheaf)).FullSubcategory ≌
      X.affineOpensQuasicoherentDerivedCategory := by
  rw [X.isQuasicoherent_eq_isQuasicoherentOnSite_ringCatSheaf]
  exact X.quasicoherentDerivedAffineOpensEquivalence

end Derived

end AlgebraicGeometry

end
