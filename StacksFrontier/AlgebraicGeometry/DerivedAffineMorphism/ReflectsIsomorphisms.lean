module

public import StacksFrontier.Algebra.Homology.DerivedCategory.MapDerivedCategoryHomology
public import StacksFrontier.AlgebraicGeometry.DerivedQCoh.AffineDerivedEquivalence
public import StacksFrontier.AlgebraicGeometry.QuasiCoherent.Coherator.AffineDerivedPushforward

/-!
# Derived pushforward along an affine morphism reflects isomorphisms

Let `φ : R ⟶ S` be a map of commutative rings and `f = Spec φ : Spec S ⟶ Spec R` the induced
morphism of affine schemes. A map `α : E ⟶ F` of complexes of `𝒪_{Spec S}`-modules with
quasi-coherent cohomology is invertible in `D_QCoh(𝒪_{Spec S})` as soon as `Rf_*α` is invertible
in `D_QCoh(𝒪_{Spec R})`.

The proof replaces both quasi-coherent derived categories by derived categories of modules. Derived
sheafification `D(S) ⥤ D_QCoh(𝒪_{Spec S})` is an equivalence [Stacks, Tag 06Z0], and under it
`Rf_*` becomes derived restriction of scalars along `φ` [Stacks, Tag 0DJK]. Restriction of scalars
of modules is exact, so the functor it induces on unbounded derived categories acts on cohomology
by applying restriction of scalars in each degree; since a map of `S`-modules whose underlying map
of `R`-modules is bijective is itself bijective, and since a map of `D(S)` is invertible exactly
when all of its maps on cohomology are, derived restriction of scalars reflects isomorphisms. An
equivalence precomposed with a functor reflects isomorphisms only if that functor does, which
transports the conclusion back to `Rf_*`.

## Main results

* `AlgebraicGeometry.reflectsIsomorphisms_mapDerivedCategory_restrictScalars`: derived restriction
  of scalars along a map of commutative rings reflects isomorphisms.
* `AlgebraicGeometry.reflectsIsomorphisms_derivedQuasicoherentPushforward_specMap`:
  [Stacks, Tag 08I8] for a morphism of affine schemes `Spec φ`.

## Implementation notes

Both derived categories are the locally small ones, `SheafOfModules.hasDerivedCategory` and
`ModuleCat.hasDerivedCategory`, which are global instances; this is the model at which
`AlgebraicGeometry.derivedTilde` and `AlgebraicGeometry.derivedQuasicoherentPushforward` are
stated, and the statements below take no model as a binder for that reason.

Tag 08I8 asserts the conclusion for an arbitrary affine morphism `f : X ⟶ S` with `S` any scheme,
and that general statement is
`AlgebraicGeometry.reflectsIsomorphisms_derivedQuasicoherentPushforward` in
`StacksFrontier/AlgebraicGeometry/DerivedAffineMorphism/ReflectsIsomorphismsAffineHom.lean`; it
subsumes the statement below, which is its value at `f = Spec φ`. The general case does not in
fact go through the source's reduction to the affine case — no base change or pseudo-functoriality
of `AlgebraicGeometry.derivedQuasicoherentPushforward` is needed — because the conclusion of that
reduction, the t-exactness of `Rf_*` on `D_QCoh` for an affine morphism, is already available as
`Stacks.AlgebraicGeometry.AffinePushforwardTExactness.isZero_homology_derivedPushforward_iff`. The
affine case is kept here because its proof is the independent one through [Stacks, Tag 06Z0] and
[Stacks, Tag 0DJK] that the source gives.

## References

* [Stacks Project, Tag 08I8](https://stacks.math.columbia.edu/tag/08I8)
* [Stacks Project, Tag 06Z0](https://stacks.math.columbia.edu/tag/06Z0)
* [Stacks Project, Tag 0DJK](https://stacks.math.columbia.edu/tag/0DJK)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(R)` for sheaves of modules on a small site.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] SheafOfModules.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe v₁ v₂ v₃ u₁ u₂ u₃ u

namespace CategoryTheory.Functor

/-- **An equivalence can be cancelled from the left in a reflection statement.** If `F` is an
equivalence and `F ⋙ G` reflects isomorphisms, then `G` reflects isomorphisms, since `G` is
isomorphic to `F⁻¹ ⋙ (F ⋙ G)` and `F⁻¹` is fully faithful. -/
public theorem reflectsIsomorphisms_of_isEquivalence_comp {C : Type u₁} {D : Type u₂}
    {E : Type u₃} [Category.{v₁} C] [Category.{v₂} D] [Category.{v₃} E] (F : C ⥤ D) (G : D ⥤ E)
    [F.IsEquivalence] (h : (F ⋙ G).ReflectsIsomorphisms) : G.ReflectsIsomorphisms :=
  @reflectsIsomorphisms_of_iso _ _ _ _ _ _ (F.asEquivalence.invFunIdAssoc G)
    (@reflectsIsomorphisms_comp _ _ _ _ _ _ _ _ inferInstance h)

end CategoryTheory.Functor

namespace AlgebraicGeometry

section

variable {R S : CommRingCat.{u}} (φ : R ⟶ S)

/-- **Derived restriction of scalars reflects isomorphisms.** A map of `D(S)` whose image in
`D(R)` is invertible is itself invertible: invertibility in either derived category is tested on
cohomology, in each degree the map on cohomology is restriction of scalars applied to the map on
cohomology upstairs because restriction of scalars is exact, and restriction of scalars of modules
reflects isomorphisms. -/
public theorem reflectsIsomorphisms_mapDerivedCategory_restrictScalars :
    (ModuleCat.restrictScalars φ.hom).mapDerivedCategory.ReflectsIsomorphisms where
  reflects {K L} ψ h := by
    rw [DerivedCategory.isIso_iff]
    intro n
    have := ((ModuleCat.restrictScalars φ.hom).isIso_mapDerivedCategory_map_iff ψ).1 h n
    exact isIso_of_reflects_iso _ (ModuleCat.restrictScalars φ.hom)

/-- **[Stacks, Tag 08I8] for a morphism of affine schemes.** Let `φ : R ⟶ S` and let
`f = Spec φ : Spec S ⟶ Spec R`. Then `Rf_* : D_QCoh(𝒪_{Spec S}) ⥤ D_QCoh(𝒪_{Spec R})` reflects
isomorphisms: a map of complexes with quasi-coherent cohomology is invertible as soon as its
derived pushforward is.

Derived sheafification is an equivalence `D(S) ≌ D_QCoh(𝒪_{Spec S})` [Stacks, Tag 06Z0] carrying
`Rf_*` to derived restriction of scalars along `φ` [Stacks, Tag 0DJK], and that functor reflects
isomorphisms. -/
@[stacks 08I8 "a morphism Spec φ of affine schemes"]
public theorem reflectsIsomorphisms_derivedQuasicoherentPushforward_specMap :
    (derivedQuasicoherentPushforward (Spec.map φ)).ReflectsIsomorphisms :=
  have hrs : ((ModuleCat.restrictScalars φ.hom).mapDerivedCategory ⋙
      derivedTilde R).ReflectsIsomorphisms :=
    @reflectsIsomorphisms_comp _ _ _ _ _ _ _ _
      (reflectsIsomorphisms_mapDerivedCategory_restrictScalars φ) inferInstance
  have hcomp : (derivedTilde S ⋙
      derivedQuasicoherentPushforward (Spec.map φ)).ReflectsIsomorphisms :=
    @reflectsIsomorphisms_of_iso _ _ _ _ _ _
      (derivedTildeCompDerivedQuasicoherentPushforwardIso φ).symm hrs
  @Functor.reflectsIsomorphisms_of_isEquivalence_comp _ _ _ _ _ _ (derivedTilde S)
    (derivedQuasicoherentPushforward (Spec.map φ)) inferInstance hcomp

end

end AlgebraicGeometry

end
