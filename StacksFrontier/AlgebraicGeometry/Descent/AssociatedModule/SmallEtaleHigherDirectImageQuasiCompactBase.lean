module

public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleCechDirectImageQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Descent.AssociatedModule.SmallEtaleFiniteAffineOverBaseCover
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentFiniteProducts
public import StacksFrontier.Homology.CompositeCollapseFiniteProducts

/-!
# Higher direct images along `ε_a` over a quasi-compact base

Let `a : X ⟶ Y` be a morphism of schemes of a big étale site and let `𝓕` be an
`𝒪_{X_étale}`-module quasi-coherent on the site. If `X` is quasi-compact, `Y` is separated and `a`
is separated, then for every `n` the higher direct image `R ⁿ (ε_a)_*(𝓕)` is cartesian between the
affine objects of `Y_étale`, hence quasi-coherent on `Y_étale` by
`AlgebraicGeometry.SmallEtale.isQuasicoherentOnSite_iff_isCartesianOnAffines`. The same holds for
an affine `Y` and a quasi-compact separated `a`.

The proof uses the sheaf-level Čech complex of a covering family `E` of the final object of
`X_étale`. Its degree-`q` term is the product `∏_{i : Fin (q+1) → E.I₀} j_{V_i,*} j_{V_i}^{-1} 𝓕`,
with `V_i` the iterated fibre product of the members indexed by `i`. When `E` is finite, its
members are affine over `Y` and `a` is separated, each factor is acyclic for `(ε_a)_*` and has a
direct image quasi-coherent on the site, and both properties are closed under finite products.
Such a finite family exists when `X` is quasi-compact and `Y` is separated.

## Main results

* `sheafLevelCechComplex_obj_X`: the degree-`q` term of the sheaf-level Čech complex is the
  product, over the `(q + 1)`-tuples of members, of the Čech direct images at the iterated fibre
  products.
* `acyclic_pushforward_sheafLevelCechComplex_X_of_isSeparatedHom`: for a separated `a`, the terms
  of the sheaf-level Čech complex of a finite covering family whose members are affine over `Y`
  are acyclic for `(ε_a)_*`.
* `isQuasicoherentOnSite_pushforward_sheafLevelCechComplex_X_of_isSeparatedHom`: under the same
  hypotheses, the direct images of these terms are quasi-coherent on the site.
* `isCartesianOnAffines_rightDerived_pushforward_of_compactSpace_of_isSeparated_of_isSeparatedHom`:
  for a quasi-compact `X`, a separated `Y` and a separated `a`, every `R ⁿ (ε_a)_*(𝓕)` is
  cartesian between the affine objects of `Y_étale`.
* `isQuasicoherentOnSite_rightDerived_pushforward_of_compactSpace_of_isSeparated_of_isSeparatedHom`
  states that, under the same hypotheses, every `R ⁿ (ε_a)_*(𝓕)` is quasi-coherent on the site.
* `isCartesianOnAffines_rightDerived_pushforward_of_isAffine_of_quasiCompact_of_isSeparatedHom`:
  for an affine `Y` and a quasi-compact separated `a`, every `R ⁿ (ε_a)_*(𝓕)` is cartesian
  between the affine objects of `Y_étale`.

## Implementation notes

Finiteness of the covering family is essential: quasi-coherence on a site is not closed under
infinite products. Separatedness of `a` cannot be dropped on this route: for a non-separated `a`
an intersection of two affine opens of `X` is quasi-affine and can carry nonvanishing higher
quasi-coherent cohomology, so the Čech terms need not be acyclic.

## References

* [Stacks Project, Tag 01SG](https://stacks.math.columbia.edu/tag/01SG)
* [Stacks Project, Tag 03AM](https://stacks.math.columbia.edu/tag/03AM)
* [Stacks Project, Tag 070R](https://stacks.math.columbia.edu/tag/070R)
* [Stacks Project, Tag 071N](https://stacks.math.columbia.edu/tag/071N)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 5000] SheafOfModules.instAbelian

namespace AlgebraicGeometry.SmallEtale

/-- Products of `𝒪`-modules on the small étale site, supplied directly: instance search for
them times out under Lean v4.35.0. -/
private instance (priority := high) hasProducts_smallEtaleHigherDirectImageQuasiCompactBase
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) :
    HasProducts.{u} (SheafOfModules.{u} (structureSheaf B S hS)) :=
  fun J => SheafOfModules.hasLimitsOfShape (Discrete J) _

variable (B : BigEtaleSite.{u}) {X Y : B.Scheme} (a : X ⟶ Y)

set_option synthInstance.maxHeartbeats 400000 in
/-- The degree-`q` term of the sheaf-level Čech complex of a covering family `E` is the product,
over the `(q + 1)`-tuples `i` of members of `E`, of the Čech direct images
`j_{V_i,*} j_{V_i}^{-1} 𝓕` at the iterated fibre products `V_i`. -/
public theorem sheafLevelCechComplex_obj_X
    (E : PreZeroHypercover.{u} (final B X.obj X.property))
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property)) (q : ℕ) :
    ((sheafLevelCechComplex B X.obj X.property E).obj 𝓕).X q =
      ∏ᶜ (fun i : Fin (q + 1) → E.I₀ ↦
        (Stacks.CechSite.SheafLevel.directImage (structureSheaf B X.obj X.property)
          (∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left).obj 𝓕) :=
  rfl

/-- For a separated `a`, the terms of the sheaf-level Čech complex of a finite covering family
whose members are affine over `Y`, with coefficients in a module quasi-coherent on the site, are
acyclic for `(ε_a)_*`. -/
public theorem acyclic_pushforward_sheafLevelCechComplex_X_of_isSeparatedHom
    [IsSeparated (schemeHom B a)]
    (E : PreZeroHypercover.{u} (final B X.obj X.property)) [Finite E.I₀]
    (hE : ∀ j, IsAffineHom (toBaseHom B a (E.X j)))
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓕 : 𝓕.IsQuasicoherentOnSite) (q : ℕ) :
    Stacks.RightDerivedComp.acyclic
      (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
      (((sheafLevelCechComplex B X.obj X.property E).obj 𝓕).X q) := by
  have : Finite (Fin (q + 1) → E.I₀) :=
    @Pi.finite _ _ (Finite.of_fintype (Fin (q + 1))) fun _ ↦ ‹Finite E.I₀›
  exact Stacks.RightDerivedComp.acyclic_pi
    (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
    (fun i : Fin (q + 1) → E.I₀ ↦
      (Stacks.CechSite.SheafLevel.directImage (structureSheaf B X.obj X.property)
        (∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left).obj 𝓕)
    (fun i ↦ acyclic_pushforward_directImage_piObj_of_isSeparatedHom B a E hE 𝓕 h𝓕 q i)

/-- For a separated `a`, the direct images along `ε_a` of the terms of the sheaf-level Čech
complex of a finite covering family whose members are affine over `Y`, with coefficients in a
module quasi-coherent on the site, are quasi-coherent on the site. -/
public theorem isQuasicoherentOnSite_pushforward_sheafLevelCechComplex_X_of_isSeparatedHom
    [IsSeparated (schemeHom B a)]
    (E : PreZeroHypercover.{u} (final B X.obj X.property)) [Finite E.I₀]
    (hE : ∀ j, IsAffineHom (toBaseHom B a (E.X j)))
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓕 : 𝓕.IsQuasicoherentOnSite) (q : ℕ) :
    ((SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a)).obj
      (((sheafLevelCechComplex B X.obj X.property E).obj 𝓕).X q)).IsQuasicoherentOnSite := by
  exact (SheafOfModules.isQuasicoherentOnSite _).prop_of_iso
    (PreservesProduct.iso (SheafOfModules.pushforward.{u} (smallEtaleStructureMapRing B a))
      (fun i : Fin (q + 1) → E.I₀ ↦
        (Stacks.CechSite.SheafLevel.directImage (structureSheaf B X.obj X.property)
          (∏ᶜ (fun b ↦ Over.mk (E.f (i b)))).left).obj 𝓕)).symm
    (ObjectProperty.prop_product _ fun i ↦
      isQuasicoherentOnSite_pushforward_directImage_piObj_of_isSeparatedHom B a E hE 𝓕 h𝓕 q i)

/-- For a quasi-compact `X`, a separated `Y` and a separated `a`, and a module `𝓕` quasi-coherent
on the site, every higher direct image `R ⁿ (ε_a)_*(𝓕)` is cartesian between the affine objects
of `Y_étale`. -/
public theorem
    isCartesianOnAffines_rightDerived_pushforward_of_compactSpace_of_isSeparated_of_isSeparatedHom
    [CompactSpace ↥X.obj] [Y.obj.IsSeparated] [IsSeparated (schemeHom B a)]
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓕 : 𝓕.IsQuasicoherentOnSite) (n : ℕ) :
    IsCartesianOnAffines B Y.obj Y.property
      (((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕) := by
  obtain ⟨E, hfin, hcov, -, hbase, -⟩ :=
    exists_finite_coversTop_isAffineHom_piObj_of_compactSpace_of_isSeparated_of_isSeparatedHom B a
  have := hfin
  exact fun _ _ g hT hT' ↦
    isCartesianOnAffines_rightDerived_pushforward_sheafLevelCech B a E hcov 𝓕
      (fun q ↦ acyclic_pushforward_sheafLevelCechComplex_X_of_isSeparatedHom B a E hbase 𝓕 h𝓕 q)
      (fun q ↦ isQuasicoherentOnSite_pushforward_sheafLevelCechComplex_X_of_isSeparatedHom
        B a E hbase 𝓕 h𝓕 q) n g hT hT'

/-- For a quasi-compact `X`, a separated `Y` and a separated `a`, and a module `𝓕` quasi-coherent
on the site, every higher direct image `R ⁿ (ε_a)_*(𝓕)` is quasi-coherent on the site. -/
public theorem
    isQuasicoherentOnSite_rightDerived_pushforward_of_compactSpace_of_isSeparated_of_isSeparatedHom
    [CompactSpace ↥X.obj] [Y.obj.IsSeparated] [IsSeparated (schemeHom B a)]
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓕 : 𝓕.IsQuasicoherentOnSite) (n : ℕ) :
    (((SheafOfModules.pushforward.{u}
      (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕).IsQuasicoherentOnSite :=
  (isQuasicoherentOnSite_iff_isCartesianOnAffines B Y.obj Y.property _).2
    (isCartesianOnAffines_rightDerived_pushforward_of_compactSpace_of_isSeparated_of_isSeparatedHom
      B a 𝓕 h𝓕 n)

/-- For an affine `Y`, a quasi-compact separated `a`, and a module `𝓕` quasi-coherent on the site,
every higher direct image `R ⁿ (ε_a)_*(𝓕)` is cartesian between the affine objects of
`Y_étale`. -/
public theorem
    isCartesianOnAffines_rightDerived_pushforward_of_isAffine_of_quasiCompact_of_isSeparatedHom
    [AlgebraicGeometry.IsAffine Y.obj] [QuasiCompact (schemeHom B a)]
    [IsSeparated (schemeHom B a)]
    (𝓕 : SheafOfModules.{u} (structureSheaf B X.obj X.property))
    (h𝓕 : 𝓕.IsQuasicoherentOnSite) (n : ℕ) :
    IsCartesianOnAffines B Y.obj Y.property
      (((SheafOfModules.pushforward.{u}
        (smallEtaleStructureMapRing B a)).rightDerived n).obj 𝓕) :=
  have : CompactSpace ↥X.obj :=
    QuasiCompact.compactSpace_of_compactSpace (schemeHom B a)
  isCartesianOnAffines_rightDerived_pushforward_of_compactSpace_of_isSeparated_of_isSeparatedHom
    B a 𝓕 h𝓕 n

end AlgebraicGeometry.SmallEtale

end
