module

public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartPrimeCriterion
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartStalkRings
public import StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineOpenDerivedStalk
public import StacksFrontier.Homology.Tor.DerivedExtensionLocalizationComp

/-!
# The pointwise condition of Stacks 0DJ8, read at the coordinate rings of a chart

Condition (1) of Stacks 0DJ8 is pointwise on `X'`: it asks that the map of Stacks 0DJ7 at every
point `x'` and in every degree be invertible. Condition (2) is read, by
`AlgebraicGeometry.BaseChangeChart.isIso_comparison_iff_forall_germ`, as the invertibility of the
chart's *ring-level* map of Stacks 0DJ7 after extension of scalars along the germ map of
`Spec 𝒪_{X'}(U')`. The two are statements about different rings and different objects, and this
module carries the part of their comparison which is pure transport of the geometry.

Two things are proved.

*The pointwise map is itself a ring-level map.* `AlgebraicGeometry.baseChangeCohomologyMap` is,
by construction, the map that
`RingTheory.TorIndependence.exists_unique_ringBaseChangeCohomologyMap` produces for the square of
the four local rings of the square of schemes at `x'`, applied to the derived stalks of `K` and
`K'`; so its value on the pure tensors `1 ⊗ m` that generate its source is the cohomology
comparison of that square. Saying so turns the pointwise condition into a condition about a map
of `𝒪_{X', x'}`-modules, and — reducing `IsIso` to bijectivity of the underlying function before
anything is transported — into a condition about a function.

*The target of the two maps is the same module.* The germ map `𝒪_{X'}(U') ⟶ 𝒪_{Spec 𝒪_{X'}(U'), y}`
is the localization at the prime that `y` names, hence flat, so cohomology commutes with derived
extension of scalars along it; and the derived localization of `RΓ(U', K')` is the derived stalk
of `K'`, by `AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso`. Together:

`𝒪_{Spec 𝒪_{X'}(U'), y} ⊗_{𝒪_{X'}(U')} H^n(RΓ(U', K'))  ≅  H^n(K'_{x'})`,

the right-hand side read over `𝒪_{Spec 𝒪_{X'}(U'), y}` along the inverse of the germ comparison.
The left-hand side is the target of the germ-localized chart map and the right-hand side is the
target of the pointwise map, so the two maps of the comparison have the same target.

## Main definitions

* `AlgebraicGeometry.homologyDerivedStalkAffineSectionsRestrictIso`: the displayed isomorphism,
  for `i : Spec A ⟶ X` whose germ comparison at `y` is inverted by a given `ε'`.
* `AlgebraicGeometry.derivedStalkAffineSectionsInvIso` and
  `AlgebraicGeometry.homologyDerivedStalkAffineSectionsInvIso`: the same two statements for `i` an
  open immersion, where `ε'` is the inverse of the germ comparison.

## Main results

* `ModuleCat.isIso_iff_isIso_of_bijective_comm`: two maps of modules, over two possibly different
  rings, which agree up to a bijection of their sources and a bijection of their targets, are
  invertible together.
* `AlgebraicGeometry.bijective_homologyDerivedStalkAffineSectionsRestrictIso`: the displayed
  isomorphism, read as a bijection of the underlying sets.
* `AlgebraicGeometry.baseChangeCohomologyMap_one_tmul`: the pointwise map of Stacks 0DJ7 at `x'`
  sends `1 ⊗ m` to the cohomology comparison of the square of local rings at `x'`, applied to the
  derived stalks.
* `AlgebraicGeometry.isIso_baseChangeCohomologyMap_iff_bijective`: so condition (1) at `x'` in
  degree `n` is bijectivity of a function.

## Implementation notes

Every `IsIso` is reduced to `Function.Bijective` before any transport happens, which is what
`ModuleCat.isIso_iff_isIso_of_bijective_comm` is for. Transporting an `IsIso` statement between
the two squares directly would mean transporting `ModuleCat` objects along ring isomorphisms, and
the resulting `eqToHom` bookkeeping is what the shape above avoids: the underlying function of a
map of modules does not know which ring acts on it, so a bijection between underlying functions
is all that a transport has to produce.

The seven algebra and scalar-tower structures on the four local rings are written out as `letI`
and `haveI` in the statements rather than named: they are the structures
`AlgebraicGeometry.baseChangeCohomologyMap` introduces inside its own body, and writing the same
terms is what lets `baseChangeCohomologyMap_one_tmul` be the defining equation of
`RingTheory.TorIndependence.exists_unique_ringBaseChangeCohomologyMap` with nothing rewritten.

*What is not proved here.* The two maps of the comparison have the same target, by
`homologyDerivedStalkAffineSectionsInvIso`; that their *sources* agree is the remaining step, and
it is not transport. The source of the germ-localized chart map is
`𝒪_{X'}(U')_y ⊗_{𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V')} H^n(RΓ(U,K) ⊗ᴸ_{𝒪_S(V)} 𝒪_{S'}(V'))` and the
source of the pointwise map is the same expression for the four local rings; identifying them
needs the comparison of Stacks 065Z to be natural along the cube of localizations. That
naturality is available: `RingTheory.TorIndependence.squareComparison_localized` moves `𝒪_S(V)`
and `𝒪_X(U)` to the local rings, `RingTheory.TorIndependence.squareComparison_pasted` moves
`𝒪_{S'}(V')` and `𝒪_{X'}(U')` to theirs,
`RingTheory.TorIndependence.squareComparison_cube` joins the two, and
`AlgebraicGeometry.BaseChangeChart.squareComparison_localRings` is the result at a chart, at the
square of stalk rings of the square of schemes. So is the cohomology-level exchange of a flat
extension of the algebra with derived base change,
`RingTheory.TorIndependence.isIso_localizedBaseChangeCohomologyComparison`.

So is the statement about the chart comparison's other factor, the morphism rather than the
square: that `AlgebraicGeometry.BaseChangeChart.sectionsBaseChangeMap`, base changed along the
germ map at `y`, is `AlgebraicGeometry.derivedPullbackStalkIso` at `ch.incU' y`, read through
`AlgebraicGeometry.derivedStalkAffineSectionsIso` at `U` and at `U'`. That is
`AlgebraicGeometry.BaseChangeChart.extendScalars_map_sectionsBaseChangeMap_eq` of
`StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartMorphismMatch`.

What `θ` still needs beyond those is the module-level assembly: the two naturality statements and
the two cohomology-level exchanges above identify the comparisons, and `θ` is then the chain of
module isomorphisms carrying the source of the germ-localized chart map to the source of the
pointwise map — `Stacks.TensorProductPushout.localizedRearrange` and
`Stacks.TensorProductPushout.baseCongr` of
`StacksFrontier.RingTheory.TensorProduct.LocalizedPushoutRearrangement`, together with the
cancellation of a base change along a composite.

Once that one bijection `θ` of sources is available, together with the commutation of the two
maps through the target bijection of
`bijective_homologyDerivedStalkAffineSectionsRestrictIso`, the bridge that
`AlgebraicGeometry.baseChange_tfae_of_bridge` asks for is
`ModuleCat.isIso_iff_isIso_of_bijective_comm` applied to `θ` and that target bijection: nothing
further about the geometry is needed.

No tag attribute is placed here. Nothing below is a clause of Stacks 0DJ8: the tag belongs on the
three-way equivalence, and these are inputs to it.

## References

* [Stacks Project, Tag 00HN](https://stacks.math.columbia.edu/tag/00HN)
* [Stacks Project, Tag 01HR](https://stacks.math.columbia.edu/tag/01HR)
* [Stacks Project, Tag 065Z](https://stacks.math.columbia.edu/tag/065Z)
* [Stacks Project, Tag 0DJ7](https://stacks.math.columbia.edu/tag/0DJ7)
* [Stacks Project, Tag 0DJ8](https://stacks.math.columbia.edu/tag/0DJ8)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(R)` for `R`-modules.
-- `D(𝒪_X)` for a scheme.
attribute [local instance] ModuleCat.hasDerivedCategory
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits
open CochainComplex.DerivedExtensionScalars (totalDerivedExtensionScalars)
open scoped TensorProduct ChangeOfRings

universe u v₁ v₂ u₁ u₂

/-! ### Transporting invertibility along bijections -/

namespace ModuleCat

/-- **Invertibility of a map of modules transports along bijections of its source and its
target.** Two maps of modules, over two possibly *different* rings, which agree up to a bijection
of their sources and a bijection of their targets, are invertible together.

This is the whole technique by which the two conditions of Stacks 0DJ8 are compared at a point of
a chart. The four local rings of the square of schemes there are isomorphic to, and not equal to,
the local rings of the spectra of the chart's coordinate rings, so the comparison has to move
along ring isomorphisms; moving an `IsIso` statement along them means transporting `ModuleCat`
objects and carrying the resulting `eqToHom`s, whereas the underlying function of a map of
modules does not know which ring acts on it, and a bijection is all that has to be produced. -/
public theorem isIso_iff_isIso_of_bijective_comm {R₁ : Type u₁} {R₂ : Type u₂} [Ring R₁]
    [Ring R₂] {M₁ N₁ : ModuleCat.{v₁} R₁} {M₂ N₂ : ModuleCat.{v₂} R₂} (b₁ : M₁ ⟶ N₁)
    (b₂ : M₂ ⟶ N₂) {θ : M₁ → M₂} (hθ : Function.Bijective θ) {ψ : N₁ → N₂}
    (hψ : Function.Bijective ψ) (hcomm : ∀ m, b₂.hom (θ m) = ψ (b₁.hom m)) :
    IsIso b₁ ↔ IsIso b₂ := by
  rw [ConcreteCategory.isIso_iff_bijective, ConcreteCategory.isIso_iff_bijective]
  calc Function.Bijective (b₁.hom : M₁ → N₁)
      ↔ Function.Bijective (ψ ∘ (b₁.hom : M₁ → N₁)) :=
        (Function.Bijective.of_comp_iff' hψ _).symm
    _ ↔ Function.Bijective ((b₂.hom : M₂ → N₂) ∘ θ) :=
        Iff.of_eq (congrArg Function.Bijective (funext hcomm).symm)
    _ ↔ Function.Bijective (b₂.hom : M₂ → N₂) := Function.Bijective.of_comp_iff _ hθ

end ModuleCat

namespace AlgebraicGeometry

/-! ### The cohomology of a derived stalk over an affine open -/

section AffineOpen

variable {A : CommRingCat.{u}} {X : Scheme.{u}} (i : Spec A ⟶ X)

/-- **The germ-localization of the cohomology of the derived sections is the cohomology of the
derived stalk.** For `i : Spec A ⟶ X` whose germ comparison at `y` is inverted by `ε'` and for
`K` in `D(𝒪_X)` with quasi-coherent cohomology sheaves,

`𝒪_{Spec A, y} ⊗_A H^n(RΓ(U, K))  ≅  H^n(K_{i y})`,

the right-hand side read over `𝒪_{Spec A, y}` along `ε'`.

Two inputs: the germ map is the localization at the prime `y` names, hence flat, so extension of
scalars along it is exact and commutes with cohomology
(`AlgebraicGeometry.flat_specGermRingHom` and
`RingTheory.TorIndependence.flatDerivedHomologyIso`); and the derived localization of `RΓ(U, K)`
is the derived stalk (`AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso`). -/
public def homologyDerivedStalkAffineSectionsRestrictIso (y : Spec A)
    (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (ε' : (Spec A).presheaf.stalk y →+* X.presheaf.stalk (i y))
    (h₁ : ∀ x, ε' ((i.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (i.stalkMap y).hom (ε' z) = z) (n : ℤ) :
    (ModuleCat.extendScalars.{u, u, u} (specGermRingHom A y)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
          ((affineDerivedSections i).obj K)) ≅
      (ModuleCat.restrictScalars.{u, u, u} ε').obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk (i y))) n).obj
          ((derivedStalkFunctor (i y)).obj K)) :=
  ((RingTheory.TorIndependence.flatDerivedHomologyIso.{u, u}
        (specGermRingHom A y) (flat_specGermRingHom A y) n).app
      ((affineDerivedSections i).obj K)).symm ≪≫
    (DerivedCategory.homologyFunctor (ModuleCat.{u} ((Spec A).presheaf.stalk y)) n).mapIso
      (derivedStalkAffineSectionsRestrictIso i y K hK ε' h₁ h₂) ≪≫
    ((ModuleCat.restrictScalars.{u, u, u} ε').mapDerivedCategoryHomologyIso n).app
      ((derivedStalkFunctor (i y)).obj K)

/-- **The two targets agree as sets.** The underlying function of
`AlgebraicGeometry.homologyDerivedStalkAffineSectionsRestrictIso` is a bijection from
`𝒪_{Spec A, y} ⊗_A H^n(RΓ(U, K))` to `H^n(K_{i y})`. This is the form
`ModuleCat.isIso_iff_isIso_of_bijective_comm` consumes: at a chart, with
`i : Spec 𝒪_{X'}(U') ⟶ X'`, the source of this bijection is the target of the germ-localized
chart map of condition (2) of Stacks 0DJ8 and its target is the target of the pointwise map of
condition (1). -/
public theorem bijective_homologyDerivedStalkAffineSectionsRestrictIso (y : Spec A)
    (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (ε' : (Spec A).presheaf.stalk y →+* X.presheaf.stalk (i y))
    (h₁ : ∀ x, ε' ((i.stalkMap y).hom x) = x)
    (h₂ : ∀ z, (i.stalkMap y).hom (ε' z) = z) (n : ℤ) :
    Function.Bijective
      (homologyDerivedStalkAffineSectionsRestrictIso i y K hK ε' h₁ h₂ n).hom.hom :=
  (ConcreteCategory.isIso_iff_bijective
    (f := (homologyDerivedStalkAffineSectionsRestrictIso i y K hK ε' h₁ h₂ n).hom)).mp
      inferInstance

section OpenImmersion

variable [IsOpenImmersion i]

/-- The inverse of the germ comparison of an open immersion inverts it, on elements. -/
public theorem inv_stalkMap_stalkMap_apply (y : Spec A) (x : X.presheaf.stalk (i y)) :
    (inv (i.stalkMap y)).hom ((i.stalkMap y).hom x) = x :=
  IsIso.hom_inv_id_apply (i.stalkMap y) x

/-- The germ comparison of an open immersion inverts its inverse, on elements. -/
public theorem stalkMap_inv_stalkMap_apply (y : Spec A) (z : (Spec A).presheaf.stalk y) :
    (i.stalkMap y).hom ((inv (i.stalkMap y)).hom z) = z :=
  IsIso.inv_hom_id_apply (i.stalkMap y) z

/-- **The derived localization of the derived sections over an affine open is the derived
stalk.** This is `AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso` for `i` an open
immersion, where the inverse of the germ comparison it asks for as data is the categorical
inverse of the germ comparison. -/
public def derivedStalkAffineSectionsInvIso (y : Spec A) (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    (totalDerivedExtensionScalars.{u, u, u} (specGermRingHom A y)).functor.obj
        ((affineDerivedSections i).obj K) ≅
      (ModuleCat.restrictScalars.{u, u, u}
          (inv (i.stalkMap y)).hom).mapDerivedCategory.obj
        ((derivedStalkFunctor (i y)).obj K) :=
  derivedStalkAffineSectionsRestrictIso i y K hK (inv (i.stalkMap y)).hom
    (inv_stalkMap_stalkMap_apply i y) (stalkMap_inv_stalkMap_apply i y)

/-- **The germ-localization of the cohomology of the derived sections is the cohomology of the
derived stalk**, for `i` an open immersion. This is the form in which the comparison of the two
conditions of Stacks 0DJ8 reads it at a chart: `i` is then `Spec 𝒪_{X'}(U') ⟶ X'`, the left-hand
side is the target of the germ-localized chart map of condition (2) and the right-hand side is
the target of the pointwise map of condition (1). -/
public def homologyDerivedStalkAffineSectionsInvIso (y : Spec A)
    (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (n : ℤ) :
    (ModuleCat.extendScalars.{u, u, u} (specGermRingHom A y)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} A) n).obj
          ((affineDerivedSections i).obj K)) ≅
      (ModuleCat.restrictScalars.{u, u, u} (inv (i.stalkMap y)).hom).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} (X.presheaf.stalk (i y))) n).obj
          ((derivedStalkFunctor (i y)).obj K)) :=
  homologyDerivedStalkAffineSectionsRestrictIso i y K hK (inv (i.stalkMap y)).hom
    (inv_stalkMap_stalkMap_apply i y) (stalkMap_inv_stalkMap_apply i y) n

end OpenImmersion

end AffineOpen

/-! ### The pointwise map of Stacks 0DJ7 as a ring-level map -/

section StalkSquare

variable {X X' S S' : Scheme.{u}} (f : X ⟶ S) (g : S' ⟶ S) (f' : X' ⟶ S') (g' : X' ⟶ X)
  (w : g' ≫ f = f' ≫ g) (x' : X')

/-- **The pointwise map of Stacks 0DJ7, on the pure tensors of its source.** For a commutative
square of schemes and a point `x'` of `X'`, the value of
`AlgebraicGeometry.baseChangeCohomologyMap` on `1 ⊗ m` is the cohomology comparison
`RingTheory.TorIndependence.cohomologyComparisonMapGeneral` for the square of the four local rings
of the square at `x'`, applied to the derived stalks of `K` and of `K'` and to the morphism `φ`
transported to the stalks.

This is the defining equation of
`RingTheory.TorIndependence.exists_unique_ringBaseChangeCohomologyMap`, whose map
`baseChangeCohomologyMap` is: the pointwise condition (1) of Stacks 0DJ8 becomes a statement
about a map of `𝒪_{X', x'}`-modules which is computed on the generators `1 ⊗ m` of its source. -/
public theorem baseChangeCohomologyMap_one_tmul
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') (n : ℤ) :
    letI := (f.stalkMap (g' x')).hom.toAlgebra
    letI := (baseStalkMap f g f' g' w x').toAlgebra
    letI := ((g'.stalkMap x').hom.comp (f.stalkMap (g' x')).hom).toAlgebra
    letI := (g'.stalkMap x').hom.toAlgebra
    letI := (f'.stalkMap x').hom.toAlgebra
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' x'))))
        (ToType (X.presheaf.stalk (g' x'))) (ToType (X'.presheaf.stalk x')) :=
      IsScalarTower.of_algebraMap_eq' rfl
    haveI : IsScalarTower (ToType (S.presheaf.stalk (f (g' x'))))
        (ToType (S'.presheaf.stalk (f' x'))) (ToType (X'.presheaf.stalk x')) :=
      IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
    ∀ m : RingTheory.TorIndependence.baseChangeCohomology
        (R := ToType (S.presheaf.stalk (f (g' x'))))
        (R' := ToType (S'.presheaf.stalk (f' x')))
        ((derivedStalkFunctor (g' x')).obj K) n,
      (baseChangeCohomologyMap f g f' g' w K K' φ x' n).hom
          ((1 : ToType (X'.presheaf.stalk x')) ⊗ₜ[
              ToType (X.presheaf.stalk (g' x')) ⊗[ToType (S.presheaf.stalk (f (g' x')))]
                ToType (S'.presheaf.stalk (f' x')),
              RingTheory.TorIndependence.baseChangeTensorRingMap] m) =
        (RingTheory.TorIndependence.cohomologyComparisonMapGeneral
            (R := ToType (S.presheaf.stalk (f (g' x'))))
            (R' := ToType (S'.presheaf.stalk (f' x')))
            ((derivedStalkFunctor (g' x')).obj K) ((derivedStalkFunctor x').obj K')
            ((derivedPullbackStalkIso g' x').inv.app K ≫
              (derivedStalkFunctor x').map φ) n).hom m := by
  let := (f.stalkMap (g' x')).hom.toAlgebra
  let := (baseStalkMap f g f' g' w x').toAlgebra
  let := ((g'.stalkMap x').hom.comp (f.stalkMap (g' x')).hom).toAlgebra
  let := (g'.stalkMap x').hom.toAlgebra
  let := (f'.stalkMap x').hom.toAlgebra
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' x'))))
      (ToType (X.presheaf.stalk (g' x'))) (ToType (X'.presheaf.stalk x')) :=
    IsScalarTower.of_algebraMap_eq' rfl
  have : IsScalarTower (ToType (S.presheaf.stalk (f (g' x'))))
      (ToType (S'.presheaf.stalk (f' x'))) (ToType (X'.presheaf.stalk x')) :=
    IsScalarTower.of_algebraMap_eq' (stalkMap_square f g f' g' w x')
  exact Classical.choose_spec
    (RingTheory.TorIndependence.exists_unique_ringBaseChangeCohomologyMap
      (R := ToType (S.presheaf.stalk (f (g' x'))))
      (A := ToType (X.presheaf.stalk (g' x')))
      (R' := ToType (S'.presheaf.stalk (f' x')))
      (A' := ToType (X'.presheaf.stalk x'))
      ((derivedStalkFunctor (g' x')).obj K) ((derivedStalkFunctor x').obj K')
      ((derivedPullbackStalkIso g' x').inv.app K ≫ (derivedStalkFunctor x').map φ) n).exists

/-- **Condition (1) of Stacks 0DJ8 at one point and in one degree is a bijectivity statement.**
The pointwise map of Stacks 0DJ7 at `x'` is invertible exactly when its underlying function is
bijective.

This is the shape in which the comparison with condition (2) is carried out: the four local rings
of the square at a point of a chart's open `U'` are isomorphic to, and not equal to, the local
rings of the spectra of the chart's coordinate rings, so the comparison has to move along ring
isomorphisms, and a bijection of underlying functions moves along them with no transport of
module structures at all. -/
public theorem isIso_baseChangeCohomologyMap_iff_bijective
    (K : DerivedCategory X.Modules) (K' : DerivedCategory X'.Modules)
    (φ : (Stacks.Duality.derivedPullback g').obj K ⟶ K') (n : ℤ) :
    IsIso (baseChangeCohomologyMap f g f' g' w K K' φ x' n) ↔
      Function.Bijective (baseChangeCohomologyMap f g f' g' w K K' φ x' n).hom :=
  ConcreteCategory.isIso_iff_bijective _

end StalkSquare

end AlgebraicGeometry

end
