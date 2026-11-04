module

public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineChartStalkAlgebra
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.AffineOpenDerivedStalk
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologyFlatExtension
public import
  StacksFrontier.AlgebraicGeometry.BaseChange.TorIndependence.BaseChangeCohomologyFlatRing
public import StacksFrontier.Homology.Tor.BaseChangeCohomologyDevissage
public import StacksFrontier.Homology.Tor.DerivedBaseChangeSquareLocalization

/-!
# The two source corners of the cube of localizations, at a chart, on cohomology

`AlgebraicGeometry.BaseChangeChart.squareComparison_localRings` reads the Tag 065Z comparison of
the four local rings of a chart at a point `y` of `Spec 𝒪_{X'}(U')` as the chart's own comparison,
through `RingTheory.TorIndependence.localizedSquareDomainIso` on the source. That identification
is a statement in the derived category; the affine reduction of Stacks 0DJ8 consumes it on
cohomology, where the two *source* corners `𝒪_S(V) → 𝒪_{S, f(g' x')}` and
`𝒪_X(U) → 𝒪_{X, g' x'}` of the cube have to be moved one at a time. This module supplies the two
moves and the geometric input they need.

*The `𝒪_{S'}(V')` corner.* The germ map `𝒪_{S'}(V') → 𝒪_{S', f' x'}` is a localization, hence
flat, so it passes through cohomology: the base-change cohomology of the chart taken directly
over `𝒪_{S', f' x'}` is `𝒪_{S', f' x'} ⊗_{𝒪_{S'}(V')}` of the one taken over `𝒪_{S'}(V')`. This
is `RingTheory.TorIndependence.flatCompDerivedHomologyIso` supplied with
`AlgebraicGeometry.BaseChangeChart.flat_toStalkR'`.

*The `𝒪_X(U)` corner.* The germ map `𝒪_X(U) → 𝒪_{Spec 𝒪_X(U), q}` is a localization too, but it
occupies the *module* slot of the derived base change rather than the ring slot, so no flatness
argument reaches it; the statement that it passes through base-change cohomology is the dévissage
`RingTheory.TorIndependence.localizedBaseChangeCohomologyIso`. Supplying it at the chart asks for
the complex `RΓ(U, K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{Spec 𝒪_X(U), q}` to be the derived stalk of `K` at `g' x'`,
which is `AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso` — except that the latter is
stated at the point `ch.incU q` of `X`, whereas the chart's four local rings, and so
`AlgebraicGeometry.baseChangeCohomologyMap`, are at `g' x'`. The two points are equal, by
`AlgebraicGeometry.BaseChangeChart.apply_g'_incU'`, and the comparison of the stalks at them is
`AlgebraicGeometry.BaseChangeChart.stalkCompA`; `derivedStalkAffineSectionsCongrIso` below is the
derived stalk identification stated at a point given together with such an equality, which is
what lets the chart read it at `g' x'` with no transport left over.

## Main definitions

* `AlgebraicGeometry.derivedStalkAffineSectionsCongrIso`: the derived localization of the derived
  sections over an affine open, at a point of `X` presented as the image of a point of `Spec A`
  through an equality of points.
* `AlgebraicGeometry.BaseChangeChart.germDerivedStalkSectionsIso`: that identification at a
  chart, at the point `g' x'` and along the inverse of the chart's comparison at `U`.
* `AlgebraicGeometry.BaseChangeChart.restrictGermDerivedStalkSectionsIso`: the same read over
  `𝒪_X(U)`, which is the slot `localizedBaseChangeCohomologyIso` and
  `localizedSquareDomainIso` both use.
* `AlgebraicGeometry.BaseChangeChart.homologyBaseChangeLocalizedIso`: the `𝒪_{S'}(V')` corner.
* `AlgebraicGeometry.BaseChangeChart.germBaseChangeCohomologyIso`: the `𝒪_X(U)` corner.

## Main results

* `AlgebraicGeometry.BaseChangeChart.germBaseChangeCohomologyIso_hom_includeRight_smul`: the
  `𝒪_X(U)` corner move is equivariant for the right tensor factor `𝒪_{S', f' x'}`. The move is an
  isomorphism of `𝒪_{Spec 𝒪_X(U), q}`-modules by construction, which is only half of the
  linearity the comparison of the two conditions of Stacks 0DJ8 consumes: the source of the
  pointwise map of Stacks 0DJ7 at `x'` is a module over the whole of
  `𝒪_{X, g' x'} ⊗_{𝒪_{S, f(g' x')}} 𝒪_{S', f' x'}`. The `𝒪_{S'}(V')` corner carries its own
  `𝒪_{S', f' x'}`-linearity, being an isomorphism of `𝒪_{S', f' x'}`-modules; its
  `𝒪_X(U)`-equivariance is the naturality of
  `RingTheory.TorIndependence.flatCompDerivedHomologyIso` at `a • 𝟙`, in the manner of
  `RingTheory.TorIndependence.baseChangeCohomologyRestrictMap_includeLeft_smul`, and is not
  recorded here.

## Implementation notes

`derivedStalkAffineSectionsCongrIso` takes the point `z` of `X` and the equality `z = i w` as
separate arguments rather than specializing to `z = i w`: with `z` a variable the equality can be
substituted, and after the substitution the specialization isomorphism of the two stalks is the
identity and the statement is `AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso`. Stated
directly at `i w` it would carry the specialization isomorphism of
`AlgebraicGeometry.BaseChangeChart.stalkCompA` as an irreducible factor.

The inverse of the comparison at `U` is taken as data — a ring map together with the two
equations inverting it — exactly as `derivedStalkAffineSectionsRestrictIso` takes the inverse of
the germ comparison, and is instantiated at the categorical inverse of
`AlgebraicGeometry.BaseChangeChart.stalkCompAIso`.

The two corners are stated at the algebra structures the chart's own ring maps provide, written
out as `letI` in the statements rather than named: `ch.toStalkR'` for `𝒪_{S'}(V') → 𝒪_{S', f' x'}`
and the germ map for `𝒪_X(U) → 𝒪_{Spec 𝒪_X(U), q}`, with `𝒪_S(V) → 𝒪_{S', f' x'}` spelled as the
composite through `𝒪_{S'}(V')`. `AlgebraicGeometry.BaseChangeChart.toStalkR'_b` is what identifies
that spelling with the one `localizedSquareDomainIso` uses, which goes through `𝒪_{S, f(g' x')}`.

No tag attribute is placed here. Nothing below is a clause of Stacks 0DJ8: these are the two
corner moves its affine reduction consumes, and the tag belongs on the three-way equivalence.

## References

* [Stacks Project, Tag 00HN](https://stacks.math.columbia.edu/tag/00HN)
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
open CochainComplex.DerivedExtensionScalars
open scoped TensorProduct ChangeOfRings

universe u

namespace AlgebraicGeometry

/-- **The derived localization of the derived sections over an affine open, at a point of `X`
presented through an equality of points.** For `i : Spec A ⟶ X` an open immersion, `w` a point of
`Spec A` and `z` a point of `X` with `z = i w`,

`RΓ(U, K) ⊗ᴸ_A 𝒪_{Spec A, w}  ≅  K_z`,

the right-hand side read over `𝒪_{Spec A, w}` along a given inverse `ε` of the comparison
`𝒪_{X, z} ⟶ 𝒪_{Spec A, w}` — the specialization isomorphism of the stalks at `z` and `i w`
followed by the germ comparison of `i` at `w`.

This is `AlgebraicGeometry.derivedStalkAffineSectionsRestrictIso` with the point of `X` left
free: substituting the equality makes the specialization isomorphism the identity. -/
public def derivedStalkAffineSectionsCongrIso {A : CommRingCat.{u}} {X : Scheme.{u}}
    (i : Spec A ⟶ X) [IsOpenImmersion i] (w : Spec A) (z : X) (hz : z = i w)
    (K : DerivedCategory X.Modules)
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent)
    (ε : ToType ((Spec A).presheaf.stalk w) →+* ToType (X.presheaf.stalk z))
    (k₁ : ∀ t, ε (((X.presheaf.stalkCongr (.of_eq hz)).hom ≫ i.stalkMap w).hom t) = t)
    (k₂ : ∀ v, ((X.presheaf.stalkCongr (.of_eq hz)).hom ≫ i.stalkMap w).hom (ε v) = v) :
    (totalDerivedExtensionScalars.{u, u, u} (specGermRingHom A w)).functor.obj
        ((affineDerivedSections i).obj K) ≅
      (ModuleCat.restrictScalars.{u, u, u} ε).mapDerivedCategory.obj
        ((derivedStalkFunctor z).obj K) := by
  subst hz
  refine derivedStalkAffineSectionsRestrictIso i w K hK ε ?_ ?_
  · intro t
    simpa using k₁ t
  · intro v
    simpa using k₂ v

namespace BaseChangeChart

variable {X X' S S' : Scheme.{u}} {f : X ⟶ S} {g : S' ⟶ S} {f' : X' ⟶ S'} {g' : X' ⟶ X}
  (ch : BaseChangeChart f g f' g') (y : Spec ch.A') (K : DerivedCategory X.Modules)

/-- **The derived sections of a chart, localized at a point of `Spec 𝒪_X(U)`, are the derived
stalk at `g' x'`.** For `K` with quasi-coherent cohomology sheaves,

`RΓ(U, K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{Spec 𝒪_X(U), q}  ≅  K_{g' x'}`,

where `q = Spec(c) y`, the right-hand side read over `𝒪_{Spec 𝒪_X(U), q}` along the inverse of
the chart's comparison at `U`.

This is `AlgebraicGeometry.derivedStalkAffineSectionsCongrIso` at the point `g' x'`, which the
chart presents as `ch.incU q`; stating it there rather than at `ch.incU q` is what puts it over
the same local ring as the chart's `ch.toStalkA` and so as
`AlgebraicGeometry.baseChangeCohomologyMap`. -/
public def germDerivedStalkSectionsIso
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    (totalDerivedExtensionScalars.{u, u, u}
          (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
        ((affineDerivedSections ch.incU).obj K) ≅
      (ModuleCat.restrictScalars.{u, u, u} (ch.stalkCompAIso y).inv.hom).mapDerivedCategory.obj
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) :=
  haveI := ch.isOpenImmersion_incU
  derivedStalkAffineSectionsCongrIso ch.incU (Spec.map ch.c y) (g' (ch.incU' y))
    (ch.apply_g'_incU' y) K hK (ch.stalkCompAIso y).inv.hom
    (commRingCatIso_inv_hom_apply (ch.stalkCompAIso y))
    (commRingCatIso_hom_inv_apply (ch.stalkCompAIso y))

/-- **The same identification read over `𝒪_X(U)`.** Restricting
`AlgebraicGeometry.BaseChangeChart.germDerivedStalkSectionsIso` along the germ map merges the two
restrictions of scalars into the chart's own `ch.toStalkA`, so the right-hand side is the derived
stalk of `K` at `g' x'` read over `𝒪_X(U)` exactly as
`RingTheory.TorIndependence.localizedSquareDomainIso` reads it.

This is the form in which the `𝒪_X(U)` corner of
`AlgebraicGeometry.BaseChangeChart.germBaseChangeCohomologyIso` meets
`AlgebraicGeometry.BaseChangeChart.squareComparison_localRings`. -/
public def restrictGermDerivedStalkSectionsIso
    (hK : ∀ n : ℤ, ((DerivedCategory.homologyFunctor X.Modules n).obj K).IsQuasicoherent) :
    (ModuleCat.restrictScalars.{u}
          (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.obj
        ((totalDerivedExtensionScalars.{u, u, u}
            (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
          ((affineDerivedSections ch.incU).obj K)) ≅
      (ModuleCat.restrictScalars.{u} (ch.toStalkA y)).mapDerivedCategory.obj
        ((derivedStalkFunctor (g' (ch.incU' y))).obj K) :=
  (ModuleCat.restrictScalars.{u}
        (specGermRingHom ch.A (Spec.map ch.c y))).mapDerivedCategory.mapIso
      (ch.germDerivedStalkSectionsIso y K hK) ≪≫
    (RingTheory.TorIndependence.mapDerivedCategoryCompNatIso
      (ModuleCat.restrictScalars.{u} (ch.stalkCompAIso y).inv.hom)
      (ModuleCat.restrictScalars.{u} (specGermRingHom ch.A (Spec.map ch.c y)))
      (ModuleCat.restrictScalars.{u} (ch.toStalkA y))
      (ModuleCat.restrictScalarsComp'.{u} (specGermRingHom ch.A (Spec.map ch.c y))
        (ch.stalkCompAIso y).inv.hom (ch.toStalkA y) rfl).symm).app
      ((derivedStalkFunctor (g' (ch.incU' y))).obj K)

/-- **The `𝒪_{S'}(V')` corner of the cube, on cohomology.** The germ map
`𝒪_{S'}(V') → 𝒪_{S', f' x'}` is the localization at the prime of `f' x'`, hence flat, so

`H^n(RΓ(U,K)|_{𝒪_S(V)} ⊗ᴸ_{𝒪_S(V)} 𝒪_{S', f' x'})  ≅
  𝒪_{S', f' x'} ⊗_{𝒪_{S'}(V')} H^n(RΓ(U,K)|_{𝒪_S(V)} ⊗ᴸ_{𝒪_S(V)} 𝒪_{S'}(V'))`.

The right-hand side is the germ localization of the chart's base-change cohomology and the
left-hand side is the base-change cohomology taken directly over the local ring of `S'`, which is
the corner `RingTheory.TorIndependence.localizedSquareDomainIso` leaves to be moved. -/
public def homologyBaseChangeLocalizedIso (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (S'.presheaf.stalk (f' (ch.incU' y)))) n).obj
        ((totalDerivedExtensionScalars.{u, u, u}
            ((ch.toStalkR' y).comp ch.b.hom)).functor.obj
          ((ModuleCat.restrictScalars.{u} ch.a.hom).mapDerivedCategory.obj
            ((affineDerivedSections ch.incU).obj K))) ≅
      (ModuleCat.extendScalars.{u, u, u} (ch.toStalkR' y)).obj
        ((DerivedCategory.homologyFunctor (ModuleCat.{u} ch.R') n).obj
          ((totalDerivedExtensionScalars.{u, u, u} ch.b.hom).functor.obj
            ((ModuleCat.restrictScalars.{u} ch.a.hom).mapDerivedCategory.obj
              ((affineDerivedSections ch.incU).obj K)))) :=
  letI := ch.a.hom.toAlgebra
  letI := ch.b.hom.toAlgebra
  letI := (ch.toStalkR' y).toAlgebra
  letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  (RingTheory.TorIndependence.flatCompDerivedHomologyIso.{u, u} ch.b.hom (ch.toStalkR' y)
      (ch.flat_toStalkR' y) n).app
    ((ModuleCat.restrictScalars.{u} ch.a.hom).mapDerivedCategory.obj
      ((affineDerivedSections ch.incU).obj K))

/-- **The `𝒪_{S'}(V')` corner move is equivariant for `𝒪_X(U)`.**
`AlgebraicGeometry.BaseChangeChart.homologyBaseChangeLocalizedIso` is an isomorphism of
`𝒪_{S', f' x'}`-modules by construction; this is the other half of the linearity the comparison
of the two conditions of Stacks 0DJ8 consumes, namely that it carries the action of the left
tensor factor `𝒪_X(U)` of `𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S', f' x'}` to the germ localization of the
action of the left tensor factor of `𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S'}(V')`.

This is `RingTheory.TorIndependence.flatCompDerivedHomologyIso_app_includeLeft_smul` at the
chart's algebra structures. -/
public theorem homologyBaseChangeLocalizedIso_hom_includeLeft_smul (n : ℤ) (a : ch.A) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    ∀ m : RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((affineDerivedSections ch.incU).obj K) n,
      (ch.homologyBaseChangeLocalizedIso y K n).hom.hom
          ((Algebra.TensorProduct.includeLeft (R := ch.R) (S := ch.R) a :
            ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) • m) =
        ((ModuleCat.extendScalars.{u, u, u} (ch.toStalkR' y)).map
            ((RingTheory.TorIndependence.derivedBaseChangeFunctor (R := ch.R) (A := ch.A)
                (R' := ch.R') ⋙
              DerivedCategory.homologyFunctor (ModuleCat.{u} ch.R') n).map
              (a • 𝟙 ((affineDerivedSections ch.incU).obj K)))).hom
          ((ch.homologyBaseChangeLocalizedIso y K n).hom.hom m) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := (ch.toStalkR' y).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  exact RingTheory.TorIndependence.flatCompDerivedHomologyIso_app_includeLeft_smul
    (ch.flat_toStalkR' y) n ((affineDerivedSections ch.incU).obj K) a

/-- **The `𝒪_X(U)` corner of the cube, on cohomology.** The germ map
`𝒪_X(U) → 𝒪_{Spec 𝒪_X(U), q}` is a localization, so by the dévissage
`RingTheory.TorIndependence.localizedBaseChangeCohomologyIso`

`𝒪_{Spec 𝒪_X(U), q} ⊗_{𝒪_X(U)} H^n(RΓ(U,K)|_{𝒪_S(V)} ⊗ᴸ_{𝒪_S(V)} 𝒪_{S', f' x'})  ≅
  H^n((RΓ(U,K) ⊗ᴸ_{𝒪_X(U)} 𝒪_{Spec 𝒪_X(U), q})|_{𝒪_S(V)} ⊗ᴸ_{𝒪_S(V)} 𝒪_{S', f' x'})`,

both sides read over `𝒪_{Spec 𝒪_X(U), q}` through the left tensor inclusion. Unlike the
`𝒪_{S'}(V')` corner this is not a flatness statement: there the localized ring occupies the ring
slot of the derived base change, here the varying complex lives over it and the localization sits
in the module slot.

The complex on the right is the derived stalk of `K` at `g' x'`, by
`AlgebraicGeometry.BaseChangeChart.germDerivedStalkSectionsIso`. -/
public def germBaseChangeCohomologyIso (n : ℤ) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
    letI := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A
        (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    (ModuleCat.extendScalars.{u, u, u} (specGermRingHom ch.A (Spec.map ch.c y))).obj
        ((ModuleCat.restrictScalars.{u}
            (RingTheory.TorIndependence.includeLeftRingHom ch.R ch.A
              (ToType (S'.presheaf.stalk (f' (ch.incU' y)))))).obj
          (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
            (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
            ((affineDerivedSections ch.incU).obj K) n)) ≅
      (ModuleCat.restrictScalars.{u}
          (RingTheory.TorIndependence.includeLeftRingHom
            ch.R (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
            (ToType (S'.presheaf.stalk (f' (ch.incU' y)))))).obj
        (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
          (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
          ((totalDerivedExtensionScalars.{u, u, u}
              (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
            ((affineDerivedSections ch.incU).obj K)) n) :=
  letI := ch.a.hom.toAlgebra
  letI := ch.b.hom.toAlgebra
  letI := (ch.toStalkR' y).toAlgebra
  letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  letI := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
  haveI : IsScalarTower ch.R ch.A
      (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  RingTheory.TorIndependence.localizedBaseChangeCohomologyIso
    (flat_specGermRingHom ch.A (Spec.map ch.c y)) n
    ((affineDerivedSections ch.incU).obj K)

/-- **The `𝒪_X(U)` corner move is equivariant for `𝒪_{S', f' x'}`.** On the generators
`x • (1 ⊗ m)` of its source, `AlgebraicGeometry.BaseChangeChart.germBaseChangeCohomologyIso`
carries the action of the right tensor factor `𝒪_{S', f' x'}` of
`𝒪_X(U) ⊗_{𝒪_S(V)} 𝒪_{S', f' x'}` to the action of the right tensor factor of
`𝒪_{Spec 𝒪_X(U), q} ⊗_{𝒪_S(V)} 𝒪_{S', f' x'}`.

The corner move is an isomorphism of `𝒪_{Spec 𝒪_X(U), q}`-modules by construction, and the
source of the pointwise map of Stacks 0DJ7 at `x'` is a module over the whole of
`𝒪_{X, g' x'} ⊗_{𝒪_{S, f(g' x')}} 𝒪_{S', f' x'}`; so the comparison of the two conditions of
Stacks 0DJ8 needs this second half of the linearity as well. It is
`RingTheory.TorIndependence.localizedBaseChangeCohomologyComparison_app_includeRight_smul` at the
chart's algebra structures. -/
public theorem germBaseChangeCohomologyIso_hom_includeRight_smul (n : ℤ)
    (x : ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
    (r : ToType (S'.presheaf.stalk (f' (ch.incU' y)))) :
    letI := ch.a.hom.toAlgebra
    letI := ch.b.hom.toAlgebra
    letI := (ch.toStalkR' y).toAlgebra
    letI := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
    letI := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
    letI := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
    haveI : IsScalarTower ch.R ch.A
        (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
      IsScalarTower.of_algebraMap_eq' rfl
    ∀ m : RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
        ((affineDerivedSections ch.incU).obj K) n,
      (ch.germBaseChangeCohomologyIso y K n).hom.hom
          (x • (show (ModuleCat.extendScalars.{u, u, u}
              (specGermRingHom ch.A (Spec.map ch.c y))).obj
                ((ModuleCat.restrictScalars.{u}
                    (RingTheory.TorIndependence.includeLeftRingHom ch.R ch.A
                      (ToType (S'.presheaf.stalk (f' (ch.incU' y)))))).obj
                  (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
                    (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                    ((affineDerivedSections ch.incU).obj K) n)) from
            (1 : ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
              ⊗ₜ[ch.A, specGermRingHom ch.A (Spec.map ch.c y)]
              (show (ModuleCat.restrictScalars.{u}
                  (RingTheory.TorIndependence.includeLeftRingHom ch.R ch.A
                    (ToType (S'.presheaf.stalk (f' (ch.incU' y)))))).obj
                (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
                  (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                  ((affineDerivedSections ch.incU).obj K) n) from
                (Algebra.TensorProduct.includeRight r :
                  ch.A ⊗[ch.R] ToType (S'.presheaf.stalk (f' (ch.incU' y)))) • m))) =
        (Algebra.TensorProduct.includeRight r :
              ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)) ⊗[ch.R]
                ToType (S'.presheaf.stalk (f' (ch.incU' y)))) •
          (show RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
              (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
              ((totalDerivedExtensionScalars.{u, u, u}
                  (specGermRingHom ch.A (Spec.map ch.c y))).functor.obj
                ((affineDerivedSections ch.incU).obj K)) n from
            (ch.germBaseChangeCohomologyIso y K n).hom.hom
              (x • (show (ModuleCat.extendScalars.{u, u, u}
                  (specGermRingHom ch.A (Spec.map ch.c y))).obj
                    ((ModuleCat.restrictScalars.{u}
                        (RingTheory.TorIndependence.includeLeftRingHom ch.R ch.A
                          (ToType (S'.presheaf.stalk (f' (ch.incU' y)))))).obj
                      (RingTheory.TorIndependence.baseChangeCohomology (R := ch.R)
                        (R' := ToType (S'.presheaf.stalk (f' (ch.incU' y))))
                        ((affineDerivedSections ch.incU).obj K) n)) from
                (1 : ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y)))
                  ⊗ₜ[ch.A, specGermRingHom ch.A (Spec.map ch.c y)] m))) := by
  let := ch.a.hom.toAlgebra
  let := ch.b.hom.toAlgebra
  let := (ch.toStalkR' y).toAlgebra
  let := ((ch.toStalkR' y).comp ch.b.hom).toAlgebra
  let := (specGermRingHom ch.A (Spec.map ch.c y)).toAlgebra
  let := ((specGermRingHom ch.A (Spec.map ch.c y)).comp ch.a.hom).toAlgebra
  have : IsScalarTower ch.R ch.A
      (ToType ((Spec ch.A).presheaf.stalk (Spec.map ch.c y))) :=
    IsScalarTower.of_algebraMap_eq' rfl
  intro m
  exact RingTheory.TorIndependence.localizedBaseChangeCohomologyComparison_app_includeRight_smul
    n ((affineDerivedSections ch.incU).obj K) x r m

end BaseChangeChart

end AlgebraicGeometry

end
