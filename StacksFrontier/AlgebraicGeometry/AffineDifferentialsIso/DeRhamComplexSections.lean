module

public import StacksFrontier.AlgebraicGeometry.DeRham.SchemeComplex

/-!
# The base ring of a complex of sheaves of `f⁻¹𝒪_S`-modules

The relative de Rham complex `Ω^•_{X/S}` of a morphism of schemes `f : X ⟶ S`
(`AlgebraicGeometry.Scheme.Hom.deRhamComplex`) is a complex of sheaves of `f⁻¹𝒪_S`-modules, not
of `𝒪_X`-modules: the de Rham differential is only linear over the base. Its global sections are
therefore a module over `Γ(X, f⁻¹𝒪_S)`, which is the ring
`AlgebraicGeometry.SheafOfModules.deRhamCohomology` is stated over, and *not* over the ring
`Γ(S, 𝒪_S)` of functions on the base.

This file supplies the ring map that relates the two, which is what lets sections of a sheaf of
`f⁻¹𝒪_S`-modules be read as modules over the base.

## Main definitions

* `AlgebraicGeometry.Scheme.Hom.inverseImageRingSheaf`: the sheaf of rings `f⁻¹𝒪_S`.
* `AlgebraicGeometry.Scheme.Hom.inverseImageSectionsMap`: **the ring map
  `Γ(S, 𝒪_S) ⟶ Γ(X, f⁻¹𝒪_S)`** — the unit of `f⁻¹ ⊣ f_*` at `𝒪_S`, read on global sections.
* `AlgebraicGeometry.Scheme.Hom.affineBaseRingMap`: **the ring map
  `R ⟶ Γ(Spec A, (Spec φ)⁻¹𝒪_{Spec R})`** for a morphism of affine schemes `Spec φ`, with the
  base ring spelled `R` rather than `Γ(Spec R, 𝒪)`.

## Implementation notes

**This is a ring map, not an isomorphism, and it cannot be one.** `Γ(X, f⁻¹𝒪_S)` is not
`Γ(S, 𝒪_S)` in general: already for `X` the disjoint union of two copies of `S` and `f` the fold
map, `f⁻¹𝒪_S` has `Γ(S,𝒪_S) × Γ(S,𝒪_S)` as its global sections. So the base-module structure on
sections of a sheaf of `f⁻¹𝒪_S`-modules is restriction of scalars along the map here, and no
isomorphism is claimed. The map is the unit of the adjunction `f⁻¹ ⊣ f_*`, which is the only
canonical comparison available in that direction.

The unit component lands in the sections of `f⁻¹𝒪_S` over `(Opens.map f.base).obj ⊤`, which is
`⊤` by `TopologicalSpace.Opens.map_top`, a `rfl`; the crossing is left to unification in term
position rather than transported with `eqToHom`. The presheaf-level natural transformation of a
morphism of `TopCat.Sheaf`es is extracted with `CategoryTheory.sheafToPresheaf`, because
`TopCat.Sheaf` carries an induced category structure and the field projection `.val` is not
available on its morphisms.

## What is not done here

The *functor* `Γ(X, -) : SheafOfModules (f⁻¹𝒪_S) ⥤ ModuleCat Γ(S,𝒪_S)` is not constructed in this
file, but it **is** available in the library, as
`Stacks.Cohomology.DerivedSectionsLeray.preimageSections (inverseImageBaseProjection f) ⊤` of
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.LerayForDerivedSections`, whose
source is `Stacks.DeRhamDirectImage.Modules (inverseImageBase f)` — the category the relative de
Rham complex lives in — and whose target is `ModuleCat Γ(S, 𝒪_S)`, the identification of
`(ringSheaf S.toRingedSpace).obj.obj (op ⊤)` with `Γ(S, ⊤)` being a `rfl`. It is additive
(`preimageSections_additive`), so its lift to cochain complexes along
`CategoryTheory.Functor.mapHomologicalComplex` exists as well and carries `Ω^•_{X/S}` to a
cochain complex of `Γ(S, 𝒪_S)`-modules.

There is **no universe obstruction** to either, and in particular none to the composite
`Stacks.Cohomology.DerivedSectionsLeray.sectionsOverOpen` of
`AlgebraicGeometry.SheafOfModules.baseRingedSpace` followed by a restriction of scalars: that
composite elaborates at `RingedSpace.{u, u}`, and the only thing a caller must supply for its
complex-level lift is an `Additive` instance, which holds by `map_add := rfl`. What is genuinely
awkward is `SheafOfModules.evaluation`, which takes its site as `{C : Type u'} [Category.{v'} C]
{J : GrothendieckTopology C}` with the two site universes independent: instantiated at
`Opens X.carrier` for `X : Scheme.{u}` and at the pulled-back ring sheaf, the elaborator is left
with a constraint of the form `max ?u ?v =?= u` coming from `TopCat.Sheaf`'s three universes and
reports `stuck at solving universe constraint`. The universe-specialised sections functor for
`Opens`-sites that avoids this is exactly `sectionsOverOpen`, and it is what the Leray file uses.

Tag 0FLW is nevertheless **not** closed by this file, and no declaration here carries a
`@[stacks 0FLW]` attribute: the three definitions above are a ring map and the two sheaves it is
read on, none of which is a clause of the tag.

**Where the tag is proved.** Both of its assertions are proved in
`StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamDerived` —
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.derivedDeRhamSectionsIso` for
`RΓ(Spec A, Ω^•_{Spec A/Spec R}) ≅ Ω^•_{A/R}` in `D(R)`, and
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.deRhamCohomologyIsoInt` for the resulting
statement about de Rham cohomology. The `R`-module structure on the left-hand side is taken
along `affineBaseRingMap` above, so this file supplies the comparison through which the derived
statement is read; the two steps between are the complex-level comparison
`Stacks.AlgebraicGeometry.AffineDifferentialsIso.deRhamSectionsComplexIso` of
`StacksFrontier.AlgebraicGeometry.AffineDifferentialsIso.DeRhamComplexComparison` and the passage
from `Γ` to `RΓ` by Leray's acyclicity lemma, which is
`Stacks.Cohomology.DerivedSectionsOverBase.isIso_sectionsOverComplexComparison_app` in
`StacksFrontier.Topology.Sheaves.Cohomology.DerivedPushforward.SectionsOverBaseComplexComparison`.

## References

* [Stacks Project, Tag 0FKQ](https://stacks.math.columbia.edu/tag/0FKQ)
* [Stacks Project, Tag 0FLW](https://stacks.math.columbia.edu/tag/0FLW)
* [Stacks Project, Tag 0D5W](https://stacks.math.columbia.edu/tag/0D5W)
-/

@[expose] public noncomputable section

open CategoryTheory Opposite TopologicalSpace

universe u

namespace AlgebraicGeometry.Scheme.Hom

variable {X S : Scheme.{u}} (f : X ⟶ S)

/-- The sheaf of rings `f⁻¹𝒪_S` on `X`: the sheaf of rings the relative de Rham complex of `f`
is a complex of modules over. -/
abbrev inverseImageRingSheaf : TopCat.Sheaf CommRingCat.{u} X.carrier :=
  (TopCat.Sheaf.pullback CommRingCat.{u} f.base).obj S.sheaf

/-- **The ring map `Γ(S, 𝒪_S) ⟶ Γ(X, f⁻¹𝒪_S)`**: the unit of the adjunction `f⁻¹ ⊣ f_*` at
`𝒪_S`, read on global sections.

It is not an isomorphism in general, and it is what makes global sections of a sheaf of
`f⁻¹𝒪_S`-modules — in particular the terms of the relative de Rham complex — into modules over
the ring of functions on the base. -/
def inverseImageSectionsMap :
    S.sheaf.obj.obj (op ⊤) ⟶ (inverseImageRingSheaf f).obj.obj (op ⊤) :=
  ((sheafToPresheaf (Opens.grothendieckTopology S.carrier) CommRingCat.{u}).map
    ((TopCat.Sheaf.pullbackPushforwardAdjunction CommRingCat.{u} f.base).unit.app
      S.sheaf)).app (op ⊤)

section Affine

variable {R A : CommRingCat.{u}} (φ : R ⟶ A)

/-- **The base ring map of a morphism of affine schemes**,
`R ⟶ Γ(Spec A, (Spec φ)⁻¹𝒪_{Spec R})`: the identification `R ≅ Γ(Spec R, 𝒪)` followed by
`inverseImageSectionsMap`.

This is the comparison that reads the terms of the relative de Rham complex of `Spec φ` as
`R`-modules, which is the form [Stacks Project, Tag 0FLW] compares with the de Rham complex
`Ω^•_{A/R}` of the coordinate rings. -/
def affineBaseRingMap :
    R ⟶ (inverseImageRingSheaf (Spec.map φ)).obj.obj (op ⊤) :=
  (Scheme.ΓSpecIso R).inv ≫ inverseImageSectionsMap (Spec.map φ)

end Affine

end AlgebraicGeometry.Scheme.Hom

end
