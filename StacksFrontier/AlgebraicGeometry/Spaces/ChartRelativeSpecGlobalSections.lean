module

public import StacksFrontier.AlgebraicGeometry.Spaces.ChartOpenRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecChartMapComp
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRelativeSpecUniversalProperty

/-!
# The global sections of the relative spectrum over a chart, naturally in the chart

Let `X` be an algebraic space over `S`, let `A` be a quasi-coherent sheaf of commutative
`𝒪_X`-algebras on its small étale site and let `V` be an étale scheme chart of `X`.
`AlgebraicGeometry.Space.chartRelativeSpecPushforwardIso` identifies the direct image of the
structure sheaf of `\underline{Spec}_{V}(A|_V)` with the chart restriction `A|_{chartScheme V}`,
as sheaves of algebras on the Zariski site of `chartScheme V`.  Read at the top open that says

`Γ(\underline{Spec}_{V}(A|_V), 𝒪) ≅ A(V)`,

and this file proves that identification **natural in `V`**: the morphism of relative spectra
`AlgebraicGeometry.Space.chartRelativeSpecChartMap` attached to a morphism `h : V' ⟶ V` of charts
induces, on global sections, the restriction map `A(V) ⟶ A(V')` of `A`.

## Main definitions

* `AlgebraicGeometry.Space.openChartTopIso`: the étale chart cut out of `V` by the top open of
  `chartScheme V` is `V` itself.
* `Stacks.RelativeSpec.AlgebraSheaf.sectionsIso`: the ring isomorphism on sections over a Zariski
  open induced by an isomorphism of sheaves of algebras.
* `AlgebraicGeometry.Space.chartRelativeSpecSectionsIso`: **the identification
  `A(V) ≅ Γ(\underline{Spec}_{V}(A|_V), 𝒪)`.**

## Main results

* `AlgebraicGeometry.Space.Γ_map_chartRelativeSpecChartMap`: **the global-sections map of the
  morphism of relative spectra over a morphism of charts** is the restriction map of `A`,
  conjugated by the two chart identifications.
* `AlgebraicGeometry.Space.chartRelativeSpecSectionsIso_naturality`: **the identification is
  natural in the chart.**

## Implementation notes

**Why the naturality is the content.**  The identification at a single chart is Stacks 01LX (3),
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`, read at the top open; it was available
before this file.  What the descent of a morphism of sheaves of algebras along a surjective étale
chart consumes (`AlgebraicGeometry.Space.descChartAlgebraIso`) is a *natural* transformation on a
subcategory of charts, and naturality in the chart is a statement about a varying *base*: the
relative spectra over `V` and over `V'` live over different schemes.

**Where the naturality comes from.**  It is not proved by hand.  The whole content is already
carried by the universal property of the relative spectrum over a varying base, in
`StacksFrontier.AlgebraicGeometry.RelativeSpec.BaseFunctoriality`:
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_relativeSpecOverBaseHom` says that the
algebra map induced by `Stacks.AffineAlgebraEquivalence.relativeSpecOverBaseHom` is the one it
was built from, conjugated by `Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso` at the
source and by `Stacks.AffineAlgebraEquivalence.relativeSpecPushforwardIsoOverBase` at the target.
`AlgebraicGeometry.Space.chartRelativeSpecChartMap_eq` identifies the morphism of relative
spectra over a morphism of charts with exactly such a morphism, at the algebra map
`AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardHom`, whose sections over a Zariski open
are the restriction maps of `A` by
`AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardComparison_app`.  Reading all of that at
the top open is the theorem.

**The top open, and why an isomorphism of charts is needed.**  The sections of the chart
restriction over the top open are `A(openChart V ⊤)`, not `A(V)`:
`AlgebraicGeometry.Space.openChart` is built from the inclusion of an open subscheme and the top
open's inclusion is an isomorphism but not the identity.  The comparison is therefore
`AlgebraicGeometry.Space.openChartTopIso`, obtained by reflecting `AlgebraicGeometry.Scheme.topIso`
along `AlgebraicGeometry.Space.SmallEtale.toOver ⋙ AlgebraicGeometry.BigFppfOver.toScheme`, which
reflects isomorphisms; its naturality in the chart is
`AlgebraicGeometry.Space.openChartRestrict_comp_openChartInclusion` at the top open.

**Two definitional coercions are isolated in type ascriptions.**  The sections of
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebra` over the top open are the global sections of
the source, and the preimage of the top open is the top open; both hold at reducible transparency
but not syntactically, and `AlgebraicGeometry.Space.openChart` is semireducible, so
`AlgebraicGeometry.Space.openChartRestrictTop` and
`AlgebraicGeometry.Space.chartRelativeSpecTopSectionsIso` carry them in their stated types rather
than letting them appear inside a proof term, where `rw` and `simp` would stop seeing inside the
result.

**No `stacks` attribute is carried.**  Stacks 01LX (3) is registered on
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraIso`; the chart functoriality of the relative
spectrum of an algebra on an algebraic space is a step of the atlas construction of Stacks 081V
and is untagged where it is built.

## References

* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 0822](https://stacks.math.columbia.edu/tag/0822)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.AffineAlgebraEquivalence

universe u

/-! ### Sections of an isomorphism of sheaves of algebras -/

namespace Stacks.RelativeSpec.AlgebraSheaf

/-- **The ring isomorphism on sections over a Zariski open induced by an isomorphism of sheaves
of algebras.**  A morphism of algebra sheaves acts on sections through its underlying morphism of
sheaves of commutative rings, and that action is functorial, so an isomorphism gives an
isomorphism. -/
def sectionsIso {Z : Scheme.{u}} {P C : Stacks.RelativeSpec.AlgebraSheaf Z} (θ : P ≅ C)
    (O : Z.Opens) : P.sections O ≅ C.sections O where
  hom := θ.hom.right.hom.app (op O)
  inv := θ.inv.right.hom.app (op O)
  hom_inv_id := congrArg (fun m : P ⟶ P => m.right.hom.app (op O)) θ.hom_inv_id
  inv_hom_id := congrArg (fun m : C ⟶ C => m.right.hom.app (op O)) θ.inv_hom_id

/-- The forward map of `sectionsIso θ O` is the component of `θ.hom` at `O`. -/
@[simp]
theorem sectionsIso_hom {Z : Scheme.{u}} {P C : Stacks.RelativeSpec.AlgebraSheaf Z} (θ : P ≅ C)
    (O : Z.Opens) : (sectionsIso θ O).hom = θ.hom.right.hom.app (op O) :=
  rfl

/-- The inverse map of `sectionsIso θ O` is the component of `θ.inv` at `O`. -/
@[simp]
theorem sectionsIso_inv {Z : Scheme.{u}} {P C : Stacks.RelativeSpec.AlgebraSheaf Z} (θ : P ≅ C)
    (O : Z.Opens) : (sectionsIso θ O).inv = θ.inv.right.hom.app (op O) :=
  rfl

end Stacks.RelativeSpec.AlgebraSheaf

namespace AlgebraicGeometry.Space

/-! ### The chart cut out by the top open -/

section TopOpen

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)

/-- **The inclusion of the étale chart cut out by the top open is an isomorphism.**  Its
underlying morphism of schemes is the inclusion of the top open, which is
`AlgebraicGeometry.Scheme.topIso`, and the passage from charts to schemes reflects
isomorphisms. -/
theorem isIso_openChartInclusion_top (V : SmallEtale B S hS F) :
    IsIso (openChartInclusion B S hS F V ⊤) := by
  have : IsIso ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map
      (openChartInclusion B S hS F V ⊤)) := by
    rw [show (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).map
          (openChartInclusion B S hS F V ⊤) = (⊤ : (chartScheme V).Opens).ι from
        toScheme_map_toOver_map_openChartInclusion B S hS F V ⊤,
      ← Scheme.topIso_hom]
    exact Iso.isIso_hom _
  exact isIso_of_reflects_iso _ (SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS)

/-- **The étale chart cut out of `V` by the top open of `chartScheme V` is `V` itself.** -/
def openChartTopIso (V : SmallEtale B S hS F) : openChart B S hS F V ⊤ ≅ V :=
  haveI := isIso_openChartInclusion_top B S hS F V
  asIso (openChartInclusion B S hS F V ⊤)

/-- The forward map of `openChartTopIso` is the inclusion of the chart cut out by the top open. -/
@[simp]
theorem openChartTopIso_hom (V : SmallEtale B S hS F) :
    (openChartTopIso B S hS F V).hom = openChartInclusion B S hS F V ⊤ :=
  rfl

/-- The restriction of a morphism of charts to the top opens.  The preimage of the top open is
the top open, and `AlgebraicGeometry.Space.openChart` is semireducible, so the coercion is
isolated in this type ascription; see the implementation notes. -/
def openChartRestrictTop {U V : SmallEtale B S hS F} (g : V ⟶ U) :
    openChart B S hS F V ⊤ ⟶ openChart B S hS F U ⊤ :=
  openChartRestrict B S hS F g ⊤

/-- **The chart cut out by the top open is `V` itself, naturally in `V`.**  This is
`AlgebraicGeometry.Space.openChartRestrict_comp_openChartInclusion` at the top open. -/
theorem openChartRestrictTop_comp_openChartTopIso_hom {U V : SmallEtale B S hS F} (g : V ⟶ U) :
    openChartRestrictTop B S hS F g ≫ (openChartTopIso B S hS F U).hom =
      (openChartTopIso B S hS F V).hom ≫ g :=
  openChartRestrict_comp_openChartInclusion B S hS F g ⊤

end TopOpen

/-! ### The global sections of the relative spectrum over a chart -/

section Sections

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : AlgebraicSpaces B S hS) (A : AlgebraSheaf.{u, u} B S hS X.1 X.2)
    (hA : A.IsQuasicoherent)

/-- **Stacks 01LX (3) at the top open**: the global sections of the relative spectrum of `A` over
a chart are the sections of `A` over the chart that the top open cuts out.

The source is spelled as the sections of `A`, which is the same object as the sections of the
chart restriction over the top open at reducible transparency but not syntactically; the coercion
is isolated here.  See the implementation notes. -/
def chartRelativeSpecTopSectionsIso (V : SmallEtale B S hS X.1) :
    Scheme.Γ.obj (op (chartRelativeSpec B S hS X A hA V)) ≅
      A.right.obj.obj (op (openChart B S hS X.1 V ⊤)) :=
  Stacks.RelativeSpec.AlgebraSheaf.sectionsIso
    (chartRelativeSpecPushforwardIso B S hS X A hA V) ⊤

/-- The forward map of `chartRelativeSpecTopSectionsIso` is the component at the top open of
`chartRelativeSpecPushforwardIso`. -/
@[simp]
theorem chartRelativeSpecTopSectionsIso_hom (V : SmallEtale B S hS X.1) :
    (chartRelativeSpecTopSectionsIso B S hS X A hA V).hom =
      (chartRelativeSpecPushforwardIso B S hS X A hA V).hom.right.hom.app (op ⊤) :=
  rfl

/-- The inverse map of `chartRelativeSpecTopSectionsIso` is the component at the top open of the
inverse of `chartRelativeSpecPushforwardIso`. -/
@[simp]
theorem chartRelativeSpecTopSectionsIso_inv (V : SmallEtale B S hS X.1) :
    (chartRelativeSpecTopSectionsIso B S hS X A hA V).inv =
      (chartRelativeSpecPushforwardIso B S hS X A hA V).inv.right.hom.app (op ⊤) :=
  rfl

/-- **The global-sections map of the morphism of relative spectra over a morphism of charts is
the restriction map of `A`**, conjugated by the chart identifications of Stacks 01LX (3).

This is the universal property of the relative spectrum over a varying base,
`Stacks.AffineAlgebraEquivalence.pushforwardAlgebraMap_relativeSpecOverBaseHom`, read at the top
open: `AlgebraicGeometry.Space.chartRelativeSpecChartMap_eq` exhibits the morphism of relative
spectra as `Stacks.AffineAlgebraEquivalence.relativeSpecMapOverBase` of the algebra map
`AlgebraicGeometry.Space.chartSchemeAlgebraPushforwardHom`, whose sections over a Zariski open
are the restriction maps of `A`. -/
theorem Γ_map_chartRelativeSpecChartMap {V' V : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    Scheme.Γ.map (chartRelativeSpecChartMap B S hS X A hA h).op =
      (chartRelativeSpecTopSectionsIso B S hS X A hA V).hom ≫
        A.right.obj.map (openChartRestrictTop B S hS X.1 h).op ≫
          (chartRelativeSpecTopSectionsIso B S hS X A hA V').inv := by
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V
  have := isQuasicoherent_chartSchemeAlgebra B S hS X A hA V'
  have hleft : (relativeSpecOverBaseHom (chartSchemeMap h) (chartSchemeAlgebra B S hS X A V)
        (chartSchemeAlgebra B S hS X A V')
        (chartSchemeAlgebraPushforwardHom B S hS X A h)).left =
      chartRelativeSpecChartMap B S hS X A hA h :=
    (chartRelativeSpecChartMap_eq B S hS X A hA h).symm
  have hmap : (pushforwardAlgebraMap (relativeSpecOverBaseHom (chartSchemeMap h)
          (chartSchemeAlgebra B S hS X A V) (chartSchemeAlgebra B S hS X A V')
          (chartSchemeAlgebraPushforwardHom B S hS X A h))).right.hom.app
        (op (⊤ : (chartScheme V).Opens)) =
      (chartRelativeSpecChartMap B S hS X A hA h).appTop :=
    ((pushforwardAlgebraMap_app (relativeSpecOverBaseHom (chartSchemeMap h)
        (chartSchemeAlgebra B S hS X A V) (chartSchemeAlgebra B S hS X A V')
        (chartSchemeAlgebraPushforwardHom B S hS X A h)) ⊤ (by simp)).trans
      (Scheme.Hom.appLE_eq_app _)).trans (congrArg Scheme.Hom.appTop hleft)
  have halg := congrArg
    (fun m : Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
          (relativeSpecToBase (chartSchemeAlgebra B S hS X A V)) ⟶
        Stacks.AffineAlgebraEquivalence.pushforwardAlgebra
          (relativeSpecToBase (chartSchemeAlgebra B S hS X A V') ≫
            chartSchemeMap h) => m.right.hom.app (op (⊤ : (chartScheme V).Opens)))
    ((pushforwardAlgebraMap_relativeSpecOverBaseHom (chartSchemeMap h)
      (chartSchemeAlgebra B S hS X A V) (chartSchemeAlgebra B S hS X A V')
      (chartSchemeAlgebraPushforwardHom B S hS X A h)).trans
      (relativeSpecOverBaseAlgebraHom_eq (chartSchemeMap h) (chartSchemeAlgebra B S hS X A V)
        (chartSchemeAlgebra B S hS X A V') (chartSchemeAlgebraPushforwardHom B S hS X A h)))
  have hmid : (chartSchemeAlgebraPushforwardHom B S hS X A h).right.hom.app
        (op (⊤ : (chartScheme V).Opens)) =
      A.right.obj.map (openChartRestrictTop B S hS X.1 h).op :=
    congrArg (fun r => r.hom.app (op (⊤ : (chartScheme V).Opens)))
      (chartSchemeAlgebraPushforwardHom_right B S hS X A h)
  refine hmap.symm.trans (halg.trans ?_)
  exact congrArg (fun m => (chartRelativeSpecTopSectionsIso B S hS X A hA V).hom ≫
    m ≫ (chartRelativeSpecTopSectionsIso B S hS X A hA V').inv) hmid

/-- **The global sections of the relative spectrum of `A` over a chart are the sections of `A`
over that chart.**  This is Stacks 01LX (3) at the top open, composed with the identification
`AlgebraicGeometry.Space.openChartTopIso` of the chart cut out by the top open with the chart
itself. -/
def chartRelativeSpecSectionsIso (V : SmallEtale B S hS X.1) :
    A.right.obj.obj (op V) ≅ Scheme.Γ.obj (op (chartRelativeSpec B S hS X A hA V)) :=
  A.right.obj.mapIso (openChartTopIso B S hS X.1 V).op ≪≫
    (chartRelativeSpecTopSectionsIso B S hS X A hA V).symm

/-- **The identification of the global sections of the relative spectrum over a chart with the
sections of `A` is natural in the chart.**

This is `AlgebraicGeometry.Space.Γ_map_chartRelativeSpecChartMap` together with the naturality
`AlgebraicGeometry.Space.openChartRestrictTop_comp_openChartTopIso_hom` of the top-open
comparison. -/
theorem chartRelativeSpecSectionsIso_naturality {V' V : SmallEtale B S hS X.1} (h : V' ⟶ V) :
    A.right.obj.map h.op ≫ (chartRelativeSpecSectionsIso B S hS X A hA V').hom =
      (chartRelativeSpecSectionsIso B S hS X A hA V).hom ≫
        Scheme.Γ.map (chartRelativeSpecChartMap B S hS X A hA h).op := by
  have hsq : openChartRestrictTop B S hS X.1 h ≫ (openChartTopIso B S hS X.1 V).hom =
      (openChartTopIso B S hS X.1 V').hom ≫ h :=
    openChartRestrictTop_comp_openChartTopIso_hom B S hS X.1 h
  change A.right.obj.map h.op ≫ A.right.obj.map (openChartTopIso B S hS X.1 V').hom.op ≫
        (chartRelativeSpecTopSectionsIso B S hS X A hA V').inv =
      (A.right.obj.map (openChartTopIso B S hS X.1 V).hom.op ≫
          (chartRelativeSpecTopSectionsIso B S hS X A hA V).inv) ≫
        Scheme.Γ.map (chartRelativeSpecChartMap B S hS X A hA h).op
  rw [Γ_map_chartRelativeSpecChartMap B S hS X A hA h, Category.assoc,
    Iso.inv_hom_id_assoc, ← Category.assoc, ← Category.assoc, ← A.right.obj.map_comp,
    ← A.right.obj.map_comp, ← op_comp, ← op_comp, hsq]

end Sections

end AlgebraicGeometry.Space

end
