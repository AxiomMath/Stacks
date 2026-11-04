module

public import StacksFrontier.AlgebraicGeometry.RelativeSpecEssSurj.Basic
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineHigherPushforwardVanishing
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafChartRestriction
public import StacksFrontier.AlgebraicGeometry.Spaces.ChartRestrictionSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraChartSections
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraMorphism
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentPushforwardAlgebraFunctor

/-!
# Identifying a direct-image algebra with an algebra sheaf, one chart at a time

Let `X` be an algebraic space, `𝒜` a sheaf of `𝒪_X`-algebras and `Y` an algebraic space over `X`
with representable structure morphism. A morphism `φ : Y.hom_* 𝒪_Y ⟶ 𝒜` of algebra sheaves is an
isomorphism as soon as it is invertible on the sections over every étale scheme chart of `X`. For
a quasi-coherent `𝒜` and an étale scheme chart `V` of `X`, the global functions on the relative
spectrum of `𝒜|_V` are `𝒜(V)`.

## Main definitions

* `AlgebraicGeometry.Space.pushforwardAlgebraChartComparison`: the chart-level reading of a
  morphism `φ : Y.hom_* 𝒪_Y ⟶ 𝒜` of algebra sheaves, a ring map from the regular functions on
  the base-changed chart `Y ×_X V` to `𝒜(V)`, obtained from `φ` at `V` through
  `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`.
* `AlgebraicGeometry.Space.pushforwardAlgebraIsoOfChartComparison`: the isomorphism
  `Y.hom_* 𝒪_Y ≅ 𝒜` of algebra sheaves, when that comparison is invertible at every chart.
* `AlgebraicGeometry.Space.relativeSpecSectionsTopIso`: the ring isomorphism
  `Γ(relativeSpec 𝒜, ⊤) ≅ 𝒜(⊤)` for a quasi-coherent algebra `𝒜` on a scheme.
* `AlgebraicGeometry.Space.relativeSpecChartSectionsIso`: for a quasi-coherent `𝒪_X`-algebra `𝒜`
  and an étale scheme chart `V` of `X`, the global functions on the relative spectrum of `𝒜|_V`
  are `𝒜(V)`.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.isIso_of_isIso_right`,
  `AlgebraicGeometry.Space.AlgebraSheaf.isIso_of_bijective_right_app` and
  `AlgebraicGeometry.Space.AlgebraSheaf.isIso_of_isIso_right_app`: a morphism of algebra sheaves
  is an isomorphism as soon as its underlying morphism of sheaves of rings is, and so as soon as
  it is invertible on the sections over every étale chart.
* `AlgebraicGeometry.Space.isIso_of_isIso_pushforwardAlgebraChartComparison`: a morphism
  `φ : Y.hom_* 𝒪_Y ⟶ 𝒜` whose chart-level comparison is invertible at every chart is an
  isomorphism.
* `AlgebraicGeometry.Space.essImage_affinePushforwardAlgebraFunctor_of_isIso_chartComparison`: a
  quasi-coherent `𝒪_X`-algebra lies in the essential image of
  `AlgebraicGeometry.Space.quasicoherentPushforwardAlgebraFunctor` as soon as some morphism to it
  out of the direct image of an algebraic space affine over `X` has invertible chart comparison.

## References

* [Stacks Project, Tag 081V](https://stacks.math.columbia.edu/tag/081V)
* [Stacks Project, Tag 01LX](https://stacks.math.columbia.edu/tag/01LX)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/


@[expose] public noncomputable section

open CategoryTheory Opposite

universe u m

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### Recognising an isomorphism of algebra sheaves -/

namespace AlgebraSheaf

section Recognition

variable {B S hS} {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- **A morphism of algebra sheaves is an isomorphism as soon as its underlying morphism of
sheaves of rings is one**: the forgetful functor `AlgebraicGeometry.Space.AlgebraSheaf.forget` to
the sheaves of rings reflects isomorphisms. -/
theorem isIso_of_isIso_right {A C : AlgebraSheaf.{u, m} B S hS F hF} (φ : A ⟶ C)
    (h : IsIso φ.right) : IsIso φ := by
  refine ⟨⟨⟨inv φ.right, fun U r => ?_⟩, ?_, ?_⟩⟩
  · have hid := congrArg (fun ψ : A.right ⟶ A.right => ψ.hom.app U)
      (IsIso.hom_inv_id φ.right)
    rw [← φ.comm U r]
    exact ConcreteCategory.congr_hom hid (A.algebraMap U r)
  · exact Hom.ext (IsIso.hom_inv_id φ.right)
  · exact Hom.ext (IsIso.inv_hom_id φ.right)

/-- **A morphism of algebra sheaves which is bijective on the sections over every chart is an
isomorphism.** The converse is `AlgebraicGeometry.Space.AlgebraSheaf.bijective_iso_right_app`. -/
theorem isIso_of_bijective_right_app {A C : AlgebraSheaf.{u, m} B S hS F hF} (φ : A ⟶ C)
    (h : ∀ U : (SmallEtale B S hS F)ᵒᵖ, Function.Bijective (φ.right.hom.app U).hom) :
    IsIso φ := by
  refine isIso_of_isIso_right φ ?_
  have : IsIso ((sheafToPresheaf (SmallEtale.topology B S hS F) CommRingCat.{m}).map φ.right) :=
    (NatTrans.isIso_iff_isIso_app _).2 fun U => (ConcreteCategory.isIso_iff_bijective _).2 (h U)
  exact isIso_of_reflects_iso _ (sheafToPresheaf (SmallEtale.topology B S hS F) CommRingCat.{m})

/-- **A morphism of algebra sheaves which is an isomorphism on the sections over every chart is
an isomorphism**, stated with `CategoryTheory.IsIso` on each ring of sections rather than with
bijectivity. -/
theorem isIso_of_isIso_right_app {A C : AlgebraSheaf.{u, m} B S hS F hF} (φ : A ⟶ C)
    (h : ∀ U : (SmallEtale B S hS F)ᵒᵖ, IsIso (φ.right.hom.app U)) : IsIso φ :=
  isIso_of_bijective_right_app φ fun U =>
    have := h U
    ConcreteCategory.bijective_of_isIso (φ.right.hom.app U)

end Recognition

end AlgebraSheaf

/-! ### The chart-level comparison of a direct-image algebra with an algebra sheaf -/

/-- **The chart-level comparison attached to a morphism out of a direct-image algebra.**  Let
`Y` be an algebraic space over `X` with representable structure morphism, `𝒜` a sheaf of
`𝒪_X`-algebras, and `φ : Y.hom_* 𝒪_Y ⟶ 𝒜` a morphism of algebra sheaves.  Over an étale scheme
chart `V` of `X` the sections of the direct image are the regular functions on the base-changed
chart `Y ×_X V`, by `AlgebraicGeometry.Space.pushforwardAlgebraSectionsIso`, and this is `φ` at
`V` read through that identification: a ring map `Γ(Y ×_X V) ⟶ 𝒜(V)`. -/
def pushforwardAlgebraChartComparison {X : AlgebraicSpaces B S hS} {Y : Over X}
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (φ : pushforwardAlgebra B S hS Y ⟶ A)
    (V : SmallEtale B S hS X.1) :
    Γ(chartScheme ((smallBaseChange B S hS Y.hom hY).obj V), ⊤) ⟶ A.right.obj.obj (op V) :=
  (pushforwardAlgebraSectionsIso B S hS Y hY V).inv ≫ φ.right.hom.app (op V)

/-- The sections of `φ` over a chart are its chart-level comparison, preceded by the
identification of those sections with the regular functions on the base-changed chart. -/
theorem right_app_eq_pushforwardAlgebraChartComparison {X : AlgebraicSpaces B S hS}
    {Y : Over X} (hY : yoneda.relativelyRepresentable Y.hom.hom)
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (φ : pushforwardAlgebra B S hS Y ⟶ A)
    (V : SmallEtale B S hS X.1) :
    φ.right.hom.app (op V) =
      (pushforwardAlgebraSectionsIso B S hS Y hY V).hom ≫
        pushforwardAlgebraChartComparison B S hS hY φ V := by
  rw [pushforwardAlgebraChartComparison, ← Category.assoc, Iso.hom_inv_id, Category.id_comp]

/-- **The direct image of `Y` is identified with `𝒜` as soon as the comparison is invertible at
every chart**: a morphism `φ : Y.hom_* 𝒪_Y ⟶ 𝒜` of algebra sheaves whose chart-level comparison
`AlgebraicGeometry.Space.pushforwardAlgebraChartComparison` is invertible at every étale scheme
chart of `X` is an isomorphism. -/
theorem isIso_of_isIso_pushforwardAlgebraChartComparison {X : AlgebraicSpaces B S hS}
    {Y : Over X} (hY : yoneda.relativelyRepresentable Y.hom.hom)
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (φ : pushforwardAlgebra B S hS Y ⟶ A)
    (h : ∀ V : SmallEtale B S hS X.1,
      IsIso (pushforwardAlgebraChartComparison B S hS hY φ V)) :
    IsIso φ := by
  refine AlgebraSheaf.isIso_of_isIso_right_app φ fun U => ?_
  rw [right_app_eq_pushforwardAlgebraChartComparison B S hS hY φ U.unop]
  have := h U.unop
  infer_instance

/-- **The direct image of `Y` is isomorphic to `𝒜` as soon as the comparison is invertible at
every chart**, as an isomorphism of algebra sheaves rather than as invertibility of `φ`. -/
def pushforwardAlgebraIsoOfChartComparison {X : AlgebraicSpaces B S hS} {Y : Over X}
    (hY : yoneda.relativelyRepresentable Y.hom.hom)
    {A : AlgebraSheaf.{u, u} B S hS X.1 X.2} (φ : pushforwardAlgebra B S hS Y ⟶ A)
    (h : ∀ V : SmallEtale B S hS X.1,
      IsIso (pushforwardAlgebraChartComparison B S hS hY φ V)) :
    pushforwardAlgebra B S hS Y ≅ A :=
  haveI := isIso_of_isIso_pushforwardAlgebraChartComparison B S hS hY φ h
  asIso φ

/-! ### The essential image of the direct-image functor -/

/-- **A quasi-coherent `𝒪_X`-algebra is a direct image as soon as some morphism out of a direct
image is invertible at every chart.**  Given an algebraic space `Y` affine over `X` and a
morphism `φ : Y.hom_* 𝒪_Y ⟶ 𝒜` of algebra sheaves whose chart-level comparison
`AlgebraicGeometry.Space.pushforwardAlgebraChartComparison` — a ring map from the regular
functions on `Y ×_X V` to `𝒜(V)` — is invertible at every étale scheme chart `V` of `X`, the
algebra `𝒜` lies in the essential image of
`AlgebraicGeometry.Space.quasicoherentPushforwardAlgebraFunctor`. -/
theorem essImage_affinePushforwardAlgebraFunctor_of_isIso_chartComparison
    {X : AlgebraicSpaces B S hS} (A : QuasicoherentAlgebra B S hS X)
    (Y : AffineOver B S hS X) (φ : pushforwardAlgebra B S hS Y.obj ⟶ A.obj)
    (h : ∀ V : SmallEtale B S hS X.1,
      IsIso (pushforwardAlgebraChartComparison B S hS
        (relativelyRepresentable_of_isAffineHom B S hS Y.obj.hom Y.property) φ V)) :
    (quasicoherentPushforwardAlgebraFunctor B S hS X).essImage A :=
  ⟨op Y, ⟨(quasicoherentAlgebraInclusion B S hS X).preimageIso
    (pushforwardAlgebraIsoOfChartComparison B S hS
      (relativelyRepresentable_of_isAffineHom B S hS Y.obj.hom Y.property) φ h)⟩⟩

/-! ### Global functions on relative spectra -/

/-- **The global functions on the relative spectrum of a quasi-coherent algebra on a scheme are
the global sections of that algebra**: the identification `(relativeSpecToBase A)_* 𝒪 ≅ A` of
`Stacks.AffineAlgebraEquivalence.pushforwardSheafIso` read at the open `⊤` of the base. -/
def relativeSpecSectionsTopIso {T : Scheme.{u}} (A : Stacks.RelativeSpec.AlgebraSheaf T)
    [Stacks.RelativeSpec.AlgebraSheaf.IsQuasicoherent A] :
    Γ(Stacks.AffineAlgebraEquivalence.relativeSpec A, ⊤) ≅
      A.right.obj.obj (op (⊤ : T.Opens)) where
  hom := (Stacks.AffineAlgebraEquivalence.pushforwardSheafIso A).hom.hom.app (op ⊤)
  inv := (Stacks.AffineAlgebraEquivalence.pushforwardSheafIso A).inv.hom.app (op ⊤)
  hom_inv_id := congrArg (fun φ => φ.hom.app (op (⊤ : T.Opens)))
    (Stacks.AffineAlgebraEquivalence.pushforwardSheafIso A).hom_inv_id
  inv_hom_id := congrArg (fun φ => φ.hom.app (op (⊤ : T.Opens)))
    (Stacks.AffineAlgebraEquivalence.pushforwardSheafIso A).inv_hom_id

section Chart

variable {X : AlgebraicSpaces B S hS}

/-- **The direct image of the relative spectrum of a chart restriction is the algebra, at that
chart.**  For a quasi-coherent sheaf `𝒜` of `𝒪_X`-algebras and an étale scheme chart `V` of `X`,
the global functions on the relative spectrum over `V` of the restriction `𝒜|_V` are the
sections `𝒜(V)`. -/
def relativeSpecChartSectionsIso (A : QuasicoherentAlgebra B S hS X)
    (V : SmallEtale B S hS X.1) :
    Γ(Stacks.AffineAlgebraEquivalence.relativeSpec (A.obj.restrictToChartScheme B S hS V), ⊤) ≅
      A.obj.right.obj.obj (op V) :=
  relativeSpecSectionsTopIso (A.obj.restrictToChartScheme B S hS V) ≪≫
    (A.obj.right.obj.mapIso (asIso (chartOpensTopHom B S hS X V)).op).symm

end Chart

end AlgebraicGeometry.Space

end
