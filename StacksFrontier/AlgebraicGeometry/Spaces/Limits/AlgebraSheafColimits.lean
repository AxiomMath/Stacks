module

public import Mathlib.CategoryTheory.Limits.Constructions.Over.Connected
public import Mathlib.CategoryTheory.Limits.FunctorCategory.Basic
public import StacksFrontier.AlgebraicGeometry.QuasiCompactColimit.Pointwise
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDenseSubsite
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnder

/-!
# Colimits of algebra sheaves on an algebraic space

A cocone of sheaves of commutative `𝒪_F`-algebras on the small étale site of an algebraic space
`F` is recognised here from the sections of its members over the *affine* étale charts of `F`,
and the category of such algebra sheaves is shown to have all connected colimits.

Both halves of Stacks 082A and Stacks 086Z assert that a canonical cocone of algebra sheaves on
an algebraic space is colimiting, and before this file there was no way to produce such an
assertion: the recorded obstruction, in the module documentation of
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.IdealQuotientApproximationSystem` and in the
attribute on Stacks 086Z in
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.FiniteAlgebraSurjectiveSystem`, says
that `AlgebraicGeometry.Space.AlgebraSheaf` is a bespoke structure rather than a
`CategoryTheory.Under` category, so the scheme-level reduction
`Stacks.RelativeSpec.AlgebraSheaf.isColimit_of_isColimit_forget` does not apply, and that the
scheme-level affine criterion `Stacks.QcohAlgebraFPColimit.nonempty_isColimit_of_affineSections`
is stated for schemes.  This file removes both halves of that obstruction.

## Main definitions

* `Stacks.SheafSectionsColimit.isColimit_of_sheafSections`: a cocone of sheaves on a site is
  colimiting as soon as its cocones of sections over *every* object are.
* `Stacks.SheafSectionsColimit.isColimit_of_sheafSections_denseSubsite`: the same with the
  objects restricted to the image of a dense subsite inclusion.
* `AlgebraicGeometry.Space.AlgebraSheaf.chartSectionsFunctor`: the sections of an algebra sheaf
  over a fixed étale chart, as a functor on algebra sheaves.

## Main results

* `AlgebraicGeometry.Space.AlgebraSheaf.isColimit_of_isColimit_forget` and
  `AlgebraicGeometry.Space.AlgebraSheaf.nonempty_isColimit_forget_iff`: **a cocone of algebra
  sheaves over a connected diagram is colimiting exactly when the underlying cocone of sheaves
  of rings is.**
* `AlgebraicGeometry.Space.AlgebraSheaf.isColimit_of_chartSections` and
  `AlgebraicGeometry.Space.AlgebraSheaf.isColimit_of_affineChartSections`: **a cocone of algebra
  sheaves over a connected diagram is colimiting as soon as its cocones of sections over the
  étale charts — indeed over the affine étale charts alone — are colimiting.**
* `AlgebraicGeometry.Space.isColimit_sheaf_of_affineChartSections`: the same for a cocone of
  sheaves on the small étale site, with no algebra structure in sight.
* `AlgebraicGeometry.Space.AlgebraSheaf.nonempty_isColimit_of_affineChartSections`: **the same
  with the sectionwise colimit property replaced by its elementwise form** over a filtered
  diagram: over every affine étale chart the components are jointly surjective on sections and
  two sections with the same image already agree at a later index.  This is the algebraic-space
  analogue of `Stacks.QcohAlgebraFPColimit.nonempty_isColimit_of_affineSections`, and
  `...nonempty_isColimit_of_affineChartSections_of_injective` is its specialisation to a diagram
  of subalgebras, where joint surjectivity on affine chart sections is the only input.
* `AlgebraicGeometry.Space.hasColimitsOfShape_algebraSheaf`: **algebra sheaves with sections in
  the universe of the schemes have all connected colimits.**
* `AlgebraicGeometry.Space.nonempty_isColimit_quasicoherentAlgebra_of_affineChartSections`: the
  elementwise criterion for a cocone of *quasi-coherent* algebras, which is the shape in which
  Stacks 082A and Stacks 086Z state their colimit assertion.

## Implementation notes

### Why the `Under` layer is free after all

`AlgebraicGeometry.Space.AlgebraSheaf` stores a sheaf of commutative rings together with a
*sectionwise* family of ring homomorphisms out of the sections of the structure sheaf, so that
the sections of the algebra may live in a universe `m` independent of the universe `u` of the
schemes.  That is what makes it a bespoke structure and not an `Under` category.  In the
single-universe case `m = u` the sectionwise family is the same thing as a morphism of sheaves
of rings, and `AlgebraicGeometry.Space.AlgebraSheaf.underEquivalence` is the resulting
equivalence with `CategoryTheory.Under (AlgebraicGeometry.Space.structureSheaf B S hS F hF)`.
Composing that equivalence with
`CategoryTheory.Under.createsColimitsOfShapeForgetOfIsConnected` makes
`AlgebraicGeometry.Space.AlgebraSheaf.forget` reflect connected colimits, which is the
algebraic-space analogue of `Stacks.RelativeSpec.AlgebraSheaf.isColimit_of_isColimit_forget`.
The identification
`AlgebraicGeometry.Space.AlgebraSheaf.toUnder_comp_forget` of the two forgetful functors is an
equality of functors, so the transfer is a rewrite and costs nothing.

Everything in this file is therefore restricted to `AlgebraSheaf.{u, u}`.  For a general
universe `m` of sections the equivalence is unavailable for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnder`, and so is sheafification.

### Why no cover-dense plumbing is needed for the sheaf half

On a topological space the reduction of a colimit assertion to a basis of opens needs an
extension device — `Stacks.QuasiCompactColimit.isColimitOfBasis` glues a morphism prescribed on
a basis with `TopCat.Sheaf.restrictHomEquivHom`.  On a site none of that is required.  Three
functors reflect colimits for formal reasons:

* `CategoryTheory.sheafToPresheaf` is fully faithful, and a fully faithful functor reflects
  colimits (`CategoryTheory.Limits.fullyFaithful_reflectsColimits`);
* the evaluation functors on a presheaf category jointly reflect colimits
  (`CategoryTheory.Limits.evaluationJointlyReflectsColimits`);
* for a dense subsite inclusion `G` the restriction functor
  `CategoryTheory.Functor.sheafPushforwardContinuous` is fully faithful
  (`CategoryTheory.Functor.IsDenseSubsite.full_sheafPushforwardContinuous` and
  `...faithful_sheafPushforwardContinuous`), hence also reflects colimits.

Reflection along the third followed by the first two is exactly the statement that sections over
the objects of a dense subsite detect colimits, and the composite of the three *is* the sections
functor, by definition and not up to an isomorphism: Mathlib's
`CategoryTheory.sheafSectionsNatIsoEvaluation` and
`CategoryTheory.Functor.sheafPushforwardContinuousCompSheafToPresheafIso` are both
`CategoryTheory.Iso.refl`.  So no hom-extension lemma, and in particular no cover-dense
machinery beyond the `CategoryTheory.Functor.IsDenseSubsite` instance itself, appears below.
Note that essential surjectivity of the restriction functor — the hard half of the dense-subsite
equivalence of topoi — is *not* used; full faithfulness suffices to reflect.

For the small étale site of an algebraic space the dense subsite is the inclusion of the affine
étale charts, which is Stacks 04JS, available here as
`AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`.  That is the single
geometric input of this file; everything else is formal.

### What this does *not* supply

The criteria below produce the colimit assertion from a statement about sections over the affine
étale charts.  They say nothing about *verifying* that statement.

They also do not make the colimit assertion *equivalent* to it.  Only
`AlgebraicGeometry.Space.AlgebraSheaf.nonempty_isColimit_forget_iff` is an equivalence; the
sectionwise criteria are sufficient and not necessary, a colimit of sheaves being the
sheafification of the objectwise colimit.  So the colimit hypothesis carried by Stacks 082A in
`AlgebraicGeometry.Space.exists_directed_isFinitePresentation_algebra_of_idealQuotients` and by
Stacks 086Z in
`AlgebraicGeometry.Space.exists_directed_isFinite_isFinitePresentation_locallySurjective` cannot
simply be replaced by the sectionwise one: that would make those theorems *weaker*, not
stronger.  What those tags still need in order to shed it is the verification, not another
criterion.  For the system of Stacks 082A the
verification is the identification of the sections of a sheafified quotient over an affine chart
with the objectwise quotient, which is an H¹-vanishing statement on the small étale site of an
affine chart (Stacks 0942) and is not proved anywhere in this tree.  Quasi-compactness and
quasi-separatedness of the space, which is where that verification uses them, are likewise
absent: no hypothesis on `F` beyond being an algebraic space is used.

For the particular diagrams of Stacks 082A and Stacks 086Z — the quotients of one algebra sheaf
by a growing family of sheaves of ideals — the affine-chart route above is not needed at all, and
`StacksFrontier.AlgebraicGeometry.Spaces.Limits.AlgebraSheafIdealQuotientColimit` takes a different
one: the diagram of quotients *is* the sheafification of the diagram of objectwise quotients, and
sheafification preserves colimits, so the colimit assertion reduces to local bijectivity of a
morphism of *presheaves* — an equivalence, not a criterion, and one in which no section of a
sheafification occurs.  The criteria below remain the general-purpose tool for a diagram with no
such presheaf model.

## References

* [Stacks Project, Tag 04JS](https://stacks.math.columbia.edu/tag/04JS)
* [Stacks Project, Tag 082A](https://stacks.math.columbia.edu/tag/082A)
* [Stacks Project, Tag 086Z](https://stacks.math.columbia.edu/tag/086Z)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe v₁ u₁ v₂ u₂ v₃ u₃ v₄ u₄ v w u

namespace Stacks.SheafSectionsColimit

/-! ### Colimits of sheaves on a site are detected on sections -/

variable {C : Type u₁} [Category.{v₁} C] {A : Type u₂} [Category.{v₂} A]
    {K : GrothendieckTopology C} {J : Type u₃} [Category.{v₃} J]

/-- **A cocone of sheaves on a site is colimiting as soon as its cocones of sections over every
object of the site are colimiting.**

The inclusion of sheaves into presheaves is fully faithful, hence reflects colimits, and the
evaluation functors jointly reflect colimits of presheaves.  Nothing is assumed about the
topology, and no colimit is assumed to exist. -/
def isColimit_of_sheafSections {Φ : J ⥤ Sheaf K A} (c : Cocone Φ)
    (h : ∀ U : Cᵒᵖ, IsColimit (((sheafSections K A).obj U).mapCocone c)) :
    IsColimit c :=
  isColimitOfReflects (sheafToPresheaf K A) (evaluationJointlyReflectsColimits _ h)

variable {C₀ : Type u₄} [Category.{v₄} C₀]

/-- **A cocone of sheaves on a site is colimiting as soon as its cocones of sections over the
objects of a dense subsite are colimiting.**

For a dense subsite inclusion `G` the restriction functor
`CategoryTheory.Functor.sheafPushforwardContinuous` is fully faithful, hence reflects colimits,
and the sections of the restriction of a sheaf over `U` are the sections of the sheaf over
`G.obj U`.  So this is `Stacks.SheafSectionsColimit.isColimit_of_sheafSections` on the subsite,
reflected along the restriction. -/
def isColimit_of_sheafSections_denseSubsite (J₀ : GrothendieckTopology C₀) (G : C₀ ⥤ C)
    [G.IsDenseSubsite J₀ K] {Φ : J ⥤ Sheaf K A} (c : Cocone Φ)
    (h : ∀ U : C₀, IsColimit (((sheafSections K A).obj (op (G.obj U))).mapCocone c)) :
    IsColimit c :=
  isColimitOfReflects (G.sheafPushforwardContinuous A J₀ K)
    (isColimit_of_sheafSections _ fun U => h U.unop)

end Stacks.SheafSectionsColimit

namespace AlgebraicGeometry.Space

/-! ### Sheaves on the small étale site are detected on the affine charts -/

/-- **A cocone of sheaves on the small étale site of an algebraic space is colimiting as soon as
its cocones of sections over the *affine* étale charts are colimiting.**

The affine étale charts are a dense subsite of the small étale site, which is Stacks 04JS,
available as `AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`; that is the
only geometric input, and the rest is
`Stacks.SheafSectionsColimit.isColimit_of_sheafSections_denseSubsite`.  No hypothesis on `F`
beyond being an algebraic space is used, and no colimit is assumed to exist. -/
def isColimit_sheaf_of_affineChartSections {A : Type u₂} [Category.{v₂} A]
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hF : IsAlgebraicSpace B S hS F)
    {J : Type w} [Category.{v} J] {Φ : J ⥤ Sheaf (SmallEtale.topology B S hS F) A}
    (c : Cocone Φ)
    (h : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        IsColimit (((sheafSections (SmallEtale.topology B S hS F) A).obj (op U)).mapCocone c)) :
    IsColimit c :=
  have : (AffineEtale.inclusion B S hS F).IsDenseSubsite
      (AffineEtale.topology B S hS F) (SmallEtale.topology B S hS F) :=
    (AffineEtale.inclusion_isSpecialCocontinuous B S hS F hF).2
  Stacks.SheafSectionsColimit.isColimit_of_sheafSections_denseSubsite
    (AffineEtale.topology B S hS F) (AffineEtale.inclusion B S hS F) c
    fun U => h U.obj U.property

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

namespace AlgebraSheaf

/-! ### The `Under` layer is free for a connected diagram -/

/-- **Forgetting the algebra structure reflects connected colimits.**

`AlgebraicGeometry.Space.AlgebraSheaf.toUnder` is an equivalence, hence reflects colimits, and
`CategoryTheory.Under.forget` creates — hence reflects — colimits of connected shape; the
composite of the two *is* `AlgebraicGeometry.Space.AlgebraSheaf.forget`, by
`AlgebraicGeometry.Space.AlgebraSheaf.toUnder_comp_forget`. -/
instance reflectsColimitsOfShape_forget (J : Type w) [Category.{v} J] [IsConnected J] :
    ReflectsColimitsOfShape J
      (forget (B := B) (S := S) (hS := hS) (F := F) (hF := hF) :
        AlgebraSheaf.{u, u} B S hS F hF ⥤ _) := by
  rw [← toUnder_comp_forget (B := B) (S := S) (hS := hS) (F := F) (hF := hF)]
  infer_instance

/-- **A cocone of algebra sheaves over a connected diagram is colimiting as soon as the
underlying cocone of sheaves of rings is.**  This is the algebraic-space analogue of
`Stacks.RelativeSpec.AlgebraSheaf.isColimit_of_isColimit_forget`, whose unavailability here was
the recorded obstruction to the colimit assertions of Stacks 082A and Stacks 086Z. -/
def isColimit_of_isColimit_forget {J : Type w} [Category.{v} J] [IsConnected J]
    {Φ : J ⥤ AlgebraSheaf.{u, u} B S hS F hF} (c : Cocone Φ)
    (hc : IsColimit (forget.mapCocone c)) : IsColimit c :=
  isColimitOfReflects forget hc

/-- **Forgetting the algebra structure preserves connected colimits.**  The same two inputs as
`AlgebraicGeometry.Space.AlgebraSheaf.reflectsColimitsOfShape_forget`: an equivalence preserves
all colimits and `CategoryTheory.Under.forget` preserves the connected ones.

Together with the existence of connected colimits
(`AlgebraicGeometry.Space.hasColimitsOfShape_algebraSheaf`) this says that the underlying sheaf
of rings of a connected colimit of algebra sheaves is the colimit of the underlying sheaves of
rings. -/
instance preservesColimitsOfShape_forget (J : Type w) [Category.{v} J] [IsConnected J] :
    PreservesColimitsOfShape J
      (forget (B := B) (S := S) (hS := hS) (F := F) (hF := hF) :
        AlgebraSheaf.{u, u} B S hS F hF ⥤ _) := by
  rw [← toUnder_comp_forget (B := B) (S := S) (hS := hS) (F := F) (hF := hF)]
  infer_instance

/-- A cocone of algebra sheaves over a connected diagram is colimiting exactly when the
underlying cocone of sheaves of commutative rings is. -/
theorem nonempty_isColimit_forget_iff {J : Type w} [Category.{v} J] [IsConnected J]
    {Φ : J ⥤ AlgebraSheaf.{u, u} B S hS F hF} (c : Cocone Φ) :
    Nonempty (IsColimit c) ↔ Nonempty (IsColimit (forget.mapCocone c)) :=
  ⟨fun ⟨hc⟩ => ⟨isColimitOfPreserves _ hc⟩,
    fun ⟨hc⟩ => ⟨isColimit_of_isColimit_forget c hc⟩⟩

/-! ### Sections over an étale chart -/

/-- The sections of an algebra sheaf over a fixed étale chart, as a functor on algebra
sheaves. -/
def chartSectionsFunctor (U : SmallEtale B S hS F) :
    AlgebraSheaf.{u, u} B S hS F hF ⥤ CommRingCat.{u} :=
  forget ⋙ (sheafSections (SmallEtale.topology B S hS F) CommRingCat.{u}).obj (op U)

/-- The value of `chartSectionsFunctor U` at an algebra sheaf is its ring of sections over `U`. -/
@[simp]
theorem chartSectionsFunctor_obj (U : SmallEtale B S hS F) (A : AlgebraSheaf.{u, u} B S hS F hF) :
    (chartSectionsFunctor (hF := hF) U).obj A = A.right.obj.obj (op U) :=
  rfl

/-- The image under `chartSectionsFunctor U` of a morphism of algebra sheaves is its component
at `U`. -/
@[simp]
theorem chartSectionsFunctor_map (U : SmallEtale B S hS F)
    {A C : AlgebraSheaf.{u, u} B S hS F hF} (f : A ⟶ C) :
    (chartSectionsFunctor (hF := hF) U).map f = f.right.hom.app (op U) :=
  rfl

/-! ### The sectionwise criteria -/

/-- **A cocone of algebra sheaves over a connected diagram is colimiting as soon as its cocones
of sections over every étale chart are colimiting.** -/
def isColimit_of_chartSections {J : Type w} [Category.{v} J] [IsConnected J]
    {Φ : J ⥤ AlgebraSheaf.{u, u} B S hS F hF} (c : Cocone Φ)
    (h : ∀ U : SmallEtale B S hS F, IsColimit ((chartSectionsFunctor U).mapCocone c)) :
    IsColimit c :=
  isColimit_of_isColimit_forget c
    (Stacks.SheafSectionsColimit.isColimit_of_sheafSections _ fun U => h U.unop)

/-- **A cocone of algebra sheaves over a connected diagram is colimiting as soon as its cocones
of sections over the *affine* étale charts are colimiting.**

The affine étale charts are a dense subsite of the small étale site of an algebraic space, which
is Stacks 04JS, available as
`AlgebraicGeometry.Space.AffineEtale.inclusion_isSpecialCocontinuous`; this is the only
geometric input of the criterion.  It is the algebraic-space analogue of
`Stacks.QuasiCompactColimit.nonempty_isColimit_of_affineOpens`. -/
def isColimit_of_affineChartSections {J : Type w} [Category.{v} J] [IsConnected J]
    {Φ : J ⥤ AlgebraSheaf.{u, u} B S hS F hF} (c : Cocone Φ)
    (h : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        IsColimit ((chartSectionsFunctor U).mapCocone c)) :
    IsColimit c :=
  isColimit_of_isColimit_forget c
    (isColimit_sheaf_of_affineChartSections B S hS F hF _ h)

/-- **A cocone of algebra sheaves over a filtered diagram is colimiting as soon as, over every
affine étale chart, its components are jointly surjective on sections and two sections with the
same image already agree at a later index.**

This is the algebraic-space analogue of
`Stacks.QcohAlgebraFPColimit.nonempty_isColimit_of_affineSections`, which is stated for schemes.
The elementwise recognition of a filtered colimit of commutative rings is
`Stacks.QuasiCompactColimit.isColimitOfJointlySurjective`; no injectivity of the components is
asked, so the criterion applies to a diagram which is not one of subalgebras of the vertex —
which is the situation of Stacks 082A, where the approximating algebras are quotients of a
symmetric algebra and the maps to the vertex are injective only in the limit. -/
theorem nonempty_isColimit_of_affineChartSections {J : Type w} [Category.{v} J] [IsFiltered J]
    {Φ : J ⥤ AlgebraSheaf.{u, u} B S hS F hF} (c : Cocone Φ)
    (hsurj : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        ∀ x : (chartSectionsFunctor U).obj c.pt,
          ∃ (k : J) (y : (chartSectionsFunctor U).obj (Φ.obj k)),
            (chartSectionsFunctor U).map (c.ι.app k) y = x)
    (hinj : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        ∀ (k : J) (x y : (chartSectionsFunctor U).obj (Φ.obj k)),
          (chartSectionsFunctor U).map (c.ι.app k) x = (chartSectionsFunctor U).map (c.ι.app k) y →
            ∃ (l : J) (f : k ⟶ l),
              (Φ ⋙ chartSectionsFunctor U).map f x = (Φ ⋙ chartSectionsFunctor U).map f y) :
    Nonempty (IsColimit c) :=
  let := IsFiltered.isConnected (C := J)
  ⟨isColimit_of_affineChartSections c fun U hU =>
    Stacks.QuasiCompactColimit.isColimitOfJointlySurjective _ (hsurj U hU) (hinj U hU)⟩

/-- **A filtered family of subalgebras of an algebra sheaf is colimiting as soon as every
section over an affine étale chart lies in one of them.**

The specialisation of
`AlgebraicGeometry.Space.AlgebraSheaf.nonempty_isColimit_of_affineChartSections` to a diagram of
subalgebras: with the components injective on the sections over each affine
chart the eventual-injectivity hypothesis is discharged at the same index by the identity.  This
is the shape the colimit assertions of Stacks 082B and Stacks 082C(1) supply, the diagram there
being one of subobjects of the ambient algebra. -/
theorem nonempty_isColimit_of_affineChartSections_of_injective {J : Type w} [Category.{v} J]
    [IsFiltered J] {Φ : J ⥤ AlgebraSheaf.{u, u} B S hS F hF} (c : Cocone Φ)
    (hinj : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        ∀ k : J, Function.Injective ((chartSectionsFunctor U).map (c.ι.app k)))
    (hsurj : ∀ U : SmallEtale B S hS F,
      IsAffine ((SmallEtale.toOver B S hS F ⋙ BigFppfOver.toScheme B S hS).obj U) →
        ∀ x : (chartSectionsFunctor U).obj c.pt,
          ∃ (k : J) (y : (chartSectionsFunctor U).obj (Φ.obj k)),
            (chartSectionsFunctor U).map (c.ι.app k) y = x) :
    Nonempty (IsColimit c) :=
  nonempty_isColimit_of_affineChartSections c hsurj fun U hU k _ _ h =>
    ⟨k, 𝟙 k, hinj U hU k h ▸ rfl⟩

end AlgebraSheaf

/-! ### Existence of connected colimits -/

/-- **Algebra sheaves with sections in the universe of the schemes have all connected
colimits.**  Sheaves of commutative rings on the small étale site have all small colimits, an
under category has the connected ones among them, and
`AlgebraicGeometry.Space.AlgebraSheaf.underEquivalence` carries them across.

Stated as a theorem rather than an instance for the reason recorded in
`StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafUnder`: a shape-indexed limit instance for
sheaves on this site is cheap at a universe variable and expensive at the universe `u` of the
schemes, so it is elaborated once here and read from the environment at the point of use. -/
theorem hasColimitsOfShape_algebraSheaf (J : Type u) [SmallCategory J] [IsConnected J] :
    HasColimitsOfShape J (AlgebraSheaf.{u, u} B S hS F hF) :=
  let : HasColimitsOfShape J (Under (structureSheaf B S hS F hF)) := inferInstance
  Adjunction.hasColimitsOfShape_of_equivalence
    (AlgebraSheaf.toUnder (B := B) (S := S) (hS := hS) (F := F) (hF := hF))

/-! ### The criterion for quasi-coherent algebras

Stacks 082A and Stacks 086Z state their colimit assertions for cocones in
`AlgebraicGeometry.Space.QuasicoherentAlgebra`, the full subcategory of the quasi-coherent
algebra sheaves.  A full subcategory inclusion is fully faithful, hence reflects colimits, so
the criteria above apply there verbatim.
-/

/-- A cocone of quasi-coherent algebras is colimiting as soon as its image in all algebra
sheaves is: the inclusion is fully faithful, hence reflects colimits. -/
def isColimit_of_isColimit_quasicoherentAlgebraInclusion {X : AlgebraicSpaces B S hS}
    {J : Type w} [Category.{v} J] {Φ : J ⥤ QuasicoherentAlgebra B S hS X} (c : Cocone Φ)
    (hc : IsColimit ((quasicoherentAlgebraInclusion B S hS X).mapCocone c)) :
    IsColimit c :=
  isColimitOfReflects _ hc

/-- The sections of a quasi-coherent algebra over a fixed étale chart, as a functor. -/
def qcohChartSectionsFunctor {X : AlgebraicSpaces B S hS} (U : SmallEtale B S hS X.1) :
    QuasicoherentAlgebra B S hS X ⥤ CommRingCat.{u} :=
  quasicoherentAlgebraInclusion B S hS X ⋙ AlgebraSheaf.chartSectionsFunctor U

/-- The value of `qcohChartSectionsFunctor U` at a quasi-coherent algebra is its ring of sections
over `U`. -/
@[simp]
theorem qcohChartSectionsFunctor_obj {X : AlgebraicSpaces B S hS} (U : SmallEtale B S hS X.1)
    (A : QuasicoherentAlgebra B S hS X) :
    (qcohChartSectionsFunctor U).obj A = A.obj.right.obj.obj (op U) :=
  rfl

/-- The image under `qcohChartSectionsFunctor U` of a morphism of quasi-coherent algebras is its
component at `U`. -/
@[simp]
theorem qcohChartSectionsFunctor_map {X : AlgebraicSpaces B S hS} (U : SmallEtale B S hS X.1)
    {A C : QuasicoherentAlgebra B S hS X} (f : A ⟶ C) :
    (qcohChartSectionsFunctor U).map f = f.hom.right.hom.app (op U) :=
  rfl

/-- **A cocone of quasi-coherent algebras over a filtered diagram is colimiting as soon as, over
every affine étale chart, its components are jointly surjective on sections and two sections
with the same image already agree at a later index.**

This is the shape in which Stacks 082A and Stacks 086Z state their colimit assertion, produced
from a statement about the sections over the affine étale charts.  The implication runs one way
only; see the module documentation. -/
theorem nonempty_isColimit_quasicoherentAlgebra_of_affineChartSections
    {X : AlgebraicSpaces B S hS} {J : Type w} [Category.{v} J] [IsFiltered J]
    {Φ : J ⥤ QuasicoherentAlgebra B S hS X} (c : Cocone Φ)
    (hsurj : ∀ U : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
        ∀ x : (qcohChartSectionsFunctor U).obj c.pt,
          ∃ (k : J) (y : (qcohChartSectionsFunctor U).obj (Φ.obj k)),
            (qcohChartSectionsFunctor U).map (c.ι.app k) y = x)
    (hinj : ∀ U : SmallEtale B S hS X.1,
      IsAffine ((SmallEtale.toOver B S hS X.1 ⋙ BigFppfOver.toScheme B S hS).obj U) →
        ∀ (k : J) (x y : (qcohChartSectionsFunctor U).obj (Φ.obj k)),
          (qcohChartSectionsFunctor U).map (c.ι.app k) x =
              (qcohChartSectionsFunctor U).map (c.ι.app k) y →
            ∃ (l : J) (f : k ⟶ l),
              (Φ ⋙ qcohChartSectionsFunctor U).map f x = (Φ ⋙ qcohChartSectionsFunctor U).map f y) :
    Nonempty (IsColimit c) := by
  obtain ⟨hc⟩ := AlgebraSheaf.nonempty_isColimit_of_affineChartSections
    ((quasicoherentAlgebraInclusion B S hS X).mapCocone c) hsurj hinj
  exact ⟨isColimit_of_isColimit_quasicoherentAlgebraInclusion c hc⟩

end AlgebraicGeometry.Space

end
