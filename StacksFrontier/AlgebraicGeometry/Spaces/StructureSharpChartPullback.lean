module

public import StacksFrontier.AlgebraicGeometry.Spaces.SheafOfDifferentialsMap

/-!
# The image of the structure map, chart by chart

Let `f : X ⟶ Y` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf
site `B`.  The structure map of `f` in inverse-image form is a homomorphism
`f♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` of sheaves of commutative rings on the small étale site of `X`
(Stacks 03G8), and the sections of `f^{-1}𝒪_Y` are computed by no formula: the inverse image is
a sheafification.  This file identifies, for the purpose of *testing a morphism out of `𝒪_X` on
the image of `f♯`*, exactly which sections of `𝒪_X` have to be looked at.

They are the chartwise pullbacks `AlgebraicGeometry.Space.chartPullback`: for an étale scheme
chart `V` of `Y` and an étale scheme chart of `X` above `X ×_Y V`, the pullback of a regular
function on `V` along the induced morphism of schemes.  Two morphisms of sheaves of sets out of
`𝒪_X` agree after `f♯` **exactly** when they agree on every such section; both directions are
proved here, with no hypothesis.

This is the comparison that the invertibility clause of Stacks 04CS and the final sentence of
Stacks 04CU need.  Stacks 04CS compares `(Ω_{X/Y})^a` with `Ω_{X_étale/Y_étale}` for a morphism
of schemes.  The first is corepresented, by
`AlgebraicGeometry.SmallEtale.existsUnique_postcomp_associatedDerivation`, among the derivations
of `𝒪_{X_étale}` subject to a *vanishing on named sections* — the functions pulled back from the
opens of `Y`, and, by `AlgebraicGeometry.SmallEtale.associatedDerivation_etaleBase_eq_zero`, from
the schemes étale over `Y`.  The second is the module of differentials of `f♯`, whose definition
names the sheaf `f^{-1}𝒪_Y` instead.  The lemmas below match the two descriptions of the class of
derivations: a derivation vanishes on the image of `f♯` precisely when it kills every chartwise
pullback.

## Main results

* `AlgebraicGeometry.Space.chartIsLimitSheaf`,
  `AlgebraicGeometry.Space.chartProjection_app_apply_sheaf` and
  `AlgebraicGeometry.Space.chartProjection_ext_sheaf`: the sections over an étale chart `V` of
  `Y` of the direct image of an *arbitrary* sheaf of sets are the limit of its sections over the
  étale charts of `X` above `X ×_Y V`, and `AlgebraicGeometry.Space.chartProjection` computes
  the projections of that limit.  These generalize
  `AlgebraicGeometry.Space.chartIsLimit`, `AlgebraicGeometry.Space.chartProjection_app_apply`
  and `AlgebraicGeometry.Space.chartProjection_ext`, which are stated for the structure sheaf
  only, by the same proofs.
* `AlgebraicGeometry.Space.structureSharpSet_comp_eq_iff_chartPullback`: **two morphisms of
  sheaves of sets out of `𝒪_X` agree after the direct-image form `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of the
  structure map if and only if they agree on every chartwise pullback.**
* `AlgebraicGeometry.Space.structureSharpInverseImageSet_comp_eq_iff_chartPullback`: the same for
  the inverse-image form `f♯ : f^{-1}𝒪_Y ⟶ 𝒪_X`, by the adjunction of Stacks 03G8.  So the
  chartwise pullbacks generate the image of `f♯` for the purpose of testing a morphism on it.
* `AlgebraicGeometry.Space.derivation_d_chartPullback_eq_zero`: a `Y`-derivation of `𝒪_X` kills
  every chartwise pullback.
* `AlgebraicGeometry.Space.Derivation'.ofChartPullback`: conversely, a derivation of `𝒪_X`
  killing every chartwise pullback *is* a `Y`-derivation — a derivation relative to
  `f♯ : f^{-1}𝒪_Y ⟶ 𝒪_X`, which is what `AlgebraicGeometry.Space.sheafOfDifferentials`
  corepresents.  Its underlying additive map is unchanged.

## Implementation notes

Both directions run through the direct-image form of the structure map, and the content of the
file is the computation of the sections of the direct image at an arbitrary sheaf of sets.

The direct-image form is `f♯ : 𝒪_Y ⟶ f_*𝒪_X`, whose sections over `V` are, by
`AlgebraicGeometry.Space.structureMapApp`, exactly the family of chartwise pullbacks of a regular
function on `V`; so a condition on the chartwise pullbacks *is* a condition after the
direct-image form.  The adjunction `f^{-1} ⊣ f_*` of Stacks 03G8 then carries it both ways
between the two forms of the structure map, by
`AlgebraicGeometry.Space.structureSharpInverseImage_of_structureSharpSetComp` and
`AlgebraicGeometry.Space.structureSharpSetComp_of_structureSharpInverseImage`.  No section of
`f^{-1}𝒪_Y` is ever exhibited and none is needed.

Reading a condition after the direct-image form uses the limit description of the sections of
the direct image at the sheaf of sets underlying the *coefficient* module, not at the structure
sheaf, which is why `AlgebraicGeometry.Space.chartIsLimit`,
`AlgebraicGeometry.Space.chartProjection_app_apply` and
`AlgebraicGeometry.Space.chartProjection_ext` are generalized here.  Their proofs are unchanged:
the right Kan extension along the comparison functor of Stacks 03G1 is pointwise at every sheaf
of sets, and `AlgebraicGeometry.Space.chartProjection` is already a natural transformation of
functors of the sheaf, so it has the generalized statements' projections as its components.

The sections of the direct image are compared with their Kan-extension form through
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso`, whose naturality in the sheaf is what
moves a condition between the two; that is
`AlgebraicGeometry.Space.structureSharpSet_comp_eq_iff_ran`.

## References

* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8), the morphism of small
  étale ringed topoi of a morphism of algebraic spaces and its structure map.
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1), the comparison of the
  small étale site of an algebraic space with its site of étale algebraic spaces.
* [Stacks Project, Tag 04CT](https://stacks.math.columbia.edu/tag/04CT), the sheaf of
  differentials of a morphism of algebraic spaces and its universal derivation.
* [Stacks Project, Tag 04CS](https://stacks.math.columbia.edu/tag/04CS), the comparison of the
  differentials of a morphism of schemes on its small Zariski and small étale sites.
* [Stacks Project, Tag 04CU](https://stacks.math.columbia.edu/tag/04CU), the identification
  `Ω_{X/Y}|_{U_étale} = Ω_{U/V}` on a square of étale charts.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CategoryTheory.Sheaf CategoryTheory.Functor
open Opposite

universe w u

namespace CategoryTheory.Sheaf

variable {C : Type*} [Category C] {J : GrothendieckTopology C}

/-- Two morphisms of sheaves of types which agree after a third have equal effects on every
section in the image of that third one.  Stated at an arbitrary site, so that the composites it
is applied to — which are large terms — are never rewritten inside.

This is the companion of `CategoryTheory.Sheaf.hom_ext_sections` for a condition imposed only
after a fixed morphism. -/
theorem congr_sections_comp {A A' A'' : Sheaf J (Type w)} (n : A ⟶ A') {m m' : A' ⟶ A''}
    (h : n ≫ m = n ≫ m') (U : Cᵒᵖ) (s : (sectionsFunctor J U).obj A) :
    (sectionsFunctor J U).map m ((sectionsFunctor J U).map n s) =
      (sectionsFunctor J U).map m' ((sectionsFunctor J U).map n s) := by
  rw [← (sectionsFunctor J U).map_comp_apply, ← (sectionsFunctor J U).map_comp_apply, h]

/-- Two morphisms of sheaves of types agree after a third as soon as they agree on every section
in the image of that third one.  Stated at an arbitrary site, for the same reason. -/
theorem comp_eq_of_sections {A A' A'' : Sheaf J (Type w)} (n : A ⟶ A') (m m' : A' ⟶ A'')
    (h : ∀ (U : Cᵒᵖ) (s : (sectionsFunctor J U).obj A),
      (sectionsFunctor J U).map m ((sectionsFunctor J U).map n s) =
        (sectionsFunctor J U).map m' ((sectionsFunctor J U).map n s)) :
    n ≫ m = n ≫ m' := by
  refine hom_ext_sections fun U s ↦ ?_
  rw [(sectionsFunctor J U).map_comp_apply, (sectionsFunctor J U).map_comp_apply]
  exact h U s

end CategoryTheory.Sheaf

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-! ### The sections of the direct image of an arbitrary sheaf of sets -/

/-- The sections over an étale chart `V` of `Y` of the direct image of a sheaf of sets `E` on the
small étale site of `X` are the limit of the sections of `E` over the étale scheme charts of `X`
above `X ×_Y V`.

This is `AlgebraicGeometry.Space.chartIsLimit` with the structure sheaf of `X` replaced by an
arbitrary sheaf of sets; the right Kan extension along the comparison functor of Stacks 03G1 is
pointwise for every one of them. -/
noncomputable def chartIsLimitSheaf (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (E : Sheaf (SmallEtale.topology B S hS X.1) (Type u)) :
    IsLimit ((Functor.RightExtension.mk _
      ((comparisonFunctor B S hS X).op.ranCounit.app E.obj)).coneAt
      (op (chartBaseChange B S hS f V))) :=
  (comparisonFunctor B S hS X).op.isPointwiseRightKanExtensionRanCounit E.obj
    (op (chartBaseChange B S hS f V))

/-- The chart projection of `AlgebraicGeometry.Space.chartProjection`, read at an arbitrary sheaf
of sets, is the projection of the limit cone of `AlgebraicGeometry.Space.chartIsLimitSheaf`.

This is `AlgebraicGeometry.Space.chartProjection_app_apply` with the structure sheaf of `X`
replaced by an arbitrary sheaf of sets. -/
theorem chartProjection_app_apply_sheaf (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (E : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (a : ((comparisonFunctor B S hS X).op.ran.obj E.obj).obj
      (op (chartBaseChange B S hS f V))) :
    (chartProjection B S hS f V j).app E a =
      ((Functor.RightExtension.mk _
        ((comparisonFunctor B S hS X).op.ranCounit.app E.obj)).coneAt
        (op (chartBaseChange B S hS f V))).π.app j a := by
  have h : (((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app E).hom =
      (comparisonFunctor B S hS X).op.ranCounit.app E.obj := by
    rw [Functor.sheafAdjunctionCocontinuous_counit_app_hom, Functor.ranAdjunction_counit]
  change (((comparisonFunctor B S hS X).sheafAdjunctionCocontinuous (Type u)
        (SmallEtale.topology B S hS X.1) (SpacesEtale.topology B S hS X)).counit.app
        E).hom.app j.right
      (((comparisonFunctor B S hS X).op.ran.obj E.obj).map j.hom a) = _
  rw [h]
  rfl

/-- Two sections over `V` of the direct image of a sheaf of sets agree as soon as all their chart
projections agree.

This is `AlgebraicGeometry.Space.chartProjection_ext` with the structure sheaf of `X` replaced
by an arbitrary sheaf of sets. -/
theorem chartProjection_ext_sheaf (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    (E : Sheaf (SmallEtale.topology B S hS X.1) (Type u))
    {a b : ((comparisonFunctor B S hS X).op.ran.obj E.obj).obj
      (op (chartBaseChange B S hS f V))}
    (h : ∀ j, (chartProjection B S hS f V j).app E a =
      (chartProjection B S hS f V j).app E b) :
    a = b := by
  refine (Types.isLimitEquivSections (chartIsLimitSheaf B S hS f V E)).injective
    (Subtype.ext (funext fun j ↦ ?_))
  exact (chartProjection_app_apply_sheaf B S hS f V E j a).symm.trans
    ((h j).trans (chartProjection_app_apply_sheaf B S hS f V E j b))

/-- The chart projection of the image of a section under the direct image of `ε` is `ε` on the
chart projection of that section: `AlgebraicGeometry.Space.chartProjection` is natural in the
sheaf of sets. -/
private theorem chartProjection_app_map_aux (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {E E' : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (ε : E ⟶ E')
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (a : (smallEtaleDirectImageRan B S hS f ⋙
      sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj E) :
    (chartProjection B S hS f V j).app E'
        ((smallEtaleDirectImageRan B S hS f ⋙
          sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).map ε a) =
      (sectionsFunctor (SmallEtale.topology B S hS X.1) j.right).map ε
        ((chartProjection B S hS f V j).app E a) := by
  have h := ConcreteCategory.congr_hom ((chartProjection B S hS f V j).naturality ε) a
  rwa [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply] at h

/-- The chart projection of the image of a section under the direct image of `ε` is `ε` on the
chart projection of that section. -/
theorem chartProjection_app_map (f : X ⟶ Y) (V : SmallEtale B S hS Y.1)
    {E E' : Sheaf (SmallEtale.topology B S hS X.1) (Type u)} (ε : E ⟶ E')
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (a : (sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).obj
      ((smallEtaleDirectImageRan B S hS f).obj E)) :
    (chartProjection B S hS f V j).app E'
        ((sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).map
          ((smallEtaleDirectImageRan B S hS f).map ε) a) =
      (sectionsFunctor (SmallEtale.topology B S hS X.1) j.right).map ε
        ((chartProjection B S hS f V j).app E a) :=
  chartProjection_app_map_aux B S hS f V ε j a

/-! ### Testing a morphism out of `𝒪_X` on the image of the structure map -/

/-- A condition after the direct-image form of the structure map may be read in the
Kan-extension form of the direct image, the two being compared by
`AlgebraicGeometry.Space.smallEtaleDirectImageRanIso`, which is natural in the sheaf. -/
theorem structureSharpSet_comp_eq_iff_ran (f : X ⟶ Y)
    {E : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (ε ε' : structureSetSheaf B S hS X ⟶ E) :
    structureSharpSet B S hS f ≫ (smallEtaleDirectImage B S hS f).map ε =
        structureSharpSet B S hS f ≫ (smallEtaleDirectImage B S hS f).map ε' ↔
      structureSharpRanSet B S hS f ≫ (smallEtaleDirectImageRan B S hS f).map ε =
        structureSharpRanSet B S hS f ≫ (smallEtaleDirectImageRan B S hS f).map ε' := by
  have hn : ∀ δ : structureSetSheaf B S hS X ⟶ E,
      structureSharpRanSet B S hS f ≫ (smallEtaleDirectImageRan B S hS f).map δ =
        (structureSharpSet B S hS f ≫ (smallEtaleDirectImage B S hS f).map δ) ≫
          (smallEtaleDirectImageRanIso B S hS f).hom.app E := by
    intro δ
    rw [Category.assoc, (smallEtaleDirectImageRanIso B S hS f).hom.naturality δ,
      ← Category.assoc, structureSharpSet_comp_ranIso]
  rw [hn ε, hn ε']
  exact (Iso.cancel_iso_hom_right _ _ ((smallEtaleDirectImageRanIso B S hS f).app E)).symm

/-- **Two morphisms of sheaves of sets out of `𝒪_X` agree after the direct-image form
`f♯ : 𝒪_Y ⟶ f_*𝒪_X` of the structure map exactly when they agree on every chartwise pullback of
a regular function.**

The sections of the direct image over an étale chart `V` of `Y` are the limit of the sections
over the étale charts of `X` above `X ×_Y V`, and the structure map sends a regular function on
`V` to the family of its chartwise pullbacks
(`AlgebraicGeometry.Space.chartProjection_structureMapApp`). -/
theorem structureSharpSet_comp_eq_iff_chartPullback (f : X ⟶ Y)
    {E : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (ε ε' : structureSetSheaf B S hS X ⟶ E) :
    structureSharpSet B S hS f ≫ (smallEtaleDirectImage B S hS f).map ε =
        structureSharpSet B S hS f ≫ (smallEtaleDirectImage B S hS f).map ε' ↔
      ∀ (V : SmallEtale B S hS Y.1)
        (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
        (g : (structureSetSheaf B S hS Y).obj.obj (op V)),
        (sectionsFunctor (SmallEtale.topology B S hS X.1) j.right).map ε
            (chartPullback B S hS f V j g) =
          (sectionsFunctor (SmallEtale.topology B S hS X.1) j.right).map ε'
            (chartPullback B S hS f V j g) := by
  rw [structureSharpSet_comp_eq_iff_ran B S hS f ε ε']
  have hp : ∀ (V : SmallEtale B S hS Y.1)
      (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
      (g : (structureSetSheaf B S hS Y).obj.obj (op V)),
      (chartProjection B S hS f V j).app (structureSetSheaf B S hS X)
          ((sectionsFunctor (SmallEtale.topology B S hS Y.1) (op V)).map
            (structureSharpRanSet B S hS f) g) =
        chartPullback B S hS f V j g :=
    fun V j g ↦ chartProjection_structureMapApp B S hS f V j g
  refine ⟨fun h V j g ↦ ?_, fun h ↦ ?_⟩
  · have hs := congr_sections_comp (structureSharpRanSet B S hS f) h (op V) g
    have hc := congrArg ((chartProjection B S hS f V j).app E) hs
    rwa [chartProjection_app_map B S hS f V ε j _,
      chartProjection_app_map B S hS f V ε' j _, hp V j g] at hc
  · refine comp_eq_of_sections (structureSharpRanSet B S hS f) _ _ (fun W g ↦ ?_)
    refine chartProjection_ext_sheaf B S hS f W.unop E (fun j ↦ ?_)
    rw [chartProjection_app_map B S hS f W.unop ε j _,
      chartProjection_app_map B S hS f W.unop ε' j _, hp W.unop j g]
    exact h W.unop j g

/-- **Two morphisms of sheaves of sets out of `𝒪_X` agree after the inverse-image form
`f♯ : f^{-1}𝒪_Y ⟶ 𝒪_X` of the structure map exactly when they agree on every chartwise pullback
of a regular function.**

So the chartwise pullbacks generate the image of `f♯` for the purpose of testing a morphism on
it, even though no section of `f^{-1}𝒪_Y` is written down: the two forms of the structure map are
adjunct, by Stacks 03G8, and the condition transports both ways. -/
theorem structureSharpInverseImageSet_comp_eq_iff_chartPullback (f : X ⟶ Y)
    {E : Sheaf (SmallEtale.topology B S hS X.1) (Type u)}
    (ε ε' : structureSetSheaf B S hS X ⟶ E) :
    structureSharpInverseImageSet B S hS f ≫ ε =
        structureSharpInverseImageSet B S hS f ≫ ε' ↔
      ∀ (V : SmallEtale B S hS Y.1)
        (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
        (g : (structureSetSheaf B S hS Y).obj.obj (op V)),
        (sectionsFunctor (SmallEtale.topology B S hS X.1) j.right).map ε
            (chartPullback B S hS f V j g) =
          (sectionsFunctor (SmallEtale.topology B S hS X.1) j.right).map ε'
            (chartPullback B S hS f V j g) :=
  ⟨fun h ↦ (structureSharpSet_comp_eq_iff_chartPullback B S hS f ε ε').1
      (structureSharpSetComp_of_structureSharpInverseImage B S hS f ε ε' h),
   fun h ↦ structureSharpInverseImage_of_structureSharpSetComp B S hS f ε ε'
      ((structureSharpSet_comp_eq_iff_chartPullback B S hS f ε ε').2 h)⟩

/-! ### The two descriptions of a `Y`-derivation of `𝒪_X` -/

section Derivation

variable {F : Modules.{u, u} B S hS X.1 X.2}
  {R : (SmallEtale B S hS X.1)ᵒᵖ ⥤ CommRingCat.{u}}
  {ψ : R ⟶ structurePresheaf B S hS X.1}

/-- A derivation of `𝒪_X` with values in an `𝒪_X`-module, read as a morphism of the underlying
sheaves of sets.  This is `AlgebraicGeometry.Space.universalDerivationHom` for an arbitrary
derivation. -/
noncomputable def derivationSetHom (D : F.val.Derivation' ψ) :
    structureSetSheaf B S hS X ⟶
      moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) F :=
  unaryOpHom (fun _ a ↦ D.d a) (fun g a ↦ (D.d_map g a).symm)

/-- The zero derivation, read as a morphism of the underlying sheaves of sets. -/
noncomputable def zeroSetHom (F : Modules.{u, u} B S hS X.1 X.2) :
    structureSetSheaf B S hS X ⟶
      moduleSheaf.{u, u, u + 1} (structureRingSheaf B S hS X) F :=
  unaryOpHom (fun W (_ : (structureRingSheaf B S hS X).obj.obj W) ↦ (0 : F.val.obj W))
    (fun g _ ↦ (F.val.map g).hom.map_zero)

/-- On sections, the morphism of sheaves of sets attached to a derivation is the derivation. -/
theorem sectionsFunctor_map_derivationSetHom (D : F.val.Derivation' ψ)
    {W : (SmallEtale B S hS X.1)ᵒᵖ} (a : (structureRingSheaf B S hS X).obj.obj W) :
    (sectionsFunctor (SmallEtale.topology B S hS X.1) W).map (derivationSetHom B S hS D) a =
      D.d a := rfl

/-- On sections, the morphism of sheaves of sets attached to the zero derivation is zero. -/
theorem sectionsFunctor_map_zeroSetHom (F : Modules.{u, u} B S hS X.1 X.2)
    {W : (SmallEtale B S hS X.1)ᵒᵖ} (a : (structureRingSheaf B S hS X).obj.obj W) :
    (sectionsFunctor (SmallEtale.topology B S hS X.1) W).map (zeroSetHom B S hS F) a =
      (0 : F.val.obj W) := rfl

/-- **A `Y`-derivation of `𝒪_X` kills every chartwise pullback of a regular function from an
étale chart of `Y`.**

A `Y`-derivation is a derivation relative to `f♯ : f^{-1}𝒪_Y ⟶ 𝒪_X`, so it kills the image of
`f♯`, and the chartwise pullbacks lie in that image for the purpose of
`AlgebraicGeometry.Space.structureSharpInverseImageSet_comp_eq_iff_chartPullback`. -/
theorem derivation_d_chartPullback_eq_zero (f : X ⟶ Y)
    (D : F.val.Derivation' (structureSharpInverseImage B S hS f).hom)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
    (g : (structureSetSheaf B S hS Y).obj.obj (op V)) :
    D.d (chartPullback B S hS f V j g) = 0 :=
  (structureSharpInverseImageSet_comp_eq_iff_chartPullback B S hS f
      (derivationSetHom B S hS D) (zeroSetHom B S hS F)).1
    (comp_eq_of_sections (structureSharpInverseImageSet B S hS f) _ _
      (fun _ s ↦ D.d_app s)) V j g

/-- **A derivation of `𝒪_X` killing every chartwise pullback of a regular function from an étale
chart of `Y` is a `Y`-derivation**: a derivation relative to `f♯ : f^{-1}𝒪_Y ⟶ 𝒪_X`, which is
the base that `AlgebraicGeometry.Space.sheafOfDifferentials` takes its differentials over.

The underlying additive map is unchanged: only the vanishing condition differs between the two
notions, and `AlgebraicGeometry.Space.structureSharpInverseImageSet_comp_eq_iff_chartPullback`
turns the chartwise vanishing into the vanishing on the image of `f♯`. -/
noncomputable def Derivation'.ofChartPullback (f : X ⟶ Y) (D : F.val.Derivation' ψ)
    (h : ∀ (V : SmallEtale B S hS Y.1)
      (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
      (g : (structureSetSheaf B S hS Y).obj.obj (op V)),
      D.d (chartPullback B S hS f V j g) = 0) :
    F.val.Derivation' (structureSharpInverseImage B S hS f).hom where
  d := D.d
  d_mul := D.d_mul
  d_map := D.d_map
  d_app {W} s :=
    congr_sections_comp (structureSharpInverseImageSet B S hS f)
      ((structureSharpInverseImageSet_comp_eq_iff_chartPullback B S hS f
        (derivationSetHom B S hS D) (zeroSetHom B S hS F)).2 h) W s

/-- The derivation of `AlgebraicGeometry.Space.Derivation'.ofChartPullback` has the same
underlying additive map as the one it is built from. -/
@[simp]
theorem Derivation'.ofChartPullback_d (f : X ⟶ Y) (D : F.val.Derivation' ψ)
    (h : ∀ (V : SmallEtale B S hS Y.1)
      (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op)
      (g : (structureSetSheaf B S hS Y).obj.obj (op V)),
      D.d (chartPullback B S hS f V j g) = 0)
    {W : (SmallEtale B S hS X.1)ᵒᵖ} (x : (structureRingSheaf B S hS X).obj.obj W) :
    (Derivation'.ofChartPullback B S hS f D h).d x = D.d x := rfl

end Derivation

end AlgebraicGeometry.Space

end
