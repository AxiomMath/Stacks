module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.QuasicoherentCoprod
public import StacksFrontier.AlgebraicGeometry.PushforwardColimits.Unit
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraAffineChartLocality
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraColimits
public import StacksFrontier.AlgebraicGeometry.Spaces.DirectImageAlgebraPullbackUnit
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf

/-!
# The unit and the counit of Stacks 03D4 at a free module and at a presentation

Let `f : Y ⟶ X` be a morphism of algebraic spaces over a scheme `S` contained in a big fppf site
`B`, and let `𝒜 = f_*𝒪_Y`.  `AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` is
Stacks 03D4 for the small étale sites,

`𝒢 ↦ 𝒪_Y ⊗_{f⁻¹𝒜} f⁻¹𝒢  ⊣  ℱ ↦ f_*ℱ`,

and the first assertion of Stacks 08AI is that its unit and counit are invertible at
quasi-coherent modules.  The base case — the unit at `𝒜` regarded as a module over itself and the
counit at `𝒪_Y`, for an arbitrary `f` — is
`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_unit` and
`...counit_app_unit`.  This file runs the colimit argument on top of it: from the unit module to a
free module on an arbitrary index type, and from there to a module with a
`SheafOfModules.Presentation`.

It is the transposition to the small étale sites of
`StacksFrontier/AlgebraicGeometry/PushforwardColimits/Unit.lean`, whose four statements
`Stacks.AlgebraicGeometry.PushforwardColimits.isIso_unit_app_free`,
`...isIso_counit_app_free`, `...isIso_unit_app_of_presentation` and
`...isIso_counit_app_of_presentation` are the scheme-level case of the tag, Stacks 01SB.  The
plain category theory of the argument is shared with them and not restated:
`Stacks.AlgebraicGeometry.PushforwardColimits.isIso_app_of_isColimit` is already stated for an
arbitrary natural transformation between functors of arbitrary categories.

## The hypotheses, and why the target is representable

**Affineness of `f` alone is not enough, and a representable target is not a weakening.**  The
only colimit input this tree has for direct image along an affine morphism of algebraic spaces is
`AlgebraicGeometry.Space.preservesColimit_moduleDirectImage_of_schemeTarget`, which asks the
target to be a representable algebraic space `schemeSpace V`.  Preservation of a colimit is not
a local property of the base, so no chartwise glueing removes the hypothesis.

A representable target is therefore the generality in which every statement below is stated — and
it is exactly the generality that the chartwise reduction of the tag consumes.
`AlgebraicGeometry.Space.affineDirectImageEquivalence_of_isIso_over_affineCharts` tests the unit
and the counit on the slice at one affine étale chart of `X` at a time, and an étale chart of an
algebraic space is representable by construction.

The two instance binders of the colimit statement that are about the shape of the diagram rather
than about `f` are discharged, not assumed, at both shapes used here: a discrete shape on a type
in the module universe, and `CategoryTheory.Limits.WalkingParallelPair`.  For the second, the left
adjoint's preservation of colimits has to be taken at the smallest size — the instance
`AlgebraicGeometry.Space.preservesColimitsOfSize_directImageAlgebraPullback` is stated at `u`, and
`WalkingParallelPair` is a category in `Type 0` — so it is re-derived from
`CategoryTheory.Adjunction.leftAdjoint_preservesColimits`, which is universe-polymorphic.

## Main results

* `AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback_unit` — the left
  adjoint carries `𝒜`, regarded as a module over itself, to a quasi-coherent `𝒪_Y`-module.  No
  hypothesis on `f`.
* `AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_free` — **the unit
  of Stacks 03D4 is invertible at the free `𝒜`-module on an arbitrary type**, for an affine
  morphism with representable target.
* `AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_counit_app_free` — the
  counit is invertible at the free `𝒪_Y`-module on an arbitrary type.
* `AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_of_presentation`
  and `...counit_app_of_presentation` — **both are invertible at a module admitting a
  presentation.**
* `AlgebraicGeometry.Space.affineDirectImageEquivalence_of_schemeTarget_of_presentations` — **the
  first assertion of Stacks 08AI for an affine morphism with representable target, granted that
  quasi-coherent modules on the two small étale sites involved admit presentations.**  For a
  representable target no chartwise reduction is needed.

## Implementation notes

The colimit exhibiting a presentation is written at the folded spelling
`SheafOfModules.Presentation.relationsHom` and
`SheafOfModules.Presentation.isColimitRelationsHom` of
`StacksFrontier/Algebra/Category/ModuleCat/Sheaf/QuasicoherentCoprod.lean` rather than at Mathlib's
unfolded `SheafOfModules.Presentation.isColimit`, which keeps the diagram a single application
instead of a composite through `SheafOfModules.freeHomEquiv`.

`Stacks.AlgebraicGeometry.PushforwardColimits.isIso_app_of_isColimit` is applied at the two
presentation statements with **every implicit argument given**, the diagram and the cocone
included.  Left to unification they exhaust the heartbeat budget, and raising that budget would not
help: the unifier meets the conclusion `IsIso (η.app c.pt)` against the goal while the
cocone `c` is still a metavariable, so the projection `c.pt` cannot be solved and the search goes
elsewhere.  The free-module statements do not need it, their cocone point being the free module on
the nose.

Stacks 03D4 is the adjunction itself; the invertibility of its unit and counit at a free module or
at a presented module is a step in the proof of the first assertion of Stacks 08AI.

## References

* [Stacks Project, Tag 01SB](https://stacks.math.columbia.edu/tag/01SB)
* [Stacks Project, Tag 03D4](https://stacks.math.columbia.edu/tag/03D4)
* [Stacks Project, Tag 03LU](https://stacks.math.columbia.edu/tag/03LU)
* [Stacks Project, Tag 08AI](https://stacks.math.columbia.edu/tag/08AI)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.Space

open Stacks.AlgebraicGeometry.PushforwardColimits

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {Y X : AlgebraicSpaces B S hS}

/-- **The left adjoint of Stacks 03D4 carries `𝒜` to a quasi-coherent `𝒪_Y`-module**, for
`𝒜 = f_*𝒪_Y` regarded as a module over itself and with no hypothesis on `f`: it carries it to
`𝒪_Y` by `AlgebraicGeometry.Space.directImageAlgebraPullbackObjUnitIso`, and the structure sheaf
is quasi-coherent over any sheaf of rings on any site. -/
theorem isQuasicoherentOnSite_directImageAlgebraPullback_unit (f : Y ⟶ X) :
    ((directImageAlgebraPullback B S hS f).obj
      (SheafOfModules.unit (structureRingSheafDirectImage B S hS f))).IsQuasicoherentOnSite :=
  SheafOfModules.IsQuasicoherentOnSite.of_iso
    (directImageAlgebraPullbackObjUnitIso B S hS f).symm
    (SheafOfModules.isQuasicoherentOnSite_unit (structureRingSheaf B S hS Y))

/-- **The unit of Stacks 03D4 is invertible at a free module.**  For an affine morphism
`f : Y ⟶ schemeSpace V` of algebraic spaces with representable target, `𝒜 = f_*𝒪_Y` and an
arbitrary type `I`, the unit of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` is invertible at the free
`𝒜`-module on `I`.

The free module is the coproduct of copies of `𝒜`, at which the unit is invertible by
`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_unit`; the left
adjoint preserves that coproduct, being a left adjoint, and the direct image over `𝒜` preserves it
by `AlgebraicGeometry.Space.preservesColimit_moduleDirectImage_of_schemeTarget`, the copies of
`𝒜` going to quasi-coherent `𝒪_Y`-modules. -/
theorem isIso_directImageAlgebraPullbackAdjunction_unit_app_free (V : BigFppfOver B S hS)
    (f : Y ⟶ schemeSpace V) (hf : IsAffineHom B S hS f.hom) (I : Type u) :
    IsIso ((directImageAlgebraPullbackAdjunction B S hS f).unit.app
      (SheafOfModules.free.{u} (R := structureRingSheafDirectImage B S hS f) I)) := by
  have hE : ∀ k : Discrete I,
      (((Discrete.functor fun _ : I ↦
            SheafOfModules.unit (structureRingSheafDirectImage B S hS f)) ⋙
          directImageAlgebraPullback B S hS f).obj k).IsQuasicoherentOnSite :=
    fun _ ↦ isQuasicoherentOnSite_directImageAlgebraPullback_unit B S hS f
  have _hp2 : PreservesColimit
      ((Discrete.functor fun _ : I ↦
          SheafOfModules.unit (structureRingSheafDirectImage B S hS f)) ⋙
        directImageAlgebraPullback B S hS f)
      (moduleDirectImage B S hS f) :=
    preservesColimit_moduleDirectImage_of_schemeTarget B S hS V f hf hE
  have hp : PreservesColimit
      (Discrete.functor fun _ : I ↦
        SheafOfModules.unit (structureRingSheafDirectImage B S hS f))
      (directImageAlgebraPullback B S hS f ⋙ moduleDirectImage B S hS f) :=
    inferInstance
  exact isIso_app_of_isColimit ((directImageAlgebraPullbackAdjunction B S hS f).unit)
    (isColimitOfPreserves (𝟭 (SheafOfModules.{u} (structureRingSheafDirectImage B S hS f)))
      (SheafOfModules.isColimitFreeCofan I))
    (hp.preserves (SheafOfModules.isColimitFreeCofan I)).some
    fun _ ↦ isIso_directImageAlgebraPullbackAdjunction_unit_app_unit B S hS f

/-- **The counit of Stacks 03D4 is invertible at a free module.**  For an affine morphism
`f : Y ⟶ schemeSpace V` with representable target and an arbitrary type `I`, the counit of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` is invertible at the free
`𝒪_Y`-module on `I`.

The counit is invertible at the image under the left adjoint of the free `𝒜`-module, by
`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_counit_app_pullback` and
`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_free`, and
`AlgebraicGeometry.Space.directImageAlgebraPullbackFreeIso` identifies that module with the free
`𝒪_Y`-module; naturality of the counit transports the conclusion. -/
theorem isIso_directImageAlgebraPullbackAdjunction_counit_app_free (V : BigFppfOver B S hS)
    (f : Y ⟶ schemeSpace V) (hf : IsAffineHom B S hS f.hom) (I : Type u) :
    IsIso ((directImageAlgebraPullbackAdjunction B S hS f).counit.app
      (SheafOfModules.free.{u} (R := structureRingSheaf B S hS Y) I)) := by
  have : IsIso (directImageAlgebraPullbackFreeIso B S hS f I).hom :=
    (directImageAlgebraPullbackFreeIso B S hS f I).isIso_hom
  exact @IsIso.of_isIso_fac_left _ _ _ _ _ _ _ _
    (Functor.map_isIso (moduleDirectImage B S hS f ⋙ directImageAlgebraPullback B S hS f)
      (directImageAlgebraPullbackFreeIso B S hS f I).hom)
    (@IsIso.comp_isIso _ _ _ _ _ _ _
      (isIso_directImageAlgebraPullbackAdjunction_counit_app_pullback B S hS f _
        (isIso_directImageAlgebraPullbackAdjunction_unit_app_free B S hS V f hf I))
      (Functor.map_isIso (𝟭 (Modules.{u, u} B S hS Y.1 Y.2))
        (directImageAlgebraPullbackFreeIso B S hS f I).hom))
    ((directImageAlgebraPullbackAdjunction B S hS f).counit.naturality
      (directImageAlgebraPullbackFreeIso B S hS f I).hom)

/-- **The unit of Stacks 03D4 is invertible at an `𝒜`-module admitting a presentation.**  For an
affine morphism `f : Y ⟶ schemeSpace V` with representable target and `𝒜 = f_*𝒪_Y`, the unit of
`AlgebraicGeometry.Space.directImageAlgebraPullbackAdjunction` is invertible at any `𝒜`-module
carrying a `SheafOfModules.Presentation`.

A presentation exhibits the module as the cokernel of a morphism between free modules, hence as
the point of a colimit cocone over a diagram of free modules.  Both functors of the adjunction
preserve that colimit — the left adjoint because it is one, the direct image over `𝒜` by
`AlgebraicGeometry.Space.preservesColimit_moduleDirectImage_of_schemeTarget`, the two free
`𝒜`-modules going to quasi-coherent `𝒪_Y`-modules by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback_free` — and the unit is
invertible at both of them by
`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_free`. -/
theorem isIso_directImageAlgebraPullbackAdjunction_unit_app_of_presentation
    (V : BigFppfOver B S hS) (f : Y ⟶ schemeSpace V) (hf : IsAffineHom B S hS f.hom)
    (G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f)) (P : G.Presentation) :
    IsIso ((directImageAlgebraPullbackAdjunction B S hS f).unit.app G) := by
  have hE : ∀ k, ((parallelPair P.relationsHom 0 ⋙
      directImageAlgebraPullback B S hS f).obj k).IsQuasicoherentOnSite := by
    intro k
    obtain _ | _ := k
    · exact isQuasicoherentOnSite_directImageAlgebraPullback_free B S hS f P.relations.I
    · exact isQuasicoherentOnSite_directImageAlgebraPullback_free B S hS f P.generators.I
  have _hp2 : PreservesColimit
      (parallelPair P.relationsHom 0 ⋙ directImageAlgebraPullback B S hS f)
      (moduleDirectImage B S hS f) :=
    preservesColimit_moduleDirectImage_of_schemeTarget B S hS V f hf hE
  have _hpL : PreservesColimitsOfSize.{0, 0} (directImageAlgebraPullback B S hS f) :=
    (directImageAlgebraPullbackAdjunction B S hS f).leftAdjoint_preservesColimits
  have hp : PreservesColimit (parallelPair P.relationsHom 0)
      (directImageAlgebraPullback B S hS f ⋙ moduleDirectImage B S hS f) :=
    inferInstance
  have hfree : ∀ k, IsIso ((directImageAlgebraPullbackAdjunction B S hS f).unit.app
      ((parallelPair P.relationsHom 0).obj k)) := by
    intro k
    obtain _ | _ := k
    · exact isIso_directImageAlgebraPullbackAdjunction_unit_app_free B S hS V f hf P.relations.I
    · exact isIso_directImageAlgebraPullbackAdjunction_unit_app_free B S hS V f hf P.generators.I
  have h1 : IsColimit
      ((𝟭 (SheafOfModules.{u} (structureRingSheafDirectImage B S hS f))).mapCocone
        (CokernelCofork.ofπ (f := P.relationsHom) P.generators.π P.relationsHom_comp_π)) :=
    isColimitOfPreserves _ P.isColimitRelationsHom
  have h2 : IsColimit
      ((directImageAlgebraPullback B S hS f ⋙ moduleDirectImage B S hS f).mapCocone
        (CokernelCofork.ofπ (f := P.relationsHom) P.generators.π P.relationsHom_comp_π)) :=
    (hp.preserves P.isColimitRelationsHom).some
  exact @isIso_app_of_isColimit WalkingParallelPair _ _ _ _ _ _ _
    ((directImageAlgebraPullbackAdjunction B S hS f).unit) (parallelPair P.relationsHom 0)
    (CokernelCofork.ofπ (f := P.relationsHom) P.generators.π P.relationsHom_comp_π) h1 h2 hfree

/-- **The counit of Stacks 03D4 is invertible at an `𝒪_Y`-module admitting a presentation.**  This
is the argument of
`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_of_presentation` for
the counit: the composite of the direct image over `𝒜` with the left adjoint preserves the colimit
exhibiting the presentation — the direct image because the free `𝒪_Y`-modules occurring in it are
quasi-coherent and `f` is affine with representable target, the left adjoint because it is a left
adjoint — and the counit is invertible at a free module by
`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_counit_app_free`. -/
theorem isIso_directImageAlgebraPullbackAdjunction_counit_app_of_presentation
    (V : BigFppfOver B S hS) (f : Y ⟶ schemeSpace V) (hf : IsAffineHom B S hS f.hom)
    (M : Modules.{u, u} B S hS Y.1 Y.2) (P : M.Presentation) :
    IsIso ((directImageAlgebraPullbackAdjunction B S hS f).counit.app M) := by
  have hE : ∀ k, ((parallelPair P.relationsHom 0).obj k).IsQuasicoherentOnSite := by
    intro k
    obtain _ | _ := k
    · exact isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
        (isCartesianOnAffineCharts_free P.relations.I)
    · exact isQuasicoherentOnSite_of_isCartesianOnAffineCharts _
        (isCartesianOnAffineCharts_free P.generators.I)
  have _hp2 : PreservesColimit (parallelPair P.relationsHom 0) (moduleDirectImage B S hS f) :=
    preservesColimit_moduleDirectImage_of_schemeTarget B S hS V f hf hE
  have _hpL : PreservesColimitsOfSize.{0, 0} (directImageAlgebraPullback B S hS f) :=
    (directImageAlgebraPullbackAdjunction B S hS f).leftAdjoint_preservesColimits
  have hp : PreservesColimit (parallelPair P.relationsHom 0)
      (moduleDirectImage B S hS f ⋙ directImageAlgebraPullback B S hS f) :=
    inferInstance
  have hfree : ∀ k, IsIso ((directImageAlgebraPullbackAdjunction B S hS f).counit.app
      ((parallelPair P.relationsHom 0).obj k)) := by
    intro k
    obtain _ | _ := k
    · exact isIso_directImageAlgebraPullbackAdjunction_counit_app_free B S hS V f hf P.relations.I
    · exact isIso_directImageAlgebraPullbackAdjunction_counit_app_free B S hS V f hf
        P.generators.I
  have h1 : IsColimit
      ((moduleDirectImage B S hS f ⋙ directImageAlgebraPullback B S hS f).mapCocone
        (CokernelCofork.ofπ (f := P.relationsHom) P.generators.π P.relationsHom_comp_π)) :=
    (hp.preserves P.isColimitRelationsHom).some
  have h2 : IsColimit
      ((𝟭 (Modules.{u, u} B S hS Y.1 Y.2)).mapCocone
        (CokernelCofork.ofπ (f := P.relationsHom) P.generators.π P.relationsHom_comp_π)) :=
    isColimitOfPreserves _ P.isColimitRelationsHom
  exact @isIso_app_of_isColimit WalkingParallelPair _ _ _ _ _ _ _
    ((directImageAlgebraPullbackAdjunction B S hS f).counit) (parallelPair P.relationsHom 0)
    (CokernelCofork.ofπ (f := P.relationsHom) P.generators.π P.relationsHom_comp_π) h1 h2 hfree

/-- **The first assertion of Stacks 08AI for an affine morphism with representable target,
granted presentations.**  For `f : Y ⟶ schemeSpace V` affine,
`AlgebraicGeometry.Space.quasicoherentDirectImage` is an equivalence from the quasi-coherent
`𝒪_Y`-modules onto the quasi-coherent `𝒜`-modules as soon as every quasi-coherent `𝒜`-module and
every quasi-coherent `𝒪_Y`-module admits a `SheafOfModules.Presentation`.

The hypothesis `hL` of
`AlgebraicGeometry.Space.affineDirectImageEquivalence_of_isIso_unit_counit` is discharged by
`AlgebraicGeometry.Space.isQuasicoherentOnSite_directImageAlgebraPullback`, and its two
invertibility hypotheses by
`AlgebraicGeometry.Space.isIso_directImageAlgebraPullbackAdjunction_unit_app_of_presentation` and
`...counit_app_of_presentation`.

Neither hypothesis is the conclusion in disguise: each is the statement that a quasi-coherent
module on one small étale site is the cokernel of a map of free modules *globally*, which
`SheafOfModules.IsQuasicoherentOnSite` gives only on a covering.  **Both hold when the
underlying scheme of `V` is affine**, by
`AlgebraicGeometry.Space.nonempty_presentation_directImageAlgebra_of_isAffine` and
`AlgebraicGeometry.Space.nonempty_presentation_of_isAffineHom_of_isAffine`
(`StacksFrontier/AlgebraicGeometry/Spaces/DirectImageAlgebraAffineTarget.lean`), which give the
unconditional `AlgebraicGeometry.Space.affineDirectImageEquivalence_of_affineSchemeTarget` there;
affineness of `V` is a necessary hypothesis for them, since on a non-affine base a quasi-coherent
module need not be a quotient of a free module at all. -/
theorem affineDirectImageEquivalence_of_schemeTarget_of_presentations (V : BigFppfOver B S hS)
    (f : Y ⟶ schemeSpace V) (hf : IsAffineHom B S hS f.hom)
    (hG : ∀ G : SheafOfModules.{u} (structureRingSheafDirectImage B S hS f),
      G.IsQuasicoherentOnSite → Nonempty G.Presentation)
    (hM : ∀ M : Modules.{u, u} B S hS Y.1 Y.2,
      M.IsQuasicoherentOnSite → Nonempty M.Presentation) :
    AffineDirectImageEquivalence B S hS f :=
  affineDirectImageEquivalence_of_isIso_unit_counit B S hS f
    (fun G hGq ↦ isQuasicoherentOnSite_directImageAlgebraPullback B S hS f hf G hGq) hf
    (fun G hGq ↦ isIso_directImageAlgebraPullbackAdjunction_unit_app_of_presentation B S hS V f hf
      G (hG G hGq).some)
    (fun M hMq ↦ isIso_directImageAlgebraPullbackAdjunction_counit_app_of_presentation B S hS V f
      hf M (hM M hMq).some)

end AlgebraicGeometry.Space

end
