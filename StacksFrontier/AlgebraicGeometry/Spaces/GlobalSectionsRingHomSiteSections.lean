module

public import StacksFrontier.AlgebraicGeometry.Spaces.GlobalSectionsRingHomComposition
public import StacksFrontier.AlgebraicGeometry.Spaces.ModuleChartCorrespondence
public import StacksFrontier.CategoryTheory.Sites.Cohomology.Modules.GlobalSectionsRingHomSections

/-!
# The ring map on global functions of a morphism of algebraic spaces, on a family of sections

A morphism `f : X ⟶ Y` of algebraic spaces induces a ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` on global
regular functions — the one of **Stacks 0732** read at the small étale ringed topoi, which is
`AlgebraicGeometry.Space.globalSectionsRingHomSite`.  This file says what it does to an actual
compatible family of regular functions: it is `Γ` of the structure map
`f♯ : 𝒪_Y ⟶ f_*𝒪_X` of **Stacks 03G8**.

This is `Stacks.Cohomology.SiteModules.ringSectionHom_globalSectionsRingHom` read at the small
étale seating, where the structure map of the morphism of ringed topoi is the structure map
`AlgebraicGeometry.Space.structureSharpSet` of the morphism of algebraic spaces by
`AlgebraicGeometry.Space.fSharpSet_smallEtaleRingedToposModulesHom`.  The point of making the
passage is that `AlgebraicGeometry.Space.structureSharpSet` *is* described chartwise, which
`Stacks.Cohomology.SiteModules.unitEnd` is not, and so the ring map becomes computable: on a
commutative diagram of étale scheme charts over `f` — a chart `U` of `X`, a chart `V` of `Y` and
a morphism of schemes `U ⟶ V` over `f` — the value of `globalSectionsRingHomSite f a` on `U` is
the pullback of the regular function `a V` along `U ⟶ V`, and nothing else enters.

## Main results

* `AlgebraicGeometry.Space.globalSectionsRingHomSite_val_chartDiagram`: **the chart-square
  formula.**  On a commutative diagram of étale scheme charts over `f`, the ring map of
  **Stacks 0732** is pullback of regular functions along the vertical morphism of schemes.
  `AlgebraicGeometry.Space.globalSectionsRingHomSite_val_chartPullback` is the same indexed by
  the charts of `X` above `X ×_Y V` instead of by chart squares.
* `AlgebraicGeometry.Space.ringSectionHom_globalSectionsRingHomSite`: **the ring map on global
  regular functions is `Γ` of the structure map of the morphism of algebraic spaces**, read
  through the canonical identification `Γ(Y, f_*𝒪_X) = Γ(X, 𝒪_X)`, and
  `AlgebraicGeometry.Space.ringSectionHom_comp_structureSharpSet` the same transposed, where
  the identification is gone and only `f♯` and a direct image remain.  The second is what the
  chart-square formula is read off.
* `AlgebraicGeometry.Space.ringSectionHom_globalSectionsRingHomSite_inverseImage`: the same in
  the inverse-image form of the structure map, and
  `AlgebraicGeometry.Space.globalSectionsRingHomSite_val_apply` its value over an étale chart
  of `X`.

## Implementation notes

*The two spellings of the structure ring sheaf.*  `AlgebraicGeometry.Space.structureRingSheaf`
of an algebraic space is `AlgebraicGeometry.RingedSite.ringSheaf` of its small étale ringed
*site*, while `Stacks.Cohomology.SiteModules.globalSectionsRingHom` is stated with
`Stacks.Sheaves.RingedToposModules.structureRingSheaf` of the small étale ringed *topos*.  The
two are definitionally equal, and as in
`StacksFrontier.AlgebraicGeometry.Spaces.FlatAffineCohomologyPullback` everything here is phrased
at the site spelling; that is why the statements below are proved by terms whose composition is
left to the unifier rather than by rewriting, a rewrite leaving a goal that is not type-correct
at `implicit` transparency.

*The canonical identification of global sections is never evaluated.*  The small étale
development has no description of `MorphismOfTopoi.pushforwardTerminalHomEquiv` — the
identification `Γ(Y, f_*E) = Γ(X, E)` — on sections over an étale chart, and none is needed:
the direct image is reached through the comparison equivalence of **Stacks 03G1** and its right
Kan extension, where sections over a chart `V` of `Y` are a limit over the charts of `X` above
`X ×_Y V`, while that identification is the transposition across `f⁻¹ ⊣ f_*` of the underlying
topoi, which the limit presentation does not see.  The chart-square formula avoids it by using
`Stacks.Cohomology.SiteModules.ringSectionHom_comp_fSharpSet`, where the identification has
been transposed away: what is left on the side of `X` is the *direct image of a constant family
of sections*, and the chart projection passes through a direct image by its naturality in the
sheaf, so the only thing ever evaluated is the structure map.  For the same reason the morphism
`1 ⟶ f_*1` that the transposed form carries — arbitrary, `f_*1` being terminal — never has to
be computed.

## References

* [Stacks Project, Tag 0732](https://stacks.math.columbia.edu/tag/0732)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
* [Stacks Project, Tag 03G1](https://stacks.math.columbia.edu/tag/03G1)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
open Stacks.Sheaves.RingedToposModules (fSharpSet)

noncomputable section

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicSpaces B S hS}

/-- **The ring map on global regular functions of Stacks 0732 is `Γ` of the structure map of
Stacks 03G8.**  For a morphism `f : X ⟶ Y` of algebraic spaces and a compatible family `a` of
regular functions on the étale charts of `Y`, read as a morphism `1 ⟶ 𝒪_Y` out of the terminal
sheaf, the family `globalSectionsRingHomSite f a` of regular functions on the étale charts of
`X` is `a` followed by the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X`, read back through the canonical
identification `Γ(Y, f_*𝒪_X) = Γ(X, 𝒪_X)`.

Chartwise this says: `globalSectionsRingHomSite f a` is the global section of `𝒪_X` whose
transport to `f_*𝒪_X` has, over an étale chart `V` of `Y`, the value that
`AlgebraicGeometry.Space.structureSharpSet` takes at the regular function `a V`.  Read in the
Kan-extension form of the direct image by `AlgebraicGeometry.Space.structureSharpSet_eq` and
`AlgebraicGeometry.Space.structureSharpRanSet_app` that value is
`AlgebraicGeometry.Space.structureMapApp f V (a V)`, whose projection to an étale chart `V'` of
`X` over `X ×_Y V` is the pullback of `a V` along the induced morphism of schemes `V' ⟶ V`, by
`AlgebraicGeometry.Space.chartProjection_structureMapApp`. -/
theorem ringSectionHom_globalSectionsRingHomSite (f : X ⟶ Y)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS Y).obj) :
    Sheaf.ringSectionHom (structureRingSheaf B S hS X)
        (globalSectionsRingHomSite B S hS f a) =
      (smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforwardTerminalHomEquiv
          (structureSetSheaf B S hS X)
        (Sheaf.ringSectionHom (structureRingSheaf B S hS Y) a ≫ structureSharpSet B S hS f) :=
  (Stacks.Cohomology.SiteModules.ringSectionHom_globalSectionsRingHom
      (smallEtaleRingedToposModulesHom B S hS f) a).trans
    (congrArg (fun m ↦ MorphismOfTopoi.pushforwardTerminalHomEquiv
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom (structureSetSheaf B S hS X)
        (Sheaf.ringSectionHom (structureRingSheaf B S hS Y) a ≫ m))
      (fSharpSet_smallEtaleRingedToposModulesHom B S hS f))

/-- **The ring map on global regular functions, in the inverse-image form of the structure
map.**  The family `globalSectionsRingHomSite f a` is the inverse image `f⁻¹a` of the family `a`
followed by the inverse-image form `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map.

This is the form that reads off over a single étale chart of `X`, in
`AlgebraicGeometry.Space.globalSectionsRingHomSite_val_apply`. -/
theorem ringSectionHom_globalSectionsRingHomSite_inverseImage (f : X ⟶ Y)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS Y).obj) :
    Sheaf.ringSectionHom (structureRingSheaf B S hS X)
        (globalSectionsRingHomSite B S hS f a) =
      (MorphismOfTopoi.inverseImageTerminalIso
            (smallEtaleRingedToposModulesHom B S hS f).toToposHom).inv ≫
        (smallEtaleRingedToposModulesHom B S hS f).toToposHom.inverseImage.map
            (Sheaf.ringSectionHom (structureRingSheaf B S hS Y) a) ≫
          (sheafCompose (SmallEtale.topology B S hS X.1) (forget RingCat.{u})).map
            (smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage :=
  Stacks.Cohomology.SiteModules.ringSectionHom_globalSectionsRingHom_inverseImage
    (smallEtaleRingedToposModulesHom B S hS f) a

/-- **The value of `globalSectionsRingHomSite f a` over an étale chart `U` of `X`.**  It is the
inverse-image form `f♯ : f⁻¹𝒪_Y ⟶ 𝒪_X` of the structure map, applied over `U` to the value over
`U` of the inverse image of the family `a`. -/
theorem globalSectionsRingHomSite_val_apply (f : X ⟶ Y)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS Y).obj)
    (U : (SmallEtale B S hS X.1)ᵒᵖ) :
    (globalSectionsRingHomSite B S hS f a).1 U =
      ((smallEtaleRingedToposModulesHom B S hS f).fSharpInverseImage.hom.app U).hom
        (((MorphismOfTopoi.inverseImageTerminalIso
              (smallEtaleRingedToposModulesHom B S hS f).toToposHom).inv ≫
            (smallEtaleRingedToposModulesHom B S hS f).toToposHom.inverseImage.map
              (Sheaf.ringSectionHom (structureRingSheaf B S hS Y) a)).hom.app U
          (Sheaf.terminalSheafSection (SmallEtale.topology B S hS X.1) U)) :=
  Stacks.Cohomology.SiteModules.globalSectionsRingHom_val_apply_fSharpInverseImage
    (smallEtaleRingedToposModulesHom B S hS f) a U

/-- **The ring map on global regular functions, transposed:**
`f♯ ∘ a = f_*(globalSectionsRingHomSite f a)`.
The family `a` followed by the structure map `f♯ : 𝒪_Y ⟶ f_*𝒪_X` of **Stacks 03G8** is the
direct image of the family `globalSectionsRingHomSite f a`, precomposed with a morphism
`1 ⟶ f_*1`; the morphism may be chosen at will, `f_*1` being terminal.

This is the form that computes: it is an equation between two sections of a direct image, where
the chart extensionality `AlgebraicGeometry.Space.moduleChartProjection_ext` applies, and that
is what gives the chart-square formula below. -/
theorem ringSectionHom_comp_structureSharpSet (f : X ⟶ Y)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS Y).obj)
    (α : ⊤_ (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) ⟶
      (smallEtaleDirectImage B S hS f).obj
        (⊤_ (Sheaf (SmallEtale.topology B S hS X.1) (Type u)))) :
    Sheaf.ringSectionHom (structureRingSheaf B S hS Y) a ≫ structureSharpSet B S hS f =
      α ≫ (smallEtaleDirectImage B S hS f).map
        (Sheaf.ringSectionHom (structureRingSheaf B S hS X)
          (globalSectionsRingHomSite B S hS f a)) :=
  (congrArg (fun m ↦ Sheaf.ringSectionHom (structureRingSheaf B S hS Y) a ≫ m)
      (fSharpSet_smallEtaleRingedToposModulesHom B S hS f)).symm.trans
    (Stacks.Cohomology.SiteModules.ringSectionHom_comp_fSharpSet
      (smallEtaleRingedToposModulesHom B S hS f) a α)

/-- **The ring map on global regular functions, on an étale chart square.**  For an étale scheme
chart `V` of `Y` and an étale scheme chart of `X` above `X ×_Y V`, the value of
`globalSectionsRingHomSite f a` on that chart of `X` is the pullback of the regular function
`a V` along the induced morphism of schemes.

This is the chart-square formula: it computes the ring map `Γ(Y, 𝒪_Y) ⟶ Γ(X, 𝒪_X)` of
**Stacks 0732** chart by chart, out of nothing but pullback of regular functions.

The proof applies the chart projection
`AlgebraicGeometry.Space.moduleChartProjection` to both sides of
`AlgebraicGeometry.Space.ringSectionHom_comp_structureSharpSet` over `V`.  On the left it meets
the structure map, where `AlgebraicGeometry.Space.moduleChartProjection_app_structureSharp`
evaluates it as pullback of functions; on the right it passes through the direct image by its
naturality in the sheaf, and what it meets there is a *constant* family of sections, so the
chosen morphism `1 ⟶ f_*1` never has to be evaluated. -/
theorem globalSectionsRingHomSite_val_chartPullback (f : X ⟶ Y)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS Y).obj)
    (V : SmallEtale B S hS Y.1)
    (j : StructuredArrow (op (chartBaseChange B S hS f V)) (comparisonFunctor B S hS X).op) :
    (globalSectionsRingHomSite B S hS f a).1 j.right =
      chartPullback B S hS f V j (a.1 (op V)) := by
  have key := congrArg
    (fun m : ⊤_ (Sheaf (SmallEtale.topology B S hS Y.1) (Type u)) ⟶
        (smallEtaleDirectImage B S hS f).obj (structureSetSheaf B S hS X) ↦
      (moduleChartProjection B S hS f V j).app (structureSetSheaf B S hS X)
        (m.hom.app (op V)
          (Sheaf.terminalSheafSection (SmallEtale.topology B S hS Y.1) (op V))))
    (ringSectionHom_comp_structureSharpSet B S hS f a
      (((smallEtaleRingedToposModulesHom B S hS f).toToposHom.pushforwardTerminalHomEquiv
        (⊤_ (Sheaf (SmallEtale.topology B S hS X.1) (Type u)))).symm (𝟙 _)))
  refine Eq.trans ?_ (Eq.trans key.symm
    (moduleChartProjection_app_structureSharp B S hS f V j (a.1 (op V))))
  exact (NatTrans.naturality_apply (moduleChartProjection B S hS f V j)
    (Sheaf.ringSectionHom (structureRingSheaf B S hS X)
      (globalSectionsRingHomSite B S hS f a)) _).symm

/-- **The ring map on global regular functions, on a commutative diagram of étale scheme charts
over `f`.**  For a chart diagram `d` — an étale scheme chart `U` of `X`, an étale scheme chart
`V` of `Y` and a morphism of schemes `U ⟶ V` over `f` — the value of
`globalSectionsRingHomSite f a` on `U` is the pullback of the regular function `a V` along
`U ⟶ V`.

This is `AlgebraicGeometry.Space.globalSectionsRingHomSite_val_chartPullback` with the index of
the limit cone replaced by the chart square it names, by
`AlgebraicGeometry.Space.chartPullback_indexOfChartDiagram`.  In this shape the ring map of
**Stacks 0732** is computed by `Γ` of the chart square, which is what the structure map of
**Stacks 03G8** does chartwise
(`AlgebraicGeometry.Space.smallEtaleRingedToposHom_chart`). -/
theorem globalSectionsRingHomSite_val_chartDiagram (f : X ⟶ Y)
    (a : RingCat.sectionsSubring (structureRingSheaf B S hS Y).obj)
    (d : ChartDiagram B S hS X.1 Y.1 f.hom) :
    (globalSectionsRingHomSite B S hS f a).1 (op d.U) =
      chartDiagramPullback B S hS f d (a.1 (op d.V)) :=
  (globalSectionsRingHomSite_val_chartPullback B S hS f a d.V
      (indexOfChartDiagram B S hS f d)).trans
    (chartPullback_indexOfChartDiagram B S hS f d (a.1 (op d.V)))

end AlgebraicGeometry.Space

end

end
