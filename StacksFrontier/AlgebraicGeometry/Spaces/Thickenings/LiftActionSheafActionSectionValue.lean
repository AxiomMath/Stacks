module

public import StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSection

/-!
# The value of the identification of the acting sheaf's chart sections with the acting group

`AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv` identifies the sections of the
acting sheaf of [Stacks Project, Tag 061D] over the étale chart that a chart presentation
presents with the acting group
`AlgebraicGeometry.Space.ChartLiftPresentation.ActionSection` of that presentation.  It is built
as the underlying bijection of an isomorphism of abelian groups whose two factors are

* `AlgebraicGeometry.Space.smallEtaleInternalHomChartAssociatedLinearEquiv` at the two geometric
  comparisons of the presentation, reading a chart-level section as a `Γ(U, ⊤)`-linear map
  `Γ(a^*Ω_{W/V}, ⊤) ⟶ Γ(𝒞_{U/U'}, ⊤)` of Zariski global sections, and
* `Stacks.Thickenings.conormalTopSectionsLinearEquivKer`, identifying the global sections of the
  Zariski conormal sheaf of the chart thickening with `RingHom.ker i^♯`,

composed by `LinearEquiv.arrowCongr` on the target.  This file peels that composition off: the
linear map attached to a chart-level section is the chart-level reading of that section followed
by the conormal identification.

## Why this needed a separate file, and a correction

The implementation notes of
`StacksFrontier.AlgebraicGeometry.Spaces.Thickenings.LiftActionSheafActionSection` record that this
statement "was written out and it does **not** fit the 200 000-heartbeat budget", and conclude
that a consumer must instead state what it needs about the characterising equations of the two
factors.  **That is refuted here: the statement is provable, in about ten seconds, and the three
moves that make it so are not mathematical.**

1. The `rfl` is done **at the level of the isomorphisms of abelian groups**, as
   `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionAddEquiv_eq`, never at an applied
   value.  That follows the rule observed elsewhere in this development: an
   identification of a concrete comparison with its defining composite is cheap between the
   isomorphisms and over budget between their components.
2. The passage from the isomorphism to the value is a **generic** lemma at plain variables,
   `Stacks.addEquivTransArrowCongrRefl_apply`, so that nothing geometric is unfolded by it.
3. The module structure of the conormal data over the ring of the chart has to be supplied by
   hand.  Instance resolution does not find it: the ring is spelled `Γ(chartScheme A, ⊤)` by the
   first factor and `Γ(U, ⊤)` by the second, and the two are definitionally but not reducibly
   equal, so the `Module` instance of `Stacks.Smooth.thickeningKerModule` is invisible at the
   first spelling.  This is the same shape as the measurement recorded in
   `StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleInternalHomChartAdditive` for `Add` on the
   hom-set of two associated modules.

## Main results

* `Stacks.addEquivTransArrowCongrRefl_apply`: the generic peeling — postcomposing a bijection
  onto linear maps with `LinearEquiv.arrowCongr` at the identity of the source is postcomposition
  of the values.
* `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionAddEquiv_eq`: the identification of
  the acting group **is** its defining composite, as an isomorphism of abelian groups.
* `AlgebraicGeometry.Space.ChartLiftPresentation.actionSectionEquiv_apply`: **the value of the
  identification** — the acting section attached to a chart-level section of the acting sheaf is
  the Zariski linear map that section becomes, followed by the identification of the global
  sections of the Zariski conormal sheaf with `RingHom.ker i^♯`.

No `@[stacks]` attribute is claimed.

## References

* [Stacks Project, Tag 04AM](https://stacks.math.columbia.edu/tag/04AM)
* [Stacks Project, Tag 061D](https://stacks.math.columbia.edu/tag/061D)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace Stacks

/-- **Postcomposing a bijection onto linear maps with `LinearEquiv.arrowCongr` at the identity of
the source is postcomposition of the values.**  Stated at plain variables, because its only use
is at an instantiation whose arguments must not be unfolded. -/
theorem addEquivTransArrowCongrRefl_apply {R₀ : Type*} [CommRing R₀] {M N W : Type*}
    [AddCommGroup M] [Module R₀ M] [AddCommGroup N] [Module R₀ N] [AddCommGroup W]
    [Module R₀ W] {H : Type*} [AddCommGroup H] (A : H ≃ (M →ₗ[R₀] N))
    (hA : ∀ x y : H, A (x + y) = A x + A y) (K : N ≃ₗ[R₀] W) (h : H) (y : M) :
    ((AddEquiv.mk' A hA).trans
        (LinearEquiv.arrowCongr (LinearEquiv.refl R₀ M) K).toAddEquiv).toEquiv h y = K (A h y) :=
  rfl

end Stacks

namespace AlgebraicGeometry.Space

variable (C : BigFppfSite.{u}) (S : Scheme.{u}) (hS : C.Contains S)
variable {Bb X' Y : AlgebraicSpaces C S hS}

namespace ChartLiftPresentation

variable {C S hS} {p : X' ⟶ Bb} {q : Y ⟶ Bb} {Z : ClosedSubspaces C S hS X'.1}
  {a : (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS) ⟶ Y}
  {U' : SmallEtale C S hS X'.1} (P : ChartLiftPresentation C S hS p q a.hom U')

/-- **The identification of the acting group is its defining composite**, as an isomorphism of
abelian groups: the chart-level reading of a section as a Zariski linear map, followed by the
identification of the global sections of the Zariski conormal sheaf of the chart thickening with
`RingHom.ker i^♯`.

This is `rfl`, and it is stated at the isomorphisms rather than at their values on purpose — see
the implementation notes of this file. -/
theorem actionSectionAddEquiv_eq
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart) :
      letI := P.isAffineAmbient
      letI : IsAffine (chartScheme P.subEtaleChart) := P.isAffineSub
      haveI := P.isFirstOrderThickening.1
      haveI : AlgebraicGeometry.IsImmersion P.inclScheme := inferInstance
      haveI : (P.chartCotangent).IsQuasicoherent :=
        Stacks.Smooth.isQuasicoherent_pullbackCotangentSheaf' _ _
      haveI : (Stacks.Thickenings.conormalModules P.inclScheme).IsQuasicoherent :=
        Stacks.Conormal.conormalSheaf_isQuasicoherent P.inclScheme
      letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
      actionSectionAddEquiv C S hS P hw hv =
        (AddEquiv.mk' (smallEtaleInternalHomChartAssociatedLinearEquiv C S hS
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
              ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q))
              (conormalModule C S hS X' Z) P.subEtaleChart P.chartCotangent
              (Stacks.Thickenings.conormalModules P.inclScheme)
              (chartSourceIso C S hS P hw hv) (chartTargetIso C S hS P))
            (smallEtaleInternalHomChartAssociatedLinearEquiv_add C S hS
              (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
              ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q))
              (conormalModule C S hS X' Z) P.subEtaleChart P.chartCotangent
              (Stacks.Thickenings.conormalModules P.inclScheme)
              (chartSourceIso C S hS P hw hv) (chartTargetIso C S hS P))).trans
          (LinearEquiv.arrowCongr (LinearEquiv.refl _ _)
            (Stacks.Thickenings.conormalTopSectionsLinearEquivKer P.inclScheme
              P.isFirstOrderThickening.2)).toAddEquiv :=
  rfl

/-- **The value of the identification of the acting sheaf's chart sections with the acting
group.**  The acting section attached to a section `g` of the acting sheaf over the presented
chart carries a global section of the Zariski cotangent sheaf of the chart square to the image,
under the identification
`Stacks.Thickenings.conormalTopSectionsLinearEquivKer` of the global sections of the Zariski
conormal sheaf with `RingHom.ker i^♯`, of its image under the Zariski linear map that `g` becomes
on the chart.

So the identification is used through the chart-level reading of a section together with the
conormal identification, and no value of the `Function.surjInv` inside
`AlgebraicGeometry.Space.representedAssociatedModuleHomEquivLinearMap` is computed. -/
theorem actionSectionEquiv_apply
    (hw : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.tgtChart)
    (hv : (MorphismProperty.inverseImage
      (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme C S hS)).presheaf P.bseChart)
    (g : (liftActionSheaf C S hS Z q a).val.obj (op P.subEtaleChart))
    (y : Γ(P.chartCotangent, (⊤ : P.subScheme.Opens))) :
      letI := P.isAffineAmbient
      letI : IsAffine (chartScheme P.subEtaleChart) := P.isAffineSub
      haveI := P.isFirstOrderThickening.1
      haveI : AlgebraicGeometry.IsImmersion P.inclScheme := inferInstance
      haveI : (P.chartCotangent).IsQuasicoherent :=
        Stacks.Smooth.isQuasicoherent_pullbackCotangentSheaf' _ _
      haveI : (Stacks.Thickenings.conormalModules P.inclScheme).IsQuasicoherent :=
        Stacks.Conormal.conormalSheaf_isQuasicoherent P.inclScheme
      letI := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
      actionSectionEquiv C S hS P hw hv g y =
        (Stacks.Thickenings.conormalTopSectionsLinearEquivKer P.inclScheme
            P.isFirstOrderThickening.2)
          (smallEtaleInternalHomChartAssociatedLinearEquiv C S hS
            (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
            ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q))
            (conormalModule C S hS X' Z) P.subEtaleChart P.chartCotangent
            (Stacks.Thickenings.conormalModules P.inclScheme)
            (chartSourceIso C S hS P hw hv) (chartTargetIso C S hS P) g y) :=
  let := P.isAffineAmbient
  let : IsAffine (chartScheme P.subEtaleChart) := P.isAffineSub
  have := P.isFirstOrderThickening.1
  have : AlgebraicGeometry.IsImmersion P.inclScheme := inferInstance
  have : (P.chartCotangent).IsQuasicoherent :=
    Stacks.Smooth.isQuasicoherent_pullbackCotangentSheaf' _ _
  have : (Stacks.Thickenings.conormalModules P.inclScheme).IsQuasicoherent :=
    Stacks.Conormal.conormalSheaf_isQuasicoherent P.inclScheme
  let := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
  let : Module Γ(chartScheme P.subEtaleChart, (⊤ : (chartScheme P.subEtaleChart).Opens))
      P.conormal := Stacks.Smooth.thickeningKerModule P.isFirstOrderThickening
  (congrArg (fun e => (e.toEquiv g) y) (P.actionSectionAddEquiv_eq hw hv)).trans
    (Stacks.addEquivTransArrowCongrRefl_apply
      (smallEtaleInternalHomChartAssociatedLinearEquiv C S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
        ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q))
        (conormalModule C S hS X' Z) P.subEtaleChart P.chartCotangent
        (Stacks.Thickenings.conormalModules P.inclScheme)
        (chartSourceIso C S hS P hw hv) (chartTargetIso C S hS P))
      (smallEtaleInternalHomChartAssociatedLinearEquiv_add C S hS
        (⟨Z.1.toFunctor, Z.2.1⟩ : AlgebraicSpaces C S hS)
        ((modulePullback C S hS a).obj (sheafOfDifferentials C S hS q))
        (conormalModule C S hS X' Z) P.subEtaleChart P.chartCotangent
        (Stacks.Thickenings.conormalModules P.inclScheme)
        (chartSourceIso C S hS P hw hv) (chartTargetIso C S hS P))
      (Stacks.Thickenings.conormalTopSectionsLinearEquivKer P.inclScheme
        P.isFirstOrderThickening.2) g y)

end ChartLiftPresentation

end AlgebraicGeometry.Space

end
